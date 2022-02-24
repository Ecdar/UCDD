/* -*- mode: C++; c-file-style: "stroustrup"; c-basic-offset: 4; indent-tabs-mode: nil; -*- */
/*********************************************************************
 *
 * This file is not part of the UPPAAL toolkit.
 * Copyright (c) 1995 - 2003, Uppsala University and Aalborg University.
 * All right reserved.
 *
 * $Id: testcdd.cpp,v 1.12 2005/05/11 19:08:15 adavid Exp $
 *
 *********************************************************************/

/** @file testdbm
 *
 * Test of CDD module.
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <iostream>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include "base/Timer.h"
#include "cdd/cdd.h"
#include "cdd/kernel.h"
#include "cdd/debug.h"
#include "dbm/dbm.h"
#include "dbm/gen.h"
#include "dbm/print.h"
#include "debug/macros.h"

using std::endl;
using std::cerr;
using std::cout;
using base::Timer;

/* Inner repeat loop. Inner loop of what?
 */
#define LOOP 100

/* Allocation of DBM, vector, bitstring
 */
#define ADBM(NAME)  raw_t NAME[size * size];
#define AVECT(NAME) int32_t NAME[size];
#define ABITS(NAME) uint32_t NAME[bits2intsize(size)];

/* Random range
 * may change definition
 */
#define RANGE() ((rand() % 10000) + 1)

/* Print the difference between two DBMs two stdout.
 */
#define DIFF(D1, D2) dbm_printDiff(stdout, D1, D2, size)

/* Assert that two DBMs are equal. If not, prints the difference
 * between the two DBMs are exits the program.
 */
#define DBM_EQUAL(D1, D2) ASSERT(dbm_areEqual(D1, D2, size), DIFF(D1, D2))

/* Show progress
 */
#define PROGRESS() debug_spin(stderr)

/* Generation of DBMs: track non trivial ones
 * and count them all.
 */
#define DBM_GEN(D)                                  \
    do {                                            \
        bool good = dbm_generate(D, size, RANGE()); \
        allDBMs++;                                  \
        goodDBMs += good;                           \
    } while (0)

uint32_t allDBMs = 0;
uint32_t goodDBMs = 0;
uint32_t printCounter = 0; // Used to number printed CDDs

typedef void (*TestFunction)(size_t size);

static void print_cdd(cdd to_print, char* name, bool push_negate) {
    char filename[30];
    sprintf(filename, "%s_%d.dot", name, printCounter);
    printf("Printing cdd %s to file : \n", name);
    FILE *fp_main;
    fp_main = fopen(filename, "w");
    cdd_fprintdot(fp_main, to_print, push_negate);
    fclose(fp_main);

    printCounter++;
}

static void print_cdd(cdd to_print, bool push_negate) {
    print_cdd(to_print, "",push_negate);
}

/* test conversion between CDD and DBMs
 */
static void test_conversion(size_t size)
{
    ADBM(dbm1);
    ADBM(dbm2);

    /* Convert to CDD
     */
    DBM_GEN(dbm1);
    cdd cdd1(dbm1, size);

    /* Check conversion
     */
    ASSERT(cdd_contains(cdd1, dbm1, size), dbm_print(stdout, dbm1, size));

    /* Convert to DBM
     */
    cdd cdd2 = cdd_extract_dbm(cdd1, dbm2, size);

    /* Check conversion
     */
    DBM_EQUAL(dbm1, dbm2);
    assert(cdd_reduce(cdd2) == cdd_false());
}

/* test intersection of CDDs
 */
static void test_intersection(size_t size)
{
    cdd cdd1, cdd2, cdd3, cdd4;
    ADBM(dbm1);
    ADBM(dbm2);
    ADBM(dbm3);
    ADBM(dbm4);

    /* Generate DBMs
     */
    DBM_GEN(dbm1);
    DBM_GEN(dbm2);
    dbm_copy(dbm3, dbm2, size);

    /* Generate intersection
     */
    bool empty = !dbm_intersection(dbm3, dbm1, size);

    /* Do the same with CDDs.
     */
    cdd1 = cdd(dbm1, size);
    cdd2 = cdd(dbm2, size);
    cdd3 = cdd1 & cdd2;

    /* Check the result.
     */
    if (!empty) {
        assert(cdd_contains(cdd3, dbm3, size));

        /* Extract DBM.
         */
        cdd3 = cdd_reduce(cdd3);
        cdd4 = cdd_extract_dbm(cdd3, dbm4, size);

        /* Check result.
         */
        DBM_EQUAL(dbm3, dbm4);
    }
}

static double time_apply_and_reduce = 0;
static double time_apply_reduce = 0;

static void test_apply_reduce(size_t size)
{
    /* Generate 8 simple CDDs and then 'or' them together in a pair
     * wise/binary tree fashion.
     */
    cdd cdds[8];
    ADBM(dbm);

    for (uint32_t i = 0; i < 8; i++) {
        DBM_GEN(dbm);
        cdds[i] = cdd(dbm, size);
    }

    for (uint32_t j = 4; j > 0; j /= 2) {
        for (uint32_t i = 0; i < j; i++) {
            cdd a, b, c, e, f;

            a = cdds[2 * i];
            b = cdds[2 * i + 1];

            /* Fake run to ensure that the result has already been
             * created (timing is more fair).
             */
            c = !cdd_apply_reduce(!a, !b, cddop_and);

            /* Run (a|b) last so that the apply_reduce calls do not
             * gain from any cache lookups.
             */
            Timer timer;
            c = !cdd_apply_reduce(!a, !b, cddop_and);
            time_apply_reduce += timer.getElapsed();
            e = a | b;
            cdd_reduce(e);
            time_apply_and_reduce += timer.getElapsed();

            /* Check that c/d are actually reduced.
             */
            assert(c == cdd_reduce(c));

            /* Check that c/d and e describe the same federation.
             */
            assert(cdd_reduce(c ^ e) == cdd_false());

            cdds[i] = c;
        }
    }
}

static double time_reduce = 0;
static double time_bf = 0;

static void test(const char* name, TestFunction f, size_t size)
{
    cout << name << " size = " << size << endl;
    for (uint32_t k = 0; k < LOOP; ++k) {
        PROGRESS();
        f(size);
    }
}


static cdd randomCddFromDBMs(size_t size, int number_of_DBMs)
{
    cdd cdd_result = cdd_false();
    ADBM(dbm);
    for (int i = 0; i < number_of_DBMs; i++) {
        //ADBM(dbm);
        DBM_GEN(dbm);
        assert(dbm_isValid(dbm, size));
        cdd_result |= cdd(dbm, size);
    }
    return cdd_result;
}


static void test_reduce(size_t size)
{
    cdd cdd1, cdd_bf, cdd_tarjan, cdd_reduce_2;
    ADBM(dbm);

    cdd1 = cdd_false();
    for (uint32_t j = 0; j < 5; j++) {
        DBM_GEN(dbm);
        cdd1 |= cdd(dbm, size);
    }

    cdd_bf = cdd(cdd_bf_reduce(cdd1.handle()));
    cdd_tarjan = cdd_reduce(cdd1);
    cdd_reduce_2 = cdd_reduce2(cdd1);

    printf("cdd_bf == cdd1: %i\n",(cdd_bf == cdd1));
    printf("cdd_bf == cdd_tarjan: %i\n",(cdd_bf == cdd_tarjan));
    printf("cdd_bf == cdd_reduce_2: %i\n",(cdd_bf == cdd_reduce_2));
    printf("cdd_bf == cdd_bf: %i\n",(cdd_bf == cdd_bf));

    printf("---\n");

    printf("(!cdd_bf & cdd1) == cdd_false()) && ((cdd_bf & !cdd1) == cdd_false()): %i\n",((!cdd_bf & cdd1) == cdd_false()) && ((cdd_bf & !cdd1) == cdd_false()));
    printf("(!cdd_bf & cdd_tarjan) == cdd_false()) && ((cdd_bf & !cdd_tarjan) == cdd_false()): %i\n",((!cdd_bf & cdd_tarjan) == cdd_false()) && ((cdd_bf & !cdd_tarjan) == cdd_false()));
    printf("(!cdd_bf & cdd_reduce_2) == cdd_false()) && ((cdd_bf & !cdd_reduce_2) == cdd_false()): %i\n",((!cdd_bf & cdd_reduce_2) == cdd_false()) && ((cdd_bf & !cdd_reduce_2) == cdd_false()));

    printf("---\n");



    printf("cdd_reduce(cdd_bf ^ cdd1) == cdd_false(): %i\n",(cdd_reduce(cdd_bf ^ cdd1) == cdd_false()));
    printf("cdd_reduce(cdd_bf ^ cdd_tarjan) == cdd_false(): %i\n",(cdd_reduce(cdd_bf ^ cdd_tarjan) == cdd_false()));
    printf("cdd_reduce(cdd_bf ^ cdd_reduce_2) == cdd_false(): %i\n",(cdd_reduce(cdd_bf ^ cdd_reduce_2) == cdd_false()));
    printf("cdd_reduce(cdd_bf ^ cdd_bf) == cdd_false(): %i\n",(cdd_reduce(cdd_bf ^ cdd_bf) == cdd_false()));

    printf("---\n");





    assert(((cdd_bf ^ cdd1) == cdd_false()) == false);
    assert(((cdd_bf ^ cdd_tarjan) == cdd_false()) == true);
    assert(((cdd_bf ^ cdd_reduce_2) == cdd_false()) == false);
    assert(((cdd_bf ^ cdd_bf) == cdd_false()) == true);

    assert(((cdd_tarjan ^ cdd1) == cdd_false())  == false);
    assert(((cdd_tarjan ^ cdd_tarjan) == cdd_false()) == true);
    assert(((cdd_tarjan ^ cdd_reduce_2) == cdd_false()) == false);
    assert(((cdd_tarjan ^ cdd_bf) == cdd_false()) == true);

    assert(((cdd_reduce_2 ^ cdd1) == cdd_false()) == true);
    assert(((cdd_reduce_2 ^ cdd_tarjan) == cdd_false())== false);
    assert(((cdd_reduce_2 ^ cdd_reduce_2) == cdd_false()) == true);
    assert(((cdd_reduce_2 ^ cdd_bf) == cdd_false())==false);

}


static cdd test1_CDD_from_random_DBMs(size_t size, int numberOfDBMs)
{
    cdd cdd_result;
    printf("Test1: Building CDDs and their negations from random DBMs\n");

    cdd_result = cdd_true();
    ADBM(dbm);
    // Build DBMs
    for (int i = 0; i < numberOfDBMs; i++) {
        DBM_GEN(dbm);

        printf("_______________\n");
        dbm_print(stdout, dbm, size);
        cdd_result = cdd(dbm, size);
        cdd_result= cdd_reduce(cdd_result);
        print_cdd(cdd_result, "test1_normal", true);

        cdd cdd_negated = !cdd_result;
        cdd_negated= cdd_reduce(cdd_negated);
        print_cdd(cdd_negated, "test1_negated", true);

        assert(cdd_reduce(cdd_result & cdd_negated) == cdd_false());
    }
    return cdd_result;
}

static cdd buildSimpleStaticBDD(int bdd_start_level) {

    printf("Test2: Building a static BDD\n");

    cdd negated = !cdd_bddvarpp(bdd_start_level + 1);
    cdd myTrueNode = cdd_bddvarpp(bdd_start_level + 1);

    cdd topNodeTrue = cdd_bddvarpp(bdd_start_level + 0);
    cdd leftNode = topNodeTrue & myTrueNode;
    cdd rightNode = (!topNodeTrue) & negated;
    cdd topNode = leftNode | rightNode;

    print_cdd(rightNode, "rightNode", true);

    print_cdd(negated, "negated", true);
    print_cdd(topNode, "topnode", true);

    topNode = !topNode;
    print_cdd(topNode, "topnode_neg", true);

    //TODO: Find a good assert

    return topNode;
}


static void extractDBMTest(size_t size, int number_of_DBMs) {
    printf("Running extractDBMTest.\n");
    cdd cdd_result = randomCddFromDBMs(size,number_of_DBMs);
    ADBM(dbm);
    /*
    cdd test = cdd_result;
    print_cdd(cdd_result, "beforereduce2", true);
    cdd_result = cdd_reduce2(cdd_result);
    print_cdd(cdd_result, "afterreduce2", true);

    cdd one1 = test & !cdd_result;
    cdd two1 = !test & cdd_result;

    print_cdd(one1, "one1", true);
    print_cdd(two1, "two1", true);
    */

    cdd_result=cdd_reduce(cdd_result);

    printf("Extracting first BDM. \n");
    cdd extracted = cdd_extract_dbm(cdd_result,dbm,size);

    printf("Printing the extracted BDM. \n");
    dbm_print(stdout, dbm, size);

    printf("Starting a new CDD based on the extraced DBMS. \n");
    cdd rebuilt = cdd(dbm, size);

    printf("Printing original CDD\n");
    print_cdd(cdd_result, "original", true);

    printf("Printing CDD after extracting\n");
    print_cdd(extracted, "extracted", true);

    while ( !cdd_isterminal(extracted.handle())&& cdd_info(extracted.handle())->type != TYPE_BDD  )    {
        extracted = cdd_reduce(extracted);
        printf("Extracting\n");
        extracted = cdd_extract_dbm(extracted,dbm,size);
        printf("Printing CDD after extracting\n");
        print_cdd(extracted, "extracted_while", true);
        rebuilt |= cdd(dbm, size);
    }

    printf("Printing rebuilt rebuilt CDD \n");
    print_cdd(rebuilt, "rebuilt", true);


    printf("Printing reduced rebuilt CDD \n");
    rebuilt= cdd_reduce(rebuilt);
    print_cdd(rebuilt, "rebuilt_red", true);

    cdd one = rebuilt & !cdd_result;
    cdd two = !rebuilt & cdd_result;

    print_cdd(one, "difference1", true);
    print_cdd(two, "difference2", true);

    assert(cdd_reduce(one) == cdd_false());
    assert(cdd_reduce(two) == cdd_false());
    assert(cdd_reduce(rebuilt ^ cdd_result) == cdd_false());

}


static void negationTest(size_t size, int number_of_DBMs) {
    printf("Running negationTest.\n");
    cdd cdd_result = randomCddFromDBMs(size, number_of_DBMs);

    cdd first = cdd_result & !cdd_result;
    cdd second = !cdd_result & cdd_result;

    print_cdd(first, "one1", true);
    print_cdd(second, "two1", true);

    assert(cdd_reduce(first) == cdd_false());
    assert(cdd_reduce(second) == cdd_false());
}



static void equalityTest(size_t size, int number_of_DBMs) {
    printf("Running equalityTest.\n");
    cdd cdd_result = randomCddFromDBMs(size, number_of_DBMs);

    assert((cdd_result ^ cdd_result)==cdd_false());
    assert(cdd_reduce(cdd_result ^ cdd_result)==cdd_false());
}

static void reduceTest(size_t size, int number_of_DBMs) {
    printf("Running reduceTest.\n");
    cdd cdd_result = randomCddFromDBMs(size, number_of_DBMs);

    cdd test = cdd_result;
    print_cdd(cdd_result, "beforereduce", true);
    cdd_result = cdd_reduce(cdd_result);
    print_cdd(cdd_result, "afterreduce", true);

    cdd one1 = test & !cdd_result;
    cdd two1 = !test & cdd_result;

    print_cdd(one1, "one1", true);
    print_cdd(two1, "two1", true);

    printf("one1 == cdd_false(): %i",one1 == cdd_false());
    printf("two1 == cdd_false(): %i",two1 == cdd_false());

    assert(cdd_reduce(one1) == cdd_false());
    assert(cdd_reduce(two1) == cdd_false());



}

/*
static void extractDBMBFTest(size_t size, int number_of_DBMs) {
    printf("Running extractDBMTest.\n");
    cdd cdd_result = randomCddFromDBMs(size, number_of_DBMs);

    cdd test = cdd_result;
    print_cdd(cdd_result, "beforereduce2", true);
    cdd_result = cdd_reduce(cdd_result);
    print_cdd(cdd_result, "afterreduce2", true);

    cdd one1 = test & !cdd_result;
    cdd two1 = !test & cdd_result;

    print_cdd(one1, "one1", true);
    print_cdd(two1, "two1", true);

    assert(one1 == cdd_false());
    assert(two1 == cdd_false());


    assert(cdd_reduce(test ^ cdd_result) == cdd_false());


    printf("Extracting the BDM. \n");
    cdd extracted = cdd_extract_dbm(cdd_result,dbm,size);



    printf("Printing the extracted BDM. \n");
    dbm_print(stdout, dbm, size);

    cdd rebuilt = cdd(dbm, size);

    printf("Printing original CDD\n");
    print_cdd(cdd_result, "originalWB", true);

    printf("Printing CDD after extracting\n");
    print_cdd(extracted, "extractedWB", true);

    while ( !cdd_isterminal(extracted.handle())&& cdd_info(extracted.handle())->type != TYPE_BDD  )    {
        extracted = cdd_reduce2(extracted);
        printf("Extracting\n");
        extracted = cdd_extract_dbm(extracted,dbm,size);
        printf("Printing CDD after extracting\n");
        print_cdd(extracted, "extractedWB_while", true);
        rebuilt |= cdd(dbm, size);

    }

    printf("Printing rebuilt rebuilt CDD \n");
    print_cdd(rebuilt, "rebuilt", true);


    printf("Printing regularized rebuilt CDD \n");
    rebuilt= cdd_reduce2(rebuilt);
    print_cdd(rebuilt, "rebuilt_red", true);

    cdd one = rebuilt & !cdd_result;
    cdd two = !rebuilt & cdd_result;

    print_cdd(one, "one", true);
    print_cdd(two, "two", true);



}*/


static void extractDBMWithBoolsTest(size_t size, int number_of_DBMs, int bdd_start_level) {
    printf("Running extractDBMWithBoolsTest.\n");
    cdd cdd_result = randomCddFromDBMs(size, number_of_DBMs);
    ADBM(dbm);

    cdd b1 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b2 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b3 = cdd_bddvarpp(bdd_start_level + 2);

    // TODO: make a test for how brackets affect the CDD creation
    cdd cdd_result1 = (cdd_result &  (b1 & b2 & !b3)) | (b1 & b2 & b3);
    print_cdd(cdd_result1, "outerOR", true);


    cdd_result = cdd_result &  ((b1 & b2 & !b3) | (b1 & b2 & b3));
    cdd_result = cdd_reduce(cdd_result);
    printf("Extracting the BDM. \n");
    cdd extracted = cdd_extract_dbm(cdd_result,dbm,size);

    printf("Printing the extracted BDM. \n");
    dbm_print(stdout, dbm, size);

    cdd rebuilt = cdd(dbm, size);

    printf("Printing original CDD\n");
    print_cdd(cdd_result, "originalWB", true);

    cdd reduced = cdd_reduce(cdd_result);
    printf("Printing reduced rebuilt CDD\n");
    print_cdd(reduced, "reduced_origEB", true);

    printf("Printing CDD after extracting\n");
    print_cdd(extracted, "extractedWB", true);

    while ( !cdd_isterminal(extracted.handle())&& cdd_info(extracted.handle())->type != TYPE_BDD  )    {
        extracted = cdd_reduce(extracted);
        printf("Extracting\n");
        extracted = cdd_extract_dbm(extracted,dbm,size);
        printf("Printing CDD after extracting\n");
        print_cdd(extracted, "extractedWB_while", true);
        rebuilt |= cdd(dbm, size);
    }

    printf("Printing rebuilt rebuilt CDD \n");
    rebuilt= cdd_reduce(rebuilt);
    print_cdd(rebuilt, "rebuiltWB", true);

    rebuilt = rebuilt &  ((b1 & b2 & !b3) | (b1 & b2 & b3));

    assert(cdd_reduce(cdd_result  ^ rebuilt) == cdd_false());
}



static void containsDBMTest(size_t size, int number_of_DBMs) {
    printf("Running containsDBMTest.\n");
    cdd cdd_result = cdd_false();

    printf("Building %i DBMS\n", number_of_DBMs);
    ADBM(dbm);
    // Build DBMs
    for (int i = 0; i < number_of_DBMs; i++) {
        //ADBM(dbm);
        DBM_GEN(dbm);
        printf("Adding DBM to cdd \n");
        cdd_result |= cdd(dbm, size);
    }

    dbm_print(stdout, dbm, size);
    printf("Checking if the last added DBM is included: %i\n", cdd_contains(cdd_result,dbm,size));
    assert(cdd_contains(cdd_result,dbm,size));

    ADBM(dbm1);
    printf("Extracting a BDM. \n");
    cdd extracted = cdd_extract_dbm(cdd_result,dbm1,size);

    dbm_print(stdout, dbm1, size);

    printf("Checking if the last added DBM is included: %i\n", cdd_contains(extracted,dbm,size));
    assert(!cdd_contains(extracted,dbm1,size));

    printf("Printing CDD after extracting\n");
    print_cdd(extracted, "extracted", false);
}

static cdd buildCDDWithBooleansTest(size_t size, int number_of_DBMs, int number_of_booleans, int bdd_start_level) {
    printf("Building CDD with Booleans\n");

    cdd cdd_result = cdd_false();
    ADBM(dbm);
    for (int i = 0; i < number_of_DBMs; i++) {
        DBM_GEN(dbm);
        assert(dbm_isValid(dbm, size));
        cdd_result |= cdd(dbm, size);
    }

/*
    for (int i = 0; i < number_of_booleans; i++) {


        if (rand() < RAND_MAX/2) {
            printf("Random is working");
            cdd new_cdd = cdd_bddvarpp(bdd_start_level + i);
            print_cdd(new_cdd, "non_negated");
            cdd_result |= new_cdd;
        } else  {
            printf("Random is NOT working");

            cdd new_cdd = cdd_bddnvarpp(bdd_start_level + i);
            print_cdd(new_cdd, "negated");
            cdd_result |= new_cdd;
        }


    }
    */

    cdd b1 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b2 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b3 = cdd_bddvarpp(bdd_start_level + 2);
    cdd b4 = cdd_bddvarpp(bdd_start_level + 3);

    printf("Before adding boolean vars, the inclusion check is %i \n",cdd_contains(cdd_result,dbm,size));
    cdd_result = cdd_result &  (b1 & b2 & !b3) | (b1 & b2 & b3);
    printf("After adding boolean vars, the inclusion check is %i \n",cdd_contains(cdd_result,dbm,size));
    assert(cdd_contains(cdd_result,dbm,size));
    return cdd_result;
}

static bool cddContainsBoolStateRec(ddNode* r, bool state[], int bdd_start_level, int index, bool negated) {
    assert(cdd_info(r)->type == TYPE_BDD);
    bddNode* node = bdd_node(r);

    if (node->level!=index+bdd_start_level)
        return (cddContainsBoolStateRec(r, state, bdd_start_level, index+1, negated));

    if (node->high==cddtrue) {
        if (state[index]) return true ^ negated ^ cdd_is_negated(r);
    }
    if (node->high==cddfalse) {
        if (state[index]) return false ^ negated ^ cdd_is_negated(r);
    }
    if (node->low==cddtrue) {
        if (!state[index]) return true ^ negated ^ cdd_is_negated(r);
    }
    if (node->low==cddfalse) {
        if (!state[index]) return false ^ negated ^ cdd_is_negated(r);
    }

    if (state[index])
        return cddContainsBoolStateRec(node->high, state, bdd_start_level, index+1, negated ^ cdd_is_negated(r));
    else
        return cddContainsBoolStateRec(node->low, state, bdd_start_level, index+1, negated ^ cdd_is_negated(r));

}


static bool cddContainsStateRec(ddNode* r, bool state[], int bdd_start_level, int index, bool negated) {

    if (cdd_info(r)->type == TYPE_BDD)
        return cddContainsBoolStateRec(r,state, bdd_start_level,index, negated);
    else
    {
        // TODO: this part is just skipped at the moment, add support for CDDs
        printf("encountrered CDD");
        cddNode* node = cdd_node(r);
        return cddContainsStateRec(node->next,state, bdd_start_level,index, negated);
    }

}

bool cddContainsState(ddNode* cdd_, bool state[], int bdd_start_level)
{

   return cddContainsStateRec(cdd_, state, bdd_start_level, 0, false);
}

bool cddFromIntervalTest()
{
    // note that 5 means 2 including, while the 10 below means 5 non including
    cdd smaller = cdd_interval(1,0,0,5);
    print_cdd(smaller,"smaller",true);
    cdd larger = cdd_interval(1,0,0,10);
    print_cdd(larger,"larger",true);
    assert(cdd_reduce(larger - smaller) != cdd_false() );
    assert(cdd_reduce(smaller - larger) == cdd_false() );
}

bool orOfBCDDTest(  int32_t bdd_start_level)
{
    // note that 5 means 2 including, while the 10 below means 5 non including
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);

    cdd smaller = cdd_interval(1,0,0,5);
    smaller &= b6;
    print_cdd(smaller,"smaller",true);
    cdd larger = cdd_interval(1,0,6,10);
    larger &= !b6;
    print_cdd(larger,"larger",true);
    cdd result = larger | smaller;
    cdd_reduce(result);
    print_cdd(result,"orOfBCDD",true);
    return true;
    //TODO: Figure out good assert
}

bool orExactractTest(size_t size, int32_t bdd_start_level) {
    // note that 5 means 2 including, while the 10 below means 5 non including
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);

    cdd smaller = cdd_intervalpp(1,0,0,5);
    smaller &= cdd_interval(2,0,0,dbm_LS_INFINITY);
    smaller &= cdd_interval(3,0,0,dbm_LS_INFINITY);
    smaller &= b6;
    print_cdd(smaller,"smaller",true);
    cdd larger = cdd_intervalpp(1,0,6,10);
    larger &= cdd_interval(2,0,0,dbm_LS_INFINITY);
    larger &= cdd_interval(3,0,0,dbm_LS_INFINITY);
    larger &= !b6;
    print_cdd(larger, "larger", true);
    cdd result = larger | smaller;
    cdd_reduce(result);
    print_cdd(result, "orOfBCDD", true);

    ADBM(dbm);
    cdd extract = cdd_extract_dbm(result, dbm, size);
    extract = cdd_reduce(extract);
    dbm_print(stdout, dbm, size);


    print_cdd(extract, "extract", true);
    cdd dbmcdd= cdd(dbm,size);
    print_cdd(dbmcdd, "dbm", true);

    cdd extract1 = cdd_extract_dbm(extract, dbm, size);
    print_cdd(extract, "extract1", true);

}


bool orExactractWithBddTest(size_t size, int32_t bdd_start_level)
{
    // note that 5 means 2 including, while the 10 below means 5 non including
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);

    cdd smaller = cdd_intervalpp(1,0,0,5);
    smaller &= cdd_interval(2,0,0,dbm_LS_INFINITY);
    smaller &= cdd_interval(3,0,0,dbm_LS_INFINITY);
    smaller &= b6;
    print_cdd(smaller,"smaller",true);
    cdd larger = cdd_intervalpp(1,0,6,10);
    larger &= cdd_interval(2,0,0,dbm_LS_INFINITY);
    larger &= cdd_interval(3,0,0,dbm_LS_INFINITY);
    larger &= !b6;
    print_cdd(larger,"larger",true);
    cdd result = larger | smaller;
    cdd_reduce(result);
    print_cdd(result,"orOfBCDD",true);




    cdd cdd_at_bottom;
    ADBM(dbm);

    cdd extract = cdd_extract_dbm_and_bdd(result,dbm, size,cdd_at_bottom);
    printf("came out of the extraction\n");
    printf("Current pointer value: %p\n", cdd_at_bottom.handle());

    extract = cdd_reduce(extract);

    cdd removed = cdd(dbm, size);
    removed = cdd_reduce(removed);

    cdd_at_bottom = cdd_reduce(cdd_at_bottom);
    print_cdd(extract,"extract", true);
    print_cdd(removed,"removed", true);
    print_cdd(cdd_at_bottom,"cdd_at_bottom", true);

    cdd cdd_at_bottom1;
    ADBM(dbm1);
    cdd extract1 = cdd_extract_dbm_and_bdd(extract,dbm1, size,cdd_at_bottom1);
    printf("came out of the extraction\n");

    extract1 = cdd_reduce(extract1);
    cdd removed1 = cdd(dbm1, size);
    removed1 = cdd_reduce(removed1);

    cdd_at_bottom1 = cdd_reduce(cdd_at_bottom1);
    print_cdd(extract1,"extract1", true);
    print_cdd(removed1,"removed1", true);
    print_cdd(cdd_at_bottom1,"cdd_at_bottom1", true);


    cdd rebuilt = (removed & cdd_at_bottom) | (removed1 & cdd_at_bottom1);
    rebuilt= cdd_reduce(rebuilt);

    print_cdd(rebuilt,"rebuilt", true);
    assert(cdd_equiv(rebuilt,result));





    return true;
    //TODO: Figure out good assert
}

void restrictTest( int32_t number_of_booleans, int32_t bdd_start_level)
{
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b7 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b8 = cdd_bddvarpp(bdd_start_level + 2);
    cdd b9 = cdd_bddvarpp(bdd_start_level + 3);
    cdd result =  (!b6 & !b7 ) |  ( !b8 & b9);
    print_cdd(result, "before_restriction", true );
    cdd result1 = cdd_restrict(result, reinterpret_cast<int32_t *>(bdd_start_level + 2), 0);
    print_cdd(result1, "after_restriction", true );
    cdd result2 = cdd_restrict(result, reinterpret_cast<int32_t *>(bdd_start_level + 1), reinterpret_cast<int32_t *>(1));
    print_cdd(result2, "after_restriction", true );
    cdd result3 = cdd_restrict(result2, reinterpret_cast<int32_t *>(bdd_start_level + 2), reinterpret_cast<int32_t *>(1));
    print_cdd(result3, "after_restriction", true );
    assert( result3 == cdd_false());
}


static cdd MartijnTest(int bdd_start_level)
{
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b7 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b8 = cdd_bddvarpp(bdd_start_level + 2);
    cdd b9 = cdd_bddvarpp(bdd_start_level + 3);

    cdd result;
    // single traces
    result =  (!b6 & !b7 & !b8 & b9);
    print_cdd(result, "!b6!b7!b8b9", true);
    bool state[4] = {false, false, false,true};
    assert(cddContainsState(result.handle(), state, bdd_start_level));
    bool state1[4] = {false, false, true,true};
    assert(!cddContainsState(result.handle(), state1, bdd_start_level));


    result =  (!b6 & !b7 & b8 & b9);
    print_cdd(result, "!b6!b7b8b9", true);
    bool state2[4] = {false, false, true,true};
    assert(cddContainsState(result.handle(), state2, bdd_start_level));
    bool state3[4] = {false, false, false,true};
    assert(!cddContainsState(result.handle(), state3, bdd_start_level));

    result =  (!b6 & b7 & b8 & b9);
    print_cdd(result, "!b6b7b8b9", true);
    bool state4[4] = {false, true, true,true};
    assert(cddContainsState(result.handle(), state4, bdd_start_level));
    bool state5[4] = {false, false, false,true};
    assert(!cddContainsState(result.handle(), state5, bdd_start_level));

    result =  (!b6 & b7 & b8 & !b9);
    print_cdd(result, "!b6b7b8!b9", true);

    bool state6[4] = {false, true, true,false};
    assert(cddContainsState(result.handle(), state6, bdd_start_level));
    bool state7[4] = {false, false, false,true};
    assert(!cddContainsState(result.handle(), state7, bdd_start_level));

    result =  (b6 & b7 & !b8 & !b9);
    print_cdd(result, "b6b7!b8!b9", true);

    bool state8[4] = {true, true, false,false};
    assert(cddContainsState(result.handle(), state8, bdd_start_level));
    bool state9[4] = {false, false, false,true};
    assert(!cddContainsState(result.handle(), state9, bdd_start_level));

    result = (b6 & b7 & b8) | (!b6 & !b7 & !b8);
    print_cdd(result, "b6b7b8or!b6!b7!b8", true);


    bool state10[3] = {true, true, true};
    assert(cddContainsState(result.handle(), state10, bdd_start_level));
    bool state11[3] = {false, false, false};
    assert(cddContainsState(result.handle(), state11, bdd_start_level));


    bool state12[3] = {true, true, false};
    assert(!cddContainsState(result.handle(), state12, bdd_start_level));
    bool state13[3] = {false, false, true};
    assert(!cddContainsState(result.handle(), state13, bdd_start_level));

    result = (b6 & b7 & b8) | (!b6 & !b7 & b8);
    print_cdd(result, "b6b7b8or!b6!b7b8", true);


    bool state14[3] = {true, true, true};
    assert(cddContainsState(result.handle(), state14, bdd_start_level));
    bool state15[3] = {false, false, true};
    assert(cddContainsState(result.handle(), state15, bdd_start_level));

    bool state16[3] = {true, true, false};
    assert(!cddContainsState(result.handle(), state16, bdd_start_level));
    bool state17[3] = {false, false, false};
    assert(!cddContainsState(result.handle(), state17, bdd_start_level));

    result = (b6 & b7 & b8) | (!b6 & b7 & b8);
    print_cdd(result, "b6b7b8or!b6b7b8", true);

    bool state18[3] = {true, true, true};
    assert(cddContainsState(result.handle(), state18, bdd_start_level));
    bool state19[3] = {false, true, true};
    assert(cddContainsState(result.handle(), state19, bdd_start_level));

    bool state20[3] = {true, true, false};
    assert(!cddContainsState(result.handle(), state20, bdd_start_level));
    bool state21[3] = {false, false, false};
    assert(!cddContainsState(result.handle(), state21, bdd_start_level));

    result = (b6 & b7 & !b8) | (!b6 & b7 & !b8);
    print_cdd(result, "b6b7!b8or!b6b7!b8", true);

    bool state22[3] = {true, true, false};
    assert(cddContainsState(result.handle(), state22, bdd_start_level));
    bool state23[3] = {false, true, false};
    assert(cddContainsState(result.handle(), state23, bdd_start_level));

    bool state24[3] = {true, false, false};
    assert(!cddContainsState(result.handle(), state24, bdd_start_level));
    bool state25[3] = {false, false, false};
    assert(!cddContainsState(result.handle(), state25, bdd_start_level));

    return result;
}

int main(int argc, char* argv[])
{
    srand(300);
    uint32_t number_of_clocks, number_of_clocks_including_zero, number_of_DBMs, number_of_booleans;
    number_of_clocks = 3;
    number_of_clocks_including_zero = number_of_clocks + 1;
    number_of_DBMs = 2;
    number_of_booleans = 5;

    cdd_init(1000000,100000,100000);
    cdd_add_clocks(number_of_clocks_including_zero);
    int bdd_start_level = cdd_add_bddvar(number_of_booleans);

    orExactractTest(number_of_clocks_including_zero, bdd_start_level);
    orOfBCDDTest( bdd_start_level);
    orExactractWithBddTest(number_of_clocks_including_zero,bdd_start_level);


    cdd cdd_main = test1_CDD_from_random_DBMs(number_of_clocks_including_zero, number_of_DBMs);

    containsDBMTest(number_of_clocks_including_zero,number_of_DBMs);
    reduceTest(number_of_clocks_including_zero,number_of_DBMs);
    test_reduce(number_of_clocks_including_zero);
    equalityTest(number_of_clocks_including_zero,number_of_DBMs);
    negationTest(number_of_clocks_including_zero,number_of_DBMs);
    extractDBMTest(number_of_clocks_including_zero,number_of_DBMs);
    orExactractWithBddTest(number_of_clocks_including_zero,bdd_start_level);
    extractDBMWithBoolsTest(number_of_clocks_including_zero,number_of_DBMs, bdd_start_level);
    cddFromIntervalTest();
    orOfBCDDTest(bdd_start_level);
    restrictTest(  number_of_booleans,  bdd_start_level);
    cdd_main = buildCDDWithBooleansTest(number_of_clocks+1, number_of_DBMs, number_of_booleans, bdd_start_level);
    cdd_main = buildSimpleStaticBDD(bdd_start_level);
    cdd_main = MartijnTest(bdd_start_level);

    cdd_done();
    exit(0);
}



