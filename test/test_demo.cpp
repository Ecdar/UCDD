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

static void print_cdd(cdd to_print, char *name, bool push_negate) {
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
    print_cdd(to_print, "", push_negate);
}

/* test conversion between CDD and DBMs
 */
static void test_conversion(size_t size) {
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
static void test_intersection(size_t size) {
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

static void test_apply_reduce(size_t size) {
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

static void test(const char *name, TestFunction f, size_t size) {
    cout << name << " size = " << size << endl;
    for (uint32_t k = 0; k < LOOP; ++k) {
        PROGRESS();
        f(size);
    }
}


static cdd randomCddFromDBMs(size_t size, int number_of_DBMs) {
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


static void test_reduce(size_t size) {
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

    printf("cdd_bf == cdd1: %i\n", (cdd_bf == cdd1));
    printf("cdd_bf == cdd_tarjan: %i\n", (cdd_bf == cdd_tarjan));
    printf("cdd_bf == cdd_reduce_2: %i\n", (cdd_bf == cdd_reduce_2));
    printf("cdd_bf == cdd_bf: %i\n", (cdd_bf == cdd_bf));

    printf("---\n");

    printf("(!cdd_bf & cdd1) == cdd_false()) && ((cdd_bf & !cdd1) == cdd_false()): %i\n",
           ((!cdd_bf & cdd1) == cdd_false()) && ((cdd_bf & !cdd1) == cdd_false()));
    printf("(!cdd_bf & cdd_tarjan) == cdd_false()) && ((cdd_bf & !cdd_tarjan) == cdd_false()): %i\n",
           ((!cdd_bf & cdd_tarjan) == cdd_false()) && ((cdd_bf & !cdd_tarjan) == cdd_false()));
    printf("(!cdd_bf & cdd_reduce_2) == cdd_false()) && ((cdd_bf & !cdd_reduce_2) == cdd_false()): %i\n",
           ((!cdd_bf & cdd_reduce_2) == cdd_false()) && ((cdd_bf & !cdd_reduce_2) == cdd_false()));

    printf("---\n");


    printf("cdd_reduce(cdd_bf ^ cdd1) == cdd_false(): %i\n", (cdd_reduce(cdd_bf ^ cdd1) == cdd_false()));
    printf("cdd_reduce(cdd_bf ^ cdd_tarjan) == cdd_false(): %i\n", (cdd_reduce(cdd_bf ^ cdd_tarjan) == cdd_false()));
    printf("cdd_reduce(cdd_bf ^ cdd_reduce_2) == cdd_false(): %i\n",
           (cdd_reduce(cdd_bf ^ cdd_reduce_2) == cdd_false()));
    printf("cdd_reduce(cdd_bf ^ cdd_bf) == cdd_false(): %i\n", (cdd_reduce(cdd_bf ^ cdd_bf) == cdd_false()));

    printf("---\n");

// these asserts do not hold, in case a random DBM is already reduced when created
//    assert(((cdd_bf ^ cdd1) == cdd_false()) == false);
//    assert(((cdd_bf ^ cdd_tarjan) == cdd_false()) == true);
//    assert(((cdd_bf ^ cdd_reduce_2) == cdd_false()) == false);
//    assert(((cdd_bf ^ cdd_bf) == cdd_false()) == true);

//    assert(((cdd_tarjan ^ cdd1) == cdd_false()) == false);
//    assert(((cdd_tarjan ^ cdd_tarjan) == cdd_false()) == true);
//    assert(((cdd_tarjan ^ cdd_reduce_2) == cdd_false()) == false);
//    assert(((cdd_tarjan ^ cdd_bf) == cdd_false()) == true);

//    assert(((cdd_reduce_2 ^ cdd1) == cdd_false()) == true);
//    assert(((cdd_reduce_2 ^ cdd_tarjan) == cdd_false())== false);
//    assert(((cdd_reduce_2 ^ cdd_reduce_2) == cdd_false()) == true);
//    assert(((cdd_reduce_2 ^ cdd_bf) == cdd_false())==false);

}


static cdd test1_CDD_from_random_DBMs(size_t size, int numberOfDBMs) {
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
        cdd_result = cdd_reduce(cdd_result);
        print_cdd(cdd_result, "test1_normal", true);

        cdd cdd_negated = !cdd_result;
        cdd_negated = cdd_reduce(cdd_negated);
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
    cdd cdd_result = randomCddFromDBMs(size, number_of_DBMs);
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

    cdd_result = cdd_reduce(cdd_result);

    printf("Extracting first BDM. \n");
    cdd extracted = cdd_extract_dbm(cdd_result, dbm, size);

    printf("Printing the extracted BDM. \n");
    dbm_print(stdout, dbm, size);

    printf("Starting a new CDD based on the extraced DBMS. \n");
    cdd rebuilt = cdd(dbm, size);

    printf("Printing original CDD\n");
    print_cdd(cdd_result, "original", true);

    printf("Printing CDD after extracting\n");
    print_cdd(extracted, "extracted", true);

    while (!cdd_isterminal(extracted.handle()) && cdd_info(extracted.handle())->type != TYPE_BDD) {
        extracted = cdd_reduce(extracted);
        printf("Extracting\n");
        extracted = cdd_extract_dbm(extracted, dbm, size);
        printf("Printing CDD after extracting\n");
        print_cdd(extracted, "extracted_while", true);
        rebuilt |= cdd(dbm, size);
    }

    printf("Printing rebuilt rebuilt CDD \n");
    print_cdd(rebuilt, "rebuilt", true);


    printf("Printing reduced rebuilt CDD \n");
    rebuilt = cdd_reduce(rebuilt);
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

    assert((cdd_result ^ cdd_result) == cdd_false());
    assert(cdd_reduce(cdd_result ^ cdd_result) == cdd_false());
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

    printf("one1 == cdd_false(): %i", one1 == cdd_false());
    printf("two1 == cdd_false(): %i", two1 == cdd_false());

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


static void extractDBMWithBoolsTest(size_t size, int number_of_DBMs, int bdd_start_level)
{
    printf("Running extractDBMWithBoolsTest.\n");
    cdd cdd_result = randomCddFromDBMs(size, number_of_DBMs);
    ADBM(dbm);

    cdd b1 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b2 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b3 = cdd_bddvarpp(bdd_start_level + 2);

    // TODO: make a test for how brackets affect the CDD creation
    cdd cdd_result1 = (cdd_result & (b1 & b2 & !b3)) | (b1 & b2 & b3);
    print_cdd(cdd_result1, "outerOR", true);

    cdd_result = cdd_result & ((b1 & b2 & !b3) | (b1 & b2 & b3));
    cdd_result = cdd_reduce(cdd_result);
    printf("Extracting the BDM. \n");
    cdd extracted = cdd_extract_dbm(cdd_result, dbm, size);

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

    while (!cdd_isterminal(extracted.handle()) && cdd_info(extracted.handle())->type != TYPE_BDD) {
        extracted = cdd_reduce(extracted);
        printf("Extracting\n");
        extracted = cdd_extract_dbm(extracted, dbm, size);
        printf("Printing CDD after extracting\n");
        print_cdd(extracted, "extractedWB_while", true);
        print_cdd(cdd(dbm,size), "dbmWB", true);
        rebuilt |= cdd(dbm, size);
    }

    printf("Printing rebuilt rebuilt CDD \n");
    rebuilt = cdd_reduce(rebuilt);
    print_cdd(rebuilt, "rebuiltWB", true);

    rebuilt = rebuilt & ((b1 & b2 & !b3) | (b1 & b2 & b3));

    assert(cdd_reduce(cdd_result ^ rebuilt) == cdd_false());
}


static void extractDBMAndCDDWithBoolsTest(size_t size, int number_of_DBMs, int bdd_start_level) {
    printf("Running extractDBMWithBoolsTest.\n");
    cdd original = randomCddFromDBMs(size, number_of_DBMs);
    ADBM(dbm);

    cdd b1 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b2 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b3 = cdd_bddvarpp(bdd_start_level + 2);

    // TODO: make a test for how brackets affect the CDD creation
    cdd cdd_result1 = (original & (b1 & b2 & !b3)) | (b1 & b2 & b3);
    print_cdd(cdd_result1, "outerOR", true);

    original = original & ((b1 & b2 & !b3) | (b1 & b2 & b3));
    original = cdd_reduce(original);
    printf("Extracting the BDM. \n");
    extraction_result extracted = cdd_extract_bdd_and_dbm(original);

    printf("Printing the extracted BDM. \n");
    dbm_print(stdout, extracted.dbm, size);

    cdd rebuilt = cdd(extracted.dbm, size);

    printf("Printing original CDD\n");
    print_cdd(original, "originalCB", true);

    cdd reduced = cdd_reduce(original);
    printf("Printing reduced rebuilt CDD\n");
    print_cdd(reduced, "reduced_origCB", true);

    printf("Printing CDD after extracting\n");
    print_cdd(extracted.CDD_part, "extractedCB", true);

    while (!cdd_isterminal((extracted.CDD_part).handle()) && cdd_info((extracted.CDD_part).handle())->type != TYPE_BDD) {
        extracted.CDD_part = cdd_reduce(extracted.CDD_part);
        printf("Extracting\n");
        extracted = cdd_extract_bdd_and_dbm(extracted.CDD_part);
        printf("Printing CDD after extracting\n");
        print_cdd(extracted.CDD_part, "extractedCB_while", true);
        print_cdd(cdd(extracted.dbm,size), "dbmCB", true);
        rebuilt |= cdd(extracted.dbm, size);
    }

    printf("Printing rebuilt rebuilt CDD \n");
    rebuilt = cdd_reduce(rebuilt);
    print_cdd(rebuilt, "rebuiltCB", true);

    rebuilt = rebuilt & ((b1 & b2 & !b3) | (b1 & b2 & b3));

    assert(cdd_reduce(original ^ rebuilt) == cdd_false());
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
    printf("Checking if the last added DBM is included: %i\n", cdd_contains(cdd_result, dbm, size));
    assert(cdd_contains(cdd_result, dbm, size));

    ADBM(dbm1);
    printf("Extracting a BDM. \n");
    cdd_result = cdd_reduce(cdd_result);
    cdd extracted = cdd_extract_dbm(cdd_result, dbm1, size);

    dbm_print(stdout, dbm1, size);

    printf("Checking if the last added DBM is included: %i\n", cdd_contains(extracted, dbm, size));
    assert(!cdd_contains(extracted, dbm1, size));

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
    cdd b1 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b2 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b3 = cdd_bddvarpp(bdd_start_level + 2);
    cdd b4 = cdd_bddvarpp(bdd_start_level + 3);

    printf("Before adding boolean vars, the inclusion check is %i \n", cdd_contains(cdd_result, dbm, size));
    cdd_result = cdd_result & (b1 & b2 & !b3) | (b1 & b2 & b3);
    printf("After adding boolean vars, the inclusion check is %i \n", cdd_contains(cdd_result, dbm, size));
    assert(cdd_contains(cdd_result, dbm, size));
    return cdd_result;
}

static bool cddContainsBoolStateRec(ddNode *r, bool state[], int bdd_start_level, int index, bool negated) {
    assert(cdd_info(r)->type == TYPE_BDD);
    bddNode *node = bdd_node(r);

    if (node->level != index + bdd_start_level)
        return (cddContainsBoolStateRec(r, state, bdd_start_level, index + 1, negated));

    if (node->high == cddtrue) {
        if (state[index]) return true ^ negated ^ cdd_is_negated(r);
    }
    if (node->high == cddfalse) {
        if (state[index]) return false ^ negated ^ cdd_is_negated(r);
    }
    if (node->low == cddtrue) {
        if (!state[index]) return true ^ negated ^ cdd_is_negated(r);
    }
    if (node->low == cddfalse) {
        if (!state[index]) return false ^ negated ^ cdd_is_negated(r);
    }

    if (state[index])
        return cddContainsBoolStateRec(node->high, state, bdd_start_level, index + 1, negated ^ cdd_is_negated(r));
    else
        return cddContainsBoolStateRec(node->low, state, bdd_start_level, index + 1, negated ^ cdd_is_negated(r));

}


static bool cddContainsStateRec(ddNode *r, bool state[], int bdd_start_level, int index, bool negated) {

    if (cdd_info(r)->type == TYPE_BDD)
        return cddContainsBoolStateRec(r, state, bdd_start_level, index, negated);
    else {
        // TODO: this part is just skipped at the moment, add support for CDDs
        printf("encountrered CDD");
        cddNode *node = cdd_node(r);
        return cddContainsStateRec(node->next, state, bdd_start_level, index, negated);
    }

}

bool cddContainsState(ddNode *cdd_, bool state[], int bdd_start_level) {

    return cddContainsStateRec(cdd_, state, bdd_start_level, 0, false);
}

bool cddFromIntervalTest() {
    // note that 5 means 2 including, while the 10 below means 5 non including
    cdd smaller = cdd_interval(1, 0, 0, 5);
    print_cdd(smaller, "smaller", true);
    cdd larger = cdd_interval(1, 0, 0, 10);
    print_cdd(larger, "larger", true);
    assert(cdd_reduce(larger - smaller) != cdd_false());
    assert(cdd_reduce(smaller - larger) == cdd_false());
}

bool orOfBCDDTest(int32_t bdd_start_level) {
    // note that 5 means 2 including, while the 10 below means 5 non including
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);

    cdd smaller = cdd_interval(1, 0, 0, 5);
    smaller &= b6;
    print_cdd(smaller, "smaller", true);
    cdd larger = cdd_interval(1, 0, 6, 10);
    larger &= !b6;
    print_cdd(larger, "larger", true);
    cdd result = larger | smaller;
    cdd_reduce(result);
    print_cdd(result, "orOfBCDD", true);
    return true;
    //TODO: Figure out good assert
}

bool orExactractTest(size_t size, int32_t bdd_start_level) {
    // note that 5 means 2 including, while the 10 below means 5 non including
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);

    cdd smaller = cdd_intervalpp(1, 0, 0, 5);
    smaller &= cdd_interval(2, 0, 0, dbm_LS_INFINITY);
    smaller &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    smaller &= b6;
    print_cdd(smaller, "smaller", true);
    cdd larger = cdd_intervalpp(1, 0, 6, 10);
    larger &= cdd_interval(2, 0, 0, dbm_LS_INFINITY);
    larger &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
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
    cdd dbmcdd = cdd(dbm, size);
    print_cdd(dbmcdd, "dbm", true);

    cdd extract1 = cdd_extract_dbm(extract, dbm, size);
    print_cdd(extract, "extract1", true);

}


bool predtTest(size_t size, int32_t bdd_start_level) {
    // note that 5 means 2 including, while the 10 below means 5 non including
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);

    cdd smaller = cdd_intervalpp(1, 0, 0, 5);
    smaller &= cdd_interval(2, 0, 0, dbm_LS_INFINITY);
    smaller &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    smaller &= b6;
    print_cdd(smaller, "smaller", true);
    cdd larger = cdd_intervalpp(1, 0, 6, 10);
    larger &= cdd_interval(2, 0, 0, dbm_LS_INFINITY);
    larger &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    larger &= !b6;
    print_cdd(larger, "larger", true);
    cdd result = larger | smaller;
    cdd_reduce(result);
    print_cdd(result, "orOfBCDD", true);

    result = cdd_predt(result,smaller);

    print_cdd(result, "restultPredt", true);

}



bool orExactractWithBddTest(size_t size, int32_t bdd_start_level) {
    // note that 5 means 2 including, while the 10 below means 5 non including
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);

    cdd smaller = cdd_intervalpp(1, 0, 0, 5);
    smaller &= cdd_interval(2, 0, 0, dbm_LS_INFINITY);
    smaller &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    smaller &= b6;
    print_cdd(smaller, "smaller", true);
    cdd larger = cdd_intervalpp(1, 0, 6, 10);
    larger &= cdd_interval(2, 0, 0, dbm_LS_INFINITY);
    larger &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    larger &= !b6;
    print_cdd(larger, "larger", true);
    cdd result = larger | smaller;
    cdd_reduce(result);
    print_cdd(result, "orOfBCDD", true);


    cdd cdd_at_bottom;
    ADBM(dbm);
    // TODO: This is deprecated!!!
    cdd_at_bottom = cdd_extract_bdd(result, dbm, size);
    cdd extract = cdd_extract_dbm(result, dbm, size);
    printf("came out of the extraction\n");
    printf("Current pointer value: %p\n", cdd_at_bottom.handle());

    extract = cdd_reduce(extract);

    cdd removed = cdd(dbm, size);
    removed = cdd_reduce(removed);

    cdd_at_bottom = cdd_reduce(cdd_at_bottom);
    print_cdd(extract, "extract", true);
    print_cdd(removed, "removed", true);
    print_cdd(cdd_at_bottom, "cdd_at_bottom", true);

    cdd cdd_at_bottom1;
    ADBM(dbm1);
    cdd_at_bottom1 = cdd_extract_bdd(extract, dbm1, size);
    cdd extract1 = cdd_extract_dbm(extract, dbm1, size);
    printf("came out of the extraction\n");

    extract1 = cdd_reduce(extract1);
    cdd removed1 = cdd(dbm1, size);
    removed1 = cdd_reduce(removed1);

    cdd_at_bottom1 = cdd_reduce(cdd_at_bottom1);
    print_cdd(extract1, "extract1", true);
    print_cdd(removed1, "removed1", true);
    print_cdd(cdd_at_bottom1, "cdd_at_bottom1", true);


    cdd rebuilt = (removed & cdd_at_bottom) | (removed1 & cdd_at_bottom1);
    rebuilt = cdd_reduce(rebuilt);

    print_cdd(rebuilt, "rebuilt", true);
    assert(cdd_equiv(rebuilt, result));


    return true;
    //TODO: Figure out good assert
}


bool extractEdgeCasesTest(size_t size, int32_t bdd_start_level) {
    // note that 5 means 2 including, while the 10 below means 5 non including
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b7 = cdd_bddvarpp(bdd_start_level + 1);

    cdd smaller = cdd_intervalpp(1, 0, 0, 5);
    smaller &= cdd_interval(2, 0, 0, dbm_LS_INFINITY);
    smaller &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    //smaller &= b6;
    print_cdd(smaller, "smaller", true);
    cdd larger = cdd_intervalpp(1, 0, 6, 10);
    larger &= cdd_interval(2, 0, 0, dbm_LS_INFINITY);
    larger &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    //larger &= !b6;
    print_cdd(larger, "larger", true);
    cdd result = larger | smaller;
    cdd_reduce(result);
    print_cdd(result, "orOfBCDD", true);


    cdd cdd_at_bottom;
    ADBM(dbm);

    cdd extract = cdd_extract_bdd(result, dbm, size);
    print_cdd(extract,"empty_bdd",true);


    ADBM(dbm1);
    cdd pure_bdd = !b6 & b7;
    cdd extractBDD = cdd_extract_bdd(pure_bdd, dbm1, size);
    print_cdd(extractBDD,"empty_bdd",true);
    cdd remainder = cdd_extract_dbm(pure_bdd, dbm1, size);
    dbm_print(stdout,dbm1, size);
    remainder = cdd_reduce(remainder);
    //ADBM(dbm2)
    //dbm_init(dbm2, size);
    //remainder &= cdd(dbm2,size);
    remainder = cdd_remove_negative(remainder);
    print_cdd(remainder,"remainder1",true);

    return true;
    //TODO: Figure out good assert
}




int nstrict(int inputNumber)
{
    return inputNumber*2 +1;
}
int strict(int inputNumber)
{
    return inputNumber*2 ;
}

static inline void base_resetBits(uint32_t* bits, size_t n)
{
    assert(n == 0 || bits);
    for (; n != 0; --n)
        *bits++ = 0;
}


void delayTest(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level) {
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b7 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b8 = cdd_bddvarpp(bdd_start_level + 2);
    cdd b9 = cdd_bddvarpp(bdd_start_level + 3);
    cdd stateBeforeTrans = cdd_true();

    // Assume we start in an unconstrained state, with three clocks and 4 boolean variables
    // We take a transition with guard (x1>5 && b6==true) | (x2<4 && b7==false)
    cdd left = cdd_intervalpp(1, 0, strict(5), dbm_LS_INFINITY);
    left &= cdd_interval(2, 0, 0, dbm_LS_INFINITY);
    left &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    left &= b6;
    print_cdd(left, "left", true);
    cdd right = cdd_intervalpp(2, 0, 0, strict(4));
    right &= cdd_interval(1, 0, 0, dbm_LS_INFINITY);
    right &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    right &= !b7;
    print_cdd(right, "right", true);
    left = cdd_reduce(left);
    right = cdd_reduce(right);
    print_cdd(right, "rightRed", true);

    cdd guard = left | right;
    cdd stateAfterGuard = stateBeforeTrans & guard;
    stateAfterGuard = cdd_reduce(stateAfterGuard);
    cdd_delay(stateAfterGuard);
}


void downTest(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level) {
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b7 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b8 = cdd_bddvarpp(bdd_start_level + 2);
    cdd b9 = cdd_bddvarpp(bdd_start_level + 3);
    cdd stateBeforeTrans = cdd_true();

    // Assume we start in an unconstrained state, with three clocks and 4 boolean variables
    // We take a transition with guard (x1>5 && b6==true) | (x2<4 && b7==false)
    cdd left = cdd_intervalpp(1, 0, strict(5), dbm_LS_INFINITY);
    left &= cdd_interval(2, 0, 0, dbm_LS_INFINITY);
    left &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    left &= b6;
    print_cdd(left, "left", true);
    cdd right = cdd_intervalpp(2, 0, 0, strict(4));
    right &= cdd_interval(1, 0, 0, dbm_LS_INFINITY);
    right &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    right &= !b7;
    print_cdd(right, "right", true);
    left = cdd_reduce(left);
    right = cdd_reduce(right);
    print_cdd(right, "rightRed", true);

    cdd guard = left | right;
    cdd stateAfterGuard = stateBeforeTrans & guard;
    stateAfterGuard = cdd_reduce(stateAfterGuard);
    cdd_past(stateAfterGuard);
}

void apply_reset_test(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level)
{
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b7 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b8 = cdd_bddvarpp(bdd_start_level + 2);
    cdd b9 = cdd_bddvarpp(bdd_start_level + 3);
    cdd stateBeforeTrans = cdd_true();

    // Assume we start in an unconstrained state, with three clocks and 4 boolean variables
    // We take a transition with guard (x1>5 && b6==true) | (x2<4 && b7==false)
    cdd left = cdd_intervalpp(1, 0, 0, strict(5));
    left &= cdd_intervalpp(2, 0, 0, strict(5));
    left &= cdd_intervalpp(3, 0, 0, dbm_LS_INFINITY);
    left &= cdd_intervalpp(1, 2, 0, nstrict(0));
    left &= cdd_intervalpp(2, 1, 0, nstrict(0));
    left = cdd_reduce(left);
    cdd guard = left;
    cdd stateAfterGuard = stateBeforeTrans & guard;
    stateAfterGuard = cdd_reduce(stateAfterGuard);
    print_cdd(stateAfterGuard, "afterGuard", true);

    // the transition has an update of x1=0 & b7=true
    // 1. apply the booleans
    int clock_array[1];
    int bool_array[0];
    int clock_values[1];
    int bool_values[0];
    clock_array[0] = 1;
    clock_values[0] = 0;
//    clock_array[1] = 2;
//    clock_values[1] = 0;
    int* clkArrPtr = clock_array;
    int* boolArrPtr = bool_array;
    int* clkVluPtr = clock_values;
    int* boolVluPtr = bool_values;

    cdd afterReset = cdd_apply_reset(stateAfterGuard, clkArrPtr, clkVluPtr, 1,  boolArrPtr, boolVluPtr,0);

    print_cdd(afterReset, "afterResets", true);
}

void bdd_thing_test(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level)
{
    cdd b1 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b2 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b3 = cdd_bddvarpp(bdd_start_level + 2);
    int number_of_booleans_overwrite = 3;
    cdd cdd_result = (b1 | (b2 & b3));
    bdd_arrays  arys = cdd_bdd_to_array(cdd_result, number_of_booleans_overwrite);
    printf("numTraces: %i, numBools: %i \n", arys.numTraces, arys.numBools);

    printf("vars: \n");
    for (int i=0; i< arys.numTraces; i++)
    {
        printf("trace: \n");
        for (int j=0; j< arys.numBools; j++)
           printf("%i ", arys.vars[i*arys.numBools + j] );
        printf("\n");
    }
    printf("values: \n");
    for (int i=0; i< arys.numTraces; i++)
    {
        printf("trace: \n");
        for (int j=0; j< arys.numBools; j++)
            printf("%i ", arys.values[i*arys.numBools + j]);
        printf("\n");
    }
    printf("done: \n");
    delete []arys.vars;
    delete []arys.values;
}

void bdd_conjunction_test(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level)
{
    cdd b1 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b2 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b3 = cdd_bddvarpp(bdd_start_level + 2);
    int number_of_booleans_overwrite = 3;
    cdd cdd_result = (b1 & !b2 & !b3);
    bdd_arrays  arys = cdd_bdd_to_array(cdd_result, number_of_booleans_overwrite);
    printf("numTraces: %i, numBools: %i \n", arys.numTraces, arys.numBools);



    printf("vars: \n");
    for (int i=0; i< arys.numTraces; i++)
    {
        printf("trace: \n");
        for (int j=0; j< arys.numBools; j++)
            printf("%i ", arys.vars[i*(arys.numBools) + j] );
        printf("\n");
    }
    printf("values: \n");
    for (int i=0; i< arys.numTraces; i++)
    {
        printf("trace: \n");
        for (int j=0; j< arys.numBools; j++)
            printf("%i ", arys.values[i*(arys.numBools) + j] );
        printf("\n");
    }
    printf("done: \n");
    delete []arys.vars;
    delete []arys.values;

}


void bdd_test_big(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level)
{
    cdd b1 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b2 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b3 = cdd_bddvarpp(bdd_start_level + 2);
    cdd b4 = cdd_bddvarpp(bdd_start_level + 3);
    cdd cdd_result = ((b1 & !b2 & !b3) | (b2 & !b1 & !b4)) & !b4;
    print_cdd(cdd_result, "out",true);
    bdd_arrays  arys = cdd_bdd_to_array(cdd_result, number_of_booleans-1);
    printf("numTraces: %i, numBools: %i \n", arys.numTraces, arys.numBools);

    printf("vars: \n");
    for (int i=0; i< arys.numTraces; i++)
    {
        printf("trace: \n");
        for (int j=0; j< arys.numBools; j++)
            printf("%i ", arys.vars[i*(arys.numBools) + j] );
        printf("\n");
    }
    printf("values: \n");
    for (int i=0; i< arys.numTraces; i++)
    {
        printf("trace: \n");
        for (int j=0; j< arys.numBools; j++)
            printf("%i ", arys.values[i*(arys.numBools) + j]);
        printf("\n");
    }
    printf("done: \n");
    delete []arys.vars;
    delete []arys.values;

}

void apply_reset_test2(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level)
{
    cdd stateBeforeTrans = cdd_true();
    cdd left = cdd_intervalpp(1, 0, 0, nstrict(3));
    left &= cdd_intervalpp(3, 0, 0, dbm_LS_INFINITY);
    left &= cdd_intervalpp(1, 2, strict(0), nstrict(0)); // TODO: someone explain to me me why the first has to be strict?
    left = cdd_reduce(left);
    cdd guard = left;
    cdd stateAfterGuard = stateBeforeTrans & guard;
    stateAfterGuard = cdd_reduce(stateAfterGuard);
    print_cdd(stateAfterGuard, "afterGuard", true);
    ADBM(dbm);
    cdd_extract_dbm(stateAfterGuard, dbm,size);

    int clock_array[1];
    int bool_array[0];
    int clock_values[1];
    int bool_values[0];
    clock_array[0] = 1;
    clock_values[0] = 0;
    int* clkArrPtr = clock_array;
    int* boolArrPtr = bool_array;
    int* clkVluPtr = clock_values;
    int* boolVluPtr = bool_values;
    int numClockResets = 1;

    cdd afterReset = cdd_apply_reset(stateAfterGuard, clkArrPtr, clkVluPtr, numClockResets,  boolArrPtr, boolVluPtr,0);
//    cdd afterReset = cdd_exist(stateAfterGuard,  boolArrPtr, clkArrPtr, 0, 1);

    print_cdd(afterReset, "afterReset", true);
}


void free_clock_test(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level)
{
    cdd stateBeforeTrans = cdd_true();
    cdd left = cdd_intervalpp(1, 0, nstrict(0), nstrict(3));
    left &= cdd_intervalpp(3, 0, 0, dbm_LS_INFINITY);
    left &= cdd_intervalpp(2, 1, nstrict(7), nstrict(13)); // TODO: someone explain to me me why the first has to be strict?
    left = cdd_reduce(left);
    cdd guard = left;
    cdd stateAfterGuard = stateBeforeTrans & guard;
    stateAfterGuard = cdd_reduce(stateAfterGuard);
    print_cdd(stateAfterGuard, "afterGuard2", true);
    ADBM(dbm);
    cdd_extract_dbm(stateAfterGuard, dbm,size);
    dbm_print(stdout,dbm,size);

    int clock_array[1];
    int bool_array[0];
    int clock_values[1];
    int bool_values[0];
    clock_array[0] = 1;
    clock_values[0] = 0;
    int* clkArrPtr = clock_array;
    int* boolArrPtr = bool_array;
    int* clkVluPtr = clock_values;
    int* boolVluPtr = bool_values;
    int numClockResets = 1;

    //cdd afterReset = cdd_apply_reset(stateAfterGuard, clkArrPtr, clkVluPtr, numClockResets,  boolArrPtr, boolVluPtr,0);
    //    cdd afterReset = cdd_exist(stateAfterGuard,  boolArrPtr, clkArrPtr, 0, 1);

    dbm_freeClock(dbm, 1,size);
    dbm_print(stdout,dbm,size);
    cdd* afterFree = new cdd(dbm,size);

    print_cdd(*afterFree, "afterReset", true);
}


void delay_true_test(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level)
{
    cdd t = cdd_true();
    print_cdd(t, true);
    t= cdd_delay(t);
    print_cdd(t, true);
}

    void traverseTransitionTest(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level) {
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b7 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b8 = cdd_bddvarpp(bdd_start_level + 2);
    cdd b9 = cdd_bddvarpp(bdd_start_level + 3);
    cdd stateBeforeTrans = cdd_true();

    // Assume we start in an unconstrained state, with three clocks and 4 boolean variables
    // We take a transition with guard (x1>5 && b6==true) | (x2<4 && b7==false)
    cdd left = cdd_intervalpp(1, 0, strict(5), dbm_LS_INFINITY);
    left &= cdd_intervalpp(2, 0, 0, dbm_LS_INFINITY);
    left &= cdd_intervalpp(3, 0, 0, dbm_LS_INFINITY);
    left &= b6;
    print_cdd(left, "left", true);
    cdd right = cdd_intervalpp(2, 0, 0, strict(4));
    right &= cdd_intervalpp(1, 0, 0, dbm_LS_INFINITY);
    right &= cdd_intervalpp(3, 0, 0, dbm_LS_INFINITY);
    right &= !b7;
    print_cdd(right, "right", true);
    left = cdd_reduce(left);
    right = cdd_reduce(right);
    print_cdd(right, "rightRed", true);

    cdd guard = left | right;
    cdd stateAfterGuard = stateBeforeTrans & guard;
    stateAfterGuard= cdd_reduce(stateAfterGuard);
    print_cdd(stateAfterGuard, "afterGuard", true);

    // the transition has an update of x1=0 & b7=true
    // 1. apply the booleans
    int nice_array[0];
    int nice_array_bool[1];
    nice_array_bool[0]=bdd_start_level + 1;
    int *nicePtr = nice_array;
    int *nicePtrBool = nice_array_bool;



    cdd stateAfterBoolExist = cdd_exist(stateAfterGuard, nicePtrBool, nicePtr, 1,0);



    print_cdd(stateAfterBoolExist, "afterBoolExist", true);
    cdd stateAfterBool = stateAfterBoolExist & b7;
    print_cdd(stateAfterBool, "afterBoolReset", true);
    // 2. apply the clock update
    cdd rebuilt = cdd_false();
    cdd stateAfterBool_second_approach = stateAfterBool;
    ADBM(dbm);
    cdd cdd_at_bottom;
    while (!cdd_isterminal(stateAfterBool.handle()) && cdd_info(stateAfterBool.handle())->type != TYPE_BDD) {
        stateAfterBool = cdd_reduce(stateAfterBool);
        cdd_at_bottom = cdd_extract_bdd(stateAfterBool, dbm, size);
        print_cdd(cdd_at_bottom, "cdd_at_bottom", true);
        stateAfterBool = cdd_extract_dbm(stateAfterBool, dbm, size);
        print_cdd(stateAfterBool, "beforeReduce", true);
        stateAfterBool = cdd_reduce(stateAfterBool);
        print_cdd(stateAfterBool, "extractedOneDBM", true);
        dbm_updateValue(dbm,size,1,0);
        rebuilt |= (cdd(dbm, size) & cdd_at_bottom);
        print_cdd(rebuilt, "resultOfCurrentIteration", true);

    }
    // We take a transition with guard (x1>5 && b6==true) | (x2<4 && b7==false)
    // the transition has an update of x1=0 & b7=true

}






// functions we want to expose:
// input enabledness:
// - complement (should be there)
//
// forward transitions:
//  - existential quantification on bools
//
// backward transition:
// - existential quantification on bools and clocks ?
//
// general BDD handling:
// - print
// - extractMetaFederation
// - isTerminal
// - BCDD to guard
//   - is there a better way than extracting DBM by BDM?
//   - to be done on the C side? Yes ---  But how to return it? as a string?
//   - do we need a way to get variable names into the BCDD library?
//   - can we in the GUI display the BCDD for an edge?
//
// -






void inputEnableTest(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level) {
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b7 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b8 = cdd_bddvarpp(bdd_start_level + 2);
    cdd b9 = cdd_bddvarpp(bdd_start_level + 3);
    cdd stateBeforeTrans = cdd_true();

    // Assume we have two output transitions with
    // guard 1: (x1>5 && b6==true) | (x2<4 && b7==false)
    // and guard 2: (x2<3 && b6==false) | (x2>4 && b7 && b8)
    cdd left = cdd_intervalpp(1, 0, strict(5), dbm_LS_INFINITY);
    left &= cdd_interval(2, 0, 0, dbm_LS_INFINITY);
    left &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    left &= b6;
    print_cdd(left, "left", true);
    cdd right = cdd_intervalpp(2, 0, 0, strict(4));
    right &= cdd_interval(1, 0, 0, dbm_LS_INFINITY);
    right &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    right &= !b7;
    print_cdd(right, "right", true);
    left = cdd_reduce(left);
    right = cdd_reduce(right);
    print_cdd(right, "rightRed", true);
    cdd guard1 = left | right;

    left = cdd_intervalpp(2, 0, 0, strict(3));
    left &= cdd_interval(1, 0, 0, dbm_LS_INFINITY);
    left &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    left &= !b6;
    print_cdd(left, "left", true);
    right = cdd_intervalpp(2, 0, strict(4), dbm_LS_INFINITY);
    right &= cdd_interval(1, 0, 0, dbm_LS_INFINITY);
    right &= cdd_interval(3, 0, 0, dbm_LS_INFINITY);
    right &= b7 & b8;
    print_cdd(right, "right", true);
    left = cdd_reduce(left);
    right = cdd_reduce(right);
    print_cdd(right, "rightRed", true);
    cdd guard2 = left | right;


    cdd mergedInputs = guard1 | guard2;
    mergedInputs= cdd_reduce(mergedInputs);
    print_cdd(mergedInputs, "mergedInputs", true);

    cdd complement = !mergedInputs;
    // TODO: MAKE ASSERT

}




void existTest(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level) {
    cdd cdd_part = randomCddFromDBMs(size, number_of_DBMs);
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b7 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b8 = cdd_bddvarpp(bdd_start_level + 2);
    cdd b9 = cdd_bddvarpp(bdd_start_level + 3);
    cdd bdd_part = (!b6 & !b7) | (!b8 & b9);
    cdd result = cdd_part & bdd_part;
    const int num_bools =1;
    const int num_clocks=1;
    int arr[num_clocks] = {1};
    int *clockPtr = arr;
    int arr1[num_bools] = {6};
    int *boolPtr = arr1;
    cdd result1 = cdd_exist(result, boolPtr, clockPtr, num_bools,num_clocks);
    result1 = cdd_reduce(result1);
    print_cdd(result, "pre_exist_result", true);
    print_cdd(result1, "exist_result", true);

    cdd result2 = cdd_exist(result1, boolPtr, clockPtr, num_bools,num_clocks);
    result2 = cdd_reduce(result2);
    print_cdd(result2, "exist_result2", true);

    cdd  result3 = cdd_exist(result2, boolPtr, clockPtr, num_bools,num_clocks);
    result3 = cdd_reduce(result3);
    print_cdd(result3, "exist_result3", true);
    //assert(result3==cdd_false());
}





void existTest1(size_t size, int number_of_DBMs, int32_t number_of_booleans, int32_t bdd_start_level) {
    cdd cdd_part = randomCddFromDBMs(size, number_of_DBMs);
    const int num_bools =1;
    const int num_clocks=0;
    int arr[num_clocks] = {};
    int *clockPtr = arr;
    int arr1[num_bools] = {6};
    int *boolPtr = arr1;
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);
    cdd result1 = cdd_transition_back(cdd_part, cdd_true(), b6, clockPtr, num_clocks,boolPtr,num_bools);
    print_cdd(result1, "exist_result_resetting_bools", true);

    cdd result2 = cdd_exist(result1, boolPtr, clockPtr, num_bools,num_clocks);
    result2 = cdd_reduce(result2);
    print_cdd(result2, "exist_result2", true);

    cdd  result3 = cdd_exist(result2, boolPtr, clockPtr, num_bools,num_clocks);
    result3 = cdd_reduce(result3);
    print_cdd(result3, "exist_result3", true);
    //assert(result3==cdd_false());
}


static cdd MartijnTest(int bdd_start_level) {
    cdd b6 = cdd_bddvarpp(bdd_start_level + 0);
    cdd b7 = cdd_bddvarpp(bdd_start_level + 1);
    cdd b8 = cdd_bddvarpp(bdd_start_level + 2);
    cdd b9 = cdd_bddvarpp(bdd_start_level + 3);

    cdd result;
    // single traces
    result = (!b6 & !b7 & !b8 & b9);
    print_cdd(result, "!b6!b7!b8b9", true);
    bool state[4] = {false, false, false, true};
    assert(cddContainsState(result.handle(), state, bdd_start_level));
    bool state1[4] = {false, false, true, true};
    assert(!cddContainsState(result.handle(), state1, bdd_start_level));


    result = (!b6 & !b7 & b8 & b9);
    print_cdd(result, "!b6!b7b8b9", true);
    bool state2[4] = {false, false, true, true};
    assert(cddContainsState(result.handle(), state2, bdd_start_level));
    bool state3[4] = {false, false, false, true};
    assert(!cddContainsState(result.handle(), state3, bdd_start_level));

    result = (!b6 & b7 & b8 & b9);
    print_cdd(result, "!b6b7b8b9", true);
    bool state4[4] = {false, true, true, true};
    assert(cddContainsState(result.handle(), state4, bdd_start_level));
    bool state5[4] = {false, false, false, true};
    assert(!cddContainsState(result.handle(), state5, bdd_start_level));

    result = (!b6 & b7 & b8 & !b9);
    print_cdd(result, "!b6b7b8!b9", true);

    bool state6[4] = {false, true, true, false};
    assert(cddContainsState(result.handle(), state6, bdd_start_level));
    bool state7[4] = {false, false, false, true};
    assert(!cddContainsState(result.handle(), state7, bdd_start_level));

    result = (b6 & b7 & !b8 & !b9);
    print_cdd(result, "b6b7!b8!b9", true);

    bool state8[4] = {true, true, false, false};
    assert(cddContainsState(result.handle(), state8, bdd_start_level));
    bool state9[4] = {false, false, false, true};
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

int main(int argc, char *argv[]) {

    uint32_t number_of_clocks, number_of_clocks_including_zero, number_of_DBMs, number_of_booleans;
    number_of_clocks = 3;
    number_of_clocks_including_zero = number_of_clocks + 1;
    number_of_DBMs = 3;
    number_of_booleans = 5;

    cdd_init(1000000, 100000, 100000);
    cdd_add_clocks(number_of_clocks_including_zero);
    int bdd_start_level = cdd_add_bddvar(number_of_booleans);
    cdd cdd_main;
    bool run_all = false;
    for (int i = 1; i <= 1; i++) {
        printf("running tests with seed %i\n", i);
        srand(i); //
        printf("Running the tests \n");


        //existTest(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);
        existTest1(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);
        //bdd_thing_test(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);
        //bdd_conjunction_test(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);
        //bdd_test_big(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);

        // delay_true_test(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);
       // apply_reset_test2(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);
       // free_clock_test(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);
//        traverseTransitionTest(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);
        if (run_all) {
            predtTest(number_of_clocks_including_zero, bdd_start_level);
            extractDBMWithBoolsTest(number_of_clocks_including_zero, number_of_DBMs, bdd_start_level);
            extractDBMAndCDDWithBoolsTest(number_of_clocks_including_zero, number_of_DBMs, bdd_start_level);

            traverseTransitionTest(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans,
                                   bdd_start_level);
            delayTest(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);
            downTest(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);

            extractEdgeCasesTest(number_of_clocks_including_zero, bdd_start_level);

            existTest(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);
            traverseTransitionTest(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans,
                                   bdd_start_level);
            inputEnableTest(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans, bdd_start_level);
            test_reduce(number_of_clocks_including_zero);

            orExactractWithBddTest(
                4, bdd_start_level);  // hard coded number of clocks needed to the the use ot cdd_interval
            orExactractTest(number_of_clocks_including_zero, bdd_start_level);
            orOfBCDDTest(bdd_start_level);
            cdd cdd_main;
            cdd_main = test1_CDD_from_random_DBMs(number_of_clocks_including_zero, number_of_DBMs);
            containsDBMTest(number_of_clocks_including_zero, number_of_DBMs);
            reduceTest(number_of_clocks_including_zero, number_of_DBMs);
            equalityTest(number_of_clocks_including_zero, number_of_DBMs);
            negationTest(number_of_clocks_including_zero, number_of_DBMs);
            extractDBMTest(number_of_clocks_including_zero, number_of_DBMs);
            extractDBMWithBoolsTest(number_of_clocks_including_zero, number_of_DBMs, bdd_start_level);

            cddFromIntervalTest();
            orOfBCDDTest(bdd_start_level);
            cdd_main = buildCDDWithBooleansTest(number_of_clocks_including_zero, number_of_DBMs, number_of_booleans,
                                                bdd_start_level);
            cdd_main = buildSimpleStaticBDD(bdd_start_level);
            cdd_main = MartijnTest(bdd_start_level);
        }

        printf("finished tests with seed %i\n", i);


        printf("done %i\n", i);
    }

    cdd_done();

    cdd_init(100,100,100);
    cdd_add_clocks(3);
    int start_level = cdd_add_bddvar(1);
    cdd nb6 = cdd_bddnvarpp(start_level + 0);
    bdd_arrays arys = cdd_bdd_to_array(nb6,1);


    printf("vars: \n");
    for (int i=0; i< arys.numTraces; i++)
    {
        printf("trace: \n");
        for (int j=0; j< arys.numBools; j++)
            printf("%i ", arys.vars[i*arys.numBools + j] );
        printf("\n");
    }
    printf("values: \n");
    for (int i=0; i< arys.numTraces; i++)
    {
        printf("trace: \n");
        for (int j=0; j< arys.numBools; j++)
            printf("%i ", arys.values[i*arys.numBools + j]);
        printf("\n");
    }
    printf("done: \n");
    delete []arys.vars;
    delete []arys.values;



    cdd b6 = cdd_bddnvarpp(start_level + 0);
    bdd_arrays arys1 = cdd_bdd_to_array(b6,1);


    printf("vars: \n");
    for (int i=0; i< arys1.numTraces; i++)
    {
        printf("trace: \n");
        for (int j=0; j< arys1.numBools; j++)
            printf("%i ", arys1.vars[i*arys1.numBools + j] );
        printf("\n");
    }
    printf("values: \n");
    for (int i=0; i< arys1.numTraces; i++)
    {
        printf("trace: \n");
        for (int j=0; j< arys1.numBools; j++)
            printf("%i ", arys1.values[i*arys1.numBools + j]);
        printf("\n");
    }
    printf("done: \n");
    delete []arys1.vars;
    delete []arys1.values;


    cdd_done();





/* Below shows the crash that happens when you try to extract a CDD from a pure BDD
    cdd_init(1000000, 100000, 100000);
    int bdd_start_level_new = cdd_add_bddvar(3);
    cdd main = cdd_true();
    main &= cdd_bddvarpp(bdd_start_level_new + 0);
    main &= cdd_bddnvarpp(bdd_start_level_new + 1);
    main &= cdd_bddnvarpp(bdd_start_level_new + 2);
    size_t size = 0;
    while (!cdd_isterminal(main.handle())) {
        ADBM(dbm);
        printf("started while\n");
        cdd bdd = cdd_extract_bdd(main,dbm,size);
        main = cdd_false();

        printf("Printing CDD after extracting\n");
    }

    while (!cdd_isterminal(main.handle())) {

        printf("started while\n");
        extraction_result extracted;
        extracted = cdd_extract_bdd_and_dbm(main);
        main = extracted.CDD_part;

        printf("Printing CDD after extracting\n");
        print_cdd(extracted.BDD_part, "extractedBDD_while", true);
    }

*/
    std::cerr << "Completed Test Cases" << std::endl;
    exit(0);
}



