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

static void print_cdd(cdd to_print, char* name) {
    char filename[30];
    sprintf(filename, "%s_%d.dot", name, printCounter);
    printf("Printing cdd %s to file : \n", name);
    FILE *fp_main;
    fp_main = fopen(filename, "w");
    cdd_fprintdot(fp_main, to_print);
    fclose(fp_main);

    printCounter++;
}

static void print_cdd(cdd to_print) {
    print_cdd(to_print, "");
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

static void test_reduce(size_t size)
{
    cdd cdd1, cdd2, cdd3;
    ADBM(dbm);

    cdd1 = cdd_false();
    for (uint32_t j = 0; j < 5; j++) {
        DBM_GEN(dbm);
        cdd1 |= cdd(dbm, size);
    }

    cdd2 = cdd_reduce(cdd1);
    Timer timer;
    cdd2 = cdd(cdd_bf_reduce(cdd1.handle()));
    time_reduce += timer.getElapsed();
    cdd3 = cdd(cdd_bf_reduce(cdd1.handle()));
    time_bf += timer.getElapsed();

//    print_cdd(cdd2, "cdd2");
//    print_cdd(cdd3, "cdd3");

    cdd3 = cdd_reduce(cdd3);

    assert(cdd_reduce(cdd2 ^ cdd3) == cdd_false());

    // assert(cdd2 == cdd3);
}

static void test(const char* name, TestFunction f, size_t size)
{
    cout << name << " size = " << size << endl;
    for (uint32_t k = 0; k < LOOP; ++k) {
        PROGRESS();
        f(size);
    }
}

static cdd test1_CDD_from_random_DBMs(size_t size, int numberOfDBMs)
{
    cdd cdd_result;
    printf("Test1: Building CDD from random DBMs\n");

    cdd_result = cdd_true();

    // Build DBMs
    for (int i = 0; i < numberOfDBMs; i++) {
        ADBM(dbm);
        DBM_GEN(dbm);

        printf("_______________\n");
        dbm_print(stdout, dbm, size);

        cdd_result = cdd(dbm, size);
        print_cdd(cdd_result, "test1_normal");

        cdd cdd_negated = !cdd_result;
        print_cdd(cdd_negated, "test1_negated");
    }
    return cdd_result;
}

static cdd buildSimpleStaticBDD(int bdd_start_level) {

/*
    cdd trueNode = cdd_true();
    print_cdd(trueNode);

    cdd falseNode = cdd_false();
    print_cdd(falseNode);

    cdd n10 = cdd_bddvarpp(bdd_start_level + 0);
    cdd n11 = n10 & cdd_bddvarpp(bdd_start_level + 1);
    print_cdd(n11);

    cdd n20 = cdd_bddvarpp(bdd_start_level + 0);
    cdd n22 = n20 & !cdd_bddvarpp(bdd_start_level + 1);
    print_cdd(n22);


    cdd n3 = n11 | n22;
    print_cdd(n3);
*/
    cdd negated = !cdd_bddvarpp(bdd_start_level + 1);
    cdd myTrueNode = cdd_bddvarpp(bdd_start_level + 1);

    cdd topNodeTrue = cdd_bddvarpp(bdd_start_level + 0);
    cdd leftNode = topNodeTrue & myTrueNode;
    cdd rightNode = !topNodeTrue & negated;
    cdd topNode = leftNode | rightNode;

    print_cdd(topNode);

    return topNode;
}

static cdd buildCDDWithBooleansTest(size_t size, int number_of_DBMs, int number_of_booleans, int bdd_start_level) {
    cdd cdd_result;

    printf("Building CDD with Booleans\n");

    cdd_result = cdd_false();

    // Build DBMs
    for (int i = 0; i < number_of_DBMs; i++) {
        ADBM(dbm);
        DBM_GEN(dbm);

        printf("_______________\n");
        dbm_print(stdout, dbm, size);

        cdd_result |= cdd(dbm, size);


        print_cdd(cdd_result);
    }


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

    return cdd_result;
}

//static cdd addConstraint()

int test_global_1(int seed) {


}

int main(int argc, char* argv[])
{
    srand(287);
    uint32_t number_of_clocks, number_of_clocks_including_zero, number_of_DBMs, number_of_booleans;
    number_of_clocks = 3;
    number_of_clocks_including_zero = number_of_clocks + 1;
    number_of_DBMs = 1;
    number_of_booleans = 5;

    cdd_init(1000000,100000,100000);
    cdd_add_clocks(number_of_clocks_including_zero);
    int bdd_start_level = cdd_add_bddvar(number_of_booleans);

    int bdd_level_count = cdd_get_bdd_level_count();

    // Call test method
    for (int i = 0; i < 1; i++) {
        cdd cdd_main = test1_CDD_from_random_DBMs(number_of_clocks_including_zero, number_of_DBMs);
    }


    cdd cdd_main = buildCDDWithBooleansTest(number_of_clocks+1, number_of_DBMs, number_of_booleans, bdd_start_level);
    //cdd_main = buildSimpleStaticBDD(bdd_start_level);

   // print_cdd(cdd_main, "main");

    /*
    print_cdd(cdd_true());
    print_cdd(cdd_false());

    print_cdd(!cdd_true());
    print_cdd(!cdd_false());
    */

    cdd_done();
    exit(0);
}



