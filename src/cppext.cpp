// -*- mode: C++; c-file-style: "stroustrup"; c-basic-offset: 4; indent-tabs-mode: nil; -*-
///////////////////////////////////////////////////////////////////////////////
//
// This file is a part of the UPPAAL toolkit.
// Copyright (c) 1995 - 2003, Uppsala University and Aalborg University.
// All right reserved.
//
// $Id: cppext.cpp,v 1.4 2004/04/02 22:53:55 behrmann Exp $
//
///////////////////////////////////////////////////////////////////////////////

#include <malloc.h>
#include "cdd/kernel.h"

uint32_t printCounter1 = 0; // Used to number printed CDDs

static void print_cdd(cdd to_print, char *name, bool push_negate) {
    char filename[30];
    sprintf(filename, "%s_%d.dot", name, printCounter1);
    printf("Printing cdd %s to file : \n", name);
    FILE *fp_main;
    fp_main = fopen(filename, "w");
    cdd_fprintdot(fp_main, to_print, push_negate);
    fclose(fp_main);
    printCounter1++;
}

cdd::cdd(const cdd& r)
{
    assert(cdd_isrunning());
    root = r.root;
    if (root)
        cdd_ref(root);
}

cdd::cdd(const raw_t* dbm, uint32_t dim)
{
    assert(cdd_isrunning());
    root = cdd_from_dbm(dbm, dim);
    cdd_ref(root);
}

cdd::cdd(ddNode* r)
{
    assert(cdd_isrunning() && r);
    root = r;
    cdd_ref(r);
}

cdd::~cdd() { cdd_rec_deref(root); }

cdd& cdd::operator=(const cdd& r)
{
    if (root != r.root) {
        cdd_rec_deref(root);
        root = r.root;
        cdd_ref(root);
    }
    return *this;
}

cdd cdd::operator=(ddNode* node)
{
    if (root != node) {
        cdd_rec_deref(root);
        root = node;
        cdd_ref(root);
    }
    return *this;
}

#define ADBM(NAME)  raw_t* NAME = allocDBM(size)

/* allocate a DBM
 */
static raw_t* allocDBM(uint32_t dim) { return (raw_t*)malloc(dim * dim * sizeof(raw_t)); }


cdd cdd_delay(const cdd& state)
{
    uint32_t size = cdd_clocknum;
    cdd copy= state;
    cdd res= cdd_false();
    ADBM(dbm);
    while (!cdd_isterminal(copy.root) && cdd_info(copy.root)->type != TYPE_BDD) {
        copy = cdd_reduce(copy);
        cdd bottom = cdd_extract_bdd(copy, dbm, size);
        copy = cdd_extract_dbm(copy, dbm, size);
        copy = cdd_reduce(copy);
        dbm_up(dbm, size);
        cdd fixed_cdd = cdd(dbm,size);
        fixed_cdd &= bottom;
        res |= fixed_cdd;
    }
    return res;
}


extraction_result cdd_extract_bdd_and_dbm(const cdd& state)
{
    uint32_t size = cdd_clocknum;
    ADBM(dbm);
    cdd bdd_part = cdd_extract_bdd(state, dbm, size);
    cdd cdd_part = cdd_extract_dbm(state, dbm, size);
    extraction_result res;
    res.BDD_part=bdd_part;
    res.CDD_part=cdd_part;
    res.dbm=dbm;
    return res;
}


cdd cdd_predt(const cdd&  target, const cdd&  safe)
{
    cdd allThatKillsUs = cdd_false();
    uint32_t size = cdd_clocknum;
    cdd copy = target;
    ADBM(dbm);
    while (!cdd_isterminal(copy.handle()) && cdd_info(copy.handle())->type != TYPE_BDD) {
        extraction_result res = cdd_extract_bdd_and_dbm(copy);
        copy = res.CDD_part;
        dbm = res.dbm;
        cdd bdd = res.BDD_part;
        cdd bdd_intersect = bdd & safe;
        if ( bdd_intersect != cdd_false())
        {
            dbm_down(dbm, size);
            cdd past = cdd(dbm,size);
            past &= bdd;
            cdd escape = safe & past;
            allThatKillsUs |= (past - escape);
        }
        else
        {
            dbm_down(dbm,size);
            cdd past = cdd (dbm, size) & bdd;
            allThatKillsUs |= past;
        }
    }
    return allThatKillsUs;
}

cdd cdd_delay_invariant(const cdd& state, const cdd& invar)
{
    cdd res = cdd_delay(state);
    res &= invar;
    return res;
}

cdd cdd_past(const cdd& state)
{
    uint32_t size = cdd_clocknum;
    cdd copy= state;
    cdd res= cdd_false();
    ADBM(dbm);
    while (!cdd_isterminal(copy.handle()) && cdd_info(copy.handle())->type != TYPE_BDD) {
        copy = cdd_reduce(copy);
        cdd bottom = cdd_extract_bdd(copy, dbm, size);
        copy = cdd_extract_dbm(copy, dbm, size);
        copy = cdd_reduce(copy);
        dbm_down(dbm, size);
        res |= (cdd(dbm,size) & bottom);
    }
    return res;
}



cdd cdd_apply_reset(const cdd& state, int32_t* clock_resets, int32_t* clock_values, int32_t num_clock_resets, int32_t* bool_resets, int32_t* bool_values, int32_t num_bool_resets)
{
    uint32_t size = cdd_clocknum;
    //ADBM(dbm);
    cdd copy= state;
    copy = cdd_exist(copy, bool_resets, clock_resets, num_bool_resets,num_clock_resets);
    // Hint: if this quantifies a clock, the resulting CDD will include negative clock values

    // apply bool updates
    for (int i=bdd_start_level;i<bdd_start_level+cdd_varnum; i++)
    {
        if (bool_resets[i] == 1) { // TODO: FIX THIS TO THE NEW FORMAT OF LISTING RESETS
            if (bool_values[i]==1) {
                copy = cdd_apply(copy, cdd_bddvarpp(i), cddop_and);
            }
            else
            {
                copy = cdd_apply(copy, cdd_bddnvarpp(i), cddop_and);
            }
        }
    }
    copy = cdd_remove_negative(copy);
    copy = cdd_reduce(copy);
    // apply clock resets
    cdd res= cdd_true();
    for (int i = 0; i < num_clock_resets; i++) {
        ADBM(dbm_for_bounds);
        dbm_init(dbm_for_bounds, size);
        dbm_updateValue(dbm_for_bounds, size, clock_resets[i] , clock_values[i]);
        res |= (cdd(dbm_for_bounds,size));
    }
    print_cdd(res, "outputCDD",true);
    res = res & copy;
/*    while (!cdd_isterminal(copy.root) && cdd_info(copy.root)->type != TYPE_BDD) {
        copy = cdd_remove_negative(copy);
        copy = cdd_reduce(copy);
        cdd bottom = cdd_extract_bdd(copy, dbm, size);
        copy = cdd_extract_dbm(copy, dbm, size);
        for (int i = 0; i < num_clock_resets; i++) {
                dbm_updateValue(dbm, size, clock_resets[i] , clock_values[i]);
        }
        res |= (cdd(dbm,size) & bottom);
    }*/

    return res;
}


cdd cdd_transition(const cdd& state, const cdd& guard, int32_t* clock_resets, int32_t* clock_values, int32_t num_clock_resets, int32_t* bool_resets, int32_t* bool_values,   int32_t num_bool_resets )
{
    uint32_t size = cdd_clocknum;
    ADBM(dbm);
    cdd copy= state;
    copy &= guard;
    copy = cdd_exist(copy, bool_resets, clock_resets, num_bool_resets,num_clock_resets);
    // Hint: if this quantifies a clock, the resulting CDD will include negative clock values

    for (int i=bdd_start_level;i<bdd_start_level+cdd_varnum; i++)
    {
        if (bool_resets[i] == 1) {
            if (bool_values[i]==1) {
                copy = cdd_apply(copy, cdd_bddvarpp(i), cddop_and);
            }
            else
            {
                copy = cdd_apply(copy, cdd_bddnvarpp(i), cddop_and);
            }
        }
    }

        cdd res= cdd_false();
        for (int i = 0; i < num_clock_resets; i++) {
            res = res & cdd_lowerpp(0, clock_resets[i], clock_values[i]);
            res = res & cdd_upperpp(0, clock_resets[i], clock_values[i]);
        }
        res = res & copy;
    /*cdd res= cdd_false();
    while (!cdd_isterminal(copy.root) && cdd_info(copy.root)->type != TYPE_BDD) {
        copy = cdd_remove_negative(copy);
        copy = cdd_reduce(copy);
        cdd bottom = cdd_extract_bdd(copy, dbm, size);
        copy = cdd_extract_dbm(copy, dbm, size);
        for (int i = 0; i < cdd_clocknum; i++) {
            for (int i = 0; i < num_clock_resets; i++) {
                dbm_updateValue(dbm, size, clock_resets[i] , clock_values[i]);
            }
        }
        res |= (cdd(dbm,size) & bottom);
    }*/
    return res;
}

cdd cdd_transition_back(const cdd&  state, const cdd& guard, const cdd& update, int32_t* clock_resets,  int32_t num_clock_resets, int32_t* bool_resets,  int32_t num_bool_resets)
{
    cdd copy= state;
    // TODO: sanity check: implement cdd_is_update();
    // assert(ccd_is_update(update));
    copy &= update;
    if (copy == cdd_false()) {
        return copy;
    }
    copy = cdd_exist(copy, bool_resets, clock_resets, num_bool_resets, num_clock_resets);
    copy = cdd_remove_negative(copy);
    copy &= guard;
    return copy;
}

cdd cdd_transition_back_past(const cdd&  state, const cdd& guard, const cdd& update, int32_t* clock_resets, int32_t num_clock_resets, int32_t* bool_resets, int32_t num_bool_resets)
{
    cdd result = cdd_transition_back(state,guard, update, clock_resets, num_clock_resets, bool_resets, num_bool_resets);
    return cdd_past(result);
}
