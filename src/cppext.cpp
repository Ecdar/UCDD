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
    if (cdd_equiv(state, cdd_true()))
        return state;
    uint32_t size = cdd_clocknum;
    cdd copy= state;
    cdd res= cdd_false();
    ADBM(dbm);
    while (!cdd_isterminal(copy.root) && cdd_info(copy.root)->type != TYPE_BDD) {
        copy = cdd_reduce(copy);
        cdd bottom = cdd_extract_bdd(copy, dbm, size);
        copy = cdd_extract_dbm(copy, dbm, size);
        copy = cdd_reduce(cdd_remove_negative(copy));
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
        copy = cdd_reduce(cdd_remove_negative(res.CDD_part));
        dbm = res.dbm;
        cdd bdd = res.BDD_part;
        cdd bdd_intersect = bdd & safe;
        if ( bdd_intersect != cdd_false())
        {
            dbm_down(dbm, size);
            cdd past = cdd(dbm,size);
            past &= bdd; //TODO should that be bdd_intersect?
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
        copy = cdd_reduce(cdd_remove_negative(copy));
        dbm_down(dbm, size);
        res |= (cdd(dbm,size) & bottom);
    }
    return res;
}

bool cdd_isBDD(const cdd& state)
{
    if (cdd_isterminal(state.root))
        return false;
    return cdd_info(state.handle())->type == TYPE_BDD;
}








int maxNumberOfTraces =10;
int** resultArraysVars;// = new int[arraySize];
int** resultArraysValues;// = new int[arraySize];
int currentTrace;

void resizeArrays()
{
    printf("resizing");
    int ** newVarsArray = new int*[maxNumberOfTraces *2];
    int ** newValuesArray = new int*[maxNumberOfTraces *2];
    for (int i=0; i< maxNumberOfTraces;i++) {
        newValuesArray[i] = resultArraysValues[i];
        newVarsArray[i] = resultArraysVars[i];
    }
    for(int i = 0; i <= currentTrace; ++i) {
        delete [] resultArraysVars[i];
        delete [] resultArraysValues[i];
    }
    delete[] resultArraysVars;
    delete[] resultArraysValues;
    maxNumberOfTraces = maxNumberOfTraces *2;
    resultArraysVars = newVarsArray;
    resultArraysValues = newValuesArray;
}



void cdd_bdd_to_array_rec(ddNode* r, int32_t* trace_vars,  int32_t* trace_values, int32_t  current_step, bool negated, int num_bools)
{
    if (r == cddtrue && negated ==false) {
        if (currentTrace== maxNumberOfTraces -1)
            resizeArrays();
        resultArraysValues[currentTrace]=new int[num_bools];
        resultArraysVars[currentTrace]=new int[num_bools];
        int i;
        for (i = 0; i < num_bools; i++) {
            resultArraysValues[currentTrace][i]=trace_values[i];
            resultArraysVars[currentTrace][i]=trace_vars[i];
        }
        currentTrace++;
        return;
    }
    if (r == cddtrue && negated ==true) {
        return;
    }
    if (r == cddfalse && negated ==true)
    {

            if (currentTrace== maxNumberOfTraces -1)
                resizeArrays();
            resultArraysValues[currentTrace]=new int[num_bools];
            resultArraysVars[currentTrace]=new int[num_bools];
            int i;
            for (i = 0; i < num_bools; i++) {
                resultArraysValues[currentTrace][i]=trace_values[i];
                resultArraysVars[currentTrace][i]=trace_vars[i];
            }
            currentTrace++;
            return;
    }
    if (r == cddfalse && negated == false) {
        return;
    }


    if (cdd_info(r)->type == TYPE_BDD) {
        bddNode* node = bdd_node(r);

        int trace_vars1[num_bools-1];
        int trace_vars2[num_bools-1];
        int trace_values1[num_bools-1];
        int trace_values2[num_bools-1];
        for (int i = 0; i < num_bools; i++) {
            trace_vars1[i] = trace_vars[i];
            trace_vars2[i] = trace_vars[i];
            trace_values1[i] = trace_values[i];
            trace_values2[i] = trace_values[i];
        }
        trace_vars1[current_step]=node->level;
        trace_values1[current_step]=1;


        cdd_bdd_to_array_rec(node->high, trace_vars1,trace_values1,current_step+1, negated ^ cdd_is_negated(r), num_bools);

        trace_vars2[current_step]=node->level;
        trace_values2[current_step]=0;
        cdd_bdd_to_array_rec(node->low, trace_vars2,trace_values2,current_step+1, negated ^ cdd_is_negated(r), num_bools);
        }
 else {
        printf("not called with a BDD node");
    }
}


bdd_arrays cdd_bdd_to_array(const cdd& state, int num_bools)
{
    currentTrace=0;
    maxNumberOfTraces =100;
    resultArraysVars=new int*[maxNumberOfTraces];
    resultArraysValues=new int*[maxNumberOfTraces];

    int vars[num_bools];
    int values[num_bools];
    for (int i = 0; i < num_bools; i++) {
        vars[i]=-1;
        values[i]=-1;
    }
    cdd_bdd_to_array_rec(state.handle(),vars,values, 0,false, num_bools);
    printf("allocating now %i \n" ,(num_bools)*(currentTrace));


    int32_t *varRes = new int32_t[(num_bools)*(currentTrace)];
    int32_t *valRes = new int32_t[(num_bools)*(currentTrace)];
    for (uint32_t  i = 0; i< currentTrace; i++)
    {
        for (uint32_t  j= 0; j<num_bools;j++)
        {
            varRes[i*(num_bools)+j]= resultArraysVars[i][j];
            printf(" val[0][0]: %i %i\n",resultArraysValues[i][j],i*(num_bools)+j);
            valRes[i*(num_bools)+j]= 0;//resultArraysValues[i][j];
        }
    }

    bdd_arrays arys;
    arys.values=valRes;
    arys.vars=varRes;
    arys.numTraces=currentTrace;
    arys.numBools=num_bools;
    printf("Values[0] on C side: %i \n", arys.values[0]);

    for(int i = 0; i < currentTrace; ++i) {
        delete [] resultArraysVars[i];
        delete [] resultArraysValues[i];
    }
    delete[] resultArraysVars;
    delete[] resultArraysValues;
    return arys;
}















cdd cdd_apply_reset(const cdd& state, int32_t* clock_resets, int32_t* clock_values, int32_t num_clock_resets, int32_t* bool_resets, int32_t* bool_values, int32_t num_bool_resets)
{
    uint32_t size = cdd_clocknum;
    //ADBM(dbm);
    cdd copy= state;
    int empty[0];
    int* emptyPtr = empty;
    //copy = cdd_exist(copy, bool_resets, emptyPtr, num_bool_resets,0);
    //copy = cdd_exist(copy, bool_resets, clock_resets, num_bool_resets,num_clock_resets);
    // Hint: if this quantifies a clock, the resulting CDD will include negative clock values
/*
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
    }*/

    // apply bool updates
    for (int i=0;i<num_bool_resets; i++)
    {
        if (bool_values[i]==1) {
            copy = cdd_apply(copy, cdd_bddvarpp( bool_resets[i]), cddop_and);
        }
        else
        {
            copy = cdd_apply(copy, cdd_bddnvarpp(bool_resets[i]), cddop_and);
        }
    }

    cdd res= cdd_false();
    copy = cdd_remove_negative(copy);

    while (!cdd_isterminal(copy.root) && cdd_info(copy.root)->type != TYPE_BDD) {


        copy = cdd_reduce(copy);
        extraction_result exres = cdd_extract_bdd_and_dbm(copy);
        cdd bottom = exres.BDD_part;
        copy = cdd_reduce(cdd_remove_negative(exres.CDD_part));
        for (int i = 0; i < num_clock_resets; i++) {
            dbm_updateValue(exres.dbm, size, clock_resets[i] , clock_values[i]);
        }
        res |= (cdd(exres.dbm,size) & bottom);
    }
    return res;
}


cdd cdd_transition(const cdd& state, const cdd& guard, int32_t* clock_resets, int32_t* clock_values, int32_t num_clock_resets, int32_t* bool_resets, int32_t* bool_values,   int32_t num_bool_resets )
{
    uint32_t size = cdd_clocknum;
    ADBM(dbm);
    cdd copy= state;
    copy &= guard;
    int empty[0];
    int* emptyPtr = empty;
    copy = cdd_exist(copy, bool_resets, emptyPtr, num_bool_resets,0);
    // Hint: if this quantifies a clock, the resulting CDD will include negative clock values

    // apply bool updates
    for (int i=0;i<num_bool_resets; i++)
    {
        if (bool_values[i]==1) {
            copy = cdd_apply(copy, cdd_bddvarpp(bdd_start_level + bool_resets[i]), cddop_and);
        }
        else
        {
            copy = cdd_apply(copy, cdd_bddnvarpp(bdd_start_level + bool_resets[i]), cddop_and);
        }
    }

    cdd res= cdd_false();
    copy = cdd_remove_negative(copy);

    while (!cdd_isterminal(copy.root) && cdd_info(copy.root)->type != TYPE_BDD) {

        copy = cdd_reduce(copy);
        extraction_result exres = cdd_extract_bdd_and_dbm(copy);
        cdd bottom = exres.BDD_part;
        copy = cdd_reduce(cdd_remove_negative(exres.CDD_part));
        for (int i = 0; i < num_clock_resets; i++) {
            dbm_updateValue(exres.dbm, size, clock_resets[i] , clock_values[i]);
        }
        res |= (cdd(exres.dbm,size) & bottom);
    }
    return res;

}

cdd cdd_transition_back(const cdd&  state, const cdd& guard, const cdd& update, int32_t* clock_resets,  int32_t num_clock_resets, int32_t* bool_resets,  int32_t num_bool_resets)
{
    uint32_t size = cdd_clocknum;
    cdd copy= state;
    // TODO: sanity check: implement cdd_is_update();
    // assert(ccd_is_update(update));
    copy &= update;
    if (copy == cdd_false()) {
        return copy;
    }
    int empty[0];
    int* emptyPtr = empty;
    copy = cdd_exist(copy, bool_resets, emptyPtr, num_bool_resets,0);

    cdd res= cdd_false();
    copy = cdd_remove_negative(copy);

    while (!cdd_isterminal(copy.root) && cdd_info(copy.root)->type != TYPE_BDD) {

        copy = cdd_reduce(copy);
        extraction_result exres = cdd_extract_bdd_and_dbm(copy);
        cdd bottom = exres.BDD_part;
        copy = cdd_reduce(cdd_remove_negative(exres.CDD_part));
        for (int i = 0; i < num_clock_resets; i++) {
            dbm_freeClock(exres.dbm, size, clock_resets[i]);
        }
        res |= (cdd(exres.dbm,size) & bottom);
    }
    return res & guard;
}

cdd cdd_transition_back_past(const cdd&  state, const cdd& guard, const cdd& update, int32_t* clock_resets, int32_t num_clock_resets, int32_t* bool_resets, int32_t num_bool_resets)
{
    cdd result = cdd_transition_back(state,guard, update, clock_resets, num_clock_resets, bool_resets, num_bool_resets);
    return cdd_past(result);
}
