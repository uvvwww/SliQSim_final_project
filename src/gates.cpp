#include "Simulator.h"
#include "util_sim.h"


void Simulator::Toffoli(int targ, std::vector<int> cont, std::vector<int> ncont)
{
    assert((cont.size() + ncont.size()) < n);
    int IsBadtarg = 0;
    int cont_tot = cont.size() + ncont.size();
    for (int i = 0; i < cont_tot; i++)
    {
        if (i < cont.size())
        {
            if (targ == cont[i])
            {
                IsBadtarg = 1;
                break;
            }
        }
        else
        {
            if (targ == ncont[i - cont.size()])
            {
                IsBadtarg = 1;
                break;
            }
        }
    }
    assert(!IsBadtarg);

    DdNode *term1, *term2, *term3, *g, *tmp;

    g = Cudd_ReadOne(manager);
    Cudd_Ref(g);
    for (int h = cont.size() - 1; h >= 0; h--)
    {
        tmp = Cudd_bddAnd(manager, Cudd_bddIthVar(manager, cont[h]), g);
        Cudd_Ref(tmp);
        Cudd_RecursiveDeref(manager, g);
        g = tmp;
    }
    for (int h = ncont.size() - 1; h >= 0; h--)
    {
        tmp = Cudd_bddAnd(manager, Cudd_Not(Cudd_bddIthVar(manager, ncont[h])), g);
        Cudd_Ref(tmp);
        Cudd_RecursiveDeref(manager, g);
        g = tmp;
    }

    for (int i = 0; i < w; i++) // F = All_Bdd[i][j]
    {
        for (int j = 0; j < r; j++)
        {
            //term1
            term1 = Cudd_ReadOne(manager);
            Cudd_Ref(term1);
            tmp = Cudd_bddAnd(manager, All_Bdd[i][j], term1);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term1);
            term1 = tmp;
            tmp = Cudd_bddAnd(manager, Cudd_Not(g), term1);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term1);
            term1 = tmp;

            //term2
            term2 = Cudd_Cofactor(manager, All_Bdd[i][j], Cudd_Not(Cudd_bddIthVar(manager, targ)));
            Cudd_Ref(term2);

            tmp = Cudd_Cofactor(manager, term2, g);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;

            tmp = Cudd_bddAnd(manager, term2, g);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;

            tmp = Cudd_bddAnd(manager, term2, Cudd_bddIthVar(manager, targ));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;

            //term3
            term3 = Cudd_Cofactor(manager, All_Bdd[i][j], Cudd_bddIthVar(manager, targ));
            Cudd_Ref(term3);
            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);

            tmp = Cudd_Cofactor(manager, term3, g);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term3);
            term3 = tmp;

            tmp = Cudd_bddAnd(manager, term3, g);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term3);
            term3 = tmp;

            tmp = Cudd_bddAnd(manager, term3, Cudd_Not(Cudd_bddIthVar(manager, targ)));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term3);
            term3 = tmp;

            //OR
            All_Bdd[i][j] = Cudd_bddOr(manager, term1, term2);
            Cudd_Ref(All_Bdd[i][j]);
            Cudd_RecursiveDeref(manager, term1);
            Cudd_RecursiveDeref(manager, term2);
            tmp = Cudd_bddOr(manager, term3, All_Bdd[i][j]);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term3);
            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
            All_Bdd[i][j] = tmp;
        }
    }
    Cudd_RecursiveDeref(manager, g);
    gatecount++;
    nodecount();
}

void Simulator::Fredkin(int swapA , int swapB, std::vector<int> cont)
{
    assert(cont.size() < n);
    int IsBadtarg = 0;
    for (int i = 0; i < cont.size(); i++)
    {
        if ((swapA == cont[i]) || (swapB == cont[i]))
        {
            IsBadtarg = 1;
            break;
        }
    }
    assert(!IsBadtarg);

    DdNode *term1, *term2, *term3, *g, *tmp, *tmp0;

    g = Cudd_ReadOne(manager);
    Cudd_Ref(g);
    for (int h = cont.size() - 1; h >= 0; h--)
    {
        tmp = Cudd_bddAnd(manager, Cudd_bddIthVar(manager, cont[h]), g);
        Cudd_Ref(tmp);
        Cudd_RecursiveDeref(manager, g);
        g = tmp;
    }

    for (int i = 0; i < w; i++) // F = All_Bdd[i][j]
    {
        for (int j = 0; j < r; j++)
        {
            //term1
            term1 = Cudd_ReadOne(manager);
            Cudd_Ref(term1);
            tmp = Cudd_bddAnd(manager, All_Bdd[i][j], term1);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term1);
            term1 = tmp;
            tmp = Cudd_bddXor(manager, Cudd_bddIthVar(manager, swapA), Cudd_bddIthVar(manager, swapB));
            Cudd_Ref(tmp);
            tmp0 = Cudd_Not(Cudd_bddAnd(manager, g, tmp));
            Cudd_Ref(tmp0);
            Cudd_RecursiveDeref(manager, tmp);
            tmp = Cudd_bddAnd(manager, term1, tmp0);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term1);
            Cudd_RecursiveDeref(manager, tmp0);
            term1 = tmp;

            //term2
            term2 = Cudd_Cofactor(manager, All_Bdd[i][j], g);
            Cudd_Ref(term2);

            tmp = Cudd_Cofactor(manager, term2, Cudd_Not(Cudd_bddIthVar(manager, swapA)));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;

            tmp = Cudd_Cofactor(manager, term2, Cudd_bddIthVar(manager, swapB));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;

            tmp = Cudd_bddAnd(manager, term2, g);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;

            tmp = Cudd_bddAnd(manager, term2, Cudd_bddIthVar(manager, swapA));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;

            tmp = Cudd_bddAnd(manager, term2, Cudd_Not(Cudd_bddIthVar(manager, swapB)));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;

            //term3
            term3 = Cudd_Cofactor(manager, All_Bdd[i][j], g);
            Cudd_Ref(term3);

            tmp = Cudd_Cofactor(manager, term3, Cudd_bddIthVar(manager, swapA));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term3);
            term3 = tmp;

            tmp = Cudd_Cofactor(manager, term3, Cudd_Not(Cudd_bddIthVar(manager, swapB)));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term3);
            term3 = tmp;

            tmp = Cudd_bddAnd(manager, term3, g);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term3);
            term3 = tmp;

            tmp = Cudd_bddAnd(manager, term3, Cudd_Not(Cudd_bddIthVar(manager, swapA)));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term3);
            term3 = tmp;

            tmp = Cudd_bddAnd(manager, term3, Cudd_bddIthVar(manager, swapB));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term3);
            term3 = tmp;

            //OR
            All_Bdd[i][j] = Cudd_bddOr(manager, term1, term2);
            Cudd_Ref(All_Bdd[i][j]);
            Cudd_RecursiveDeref(manager, term1);
            Cudd_RecursiveDeref(manager, term2);
            tmp = Cudd_bddOr(manager, term3, All_Bdd[i][j]);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term3);
            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
            All_Bdd[i][j] = tmp;
        }
    }
    Cudd_RecursiveDeref(manager, g);
    gatecount++;
    nodecount();
}

void Simulator::Peres(int a, int b, int c)
{
    std::vector<int> ncont(0);
    std::vector<int> cont1(2);
    cont1[0] = b;
    cont1[1] = c;
    Toffoli(a, cont1, ncont);
    cont1.clear();
    std::vector<int> cont2(1);
    cont2[0] = c;
    Toffoli(b, cont2, ncont);
    cont2.clear();
    ncont.clear();
    gatecount++;
    nodecount();
}

void Simulator::Peres_i(int a, int b, int c)
{
    std::vector<int> ncont(0);
    std::vector<int> cont2(1);
    cont2[0] = c;
    Toffoli(b, cont2, ncont);
    cont2.clear();
    std::vector<int> cont1(2);
    cont1[0] = b;
    cont1[1] = c;
    Toffoli(a, cont1, ncont);
    cont1.clear();
    ncont.clear();
    gatecount++;
    nodecount();
}

void Simulator::Hadamard(int iqubit)
{
    assert((iqubit >= 0) & (iqubit < n));

    k = k + 1;

    DdNode *g, *d, *c, *tmp, *term1, *term2;

    int overflow_done = 0;

    for (int i = 0; i < w; i++) // F = All_Bdd[i][j]
    {
        c = Cudd_ReadOne(manager); // init c
        Cudd_Ref(c);
        tmp = Cudd_bddAnd(manager, c, Cudd_bddIthVar(manager, iqubit));
        Cudd_Ref(tmp);
        Cudd_RecursiveDeref(manager, c);
        c = tmp;
        for (int j = 0; j < r; j++)
        {
            //g
            g = Cudd_Cofactor(manager, All_Bdd[i][j], Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
            Cudd_Ref(g);
            //d
            term1 = Cudd_Cofactor(manager, All_Bdd[i][j], Cudd_bddIthVar(manager, iqubit));
            Cudd_Ref(term1);
            tmp = Cudd_bddAnd(manager, term1, Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term1);
            term1 = tmp;
            term2 = Cudd_Not(All_Bdd[i][j]);
            Cudd_Ref(term2);
            tmp = Cudd_bddAnd(manager, term2, Cudd_bddIthVar(manager, iqubit));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;
            d = Cudd_bddOr(manager, term1, term2);
            Cudd_Ref(d);
            Cudd_RecursiveDeref(manager, term1);
            Cudd_RecursiveDeref(manager, term2);
            //detect overflow
            if ((j == r - 1) && !overflow_done)
                if (overflow3(g, d, c))
                {   if (isAlloc)
                    {
                        r += inc;
                        alloc_BDD(All_Bdd, true); // add new BDDs
                    }
                    else
                    {
                        j -= 1;
                        ++shift;
                        dropLSB(All_Bdd);
                    }
                    overflow_done = 1;
                }
            //sum
            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
            All_Bdd[i][j] = Cudd_bddXor(manager, g, d);
            Cudd_Ref(All_Bdd[i][j]);
            tmp = Cudd_bddXor(manager, All_Bdd[i][j], c);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
            All_Bdd[i][j] = tmp;
            //carry
            if (j == r - 1)
            {
                Cudd_RecursiveDeref(manager, c);
                Cudd_RecursiveDeref(manager, g);
                Cudd_RecursiveDeref(manager, d);
            }
            else
            {
                term1 = Cudd_bddAnd(manager, g, d);
                Cudd_Ref(term1);
                term2 = Cudd_bddOr(manager, g, d);
                Cudd_Ref(term2);
                Cudd_RecursiveDeref(manager, g);
                Cudd_RecursiveDeref(manager, d);
                tmp = Cudd_bddAnd(manager, term2, c);
                Cudd_Ref(tmp);
                Cudd_RecursiveDeref(manager, term2);
                Cudd_RecursiveDeref(manager, c);
                term2 = tmp;
                c = Cudd_bddOr(manager, term1, term2);
                Cudd_Ref(c);
                Cudd_RecursiveDeref(manager, term1);
                Cudd_RecursiveDeref(manager, term2);
            }
        }
    }
    gatecount++;
    nodecount();
}

void Simulator::rx_pi_2(int iqubit)
{
    assert((iqubit >= 0) & (iqubit < n));

    k = k + 1;

    int nshift = w / 2;
    int overflow_done = 0;

    DdNode *g, *d, *c, *tmp, *term1, *term2;
    DdNode **copy[w];
    for (int i = 0; i < w; i++)
        copy[i] = new DdNode *[r];

    /* copy */
    for (int i = 0; i < w; i++)
    {
         for (int j = 0; j < r; j++)
        {
            copy[i][j] = Cudd_ReadOne(manager);
            Cudd_Ref(copy[i][j]);
            tmp = Cudd_bddAnd(manager, copy[i][j], All_Bdd[i][j]);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, copy[i][j]);
            copy[i][j] = tmp;
        }
    }

    for (int i = 0; i < w; i++)
    {
        // init c
        if (i < nshift)
            c = Cudd_ReadOne(manager);

        else
            c = Cudd_Not(Cudd_ReadOne(manager));
        Cudd_Ref(c);
        for (int j = 0; j < r; j++)
        {
            //d
            term1 = Cudd_Cofactor(manager, copy[(i + nshift) % w][j], Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
            Cudd_Ref(term1);
            tmp = Cudd_bddAnd(manager, term1, Cudd_bddIthVar(manager, iqubit));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term1);
            term1 = tmp;
            term2 = Cudd_Cofactor(manager, copy[(i + nshift) % w][j], Cudd_bddIthVar(manager, iqubit));
            Cudd_Ref(term2);
            tmp = Cudd_bddAnd(manager, term2, Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;
            if (i < nshift) d = Cudd_Not(Cudd_bddOr(manager, term1, term2));
            else d = Cudd_bddOr(manager, term1, term2);
            Cudd_Ref(d);
            Cudd_RecursiveDeref(manager, term1);
            Cudd_RecursiveDeref(manager, term2);
            //detect overflow
            if ((j == r - 1) && !overflow_done)
                if (overflow3(copy[i][j], d, c))
                {   if (isAlloc)
                    {
                        r += inc;
                        alloc_BDD(All_Bdd, true); // add new BDDs
                        alloc_BDD(copy, true);
                    }
                    else
                    {
                        j -= 1;
                        ++shift;
                        dropLSB(All_Bdd);
                        dropLSB(copy);
                    }
                    overflow_done = 1;
                }
            //sum
            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
            All_Bdd[i][j] = Cudd_bddXor(manager, copy[i][j], d);
            Cudd_Ref(All_Bdd[i][j]);
            tmp = Cudd_bddXor(manager, All_Bdd[i][j], c);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
            All_Bdd[i][j] = tmp;
            //carry
            if (j == r - 1)
            {
                Cudd_RecursiveDeref(manager, c);
                Cudd_RecursiveDeref(manager, d);
            }
            else
            {
                term1 = Cudd_bddAnd(manager, copy[i][j], d);
                Cudd_Ref(term1);
                term2 = Cudd_bddOr(manager, copy[i][j], d);
                Cudd_Ref(term2);
                Cudd_RecursiveDeref(manager, d);
                tmp = Cudd_bddAnd(manager, term2, c);
                Cudd_Ref(tmp);
                Cudd_RecursiveDeref(manager, term2);
                Cudd_RecursiveDeref(manager, c);
                term2 = tmp;
                c = Cudd_bddOr(manager, term1, term2);
                Cudd_Ref(c);
                Cudd_RecursiveDeref(manager, term1);
                Cudd_RecursiveDeref(manager, term2);
            }
        }
    }
    for (int i = 0; i < w; i++)
    {
        for (int j = 0; j < r; j++)
            Cudd_RecursiveDeref(manager, copy[i][j]);
        delete[] copy[i];
    }
    gatecount++;
    nodecount();
}

void Simulator::ry_pi_2(int iqubit)
{

    assert((iqubit >= 0) & (iqubit < n));

    k = k + 1;

    int overflow_done = 0;

    DdNode *g, *d, *c, *tmp, *term1, *term2;

    for (int i = 0; i < w; i++)
    {
        c = Cudd_ReadOne(manager); // init c
        Cudd_Ref(c);
        tmp = Cudd_bddAnd(manager, c, Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
        Cudd_Ref(tmp);
        Cudd_RecursiveDeref(manager, c);
        c = tmp;
        for (int j = 0; j < r; j++)
        {
            //g
            g = Cudd_Cofactor(manager, All_Bdd[i][j], Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
            Cudd_Ref(g);
            //d
            term1 = Cudd_bddAnd(manager, All_Bdd[i][j], Cudd_bddIthVar(manager, iqubit));
            Cudd_Ref(term1);
            term2 = Cudd_Not(Cudd_Cofactor(manager, All_Bdd[i][j], Cudd_bddIthVar(manager, iqubit)));
            Cudd_Ref(term2);
            tmp = Cudd_bddAnd(manager, term2, Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;
            d = Cudd_bddOr(manager, term1, term2);
            Cudd_Ref(d);
            Cudd_RecursiveDeref(manager, term1);
            Cudd_RecursiveDeref(manager, term2);

            //detect overflow
            if ((j == r - 1) && !overflow_done)
                if (overflow3(g, d, c))
                {   if (isAlloc)
                    {
                        r += inc;
                        alloc_BDD(All_Bdd, true); // add new BDDs
                    }
                    else
                    {
                        j -= 1;
                        ++shift;
                        dropLSB(All_Bdd);
                    }
                    overflow_done = 1;
                }
            //sum
            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
            All_Bdd[i][j] = Cudd_bddXor(manager, g, d);
            Cudd_Ref(All_Bdd[i][j]);
            tmp = Cudd_bddXor(manager, All_Bdd[i][j], c);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
            All_Bdd[i][j] = tmp;
            //carry
            if (j == r - 1)
            {
                Cudd_RecursiveDeref(manager, c);
                Cudd_RecursiveDeref(manager, g);
                Cudd_RecursiveDeref(manager, d);
            }
            else
            {
                term1 = Cudd_bddAnd(manager, g, d);
                Cudd_Ref(term1);
                term2 = Cudd_bddOr(manager, g, d);
                Cudd_Ref(term2);
                Cudd_RecursiveDeref(manager, g);
                Cudd_RecursiveDeref(manager, d);
                tmp = Cudd_bddAnd(manager, term2, c);
                Cudd_Ref(tmp);
                Cudd_RecursiveDeref(manager, term2);
                Cudd_RecursiveDeref(manager, c);
                term2 = tmp;
                c = Cudd_bddOr(manager, term1, term2);
                Cudd_Ref(c);
                Cudd_RecursiveDeref(manager, term1);
                Cudd_RecursiveDeref(manager, term2);
            }
        }
    }
    gatecount++;
    nodecount();
}

void Simulator::Phase_shift(int phase, int iqubit)
{
    assert((iqubit >= 0) & (iqubit < n));

    int nshift = w / phase;
    int overflow_done = 0;

    DdNode *g, *c, *tmp, *term1, *term2;

    /* copy */
    DdNode **copy[w];
    for (int i = 0; i < w; i++)
        copy[i] = new DdNode *[r];
    for (int i = 0; i < w; i++)
    {
         for (int j = 0; j < r; j++)
        {
            copy[i][j] = Cudd_ReadOne(manager);
            Cudd_Ref(copy[i][j]);
            tmp = Cudd_bddAnd(manager, copy[i][j], All_Bdd[i][j]);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, copy[i][j]);
            copy[i][j] = tmp;
        }
    }

    for (int i = 0; i < w; i++)
    {
        // init c
        if (i >= w - nshift)
        {
            c = Cudd_bddIthVar(manager, iqubit);
            Cudd_Ref(c);
        }

        for (int j = 0; j < r; j++)
        {
            if (i >= w - nshift)
            {
                term1 = Cudd_bddAnd(manager, copy[i][j], Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
                Cudd_Ref(term1);
                term2 = Cudd_bddAnd(manager, Cudd_Not(copy[i - (w - nshift)][j]), Cudd_bddIthVar(manager, iqubit));
                Cudd_Ref(term2);
                g = Cudd_bddOr(manager, term1, term2);
                Cudd_Ref(g);
                Cudd_RecursiveDeref(manager, term1);
                Cudd_RecursiveDeref(manager, term2);

                //detect overflow
                if ((j == r - 1) && !overflow_done)
                    if (overflow2(g, c))
                    {   if (isAlloc)
                        {
                            r += inc;
                            alloc_BDD(All_Bdd, true);
                            alloc_BDD(copy, true);      // add new BDDs
                        }
                        else
                        {
                            j -= 1;
                            ++shift;
                            dropLSB(All_Bdd);
                            dropLSB(copy);
                        }
                        overflow_done = 1;
                    }

                /* plus */
                Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
                if (Cudd_IsConstant(c))     // must be constant 0
                    All_Bdd[i][j] = g;
                else
                {
                    /* sum */
                    All_Bdd[i][j] = Cudd_bddXor(manager, g, c);
                    Cudd_Ref(All_Bdd[i][j]);
                    /*carry*/
                    if (j == r - 1)
                    {
                        Cudd_RecursiveDeref(manager, g);
                        Cudd_RecursiveDeref(manager, c);
                    }
                    else
                    {
                        tmp = Cudd_bddAnd(manager, g, c);
                        Cudd_Ref(tmp);
                        Cudd_RecursiveDeref(manager, g);
                        Cudd_RecursiveDeref(manager, c);
                        c = tmp;
                    }
                }
            }
            else
            {
                term1 = Cudd_bddAnd(manager, copy[i][j], Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
                Cudd_Ref(term1);
                term2 = Cudd_bddAnd(manager, copy[i + nshift][j], Cudd_bddIthVar(manager, iqubit));
                Cudd_Ref(term2);

                Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
                All_Bdd[i][j] = Cudd_bddOr(manager, term1, term2);
                Cudd_Ref(All_Bdd[i][j]);

                Cudd_RecursiveDeref(manager, term1);
                Cudd_RecursiveDeref(manager, term2);
            }
        }
    }

    for (int i = 0; i < w; i++)
    {
        for (int j = 0; j < r; j++)
            Cudd_RecursiveDeref(manager, copy[i][j]);
        delete[] copy[i];
    }
    gatecount++;
    nodecount();
}

void Simulator::Phase_shift_dagger(int phase, int iqubit)
{
    assert((iqubit >= 0) & (iqubit < n));

    int nshift = w / abs(phase);
    int overflow_done = 0;

    DdNode *g, *c, *tmp, *term1, *term2;

    /* copy */
    DdNode **copy[w];
    for (int i = 0; i < w; i++)
        copy[i] = new DdNode *[r];
    for (int i = 0; i < w; i++)
    {
         for (int j = 0; j < r; j++)
        {
            copy[i][j] = Cudd_ReadOne(manager);
            Cudd_Ref(copy[i][j]);
            tmp = Cudd_bddAnd(manager, copy[i][j], All_Bdd[i][j]);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, copy[i][j]);
            copy[i][j] = tmp;
        }
    }

    for (int i = 0; i < w; i++)
    {
        // init c
        if (i < nshift)
        {
            c = Cudd_bddIthVar(manager, iqubit);
            Cudd_Ref(c);
        }

        for (int j = 0; j < r; j++)
        {
            if (i < nshift)
            {
                term1 = Cudd_bddAnd(manager, copy[i][j], Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
                Cudd_Ref(term1);
                term2 = Cudd_bddAnd(manager, Cudd_Not(copy[w - nshift + i][j]), Cudd_bddIthVar(manager, iqubit));
                Cudd_Ref(term2);
                g = Cudd_bddOr(manager, term1, term2);
                Cudd_Ref(g);
                Cudd_RecursiveDeref(manager, term1);
                Cudd_RecursiveDeref(manager, term2);

                //detect overflow
                if ((j == r - 1) && !overflow_done)
                    if (overflow2(g, c))
                    {   if (isAlloc)
                        {
                            r += inc;
                            alloc_BDD(All_Bdd, true);
                            alloc_BDD(copy, true);      // add new BDDs
                        }
                        else
                        {
                            j -= 1;
                            ++shift;
                            dropLSB(All_Bdd);
                            dropLSB(copy);
                        }
                        overflow_done = 1;
                    }

                /* plus */
                Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
                if (Cudd_IsConstant(c))     // must be constant 0
                    All_Bdd[i][j] = g;
                else
                {
                    /* sum */
                    All_Bdd[i][j] = Cudd_bddXor(manager, g, c);
                    Cudd_Ref(All_Bdd[i][j]);
                    /*carry*/
                    if (j == r - 1)
                    {
                        Cudd_RecursiveDeref(manager, g);
                        Cudd_RecursiveDeref(manager, c);
                    }
                    else
                    {
                        tmp = Cudd_bddAnd(manager, g, c);
                        Cudd_Ref(tmp);
                        Cudd_RecursiveDeref(manager, g);
                        Cudd_RecursiveDeref(manager, c);
                        c = tmp;
                    }
                }
            }
            else
            {
                term1 = Cudd_bddAnd(manager, copy[i][j], Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
                Cudd_Ref(term1);
                term2 = Cudd_bddAnd(manager, copy[i - nshift][j], Cudd_bddIthVar(manager, iqubit));
                Cudd_Ref(term2);

                Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
                All_Bdd[i][j] = Cudd_bddOr(manager, term1, term2);
                Cudd_Ref(All_Bdd[i][j]);

                Cudd_RecursiveDeref(manager, term1);
                Cudd_RecursiveDeref(manager, term2);
            }
        }
    }

    for (int i = 0; i < w; i++)
    {
        for (int j = 0; j < r; j++)
            Cudd_RecursiveDeref(manager, copy[i][j]);
        delete[] copy[i];
    }
    gatecount++;
    nodecount();
}

// Controlled-U1 gate: applies U1(phase) to targ if control is 1
// phase: integer phase (e.g., 2 for S, 4 for T, 8 for pi/8, etc.)
// control: control qubit index
// targ: target qubit index
void Simulator::ControlledU1(int control, int targ, int phase)
{
    std::vector<int> cont(1);
    std::vector<int> ncont(0);
    cont[0] = control;
    Phase_shift(phase * 2, control);
    Phase_shift(phase * 2, targ);
    Toffoli(targ, cont, ncont);
    Phase_shift_dagger(-phase * 2, targ);
    Toffoli(targ, cont, ncont);
    cont.clear();
    ncont.clear();
    gatecount++;
    nodecount();
}

void Simulator::ControlledU1_dagger(int control, int targ, int phase)
{
    std::vector<int> cont(1);
    std::vector<int> ncont(0);
    cont[0] = control;
    Phase_shift_dagger(-phase * 2, control);
    Phase_shift_dagger(-phase * 2, targ);
    Toffoli(targ, cont, ncont);
    Phase_shift(phase * 2, targ);
    Toffoli(targ, cont, ncont);
    cont.clear();
    ncont.clear();
    gatecount++;
    nodecount();
}

void Simulator::PauliX(int iqubit)
{
    assert((iqubit >= 0) & (iqubit < n));

    DdNode *tmp, *term1, *term2;

    for (int i = 0; i < w; i++) // F = All_Bdd[i][j]
    {
        for (int j = 0; j < r; j++)
        {
            /*
            tmp = Cudd_bddCompose(manager,  All_Bdd[i][j], Cudd_Not(Cudd_bddIthVar(manager, iqubit)), iqubit);
            Cudd_Ref(tmp);            
            
            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
            All_Bdd[i][j] = tmp;*/
            
            //term1
            term1 = Cudd_Cofactor(manager, All_Bdd[i][j], Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
            Cudd_Ref(term1);

            tmp = Cudd_bddAnd(manager, term1, Cudd_bddIthVar(manager, iqubit));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term1);
            term1 = tmp;

            //term2
            term2 = Cudd_Cofactor(manager, All_Bdd[i][j], Cudd_bddIthVar(manager, iqubit));
            Cudd_Ref(term2);
            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);

            tmp = Cudd_bddAnd(manager, term2, Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;

            //OR
            All_Bdd[i][j] = Cudd_bddOr(manager, term1, term2);
            Cudd_Ref(All_Bdd[i][j]);
            Cudd_RecursiveDeref(manager, term1);
            Cudd_RecursiveDeref(manager, term2);
        }
    }
    gatecount++;
    nodecount();
}

void Simulator::PauliY(int iqubit)
{
    assert((iqubit >= 0) & (iqubit < n));

    PauliX(iqubit);

    int nshift = w / 2;

    DdNode *g, *c, *tmp, *term1, *term2;
    int overflow_done = 0;

    /* copy */
    DdNode **copy[w];
    for (int i = 0; i < w; i++)
        copy[i] = new DdNode *[r];
    for (int i = 0; i < w; i++)
    {
         for (int j = 0; j < r; j++)
        {
            copy[i][j] = Cudd_ReadOne(manager);
            Cudd_Ref(copy[i][j]);
            tmp = Cudd_bddAnd(manager, copy[i][j], All_Bdd[i][j]);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, copy[i][j]);
            copy[i][j] = tmp;
        }
    }

    for (int i = 0; i < w; i++)
    {
        // init c
        if (i < nshift)
            c = Cudd_Not(Cudd_bddIthVar(manager, iqubit));
        else
            c = Cudd_bddIthVar(manager, iqubit);
        Cudd_Ref(c);

        for (int j = 0; j < r; j++)
        {
            if (i < nshift)
            {
                term1 = Cudd_bddAnd(manager, copy[i + nshift][j], Cudd_bddIthVar(manager, iqubit));
                Cudd_Ref(term1);
                term2 = Cudd_bddAnd(manager, Cudd_Not(copy[i + nshift][j]), Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
                Cudd_Ref(term2);
            }
            else
            {
                term1 = Cudd_bddAnd(manager, Cudd_Not(copy[i - nshift][j]), Cudd_bddIthVar(manager, iqubit));
                Cudd_Ref(term1);
                term2 = Cudd_bddAnd(manager, copy[i - nshift][j], Cudd_Not(Cudd_bddIthVar(manager, iqubit)));
                Cudd_Ref(term2);
            }
            g = Cudd_bddOr(manager, term1, term2);
            Cudd_Ref(g);
            Cudd_RecursiveDeref(manager, term1);
            Cudd_RecursiveDeref(manager, term2);

            //detect overflow
            if ((j == r - 1) && !overflow_done)
                if (overflow2(g, c))
                {   if (isAlloc)
                    {
                        r += inc;
                        alloc_BDD(All_Bdd, true);
                        alloc_BDD(copy, true);      // add new BDDs
                    }
                    else
                    {
                        j -= 1;
                        ++shift;
                        dropLSB(All_Bdd);
                        dropLSB(copy);
                    }
                    overflow_done = 1;
                }

            /* plus 1*/
            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
            if (Cudd_IsConstant(c))
                All_Bdd[i][j] = g;
            else
            {
                /* sum */
                All_Bdd[i][j] = Cudd_bddXor(manager, g, c);
                Cudd_Ref(All_Bdd[i][j]);
                /*carry*/
                if (j == r - 1)
                {
                    Cudd_RecursiveDeref(manager, g);
                    Cudd_RecursiveDeref(manager, c);
                }
                else
                {
                    tmp = Cudd_bddAnd(manager, g, c);
                    Cudd_Ref(tmp);
                    Cudd_RecursiveDeref(manager, g);
                    Cudd_RecursiveDeref(manager, c);
                    c = tmp;
                }
            }
        }
    }

    for (int i = 0; i < w; i++)
    {
        for (int j = 0; j < r; j++)
            Cudd_RecursiveDeref(manager, copy[i][j]);
        delete[] copy[i];
    }
    gatecount++;
    nodecount();
}

void Simulator::PauliZ(std::vector<int> iqubit)
{
    for (int i = 0; i < iqubit.size(); i++)
    {
        assert((iqubit[i] >= 0) & (iqubit[i] < n));
    }
    assert((iqubit.size() == 1) || (iqubit.size() == 2));

    DdNode *c, *tmp, *term1, *term2, *inter, *qubit_and;
    int overflow_done = 0;

    qubit_and = Cudd_ReadOne(manager); // init qubit_and
    Cudd_Ref(qubit_and);
    for (int i = iqubit.size() - 1; i >= 0; i--)
    {
        tmp = Cudd_bddAnd(manager, qubit_and, Cudd_bddIthVar(manager, iqubit[i]));
        Cudd_Ref(tmp);
        Cudd_RecursiveDeref(manager, qubit_and);
        qubit_and = tmp;
    }

    for (int i = 0; i < w; i++)
    {
        c = Cudd_ReadOne(manager); // init c
        Cudd_Ref(c);
        tmp = Cudd_bddAnd(manager, c, qubit_and);
        Cudd_Ref(tmp);
        Cudd_RecursiveDeref(manager, c);
        c = tmp;
        for (int j = 0; j < r; j++)
        {
            term1 = Cudd_bddAnd(manager, All_Bdd[i][j], Cudd_Not(qubit_and));
            Cudd_Ref(term1);
            term2 = Cudd_Not(All_Bdd[i][j]);
            Cudd_Ref(term2);
            tmp = Cudd_bddAnd(manager, term2, qubit_and);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(manager, term2);
            term2 = tmp;
            inter = Cudd_bddOr(manager, term1, term2);
            Cudd_Ref(inter);
            Cudd_RecursiveDeref(manager, term1);
            Cudd_RecursiveDeref(manager, term2);

            //detect overflow
            if ((j == r - 1) && !overflow_done)
                if (overflow2(inter, c))
                {   if (isAlloc)
                    {
                        r += inc;
                        alloc_BDD(All_Bdd, true); // add new BDDs
                    }
                    else
                    {
                        j -= 1;
                        ++shift;
                        dropLSB(All_Bdd);
                    }
                    overflow_done = 1;
                }

            Cudd_RecursiveDeref(manager, All_Bdd[i][j]);
            /* plus 1*/
            if (Cudd_IsConstant(c))
                All_Bdd[i][j] = inter;
            else
            {
                /* sum */
                All_Bdd[i][j] = Cudd_bddXor(manager, inter, c);
                Cudd_Ref(All_Bdd[i][j]);
                /*carry*/
                if (j == r - 1)
                    Cudd_RecursiveDeref(manager, inter);
                else
                {
                    tmp = Cudd_bddAnd(manager, inter, c);
                    Cudd_Ref(tmp);
                    Cudd_RecursiveDeref(manager, c);
                    Cudd_RecursiveDeref(manager, inter);
                    c = tmp;
                }
            }
        }
        Cudd_RecursiveDeref(manager, c);
    }
    Cudd_RecursiveDeref(manager, qubit_and);
    gatecount++;
    nodecount();
}

void Simulator::measure(int qreg, int creg)
{
    assert(creg < nClbits);
    measured_qubits_to_clbits[qreg].push_back(creg);
}
