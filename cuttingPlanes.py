
__author__ = "Kenan Wood"
__email__ = "kewood@davidson.edu"

'''
This file provides a framework for determining FC-families using Gurobi Optimization and floating point arithmetic.
'''

import gurobipy as gp
from enumerateFamilies import *


def getIPBaseModel(n, Pn = None):
    '''
    Returns a pair (m, x) where m is a Gurobi model object with the variable x
    and m contains only the UC constraints.
    '''
    if Pn == None:
        Pn = powerSet(n)

    m = gp.Model()
    m.Params.LogToConsole = 0

    # Create variables indexed by P(n)
    x = m.addVars(list(Pn), vtype=gp.GRB.BINARY, name='x')

    for s in Pn:
        for t in Pn:
            m.addConstr(x[s] + x[t] <= 1 + x[s | t])

    return m, x


def IP(A, c, n, Pn = None, m = None, x = None):
    '''
    Returns None if X(A,c) is empty, and the optimum of IP(A, c) otherwise.

    If m, x is passed, it must be the result of getIPBaseModel(n, P(n))
    and the FS inequalities must be manually added to model m before this
    computation.
    '''

    if Pn == None:
        Pn = powerSet(n)

    if m == None or x == None:
        m, x = getIPBaseModel(n, Pn)
        FS = m.addConstrs((x[S] <= x[a | S] for S in Pn for a in A), name='FS')
    
    m.setObjective(gp.quicksum(c[i-1]*(gp.quicksum(x[S] for S in Pn) - 
    2*gp.quicksum(x[S] for S in Pn if i in S)) for i in range(1,n+1)), gp.GRB.MAXIMIZE)

    WV = m.addConstr(gp.quicksum(
    (gp.quicksum(c[i-1] for i in S)
    - gp.quicksum(c[i-1] for i in set({a for a in range(1, n+1) if a not in S})))
    * x[S]
    for S in Pn) <= -1, name='WV')
    
    m.optimize()

    m.remove(WV)


    if m.Status == gp.GRB.INFEASIBLE:
        return None
    
    else:
        return dict({S: x[S].X for S in Pn})



def getFrequencies(XB, n):
    '''
    Given an incidence vector XB of a family B with universe [n],
    return a dictionary which maps each i in [n] to |B_i|.
    '''
    B_i = {}
    for i in range(1,n+1):
        B_i[i] = 0
    
    for S in XB.keys():
        if XB[S] < 0.5: continue # floating point error control
        for elem in S:
            B_i[elem] += 1
    
    return B_i



def cuttingPlanes(A, n, Pn = None, baseIPModel = None, x = None):
    '''
    Given a family A with universe [n], return True if A is FC and False
    otherwise. We do not require that A is UC or that A contains the emptyset.

    Parameters:
    A: a set of frozensets
    n: the integer such that U(A) = [n]
    Pn: (optional) the powerset of [n]
    baseIPModel, x: (optional) the result of getIPBaseModel(n, Pn)

    Returns: True or False, depending on if A is FC or Non-FC.
    '''
    A = unionClosure(A)
    
    if Pn == None:
        Pn = powerSet(n)
    if x == None:
        baseIPModel, x = getIPBaseModel(n, Pn)

    FS = baseIPModel.addConstrs((x[S] <= x[a | S] for S in Pn for a in A), name='FS')

    # Initialize the set H as an integer optimization model
    H = gp.Model()
    H.Params.LogToConsole = 0

    z = H.addMVar(shape=n, vtype=gp.GRB.INTEGER, name='z', lb = 0)

    H.addConstr(gp.quicksum(z[i] for i in range(n)) >= 1)

    # Add the A \uplus P([n]-{j}) inequalities for j in [n].
    for j in range(1, n+1):
        B = power(set({i for i in range(1, n+1) if i != j}))
        B = uplus(A, B)
        # Get frequencies
        freq = {}
        for S in B:
            for i in S:
                if i in freq.keys():
                    freq[i] += 1
                else:
                    freq[i] = 1
        
        H.addConstr(gp.quicksum(z[i-1]*freq[i] for i in range(1,n+1)) >= len(B)/2
        * gp.quicksum(z[i-1] for i in range(1,n+1))) # z[i-1] instead of z[i] since z is indexed by [0: n-1].
    
    H.setObjective(gp.quicksum(z[i] for i in range(n)), gp.GRB.MINIMIZE)

    H.optimize()

    while H.Status != gp.GRB.INFEASIBLE:
      
        c = list(z.X)
        XB = IP(A, c, n, Pn, baseIPModel, x)

        # If X(A,c) is empty, return true
        if XB == None:
            baseIPModel.remove(FS) # leave the baseIPModel unchanged for future use
            return True
        # Otherwise, add a new constraint, and reoptimize H for the next iteration
        else:
            B_i = getFrequencies(XB, n)
            H.addConstr(gp.quicksum(z[i-1]*B_i[i] for i in range(1,n+1)) >= sum(XB.values())/2
            * gp.quicksum(z[i-1] for i in range(1,n+1)))
            H.optimize()

    baseIPModel.remove(FS)
    return False


if __name__ == "__main__":

    A = {frozenset(), frozenset({1,2,3}), frozenset({1,2,4,5}), frozenset({1,3,4,5}), frozenset({2,3,4,5})}
    n = 5
    print(cuttingPlanes({frozenset(S) for S in A}, n))



