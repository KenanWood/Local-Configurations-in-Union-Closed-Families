
__author__ = "Kenan Wood"
__email__ = "kewood@davidson.edu"

'''
This file allows for exact computation of FC(k, n) using SMT verification.
'''


from enumerateFamilies import *
from cuttingPlanes import getIPBaseModel, IP, getFrequencies
from math import ceil
from time import time
from itertools import combinations
from sage.all import IncidenceStructure
from pysmt.shortcuts import Symbol, And, GE, LE, Plus, Equals, Times, Div, Int, Real, is_sat, is_unsat, get_model, Solver
from pysmt.typing import INT
import gurobipy as gp


# Alternate cuttingPlanes function for verification. Returns certificates, but does not verify.
def cuttingPlanes(A, n, Pn = None, baseIPModel = None, x = None):
    '''
    Given a family A with universe [n], return True if A is FC and False otherwise.
    Additionally, we return certificates.

    Parameters:
    A: a set of frozensets
    n: the integer such that U(A) = [n]
    Pn: the power of [n]
    baseIPModel, x: the result of getIPBaseModel(n, Pn)

    Returns: (True, FC-certificate c) or (False, Non-FC-certificate)
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
    families = [] # a list of the inicence vectors of maximally violating 
                  # families B produced by the algorithm

    # Add the A \uplus P([n]-{j}) inequalities
    for j in range(1, n+1):
        B = power(set({i for i in range(1, n+1) if i != j}))
        B = uplus(A, B)
        # Get frequencies and incidence vector
        freq = {}
        XB = {}
        for S in Pn:
            if S in B:
                for i in S:
                    if i in freq.keys():
                        freq[i] += 1
                    else:
                        freq[i] = 1
                XB[S] = 1
            else:
                XB[S] = 0
        
        H.addConstr(gp.quicksum(z[i-1]*freq[i] for i in range(1,n+1)) >= len(B)/2
        * gp.quicksum(z[i-1] for i in range(1,n+1)))

        families.append([XB, freq])

    
    H.setObjective(gp.quicksum(z[i] for i in range(n)), gp.GRB.MINIMIZE)

    H.optimize()

    while H.Status != gp.GRB.INFEASIBLE:
      
        c = list(z.X)
        XB = IP(A, c, n, Pn, baseIPModel, x)

        # If X(A,c) is empty, A is FC
        if XB == None:
            baseIPModel.remove(FS)
            return (True, c)
        # Otherwise, add a new constraint, and reoptimize H for the next iteration
        else:
            B_i = getFrequencies(XB, n)
            H.addConstr(gp.quicksum(z[i-1]*B_i[i] for i in range(1,n+1)) >= sum(XB.values())/2
            * gp.quicksum(z[i-1] for i in range(1,n+1)))
            families.append([XB, B_i])
            H.optimize()

    baseIPModel.remove(FS)

    return (False, families)



# FC-verification of a family A
def verify(A, n, isFC, Pn = None):
    '''
    Verifies the FC result on A using pysmt after running cuttingPlanes(A, n).

    isFC is a pair including the proposed result in {True, False} and
    the proposed certificate, either an unsolvable contraint set (corresponding
    to False) or a vector c in Z^n such that X(A, c) is empty (for True).
    '''
    if Pn == None:
        Pn = powerSet(n)

    if isFC[0] == True: # verifying FC family
        c = isFC[1]

        # Create variables
        x = {}
        for S in Pn:
            x[S] = Symbol(str(tuple(S)), INT)

        formula = []

        # UC constraints
        for S,T in combinations(Pn, 2):
            formula.append(LE(Plus(x[S], x[T]), Plus(Int(1), x[S | T])))

        for S in Pn:
            for setA in A:
                formula.append(LE(x[S], x[setA | S]))

        for S in Pn:
            formula.append(And(LE(Int(0), x[S]), LE(x[S], Int(1))))

        formula.append(LE(Plus([
            Times(Int(int(sum(c[j-1] for j in S) - sum(c[j-1] for j in range(1, n+1) if j not in S))), x[S]) for S in Pn
        ]), Int(-1)))


        formula = And(formula)

        model = get_model(formula, solver_name="z3")
        if model: # there is a solution B
            XB = {}
            for S in Pn:
                if model[S] == Int(1):
                    XB[S] = 1
                else:
                    XB[S] = 0
            return XB
        else:
            return True

    
    else: # verifying Non-FC family
        families = isFC[1]

        # Create variables
        z = {}
        for i in range(1, n+1):
            z[i] = Symbol(str(i), INT)

        # Nonnegativity
        formula = [GE(z[i], Int(0)) for i in range(1, n+1)]

        # Nonzero
        formula.append(GE(Plus(z.values()), Int(1)))

        for XB, freq in families:
            # Main family constraints
            formula.append(
                GE( Times( Int(2), Plus( [Times(Int(freq[i]), z[i]) for i in range(1, n+1)] ) ), # 2 * (\sum |B_i|*z_i) >=
                Times( Times(Int(int(sum(XB.values())))), Plus(z.values()) ) ) # |B| * \sum z_i
            )

        formula = And(formula)

        model = get_model(formula, solver_name="z3")
        if model:
            return list([int(model.get_py_value(z[i])) for i in range(1, n+1)])
        else:
            return True



def exactCuttingPlanes(A, n, Pn = None, baseIPModel = None, x = None):
    '''
    Runs the entire cutting planes algorithm to determine if A is FC,
    and verifies the result using pySMT's interface to the Z3 SMT solver.
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
    families = [] # a list of the inicence vectors of maximally violating 
                  # families B produced by the algorithm

    # Add the A \uplus P([n]-{j}) inequalities
    for j in range(1, n+1):
        B = power(set({i for i in range(1, n+1) if i != j}))
        B = uplus(A, B)
        # Get frequencies and incidence vector
        freq = {}
        XB = {}
        for S in Pn:
            if S in B:
                for i in S:
                    if i in freq.keys():
                        freq[i] += 1
                    else:
                        freq[i] = 1
                XB[S] = 1
            else:
                XB[S] = 0
        
        H.addConstr(gp.quicksum(z[i-1]*freq[i] for i in range(1,n+1)) >= len(B)/2
        * gp.quicksum(z[i-1] for i in range(1,n+1)))

        families.append([XB, freq])

    H.setObjective(gp.quicksum(z[i] for i in range(n)), gp.GRB.MINIMIZE)

    H.optimize()

    while True:
        if H.Status == gp.GRB.INFEASIBLE: # verify, and update c if incorrect.
            isFC = (False, families)
            c = verify(A, n, isFC, Pn)
            if c == True: # correct computation
                baseIPModel.remove(FS)
                return False
            # else continue as usual
        else:
            c = list(z.X)

        XB = IP(A, c, n, Pn, baseIPModel, x)

        # If X(A,c) is empty, A is FC
        if XB == None:
            isFC = (True, c)
            # verify
            XB = verify(A, n, isFC, Pn)
            if XB != True: # if verifiably incorrect, continue as usual
                B_i = getFrequencies(XB, n)
                H.addConstr(gp.quicksum(z[i-1]*B_i[i] for i in range(1,n+1)) >= sum(XB.values())/2
                * gp.quicksum(z[i-1] for i in range(1,n+1)))
                families.append([XB, B_i])
                H.optimize()
            else:
                baseIPModel.remove(FS)
                return True
        # Otherwise, add a new constraint, and reoptimize H for the next iteration
        else:
            B_i = getFrequencies(XB, n)
            H.addConstr(gp.quicksum(z[i-1]*B_i[i] for i in range(1,n+1)) >= sum(XB.values())/2
            * gp.quicksum(z[i-1] for i in range(1,n+1)))
            families.append([XB, B_i])
            H.optimize()


def containsProperFC(A, previousCanonForms):
    '''
    Determines if A properly contains an FC family (not in previousCanonForms.)

    Parameters:
    A: the family being checked.
    previousCanonForms: a set of the canonical forms of the previous layer.
    '''
    for S in A:
        A.remove(S)

        canonA = IncidenceStructure(A)
        canonA.relabel(canonA.canonical_label()) # canonical form of A
        # make it hashable
        canonA = frozenset({frozenset(T) for T in canonA.blocks()})

        if canonA not in previousCanonForms:
            A.add(S)
            return True

        A.add(S)

    return False


def getNFCFamilies(n, k, m):
    '''
    Given that the files NonIsomorphicNFC[i][k][m-1] are stored
    on the computer running this function for all max{k, n-k} <= i <= n and were
    generated with this algorithm, return a list of all non-isomorphic Non-FC
    families of m distinct k-sets with universe [n]. Then write the results to
    file NonIsomorphicNFC[n][k][m].

    Parameters:
    n: a positive integer
    k: a positive integer
    m: a positive integer

    Return: a list of all non-isomorphic Non-FC families of m distinct k-sets 
            with universe [n]
    '''
    if n < 1 or k < 1 or m < 1:
        raise ValueError
    
    if m*k < n:
        return []

    canonicalFamilies = {True: set(), False: set()}

    Pn = powerSet(n)
    baseIPModel, x = getIPBaseModel(n, Pn) # base IP model for the cuttingPlanes algorithm

    # if m is minimal
    if (m-1)*k < n:
        NFC = set()
        for A in enumerateFamilies(n, k, m):
            isFC = exactCuttingPlanes(A, n, Pn, baseIPModel, x)
            if not isFC:
                NFC.add(A)

        writeNonIsomorphicNFCtoFile(n, k, m, NFC)
        return NFC


    # Obtain all previous NFC families
    previousNFC = {}
    # For i in [max{n-k, k}, n],
    for i in range(max(n-k, k), n+1):
        # Read the desired file
        try:
            previousNFC[i] = readNFC(i, k, m-1, "NonIsomorphicNFC")
        except:
            previousNFC[i] = []

    # Get the set of all canonical forms
    previousCanonForms = set()
    for i in range(max(n-k, k), n+1):
        for A in previousNFC[i]:
            canonA = IncidenceStructure(A)
            canonA.relabel(canonA.canonical_label()) # canonical form of A
            # make it hashable
            canonA = frozenset({frozenset(T) for T in canonA.blocks()})
            previousCanonForms.add(canonA)



    for i in range(max(n-k, k), n+1):

        # Since we are looping through all S \subseteq [n] such that
        # U(family U S) = [n], we must have {k \in Z | i+1 <= k <= n} \subseteq S
        # which leaves k - (n - i) = k - n + i elements to choose from in [i].
        k_iSets = list(combinations(range(1, i+1), k - n + i))
        toAdd = frozenset(range(i+1, n+1))
        
        for F in previousNFC[i]:
            for S in k_iSets: # For each possible k-set to add
                S = frozenset(S).union(toAdd)

                if S in F:
                    continue

                F.add(S) # add S to the family

                # Check for isomorphisms
                canonF = IncidenceStructure(F)
                canonF.relabel(canonF.canonical_label()) # canonical form of F
                # make it hashable with universe [n]
                canonF = frozenset({frozenset([j+1 for j in T]) for T in canonF.blocks()})
                # If that canonical form has been seen before
                if canonF in canonicalFamilies[True] or canonF in canonicalFamilies[False]:
                    # continue to next iteration
                    F.remove(S)
                    continue

                # Check if F properly contains an FC family
                if containsProperFC(F, previousCanonForms):
                    F.remove(S)
                    continue

                # Now we may run the cutting planes algorithm to determine
                # if family is FC or Non-FC
                isFC = exactCuttingPlanes(F, n, Pn, baseIPModel, x)

                canonicalFamilies[isFC].add(canonF)

                F.remove(S)
    
    # Write results to file for the next iteration
    writeNonIsomorphicNFCtoFile(n, k, m, canonicalFamilies[False])

    return canonicalFamilies[False]



def FC(k, n, m = None):
    '''
    Determines the value of FC(k, n), starting at the initial 
    number of sets m = ceil(n / k), unless otherwise specified. Assumes
    FC(k, i) has been computed on the machine running this funtion for all
    max{k, n-k} <= i < n. Writes all results to files.

    Parameters:
    k: a positive integer
    n: a positive integer
    m: if specified, the least integer such that NonIsomorphicNFC[n][k][m] is not
       stored on the machine running this algorithm.
    '''
    if m == None:
        m = ceil(n / k)

    print("initialized to n = "+str(n)+", k = "+str(k)+", m = "+str(m))

    initial = time()
    t = time()
    NFC = getNFCFamilies(n, k, m)
    print("Completed getNFCFamilies(" + str(n) + ", " + str(k) + ", " + str(m) + ") in " + str(time()-t) + " seconds")
    t = time()
    while len(NFC) > 0:
        m += 1
        NFC = getNFCFamilies(n, k, m)
        print("Completed getNFCFamilies(" + str(n) + ", " + str(k) + ", " + str(m) + ") in " + str(time()-t) + " seconds")
        t = time()
    print("")
    print("Total time to complete:", time()-initial)
    return m


if __name__ == "__main__":
    FC(4, 4)
    FC(4, 5)
    FC(4, 6)
    FC(4, 7)

    FC(5, 5)
    FC(5, 6)
    FC(5, 7)

    FC(6, 6)
    FC(6, 7)
    FC(6, 8)

    FC(4, 8)
