
__author__ = "Kenan Wood"
__email__ = "kewood@davidson.edu"

'''
This file contains many useful method for determining useful properties about FC-families.
'''

from itertools import combinations, permutations
from sage.all import IncidenceStructure


def unionClosure(A):
    '''
    Returns the union-closure of a family of sets A.
    The union-closure of A is defined to be the minimal union-closed
    family containing A \cup \{\emptyset\}.
    '''

    if len(A) == 0:
        return set({frozenset()})

    A = set(A)
    
    # Choose an element of A
    S = next(iter(A))
    A.remove(S)
    B = A.copy()
    A.add(S)
    B = unionClosure(B)
    closure = B.copy()
    for b in B:
        closure.add(b | S)
    return closure


def getUniverse(A):
    '''
    Returns the universe U(A) of a given family of sets A.
    '''
    universe = set({})
    for S in A:
        universe = universe.union(S)
    
    return universe


def uplus(A, B):
    '''
    Determines the set {S \cup T : S in A, T in B}, given families A and B.
    '''
    uplusAB = set({})
    for S in A:
        for T in B:
            uplusAB.add(S.union(T))
    return uplusAB


def power(S):
    '''
    Returns the powerset of S, where the elements in S are hashable.
    '''
    S = set(S)

    if len(S) <= 0:
        return set({frozenset({})})
    
    x = next(iter(S))
    T = S.difference({x})
    powerSubProblem = power(T)
    containsx = set({frozenset({x}) | A for A in powerSubProblem})

    return set(powerSubProblem.union(containsx))


def powerSet(n):
    '''
    Returns the power set of [n]
    n > 0
    '''
    if n == 1:
        return set({frozenset({}), frozenset({1})})
    
    powerSubProblem = powerSet(n-1)
    containsN = {frozenset({n}) | A for A in powerSubProblem}

    return powerSubProblem.union(containsN)


def enumerateFamilies(n, k, m):
    '''
    Enumerates all nonisomorphic families of m distinct k-sets with universe [n].
    '''
    families = set({}) # Non-isomorphic families

    # For each desired family
    for comb in combinations(combinations(range(1, n+1), k), m):
        F = set({})
        for S in comb:
            F.add(frozenset(S))
        
        if len(getUniverse(F)) == n: 
            # Check for isomorphisms
            t = 0
            for family in families:
                if IncidenceStructure(F).is_isomorphic(IncidenceStructure(family)):
                    t = 1
                    break
            if t == 0:
                families.add(frozenset(F))

        # Else U(F) \neq [n]

    return families



def readNFC(n, k, m, fileType):
    '''
    Reads the file [fileType][n][k][m].txt assuming the file exists.
    The parameter fileType must be either "NFC" or "NonIsomorphicNFC"
    '''
    filename = fileType + str(n) + str(k) + str(m) + ".txt"
    NFC = []
    with open(filename, 'r') as file:
        for line in file:
            familyString = line.split()
            family = set({})
            for stringS in familyString:
                s = set({})
                for elem in stringS:
                    s.add(int(elem))
                family.add(frozenset(s))
            NFC.append(family)
    
    return NFC


def writeNonIsomorphicNFCtoFile(n, k, m, NFC):
    '''
    Writes all non-isomorphic Non-FC families of m distict k-sets with
    universe [n], as given in the parameter NFC, to a file named 
    "NonIsomorphicNFC[n][k][m].txt"
    '''
    filename = "NonIsomorphicNFC" + str(n) + str(k) + str(m) + ".txt"
    file = open(filename, 'w')

    i = 1
    for family in NFC:
        familyString = ""
        for S in family:
            listS = list(S)
            listS.sort()
            for elem in listS:
                familyString += str(elem)
            familyString += " "
        if i != len(NFC):
            file.write(familyString[:-1] + '\n')
        else:
            file.write(familyString[:-1])
        i += 1



def applyPermutation(A, perm):
    '''
    Applies the permutation perm to the family of sets A
    '''
    permA = set({})
    for S in A:
        permS = set({})
        for elem in S:
            permS.add(perm[elem])
        permA.add(frozenset(permS))
    return permA



def getPermutationStrings(n):
    '''
    Returns a list of all permutations of the string "12...n"
    '''
    if n == 1:
        return ['1']
    
    subPerms = getPermutationStrings(n-1)
    perms = []
    for perm in subPerms:
        for i in range(0, n):
            perms.append(perm[:i] + str(n) + perm[i:])

    return perms



def getPermutations(n):
    '''
    Returns a list of all permutations (as dictionaries) of [n],
    where n is a positive integer
    '''
    perms = []
    for perm in permutations(range(1, n+1)):
        permDict = {}
        for i in range(1, n+1):
            permDict[i] = perm[i-1]
        perms.append(permDict)
    return perms



def writeAllNFCtoFile(n, k, m, NFC):
    '''
    Writes ALL Non-FC families of m distict k-sets with
    universe [n] a file named "NFC[n][k][m].txt"
    '''
    filename = "NFC" + str(n) + str(k) + str(m) + ".txt"
    with open(filename, 'w') as file:

        permutations = getPermutations(n)
        allNFC = set({})
        for NFCSet in NFC:
            for permutation in permutations:

                allNFC.add(frozenset(applyPermutation(NFCSet, permutation)))

        i = 0
        for F in allNFC:
            if i > 0:
                file.write('\n')
            i = 1
            FString = ""
            for S in F:
                for elem in S:
                    FString += str(elem)
                FString += " "
            file.write(FString[:-1])

