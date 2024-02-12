# Local-Configurations-in-Union-Closed-Families
This is the code used to generate all of the computational results in the paper "Local Configurations in Union-Closed Families," currently available at https://arxiv.org/abs/2301.01331.
Three files are included: 

$\mathtt{enumerateFamilies.py}$: This file provides useful methods for the $FC(k, n)$ computations.

$\mathtt{cuttingPlanes.py}$: This file provides a way to detect FC-families, without formal verification of the floating point computations.

$\mathtt{classifyFamiliesWithVerification.py}$: This file implements the Algorithm described in the paper, along with SMT verification of the FC-detection algorithm presented in $\mathtt{cuttingPLanes.py}$.

# Work Flow
The prerequisite software to run these files is an installation of Gurobi Optimization, SageMath, and pySMT in python 3.

Let $\mathcal{A}$ be a family of sets with $\bigcup \mathcal{A} = [n]$, where $[n] = \{ 1, \dots, n \}$. In the following example, $\mathcal{A}$ is a $\mathtt{set}$ of $\mathtt{frozenset}$ objects in python.
To exactly determine if $\mathcal{A}$ is FC, run the method $\mathtt{exactCuttingPlanes}(\mathcal{A}, n)$ from $\mathtt{classifyFamiliesWithVerification.py}$. The result is the value of the predicate "$\mathcal{A}$ is an FC-family."

Suppose we wish to compute $FC(k, n)$ for some integers $k$ and $n$. To this end, use the $\mathtt{FC}()$ method in $\mathtt{classifyFamiliesWithVerification.py}$. First, ensure that $\mathtt{FC}(k, i)$ has been executed on the machine running this method for all $\max (k, n-k) \le i < n$. Then run $\mathtt{FC}(k, n)$, and the returned result is exactly $FC(k, n)$. In this computation, all non-isomorphic Non-FC families of $k$-sets with universe (union of all its sets) $[n]$ are written to files (which is why we needed to ensure the previous $\mathtt{FC}()$ calls have been executed before running $\mathtt{FC}(k, n)$ ). In particular, all of these families with exactly $m$ member-sets are written to the file $\mathtt{NonIsomorphicNFC}[n][k][m]$. Note that inspecting these files is how we observed Conjecture 1 in our paper above.
