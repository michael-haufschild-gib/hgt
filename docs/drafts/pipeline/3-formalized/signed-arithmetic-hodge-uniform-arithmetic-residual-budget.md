# A horizon-independent arithmetic residual budget

## Statement

For the actual arithmetic profile

\[
b(y)=\left|\sum_{t\le y}\Lambda(t)/t-\log y+\gamma\right|+1/y,
\qquad B_N=\sum_{n=1}^N b(\lfloor N/n\rfloor)^2/n,
\]

there are constants C>0 and B>0 such that
b(y)<=C/(1+log y) for every positive integer y and B_N<=B for every natural N.
One may take B=2C^2(1+2*pi^2).

Consequently, for every finite positive-conductor family S, all real coefficients a,
and every N, the actual prime-matrix residuals satisfy

\[
\left\|\sum_{m\in S}a_m r_{m,N}\right\|_2^2
\le B\left(\sum_{m\in S}\phi(m)(1+4\log m)^2\right)
       \left(\sum_{m\in S}a_m^2\right).
\]

## Proof

The corpus's global Mertens theorem supplies A>=0 and c>0 with remainder
at most A exp(-c sqrt(log y)). The quadratic term of the exponential series gives
L exp(-c sqrt L)<=2/c^2 for L>=0, while the exponential itself is at most one.
Thus multiplying the Mertens remainder by 1+log y costs at most A(1+2/c^2).
The inequality log y<=y-1 pays the extra reciprocal term. Take
C=A(1+2/c^2)+1.

For y=floor(N/n), 1<=n<=N, exact roundoff gives
|log(n/N)|<=1+log y. Since 0<=1/(2*pi)<=1,

1+(log(n/N)/(2*pi))^2 <=2(1+log y)^2.

The squared remainder is therefore bounded by 2C^2 times the Wiener kernel.
The constant arithmetic sequence has Chebyshev constant one. Its kernel is
summable and its total mass is at most 1+2*pi^2. Nonnegativity permits the
finite-sum comparison. N=0 has zero budget. The previously proved whole-family
residual inequality supplies the final conclusion without a new arithmetic premise.

## Lean

Module:
formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/TheArithmeticResidualBudgetIsUniformInTheHorizon.lean

Declarations:

- exists_primeMertensRemainder_log_envelope
- exists_uniform_primeMertensSquareBudget
- exists_uniform_ramanujanPrimeResidual_family_bound

Final individual no-olean check passes. All three capstones have only
propext, Classical.choice and Quot.sound as transitive axioms.
Module is wired into the programme umbrella; no umbrella build is used.

## Scope

The bound is uniform over all horizons, conductor sets and coefficient vectors;
conductor dependence is the explicit finite sum above. It controls the literal
prime-matrix residual in the integer-coordinate norm. It does not identify that
norm with the full source graph, pay continuous Gamma or both polar terms,
prove a full-Weil complement sign, or supply growing adjunction-energy separation.
