# The actual Haar divisor reserve controls complete valuation occupation

- **ID:** acs-haar-subcritical-source-transport
- **Stage:** 2-fully-proven; Lean formalization in progress
- **Type:** THEOREM (paper), `[PROVED HERE]`
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Parent:** [subcritical divisor operator](../1-in-progress/acs-haar-subcritical-divisor-operator.md)
- **Scope:** Actual signed finite Haar source, every horizon and every low index.

## Exact statement

Write `n_a=2a+1`, `M_a=haarMass(a)`, `x_a=d_a/sqrt(n_a)` and
`w_a=n_a*M_a`. Let Q contain exactly the primes occurring among the
`n_a`, `1<=a<=X`, and put `C_Q=sum_(p in Q) log(p)/(p^2-1)`.
The finite model outgoing row is

`O0_X(a)=sum_(m,b: n_a*m=n_b, 1<=b<=X, m>=2) Lambda(m)/m^2`.

Let `T_Q=(1/2)*sum_a (C_Q-O0_X(a))*x_a^2`. For the actual
logarithmic prime defect D_X already proved in the corpus,

`D_X + T_Q = (1/2)*sum_e E_Q(e)*|xhat(e)|^2 + R_X`,

where xhat is the complete product Blaschke transform at parameters
`q_p=1/p`,

`E_Q(e)=sum_(p in Q, e_p>0) log(p)*(e_p+1/(p^2-1))`,

and R_X is the original divisor graph form in x with receiving weights
`w_b-1/2`, including the missing-root charge. R_X is nonnegative. The
occupation series is summable. No spectral-domain assumption is imposed
on the finite source. This is an exact source identity with its required
diagonal compensation, not a free addition of outgoing reserve.

## Dependency-closed paper proof

1. The first term of the logarithmic odd-power series gives
   `log((k+1)/k)>=2/(2k+1)`. Apply this to both half cells. Their harmonic
   parallel mass satisfies `M_a>=1/(2*n_a)`, so `w_a>=1/2`.
2. On every original edge `n_a*m=n_b`, square-root multiplicativity gives
   `M_b*(d_a/sqrt(m)-d_b)^2 = w_b*(x_a/m-x_b)^2`.
   The missing-root charge becomes `Lambda(n_a)*w_a*x_a^2`.
   Splitting `w_b=1/2+(w_b-1/2)` therefore gives the unit-weight graph
   form divided by two plus the nonnegative exact remainder R_X.
3. Expand the unit-weight squares. The incoming proper-divisor sum plus
   the missing root is `sum_(m|n_a) Lambda(m)=log(n_a)`. Its outgoing
   diagonal is precisely O0_X. Thus the unit graph form equals
   `sum_a (log(n_a)+O0_X(a))*x_a^2` minus its literal symmetric
   prime kernel. The kernel entry at distinct supported integers r,s is
   `Lambda(s/r)/(s/r)` when r divides s, with the symmetric reverse entry.
4. Unique prime-power factorization puts each nonzero entry on exactly
   one valuation ladder. At prime p it is
   `log(p)*(K_(1/p)-I)`, with equality of all other prime coordinates.
   Every original interaction lies in Q. On the complete valuation
   space, the resulting operator is logarithmic degree minus this
   bounded finite-prime kernel plus C_Q.
5. The corpus's complete general-parameter Blaschke basis diagonalizes
   that original maximal-domain operator. At q=1/p its local ground
   energy is `-1/(p^2-1)` and its positive-label energies are k.
   Adding C_Q leaves exactly E_Q above. The actual source has finite
   coordinate support, hence lies in the original operator domain.
   Inner-product Parseval gives the full summable occupation series.
6. Changing the finite outgoing row O0_X to C_Q costs exactly T_Q.
   Substitute the previous identities to obtain the displayed equality
   and its lower bound by the complete occupation energy.

## Lean status

`TheHaarDivisorFormHasSubcriticalPrimeWeights.lean` passed its direct
Lean check. It proves the sharp mass comparison, exact source-coordinate
identity, nonnegative remainder decomposition, and exact finite number
potential. Its required olean was built for the importing source theorem;
the finished module is wired into the umbrella.

The inverse-prime kernel, operator energy identity, and actual-source
occupation theorem are written and awaiting checks. No umbrella is built.
No axiom checks, web search, novelty checks, or numerical experiments.

## Remaining route gap

This identity does not pay T_Q or the original Gamma/central-mass
remainder. Joint signed Haar payment remains open; first-prime
coarse/detail mixing, the coarse source, and other finite-head costs also
remain. The parent investigation stays in progress.
