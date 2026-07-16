# Polynomial Taylor Magnitudes Force Exponentially Accurate Prouhet Phase Locks

- **ID:** `polynomial-taylor-prouhet-phase-lock`
- **Stage:** 3-formalized / needs scientific-novelty audit
- **Type:** THEOREM CANDIDATE / GENERAL DA PHASE LAW / PROUHET OSCULATION
- **Scientific status:** `[PROVED HERE] [LEAN FORMALIZED] [NOVELTY UNVERIFIED] [SIGNIFICANT]`
- **Statement:** For exact polynomial logarithmic Taylor magnitudes with exponent `beta>2`, every integer ADE forces the coefficient phases to satisfy an exponentially accurate bounded-window trigonometric relation inside one minimal high-order Prouhet class at every sufficiently large coefficient index.

## Goal

Pass from the magnitude-only recurrent Prouhet lock to the first phase-sensitive necessary law. A logarithmic bend only says two magnitudes are close. The full coefficient identity is stronger: after all atoms separated by a positive power of the balanced index are removed, the remaining Prouhet cluster must cancel to exponentially small relative error.

## Setup

Fix `B>0`, `beta>2`, and write

`a_n=exp(-B n^beta)u_n`, `|u_n|=1`.                                       `(1)`

Assume that `f(z)=sum_n a_nz^n` satisfies a nonzero integer ADE `P` of maximal total dependent-variable degree `D`.

For a bounded degree-`D` offset multiset `A`, write `m_A(r)` for the multiplicity of the offset `r` and define its moments

`p_j(A)=sum_r m_A(r)r^j`.                                                   `(2)`

Put

`L=ceil(beta)-1`,

and call

`sig_L(A)=(p_2(A),...,p_L(A))`                                             `(3)`

its polynomial-scale signature. Degree and source-sum constraints already fix `p_0` and `p_1`.

## Phase-lock theorem `[PROVED HERE]`

For every residue class `tau modulo D`, there exist

- a finite set `C_tau` of at least two distinct bounded degree-`D` offset multisets, all in the least active source-sum class;
- nonzero integer-valued polynomials `w_(tau,A)(q) in Q[q]` for `A in C_tau`;
- constants `c_tau>0`, `eta_tau>0`, and `M_tau>=0`;

such that:

1. all `A in C_tau` have the same signature `(3)`, which is lexicographically minimal among the surviving bounded patterns;
2. if

   `V_tau(q)=min_(A in C_tau) B sum_r m_A(r)(q+r)^beta`,                    `(4)`

   and

   `delta_(tau,A)(q)=B sum_r m_A(r)(q+r)^beta-V_tau(q)`,                   `(5)`

   then `0<=delta_(tau,A)(q)=O_(P,beta)(1)`;
3. for every sufficiently large `q` with coefficient index `N=Dq+tau`,

   `|sum_(A in C_tau) w_(tau,A)(q) exp(-delta_(tau,A)(q))`

   `   * product_r u_(q+r)^(m_A(r))|`

   ` <= q^(M_tau) exp(-c_tau q^(eta_tau)).`                                `(PL)`

One may take

`eta_tau=min(beta-2, beta-L)>0`                                            `(6)`

after decreasing the constant. Thus a DA phase tail lies in exponentially shrinking neighborhoods of a fixed finite family of local Prouhet hypersurfaces at every scale.

## Proof

Retain the original coefficient indexing. Finitely many exceptional initial coefficients can occur only in macroscopically imbalanced atoms and are absorbed by the confinement estimate below. Suppose

`P(z,f,f',...,f^(m))=0`                                                    `(7)`

with `P in Z[z,Y_0,...,Y_m]` nonzero and maximal total `Y`-degree `D`. Generic coefficient extraction and grouping give

`sum_(nu in A_N)c_(N,nu)a^nu=0`,                                          `(8)`

where the nonzero `c_(N,nu)` are integers of polynomially bounded number and size.

### 1. Stable bounded patterns and polynomial weights

Fix a residue `tau modulo D` and write `N=Dq+tau`. The polynomial-confinement argument for `beta>2` applies without a bound on `D`: lower degrees are separated at scale `q^beta`, larger top-degree source shifts at scale `q^(beta-1)`, and sufficiently imbalanced tuples in the least active shift at scale `q^(beta-2)`. Balanced survival supplies a fixed-offset nonzero witness in that shift.

Choose the offset window so large that every atom outside it lies at least `c q^(beta-2)` above the minimum for all large `q`. Inside the window there are only finitely many degree-`D` offset multisets with the fixed source sum.

For one such multiset `A`, the grouped coefficient in (8) is a finite sum of symmetrized products of falling factorials `(q+r)_j`, divided only by the fixed multiplicity factorials of repeated source indices. It is therefore a polynomial

`w_(tau,A)(q) in Q[q]`                                                     `(9)`

which takes integer values at integer `q`. Delete the identically zero polynomials. Every remaining `w_(tau,A)` is a nonzero integer for all sufficiently large integer `q`, since a nonzero polynomial has only finitely many roots. The balanced witness ensures that the surviving finite pattern set is nonempty.

### 2. Moment lexicography selects the Prouhet cluster

All surviving bounded patterns have the same `p_0=D` and the same `p_1`, fixed by the source sum. Their valuations are

`B sum_r m_A(r)(q+r)^beta`

` = B sum_(j>=0) binom(beta,j)p_j(A)q^(beta-j)`,                           `(10)`

with the usual finite expansion when `beta` is an integer and an asymptotic expansion to arbitrary fixed order otherwise.

For every `2<=j<=L=ceil(beta)-1`, one has `j<beta`, so `binom(beta,j)>0` and `q^(beta-j)->infinity`. Order the finite signatures `(p_2,...,p_L)` lexicographically and let `C_tau` be the patterns with the least signature.

If `A` lies outside `C_tau`, let `j<=L` be its first differing moment. Lexicographic minimality and the positivity above give

`V_A(q)-V_C(q)>=c_A q^(beta-j)`                                           `(11)`

against every `C in C_tau`, for all large `q`. Finiteness of the pattern set yields common constants and the uniform bound

`V_A(q)-V_tau(q)>=c q^(beta-L)`.                                          `(12)`

Combining (12) with the confinement gaps for all other degrees, shifts, and offsets gives

`V_A(q)-V_tau(q)>=c q^eta`,

for every atom excluded from `C_tau`, with `eta=min(beta-2,beta-L)>0` after decreasing `c`.

### 3. Relative valuations inside the cluster are bounded

If `beta` is not an integer, all moments through `L=floor(beta)` agree inside `C_tau`; the first possible difference has order `L+1>beta`, so (10) gives `V_A(q)-V_C(q)=o(1)`. If `beta=k` is an integer, then `L=k-1`; the first possible difference is the constant `j=k` term, and all higher terms vanish. Hence the numbers `delta_(tau,A)(q)` in (5) are nonnegative and uniformly bounded.

### 4. The exact coefficient identity forces the phase lock

Substitute (1) into (8), isolate the terms indexed by `C_tau`, and divide by `exp(-V_tau(q))`. Every excluded atom has relative magnitude at most `exp(-c q^eta)`. The number and integer weights of all atoms are polynomially bounded in `q`. Thus there is `M_tau` such that

`|sum_(A in C_tau) w_(tau,A)(q) exp(-delta_(tau,A)(q))`

`   * product_r u_(q+r)^(m_A(r))|`

` <= q^(M_tau)exp(-c_tau q^(eta_tau))`,                                   `(13)`

with `eta_tau=eta`, proving `(PL)`.

If `C_tau` contained only one pattern, its left side would be

`|w_(tau,A)(q)|exp(-delta_(tau,A)(q))=|w_(tau,A)(q)|>=1`,

because then `delta=0` and the weight is a nonzero integer for all large integer `q`. The right side tends to zero, a contradiction. Therefore `|C_tau|>=2`. Every two patterns in the cluster agree in moments through `L`, so their difference is divisible by `(T-1)^(L+1)=(T-1)^ceil(beta)`. `square`

## Boundary attacks

1. **Finite initial coefficients cannot remove the cluster.** Balanced survival occurs entirely at indices `q+O(1)` on the eventual exact-magnitude tail. Any atom using a fixed initial index is macroscopically imbalanced and belongs to the exponentially separated complement.
2. **No sign claim is made beyond `L`.** Lexicographic ordering uses only `j<beta`, where the binomial coefficients are positive. Later terms are bounded or decaying and remain inside the cluster weights.
3. **Repeated source indices are harmless.** Grouping divides a symmetric falling-factorial polynomial by fixed multiplicity factorials, producing an integer-valued polynomial in `Q[q]`; pointwise integrality supplies the singleton lower bound.
4. **The error is exponential in a positive power.** The finite bounded complement loses at scale `q^(beta-L)` and the unbounded complement at scale `q^(beta-2)`; polynomially many coefficient weights cannot erase either gap.

## Parent and novelty status

- **Prouhet--Tarry--Escott theory:** classical PTE theory classifies or constructs finite multisets with matching power sums. It does not force one such class to occur as the dominant phase-cancellation locus of every ADE coefficient identity.
- **Nonlinear Taylor recurrences:** modern D-algebraic coefficient work extracts nonlinear recurrences and studies arithmetic or effective computation. The located results do not give an Archimedean phase relation with exponentially small error for arbitrary complex coefficients.
- **Newton polygon and transseries methods:** these organize asymptotic balances of solutions or formal transseries. Here the asymptotic object is instead the grouped convolution recurrence for the Taylor coefficients, and the surviving phases are unconstrained unit complex numbers.
- **q-algebraic coefficient asymptotics:** the established q-algebraic theory concerns equations with a q-shift and grid-based Hahn series. No q-shift is assumed here.
- **Preliminary verdict:** exact, equivalent, recurrence, Prouhet, Newton-polygon, and phase-cancellation searches located no theorem implying `(PL)`. Novelty remains unverified pending full specialist comparison and independent proof review.

## Exact RH-route scope

This law says that a polynomial-magnitude DA escape requires exponentially accurate local phase synchronization at every scale. It excludes only RH implementations that replace exact spectral, positivity, norm, or Euler information by the polynomial magnitude jet without retaining these phase locks. It does not categorically exclude the complete literature criteria.

## Lean status

Formalized unconditionally in
`formal/GaloisForLFunctions/HTGeometry/PolynomialTaylorProuhetPhaseLock.lean`.
The capstone theorem `exists_polynomialTaylorProuhetPhaseLock` proves, for
`beta > 2`, `B > 0`, an integer-coefficient ADE of positive maximal dependent-variable
degree, and every residue `tau < D`:

- a nonempty finite survivor set and its least-source, lexicographically minimal moment cluster;
- at least two distinct patterns in that cluster;
- nonzero integer weight polynomials giving the exact grouped ADE weights at every large index;
- common moments through `ceil(beta)-1` and divisibility of every cluster difference by
  `(X-1)^ceil(beta)`;
- nonnegative uniformly bounded relative valuations inside the cluster; and
- the normalized phase-lock inequality with exponent
  `min(beta-2, beta-(ceil(beta)-1)) > 0` and a polynomial weight-mass factor.

The proof has no project axioms or placeholders; `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] Exact candidate phase law stated.
- [x] Complete unconditional paper proof.
- [ ] Parent-theory and literature novelty gates.
- [x] Whole theorem formalized unconditionally in Lean.

## Log

- 2026-07-11 — Opened the phase-sensitive propagation of the recurrent polynomial Prouhet lock.
- 2026-07-11 — Proved the residue-class polynomial-weight decomposition, minimal Prouhet cluster selection, and exponentially accurate local phase-lock law; promoted to paper-proven with novelty unverified.
- 2026-07-16 — Formalized the full residue-wise Prouhet cluster, bounded relative valuation, exponentially accurate phase-lock, nonsingleton cardinality, and Prouhet divisibility theorem in Lean 4; moved to stage 3.
