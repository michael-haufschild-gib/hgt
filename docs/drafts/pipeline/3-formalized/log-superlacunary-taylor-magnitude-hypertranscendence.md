# Log-Superlacunary Taylor Magnitudes Force Hypertranscendence

- **ID:** `log-superlacunary-taylor-magnitude-hypertranscendence`
- **Stage:** 3-formalized / needs scientific-novelty audit
- **Type:** THEOREM (paper) / GENERAL HT LAW / COEFFICIENT CONSTRAINT
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANT]`
- **Statement:** If an entire power series has eventually nonzero coefficients and the negative logarithms of their moduli have successive ratios tending to infinity, then the function is hypertranscendental over `C(z)`, for every possible choice of coefficient phases.

## Goal

Find a coefficient-magnitude law for HT that does not use coefficient arithmetic, support gaps, random phases, or a flow. The native constraint is the coefficient identity of a hypothetical ADE. Mahler's normalization makes that identity integral; an integral zero-sum cannot have one convolution atom exponentially larger than the sum of all the others.

The resulting law is a full-support magnitude analogue of a gap theorem. It is strictly outside Ostrowski's finite-coefficient-basis obstruction: the explicit positive example below has every coefficient in the one-generator field `Q(exp(-1))`.

## Setup

Let

`f(z)=sum_(n>=0) a_n z^n`

be a formal power series over `C`. Assume that `a_n!=0` for all sufficiently large `n`, and put

`b_n=-log|a_n|`

on that tail.

Finite Taylor prefixes are irrelevant to DA versus HT: if `T` is the first index of an all-nonzero tail, then

`g(z)=z^(-T)(f(z)-sum_(n<T)a_nz^n)`

is DA whenever `f` is DA, because DA functions form a differential field and rational multiplication preserves DA. Thus it is enough to treat the case `a_n!=0` for every `n`.

## The Archimedean tropical bend law `[PROVED HERE]`

Assume that `f` is DA over `C(z)`. By Mahler's integer-normalization theorem, there is a nonzero polynomial

`P in Z[z,Y_0,...,Y_m]`

such that

`P(z,f,f',...,f^(m))=0`.                                                     `(1)`

Introduce algebraically independent coefficient variables `(X_n)_(n>=0)` and the generic series

`F(z)=sum_(n>=0) X_nz^n`.

For every `N`, expand and group equal coefficient monomials:

`[z^N]P(z,F,F',...,F^(m))`

` = sum_(nu in A_N) c_(N,nu) X^nu`,                                         `(2)`

where:

- every `c_(N,nu)` is a nonzero integer;
- `nu=(nu_0,nu_1,...)` has finite support and `X^nu=prod_n X_n^(nu_n)`;
- the total degree `|nu|=sum_n nu_n` is at most the total `Y`-degree `D` of `P`.

For fixed `P`, there is a constant `C_P` such that

`#A_N <= (N+2)^(C_P)` and `|c_(N,nu)| <= (N+2)^(C_P)`                        `(3)`

for all `N`. Indeed, each differential monomial of degree at most `D` contributes ordered compositions of an integer `N+O_P(1)` into at most `D` parts; derivative factors are falling factorials of fixed total degree at most `mD`. Grouping can only add polynomially many such integer weights.

After substituting `X_n=a_n`, equation (1) gives

`sum_(nu in A_N) c_(N,nu) a^nu=0`.                                          `(4)`

Define the Archimedean valuation of an atom by

`V_N(nu)=sum_n nu_n b_n=-log|a^nu|`.                                        `(5)`

Suppose `(2)` is nonzero and that `nu_0` is its unique valuation minimizer. Let `V_1=V_N(nu_0)` and let `V_2` be the second-smallest valuation. From (4), the triangle inequality, `|c_(N,nu_0)|>=1`, and (3),

`exp(-V_1)`

` <= sum_(nu!=nu_0)|c_(N,nu)|exp(-V_N(nu))`

` <= (N+2)^(2C_P) exp(-V_2)`.

Therefore

`V_2-V_1 <= 2C_P log(N+2)`.                                                  `(6)`

If the minimum is attained at least twice, its gap is zero. If `(2)` has only one atom, (4) is impossible because every `a_n` is nonzero. We have proved:

> **Archimedean tropical bend law.** Every nonvacuous coefficient identity of an integer-normalized ADE has two distinct grouped convolution atoms whose logarithmic magnitudes differ by at most `O_P(log N)`.

This is the exact phase-sensitive replacement for the false inference from Newton trapping to recurrence. Phases can cancel near-equal atoms, but no phase choice can cancel one atom that beats the entire remaining recurrence by a superlogarithmic valuation gap.

### Formalization of the bend inequality

The load-bearing archimedean inequality — an integer-weighted zero-sum `sum c_nu a^nu = 0` cannot
have one atom strictly dominating the modulus-sum of the others — is formalized axiom-clean in
`GaloisForLFunctions.ArchimedeanBendLaw`:

```text
norm_term_le_of_sum_eq_zero :
  (sum i in s, (c i) * x i = 0) -> ‖(c i0) * x i0‖ <= sum i in s.erase i0, ‖(c i) * x i‖
sum_ne_zero_of_dominant :
  c i0 != 0 -> (sum i in s.erase i0, ‖(c i) * x i‖ < ‖x i0‖) -> sum i in s, (c i) * x i != 0
```

for integer weights `c : ι -> Z` and complex atoms `x : ι -> C` (using `‖(c i0 : C)‖ >= 1` for the
nonzero integer weight).  This is the exact contradiction driving the theorem: when the log-magnitudes
`b_n` are superlacunary, the valuation minimizer strictly dominates, so `sum_ne_zero_of_dominant`
refutes the coefficient identity `(4)`, forcing HT.  The same inequality is the shared engine of the
sibling Taylor-magnitude cards (stretched-exponential, rough-subleading, polynomial, rapid-convex);
the analytic content of each card enters only to verify its strict-dominance hypothesis. The complete
chain for this card, including Mahler normalization, generic-coefficient regrouping, valuation-gap
dominance, the eventual finite-prefix reduction, and the explicit arbitrary-phase family, is now
formalized axiom-clean in the modules listed under **Lean status**.

## Main theorem `[PROVED HERE] [NOVELTY UNVERIFIED]`

Assume that, eventually,

`b_n>0` and `b_(n+1)/b_n -> infinity`.                                       `(LSL)`

Then `f` is HT over `C(z)`.

The conclusion is uniform in the coefficient phases: every series with the same tail moduli `|a_n|=exp(-b_n)` is HT.

### Proof

Condition `(LSL)` implies `b_n/n->infinity`, so the series is entire. Suppose for contradiction that `f` is DA, and choose the integer differential polynomial `P` above.

Let `D>=1` be the largest total `Y`-degree in `P`. A differential monomial

`z^p product_(j=0)^m (F^(j))^(alpha_j)`, `sum_j alpha_j=d`,

contributes coefficient atoms of degree `d` whose source indices `k_1,...,k_d` satisfy

`k_1+...+k_d=N+c`,                                                          `(7)`

where `c=sum_j j alpha_j-p` belongs to a finite set depending only on `P`. Its integer weight is a product of falling factorials, summed over finitely many assignments.

### 1. A bounded balanced top-degree atom always survives

Fix the degree-`D` part of `P` and group its differential monomials by the shift `c` in (7). Polarizing each nonzero group gives a symmetric polynomial

`W_c(k_1,...,k_D)`

with rational-integer coefficients. Here is the precise relation with the grouped atoms in (2). For one differential monomial, list the derivative orders of its `D` factors as `j_1,...,j_D`, with repetitions, and symmetrize the falling-factorial weight

`sum_(sigma in S_D) product_(ell=1)^D (k_(sigma(ell)))_(j_ell)`,

where `(x)_j=x(x-1)...(x-j+1)`. Sum these symmetric polynomials, with the integer coefficients of `P`, over all degree-`D` monomials having shift `c`; this is `W_c`. If the tuple `(k_1,...,k_D)` has multiplicities `nu_s`, then the coefficient of the commutative monomial `prod_s X_s^(nu_s)` contributed by the shift-`c` group is exactly

`W_c(k_1,...,k_D) / product_s nu_s!`.                                      `(8)`

Indeed, the numerator sums over all labelled assignments of the multiset of source indices, while each assignment occurs `prod_s nu_s!` times. In particular, a nonzero value of `W_c` gives a genuinely nonzero grouped atom even when some source indices coincide.

At least one `W_c` is nonzero. Otherwise every degree-`D` coefficient of the generic substitution would vanish. The substitution map

`Q[z,Y_0,...,Y_m] -> Q[X_0,X_1,...][[z]]`, `Y_j |-> F^(j)`,

is injective: if a differential polynomial vanished after generic substitution, specialize `F` to arbitrary polynomials and evaluate at an arbitrary point; polynomial Hermite interpolation realizes an arbitrary finite jet there, so the original polynomial vanishes identically. Hence all `W_c=0` would force the complete degree-`D` part of `P` to be zero, contradicting the definition of `D`.

Fix such a `c`. For each residue `r modulo D`, there are fixed integer offsets

`delta_(r,1),...,delta_(r,D)`, `sum_i delta_(r,i)=r`,

such that

`q |-> W_c(q+delta_(r,1),...,q+delta_(r,D))`                                 `(9)`

is not the zero polynomial. To justify this choice, suppose instead that every integer-offset diagonal with offset sum `r` were annihilated identically. Every nonnegative integer tuple with coordinate sum congruent to `r modulo D` lies on one such diagonal, so `W_c` would vanish on that lattice coset. That coset is Zariski dense in `C^D`: after fixing the first `D-1` nonnegative coordinates arbitrarily, the last coordinate runs through an infinite arithmetic progression, and induction on the number of variables kills every coefficient. This would force `W_c=0`.

For `q` sufficiently large, (9) is nonzero except at finitely many roots. Taking

`q=floor((N+c)/D)` and `r=(N+c)-Dq`,

we obtain, for every sufficiently large `N`, a nonzero grouped atom in (2) of degree `D` all of whose indices lie in

`[N/D-B, N/D+B]`                                                            `(10)`

for one constant `B=B_P`.

### 2. Every valuation minimizer is balanced and has degree `D`

Condition `(LSL)` implies that for every fixed `A>0`,

`b_k > A sum_(j<k)b_j`                                                       `(11)`

for all sufficiently large `k`. Indeed, eventually the successive ratios exceed `2A+2`, so the preceding tail is bounded by a geometric multiple of `b_(k-1)`, while `b_k/b_(k-1)->infinity`; the finite initial sum is negligible.

The witness (10) has valuation at most `D b_(floor(N/D)+B)`. If `D=1`, every lower-degree term has degree zero and contributes to only finitely many coefficient indices, so there are no lower-degree atoms for large `N`. Suppose `D>=2`. An atom of degree `d<D` satisfying (7) has a largest index at least

`(N-O_P(1))/d >= N/(D-1)-O_P(1)`.

By `(LSL)`, its one largest `b`-term eventually exceeds `D b_(N/D+B)` by an arbitrarily large factor. Hence no lower-degree atom minimizes `V_N`.

For a degree-`D` atom, choose a fixed `B'>B+O_P(1)`. If its largest index exceeds `floor(N/D)+B'`, its valuation is at least `b_(floor(N/D)+B'+1)`, whereas the witness has valuation at most `D b_(floor(N/D)+B)`; by `(LSL)` the former is eventually larger by a factor tending to infinity. Thus every minimizer has largest index at most `floor(N/D)+B'`. Equation (7) then forces every one of its `D` indices to lie in

`[N/D-B'',N/D+B'']`                                                         `(12)`

for a fixed `B''=B''_P`.

### 3. Distinct balanced atoms have a superlogarithmic gap

Consider two distinct grouped atoms satisfying (12). Let `k` be the largest index at which their multiplicity vectors differ. The coefficient of `b_k` in the valuation difference is a nonzero integer, while the total absolute multiplicity below `k` is at most `2D`. By (11),

`|V_N(nu)-V_N(mu)|`

` >= b_k-2D sum_(j<k)b_j >= b_k/2`                                          `(13)`

for all sufficiently large `N`.

Here `k=N/D+O_P(1)`, so `(LSL)` gives

`b_k/log N -> infinity`.                                                     `(14)`

Thus the finitely many balanced candidate valuations are strictly ordered, the minimum is unique, and every other balanced valuation is separated from it by `omega(log N)`. The comparison in Step 2 is quantitative as well: a lower-degree atom has an index at least `N/(D-1)-O_P(1)`, and an unbalanced degree-`D` atom has an index at least `floor(N/D)+B'+1`; after subtracting the balanced minimum, each therefore has gap `omega(log N)`. Hence the global second-smallest valuation has superlogarithmic gap from the unique minimum.

This contradicts the Archimedean tropical bend law (6) for every sufficiently large coefficient identity (2). These identities are nonzero for every sufficiently large `N`, not merely along a subsequence: Step 1 explicitly supplies a nonzero degree-`D` grouped atom for each such `N`.

Therefore no ADE for `f` exists. Hence `f` is HT over `C(z)`. `square`

## Explicit finite-basis family `[PROVED COROLLARY]`

For every phase sequence `(theta_n)` in `R^N`, the entire function

`F_theta(z)=sum_(n>=0) exp(-2^(2^n)) exp(i theta_n) z^n`                      `(15)`

is HT over `C(z)`.

Indeed, `b_n=2^(2^n)` and `b_(n+1)/b_n=2^(2^n)->infinity`. For `theta_n=0`, every coefficient belongs to the one-generator field

`Q(exp(-1))`,

because `exp(-2^(2^n))=(exp(-1))^(2^(2^n))`. Thus (15) is not detected by Ostrowski's no-finite-coefficient-basis theorem. Its support is all of `N`, so it is not detected by a support-gap theorem either.

## Boundaries and attacks

1. **The ratio condition is sufficient, not claimed sharp.** The universal super-Gaussian conjecture only assumes `b_n/n^2->infinity`, far weaker than `(LSL)`.
2. **Critical DA examples lie outside the theorem.** For exponential, theta, and Valiron-type coefficients, successive ratios `b_(n+1)/b_n` tend to `1`, not infinity.
3. **Phases are genuinely arbitrary.** No algebraicity, independence, positivity, or Diophantine lower bound is used.
4. **Full support matters to this proof.** If coefficients vanish, some grouped atoms disappear. Support-gap theory is a separate complementary mechanism.
5. **Mahler normalization is essential.** Without integral coefficients, a grouped polynomial weight could be Liouville-small. Integer weights are either zero and removed, or have modulus at least one.
6. **The new mechanism is convolution isolation.** It is not coefficient-field entropy: example (15) has a finite coefficient basis. It is not a Newton-plateau statement: the proof works directly in exact coefficient identities.

## Consequence for the super-Gaussian program

The arbitrary-order coefficient-floor problem now has a proved phase-uniform stratum:

> Every eventually full-support series satisfying `(LSL)` is HT, regardless of coefficient arithmetic and phases.

The remaining open range is where `b_n/n^2->infinity` but adjacent logarithmic sizes remain comparable often enough to permit the `O(log N)` convolution bends required by an ADE. The exact next target is therefore not generic cluster density. It is:

> `[OPEN CORE]` Prove that an integer differential recurrence cannot sustain logarithmic-width convolution bends at every large coefficient index when `b_n/n^2->infinity`, unless the series has finite support.

This formulation incorporates phases correctly: a bend supplies the only scale on which phase cancellation is possible; the unresolved task is to show that a finite ADE cannot supply such bends indefinitely at quadratic type zero.

## Exact RH-route scope

For heat or coefficient-Newton implementations, `(LSL)` makes HT status depend only on extreme coefficient magnitudes and makes it constant across the entire phase fiber. Therefore HT status in this stratum cannot itself carry phase-sensitive divisor localization. This excludes only implementations whose RH selector is asserted to factor through that forced HT bit or through the same dominant-convolution magnitude data.

It does not exclude the complete de Bruijn--Newman, Hilbert--Polya, Connes, de Branges, Nyman--Beurling, Weil, or Li criteria, all of which may retain exact positivity, spectral, norm, Euler, or divisor information absent from this theorem.

## Parent and novelty status

- **Mahler parent:** K. Mahler, *A remark on algebraic differential equations*, Rend. Accad. Naz. Lincei 50 (1971), 402--412, proves the rational-integral ADE normalization used above.
- **Ostrowski boundary:** the finite-coefficient-basis theorem does not apply to (15).
- **Lipshitz--Rubel boundary:** support-gap theorems do not apply because (15) has full support.
- **Coefficient-arithmetic boundary:** Hurwitz--Kakeya--Mahler--Sibuya--Sperber coefficient theorems, including Laohakosol--Kongsakorn--Ubolsri's *Coefficients of differentially algebraic series* and Krattenthaler--Rivoal's 2025 refinement, assume rational or algebraic Taylor coefficients and prove denominator or non-Archimedean bounds. They do not give a phase-uniform Archimedean magnitude obstruction for arbitrary complex coefficients.
- **Current verdict:** proof and significance gates pass. Parent-theory, exact-literature, and rediscovery audits remain open. The theorem must remain `[NOVELTY UNVERIFIED]` until those audits are completed.

## Lean status

Fully formalized axiom-clean in Lean 4.

- `HTGeometry/FormalMahlerIntegerNormalization.lean` proves
  `formal_mahler_integer_normalization`, deriving a nonzero integer-coefficient formal jet relation
  from an arbitrary complex-coefficient relation by finite coefficient adjunction, differential-
  algebraic descent, and denominator clearing.
- `HTGeometry/MagnitudeIntegerDominance.lean` contains the grouped integer-weight dominance theorem
  and `hypertranscendental_of_mahler_logSuperlacunary`.
- `HTGeometry/LogSuperlacunaryMagnitudeHypertranscendence.lean` proves
  `hypertranscendental_of_eventually_logSuperlacunary`. Polynomial translation closes the arbitrary
  finite Taylor-prefix gap, so the theorem has exactly the eventual hypotheses stated here.
- `HTGeometry/LogSuperlacunaryDoubleExponentialFamily.lean` constructs
  `doubleExponentialPhaseFunction`, proves that its defining power series has infinite radius,
  identifies all Taylor coefficients, proves full support, and proves
  `hypertranscendental_doubleExponentialPhaseFunction` for every real phase sequence. It also proves
  that every zero-phase Taylor coefficient lies in `expMinusOneCoefficientField = ℚ(exp(-1))`.

The load-bearing declarations depend only on Lean's standard logical axioms `propext`,
`Classical.choice`, and `Quot.sound`; the formal lint gate reports no `sorry`, `admit`, `axiom`,
`opaque`, or `unsafe` declaration.

## Gates

- [x] Exact theorem and phase-uniform strengthening stated.
- [x] Complete unconditional paper proof.
- [x] Explicit full-support finite-basis family proved HT.
- [x] Significance gate: supplies a new coefficient-magnitude HT mechanism and a proved arbitrary-complex stratum of the super-Gaussian problem.
- [ ] Parent-theory and literature novelty gates.
- [x] Whole theorem and explicit corollary formalized unconditionally in Lean.

## Log

- 2026-07-11 — Proved the Archimedean tropical bend law from Mahler normalization and derived phase-uniform HT from log-superlacunary full-support magnitudes.
