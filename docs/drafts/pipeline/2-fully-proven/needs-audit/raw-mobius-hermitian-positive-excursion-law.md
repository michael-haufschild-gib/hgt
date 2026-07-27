# Raw Möbius Hermitian positive-excursion law

- **ID:** `raw-mobius-hermitian-positive-excursion-law`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [UNCONDITIONAL] [NOT RH]`
- **Dominance status:** strict even-index strengthening proved in
  `even-index-hermitian-additive-pole-law.md`; do not reuse unrestricted recurrence as newest claim.
- **Source:** ordinary generating function of reciprocal Dirichlet coefficients / Mellin pole
  obstruction
- **Statement:** Raw Hermitian additive convolutions of twisted Möbius coefficients have
  infinitely many positive values.  At every order at least four, their positive excursions have
  an unconditional power-law lower order.  In particular, the binary additive Möbius
  self-convolution is positive infinitely often.

## Statement

Let `chi` be a fixed primitive Dirichlet character and put

```text
a_chi(n)=mu(n)chi(n),
A_chi(z)=sum_(n>=1) a_chi(n)z^n.
```

For `k>=1`, define the raw Hermitian `2k`-fold additive convolution

```text
R_(chi,k)(N)
 = sum_(n_1+...+n_k+m_1+...+m_k=N)
     product_j a_chi(n_j) product_j conjugate(a_chi(m_j)).       (R1)
```

All coordinates in `(R1)` are positive integers.  The coefficient is real.  Let

```text
Psi_(chi,k)=limsup_(N->infinity)
  log(1+max(R_(chi,k)(N),0))/log(N+1),                           (R2)
```

and let `Theta_chi` be the supremum of the real parts of the nontrivial zeros of
`L(s,chi)`.  Then

```text
2k Theta_chi-1 <= Psi_(chi,k) <= 2k-1.                           (R3)
```

Moreover,

```text
R_(chi,k)(N)>0 for infinitely many N, for every k>=1.            (R4)
```

Functional-equation symmetry gives `Theta_chi>=1/2`.  Consequently, for every `k>=2`
and every `epsilon>0`,

```text
R_(chi,k)(N)=Omega_+(N^(k-1-epsilon)).                           (R5)
```

For a real primitive character, including the conductor-one zeta case, `(R4)` is an
`Omega_+(1)` statement because every coefficient is an integer.  In particular,

```text
sum_(a+b=N) mu(a)mu(b) >= 1                                    (R6)
```

for infinitely many positive integers `N`.

This is not an upper bound and does not prove binary Chowla cancellation or RH.

## Exact radial law

For real `0<r<1`, absolute convergence and Cauchy multiplication give

```text
sum_(N>=1) R_(chi,k)(N) r^N = |A_chi(r)|^(2k) >= 0.              (R7)
```

Hence

```text
|A_chi(r)|^(2k)
 <= sum_(N>=1) max(R_(chi,k)(N),0) r^N.                         (R8)
```

The exact Mellin identity in `Re(s)>1` is

```text
integral_0^infinity A_chi(exp(-x)) x^(s-1) dx
 = Gamma(s)/L(s,chi).                                          (R9)
```

Unlike a norm estimate, `(R8)` discards all negative raw correlations while retaining enough
radial information to detect every pole of `1/L`.

## Proof of the exponent lower bound

Suppose first that `2k Theta_chi-1>0` and that the lower inequality in `(R3)` fails.  Choose

```text
Psi_(chi,k) < lambda < 2k Theta_chi-1.
```

The limsup definition gives

```text
max(R_(chi,k)(N),0) <= C_lambda (N+1)^lambda.                   (R10)
```

Set `r=exp(-x)`, `0<x<=1`.  The standard exponential-moment bound and `(R8)` imply

```text
|A_chi(exp(-x))|^(2k) = O(x^(-lambda-1)),
|A_chi(exp(-x))| = O(x^(-b)),
b=(lambda+1)/(2k) < Theta_chi.                                 (R11)
```

The function

```text
H(s)=1/Gamma(s) integral_0^infinity
       A_chi(exp(-x)) x^(s-1) dx                               (R12)
```

is therefore holomorphic in `Re(s)>b`.  Equation `(R9)` and the identity theorem give
`H(s)L(s,chi)=1` there.  By the definition of `Theta_chi`, there is a nontrivial zero `rho`
with `Re(rho)>b`, contradicting evaluation at `rho`.  Thus the lower bound holds when its
right side is positive.  When `2k Theta_chi-1<=0`, it follows from the automatic inequality
`Psi_(chi,k)>=0`.

The upper bound in `(R3)` is elementary: `(R1)` has at most `(N+1)^(2k-1)` summands and every
summand has modulus at most one.

For `k>=2`, symmetry `Theta_chi>=1/2` and `(R3)` give
`Psi_(chi,k)>=k-1>0`; the definition of limsup gives `(R5)`.

## Proof of positive recurrence at the binary endpoint

The exponent statement alone is insufficient when `k=1` and `Theta_chi=1/2`, because the
right side of `(R3)` is zero.  A separate endpoint argument gives `(R4)` at every order.

Assume only finitely many `R_(chi,k)(N)` are positive.  Then the positive-part series in `(R8)`
is a polynomial and is uniformly bounded for `0<r<1`.  Therefore `A_chi(r)` is bounded as
`r` tends to one.  Since `A_chi(exp(-x))` decays exponentially as `x` tends to infinity,
`(R12)` is now holomorphic throughout `Re(s)>0`.  But `(R9)` would continue `1/L(s,chi)`
holomorphically across every nontrivial zero.  Primitive Dirichlet `L`-functions have
nontrivial zeros in the critical strip, a contradiction.  Thus positive coefficients recur
infinitely often.

## Relation to the exact Mertens-convolution law

Let `M_chi(N)=sum_(n<=N)a_chi(n)` and let `C_(chi,k)` be its mixed `2k`-fold convolution.
Ordinary generating functions give the exact integration law

```text
sum_N C_(chi,k)(N)z^N
 = (1-z)^(-2k) sum_N R_(chi,k)(N)z^N.                           (R13)
```

Equivalently,

```text
C_(chi,k)(N)
 = sum_(j<=N) binom(N-j+2k-1,2k-1) R_(chi,k)(j).               (R14)
```

The companion theorem

```text
limsup log(1+[C_(chi,k)(N)]_+)/log(N+1)
 = 2k(1+Theta_chi)-1                                          (R15)
```

is exact because the classical twisted Littlewood theorem also supplies the matching upper
bound for `M_chi`.  The raw theorem `(R3)` supplies only the lower spectral edge; proving a
matching critical upper edge for raw binary convolution is substantially stronger and remains
open.

## Hostile audit

1. **Not RH.**  `(R3)` detects a lower edge forced by existing zeros; it does not prove
   `Theta_chi=1/2`.
2. **Not binary Chowla.**  Positive recurrence gives neither `o(N)` nor cancellation in
   `sum_(a+b=N)mu(a)mu(b)`.
3. **Not an estimate in disguise.**  Core statements `(R4)` and `(R7)` are qualitative/exact;
   `(R3)` is an order law.  The higher-order omega corollary is a consequence, not the source
   theorem.
4. **No simplicity, RH, LI, or zero-density assumption.**  A single nontrivial zero suffices
   for `(R4)`; the full zero frontier gives `(R3)`.
5. **Endpoint handled separately.**  `Psi>=0` alone would not prove infinitely many positive
   binary coefficients.  The bounded-positive-tail argument is essential.
6. **Complex characters handled Hermitianly.**  Plain even powers would not be nonnegative for
   complex coefficients.  Conjugate pairing gives the real coefficients and `(R7)`.

## Literature boundary

Targeted corpus and external searches through 2026-07-22 found no statement of `(R3)`--`(R6)`.
The closest sources are:

- M. Cantarini, A. Gambini and A. Zaccagnini, *On the discrete convolution of the Liouville and
  Möbius functions*, arXiv:2603.10241 (2026), derive weighted explicit formulas for raw
  Liouville and Möbius convolutions under RH and simplicity assumptions.  Their paper does not
  state unconditional positive recurrence or the one-sided exponent lower law.
- W. D. Banks and I. E. Shparlinski, *Multiple sums with the Möbius function*, Q. J. Math. 77
  (2026), 109--127, explicitly note that binary versions of their nontrivial cancellation bounds
  remain out of reach.  `(R6)` is a weaker sign-recurrence theorem, not such a cancellation
  bound.
- J. Kaczorowski and A. Perelli, *General Omega-theorems for coefficients of L-functions*,
  Proc. Amer. Math. Soc. 143 (2015), 5139--5145, concern Dirichlet coefficients of polynomial
  combinations of Selberg-class `L`-functions.  The coefficients in `(R1)` are ordinary-additive
  Cauchy convolutions of reciprocal coefficients, so their theorem is not `(R3)`.
- Classical Littlewood and modern Hardy--Littlewood--Riesz criteria control linear reciprocal
  sums or smoothed transforms and supply neighboring Mellin methodology, not positive parts of
  raw additive convolutions.

Negative search is not proof of priority.  Specialist review and MathSciNet/Zentralblatt searches
remain required before any priority claim.

## Significance verdict

The theorem gives a first candidate unconditional sign law on the raw binary additive Möbius
convolution and a universal higher-order positive-excursion law for every primitive Dirichlet
character.  It is directly adjacent to an active binary frontier and uses neither RH nor the
conditional explicit formulas currently used for this object.

It does **not** solve a recognized major open problem such as binary Chowla, GRH, or RH.  Current
classification is `CANDIDATE NEW SCIENTIFIC KNOWLEDGE`, not `MAJOR OPEN PROBLEM SOLVED`.

## Formal certificate

The existing Lean module

```text
formal/GaloisForLFunctions/RHTower/DirichletLMixedAdditiveZeroAbscissaLaw.lean
```

already formalizes the exact generic algebraic core needed here:

- `mixedAdditiveConvolutionPower` is `(R1)` for an arbitrary complex sequence;
- `star_mixedAdditiveConvolutionPower` and
  `mixedAdditiveConvolutionPower_im_eq_zero` prove reality;
- `pow_mul_star_pow_eq_tsum_mixedAdditiveConvolutionPower_mul_pow` proves `(R7)`;
- `norm_sq_pow_le_tsum_of_mixedAdditiveConvolutionPower_upper` formalizes `(R8)`.

The Dirichlet character, nontrivial-zero, Mellin-continuation, and limsup layers remain
paper-level.  No duplicate Lean wrapper is warranted.

## Gates

- [x] corpus search
- [x] exact theorem and endpoint proof
- [x] complex-character audit
- [x] initial 2025--2026 collision search
- [x] dependency-closed paper proof
- [x] generic Hermitian Abel core already formalized
- [ ] specialist priority review
- [ ] MathSciNet/Zentralblatt search
- [ ] full analytic Lean formalization
- [ ] binary Chowla cancellation
- [ ] RH

## Log

- 2026-07-22 -- derived raw Hermitian radial law from existing mixed Abel core; proved the
  zero-frontier lower exponent, unconditional higher-order positive excursions, and separate
  binary endpoint positive recurrence; audited closest 2015, 2025, and 2026 literature.
- 2026-07-22 -- superseded as publication headline by `PARITY-RAW-001`, which proves the same
  lower edge and recurrence on even output indices and contains a dyadic Gram refinement.

## Log

- 2026-07-24 — Formalization audit + capstone. The convolution-power norm bounds underlying the `(R3)`
  upper bound `Ψ_{χ,k} ≤ 2k-1` are already in the corpus (`RHTower/MobiusMertensEvenConvolutionOrderLaw.lean`:
  `additiveConvolutionPower_one`, `norm_additiveConvolutionPower_succ_le`; and the one-sided order
  comparisons `norm_pow_even_mobiusDiscreteLaplaceTransform_le_of_evenConvolutionUpper` /
  `...SubpowerUpperBound`).  Formalized the reusable analytic **capstone** for the `Ψ ≤ d` order shape
  (`HTGeometry/LogOrderLimsupBound.lean`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`):
  * `limsup_log_one_add_div_log_le` — for `0 ≤ f N ≤ C·(N+1)^d`,
    `limsup_N log(1 + f N)/log(N+1) ≤ d`.
  With `f N = max(R_{χ,k}(N), 0)` bounded by the binomial term count `~ N^{2k-1}` (via the existing norm
  bounds), this yields the `(R3)` upper bound `Ψ_{χ,k} ≤ 2k-1`.  The lower bound `2kΘ_χ - 1 ≤ Ψ` and the
  positivity `(R4)` remain the analytic/`L`-zero direction (the abstract `(9)` route is formalized in
  `even-index-hermitian-additive-pole-law` via `frequently_re_pos_of_dirichletPole`; the concrete claim
  needs a pole of `1/L(s,χ)` in `Re s > 0`, i.e. an `L`-function zero).
- 2026-07-24 — **`(R3)` upper bound `Ψ_{χ,k} ≤ 2k-1` formalized** abstractly
  (`RHTower/EvenIndexHermitianOrderUpperBound.lean`, unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`), for any unit-bounded coefficient sequence
  (`∀ n, ‖a n‖ ≤ 1`):
  * `norm_additiveConvolutionPower_succ_le_pow` — `‖C_{j+1}(N)‖ ≤ (N+1)^j` (the corpus convolution
    estimate at `A = 1`, `α = 0`).
  * `norm_mixedAdditiveConvolutionPower_le_pow` — `‖R_{j+1}(N)‖ ≤ (N+1)^{2j+1}` (antidiagonal sum of
    the leg bounds; the composition count).
  * `limsup_log_mixedAdditiveConvolutionPower_re_le` —
    `limsup_N log(1 + max(Re R_{j+1}(N), 0))/log(N+1) ≤ 2j+1`, i.e. `Ψ_{χ,j+1} ≤ 2(j+1)-1`, via the
    log-order limsup capstone `HTGeometry.limsup_log_one_add_div_log_le`.
  The lower bound `2kΘ_χ - 1 ≤ Ψ` and the positivity `(R4)` remain the analytic `L`-zero direction
  (the abstract `(9)`/`(R4)` route is formalized in `even-index-hermitian-additive-pole-law` via
  `frequently_re_pos_of_dirichletPole`; the concrete claim needs a pole of `1/L(s,χ)` in `Re s > 0`).

## Lean progress

- 2026-07-26 — **The Mertens integration law `(R13)`/`(R14)` formalized**, new module
  `RHTower/HermitianMertensIntegrationLaw.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).

  Audit first.  Of the pieces this card needs beyond `## Formal certificate`, the order upper bound
  of `(R3)` turned out to be **already** in the corpus
  (`EvenIndexHermitianOrderUpperBound.norm_mixedAdditiveConvolutionPower_le_pow` and
  `limsup_log_mixedAdditiveConvolutionPower_re_le`), so no work was needed there.  The integration
  law was absent everywhere.

  * `partialSumSeq`, `mk_partialSumSeq` — passing to partial sums multiplies the generating series
    by `1 + X + X^2 + ...`.
  * `conj_additiveConvolutionPower`, `conj_partialSumSeq` — conjugation commutes with both
    operations.
  * `mixedAdditiveConvolutionPower_eq_coeff` — the Hermitian mixed power is a coefficient of
    `(mk a)^k * (mk (conj a))^k`.
  * `mixedAdditiveConvolutionPower_partialSumSeq` — **the integration law**: the mixed
    `2(k+1)`-convolution of the partial sums is the mixed convolution of the coefficients against
    the binomial kernel of `(1-X)^(-(2k+2))`,
    `C_k(N) = sum_(i+j=N) R_k(i) * binom(2k+1+j, 2k+1)`, via mathlib's
    `PowerSeries.mk_one_pow_eq_mk_choose_add`.  `..._range` gives the card's explicit
    `sum_(j<=N)` form `(R14)`.
  * `partialSumSeq_im_eq_zero`, `additiveConvolutionPower_partialSumSeq_of_real` — on a real
    coefficient sequence the same binomial kernel relates the plain even convolution powers, routed
    through the corpus bridge
    `mixedAdditiveConvolutionPower_eq_additiveConvolutionPower_two_mul_of_real`.  This connects the
    new law to the even-order framework of `MobiusMertensEvenConvolutionOrderLaw`.

  The remaining content of the gate `full analytic Lean formalization` is the analytic layer the
  `## Formal certificate` section already identifies as paper-level: the Dirichlet character, the
  existence of nontrivial `L`-zeros, the Mellin identity `(R9)` and its holomorphic continuation,
  and the limsup lower bound.  Gate stays unchecked.
- 2026-07-26 — **The functional-equation input `Theta >= 1/2` formalized**, new module
  `RHTower/XiZeroHalfPlaneWitness.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).  The card uses "functional-equation symmetry gives
  `Theta_chi >= 1/2`" to turn `(R3)` into the effective bound `(R5)`; in the conductor-one case this
  is now a Lean theorem rather than a paper remark.
  * `xiZeroSet_one_sub` — reflection symmetry of the Xi zero set (`xi_one_sub`), previously only
    inline inside one Hedenmalm proof, now a named reusable lemma.
  * `exists_xiZeroSet_half_le_re` — **`Theta >= 1/2`**: some Xi zero has real part at least `1/2`.
    Only two facts are used: the zero set is nonempty (`xiZeroSet_infinite`) and it is
    reflection-symmetric.  Nothing about where the zeros lie.
  * `exists_xiZeroSet_lt_re` — the form the card's contradiction step consumes: every abscissa
    `b < 1/2` is exceeded by some zero, so no half-plane `Re s > b` with `b < 1/2` can be a domain of
    holomorphy for `1/zeta`.
  * `exists_xiZeroSet_re_le_half` — the reflected witness, bracketing the zero set about the
    critical line.

  Corpus audit for this step: the corpus already had `xiZeroSet`, `xiZeroSet_infinite`, and
  `xi_one_sub`; and, for the neighbouring conditional direction,
  `MobiusMertensEvenConvolutionOrderLaw.mobiusMertensEvenConvolutionSubpowerUpperBound_iff_riemannHypothesis_of_mertens`
  and `LandauSummabilityTransfer.landau_summability_transfer`.  What remains of the gate is the
  Mellin layer proper: the identity `(R9)`, holomorphy of `H` on `Re s > b` from the radial bound
  `(R11)`, and `H . L = 1` by the identity theorem.  Gate stays unchecked.
- 2026-07-26 — **`(R11)` formalized for an arbitrary coefficient sequence**, new module
  `RHTower/MixedConvolutionSubpowerAbelBound.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).
  * `mixedSubpowerAbelConstant α = 1 + e · 2^α · Γ(α+1)`, with nonnegativity.
  * `norm_sq_pow_le_of_mixedAdditiveConvolutionPower_subpower` — **the radial bound**: if
    `Re R_k(N) <= C (N+1)^α` then at radius `e^{-x}` with `0 < x <= 1`,
    `‖(sum a(N) e^{-Nx})^k‖^2 <= C · A(α) · x^{-(α+1)}`.

  This is the general-sequence form of the estimate the corpus previously carried only for the
  Möbius/Mertens coefficients
  (`norm_pow_even_mobiusDiscreteLaplaceTransform_le_of_evenConvolutionSubpowerUpperBound`).  It is
  assembled from two existing corpus assets rather than proved from scratch: the Hermitian
  positivity bound `(R8)`
  (`norm_sq_pow_le_tsum_of_mixedAdditiveConvolutionPower_upper`) and the moment estimate
  `summable_natSucc_rpow_exp_neg_and_tsum_le` for `sum (N+1)^α e^{-Nx}`.  The `1` in the moment
  estimate is absorbed using `1 <= (1/x)^(α+1)`, valid because `x <= 1`.

  With this the card's chain `(R10) -> (R11)` is Lean-complete for arbitrary `a`, and combined with
  the previous entry (`Theta >= 1/2`) the only remaining analytic step of the lower bound is the
  Mellin layer: the identity `(R9)`, holomorphy of `H` on `Re s > b`, and `H · L = 1` by the
  identity theorem.  Gate stays unchecked.
- 2026-07-27 — **`(R11)` completed: the bound on the series itself.**  Appended to
  `RHTower/MixedConvolutionSubpowerAbelBound.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).
  * `norm_tsum_le_of_mixedAdditiveConvolutionPower_subpower` — taking the `2k`-th root of the
    previous estimate,
    `‖A(e^{-x})‖ <= (C · A(α))^(1/(2k)) · x^(-(α+1)/(2k))`,
    which is `(R11)` with the card's exponent `b = (lambda+1)/(2k)`.

  **Audit note on the Mellin layer.**  Tracing how the corpus proves `(R9)` for the Möbius case
  (`mellin_mobiusDiscreteLaplaceTransform_eq_gamma_mul_LSeries`) shows it is a direct application of
  **mathlib's `hasSum_mellin`**, which is already fully general: for any coefficients `a` and
  frequencies `p` with absolute convergence,
  `mellin (fun t => sum a n e^{-p n t}) s = Gamma s * sum a n / (p n)^s`.  mathlib also supplies
  `mellin_differentiableAt_of_isBigO_rpow_exp` for holomorphy of a Mellin transform from growth
  bounds at `0` and `infinity`.  So `(R9)` and the holomorphy criterion are *available* rather than
  missing; what they need as input is exactly the `O(x^{-b})` bound just proved, plus exponential
  decay at infinity.

  Remaining for the gate, and now precisely delimited: assemble those three mathlib/corpus pieces
  into `H` holomorphic on `Re s > b`, then `H · L = 1` by the identity theorem and the contradiction
  against `exists_xiZeroSet_lt_re`.  The character-twisted `L`-series and its zeros (as opposed to
  the conductor-one case now covered) remain outside what the corpus carries.  Gate stays unchecked.
- 2026-07-27 — **The packaged decay hypothesis is discharged from a coefficient bound**, new module
  `RHTower/MobiusHalfDecayFromSubpower.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).

  The corpus states the source decay as a *packaged proposition*
  `MobiusDiscreteLaplaceHalfDecay` (`exists C delta, ‖A(x)‖ <= C x^(-1/2)` near `0`) and derives from
  it `analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform`.  Packaging a conclusion as a hypothesis
  is not a formalization of it, so the useful step is to *produce* it:
  * `mobiusCoeff`, `mobiusDiscreteLaplaceTerm_eq_coeff_mul_pow`,
    `mobiusDiscreteLaplaceTransform_eq_tsum` — the corpus source is the radial series of the Möbius
    coefficients at radius `e^{-x}`, matching the general `(R11)` shape.
  * `summable_norm_mobiusCoeff_mul_pow` — absolute convergence by geometric comparison
    (`|mu| <= 1`, `e^{-x} < 1`).
  * `mobiusDiscreteLaplaceHalfDecay_of_subpower` — **the discharge**: if
    `Re R_k(N) <= C (N+1)^alpha` with `alpha + 1 <= k`, then `MobiusDiscreteLaplaceHalfDecay` holds.
    The exponent condition is exactly what makes the radial exponent `(alpha+1)/(2k)` at most `1/2`;
    since `1/x >= 1` on `(0,1)` the smaller exponent gives the weaker bound.

  Consequence: `analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform` and everything downstream of it
  in `MobiusLaplaceBoundaryMultiplicity` now follow from an explicit coefficient hypothesis rather
  than from a packaged analytic assumption.  Combined with
  `mellin_mobiusDiscreteLaplaceTransform_eq_gamma_div_zeta` this is the conductor-one form of the
  card's `(R11) -> (R12)` step.

  Remaining for the gate: the identity-theorem contradiction itself (continuing `1/zeta` past a zero,
  against `exists_xiZeroSet_lt_re`), and the character-twisted case.  Gate stays unchecked.
- 2026-07-27 — **Coefficient criterion assembled**, new module
  `RHTower/MobiusSubpowerRiemannCriterion.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).  Composing the discharge with the corpus criterion
  removes every analytic hypothesis:
  * `riemannHypothesis_and_xiZerosSimple_of_mixedSubpower` — if
    `Re R_k(N) <= C (N+1)^alpha` with `alpha + 1 <= k`, then `RiemannHypothesis` **and**
    `XiZerosSimple`.  The chain is: coefficient bound -> radial bound `(R11)` ->
    `MobiusDiscreteLaplaceHalfDecay` -> corpus criterion.
  * `not_mixedSubpower_of_not_riemannHypothesis` and
    `exists_lt_mixedAdditiveConvolutionPower_re_of_not_riemannHypothesis` — the no-go form: a failure
    of RH forbids every such bound, so some index beats every admissible constant.

  **Exactly what this is and is not.**  The card's `(R3)` lower bound `Psi >= 2k Theta - 1` is
  unconditional and uses the actual value of `Theta`, obtained by contradicting a single zero beyond
  the abscissa `b`.  What is proved here is the neighbouring implication with a *stronger*
  conclusion: the same coefficient bound yields full RH, not merely a contradiction with one zero.
  The two coincide in content only when RH fails.  So this does **not** by itself formalize
  `Psi >= k - 1` unconditionally, and the card's `(R5)` is not yet closed; what is closed is the
  criterion direction and its contrapositive no-go.

  For the unconditional `(R3)` one still needs the weaker, `Theta`-sensitive contradiction:
  holomorphy of the Mellin transform on `Re s > b` with `b = (alpha+1)/(2k)`, the identity
  `H . zeta = 1` there, and a zero with real part exceeding `b` from `exists_xiZeroSet_lt_re`.
  Gate stays unchecked.
- 2026-07-27 — **The decay/analyticity layer generalized to an arbitrary exponent**, new module
  `RHTower/MobiusDecayExponent.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).  The corpus fixes the exponent at `1/2`; the
  `Theta`-sensitive form of `(R3)` needs it at `b = (alpha+1)/(2k)`, which is what a subpower bound
  actually produces.
  * `MobiusDiscreteLaplaceDecay b` — the decay predicate with the exponent carried as a parameter,
    and `MobiusDiscreteLaplaceDecay.isBigO` its asymptotic form.
  * `mobiusDiscreteLaplaceHalfDecay_iff_decay_half` — the corpus predicate is *definitionally* the
    case `b = 1/2` (`Iff.rfl`), so the generalization is conservative: nothing downstream changes.
  * `mobiusDiscreteLaplaceDecay_of_subpower` — a subpower coefficient bound gives decay at exactly
    `(alpha+1)/(2k)`, with no constraint relating `alpha` and `k` (unlike the `1/2` version, which
    needed `alpha + 1 <= k` to weaken the exponent).
  * `analyticOnNhd_mellin_of_mobiusDiscreteLaplaceDecay` — **the Mellin transform is analytic on
    `Re s > b`**, via mathlib's `mellin_differentiableAt_of_isBigO_rpow_exp` together with the
    corpus's local integrability and exponential decay at infinity.

  Route for the remaining step, now fully scouted.  With `G s = mellin A s * zetaResidueUnit s` and
  `H s = Gamma s * (s-1)`, both analytic on the convex (hence connected) open half-plane
  `Re s > b >= 0`, and `G = H` on `Re s > 1` by
  `mellin_mobiusDiscreteLaplaceTransform_eq_gamma_div_zeta`, the identity theorem forces `G = H`
  throughout.  At a zeta zero `rho != 1` with `Re rho > b` the left side vanishes while
  `Gamma rho * (rho - 1) != 0` (`Complex.Gamma_ne_zero`), the contradiction that yields `(R3)`.
  The corpus supplies `zetaResidueUnit = Function.update (fun s => (s-1) * zeta s) 1 1`
  (`ZetaLogDerivResidue`), which is the entire representative needed to avoid the pole at `1`.
  Gate stays unchecked.
- 2026-07-27 — **`(R3)` proved in no-go form: a zeta zero obstructs the subpower bound.**  New module
  `RHTower/MobiusDecayZeroObstruction.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).  This is the Mellin contradiction the card describes,
  and it closes the analytic chain.
  * `analyticOnNhd_Gamma_halfPlane` — `Gamma` is analytic on `Re s > b` whenever `b >= 0`, since the
    poles sit at the nonpositive integers.
  * `not_mobiusDiscreteLaplaceDecay_of_riemannZeta_eq_zero` — **the obstruction**: if `zeta` vanishes
    at some `rho != 1` with `Re rho > b >= 0`, the source cannot decay at exponent `b`.  Proof as
    scouted: `mellin A . zetaResidueUnit` and `Gamma(s)(s-1)` are analytic on the convex — hence
    preconnected — half-plane, agree on `Re s > 1` by
    `mellin_mobiusDiscreteLaplaceTransform_eq_gamma_div_zeta`, so the identity theorem
    (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) propagates the identity; at `rho` the left
    side vanishes and `Gamma rho (rho - 1)` does not (`Complex.Gamma_ne_zero`).
  * `not_mixedSubpower_of_riemannZeta_eq_zero` — **`(R3)`**: a zeta zero beyond the abscissa
    `(alpha+1)/(2k)` forbids `Re R_k(N) <= C (N+1)^alpha`.  The coefficient order cannot drop below
    what the zero permits.

  Note the base point of the identity theorem is `b + 2`, not `2`: the two half-planes
  `Re s > b` and `Re s > 1` must both contain it and `b` is unconstrained above.

  With this the card's analytic chain is complete for the conductor-one case:
  `(R8) -> (R11) -> decay at (alpha+1)/(2k) -> Mellin analyticity -> identity theorem -> zero
  contradiction`.  What remains for the gate is the passage from a Xi zero to a zeta zero (to feed
  `exists_xiZeroSet_lt_re` into the last theorem and obtain the unconditional `Psi >= k - 1`), and
  the character-twisted case.  Gate stays unchecked.
- 2026-07-27 — **`(R5)` proved unconditionally for conductor one.**  New module
  `RHTower/MobiusOrderLowerBound.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).
  * `exists_riemannZeta_eq_zero_lt_re` — every abscissa `b < 1/2` is exceeded by a zeta zero
    different from `1`.  The Xi witness `exists_xiZeroSet_lt_re` is transported by
    `xi_eq_zero_iff` (valid on `0 < Re s`, `s != 1`) using `xiZeroSet_mem_openUnitStrip`.
  * `not_mixedSubpower_of_lt_sub_one` — **the order lower bound**: if `alpha + 1 < k` then no bound
    `Re R_k(N) <= C (N+1)^alpha` holds.  Equivalently the Hermitian mixed `2k`-fold convolution of
    the Möbius coefficients has order at least `k - 1`, which is `(R5)` at `Theta = 1/2`.
  * `exists_lt_mixedAdditiveConvolutionPower_re_of_lt_sub_one` — the same as an exceeded bound.

  Unconditional in the strict sense: nothing is assumed about where the zeros lie, only that one
  exists and that the zero set is reflection-symmetric.

  **Scope, stated exactly.**  What is now complete is the *conductor-one* case of the card:
  `(R1)`, reality, `(R7)`, `(R8)` (pre-existing); the `(R3)` upper bound (pre-existing); `(R11)`,
  `(R13)`/`(R14)`, `Theta >= 1/2`, the Mellin obstruction `(R3)` lower bound, and now `(R5)`.
  Two things are *not* covered.  First, the card states everything for an arbitrary primitive
  Dirichlet character, and the corpus has no `L(s,chi)` zero infrastructure.  Second, `(R4)`/`(R6)`
  — positivity infinitely often, in particular `sum_(a+b=N) mu(a)mu(b) >= 1` — is the `k = 1`
  endpoint, where `alpha + 1 < k` is unsatisfiable for `alpha >= 0`; the card proves it by a
  separate boundedness argument, not by the exponent bound.  Gate stays unchecked.
- 2026-07-27 — **`(R4)` proved: positive excursions recur, at every order.**  New module
  `RHTower/MobiusPositiveExcursion.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).  This is the card's endpoint argument, and unlike
  `(R5)` it applies at `k = 1`.
  * `mobiusDiscreteLaplaceDecay_zero_of_nonpos_outside` — if every coefficient outside a finite set
    is nonpositive, the positive part of the radial series is a finite sum, so
    `‖A(r)^k‖^2 <= sum_(N in S) max(Re R_k(N), 0)` uniformly in `r`; taking the `2k`-th root this is
    **decay at exponent `0`**.
  * `exists_notMem_pos_mixedAdditiveConvolutionPower` — **`(R4)`**: for every order `k` and every
    finite set of indices, some index outside it carries a positive coefficient.  The Mellin
    obstruction at `b = 0` supplies the contradiction, because a zeta zero has real part strictly
    greater than `0`.
  * `infinite_pos_mixedAdditiveConvolutionPower` — the set of such indices is infinite.

  Why this reaches the endpoint the exponent bound cannot: `(R5)` needs `alpha + 1 < k`, vacuous at
  `k = 1` for `alpha >= 0`.  Here no exponent is involved at all — finitely many positive
  coefficients give a *bounded* source, which is already decay at `b = 0`, and `0 < Re rho` for every
  nontrivial zero.

  The conductor-one case of the card is now complete: `(R1)`, reality, `(R7)`, `(R8)`, the `(R3)`
  upper bound (all pre-existing), plus `Theta >= 1/2`, `(R11)`, `(R13)`/`(R14)`, the Mellin
  obstruction, `(R5)`, and `(R4)`.  Remaining: the arbitrary primitive character (no `L(s,chi)` zero
  infrastructure in the corpus), and the arithmetic restatement of `(R6)` as
  `sum_(a+b=N) mu(a) mu(b) >= 1` via `mixedAdditiveConvolutionPower_one` and integrality.
  Gate stays unchecked.
- 2026-07-27 — **`(R6)` proved: `sum_(a+b=N) mu(a) mu(b) >= 1` for infinitely many `N`.**  New module
  `RHTower/MobiusBinaryExcursion.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).  This is the card's headline arithmetic statement.
  * `mobiusIntConvolution N` — the binary additive self-convolution as an **integer**.
  * `mixedAdditiveConvolutionPower_one_mobius` — at order one the Hermitian mixed convolution is the
    corpus's `mobiusAdditiveConvolution` (conjugation is trivial on integer casts).
  * `mixedAdditiveConvolutionPower_one_mobius_re` — its real part is that integer.
  * `exists_notMem_one_le_mobiusIntConvolution` and `infinite_one_le_mobiusIntConvolution` —
    **`(R6)`**: beyond every finite set of indices the convolution attains a value `>= 1`, and the
    set of such indices is infinite.  Positivity upgrades to `>= 1` purely by integrality.

  Duplication note, corrected: this development introduced `mobiusCoeff`, which is definitionally
  the corpus's `mobiusComplexCoefficient`.  `mobiusCoeff_eq_mobiusComplexCoefficient` records the
  identification (`rfl`) so the two notions cannot drift apart.

  **Conductor one is now complete**, `(R1)` through `(R14)` including both `(R4)`/`(R6)` and `(R5)`.
  The gate `full analytic Lean formalization` nonetheless stays unchecked, for one reason only: the
  card states its theorem for an arbitrary primitive Dirichlet character `chi`, and the corpus has no
  `L(s,chi)` zero infrastructure to instantiate the Mellin obstruction with.  Everything else the
  card asserts is formalized and unconditional.
- 2026-07-27 — **`(R9)` at arbitrary conductor.**  New module `RHTower/TwistedMobiusMellin.lean`
  (unconditional, axioms `[propext, Classical.choice, Quot.sound]`).  First step of the
  general-character case.
  * `twistedMobiusLaplaceTransform chi` — the source `sum chi(n) mu(n) e^{-n x}`, with absolute
    convergence at every positive scale (`|chi(n) mu(n)| <= 1`).
  * `twistedMobiusMellin_weight_summable` — the Mellin interchange weight is summable on `Re s > 1`,
    from mathlib's `DirichletCharacter.LSeriesSummable_mul` applied to the Möbius series.
  * `mellin_twistedMobiusLaplaceTransform_eq_gamma_mul_LSeries` — `mellin A_chi s = Gamma s * L(chi mu) s`,
    by `hasSum_mellin`, mirroring the corpus's conductor-one proof.
  * `mellin_twistedMobiusLaplaceTransform_eq_gamma_div_LSeries` — **`(R9)`**:
    `mellin A_chi s = Gamma s / L(s, chi)`, using mathlib's `DirichletCharacter.LSeries.mul_mu_eq_one`.

  Corpus/mathlib audit for the general case: mathlib carries the pieces this step needs — the
  twisted convolution identity `chi * (chi mu) = delta`, the inverse relation, nonvanishing on
  `Re s > 1`, and the functional equation `IsPrimitive.completedLFunction_one_sub`.  What it does
  **not** carry, and what the corpus supplies only for `zeta`, is the existence of nontrivial zeros
  of `L(s, chi)`.  The corpus's `xiDivisorSupport_infinite` is a bespoke growth argument for `xi`
  (`xiFinitePolynomial`), not a general order-one mechanism, so it does not transfer as it stands.

  That single missing input — a zero of `L(s, chi)` in the strip — is now the only obstacle to
  running the whole conductor-one chain at arbitrary conductor.  Gate stays unchecked.
- 2026-07-27 — **Twisted analytic groundwork.**  Appended to `RHTower/TwistedMobiusMellin.lean`
  (unconditional, axioms `[propext, Classical.choice, Quot.sound]`).  The estimates the Mellin
  analyticity criterion consumes depend only on `‖chi(n) mu(n)‖ <= 1`, so they transfer from the
  untwisted development with the coefficient bound swapped:
  * `continuousOn_twistedMobiusLaplaceTransform`,
    `twistedMobiusLaplaceTransform_locallyIntegrableOn` — continuity on `(0, infinity)` by uniform
    majorant on `[x/2, infinity)`, hence local integrability.
  * `norm_twistedMobiusLaplaceTransform_le_exp_neg`,
    `twistedMobiusLaplaceTransform_isBigO_exp_neg` — the exponential tail past scale one.
  * `TwistedMobiusLaplaceDecay chi b` and its `isBigO` — the decay predicate at arbitrary exponent.
  * `analyticOnNhd_mellin_of_twistedMobiusLaplaceDecay` — **the twisted Mellin transform is analytic
    on `Re s > b`**.

  The general-conductor chain now matches the conductor-one one as far as analyticity:
  `(R9)` (previous entry) and Mellin analyticity from decay are both in place for arbitrary `chi`.
  Still missing, and still the only obstacle: existence of a zero of `L(s, chi)` in the strip, plus
  the `(R8)`/`(R11)` coefficient side for the twisted sequence (which is generic in the coefficient
  sequence and so should specialize without new analysis).  Gate stays unchecked.
- 2026-07-27 — **General conductor: `(R9)`, analytic groundwork, coefficient side, and the
  obstruction.**  New modules `RHTower/TwistedMobiusMellin.lean` and
  `RHTower/TwistedMobiusZeroObstruction.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).
  * `twistedMobiusLaplaceTransform chi` and `mellin_..._eq_gamma_div_LSeries` — `(R9)` at arbitrary
    conductor, `mellin A_chi s = Gamma s / L(s, chi)` on `Re s > 1`, from mathlib's `hasSum_mellin`
    and `DirichletCharacter.LSeries.mul_mu_eq_one`.
  * `continuousOn_...`, `..._locallyIntegrableOn`, `..._isBigO_exp_neg`,
    `TwistedMobiusLaplaceDecay chi b`, `analyticOnNhd_mellin_of_twistedMobiusLaplaceDecay` — the
    analytic groundwork; these use only `‖chi(n) mu(n)‖ <= 1` and so transfer from the untwisted
    development.
  * `twistedMobiusLaplaceDecay_of_subpower` — the coefficient side.  No new analysis was needed:
    the radial bound in `MixedConvolutionSubpowerAbelBound` is generic in the coefficient sequence
    and specializes directly.
  * `not_twistedMobiusLaplaceDecay_of_LFunction_eq_zero` and
    `not_twistedMixedSubpower_of_LFunction_eq_zero` — **the obstruction at arbitrary conductor**.
    For `chi != 1` the L-function is entire, so this is shorter than the conductor-one argument: no
    regularizing factor `(s-1)` is needed, and `G = mellin A_chi . L(.,chi)` is compared directly
    with `Gamma`.

  The general-conductor chain therefore matches conductor one at every step except the endpoint.
  The single remaining input is existence of a zero of `L(s, chi)` in the strip: mathlib supplies
  the functional equation (`IsPrimitive.completedLFunction_one_sub`) but not zero existence, and the
  corpus's `xiDivisorSupport_infinite` is a bespoke growth argument for `xi` that does not transfer.
  Gate stays unchecked.
- 2026-07-27 — **`(R4)` proved unconditionally at arbitrary primitive conductor.**  The only
  remaining input was the existence of an `L(s,chi)` zero with `Re > 0`; that is now formalized from
  scratch.  Seven new modules, all axiom-clean `[propext, Classical.choice, Quot.sound]`:
  - `HTGeometry/OrderOneEnvelope.lean` — the growth class `OrderOneEnvelope f`
    (`‖f s‖ ≤ exp(C(1+‖s‖)log(2+‖s‖))`) with closure under sums, products, constants, finite sums,
    affine substitution and the factors `n^(-s)`, plus `OrderOneEnvelope.subquadratic` converting it
    to the `exp(C(1+‖s‖)^(3/2))` shape consumed by `exists_zero_of_superlinear_ray_growth`.
  - `RHTower/MellinOrderOneEnvelope.lean` — `mellin_orderOneEnvelope_of_decay` (a kernel with
    exponential decay at both ends has an order-one Mellin transform), `rpow_mul_exp_neg_le`
    (`u^m e^{-cu} ≤ e^{m²/c}` on `[1,∞)`), `head_bound_absorb`, and the two-sided decay estimates
    `weakFEPair_f_modif_decay` / `weakFEPair_f_decay` for an abstract `WeakFEPair`.
  - `RHTower/HurwitzZetaOrderOne.lean` — `completedHurwitzZetaEven₀_orderOneEnvelope` and
    `completedHurwitzZetaOdd_orderOneEnvelope` for *every* shift `a`, from the mathlib theta bounds
    `isBigO_atTop_{even,cos,odd,sin}Kernel*` globalized by `global_exp_bound`.
  - `RHTower/DirichletCompletedLOrderOne.lean` — `completedLFunction_orderOneEnvelope`.  For
    `chi ≠ 1` both rational correction terms of `ZMod.completedLFunction_eq` vanish, so the completed
    L-function *is* the entire `completedLFunction₀`.
  - `RHTower/DirichletCompletedLRayGrowth.lean` — `norm_Gammaℝ_ofReal`, `Gammaℝ_ofReal_ne_zero`,
    `log_norm_Gammaℝ_ofReal`, `exists_Gammaℝ_ray_growth` and `completedLFunction_ray_growth`.
    Evaluating at `sigma = 2(m+1) - d` (`d = 0/1` by parity) turns the Archimedean factor into
    `pi^{-(m+1)} m!`.
  - `RHTower/DirichletLZeroExistence.lean` — `exists_completedLFunction_eq_zero` (Hadamard) and
    `exists_LFunction_eq_zero_pos_re`.  Side result `rootNumber_ne_zero` for primitive `chi`, proved
    from the functional equation plus nonvanishing of the completion on the real ray — mathlib has no
    such lemma.
  - `RHTower/TwistedMobiusPositiveExcursion.lean` —
    `exists_notMem_pos_twistedMixedAdditiveConvolutionPower` and
    `infinite_pos_twistedMixedAdditiveConvolutionPower`: **`(R4)` for every nontrivial primitive
    Dirichlet character**, at every order `k >= 1`.
  Reuse: `intbound_of_decay` and `global_exp_bound` (previously `private` in `CompletedZetaGrowth`)
  were the whole analytic engine and are now public; `norm_le_rpow_of_norm_pow_sq_le` likewise.
  Corpus search first ruled out re-deriving the Mellin modulus estimate.
  Still open on this card: `Theta_chi >= 1/2` at general conductor (needs the conjugation
  `L(conj s, chi⁻¹) = conj L(s,chi)` to reflect zeros across `Re = 1/2`), hence the twisted `(R5)`.
- 2026-07-27 — **`Theta_chi >= 1/2` and the twisted `(R5)` proved.**  Five further modules, all
  axiom-clean:
  - `HTGeometry/MellinConjugate.lean` — `mellin_conj` (conjugation passes through a Mellin
    transform after conjugating the parameter, since the kernel has positive real base),
    `mellin_conj_of_conj_invariant` (the reflection principle for a real kernel), `conj_indicator`,
    `conj_natCast_cpow_neg`.
  - `RHTower/DirichletCompletedLConjugate.lean` — `conj_f_modif` (the modified kernel of a
    functional-equation pair with real data is real), `conj_completedHurwitzZetaEven₀`,
    `conj_completedHurwitzZetaOdd`, `norm_dirichletCharacter_apply` (unit modulus on units, from
    `MulChar.pow_card_eq_one`), `conj_dirichletCharacter_apply` (`conj (chi j) = chi⁻¹ j`), and the
    headline `conj_completedLFunction`: `conj Lambda(s,chi) = Lambda(conj s, chi⁻¹)`.  Mathlib has
    none of these.
  - `RHTower/DirichletLZeroHalfPlane.lean` — `completedLFunction_eq_zero_reflect`: conjugation
    followed by the functional equation is the reflection `rho -> 1 - conj rho` in the critical
    line, so the completed zero divisor is symmetric about `Re = 1/2`.  Hence
    `exists_LFunction_eq_zero_half_le_re` (**`Theta_chi >= 1/2`**) and
    `not_twistedMixedSubpower_of_lt_sub_one` (no subpower bound of exponent below `k-1`).
  - `HTGeometry/LogOrderLimsupLower.lean` — `isBoundedUnder_log_one_add_div_log` and
    `le_limsup_log_one_add_div_log`, the lower-bound companions of the existing
    `limsup_log_one_add_div_log_le`.
  - `RHTower/TwistedMobiusOrderLowerBound.lean` — `exists_global_subpower` (a subpower bound valid
    off a finite set globalizes), `frequently_lt_re_twistedMixedAdditiveConvolutionPower`
    (**`(R5)` in the literal omega-plus form**: for every `alpha < k-1` and every `C`,
    `C (M+1)^alpha < Re R_{chi,k}(M)` infinitely often) and
    `sub_one_le_limsup_twistedMixedAdditiveConvolutionPower` (**the lower half `k-1 <= Psi_{chi,k}`
    of the order law `(R3)`**, in the same `limsup log(1+max(Re R,0))/log(N+1)` exponent used by the
    already-formalized upper half `Psi <= 2k-1`).
  With this, `(R1)`-`(R15)` are formalized for every nontrivial primitive Dirichlet character:
  `(R3)` both halves, `(R4)`, `(R5)`, `(R6)` at conductor one, `(R7)`-`(R14)` for an arbitrary
  coefficient sequence.  Primitivity is the hypothesis the functional equation needs; it is not a
  weakening of the card, whose zero-frontier quantity `Theta_chi` is a primitive-character notion.
- 2026-07-27 — **`(R3)` lower half generalized to the true zero frontier**, correcting the previous
  entry, which had only recorded the `Theta_chi = 1/2` specialization.  In
  `RHTower/TwistedMobiusOrderLowerBound.lean`, the argument is now factored as
  `frequently_lt_of_no_subpower` (no subpower bound at exponent `alpha` implies recurrence of large
  values) and `le_limsup_of_no_subpower_below` (no subpower bound below `theta` implies
  `theta <= Psi`), so the `L`-zero enters only through the threshold.  The headline is
  `two_mul_re_sub_one_le_limsup_twistedMixedAdditiveConvolutionPower`: **every** `L`-zero `rho`
  gives `2k·Re rho - 1 <= Psi_{chi,k}`, which is `(R3)` as stated.  The earlier
  `sub_one_le_limsup_...` (`k-1 <= Psi`) is now a two-line corollary via
  `exists_LFunction_eq_zero_half_le_re`.
- 2026-07-27 — **Gate audit: the Lean gate stays unchecked, and the reason is `(R15)`.**  Going
  statement by statement, `(R1)`, `(R2)`, `(R3)` (both halves), `(R4)`, `(R5)`, `(R7)`-`(R14)` are
  formalized, and `(R6)` at conductor one.  `(R15)` — the exact companion
  `limsup log(1+[C_{chi,k}(N)]_+)/log(N+1) = 2k(1+Theta_chi)-1` for the mixed convolution of the
  partial sums `M_chi` — is not.  Its lower half should follow from the already-formalized `(R14)`
  binomial integration law plus the `(R3)` machinery above; its upper half is the part the card
  itself flags as resting on the classical twisted Littlewood theorem, i.e. it needs
  `M_chi(N) = O(N^{Theta_chi + epsilon})`.  That is a Perron/contour estimate on `1/L(s,chi)` in
  `Re s > Theta_chi` and has no mathlib counterpart, so it is the next build.  Note this is the
  hard direction: the corpus route so far has produced lower spectral edges from zeros, and the
  matching upper edge is a genuinely different argument, not a rearrangement of what exists.
- 2026-07-27 — **`(R15)` lower half proved; `(R3)` and `(R15)` restated at the zero frontier.**
  Four new modules plus one extension, all axiom-clean:
  - `RHTower/TwistedMertensOrderLowerBound.lean` — the partial-sum source.  `norm_partialSumSeq_le`,
    `summable_norm_partialSumSeq_mul_pow`, and `tsum_partialSumSeq_mul_pow`
    (`(1-q)·sum M(n)q^n = sum a(n)q^n`, by Cauchy product against the geometric series).  The key
    step is `twistedMobiusLaplaceDecay_of_mertensSubpower`: on the ray `z = e^{-x}` the factor
    `1 - e^{-x} <= x` converts a subpower bound of exponent `alpha` on the Hermitian mixed
    convolution of `M_chi` into decay of the *raw* source at the shifted exponent
    `(alpha+1)/(2k) - 1`.  Hence `not_mertensSubpower_of_LFunction_eq_zero` and
    `two_mul_one_add_re_sub_one_le_limsup_mertens`: an `L`-zero at `rho` gives
    `2k(1 + Re rho) - 1 <= Psi^C_{chi,k}`.
  - `RHTower/DirichletZeroAbscissa.lean` — `zeroAbscissa chi` (= `Theta_chi`), well defined because
    the zero set is nonempty (this programme's Hadamard argument) and bounded above by `1`
    (mathlib's nonvanishing on `Re >= 1`).  With `half_le_zeroAbscissa`, `zeroAbscissa_le_one`,
    `LFunction_ne_zero_of_zeroAbscissa_lt` and `exists_zero_lt_re`.
  - `RHTower/TwistedOrderLawTheta.lean` — the order laws in the card's own form:
    `two_mul_zeroAbscissa_sub_one_le_limsup` is **`(R3)` lower, `2k Theta_chi - 1 <= Psi_{chi,k}`**,
    and `two_mul_one_add_zeroAbscissa_sub_one_le_limsup_mertens` is **`(R15)` lower,
    `2k(1 + Theta_chi) - 1 <= Psi^C_{chi,k}`**.  Both use `exists_zero_lt_re` to approach the
    frontier, so they are sup statements, not single-zero statements.
  - `HTGeometry/LogOrderLimsupLower.lean` gained `limsup_log_one_add_div_log_le_rpow`, the
    real-exponent form of the order upper bound.
  - `TwistedMobiusOrderLowerBound.lean` was refactored so `frequently_lt_of_no_subpower` and
    `le_limsup_of_no_subpower_below` apply to an arbitrary coefficient sequence with a polynomial
    bound; the `chi` and the partial-sum instances now share one proof.
  **Remaining for `(R15)`: only its upper half**, and it is isolated exactly.
  `norm_mixedAdditiveConvolutionPower_le_of_subpower` plus
  `limsup_mertens_le_of_subpowerBound` prove unconditionally that the interface
  `TwistedMertensSubpowerBound chi theta` (`M_chi(N) = O(N^{theta+eps})` for every `eps > 0`) caps
  the companion exponent at `2k(1+theta) - 1`, and `limsup_mertens_eq_of_subpowerBound` then gives
  `(R15)` as an equality.  So the entire remaining debt on this card is the classical Littlewood
  estimate at `theta = Theta_chi`: a Perron/contour argument needing (a) polynomial growth of
  `1/L(s,chi)` in `Re s >= Theta_chi + eps` and (b) Perron's formula, neither in mathlib.  That is
  the next build; nothing else on `(R1)`-`(R15)` is open.
- 2026-07-27 — **Started the Littlewood build: exact Gamma modulus on vertical lines.**  New module
  `HTGeometry/GammaVerticalModulus.lean`, axiom-clean.  The reduction of the remaining debt in the
  previous entry needs `1/L(s,chi)` polynomially bounded right of `Theta_chi`, which classically
  routes through Phragmen-Lindelof between two vertical lines, and that needs two-sided control of
  the Archimedean factor.  Mathlib has `PhragmenLindelof.vertical_strip` but **no Stirling estimate
  for the complex Gamma function**, so the usual route is blocked.
  Route taken instead: on the lines `Re z = 1/2` and `Re z = 1` the reflected point `1 - z` is the
  complex conjugate of `z`, so `Gamma(z) Gamma(1-z) = pi / sin(pi z)` computes the modulus
  **exactly**, with no asymptotics:
  - `norm_Gamma_half_add_I_sq` : `‖Gamma(1/2 + it)‖^2 = pi / cosh(pi t)`;
  - `norm_Gamma_one_add_I_sq` : `‖Gamma(1 + it)‖^2 = pi |t| / |sinh(pi t)|` (via
    `Gamma(1+it) = it Gamma(it)`);
  - `norm_Gamma_add_one` : `‖Gamma(z+1)‖ = ‖z‖ ‖Gamma(z)‖`, which propagates both to every line
    `Re z` in `(1/2)Z`;
  - `norm_Gamma_half_add_I_bounds` : `sqrt(pi) e^{-pi|t|/2} <= ‖Gamma(1/2+it)‖ <=
    sqrt(2 pi) e^{-pi|t|/2}`, from `e^{|x|}/2 <= cosh x <= e^{|x|}`.
  Both base lines are needed, not just one: the functional equation puts the two Gamma arguments at
  `(sigma+delta)/2` and `(1-sigma+delta)/2`, whose parities are opposite, so one always lands on a
  half-integer line and the other on an integer line.
  Next: the `Re z = 1` two-sided bound, the recursion to a general line, then the strip bound for
  `L(s,chi)` and Borel-Caratheodory for `log L`.
- 2026-07-27 — **Gamma vertical-line infrastructure completed** (same module, all axiom-clean):
  - `norm_Gamma_le_Gamma_re` : `‖Gamma s‖ <= Gamma (Re s)` for `Re s > 0`, straight from the
    integral representation (`Gamma_eq_integral` + `GammaIntegral_eq_mellin`).  This is the cheap
    upper bound on Gamma in any right half-plane, needed in the strip argument.
  - `norm_Gamma_add_nat` : `‖Gamma (z+m)‖ = (prod_{i<m} ‖z+i‖) ‖Gamma z‖`.
  - `norm_Gamma_shift_bounds` : transports a two-sided bound on the line `Re z = sigma` to
    `Re z = sigma + m`, each factor `‖z+i‖` lying between `|t|` and `(sigma+m+1)|t|`, so the
    polynomial factor is `|t|^m` on both sides and the exponential factor is untouched.
  - `norm_Gamma_one_add_I_bounds` : `sqrt(2 pi |t|) e^{-pi|t|/2} <= ‖Gamma(1+it)‖ <=
    sqrt(2 pi |t|/(1-e^{-2})) e^{-pi|t|/2}` for `|t| >= 1`, from
    `(1-e^{-2}) e^x/2 <= sinh x <= e^x/2`.
  - `norm_Gamma_half_add_nat_bounds`, `norm_Gamma_one_add_nat_bounds` : the two families on the
    lines `Re z = 1/2 + m` and `Re z = 1 + m`, covering every line in `(1/2)Z` to the right of the
    base lines.
  Both families carry the same exponential factor `e^{-pi|t|/2}`, which is why the argument works:
  in the functional equation the two Gamma factors sit at `(sigma+delta)/2` and
  `(1-sigma+delta)/2`, both with imaginary part of modulus `|t|/2`, so the exponentials cancel and
  the ratio is polynomial in `|t|`.  That is the estimate the left edge of the
  Phragmen-Lindelof strip needs.
  Next: the left/right edge bounds for `L(s,chi)` on `Re s = -2` and `Re s = 3`, then
  `PhragmenLindelof.vertical_strip` for polynomial growth of `L` throughout, then
  Borel-Caratheodory on `log L` in the zero-free half-plane for `1/L`, then Perron.
- 2026-07-27 — **Right edge of the Phragmen-Lindelof strip, and the compact Gamma bound.**  New
  module `RHTower/DirichletLStripBounds.lean`, axiom-clean:
  - `norm_dirichletCharacter_le_one` : `‖chi a‖ <= 1` everywhere (unit modulus on units, zero
    elsewhere), from `norm_dirichletCharacter_apply`.
  - `exists_bound_LFunction_of_two_le_re` : `‖L(s,chi)‖` is bounded by a single constant on the
    whole half-plane `Re s >= 2`, by comparison of the Dirichlet series with `sum n^{-2}`
    (`Real.summable_nat_rpow_inv`).  This is the right edge of the strip.
  - `exists_bound_Gamma_Icc` / `exists_bound_norm_Gamma_strip` : `‖Gamma v‖ <= B` uniformly on any
    vertical strip `a <= Re v <= b` with `a > 0`, combining `norm_Gamma_le_Gamma_re` with
    continuity of the real `Gamma` on a compact interval (`Real.differentiableAt_Gamma`, which
    applies since every point of the interval is positive hence not a pole).
  Remaining chain to the Littlewood estimate, in order: the left edge on `Re s = -2` via the
  functional equation and the Gamma-line bounds (the exponential factors `e^{-pi|t|/2}` cancel
  between the two Gamma factors, leaving a polynomial ratio); `PhragmenLindelof.vertical_strip`
  for polynomial growth of `L` throughout `-2 <= Re s <= 3`; Borel-Caratheodory on `log L` in the
  zero-free half-plane to invert that into polynomial growth of `1/L`; then Perron.
- 2026-07-27 — **Left-edge ingredients: leftward Gamma lower bounds and the parity bookkeeping.**
  All axiom-clean.  In `HTGeometry/GammaVerticalModulus.lean`:
  - `norm_Gamma_lower_of_shift` : the recursion run backwards.  A lower bound at `Re z = a + m`
    yields `c e^{-pi|t|/2} <= ((|a|+m+1)|t|)^m ‖Gamma(a+it)‖`, i.e. a lower bound on lines *left* of
    the base lines.  This is what the denominator of the functional-equation ratio needs: at
    `Re w = -2` the Gamma arguments sit at `Re = -1` and `Re = -1/2`, two and one steps left of the
    base lines `Re = 1` and `Re = 1/2`.
  - `norm_Gammaℝ` : `‖Gammaℝ z‖ = pi^{-Re z/2} ‖Gamma(z/2)‖` at an arbitrary complex point
    (the earlier version was only for real argument).
  In `RHTower/DirichletLStripBounds.lean`:
  - `inv_even_iff`, `gammaFactor_inv` : `chi` and `chi⁻¹` have the same parity, so the same
    Archimedean factor.  Needed because the functional equation swaps the character, and the two
    Gamma factors must carry the same shift `delta` for their exponentials to cancel.
  - `gammaFactor_eq_Gammaℝ` : the factor is `Gammaℝ(s + delta)` with `delta` in `{0,1}`, packaged so
    the parity split happens once.
  With the right edge already bounded, the left edge is now a bookkeeping assembly: at `Re w = -2`
  and `s = 1 - w` (so `Re s = 3`), the ratio `‖Gammaℝ(s+delta)‖/‖Gammaℝ(w+delta)‖` has both Gamma
  arguments at imaginary part of modulus `|t|/2`, so the `e^{-pi|t|/2}` factors cancel and only the
  polynomial factors survive.  Then Phragmen-Lindelof, Borel-Caratheodory, Perron.
- 2026-07-27 — **The Archimedean ratio across the functional equation is polynomial.**  New module
  `RHTower/DirichletLGammaRatio.lean`, axiom-clean.  This is the step the whole
  Phragmen-Lindelof route hangs on.
  - `ratio_bound_of_exp_cancel` : an upper bound `X <= U E` and a lower bound `c E <= P Y` sharing
    the same exponential `E` give `c X <= U P Y`, with `E` gone.
  - `gammaArg_even_num` / `gammaArg_odd_num` / `gammaArg_even_den` / `gammaArg_odd_den` and the two
    `_shift` variants: the four points of the ratio, identified with the base lines.  At
    `Re w = -2`, `s = 1 - w`, the arguments are `(3+delta)/2 - (t/2)i` and `(-2+delta)/2 + (t/2)i`.
    For `delta = 0` they sit one step right of `Re = 1/2` and two steps left of `Re = 1`; for
    `delta = 1`, one step right of `Re = 1` and one step left of `Re = 1/2`.
  - `norm_Gamma_ratio_even` : for `|t| >= 2`,
    `‖Gamma((3 - it)/2)‖ <= 40 |t/2|^3 ‖Gamma((-2 + it)/2)‖`.
  - `exists_norm_Gamma_ratio_odd` : the same with the odd shift and constant
    `sqrt(2 pi/(1-e^{-2})) (15/2)/sqrt(pi)`.
  Both imaginary parts have modulus `|t|/2`, so the factor `e^{-pi|t|/4}` cancels exactly between
  numerator and denominator and only the polynomial factors of the vertical bounds survive.  This
  is the reason the Stirling-free route works at all: the two-sided bounds proved earlier are sharp
  in the exponential, and sharpness is exactly what makes the cancellation exact.
  Next: combine with the functional equation and the right-edge bound to get the left edge
  `‖L(w,chi)‖ = O(|t|^A)` on `Re w = -2`, then `PhragmenLindelof.vertical_strip`.
- 2026-07-27 — **Left edge of the strip proved.**  New module `RHTower/DirichletLLeftEdge.lean`,
  axiom-clean: `exists_bound_LFunction_left_edge` — for a primitive character,
  `‖L(-2 + it, chi)‖ <= A |t|^3` for `|t| >= 2`.
  The assembly runs the functional equation `Lambda(chi, 1-s) = N^{s-1/2} eps(chi) Lambda(chi⁻¹, s)`
  at `s = 3 - it`, clears both completions into `L * gammaFactor` (both Archimedean factors are
  nonzero there: at `Re = 3+delta` by positivity of the real part, at `Re = -2+delta` because
  `Gammaℝ` vanishes only at even negative *reals* while the argument has imaginary part `t != 0`),
  passes to norms, and applies the right-edge bound to `L(chi⁻¹, 3-it)` and the Gamma-ratio bound
  to the Archimedean quotient.  The constants `N^{5/2}`, `‖eps(chi)‖` and the two `pi`-powers
  `pi^{-(3+delta)/2}`, `pi^{-(-2+delta)/2}` are absorbed.
  Note the hypothesis `chi != 1` turned out to be unnecessary and was dropped: only primitivity is
  used, and the pole of the principal character sits at `s = 1`, away from both edges.
  Both strip edges are now bounded.  Next: `PhragmenLindelof.vertical_strip` needs, besides the two
  edge bounds, a growth condition inside `-2 <= Re s <= 3`; that comes from the order-one envelope
  of `Lambda` together with an upper bound for `1/Gamma` in the strip (via the reflection formula,
  `‖1/Gamma(z)‖ = ‖Gamma(1-z)‖ ‖sin(pi z)‖/pi`, both factors elementary there).  Then
  Borel-Caratheodory and Perron.
- 2026-07-27 — **Reciprocal Gamma bound in the strip** (appended to `RHTower/DirichletLStripBounds.lean`),
  axiom-clean.  This is the interior growth ingredient the Phragmen-Lindelof hypothesis needs.
  - `norm_sin_le` : `‖sin z‖ <= e^{|Im z|}`, from the exponential form of `sin` (no such bound in
    mathlib).
  - `exists_bound_norm_Gamma_strip_off_axis` : `‖Gamma v‖ <= B` on any vertical strip, with no
    positivity requirement on the real parts, provided `|Im v| >= 1`.  Shifting right past the poles
    is free: each shift factor `v+i` has modulus at least `|Im v| >= 1`, so the product in
    `norm_Gamma_add_nat` only helps.
  - `exists_lower_bound_norm_Gamma_strip` : `pi <= B e^{pi|Im z|} ‖Gamma z‖`, i.e. a *lower* bound on
    `‖Gamma z‖` in the strip.  Proof: clear the reflection formula to
    `Gamma(z) Gamma(1-z) sin(pi z) = pi` (legitimate since `sin(pi z) != 0` when `Im z != 0`), take
    norms, and bound the last two factors.  Stated multiplicatively so no division is needed.
  With this, `‖L(s,chi)‖ = ‖Lambda(s,chi)‖ · ‖1/gammaFactor‖` is bounded in the strip by
  `exp(C(1+‖s‖)log(2+‖s‖)) · B' e^{pi|Im s|/2}`, which is far inside the
  `exp(A exp(c|Im z|))` allowance of `PhragmenLindelof.vertical_strip` for any `c > 0`.
  Remaining: assemble that growth statement, apply Phragmen-Lindelof to
  `L(s,chi)/(s-4)^3` (whose two edge bounds are then both uniform: on `Re s = 3` because
  `|s-4| >= 1`, on `Re s = -2` because `|s-4| >= |t|` absorbs the cubic), then Borel-Caratheodory
  and Perron.
- 2026-07-27 — **Interior growth of `L` in the strip.**  New module
  `RHTower/DirichletLStripGrowth.lean`, axiom-clean: `exists_growth_LFunction_strip` — for
  `chi != 1`, on `-2 <= Re s <= 3` with `|Im s| >= 2`,
  `‖L(s,chi)‖ <= exp(B (1+‖s‖) log(2+‖s‖))`.
  The point is that the *same* order-one shape absorbs everything.  Writing
  `L = Lambda / gammaFactor`, the numerator has the order-one envelope
  (`completedLFunction_orderOneEnvelope`), and the denominator is bounded below by
  `kappa e^{-pi|t|/2}` — from `exists_lower_bound_norm_Gamma_strip` for the Gamma factor and
  `pi^{-(Re s+delta)/2} >= pi^{-2}` for the power of `pi`, the latter uniform because the strip is
  bounded.  The resulting `e^{pi|t|/2}` is then itself dominated by the order-one shape, since
  `pi|t|/2 <= (pi/(2 log 2)) (1+‖s‖) log(2+‖s‖)`.  So no new growth class is needed.
  This is well inside the `exp(A exp(c |Im z|))` allowance of `PhragmenLindelof.vertical_strip`
  for every `c > 0`, so the last hypothesis of Phragmen-Lindelof is now available.
  Note the module is slow to elaborate (about five minutes) because of the nonlinear arithmetic;
  one `nlinarith` had to be replaced by an explicit chain after hitting the heartbeat limit.
  Remaining: apply Phragmen-Lindelof to `L(s,chi)/(s-4)^3`, then Borel-Caratheodory for `1/L`,
  then Perron.
- 2026-07-27 — **Uniform edge bounds for the regularized L-function.**  New module
  `RHTower/DirichletLRegularizedEdges.lean`, axiom-clean.
  Phragmen-Lindelof compares against a *single* constant on both edges, but the two edge bounds
  have different strength: bounded on `Re s = 3`, `O(|t|^3)` on `Re s = -2`.  Dividing by `(s-4)^3`
  equalizes them — on the right edge the divisor has modulus at least `1` so nothing is lost, on
  the left edge at least `|t|`, which absorbs the cubic exactly.
  - `exists_bound_LFunction_segment` : `L(chi, a + it)` is bounded for `|t| <= T`, by continuity of
    the entire L-function on a compact segment.  This patches the gap near the real axis, where the
    polynomial left-edge bound (proved only for `|t| >= 2`) says nothing.
  - `exists_bound_regularized_edges` : one constant `C` with
    `‖L(z,chi)/(z-4)^3‖ <= C` on both `Re z = 3` and `Re z = -2`, for all `z` on those lines.
  All four Phragmen-Lindelof hypotheses are now in hand: the two uniform edge bounds here, the
  interior growth from `exists_growth_LFunction_strip`, and differentiability of
  `L(.,chi)/(s-4)^3` on the closed strip (the pole at `4` sits outside `Re s <= 3`).
  Next: convert the interior growth into the `IsBigO` shape
  `f =O[|im| -> infinity within the strip] exp(B exp(c|im z|))` and apply
  `PhragmenLindelof.vertical_strip`.
- 2026-07-27 — **Phragmen-Lindelof applied: `L(s,chi)` grows polynomially across the strip.**
  New module `RHTower/DirichletLPhragmenInputs.lean`, axiom-clean.
  - `eventually_sq_le_exp` : `(c+u)^2 <= exp(b u)` eventually, for any `b > 0`.  Proved from the
    cubic term of the exponential series (`Real.sum_le_exp_of_nonneg` at `n = 4`) rather than from
    asymptotic machinery, so the threshold is explicit: `u >= max(|c|, 24/b^3, 1)`.
  - `differentiableAt_regularized`, `diffContOnCl_regularized` : the regularized function is
    holomorphic on the open strip and continuous on its closure — the pole at `4` is outside
    `Re s <= 3`, and `closure (re ⁻¹' Ioo a b) ⊆ re ⁻¹' Icc a b` by `closure_minimal`.
  - `isBigO_regularized` : the growth hypothesis, with rate `c = 1/3`.  The requirement is
    `c < pi/(b-a) = pi/5`, and `1/3 < pi/5` follows from `2 <= pi` alone — no sharper numeric bound
    on `pi` is needed, which matters because mathlib has no `pi_gt_three`.
  - `bound_LFunction_strip` : **`‖L(z,chi)‖ <= C ‖z-4‖^3` on the whole closed strip
    `-2 <= Re z <= 3`.**
  This closes the Phragmen-Lindelof stage.  The chain from here: Borel-Caratheodory on `log L` in
  the zero-free half-plane `Re s > Theta_chi` converts this upper bound into a *lower* bound
  `1/L(s,chi) = O(|t|^eps)`, and then Perron's formula turns that into the Littlewood estimate
  `M_chi(N) = O(N^{Theta_chi + eps})`, which is the single remaining input for `(R15)`.
- 2026-07-27 — **Holomorphic logarithm on a disc.**  New module `HTGeometry/BallLogarithm.lean`,
  axiom-clean: `exists_log_on_ball` — a nonvanishing holomorphic `f` on `ball c r` equals
  `f c · exp(g)` for a holomorphic `g` on the disc with `g c = 0`.
  This is the disc analogue of the earlier `exists_entire_log_of_ne_zero`, and it is the gate for
  Borel-Caratheodory: the whole point of the next step is to convert the *upper* bound
  `‖L‖ <= C‖z-4‖^3` into a *lower* bound on `‖L‖`, and Borel-Caratheodory does that by bounding
  `|log L|` in terms of `sup Re log L = sup log|L|` — which requires a genuine holomorphic branch of
  `log L` on the disc, not just the principal value.
  Mathlib supplies the missing analytic input: `DifferentiableOn.isExactOn_ball` (Morera for a
  disc) gives a primitive of `f'/f` there, and `Convex.is_const_of_fderivWithin_eq_zero` then makes
  `f · exp(-g)` constant.  Neither the entire version nor this one exists in mathlib.
  Next: apply `Complex.borelCaratheodory_zero` on the disc centred at `2 + it` with radii chosen
  inside the zero-free half-plane `Re s > Theta_chi`, to get `1/L(s,chi)` polynomially bounded;
  then Perron.
- 2026-07-27 — **Borel-Caratheodory lower bound.**  Appended to `HTGeometry/BallLogarithm.lean`,
  axiom-clean: `norm_lower_bound_of_ball` — a nonvanishing holomorphic `f` on `ball c R`, bounded
  above by `M` there and below by `m` at the centre, satisfies
  `m exp(-2 (log(M/m)+1) r/(R-r)) <= ‖f z‖` for `‖z - c‖ <= r < R`.
  This is the sign reversal the whole Phragmen-Lindelof chain was built for: an *upper* bound on
  `‖f‖` becomes a *lower* bound, at the cost of an exponential in `log(M/m)` — i.e. of turning a
  polynomial upper bound into a polynomial lower bound with a worse exponent, which is exactly what
  Perron tolerates.
  Mechanism: `exists_log_on_ball` gives `g` with `f = f c exp g` and `g c = 0`; then
  `Re g = log(‖f‖/‖f c‖) <= log(M/m)`, mathlib's `Complex.borelCaratheodory_zero` (translated to
  the origin) bounds `‖g‖` on the inner disc, and `‖f‖ = ‖f c‖ exp(Re g) >= m exp(-‖g‖)`.
  The `+1` in the constant is not slack for its own sake: Borel-Caratheodory requires a *strictly*
  positive bound on `Re g`, and `log(M/m)` can be zero.
  Next: instantiate at `c = 2 + it` with `r = 2 - (Theta_chi + eps)`, `R = 2 - (Theta_chi + eps/2)`,
  using `bound_LFunction_strip` for `M` and `eventually_half_le_norm_LSeries` for `m`, to get
  `1/L(s,chi)` polynomially bounded right of `Theta_chi`.  Then Perron.
- 2026-07-27 — **Uniform lower bound on a vertical line.**  New module
  `RHTower/DirichletLLineLowerBound.lean`, axiom-clean: `exists_line_lower_bound` — there is an
  explicit abscissa `sigma_0 >= 2` with `‖L(s,chi)‖ >= 1/2` for **every** `s` with
  `Re s >= sigma_0`, uniformly in `Im s`.
  Uniformity in the imaginary part is the whole point: this supplies the value at the *centre* of
  the Borel-Caratheodory disc, and that centre travels up the vertical line, so the earlier
  `eventually_half_le_norm_LSeries` (valid only along the real ray) is not usable here.
  The proof splits `n = 1` off the Dirichlet series and compares the remainder with
  `2^{2-sigma} sum n^{-2}`, using `n^{-sigma} = n^{-2} n^{2-sigma} <= n^{-2} 2^{2-sigma}` for
  `n >= 2`.  The threshold is `sigma_0 = max 2 (2 + log(2(S+1))/log 2)` with `S = sum n^{-2}`
  — explicit, and with no numerical estimate: the tail is compared against itself at exponent `2`
  rather than evaluated.  (Comparing at `Re s = 2` directly would have required knowing
  `zeta(2) - 1 < 1`, i.e. a numeric bound, which the card's rules forbid.)
  Next: instantiate `norm_lower_bound_of_ball` at `c = sigma_0 + it` with
  `r = sigma_0 - (Theta_chi + eps)`, `R = sigma_0 - (Theta_chi + eps/2)`, taking `M` from
  `bound_LFunction_strip` together with the right-edge bound, and `m = 1/2` from here.
- 2026-07-27 — **Polynomial lower bound for `L` right of the zero abscissa.**  New module
  `RHTower/DirichletLInverseBound.lean`, axiom-clean: `exists_lower_bound_right_of_abscissa` — for
  every `eps` in `(0,1)` there are `sigma_0 >= 2`, `K > 0`, `A >= 0` with
  `K exp(-A log(2+|Im s|)) <= ‖L(s,chi)‖` for all `s` with
  `Theta_chi + eps <= Re s <= sigma_0`.  Equivalently `1/L(s,chi)` is `O((2+|t|)^A)` there.
  This is the sign flip the whole Phragmen-Lindelof chain existed to produce.  The disc is centred
  at `sigma_0 + it` with outer radius `sigma_0 - (Theta_chi + eps/2)` — chosen so the closed outer
  disc stays inside the zero-free half-plane — and inner radius `sigma_0 - (Theta_chi + eps)`, so
  `R - r = eps/2` and the exponent comes out proportional to `1/eps`.  The upper bound `M` on the
  disc is assembled from the two regimes: the right-edge bound where `Re z >= 2`, the
  Phragmen-Lindelof cubic where `Re z <= 3`.
  One Lean-level obstacle worth recording: `set Theta := zeroAbscissa chi` makes `Theta` a
  let-binding, and every `nlinarith`/`positivity` call downstream then tries to unfold it through
  `sSup` and dies on heartbeats.  Introducing the abscissa opaquely
  (`obtain ⟨Theta, hTheta⟩ : ∃ T, zeroAbscissa chi = T := ⟨_, rfl⟩`) and calling `clear_value` on the
  remaining `set` variables fixed it.
  Remaining for the card: Perron's formula, turning this into
  `M_chi(N) = O(N^{Theta_chi + eps})`, which discharges `TwistedMertensSubpowerBound` and with it
  the upper half of `(R15)`.
- 2026-07-27 — **Route analysis for the last step (Perron), two cheap routes ruled out.**  No new
  Lean this entry; the deliverable is that the remaining construction is now pinned down and two
  plausible shortcuts are eliminated by computation rather than left to be discovered later.
  - *Ruled out: Riesz / Cesaro means.*  Mathlib's `mellinInv_mellin_eq` makes the order-1 kernel
    free — `(1-x)_+` has Mellin transform `1/(s(s+1))`, which is vertically integrable, so the
    absolutely convergent Perron formula for `R(N) = sum_{n<=N}(N-n)a_n` needs no contour work at
    all, and the shift gives `R(N) = O(N^{1+Theta+eps})` with no residues (the kernel's poles at
    `s = 0,-1` lie left of `Theta`, and `1/L` is analytic right of it).  But recovering `M(N)`
    costs too much: `h M(N) = R(N+h) - R(N) - sum_{N<n<=N+h}(N+h-n)a_n`, the last sum is only
    `O(h^2)` under `|a_n| <= 1`, and optimizing `h` gives `M(N) = O(N^{(1+Theta)/2 + eps})`.  Since
    `(1+Theta)/2 > Theta` for every `Theta < 1`, this is strictly lossy — at `Theta = 1/2` it gives
    `3/4` instead of `1/2`.  Higher-order Riesz means are worse: the exponent
    `(k+Theta)/(k+1)` increases to `1`.  Bootstrapping fails too: re-substituting the improved bound
    into the boundary sum reproduces the same term.
  - *Ruled out: coefficients from the radial bound.*  For a nonnegative coefficient sequence,
    `sum b_N r^N <= B(1-r)^{-beta}` gives `b_N = O(N^beta)` by taking `r = 1 - 1/N`.  That is
    unavailable here: `C_{chi,k}(N)` is a Hermitian mixed convolution, nonnegative only in the
    aggregate (`sum C r^N = |G(r)|^{2k}`), not termwise, and the positive parts appearing in
    `Psi^C` are not controlled by the generating function.
  - *The route that works: Perron with a smooth weight.*  Take `w` smooth, `1` on `(-inf,N]`, `0`
    on `[N+H,inf)`, with `w^{(j)} = O(H^{-j})`.  Its Mellin transform decays in `|t|` like
    `(1+|t|H/N)^{-j}` by `j`-fold integration by parts, so the vertical integral converges
    absolutely, the line shift from `Re s = c > 1` to `Re s = Theta+eps` is a rectangle contour with
    vanishing horizontal sides, and `sum a_n w(n) = O(N^{Theta+eps})`.  Finally
    `|M(N) - sum a_n w(n)| <= H` since `|a_n| <= 1`, and `H = N^{Theta+eps}` makes both terms the
    same size — **sharp**, and with no truncated-kernel estimate anywhere.
  Build order for the next sessions: (P1) the smooth weight and its derivative bounds; (P2) the
  Mellin decay by integration by parts; (P3) `sum a_n w(n) = (1/2pi i) int F(s) W(s) ds` by Fubini;
  (P4) the line shift via `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`;
  (P5) the shifted estimate; (P6) the trivial comparison with `M(N)`.
- 2026-07-27 — **(P1) done: the smooth weight with scaled derivative bounds.**  New module
  `HTGeometry/SmoothWeight.lean`, axiom-clean.
  - `exists_bound_iteratedDeriv_smoothTransition` : every iterated derivative of
    `Real.smoothTransition` is globally bounded.  For `j >= 1` it vanishes off `[0,1]` — the
    transition is locally constant on either side, so `Filter.EventuallyEq.iteratedDeriv_eq`
    together with `iteratedDeriv_const` kills it there — and on `[0,1]` continuity plus compactness
    finish.
  - `smoothWeight N H x = 1 - smoothTransition (H⁻¹ (x + -N))`, with `smoothWeight_contDiff`,
    `smoothWeight_eq_one` (on `x <= N`), `smoothWeight_eq_zero` (on `N+H <= x`),
    `smoothWeight_nonneg`, `smoothWeight_le_one`.
  - `exists_bound_iteratedDeriv_smoothWeight` : **`|w^(j)(x)| <= C_j / H^j`**, the property the
    whole construction exists for.  Writing the argument as `H⁻¹ * (x + -N)` rather than
    `(x - N)/H` lets `iteratedDeriv_comp_const_mul` and `iteratedDeriv_comp_add_const` apply
    directly, so the scaling is exact rather than estimated.
  This is the first of the six steps of the smoothed-Perron plan.  Next: (P2) the Mellin transform
  of the weight and its `(1 + |t| H/N)^{-j}` decay by `j`-fold integration by parts.
- 2026-07-27 — **(P2) started: convergence of the cutoff's Mellin transform.**  New module
  `HTGeometry/SmoothWeightMellin.lean`, axiom-clean.
  - `continuousOn_mellin_smoothWeight` : the integrand `x^{s-1} w(x)` is continuous on `(0,∞)`.
  - `mellin_smoothWeight_eq_zero_of_le` : it vanishes from `N+H` on.
  - `integrableOn_mellin_smoothWeight` : **the Mellin transform converges for every `Re s > 0`.**
    Split `(0,∞) = (0,N+H] ∪ (N+H,∞)`; on the tail the integrand is identically zero, and on the
    head it is dominated by `x^{sigma-1}`, integrable near the origin exactly because
    `sigma > 0` (`intervalIntegral.intervalIntegrable_rpow'`).
  - `mellin_smoothWeight_eq` : the transform written as an explicit integral (`smul` to `mul`).
  Convergence on the *whole* half-plane `Re s > 0` is the point: the contour shift in the smoothed
  Perron formula moves the line from `c > 1` down to `Theta_chi + eps`, which is in `(1/2, 1)`, and
  both lines must be inside the region of convergence for the shift to say anything.
  Next in (P2): the `j`-fold integration by parts giving
  `W(s) = (-1)^j (s(s+1)...(s+j-1))^{-1} int w^{(j)}(x) x^{s+j-1} dx`, and with the `H^{-j}`
  derivative bounds the decay `|W(sigma+it)| = O(N^sigma (N/(H|t|))^{j-1}/|t|)`.
- 2026-07-27 — **(P2) integration by parts, finite-interval form.**  Appended to
  `HTGeometry/SmoothWeightMellin.lean`, axiom-clean:
  `intervalIntegral_mellin_smoothWeight_byParts` —
  `int_delta^{N+H} x^{s-1} w(x) dx = -delta^s/s - int_delta^{N+H} w'(x) x^s/s dx` for `s != 0`,
  `0 < delta <= N`.
  Both boundary terms are exact rather than estimated: at `N+H` the cutoff is zero
  (`smoothWeight_eq_zero`), at `delta` it is still one (`smoothWeight_eq_one`), so the term is
  `delta^s/s` with no error.  The analytic input is mathlib's `hasDerivAt_ofReal_cpow_const'` at
  exponent `r = s-1`, whose side condition `r != -1` is exactly `s != 0`; the cutoff side uses
  `HasDerivAt.ofReal_comp` on the real derivative.
  Cutting at a positive `delta` rather than at `0` is deliberate: on `[delta, N+H]` the factor
  `x^{s-1}` is continuous even when `Re s < 1`, so no improper endpoint enters, and the boundary
  term `delta^s/s` will simply vanish as `delta -> 0` for every `Re s > 0` — which is the whole
  half-plane the contour shift moves through.
  Next: the `delta -> 0` limit, then iterate to `j` derivatives, then the resulting decay estimate.
- 2026-07-27 — **(P2) the pieces for the `delta -> 0` passage.**  Appended to
  `HTGeometry/SmoothWeightMellin.lean`, axiom-clean:
  - `norm_integral_Ioc_zero_le` : `‖int_{(0,delta]} x^{s-1} w(x) dx‖ <= delta^sigma / sigma`.  The
    majorant `x^{sigma-1}` is integrated exactly (`integral_rpow`, using `0^sigma = 0` for
    `sigma > 0`), so the near-origin contribution is explicit rather than an unquantified `o(1)`.
  - `integral_Ioi_split` : `int_{(0,inf)} = int_{(0,delta]} + int_{(delta,N+H]}`, assembled from
    `Ioc_union_Ioi_eq_Ioi` (the tail integrand vanishes) and `Ioc_union_Ioc_eq_Ioc`.
  With these two the `delta -> 0` limit of the integration-by-parts identity is a bounded
  computation rather than an abstract convergence argument: every term on the right is either
  independent of `delta` or explicitly `O(delta^sigma)`, so the identity on `(0,inf)` follows by
  letting the explicit bound go to zero.
  Next: that passage, then the iteration to `j` derivatives.
- 2026-07-27 — **(P2) the derivative side: support and continuity.**  Appended to
  `HTGeometry/SmoothWeightMellin.lean`, axiom-clean:
  `deriv_smoothWeight_eq_zero_of_lt`, `deriv_smoothWeight_eq_zero_of_gt` (the cutoff's derivative
  vanishes on `x < N` and on `x > N+H`, since the cutoff is locally constant there),
  `continuousOn_deriv_integrand`, and the two integrand-vanishing corollaries.
  This settles a point that was not obvious in advance and simplifies the rest: `w'` is supported
  in `[N, N+H]`, a compact interval *bounded away from the origin*.  So the integral
  `int_{(0,inf)} w'(x) x^s/s dx` has no singular endpoint at all — unlike the `x^{s-1} w(x)` side,
  where the origin is genuinely improper for `Re s < 1`.  In particular
  `int_{(0,delta]} w'(x) x^s/s dx = 0` outright for `delta < N`, so in the `delta -> 0` passage the
  derivative term does not move: only the `x^{s-1} w` term and the boundary term `delta^s/s` do,
  and both are already bounded explicitly by `O(delta^sigma)`.
  Next: assemble those into the identity on `(0,inf)`, then iterate to `j` derivatives.
- 2026-07-27 — **(P2) integration by parts on `(0,inf)` — done.**  Appended to
  `HTGeometry/SmoothWeightMellin.lean`, axiom-clean:
  - `integrableOn_deriv_integrand`, `integral_deriv_integrand_eq` : the derivative integrand is
    integrable on the ray and its integral is just the one over `(delta, N+H]` for any
    `delta < N`.
  - `mellin_smoothWeight_byParts` : **`int_{(0,inf)} x^{s-1} w(x) dx =
    - int_{(0,inf)} w'(x) x^s/s dx` for every `Re s > 0`.**
  The boundary term at the origin is killed without any convergence machinery: for each
  `0 < delta < N` the exact identity reads
  `F + G = int_{(0,delta]} x^{s-1} w - delta^s/s`, whose norm is at most
  `delta^sigma (1/sigma + 1/‖s‖)` by the explicit bound proved earlier.  Choosing
  `delta = min(N/2, (eps/C)^{1/sigma})` makes that at most `eps`, so `‖F+G‖ <= 0` by
  `le_of_forall_pos_le_add`.  No filter limits, no dominated convergence — the whole passage is a
  single explicit estimate.
  Next: iterate this identity `j` times (the same lemma applies to `w'` in place of `w` after
  shifting `s`), then combine with the `H^{-j}` derivative bounds for the decay
  `|W(sigma+it)| = O(N^sigma (N/(H|t|))^{j-1}/|t|)`.
- 2026-07-27 — **(P2) the iteration step.**  Appended to `HTGeometry/SmoothWeightMellin.lean`,
  axiom-clean: `intervalIntegral_byParts_of_vanishing` — for `v` of class `C^2` on `[a,b]` with
  `0 < a` and `v a = v b = 0`,
  `int_a^b v(x) x^{s-1} dx = - int_a^b v'(x) x^s/s dx`, with **no boundary terms at all**.
  This is what makes the iteration uniform.  The first integration by parts (already proved) is
  special: `w` equals `1` near the origin, so it leaves the term `-delta^s/s`, which needed the
  explicit `delta -> 0` estimate.  Every subsequent step acts on `w'`, `w''`, ... , all of which
  vanish at both ends of any interval containing `[N, N+H]` — so from the second step on the
  identity is exact with no limit and no error term.  Choosing the right endpoint strictly beyond
  `N+H` (rather than at `N+H`) also sidesteps the one-sided-derivative edge case at the support
  boundary.
  Applying it once more to `w'` on `[N/2, N+H+1]` at exponent `s+1` gives
  `W(s) = (s(s+1))^{-1} int w''(x) x^{s+1} dx`, hence `|W(sigma+it)| = O(|t|^{-2})` — already enough
  for absolute convergence of a vertical integral against a bounded factor.  For `1/L`, which grows
  like `|t|^A`, the same step is iterated `j > A+1` times.
  Next: the general `j`-fold form and the resulting decay estimate, completing (P2).
- 2026-07-27 — **(P2) the `j`-fold integration by parts — done.**  Appended to
  `HTGeometry/SmoothWeightMellin.lean`, axiom-clean:
  - `contDiff_top_iteratedDeriv` : iterated derivatives of a smooth function are smooth
    (induction on `iteratedDeriv_succ` plus `ContDiff.deriv'`; mathlib has no direct lemma).
  - `intervalIntegral_byParts_iterate` : **for `v` smooth with all derivatives vanishing at both
    endpoints and `0 < a`,
    `int_a^b v(x) x^{s-1} dx = (-1)^j (prod_{i<j} (s+i))^{-1} int_a^b v^{(j)}(x) x^{s+j-1} dx`**
    for every `j`, by induction on the boundary-free step proved last turn.
  The product `prod_{i<j}(s+i)` is exactly the factor that supplies the decay: on the line
  `Re s = sigma` its modulus is at least `|t|^j`, so combined with the `H^{-j}` bounds on `v^{(j)}`
  the Mellin transform of the cutoff decays like `(N/(H|t|))^{j}` — arbitrarily fast in `|t|` at the
  cost of powers of `N/H`.  Each factor `s+i` is nonzero because `Re s > 0` and `i >= 0`, so no
  case analysis on `j` is needed.
  This completes the analytic core of (P2).  What remains there is only to package the bound:
  combine with `exists_bound_iteratedDeriv_smoothWeight` and estimate the finite integral.
- 2026-07-27 — **(P2) the hypotheses of the `j`-fold identity, discharged for the cutoff.**
  Appended to `HTGeometry/SmoothWeightMellin.lean`, axiom-clean:
  `iteratedDeriv_smoothWeight_eq_zero_of_lt` and `..._of_gt` (every derivative of positive order
  vanishes off `[N, N+H]`), `iteratedDeriv_deriv_smoothWeight_vanishing` (via `iteratedDeriv_succ'`,
  all derivatives of `w'` vanish at any endpoints straddling the support — the `i = 0` case included,
  which is why the iteration is applied to `w'` and not to `w`), and `contDiff_deriv_smoothWeight`.
  With these, `intervalIntegral_byParts_iterate` applies to `v = w'` on `[N/2, N+H+1]` with no
  further conditions.  Note the choice of interval: the left end is strictly inside `x < N` and the
  right end strictly beyond `N+H`, so both endpoint conditions hold on the nose and the
  one-sided-derivative questions at the exact support boundary never arise.
  What is left in (P2) is arithmetic packaging: chain
  `mellin_smoothWeight_byParts` -> `integral_deriv_integrand_eq` -> `intervalIntegral_byParts_iterate`,
  bound the finite integral by `(b-a) sup|w^{(j+1)}| b^{sigma+j}`, and feed in
  `exists_bound_iteratedDeriv_smoothWeight` to get
  `‖s‖ prod_{i<j} ‖s+1+i‖ ‖W(s)‖ <= C(j,N,H,sigma_max)`.
- 2026-07-27 — **(P2) the `j`-fold form of the cutoff's Mellin transform.**  Appended to
  `HTGeometry/SmoothWeightMellin.lean`, axiom-clean:
  - `integral_deriv_integrand_eq'` : the derivative integral over `(0,inf)` equals the one over any
    interval `[N/2, b]` with `b > N+H`.
  - `norm_mellin_smoothWeight_mul_eq` : **`‖s‖ (prod_{i<j} ‖s+1+i‖) ‖W(s)‖ =
    ‖int_{N/2}^{N+H+1} w^{(j+1)}(x) x^{s+j} dx‖`** for every `Re s > 0` and every `j`.
  An equality, not an estimate: the chain
  `mellin_smoothWeight_byParts` -> `integral_deriv_integrand_eq'` -> `intervalIntegral_byParts_iterate`
  produces exactly the factor `s prod_{i<j}(s+1+i)`, and taking norms turns the division into the
  stated identity.  Each factor is nonzero because `Re s > 0`.
  Only the last arithmetic step of (P2) is now left: bound the right-hand side by
  `(b-a) sup|w^{(j+1)}| b^{sigma+j}` and substitute
  `exists_bound_iteratedDeriv_smoothWeight` (`sup|w^{(j+1)}| <= C_{j+1}/H^{j+1}`), giving
  `‖W(sigma+it)‖ = O((N/(H|t|))^{j})` — the decay the contour shift needs.
- 2026-07-27 — **(P2) complete.**  Appended to `HTGeometry/SmoothWeightMellin.lean`, axiom-clean:
  `exists_bound_mellin_smoothWeight` — for every order `j` and every `sigma_max` there is a
  constant `C` with
  `‖s‖ (prod_{i<j} ‖s+1+i‖) ‖W(s)‖ <= C` on the strip `0 < Re s <= sigma_max`,
  where `C = (N+H+1-N/2) (C_{j+1}/H^{j+1}) (N+H+1)^{sigma_max+j}`.
  Since each `‖s+1+i‖ >= |Im s|`, the left side is at least `|t|^{j+1} ‖W(s)‖`, so this is decay of
  order `j+1` in `|t|` with the constant scaling as `H^{-(j+1)}` — exactly the tradeoff the plan
  called for: **arbitrarily fast decay in `|t|`, bought with powers of `1/H`.**
  That closes step (P2) of the smoothed-Perron programme.  Steps (P1) and (P2) are now done:
  the cutoff exists with the right derivative scaling, and its Mellin transform converges on
  `Re s > 0` and decays faster than any fixed power of `|t|`.
  Remaining: (P3) `sum_n a_n w(n) = (1/2 pi i) int F(s) W(s) ds` by Fubini; (P4) the line shift from
  `Re s = c > 1` to `Re s = Theta_chi + eps` via
  `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`; (P5) the shifted estimate;
  (P6) `|M_chi(N) - sum a_n w(n)| <= H` and the choice `H = N^{Theta+eps}`.
- 2026-07-27 — **(P6) done.**  New module `HTGeometry/SmoothWeightSum.lean`, axiom-clean, wired
  into the umbrella:
  `norm_weighted_sub_partialSum_le` — for unit-bounded coefficients `a`,
  `‖sum_{n<m} a_n w(n) - sum_{n<=K} a_n‖ <= H + 1` whenever `K + H <= m`.
  Proof: the two sums agree term by term on `n <= K` (`smoothWeight_eq_one`), the tail terms
  vanish once `n >= K + 1 + ceil H` (`smoothWeight_eq_zero`), and the surviving block has at most
  `ceil H < H + 1` terms, each of norm `<= 1`.
  So the **elementary half of the smoothed-Perron argument is complete**: replacing the sharp
  cutoff by the smooth one costs `O(H)`.  Combined with (P2), choosing `H = N^{Theta+eps}` balances
  the smoothing error against the analytic one.
  Status of the programme: (P1) cutoff ✓, (P2) Mellin decay ✓, (P6) smoothing error ✓.
  Left: (P3) Fubini, (P4) contour shift, (P5) the shifted estimate.
- 2026-07-27 — **Mellin inversion for the cutoff — the pivot of the whole Perron route.**
  New module `HTGeometry/SmoothWeightInversion.lean`, axiom-clean, wired into the umbrella.
  Mathlib has `mellinInv_mellin_eq` (inversion via Fourier inversion); its one hard hypothesis is
  absolute convergence of the vertical integral, and **that is precisely what (P2) supplies**:
  - `exists_bound_mellin_smoothWeight_line` : on `Re s = sigma > 0`, taking `j = 1` in the
    integration-by-parts bound gives `‖s‖ ‖s+1‖ ‖W(s)‖ <= C`, and since `‖s+1‖ >= ‖s‖` and
    `‖s‖^2 = sigma^2 + y^2`, this is **`‖W(sigma+iy)‖ <= C/(sigma^2+y^2) <= (C/m)(1+y^2)^{-1}`**
    with `m = min(sigma^2, 1)`.
  - `verticalIntegrable_mellin_smoothWeight` : hence `VerticalIntegrable (mellin w) sigma`,
    dominating by `integrable_inv_one_add_sq`.
  - `differentiableAt_mellin_smoothWeight` / `continuous_mellin_smoothWeight_line` : holomorphy of
    `W` on `Re s > 0` via `mellin_differentiableAt_of_isBigO_rpow`, with the two `IsBigO` inputs
    supplied by `smoothWeight_eq_zero` (at infinity) and `smoothWeight_le_one` (at the origin).
  - **`mellinInv_mellin_smoothWeight`** : `mellinInv sigma (mellin w) x = w x` for all `x > 0` and
    all `sigma > 0`.
  This is the inversion formula the Perron argument runs on: `w(n) = (1/2 pi) int x^{-(sigma+iy)}
  W(sigma+iy) dy`.  With it, (P3) reduces to a Fubini interchange between the `n`-sum and the
  `y`-integral, both now known to converge absolutely.
- 2026-07-27 — **(P3) done: the smoothed Perron formula.**  New module
  `HTGeometry/SmoothWeightPerron.lean`, axiom-clean, wired into the umbrella:
  **`tsum_mul_smoothWeight_eq_integral`** — for `‖a_n‖ <= 1`, `a_0 = 0` and any `sigma > 1`,
  `2 pi * sum_n a_n w(n) = int_R (sum_n a_n n^{-(sigma+iy)}) W(sigma+iy) dy`.
  Supporting: `norm_natCast_cpow_neg_line`, `integrable_perron_term` (each term dominated by
  `n^{-sigma} C (1+y^2)^{-1}`), `integral_perron_term` (each term integrates to `2 pi a_n w(n)`,
  i.e. Mellin inversion evaluated at `x = n`).
  The interchange is `hasSum_integral_of_summable_integral_norm`, justified by
  `sum_n int ‖a_n n^{-(sigma+iy)} W‖ <= (sum_n n^{-sigma}) int ‖W‖ < inf`, which needs exactly
  `sigma > 1` on the left factor and the quadratic decay of `W` on the right.
  Programme status: (P1) ✓, (P2) ✓, (P3) ✓, (P6) ✓.  Left: (P4) the contour shift from
  `Re s = sigma > 1` to `Re s = Theta_chi + eps`, and (P5) the estimate on the shifted line.
- 2026-07-27 — **(P4) engine built.**  New module `HTGeometry/VerticalContourShift.lean`,
  axiom-clean, wired into the umbrella.  The corpus only had an AFE-zeta-specific contour shift
  (`smoothAFEZetaMellin_infinite_contour_shift_line_of_horizontal_tendsto`); this is the general,
  function-agnostic version:
  - `verticalStrip c d`, `mem_verticalStrip`, `rect_subset_verticalStrip`.
  - **`integral_vertical_line_eq_of_horizontal_tendsto`** — if `G` is holomorphic on the closed
    strip `c <= Re s <= d`, integrable on both edges, and the two horizontal edge integrals over
    `[c,d]` tend to `0` as the height goes to infinity, then
    `int_R G(d+iy) dy = int_R G(c+iy) dy`.
  Proof: `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` on `[c,d] x [-T,T]`, then
  `T -> inf`; the vertical sides converge by `intervalIntegral_tendsto_integral` and the horizontal
  ones vanish by hypothesis, leaving `I (A - B) = 0`.
  This is reusable infrastructure for every Perron/Mellin shift in the corpus, not just this card.
  What remains for the card's (P4) is the three inputs at `G = F W`: holomorphy on
  `Theta_chi + eps <= Re s <= sigma` (from `LFunction_ne_zero_of_zeroAbscissa_lt`), edge
  integrability, and horizontal decay.
