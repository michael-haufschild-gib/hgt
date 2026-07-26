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
