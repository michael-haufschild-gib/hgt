# Theta likelihood square-gap nondivisibility

- **ID:** theta-likelihood-square-gap-nondivisibility
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Source:** `docs/handover/connes.md` §§13–18
- **Statement:** Every normalized fixed-measure theta likelihood law on the intrinsic half-line
  \(B>0\) has atoms at \(0\) and \(3\), no atom at \(6=3+3\), and therefore is neither infinitely
  divisible nor a generalized gamma convolution.

Labels: `[PAPER-PROVED] [LEAN-SOURCE-PREMISE] [NO-GO] [POSITIVE-SURVIVOR]`
`[NOVELTY-UNVERIFIED] [NOT-RH]`

## Goal

Decide whether the fixed modular-seam likelihood measure from
`ThetaCuspLikelihoodModularSeam.lean` can be exponentiated into a Lévy/Thorin/subordinator
scattering carrier. This is a source-structure question, not an estimate and not an RH-equivalent
criterion.

## Gates

- [x] 0 → 1: exact source law already available; independent-increment route identified
- [x] 1 → 2: complete paper proof below; standard parent theorem cited explicitly
- [x] 2 → 3: full infinite-divisibility implication formalized in Lean (unconditionally; the
  Steutel--van Harn classification turned out to be unnecessary for this carrier)
- [ ] 3 → 4: independent novelty review and publication packaging

## Exact theorem

For \(B>0\), let

\[
d\nu(t)=\sum_{n\ge2}e^{-3(n^2-1)/2}
\left[n^4\delta_{n^2-1}
+\frac32n^2(n^2-1)\mathbf 1_{(n^2-1,\infty)}(t)\,dt\right],
\]

\[
Z(B)=1+\int_0^\infty e^{-Bt}\,d\nu(t),
\qquad
dP_B(t)=\frac{\delta_0(dt)+e^{-Bt}d\nu(t)}{Z(B)}.
\]

Then:

1. \(P_B\) is a probability law on \([0,\infty)\).
2. \(P_B\{0\}>0\), \(P_B\{3\}>0\), and \(P_B\{6\}=0\).
3. The pair law satisfies \((P_B*P_B)\{6\}>0\): the two-particle sector creates an atom absent
   from the one-particle carrier.
4. The atom support
   \(A(P_B)=\{t:P_B\{t\}>0\}\) is not closed under addition.
5. \(P_B\) is not infinitely divisible.
6. Hence \(P_B\) is not a generalized gamma convolution and cannot be a marginal of a Thorin
   subordinator.

The conclusion holds for every \(B>0\), not only at the modular seam
\(B_0=\pi-3/2\).

## Proof

### 1. Probability normalization

The fixed-measure likelihood theorem gives

\[
\int e^{-Bt}\,d\nu(t)=L(B)<\infty
\]

for every \(B>0\). Therefore \(0<Z(B)=1+L(B)<\infty\), and \(P_B\) is a probability law supported
on \([0,\infty)\).

### 2. Exact atoms

The added \(\delta_0\) gives \(P_B\{0\}=Z(B)^{-1}>0\). Every component of \(\nu\) has one Dirac
mass at the square gap \(n^2-1\ge3\) and an atomless Lebesgue ray. Thus the only contribution at
\(3\) is the \(n=2\) Dirac mass:

\[
P_B\{3\}=\frac{e^{-3B}e^{-9/2}2^4}{Z(B)}>0.
\]

There is no integer \(n\ge2\) with \(n^2-1=6\): \(n=2\) gives \(3\), while \(n\ge3\) gives at
least \(8\). Lebesgue rays charge no singleton, so \(P_B\{6\}=0\). Consequently
\(3\in A(P_B)\) but \(3+3\notin A(P_B)\).

Nevertheless the product atom \((3,3)\) has positive \(P_B\otimes P_B\)-mass and addition maps it
to \(6\). Hence

\[
(P_B*P_B)\{6\}\ge P_B\{3\}^2>0.
\]

This is not merely a missing closure law: convolution produces a genuinely new two-particle
spectral atom.

### 3. Compound-Poisson atom closure

Let \(P\) be compound Poisson with intensity \(\lambda>0\) and jump law \(Q\):

\[
P=e^{-\lambda}\sum_{m\ge0}\frac{\lambda^m}{m!}Q^{*m}.
\]

Its atom support is additively closed. Indeed, if \(P\{x\}>0\), positivity of the series gives an
\(m\) with \(Q^{*m}\{x\}>0\). For finite Borel measures, an atom of a convolution is a sum of
atoms: from

\[
(\mu*\eta)\{x\}=\int \eta\{x-y\}\,d\mu(y),
\]

the integrand is supported on the countable atom set of \(\eta\); a positive integral therefore
contains \(y\) with \(\mu\{y\}>0\) and \(\eta\{x-y\}>0\). Iteration writes \(x\) as a sum of \(m\)
atoms of \(Q\). Do the same for an atom \(y\) using \(n\) jumps. Concatenating the two tuples gives
\(Q^{*(m+n)}\{x+y\}>0\), hence \(P\{x+y\}>0\).

The case \(\lambda=0\) is \(\delta_0\), whose atom support is also additively closed.

### 4. Infinite-divisibility contradiction

A standard classification theorem for probability laws on \([0,\infty)\) says: an infinitely
divisible law with infimum of support \(0\) has a discontinuity (an atom) iff it is compound
Poisson. See Steutel–van Harn, *Infinite Divisibility of Probability Distributions on the Real
Line*, Chapter III, Theorem 4.15. Since \(P_B\{0\}>0\), infinite divisibility of \(P_B\) would make
it compound Poisson. The preceding lemma would then force

\[
P_B\{3\}>0 \Longrightarrow P_B\{6\}>0,
\]

contradicting the exact source calculation. Thus \(P_B\) is not infinitely divisible. Every GGC
law is infinitely divisible, so the GGC/Thorin conclusions follow.

## Lean certificate

Modules:

`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspLikelihoodAtomicNondivisibility.lean`

`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspLikelihoodProbabilityNondivisibility.lean`

Lean proves exactly:

- the higher tilted mass equals the spectral response and the complete carrier mass equals `Z(B)`;
- the literal normalized carrier `P_B = Z(B)⁻¹ • (δ₀ + exp(-Bt)ν)` is a probability measure
  carried by `[0, ∞)`;
- singleton formula for every atom-ray carrier;
- exact normalized masses at \(0,3,6\), including
  `P_B{3} = Z(B)⁻¹ exp(-3B) exp(-9/2) 2⁴`;
- preservation under every real exponential tilt;
- failure of additive atom closure;
- persistence under every nonzero scalar normalization.
- birth of a nonzero self-convolution atom at \(6\).
- unconditional failure of infinite divisibility for the normalized probability law;
- exclusion from every concrete GGC or Thorin-marginal law class carrying the standard defining
  inclusion into infinitely divisible laws.

Principal declarations:

- `thetaCuspHigherLikelihoodSpectralMeasure_singleton_three`
- `thetaCuspHigherLikelihoodSpectralMeasure_singleton_six`
- `thetaCuspLikelihoodSeamTiltedMeasure_singleton_three_ne_zero`
- `not_additivelyClosedAtomSupport_thetaCuspLikelihoodSeamTiltedMeasure`
- `not_additivelyClosedAtomSupport_smul_thetaCuspLikelihoodSeamTiltedMeasure`
- `thetaCuspLikelihoodSeamTiltedMeasure_selfConv_singleton_six_ne_zero`
- `thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure`
- `ae_nonneg_thetaCuspLikelihoodProbabilityMeasure`
- `thetaCuspLikelihoodProbabilityMeasure_singleton_three_explicit`
- `thetaCuspLikelihoodProbabilityMeasure_selfConv_singleton_six_ne_zero`
- `thetaCuspLikelihoodProbabilityMeasure_not_infinitelyDivisible`
- `thetaCuspLikelihoodProbabilityMeasure_not_generalizedGammaConvolution`
- `thetaCuspLikelihoodProbabilityMeasure_not_thorinSubordinatorMarginal`

The full nondivisibility corollary is also formalized, and unconditionally: the Steutel--van Harn
classification is not needed for this carrier, because its atomic support already forbids a
convolution square root.  See `not_infinitelyDivisible_of_atomic_gap` and
`thetaCuspLikelihoodSeamTiltedMeasure_not_infinitelyDivisible`.

## Hostile audit

1. **Topological support is irrelevant.** The first ray makes every point above \(3\) belong to the
   topological support, including \(6\). The contradiction concerns singleton mass, not support.
2. **Continuous jumps cannot hide the defect.** An atom of a finite convolution can only be
   assembled from atoms of its factors; the countability argument above excludes a continuous
   contribution to a singleton.
3. **Tilt cannot remove or create these atoms.** \(e^{-Bt}\) is strictly positive at every finite
   \(t\); normalization is also strictly positive.
4. **No shifted compound-Poisson escape.** \(P_B\) is supported on \([0,\infty)\), has infimum
   support \(0\), and already charges \(0\). The classification has zero drift/shift here.
5. **No contradiction with Polson's Thorin tiers.** Polson's incomplete-gamma/zero-based GGC
   objects are different probability laws. This theorem forbids exponentiating this specific
   fixed likelihood carrier \(\delta_0+e^{-Bt}\nu\); it does not refute other Xi-related GGC
   representations.

## No-go closure

- **Exact killing theorem/mechanism:** square-gap atom support fails the mandatory
  compound-Poisson closure law at \(3+3=6\).
- **Strongest positive survivor:** the first atomic semigroup defect
  \[
  3\in A(P_B),\qquad 6\notin A(P_B),\qquad 6\in A(P_B*P_B)
  \]
  is an exact, tilt-invariant arithmetic signature of the completed source. Pairing creates a
  new latent sector absent from the one-particle law.
- **New insight:** fixed latent scattering cannot be realized by independent increments, a Lévy
  exponent, or a Thorin carrier. Any source-side phase producer must retain coherent off-diagonal
  interaction among square-gap atoms and Lebesgue rays; exponentiating channels independently
  destroys the arithmetic incidence that distinguishes the actual theta source. The missing
  phase orientation must first be sought in this irreducible two-particle sector, not in another
  one-particle MLR observable.
- **Status:** paper proof and Lean formalization dependency-closed and unconditional; external
  priority audit incomplete.

## Literature and novelty audit

- F. W. Steutel and K. van Harn, *Infinite Divisibility of Probability Distributions on the Real
  Line* (2004), Chapter III, Theorem 4.15 and Chapter II/III compound-Poisson material:
  https://www.routledge.com/Infinite-Divisibility-of-Probability-Distributions-on-the-Real-Line/Steutel-Harn/p/book/9780824707242
- L. F. James, B. Roynette, M. Yor, “Generalized Gamma Convolutions, Dirichlet means, Thorin
  measures, with explicit examples” (2008): https://arxiv.org/abs/0708.3932
- N. G. Polson, “Incomplete Gamma Representations of the Riemann Xi Function: a Thorin Bernstein
  Framework” (2026): https://ssrn.com/abstract=6954119

Targeted searches found Xi/GGC constructions and general infinite-divisibility classifications,
but no source treating this fixed theta likelihood law or its \(3+3\notin A(P_B)\) obstruction.
That is insufficient for a priority claim. Label remains `[NOVELTY-UNVERIFIED]`.

## Log

- 2026-07-21 — derived exact square-gap obstruction; completed paper proof; formalized
  theta-specific atom-support theorem.

## Lean progress

- 2026-07-25 — **Correction + reusable-lemma extraction.**  The theta-specific atom content of this
  card was **already** fully formalized in `RHTower/ThetaCusp/ThetaCuspLikelihoodAtomicNondivisibility.lean`
  (`thetaCuspLikelihoodSeamTiltedMeasure` = `P_B`, its singleton masses at `0,3,6`,
  `not_additivelyClosedAtomSupport_...` on the actual measure, and
  `thetaCuspLikelihoodSeamTiltedMeasure_selfConv_singleton_six_ne_zero`).  An abstract-atom-set
  restatement I had briefly added (`ThetaSquareGapAtomNonClosure.lean`) duplicated that weaker and was
  **removed**.  Net kept contribution: the one genuinely reusable general lemma, now placed in the
  existing module and used to simplify its self-convolution proof (axioms
  `[propext, Classical.choice, Quot.sound]`):
  * `measure_singleton_le_conv` — **atoms add under convolution**: `μ{a}·ν{b} ≤ (μ ∗ ν){a+b}` for any
    measures on an additive monoid (`Measure.conv = map (+) (μ.prod ν)`, `Measure.prod_prod`,
    singleton-`⊆`-preimage monotonicity).  `thetaCuspLikelihoodSeamTiltedMeasure_selfConv_singleton_six_ne_zero`
    now discharges via `measure_singleton_le_conv μ μ 3 3` (step 3) instead of an inline argument.
  **Still open for gate `2 → 3`** (unchanged): the classical parent "an infinitely divisible law on
  `[0,∞)` with an atom at `0` is compound Poisson, whose atom support is additively closed"
  (Steutel--van Harn Ch. III Thm 4.15) is absent from mathlib.  The theta-specific premise is Lean-done;
  only this general probability parent remains.
- 2026-07-25 — **`n`-fold convolution atom bound formalized (unconditional, reusable)**, new general
  module `HTGeometry/ConvolutionAtomBounds.lean` (axioms `[propext, Classical.choice, Quot.sound]`);
  `measure_singleton_le_conv` was **moved here** from the theta module (now imported, no duplication):
  * `convPow μ n` — the `n`-fold self-convolution `μ^{∗n}` (with `μ^{∗0} = δ₀`), `SFinite`-preserving
    (`sFinite_convPow`).
  * `prod_measure_singleton_le_convPow` — **atoms add under `n`-fold convolution**: if each `a i` is an
    atom of `μ`, then `∑ a i` is an atom of `μ^{∗n}` with mass `≥ ∏ μ{a i}` (induction on the binary
    `measure_singleton_le_conv`).
  This is exactly the "iterate ... writes `x` as a sum of `m` atoms" primitive of the card's step-3
  compound-Poisson atom-support closure — the general-probability parent that the open `2 → 3` gate
  still needs (its remaining piece is packaging the compound-Poisson series `e^{-λ}∑ λ^m/m! Q^{*m}`
  around this convolution-power atom bound, then the Steutel--van Harn ID ⟹ compound-Poisson step).
- 2026-07-25 — **Convolution-power atom semigroup formalized (unconditional)**, appended to
  `HTGeometry/ConvolutionAtomBounds.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `convPow_add` — `μ^{∗(m+n)} = μ^{∗m} ∗ μ^{∗n}` (convolution associativity + `δ₀` identity).
  * `convPow_singleton_add_ne_zero` — **atoms of convolution powers form an additive sub-semigroup**:
    `x` an atom of `μ^{∗m}` and `y` an atom of `μ^{∗n}` ⟹ `x+y` an atom of `μ^{∗(m+n)}`.
  This is exactly the card's step-3 "concatenate the two atom tuples to get `Q^{*(m+n)}{x+y} > 0`"
  conclusion, now fully general and unconditional.  With this, the compound-Poisson atom-support
  closure reduces to a single wrapping: `P = e^{-λ}∑_m (λ^m/m!) Q^{*m}` positive ⟹ some
  `Q^{*m}{x} > 0`, then `convPow_singleton_add_ne_zero`.  Only the `P` series-measure definition and
  the Steutel--van Harn `ID ⟹ compound Poisson` classification then remain for the `2 → 3` gate.
- 2026-07-25 — **Compound-Poisson atom-support closure formalized (unconditional)**, appended to
  `HTGeometry/ConvolutionAtomBounds.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `convPowMixture c μ` — a nonnegative-weighted mixture `∑_m c_m·μ^{∗m}` (`= Measure.sum`); with
    `c_m = e^{-λ}λ^m/m!` this is the compound Poisson law with jump distribution `μ`.
  * `convPowMixture_singleton` — `(∑_m c_m·μ^{∗m}){x} = ∑'_m c_m·μ^{∗m}{x}`.
  * `convPowMixture_singleton_add_ne_zero` — **step-3 in full: the atom support of every
    positive-weighted convolution-power mixture is additively closed** (`x, y` atoms ⟹ `x+y` atom):
    a positive tsum yields `m, n` with `μ^{∗m}{x}, μ^{∗n}{y} ≠ 0`, then
    `convPow_singleton_add_ne_zero` gives `μ^{∗(m+n)}{x+y} ≠ 0`, which bounds the `x+y` tsum below.
  **This completes the compound-Poisson side of the card's paper proof** (step 3, general form).  The
  only remaining input for the `2 → 3` gate is the classical Steutel--van Harn direction
  `ID + atom at 0 ⟹ compound Poisson` (still absent from mathlib).
- 2026-07-25 — **`P_B` is not a compound Poisson — connector formalized (unconditional)**, appended to
  `RHTower/ThetaCusp/ThetaCuspLikelihoodAtomicNondivisibility.lean` (axioms `[propext, Classical.choice,
  Quot.sound]`):
  * `thetaCuspLikelihoodSeamTiltedMeasure_not_convPowMixture` — **`P_B ≠ convPowMixture c Q`** for
    every positive-weight `c` and jump law `Q`: a compound-Poisson mixture has additively closed atom
    support (`convPowMixture_singleton_add_ne_zero`), but `P_B` does not
    (`not_additivelyClosedAtomSupport_...`).
  This connects the general compound-Poisson machinery to the specific theta carrier: **`P_B` is not a
  compound Poisson**, unconditionally.  The full `2 → 3` non-divisibility is now literally one step
  away — `P_B` infinitely divisible ⟹ (Steutel--van Harn, `ID + atom at 0 ⟹ compound Poisson`)
  ⟹ `P_B` is a compound Poisson ⟹ contradiction with this theorem.  Only the Steutel--van Harn
  classification (mathlib-absent) remains unformalized.
- 2026-07-25 — **`(2→3)` argument fully packaged; reusable ID infrastructure added (unconditional
  where noted)**.  New reusable infrastructure in `HTGeometry/ConvolutionAtomBounds.lean` (axioms
  `[propext, Classical.choice, Quot.sound]`; `InfinitelyDivisible` confirmed absent from mathlib):
  * `isProbabilityMeasure_convPow` — `μ^{∗n}` is a probability measure when `μ` is.
  * `InfinitelyDivisible μ := ∀ n>0, ∃ ν prob, μ = ν^{∗n}` — the infinite-divisibility predicate.
  * `IsCompoundPoissonMixture μ := ∃ c Q, (∀m, c m ≠ 0) ∧ SFinite Q ∧ μ = convPowMixture c Q`, with
    `IsCompoundPoissonMixture.singleton_add_ne_zero` (its atom support is additively closed).
  In `RHTower/ThetaCusp/ThetaCuspLikelihoodAtomicNondivisibility.lean`:
  * `thetaCuspLikelihoodSeamTiltedMeasure_not_compoundPoisson` — **`¬ IsCompoundPoissonMixture P_B`,
    unconditional** (existential form: `P_B` is not any compound Poisson mixture).
  * `thetaCuspLikelihoodSeamTiltedMeasure_not_infinitelyDivisible` — **`¬ InfinitelyDivisible P_B`
    given the Steutel--van Harn interface** `svh : InfinitelyDivisible P_B → IsCompoundPoissonMixture P_B`.
  This formalizes the card's `(2→3)` argument in full, with the *only* classical input — Steutel--van
  Harn `ID + atom at 0 ⟹ compound Poisson` — isolated as the explicit `svh` hypothesis (still absent
  from mathlib).  Everything else (`P_B` not compound Poisson) is unconditional Lean.
- 2026-07-25 — **Convolution distributes over `Measure.sum` (reusable, mathlib-gap)**, appended to
  `HTGeometry/ConvolutionAtomBounds.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `sum_conv` — `(∑_i f i) ∗ ν = ∑_i (f i ∗ ν)`.
  * `conv_sum` — `μ ∗ (∑_i f i) = ∑_i (μ ∗ f i)` (for `Countable ι`).
  These (from `Measure.prod_sum_left/right` + `Measure.map_sum`) are the interchange primitives absent
  from mathlib that a compound-Poisson **convolution semigroup** `compoundPoisson(λ₁)∗compoundPoisson(λ₂)
  = compoundPoisson(λ₁+λ₂)` needs (Cauchy product over the two Poisson series), hence the still-open
  *easy* half `compound Poisson ⟹ ID`.  They complete the reusable convolution-distributivity layer of
  the ID/compound-Poisson nucleus in `ConvolutionAtomBounds`.
- 2026-07-25 — **Convolution of convolution-power mixtures formalized (reusable)**, appended to
  `HTGeometry/ConvolutionAtomBounds.lean` (axioms `[propext, Classical.choice, Quot.sound]`; also
  promoted `sFinite_convPow` to an instance so mixture `SFinite` inference works):
  * `convPowMixture_conv` — **`(∑_m c₁_m Q^{∗m}) ∗ (∑_k c₂_k Q^{∗k}) = ∑_m ∑_k (c₁_m·c₂_k) Q^{∗(m+k)}`**
    (via `sum_conv` + `conv_sum` + scalar bilinearity `conv_smul_left/right` + `convPow_add`).
  This is the structural core of the compound-Poisson **convolution semigroup**: the resulting
  coefficient double sum is the Cauchy product of `c₁, c₂`.  For the Poisson weights the Cauchy product
  is the binomial `∑_{m+k=j}(e^{-a}a^m/m!)(e^{-b}b^k/k!) = e^{-(a+b)}(a+b)^j/j!`, giving
  `compoundPoisson(a) ∗ compoundPoisson(b) = compoundPoisson(a+b)` and hence `compound Poisson ⟹ ID`.
  Remaining for that easy half: the double-sum → antidiagonal Cauchy reindex of `Measure.sum` and the
  Poisson binomial identity.  (The card's actual gate still needs the hard Steutel--van Harn converse.)
- 2026-07-25 — **Poisson/exponential coefficient Cauchy product formalized (reusable)**, appended to
  `HTGeometry/ConvolutionAtomBounds.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `poisson_cauchy` — **`∑_{(m,k)∈antidiag j} (a^m/m!)(b^k/k!) = (a+b)^j/j!`** (the exponential
    generating-function product identity, via `add_pow` + `Nat.choose_mul_factorial_mul_factorial`).
  This is the **scalar** half of the compound-Poisson convolution semigroup — with the measure-level
  double sum `convPowMixture_conv`, it gives `compoundPoisson(a) ∗ compoundPoisson(b) =
  compoundPoisson(a+b)`, hence `compound Poisson ⟹ ID`.  The only remaining bridge is the measure-level
  antidiagonal Cauchy reindex of `Measure.sum` (mathlib lacks `sigmaAntidiagonalEquivProd`/`sum_sigma`,
  so it must be built from `Measure.sum_sum` + `Measure.sum_comp_equiv` + `Measure.sum_coe_finset`).
- 2026-07-25 — **Measure Cauchy-product primitives + full mixture convolution formula (reusable,
  mathlib-gap)**, appended to `HTGeometry/ConvolutionAtomBounds.lean` (axioms `[propext,
  Classical.choice, Quot.sound]`):
  * `measure_sum_sigma` — `Measure.sum` over a sigma type is the iterated sum (`Measure.sum_apply`
    + `ENNReal.tsum_sigma'`) — genuinely absent from mathlib.
  * `sigmaAntidiagEquiv` / `measure_sum_antidiagonal` — the antidiagonal Cauchy reindex for
    `Measure.sum`: `∑_{p:ℕ×ℕ} g p = ∑_j ∑_{p∈antidiag j} g p`.
  * `convPowMixture_conv_antidiagonal` — **`(∑_m c₁_m Q^{∗m}) ∗ (∑_k c₂_k Q^{∗k}) =
    ∑_j (∑_{p∈antidiag j} c₁_{p.1}·c₂_{p.2}) Q^{∗j}`**: the convolution of two mixtures is a mixture
    whose coefficient sequence is the Cauchy product — the complete compound-Poisson
    convolution-semigroup structural formula.
  With `poisson_cauchy` (the Poisson coefficient Cauchy identity), this gives
  `compoundPoisson(a) ∗ compoundPoisson(b) = compoundPoisson(a+b)` once the coefficients are cast to
  `ℝ≥0∞`, hence `compound Poisson ⟹ ID` (the easy half of the ID/compound-Poisson equivalence).
- 2026-07-25 — **Compound Poisson convolution semigroup formalized (unconditional)**, appended to
  `HTGeometry/ConvolutionAtomBounds.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `compoundPoisson lam Q := convPowMixture (fun m => ofReal(e^{-lam} lam^m/m!)) Q` — the compound
    Poisson law with intensity `lam` and jump law `Q`.
  * `compoundPoisson_coeff_cauchy` — the `ℝ≥0∞` coefficient Cauchy identity (from `poisson_cauchy`
    + `exp(-a)exp(-b)=exp(-(a+b))` + `ENNReal.ofReal_mul/ofReal_sum`).
  * `compoundPoisson_conv` — **`compoundPoisson(a) ∗ compoundPoisson(b) = compoundPoisson(a+b)`** for
    `a, b ≥ 0`, via `convPowMixture_conv_antidiagonal` + the coefficient identity.
  This is the compound-Poisson **convolution semigroup**, unconditional.  The immediate corollary
  `compound Poisson ⟹ ID` follows by iterating: `compoundPoisson(lam) = compoundPoisson(lam/n)^{∗n}`
  (`n`-fold semigroup), with `compoundPoisson(lam/n)` a probability measure.  This validates the entire
  ID/compound-Poisson nucleus (`ConvolutionAtomBounds` is now a self-contained Lévy-atom theory).
- 2026-07-25 — **`compound Poisson ⟹ infinitely divisible` fully formalized (unconditional)** — the
  easy half of the ID/compound-Poisson equivalence — in `HTGeometry/ConvolutionAtomBounds.lean`
  (axioms `[propext, Classical.choice, Quot.sound]`):
  * `compoundPoisson_zero` — `compoundPoisson 0 Q = δ₀`.
  * `convPow_compoundPoisson` — **`(compoundPoisson lam Q)^{∗n} = compoundPoisson (n·lam) Q`** (n-fold
    semigroup, induction on `compoundPoisson_conv`).
  * `isProbabilityMeasure_compoundPoisson` — `compoundPoisson lam Q` is a probability measure for
    `lam ≥ 0` (its Poisson weights sum to `1` via the exponential series `∑ lam^m/m! = exp lam`).
  * `infinitelyDivisible_compoundPoisson` — **`InfinitelyDivisible (compoundPoisson lam Q)`**: for each
    `n`, `compoundPoisson lam Q = (compoundPoisson (lam/n) Q)^{∗n}` with `compoundPoisson (lam/n) Q` a
    probability measure.
  The whole ID/compound-Poisson nucleus (`ConvolutionAtomBounds`) is now demonstrably non-vacuous and
  correct.  The theta card's `2 → 3` gate still needs the *converse* (Steutel--van Harn: `ID + atom at
  0 ⟹ compound Poisson`), but the framework it plugs into is fully validated end to end.
- 2026-07-25 — **Infinite-divisibility closure + `δ₀` example (reusable ID-theory)**, appended to
  `HTGeometry/ConvolutionAtomBounds.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `convPow_conv` — `(μ ∗ ν)^{∗n} = μ^{∗n} ∗ ν^{∗n}` on a commutative monoid (via `conv_comm` +
    `conv_assoc`).
  * `InfinitelyDivisible.conv` — **infinite divisibility is closed under convolution**.
  * `convPow_dirac_zero` / `infinitelyDivisible_dirac_zero` — `δ₀^{∗n} = δ₀`, so `δ₀` is ID.
  These round out the reusable ID-theory library.  The whole `ConvolutionAtomBounds` module is now a
  self-contained Lévy/infinite-divisibility contribution (absent from mathlib): convolution
  powers/mixtures, atom-support closure, the ID and compound-Poisson-mixture predicates, convolution
  distributivity, the measure Cauchy product, the compound-Poisson semigroup, `compound Poisson ⟹ ID`,
  and now ID closure under convolution.  The theta `2 → 3` gate awaits only the hard Steutel--van Harn
  converse (Lévy--Khintchine level).
- 2026-07-25 — **Generating-function calculus for convolutions (reusable Laplace/MGF layer)**,
  appended to `HTGeometry/ConvolutionAtomBounds.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `lintegral_conv_of_multiplicative` — for any measurable multiplicative kernel
    `f (x+y) = f x · f y` (Laplace `exp(-s·)`, MGF, character), `∫⁻ f d(μ ∗ ν) = ∫⁻f dμ · ∫⁻f dν`.
  * `lintegral_convPow_of_multiplicative` — `∫⁻ f d(μ^{∗n}) = (∫⁻ f dμ)^n` (transform of the
    `n`-th convolution power is the `n`-th power).
  This is exactly the transform layer a Laplace-transform proof of the Steutel--van Harn converse
  (`ID + atom at 0 ⟹ compound Poisson`, the theta `2 → 3` gate) is built on: the ID hypothesis gives
  `Laplace(P) = Laplace(Q_n)^n`, and Bernstein-function structure of `-log Laplace` finishes it.  The
  transform multiplicativity is now unconditional Lean; the remaining input is the Bernstein/Lévy–
  Khintchine representation.
- 2026-07-25 — **Laplace transform of a measure + convolution law** (new module
  `HTGeometry/LaplaceTransformConvolution.lean`, axioms `[propext, Classical.choice, Quot.sound]`):
  * `laplace μ s := ∫⁻ x, exp(-(s x)) dμ` — the Laplace–Stieltjes transform, valued in `ℝ≥0∞`.
  * `laplace_conv` — `laplace (μ ∗ ν) s = laplace μ s · laplace ν s` (convolution ↦ product), a
    direct specialization of the abstract multiplicative-kernel lemma to the exponential kernel.
  * `laplace_convPow` — `laplace (μ^{∗n}) s = (laplace μ s)^n`.
  * `laplace_dirac_zero` — `laplace δ₀ s = 1`.
  * `InfinitelyDivisible.exists_laplace_root` — **ID forces the Laplace transform to be a perfect
    `n`-th power at every `s` and every order `n`** (`∃ r, laplace μ s = r^n`), the transform-side
    skeleton of the Steutel–van Harn / Lévy–Khintchine analysis for the theta `2 → 3` gate.
  The transform layer is now a concrete Laplace transform (not just an abstract kernel), tying
  `InfinitelyDivisible` directly to a perfect-`n`-th-power structure on `ℝ≥0∞`.  Remaining input for
  the gate: the Bernstein-function representation of `-log laplace` (Lévy–Khintchine on `[0,∞)`).
- 2026-07-25 — **Laplace-transform domain lemmas** (appended to
  `HTGeometry/LaplaceTransformConvolution.lean`, axioms `[propext, Classical.choice, Quot.sound]`):
  `laplace_dirac` (`laplace δₐ s = exp(-(s a))`), `laplace_zero` (`laplace μ 0 = μ univ`),
  `laplace_zero_prob` (`= 1`), `laplace_le_one` (probability measure on `[0,∞)`, `s ≥ 0 ⟹ ≤ 1`),
  `laplace_antitone` (antitone in `s` on the half line), `laplace_pos` (strictly positive at every
  argument — the everywhere-positive exponential kernel).  These are the boundedness/monotonicity/
  positivity constraints that pin the `n`-th roots produced by `InfinitelyDivisible.exists_laplace_root`
  into `(0,1]` and let one pass to `-log laplace` — the domain backbone for the Bernstein-function
  (Lévy–Khintchine) step of the theta `2 → 3` gate.
- 2026-07-25 — **Cumulant (log-Laplace) layer** (appended to
  `HTGeometry/LaplaceTransformConvolution.lean`, axioms `[propext, Classical.choice, Quot.sound]`):
  `logLaplace μ s := -log (laplace μ s).toReal`, the additive/cumulant picture.
  * `logLaplace_zero_prob` (`= 0` at `s=0`), `logLaplace_nonneg` (`≥ 0` on `[0,∞)`, `s ≥ 0`).
  * `logLaplace_conv` — **additive under convolution** (probability measures, finite transform).
  * `InfinitelyDivisible.exists_logLaplace_root` — **ID makes the cumulant divisible by every `n`**:
    `∃ c, logLaplace μ s = n·c`, the additive Lévy shadow of `exists_laplace_root`, unconditional
    (via `-log(rⁿ) = n·(-log r)`).
  The cumulant is now a nonnegative, convolution-additive, infinitely-`n`-divisible function
  vanishing at `0` — precisely the shape of a Bernstein-function candidate.  Remaining input for the
  theta `2 → 3` gate: complete monotonicity of `s ↦ logLaplace μ s` (Bernstein/Lévy–Khintchine on `[0,∞)`).
- 2026-07-25 — **Compound Poisson cumulant computed in closed form — easy direction end-to-end on
  the transform side** (appended to `HTGeometry/LaplaceTransformConvolution.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`):
  * `laplace_convPowMixture` — `laplace(∑ₘ cₘ·Q^{∗m}) s = ∑ₘ cₘ·(laplace Q s)ᵐ` (reusable).
  * `tsum_ofReal_poisson_scaled` — the scaled real exp-series `∑ₘ e^{-λ}aᵐ/m!` lifted through
    `ENNReal.ofReal` equals `e^{-λ}·eᵃ`.
  * `laplace_compoundPoisson` — **`laplace(compoundPoisson λ Q) s = exp(λ·((laplace Q s)−1))`**.
  * `logLaplace_compoundPoisson` — **`logLaplace(compoundPoisson λ Q) s = λ·(1 − (laplace Q s))`**,
    the explicit closed-form compound-Poisson cumulant (a concrete Bernstein-type form: `λ` times
    `1 −` a completely monotone transform).
  * `logLaplace_compoundPoisson_nonneg` — that cumulant is `≥ 0` on the half line.
  This closes the **easy** half of the Steutel–van Harn equivalence entirely on the transform side:
  compound Poisson ⟹ explicit cumulant `λ(1−L̂)`.  The hard converse (ID + atom at 0 ⟹ that cumulant
  form, i.e. `−logLaplace` is Bernstein) remains the theta `2 → 3` analytic input.
- 2026-07-25 — **Atomic convolution infrastructure — foundation for discharging `svh`
  unconditionally** (appended to `HTGeometry/ConvolutionAtomBounds.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`):
  * `conv_singleton_eq_lintegral` — `(μ ∗ ν){z} = ∫⁻ x, ν{z − x} ∂μ` (singleton mass = fibre integral).
  * `countable_atoms` — the atom set `{x | ν{x} ≠ 0}` of a finite measure on `ℝ` is countable.
  * `conv_self_singleton_eq_zero_of_no_pair` — if `∀ x, ν{x} ≠ 0 → ν{z − x} = 0` (no atom pair sums
    to `z`) then `(ν ∗ ν){z} = 0`.
  **Route to unconditional non-divisibility** (no general Steutel–van Harn needed).  `P_B = δ₀ + tilted
  Σ δ_{n²−1}` is purely atomic on `{0,3,8,15,…} ⊆ [0,∞)`, min positive atom `3`, `6 ∉ supp`.  If
  `P_B = ν ∗ ν` (from `InfinitelyDivisible`, `n = 2`): (i) `ν` has no negative atoms — for `b < 0`,
  `ν{b}² ≤ (ν∗ν){2b} = P_B{2b} = 0`; (ii) `ν{0} ≠ 0` from `P_B{0} = ν{0}² ≠ 0`; (iii) `ν{3} = 0` from
  `ν{3}² ≤ P_B{6} = 0`; (iv) every `ν`-atom is a `P_B`-atom (`P_B{a} ≥ ν{0}·ν{a}`), so `ν`-atoms lie in
  `{0,3,8,…}`; hence no `ν`-atom pair sums to `3`, and `conv_self_singleton_eq_zero_of_no_pair` gives
  `P_B{3} = (ν∗ν){3} = 0`, contradicting `P_B{3} ≠ 0`.  Remaining to formalize: the two global support
  facts for `P_B` (`∀ x<0, P_B{x}=0`; `∀ x, 0<x<3 → P_B{x}=0`) and the assembly — then
  `thetaCuspLikelihoodSeamTiltedMeasure_not_infinitelyDivisible` becomes **unconditional** (drops `svh`).
- 2026-07-26 — **Gate `2 → 3` closed: non-divisibility is now UNCONDITIONAL.**  The Steutel--van Harn
  classification turned out to be *unnecessary* for this carrier, so the `svh` hypothesis is gone
  (axioms `[propext, Classical.choice, Quot.sound]` throughout).

  New general criterion in `HTGeometry/ConvolutionAtomBounds.lean`:
  * `not_infinitelyDivisible_of_atomic_gap` — a measure on `R` that charges no negative point,
    charges `0` and `a`, charges nothing strictly between `0` and `a`, and charges nothing at `2a`,
    is not infinitely divisible.  Proof: write `mu = nu * nu`.  No `nu`-atom is negative (its double
    would be a negative `mu`-atom); `nu` charges the origin (otherwise no atom pair reaches `0`);
    pairing against that origin atom makes every `nu`-atom a `mu`-atom, so `nu` charges nothing in
    `(0,a)`; and `nu{a} = 0` because `mu{2a} = 0`.  No pair of `nu`-atoms can then sum to `a`, so
    `conv_self_singleton_eq_zero_of_no_pair` forces `mu{a} = 0` -- contradiction.  (Positivity of `a`
    is not assumed; it follows.)

  New in `RHTower/ThetaCusp/ThetaCuspLikelihoodAtomicNondivisibility.lean`, giving the exact atomic support:
  * `three_le_thetaCuspLikelihoodGap_shift`, `thetaCuspHigherLikelihoodSpectralMeasure_singleton_eq_zero`,
    `thetaCuspLikelihoodSeamTiltedMeasure_singleton_eq_zero` — off the origin and the square gaps
    nothing is charged (the Lebesgue rays charge no singleton), hence
    `..._singleton_neg` (`P_B` lives on the half line) and `..._singleton_lt_three` (`3` is the first
    positive atom).
  * `not_infinitelyDivisible_smul_thetaCuspLikelihoodSeamTiltedMeasure` — **`c . P_B` is not
    infinitely divisible for every nonzero `c`**, in particular for the normalized probability law.
  * `thetaCuspLikelihoodSeamTiltedMeasure_not_infinitelyDivisible` — the same for `P_B` itself; the
    old `svh` hypothesis is **removed**, this now discharges it.

  Why the classification was avoidable: Steutel--van Harn is needed when one only knows the *atom
  support* fails to be additively closed.  Here we know more -- `P_B` is supported on `[0,infinity)`
  with first positive atom `3` -- and that pins any convolution square root tightly enough on its own.
  The compound-Poisson layer built earlier is not wasted: it still gives the independent statement
  `P_B` is not a compound Poisson mixture, and the ID/Laplace/cumulant infrastructure remains general.

  The carrier-level nondivisibility is unconditional.  A later audit identified one remaining
  formal mismatch: this module called the unnormalized seam carrier `P_B`, whereas the paper's
  `P_B` is the literal probability normalization.  That mismatch is closed below.

- 2026-08-01 — **Normalized probability law and items 1--6 formalized exactly.**  Added
  `RHTower/ThetaCusp/ThetaCuspLikelihoodProbabilityNondivisibility.lean`, proving the tilted mass and seam
  mass formulas, defining the literal `P_B`, proving its probability and half-line support laws,
  transferring the exact `0,3,6` atom formulas, proving the normalized self-convolution atom at
  `6`, additive nonclosure, and unconditional non-infinite-divisibility.  The GGC and
  Thorin-subordinator conclusions are formalized uniformly for every concrete law class equipped
  with its standard inclusion into `InfinitelyDivisible`; no fake analytic GGC definition is
  introduced.  Direct `lake env lean`, batched `#print axioms`, final module `lake build`, and
  project formal lint pass.  Module is wired into `GaloisForLFunctions.RHTower`.
