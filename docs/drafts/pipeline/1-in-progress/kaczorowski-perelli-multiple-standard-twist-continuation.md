# Kaczorowski–Perelli multiple-standard-twist continuation

- **ID:** `kaczorowski-perelli-multiple-standard-twist-continuation`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** J. Kaczorowski and A. Perelli, *Multiple standard twists of
  L-functions*, J. Number Theory 284 (2026), 188–213; arXiv:2603.13885v1,
  Theorems 1–2 and Corollary 1
- **Statement:** Reconstruct, without a continuation provider, the published
  meromorphic continuation of the normalized multiple standard twist of an
  `N ≥ 2` family in `S♯`, including its gamma-cleared entire quotient, spectral
  polar hyperplanes, and finite-fibre residue formula.

## Goal

Formalize the current published analytic frontier before treating the
square-fibre trace or any proposed Selberg C1/C2 mechanism as a new theorem.
The target is the source theorem itself, not a structure field, an axiom, or a
`Prop`-only continuation interface.

## Exact source target

For positive real weights `κ_ν` satisfying the source weighted-degree
normalization, the initially absolutely convergent tensor

```
M(s; α) = Σ_n ∏_ν a_ν(n_ν)n_ν^(−s_ν) exp(−2πi α ∏_ν n_ν^(κ_ν))
```

has the source's global meromorphic continuation on `ℂ^N`.  Off the source
spectrum it is entire.  On the spectrum its possible divisor is the stated
family of affine hyperplanes, its gamma-cleared quotient is entire, and its
residues are the stated finite spectral fibres.  The final Lean theorem must
encode the source normalization and signs verbatim from the paper, rather than
silently normalize them away.

## Formal proof ledger

### Dependency-closed components already formalized

- Exact `S♯` carrier, coefficient convergence, and functional-equation data:
  `RHTower/SelbergClass/Basic.lean`.
- Multiple-twist datum, initial tensor, damping, global damped convergence, and
  joint damped holomorphy:
  `MultipleStandardTwist{Damping,Holomorphy,Tensor}.lean`.
- Global `C^N` analyticity of the damped tensor from the finite-dimensional
  Fréchet-to-analytic bridge: `MultipleStandardTwistAnalytic.lean`.
- Initial-domain joint holomorphy:
  `MultipleStandardTwistInitialHolomorphy.lean`.
- Initial-domain analytic uniqueness for global candidates:
  `MultipleStandardTwistContinuationUniqueness.lean`.
- Actual `X`-uniform local bound for the damped family on initial-domain balls:
  `MultipleStandardTwistNormalFamily.lean`.
- Actual uniform undamping on those initial-domain balls:
  `MultipleStandardTwistInitialUndamping.lean`.
- Actual locally-uniform undamping on the full exact initial domain:
  `MultipleStandardTwistInitialUndampingLocal.lean`.
- Finite-dimensional locally-uniform Weierstrass closure and open-set
  identification of a subsequential limit:
  `HTGeometry/MultivariableVitali.lean`.
- Complex-ray Mellin inversion at the `2 + it` line:
  `ComplexRayMellinInversion.lean`.
- Complex-ray Mellin inversion on every positive vertical line:
  `ComplexRayMellinInversionGeneralLine.lean`.
- Termwise Mellin–Barnes identity:
  `MultipleStandardTwistMellinBarnes.lean`.
- General-positive-line Mellin–Barnes L¹ Fubini, including the exact shifted
  initial-domain condition and an explicit common starting line:
  `MultipleStandardTwistMellinBarnesGeneralLine.lean`.
- Function-level multivariable quotient object and gamma-cleared denominator:
  `MeromorphicTensor.lean`, `MultipleStandardTwistGammaClearing.lean`.
- Finite tangent-resonance projector for residue fibres:
  `MultipleStandardTwistDegreeResonanceTrace.lean`.
- Source-faithful spectrum, finite fibres, finite entire `Ξ`, invariant root
  phase, and affine hyperplanes:
  `MultipleStandardTwistSpectrum.lean`,
  `MultipleStandardTwistSpectrumGaps.lean`,
  `RHTower/SelbergClass/InvariantRootNumber.lean`.
- Codiscrete-to-pointwise functional-equation localization and critical-line
  analytic locus:
  `RHTower/SelbergClass/{FunctionalEquationLocal,GammaCriticalLine}.lean`.
- Source-normalized asymmetric functional equation on its explicit
  pair-analytic, Gamma-pole-free locus:
  `RHTower/SelbergClass/AsymmetricFunctionalEquation.lean`.
- Explicit finite Gamma-data height bound placing high vertical points in that
  locus:
  `RHTower/SelbergClass/GammaTailRegularity.lean`.
- Source-L3 polynomial-times-exponential decay for each actual asymmetric
  Gamma pair, using the valid lower height `K`:
  `RHTower/SelbergClass/GammaTailDecay.lean`.
- Finite-product assembly of that L3 decay at the exact total Gamma rate:
  `RHTower/SelbergClass/GammaTailDecayProduct.lean`.
- Exact simple affine-Gamma pole lattice, spacing, and vertical-line
  uniqueness for contour bookkeeping:
  `RHTower/SelbergClass/AffineGammaPoleLattice.lean`.
- Exact affine-Gamma principal coefficients
  `(-1)^n/(n! b)` at that lattice:
  `RHTower/SelbergClass/AffineGammaResidues.lean`.
- Sharp scalar Barnes two-Gamma/cpow vertical-tail majorant at the full
  sector threshold `|arg η|<π`:
  `RHTower/SelbergClass/BarnesTwoGammaTail.lean`.
- Lean counterexample showing why an accumulating complex hyperplane is not a
  several-variable uniqueness set:
  `MultivariableVitaliAccumulationCounterexample.lean`.

### Still required for the published theorem

1. Extend the high-vertical regularity result to every selected contour
   segment and every deformation endpoint, then use the local asymmetric
   functional equation there.
2. Combine factorwise L3 Gamma-pair decay with the remaining twist factors,
   prove line integrability and contour displacement, including all residues
   crossed by the source contours.
3. Local-uniform limiting argument as damping is removed.  The raw family
   already converges uniformly to the initial tensor on initial-domain balls,
   and the C^N Weierstrass closure/open-set uniqueness halves are formalized.
   What remains is the source's uniform bound for contour-transformed
   remainders on domains crossing the initial boundary, then normal-family
   compactness there.
4. Combine the now-formal affine-Gamma principal coefficients with all other
   contour factors to derive the source residue formula, its polynomial factor,
   and the non-identically-zero residue conclusion.

No item may be represented by a theorem parameter asserting a continuation,
residue formula, spectral set, or normal-family bound.

## Proof DAG

```text
initial absolute convergence + damping
  → Mellin inversion
  → L¹ Fubini interchange
  → factor functional equations
  → contour shifts + residue accounting
  → local-uniform undamping/Vitali
  → global gamma-cleared continuation
  → spectrum and finite-fibre residues
```

## Boundary with new research

The published continuation theorem alone does not license an unbounded tangent
Bohr mean of its regular part, nor an `α → 0` interchange.  Those two
uniformities are the later, genuinely open bridge to Selberg orthogonality.
The finite-fibre trace is therefore a `[BRIDGE]`, while this card is
`[LITERATURE]` reconstruction.

## Gates

- [x] Source theorem and proof architecture audited; corrections logged
- [x] Carrier, damping, initial holomorphy, Mellin inversion, quotient, and
  finite-fibre trace prerequisites formalized
- [x] Initial-domain (`Re w = 2`) Mellin–Barnes L¹ Fubini module integrated
  and audited
- [x] General-line Mellin–Barnes formula matching source (3.4)
- [ ] Functional-equation contour transformation formalized
- [ ] Contour shift and source residue accounting formalized
- [ ] Several-variable undamping/Vitali argument formalized
- [ ] Source Theorems 1–2 / Corollary 1 stated and proved in Lean
- [ ] Independent theorem-by-theorem source audit and target-module builds

## Log

- 2026-08-15 — created after audit established that no full Kaczorowski–Perelli
  continuation/residue theorem currently exists in Lean.  This is the required
  literature-frontier gate before claiming a new Selberg route.
- 2026-08-15 — the initial-domain sum–integral interchange was integrated as
  `MultipleStandardTwistMellinBarnesFubini.lean`.  Its concrete theorem
  `MultipleStandardTwistData.damped_eq_smul_integral_mellinBarnes` is
  source-checked, exact-module-built, and axiom-clean.  It closes only the
  initial `Re w = 2` line; source equation (3.4) still needs the variable-line
  generalization used away from the initial domain.
- 2026-08-15 — Mathlib audit found no multivariable Montel/Vitali theorem for
  functions `(Fin N → ℂ) → ℂ`.  The available
  `Complex.analyticOnNhd_iff_differentiableOn` and locally-uniform derivative
  APIs are one-variable only and cannot be applied by coercion.  The required
  replacement is an honest finite-dimensional polydisc normal-family layer:
  analytic certificates for the damped sums, compact-polydisc equicontinuity,
  Arzelà–Ascoli plus diagonal exhaustion, and a Cⁿ Vitali uniqueness theorem.
  `HTGeometry/MultivariableVitali.lean` now supplies the closure and
  open-set-uniqueness halves after such a locally uniform limit is obtained;
  it deliberately does not supply normality or compactness.
- 2026-08-15 — source-audit correction for arXiv:2603.13885v1: Lemma 7 states
  a several-variable Vitali theorem from convergence on a set with merely an
  accumulation point.  That is false in `C^N` for `N ≥ 2`: a coordinate
  hyperplane has accumulation points but is not a holomorphic uniqueness set.
  The cited Narasimhan proposition requires a uniqueness set.  The paper's
  actual convergence set `D ∩ C_1^N` is nonempty and open, so the intended
  application can be repaired, but the literal lemma must not be formalized.
  This is a literature-correction candidate, not a novelty claim.
- 2026-08-15 — second source-audit correction: the contour `L_3` begins at
  height `K`, but the estimates following (3.24) use the stronger lower bound
  `V` although only `V ≥ K` was assumed.  Replacing `V` by `K` is sufficient
  under (3.6), or one may split the segment at `V`; formal work must use one
  of those valid versions.  No verbatim contour transcription is accepted.
- 2026-08-15 — audited the existing Fubini module against source (3.4): it
  proves exactly the `Re w = 2` initial-domain identity, while the source
  requires a variable line `Re w = c` for points throughout `D`.  This is an
  open direct formalization task, not a gap that can be hidden inside the
  later contour shift.
- 2026-08-15 — `MultipleStandardTwistSpectrumGaps.lean` proved the previously
  hidden strict-sublevel finiteness and positive right-gap statements for the
  explicit spectral-value map.  This supplies the uniform spectral separation
  needed to choose the source damping threshold; it supplies no contour shift
  or residue formula.
- 2026-08-15 — `ComplexRayMellinInversionGeneralLine.lean` proved the exact
  Gamma inversion formula on every line `Re w = c > 0`, with the sector Gamma
  majorant needed for later Mellin--Barnes bounds.  It is source-checked,
  exact-module-built, and axiom-clean.  This closes the one-variable inversion
  prerequisite only; the shifted-series Fubini interchange remains the next
  open source equation.
- 2026-08-15 — `RHTower/SelbergClass/AsymmetricFunctionalEquation.lean`
  formalized K–P (2.2) on the explicit intersection of the pair-analytic
  completed-functional-equation locus and the two-Gamma-factor pole-free
  locus.  This corrects the totalized-Gamma issue: it is not an everywhere
  pointwise identity.  Contour regularity, decay, deformation, and residues
  remain open.
- 2026-08-15 — `HTGeometry/MultivariableVitali.lean` formalized the valid
  C^N Weierstrass step: a locally uniformly convergent holomorphic sequence
  has an analytic limit, and convergence on a nonempty open subset identifies
  that limit on a preconnected domain.  It supplies neither a normal-family
  theorem nor a locally-uniform subsequence, so it does not close the
  undamping argument.
- 2026-08-15 — `RHTower/SelbergClass/GammaTailRegularity.lean` proved a
  source-correct high-tail condition: if every `|Im μ_j| < λ_j |t|`, then the
  point `σ + it` lies in the local asymmetric-FE regular locus, provided its
  displayed continuation singularity is excluded.  The finite sum height
  `Σ |Im μ_j|/λ_j < |t|` discharges that exception even for rank-zero data.
  This resolves only tail pole avoidance; it does not prove a contour shift.
- 2026-08-15 — `MultipleStandardTwistMellinBarnesGeneralLine.lean` proved
  source (3.4)'s L¹ sum--integral interchange for every `c > 0` with
  `1 < Re(s_i) + κ_i c` in every coordinate.  Its exact coefficient identity
  shifts by `κ_i c`, and the explicit
  `c_*(s) = 1 + Σ_j max(0, (2 - Re(s_j))/κ_j)` is positive and satisfies all
  shifted inequalities.  This closes the starting-line/Fubini step only;
  contour deformation and undamping remain open.
- 2026-08-15 — `MultipleStandardTwistNormalFamily.lean` proved an exact
  initial-domain survivor of the failed global-normality attempt: on every
  ball whose `2r` left shift remains coordinatewise to the right of `1`, the
  actual family `D.damped X` has one summable majorant independent of `X>0`.
  The direct bound necessarily stops there: outside the initial domain its
  constants degenerate as `X → ∞`.  The missing source object is the
  contour-transformed, residue-subtracted remainder bounded in (3.34)/(3.38).
- 2026-08-15 — **[CONJECTURE → FAIL/PIVOT]** The raw damped series might be
  uniformly locally bounded on a continuation domain for free.  Direct
  majorization proves it only on the initial domain and loses control as
  `X → ∞` beyond that domain.  **Pivot:** construct and bound the actual
  functional-equation/contour-shift remainder before invoking C^N compactness;
  no generic normal-family premise is introduced.
- 2026-08-15 — `MultipleStandardTwistInitialUndamping.lean` completed the
  positive initial-domain half: `D.damped X` tends uniformly to `D.initial`
  as `X → ∞` on every ball with coordinatewise `Re(s₀_i - 2r) > 1`.
  Its finite-head plus summable-tail proof gives the exact nonempty open
  convergence set needed for the repaired C^N uniqueness step, but supplies
  no bound past that domain.
- 2026-08-15 — `MultipleStandardTwistInitialUndampingLocal.lean` upgraded
  the ball theorem to `TendstoLocallyUniformlyOn` on the full exact initial
  domain by taking the finite coordinatewise distance to its boundary.  Thus
  the source's overlap `D ∩ C_1^N` has a Lean-valid local-uniform anchor;
  only continuation-side transformed bounds and compactness are missing.
- 2026-08-15 — `RHTower/SelbergClass/AffineGammaPoleLattice.lean` solved the
  affine Gamma-pole geometry used by the contour variable: poles of
  `Γ(b w + A)` are exactly `w = -(A+n)/b`, are simple, have one fixed
  imaginary level, and for `b>0` have strictly decreasing real coordinates
  with spacing `1/b`.  This is the residue-bookkeeping layer only; no residue
  coefficient or contour displacement is claimed.
- 2026-08-15 — `RHTower/SelbergClass/GammaTailDecay.lean` proved the
  source-L3 bound for one actual asymmetric Gamma pair.  Under the explicit
  factorwise `K` condition, its norm is polynomial in `v` times
  `exp(-π λ_j κ v / 2)` for every `v ≥ K`.  The proof uses `K` throughout and
  deliberately does not claim that the source's printed (3.6) supplies this
  condition or that a full contour integral is controlled.
- 2026-08-15 — `RHTower/SelbergClass/AffineGammaResidues.lean` proved the
  exact principal coefficient of every affine Gamma pole:
  `(w-p_n) Γ(bw+A) → (-1)^n/(n! b)` at `p_n = -(A+n)/b`.  This includes
  negative slopes needed by reflected factors.  It is a local residue fact;
  multiplying it by the remaining contour factors and invoking a contour
  residue theorem are still required.
- 2026-08-15 — `RHTower/SelbergClass/GammaTailDecayProduct.lean` assembled
  the pairwise L3 estimate over all Gamma factors: the actual finite Gamma
  product is bounded by `C v^N exp(-π (Σ_j λ_j) κ v / 2)` for `v ≥ K`, under
  the explicit per-factor K-height inequalities.  Sine, conductor, phase,
  Dirichlet, and contour factors remain deliberately outside this theorem.
- 2026-08-15 — contour API audit identified the first finite, source-faithful
  `[BRIDGE]`: for `J_{ξ,η}(w)=Γ(ξ-w)Γ(w)η^{-w}`, a finite rectangle from
  `Re w=-m-1/2` to `Re w=c` should equal
  `Σ_{n=0}^m (-1)^n Γ(ξ+n)η^n/n!` under `0<c<Re ξ`.  The existing
  `RectangleIntegral'_eq_sumResiduesIn` API and the new affine-Gamma residue
  theorem exactly support that statement once its concrete meromorphicity,
  boundary, and finite-pole proofs are supplied.  This is not Barnes Lemma 6
  or a K–P contour shift.  The infinite-line passage remains blocked by a
  two-Gamma tail estimate for `|arg η|<π`; the existing one-Gamma sector bound
  only covers `|arg η|<π/2`, while the source's `η=iω_X` need not lie there.
- 2026-08-15 — `RHTower/SelbergClass/BarnesTwoGammaTail.lean` closed that
  pointwise tail gap at the correct threshold: for `0<c<Re ξ` and
  `|arg η|<π`, the scalar Barnes integrand is bounded by
  `C |t|^N exp(-(π-|arg η|)|t|)` once `|t|≥|Im ξ|+1`.  Full line
  integrability and the infinite-rectangle limit remain to be assembled from
  this bound; neither was asserted prematurely.
- 2026-08-15 — `RHTower/SelbergClass/BarnesFiniteRectangle.lean` made the
  finite Barnes rectangle fully concrete: it defines
  `J_{ξ,η}(w)=Γ(ξ-w)Γ(w)η^{-w}`, proves the exact residue at every crossed
  negative-integer pole, and classifies the interior pole set of the
  half-integral rectangle as `{0,-1,…,-m}` under `0<c<Re ξ`.  The final
  `RectangleIntegral'`-to-finite-sum reduction was not claimed: its current
  `Finset.sum_image` normalization exceeded the bounded Lean elaboration
  pass.  This leaves a proof-engineering closure, not a license to assert
  Barnes Lemma 6 or a K–P contour shift.

## Source-correction ledger

- **Invariant phase.** The raw completed-functional-equation phase `ω` differs
  from the `ω_F = ω ∏ λ_j^(-2 i Im μ_j)` used in (1.8).  The former was
  initially used in the Lean finite-fibre sum; it is now corrected through
  `SelbergGammaData.invariantRootNumber`.  No residue formula is claimed.
- **Damping display.** Immediately after (3.2), the source writes an extra
  factor `α` in `exp(-α z_X(α)⋯)` despite `z_X(α)` already containing `α`;
  the displayed right-hand rate confirms the intended factor is just `z_X`.
- **Remainder index.** In (3.24), the product over `μ ≠ ν` contains
  `s^*_{0,ν}` in the `μ`th Gamma factor.  The source-consistent factor is
  `s^*_{0,μ}`.  Neither erroneous expression is copied into Lean.
- **Global-cover gap.** The source first restricts `D` to coordinatewise
  `Re s ≤ 3/2` but then says such `D` can be arbitrarily large to cover all
  `C^N`; that cannot cover mixed points such as `(3,0,…)`.  A variable
  starting line `c_*(s)` is now formalized and supplies the needed initial
  Mellin line at every point.  The separate assertion that contour/undamping
  arguments cover arbitrary connected polydiscs remains unproved.
- **Hidden arithmetic bounds.** The strict-sublevel finiteness of
  `{n : α_n < a}` and a positive right gap above a spectral value were used
  silently to choose uniform damping thresholds.  They are now direct Lean
  theorems in `MultipleStandardTwistSpectrumGaps.lean`.

These are audit findings about the current source version, not a claim that
the continuation theorem or Selberg C1/C2 is false.

## Later verification update

- 2026-08-15 — `RHTower/SelbergClass/BarnesFiniteRectangleIntegral.lean`
  subsequently passed a foreground source check and exact target-module build.
  It proves the two fixed-rectangle identities
  `rectangleIntegral_barnesJ_eq_sumResiduesIn` and
  `rectangleIntegral_barnesJ_eq_finset_sum`; the second reduces the rectangle
  integral to the finite set of concrete residues.  This corrects the earlier
  proof-engineering status above.  It still proves neither the horizontal-edge
  limit, line integrability, the `m → ∞` passage, Barnes Lemma 6, nor a K--P
  contour shift.
- 2026-08-15 — `RHTower/SelbergClass/BarnesTwoGammaLineIntegrable.lean`
  now proves the previously missing full vertical-line integrability for the
  actual scalar Barnes integrand.  The proof is exact: both Gamma arguments
  remain in the positive real half-plane on the compact middle interval, and
  the verified strict tail rate `π - |arg η|` supplies an integrable global
  majorant outside it.  This corrects the preceding status only at the
  line-integrability node.  Horizontal-edge decay, the infinite rectangle,
  `m → ∞`, Barnes Lemma 6, and K--P's contour transformation remain open.
- 2026-08-15 — `RHTower/SelbergClass/BarnesFiniteRectangleExplicitSum.lean`
  closed the finite-sum normalization: the fixed rectangle is exactly
  `Σ_{n=0}^m (-1)^n Γ(ξ+n) η^n/n!`.  The proof uses the concrete pole
  enumeration and injectivity of `n ↦ -n`, rather than a generic residue
  interface.  This is a finite bridge only; it supplies no height limit or
  infinite binomial/Barnes evaluation.
- 2026-08-15 — `RHTower/SelbergClass/BarnesHorizontalEdges.lean` proved the
  exact signed top and bottom horizontal-edge limits for every fixed finite
  Barnes rectangle.  Its key new internal bridge extends Gamma's vertical
  polynomial--exponential estimate to arbitrary compact real strips by a
  finite recurrence.  Together with the separately formalized two vertical
  line integrability, this closes all scalar fixed-rectangle analytic inputs;
  the finite-to-infinite left-edge limit, its residue-series summation, Barnes
  Lemma 6, and the K--P contour transform remain distinct open nodes.
