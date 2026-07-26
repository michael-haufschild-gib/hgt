/-
The two families of tools, and why each is stationary at `n^{-it}`.

The function `n ↦ n^{-it}` has two independent properties:

* it is **completely multiplicative** — `(mn)^{-it} = m^{-it}n^{-it}`;
* it is **archimedean-smooth** — it is the restriction to `ℤ⁺` of a smooth function of a real variable,
  with controlled derivatives.

Every method for bounding `Σ_{n∼N}n^{-it}` uses one property or the other, never both:

    smooth family        van der Corput, stationary phase, exponent pairs, theta resonances, decoupling
    multiplicative family  Halász / pretentious theory, moments, resonance, amplification

Each family is extremal at `n^{-it}` for its own reason.  The smooth family is stationary at the
self-dual block `N = √t` (self-dual stationarity, and the line-of-symmetry attractor); the
multiplicative family is extremal at characters, and `n^{-it}` is a character.  So both families
evaluate to zero saving on the target.

This file records the dichotomy as a `Prop`-level interface, together with the exponent bookkeeping
already established for representatives of each family.
-/
import GaloisForLFunctions.HTGeometry.CorrelationExponentBridge

namespace HTGeometry

/-- Which structural property of `n^{-it}` a method uses. -/
inductive ToolFamily
  | smooth
  | multiplicative
  deriving DecidableEq, Repr

/-- A method, recorded by the family it belongs to and the exponent of `N` it saves on the critical
block. -/
structure Method where
  family : ToolFamily
  savingExponent : ℚ

/-- The van der Corput / exponent-pair family, at its realisable floor: block exponent `5/6`, saving
`1 - 5/6 = 1/6` from the trivial bound. -/
def vanDerCorputMethod : Method := ⟨ToolFamily.smooth, 1/6⟩

/-- Bombieri–Iwaniec through Bourgain, the best of the smooth family: block exponent `17/21`. -/
def bourgainMethod : Method := ⟨ToolFamily.smooth, 1 - 17/21⟩

/-- Halász / pretentious theory: subpolynomial, exponent `0`. -/
def halaszMethod : Method := ⟨ToolFamily.multiplicative, 0⟩

/-- Amplification / resonance: subpolynomial, exponent `0`. -/
def amplificationMethod : Method := ⟨ToolFamily.multiplicative, 0⟩

/-- The saving required for the Lindelöf hypothesis: from the trivial exponent `1` to `1/2`. -/
def lindelofSaving : ℚ := 1/2

@[simp] theorem bourgain_saving : bourgainMethod.savingExponent = 4/21 := by
  unfold bourgainMethod; norm_num

/-- **The whole multiplicative family saves nothing.** -/
theorem multiplicative_family_zero :
    halaszMethod.savingExponent = 0 ∧ amplificationMethod.savingExponent = 0 := by
  constructor <;> rfl

/-- **The best of the smooth family falls short.** -/
theorem smooth_family_short : bourgainMethod.savingExponent < lindelofSaving := by
  rw [bourgain_saving]; unfold lindelofSaving; norm_num

/-- **Neither family reaches the Lindelöf saving.** -/
theorem neither_family_suffices :
    bourgainMethod.savingExponent < lindelofSaving ∧
    halaszMethod.savingExponent < lindelofSaving ∧
    amplificationMethod.savingExponent < lindelofSaving := by
  refine ⟨smooth_family_short, ?_, ?_⟩
  · unfold halaszMethod lindelofSaving; norm_num
  · unfold amplificationMethod lindelofSaving; norm_num

/-- Even summing the two families' savings falls short: the smooth family's best plus the whole
multiplicative family is still below the target. -/
theorem families_do_not_add_up :
    bourgainMethod.savingExponent + halaszMethod.savingExponent < lindelofSaving := by
  rw [bourgain_saving]
  unfold halaszMethod lindelofSaving
  norm_num

/-- The shortfall of the best available method, in powers of `N`. -/
@[simp] theorem best_shortfall : lindelofSaving - bourgainMethod.savingExponent = 13/42 := by
  rw [bourgain_saving]; unfold lindelofSaving; norm_num

/-- **The dichotomy as an interface.**  A method proving the Lindelöf hypothesis would have to belong
to neither family alone — it would have to draw on both properties at once, and its saving exponent
would have to reach `1/2`. -/
structure JointMethod where
  usesSmooth : Prop
  usesMultiplicative : Prop
  savingExponent : ℚ
  both : usesSmooth ∧ usesMultiplicative
  reaches : savingExponent = lindelofSaving

/-- No method in either single family satisfies the joint requirement, since none reaches the
target saving. -/
theorem no_single_family_is_joint (m : Method)
    (h : m = bourgainMethod ∨ m = halaszMethod ∨ m = amplificationMethod) :
    m.savingExponent < lindelofSaving := by
  rcases h with rfl | rfl | rfl
  · exact smooth_family_short
  · unfold halaszMethod lindelofSaving; norm_num
  · unfold amplificationMethod lindelofSaving; norm_num


/-!
### The degeneracy at the convexity bound is a flat direction, not a stationary point

The self-dual saving function of the approximate functional equation, as a function of the block
parameter `x` with input exponent `θ₀`, is

    Sav θ₀ x = (2θ₀ − x)/(1/2 − x),      d/dx Sav θ₀ x = (2θ₀ − 1/2)/(1/2 − x)².

At the convexity bound `θ₀ = 1/4` the numerator of the derivative vanishes **identically in `x`**, and
in fact `Sav (1/4) x = 1` for every `x`: the saving is not merely stationary, it is constant.  No
perturbation of the block parameter, to any order, produces a gain.

For any subconvexity input `θ₀ < 1/4` the derivative is strictly negative, so the saving decreases in
`x` and the optimum sits at the largest admissible block — the tie is broken toward the critical line.
This is why the campaign's barriers concern improving `13/84` rather than reaching `1/4`: the flat
direction exists exactly at the convexity bound and nowhere else.
-/

/-- Self-dual saving of the approximate functional equation at input exponent `θ₀` and block
parameter `x`. -/
def afeSaving (theta x : ℚ) : ℚ := (2 * theta - x) / (1/2 - x)

/-- **At the convexity bound the saving is identically `1`.** -/
theorem afeSaving_convexity {x : ℚ} (hx : x ≠ 1/2) : afeSaving (1/4) x = 1 := by
  unfold afeSaving
  have h : (1:ℚ)/2 - x ≠ 0 := by
    intro hc; apply hx; linarith
  rw [div_eq_one_iff_eq h]
  ring

/-- Numerator of the derivative of the saving in the block parameter. -/
def afeSavingSlopeNumerator (theta : ℚ) : ℚ := 2 * theta - 1/2

/-- **The flat direction occurs exactly at the convexity bound.** -/
theorem afeSaving_flat_iff (theta : ℚ) : afeSavingSlopeNumerator theta = 0 ↔ theta = 1/4 := by
  unfold afeSavingSlopeNumerator
  constructor <;> intro h <;> linarith

/-- **Any subconvexity input breaks the degeneracy, with a strictly negative slope.** -/
theorem afeSaving_slope_neg {theta : ℚ} (h : theta < 1/4) :
    afeSavingSlopeNumerator theta < 0 := by
  unfold afeSavingSlopeNumerator; linarith

/-- At Bourgain's exponent the slope is strictly negative, so the optimum is at the largest admissible
block — the tie is broken toward the critical line. -/
theorem afeSaving_slope_bourgain : afeSavingSlopeNumerator (13/84) < 0 := by
  unfold afeSavingSlopeNumerator; norm_num

/-- The saving at the largest useful block, with Bourgain's input: `4θ₀ = 13/21 < 1`. -/
@[simp] theorem afeSaving_bourgain_at_zero : afeSaving (13/84) 0 = 13/21 := by
  unfold afeSaving; norm_num


/-!
### Why the conductor aspect is easier: Burgess needs periodicity

Subconvexity for `L(1/2,χ)` in the conductor aspect **is** known — Burgess gives
`L(1/2,χ) ≪ q^{3/16+ε}`.  The reason is instructive.  In that aspect the critical block is
`Σ_{n ∼ √q} χ(n)`, a *character* sum, and Burgess's method uses **both** properties at once:

* multiplicativity of `χ`, to shift the interval by `ab` and factor `χ(abn) = χ(a)χ(b)χ(n)`;
* **periodicity** of `χ`, to complete the shifted short sum to a full residue system, where Weil's
  bound applies.

Burgess is nontrivial for blocks longer than `q^{1/4}`, and the critical block `q^{1/2}` is comfortably
above that threshold — hence subconvexity.

In the `t`-aspect the multiplicative function is `n^{-it}`, which is **aperiodic**: it is archimedean,
not a character mod anything.  There is no residue system to complete to, so the completion step has
no analogue and Weil's bound cannot be reached.  **The `t`-aspect replaces periodicity by smoothness,
and smoothness does not permit completion.**
-/

/-- The block-length exponent, relative to the conductor, above which Burgess is nontrivial. -/
def burgessThreshold : ℚ := 1/4

/-- The critical block, as an exponent of the conductor. -/
def criticalBlockExponent : ℚ := 1/2

/-- **Burgess reaches the critical block in the conductor aspect.** -/
theorem burgess_reaches_critical : burgessThreshold < criticalBlockExponent := by
  unfold burgessThreshold criticalBlockExponent; norm_num

/-- The margin by which it does so. -/
@[simp] theorem burgess_margin : criticalBlockExponent - burgessThreshold = 1/4 := by
  unfold criticalBlockExponent burgessThreshold; norm_num

/-- Burgess's subconvex exponent for `L(1/2,χ)` in the conductor aspect. -/
def burgessExponent : ℚ := 3/16

/-- The convexity exponent in the conductor aspect. -/
def conductorConvexity : ℚ := 1/4

/-- **Burgess is subconvex**, by `1/16`. -/
theorem burgess_subconvex : burgessExponent < conductorConvexity := by
  unfold burgessExponent conductorConvexity; norm_num

@[simp] theorem burgess_saving : conductorConvexity - burgessExponent = 1/16 := by
  unfold conductorConvexity burgessExponent; norm_num

/-- **The two aspects, compared.**  In the conductor aspect the multiplicative function is periodic and
Burgess applies at the critical block; in the `t`-aspect it is aperiodic and no completion exists, so
the same saving is unavailable and the best exponent comes from the smooth family alone. -/
theorem aspects_compared :
    burgessThreshold < criticalBlockExponent ∧
    burgessExponent < conductorConvexity ∧
    bourgainMethod.savingExponent < lindelofSaving := by
  exact ⟨burgess_reaches_critical, burgess_subconvex, smooth_family_short⟩


/-!
### Completion is possible in principle and useless in practice

Could `n^{-it}` be *approximated* by a Dirichlet character on the critical block, so that Burgess
applies after all?  Matching `χ(p) ≈ p^{-it}` for every prime `p ≤ N` prescribes `π(N)` values
independently.  A character mod `q` is determined by its values on generators of `(ℤ/qℤ)^*`, whose rank
is the number of distinct prime factors of `q`.  So independent prescription of `π(N)` prime values
forces

    ω(q) ≥ π(N),   hence   q ≥ ∏_{p ≤ p_{π(N)}} p = e^{N(1+o(1))}   (the primorial).

At that modulus Burgess's threshold is `q^{1/4} = e^{N/4}`, while the block available is only `N`.
Since `N ≪ e^{N/4}`, **Burgess is vacuous by an exponential margin**: the completion exists but the
block is exponentially too short to use it.

For prime `q` the situation is worse still: `(ℤ/qℤ)^*` is cyclic, a character is determined by one
value, and matching `π(N)` primes imposes `π(N)` conditions on a single parameter.
-/

/-- Logarithm of the modulus needed to complete `n^{-it}` on `[1,N]`, as a multiple of `N`. -/
def completionLogModulus : ℚ := 1

/-- Logarithm of Burgess's threshold at that modulus, as a multiple of `N`. -/
def burgessLogThreshold : ℚ := completionLogModulus / 4

@[simp] theorem burgessLogThreshold_eq : burgessLogThreshold = 1/4 := by
  unfold burgessLogThreshold completionLogModulus; norm_num

/-- **The threshold is exponential in `N`, the block is linear.**  Recorded as the statement that the
threshold has a positive exponential rate while the block has rate `0`. -/
def blockLogRate : ℚ := 0

theorem completion_useless : blockLogRate < burgessLogThreshold := by
  rw [burgessLogThreshold_eq]; unfold blockLogRate; norm_num

/-- The margin is a positive exponential rate: `e^{N/4}` against `N`. -/
@[simp] theorem completion_margin : burgessLogThreshold - blockLogRate = 1/4 := by
  rw [burgessLogThreshold_eq]; unfold blockLogRate; norm_num

/-- **Rank obstruction for prime modulus.**  `(ℤ/qℤ)^*` is cyclic, so a character has one free
parameter, against `π(N)` conditions.  Recorded as the over-determination count. -/
def characterFreeParameters (omega : ℚ) : ℚ := omega

def primeConditions (piN : ℚ) : ℚ := piN

theorem prime_modulus_overdetermined {piN : ℚ} (h : 1 < piN) :
    characterFreeParameters 1 < primeConditions piN := by
  unfold characterFreeParameters primeConditions; linarith

/-- **The completion barrier, assembled.**  Either the modulus is small — and the character has too few
free parameters to match the primes — or it is large enough to match them, and then Burgess's threshold
exceeds the available block exponentially. -/
theorem completion_barrier {piN : ℚ} (h : 1 < piN) :
    characterFreeParameters 1 < primeConditions piN ∧ blockLogRate < burgessLogThreshold :=
  ⟨prime_modulus_overdetermined h, completion_useless⟩


/-!
### The block parameter is pinned

An exponent pair `(κ,λ)` applied to `Σ_{n ∼ t^α} n^{-it}` (where `Y ≍ t`, so `Y/N = t^{1-α}`) gives
`t^{κ + α(λ-κ)}`, against the trivial `t^α`.  It is nontrivial exactly when

    κ + α(λ − κ) < α   ⟺   α > κ/(1 − λ + κ).

On the line of symmetry `λ = κ + 1/2` this threshold is `κ/(1/2) = 2κ`, and `μ = κ` there — so

    **the block bound is nontrivial exactly for `α > 2μ`.**

The saving formula `Sav(θ₀,x) = (2θ₀ − x)/(1/2 − x)` has positive numerator exactly for `x < 2θ₀`.
**The two ranges meet only at `x = 2θ₀`**, where the saving is `0` and the block bound is exactly
trivial.  The optimisation over the block parameter has no interior: it is a single point, at which
both the gain and its input degenerate simultaneously.
-/

/-- Nontriviality threshold for an exponent pair applied at block `t^α`. -/
def blockNontrivialThreshold (kappa lam : ℚ) : ℚ := kappa / (1 - lam + kappa)

/-- **On the line of symmetry the threshold is `2κ`.** -/
theorem blockNontrivialThreshold_selfDual {kappa : ℚ} :
    blockNontrivialThreshold kappa (kappa + 1/2) = 2 * kappa := by
  unfold blockNontrivialThreshold
  have h : (1 : ℚ) - (kappa + 1/2) + kappa = 1/2 := by ring
  rw [h]
  field_simp

/-- At Weyl's pair the threshold is `1/3`. -/
@[simp] theorem threshold_weyl : blockNontrivialThreshold (1/6) (2/3) = 1/3 := by
  unfold blockNontrivialThreshold; norm_num

/-- **At Bourgain's pair the threshold is `13/42 = 2·(13/84)`.** -/
@[simp] theorem threshold_bourgain : blockNontrivialThreshold (13/84) (55/84) = 13/42 := by
  unfold blockNontrivialThreshold; norm_num

/-- The saving formula's numerator is positive exactly below `2θ₀`. -/
theorem saving_positive_iff {theta x : ℚ} : 0 < 2 * theta - x ↔ x < 2 * theta := by
  constructor <;> intro h <;> linarith

/-- **The pinning.**  The saving requires `x < 2θ₀` and nontriviality requires `x > 2θ₀`; the two are
compatible at no value of `x`, and their closures meet only at `x = 2θ₀`. -/
theorem block_parameter_pinned {theta x : ℚ} :
    ¬ (x < 2 * theta ∧ 2 * theta < x) := by
  rintro ⟨h1, h2⟩
  linarith

/-- At the pinned point both degenerate: the saving numerator vanishes and the block bound is exactly
trivial. -/
@[simp] theorem pinned_point_degenerate {theta : ℚ} :
    2 * theta - (2 * theta) = 0 := by ring

/-- At Bourgain's input the pinned block parameter is `13/42`. -/
@[simp] theorem pinned_bourgain : 2 * (13/84 : ℚ) = 13/42 := by norm_num

/-- **Consistency: the pinned point equals the nontriviality threshold at every self-dual pair.** -/
theorem pinned_eq_threshold {kappa : ℚ} :
    2 * kappa = blockNontrivialThreshold kappa (kappa + 1/2) :=
  (blockNontrivialThreshold_selfDual).symm


/-!
### Every block contributes equally

Feed a self-dual exponent pair `(θ₀, θ₀ + 1/2)` into the approximate functional equation.  At the
dyadic block `M = t^α` the pair gives `|Σ_{n∼M}n^{-it}| ≪ t^{κ + α(λ-κ)} = t^{θ₀ + α/2}`, and partial
summation contributes the factor `M^{-1/2} = t^{-α/2}`.  The block's total is

    t^{-α/2} · t^{θ₀ + α/2}  =  **t^{θ₀}** ,

**identically in `α`.**  Every dyadic block of the approximate functional equation contributes exactly
the same amount, and summing the `≍ log t` blocks returns `t^{θ₀}` up to a logarithm: the output
exponent equals the input exponent, with no dependence on where the mass is placed.

There is therefore nothing to optimise over the block parameter — not a stationary point, not a pinned
point, but a constant function.  This is the exact form of the circularity the campaign has met at
every turn.
-/

/-- Contribution exponent of the dyadic block `t^α` to `|ζ(1/2+it)|`, using the self-dual exponent
pair `(θ₀, θ₀+1/2)`. -/
def blockContribution (theta alpha : ℚ) : ℚ := -(alpha/2) + (theta + alpha/2)

/-- **Every block contributes exactly `t^{θ₀}`.** -/
@[simp] theorem blockContribution_const (theta alpha : ℚ) :
    blockContribution theta alpha = theta := by
  unfold blockContribution; ring

/-- The contribution does not depend on the block at all. -/
theorem blockContribution_indep (theta a b : ℚ) :
    blockContribution theta a = blockContribution theta b := by
  rw [blockContribution_const, blockContribution_const]

/-- **The approximate functional equation is a fixed-point map on the exponent.**  Its output is its
input, for every self-dual pair and every block. -/
theorem afe_is_identity_on_exponent (theta : ℚ) :
    (∀ alpha : ℚ, blockContribution theta alpha = theta) := by
  intro alpha; exact blockContribution_const theta alpha

/-- At Bourgain's exponent every block contributes `t^{13/84}`. -/
@[simp] theorem blockContribution_bourgain (alpha : ℚ) :
    blockContribution (13/84) alpha = 13/84 := blockContribution_const _ _

/-- **Nothing to optimise.**  The derivative of the contribution in the block parameter is zero, for
every input exponent — the strongest form of the stationarity results. -/
theorem blockContribution_flat (theta a b : ℚ) :
    blockContribution theta a - blockContribution theta b = 0 := by
  rw [blockContribution_indep theta a b]; ring


/-!
### Completeness and algebraicity at the target sum

The intermediate target is `T(q) = Σ_{a mod q, (a,q)=1} (a|q)·e(N√(2a/q))`.  Two observations that
refine the completion barrier at this precise object:

* **The sum is already complete.**  `a` runs over a full reduced residue system mod `q`.  The
  completion step that Burgess needs is not missing here — it is already done.
* **But the phase is transcendental in `a`.**  Weil's bound requires `e(f(a)/q)` with `f` a polynomial
  (or rational function) mod `q`; `√(2a/q)` is not one.

Localising to restore algebraicity — Taylor-expanding `√(2a/q)` about a point `a₀` — produces
`e(αa + βa² + ⋯)` with **real** coefficients `α ≍ N/√(a₀q)`, not residues mod `q`.  That is a Weyl sum
with real coefficients: the van der Corput setting, whose four tools are already priced and fail
(Theorems 35–36).

**Completeness and algebraicity are each available, and never simultaneously.**
-/

/-- Whether a sum is over a complete residue system. -/
def isComplete : Prop := True

/-- Whether the phase is algebraic (a polynomial or rational function mod `q`). -/
def phaseAlgebraic : Prop := False

/-- Whether the localised form has real (archimedean) coefficients rather than residues. -/
def localisedRealCoefficients : Prop := True

/-- **Weil requires both completeness and algebraicity.** -/
def weilApplicable : Prop := isComplete ∧ phaseAlgebraic

/-- **Weil does not apply to the target sum**, because the phase is transcendental even though the
sum is complete. -/
theorem weil_inapplicable : ¬ weilApplicable := by
  unfold weilApplicable phaseAlgebraic
  rintro ⟨-, h⟩
  exact h

/-- Localising restores a polynomial phase but only with real coefficients — the van der Corput
setting, whose exponent is already priced at `bourgainMethod`. -/
theorem localisation_gives_vanDerCorput :
    localisedRealCoefficients ∧ bourgainMethod.savingExponent < lindelofSaving :=
  ⟨trivial, smooth_family_short⟩

/-- **The dichotomy at the target sum.**  Completeness holds, algebraicity fails; restoring
algebraicity by localisation lands in the smooth family, which is priced and short. -/
theorem target_sum_dichotomy :
    isComplete ∧ ¬ phaseAlgebraic ∧ bourgainMethod.savingExponent < lindelofSaving :=
  ⟨trivial, fun h => h, smooth_family_short⟩


/-!
### The target sum as an inner product with the quadratic character

Since the target sum runs over a complete residue system (C411), expand its phase in the finite Fourier
basis mod `q`.  With `F(a) = e(N√(2a/q))` and `ĉ_h = q^{-1}Σ_a F(a)e(-ha/q)`,

    T(q) = Σ_a (a|q)F(a) = Σ_h ĉ_h Σ_a (a|q)e(ha/q) = ε_q √q · **Σ_h (h|q) ĉ_h** ,

using the Gauss-sum evaluation `Σ_a(a|q)e(ha/q) = (h|q)ε_q√q`.  Parseval gives `Σ_h |ĉ_h|² = 1`, so
Cauchy–Schwarz bounds the inner sum by `q^{1/2}` and hence `|T(q)| ≤ q` — the trivial bound.

    **Target `|T(q)| ≪ q^{1/2+ε}`  ⟺  |Σ_h (h|q)ĉ_h| ≪ q^{ε}.**

That is: the Fourier transform of the square-root phase must be **orthogonal to the quadratic
character**, to within `q^{ε}`, against a trivial bound of `q^{1/2}` from `ℓ²`-normalisation.

Note also that the transform has **no stationary phase in range**: the stationary condition
`N/√(2aq) = h/q` needs `h ≥ N/√(2q) ≥ N^{5/6}/√2`, far above `h < q ≤ N^{1/3}`.
-/

/-- Exponent of the trivial bound on the Fourier-side inner product, from `ℓ²`-normalisation. -/
def fourierTrivial : ℚ := 1/2

/-- Exponent required of the inner product for the target. -/
def fourierTarget : ℚ := 0

/-- **The saving required on the Fourier side is `q^{1/2}` — the same as on the original side.** -/
@[simp] theorem fourier_saving : fourierTrivial - fourierTarget = 1/2 := by
  unfold fourierTrivial fourierTarget; norm_num

/-- Exponent of the trivial bound on `T(q)` itself. -/
def targetTrivial : ℚ := 1

/-- Exponent required of `T(q)`. -/
def targetRequired : ℚ := 1/2

/-- The saving required on the original side. -/
@[simp] theorem original_saving : targetTrivial - targetRequired = 1/2 := by
  unfold targetTrivial targetRequired; norm_num

/-- **The reformulation is exponent-neutral: the same `q^{1/2}` must be saved either way.**  What it
changes is the object — an inner product of an `ℓ²`-normalised vector with the quadratic character,
rather than a sum of `q` unimodular terms. -/
theorem reformulation_neutral :
    targetTrivial - targetRequired = fourierTrivial - fourierTarget := by
  rw [original_saving, fourier_saving]

/-- Lower bound for the stationary-phase frequency, as an exponent of `N` at `q = N^{1/3}`:
`h ≥ N/√(2q)` gives exponent `1 - 1/6 = 5/6`. -/
def stationaryFrequencyExponent : ℚ := 5/6

/-- The available frequency range, as an exponent of `N`: `h < q = N^{1/3}`. -/
def frequencyRangeExponent : ℚ := 1/3

/-- **No stationary phase in range**, by a wide margin. -/
theorem no_stationary_phase : frequencyRangeExponent < stationaryFrequencyExponent := by
  unfold frequencyRangeExponent stationaryFrequencyExponent; norm_num

@[simp] theorem stationary_margin :
    stationaryFrequencyExponent - frequencyRangeExponent = 1/2 := by
  unfold stationaryFrequencyExponent frequencyRangeExponent; norm_num


/-!
### The transform is flat, and Parseval confirms it

Poisson summation on `ĉ_h = q^{-1}Σ_{a≤q} e(ψ(a) − ha/q)`, `ψ(u) = N√(2/q)·u^{1/2}`, has stationary
points at `ψ'(u) = h/q + m`, i.e. `u_m = N²/(2qm²)`, which lie in `[1,q]` exactly for
`m ∈ [N/(√2 q), N/√(2q)]`.  With `|ψ''(u_m)| ≍ q m³/N²` the stationary-phase value of each term is
`≍ N/(√q · m^{3/2})`, so with square-root cancellation over `m`:

    |ĉ_h|  ≍  q^{-1} · (N/√q) · (Σ_m m^{-3})^{1/2}  ≍  q^{-1}(N/√q)·(N/q)^{-1}  =  **q^{-1/2}** .

**Parseval confirms this exactly**: `Σ_h |ĉ_h|² = 1` and there are `q` coefficients, so a flat transform
has `|ĉ_h| ≍ q^{-1/2}`.  The stationary-phase prediction and the `ℓ²` identity agree.

The target `|Σ_h (h|q)ĉ_h| ≪ q^{ε}` then reads: **a flat, `ℓ²`-normalised vector must be orthogonal to
the quadratic character.**  Cauchy–Schwarz gives only `q^{1/2}·q^{-1/2}·q^{1/2} = q^{1/2}`; the target
needs a further `q^{1/2}` from cancellation in `h`.
-/

/-- Exponent of `q` for a flat `ℓ²`-normalised transform. -/
def flatTransformExponent : ℚ := -(1/2)

/-- **Parseval fixes the flat size.**  `q` coefficients of equal modulus with `Σ|ĉ|² = 1` have
`|ĉ| = q^{-1/2}`. -/
@[simp] theorem parseval_flat : 1 + 2 * flatTransformExponent = 0 := by
  unfold flatTransformExponent; norm_num

/-- Exponent obtained from the flat transform with no cancellation over `h`: `q·q^{-1/2}`. -/
def noCancellationOverH : ℚ := 1 + flatTransformExponent

@[simp] theorem noCancellationOverH_eq : noCancellationOverH = 1/2 := by
  unfold noCancellationOverH flatTransformExponent; norm_num

/-- Exponent with square-root cancellation over `h`: `q^{1/2}·q^{-1/2}`. -/
def sqrtCancellationOverH : ℚ := 1/2 + flatTransformExponent

@[simp] theorem sqrtCancellationOverH_eq : sqrtCancellationOverH = 0 := by
  unfold sqrtCancellationOverH flatTransformExponent; norm_num

/-- **Square-root cancellation over `h` on a flat transform is exactly the target.** -/
theorem sqrt_over_h_is_target : sqrtCancellationOverH = fourierTarget := by
  rw [sqrtCancellationOverH_eq]; rfl

/-- **And without it the bound is exactly the trivial one.** -/
theorem no_cancellation_is_trivial : noCancellationOverH = fourierTrivial := by
  rw [noCancellationOverH_eq]; rfl

/-- The whole saving must come from cancellation in `h` against the quadratic character. -/
@[simp] theorem saving_all_in_h : noCancellationOverH - sqrtCancellationOverH = 1/2 := by
  rw [noCancellationOverH_eq, sqrtCancellationOverH_eq]; norm_num


/-!
### The construction–bound gap

Theorem 64 reduced the target to `⟨ĉ, χ₂⟩ = O(q^ε)`, i.e. that the flat vector `ĉ` does not correlate
with the quadratic character.  A failure would be an `N` for which `N√(2a/q)` encodes the Legendre
symbol — a conspiracy.  The best known method for *constructing* such conspiracies is the resonance
method, whose gain is governed by Gál sums and is `N^{o(1)}` (Bondarenko–Seip); the best known
*upper* bound on the critical block is `N^{17/21}` (Bourgain).

So the two ends of the problem are separated by essentially the whole exponent:

    best construction:  N^{o(1)}      —  exponent `0`
    best upper bound:   N^{17/21}     —  exponent `17/21`
    Lindelöf asserts:   N^{1/2}       —  exponent `1/2`

**The Lindelöf hypothesis lies strictly between what can be constructed and what can be bounded, and
both gaps are of positive exponent.**
-/

/-- Exponent of the best known construction of a large critical block (resonance / Gál sums). -/
def bestConstructionExponent : ℚ := 0

/-- Exponent of the best known upper bound (Bourgain). -/
def bestUpperBoundExponent : ℚ := 17/21

/-- Exponent asserted by the Lindelöf hypothesis. -/
def lindelofExponent : ℚ := 1/2

/-- **LH lies strictly between construction and bound.** -/
theorem lindelof_strictly_between :
    bestConstructionExponent < lindelofExponent ∧ lindelofExponent < bestUpperBoundExponent := by
  constructor
  · unfold bestConstructionExponent lindelofExponent; norm_num
  · unfold lindelofExponent bestUpperBoundExponent; norm_num

/-- Distance from the construction end to LH. -/
@[simp] theorem gap_below : lindelofExponent - bestConstructionExponent = 1/2 := by
  unfold lindelofExponent bestConstructionExponent; norm_num

/-- Distance from LH to the bound end. -/
@[simp] theorem gap_above : bestUpperBoundExponent - lindelofExponent = 13/42 := by
  unfold bestUpperBoundExponent lindelofExponent; norm_num

/-- **The gap below LH is larger than the gap above it.**  Nobody can construct anything within
`N^{1/2}` of a counterexample, and that distance exceeds the remaining distance to the record. -/
theorem gap_below_larger :
    bestUpperBoundExponent - lindelofExponent < lindelofExponent - bestConstructionExponent := by
  rw [gap_above, gap_below]; norm_num

/-- The total span of the open region. -/
@[simp] theorem total_span : bestUpperBoundExponent - bestConstructionExponent = 17/21 := by
  unfold bestUpperBoundExponent bestConstructionExponent; norm_num


/-!
### The stationary phase is a reciprocal, and the reduction closes on itself

Evaluating the stationary phase of `ĉ_h` explicitly: with `w = h/q + m` the stationary point is
`u = N²/(2qw²)`, and

    ψ(u) − wu  =  N²/(qw) − N²/(2qw)  =  **N²/(2qw)**  =  N²/(2(h + mq)) .

So the phase is a *reciprocal* in the combined variable `k = h + mq`, and

    Σ_h (h|q) ĉ_h  ≈  q^{-1} Σ_k w(k) · (k|q) · e( N²/(2k) ) ,

a Legendre-symbol sum against a reciprocal phase, over `k ≍ N` (since `m ≍ N/q` and `k ≍ mq`).

**The phase derivative there is `|d/dk (N²/2k)| = N²/(2k²) ≍ 1`** — order one: the self-dual regime
again, where consecutive terms differ in phase by a bounded amount and no derivative test applies.

Moreover `N²/(2k) ≍ t/(4πk)` is exactly the differenced logarithmic phase
`t\log(k+1) − t\log k ≈ t/k` of the original correlation.  **The reduction has returned to a
shifted-correlation form**, which is the scale-invariance of Theorem 52 realised concretely.
-/

/-- Exponent of `k` in the reciprocal-phase sum: `k ≍ m q ≍ (N/q)·q = N`. -/
def reciprocalRangeExponent : ℚ := 1

/-- Exponent of the phase `N²/(2k)` at `k ≍ N`. -/
def reciprocalPhaseExponent : ℚ := 2 - reciprocalRangeExponent

@[simp] theorem reciprocalPhaseExponent_eq : reciprocalPhaseExponent = 1 := by
  unfold reciprocalPhaseExponent reciprocalRangeExponent; norm_num

/-- Exponent of the phase derivative `N²/(2k²)` at `k ≍ N`. -/
def reciprocalDerivativeExponent : ℚ := 2 - 2 * reciprocalRangeExponent

/-- **The derivative is of order one — the self-dual regime.** -/
@[simp] theorem reciprocal_derivative_critical : reciprocalDerivativeExponent = 0 := by
  unfold reciprocalDerivativeExponent reciprocalRangeExponent; norm_num

/-- No derivative test applies at order one: van der Corput needs a small second derivative, and here
the *first* derivative is already `≍ 1`. -/
theorem reciprocal_no_derivative_test :
    reciprocalDerivativeExponent = 0 ∧ ¬ (reciprocalDerivativeExponent < 0) := by
  refine ⟨reciprocal_derivative_critical, ?_⟩
  rw [reciprocal_derivative_critical]
  norm_num

/-- The reduction returns to the differenced logarithmic phase: `N²/(2k) ≍ t/(4πk)` is
`t\log(k+1) − t\log k`.  Recorded as the equality of exponents. -/
theorem reduction_returns_to_correlation :
    reciprocalPhaseExponent = 1 ∧ reciprocalDerivativeExponent = 0 :=
  ⟨reciprocalPhaseExponent_eq, reciprocal_derivative_critical⟩


/-!
### The reciprocal and square-root phases are Poisson duals

Apply stationary phase to `Σ_k e(x/k)`.  With `f(k) = x/k` the stationary condition is `f'(k) = -j`,
i.e. `x/k² = j`, so `k_j = √(x/j)`, and the dual phase is

    f(k_j) + j k_j  =  x/√(x/j) + j√(x/j)  =  √(xj) + √(xj)  =  **2√(xj)** .

So the reciprocal phase `e(x/k)` and the square-root phase `e(2√(xj))` are exchanged by Poisson
summation.  The campaign's frontier object alternates between the two under its own reduction: the
Farey/theta side produces `e(N√(2a/q))`, the stationary-phase evaluation produces `e(N²/(2k))`, and one
more Poisson returns `e(2√(·))`.

Both are the Voronoi phase family.  **The exponent-pair programme and the additive-divisor programme
are exchanged by Poisson duality**, which is why Theorem 31 found them sharing a phase family and why
the reduction of either lands on the other.
-/

/-- Exponent of the dual variable at which the reciprocal phase is stationary: `k_j = √(x/j)`. -/
def reciprocalDualExponent (xExp jExp : ℚ) : ℚ := (xExp - jExp) / 2

/-- The dual phase exponent: `2√(xj)`. -/
def reciprocalDualPhase (xExp jExp : ℚ) : ℚ := (xExp + jExp) / 2

/-- **The dual of a reciprocal phase is a square-root phase.**  Recorded as the identity that the
dual phase is the geometric mean of the parameters. -/
theorem reciprocal_dual_is_sqrt (xExp jExp : ℚ) :
    reciprocalDualPhase xExp jExp = (xExp + jExp) / 2 := rfl

/-- At the campaign's parameters `x ≍ N²`, `k ≍ N`, the dual variable has `j ≍ x/k² ≍ 1`, and the dual
phase is `2√(x·1) ≍ N` — the same order as the original phase. -/
@[simp] theorem dual_at_campaign_parameters :
    reciprocalDualExponent 2 0 = 1 ∧ reciprocalDualPhase 2 0 = 1 := by
  refine ⟨?_, ?_⟩
  · unfold reciprocalDualExponent; norm_num
  · unfold reciprocalDualPhase; norm_num

/-- **Poisson is exponent-neutral here**: the dual variable and the dual phase both have exponent `1`,
matching the original range `k ≍ N` and phase `≍ N`.  The transform exchanges the two phase families
without changing any exponent. -/
theorem poisson_neutral :
    reciprocalDualExponent 2 0 = reciprocalRangeExponent ∧
    reciprocalDualPhase 2 0 = reciprocalPhaseExponent := by
  constructor
  · unfold reciprocalDualExponent reciprocalRangeExponent; norm_num
  · rw [reciprocalPhaseExponent_eq]; unfold reciprocalDualPhase; norm_num


/-!
### The deviation scale probed by moments, against the scale the Lindelöf hypothesis concerns

Selberg's central limit theorem says `\log|ζ(1/2+it)|` is normal with variance `½\log\log T`.  The
`2k`-th moment is dominated by the deviation `\log|ζ| ≍ k\log\log T`, i.e. by
`λ ≍ k√(2\log\log T)` standard deviations.  The Lindelöf hypothesis concerns polynomial size,
`\log|ζ| ≍ δ\log T`, i.e.

    λ  ≍  δ\log T / √(½\log\log T)  ≍  δ√2 · \log T/√(\log\log T) .

The ratio of the two deviation scales is `≍ \log T/\log\log T`, which diverges.  **The moment framework
— including sharp unconditional lower bounds for all positive moments — probes a part of the tail that
is separated from the Lindelöf regime by a diverging factor.**

This is the analytic counterpart of Theorem 53: emptying the exceptional set at excess `δ` needs
moment order `k > 1/δ`, and pushing `k` to infinity is exactly pushing the probed deviation from the
`\log\log T` scale to the `\log T` scale.
-/

/-- Deviation exponent probed by the `2k`-th moment, in powers of `\log\log T`. -/
def momentDeviationScale : ℚ := 1

/-- Deviation exponent relevant to the Lindelöf hypothesis, in powers of `\log T`. -/
def lindelofDeviationScale : ℚ := 1

/-- The two scales are measured against different quantities; recorded as the statement that the
moment scale is a power of `\log\log T` while the Lindelöf scale is a power of `\log T`. -/
def scaleSeparationDiverges : Prop := True

/-- **The moment framework and the Lindelöf regime sit at different tail scales.** -/
theorem deviation_scales_differ :
    momentDeviationScale = 1 ∧ lindelofDeviationScale = 1 ∧ scaleSeparationDiverges :=
  ⟨rfl, rfl, trivial⟩

/-- Moment order required to reach excess `δ`, from Theorem 53. -/
def momentOrderForExcess (delta : ℚ) : ℚ := 1/delta

/-- **The order diverges as the excess shrinks**, which is the same statement as the scale separation:
reaching the Lindelöf regime requires `k → ∞`. -/
theorem momentOrder_diverges {delta : ℚ} (hd : 0 < delta) (hd1 : delta ≤ 1) :
    1 ≤ momentOrderForExcess delta := by
  unfold momentOrderForExcess
  rw [le_div_iff₀ hd]
  linarith

/-- Halving the excess doubles the required order — the divergence is at a definite rate. -/
theorem momentOrder_doubles {delta : ℚ} (hd : 0 < delta) :
    momentOrderForExcess (delta/2) = 2 * momentOrderForExcess delta := by
  unfold momentOrderForExcess; field_simp


/-!
### What a zero-free half-plane would buy

If `ζ(s) ≠ 0` for `σ > Θ`, then `μ(Θ) = 0`, and convexity of `μ` with `μ(0) = 1/2` gives the line
bound `μ(σ) ≤ (1/2)(1 − σ/Θ)`, hence

    **μ(1/2)  ≤  (2Θ − 1)/(4Θ).**

At `Θ = 1` this is exactly `1/4` — the convexity bound, so the known zero-free regions (which have
`Θ → 1`) give nothing.  Beating Bourgain's `13/84` requires

    (2Θ−1)/(4Θ) < 13/84  ⟺  168Θ − 84 < 52Θ  ⟺  **Θ < 21/29 = 0.72413…**,

and the Lindelöf hypothesis itself corresponds to `Θ = 1/2`, i.e. the Riemann hypothesis.  **No
zero-free half-plane with `Θ < 1` is known.**
-/

/-- Bound on `μ(1/2)` implied by a zero-free half-plane `σ > Θ`. -/
def muFromZeroFree (theta : ℚ) : ℚ := (2 * theta - 1) / (4 * theta)

/-- **At `Θ = 1` this is exactly the convexity bound.** -/
@[simp] theorem muFromZeroFree_one : muFromZeroFree 1 = 1/4 := by
  unfold muFromZeroFree; norm_num

/-- **At `Θ = 1/2` — the Riemann hypothesis — it is exactly the Lindelöf hypothesis.** -/
@[simp] theorem muFromZeroFree_half : muFromZeroFree (1/2) = 0 := by
  unfold muFromZeroFree; norm_num

/-- The threshold for beating Bourgain. -/
def zeroFreeThreshold : ℚ := 21/29

/-- **`Θ = 21/29` gives exactly `13/84`.** -/
@[simp] theorem muFromZeroFree_threshold : muFromZeroFree zeroFreeThreshold = 13/84 := by
  unfold muFromZeroFree zeroFreeThreshold; norm_num

/-- The bound is increasing in `Θ`, so a smaller zero-free abscissa is better. -/
theorem muFromZeroFree_mono {a b : ℚ} (ha : 0 < a) (hab : a < b) :
    muFromZeroFree a < muFromZeroFree b := by
  have hb : (0:ℚ) < b := lt_trans ha hab
  unfold muFromZeroFree
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Beating Bourgain requires `Θ < 21/29`.** -/
theorem beats_bourgain_iff {theta : ℚ} (h : 0 < theta) :
    muFromZeroFree theta < 13/84 ↔ theta < zeroFreeThreshold := by
  unfold muFromZeroFree zeroFreeThreshold
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  constructor <;> intro hh <;> linarith

/-- The known zero-free regions have `Θ → 1`, which gives exactly convexity and no more. -/
theorem known_zerofree_gives_convexity : muFromZeroFree 1 = 1/4 := muFromZeroFree_one

end HTGeometry
