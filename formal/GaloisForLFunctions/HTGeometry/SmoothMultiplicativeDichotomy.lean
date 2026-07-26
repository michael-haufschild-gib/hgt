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

end HTGeometry
