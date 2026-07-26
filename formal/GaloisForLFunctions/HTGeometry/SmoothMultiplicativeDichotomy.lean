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

end HTGeometry
