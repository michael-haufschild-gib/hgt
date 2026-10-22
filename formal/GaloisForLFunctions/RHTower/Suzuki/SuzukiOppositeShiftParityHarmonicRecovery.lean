import GaloisForLFunctions.RHTower.Suzuki.SuzukiExteriorPoleTomography
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam

/-!
# Suzuki opposite-shift parity and harmonic recovery

Suzuki's conjectural reciprocal-logarithmic characteristic target is the zero fibre

`R_0(z) = z² XiC(z) / XiC'(z)`.

The auxiliary form shift produces the affine pencil

`R_eta(z) = z² XiC(z) / (XiC'(z) - eta XiC(z))`.

These fibres are not individually compatible with the odd parity of the canonical Donoghue
carrier.  Centered Xi parity exchanges the two opposite fibres exactly:

`R_eta(-z) = -R_(-eta)(z)`.

Consequently the zero fibre is the unique odd member of the pencil.  Nevertheless an arbitrary
finite opposite pair still recovers it: reciprocal coordinates have zero as their midpoint, or,
away from poles, `R_0` is the harmonic mean of `R_eta` and `R_(-eta)`.

For the corrected exterior multiplier `G_eta = R_eta⁻¹`, the same statement becomes linear.
Its symmetric opposite-shift projection is exactly `G_0`; its antisymmetric projection is Xi-free.
The corresponding exterior remainders obey the same decomposition.  Thus a paired finite-shift
source can target Suzuki's distinguished zero fibre without requiring the shift to converge to
zero, whereas a single nonzero fibre cannot be identified with an odd canonical carrier.

All results are unconditional.  No RH assumption and no numerical computation occur here.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Reflection exchange and parity rigidity -/

/-- Centered Xi parity exchanges the opposite affine denominator fibres. -/
theorem suzukiShiftedXiDenominator_neg (eta z : ℂ) :
    suzukiShiftedXiDenominator eta (-z) =
      -suzukiShiftedXiDenominator (-eta) z := by
  rw [suzukiShiftedXiDenominator, suzukiShiftedXiDenominator,
    deriv_XiC_neg, XiC_even]
  ring

/-- Reflection does not preserve a general shifted target: it exchanges `eta` with `-eta`. -/
theorem suzukiShiftedXiTarget_neg (eta z : ℂ) :
    suzukiShiftedXiTarget eta (-z) =
      -suzukiShiftedXiTarget (-eta) z := by
  rw [suzukiShiftedXiTarget, suzukiShiftedXiTarget,
    suzukiShiftedXiDenominator_neg, XiC_even]
  ring

/-- **Parity classifier.**  The zero fibre is the unique odd member of the complete shifted Xi
pencil.  The reverse implication is detected at `i`, which is unconditionally Xi-regular. -/
theorem suzukiShiftedXiTarget_odd_iff (eta : ℂ) :
    Function.Odd (suzukiShiftedXiTarget eta) ↔ eta = 0 := by
  constructor
  · intro hodd
    have href := suzukiShiftedXiTarget_neg eta I
    have heq : suzukiShiftedXiTarget (-eta) I =
        suzukiShiftedXiTarget eta I := by
      have ho := hodd I
      linear_combination href - ho
    have hXi : XiC I ≠ 0 := by
      apply XiC_ne_zero_of_abs_re_le_four
      norm_num
    have htrans := suzukiShiftedXiTarget_reciprocal_translation
      (alpha := eta) (beta := -eta) (z := I) I_ne_zero hXi
    rw [heq] at htrans
    have htwo : eta * 2 = 0 := by
      linear_combination -htrans
    exact (mul_eq_zero.mp htwo).resolve_right (by norm_num)
  · rintro rfl
    intro z
    simpa using suzukiShiftedXiTarget_neg 0 z

/-- Every nonzero shifted fibre fails the odd symmetry required of Suzuki's parity-normalized
Donoghue carrier. -/
theorem suzukiShiftedXiTarget_not_odd {eta : ℂ} (heta : eta ≠ 0) :
    ¬Function.Odd (suzukiShiftedXiTarget eta) := by
  exact fun hodd => heta ((suzukiShiftedXiTarget_odd_iff eta).mp hodd)

/-! ## Opposite-shift harmonic recovery -/

/-- Reciprocal coordinates of opposite fibres have the zero fibre as their exact midpoint.  No
shifted-denominator hypothesis is needed; only the common Xi numerator must be nonzero. -/
theorem suzukiShiftedXiTarget_opposite_reciprocal_midpoint
    {eta z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0) :
    z ^ (2 : ℕ) / suzukiShiftedXiTarget eta z +
        z ^ (2 : ℕ) / suzukiShiftedXiTarget (-eta) z =
      2 * (z ^ (2 : ℕ) / suzukiShiftedXiTarget 0 z) := by
  have hp := suzukiShiftedXiTarget_reciprocal_translation
    (alpha := eta) (beta := 0) (z := z) hz hXi
  have hm := suzukiShiftedXiTarget_reciprocal_translation
    (alpha := -eta) (beta := 0) (z := z) hz hXi
  linear_combination -(hp + hm)

/-- Away from the three displayed poles, the zero fibre is the harmonic mean of the opposite
shift fibres, written as a division-free cross identity. -/
theorem suzukiShiftedXiTarget_opposite_harmonic_cross
    {eta z : ℂ}
    (hp : suzukiShiftedXiDenominator eta z ≠ 0)
    (hm : suzukiShiftedXiDenominator (-eta) z ≠ 0)
    (h0 : suzukiShiftedXiDenominator 0 z ≠ 0) :
    (suzukiShiftedXiTarget eta z + suzukiShiftedXiTarget (-eta) z) *
        suzukiShiftedXiTarget 0 z =
      2 * suzukiShiftedXiTarget eta z * suzukiShiftedXiTarget (-eta) z := by
  simp only [suzukiShiftedXiTarget]
  field_simp [hp, hm, h0]
  simp only [suzukiShiftedXiDenominator]
  ring

/-! ## Exact symmetric and antisymmetric exterior projections -/

/-- The symmetric opposite-shift projection of the corrected Xi multiplier is exactly the
distinguished zero-shift multiplier.  This identity is pointwise totalized and hypothesis-free. -/
theorem suzukiShiftedXiMultiplier_opposite_average (eta z : ℂ) :
    suzukiShiftedXiMultiplier eta z + suzukiShiftedXiMultiplier (-eta) z =
      2 * suzukiShiftedXiMultiplier 0 z := by
  rw [suzukiShiftedXiMultiplier_eq, suzukiShiftedXiMultiplier_eq,
    suzukiShiftedXiMultiplier_eq]
  simp only [suzukiShiftedXiDenominator]
  ring

/-- With a common characteristic factor and interval part, symmetric opposite-shift averaging
projects the complete corrected exterior remainder exactly onto its zero-shift RH channel. -/
theorem suzukiExteriorRemainder_opposite_average
    (eta : ℂ) (W intervalPart : ℂ → ℂ) (z : ℂ) :
    suzukiExteriorRemainder eta W intervalPart z +
        suzukiExteriorRemainder (-eta) W intervalPart z =
      2 * suzukiExteriorRemainder 0 W intervalPart z := by
  rw [suzukiExteriorRemainder, suzukiExteriorRemainder,
    suzukiExteriorRemainder]
  have h := suzukiShiftedXiMultiplier_opposite_average eta z
  linear_combination W z * h

/-- Off the common numerator divisor, the antisymmetric multiplier projection is Xi-free: only
the explicit shift coordinate remains. -/
theorem suzukiShiftedXiMultiplier_opposite_difference
    {eta z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0) :
    z ^ (2 : ℕ) * (suzukiShiftedXiMultiplier (-eta) z -
        suzukiShiftedXiMultiplier eta z) = 2 * eta := by
  rw [suzukiShiftedXiMultiplier_eq, suzukiShiftedXiMultiplier_eq]
  field_simp [hz, hXi]
  simp only [suzukiShiftedXiDenominator]
  ring

/-- The antisymmetric exterior projection cancels both the finite interval part and the Xi
multiplier, leaving the explicit source factor `2 eta W / z²`. -/
theorem suzukiExteriorRemainder_opposite_difference
    {eta z : ℂ} (W intervalPart : ℂ → ℂ)
    (hz : z ≠ 0) (hXi : XiC z ≠ 0) :
    z ^ (2 : ℕ) * (suzukiExteriorRemainder (-eta) W intervalPart z -
        suzukiExteriorRemainder eta W intervalPart z) =
      2 * eta * W z := by
  rw [suzukiExteriorRemainder, suzukiExteriorRemainder]
  have h := suzukiShiftedXiMultiplier_opposite_difference (eta := eta) hz hXi
  linear_combination W z * h

/-! ## Paired exterior RH frontier -/

/-- **Opposite-shift exterior criterion for RH.**  For one common all-real Suzuki characteristic
member and one common entire interval part, RH is equivalent to off-real holomorphy of the
symmetric opposite-shift exterior channel.  The exact average theorem reduces this channel to
twice the zero-shift exterior remainder, so the criterion neither assumes nor hides `eta → 0`. -/
theorem riemannHypothesis_iff_suzukiExteriorRemainder_opposite_average_analytic_offReal
    {A E intervalPart : ℂ → ℂ} {eta u : ℂ}
    (hA : ∀ z, AnalyticAt ℂ A z) (hE : ∀ z, AnalyticAt ℂ E z)
    (hI : ∀ z, AnalyticAt ℂ intervalPart z)
    (hreal : GaloisForLFunctions.RHTower.SuzukiAllAngleRealZeros A E)
    (hu : ‖u‖ = 1) :
    RiemannHypothesis ↔
      ∀ z : ℂ, z.im ≠ 0 →
        AnalyticAt ℂ (fun w =>
          suzukiExteriorRemainder eta
              (GaloisForLFunctions.RHTower.suzukiCharacteristicPencil A E u) intervalPart w +
            suzukiExteriorRemainder (-eta)
              (GaloisForLFunctions.RHTower.suzukiCharacteristicPencil A E u) intervalPart w) z := by
  let W := GaloisForLFunctions.RHTower.suzukiCharacteristicPencil A E u
  have hcriterion := riemannHypothesis_iff_suzukiExteriorRemainder_analytic_offReal
    (eta := (0 : ℂ)) hA hE hI hreal hu
  have hpair : (fun w =>
      suzukiExteriorRemainder eta W intervalPart w +
        suzukiExteriorRemainder (-eta) W intervalPart w) =
      fun w => 2 * suzukiExteriorRemainder 0 W intervalPart w := by
    funext w
    exact suzukiExteriorRemainder_opposite_average eta W intervalPart w
  constructor
  · intro hRH z hz
    rw [hpair]
    exact analyticAt_const.mul (hcriterion.mp hRH z hz)
  · intro hsum
    apply hcriterion.mpr
    intro z hz
    have h := hsum z hz
    rw [hpair] at h
    have hscaled : AnalyticAt ℂ (fun w => (2 : ℂ)⁻¹ *
        (2 * suzukiExteriorRemainder 0 W intervalPart w)) z := by
      exact analyticAt_const.mul h
    have heq : (fun w => (2 : ℂ)⁻¹ *
        (2 * suzukiExteriorRemainder 0 W intervalPart w)) =
        suzukiExteriorRemainder 0 W intervalPart := by
      funext w
      ring
    rwa [heq] at hscaled

end

end RHTower
