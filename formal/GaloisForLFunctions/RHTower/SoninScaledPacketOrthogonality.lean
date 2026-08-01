import GaloisForLFunctions.HTGeometry.OrthonormalNormalize
import GaloisForLFunctions.RHTower.SoninScaledPacketBandFraction
import GaloisForLFunctions.RHTower.SoninScaledPacketSupport

/-!
# Rescaled packets on disjoint annuli are orthogonal

Two rescaled packets whose annuli do not meet vanish on each other's support, so their pointwise
product vanishes identically and the pairing is zero.  Nothing but the supports enters: the carriers
are arbitrary and unrelated.

Since the energy floor makes each packet nonzero, an ordered family of separated annuli therefore
normalizes to an orthonormal family, of size as large as the shell can be cut.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped InnerProduct InnerProductSpace

/-- **Exact orthogonality.**  Rescaled packets on separated annuli pair to zero. -/
theorem inner_soninScaledPacketEven_eq_zero_of_disjoint
    (m₁ δ₁ m₂ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hm₁ : 0 ≤ m₁)
    (hsep : m₁ + δ₁ ≤ m₂ - δ₂) (κ₁ κ₂ : ℝ) :
    ⟪soninScaledPacketEven m₁ δ₁ κ₁ hδ₁, soninScaledPacketEven m₂ δ₂ κ₂ hδ₂⟫_ℂ = 0 := by
  have hcoe : ⟪soninScaledPacketEven m₁ δ₁ κ₁ hδ₁, soninScaledPacketEven m₂ δ₂ κ₂ hδ₂⟫_ℂ =
      ⟪soninScaledPacketL2 m₁ δ₁ κ₁ hδ₁, soninScaledPacketL2 m₂ δ₂ κ₂ hδ₂⟫_ℂ := rfl
  rw [hcoe, MeasureTheory.L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [soninScaledPacketL2_coeFn m₁ δ₁ κ₁ hδ₁,
    soninScaledPacketL2_coeFn m₂ δ₂ κ₂ hδ₂] with x hx₁ hx₂
  show (inner ℂ ((soninScaledPacketL2 m₁ δ₁ κ₁ hδ₁ : ℝ → ℂ) x)
    ((soninScaledPacketL2 m₂ δ₂ κ₂ hδ₂ : ℝ → ℂ) x) : ℂ) = (0 : ℝ → ℂ) x
  rw [hx₁, hx₂]
  by_cases hle : |x| ≤ m₂ - δ₂
  · rw [soninScaledPacket_eq_zero_of_abs_le m₂ δ₂ κ₂ hδ₂ hle]
    simp
  · push Not at hle
    rw [soninScaledPacket_eq_zero_of_le_abs m₁ δ₁ κ₁ hδ₁ hm₁ (le_trans hsep hle.le)]
    simp

/-- The same pairing read in the other order. -/
theorem inner_soninScaledPacketEven_eq_zero_of_disjoint'
    (m₁ δ₁ m₂ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hm₁ : 0 ≤ m₁)
    (hsep : m₁ + δ₁ ≤ m₂ - δ₂) (κ₁ κ₂ : ℝ) :
    ⟪soninScaledPacketEven m₂ δ₂ κ₂ hδ₂, soninScaledPacketEven m₁ δ₁ κ₁ hδ₁⟫_ℂ = 0 := by
  have h := inner_soninScaledPacketEven_eq_zero_of_disjoint m₁ δ₁ m₂ δ₂ hδ₁ hδ₂ hm₁ hsep κ₁ κ₂
  rw [← inner_conj_symm, h, map_zero]

/-- A rescaled packet with a mean below one and a small reference-square tail is nonzero. -/
theorem soninScaledPacketEven_ne_zero (m δ w : ℝ) (hδ : 0 < δ) (hm : δ < m)
    (hmean : |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤ 1)
    (hSq : soninRefSqTailSup (δ * |w|) ≤ (∫ y : ℝ, soninUnitBumpSq y) / 20) :
    soninScaledPacketEven m δ (2 * Real.pi * w) hδ ≠ 0 := by
  intro hzero
  have hfloor := norm_sq_soninScaledPacketEven_ge_half m δ w hδ hm hmean hSq
  rw [hzero, norm_zero] at hfloor
  have hI : 0 < ∫ y : ℝ, soninUnitBumpSq y := integral_soninUnitBumpSq_pos
  nlinarith [hfloor, hδ, hI]

/-- **An orthonormal family from separated annuli.**  Ordered annuli with pairwise gaps give, after
normalizing, an orthonormal family of rescaled packets. -/
theorem orthonormal_soninScaledPacketEven
    {ι : Type*} [LinearOrder ι] (m δ w : ι → ℝ) (hδ : ∀ i, 0 < δ i) (hm : ∀ i, δ i < m i)
    (hmpos : ∀ i, 0 ≤ m i)
    (hsep : ∀ i j : ι, i < j → m i + δ i ≤ m j - δ j)
    (hmean : ∀ i, |soninScaledPacketMean (m i) (δ i) (2 * Real.pi * w i)| ≤ 1)
    (hSq : ∀ i, soninRefSqTailSup (δ i * |w i|) ≤ (∫ y : ℝ, soninUnitBumpSq y) / 20) :
    Orthonormal ℂ fun i : ι =>
      ((‖soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i)‖ : ℂ))⁻¹ •
        soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i) := by
  refine orthonormal_normalize
    (fun i => soninScaledPacketEven_ne_zero (m i) (δ i) (w i) (hδ i) (hm i) (hmean i) (hSq i))
    fun i j hij => ?_
  rcases lt_or_gt_of_ne hij with h | h
  · exact inner_soninScaledPacketEven_eq_zero_of_disjoint (m i) (δ i) (m j) (δ j)
      (hδ i) (hδ j) (hmpos i) (hsep i j h) _ _
  · exact inner_soninScaledPacketEven_eq_zero_of_disjoint' (m j) (δ j) (m i) (δ i)
      (hδ j) (hδ i) (hmpos j) (hsep j i h) _ _

end RHTower
