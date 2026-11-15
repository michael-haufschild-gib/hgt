import GaloisForLFunctions.MetaplecticMobiusDescent.MobiusBecomesACubicGaussCoefficient
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Nonprincipal projection on the arithmetic residue field

The sextic residue character extracts the inverse-character coefficient and
annihilates the constant and direct-character modes. Normalizing by the number
of nonzero residues gives a contraction for the mean absolute value.
-/

noncomputable section
open Complex NumberField IsDedekindDomain Finset
open scoped Classical

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

variable (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)

/-- The nonprincipal coefficient, averaged over the actual residue field. -/
def residueTargetProjection (f : O ⧸ P → ℂ) : ℂ :=
  (Fintype.card (O ⧸ P)ˣ : ℂ)⁻¹ *
    ∑ a : O ⧸ P, complexSexticChar P hg a * f a

/-- Mean absolute value over nonzero residues; the zero residue has weight zero. -/
def residueRowMeanNorm (f : O ⧸ P → ℂ) : ℝ :=
  (Fintype.card (O ⧸ P)ˣ : ℝ)⁻¹ * ∑ a : O ⧸ P, if a = 0 then 0 else ‖f a‖

theorem norm_sexticChar_eq_indicator (a : O ⧸ P) :
    ‖complexSexticChar P hg a‖ = if a = 0 then 0 else 1 := by
  by_cases ha : a = 0
  · subst a
    rw [MulChar.map_zero, norm_zero, if_pos rfl]
  · rw [if_neg ha]
    have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    exact Complex.norm_eq_one_of_mem_rootsOfUnity
      ((complexSexticChar P hg).apply_mem_rootsOfUnity hu.unit)

/-- Extraction loses no factor depending on the residue-field size. -/
theorem norm_residueTargetProjection_le (f : O ⧸ P → ℂ) :
    ‖residueTargetProjection P hg f‖ ≤ residueRowMeanNorm P f := by
  unfold residueTargetProjection residueRowMeanNorm
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    ‖∑ a : O ⧸ P, complexSexticChar P hg a * f a‖ ≤
        ∑ a : O ⧸ P, ‖complexSexticChar P hg a * f a‖ := norm_sum_le _ _
    _ = ∑ a : O ⧸ P, if a = 0 then 0 else ‖f a‖ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [norm_mul, norm_sexticChar_eq_indicator]
      split_ifs <;> simp only [zero_mul, one_mul]

theorem residueTargetProjection_sub (f g : O ⧸ P → ℂ) :
    residueTargetProjection P hg (fun a => f a - g a) =
      residueTargetProjection P hg f - residueTargetProjection P hg g := by
  simp only [residueTargetProjection, mul_sub, Finset.sum_sub_distrib]

theorem residueTargetProjection_mul (c : ℂ) (f : O ⧸ P → ℂ) :
    residueTargetProjection P hg (fun a => c * f a) =
      c * residueTargetProjection P hg f := by
  unfold residueTargetProjection
  have he (a : O ⧸ P) : complexSexticChar P hg a * (c * f a) =
      c * (complexSexticChar P hg a * f a) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

/-- Scaling the observed rows costs exactly the modulus of the scalar. -/
theorem norm_residueTargetProjection_mul_le (c : ℂ) (f : O ⧸ P → ℂ) :
    ‖residueTargetProjection P hg (fun a => c * f a)‖ ≤
      ‖c‖ * residueRowMeanNorm P f := by
  rw [residueTargetProjection_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_residueTargetProjection_le P hg f) (norm_nonneg c)

/-- Perturbing arithmetic row values costs at most their mean absolute error. -/
theorem norm_residueTargetProjection_sub_le (f g : O ⧸ P → ℂ) :
    ‖residueTargetProjection P hg f - residueTargetProjection P hg g‖ ≤
      residueRowMeanNorm P (fun a => f a - g a) := by
  rw [← residueTargetProjection_sub]
  exact norm_residueTargetProjection_le P hg _

/-- The inverse-character coefficient survives; constant and direct modes vanish. -/
theorem residueTargetProjection_three_modes (C L T : ℂ) :
    residueTargetProjection P hg (fun a =>
      C + L * complexSexticChar P hg a - T * (complexSexticChar P hg a)⁻¹) = -T := by
  let χ := complexSexticChar P hg
  have hsum : ∑ a : O ⧸ P, χ a = 0 :=
    MulChar.sum_eq_zero_of_ne_one (complexSexticChar_ne_one P hg)
  have hsq : ∑ a : O ⧸ P, (χ ^ 2) a = 0 := by
    change ∑ a : O ⧸ P, (complexSexticChar P hg ^ 2) a = 0
    rw [(complexSexticChar_powers P hg).1]
    exact MulChar.sum_eq_zero_of_ne_one (complexCubicChar_ne_one P hg)
  have hterm (a : O ⧸ P) :
      χ a * (C + L * χ a - T * (χ a)⁻¹) =
        C * χ a + L * (χ ^ 2) a - T * (1 : MulChar (O ⧸ P) ℂ) a := by
    rw [MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0)]
    have hi : χ a * (χ a)⁻¹ = (1 : MulChar (O ⧸ P) ℂ) a := by
      rw [← MulChar.inv_apply_eq_inv', ← MulChar.mul_apply, mul_inv_cancel]
    calc
      _ = C * χ a + L * χ a ^ 2 - T * (χ a * (χ a)⁻¹) := by ring
      _ = _ := by rw [hi]
  change (Fintype.card (O ⧸ P)ˣ : ℂ)⁻¹ *
    (∑ a : O ⧸ P, χ a * (C + L * χ a - T * (χ a)⁻¹)) = -T
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, hsum, hsq, MulChar.sum_one_eq_card_units]
  have hc : (Fintype.card (O ⧸ P)ˣ : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [mul_zero, zero_add, zero_sub, mul_neg]
  rw [mul_comm T (Fintype.card (O ⧸ P)ˣ : ℂ), ← mul_assoc,
    inv_mul_cancel₀ hc, one_mul]

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
