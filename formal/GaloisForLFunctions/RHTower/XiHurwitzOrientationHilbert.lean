import GaloisForLFunctions.RHTower.XiHurwitzOrientationEnergy
import GaloisForLFunctions.HilbertSchmidtMatrix

/-!
# Hilbert realization of the Xi--Hurwitz orientation energy

The scalar orientation energy is the squared norm of a canonical signed vector on the
multiplicity-exact Xi divisor.  This places the RH orientation law directly on the same `ell^2`
carrier used by the Xi Weil and Hilbert--Schmidt constructions.
-/

open Complex MeromorphicOn

namespace RHTower

noncomputable section

/-- The signed, radius-normalized Hurwitz orientation coordinate of one Xi-zero copy. -/
def xiHurwitzOrientationCoordinate (q : XiZeroCopy) : ℂ :=
  (((xiHurwitzMonodromyCharacter q.1).im /
      (‖xiHurwitzMonodromyCharacter q.1‖ * ‖(q.1 : ℂ) - 1 / 2‖) : ℝ) : ℂ)

theorem norm_sq_xiHurwitzOrientationCoordinate (q : XiZeroCopy) :
    ‖xiHurwitzOrientationCoordinate q‖ ^ 2 =
      xiHurwitzOrientationDefect q.1 / ‖(q.1 : ℂ) - 1 / 2‖ ^ 2 := by
  have hchar : ‖xiHurwitzMonodromyCharacter q.1‖ ≠ 0 :=
    (norm_pos_iff.mpr (xiHurwitzMonodromyCharacter_ne_zero q.1)).ne'
  have hcenter : ‖(q.1 : ℂ) - 1 / 2‖ ≠ 0 :=
    (norm_pos_iff.mpr (sub_ne_zero.mpr (xi_divisor_support_ne_half q.1))).ne'
  rw [xiHurwitzOrientationCoordinate, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, xiHurwitzOrientationDefect]
  field_simp [hchar, hcenter]

theorem tsum_norm_sq_xiHurwitzOrientationCoordinate_fiber (ρ : XiDivisorSupport) :
    (∑' j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
      ‖xiHurwitzOrientationCoordinate ⟨ρ, j⟩‖ ^ 2) =
        xiHurwitzOrientationEnergyTerm ρ := by
  rw [tsum_fintype]
  simp only [norm_sq_xiHurwitzOrientationCoordinate, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnonneg : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) :=
    le_of_lt (xi_divisor_pos_on_support ρ)
  have hcast :
      ((Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) : ℕ) : ℝ) =
        ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  rw [hcast, xiHurwitzOrientationEnergyTerm, xiHurwitzOrientationWeight]
  ring

theorem summable_norm_sq_xiHurwitzOrientationCoordinate :
    Summable (fun q : XiZeroCopy => ‖xiHurwitzOrientationCoordinate q‖ ^ 2) := by
  rw [summable_sigma_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · intro ρ
    exact (hasSum_fintype _).summable
  · simpa only [tsum_norm_sq_xiHurwitzOrientationCoordinate_fiber] using
      xiHurwitzOrientationEnergyTerm_summable

/-- The canonical Xi--Hurwitz orientation vector in the multiplicity-exact Xi `ell^2` space. -/
def xiHurwitzOrientationVector : lp (fun _ : XiZeroCopy => ℂ) 2 :=
  ⟨xiHurwitzOrientationCoordinate,
    HilbertSchmidt.memℓp_of_sq summable_norm_sq_xiHurwitzOrientationCoordinate⟩

@[simp] theorem xiHurwitzOrientationVector_apply (q : XiZeroCopy) :
    xiHurwitzOrientationVector q = xiHurwitzOrientationCoordinate q := rfl

/-- **Hilbert norm identity.**  The scalar Xi--Hurwitz orientation energy is exactly the squared
`ell^2` norm of the canonical signed orientation vector. -/
theorem norm_sq_xiHurwitzOrientationVector :
    ‖xiHurwitzOrientationVector‖ ^ 2 = xiHurwitzOrientationEnergy := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  change (∑' q : XiZeroCopy, ‖xiHurwitzOrientationCoordinate q‖ ^ 2) =
    xiHurwitzOrientationEnergy
  have hsum := summable_norm_sq_xiHurwitzOrientationCoordinate
  rw [hsum.tsum_sigma, xiHurwitzOrientationEnergy]
  apply tsum_congr
  exact tsum_norm_sq_xiHurwitzOrientationCoordinate_fiber

theorem xiHurwitzOrientationVector_eq_zero_iff_energy_eq_zero :
    xiHurwitzOrientationVector = 0 ↔ xiHurwitzOrientationEnergy = 0 := by
  constructor
  · intro hzero
    rw [← norm_sq_xiHurwitzOrientationVector, hzero, norm_zero, zero_pow]
    norm_num
  · intro henergy
    apply norm_eq_zero.mp
    have hsq : ‖xiHurwitzOrientationVector‖ ^ 2 = 0 := by
      rw [norm_sq_xiHurwitzOrientationVector, henergy]
    nlinarith [norm_nonneg xiHurwitzOrientationVector]

/-- **Hilbert-space RH law.**  RH is exactly vanishing of the canonical Xi--Hurwitz orientation
vector. -/
theorem riemannHypothesis_iff_xiHurwitzOrientationVector_eq_zero :
    RiemannHypothesis ↔ xiHurwitzOrientationVector = 0 :=
  riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.trans
    xiHurwitzOrientationVector_eq_zero_iff_energy_eq_zero.symm

/-- An explicit off-critical-line zero has a nonzero coordinate in the canonical orientation
vector. -/
theorem xiHurwitzOrientationVector_coordinate_ne_zero
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    xiHurwitzOrientationVector q ≠ 0 := by
  rw [xiHurwitzOrientationVector_apply, xiHurwitzOrientationCoordinate]
  exact Complex.ofReal_ne_zero.mpr (div_ne_zero
    (by
      intro him
      apply hq
      exact (xiHurwitzOrientationDefect_eq_zero_iff_re_eq_half q.1).mp
        ((xiHurwitzOrientationDefect_eq_zero_iff q.1).mpr him))
    (mul_ne_zero
      (norm_ne_zero_iff.mpr (xiHurwitzMonodromyCharacter_ne_zero q.1))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (xi_divisor_support_ne_half q.1)))))

end

end RHTower
