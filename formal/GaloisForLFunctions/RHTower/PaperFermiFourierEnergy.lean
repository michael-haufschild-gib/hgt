import GaloisForLFunctions.RHTower.PaperFermiFourierProfiles

/-! # Exact spectral error and the arithmetic zero mode

Every signed cross term is retained inside the residual Fourier coefficient.
Finite spectral windows increase to the full native Haar approximation error.
-/

namespace RHTower
noncomputable section
open MeasureTheory Filter Topology Set GaloisForLFunctions.HTGeometry
open scoped BigOperators

private theorem unit_coeff_lift (f : ℝ → ℂ) (k : ℤ) :
    _root_.fourierCoeff (AddCircle.liftIoc 1 0 f) k = fourierCoeffOn zero_lt_one f k := by
  simpa only [zero_add] using (_root_.fourierCoeff_liftIoc_eq (T := 1) (a := 0) f k)

private theorem unit_coeff_add (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1))) (k : ℤ) :
    fourierCoeffOn zero_lt_one (fun t => f t + g t) k =
      fourierCoeffOn zero_lt_one f k + fourierCoeffOn zero_lt_one g k := by
  have hf' : Integrable (AddCircle.liftIoc 1 0 f) AddCircle.haarAddCircle := by
    have h : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (0 + 1))) := by simpa using hf
    exact h.memLp_liftIoc.haarAddCircle.integrable (by norm_num)
  have hg' : Integrable (AddCircle.liftIoc 1 0 g) AddCircle.haarAddCircle := by
    have h : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (0 + 1))) := by simpa using hg
    exact h.memLp_liftIoc.haarAddCircle.integrable (by norm_num)
  rw [← unit_coeff_lift, ← unit_coeff_lift, ← unit_coeff_lift]
  exact congrFun (_root_.fourierCoeff.add hf' hg') k

theorem paperFermiCombination_coeff {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (k : ℤ) :
    fourierCoeffOn zero_lt_one (fermiNymanCombination c a) k =
      ∑ j, c j * paperFermiGeneratorCoeff (a j) k := by
  have hi (j : Fin n) :
      Integrable (fun y : AddCircle (1 : ℝ) => c j * AddCircle.liftIoc 1 0 (fermiNymanGen (a j)) y)
        AddCircle.haarAddCircle := by
    apply Integrable.const_mul
    have h : MemLp (fermiNymanGen (a j)) 2 (volume.restrict (Ioc (0 : ℝ) (0 + 1))) :=
      by simpa using paperFermiGenerator_memLp (a j)
    exact h.memLp_liftIoc.haarAddCircle.integrable (by norm_num)
  have h := congrFun (_root_.fourierCoeff.sum Finset.univ
    (fun j y => c j * AddCircle.liftIoc 1 0 (fermiNymanGen (a j)) y) (fun j _ => hi j)) k
  have he : (∑ j : Fin n, fun y : AddCircle (1 : ℝ) =>
      c j * AddCircle.liftIoc 1 0 (fermiNymanGen (a j)) y) =
      AddCircle.liftIoc 1 0 (fermiNymanCombination c a) := by
    ext y
    simp only [Finset.sum_apply]
    rfl
  rw [he] at h
  simpa only [Finset.sum_apply, _root_.fourierCoeff.const_mul, unit_coeff_lift,
    paperFermiGeneratorCoeff] using h

theorem paperFermiResidualCoeff_eq {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (k : ℤ) :
    paperFermiResidualCoeff c a k = paperFermiHaarCoeff k -
      ∑ j, c j * paperFermiGeneratorCoeff (a j) k := by
  have h := unit_coeff_add dyadicHaar (fun t => (-1 : ℂ) * fermiNymanCombination c a t)
    paperFermiHaar_memLp ((paperFermiCombination_memLp c a).const_mul (-1)) k
  rw [fourierCoeffOn.const_mul, paperFermiCombination_coeff] at h
  have he : (fun t => dyadicHaar t + (-1 : ℂ) * fermiNymanCombination c a t) =
      paperFermiResidual c a := by ext t; simp [paperFermiResidual, sub_eq_add_neg]
  rw [he] at h
  simpa only [neg_one_mul, paperFermiResidualCoeff, paperFermiHaarCoeff, sub_eq_add_neg] using h

private theorem unit_coeff_zero (f : ℝ → ℂ) :
    fourierCoeffOn zero_lt_one f 0 = ∫ t in Ioc (0 : ℝ) 1, f t := by
  rw [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le zero_le_one]
  simp

theorem paperFermiHaarCoeff_zero : paperFermiHaarCoeff 0 = 0 := by
  rw [paperFermiHaarCoeff, unit_coeff_zero]
  simpa using integral_dyadicHaar_mul_cpow (s := (1 : ℂ)) (by norm_num)

theorem paperFermiGeneratorCoeff_zero (a : {a : ℝ // 1 ≤ a}) :
    paperFermiGeneratorCoeff a 0 = -((Real.log 2 / a.val : ℝ) : ℂ) := by
  rw [paperFermiGeneratorCoeff, unit_coeff_zero]
  have h := integral_Ioc_fermiNymanGen_mul_cpow a.property (1 : ℂ)
  simpa only [sub_self, Complex.cpow_zero, mul_one, mellin, one_smul,
    pm_integral_fermiNymanGen (lt_of_lt_of_le one_pos a.property)] using h

theorem paperFermiResidualCoeff_zero {n : ℕ} (c : Fin n → ℂ)
    (a : Fin n → {a : ℝ // 1 ≤ a}) :
    paperFermiResidualCoeff c (fun j => a j) 0 =
      (Real.log 2 : ℂ) * ∑ j, c j / (a j).val := by
  rw [paperFermiResidualCoeff_eq, paperFermiHaarCoeff_zero, zero_sub, Finset.mul_sum]
  simp_rw [paperFermiGeneratorCoeff_zero, mul_neg, Finset.sum_neg_distrib, neg_neg]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

def paperFermiError {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, ‖paperFermiResidual c a t‖ ^ 2

def paperFermiSpectralError {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖paperFermiResidualCoeff c a k‖ ^ 2

theorem paperFermiResidual_parseval {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) :
    HasSum (fun k : ℤ => ‖paperFermiResidualCoeff c a k‖ ^ 2) (paperFermiError c a) := by
  simpa only [sub_zero, inv_one, one_smul, intervalIntegral.integral_of_le zero_le_one,
    paperFermiResidualCoeff, paperFermiError] using
    hasSum_sq_fourierCoeffOn zero_lt_one (paperFermiResidual_memLp c a)

theorem paperFermiError_eq_tsum {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) :
    paperFermiError c a = ∑' k : ℤ, ‖paperFermiHaarCoeff k -
      ∑ j, c j * paperFermiGeneratorCoeff (a j) k‖ ^ 2 := by
  rw [← (paperFermiResidual_parseval c a).tsum_eq]
  simp only [paperFermiResidualCoeff_eq]

theorem paperFermiSpectralError_nonneg {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (N : ℕ) :
    0 ≤ paperFermiSpectralError c a N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem paperFermiSpectralError_le {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (N : ℕ) :
    paperFermiSpectralError c a N ≤ paperFermiError c a :=
  sum_le_hasSum _ (fun _ _ => sq_nonneg _) (paperFermiResidual_parseval c a)

theorem paperFermiSpectralError_monotone {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) :
    Monotone (paperFermiSpectralError c a) := by
  intro N M hNM
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc (by omega) (by omega)
  · intro k _ _
    exact sq_nonneg _

theorem paperFermiSpectralError_tendsto {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) :
    Tendsto (paperFermiSpectralError c a) atTop (𝓝 (paperFermiError c a)) := by
  apply (paperFermiResidual_parseval c a).comp
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro N M hNM
    exact Finset.Icc_subset_Icc (by omega) (by omega)
  · intro k
    refine ⟨k.natAbs, ?_⟩
    rw [Finset.mem_Icc]
    omega

/-- The exact arithmetic mean is separated, with every other frequency retained. -/
theorem paperFermiSpectralError_split_mean {n : ℕ} (c : Fin n → ℂ)
    (a : Fin n → {a : ℝ // 1 ≤ a}) (N : ℕ) :
    paperFermiSpectralError c (fun j => a j) N =
      ‖(Real.log 2 : ℂ) * ∑ j, c j / (a j).val‖ ^ 2 +
      ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0,
        ‖paperFermiResidualCoeff c (fun j => a j) k‖ ^ 2 := by
  rw [← paperFermiResidualCoeff_zero]
  exact (Finset.add_sum_erase _ _ (by simp)).symm

theorem paperFermiError_mean_floor {n : ℕ} (c : Fin n → ℂ)
    (a : Fin n → {a : ℝ // 1 ≤ a}) :
    ‖(Real.log 2 : ℂ) * ∑ j, c j / (a j).val‖ ^ 2 ≤
      paperFermiError c (fun j => a j) := by
  have h := paperFermiSpectralError_le c (fun j => (a j).val) 0
  simpa [paperFermiSpectralError, paperFermiResidualCoeff_zero] using h

end
end RHTower
