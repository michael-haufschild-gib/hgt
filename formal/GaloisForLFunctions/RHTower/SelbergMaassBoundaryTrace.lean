import GaloisForLFunctions.RHTower.SelbergMaassFourierModes
import GaloisForLFunctions.RHTower.SelbergBesselBoundaryOperator
import GaloisForLFunctions.RHTower.DeningerFourierKothe

/-!
# Actual Maass traces in the critical cusp boundary-form domain

The actual C² Maass coefficient bound gives absolute summability on the integer lattice.
Multiplying its squared-frequency estimate by the coefficient norm proves summability of the
horizontal derivative energy. The literal coefficient sequence therefore lies in complex ℓ²
and in the principal frequency-weighted domain of the critical Bessel boundary form.

The compact-correction identity now applies to this constructed Maass trace. The zero channel
is retained in the sequence and explicitly omitted by the existing nonzero-mode seam coefficient.
No positivity of the quotient-core response or global spectral inequality is asserted.
-/

open Set UpperHalfPlane
namespace GaloisForLFunctions.RHTower.SelbergMaassTrace
open SelbergMaassFourier SelbergBoundaryOperator
noncomputable section

private theorem signedFrequency_factor (N : ℕ) (n : ℤ) :
    signedFrequency (N + 1 : ℕ) n = (2 * Real.pi / (N + 1 : ℕ)) * (n : ℝ) := by
  unfold signedFrequency
  ring

/-- The actual inverse-square estimate, with the constant coefficient absorbed into a finite bound. -/
theorem coefficient_weighted_bound (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ,
      (1 + |(n : ℝ)|) ^ 2 * ‖maassCoefficient N f n y‖ ≤ C := by
  obtain ⟨M, hM, hb⟩ := maassCoefficient_frequency_square_bound N f hy
  let d : ℝ := 2 * Real.pi / (N + 1 : ℕ)
  have hd : 0 < d := by unfold d; positivity
  have hL : 0 ≤ M / d ^ 2 := div_nonneg hM (sq_nonneg d)
  have hi : ∀ n : ℤ, (n : ℝ) ^ 2 * ‖maassCoefficient N f n y‖ ≤ M / d ^ 2 := by
    intro n
    apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
    have h := hb n
    rw [signedFrequency_factor] at h
    change (d * (n : ℝ)) ^ 2 * ‖maassCoefficient N f n y‖ ≤ M at h
    nlinarith [h]
  refine ⟨4 * (M / d ^ 2) + ‖maassCoefficient N f 0 y‖, by positivity, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Int.cast_zero, abs_zero, add_zero, one_pow, one_mul]
    linarith
  · have hnat : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    have ha : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hnat
    have hpoly : (1 + |(n : ℝ)|) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
      nlinarith [sq_abs (n : ℝ), sq_nonneg (|(n : ℝ)| - 1)]
    calc
      _ ≤ (4 * (n : ℝ) ^ 2) * ‖maassCoefficient N f n y‖ :=
        mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
      _ = 4 * ((n : ℝ) ^ 2 * ‖maassCoefficient N f n y‖) := by ring
      _ ≤ 4 * (M / d ^ 2) := mul_le_mul_of_nonneg_left (hi n) (by linarith)
      _ ≤ _ := le_add_of_nonneg_right (norm_nonneg _)

/-- Every positive-height Maass trace has absolutely summable Fourier coefficients. -/
theorem coefficient_norm_summable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) : Summable (fun n : ℤ => ‖maassCoefficient N f n y‖) := by
  obtain ⟨C, hC, hb⟩ := coefficient_weighted_bound N f hy
  have hs : Summable (fun n : ℤ => C / (1 + |(n : ℝ)|) ^ 2) := by
    apply (_root_.RHTower.deningerFourier_summable_inv_sq.mul_left C).congr
    intro n
    rw [zpow_neg, zpow_two, div_eq_mul_inv, pow_two]
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hs
  intro n
  apply (le_div_iff₀ (by positivity : 0 < (1 + |(n : ℝ)|) ^ 2)).mpr
  simpa only [mul_comm] using hb n

/-- The actual Fourier trace has finite squared coefficient mass. -/
theorem coefficient_normSq_summable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℤ => Complex.normSq (maassCoefficient N f n y)) := by
  obtain ⟨C, hC, hb⟩ := coefficient_weighted_bound N f hy
  have hbound : ∀ n : ℤ, ‖maassCoefficient N f n y‖ ≤ C := by
    intro n
    have hw : 1 ≤ (1 + |(n : ℝ)|) ^ 2 := by nlinarith [abs_nonneg (n : ℝ), sq_nonneg (n : ℝ)]
    calc
      _ = 1 * ‖maassCoefficient N f n y‖ := (one_mul _).symm
      _ ≤ (1 + |(n : ℝ)|) ^ 2 * ‖maassCoefficient N f n y‖ :=
        mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ ≤ C := hb n
  apply Summable.of_nonneg_of_le (fun n => Complex.normSq_nonneg _) _
    ((coefficient_norm_summable N f hy).mul_left C)
  intro n
  rw [Complex.normSq_eq_norm_sq, pow_two]
  exact mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)

/-- Its squared-frequency Fourier energy is summable. -/
theorem coefficient_gradient_summable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℤ => signedFrequency (N + 1 : ℕ) n ^ 2 *
      Complex.normSq (maassCoefficient N f n y)) := by
  obtain ⟨M, hM, hb⟩ := maassCoefficient_frequency_square_bound N f hy
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)) _
    ((coefficient_norm_summable N f hy).mul_left M)
  intro n
  rw [Complex.normSq_eq_norm_sq, pow_two ‖maassCoefficient N f n y‖, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _)

/-- The Bessel boundary frequency agrees exactly with the absolute Maass frequency. -/
theorem frequency_eq_abs_signed (N : ℕ) (n : ℤ) :
    frequency (Real.log (N + 1 : ℕ)) n = |signedFrequency (N + 1 : ℕ) n| := by
  have ha : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  unfold frequency signedFrequency
  rw [Real.exp_log (by positivity : (0 : ℝ) < (N + 1 : ℕ)), ha,
    abs_div, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2),
    abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < (N + 1 : ℕ))]

/-- The actual Maass coefficients lie in the principal boundary-form summability domain. -/
theorem coefficient_frequency_summable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℤ => frequency (Real.log (N + 1 : ℕ)) n *
      Complex.normSq (maassCoefficient N f n y)) := by
  have hs := (coefficient_normSq_summable N f hy).add (coefficient_gradient_summable N f hy)
  refine Summable.of_nonneg_of_le ?_ ?_ hs
  · intro n
    rw [frequency_eq_abs_signed]
    exact mul_nonneg (abs_nonneg _) (Complex.normSq_nonneg _)
  · intro n
    rw [frequency_eq_abs_signed]
    have hb : |signedFrequency (N + 1 : ℕ) n| ≤ 1 + signedFrequency (N + 1 : ℕ) n ^ 2 := by
      nlinarith [sq_nonneg (|signedFrequency (N + 1 : ℕ) n| - 1),
        sq_abs (signedFrequency (N + 1 : ℕ) n)]
    have h := mul_le_mul_of_nonneg_right hb (Complex.normSq_nonneg (maassCoefficient N f n y))
    simpa only [add_mul, one_mul] using h

/-- The literal Maass Fourier trace at height `exp T`, bundled in complex ℓ². -/
def boundaryTrace (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (T : ℝ) : BoundarySpace :=
  ⟨(fun n => maassCoefficient N f n (Real.exp T)), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.normSq_eq_norm_sq] using
      coefficient_normSq_summable N f (Real.exp_pos T)⟩

/-- The same actual trace bundled in the Bessel boundary-form domain. -/
def formTrace (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (T : ℝ) : FormDomain (Real.log (N + 1 : ℕ)) :=
  ⟨boundaryTrace N f T, coefficient_frequency_summable N f (Real.exp_pos T)⟩

/-- The constructed ℓ² vector has exactly the literal Maass Fourier coordinates. -/
theorem boundaryTrace_apply (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (T : ℝ) (n : ℤ) : boundaryTrace N f T n = maassCoefficient N f n (Real.exp T) := rfl

/-- The exact compact Bessel correction identity on actual Maass Fourier traces. -/
theorem maass_boundary_decomposition (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (T : ℝ) :
    (∑' n : ℤ, SelbergBesselModes.seam (Real.log (N + 1 : ℕ)) T n *
      Complex.normSq (maassCoefficient N f n (Real.exp T))) =
    (∑' n : ℤ, frequency (Real.log (N + 1 : ℕ)) n *
      Complex.normSq (maassCoefficient N f n (Real.exp T))) -
    (inner ℂ (operator (Real.log (N + 1 : ℕ)) T (boundaryTrace N f T)) (boundaryTrace N f T)).re :=
  boundary_form_decomposition (Real.log (N + 1 : ℕ)) T (formTrace N f T)

/-- The outgoing nonzero-mode seam series of the actual trace is summable. -/
theorem maass_seam_summable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (T : ℝ) :
    Summable (fun n : ℤ => SelbergBesselModes.seam (Real.log (N + 1 : ℕ)) T n *
      Complex.normSq (maassCoefficient N f n (Real.exp T))) :=
  (seam_summable_iff (Real.log (N + 1 : ℕ)) T (boundaryTrace N f T)).mpr
    (coefficient_frequency_summable N f (Real.exp_pos T))

end
end GaloisForLFunctions.RHTower.SelbergMaassTrace
