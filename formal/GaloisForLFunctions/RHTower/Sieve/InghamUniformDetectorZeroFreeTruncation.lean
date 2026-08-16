import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorZeroDensityGapPolynomial
import GaloisForLFunctions.RHTower.Sieve.ZetaUniformStripZeroFree

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- Above the uniform `log(X)⁻²` zero-free edge, the actual Littlewood zero count vanishes. -/
theorem exists_zetaLittlewoodZeroCountAbove_eq_zero_near_one :
    ∃ L0 : ℝ, 1 ≤ L0 ∧
      ∀ {sigma : ℝ} {X : ℕ}, 10 ≤ X →
        L0 ≤ Real.log (X : ℝ) →
        1 - 1 / Real.log (X : ℝ) ^ 2 ≤ sigma →
        zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma = 0 := by
  obtain ⟨L0, hL0, hzf⟩ := exists_zeta_uniform_strip_zero_free
  refine ⟨L0, hL0, ?_⟩
  intro sigma X hX hlog hsigma
  unfold zetaLittlewoodZeroCountAbove
  apply Finset.sum_eq_zero
  intro w hw
  have hwf := Finset.mem_filter.mp hw
  have hwmem := mem_zetaResidueUnitClosedRectangleZeros.mp hwf.1
  have hwK := Complex.mem_reProdIm.mp hwmem.1
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  have hT : 0 ≤ (X : ℝ) - 2 := by linarith
  have hwim : w.im ∈ Set.uIcc (-((X : ℝ) - 2)) ((X : ℝ) - 2) := by
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
      add_zero, sub_zero] using hwK.2
  rw [Set.uIcc_of_le (neg_le_self hT)] at hwim
  have himT : |w.im| ≤ (X : ℝ) - 2 := (abs_le).2 hwim
  have himX : |w.im| ≤ (X : ℝ) := by linarith
  have hw1 : w ≠ 1 := by
    intro heq
    rw [heq, zetaResidueUnit_one] at hwmem
    norm_num at hwmem
  have hzeta : riemannZeta w ≠ 0 :=
    hzf w (X : ℝ) hlog himX (hsigma.trans hwf.2) hw1
  exact False.elim (((zetaResidueUnit_ne_zero_iff hw1).2 hzeta) hwmem.2)

end

end RHTower.Sieve
