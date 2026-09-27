import GaloisForLFunctions.RHTower.XiGaussianCoefficientTail
import GaloisForLFunctions.RHTower.XiGaussianSampledPerturbation
import GaloisForLFunctions.RHTower.XiPolynomialGaussianExplicitFormula

/-!
# No finite cutoff captures all polynomial orders in native Xi energy

The finite-divisor annihilator has positive native energy at every positive
heat time. If it kills the complete low spectral shell, all its energy is
in the remaining tail. Thus a cutoff independent of polynomial degree cannot
make that tail a strict fraction of native energy, even at one fixed time.
This is an obstruction to uniform truncation, not to Hankel positivity.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Actual critical samples ensure that a normalized finite annihilator
has strictly positive full energy at every positive heat time. -/
theorem xiGaussianNativeEnergy_annihilator_pos (F : Finset XiZeroCopy)
    (t : {t : ℝ // 0 < t}) :
    0 < xiGaussianNativeEnergy (xiGaussianAnnihilator F) t := by
  classical
  let P := xiGaussianAnnihilator F
  obtain ⟨c, hc, L, _, hfloor⟩ :=
    exists_xiPolynomialGaussianEnergy_allTime_floor (P.natDegree + 1)
  have hsum : 1 ≤ ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j ^ 2 := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (P.natDegree + 1)) =>
      sq_nonneg (P.coeff j)) (Finset.mem_range.mpr (Nat.zero_lt_succ P.natDegree))
    simpa only [P, xiGaussianAnnihilator_coeff_zero, one_pow] using h
  have h := hfloor P.coeff t
  rw [← routeUPolynomial_eq_coeff_rangeSum] at h
  exact lt_of_lt_of_le
    (mul_pos (mul_pos hc (Real.exp_pos _)) (lt_of_lt_of_le zero_lt_one hsum)) h

/-- Annihilating the entire head leaves the complete energy in the tail. -/
theorem xiGaussianTailEnergy_shell_annihilator_eq_nativeEnergy
    (R : ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianTailEnergy (xiGaussianAnnihilator (finite_xiHeatShell R).toFinset) t R =
      xiGaussianNativeEnergy (xiGaussianAnnihilator (finite_xiHeatShell R).toFinset) t := by
  classical
  let F := (finite_xiHeatShell R).toFinset
  have hset : (F : Set XiZeroCopy)ᶜ = {q : XiZeroCopy | R < (xiSpectralPoint q ^ 2).re} := by
    ext q
    simp only [Set.mem_compl_iff, Finset.mem_coe, F, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq, not_le]
  have hhead : (∑ q ∈ F, ‖xiPolynomialGaussianHeatTerm (xiGaussianAnnihilator F) t q‖) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp only [xiPolynomialGaussianHeatTerm, xiGaussianAnnihilator_vanishes F ⟨q, hq⟩,
      zero_pow two_ne_zero, zero_mul, norm_zero]
  have hs := (summable_norm_xiPolynomialGaussianHeatTerm t.property
    (xiGaussianAnnihilator F)).sum_add_tsum_compl (s := F)
  rw [hset, hhead, zero_add] at hs
  exact hs

/-- The same nonzero polynomial defeats a given cutoff simultaneously at
every positive heat time. There is no RH or off-critical-node premise. -/
theorem exists_xiGaussian_allTime_full_tail (R : ℝ) :
    ∃ P : Polynomial ℝ, P.eval 0 = 1 ∧ ∀ t : {t : ℝ // 0 < t},
      0 < xiGaussianNativeEnergy P t ∧ xiGaussianTailEnergy P t R = xiGaussianNativeEnergy P t := by
  refine ⟨xiGaussianAnnihilator (finite_xiHeatShell R).toFinset,
    xiGaussianAnnihilator_zero _, fun t => ?_⟩
  exact ⟨xiGaussianNativeEnergy_annihilator_pos _ t,
    xiGaussianTailEnergy_shell_annihilator_eq_nativeEnergy R t⟩

/-- No finite cutoff makes the whole tail a strict fraction of native
energy uniformly over every polynomial degree and coefficient direction. -/
theorem not_xiGaussian_uniform_relative_tail (t : {t : ℝ // 0 < t})
    (ε : {ε : ℝ // ε < 1}) :
    ¬ ∃ R : ℝ, ∀ P : Polynomial ℝ,
      xiGaussianTailEnergy P t R ≤ (ε : ℝ) * xiGaussianNativeEnergy P t := by
  rintro ⟨R, hR⟩
  obtain ⟨P, _, hP⟩ := exists_xiGaussian_allTime_full_tail R
  have hb := hR P
  rw [(hP t).2] at hb
  have hstrict := mul_lt_mul_of_pos_right ε.property (hP t).1
  rw [one_mul] at hstrict
  exact (not_lt_of_ge hb) hstrict

end RHTower
