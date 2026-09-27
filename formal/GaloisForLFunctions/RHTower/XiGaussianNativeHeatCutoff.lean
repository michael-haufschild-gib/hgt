import GaloisForLFunctions.RHTower.XiGaussianPolarAnnihilator

/-!
# Native heat decay on complete spectral tails

The same positive heat increment damps the full energy above a spectral
cutoff by its exact exponential rate, independently of polynomial degree.
Multiplication by the finite shell annihilator puts every remaining term in
that tail. This remains true after any fixed polynomial factor, including
the factor imposing exact polar cancellation. No coefficient cross terms
are separated or discarded.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Actual critical-line samples make native energy strictly positive on
every nonzero polynomial, at every positive heat time. -/
theorem xiGaussianNativeEnergy_pos (P : {P : Polynomial ℝ // P ≠ 0})
    (t : {t : ℝ // 0 < t}) :
    0 < xiGaussianNativeEnergy P t := by
  classical
  obtain ⟨c, hc, L, _, hfloor⟩ :=
    exists_xiPolynomialGaussianEnergy_allTime_floor (P.1.natDegree + 1)
  have hcoeff : 0 < P.1.coeff P.1.natDegree ^ 2 := by
    rw [Polynomial.coeff_natDegree]
    exact sq_pos_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr P.property)
  have hsum : 0 < ∑ j ∈ Finset.range (P.1.natDegree + 1), P.1.coeff j ^ 2 :=
    hcoeff.trans_le (Finset.single_le_sum
      (fun j (_ : j ∈ Finset.range (P.1.natDegree + 1)) => sq_nonneg (P.1.coeff j))
      (Finset.mem_range.mpr (Nat.lt_succ_self _)))
  have h := hfloor P.1.coeff t
  rw [← routeUPolynomial_eq_coeff_rangeSum] at h
  exact (mul_pos (mul_pos hc (Real.exp_pos _)) hsum).trans_le h

/-- Exact tail-to-tail decay over any positive heat increment. The constant
is independent of the polynomial and all of its coefficients. -/
theorem xiGaussianTailEnergy_le_earlier_tail (P : Polynomial ℝ)
    (s : {s : ℝ // 0 < s}) (t : Set.Ici (s : ℝ)) (R : ℝ) :
    xiGaussianTailEnergy P (xiGaussianHeatAfter s t) R ≤
      Real.exp (-(((t : ℝ) - (s : ℝ)) * R)) * xiGaussianTailEnergy P s R := by
  classical
  let S : Set XiZeroCopy := {q : XiZeroCopy | R < (xiSpectralPoint q ^ 2).re}
  have hst : (s : ℝ) ≤ (t : ℝ) := t.property
  have hs := (summable_norm_xiPolynomialGaussianHeatTerm s.property P).subtype S
  have ht := (summable_norm_xiPolynomialGaussianHeatTerm
    (xiGaussianHeatAfter s t).property P).subtype S
  have hp (q : S) : ‖xiPolynomialGaussianHeatTerm P t q.1‖ ≤
      Real.exp (-(((t : ℝ) - (s : ℝ)) * R)) * ‖xiPolynomialGaussianHeatTerm P s q.1‖ := by
    rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm]
    have he : Real.exp (-((t : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) ≤
        Real.exp (-(((t : ℝ) - (s : ℝ)) * R)) *
          Real.exp (-((s : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have hm := mul_le_mul_of_nonneg_left q.property.le (sub_nonneg.mpr hst)
      nlinarith only [hm]
    exact (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq (mul_left_comm _ _ _)
  have h : (∑' q : S, ‖xiPolynomialGaussianHeatTerm P t q.1‖) ≤
      ∑' q : S, Real.exp (-(((t : ℝ) - (s : ℝ)) * R)) *
        ‖xiPolynomialGaussianHeatTerm P s q.1‖ :=
    Summable.tsum_le_tsum hp ht (hs.mul_left _)
  rw [tsum_mul_left] at h
  exact h

/-- An arbitrary polynomial multiplier preserves exact annihilation of the
complete low shell. The identity holds at every positive heat time. -/
theorem xiGaussianTailEnergy_mul_shell_annihilator_eq_nativeEnergy
    (B : Polynomial ℝ) (R : ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianTailEnergy (B * xiGaussianAnnihilator (finite_xiHeatShell R).toFinset) t R =
      xiGaussianNativeEnergy (B * xiGaussianAnnihilator (finite_xiHeatShell R).toFinset) t := by
  classical
  let F := (finite_xiHeatShell R).toFinset
  have hset : (F : Set XiZeroCopy)ᶜ = {q : XiZeroCopy | R < (xiSpectralPoint q ^ 2).re} := by
    ext q
    simp only [Set.mem_compl_iff, Finset.mem_coe, F, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq, not_le]
  have hhead : (∑ q ∈ F,
      ‖xiPolynomialGaussianHeatTerm (B * xiGaussianAnnihilator F) t q‖) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp only [xiPolynomialGaussianHeatTerm, evalRealPolynomial_mul,
      xiGaussianAnnihilator_vanishes F ⟨q, hq⟩, mul_zero,
      zero_pow two_ne_zero, zero_mul, norm_zero]
  have hs := (summable_norm_xiPolynomialGaussianHeatTerm t.property
    (B * xiGaussianAnnihilator F)).sum_add_tsum_compl (s := F)
  rw [hset, hhead, zero_add] at hs
  exact hs

/-- Every polynomial in this explicit shell-annihilating family obeys the
cutoff exponential rate in the native norm itself. -/
theorem xiGaussianNativeEnergy_mul_shell_annihilator_heat_le
    (B : Polynomial ℝ) (R : ℝ) (s : {s : ℝ // 0 < s}) (t : Set.Ici (s : ℝ)) :
    xiGaussianNativeEnergy (B * xiGaussianAnnihilator (finite_xiHeatShell R).toFinset)
        (xiGaussianHeatAfter s t) ≤
      Real.exp (-(((t : ℝ) - (s : ℝ)) * R)) *
        xiGaussianNativeEnergy (B * xiGaussianAnnihilator (finite_xiHeatShell R).toFinset) s := by
  simpa only [xiGaussianTailEnergy_mul_shell_annihilator_eq_nativeEnergy] using
    xiGaussianTailEnergy_le_earlier_tail
      (B * xiGaussianAnnihilator (finite_xiHeatShell R).toFinset) s t R

end RHTower
