import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.MovingWindows.InverseRoot
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.FirstThreeDate

/-! # Sharp exceptional duration at the identity -/
open MeasureTheory Set Filter Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

/-- The unit interval at the identity attains the order of the largest
exceptional duration. Before the first three-gate fit, a subinterval of
length one quarter of that first date lies above three in every basis. -/
theorem gaussian_exception_length_sharp :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := ((n+2:ℕ):ℝ)
      let bad := {t | ¬exactThreeAt (pathPauliDisorderShell ω n) t}
      c ≤ N*(volume.real (bad ∩ Icc 0 1))^2 ∧
      ∀ v : ℝ, N*(volume.real (bad ∩ Icc v (v+1)))^2 ≤ C := by
  obtain ⟨K,hK,hupper⟩ := gaussian_inverse_root_exception_length 1
  obtain ⟨A,B,hA,hB,hfirst⟩ := gaussian_first_three_date
  refine ⟨1/(16*B),K^2,by positivity,sq_pos_of_pos hK,?_⟩
  filter_upwards [hupper,hfirst] with ω hω hw
  filter_upwards [hω,hw.1.eventually_lt_const zero_lt_one,hw.2.1,
    hw.2.2.eventually (eventually_ge_atTop (2*A))] with n hn hearly hfloor hlate
  intro N bad
  let u := firstThreeDate A ω n
  let a := A/((n+1:ℕ):ℝ)
  have ha : 0 < a := div_pos hA (by positivity)
  have hstart : a ≤ u/2 := by
    apply (div_le_iff₀ (by positivity : 0 < ((n+1:ℕ):ℝ))).mpr
    change 2*A ≤ u*(n+1:ℕ) at hlate
    linarith only [hlate]
  have hu : 0 < u := by linarith only [ha,hstart]
  have hsmall : u < 1 := hearly
  let H := (⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩ :
    selfAdjoint (Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ))
  have hleast := SpectralApproximation.firstVisit_isLeast H a 3 (by norm_num : (0:ℝ) < 1/10)
  have hsub : Icc (u/2) (3*u/4) ⊆ bad ∩ Icc 0 1 := by
    intro t ht
    refine ⟨fun hg => ?_,(ha.le.trans hstart).trans ht.1,ht.2.trans (by linarith only [hu,hsmall])⟩
    have h : u ≤ t := hleast.2 ⟨hstart.trans ht.1,hg.1⟩
    linarith only [h,ht.2,hu]
  have hm := measureReal_mono (μ:=volume) hsub
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  rw [Real.volume_real_Icc_of_le (by linarith only [hu])] at hm
  have hl : u ≤ 4*volume.real (bad ∩ Icc 0 1) := by linarith only [hm]
  have hN : 0 < N := by dsimp only [N]; positivity
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 16*B)).mpr
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.le hl 2) (mul_nonneg hB.le hN.le)
    change 1 ≤ B*N*u^2 at hfloor
    nlinarith only [h,hfloor]
  · intro v
    have h := (le_div_iff₀ (sqrt_pos.mpr hN)).mp (hn v)
    have hsq := pow_le_pow_left₀ (mul_nonneg ENNReal.toReal_nonneg (sqrt_nonneg N)) h 2
    rw [mul_pow,sq_sqrt hN.le,mul_comm] at hsq
    exact hsq

#print axioms gaussian_exception_length_sharp
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
