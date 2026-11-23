import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.MovingWindows.SpectralOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.IsolatedFields.LogarithmicHorizon

/-! # Inverse-square-root exceptional time for the three-gate spectrum -/
open MeasureTheory Filter Set Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

/-- The total exceptional time in a logarithmically long interval is
bounded by the inverse square root of the register size, at every origin. -/
theorem gaussian_log_grid_exception (Q : ℕ) (hQ : 0 < Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∃ K > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ B : ℝ, B ≤ (Nat.log b n:ℝ) → ∀ v : ℝ,
      volume.real ({t | ¬goodGrid (pathPauliDisorderShell ω n) t Q δ} ∩ Icc v (v+B)) ≤ K/sqrt (n+2:ℕ) := by
  obtain ⟨k,hk,κ,hκ,hcov⟩ := grid_failure_cover Q hQ hδ
  obtain ⟨b,hb,A,hA,hstart⟩ := gaussian_harmonic_trace_window k hk (by positivity : 0<κ^2/2)
  let M : ℝ := ⌈2/κ^2⌉₊
  have hM : 0 ≤ M := Nat.cast_nonneg _
  let K := (k:ℝ)*(M+1)*(2*sqrt A)
  refine ⟨b,hb,K,by dsimp only [K]; positivity,?_⟩
  filter_upwards [hstart] with ω hω
  filter_upwards [hω] with n hn
  let N := ((n+2:ℕ):ℝ)
  have hN : 0 < N := by dsimp only [N]; positivity
  let r := sqrt A/sqrt N
  have hr : 0 < r := div_pos (sqrt_pos.mpr hA) (sqrt_pos.mpr hN)
  have he : N*r^2=A := by
    dsimp only [r]
    rw [div_pow,sq_sqrt hA.le,sq_sqrt hN.le]
    field_simp
  intro B hB v
  have hvol (j : Fin k) :
      volume.real (largeOverlap ω n 1 (j.val+1) κ ∩ Icc v (v+B)) ≤ M*(2*r) := by
    let p := (j.val:ℝ)+1
    have hp : 1 ≤ p := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hpk : p ≤ k := by
      change (j.val:ℝ)+1 ≤ (k:ℝ)
      exact_mod_cast Nat.succ_le_of_lt j.isLt
    apply local_overlap_duration ω n hr.le (zero_lt_one.trans_le hp) hκ _ 1 v
    intro s hs
    have hs₀ : r ≤ s := (le_mul_of_one_le_left hr.le hp).trans hs.1
    have hhi := (mul_le_mul_of_nonneg_left hB (zero_le_one.trans hp)).trans
      (mul_le_mul_of_nonneg_right hpk (Nat.cast_nonneg _))
    exact (hn s ⟨hr.le.trans hs₀,hs.2.trans hhi⟩
      (he.ge.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hs₀ 2) hN.le))).le
  apply (harmonic_cover_volume _ (hcov ω n) v B _ hvol).trans
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  calc (k:ℝ)*(M*(2*r)) ≤ (k:ℝ)*((M+1)*(2*r)) :=
         mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
           (by positivity)) (Nat.cast_nonneg _)
       _ = K/sqrt N := by dsimp only [r,K]; ring

/-- Each fixed window inherits the same inverse-root bound. -/
theorem gaussian_grid_exception_length (Q : ℕ) (hQ : 0 < Q) {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    ∃ K > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ v : ℝ,
      volume.real ({t | ¬goodGrid (pathPauliDisorderShell ω n) t Q δ} ∩ Icc v (v+B)) ≤ K/sqrt (n+2:ℕ) := by
  obtain ⟨b,hb,K,hK,h⟩ := gaussian_log_grid_exception Q hQ hδ
  obtain ⟨m,hm⟩ := exists_nat_gt B
  refine ⟨K,hK,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw,eventually_ge_atTop (b^m),eventually_gt_atTop 0] with n hn hpow hn₀
  exact hn B (hm.le.trans (Nat.cast_le.mpr ((Nat.le_log_iff_pow_le hb hn₀.ne').mpr hpow)))

/-- Every logarithmically long window has only O(1/√N) time where the
minimum differs from three after free conjugation, irrespective of origin. -/
theorem gaussian_logarithmic_exact_three_length :
    ∃ b : ℕ, 2 ≤ b ∧ ∃ K > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ B : ℝ, B ≤ (Nat.log b n:ℝ) → ∀ v : ℝ,
      volume.real ({t | ¬exactThreeAt (pathPauliDisorderShell ω n) t} ∩ Icc v (v+B)) ≤ K/sqrt (n+2:ℕ) := by
  obtain ⟨p,hp,a,ha,hu⟩ := gaussian_log_grid_exception 512 (by decide) (by norm_num : (0:ℝ) < 1/512)
  obtain ⟨q,hq,b,hb,hl⟩ := gaussian_log_grid_exception 17408 (by decide) (by norm_num : (0:ℝ) < 1/(4*17408))
  refine ⟨max p q,hp.trans (le_max_left ..),a+b,add_pos ha hb,?_⟩
  filter_upwards [hu,hl] with ω hω hw
  filter_upwards [hω,hw,eventually_ge_atTop 7] with n hn hf hN
  intro B hB v
  have h₁ := hn B (hB.trans (Nat.cast_le.mpr (Nat.log_anti_left (by omega) (le_max_left p q)))) v
  have h₂ := hf B (hB.trans (Nat.cast_le.mpr (Nat.log_anti_left (by omega) (le_max_right p q)))) v
  exact (bound_exact_three_exception hN _ v B _ _ h₁ h₂).trans_eq (add_div ..).symm

/-- Outside O(1/√N) time in every fixed-length interval, three gates
are necessary and sufficient after an arbitrary change of basis. -/
theorem gaussian_inverse_root_exception_length (B : ℝ) :
    ∃ K > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ v : ℝ,
      volume.real ({t | ¬exactThreeAt (pathPauliDisorderShell ω n) t} ∩ Icc v (v+B)) ≤ K/sqrt (n+2:ℕ) := by
  obtain ⟨b,hb,K,hK,h⟩ := gaussian_logarithmic_exact_three_length
  obtain ⟨m,hm⟩ := exists_nat_gt B
  refine ⟨K,hK,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw,eventually_ge_atTop (b^m),eventually_gt_atTop 0] with n hn hpow hn₀
  exact hn B (hm.le.trans (Nat.cast_le.mpr ((Nat.le_log_iff_pow_le hb hn₀.ne').mpr hpow)))

#print axioms gaussian_logarithmic_exact_three_length
#print axioms gaussian_inverse_root_exception_length
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
