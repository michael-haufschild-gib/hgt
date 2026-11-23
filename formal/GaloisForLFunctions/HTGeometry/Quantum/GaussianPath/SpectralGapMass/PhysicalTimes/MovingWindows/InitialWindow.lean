import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.MovingWindows.SpectralOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.IsolatedFields.LogarithmicHorizon

/-! # Pointwise spectral gate cost through logarithmic physical time -/
open MeasureTheory Filter Set
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

theorem gaussian_logarithmic_grid (Q : ℕ) (hQ : 0<Q) {δ : ℝ} (hδ : 0<δ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∃ A>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Icc (0:ℝ) (Nat.log b n:ℝ), A ≤ (n+2:ℕ)*t^2 →
        goodGrid (pathPauliDisorderShell ω n) t Q δ := by
  obtain ⟨k,hk,κ,hκ,hcov⟩ := grid_failure_cover Q hQ hδ
  obtain ⟨b,hb,A,hA,h⟩ := gaussian_harmonic_trace_window k hk hκ
  refine ⟨b,hb,A,hA,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  intro t ht hm
  by_contra hbad
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hcov ω n hbad)
  rw [empty_large_overlap] at hj
  let p := (j.val:ℝ)+1
  have hp : 1≤p := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hpk : p≤k := by
    change (j.val:ℝ)+1 ≤ (k:ℝ)
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have ht' : p*t ∈ Icc (0:ℝ) ((k:ℝ)*Nat.log b n) :=
    ⟨mul_nonneg (zero_le_one.trans hp) ht.1,(mul_le_mul_of_nonneg_left ht.2 (zero_le_one.trans hp)).trans
      (mul_le_mul_of_nonneg_right hpk (Nat.cast_nonneg _))⟩
  have hm' : A ≤ (n+2:ℕ)*(p*t)^2 := by
    apply hm.trans
    calc _ ≤ (((n+2:ℕ):ℝ)*t^2)*p^2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hp)
         _ = _ := by ring
  exact (hn (p*t) ht' hm').not_ge hj

/-- On the initial logarithmic interval every date past inverse-root onset
costs exactly three after free conjugation. -/
theorem gaussian_logarithmic_three_window :
    ∃ b : ℕ, 2 ≤ b ∧ ∃ A>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Icc (0:ℝ) (Nat.log b n:ℝ), A ≤ (n+2:ℕ)*t^2 →
        exactThreeAt (pathPauliDisorderShell ω n) t := by
  obtain ⟨b,hb,A,hA,hu⟩ := gaussian_logarithmic_grid 512 (by decide) (by norm_num : (0:ℝ)<1/512)
  obtain ⟨d,hd,C,_,hl⟩ := gaussian_logarithmic_grid 17408 (by decide) (by norm_num : (0:ℝ)<1/(4*17408))
  refine ⟨max b d,hb.trans (le_max_left ..),max A C,hA.trans_le (le_max_left ..),?_⟩
  filter_upwards [hu,hl] with ω hw hω
  filter_upwards [hw,hω,eventually_ge_atTop 7] with n hn hf hN
  intro t ht hm
  apply exact_three_of_grids hN
  · exact hn t ⟨ht.1,ht.2.trans (Nat.cast_le.mpr (Nat.log_anti_left (by omega) (le_max_left b d)))⟩
      ((le_max_left ..).trans hm)
  · exact hf t ⟨ht.1,ht.2.trans (Nat.cast_le.mpr (Nat.log_anti_left (by omega) (le_max_right b d)))⟩
      ((le_max_right ..).trans hm)

#print axioms gaussian_logarithmic_three_window
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
