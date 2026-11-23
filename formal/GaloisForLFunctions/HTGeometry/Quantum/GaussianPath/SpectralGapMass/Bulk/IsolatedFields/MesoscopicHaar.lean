import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.IsolatedFields.GaussianWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.Eigenphases

/-! # Haar eigenphases throughout mesoscopic startup -/
open MeasureTheory Set Filter Matrix
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

/-- The same inverse-root threshold works up to every fixed horizon.
Positive-time dephasing handles the part of the interval beyond one. -/
theorem gaussian_inverse_root_trace {κ : ℝ} (hκ : 0 < κ) :
    ∃ A > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ T : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Icc (0:ℝ) T, A ≤ (n+2:ℕ)*t^2 → ‖amplitude ω n t‖ < κ := by
  obtain ⟨A,hA,hs⟩ := Bulk.gaussian_startup_trace hκ
  have hl (k : ℕ) := gaussian_uniform_trace_decay (T:=(k:ℝ)) zero_lt_one hκ
  refine ⟨A,hA,?_⟩
  filter_upwards [hs,ae_all_iff.mpr hl] with ω hshort hlate
  intro T
  obtain ⟨k,hk⟩ := exists_nat_gt T
  filter_upwards [hshort,hlate k] with n hn hf
  intro t ht h
  by_cases he : t ≤ 1
  · exact hn t h (by rwa [abs_of_nonneg ht.1])
  · exact hf t ⟨le_of_not_ge he,ht.2.trans hk.le⟩

/-- All bounded nonnegative observation sequences with Nt² tending to
infinity have Haar eigenphases. The dates may be selected from the disorder. -/
theorem gaussian_mesoscopic_haar :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (T : ℝ) (t : ℕ → ℝ),
      (∀ᶠ n in atTop, t n ∈ Icc (0:ℝ) T) →
      Tendsto (fun n => (n+2:ℕ)*(t n)^2) atTop atTop →
      Tendsto (fun n => eigenphaseLaw (pathPauliDisorderShell ω n) (t n)) atTop (𝓝 uniformAngles) := by
  choose A hpos hA using fun k : ℕ =>
    gaussian_inverse_root_trace (by positivity : 0 < 1/((k:ℝ)+1))
  filter_upwards [ae_all_iff.mpr hA] with ω hw
  intro T t htime hmass
  apply haar_of_positive_moments
  intro j
  let p := ((j+1:ℕ):ℝ)
  have hp : 1 ≤ p := Nat.one_le_cast.mpr (Nat.succ_pos j)
  have hp₂ : 1 ≤ p^2 := one_le_pow₀ hp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ε)
  have hκ : 1/((k:ℝ)+1) < ε := (div_lt_iff₀ (by positivity)).mpr (by
    have h := (div_lt_iff₀ hε).mp (hk.trans (lt_add_one _))
    rwa [mul_comm ε])
  filter_upwards [hw k (p*T),htime,hmass.eventually_ge_atTop (A k)] with n hn ht hm
  rw [dist_zero_right,eigenphase_moment,Int.cast_natCast]
  have hnon : 0 ≤ ((n+2:ℕ):ℝ)*(t n)^2 := by positivity
  have he : A k ≤ (n+2:ℕ)*(p*t n)^2 := by
    apply hm.trans
    calc _ ≤ (((n+2:ℕ):ℝ)*(t n)^2)*p^2 := le_mul_of_one_le_right hnon hp₂
         _ = _ := by ring
  exact (hn _ ⟨mul_nonneg (zero_le_one.trans hp) ht.1,mul_le_mul_of_nonneg_left ht.2 (zero_le_one.trans hp)⟩ he).trans hκ

#print axioms gaussian_mesoscopic_haar
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
