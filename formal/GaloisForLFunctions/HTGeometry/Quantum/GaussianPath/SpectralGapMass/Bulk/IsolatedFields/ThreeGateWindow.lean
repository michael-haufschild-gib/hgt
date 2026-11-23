import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.IsolatedFields.MesoscopicHaar
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.FiniteMoments
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.ThreeGateCost

/-! # Three-gate spectra from inverse-square-root onset -/
open MeasureTheory Matrix Set Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
open ClockSpectrum
noncomputable section

/-- Every fixed angular grid is uniformly close to its Haar counts once
the squared time multiplied by the number of spins is large enough. -/
theorem gaussian_inverse_root_counts (Q : ℕ) (hQ : 0 < Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ T : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Icc (0:ℝ) T, A ≤ (n+2:ℕ)*t^2 → ∀ j : Fin (Q+1),
      |(phaseCount (pathPauliDisorderShell ω n) t (j.val/(Q:ℝ)):ℝ)/(2:ℝ)^(n+2)-j.val/(Q:ℝ)| < δ := by
  obtain ⟨k,hk,κ,hκ,hgrid⟩ := finite_moments_control_grid Q hQ hδ
  obtain ⟨A,hA,htr⟩ := gaussian_inverse_root_trace hκ
  refine ⟨A,hA,?_⟩
  filter_upwards [htr] with ω hω
  intro T
  filter_upwards [hω ((k:ℝ)*T)] with n hn
  intro t ht hlate
  let u := pathPauliDisorderShell ω n
  have hphase := hgrid (eigenphaseLaw u t) (fun j hj => by
    rw [eigenphase_moment,Int.cast_natCast]
    let p := ((j+1:ℕ):ℝ)
    have hp : 1 ≤ p := Nat.one_le_cast.mpr (Nat.succ_pos j)
    have hpk : p ≤ k := Nat.cast_le.mpr hj
    apply hn
    · refine ⟨mul_nonneg (zero_le_one.trans hp) ht.1,?_⟩
      exact (mul_le_mul_of_nonneg_right hpk ht.1).trans (mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg _))
    · apply hlate.trans
      calc ((n+2:ℕ):ℝ)*t^2 ≤ (((n+2:ℕ):ℝ)*t^2)*p^2 :=
             le_mul_of_one_le_right (by positivity) (one_le_pow₀ hp)
           _ = _ := by dsimp only [p]; ring)
  intro j
  simpa only [angular_fraction,phaseCount] using hphase j

/-- After Nt² reaches a fixed constant, three gates suffice after
conjugation, at all positive dates through every bounded horizon. -/
theorem gaussian_inverse_root_three_window :
    ∃ A > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ T : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Icc (0:ℝ) T, A ≤ (n+2:ℕ)*t^2 →
      ∃ W : unitaryGroup (Fin (n+2) → Bool) ℂ, HasProjectiveCircuitApproximation (n+2) (1/10) 3
        (W.val*unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t*star W.val) := by
  obtain ⟨A,hA,h⟩ := gaussian_inverse_root_counts 512 (by decide) (by norm_num : (0:ℝ) < 1/512)
  refine ⟨A,hA,?_⟩
  filter_upwards [h] with ω hω
  intro T
  filter_upwards [hω T,eventually_ge_atTop 7] with n hn hN
  intro t ht hlate
  let u := pathPauliDisorderShell ω n
  have hphase := hn t ht hlate
  obtain ⟨p,hp⟩ := three_gate_of_cdf (by omega : 9 ≤ n+2) (physicalTurns u t)
    (fun j => ⟨(turns_mem _).1.le,(turns_mem _).2⟩) hphase
  obtain ⟨W,hW⟩ := sorted_physical_diagonal u t p
  exact ⟨W,hW.symm ▸ hp⟩

/-- The two-gate spectral obstruction persists on the entire interval
where the three-gate clock is guaranteed to suffice. -/
theorem gaussian_inverse_root_exact_three :
    ∃ A > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ T : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ t∈Icc (0:ℝ) T, A ≤ (n+2:ℕ)*t^2 →
      let U := unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t
      (∃ W : unitaryGroup (Fin (n+2) → Bool) ℂ,
        HasProjectiveCircuitApproximation (n+2) (1/10) 3 (W.val*U*star W.val)) ∧
      ∀ W : unitaryGroup (Fin (n+2) → Bool) ℂ,
        ¬HasProjectiveCircuitApproximation (n+2) (1/10) 2 (W.val*U*star W.val) := by
  obtain ⟨A,hA,hu⟩ := gaussian_inverse_root_three_window
  obtain ⟨B,_,hl⟩ := gaussian_inverse_root_counts 17408 (by decide) (by norm_num : (0:ℝ) < 1/(4*17408))
  refine ⟨max A B,hA.trans_le (le_max_left ..),?_⟩
  filter_upwards [hu,hl] with ω hω hω'
  intro T
  filter_upwards [hω T,hω' T] with n hn hc
  intro t ht hlate U
  refine ⟨hn t ht ((le_max_left ..).trans hlate),?_⟩
  obtain ⟨f,hf⟩ := seventeen_phases_of_cdf _ (D:=(2:ℝ)^(n+2)) (by positivity)
    (hc t ht ((le_max_right ..).trans hlate))
  exact two_gates_excluded _ t f hf

#print axioms gaussian_inverse_root_counts
#print axioms gaussian_inverse_root_exact_three
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
