import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.WaitingWidth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.WindowOccupation

/-! # Necessary observation overhead for windows containing a cheap visit -/
open Matrix Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Arbitrarily late, a full interval of starting times shares one actual
affordable visit. Its length equals the forward window width. -/
theorem exists_full_window_of_affordable_starts {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n)) (s : ℕ) (W a : ℝ) :
    ∃ A : ℝ, a ≤ A ∧ Icc A (A+W) ⊆ circuitWindowHits H.val s W := by
  obtain ⟨v,hv,hh,_⟩ := projective_first_circuit_visit_deadline e H (a+W) s
  refine ⟨v-W,by linarith only [hv.1],?_⟩
  intro t ht
  exact ⟨v,⟨by linarith only [ht.2],by linarith only [ht.1]⟩,hh⟩

/-- A uniform occupation correction S must pay for the entire width preceding
one hit, even if the inequality is only required after an arbitrary date. -/
theorem occupation_correction_lower {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n)) (s : ℕ) {W M S a : ℝ} (hW : 0 ≤ W)
    (h : ∀ A ≥ a, ∀ T : ℝ, 0 ≤ T →
      M * volume.real (circuitWindowHits H.val s W ∩ Icc A (A+T)) ≤ T+S) :
    (M-1)*W ≤ S := by
  obtain ⟨A,hA,hfull⟩ := exists_full_window_of_affordable_starts e H s W a
  have hb := h A hA W hW
  rw [inter_eq_right.mpr hfull,Real.volume_real_Icc_of_le (le_add_of_nonneg_right hW),add_sub_cancel_left] at hb
  linarith only [hb]

/-- On the Gaussian chain a doubly exponential uniform correction is
sufficient, and every such correction, even after discarding an arbitrary
initial segment, is at least the packing excess times the protected width. -/
theorem gaussian_path_occupation_correction_scale :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let r := excursionGateBudget N
      let M := ((r:ℝ)+1)^r
      let W := translatedExcursionWidth N ‖H.val‖
      let good := fun a S : ℝ => ∀ A ≥ a, ∀ T : ℝ, 0 ≤ T →
        M*volume.real (circuitWindowHits H.val r W ∩ Icc A (A+T)) ≤ T+S
      (∀ a : ℝ, good a ((2:ℝ)^(D^c))) ∧
        ∀ a S : ℝ, good a S → ((2:ℝ)^(D/1024)-1)*(2:ℝ)^(D/2048) ≤ (M-1)*W ∧ (M-1)*W ≤ S := by
  obtain ⟨c,hc⟩ := gaussian_path_finite_window_occupation
  refine ⟨c,?_⟩
  filter_upwards [hc,gaussian_path_eventual_double_exponential_width] with ω hc hw
  filter_upwards [hc,hw,eventually_ge_atTop 64] with k hocc hwidth hk
  intro N D u H r M W good
  refine ⟨fun _ A _ T hT => hocc A T hT,?_⟩
  intro a S hh
  have he : (Fin N → Bool) ≃ Fin ((D-1)+1) := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  have hW : 0 ≤ W := by dsimp [W,translatedExcursionWidth]; positivity
  have hM : (2:ℝ)^(D/1024) ≤ M := by
    change (2:ℝ)^(D/1024) ≤ ((r:ℝ)+1)^r
    exact_mod_cast (circuit_return_spacing_factor_bounds (by dsimp [N]; omega : 64 ≤ N)).1
  have hM₁ : 1 ≤ M := (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)).trans hM
  exact ⟨mul_le_mul (sub_le_sub_right hM 1) hwidth (by positivity) (sub_nonneg.mpr hM₁),
    occupation_correction_lower he H r hW hh⟩

#print axioms gaussian_path_occupation_correction_scale
end
end GaloisForLFunctions.HTGeometry.SpectralJets
