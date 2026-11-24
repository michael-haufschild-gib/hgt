import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SignPacking.Occupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.TimedReflection

/-! # A finite observation bound for all cheap circuits after a time shift -/
open Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Once every relative phase cube can be reached by G, every interval
of length t contains cheap dates of measure at most the circuit net
size times (t+G) divided by the number of independent spectral signs. -/
theorem cheap_snapshot_volume {N d : ℕ} (H : selfAdjoint (Reg N))
    (e : (Fin N → Bool) ≃ Fin (d+1)) {G : ℝ} (hG : 0≤G)
    (hphase : ∀ c : Fin d → ℝ, ∃ v ∈ Icc 0 G, ∀ j, turnDist
      (v*RHTower.zeroProjectiveFrequency (H.2.isHermitian.eigenvalues ∘ e.symm) j-c j)<1/80)
    (s : ℕ) (o t : ℝ) (ht : 0≤t) :
    let C := {v : ℝ | HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val (o+v))}
    (2:ℝ)^d*volume.real (C ∩ Icc t (2*t)) ≤ ((atMostQuarterCircuitNet N s).card:ℝ)*(t+G) := by
  classical
  intro C
  have hsign := spectral_sign_visits_tube_occupation e H hG (fun x => by
    obtain ⟨v,hv,z,hz,h⟩ := phase_interval_approaches_reflection e H 0 G hphase x
    exact ⟨v,hv,z,hz,h.trans_lt (by norm_num)⟩)
  let J := atMostQuarterCircuitNet N s
  let T (W : J) := {v : ℝ | ∃ z : ℂ, ‖z‖=1 ∧ ‖unitaryEvolution H.val (v+o)-z • (W.val.val:Reg N)‖ ≤ 2/5}
      ∩ Icc t (2*t)
  have hsub : C ∩ Icc t (2*t) ⊆ ⋃ W : J, T W := by
    rintro v ⟨⟨z,hz,Y,hY,hy⟩,hv⟩
    obtain ⟨W,hW,hw⟩ := atMostQuarterCircuitNet_cover Y hY
    refine mem_iUnion.mpr ⟨⟨W,hW⟩,⟨z,hz,?_⟩,hv⟩
    rw [add_comm v o]
    apply (norm_sub_le_norm_sub_add_norm_sub _ (z • Y.eval.val) _).trans
    rw [←smul_sub,norm_smul,hz,one_mul]
    rw [dist_eq_norm] at hw
    linarith only [hy,hw]
  have hu : (⋃ W : J, T W) ⊆ Icc t (2*t) := iUnion_subset fun _ => inter_subset_right
  have hav := (measureReal_mono hsub (measure_ne_top_of_subset hu measure_Icc_lt_top.ne)).trans
    (measureReal_iUnion_fintype_le T)
  calc
    _ ≤ (2:ℝ)^d*∑ W, volume.real (T W) := mul_le_mul_of_nonneg_left hav (by positivity)
    _ = ∑ W, (2:ℝ)^d*volume.real (T W) := Finset.mul_sum ..
    _ ≤ ∑ _ : J, (t+G) := Finset.sum_le_sum fun W _ => by
      simpa only [T,two_mul] using hsign W.val.val o t t ht
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,J]

#print axioms cheap_snapshot_volume
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
