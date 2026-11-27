import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.TraceWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.CircuitTargets
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.BudgetOccupation

/-! # Frozen finite-window gate occupation at prescribed replica order -/
open Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open SharpOccupation
noncomputable section

/-- Covering the physical circuit set transfers a uniform family of trace
moment bounds to gate occupation, for any register and observation origin. -/
theorem gate_fraction_of_capture {K : ℕ} (H : selfAdjoint (SharpOccupation.Register K))
    {ε δ ρ : ℝ} (hδ : 0 < δ) (hnearby : ε+δ ≤ ρ) (hρ : 0 ≤ ρ) (hsmall : ρ^2 < 2)
    (s q : ℕ) (o : ℝ) {T m : ℝ} (hT : 0 < T) (hm : 0 ≤ m)
    (hobs : ∀ J : ℕ, ∀ v : Fin J → Fin (2^K) → ℂ, (∀ j i, ‖v j i‖=1) →
      (1-ρ^2/2)^(2*q)*volume.real (⋃ j, uniformTwistedCoherenceCaptureSet (microcanonicalWeight _)
        (H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm) (v j) T (1-ρ^2/2)) ≤ T*J*m) :
    visitFraction H s ε o (o+T) ≤ ((s:ℝ)+1)*((((K:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s*
      (m/(1-ρ^2/2)^(2*q)) := by
  let τ := 1-ρ^2/2
  have hτ₀ : 0 < τ := by dsimp only [τ]; linarith only [hsmall]
  classical
  obtain ⟨F,hcover,hcard⟩ := exists_budget_net K s δ hδ
  let idx : Fin F.card ≃ F := (finCongr (Fintype.card_coe F).symm).trans (Fintype.equivFin F).symm
  let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
  choose v hv htest using fun j : Fin F.card => target_twist H (idx j).val o
  let A j := uniformTwistedCoherenceCaptureSet (microcanonicalWeight (Fin (2^K))) E (v j) T τ
  let G := ⋃ j, A j
  have hG : MeasurableSet G := MeasurableSet.iUnion fun _ => uniformTwistedCoherenceCaptureSet_measurable ..
  have hfin : volume G ≠ ⊤ := ne_top_of_le_ne_top measure_Ioc_lt_top.ne
    (measure_mono (iUnion_subset fun j t ht => (show t∈Ioc (-T) T from ht.1)))
  have htr : MeasurePreserving (fun t : ℝ => t-o) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-o)
  have hs : visitSet H s ε ∩ Icc o (o+T) ⊆ (fun t : ℝ => t-o) ⁻¹' G := by
    rintro t ⟨⟨c,hc,C,hC,he⟩,ht⟩
    obtain ⟨W,hW,hfit⟩ := hcover C hC
    let j := idx.symm ⟨W,hW⟩
    have hnear : ‖unitaryEvolution H.val t-c • (W:SharpOccupation.Register K)‖ ≤ ρ := by
      have hh := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution H.val t)
        (c • (C.eval:SharpOccupation.Register K)) (c • (W:SharpOccupation.Register K))
      rw [←smul_sub,norm_smul,hc,one_mul] at hh
      exact hh.trans ((add_le_add he hfit).trans hnearby)
    apply mem_iUnion.mpr
    refine ⟨j,⟨⟨by linarith only [ht.1,hT],by linarith only [ht.2]⟩,htest j t c hc ρ hρ hsmall ?_⟩⟩
    simpa only [j,Equiv.apply_symm_apply] using hnear
  have hvol := measureReal_mono hs ((htr.measure_preimage hG.nullMeasurableSet).symm ▸ hfin)
  rw [htr.measureReal_preimage hG.nullMeasurableSet] at hvol
  have hcap := hobs F.card v hv
  change τ^(2*q)*volume.real G ≤ T*F.card*m at hcap
  have hτ : 0 < τ^(2*q) := pow_pos hτ₀ _
  have hb := (le_div_iff₀ hτ).mpr ((mul_comm _ _).le.trans hcap)
  rw [visitFraction,add_sub_cancel_left]
  calc _ ≤ (T*F.card*m/τ^(2*q))/T := div_le_div_of_nonneg_right (hvol.trans hb) hT.le
       _ = (F.card:ℝ)*(m/τ^(2*q)) := by field_simp
       _ ≤ _ := mul_le_mul_of_nonneg_right hcard (div_nonneg hm hτ.le)

/-- With probability one, every sufficiently long prefix obeys a single
finite-window bound for all origins, gate budgets and replica orders.
The final term retains the physical observation duration. -/
theorem gaussian_finite_gate_window :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D : ℕ := 2^K
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ ε δ ρ : ℝ, 0 < δ → ε+δ ≤ ρ → 0 ≤ ρ → ρ^2 < 2 → ∀ s q : ℕ, 0 < q → ∀ o : ℝ, ∀ T > (0:ℝ),
        let N := ((s:ℝ)+1)*((((K:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s
        visitFraction H s ε o (o+T) ≤
          N*(momentPrice ((q.factorial:ℝ)/(D:ℝ)^q) (T*effectiveGap k q)/(1-ρ^2/2)^(2*q)) := by
  filter_upwards [gaussian_replica_capture_windows] with ω hw
  filter_upwards [hw] with k hk
  intro K D u H ε δ ρ hδ hnearby hρ hsmall s q hq o T hT N
  apply gate_fraction_of_capture H hδ hnearby hρ hsmall s q o hT
    (momentPrice_nonneg (by positivity) (mul_nonneg hT.le (effectiveGap_pos k q).le))
  exact hk q hq T hT _ (by linarith only [hsmall])

#print axioms gaussian_finite_gate_window
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
