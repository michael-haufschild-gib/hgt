import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.CircuitWindows.PhysicalWait
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.CircuitWindows.ComponentSweep
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.AllDepths

/-! # Circuit affordability at genuine scalar entries -/
open Filter MeasureTheory Set Real Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.CircuitWindows
open EmptyVisitFlux SharpOccupation Depth
noncomputable section

/-- Realize a lower exponential base by a strictly tighter physical tolerance.
This leaves room for the error of transporting a circuit from the deeper date. -/
private theorem inner_cutoff {ε ρ l : ℝ} (hε : ε∈Ioo (0:ℝ) (sqrt 2))
    (hρ : ρ∈Ioo (0:ℝ) (sqrt 2)) (hl : l∈Ioo (0:ℝ) (physicalArc ε/physicalArc ρ)) :
    ∃ δ∈Ioo (0:ℝ) ε, l<physicalArc δ/physicalArc ρ := by
  have hx := (physicalArc_spec hρ.1 hρ.2).1
  have hy := (physicalArc_spec hε.1 hε.2).1
  obtain ⟨y,hy₁,hy₂⟩ := exists_between ((lt_div_iff₀ hx.1).mp hl.2)
  have hpos := (mul_pos hl.1 hx.1).trans hy₁
  have hI : y∈Icc (0:ℝ) (1/2) := ⟨hpos.le,(hy₂.trans hy.2).le⟩
  let δ := zeroGateArcTolerance y
  have hd : 0<δ := by
    rw [show (0:ℝ)=zeroGateArcTolerance 0 by simp [zeroGateArcTolerance]]
    exact strictMonoOn_zeroGateArcTolerance (by norm_num) hI hpos
  have he : δ<ε := (strictMonoOn_zeroGateArcTolerance hI (Ioo_subset_Icc_self hy) hy₂).trans_eq
    (physicalArc_spec hε.1 hε.2).2
  obtain ⟨hv,ht⟩ := physicalArc_spec hd (he.trans hε.2)
  have hid : physicalArc δ=y := strictMonoOn_zeroGateArcTolerance.injOn (Ioo_subset_Icc_self hv) hI ht
  exact ⟨δ,⟨hd,he⟩,(lt_div_iff₀ hx.1).mpr (hid ▸ hy₁)⟩

/-- For a fixed forward window the exponential base of the affordable
fraction is the ratio of the inner and outer enclosing widths. The lower
bound already holds at the entry date with one gate per bond, or at any
budget after waiting A/N. The upper bound applies through gᴰ time units. -/
theorem gaussian_scalar_entry_circuit_fraction :
    ∃ A K : ℝ, 0<A ∧ 0<K ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ s : ℕ→ℕ, subcriticalBudget s → ∀ ρ∈Ioo (0:ℝ) (sqrt 2), ∀ ε∈Ioo (0:ℝ) ρ,
      ∀ l∈Ioo (0:ℝ) (physicalArc ε/physicalArc ρ), ∀ g : ℝ, 1≤g →
      ∀ q∈Ioo (g*physicalArc ε/physicalArc ρ) 1, ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        let P := nearHilbertContinuousCircuitBudget N
        let E := fun j => -H.2.isHermitian.eigenvalues j
        ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧
          (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧ ∀ j ≤ s N,
          ∀ᶠ T : ℝ in atTop, ∀ W∈Icc (0:ℝ) (g^D), A/N≤W ∨ N-1≤j →
            let F := entriesAfter E (physicalArc ρ) σ T
            let f := ((followed F (visitSet H j ε) W).card:ℝ)/(F.card:ℝ)
            l^D<f ∧ f<K*q^D := by
  classical
  obtain ⟨A,B,hA,_,hS⟩ := gaussian_component_sweep
  obtain ⟨K,hK,hU⟩ := gaussian_physical_circuit_forward_wait
  refine ⟨A,K,hA,hK,?_⟩
  filter_upwards [hS,hU,gaussian_scalar_component_depth] with ω hS hU hM
  intro s hs ρ hρ ε hε l hl g hg q hq
  have hε' : ε∈Ioo (0:ℝ) (sqrt 2) := ⟨hε.1,hε.2.trans hρ.2⟩
  obtain ⟨δ,hδ,hbase⟩ := inner_cutoff hε' hρ hl
  have hδρ : δ∈Ioc (0:ℝ) ρ := ⟨hδ.1,(hδ.2.trans hε.2).le⟩
  have hδ' := physicalArc_spec hδ.1 (hδ.2.trans hε'.2)
  have hρ' := physicalArc_spec hρ.1 hρ.2
  have hratio : physicalArc δ/physicalArc ρ≤1 := by
    apply (div_le_one hρ'.1.1).mpr
    by_contra! h
    have hh := strictMonoOn_zeroGateArcTolerance (Ioo_subset_Icc_self hρ'.1) (Ioo_subset_Icc_self hδ'.1) h
    rw [hρ'.2,hδ'.2] at hh
    exact hh.not_ge hδρ.2
  have ht : Tendsto (fun k : ℕ => ((k+3:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have herr := (ht.const_div_atTop B).eventually_lt_const (sub_pos.mpr hδ.2)
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hS,hU s hs ε hε' ρ hρ g hg q hq,herr] with k hS hU herr
  intro N D H P E
  obtain ⟨σ,hσ,he,hbefore,hupper⟩ := hU
  refine ⟨σ,hσ,he,hbefore,?_⟩
  intro j hj
  have hpow : l^D<(physicalArc δ/physicalArc ρ)^(D-2) :=
    (pow_lt_pow_left₀ hbase hl.1.le (show D≠0 by dsimp [D]; positivity)).trans_le
      (pow_le_pow_of_le_one (hl.1.trans hbase).le hratio (Nat.sub_le ..))
  have hlower := (hM k σ hσ.le ρ hρ δ hδρ).eventually_const_lt hpow
  filter_upwards [hlower,hupper j hj] with T hlower hupper
  intro W hW hw F f
  have mono (U V : Finset ℝ) (huv : U⊆V) :
      (U.card:ℝ)/(F.card:ℝ)≤(V.card:ℝ)/(F.card:ℝ) :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card huv)) (Nat.cast_nonneg _)
  constructor
  · apply hlower.trans_le
    apply mono
    intro u hu
    obtain ⟨hmem,v,huv,hv,hseg⟩ := Finset.mem_filter.mp hu
    obtain ⟨hwidth,htrans⟩ := hS ρ hρ u v huv hseg
    apply Finset.mem_filter.mpr
    refine ⟨hmem,?_⟩
    rcases hw with hw|hj'
    · obtain ⟨z,hz,C,hC,hfit⟩ := hv
      exact ⟨v,⟨huv,by linarith only [hwidth,hw]⟩,z,hz,C,hC.trans (Nat.zero_le j),hfit.trans hδ.2.le⟩
    · obtain ⟨z,hz,C,hC,hfit⟩ := htrans 0 δ hv
      have hc : C.gateCount≤j := by dsimp only [N] at hj'; omega
      exact ⟨u,⟨le_rfl,le_add_of_nonneg_right hW.1⟩,z,hz,C,hc,hfit.trans (by linarith only [herr])⟩
  · apply lt_of_le_of_lt _ hupper
    apply mono
    intro u hu
    obtain ⟨hum,v,hv,hfit⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨hum,(show ∃ v∈Icc u (u+g^D), v∈visitSet H j ε from
      ⟨v,⟨hv.1,hv.2.trans (add_le_add (le_refl u) hW.2)⟩,hfit⟩)⟩

#print axioms gaussian_scalar_entry_circuit_fraction
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.CircuitWindows
