import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.Kinematics.ClosingSpeed
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ComponentCounts
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.CrossingWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # The outer entry leading to the first deep return from the near-Hilbert crossing -/
open MeasureTheory Filter Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
open EmptyVisitFlux SharpOccupation
noncomputable section

private theorem enclosing_entry {B : Set ℝ} (hB : IsClosed B) {σ v : ℝ} (hσ : σ∉B)
    (hv : v∈B) (hσv : σ≤v) (A : ℝ→Finset ℝ)
    (hA : ∀ t T, t∈A T ↔ σ<t ∧ t≤T ∧ Entry B t) :
    ∃ a∈A v, Icc a v ⊆ B := by
  obtain ⟨u,hu,he⟩ := first_after hB hσ hσv hv
  have hn : (A v).Nonempty := ⟨u,(hA ..).mpr ⟨hu.1,hu.2,he⟩⟩
  let a := (A v).max' hn
  have ha : a∈A v := Finset.max'_mem _ _
  refine ⟨a,ha,?_⟩
  intro t ht
  by_contra h
  obtain ⟨z,hz,hent⟩ := first_after hB h ht.2 hv
  have hσa := ((hA a v).mp ha).1
  have hz' : z∈A v := (hA z v).mpr ⟨(hσa.trans_le ht.1).trans hz.1,hz.2,hent⟩
  exact (ht.1.trans_lt hz.1).not_ge (Finset.le_max' _ _ hz')

/-- At the first empty return of accuracy δ following the physical crossing,
the elapsed time from its containing ρ-entry is pinned by the full
bandwidth. The same bound forces every closing pair of that entry toward
the extreme energies as the ratio of inner to outer arc width vanishes. -/
theorem gaussian_first_deep_entry_edges :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let E := fun i => -H.2.isHermitian.eigenvalues i
      let w := fun i => E i/(2*π)
      let W := Finset.univ.sup' Finset.univ_nonempty w-Finset.univ.inf' Finset.univ_nonempty w
      ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        ∀ ρ∈Ioo (0:ℝ) (9/80), ∀ δ∈Ioc (0:ℝ) ρ,
          let r := physicalArc ρ
          let d := physicalArc δ
          let v := PrecisionReturns.firstVisit H σ 0 δ
          ∃ a∈entriesAfter E r σ v, Icc a v ⊆ visitSet H 0 ρ ∧
            (v-a)*W ∈ Icc (r-d) (r+d) ∧
            ∀ i j, pairFace (forwardUnitArc r) w r a i j → (r-d)*W ≤ (r+d)*(w i-w j) := by
  filter_upwards [gaussian_first_crossing_flux] with ω hw
  filter_upwards [hw] with k hk
  intro N H P E w W
  obtain ⟨σ,hσ,he,hb,hc⟩ := hk
  refine ⟨σ,hσ,he,hb,?_⟩
  intro ρ hρ δ hδ r d v
  have hsmall : (9/80:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  have hρs := hρ.2.trans hsmall
  have hδs := hδ.2.trans_lt hρs
  obtain ⟨hr,her⟩ := physicalArc_spec hρ.1 hρs
  obtain ⟨hd,hed⟩ := physicalArc_spec hδ.1 hδs
  have hdr : d≤r := by
    by_contra! h
    have hlt := strictMonoOn_zeroGateArcTolerance (Ioo_subset_Icc_self hr) (Ioo_subset_Icc_self hd) h
    rw [her,hed] at hlt
    exact hlt.not_ge hδ.2
  have hm := (PrecisionReturns.firstVisit_isLeast H σ 0 hδ.1).1
  have hσv : σ≤v := hm.1
  have hv : v∈visitSet H 0 δ := hm.2
  have hvρ : v∈visitSet H 0 ρ := by
    obtain ⟨z,hz,C,hC,hfit⟩ := hv
    exact ⟨z,hz,C,hC,hfit.trans hδ.2⟩
  have hno : σ∉visitSet H 0 ρ := by
    rintro ⟨z,hz,C,hC,hfit⟩
    have hp : HasProjectiveCircuitApproximation N ρ P (unitaryEvolution H.val σ) :=
      ⟨z,hz,C,hC.trans (Nat.zero_le _),hfit⟩
    have hh : orbitCircuitDistance H P σ≤ρ := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hp
    exact hρ.2.not_ge (he.symm.trans_le hh)
  have hclosed : IsClosed (visitSet H 0 ρ) := by
    simp only [visitSet,hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const
  obtain ⟨a,ha,hseg⟩ := enclosing_entry hclosed hno hvρ hσv (entriesAfter E r σ) (hc ρ hρ.1 hρs).1
  have hav := ((hc ρ hρ.1 hρs).1 a v |>.mp ha).2.1
  have hpath (s) (hs : s∈Icc a v) := (physical_visit H hρ.1 hρs s).mpr (hseg hs)
  have hend := (physical_visit H hδ.1 hδs v).mpr hv
  obtain ⟨p,_,hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty w
  obtain ⟨q,_,hq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty w
  have hW : W=w p-w q := by
    change Finset.univ.sup' _ w-Finset.univ.inf' _ w=_
    rw [hp,hq]
  have hentry := ((mem_entryDates E hr.1.le hr.2 a v).mp (Finset.mem_sdiff.mp ha).1).2.2
  obtain ⟨i,j,hij⟩ := (entry_iff_closed_face w hr.1.le hr.2).mp hentry
  have hgap : w i-w j≤W := sub_le_sub (Finset.le_sup' w (Finset.mem_univ i)) (Finset.inf'_le w (Finset.mem_univ j))
  refine ⟨a,ha,hseg,⟨(closing_travel_to_depth w hd.1.le hdr hr.2 hav hij.1 hij.2.1 hend).trans
    (mul_le_mul_of_nonneg_left hgap (sub_nonneg.mpr hav)),?_⟩,?_⟩
  · rw [hW]
    exact travel_until_depth w hd.1.le hdr hr.2 hav hpath hend p q
  · rw [hW]
    exact fun i j hf => deep_entry_speed w hd.1.le hdr hr.2 hav hf hpath hend p q

#print axioms gaussian_first_deep_entry_edges
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
