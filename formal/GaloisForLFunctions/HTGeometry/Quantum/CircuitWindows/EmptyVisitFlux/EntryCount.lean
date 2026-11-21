import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.ContactDates
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.EntryFaces
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.EntryIsolation

/-! # Exact entry rate of the continuous enclosing-arc visit set -/
open Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section

/-- Every physical entry date in the positive observation window, with
coincident endpoint labels counted only once. -/
def entryDates {I : Type*} [Fintype I] (E : I → ℝ) (r T : ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ : Finset (I×I)).biUnion fun p => markedDates E p.1 p.2 r (forwardUnitArc r) T

theorem mem_entryDates {I : Type*} [Fintype I] (E : I → ℝ) {r : ℝ} (hr : 0≤r)
    (hs : r<1/2) (t T : ℝ) : t ∈ entryDates E r T ↔
    0<t ∧ t≤T ∧ visitEntry (fun i => E i/(2*Real.pi)) r t := by
  classical
  have hh : r<1 := by linarith only [hs]
  rw [entryDates,Finset.mem_biUnion,entry_iff_closed_face _ hr hs]
  constructor
  · rintro ⟨⟨i,j⟩,_,hm⟩
    obtain ⟨hp,ht,hf⟩ := (mem_markedDates E i j hr hh _ t T).mp hm
    exact ⟨hp,ht,i,j,hf⟩
  · rintro ⟨hp,ht,i,j,hf⟩
    exact ⟨(i,j),Finset.mem_univ _,(mem_markedDates E i j hr hh _ t T).mpr ⟨hp,ht,hf⟩⟩

/-- Total number of descending pair turns per unit time. Each unordered
pair contributes its absolute energy gap divided by 2π. -/
def pairTurnRate {I : Type*} [Fintype I] (E : I → ℝ) : ℝ :=
  ∑ p : I×I, max 0 (E p.1-E p.2)/(2*Real.pi)

/-- The count of genuine continuous-time entries per unit time has an
exact limit. Tied endpoint labels disappear between the strict and closed
pair counts, whose rates coincide on every winding clock. -/
theorem entry_count_rate {I : Type*} [Fintype I] [DecidableEq I] (E : I → ℝ)
    (hi : MaximallyProjectiveEnergy E) {r : ℝ} (hr : 0<r) (hs : r<1/2) :
    Tendsto (fun T : ℝ => ((entryDates E r T).card:ℝ)/T) atTop
      (𝓝 (r^(Fintype.card I-2)*pairTurnRate E)) := by
  classical
  let K := I×I
  let V (A : Set UnitAddCircle) (T : ℝ) (p : K) := markedDates E p.1 p.2 r A T
  let count (A : Set UnitAddCircle) (T : ℝ) := ∑ p : K, ((V A T p).card:ℝ)/T
  let O := openArc r
  let C := forwardUnitArc r
  have hh : r<1 := by linarith only [hs]
  have hsum (A) (hA : A∈({O,C}:Set (Set UnitAddCircle))) : Tendsto (count A) atTop
      (𝓝 (r^(Fintype.card I-2)*pairTurnRate E)) := by
    rw [pairTurnRate,Finset.mul_sum]
    exact tendsto_finsetSum _ fun p _ => markedDates_rate E hi p.1 p.2 ⟨r,hr.le,hs.le⟩ A hA
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hsum O (Or.inl rfl)) (hsum C (Or.inr rfl))
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    have hdis : (↑(Finset.univ : Finset K) : Set K).PairwiseDisjoint (V O T) := by
      intro p _ q _ hpq
      refine Finset.disjoint_left.mpr fun t hp hq => ?_
      have hf := ((mem_markedDates E p.1 p.2 hr.le hh O t T).mp hp).2.2
      have hg := ((mem_markedDates E q.1 q.2 hr.le hh O t T).mp hq).2.2
      have h := inward_endpoints_unique hr hs hf hg.2.1
      exact hpq (Prod.ext h.1.symm h.2.symm)
    have hsub : Finset.univ.biUnion (V O T) ⊆ entryDates E r T := by
      intro t ht
      obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨ht0,htT,hf⟩ := (mem_markedDates E p.1 p.2 hr.le hh O t T).mp hp
      apply (mem_entryDates E hr.le hs t T).mpr
      refine ⟨ht0,htT,(entry_iff_closed_face _ hr.le hs).mpr ⟨p.1,p.2,hf.1,hf.2.1,?_⟩⟩
      exact fun k hki hkj => image_mono Ioo_subset_Icc_self (hf.2.2 k hki hkj)
    have hcount := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdis] at hcount
    dsimp only [count]
    rw [←Finset.sum_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) hT
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    have hcount : (entryDates E r T).card ≤ ∑ p : K, (V C T p).card := Finset.card_biUnion_le
    dsimp only [count]
    rw [←Finset.sum_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) hT

#print axioms entry_count_rate
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
