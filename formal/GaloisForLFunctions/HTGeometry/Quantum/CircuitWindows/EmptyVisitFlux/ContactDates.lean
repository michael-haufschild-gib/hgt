import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.PhysicalClock

/-! # Exact enumeration of all positive inward pair dates -/
open Set
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section

private theorem exists_tick {I : Type*} (E : I → ℝ) {r t : ℝ} {i j : I}
    (hr : 0 ≤ r) (ht : 0 < t) (hg : E j < E i)
    (hc : flow (fun k => E k/(2*Real.pi)) t j-flow (fun k => E k/(2*Real.pi)) t i=(r:UnitAddCircle)) :
    ∃ k : ℕ, pairDate E i j r k = t := by
  let δ := (E i-E j)/(2*Real.pi)
  have hd : 0<δ := div_pos (sub_pos.mpr hg) (by positivity)
  have hn : ((-(t*δ):ℝ):UnitAddCircle)=(r:UnitAddCircle) := by
    rw [←hc]
    simp only [flow,←AddCircle.coe_sub]
    congr 1
    dsimp only [δ]
    ring
  have hper : ((t*δ+r:ℝ):UnitAddCircle)=0 := by
    rw [AddCircle.coe_add,←hn,AddCircle.coe_neg,add_neg_cancel]
  obtain ⟨m,hm⟩ := (AddCircle.coe_eq_zero_iff 1).mp hper
  rw [zsmul_eq_mul,mul_one] at hm
  have hmpos : (0:ℝ) < m := by rw [hm]; exact add_pos_of_pos_of_nonneg (mul_pos ht hd) hr
  have hm' : 0 < m := by exact_mod_cast hmpos
  lift m to ℕ using hm'.le
  cases m with
  | zero => simp at hm'
  | succ k =>
    refine ⟨k,?_⟩
    push_cast at hm
    have he : 1-r+(k:ℝ)=t*δ := by linarith only [hm]
    unfold pairDate
    rw [he]
    dsimp only [δ]
    field_simp [(sub_pos.mpr hg).ne']

/-- Filtering by the real date and by the endpoint constraints counts
every marked pair time exactly once on (0,T]. -/
theorem mem_markedDates {I : Type*} (E : I → ℝ) (i j : I) {r : ℝ} (hr : 0≤r)
    (hs : r<1) (A : Set UnitAddCircle) (t T : ℝ) :
    t ∈ markedDates E i j r A T ↔ 0<t ∧ t≤T ∧ pairFace A (fun k => E k/(2*Real.pi)) r t i j := by
  classical
  by_cases hg : E j<E i
  · let τ := 2*Real.pi/(E i-E j)
    have hτ : 0<τ := div_pos (by positivity) (sub_pos.mpr hg)
    have he (k : ℕ) : pairDate E i j r k = (1-r)*τ+(k:ℝ)*τ := by dsimp only [pairDate,τ]; ring
    rw [markedDates,if_pos hg]
    constructor
    · rintro h
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hb,hc⟩ := Finset.mem_filter.mp hk
      refine ⟨?_,?_,hc⟩
      · rw [he]
        exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hs) hτ) (mul_nonneg (Nat.cast_nonneg _) hτ.le)
      · rw [he]
        exact (mem_tickIndices hτ k).mp hb
    · rintro ⟨ht,hT,hc⟩
      obtain ⟨k,hk⟩ := exists_tick E hr ht hg hc.2.1
      refine Finset.mem_image.mpr ⟨k,Finset.mem_filter.mpr ⟨(mem_tickIndices hτ k).mpr ?_,hk.symm ▸ hc⟩,hk⟩
      rwa [←he,hk]
  · rw [markedDates,if_neg hg]
    refine ⟨fun h => (Finset.notMem_empty _ h).elim,fun h => ?_⟩
    exact (hg ((div_lt_div_iff_of_pos_right (by positivity : 0<2*Real.pi)).mp h.2.2.1)).elim

#print axioms mem_markedDates
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
