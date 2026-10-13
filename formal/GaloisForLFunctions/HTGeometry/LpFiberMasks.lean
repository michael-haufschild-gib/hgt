import GaloisForLFunctions.HTGeometry.LpFiberObservation

/-! # Arbitrary contraction masks of full channel histories

At every depth the mask acts on the whole channel space. No continuity or
coherence between the masks at different depths or different times is required.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology
variable {I A Y : Type*} {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] {l : Filter A}

abbrev LpFiberMask (E : I → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)] := ∀ i, Metric.closedBall (0 : E i →L[ℂ] E i) 1

theorem lpFiberMask_norm_le (m : LpFiberMask E) (i : I) : ‖(m i).val‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using (m i).property

theorem lpFiberMask_apply_norm_le (x : lp E 2) (m : LpFiberMask E) (i : I) :
    ‖(m i).val (x i)‖ ≤ ‖x i‖ := by
  exact ((m i).val.le_opNorm _).trans (by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (lpFiberMask_norm_le m i) (norm_nonneg (x i)))

def lpFiberMaskedHistory (x : lp E 2) (m : LpFiberMask E) : lp E 2 :=
  ⟨fun i => (m i).val (x i), (lp.memℓp x).mono' (lpFiberMask_apply_norm_le x m)⟩

@[simp] theorem lpFiberMaskedHistory_apply (x : lp E 2) (m : LpFiberMask E) (i : I) :
    lpFiberMaskedHistory x m i = (m i).val (x i) := rfl

theorem lpFiberMaskedHistory_mem (x : lp E 2) (m : LpFiberMask E) :
    lpFiberMaskedHistory x m ∈ lpFiberSolidHull x := lpFiberMask_apply_norm_le x m

theorem tendstoUniformly_lpFiberMaskedHistory [∀ i, ProperSpace (E i)]
    (T : A → lp E 2 →L[ℂ] Y) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a, ‖T a‖ ≤ C)
    (hp : ∀ y, Tendsto (fun a => T a y) l (𝓝 0)) (x : lp E 2) :
    TendstoUniformly (fun a m => T a (lpFiberMaskedHistory x m)) (fun _ => 0) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_lpFiberSolidHull T C hC hb hp x) ε hε] with a ha
  intro m
  exact ha _ (lpFiberMaskedHistory_mem x m)

theorem tendsto_moving_lpFiberMaskedHistory [∀ i, ProperSpace (E i)]
    (T : A → lp E 2 →L[ℂ] Y) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a, ‖T a‖ ≤ C)
    (hp : ∀ y, Tendsto (fun a => T a y) l (𝓝 0)) (x : lp E 2)
    (m : A → LpFiberMask E) :
    Tendsto (fun a => T a (lpFiberMaskedHistory x (m a))) l (𝓝 0) :=
  tendsto_zero_of_moving_mem_compact T C hC hb hp _ (isCompact_lpFiberSolidHull x)
    (fun a => lpFiberMaskedHistory x (m a)) (fun a => lpFiberMaskedHistory_mem x (m a))

end
end GaloisForLFunctions.HTGeometry
