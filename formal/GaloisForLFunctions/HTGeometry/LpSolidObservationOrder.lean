import GaloisForLFunctions.HTGeometry.LpSolidUniform

/-! # Domination of complete masked-history observations

Pointwise norm domination passes to the full observation supremum. The same
bound controls arbitrary auxiliary observation choices simultaneously.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology
variable {I Y A P : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {l : Filter A}

theorem lpSolidObservation_mono (T S : lp (fun _ : I => ℂ) 2 →L[ℂ] Y)
    (x : lp (fun _ : I => ℂ) 2)
    (h : ∀ y ∈ lpSolidHull x, ‖T y‖ ≤ ‖S y‖) :
    lpSolidObservation T x ≤ lpSolidObservation S x := by
  obtain ⟨m, hm⟩ := lpSolidObservation_attained T x
  rw [← hm]
  exact (h _ (lpMaskedHistory_mem_solidHull x m)).trans (norm_masked_le_lpSolidObservation S x m)

theorem tendstoUniformly_lpMaskedHistory_of_norm_le
    (T : A → P → lp (fun _ : I => ℂ) 2 →L[ℂ] Y)
    (S : A → lp (fun _ : I => ℂ) 2 →L[ℂ] Y) (x : lp (fun _ : I => ℂ) 2)
    (h : ∀ a p y, ‖T a p y‖ ≤ ‖S a y‖)
    (hS : TendstoUniformly (fun a m => S a (lpMaskedHistory x m)) (fun _ => 0) l) :
    TendstoUniformly (fun a (q : P × LpCoordinateMask I) => T a q.1 (lpMaskedHistory x q.2))
      (fun _ => 0) l := by
  rw [Metric.tendstoUniformly_iff] at hS ⊢
  intro ε hε
  filter_upwards [hS ε hε] with a ha
  intro q
  simpa only [dist_zero_left] using
    (h a q.1 (lpMaskedHistory x q.2)).trans_lt (by simpa only [dist_zero_left] using ha q.2)

theorem tendstoUniformly_lpSolidObservation_of_norm_le
    (T : A → P → lp (fun _ : I => ℂ) 2 →L[ℂ] Y)
    (S : A → lp (fun _ : I => ℂ) 2 →L[ℂ] Y) (x : lp (fun _ : I => ℂ) 2)
    (h : ∀ a p y, ‖T a p y‖ ≤ ‖S a y‖)
    (hS : Tendsto (fun a => lpSolidObservation (S a) x) l (𝓝 0)) :
    TendstoUniformly (fun a p => lpSolidObservation (T a p) x) (fun _ => 0) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hS.eventually_lt_const hε] with a ha
  intro p
  rw [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg (lpSolidObservation_nonneg _ _)]
  exact (lpSolidObservation_mono _ _ x (fun y _ => h a p y)).trans_lt ha

end
end GaloisForLFunctions.HTGeometry
