import GaloisForLFunctions.HTGeometry.AffineFramePacketSeparation

/-!
# Generic separation avoiding prescribed node values

A packet occurrence lands on a prescribed point only when a nontrivial affine coordinate condition
holds, because an affine automorphism has a non-constant coordinate.  Adding those defects to the
separation product gives a base which separates the packet, avoids every prescribed value, and
keeps a prescribed nonzero polynomial nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {d : ℕ}

/-- Landing on a prescribed value is a nontrivial coordinate condition. -/
theorem exists_avoid_poly (hd : 0 < d) {row idx : Type*}
    (e : idx → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (a : row) (i : idx) (c : Fin d → ℂ) :
    ∃ G : MvPolynomial (row × Fin d) ℂ, G ≠ 0 ∧
      ∀ v : row × Fin d → ℂ, eval v G ≠ 0 → (e i) (fun l => v (a, l)) ≠ c := by
  classical
  have hex : ∃ k : Fin d,
      (rename (fun l : Fin d => (a, l)) (affineCoordPolynomial (e i) k)
        - C (c k) : MvPolynomial (row × Fin d) ℂ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ z : Fin d → ℂ, (e i) z = c := by
      intro z
      funext k
      have h := congrArg (eval (fun pr : row × Fin d => z pr.2)) (hcon k)
      rw [map_sub, eval_rename, eval_C, map_zero, sub_eq_zero] at h
      simpa [Function.comp_def] using h
    have h0 := hall (Pi.single (⟨0, hd⟩ : Fin d) 1)
    have h1 := hall 0
    have hinj := (e i).injective (h0.trans h1.symm)
    have := congrFun hinj (⟨0, hd⟩ : Fin d)
    simp at this
  obtain ⟨k, hk⟩ := hex
  refine ⟨rename (fun l : Fin d => (a, l)) (affineCoordPolynomial (e i) k) - C (c k), hk, ?_⟩
  intro v hv hcontra
  apply hv
  rw [map_sub, eval_rename, eval_C, sub_eq_zero]
  simp only [Function.comp_def, eval_affineCoordPolynomial]
  rw [hcontra]

/-- **Generic separated base avoiding prescribed values.** -/
theorem exists_base_separating_avoiding_and_eval_ne_zero (hd : 0 < d)
    {row idx τ : Type*} [Fintype row] [DecidableEq row] [Fintype idx] [DecidableEq idx]
    (e : idx → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (he : Function.Injective fun i => ((e i : (Fin d → ℂ) → Fin d → ℂ)))
    (Cav : Finset (Fin d → ℂ))
    (W : MvPolynomial ((row × Fin d) ⊕ τ) ℂ) (hW : W ≠ 0) :
    ∃ (base : row → Fin d → ℂ) (t : τ → ℂ),
      Function.Injective (fun q : row × idx => (e q.2) (base q.1)) ∧
        (∀ q : row × idx, (e q.2) (base q.1) ∉ Cav) ∧
        eval (Sum.elim (fun pr : row × Fin d => base pr.1 pr.2) t) W ≠ 0 := by
  classical
  set A : (row × idx) × Cav → MvPolynomial (row × Fin d) ℂ := fun pr =>
    Classical.choose (exists_avoid_poly hd e pr.1.1 pr.1.2 (pr.2 : Fin d → ℂ)) with hA
  have hAne : ∀ pr, A pr ≠ 0 := fun pr =>
    (Classical.choose_spec (exists_avoid_poly hd e pr.1.1 pr.1.2 (pr.2 : Fin d → ℂ))).1
  have hAspec : ∀ pr, ∀ v : row × Fin d → ℂ, eval v (A pr) ≠ 0 →
      (e pr.1.2) (fun l => v (pr.1.1, l)) ≠ (pr.2 : Fin d → ℂ) := fun pr =>
    (Classical.choose_spec (exists_avoid_poly hd e pr.1.1 pr.1.2 (pr.2 : Fin d → ℂ))).2
  set W' : MvPolynomial ((row × Fin d) ⊕ τ) ℂ :=
    W * rename Sum.inl (∏ pr : (row × idx) × Cav, A pr) with hW'def
  have hW' : W' ≠ 0 := by
    refine mul_ne_zero hW ?_
    intro hzero
    have hz2 : (∏ pr : (row × idx) × Cav, A pr) = 0 :=
      rename_injective (R := ℂ) (Sum.inl : (row × Fin d) → (row × Fin d) ⊕ τ)
        Sum.inl_injective (by rw [hzero, map_zero])
    exact (Finset.prod_ne_zero_iff.mpr fun pr _ => hAne pr) hz2
  obtain ⟨base, t, hsep, hne⟩ := exists_base_separating_and_eval_ne_zero hd e he W' hW'
  set v : (row × Fin d) ⊕ τ → ℂ := Sum.elim (fun pr : row × Fin d => base pr.1 pr.2) t with hv
  have hmulne : eval v W ≠ 0 ∧ eval v (rename Sum.inl (∏ pr : (row × idx) × Cav, A pr)) ≠ 0 := by
    rw [hW'def, map_mul] at hne
    exact ⟨fun h => hne (by rw [h, zero_mul]), fun h => hne (by rw [h, mul_zero])⟩
  refine ⟨base, t, hsep, ?_, hmulne.1⟩
  intro q hq
  have hprod := hmulne.2
  rw [eval_rename] at hprod
  have hfac : ∀ pr : (row × idx) × Cav,
      eval ((fun s => v (Sum.inl s)) : row × Fin d → ℂ) (A pr) ≠ 0 := by
    intro pr hzero
    apply hprod
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ pr) hzero
  have hmem : ((e q.2) (base q.1)) ∈ Cav := hq
  have := hAspec (q, ⟨(e q.2) (base q.1), hmem⟩) _ (hfac (q, ⟨(e q.2) (base q.1), hmem⟩))
  exact this (by rfl)

end

end GaloisForLFunctions.HTGeometry
