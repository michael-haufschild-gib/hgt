import GaloisForLFunctions.HTGeometry.AffineJetPacketPrescription
import GaloisForLFunctions.HTGeometry.PolynomialEvaluationLemma

/-!
# Generic separation of an affine frame packet

Two occurrences of a packet collide when one frame sends its row point to the same place as
another.  Each coincidence is the vanishing of a degree-one polynomial in the base coordinates
which is not identically zero: distinct frames disagree somewhere, and a single frame is injective.
Multiplying those coordinate defects into any prescribed nonzero polynomial and evaluating at a
nonvanishing point produces one base which separates the whole packet and keeps the prescribed
polynomial nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {d : ℕ}

/-- The `k`-th coordinate of the difference of two frames evaluated at two base rows. -/
def coordDiffPoly {row : Type*} (e₁ e₂ : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (a b : row) (k : Fin d) : MvPolynomial (row × Fin d) ℂ :=
  rename (fun l : Fin d => (a, l)) (affineCoordPolynomial e₁ k) -
    rename (fun l : Fin d => (b, l)) (affineCoordPolynomial e₂ k)

@[simp] theorem eval_coordDiffPoly {row : Type*} (e₁ e₂ : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (a b : row) (k : Fin d) (v : row × Fin d → ℂ) :
    eval v (coordDiffPoly e₁ e₂ a b k) =
      e₁ (fun l => v (a, l)) k - e₂ (fun l => v (b, l)) k := by
  simp [coordDiffPoly, eval_rename, Function.comp_def]

/-- A coincidence between two distinct packet occurrences is a nontrivial coordinate condition. -/
theorem exists_coordDiffPoly_ne_zero (hd : 0 < d) {row idx : Type*}
    (e : idx → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (he : Function.Injective fun i => ((e i : (Fin d → ℂ) → Fin d → ℂ)))
    {a b : row} {i j : idx} (hq : (a, i) ≠ (b, j)) :
    ∃ k : Fin d, coordDiffPoly (e i) (e j) a b k ≠ 0 := by
  classical
  by_contra hcon
  have hcon' : ∀ k : Fin d, coordDiffPoly (e i) (e j) a b k = 0 := by
    intro k
    by_contra hk
    exact hcon ⟨k, hk⟩
  have hall : ∀ v : row × Fin d → ℂ,
      (e i) (fun l => v (a, l)) = (e j) (fun l => v (b, l)) := by
    intro v
    funext k
    have := congrArg (eval v) (hcon' k)
    rw [eval_coordDiffPoly] at this
    simpa [sub_eq_zero] using this
  by_cases hab : a = b
  · subst hab
    have hij : i ≠ j := by
      intro h
      exact hq (by rw [h])
    refine hij (he ?_)
    show (⇑(e i) : (Fin d → ℂ) → Fin d → ℂ) = ⇑(e j)
    funext z
    simpa using hall (fun pr => z pr.2)
  · have hconst : ∀ z : Fin d → ℂ, (e i) z = (e j) (fun _ => (0 : ℂ)) := by
      intro z
      have := hall (fun pr => if pr.1 = a then z pr.2 else 0)
      simpa [hab, Ne.symm hab] using this
    have hzero : (e i) (Pi.single (⟨0, hd⟩ : Fin d) 1) = (e i) 0 :=
      (hconst _).trans (hconst 0).symm
    have hval := congrFun ((e i).injective hzero) (⟨0, hd⟩ : Fin d)
    simp at hval

/-- A separating polynomial for one ordered pair of packet occurrences. -/
theorem exists_sep_poly (hd : 0 < d) {row idx : Type*}
    (e : idx → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (he : Function.Injective fun i => ((e i : (Fin d → ℂ) → Fin d → ℂ)))
    {q₁ q₂ : row × idx} (hq : q₁ ≠ q₂) :
    ∃ G : MvPolynomial (row × Fin d) ℂ, G ≠ 0 ∧
      ∀ v : row × Fin d → ℂ, eval v G ≠ 0 →
        (e q₁.2) (fun l => v (q₁.1, l)) ≠ (e q₂.2) (fun l => v (q₂.1, l)) := by
  obtain ⟨k, hk⟩ := exists_coordDiffPoly_ne_zero hd e he
    (a := q₁.1) (b := q₂.1) (i := q₁.2) (j := q₂.2) (by simpa using hq)
  refine ⟨coordDiffPoly (e q₁.2) (e q₂.2) q₁.1 q₂.1 k, hk, fun v hv hcontra => hv ?_⟩
  rw [eval_coordDiffPoly, hcontra, sub_self]

/-- **Generic separated base.**  Any prescribed nonzero polynomial in the base coordinates and the
remaining variables admits a nonvanishing point whose base separates the whole affine packet. -/
theorem exists_base_separating_and_eval_ne_zero (hd : 0 < d)
    {row idx τ : Type*} [Fintype row] [DecidableEq row] [Fintype idx] [DecidableEq idx]
    (e : idx → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (he : Function.Injective fun i => ((e i : (Fin d → ℂ) → Fin d → ℂ)))
    (W : MvPolynomial ((row × Fin d) ⊕ τ) ℂ) (hW : W ≠ 0) :
    ∃ (base : row → Fin d → ℂ) (t : τ → ℂ),
      Function.Injective (fun q : row × idx => (e q.2) (base q.1)) ∧
        eval (Sum.elim (fun pr : row × Fin d => base pr.1 pr.2) t) W ≠ 0 := by
  classical
  let Gtot : (row × idx) × (row × idx) → MvPolynomial (row × Fin d) ℂ := fun pr =>
    if h : pr.1 = pr.2 then 1 else Classical.choose (exists_sep_poly hd e he h)
  have hGtot : ∀ pr, Gtot pr ≠ 0 := by
    intro pr
    by_cases h : pr.1 = pr.2
    · simp [Gtot, h]
    · simpa [Gtot, h] using (Classical.choose_spec (exists_sep_poly hd e he h)).1
  let P : MvPolynomial ((row × Fin d) ⊕ τ) ℂ :=
    W * rename Sum.inl (∏ pr : (row × idx) × (row × idx), Gtot pr)
  have hP : P ≠ 0 := by
    refine mul_ne_zero hW ?_
    intro hzero
    have hz2 : (∏ pr : (row × idx) × (row × idx), Gtot pr) = 0 := by
      refine rename_injective (R := ℂ) (Sum.inl : (row × Fin d) → (row × Fin d) ⊕ τ)
        Sum.inl_injective ?_
      rw [hzero, map_zero]
    exact (Finset.prod_ne_zero_iff.mpr fun pr _ => hGtot pr) hz2
  obtain ⟨w, hw⟩ := AffineJet.exists_eval_ne_zero (K := ℂ) hP
  refine ⟨fun a k => w (Sum.inl (a, k)), fun s => w (Sum.inr s), ?_, ?_⟩
  · intro q₁ q₂ hq
    by_contra hne
    have hspec := Classical.choose_spec (exists_sep_poly hd e he hne)
    have hprod : eval w (rename Sum.inl (∏ pr, Gtot pr)) ≠ 0 := by
      intro hzero
      apply hw
      show eval w (W * rename Sum.inl (∏ pr, Gtot pr)) = 0
      rw [map_mul, hzero, mul_zero]
    rw [eval_rename] at hprod
    rw [map_prod] at hprod
    have hfac : eval (w ∘ Sum.inl) (Gtot (q₁, q₂)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hprod (q₁, q₂) (Finset.mem_univ _)
    have hGeq : Gtot (q₁, q₂) = Classical.choose (exists_sep_poly hd e he hne) := by
      simp [Gtot, hne]
    rw [hGeq] at hfac
    exact hspec.2 (w ∘ Sum.inl) hfac (by simpa using hq)
  · have hwe : Sum.elim (fun pr : row × Fin d => w (Sum.inl (pr.1, pr.2)))
        (fun s : τ => w (Sum.inr s)) = w := by
      funext s
      cases s with
      | inl a => rfl
      | inr b => rfl
    rw [hwe]
    intro hzero
    apply hw
    show eval w (W * rename Sum.inl (∏ pr, Gtot pr)) = 0
    rw [map_mul, hzero, zero_mul]

end

end GaloisForLFunctions.HTGeometry
