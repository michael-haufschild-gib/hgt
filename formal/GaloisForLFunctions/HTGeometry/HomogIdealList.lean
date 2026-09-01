import GaloisForLFunctions.HTGeometry.DegreePartMonotone
import GaloisForLFunctions.HTGeometry.CohenMacaulayLifting

/-!
# Homogeneity of ideals built by adjoining a list of forms

```text
isHomogIdeal_sup                a sup of homogeneous ideals is homogeneous
isHomogIdeal_span_singleton     a principal ideal on a form is homogeneous
ofList_take_succ                the list ideal, one entry at a time
isHomogIdeal_ofList_sup         ** adjoining a list of forms keeps an ideal homogeneous **
isXGraded_sup_ofList_C          ** and adjoining their constants keeps a family `x`-graded **
map_ofList                      list ideals push forward along ring maps
```

Bookkeeping for the degeneration iteration: at stage `i` the two ideals being compared are the
original ones with the first `i` entries of a regular sequence adjoined, and every hypothesis of the
degeneration step — homogeneity on both sides, `x`-gradedness of the family upstairs — has to be
carried along the induction.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

theorem isHomogIdeal_sup {a b : Ideal (MvPolynomial σ K)} (ha : IsHomogIdeal a)
    (hb : IsHomogIdeal b) : IsHomogIdeal (a ⊔ b) := by
  intro e f hf
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (ha e x hx))
    (Submodule.mem_sup_right (hb e y hy))

theorem isHomogIdeal_bot : IsHomogIdeal (⊥ : Ideal (MvPolynomial σ K)) := by
  intro e f hf
  rw [Ideal.mem_bot.mp hf, map_zero]
  exact Ideal.zero_mem _

theorem isHomogIdeal_span_singleton {l : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d) :
    IsHomogIdeal (Ideal.span {l}) := by
  intro e f hf
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  rcases lt_or_ge e d with hlt | hge
  · rw [mul_comm g l, homogeneousComponent_mul_left_of_lt hl g hlt]
    exact Ideal.zero_mem _
  · obtain ⟨e', rfl⟩ : ∃ e', e = d + e' := ⟨e - d, by omega⟩
    rw [mul_comm g l, homogeneousComponent_mul_left hl g e']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self l)

theorem map_ofList {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (l : List R) :
    Ideal.map f (Ideal.ofList l) = Ideal.ofList (l.map f) := by
  classical
  rw [Ideal.ofList, Ideal.ofList, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact List.mem_map.mpr ⟨y, hy, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ⟨y, hy, rfl⟩

theorem ofList_take_succ {R : Type*} [CommRing R] (l : List R) (i : ℕ) (hi : i < l.length) :
    Ideal.ofList (l.take (i + 1)) = Ideal.ofList (l.take i) ⊔ Ideal.span {l[i]} := by
  classical
  rw [Ideal.ofList, Ideal.ofList, ← Ideal.span_union]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  rw [List.take_add_one, List.mem_append]
  simp [List.getElem?_eq_getElem hi]

theorem ofList_map_take_succ {R S : Type*} [CommRing S] (f : R → S) (l : List R) (i : ℕ)
    (hi : i < l.length) :
    Ideal.ofList ((l.map f).take (i + 1))
      = Ideal.ofList ((l.map f).take i) ⊔ Ideal.span {f l[i]} := by
  rw [← List.map_take, ← List.map_take, List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
  rw [ofList_append, ofList_cons, ofList_nil, sup_bot_eq]

/-- **Adjoining a list of forms keeps an ideal homogeneous.** -/
theorem isHomogIdeal_ofList_sup {a : Ideal (MvPolynomial σ K)} (ha : IsHomogIdeal a) :
    ∀ (ls : List (MvPolynomial σ K)), (∀ l ∈ ls, ∃ d, l.IsHomogeneous d) →
      IsHomogIdeal (a ⊔ Ideal.ofList ls)
  | [], _ => by
      rw [Ideal.ofList, show {x : MvPolynomial σ K | x ∈ ([] : List _)} = ∅ from by ext; simp,
        Ideal.span_empty, sup_bot_eq]
      exact ha
  | (l :: t), h => by
      obtain ⟨d, hd⟩ := h l (List.mem_cons_self ..)
      rw [ofList_cons, ← sup_assoc]
      exact isHomogIdeal_ofList_sup (isHomogIdeal_sup ha (isHomogIdeal_span_singleton hd)) t
        (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **Adjoining the constants of a list of forms keeps a family `x`-graded.** -/
theorem isXGraded_sup_ofList_C {A : Ideal (Polynomial (MvPolynomial σ K))}
    (hA : IsXGradedIdeal A) :
    ∀ (ls : List (MvPolynomial σ K)), (∀ l ∈ ls, ∃ d, l.IsHomogeneous d) →
      IsXGradedIdeal (A ⊔ Ideal.ofList (ls.map Polynomial.C))
  | [], _ => by
      rw [List.map_nil, Ideal.ofList,
        show {x : Polynomial (MvPolynomial σ K) | x ∈ ([] : List _)} = ∅ from by ext; simp,
        Ideal.span_empty, sup_bot_eq]
      exact hA
  | (l :: t), h => by
      obtain ⟨d, hd⟩ := h l (List.mem_cons_self ..)
      rw [List.map_cons, ofList_cons, ← sup_assoc]
      exact isXGraded_sup_ofList_C (isXGraded_sup_span_C hA hd) t
        (fun x hx => h x (List.mem_cons_of_mem _ hx))

end GaloisForLFunctions.HTGeometry
