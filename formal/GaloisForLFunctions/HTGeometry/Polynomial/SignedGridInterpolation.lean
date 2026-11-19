import GaloisForLFunctions.HTGeometry.PolynomialSublevelSlicing

/-!
# Polynomial interpolation on signed tuples without repeated magnitudes

To release one coordinate of an n-variable polynomial, exclude at most
n−1 occupied magnitudes. Each remaining positive node gives two roots of
a univariate slice. Once its degree is below this root count, that
coordinate may take any real value.
-/

noncomputable section
open MvPolynomial Finset
namespace GaloisForLFunctions.HTGeometry.SignedGrid
variable {n : ℕ}

private theorem signed_card (T : Finset ℝ) (pos : ∀ t∈T, 0<t) :
    (T∪T.image Neg.neg).card=2*T.card := by
  classical
  have dis : Disjoint T (T.image Neg.neg) := by
    apply disjoint_left.mpr
    intro x hx he
    obtain ⟨y,hy,rfl⟩ := mem_image.mp he
    exact (not_lt_of_ge (neg_nonpos.mpr (pos _ hy).le)) (pos _ hx)
  rw [card_union_of_disjoint dis,card_image_of_injective _ neg_injective,two_mul]

private theorem axis_eval (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    (lineSlice p (fun j => if j=i then 1 else 0) (Function.update x i 0)).eval t=
      eval (Function.update x i t) p := by
  rw [lineSlice_eval]
  apply congrArg (fun u : Fin n → ℝ => eval u p)
  funext j
  by_cases eq : j=i <;> simp [eq,Function.update_of_ne]

/-- A polynomial below the signed-grid degree threshold is determined by
its values on tuples of distinct magnitudes in a positive finite alphabet. -/
theorem interpolation (S : Finset ℝ) (pos : ∀ s∈S, 0<s) (p : MvPolynomial (Fin n) ℝ)
    (size : ∀ _ : Fin n, p.totalDegree+2*(n-1)<2*S.card) :
    p=0 ↔ ∀ x : Fin n → ℝ, (∀ i, |x i|∈S) →
      Function.Injective (fun i => |x i|) → eval x p=0 := by
  classical
  constructor
  · rintro rfl x _ _
    exact map_zero _
  · intro original
    have release (F : Finset (Fin n)) : ∀ x : Fin n → ℝ,
        (∀ j∉F, |x j|∈S) →
        (∀ j∉F, ∀ k∉F, |x j|=|x k| → j=k) → eval x p=0 := by
      induction F using Finset.induction_on with
      | empty =>
        intro x nodes sep
        exact original x (fun i => nodes i (notMem_empty _)) (fun i j => sep i (notMem_empty _) j (notMem_empty _))
      | @insert i F free ih =>
        intro x nodes sep
        let B := (univ : Finset (Fin n)) \ insert i F
        let taken := B.image fun j => |x j|
        let T := S \ taken
        have memB (j : Fin n) : j∈B ↔ j∉insert i F := by simp [B]
        have bb : B ⊆ univ.erase i := by
          intro j hj
          exact mem_erase.mpr ⟨fun h => (memB j).mp hj (h ▸ mem_insert_self _ _),mem_univ _⟩
        have cardB := card_le_card bb
        rw [card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin] at cardB
        have ct : taken.card≤n-1 := card_image_le.trans cardB
        have left : S.card-taken.card≤T.card := le_card_sdiff _ _
        have tp (t : ℝ) (ht : t∈T) := pos t (mem_sdiff.mp ht).1
        let W := T∪T.image Neg.neg
        have cw : p.totalDegree<W.card := by
          have eq := signed_card T tp
          have sz := size i
          change p.totalDegree<(T∪T.image Neg.neg).card
          omega
        let L := lineSlice p (fun j => if j=i then 1 else 0) (Function.update x i 0)
        have Lzero : L=0 := by
          apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' L W _ ((natDegree_lineSlice_le p le_rfl _ _).trans_lt cw)
          intro t ht
          have htT : |t|∈T := by
            rcases mem_union.mp ht with h|h
            · rwa [abs_of_pos (tp t h)]
            · obtain ⟨u,hu,rfl⟩ := mem_image.mp h
              simpa only [abs_neg,abs_of_pos (tp u hu)] using hu
          have fresh (j : Fin n) (hj : j∉insert i F) : |x j|≠|t| :=
            fun eq => (mem_sdiff.mp htT).2 (mem_image.mpr ⟨j,(memB _).mpr hj,eq⟩)
          change (lineSlice _ _ _).eval t=0
          rw [axis_eval]
          apply ih
          · intro j hj
            by_cases eq : j=i
            · subst j
              simpa only [Function.update_self] using (mem_sdiff.mp htT).1
            · rw [Function.update_of_ne eq]
              exact nodes _ (fun h => (mem_insert.mp h).elim eq hj)
          · intro j hj k hk equal
            by_cases ji : j=i
            · subst j
              by_contra ne
              have ki : k ≠ i := Ne.symm ne
              rw [Function.update_self,Function.update_of_ne ki] at equal
              exact fresh k (fun h => (mem_insert.mp h).elim ki hk) equal.symm
            · by_cases ki : k=i
              · subst k
                rw [Function.update_of_ne ji,Function.update_self] at equal
                exact (fresh j (fun h => (mem_insert.mp h).elim ji hj) equal).elim
              · rw [Function.update_of_ne ji,Function.update_of_ne ki] at equal
                exact sep j (fun h => (mem_insert.mp h).elim ji hj) k (fun h => (mem_insert.mp h).elim ki hk) equal
        have atX := congrArg (fun h : Polynomial ℝ => h.eval (x i)) Lzero
        simpa only [L,axis_eval,Function.update_eq_self,Polynomial.eval_zero] using atX
    apply MvPolynomial.funext
    intro x
    rw [map_zero]
    exact release univ x (by simp) (by simp)

#print axioms interpolation
end GaloisForLFunctions.HTGeometry.SignedGrid
