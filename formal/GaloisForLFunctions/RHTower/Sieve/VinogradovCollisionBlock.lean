import GaloisForLFunctions.RHTower.Sieve.VinogradovBlockCorrelation

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- Ordered pair of distinct coordinates witnessing a collision. -/
abbrev VinogradovCollisionWitness (k : ℕ) :=
  {ij : Fin k × Fin k // ij.1 ≠ ij.2}

theorem card_vinogradovCollisionWitness (k : ℕ) :
    Fintype.card (VinogradovCollisionWitness k) = k * k - k := by
  rw [Fintype.card_of_subtype (Finset.offDiag (Finset.univ : Finset (Fin k)))
    (by intro ij; simp [Finset.mem_offDiag])]
  rw [Finset.offDiag_card]
  simp

def vinogradovCollisionRestrictionEmbedding
    {N k : ℕ} (w : VinogradovCollisionWitness k) :
    {x : Fin k → Fin N // x w.1.1 = x w.1.2} ↪
      ({a : Fin k // a ≠ w.1.2} → Fin N) where
  toFun x a := x.1 a.1
  inj' := by
    intro x y hxy
    apply Subtype.ext
    funext a
    by_cases ha : a = w.1.2
    · subst a
      rw [← x.2, ← y.2]
      exact congrFun hxy ⟨w.1.1, w.2⟩
    · exact congrFun hxy ⟨a, ha⟩

theorem card_ne_coordinate_subtype {k : ℕ} (j : Fin k) :
    Fintype.card {a : Fin k // a ≠ j} = k - 1 := by
  rw [Fintype.card_subtype_compl (fun a : Fin k => a = j)]
  simp

theorem card_vinogradovCollisionFibre_le
    {N k : ℕ} (w : VinogradovCollisionWitness k) :
    Fintype.card {x : Fin k → Fin N // x w.1.1 = x w.1.2} ≤ N ^ (k - 1) := by
  calc
    Fintype.card {x : Fin k → Fin N // x w.1.1 = x w.1.2} ≤
        Fintype.card ({a : Fin k // a ≠ w.1.2} → Fin N) :=
      Fintype.card_le_of_embedding (vinogradovCollisionRestrictionEmbedding w)
    _ = N ^ (k - 1) := by
      rw [Fintype.card_fun, Fintype.card_fin, card_ne_coordinate_subtype]

/-- Union bound for non-injective length-`k` tuples. -/
theorem card_noninjective_tuples_le (N k : ℕ) :
    Fintype.card {x : Fin k → Fin N // ¬Function.Injective x} ≤
      (k * k - k) * N ^ (k - 1) := by
  let collisionSet : VinogradovCollisionWitness k → Finset (Fin k → Fin N) :=
    fun w => Finset.univ.filter fun x => x w.1.1 = x w.1.2
  have hsubset :
      (Finset.univ.filter fun x : Fin k → Fin N => ¬Function.Injective x) ⊆
        Finset.univ.biUnion collisionSet := by
    intro x hx
    have hnon : ¬Function.Injective x := (Finset.mem_filter.mp hx).2
    obtain ⟨i, j, hijval, hij⟩ := Function.not_injective_iff.mp hnon
    let w : VinogradovCollisionWitness k := ⟨(i, j), hij⟩
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w,
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, hijval⟩⟩
  rw [Fintype.card_of_subtype
    (Finset.univ.filter fun x : Fin k → Fin N => ¬Function.Injective x) (by simp)]
  calc
    (Finset.univ.filter fun x : Fin k → Fin N => ¬Function.Injective x).card ≤
        (Finset.univ.biUnion collisionSet).card := Finset.card_le_card hsubset
    _ ≤ Finset.univ.card * N ^ (k - 1) := by
      apply Finset.card_biUnion_le_card_mul
      intro w _
      calc
        (collisionSet w).card =
            Fintype.card {x : Fin k → Fin N // x w.1.1 = x w.1.2} := by
          symm
          apply Fintype.card_of_subtype (collisionSet w)
          intro x
          simp [collisionSet]
        _ ≤ N ^ (k - 1) := card_vinogradovCollisionFibre_le w
    _ = (k * k - k) * N ^ (k - 1) := by
      rw [Finset.card_univ, card_vinogradovCollisionWitness]

end

end RHTower.Sieve
