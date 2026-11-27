import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularParabolicCosets
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerInductionDoubleCosets

/-! A simple root crossing the parabolic blocks cancels the contribution
of every unitriangular–parabolic double coset outside the open cell. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

private def upperElementary {i j : Fin n} (h : i < j) (t : ZMod g) :
    upperUnitriangular g n :=
  ⟨elemUnit h.ne t, by
    have ht := transvection_isUpperUnipotent h t
    intro r s
    exact ⟨ht.1 r s, fun e => by subst s; exact ht.2 r⟩⟩

private theorem whittakerCharacter_upperElementary (ψ : AddChar (ZMod g) ℂ)
    {i j : Fin n} (hij : i < j) (h : i.val + 1 = j.val) (t : ZMod g) :
    (whittakerCharacter ψ n (upperElementary hij t) : ℂ) = ψ t := by
  change ψ (∑ k ∈ Finset.range (n - 1), entN (Matrix.transvection i j t) k (k + 1)) = ψ t
  apply congrArg ψ
  have hi : i.val < n - 1 := by have := j.isLt; omega
  rw [Finset.sum_eq_single_of_mem i.val (Finset.mem_range.mpr hi)]
  · have h₁ : i.val < n := i.isLt
    have h₂ : i.val + 1 < n := h.symm ▸ j.isLt
    rw [entN, dif_pos ⟨h₁, h₂⟩]
    have hj : (⟨i.val + 1, h₂⟩ : Fin n) = j := Fin.ext h
    rw [hj]
    change Matrix.transvection i j t i j = t
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hij.ne,
      Matrix.single_apply_same, zero_add]
  · intro k hk hki
    have hk' := Finset.mem_range.mp hk
    let r : Fin n := ⟨k, by omega⟩
    let s : Fin n := ⟨k + 1, by omega⟩
    have hrs : r ≠ s := fun e => Nat.ne_of_lt (Nat.lt_succ_self k) (congrArg Fin.val e)
    have hir : i ≠ r := fun e => hki (congrArg Fin.val e).symm
    have he : entN (Matrix.transvection i j t) k (k + 1) = Matrix.transvection i j t r s := by
      rw [entN, dif_pos ⟨r.isLt, s.isLt⟩]
    rw [he, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hrs]
    simp [hir]

private theorem permutation_conj_elementary (σ : Equiv.Perm (Fin n)) {i j : Fin n}
    (hij : i ≠ j) (t : ZMod g) :
    (permutationUnit σ)⁻¹ * elemUnit (i := σ i) (j := σ j) (fun e => hij (σ.injective e)) t *
      permutationUnit σ = elemUnit hij t := by
  apply Units.ext
  ext r s
  rw [monomialConj_apply]
  simp [elemUnit_val, Matrix.transvection, Matrix.one_apply, Matrix.single_apply, σ.injective.eq_iff]

variable {a b : ℕ}

private def upperRightElementary (i j : Fin (a + b)) (hi : i.val < a) (hj : a ≤ j.val)
    (t : ZMod g) : (twoBlockLevi (g := g) (a := a) (b := b)).ker := by
  have hij : i < j := hi.trans_le hj
  let u := upperElementary hij t
  let p : twoBlockParabolic g a b := ⟨u.val, upperUnitriangular_le_twoBlockParabolic u.property⟩
  refine ⟨p, Prod.ext (Units.ext ?_) (Units.ext ?_)⟩
  · change tl a (Matrix.transvection i j t) = 1
    ext r s
    rw [tl_apply_add]
    have hjs : j ≠ Fin.castAdd b s := fun he => not_lt_of_ge hj ((congrArg Fin.val he).symm ▸ s.isLt)
    simp [Matrix.transvection, Matrix.one_apply, hjs]
  · change br a b (Matrix.transvection i j t) = 1
    ext r s
    rw [br_apply_add]
    have hir : i ≠ Fin.natAdd a r := by
      intro he
      have e : i.val = a + r.val := congrArg Fin.val he
      omega
    simp [Matrix.transvection, Matrix.one_apply, hir]

/-- A non-open permutation representative has zero Whittaker overlap contribution. -/
theorem whittaker_overlap_eq_zero_of_crossing (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    (σ : Equiv.Perm (Fin (a + b)))
    (hne : firstBlockImage σ ≠ firstBlockImage (openCellPermutation a b))
    (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    doubleCosetPairing (upperUnitriangular g (a + b)) (twoBlockParabolic g a b)
      (fun u => (whittakerCharacter ψ (a + b) u : ℂ))
      (fun p => α (twoBlockLevi p).1 * β (twoBlockLevi p).2) (permutationUnit σ) = 0 := by
  let U := upperUnitriangular g (a + b)
  let P := twoBlockParabolic g a b
  let χ := whittakerCharacter ψ (a + b)
  let x : Gn g (a + b) := permutationUnit σ
  let O := doubleCosetOverlap U P x
  letI : Fintype O := Fintype.ofFinite O
  obtain ⟨i, j, hi, hj, hs⟩ := exists_adjacent_crossing σ hne
  obtain ⟨t, ht⟩ : ∃ t : ZMod g, ψ t ≠ 1 := by
    by_contra! h
    apply hψ
    ext t
    exact h t
  have hlt : σ i < σ j := by
    change (σ i).val < (σ j).val
    omega
  let u := upperElementary hlt t
  let p := upperRightElementary i j hi hj t
  have hij : i < j := hi.trans_le hj
  have he : x⁻¹ * u.val * x = p.val.val :=
    permutation_conj_elementary σ (ne_of_lt hij) t
  let z : O := ⟨u, (mem_doubleCosetOverlap U P x u).mpr (he.symm ▸ p.val.property)⟩
  have hz : χ z.val ≠ 1 := fun h =>
    ht ((whittakerCharacter_upperElementary ψ hlt hs t).symm.trans (congrArg Units.val h))
  have hp : twoBlockLevi (doubleCosetOverlapConj U P x z) = 1 :=
    (congrArg twoBlockLevi (Subtype.ext he)).trans p.property
  apply doubleCosetPairing_linear_eq_zero_of_invariance U P χ _ x z hz
  intro y
  rw [map_mul, hp, one_mul]

end GlobalTheory.GLq
