import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularMonomialCosets
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDoubleCosets

/-! The upper roots that remain upper after monomial conjugation determine
whether the representative intertwines the Whittaker character. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

/-- Adjacent indices correspond to simple upper roots. -/
abbrev Adjacent (i j : Fin n) : Prop := i.val + 1 = j.val

/-- An upper root remaining upper must preserve adjacency. The column
entries on each surviving simple root must agree. -/
def WhittakerMonomialCompatible (σ : Equiv.Perm (Fin n)) (c : Fin n → (ZMod g)ˣ) : Prop :=
  ∀ ⦃i j : Fin n⦄, i < j → σ i < σ j →
    (Adjacent i j ↔ Adjacent (σ i) (σ j)) ∧ (Adjacent i j → c i = c j)

private theorem lt_of_adjacent {i j : Fin n} (h : Adjacent i j) : i < j := by
  change i.val < j.val
  rw [← h]
  exact Nat.lt_succ_self _

private def adjacentTerm (M : Mt g n) (z : Fin n × Fin n) : ZMod g :=
  if Adjacent z.1 z.2 then M z.1 z.2 else 0

private def adjacentSum (M : Mt g n) : ZMod g := ∑ z, adjacentTerm M z

private theorem sum_superdiagonal_eq (M : Mt g n) :
    (∑ i ∈ Finset.range (n - 1), entN M i (i + 1)) = adjacentSum M := by
  have e (i : Fin n) : entN M i.val (i.val + 1) = ∑ j, adjacentTerm M (i, j) := by
    by_cases h : i.val + 1 < n
    · let j : Fin n := ⟨i.val + 1, h⟩
      have h₁ : Adjacent i j := rfl
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
      · simp only [adjacentTerm, if_pos h₁, entN, i.isLt, h, and_self, ↓reduceDIte]
        rfl
      · intro k _ hk
        exact if_neg (fun e => hk (Fin.ext e.symm))
    · have hz (j : Fin n) : ¬Adjacent i j := fun t => h (t.symm ▸ j.isLt)
      have hsum : ∑ j : Fin n, adjacentTerm M (i, j) = 0 :=
        Finset.sum_eq_zero fun j _ => if_neg (hz j)
      rw [hsum]
      simp [entN, h]
  calc
    _ = ∑ i ∈ Finset.range n, entN M i (i + 1) := by
      refine Finset.sum_subset (Finset.range_mono (Nat.sub_le n 1)) fun i hi hx => ?_
      have h : ¬i + 1 < n := by
        rw [Finset.mem_range] at hi hx
        omega
      simp [entN, h]
    _ = ∑ i : Fin n, entN M i.val (i.val + 1) :=
      (Fin.sum_univ_eq_sum_range (fun k => entN M k (k + 1)) n).symm
    _ = _ := by
      rw [adjacentSum, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => e i

private theorem whittakerCharacter_val (ψ : AddChar (ZMod g) ℂ) (x : upperUnitriangular g n) :
    (whittakerCharacter ψ n x : ℂ) = ψ (adjacentSum (x.val : Mt g n)) := by
  change ψ (∑ i ∈ Finset.range (n - 1), entN (x.val : Mt g n) i (i + 1)) = _
  rw [sum_superdiagonal_eq]

private theorem prime_addChar_injective {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) :
    Function.Injective ψ := by
  apply AddChar.injective_iff.mpr
  intro x hx
  by_contra hn
  apply hψ
  ext y
  let k := (y * x⁻¹).val
  have hk : k • x = y := by
    change ((y * x⁻¹).val : ℕ) • x = y
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hn, mul_one]
  change ψ y = 1
  rw [← hk, AddChar.map_nsmul_eq_pow, hx, one_pow]

private theorem transvection_isUniUp {i j : Fin n} (hij : i < j) (a : ZMod g) :
    IsUniUp (Matrix.transvection i j a) := by
  have h := transvection_isUpperUnipotent hij a
  intro r s
  exact ⟨h.1 r s, fun e => by
    subst s
    exact h.2 r⟩

private theorem adjacentSum_transvection (i j : Fin n) (a : ZMod g) :
    adjacentSum (Matrix.transvection i j a) = if Adjacent i j then a else 0 := by
  unfold adjacentSum
  rw [Finset.sum_eq_single_of_mem (i, j) (Finset.mem_univ _)]
  · change (if Adjacent i j then Matrix.transvection i j a i j else 0) = _
    split_ifs with h
    · rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne (lt_of_adjacent h).ne,
        Matrix.single_apply_same, zero_add]
    · rfl
  · rintro ⟨r, s⟩ _ h
    have he : ¬(i = r ∧ j = s) := fun ⟨hr, hs⟩ => h (Prod.ext hr.symm hs.symm)
    by_cases hrs : Adjacent r s
    · change (if Adjacent r s then Matrix.transvection i j a r s else 0) = 0
      rw [if_pos hrs, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne (lt_of_adjacent hrs).ne,
        Matrix.single_apply_of_ne i j a r s he, zero_add]
    · exact if_neg hrs

private theorem monomialConj_transvection (σ : Equiv.Perm (Fin n)) (c : Fin n → (ZMod g)ˣ)
    {i j : Fin n} (hij : i ≠ j) (a : ZMod g) :
    (((monomialUnit σ c)⁻¹ * elemUnit (i := σ i) (j := σ j) (fun h => hij (σ.injective h)) a *
      monomialUnit σ c : Gn g n) : Mt g n) =
      Matrix.transvection i j ((c i : ZMod g)⁻¹ * a * c j) := by
  ext r s
  rw [monomialConj_apply, elemUnit_val]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, σ.injective.eq_iff]
  by_cases e : r = s
  · subst s
    have h : ¬(i = r ∧ j = r) := fun he => hij (he.1.trans he.2.symm)
    simp only [if_true, if_neg h, add_zero, mul_one, inv_mul_cancel₀ (Units.ne_zero (c r))]
  · simp only [if_neg e, zero_add]
    by_cases h : i = r ∧ j = s
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, if_true]
    · simp only [if_neg h, mul_zero, zero_mul]

private theorem compatible_of_intertwines {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → (ZMod g)ˣ)
    (h : (whittakerCharacter ψ n).Intertwines (upperUnitriangular g n) (monomialUnit σ c)) :
    WhittakerMonomialCompatible σ c := by
  intro i j hij hσ
  let T := elemUnit hσ.ne (1 : ZMod g)
  let t : upperUnitriangular g n := ⟨T, transvection_isUniUp hσ 1⟩
  let X := monomialUnit σ c
  let z : ZMod g := (c i : ZMod g)⁻¹ * c j
  have hz : z ≠ 0 := mul_ne_zero (inv_ne_zero (Units.ne_zero (c i))) (Units.ne_zero (c j))
  have he : ((X⁻¹ * (t : Gn g n) * X : Gn g n) : Mt g n) = Matrix.transvection i j z := by
    exact (monomialConj_transvection σ c hij.ne 1).trans (congrArg (Matrix.transvection i j) (congrArg (· * (c j : ZMod g)) (mul_one _)))
  have ht : X⁻¹ * (t : Gn g n) * X ∈ upperUnitriangular g n := by
    rw [mem_upperUnitriangular, he]
    exact transvection_isUniUp hij z
  have e := congrArg Units.val (h t ht)
  change (whittakerCharacter ψ n ⟨X⁻¹ * (t : Gn g n) * X, ht⟩ : ℂ) =
      (whittakerCharacter ψ n t : ℂ) at e
  rw [whittakerCharacter_val, whittakerCharacter_val] at e
  have ee := prime_addChar_injective hψ e
  change adjacentSum ((X⁻¹ * (t : Gn g n) * X : Gn g n) : Mt g n) =
    adjacentSum (Matrix.transvection (σ i) (σ j) 1) at ee
  rw [he, adjacentSum_transvection, adjacentSum_transvection] at ee
  have hiff : Adjacent i j ↔ Adjacent (σ i) (σ j) := by
    constructor
    · intro ha
      by_contra hb
      rw [if_pos ha, if_neg hb] at ee
      exact hz ee
    · intro hb
      by_contra ha
      rw [if_neg ha, if_pos hb] at ee
      exact zero_ne_one ee
  refine ⟨hiff, fun ha => Units.ext ?_⟩
  rw [if_pos ha, if_pos (hiff.mp ha)] at ee
  exact (inv_mul_eq_one₀ (Units.ne_zero (c i))).mp ee

/-- Compatibility of a monomial double coset is exactly the adjacency and
column-entry condition on roots that stay upper under conjugation. -/
theorem intertwines_monomial_iff {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → (ZMod g)ˣ) :
    (whittakerCharacter ψ n).Intertwines (upperUnitriangular g n) (monomialUnit σ c) ↔
      WhittakerMonomialCompatible σ c := by
  refine ⟨compatible_of_intertwines hψ σ c, fun h t ht => ?_⟩
  let X := monomialUnit σ c
  let M := (t.val : Mt g n)
  let B := ((X⁻¹ * (t : Gn g n) * X : Gn g n) : Mt g n)
  have hM : IsUniUp M := mem_upperUnitriangular.mp t.2
  have hB : IsUniUp B := mem_upperUnitriangular.mp ht
  have e (i j : Fin n) : B i j = (c i : ZMod g)⁻¹ * M (σ i) (σ j) * c j :=
    monomialConj_apply σ c t.val i j
  have hm (i j : Fin n) : adjacentTerm B (i, j) = adjacentTerm M (σ i, σ j) := by
    change (if Adjacent i j then B i j else 0) = if Adjacent (σ i) (σ j) then M (σ i) (σ j) else 0
    by_cases hi : Adjacent i j
    · have hij := lt_of_adjacent hi
      by_cases hj : Adjacent (σ i) (σ j)
      · have hc := (h hij (lt_of_adjacent hj)).2 hi
        rw [if_pos hi, if_pos hj, e, ← hc, mul_right_comm, inv_mul_cancel₀ (Units.ne_zero (c i)), one_mul]
      · have hgt : σ j < σ i := by
          apply lt_of_le_of_ne _ (fun eq => hij.ne (σ.injective eq.symm))
          exact le_of_not_gt (fun hlt => hj ((h hij hlt).1.mp hi))
        rw [if_pos hi, if_neg hj, e, (hM _ _).1 hgt, mul_zero, zero_mul]
    · by_cases hj : Adjacent (σ i) (σ j)
      · have hσ := lt_of_adjacent hj
        have hgt : j < i := lt_of_le_of_ne (le_of_not_gt fun hlt => hi ((h hlt hσ).1.mpr hj))
          (fun eq => hσ.ne (congrArg σ eq.symm))
        have hz := (e i j).symm.trans ((hB i j).1 hgt)
        have hzero : M (σ i) (σ j) = 0 :=
          (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (Units.ne_zero (c j)))).resolve_left
            (inv_ne_zero (Units.ne_zero (c i)))
        rw [if_neg hi, if_pos hj, hzero]
      · rw [if_neg hi, if_neg hj]
  apply Units.ext
  change (whittakerCharacter ψ n ⟨X⁻¹ * (t : Gn g n) * X, ht⟩ : ℂ) = _
  rw [whittakerCharacter_val, whittakerCharacter_val]
  apply congrArg ψ
  calc
    adjacentSum B = ∑ z : Fin n × Fin n, adjacentTerm M ((σ.prodCongr σ) z) :=
      Finset.sum_congr rfl fun ⟨i, j⟩ _ => hm i j
    _ = adjacentSum M := Equiv.sum_comp (σ.prodCongr σ) (adjacentTerm M)

end GlobalTheory.GLq
