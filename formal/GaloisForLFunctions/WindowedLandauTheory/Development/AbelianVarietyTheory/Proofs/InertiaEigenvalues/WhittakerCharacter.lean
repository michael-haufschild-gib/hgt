import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterNorm
import GaloisForLFunctions.HTGeometry.SteinbergTWTWeylKernel
import GaloisForLFunctions.RHTower.Artin.ArtinMonomialCharacter
import Mathlib.GroupTheory.OrderOfElement

/-! The Gelfand–Graev character is induced from the sum of the first superdiagonal
entries of the upper unitriangular subgroup. -/

open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

private theorem isUniUp_iff {n : ℕ} (M : Mt g n) :
    IsUniUp M ↔ HTGeometry.IsUpperUnipotent M := by
  constructor
  · intro h
    exact ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩
  · intro h i j
    refine ⟨h.1 i j, ?_⟩
    rintro rfl
    exact h.2 i

private def upperUnitriangularMonoid (g n : ℕ) [Fact g.Prime] : Submonoid (Gn g n) where
  carrier := {x | IsUniUp (x : Mt g n)}
  one_mem' := by
    change IsUniUp (1 : Mt g n)
    intro i j
    refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), ?_⟩
    rintro rfl
    exact Matrix.one_apply_eq i
  mul_mem' := by
    intro x y hx hy
    exact (isUniUp_iff _).2 (((isUniUp_iff _).1 hx).mul ((isUniUp_iff _).1 hy))

/-- Unitriangular matrices form a subgroup since the ambient group is finite. -/
def upperUnitriangular (g n : ℕ) [Fact g.Prime] : Subgroup (Gn g n) :=
  { upperUnitriangularMonoid g n with
    inv_mem' := by
      intro x hx
      have h : x ^ (orderOf x - 1) * x = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
      rw [inv_eq_of_mul_eq_one_left h]
      exact (upperUnitriangularMonoid g n).pow_mem hx _ }

@[simp]
theorem mem_upperUnitriangular {n : ℕ} {x : Gn g n} :
    x ∈ upperUnitriangular g n ↔ IsUniUp (x : Mt g n) := Iff.rfl

private theorem entN_superdiagonal_mul {n : ℕ} (A B : Mt g n)
    (hA : IsUniUp A) (hB : IsUniUp B) (i : ℕ) :
    entN (A * B) i (i + 1) = entN A i (i + 1) + entN B i (i + 1) := by
  by_cases hj : i + 1 < n
  · have hi : i < n := by omega
    simp only [entN, hi, hj, and_self, ↓reduceDIte]
    rw [Matrix.mul_apply, Finset.sum_eq_add (⟨i, hi⟩ : Fin n) ⟨i + 1, hj⟩]
    · rw [(hA _ _).2 rfl, (hB _ _).2 rfl, one_mul, mul_one, add_comm]
    · intro e
      have he := congrArg Fin.val e
      exact Nat.ne_of_lt (Nat.lt_succ_self i) he
    · intro k _ ⟨hki, hkj⟩
      by_cases hlow : k < (⟨i, hi⟩ : Fin n)
      · rw [(hA _ _).1 hlow, zero_mul]
      · have hv₁ : k.val ≠ i := fun e => hki (Fin.ext e)
        have hv₂ : k.val ≠ i + 1 := fun e => hkj (Fin.ext e)
        change ¬ k.val < i at hlow
        have hgt : (⟨i + 1, hj⟩ : Fin n) < k := by
          change i + 1 < k.val
          omega
        rw [(hB _ _).1 hgt, mul_zero]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · simp [entN, hj]

/-- The first superdiagonal sum is a homomorphism to the additive residue field. -/
def superdiagonalSum (n : ℕ) : upperUnitriangular g n →* Multiplicative (ZMod g) where
  toFun u := Multiplicative.ofAdd
    (∑ i ∈ Finset.range (n - 1), entN (u.val : Mt g n) i (i + 1))
  map_one' := by
    change (∑ i ∈ Finset.range (n - 1), entN (1 : Mt g n) i (i + 1)) = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    unfold entN
    split_ifs with h
    · exact Matrix.one_apply_ne (fun e => Nat.ne_of_lt (Nat.lt_succ_self i) (congrArg Fin.val e))
    · rfl
  map_mul' u v := by
    change (∑ i ∈ Finset.range (n - 1), entN ((u.val : Mt g n) * (v.val : Mt g n)) i (i + 1)) =
      (∑ i ∈ Finset.range (n - 1), entN (u.val : Mt g n) i (i + 1)) +
        ∑ i ∈ Finset.range (n - 1), entN (v.val : Mt g n) i (i + 1)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => entN_superdiagonal_mul _ _
      (mem_upperUnitriangular.mp u.property) (mem_upperUnitriangular.mp v.property) i

/-- The linear character used in Gelfand–Graev induction. -/
def whittakerCharacter (ψ : AddChar (ZMod g) ℂ) (n : ℕ) :
    LinearCharacter (upperUnitriangular g n) :=
  (ψ.toMonoidHom.comp (superdiagonalSum n)).toHomUnits

/-- The defining average for `gg` is ordinary character induction. -/
theorem gg_eq_inducedFunction (ψ : AddChar (ZMod g) ℂ) (n : ℕ) :
    gg ψ n = inducedFunction (upperUnitriangular g n) (fun u => (whittakerCharacter ψ n u : ℂ)) := by
  classical
  let U := upperUnitriangular g n
  let S : Finset (Gn g n) := Finset.univ.filter (fun u : Gn g n => IsUniUp (u : Mt g n))
  let e : {u : Gn g n // u ∈ U} ≃ {u : Gn g n // u ∈ S} :=
    Equiv.subtypeEquivRight fun u => by
      change u ∈ upperUnitriangular g n ↔ u ∈ (Finset.univ.filter fun v : Gn g n => IsUniUp (v : Mt g n))
      rw [mem_upperUnitriangular, Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, And.right⟩
  have hcard : Nat.card U = S.card := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  funext x
  unfold gg inducedFunction
  rw [hcard]
  refine congrArg (fun z : ℂ => (S.card : ℂ)⁻¹ * z) ?_
  refine Fintype.sum_equiv (Equiv.inv (Gn g n)) _ _ fun y => ?_
  simp only [Equiv.inv_apply, inv_inv]
  by_cases hy : IsUniUp ((y⁻¹ * x * y : Gn g n) : Mt g n)
  · rw [if_pos hy, extendByZero_of_mem _ _ (mem_upperUnitriangular.mpr hy)]
    rfl
  · rw [if_neg hy, extendByZero_of_notMem _ _ (fun h => hy (mem_upperUnitriangular.mp h))]

/-- In particular, the Gelfand–Graev class function is a genuine character. -/
theorem gg_eq_monomialCharacter (ψ : AddChar (ZMod g) ℂ) (n : ℕ) :
    gg ψ n = (monomialGenuineCharacter (Gn g n) (upperUnitriangular g n)
      (whittakerCharacter ψ n)).val := by
  rw [gg_eq_inducedFunction]
  funext x
  rw [monomialGenuineCharacter_apply, induced_character_eq_inducedFunction]
  congr 1
  funext u
  exact (linearCharacterRepresentation_character _ _).symm

private theorem wh_formula (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (χ : Gn g n → ℂ) :
    wh ψ χ = ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ *
      ∑ u : Gn g n, (if IsUniUp (u : Mt g n) then
        (ψ (∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)))⁻¹ else 0) * χ u := by
  unfold wh tr eU eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, Finsupp.single_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc]
  congr 2
  rw [Finset.sum_ite_eq']
  simp

private theorem gg_term_inv (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (u : Gn g n) :
    (if IsUniUp ((u⁻¹ : Gn g n) : Mt g n) then
        ψ (∑ i ∈ Finset.range (n - 1), entN ((u⁻¹ : Gn g n) : Mt g n) i (i + 1)) else 0) =
      if IsUniUp (u : Mt g n) then (ψ (∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)))⁻¹ else 0 := by
  by_cases hu : IsUniUp (u : Mt g n)
  · let v : upperUnitriangular g n := ⟨u, mem_upperUnitriangular.mpr hu⟩
    have hi : IsUniUp ((u⁻¹ : Gn g n) : Mt g n) :=
      mem_upperUnitriangular.mp (v⁻¹).property
    rw [if_pos hi, if_pos hu]
    change (whittakerCharacter ψ n v⁻¹ : ℂ) = (whittakerCharacter ψ n v : ℂ)⁻¹
    rw [map_inv, Units.val_inv_eq_inv_val]
  · have hi : ¬ IsUniUp ((u⁻¹ : Gn g n) : Mt g n) := fun h =>
      hu (mem_upperUnitriangular.mp (inv_mem_iff.mp (mem_upperUnitriangular.mpr h)))
    rw [if_neg hi, if_neg hu]

/-- The pairing with the induced character is the Whittaker projection trace. -/
theorem ip_gg (ψ : AddChar (ZMod g) ℂ) (n : ℕ) (χ : Gn g n → ℂ) (hχ : IsClass χ) :
    ip χ (gg ψ n) = wh ψ χ := by
  set c : ℂ := ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ with hc
  set F : Gn g n → ℂ := fun z => if IsUniUp (z : Mt g n) then
    ψ (∑ i ∈ Finset.range (n - 1), entN (z : Mt g n) i (i + 1)) else 0 with hF
  have hgg : ∀ x, gg ψ n x = c * ∑ y : Gn g n, F (y⁻¹ * x * y) := fun x => rfl
  have hinner : ∀ y : Gn g n, ∑ x : Gn g n, χ x * F (y⁻¹ * x⁻¹ * y) = ∑ u : Gn g n, χ u * F u⁻¹ := by
    intro y
    let e : Gn g n ≃ Gn g n :=
      ⟨fun x => y⁻¹ * x * y, fun u => y * u * y⁻¹, fun x => by group, fun u => by group⟩
    refine Fintype.sum_equiv e _ _ fun x => ?_
    have h1 : χ (y⁻¹ * x * y) = χ x := by
      have := hχ x y⁻¹
      rwa [inv_inv] at this
    have h2 : y⁻¹ * x⁻¹ * y = (y⁻¹ * x * y)⁻¹ := by group
    change χ x * F (y⁻¹ * x⁻¹ * y) = χ (y⁻¹ * x * y) * F (y⁻¹ * x * y)⁻¹
    rw [h1, h2]
  have hG : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e1 : ∑ x : Gn g n, χ x * gg ψ n x⁻¹ = c * ∑ y : Gn g n, ∑ x : Gn g n, χ x * F (y⁻¹ * x⁻¹ * y) := by
    simp only [hgg, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
  have e2 : wh ψ χ = c * ∑ u : Gn g n, χ u * F u⁻¹ := by
    rw [wh_formula]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_comm]
    congr 1
    exact (gg_term_inv ψ u).symm
  unfold ip
  rw [e1, e2, Finset.sum_congr rfl fun y _ => hinner y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_left_comm, ← mul_assoc, ← mul_assoc, mul_assoc c, inv_mul_cancel₀ hG, mul_one]

private theorem ip_eq_characterPairing {G : Type} [Group G] [Fintype G] (χ η : G → ℂ) :
    ip χ η = characterPairing G η χ := by
  rw [ip, characterPairing, Nat.card_eq_fintype_card]

/-- Distinct irreducible characters with nonzero Whittaker trace are counted by
the squared norm of the Gelfand–Graev character. -/
theorem card_le_wh_gg (ψ : AddChar (ZMod g) ℂ) (n : ℕ) (S : Finset (Gn g n → ℂ))
    (hS : ∀ χ ∈ S, IsIrr χ ∧ wh ψ χ ≠ 0) :
    (S.card : ℝ) ≤ (wh ψ (gg ψ n)).re := by
  have hvirt : gg ψ n ∈ virtualCharacterGroup (Gn g n) := by
    rw [gg_eq_monomialCharacter]
    exact genuineCharacterMonoid_le_virtualCharacterGroup _ (monomialGenuineCharacter _
      (upperUnitriangular g n) (whittakerCharacter ψ n)).property
  have hclass : IsClass (gg ψ n) := by
    intro x y
    rw [gg_eq_inducedFunction]
    exact inducedFunction_conj (upperUnitriangular g n) _ y x
  rw [← ip_gg ψ n _ hclass, ip_eq_characterPairing]
  refine CuspGL.card_le_pairing_of_nonzero_on_simple hvirt S fun χ hχ => ?_
  obtain ⟨⟨V, hV, hval⟩, hwh⟩ := hS χ hχ
  have hχclass : IsClass χ := by
    intro x y
    rw [← hval (y * x * y⁻¹), ← hval x]
    exact V.char_conj x y
  refine ⟨⟨V, hV, funext hval⟩, ?_⟩
  rw [← ip_eq_characterPairing, ip_gg ψ n _ hχclass]
  exact hwh

end GlobalTheory.GLq

end
