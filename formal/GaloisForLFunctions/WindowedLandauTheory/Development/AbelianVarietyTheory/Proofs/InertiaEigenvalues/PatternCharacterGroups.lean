import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCharacter
import GaloisForLFunctions.WindowedLandauTheory.Compat.MatrixTriangular

/-! A transitive, irreflexive pattern of matrix entries gives a finite
unipotent subgroup. An entry sum with no length-two paths is additive there. -/

noncomputable section
open WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

/-- Outside the allowed entries, a pattern matrix agrees with the identity. -/
def InPattern (Φ : Fin n → Fin n → Prop) (M : Mt g n) : Prop :=
  ∀ i j, ¬ Φ i j → M i j = (1 : Mt g n) i j

/-- The sum of the entries selected by a set of roots. -/
def patternEntrySum (E : Fin n → Fin n → Prop) (M : Mt g n) : ZMod g :=
  ∑ i, ∑ j, if E i j then M i j else 0

theorem InPattern.mul {Φ : Fin n → Fin n → Prop}
    (htrans : ∀ i j k, Φ i j → Φ j k → Φ i k)
    {A B : Mt g n} (hA : InPattern Φ A) (hB : InPattern Φ B) : InPattern Φ (A * B) := by
  intro i j hij
  conv_rhs => rw [← one_mul (1 : Mt g n)]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hik : Φ i k
  · have hkj : ¬ Φ k j := fun h => hij (htrans i k j hik h)
    have hk : k ≠ j := fun e => hij (e ▸ hik)
    rw [hB k j hkj, Matrix.one_apply_ne hk, mul_zero, mul_zero]
  · rw [hA i k hik]
    by_cases hk : i = k
    · subst k
      rw [hB i j hij]
    · rw [Matrix.one_apply_ne hk, zero_mul, zero_mul]

/-- A transitive entry pattern is closed under multiplication and inverse. -/
def patternGroup (Φ : Fin n → Fin n → Prop)
    (htrans : ∀ i j k, Φ i j → Φ j k → Φ i k) : Subgroup (Gn g n) where
  carrier := {u | InPattern Φ u.val}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun hA hB => InPattern.mul htrans hA hB
  inv_mem' := by
    intro u hu
    have hp (m : ℕ) : InPattern Φ ((u ^ m : Gn g n).val) := by
      induction m with
      | zero => rw [pow_zero]; exact fun _ _ _ => rfl
      | succ m ih => rw [pow_succ]; exact InPattern.mul htrans ih hu
    have h : u ^ (orderOf u - 1) * u = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos u), pow_orderOf_eq_one]
    rw [inv_eq_of_mul_eq_one_left h]
    exact hp _

/-- A transitive, irreflexive pattern matrix is invertible by triangularity. -/
theorem isUnit_of_inPattern {Φ : Fin n → Fin n → Prop}
    (hirr : ∀ i, ¬ Φ i i) (htrans : ∀ i j k, Φ i j → Φ j k → Φ i k)
    {M : Mt g n} (hM : InPattern Φ M) : IsUnit M := by
  let r (i : Fin n) := (Finset.univ.filter fun k => Φ k i).card
  have hr (i j : Fin n) (h : Φ i j) : r i < r j := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i, by simp [h], by simp [hirr i]⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact htrans k i j hk h
  have hbt : Matrix.BlockTriangular M r := by
    intro i j hj
    have hij : i ≠ j := fun h => (lt_irrefl _) (h ▸ hj)
    rw [hM i j (fun h => (not_lt_of_ge hj.le) (hr i j h)), Matrix.one_apply_ne hij]
  have hb (k : ℕ) : Matrix.toSquareBlock M r k = 1 := by
    ext i j
    rw [Matrix.toSquareBlock_def, Matrix.of_apply]
    have h : ¬ Φ i.val j.val := fun h => (hr _ _ h).ne (i.property.trans j.property.symm)
    rw [hM _ _ h]
    by_cases hij : i = j
    · subst j
      simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (fun h => hij (Subtype.ext h))]
  rw [Matrix.isUnit_iff_isUnit_det, hbt.det]
  simp [hb]

/-- The size of a pattern group is the field size raised to the number of allowed entries. -/
theorem card_patternGroup (Φ : Fin n → Fin n → Prop)
    (hirr : ∀ i, ¬ Φ i i) (htrans : ∀ i j k, Φ i j → Φ j k → Φ i k) :
    Nat.card (patternGroup (g := g) Φ htrans) =
      g ^ (Finset.univ.filter fun p : Fin n × Fin n => Φ p.1 p.2).card := by
  let S := {p : Fin n × Fin n // Φ p.1 p.2}
  let M (f : S → ZMod g) : Mt g n := fun i j =>
    if h : Φ i j then f ⟨(i, j), h⟩ else (1 : Mt g n) i j
  have hM (f : S → ZMod g) : InPattern Φ (M f) := fun i j h => dif_neg h
  let groupToMatrix : patternGroup (g := g) Φ htrans ≃ {A : Mt g n // InPattern Φ A} :=
    { toFun := fun u => ⟨u.val.val, u.property⟩
      invFun := fun A => ⟨(isUnit_of_inPattern hirr htrans A.property).unit, A.property⟩
      left_inv := fun _ => Subtype.ext (Units.ext rfl)
      right_inv := fun _ => rfl }
  let entries (A : {A : Mt g n // InPattern Φ A}) (p : S) := A.val p.val.1 p.val.2
  let coordinates : {A : Mt g n // InPattern Φ A} ≃ (S → ZMod g) :=
    { toFun := entries
      invFun := fun f => ⟨M f, hM f⟩
      left_inv := by
        intro A
        apply Subtype.ext
        refine Matrix.ext fun i j => ?_
        change M (entries A) i j = A.val i j
        by_cases h : Φ i j
        · simp [M, h, entries]
        · exact (hM (entries A) i j h).trans (A.property i j h).symm
      right_inv := by
        intro f
        funext p
        exact dif_pos p.property }
  rw [Nat.card_congr (groupToMatrix.trans coordinates), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card]
  exact congrArg (fun k => g ^ k) (Fintype.card_subtype _)

theorem patternEntrySum_mul {Φ E : Fin n → Fin n → Prop}
    (hirr : ∀ i, ¬ Φ i i) (hE : ∀ i, ¬ E i i)
    (hpath : ∀ i j k, Φ i j → Φ j k → ¬ E i k)
    {A B : Mt g n} (hA : InPattern Φ A) (hB : InPattern Φ B) :
    patternEntrySum E (A * B) = patternEntrySum E A + patternEntrySum E B := by
  unfold patternEntrySum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · have hne : i ≠ j := fun e => hE i (e ▸ hij)
    rw [Matrix.mul_apply, Fintype.sum_eq_add i j hne]
    · rw [hA i i (hirr i), hB j j (hirr j), Matrix.one_apply_eq, Matrix.one_apply_eq,
        one_mul, mul_one, add_comm]
    · intro k ⟨hki, hkj⟩
      by_cases hik : Φ i k
      · rw [hB k j (fun h => hpath i k j hik h hij), Matrix.one_apply_ne hkj, mul_zero]
      · rw [hA i k hik, Matrix.one_apply_ne hki.symm, zero_mul]
  · rw [zero_add]

/-- Compose an additive entry sum with a character of the residue field. -/
def patternCharacter (Φ E : Fin n → Fin n → Prop)
    (htrans : ∀ i j k, Φ i j → Φ j k → Φ i k) (hirr : ∀ i, ¬ Φ i i)
    (hE : ∀ i, ¬ E i i) (hpath : ∀ i j k, Φ i j → Φ j k → ¬ E i k)
    (ψ : AddChar (ZMod g) ℂ) : patternGroup (g := g) Φ htrans →* ℂˣ := by
  let H := patternGroup (g := g) Φ htrans
  let sum : H →* Multiplicative (ZMod g) :=
    { toFun := fun u => Multiplicative.ofAdd (patternEntrySum E u.val.val)
      map_one' := by
        change patternEntrySum E (1 : Mt g n) = 0
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with hij
        · exact Matrix.one_apply_ne (fun e => hE i (e ▸ hij))
        · rfl
      map_mul' := fun u v => by
        change patternEntrySum E (u.val.val * v.val.val) =
          patternEntrySum E u.val.val + patternEntrySum E v.val.val
        exact patternEntrySum_mul hirr hE hpath (A := u.val.val) (B := v.val.val)
          u.property v.property }
  exact (ψ.toMonoidHom.comp sum).toHomUnits

/-- The trace of a normalized weighted sum is the same weighted sum of character values. -/
theorem tr_eDat (P : Mt g n → Prop) (φ : Mt g n → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (χ : Gn g n → ℂ) :
    tr (eDat g n P φ ψ) χ = ((Finset.univ.filter fun u : Gn g n => P u.val).card : ℂ)⁻¹ *
      ∑ u ∈ Finset.univ.filter (fun u : Gn g n => P u.val), (ψ (φ u.val))⁻¹ * χ u := by
  unfold tr eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, Finsupp.single_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- If the predicate defines a subgroup, the trace is a normalized subgroup sum. -/
theorem tr_eDat_of_subgroup (P : Mt g n → Prop) (φ : Mt g n → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (H : Subgroup (Gn g n)) (hH : ∀ u, P u.val ↔ u ∈ H)
    (χ : Gn g n → ℂ) :
    tr (eDat g n P φ ψ) χ = (Nat.card H : ℂ)⁻¹ *
      ∑ u : H, (ψ (φ u.val.val))⁻¹ * χ u.val := by
  let S := Finset.univ.filter fun u : Gn g n => P u.val
  let F (u : Gn g n) := (ψ (φ u.val))⁻¹ * χ u
  have hm (u : Gn g n) : u ∈ S ↔ u ∈ H := ((by simp [S]) : u ∈ S ↔ P u.val).trans (hH u)
  have hc : S.card = Nat.card H := by
    rw [← Nat.card_eq_finsetCard, Nat.card_congr (Equiv.subtypeEquivRight hm)]
  calc
    _ = (S.card : ℂ)⁻¹ * ∑ u ∈ S, F u := tr_eDat P φ ψ χ
    _ = _ := by rw [hc, Finset.sum_subtype S hm F]

end GlobalTheory.GLq
