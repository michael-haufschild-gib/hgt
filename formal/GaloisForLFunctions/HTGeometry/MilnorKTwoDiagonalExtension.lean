import GaloisForLFunctions.HTGeometry.MilnorKDegTwoSymbol
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F] {n : ℕ}

def detOneDiagonalUnits (F : Type*) [Field F] (n : ℕ) : Subgroup (Fin n → Fˣ) where
  carrier := {u | ∏ i, u i = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change (∏ i, u i * v i) = 1
    rw [Finset.prod_mul_distrib, hu, hv, one_mul]
  inv_mem' := by
    intro u hu
    change (∏ i, (u i)⁻¹) = 1
    rw [Finset.prod_inv_distrib, hu, inv_one]

def milnorDiagonalCocycle (u v : detOneDiagonalUnits F n) : MilnorKDeg F 2 :=
  ∑ i : Fin n, ∑ j : Fin n, if j ≤ i then milnorSym2 F (u.1 i) (v.1 j) else 0

@[simp]
theorem milnorDiagonalCocycle_one_left (v : detOneDiagonalUnits F n) :
    milnorDiagonalCocycle (1 : detOneDiagonalUnits F n) v = 0 := by
  simp [milnorDiagonalCocycle, milnorSym2_one_left]

@[simp]
theorem milnorDiagonalCocycle_one_right (u : detOneDiagonalUnits F n) :
    milnorDiagonalCocycle u (1 : detOneDiagonalUnits F n) = 0 := by
  simp [milnorDiagonalCocycle, milnorSym2_one_right]

theorem milnorDiagonalCocycle_cocycle
    (u v w : detOneDiagonalUnits F n) :
    milnorDiagonalCocycle (u * v) w + milnorDiagonalCocycle u v
      = milnorDiagonalCocycle u (v * w) + milnorDiagonalCocycle v w := by
  unfold milnorDiagonalCocycle
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j ≤ i
  · simp [hji, milnorSym2_mul_left, milnorSym2_mul_right]
    abel
  · simp [hji]

@[simp]
theorem milnorDiagonalCocycle_mul_left
    (u v w : detOneDiagonalUnits F n) :
    milnorDiagonalCocycle (u * v) w
      = milnorDiagonalCocycle u w + milnorDiagonalCocycle v w := by
  unfold milnorDiagonalCocycle
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j ≤ i <;> simp [hji, milnorSym2_mul_left]

@[simp]
theorem milnorDiagonalCocycle_mul_right
    (u v w : detOneDiagonalUnits F n) :
    milnorDiagonalCocycle u (v * w)
      = milnorDiagonalCocycle u v + milnorDiagonalCocycle u w := by
  unfold milnorDiagonalCocycle
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j ≤ i <;> simp [hji, milnorSym2_mul_right]

theorem milnorDiagonalCocycle_inv_swap (u : detOneDiagonalUnits F n) :
    milnorDiagonalCocycle u u⁻¹ = milnorDiagonalCocycle u⁻¹ u := by
  have h := milnorDiagonalCocycle_cocycle (F := F) u u⁻¹ u
  simpa using h

@[simp]
theorem milnorDiagonalCocycle_inv_left (u v : detOneDiagonalUnits F n) :
    milnorDiagonalCocycle u⁻¹ v = -milnorDiagonalCocycle u v := by
  unfold milnorDiagonalCocycle
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j ≤ i <;> simp [hji, milnorSym2_inv_left]

@[simp]
theorem milnorDiagonalCocycle_inv_right (u v : detOneDiagonalUnits F n) :
    milnorDiagonalCocycle u v⁻¹ = -milnorDiagonalCocycle u v := by
  unfold milnorDiagonalCocycle
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j ≤ i <;> simp [hji, milnorSym2_inv_right]

theorem milnorSym2_fin_prod_left (u : Fin n → Fˣ) (b : Fˣ) :
    milnorSym2 F (∏ i, u i) b = ∑ i, milnorSym2 F (u i) b := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [milnorSym2_one_left]
  | @insert i s hi ih => simp [Finset.prod_insert hi, Finset.sum_insert hi,
      milnorSym2_mul_left, ih]

theorem milnorSym2_fin_prod_right (a : Fˣ) (v : Fin n → Fˣ) :
    milnorSym2 F a (∏ j, v j) = ∑ j, milnorSym2 F a (v j) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [milnorSym2_one_right]
  | @insert j s hj ih => simp [Finset.prod_insert hj, Finset.sum_insert hj,
      milnorSym2_mul_right, ih]

def milnorDiagonalSymbolSum (u v : detOneDiagonalUnits F n) : MilnorKDeg F 2 :=
  ∑ i : Fin n, milnorSym2 F (u.1 i) (v.1 i)

theorem milnorDiagonalTotalSymbolSum_eq_zero (u v : detOneDiagonalUnits F n) :
    (∑ i : Fin n, ∑ j : Fin n, milnorSym2 F (u.1 i) (v.1 j)) = 0 := by
  calc
    (∑ i : Fin n, ∑ j : Fin n, milnorSym2 F (u.1 i) (v.1 j))
        = ∑ i : Fin n, milnorSym2 F (u.1 i) (∏ j, v.1 j) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (milnorSym2_fin_prod_right (F := F) (u.1 i) v.1).symm
    _ = milnorSym2 F (∏ i, u.1 i) (∏ j, v.1 j) :=
      (milnorSym2_fin_prod_left (F := F) u.1 (∏ j, v.1 j)).symm
    _ = 0 := by rw [u.property, v.property, milnorSym2_one_left]

theorem milnorDiagonalCocycle_sub_swap (u v : detOneDiagonalUnits F n) :
    milnorDiagonalCocycle u v - milnorDiagonalCocycle v u
      = milnorDiagonalSymbolSum u v := by
  have hswap : milnorDiagonalCocycle v u
      = -(∑ i : Fin n, ∑ j : Fin n,
          if i ≤ j then milnorSym2 F (u.1 i) (v.1 j) else 0) := by
    calc
      milnorDiagonalCocycle v u
          = ∑ i : Fin n, ∑ j : Fin n,
              if j ≤ i then -milnorSym2 F (u.1 j) (v.1 i) else 0 := by
                unfold milnorDiagonalCocycle
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro j hj
                by_cases hji : j ≤ i
                · simp only [hji, ↓reduceIte]
                  exact milnorSym2_antisymm (v.1 i) (u.1 j)
                · simp [hji]
      _ = -(∑ i : Fin n, ∑ j : Fin n,
              if j ≤ i then milnorSym2 F (u.1 j) (v.1 i) else 0) := by
                rw [← Finset.sum_neg_distrib]
                apply Finset.sum_congr rfl
                intro i hi
                rw [← Finset.sum_neg_distrib]
                apply Finset.sum_congr rfl
                intro j hj
                by_cases hji : j ≤ i <;> simp [hji]
      _ = -(∑ i : Fin n, ∑ j : Fin n,
              if i ≤ j then milnorSym2 F (u.1 i) (v.1 j) else 0) := by
                congr 1
                rw [Finset.sum_comm]
  rw [hswap]
  have hpartition :
      milnorDiagonalCocycle u v
          + (∑ i : Fin n, ∑ j : Fin n,
              if i ≤ j then milnorSym2 F (u.1 i) (v.1 j) else 0)
        = (∑ i : Fin n, ∑ j : Fin n, milnorSym2 F (u.1 i) (v.1 j))
          + milnorDiagonalSymbolSum u v := by
    unfold milnorDiagonalCocycle milnorDiagonalSymbolSum
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    calc
      ∑ j : Fin n,
          ((if j ≤ i then milnorSym2 F (u.1 i) (v.1 j) else 0)
            + if i ≤ j then milnorSym2 F (u.1 i) (v.1 j) else 0)
          = ∑ j : Fin n,
              (milnorSym2 F (u.1 i) (v.1 j)
                + if i = j then milnorSym2 F (u.1 i) (v.1 j) else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              rcases lt_trichotomy i j with hij | rfl | hji
              · simp [hij.le, not_le.mpr hij, hij.ne]
              · simp
              · simp [hji.le, not_le.mpr hji, hji.ne']
      _ = (∑ j : Fin n, milnorSym2 F (u.1 i) (v.1 j))
          + milnorSym2 F (u.1 i) (v.1 i) := by simp [Finset.sum_add_distrib]
  rw [sub_eq_add_neg, neg_neg, hpartition, milnorDiagonalTotalSymbolSum_eq_zero, zero_add]

@[ext]
structure MilnorDiagonalExtension (F : Type*) [Field F] (n : ℕ) where
  diag : detOneDiagonalUnits F n
  central : MilnorKDeg F 2

namespace MilnorDiagonalExtension

open scoped commutatorElement

instance : Mul (MilnorDiagonalExtension F n) where
  mul x y := ⟨x.diag * y.diag,
    x.central + y.central + milnorDiagonalCocycle x.diag y.diag⟩

instance : One (MilnorDiagonalExtension F n) where
  one := ⟨1, 0⟩

instance : Inv (MilnorDiagonalExtension F n) where
  inv x := ⟨x.diag⁻¹,
    -x.central - milnorDiagonalCocycle x.diag⁻¹ x.diag⟩

@[simp] theorem diag_mul (x y : MilnorDiagonalExtension F n) :
    (x * y).diag = x.diag * y.diag := rfl

@[simp] theorem central_mul (x y : MilnorDiagonalExtension F n) :
    (x * y).central = x.central + y.central + milnorDiagonalCocycle x.diag y.diag := rfl

@[simp] theorem diag_one : (1 : MilnorDiagonalExtension F n).diag = 1 := rfl

@[simp] theorem central_one : (1 : MilnorDiagonalExtension F n).central = 0 := rfl

@[simp] theorem diag_inv (x : MilnorDiagonalExtension F n) : x⁻¹.diag = x.diag⁻¹ := rfl

@[simp] theorem central_inv (x : MilnorDiagonalExtension F n) :
    x⁻¹.central = -x.central - milnorDiagonalCocycle x.diag⁻¹ x.diag := rfl

instance : Group (MilnorDiagonalExtension F n) where
  mul_assoc x y z := by
    ext
    · simp [mul_assoc]
    · simp only [central_mul, diag_mul]
      have hc := milnorDiagonalCocycle_cocycle (F := F) x.diag y.diag z.diag
      calc
        x.central + y.central + milnorDiagonalCocycle x.diag y.diag + z.central
              + milnorDiagonalCocycle (x.diag * y.diag) z.diag
            = x.central + y.central + z.central
              + (milnorDiagonalCocycle (x.diag * y.diag) z.diag
                + milnorDiagonalCocycle x.diag y.diag) := by abel
        _ = x.central + y.central + z.central
              + (milnorDiagonalCocycle x.diag (y.diag * z.diag)
                + milnorDiagonalCocycle y.diag z.diag) := by rw [hc]
        _ = x.central + (y.central + z.central + milnorDiagonalCocycle y.diag z.diag)
              + milnorDiagonalCocycle x.diag (y.diag * z.diag) := by abel
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by
    ext
    · simp
    · simp only [central_mul, central_inv, diag_inv]
      abel

def proj : MilnorDiagonalExtension F n →* detOneDiagonalUnits F n where
  toFun := diag
  map_one' := rfl
  map_mul' _ _ := rfl

def centralIncl : Multiplicative (MilnorKDeg F 2) →* MilnorDiagonalExtension F n where
  toFun a := ⟨1, a.toAdd⟩
  map_one' := rfl
  map_mul' a b := by
    ext
    · simp
    · simp

@[simp] theorem proj_apply (x : MilnorDiagonalExtension F n) : proj x = x.diag := rfl

@[simp] theorem centralIncl_diag (a : Multiplicative (MilnorKDeg F 2)) :
    (centralIncl (F := F) (n := n) a).diag = 1 := rfl

@[simp] theorem centralIncl_central (a : Multiplicative (MilnorKDeg F 2)) :
    (centralIncl (F := F) (n := n) a).central = a.toAdd := rfl

theorem centralIncl_mem_center (a : Multiplicative (MilnorKDeg F 2)) :
    centralIncl (F := F) (n := n) a ∈ Subgroup.center (MilnorDiagonalExtension F n) := by
  rw [Subgroup.mem_center_iff]
  intro x
  ext
  · simp
  · simp
    abel

theorem commutatorElement_eq_cocycle_sub_swap (x y : MilnorDiagonalExtension F n) :
    ⁅x, y⁆ = centralIncl (F := F) (n := n)
      (Multiplicative.ofAdd
        (milnorDiagonalCocycle x.diag y.diag - milnorDiagonalCocycle y.diag x.diag)) := by
  rw [commutatorElement_def]
  apply MilnorDiagonalExtension.ext
  · change x.diag * y.diag * x.diag⁻¹ * y.diag⁻¹ = 1
    apply Subtype.ext
    funext i
    simp
  · simp only [central_mul, diag_mul, central_inv, diag_inv, centralIncl_central]
    change x.central + y.central + milnorDiagonalCocycle x.diag y.diag
        + (-x.central - milnorDiagonalCocycle x.diag⁻¹ x.diag)
        + milnorDiagonalCocycle (x.diag * y.diag) x.diag⁻¹
        + (-y.central - milnorDiagonalCocycle y.diag⁻¹ y.diag)
        + milnorDiagonalCocycle (x.diag * y.diag * x.diag⁻¹) y.diag⁻¹
      = milnorDiagonalCocycle x.diag y.diag - milnorDiagonalCocycle y.diag x.diag
    simp only [milnorDiagonalCocycle_mul_left,
      milnorDiagonalCocycle_inv_left, milnorDiagonalCocycle_inv_right]
    abel

/-- **Milnor Lemma 12.1 in additive notation.** The commutator of two lifts of determinant-one
diagonal tuples is the diagonal sum of their Milnor symbols. -/
theorem commutatorElement_eq_diagonalSymbolSum (x y : MilnorDiagonalExtension F n) :
    ⁅x, y⁆ = centralIncl (F := F) (n := n)
      (Multiplicative.ofAdd (milnorDiagonalSymbolSum x.diag y.diag)) := by
  rw [commutatorElement_eq_cocycle_sub_swap, milnorDiagonalCocycle_sub_swap]

theorem centralIncl_injective : Function.Injective (centralIncl (F := F) (n := n)) := by
  intro a b h
  have hc := congrArg central h
  exact Multiplicative.ext hc

/-- Determinant-one rank-four diagonal tuple with entries `(u,u⁻¹,1,1)`. -/
def fin4DiagonalZeroOne (u : Fˣ) : detOneDiagonalUnits F 4 :=
  ⟨![u, u⁻¹, 1, 1], by
    change (∏ i : Fin 4, (![u, u⁻¹, 1, 1] : Fin 4 → Fˣ) i) = 1
    rw [Fin.prod_univ_four]
    simp⟩

@[simp] theorem fin4DiagonalZeroOne_zero (u : Fˣ) : (fin4DiagonalZeroOne u).1 0 = u := rfl
@[simp] theorem fin4DiagonalZeroOne_one (u : Fˣ) : (fin4DiagonalZeroOne u).1 1 = u⁻¹ := rfl
@[simp] theorem fin4DiagonalZeroOne_two (u : Fˣ) : (fin4DiagonalZeroOne u).1 2 = 1 := rfl
@[simp] theorem fin4DiagonalZeroOne_three (u : Fˣ) : (fin4DiagonalZeroOne u).1 3 = 1 := rfl

theorem fin4DiagonalZeroOne_mul (u v : Fˣ) :
    fin4DiagonalZeroOne (u * v) = fin4DiagonalZeroOne u * fin4DiagonalZeroOne v := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [fin4DiagonalZeroOne, mul_comm]

/-- The fixed positive-root diagonal lift used by the rank-four Matsumoto map. -/
def fin4MatsumotoDiagonalLiftZeroOne (u : Fˣ) : MilnorDiagonalExtension F 4 :=
  ⟨fin4DiagonalZeroOne u, 0⟩

theorem milnorDiagonalCocycle_fin4DiagonalZeroOne (u v : Fˣ) :
    milnorDiagonalCocycle (fin4DiagonalZeroOne u) (fin4DiagonalZeroOne v)
      = milnorSym2 F u v := by
  simp [milnorDiagonalCocycle, fin4DiagonalZeroOne, Fin.sum_univ_four,
    milnorSym2_one_left, milnorSym2_one_right, milnorSym2_inv_left,
    milnorSym2_inv_right]

/-- **Milnor Lemma 12.2, fixed-edge multiplicativity defect.** -/
theorem fin4MatsumotoDiagonalLiftZeroOne_mul (u v : Fˣ) :
    fin4MatsumotoDiagonalLiftZeroOne u * fin4MatsumotoDiagonalLiftZeroOne v
      = centralIncl (F := F) (n := 4) (Multiplicative.ofAdd (milnorSym2 F u v))
        * fin4MatsumotoDiagonalLiftZeroOne (u * v) := by
  apply MilnorDiagonalExtension.ext
  · simp only [diag_mul, fin4MatsumotoDiagonalLiftZeroOne, fin4DiagonalZeroOne_mul,
      centralIncl_diag, one_mul]
  · simp [fin4MatsumotoDiagonalLiftZeroOne,
      milnorDiagonalCocycle_fin4DiagonalZeroOne]

/-- Rank-four determinant-one diagonal tuple supported on an oriented edge. -/
def fin4MatsumotoDiagonal (i j : Fin 4) (u : Fˣ) : detOneDiagonalUnits F 4 :=
  ⟨Pi.mulSingle (M := fun _ : Fin 4 => Fˣ) i u
      * Pi.mulSingle (M := fun _ : Fin 4 => Fˣ) j u⁻¹, by
    change (∏ k : Fin 4,
      (Pi.mulSingle (M := fun _ : Fin 4 => Fˣ) i u
        * Pi.mulSingle (M := fun _ : Fin 4 => Fˣ) j u⁻¹) k) = 1
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle']
    simp⟩

theorem fin4MatsumotoDiagonal_mul (i j : Fin 4) (u v : Fˣ) :
    fin4MatsumotoDiagonal i j (u * v)
      = fin4MatsumotoDiagonal i j u * fin4MatsumotoDiagonal i j v := by
  apply Subtype.ext
  funext k
  simp [fin4MatsumotoDiagonal, Pi.mulSingle_mul, mul_inv_rev, mul_comm]
  ac_rfl

theorem fin4MatsumotoDiagonal_inv (i j : Fin 4) (u : Fˣ) :
    (fin4MatsumotoDiagonal i j u)⁻¹ = fin4MatsumotoDiagonal i j u⁻¹ := by
  apply Subtype.ext
  funext k
  by_cases hki : k = i
  · subst k
    by_cases hij : i = j
    · subst j
      simp [fin4MatsumotoDiagonal]
    · simp [fin4MatsumotoDiagonal, hij]
  · by_cases hkj : k = j
    · subst k
      simp [fin4MatsumotoDiagonal, hki]
    · simp [fin4MatsumotoDiagonal, hki, hkj]

theorem fin4MatsumotoDiagonal_reverse {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    fin4MatsumotoDiagonal j i u = (fin4MatsumotoDiagonal i j u)⁻¹ := by
  apply Subtype.ext
  funext k
  by_cases hki : k = i
  · subst k
    simp [fin4MatsumotoDiagonal, hij]
  · by_cases hkj : k = j
    · subst k
      simp [fin4MatsumotoDiagonal, hki]
    · simp [fin4MatsumotoDiagonal, hki, hkj]

theorem milnorDiagonalCocycle_fin4MatsumotoDiagonal {i j : Fin 4}
    (hij : i ≠ j) (u v : Fˣ) :
    milnorDiagonalCocycle (fin4MatsumotoDiagonal i j u) (fin4MatsumotoDiagonal i j v)
      = milnorSym2 F u v := by
  fin_cases i <;> fin_cases j <;>
    simp_all [milnorDiagonalCocycle, fin4MatsumotoDiagonal, Fin.sum_univ_four,
      milnorSym2_one_left, milnorSym2_one_right, milnorSym2_inv_left,
      milnorSym2_inv_right]

/-- Milnor's orientation-normalized diagonal lift `hᵢⱼ(u)`. -/
def fin4MatsumotoDiagonalLift {i j : Fin 4} (_hij : i ≠ j) (u : Fˣ) :
    MilnorDiagonalExtension F 4 :=
  ⟨fin4MatsumotoDiagonal i j u, if i < j then 0 else milnorSym2 F u u⟩

/-- **Milnor Lemma 12.2: `hᵢⱼ(u)hᵢⱼ(v)=c(u,v)hᵢⱼ(uv)`.** -/
theorem fin4MatsumotoDiagonalLift_mul {i j : Fin 4} (hij : i ≠ j) (u v : Fˣ) :
    fin4MatsumotoDiagonalLift hij u * fin4MatsumotoDiagonalLift hij v
      = centralIncl (F := F) (n := 4) (Multiplicative.ofAdd (milnorSym2 F u v))
        * fin4MatsumotoDiagonalLift hij (u * v) := by
  apply MilnorDiagonalExtension.ext
  · simp only [diag_mul, fin4MatsumotoDiagonalLift, fin4MatsumotoDiagonal_mul,
      centralIncl_diag, one_mul]
  · by_cases hlt : i < j
    · simp [fin4MatsumotoDiagonalLift, hlt,
        milnorDiagonalCocycle_fin4MatsumotoDiagonal hij]
    · simp only [central_mul, fin4MatsumotoDiagonalLift, hlt, ↓reduceIte,
        milnorDiagonalCocycle_fin4MatsumotoDiagonal hij, centralIncl_central,
        centralIncl_diag, milnorDiagonalCocycle_one_left]
      rw [milnorSym2_mul_left, milnorSym2_mul_right, milnorSym2_mul_right,
        milnorSym2_antisymm v u]
      abel

/-- **Milnor Lemma 12.2: `hⱼᵢ(u)=hᵢⱼ(u)⁻¹`.** -/
theorem fin4MatsumotoDiagonalLift_reverse {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    fin4MatsumotoDiagonalLift (Ne.symm hij) u = (fin4MatsumotoDiagonalLift hij u)⁻¹ := by
  apply MilnorDiagonalExtension.ext
  · exact fin4MatsumotoDiagonal_reverse hij u
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · simp only [fin4MatsumotoDiagonalLift, hlt, ↓reduceIte, not_lt.mpr hlt.le,
        central_inv, neg_zero, zero_sub]
      rw [fin4MatsumotoDiagonal_inv,
        milnorDiagonalCocycle_fin4MatsumotoDiagonal hij, milnorSym2_inv_left]
      simp
    · simp only [fin4MatsumotoDiagonalLift, hgt, ↓reduceIte, not_lt.mpr hgt.le,
        central_inv]
      rw [fin4MatsumotoDiagonal_inv,
        milnorDiagonalCocycle_fin4MatsumotoDiagonal hij, milnorSym2_inv_left]
      abel

theorem fin4MatsumotoDiagonal_triangle (i j k : Fin 4) (u : Fˣ) :
    fin4MatsumotoDiagonal k i u * fin4MatsumotoDiagonal j k u
      = fin4MatsumotoDiagonal j i u := by
  apply Subtype.ext
  change ((Pi.mulSingle k u : Fin 4 → Fˣ) * Pi.mulSingle i u⁻¹)
      * ((Pi.mulSingle j u : Fin 4 → Fˣ) * Pi.mulSingle k u⁻¹)
    = (Pi.mulSingle j u : Fin 4 → Fˣ) * Pi.mulSingle i u⁻¹
  calc
    ((Pi.mulSingle k u : Fin 4 → Fˣ) * Pi.mulSingle i u⁻¹)
          * ((Pi.mulSingle j u : Fin 4 → Fˣ) * Pi.mulSingle k u⁻¹)
        = ((Pi.mulSingle k u : Fin 4 → Fˣ) * Pi.mulSingle k u⁻¹)
          * ((Pi.mulSingle j u : Fin 4 → Fˣ) * Pi.mulSingle i u⁻¹) := by ac_rfl
    _ = (Pi.mulSingle j u : Fin 4 → Fˣ) * Pi.mulSingle i u⁻¹ := by
      rw [← Pi.mulSingle_mul]
      simp

theorem fin4MatsumotoDiagonalLift_triangle_mul {i j k : Fin 4}
    (hki : k ≠ i) (hjk : j ≠ k) (hji : j ≠ i) (u : Fˣ) :
    fin4MatsumotoDiagonalLift hki u * fin4MatsumotoDiagonalLift hjk u
      = fin4MatsumotoDiagonalLift hji u := by
  apply MilnorDiagonalExtension.ext
  · exact fin4MatsumotoDiagonal_triangle i j k u
  · fin_cases i <;> fin_cases j <;> fin_cases k <;>
      (try omega) <;>
      simp_all [fin4MatsumotoDiagonalLift, milnorDiagonalCocycle,
        fin4MatsumotoDiagonal, Fin.sum_univ_four, milnorSym2_one_left,
        milnorSym2_one_right, milnorSym2_inv_left, milnorSym2_inv_right]

/-- **Milnor Lemma 12.2: `hᵢⱼ(u)⁻¹=hᵢₖ(u)⁻¹hₖⱼ(u)⁻¹`.** -/
theorem fin4MatsumotoDiagonalLift_triangle {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (u : Fˣ) :
    (fin4MatsumotoDiagonalLift hij u)⁻¹
      = (fin4MatsumotoDiagonalLift hik u)⁻¹
        * (fin4MatsumotoDiagonalLift hkj u)⁻¹ := by
  rw [← fin4MatsumotoDiagonalLift_reverse hij,
    ← fin4MatsumotoDiagonalLift_reverse hik,
    ← fin4MatsumotoDiagonalLift_reverse hkj]
  exact (fin4MatsumotoDiagonalLift_triangle_mul
    (Ne.symm hik) (Ne.symm hkj) (Ne.symm hij) u).symm

end MilnorDiagonalExtension

end GaloisForLFunctions.HTGeometry
