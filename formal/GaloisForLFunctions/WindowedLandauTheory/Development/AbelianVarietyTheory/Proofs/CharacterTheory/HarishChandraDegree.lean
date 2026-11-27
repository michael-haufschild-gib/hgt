import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicBlockMatrices
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! The degree of a Harish–Chandra product is multiplicative after division
by the prime-to-characteristic part of the general linear group order. -/

noncomputable section
open GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

/-- The prime-to-characteristic factor in the order of the general linear group. -/
def primeToCharOrder (g d : ℕ) : ℂ :=
  ∏ i ∈ Finset.range d, ((g : ℂ) ^ (i + 1) - 1)

private def orderPower (g d : ℕ) : ℂ :=
  ∏ i ∈ Finset.range d, (g : ℂ) ^ i

private theorem card_rect (a b : ℕ) :
    Fintype.card (Matrix (Fin a) (Fin b) (ZMod g)) = g ^ (a * b) := by
  change Fintype.card (Fin a → Fin b → ZMod g) = _
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ZMod.card,
    ← pow_mul, Nat.mul_comm b a]

private theorem card_twoBlockParabolic (a b : ℕ) :
    Fintype.card (twoBlockParabolic g a b) =
      Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  let e : twoBlockParabolic g a b ≃ (Gn g a × Gn g b) × Matrix (Fin a) (Fin b) (ZMod g) :=
    { toFun := fun x => (twoBlockLevi x, upperRightBlock x.val.val)
      invFun := fun z => ⟨upperBlockUnit z.1.1 z.2 z.1.2,
        inPar_upperBlockMatrix z.1.1.val z.2 z.1.2.val⟩
      left_inv := fun x => Subtype.ext (upperBlockUnit_eq_of_mem_parabolic x)
      right_inv := fun z => Prod.ext (twoBlockLevi_upperBlockUnit z.1.1 z.2 z.1.2)
        (upperRightBlock_upperBlockMatrix z.1.1.val z.2 z.1.2.val) }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod, card_rect]

private theorem card_Gn_factorization (d : ℕ) :
    (Fintype.card (Gn g d) : ℂ) = orderPower g d * primeToCharOrder g d := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, ZMod.card, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range (fun i => ((g ^ d - g ^ i : ℕ) : ℂ)) d]
  have hfactor (i : ℕ) (hi : i ∈ Finset.range d) :
      ((g ^ d - g ^ i : ℕ) : ℂ) = (g : ℂ) ^ i * ((g : ℂ) ^ (d - 1 - i + 1) - 1) := by
    have hid := Finset.mem_range.mp hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right (Fact.out : g.Prime).pos hid.le),
      Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one, ← pow_add,
      show i + (d - 1 - i + 1) = d by omega]
  rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, orderPower, primeToCharOrder,
    Finset.prod_range_reflect (fun i => (g : ℂ) ^ (i + 1) - 1) d]

omit [Fact g.Prime] in
private theorem orderPower_add (a b : ℕ) :
    orderPower g (a + b) = orderPower g a * orderPower g b * (g : ℂ) ^ (a * b) := by
  unfold orderPower
  rw [Finset.prod_range_add]
  simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  ring

private theorem orderPower_ne_zero (n : ℕ) : orderPower g n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero i
    (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero)

theorem primeToCharOrder_ne_zero (n : ℕ) : primeToCharOrder g n ≠ 0 := by
  have h : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [card_Gn_factorization] at h
  exact (mul_ne_zero_iff.mp h).2

/-- Dividing the general linear group order by the number of upper
unitriangular matrices leaves its prime-to-characteristic factor. -/
theorem card_Gn_eq (n : ℕ) :
    (Fintype.card (Gn g n) : ℂ) = (g : ℂ) ^ (n * (n - 1) / 2) * primeToCharOrder g n := by
  rw [card_Gn_factorization, orderPower, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

private theorem hc_one_card (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b α β (a + b) 1 * (Fintype.card (twoBlockParabolic g a b) : ℂ) =
      (Fintype.card (Gn g (a + b)) : ℂ) * (α 1 * β 1) := by
  let P := twoBlockParabolic g a b
  have hLevi : twoBlockLevi (⟨1, (twoBlockParabolic g a b).one_mem⟩ :
      twoBlockParabolic g a b) = (1, 1) := map_one twoBlockLevi
  rw [hc_eq_inducedFunction, inducedFunction, Nat.card_eq_fintype_card]
  simp only [mul_one, mul_inv_cancel,
    extendByZero_of_mem _ _ (twoBlockParabolic g a b).one_mem,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hP : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_right_comm, inv_mul_cancel₀ hP, one_mul, hLevi]

/-- Harish–Chandra induction multiplies character degrees normalized by the
prime-to-characteristic factor of the group order. -/
theorem hc_one_normalized (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b α β (a + b) 1 / primeToCharOrder g (a + b) =
      (α 1 / primeToCharOrder g a) * (β 1 / primeToCharOrder g b) := by
  have h := hc_one_card a b α β
  rw [card_twoBlockParabolic, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
    card_Gn_factorization a, card_Gn_factorization b, card_Gn_factorization (a + b),
    orderPower_add] at h
  have hg : (g : ℂ) ^ (a * b) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero)
  have hpow := mul_ne_zero (mul_ne_zero (orderPower_ne_zero (g := g) a)
    (orderPower_ne_zero (g := g) b)) hg
  have hmul :
      hc a b α β (a + b) 1 * (primeToCharOrder g a * primeToCharOrder g b) =
        primeToCharOrder g (a + b) * (α 1 * β 1) := by
    apply mul_left_cancel₀ hpow
    linear_combination h
  rw [← mul_div_mul_comm, div_eq_div_iff (primeToCharOrder_ne_zero (g := g) (a + b))
    (mul_ne_zero (primeToCharOrder_ne_zero (g := g) a) (primeToCharOrder_ne_zero (g := g) b)),
    mul_comm (α 1 * β 1)]
  exact hmul

/-- The normalized degree of the induction from a list of blocks is the
product of the normalized degrees of their characters. -/
theorem hcL_one_normalized (L : List (Pc g)) :
    hcL L (degL L) 1 / primeToCharOrder g (degL L) =
      (L.map fun p => p.2 1 / primeToCharOrder g p.1).prod := by
  induction L with
  | nil => simp [hcL_nil, degL, primeToCharOrder]
  | cons p L ih =>
    change hc p.1 (degL L) p.2 (hcL L (degL L)) (p.1 + degL L) 1 /
      primeToCharOrder g (p.1 + degL L) = _
    rw [hc_one_normalized, ih]
    rfl

end GlobalTheory.GLq
