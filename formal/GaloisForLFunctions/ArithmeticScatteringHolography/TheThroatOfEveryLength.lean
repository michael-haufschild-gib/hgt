import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

/-!
# The throat of every length

A throat of length `ℓ` is a path with one cusp: edge indices `c j` at distance `j` from the ray, for `j ≤ ℓ`, and the end of the path has all its edges going up. It is a tree lattice for every choice of `1 ≤ c j ≤ q`:
it has `q + 1` edges at every vertex (`chainOp_one`) and an invariant measure with Green's identity and no boundary but the cusp (`chain_green`).

Its modes are explicit. In `z = X²` the recursion

  `Q₀ = 1`, `Q₁ = z + q(1 - c₀)`, `Q_{j+2} = (z + q) Q_{j+1} - c_{j+1} b_j z Q_j`, `b_j = q + 1 - c_j`

gives monic polynomials of degree `j` (`thPoly_monic`). The denominator `R = (z + q) Q_{m+1} - (q + 1) b_m z Q_m` of a throat of length `ℓ = m + 1` is monic of degree `m + 2`. It vanishes at `z = q²`, the constant function
(`thDen_eval_ground`), and each of its roots is a resonance, with a nonzero outgoing eigenfunction (`chain_resonance`). Its constant term is `q^{m+2}(1 - c₀)` (`thDen_eval_zero`): **the product of the modes depends only on the
index nearest the cusp**.

So the functional equation has no room. After removing the root `q²`, a denominator of even degree `2g` with the functional equation would have constant term `q^g`, while a throat has `q^{2g-1}(c₀ - 1)`
(`denom_constant_eq`). For `g ≥ 2` this is impossible (`chain_no_functional_equation`). **A path quotient has the functional equation only at genus at most one**: at genus two the graph must branch, and the partner law is a
global statement about the lattice.
-/

open Polynomial Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable (q : ℕ) (c : ℕ → ℕ)

/-- `q + 1 - c_j`: the number of edges down at distance `j` from the ray. -/
def bq (j : ℕ) : ℂ := (q : ℂ) + 1 - c j

/-- **The polynomials of a throat**, in the variable `z = X²`. -/
def thPoly : ℕ → ℂ[X]
  | 0 => 1
  | 1 => X + C ((q : ℂ) * (1 - c 0))
  | j + 2 => (X + C (q : ℂ)) * thPoly (j + 1) - C ((c (j + 1) : ℂ) * bq q c j) * X * thPoly j

/-- The denominator of a throat of length `m + 1`. -/
def thDen (m : ℕ) : ℂ[X] :=
  (X + C (q : ℂ)) * thPoly q c (m + 1) - C (((q : ℂ) + 1) * bq q c m) * X * thPoly q c m

/-- The product of the indices. -/
def bProd (j : ℕ) : ℂ := ∏ i ∈ Finset.range j, bq q c i

theorem thPoly_monic_natDegree (j : ℕ) :
    (thPoly q c j).Monic ∧ (thPoly q c j).natDegree = j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [thPoly]
  | one =>
    refine ⟨monic_X_add_C _, natDegree_X_add_C _⟩
  | more j h0 h1 =>
    have hm : ((X + C (q : ℂ)) * thPoly q c (j + 1)).Monic := (monic_X_add_C _).mul h1.1
    have hd : ((X + C (q : ℂ)) * thPoly q c (j + 1)).natDegree = j + 2 := by
      rw [(monic_X_add_C _).natDegree_mul h1.1, natDegree_X_add_C, h1.2]
      ring
    have hlowN : (C ((c (j + 1) : ℂ) * bq q c j) * X * thPoly q c j).natDegree ≤ j + 1 := by
      refine natDegree_mul_le.trans ?_
      rw [h0.2]
      have : (C ((c (j + 1) : ℂ) * bq q c j) * X : ℂ[X]).natDegree ≤ 1 :=
        (natDegree_C_mul_le _ _).trans (by simp)
      omega
    have hlow : (C ((c (j + 1) : ℂ) * bq q c j) * X * thPoly q c j).degree <
        ((X + C (q : ℂ)) * thPoly q c (j + 1)).degree := by
      rw [degree_eq_natDegree hm.ne_zero, hd]
      exact lt_of_le_of_lt (degree_le_of_natDegree_le hlowN) (by exact_mod_cast Nat.lt_succ_self _)
    refine ⟨hm.sub_of_left hlow, ?_⟩
    show ((X + C (q : ℂ)) * thPoly q c (j + 1) - _).natDegree = _
    rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [hd]; omega), hd]

/-- The constant term of `Q_{j+1}`. -/
theorem thPoly_eval_zero (j : ℕ) :
    (thPoly q c (j + 1)).eval 0 = (q : ℂ) ^ (j + 1) * (1 - c 0) := by
  induction j with
  | zero => simp [thPoly]
  | succ j ih =>
    show ((X + C (q : ℂ)) * thPoly q c (j + 1) - _).eval 0 = _
    rw [eval_sub, eval_mul, ih]
    simp
    ring

/-- `Q_j(q²) = q^j ∏ b_i`: the constant function. -/
theorem thPoly_eval_ground (j : ℕ) :
    (thPoly q c j).eval ((q : ℂ) ^ 2) = (q : ℂ) ^ j * bProd q c j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [thPoly, bProd]
  | one =>
    simp only [thPoly, bProd, bq, eval_add, eval_X, eval_C, Finset.prod_range_one]
    ring
  | more j h0 h1 =>
    show ((X + C (q : ℂ)) * thPoly q c (j + 1) - _).eval _ = _
    rw [eval_sub, eval_mul, eval_mul, eval_mul, h1, h0]
    simp only [eval_add, eval_X, eval_C]
    have e1 : bProd q c (j + 2) = bProd q c (j + 1) * bq q c (j + 1) := Finset.prod_range_succ _ _
    have e2 : bProd q c (j + 1) = bProd q c j * bq q c j := Finset.prod_range_succ _ _
    rw [e1, e2]
    unfold bq
    ring

/-- **The denominator is monic of degree `m + 2`.** -/
theorem thDen_monic_natDegree (m : ℕ) :
    (thDen q c m).Monic ∧ (thDen q c m).natDegree = m + 2 := by
  have h1 := thPoly_monic_natDegree q c (m + 1)
  have h0 := thPoly_monic_natDegree q c m
  have hm : ((X + C (q : ℂ)) * thPoly q c (m + 1)).Monic := (monic_X_add_C _).mul h1.1
  have hd : ((X + C (q : ℂ)) * thPoly q c (m + 1)).natDegree = m + 2 := by
    rw [(monic_X_add_C _).natDegree_mul h1.1, natDegree_X_add_C, h1.2]
    ring
  have hlowN : (C (((q : ℂ) + 1) * bq q c m) * X * thPoly q c m).natDegree ≤ m + 1 := by
    refine natDegree_mul_le.trans ?_
    rw [h0.2]
    have : (C (((q : ℂ) + 1) * bq q c m) * X : ℂ[X]).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans (by simp)
    omega
  have hlow : (C (((q : ℂ) + 1) * bq q c m) * X * thPoly q c m).degree <
      ((X + C (q : ℂ)) * thPoly q c (m + 1)).degree := by
    rw [degree_eq_natDegree hm.ne_zero, hd]
    exact lt_of_le_of_lt (degree_le_of_natDegree_le hlowN) (by exact_mod_cast Nat.lt_succ_self _)
  refine ⟨hm.sub_of_left hlow, ?_⟩
  unfold thDen
  rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [hd]; omega), hd]

/-- The constant term of the denominator depends only on the index next to the cusp. -/
theorem thDen_eval_zero (m : ℕ) : (thDen q c m).eval 0 = (q : ℂ) ^ (m + 2) * (1 - c 0) := by
  unfold thDen
  rw [eval_sub, eval_mul, thPoly_eval_zero]
  simp
  ring

/-- **The constant function is a root.** -/
theorem thDen_eval_ground (m : ℕ) : (thDen q c m).eval ((q : ℂ) ^ 2) = 0 := by
  unfold thDen
  rw [eval_sub, eval_mul, eval_mul, eval_mul, thPoly_eval_ground, thPoly_eval_ground]
  simp only [eval_add, eval_X, eval_C]
  have e1 : bProd q c (m + 1) = bProd q c m * bq q c m := Finset.prod_range_succ _ _
  rw [e1]
  ring

/-! ### The wave system -/

/-- The up-index of a throat of length `ℓ`: `c` on the throat, `1` on the ray. -/
def upIndex (ℓ : ℕ) (k : ℕ) : ℕ := if k ≤ ℓ then c (ℓ - k) else 1

/-- **The wave operator of a throat of length `ℓ`.** -/
def chainOp (ℓ : ℕ) (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => ((q : ℂ) + 1) * f 1
  | k + 1 => (upIndex c ℓ (k + 1) : ℂ) * f (k + 2) + ((q : ℂ) + 1 - upIndex c ℓ (k + 1)) * f k

/-- Every vertex has `q + 1` edges. -/
theorem chainOp_one (ℓ k : ℕ) : chainOp q c ℓ (fun _ => 1) k = (q : ℂ) + 1 := by
  cases k with
  | zero => simp [chainOp]
  | succ k =>
    simp only [chainOp]
    ring

/-- The up-index at a vertex, with all `q + 1` edges going up at the end of the throat. -/
def upAt (ℓ : ℕ) : ℕ → ℂ
  | 0 => (q : ℂ) + 1
  | k + 1 => (upIndex c ℓ (k + 1) : ℂ)

/-- The invariant measure of a throat. -/
def chainMass (ℓ : ℕ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => chainMass ℓ k * upAt q c ℓ k / ((q : ℂ) + 1 - upIndex c ℓ (k + 1))

variable {q c}

theorem down_ne_zero {ℓ : ℕ} (hc : ∀ j, c j ≤ q) (hq : 1 ≤ q) (k : ℕ) :
    (q : ℂ) + 1 - upIndex c ℓ k ≠ 0 := by
  have hle : upIndex c ℓ k ≤ q := by
    unfold upIndex
    split_ifs
    · exact hc _
    · exact hq
  have h : ((q + 1 - upIndex c ℓ k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rwa [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at h

/-- **Green's identity of a throat.** The only boundary is the cusp, for every choice of indices: flux and unitarity do not see them. -/
theorem chain_green {ℓ : ℕ} (hc : ∀ j, c j ≤ q) (hq : 1 ≤ q) (f g : ℕ → ℂ) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), chainMass q c ℓ k *
        (chainOp q c ℓ f k * g k - f k * chainOp q c ℓ g k) =
      chainMass q c ℓ K * upAt q c ℓ K * (f (K + 1) * g K - f K * g (K + 1)) := by
  induction K with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, chainOp, chainMass, upAt]
    ring
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have hd := down_ne_zero (ℓ := ℓ) hc hq (K + 1)
    have hm : chainMass q c ℓ (K + 1) * ((q : ℂ) + 1 - upIndex c ℓ (K + 1)) =
        chainMass q c ℓ K * upAt q c ℓ K := by
      show chainMass q c ℓ K * upAt q c ℓ K / _ * _ = _
      field_simp
    have e : upAt q c ℓ (K + 1) = (upIndex c ℓ (K + 1) : ℂ) := rfl
    simp only [chainOp, e]
    linear_combination (f K * g (K + 1) - f (K + 1) * g K) * hm

/-! ### The modes -/

/-- The normalized value of the outgoing field at distance `j` from the ray. -/
def thVal (q : ℕ) (c : ℕ → ℕ) (X : ℂ) (j : ℕ) : ℂ :=
  (thPoly q c j).eval (X ^ 2) / (X ^ j * bProd q c j)

/-- **The outgoing field of a throat.** -/
def chainField (q : ℕ) (c : ℕ → ℕ) (ℓ : ℕ) (X Y : ℂ) (k : ℕ) : ℂ :=
  if k ≤ ℓ then Y ^ ℓ * thVal q c X (ℓ - k) else Y ^ k

theorem bq_ne_zero (hc : ∀ j, c j ≤ q) (j : ℕ) : bq q c j ≠ 0 := by
  have h : ((q + 1 - c j : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hc j; omega)
  rw [Nat.cast_sub (by have := hc j; omega), Nat.cast_add, Nat.cast_one] at h
  exact h

theorem bProd_ne_zero (hc : ∀ j, c j ≤ q) (j : ℕ) : bProd q c j ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => bq_ne_zero hc i

theorem thVal_zero (X : ℂ) : thVal q c X 0 = 1 := by
  simp [thVal, thPoly, bProd]

/-- The first step down the throat. -/
theorem thVal_one (hc : ∀ j, c j ≤ q) {X Y : ℂ} (hX : X ≠ 0) (hXY : X * Y = q) :
    bq q c 0 * thVal q c X 1 = X + (1 - (c 0 : ℂ)) * Y := by
  have hb := bq_ne_zero hc 0
  have hY : Y = (q : ℂ) / X := by
    field_simp
    linear_combination hXY
  subst hY
  simp only [thVal, thPoly, bProd, Finset.prod_range_one, eval_add, eval_X, eval_C, pow_one]
  field_simp

/-- The recursion down the throat. -/
theorem thVal_step (hc : ∀ j, c j ≤ q) {X Y : ℂ} (hX : X ≠ 0) (hXY : X * Y = q) (j : ℕ) :
    bq q c (j + 1) * thVal q c X (j + 2) =
      (X + Y) * thVal q c X (j + 1) - (c (j + 1) : ℂ) * thVal q c X j := by
  have hb := bProd_ne_zero hc j
  have hb1 := bq_ne_zero hc j
  have hb2 := bq_ne_zero hc (j + 1)
  have hY : Y = (q : ℂ) / X := by
    field_simp
    linear_combination hXY
  subst hY
  have e1 : bProd q c (j + 2) = bProd q c (j + 1) * bq q c (j + 1) := Finset.prod_range_succ _ _
  have e2 : bProd q c (j + 1) = bProd q c j * bq q c j := Finset.prod_range_succ _ _
  have e3 : (thPoly q c (j + 2)).eval (X ^ 2) = (X ^ 2 + (q : ℂ)) * (thPoly q c (j + 1)).eval (X ^ 2) -
      (c (j + 1) : ℂ) * bq q c j * X ^ 2 * (thPoly q c j).eval (X ^ 2) := by
    show ((Polynomial.X + C (q : ℂ)) * thPoly q c (j + 1) -
      C ((c (j + 1) : ℂ) * bq q c j) * Polynomial.X * thPoly q c j).eval _ = _
    simp [eval_sub, eval_mul]
  unfold thVal
  rw [e3, e1, e2]
  field_simp
  ring

/-- The condition at the end of the throat is the denominator. -/
theorem thVal_end (hc : ∀ j, c j ≤ q) {X Y : ℂ} (hX : X ≠ 0) (hXY : X * Y = q) (m : ℕ) :
    (X + Y) * thVal q c X (m + 1) - ((q : ℂ) + 1) * thVal q c X m =
      (thDen q c m).eval (X ^ 2) / (X ^ (m + 2) * bProd q c (m + 1)) := by
  have hb := bProd_ne_zero hc m
  have hb1 := bq_ne_zero hc m
  have hY : Y = (q : ℂ) / X := by
    field_simp
    linear_combination hXY
  subst hY
  have e2 : bProd q c (m + 1) = bProd q c m * bq q c m := Finset.prod_range_succ _ _
  unfold thVal thDen
  rw [e2]
  simp only [eval_sub, eval_mul, eval_add, eval_X, eval_C]
  field_simp
  ring

/-- **Each root of the denominator is a resonance of the throat.** -/
theorem chain_resonance (hc : ∀ j, c j ≤ q) (hq : 1 ≤ q) {X Y : ℂ} (hX : X ≠ 0) (hXY : X * Y = q) (m : ℕ)
    (hroot : (thDen q c m).eval (X ^ 2) = 0) :
    chainField q c (m + 1) X Y ≠ 0 ∧ (∀ k, m + 1 ≤ k → chainField q c (m + 1) X Y k = Y ^ k) ∧
      ∀ k, chainOp q c (m + 1) (chainField q c (m + 1) X Y) k = (X + Y) * chainField q c (m + 1) X Y k := by
  have hQ : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hY0 : Y ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hXY
    exact hQ hXY.symm
  have hfar (k : ℕ) (hk : m + 1 < k) : chainField q c (m + 1) X Y k = Y ^ k := by
    unfold chainField
    rw [if_neg (by omega)]
  have hnear (k : ℕ) (hk : k ≤ m + 1) :
      chainField q c (m + 1) X Y k = Y ^ (m + 1) * thVal q c X (m + 1 - k) := by
    unfold chainField
    rw [if_pos hk]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h (m + 2)
    rw [hfar _ (by omega)] at h0
    exact pow_ne_zero _ hY0 h0
  · intro k hk
    rcases Nat.lt_or_ge (m + 1) k with h | h
    · exact hfar k h
    · obtain rfl : k = m + 1 := le_antisymm h hk
      rw [hnear _ le_rfl, Nat.sub_self, thVal_zero, mul_one]
  · intro k
    rcases k with _ | k
    · -- the end of the throat
      have h0 := thVal_end hc hX hXY m
      rw [hroot, zero_div] at h0
      show ((q : ℂ) + 1) * _ = _
      rw [hnear 1 (by omega), hnear 0 (by omega), Nat.sub_zero,
        show m + 1 - 1 = m by omega]
      linear_combination (-(Y ^ (m + 1))) * h0
    · by_cases hk : k + 1 ≤ m + 1
      · -- inside the throat
        have hup : upIndex c (m + 1) (k + 1) = c (m + 1 - (k + 1)) := if_pos hk
        rw [hnear (k + 1) hk, show chainOp q c (m + 1) (chainField q c (m + 1) X Y) (k + 1) =
          (upIndex c (m + 1) (k + 1) : ℂ) * chainField q c (m + 1) X Y (k + 2) +
            ((q : ℂ) + 1 - upIndex c (m + 1) (k + 1)) * chainField q c (m + 1) X Y k from rfl, hup,
          hnear k (by omega)]
        rcases Nat.eq_or_lt_of_le hk with h | h
        · -- the vertex next to the ray
          have hkm : k = m := by omega
          subst hkm
          rw [hfar _ (by omega), show k + 1 - (k + 1) = 0 by omega, thVal_zero, show k + 1 - k = 1 by omega]
          have h1 := thVal_one (q := q) (c := c) hc hX hXY
          have e : (q : ℂ) + 1 - (c 0 : ℂ) = bq q c 0 := rfl
          rw [e]
          linear_combination (Y ^ (k + 1)) * h1
        · -- inside
          obtain ⟨j, hj⟩ : ∃ j, m + 1 - (k + 1) = j + 1 := ⟨m + 1 - (k + 1) - 1, by omega⟩
          rw [hj, hnear (k + 2) (by omega), show m + 1 - (k + 2) = j by omega,
            show m + 1 - k = j + 2 by omega]
          have h1 := thVal_step hc hX hXY j
          have e : (q : ℂ) + 1 - (c (j + 1) : ℂ) = bq q c (j + 1) := rfl
          rw [e]
          linear_combination (Y ^ (m + 1)) * h1
      · -- on the ray
        have hup : upIndex c (m + 1) (k + 1) = 1 := if_neg hk
        rw [show chainOp q c (m + 1) (chainField q c (m + 1) X Y) (k + 1) =
          (upIndex c (m + 1) (k + 1) : ℂ) * chainField q c (m + 1) X Y (k + 2) +
            ((q : ℂ) + 1 - upIndex c (m + 1) (k + 1)) * chainField q c (m + 1) X Y k from rfl, hup,
          hfar (k + 2) (by omega), hfar (k + 1) (by omega)]
        have hk' : chainField q c (m + 1) X Y k = Y ^ k := by
          rcases Nat.lt_or_ge (m + 1) k with h | h
          · exact hfar k h
          · obtain rfl : k = m + 1 := by omega
            rw [hnear _ le_rfl, Nat.sub_self, thVal_zero, mul_one]
        rw [hk', ← hXY]
        push_cast
        ring

/-! ### The functional equation -/

/-- The denominator with the constant function removed. -/
theorem exists_denom (m : ℕ) :
    ∃ D : ℂ[X], thDen q c m = (X - C ((q : ℂ) ^ 2)) * D ∧ D.Monic ∧ D.natDegree = m + 1 := by
  obtain ⟨hmon, hdeg⟩ := thDen_monic_natDegree q c m
  obtain ⟨D, hD⟩ := dvd_iff_isRoot.mpr (thDen_eval_ground q c m)
  have hne : D ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hD
    exact hmon.ne_zero hD
  have hDm : D.Monic := by
    have := hmon
    rw [hD] at this
    exact (monic_X_sub_C _).of_mul_monic_left this
  refine ⟨D, hD, hDm, ?_⟩
  have h := congrArg natDegree hD
  rw [(monic_X_sub_C _).natDegree_mul hDm, natDegree_X_sub_C, hdeg] at h
  omega

/-- **The partner law of a throat.** The constant term of the denominator is `q^m (c₀ - 1)`: it depends only on the index next to the cusp. -/
theorem denom_constant_eq (hq : 1 ≤ q) (m : ℕ) {D : ℂ[X]} (hD : thDen q c m = (X - C ((q : ℂ) ^ 2)) * D) :
    D.eval 0 = (q : ℂ) ^ m * ((c 0 : ℂ) - 1) := by
  have hQ : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h := congrArg (eval 0) hD
  rw [thDen_eval_zero, eval_mul] at h
  simp only [eval_sub, eval_X, eval_C, zero_sub] at h
  have h2 : ((q : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 hQ
  apply mul_left_cancel₀ h2
  linear_combination h

/-- A functional equation forces the top coefficient. -/
theorem top_of_functional_equation {P : ℂ[X]} {g : ℕ} {Q : ℂ} (hQ : Q ≠ 0) (hP0 : P.coeff 0 = 1)
    (hdeg : P.natDegree ≤ 2 * g)
    (hFE : ∀ w : ℂ, w ≠ 0 → P.eval w = (Q * w ^ 2) ^ g * P.eval (1 / (Q * w))) :
    P.coeff (2 * g) = Q ^ g := by
  -- the reflected polynomial
  set S : ℂ[X] := ∑ k ∈ Finset.range (2 * g + 1), C (P.coeff k * Q ^ g / Q ^ k) * X ^ (2 * g - k) with hS
  have hval (w : ℂ) (hw : w ≠ 0) : P.eval w = S.eval w := by
    rw [hFE w hw, hS, eval_finsetSum, eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ 2 * g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    have e : w ^ (2 * g) = w ^ (2 * g - k) * w ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk']
    rw [mul_pow, ← pow_mul, e, one_div, inv_pow, mul_pow]
    field_simp
  have hPS : P = S := by
    refine eq_of_infinite_eval_eq _ _ (Set.Infinite.mono (s := {w : ℂ | w ≠ 0}) (fun w hw => hval w hw) ?_)
    exact (Set.finite_singleton (0 : ℂ)).infinite_compl.mono (fun w hw => hw)
  have hcoef : S.coeff (2 * g) = P.coeff 0 * Q ^ g / Q ^ 0 := by
    rw [hS, finsetSum_coeff, Finset.sum_eq_single 0]
    · rw [Nat.sub_zero, coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro k hk hk0
      have hk' : k ≤ 2 * g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
    · simp
  refine (congrArg (fun p : ℂ[X] => p.coeff (2 * g)) hPS).trans (hcoef.trans ?_)
  rw [hP0]
  simp

/-- **A path quotient has the functional equation only at genus at most one.** For a throat of length `2g`, `g ≥ 2`, whose last index is not trivial, the denominator `P = reverse D` does not satisfy
`P(w) = (q w²)^g P(1/(q w))`. -/
theorem chain_no_functional_equation (hq : 2 ≤ q) {g : ℕ} (hg : 2 ≤ g) (hc0 : c 0 ≠ 1) (hc00 : c 0 ≠ 0)
    {D : ℂ[X]} (hD : thDen q c (2 * g - 1) = (X - C ((q : ℂ) ^ 2)) * D) (hmon : D.Monic)
    (hdeg : D.natDegree = 2 * g) :
    ¬ ∀ w : ℂ, w ≠ 0 → D.reverse.eval w = ((q : ℂ) * w ^ 2) ^ g * D.reverse.eval (1 / ((q : ℂ) * w)) := by
  intro hFE
  have hQ : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hP0 : D.reverse.coeff 0 = 1 := by
    rw [coeff_zero_reverse]
    exact hmon.leadingCoeff
  have hPdeg : D.reverse.natDegree ≤ 2 * g := by
    rw [← hdeg]
    exact reverse_natDegree_le D
  have htop := top_of_functional_equation hQ hP0 hPdeg hFE
  have hcoef : D.reverse.coeff (2 * g) = D.eval 0 := by
    rw [reverse, coeff_reflect, hdeg, revAt_le le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero]
  rw [hcoef, denom_constant_eq (by omega) _ hD] at htop
  -- `q^{2g-1}(c₀ - 1) = q^g`
  have hc1 : (c 0 : ℂ) - 1 = (((c 0 - 1 : ℕ) : ℕ) : ℂ) := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hc1] at htop
  have hnat : q ^ (2 * g - 1) * (c 0 - 1) = q ^ g := by exact_mod_cast htop
  have hle : g + 1 ≤ 2 * g - 1 := by omega
  have hpos : 1 ≤ c 0 - 1 := by omega
  have h1 : q ^ (g + 1) ≤ q ^ (2 * g - 1) := Nat.pow_le_pow_right (by omega) hle
  have h2 : q ^ g < q ^ (g + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have h3 : q ^ (2 * g - 1) ≤ q ^ (2 * g - 1) * (c 0 - 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

end GaloisForLFunctions.ArithmeticScatteringHolography

end
