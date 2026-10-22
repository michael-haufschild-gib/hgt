import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittEuler

/-!
# Integral big-Witt multiplication

This file defines the canonical product coefficientwise from the Euler-factor identity

`(1-aT^m) ⊙ (1-bT^n) = (1-a^(l/m)b^(l/n)T^l)^g`,

where `g = gcd m n` and `l = lcm m n`.  Every coefficient is a finite integral expression;
therefore the construction applies unchanged to rings with nilpotents.
-/

namespace RHTower

noncomputable section

open scoped BigOperators

open PowerSeries

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Pairwise Euler-factor product.  Indices `i,j` encode positive degrees `i+1,j+1`. -/
def deningerBigWittPairFactor (x y : ℕ → A) (i j : ℕ) : PowerSeries A :=
  let m := i + 1
  let n := j + 1
  let l := m.lcm n
  (deningerBigWittFactor (x i ^ (l / m) * y j ^ (l / n)) l) ^ (m.gcd n)

@[simp] theorem deningerBigWittPairFactor_map
    (f : A →+* B) (x y : ℕ → A) (i j : ℕ) :
    PowerSeries.map f (deningerBigWittPairFactor x y i j) =
      deningerBigWittPairFactor (f ∘ x) (f ∘ y) i j := by
  simp [deningerBigWittPairFactor]

@[simp] theorem deningerBigWittPairFactor_constantCoeff
    (x y : ℕ → A) (i j : ℕ) :
    PowerSeries.constantCoeff (deningerBigWittPairFactor x y i j) = 1 := by
  simp only [deningerBigWittPairFactor, map_pow]
  rw [deningerBigWittFactor_constantCoeff]
  · simp
  · exact (Nat.lcm_pos (Nat.succ_pos i) (Nat.succ_pos j)).ne'

/-- Product of pair factors whose two positive indices are at most `N`. -/
def deningerBigWittPairPartial (x y : ℕ → A) (N : ℕ) : PowerSeries A :=
  ∏ i ∈ Finset.range N, ∏ j ∈ Finset.range N, deningerBigWittPairFactor x y i j

@[simp] theorem deningerBigWittPairPartial_zero (x y : ℕ → A) :
    deningerBigWittPairPartial x y 0 = 1 := by
  simp [deningerBigWittPairPartial]

@[simp] theorem deningerBigWittPairPartial_constantCoeff
    (x y : ℕ → A) (N : ℕ) :
    PowerSeries.constantCoeff (deningerBigWittPairPartial x y N) = 1 := by
  simp [deningerBigWittPairPartial]

@[simp] theorem deningerBigWittPairPartial_map
    (f : A →+* B) (x y : ℕ → A) (N : ℕ) :
    PowerSeries.map f (deningerBigWittPairPartial x y N) =
      deningerBigWittPairPartial (f ∘ x) (f ∘ y) N := by
  simp [deningerBigWittPairPartial]

theorem deningerBigWittPairPartial_succ (x y : ℕ → A) (N : ℕ) :
    deningerBigWittPairPartial x y (N + 1) =
      deningerBigWittPairPartial x y N *
        (∏ i ∈ Finset.range N, deningerBigWittPairFactor x y i N) *
        (∏ j ∈ Finset.range (N + 1), deningerBigWittPairFactor x y N j) := by
  simp only [deningerBigWittPairPartial, Finset.prod_range_succ]
  rw [Finset.prod_mul_distrib]

theorem coeff_mul_deningerBigWittFactor_pow_of_lt
    (f : PowerSeries A) (a : A) {k m d : ℕ} (hkm : k < m) :
    PowerSeries.coeff k (f * deningerBigWittFactor a m ^ d) = PowerSeries.coeff k f := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, ← mul_assoc,
        coeff_mul_deningerBigWittFactor_of_lt _ _ hkm, ih]

theorem coeff_mul_deningerBigWittPairFactor_of_lt_lcm
    (f : PowerSeries A) (x y : ℕ → A) (i j k : ℕ)
    (hk : k < (i + 1).lcm (j + 1)) :
    PowerSeries.coeff k (f * deningerBigWittPairFactor x y i j) =
      PowerSeries.coeff k f := by
  exact coeff_mul_deningerBigWittFactor_pow_of_lt _ _ hk

theorem coeff_mul_prod_pairFactor_of_lt_lcm
    (f : PowerSeries A) (x y : ℕ → A) (k : ℕ) (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, k < (p.1 + 1).lcm (p.2 + 1)) :
    PowerSeries.coeff k (f * ∏ p ∈ s, deningerBigWittPairFactor x y p.1 p.2) =
      PowerSeries.coeff k f := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      rw [Finset.prod_insert hp]
      calc
        PowerSeries.coeff k
            (f * (deningerBigWittPairFactor x y p.1 p.2 *
              ∏ q ∈ s, deningerBigWittPairFactor x y q.1 q.2)) =
            PowerSeries.coeff k
              ((f * ∏ q ∈ s, deningerBigWittPairFactor x y q.1 q.2) *
                deningerBigWittPairFactor x y p.1 p.2) := by
              congr 1
              ac_rfl
        _ = PowerSeries.coeff k
              (f * ∏ q ∈ s, deningerBigWittPairFactor x y q.1 q.2) :=
            coeff_mul_deningerBigWittPairFactor_of_lt_lcm _ _ _ _ _ _
              (hs p (by simp))
        _ = PowerSeries.coeff k f := ih (fun q hq => hs q (by simp [hq]))

theorem coeff_mul_prod_pairFactor_fixed_right
    (f : PowerSeries A) (x y : ℕ → A) (j k : ℕ) (s : Finset ℕ)
    (hs : ∀ i ∈ s, k < (i + 1).lcm (j + 1)) :
    PowerSeries.coeff k (f * ∏ i ∈ s, deningerBigWittPairFactor x y i j) =
      PowerSeries.coeff k f := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      calc
        PowerSeries.coeff k
            (f * (deningerBigWittPairFactor x y i j *
              ∏ q ∈ s, deningerBigWittPairFactor x y q j)) =
            PowerSeries.coeff k
              ((f * ∏ q ∈ s, deningerBigWittPairFactor x y q j) *
                deningerBigWittPairFactor x y i j) := by
              congr 1
              ac_rfl
        _ = PowerSeries.coeff k
              (f * ∏ q ∈ s, deningerBigWittPairFactor x y q j) :=
            coeff_mul_deningerBigWittPairFactor_of_lt_lcm _ _ _ _ _ _
              (hs i (by simp))
        _ = PowerSeries.coeff k f := ih (fun q hq => hs q (by simp [hq]))

theorem coeff_mul_prod_pairFactor_fixed_left
    (f : PowerSeries A) (x y : ℕ → A) (i k : ℕ) (s : Finset ℕ)
    (hs : ∀ j ∈ s, k < (i + 1).lcm (j + 1)) :
    PowerSeries.coeff k (f * ∏ j ∈ s, deningerBigWittPairFactor x y i j) =
      PowerSeries.coeff k f := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      rw [Finset.prod_insert hj]
      calc
        PowerSeries.coeff k
            (f * (deningerBigWittPairFactor x y i j *
              ∏ q ∈ s, deningerBigWittPairFactor x y i q)) =
            PowerSeries.coeff k
              ((f * ∏ q ∈ s, deningerBigWittPairFactor x y i q) *
                deningerBigWittPairFactor x y i j) := by
              congr 1
              ac_rfl
        _ = PowerSeries.coeff k
              (f * ∏ q ∈ s, deningerBigWittPairFactor x y i q) :=
            coeff_mul_deningerBigWittPairFactor_of_lt_lcm _ _ _ _ _ _
              (hs j (by simp))
        _ = PowerSeries.coeff k f := ih (fun q hq => hs q (by simp [hq]))

theorem coeff_mul_prod_pairFactor_right_edge
    (f : PowerSeries A) (x y : ℕ → A) {k N : ℕ} (hk : k ≤ N) :
    PowerSeries.coeff k
        (f * ∏ i ∈ Finset.range N, deningerBigWittPairFactor x y i N) =
      PowerSeries.coeff k f := by
  apply coeff_mul_prod_pairFactor_fixed_right
  intro i hi
  exact (Nat.lt_succ_of_le hk).trans_le
    (Nat.le_lcm_right (N + 1) (Nat.succ_pos i))

theorem coeff_mul_prod_pairFactor_left_edge
    (f : PowerSeries A) (x y : ℕ → A) {k N : ℕ} (hk : k ≤ N) :
    PowerSeries.coeff k
        (f * ∏ j ∈ Finset.range (N + 1), deningerBigWittPairFactor x y N j) =
      PowerSeries.coeff k f := by
  apply coeff_mul_prod_pairFactor_fixed_left
  intro j hj
  exact (Nat.lt_succ_of_le hk).trans_le
    (Nat.le_lcm_left (N + 1) (Nat.succ_pos j))

theorem deningerBigWittPairPartial_coeff_stable_step
    (x y : ℕ → A) {k N : ℕ} (hk : k ≤ N) :
    PowerSeries.coeff k (deningerBigWittPairPartial x y (N + 1)) =
      PowerSeries.coeff k (deningerBigWittPairPartial x y N) := by
  rw [deningerBigWittPairPartial_succ,
    coeff_mul_prod_pairFactor_left_edge _ _ _ hk,
    coeff_mul_prod_pairFactor_right_edge _ _ _ hk]

theorem deningerBigWittPairPartial_coeff_stable
    (x y : ℕ → A) {k N M : ℕ} (hk : k ≤ N) (hNM : N ≤ M) :
    PowerSeries.coeff k (deningerBigWittPairPartial x y M) =
      PowerSeries.coeff k (deningerBigWittPairPartial x y N) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
      rw [deningerBigWittPairPartial_coeff_stable_step x y (hk.trans hNM), ih]

/-- Canonical integral big-Witt product series in Euler coordinates. -/
def deningerBigWittMulSeries (x y : ℕ → A) : PowerSeries A :=
  PowerSeries.mk fun n => PowerSeries.coeff n (deningerBigWittPairPartial x y n)

@[simp] theorem deningerBigWittMulSeries_coeff (x y : ℕ → A) (n : ℕ) :
    PowerSeries.coeff n (deningerBigWittMulSeries x y) =
      PowerSeries.coeff n (deningerBigWittPairPartial x y n) := by
  simp [deningerBigWittMulSeries]

@[simp] theorem deningerBigWittMulSeries_constantCoeff (x y : ℕ → A) :
    PowerSeries.constantCoeff (deningerBigWittMulSeries x y) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp

@[simp] theorem deningerBigWittMulSeries_map
    (f : A →+* B) (x y : ℕ → A) :
    PowerSeries.map f (deningerBigWittMulSeries x y) =
      deningerBigWittMulSeries (f ∘ x) (f ∘ y) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, deningerBigWittMulSeries_coeff,
    deningerBigWittMulSeries_coeff]
  exact congrArg (PowerSeries.coeff n) (deningerBigWittPairPartial_map f x y n)

/-- Canonical big-Witt product on the literal multiplicative carrier. -/
def deningerBigWittMul
    (u v : DeningerBigWittAdditive A) : DeningerBigWittAdditive A :=
  deningerBigWittOfSeries
    (deningerBigWittMulSeries
      ((deningerBigWittEulerEquiv A).symm u)
      ((deningerBigWittEulerEquiv A).symm v))
    (deningerBigWittMulSeries_constantCoeff _ _)

@[simp] theorem deningerBigWittSeries_mul
    (u v : DeningerBigWittAdditive A) :
    deningerBigWittSeries (deningerBigWittMul u v) =
      deningerBigWittMulSeries
        ((deningerBigWittEulerEquiv A).symm u)
        ((deningerBigWittEulerEquiv A).symm v) := by
  rfl

theorem deningerBigWittMul_comm
    (u v : DeningerBigWittAdditive A) :
    deningerBigWittMul u v = deningerBigWittMul v u := by
  apply Subtype.ext
  apply Units.ext
  change deningerBigWittMulSeries
      ((deningerBigWittEulerEquiv A).symm u)
      ((deningerBigWittEulerEquiv A).symm v) =
    deningerBigWittMulSeries
      ((deningerBigWittEulerEquiv A).symm v)
      ((deningerBigWittEulerEquiv A).symm u)
  apply PowerSeries.ext
  intro n
  simp only [deningerBigWittMulSeries_coeff]
  unfold deningerBigWittPairPartial
  rw [Finset.prod_comm]
  apply congrArg (PowerSeries.coeff n)
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.prod_congr rfl
  intro i hi
  simp only [deningerBigWittPairFactor, Nat.lcm_comm, Nat.gcd_comm]
  rw [mul_comm]

@[simp] theorem deningerBigWittMul_natural
    (f : A →+* B) (u v : DeningerBigWittAdditive A) :
    deningerBigWittMap f (deningerBigWittMul u v) =
      deningerBigWittMul (deningerBigWittMap f u) (deningerBigWittMap f v) := by
  apply Subtype.ext
  apply Units.ext
  change PowerSeries.map f
      (deningerBigWittMulSeries
        ((deningerBigWittEulerEquiv A).symm u)
        ((deningerBigWittEulerEquiv A).symm v)) =
    deningerBigWittMulSeries
      ((deningerBigWittEulerEquiv B).symm (deningerBigWittMap f u))
      ((deningerBigWittEulerEquiv B).symm (deningerBigWittMap f v))
  rw [deningerBigWittMulSeries_map]
  congr 1 <;> simp

end

end RHTower
