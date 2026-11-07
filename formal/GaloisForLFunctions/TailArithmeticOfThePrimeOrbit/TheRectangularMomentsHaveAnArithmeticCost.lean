import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.RectangularProductCollisions
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheConditionalMomentsOfTheTail
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueBasic

/-!
# Rectangular arithmetic costs for smooth-head tail moments

For smooth rows in `(X,2X]`, rough columns at most `Z`, and column coefficients
bounded by `K`, every centered interval of radius `T > 0` satisfies

`integral |R(U+t)|^2 |B(U+t)|^2
 <= (5*pi/2) * (T*sum|r|^2*sum|b|^2 + 4*Z*(X+Z)*(sum|r|)^2*K^2)`.

Smooth/rough uniqueness keeps the exact weighted diagonal. Quotient labels
and compatible integer differences bound the remaining logarithmic collisions;
a triangular Fourier majorant transfers their count without a harmonic loss.

The `k`th power of a bounded prime tail below `Y` has coefficient supremum
at most `k!` and squared coefficient sum at most `k!*(sum|b|^2)^k`.
Taking `Z = Y^k` gives actual higher moments and large-tail bounds, including
the literal smooth interval and prime support. The error retains the smooth
coefficient mass rather than charging all product terms.
-/

noncomputable section
open Finset MeasureTheory
namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open RHTower.Sieve

private theorem weighted_rectangular_row_le {X y m n Z : ℕ} {B : Finset ℕ}
    (hX : 0 < X) (hm : X < m) (hm' : m ≤ 2 * X) (hn : X < n) (hn' : n ≤ 2 * X)
    (hms : m ∈ Nat.smoothNumbers y) (hns : n ∈ Nat.smoothNumbers y)
    (hB : ∀ p ∈ B, IsRough y p) (hZ : ∀ p ∈ B, p ≤ Z)
    (b : ℕ → ℂ) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ p ∈ B, ‖b p‖ ≤ K)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ p ∈ B, ∑ q ∈ B,
      if |Real.log (m * p : ℕ) - Real.log (n * q : ℕ)| ≤ δ then ‖b p‖ * ‖b q‖ else 0) ≤
      (if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0) +
        (2 * (Z / X + 1) * ⌊2 * (X : ℝ) * Z * δ⌋₊ : ℕ) * K ^ 2 := by
  let D := rectangularOffDiagonalLogFiber m n Z δ
  have hpoint (p q : ℕ) (hp : p ∈ B) (hq : q ∈ B) :
      (if |Real.log (m * p : ℕ) - Real.log (n * q : ℕ)| ≤ δ then ‖b p‖ * ‖b q‖ else 0) ≤
      (if m = n then if p = q then ‖b p‖ ^ 2 else 0 else 0) +
        (if (p,q) ∈ D then K ^ 2 else 0) := by
    by_cases he : m * p = n * q
    · obtain ⟨hmn, hpq⟩ := smooth_mul_rough_injective hms hns (hB p hp) (hB q hq) he
      subst n
      subst q
      simp only [sub_self, abs_zero, if_pos hδ, if_true]
      have hnon : 0 ≤ (if (p,p) ∈ D then K ^ 2 else 0) := by split_ifs <;> positivity
      nlinarith only [hnon]
    · by_cases hc : |Real.log (m * p : ℕ) - Real.log (n * q : ℕ)| ≤ δ
      · have hmem : (p,q) ∈ D := mem_filter.mpr ⟨mem_product.mpr
          ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero (hB p hp).1, hZ p hp⟩,
            mem_Icc.mpr ⟨Nat.pos_of_ne_zero (hB q hq).1, hZ q hq⟩⟩, he, hc⟩
        rw [if_pos hc, if_pos hmem]
        have hd : 0 ≤ (if m = n then if p = q then ‖b p‖ ^ 2 else 0 else 0) := by
          split_ifs <;> positivity
        have hw := mul_le_mul (hb p hp) (hb q hq) (norm_nonneg _) hK
        nlinarith only [hw, hd]
      · rw [if_neg hc]
        split_ifs <;> positivity
  have hdiag : (∑ p ∈ B, ∑ q ∈ B,
      if m = n then if p = q then ‖b p‖ ^ 2 else 0 else 0) =
      if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0 := by
    by_cases h : m = n <;> simp [h]
  have hoff : (∑ p ∈ B, ∑ q ∈ B, if (p,q) ∈ D then K ^ 2 else 0) ≤
      (2 * (Z / X + 1) * ⌊2 * (X : ℝ) * Z * δ⌋₊ : ℕ) * K ^ 2 := by
    have hsub : ((B ×ˢ B).filter fun p => p ∈ D) ⊆ D := by
      intro p hp
      exact (mem_filter.mp hp).2
    have hc : (((B ×ˢ B).filter fun p => p ∈ D).card : ℝ) ≤
        (2 * (Z / X + 1) * ⌊2 * (X : ℝ) * Z * δ⌋₊ : ℕ) := by
      exact_mod_cast (card_le_card hsub).trans
        (rectangularOffDiagonalLogFiber_le_floor hX hm hm' hn hn' hδ)
    have he : (∑ p ∈ B, ∑ q ∈ B, if (p,q) ∈ D then K ^ 2 else 0) =
        ∑ p ∈ B ×ˢ B, if p ∈ D then K ^ 2 else 0 :=
      (sum_product B B (fun p : ℕ × ℕ => if p ∈ D then K ^ 2 else 0)).symm
    rw [he, ← sum_filter]
    simpa only [sum_const, nsmul_eq_mul] using mul_le_mul_of_nonneg_right hc (sq_nonneg K)
  calc
    _ ≤ ∑ p ∈ B, ∑ q ∈ B, ((if m = n then if p = q then ‖b p‖ ^ 2 else 0 else 0) +
        (if (p,q) ∈ D then K ^ 2 else 0)) :=
      sum_le_sum fun p hp => sum_le_sum fun q hq => hpoint p q hp hq
    _ = (if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0) +
        ∑ p ∈ B, ∑ q ∈ B, if (p,q) ∈ D then K ^ 2 else 0 := by
      simp only [sum_add_distrib, hdiag]
    _ ≤ _ := add_le_add le_rfl hoff

/-- Weighted closed logarithmic energy, separated into row and column coefficients. -/
def rectangularLogWeight (A B : Finset ℕ) (r b : ℕ → ℂ) (δ : ℝ) : ℝ :=
  ∑ m ∈ A, ∑ n ∈ A, ‖r m‖ * ‖r n‖ *
    ∑ p ∈ B, ∑ q ∈ B,
      if |Real.log (m * p : ℕ) - Real.log (n * q : ℕ)| ≤ δ then ‖b p‖ * ‖b q‖ else 0

/-- Smooth/rough uniqueness retains the exact coefficient diagonal in rectangular energy. -/
theorem rectangularLogWeight_le {X y Z : ℕ} {A B : Finset ℕ}
    (hX : 0 < X) (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hrows : ∀ m ∈ A, X < m ∧ m ≤ 2 * X)
    (hB : ∀ p ∈ B, IsRough y p) (hZ : ∀ p ∈ B, p ≤ Z)
    (r b : ℕ → ℂ) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ p ∈ B, ‖b p‖ ≤ K)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    rectangularLogWeight A B r b δ ≤
      (∑ m ∈ A, ‖r m‖ ^ 2) * (∑ p ∈ B, ‖b p‖ ^ 2) +
        (2 * (Z / X + 1) * ⌊2 * (X : ℝ) * Z * δ⌋₊ : ℕ) *
          (∑ m ∈ A, ‖r m‖) ^ 2 * K ^ 2 := by
  let C : ℝ := (2 * (Z / X + 1) * ⌊2 * (X : ℝ) * Z * δ⌋₊ : ℕ) * K ^ 2
  have hd : (∑ m ∈ A, ∑ n ∈ A, ‖r m‖ * ‖r n‖ *
      (if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0)) =
      (∑ m ∈ A, ‖r m‖ ^ 2) * (∑ p ∈ B, ‖b p‖ ^ 2) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro m hm
    simp [mul_ite, hm, sq, mul_assoc]
  have ho : (∑ m ∈ A, ∑ n ∈ A, ‖r m‖ * ‖r n‖ * C) =
      C * (∑ m ∈ A, ‖r m‖) ^ 2 := by
    simp only [← sum_mul, ← mul_sum]
    ring
  calc
    _ ≤ ∑ m ∈ A, ∑ n ∈ A, ‖r m‖ * ‖r n‖ *
        ((if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0) + C) :=
      sum_le_sum fun m hm => sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
        (weighted_rectangular_row_le hX (hrows m hm).1 (hrows m hm).2
          (hrows n hn).1 (hrows n hn).2 (hA m hm) (hA n hn) hB hZ b hK hb hδ)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp only [mul_add, sum_add_distrib, hd, ho]; dsimp only [C]; ring

private def rectangularFrequency (p : ℕ × ℕ) : ℝ :=
  Real.log (p.1 * p.2 : ℕ) / (2 * Real.pi)

private theorem finiteFrequencyPoly_eq_rectangular (A B : Finset ℕ)
    (r b : ℕ → ℂ) (t : ℝ) :
    finiteFrequencyPoly (fun p => r p.1 * b p.2) (A ×ˢ B) rectangularFrequency t =
      indexedPoly (A ×ˢ B) (fun p => p.1 * p.2) (fun p => r p.1 * b p.2) t := by
  unfold finiteFrequencyPoly indexedPoly
  apply sum_congr rfl
  intro p _
  have he : 2 * Real.pi * (t * rectangularFrequency p) = t * Real.log (p.1 * p.2 : ℕ) := by
    dsimp only [rectangularFrequency]
    field_simp
  rw [he]

private theorem rectangularFrequency_close (p q : ℕ × ℕ) {T : ℝ}
    (hclose : |rectangularFrequency p - rectangularFrequency q| < 1 / (2 * Real.pi * T)) :
    |Real.log (p.1 * p.2 : ℕ) - Real.log (q.1 * q.2 : ℕ)| ≤ 1 / T := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have he : |rectangularFrequency p - rectangularFrequency q| =
      |Real.log (p.1 * p.2 : ℕ) - Real.log (q.1 * q.2 : ℕ)| / (2 * Real.pi) := by
    dsimp only [rectangularFrequency]
    rw [← sub_div, abs_div, abs_of_pos hpi]
  have hd : 1 / (2 * Real.pi * T) = (1 / T) / (2 * Real.pi) := by ring
  rw [he, hd] at hclose
  exact ((div_lt_div_iff_of_pos_right hpi).mp hclose).le

private theorem rectangular_frequency_weight_le (A B : Finset ℕ) (r b : ℕ → ℂ) {T : ℝ} :
    finiteFrequencyCollisionWeight (fun p => r p.1 * b p.2) (A ×ˢ B)
      rectangularFrequency (1 / (2 * Real.pi * T)) ≤ rectangularLogWeight A B r b (1 / T) := by
  unfold finiteFrequencyCollisionWeight rectangularLogWeight
  simp only [sum_product]
  apply sum_le_sum
  intro m hm
  rw [sum_comm (s := B) (t := A)]
  apply sum_le_sum
  intro n hn
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  by_cases hc : |rectangularFrequency (m,p) - rectangularFrequency (n,q)| < 1 / (2 * Real.pi * T)
  · rw [if_pos hc, if_pos (rectangularFrequency_close (m,p) (n,q) hc)]
    simp only [norm_mul]
    exact le_of_eq (by ring)
  · rw [if_neg hc]
    split_ifs <;> positivity

private theorem integral_rectangular_head_tail_zero_le {X y Z : ℕ} {A B : Finset ℕ}
    (hX : 0 < X) (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hrows : ∀ m ∈ A, X < m ∧ m ≤ 2 * X)
    (hB : ∀ p ∈ B, IsRough y p) (hZ : ∀ p ∈ B, p ≤ Z)
    (r b : ℕ → ℂ) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ p ∈ B, ‖b p‖ ≤ K)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T, ‖headPoly A r t‖ ^ 2 * ‖headPoly B b t‖ ^ 2) ≤
      (5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * (∑ p ∈ B, ‖b p‖ ^ 2) +
          4 * (Z : ℝ) * (X + Z) * (∑ m ∈ A, ‖r m‖) ^ 2 * K ^ 2) := by
  have hδ : 0 < 1 / (2 * Real.pi * T) := by positivity
  have hscale : 2 * Real.pi * (1 / (2 * Real.pi * T)) * T ≤ 1 := by
    field_simp
    exact le_rfl
  have hker := integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight
    (fun p => r p.1 * b p.2) (A ×ˢ B) rectangularFrequency hδ hscale
  have hA0 : ∀ m ∈ A, m ≠ 0 := fun m hm => Nat.ne_zero_of_mem_smoothNumbers (hA m hm)
  have hB0 : ∀ p ∈ B, p ≠ 0 := fun p hp => (hB p hp).1
  simp_rw [finiteFrequencyPoly_eq_rectangular, ← headPoly_mul A B r b hA0 hB0,
    norm_mul, mul_pow] at hker
  have henergy := (rectangular_frequency_weight_le A B r b (T := T)).trans
    (rectangularLogWeight_le hX hA hrows hB hZ r b hK hb (by positivity : 0 ≤ 1 / T))
  let H := ⌊2 * (X : ℝ) * Z * (1 / T)⌋₊
  have hTF : T * (H : ℝ) ≤ 2 * (X : ℝ) * Z := by
    calc
      _ ≤ T * (2 * (X : ℝ) * Z * (1 / T)) :=
        mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) hT.le
      _ = _ := by field_simp
  have hquot : (X : ℝ) * (Z / X + 1 : ℕ) ≤ (Z : ℝ) + X := by
    have h := Nat.mul_div_le Z X
    exact_mod_cast (show X * (Z / X + 1) ≤ Z + X by nlinarith only [h])
  have hcost : T * ((2 * (Z / X + 1) * H : ℕ) : ℝ) ≤ 4 * (Z : ℝ) * (X + Z) := by
    calc
      _ = (2 * ((Z / X + 1 : ℕ) : ℝ)) * (T * H) := by push_cast; ring
      _ ≤ (2 * ((Z / X + 1 : ℕ) : ℝ)) * (2 * (X : ℝ) * Z) :=
        mul_le_mul_of_nonneg_left hTF (by positivity)
      _ = (4 * (Z : ℝ)) * ((X : ℝ) * ((Z / X + 1 : ℕ) : ℝ)) := by ring
      _ ≤ (4 * (Z : ℝ)) * ((Z : ℝ) + X) := mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = _ := by ring
  have hscaled : T * finiteFrequencyCollisionWeight (fun p => r p.1 * b p.2)
      (A ×ˢ B) rectangularFrequency (1 / (2 * Real.pi * T)) ≤
      T * (∑ m ∈ A, ‖r m‖ ^ 2) * (∑ p ∈ B, ‖b p‖ ^ 2) +
        4 * (Z : ℝ) * (X + Z) * (∑ m ∈ A, ‖r m‖) ^ 2 * K ^ 2 := by
    calc
      _ ≤ T * ((∑ m ∈ A, ‖r m‖ ^ 2) * (∑ p ∈ B, ‖b p‖ ^ 2) +
          ((2 * (Z / X + 1) * H : ℕ) : ℝ) * (∑ m ∈ A, ‖r m‖) ^ 2 * K ^ 2) :=
        mul_le_mul_of_nonneg_left henergy hT.le
      _ = T * (∑ m ∈ A, ‖r m‖ ^ 2) * (∑ p ∈ B, ‖b p‖ ^ 2) +
          (T * ((2 * (Z / X + 1) * H : ℕ) : ℝ)) * ((∑ m ∈ A, ‖r m‖) ^ 2 * K ^ 2) := by ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hcost (by positivity : 0 ≤ (∑ m ∈ A, ‖r m‖) ^ 2 * K ^ 2)
        nlinarith only [h]
  calc
    _ ≤ _ := hker
    _ = (5 * Real.pi / 2) * (T * finiteFrequencyCollisionWeight
        (fun p => r p.1 * b p.2) (A ×ˢ B) rectangularFrequency (1 / (2 * Real.pi * T))) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscaled (by positivity)

private def shiftCoeff (c : ℕ → ℂ) (U : ℝ) (n : ℕ) : ℂ :=
  c n * Complex.exp (((U * Real.log n : ℝ) : ℂ) * Complex.I)

private theorem norm_shiftCoeff (c : ℕ → ℂ) (U : ℝ) (n : ℕ) : ‖shiftCoeff c U n‖ = ‖c n‖ := by
  rw [shiftCoeff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem headPoly_shiftCoeff (A : Finset ℕ) (c : ℕ → ℂ) (U t : ℝ) :
    headPoly A (shiftCoeff c U) t = headPoly A c (U + t) := by
  unfold headPoly
  apply sum_congr rfl
  intro n _
  dsimp only [shiftCoeff]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Every centered smooth-head/rough-tail mean square has a rectangular arithmetic error. -/
theorem integral_rectangular_head_tail_le {X y Z : ℕ} {A B : Finset ℕ}
    (hX : 0 < X) (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hrows : ∀ m ∈ A, X < m ∧ m ≤ 2 * X)
    (hB : ∀ p ∈ B, IsRough y p) (hZ : ∀ p ∈ B, p ≤ Z)
    (r b : ℕ → ℂ) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ p ∈ B, ‖b p‖ ≤ K)
    (U : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T, ‖headPoly A r (U + t)‖ ^ 2 * ‖headPoly B b (U + t)‖ ^ 2) ≤
      (5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * (∑ p ∈ B, ‖b p‖ ^ 2) +
          4 * (Z : ℝ) * (X + Z) * (∑ m ∈ A, ‖r m‖) ^ 2 * K ^ 2) := by
  have hb' : ∀ p ∈ B, ‖shiftCoeff b U p‖ ≤ K := by
    intro p hp
    rw [norm_shiftCoeff]
    exact hb p hp
  have h := integral_rectangular_head_tail_zero_le hX hA hrows hB hZ
    (shiftCoeff r U) (shiftCoeff b U) hK hb' hT
  simpa only [headPoly_shiftCoeff, norm_shiftCoeff] using h


/-- A bounded prime coefficient vector has convolution coefficients at most `k!`. -/
theorem norm_powCoeff_le_factorial {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime)
    (b : ℕ → ℂ) (hb : ∀ p ∈ B, ‖b p‖ ≤ 1) :
    ∀ k, ∀ q ∈ powSupport B k, ‖powCoeff B b k q‖ ≤ (k.factorial : ℝ)
  | 0, q, _ => by simp [powCoeff]
  | k + 1, q, hq => by
    let F := (powSupport B k ×ˢ B).filter (fun x => x.1 * x.2 = q)
    have hcard : (F.card : ℝ) ≤ k + 1 := by exact_mod_cast card_fiber_le hB k hq
    calc
      _ ≤ ∑ x ∈ F, ‖powCoeff B b k x.1 * b x.2‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ F, (k.factorial : ℝ) := by
        apply sum_le_sum
        intro x hx
        obtain ⟨hx1, hx2⟩ := mem_product.mp (mem_filter.mp hx).1
        rw [norm_mul]
        exact (mul_le_mul (norm_powCoeff_le_factorial hB b hb k x.1 hx1)
          (hb x.2 hx2) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
      _ = (F.card : ℝ) * k.factorial := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ (k + 1) * k.factorial := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ((k + 1).factorial : ℝ) := by
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]


/-- Prime-tail moments retain the rectangular arithmetic error and the factorial diagonal. -/
theorem integral_rectangular_head_prime_tail_pow_le {X y Y : ℕ} {A B : Finset ℕ}
    (hX : 0 < X) (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hrows : ∀ m ∈ A, X < m ∧ m ≤ 2 * X)
    (hB : ∀ p ∈ B, p.Prime ∧ y ≤ p) (hY : ∀ p ∈ B, p ≤ Y)
    (r b : ℕ → ℂ) (hb : ∀ p ∈ B, ‖b p‖ ≤ 1) (k : ℕ)
    (U : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T, ‖headPoly A r (U + t)‖ ^ 2 *
        ‖headPoly B b (U + t)‖ ^ (2 * k)) ≤
      (5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * ((k.factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k) +
          4 * (Y : ℝ) ^ k * (X + (Y : ℝ) ^ k) *
            (∑ m ∈ A, ‖r m‖) ^ 2 * (k.factorial : ℝ) ^ 2) := by
  have hrough : ∀ q ∈ powSupport B k, IsRough y q :=
    powSupport_rough (fun p hp => isRough_of_prime (hB p hp).1 (hB p hp).2) k
  have hcoef : ∀ q ∈ powSupport B k, ‖powCoeff B b k q‖ ≤ (k.factorial : ℝ) :=
    norm_powCoeff_le_factorial (fun p hp => (hB p hp).1) b hb k
  have h := integral_rectangular_head_tail_le hX hA hrows hrough (powSupport_le hY k)
    r (powCoeff B b k) (by positivity : 0 ≤ (k.factorial : ℝ)) hcoef U hT
  have hpoly (t : ℝ) : ‖headPoly (powSupport B k) (powCoeff B b k) (U+t)‖ ^ 2 =
      ‖headPoly B b (U+t)‖ ^ (2*k) := by
    rw [← headPoly_pow b (fun p hp => (hB p hp).1.ne_zero) (U+t) k, norm_pow,
      ← pow_mul, mul_comm k 2]
  simp only [hpoly, Nat.cast_pow] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_left (powNorm_le (fun p hp => (hB p hp).1) b k)
    (by positivity : 0 ≤ T * ∑ m ∈ A, ‖r m‖ ^ 2)


/-- Large prime-tail events pay their full moment threshold under smooth-head weight. -/
theorem setIntegral_rectangular_head_on_large_prime_tail_le {X y Y : ℕ} {A B : Finset ℕ}
    (hX : 0 < X) (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hrows : ∀ m ∈ A, X < m ∧ m ≤ 2 * X)
    (hB : ∀ p ∈ B, p.Prime ∧ y ≤ p) (hY : ∀ p ∈ B, p ≤ Y)
    (r b : ℕ → ℂ) (hb : ∀ p ∈ B, ‖b p‖ ≤ 1) (k : ℕ)
    (U : ℝ) {T V : ℝ} (hT : 0 < T) (hV : 0 < V) :
    (∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖headPoly B b (U+t)‖},
        ‖headPoly A r (U+t)‖ ^ 2) ≤
      ((5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * ((k.factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k) +
          4 * (Y : ℝ) ^ k * (X + (Y : ℝ) ^ k) *
            (∑ m ∈ A, ‖r m‖) ^ 2 * (k.factorial : ℝ) ^ 2)) / V ^ (2*k) := by
  let R (t : ℝ) := headPoly A r (U+t)
  let Q (t : ℝ) := headPoly B b (U+t)
  have hcR : Continuous R := (continuous_headPoly A r).comp (continuous_const.add continuous_id)
  have hcQ : Continuous Q := (continuous_headPoly B b).comp (continuous_const.add continuous_id)
  let g (t : ℝ) := (‖R t‖ ^ 2 * ‖Q t‖ ^ (2*k)) / V ^ (2*k)
  have hgc : Continuous g := ((hcR.norm.pow 2).mul (hcQ.norm.pow (2*k))).div_const _
  have hclosed : IsClosed {t | V ≤ ‖Q t‖} := isClosed_le continuous_const hcQ.norm
  have hcompact : IsCompact (Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}) := isCompact_Icc.inter_right hclosed
  have hmeas : MeasurableSet (Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}) :=
    measurableSet_Icc.inter hclosed.measurableSet
  have h1 : (∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}, ‖R t‖ ^ 2) ≤
      ∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}, g t := by
    apply setIntegral_mono_on ((hcR.norm.pow 2).continuousOn.integrableOn_compact hcompact)
      (hgc.continuousOn.integrableOn_compact hcompact) hmeas
    intro t ht
    dsimp only [g]
    apply (le_div_iff₀ (by positivity : 0 < V ^ (2*k))).mpr
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV.le ht.2 (2*k)) (sq_nonneg _)
  have h2 : (∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}, g t) ≤
      ∫ t in Set.Icc (-T) T, g t :=
    setIntegral_mono_set hgc.integrableOn_Icc (Filter.Eventually.of_forall fun t => by
      dsimp only [g]; positivity) (Filter.Eventually.of_forall Set.inter_subset_left)
  have h3 : (∫ t in Set.Icc (-T) T, g t) =
      (∫ t in Set.Icc (-T) T, ‖R t‖ ^ 2 * ‖Q t‖ ^ (2*k)) / V ^ (2*k) := by
    dsimp only [g]
    rw [MeasureTheory.integral_div]
  have h4 := div_le_div_of_nonneg_right
    (integral_rectangular_head_prime_tail_pow_le hX hA hrows hB hY r b hb k U hT)
    (by positivity : 0 ≤ V ^ (2*k))
  exact h1.trans (h2.trans (h3.trans_le h4))


/-- The literal smooth interval and prime tail satisfy the arithmetic moment bound. -/
theorem integral_rectangular_full_prime_tail_pow_le (X y Y k : ℕ) (hX : 0 < X)
    (U : ℝ) {T : ℝ} (hT : 0 < T) :
    let A := (Ioc X (2*X)).filter fun m => m ∈ Nat.smoothNumbers y
    let B := (Icc y Y).filter Nat.Prime
    (∫ t in Set.Icc (-T) T, ‖headPoly A (fun _ => 1) (U+t)‖ ^ 2 *
        ‖headPoly B (fun _ => 1) (U+t)‖ ^ (2*k)) ≤
      (5 * Real.pi / 2) *
        (T * (A.card : ℝ) * ((k.factorial : ℝ) * (B.card : ℝ) ^ k) +
          4 * (Y : ℝ) ^ k * (X + (Y : ℝ) ^ k) *
            (A.card : ℝ) ^ 2 * (k.factorial : ℝ) ^ 2) := by
  dsimp only
  let A := (Ioc X (2*X)).filter fun m => m ∈ Nat.smoothNumbers y
  let B := (Icc y Y).filter Nat.Prime
  have hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y := fun m hm => (mem_filter.mp hm).2
  have hrows : ∀ m ∈ A, X < m ∧ m ≤ 2 * X :=
    fun m hm => mem_Ioc.mp (mem_filter.mp hm).1
  have hB : ∀ p ∈ B, p.Prime ∧ y ≤ p := fun p hp =>
    ⟨(mem_filter.mp hp).2, (mem_Icc.mp (mem_filter.mp hp).1).1⟩
  have hY : ∀ p ∈ B, p ≤ Y := fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).2
  have h := integral_rectangular_head_prime_tail_pow_le hX hA hrows hB hY
    (fun _ => 1) (fun _ => 1) (by intro p hp; simp) k U hT
  simpa only [norm_one, one_pow, sum_const, nsmul_eq_mul, mul_one] using h


end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
