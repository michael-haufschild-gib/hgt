import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.CumulativeSmoothPrimeEnergy
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueBasic

/-!
# The arithmetic cost of a smooth-times-prime mean square

Let smooth rows `A` and prime columns `B` lie in `(X, 2X]`, with all row
prime factors at most `y` and every column prime above `y`. For coefficients
of modulus at most one, every height center `U` and radius `T > 0` satisfy

`integral_{-T}^T |sum c(m,p) (mp)^(-i(U+t))|^2
  <= (5*pi/2) * (T*card(A)*card(B) + 8*X^2*card(A)^2)`.

Unique smooth/prime factorization identifies the diagonal. Summing compatible
integer differences cancels the off-diagonal gcd cost. A triangular Fourier
majorant transfers this count to the physical mean square without a harmonic
logarithmic loss. Factorized coefficients give smooth-head-weighted prime-tail
second moments, and restriction to a large-tail event costs its threshold squared.
-/

noncomputable section
open Finset MeasureTheory
namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open GaloisForLFunctions.Goldbach
open RHTower.Sieve

private def closedProductFiber {X : ℕ} (B : Finset (Fin X)) (m₁ m₂ : Fin X) (δ : ℝ) :
    Finset (Fin X × Fin X) :=
  (B ×ˢ B).filter fun p =>
    |Real.log (balancedIntervalValue m₁ * balancedIntervalValue p.1 : ℕ) -
      Real.log (balancedIntervalValue m₂ * balancedIntervalValue p.2 : ℕ)| ≤ δ

private theorem closedProductFiber_le {X y : ℕ} {B : Finset (Fin X)}
    (hB : B ⊆ roughPrimeColumns X y) (m₁ m₂ : Fin X)
    (hm₁ : m₁ ∈ smoothRows X y) (hm₂ : m₂ ∈ smoothRows X y)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (closedProductFiber B m₁ m₂ δ).card ≤
      (if m₁ = m₂ then B.card else 0) + 2 * ⌊4 * (X : ℝ) ^ 2 * δ⌋₊ := by
  let D : Finset (Fin X × Fin X) := if m₁ = m₂ then B.diag else ∅
  let U := smoothPrimeUpperLogFiber y m₁ m₂ δ
  let V := (smoothPrimeUpperLogFiber y m₂ m₁ δ).image Prod.swap
  have hcover : closedProductFiber B m₁ m₂ δ ⊆ (D ∪ U) ∪ V := by
    intro p hp
    obtain ⟨hpB, hclose⟩ := mem_filter.mp hp
    obtain ⟨hp₁, hp₂⟩ := mem_product.mp hpB
    have hpCols := mem_product.mpr ⟨hB hp₁, hB hp₂⟩
    have hab := abs_le.mp hclose
    by_cases hlt : balancedIntervalValue m₁ * balancedIntervalValue p.1 <
        balancedIntervalValue m₂ * balancedIntervalValue p.2
    · apply mem_union_left
      apply mem_union_right
      exact mem_filter.mpr ⟨hpCols, hlt, by linarith only [hab.1]⟩
    · by_cases hgt : balancedIntervalValue m₂ * balancedIntervalValue p.2 <
          balancedIntervalValue m₁ * balancedIntervalValue p.1
      · apply mem_union_right
        apply mem_image.mpr
        refine ⟨Prod.swap p, ?_, Prod.swap_swap p⟩
        exact mem_filter.mpr ⟨mem_product.mpr ⟨hB hp₂, hB hp₁⟩, hgt, hab.2⟩
      · have he : balancedIntervalValue m₁ * balancedIntervalValue p.1 =
            balancedIntervalValue m₂ * balancedIntervalValue p.2 := by omega
        have hp1 := (mem_filter.mp (hB hp₁)).2
        have hp2 := (mem_filter.mp (hB hp₂)).2
        have heq := (smooth_prime_product_eq_iff (mem_filter.mp hm₁).2 (mem_filter.mp hm₂).2
          hp1.1 hp2.1 hp1.2 hp2.2).mp he
        have hm : m₁ = m₂ := balancedIntervalValue_injective X heq.1
        have hp : p.1 = p.2 := balancedIntervalValue_injective X heq.2
        apply mem_union_left
        apply mem_union_left
        dsimp only [D]
        rw [if_pos hm]
        exact mem_diag.mpr ⟨hp₁, hp⟩
  have hD : D.card = if m₁ = m₂ then B.card else 0 := by
    dsimp only [D]
    split_ifs <;> simp only [diag_card, card_empty]
  have hU : U.card ≤ ⌊4 * (X : ℝ) ^ 2 * δ⌋₊ := smoothPrimeUpperLogFiber_le_floor y m₁ m₂ hδ
  have hV : V.card ≤ ⌊4 * (X : ℝ) ^ 2 * δ⌋₊ :=
    card_image_le.trans (smoothPrimeUpperLogFiber_le_floor y m₂ m₁ hδ)
  calc
    _ ≤ ((D ∪ U) ∪ V).card := card_le_card hcover
    _ ≤ (D.card + U.card) + V.card :=
      (card_union_le (D ∪ U) V).trans (Nat.add_le_add_right (card_union_le D U) _)
    _ ≤ (if m₁ = m₂ then B.card else 0) +
        ⌊4 * (X : ℝ) ^ 2 * δ⌋₊ + ⌊4 * (X : ℝ) ^ 2 * δ⌋₊ := by
      rw [hD]
      exact Nat.add_le_add (Nat.add_le_add_left hU _) hV
    _ = _ := by omega

/-- Closed logarithmic energy on arbitrary balanced smooth and prime sub-supports. -/
def balancedSmoothPrimeEnergy {X : ℕ} (A B : Finset (Fin X)) (δ : ℝ) : ℕ :=
  ∑ m₁ ∈ A, ∑ m₂ ∈ A, (closedProductFiber B m₁ m₂ δ).card

/-- Arbitrary balanced smooth and prime sub-supports retain the cumulative arithmetic envelope. -/
theorem balancedSmoothPrimeEnergy_le {X y : ℕ} {A B : Finset (Fin X)}
    (hA : A ⊆ smoothRows X y) (hB : B ⊆ roughPrimeColumns X y)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    balancedSmoothPrimeEnergy A B δ ≤ A.card * B.card +
      2 * ⌊4 * (X : ℝ) ^ 2 * δ⌋₊ * A.card ^ 2 := by
  have hdiag : (∑ m₁ ∈ A, ∑ m₂ ∈ A, if m₁ = m₂ then B.card else 0) = A.card * B.card := by
    simp
  calc
    _ ≤ ∑ m₁ ∈ A, ∑ m₂ ∈ A,
        ((if m₁ = m₂ then B.card else 0) + 2 * ⌊4 * (X : ℝ) ^ 2 * δ⌋₊) :=
      sum_le_sum fun m₁ hm₁ => sum_le_sum fun m₂ hm₂ =>
        closedProductFiber_le hB m₁ m₂ (hA hm₁) (hA hm₂) hδ
    _ = _ := by
      simp only [sum_add_distrib, hdiag, sum_const, nsmul_eq_mul, Nat.cast_id]
      ring

/-- Actual bounded-coefficient product polynomial on balanced smooth and prime sub-supports. -/
def balancedSmoothPrimePoly {X : ℕ} (A B : Finset (Fin X)) (c : Fin X × Fin X → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ A, ∑ p ∈ B, c (m, p) * Complex.exp
    ((-((t * Real.log (balancedIntervalValue m * balancedIntervalValue p : ℕ) : ℝ) : ℂ)) * Complex.I)

private def balancedFrequency {X : ℕ} (p : Fin X × Fin X) : ℝ :=
  -Real.log (balancedIntervalValue p.1 * balancedIntervalValue p.2 : ℕ) / (2 * Real.pi)

private theorem finiteFrequencyPoly_eq_balanced {X : ℕ} (A B : Finset (Fin X))
    (c : Fin X × Fin X → ℂ) (t : ℝ) :
    finiteFrequencyPoly c (A ×ˢ B) balancedFrequency t = balancedSmoothPrimePoly A B c t := by
  rw [finiteFrequencyPoly, sum_product, balancedSmoothPrimePoly]
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro p _
  have he : 2 * Real.pi * (t * balancedFrequency (m, p)) =
      -(t * Real.log (balancedIntervalValue m * balancedIntervalValue p : ℕ)) := by
    dsimp only [balancedFrequency]
    field_simp
  rw [he, Complex.ofReal_neg]

private theorem balancedFrequency_close {X : ℕ} (p q : Fin X × Fin X) {T : ℝ}
    (hclose : |balancedFrequency p - balancedFrequency q| < 1 / (2 * Real.pi * T)) :
    |Real.log (balancedIntervalValue p.1 * balancedIntervalValue p.2 : ℕ) -
      Real.log (balancedIntervalValue q.1 * balancedIntervalValue q.2 : ℕ)| ≤ 1 / T := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have he : |balancedFrequency p - balancedFrequency q| =
      |Real.log (balancedIntervalValue p.1 * balancedIntervalValue p.2 : ℕ) -
        Real.log (balancedIntervalValue q.1 * balancedIntervalValue q.2 : ℕ)| / (2 * Real.pi) := by
    dsimp only [balancedFrequency]
    rw [show -Real.log (balancedIntervalValue p.1 * balancedIntervalValue p.2 : ℕ) / (2 * Real.pi) -
        -Real.log (balancedIntervalValue q.1 * balancedIntervalValue q.2 : ℕ) / (2 * Real.pi) =
        -(Real.log (balancedIntervalValue p.1 * balancedIntervalValue p.2 : ℕ) -
          Real.log (balancedIntervalValue q.1 * balancedIntervalValue q.2 : ℕ)) / (2 * Real.pi) by ring,
      abs_div, abs_neg, abs_of_pos hpi]
  have hd : 1 / (2 * Real.pi * T) = (1 / T) / (2 * Real.pi) := by ring
  rw [he, hd] at hclose
  exact ((div_lt_div_iff_of_pos_right hpi).mp hclose).le

private theorem weightedCollision_le_energy {X : ℕ} (A B : Finset (Fin X))
    (c : Fin X × Fin X → ℂ) (hc : ∀ p ∈ A ×ˢ B, ‖c p‖ ≤ 1) {T : ℝ} :
    finiteFrequencyCollisionWeight c (A ×ˢ B) balancedFrequency (1 / (2 * Real.pi * T)) ≤
      (balancedSmoothPrimeEnergy A B (1 / T) : ℝ) := by
  let F (p q : Fin X × Fin X) : ℝ :=
    if |Real.log (balancedIntervalValue p.1 * balancedIntervalValue p.2 : ℕ) -
      Real.log (balancedIntervalValue q.1 * balancedIntervalValue q.2 : ℕ)| ≤ 1 / T then 1 else 0
  have hb : finiteFrequencyCollisionWeight c (A ×ˢ B) balancedFrequency (1 / (2 * Real.pi * T)) ≤
      ∑ p ∈ A ×ˢ B, ∑ q ∈ A ×ˢ B, F p q := by
    unfold finiteFrequencyCollisionWeight
    apply sum_le_sum
    intro p hp
    apply sum_le_sum
    intro q hq
    by_cases hclose : |balancedFrequency p - balancedFrequency q| < 1 / (2 * Real.pi * T)
    · rw [if_pos hclose]
      dsimp only [F]
      rw [if_pos (balancedFrequency_close p q hclose)]
      calc
        _ ≤ 1 * 1 := mul_le_mul (hc p hp) (hc q hq) (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    · rw [if_neg hclose]
      dsimp only [F]
      split_ifs <;> norm_num
  apply hb.trans_eq
  have hreorder : (∑ m ∈ A, ∑ p ∈ B, ∑ n ∈ A, ∑ q ∈ B, F (m, p) (n, q)) =
      ∑ m ∈ A, ∑ n ∈ A, ∑ p ∈ B, ∑ q ∈ B, F (m, p) (n, q) := by
    apply sum_congr rfl
    intro m _
    rw [sum_comm (s := B) (t := A)]
  simp only [sum_product]
  rw [hreorder]
  unfold balancedSmoothPrimeEnergy
  push_cast
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro n _
  rw [closedProductFiber, card_filter]
  push_cast
  rw [sum_product]
  simp only [F, Nat.cast_mul]

private theorem integral_balancedSmoothPrimePoly_le_energy {X : ℕ} (A B : Finset (Fin X))
    (c : Fin X × Fin X → ℂ) (hc : ∀ p ∈ A ×ˢ B, ‖c p‖ ≤ 1) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T, ‖balancedSmoothPrimePoly A B c t‖ ^ (2 : ℕ)) ≤
      (5 * Real.pi / 2) * T * (balancedSmoothPrimeEnergy A B (1 / T) : ℝ) := by
  have hδ : 0 < 1 / (2 * Real.pi * T) := by positivity
  have hscale : 2 * Real.pi * (1 / (2 * Real.pi * T)) * T ≤ 1 := by
    field_simp
    exact le_rfl
  have h := integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight c (A ×ˢ B) balancedFrequency hδ hscale
  simp_rw [finiteFrequencyPoly_eq_balanced] at h
  apply h.trans
  calc
    _ ≤ (5 / (4 * (1 / (2 * Real.pi * T)))) *
        (balancedSmoothPrimeEnergy A B (1 / T) : ℝ) :=
      mul_le_mul_of_nonneg_left (weightedCollision_le_energy A B c hc) (by positivity)
    _ = _ := by field_simp; ring

/-- A bounded-coefficient smooth–prime polynomial has an off-diagonal cost quadratic only in its smooth support. -/
theorem integral_balancedSmoothPrimePoly_le {X y : ℕ} {A B : Finset (Fin X)}
    (hA : A ⊆ smoothRows X y) (hB : B ⊆ roughPrimeColumns X y)
    (c : Fin X × Fin X → ℂ) (hc : ∀ p ∈ A ×ˢ B, ‖c p‖ ≤ 1) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T, ‖balancedSmoothPrimePoly A B c t‖ ^ (2 : ℕ)) ≤
      (5 * Real.pi / 2) *
        (T * (A.card : ℝ) * B.card + 8 * (X : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := by
  have hE : (balancedSmoothPrimeEnergy A B (1 / T) : ℝ) ≤
      (A.card : ℝ) * B.card + 2 * (⌊4 * (X : ℝ) ^ 2 * (1 / T)⌋₊ : ℝ) * (A.card : ℝ) ^ 2 := by
    exact_mod_cast balancedSmoothPrimeEnergy_le hA hB (by positivity : 0 ≤ 1 / T)
  have hfloor := Nat.floor_le (by positivity : 0 ≤ 4 * (X : ℝ) ^ 2 * (1 / T))
  have hTF : T * (⌊4 * (X : ℝ) ^ 2 * (1 / T)⌋₊ : ℝ) ≤ 4 * (X : ℝ) ^ 2 := by
    calc
      _ ≤ T * (4 * (X : ℝ) ^ 2 * (1 / T)) := mul_le_mul_of_nonneg_left hfloor hT.le
      _ = _ := by field_simp
  have hscaled : T * (balancedSmoothPrimeEnergy A B (1 / T) : ℝ) ≤
      T * (A.card : ℝ) * B.card + 8 * (X : ℝ) ^ 2 * (A.card : ℝ) ^ 2 := by
    calc
      _ ≤ T * ((A.card : ℝ) * B.card +
          2 * (⌊4 * (X : ℝ) ^ 2 * (1 / T)⌋₊ : ℝ) * (A.card : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hE hT.le
      _ = T * (A.card : ℝ) * B.card +
          (T * (⌊4 * (X : ℝ) ^ 2 * (1 / T)⌋₊ : ℝ)) * (2 * (A.card : ℝ) ^ 2) := by ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hTF (by positivity : 0 ≤ 2 * (A.card : ℝ) ^ 2)
        nlinarith only [h]
  calc
    _ ≤ (5 * Real.pi / 2) * T * (balancedSmoothPrimeEnergy A B (1 / T) : ℝ) :=
      integral_balancedSmoothPrimePoly_le_energy A B c hc hT
    _ = (5 * Real.pi / 2) * (T * (balancedSmoothPrimeEnergy A B (1 / T) : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscaled (by positivity)

/-- The arithmetic mean-square bound is uniform in the center of the height interval. -/
theorem integral_balancedSmoothPrimePoly_shift_le {X y : ℕ} {A B : Finset (Fin X)}
    (hA : A ⊆ smoothRows X y) (hB : B ⊆ roughPrimeColumns X y)
    (c : Fin X × Fin X → ℂ) (hc : ∀ p ∈ A ×ˢ B, ‖c p‖ ≤ 1)
    (U : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T, ‖balancedSmoothPrimePoly A B c (U + t)‖ ^ (2 : ℕ)) ≤
      (5 * Real.pi / 2) *
        (T * (A.card : ℝ) * B.card + 8 * (X : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := by
  let d (p : Fin X × Fin X) : ℂ := c p * Complex.exp
    (((-(U * Real.log (balancedIntervalValue p.1 * balancedIntervalValue p.2 : ℕ)) : ℝ) : ℂ) * Complex.I)
  have hd : ∀ p ∈ A ×ˢ B, ‖d p‖ ≤ 1 := by
    intro p hp
    dsimp only [d]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hc p hp
  have hshift (t : ℝ) : balancedSmoothPrimePoly A B d t = balancedSmoothPrimePoly A B c (U + t) := by
    unfold balancedSmoothPrimePoly
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro p _
    dsimp only [d]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h := integral_balancedSmoothPrimePoly_le hA hB d hd hT
  simpa only [hshift] using h

/-- The literal unweighted smooth–prime sum obeys the uniform arithmetic mean-square estimate. -/
theorem integral_fullSmoothPrimePoly_shift_le (X y : ℕ) (U : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T,
      ‖balancedSmoothPrimePoly (smoothRows X y) (roughPrimeColumns X y) (fun _ => 1) (U + t)‖ ^ (2 : ℕ)) ≤
      (5 * Real.pi / 2) * (T * ((smoothRows X y).card : ℝ) * (roughPrimeColumns X y).card +
        8 * (X : ℝ) ^ 2 * ((smoothRows X y).card : ℝ) ^ 2) := by
  exact integral_balancedSmoothPrimePoly_shift_le (Finset.Subset.refl _) (Finset.Subset.refl _)
    (fun _ => 1) (by intro p hp; simp) U hT

/-- A finite physical Dirichlet polynomial on a balanced integer block. -/
def balancedBlockDirichletPoly {X : ℕ} (A : Finset (Fin X)) (r : Fin X → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ A, r m * Complex.exp ((-((t * Real.log (balancedIntervalValue m) : ℝ) : ℂ)) * Complex.I)

private theorem balancedSmoothPrimePoly_mul {X : ℕ} (A B : Finset (Fin X))
    (r b : Fin X → ℂ) (t : ℝ) :
    balancedSmoothPrimePoly A B (fun p => r p.1 * b p.2) t =
      balancedBlockDirichletPoly A r t * balancedBlockDirichletPoly B b t := by
  rw [balancedSmoothPrimePoly, balancedBlockDirichletPoly, balancedBlockDirichletPoly, sum_mul_sum]
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro p _
  have hm : (balancedIntervalValue m : ℝ) ≠ 0 := by exact_mod_cast (balancedIntervalValue_pos m).ne'
  have hp : (balancedIntervalValue p : ℝ) ≠ 0 := by exact_mod_cast (balancedIntervalValue_pos p).ne'
  rw [Nat.cast_mul, Real.log_mul hm hp]
  have he : Complex.exp ((-((t * (Real.log (balancedIntervalValue m : ℝ) +
      Real.log (balancedIntervalValue p : ℝ)) : ℝ) : ℂ)) * Complex.I) =
      Complex.exp ((-((t * Real.log (balancedIntervalValue m : ℝ) : ℝ) : ℂ)) * Complex.I) *
        Complex.exp ((-((t * Real.log (balancedIntervalValue p : ℝ) : ℝ) : ℂ)) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- Smooth head weights and prime tail second moments retain the arithmetic off-diagonal cost. -/
theorem integral_balancedHead_primeTail_sq_le {X y : ℕ} {A B : Finset (Fin X)}
    (hA : A ⊆ smoothRows X y) (hB : B ⊆ roughPrimeColumns X y)
    (r b : Fin X → ℂ) (hr : ∀ m ∈ A, ‖r m‖ ≤ 1) (hb : ∀ p ∈ B, ‖b p‖ ≤ 1)
    (U : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T,
      ‖balancedBlockDirichletPoly A r (U + t)‖ ^ (2 : ℕ) *
        ‖balancedBlockDirichletPoly B b (U + t)‖ ^ (2 : ℕ)) ≤
      (5 * Real.pi / 2) *
        (T * (A.card : ℝ) * B.card + 8 * (X : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := by
  have hc : ∀ p ∈ A ×ˢ B, ‖r p.1 * b p.2‖ ≤ 1 := by
    intro p hp
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (hr p.1 (mem_product.mp hp).1)
        (hb p.2 (mem_product.mp hp).2) (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have h := integral_balancedSmoothPrimePoly_shift_le hA hB (fun p => r p.1 * b p.2) hc U hT
  simpa only [balancedSmoothPrimePoly_mul, norm_mul, mul_pow] using h

private theorem continuous_balancedBlockDirichletPoly {X : ℕ} (A : Finset (Fin X)) (r : Fin X → ℂ) :
    Continuous (balancedBlockDirichletPoly A r) := by
  unfold balancedBlockDirichletPoly
  apply continuous_finsetSum
  intro m _
  fun_prop

/-- The smooth-head mass of a large prime tail is paid at the arithmetic mean-square scale. -/
theorem setIntegral_balancedHead_on_large_primeTail_le {X y : ℕ} {A B : Finset (Fin X)}
    (hA : A ⊆ smoothRows X y) (hB : B ⊆ roughPrimeColumns X y)
    (r b : Fin X → ℂ) (hr : ∀ m ∈ A, ‖r m‖ ≤ 1) (hb : ∀ p ∈ B, ‖b p‖ ≤ 1)
    (U : ℝ) {T V : ℝ} (hT : 0 < T) (hV : 0 < V) :
    (∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖balancedBlockDirichletPoly B b (U + t)‖},
      ‖balancedBlockDirichletPoly A r (U + t)‖ ^ (2 : ℕ)) ≤
      ((5 * Real.pi / 2) *
        (T * (A.card : ℝ) * B.card + 8 * (X : ℝ) ^ 2 * (A.card : ℝ) ^ 2)) / V ^ 2 := by
  let R (t : ℝ) := balancedBlockDirichletPoly A r (U + t)
  let Q (t : ℝ) := balancedBlockDirichletPoly B b (U + t)
  have hcR : Continuous R := (continuous_balancedBlockDirichletPoly A r).comp (continuous_const.add continuous_id)
  have hcQ : Continuous Q := (continuous_balancedBlockDirichletPoly B b).comp (continuous_const.add continuous_id)
  let g (t : ℝ) := ‖R t‖ ^ 2 * ‖Q t‖ ^ 2 / V ^ 2
  have hgc : Continuous g := ((hcR.norm.pow 2).mul (hcQ.norm.pow 2)).div_const _
  have hclosed : IsClosed {t | V ≤ ‖Q t‖} := isClosed_le continuous_const hcQ.norm
  have hmeas : MeasurableSet (Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}) :=
    measurableSet_Icc.inter hclosed.measurableSet
  have hcompact : IsCompact (Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}) := isCompact_Icc.inter_right hclosed
  have h1 : (∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}, ‖R t‖ ^ 2) ≤
      ∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}, g t := by
    apply setIntegral_mono_on ((hcR.norm.pow 2).continuousOn.integrableOn_compact hcompact)
      (hgc.continuousOn.integrableOn_compact hcompact) hmeas
    intro t ht
    dsimp only [g]
    apply (le_div_iff₀ (by positivity : 0 < V ^ 2)).mpr
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV.le ht.2 2) (sq_nonneg _)
  have h2 : (∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}, g t) ≤
      ∫ t in Set.Icc (-T) T, g t :=
    setIntegral_mono_set hgc.integrableOn_Icc (Filter.Eventually.of_forall fun t => by
      dsimp only [g]; positivity) (Filter.Eventually.of_forall Set.inter_subset_left)
  have h3 : (∫ t in Set.Icc (-T) T, g t) =
      (∫ t in Set.Icc (-T) T, ‖R t‖ ^ 2 * ‖Q t‖ ^ 2) / V ^ 2 := by
    dsimp only [g]
    rw [MeasureTheory.integral_div]
  have h4 := div_le_div_of_nonneg_right
    (integral_balancedHead_primeTail_sq_le hA hB r b hr hb U hT) (by positivity : 0 ≤ V ^ 2)
  exact h1.trans (h2.trans (h3.trans_le h4))


end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
