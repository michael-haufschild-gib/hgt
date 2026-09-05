import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Models

/-!
# Quantitative loss under reversal

Products of normalized window increments satisfy a degree-times-variation
Lipschitz bound. Orienting a probe by its net displacement compares its absolute
response with the monotone absolute-gap probe, with defect bounded by degree
times coefficient budget times lost net displacement.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Finset

theorem normalized_window_bound {n : ℕ} (W : Finset (Fin n)) (g : Fin n → ℝ) :
    |windowValue W (normalizeProbe g)| ≤ 1 :=
  (windowValue_bound W _).trans (normalizeProbe_budget g)

theorem windowValue_difference_bound {n : ℕ} (W : Finset (Fin n)) (g h : Fin n → ℝ) :
    |windowValue W g - windowValue W h| ≤ variation (g-h) := by
  simpa only [windowValue, sum_sub_distrib, Pi.sub_apply] using windowValue_bound W (g-h)

theorem normalized_window_product_difference {n r : ℕ} (D : Fin r → Finset (Fin n))
    (s : Finset (Fin r)) (g h : Fin n → ℝ) :
    |(∏ j ∈ s, windowValue (D j) (normalizeProbe g)) -
      (∏ j ∈ s, windowValue (D j) (normalizeProbe h))| ≤
      (s.card : ℝ) * variation (normalizeProbe g - normalizeProbe h) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
    let A := windowValue (D i) (normalizeProbe g)
    let B := windowValue (D i) (normalizeProbe h)
    let P := ∏ j ∈ s, windowValue (D j) (normalizeProbe g)
    let Q := ∏ j ∈ s, windowValue (D j) (normalizeProbe h)
    let d := variation (normalizeProbe g - normalizeProbe h)
    have hA : |A| ≤ 1 := normalized_window_bound (D i) g
    have hQ : |Q| ≤ 1 := by
      dsimp [Q]
      rw [Finset.abs_prod]
      exact prod_le_one (fun j _ => abs_nonneg _) (fun j _ => normalized_window_bound (D j) h)
    have hAB : |A-B| ≤ d := windowValue_difference_bound (D i) _ _
    change |A*P-B*Q| ≤ ((s.card : ℝ)+1)*d
    calc
      _ = |A*(P-Q)+(A-B)*Q| := by congr 1; ring
      _ ≤ |A*(P-Q)|+|(A-B)*Q| := abs_add_le _ _
      _ = |A| * |P-Q|+|A-B| * |Q| := by rw [abs_mul,abs_mul]
      _ ≤ 1*((s.card : ℝ)*d)+d*1 := add_le_add
        (mul_le_mul hA ih (abs_nonneg _) (by positivity))
        (mul_le_mul hAB hQ (abs_nonneg _) (variation_nonneg _))
      _ = _ := by ring

theorem normalized_family_difference {n r m : ℕ}
    (D : Fin m → Fin r → Finset (Fin n)) (c : Fin m → ℝ) (g h : Fin n → ℝ) :
    |familyValue D c (normalizeProbe g) - familyValue D c (normalizeProbe h)| ≤
      (r : ℝ) * coefficientBudget c * variation (normalizeProbe g - normalizeProbe h) := by
  unfold familyValue
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j, |c j * diagramValue (D j) (normalizeProbe g) -
      c j * diagramValue (D j) (normalizeProbe h)| := abs_sum_le_sum_abs _ _
    _ = ∑ j, |c j| * |diagramValue (D j) (normalizeProbe g)-
      diagramValue (D j) (normalizeProbe h)| := by simp only [← mul_sub, abs_mul]
    _ ≤ ∑ j, |c j| * ((r : ℝ) * variation (normalizeProbe g - normalizeProbe h)) := by
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [diagramValue,card_univ,Fintype.card_fin] using
        normalized_window_product_difference (D j) univ g h
    _ = _ := by rw [← sum_mul]; unfold coefficientBudget; ring

def monotoneProbe {n : ℕ} (g : Fin n → ℝ) : Fin n → ℝ :=
  fun i => |normalizeProbe g i|

def displacement {n : ℕ} (g : Fin n → ℝ) : ℝ := ∑ i, g i

theorem normalizeProbe_abs {n : ℕ} (g : Fin n → ℝ) :
    normalizeProbe (fun i => |g i|) = monotoneProbe g := by
  funext i
  have hd : 0 ≤ max 1 (variation g) := le_trans (by positivity) (le_max_left _ _)
  have hv : variation (fun i => |g i|) = variation g := by simp only [variation,abs_abs]
  simp only [normalizeProbe,monotoneProbe,hv,abs_div,abs_of_nonneg hd]

theorem normalizeProbe_neg {n : ℕ} (g : Fin n → ℝ) :
    normalizeProbe (-g) = -normalizeProbe g := by
  funext i
  simp [normalizeProbe,variation,neg_div]

theorem monotoneProbe_budget {n : ℕ} (g : Fin n → ℝ) : variation (monotoneProbe g) ≤ 1 := by
  simpa only [variation,monotoneProbe,abs_abs] using normalizeProbe_budget g

theorem monotoneProbe_distance {n : ℕ} (g : Fin n → ℝ) :
    variation (normalizeProbe g-monotoneProbe g) =
      variation (normalizeProbe g)-displacement (normalizeProbe g) := by
  unfold variation displacement
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  dsimp [monotoneProbe]
  rw [abs_of_nonpos (sub_nonpos.mpr (le_abs_self _))]
  ring

theorem familyValue_neg {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) :
    familyValue D c (-g) = (-1 : ℝ)^r * familyValue D c g := by
  simp only [familyValue,diagramValue,windowValue,Pi.neg_apply,sum_neg_distrib,prod_neg,
    card_univ,Fintype.card_fin,mul_sum]
  apply sum_congr rfl
  intro j _
  ring

theorem familyValue_neg_abs {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) : |familyValue D c (-g)| = |familyValue D c g| := by
  rw [familyValue_neg,abs_mul,abs_pow]
  simp

theorem family_reversal_defect {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) :
    |familyValue D c (normalizeProbe g)| ≤ |familyValue D c (monotoneProbe g)| +
      (r : ℝ)*coefficientBudget c*(1-|displacement (normalizeProbe g)|) := by
  have hc : 0 ≤ (r : ℝ)*coefficientBudget c := by
    unfold coefficientBudget; positivity
  have h (h : Fin n → ℝ) :
      |familyValue D c (normalizeProbe h)| ≤ |familyValue D c (monotoneProbe h)| +
        (r : ℝ)*coefficientBudget c*(1-displacement (normalizeProbe h)) := by
    have hb := normalized_family_difference D c h (fun i => |h i|)
    rw [normalizeProbe_abs,monotoneProbe_distance] at hb
    have ha := abs_sub_abs_le_abs_sub (familyValue D c (normalizeProbe h))
      (familyValue D c (monotoneProbe h))
    have hv := normalizeProbe_budget h
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hv (displacement (normalizeProbe h))) hc
    linarith
  by_cases hs : 0 ≤ displacement (normalizeProbe g)
  · simpa only [abs_of_nonneg hs] using h g
  · have hh := h (-g)
    rw [normalizeProbe_neg,familyValue_neg_abs] at hh
    have hm : monotoneProbe (-g) = monotoneProbe g := by
      funext i
      simp only [monotoneProbe,normalizeProbe_neg,Pi.neg_apply,abs_neg]
    rw [hm] at hh
    have hd : displacement (-normalizeProbe g) = -displacement (normalizeProbe g) := by
      simp only [displacement,Pi.neg_apply,sum_neg_distrib]
    rw [hd] at hh
    rw [abs_of_neg (lt_of_not_ge hs)]
    exact hh


end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
