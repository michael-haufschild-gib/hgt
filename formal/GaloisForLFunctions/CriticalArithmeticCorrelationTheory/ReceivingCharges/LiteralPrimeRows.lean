import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralPrimeIncidence
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.MangoldtKernelGram

/-!
# Literal prime rows and their own towers

Finite prime-band expansion preserves both signed kernels. The omitted
same-source multiplier towers have an explicit logarithmic charge bound.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open MeasureTheory Finset ArithmeticFunction
open GaloisForLFunctions
open CriticalArithmeticCorrelationTheory BezoutValuationIncidence
  CriticalScaleArithmeticRigidity ArithmeticCouplingTheory

/-- The omitted same-source prime towers retain their complete literal offset rows. -/
def literalTowerRow (P : Finset ℕ) (Y B : ℕ) (G : ℕ → ℝ)
    (T : ℕ → ℕ → ℕ) (f : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, ∑ i ∈ Icc 1 Y ×ˢ Icc 1 B,
    if p ∣ i.1 then (vonMangoldt i.1 / (i.1 : ℝ)) * f i.1 i.2 * G (T i.1 i.2) / p else 0

/-- Exact finite prime-band expansion separates a periodic unit row from its own prime towers. -/
theorem finite_prime_row_split (P : Finset ℕ) (Y B M n : ℕ) (s : ℝ)
    (G : ℕ → ℝ) (T : ℕ → ℕ → ℕ) (f : ℕ → ℕ → ℕ → ℝ)
    (b : ℕ → ℕ → ℕ) (z : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hsplit : ∀ p ∈ P, ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B,
      (vonMangoldt k / (k : ℝ)) * f k h n * G (T k h) *
        ((if p ∣ T k h then (1 : ℝ) else 0) - 1 / p) =
      unitMangoldtWeight p k * f k h n *
        (z p k h (n % M) * centeredResidue p (multiplierResidue p k (b p h)) n) -
      (if p ∣ k then (vonMangoldt k / (k : ℝ)) * f k h n * G (T k h) / p else 0)) :
    (∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) *
      ∑ h ∈ Icc 1 B, (G (T k h) * incidencePacket P (fun _ => s) (T k h)) * f k h n) =
      s * unitMangoldtKernelRow P Y B M b z f n -
        s * literalTowerRow P Y B G T (fun k h => f k h n) := by
  have he :
      (∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) *
        ∑ h ∈ Icc 1 B, (G (T k h) * incidencePacket P (fun _ => s) (T k h)) * f k h n) =
      ∑ i ∈ Icc 1 Y ×ˢ Icc 1 B,
        ((vonMangoldt i.1 / (i.1 : ℝ)) * f i.1 i.2 n) * G (T i.1 i.2) *
          incidencePacket P (fun _ => s) (T i.1 i.2) := by
    simp only [sum_product, mul_sum]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro h _
    ring
  rw [he, finite_prime_band_row]
  have hs :
      (∑ p ∈ P, ∑ i ∈ Icc 1 Y ×ˢ Icc 1 B,
        ((vonMangoldt i.1 / (i.1 : ℝ)) * f i.1 i.2 n) * G (T i.1 i.2) *
          ((if p ∣ T i.1 i.2 then (1 : ℝ) else 0) - 1 / p)) =
      unitMangoldtKernelRow P Y B M b z f n -
        literalTowerRow P Y B G T (fun k h => f k h n) := by
    unfold unitMangoldtKernelRow literalTowerRow
    rw [sum_product, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    exact hsplit p hp i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2
  rw [hs, mul_sub]

/-- The positive literal row keeps its exact periodic incidence and every same-source tower term. -/
theorem positive_literal_prime_row_split {P : Finset ℕ} {G : ℕ → ℝ} {M B : ℕ}
    (hG : Function.Periodic G M) (hp : ∀ p ∈ P, p.Prime) (hBP : ∀ p ∈ P, B < p)
    (φ : ℝ → ℝ) (c : ℝ) (N n : ℕ) (s : ℝ) :
    positiveLiteralUpwardRow φ c B N (fun j => G j * incidencePacket P (fun _ => s) j) n =
      s * unitMangoldtKernelRow P (N + B) B M (fun p h => p - h)
        (fun _ k h r => G (k * r + h)) (positiveLiteralUpwardKernel φ c N) n -
      s * literalTowerRow P (N + B) B G (fun k h => k * n + h)
        (fun k h => positiveLiteralUpwardKernel φ c N k h n) := by
  apply finite_prime_row_split
  intro p hpP k _ h hh
  exact positive_literal_incidence_split hG (hp p hpP) (mem_Icc.mp hh).1
    ((mem_Icc.mp hh).2.trans_lt (hBP p hpP)) φ c N

/-- Negative rows have the same exact split whenever the receiving index exceeds the offset strip. -/
theorem negative_literal_prime_row_split {P : Finset ℕ} {G : ℕ → ℝ} {M B n : ℕ}
    (hM : 0 < M) (hG : Function.Periodic G M) (hp : ∀ p ∈ P, p.Prime)
    (hBP : ∀ p ∈ P, B < p) (hn : B ≤ n)
    (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (s : ℝ) :
    negativeLiteralUpwardRow φ c B N (fun j => G j * incidencePacket P (fun _ => s) j) n =
      s * unitMangoldtKernelRow P (N + B) B M (fun _ h => h)
        (fun _ k h => negativePeriodicProfile G M k h) (negativeLiteralUpwardKernel φ c N) n -
      s * literalTowerRow P (N + B) B G (fun k h => k * n - h)
        (fun k h => negativeLiteralUpwardKernel φ c N k h n) := by
  apply finite_prime_row_split
  intro p hpP k hk h hh
  have hnkn : n ≤ k * n := by
    simpa only [one_mul] using Nat.mul_le_mul_right n (mem_Icc.mp hk).1
  exact negative_literal_incidence_split hM hG (hp p hpP) (mem_Icc.mp hk).1
    (mem_Icc.mp hh).1 ((mem_Icc.mp hh).2.trans_lt (hBP p hpP))
    (((mem_Icc.mp hh).2.trans hn).trans hnkn) φ c N

#print axioms positive_literal_prime_row_split
#print axioms negative_literal_prime_row_split

/-- Every same-source tower remainder is controlled uniformly in the receiving index. -/
theorem abs_literalTowerRow_le {P : Finset ℕ} {R Y B : ℕ}
    (hR : 0 < R) (hp : ∀ p ∈ P, p.Prime) (hRP : ∀ p ∈ P, R < p)
    (G : ℕ → ℝ) (T : ℕ → ℕ → ℕ) (f : ℕ → ℕ → ℝ)
    {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hG : ∀ j, |G j| ≤ V)
    (hf : ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, |f k h| ≤ U) :
    |literalTowerRow P Y B G T f| ≤
      (2 * (B : ℝ) * U * V / R) * ∑ p ∈ P, Real.log p / (p : ℝ) := by
  have he :
      (∑ p ∈ P, ∑ i ∈ Icc 1 Y ×ˢ Icc 1 B,
        if p ∣ i.1 then (vonMangoldt i.1 / (i.1 : ℝ)) * U * V / p else 0) =
      ((B : ℝ) * U * V) *
        ∑ p ∈ P, (1 / (p : ℝ)) *
          ∑ k ∈ Icc 1 Y, if p ∣ k then vonMangoldt k / (k : ℝ) else 0 := by
    simp only [sum_product, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_sum]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro k _
    split_ifs <;> ring
  calc
    _ ≤ ∑ p ∈ P, ∑ i ∈ Icc 1 Y ×ˢ Icc 1 B,
        if p ∣ i.1 then (vonMangoldt i.1 / (i.1 : ℝ)) * U * V / p else 0 := by
      unfold literalTowerRow
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
      intro p hpP
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
      intro i hi
      split_ifs
      · have hMangoldt : 0 ≤ vonMangoldt i.1 / (i.1 : ℝ) :=
          div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg i.1)
        rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hMangoldt,
          show |(p : ℝ)| = (p : ℝ) from abs_of_nonneg (Nat.cast_nonneg p)]
        exact div_le_div_of_nonneg_right
          (mul_le_mul
            (mul_le_mul_of_nonneg_left (hf i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2) hMangoldt)
            (hG _) (abs_nonneg _) (mul_nonneg hMangoldt hU)) (Nat.cast_nonneg p)
      · simp only [abs_zero, le_refl]
    _ = _ := he
    _ ≤ ((B : ℝ) * U * V) *
        ((2 / (R : ℝ)) * ∑ p ∈ P, Real.log p / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left (source_prime_tower_mass_le hR hp hRP Y)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg B) hU) hV)
    _ = _ := by ring

#print axioms abs_literalTowerRow_le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
