import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PrimeBlockGram
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.AffineKernelMass

/-!
# Full Mangoldt covariance bounds for finite prime bands

Positive kernel mass and affine collisions control equal-prime blocks.
Periodic covariance retains every finite endpoint and proper-power error.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open Finset ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- The full unit-multiplier row, with finite offset and prime sets and exact periodic residues. -/
def unitMangoldtKernelRow (P : Finset ℕ) (Y B M : ℕ)
    (b : ℕ → ℕ → ℕ) (z : ℕ → ℕ → ℕ → ℕ → ℝ) (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ P ×ˢ (Icc 1 Y ×ˢ Icc 1 B), unitMangoldtWeight i.1 i.2.1 * f i.2.1 i.2.2 n *
    (z i.1 i.2.1 i.2.2 (n % M) * centeredResidue i.1
      (multiplierResidue i.1 i.2.1 (b i.1 i.2.2)) n)

/-- Prime-progression collision control gives the complete finite middle-row Gram estimate. -/
theorem exists_unit_mangoldt_kernel_Gram_le :
    ∃ p₀ : ℕ, 8 ≤ p₀ ∧ ∀ (P : Finset ℕ) (Y B M A Z : ℕ)
      (b : ℕ → ℕ → ℕ) (z : ℕ → ℕ → ℕ → ℕ → ℝ) (f : ℕ → ℕ → ℕ → ℝ)
      (H X : ℕ → ℕ) (U K V W : ℝ),
      1 ≤ A → A ≤ Z → 0 < M → 0 ≤ U → 0 ≤ K → 0 ≤ V → 0 ≤ W →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p₀ ≤ p) → (∀ p ∈ P, M.Coprime p) →
      (∀ p ∈ P, ∀ h ∈ Icc 1 B, p.Coprime (b p h)) →
      (∀ p ∈ P, ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, ∀ r ∈ range M, |z p k h r| ≤ V) →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, ∀ n ∈ Icc A Z, 0 ≤ f k h n) →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, ∀ n ∈ Icc A Z, |f k h n| ≤ U) →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, discreteVariation (f k h) A Z ≤ K) →
      (∀ n ∈ Icc A Z, 1 ≤ H n) →
      (∀ n ∈ Icc A Z, ∀ p ∈ P, p ^ 2 ≤ H n) →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, ∀ n ∈ Icc A Z,
        f k h n ≠ 0 → k ∈ Icc (H n) (X n)) →
      (∀ n ∈ Icc A Z, H n ≤ X n →
        Real.log (X n) - Real.log (H n) + mertensWindowConstant + 1 ≤ W) →
      (∑ n ∈ Icc A Z, unitMangoldtKernelRow P Y B M b z f n ^ 2 / (n : ℝ)) ≤
        (B : ℝ) ^ 2 * U ^ 2 * V ^ 2 *
          (∑ n ∈ Icc A Z, (∑ p ∈ P,
            (1027 * W ^ 2 / (p : ℝ) ^ 2 +
              576 * W * (H n : ℝ) ^ (-(7 / 16 : ℝ)) / p)) / (n : ℝ)) +
        (4 * (M : ℝ) * V ^ 2 * (2 * U ^ 2 + 2 * U * K) / A) *
          ((P.card : ℝ) * B * (Real.log Y + mertensWindowConstant + 1)) ^ 2 := by
  obtain ⟨p₀, hp₀, hcollision⟩ := exists_unit_mangoldt_collision_row_le
  refine ⟨p₀, hp₀, ?_⟩
  intro P Y B M A Z b z f H X U K V W hA hAZ hM hU hK hV hW
    hp hpp hMp hb hz hf0 hf hfv hH hpH hsupp hwidth
  have htotal (n : ℕ) (hn : n ∈ Icc A Z) (p : ℕ) (_hp : p ∈ P) :
      (∑ i ∈ Icc 1 Y ×ˢ Icc 1 B, unitMangoldtWeight p i.1 * f i.1 i.2 n) ≤
        (B : ℝ) * U * W :=
    unit_mangoldt_kernel_mass (hH n hn) (fun k h => f k h n) hU hW
      (fun k hk h hh => hf0 k hk h hh n hn)
      (fun k hk h hh => hf k hk h hh n hn)
      (fun k hk h hh => hsupp k hk h hh n hn) (hwidth n hn)
  have hrow (n : ℕ) (hn : n ∈ Icc A Z) (p : ℕ) (hpP : p ∈ P)
      (j : ℕ × ℕ) (hj : j ∈ Icc 1 Y ×ˢ Icc 1 B) :
      (∑ i ∈ Icc 1 Y ×ˢ Icc 1 B,
        if multiplierResidue p i.1 (b p i.2) ≡ multiplierResidue p j.1 (b p j.2) [MOD p]
        then unitMangoldtWeight p i.1 * f i.1 i.2 n else 0) ≤
        (1026 * ((B : ℝ) * U * W)) / p +
          576 * (B : ℝ) * U * (H n : ℝ) ^ (-(7 / 16 : ℝ)) := by
    exact (hcollision p (H n) (X n) Y B (hp p hpP) (hpp p hpP) (hpH n hn p hpP)
      (b p) (hb p hpP) (fun k h => f k h n) U W hU hW
      (fun k hk h hh => hf k hk h hh n hn)
      (fun k hk h hh => hsupp k hk h hh n hn) (hwidth n hn)
      j.1 j.2 (mem_product.mp hj).2).trans_eq (by ring)
  have h := periodic_prime_block_Gram_le P (Icc 1 Y ×ˢ Icc 1 B)
    (fun p i => multiplierResidue p i.1 (b p i.2))
    (fun p i => unitMangoldtWeight p i.1)
    (fun p i => z p i.1 i.2) (fun _ i => f i.1 i.2)
    hU hK hV hA hAZ hM hp hMp
    (fun p _ i _ => unitMangoldtWeight_nonneg p i.1)
    (fun p hpP i hi => hz p hpP i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2)
    (fun _ _ i hi => hf0 i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2)
    (fun _ _ i hi => hf i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2)
    (fun _ _ i hi => hfv i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2)
    (fun _ _ => (B : ℝ) * U * W) (fun _ _ => 1026 * ((B : ℝ) * U * W))
    (fun n _ => 576 * (B : ℝ) * U * (H n : ℝ) ^ (-(7 / 16 : ℝ)))
    (fun _ _ _ _ => by positivity) (fun _ _ _ _ => by positivity) htotal hrow
  change (∑ n ∈ Icc A Z, unitMangoldtKernelRow P Y B M b z f n ^ 2 / (n : ℝ)) ≤ _ at h
  have herr :
      (4 * (M : ℝ) * V ^ 2 * (2 * U ^ 2 + 2 * U * K) / A) *
        (∑ i ∈ P ×ˢ (Icc 1 Y ×ˢ Icc 1 B), |unitMangoldtWeight i.1 i.2.1|) ^ 2 ≤
      (4 * (M : ℝ) * V ^ 2 * (2 * U ^ 2 + 2 * U * K) / A) *
        ((P.card : ℝ) * B * (Real.log Y + mertensWindowConstant + 1)) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _)
      (unit_mangoldt_weight_sum_le P Y B) 2
  refine h.trans ((add_le_add (le_refl _) herr).trans_eq ?_)
  congr 1
  simp only [mul_sum]
  apply sum_congr rfl
  intro n _
  simp only [sum_div, mul_sum]
  apply sum_congr rfl
  intro p _
  ring

#print axioms exists_unit_mangoldt_kernel_Gram_le

/-- Terminal rows retain covariance averaging with the full coarse collision mass. -/
theorem unit_mangoldt_terminal_Gram_le (P : Finset ℕ) (Y B M A Z : ℕ)
    (b : ℕ → ℕ → ℕ) (z : ℕ → ℕ → ℕ → ℕ → ℝ) (f : ℕ → ℕ → ℕ → ℝ)
    (H X : ℕ → ℕ) (U K V W : ℝ)
    (hA : 1 ≤ A) (hAZ : A ≤ Z) (hM : 0 < M)
    (hU : 0 ≤ U) (hK : 0 ≤ K) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hp : ∀ p ∈ P, p.Prime) (hMp : ∀ p ∈ P, M.Coprime p)
    (hz : ∀ p ∈ P, ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, ∀ r ∈ range M, |z p k h r| ≤ V)
    (hf0 : ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, ∀ n ∈ Icc A Z, 0 ≤ f k h n)
    (hf : ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, ∀ n ∈ Icc A Z, |f k h n| ≤ U)
    (hfv : ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, discreteVariation (f k h) A Z ≤ K)
    (hH : ∀ n ∈ Icc A Z, 1 ≤ H n)
    (hsupp : ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, ∀ n ∈ Icc A Z,
      f k h n ≠ 0 → k ∈ Icc (H n) (X n))
    (hwidth : ∀ n ∈ Icc A Z, H n ≤ X n →
      Real.log (X n) - Real.log (H n) + mertensWindowConstant + 1 ≤ W) :
    (∑ n ∈ Icc A Z, unitMangoldtKernelRow P Y B M b z f n ^ 2 / (n : ℝ)) ≤
      (B : ℝ) ^ 2 * U ^ 2 * V ^ 2 * W ^ 2 *
        (∑ n ∈ Icc A Z, (∑ p ∈ P, (1 / (p : ℝ) ^ 2 + 1 / (p : ℝ))) / (n : ℝ)) +
      (4 * (M : ℝ) * V ^ 2 * (2 * U ^ 2 + 2 * U * K) / A) *
        ((P.card : ℝ) * B * (Real.log Y + mertensWindowConstant + 1)) ^ 2 := by
  have htotal (n : ℕ) (hn : n ∈ Icc A Z) (p : ℕ) (_hp : p ∈ P) :
      (∑ i ∈ Icc 1 Y ×ˢ Icc 1 B, unitMangoldtWeight p i.1 * f i.1 i.2 n) ≤
        (B : ℝ) * U * W :=
    unit_mangoldt_kernel_mass (hH n hn) (fun k h => f k h n) hU hW
      (fun k hk h hh => hf0 k hk h hh n hn)
      (fun k hk h hh => hf k hk h hh n hn)
      (fun k hk h hh => hsupp k hk h hh n hn) (hwidth n hn)
  have hrow (n : ℕ) (hn : n ∈ Icc A Z) (p : ℕ) (hpP : p ∈ P)
      (j : ℕ × ℕ) (_hj : j ∈ Icc 1 Y ×ˢ Icc 1 B) :
      (∑ i ∈ Icc 1 Y ×ˢ Icc 1 B,
        if multiplierResidue p i.1 (b p i.2) ≡ multiplierResidue p j.1 (b p j.2) [MOD p]
        then unitMangoldtWeight p i.1 * f i.1 i.2 n else 0) ≤
        (0 : ℝ) / p + (B : ℝ) * U * W := by
    rw [zero_div, zero_add]
    refine (sum_le_sum fun i hi => ?_).trans (htotal n hn p hpP)
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (unitMangoldtWeight_nonneg p i.1)
        (hf0 i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2 n hn)
  have h := periodic_prime_block_Gram_le P (Icc 1 Y ×ˢ Icc 1 B)
    (fun p i => multiplierResidue p i.1 (b p i.2))
    (fun p i => unitMangoldtWeight p i.1)
    (fun p i => z p i.1 i.2) (fun _ i => f i.1 i.2)
    hU hK hV hA hAZ hM hp hMp
    (fun p _ i _ => unitMangoldtWeight_nonneg p i.1)
    (fun p hpP i hi => hz p hpP i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2)
    (fun _ _ i hi => hf0 i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2)
    (fun _ _ i hi => hf i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2)
    (fun _ _ i hi => hfv i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2)
    (fun _ _ => (B : ℝ) * U * W) (fun _ _ => 0) (fun _ _ => (B : ℝ) * U * W)
    (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => by positivity) htotal hrow
  change (∑ n ∈ Icc A Z, unitMangoldtKernelRow P Y B M b z f n ^ 2 / (n : ℝ)) ≤ _ at h
  have herr :
      (4 * (M : ℝ) * V ^ 2 * (2 * U ^ 2 + 2 * U * K) / A) *
        (∑ i ∈ P ×ˢ (Icc 1 Y ×ˢ Icc 1 B), |unitMangoldtWeight i.1 i.2.1|) ^ 2 ≤
      (4 * (M : ℝ) * V ^ 2 * (2 * U ^ 2 + 2 * U * K) / A) *
        ((P.card : ℝ) * B * (Real.log Y + mertensWindowConstant + 1)) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _)
      (unit_mangoldt_weight_sum_le P Y B) 2
  refine h.trans ((add_le_add (le_refl _) herr).trans_eq ?_)
  congr 1
  simp only [mul_sum]
  apply sum_congr rfl
  intro n _
  simp only [sum_div, mul_sum]
  apply sum_congr rfl
  intro p _
  ring

#print axioms unit_mangoldt_terminal_Gram_le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
