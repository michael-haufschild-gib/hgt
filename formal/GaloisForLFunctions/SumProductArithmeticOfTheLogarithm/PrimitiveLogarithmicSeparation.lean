import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PrimitiveProductCollisionCosts
import GaloisForLFunctions.HTGeometry.LogFrequencySeparation

/-!
# Logarithmic separation at the reduced ratio height

The finite support invariant `primitiveSupportHeight` is the largest
numerator of an actual reduced ratio, with lower bound one. Cancelling
the gcd preserves each logarithmic difference, so distinct positive
frequencies have logarithmic gap at least its reciprocal.

The same invariant bounds the primitive product-collision kernel. It is
unchanged by a common positive integer dilation of the support.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

/-- The largest reduced numerator in the head's actual ratio set. -/
def primitiveSupportHeight (A : Finset ℕ) : ℕ :=
  max 1 ((A ×ˢ A).sup fun p => p.1 / Nat.gcd p.1 p.2)

theorem primitiveSupportHeight_pos (A : Finset ℕ) : 0 < primitiveSupportHeight A :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem div_gcd_le_primitiveSupportHeight {A : Finset ℕ} {m n : ℕ}
    (hm : m ∈ A) (hn : n ∈ A) : m / Nat.gcd m n ≤ primitiveSupportHeight A := by
  unfold primitiveSupportHeight
  have hmem : (m,n) ∈ A ×ˢ A := mem_product.mpr ⟨hm, hn⟩
  exact (Finset.le_sup (f := fun p : ℕ × ℕ => p.1 / Nat.gcd p.1 p.2) hmem).trans
    (le_max_right _ _)

/-- Reduced ratios never exceed the original support cutoff. -/
theorem primitiveSupportHeight_le {A : Finset ℕ} {M : ℕ} (hM : 1 ≤ M)
    (hA : ∀ m ∈ A, m ≤ M) : primitiveSupportHeight A ≤ M := by
  apply max_le hM
  apply Finset.sup_le
  intro p hp
  exact (Nat.div_le_self p.1 _).trans (hA p.1 (mem_product.mp hp).1)

/-- Cancelling the gcd preserves the logarithmic difference exactly. -/
theorem log_sub_log_eq_primitive {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Real.log (m : ℝ) - Real.log (n : ℝ) =
      Real.log (m / Nat.gcd m n : ℕ) - Real.log (n / Nat.gcd m n : ℕ) := by
  let g := Nat.gcd m n
  have hg : 0 < g := Nat.gcd_pos_of_pos_left n hm
  have hmf : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
  have hnf : g * (n / g) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)
  have hmg : 0 < m / g := by nlinarith only [hmf, hm]
  have hng : 0 < n / g := by nlinarith only [hnf, hn]
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hmR : ((m / g : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmg.ne'
  have hnR : ((n / g : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hng.ne'
  have hem : Real.log (m : ℝ) = Real.log (g : ℝ) + Real.log (m / g : ℕ) := by
    conv_lhs => rw [← hmf]
    rw [Nat.cast_mul, Real.log_mul hgR hmR]
  have hen : Real.log (n : ℝ) = Real.log (g : ℝ) + Real.log (n / g : ℕ) := by
    conv_lhs => rw [← hnf]
    rw [Nat.cast_mul, Real.log_mul hgR hnR]
  rw [hem, hen]
  dsimp only [g]
  ring

/-- Integer separation is governed by reduced ratios rather than absolute row size. -/
theorem inv_primitiveSupportHeight_le_abs_log_sub_log {A : Finset ℕ}
    (hA : ∀ m ∈ A, 0 < m) {m n : ℕ} (hm : m ∈ A) (hn : n ∈ A) (hmn : m ≠ n) :
    (primitiveSupportHeight A : ℝ)⁻¹ ≤ |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  let g := Nat.gcd m n
  have hmf : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
  have hnf : g * (n / g) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)
  have hmg : 0 < m / g := by nlinarith only [hmf, hA m hm]
  have hng : 0 < n / g := by nlinarith only [hnf, hA n hn]
  have hne : m / g ≠ n / g := by
    intro he
    apply hmn
    rw [← hmf, ← hnf, he]
  have hmH : m / g ≤ primitiveSupportHeight A := div_gcd_le_primitiveSupportHeight hm hn
  have hnH : n / g ≤ primitiveSupportHeight A := by
    dsimp only [g]
    rw [Nat.gcd_comm]
    exact div_gcd_le_primitiveSupportHeight hn hm
  rw [log_sub_log_eq_primitive (hA m hm) (hA n hn)]
  exact HTGeometry.inv_le_abs_log_sub_log_of_le hmg hng hne hmH hnH

/-- The same ratio height bounds the primitive product-collision kernel. -/
theorem primitiveProductCost_le_supportHeight {A : Finset ℕ} {m n : ℕ}
    (hm : m ∈ A) (hn : n ∈ A) (Z : ℕ) :
    primitiveProductCost m n Z ≤ 2 * (Z : ℝ) * (Z + primitiveSupportHeight A) := by
  have hmH : ((m / Nat.gcd m n : ℕ) : ℝ) ≤ primitiveSupportHeight A := by
    exact_mod_cast div_gcd_le_primitiveSupportHeight hm hn
  have hnH : ((n / Nat.gcd m n : ℕ) : ℝ) ≤ primitiveSupportHeight A := by
    rw [Nat.gcd_comm]
    exact_mod_cast div_gcd_le_primitiveSupportHeight hn hm
  unfold primitiveProductCost
  have h := mul_le_mul_of_nonneg_left (add_le_add hmH hnH) (Nat.cast_nonneg Z : (0 : ℝ) ≤ Z)
  nlinarith only [h]

/-- A common dilation leaves the actual reduced ratio height unchanged. -/
theorem primitiveSupportHeight_image_mul (A : Finset ℕ) {a : ℕ} (ha : 0 < a) :
    primitiveSupportHeight (A.image (a * ·)) = primitiveSupportHeight A := by
  have hratio (m n : ℕ) : (a * m) / Nat.gcd (a * m) (a * n) = m / Nat.gcd m n := by
    rw [Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ ha]
  unfold primitiveSupportHeight
  apply congrArg (max 1)
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨u,v⟩ hp
    obtain ⟨m, hm, rfl⟩ := mem_image.mp (mem_product.mp hp).1
    obtain ⟨n, hn, rfl⟩ := mem_image.mp (mem_product.mp hp).2
    rw [hratio]
    have hmem : (m,n) ∈ A ×ˢ A := mem_product.mpr ⟨hm, hn⟩
    exact Finset.le_sup (f := fun p : ℕ × ℕ => p.1 / Nat.gcd p.1 p.2) hmem
  · apply Finset.sup_le
    rintro ⟨m,n⟩ hp
    have hmem : (a*m,a*n) ∈ A.image (a * ·) ×ˢ A.image (a * ·) := mem_product.mpr
      ⟨mem_image_of_mem (a * ·) (mem_product.mp hp).1,
        mem_image_of_mem (a * ·) (mem_product.mp hp).2⟩
    have h := le_sup (f := fun p : ℕ × ℕ => p.1 / Nat.gcd p.1 p.2) hmem
    simpa only [hratio] using h

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
