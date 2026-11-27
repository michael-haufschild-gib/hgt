import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.HeatTrace
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Heat

/-! # An integer identity for coincident heat traces of logarithmic labels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic

open Finset Real
open _root_.HTGeometry (finiteGibbsPartition)

variable {I : Type*} [Fintype I]

def labelEnergy (a : I → ℕ+) (i : I) := energy (a i)
def labelProduct (a : I → ℕ+) : ℕ := ∏ i, (a i : ℕ)
def omitted (a : I → ℕ+) (i : I) : ℕ := by classical exact ∏ x ∈ univ.erase i, (a x : ℕ)
def direct (a : I → ℕ+) (j : ℕ) : ℕ := ∑ i, (a i : ℕ)^j
def reverse (a : I → ℕ+) (j : ℕ) : ℕ := ∑ i, (omitted a i)^j

theorem full_eq (a : I → ℕ+) (i : I) : labelProduct a = omitted a i*(a i : ℕ) := by
  classical
  exact (prod_erase_mul _ _ (mem_univ i)).symm

theorem product_pos (a : I → ℕ+) : 0<labelProduct a := prod_pos fun i _ => (a i).pos
theorem omitted_pos (a : I → ℕ+) (i : I) : 0<omitted a i := by
  classical
  exact prod_pos fun x _ => (a x).pos

private def geometric (a : I → ℕ+) := exp (meanEnergy (labelEnergy a))

private theorem geometric_pow [Nonempty I] (a : I → ℕ+) :
    (geometric a)^(Fintype.card I) = (labelProduct a : ℝ) := by
  have hn : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold geometric meanEnergy
  rw [← exp_nat_mul,show (Fintype.card I : ℝ)*((∑ i, labelEnergy a i)/Fintype.card I)=∑ i, labelEnergy a i by field_simp,
    exp_sum]
  simp only [labelEnergy,energy,exp_log (Nat.cast_pos.mpr (PNat.pos _)),labelProduct,Nat.cast_prod]

private theorem weight_eq (a : I → ℕ+) (i : I) :
    weight (centered (labelEnergy a)) i = geometric a/(a i : ℕ) := by
  rw [weight,centered,neg_sub,exp_sub,labelEnergy,energy,exp_log (Nat.cast_pos.mpr (a i).pos)]
  rfl

private theorem scaled_direct (a : I → ℕ+) (j : ℕ) :
    (geometric a)^j*moment (fun i => (weight (centered (labelEnergy a)) i)⁻¹) j=(direct a j : ℝ) := by
  have g : geometric a ≠ 0 := (exp_pos (meanEnergy (labelEnergy a))).ne'
  have read (i : I) : geometric a*(weight (centered (labelEnergy a)) i)⁻¹ = (a i : ℕ) := by
    rw [weight_eq,inv_div]
    field_simp [g]
  simp only [moment,mul_sum,← mul_pow,read,direct,Nat.cast_sum,Nat.cast_pow]

private theorem scaled_reverse (a : I → ℕ+) (j : ℕ) :
    (labelProduct a : ℝ)^j*moment (weight (centered (labelEnergy a))) j=(geometric a)^j*(reverse a j : ℝ) := by
  have read (i : I) : (labelProduct a : ℝ)*weight (centered (labelEnergy a)) i = geometric a*(omitted a i : ℝ) := by
    rw [weight_eq,full_eq a i,Nat.cast_mul]
    have hn : (↑(a i : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (a i).ne_zero
    field_simp
  simp only [moment,reverse,Nat.cast_sum,Nat.cast_pow,mul_sum,← mul_pow,read]

/-- Clearing denominators and raising to the dimension retains an equivalence because
the geometric mean, the label product and both power sums are nonnegative. -/
theorem trace_iff_integer [Nonempty I] (a : I → ℕ+) (j : ℕ) :
    finiteGibbsPartition (j : ℝ) (centered (labelEnergy a)) =
      finiteGibbsPartition (-(j : ℝ)) (centered (labelEnergy a)) ↔
    (labelProduct a)^(2*j)*(reverse a j)^(Fintype.card I) =
      (labelProduct a)^(Fintype.card I*j)*(direct a j)^(Fintype.card I) := by
  let w := weight (centered (labelEnergy a))
  let A : ℝ := labelProduct a
  let g := geometric a
  let n := Fintype.card I
  have hp : 0<A := Nat.cast_pos.mpr (product_pos a)
  have hg : 0<g := exp_pos _
  have eq₁ := scaled_reverse a j
  have eq₂ := scaled_direct a j
  change A^j*moment w j=g^j*(reverse a j : ℝ) at eq₁
  change g^j*moment (fun i => (w i)⁻¹) j=(direct a j : ℝ) at eq₂
  have h : moment w j = moment (fun i => (w i)⁻¹) j ↔
      g^j*(g^j*(reverse a j : ℝ))=A^j*(direct a j : ℝ) := by
    rw [← eq₁,← eq₂,mul_left_comm (g^j)]
    exact (mul_right_injective₀ (pow_pos hp j).ne').eq_iff.trans
      (mul_right_injective₀ (pow_pos hg j).ne').eq_iff |>.symm
  have pow_g : (g^j)^n = A^j := by rw [← pow_mul,Nat.mul_comm,pow_mul]; exact congrArg (·^j) (geometric_pow a)
  have left : (g^j*(g^j*(reverse a j : ℝ)))^n = A^(2*j)*(reverse a j : ℝ)^n := by
    simp only [mul_pow,pow_g,two_mul,pow_add]; ring
  have right : (A^j*(direct a j : ℝ))^n = A^(n*j)*(direct a j : ℝ)^n := by rw [mul_pow,← pow_mul,Nat.mul_comm j n]
  have he : weight (centered (labelEnergy a)) = fun i => exp (-(centered (labelEnergy a) i)) := rfl
  have flip : (fun i => (w i)⁻¹) = fun i => exp (centered (labelEnergy a) i) := by
    funext i; change (exp (-_))⁻¹ = _; rw [exp_neg,inv_inv]
  calc _ ↔ moment w j=moment (fun i => (w i)⁻¹) j := by
             rw [partition_negative,partition_moment,partition_moment,flip]
             simp only [neg_neg,w,he]
       _ ↔ _ := h
       _ ↔ (g^j*(g^j*(reverse a j : ℝ)))^n=(A^j*(direct a j : ℝ))^n :=
               (pow_left_inj₀ (mul_nonneg (pow_nonneg hg.le j) (mul_nonneg (pow_nonneg hg.le j) (Nat.cast_nonneg _)))
                (mul_nonneg (pow_nonneg hp.le j) (Nat.cast_nonneg _)) Fintype.card_ne_zero).symm
       _ ↔ _ := by rw [left,right]; unfold A n; norm_cast

#print axioms trace_iff_integer

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic
