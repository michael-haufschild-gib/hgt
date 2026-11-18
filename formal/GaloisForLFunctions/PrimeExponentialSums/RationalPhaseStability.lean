import GaloisForLFunctions.PrimeExponentialSums.PrimeSumsByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Frequency width in the rational-approximation error

Gou's Lemma 2.1 (arXiv:2610.22345) transfers estimates from a rational
phase to a nearby real phase. Removing a common phase first pays only for
the width of a block. For positive coefficients at a resonance, taking real
parts makes the loss quadratic in frequency displacement.
-/

noncomputable section
open Finset Complex GaloisForLFunctions.LogarithmicChowla

namespace GaloisForLFunctions.PrimeExponentialSums.PhaseStability

variable {ι : Type*}

/-- The frequencies may be prime indices, reciprocal phases, or any real samples. -/
def sumAt (s : Finset ι) (w : ι → ℂ) (f : ι → ℝ) (x : ℝ) : ℂ :=
  ∑ i ∈ s, w i * ex (f i*x)

/-- A translation of all frequencies contributes only a common phase. -/
theorem recenter (s : Finset ι) (w : ι → ℂ) (f : ι → ℝ) (c x : ℝ) :
    sumAt s w f x = ex (c*x) * sumAt s w (fun i => f i-c) x := by
  rw [sumAt, sumAt, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [show f i*x = c*x+(f i-c)*x by ring, ex_add]
  ring

/-- Complex-valued transfer with the full weighted first moment. -/
theorem transfer (s : Finset ι) (w : ι → ℂ) (f : ι → ℝ) (x y : ℝ) :
    ‖sumAt s w f x - sumAt s w f y‖ ≤
      (2*Real.pi*|x-y|) * ∑ i ∈ s, ‖w i‖ * |f i| := by
  rw [sumAt, sumAt, ← sum_sub_distrib, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [← mul_sub, norm_mul]
  have he := norm_ex_add_sub_le (f i*y) (f i*(x-y))
  rw [show f i*y + f i*(x-y) = f i*x by ring, abs_mul] at he
  exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (by ring)

/-- The amplitude transfer is insensitive to any common frequency offset. -/
theorem centered_transfer (s : Finset ι) (w : ι → ℂ) (f : ι → ℝ) (c x y : ℝ) :
    |‖sumAt s w f x‖ - ‖sumAt s w f y‖| ≤
      (2*Real.pi*|x-y|) * ∑ i ∈ s, ‖w i‖ * |f i-c| := by
  rw [recenter s w f c x, recenter s w f c y, norm_mul, norm_mul, norm_ex, norm_ex,
    one_mul, one_mul]
  exact (abs_norm_sub_norm_le _ _).trans (transfer _ _ _ _ _)

/-- On any frequency interval the first moment can be replaced by half its diameter. -/
theorem interval_transfer (s : Finset ι) (w : ι → ℂ) (f : ι → ℝ) (a b x y : ℝ)
    (hs : ∀ i ∈ s, f i ∈ Set.Icc a b) :
    |‖sumAt s w f x‖ - ‖sumAt s w f y‖| ≤
      Real.pi * |x-y| * (b-a) * ∑ i ∈ s, ‖w i‖ := by
  refine (centered_transfer s w f ((a+b)/2) x y).trans ?_
  have hb := sum_le_sum (s := s) (fun i hi =>
    mul_le_mul_of_nonneg_left (show |f i-(a+b)/2| ≤ (b-a)/2 from
      abs_le.mpr ⟨by linarith only [(hs i hi).1], by linarith only [(hs i hi).2]⟩) (norm_nonneg (w i)))
  rw [← Finset.sum_mul] at hb
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2*Real.pi*|x-y|)).trans_eq (by ring)

/-- At a rational major arc the original complex sum has error at most 2πN/q,
with every coefficient of norm at most one, regardless of multiplicativity. -/
theorem rational_transfer (N q : ℕ+) (a : ℤ) (x : ℝ) (w : ℕ → ℂ)
    (hw : ∀ n ∈ Icc 1 (N : ℕ), ‖w n‖ ≤ 1)
    (hx : |x - (a : ℝ)/q| ≤ 1 / ((q : ℝ)*N)) :
    ‖sumAt (Icc 1 (N : ℕ)) w Nat.cast x -
      sumAt (Icc 1 (N : ℕ)) w Nat.cast ((a : ℝ)/q)‖ ≤ 2*Real.pi*N/q := by
  have hm : (∑ n ∈ Icc 1 (N : ℕ), ‖w n‖ * |(n : ℝ)|) ≤ (N : ℝ)^2 := by
    calc
      _ ≤ ∑ _n ∈ Icc 1 (N : ℕ), (N : ℝ) := by
        apply sum_le_sum
        intro n hn
        rw [abs_of_nonneg (Nat.cast_nonneg n)]
        calc ‖w n‖ * n ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right (hw n hn) (Nat.cast_nonneg _)
             _ ≤ N := by simpa using (show (n : ℝ) ≤ N by exact_mod_cast (mem_Icc.mp hn).2)
      _ = _ := by simp [sq]
  refine (transfer _ _ _ _ _).trans ?_
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast q.pos.ne'
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.pos.ne'
  calc
    _ ≤ (2*Real.pi*(1/((q : ℝ)*N))) * (N : ℝ)^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hx (by positivity)) hm
        (sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)) (by positivity)
    _ = _ := by field_simp

/-- At zero phase the loss of coherent mass is bounded by the centered second moment. -/
theorem coherent_loss (s : Finset ι) (w : ι → NNReal) (f : ι → ℝ) (c x : ℝ) :
    (∑ i ∈ s, (w i : ℝ)) - ‖sumAt s (fun i => ((w i : ℝ) : ℂ)) f x‖ ≤
      2*Real.pi^2*x^2 * ∑ i ∈ s, (w i : ℝ) * (f i-c)^2 := by
  rw [recenter _ _ f c x, norm_mul, norm_ex, one_mul]
  have hr := Complex.re_le_norm (sumAt s (fun i => ((w i : ℝ) : ℂ)) (fun i => f i-c) x)
  refine (sub_le_sub_left hr _).trans ?_
  simp only [sumAt, re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ex_re]
  rw [← sum_sub_distrib, mul_sum]
  apply sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left
    (Real.one_sub_sq_div_two_le_cos (x := 2*Real.pi*((f i-c)*x))) (w i).property
  nlinarith only [h]

end GaloisForLFunctions.PrimeExponentialSums.PhaseStability

#print axioms GaloisForLFunctions.PrimeExponentialSums.PhaseStability.recenter
#print axioms GaloisForLFunctions.PrimeExponentialSums.PhaseStability.transfer
#print axioms GaloisForLFunctions.PrimeExponentialSums.PhaseStability.centered_transfer
#print axioms GaloisForLFunctions.PrimeExponentialSums.PhaseStability.interval_transfer
#print axioms GaloisForLFunctions.PrimeExponentialSums.PhaseStability.rational_transfer
#print axioms GaloisForLFunctions.PrimeExponentialSums.PhaseStability.coherent_loss
