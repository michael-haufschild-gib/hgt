import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.LiouvilleOddWindowRefutationAndSelectiveFullPositivity
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Polynomial evaluation from its interval energy

Bonnet's recurrence controls every Legendre polynomial outside the unit interval.
Orthogonality turns this control into a degree-uniform reproducing-kernel estimate.
The leading coefficients retain the scale lost by monomial interpolation.
-/

open MeasureTheory Set
noncomputable section

namespace GaloisForLFunctions.ThetaCuspSections
open GaloisForLFunctions.SelectivePositivityAndThresholdLaws

/-- The leading coefficient of the Legendre polynomial of degree `n`. -/
def legendreLead : ℕ → ℝ
  | 0 => 1
  | n + 1 => (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * legendreLead n

theorem legendreLead_pos (n : ℕ) : 0 < legendreLead n := by
  induction n with
  | zero => norm_num [legendreLead]
  | succ n ih => simp only [legendreLead]; positivity

/-- On the positive exterior, consecutive Legendre polynomials increase. -/
theorem legP_nonneg_le_succ {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    0 ≤ legP n x ∧ legP n x ≤ legP (n + 1) x := by
  induction n with
  | zero => simpa only [legP_zero, legP_one] using And.intro (by norm_num : (0 : ℝ) ≤ 1) hx
  | succ n ih =>
    have hcur : 0 ≤ legP (n + 1) x := ih.1.trans ih.2
    refine ⟨hcur, ?_⟩
    have hb := legP_bonnet n x
    have hp := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 3)
      (mul_nonneg (sub_nonneg.mpr hx) hcur)
    have hd := mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
      (sub_nonneg.mpr ih.2)
    have hstep : ((n : ℝ) + 2) * (legP (n + 2) x - legP (n + 1) x) ≥ 0 := by
      nlinarith only [hb, hp, hd]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left
      (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mp hstep)

theorem legendreLead_mono : Monotone legendreLead := by
  apply monotone_nat_of_le_succ
  intro n
  rw [legendreLead]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc := (legendreLead_pos n).le
  have hr : 1 ≤ (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [hn]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hr hc

/-- Dropping the nonpositive term of Bonnet's recurrence gives the sharp leading scale. -/
theorem legP_le_lead_mul_pow {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    legP n x ≤ legendreLead n * x ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp only [legP_zero, legendreLead, pow_zero, mul_one, le_refl]
    · norm_num [legP_one, legendreLead]
    · have hprev := (legP_nonneg_le_succ hx n).1
      have hcur := ih (n + 1) (by omega)
      have hfactor : 0 ≤ (2 * (n : ℝ) + 3) * x := by positivity
      calc
        legP (n + 2) x ≤
            ((2 * (n : ℝ) + 3) * x * legP (n + 1) x) / ((n : ℝ) + 2) := by
              rw [legP_succ_succ]
              exact div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) (by positivity)
        _ ≤ ((2 * (n : ℝ) + 3) * x * (legendreLead (n + 1) * x ^ (n + 1))) /
            ((n : ℝ) + 2) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcur hfactor) (by positivity)
        _ = legendreLead (n + 2) * x ^ (n + 2) := by
              rw [legendreLead, pow_succ]
              push_cast
              ring

/-- The Legendre span of all degrees strictly below `N`. -/
def legendreSpan (N : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ (range fun j : Fin N => legP j)

/-- Multiplication by a monomial raises the Legendre cutoff by at most its degree. -/
theorem pow_mul_legP_mem_span (N r d : ℕ) (h : r + d < N) :
    (fun x : ℝ => x ^ r * legP d x) ∈ legendreSpan N := by
  induction r generalizing d with
  | zero =>
    simpa only [pow_zero, one_mul] using
      (Submodule.subset_span (Set.mem_range.mpr ⟨⟨d, by omega⟩, rfl⟩) :
        legP d ∈ legendreSpan N)
  | succ r ih =>
    cases d with
    | zero =>
      convert ih 1 (by omega) using 1
      funext x
      simp only [legP_zero, legP_one, pow_succ, mul_one]
    | succ d =>
      have hh := (legendreSpan N).add_mem
        ((legendreSpan N).smul_mem (((d : ℝ) + 2) / (2 * (d : ℝ) + 3))
          (ih (d + 2) (by omega)))
        ((legendreSpan N).smul_mem (((d : ℝ) + 1) / (2 * (d : ℝ) + 3))
          (ih d (by omega)))
      convert hh using 1
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
      have hd : 2 * (d : ℝ) + 3 ≠ 0 := by positivity
      field_simp
      linear_combination -(x ^ r * legP_bonnet d x)

/-- Every polynomial of degree below `N` belongs to the first `N` Legendre modes. -/
theorem polynomial_eval_mem_legendreSpan (N : ℕ) (p : Polynomial ℝ)
    (hp : p.degree < (N : WithBot ℕ)) :
    (fun x => p.eval x) ∈ legendreSpan N := by
  have hm (j : ℕ) (hj : j < N) : (fun x : ℝ => x ^ j) ∈ legendreSpan N := by
    simpa only [legP_zero, mul_one] using pow_mul_legP_mem_span N j 0 (by omega)
  have hc (j : ℕ) (hj : j ∈ p.support) : j < N := by
    have hjd : (j : WithBot ℕ) ≤ p.degree := Polynomial.le_degree_of_ne_zero
      (Polynomial.mem_support_iff.mp hj)
    exact_mod_cast hjd.trans_lt hp
  have hh := (legendreSpan N).sum_mem fun j hj =>
    (legendreSpan N).smul_mem (p.coeff j) (hm j (hc j hj))
  convert hh using 1
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Polynomial.eval_eq_sum

/-- Finite Legendre expansion with the same degree cutoff. -/
theorem polynomial_eval_eq_legendre_sum (N : ℕ) (p : Polynomial ℝ)
    (hp : p.degree < (N : WithBot ℕ)) :
    ∃ c : Fin N → ℝ, ∀ x, p.eval x = ∑ j, c j * legP j x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (polynomial_eval_mem_legendreSpan N p hp)
  refine ⟨c, fun x => ?_⟩
  have he := congrFun hc x
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he.symm

/-- The diagonal reproducing kernel for degrees strictly below `N`. -/
def legendreKernel (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j : Fin N, ((j : ℝ) + 1 / 2) * legP j x ^ 2

/-- Orthogonality gives the complete energy of a finite Legendre expansion. -/
theorem integral_legendre_sum_sq {N : ℕ} (c : Fin N → ℝ) :
    (∫ x in (-1 : ℝ)..1, (∑ j, c j * legP j x) ^ 2) =
      ∑ j, c j ^ 2 / ((j : ℝ) + 1 / 2) := by
  have hexp (x : ℝ) : (∑ j, c j * legP j x) ^ 2 =
      ∑ i, ∑ j, (c i * c j) * (legP i x * legP j x) := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [Finset.sum_eq_single i]
  · simp only [← sq, legP_sq_integral]
    have hi : (i : ℝ) + 1 / 2 ≠ 0 := by positivity
    have hi' : 2 * (i : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · intro j _ hji
    rw [legP_orthog (fun h => hji (Fin.ext h.symm)), mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Weighted Cauchy bounds evaluation by the full Legendre kernel. -/
theorem legendre_sum_sq_le_kernel {N : ℕ} (c : Fin N → ℝ) (x : ℝ) :
    (∑ j, c j * legP j x) ^ 2 ≤
      legendreKernel N x * ∫ u in (-1 : ℝ)..1, (∑ j, c j * legP j u) ^ 2 := by
  rw [integral_legendre_sum_sq, mul_comm]
  unfold legendreKernel
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro j _
    positivity
  · intro j _
    positivity
  · intro j _
    have hj : (j : ℝ) + 1 / 2 ≠ 0 := by positivity
    apply le_of_eq
    field_simp
    ring

/-- Polynomial evaluation is bounded by its interval energy at every degree. -/
theorem polynomial_sq_le_legendreKernel (N : ℕ) (p : Polynomial ℝ)
    (hp : p.degree < (N : WithBot ℕ)) (x : ℝ) :
    p.eval x ^ 2 ≤ legendreKernel N x * ∫ u in (-1 : ℝ)..1, p.eval u ^ 2 := by
  obtain ⟨c, hc⟩ := polynomial_eval_eq_legendre_sum N p hp
  simp_rw [hc]
  exact legendre_sum_sq_le_kernel c x

private theorem sum_even_powers_le {x : ℝ} (hx : 4 ≤ x) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), x ^ (2 * j)) ≤ 16 / 15 * x ^ (2 * n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have he : x ^ (2 * (n + 1)) = x ^ (2 * n) * x ^ 2 := by
      rw [Nat.mul_add, pow_add]
      norm_num
    have hx2 : 16 ≤ x ^ 2 := by nlinarith only [hx]
    have hp := mul_le_mul_of_nonneg_left hx2 (by positivity : 0 ≤ x ^ (2 * n))
    rw [he]
    nlinarith only [ih, hp]

/-- The exterior kernel is controlled by its top leading coefficient, uniformly in degree. -/
theorem legendreKernel_le {x : ℝ} (hx : 4 ≤ x) (n : ℕ) :
    legendreKernel (n + 1) x ≤
      16 / 15 * ((n : ℝ) + 1 / 2) * legendreLead n ^ 2 * x ^ (2 * n) := by
  unfold legendreKernel
  rw [Fin.sum_univ_eq_sum_range]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hsum : (∑ j ∈ Finset.range (n + 1), ((j : ℝ) + 1 / 2) * legP j x ^ 2) ≤
      ((n : ℝ) + 1 / 2) * legendreLead n ^ 2 *
        ∑ j ∈ Finset.range (n + 1), x ^ (2 * j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    have hw : (j : ℝ) + 1 / 2 ≤ (n : ℝ) + 1 / 2 :=
      add_le_add_right (by exact_mod_cast hjn) _
    have hP := pow_le_pow_left₀ (legP_nonneg_le_succ hx1 j).1
      (legP_le_lead_mul_pow hx1 j) 2
    have hC := pow_le_pow_left₀ (legendreLead_pos j).le (legendreLead_mono hjn) 2
    have hpow : (legendreLead j * x ^ j) ^ 2 = legendreLead j ^ 2 * x ^ (2 * j) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm j 2]
    rw [hpow] at hP
    have hP' : legP j x ^ 2 ≤ legendreLead n ^ 2 * x ^ (2 * j) :=
      hP.trans (mul_le_mul_of_nonneg_right hC (by positivity))
    calc
      ((j : ℝ) + 1 / 2) * legP j x ^ 2 ≤
          ((n : ℝ) + 1 / 2) * (legendreLead n ^ 2 * x ^ (2 * j)) :=
            mul_le_mul hw hP' (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hgeo := mul_le_mul_of_nonneg_left (sum_even_powers_le hx n)
    (by positivity : 0 ≤ ((n : ℝ) + 1 / 2) * legendreLead n ^ 2)
  exact hsum.trans (hgeo.trans_eq (by ring))

theorem legendreKernel_neg (N : ℕ) (x : ℝ) :
    legendreKernel N (-x) = legendreKernel N x := by
  unfold legendreKernel
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [legP_neg, mul_pow, ← pow_mul, Nat.mul_comm j.val 2, pow_mul]
  norm_num

/-- The exterior envelope is valid on both sides of the interval. -/
theorem legendreKernel_le_abs {x : ℝ} (hx : 4 ≤ |x|) (n : ℕ) :
    legendreKernel (n + 1) x ≤
      16 / 15 * ((n : ℝ) + 1 / 2) * legendreLead n ^ 2 * |x| ^ (2 * n) := by
  have hh := legendreKernel_le hx n
  by_cases hx0 : 0 ≤ x
  · simpa only [abs_of_nonneg hx0] using hh
  · simpa only [abs_of_neg (lt_of_not_ge hx0), legendreKernel_neg] using hh

#print axioms polynomial_sq_le_legendreKernel
#print axioms legendreKernel_le_abs

end GaloisForLFunctions.ThetaCuspSections
