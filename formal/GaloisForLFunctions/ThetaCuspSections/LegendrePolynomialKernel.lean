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

@[positivity]
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
    exact nonneg_of_mul_nonneg_left hstep (by positivity)

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
    · simp only [legP_one, legendreLead, Nat.cast_zero, zero_mul, zero_add, div_self,
        one_mul, pow_one, le_refl]
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
  exact p.eval_eq_sum

/-- Finite Legendre expansion with the same degree cutoff. -/
theorem polynomial_eval_eq_legendre_sum (N : ℕ) (p : Polynomial ℝ)
    (hp : p.degree < (N : WithBot ℕ)) :
    ∃ c : Fin N → ℝ, ∀ x, p.eval x = ∑ j, c j * legP j x := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun.mp
    (polynomial_eval_mem_legendreSpan N p hp)
  refine ⟨c, fun x => ?_⟩
  have he := congrFun hc x
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he.symm

end GaloisForLFunctions.ThetaCuspSections
