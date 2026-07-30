import GaloisForLFunctions.RHTower.FiniteSuperzetaFredholmLogDerivativeUniversalityLaw
import GaloisForLFunctions.RHTower.FredholmDeterminantEuler

/-!
# Finite-index Euler-head Fredholm-response universality

The cardinality-corrected superzeta--Fredholm response law is intrinsic to an arbitrary finite
index type, not to a chosen `Fin n` presentation.  Applying it to the subtype of members of a
finite prime set gives one finite-dimensional characteristic determinant with two exact faces:
its value at pencil parameter one is the finite Euler head, while its logarithmic derivative is
the additive prime resolvent response.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- The finite superzeta--Fredholm response law is intrinsic to every finite index type. -/
theorem finiteIndexedResolventValue_eq_fredholmDet1_logDeriv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → ℂ) (R : ℝ)
    (hR : R * HilbertSchmidt.hsNorm (HilbertSchmidt.diagMul r) < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) R) :
    (∑ i, (1 - z * r i)⁻¹) =
      (Fintype.card ι : ℂ) - z * logDeriv
        (fun w => HilbertSchmidt.fredholmDet1 (HilbertSchmidt.diagMul r) w) z := by
  have hg : ∀ i ∉ (Finset.univ : Finset ι), r i = 0 := by simp
  have hHS : HilbertSchmidt.IsHS (HilbertSchmidt.diagMul r) :=
    HilbertSchmidt.isHS_diagMul r Finset.univ hg
  have hzr : ‖z‖ < R := by rwa [mem_ball_zero_iff] at hz
  have hzM : ‖z‖ * HilbertSchmidt.hsNorm (HilbertSchmidt.diagMul r) < 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hzr.le
        (HilbertSchmidt.hsNorm_nonneg _)) hR
  have hfac : ∀ i ∈ (Finset.univ : Finset ι), ‖z * r i‖ < 1 := by
    intro i hi
    rw [norm_mul]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left
        (HilbertSchmidt.norm_le_hsNorm_diagMul r Finset.univ hg hi)
        (norm_nonneg z)) hzM
  have hlog := HilbertSchmidt.logDeriv_fredholmDet1 hHS R hR z hz
  have hres := HilbertSchmidt.resolventTrace_diagMul r Finset.univ hg z hfac
  have htr := HilbertSchmidt.tsum_diagMul_diag r Finset.univ hg
  rw [hres, HilbertSchmidt.hsTraceDiag, htr] at hlog
  rw [hlog]
  have hterm : ∀ i : ι,
      (1 - z * r i)⁻¹ = 1 + z * (r i + z * r i ^ 2 / (1 - z * r i)) := by
    intro i
    have hden : 1 - z * r i ≠ 0 := by
      intro h
      have hi := hfac i (Finset.mem_univ i)
      have hone : z * r i = 1 := by linear_combination -h
      rw [hone, norm_one] at hi
      exact lt_irrefl 1 hi
    rw [inv_eq_one_div]
    field_simp [hden]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The intrinsic finite-prime diagonal determinant is the Euler head at pencil value one. -/
theorem finitePrimeFredholmDet1_eq_eulerHeadAnchor
    (P : Finset ℕ) (s : ℂ) (R : ℝ)
    (hR : R * HilbertSchmidt.hsNorm
      (HilbertSchmidt.diagMul (fun p : P => (p.1 : ℂ) ^ (-s))) < 1)
    (h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R) :
    HilbertSchmidt.fredholmDet1
        (HilbertSchmidt.diagMul (fun p : P => (p.1 : ℂ) ^ (-s))) 1 =
      RHTower.eulerHeadAnchor P s := by
  rw [HilbertSchmidt.fredholmDet1_diagMul
    (fun p : P => (p.1 : ℂ) ^ (-s)) Finset.univ (by simp) R hR 1 h1]
  simpa only [one_mul, RHTower.eulerHeadAnchor] using
    (Finset.prod_coe_sort P (fun p : ℕ => 1 - (p : ℂ) ^ (-s)))

/-- One finite-prime determinant carries both Euler-head value and additive resolvent response. -/
theorem finitePrimeEulerHead_fredholm_value_and_response
    (P : Finset ℕ) (s : ℂ) (R : ℝ)
    (hR : R * HilbertSchmidt.hsNorm
      (HilbertSchmidt.diagMul (fun p : P => (p.1 : ℂ) ^ (-s))) < 1)
    (h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R) :
    HilbertSchmidt.fredholmDet1
        (HilbertSchmidt.diagMul (fun p : P => (p.1 : ℂ) ^ (-s))) 1 =
        RHTower.eulerHeadAnchor P s ∧
      (∑ p : P, (1 - (p.1 : ℂ) ^ (-s))⁻¹) =
        (P.card : ℂ) - logDeriv
          (fun w => HilbertSchmidt.fredholmDet1
            (HilbertSchmidt.diagMul (fun p : P => (p.1 : ℂ) ^ (-s))) w) 1 := by
  constructor
  · exact finitePrimeFredholmDet1_eq_eulerHeadAnchor P s R hR h1
  · simpa using finiteIndexedResolventValue_eq_fredholmDet1_logDeriv
      (fun p : P => (p.1 : ℂ) ^ (-s)) R hR 1 h1

end

end GaloisForLFunctions
