import GaloisForLFunctions.RHTower.DivisorSourceHarmonicBoundary
import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel
import GaloisForLFunctions.RHTower.DirichletUniformAbel
import GaloisForLFunctions.RHTower.DirichletLSeriesBridge

/-!
# Holomorphic Dirichlet series of the actual divisor source

The coefficients are literally `b(n) = log n - τ(n) + 2γ`, indexed by `n+1`.
Their partial sums are the existing square-root-bounded divisor defect.
The corpus's polynomial Abel theorem therefore constructs a holomorphic sum
on `Re s > 1/2`. Its value at one is the positive harmonic boundary, at least
`1/30`. On `Re s > 3/2`, absolute convergence identifies this continuation with
mathlib's `LSeries` of the same source, providing the input for Euler multiplication.

This supplies the nonvanishing source factor in the PE5 pole obstruction.
It does not assert a bound or obstruction for the deformed prime mean.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower
open GaloisForLFunctions.RHTower

/-- The actual source coefficients, shifted for the ordinary Dirichlet-series API. -/
def divisorSourceCoeff (n : ℕ) : ℂ := (primeFreeDivisorIncrement (n+1) : ℝ)

/-- The ordinary Dirichlet sum of the actual source. -/
def divisorSourceDirichlet (s : ℂ) : ℂ := dirichletSum divisorSourceCoeff s

/-- Exact identification of the coefficient partial sums with the divisor defect. -/
theorem sum_divisorSourceCoeff (N : ℕ) :
    (∑ n ∈ range N, divisorSourceCoeff n) = (primeFreeDivisorDefect N : ℂ) := by
  rw [← sum_primeFreeDivisorIncrement N, Complex.ofReal_sum]
  rw [← Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right,divisorSourceCoeff,Nat.add_comm 1]

/-- The existing defect bound in the form required by polynomial Abel summation. -/
theorem norm_sum_divisorSourceCoeff_le (N : ℕ) :
    ‖∑ n ∈ range N, divisorSourceCoeff n‖ ≤ 24*((N:ℝ)+1)^(1/2:ℝ) := by
  rw [sum_divisorSourceCoeff,Complex.norm_real,Real.norm_eq_abs,← Real.sqrt_eq_rpow]
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [primeFreeDivisorDefect]
  · exact (abs_primeFreeDivisorDefect_le hN).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num))

/-- Ordinary convergence throughout the strict right half-plane. -/
theorem divisorSourceDirichlet_converges {s : ℂ} (hs : (1/2:ℝ)<s.re) :
    DirichletConvergesAt divisorSourceCoeff s :=
  tendsto_dirichlet_partialSum_of_poly_bounded (by norm_num : (0:ℝ)≤24)
    (by norm_num : (0:ℝ)≤1/2) norm_sum_divisorSourceCoeff_le hs

/-- The actual source sum is holomorphic throughout `Re s > 1/2`. -/
theorem differentiableOn_divisorSourceDirichlet :
    DifferentiableOn ℂ divisorSourceDirichlet {s : ℂ | (1/2:ℝ)<s.re} := by
  intro s hs
  change (1/2:ℝ) < s.re at hs
  let σ : ℝ := ((1/2:ℝ)+s.re)/2
  have hσ : (1/2:ℝ)<(σ:ℂ).re := by simp only [Complex.ofReal_re]; dsimp [σ]; linarith
  have hσs : (σ:ℂ).re<s.re := by simp only [Complex.ofReal_re]; dsimp [σ]; linarith
  have hd := differentiableOn_dirichletSum (divisorSourceDirichlet_converges hσ)
  exact (hd.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσs)).differentiableWithinAt

/-- Analytic germs of the actual source are available at every strict-half-plane point. -/
theorem analyticOnNhd_divisorSourceDirichlet :
    AnalyticOnNhd ℂ divisorSourceDirichlet {s : ℂ | (1/2:ℝ)<s.re} :=
  differentiableOn_divisorSourceDirichlet.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

/-- Exact finite identification of the exponent-one source partial sums. -/
theorem divisorSourceDirichlet_partialSum_one (N : ℕ) :
    dirichletPartialSum divisorSourceCoeff N 1 =
      ((∑ n ∈ Icc 1 N, primeFreeDivisorIncrement n/(n:ℝ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum,← Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right,Nat.add_comm 1,dirichletPartialSum,
    divisorSourceCoeff,Complex.cpow_neg_one]
  apply sum_congr rfl
  intro n hn
  push_cast
  simp only [div_eq_mul_inv]

/-- The value at one is the absolute harmonic boundary of the divisor defect. -/
theorem divisorSourceDirichlet_one :
    divisorSourceDirichlet 1 = (divisorHarmonicBoundary : ℂ) := by
  have h := tendsto_dirichletSum (divisorSourceDirichlet_converges
    (s := 1) (by norm_num))
  have hb := Complex.continuous_ofReal.continuousAt.tendsto.comp
    tendsto_sum_primeFreeDivisorIncrement_div
  change Tendsto (fun N : ℕ =>
    ((∑ n ∈ Icc 1 N, primeFreeDivisorIncrement n/(n:ℝ) : ℝ) : ℂ))
    atTop (𝓝 (divisorHarmonicBoundary : ℂ)) at hb
  simp_rw [← divisorSourceDirichlet_partialSum_one] at hb
  exact tendsto_nhds_unique h hb

/-- A quantitative positive value at one, derived from the actual source. -/
theorem one_thirtieth_le_divisorSourceDirichlet_one_re :
    (1/30:ℝ) ≤ (divisorSourceDirichlet 1).re := by
  rw [divisorSourceDirichlet_one,Complex.ofReal_re]
  exact one_thirtieth_le_divisorHarmonicBoundary

/-- The source factor is nonzero at one, without a numerical constant premise. -/
theorem divisorSourceDirichlet_one_ne_zero : divisorSourceDirichlet 1 ≠ 0 := by
  intro h
  have hp := one_thirtieth_le_divisorSourceDirichlet_one_re
  rw [h] at hp
  norm_num at hp

/-- Absolute convergence on a safe half-plane for Euler multiplication. -/
theorem divisorSourceCoeff_absConv {x : ℝ} (hx : 3/2<x) :
    DirichletAbsConvAt divisorSourceCoeff x := by
  let σ : ℝ := ((1/2:ℝ)+(x-1))/2
  have hσ : (1/2:ℝ)<(σ:ℂ).re := by
    simp only [Complex.ofReal_re]; dsimp [σ]; linarith
  have hσx : (σ:ℂ).re+1<x := by
    simp only [Complex.ofReal_re]; dsimp [σ]; linarith
  exact absConvAt_of_convergesAt (divisorSourceDirichlet_converges hσ) hσx

private theorem summable_divisorSource_shifted {s : ℂ} (hs : 3/2<s.re) :
    Summable (fun n : ℕ => divisorSourceCoeff n * (((n:ℝ)+1:ℝ):ℂ)^(-s)) := by
  exact Summable.of_norm_bounded (divisorSourceCoeff_absConv hs)
    (fun n => norm_dirichletTerm_le divisorSourceCoeff n le_rfl)

/-- Absolute summability in mathlib indexing on `Re s > 3/2`. -/
theorem LSeriesSummable_primeFreeDivisorIncrement {s : ℂ} (hs : 3/2<s.re) :
    LSeriesSummable (fun n => (primeFreeDivisorIncrement n : ℂ)) s := by
  apply (summable_nat_add_iff 1).1
  simpa only [term_succ_eq,divisorSourceCoeff] using summable_divisorSource_shifted hs

/-- The continuation and the absolutely convergent L-series have the same source and value. -/
theorem divisorSourceDirichlet_eq_LSeries {s : ℂ} (hs : 3/2<s.re) :
    divisorSourceDirichlet s = LSeries (fun n => (primeFreeDivisorIncrement n : ℂ)) s := by
  have hconv := tendsto_dirichletSum (divisorSourceDirichlet_converges (by linarith : 1/2<s.re))
  have hsum := summable_divisorSource_shifted hs
  have he : divisorSourceDirichlet s =
      ∑' n : ℕ, divisorSourceCoeff n * (((n:ℝ)+1:ℝ):ℂ)^(-s) :=
    tendsto_nhds_unique hconv hsum.hasSum.tendsto_sum_nat
  rw [he]
  have ha := (LSeriesSummable_primeFreeDivisorIncrement hs).sum_add_tsum_nat_add 1
  simpa only [sum_range_one,LSeries.term_zero,zero_add,term_succ_eq,divisorSourceCoeff,LSeries] using ha

end RHTower
