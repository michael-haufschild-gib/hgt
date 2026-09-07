import GaloisForLFunctions.RHTower.DivisorUnsignedChannelPositivity
import Mathlib.Analysis.PSeries

/-!
# Positive harmonic boundary of the actual divisor source

Write `D(N) = primeFreeDivisorDefect N` and
`b(n) = log n - τ(n) + 2γ = primeFreeDivisorIncrement n`.
The square-root bound on `D` makes `∑ D(n)/(n(n+1))` absolutely convergent.
Nonnegative ordinary prefixes of `D` and a second Abel summation give the
strict quantitative lower bound `1/30`. The original source satisfies
`∑_{n≤N} b(n)/n → divisorHarmonicBoundary`.

All bounds are analytic; no numerical experiment is used as a premise.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

/-- The positive reciprocal first difference used in Abel summation. -/
def divisorHarmonicWeight (n : ℕ) : ℝ := 1 / ((n:ℝ)*(n+1))

/-- The absolutely summable defect term, indexed from zero. -/
def divisorHarmonicBoundaryTerm (n : ℕ) : ℝ :=
  primeFreeDivisorDefect (n+1)*divisorHarmonicWeight (n+1)

/-- The harmonic boundary of the actual source, represented by an absolute series. -/
def divisorHarmonicBoundary : ℝ := ∑' n : ℕ, divisorHarmonicBoundaryTerm n

private theorem harmonic_weight_nonneg (n : ℕ) : 0 ≤ divisorHarmonicWeight n := by
  unfold divisorHarmonicWeight
  positivity

private theorem harmonic_weight_gap {n : ℕ} (hn : 1 ≤ n) :
    divisorHarmonicWeight n-divisorHarmonicWeight (n+1) =
      2 / ((n:ℝ)*(n+1)*(n+2)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
  have hn2 : (n:ℝ)+2 ≠ 0 := by positivity
  simp only [divisorHarmonicWeight,Nat.cast_add,Nat.cast_one]
  have heq : (n:ℝ)+1+1=(n:ℝ)+2 := by ring
  rw [heq]
  field_simp [hnR.ne',hn1,hn2]
  ring

private theorem harmonic_weight_gap_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ divisorHarmonicWeight n-divisorHarmonicWeight (n+1) := by
  rw [harmonic_weight_gap hn]
  positivity

private theorem sqrt_div_sq {x : ℝ} (hx : 0<x) :
    Real.sqrt x/x^2 = 1/x^(3/2:ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 2, ← Real.rpow_sub hx]
  have he : (1/2:ℝ)-(2:ℕ) = -(3/2:ℝ) := by norm_num
  rw [he,Real.rpow_neg hx.le]
  simp only [one_div]

private theorem harmonic_boundary_term_bound (n : ℕ) :
    |divisorHarmonicBoundaryTerm n| ≤ 24 / ((n:ℝ)+1)^(3/2:ℝ) := by
  let x : ℝ := (n:ℝ)+1
  have hx : 0<x := by dsimp [x]; positivity
  have hD := abs_primeFreeDivisorDefect_le (show 1 ≤ n+1 by omega)
  have hD' : |primeFreeDivisorDefect (n+1)| ≤ 24*Real.sqrt x := by
    simpa [x] using hD
  change |primeFreeDivisorDefect (n+1)*(1/(((n+1:ℕ):ℝ)*(((n+1:ℕ):ℝ)+1)))| ≤ _
  have hcast : ((n+1:ℕ):ℝ)=x := by simp [x]
  rw [hcast]
  calc
    _ = |primeFreeDivisorDefect (n+1)| / (x*(x+1)) := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/(x*(x+1)))]
      ring
    _ ≤ 24*Real.sqrt x/(x*(x+1)) := div_le_div_of_nonneg_right hD' (by positivity)
    _ ≤ 24*Real.sqrt x/x^2 := div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    _ = 24*(Real.sqrt x/x^2) := by ring
    _ = 24*(1/x^(3/2:ℝ)) := by rw [sqrt_div_sq hx]
    _ = _ := by dsimp [x]; ring

/-- The existing square-root defect bound gives absolute convergence. -/
theorem summable_divisorHarmonicBoundaryTerm : Summable divisorHarmonicBoundaryTerm := by
  have hs : Summable (fun n : ℕ => 24 / ((n:ℝ)+1)^(3/2:ℝ)) := by
    have h := ((Real.summable_one_div_nat_add_rpow 1 (3/2)).2 (by norm_num)).mul_left 24
    have ha (n : ℕ) : |(n:ℝ)+1|=(n:ℝ)+1 := abs_of_pos (by positivity)
    simpa only [ha,mul_one_div] using h
  apply Summable.of_norm
  simp only [Real.norm_eq_abs]
  exact Summable.of_nonneg_of_le (fun n => abs_nonneg _) harmonic_boundary_term_bound hs

/-- A second Abel summation retains a strictly positive first-prefix contribution. -/
theorem divisorHarmonicBoundary_prefix_lower {N : ℕ} (hN : 1 ≤ N) :
    primeFreeDivisorDefect 1/3 ≤
      ∑ n ∈ Icc 1 N, primeFreeDivisorDefect n*divisorHarmonicWeight n := by
  rw [HTGeometry.sum_mul_eq_partial_mul_diff_ring]
  have hnonneg (n : ℕ) (hn : n ∈ Icc 1 N) :
      0 ≤ (∑ k ∈ Icc 1 n, primeFreeDivisorDefect k)*
        (divisorHarmonicWeight n-divisorHarmonicWeight (n+1)) :=
    mul_nonneg (sum_primeFreeDivisorDefect_nonneg n)
      (harmonic_weight_gap_nonneg (mem_Icc.mp hn).1)
  have hfirst := single_le_sum hnonneg (show 1 ∈ Icc 1 N by simp [hN])
  have hfirst' : primeFreeDivisorDefect 1/3 ≤
      ∑ n ∈ Icc 1 N, (∑ k ∈ Icc 1 n, primeFreeDivisorDefect k)*
        (divisorHarmonicWeight n-divisorHarmonicWeight (n+1)) := by
    have he : (∑ k ∈ Icc 1 1, primeFreeDivisorDefect k)*
        (divisorHarmonicWeight 1-divisorHarmonicWeight 2) = primeFreeDivisorDefect 1/3 := by
      norm_num [divisorHarmonicWeight]
      ring
    rw [he] at hfirst
    exact hfirst
  have hterminal := mul_nonneg (sum_primeFreeDivisorDefect_nonneg N)
    (harmonic_weight_nonneg (N+1))
  linarith only [hfirst',hterminal]

private theorem sum_harmonic_boundary_range (N : ℕ) :
    (∑ n ∈ range N, divisorHarmonicBoundaryTerm n) =
      ∑ n ∈ Icc 1 N, primeFreeDivisorDefect n*divisorHarmonicWeight n := by
  rw [← Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right,divisorHarmonicBoundaryTerm,Nat.add_comm 1]

/-- The first-prefix contribution survives the infinite limit. -/
theorem divisorHarmonicBoundary_lower : primeFreeDivisorDefect 1/3 ≤ divisorHarmonicBoundary := by
  have hlim := summable_divisorHarmonicBoundaryTerm.hasSum.tendsto_sum_nat
  have hb : ∀ᶠ N : ℕ in atTop, primeFreeDivisorDefect 1/3 ≤
      ∑ n ∈ range N, divisorHarmonicBoundaryTerm n := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [sum_harmonic_boundary_range]
    exact divisorHarmonicBoundary_prefix_lower hN
  exact ge_of_tendsto hlim hb

/-- A symbolic harmonic estimate gives a uniform positive lower bound. -/
theorem one_thirtieth_le_divisorHarmonicBoundary : (1/30:ℝ) ≤ divisorHarmonicBoundary := by
  have h := (harmonic_mascheroni_half_bounds (n := 4) (by norm_num)).2
  norm_num [harmonic,Finset.sum_range_succ,Real.log_four_eq] at h
  have hD : (1/10:ℝ) ≤ primeFreeDivisorDefect 1 := by
    norm_num [primeFreeDivisorDefect]
    linarith [Real.log_two_lt_d9]
  have hB := divisorHarmonicBoundary_lower
  linarith only [hD,hB]

/-- The actual harmonic boundary is strictly positive. -/
theorem divisorHarmonicBoundary_pos : 0 < divisorHarmonicBoundary :=
  lt_of_lt_of_le (by norm_num) one_thirtieth_le_divisorHarmonicBoundary

private theorem harmonic_weight_eq_reciprocal_gap {n : ℕ} (hn : 1 ≤ n) :
    divisorHarmonicWeight n = 1/(n:ℝ)-1/((n:ℝ)+1) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n≠0 by omega)
  have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
  unfold divisorHarmonicWeight
  field_simp [hn0,hn1]
  ring

/-- Exact Abel decomposition of the original source at the harmonic exponent. -/
theorem sum_primeFreeDivisorIncrement_div_eq (N : ℕ) :
    (∑ n ∈ Icc 1 N, primeFreeDivisorIncrement n/(n:ℝ)) =
      (∑ n ∈ Icc 1 N, primeFreeDivisorDefect n*divisorHarmonicWeight n) +
        primeFreeDivisorDefect N/((N:ℝ)+1) := by
  have hleft : (∑ n ∈ Icc 1 N, primeFreeDivisorIncrement n/(n:ℝ)) =
      ∑ n ∈ Icc 1 N, primeFreeDivisorIncrement n*(1/(n:ℝ)) := by
    apply sum_congr rfl
    intro n hn
    ring
  rw [hleft,HTGeometry.sum_mul_eq_partial_mul_diff_ring]
  simp_rw [sum_primeFreeDivisorIncrement]
  rw [show primeFreeDivisorDefect N*(1/((N+1:ℕ):ℝ)) =
      primeFreeDivisorDefect N/((N:ℝ)+1) by push_cast; ring]
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [harmonic_weight_eq_reciprocal_gap (mem_Icc.mp hn).1]
  push_cast
  rfl

/-- The terminal Abel contribution vanishes by the square-root defect bound. -/
theorem tendsto_primeFreeDivisorDefect_div_succ :
    Tendsto (fun N : ℕ => primeFreeDivisorDefect N/((N:ℝ)+1)) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun N : ℕ => 24*(Real.sqrt N/(N:ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_sqrt_natCast_div_natCast_atTop_zero.const_mul (24:ℝ)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0 < (N:ℝ)+1)]
  calc
    _ ≤ 24*Real.sqrt N/((N:ℝ)+1) :=
      div_le_div_of_nonneg_right (abs_primeFreeDivisorDefect_le hN) (by positivity)
    _ ≤ 24*Real.sqrt N/(N:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hN0 (by linarith)
    _ = _ := by ring

/-- The ordinary source Dirichlet series converges at one to the positive boundary. -/
theorem tendsto_sum_primeFreeDivisorIncrement_div :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, primeFreeDivisorIncrement n/(n:ℝ))
      atTop (𝓝 divisorHarmonicBoundary) := by
  have hlim := summable_divisorHarmonicBoundaryTerm.hasSum.tendsto_sum_nat
  simp_rw [sum_harmonic_boundary_range] at hlim
  have h := hlim.add tendsto_primeFreeDivisorDefect_div_succ
  simpa only [← sum_primeFreeDivisorIncrement_div_eq,add_zero,divisorHarmonicBoundary] using h

end RHTower
