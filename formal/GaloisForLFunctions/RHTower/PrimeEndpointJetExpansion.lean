import GaloisForLFunctions.RHTower.PrimeHigherMertensRate
import Mathlib

/-!
# The endpoint-jet expansion of the prime boundary layer

The prime-harmonic boundary defect is linear in its test function, so a test function of the form
"Taylor polynomial + remainder vanishing to order `M+1`" has defect

`D_x(h) = ∑_{k < M} b_k C_{k+1} / (log x)^{k+1} + O((log x)^{-M-1})`,

where `C_{k+1}` are the higher-order Mertens constants.  The monomial terms come from
`PrimeHigherMertensRate` and the remainder from `PrimeEndpointJet`; this module supplies the
linearity of the defect and assembles the expansion.

This is the card's endpoint-jet theorem: every algebraic order of the prime boundary layer in
`1/log x` is a distributional jet supported at the collapsed endpoint `u = 0`.
-/

set_option maxHeartbeats 1600000

open Filter Topology Set MeasureTheory Asymptotics

namespace RHTower

noncomputable section

/-! ## Linearity of the boundary defect -/

theorem primeBoundaryDefect_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : IntervalIntegrable (fun u : ℝ => f u / u) volume 0 1)
    (hg : IntervalIntegrable (fun u : ℝ => g u / u) volume 0 1) :
    primeBoundaryDefect (fun u : ℝ => f u + g u) x
      = primeBoundaryDefect f x + primeBoundaryDefect g x := by
  have hsum : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
      (if n.Prime then (f (Real.log n / Real.log x) + g (Real.log n / Real.log x)) / n else 0))
      = (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (if n.Prime then f (Real.log n / Real.log x) / n else 0))
        + ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (if n.Prime then g (Real.log n / Real.log x) / n else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · rw [if_pos hp, if_pos hp, if_pos hp, add_div]
    · rw [if_neg hp, if_neg hp, if_neg hp, add_zero]
  have hint : (∫ u in (0 : ℝ)..1, (f u + g u) / u)
      = (∫ u in (0 : ℝ)..1, f u / u) + ∫ u in (0 : ℝ)..1, g u / u := by
    have hpt : ∀ u : ℝ, (f u + g u) / u = f u / u + g u / u := fun u => add_div _ _ _
    simp only [hpt]
    exact intervalIntegral.integral_add hf hg
  rw [primeBoundaryDefect, primeBoundaryDefect, primeBoundaryDefect, hsum, hint]
  ring

theorem primeBoundaryDefect_const_mul (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    primeBoundaryDefect (fun u : ℝ => c * f u) x = c * primeBoundaryDefect f x := by
  have hsum : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
      (if n.Prime then c * f (Real.log n / Real.log x) / n else 0))
      = c * ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (if n.Prime then f (Real.log n / Real.log x) / n else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · rw [if_pos hp, if_pos hp, mul_div_assoc]
    · rw [if_neg hp, if_neg hp, mul_zero]
  have hint : (∫ u in (0 : ℝ)..1, c * f u / u) = c * ∫ u in (0 : ℝ)..1, f u / u := by
    have hpt : ∀ u : ℝ, c * f u / u = c * (f u / u) := fun u => mul_div_assoc c (f u) u
    simp only [hpt]
    exact intervalIntegral.integral_const_mul c _
  rw [primeBoundaryDefect, primeBoundaryDefect, hsum, hint]
  ring

theorem primeBoundaryDefect_sum (M : ℕ) (b : ℕ → ℝ) (x : ℝ) :
    primeBoundaryDefect (fun u : ℝ => ∑ k ∈ Finset.range M, b k * u ^ (k + 1)) x
      = ∑ k ∈ Finset.range M, b k * primeBoundaryDefect (fun u : ℝ => u ^ (k + 1)) x := by
  induction M with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      rw [primeBoundaryDefect]
      simp
  | succ N ih =>
      have hint : ∀ k : ℕ, IntervalIntegrable
          (fun u : ℝ => b k * u ^ (k + 1) / u) volume 0 1 := by
        intro k
        have hpt : EqOn (fun u : ℝ => b k * u ^ k) (fun u : ℝ => b k * u ^ (k + 1) / u)
            (uIoc (0 : ℝ) 1) := by
          intro u hu
          have hu' : u ∈ Ioc (0 : ℝ) 1 := by
            rwa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
          have hu0 : u ≠ 0 := ne_of_gt hu'.1
          simp only
          field_simp
          ring
        exact ((intervalIntegral.intervalIntegrable_pow k).const_mul (b k)).congr hpt
      have hintsum : IntervalIntegrable
          (fun u : ℝ => (∑ k ∈ Finset.range N, b k * u ^ (k + 1)) / u) volume 0 1 := by
        have hpt : EqOn (fun u : ℝ => ∑ k ∈ Finset.range N, b k * u ^ k)
            (fun u : ℝ => (∑ k ∈ Finset.range N, b k * u ^ (k + 1)) / u) (uIoc (0 : ℝ) 1) := by
          intro u hu
          have hu' : u ∈ Ioc (0 : ℝ) 1 := by
            rwa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
          have hu0 : u ≠ 0 := ne_of_gt hu'.1
          simp only
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun k _ => ?_
          field_simp
          ring
        have hcontsum : IntervalIntegrable
            (fun u : ℝ => ∑ k ∈ Finset.range N, b k * u ^ k) volume 0 1 := by
          refine Continuous.intervalIntegrable ?_ 0 1
          exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_pow k)
        exact hcontsum.congr hpt
      have hsplit : (fun u : ℝ => ∑ k ∈ Finset.range (N + 1), b k * u ^ (k + 1))
          = fun u : ℝ => (∑ k ∈ Finset.range N, b k * u ^ (k + 1)) + b N * u ^ (N + 1) := by
        funext u
        rw [Finset.sum_range_succ]
      rw [hsplit, primeBoundaryDefect_add hintsum (hint N),
        primeBoundaryDefect_const_mul (b N) (fun u : ℝ => u ^ (N + 1)) x, ih,
        Finset.sum_range_succ]

/-! ## The endpoint-jet expansion -/

/-- **`(6)`--`(7)`: the endpoint-jet expansion of the prime-harmonic boundary defect.**
A test function whose Taylor polynomial at the collapsed endpoint is `∑_{k<M} b_k u^{k+1}` and
whose remainder vanishes to order `M+1` has boundary defect equal to the corresponding jet
`∑_{k<M} b_k C_{k+1} / (log x)^{k+1}` up to `O((log x)^{-M-1})`. -/
theorem exists_abs_primeBoundaryDefect_jet_le (M : ℕ) (b : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ B X₀ : ℝ, 0 ≤ B ∧ 4 ≤ X₀ ∧
      ∀ (r r' : ℝ → ℝ),
        (∀ u ∈ Ioc (0 : ℝ) 1, HasDerivAt r (r' u) u) →
        ContinuousOn r' (Ioc (0 : ℝ) 1) →
        (∀ u ∈ Ioc (0 : ℝ) 1, |r u| ≤ A * u ^ (M + 1)) →
        (∀ u ∈ Ioc (0 : ℝ) 1, |r' u| ≤ A * u ^ M) →
        ∀ x : ℝ, X₀ ≤ x →
          |primeBoundaryDefect (fun u : ℝ => (∑ k ∈ Finset.range M, b k * u ^ (k + 1)) + r u) x
              - ∑ k ∈ Finset.range M,
                  b k * mertensLogPowConstantFull k / (Real.log x) ^ (k + 1)|
            ≤ B / (Real.log x) ^ (M + 1) := by
  classical
  choose Bm Xm hBm hXm hboundm using fun k : ℕ => exists_abs_primeBoundaryDefect_pow_le k M
  obtain ⟨Br, Xr, hBr, hXr, hboundr⟩ := exists_abs_primeBoundaryDefect_le M
  refine ⟨(∑ k ∈ Finset.range M, |b k| * Bm k) + A * Br,
    Xr + ∑ k ∈ Finset.range M, (|Xm k| + 4), ?_, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑ k ∈ Finset.range M, |b k| * Bm k :=
      Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (hBm k)
    have h2 : (0 : ℝ) ≤ A * Br := mul_nonneg hA hBr
    linarith
  · have h1 : (0 : ℝ) ≤ ∑ k ∈ Finset.range M, (|Xm k| + 4) :=
      Finset.sum_nonneg fun k _ => by positivity
    linarith
  intro r r' hr hr' hb hb' x hx
  have hXrx : Xr ≤ x := by
    have h1 : (0 : ℝ) ≤ ∑ k ∈ Finset.range M, (|Xm k| + 4) :=
      Finset.sum_nonneg fun k _ => by positivity
    linarith
  have hXmx : ∀ k ∈ Finset.range M, Xm k ≤ x := by
    intro k hk
    have hle : |Xm k| + 4 ≤ ∑ j ∈ Finset.range M, (|Xm j| + 4) :=
      Finset.single_le_sum (f := fun j => |Xm j| + 4) (fun j _ => by positivity) hk
    have h2 : Xm k ≤ |Xm k| := le_abs_self _
    linarith
  have hx4 : (4 : ℝ) ≤ x := le_trans hXr hXrx
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hLpow : (0 : ℝ) < (Real.log x) ^ (M + 1) := by positivity
  -- split the defect
  have hintr : IntervalIntegrable (fun u : ℝ => r u / u) volume 0 1 :=
    intervalIntegrable_rDiv (M := M) hA hr hb
  have hintP : IntervalIntegrable
      (fun u : ℝ => (∑ k ∈ Finset.range M, b k * u ^ (k + 1)) / u) volume 0 1 := by
    have hpt : EqOn (fun u : ℝ => ∑ k ∈ Finset.range M, b k * u ^ k)
        (fun u : ℝ => (∑ k ∈ Finset.range M, b k * u ^ (k + 1)) / u) (uIoc (0 : ℝ) 1) := by
      intro u hu
      have hu' : u ∈ Ioc (0 : ℝ) 1 := by
        rwa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      have hu0 : u ≠ 0 := ne_of_gt hu'.1
      simp only
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
      ring
    have hcontsum : IntervalIntegrable
        (fun u : ℝ => ∑ k ∈ Finset.range M, b k * u ^ k) volume 0 1 := by
      refine Continuous.intervalIntegrable ?_ 0 1
      exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_pow k)
    exact hcontsum.congr hpt
  rw [primeBoundaryDefect_add hintP hintr, primeBoundaryDefect_sum M b x]
  -- bound each monomial and the remainder
  have hmono : ∀ k ∈ Finset.range M,
      |b k * primeBoundaryDefect (fun u : ℝ => u ^ (k + 1)) x
        - b k * mertensLogPowConstantFull k / (Real.log x) ^ (k + 1)|
        ≤ |b k| * Bm k / (Real.log x) ^ (M + 1) := by
    intro k hk
    have hkey := hboundm k x (hXmx k hk)
    have hval : b k * primeBoundaryDefect (fun u : ℝ => u ^ (k + 1)) x
        - b k * mertensLogPowConstantFull k / (Real.log x) ^ (k + 1)
        = b k * (primeBoundaryDefect (fun u : ℝ => u ^ (k + 1)) x
          - mertensLogPowConstantFull k / (Real.log x) ^ (k + 1)) := by
      ring
    rw [hval, abs_mul]
    have hstep : |b k| * |primeBoundaryDefect (fun u : ℝ => u ^ (k + 1)) x
        - mertensLogPowConstantFull k / (Real.log x) ^ (k + 1)|
        ≤ |b k| * (Bm k / (Real.log x) ^ (M + 1)) :=
      mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
    refine hstep.trans_eq ?_
    ring
  have hrem : |primeBoundaryDefect r x| ≤ A * Br / (Real.log x) ^ (M + 1) :=
    hboundr r r' A hA hr hr' hb hb' x hXrx
  have hsum : |(∑ k ∈ Finset.range M, b k * primeBoundaryDefect (fun u : ℝ => u ^ (k + 1)) x)
      - ∑ k ∈ Finset.range M, b k * mertensLogPowConstantFull k / (Real.log x) ^ (k + 1)|
      ≤ ∑ k ∈ Finset.range M, |b k| * Bm k / (Real.log x) ^ (M + 1) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum hmono
  have htri : |(∑ k ∈ Finset.range M, b k * primeBoundaryDefect (fun u : ℝ => u ^ (k + 1)) x)
      + primeBoundaryDefect r x
      - ∑ k ∈ Finset.range M, b k * mertensLogPowConstantFull k / (Real.log x) ^ (k + 1)|
      ≤ |(∑ k ∈ Finset.range M, b k * primeBoundaryDefect (fun u : ℝ => u ^ (k + 1)) x)
          - ∑ k ∈ Finset.range M, b k * mertensLogPowConstantFull k / (Real.log x) ^ (k + 1)|
        + |primeBoundaryDefect r x| := by
    have hrw : (∑ k ∈ Finset.range M, b k * primeBoundaryDefect (fun u : ℝ => u ^ (k + 1)) x)
        + primeBoundaryDefect r x
        - ∑ k ∈ Finset.range M, b k * mertensLogPowConstantFull k / (Real.log x) ^ (k + 1)
        = ((∑ k ∈ Finset.range M, b k * primeBoundaryDefect (fun u : ℝ => u ^ (k + 1)) x)
            - ∑ k ∈ Finset.range M,
                b k * mertensLogPowConstantFull k / (Real.log x) ^ (k + 1))
          + primeBoundaryDefect r x := by ring
    rw [hrw]
    exact abs_add_le _ _
  refine htri.trans ?_
  have hfin : (∑ k ∈ Finset.range M, |b k| * Bm k / (Real.log x) ^ (M + 1))
      + A * Br / (Real.log x) ^ (M + 1)
      = ((∑ k ∈ Finset.range M, |b k| * Bm k) + A * Br) / (Real.log x) ^ (M + 1) := by
    rw [add_div, ← Finset.sum_div]
  rw [← hfin]
  exact add_le_add hsum hrem

end

end RHTower
