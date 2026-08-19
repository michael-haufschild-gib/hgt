import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Landau's theorem for general Dirichlet series

A general Dirichlet series `Σ a_j exp(-λ_j s)` with nonnegative coefficients and nonnegative
frequencies converges uniformly on the closed half plane to the right of any convergence point,
and its Taylor coefficients at a centre one step to the right are signs times the nonnegative
frequency moments.  Positivity therefore removes all cancellation from the Taylor coefficients,
and Tonelli reassembles the exponential: analytic continuation across the real abscissa forces
convergence further left.

This is the general-frequency form of Landau's theorem; the classical `Σ a_n n^{-s}` statement is
the special case `λ_n = log n`.
-/

open Complex Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- The `k`-th frequency-twisted term of a general Dirichlet series at a real abscissa. -/
def gdTwistTerm (a lam : ι → ℝ) (σ : ℝ) (k : ℕ) (j : ι) : ℝ :=
  a j * lam j ^ k * Real.exp (-(σ * lam j))

/-- The general Dirichlet series itself. -/
def gdSeries (a lam : ι → ℝ) (s : ℂ) : ℂ :=
  ∑' j, (a j : ℂ) * Complex.exp (-(s * (lam j : ℂ)))

theorem gdTwistTerm_nonneg {a lam : ι → ℝ} (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    (σ : ℝ) (k : ℕ) (j : ι) : 0 ≤ gdTwistTerm a lam σ k j := by
  have h1 := ha j
  have h2 := hlam j
  rw [gdTwistTerm]
  positivity

theorem pow_le_factorial_mul_exp_nonneg {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    t ^ m ≤ (Nat.factorial m : ℝ) * Real.exp t := by
  have hser := Real.sum_le_exp_of_nonneg ht (m + 1)
  have hmem : t ^ m / (Nat.factorial m : ℝ)
      ≤ ∑ i ∈ Finset.range (m + 1), t ^ i / (Nat.factorial i : ℝ) := by
    refine Finset.single_le_sum (f := fun i => t ^ i / (Nat.factorial i : ℝ)) (fun i _ => ?_)
      (Finset.self_mem_range_succ m)
    positivity
  have hfac : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hfac] at hmem
  nlinarith [hmem, hser, hfac, Real.exp_pos t]

/-- The frequency twist is dominated by the factorial-scaled base term one step to the right. -/
theorem gdTwistTerm_le {a lam : ι → ℝ} (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    (σ₁ : ℝ) {h : ℝ} (hh : 0 < h) (k : ℕ) (j : ι) :
    gdTwistTerm a lam (σ₁ + h) k j ≤
      ((Nat.factorial k : ℝ) / h ^ k) * gdTwistTerm a lam σ₁ 0 j := by
  have hlj := hlam j
  have haj := ha j
  have hkey : lam j ^ k * Real.exp (-(h * lam j)) ≤ (Nat.factorial k : ℝ) / h ^ k := by
    have hpow := pow_le_factorial_mul_exp_nonneg (mul_nonneg hh.le hlj) k
    rw [mul_pow] at hpow
    have hhk : (0 : ℝ) < h ^ k := by positivity
    rw [le_div_iff₀ hhk]
    have hexp : Real.exp (-(h * lam j)) * Real.exp (h * lam j) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (h * lam j), Real.exp_pos (-(h * lam j)),
      pow_nonneg hlj k, hpow, hexp]
  have hsplit : Real.exp (-((σ₁ + h) * lam j)) =
      Real.exp (-(σ₁ * lam j)) * Real.exp (-(h * lam j)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [gdTwistTerm, gdTwistTerm, hsplit, pow_zero, mul_one]
  have hbase : 0 ≤ a j * Real.exp (-(σ₁ * lam j)) := by positivity
  nlinarith [hkey, hbase, Real.exp_pos (-(σ₁ * lam j)), pow_nonneg hlj k,
    Real.exp_pos (-(h * lam j))]

theorem summable_gdTwistTerm {a lam : ι → ℝ} (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σ₁ : ℝ} (hsum : Summable (gdTwistTerm a lam σ₁ 0)) {h : ℝ} (hh : 0 < h) (k : ℕ) :
    Summable (gdTwistTerm a lam (σ₁ + h) k) :=
  Summable.of_nonneg_of_le (gdTwistTerm_nonneg ha hlam _ k)
    (gdTwistTerm_le ha hlam σ₁ hh k) (hsum.mul_left _)

theorem norm_gd_term {a lam : ι → ℝ} (ha : ∀ j, 0 ≤ a j) (_hlam : ∀ j, 0 ≤ lam j)
    (s : ℂ) (j : ι) :
    ‖(a j : ℂ) * Complex.exp (-(s * (lam j : ℂ)))‖ = gdTwistTerm a lam s.re 0 j := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha j), Complex.norm_exp,
    gdTwistTerm, pow_zero, mul_one]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

theorem summable_gd_term {a lam : ι → ℝ} (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σ₁ : ℝ} (hsum : Summable (gdTwistTerm a lam σ₁ 0)) {s : ℂ} (hs : σ₁ ≤ s.re) :
    Summable (fun j => (a j : ℂ) * Complex.exp (-(s * (lam j : ℂ)))) := by
  refine Summable.of_norm_bounded hsum (fun j => ?_)
  rw [norm_gd_term ha hlam s j, gdTwistTerm, gdTwistTerm, pow_zero, mul_one]
  have hexp : Real.exp (-(s.re * lam j)) ≤ Real.exp (-(σ₁ * lam j)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hlam j]
  exact mul_le_mul_of_nonneg_left hexp (ha j)

/-! ## The Taylor series at a safe centre -/

/-- The `k`-th nonnegative frequency moment at a real abscissa. -/
def gdMoment (a lam : ι → ℝ) (σ : ℝ) (k : ℕ) : ℝ := ∑' j, gdTwistTerm a lam σ k j

theorem gdMoment_nonneg {a lam : ι → ℝ} (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    (σ : ℝ) (k : ℕ) : 0 ≤ gdMoment a lam σ k :=
  tsum_nonneg (gdTwistTerm_nonneg ha hlam σ k)

theorem gdMoment_le {a lam : ι → ℝ} (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σ₁ : ℝ} (hsum : Summable (gdTwistTerm a lam σ₁ 0)) {h : ℝ} (hh : 0 < h) (k : ℕ) :
    gdMoment a lam (σ₁ + h) k ≤
      ((Nat.factorial k : ℝ) / h ^ k) * gdMoment a lam σ₁ 0 := by
  rw [gdMoment, gdMoment, ← tsum_mul_left]
  exact (summable_gdTwistTerm ha hlam hsum hh k).tsum_mono
    (hsum.mul_left _) (gdTwistTerm_le ha hlam σ₁ hh k)

/-- The Taylor series of a general Dirichlet series at a real centre. -/
def gdPowerSeries (a lam : ι → ℝ) (σ : ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun k => (-1) ^ k * ((gdMoment a lam σ k : ℝ) : ℂ) / (Nat.factorial k : ℂ))

theorem gdPowerSeries_coeff (a lam : ι → ℝ) (σ : ℝ) (k : ℕ) :
    (gdPowerSeries a lam σ).coeff k =
      (-1) ^ k * ((gdMoment a lam σ k : ℝ) : ℂ) / (Nat.factorial k : ℂ) := by
  rw [gdPowerSeries, FormalMultilinearSeries.coeff_ofScalars]

theorem norm_gdPowerSeries_coeff {a lam : ι → ℝ} (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    (σ : ℝ) (k : ℕ) :
    ‖(gdPowerSeries a lam σ).coeff k‖ = gdMoment a lam σ k / (Nat.factorial k : ℝ) := by
  rw [gdPowerSeries_coeff, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (gdMoment_nonneg ha hlam σ k),
    Complex.norm_natCast]

/-! ## The Taylor expansion inside the safe disk -/

section Expansion

variable {a lam : ι → ℝ}

private def gdArray (a lam : ι → ℝ) (σ : ℝ) (y : ℂ) (p : ι × ℕ) : ℂ :=
  (a p.1 : ℂ) * Complex.exp (-((σ : ℂ) * (lam p.1 : ℂ))) *
    ((-(y * (lam p.1 : ℂ))) ^ p.2 / (Nat.factorial p.2 : ℂ))

private theorem norm_gdArray (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    (σ : ℝ) (y : ℂ) (p : ι × ℕ) :
    ‖gdArray a lam σ y p‖ =
      gdTwistTerm a lam σ p.2 p.1 * (‖y‖ ^ p.2 / (Nat.factorial p.2 : ℝ)) := by
  rw [gdArray, norm_mul, norm_mul, norm_div, norm_pow, norm_neg, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (ha p.1), Complex.norm_exp,
    Complex.norm_real, Real.norm_of_nonneg (hlam p.1), Complex.norm_natCast,
    gdTwistTerm]
  have hre : (-((σ : ℂ) * (lam p.1 : ℂ))).re = -(σ * lam p.1) := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  rw [hre]
  ring

private theorem summable_gdArray_norm (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σ₁ : ℝ} (hsum : Summable (gdTwistTerm a lam σ₁ 0)) {h : ℝ} (_hh : 0 < h)
    {y : ℂ} (hy : ‖y‖ < h) :
    Summable (fun p : ι × ℕ => ‖gdArray a lam (σ₁ + h) y p‖) := by
  have hnn : (0 : ι × ℕ → ℝ) ≤ fun p => ‖gdArray a lam (σ₁ + h) y p‖ :=
    fun p => norm_nonneg _
  refine (summable_prod_of_nonneg hnn).mpr ⟨fun j => ?_, ?_⟩
  · have hexp : Summable (fun k : ℕ => (‖y‖ * lam j) ^ k / (Nat.factorial k : ℝ)) := by
      simpa using (Real.summable_pow_div_factorial (‖y‖ * lam j))
    refine (hexp.mul_left (a j * Real.exp (-((σ₁ + h) * lam j)))).congr (fun k => ?_)
    rw [norm_gdArray ha hlam, gdTwistTerm]
    rw [mul_pow]
    ring
  · have hshift : Summable (gdTwistTerm a lam (σ₁ + (h - ‖y‖)) 0) :=
      summable_gdTwistTerm ha hlam hsum (by linarith) 0
    refine hshift.congr (fun j => ?_)
    have hexp : ∑' k : ℕ, (‖y‖ * lam j) ^ k / (Nat.factorial k : ℝ) =
        Real.exp (‖y‖ * lam j) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have hval : ∑' k : ℕ, ‖gdArray a lam (σ₁ + h) y (j, k)‖ =
        a j * Real.exp (-((σ₁ + h) * lam j)) *
          ∑' k : ℕ, (‖y‖ * lam j) ^ k / (Nat.factorial k : ℝ) := by
      rw [← tsum_mul_left]
      refine tsum_congr (fun k => ?_)
      rw [norm_gdArray ha hlam, gdTwistTerm, mul_pow]
      ring
    rw [gdTwistTerm, pow_zero, mul_one, hval, hexp]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring

private theorem summable_gdArray (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σ₁ : ℝ} (hsum : Summable (gdTwistTerm a lam σ₁ 0)) {h : ℝ} (hh : 0 < h)
    {y : ℂ} (hy : ‖y‖ < h) :
    Summable (gdArray a lam (σ₁ + h) y) :=
  Summable.of_norm (summable_gdArray_norm ha hlam hsum hh hy)

private theorem hasSum_gdArray_column (_hlam : ∀ j, 0 ≤ lam j) (σ : ℝ) (y : ℂ) (j : ι) :
    HasSum (fun k : ℕ => gdArray a lam σ y (j, k))
      ((a j : ℂ) * Complex.exp (-((((σ : ℂ)) + y) * (lam j : ℂ)))) := by
  have hexp : HasSum (fun k : ℕ => (-(y * (lam j : ℂ))) ^ k / (Nat.factorial k : ℂ))
      (Complex.exp (-(y * (lam j : ℂ)))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hmul := hexp.mul_left ((a j : ℂ) * Complex.exp (-((σ : ℂ) * (lam j : ℂ))))
  have hfun : (fun k : ℕ => gdArray a lam σ y (j, k)) =
      fun k : ℕ => (a j : ℂ) * Complex.exp (-((σ : ℂ) * (lam j : ℂ))) *
        ((-(y * (lam j : ℂ))) ^ k / (Nat.factorial k : ℂ)) := by
    funext k
    rw [gdArray]
  have hval : (a j : ℂ) * Complex.exp (-((σ : ℂ) * (lam j : ℂ))) *
      Complex.exp (-(y * (lam j : ℂ))) =
      (a j : ℂ) * Complex.exp (-((((σ : ℂ)) + y) * (lam j : ℂ))) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hfun, ← hval]
  exact hmul

private theorem hasSum_gdArray_row (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σ₁ : ℝ} (hsum : Summable (gdTwistTerm a lam σ₁ 0)) {h : ℝ} (hh : 0 < h)
    (y : ℂ) (k : ℕ) :
    HasSum (fun j : ι => gdArray a lam (σ₁ + h) y (j, k))
      ((gdPowerSeries a lam (σ₁ + h)).coeff k * y ^ k) := by
  have hreal : HasSum (fun j : ι => gdTwistTerm a lam (σ₁ + h) k j)
      (gdMoment a lam (σ₁ + h) k) := (summable_gdTwistTerm ha hlam hsum hh k).hasSum
  have hcx : HasSum (fun j : ι => ((gdTwistTerm a lam (σ₁ + h) k j : ℝ) : ℂ))
      (((gdMoment a lam (σ₁ + h) k : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.hasSum hreal)
  have hscaled := hcx.mul_left ((-1) ^ k * y ^ k / (Nat.factorial k : ℂ))
  have hfun : (fun j : ι => gdArray a lam (σ₁ + h) y (j, k)) =
      fun j : ι => (-1) ^ k * y ^ k / (Nat.factorial k : ℂ) *
        ((gdTwistTerm a lam (σ₁ + h) k j : ℝ) : ℂ) := by
    funext j
    rw [gdArray, gdTwistTerm]
    have hexp : Complex.exp (-(((σ₁ + h : ℝ) : ℂ) * (lam j : ℂ))) =
        ((Real.exp (-((σ₁ + h) * lam j)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  have hval : (gdPowerSeries a lam (σ₁ + h)).coeff k * y ^ k =
      (-1) ^ k * y ^ k / (Nat.factorial k : ℂ) *
        ((gdMoment a lam (σ₁ + h) k : ℝ) : ℂ) := by
    rw [gdPowerSeries_coeff]
    ring
  rw [hfun, hval]
  exact hscaled

/-- **Taylor expansion at a safe centre.**  Inside the disk of radius `h` around `σ₁ + h` the
general Dirichlet series is the sum of its frequency-moment Taylor series. -/
theorem hasSum_gdPowerSeries (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σ₁ : ℝ} (hsum : Summable (gdTwistTerm a lam σ₁ 0)) {h : ℝ} (hh : 0 < h)
    {y : ℂ} (hy : ‖y‖ < h) :
    HasSum (fun k : ℕ => (gdPowerSeries a lam (σ₁ + h)).coeff k * y ^ k)
      (gdSeries a lam (((σ₁ + h : ℝ) : ℂ) + y)) := by
  have hF := summable_gdArray ha hlam hsum hh hy
  have hcolumns : HasSum (fun j : ι =>
      (a j : ℂ) * Complex.exp (-((((σ₁ + h : ℝ) : ℂ) + y) * (lam j : ℂ))))
      (∑' p : ι × ℕ, gdArray a lam (σ₁ + h) y p) :=
    hF.hasSum.prod_fiberwise (fun j => hasSum_gdArray_column hlam _ y j)
  have hvalue : (∑' p : ι × ℕ, gdArray a lam (σ₁ + h) y p) =
      gdSeries a lam (((σ₁ + h : ℝ) : ℂ) + y) := by
    rw [gdSeries]
    exact (hcolumns.tsum_eq).symm
  have hswap : Summable (fun p : ℕ × ι => gdArray a lam (σ₁ + h) y (p.2, p.1)) :=
    ((Equiv.prodComm ℕ ι).summable_iff).mpr hF
  have hrows : HasSum (fun k : ℕ =>
      (gdPowerSeries a lam (σ₁ + h)).coeff k * y ^ k)
      (∑' p : ℕ × ι, gdArray a lam (σ₁ + h) y (p.2, p.1)) :=
    hswap.hasSum.prod_fiberwise (fun k => hasSum_gdArray_row ha hlam hsum hh y k)
  have hsame : (∑' p : ℕ × ι, gdArray a lam (σ₁ + h) y (p.2, p.1)) =
      ∑' p : ι × ℕ, gdArray a lam (σ₁ + h) y p :=
    ((Equiv.prodComm ℕ ι).tsum_eq (gdArray a lam (σ₁ + h) y))
  rw [hsame, hvalue] at hrows
  exact hrows

end Expansion

end

end GaloisForLFunctions.HTGeometry
