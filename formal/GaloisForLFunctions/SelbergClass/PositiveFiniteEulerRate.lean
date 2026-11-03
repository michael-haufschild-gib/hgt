import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerProduct
import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerZeros

/-!
# The exact Euler discrepancy boundary of positive reciprocal twins

The two negative local roots have radii `p^σ` and `p^(1-σ)`.
For `σ ≥ 1/2`, their logarithmic discrepancy converges absolutely exactly
on `Re s > σ`. The harmonic series forces failure at the boundary.
-/

noncomputable section
open Complex Filter Topology Set
namespace GaloisForLFunctions.SelbergClass.PositiveFiniteEuler

/-- The positive root radius corresponding to real part `σ`. -/
def rootRadius (p : ℕ) (σ : ℝ) : ℝ := Real.exp (σ * Real.log p)

theorem rootRadius_pos (p : ℕ) (σ : ℝ) : 0 < rootRadius p σ := Real.exp_pos _

theorem rootRadius_eq_rpow {p : ℕ} (hp : 0 < p) (σ : ℝ) :
    rootRadius p σ = (p : ℝ) ^ σ := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hp), rootRadius]
  congr 1
  ring

theorem rootRadius_mul_reflection {p : ℕ} (hp : 0 < p) (σ : ℝ) :
    rootRadius p σ * rootRadius p (1 - σ) = p := by
  rw [rootRadius, rootRadius, ← Real.exp_add,
    show σ * Real.log p + (1 - σ) * Real.log p = Real.log p by ring,
    Real.exp_log (by exact_mod_cast hp)]

/-- The logarithmic discrepancy from zeta, supported on powers of one prime. -/
def localDiscrepancy (p : ℕ) (σ : ℝ) : ℕ → ℂ :=
  powerLogCoeff p (-(rootRadius p σ : ℂ)) +
    powerLogCoeff p (-(rootRadius p (1 - σ) : ℂ))

/-- This sequence is the actual difference from zeta's canonical Euler logarithm. -/
theorem localDiscrepancy_eq_sub (p : ℕ) (σ : ℝ) :
    localDiscrepancy p σ =
      eulerLogCoeff p (-(rootRadius p σ : ℂ)) (-(rootRadius p (1 - σ) : ℂ)) -
        RHTower.eulerLogDirichletCoeff := by
  funext n
  simp only [localDiscrepancy, eulerLogCoeff, Pi.add_apply, Pi.sub_apply]
  ring

/-- The two local powers have the same phase, so their norms add exactly. -/
theorem norm_localDiscrepancy_prime_pow {p : ℕ} (hp : 1 < p) (σ : ℝ) (k : ℕ) :
    ‖localDiscrepancy p σ (p ^ k)‖ =
      (rootRadius p σ ^ k + rootRadius p (1 - σ) ^ k) / (k : ℝ) := by
  let r := rootRadius p σ
  let q := rootRadius p (1 - σ)
  have hr : 0 < r := rootRadius_pos p σ
  have hq : 0 < q := rootRadius_pos p (1 - σ)
  rw [localDiscrepancy, Pi.add_apply, powerLogCoeff_pow hp, powerLogCoeff_pow hp]
  change ‖-((-(r : ℂ)) ^ k) / (k : ℂ) + -((-(q : ℂ)) ^ k) / (k : ℂ)‖ = _
  have hid : -((-(r : ℂ)) ^ k) / (k : ℂ) + -((-(q : ℂ)) ^ k) / (k : ℂ) =
      -((-1 : ℂ) ^ k * ((r : ℂ) ^ k + (q : ℂ) ^ k)) / (k : ℂ) := by
    rw [show -(r : ℂ) = (-1 : ℂ) * r by ring,
      show -(q : ℂ) = (-1 : ℂ) * q by ring, mul_pow, mul_pow]
    ring
  rw [hid, norm_div, norm_neg, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Complex.norm_natCast]
  have hreal : (r : ℂ) ^ k + (q : ℂ) ^ k = ((r ^ k + q ^ k : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private theorem natPow_rpow {p : ℕ} (hp : 0 < p) (v : ℝ) (k : ℕ) :
    ((p ^ k : ℕ) : ℝ) ^ v = ((p : ℝ) ^ v) ^ k := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Nat.cast_pow, Real.rpow_def_of_pos (pow_pos hpR k), Real.log_pow,
    Real.rpow_def_of_pos hpR, ← Real.exp_nat_mul]
  congr 1
  ring

/-- The absolute prime-power terms dominate the harmonic series on the closed left half-plane. -/
theorem harmonic_le_norm_localDiscrepancy_term {p : ℕ} (hp : p.Prime) (σ : ℝ)
    {s : ℂ} (hs : s.re ≤ σ) (k : ℕ) :
    1 / (k : ℝ) ≤ ‖LSeries.term (localDiscrepancy p σ) s (p ^ k)‖ := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hden : 0 < ((p ^ k : ℕ) : ℝ) ^ s.re :=
    Real.rpow_pos_of_pos (by exact_mod_cast pow_pos hp.pos k) _
  have hbase : (p : ℝ) ^ s.re ≤ rootRadius p σ := by
    rw [rootRadius_eq_rpow hp.pos]
    exact Real.rpow_le_rpow_of_exponent_le hpR hs
  have hnum : ((p ^ k : ℕ) : ℝ) ^ s.re ≤
      rootRadius p σ ^ k + rootRadius p (1 - σ) ^ k := by
    rw [natPow_rpow hp.pos]
    have hpow : ((p : ℝ) ^ s.re) ^ k ≤ rootRadius p σ ^ k := by gcongr
    exact hpow.trans (le_add_of_nonneg_right (pow_nonneg (rootRadius_pos p (1 - σ)).le k))
  rw [LSeries.term_of_ne_zero (pow_ne_zero k hp.ne_zero), norm_div,
    norm_localDiscrepancy_prime_pow hp.one_lt,
    Complex.norm_natCast_cpow_of_pos (pow_pos hp.pos k)]
  calc 1 / (k : ℝ) =
      (((p ^ k : ℕ) : ℝ) ^ s.re / (k : ℝ)) / ((p ^ k : ℕ) : ℝ) ^ s.re := by
        rw [div_right_comm, div_self hden.ne']
    _ ≤ (rootRadius p σ ^ k + rootRadius p (1 - σ) ^ k) / (k : ℝ) /
        ((p ^ k : ℕ) : ℝ) ^ s.re :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hnum (Nat.cast_nonneg k)) hden.le

private theorem root_log_converges {p : ℕ} (hp : p.Prime) {τ : ℝ} {s : ℂ}
    (hs : τ < s.re) : ‖-(rootRadius p τ : ℂ) * (p : ℂ) ^ (-s)‖ < 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hl : 0 < Real.log p := Real.log_pos hpR
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (rootRadius_pos p τ), Complex.norm_natCast_cpow_of_pos hp.pos,
    Complex.neg_re, Real.rpow_def_of_pos (zero_lt_one.trans hpR), rootRadius,
    ← Real.exp_add]
  apply Real.exp_lt_one_iff.mpr
  rw [show τ * Real.log p + Real.log p * -s.re = (τ - s.re) * Real.log p by ring]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hs) hl

/-- The local Taylor logarithms converge to the right of the larger root radius. -/
theorem localDiscrepancy_summable {p : ℕ} (hp : p.Prime) {σ : ℝ}
    (hσ : 1 / 2 ≤ σ) {s : ℂ} (hs : σ < s.re) :
    LSeriesSummable (localDiscrepancy p σ) s := by
  have hq : 1 - σ < s.re := by linarith only [hσ, hs]
  exact (LSeriesHasSum.add
    (hasSum_powerLogCoeff hp.one_lt _ (root_log_converges hp hs))
    (hasSum_powerLogCoeff hp.one_lt _ (root_log_converges hp hq))).LSeriesSummable

/-- The boundary fails absolute convergence because the prime powers carry a harmonic minorant. -/
theorem localDiscrepancy_not_summable {p : ℕ} (hp : p.Prime) (σ : ℝ)
    {s : ℂ} (hs : s.re ≤ σ) : ¬ LSeriesSummable (localDiscrepancy p σ) s := by
  intro hsum
  have habs : Summable (fun n : ℕ => ‖LSeries.term (localDiscrepancy p σ) s n‖) :=
    summable_norm_iff.mpr hsum
  have hpowers := habs.comp_injective (pow_right_strictMono₀ hp.one_lt).injective
  have hharm : Summable (fun k : ℕ => 1 / (k : ℝ)) :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => harmonic_le_norm_localDiscrepancy_term hp σ hs k) hpowers
  exact Real.not_summable_one_div_natCast hharm

/-- Exact absolute-convergence half-plane of the logarithmic Euler discrepancy. -/
theorem localDiscrepancy_summable_iff {p : ℕ} (hp : p.Prime) {σ : ℝ}
    (hσ : 1 / 2 ≤ σ) (s : ℂ) :
    LSeriesSummable (localDiscrepancy p σ) s ↔ σ < s.re := by
  constructor
  · intro hsum
    by_contra h
    exact localDiscrepancy_not_summable hp σ (le_of_not_gt h) hsum
  · exact localDiscrepancy_summable hp hσ

/-- The Euler discrepancy abscissa is exactly the right boundary of the added-zero strip. -/
theorem localDiscrepancy_abscissa {p : ℕ} (hp : p.Prime) {σ : ℝ}
    (hσ : 1 / 2 ≤ σ) : LSeries.abscissaOfAbsConv (localDiscrepancy p σ) = (σ : EReal) := by
  have hiff (v : ℝ) : LSeriesSummable (localDiscrepancy p σ) (v : ℂ) ↔ σ < v := by
    simpa only [Complex.ofReal_re] using localDiscrepancy_summable_iff hp hσ (v : ℂ)
  simp [LSeries.abscissaOfAbsConv, hiff, Set.Ioi_def, EReal.image_coe_Ioi]

theorem reciprocalParameter_rootRadius {p : ℕ} (hp : 0 < p) (σ : ℝ) :
    reciprocalParameter p (rootRadius p σ) = rootRadius p σ + rootRadius p (1 - σ) := by
  unfold reciprocalParameter
  rw [(div_eq_iff (rootRadius_pos p σ).ne').mpr
    (show (p : ℝ) = rootRadius p (1 - σ) * rootRadius p σ by
      rw [mul_comm, rootRadius_mul_reflection hp])]

/-- The reciprocal quadratic splits into the two prescribed negative roots. -/
theorem localFactor_zero_rootRadius_iff {p : ℕ} (hp : p.Prime) (σ : ℝ) (s : ℂ) :
    localFactor p (reciprocalParameter p (rootRadius p σ)) s = 0 ↔
      (p : ℂ) ^ s = -(rootRadius p σ : ℂ) ∨
      (p : ℂ) ^ s = -(rootRadius p (1 - σ) : ℂ) := by
  have hpC : (rootRadius p σ : ℂ) * (rootRadius p (1 - σ) : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, rootRadius_mul_reflection hp.pos, Complex.ofReal_natCast]
  rw [localFactor_zero_iff hp.ne_zero, reciprocalParameter_rootRadius hp.pos]
  have hid : ((p : ℂ) ^ s) ^ 2 +
      ((rootRadius p σ + rootRadius p (1 - σ) : ℝ) : ℂ) * (p : ℂ) ^ s + p =
      ((p : ℂ) ^ s + rootRadius p σ) * ((p : ℂ) ^ s + rootRadius p (1 - σ)) := by
    calc _ = ((p : ℂ) ^ s) ^ 2 +
        ((rootRadius p σ : ℂ) + rootRadius p (1 - σ)) * (p : ℂ) ^ s +
        (rootRadius p σ : ℂ) * rootRadius p (1 - σ) := by
          rw [hpC, Complex.ofReal_add]
      _ = _ := by ring
  rw [hid, mul_eq_zero]
  simp only [add_eq_zero_iff_eq_neg]

private theorem re_eq_of_cpow_neg_rootRadius {p : ℕ} (hp : p.Prime) (τ : ℝ) {s : ℂ}
    (hs : (p : ℂ) ^ s = -(rootRadius p τ : ℂ)) : s.re = τ := by
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hn := congrArg norm hs
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (rootRadius_pos p τ),
    Real.rpow_def_of_pos (by exact_mod_cast hp.pos), rootRadius] at hn
  apply mul_right_cancel₀ hl.ne'
  calc s.re * Real.log p = Real.log p * s.re := mul_comm _ _
    _ = τ * Real.log p := Real.exp_injective hn

/-- Every added zero lies on one of the two boundary lines. -/
theorem localFactor_zero_re_rootRadius {p : ℕ} (hp : p.Prime) (σ : ℝ) {s : ℂ}
    (hs : localFactor p (reciprocalParameter p (rootRadius p σ)) s = 0) :
    s.re = σ ∨ s.re = 1 - σ := by
  rcases (localFactor_zero_rootRadius_iff hp σ s).mp hs with hr | hq
  · exact Or.inl (re_eq_of_cpow_neg_rootRadius hp σ hr)
  · exact Or.inr (re_eq_of_cpow_neg_rootRadius hp (1 - σ) hq)

theorem factorZero_rootRadius_re {p : ℕ} (hp : p.Prime) (σ : ℝ) :
    (factorZero p (rootRadius p σ)).re = σ := by
  rw [factorZero_re, rootRadius, Real.log_exp]
  exact mul_div_cancel_right₀ _ (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'

/-- Both boundary lines are attained by added zeros. -/
theorem added_zero_on_each_boundary {p : ℕ} (hp : p.Prime) (σ : ℝ) :
    (∃ s : ℂ, localFactor p (reciprocalParameter p (rootRadius p σ)) s = 0 ∧ s.re = σ) ∧
    (∃ s : ℂ, localFactor p (reciprocalParameter p (rootRadius p σ)) s = 0 ∧ s.re = 1 - σ) := by
  constructor
  · exact ⟨factorZero p (rootRadius p σ),
      localFactor_factorZero hp.one_lt (rootRadius_pos p σ), factorZero_rootRadius_re hp σ⟩
  · refine ⟨factorZero p (rootRadius p (1 - σ)), ?_, factorZero_rootRadius_re hp (1 - σ)⟩
    exact (localFactor_zero_rootRadius_iff hp σ _).mpr
      (Or.inr (cpow_factorZero hp.one_lt (rootRadius_pos p (1 - σ))))

/-- An actual added zero attains the Euler discrepancy abscissa and the relative-strip depth bound. -/
theorem added_zero_attains_euler_abscissa {p : ℕ} (hp : p.Prime) {σ : ℝ}
    (hσ : 1 / 2 ≤ σ) :
    ∃ s : ℂ, localFactor p (reciprocalParameter p (rootRadius p σ)) s = 0 ∧
      (s.re : EReal) = LSeries.abscissaOfAbsConv (localDiscrepancy p σ) ∧
      |s.re - 1 / 2| = σ - 1 / 2 := by
  obtain ⟨s, hz, hre⟩ := (added_zero_on_each_boundary hp σ).1
  refine ⟨s, hz, ?_, ?_⟩
  · rw [hre, localDiscrepancy_abscissa hp hσ]
  · rw [hre, abs_of_nonneg (sub_nonneg.mpr hσ)]

end GaloisForLFunctions.SelbergClass.PositiveFiniteEuler

