import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleCharFun
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ModulusDivergence

/-!
# The socle observable has no limit law in the condensed chamber

The characteristic function of a finite-mode socle observable is a product of geometric factors
`(1 − q)/(1 − q e^{iφ})`, each of modulus at most one.  The modulus deficit of a single factor is
bounded below by `q(1 − cos φ)/4`, so summing over the depth-one modes of the primes reproduces the
leading term of the modulus budget — which diverges for `1/2 < σ ≤ 1` and every nonzero phase.

Hence the characteristic functions of the partial sums tend to `0` at every nonzero argument, no
matter how the modes are centred, and no limit law exists.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The characteristic function of a geometric occupation with ratio `q` and phase `φ`. -/
noncomputable def geomFactor (q φ : ℝ) : ℂ :=
  (1 - (q : ℂ)) / (1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I))

theorem norm_sq_one_sub_geom (q φ : ℝ) :
    ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ ^ 2
      = (1 - q) ^ 2 + 2 * q * (1 - Real.cos φ) := by
  have hre : (Complex.exp ((φ : ℝ) * Complex.I)).re = Real.cos φ :=
    Complex.exp_ofReal_mul_I_re φ
  have him : (Complex.exp ((φ : ℝ) * Complex.I)).im = Real.sin φ :=
    Complex.exp_ofReal_mul_I_im φ
  have hsq := Real.sin_sq_add_cos_sq φ
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, hre, him]
  simp only [Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (q ^ 2) * hsq

theorem norm_one_sub_geom_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (φ : ℝ) :
    0 < ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ := by
  have hcos := Real.cos_le_one φ
  have hsq : (0 : ℝ) < ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ ^ 2 := by
    rw [norm_sq_one_sub_geom]
    nlinarith
  refine lt_of_le_of_ne (norm_nonneg _) (Ne.symm ?_)
  intro h
  rw [h] at hsq
  simp at hsq

/-- The modulus deficit of one geometric characteristic factor. -/
noncomputable def geomDefect (q φ : ℝ) : ℝ := -Real.log ‖geomFactor q φ‖

theorem norm_geomFactor {q : ℝ} (hq1 : q < 1) (φ : ℝ) :
    ‖geomFactor q φ‖
      = (1 - q) / ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ := by
  rw [geomFactor, norm_div]
  congr 1
  rw [show (1 : ℂ) - (q : ℂ) = ((1 - q : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith)]

/-- **The deficit of one mode is at least a quarter of its leading term.** -/
theorem geomDefect_ge {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (φ : ℝ) :
    q * (1 - Real.cos φ) / 4 ≤ geomDefect q φ := by
  have hcos := Real.neg_one_le_cos φ
  have hcos' := Real.cos_le_one φ
  have hbase : (0 : ℝ) < 1 - q := by linarith
  have hD : ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ ^ 2
      = (1 - q) ^ 2 + 2 * q * (1 - Real.cos φ) := norm_sq_one_sub_geom q φ
  have hDpos : (0 : ℝ) < ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ :=
    norm_one_sub_geom_pos hq0 hq1 φ
  have hD2pos : (0 : ℝ) < ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ ^ 2 := by positivity
  have hDle : ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ ^ 2 ≤ 4 := by
    rw [hD]; nlinarith
  have hlog : geomDefect q φ
      = (Real.log (‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ ^ 2)
          - Real.log ((1 - q) ^ 2)) / 2 := by
    rw [geomDefect, norm_geomFactor hq1, Real.log_div hbase.ne' hDpos.ne',
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hkey : 1 - (1 - q) ^ 2 / ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ ^ 2
      ≤ Real.log (‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ ^ 2)
        - Real.log ((1 - q) ^ 2) := by
    have hpos : (0 : ℝ) < (1 - q) ^ 2
        / ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ ^ 2 := by positivity
    have hle := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by positivity) (by positivity)] at hle
    linarith
  have hfrac : q * (1 - Real.cos φ) / 2
      ≤ 1 - (1 - q) ^ 2 / ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ ^ 2 := by
    have heq : 1 - (1 - q) ^ 2 / ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ ^ 2
        = (2 * q * (1 - Real.cos φ))
          / ‖1 - (q : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ ^ 2 := by
      field_simp
      linarith [hD]
    rw [heq, le_div_iff₀ hD2pos]
    nlinarith [mul_nonneg hq0.le (by linarith : (0 : ℝ) ≤ 1 - Real.cos φ)]
  rw [hlog]
  linarith

theorem geomDefect_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (φ : ℝ) :
    0 ≤ geomDefect q φ := by
  have hcos := Real.cos_le_one φ
  have hge := geomDefect_ge hq0 hq1 φ
  nlinarith

/-! ## The gas modes -/

/-- The realization deficit of one gas mode at characteristic argument `t`. -/
noncomputable def gasModeDefect {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (m : AbelianZetaMode) : ℝ :=
  geomDefect ((AbelianZetaParameters.temperatureParameters σ hσ).ratio m) (socleCoeff σ t m.1)

theorem gasModeDefect_nonneg {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (m : AbelianZetaMode) :
    0 ≤ gasModeDefect hσ t m :=
  geomDefect_nonneg
    ((AbelianZetaParameters.temperatureParameters σ hσ).ratio_pos m)
    ((AbelianZetaParameters.temperatureParameters σ hσ).ratio_lt_one m) _

theorem cos_socleCoeff {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (p : Nat.Primes) :
    Real.cos (socleCoeff σ t p) = Real.cos (phaseAngle (primeNome hσ p) t) := by
  rw [socleCoeff, phaseAngle_primeNome, ← Real.cos_neg (t * σ * Real.log ((p : ℕ) : ℝ))]
  congr 1
  ring

/-- **The mode deficits are not summable** in the condensed chamber, for every nonzero `t`:
the depth-one modes alone reproduce a quarter of the leading term of the modulus budget. -/
theorem not_summable_gasModeDefect {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    {t : ℝ} (ht : t ≠ 0) : ¬ Summable (gasModeDefect hσ t) := by
  intro hsum
  have hinj : Function.Injective (fun p : Nat.Primes => ((p, 0) : AbelianZetaMode)) := by
    intro i j hij
    exact (Prod.mk.injEq _ _ _ _ ▸ hij).1
  have hrestrict := hsum.comp_injective hinj
  refine not_summable_leading hσ hσ1 ht ?_
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hrestrict.mul_left 4)
  · have hcos := Real.cos_le_one (phaseAngle (primeNome hσ p) t)
    have hq : 0 < (primeNome hσ p).val := (primeNome hσ p).pos
    nlinarith
  · have hge := geomDefect_ge
      ((AbelianZetaParameters.temperatureParameters σ hσ).ratio_pos ((p, 0) : AbelianZetaMode))
      ((AbelianZetaParameters.temperatureParameters σ hσ).ratio_lt_one ((p, 0) : AbelianZetaMode))
      (socleCoeff σ t p)
    rw [ratio_temperatureParameters hσ p 0, cos_socleCoeff hσ t p] at hge
    simp only [Function.comp_apply, gasModeDefect]
    rw [pow_one] at hge
    rw [ratio_temperatureParameters hσ p 0, pow_one]
    linarith

/-! ## The characteristic functions of the finite-mode partial sums -/

/-- The centred socle observable over a finite set of modes. -/
noncomputable def socleSum {σ : ℝ} (_hσ : 0 < σ) (c : AbelianZetaMode → ℝ)
    (s : Finset AbelianZetaMode) (k : AbelianZetaMode → ℕ) : ℝ :=
  ∑ m ∈ s, (socleCoeff σ 1 m.1 * k m - c m)

theorem measurable_socleSum {σ : ℝ} (hσ : 0 < σ) (c : AbelianZetaMode → ℝ)
    (s : Finset AbelianZetaMode) : Measurable (socleSum hσ c s) := by
  refine Finset.measurable_sum s fun m _ => ?_
  exact ((measurable_pi_apply m).natCast.const_mul _).sub measurable_const

/-- The law of the centred socle observable over a finite set of modes. -/
noncomputable def socleLaw {σ : ℝ} (hσ : 0 < σ) (c : AbelianZetaMode → ℝ)
    (s : Finset AbelianZetaMode) : Measure ℝ :=
  (AbelianZetaParameters.temperatureParameters σ hσ).gasMeasure.map (socleSum hσ c s)

instance socleLaw_isProbability {σ : ℝ} (hσ : 0 < σ) (c : AbelianZetaMode → ℝ)
    (s : Finset AbelianZetaMode) : IsProbabilityMeasure (socleLaw hσ c s) :=
  isProbabilityMeasure_map (measurable_socleSum hσ c s).aemeasurable

/-- **The modulus of the characteristic function is the exponential of minus the mode deficit.** -/
theorem norm_charFun_socleLaw {σ : ℝ} (hσ : 0 < σ) (c : AbelianZetaMode → ℝ)
    (s : Finset AbelianZetaMode) (t : ℝ) :
    ‖charFun (socleLaw hσ c s) t‖ = Real.exp (-∑ m ∈ s, gasModeDefect hσ t m) := by
  classical
  have hmeas := measurable_socleSum hσ c s
  have hcf : charFun (socleLaw hσ c s) t
      = ∫ k, Complex.exp ((socleSum hσ c s k * t : ℝ) * Complex.I)
          ∂(AbelianZetaParameters.temperatureParameters σ hσ).gasMeasure := by
    rw [charFun_apply_real, socleLaw,
      integral_map hmeas.aemeasurable
        (Measurable.aestronglyMeasurable (by fun_prop))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => by push_cast; ring_nf)
  have hsplit : ∀ k : AbelianZetaMode → ℕ,
      Complex.exp ((socleSum hσ c s k * t : ℝ) * Complex.I)
        = Complex.exp ((-(t * ∑ m ∈ s, c m) : ℝ) * Complex.I)
          * Complex.exp ((∑ m ∈ s, socleCoeff σ t m.1 * k m : ℝ) * Complex.I) := by
    intro k
    rw [← Complex.exp_add]
    congr 1
    rw [socleSum, Finset.sum_sub_distrib]
    push_cast
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    have hcoeff : ∀ m ∈ s, socleCoeff σ 1 m.1 * (k m : ℝ) * t
        = socleCoeff σ t m.1 * (k m : ℝ) := by
      intro m _
      rw [socleCoeff, socleCoeff]
      ring
    rw [show (∑ m ∈ s, socleCoeff σ 1 m.1 * (k m : ℝ)) = ∑ m ∈ s, socleCoeff σ 1 m.1 * (k m : ℝ)
      from rfl]
    push_cast
    rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl hcoeff]
    ring
  rw [hcf]
  simp only [hsplit]
  rw [MeasureTheory.integral_const_mul,
    AbelianZetaParameters.integral_gasMeasure_expo_finset, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul, norm_prod, Real.exp_neg, Real.exp_sum]
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  have hq0 : (0 : ℝ) < (AbelianZetaParameters.temperatureParameters σ hσ).ratio m :=
    (AbelianZetaParameters.temperatureParameters σ hσ).ratio_pos m
  have hq1 : (AbelianZetaParameters.temperatureParameters σ hσ).ratio m < 1 :=
    (AbelianZetaParameters.temperatureParameters σ hσ).ratio_lt_one m
  have hpos : 0 < ‖geomFactor ((AbelianZetaParameters.temperatureParameters σ hσ).ratio m)
      (socleCoeff σ t m.1)‖ := by
    rw [norm_geomFactor hq1]
    have := norm_one_sub_geom_pos hq0 hq1 (socleCoeff σ t m.1)
    positivity
  rw [gasModeDefect, geomDefect, Real.exp_neg, Real.exp_log hpos, inv_inv]
  rfl

end GaloisForLFunctions.HTGeometry
