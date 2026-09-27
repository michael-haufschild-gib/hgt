import GaloisForLFunctions.RHTower.STCPrimeBoundaryTangentSpace

/-!
# The critical prime source escapes to a Gamma law in the coordinate `v log p`

For `a, v > 0` the probability measures

`μ_{a,v} = S(av)^{-1} Σ_p b_{av}(p)² δ_{v log p}`

have Laplace transforms `S((a+λ)v)/S(av)` and characteristic functions
`F(av - iξv)/F(av)`.  The moving pole scaling gives `(a/(a+λ))²` and `(a/(a - iξ))²` in the limit
`v → 0⁺`, and Lévy's continuity theorem gives weak convergence of `μ_{a,v}` to the Gamma law with
density `a² t e^{-at}` on `(0, ∞)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

/-- The prime weights `b_{av}(p)²/S(av)`. -/
def primeBoundaryWeight (a v : ℝ) (p : Nat.Primes) : ℝ :=
  stcDepthZeroAmplitude (a * v) p ^ 2 / ‖stcBoundaryVec (a * v)‖ ^ 2

/-- The boundary law `μ_{a,v} = Σ_p (b_{av}(p)²/S(av)) δ_{v log p}`. -/
def primeBoundaryLaw (a v : ℝ) : Measure ℝ :=
  Measure.sum fun p : Nat.Primes =>
    ENNReal.ofReal (primeBoundaryWeight a v p) • Measure.dirac (v * Real.log (p : ℕ))

theorem primeBoundaryWeight_nonneg (a v : ℝ) (p : Nat.Primes) : 0 ≤ primeBoundaryWeight a v p :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem norm_sq_stcBoundaryVec_pos {u : ℝ} (hu : 0 < u) : 0 < ‖stcBoundaryVec u‖ ^ 2 := by
  rw [norm_sq_stcBoundaryVec hu]
  exact (summable_stcDepthZeroAmplitude_sq_iff u).mpr hu |>.tsum_pos
    (fun p => sq_nonneg _) ⟨2, Nat.prime_two⟩ (pow_pos (stcDepthZeroAmplitude_pos u _) 2)

theorem summable_primeBoundaryWeight {a v : ℝ} (hav : 0 < a * v) :
    Summable (primeBoundaryWeight a v) :=
  ((summable_stcDepthZeroAmplitude_sq_iff (a * v)).mpr hav).div_const _

theorem tsum_primeBoundaryWeight {a v : ℝ} (hav : 0 < a * v) :
    ∑' p, primeBoundaryWeight a v p = 1 := by
  unfold primeBoundaryWeight
  rw [tsum_div_const, ← norm_sq_stcBoundaryVec hav, div_self (norm_sq_stcBoundaryVec_pos hav).ne']

theorem isProbabilityMeasure_primeBoundaryLaw {a v : ℝ} (hav : 0 < a * v) :
    IsProbabilityMeasure (primeBoundaryLaw a v) := by
  constructor
  rw [primeBoundaryLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (primeBoundaryWeight_nonneg a v)
    (summable_primeBoundaryWeight hav), tsum_primeBoundaryWeight hav, ENNReal.ofReal_one]

/-- `μ_{a,v}` is carried by `[0, ∞)`. -/
theorem ae_primeBoundaryLaw_nonneg (a : ℝ) {v : ℝ} (hv : 0 < v) :
    ∀ᵐ x ∂primeBoundaryLaw a v, 0 ≤ x := by
  rw [primeBoundaryLaw, Measure.ae_sum_iff' (measurableSet_Ici (a := (0 : ℝ)))]
  intro p
  refine Measure.smul_absolutelyContinuous.ae_le
    ((ae_dirac_iff (measurableSet_Ici (a := (0 : ℝ)))).mpr ?_)
  exact mul_nonneg hv.le (Real.log_nonneg (by exact_mod_cast p.property.one_lt.le))

/-- Integration against `μ_{a,v}` of a continuous function bounded on `[0,∞)` is the weighted prime
sum. -/
theorem integral_primeBoundaryLaw {a v : ℝ} (hav : 0 < a * v) (hv : 0 < v) (f : ℝ → ℂ)
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, 0 ≤ x → ‖f x‖ ≤ C) :
    ∫ x, f x ∂primeBoundaryLaw a v =
      ∑' p : Nat.Primes, (primeBoundaryWeight a v p : ℂ) * f (v * Real.log (p : ℕ)) := by
  haveI := isProbabilityMeasure_primeBoundaryLaw hav
  have hint : Integrable f (primeBoundaryLaw a v) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      ((ae_primeBoundaryLaw_nonneg a hv).mono fun x hx => hC x hx)
  rw [primeBoundaryLaw, integral_sum_measure hint]
  refine tsum_congr fun p => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (primeBoundaryWeight_nonneg a v p),
    Complex.real_smul]

theorem ofReal_norm_sq_stcBoundaryVec {u : ℝ} (hu : 0 < u) :
    ((‖stcBoundaryVec u‖ ^ 2 : ℝ) : ℂ) = primeLogSquareComplex (1 + ((u : ℝ) : ℂ)) := by
  rw [← inner_self_ofReal_norm_sq, inner_stcBoundaryVec hu hu, show (u + u) / 2 = u by ring]

/-- The weighted exponential prime sum is a value of `F`. -/
theorem tsum_amplitude_sq_exp (u : ℝ) (w : ℂ) :
    ∑' p : Nat.Primes, ((stcDepthZeroAmplitude u p ^ 2 : ℝ) : ℂ) *
        Complex.exp (w * (Real.log (p : ℕ) : ℂ)) =
      primeLogSquareComplex (1 + ((u : ℝ) : ℂ) - w) := by
  rw [primeLogSquareComplex_eq_tsum_exp]
  refine tsum_congr fun p => ?_
  rw [stcDepthZeroAmplitude_eq_exp, mul_pow, ← Real.exp_nat_mul]
  push_cast
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem tsum_weight_exp {a v : ℝ} (hav : 0 < a * v) (w : ℂ) :
    ∑' p : Nat.Primes, (primeBoundaryWeight a v p : ℂ) * Complex.exp (w * (Real.log (p : ℕ) : ℂ)) =
      primeLogSquareComplex (1 + ((a * v : ℝ) : ℂ) - w) /
        primeLogSquareComplex (1 + ((a * v : ℝ) : ℂ)) := by
  rw [← ofReal_norm_sq_stcBoundaryVec hav, ← tsum_amplitude_sq_exp, ← tsum_div_const]
  refine tsum_congr fun p => ?_
  rw [primeBoundaryWeight]
  push_cast
  ring

/-- **Characteristic function.** `φ_{a,v}(ξ) = F(av - iξv)/F(av)`. -/
theorem charFun_primeBoundaryLaw {a v : ℝ} (hav : 0 < a * v) (hv : 0 < v) (ξ : ℝ) :
    charFun (primeBoundaryLaw a v) ξ =
      primeLogSquareComplex (1 + ((a * v : ℝ) : ℂ) - ((ξ * v : ℝ) : ℂ) * Complex.I) /
        primeLogSquareComplex (1 + ((a * v : ℝ) : ℂ)) := by
  rw [charFun_apply_real, integral_primeBoundaryLaw hav hv _ (by fun_prop) (C := 1)
    (fun x _ => by rw [Complex.norm_exp]; simp), ← tsum_weight_exp hav]
  refine tsum_congr fun p => ?_
  congr 2
  push_cast
  ring

/-- **Laplace transform.** `∫ e^{-λx} dμ_{a,v} = S((a+λ)v)/S(av)` for `λ ≥ 0`. -/
theorem laplace_primeBoundaryLaw {a v l : ℝ} (ha : 0 < a) (hv : 0 < v) (hl : 0 ≤ l) :
    ∫ x, Real.exp (-(l * x)) ∂primeBoundaryLaw a v =
      ‖stcBoundaryVec ((a + l) * v)‖ ^ 2 / ‖stcBoundaryVec (a * v)‖ ^ 2 := by
  have hav : 0 < a * v := mul_pos ha hv
  have halv : 0 < (a + l) * v := mul_pos (by linarith) hv
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, integral_primeBoundaryLaw hav hv _ (by fun_prop) (C := 1)
    (fun x hx => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith))]
  have e : ∀ p : Nat.Primes, ((Real.exp (-(l * (v * Real.log (p : ℕ)))) : ℝ) : ℂ) =
      Complex.exp ((-(l * v) : ℂ) * (Real.log (p : ℕ) : ℂ)) := fun p => by
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  simp_rw [e]
  rw [tsum_weight_exp hav, ← ofReal_norm_sq_stcBoundaryVec hav,
    show (1 : ℂ) + ((a * v : ℝ) : ℂ) - -((l : ℂ) * (v : ℂ)) = 1 + (((a + l) * v : ℝ) : ℂ) by
      push_cast; ring, ← ofReal_norm_sq_stcBoundaryVec halv, Complex.ofReal_div]

/-- **Laplace limit.** `S((a+λ)v)/S(av) → (a/(a+λ))²`. -/
theorem tendsto_laplace_primeBoundaryLaw {a l : ℝ} (ha : 0 < a) (hl : 0 ≤ l) :
    Tendsto (fun v => ∫ x, Real.exp (-(l * x)) ∂primeBoundaryLaw a v) (𝓝[>] 0)
      (𝓝 ((a / (a + l)) ^ 2)) := by
  have hal : 0 < a + l := by linarith
  have h := (tendsto_norm_sq_tangentProbe hal).div (tendsto_norm_sq_tangentProbe ha)
    (by positivity)
  rw [show 1 / (a + l) ^ 2 / (1 / a ^ 2) = (a / (a + l)) ^ 2 by field_simp] at h
  have hprobe : ∀ c v : ℝ, ‖tangentProbe c v‖ ^ 2 = v ^ 2 * ‖stcBoundaryVec (c * v)‖ ^ 2 := by
    intro c v
    rw [tangentProbe, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv' : (0 : ℝ) < v := hv
  rw [Pi.div_apply, laplace_primeBoundaryLaw ha hv' hl, hprobe, hprobe]
  have hS := norm_sq_stcBoundaryVec_pos (mul_pos ha hv')
  have hv2 : 0 < v ^ 2 := by positivity
  field_simp

/-- **Characteristic function limit.** `φ_{a,v}(ξ) → (a/(a - iξ))²`. -/
theorem tendsto_charFun_primeBoundaryLaw {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    Tendsto (fun v => charFun (primeBoundaryLaw a v) ξ) (𝓝[>] 0)
      (𝓝 (((a : ℂ) / ((a : ℂ) - (ξ : ℂ) * Complex.I)) ^ 2)) := by
  have hw₁ : 0 < ((a : ℂ) - (ξ : ℂ) * Complex.I).re := by simp [ha]
  have hw₂ : 0 < ((a : ℂ)).re := by simp [ha]
  have hn := tendsto_sq_mul_primeLogSquareComplex hw₁ (tendsto_const_nhds (x := (a : ℂ) - ξ * Complex.I))
  have hd := tendsto_sq_mul_primeLogSquareComplex hw₂ (tendsto_const_nhds (x := (a : ℂ)))
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hq := hn.div hd (inv_ne_zero (pow_ne_zero 2 ha0))
  have hw0 : (a : ℂ) - (ξ : ℂ) * Complex.I ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hw₁; exact lt_irrefl _ hw₁
  rw [show ((((a : ℂ) - (ξ : ℂ) * Complex.I) ^ 2)⁻¹ / ((a : ℂ) ^ 2)⁻¹) =
    ((a : ℂ) / ((a : ℂ) - (ξ : ℂ) * Complex.I)) ^ 2 by field_simp] at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv' : (0 : ℝ) < v := hv
  have hvc : (v : ℂ) ≠ 0 := by exact_mod_cast hv'.ne'
  rw [Pi.div_apply, charFun_primeBoundaryLaw (mul_pos ha hv') hv',
    mul_div_mul_left _ _ (pow_ne_zero 2 hvc)]
  congr 2 <;> push_cast <;> ring

/-- `∫₀^∞ x e^{-wx} dx = 1/w²` for `Re w > 0`. -/
theorem integral_Ioi_mul_cexp_neg {w : ℂ} (hw : 0 < w.re) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) * Complex.exp (-w * x) = 1 / w ^ 2 := by
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; exact lt_irrefl _ hw
  set G : ℝ → ℂ := fun x => ((x : ℂ) / w + 1 / w ^ 2) * Complex.exp (-w * x)
  have hderiv : ∀ x : ℝ, HasDerivAt G (-((x : ℂ) * Complex.exp (-w * x))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) / w + 1 / w ^ 2) (1 / w) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp.div_const w).add_const (1 / w ^ 2)
    have h2 : HasDerivAt (fun x : ℝ => Complex.exp (-w * x)) (Complex.exp (-w * x) * (-w)) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp.const_mul (-w)).cexp
    exact (h1.mul h2).congr_deriv (by field_simp; ring)
  have hbound : ∀ x : ℝ, ‖(x : ℂ) * Complex.exp (-w * x)‖ = |x| * Real.exp (-(w.re * x)) := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    simp
  have hint : IntegrableOn (fun x : ℝ => (x : ℂ) * Complex.exp (-w * x)) (Ioi 0) := by
    refine (integrableOn_Ioi_mul_exp_neg hw).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [hbound, abs_of_pos hx]
  have hlim : Tendsto G atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 w.re hw
    have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 w.re hw
    have hsum := (h1.const_mul ‖w‖⁻¹).add (h0.const_mul (‖w‖ ^ 2)⁻¹)
    simp only [mul_zero, add_zero] at hsum
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hsum
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [norm_mul, Complex.norm_exp, Real.rpow_one, Real.rpow_zero, one_mul]
    have hre : (-w * (x : ℂ)).re = -w.re * x := by simp
    rw [hre]
    have hn : ‖(x : ℂ) / w + 1 / w ^ 2‖ ≤ ‖w‖⁻¹ * x + (‖w‖ ^ 2)⁻¹ := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_div, norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hx]
      ring
    nlinarith [Real.exp_pos (-w.re * x), norm_nonneg ((x : ℂ) / w + 1 / w ^ 2)]
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    have : Continuous G := by simp only [G]; fun_prop
    exact this.continuousWithinAt
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun x _ => hderiv x) hint.neg hlim
  rw [integral_neg] at h
  have hG0 : G 0 = 1 / w ^ 2 := by simp [G]
  rw [hG0, zero_sub] at h
  exact neg_injective h

/-- **Characteristic function of the Gamma law** of shape `2` and rate `a`. -/
theorem charFun_gammaMeasure_two {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    charFun (gammaMeasure 2 a) ξ = ((a : ℂ) / ((a : ℂ) - (ξ : ℂ) * Complex.I)) ^ 2 := by
  have hw : 0 < ((a : ℂ) - (ξ : ℂ) * Complex.I).re := by simp [ha]
  have hw0 : (a : ℂ) - (ξ : ℂ) * Complex.I ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hw; exact lt_irrefl _ hw
  rw [charFun_apply_real, gammaMeasure, integral_withDensity_eq_integral_toReal_smul
    (f := gammaPDF 2 a) (by exact (measurable_gammaPDFReal 2 a).ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have hsplit : ∫ x, (gammaPDF 2 a x).toReal • Complex.exp ((ξ : ℂ) * x * Complex.I) =
      ∫ x in Ioi (0 : ℝ), ((a ^ 2 : ℝ) : ℂ) * ((x : ℂ) * Complex.exp (-((a : ℂ) - ξ * Complex.I) * x)) := by
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae ?_
    refine Eventually.of_forall fun x => ?_
    beta_reduce
    by_cases h0 : 0 < x
    · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from h0), gammaPDF_of_nonneg h0.le,
        ENNReal.toReal_ofReal (by positivity), Real.Gamma_two, div_one, Complex.real_smul,
        show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]
      push_cast
      rw [mul_assoc, mul_assoc, ← Complex.exp_add]
      congr 3
      ring
    · rw [Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from h0)]
      rcases (not_lt.mp h0).lt_or_eq with hneg | hzero
      · rw [gammaPDF_of_neg hneg, ENNReal.toReal_zero, zero_smul]
      · subst hzero
        rw [gammaPDF_of_nonneg le_rfl, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_zero,
          zero_mul, ENNReal.ofReal_zero, ENNReal.toReal_zero, zero_smul]
  rw [hsplit, integral_const_mul, integral_Ioi_mul_cexp_neg hw]
  push_cast
  field_simp

/-- The Gamma law as a probability measure. -/
def gammaLawTwo (a : ℝ) (ha : 0 < a) : ProbabilityMeasure ℝ :=
  ⟨gammaMeasure 2 a, isProbabilityMeasure_gammaMeasure two_pos ha⟩

/-- The boundary law as a probability measure (the Gamma law for `v ≤ 0`, where it is not used). -/
def primeBoundaryProbability (a : ℝ) (ha : 0 < a) (v : ℝ) : ProbabilityMeasure ℝ :=
  if hv : 0 < v then ⟨primeBoundaryLaw a v, isProbabilityMeasure_primeBoundaryLaw (mul_pos ha hv)⟩
  else gammaLawTwo a ha

/-- **Escape to the Gamma law.** `μ_{a,v}` converges weakly, as `v → 0⁺`, to the Gamma law with
density `a² t e^{-at}` on `(0, ∞)`. -/
theorem tendsto_primeBoundaryProbability {a : ℝ} (ha : 0 < a) :
    Tendsto (primeBoundaryProbability a ha) (𝓝[>] 0) (𝓝 (gammaLawTwo a ha)) := by
  rw [tendsto_iff_seq_tendsto]
  intro x hx
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro ξ
  have hpos : ∀ᶠ n in atTop, 0 < x n := (tendsto_nhdsWithin_iff.mp hx).2
  have h := (tendsto_charFun_primeBoundaryLaw ha ξ).comp hx
  rw [gammaLawTwo, ProbabilityMeasure.coe_mk, charFun_gammaMeasure_two ha]
  refine h.congr' ?_
  filter_upwards [hpos] with n hn
  simp only [Function.comp_apply, primeBoundaryProbability, dif_pos hn, ProbabilityMeasure.coe_mk]

end

end RHTower
