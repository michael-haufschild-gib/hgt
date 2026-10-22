import GaloisForLFunctions.RHTower.Suzuki.SuzukiForcedStripParticular
import GaloisForLFunctions.HTGeometry.PowerTailIntegral

/-!
# Forced Gamma transport: exact upper-strip gluing and the weighted source criterion

The forced boundary problem on the two real-frequency channels carries the same particular solution
on both sides, because all half-power monodromy in it cancels.  Hence the forced gluing criterion is
exactly the homogeneous one: the two boundary solutions glue into a single holomorphic strip
solution precisely when the endpoint half-log trace vanishes, that is when `c₋ = -ic₊`.

Quantitatively, the exact Gamma quotient gives on the line `z = x + iσ`

`‖H(x+iσ)‖ ≤ K(1+|x|)^{-1/2-σ},   ‖H(x+iσ)^{-1}‖ ≤ A(1+|x|)^{1/2+σ}`,

so a weighted source bound `∫(1+|x|)^{1/2+σ}‖b(x+iσ)‖dx < ∞` makes the variation-of-constants
bracket uniformly bounded, and the remaining propagator power has square exponent `1+2σ > 1`.  The
forced solution is therefore square integrable on the whole shifted line.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

section Gluing

omit [Nontrivial X] in
/-- **Theorem 2, `(11)`.**  Zero endpoint trace, the channel relation `c₋ = -i c₊`, and gluing of
the two forced boundary solutions into one holomorphic strip solution are equivalent.  The
particular solution is common to both channels by branch cancellation, so the forced criterion is
exactly the homogeneous one. -/
theorem forcedGlue_iff_halfLogScatter_eq_zero {E : ℂ → ℂ} {T : X →L[ℂ] X}
    (hE : E ((-1 : ℝ) : ℂ) ≠ 0) (b : ℂ → X) (cp cm : X) :
    halfLogScatter cp cm = 0
      ↔ (∀ η : ℝ, η < 0 →
          stripSolution E T cp (η : ℂ) + forcedParticular E T b (η : ℂ)
            = (((-η) ^ (-(1 : ℝ) / 2) : ℝ)) • stripTransport E T (η : ℂ) cm
              + forcedParticular E T b (η : ℂ)) := by
  rw [halfLogScatter_eq_zero_iff_glue hE cp cm]
  constructor
  · intro h η hη
    rw [h η hη]
  · intro h η hη
    exact add_right_cancel (h η hη)

omit [Nontrivial X] in
/-- The forced boundary solution on the negative channel equals the one carried by `c₋ = -i c₊`. -/
theorem forcedGlue_of_channel {E : ℂ → ℂ} {T : X →L[ℂ] X} (b : ℂ → X) (cp cm : X)
    (h : cm = (-Complex.I) • cp) {η : ℝ} (hη : η < 0) :
    stripSolution E T cp (η : ℂ) + forcedParticular E T b (η : ℂ)
      = (((-η) ^ (-(1 : ℝ) / 2) : ℝ)) • stripTransport E T (η : ℂ) cm
        + forcedParticular E T b (η : ℂ) := by
  rw [stripSolution_ofReal_neg E T cp hη, h]

omit [Nontrivial X] in
/-- **`(9)`, uniqueness of the positive channel vector.**  The forced boundary solution determines
its channel vector, because the particular solution is common to both representations and the
transport is injective. -/
theorem forcedChannel_pos_unique {E : ℂ → ℂ} {T : X →L[ℂ] X} (b : ℂ → X) {η : ℝ} (hη : 0 < η)
    (hE : E ((η : ℝ) : ℂ) ≠ 0) (c c' : X)
    (h : stripSolution E T c ((η : ℝ) : ℂ) + forcedParticular E T b ((η : ℝ) : ℂ)
      = stripSolution E T c' ((η : ℝ) : ℂ) + forcedParticular E T b ((η : ℝ) : ℂ)) :
    c = c' := by
  have hhom : stripSolution E T c ((η : ℝ) : ℂ) = stripSolution E T c' ((η : ℝ) : ℂ) :=
    add_right_cancel h
  rw [stripSolution_ofReal_pos E T c hη, stripSolution_ofReal_pos E T c' hη] at hhom
  have hscal : ((η ^ (-(1 : ℝ) / 2) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hη _)
  have hsub : stripTransport E T ((η : ℝ) : ℂ) c = stripTransport E T ((η : ℝ) : ℂ) c' := by
    have hz := sub_eq_zero.mpr hhom
    rw [← smul_sub] at hz
    have := (smul_eq_zero.mp hz).resolve_left (by simpa using hscal)
    exact sub_eq_zero.mp this
  exact stripTransport_injective hE hsub

omit [Nontrivial X] in
/-- **`(9)`, uniqueness of the negative channel vector.** -/
theorem forcedChannel_neg_unique {E : ℂ → ℂ} {T : X →L[ℂ] X} (b : ℂ → X) {η : ℝ} (hη : η < 0)
    (hE : E ((η : ℝ) : ℂ) ≠ 0) (c c' : X)
    (h : (((-η) ^ (-(1 : ℝ) / 2) : ℝ)) • stripTransport E T ((η : ℝ) : ℂ) c
          + forcedParticular E T b ((η : ℝ) : ℂ)
      = (((-η) ^ (-(1 : ℝ) / 2) : ℝ)) • stripTransport E T ((η : ℝ) : ℂ) c'
          + forcedParticular E T b ((η : ℝ) : ℂ)) :
    c = c' := by
  have hhom := add_right_cancel h
  have hscal : (((-η) ^ (-(1 : ℝ) / 2) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
  have hsub : stripTransport E T ((η : ℝ) : ℂ) c = stripTransport E T ((η : ℝ) : ℂ) c' := by
    have hz := sub_eq_zero.mpr hhom
    rw [← smul_sub] at hz
    have := (smul_eq_zero.mp hz).resolve_left (by simpa using hscal)
    exact sub_eq_zero.mp this
  exact stripTransport_injective hE hsub

end Gluing

section LineBounds

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- **`(12)`: the exact Gamma quotient bounds the propagator and its inverse on a shifted line.** -/
theorem exists_stripPropagator_line_bounds (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧
      (∀ x : ℝ, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
        ≤ K * (1 + |x|) ^ (-(1 / 2 + σ))) ∧
      (∀ x : ℝ, ‖stripPropagatorInv E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
        ≤ A * (1 + |x|) ^ ((1 : ℝ) / 2 + σ)) := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hbounds⟩ := exists_twoSided_suzukiGammaStripNormSq hσ0 hσ1
  set p : ℝ := 1 / 2 + σ with hpdef
  have h2p : (1 : ℝ) + 2 * σ = 2 * p := by rw [hpdef]; ring
  have hsqrt : ∀ y : ℝ, Real.sqrt ((1 + |y|) ^ (-(1 + 2 * σ))) = (1 + |y|) ^ (-p) := by
    intro y
    have hy : (0 : ℝ) < 1 + |y| := by positivity
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy.le]
    congr 1
    rw [h2p]
    ring
  have hcarrier_le : ∀ y : ℝ,
      suzukiGammaStripCarrier σ y ≤ Real.sqrt C₀ * (1 + |y|) ^ (-p) := by
    intro y
    calc suzukiGammaStripCarrier σ y
        ≤ Real.sqrt (C₀ * (1 + |y|) ^ (-(1 + 2 * σ))) := Real.sqrt_le_sqrt (hbounds y).2
      _ = Real.sqrt C₀ * (1 + |y|) ^ (-p) := by rw [Real.sqrt_mul hC₀.le, hsqrt]
  have hcarrier_ge : ∀ y : ℝ,
      Real.sqrt c₀ * (1 + |y|) ^ (-p) ≤ suzukiGammaStripCarrier σ y := by
    intro y
    calc Real.sqrt c₀ * (1 + |y|) ^ (-p) = Real.sqrt (c₀ * (1 + |y|) ^ (-(1 + 2 * σ))) := by
          rw [Real.sqrt_mul hc₀.le, hsqrt]
      _ ≤ suzukiGammaStripCarrier σ y := Real.sqrt_le_sqrt (hbounds y).1
  set E₁ : ℝ := Real.exp (-(Real.eulerMascheroniConstant * σ)) * Real.exp (σ / 2 * ‖T‖) with hE₁
  set E₂ : ℝ := Real.exp (Real.eulerMascheroniConstant * σ) * Real.exp (σ / 2 * ‖T‖) with hE₂
  have hE₁pos : 0 < E₁ := by rw [hE₁]; positivity
  have hE₂pos : 0 < E₂ := by rw [hE₂]; positivity
  refine ⟨E₁ * Real.sqrt C₀, E₂ * (Real.sqrt c₀)⁻¹,
    mul_pos hE₁pos (Real.sqrt_pos.mpr hC₀),
    mul_pos hE₂pos (inv_pos.mpr (Real.sqrt_pos.mpr hc₀)), ?_, ?_⟩
  · intro x
    refine le_trans (norm_stripPropagator_shift_le hT hE hσ0 hσ1 x) ?_
    calc E₁ * suzukiGammaStripCarrier σ x
        ≤ E₁ * (Real.sqrt C₀ * (1 + |x|) ^ (-p)) :=
          mul_le_mul_of_nonneg_left (hcarrier_le x) hE₁pos.le
      _ = E₁ * Real.sqrt C₀ * (1 + |x|) ^ (-p) := by ring
  · intro x
    refine le_trans (norm_stripPropagatorInv_shift_le hT hE hσ0 hσ1 x) ?_
    have hpos : 0 < Real.sqrt c₀ * (1 + |x|) ^ (-p) := by
      have : (0 : ℝ) < 1 + |x| := by positivity
      exact mul_pos (Real.sqrt_pos.mpr hc₀) (Real.rpow_pos_of_pos this _)
    have hinv : (suzukiGammaStripCarrier σ x)⁻¹
        ≤ (Real.sqrt c₀)⁻¹ * (1 + |x|) ^ p := by
      have hstep := one_div_le_one_div_of_le hpos (hcarrier_ge x)
      rw [one_div, one_div] at hstep
      refine le_trans hstep (le_of_eq ?_)
      rw [mul_inv, Real.rpow_neg (by positivity), inv_inv]
    calc E₂ * (suzukiGammaStripCarrier σ x)⁻¹
        ≤ E₂ * ((Real.sqrt c₀)⁻¹ * (1 + |x|) ^ p) :=
          mul_le_mul_of_nonneg_left hinv hE₂pos.le
      _ = E₂ * (Real.sqrt c₀)⁻¹ * (1 + |x|) ^ p := by ring

end LineBounds

section WeightedCriterion

/-- The symmetric power weight is integrable above the critical exponent. -/
theorem integrable_oneAddAbs_rpow {a : ℝ} (ha : 1 < a) :
    Integrable (fun x : ℝ => (1 + |x|) ^ (-a)) volume := by
  have hband : IntegrableOn (fun x : ℝ => (1 + |x|) ^ (-a)) {x : ℝ | |x| ≤ 1} volume := by
    have hsub : {x : ℝ | |x| ≤ 1} = Icc (-1 : ℝ) 1 := by
      ext x
      simp [abs_le]
    rw [hsub]
    refine (Continuous.continuousOn ?_).integrableOn_Icc
    exact (continuous_const.add continuous_abs).rpow_const fun x =>
      Or.inl (by positivity : (0 : ℝ) < 1 + |x|).ne'
  have htail : IntegrableOn (fun x : ℝ => (1 + |x|) ^ (-a)) {x : ℝ | 1 ≤ |x|} volume := by
    refine Integrable.mono' ((HTGeometry.integrableOn_powerTail one_pos ha)) ?_ ?_
    · refine (Continuous.continuousOn ?_).aestronglyMeasurable ?_
      · exact (continuous_const.add continuous_abs).rpow_const fun x =>
          Or.inl (by positivity : (0 : ℝ) < 1 + |x|).ne'
      · exact HTGeometry.measurableSet_centralTail 1
    · filter_upwards [ae_restrict_mem (HTGeometry.measurableSet_centralTail 1)] with x hx
      have hx1 : (1 : ℝ) ≤ |x| := hx
      have hx0 : (0 : ℝ) < |x| := lt_of_lt_of_le zero_lt_one hx1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
  have huniv : {x : ℝ | |x| ≤ 1} ∪ {x : ℝ | 1 ≤ |x|} = univ := by
    ext x
    simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact le_total |x| 1
  have := hband.union htail
  rw [huniv, integrableOn_univ] at this
  exact this

/-- The extended-norm form of the weight integral. -/
theorem lintegral_oneAddAbs_rpow_lt_top {a : ℝ} (ha : 1 < a) :
    (∫⁻ x : ℝ, ENNReal.ofReal ((1 + |x|) ^ (-a))) < ⊤ := by
  have hnn : 0 ≤ᵐ[volume] fun x : ℝ => (1 + |x|) ^ (-a) :=
    Filter.Eventually.of_forall fun x => Real.rpow_nonneg (by positivity) _
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_oneAddAbs_rpow ha) hnn]
  exact ENNReal.ofReal_lt_top

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- `(9)` on the shifted line: the forced solution rebased at the origin of the line. -/
def forcedStripLine (E : ℂ → ℂ) (T : X →L[ℂ] X) (c : X) (b : ℝ → X) (σ x : ℝ) : X :=
  stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
    (c + ∫ t in (0 : ℝ)..x,
      stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t))

omit [CompleteSpace X] [Nontrivial X] in
private theorem enorm_intervalIntegral_le {g : ℝ → X} (x : ℝ) :
    ‖∫ t in (0 : ℝ)..x, g t‖ₑ ≤ 2 * ∫⁻ t : ℝ, ‖g t‖ₑ := by
  have hgen : ∀ u v : ℝ, ‖∫ t in Ioc u v, g t‖ₑ ≤ ∫⁻ t : ℝ, ‖g t‖ₑ := by
    intro u v
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  rw [intervalIntegral, two_mul]
  exact le_trans enorm_sub_le (add_le_add (hgen 0 x) (hgen x 0))

/-- **Theorem 3, `(14) ⟹ (15)`.**  A weighted shifted-line source bound makes the
variation-of-constants bracket uniformly bounded, and the propagator power then has square exponent
`1 + 2σ > 1`, so the forced solution is square integrable on the whole shifted line. -/
theorem lintegral_enorm_sq_forcedStripLine_lt_top (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) (c : X) (b : ℝ → X)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hb : (∫⁻ t : ℝ, ENNReal.ofReal ((1 + |t|) ^ ((1 : ℝ) / 2 + σ) * ‖b t‖)) < ⊤) :
    (∫⁻ x : ℝ, ‖forcedStripLine E T c b σ x‖ₑ ^ 2) < ⊤ := by
  obtain ⟨K, A, hK, hA, hKb, hAb⟩ := exists_stripPropagator_line_bounds hT hE hσ0 hσ1
  set p : ℝ := 1 / 2 + σ with hpdef
  -- the source integral is finite
  set S : ℝ≥0∞ := ∫⁻ t : ℝ,
    ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ₑ with hSdef
  have hS : S ≤ ENNReal.ofReal A * ∫⁻ t : ℝ, ENNReal.ofReal ((1 + |t|) ^ p * ‖b t‖) := by
    rw [hSdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono ?_
    intro t
    have hstep : ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖
        ≤ A * ((1 + |t|) ^ p * ‖b t‖) := by
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hAb t) (norm_nonneg _)
    calc ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ₑ
        = ENNReal.ofReal ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ :=
          (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (A * ((1 + |t|) ^ p * ‖b t‖)) := ENNReal.ofReal_le_ofReal hstep
      _ = ENNReal.ofReal A * ENNReal.ofReal ((1 + |t|) ^ p * ‖b t‖) :=
          ENNReal.ofReal_mul hA.le
  have hSfin : S < ⊤ := lt_of_le_of_lt hS (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb)
  set B : ℝ≥0∞ := ENNReal.ofReal ‖c‖ + 2 * S with hBdef
  have hBfin : B < ⊤ := by
    rw [hBdef]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top (by norm_num) hSfin⟩
  -- the pointwise bound
  have hpt : ∀ x : ℝ, ‖forcedStripLine E T c b σ x‖ₑ ^ 2
      ≤ ENNReal.ofReal (K ^ 2 * (1 + |x|) ^ (-(2 * p))) * B ^ 2 := by
    intro x
    have hx : (0 : ℝ) < 1 + |x| := by positivity
    have hbracket : ‖c + ∫ t in (0 : ℝ)..x,
        stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ₑ ≤ B := by
      refine le_trans (enorm_add_le _ _) ?_
      rw [hBdef]
      exact add_le_add (le_of_eq (ofReal_norm c).symm) (enorm_intervalIntegral_le x)
    have houter : ‖forcedStripLine E T c b σ x‖ₑ
        ≤ ENNReal.ofReal (K * (1 + |x|) ^ (-p)) * B := by
      calc ‖forcedStripLine E T c b σ x‖ₑ
          = ENNReal.ofReal ‖forcedStripLine E T c b σ x‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
              * ‖c + ∫ t in (0 : ℝ)..x,
                  stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖) :=
            ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
        _ = ENNReal.ofReal ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
              * ‖c + ∫ t in (0 : ℝ)..x,
                  stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ₑ := by
            rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
        _ ≤ ENNReal.ofReal (K * (1 + |x|) ^ (-p)) * B :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (hKb x)) hbracket
    have hsq : (ENNReal.ofReal (K * (1 + |x|) ^ (-p))) ^ 2
        = ENNReal.ofReal (K ^ 2 * (1 + |x|) ^ (-(2 * p))) := by
      rw [← ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [mul_pow, ← Real.rpow_natCast ((1 + |x|) ^ (-p)) 2, ← Real.rpow_mul hx.le,
        show -p * ((2 : ℕ) : ℝ) = -(2 * p) by push_cast; ring]
    calc ‖forcedStripLine E T c b σ x‖ₑ ^ 2
        ≤ (ENNReal.ofReal (K * (1 + |x|) ^ (-p)) * B) ^ 2 := pow_le_pow_left' houter 2
      _ = ENNReal.ofReal (K ^ 2 * (1 + |x|) ^ (-(2 * p))) * B ^ 2 := by rw [mul_pow, hsq]
  -- integrate
  have hweight : (∫⁻ x : ℝ, ENNReal.ofReal (K ^ 2 * (1 + |x|) ^ (-(2 * p)))) < ⊤ := by
    have hrw : ∀ x : ℝ, ENNReal.ofReal (K ^ 2 * (1 + |x|) ^ (-(2 * p)))
        = ENNReal.ofReal (K ^ 2) * ENNReal.ofReal ((1 + |x|) ^ (-(2 * p))) := by
      intro x
      exact ENNReal.ofReal_mul (by positivity)
    simp only [hrw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact lintegral_oneAddAbs_rpow_lt_top (by rw [hpdef]; linarith)
  calc (∫⁻ x : ℝ, ‖forcedStripLine E T c b σ x‖ₑ ^ 2)
      ≤ ∫⁻ x : ℝ, ENNReal.ofReal (K ^ 2 * (1 + |x|) ^ (-(2 * p))) * B ^ 2 :=
        lintegral_mono hpt
    _ = (∫⁻ x : ℝ, ENNReal.ofReal (K ^ 2 * (1 + |x|) ^ (-(2 * p)))) * B ^ 2 :=
        lintegral_mul_const _ (by fun_prop)
    _ < ⊤ := ENNReal.mul_lt_top hweight (ENNReal.pow_lt_top hBfin)

end WeightedCriterion

end GaloisForLFunctions.RHTower
