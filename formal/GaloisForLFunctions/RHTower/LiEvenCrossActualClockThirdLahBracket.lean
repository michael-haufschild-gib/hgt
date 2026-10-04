import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitiveCumulant
import GaloisForLFunctions.RHTower.XiOffLineQuartetThermalOrientationBound
import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius

/-!
# The third Lah bracket of the integrated clock is positive

Write `λ_q` for the reciprocal squares of all multiplicity copies of the Xi zeros, `H(p) =
log Φ(1/p)` and `z = 1/p`.

* (sector law) `Re λ_q ≥ (167/168)|λ_q|` and `(Im λ_q)² ≤ (Re λ_q)²/84`;
* `-H'(p) = P̂(p) = F̂(p)/p = Σ_q Re[λ_q/(p(p² + λ_q))]` for `p > 1/300`;
* termwise differentiation (uniform `|λ_q|` majorants on `p ≥ a > 0`) gives
  `-H'''(p) = Σ_q Re[2λ_q(6p⁴ + 3λ_q p² + λ_q²)/(p³(p² + λ_q)³)]`;
* each `Re[λ^k/(p² + λ)³]`, `k = 1, 2, 3`, is positive for `λ` in the sector, so
  `6κ₁(z) + 6zκ₂(z) + z²κ₃(z) > 0` for every `0 < z < 300`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry Complex

noncomputable section

namespace RHTower

local notation "P" => liEvenCrossActualClockPrimitive
local notation "Φ" => liClockThetaGeneratorReal

/-! ## The sector law -/

/-- `Re λ_q ≥ (167/168)|λ_q|`. -/
theorem re_xiZeroCopyReciprocalSquare_ge (q : XiZeroCopy) :
    (167 / 168 : ℝ) * ‖xiZeroCopyReciprocalSquare q‖ ≤ (xiZeroCopyReciprocalSquare q).re := by
  have h := sectorFactor_mul_norm_xiZeroCopyReciprocalSquare_pow_le_re q 1
  norm_num at h
  linarith

theorem re_xiZeroCopyReciprocalSquare_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q).re := by
  simpa only [xiThermalNode] using xiThermalNode_pos q

theorem im_sq_xiZeroCopyReciprocalSquare_le (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 ≤ (1 / 84 : ℝ) * (xiZeroCopyReciprocalSquare q).re ^ 2 := by
  simpa only [xiThermalNode] using xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q

/-! ## The first derivative as a resolvent sum -/

/-- `P̂(p) = F̂(p)/p` by integration by parts. -/
theorem integral_exp_mul_liEvenCrossActualClockPrimitive_eq_response {p : ℝ} (hp : 1 / 300 < p) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * P t =
      (∫ t in Ioi (0 : ℝ), Real.exp (-p * t) * liEvenCrossActualClockResponse t) / p := by
  have hp0 : 0 < p := by linarith
  set v : ℝ → ℝ := fun t => -(Real.exp (-(p * t)) / p)
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (Real.exp (-(p * x))) x := by
    intro x _
    have h := (((hasDerivAt_id' x).const_mul p).fun_neg.exp.div_const p).fun_neg
    refine h.congr_deriv ?_
    field_simp
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt P (liEvenCrossActualClockResponse x) x :=
    fun x _ => hasDerivAt_liEvenCrossActualClockPrimitive x
  have huv' : IntegrableOn (P * fun t => Real.exp (-(p * t))) (Ioi 0) :=
    (integrableOn_exp_mul_liEvenCrossActualClockPrimitive
      (liEvenCrossActualClockMaxGrowthRate_lt_of_lt hp)).congr_fun
      (fun t _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  have hu'v : IntegrableOn (liEvenCrossActualClockResponse * v) (Ioi 0) :=
    IntegrableOn.congr_fun ((integrableOn_liEvenCrossActualClockDampedResponse hp).const_mul (-(1 / p)))
      (fun t _ => by simp only [Pi.mul_apply, v, neg_mul]; ring) measurableSet_Ioi
  have hcont : Continuous (P * v) :=
    continuous_liEvenCrossActualClockPrimitive.mul (by fun_prop)
  have h0 : Tendsto (P * v) (𝓝[>] 0) (𝓝 0) := by
    have := hcont.tendsto 0
    simp only [Pi.mul_apply, liEvenCrossActualClockPrimitive_zero, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (P * v) atTop (𝓝 0) := by
    set c := p - 1 / 300
    have hc : 0 < c := by simp only [c]; linarith
    have hlim : Tendsto (fun t : ℝ => xiShiftAbsoluteMass 0 / (2 * p * c ^ 2) *
        ((c * t) ^ 2 * Real.exp (-(c * t)))) atTop (𝓝 0) := by
      have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
        (tendsto_id.const_mul_atTop hc)).const_mul (xiShiftAbsoluteMass 0 / (2 * p * c ^ 2))
      simpa only [mul_zero, Function.comp_def, id] using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hb := abs_liEvenCrossActualClockPrimitive_le t
    rw [abs_of_nonneg ht] at hb
    simp only [Pi.mul_apply, v, Real.norm_eq_abs, abs_mul, abs_neg, abs_div,
      abs_of_pos (Real.exp_pos _), abs_of_pos hp0]
    calc |P t| * (Real.exp (-(p * t)) / p) ≤
        xiShiftAbsoluteMass 0 * t ^ 2 / 2 * Real.exp (t / 300) * (Real.exp (-(p * t)) / p) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by
          rw [show -(c * t) = t / 300 + -(p * t) by simp only [c]; ring, Real.exp_add]
          field_simp
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  have e1 : ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * P t =
      ∫ t in Ioi (0 : ℝ), P t * Real.exp (-(p * t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _
  have e2 : ∫ t in Ioi (0 : ℝ), liEvenCrossActualClockResponse t * v t =
      -((∫ t in Ioi (0 : ℝ), Real.exp (-p * t) * liEvenCrossActualClockResponse t) / p) := by
    rw [← integral_div, ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp only [v, neg_mul]; ring
  rw [e1, h, e2]
  ring

/-- The first resolvent sum `S(p) = Σ_q λ_q/(p(p² + λ_q))`. -/
def liClockThirdLahResolvent (p : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q /
    ((p : ℂ) * ((p : ℂ) ^ 2 + xiZeroCopyReciprocalSquare q))

/-- `-H'(p) = Re S(p)` for `p > 1/300`. -/
theorem neg_deriv_log_liClockThetaGeneratorReal_inv_eq {p : ℝ} (hp : 1 / 300 < p) :
    -deriv (fun q => Real.log (Φ q⁻¹)) p = (liClockThirdLahResolvent p).re := by
  have hp0 : 0 < p := by linarith
  have h1 := iteratedDeriv_log_liClockThetaGeneratorReal_inv 1
    (liEvenCrossActualClockMaxGrowthRate_lt_of_lt hp)
  rw [iteratedDeriv_one] at h1
  rw [h1, pow_one, neg_one_mul, neg_neg]
  have hM : liClockPrimitiveLaplaceMoment 1 p =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * P t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t : ℝ) ≠ 0 := (show (0 : ℝ) < t from ht).ne'
    field_simp
  rw [hM, integral_exp_mul_liEvenCrossActualClockPrimitive_eq_response hp,
    liEvenCrossActualClockDampedResponse_integral_eq_resolvent hp]
  unfold liEvenCrossActualClockDampedResolvent liClockThirdLahResolvent
  have hs := summable_liEvenCrossActualClockDampedResolvent hp0
  have e : (fun q : XiZeroCopy => xiZeroCopyReciprocalSquare q /
      ((p : ℂ) * ((p : ℂ) ^ 2 + xiZeroCopyReciprocalSquare q))) =
        fun q => (p : ℂ)⁻¹ * (xiZeroCopyReciprocalSquare q / ((p : ℂ) ^ 2 +
          xiZeroCopyReciprocalSquare q)) := by
    funext q; rw [div_mul_eq_div_div_swap, div_eq_inv_mul]
  rw [e, tsum_mul_left, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  field_simp

/-! ## Termwise derivatives -/

/-- `g(z) = λ/(z³ + λz)`. -/
def thirdLahAtom (lam z : ℂ) : ℂ := lam / (z ^ 3 + lam * z)

/-- `g'(z) = -λ(3z² + λ)/(z³ + λz)²`. -/
def thirdLahAtomDeriv (lam z : ℂ) : ℂ := -(lam * (3 * z ^ 2 + lam)) / (z ^ 3 + lam * z) ^ 2

/-- `g''(z) = 2λ(6z⁴ + 3λz² + λ²)/(z³ + λz)³`. -/
def thirdLahAtomDeriv2 (lam z : ℂ) : ℂ :=
  2 * lam * (6 * z ^ 4 + 3 * lam * z ^ 2 + lam ^ 2) / (z ^ 3 + lam * z) ^ 3

theorem hasDerivAt_thirdLahAtom {lam z : ℂ} (hz : z ^ 3 + lam * z ≠ 0) :
    HasDerivAt (thirdLahAtom lam) (thirdLahAtomDeriv lam z) z := by
  have hu : HasDerivAt (fun w : ℂ => w ^ 3 + lam * w) (3 * z ^ 2 + lam) z := by
    have := ((hasDerivAt_pow 3 z).add ((hasDerivAt_id z).const_mul lam))
    refine this.congr_deriv ?_
    simp
  have h := (hasDerivAt_const z lam).div hu hz
  refine h.congr_deriv ?_
  unfold thirdLahAtomDeriv
  ring

theorem hasDerivAt_thirdLahAtomDeriv {lam z : ℂ} (hz : z ^ 3 + lam * z ≠ 0) :
    HasDerivAt (thirdLahAtomDeriv lam) (thirdLahAtomDeriv2 lam z) z := by
  have hu : HasDerivAt (fun w : ℂ => w ^ 3 + lam * w) (3 * z ^ 2 + lam) z := by
    have := ((hasDerivAt_pow 3 z).add ((hasDerivAt_id z).const_mul lam))
    refine this.congr_deriv ?_
    simp
  have hn : HasDerivAt (fun w : ℂ => -(lam * (3 * w ^ 2 + lam))) (-(lam * (6 * z))) z := by
    have h0 : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
    exact (((h0.const_mul 3).add_const lam).const_mul lam).fun_neg.congr_deriv (by ring)
  have h := hn.div (hu.fun_pow 2) (pow_ne_zero 2 hz)
  refine h.congr_deriv ?_
  unfold thirdLahAtomDeriv2
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  rw [div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 hz)) (pow_ne_zero 3 hz)]
  ring

private theorem norm_cubic_ge {lam : ℂ} (hre : 0 < lam.re) {p : ℝ} (hp : 0 < p) :
    p ^ 3 ≤ ‖(p : ℂ) ^ 3 + lam * p‖ := by
  have e : (p : ℂ) ^ 3 + lam * p = (p : ℂ) * ((p : ℂ) ^ 2 + lam) := by ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  have h2 : p ^ 2 ≤ ‖(p : ℂ) ^ 2 + lam‖ := by
    calc p ^ 2 ≤ ((p : ℂ) ^ 2 + lam).re := by
          simp only [← Complex.ofReal_pow, Complex.add_re, Complex.ofReal_re]; linarith
      _ ≤ _ := Complex.re_le_norm _
  calc p ^ 3 = p * p ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hp.le

private theorem cubic_ne_zero {lam : ℂ} (hre : 0 < lam.re) {p : ℝ} (hp : 0 < p) :
    (p : ℂ) ^ 3 + lam * p ≠ 0 := by
  intro h
  have := norm_cubic_ge hre hp
  rw [h, norm_zero] at this
  have : 0 < p ^ 3 := by positivity
  linarith

/-- Uniform bound `|g'(p)| ≤ C_a |λ|` on `p ≥ a`. -/
theorem norm_thirdLahAtomDeriv_le {lam : ℂ} (hre : 0 < lam.re) (hl : ‖lam‖ ≤ 1) {a p : ℝ}
    (ha : 0 < a) (hp : a ≤ p) :
    ‖thirdLahAtomDeriv lam p‖ ≤ (4 / a ^ 4 + 4 / a ^ 6) * ‖lam‖ := by
  have hp0 : 0 < p := ha.trans_le hp
  have hu := norm_cubic_ge hre hp0
  unfold thirdLahAtomDeriv
  rw [norm_div, norm_neg, norm_mul, norm_pow]
  have hnum : ‖3 * (p : ℂ) ^ 2 + lam‖ ≤ 3 * p ^ 2 + 1 := by
    calc ‖3 * (p : ℂ) ^ 2 + lam‖ ≤ ‖3 * (p : ℂ) ^ 2‖ + ‖lam‖ := norm_add_le _ _
      _ ≤ 3 * p ^ 2 + 1 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
          norm_num
          linarith
  have hden : (p ^ 3) ^ 2 ≤ ‖(p : ℂ) ^ 3 + lam * p‖ ^ 2 := pow_le_pow_left₀ (by positivity) hu 2
  have hpa4 : a ^ 4 ≤ p ^ 4 := pow_le_pow_left₀ ha.le hp 4
  have hpa6 : a ^ 6 ≤ p ^ 6 := pow_le_pow_left₀ ha.le hp 6
  rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hden)]
  calc ‖lam‖ * ‖3 * (p : ℂ) ^ 2 + lam‖ ≤ ‖lam‖ * (3 * p ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left hnum (norm_nonneg _)
    _ ≤ (4 / a ^ 4 + 4 / a ^ 6) * ‖lam‖ * (p ^ 3) ^ 2 := by
        have h1 : 3 * p ^ 2 + 1 ≤ (4 / a ^ 4 + 4 / a ^ 6) * (p ^ 3) ^ 2 := by
          have e1 : 4 / a ^ 4 * (p ^ 3) ^ 2 = 4 * p ^ 2 * (p ^ 4 / a ^ 4) := by field_simp
          have e2 : 4 / a ^ 6 * (p ^ 3) ^ 2 = 4 * (p ^ 6 / a ^ 6) := by field_simp
          have g1 : 1 ≤ p ^ 4 / a ^ 4 := (one_le_div (by positivity)).2 hpa4
          have g2 : 1 ≤ p ^ 6 / a ^ 6 := (one_le_div (by positivity)).2 hpa6
          rw [add_mul, e1, e2]
          nlinarith [sq_nonneg p]
        nlinarith [norm_nonneg lam]
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

/-- Uniform bound `|g''(p)| ≤ C_a |λ|` on `p ≥ a`. -/
theorem norm_thirdLahAtomDeriv2_le {lam : ℂ} (hre : 0 < lam.re) (hl : ‖lam‖ ≤ 1) {a p : ℝ}
    (ha : 0 < a) (hp : a ≤ p) :
    ‖thirdLahAtomDeriv2 lam p‖ ≤ (20 / a ^ 5 + 20 / a ^ 9) * ‖lam‖ := by
  have hp0 : 0 < p := ha.trans_le hp
  have hu := norm_cubic_ge hre hp0
  unfold thirdLahAtomDeriv2
  rw [norm_div, norm_mul, norm_mul, norm_pow]
  have hnum : ‖6 * (p : ℂ) ^ 4 + 3 * lam * (p : ℂ) ^ 2 + lam ^ 2‖ ≤ 6 * p ^ 4 + 3 * p ^ 2 + 1 := by
    have hp2 : ‖(p : ℂ) ^ 2‖ = p ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
    have hp4 : ‖(p : ℂ) ^ 4‖ = p ^ 4 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
    calc ‖6 * (p : ℂ) ^ 4 + 3 * lam * (p : ℂ) ^ 2 + lam ^ 2‖ ≤
        ‖6 * (p : ℂ) ^ 4‖ + ‖3 * lam * (p : ℂ) ^ 2‖ + ‖lam ^ 2‖ := norm_add₃_le
      _ ≤ 6 * p ^ 4 + 3 * p ^ 2 + 1 := by
          rw [norm_mul, norm_mul, norm_mul, hp2, hp4, norm_pow]
          norm_num
          have h1 : ‖lam‖ * p ^ 2 ≤ p ^ 2 := by nlinarith [sq_nonneg p, norm_nonneg lam]
          have h2 : ‖lam‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg lam]
          nlinarith
  have hden : (p ^ 3) ^ 3 ≤ ‖(p : ℂ) ^ 3 + lam * p‖ ^ 3 := pow_le_pow_left₀ (by positivity) hu 3
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2, div_le_iff₀ (lt_of_lt_of_le (by positivity) hden)]
  have hpa5 : a ^ 5 ≤ p ^ 5 := pow_le_pow_left₀ ha.le hp 5
  have hpa9 : a ^ 9 ≤ p ^ 9 := pow_le_pow_left₀ ha.le hp 9
  have hkey : 2 * (6 * p ^ 4 + 3 * p ^ 2 + 1) ≤ (20 / a ^ 5 + 20 / a ^ 9) * (p ^ 3) ^ 3 := by
    have e1 : 20 / a ^ 5 * (p ^ 3) ^ 3 = 20 * p ^ 4 * (p ^ 5 / a ^ 5) := by field_simp
    have e2 : 20 / a ^ 9 * (p ^ 3) ^ 3 = 20 * (p ^ 9 / a ^ 9) := by field_simp
    have g1 : 1 ≤ p ^ 5 / a ^ 5 := (one_le_div (by positivity)).2 hpa5
    have g2 : 1 ≤ p ^ 9 / a ^ 9 := (one_le_div (by positivity)).2 hpa9
    rw [add_mul, e1, e2]
    have : 6 * p ^ 2 ≤ 6 * p ^ 4 + 6 := by nlinarith [sq_nonneg (p ^ 2 - 1)]
    nlinarith [sq_nonneg p, pow_pos hp0 4]
  calc 2 * ‖lam‖ * ‖6 * (p : ℂ) ^ 4 + 3 * lam * (p : ℂ) ^ 2 + lam ^ 2‖ ≤
      2 * ‖lam‖ * (6 * p ^ 4 + 3 * p ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
    _ ≤ (20 / a ^ 5 + 20 / a ^ 9) * ‖lam‖ * (p ^ 3) ^ 3 := by nlinarith [norm_nonneg lam]
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

/-! ## Termwise differentiation of the resolvent sum -/

/-- `S'(p) = Σ_q g'_q(p)`. -/
def liClockThirdLahResolventDeriv (p : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, thirdLahAtomDeriv (xiZeroCopyReciprocalSquare q) p

/-- `S''(p) = Σ_q g''_q(p)`. -/
def liClockThirdLahResolventDeriv2 (p : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, thirdLahAtomDeriv2 (xiZeroCopyReciprocalSquare q) p

private theorem norm_lam_le_one (q : XiZeroCopy) : ‖xiZeroCopyReciprocalSquare q‖ ≤ 1 :=
  (norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q).le.trans (by norm_num)

private theorem summable_norm_lam : Summable fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖ := by
  simpa using summable_xiShiftAbsoluteMass 0

theorem liClockThirdLahResolvent_eq (p : ℝ) :
    liClockThirdLahResolvent p =
      ∑' q : XiZeroCopy, thirdLahAtom (xiZeroCopyReciprocalSquare q) p := by
  unfold liClockThirdLahResolvent thirdLahAtom
  exact tsum_congr fun q => by ring_nf

theorem hasDerivAt_liClockThirdLahResolvent {p : ℝ} (hp : 0 < p) :
    HasDerivAt liClockThirdLahResolvent (liClockThirdLahResolventDeriv p) p := by
  set a := p / 2
  have ha : 0 < a := half_pos hp
  have hpa : p ∈ Ioi a := by simp only [mem_Ioi, a]; linarith
  have hfun : liClockThirdLahResolvent =
      fun y : ℝ => ∑' q : XiZeroCopy, thirdLahAtom (xiZeroCopyReciprocalSquare q) y :=
    funext liClockThirdLahResolvent_eq
  rw [hfun]
  refine hasDerivAt_tsum_of_isPreconnected (g := fun q (y : ℝ) =>
      thirdLahAtom (xiZeroCopyReciprocalSquare q) y)
    (g' := fun q (y : ℝ) => thirdLahAtomDeriv (xiZeroCopyReciprocalSquare q) y)
    (summable_norm_lam.mul_left (4 / a ^ 4 + 4 / a ^ 6)) isOpen_Ioi isPreconnected_Ioi
    (fun q y hy => (hasDerivAt_thirdLahAtom
      (cubic_ne_zero (re_xiZeroCopyReciprocalSquare_pos q) (ha.trans hy))).comp_ofReal)
    (fun q y hy => norm_thirdLahAtomDeriv_le (re_xiZeroCopyReciprocalSquare_pos q)
      (norm_lam_le_one q) ha (le_of_lt hy))
    hpa ?_ hpa
  have hs := summable_liEvenCrossActualClockDampedResolvent hp
  refine (hs.mul_left ((p : ℂ)⁻¹)).congr fun q => ?_
  unfold thirdLahAtom
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

theorem hasDerivAt_liClockThirdLahResolventDeriv {p : ℝ} (hp : 0 < p) :
    HasDerivAt liClockThirdLahResolventDeriv (liClockThirdLahResolventDeriv2 p) p := by
  set a := p / 2
  have ha : 0 < a := half_pos hp
  have hpa : p ∈ Ioi a := by simp only [mem_Ioi, a]; linarith
  refine hasDerivAt_tsum_of_isPreconnected (g := fun q (y : ℝ) =>
      thirdLahAtomDeriv (xiZeroCopyReciprocalSquare q) y)
    (g' := fun q (y : ℝ) => thirdLahAtomDeriv2 (xiZeroCopyReciprocalSquare q) y)
    (summable_norm_lam.mul_left (20 / a ^ 5 + 20 / a ^ 9)) isOpen_Ioi isPreconnected_Ioi
    (fun q y hy => (hasDerivAt_thirdLahAtomDeriv
      (cubic_ne_zero (re_xiZeroCopyReciprocalSquare_pos q) (ha.trans hy))).comp_ofReal)
    (fun q y hy => norm_thirdLahAtomDeriv2_le (re_xiZeroCopyReciprocalSquare_pos q)
      (norm_lam_le_one q) ha (le_of_lt hy))
    hpa ?_ hpa
  exact Summable.of_norm_bounded (summable_norm_lam.mul_left (4 / a ^ 4 + 4 / a ^ 6))
    fun q => norm_thirdLahAtomDeriv_le (re_xiZeroCopyReciprocalSquare_pos q) (norm_lam_le_one q) ha
      (le_of_lt hpa)

private theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).re) f'.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

/-- **Third derivative (C3).**  `-H'''(p) = Re S''(p)` for `p > 1/300`. -/
theorem neg_iteratedDeriv_three_log_liClockThetaGeneratorReal_inv_eq {p : ℝ} (hp : 1 / 300 < p) :
    -iteratedDeriv 3 (fun q => Real.log (Φ q⁻¹)) p = (liClockThirdLahResolventDeriv2 p).re := by
  set H := fun q : ℝ => Real.log (Φ q⁻¹)
  have h1 : ∀ q, 1 / 300 < q → iteratedDeriv 1 H q = -(liClockThirdLahResolvent q).re := by
    intro q hq
    rw [iteratedDeriv_one, ← neg_deriv_log_liClockThetaGeneratorReal_inv_eq hq, neg_neg]
  have h2 : ∀ q, 1 / 300 < q → iteratedDeriv 2 H q = -(liClockThirdLahResolventDeriv q).re := by
    intro q hq
    have hev : iteratedDeriv 1 H =ᶠ[𝓝 q] fun y => -(liClockThirdLahResolvent y).re := by
      filter_upwards [Ioi_mem_nhds hq] with y hy
      exact h1 y hy
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact (hasDerivAt_re (hasDerivAt_liClockThirdLahResolvent (by linarith))).neg.deriv
  have hev : iteratedDeriv 2 H =ᶠ[𝓝 p] fun y => -(liClockThirdLahResolventDeriv y).re := by
    filter_upwards [Ioi_mem_nhds hp] with y hy
    exact h2 y hy
  rw [iteratedDeriv_succ, hev.deriv_eq,
    (hasDerivAt_re (hasDerivAt_liClockThirdLahResolventDeriv (by linarith))).fun_neg.deriv, neg_neg]

/-! ## Sector positivity -/

private theorem re_div_pos {z w : ℂ} (hw : w ≠ 0) (h : 0 < z.re * w.re + z.im * w.im) :
    0 < (z / w).re := by
  rw [Complex.div_re, ← add_div]
  exact div_pos h (Complex.normSq_pos.2 hw)

/-- For `λ` in the sector, `Re[λ^k/(p² + λ)³] > 0`, `k = 1, 2, 3`. -/
theorem re_pow_div_cube_pos {lam : ℂ} (hre : 0 < lam.re) (him : lam.im ^ 2 ≤ (1 / 84) * lam.re ^ 2)
    (p : ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    0 < (lam ^ k / ((p : ℂ) ^ 2 + lam) ^ 3).re := by
  set a := lam.re
  set b := lam.im
  set Q := p ^ 2 + a
  have hQ : a ≤ Q := by simp only [Q]; nlinarith [sq_nonneg p]
  have hQ0 : 0 < Q := hre.trans_le hQ
  have hbQ : b ^ 2 ≤ (1 / 84) * Q ^ 2 := him.trans (by nlinarith)
  have hw : ((p : ℂ) ^ 2 + lam) ^ 3 ≠ 0 := by
    refine pow_ne_zero 3 fun h => ?_
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at this
    norm_cast at this
    nlinarith [sq_nonneg p]
  have hwr : (((p : ℂ) ^ 2 + lam) ^ 3).re = Q ^ 3 - 3 * Q * b ^ 2 := by
    simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Q, a, b]
    ring
  have hwi : (((p : ℂ) ^ 2 + lam) ^ 3).im = 3 * Q ^ 2 * b - b ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Q, a, b]
    ring
  have hA : 0 < Q * (Q ^ 2 - 3 * b ^ 2) := mul_pos hQ0 (by nlinarith)
  have hB : 0 ≤ b ^ 2 * (3 * Q ^ 2 - b ^ 2) := mul_nonneg (sq_nonneg b) (by nlinarith)
  have hab : b ^ 2 ≤ (1 / 84) * a ^ 2 := him
  refine re_div_pos hw ?_
  rw [hwr, hwi]
  interval_cases k
  · simp only [pow_one]
    change 0 < a * (Q ^ 3 - 3 * Q * b ^ 2) + b * (3 * Q ^ 2 * b - b ^ 3)
    have e : a * (Q ^ 3 - 3 * Q * b ^ 2) + b * (3 * Q ^ 2 * b - b ^ 3) =
        a * (Q * (Q ^ 2 - 3 * b ^ 2)) + b ^ 2 * (3 * Q ^ 2 - b ^ 2) := by ring
    rw [e]; nlinarith [mul_pos hre hA]
  · have hr : (lam ^ 2).re = a ^ 2 - b ^ 2 := by simp [pow_two, a, b]
    have hi : (lam ^ 2).im = 2 * a * b := by simp [pow_two, a, b]; ring
    rw [hr, hi]
    have e : (a ^ 2 - b ^ 2) * (Q ^ 3 - 3 * Q * b ^ 2) + 2 * a * b * (3 * Q ^ 2 * b - b ^ 3) =
        (a ^ 2 - b ^ 2) * (Q * (Q ^ 2 - 3 * b ^ 2)) + 2 * a * (b ^ 2 * (3 * Q ^ 2 - b ^ 2)) := by ring
    rw [e]
    have h1 : 0 < a ^ 2 - b ^ 2 := by nlinarith
    nlinarith [mul_pos h1 hA, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hre.le) hB]
  · have hr : (lam ^ 3).re = a ^ 3 - 3 * a * b ^ 2 := by
      simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im, a, b]; ring
    have hi : (lam ^ 3).im = 3 * a ^ 2 * b - b ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im, a, b]; ring
    rw [hr, hi]
    have e : (a ^ 3 - 3 * a * b ^ 2) * (Q ^ 3 - 3 * Q * b ^ 2) +
        (3 * a ^ 2 * b - b ^ 3) * (3 * Q ^ 2 * b - b ^ 3) =
          a * (a ^ 2 - 3 * b ^ 2) * (Q * (Q ^ 2 - 3 * b ^ 2)) +
            (3 * a ^ 2 - b ^ 2) * (b ^ 2 * (3 * Q ^ 2 - b ^ 2)) := by ring
    rw [e]
    have h1 : 0 < a * (a ^ 2 - 3 * b ^ 2) := mul_pos hre (by nlinarith)
    have h2 : 0 ≤ 3 * a ^ 2 - b ^ 2 := by nlinarith
    nlinarith [mul_pos h1 hA, mul_nonneg h2 hB]

/-- Each atom of `S''` has positive real part on `p > 0`. -/
theorem re_thirdLahAtomDeriv2_pos {lam : ℂ} (hre : 0 < lam.re)
    (him : lam.im ^ 2 ≤ (1 / 84) * lam.re ^ 2) {p : ℝ} (hp : 0 < p) :
    0 < (thirdLahAtomDeriv2 lam p).re := by
  have hw : ((p : ℂ) ^ 2 + lam) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [← Complex.ofReal_pow, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
    nlinarith [sq_nonneg p]
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have e : thirdLahAtomDeriv2 lam p = ((2 / p ^ 3 * (6 * p ^ 4) : ℝ) : ℂ) *
      (lam / ((p : ℂ) ^ 2 + lam) ^ 3) + ((2 / p ^ 3 * (3 * p ^ 2) : ℝ) : ℂ) *
        (lam ^ 2 / ((p : ℂ) ^ 2 + lam) ^ 3) + ((2 / p ^ 3 : ℝ) : ℂ) *
          (lam ^ 3 / ((p : ℂ) ^ 2 + lam) ^ 3) := by
    unfold thirdLahAtomDeriv2
    push_cast
    field_simp
  rw [e, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]
  have h1 := re_pow_div_cube_pos hre him p (k := 1) le_rfl (by norm_num)
  have h2 := re_pow_div_cube_pos hre him p (k := 2) (by norm_num) (by norm_num)
  have h3 := re_pow_div_cube_pos hre him p (k := 3) (by norm_num) le_rfl
  rw [pow_one] at h1
  have c1 : 0 < 2 / p ^ 3 * (6 * p ^ 4) := by positivity
  have c2 : 0 < 2 / p ^ 3 * (3 * p ^ 2) := by positivity
  have c3 : 0 < 2 / p ^ 3 := by positivity
  nlinarith [mul_pos c1 h1, mul_pos c2 h2, mul_pos c3 h3]

theorem re_liClockThirdLahResolventDeriv2_pos {p : ℝ} (hp : 0 < p) :
    0 < (liClockThirdLahResolventDeriv2 p).re := by
  have hs : Summable fun q : XiZeroCopy => thirdLahAtomDeriv2 (xiZeroCopyReciprocalSquare q) p :=
    Summable.of_norm_bounded (summable_norm_lam.mul_left (20 / p ^ 5 + 20 / p ^ 9))
      fun q => norm_thirdLahAtomDeriv2_le (re_xiZeroCopyReciprocalSquare_pos q) (norm_lam_le_one q)
        hp le_rfl
  unfold liClockThirdLahResolventDeriv2
  rw [Complex.re_tsum hs]
  exact (Complex.reCLM.summable hs).tsum_pos
    (fun q => (re_thirdLahAtomDeriv2_pos (re_xiZeroCopyReciprocalSquare_pos q)
      (im_sq_xiZeroCopyReciprocalSquare_le q) hp).le)
    (Classical.choice nonempty_xiZeroCopy)
    (re_thirdLahAtomDeriv2_pos (re_xiZeroCopyReciprocalSquare_pos _)
      (im_sq_xiZeroCopyReciprocalSquare_le _) hp)

/-- `-H'''(p) > 0` for `p > 1/300`. -/
theorem neg_iteratedDeriv_three_log_liClockThetaGeneratorReal_inv_pos {p : ℝ} (hp : 1 / 300 < p) :
    0 < -iteratedDeriv 3 (fun q => Real.log (Φ q⁻¹)) p := by
  rw [neg_iteratedDeriv_three_log_liClockThetaGeneratorReal_inv_eq hp]
  exact re_liClockThirdLahResolventDeriv2_pos (by linarith)

/-- **Third Lah bracket (C4).**  `6κ₁(z) + 6zκ₂(z) + z²κ₃(z) > 0` for every `0 < z < 300`. -/
theorem thirdLahBracket_pos {z : ℝ} (hz : 0 < z) (hz300 : z < 300) :
    0 < 6 * iteratedDeriv 1 liClockThetaLogGenerator z +
      6 * z * iteratedDeriv 2 liClockThetaLogGenerator z +
        z ^ 2 * iteratedDeriv 3 liClockThetaLogGenerator z := by
  have hp : 1 / 300 < z⁻¹ := by
    rw [one_div]; exact inv_strictAnti₀ hz hz300
  have h := neg_iteratedDeriv_three_log_liClockThetaGeneratorReal_inv_pos hp
  rw [neg_iteratedDeriv_three_log_liClockThetaGeneratorReal_inv (inv_pos.2 hz), inv_inv] at h
  exact pos_of_mul_pos_right h (by positivity)

end RHTower
