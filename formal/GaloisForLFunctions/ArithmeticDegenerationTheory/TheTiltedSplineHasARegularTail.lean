import GaloisForLFunctions.ArithmeticDegenerationTheory.RegularTailsGiveJordanTotientLimits
import GaloisForLFunctions.CompletedArithmeticForms.ConductorOverlapDecay

/-!
# The tilted spline has a regular spectral tail

The tilted unit spline `φ = e^{8(·−½)}`-boosted cubic spline on `[0, 1]` has an explicit spectrum:
with `x = πt/4`,

`|φ̂(2πt)|² = (1/64) · ((sinh²1 + sin²x)/(1 + x²))⁴`   (`shellSpectrum_tiltedUnitSpline`).

The numerator `q(x) = (sinh²1 + sin²x)⁴` is `π`-periodic and positive, so the spectrum decays like
`x^{-8}` modulated by a periodic factor. A block comparison over periods
(`periodic_tail_squeeze`) shows that a periodic modulation of an antitone integrable weight contributes
its mean: `μ ∫_{Y+L}^∞ h ≤ ∫_Y^∞ q h ≤ μ (L h(Y) + ∫_Y^∞ h)`. Hence

`c⁷ T(c) → A_φ = (4/π)⁷/(16π) · μ_q/7 > 0`   (`tendsto_rpow_seven_mul_spectralTail_tiltedUnitSpline`),

with `μ_q` the mean of `q` over a period. The general theorem of `RegularTailsGiveJordanTotientLimits`
then gives the rescaled limit of every completed conductor energy of the tilted spline:
`c⁷ E_m(c) → (2A_φ/M) ζ(8) J₈(m)/φ(m)`, a positive multiple of the Jordan-totient ratio.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset Complex
open scoped Real

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticCastelnuovoSeveri BiScaleUncertainty BiScaleUncertainty.ChebyshevGauge RHTower
  RHTower.WeilDeletion

/-! ## The exact spectrum -/

/-- `|sin(x − i)|² / |x − i|²`, the squared modulus of the uniform transform on the boosted line. -/
theorem norm_paperFT_unif_shift_sq (x : ℝ) :
    ‖Zeta23.paperFT (fun u => (unif 1 u : ℂ)) ((x : ℂ) - I * (1 : ℝ))‖ ^ 2 =
      (Real.sinh 1 ^ 2 + Real.sin x ^ 2) / (1 + x ^ 2) := by
  have hz : (x : ℂ) - I * (1 : ℝ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  rw [paperFT_unif one_pos hz, norm_div, div_pow]
  have hnum : I * ((x : ℂ) - I * (1 : ℝ)) * (1 : ℝ) = ⟨1, x⟩ := by
    apply Complex.ext <;> simp
  have hnum' : -(I * ((x : ℂ) - I * (1 : ℝ)) * (1 : ℝ)) = ⟨-1, -x⟩ := by
    rw [hnum]; apply Complex.ext <;> simp
  have hden : ‖(2 : ℂ) * I * ((x : ℂ) - I * (1 : ℝ)) * (1 : ℝ)‖ ^ 2 = 4 * (1 + x ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hw : ‖Complex.exp ⟨1, x⟩ - Complex.exp ⟨-1, -x⟩‖ ^ 2 =
      4 * (Real.sinh 1 ^ 2 + Real.sin x ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.exp_re, Complex.exp_im, Real.cos_neg,
      Real.sin_neg]
    have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    have hs : Real.sinh 1 = (Real.exp 1 - Real.exp (-1)) / 2 := Real.sinh_eq 1
    rw [hs]
    have hsc := Real.sin_sq_add_cos_sq x
    linear_combination (Real.exp 1 - Real.exp (-1)) ^ 2 * hsc + 4 * Real.sin x ^ 2 * he
  rw [hnum, show -(⟨1, x⟩ : ℂ) = ⟨-1, -x⟩ from by apply Complex.ext <;> simp, hw, hden]
  field_simp

/-- The spline probe transform on the real line: `‖Û(r)‖² = ((sinh²1 + sin²r)/(1 + r²))⁴`. -/
theorem norm_paperFT_splineProbe_sq (r : ℝ) :
    ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r‖ ^ 2 =
      ((Real.sinh 1 ^ 2 + Real.sin r ^ 2) / (1 + r ^ 2)) ^ 4 := by
  unfold splineProbe
  rw [paperFT_tiltedSource, cubicSpline, paperFT_upow, norm_pow, ← pow_mul,
    show (3 + 1) * 2 = 2 * 4 by norm_num, pow_mul, norm_paperFT_unif_shift_sq]

theorem norm_paperFT_tiltedUnitSpline (r : ℝ) :
    ‖Zeta23.paperFT (cx tiltedUnitSpline) (r : ℂ)‖ =
      (1 / 8 : ℝ) * ‖Zeta23.paperFT (cx splineProbe) ((r / 8 : ℝ) : ℂ)‖ := by
  have heq : cx tiltedUnitSpline =
      ArithmeticCastelnuovoSeveri.translate (1 / 2) (cx (atomDilate splineProbe (1 / 8))) := rfl
  rw [heq, ArithmeticCastelnuovoSeveri.paperFT_translate, paperFT_atomDilate (by norm_num : (0 : ℝ) < 1 / 8),
    norm_mul, norm_mul, Complex.norm_exp]
  have hz : ((1 / 8 : ℝ) : ℂ) * (r : ℂ) = ((r / 8 : ℝ) : ℂ) := by push_cast; ring
  rw [hz]
  norm_num [Complex.mul_re, Complex.mul_im]

/-- The periodic numerator `q(x) = (sinh²1 + sin²x)⁴` of the tilted spline spectrum. -/
def splineNumerator (x : ℝ) : ℝ := (Real.sinh 1 ^ 2 + Real.sin x ^ 2) ^ 4

/-- The weight `h(x) = (1 + x²)⁻⁴`. -/
def splineWeight (x : ℝ) : ℝ := ((1 + x ^ 2) ^ 4)⁻¹

/-- **The exact spectrum of the tilted spline**: `P(t) = (1/64) q(πt/4) h(πt/4)`. -/
theorem shellSpectrum_tiltedUnitSpline (t : ℝ) :
    shellSpectrum tiltedUnitSpline t =
      (1 / 64) * (splineNumerator (π * t / 4) * splineWeight (π * t / 4)) := by
  change ‖Zeta23.paperFT (cx tiltedUnitSpline) ((2 * π * t : ℝ) : ℂ)‖ ^ 2 = _
  rw [norm_paperFT_tiltedUnitSpline, mul_pow]
  change (1 / 8 : ℝ) ^ 2 * ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ))
    ((2 * π * t / 8 : ℝ) : ℂ)‖ ^ 2 = _
  rw [norm_paperFT_splineProbe_sq, show 2 * π * t / 8 = π * t / 4 by ring, splineNumerator,
    splineWeight, div_pow]
  field_simp
  norm_num

/-! ## Periodic modulation of an antitone tail -/

/-- **Periodic tail squeeze.** A nonnegative `L`-periodic factor `q` of mean `μ` modulating a
nonnegative weight `h` that is antitone and integrable beyond `Y` contributes its mean:
`μ ∫_{Y+L}^∞ h ≤ ∫_Y^∞ q h ≤ μ (L h(Y) + ∫_Y^∞ h)`. -/
theorem periodic_tail_squeeze {q h : ℝ → ℝ} {L Y B : ℝ} (hL : 0 < L) (hq : Continuous q)
    (hq0 : ∀ x, 0 ≤ q x) (hqB : ∀ x, q x ≤ B) (hqp : Function.Periodic q L) (hc : Continuous h)
    (hh0 : ∀ x, 0 ≤ h x) (hanti : AntitoneOn h (Ici Y)) (hint : IntegrableOn h (Ioi Y)) :
    (∫ x in (0 : ℝ)..L, q x) / L * ∫ x in Ioi (Y + L), h x ≤ ∫ x in Ioi Y, q x * h x ∧
      ∫ x in Ioi Y, q x * h x ≤
        (∫ x in (0 : ℝ)..L, q x) / L * (L * h Y + ∫ x in Ioi Y, h x) := by
  set P := ∫ x in (0 : ℝ)..L, q x
  set μ := P / L
  have hP : 0 ≤ P := intervalIntegral.integral_nonneg hL.le fun x _ => hq0 x
  have hμ : 0 ≤ μ := div_nonneg hP hL.le
  have hblock : ∀ a, ∫ x in a..a + L, q x = P := fun a => by
    simpa [zero_add] using hqp.intervalIntegral_add_eq a 0
  -- block bounds for `q h` and for `h`
  have hqh_le : ∀ a, Y ≤ a → ∫ x in a..a + L, q x * h x ≤ P * h a := by
    intro a ha
    calc ∫ x in a..a + L, q x * h x ≤ ∫ x in a..a + L, q x * h a := by
          refine intervalIntegral.integral_mono_on (by linarith) ((hq.mul hc).intervalIntegrable _ _)
            ((hq.mul continuous_const).intervalIntegrable _ _) fun x hx => ?_
          exact mul_le_mul_of_nonneg_left (hanti (mem_Ici.mpr ha) (mem_Ici.mpr (ha.trans hx.1))
            hx.1) (hq0 x)
      _ = P * h a := by rw [intervalIntegral.integral_mul_const, hblock]
  have hqh_ge : ∀ a, Y ≤ a → P * h (a + L) ≤ ∫ x in a..a + L, q x * h x := by
    intro a ha
    calc P * h (a + L) = ∫ x in a..a + L, q x * h (a + L) := by
          rw [intervalIntegral.integral_mul_const, hblock]
      _ ≤ ∫ x in a..a + L, q x * h x := by
          refine intervalIntegral.integral_mono_on (by linarith)
            ((hq.mul continuous_const).intervalIntegrable _ _)
            ((hq.mul hc).intervalIntegrable _ _) fun x hx => ?_
          exact mul_le_mul_of_nonneg_left (hanti (mem_Ici.mpr (ha.trans hx.1))
            (mem_Ici.mpr (by linarith)) hx.2) (hq0 x)
  have hh_ge : ∀ a, Y ≤ a → L * h (a + L) ≤ ∫ x in a..a + L, h x := by
    intro a ha
    calc L * h (a + L) = ∫ x in a..a + L, h (a + L) := by simp
      _ ≤ ∫ x in a..a + L, h x := by
          refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
            (hc.intervalIntegrable _ _) fun x hx => ?_
          exact hanti (mem_Ici.mpr (ha.trans hx.1)) (mem_Ici.mpr (by linarith)) hx.2
  have hh_le : ∀ a, Y ≤ a → ∫ x in a..a + L, h x ≤ L * h a := by
    intro a ha
    calc ∫ x in a..a + L, h x ≤ ∫ x in a..a + L, h a := by
          refine intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
            intervalIntegrable_const fun x hx => ?_
          exact hanti (mem_Ici.mpr ha) (mem_Ici.mpr (ha.trans hx.1)) hx.1
      _ = L * h a := by simp
  set b : ℕ → ℝ := fun n => Y + n * L
  have hb : ∀ n : ℕ, b (n + 1) = b n + L := fun n => by simp only [b]; push_cast; ring
  have hbY : ∀ n : ℕ, Y ≤ b n := fun n => by simp only [b]; nlinarith [n.cast_nonneg (α := ℝ)]
  have hII : ∀ u v : ℝ, IntervalIntegrable (fun x => q x * h x) volume u v :=
    fun u v => (hq.mul hc).intervalIntegrable _ _
  have hIh : ∀ u v : ℝ, IntervalIntegrable h volume u v := fun u v => hc.intervalIntegrable _ _
  -- the two inductive bounds on partial integrals
  have hupper : ∀ n : ℕ, ∫ x in Y..b (n + 1), q x * h x ≤ μ * (L * h Y + ∫ x in Y..b n, h x) := by
    intro n
    induction n with
    | zero =>
        simp only [b, Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, zero_add,
          one_mul, intervalIntegral.integral_same]
        have := hqh_le Y le_rfl
        calc ∫ x in Y..Y + L, q x * h x ≤ P * h Y := this
          _ = μ * (L * h Y) := by simp only [μ]; field_simp
    | succ n ih =>
        rw [← intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII (b (n + 1)) _), hb (n + 1),
          ← intervalIntegral.integral_add_adjacent_intervals (hIh Y (b n)) (hIh (b n) (b (n + 1))),
          hb n]
        have h1 := hqh_le (b n + L) (by linarith [hbY n])
        have h2 := hh_ge (b n) (hbY n)
        rw [hb n] at ih
        have h3 : P * h (b n + L) = μ * (L * h (b n + L)) := by simp only [μ]; field_simp
        nlinarith [mul_le_mul_of_nonneg_left h2 hμ]
  have hlower : ∀ n : ℕ, μ * ∫ x in Y + L..b (n + 1), h x ≤ ∫ x in Y..b n, q x * h x := by
    intro n
    induction n with
    | zero => simp [b]
    | succ n ih =>
        rw [← intervalIntegral.integral_add_adjacent_intervals (hIh (Y + L) (b (n + 1)))
          (hIh (b (n + 1)) (b (n + 2))), hb (n + 1),
          ← intervalIntegral.integral_add_adjacent_intervals (hII Y (b n)) (hII (b n) (b (n + 1))),
          hb n]
        rw [hb n] at ih
        have h1 := hqh_ge (b n) (hbY n)
        have h2 := hh_le (b n + L) (by linarith [hbY n])
        have h3 : P * h (b n + L) = μ * (L * h (b n + L)) := by simp only [μ]; field_simp
        nlinarith [mul_le_mul_of_nonneg_left h2 hμ]
  -- pass to the limit
  have hbt : Tendsto b atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const hL)
  have hb1 : Tendsto (fun n : ℕ => b (n + 1)) atTop atTop :=
    hbt.comp (tendsto_add_atTop_nat 1)
  have hqhint : IntegrableOn (fun x => q x * h x) (Ioi Y) := by
    refine (hint.const_mul B).mono' ((hq.mul hc).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (mul_nonneg (hq0 x) (hh0 x))]
    exact mul_le_mul_of_nonneg_right (hqB x) (hh0 x)
  have hintL : IntegrableOn h (Ioi (Y + L)) := hint.mono_set (Ioi_subset_Ioi (by linarith))
  have tqh := intervalIntegral_tendsto_integral_Ioi Y hqhint hbt
  have tqh1 := intervalIntegral_tendsto_integral_Ioi Y hqhint hb1
  have th := intervalIntegral_tendsto_integral_Ioi Y hint hbt
  have thL := intervalIntegral_tendsto_integral_Ioi (Y + L) hintL hb1
  constructor
  · exact le_of_tendsto_of_tendsto' (thL.const_mul μ) tqh hlower
  · exact le_of_tendsto_of_tendsto' tqh1 ((th.const_add (L * h Y)).const_mul μ) hupper

/-! ## The weight `(1 + x²)⁻⁴` -/

theorem splineWeight_nonneg (x : ℝ) : 0 ≤ splineWeight x := by unfold splineWeight; positivity

theorem continuous_splineWeight : Continuous splineWeight := by
  unfold splineWeight
  exact Continuous.inv₀ (by fun_prop) fun x => by positivity

theorem splineWeight_le (x : ℝ) (hx : 0 < x) : splineWeight x ≤ x ^ (-8 : ℝ) := by
  rw [splineWeight, Real.rpow_neg hx.le, show (8 : ℝ) = (8 : ℕ) by norm_num, Real.rpow_natCast]
  exact inv_anti₀ (by positivity) (by nlinarith [pow_pos hx 8, pow_pos hx 2, pow_pos hx 4, pow_pos hx 6])

theorem le_splineWeight (x : ℝ) (hx : 0 < x) :
    x ^ (-8 : ℝ) - 4 * x ^ (-10 : ℝ) ≤ splineWeight x := by
  have h8 : x ^ (-8 : ℝ) = (x ^ 8)⁻¹ := by
    rw [Real.rpow_neg hx.le, show (8 : ℝ) = (8 : ℕ) by norm_num, Real.rpow_natCast]
  have h10 : x ^ (-10 : ℝ) = (x ^ 10)⁻¹ := by
    rw [Real.rpow_neg hx.le, show (10 : ℝ) = (10 : ℕ) by norm_num, Real.rpow_natCast]
  rw [h8, h10, splineWeight]
  set a := (x ^ 2)⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  -- `(1 − 4a)(1 + a)⁴ ≤ 1` with `a = x⁻²`
  have key : (1 - 4 * a) * (1 + a) ^ 4 ≤ 1 := by
    nlinarith [sq_nonneg a, pow_nonneg ha0 3, pow_nonneg ha0 4, pow_nonneg ha0 5]
  have hx2 : x ^ 2 * a = 1 := by rw [ha]; field_simp
  have e1 : (x ^ 8)⁻¹ - 4 * (x ^ 10)⁻¹ = (1 - 4 * a) * a ^ 4 := by
    rw [ha]; field_simp; try ring
  have e2 : ((1 + x ^ 2) ^ 4)⁻¹ = a ^ 4 / (1 + a) ^ 4 := by
    rw [ha]; field_simp; try ring
  rw [e1, e2, le_div_iff₀ (by positivity)]
  nlinarith [pow_nonneg ha0 4, key, mul_le_mul_of_nonneg_left key (pow_nonneg ha0 4)]

theorem antitoneOn_splineWeight : AntitoneOn splineWeight (Ici 0) := by
  intro x hx y hy hxy
  simp only [splineWeight]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity)
    (by nlinarith [mem_Ici.mp hx, mem_Ici.mp hy]) 4)

theorem integrableOn_splineWeight {Y : ℝ} (hY : 0 < Y) : IntegrableOn splineWeight (Ioi Y) := by
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-8 : ℝ) < -1) hY).mono'
    (continuous_splineWeight.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_of_nonneg (splineWeight_nonneg x)]
  exact splineWeight_le x (lt_trans hY hx)

theorem integral_splineWeight_le {Y : ℝ} (hY : 0 < Y) :
    ∫ x in Ioi Y, splineWeight x ≤ Y ^ (-7 : ℝ) / 7 := by
  have hval : ∫ x in Ioi Y, x ^ (-8 : ℝ) = Y ^ (-7 : ℝ) / 7 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hY]; norm_num
  rw [← hval]
  refine setIntegral_mono_on (integrableOn_splineWeight hY)
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hY) measurableSet_Ioi fun x hx => ?_
  exact splineWeight_le x (lt_trans hY hx)

theorem le_integral_splineWeight {Y : ℝ} (hY : 0 < Y) :
    Y ^ (-7 : ℝ) / 7 - 4 * (Y ^ (-9 : ℝ) / 9) ≤ ∫ x in Ioi Y, splineWeight x := by
  have h8 : ∫ x in Ioi Y, x ^ (-8 : ℝ) = Y ^ (-7 : ℝ) / 7 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hY]; norm_num
  have h10 : ∫ x in Ioi Y, x ^ (-10 : ℝ) = Y ^ (-9 : ℝ) / 9 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hY]; norm_num
  have i8 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-8 : ℝ) < -1) hY
  have i10 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-10 : ℝ) < -1) hY
  rw [← h8, ← h10, ← integral_const_mul, ← integral_sub i8 (i10.const_mul 4)]
  exact setIntegral_mono_on (i8.sub (i10.const_mul 4)) (integrableOn_splineWeight hY)
    measurableSet_Ioi fun x hx => le_splineWeight x (lt_trans hY hx)

/-! ## The numerator `(sinh²1 + sin²x)⁴` -/

theorem continuous_splineNumerator : Continuous splineNumerator := by
  unfold splineNumerator; fun_prop

theorem splineNumerator_nonneg (x : ℝ) : 0 ≤ splineNumerator x := by
  unfold splineNumerator; positivity

theorem splineNumerator_le (x : ℝ) : splineNumerator x ≤ (Real.sinh 1 ^ 2 + 1) ^ 4 := by
  unfold splineNumerator
  exact pow_le_pow_left₀ (by positivity) (by nlinarith [Real.sin_sq_le_one x]) 4

theorem splineNumerator_periodic : Function.Periodic splineNumerator π := fun x => by
  simp [splineNumerator, Real.sin_add_pi]

/-- The mean `μ_q = π⁻¹ ∫_0^π q` of the numerator over a period. -/
def splineNumeratorMean : ℝ := (∫ x in (0 : ℝ)..π, splineNumerator x) / π

theorem splineNumeratorMean_pos : 0 < splineNumeratorMean := by
  have h : π * Real.sinh 1 ^ 8 ≤ ∫ x in (0 : ℝ)..π, splineNumerator x := by
    calc π * Real.sinh 1 ^ 8 = ∫ x in (0 : ℝ)..π, Real.sinh 1 ^ 8 := by simp
      _ ≤ ∫ x in (0 : ℝ)..π, splineNumerator x :=
          intervalIntegral.integral_mono_on Real.pi_pos.le intervalIntegrable_const
            (continuous_splineNumerator.intervalIntegrable _ _) fun x _ => by
              unfold splineNumerator
              calc Real.sinh 1 ^ 8 = (Real.sinh 1 ^ 2) ^ 4 := by ring
                _ ≤ _ := pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg (Real.sin x)]) 4
  have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
  unfold splineNumeratorMean
  exact div_pos (lt_of_lt_of_le (by positivity) h) Real.pi_pos

/-- **The modulated tail.** `Y⁷ ∫_Y^∞ q(x)(1 + x²)⁻⁴ dx → μ_q/7`. -/
theorem tendsto_rpow_seven_mul_integral_numerator_weight :
    Tendsto (fun Y : ℝ => Y ^ (7 : ℝ) * ∫ x in Ioi Y, splineNumerator x * splineWeight x) atTop
      (𝓝 (splineNumeratorMean / 7)) := by
  set μ := splineNumeratorMean
  have hμ := splineNumeratorMean_pos
  have hsq : ∀ Y : ℝ, 0 < Y → _ := fun Y hY =>
    periodic_tail_squeeze Real.pi_pos continuous_splineNumerator splineNumerator_nonneg
      splineNumerator_le splineNumerator_periodic continuous_splineWeight splineWeight_nonneg
      (antitoneOn_splineWeight.mono (Ici_subset_Ici.mpr hY.le)) (integrableOn_splineWeight hY)
  -- upper envelope `μ(π/Y + 1/7)`
  have hup : Tendsto (fun Y : ℝ => μ * (1 / 7 + π * Y⁻¹)) atTop (𝓝 (μ / 7)) := by
    have := ((tendsto_inv_atTop_zero.const_mul π).const_add (1 / 7 : ℝ)).const_mul μ
    simpa [div_eq_mul_inv] using this
  -- lower envelope `μ (Y/(Y+π))⁷ (1/7 − (4/9)(Y+π)⁻²)`
  have hlow : Tendsto (fun Y : ℝ => μ * ((Y / (Y + π)) ^ (7 : ℝ) *
      (1 / 7 - 4 / 9 * ((Y + π) ^ 2)⁻¹))) atTop (𝓝 (μ / 7)) := by
    have hr : Tendsto (fun Y : ℝ => Y / (Y + π)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun Y : ℝ => 1 - π * (Y + π)⁻¹) atTop (𝓝 (1 - π * 0)) :=
        (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ π tendsto_id)).const_mul π
          |>.const_sub 1
      refine (by simpa using h1 : Tendsto (fun Y : ℝ => 1 - π * (Y + π)⁻¹) atTop (𝓝 1)).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with Y hY
      have : Y + π ≠ 0 := by positivity
      field_simp
      try ring
    have hr7 : Tendsto (fun Y : ℝ => (Y / (Y + π)) ^ (7 : ℝ)) atTop (𝓝 1) := by
      have := hr.rpow_const (p := (7 : ℝ)) (Or.inl one_ne_zero)
      rwa [Real.one_rpow] at this
    have hs : Tendsto (fun Y : ℝ => ((Y + π) ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp
        (tendsto_atTop_add_const_right _ π tendsto_id))
    have := (hr7.mul ((hs.const_mul (4 / 9 : ℝ)).const_sub (1 / 7 : ℝ))).const_mul μ
    simpa [div_eq_mul_inv] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with Y hY
    have hYp : 0 < Y + π := by linarith [Real.pi_pos]
    have hl := le_integral_splineWeight hYp
    have hmain := (hsq Y hY).1
    have hY7 : 0 < Y ^ (7 : ℝ) := Real.rpow_pos_of_pos hY _
    have e : (Y / (Y + π)) ^ (7 : ℝ) * (1 / 7 - 4 / 9 * ((Y + π) ^ 2)⁻¹) =
        Y ^ (7 : ℝ) * ((Y + π) ^ (-7 : ℝ) / 7 - 4 * ((Y + π) ^ (-9 : ℝ) / 9)) := by
      rw [Real.div_rpow hY.le hYp.le, Real.rpow_neg hYp.le, Real.rpow_neg hYp.le,
        show (9 : ℝ) = 7 + 2 by norm_num, Real.rpow_add hYp, Real.rpow_two]
      have : 0 < (Y + π) ^ (7 : ℝ) := Real.rpow_pos_of_pos hYp _
      field_simp
      try ring
    rw [e]
    calc μ * (Y ^ (7 : ℝ) * ((Y + π) ^ (-7 : ℝ) / 7 - 4 * ((Y + π) ^ (-9 : ℝ) / 9)))
        ≤ μ * (Y ^ (7 : ℝ) * ∫ x in Ioi (Y + π), splineWeight x) := by gcongr
      _ = Y ^ (7 : ℝ) * (μ * ∫ x in Ioi (Y + π), splineWeight x) := by ring
      _ ≤ Y ^ (7 : ℝ) * ∫ x in Ioi Y, splineNumerator x * splineWeight x :=
          mul_le_mul_of_nonneg_left hmain hY7.le
  · filter_upwards [eventually_gt_atTop 0] with Y hY
    have hmain := (hsq Y hY).2
    have hu := integral_splineWeight_le hY
    have hY7 : 0 < Y ^ (7 : ℝ) := Real.rpow_pos_of_pos hY _
    have hw := splineWeight_le Y hY
    have e1 : Y ^ (7 : ℝ) * Y ^ (-8 : ℝ) = Y⁻¹ := by
      rw [← Real.rpow_add hY]; norm_num [Real.rpow_neg_one]
    have e2 : Y ^ (7 : ℝ) * (Y ^ (-7 : ℝ) / 7) = 1 / 7 := by
      rw [mul_div_assoc', ← Real.rpow_add hY]; norm_num
    calc Y ^ (7 : ℝ) * ∫ x in Ioi Y, splineNumerator x * splineWeight x
        ≤ Y ^ (7 : ℝ) * (μ * (π * splineWeight Y + ∫ x in Ioi Y, splineWeight x)) :=
          mul_le_mul_of_nonneg_left hmain hY7.le
      _ ≤ Y ^ (7 : ℝ) * (μ * (π * Y ^ (-8 : ℝ) + Y ^ (-7 : ℝ) / 7)) := by
          gcongr
      _ = μ * (π * (Y ^ (7 : ℝ) * Y ^ (-8 : ℝ)) + Y ^ (7 : ℝ) * (Y ^ (-7 : ℝ) / 7)) := by ring
      _ = μ * (1 / 7 + π * Y⁻¹) := by rw [e1, e2]; ring

/-- The tail constant `A_φ = (4/π)⁷/(16π) · μ_q/7` of the tilted spline. -/
def tiltedTailConstant : ℝ := (4 / π) ^ (7 : ℝ) / (16 * π) * (splineNumeratorMean / 7)

theorem tiltedTailConstant_pos : 0 < tiltedTailConstant := by
  have := splineNumeratorMean_pos
  have : 0 < (4 / π) ^ (7 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  unfold tiltedTailConstant
  positivity

/-- The spectral tail as a modulated tail in the variable `x = πt/4`. -/
theorem spectralTail_tiltedUnitSpline (c : ℝ) :
    spectralTail tiltedUnitSpline c =
      1 / (16 * π) * ∫ x in Ioi (π / 4 * c), splineNumerator x * splineWeight x := by
  unfold spectralTail
  simp_rw [shellSpectrum_tiltedUnitSpline]
  rw [integral_const_mul]
  have h := integral_comp_mul_left_Ioi (fun x => splineNumerator x * splineWeight x) c
    (by positivity : (0 : ℝ) < π / 4)
  simp only [smul_eq_mul] at h
  have e : ∀ t : ℝ, π * t / 4 = π / 4 * t := fun t => by ring
  simp_rw [e]
  rw [h]
  field_simp
  ring

/-- **The tilted spline has a regular spectral tail**: `c⁷ T(c) → A_φ > 0`. -/
theorem tendsto_rpow_seven_mul_spectralTail_tiltedUnitSpline :
    Tendsto (fun c : ℝ => c ^ (7 : ℝ) * spectralTail tiltedUnitSpline c) atTop
      (𝓝 tiltedTailConstant) := by
  have hY : Tendsto (fun c : ℝ => π / 4 * c) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have h := (tendsto_rpow_seven_mul_integral_numerator_weight.comp hY).const_mul
    ((4 / π) ^ (7 : ℝ) / (16 * π))
  unfold tiltedTailConstant
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  simp only [Function.comp, spectralTail_tiltedUnitSpline]
  rw [Real.mul_rpow (by positivity) hc.le, Real.div_rpow (by norm_num) Real.pi_pos.le]
  have : 0 < π ^ (7 : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
  field_simp
  rw [← Real.mul_rpow (by norm_num) (by positivity), show (4 : ℝ) * (π / 4) = π by ring]

/-! ## The rescaled limit of the tilted spline -/

/-- **Jordan-totient rescaled limit of the tilted spline, Möbius form.**
`c⁷ E_m(c) → (2A_φ/M) ζ(8) J₈(m)/φ(m)`. -/
theorem tendsto_rpow_seven_mul_completedConductorEnergy_tiltedUnitSpline (m : ℕ) :
    Tendsto (fun c => c ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline c m) atTop
      (𝓝 (2 / (∫ u, tiltedUnitSpline u ^ 2) * tiltedTailConstant * zetaSum 8 *
        jordanTotient 8 m / m.totient)) := by
  have h := tendsto_rpow_mul_completedConductorEnergy contDiff_tiltedUnitSpline
    (fun u hu => tiltedUnitSpline_eq_zero u hu) integral_tiltedUnitSpline_sq_pos
    (by norm_num : (0 : ℝ) < 7) tendsto_rpow_seven_mul_spectralTail_tiltedUnitSpline m
  norm_num at h ⊢
  exact h

/-- **Jordan-totient rescaled limit of the tilted spline, coprime form.** The limit is
`(2A_φ/(Mφ(m))) m⁸ Σ_{(n,m)=1} n⁻⁸ > 0`. -/
theorem tendsto_rpow_seven_mul_completedConductorEnergy_tiltedUnitSpline_coprime {m : ℕ}
    (hm : 0 < m) :
    Tendsto (fun c => c ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline c m) atTop
      (𝓝 (2 / ((∫ u, tiltedUnitSpline u ^ 2) * m.totient) * (m : ℝ) ^ (8 : ℝ) *
        tiltedTailConstant * coprimeZetaSum 8 m)) ∧
    0 < 2 / ((∫ u, tiltedUnitSpline u ^ 2) * m.totient) * (m : ℝ) ^ (8 : ℝ) *
        tiltedTailConstant * coprimeZetaSum 8 m := by
  have h := tendsto_rpow_mul_completedConductorEnergy_coprime contDiff_tiltedUnitSpline
    (fun u hu => tiltedUnitSpline_eq_zero u hu) integral_tiltedUnitSpline_sq_pos
    (by norm_num : (0 : ℝ) < 7) tendsto_rpow_seven_mul_spectralTail_tiltedUnitSpline hm
  have hp := jordanLimit_pos (by norm_num : (0 : ℝ) < 7) tiltedTailConstant_pos
    integral_tiltedUnitSpline_sq_pos hm
  norm_num at h hp ⊢
  exact ⟨h, hp⟩

/-- **The Jordan identity of exponent `8`**, `ζ(8) J₈(m) = m⁸ Σ_{(n,m)=1} n⁻⁸`, read off the
degeneration of the tilted spline. -/
theorem zetaSum_eight_mul_jordanTotient_eight {m : ℕ} (hm : 0 < m) :
    zetaSum 8 * jordanTotient 8 m = (m : ℝ) ^ (8 : ℝ) * coprimeZetaSum 8 m := by
  have h := zetaSum_mul_jordanTotient_eq contDiff_tiltedUnitSpline
    (fun u hu => tiltedUnitSpline_eq_zero u hu) integral_tiltedUnitSpline_sq_pos
    (by norm_num : (0 : ℝ) < 7) tiltedTailConstant_pos.ne'
    tendsto_rpow_seven_mul_spectralTail_tiltedUnitSpline hm
  norm_num at h ⊢
  exact h

/-- The Jordan totient of exponent `8` is positive. -/
theorem jordanTotient_eight_pos {m : ℕ} (hm : 0 < m) : 0 < jordanTotient 8 m := by
  have h := zetaSum_eight_mul_jordanTotient_eight hm
  have hz : 0 < zetaSum 8 := by
    have := one_le_coprimeZetaSum (k := 8) (by norm_num) 1
    have hle : coprimeZetaSum 8 1 = zetaSum 8 := by
      simp [coprimeZetaSum, zetaSum]
    linarith
  have hr : 0 < (m : ℝ) ^ (8 : ℝ) * coprimeZetaSum 8 m := by
    have := one_le_coprimeZetaSum (k := 8) (by norm_num) m
    have : (0 : ℝ) < (m : ℝ) ^ (8 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hm) _
    positivity
  rw [← h] at hr
  exact pos_of_mul_pos_right hr hz.le

end GaloisForLFunctions.ArithmeticDegenerationTheory
