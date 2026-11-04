import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicGap
import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine
import GaloisForLFunctions.SignedWindowCriticality.TheKickIsAPositiveSourceAndANegativeCollarConductance

/-!
# The light cone of a collar carries its reflection

A collar `C = [c − h, c + h]` carries the reflection `R(u) = 2c − u`. In reference coordinates
`F(s) = f(c + hs)` it is `[−1, 1]` with `R(s) = −s`, and the regional logarithmic energy
`E(F) = ∫∫(F(x) − F(y))²/(2|x − y|)` has the Legendre spectrum `2H_n` (LST).

* **Reflection inequality** (`integral_sub_reflect_sq_add_le`, sharp by
  `integral_sub_reflect_sq_id`). `∫(F − F∘R)² + ½E(F + F∘R) ≤ 2E(F)`, with equality for `F(s) = s`.
  The odd part `F − F∘R` has mean zero, so the first Legendre gap `2H₁ = 2` bounds its mass by half
  its energy; the parallelogram law `E(F − F∘R) + E(F + F∘R) = 4E(F)` closes the estimate.
* **Reflection pairing** (`neg_half_regionalLogEnergy_le_integral_mul_reflect`).
  `∫F·F∘R ≥ −½E(F)`, sharp at `F(s) = s`.
* **Physical collar** (`collarLogEnergy_eq`, `neg_half_collarLogEnergy_le`). With
  `E_C(f) = ∫_C∫_C (f(u) − f(v))²/(2|u − v|)` one has `E_C(f) = h E(F)` and
  `∫_C f(u) f(2c − u) du ≥ −½E_C(f)`.
* **Light cone** (`exp_neg_mul_collarLogEnergy_le`). The archimedean jump energy of the pairs
  inside the collar, `A_C(f) = ½∫_C∫_C ω(|u − v|)(f(u) − f(v))²`, satisfies `e^{−h}E_C(f) ≤ 2A_C(f)`,
  since `ω(t) ≥ e^{−t/2}/(2t)`.
* **Prime anti-diagonals** (`neg_collarLogEnergy_le_kick`, `kick_add_collarLevyEnergy_nonneg`).
  For an odd `f` supported in `[−a, a]` and `ℓ/2 < a`, the prime term `−2w∫f(t)f(t + ℓ)dt` of
  weight `w ≥ 0` is the anti-diagonal pairing on the collar `[ℓ − a, a]`, and
  `−2w∫f(t)f(t + ℓ) + 2we^{h}A_C(f) ≥ 0`, `h = a − ℓ/2`.

For `ℓ = log n`, `w = Λ(n)n^{−1/2}`, the collar's light cone therefore carries the frustrated
anti-diagonal of `n` at the ratio `2Λ(n)n^{−1/2}e^{h}`; in the regional model (`A_C = ½E_C`) the
ratio `2Λ(n)n^{−1/2}` is attained by the linear profile. The ratio `√2 log 2` of the first prime is
below `1` (`two_mul_log_two_div_sqrt_two_lt_one`), so a thin collar of prime `2` pays its own
frustration; that of `3` is above `1` (`one_lt_two_mul_log_three_div_sqrt_three`), so in the
regional model the collar of prime `3` cannot pay its own frustration.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open GaloisForLFunctions.LatticeSectionTheory GaloisForLFunctions.SelectivePositivityAndThresholdLaws

local notation "ν" => volume.restrict (Icc (-1 : ℝ) 1)

/-! ### Reflection of the reference collar -/

theorem measurePreserving_neg_Icc : MeasurePreserving (Neg.neg : ℝ → ℝ) ν ν := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Icc (a := (-1 : ℝ)) (b := 1))
  have hs : (Neg.neg : ℝ → ℝ) ⁻¹' Icc (-1 : ℝ) 1 = Icc (-1) 1 := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  rwa [hs] at h

theorem setIntegral_Icc_comp_neg (g : ℝ → ℝ) :
    (∫ x in Icc (-1 : ℝ) 1, g (-x)) = ∫ x in Icc (-1 : ℝ) 1, g x :=
  measurePreserving_neg_Icc.integral_comp (MeasurableEquiv.neg ℝ).measurableEmbedding g

theorem regionalLogPair_comp_neg (F G : ℝ → ℝ) :
    regionalLogPair (fun x => F (-x)) (fun x => G (-x)) = regionalLogPair F G := by
  unfold regionalLogPair
  have hP : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ℝ → ℝ))
      ((ν).prod ν) ((ν).prod ν) :=
    measurePreserving_neg_Icc.prod measurePreserving_neg_Icc
  have hE : MeasurableEmbedding (Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ℝ → ℝ)) :=
    ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)).measurableEmbedding
  have key := hP.integral_comp hE
    (fun q : ℝ × ℝ => (F q.1 - F q.2) * (G q.1 - G q.2) / (2 * |q.1 - q.2|))
  rw [← key]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [Prod.map_fst, Prod.map_snd]
  have : |-p.1 - -p.2| = |p.1 - p.2| := by
    rw [show -p.1 - -p.2 = -(p.1 - p.2) by ring, abs_neg]
  rw [this]

theorem regionalLogEnergy_comp_neg (F : ℝ → ℝ) :
    regionalLogEnergy (fun x => F (-x)) = regionalLogEnergy F :=
  regionalLogPair_comp_neg F F

/-- The parallelogram law of the regional energy for the reflection. -/
theorem regionalLogEnergy_parallelogram {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    regionalLogEnergy (fun x => F x - F (-x)) + regionalLogEnergy (fun x => F x + F (-x)) =
      4 * regionalLogEnergy F := by
  have hN : ContDiff ℝ 1 (fun x => F (-x)) := hF.comp contDiff_neg
  have h1 := regionalLogEnergy_sub hF hN
  have h2 := regionalLogEnergy_sub hF hN.neg
  have e1 : regionalLogEnergy (fun x => F x - -F (-x)) =
      regionalLogEnergy (fun x => F x + F (-x)) :=
    congrArg regionalLogEnergy (funext fun x => by ring)
  have e2 : regionalLogEnergy (fun x => -F (-x)) = regionalLogEnergy (fun x => F (-x)) := by
    unfold regionalLogEnergy regionalLogPair
    exact integral_congr_ae (Eventually.of_forall fun p => by simp only; ring)
  have e3 : regionalLogPair F (fun x => -F (-x)) = -regionalLogPair F (fun x => F (-x)) := by
    unfold regionalLogPair
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun p => by simp only; ring)
  rw [e1, e2, e3] at h2
  rw [h1, h2, regionalLogEnergy_comp_neg]
  ring

/-- The odd part of a test has mean zero on the reference collar. -/
theorem regionalLegendreMoment_zero_sub_reflect {F : ℝ → ℝ} (hF : Continuous F) :
    regionalLegendreMoment (fun x => F x - F (-x)) 0 = 0 := by
  unfold regionalLegendreMoment
  simp only [legP, mul_one]
  have hi1 : Integrable F ν := hF.integrableOn_Icc
  have hi2 : Integrable (fun x => F (-x)) ν := (hF.comp continuous_neg).integrableOn_Icc
  rw [integral_sub hi1 hi2, setIntegral_Icc_comp_neg F, sub_self]

/-- The first Legendre gap on the odd part. -/
theorem two_mul_integral_sub_reflect_sq_le {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    2 * (∫ x in Icc (-1 : ℝ) 1, (F x - F (-x)) ^ 2) ≤
      regionalLogEnergy (fun x => F x - F (-x)) := by
  have hG : ContDiff ℝ 1 (fun x => F x - F (-x)) := hF.sub (hF.comp contDiff_neg)
  have h := regionalLogEnergy_moment_gap hG 1 (fun n hn => by
    have : n = 0 := by omega
    subst this
    exact regionalLegendreMoment_zero_sub_reflect hF.continuous)
  norm_num [regionalLogEigenvalue, Finset.sum_range_succ] at h
  exact h

/-- **Reflection inequality.** `∫(F − F∘R)² + ½E(F + F∘R) ≤ 2E(F)` on the reference collar. -/
theorem integral_sub_reflect_sq_add_le {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    (∫ x in Icc (-1 : ℝ) 1, (F x - F (-x)) ^ 2) +
        regionalLogEnergy (fun x => F x + F (-x)) / 2 ≤ 2 * regionalLogEnergy F := by
  have h1 := two_mul_integral_sub_reflect_sq_le hF
  have h2 := regionalLogEnergy_parallelogram hF
  linarith

/-- **Reflection pairing.** `∫F·F∘R ≥ −½E(F)` on the reference collar. -/
theorem neg_half_regionalLogEnergy_le_integral_mul_reflect {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    -(regionalLogEnergy F / 2) ≤ ∫ x in Icc (-1 : ℝ) 1, F x * F (-x) := by
  have hc := hF.continuous
  have hN : Continuous fun x => F (-x) := hc.comp continuous_neg
  have hi1 : Integrable (fun x => (F x + F (-x)) ^ 2) ν := ((hc.add hN).pow 2).integrableOn_Icc
  have hi2 : Integrable (fun x => (F x - F (-x)) ^ 2) ν := ((hc.sub hN).pow 2).integrableOn_Icc
  have e : (∫ x in Icc (-1 : ℝ) 1, F x * F (-x)) =
      ((∫ x in Icc (-1 : ℝ) 1, (F x + F (-x)) ^ 2) -
        ∫ x in Icc (-1 : ℝ) 1, (F x - F (-x)) ^ 2) / 4 := by
    rw [← integral_sub hi1 hi2, ← integral_div]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have hH : 0 ≤ ∫ x in Icc (-1 : ℝ) 1, (F x + F (-x)) ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  have hE := regionalLogEnergy_nonneg (fun x => F x + F (-x))
  have hG := integral_sub_reflect_sq_add_le hF
  rw [e]
  linarith

/-- The regional energy of the linear profile is `4/3`. -/
theorem regionalLogEnergy_id : regionalLogEnergy (fun x => x) = 4 / 3 := by
  have h := regionalLogEnergy_legendreSum {1} (fun _ => 1)
  have he : regionalLegendreSum {1} (fun _ => (1 : ℝ)) = fun x => x := by
    funext x
    simp [regionalLegendreSum, legP_one]
  rw [he] at h
  rw [h]
  norm_num [regionalLogEigenvalue]

/-- **Sharpness.** The linear profile attains the reflection inequality. -/
theorem integral_sub_reflect_sq_id :
    (∫ x in Icc (-1 : ℝ) 1, (x - -x) ^ 2) + regionalLogEnergy (fun x : ℝ => x + -x) / 2 =
      2 * regionalLogEnergy (fun x : ℝ => x) := by
  have h0 : regionalLogEnergy (fun x : ℝ => x + -x) = 0 := by
    unfold regionalLogEnergy regionalLogPair
    simp
  have hi : (∫ x in Icc (-1 : ℝ) 1, (x - -x) ^ 2) = 8 / 3 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    have hf : (fun x : ℝ => (x - -x) ^ 2) = fun x => 4 * x ^ 2 := by funext x; ring
    rw [hf, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [h0, hi, regionalLogEnergy_id]
  norm_num

/-! ### The physical collar -/

/-- `h ∫_{−1}^{1} g(c + hx) dx = ∫_{c−h}^{c+h} g`. -/
theorem collar_rescale {h : ℝ} (hh : 0 ≤ h) (c : ℝ) (g : ℝ → ℝ) :
    h * (∫ x in Icc (-1 : ℝ) 1, g (c + h * x)) = ∫ u in Icc (c - h) (c + h), g u := by
  have e := intervalIntegral.smul_integral_comp_mul_add (a := (-1 : ℝ)) (b := 1) g h c
  have hl : h * (-1) + c = c - h := by ring
  have hr : h * 1 + c = c + h := by ring
  have hf : (fun x => g (h * x + c)) = fun x => g (c + h * x) := by funext x; rw [add_comm]
  rw [hl, hr, hf] at e
  simpa only [smul_eq_mul, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by linarith : c - h ≤ c + h),
    ← integral_Icc_eq_integral_Ioc] using e

/-- The regional logarithmic energy of the collar `[c − h, c + h]`. -/
def collarLogEnergy (c h : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ u in Icc (c - h) (c + h), ∫ v in Icc (c - h) (c + h), (f u - f v) ^ 2 / (2 * |u - v|)

theorem collar_kernel_rescale {h : ℝ} (hh : 0 < h) (c : ℝ) (f : ℝ → ℝ) (x y : ℝ) :
    (f (c + h * x) - f (c + h * y)) * (f (c + h * x) - f (c + h * y)) / (2 * |x - y|) =
      h * ((f (c + h * x) - f (c + h * y)) ^ 2 / (2 * |c + h * x - (c + h * y)|)) := by
  rw [show c + h * x - (c + h * y) = h * (x - y) by ring, abs_mul, abs_of_pos hh]
  by_cases hxy : x = y
  · subst hxy; simp
  · have : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    field_simp

/-- `E_C(f) = h E(F)`, `F(s) = f(c + hs)`. -/
theorem collarLogEnergy_eq {h : ℝ} (hh : 0 < h) (c : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    collarLogEnergy c h f = h * regionalLogEnergy (fun s => f (c + h * s)) := by
  have hF : ContDiff ℝ 1 (fun s => f (c + h * s)) :=
    hf.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  set k : ℝ → ℝ → ℝ := fun u v => (f u - f v) ^ 2 / (2 * |u - v|) with hk
  have hrow : ∀ x, (∫ y in Icc (-1 : ℝ) 1,
      (f (c + h * x) - f (c + h * y)) * (f (c + h * x) - f (c + h * y)) / (2 * |x - y|)) =
      ∫ v in Icc (c - h) (c + h), k (c + h * x) v := by
    intro x
    rw [← collar_rescale hh.le c (k (c + h * x)), ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => collar_kernel_rescale hh c f x y)
  unfold regionalLogEnergy regionalLogPair
  rw [integral_prod _ (regionalLogPair_integrable hF hF)]
  dsimp only
  have hx : (∫ x in Icc (-1 : ℝ) 1, ∫ y in Icc (-1 : ℝ) 1,
      (f (c + h * x) - f (c + h * y)) * (f (c + h * x) - f (c + h * y)) / (2 * |x - y|)) =
      ∫ x in Icc (-1 : ℝ) 1, (fun u => ∫ v in Icc (c - h) (c + h), k u v) (c + h * x) :=
    integral_congr_ae (Eventually.of_forall hrow)
  rw [hx, collar_rescale hh.le c (fun u => ∫ v in Icc (c - h) (c + h), k u v)]
  rfl

/-- **Reflection pairing on a physical collar.** `∫_C f(u)f(2c − u) du ≥ −½E_C(f)`. -/
theorem neg_half_collarLogEnergy_le {h : ℝ} (hh : 0 < h) (c : ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) :
    -(collarLogEnergy c h f / 2) ≤ ∫ u in Icc (c - h) (c + h), f u * f (2 * c - u) := by
  have hF : ContDiff ℝ 1 (fun s => f (c + h * s)) :=
    hf.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have h1 := neg_half_regionalLogEnergy_le_integral_mul_reflect hF
  have h2 := collar_rescale hh.le c (fun u => f u * f (2 * c - u))
  have hre : (∫ x in Icc (-1 : ℝ) 1, f (c + h * x) * f (c + h * -x)) =
      ∫ x in Icc (-1 : ℝ) 1, (fun u => f u * f (2 * c - u)) (c + h * x) :=
    integral_congr_ae (Eventually.of_forall fun x => by
      simp only
      rw [show c + h * -x = 2 * c - (c + h * x) by ring])
  rw [collarLogEnergy_eq hh c hf, ← h2, ← hre]
  have := mul_le_mul_of_nonneg_left h1 hh.le
  linarith

/-! ### The light cone of the collar -/

/-- The archimedean jump energy of the pairs inside the collar `[c − h, c + h]`. -/
def collarLevyEnergy (c h : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ u in Icc (c - h) (c + h), ∫ v in Icc (c - h) (c + h),
    _root_.RHTower.archLevyDensity |u - v| * (f u - f v) ^ 2) / 2

theorem archLevyDensity_ge_exp_div {t : ℝ} (ht : 0 < t) :
    Real.exp (-t / 2) / (2 * t) ≤ _root_.RHTower.archLevyDensity t := by
  unfold _root_.RHTower.archLevyDensity
  have h1 : 1 - Real.exp (-2 * t) ≤ 2 * t := by linarith [Real.add_one_le_exp (-2 * t)]
  have h2 : 0 < 1 - Real.exp (-2 * t) := by
    have : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le h2 h1

theorem archLevyDensity_mul_le {t : ℝ} (ht : 0 < t) :
    _root_.RHTower.archLevyDensity t * t ≤ (1 + 2 * t) / 2 := by
  unfold _root_.RHTower.archLevyDensity
  have hlt : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < 1 - Real.exp (-2 * t) := by linarith
  have he : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  -- `1 − e^{−2t} ≥ 2t/(1 + 2t)` from `e^{2t} ≥ 1 + 2t`.
  have h1 : 1 + 2 * t ≤ Real.exp (2 * t) := by linarith [Real.add_one_le_exp (2 * t)]
  have h2 : Real.exp (-2 * t) * Real.exp (2 * t) = 1 := by rw [← Real.exp_add]; simp
  have hden : 2 * t ≤ (1 - Real.exp (-2 * t)) * (1 + 2 * t) := by
    nlinarith [Real.exp_pos (-2 * t)]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hpos (by norm_num)]
  nlinarith [Real.exp_pos (-t / 2)]

theorem collar_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (c h : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ Icc (c - h) (c + h), ∀ v ∈ Icc (c - h) (c + h),
      |f u - f v| ≤ K * |u - v| := by
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_Icc (c - h) (c + h)) isCompact_Icc
  refine ⟨K, K.coe_nonneg, fun u hu v hv => ?_⟩
  simpa only [Real.dist_eq] using hK.dist_le_mul u hu v hv

theorem integrableOn_collar_of_bound {g : ℝ → ℝ} (hg : Measurable g) {B p q : ℝ}
    (hb : ∀ v ∈ Icc p q, |g v| ≤ B) : IntegrableOn g (Icc p q) :=
  Measure.integrableOn_of_bounded (M := B) measure_Icc_lt_top.ne hg.aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      rw [Real.norm_eq_abs]
      exact hb v hv)

/-- **The light cone of the collar dominates its regional energy.** `e^{−h}E_C(f) ≤ 2A_C(f)`. -/
theorem exp_neg_mul_collarLogEnergy_le {h : ℝ} (hh : 0 < h) (c : ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) :
    Real.exp (-h) * collarLogEnergy c h f ≤ 2 * collarLevyEnergy c h f := by
  obtain ⟨K, hK0, hK⟩ := collar_lipschitz hf c h
  have hfc := hf.continuous
  set ω := _root_.RHTower.archLevyDensity
  have hdist : ∀ u ∈ Icc (c - h) (c + h), ∀ v ∈ Icc (c - h) (c + h), |u - v| ≤ 2 * h :=
    fun u hu v hv => by rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  -- pointwise comparison of the kernels
  have hpt : ∀ u ∈ Icc (c - h) (c + h), ∀ v ∈ Icc (c - h) (c + h),
      Real.exp (-h) * ((f u - f v) ^ 2 / (2 * |u - v|)) ≤ ω |u - v| * (f u - f v) ^ 2 := by
    intro u hu v hv
    by_cases huv : u = v
    · subst huv; simp
    · have ht : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
      have hω := archLevyDensity_ge_exp_div ht
      have hexp : Real.exp (-h) ≤ Real.exp (-|u - v| / 2) :=
        Real.exp_le_exp.mpr (by linarith [hdist u hu v hv])
      have : Real.exp (-h) / (2 * |u - v|) ≤ ω |u - v| :=
        le_trans (div_le_div_of_nonneg_right hexp (by positivity)) hω
      calc Real.exp (-h) * ((f u - f v) ^ 2 / (2 * |u - v|))
          = Real.exp (-h) / (2 * |u - v|) * (f u - f v) ^ 2 := by ring
        _ ≤ ω |u - v| * (f u - f v) ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
  -- bounds for integrability
  have hbL : ∀ u ∈ Icc (c - h) (c + h), ∀ v ∈ Icc (c - h) (c + h),
      |(f u - f v) ^ 2 / (2 * |u - v|)| ≤ K ^ 2 * h := by
    intro u hu v hv
    by_cases huv : u = v
    · subst huv; simp; positivity
    · have ht : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
      have hL := hK u hu v hv
      have hsq : (f u - f v) ^ 2 ≤ K ^ 2 * |u - v| ^ 2 := by
        rw [← sq_abs (f u - f v)]
        nlinarith [abs_nonneg (f u - f v)]
      rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
      nlinarith [hdist u hu v hv, sq_nonneg K]
  have hbA : ∀ u ∈ Icc (c - h) (c + h), ∀ v ∈ Icc (c - h) (c + h),
      |ω |u - v| * (f u - f v) ^ 2| ≤ K ^ 2 * (1 + 4 * h) * h := by
    intro u hu v hv
    by_cases huv : u = v
    · subst huv; simp; positivity
    · have ht : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
      have hL := hK u hu v hv
      have hsq : (f u - f v) ^ 2 ≤ K ^ 2 * |u - v| ^ 2 := by
        rw [← sq_abs (f u - f v)]
        nlinarith [abs_nonneg (f u - f v)]
      have hω0 : 0 ≤ ω |u - v| := (RHTower.archLevyDensity_pos ht).le
      have hωt := archLevyDensity_mul_le ht
      have hd := hdist u hu v hv
      rw [abs_of_nonneg (mul_nonneg hω0 (sq_nonneg _))]
      calc ω |u - v| * (f u - f v) ^ 2 ≤ ω |u - v| * (K ^ 2 * |u - v| ^ 2) :=
            mul_le_mul_of_nonneg_left hsq hω0
        _ = K ^ 2 * |u - v| * (ω |u - v| * |u - v|) := by ring
        _ ≤ K ^ 2 * |u - v| * ((1 + 2 * |u - v|) / 2) :=
            mul_le_mul_of_nonneg_left hωt (by positivity)
        _ ≤ K ^ 2 * (2 * h) * ((1 + 2 * (2 * h)) / 2) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hd (sq_nonneg K)) (by linarith)
              (by positivity) (by positivity)
        _ = K ^ 2 * (1 + 4 * h) * h := by ring
  have hmL : ∀ u, Measurable fun v => (f u - f v) ^ 2 / (2 * |u - v|) := fun u =>
    ((continuous_const.sub hfc).pow 2).measurable.div
      (continuous_const.mul (continuous_const.sub continuous_id).abs).measurable
  have hmA : ∀ u, Measurable fun v => ω |u - v| * (f u - f v) ^ 2 := fun u =>
    (RHTower.measurable_archLevyDensity.comp
      (continuous_const.sub continuous_id).abs.measurable).mul
      ((continuous_const.sub hfc).pow 2).measurable
  -- the inner integrals
  have hin : ∀ u ∈ Icc (c - h) (c + h),
      Real.exp (-h) * (∫ v in Icc (c - h) (c + h), (f u - f v) ^ 2 / (2 * |u - v|)) ≤
        ∫ v in Icc (c - h) (c + h), ω |u - v| * (f u - f v) ^ 2 := by
    intro u hu
    rw [← integral_const_mul]
    exact setIntegral_mono_on ((integrableOn_collar_of_bound (hmL u) (hbL u hu)).const_mul _)
      (integrableOn_collar_of_bound (hmA u) (hbA u hu)) measurableSet_Icc
      fun v hv => hpt u hu v hv
  -- the outer integrals: measurability of the rows from the product
  have hcp : Continuous fun p : ℝ × ℝ => (f p.1 - f p.2) ^ 2 := by fun_prop
  have hcd : Continuous fun p : ℝ × ℝ => 2 * |p.1 - p.2| := by fun_prop
  have hca : Continuous fun p : ℝ × ℝ => |p.1 - p.2| := by fun_prop
  have hjL : Measurable fun p : ℝ × ℝ => (f p.1 - f p.2) ^ 2 / (2 * |p.1 - p.2|) :=
    hcp.measurable.div hcd.measurable
  have hjA : Measurable fun p : ℝ × ℝ => ω |p.1 - p.2| * (f p.1 - f p.2) ^ 2 :=
    (RHTower.measurable_archLevyDensity.comp hca.measurable).mul hcp.measurable
  have hrowL : Measurable fun u => ∫ v in Icc (c - h) (c + h), (f u - f v) ^ 2 / (2 * |u - v|) :=
    by exact hjL.stronglyMeasurable.integral_prod_right'.measurable
  have hrowA : Measurable fun u => ∫ v in Icc (c - h) (c + h), ω |u - v| * (f u - f v) ^ 2 :=
    by exact hjA.stronglyMeasurable.integral_prod_right'.measurable
  have hvol : volume.real (Icc (c - h) (c + h)) = 2 * h := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hrbL : ∀ u ∈ Icc (c - h) (c + h),
      |∫ v in Icc (c - h) (c + h), (f u - f v) ^ 2 / (2 * |u - v|)| ≤ K ^ 2 * h * (2 * h) := by
    intro u hu
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (c - h) (c + h))
      measure_Icc_lt_top (C := K ^ 2 * h) fun v hv => by
        rw [Real.norm_eq_abs]; exact hbL u hu v hv
    rw [Real.norm_eq_abs, hvol] at this
    linarith
  have hrbA : ∀ u ∈ Icc (c - h) (c + h),
      |∫ v in Icc (c - h) (c + h), ω |u - v| * (f u - f v) ^ 2| ≤
        K ^ 2 * (1 + 4 * h) * h * (2 * h) := by
    intro u hu
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (c - h) (c + h))
      measure_Icc_lt_top (C := K ^ 2 * (1 + 4 * h) * h) fun v hv => by
        rw [Real.norm_eq_abs]; exact hbA u hu v hv
    rw [Real.norm_eq_abs, hvol] at this
    linarith
  unfold collarLogEnergy collarLevyEnergy
  rw [← integral_const_mul]
  have := setIntegral_mono_on ((integrableOn_collar_of_bound hrowL hrbL).const_mul _)
    (integrableOn_collar_of_bound hrowA hrbA) measurableSet_Icc hin
  linarith

/-! ### Prime anti-diagonals -/

/-- **The prime term on an odd test is an anti-diagonal pairing on its collar, bounded by the
collar's regional energy.** For odd `f` supported in `[−a, a]`, `ℓ/2 < a`, and `w ≥ 0`:
`−2w∫f(t)f(t + ℓ)dt ≥ −wE_C(f)`, `C = [ℓ − a, a]`. -/
theorem neg_collarLogEnergy_le_kick {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {ℓ a w : ℝ} (hw : 0 ≤ w)
    (hℓa : ℓ / 2 < a) (hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0) (hodd : ∀ x, f (-x) = -f x) :
    -(w * collarLogEnergy (ℓ / 2) (a - ℓ / 2) f) ≤ -2 * w * ∫ t, f t * f (t + ℓ) := by
  have hcorr := integral_mul_shift_eq_neg_antidiagonal hodd ℓ
  have hC : (∫ s, f s * f (ℓ - s)) = ∫ s in Icc (ℓ - a) a, f s * f (ℓ - s) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_).symm
    simp only [mem_Icc, not_and_or, not_le] at hs
    rcases hs with hs | hs
    · rw [hsupp (ℓ - s) fun h => by linarith [h.2], mul_zero]
    · rw [hsupp s fun h => by linarith [h.2], zero_mul]
  have hpair := neg_half_collarLogEnergy_le (c := ℓ / 2) (by linarith : 0 < a - ℓ / 2) hf
  have he1 : ℓ / 2 - (a - ℓ / 2) = ℓ - a := by ring
  have he2 : ℓ / 2 + (a - ℓ / 2) = a := by ring
  have he3 : ∀ s, 2 * (ℓ / 2) - s = ℓ - s := fun s => by ring
  simp only [he1, he2, he3] at hpair
  rw [hcorr, hC]
  nlinarith [mul_le_mul_of_nonneg_left hpair hw]

/-- **The light cone of the collar carries the anti-diagonal at the ratio `2we^h`.** For odd `f`
supported in `[−a, a]`, `ℓ/2 < a`, `w ≥ 0`, `h = a − ℓ/2`:
`−2w∫f(t)f(t + ℓ)dt + 2we^{h}A_C(f) ≥ 0`. -/
theorem kick_add_collarLevyEnergy_nonneg {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {ℓ a w : ℝ}
    (hw : 0 ≤ w) (hℓa : ℓ / 2 < a) (hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0)
    (hodd : ∀ x, f (-x) = -f x) :
    0 ≤ -2 * w * (∫ t, f t * f (t + ℓ)) +
      2 * w * Real.exp (a - ℓ / 2) * collarLevyEnergy (ℓ / 2) (a - ℓ / 2) f := by
  have h1 := neg_collarLogEnergy_le_kick hf hw hℓa hsupp hodd
  have h2 := exp_neg_mul_collarLogEnergy_le (c := ℓ / 2) (by linarith : 0 < a - ℓ / 2) hf
  have hE : collarLogEnergy (ℓ / 2) (a - ℓ / 2) f ≤
      2 * Real.exp (a - ℓ / 2) * collarLevyEnergy (ℓ / 2) (a - ℓ / 2) f := by
    have hx : Real.exp (a - ℓ / 2) * Real.exp (-(a - ℓ / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (a - ℓ / 2)).le
    rw [← mul_assoc, hx, one_mul] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hE hw]

/-! ### The first two primes -/

/-- The ratio of the first prime: `2 log 2/√2 = √2 log 2 < 1`. -/
theorem two_mul_log_two_div_sqrt_two_lt_one : 2 * Real.log 2 / Real.sqrt 2 < 1 := by
  have hs : (1.4142 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hl := Real.log_two_lt_d9
  rw [div_lt_one (by positivity)]
  linarith

/-- The ratio of the second prime: `2 log 3/√3 > 1`. -/
theorem one_lt_two_mul_log_three_div_sqrt_three : 1 < 2 * Real.log 3 / Real.sqrt 3 := by
  have hs : Real.sqrt 3 < 1.7321 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hl : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  rw [one_lt_div (by positivity)]
  linarith

end GaloisForLFunctions.SignedWindowCriticality

end
