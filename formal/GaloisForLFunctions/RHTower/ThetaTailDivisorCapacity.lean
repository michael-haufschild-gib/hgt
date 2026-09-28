import GaloisForLFunctions.RHTower.ThetaRelativeSourceRigidity
import GaloisForLFunctions.RHTower.XiMassHeightTransfer
import GaloisForLFunctions.RHTower.XiHeightAdaptiveHedenmalmCensusCollision
import GaloisForLFunctions.HTGeometry.JensenIntegratedCountBound

/-!
# Sharp theta-tail capacity for the complete Xi divisor

If `|u(x)| ≤ C exp(-a e^{b|x|})` and the transform `H(z) = ∫ e^{-izx} u(x) dx` vanishes at every
zero of `F = XiC` to at least its multiplicity, then `u = 0` a.e. as soon as `b > 2`.

Source decay sets the angular growth capacity: the Legendre bound
`y v - (a/2) e^{bv} ≤ (y/b) log(1 + 2y/(ab))` gives `log|H(z)| ≤ (|Im z|/b) log(1 + 2|Im z|/(ab)) +
O(1)`, and the angular average of `|Im z|` on a circle is `|Im c| + (2/π)R`, so the circle average
of `log|H|` is at most `(2/(πb)) R log R + O(R)`. The complete Xi divisor fills every large disc:
the symmetric Riemann–von Mangoldt mass `(1/π) T log T` of the rectangle of height `T` sits in
`closedBall c (T + 3/2 + |c|)` in the `XiC` coordinate. Jensen's formula with the integrated count
then forces `1/π ≤ 2/(πb)`, i.e. `b ≤ 2`.
-/

open MeasureTheory Set Filter Topology Complex Metric

namespace RHTower

noncomputable section

/-! ## Double-exponential sources -/

/-- **The Legendre bound.** `y v - (a/2) e^{bv} ≤ (y/b) log(1 + 2y/(ab))` for `y, v ≥ 0`. -/
theorem legendre_doubleExp_le {a b y v : ℝ} (ha : 0 < a) (hb : 0 < b) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    y * v - a / 2 * Real.exp (b * v) ≤ y / b * Real.log (1 + 2 * y / (a * b)) := by
  set t := 2 * y / (a * b) with ht
  have ht0 : 0 ≤ t := by positivity
  set L := Real.log (1 + t) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hLt : L ≤ t := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith); linarith
  have hexp : (1 + t) * (1 + b * v - L) ≤ Real.exp (b * v) := by
    have h1 := Real.add_one_le_exp (b * v - L)
    have h2 : Real.exp (b * v - L) * (1 + t) = Real.exp (b * v) := by
      rw [Real.exp_sub, hL, Real.exp_log (by linarith)]; field_simp
    nlinarith [Real.exp_pos (b * v - L)]
  have hat : a / 2 * t = y / b := by rw [ht]; field_simp
  have key : a / 2 * ((1 + t) * (1 + b * v - L)) = (a / 2 + y / b) * (1 + b * v - L) := by
    rw [← hat]; ring
  have h3 : a / 2 * ((1 + t) * (1 + b * v - L)) ≤ a / 2 * Real.exp (b * v) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  rw [key] at h3
  have hyb : y / b * (b * v) = y * v := by field_simp
  have h4 : a / 2 * (L - 1 - b * v) ≤ a / 2 * t := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  nlinarith

/-- The decay profile `exp(-a e^{b|x|})` is dominated by a Gaussian. -/
theorem exp_neg_doubleExp_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    Real.exp (-a * Real.exp (b * |x|)) ≤ Real.exp (-(a * b ^ 2 / 2) * x ^ 2) := by
  refine Real.exp_le_exp.mpr ?_
  have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ b * |x| by positivity)
  have hx : (b * |x|) ^ 2 = b ^ 2 * x ^ 2 := by rw [mul_pow, sq_abs]
  have h' : b ^ 2 * x ^ 2 / 2 ≤ Real.exp (b * |x|) := by
    rw [← hx]; nlinarith [mul_nonneg hb.le (abs_nonneg x)]
  nlinarith [mul_le_mul_of_nonneg_left h' ha.le]

theorem integrable_exp_neg_doubleExp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-a * Real.exp (b * |x|))) := by
  refine (integrable_exp_neg_mul_sq (by positivity : 0 < a * b ^ 2 / 2)).mono'
    (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact exp_neg_doubleExp_le ha hb x

/-- The double-exponential profile integral `I(a, b) = ∫ exp(-(a/2) e^{b|x|}) dx`. -/
def doubleExpMass (a b : ℝ) : ℝ := ∫ x : ℝ, Real.exp (-(a / 2) * Real.exp (b * |x|))

theorem exp_mul_abs_le_doubleExp {a b y : ℝ} (ha : 0 < a) (hb : 0 < b) (hy : 0 ≤ y) (x : ℝ) :
    Real.exp (y * |x|) * Real.exp (-a * Real.exp (b * |x|)) ≤
      Real.exp (y / b * Real.log (1 + 2 * y / (a * b))) *
        Real.exp (-(a / 2) * Real.exp (b * |x|)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := legendre_doubleExp_le ha hb hy (abs_nonneg x)
  linarith

variable {u : ℝ → ℂ} {a b C : ℝ}

theorem measurableMomentSource_of_doubleExp (hu : AEStronglyMeasurable u) (ha : 0 < a)
    (hb : 0 < b) (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|))) :
    MeasurableMomentSource u := by
  refine ⟨hu, fun c => ?_⟩
  have hint := ((integrable_exp_neg_doubleExp (a := a / 2) (by linarith) hb).const_mul
    (C * Real.exp (|c| / b * Real.log (1 + 2 * |c| / (a * b)))))
  refine hint.mono' ((by fun_prop : Continuous fun x : ℝ => Real.exp (c * |x|)).aestronglyMeasurable.mul
    hu.norm) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, norm_norm]
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have h1 : Real.exp (c * |x|) ≤ Real.exp (|c| * |x|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg x))
  have h2 := exp_mul_abs_le_doubleExp ha hb (abs_nonneg c) x
  calc Real.exp (c * |x|) * ‖u x‖ ≤ Real.exp (|c| * |x|) * (C * Real.exp (-a * Real.exp (b * |x|))) :=
        mul_le_mul h1 (hC x) (norm_nonneg _) (Real.exp_pos _).le
    _ = C * (Real.exp (|c| * |x|) * Real.exp (-a * Real.exp (b * |x|))) := by ring
    _ ≤ C * (Real.exp (|c| / b * Real.log (1 + 2 * |c| / (a * b))) *
          Real.exp (-(a / 2) * Real.exp (b * |x|))) := mul_le_mul_of_nonneg_left h2 hC0
    _ = _ := by ring

/-- **Fourier growth of double-exponential sources.**
`|H(z)| ≤ C I(a,b) exp[(|Im z|/b) log(1 + 2|Im z|/(ab))]`. -/
theorem norm_sourceTransform_le_doubleExp (ha : 0 < a) (hb : 0 < b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|))) (z : ℂ) :
    ‖sourceTransform u z‖ ≤ C * doubleExpMass a b *
      Real.exp (|z.im| / b * Real.log (1 + 2 * |z.im| / (a * b))) := by
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  set M := Real.exp (|z.im| / b * Real.log (1 + 2 * |z.im| / (a * b)))
  have hint := (integrable_exp_neg_doubleExp (a := a / 2) (by linarith) hb).const_mul (C * M)
  rw [sourceTransform, doubleExpMass]
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun x => ?_)).trans
    (le_of_eq (by rw [integral_const_mul]; ring))
  rw [norm_mul, Complex.norm_exp]
  have hre : (-I * z * (x : ℂ)).re = z.im * x := by simp [Complex.mul_re]
  rw [hre]
  have h1 : Real.exp (z.im * x) ≤ Real.exp (|z.im| * |x|) :=
    Real.exp_le_exp.mpr (by rw [← abs_mul]; exact le_abs_self _)
  have h2 := exp_mul_abs_le_doubleExp ha hb (abs_nonneg z.im) x
  calc Real.exp (z.im * x) * ‖u x‖ ≤ Real.exp (|z.im| * |x|) * (C * Real.exp (-a * Real.exp (b * |x|))) :=
        mul_le_mul h1 (hC x) (norm_nonneg _) (Real.exp_pos _).le
    _ = C * (Real.exp (|z.im| * |x|) * Real.exp (-a * Real.exp (b * |x|))) := by ring
    _ ≤ C * (M * Real.exp (-(a / 2) * Real.exp (b * |x|))) := mul_le_mul_of_nonneg_left h2 hC0
    _ = C * M * Real.exp (-(a / 2) * Real.exp (b * |x|)) := by ring

/-- **Angular capacity.** For a double-exponential source, the circle average of `log|H|` on
`|z - c| = R` is at most `log⁺(C I) + ((|Im c| + (2/π) R)/b) log(1 + 2(|Im c| + R)/(ab))`. -/
theorem circleAverage_log_norm_le_doubleExp (hu : AEStronglyMeasurable u) (ha : 0 < a)
    (hb : 0 < b) (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|))) (c : ℂ) {R : ℝ}
    (hR : 0 ≤ R) :
    Real.circleAverage (fun z => Real.log ‖sourceTransform u z‖) c R ≤
      Real.posLog (C * doubleExpMass a b) + (|c.im| + 2 / Real.pi * R) / b *
        Real.log (1 + 2 * (|c.im| + R) / (a * b)) := by
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hI0 : 0 ≤ doubleExpMass a b := integral_nonneg fun x => (Real.exp_pos _).le
  have hHd := (measurableMomentSource_of_doubleExp hu ha hb hC).differentiable_sourceTransform
  set L := Real.log (1 + 2 * (|c.im| + R) / (a * b)) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by have : 0 ≤ 2 * (|c.im| + R) / (a * b) := by positivity
                                          linarith)
  set Φ : ℂ → ℝ := fun z => Real.posLog (C * doubleExpMass a b) + L / b * |z.im|
  have hpt : ∀ z ∈ sphere c |R|, Real.log ‖sourceTransform u z‖ ≤ Φ z := by
    intro z hz
    rw [mem_sphere, abs_of_nonneg hR, dist_eq_norm] at hz
    have hzim : |z.im| ≤ |c.im| + R := by
      have h1 : |z.im - c.im| ≤ ‖z - c‖ := by
        simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - c)
      have h2 := abs_sub_abs_le_abs_sub z.im c.im
      linarith
    have hm0 : 0 ≤ |z.im| / b * Real.log (1 + 2 * |z.im| / (a * b)) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by
        have : 0 ≤ 2 * |z.im| / (a * b) := by positivity
        linarith))
    have hbound := norm_sourceTransform_le_doubleExp ha hb hC z
    have hlogmono : Real.log (1 + 2 * |z.im| / (a * b)) ≤ L := by
      refine Real.log_le_log (by positivity) ?_
      have : 2 * |z.im| / (a * b) ≤ 2 * (|c.im| + R) / (a * b) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      linarith
    calc Real.log ‖sourceTransform u z‖ ≤ Real.posLog ‖sourceTransform u z‖ := le_max_right _ _
      _ ≤ Real.posLog (C * doubleExpMass a b *
            Real.exp (|z.im| / b * Real.log (1 + 2 * |z.im| / (a * b)))) :=
          Real.posLog_le_posLog (norm_nonneg _) hbound
      _ ≤ Real.posLog (C * doubleExpMass a b) +
            Real.posLog (Real.exp (|z.im| / b * Real.log (1 + 2 * |z.im| / (a * b)))) :=
          Real.posLog_mul
      _ = Real.posLog (C * doubleExpMass a b) + |z.im| / b * Real.log (1 + 2 * |z.im| / (a * b)) := by
          rw [posLog_exp_of_nonneg hm0]
      _ ≤ Φ z := by
          simp only [Φ]
          have : |z.im| / b * Real.log (1 + 2 * |z.im| / (a * b)) ≤ |z.im| / b * L :=
            mul_le_mul_of_nonneg_left hlogmono (by positivity)
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm L] at *
          linarith
  have hcont : Continuous Φ := by fun_prop
  have hmono := Real.circleAverage_mono
    (MeromorphicOn.circleIntegrable_log_norm (fun z _ => (hHd.analyticAt z).meromorphicAt))
    (hcont.continuousOn.circleIntegrable') hpt
  refine hmono.trans ?_
  have hsplit : Real.circleAverage Φ c R = Real.posLog (C * doubleExpMass a b) +
      L / b * Real.circleAverage (fun z => |z.im|) c R := by
    rw [show Φ = (fun _ => Real.posLog (C * doubleExpMass a b)) + fun z => (L / b) • |z.im| by
      funext z; simp [Φ, smul_eq_mul],
      Real.circleAverage_add (continuous_const.continuousOn.circleIntegrable')
        ((by fun_prop : Continuous fun z : ℂ => (L / b) • |z.im|).continuousOn.circleIntegrable'),
      Real.circleAverage_const, Real.circleAverage_fun_smul, smul_eq_mul]
  rw [hsplit]
  have := HTGeometry.circleAverage_abs_im_le c hR
  have hLb : 0 ≤ L / b := by positivity
  have := mul_le_mul_of_nonneg_left this hLb
  calc Real.posLog (C * doubleExpMass a b) + L / b * Real.circleAverage (fun z => |z.im|) c R ≤
        Real.posLog (C * doubleExpMass a b) + L / b * (|c.im| + 2 / Real.pi * R) := by linarith
    _ = _ := by ring

/-! ## The complete Xi divisor fills every large disc -/

/-- **Disc count.** The symmetric Xi divisor mass of height `T` lies inside `closedBall c r` in
the `XiC` coordinate once `T + 3/2 + |c| ≤ r`. -/
theorem xiSymmetricMass_le_finsum_divisor_XiC (c : ℂ) {r T : ℝ} (hT : 0 ≤ T)
    (hTr : T + 3 / 2 + ‖c‖ ≤ r) :
    xiSymmetricMass T ≤ ∑ᶠ z, MeromorphicOn.divisor XiC (closedBall c r) z := by
  set rect := Rectangle (((1 - 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) ((2 : ℂ) + (T : ℂ) * I)
  let e : ℂ ≃ ℂ :=
    { toFun := fun s => (s - 1 / 2) * (-I)
      invFun := fun z => 1 / 2 + z * I
      left_inv := fun s => by
        simp only
        rw [mul_assoc, show -I * I = (1 : ℂ) by rw [neg_mul, I_mul_I]; ring]; ring
      right_inv := fun z => by
        simp only
        rw [show (1 / 2 + z * I - 1 / 2) * -I = z * (-(I * I)) by ring, I_mul_I]; ring }
  have hxiA : AnalyticOnNhd ℂ xi univ := fun z _ => xi_differentiable.analyticAt z
  have hXA : AnalyticOnNhd ℂ XiC univ := fun z _ => XiC_differentiable.analyticAt z
  have hin : ∀ s ∈ rect, e s ∈ closedBall c r := by
    intro s hs
    have hs' : s ∈ Set.uIcc (((1 - 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).re ((2 : ℂ) + (T : ℂ) * I).re ×ℂ
        Set.uIcc (((1 - 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).im ((2 : ℂ) + (T : ℂ) * I).im := hs
    rw [Complex.mem_reProdIm] at hs'
    have hre := hs'.1
    have him := hs'.2
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, Complex.re_ofNat, Complex.add_im,
      Complex.mul_im, zero_add, Complex.im_ofNat, add_zero] at hre him
    rw [uIcc_of_le (by norm_num)] at hre
    rw [uIcc_of_le (by linarith)] at him
    rw [mem_closedBall, dist_eq_norm]
    have hes : ‖e s‖ ≤ 3 / 2 + T := by
      show ‖(s - 1 / 2) * (-I)‖ ≤ 3 / 2 + T
      rw [norm_mul, norm_neg, Complex.norm_I, mul_one]
      calc ‖s - 1 / 2‖ ≤ |(s - 1 / 2).re| + |(s - 1 / 2).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 3 / 2 + T := by
          simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.one_re,
            Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero]
          have h1 : |s.re - 1 / 2| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hre.1], by linarith [hre.2]⟩
          have h2 : |s.im| ≤ T := abs_le.mpr ⟨by linarith [him.1], him.2⟩
          linarith
    calc ‖e s - c‖ ≤ ‖e s‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ r := by linarith
  have hfinX : (MeromorphicOn.divisor XiC (closedBall c r)).support.Finite :=
    (MeromorphicOn.divisor XiC (closedBall c r)).finiteSupport (isCompact_closedBall c r)
  have hfinx : (MeromorphicOn.divisor xi rect).support.Finite :=
    (MeromorphicOn.divisor xi rect).finiteSupport (isCompact_uIcc.reProdIm isCompact_uIcc)
  rw [xiSymmetricMass, xiRegionOrderSum]
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_le_finsum' hfinx (hfinX.preimage (e.injective.injOn)) fun s => ?_
  by_cases hs : s ∈ rect
  · have hes := hin s hs
    rw [MeromorphicOn.divisor_apply (hxiA.mono (subset_univ _)).meromorphicOn hs,
      MeromorphicOn.divisor_apply (hXA.mono (subset_univ _)).meromorphicOn hes,
      (hxiA s (mem_univ s)).meromorphicOrderAt_eq, (hXA _ (mem_univ _)).meromorphicOrderAt_eq]
    have hes' : e s = (s - 1 / 2) * -I := rfl
    rw [hes', analyticOrderAt_XiC_centeredCoordinate]
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hs]
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hXA.mono (subset_univ _)) _

/-! ## Divisor containment and counting -/

theorem enat_map_cast_mono {m n : ℕ∞} (h : m ≤ n) :
    m.map (Nat.cast : ℕ → ℤ) ≤ n.map (Nat.cast : ℕ → ℤ) := by
  induction n using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    induction m using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe m =>
      rw [ENat.map_coe, ENat.map_coe]
      exact_mod_cast (show m ≤ n by exact_mod_cast h)

/-- Divisor containment compares the disc counts. -/
theorem finsum_divisor_le_of_order_le {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hg0 : ∃ z, g z ≠ 0)
    (hord : ∀ z, analyticOrderAt f z ≤ analyticOrderAt g z) (c : ℂ) (r : ℝ) :
    ∑ᶠ z, MeromorphicOn.divisor f (closedBall c r) z ≤
      ∑ᶠ z, MeromorphicOn.divisor g (closedBall c r) z := by
  have hfA : AnalyticOnNhd ℂ f (closedBall c r) := fun z _ => hf.analyticAt z
  have hgA : AnalyticOnNhd ℂ g (closedBall c r) := fun z _ => hg.analyticAt z
  refine finsum_le_finsum' ((MeromorphicOn.divisor f _).finiteSupport (isCompact_closedBall c r))
    ((MeromorphicOn.divisor g _).finiteSupport (isCompact_closedBall c r)) fun z => ?_
  by_cases hz : z ∈ closedBall c r
  · rw [MeromorphicOn.divisor_apply hfA.meromorphicOn hz, MeromorphicOn.divisor_apply hgA.meromorphicOn hz,
      (hf.analyticAt z).meromorphicOrderAt_eq, (hg.analyticAt z).meromorphicOrderAt_eq]
    refine WithTop.untop₀_le_untop₀ ?_ (enat_map_cast_mono (hord z))
    have := meromorphicOrderAt_ne_top_of_differentiable hg hg0 z
    rwa [(hg.analyticAt z).meromorphicOrderAt_eq] at this
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

theorem cast_finsum_divisor (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    ((∑ᶠ z, MeromorphicOn.divisor f (closedBall c r) z : ℤ) : ℝ) =
      ∑ᶠ z, (MeromorphicOn.divisor f (closedBall c r) z : ℝ) :=
  (Int.castAddHom ℝ).map_finsum ((MeromorphicOn.divisor f _).finiteSupport (isCompact_closedBall c r))

/-- A superlinear-logarithmic comparison: for `ε > 0` and any constants there is an arbitrarily
large `R` with `ε R log R > B₁ R + B₂ log R + B₃`. -/
theorem exists_large_mul_log {ε : ℝ} (hε : 0 < ε) (B₁ B₂ B₃ R₀ : ℝ) :
    ∃ R, R₀ ≤ R ∧ 1 ≤ R ∧ B₁ * R + B₂ * Real.log R + B₃ < ε * (R * Real.log R) := by
  set t := max (max (Real.log (max R₀ 1)) 1) (max ((|B₁| + 1) / ε) (2 * (|B₂| + |B₃| + 1)))
  have ht1 : 1 ≤ t := le_max_of_le_left (le_max_right _ _)
  have htR : Real.log (max R₀ 1) ≤ t := le_max_of_le_left (le_max_left _ _)
  have htB1 : (|B₁| + 1) / ε ≤ t := le_max_of_le_right (le_max_left _ _)
  have htB2 : 2 * (|B₂| + |B₃| + 1) ≤ t := le_max_of_le_right (le_max_right _ _)
  refine ⟨Real.exp t, ?_, Real.one_le_exp (by linarith), ?_⟩
  · calc R₀ ≤ max R₀ 1 := le_max_left _ _
      _ = Real.exp (Real.log (max R₀ 1)) := (Real.exp_log (lt_max_of_lt_right one_pos)).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr htR
  · rw [Real.log_exp]
    have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ t by linarith)
    have hεt : |B₁| + 1 ≤ ε * t := by rwa [div_le_iff₀ hε, mul_comm] at htB1
    have hsq : (|B₂| + |B₃| + 1) * t ≤ t ^ 2 / 2 := by nlinarith
    have h2 : |B₂| * t + |B₃| < Real.exp t := by nlinarith [abs_nonneg B₂, abs_nonneg B₃]
    have h3 : B₁ * Real.exp t ≤ |B₁| * Real.exp t :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    have h4 : B₂ * t ≤ |B₂| * t := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have h5 := le_abs_self B₃
    have h6 : (|B₁| + 1) * Real.exp t ≤ ε * t * Real.exp t :=
      mul_le_mul_of_nonneg_right hεt (Real.exp_pos _).le
    nlinarith

/-! ## The sharp capacity theorem -/

/-- **The capacity contradiction.** Let `u` be a double-exponential source with `H(c) ≠ 0`. If
for all large `T` the disc `closedBall c (T + K)` carries at least `κ T log T` zeros of `H` with
`κ > 2/(πb)`, Jensen's formula contradicts the angular capacity bound. -/
theorem false_of_capacity (hu : AEStronglyMeasurable u) (ha : 0 < a) (hb0 : 0 < b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|))) {c : ℂ}
    (hc : sourceTransform u c ≠ 0) {κ K T₀ : ℝ} (hK0 : 0 ≤ K) (hκ : 2 / (Real.pi * b) < κ)
    (hT₀ : 1 ≤ T₀)
    (hcountT : ∀ T, T₀ ≤ T → κ * (T * Real.log T) ≤
      ∑ᶠ z, (MeromorphicOn.divisor (sourceTransform u) (closedBall c (T + K)) z : ℝ)) :
    False := by
  have hms := measurableMomentSource_of_doubleExp hu ha hb0 hC
  have hHd := hms.differentiable_sourceTransform
  have hπ := Real.pi_pos
  set ε := κ - 2 / (Real.pi * b) with hεdef
  have hε : 0 < ε := by linarith
  have hκ0 : 0 < κ := by
    have : 0 < 2 / (Real.pi * b) := by positivity
    linarith
  set r₁ := T₀ + 2 * K + 2 with hr₁
  have hr₁0 : 0 < r₁ := by linarith
  set φ : ℝ → ℝ := fun r => κ * (r * Real.log r - (Real.log 2 + K) * r)
  have hcount : ∀ r, r₁ ≤ r → φ r ≤
      ∑ᶠ z, (MeromorphicOn.divisor (sourceTransform u) (closedBall c r) z : ℝ) := by
    intro r hr'
    obtain ⟨T, hTdef⟩ : ∃ T, T = r - K := ⟨_, rfl⟩
    have hT : T₀ ≤ T := by rw [hTdef]; linarith
    have hcT := hcountT T hT
    rw [show T + K = r by rw [hTdef]; ring] at hcT
    have hr2 : 2 * K ≤ r := by linarith
    have hrpos : 0 < r := by linarith
    have hTpos : 0 < T := by rw [hTdef]; linarith
    have hlogT : Real.log r - Real.log 2 ≤ Real.log T := by
      rw [← Real.log_div hrpos.ne' two_ne_zero]
      exact Real.log_le_log (by positivity) (by rw [hTdef]; linarith)
    have hlogr : Real.log r ≤ r := (Real.log_le_sub_one_of_pos hrpos).trans (by linarith)
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
    have hTT : r * Real.log r - (Real.log 2 + K) * r ≤ T * Real.log T := by
      have h1 : T * (Real.log r - Real.log 2) ≤ T * Real.log T :=
        mul_le_mul_of_nonneg_left hlogT hTpos.le
      have h2 : T * (Real.log r - Real.log 2) = r * Real.log r - r * Real.log 2 - K * Real.log r +
          K * Real.log 2 := by rw [hTdef]; ring
      nlinarith [mul_le_mul_of_nonneg_left hlogr hK0]
    calc φ r = κ * (r * Real.log r - (Real.log 2 + K) * r) := rfl
      _ ≤ κ * (T * Real.log T) := mul_le_mul_of_nonneg_left hTT hκ0.le
      _ ≤ _ := hcT
  set A₁ := Real.log (1 + 2 * (|c.im| + 1) / (a * b))
  obtain ⟨R, hRr, hR1, hRbig⟩ := exists_large_mul_log hε
    (κ * (1 + Real.log 2 + K) + 2 / (Real.pi * b) * A₁)
    (|c.im| / b)
    (Real.posLog (C * doubleExpMass a b) + |c.im| / b * A₁ - Real.log ‖sourceTransform u c‖ -
      κ * (r₁ - r₁ * Real.log r₁ + (Real.log 2 + K) * r₁))
    (r₁ + 1)
  have hR : r₁ ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hφi : IntervalIntegrable (fun r => φ r / r) volume r₁ R := by
    refine ContinuousOn.intervalIntegrable fun r hr => ?_
    rw [uIcc_of_le hR] at hr
    have hr0 : 0 < r := hr₁0.trans_le hr.1
    exact ((continuousAt_const.mul ((continuousAt_id.mul (Real.continuousAt_log hr0.ne')).sub
      (continuousAt_const.mul continuousAt_id))).div continuousAt_id hr0.ne').continuousWithinAt
  have hJ := HTGeometry.log_norm_add_integral_le_circleAverage
    (fun z _ => hHd.analyticAt z) hc hr₁0 hR hφi (fun r hr => hcount r hr.1)
  have hIeq : ∫ r in r₁..R, φ r / r =
      κ * ((R * Real.log R - r₁ * Real.log r₁ - R + r₁) - (Real.log 2 + K) * (R - r₁)) := by
    have hcongr : ∫ r in r₁..R, φ r / r = ∫ r in r₁..R, κ * (Real.log r - (Real.log 2 + K)) :=
      intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le hR] at hr
        have hr0 : 0 < r := hr₁0.trans_le hr.1
        simp only [φ]; field_simp
    rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      (intervalIntegral.intervalIntegrable_log' ) intervalIntegrable_const, integral_log,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hIeq] at hJ
  have hU := circleAverage_log_norm_le_doubleExp hu ha hb0 hC c hRpos.le
  have hlogU : Real.log (1 + 2 * (|c.im| + R) / (a * b)) ≤ Real.log R + A₁ := by
    rw [← Real.log_mul hRpos.ne' (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    have hab : 0 < a * b := by positivity
    have key : 2 * (|c.im| + R) ≤ R * (2 * (|c.im| + 1)) := by nlinarith [abs_nonneg c.im]
    calc 1 + 2 * (|c.im| + R) / (a * b) ≤ R + R * (2 * (|c.im| + 1)) / (a * b) :=
          add_le_add hR1 (div_le_div_of_nonneg_right key hab.le)
      _ = R * (1 + 2 * (|c.im| + 1) / (a * b)) := by ring
  have hU' : (|c.im| + 2 / Real.pi * R) / b * Real.log (1 + 2 * (|c.im| + R) / (a * b)) ≤
      (|c.im| + 2 / Real.pi * R) / b * (Real.log R + A₁) :=
    mul_le_mul_of_nonneg_left hlogU (by positivity)
  have hexpand : (|c.im| + 2 / Real.pi * R) / b * (Real.log R + A₁) =
      2 / (Real.pi * b) * (R * Real.log R) + 2 / (Real.pi * b) * A₁ * R +
        |c.im| / b * Real.log R + |c.im| / b * A₁ := by
    field_simp; ring
  have hsplitκ : κ * (R * Real.log R) = 2 / (Real.pi * b) * (R * Real.log R) +
      ε * (R * Real.log R) := by rw [hεdef]; ring
  have hJ' : Real.log ‖sourceTransform u c‖ + (κ * (R * Real.log R) - κ * (r₁ * Real.log r₁) -
      κ * R + κ * r₁ - κ * (Real.log 2 + K) * R + κ * (Real.log 2 + K) * r₁) ≤
      Real.circleAverage (fun z => Real.log ‖sourceTransform u z‖) c R := by
    convert hJ using 2; ring
  linarith

/-- **Sharp theta-tail capacity (`b > 2`).** If a measurable `u` obeys
`|u(x)| ≤ C exp(-a e^{b|x|})` with `a > 0`, `b > 2`, and its entire Fourier transform
`H(z) = ∫ e^{-izx} u(x) dx` vanishes at every zero of `F = XiC` to at least that zero's
multiplicity, then `u = 0` almost everywhere. -/
theorem ae_eq_zero_of_doubleExp_divisor (hu : AEStronglyMeasurable u) (ha : 0 < a) (hb : 2 < b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hdiv : ∀ z, analyticOrderAt XiC z ≤ analyticOrderAt (sourceTransform u) z) :
    u =ᵐ[volume] 0 := by
  have hb0 : 0 < b := by linarith
  have hms := measurableMomentSource_of_doubleExp hu ha hb0 hC
  have hHd := hms.differentiable_sourceTransform
  have hint_u : Integrable u := (hms.moment 0).mono' hu (Eventually.of_forall fun x => by simp)
  by_cases hH : ∀ z, sourceTransform u z = 0
  · exact ae_eq_zero_of_sourceTransform_eq_zero hint_u hH
  exfalso
  push Not at hH
  obtain ⟨c, hc⟩ := hH
  have hπ := Real.pi_pos
  set ε := (1 / Real.pi - 2 / (Real.pi * b)) / 2 with hεdef
  have hgap : 2 / (Real.pi * b) < 1 / Real.pi := by
    rw [div_lt_div_iff₀ (by positivity) hπ]; nlinarith
  have hε : 0 < ε := by linarith
  obtain ⟨T₀, hT₀4, hmass⟩ := exists_xiSymmetricMass_close ε hε
  refine false_of_capacity hu ha hb0 hC hc (κ := 1 / Real.pi - ε) (K := 3 / 2 + ‖c‖)
    (T₀ := T₀) (by positivity) (by linarith) (by linarith) fun T hT => ?_
  have hlow : (1 / Real.pi - ε) * (T * Real.log T) ≤ (xiSymmetricMass T : ℝ) := by
    have := (abs_le.mp (hmass T hT)).1; linarith
  have hdisc := xiSymmetricMass_le_finsum_divisor_XiC c (r := T + (3 / 2 + ‖c‖)) (T := T)
    (by linarith) (by linarith)
  have hmono := finsum_divisor_le_of_order_le XiC_differentiable hHd ⟨c, hc⟩ hdiv c
    (T + (3 / 2 + ‖c‖))
  rw [← cast_finsum_divisor]
  exact hlow.trans (by exact_mod_cast hdisc.trans hmono)

/-- For continuous `u` the capacity theorem is pointwise: `u = 0`. -/
theorem eq_zero_of_doubleExp_divisor_of_continuous (hu : Continuous u) (ha : 0 < a) (hb : 2 < b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hdiv : ∀ z, analyticOrderAt XiC z ≤ analyticOrderAt (sourceTransform u) z) : u = 0 :=
  (hu.ae_eq_iff_eq volume continuous_const).mp
    (ae_eq_zero_of_doubleExp_divisor hu.aestronglyMeasurable ha hb hC hdiv)

/-- **Equivalent form.** If `g` carries the complete Xi divisor as a sub-divisor of its
transform, then `g - k` cannot obey a double-exponential tail bound with `b > 2` unless
`g = k` almost everywhere. -/
theorem ae_eq_thetaSource_of_subdivisor {g : ℝ → ℂ} (hg : AEStronglyMeasurable g) (ha : 0 < a)
    (hb : 2 < b) (hC : ∀ x, ‖g x - thetaSourceC x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hdiv : ∀ z, analyticOrderAt XiC z ≤ analyticOrderAt (sourceTransform g) z) :
    g =ᵐ[volume] thetaSourceC := by
  have hb0 : 0 < b := by linarith
  have huM : AEStronglyMeasurable (fun x => g x - thetaSourceC x) :=
    hg.sub expMomentSource_thetaSourceC.continuous.aestronglyMeasurable
  have hms := measurableMomentSource_of_doubleExp huM ha hb0 hC
  have heq : sourceTransform (fun x => g x - thetaSourceC x) =
      sourceTransform g - XiC := by
    funext z
    have h1 := hms.integrable_cexp z
    have h2 := expMomentSource_thetaSourceC.integrable_cexp z
    have hgz : Integrable (fun x : ℝ => Complex.exp (-I * z * x) * g x) := by
      have := h1.add h2
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply]; ring
    rw [Pi.sub_apply, ← sourceTransform_thetaSourceC, sourceTransform, sourceTransform,
      sourceTransform, ← integral_sub hgz h2]
    congr 1; funext x; ring
  have hdiv' : ∀ z, analyticOrderAt XiC z ≤
      analyticOrderAt (sourceTransform fun x => g x - thetaSourceC x) z := by
    intro z
    rw [heq]
    exact (le_min (hdiv z) le_rfl).trans le_analyticOrderAt_sub
  filter_upwards [ae_eq_zero_of_doubleExp_divisor huM ha hb hC hdiv'] with x hx
  simpa [sub_eq_zero] using hx

end

end RHTower
