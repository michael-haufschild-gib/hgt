import GaloisForLFunctions.ArithmeticCompensationTheory.TheHorizonEnergyIsNotUniformlyCoercive

/-!
# The resolvent energy identity, the exact second correction, and fixed-aperture coercivity

`TheTranslationLawHasAnInverseSquareDeficit` establishes the single-average formula
`J(F) = ∫_{u>0} A_F(u) ½e^{−u/2} du` and the first correction `4‖f′‖²/r²` on the slowly varying
family `F_r(x) = r^{−1/2} f(x/r)`. This file resolves the two remaining quantitative problems at the
horizon: the exact second correction of the horizon and comb energies on the slowly varying family,
and the coercive constant of `J` on the ledger's odd test class at a fixed aperture.

The structural engine is an exact, non-asymptotic **resolvent energy identity** valid for every
compactly supported `C¹` test `F`. Because `A_F` is even, its derivative `C_F(u) = ∫ F(x) F′(x + u)`
is odd (`crossCorr_neg`), vanishes at the origin (`crossCorr_zero`), and satisfies
`C_F′(u) = −A_{F′}(u)` (`hasDerivAt_crossCorr`) without requiring a second derivative on `F`. The
combined horizon potential `W(u) = −(A_F(u) + 2 C_F(u)) e^{−u/2}` therefore has derivative
`A_F(u) ½e^{−u/2} + 4 A_{F′}(u) ½e^{−u/2}`, and the fundamental theorem of calculus on `(0, ∞)`
gives

`J(F) + 4 J(F′) = A_F(0)`  (`horizonEnergy_add_four_mul_horizonEnergy_deriv`),

the exact lag-side counterpart of `‖F‖² = ‖(1 + 2∂)ΨF‖² = ‖ΨF‖² + 4‖(ΨF)′‖²`. Every quantitative
property of the horizon energy follows directly from this identity:

1. **Universal `H¹` lower bound and second-order resolvent expansion.** Since `0 ≤ J(F′) ≤ A_{F′}(0)`,
   every `F ∈ C¹_c(ℝ)` satisfies `A_F(0) − 4∫(F′)² ≤ J(F) ≤ A_F(0)`
   (`horizonEnergy_ge_autoCorr_zero_sub_four_mul_deriv_sq`), eliminating both the cubic remainder and
   the support-radius dependence of the Lipschitz bound. For `F ∈ C²_c(ℝ)`, iterating the identity
   on `F′` gives the exact second-order expansion
   `J(F) = A_F(0) − 4 A_{F′}(0) + 16 J(F″)` (`horizonEnergy_eq_second_order_resolvent`) and the
   two-sided Taylor sandwich (`horizonEnergy_second_order_sandwich`).

2. **The exact second correction on the slowly varying family.** Under `F_r(x) = r^{−1/2} f(x/r)`,
   differentiation rescales by `r^{−1}` (`deriv_rescaledTest`), so for `f ∈ C²_c(ℝ)` the second-order
   expansion becomes the finite-aperture identity
   `A_f(0) − J(F_r) − (4/r²)∫(f′)² = −(16/r⁴) J(rescaledTest f″ r)`
   (`horizonEnergy_rescaledTest_second_deficit_eq`). Because `J(rescaledTest g r) → A_g(0)` for
   every `g ∈ C⁰_c(ℝ)` (`tendsto_horizonEnergy_rescaledTest`) and `r⁴ exp(−c√r) → 0`, both the
   horizon energy and the normalized prime comb energy have the exact fourth-order (`1/r⁴`) second
   correction `−16∫(f″)²` (`tendsto_pow_four_mul_horizonEnergy_rescaledTest_second_deficit`,
   `tendsto_pow_four_mul_combEnergy_rescaledTest_second_deficit`). There is no `1/r³` term.

3. **Fixed-aperture coercivity on the ledger's odd test class.** For a test supported in `[−R, R]`,
   `A_G` vanishes past `2R`, so `J(G) ≤ (1 − e^{−R}) A_G(0)`
   (`horizonEnergy_le_one_sub_exp_neg_mul_autoCorr_zero`). Applying this bound to `F′` inside the
   resolvent identity yields the aperture-refined lower bound
   `J(F) ≥ ∫F² − 4(1 − e^{−R})∫(F′)²` (`horizonEnergy_ge_one_sub_exp_of_support`), and hence the
   coercive constant `1 − 4(1 − e^{−R})Λ² ≥ 1 − 4Λ²` on the odd regularity class
   `∫(F′)² ≤ Λ²∫F²` (`horizonEnergy_ge_of_oddApertureRegularityClass`), whose constant `1 − 4Λ²` is
   asymptotically attained on rescaled odd profiles (`tendsto_horizonEnergy_deficit_div_four_mul_deriv_sq`).
   Without a derivative bound, squeezing `oddBump` inside `[−R, R]` shows that the infimum of
   `J(F)/∫F²` over smooth odd tests supported in `[−R, R]` is `0` at every fixed aperture `R > 0`
   (`not_exists_odd_fixed_aperture_horizonEnergy_ge`,
   `exists_odd_fixed_aperture_combEnergy_le_mul`).
-/

open Filter Topology Finset MeasureTheory Set
open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## §1. The derivative calculus of the autocorrelation on `C¹_c(ℝ)` -/

/-- The cross-correlation of a test with its derivative, `C_F(t) = ∫ F(x) F′(x + t) dx`. -/
def crossCorr (F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, F x * deriv F (x + t)

theorem autoCorr_zero_eq_integral_sq (F : ℝ → ℝ) :
    autoCorr F 0 = ∫ x, F x ^ 2 := by
  unfold autoCorr
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show F x * F (x + 0) = F x ^ 2
  rw [add_zero, sq]

/-- For `F ∈ C¹_c(ℝ)`, the autocorrelation `A_F` is differentiable with derivative `crossCorr F`. -/
theorem hasDerivAt_autoCorr {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (t : ℝ) : HasDerivAt (autoCorr F) (crossCorr F t) t := by
  have hFcont : Continuous F := hF.continuous
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hFc.deriv.exists_bound_of_continuous hdcont
  have hbound : Integrable fun x => ‖F x‖ * M :=
    (hFcont.norm.mul continuous_const).integrable_of_hasCompactSupport hFc.norm.mul_right
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (u : ℝ) (x : ℝ) => F x * F (x + u))
    (F' := fun (u : ℝ) (x : ℝ) => F x * deriv F (x + u))
    (x₀ := t) (bound := fun x => ‖F x‖ * M) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun u =>
      (hFcont.mul (hFcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    ((hFcont.mul (hFcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right)
    ((hFcont.mul (hdcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    (Eventually.of_forall fun x u _ => by
      rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM (x + u)) (norm_nonneg _))
    hbound
    (Eventually.of_forall fun x u _ =>
      (HasDerivAt.comp_const_add x u ((hF.differentiable one_ne_zero (x + u)).hasDerivAt)).const_mul
        (F x))).2

theorem continuous_crossCorr {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    Continuous (crossCorr F) := by
  have hFcont : Continuous F := hF.continuous
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hFc.deriv.exists_bound_of_continuous hdcont
  have hbound : Integrable fun x => ‖F x‖ * M :=
    (hFcont.norm.mul continuous_const).integrable_of_hasCompactSupport hFc.norm.mul_right
  refine continuous_of_dominated (bound := fun x => ‖F x‖ * M)
    (fun u => (hFcont.mul (hdcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    (fun u => Eventually.of_forall fun x => ?_) hbound
    (Eventually.of_forall fun x =>
      continuous_const.mul (hdcont.comp (continuous_const.add continuous_id)))
  rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hM (x + u)) (norm_nonneg _)

/-- Because `A_F` is even, its derivative `crossCorr F` is odd. -/
theorem crossCorr_neg {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (t : ℝ) :
    crossCorr F (-t) = -crossCorr F t := by
  have h1 : HasDerivAt (fun s => autoCorr F (-s)) (crossCorr F (-t) * -1) t :=
    (hasDerivAt_autoCorr hF hFc (-t)).comp t (hasDerivAt_neg t)
  have h2 : HasDerivAt (fun s => autoCorr F (-s)) (crossCorr F t) t := by
    simp only [autoCorr_neg]
    exact hasDerivAt_autoCorr hF hFc t
  linarith [h1.unique h2]

theorem crossCorr_zero {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    crossCorr F 0 = 0 := by
  have h := crossCorr_neg hF hFc 0
  rw [neg_zero] at h
  linarith

/-- Translation invariance and oddness rewrite `crossCorr F t` as `−∫ F′(x) F(x + t) dx` without
requiring a second derivative on `F`. -/
theorem crossCorr_eq_neg_integral_deriv_mul_shift {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) (t : ℝ) :
    crossCorr F t = -∫ x, deriv F x * F (x + t) := by
  have hneg := crossCorr_neg hF hFc t
  have htr := integral_add_right_eq_self (μ := volume) (fun x => F x * deriv F (x + -t)) t
  have heq : (∫ x, F (x + t) * deriv F (x + t + -t)) = ∫ x, deriv F x * F (x + t) :=
    integral_congr_ae (Eventually.of_forall fun x => by dsimp only; rw [add_neg_cancel_right, mul_comm])
  rw [crossCorr, ← htr, heq] at hneg
  linarith

/-- **Second derivative of the autocorrelation on `C¹_c(ℝ)`.** For every `F ∈ C¹_c(ℝ)`,
`crossCorr F` is differentiable with derivative `−autoCorr (deriv F) t`. -/
theorem hasDerivAt_crossCorr {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (t : ℝ) : HasDerivAt (crossCorr F) (-autoCorr (deriv F) t) t := by
  have hFcont : Continuous F := hF.continuous
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hdcs : HasCompactSupport (deriv F) := hFc.deriv
  obtain ⟨M, hM⟩ := hdcs.exists_bound_of_continuous hdcont
  have hbound : Integrable fun x => ‖deriv F x‖ * M :=
    (hdcont.norm.mul continuous_const).integrable_of_hasCompactSupport hdcs.norm.mul_right
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (u : ℝ) (x : ℝ) => deriv F x * F (x + u))
    (F' := fun (u : ℝ) (x : ℝ) => deriv F x * deriv F (x + u))
    (x₀ := t) (bound := fun x => ‖deriv F x‖ * M) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun u =>
      (hdcont.mul (hFcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    ((hdcont.mul (hFcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hdcs.mul_right)
    ((hdcont.mul (hdcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    (Eventually.of_forall fun x u _ => by
      rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM (x + u)) (norm_nonneg _))
    hbound
    (Eventually.of_forall fun x u _ =>
      (HasDerivAt.comp_const_add x u ((hF.differentiable one_ne_zero (x + u)).hasDerivAt)).const_mul
        (deriv F x))).2
  have hfun : crossCorr F = fun u => -∫ x, deriv F x * F (x + u) :=
    funext fun u => crossCorr_eq_neg_integral_deriv_mul_shift hF hFc u
  rw [hfun]
  exact key.neg

/-! ## §2. The exact resolvent energy identity and universal Sobolev sandwich -/

/-- **The resolvent energy identity.** For every `F ∈ C¹_c(ℝ)`,
`J(F) + 4 J(F′) = A_F(0)`. -/
theorem horizonEnergy_add_four_mul_horizonEnergy_deriv {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) :
    horizonEnergy F + 4 * horizonEnergy (deriv F) = autoCorr F 0 := by
  have hFcont : Continuous F := hF.continuous
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hdcs : HasCompactSupport (deriv F) := hFc.deriv
  set A := autoCorr F
  set C := crossCorr F
  set A₁ := autoCorr (deriv F)
  set W : ℝ → ℝ := fun u => (A u + 2 * C u) * (-Real.exp (-u / 2))
  set W' : ℝ → ℝ := fun u => A u * horizonDensity u + 4 * (A₁ u * horizonDensity u)
  have hWd : ∀ u, HasDerivAt W (W' u) u := fun u => by
    have hAC : HasDerivAt (fun x => A x + 2 * C x) (C u + 2 * (-A₁ u)) u :=
      (hasDerivAt_autoCorr hF hFc u).add ((hasDerivAt_crossCorr hF hFc u).const_mul 2)
    refine (hAC.mul (hasDerivAt_neg_exp_half u)).congr_deriv ?_
    simp only [W', horizonDensity]
    ring
  have hWc : Continuous W := continuous_iff_continuousAt.mpr fun u => (hWd u).continuousAt
  have hIA : IntegrableOn (fun u => A u * horizonDensity u) (Ioi 0) :=
    integrableOn_mul_horizonDensity (continuous_autoCorr hFcont hFc)
      (abs_autoCorr_le_autoCorr_zero hFcont hFc) 0
  have hIA₁ : IntegrableOn (fun u => 4 * (A₁ u * horizonDensity u)) (Ioi 0) :=
    (integrableOn_mul_horizonDensity (continuous_autoCorr hdcont hdcs)
      (abs_autoCorr_le_autoCorr_zero hdcont hdcs) 0).const_mul 4
  -- `W(u) → 0` as `u → ∞` because `A` and `C` are bounded and `e^{−u/2} → 0`
  obtain ⟨M, hM⟩ := hdcs.exists_bound_of_continuous hdcont
  have hFi : Integrable fun x => ‖F x‖ * M :=
    (hFcont.norm.mul continuous_const).integrable_of_hasCompactSupport hFc.norm.mul_right
  set BC := ∫ x, ‖F x‖ * M
  have hCb : ∀ u, |C u| ≤ BC := fun u => by
    refine abs_integral_le_integral_abs.trans (integral_mono
      ((hFcont.mul (hdcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
        hFc.mul_right).abs hFi fun x => ?_)
    rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM (x + u)) (norm_nonneg _)
  set B := |A 0| + 2 * |BC|
  have hlim : Tendsto W atTop (𝓝 0) := by
    have hexp : Tendsto (fun u : ℝ => B * Real.exp (-u / 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun u : ℝ => u / 2) atTop atTop :=
        tendsto_id.atTop_div_const (by norm_num)
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B
      rw [mul_zero] at h2
      refine h2.congr fun u => ?_
      simp only [Function.comp_apply]
      ring_nf
    refine squeeze_zero_norm (fun u => ?_) hexp
    rw [Real.norm_eq_abs]
    simp only [W, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    have hAu : |A u| ≤ |A 0| := (abs_autoCorr_le_autoCorr_zero hFcont hFc u).trans (le_abs_self _)
    have hCu : |C u| ≤ |BC| := (hCb u).trans (le_abs_self _)
    have hsum : |A u + 2 * C u| ≤ B := by
      calc |A u + 2 * C u| ≤ |A u| + |2 * C u| := abs_add_le _ _
        _ = |A u| + 2 * |C u| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ ≤ |A 0| + 2 * |BC| := by linarith
    exact mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hWc.continuousWithinAt
    (fun u _ => hWd u) (hIA.add hIA₁) hlim
  rw [integral_add hIA hIA₁, integral_const_mul] at hFTC
  have hW0 : W 0 = -A 0 := by
    simp only [W, C, crossCorr_zero hF hFc, neg_zero, zero_div, Real.exp_zero]
    ring
  rw [hW0, sub_neg_eq_add, zero_add] at hFTC
  rw [horizonEnergy_eq_horizonIntegral_autoCorr hFcont hFc,
    horizonEnergy_eq_horizonIntegral_autoCorr hdcont hdcs]
  exact hFTC

/-- **First-order resolvent expansion of the horizon energy.** For every `F ∈ C¹_c(ℝ)`,
`J(F) = A_F(0) − 4 J(F′)`. -/
theorem horizonEnergy_eq_autoCorr_zero_sub_four_mul_horizonEnergy_deriv {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    horizonEnergy F = autoCorr F 0 - 4 * horizonEnergy (deriv F) := by
  linarith [horizonEnergy_add_four_mul_horizonEnergy_deriv hF hFc]

/-- **Second-order resolvent expansion of the horizon energy.** For every `F ∈ C²_c(ℝ)`,
`J(F) = A_F(0) − 4 A_{F′}(0) + 16 J(F″)`. -/
theorem horizonEnergy_eq_second_order_resolvent {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) :
    horizonEnergy F =
      autoCorr F 0 - 4 * autoCorr (deriv F) 0 + 16 * horizonEnergy (deriv (deriv F)) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hF' : ContDiff ℝ 1 (deriv F) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) F from hF)).2.2
  have h1 := horizonEnergy_eq_autoCorr_zero_sub_four_mul_horizonEnergy_deriv hF1 hFc
  have h2 := horizonEnergy_eq_autoCorr_zero_sub_four_mul_horizonEnergy_deriv hF' hFc.deriv
  linarith

/-- **Universal `H¹` sandwich for the horizon energy.** Every `F ∈ C¹_c(ℝ)` satisfies
`A_F(0) − 4∫(F′)² ≤ J(F) ≤ A_F(0)`, with no cubic remainder and no dependence on the support
radius. -/
theorem horizonEnergy_ge_autoCorr_zero_sub_four_mul_deriv_sq {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) :
    autoCorr F 0 - 4 * (∫ x, deriv F x ^ 2) ≤ horizonEnergy F ∧
      horizonEnergy F ≤ autoCorr F 0 := by
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hdcs : HasCompactSupport (deriv F) := hFc.deriv
  have h1 := horizonEnergy_eq_autoCorr_zero_sub_four_mul_horizonEnergy_deriv hF hFc
  have hle := horizonEnergy_le hdcont hdcs
  have hnn := horizonEnergy_nonneg hdcont hdcs
  rw [autoCorr_zero_eq_integral_sq] at hle
  exact ⟨by linarith, by linarith⟩

/-- **Universal second-order Taylor sandwich for the horizon energy.** Every `F ∈ C²_c(ℝ)`
satisfies
`A_F(0) − 4∫(F′)² ≤ J(F) ≤ A_F(0) − 4∫(F′)² + 16∫(F″)²`. -/
theorem horizonEnergy_second_order_sandwich {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) :
    autoCorr F 0 - 4 * (∫ x, deriv F x ^ 2) ≤ horizonEnergy F ∧
      horizonEnergy F ≤
        autoCorr F 0 - 4 * (∫ x, deriv F x ^ 2) + 16 * ∫ x, deriv (deriv F) x ^ 2 := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hF' : ContDiff ℝ 1 (deriv F) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) F from hF)).2.2
  have hd2cont : Continuous (deriv (deriv F)) := hF'.continuous_deriv le_rfl
  have hd2cs : HasCompactSupport (deriv (deriv F)) := hFc.deriv.deriv
  have h2 := horizonEnergy_eq_second_order_resolvent hF hFc
  have hnn := horizonEnergy_nonneg hd2cont hd2cs
  have hle := horizonEnergy_le hd2cont hd2cs
  rw [autoCorr_zero_eq_integral_sq (deriv F)] at h2
  rw [autoCorr_zero_eq_integral_sq (deriv (deriv F))] at hle
  exact ⟨by linarith, by linarith⟩

/-! ## §3. The exact second correction (`−16‖f″‖²/r⁴`) on the slowly varying family -/

theorem autoCorr_const_mul (c : ℝ) (F : ℝ → ℝ) (t : ℝ) :
    autoCorr (fun x => c * F x) t = c ^ 2 * autoCorr F t := by
  unfold autoCorr
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x => by ring)

theorem horizonIntegral_const_mul (c : ℝ) (g : ℝ → ℝ) :
    horizonIntegral (fun u => c * g u) = c * horizonIntegral g := by
  unfold horizonIntegral
  rw [← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun u _ => by ring

theorem horizonEnergy_const_mul (c : ℝ) (F : ℝ → ℝ) :
    horizonEnergy (fun x => c * F x) = c ^ 2 * horizonEnergy F := by
  unfold horizonEnergy
  simp only [autoCorr_const_mul, horizonIntegral_const_mul]

theorem contDiff_rescaledTest {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) (r : ℝ) :
    ContDiff ℝ n (rescaledTest f r) :=
  contDiff_const.mul (hf.comp (contDiff_id.div_const r))

/-- Rescaling a test to aperture `r` multiplies its derivative by `r^{−1}`:
`(rescaledTest f r)′ = r^{−1} · rescaledTest f′ r`. -/
theorem deriv_rescaledTest {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {r : ℝ} (_ : 0 < r) :
    deriv (rescaledTest f r) = fun x => r⁻¹ * rescaledTest (deriv f) r x := by
  funext x
  have hd : HasDerivAt (fun y => f (y / r)) (deriv f (x / r) * (1 / r)) x :=
    ((hf.differentiable one_ne_zero (x / r)).hasDerivAt).comp x ((hasDerivAt_id x).div_const r)
  have hmul : HasDerivAt (rescaledTest f r) ((Real.sqrt r)⁻¹ * (deriv f (x / r) * (1 / r))) x :=
    hd.const_mul (Real.sqrt r)⁻¹
  refine (hmul.congr_deriv ?_).deriv
  simp only [rescaledTest]
  ring

/-- Second derivative of the rescaled test:
`(rescaledTest f r)″ = (r²)^{−1} · rescaledTest f″ r`. -/
theorem deriv_deriv_rescaledTest {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (rescaledTest f r)) = fun x => (r ^ 2)⁻¹ * rescaledTest (deriv (deriv f)) r x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hf' : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  funext x
  have hd : DifferentiableAt ℝ (rescaledTest (deriv f) r) x :=
    (contDiff_rescaledTest hf' r).differentiable one_ne_zero x
  rw [deriv_rescaledTest hf1 hr, deriv_const_mul _ hd, deriv_rescaledTest hf' hr]
  ring

/-- **Exact first-order deficit identity on the slowly varying family.** For every `f ∈ C¹_c(ℝ)`
and `r > 0`, `A_f(0) − J(F_r) = (4/r²) J(rescaledTest f′ r)`. -/
theorem horizonEnergy_rescaledTest_deficit_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {r : ℝ} (hr : 0 < r) :
    autoCorr f 0 - horizonEnergy (rescaledTest f r) =
      4 / r ^ 2 * horizonEnergy (rescaledTest (deriv f) r) := by
  have hFr : ContDiff ℝ 1 (rescaledTest f r) := contDiff_rescaledTest hf r
  have hFrc : HasCompactSupport (rescaledTest f r) := hasCompactSupport_rescaledTest hr hfc
  have h1 := horizonEnergy_eq_autoCorr_zero_sub_four_mul_horizonEnergy_deriv hFr hFrc
  have hA0 : autoCorr (rescaledTest f r) 0 = autoCorr f 0 := by
    rw [autoCorr_rescaledTest hr, zero_div]
  rw [hA0, deriv_rescaledTest hf hr, horizonEnergy_const_mul] at h1
  have : 4 * ((r⁻¹) ^ 2 * horizonEnergy (rescaledTest (deriv f) r)) =
      4 / r ^ 2 * horizonEnergy (rescaledTest (deriv f) r) := by ring
  linarith

/-- **Exact second-order deficit identity on the slowly varying family.** For every `f ∈ C²_c(ℝ)`
and `r > 0`,
`A_f(0) − J(F_r) − (4/r²)∫(f′)² = −(16/r⁴) J(rescaledTest f″ r)`. -/
theorem horizonEnergy_rescaledTest_second_deficit_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {r : ℝ} (hr : 0 < r) :
    autoCorr f 0 - horizonEnergy (rescaledTest f r) - 4 / r ^ 2 * (∫ x, deriv f x ^ 2) =
      -(16 / r ^ 4 * horizonEnergy (rescaledTest (deriv (deriv f)) r)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hf' : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have h1 := horizonEnergy_rescaledTest_deficit_eq hf1 hfc hr
  have h2 := horizonEnergy_rescaledTest_deficit_eq hf' hfc.deriv hr
  rw [autoCorr_zero_eq_integral_sq] at h2
  have halg : 4 / r ^ 2 * horizonEnergy (rescaledTest (deriv f) r) =
      4 / r ^ 2 * (∫ x, deriv f x ^ 2) -
        16 / r ^ 4 * horizonEnergy (rescaledTest (deriv (deriv f)) r) := by
    calc 4 / r ^ 2 * horizonEnergy (rescaledTest (deriv f) r)
        = 4 / r ^ 2 * ((∫ x, deriv f x ^ 2) -
            4 / r ^ 2 * horizonEnergy (rescaledTest (deriv (deriv f)) r)) := by
          congr 1; linarith [h2]
      _ = 4 / r ^ 2 * (∫ x, deriv f x ^ 2) -
            16 / r ^ 4 * horizonEnergy (rescaledTest (deriv (deriv f)) r) := by ring
  linarith

/-- **Finite-aperture second-order Taylor sandwich on the slowly varying family.** For every
`f ∈ C²_c(ℝ)` and `r > 0`,
`(4/r²)∫(f′)² − (16/r⁴)∫(f″)² ≤ A_f(0) − J(F_r) ≤ (4/r²)∫(f′)²`. -/
theorem horizonEnergy_rescaledTest_second_order_sandwich {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {r : ℝ} (hr : 0 < r) :
    4 / r ^ 2 * (∫ x, deriv f x ^ 2) - 16 / r ^ 4 * (∫ x, deriv (deriv f) x ^ 2) ≤
        autoCorr f 0 - horizonEnergy (rescaledTest f r) ∧
      autoCorr f 0 - horizonEnergy (rescaledTest f r) ≤ 4 / r ^ 2 * ∫ x, deriv f x ^ 2 := by
  have hf' : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hd2cont : Continuous (deriv (deriv f)) := hf'.continuous_deriv le_rfl
  have hd2cs : HasCompactSupport (deriv (deriv f)) := hfc.deriv.deriv
  have hF2cont := continuous_rescaledTest hd2cont r
  have hF2cs := hasCompactSupport_rescaledTest hr hd2cs
  have hnn := horizonEnergy_nonneg hF2cont hF2cs
  have hle := horizonEnergy_le hF2cont hF2cs
  rw [autoCorr_rescaledTest hr, zero_div, autoCorr_zero_eq_integral_sq] at hle
  have hid := horizonEnergy_rescaledTest_second_deficit_eq hf hfc hr
  have hr4 : 0 ≤ 16 / r ^ 4 := by positivity
  have hlo := mul_nonneg hr4 hnn
  have hhi := mul_le_mul_of_nonneg_left hle hr4
  exact ⟨by linarith, by linarith⟩

/-- For every continuous compactly supported profile `g ∈ C⁰_c(ℝ)`,
`J(rescaledTest g r) → A_g(0)` as `r → ∞`. -/
theorem tendsto_horizonEnergy_rescaledTest {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Tendsto (fun r => horizonEnergy (rescaledTest g r)) atTop (𝓝 (autoCorr g 0)) := by
  have hAg := continuous_autoCorr hg hgc
  have hAb : ∀ t, |autoCorr g t| ≤ autoCorr g 0 := abs_autoCorr_le_autoCorr_zero hg hgc
  have hA0 : 0 ≤ autoCorr g 0 := (abs_nonneg _).trans (hAb 0)
  have hlim : Tendsto (fun r => ∫ u in Ioi (0 : ℝ), autoCorr g (u / r) * horizonDensity u) atTop
      (𝓝 (∫ u in Ioi (0 : ℝ), autoCorr g 0 * horizonDensity u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => autoCorr g 0 * horizonDensity u) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun r =>
        ((hAg.comp (continuous_id.div_const r)).mul continuous_horizonDensity).aestronglyMeasurable
    · refine Eventually.of_forall fun r => ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u _ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (horizonDensity_nonneg u)]
      exact mul_le_mul_of_nonneg_right (hAb (u / r)) (horizonDensity_nonneg u)
    · exact (integrableOn_horizonDensity 0).const_mul (autoCorr g 0)
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u _ => ?_
      have hto : Tendsto (fun r : ℝ => u / r) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      exact (hAg.continuousAt.tendsto.comp hto).mul_const (horizonDensity u)
  rw [integral_const_mul, integral_Ioi_horizonDensity, neg_zero, zero_div, Real.exp_zero,
    mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [horizonEnergy_eq_horizonIntegral_autoCorr (continuous_rescaledTest hg r)
    (hasCompactSupport_rescaledTest hr hgc), horizonIntegral]
  exact setIntegral_congr_fun measurableSet_Ioi fun u _ => by rw [autoCorr_rescaledTest hr]

/-- **The exact second correction of the horizon energy.** For every `f ∈ C²_c(ℝ)`,
`r⁴ (A_f(0) − J(F_r) − (4/r²)∫(f′)²) → −16∫(f″)²` as `r → ∞`. -/
theorem tendsto_pow_four_mul_horizonEnergy_rescaledTest_second_deficit {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (fun r => r ^ 4 * (autoCorr f 0 - horizonEnergy (rescaledTest f r) -
        4 / r ^ 2 * ∫ x, deriv f x ^ 2)) atTop
      (𝓝 (-16 * ∫ x, deriv (deriv f) x ^ 2)) := by
  have hf' : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hd2cont : Continuous (deriv (deriv f)) := hf'.continuous_deriv le_rfl
  have hd2cs : HasCompactSupport (deriv (deriv f)) := hfc.deriv.deriv
  have hlim := (tendsto_horizonEnergy_rescaledTest hd2cont hd2cs).const_mul (-16)
  rw [autoCorr_zero_eq_integral_sq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [horizonEnergy_rescaledTest_second_deficit_eq hf hfc hr]
  field_simp

/-- `r⁴ exp(−c√r) → 0` as `r → ∞`. -/
theorem tendsto_pow_four_mul_exp_neg_sqrt {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℝ => r ^ 4 * Real.exp (-c * Real.sqrt r)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => (c * x) ^ 8 * Real.exp (-(c * x))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 8).comp (tendsto_id.const_mul_atTop hc)
  have h2 : Tendsto (fun r : ℝ => (c * Real.sqrt r) ^ 8 * Real.exp (-(c * Real.sqrt r))) atTop
      (𝓝 0) := h1.comp Real.tendsto_sqrt_atTop
  have h3 := h2.const_mul (c ^ 8)⁻¹
  rw [mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with r hr0
  have hs : Real.sqrt r ^ 8 = r ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt hr0]
  have hc8 : c ^ 8 ≠ 0 := by positivity
  rw [mul_pow, hs, show -(c * Real.sqrt r) = -c * Real.sqrt r by ring]
  field_simp

/-- **The exact second correction of the prime comb energy on the slowly varying family.** For
every `f ∈ C²_c(ℝ)` supported in `[−1, 1]`,
`r⁴ (A_f(0) − E_r(F_r)/S_r² − (4/r²)∫(f′)²) → −16∫(f″)²` as `r → ∞`: the second correction of the
comb is the fourth-order resolvent term `−16‖f″‖²/r⁴`, and the prime error `O(exp(−c√r))` does not
reach it. -/
theorem tendsto_pow_four_mul_combEnergy_rescaledTest_second_deficit {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hsupp : ∀ x, 1 < |x| → f x = 0) :
    Tendsto (fun r => r ^ 4 * (autoCorr f 0 -
        combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2 -
        4 / r ^ 2 * ∫ x, deriv f x ^ 2)) atTop
      (𝓝 (-16 * ∫ x, deriv (deriv f) x ^ 2)) := by
  have hfc : HasCompactSupport f := hasCompactSupport_of_eq_zero hsupp
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  obtain ⟨Cl, hCl⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf1 one_ne_zero
  set Λ : ℝ := (Cl : ℝ)
  have hΛ : ∀ a b, |f a - f b| ≤ Λ * |a - b| := fun a b => by
    have := hCl.dist_le_mul a b
    rwa [Real.dist_eq, Real.dist_eq] at this
  obtain ⟨c, hc, K, _, hev⟩ := exists_abs_combEnergy_rescaledTest_div_sub_le
  set M := K * (Λ * (∫ x, |f x|) + autoCorr f 0)
  have herr : Tendsto (fun r => r ^ 4 * (horizonEnergy (rescaledTest f r) -
      combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2)) atTop (𝓝 0) := by
    have hmaj := (tendsto_pow_four_mul_exp_neg_sqrt hc).const_mul |M|
    rw [mul_zero] at hmaj
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [hev] with r hr
    have h := hr f Λ hsupp hΛ
    have hr4 : 0 ≤ r ^ 4 := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hr4, abs_sub_comm]
    calc r ^ 4 * |combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2 -
          horizonEnergy (rescaledTest f r)| ≤ r ^ 4 * (M * Real.exp (-c * Real.sqrt r)) :=
          mul_le_mul_of_nonneg_left h hr4
      _ ≤ r ^ 4 * (|M| * Real.exp (-c * Real.sqrt r)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self M)
            (Real.exp_pos _).le) hr4
      _ = |M| * (r ^ 4 * Real.exp (-c * Real.sqrt r)) := by ring
  have h := (tendsto_pow_four_mul_horizonEnergy_rescaledTest_second_deficit hf hfc).add herr
  rw [add_zero] at h
  refine h.congr fun r => ?_
  ring

/-! ## §4. Fixed-aperture support bounds and the optimal coercive constant on the odd test class -/

/-- **Support-localized upper bound on the horizon energy.** For every continuous test `G`
supported in `[−R, R]` (`R ≥ 0`), `A_G` vanishes past `2R`, so
`J(G) ≤ (1 − e^{−R}) A_G(0) = (1 − e^{−R}) ∫ G²`. -/
theorem horizonEnergy_le_one_sub_exp_neg_mul_autoCorr_zero {G : ℝ → ℝ} {R : ℝ} (hG : Continuous G)
    (hR : 0 ≤ R) (hsupp : ∀ x, R < |x| → G x = 0) :
    horizonEnergy G ≤ (1 - Real.exp (-R)) * autoCorr G 0 := by
  have hGc : HasCompactSupport G := hasCompactSupport_of_eq_zero hsupp
  have hAG := continuous_autoCorr hG hGc
  have hAb : ∀ t, |autoCorr G t| ≤ autoCorr G 0 := abs_autoCorr_le_autoCorr_zero hG hGc
  have h2R : 0 ≤ 2 * R := by linarith
  set f : ℝ → ℝ := fun u => autoCorr G u * horizonDensity u
  have hfc : Continuous f := hAG.mul continuous_horizonDensity
  have hvan : ∀ u ∈ Ioi (2 * R), f u = 0 := fun u hu => by
    have hu2R : 2 * R < u := hu
    have h0 : autoCorr G u = 0 :=
      autoCorr_eq_zero_of_support hsupp (by rw [abs_of_pos (by linarith)]; linarith)
    simp [f, h0]
  have hsplit : horizonEnergy G = ∫ u in (0 : ℝ)..(2 * R), f u := by
    rw [horizonEnergy_eq_horizonIntegral_autoCorr hG hGc, horizonIntegral,
      ← Ioc_union_Ioi_eq_Ioi h2R,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hfc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        ((integrableOn_zero (μ := volume) (s := Ioi (2 * R))).congr_fun
          (fun u hu => (hvan u hu).symm) measurableSet_Ioi),
      setIntegral_congr_fun measurableSet_Ioi hvan, integral_zero, add_zero,
      intervalIntegral.integral_of_le h2R]
  rw [hsplit]
  calc (∫ u in (0 : ℝ)..(2 * R), f u)
      ≤ ∫ u in (0 : ℝ)..(2 * R), autoCorr G 0 * horizonDensity u := by
        refine intervalIntegral.integral_mono_on h2R (hfc.intervalIntegrable _ _)
          ((continuous_horizonDensity.const_mul _).intervalIntegrable _ _) fun u _ => ?_
        exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hAb u)) (horizonDensity_nonneg u)
    _ = autoCorr G 0 * (Real.exp (-0 / 2) - Real.exp (-(2 * R) / 2)) := by
        rw [intervalIntegral.integral_const_mul, integral_horizonDensity]
    _ = (1 - Real.exp (-R)) * autoCorr G 0 := by
        rw [neg_zero, zero_div, Real.exp_zero, show -(2 * R) / 2 = -R by ring]
        ring

/-- If `F` vanishes outside `[−R, R]`, then so does `deriv F`. -/
theorem deriv_eq_zero_of_support {F : ℝ → ℝ} {R : ℝ} (hsupp : ∀ x, R < |x| → F x = 0)
    {x : ℝ} (hx : R < |x|) : deriv F x = 0 := by
  have hev : F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy
    exact hsupp y hy
  rw [hev.deriv_eq, deriv_const]

/-- **Aperture-refined `H¹` lower bound on the horizon energy.** For every `F ∈ C¹` supported in
`[−R, R]` (`R ≥ 0`), applying the support-localized upper bound to `F′` inside the resolvent
identity gives `J(F) ≥ ∫F² − 4(1 − e^{−R})∫(F′)²`. -/
theorem horizonEnergy_ge_one_sub_exp_of_support {F : ℝ → ℝ} {R : ℝ} (hF : ContDiff ℝ 1 F)
    (hR : 0 ≤ R) (hsupp : ∀ x, R < |x| → F x = 0) :
    (∫ x, F x ^ 2) - 4 * (1 - Real.exp (-R)) * (∫ x, deriv F x ^ 2) ≤ horizonEnergy F := by
  have hFc : HasCompactSupport F := hasCompactSupport_of_eq_zero hsupp
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hdsupp : ∀ x, R < |x| → deriv F x = 0 := fun _ hx => deriv_eq_zero_of_support hsupp hx
  have h1 := horizonEnergy_eq_autoCorr_zero_sub_four_mul_horizonEnergy_deriv hF hFc
  have h2 := horizonEnergy_le_one_sub_exp_neg_mul_autoCorr_zero hdcont hR hdsupp
  rw [autoCorr_zero_eq_integral_sq] at h1 h2
  linarith

/-- The ledger's odd test class at aperture `R` with Dirichlet ratio at most `Λ²`: odd `C¹` tests
supported in `[−R, R]` satisfying `∫(F′)² ≤ Λ²∫F²`. -/
def OddApertureRegularityClass (R Λ : ℝ) (F : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 F ∧ (∀ x, F (-x) = -F x) ∧ (∀ x, R < |x| → F x = 0) ∧
    (∫ x, deriv F x ^ 2) ≤ Λ ^ 2 * ∫ x, F x ^ 2

/-- **Coercivity of `J` on the ledger's odd regularity class at aperture `R`.** Every test in
`OddApertureRegularityClass R Λ` (`R ≥ 0`) satisfies
`(1 − 4(1 − e^{−R})Λ²)∫F² ≤ J(F)` and `(1 − 4Λ²)∫F² ≤ J(F)`. In particular, `J` is uniformly
coercive on `OddApertureRegularityClass R Λ` whenever `Λ < ½ (1 − e^{−R})^{−1/2}` (and uniformly in
`R` whenever `Λ < ½`). -/
theorem horizonEnergy_ge_of_oddApertureRegularityClass {F : ℝ → ℝ} {R Λ : ℝ} (hR : 0 ≤ R)
    (hF : OddApertureRegularityClass R Λ F) :
    (1 - 4 * (1 - Real.exp (-R)) * Λ ^ 2) * (∫ x, F x ^ 2) ≤ horizonEnergy F ∧
      (1 - 4 * Λ ^ 2) * (∫ x, F x ^ 2) ≤ horizonEnergy F := by
  obtain ⟨hF1, _, hsupp, hreg⟩ := hF
  have hlo := horizonEnergy_ge_one_sub_exp_of_support hF1 hR hsupp
  have hexp1 : Real.exp (-R) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp0 : 0 ≤ Real.exp (-R) := (Real.exp_pos (-R)).le
  have hc : 0 ≤ 4 * (1 - Real.exp (-R)) := by linarith
  have hm := mul_le_mul_of_nonneg_left hreg hc
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hsub : (1 - 4 * Λ ^ 2) * (∫ x, F x ^ 2) ≤
      (1 - 4 * (1 - Real.exp (-R)) * Λ ^ 2) * (∫ x, F x ^ 2) := by
    refine mul_le_mul_of_nonneg_right ?_ hI0
    nlinarith [sq_nonneg Λ]
  refine ⟨by linarith, by linarith⟩

/-- **Asymptotic sharpness of the `1 − 4Λ²` coercive law on odd tests.** For any odd profile
`f ∈ C¹_c(ℝ)` with `∫(f′)² > 0`, the rescaled odd tests `F_r = rescaledTest f r` satisfy
`(A_{F_r}(0) − J(F_r)) / (4∫(F_r′)²) → 1` as `r → ∞`: the relative deficit `4∫(F′)²` in
`J(F) ≥ ∫F² − 4∫(F′)²` has the optimal constant `4`. -/
theorem tendsto_horizonEnergy_deficit_div_four_mul_deriv_sq {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (hdf : 0 < ∫ x, deriv f x ^ 2) :
    Tendsto (fun r => (autoCorr (rescaledTest f r) 0 - horizonEnergy (rescaledTest f r)) /
        (4 * ∫ x, deriv (rescaledTest f r) x ^ 2)) atTop (𝓝 1) := by
  have hdcont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hdcs : HasCompactSupport (deriv f) := hfc.deriv
  have hlim := (tendsto_horizonEnergy_rescaledTest hdcont hdcs).div_const (autoCorr (deriv f) 0)
  have hA0 : autoCorr (deriv f) 0 ≠ 0 := by
    rw [autoCorr_zero_eq_integral_sq]; exact hdf.ne'
  rw [div_self hA0] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  have h1 := horizonEnergy_rescaledTest_deficit_eq hf hfc hr
  have hA : autoCorr (rescaledTest f r) 0 = autoCorr f 0 := by
    rw [autoCorr_rescaledTest hr, zero_div]
  have hd : (∫ x, deriv (rescaledTest f r) x ^ 2) = r⁻¹ ^ 2 * autoCorr (deriv f) 0 := by
    rw [deriv_rescaledTest hf hr, ← autoCorr_zero_eq_integral_sq, autoCorr_const_mul,
      autoCorr_rescaledTest hr, zero_div]
  rw [hA, h1, hd]
  field_simp

/-- **Unconstrained smooth odd tests at a fixed aperture have optimal coercive constant `0`.**
For every fixed aperture `R > 0`, no constant `c > 0` satisfies `c ∫F² ≤ J(F)` across all smooth
odd tests supported in `[−R, R]`. -/
theorem not_exists_odd_fixed_aperture_horizonEnergy_ge {R : ℝ} (hR : 0 < R) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ F : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n F) →
      (∀ x, F (-x) = -F x) → (∀ x, R < |x| → F x = 0) →
      c * ∫ x, F x ^ 2 ≤ horizonEnergy F := by
  rintro ⟨c, hc, h⟩
  have hφ := continuous_oddBump
  have hφc := hasCompactSupport_oddBump
  have hmass : 0 < ∫ x, oddBump x ^ 2 := by
    have := autoCorr_oddBump_zero_pos
    simpa [autoCorr, sq] using this
  set K := ∫ v in Ioi (0 : ℝ), |autoCorr oddBump v|
  have hK : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun v _ => abs_nonneg _
  set lam := max (K / (c * ∫ x, oddBump x ^ 2) + 1) (1 / R + 1)
  have hlam1 : K / (c * ∫ x, oddBump x ^ 2) + 1 ≤ lam := le_max_left _ _
  have hlam2 : 1 / R + 1 ≤ lam := le_max_right _ _
  have hlam : 0 < lam := lt_of_lt_of_le (by positivity) hlam1
  set F := concentratedTest oddBump lam
  have hFsmooth : ∀ n : ℕ, ContDiff ℝ n F := fun n =>
    contDiff_const.mul ((contDiff_oddBump n).comp (contDiff_const.mul contDiff_id))
  have hFodd : ∀ x, F (-x) = -F x := fun x => by
    simp only [F, concentratedTest, mul_neg, oddBump_neg, mul_neg]
  have hFsupp : ∀ x, R < |x| → F x = 0 := fun x hx => by
    have h1 : 1 < |lam * x| := by
      rw [abs_mul, abs_of_pos hlam]
      have hlamR : 1 / R < lam := by linarith
      have : 1 < lam * R := (div_lt_iff₀ hR).mp hlamR
      nlinarith
    simp [F, concentratedTest, oddBump_eq_zero h1]
  have hJ := horizonEnergy_concentratedTest_le hφ hφc hlam
  have hlow := h F hFsmooth hFodd hFsupp
  rw [integral_concentratedTest_sq oddBump hlam] at hlow
  have hcm : 0 < c * ∫ x, oddBump x ^ 2 := mul_pos hc hmass
  have hkey : K / (2 * lam) < c * ∫ x, oddBump x ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    have : K < c * (∫ x, oddBump x ^ 2) * lam := by
      calc K = c * (∫ x, oddBump x ^ 2) * (K / (c * ∫ x, oddBump x ^ 2)) :=
            (mul_div_cancel₀ _ hcm.ne').symm
        _ < c * (∫ x, oddBump x ^ 2) * (K / (c * ∫ x, oddBump x ^ 2) + 1) := by linarith
        _ ≤ c * (∫ x, oddBump x ^ 2) * lam := mul_le_mul_of_nonneg_left hlam1 hcm.le
    nlinarith
  linarith

/-- **The raw integer comb is not uniformly coercive on smooth odd tests of fixed aperture `R`.**
For every `R > 0` and `c > 0`, there is a smooth odd test `F` supported in `[−R, R]` of positive
mass with `E_r(F) ≤ c S_r² ∫F²` for all large apertures `r`. -/
theorem exists_odd_fixed_aperture_combEnergy_le_mul {R c : ℝ} (hR : 0 < R) (hc : 0 < c) :
    ∃ F : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n F) ∧ (∀ x, F (-x) = -F x) ∧
      (∀ x, R < |x| → F x = 0) ∧ 0 < ∫ x, F x ^ 2 ∧
      ∀ᶠ r in atTop, combEnergy F (combPrimes r) combWeight ≤ c * combMass r ^ 2 * ∫ x, F x ^ 2 := by
  have hφ := continuous_oddBump
  have hφc := hasCompactSupport_oddBump
  have hmass : 0 < ∫ x, oddBump x ^ 2 := by
    have := autoCorr_oddBump_zero_pos
    simpa [autoCorr, sq] using this
  set K := ∫ v in Ioi (0 : ℝ), |autoCorr oddBump v|
  have hK : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun v _ => abs_nonneg _
  set lam := max (K / (c * ∫ x, oddBump x ^ 2) + 1) (1 / R + 1)
  have hlam1 : K / (c * ∫ x, oddBump x ^ 2) + 1 ≤ lam := le_max_left _ _
  have hlam2 : 1 / R + 1 ≤ lam := le_max_right _ _
  have hlam : 0 < lam := lt_of_lt_of_le (by positivity) hlam1
  set F := concentratedTest oddBump lam
  have hFsmooth : ∀ n : ℕ, ContDiff ℝ n F := fun n =>
    contDiff_const.mul ((contDiff_oddBump n).comp (contDiff_const.mul contDiff_id))
  have hFodd : ∀ x, F (-x) = -F x := fun x => by
    simp only [F, concentratedTest, mul_neg, oddBump_neg, mul_neg]
  have hFsupp : ∀ x, R < |x| → F x = 0 := fun x hx => by
    have h1 : 1 < |lam * x| := by
      rw [abs_mul, abs_of_pos hlam]
      have hlamR : 1 / R < lam := by linarith
      have : 1 < lam * R := (div_lt_iff₀ hR).mp hlamR
      nlinarith
    simp [F, concentratedTest, oddBump_eq_zero h1]
  have hF := continuous_concentratedTest hφ lam
  have hFc := hasCompactSupport_concentratedTest hφc hlam
  have hFm : ∫ x, F x ^ 2 = ∫ x, oddBump x ^ 2 := integral_concentratedTest_sq oddBump hlam
  have hcm : 0 < c * ∫ x, oddBump x ^ 2 := mul_pos hc hmass
  have hJ : horizonEnergy F < c * ∫ x, F x ^ 2 := by
    refine (horizonEnergy_concentratedTest_le hφ hφc hlam).trans_lt ?_
    rw [hFm, div_lt_iff₀ (by positivity)]
    have : K < c * (∫ x, oddBump x ^ 2) * lam := by
      calc K = c * (∫ x, oddBump x ^ 2) * (K / (c * ∫ x, oddBump x ^ 2)) :=
            (mul_div_cancel₀ _ hcm.ne').symm
        _ < c * (∫ x, oddBump x ^ 2) * (K / (c * ∫ x, oddBump x ^ 2) + 1) := by linarith
        _ ≤ c * (∫ x, oddBump x ^ 2) * lam := mul_le_mul_of_nonneg_left hlam1 hcm.le
    nlinarith
  refine ⟨F, hFsmooth, hFodd, hFsupp, hFm ▸ hmass, ?_⟩
  filter_upwards [(tendsto_combEnergy_div_combMass_sq_horizonEnergy hF hFc).eventually
    (eventually_le_nhds hJ), eventually_combMass_pos] with r hr hS
  rw [div_le_iff₀ (by positivity)] at hr
  linarith

end GaloisForLFunctions.ArithmeticCompensationTheory
