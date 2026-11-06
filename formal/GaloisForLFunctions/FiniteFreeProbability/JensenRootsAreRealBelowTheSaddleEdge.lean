import GaloisForLFunctions.FiniteFreeProbability.JensenLocalHermiteBiehler
import GaloisForLFunctions.FiniteFreeProbability.NonRealJensenCountBound
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

/-!
# Every root of `R_d(Ξ)` below the saddle edge is real

**Theorem.** For all large `d`, every root `z` of `R_d(Ξ)` with `|Re z| ≤ √(d log d)/100` is real.
Equivalently, every non-real zero `u` of the approximant `Φ_d` has `|Re u| < 100 √(d/log d)`: an off-line
zero of `Ξ` at height `γ` can be counted at degree `d` only if `d ≳ γ² log γ`. No property of the zeros of
`ζ` enters.

The upper half-plane above `[-X, X]` splits into three regions. Close to the axis (`t r₁ < 450`, where
`r₁` is the real part of the saddle at `Re z`) the modulus of the upper transform increases across the
axis. Above that, the exact saddle at `z` itself makes the transform at `conj z` negligible. Far out, `d/z`
lies in a compact cone around the imaginary axis on which `Ξ` does not vanish, and `Φ_d → Ξ` uniformly.
-/

open Polynomial Filter Topology Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace FiniteFreeProbability

noncomputable section

/-! ## The saddle at a complex point -/

/-- The rectangle of slopes with lower edge `ℓ`. -/
def slopeBox (ℓ L : ℝ) : Set ℂ := {a | ℓ ≤ a.re ∧ a.re ≤ L / 2 ∧ |a.im| ≤ 5}

theorem isClosed_slopeBox (ℓ L : ℝ) : IsClosed (slopeBox ℓ L) := by
  have h1 : IsClosed {a : ℂ | ℓ ≤ a.re} := isClosed_le continuous_const Complex.continuous_re
  have h2 : IsClosed {a : ℂ | a.re ≤ L / 2} := isClosed_le Complex.continuous_re continuous_const
  have h3 : IsClosed {a : ℂ | |a.im| ≤ 5} :=
    isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
  exact h1.inter (h2.inter h3)

theorem convex_slopeBox (ℓ L : ℝ) : Convex ℝ (slopeBox ℓ L) := by
  have h1 : Convex ℝ {a : ℂ | ℓ ≤ a.re} := convex_halfSpace_re_ge _
  have h2 : Convex ℝ {a : ℂ | a.re ≤ L / 2} := convex_halfSpace_re_le _
  have h3 : Convex ℝ {a : ℂ | |a.im| ≤ 5} := by
    have : {a : ℂ | |a.im| ≤ 5} = {a : ℂ | -5 ≤ a.im} ∩ {a : ℂ | a.im ≤ 5} := by
      ext a
      simp [abs_le]
    rw [this]
    exact (convex_halfSpace_im_ge _).inter (convex_halfSpace_im_le _)
  exact h1.inter (h2.inter h3)

/-- The point `τ = d/(a − iz)`. -/
def saddleTauAt (d : ℕ) (a z : ℂ) : ℂ := (d : ℂ) / (a - I * z)

theorem re_sub_I_mul (a z : ℂ) : (a - I * z).re = a.re + z.im := by simp

theorem im_sub_I_mul (a z : ℂ) : (a - I * z).im = a.im - z.re := by simp

theorem eight_thousand_le_exp_fourteen : (8000 : ℝ) ≤ Real.exp 14 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith only [this]
  have h2 : Real.exp 14 = Real.exp 1 ^ 14 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h2]
  calc (8000 : ℝ) ≤ 2 ^ 14 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 14

/-- **The saddle exists at a complex point of the upper half-plane.** -/
theorem exists_complex_saddle {d : ℕ} (hd : 0 < d) {z : ℂ} {ℓ : ℝ} (hℓ : Real.exp 14 ≤ ℓ)
    (hℓL : ℓ ≤ Real.log d / 2) (ht : 0 ≤ z.im)
    (hτ : ∀ a ∈ slopeBox ℓ (Real.log d), 400 ≤ (saddleTauAt d a z).re ∧
      2 * ℓ + 14 ≤ Real.log ‖saddleTauAt d a z‖) :
    ∃ a ∈ slopeBox ℓ (Real.log d), gammaSlope (saddleTauAt d a z) = a := by
  set L := Real.log (d : ℝ) with hL
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h8000 := eight_thousand_le_exp_fourteen
  have hℓ8 : 8000 ≤ ℓ := h8000.trans hℓ
  have hwne {a : ℂ} (ha : a ∈ slopeBox ℓ L) : ℓ ≤ ‖a - I * z‖ := by
    have h1 := Complex.re_le_norm (a - I * z)
    rw [re_sub_I_mul] at h1
    linarith only [h1, ha.1, ht]
  have hwpos {a : ℂ} (ha : a ∈ slopeBox ℓ L) : 0 < ‖a - I * z‖ := by
    have := hwne ha
    linarith only [this, hℓ8]
  have hnorm {a : ℂ} (ha : a ∈ slopeBox ℓ L) : ‖saddleTauAt d a z‖ * ‖a - I * z‖ = d := by
    rw [saddleTauAt, norm_div, Complex.norm_natCast]
    exact div_mul_cancel₀ _ (hwpos ha).ne'
  have hmaps : MapsTo (fun c => gammaSlope (saddleTauAt d c z)) (slopeBox ℓ L) (slopeBox ℓ L) := by
    intro a ha
    obtain ⟨hre, hlog⟩ := hτ a ha
    have hre1 : 1 ≤ (saddleTauAt d a z).re := by linarith only [hre]
    have hst := abs_le.1 (abs_re_gammaSlope_sub_le hre1)
    have him := abs_im_gammaSlope_le hre1
    have hτpos : 0 < ‖saddleTauAt d a z‖ :=
      lt_of_lt_of_le (by linarith only [hre]) (Complex.re_le_norm _)
    have hlogeq : Real.log ‖saddleTauAt d a z‖ + Real.log ‖a - I * z‖ = L := by
      rw [← Real.log_mul hτpos.ne' (hwpos ha).ne', hnorm ha]
    have h14 : 14 ≤ Real.log ‖a - I * z‖ := by
      rw [Real.le_log_iff_exp_le (hwpos ha)]
      exact hℓ.trans (hwne ha)
    refine ⟨?_, ?_, him⟩
    · linarith only [hst.1, hlog]
    · linarith only [hst.2, hlogeq, h14]
  have hderiv {a : ℂ} (ha : a ∈ slopeBox ℓ L) :
      HasDerivAt (fun b => gammaSlope (saddleTauAt d b z))
        (gammaSlopeDeriv (saddleTauAt d a z) * (-(d : ℂ) / (a - I * z) ^ 2)) a := by
    have hne : a - I * z ≠ 0 := norm_pos_iff.1 (hwpos ha)
    have hre := (hτ a ha).1
    have hτd : HasDerivAt (fun b => saddleTauAt d b z) (-(d : ℂ) / (a - I * z) ^ 2) a := by
      have h1 := ((hasDerivAt_id a).sub_const (I * z)).inv hne
      have h2 := h1.const_mul (d : ℂ)
      simp only [saddleTauAt, div_eq_mul_inv]
      refine h2.congr_deriv ?_
      simp [id]
      ring
    have hτne : saddleTauAt d a z ≠ 1 / 2 := re_ne_half (by linarith only [hre])
    exact (hasDerivAt_gammaSlope (by linarith only [hre]) hτne).comp a hτd
  have hderivnorm {a : ℂ} (ha : a ∈ slopeBox ℓ L) :
      ‖gammaSlopeDeriv (saddleTauAt d a z) * (-(d : ℂ) / (a - I * z) ^ 2)‖ ≤ 1 / 2 := by
    have hre := (hτ a ha).1
    have hρ : 4 ≤ ‖saddleTauAt d a z‖ := by
      have := Complex.re_le_norm (saddleTauAt d a z)
      linarith only [this, hre]
    have hb := norm_gammaSlopeDeriv_le (τ := saddleTauAt d a z) (by linarith only [hre]) hρ
    have hτpos : 0 < ‖saddleTauAt d a z‖ := by linarith only [hρ]
    have hW := hwpos ha
    rw [norm_mul, norm_div, norm_neg, norm_pow, Complex.norm_natCast, ← hnorm ha]
    calc
      _ ≤ 6 / ‖saddleTauAt d a z‖ * (‖saddleTauAt d a z‖ * ‖a - I * z‖ / ‖a - I * z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 6 / ‖a - I * z‖ := by field_simp
      _ ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hW (by norm_num)]
        linarith only [hwne ha, hℓ8]
  have hcontr {a b : ℂ} (ha : a ∈ slopeBox ℓ L) (hb : b ∈ slopeBox ℓ L) :
      ‖gammaSlope (saddleTauAt d a z) - gammaSlope (saddleTauAt d b z)‖ ≤ 1 / 2 * ‖a - b‖ :=
    (convex_slopeBox _ _).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun c => gammaSlope (saddleTauAt d c z)) (C := 1 / 2)
      (fun _ hc => (hderiv hc).hasDerivWithinAt) (fun _ hc => hderivnorm hc) hb ha
  have hmem : ((L / 2 : ℝ) : ℂ) ∈ slopeBox ℓ L := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Complex.ofReal_re]
      exact hℓL
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      norm_num
  have hcontracting : ContractingWith (1 / 2) (hmaps.restrict _ _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun c e => ?_⟩
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, dist_eq_norm]
    have := hcontr c.2 e.2
    simpa using this
  obtain ⟨a, ha, hfix, -, -⟩ := hcontracting.exists_fixedPoint' (isClosed_slopeBox _ _).isComplete hmaps
    hmem (edist_ne_top _ _)
  exact ⟨a, ha, hfix⟩

/-- The real part and the norm of `τ = d/w`. -/
theorem re_saddleTauAt (d : ℕ) (a z : ℂ) :
    (saddleTauAt d a z).re = d * (a - I * z).re / ‖a - I * z‖ ^ 2 := by
  rw [saddleTauAt, ← Complex.normSq_eq_norm_sq, Complex.div_re]
  simp only [natCast_re, natCast_im, zero_mul, zero_div, add_zero]

/-! ## The compact cone around the imaginary axis -/

theorem XiC_ne_zero_of_cone {u : ℂ} (h : |u.re| ≤ |u.im|) : XiC u ≠ 0 := by
  intro h0
  have hxi : xi (1 / 2 + I * u) = 0 := by
    have := XiC_eq_xiCentered u
    rw [h0, xiCentered] at this
    exact this.symm
  have hre := xi_zero_re_mem_open_unit hxi
  have hsre : (1 / 2 + I * u : ℂ).re = 1 / 2 - u.im := by
    simp
    ring
  have hsim : (1 / 2 + I * u : ℂ).im = u.re := by simp
  rw [hsre] at hre
  have him : |u.im| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith only [hre.1, hre.2]
  refine xi_ne_zero_of_abs_im_le_four (rho := 1 / 2 + I * u) ?_ hxi
  rw [hsim]
  linarith only [h, him]

/-- On a compact cone around the imaginary axis `Φ_d` eventually has no zero. -/
theorem eventually_scaledJensen_ne_zero_on_cone (U : ℝ) :
    ∀ᶠ d : ℕ in atTop, ∀ u : ℂ, ‖u‖ ≤ U → |u.re| ≤ |u.im| → scaledJensen xiCoeff d u ≠ 0 := by
  have hsum : ∀ z, HasSum (fun k => xiCoeff k * z ^ k) (XiC z) := fun z => by
    simpa [xiSeries, xiCoeff] using hasSum_xiSeries z
  have hf := summable_norm_mul_pow_of_summable fun z => (hsum z).summable
  have hloc := tendstoLocallyUniformly_scaledJensen hf (ψ := fun n => n) tendsto_id
  have hfun : (fun u => ∑' k, xiCoeff k * u ^ k) = XiC := funext fun u => (hsum u).tsum_eq
  rw [hfun] at hloc
  let S : Set ℂ := Metric.closedBall 0 U ∩ {u | |u.re| ≤ |u.im|}
  have hSc : IsCompact S := by
    refine (isCompact_closedBall 0 U).inter_right ?_
    exact isClosed_le (continuous_abs.comp Complex.continuous_re)
      (continuous_abs.comp Complex.continuous_im)
  have hmem {u : ℂ} (hu : ‖u‖ ≤ U) (hc : |u.re| ≤ |u.im|) : u ∈ S :=
    ⟨by simpa using hu, hc⟩
  rcases S.eq_empty_or_nonempty with hempty | hne
  · refine Eventually.of_forall fun d u hu hc _ => ?_
    have := hmem hu hc
    rw [hempty] at this
    exact this
  obtain ⟨u₀, hu₀, hmin⟩ := hSc.exists_isMinOn hne XiC_differentiable.continuous.norm.continuousOn
  have hpos : 0 < ‖XiC u₀‖ := norm_pos_iff.2 (XiC_ne_zero_of_cone hu₀.2)
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.mp hloc) S hSc
  have hev := Metric.tendstoUniformlyOn_iff.mp hunif _ hpos
  filter_upwards [hev] with d hd u hu hc h0
  have h1 := hd u (hmem hu hc)
  rw [h0, dist_zero_right] at h1
  exact absurd (hmin (hmem hu hc)) (not_le.2 h1)

/-! ## Assembly -/

/-- The constant bounding the region of the exact complex saddle. -/
def saddleEdgeConstant : ℝ := Real.exp (2 * Real.exp 14 + 16)

theorem saddleEdgeConstant_ge : (800 : ℝ) ≤ saddleEdgeConstant := by
  have h := eight_thousand_le_exp_fourteen
  have h1 : Real.exp 14 ≤ saddleEdgeConstant := by
    apply Real.exp_le_exp.2
    linarith only [h]
  linarith only [h, h1]

/-- The degrees to which the argument applies. -/
structure JensenLargeDegree (d : ℕ) : Prop where
  hR : SaddleRange d (saddleX d)
  hX10 : 10 ≤ saddleX d
  hL : (10 : ℝ) ^ 10 ≤ Real.log d
  hsd : 1000 ≤ Real.sqrt d
  hT : 4 * (saddleX d + 5 + Real.log d) ≤ Real.exp (3 / 5 * Real.log d - 14)
  hC : 4 * saddleEdgeConstant * (saddleX d + Real.log d) ≤ d
  hΦ : ∀ u : ℂ, ‖u‖ ≤ 2 * saddleEdgeConstant → |u.re| ≤ |u.im| → scaledJensen xiCoeff d u ≠ 0

variable {d : ℕ}

theorem JensenLargeDegree.X_sq (h : JensenLargeDegree d) :
    saddleX d ^ 2 = d * Real.log d / 10000 := by
  have hdL : 0 ≤ (d : ℝ) * Real.log d := mul_nonneg (Nat.cast_nonneg d) (by
    have := h.hL
    have h10 : (0 : ℝ) < 10 ^ 10 := by norm_num
    linarith only [this, h10])
  rw [saddleX, div_pow, Real.sq_sqrt hdL]
  norm_num

theorem JensenLargeDegree.d_ge (h : JensenLargeDegree d) : (1000000 : ℝ) ≤ d := by
  have hsq := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have := h.hsd
  nlinarith only [hsq, this]

/-- The two far conditions follow from a bound for `‖w‖`. -/
theorem far_conditions {τ₁ w : ℂ} (hd : 0 < d) (hs : w * τ₁ = d) (hw : 0 < w.re)
    (hW : ‖w‖ ≤ 3 / 128 * w.re * Real.sqrt d) (hτ : 0 < τ₁.re) :
    4 / Real.sqrt (d / π ^ 2) * ‖τ₁‖ ≤ 3 / 8 * τ₁.re := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_four
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hsqrt : Real.sqrt ((d : ℝ) / π ^ 2) = Real.sqrt d / π := by
    rw [Real.sqrt_div hdR.le, Real.sqrt_sq hπ.le]
  have hρ : 0 < ‖τ₁‖ := lt_of_lt_of_le hτ (Complex.re_le_norm τ₁)
  have hid := re_mul_norm_sq hs
  have hnid : ‖w‖ * ‖τ₁‖ = d := by rw [← norm_mul, hs, Complex.norm_natCast]
  have hWpos : 0 < ‖w‖ := lt_of_lt_of_le hw (Complex.re_le_norm w)
  -- `r ‖w‖ = Re(w) ‖τ₁‖`
  have hr : τ₁.re * ‖w‖ = w.re * ‖τ₁‖ := by
    have h1 : (‖w‖ * ‖τ₁‖) * τ₁.re = (w.re * ‖τ₁‖) * ‖τ₁‖ := by
      rw [hnid, ← hid]
      ring
    have h2 : ‖τ₁‖ * (τ₁.re * ‖w‖) = ‖τ₁‖ * (w.re * ‖τ₁‖) := by linarith only [h1]
    exact mul_left_cancel₀ hρ.ne' h2
  rw [hsqrt, div_div_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hsd]
  apply le_of_mul_le_mul_right _ hWpos
  have h4 : 4 * π ≤ 16 := by linarith only [hπ4]
  calc
    4 * π * ‖τ₁‖ * ‖w‖ ≤ 16 * ‖τ₁‖ * ‖w‖ := by
      apply mul_le_mul_of_nonneg_right _ hWpos.le
      exact mul_le_mul_of_nonneg_right h4 hρ.le
    _ ≤ 16 * ‖τ₁‖ * (3 / 128 * w.re * Real.sqrt d) :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    _ = 3 / 8 * (τ₁.re * ‖w‖) * Real.sqrt d := by
      rw [hr]
      ring
    _ = 3 / 8 * τ₁.re * Real.sqrt d * ‖w‖ := by ring

theorem small_condition (h : JensenLargeDegree d) : 4 / Real.sqrt ((d : ℝ) / π ^ 2) ≤ 1 / 2 := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_four
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [Real.sqrt_div hdR, Real.sqrt_sq hπ.le, div_div_eq_mul_div]
  have hsd := h.hsd
  rw [div_le_div_iff₀ (by linarith only [hsd]) (by norm_num)]
  nlinarith only [hsd, hπ4]

/-- `Re τ ≥ 400` and `tr ≥ 3` from `‖w‖² ≤ …`. -/
theorem JensenLargeDegree.caseA (h : JensenLargeDegree d) {z ax : ℂ} (ht : 0 < z.im)
    (hx : |z.re| ≤ saddleX d)
    (hzA : ‖z‖ + Real.log d ≤ Real.exp (3 / 5 * Real.log d - 14))
    (hax : ax ∈ saddleRect (Real.log d))
    (h450 : 450 ≤ z.im * (saddleTau d ax z.re).re) :
    (jensenRev d xiSeries).eval z ≠ 0 := by
  have hd := h.hR.hd
  have hdR : (0 : ℝ) < d := h.hR.d_pos
  set L := Real.log (d : ℝ) with hLdef
  set X := saddleX d with hXdef
  have hL1 : (10 : ℝ) ^ 10 ≤ L := h.hL
  have hL100 : (100 : ℝ) ≤ L := by
    have h10 : (100 : ℝ) ≤ 10 ^ 10 := by norm_num
    linarith only [hL1, h10]
  have hLone : (1 : ℝ) ≤ L := by linarith only [hL100]
  have hLpos : 0 < L := by linarith only [hL100]
  have hXsq : X ^ 2 = d * L / 10000 := h.X_sq
  have hX0 : 0 ≤ X := (by norm_num : (0 : ℝ) ≤ 10).trans h.hX10
  have hX5 : (X + 5) ^ 2 ≤ d * L / 5000 + 50 := by nlinarith only [sq_nonneg (X - 5), hXsq]
  have hd6 := h.d_ge
  have h8000 := eight_thousand_le_exp_fourteen
  have hLe14 : Real.exp 14 ≤ L / 5 := by
    have h5 : 5 * Real.exp 14 ≤ L := h.hR.hL
    linarith only [h5]
  have hLexp : Real.exp L = d := Real.exp_log hdR
  -- `T_A ≤ d/800`
  have hTA : 800 * Real.exp (3 / 5 * L - 14) ≤ d := by
    rw [← hLexp]
    have e : Real.exp L = Real.exp (3 / 5 * L - 14) * Real.exp (2 / 5 * L + 14) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have h14 : Real.exp 14 ≤ Real.exp (2 / 5 * L + 14) :=
      Real.exp_le_exp.2 (by linarith only [hLpos])
    linarith only [h14, h8000]
  obtain ⟨a, ha, hfix⟩ := exists_complex_saddle hd (z := z) (ℓ := L / 5) hLe14
    (by linarith only [hLpos]) ht.le (fun a ha => by
      have hwre := re_sub_I_mul a z
      have hwim := im_sub_I_mul a z
      set w := a - I * z with hw
      have hB : L / 5 ≤ w.re := by linarith only [hwre, ha.1, ht]
      have hBpos : 0 < w.re := by linarith only [hB, hLpos]
      have hWpos : 0 < ‖w‖ := lt_of_lt_of_le hBpos (Complex.re_le_norm w)
      have hanorm : ‖a‖ ≤ L := by
        have h1 := Complex.norm_le_abs_re_add_abs_im a
        have h2 : |a.re| ≤ L / 2 := by
          rw [abs_le]
          constructor <;> linarith only [ha.1, ha.2.1, hLpos]
        have h3 := ha.2.2
        linarith only [h1, h2, h3, hL1, (by norm_num : (100 : ℝ) ≤ 10 ^ 10)]
      have hWle : ‖w‖ ≤ Real.exp (3 / 5 * L - 14) := by
        have h1 : ‖w‖ ≤ ‖a‖ + ‖z‖ := by
          have h2 := norm_sub_le a (I * z)
          rw [norm_mul, Complex.norm_I, one_mul] at h2
          exact h2
        linarith only [h1, hanorm, hzA]
      have him : |w.im| ≤ X + 5 := by
        rw [hwim]
        have h1 := abs_sub a.im z.re
        have h2 := ha.2.2
        linarith only [h1, h2, hx]
      have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have him2 : w.im ^ 2 ≤ (X + 5) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) him 2
      have hBle : w.re ≤ ‖w‖ := Complex.re_le_norm w
      refine ⟨?_, ?_⟩
      · rw [re_saddleTauAt, ← hw, le_div_iff₀ (by positivity), hsq]
        have h1 : 800 * w.re ≤ d := by linarith only [hBle, hWle, hTA]
        have h2 : 800 * (X + 5) ^ 2 ≤ d * w.re := by
          have h3 : (d : ℝ) * (L / 5) ≤ d * w.re := mul_le_mul_of_nonneg_left hB hdR.le
          have h4 : (1000000 : ℝ) ≤ d * L := hd6.trans (le_mul_of_one_le_right hdR.le hLone)
          nlinarith only [h3, hX5, h4]
        nlinarith only [h1, h2, him2, hBpos]
      · have hτnorm : ‖saddleTauAt d a z‖ = d / ‖w‖ := by
          rw [saddleTauAt, norm_div, Complex.norm_natCast]
        rw [hτnorm, Real.log_div hdR.ne' hWpos.ne']
        have hlog : Real.log ‖w‖ ≤ 3 / 5 * L - 14 := by
          rw [Real.log_le_iff_le_exp hWpos]
          exact hWle
        linarith only [hlog])
  -- Data of the saddle at `z`.
  set τ₁ := saddleTauAt d a z with hτ₁
  have hwre := re_sub_I_mul a z
  have hwim := im_sub_I_mul a z
  set w := a - I * z with hw
  have hB : L / 5 ≤ w.re := by linarith only [hwre, ha.1, ht]
  have hBpos : 0 < w.re := by linarith only [hB, hLpos]
  have hWpos : 0 < ‖w‖ := lt_of_lt_of_le hBpos (Complex.re_le_norm w)
  have hwne : w ≠ 0 := norm_pos_iff.1 hWpos
  have hsw : w * τ₁ = d := by
    rw [hτ₁, saddleTauAt, ← hw]
    field_simp
  have hs : (gammaSlope τ₁ - I * z) * τ₁ = d := by rw [hfix]; exact hsw
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have him : |w.im| ≤ X + 5 := by
    rw [hwim]
    have h1 := abs_sub a.im z.re
    have h2 := ha.2.2
    linarith only [h1, h2, hx]
  have him2 : w.im ^ 2 ≤ (X + 5) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) him 2
  have hτre : τ₁.re = d * w.re / ‖w‖ ^ 2 := re_saddleTauAt d a z
  have hBle : w.re ≤ ‖w‖ := Complex.re_le_norm w
  have hanorm : ‖a‖ ≤ L := by
    have h1 := Complex.norm_le_abs_re_add_abs_im a
    have h2 : |a.re| ≤ L / 2 := by
      rw [abs_le]
      constructor <;> linarith only [ha.1, ha.2.1, hLpos]
    have h3 := ha.2.2
    linarith only [h1, h2, h3, hL1, (by norm_num : (100 : ℝ) ≤ 10 ^ 10)]
  have hWle : ‖w‖ ≤ Real.exp (3 / 5 * L - 14) := by
    have h1 : ‖w‖ ≤ ‖a‖ + ‖z‖ := by
      have h2 := norm_sub_le a (I * z)
      rw [norm_mul, Complex.norm_I, one_mul] at h2
      exact h2
    linarith only [h1, hanorm, hzA]
  have hr400 : 400 ≤ τ₁.re := by
    rw [hτre, le_div_iff₀ (by positivity), hsq]
    have h1 : 800 * w.re ≤ d := by linarith only [hBle, hWle, hTA]
    have h2 : 800 * (X + 5) ^ 2 ≤ d * w.re := by
      have h3 : (d : ℝ) * (L / 5) ≤ d * w.re := mul_le_mul_of_nonneg_left hB hdR.le
      have h4 : (1000000 : ℝ) ≤ d * L := hd6.trans (le_mul_of_one_le_right hdR.le hLone)
      nlinarith only [h3, hX5, h4]
    nlinarith only [h1, h2, him2, hBpos]
  have hA : 8000 ≤ (gammaSlope τ₁).re := by
    rw [hfix]
    linarith only [ha.1, hLe14, h8000]
  -- `t r ≥ 3`, by comparison with the real saddle when `t ≤ L`.
  have htr : 3 ≤ z.im * τ₁.re := by
    by_cases htL : z.im ≤ L
    · set wx := ax - I * (z.re : ℂ) with hwx
      have hwxre : wx.re = ax.re := by simp [hwx]
      have hwxim : wx.im = ax.im - z.re := by simp [hwx]
      have hτx : (saddleTau d ax z.re).re = d * wx.re / ‖wx‖ ^ 2 := by
        rw [saddleTau, ← hwx, ← Complex.normSq_eq_norm_sq, Complex.div_re]
        simp only [natCast_re, natCast_im, zero_mul, zero_div, add_zero]
      have hAx1 := hax.1
      have hAx2 := hax.2.1
      have hwxsq : ‖wx‖ ^ 2 = ax.re ^ 2 + (ax.im - z.re) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hwxre, hwxim]
        ring
      have hWx0 : 0 < ‖wx‖ ^ 2 := by
        rw [hwxsq]
        have : 0 < ax.re := by linarith only [hAx1, hLpos]
        positivity
      -- `‖w‖² ≤ 60 ‖wx‖²`
      have him3 : (a.im - z.re) ^ 2 ≤ 2 * (ax.im - z.re) ^ 2 + 200 := by
        have h1 := (abs_le.1 ha.2.2)
        have h2 := (abs_le.1 hax.2.2)
        nlinarith only [sq_nonneg (ax.im - z.re - (a.im - ax.im)), h1.1, h1.2, h2.1, h2.2,
          sq_nonneg (a.im - ax.im)]
      have hBup : w.re ≤ 3 / 2 * L := by linarith only [hwre, ha.2.1, htL]
      have hWW : ‖w‖ ^ 2 ≤ 60 * ‖wx‖ ^ 2 := by
        rw [hsq, hwxsq, hwim]
        have h1 : w.re ^ 2 ≤ (3 / 2 * L) ^ 2 := pow_le_pow_left₀ hBpos.le hBup 2
        have h2 : (L / 5) ^ 2 ≤ ax.re ^ 2 := pow_le_pow_left₀ (by positivity) hAx1 2
        have h3 : (0 : ℝ) ≤ (ax.im - z.re) ^ 2 := sq_nonneg _
        have h4 : (10000 : ℝ) ≤ L ^ 2 := by nlinarith only [hL100]
        nlinarith only [h1, h2, h3, h4, him3]
      have hcompare : (saddleTau d ax z.re).re ≤ 150 * τ₁.re := by
        have hw2pos : 0 < ‖w‖ ^ 2 := by positivity
        have e : 150 * ((d : ℝ) * w.re / ‖w‖ ^ 2) * ‖wx‖ ^ 2 =
            150 * ((d : ℝ) * w.re * ‖wx‖ ^ 2) / ‖w‖ ^ 2 := by ring
        rw [hτx, hτre, div_le_iff₀ hWx0, e, le_div_iff₀ hw2pos]
        have h1 : ax.re ≤ L / 2 := hAx2
        have h2 : (d : ℝ) * ax.re * ‖w‖ ^ 2 ≤ d * (L / 2) * (60 * ‖wx‖ ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hdR.le) hWW (by positivity) (by positivity)
        have h3 : (d : ℝ) * (L / 2) * (60 * ‖wx‖ ^ 2) ≤ 150 * (d * w.re * ‖wx‖ ^ 2) := by
          have h4 : (d : ℝ) * ‖wx‖ ^ 2 * (L / 5) ≤ d * ‖wx‖ ^ 2 * w.re :=
            mul_le_mul_of_nonneg_left hB (by positivity)
          nlinarith only [h4]
        calc
          (d : ℝ) * wx.re * ‖w‖ ^ 2 = d * ax.re * ‖w‖ ^ 2 := by rw [hwxre]
          _ ≤ _ := h2.trans h3
          _ = _ := by ring
      have hmul := mul_le_mul_of_nonneg_left hcompare ht.le
      nlinarith only [h450, hmul]
    · push Not at htL
      have hBt : w.re ≤ 3 / 2 * z.im := by linarith only [hwre, ha.2.1, htL]
      have hBt2 : L ≤ w.re := by linarith only [hwre, ha.1, htL, hLpos]
      rw [hτre, ← mul_div_assoc, le_div_iff₀ (by positivity), hsq]
      have ht23 : 2 / 3 * w.re ≤ z.im := by linarith only [hBt]
      have h1 : 2 / 3 * w.re * (d * w.re) ≤ z.im * (d * w.re) :=
        mul_le_mul_of_nonneg_right ht23 (by positivity)
      have h2 : (L : ℝ) ^ 2 ≤ w.re ^ 2 := pow_le_pow_left₀ hLpos.le hBt2 2
      have h3 : (100000 : ℝ) ≤ L := by
        have : (100000 : ℝ) ≤ 10 ^ 10 := by norm_num
        linarith only [this, hL1]
      have h4 : (d : ℝ) * L ≤ d * L ^ 2 / 100000 := by
        have h5 : L * 100000 ≤ L ^ 2 := by nlinarith only [h3, hLpos]
        have h6 := mul_le_mul_of_nonneg_left h5 hdR.le
        rw [le_div_iff₀ (by norm_num)]
        nlinarith only [h6]
      have h7 : (d : ℝ) * L ^ 2 ≤ d * w.re ^ 2 := mul_le_mul_of_nonneg_left h2 hdR.le
      have h8 : (10 : ℝ) ≤ d := by linarith only [hd6]
      have h9 : 10 * w.re ^ 2 ≤ d * w.re ^ 2 := mul_le_mul_of_nonneg_right h8 (sq_nonneg _)
      have hdL1 : (1000 : ℝ) ≤ d * L :=
        (by linarith only [hd6] : (1000 : ℝ) ≤ d).trans (le_mul_of_one_le_right hdR.le hLone)
      nlinarith only [h1, h9, h7, h4, hX5, him2, hdL1, sq_nonneg w.re]
  -- The far conditions.
  have hfar : 4 / Real.sqrt (d / π ^ 2) * ‖τ₁‖ ≤ 3 / 8 * τ₁.re := by
    refine far_conditions hd hsw hBpos ?_ (by linarith only [hr400])
    have hsd := h.hsd
    have hsdsq := Real.sq_sqrt hdR.le
    set sd := Real.sqrt (d : ℝ) with hsddef
    have hWbound : ‖w‖ ≤ w.re + (X + 5) := by
      have h1 := Complex.norm_le_abs_re_add_abs_im w
      rw [abs_of_pos hBpos] at h1
      linarith only [h1, him]
    -- `X = sd √L / 100`
    have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
    have hsLsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLpos.le
    have hXeq : X = sd * Real.sqrt L / 100 := by
      rw [hXdef, saddleX, Real.sqrt_mul hdR.le]
    have hsLbig : 1000 ≤ Real.sqrt L := by
      rw [Real.le_sqrt' (by norm_num)]
      have : (1000 : ℝ) ^ 2 ≤ 10 ^ 10 := by norm_num
      linarith only [this, hL1]
    have hBL : Real.sqrt L * 200 ≤ w.re := by
      have h1 : L / 5 ≤ w.re := hB
      have h2 : Real.sqrt L * 1000 ≤ L := by nlinarith only [hsLbig, hsLsq, hsL]
      linarith only [h1, h2]
    have h5 : X + 5 ≤ 1 / 100 * w.re * sd := by
      rw [hXeq]
      nlinarith only [hBL, hsd, hsLbig, hBpos, mul_le_mul_of_nonneg_right hBL (by linarith only [hsd] : 0 ≤ sd)]
    have h6 : w.re ≤ 1 / 1000 * w.re * sd := by nlinarith only [hsd, hBpos]
    nlinarith only [hWbound, h5, h6, hBpos, hsd]
  exact eval_ne_zero_of_far hd ht hs hA hr400 htr hfar (small_condition h)

/-- The intermediate region, where `Re a` may be much smaller than `log d`. -/
theorem JensenLargeDegree.caseB (h : JensenLargeDegree d) {z : ℂ} (ht : 0 < z.im)
    (hx : |z.re| ≤ saddleX d)
    (hzA : Real.exp (3 / 5 * Real.log d - 14) < ‖z‖ + Real.log d)
    (hzB : (‖z‖ + Real.log d) * saddleEdgeConstant < d) :
    (jensenRev d xiSeries).eval z ≠ 0 := by
  have hd := h.hR.hd
  have hdR : (0 : ℝ) < d := h.hR.d_pos
  set L := Real.log (d : ℝ) with hLdef
  set X := saddleX d with hXdef
  have hL1 : (10 : ℝ) ^ 10 ≤ L := h.hL
  have hLpos : 0 < L := by
    have h10 : (0 : ℝ) < 10 ^ 10 := by norm_num
    linarith only [hL1, h10]
  have hX10 : 10 ≤ X := h.hX10
  have hT : 4 * (X + 5 + L) ≤ Real.exp (3 / 5 * L - 14) := h.hT
  have h8000 := eight_thousand_le_exp_fourteen
  have hd6 := h.d_ge
  have hC800 := saddleEdgeConstant_ge
  have hCpos : 0 < saddleEdgeConstant := by linarith only [hC800]
  have hLe14 : Real.exp 14 ≤ L / 2 := by
    have h5 : 5 * Real.exp 14 ≤ L := h.hR.hL
    linarith only [h5, Real.exp_pos 14]
  -- `t` dominates `X` and `L`.
  have hzbig : 3 * (X + 5 + L) ≤ ‖z‖ := by linarith only [hzA, hT, hX10]
  have hzsum : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos ht] at hzsum
  have htbig : 2 * (X + 5 + L) ≤ z.im := by linarith only [hzbig, hzsum, hx, hX10, hLpos]
  obtain ⟨a, ha, hfix⟩ := exists_complex_saddle hd (z := z) (ℓ := Real.exp 14) le_rfl hLe14 ht.le
    (fun a ha => by
      have hwre := re_sub_I_mul a z
      have hwim := im_sub_I_mul a z
      set w := a - I * z with hw
      have hBpos : 0 < w.re := by linarith only [hwre, ha.1, ht, Real.exp_pos 14]
      have hWpos : 0 < ‖w‖ := lt_of_lt_of_le hBpos (Complex.re_le_norm w)
      have hanorm : ‖a‖ ≤ L := by
        have h1 := Complex.norm_le_abs_re_add_abs_im a
        have h2 : |a.re| ≤ L / 2 := by
          rw [abs_le]
          constructor <;> linarith only [ha.1, ha.2.1, Real.exp_pos 14, hLpos]
        have h3 := ha.2.2
        linarith only [h1, h2, h3, hL1, (by norm_num : (100 : ℝ) ≤ 10 ^ 10)]
      have hWle : ‖w‖ ≤ ‖z‖ + L := by
        have h2 := norm_sub_le a (I * z)
        rw [norm_mul, Complex.norm_I, one_mul] at h2
        linarith only [h2, hanorm]
      have hWC : ‖w‖ * saddleEdgeConstant ≤ d := by
        have := mul_le_mul_of_nonneg_right hWle hCpos.le
        linarith only [this, hzB]
      have him : |w.im| ≤ X + 5 := by
        rw [hwim]
        have h1 := abs_sub a.im z.re
        have h2 := ha.2.2
        linarith only [h1, h2, hx]
      have hBt : z.im ≤ w.re := by linarith only [hwre, ha.1, Real.exp_pos 14]
      have him2 : w.im ^ 2 ≤ w.re ^ 2 := by
        rw [← sq_abs w.im]
        refine pow_le_pow_left₀ (abs_nonneg _) (him.trans ?_) 2
        linarith only [htbig, hBt, hLpos, hX10]
      have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have hBle : w.re ≤ ‖w‖ := Complex.re_le_norm w
      refine ⟨?_, ?_⟩
      · rw [re_saddleTauAt, ← hw, le_div_iff₀ (by positivity), hsq]
        have h1 : w.re * saddleEdgeConstant ≤ d :=
          (mul_le_mul_of_nonneg_right hBle hCpos.le).trans hWC
        have h2 : 800 * w.re ≤ d := by nlinarith only [h1, hC800, hBpos]
        nlinarith only [h2, him2, hBpos]
      · have hτnorm : ‖saddleTauAt d a z‖ = d / ‖w‖ := by
          rw [saddleTauAt, norm_div, Complex.norm_natCast]
        have hge : saddleEdgeConstant ≤ d / ‖w‖ := by
          rw [le_div_iff₀ hWpos, mul_comm]
          exact hWC
        have hlog := Real.log_le_log hCpos hge
        rw [saddleEdgeConstant, Real.log_exp] at hlog
        rw [hτnorm]
        linarith only [hlog])
  -- Data of the saddle at `z`.
  set τ₁ := saddleTauAt d a z with hτ₁
  have hwre := re_sub_I_mul a z
  have hwim := im_sub_I_mul a z
  set w := a - I * z with hw
  have hBt : z.im ≤ w.re := by linarith only [hwre, ha.1, Real.exp_pos 14]
  have hBpos : 0 < w.re := by linarith only [hBt, ht]
  have hWpos : 0 < ‖w‖ := lt_of_lt_of_le hBpos (Complex.re_le_norm w)
  have hwne : w ≠ 0 := norm_pos_iff.1 hWpos
  have hsw : w * τ₁ = d := by
    rw [hτ₁, saddleTauAt, ← hw]
    field_simp
  have hs : (gammaSlope τ₁ - I * z) * τ₁ = d := by rw [hfix]; exact hsw
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have him : |w.im| ≤ X + 5 := by
    rw [hwim]
    have h1 := abs_sub a.im z.re
    have h2 := ha.2.2
    linarith only [h1, h2, hx]
  have himB : |w.im| ≤ w.re := him.trans (by linarith only [htbig, hBt, hLpos, hX10])
  have him2 : w.im ^ 2 ≤ w.re ^ 2 := by
    rw [← sq_abs w.im]
    exact pow_le_pow_left₀ (abs_nonneg _) himB 2
  have hτre : τ₁.re = d * w.re / ‖w‖ ^ 2 := re_saddleTauAt d a z
  have hBle : w.re ≤ ‖w‖ := Complex.re_le_norm w
  have hanorm : ‖a‖ ≤ L := by
    have h1 := Complex.norm_le_abs_re_add_abs_im a
    have h2 : |a.re| ≤ L / 2 := by
      rw [abs_le]
      constructor <;> linarith only [ha.1, ha.2.1, Real.exp_pos 14, hLpos]
    have h3 := ha.2.2
    linarith only [h1, h2, h3, hL1, (by norm_num : (100 : ℝ) ≤ 10 ^ 10)]
  have hWle : ‖w‖ ≤ ‖z‖ + L := by
    have h2 := norm_sub_le a (I * z)
    rw [norm_mul, Complex.norm_I, one_mul] at h2
    linarith only [h2, hanorm]
  have hWC : ‖w‖ * saddleEdgeConstant ≤ d := by
    have := mul_le_mul_of_nonneg_right hWle hCpos.le
    linarith only [this, hzB]
  have hr400 : 400 ≤ τ₁.re := by
    rw [hτre, le_div_iff₀ (by positivity), hsq]
    have h1 : w.re * saddleEdgeConstant ≤ d :=
      (mul_le_mul_of_nonneg_right hBle hCpos.le).trans hWC
    have h2 : 800 * w.re ≤ d := by nlinarith only [h1, hC800, hBpos]
    nlinarith only [h2, him2, hBpos]
  have hA : 8000 ≤ (gammaSlope τ₁).re := by
    rw [hfix]
    linarith only [ha.1, h8000]
  have htr : 3 ≤ z.im * τ₁.re := by
    have ht2 : w.re / 2 ≤ z.im := by linarith only [hwre, ha.2.1, htbig, hX10, hLpos]
    rw [hτre, ← mul_div_assoc, le_div_iff₀ (by positivity), hsq]
    have h1 : w.re / 2 * (d * w.re) ≤ z.im * (d * w.re) :=
      mul_le_mul_of_nonneg_right ht2 (by positivity)
    have h2 : 12 * w.re ^ 2 ≤ d * w.re ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [hd6]) (sq_nonneg _)
    nlinarith only [h1, h2, him2]
  have hfar : 4 / Real.sqrt (d / π ^ 2) * ‖τ₁‖ ≤ 3 / 8 * τ₁.re := by
    refine far_conditions hd hsw hBpos ?_ (by linarith only [hr400])
    have hsd := h.hsd
    have hWbound : ‖w‖ ≤ 2 * w.re := by
      have h1 := Complex.norm_le_abs_re_add_abs_im w
      rw [abs_of_pos hBpos] at h1
      linarith only [h1, himB]
    nlinarith only [hWbound, hsd, hBpos]
  exact eval_ne_zero_of_far hd ht hs hA hr400 htr hfar (small_condition h)

/-- The near-axis condition at the real saddle. -/
theorem JensenLargeDegree.near_condition (h : JensenLargeDegree d) {x : ℝ} {ax : ℂ}
    (hx : |x| ≤ saddleX d) (hax : ax ∈ saddleRect (Real.log d)) :
    450 * ‖saddleTau d ax x‖ / (saddleTau d ax x).re ≤ Real.sqrt (d / π ^ 2) / 200 := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_four
  have hd := h.hR.hd
  have hdR : (0 : ℝ) < d := h.hR.d_pos
  set L := Real.log (d : ℝ) with hLdef
  have hL1 : (10 : ℝ) ^ 10 ≤ L := h.hL
  have hLpos : 0 < L := by
    have h10 : (0 : ℝ) < 10 ^ 10 := by norm_num
    linarith only [hL1, h10]
  set τ := saddleTau d ax x with hτ
  set w := ax - I * (x : ℂ) with hw
  have hwre : w.re = ax.re := by simp [hw]
  have hsw : w * τ = d := h.hR.saddle_identity hax
  have hr0 : 0 < τ.re := by
    have := h.hR.re_tau_ge hax hx
    linarith only [this]
  have hρ : 0 < ‖τ‖ := lt_of_lt_of_le hr0 (Complex.re_le_norm τ)
  have hid := re_mul_norm_sq hsw
  have hnid : ‖w‖ * ‖τ‖ = d := by rw [← norm_mul, hsw, Complex.norm_natCast]
  have hB : L / 5 ≤ w.re := by
    rw [hwre]
    exact hax.1
  have hBpos : 0 < w.re := by linarith only [hB, hLpos]
  have hWpos : 0 < ‖w‖ := lt_of_lt_of_le hBpos (Complex.re_le_norm w)
  have hr : τ.re * ‖w‖ = w.re * ‖τ‖ := by
    have h1 : ‖τ‖ * (τ.re * ‖w‖) = ‖τ‖ * (w.re * ‖τ‖) := by
      calc
        ‖τ‖ * (τ.re * ‖w‖) = (‖w‖ * ‖τ‖) * τ.re := by ring
        _ = d * τ.re := by rw [hnid]
        _ = w.re * ‖τ‖ ^ 2 := hid.symm
        _ = _ := by ring
    exact mul_left_cancel₀ hρ.ne' h1
  have hnorm2 : ‖w‖ ^ 2 ≤ d * L / 2000 := by
    have h1 := h.hR.normSq_denom_le hax hx
    have h2 := h.hR.h1
    rw [le_div_iff₀ (by norm_num)]
    linarith only [h1, h2]
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hsdsq := Real.sq_sqrt hdR.le
  -- `1.8·10⁶ ‖w‖ ≤ L √d`.
  have hmain : 1800000 * ‖w‖ ≤ L * Real.sqrt d := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, hsdsq]
    have h1 : (1800000 : ℝ) ^ 2 * ‖w‖ ^ 2 ≤ 1800000 ^ 2 * (d * L / 2000) :=
      mul_le_mul_of_nonneg_left hnorm2 (by norm_num)
    have h2 : (2 * 10 ^ 9 : ℝ) ≤ L := by
      have : (2 * 10 ^ 9 : ℝ) ≤ 10 ^ 10 := by norm_num
      linarith only [this, hL1]
    have h3 : (d : ℝ) * L * (2 * 10 ^ 9) ≤ d * L * L :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith only [h1, h3]
  have hsqrt : Real.sqrt ((d : ℝ) / π ^ 2) = Real.sqrt d / π := by
    rw [Real.sqrt_div hdR.le, Real.sqrt_sq hπ.le]
  rw [hsqrt, div_le_iff₀ hr0]
  have hkey : 450 * ‖w‖ ≤ Real.sqrt d / π / 200 * w.re := by
    have h1 : Real.sqrt d / 4 ≤ Real.sqrt d / π :=
      div_le_div_of_nonneg_left hsd.le hπ hπ4.le
    have h2 : Real.sqrt d / 4 / 200 * (L / 5) ≤ Real.sqrt d / π / 200 * w.re := by
      apply mul_le_mul _ hB (by positivity) (by positivity)
      linarith only [h1]
    nlinarith only [h2, hmain]
  apply le_of_mul_le_mul_right _ hWpos
  calc
    450 * ‖τ‖ * ‖w‖ = (450 * ‖w‖) * ‖τ‖ := by ring
    _ ≤ (Real.sqrt d / π / 200 * w.re) * ‖τ‖ := mul_le_mul_of_nonneg_right hkey hρ.le
    _ = Real.sqrt d / π / 200 * (τ.re * ‖w‖) := by
      rw [hr]
      ring
    _ = _ := by ring

/-- **No root above the segment `[-X, X]`.** -/
theorem JensenLargeDegree.eval_ne_zero (h : JensenLargeDegree d) {z : ℂ} (ht : 0 < z.im)
    (hx : |z.re| ≤ saddleX d) : (jensenRev d xiSeries).eval z ≠ 0 := by
  have hd := h.hR.hd
  have hdR : (0 : ℝ) < d := h.hR.d_pos
  have hL1 : (10 : ℝ) ^ 10 ≤ Real.log d := h.hL
  have hLpos : 0 < Real.log d := by
    have h10 : (0 : ℝ) < 10 ^ 10 := by norm_num
    linarith only [hL1, h10]
  have hX10 := h.hX10
  have hC800 := saddleEdgeConstant_ge
  have hCpos : 0 < saddleEdgeConstant := by linarith only [hC800]
  have hz0 : z ≠ 0 := fun h0 => by
    rw [h0, zero_im] at ht
    exact lt_irrefl _ ht
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  by_cases hfar : (d : ℝ) ≤ (‖z‖ + Real.log d) * saddleEdgeConstant
  · -- `d/z` lies in the compact cone.
    have hC := h.hC
    have hbig : 4 * (saddleX d + Real.log d) ≤ ‖z‖ + Real.log d := by
      have h1 := hC.trans hfar
      have h2 : saddleEdgeConstant * (4 * (saddleX d + Real.log d)) ≤
          saddleEdgeConstant * (‖z‖ + Real.log d) := by
        calc _ = 4 * saddleEdgeConstant * (saddleX d + Real.log d) := by ring
          _ ≤ _ := h1
          _ = _ := by ring
      exact le_of_mul_le_mul_left h2 hCpos
    set u : ℂ := (d : ℂ) / z with hu
    have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    have hu0 : u ≠ 0 := div_ne_zero hdC hz0
    have hdu : (d : ℂ) / u = z := by
      rw [hu]
      field_simp
    have heval := eval_jensenRev_div xiCoeff hd hu0
    rw [mk_xiCoeff, hdu] at heval
    rw [heval]
    refine mul_ne_zero (pow_ne_zero _ hz0) (h.hΦ u ?_ ?_)
    · rw [hu, norm_div, Complex.norm_natCast, div_le_iff₀ hzn]
      have hLz : Real.log d ≤ ‖z‖ := by linarith only [hbig, hX10, hLpos]
      have h1 : (‖z‖ + Real.log d) * saddleEdgeConstant ≤ (2 * ‖z‖) * saddleEdgeConstant :=
        mul_le_mul_of_nonneg_right (by linarith only [hLz]) hCpos.le
      linarith only [h1, hfar]
    · have hre : u.re = d * z.re / Complex.normSq z := by
        rw [hu, Complex.div_re]
        simp only [natCast_re, natCast_im, zero_mul, zero_div, add_zero]
      have him : u.im = -(d * z.im / Complex.normSq z) := by
        rw [hu, Complex.div_im]
        simp only [natCast_re, natCast_im, zero_mul, zero_div, zero_sub]
      have hN : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
      rw [hre, him, abs_neg, abs_div, abs_div, abs_of_pos hN, abs_mul, abs_mul, abs_of_pos hdR,
        abs_of_pos ht]
      apply div_le_div_of_nonneg_right _ hN.le
      apply mul_le_mul_of_nonneg_left _ hdR.le
      have hsum := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos ht] at hsum
      linarith only [hsum, hbig, hx, hX10, hLpos]
  push Not at hfar
  by_cases hzA : ‖z‖ + Real.log d ≤ Real.exp (3 / 5 * Real.log d - 14)
  · obtain ⟨ax, hax, hfix⟩ := h.hR.exists_fixedPoint hx
    by_cases hnear : z.im * (saddleTau d ax z.re).re < 450
    · have hs : (gammaSlope (saddleTau d ax z.re) - I * z.re) * saddleTau d ax z.re = d := by
        rw [hfix]
        exact h.hR.saddle_identity hax
      have hA : 8000 ≤ (gammaSlope (saddleTau d ax z.re)).re := by
        rw [hfix]
        have h1 := hax.1
        have h2 := h.hR.L_ge
        linarith only [h1, h2]
      have hr := h.hR.re_tau_ge hax hx
      have hne := eval_ne_zero_of_near hd hs hA hr (K := 450) (by norm_num) (h.near_condition hx hax)
        ht hnear
      rwa [Complex.re_add_im] at hne
    · push Not at hnear
      exact h.caseA ht hx hzA hax hnear
  · push Not at hzA
    exact h.caseB ht hx hzA hfar

/-- **Every root below the saddle edge is real**, at every large degree. -/
theorem JensenLargeDegree.im_eq_zero_of_root (h : JensenLargeDegree d) {z : ℂ}
    (hx : |z.re| ≤ saddleX d) (h0 : (jensenRev d xiSeries).eval z = 0) : z.im = 0 := by
  have hconj : (jensenRev d xiSeries).eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((jensenRev d xiSeries).eval z) := by
    rw [eval_eq_jensenUpper_add_conj d _ one_pos, eval_eq_jensenUpper_add_conj d z one_pos,
      starRingEnd_self_apply, map_add, starRingEnd_self_apply]
    ring
  by_contra him
  rcases lt_or_gt_of_ne him with hneg | hpos
  · have ht : 0 < ((starRingEnd ℂ) z).im := by
      rw [Complex.conj_im]
      linarith only [hneg]
    refine h.eval_ne_zero ht (by rwa [Complex.conj_re]) ?_
    rw [hconj, h0, map_zero]
  · exact h.eval_ne_zero hpos hx h0

/-- All sufficiently large degrees qualify. -/
theorem eventually_jensenLargeDegree : ∀ᶠ d : ℕ in atTop, JensenLargeDegree d := by
  have hC800 := saddleEdgeConstant_ge
  have hCpos : 0 < saddleEdgeConstant := by linarith only [hC800]
  have hlogsmall := Real.isLittleO_log_id_atTop.def (show (0 : ℝ) < 1 / 20 by norm_num)
  filter_upwards [eventually_saddleRange,
    eventually_scaledJensen_ne_zero_on_cone (2 * saddleEdgeConstant),
    tendsto_log_natCast.eventually_ge_atTop ((10 : ℝ) ^ 10),
    eventually_ge_atTop 1000000,
    eventually_log_le_mul (show (0 : ℝ) < 1 / (64 * saddleEdgeConstant ^ 2) by positivity),
    tendsto_log_natCast.eventually hlogsmall] with d hS hΦ hL hd1 hlog hloglog
  obtain ⟨hR, hX10⟩ := hS
  have hdR : (0 : ℝ) < d := hR.d_pos
  set L := Real.log (d : ℝ) with hLdef
  have hLpos : 0 < L := by
    have h10 : (0 : ℝ) < 10 ^ 10 := by norm_num
    linarith only [hL, h10]
  have hd6 : (1000000 : ℝ) ≤ d := by exact_mod_cast hd1
  have hdL : 0 ≤ (d : ℝ) * L := by positivity
  have hXsq : saddleX d ^ 2 = d * L / 10000 := by
    rw [saddleX, div_pow, Real.sq_sqrt hdL]
    norm_num
  have hX0 : 0 ≤ saddleX d := by
    rw [saddleX]
    positivity
  refine ⟨hR, hX10, hL, ?_, ?_, ?_, hΦ⟩
  · rw [Real.le_sqrt' (by norm_num)]
    linarith only [hd6]
  · -- `4(X + 5 + L) ≤ e^{3L/5 − 14}`.
    have hexpL : Real.exp L = d := Real.exp_log hdR
    have hsq2 : Real.sqrt (d : ℝ) = Real.exp (L / 2) := by
      rw [Real.sqrt_eq_rpow, ← hexpL, ← Real.exp_mul]
      congr 1
      ring
    have hL1 : 1 ≤ L := by
      have h10 : (1 : ℝ) ≤ 10 ^ 10 := by norm_num
      linarith only [hL, h10]
    have hsL : Real.sqrt L ≤ L := by
      rw [Real.sqrt_le_left hLpos.le]
      nlinarith only [hL1]
    have hXle : saddleX d ≤ Real.exp (L / 2) * L := by
      rw [saddleX, Real.sqrt_mul hdR.le, hsq2]
      have h1 := Real.exp_pos (L / 2)
      have h2 : Real.exp (L / 2) * Real.sqrt L ≤ Real.exp (L / 2) * L :=
        mul_le_mul_of_nonneg_left hsL h1.le
      have h3 : 0 ≤ Real.exp (L / 2) * Real.sqrt L := by positivity
      linarith only [h2, h3]
    have hE1 : 1 ≤ Real.exp (L / 2) := Real.one_le_exp (by positivity)
    have hsum : 4 * (saddleX d + 5 + L) ≤ 40 * L * Real.exp (L / 2) := by
      have h1 : 5 + L ≤ 6 * L * Real.exp (L / 2) := by nlinarith only [hL1, hE1]
      nlinarith only [hXle, h1, hE1, hL1]
    have hlog2 : Real.log L ≤ L / 20 := by
      have hh := hloglog
      simp only [id, Real.norm_eq_abs, abs_of_pos hLpos] at hh
      have h1 := (le_abs_self _).trans hh
      linarith only [h1]
    have hbig : 40 * L ≤ Real.exp (L / 10 - 14) := by
      rw [← Real.log_le_iff_le_exp (by positivity), Real.log_mul (by norm_num) hLpos.ne']
      have h40 : Real.log 40 ≤ 40 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
      have h1000 : (2000 : ℝ) ≤ L := by
        have : (2000 : ℝ) ≤ 10 ^ 10 := by norm_num
        linarith only [this, hL]
      linarith only [hlog2, h40, h1000]
    calc
      _ ≤ 40 * L * Real.exp (L / 2) := hsum
      _ ≤ Real.exp (L / 10 - 14) * Real.exp (L / 2) :=
        mul_le_mul_of_nonneg_right hbig (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
  · -- `4C(X + L) ≤ d`.
    set C := saddleEdgeConstant with hC
    have hlog' : L * (64 * C ^ 2) ≤ d := by
      have h1 := (le_div_iff₀ (by positivity : 0 < 64 * C ^ 2)).mp
        (show L ≤ (d : ℝ) / (64 * C ^ 2) by
          rw [div_eq_mul_inv, mul_comm, ← one_div]
          exact hlog)
      exact h1
    have hLC : L * (8 * C) ≤ d := by
      have h1 : L * (8 * C) ≤ L * (64 * C ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hC800]) hLpos.le
      linarith only [h1, hlog']
    have hXC : saddleX d * (8 * C) ≤ d := by
      apply (sq_le_sq₀ (by positivity) hdR.le).mp
      rw [mul_pow, hXsq]
      have h2 : (d : ℝ) * (L * (64 * C ^ 2)) ≤ d * d := mul_le_mul_of_nonneg_left hlog' hdR.le
      nlinarith only [h2, hdL, sq_nonneg C, mul_nonneg hdL (sq_nonneg C)]
    nlinarith only [hLC, hXC]

/-- **Every root of `R_d(Ξ)` with `|Re z| ≤ √(d log d)/100` is real, for all large `d`.** -/
theorem eventually_im_eq_zero_of_root :
    ∀ᶠ d : ℕ in atTop, ∀ z : ℂ, |z.re| ≤ saddleX d → (jensenRev d xiSeries).eval z = 0 → z.im = 0 := by
  filter_upwards [eventually_jensenLargeDegree] with d hd z hx h0
  exact hd.im_eq_zero_of_root hx h0

/-- **The height law.** For all large `d`, every non-real zero `u` of `Φ_d` has
`|Re u| · √(d log d)/100 < d`, that is `|Re u| < 100 √(d/log d)`. -/
theorem eventually_abs_re_mul_lt_of_scaledJensen_eq_zero :
    ∀ᶠ d : ℕ in atTop, ∀ u : ℂ, u.im ≠ 0 → scaledJensen xiCoeff d u = 0 → |u.re| * saddleX d < d := by
  filter_upwards [eventually_jensenLargeDegree] with d hd u him h0
  have hd0 := hd.hR.hd
  have hdR : (0 : ℝ) < d := hd.hR.d_pos
  have hu0 : u ≠ 0 := fun h => him (by rw [h, zero_im])
  have heval := eval_jensenRev_div xiCoeff hd0 hu0
  rw [mk_xiCoeff, h0, mul_zero] at heval
  have hN : 0 < Complex.normSq u := Complex.normSq_pos.2 hu0
  have hzim : ((d : ℂ) / u).im ≠ 0 := by
    rw [Complex.div_im]
    simp only [natCast_re, natCast_im, zero_mul, zero_div, zero_sub]
    exact neg_ne_zero.2 (div_ne_zero (mul_ne_zero hdR.ne' him) hN.ne')
  have hzre : ((d : ℂ) / u).re = d * u.re / Complex.normSq u := by
    rw [Complex.div_re]
    simp only [natCast_re, natCast_im, zero_mul, zero_div, add_zero]
  have hgt : saddleX d < |((d : ℂ) / u).re| := by
    by_contra hle
    exact hzim (hd.im_eq_zero_of_root (not_lt.1 hle) heval)
  rw [hzre, abs_div, abs_mul, abs_of_pos hdR, abs_of_pos hN, lt_div_iff₀ hN] at hgt
  have hre2 : |u.re| ^ 2 ≤ Complex.normSq u := by
    rw [sq_abs, Complex.normSq_apply]
    nlinarith only [mul_self_nonneg u.im, sq_nonneg u.re]
  have hX0 : 0 ≤ saddleX d := (by norm_num : (0 : ℝ) ≤ 10).trans hd.hX10
  rcases (abs_nonneg u.re).eq_or_lt with hz | hpos
  · rw [← hz, zero_mul]
    exact hdR
  · have h1 : saddleX d * |u.re| ^ 2 ≤ saddleX d * Complex.normSq u :=
      mul_le_mul_of_nonneg_left hre2 hX0
    have h2 : (|u.re| * saddleX d) * |u.re| < d * |u.re| := by nlinarith only [h1, hgt]
    exact lt_of_mul_lt_mul_right h2 hpos.le

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.exists_complex_saddle
#print axioms FiniteFreeProbability.eventually_im_eq_zero_of_root
#print axioms FiniteFreeProbability.eventually_abs_re_mul_lt_of_scaledJensen_eq_zero
