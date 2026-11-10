import GaloisForLFunctions.ExceptionalLayerTheory.GaussianDampingErrorAnalytic
import GaloisForLFunctions.ExceptionalLayerTheory.HolomorphicDampingFilters

/-!
# The filtered centred Vaughan error

The actual arithmetic error is holomorphic in logarithmic damping on a
half-strip of width proportional to the reciprocal height. Its unfiltered
scale bound and Cauchy cancellation retain every spacing factor in a
polynomial filter, uniformly in quadratic Vaughan cutoffs.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem small_damping_rotation {α ξ t y : ℝ}
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hy : t * |y| ≤ 1 / 16) :
    let q := ((α : ℂ) - ξ * I) * Complex.exp (I * ((-2 * y : ℝ) : ℂ))
    0 < q.re ∧ α / 2 ≤ q.re ∧ q.re ≤ 2 * α ∧
      q.re ≤ -q.im ∧ -q.im ≤ 2 * q.re * t := by
  have ht0 : 0 < t := by linarith only [ht]
  let ε : ℂ := (α : ℂ) - ξ * I
  let q := ε * Complex.exp (I * ((-2 * y : ℝ) : ℂ))
  have hξ : 0 ≤ ξ := by linarith only [hα, hlo]
  have hε : ‖ε‖ ≤ 2 * α * t := by
    calc
      _ ≤ ‖(α : ℂ)‖ + ‖(ξ : ℂ) * I‖ := norm_sub_le _ _
      _ = α + ξ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hα.le, abs_of_nonneg hξ, Complex.norm_I, mul_one]
      _ ≤ 2 * α * t := by nlinarith only [ht, hα, hhi]
  have hchord : ‖Complex.exp (I * ((-2 * y : ℝ) : ℂ)) - 1‖ ≤ 2 * |y| := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2 * y))
  have hdiff : ‖q - ε‖ ≤ α / 4 := by
    have he : q - ε = ε * (Complex.exp (I * ((-2 * y : ℝ) : ℂ)) - 1) := by
      dsimp only [q]; ring
    rw [he, norm_mul]
    calc
      _ ≤ (2 * α * t) * (2 * |y|) :=
        mul_le_mul hε hchord (norm_nonneg _) (by positivity)
      _ ≤ α / 4 := by nlinarith only [mul_le_mul_of_nonneg_left hy hα.le]
  have hre := (Complex.abs_re_le_norm (q - ε)).trans hdiff
  have him := (Complex.abs_im_le_norm (q - ε)).trans hdiff
  have heR : ε.re = α := by simp [ε]
  have heI : ε.im = -ξ := by simp [ε]
  rw [Complex.sub_re, heR] at hre
  rw [Complex.sub_im, heI] at him
  obtain ⟨hrl, hru⟩ := abs_le.mp hre
  obtain ⟨hil, hiu⟩ := abs_le.mp him
  have hq : 0 < q.re := by linarith only [hrl, hα]
  change 0 < q.re ∧ α / 2 ≤ q.re ∧ q.re ≤ 2 * α ∧ q.re ≤ -q.im ∧ -q.im ≤ 2 * q.re * t
  refine ⟨hq, ?_, ?_, ?_, ?_⟩
  · linarith only [hrl, hα]
  · linarith only [hru, hα]
  · linarith only [hru, hiu, hlo, hα]
  · have hh := mul_le_mul_of_nonneg_right hrl (show 0 ≤ t by linarith only [ht])
    nlinarith only [hh, hil, hhi, hα, mul_le_mul_of_nonneg_left ht hα.le]

private theorem damping_exp_split (ε z : ℂ) :
    ε * Complex.exp (-2 * z) = (Real.exp (-2 * z.re) : ℂ) *
      (ε * Complex.exp (I * ((-2 * z.im : ℝ) : ℂ))) := by
  have he : -2 * z = ((-2 * z.re : ℝ) : ℂ) + I * ((-2 * z.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [he, Complex.exp_add, ← Complex.ofReal_exp]
  ring

/-- A narrow logarithmic damping rotation preserves the arithmetic sector and
changes the physical scale by at most a fixed factor after real dilation. -/
theorem exists_damping_rotated_scale {α ξ t X : ℝ} {z : ℂ}
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hz : t * |z.im| ≤ 1 / 16) (hX : 0 < X) (hscale : α * X ^ 2 = 2) :
    let ε' := ((α : ℂ) - ξ * I) * Complex.exp (-2 * z)
    0 < ε'.re ∧ ε'.re ≤ -ε'.im ∧ -ε'.im ≤ 2 * ε'.re * t ∧
    ∃ Y : ℝ, 0 < Y ∧ ε'.re * Y ^ 2 = 2 ∧ X * Real.exp z.re / 2 ≤ Y := by
  let q := ((α : ℂ) - ξ * I) * Complex.exp (I * ((-2 * z.im : ℝ) : ℂ))
  obtain ⟨hq, hqlo, hqhi, hqξ, hqξt⟩ := small_damping_rotation hα ht hlo hhi hz
  change 0 < q.re at hq
  change α / 2 ≤ q.re at hqlo
  change q.re ≤ 2 * α at hqhi
  change q.re ≤ -q.im at hqξ
  change -q.im ≤ 2 * q.re * t at hqξt
  let ℓ := Real.sqrt (α / q.re)
  have hℓ0 : 0 ≤ ℓ := Real.sqrt_nonneg _
  have hℓ2 : ℓ ^ 2 = α / q.re := Real.sq_sqrt (div_nonneg hα.le hq.le)
  have hratio : 1 / 2 ≤ α / q.re := (le_div_iff₀ hq).mpr (by linarith only [hqhi])
  have hℓ : 1 / 2 ≤ ℓ := by nlinarith only [hℓ2, hratio, hℓ0]
  have hℓscale : q.re * ℓ ^ 2 = α := by rw [hℓ2]; field_simp [hq.ne']
  let Y := X * Real.exp z.re * ℓ
  have hY : 0 < Y := mul_pos (mul_pos hX (Real.exp_pos _)) (by linarith only [hℓ])
  have hYlo : X * Real.exp z.re / 2 ≤ Y := by
    have hh := mul_le_mul_of_nonneg_left hℓ (mul_nonneg hX.le (Real.exp_pos z.re).le)
    simpa only [Y, mul_one_div] using hh
  dsimp only
  rw [damping_exp_split]
  have heR : ((Real.exp (-2 * z.re) : ℂ) * q).re = Real.exp (-2 * z.re) * q.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have heI : ((Real.exp (-2 * z.re) : ℂ) * q).im = Real.exp (-2 * z.re) * q.im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  change 0 < ((Real.exp (-2 * z.re) : ℂ) * q).re ∧ _
  rw [heR, heI]
  refine ⟨mul_pos (Real.exp_pos _) hq, ?_, ?_, Y, hY, ?_, hYlo⟩
  · nlinarith only [mul_le_mul_of_nonneg_left hqξ (Real.exp_pos (-2 * z.re)).le]
  · nlinarith only [mul_le_mul_of_nonneg_left hqξt (Real.exp_pos (-2 * z.re)).le]
  · have he : Real.exp (-2 * z.re) * (Real.exp z.re) ^ 2 = 1 := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    calc
      _ = (Real.exp (-2 * z.re) * (Real.exp z.re) ^ 2) * (q.re * ℓ ^ 2) * X ^ 2 := by
        dsimp only [Y]; ring
      _ = 2 := by rw [he, hℓscale, one_mul, hscale]

/-- The Mellin twist of the actual centred arithmetic error. -/
def twistedGaussianCentredVaughanError (σ β t : ℝ) (U V : ℕ) (ε z : ℂ) : ℂ :=
  Complex.exp ((((σ : ℂ) + t * I) - β) * z) *
    gaussianCentredVaughanError σ t U V (ε * Complex.exp (-2 * z))

private theorem error_halfStrip_bounds {σ β α ξ t X : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hβ : σ ≤ β)
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hX : 0 < X) (hscale : α * X ^ 2 = 2) (hTX : 2 * Real.exp 1 * t ^ 8 ≤ X)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUt : (U : ℝ) ≤ t ^ 2) (hVt : (V : ℝ) ≤ t ^ 2) :
    let r := 1 / (16 * t)
    let f := twistedGaussianCentredVaughanError σ β t U V ((α : ℂ) - ξ * I)
    DifferentiableOn ℂ f (dampingHalfStrip r) ∧
    ∀ z ∈ dampingHalfStrip r, ‖f z‖ ≤
      (2 * Real.exp (β + 2 - σ) *
        (8 * gaussianSecondMomentLatticeConstant σ + 3 * gaussianLogSecondMomentConstant σ + 8)) * t ^ 7 / X := by
  let r := 1 / (16 * t)
  let ε : ℂ := (α : ℂ) - ξ * I
  let K := 8 * gaussianSecondMomentLatticeConstant σ + 3 * gaussianLogSecondMomentConstant σ + 8
  have ht0 : 0 < t := by linarith only [ht]
  have hr1 : r ≤ 1 := by dsimp only [r]; apply (div_le_iff₀ (by positivity)).mpr; linarith only [ht]
  have htr : t * r = 1 / 16 := by dsimp only [r]; field_simp [ht0.ne']
  have hK : 0 ≤ K := by
    have hD := gaussianSecondMomentLatticeConstant_nonneg hσ1
    have hL := gaussianLogSecondMomentConstant_nonneg hσ1
    dsimp only [K]
    positivity
  have hgeom (z : ℂ) (hz : z ∈ dampingHalfStrip r) :
      0 < (ε * Complex.exp (-2 * z)).re ∧
      (ε * Complex.exp (-2 * z)).re ≤ -(ε * Complex.exp (-2 * z)).im ∧
      -(ε * Complex.exp (-2 * z)).im ≤ 2 * (ε * Complex.exp (-2 * z)).re * t ∧
      ∃ Y : ℝ, 0 < Y ∧ (ε * Complex.exp (-2 * z)).re * Y ^ 2 = 2 ∧
        X * Real.exp z.re / 2 ≤ Y := by
    apply exists_damping_rotated_scale hα ht hlo hhi _ hX hscale
    exact (mul_le_mul_of_nonneg_left hz.2.le ht0.le).trans_eq htr
  refine ⟨?_, ?_⟩
  · intro z hz
    have hd := differentiableAt_gaussianCentredVaughanError
      (by linarith only [hσ]) (by linarith only [hσ1]) t U V (hgeom z hz).1
    have he : DifferentiableAt ℂ (fun w : ℂ => ε * Complex.exp (-2 * w)) z := by fun_prop
    have hw : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((((σ : ℂ) + t * I) - β) * w)) z := by fun_prop
    exact (hw.mul (hd.comp z he)).differentiableWithinAt
  · intro z hz
    obtain ⟨hε, hεξ, hεξt, Y, hY, hscaleY, hYlo⟩ := hgeom z hz
    have hx : -1 ≤ z.re := by linarith only [hz.1, hr1]
    have hex : 1 ≤ Real.exp 1 * Real.exp z.re := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith only [hx])
    have hTY : t ^ 8 ≤ Y := by
      calc
        _ ≤ (Real.exp 1 * Real.exp z.re) * t ^ 8 := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hex (by positivity : 0 ≤ t ^ 8)
        _ ≤ X * Real.exp z.re / 2 := by
          have hh := mul_le_mul_of_nonneg_right hTX (Real.exp_pos z.re).le
          nlinarith only [hh]
        _ ≤ Y := hYlo
    have heR : (((ε * Complex.exp (-2 * z)).re : ℝ) : ℂ) -
        (-(ε * Complex.exp (-2 * z)).im : ℝ) * I = ε * Complex.exp (-2 * z) := by
      apply Complex.ext <;> simp
    have hE : ‖gaussianCentredVaughanError σ t U V (ε * Complex.exp (-2 * z))‖ ≤ K * t ^ 7 / Y := by
      have hh := norm_gaussianPrimeMoment_sub_centredVaughan_le_scale
        hσ hσ1 hε hεξ (by linarith only [ht]) hεξt hscaleY hTY hU hV hUt hVt
      simpa only [gaussianCentredVaughanError, heR, K] using hh
    have hE' : ‖gaussianCentredVaughanError σ t U V (ε * Complex.exp (-2 * z))‖ ≤
        2 * K * t ^ 7 / (X * Real.exp z.re) := by
      calc
        _ ≤ K * t ^ 7 / Y := hE
        _ ≤ K * t ^ 7 / (X * Real.exp z.re / 2) :=
          div_le_div_of_nonneg_left (mul_nonneg hK (by positivity)) (by positivity) hYlo
        _ = _ := by ring
    have hphase : ((((σ : ℂ) + t * I) - β) * z).re = (σ - β) * z.re - t * z.im := by simp
    have hphaseBound : (σ - β) * z.re - t * z.im - z.re ≤ β + 2 - σ := by
      have hx' := mul_le_mul_of_nonneg_left (show -z.re ≤ 1 by linarith only [hx])
        (show 0 ≤ β + 1 - σ by linarith only [hβ])
      have hy' := mul_le_mul_of_nonneg_left (neg_le_abs z.im) ht0.le
      have hy'' := (mul_le_mul_of_nonneg_left hz.2.le ht0.le).trans_eq htr
      nlinarith only [hx', hy', hy'']
    dsimp only [twistedGaussianCentredVaughanError]
    rw [norm_mul, Complex.norm_exp, hphase]
    calc
      _ ≤ Real.exp ((σ - β) * z.re - t * z.im) * (2 * K * t ^ 7 / (X * Real.exp z.re)) :=
        mul_le_mul_of_nonneg_left hE' (Real.exp_pos _).le
      _ = (2 * K * t ^ 7 / X) * Real.exp ((σ - β) * z.re - t * z.im - z.re) := by
        rw [sub_eq_add_neg ((σ - β) * z.re - t * z.im), Real.exp_add, Real.exp_neg]
        ring
      _ ≤ (2 * K * t ^ 7 / X) * Real.exp (β + 2 - σ) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphaseBound) (by positivity)
      _ = _ := by dsimp only [K]; ring

/-- The literal polynomial filter of the actual centred Vaughan error keeps
all spacing factors. The constant is independent of spacing and cutoffs. -/
theorem norm_filtered_gaussianCentredVaughanError_le_scale {σ β α ξ t X h : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hβ : σ ≤ β)
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hX : 0 < X) (hscale : α * X ^ 2 = 2) (hTX : 2 * Real.exp 1 * t ^ 8 ≤ X)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUt : (U : ℝ) ≤ t ^ 2) (hVt : (V : ℝ) ≤ t ^ 2)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ws : List ℂ) :
    ‖∑ j ∈ Finset.range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
      (Complex.exp ((((σ : ℂ) + t * I) - β) * ((j : ℂ) * h)) *
        gaussianCentredVaughanError σ t U V
          (((α : ℂ) - ξ * I) * Complex.exp (-2 * ((j : ℂ) * h))))‖ ≤
    (2 * Real.exp (β + 2 - σ) *
      (8 * gaussianSecondMomentLatticeConstant σ + 3 * gaussianLogSecondMomentConstant σ + 8) *
      (16 : ℝ) ^ ws.length * dampingFilterCost ws) * h ^ ws.length * t ^ (ws.length + 7) / X := by
  have ht0 : 0 < t := by linarith only [ht]
  have hr : 0 < 1 / (16 * t) := by positivity
  have hr1 : 1 / (16 * t) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [ht]
  let K := 8 * gaussianSecondMomentLatticeConstant σ + 3 * gaussianLogSecondMomentConstant σ + 8
  let M := (2 * Real.exp (β + 2 - σ) * K) * t ^ 7 / X
  have hM : 0 ≤ M := by
    have hD := gaussianSecondMomentLatticeConstant_nonneg hσ1
    have hL := gaussianLogSecondMomentConstant_nonneg hσ1
    dsimp only [M, K]
    positivity
  obtain ⟨hf, hb⟩ := error_halfStrip_bounds hσ hσ1 hβ hα ht hlo hhi hX hscale hTX hU hV hUt hVt
  have H := norm_dampingFilterPolynomial_sum_le hr hr1 hM hh hh1 ws hf hb
  change ‖∑ j ∈ Finset.range ((dampingFilterPolynomial h ws).natDegree + 1),
    (dampingFilterPolynomial h ws).coeff j *
      twistedGaussianCentredVaughanError σ β t U V ((α : ℂ) - ξ * I) ((j : ℂ) * h)‖ ≤ _
  calc
    _ ≤ M * (h / (1 / (16 * t))) ^ ws.length * dampingFilterCost ws := H
    _ = _ := by
      dsimp only [M, K]
      have he : h / (1 / (16 * t)) = h * (16 * t) := by field_simp [ht0.ne']
      rw [he, mul_pow, mul_pow, pow_add]
      ring

#print axioms exists_damping_rotated_scale
#print axioms norm_filtered_gaussianCentredVaughanError_le_scale

/-- Above the degree-adjusted polynomial scale, the actual filtered arithmetic
reduction has error at most a constant times `h^d/t`, even as `h` contracts. -/
theorem norm_filtered_gaussianCentredVaughanError_le_inv {σ β α ξ t X h : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hβ : σ ≤ β)
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hscale : α * X ^ 2 = 2) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUt : (U : ℝ) ≤ t ^ 2) (hVt : (V : ℝ) ≤ t ^ 2)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ws : List ℂ)
    (hTX : 2 * Real.exp 1 * t ^ (ws.length + 8) ≤ X) :
    ‖∑ j ∈ Finset.range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
      (Complex.exp ((((σ : ℂ) + t * I) - β) * ((j : ℂ) * h)) *
        gaussianCentredVaughanError σ t U V
          (((α : ℂ) - ξ * I) * Complex.exp (-2 * ((j : ℂ) * h))))‖ ≤
    (2 * Real.exp (β + 2 - σ) *
      (8 * gaussianSecondMomentLatticeConstant σ + 3 * gaussianLogSecondMomentConstant σ + 8) *
      (16 : ℝ) ^ ws.length * dampingFilterCost ws) * h ^ ws.length / t := by
  have ht0 : 0 < t := by linarith only [ht]
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hc : 1 ≤ 2 * Real.exp 1 := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    linarith only [he]
  have hX : 0 < X := (by positivity : 0 < 2 * Real.exp 1 * t ^ (ws.length + 8)).trans_le hTX
  have hTX8 : 2 * Real.exp 1 * t ^ 8 ≤ X :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega : 8 ≤ ws.length + 8)) (by positivity)).trans hTX
  have hTXd : t ^ (ws.length + 8) ≤ X := by
    calc
      _ ≤ 2 * Real.exp 1 * t ^ (ws.length + 8) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ t ^ (ws.length + 8))
      _ ≤ X := hTX
  let C := 2 * Real.exp (β + 2 - σ) *
      (8 * gaussianSecondMomentLatticeConstant σ + 3 * gaussianLogSecondMomentConstant σ + 8) *
      (16 : ℝ) ^ ws.length * dampingFilterCost ws
  have hC : 0 ≤ C := by
    have hD := gaussianSecondMomentLatticeConstant_nonneg hσ1
    have hL := gaussianLogSecondMomentConstant_nonneg hσ1
    have hF := dampingFilterCost_nonneg ws
    dsimp only [C]
    positivity
  apply (norm_filtered_gaussianCentredVaughanError_le_scale
    hσ hσ1 hβ hα ht hlo hhi hX hscale hTX8 hU hV hUt hVt hh hh1 ws).trans
  change C * h ^ ws.length * t ^ (ws.length + 7) / X ≤ C * h ^ ws.length / t
  apply (div_le_div_iff₀ hX ht0).mpr
  calc
    _ = (C * h ^ ws.length) * t ^ (ws.length + 8) := by
      rw [show ws.length + 8 = (ws.length + 7) + 1 by omega, pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hTXd (mul_nonneg hC (pow_nonneg hh _))

#print axioms norm_filtered_gaussianCentredVaughanError_le_inv

private theorem dampingSampleWeight_eq_log_twist (β h : ℝ) (s : ℂ) (j : ℕ) :
    dampingSampleWeight β h s j = Complex.exp ((s - β) * ((j : ℂ) * h)) := by
  unfold dampingSampleWeight
  congr 1
  ring

private theorem complexGaussianDamping_geometric_shift (a h φ t : ℝ) (j : ℕ) :
    complexGaussianDamping (geometricGaussianDamping a h t j) φ =
      complexGaussianDamping (Real.exp (-a * t)) φ * Complex.exp (-2 * ((j : ℂ) * h)) := by
  unfold complexGaussianDamping geometricGaussianDamping
  rw [Real.log_exp, Real.log_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The logarithmic damping samples are exactly the existing rotated prime
filter minus the filtered continuum and centred arithmetic current. -/
theorem rotatedPrimeMomentFilter_sub_centredVaughan_eq (P : Polynomial ℂ)
    (σ β a h φ t : ℝ) (U V : ℕ) :
    rotatedPrimeMomentFilter P σ β a h φ t -
      (∑ j ∈ Finset.range (P.natDegree + 1),
        P.coeff j * dampingSampleWeight β h ((σ : ℂ) + t * I) j *
          (gaussianFirstMomentPole ((σ : ℂ) + t * I)
            (complexGaussianDamping (geometricGaussianDamping a h t j) φ) t +
            gaussianCentredVaughanCurrent σ
              (complexGaussianDamping (geometricGaussianDamping a h t j) φ).re
              (-(complexGaussianDamping (geometricGaussianDamping a h t j) φ).im) t U V)) =
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j *
        twistedGaussianCentredVaughanError σ β t U V
          (complexGaussianDamping (Real.exp (-a * t)) φ) ((j : ℂ) * h) := by
  unfold rotatedPrimeMomentFilter
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [dampingSampleWeight_eq_log_twist, twistedGaussianCentredVaughanError,
    ← complexGaussianDamping_geometric_shift, gaussianCentredVaughanError,
    rotatedGaussianMomentPrimeSum_eq_arithmetic]
  ring

/-- The spacing-preserving error estimate applies to the literal rotated
prime filter and its actual centred Vaughan approximation. -/
theorem norm_rotatedPrimeMomentFilter_sub_centredVaughan_le_scale
    {σ β a h φ t X : ℝ} (ws : List ℂ) (U V : ℕ)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hβ : σ ≤ β)
    (ht : 4 ≤ t) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hα : 0 < (complexGaussianDamping (Real.exp (-a * t)) φ).re)
    (hlo : 2 * (complexGaussianDamping (Real.exp (-a * t)) φ).re ≤
      -(complexGaussianDamping (Real.exp (-a * t)) φ).im)
    (hhi : -(complexGaussianDamping (Real.exp (-a * t)) φ).im ≤
      (complexGaussianDamping (Real.exp (-a * t)) φ).re * t)
    (hX : 0 < X) (hscale : (complexGaussianDamping (Real.exp (-a * t)) φ).re * X ^ 2 = 2)
    (hTX : 2 * Real.exp 1 * t ^ 8 ≤ X)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUt : (U : ℝ) ≤ t ^ 2) (hVt : (V : ℝ) ≤ t ^ 2) :
    ‖rotatedPrimeMomentFilter (dampingFilterPolynomial h ws) σ β a h φ t -
      (∑ j ∈ Finset.range ((dampingFilterPolynomial h ws).natDegree + 1),
        (dampingFilterPolynomial h ws).coeff j * dampingSampleWeight β h ((σ : ℂ) + t * I) j *
          (gaussianFirstMomentPole ((σ : ℂ) + t * I)
            (complexGaussianDamping (geometricGaussianDamping a h t j) φ) t +
            gaussianCentredVaughanCurrent σ
              (complexGaussianDamping (geometricGaussianDamping a h t j) φ).re
              (-(complexGaussianDamping (geometricGaussianDamping a h t j) φ).im) t U V))‖ ≤
    (2 * Real.exp (β + 2 - σ) *
      (8 * gaussianSecondMomentLatticeConstant σ + 3 * gaussianLogSecondMomentConstant σ + 8) *
      (16 : ℝ) ^ ws.length * dampingFilterCost ws) * h ^ ws.length * t ^ (ws.length + 7) / X := by
  rw [rotatedPrimeMomentFilter_sub_centredVaughan_eq]
  have he : (((complexGaussianDamping (Real.exp (-a * t)) φ).re : ℝ) : ℂ) -
      (-(complexGaussianDamping (Real.exp (-a * t)) φ).im : ℝ) * I =
        complexGaussianDamping (Real.exp (-a * t)) φ := by
    apply Complex.ext <;> simp
  have H := norm_filtered_gaussianCentredVaughanError_le_scale
    hσ hσ1 hβ hα ht hlo hhi hX hscale hTX hU hV hUt hVt hh hh1 ws
  simpa only [he, twistedGaussianCentredVaughanError] using H

#print axioms rotatedPrimeMomentFilter_sub_centredVaughan_eq
#print axioms norm_rotatedPrimeMomentFilter_sub_centredVaughan_le_scale

end GaloisForLFunctions.ExceptionalLayerTheory
