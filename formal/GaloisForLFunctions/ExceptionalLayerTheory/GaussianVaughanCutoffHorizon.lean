import GaloisForLFunctions.ExceptionalLayerTheory.GaussianFilteredCentredVaughanError

/-!
# Power-sized Vaughan cutoffs

The centred arithmetic error is controlled by the product of the two
cutoffs. Absorbing the logarithm and retaining the filter spacing allows
power-sized unbalanced cutoffs at long Gaussian observation scales.
-/

open Complex Finset RHTower ArithmeticFunction
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The continuum-error constant for unrestricted product cutoffs. -/
def gaussianVaughanProductConstant (σ : ℝ) : ℝ :=
  8 + 2 * gaussianSecondMomentLatticeConstant σ + gaussianLogSecondMomentConstant σ

theorem gaussianVaughanProductConstant_nonneg {σ : ℝ} (hσ : σ < 1) :
    0 ≤ gaussianVaughanProductConstant σ := by
  have hD := gaussianSecondMomentLatticeConstant_nonneg hσ
  have hC := gaussianLogSecondMomentConstant_nonneg hσ
  unfold gaussianVaughanProductConstant
  positivity

/-- The complete centred error depends on the product cutoff, without an
individual polynomial-height restriction on either Vaughan cutoff. -/
theorem norm_gaussianCentredVaughanError_le_product {σ α ξ t X : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 < α) (hαξ : α ≤ ξ)
    (ht : 2 ≤ t) (hξ : ξ ≤ 2 * α * t) (hscale : α * X ^ 2 = 2)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : ((U * V : ℕ) : ℝ) ≤ X) :
    ‖gaussianCentredVaughanError σ t U V ((α : ℂ) - ξ * I)‖ ≤
      gaussianVaughanProductConstant σ * t ^ 2 * ((U * V : ℕ) : ℝ) ^ 2 *
        X ^ (-1 - σ) * (1 + Real.log X) := by
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hK1 : (1 : ℝ) ≤ ((U * V : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hU hV
  have hUK : (U : ℝ) ≤ ((U * V : ℕ) : ℝ) := by
    push_cast
    nlinarith only [hU1, hV1]
  have hVK : (V : ℝ) ≤ ((U * V : ℕ) : ℝ) := by
    push_cast
    nlinarith only [hU1, hV1]
  have hX1 := hK1.trans hUV
  have hX : 0 < X := zero_lt_one.trans_le hX1
  have hUX := hUK.trans hUV
  have hVX := hVK.trans hUV
  have hlogX := Real.log_nonneg hX1
  have ht2 : 1 ≤ t ^ 2 := by nlinarith only [ht]
  have hup : (U : ℝ) ^ (1 - σ) ≤ X ^ (1 - σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg U) hUX (by linarith only [hσ1])
  have hlogU := Real.log_le_log (zero_lt_one.trans_le hU1) hUX
  have hlogK := Real.log_le_log (zero_lt_one.trans_le hK1) hUV
  have hpower : X ^ (1 - σ) = X ^ 2 * X ^ (-1 - σ) := by
    rw [← Real.rpow_two, ← Real.rpow_add hX]
    congr 1
    ring
  have hhead : 4 * α * (U : ℝ) ^ 2 * (U : ℝ) ^ (1 - σ) * Real.log U ≤
      8 * t ^ 2 * ((U * V : ℕ) : ℝ) ^ 2 * X ^ (-1 - σ) * (1 + Real.log X) := by
    calc
      _ ≤ 4 * α * ((U * V : ℕ) : ℝ) ^ 2 * X ^ (1 - σ) * Real.log X := by gcongr
      _ = 8 * ((U * V : ℕ) : ℝ) ^ 2 * X ^ (-1 - σ) * Real.log X := by
        rw [hpower]
        linear_combination 4 * ((U * V : ℕ) : ℝ) ^ 2 * X ^ (-1 - σ) * Real.log X * hscale
      _ ≤ 8 * t ^ 2 * ((U * V : ℕ) : ℝ) ^ 2 * X ^ (-1 - σ) * (1 + Real.log X) := by
        calc
          _ = 8 * 1 * ((U * V : ℕ) : ℝ) ^ 2 * X ^ (-1 - σ) * Real.log X := by ring
          _ ≤ _ := by gcongr; linarith only [hlogX]
  have hD := gaussianSecondMomentLatticeConstant_nonneg hσ1
  have hC := gaussianLogSecondMomentConstant_nonneg hσ1
  have hfirst : 2 * gaussianSecondMomentLatticeConstant σ * t ^ 2 * X ^ (-1 - σ) *
      ((U * V : ℕ) : ℝ) ^ 2 * Real.log ((U * V : ℕ) : ℝ) ≤
      2 * gaussianSecondMomentLatticeConstant σ * t ^ 2 * ((U * V : ℕ) : ℝ) ^ 2 *
        X ^ (-1 - σ) * (1 + Real.log X) := by
    calc
      _ ≤ 2 * gaussianSecondMomentLatticeConstant σ * t ^ 2 * X ^ (-1 - σ) *
          ((U * V : ℕ) : ℝ) ^ 2 * (1 + Real.log X) := by gcongr; linarith only [hlogK]
      _ = _ := by ring
  have hlog : gaussianLogSecondMomentConstant σ * t ^ 2 * X ^ (-1 - σ) *
      (1 + Real.log X) * (V : ℝ) ^ 2 ≤
      gaussianLogSecondMomentConstant σ * t ^ 2 * ((U * V : ℕ) : ℝ) ^ 2 *
        X ^ (-1 - σ) * (1 + Real.log X) := by
    calc
      _ ≤ gaussianLogSecondMomentConstant σ * t ^ 2 * X ^ (-1 - σ) *
          (1 + Real.log X) * ((U * V : ℕ) : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  have he := norm_gaussianPrimeMoment_sub_centredVaughan_le
    hσ hσ1 hα hαξ ht hξ hX hscale hU hV hVX
  have he' : ‖gaussianCentredVaughanError σ t U V ((α : ℂ) - ξ * I)‖ ≤
      4 * α * (U : ℝ) ^ 2 * (U : ℝ) ^ (1 - σ) * Real.log U +
      2 * gaussianSecondMomentLatticeConstant σ * t ^ 2 * X ^ (-1 - σ) *
        ((U * V : ℕ) : ℝ) ^ 2 * Real.log ((U * V : ℕ) : ℝ) +
      gaussianLogSecondMomentConstant σ * t ^ 2 * X ^ (-1 - σ) * (1 + Real.log X) * (V : ℝ) ^ 2 := by
    simpa only [gaussianCentredVaughanError, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_zero, Complex.sub_im, Complex.mul_im, mul_one, add_zero, sub_neg_eq_add,
      neg_neg, zero_sub] using he
  apply he'.trans
  have hs := _root_.add_le_add (_root_.add_le_add hhead hfirst) hlog
  convert hs using 1
  unfold gaussianVaughanProductConstant
  ring

private theorem one_add_log_le_rpow {X η : ℝ} (hX : 1 ≤ X) (hη : 0 < η) :
    1 + Real.log X ≤ (1 + 1 / η) * X ^ η := by
  have hX0 := zero_lt_one.trans_le hX
  have hp : 1 ≤ X ^ η := Real.one_le_rpow hX hη.le
  have hl := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hX0 η)
  rw [Real.log_rpow hX0] at hl
  have hdiv : Real.log X ≤ X ^ η / η := (le_div_iff₀ hη).mpr (by linarith only [hl])
  calc
    _ ≤ X ^ η + X ^ η / η := _root_.add_le_add hp hdiv
    _ = _ := by ring

/-- Arbitrarily small power slack removes the logarithm from the product
cutoff estimate. -/
theorem norm_gaussianCentredVaughanError_le_product_power {σ α ξ t X η : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 < α) (hαξ : α ≤ ξ)
    (ht : 2 ≤ t) (hξ : ξ ≤ 2 * α * t) (hscale : α * X ^ 2 = 2)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : ((U * V : ℕ) : ℝ) ≤ X)
    (hη : 0 < η) :
    ‖gaussianCentredVaughanError σ t U V ((α : ℂ) - ξ * I)‖ ≤
      (gaussianVaughanProductConstant σ * (1 + 1 / η)) * t ^ 2 *
        ((U * V : ℕ) : ℝ) ^ 2 * X ^ (-1 - σ + η) := by
  have hX1 : 1 ≤ X := (by exact_mod_cast Nat.mul_pos hU hV : (1 : ℝ) ≤ ((U * V : ℕ) : ℝ)).trans hUV
  have hX := zero_lt_one.trans_le hX1
  have hK := gaussianVaughanProductConstant_nonneg hσ1
  apply (norm_gaussianCentredVaughanError_le_product hσ hσ1 hα hαξ ht hξ hscale hU hV hUV).trans
  calc
    _ ≤ gaussianVaughanProductConstant σ * t ^ 2 * ((U * V : ℕ) : ℝ) ^ 2 *
        X ^ (-1 - σ) * ((1 + 1 / η) * X ^ η) := by
      exact mul_le_mul_of_nonneg_left (one_add_log_le_rpow hX1 hη) (by positivity)
    _ = _ := by rw [Real.rpow_add hX]; ring

private theorem product_error_halfStrip_bounds {σ β α ξ t X η : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hβ : σ ≤ β)
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hX : 0 < X) (hscale : α * X ^ 2 = 2)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUV : 2 * Real.exp 1 * ((U * V : ℕ) : ℝ) ≤ X)
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) :
    let r := 1 / (16 * t)
    let f := twistedGaussianCentredVaughanError σ β t U V ((α : ℂ) - ξ * I)
    DifferentiableOn ℂ f (dampingHalfStrip r) ∧
    ∀ z ∈ dampingHalfStrip r, ‖f z‖ ≤
      (Real.exp (β + 4) * gaussianVaughanProductConstant σ * (1 + 1 / η)) *
        t ^ 2 * ((U * V : ℕ) : ℝ) ^ 2 * X ^ (-1 - σ + η) := by
  let r := 1 / (16 * t)
  let ε : ℂ := (α : ℂ) - ξ * I
  let K := gaussianVaughanProductConstant σ * (1 + 1 / η)
  let q := -1 - σ + η
  have ht0 : 0 < t := by linarith only [ht]
  have hr1 : r ≤ 1 := by
    dsimp only [r]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [ht]
  have htr : t * r = 1 / 16 := by dsimp only [r]; field_simp [ht0.ne']
  have hK : 0 ≤ K := mul_nonneg (gaussianVaughanProductConstant_nonneg hσ1) (by positivity)
  have hq : q ≤ 0 := by dsimp only [q]; linarith only [hσ, hη1]
  have hq2 : -2 ≤ q := by dsimp only [q]; linarith only [hσ1, hη]
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
    have hd := differentiableAt_gaussianCentredVaughanError hσ
      (by linarith only [hσ1]) t U V (hgeom z hz).1
    have he : DifferentiableAt ℂ (fun w : ℂ => ε * Complex.exp (-2 * w)) z := by fun_prop
    have hw : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((((σ : ℂ) + t * I) - β) * w)) z := by fun_prop
    exact (hw.mul (hd.comp z he)).differentiableWithinAt
  · intro z hz
    obtain ⟨hε, hεξ, hεξt, Y, hY, hscaleY, hYlo⟩ := hgeom z hz
    have hx : -1 ≤ z.re := by linarith only [hz.1, hr1]
    have hex : 1 ≤ Real.exp 1 * Real.exp z.re := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith only [hx])
    have hKY : ((U * V : ℕ) : ℝ) ≤ Y := by
      calc
        _ ≤ (Real.exp 1 * Real.exp z.re) * ((U * V : ℕ) : ℝ) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hex (Nat.cast_nonneg (U * V))
        _ ≤ X * Real.exp z.re / 2 := by
          have hh := mul_le_mul_of_nonneg_right hUV (Real.exp_pos z.re).le
          nlinarith only [hh]
        _ ≤ Y := hYlo
    have heR : (((ε * Complex.exp (-2 * z)).re : ℝ) : ℂ) -
        (-(ε * Complex.exp (-2 * z)).im : ℝ) * I = ε * Complex.exp (-2 * z) := by
      apply Complex.ext <;> simp
    have hE : ‖gaussianCentredVaughanError σ t U V (ε * Complex.exp (-2 * z))‖ ≤
        K * t ^ 2 * ((U * V : ℕ) : ℝ) ^ 2 * Y ^ q := by
      have hh := norm_gaussianCentredVaughanError_le_product_power
        hσ hσ1 hε hεξ (by linarith only [ht]) hεξt hscaleY hU hV hKY hη
      simpa only [heR, K, q] using hh
    have hlogY : Real.log X + z.re - 1 ≤ Real.log Y := by
      have hl := Real.log_le_log (by positivity : 0 < X * Real.exp z.re / 2) hYlo
      rw [Real.log_div (by positivity) (by norm_num),
        Real.log_mul hX.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
      have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [hl, htwo]
    have hphase : ((((σ : ℂ) + t * I) - β) * z).re = (σ - β) * z.re - t * z.im := by simp
    have hb : (σ - β) * z.re - t * z.im + Real.log Y * q ≤
        Real.log X * q + (β + 4) := by
      have hl := mul_le_mul_of_nonpos_right hlogY hq
      have hx' := mul_le_mul_of_nonneg_left (show -z.re ≤ 1 by linarith only [hx])
        (show 0 ≤ β + 1 - η by linarith only [hβ, hσ, hη1])
      have hy' := mul_le_mul_of_nonneg_left (neg_le_abs z.im) ht0.le
      have hy'' := (mul_le_mul_of_nonneg_left hz.2.le ht0.le).trans_eq htr
      dsimp only [q] at hl hq2 ⊢
      nlinarith only [hl, hx', hy', hy'', hq2, hη]
    dsimp only [twistedGaussianCentredVaughanError]
    rw [norm_mul, Complex.norm_exp, hphase]
    calc
      _ ≤ Real.exp ((σ - β) * z.re - t * z.im) *
          (K * t ^ 2 * ((U * V : ℕ) : ℝ) ^ 2 * Y ^ q) :=
        mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le
      _ = (K * t ^ 2 * ((U * V : ℕ) : ℝ) ^ 2) *
          Real.exp ((σ - β) * z.re - t * z.im + Real.log Y * q) := by
        rw [Real.rpow_def_of_pos hY, Real.exp_add]
        ring
      _ ≤ (K * t ^ 2 * ((U * V : ℕ) : ℝ) ^ 2) *
          Real.exp (Real.log X * q + (β + 4)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb) (by positivity)
      _ = _ := by
        rw [Real.exp_add, ← Real.rpow_def_of_pos hX]
        dsimp only [K, q]
        ring

/-- Power-sized cutoffs retain every spacing factor in the actual filter. -/
theorem norm_filtered_gaussianCentredVaughanError_le_product {σ β α ξ t X η h : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hβ : σ ≤ β)
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hX : 0 < X) (hscale : α * X ^ 2 = 2)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUV : 2 * Real.exp 1 * ((U * V : ℕ) : ℝ) ≤ X)
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hh : 0 ≤ h) (hh1 : h ≤ 1) (ws : List ℂ) :
    ‖∑ j ∈ range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianCentredVaughanError σ β t U V ((α : ℂ) - ξ * I) ((j : ℂ) * h)‖ ≤
      (Real.exp (β + 4) * gaussianVaughanProductConstant σ * (1 + 1 / η) *
        (16 : ℝ) ^ ws.length * dampingFilterCost ws) * h ^ ws.length *
        t ^ (ws.length + 2) * ((U * V : ℕ) : ℝ) ^ 2 * X ^ (-1 - σ + η) := by
  have ht0 : 0 < t := by linarith only [ht]
  have hr : 0 < 1 / (16 * t) := by positivity
  have hr1 : 1 / (16 * t) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [ht]
  let M := (Real.exp (β + 4) * gaussianVaughanProductConstant σ * (1 + 1 / η)) *
    t ^ 2 * ((U * V : ℕ) : ℝ) ^ 2 * X ^ (-1 - σ + η)
  have hM : 0 ≤ M := by
    have hK := gaussianVaughanProductConstant_nonneg hσ1
    dsimp only [M]
    positivity
  obtain ⟨hf, hb⟩ := product_error_halfStrip_bounds hσ hσ1 hβ hα ht hlo hhi hX hscale hU hV hUV hη hη1
  have H := norm_dampingFilterPolynomial_sum_le hr hr1 hM hh hh1 ws hf hb
  calc
    _ ≤ M * (h / (1 / (16 * t))) ^ ws.length * dampingFilterCost ws := H
    _ = _ := by
      dsimp only [M]
      have he : h / (1 / (16 * t)) = h * (16 * t) := by field_simp [ht0.ne']
      rw [he, mul_pow, mul_pow, pow_add]
      ring

/-- A product cutoff below the fractional observation horizon gives a
vanishing error even after division by the filter spacing to its degree. -/
theorem norm_filtered_gaussianCentredVaughanError_product_le_inv {σ β α ξ t X η h : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hβ : σ ≤ β)
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hX : 0 < X) (hscale : α * X ^ 2 = 2)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUV : 2 * Real.exp 1 * ((U * V : ℕ) : ℝ) ≤ X)
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hh : 0 ≤ h) (hh1 : h ≤ 1) (ws : List ℂ)
    (hcut : ((U * V : ℕ) : ℝ) ^ 2 * t ^ (ws.length + 3) ≤ X ^ (1 + σ - η)) :
    ‖∑ j ∈ range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianCentredVaughanError σ β t U V ((α : ℂ) - ξ * I) ((j : ℂ) * h)‖ ≤
      (Real.exp (β + 4) * gaussianVaughanProductConstant σ * (1 + 1 / η) *
        (16 : ℝ) ^ ws.length * dampingFilterCost ws) * h ^ ws.length / t := by
  have ht0 : 0 < t := by linarith only [ht]
  have hpow : X ^ (1 + σ - η) * X ^ (-1 - σ + η) = 1 := by
    rw [← Real.rpow_add hX]
    rw [show (1 + σ - η) + (-1 - σ + η) = 0 by ring, Real.rpow_zero]
  have hb : t ^ (ws.length + 2) * ((U * V : ℕ) : ℝ) ^ 2 * X ^ (-1 - σ + η) ≤ 1 / t := by
    apply (le_div_iff₀ ht0).mpr
    have H := mul_le_mul_of_nonneg_right hcut (Real.rpow_nonneg hX.le (-1 - σ + η))
    rw [hpow] at H
    convert H using 1
    rw [show ws.length + 3 = (ws.length + 2) + 1 by omega, pow_succ]
    ring
  have hK := gaussianVaughanProductConstant_nonneg hσ1
  have hA := dampingFilterCost_nonneg ws
  have H := norm_filtered_gaussianCentredVaughanError_le_product
    hσ hσ1 hβ hα ht hlo hhi hX hscale hU hV hUV hη hη1 hh hh1 ws
  apply H.trans
  have HH := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (Real.exp (β + 4) * gaussianVaughanProductConstant σ * (1 + 1 / η) *
      (16 : ℝ) ^ ws.length * dampingFilterCost ws) * h ^ ws.length by positivity)
  convert HH using 1 <;> ring

#print axioms norm_filtered_gaussianCentredVaughanError_le_product
#print axioms norm_filtered_gaussianCentredVaughanError_product_le_inv
#print axioms norm_gaussianCentredVaughanError_le_product
#print axioms norm_gaussianCentredVaughanError_le_product_power

end GaloisForLFunctions.ExceptionalLayerTheory
