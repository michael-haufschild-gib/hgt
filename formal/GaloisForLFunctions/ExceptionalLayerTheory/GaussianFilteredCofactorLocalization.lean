import GaloisForLFunctions.ExceptionalLayerTheory.GaussianVaughanCofactorTail
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianVaughanCutoffHorizon
import GaloisForLFunctions.HTGeometry.EigenLogDerivNormalization

/-!
# Spacing-preserving localization of the centred arithmetic current

An exponential twist bounds the Gaussian cofactor tail on a logarithmic
half-strip. Shifting the filter roots compensates that twist exactly.
The product-cutoff reduction therefore retains only short cofactors,
with both continuum terms and every spacing factor preserved.
-/

open Complex Finset
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem cofactor_filter_monic (h : ℝ) (ws : List ℂ) :
    (dampingFilterPolynomial h ws).Monic := by
  induction ws with
  | nil => exact Polynomial.monic_one
  | cons ω ws ih => exact (Polynomial.monic_X_sub_C _).mul ih

private theorem cofactor_filter_degree (h : ℝ) (ws : List ℂ) :
    (dampingFilterPolynomial h ws).natDegree = ws.length := by
  induction ws with
  | nil => exact Polynomial.natDegree_one
  | cons ω ws ih =>
    rw [dampingFilterPolynomial, Polynomial.natDegree_mul
      (Polynomial.monic_X_sub_C _).ne_zero (cofactor_filter_monic h ws).ne_zero,
      Polynomial.natDegree_X_sub_C, ih, List.length_cons]
    omega

private theorem cofactor_filter_scale (h c : ℝ) (ws : List ℂ) :
    (dampingFilterPolynomial h ws).comp
      (Polynomial.C (Complex.exp ((h : ℂ) * c)) * Polynomial.X) =
      Polynomial.C (Complex.exp ((h : ℂ) * c) ^ ws.length) *
        dampingFilterPolynomial h (ws.map (fun ω => ω - (c : ℂ))) := by
  induction ws with
  | nil => simp [dampingFilterPolynomial]
  | cons ω ws ih =>
    have he : Complex.exp ((h : ℂ) * ω) =
        Complex.exp ((h : ℂ) * c) * Complex.exp ((h : ℂ) * (ω - (c : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [dampingFilterPolynomial, Polynomial.mul_comp, Polynomial.sub_comp,
      Polynomial.X_comp, Polynomial.C_comp, ih]
    simp only [List.map_cons, dampingFilterPolynomial, List.length_cons, pow_succ, he, Polynomial.C_mul]
    ring

/-- Multiplying samples by an exponential translates every filter root. -/
theorem cofactor_filter_twist (h c : ℝ) (ws : List ℂ) (f : ℂ → ℂ) :
    (∑ j ∈ range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        (Complex.exp ((c : ℂ) * ((j : ℂ) * h)) * f ((j : ℂ) * h))) =
    Complex.exp ((h : ℂ) * c) ^ ws.length *
      ∑ j ∈ range ((dampingFilterPolynomial h (ws.map (fun ω => ω - (c : ℂ)))).natDegree + 1),
        (dampingFilterPolynomial h (ws.map (fun ω => ω - (c : ℂ)))).coeff j * f ((j : ℂ) * h) := by
  rw [cofactor_filter_degree, cofactor_filter_degree, List.length_map, Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff j) (cofactor_filter_scale h c ws)
  rw [HTGeometry.coeff_comp_C_mul_X, Polynomial.coeff_C_mul] at hc
  have he : Complex.exp ((c : ℂ) * ((j : ℂ) * h)) = Complex.exp ((h : ℂ) * c) ^ j := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [he]
  calc
    _ = (Complex.exp ((h : ℂ) * c) ^ j * (dampingFilterPolynomial h ws).coeff j) * f ((j : ℂ) * h) := by ring
    _ = _ := by rw [hc]; ring

private theorem cofactor_damping_exp_split (ε z : ℂ) :
    ε * Complex.exp (-2 * z) = (Real.exp (-2 * z.re) : ℂ) *
      (ε * Complex.exp (I * ((-2 * z.im : ℝ) : ℂ))) := by
  have he : -2 * z = ((-2 * z.re : ℝ) : ℂ) + I * ((-2 * z.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [he, Complex.exp_add, ← Complex.ofReal_exp]
  ring

/-- A narrow complex damping rotation enlarges the dilated physical scale by at most two. -/
theorem cofactor_rotated_scale_upper {α ξ t X Y : ℝ} {z : ℂ}
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hz : t * |z.im| ≤ 1 / 16) (hX : 0 < X) (hscale : α * X ^ 2 = 2)
    (hY : 0 < Y) (hscaleY : (((α : ℂ) - ξ * I) * Complex.exp (-2 * z)).re * Y ^ 2 = 2) :
    Y ≤ 2 * X * Real.exp z.re := by
  let ε : ℂ := (α : ℂ) - ξ * I
  let q := ε * Complex.exp (I * ((-2 * z.im : ℝ) : ℂ))
  have hξ : 0 ≤ ξ := by linarith only [hα, hlo]
  have hε : ‖ε‖ ≤ 2 * α * t := by
    calc
      _ ≤ ‖(α : ℂ)‖ + ‖(ξ : ℂ) * I‖ := norm_sub_le _ _
      _ = α + ξ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hα.le, abs_of_nonneg hξ, Complex.norm_I, mul_one]
      _ ≤ _ := by nlinarith only [ht, hα, hhi]
  have hchord : ‖Complex.exp (I * ((-2 * z.im : ℝ) : ℂ)) - 1‖ ≤ 2 * |z.im| := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2 * z.im))
  have hdiff : ‖q - ε‖ ≤ α / 4 := by
    have he : q - ε = ε * (Complex.exp (I * ((-2 * z.im : ℝ) : ℂ)) - 1) := by
      dsimp only [q]; ring
    rw [he, norm_mul]
    calc
      _ ≤ (2 * α * t) * (2 * |z.im|) := mul_le_mul hε hchord (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hz hα.le]
  have hre := (Complex.abs_re_le_norm (q - ε)).trans hdiff
  have heR : ε.re = α := by simp [ε]
  rw [Complex.sub_re, heR] at hre
  have hq : α / 2 ≤ q.re := by
    have hh := (abs_le.mp hre).1
    linarith only [hh, hα]
  have hscaleY' : (Real.exp (-2 * z.re) * q.re) * Y ^ 2 = 2 := by
    rw [cofactor_damping_exp_split] at hscaleY
    simpa only [q, ε, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hscaleY
  have he : Real.exp (-2 * z.re) * (Real.exp z.re) ^ 2 = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hsmall : (α / 2) * Real.exp (-2 * z.re) * Y ^ 2 ≤ 2 := by
    calc
      _ ≤ q.re * Real.exp (-2 * z.re) * Y ^ 2 := by gcongr
      _ = 2 := by nlinarith only [hscaleY']
  have hs := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ X ^ 2 * (Real.exp z.re) ^ 2 by positivity)
  have hsq : Y ^ 2 ≤ 2 * (X * Real.exp z.re) ^ 2 := by
    calc
      _ = ((α * X ^ 2) / 2) * (Real.exp (-2 * z.re) * (Real.exp z.re) ^ 2) * Y ^ 2 := by
        rw [hscale, he]; ring
      _ = ((α / 2) * Real.exp (-2 * z.re) * Y ^ 2) *
          (X ^ 2 * (Real.exp z.re) ^ 2) := by ring
      _ ≤ 2 * (X ^ 2 * (Real.exp z.re) ^ 2) := hs
      _ = _ := by ring
  have hx : 0 < X * Real.exp z.re := mul_pos hX (Real.exp_pos _)
  nlinarith only [hsq, hx, hY]

/-- The Mellin twist of the actual cofactor tail. -/
def twistedGaussianVaughanCofactorTail (σ β t : ℝ) (U V W : ℕ) (ε z : ℂ) : ℂ :=
  Complex.exp ((((σ : ℂ) + t * I) - β) * z) *
    gaussianVaughanCofactorTail σ t U V W (ε * Complex.exp (-2 * z))

private theorem cofactor_tail_halfStrip_bounds {σ α ξ t X : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 < α) (ht : 4 ≤ t)
    (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t) (hX : 2 * Real.exp 1 ≤ X)
    (hscale : α * X ^ 2 = 2) {U W : ℕ} (hU : 1 ≤ U) (hW : 1 ≤ W) (V k : ℕ) :
    let r := 1 / (16 * t)
    let p := 3 + 2 * k
    let f := twistedGaussianVaughanCofactorTail σ (σ + p + 1) t U V W ((α : ℂ) - ξ * I)
    DifferentiableOn ℂ f (dampingHalfStrip r) ∧
    ∀ z ∈ dampingHalfStrip r, ‖f z‖ ≤
      (784 * ((k + 2).factorial : ℝ) * (2 : ℝ) ^ p * Real.exp 2) *
        X ^ p / ((U * W : ℕ) : ℝ) ^ (2 * k) := by
  let r := 1 / (16 * t)
  let p := 3 + 2 * k
  let ε : ℂ := (α : ℂ) - ξ * I
  let K := 784 * ((k + 2).factorial : ℝ)
  have ht0 : 0 < t := by linarith only [ht]
  have hX0 : 0 < X := (by positivity : 0 < 2 * Real.exp 1).trans_le hX
  have hr1 : r ≤ 1 := by
    dsimp only [r]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [ht]
  have htr : t * r = 1 / 16 := by dsimp only [r]; field_simp [ht0.ne']
  have hgeom (z : ℂ) (hz : z ∈ dampingHalfStrip r) :
      0 < (ε * Complex.exp (-2 * z)).re ∧
      (ε * Complex.exp (-2 * z)).re ≤ -(ε * Complex.exp (-2 * z)).im ∧
      -(ε * Complex.exp (-2 * z)).im ≤ 2 * (ε * Complex.exp (-2 * z)).re * t ∧
      ∃ Y : ℝ, 0 < Y ∧ (ε * Complex.exp (-2 * z)).re * Y ^ 2 = 2 ∧
        X * Real.exp z.re / 2 ≤ Y := by
    apply exists_damping_rotated_scale hα ht hlo hhi _ hX0 hscale
    exact (mul_le_mul_of_nonneg_left hz.2.le ht0.le).trans_eq htr
  refine ⟨?_, ?_⟩
  · intro z hz
    have hd := differentiableAt_gaussianVaughanCofactorTail hσ t U V W (hgeom z hz).1
    have he : DifferentiableAt ℂ (fun w : ℂ => ε * Complex.exp (-2 * w)) z := by fun_prop
    have hw : DifferentiableAt ℂ
        (fun w : ℂ => Complex.exp ((((σ : ℂ) + t * I) - ((σ + (p : ℝ) + 1 : ℝ) : ℂ)) * w)) z := by fun_prop
    exact (hw.mul (hd.comp z he)).differentiableWithinAt
  · intro z hz
    obtain ⟨hε, hεξ, hεξt, Y, hY, hscaleY, hYlo⟩ := hgeom z hz
    have hx : -1 ≤ z.re := by linarith only [hz.1, hr1]
    have hy := (mul_le_mul_of_nonneg_left hz.2.le ht0.le).trans_eq htr
    have hYhi := cofactor_rotated_scale_upper hα ht hlo hhi hy hX0 hscale hY hscaleY
    have hex : 1 ≤ Real.exp 1 * Real.exp z.re := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith only [hx])
    have hY1 : 1 ≤ Y := by
      have hh := mul_le_mul_of_nonneg_right hX (Real.exp_pos z.re).le
      linarith only [hh, hex, hYlo]
    have heR : (((ε * Complex.exp (-2 * z)).re : ℝ) : ℂ) -
        (-(ε * Complex.exp (-2 * z)).im : ℝ) * I = ε * Complex.exp (-2 * z) := by
      apply Complex.ext <;> simp
    have hE : ‖gaussianVaughanCofactorTail σ t U V W (ε * Complex.exp (-2 * z))‖ ≤
        K * Y ^ p / ((U * W : ℕ) : ℝ) ^ (2 * k) := by
      have hh := norm_gaussianVaughanCofactorTail_le hσ hε hεξ ht0 hεξt hY1 hscaleY hU hW V k
      simpa only [heR, K, p] using hh
    have hphase : ((((σ : ℂ) + t * I) - ((σ + (p : ℝ) + 1 : ℝ) : ℂ)) * z).re =
        -((p : ℝ) + 1) * z.re - t * z.im := by
      simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im,
        Complex.add_im, Complex.sub_im, mul_zero, mul_one, sub_zero, add_zero]
      ring
    have hb : -z.re - t * z.im ≤ 2 := by
      have hh := mul_le_mul_of_nonneg_left (neg_le_abs z.im) ht0.le
      linarith only [hx, hh, hy]
    dsimp only [twistedGaussianVaughanCofactorTail]
    rw [norm_mul, Complex.norm_exp, hphase]
    calc
      _ ≤ Real.exp (-((p : ℝ) + 1) * z.re - t * z.im) *
          (K * (2 * X * Real.exp z.re) ^ p / ((U * W : ℕ) : ℝ) ^ (2 * k)) := by
        apply mul_le_mul_of_nonneg_left (hE.trans ?_) (Real.exp_pos _).le
        dsimp only [K]
        gcongr
      _ = (K * (2 : ℝ) ^ p * X ^ p / ((U * W : ℕ) : ℝ) ^ (2 * k)) *
          Real.exp (-z.re - t * z.im) := by
        rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
        have he : -z.re - t * z.im = (-((p : ℝ) + 1) * z.re - t * z.im) + (p : ℝ) * z.re := by ring
        rw [he, Real.exp_add]
        ring
      _ ≤ (K * (2 : ℝ) ^ p * X ^ p / ((U * W : ℕ) : ℝ) ^ (2 * k)) * Real.exp 2 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb) (by dsimp only [K]; positivity)
      _ = _ := by dsimp only [K, p]; ring

/-- The fixed extra twist that makes the `k`th Gaussian tail moment decay
under forward logarithmic damping translation. -/
def gaussianCofactorTwist (σ β : ℝ) (k : ℕ) : ℝ := σ + (3 + 2 * k : ℕ) + 1 - β

/-- Explicit spacing-independent cost of filtering the actual cofactor tail. -/
def gaussianCofactorFilterConstant (σ β : ℝ) (k : ℕ) (ws : List ℂ) : ℝ :=
  (784 * ((k + 2).factorial : ℝ) * (2 : ℝ) ^ (3 + 2 * k) * Real.exp 2) *
    Real.exp (|gaussianCofactorTwist σ β k| * ws.length) * (16 : ℝ) ^ ws.length *
      dampingFilterCost (ws.map (fun ω => ω - (gaussianCofactorTwist σ β k : ℂ)))

/-- The actual cofactor tail retains all filter spacing factors, uniformly
in the three arithmetic cutoffs and without an arithmetic-cancellation input. -/
theorem norm_filtered_gaussianVaughanCofactorTail_le {σ β α ξ t X h : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 < α) (ht : 4 ≤ t)
    (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t) (hX : 2 * Real.exp 1 ≤ X)
    (hscale : α * X ^ 2 = 2) {U W : ℕ} (hU : 1 ≤ U) (hW : 1 ≤ W) (V k : ℕ)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ws : List ℂ) :
    ‖∑ j ∈ range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianVaughanCofactorTail σ β t U V W ((α : ℂ) - ξ * I) ((j : ℂ) * h)‖ ≤
      gaussianCofactorFilterConstant σ β k ws * h ^ ws.length * t ^ ws.length *
        X ^ (3 + 2 * k) / ((U * W : ℕ) : ℝ) ^ (2 * k) := by
  let c := gaussianCofactorTwist σ β k
  let roots := ws.map (fun ω => ω - (c : ℂ))
  let ε : ℂ := (α : ℂ) - ξ * I
  let f := twistedGaussianVaughanCofactorTail σ (σ + (3 + 2 * k : ℕ) + 1) t U V W ε
  let M := (784 * ((k + 2).factorial : ℝ) * (2 : ℝ) ^ (3 + 2 * k) * Real.exp 2) *
    X ^ (3 + 2 * k) / ((U * W : ℕ) : ℝ) ^ (2 * k)
  have ht0 : 0 < t := by linarith only [ht]
  have hX0 : 0 < X := (by positivity : 0 < 2 * Real.exp 1).trans_le hX
  have hr : 0 < 1 / (16 * t) := by positivity
  have hr1 : 1 / (16 * t) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [ht]
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  obtain ⟨hf, hb⟩ := cofactor_tail_halfStrip_bounds hσ hα ht hlo hhi hX hscale hU hW V k
  have H := norm_dampingFilterPolynomial_sum_le hr hr1 hM hh hh1 roots hf hb
  have he (z : ℂ) : twistedGaussianVaughanCofactorTail σ β t U V W ε z =
      Complex.exp ((c : ℂ) * z) * f z := by
    dsimp only [twistedGaussianVaughanCofactorTail, f]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp only [c, gaussianCofactorTwist]
    push_cast
    ring
  have hsum := cofactor_filter_twist h c ws f
  simp_rw [← he] at hsum
  have hscalar : ‖Complex.exp ((h : ℂ) * c) ^ ws.length‖ ≤ Real.exp (|c| * ws.length) := by
    rw [norm_pow, Complex.norm_exp]
    have hre : ((h : ℂ) * c).re = h * c := by simp
    rw [hre, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hc : h * c ≤ |c| := by
      calc
        _ ≤ h * |c| := mul_le_mul_of_nonneg_left (le_abs_self c) hh
        _ ≤ 1 * |c| := mul_le_mul_of_nonneg_right hh1 (abs_nonneg c)
        _ = _ := one_mul _
    nlinarith only [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg ws.length : (0 : ℝ) ≤ ws.length)]
  rw [hsum, norm_mul]
  calc
    _ ≤ Real.exp (|c| * ws.length) *
        (M * (h / (1 / (16 * t))) ^ roots.length * dampingFilterCost roots) :=
      mul_le_mul hscalar H (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      have hd : roots.length = ws.length := by simp only [roots, List.length_map]
      rw [hd]
      have heh : h / (1 / (16 * t)) = h * (16 * t) := by field_simp [ht0.ne']
      rw [heh, mul_pow, mul_pow]
      dsimp only [M, roots, c, gaussianCofactorFilterConstant]
      ring


/-- The error after retaining only the actual cofactors at most `W`, with
both signed continuum terms still present. -/
def gaussianCofactorReductionError (σ t : ℝ) (U V W : ℕ) (ε : ℂ) : ℂ :=
  ((∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
    gaussianPrimeMomentWeight σ ε.re (-ε.im) t n) -
    gaussianFirstMomentPole ((σ : ℂ) + t * I) ε t) -
    gaussianCentredVaughanCofactorCurrent σ ε.re (-ε.im) t U V W

/-- The usual Mellin twist of the short-cofactor reduction error. -/
def twistedGaussianCofactorReductionError (σ β t : ℝ) (U V W : ℕ) (ε z : ℂ) : ℂ :=
  Complex.exp ((((σ : ℂ) + t * I) - β) * z) *
    gaussianCofactorReductionError σ t U V W (ε * Complex.exp (-2 * z))

private theorem cofactor_error_eq {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (U V W : ℕ) {ε : ℂ} (hε : 0 < ε.re) (hlo : ε.re ≤ -ε.im)
    (hhi : -ε.im ≤ 2 * ε.re * t) :
    gaussianCofactorReductionError σ t U V W ε =
      gaussianCentredVaughanError σ t U V ε + gaussianVaughanCofactorTail σ t U V W ε := by
  have he : (ε.re : ℂ) - (-ε.im : ℝ) * I = ε := by apply Complex.ext <;> simp
  have hh := gaussianCentredVaughan_sub_cofactorCurrent_eq hσ hε hlo ht hhi U V W
  rw [he] at hh
  dsimp only [gaussianCofactorReductionError, gaussianCentredVaughanError]
  linear_combination hh

private theorem cofactor_error_filter_eq {σ β α ξ t X h : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hX : 0 < X) (hscale : α * X ^ 2 = 2) (U V W : ℕ) (ws : List ℂ) :
    (∑ j ∈ range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianCofactorReductionError σ β t U V W ((α : ℂ) - ξ * I) ((j : ℂ) * h)) =
    (∑ j ∈ range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianCentredVaughanError σ β t U V ((α : ℂ) - ξ * I) ((j : ℂ) * h)) +
    ∑ j ∈ range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianVaughanCofactorTail σ β t U V W ((α : ℂ) - ξ * I) ((j : ℂ) * h) := by
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  have hz : t * |((j : ℂ) * h).im| ≤ 1 / 16 := by simp
  obtain ⟨hε, hεlo, hεhi, _⟩ := exists_damping_rotated_scale hα ht hlo hhi hz hX hscale
  dsimp only [twistedGaussianCofactorReductionError, twistedGaussianCentredVaughanError,
    twistedGaussianVaughanCofactorTail]
  rw [cofactor_error_eq hσ (by linarith only [ht]) U V W hε hεlo hεhi]
  ring

/-- The complete pole-subtracted prime current reduces to the actual
short-cofactor current with explicit product-cutoff and Gaussian-tail costs. -/
theorem norm_filtered_gaussianCofactorReductionError_le {σ β α ξ t X η h : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hβ : σ ≤ β)
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hX : 0 < X) (hscale : α * X ^ 2 = 2) {U V W : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hW : 1 ≤ W)
    (hUV : 2 * Real.exp 1 * ((U * V : ℕ) : ℝ) ≤ X)
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hh : 0 ≤ h) (hh1 : h ≤ 1) (ws : List ℂ) (k : ℕ) :
    ‖∑ j ∈ range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianCofactorReductionError σ β t U V W ((α : ℂ) - ξ * I) ((j : ℂ) * h)‖ ≤
    (Real.exp (β + 4) * gaussianVaughanProductConstant σ * (1 + 1 / η) *
      (16 : ℝ) ^ ws.length * dampingFilterCost ws) * h ^ ws.length *
      t ^ (ws.length + 2) * ((U * V : ℕ) : ℝ) ^ 2 * X ^ (-1 - σ + η) +
    gaussianCofactorFilterConstant σ β k ws * h ^ ws.length * t ^ ws.length *
      X ^ (3 + 2 * k) / ((U * W : ℕ) : ℝ) ^ (2 * k) := by
  have hK1 : (1 : ℝ) ≤ ((U * V : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hU hV
  have hX2 : 2 * Real.exp 1 ≤ X := by
    have hh := mul_le_mul_of_nonneg_left hK1 (by positivity : 0 ≤ 2 * Real.exp 1)
    have hle : 2 * Real.exp 1 ≤ 2 * Real.exp 1 * ((U * V : ℕ) : ℝ) := by
      simpa only [mul_one] using hh
    exact hle.trans hUV
  rw [cofactor_error_filter_eq hσ hα ht hlo hhi hX hscale U V W ws]
  apply (norm_add_le _ _).trans
  exact _root_.add_le_add
    (norm_filtered_gaussianCentredVaughanError_le_product
      hσ hσ1 hβ hα ht hlo hhi hX hscale hU hV hUV hη hη1 hh hh1 ws)
    (norm_filtered_gaussianVaughanCofactorTail_le hσ hα ht hlo hhi hX2 hscale hU hW V k hh hh1 ws)

/-- The product and cofactor budgets make the short-cofactor reduction
error vanish after normalization by every spacing factor. -/
theorem norm_filtered_gaussianCofactorReductionError_le_inv {σ β α ξ t X η h : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hβ : σ ≤ β)
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hX : 0 < X) (hscale : α * X ^ 2 = 2) {U V W : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hW : 1 ≤ W)
    (hUV : 2 * Real.exp 1 * ((U * V : ℕ) : ℝ) ≤ X)
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hh : 0 ≤ h) (hh1 : h ≤ 1) (ws : List ℂ) (k : ℕ)
    (hcut : ((U * V : ℕ) : ℝ) ^ 2 * t ^ (ws.length + 3) ≤ X ^ (1 + σ - η))
    (htail : X ^ (3 + 2 * k) * t ^ (ws.length + 1) ≤ ((U * W : ℕ) : ℝ) ^ (2 * k)) :
    ‖∑ j ∈ range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianCofactorReductionError σ β t U V W ((α : ℂ) - ξ * I) ((j : ℂ) * h)‖ ≤
    ((Real.exp (β + 4) * gaussianVaughanProductConstant σ * (1 + 1 / η) *
      (16 : ℝ) ^ ws.length * dampingFilterCost ws) + gaussianCofactorFilterConstant σ β k ws) *
        h ^ ws.length / t := by
  have ht0 : 0 < t := by linarith only [ht]
  have hB : (0 : ℝ) < ((U * W : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hU hW
  have hK1 : (1 : ℝ) ≤ ((U * V : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hU hV
  have hX2 : 2 * Real.exp 1 ≤ X := by
    calc
      _ = 2 * Real.exp 1 * 1 := by ring
      _ ≤ 2 * Real.exp 1 * ((U * V : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hK1 (by positivity)
      _ ≤ X := hUV
  have hC : 0 ≤ gaussianCofactorFilterConstant σ β k ws := by
    have ha := dampingFilterCost_nonneg (ws.map (fun ω => ω - (gaussianCofactorTwist σ β k : ℂ)))
    unfold gaussianCofactorFilterConstant
    positivity
  have hnorm : t ^ ws.length * X ^ (3 + 2 * k) / ((U * W : ℕ) : ℝ) ^ (2 * k) ≤ 1 / t := by
    apply (div_le_div_iff₀ (pow_pos hB _) ht0).mpr
    rw [pow_succ] at htail
    calc
      _ = X ^ (3 + 2 * k) * (t ^ ws.length * t) := by ring
      _ ≤ ((U * W : ℕ) : ℝ) ^ (2 * k) := htail
      _ = _ := by ring
  have hT := norm_filtered_gaussianVaughanCofactorTail_le (β := β) hσ hα ht hlo hhi hX2 hscale hU hW V k hh hh1 ws
  have hT' : ‖∑ j ∈ range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianVaughanCofactorTail σ β t U V W ((α : ℂ) - ξ * I) ((j : ℂ) * h)‖ ≤
      gaussianCofactorFilterConstant σ β k ws * h ^ ws.length / t := by
    apply hT.trans
    have HH := mul_le_mul_of_nonneg_left hnorm
      (show 0 ≤ gaussianCofactorFilterConstant σ β k ws * h ^ ws.length by positivity)
    convert HH using 1 <;> ring
  have hE := norm_filtered_gaussianCentredVaughanError_product_le_inv
    hσ hσ1 hβ hα ht hlo hhi hX hscale hU hV hUV hη hη1 hh hh1 ws hcut
  rw [cofactor_error_filter_eq hσ hα ht hlo hhi hX hscale U V W ws]
  have H := (norm_add_le _ _).trans (_root_.add_le_add hE hT')
  apply H.trans_eq
  ring

private theorem cofactor_power_budget {X B δ t : ℝ} (hX : 1 ≤ X) (d k : ℕ)
    (hBX : X ^ (1 + δ) ≤ B) (hgain : 4 ≤ (2 * k : ℕ) * δ)
    (htX : t ^ (d + 1) ≤ X) : X ^ (3 + 2 * k) * t ^ (d + 1) ≤ B ^ (2 * k) := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  calc
    _ ≤ X ^ (3 + 2 * k) * X := mul_le_mul_of_nonneg_left htX (by positivity)
    _ = X ^ (4 + 2 * k) := by rw [show 4 + 2 * k = (3 + 2 * k) + 1 by omega, pow_succ]
    _ ≤ (X ^ (1 + δ)) ^ (2 * k) := by
      rw [← Real.rpow_natCast X (4 + 2 * k), ← Real.rpow_mul_natCast hX0]
      apply Real.rpow_le_rpow_of_exponent_le hX
      push_cast at hgain ⊢
      nlinarith only [hgain]
    _ ≤ B ^ (2 * k) := pow_le_pow_left₀ (Real.rpow_nonneg hX0 _) hBX (2 * k)


/-- A superlinear cofactor product absorbs every prescribed Gaussian-tail
moment loss while the filter retains its full spacing normalization. -/
theorem norm_filtered_gaussianCofactorReductionError_le_inv_of_power {σ β α ξ t X η δ h : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hβ : σ ≤ β)
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hX : 1 ≤ X) (hscale : α * X ^ 2 = 2) {U V W : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hW : 1 ≤ W)
    (hUV : 2 * Real.exp 1 * ((U * V : ℕ) : ℝ) ≤ X)
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hh : 0 ≤ h) (hh1 : h ≤ 1) (ws : List ℂ) (k : ℕ)
    (hcut : ((U * V : ℕ) : ℝ) ^ 2 * t ^ (ws.length + 3) ≤ X ^ (1 + σ - η))
    (hUW : X ^ (1 + δ) ≤ ((U * W : ℕ) : ℝ)) (hgain : 4 ≤ (2 * k : ℕ) * δ)
    (htX : t ^ (ws.length + 1) ≤ X) :
    ‖∑ j ∈ range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianCofactorReductionError σ β t U V W ((α : ℂ) - ξ * I) ((j : ℂ) * h)‖ ≤
    ((Real.exp (β + 4) * gaussianVaughanProductConstant σ * (1 + 1 / η) *
      (16 : ℝ) ^ ws.length * dampingFilterCost ws) + gaussianCofactorFilterConstant σ β k ws) *
        h ^ ws.length / t := by
  exact norm_filtered_gaussianCofactorReductionError_le_inv hσ hσ1 hβ hα ht hlo hhi
    (zero_lt_one.trans_le hX) hscale hU hV hW hUV hη hη1 hh hh1 ws k hcut
    (cofactor_power_budget hX ws.length k hUW hgain htX)

end GaloisForLFunctions.ExceptionalLayerTheory
