import GaloisForLFunctions.RHTower.MaassBesselSeries

/-!
# The Maass function of a Dirichlet series with the functional equation of `ζ²`

For coefficients `g` of polynomial growth and constants `a, b` put

`u(x + iy) = 4 Σ_{n ≥ 1} g_n √y K₀(2πny) cos(2πnx) + √y (b + a log y)`  (`maassFun`).

* `u` is smooth on the upper half-plane (`contDiffOn_maassFun`);
* `u` is a quarter eigenfunction, `−y²(∂ₓ² + ∂ᵧ²)u = u/4` (`quarterDefect_maassFun`): termwise this
  is Bessel's equation `r(K₂ − K₀) = K₁` for the series, and `(√y)'' = −√y/(4y²)`,
  `(√y log y)'' = −√y log y/(4y²)` for the constant term;
* `u(−z̄) = u(z)` and `u(z + 1) = u(z)` (`maassFun_neg_conj`, `maassFun_add_one`).
-/

open Complex Set Filter
open scoped ContDiff

noncomputable section

namespace RHTower.MaassBesselSeries

open BesselKZero MaassAxisContinuation

variable {g : ℕ → ℂ}

/-! ## Directional derivatives of the Bessel series -/

theorem dirD_one_besselSeries (hg : PolyGrowth g) (α : ℝ) (j k : ℕ) (b : Bool) {z : ℂ}
    (hz : 0 < z.im) : dirD 1 (besselSeries g α j k b) z = seriesDx (g := g) α j k b z := by
  unfold dirD
  rw [(hasFDerivAt_besselSeries hg α j k b hz).fderiv]
  simp

theorem dirD_I_besselSeries (hg : PolyGrowth g) (α : ℝ) (j k : ℕ) (b : Bool) {z : ℂ}
    (hz : 0 < z.im) : dirD I (besselSeries g α j k b) z = seriesDy (g := g) α j k b z := by
  unfold dirD
  rw [(hasFDerivAt_besselSeries hg α j k b hz).fderiv]
  simp

theorem differentiableAt_besselSeries (hg : PolyGrowth g) (α : ℝ) (j k : ℕ) (b : Bool) {z : ℂ}
    (hz : 0 < z.im) : DifferentiableAt ℝ (besselSeries g α j k b) z :=
  (hasFDerivAt_besselSeries hg α j k b hz).differentiableAt

/-- `∂ᵥ(c F) = c ∂ᵥF`. -/
theorem dirD_const_mul {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z) (c : ℂ) (v : ℂ) :
    dirD v (fun w => c * F w) z = c * dirD v F z := by
  unfold dirD
  rw [(hF.hasFDerivAt.const_mul c).fderiv]
  simp

/-- `∂ᵥ(F − G) = ∂ᵥF − ∂ᵥG`. -/
theorem dirD_sub {F G : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z)
    (hG : DifferentiableAt ℝ G z) (v : ℂ) :
    dirD v (fun w => F w - G w) z = dirD v F z - dirD v G z := by
  unfold dirD
  rw [show (fun w => F w - G w) = F - G from rfl, (hF.hasFDerivAt.sub hG.hasFDerivAt).fderiv]
  simp

theorem dirD_add {F G : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z)
    (hG : DifferentiableAt ℝ G z) (v : ℂ) :
    dirD v (fun w => F w + G w) z = dirD v F z + dirD v G z := by
  unfold dirD
  rw [show (fun w => F w + G w) = F + G from rfl, (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv]
  simp

/-! ## Two termwise identities -/

theorem rpow_half_eq (y : ℝ) (hy : 0 < y) : y ^ (1 / 2 : ℝ) = y * y ^ (-(1 / 2) : ℝ) := by
  have h := Real.rpow_add hy (1 : ℝ) (-(1 / 2))
  rw [Real.rpow_one] at h
  rw [← h]
  norm_num

theorem rpow_half_eq_sq (y : ℝ) (hy : 0 < y) : y ^ (1 / 2 : ℝ) = y ^ 2 * y ^ (-(3 / 2) : ℝ) := by
  have h := Real.rpow_add hy (2 : ℝ) (-(3 / 2))
  rw [Real.rpow_two] at h
  rw [← h]
  norm_num

/-- Bessel's equation for the terms: `n²√y (K₂ − K₀)(2πny) = n K₁(2πny)/(2π√y)`. -/
theorem bterm_bessel (b : Bool) {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : 0 < z.im) :
    bterm (1 / 2) 2 2 b n z - bterm (1 / 2) 0 2 b n z =
      (1 / (2 * Real.pi)) * bterm (-(1 / 2)) 1 1 b n z := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < 2 * Real.pi * n * z.im := by positivity
  have hode := kMoment_ode hr
  unfold bterm yPart
  rw [rpow_half_eq z.im hz]
  have hK : kMoment 2 (2 * Real.pi * ↑n * z.im) - kMoment 0 (2 * Real.pi * ↑n * z.im) =
      kMoment 1 (2 * Real.pi * ↑n * z.im) / (2 * Real.pi * ↑n * z.im) := by
    field_simp
    linarith
  have : (n : ℝ) ^ 2 * (z.im * z.im ^ (-(1 / 2) : ℝ)) * kMoment 2 (2 * Real.pi * ↑n * z.im) *
        xPart b n z.re -
      (n : ℝ) ^ 2 * (z.im * z.im ^ (-(1 / 2) : ℝ)) * kMoment 0 (2 * Real.pi * ↑n * z.im) *
        xPart b n z.re =
      (n : ℝ) ^ 2 * (z.im * z.im ^ (-(1 / 2) : ℝ)) * xPart b n z.re *
        (kMoment 2 (2 * Real.pi * ↑n * z.im) - kMoment 0 (2 * Real.pi * ↑n * z.im)) := by ring
  rw [this, hK]
  field_simp

/-- `y^{1/2}/(4y²) = y^{−3/2}/4` for the terms. -/
theorem quarterWeight_bterm (b : Bool) (n : ℕ) {z : ℂ} (hz : 0 < z.im) :
    quarterWeight z * bterm (1 / 2) 0 0 b n z = (1 / 4) * bterm (-(3 / 2)) 0 0 b n z := by
  unfold quarterWeight bterm yPart
  rw [rpow_half_eq_sq z.im hz]
  field_simp

theorem besselSeries_bessel (hg : PolyGrowth g) (b : Bool) {z : ℂ} (hz : 0 < z.im) :
    besselSeries g (1 / 2) 2 2 b z - besselSeries g (1 / 2) 0 2 b z =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * besselSeries g (-(1 / 2)) 1 1 b z := by
  unfold besselSeries
  rw [← Summable.tsum_sub (summable_sterm hg _ _ _ _ hz) (summable_sterm hg _ _ _ _ hz),
    ← tsum_mul_left]
  congr 1
  funext n
  simp only [sterm]
  rw [← mul_sub, ← Complex.ofReal_sub, bterm_bessel b (Nat.succ_le_succ (Nat.zero_le n)) hz]
  push_cast
  ring

theorem quarterWeight_besselSeries (b : Bool) {z : ℂ} (hz : 0 < z.im) :
    quarterWeight z • besselSeries g (1 / 2) 0 0 b z =
      (1 / 4 : ℂ) * besselSeries g (-(3 / 2)) 0 0 b z := by
  unfold besselSeries
  rw [← tsum_mul_left, Complex.real_smul, ← tsum_mul_left]
  congr 1
  funext n
  simp only [sterm]
  have h := quarterWeight_bterm b (n + 1) hz
  have h' : ((quarterWeight z : ℝ) : ℂ) * (bterm (1 / 2) 0 0 b (n + 1) z : ℂ) =
      (1 / 4 : ℂ) * (bterm (-(3 / 2)) 0 0 b (n + 1) z : ℂ) := by
    rw [← Complex.ofReal_mul, h]; push_cast; ring
  linear_combination g (n + 1) * h'

/-! ## The quarter equation for the cosine series -/

/-- The cosine series `S₀ = Σ g_n √y K₀(2πny) cos(2πnx)`. -/
def cosSeries (g : ℕ → ℂ) : ℂ → ℂ := besselSeries g (1 / 2) 0 0 false

theorem quarterDefect_cosSeries (hg : PolyGrowth g) {z : ℂ} (hz : 0 < z.im) :
    quarterDefect (cosSeries g) z = 0 := by
  have hzU : z ∈ upper := hz
  -- first derivatives as functions on the upper half-plane
  have hx1 : EqOn (dirD 1 (cosSeries g))
      (fun w => ((2 * Real.pi * trigSign false : ℝ) : ℂ) * besselSeries g (1 / 2) 0 1 true w)
      upper := by
    intro w hw
    rw [cosSeries, dirD_one_besselSeries hg _ _ _ _ hw]
    rfl
  have hy1 : EqOn (dirD I (cosSeries g))
      (fun w => ((1 / 2 : ℝ) : ℂ) * besselSeries g (1 / 2 - 1) 0 0 false w -
        ((2 * Real.pi : ℝ) : ℂ) * besselSeries g (1 / 2) 1 1 false w) upper := by
    intro w hw
    rw [cosSeries, dirD_I_besselSeries hg _ _ _ _ hw]
    rfl
  have hxx : dirD 1 (dirD 1 (cosSeries g)) z =
      ((2 * Real.pi * trigSign false : ℝ) : ℂ) *
        (((2 * Real.pi * trigSign true : ℝ) : ℂ) * besselSeries g (1 / 2) 0 2 false z) := by
    rw [dirD_congr hx1 hzU, dirD_const_mul (differentiableAt_besselSeries hg _ _ _ _ hz),
      dirD_one_besselSeries hg _ _ _ _ hz]
    rfl
  have hyy : dirD I (dirD I (cosSeries g)) z =
      ((1 / 2 : ℝ) : ℂ) * (((1 / 2 - 1 : ℝ) : ℂ) * besselSeries g (1 / 2 - 1 - 1) 0 0 false z -
          ((2 * Real.pi : ℝ) : ℂ) * besselSeries g (1 / 2 - 1) 1 1 false z) -
        ((2 * Real.pi : ℝ) : ℂ) * (((1 / 2 : ℝ) : ℂ) * besselSeries g (1 / 2 - 1) 1 1 false z -
          ((2 * Real.pi : ℝ) : ℂ) * besselSeries g (1 / 2) (1 + 1) (1 + 1) false z) := by
    rw [dirD_congr hy1 hzU,
      dirD_sub ((differentiableAt_besselSeries hg _ _ _ _ hz).const_mul _)
        ((differentiableAt_besselSeries hg _ _ _ _ hz).const_mul _),
      dirD_const_mul (differentiableAt_besselSeries hg _ _ _ _ hz),
      dirD_const_mul (differentiableAt_besselSeries hg _ _ _ _ hz),
      dirD_I_besselSeries hg _ _ _ _ hz, dirD_I_besselSeries hg _ _ _ _ hz]
    rfl
  have hB := besselSeries_bessel hg false hz
  have hW := quarterWeight_besselSeries (g := g) false hz
  have hB' : besselSeries g (1 / 2) 2 2 false z = besselSeries g (1 / 2) 0 2 false z +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * besselSeries g (-(1 / 2)) 1 1 false z := by
    rw [← hB]; ring
  have e1 : (1 / 2 - 1 - 1 : ℝ) = -(3 / 2) := by norm_num
  have e2 : (1 / 2 - 1 : ℝ) = -(1 / 2) := by norm_num
  unfold quarterDefect
  rw [hxx, hyy, show cosSeries g z = besselSeries g (1 / 2) 0 0 false z from rfl, hW, e1, e2,
    show (1 + 1 : ℕ) = 2 from rfl, hB']
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [trigSign, Bool.false_eq_true, ↓reduceIte]
  push_cast
  field_simp
  ring

/-! ## The constant term -/

/-- `√y`. -/
def sqrtPart (y : ℝ) : ℝ := y ^ (1 / 2 : ℝ)

/-- `√y log y`. -/
def sqrtLogPart (y : ℝ) : ℝ := y ^ (1 / 2 : ℝ) * Real.log y

/-- The constant term `√y (b + a log y)`. -/
def constTerm (a b : ℂ) (z : ℂ) : ℂ := b * (sqrtPart z.im : ℂ) + a * (sqrtLogPart z.im : ℂ)

theorem hasDerivAt_sqrtPart {y : ℝ} (hy : 0 < y) :
    HasDerivAt sqrtPart ((1 / 2) * y ^ (-(1 / 2) : ℝ)) y := by
  have := Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ)) (Or.inl hy.ne')
  unfold sqrtPart
  convert this using 2
  norm_num

theorem hasDerivAt_sqrtLogPart {y : ℝ} (hy : 0 < y) :
    HasDerivAt sqrtLogPart ((1 / 2) * y ^ (-(1 / 2) : ℝ) * Real.log y + y ^ (-(1 / 2) : ℝ)) y := by
  have h1 := hasDerivAt_sqrtPart hy
  have h2 := Real.hasDerivAt_log hy.ne'
  have := h1.mul h2
  refine this.congr_deriv ?_
  unfold sqrtPart
  rw [rpow_half_eq y hy]
  field_simp

theorem hasDerivAt_sqrtPart_deriv {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => (1 / 2) * y ^ (-(1 / 2) : ℝ))
      (-(sqrtPart y) / (4 * y ^ 2)) y := by
  have := (Real.hasDerivAt_rpow_const (p := (-(1 / 2) : ℝ)) (Or.inl hy.ne')).const_mul (1 / 2 : ℝ)
  refine this.congr_deriv ?_
  unfold sqrtPart
  rw [rpow_half_eq_sq y hy, show (-(1 / 2) : ℝ) - 1 = -(3 / 2) by norm_num]
  field_simp
  ring

theorem hasDerivAt_sqrtLogPart_deriv {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => (1 / 2) * y ^ (-(1 / 2) : ℝ) * Real.log y + y ^ (-(1 / 2) : ℝ))
      (-(sqrtLogPart y) / (4 * y ^ 2)) y := by
  have hp : HasDerivAt (fun y : ℝ => y ^ (-(1 / 2) : ℝ))
      ((-(1 / 2) : ℝ) * y ^ ((-(1 / 2) : ℝ) - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl hy.ne')
  have hl := Real.hasDerivAt_log hy.ne'
  have := ((hp.const_mul (1 / 2 : ℝ)).mul hl).add hp
  refine this.congr_deriv ?_
  unfold sqrtLogPart
  have e1 : y ^ ((-(1 / 2) : ℝ) - 1) = y ^ (-(3 / 2) : ℝ) := by norm_num
  have e2 : y ^ (-(1 / 2) : ℝ) = y * y ^ (-(3 / 2) : ℝ) := by
    rw [show (-(1 / 2) : ℝ) = 1 + (-(3 / 2)) by norm_num, Real.rpow_add hy, Real.rpow_one]
  rw [e1, e2, rpow_half_eq_sq y hy]
  field_simp
  ring

/-- A function of `y` only, with its derivatives. -/
theorem hasFDerivAt_of_im {φ : ℝ → ℝ} {φ' : ℝ} {z : ℂ} (h : HasDerivAt φ φ' z.im) (c : ℂ) :
    HasFDerivAt (fun w : ℂ => c * (φ w.im : ℂ)) ((c * φ') • imL) z := by
  have h1 := (h.comp_hasFDerivAt z imCLM.hasFDerivAt)
  have h2 := (ofRealCLM.hasFDerivAt.comp z h1).const_mul c
  refine h2.congr_fderiv ?_
  ext v
  simp [imL]
  ring

theorem dirD_one_of_im {φ : ℝ → ℝ} {φ' : ℝ} {z : ℂ} (h : HasDerivAt φ φ' z.im) (c : ℂ) :
    dirD 1 (fun w : ℂ => c * (φ w.im : ℂ)) z = 0 := by
  unfold dirD
  rw [(hasFDerivAt_of_im h c).fderiv]
  simp

theorem dirD_I_of_im {φ : ℝ → ℝ} {φ' : ℝ} {z : ℂ} (h : HasDerivAt φ φ' z.im) (c : ℂ) :
    dirD I (fun w : ℂ => c * (φ w.im : ℂ)) z = c * φ' := by
  unfold dirD
  rw [(hasFDerivAt_of_im h c).fderiv]
  simp

theorem differentiableAt_of_im {φ : ℝ → ℝ} {φ' : ℝ} {z : ℂ} (h : HasDerivAt φ φ' z.im) (c : ℂ) :
    DifferentiableAt ℝ (fun w : ℂ => c * (φ w.im : ℂ)) z :=
  (hasFDerivAt_of_im h c).differentiableAt

theorem quarterDefect_constTerm (a b : ℂ) {z : ℂ} (hz : 0 < z.im) :
    quarterDefect (constTerm a b) z = 0 := by
  have hzU : z ∈ upper := hz
  have hR : ∀ w : ℂ, 0 < w.im → HasDerivAt sqrtPart ((1 / 2) * w.im ^ (-(1 / 2) : ℝ)) w.im :=
    fun w hw => hasDerivAt_sqrtPart hw
  have hL : ∀ w : ℂ, 0 < w.im → HasDerivAt sqrtLogPart
      ((1 / 2) * w.im ^ (-(1 / 2) : ℝ) * Real.log w.im + w.im ^ (-(1 / 2) : ℝ)) w.im :=
    fun w hw => hasDerivAt_sqrtLogPart hw
  have hc : constTerm a b = fun w => b * (sqrtPart w.im : ℂ) + a * (sqrtLogPart w.im : ℂ) := rfl
  -- `∂₁ c = 0` on the upper half-plane
  have h1 : EqOn (dirD 1 (constTerm a b)) (fun _ => 0) upper := by
    intro w hw
    rw [hc, dirD_add (differentiableAt_of_im (hR w hw) b) (differentiableAt_of_im (hL w hw) a),
      dirD_one_of_im (hR w hw), dirD_one_of_im (hL w hw), add_zero]
  -- `∂ᵢ c = c'(y)`
  have hI : EqOn (dirD I (constTerm a b))
      (fun w => b * (((1 / 2) * w.im ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) +
        a * (((1 / 2) * w.im ^ (-(1 / 2) : ℝ) * Real.log w.im + w.im ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))
      upper := by
    intro w hw
    rw [hc, dirD_add (differentiableAt_of_im (hR w hw) b) (differentiableAt_of_im (hL w hw) a),
      dirD_I_of_im (hR w hw), dirD_I_of_im (hL w hw)]
  have hxx : dirD 1 (dirD 1 (constTerm a b)) z = 0 := by
    rw [dirD_congr h1 hzU]; simp [dirD]
  have hR2 := hasDerivAt_sqrtPart_deriv hz
  have hL2 := hasDerivAt_sqrtLogPart_deriv hz
  have hyy : dirD I (dirD I (constTerm a b)) z =
      b * ((-(sqrtPart z.im) / (4 * z.im ^ 2) : ℝ) : ℂ) +
        a * ((-(sqrtLogPart z.im) / (4 * z.im ^ 2) : ℝ) : ℂ) := by
    rw [dirD_congr hI hzU,
      dirD_add (differentiableAt_of_im (φ := fun y : ℝ => (1 / 2) * y ^ (-(1 / 2) : ℝ)) hR2 b)
        (differentiableAt_of_im (φ := fun y : ℝ => (1 / 2) * y ^ (-(1 / 2) : ℝ) * Real.log y +
          y ^ (-(1 / 2) : ℝ)) hL2 a),
      dirD_I_of_im (φ := fun y : ℝ => (1 / 2) * y ^ (-(1 / 2) : ℝ)) hR2,
      dirD_I_of_im (φ := fun y : ℝ => (1 / 2) * y ^ (-(1 / 2) : ℝ) * Real.log y +
          y ^ (-(1 / 2) : ℝ)) hL2]
  unfold quarterDefect
  rw [hxx, hyy, hc]
  simp only [quarterWeight, Complex.real_smul]
  have hy0 : z.im ≠ 0 := ne_of_gt hz
  push_cast
  field_simp
  ring

/-! ## The Maass function -/

/-- `u(x + iy) = 4 Σ g_n √y K₀(2πny) cos(2πnx) + √y (b + a log y)`. -/
def maassFun (g : ℕ → ℂ) (a b : ℂ) (z : ℂ) : ℂ := 4 * cosSeries g z + constTerm a b z

theorem contDiffOn_constTerm (a b : ℂ) : ContDiffOn ℝ ∞ (constTerm a b) upper := by
  have hR : ContDiffOn ℝ ∞ (fun w : ℂ => sqrtPart w.im) upper := by
    intro w hw
    have hw' : 0 < w.im := hw
    refine ContDiffAt.contDiffWithinAt ?_
    unfold sqrtPart
    exact (contDiffAt_id.rpow_const_of_ne (by exact ne_of_gt hw')).comp w
      imCLM.contDiff.contDiffAt
  have hL : ContDiffOn ℝ ∞ (fun w : ℂ => sqrtLogPart w.im) upper := by
    intro w hw
    have hw' : 0 < w.im := hw
    refine ContDiffAt.contDiffWithinAt ?_
    unfold sqrtLogPart
    exact ((contDiffAt_id.rpow_const_of_ne (by exact ne_of_gt hw')).mul
      (Real.contDiffAt_log.mpr (ne_of_gt hw'))).comp w imCLM.contDiff.contDiffAt
  have hRc := (ofRealCLM.contDiff.comp_contDiffOn hR).const_smul b
  have hLc := (ofRealCLM.contDiff.comp_contDiffOn hL).const_smul a
  refine (hRc.add hLc).congr fun w _ => ?_
  simp [constTerm, smul_eq_mul]

theorem contDiffOn_maassFun (hg : PolyGrowth g) (a b : ℂ) :
    ContDiffOn ℝ ∞ (maassFun g a b) upper := by
  have hS := contDiffOn_of_mem_besselSpan hg (seriesOf_mem g (1 / 2, 0, 0, false))
  exact ((hS.const_smul (4 : ℂ)).add (contDiffOn_constTerm a b)).congr fun w _ => by
    simp [maassFun, cosSeries, seriesOf, smul_eq_mul]

/-- The quarter defect is additive on smooth functions. -/
theorem quarterDefect_add {F G : ℂ → ℂ} (hF : ContDiffOn ℝ ∞ F upper) (hG : ContDiffOn ℝ ∞ G upper)
    {z : ℂ} (hz : z ∈ upper) :
    quarterDefect (fun w => F w + G w) z = quarterDefect F z + quarterDefect G z := by
  have hd : ∀ {H : ℂ → ℂ}, ContDiffOn ℝ ∞ H upper → ∀ w ∈ upper, DifferentiableAt ℝ H w :=
    fun hH w hw => differentiableAt_of_contDiffOn hH hw
  have h1 : ∀ v : ℂ, EqOn (dirD v (fun w => F w + G w)) (fun w => dirD v F w + dirD v G w) upper :=
    fun v w hw => dirD_add (hd hF w hw) (hd hG w hw) v
  have h2 : ∀ v : ℂ, dirD v (dirD v (fun w => F w + G w)) z =
      dirD v (dirD v F) z + dirD v (dirD v G) z := by
    intro v
    rw [dirD_congr (h1 v) hz, dirD_add (hd (contDiffOn_dirD hF v) z hz)
      (hd (contDiffOn_dirD hG v) z hz)]
  unfold quarterDefect
  rw [h2 1, h2 I, smul_add]
  ring

/-- The quarter defect commutes with constant multiples on smooth functions. -/
theorem quarterDefect_const_mul {F : ℂ → ℂ} (hF : ContDiffOn ℝ ∞ F upper) (c : ℂ) {z : ℂ}
    (hz : z ∈ upper) : quarterDefect (fun w => c * F w) z = c * quarterDefect F z := by
  have hd : ∀ {H : ℂ → ℂ}, ContDiffOn ℝ ∞ H upper → ∀ w ∈ upper, DifferentiableAt ℝ H w :=
    fun hH w hw => differentiableAt_of_contDiffOn hH hw
  have h1 : ∀ v : ℂ, EqOn (dirD v (fun w => c * F w)) (fun w => c * dirD v F w) upper :=
    fun v w hw => dirD_const_mul (hd hF w hw) c v
  have h2 : ∀ v : ℂ, dirD v (dirD v (fun w => c * F w)) z = c * dirD v (dirD v F) z := by
    intro v
    rw [dirD_congr (h1 v) hz, dirD_const_mul (hd (contDiffOn_dirD hF v) z hz)]
  unfold quarterDefect
  rw [h2 1, h2 I, Complex.real_smul, Complex.real_smul]
  ring

/-- **`u` is a quarter eigenfunction.** -/
theorem quarterDefect_maassFun (hg : PolyGrowth g) (a b : ℂ) {z : ℂ} (hz : 0 < z.im) :
    quarterDefect (maassFun g a b) z = 0 := by
  have hzU : z ∈ upper := hz
  have hS : ContDiffOn ℝ ∞ (cosSeries g) upper :=
    contDiffOn_of_mem_besselSpan hg (seriesOf_mem g (1 / 2, 0, 0, false))
  have hS4 : ContDiffOn ℝ ∞ (fun w => 4 * cosSeries g w) upper :=
    (hS.const_smul (4 : ℂ)).congr fun w _ => by simp [smul_eq_mul]
  rw [show maassFun g a b = fun w => 4 * cosSeries g w + constTerm a b w from rfl,
    quarterDefect_add hS4 (contDiffOn_constTerm a b) hzU, quarterDefect_const_mul hS 4 hzU,
    quarterDefect_cosSeries hg hz, quarterDefect_constTerm a b hz]
  ring

/-! ## Symmetries -/

theorem trigFun_false_neg (θ : ℝ) : trigFun false (-θ) = trigFun false θ := by
  simp [trigFun]

theorem bterm_neg_conj (α : ℝ) (j k n : ℕ) (z : ℂ) :
    bterm α j k false n (-(starRingEnd ℂ) z) = bterm α j k false n z := by
  unfold bterm xPart
  simp only [neg_im, conj_im, neg_neg, neg_re, conj_re]
  rw [show 2 * Real.pi * n * -z.re = -(2 * Real.pi * n * z.re) by ring, trigFun_false_neg]

theorem bterm_add_one (α : ℝ) (j k n : ℕ) (z : ℂ) :
    bterm α j k false n (z + 1) = bterm α j k false n z := by
  unfold bterm xPart trigFun
  simp only [add_im, one_im, add_zero, add_re, one_re, Bool.false_eq_true, ↓reduceIte]
  rw [show 2 * Real.pi * n * (z.re + 1) = 2 * Real.pi * n * z.re + (n : ℕ) * (2 * Real.pi) by ring,
    Real.cos_add_nat_mul_two_pi]

theorem constTerm_neg_conj (a b : ℂ) (z : ℂ) : constTerm a b (-(starRingEnd ℂ) z) = constTerm a b z := by
  simp [constTerm]

theorem constTerm_add_one (a b : ℂ) (z : ℂ) : constTerm a b (z + 1) = constTerm a b z := by
  simp [constTerm]

/-- **`u(−z̄) = u(z)`.** -/
theorem maassFun_neg_conj (a b : ℂ) (z : ℂ) :
    maassFun g a b (-(starRingEnd ℂ) z) = maassFun g a b z := by
  simp only [maassFun, cosSeries, besselSeries, sterm, bterm_neg_conj, constTerm_neg_conj]

/-- **`u(z + 1) = u(z)`.** -/
theorem maassFun_add_one (a b : ℂ) (z : ℂ) : maassFun g a b (z + 1) = maassFun g a b z := by
  simp only [maassFun, cosSeries, besselSeries, sterm, bterm_add_one, constTerm_add_one]

end RHTower.MaassBesselSeries
