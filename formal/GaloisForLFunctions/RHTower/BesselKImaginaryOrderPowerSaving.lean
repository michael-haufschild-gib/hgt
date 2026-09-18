import GaloisForLFunctions.RHTower.BesselKImaginaryOrderUniformBound
import GaloisForLFunctions.RHTower.VanDerCorput

/-!
# A power saving in the order for the modified Bessel function of imaginary order

On the contour `Im w = θ` the Schläfli integrand of `K_{iτ}(x)` factors as `e^{-τθ}` times the
weight `exp(-x cos θ cosh u)` times the phase `exp(i(τu - x sin θ sinh u))`.  The weight lies in
`(0, 1]` and is antitone on the half line, so the van der Corput derivative tests apply to the
phase `ψ(u) = x sin θ sinh u - τu`, whose derivatives are `ψ' = X cosh u - τ` and
`ψ'' = X sinh u` with `X = x sin θ`.

* For `X ≤ τ/4` the phase has a nondegenerate stationary point: on `[0, arcosh(τ/2X)]` and on
  `[arcosh(2τ/X), ∞)` the frequency `|ψ'|` is at least `τ/2`, and in between `ψ'' ≥ τ/4`; the
  first- and second-derivative tests give `O(τ^{-1/2})`.
* For `τ/4 < x ≤ 2τ` the second derivative vanishes only at `u = 0`; splitting at
  `u = X^{-1/3}` gives `O(X^{-1/3})`.

With `θ = π/2 - 1/τ` this yields `‖K_{iτ}(x)‖ ≤ 420 e^{-πτ/2} τ^{-1/3}` for all `0 < x ≤ 2τ`,
`τ ≥ 2`, and `‖K_{iτ}(x)‖ ≤ 152 e · e^{-πτ/2} τ^{-1/2}` for `x ≤ τ/4`.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The shifted integrand as weight times phase -/

/-- The weight `exp(-c cosh u)` of the shifted Schläfli integrand. -/
def besselShiftWeight (c u : ℝ) : ℝ := Real.exp (-c * Real.cosh u)

/-- The phase `τu - X sinh u` of the shifted Schläfli integrand. -/
def besselShiftPhase (τ X u : ℝ) : ℝ := τ * u - X * Real.sinh u

/-- The reversed phase `X sinh u - τu`, to which the derivative tests are applied. -/
def besselShiftPsi (τ X u : ℝ) : ℝ := X * Real.sinh u - τ * u

theorem besselShiftPsi_eq_neg (τ X u : ℝ) : besselShiftPsi τ X u = -besselShiftPhase τ X u := by
  unfold besselShiftPsi besselShiftPhase; ring

theorem besselShiftWeight_pos (c u : ℝ) : 0 < besselShiftWeight c u := Real.exp_pos _

theorem besselShiftWeight_le_one {c : ℝ} (hc : 0 ≤ c) (u : ℝ) : besselShiftWeight c u ≤ 1 := by
  unfold besselShiftWeight
  rw [Real.exp_le_one_iff]
  have := Real.cosh_pos u
  nlinarith

theorem besselShiftWeight_neg (c u : ℝ) : besselShiftWeight c (-u) = besselShiftWeight c u := by
  unfold besselShiftWeight; rw [Real.cosh_neg]

theorem besselShiftPhase_neg (τ X u : ℝ) : besselShiftPhase τ X (-u) = -besselShiftPhase τ X u := by
  unfold besselShiftPhase; rw [Real.sinh_neg]; ring

theorem besselOrderEntireKernel_shift_eq (x τ θ u : ℝ) :
    besselOrderEntireKernel x ((τ : ℂ) * I) ((u : ℂ) + (θ : ℂ) * I) =
      ((Real.exp (-τ * θ) : ℝ) : ℂ) * ((besselShiftWeight (x * Real.cos θ) u : ℝ) : ℂ) *
        Complex.exp (I * ((besselShiftPhase τ (x * Real.sin θ) u : ℝ) : ℂ)) := by
  unfold besselOrderEntireKernel besselShiftWeight besselShiftPhase
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.ofReal_exp,
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination ((τ : ℂ) * (θ : ℂ)) * Complex.I_sq

/-- Conjugation commutes with interval integrals. -/
theorem intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, (starRingEnd ℂ) (f x) = (starRingEnd ℂ) (∫ x in a..b, f x) := by
  rw [intervalIntegral, intervalIntegral, integral_conj, integral_conj, map_sub]

/-- The half-line integral of the weight times the phase, the quantity bounded below. -/
def besselShiftHalfLine (c τ X : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), ((besselShiftWeight c u : ℝ) : ℂ) *
    Complex.exp (I * ((besselShiftPhase τ X u : ℝ) : ℂ))

/-- **Reduction to the half line.**  `‖K_{iτ}(x)‖ ≤ e^{-τθ} ‖∫_0^∞ w e^{iφ}‖`. -/
theorem norm_modifiedBesselKOrder_I_mul_le_halfLine {x : ℝ} (hx : 0 < x) (τ : ℝ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi / 2) :
    ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖ ≤
      Real.exp (-τ * θ) * ‖besselShiftHalfLine (x * Real.cos θ) τ (x * Real.sin θ)‖ := by
  set g : ℝ → ℂ := fun u => ((besselShiftWeight (x * Real.cos θ) u : ℝ) : ℂ) *
    Complex.exp (I * ((besselShiftPhase τ (x * Real.sin θ) u : ℝ) : ℂ)) with hg
  set f : ℝ → ℂ := fun u => besselOrderEntireKernel x ((τ : ℂ) * I) ((u : ℂ) + (θ : ℂ) * I)
    with hf
  have hfg : ∀ u, f u = ((Real.exp (-τ * θ) : ℝ) : ℂ) * g u := fun u => by
    simp only [hf, hg]; rw [besselOrderEntireKernel_shift_eq]; ring
  have hfint : Integrable f := integrable_shifted_besselOrderEntireKernel hx _ hθ0 hθ
  have h2K : (∫ u, f u) = 2 * modifiedBesselKOrder x ((τ : ℂ) * I) := by
    rw [← integral_besselOrderExpKernel_eq_two_mul hx,
      integral_besselOrderExpKernel_eq_shifted hx _ hθ0 hθ]
  have hsymm : ∀ u, f (-u) = (starRingEnd ℂ) (f u) := by
    intro u
    rw [hfg, hfg, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.exp_conj,
      map_mul, Complex.conj_I, Complex.conj_ofReal]
    simp only [hg, besselShiftWeight_neg, besselShiftPhase_neg]
    push_cast
    ring_nf
  have hsplit : (∫ u, f u) = (∫ u in Ioi (0 : ℝ), f u) + (starRingEnd ℂ) (∫ u in Ioi (0 : ℝ), f u) := by
    rw [← integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hfint, compl_Ioi]
    congr 1
    rw [← integral_conj]
    have h := integral_comp_neg_Ioi (0 : ℝ) f
    rw [neg_zero] at h
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => hsymm u)
  have hJ : (∫ u in Ioi (0 : ℝ), f u) = ((Real.exp (-τ * θ) : ℝ) : ℂ) * besselShiftHalfLine
      (x * Real.cos θ) τ (x * Real.sin θ) := by
    unfold besselShiftHalfLine
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun u _ => hfg u
  rw [Complex.add_conj, h2K] at hsplit
  have hK : modifiedBesselKOrder x ((τ : ℂ) * I) =
      (((∫ u in Ioi (0 : ℝ), f u).re : ℝ) : ℂ) := by
    have h2 : (2 : ℂ) * modifiedBesselKOrder x ((τ : ℂ) * I) =
        (2 : ℂ) * (((∫ u in Ioi (0 : ℝ), f u).re : ℝ) : ℂ) := by
      rw [hsplit]; push_cast; ring
    exact mul_left_cancel₀ two_ne_zero h2
  rw [hK, Complex.norm_real, Real.norm_eq_abs]
  calc |(∫ u in Ioi (0 : ℝ), f u).re| ≤ ‖∫ u in Ioi (0 : ℝ), f u‖ := Complex.abs_re_le_norm _
    _ = Real.exp (-τ * θ) * ‖besselShiftHalfLine (x * Real.cos θ) τ (x * Real.sin θ)‖ := by
        rw [hJ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-! ## Smoothness data for the weight and the reversed phase -/

theorem hasDerivAt_besselShiftWeight (c u : ℝ) :
    HasDerivAt (besselShiftWeight c) (besselShiftWeight c u * (-c * Real.sinh u)) u := by
  unfold besselShiftWeight
  exact ((Real.hasDerivAt_cosh u).const_mul (-c)).exp

theorem contDiff_besselShiftWeight (c : ℝ) : ContDiff ℝ 1 (besselShiftWeight c) := by
  unfold besselShiftWeight
  exact ((contDiff_const (c := -c)).mul Real.contDiff_cosh).exp

/-- The complexified weight, the amplitude of the oscillatory integrals. -/
def besselShiftAmp (c : ℝ) : ℝ → ℂ := fun u => ((besselShiftWeight c u : ℝ) : ℂ)

theorem contDiff_besselShiftAmp (c : ℝ) : ContDiff ℝ 1 (besselShiftAmp c) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_besselShiftWeight c)

theorem deriv_besselShiftAmp (c u : ℝ) :
    deriv (besselShiftAmp c) u = ((besselShiftWeight c u * (-c * Real.sinh u) : ℝ) : ℂ) :=
  ((hasDerivAt_besselShiftWeight c u).ofReal_comp).deriv

theorem norm_besselShiftAmp_le {c : ℝ} (hc : 0 ≤ c) (u : ℝ) : ‖besselShiftAmp c u‖ ≤ 1 := by
  unfold besselShiftAmp
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (besselShiftWeight_pos c u)]
  exact besselShiftWeight_le_one hc u

/-- The amplitude budget of the derivative tests is at most `2` on `[a, b] ⊂ [0, ∞)`. -/
theorem besselShiftAmp_budget_le {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖besselShiftAmp c b‖ + ‖besselShiftAmp c a‖ +
      ∫ u in a..b, ‖deriv (besselShiftAmp c) u‖ ≤ 2 := by
  have hderiv : ∀ u ∈ Set.uIcc a b, HasDerivAt (besselShiftWeight c)
      (besselShiftWeight c u * (-c * Real.sinh u)) u := fun u _ => hasDerivAt_besselShiftWeight c u
  have hcont : Continuous fun u => besselShiftWeight c u * (-c * Real.sinh u) := by
    unfold besselShiftWeight; fun_prop
  have hFTC : ∫ u in a..b, besselShiftWeight c u * (-c * Real.sinh u) =
      besselShiftWeight c b - besselShiftWeight c a :=
    integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a b)
  have hnorm : ∀ u ∈ Set.uIcc a b, ‖deriv (besselShiftAmp c) u‖ =
      -(besselShiftWeight c u * (-c * Real.sinh u)) := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : 0 ≤ u := le_trans ha hu.1
    have hs : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu0
    have hw := besselShiftWeight_pos c u
    rw [deriv_besselShiftAmp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
    nlinarith [mul_nonneg hc hs]
  have hint : ∫ u in a..b, ‖deriv (besselShiftAmp c) u‖ =
      besselShiftWeight c a - besselShiftWeight c b := by
    rw [integral_congr hnorm, intervalIntegral.integral_neg, hFTC]; ring
  rw [hint]
  have h1 := norm_besselShiftAmp_le hc a
  have h2 := norm_besselShiftAmp_le hc b
  have h3 : ‖besselShiftAmp c a‖ = besselShiftWeight c a := by
    unfold besselShiftAmp
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (besselShiftWeight_pos c a)]
  have h4 : ‖besselShiftAmp c b‖ = besselShiftWeight c b := by
    unfold besselShiftAmp
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (besselShiftWeight_pos c b)]
  rw [h3, h4]
  have := besselShiftWeight_le_one hc a
  linarith

theorem hasDerivAt_besselShiftPsi (τ X u : ℝ) :
    HasDerivAt (besselShiftPsi τ X) (X * Real.cosh u - τ) u := by
  unfold besselShiftPsi
  have h1 : HasDerivAt (fun y : ℝ => X * Real.sinh y) (X * Real.cosh u) u :=
    (Real.hasDerivAt_sinh u).const_mul X
  have h2 : HasDerivAt (fun y : ℝ => τ * y) τ u := by
    simpa using (hasDerivAt_id u).const_mul τ
  exact h1.sub h2

theorem deriv_besselShiftPsi (τ X : ℝ) :
    deriv (besselShiftPsi τ X) = fun u => X * Real.cosh u - τ :=
  funext fun u => (hasDerivAt_besselShiftPsi τ X u).deriv

theorem deriv_deriv_besselShiftPsi (τ X u : ℝ) :
    deriv (deriv (besselShiftPsi τ X)) u = X * Real.sinh u := by
  rw [deriv_besselShiftPsi]
  have h := ((Real.hasDerivAt_cosh u).const_mul X).sub_const τ
  exact h.deriv

theorem contDiff_besselShiftPsi (τ X : ℝ) : ContDiff ℝ 2 (besselShiftPsi τ X) := by
  unfold besselShiftPsi
  exact ((contDiff_const (c := X)).mul Real.contDiff_sinh).sub ((contDiff_const (c := τ)).mul contDiff_id)

/-- The oscillatory integral of the weight against the phase is the conjugate of the one against
the reversed phase. -/
theorem intervalIntegral_weight_phase_eq_conj (c τ X a b : ℝ) :
    ∫ u in a..b, ((besselShiftWeight c u : ℝ) : ℂ) *
        Complex.exp (I * ((besselShiftPhase τ X u : ℝ) : ℂ)) =
      (starRingEnd ℂ) (∫ u in a..b, besselShiftAmp c u *
        Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ))) := by
  rw [← intervalIntegral_conj]
  refine integral_congr fun u _ => ?_
  unfold besselShiftAmp
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, besselShiftPsi_eq_neg]
  push_cast
  ring_nf

/-! ## The bulk regime `X ≤ τ/4`: a nondegenerate stationary point -/

/-- The oscillatory integral against the reversed phase on `[0, b]`, `b ≥ arcosh(2τ/X)`, in the
bulk regime. -/
theorem norm_intervalIntegral_psi_le_bulk {c τ X : ℝ} (hc : 0 ≤ c) (hτ : 1 ≤ τ) (hX : 0 < X)
    (hXτ : X ≤ τ / 4) {b : ℝ} (hb : Real.arcosh (2 * τ / X) ≤ b) :
    ‖∫ u in (0 : ℝ)..b, besselShiftAmp c u *
        Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ))‖ ≤ 152 / Real.sqrt τ := by
  have hτ0 : 0 < τ := by linarith
  set u₁ : ℝ := Real.arcosh (τ / (2 * X)) with hu₁
  set u₂ : ℝ := Real.arcosh (2 * τ / X) with hu₂
  have h1 : 1 ≤ τ / (2 * X) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have h2 : 1 ≤ 2 * τ / X := by
    rw [le_div_iff₀ hX]; linarith
  have hcosh₁ : Real.cosh u₁ = τ / (2 * X) := Real.cosh_arcosh h1
  have hcosh₂ : Real.cosh u₂ = 2 * τ / X := Real.cosh_arcosh h2
  have hu₁0 : 0 ≤ u₁ := Real.arcosh_nonneg h1
  have hu₂0 : 0 ≤ u₂ := Real.arcosh_nonneg h2
  have hu₁₂ : u₁ ≤ u₂ := by
    have hle : Real.cosh u₁ ≤ Real.cosh u₂ := by
      rw [hcosh₁, hcosh₂, div_le_div_iff₀ (by positivity) hX]; nlinarith
    rw [Real.cosh_le_cosh, abs_of_nonneg hu₁0, abs_of_nonneg hu₂0] at hle
    exact hle
  have hψ := contDiff_besselShiftPsi τ X
  have hA := contDiff_besselShiftAmp c
  have hcontI : Continuous fun u => besselShiftAmp c u *
      Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ)) := by
    have := hA.continuous
    have := hψ.continuous
    fun_prop
  -- piece one: `[0, u₁]`, frequency at least `τ/2`
  have hp1 : ‖∫ u in (0 : ℝ)..u₁, besselShiftAmp c u *
      Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ))‖ ≤ 16 / τ := by
    have hnn : ∀ t ∈ Icc (0 : ℝ) u₁, 0 ≤ deriv (deriv (besselShiftPsi τ X)) t := by
      intro t ht
      rw [deriv_deriv_besselShiftPsi]
      exact mul_nonneg hX.le (Real.sinh_nonneg_iff.mpr ht.1)
    have hbd : ∀ t ∈ Icc (0 : ℝ) u₁, τ / 2 ≤ |deriv (besselShiftPsi τ X) t| := by
      intro t ht
      rw [deriv_besselShiftPsi]
      have hct : Real.cosh t ≤ Real.cosh u₁ := by
        rw [Real.cosh_le_cosh, abs_of_nonneg ht.1, abs_of_nonneg hu₁0]; exact ht.2
      have hXc : X * Real.cosh t ≤ τ / 2 := by
        calc X * Real.cosh t ≤ X * Real.cosh u₁ := mul_le_mul_of_nonneg_left hct hX.le
          _ = τ / 2 := by rw [hcosh₁]; field_simp
      rw [abs_of_nonpos (by linarith)]
      linarith
    have h := _root_.RHTower.firstDerivTest hu₁0 (by positivity : 0 < τ / 2) hψ hnn hbd hA
    have hbudget := besselShiftAmp_budget_le hc le_rfl hu₁0
    calc _ ≤ 4 * (‖besselShiftAmp c u₁‖ + ‖besselShiftAmp c 0‖ +
          ∫ t in (0 : ℝ)..u₁, ‖deriv (besselShiftAmp c) t‖) / (τ / 2) := h
      _ ≤ 4 * 2 / (τ / 2) := by gcongr
      _ = 16 / τ := by field_simp; norm_num
  -- piece two: `[u₁, u₂]`, second derivative at least `τ/4`
  have hp2 : ‖∫ u in u₁..u₂, besselShiftAmp c u *
      Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ))‖ ≤ 128 / Real.sqrt τ := by
    have hbd : ∀ t ∈ Icc u₁ u₂, τ / 4 ≤ deriv (deriv (besselShiftPsi τ X)) t := by
      intro t ht
      rw [deriv_deriv_besselShiftPsi]
      have ht0 : 0 ≤ t := le_trans hu₁0 ht.1
      have hs : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht0
      have hct : Real.cosh u₁ ≤ Real.cosh t := by
        rw [Real.cosh_le_cosh, abs_of_nonneg ht0, abs_of_nonneg hu₁0]; exact ht.1
      have hXc : τ / 2 ≤ X * Real.cosh t := by
        calc τ / 2 = X * Real.cosh u₁ := by rw [hcosh₁]; field_simp
          _ ≤ X * Real.cosh t := mul_le_mul_of_nonneg_left hct hX.le
      have hsq : (τ / 4) ^ 2 ≤ (X * Real.sinh t) ^ 2 := by
        have hc2 : (X * Real.sinh t) ^ 2 = (X * Real.cosh t) ^ 2 - X ^ 2 := by
          have := Real.cosh_sq t
          nlinarith [this]
        rw [hc2]
        nlinarith [mul_nonneg hX.le hs]
      exact (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg hX.le hs) two_ne_zero).mp hsq
    have h := _root_.RHTower.secondDerivTest hu₁₂ (by positivity : 0 < τ / 4) hψ hbd hA
    have hbudget := besselShiftAmp_budget_le hc hu₁0 hu₁₂
    have hsqrt : Real.sqrt (τ / 4) = Real.sqrt τ / 2 := by
      rw [show τ / 4 = τ / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num), Real.sqrt_sq
        (by norm_num)]
    calc _ ≤ 32 * (‖besselShiftAmp c u₂‖ + ‖besselShiftAmp c u₁‖ +
          ∫ t in u₁..u₂, ‖deriv (besselShiftAmp c) t‖) / Real.sqrt (τ / 4) := h
      _ ≤ 32 * 2 / Real.sqrt (τ / 4) := by gcongr
      _ = 128 / Real.sqrt τ := by
          rw [hsqrt]; field_simp; ring
  -- piece three: `[u₂, b]`, frequency at least `τ`
  have hp3 : ‖∫ u in u₂..b, besselShiftAmp c u *
      Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ))‖ ≤ 8 / τ := by
    have hnn : ∀ t ∈ Icc u₂ b, 0 ≤ deriv (deriv (besselShiftPsi τ X)) t := by
      intro t ht
      rw [deriv_deriv_besselShiftPsi]
      exact mul_nonneg hX.le (Real.sinh_nonneg_iff.mpr (le_trans hu₂0 ht.1))
    have hbd : ∀ t ∈ Icc u₂ b, τ ≤ |deriv (besselShiftPsi τ X) t| := by
      intro t ht
      rw [deriv_besselShiftPsi]
      have ht0 : 0 ≤ t := le_trans hu₂0 ht.1
      have hct : Real.cosh u₂ ≤ Real.cosh t := by
        rw [Real.cosh_le_cosh, abs_of_nonneg ht0, abs_of_nonneg hu₂0]; exact ht.1
      have hXc : 2 * τ ≤ X * Real.cosh t := by
        calc 2 * τ = X * Real.cosh u₂ := by rw [hcosh₂]; field_simp
          _ ≤ X * Real.cosh t := mul_le_mul_of_nonneg_left hct hX.le
      rw [abs_of_nonneg (by linarith)]
      linarith
    have h := _root_.RHTower.firstDerivTest hb hτ0 hψ hnn hbd hA
    have hbudget := besselShiftAmp_budget_le hc hu₂0 hb
    calc _ ≤ 4 * (‖besselShiftAmp c b‖ + ‖besselShiftAmp c u₂‖ +
          ∫ t in u₂..b, ‖deriv (besselShiftAmp c) t‖) / τ := h
      _ ≤ 4 * 2 / τ := by gcongr
      _ = 8 / τ := by ring
  -- assemble
  have hsplit : ∫ u in (0 : ℝ)..b, besselShiftAmp c u *
      Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ)) =
      (∫ u in (0 : ℝ)..u₁, besselShiftAmp c u * Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ))) +
      (∫ u in u₁..u₂, besselShiftAmp c u * Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ))) +
      ∫ u in u₂..b, besselShiftAmp c u * Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ)) := by
    rw [integral_add_adjacent_intervals (hcontI.intervalIntegrable _ _) (hcontI.intervalIntegrable _ _),
      integral_add_adjacent_intervals (hcontI.intervalIntegrable _ _) (hcontI.intervalIntegrable _ _)]
  rw [hsplit]
  have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ0
  have hsτ1 : 1 ≤ Real.sqrt τ := by
    rw [Real.one_le_sqrt]; exact hτ
  have hτsqrt : 1 / τ ≤ 1 / Real.sqrt τ := by
    rw [div_le_div_iff₀ hτ0 hsτ]
    nlinarith [Real.sq_sqrt hτ0.le]
  calc ‖_ + _ + _‖ ≤ ‖_‖ + ‖_‖ + ‖_‖ := norm_add₃_le
    _ ≤ 16 / τ + 128 / Real.sqrt τ + 8 / τ := by gcongr
    _ = 24 * (1 / τ) + 128 / Real.sqrt τ := by ring
    _ ≤ 24 * (1 / Real.sqrt τ) + 128 / Real.sqrt τ := by gcongr
    _ = 152 / Real.sqrt τ := by ring

/-! ## The transition regime: a second derivative vanishing only at the origin -/

/-- The oscillatory integral against the reversed phase on `[0, b]`, `b ≥ X^{-1/3}`, for any
`X > 0`. -/
theorem norm_intervalIntegral_psi_le_transition {c τ X : ℝ} (hc : 0 ≤ c) (hX : 0 < X)
    {b : ℝ} (hb : X ^ (-(1 / 3 : ℝ)) ≤ b) :
    ‖∫ u in (0 : ℝ)..b, besselShiftAmp c u *
        Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ))‖ ≤ 65 * X ^ (-(1 / 3 : ℝ)) := by
  set δ : ℝ := X ^ (-(1 / 3 : ℝ)) with hδ
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hX _
  have hψ := contDiff_besselShiftPsi τ X
  have hA := contDiff_besselShiftAmp c
  have hcontI : Continuous fun u => besselShiftAmp c u *
      Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ)) := by
    have := hA.continuous
    have := hψ.continuous
    fun_prop
  -- piece one: `[0, δ]`, trivial bound
  have hp1 : ‖∫ u in (0 : ℝ)..δ, besselShiftAmp c u *
      Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ))‖ ≤ δ := by
    have h := _root_.RHTower.norm_integral_le_const_mul_length (φ := besselShiftPsi τ X)
      (A := besselShiftAmp c) (a := 0) (b := δ) (C := 1) hδ0.le
      (fun t _ => norm_besselShiftAmp_le hc t)
    simpa using h
  -- piece two: `[δ, b]`, second derivative at least `X δ = X^{2/3}`
  have hp2 : ‖∫ u in δ..b, besselShiftAmp c u *
      Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ))‖ ≤ 64 * X ^ (-(1 / 3 : ℝ)) := by
    have hbd : ∀ t ∈ Icc δ b, X * δ ≤ deriv (deriv (besselShiftPsi τ X)) t := by
      intro t ht
      rw [deriv_deriv_besselShiftPsi]
      have ht0 : 0 ≤ t := le_trans hδ0.le ht.1
      have hs : t ≤ Real.sinh t := Real.self_le_sinh_iff.mpr ht0
      have : δ ≤ Real.sinh t := le_trans ht.1 hs
      exact mul_le_mul_of_nonneg_left this hX.le
    have h := _root_.RHTower.secondDerivTest hb (mul_pos hX hδ0) hψ hbd hA
    have hbudget := besselShiftAmp_budget_le hc hδ0.le hb
    have hsqrt : Real.sqrt (X * δ) = X ^ (1 / 3 : ℝ) := by
      have hXδ : X * δ = X ^ (2 / 3 : ℝ) := by
        rw [hδ]
        calc X * X ^ (-(1 / 3 : ℝ)) = X ^ (1 : ℝ) * X ^ (-(1 / 3 : ℝ)) := by rw [Real.rpow_one]
          _ = X ^ ((1 : ℝ) + -(1 / 3 : ℝ)) := (Real.rpow_add hX _ _).symm
          _ = X ^ (2 / 3 : ℝ) := by norm_num
      rw [hXδ, Real.sqrt_eq_rpow, ← Real.rpow_mul hX.le]; norm_num
    have hpos : 0 < X ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hX _
    calc _ ≤ 32 * (‖besselShiftAmp c b‖ + ‖besselShiftAmp c δ‖ +
          ∫ t in δ..b, ‖deriv (besselShiftAmp c) t‖) / Real.sqrt (X * δ) := h
      _ ≤ 32 * 2 / Real.sqrt (X * δ) := by gcongr
      _ = 64 * X ^ (-(1 / 3 : ℝ)) := by
          rw [hsqrt, Real.rpow_neg hX.le]; ring
  have hsplit : ∫ u in (0 : ℝ)..b, besselShiftAmp c u *
      Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ)) =
      (∫ u in (0 : ℝ)..δ, besselShiftAmp c u * Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ))) +
      ∫ u in δ..b, besselShiftAmp c u * Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ)) := by
    rw [integral_add_adjacent_intervals (hcontI.intervalIntegrable _ _) (hcontI.intervalIntegrable _ _)]
  rw [hsplit]
  calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
    _ ≤ δ + 64 * X ^ (-(1 / 3 : ℝ)) := by gcongr
    _ = 65 * X ^ (-(1 / 3 : ℝ)) := by rw [hδ]; ring

/-! ## Passage to the half line -/

theorem integrableOn_besselShift_halfLine {x : ℝ} (hx : 0 < x) (τ : ℝ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ < Real.pi / 2) :
    IntegrableOn (fun u : ℝ => ((besselShiftWeight (x * Real.cos θ) u : ℝ) : ℂ) *
      Complex.exp (I * ((besselShiftPhase τ (x * Real.sin θ) u : ℝ) : ℂ))) (Ioi 0) := by
  have hf := integrable_shifted_besselOrderEntireKernel hx ((τ : ℂ) * I) hθ0 hθ
  have heq : (fun u : ℝ => ((besselShiftWeight (x * Real.cos θ) u : ℝ) : ℂ) *
      Complex.exp (I * ((besselShiftPhase τ (x * Real.sin θ) u : ℝ) : ℂ))) =
      fun u : ℝ => ((Real.exp (τ * θ) : ℝ) : ℂ) *
        besselOrderEntireKernel x ((τ : ℂ) * I) ((u : ℂ) + (θ : ℂ) * I) := by
    funext u
    rw [besselOrderEntireKernel_shift_eq, ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add]
    have : τ * θ + -τ * θ = 0 := by ring
    rw [this, Real.exp_zero, Complex.ofReal_one, one_mul]
  exact (hf.const_mul _).integrableOn.congr_fun (fun u _ => (congrFun heq u).symm)
    measurableSet_Ioi

/-- A uniform bound on `[0, b]` for all large `b` bounds the half-line integral. -/
theorem norm_besselShiftHalfLine_le_of_forall {c τ X B b₀ : ℝ}
    (hint : IntegrableOn (fun u : ℝ => ((besselShiftWeight c u : ℝ) : ℂ) *
      Complex.exp (I * ((besselShiftPhase τ X u : ℝ) : ℂ))) (Ioi 0))
    (hB : ∀ b, b₀ ≤ b → ‖∫ u in (0 : ℝ)..b, ((besselShiftWeight c u : ℝ) : ℂ) *
      Complex.exp (I * ((besselShiftPhase τ X u : ℝ) : ℂ))‖ ≤ B) :
    ‖besselShiftHalfLine c τ X‖ ≤ B := by
  have ht := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hint tendsto_id
  exact le_of_tendsto ht.norm (Filter.eventually_atTop.mpr ⟨b₀, hB⟩)

/-- The interval integrals against the phase and against the reversed phase have equal norms. -/
theorem norm_intervalIntegral_weight_phase_eq (c τ X a b : ℝ) :
    ‖∫ u in a..b, ((besselShiftWeight c u : ℝ) : ℂ) *
        Complex.exp (I * ((besselShiftPhase τ X u : ℝ) : ℂ))‖ =
      ‖∫ u in a..b, besselShiftAmp c u * Complex.exp (I * ((besselShiftPsi τ X u : ℝ) : ℂ))‖ := by
  rw [intervalIntegral_weight_phase_eq_conj, Complex.norm_conj]

theorem norm_besselShiftHalfLine_le_bulk {x τ : ℝ} (hx : 0 < x) (hτ : 1 ≤ τ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi / 2) (hsin : 0 < Real.sin θ) (hxτ : x * Real.sin θ ≤ τ / 4) :
    ‖besselShiftHalfLine (x * Real.cos θ) τ (x * Real.sin θ)‖ ≤ 152 / Real.sqrt τ := by
  have hc : 0 ≤ x * Real.cos θ :=
    mul_nonneg hx.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ.le⟩)
  refine norm_besselShiftHalfLine_le_of_forall (b₀ := Real.arcosh (2 * τ / (x * Real.sin θ)))
    (integrableOn_besselShift_halfLine hx τ hθ0 hθ) fun b hb => ?_
  rw [norm_intervalIntegral_weight_phase_eq]
  exact norm_intervalIntegral_psi_le_bulk hc hτ (mul_pos hx hsin) hxτ hb

theorem norm_besselShiftHalfLine_le_transition {x : ℝ} (hx : 0 < x) (τ : ℝ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi / 2) (hsin : 0 < Real.sin θ) :
    ‖besselShiftHalfLine (x * Real.cos θ) τ (x * Real.sin θ)‖ ≤
      65 * (x * Real.sin θ) ^ (-(1 / 3 : ℝ)) := by
  have hc : 0 ≤ x * Real.cos θ :=
    mul_nonneg hx.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ.le⟩)
  refine norm_besselShiftHalfLine_le_of_forall (b₀ := (x * Real.sin θ) ^ (-(1 / 3 : ℝ)))
    (integrableOn_besselShift_halfLine hx τ hθ0 hθ) fun b hb => ?_
  rw [norm_intervalIntegral_weight_phase_eq]
  exact norm_intervalIntegral_psi_le_transition hc (mul_pos hx hsin) hb

/-! ## The bounds at `θ = π/2 - 1/τ` -/

theorem shiftAngle_bounds {τ : ℝ} (hτ : 2 ≤ τ) :
    0 ≤ Real.pi / 2 - 1 / τ ∧ Real.pi / 2 - 1 / τ < Real.pi / 2 ∧
      0 < Real.sin (Real.pi / 2 - 1 / τ) ∧ Real.sin (Real.pi / 2 - 1 / τ) ≤ 1 ∧
      1 / 2 ≤ Real.sin (Real.pi / 2 - 1 / τ) := by
  have hτ0 : 0 < τ := by linarith
  have h1τ : 0 < 1 / τ := by positivity
  have h1τ' : 1 / τ ≤ 1 / 2 := by rw [div_le_div_iff₀ hτ0 (by norm_num)]; linarith
  have hπ := Real.pi_gt_three
  refine ⟨by linarith, by linarith, ?_, Real.sin_le_one _, ?_⟩
  · rw [Real.sin_pi_div_two_sub]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  · rw [Real.sin_pi_div_two_sub]
    have := Real.one_sub_sq_div_two_le_cos (x := 1 / τ)
    nlinarith

theorem exp_shiftAngle {τ : ℝ} (hτ : 2 ≤ τ) :
    Real.exp (-τ * (Real.pi / 2 - 1 / τ)) = Real.exp 1 * Real.exp (-(Real.pi * τ) / 2) := by
  have hτ0 : τ ≠ 0 := by positivity
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **Bulk bound.**  For `τ ≥ 2` and `0 < x ≤ τ/4`,
`‖K_{iτ}(x)‖ ≤ 152 e · e^{-πτ/2} / √τ`. -/
theorem norm_modifiedBesselKOrder_I_mul_le_bulk {x τ : ℝ} (hτ : 2 ≤ τ) (hx0 : 0 < x)
    (hx : x ≤ τ / 4) :
    ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖ ≤
      152 * Real.exp 1 * Real.exp (-(Real.pi * τ) / 2) / Real.sqrt τ := by
  obtain ⟨hθ0, hθ, hsin, hsin1, -⟩ := shiftAngle_bounds hτ
  have hτ1 : 1 ≤ τ := by linarith
  have h := norm_modifiedBesselKOrder_I_mul_le_halfLine hx0 τ hθ0 hθ
  have hb := norm_besselShiftHalfLine_le_bulk hx0 hτ1 hθ0 hθ hsin
    (by nlinarith [mul_le_mul_of_nonneg_left hsin1 hx0.le])
  rw [exp_shiftAngle hτ] at h
  calc _ ≤ _ := h
    _ ≤ Real.exp 1 * Real.exp (-(Real.pi * τ) / 2) * (152 / Real.sqrt τ) := by gcongr
    _ = _ := by ring

/-- **Transition bound.**  For `τ ≥ 2` and `τ/4 < x ≤ 2τ`,
`‖K_{iτ}(x)‖ ≤ 130 e · e^{-πτ/2} τ^{-1/3}`. -/
theorem norm_modifiedBesselKOrder_I_mul_le_transition {x τ : ℝ} (hτ : 2 ≤ τ) (hx0 : τ / 4 < x) :
    ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖ ≤
      130 * Real.exp 1 * Real.exp (-(Real.pi * τ) / 2) * τ ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨hθ0, hθ, hsin, -, hsin2⟩ := shiftAngle_bounds hτ
  have hτ0 : 0 < τ := by linarith
  have hxpos : 0 < x := by linarith
  have h := norm_modifiedBesselKOrder_I_mul_le_halfLine hxpos τ hθ0 hθ
  have hb := norm_besselShiftHalfLine_le_transition hxpos τ hθ0 hθ hsin
  rw [exp_shiftAngle hτ] at h
  have hX : τ / 8 ≤ x * Real.sin (Real.pi / 2 - 1 / τ) := by
    nlinarith [mul_le_mul_of_nonneg_left hsin2 hxpos.le]
  have hX8 : (τ / 8) ^ (-(1 / 3 : ℝ)) = 2 * τ ^ (-(1 / 3 : ℝ)) := by
    rw [Real.div_rpow hτ0.le (by norm_num), show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
    ring
  have hmono : (x * Real.sin (Real.pi / 2 - 1 / τ)) ^ (-(1 / 3 : ℝ)) ≤
      (τ / 8) ^ (-(1 / 3 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_le_rpow (by positivity) hX (by norm_num))
  calc _ ≤ _ := h
    _ ≤ Real.exp 1 * Real.exp (-(Real.pi * τ) / 2) *
        (65 * (x * Real.sin (Real.pi / 2 - 1 / τ)) ^ (-(1 / 3 : ℝ))) := by gcongr
    _ ≤ Real.exp 1 * Real.exp (-(Real.pi * τ) / 2) * (65 * (τ / 8) ^ (-(1 / 3 : ℝ))) := by gcongr
    _ = _ := by rw [hX8]; ring

/-- **Uniform power saving.**  For `τ ≥ 2` and `0 < x ≤ 2τ`,
`‖K_{iτ}(x)‖ ≤ 420 e^{-πτ/2} τ^{-1/3}`. -/
theorem norm_modifiedBesselKOrder_I_mul_le_powerSaving {x τ : ℝ} (hτ : 2 ≤ τ) (hx0 : 0 < x) :
    ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖ ≤
      420 * Real.exp (-(Real.pi * τ) / 2) * τ ^ (-(1 / 3 : ℝ)) := by
  have hτ0 : 0 < τ := by linarith
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hE : 0 < Real.exp (-(Real.pi * τ) / 2) := Real.exp_pos _
  have hτ3 : 0 < τ ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hτ0 _
  rcases le_or_gt x (τ / 4) with hx | hx
  · have h := norm_modifiedBesselKOrder_I_mul_le_bulk hτ hx0 hx
    have hsqrt : 1 / Real.sqrt τ ≤ τ ^ (-(1 / 3 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hτ0.le]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    calc _ ≤ _ := h
      _ = 152 * Real.exp 1 * Real.exp (-(Real.pi * τ) / 2) * (1 / Real.sqrt τ) := by ring
      _ ≤ 152 * Real.exp 1 * Real.exp (-(Real.pi * τ) / 2) * τ ^ (-(1 / 3 : ℝ)) := by gcongr
      _ ≤ 420 * Real.exp (-(Real.pi * τ) / 2) * τ ^ (-(1 / 3 : ℝ)) := by
          have : 152 * Real.exp 1 ≤ 420 := by nlinarith
          nlinarith [mul_pos hE hτ3]
  · have h := norm_modifiedBesselKOrder_I_mul_le_transition hτ hx
    calc _ ≤ _ := h
      _ ≤ 420 * Real.exp (-(Real.pi * τ) / 2) * τ ^ (-(1 / 3 : ℝ)) := by
          have : 130 * Real.exp 1 ≤ 420 := by nlinarith
          nlinarith [mul_pos hE hτ3]

end

end GaloisForLFunctions.RHTower
