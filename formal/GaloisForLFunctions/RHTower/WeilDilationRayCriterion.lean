import GaloisForLFunctions.RHTower.WeilCutFreeHolomorphicExtension

/-!
# The dilation-ray criterion for odd Weil-positive weights

Let `φ` be the reference bump (`1` on `[−1, 1]`, supported in `(−2, 2)`, even, `0 ≤ φ ≤ 1`) and
`φ_T(x) = φ(x/T)`.  For an odd Weil-positive weight `lam` with odd Nevanlinna data `(ν, c)`, the
spectral weights of the dilates are, with `D = ∫φ`,
`Θ = [(1+γ²)T²|φ̂(T√γ)|² − T²D²]/γ` on the critical ordinates and
`Θ = T²[D² − (1+γ²)E(Tr)²]/r²` on the cut, `E(Tr) = ∫φ(u)e^{−Tru}du ≥ 2 + T²r²/6`.
So `Θ ≤ T²C₁` on the critical ordinates, `Θ ≤ T²γD² − T⁴D/6` near the centre, and
`Θ ≤ −4T²(T⁴r₀⁴/36 − 12)` on the cut at distance `≥ r₀`.

**Theorem** (`eq_vonMangoldt_and_riemannHypothesis_of_dilationRay_nonneg`).  If `lam` is odd
Weil-positive and `Re W_lam(φ_T ⋆ φ̃_T) ≥ 0` for every `T ≥ 1`, then `lam = Λ` and RH hold.
Positivity on the ray removes the cut (quartic beats quadratic growth), excludes a central atom
(`Θ(−1) ≤ −T⁴D/6`), and forces `∫_{γ ≥ δ} dν/γ ≤ δ ν(S¹) − c` for every `δ`, so the cut-free
extension `Φ(s) = (∫(γz−1)/(z+γ) dν − c)/(s − ½)` is nonnegative on `(½, ∞)`; the square-root
Herglotz transfer concludes.  Conversely `Λ` satisfies the hypothesis under RH, so RH is equivalent
to the existence of an odd Weil-positive weight that is Weil-positive on the dilation ray of a
single bump (`riemannHypothesis_iff_exists_weilPositiveOdd_dilationRay`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real
open Zeta23 Zeta23.WeilEF GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.OddResolvent
open WeilHerglotz RHTower.AtomDomination RHTower.WeilLineIntegral RHTower.WeilAtomic RHTower.EvenSector

/-! ## The reference bump -/

/-- The reference bump: `1` on `[−1, 1]`, supported in `(−2, 2)`, even, `0 ≤ φ ≤ 1`. -/
def refBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The real profile of the reference bump. -/
def refProfile (x : ℝ) : ℝ := refBump x

theorem refProfile_nonneg (x : ℝ) : 0 ≤ refProfile x := refBump.nonneg' x

theorem refProfile_le_one (x : ℝ) : refProfile x ≤ 1 := refBump.le_one

theorem refProfile_neg (x : ℝ) : refProfile (-x) = refProfile x := refBump.neg x

theorem refProfile_eq_one {x : ℝ} (hx : |x| ≤ 1) : refProfile x = 1 :=
  refBump.one_of_mem_closedBall
    (by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact hx)

theorem refProfile_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : refProfile x = 0 :=
  refBump.zero_of_le_dist (by rw [dist_zero_right, Real.norm_eq_abs]; exact hx)

theorem contDiff_refProfile : ContDiff ℝ 2 refProfile := refBump.contDiff

theorem continuous_refProfile : Continuous refProfile := refBump.continuous

theorem hasCompactSupport_refProfile : HasCompactSupport refProfile := refBump.hasCompactSupport

theorem integrable_refProfile : Integrable refProfile :=
  continuous_refProfile.integrable_of_hasCompactSupport hasCompactSupport_refProfile

/-- The mass of the bump is at least `2`. -/
theorem two_le_integral_refProfile : 2 ≤ ∫ x, refProfile x := by
  have h1 : ∫ x in Icc (-1 : ℝ) 1, refProfile x = 2 := by
    rw [setIntegral_congr_fun measurableSet_Icc
      (fun x hx => refProfile_eq_one (abs_le.mpr hx) : EqOn refProfile (fun _ => (1 : ℝ)) _),
      setIntegral_const, Measure.real, Real.volume_Icc, smul_eq_mul, mul_one,
      ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  calc (2 : ℝ) = ∫ x in Icc (-1 : ℝ) 1, refProfile x := h1.symm
    _ ≤ ∫ x, refProfile x :=
        setIntegral_le_integral integrable_refProfile (Eventually.of_forall refProfile_nonneg)

/-- The mass of the bump is at most `4`. -/
theorem integral_refProfile_le_four : ∫ x, refProfile x ≤ 4 := by
  have h : ∀ x, refProfile x ≤ (Icc (-2 : ℝ) 2).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ Icc (-2 : ℝ) 2
    · rw [Set.indicator_of_mem hx]; exact refProfile_le_one x
    · rw [Set.indicator_of_notMem hx, refProfile_eq_zero]
      rw [Set.mem_Icc, not_and_or] at hx
      rcases hx with hx | hx
      · have := not_le.mp hx; rw [abs_of_neg (by linarith)]; linarith
      · have := not_le.mp hx; rw [abs_of_pos (by linarith)]; linarith
  have hind : Integrable ((Icc (-2 : ℝ) 2).indicator fun _ => (1 : ℝ)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (C := (1 : ℝ)) (by simp)
  calc ∫ x, refProfile x ≤ ∫ x, (Icc (-2 : ℝ) 2).indicator (fun _ => (1 : ℝ)) x :=
        integral_mono integrable_refProfile hind h
    _ = 4 := by
        rw [integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc, smul_eq_mul,
          mul_one, ENNReal.toReal_ofReal (by norm_num)]
        norm_num

/-- The second moment of the bump is at least `2/3`. -/
theorem two_thirds_le_integral_sq_mul_refProfile : 2 / 3 ≤ ∫ x, x ^ 2 * refProfile x := by
  have hi : Integrable fun x : ℝ => x ^ 2 * refProfile x :=
    ((continuous_id.pow 2).mul continuous_refProfile).integrable_of_hasCompactSupport
      hasCompactSupport_refProfile.mul_left
  have h1 : ∫ x in Icc (-1 : ℝ) 1, x ^ 2 * refProfile x = 2 / 3 := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun x hx => by
        simp only
        rw [refProfile_eq_one (abs_le.mpr hx), mul_one] :
        EqOn (fun x : ℝ => x ^ 2 * refProfile x) (fun x => x ^ 2) _),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      integral_pow]
    norm_num
  calc (2 / 3 : ℝ) = ∫ x in Icc (-1 : ℝ) 1, x ^ 2 * refProfile x := h1.symm
    _ ≤ ∫ x, x ^ 2 * refProfile x :=
        setIntegral_le_integral hi (Eventually.of_forall fun x => by
          have := refProfile_nonneg x; positivity)

/-! ## Transforms of the bump -/

/-- The complex profile. -/
def refProfileC (x : ℝ) : ℂ := (refProfile x : ℂ)

theorem integrable_refProfileC : Integrable refProfileC := integrable_refProfile.ofReal

theorem paperFT_refProfileC_zero : paperFT refProfileC 0 = ((∫ x, refProfile x : ℝ) : ℂ) := by
  unfold paperFT refProfileC
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  exact integral_complex_ofReal

/-- The transform on the real line is the real cosine transform (evenness kills the sine). -/
theorem paperFT_refProfileC_ofReal (v : ℝ) :
    paperFT refProfileC v = ((∫ x, refProfile x * Real.cos (v * x) : ℝ) : ℂ) := by
  unfold paperFT refProfileC
  have hi1 : Integrable fun x : ℝ => refProfile x * Real.cos (v * x) :=
    (continuous_refProfile.mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_refProfile.mul_right
  have hi2 : Integrable fun x : ℝ => refProfile x * Real.sin (v * x) :=
    (continuous_refProfile.mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_refProfile.mul_right
  have hodd : ∫ x, refProfile x * Real.sin (v * x) = 0 := by
    have h := integral_neg_eq_self (fun x => refProfile x * Real.sin (v * x)) volume
    simp only [refProfile_neg, mul_neg, Real.sin_neg, integral_neg] at h
    linarith
  have e : ∀ x : ℝ, (refProfile x : ℂ) * Complex.exp (I * v * x) =
      ((refProfile x * Real.cos (v * x) : ℝ) : ℂ) +
        I * ((refProfile x * Real.sin (v * x) : ℝ) : ℂ) := by
    intro x
    rw [show I * v * x = ((v * x : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  simp_rw [e]
  have hadd : (∫ a : ℝ, (((refProfile a * Real.cos (v * a) : ℝ) : ℂ) +
      I * ((refProfile a * Real.sin (v * a) : ℝ) : ℂ))) =
      (∫ a : ℝ, ((refProfile a * Real.cos (v * a) : ℝ) : ℂ)) +
        ∫ a : ℝ, I * ((refProfile a * Real.sin (v * a) : ℝ) : ℂ) :=
    integral_add hi1.ofReal (hi2.ofReal.const_mul I)
  rw [hadd, integral_complex_ofReal, integral_const_mul, integral_complex_ofReal, hodd]
  simp

theorem norm_paperFT_refProfileC_le (v : ℝ) : ‖paperFT refProfileC v‖ ≤ ∫ x, refProfile x := by
  have hsupp : ∀ u, refProfileC u ≠ 0 → |u| ≤ 2 := fun u hu => by
    by_contra h
    exact hu (by simp [refProfileC, refProfile_eq_zero (not_le.mp h).le])
  have := norm_paperFT_le integrable_refProfileC hsupp (v : ℂ)
  rw [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul] at this
  refine this.trans (le_of_eq ?_)
  congr 1
  funext u
  simp [refProfileC, Real.norm_eq_abs, abs_of_nonneg (refProfile_nonneg u)]

/-- For `|v| ≤ 1/2` the cosine transform is nonnegative. -/
theorem integral_refProfile_mul_cos_nonneg {v : ℝ} (hv : |v| ≤ 1 / 2) :
    0 ≤ ∫ x, refProfile x * Real.cos (v * x) := by
  refine integral_nonneg fun x => ?_
  by_cases hx : 2 ≤ |x|
  · simp [refProfile_eq_zero hx]
  · have hx' : |x| < 2 := not_le.mp hx
    have hvx : |v * x| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg v, abs_nonneg x]
    have hpi := Real.pi_gt_three
    refine mul_nonneg (refProfile_nonneg x)
      (Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_) <;> linarith [abs_le.mp hvx]

/-- `φ̂(0) − φ̂(v) ≥ v²/6` for `|v| ≤ 1/2`. -/
theorem sq_div_six_le_integral_refProfile_sub_cos {v : ℝ} (hv : |v| ≤ 1 / 2) :
    v ^ 2 / 6 ≤ (∫ x, refProfile x) - ∫ x, refProfile x * Real.cos (v * x) := by
  have hi1 := integrable_refProfile
  have hi2 : Integrable fun x : ℝ => refProfile x * Real.cos (v * x) :=
    (continuous_refProfile.mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_refProfile.mul_right
  rw [← integral_sub hi1 hi2]
  have hnn : ∀ x, 0 ≤ refProfile x - refProfile x * Real.cos (v * x) := fun x => by
    have := Real.cos_le_one (v * x)
    nlinarith [refProfile_nonneg x]
  calc v ^ 2 / 6 = ∫ x in Icc (-1 : ℝ) 1, (v ^ 2 / 4) * x ^ 2 := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
          intervalIntegral.integral_const_mul, integral_pow]
        norm_num
        ring
    _ ≤ ∫ x in Icc (-1 : ℝ) 1, (refProfile x - refProfile x * Real.cos (v * x)) := by
        refine setIntegral_mono_on ((continuous_const.mul (continuous_id.pow 2)).integrableOn_Icc)
          (hi1.sub hi2).integrableOn measurableSet_Icc fun x hx => ?_
        rw [refProfile_eq_one (abs_le.mpr hx), one_mul]
        have hvx : |v * x| ≤ 1 := by
          rw [abs_mul]
          nlinarith [abs_nonneg v, abs_nonneg x, abs_le.mpr hx]
        have hb := Real.cos_bound hvx
        rw [abs_le] at hb
        have h4 : |v * x| ^ 4 ≤ |v * x| ^ 2 := by
          have h0 := abs_nonneg (v * x)
          calc |v * x| ^ 4 = |v * x| ^ 2 * |v * x| ^ 2 := by ring
            _ ≤ 1 * |v * x| ^ 2 := by
                gcongr
                nlinarith
            _ = |v * x| ^ 2 := one_mul _
        rw [sq_abs] at h4
        nlinarith [sq_abs (v * x)]
    _ ≤ ∫ x, (refProfile x - refProfile x * Real.cos (v * x)) :=
        setIntegral_le_integral (hi1.sub hi2) (Eventually.of_forall hnn)

/-- The transform of the bump on the imaginary axis is its exponential moment. -/
theorem paperFT_refProfileC_I_mul (r : ℝ) :
    paperFT refProfileC (I * r) = ((expMoment refProfile r : ℝ) : ℂ) :=
  paperFT_ofReal_I_mul refProfile r

/-- `E(r) = ∫ φ(u) cosh(ru) du` for the even profile. -/
theorem expMoment_refProfile_eq (r : ℝ) :
    expMoment refProfile r = ∫ u, refProfile u * Real.cosh (r * u) := by
  have hi : ∀ s : ℝ, Integrable fun u : ℝ => refProfile u * Real.exp (-(s * u)) := fun s =>
    (continuous_refProfile.mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_refProfile.mul_right
  have hrefl : expMoment refProfile r = ∫ u, refProfile u * Real.exp (r * u) := by
    unfold expMoment
    rw [← integral_neg_eq_self]
    congr 1; funext u
    rw [refProfile_neg]; congr 2; ring
  have h2 : 2 * expMoment refProfile r =
      ∫ u, refProfile u * (Real.exp (-(r * u)) + Real.exp (r * u)) := by
    rw [two_mul]
    nth_rewrite 2 [hrefl]
    unfold expMoment
    rw [← integral_add (hi r) (by simpa using hi (-r))]
    congr 1; funext u; ring
  have h3 : ∫ u, refProfile u * (Real.exp (-(r * u)) + Real.exp (r * u)) =
      2 * ∫ u, refProfile u * Real.cosh (r * u) := by
    rw [← integral_const_mul]
    congr 1; funext u
    rw [Real.cosh_eq]
    ring
  linarith

/-- `E(r) ≥ 2 + r²/6`. -/
theorem expMoment_refProfile_ge (r : ℝ) : 2 + r ^ 2 / 6 ≤ expMoment refProfile r := by
  rw [expMoment_refProfile_eq]
  have hi1 := integrable_refProfile
  have hi2 : Integrable fun x : ℝ => x ^ 2 * refProfile x :=
    ((continuous_id.pow 2).mul continuous_refProfile).integrable_of_hasCompactSupport
      hasCompactSupport_refProfile.mul_left
  have hic : Integrable fun u : ℝ => refProfile u * Real.cosh (r * u) :=
    (continuous_refProfile.mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_refProfile.mul_right
  have hcosh : ∀ y : ℝ, 1 + y ^ 2 / 4 ≤ Real.cosh y := fun y => by
    have h := sq_div_two_le_two_cosh_sub_two (u := |y|) (abs_nonneg y)
    rw [Real.cosh_abs, sq_abs] at h
    linarith
  have hpt : ∀ u : ℝ, refProfile u + r ^ 2 / 4 * (u ^ 2 * refProfile u) ≤
      refProfile u * Real.cosh (r * u) := fun u => by
    have := hcosh (r * u)
    have h0 := refProfile_nonneg u
    nlinarith
  have hmono := integral_mono (hi1.add (hi2.const_mul (r ^ 2 / 4))) hic hpt
  simp only [Pi.add_apply] at hmono
  rw [integral_add hi1 (hi2.const_mul _), integral_const_mul] at hmono
  have hm := two_le_integral_refProfile
  have hs := two_thirds_le_integral_sq_mul_refProfile
  nlinarith [sq_nonneg r]

/-! ## The dilates -/

/-- The dilate `φ(x/T)` as a complex test. -/
def dilate (T x : ℝ) : ℂ := (refProfile (x / T) : ℂ)

theorem dilate_neg (T x : ℝ) : dilate T (-x) = dilate T x := by
  simp only [dilate, neg_div, refProfile_neg]

theorem contDiff_dilate (T : ℝ) : ContDiff ℝ 2 (dilate T) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_refProfile.comp (contDiff_id.div_const T))

theorem hasCompactSupport_dilate {T : ℝ} (hT : 0 < T) : HasCompactSupport (dilate T) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * T)) (b := 2 * T)) fun x hx => ?_
  simp only [dilate]
  rw [refProfile_eq_zero, Complex.ofReal_zero]
  rw [Set.mem_Icc, not_and_or] at hx
  rw [abs_div, abs_of_pos hT, le_div_iff₀ hT]
  rcases hx with hx | hx
  · have := not_le.mp hx
    rw [abs_of_neg (by linarith)]
    linarith
  · have := not_le.mp hx
    rw [abs_of_pos (by linarith)]
    linarith

/-- `paperFT (φ(·/T)) z = T · φ̂(Tz)`. -/
theorem paperFT_dilate {T : ℝ} (hT : 0 < T) (z : ℂ) :
    paperFT (dilate T) z = T * paperFT refProfileC (T * z) := by
  unfold paperFT dilate refProfileC
  have h := Measure.integral_comp_div
    (fun y : ℝ => (refProfile y : ℂ) * Complex.exp (I * (T * z) * y)) T
  rw [abs_of_pos hT, Complex.real_smul] at h
  rw [← h]
  congr 1
  funext x
  congr 2
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  push_cast
  field_simp

theorem paperFT_dilate_zero {T : ℝ} (hT : 0 < T) :
    paperFT (dilate T) 0 = ((T * ∫ x, refProfile x : ℝ) : ℂ) := by
  rw [paperFT_dilate hT, mul_zero, paperFT_refProfileC_zero]
  push_cast
  ring

theorem norm_paperFT_dilate_ofReal {T : ℝ} (hT : 0 < T) (v : ℝ) :
    ‖paperFT (dilate T) v‖ = T * ‖paperFT refProfileC ((T * v : ℝ) : ℂ)‖ := by
  rw [paperFT_dilate hT, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  push_cast
  rfl

theorem paperFT_dilate_I_mul {T : ℝ} (hT : 0 < T) (r : ℝ) :
    paperFT (dilate T) (I * r) = ((T * expMoment refProfile (T * r) : ℝ) : ℂ) := by
  rw [paperFT_dilate hT, show (T : ℂ) * (I * r) = I * ((T * r : ℝ) : ℂ) by push_cast; ring,
    paperFT_refProfileC_I_mul]
  push_cast
  ring

/-! ## Bounds on the spectral weights of the dilates -/

/-- The mass `D = ∫φ`. -/
def refMass : ℝ := ∫ x, refProfile x

theorem two_le_refMass : 2 ≤ refMass := two_le_integral_refProfile

theorem refMass_le_four : refMass ≤ 4 := integral_refProfile_le_four

theorem refMass_pos : 0 < refMass := by linarith [two_le_refMass]

/-- On the critical ordinates: `Θ ≤ T²γD² − T²(D² − |φ̂(T√γ)|²)/γ`. -/
theorem spectralWeight_dilate_le_of_pos {T : ℝ} (hT : 0 < T) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (h1 : ζ ≠ 1) (hγ : 0 < circleOrd ζ) :
    oddSpectralWeight (dilate T) ζ ≤
      T ^ 2 * circleOrd ζ * refMass ^ 2 -
        T ^ 2 * (refMass ^ 2 -
          ‖paperFT refProfileC ((T * Real.sqrt (circleOrd ζ) : ℝ) : ℂ)‖ ^ 2) / circleOrd ζ := by
  have hfd := contDiff_dilate T
  have hfc := hasCompactSupport_dilate hT
  have hfe := dilate_neg T
  rw [spectralWeight_eq_of_pos hfd hfc hζ h1 hγ, paperFT_dilate_zero hT, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  set v := Real.sqrt (circleOrd ζ) with hv
  have hv2 : v ^ 2 = circleOrd ζ := Real.sq_sqrt hγ.le
  have hneg : ‖paperFT (dilate T) (-(v : ℂ))‖ = ‖paperFT (dilate T) v‖ := by
    rw [paperFT_neg_of_even hfe]
  rw [hneg, norm_paperFT_dilate_ofReal hT]
  set B := ‖paperFT refProfileC ((T * v : ℝ) : ℂ)‖ with hB
  have hB0 : 0 ≤ B := norm_nonneg _
  have hBD : B ≤ refMass := norm_paperFT_refProfileC_le _
  have hDeq : ∫ x, refProfile x = refMass := rfl
  rw [hDeq, div_le_iff₀ hγ, sub_mul, div_mul_cancel₀ _ hγ.ne']
  have hBB : B ^ 2 ≤ refMass ^ 2 := pow_le_pow_left₀ hB0 hBD 2
  have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
  have hγ2 : 0 ≤ circleOrd ζ ^ 2 := sq_nonneg _
  have key : (1 + circleOrd ζ ^ 2) * (((T * B) ^ 2 + (T * B) ^ 2) / 2) - (T * refMass) ^ 2 =
      T ^ 2 * circleOrd ζ ^ 2 * B ^ 2 - T ^ 2 * (refMass ^ 2 - B ^ 2) := by ring
  rw [key]
  have : T ^ 2 * circleOrd ζ ^ 2 * B ^ 2 ≤ T ^ 2 * circleOrd ζ ^ 2 * refMass ^ 2 := by
    gcongr
  nlinarith

/-- On the critical ordinates: `Θ ≤ T²γD²`. -/
theorem spectralWeight_dilate_le_mul_of_pos {T : ℝ} (hT : 0 < T) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (h1 : ζ ≠ 1) (hγ : 0 < circleOrd ζ) :
    oddSpectralWeight (dilate T) ζ ≤ T ^ 2 * circleOrd ζ * refMass ^ 2 := by
  have h := spectralWeight_dilate_le_of_pos hT hζ h1 hγ
  have hBD : ‖paperFT refProfileC ((T * Real.sqrt (circleOrd ζ) : ℝ) : ℂ)‖ ≤ refMass :=
    norm_paperFT_refProfileC_le _
  have hq : 0 ≤ refMass ^ 2 - ‖paperFT refProfileC ((T * Real.sqrt (circleOrd ζ) : ℝ) : ℂ)‖ ^ 2 := by
    nlinarith [norm_nonneg (paperFT refProfileC ((T * Real.sqrt (circleOrd ζ) : ℝ) : ℂ))]
  have : 0 ≤ T ^ 2 * (refMass ^ 2 -
      ‖paperFT refProfileC ((T * Real.sqrt (circleOrd ζ) : ℝ) : ℂ)‖ ^ 2) / circleOrd ζ := by
    positivity
  linarith

/-- Near the centre (`T√γ ≤ 1/2`): `Θ ≤ T²γD² − T⁴D/6`. -/
theorem spectralWeight_dilate_le_near_centre {T : ℝ} (hT : 1 ≤ T) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (h1 : ζ ≠ 1) (hγ : 0 < circleOrd ζ) (hsmall : T * Real.sqrt (circleOrd ζ) ≤ 1 / 2) :
    oddSpectralWeight (dilate T) ζ ≤ T ^ 2 * circleOrd ζ * refMass ^ 2 - T ^ 4 * refMass / 6 := by
  have hT0 : 0 < T := by linarith
  have h := spectralWeight_dilate_le_of_pos hT0 hζ h1 hγ
  set v := T * Real.sqrt (circleOrd ζ) with hv
  have hv0 : 0 ≤ v := by positivity
  have hvabs : |v| ≤ 1 / 2 := by rw [abs_of_nonneg hv0]; exact hsmall
  have hv2 : v ^ 2 = T ^ 2 * circleOrd ζ := by
    rw [hv, mul_pow, Real.sq_sqrt hγ.le]
  -- `B = ∫φ cos(v x) ∈ [0, D − v²/6]`
  have hBeq : ‖paperFT refProfileC (v : ℂ)‖ = ∫ x, refProfile x * Real.cos (v * x) := by
    rw [paperFT_refProfileC_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_refProfile_mul_cos_nonneg hvabs)]
  have hBle := sq_div_six_le_integral_refProfile_sub_cos hvabs
  have hB0 := integral_refProfile_mul_cos_nonneg hvabs
  rw [hBeq] at h
  set B := ∫ x, refProfile x * Real.cos (v * x) with hB
  have hD := two_le_refMass
  have hq : refMass * v ^ 2 / 6 ≤ refMass ^ 2 - B ^ 2 := by
    have : refMass ^ 2 - B ^ 2 = (refMass - B) * (refMass + B) := by ring
    rw [this]
    have h1' : v ^ 2 / 6 ≤ refMass - B := by unfold refMass; linarith
    have h2' : refMass ≤ refMass + B := by linarith
    have hv2' := sq_nonneg v
    calc refMass * v ^ 2 / 6 = (v ^ 2 / 6) * refMass := by ring
      _ ≤ (refMass - B) * (refMass + B) :=
          mul_le_mul h1' h2' (by linarith) (by linarith)
  have hq' : T ^ 2 * (refMass * v ^ 2 / 6) / circleOrd ζ ≤
      T ^ 2 * (refMass ^ 2 - B ^ 2) / circleOrd ζ := by
    gcongr
  have hval : T ^ 2 * (refMass * v ^ 2 / 6) / circleOrd ζ = T ^ 4 * refMass / 6 := by
    rw [hv2]
    field_simp
  linarith

/-- On the critical ordinates: `Θ ≤ (1 + γ²)N₂²/(T²γ³) − T²D²/γ`. -/
theorem spectralWeight_dilate_le_of_pos_decay {T : ℝ} (hT : 0 < T) {N₂ : ℝ}
    (hN : ∀ v : ℝ, v ^ 2 * ‖paperFT refProfileC v‖ ≤ N₂) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (h1 : ζ ≠ 1) (hγ0 : 0 < circleOrd ζ) :
    oddSpectralWeight (dilate T) ζ ≤
      (1 + circleOrd ζ ^ 2) * N₂ ^ 2 / (T ^ 2 * circleOrd ζ ^ 3) - T ^ 2 * refMass ^ 2 / circleOrd ζ := by
  have hfd := contDiff_dilate T
  have hfc := hasCompactSupport_dilate hT
  have hfe := dilate_neg T
  rw [spectralWeight_eq_of_pos hfd hfc hζ h1 hγ0, paperFT_dilate_zero hT, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  have hDeq : ∫ x, refProfile x = refMass := rfl
  rw [hDeq]
  set v := Real.sqrt (circleOrd ζ) with hv
  have hv2 : v ^ 2 = circleOrd ζ := Real.sq_sqrt hγ0.le
  have hneg : ‖paperFT (dilate T) (-(v : ℂ))‖ = ‖paperFT (dilate T) v‖ := by
    rw [paperFT_neg_of_even hfe]
  rw [hneg, norm_paperFT_dilate_ofReal hT]
  set B := ‖paperFT refProfileC ((T * v : ℝ) : ℂ)‖ with hB
  have hB0 : 0 ≤ B := norm_nonneg _
  have hBN : T ^ 2 * circleOrd ζ * B ≤ N₂ := by
    have := hN (T * v)
    rw [mul_pow, hv2] at this
    exact this
  have hN0 : 0 ≤ N₂ := le_trans (by positivity) hBN
  have hpos : 0 < T ^ 2 * circleOrd ζ := by positivity
  -- `B ≤ N₂/(T²γ)`, hence `B² ≤ N₂²/(T⁴γ²)`
  have hB2 : (T ^ 2 * circleOrd ζ) ^ 2 * B ^ 2 ≤ N₂ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hBN 2
    calc (T ^ 2 * circleOrd ζ) ^ 2 * B ^ 2 = (T ^ 2 * circleOrd ζ * B) ^ 2 := by ring
      _ ≤ N₂ ^ 2 := this
  rw [div_le_iff₀ hγ0]
  have e : ((1 + circleOrd ζ ^ 2) * N₂ ^ 2 / (T ^ 2 * circleOrd ζ ^ 3) -
      T ^ 2 * refMass ^ 2 / circleOrd ζ) * circleOrd ζ =
      (1 + circleOrd ζ ^ 2) * N₂ ^ 2 / (T ^ 2 * circleOrd ζ ^ 2) - T ^ 2 * refMass ^ 2 := by
    field_simp
  rw [e]
  have hmain : (1 + circleOrd ζ ^ 2) * ((T * B) ^ 2 + (T * B) ^ 2) / 2 ≤
      (1 + circleOrd ζ ^ 2) * N₂ ^ 2 / (T ^ 2 * circleOrd ζ ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have : (T * B) ^ 2 * (T ^ 2 * circleOrd ζ ^ 2) ≤ N₂ ^ 2 := by nlinarith
    nlinarith [sq_nonneg (circleOrd ζ)]
  have hsq : (T * refMass) ^ 2 = T ^ 2 * refMass ^ 2 := by ring
  rw [hsq]
  linarith

/-- On the cut: `Θ ≤ 0`. -/
theorem spectralWeight_dilate_nonpos_of_cut {T : ℝ} (hT : 0 < T) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (h1 : ζ ≠ 1) (hγ : -(1 / 4) ≤ circleOrd ζ) (hγ' : circleOrd ζ < 0) :
    oddSpectralWeight (dilate T) ζ ≤ 0 := by
  have hfd := contDiff_dilate T
  have hfc := hasCompactSupport_dilate hT
  have hfe := dilate_neg T
  rw [spectralWeight_eq_of_neg_of_even hfd hfc hfe hζ h1 hγ hγ', paperFT_dilate_zero hT,
    paperFT_dilate_I_mul hT, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs]
  have hDeq : ∫ x, refProfile x = refMass := rfl
  rw [hDeq]
  have hE : refMass ≤ expMoment refProfile (T * Real.sqrt (-circleOrd ζ)) :=
    integral_le_expMoment continuous_refProfile hasCompactSupport_refProfile refProfile_nonneg
      refProfile_neg _
  have hD := refMass_pos
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by linarith)
  have hE2 : (T * refMass) ^ 2 ≤ (T * expMoment refProfile (T * Real.sqrt (-circleOrd ζ))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hE hT.le) 2
  nlinarith [sq_nonneg (circleOrd ζ), sq_nonneg (T * expMoment refProfile (T * Real.sqrt (-circleOrd ζ)))]

/-- On the cut at distance `≥ r₀`: `Θ ≤ 4T²(12 − T⁴r₀⁴/36)` once `T⁴r₀⁴ ≥ 432`. -/
theorem spectralWeight_dilate_le_of_cut {T r₀ : ℝ} (hT : 0 < T) (hr₀ : 0 ≤ r₀)
    (hbig : 12 ≤ T ^ 4 * r₀ ^ 4 / 36) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1)
    (hγ : -(1 / 4) ≤ circleOrd ζ) (hγ' : circleOrd ζ ≤ -(r₀ ^ 2)) (hγ'' : circleOrd ζ < 0) :
    oddSpectralWeight (dilate T) ζ ≤ 4 * T ^ 2 * (12 - T ^ 4 * r₀ ^ 4 / 36) := by
  have hfd := contDiff_dilate T
  have hfc := hasCompactSupport_dilate hT
  have hfe := dilate_neg T
  rw [spectralWeight_eq_of_neg_of_even hfd hfc hfe hζ h1 hγ hγ'', paperFT_dilate_zero hT,
    paperFT_dilate_I_mul hT, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs]
  have hDeq : ∫ x, refProfile x = refMass := rfl
  rw [hDeq]
  set r := Real.sqrt (-circleOrd ζ) with hr
  have hr0 : r₀ ≤ r := by
    rw [hr]
    exact (Real.le_sqrt hr₀ (by linarith)).mpr (by linarith)
  have hrpos : 0 < -circleOrd ζ := by linarith
  have hr2 : r ^ 2 = -circleOrd ζ := Real.sq_sqrt hrpos.le
  have hE : 2 + (T * r) ^ 2 / 6 ≤ expMoment refProfile (T * r) := expMoment_refProfile_ge _
  have hD4 := refMass_le_four
  have hD := refMass_pos
  -- `D² − (1+γ²)E² ≤ 16 − E² ≤ 12 − T⁴r⁴/36`
  have hE0 : 0 ≤ 2 + (T * r) ^ 2 / 6 := by positivity
  have hE2 : (2 + (T * r) ^ 2 / 6) ^ 2 ≤ expMoment refProfile (T * r) ^ 2 :=
    pow_le_pow_left₀ hE0 hE 2
  have hr4 : T ^ 4 * r₀ ^ 4 ≤ T ^ 4 * r ^ 4 := by
    have := pow_le_pow_left₀ hr₀ hr0 4
    nlinarith [pow_nonneg hT.le 4]
  have hbr : (T * refMass) ^ 2 - (1 + circleOrd ζ ^ 2) * (T * expMoment refProfile (T * r)) ^ 2 ≤
      T ^ 2 * (12 - T ^ 4 * r₀ ^ 4 / 36) := by
    have h16 : refMass ^ 2 ≤ 16 := by nlinarith
    have hEE : expMoment refProfile (T * r) ^ 2 ≥ 4 + T ^ 4 * r ^ 4 / 36 := by nlinarith
    have hγ2 : 1 ≤ 1 + circleOrd ζ ^ 2 := by nlinarith [sq_nonneg (circleOrd ζ)]
    have hEnn : 0 ≤ (T * expMoment refProfile (T * r)) ^ 2 := sq_nonneg _
    have : (T * expMoment refProfile (T * r)) ^ 2 ≤ (1 + circleOrd ζ ^ 2) *
        (T * expMoment refProfile (T * r)) ^ 2 := by nlinarith
    nlinarith [sq_nonneg T]
  have hneg : T ^ 2 * (12 - T ^ 4 * r₀ ^ 4 / 36) ≤ 0 := by nlinarith [sq_nonneg T]
  have h4 : 1 / 4 ≥ -circleOrd ζ := by linarith
  rw [div_le_iff₀ hrpos]
  nlinarith

/-- The uniform constant `C₁ = D² + 2N₂²`. -/
def dilateConst (N₂ : ℝ) : ℝ := refMass ^ 2 + 2 * N₂ ^ 2

/-- Uniformly on the support: `Θ ≤ T²C₁` for `T ≥ 1`. -/
theorem spectralWeight_dilate_le_uniform {T : ℝ} (hT : 1 ≤ T) {N₂ : ℝ}
    (hN : ∀ v : ℝ, v ^ 2 * ‖paperFT refProfileC v‖ ≤ N₂) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hs : ζ = 1 ∨ -(1 / 4) ≤ circleOrd ζ) :
    oddSpectralWeight (dilate T) ζ ≤ T ^ 2 * dilateConst N₂ := by
  have hT0 : 0 < T := by linarith
  have hfd := contDiff_dilate T
  have hfc := hasCompactSupport_dilate hT0
  have hN0 : 0 ≤ N₂ := le_trans (by positivity) (hN 0)
  have hD := refMass_pos
  have hC : 0 ≤ T ^ 2 * dilateConst N₂ := by unfold dilateConst; positivity
  have hcrit : ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ≠ 1 → 0 < circleOrd ζ →
      oddSpectralWeight (dilate T) ζ ≤ T ^ 2 * dilateConst N₂ := by
    intro ζ hζ h1 hγ
    unfold dilateConst
    by_cases hγ1 : circleOrd ζ ≤ 1
    · have := spectralWeight_dilate_le_mul_of_pos hT0 hζ h1 hγ
      have h2 : T ^ 2 * circleOrd ζ * refMass ^ 2 ≤ T ^ 2 * refMass ^ 2 := by
        have : 0 ≤ T ^ 2 * refMass ^ 2 := by positivity
        nlinarith
      nlinarith [sq_nonneg N₂, sq_nonneg T]
    · have hγ1' : 1 ≤ circleOrd ζ := (not_le.mp hγ1).le
      have hγ0 : 0 < circleOrd ζ := by linarith
      have := spectralWeight_dilate_le_of_pos_decay hT0 hN hζ h1 hγ0
      have hA : (1 + circleOrd ζ ^ 2) * N₂ ^ 2 / (T ^ 2 * circleOrd ζ ^ 3) ≤ 2 * N₂ ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have hT2 : 1 ≤ T ^ 2 := by nlinarith
        have hγ3 : 1 + circleOrd ζ ^ 2 ≤ 2 * circleOrd ζ ^ 3 := by nlinarith
        have e1 : (1 + circleOrd ζ ^ 2) * N₂ ^ 2 ≤ 2 * circleOrd ζ ^ 3 * N₂ ^ 2 :=
          mul_le_mul_of_nonneg_right hγ3 (sq_nonneg N₂)
        have e2 : 2 * circleOrd ζ ^ 3 * N₂ ^ 2 ≤ 2 * circleOrd ζ ^ 3 * N₂ ^ 2 * T ^ 2 := by
          have : 0 ≤ 2 * circleOrd ζ ^ 3 * N₂ ^ 2 := by positivity
          nlinarith
        nlinarith
      have hB : 0 ≤ T ^ 2 * refMass ^ 2 / circleOrd ζ := by positivity
      have hT2 : 1 ≤ T ^ 2 := by nlinarith
      nlinarith [sq_nonneg N₂]
  by_cases h1 : ζ = 1
  · rw [h1, oddSpectralWeight_one hfd hfc]; exact hC
  · have hγ : -(1 / 4) ≤ circleOrd ζ := hs.resolve_left h1
    rcases lt_trichotomy (circleOrd ζ) 0 with hneg | hzero | hpos
    · exact (spectralWeight_dilate_nonpos_of_cut hT0 hζ h1 hγ hneg).trans hC
    · have : ζ = -1 := by rw [eq_bdryPt_circleOrd hζ h1, hzero, bdryPt_zero]
      rw [this]
      exact spectralWeight_neg_one_le_of_forall_pos hfd hfc hcrit
    · exact hcrit ζ hζ h1 hpos

/-- At the centre: `Θ(−1) ≤ −T⁴D/6` for `T ≥ 1`. -/
theorem spectralWeight_dilate_neg_one_le {T : ℝ} (hT : 1 ≤ T) :
    oddSpectralWeight (dilate T) (-1) ≤ -(T ^ 4 * refMass / 6) := by
  have hT0 : 0 < T := by linarith
  have hfd := contDiff_dilate T
  have hfc := hasCompactSupport_dilate hT0
  have hlim := tendsto_spectralWeight_bdryPt hfd hfc
  set γn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hγn
  have hγpos : ∀ n, 0 < γn n := fun n => by positivity
  have hγ0 : Tendsto γn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- the bound `Θ(bdryPt γ) ≤ T²γD² − T⁴D/6` holds eventually
  have hev : ∀ᶠ n in atTop, oddSpectralWeight (dilate T) (bdryPt (γn n)) ≤
      T ^ 2 * γn n * refMass ^ 2 - T ^ 4 * refMass / 6 := by
    have hsmall : ∀ᶠ n in atTop, γn n ≤ 1 / (4 * T ^ 2) := by
      have : (0 : ℝ) < 1 / (4 * T ^ 2) := by positivity
      exact (hγ0.eventually (gt_mem_nhds this)).mono fun n hn => hn.le
    filter_upwards [hsmall] with n hn
    have hb := spectralWeight_dilate_le_near_centre hT (norm_bdryPt _) (bdryPt_ne_one _)
      (by rw [circleOrd_bdryPt]; exact hγpos n) (by
        rw [circleOrd_bdryPt]
        have h1 : Real.sqrt (γn n) ≤ Real.sqrt (1 / (4 * T ^ 2)) := Real.sqrt_le_sqrt hn
        have h2 : Real.sqrt (1 / (4 * T ^ 2)) = 1 / (2 * T) := by
          rw [show (1 / (4 * T ^ 2) : ℝ) = (1 / (2 * T)) ^ 2 by field_simp; ring,
            Real.sqrt_sq (by positivity)]
        rw [h2] at h1
        calc T * Real.sqrt (γn n) ≤ T * (1 / (2 * T)) :=
              mul_le_mul_of_nonneg_left h1 hT0.le
          _ = 1 / 2 := by field_simp)
    rw [circleOrd_bdryPt] at hb
    exact hb
  have hbound : Tendsto (fun n => T ^ 2 * γn n * refMass ^ 2 - T ^ 4 * refMass / 6) atTop
      (𝓝 (T ^ 2 * 0 * refMass ^ 2 - T ^ 4 * refMass / 6)) :=
    ((hγ0.const_mul _).mul_const _).sub_const _
  have := le_of_tendsto_of_tendsto hlim hbound hev
  simpa using this

/-! ## The measure inequality from positivity on one test -/

/-- Positivity on one test whose weight is `≤ M₀` off a measurable set `A` and `≤ −K` on `A`
gives `K ν(A) ≤ M₀ ν(S¹) − c|f̂(0)|²`. -/
theorem mul_measureReal_le_of_weight_bounds {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hsupp : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} = 0)
    (hrep : ∀ a : ℂ, 0 < a.re → 0 < a.im →
      a * Ψ (1 / 2 + a) =
        (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hW : 0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re)
    {A : Set ℝ} (hA : MeasurableSet A) {M₀ K : ℝ} (hM₀ : 0 ≤ M₀)
    (hbound : ∀ᵐ θ ∂ν,
      (θ ∈ A → oddSpectralWeight f (circleMap 0 1 θ) ≤ -K) ∧
        (θ ∉ A → oddSpectralWeight f (circleMap 0 1 θ) ≤ M₀)) :
    K * ν.real A ≤ M₀ * ν.real univ - c * ‖paperFT f 0‖ ^ 2 := by
  rw [re_weilFullFunctional_eq_integral_spectralWeight_sub hsl hΨd hΨe hsupp hrep hf hfc] at hW
  set φ : ℝ → ℝ := fun θ => M₀ - (M₀ + K) * A.indicator (fun _ => (1 : ℝ)) θ with hφ
  have hae : ∀ᵐ θ ∂ν, oddSpectralWeight f (circleMap 0 1 θ) ≤ φ θ := by
    filter_upwards [hbound] with θ hθ
    simp only [hφ]
    by_cases hc : θ ∈ A
    · rw [Set.indicator_of_mem hc, mul_one]; linarith [hθ.1 hc]
    · rw [Set.indicator_of_notMem hc, mul_zero, sub_zero]; exact hθ.2 hc
  have hind : Integrable (A.indicator fun _ => (1 : ℝ)) ν := (integrable_const (1 : ℝ)).indicator hA
  have hφi : Integrable φ ν := (integrable_const _).sub (hind.const_mul _)
  have hle := integral_mono_ae (integrable_spectralWeight_circleMap hsupp hf hfc) hφi hae
  have hφint : ∫ θ, φ θ ∂ν = M₀ * ν.real univ - (M₀ + K) * ν.real A := by
    simp only [hφ]
    rw [integral_sub (integrable_const _) (hind.const_mul _), integral_const, integral_const_mul,
      integral_indicator_const _ hA]
    simp only [smul_eq_mul, mul_one]
    ring
  rw [hφint] at hle
  have hm := measureReal_nonneg (μ := ν) (s := A)
  nlinarith [mul_nonneg hM₀ hm]

/-! ## Cut removal on the dilation ray -/

/-- The union of the pieces `cutSet (1/(k+1))` with the far cut covers the whole cut. -/
theorem cut_measure_eq_zero_of_forall_cutSet {ν : Measure ℝ}
    (hsupp : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} = 0)
    (h : ∀ r₀ : ℝ, 0 < r₀ → ν (cutSet r₀) = 0) :
    ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < 0} = 0 := by
  have hsub : {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < 0} ⊆
      {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} ∪
        ⋃ k : ℕ, cutSet (1 / ((k : ℝ) + 1)) := by
    rintro θ ⟨h1, hγ⟩
    by_cases hq : angleOrd θ < -(1 / 4)
    · exact Or.inl ⟨h1, hq⟩
    · have hq' : -(1 / 4) ≤ angleOrd θ := not_lt.mp hq
      refine Or.inr (Set.mem_iUnion.mpr ?_)
      have hpos' : 0 < -angleOrd θ := by linarith
      obtain ⟨k, hk⟩ := exists_nat_gt (1 / (-angleOrd θ))
      refine ⟨k, h1, hq', ?_⟩
      have hk0 : (0 : ℝ) < k := lt_trans (by positivity) hk
      have hk1 : 1 / (k : ℝ) < -angleOrd θ := by
        rw [div_lt_iff₀ hk0]
        rw [div_lt_iff₀ hpos'] at hk
        linarith
      have hk2 : (1 / ((k : ℝ) + 1)) ^ 2 ≤ 1 / (k : ℝ) := by
        rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) hk0]
        nlinarith
      linarith
  exact measure_mono_null hsub (measure_union_null hsupp (measure_iUnion_null fun k =>
    h _ (by positivity)))

/-- Positivity on the dilation ray kills the cut at distance `≥ r₀`. -/
theorem measure_cutSet_eq_zero_of_dilationRay {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hsupp : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} = 0)
    (hrep : ∀ a : ℂ, 0 < a.re → 0 < a.im →
      a * Ψ (1 / 2 + a) =
        (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c)
    (hpos : ∀ T : ℝ, 1 ≤ T →
      0 ≤ (weilFullFunctional lam (EF.weilTest (dilate T) (dilate T))).re)
    {r₀ : ℝ} (hr₀ : 0 < r₀) : ν (cutSet r₀) = 0 := by
  obtain ⟨N₀, N₂, -, -, hN⟩ := exists_profile_bounds contDiff_refProfile hasCompactSupport_refProfile
  have hN' : ∀ v : ℝ, v ^ 2 * ‖paperFT refProfileC v‖ ≤ N₂ := fun v => (hN v).2
  set M : ℝ := ν.real univ with hM
  set C₁ : ℝ := dilateConst N₂ with hC₁
  have hC₁0 : 0 ≤ C₁ := by unfold dilateConst at hC₁; rw [hC₁]; positivity
  set m : ℝ := ν.real (cutSet r₀) with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hD := refMass_pos
  have key : ∀ T : ℝ, 1 ≤ T → 12 ≤ T ^ 4 * r₀ ^ 4 / 36 →
      (4 * (T ^ 4 * r₀ ^ 4 / 36 - 12)) * m ≤ C₁ * M - c * refMass ^ 2 := by
    intro T hT hbig
    have hT0 : 0 < T := by linarith
    have h := mul_measureReal_le_of_weight_bounds hsl hΨd hΨe hsupp hrep (contDiff_dilate T)
      (hasCompactSupport_dilate hT0) (hpos T hT) (measurableSet_cutSet r₀)
      (M₀ := T ^ 2 * C₁) (K := -(4 * T ^ 2 * (12 - T ^ 4 * r₀ ^ 4 / 36))) (by positivity) ?_
    · rw [paperFT_dilate_zero hT0, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
      have hDeq : ∫ x, refProfile x = refMass := rfl
      rw [hDeq, ← hM] at h
      have hT2 : 0 < T ^ 2 := by positivity
      have e1 : -(4 * T ^ 2 * (12 - T ^ 4 * r₀ ^ 4 / 36)) * m =
          T ^ 2 * ((4 * (T ^ 4 * r₀ ^ 4 / 36 - 12)) * m) := by ring
      have e2 : T ^ 2 * C₁ * M - c * (T * refMass) ^ 2 = T ^ 2 * (C₁ * M - c * refMass ^ 2) := by
        ring
      rw [e1, e2] at h
      exact le_of_mul_le_mul_left h hT2
    · filter_upwards [ae_support_of_measure_eq_zero hsupp] with θ hθ
      refine ⟨fun hc => ?_, fun _ => ?_⟩
      · obtain ⟨h1, hγ, hγ'⟩ := hc
        have hγ'' : circleOrd (circleMap 0 1 θ) < 0 := by
          change angleOrd θ < 0
          nlinarith
        have := spectralWeight_dilate_le_of_cut hT0 hr₀.le hbig (norm_circleMap_one θ) h1 hγ hγ' hγ''
        linarith
      · exact spectralWeight_dilate_le_uniform hT hN' (norm_circleMap_one θ) hθ
  have hm_eq : m = 0 := by
    by_contra hne
    have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hne)
    set R : ℝ := C₁ * M - c * refMass ^ 2 with hR
    have h4m : 0 < 4 * m := by linarith
    have hRm : 0 ≤ |R| / (4 * m) := div_nonneg (abs_nonneg R) h4m.le
    set Q : ℝ := (|R| / (4 * m) + 13) * 36 / r₀ ^ 4 + 1 with hQ
    have hQ1 : 1 ≤ Q := by
      have : 0 ≤ (|R| / (4 * m) + 13) * 36 / r₀ ^ 4 :=
        div_nonneg (mul_nonneg (by linarith) (by norm_num)) (by positivity)
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt Q
    have hT1 : (1 : ℝ) ≤ n := by linarith
    have hT4 : Q ≤ (n : ℝ) ^ 4 := by
      have h2 : (n : ℝ) ≤ (n : ℝ) ^ 4 := by
        have h3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hT1
        nlinarith
      linarith
    have hr4 : 0 < r₀ ^ 4 := by positivity
    have hbig' : |R| / (4 * m) + 13 ≤ (n : ℝ) ^ 4 * r₀ ^ 4 / 36 := by
      have : (|R| / (4 * m) + 13) * 36 / r₀ ^ 4 ≤ (n : ℝ) ^ 4 := by linarith
      rw [div_le_iff₀ hr4] at this
      linarith
    have hbig : 12 ≤ (n : ℝ) ^ 4 * r₀ ^ 4 / 36 := by
      linarith
    have hk := key n hT1 hbig
    have hcontra : |R| + 4 * m ≤ 4 * ((n : ℝ) ^ 4 * r₀ ^ 4 / 36 - 12) * m := by
      have : |R| / (4 * m) + 1 ≤ (n : ℝ) ^ 4 * r₀ ^ 4 / 36 - 12 := by linarith
      calc |R| + 4 * m = (|R| / (4 * m) + 1) * (4 * m) := by field_simp
        _ ≤ ((n : ℝ) ^ 4 * r₀ ^ 4 / 36 - 12) * (4 * m) :=
            mul_le_mul_of_nonneg_right this h4m.le
        _ = 4 * ((n : ℝ) ^ 4 * r₀ ^ 4 / 36 - 12) * m := by ring
    linarith [le_abs_self R]
  exact (measureReal_eq_zero_iff (measure_ne_top ν _)).mp hm_eq

/-- **Cut removal on the dilation ray.** -/
theorem cut_measure_eq_zero_of_dilationRay {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hsupp : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} = 0)
    (hrep : ∀ a : ℂ, 0 < a.re → 0 < a.im →
      a * Ψ (1 / 2 + a) =
        (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c)
    (hpos : ∀ T : ℝ, 1 ≤ T →
      0 ≤ (weilFullFunctional lam (EF.weilTest (dilate T) (dilate T))).re) :
    ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < 0} = 0 :=
  cut_measure_eq_zero_of_forall_cutSet hsupp fun _ hr₀ =>
    measure_cutSet_eq_zero_of_dilationRay hsl hΨd hΨe hsupp hrep hpos hr₀

/-! ## No central atom -/

theorem measurableSet_centreSet : MeasurableSet {θ : ℝ | circleMap 0 1 θ = -1} :=
  measurable_circleMap 0 1 (measurableSet_singleton (-1))

/-- **Positivity on the dilation ray excludes a central atom.** -/
theorem measure_centre_eq_zero_of_dilationRay {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hsupp : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} = 0)
    (hrep : ∀ a : ℂ, 0 < a.re → 0 < a.im →
      a * Ψ (1 / 2 + a) =
        (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c)
    (hpos : ∀ T : ℝ, 1 ≤ T →
      0 ≤ (weilFullFunctional lam (EF.weilTest (dilate T) (dilate T))).re) :
    ν {θ : ℝ | circleMap 0 1 θ = -1} = 0 := by
  obtain ⟨N₀, N₂, -, -, hN⟩ := exists_profile_bounds contDiff_refProfile hasCompactSupport_refProfile
  have hN' : ∀ v : ℝ, v ^ 2 * ‖paperFT refProfileC v‖ ≤ N₂ := fun v => (hN v).2
  set M : ℝ := ν.real univ with hM
  set C₁ : ℝ := dilateConst N₂ with hC₁
  have hC₁0 : 0 ≤ C₁ := by unfold dilateConst at hC₁; rw [hC₁]; positivity
  set m : ℝ := ν.real {θ : ℝ | circleMap 0 1 θ = -1} with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hD := refMass_pos
  have key : ∀ T : ℝ, 1 ≤ T → (T ^ 2 * refMass / 6) * m ≤ C₁ * M - c * refMass ^ 2 := by
    intro T hT
    have hT0 : 0 < T := by linarith
    have h := mul_measureReal_le_of_weight_bounds hsl hΨd hΨe hsupp hrep (contDiff_dilate T)
      (hasCompactSupport_dilate hT0) (hpos T hT) measurableSet_centreSet
      (M₀ := T ^ 2 * C₁) (K := T ^ 4 * refMass / 6) (by positivity) ?_
    · rw [paperFT_dilate_zero hT0, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
      have hDeq : ∫ x, refProfile x = refMass := rfl
      rw [hDeq, ← hM] at h
      have hT2 : 0 < T ^ 2 := by positivity
      have e1 : T ^ 4 * refMass / 6 * m = T ^ 2 * ((T ^ 2 * refMass / 6) * m) := by ring
      have e2 : T ^ 2 * C₁ * M - c * (T * refMass) ^ 2 = T ^ 2 * (C₁ * M - c * refMass ^ 2) := by
        ring
      rw [e1, e2] at h
      exact le_of_mul_le_mul_left h hT2
    · filter_upwards [ae_support_of_measure_eq_zero hsupp] with θ hθ
      refine ⟨fun hc => ?_, fun _ => ?_⟩
      · have hc' : circleMap 0 1 θ = -1 := hc
        rw [hc']
        exact spectralWeight_dilate_neg_one_le hT
      · exact spectralWeight_dilate_le_uniform hT hN' (norm_circleMap_one θ) hθ
  have hm_eq : m = 0 := by
    by_contra hne
    have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hne)
    set R : ℝ := C₁ * M - c * refMass ^ 2 with hR
    have hDm : 0 < refMass / 6 * m := by positivity
    obtain ⟨n, hn⟩ := exists_nat_gt (|R| / (refMass / 6 * m) + 1)
    have hT1 : (1 : ℝ) ≤ n := by
      have : 0 ≤ |R| / (refMass / 6 * m) := div_nonneg (abs_nonneg R) hDm.le
      linarith
    have hk := key n hT1
    have hn2 : |R| / (refMass / 6 * m) + 1 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hcontra : |R| + refMass / 6 * m ≤ (n : ℝ) ^ 2 * refMass / 6 * m := by
      calc |R| + refMass / 6 * m = (|R| / (refMass / 6 * m) + 1) * (refMass / 6 * m) := by
            field_simp
        _ ≤ (n : ℝ) ^ 2 * (refMass / 6 * m) := mul_le_mul_of_nonneg_right hn2 hDm.le
        _ = (n : ℝ) ^ 2 * refMass / 6 * m := by ring
    linarith [le_abs_self R]
  exact (measureReal_eq_zero_iff (measure_ne_top ν _)).mp hm_eq

/-! ## The far-ordinate inequality -/

/-- The critical ordinates at distance at least `δ` from the centre. -/
def farSet (δ : ℝ) : Set ℝ := {θ | circleMap 0 1 θ ≠ 1 ∧ δ ≤ angleOrd θ}

/-- The near-centre piece off `ζ = 1`. -/
def nearSet (δ : ℝ) : Set ℝ := {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < δ}

theorem measurableSet_farSet (δ : ℝ) : MeasurableSet (farSet δ) := by
  show MeasurableSet ({θ | circleMap 0 1 θ ≠ 1} ∩ {θ | δ ≤ angleOrd θ})
  exact ((measurable_circleMap 0 1 (measurableSet_singleton 1)).compl).inter
    (measurableSet_le measurable_const measurable_angleOrd)

theorem measurableSet_nearSet (δ : ℝ) : MeasurableSet (nearSet δ) := by
  show MeasurableSet ({θ | circleMap 0 1 θ ≠ 1} ∩ {θ | angleOrd θ < δ})
  exact ((measurable_circleMap 0 1 (measurableSet_singleton 1)).compl).inter
    (measurableSet_lt measurable_angleOrd measurable_const)

/-- `1/γ` is integrable on the far set (bounded by `1/δ`). -/
theorem integrableOn_inv_angleOrd_farSet {ν : Measure ℝ} [IsFiniteMeasure ν] {δ : ℝ}
    (hδ : 0 < δ) : IntegrableOn (fun θ => 1 / angleOrd θ) (farSet δ) ν := by
  refine Integrable.mono' (integrable_const (1 / δ)) (measurable_angleOrd.const_div 1).aestronglyMeasurable ?_
  rw [ae_restrict_iff' (measurableSet_farSet δ)]
  refine Eventually.of_forall fun θ hθ => ?_
  have hγ : δ ≤ angleOrd θ := hθ.2
  rw [Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr (by linarith))]
  exact one_div_le_one_div_of_le hδ hγ

/-- **The far-ordinate inequality**: positivity on the dilation ray gives
`∫_{γ ≥ δ} dν/γ ≤ δ ν(S¹) − c` for every `0 < δ ≤ 1`. -/
theorem integral_farSet_inv_le_of_dilationRay {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hsupp : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} = 0)
    (hrep : ∀ a : ℂ, 0 < a.re → 0 < a.im →
      a * Ψ (1 / 2 + a) =
        (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c)
    (hpos : ∀ T : ℝ, 1 ≤ T →
      0 ≤ (weilFullFunctional lam (EF.weilTest (dilate T) (dilate T))).re)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ θ in farSet δ, 1 / angleOrd θ ∂ν ≤ δ * ν.real univ - c := by
  obtain ⟨N₀, N₂, -, -, hN⟩ := exists_profile_bounds contDiff_refProfile hasCompactSupport_refProfile
  have hN' : ∀ v : ℝ, v ^ 2 * ‖paperFT refProfileC v‖ ≤ N₂ := fun v => (hN v).2
  have hN0 : 0 ≤ N₂ := le_trans (by positivity) (hN' 0)
  set M : ℝ := ν.real univ with hM
  have hM0 : 0 ≤ M := measureReal_nonneg
  set D := refMass with hDdef
  have hD := refMass_pos
  set Kδ : ℝ := N₂ ^ 2 * (1 / δ ^ 3 + 1 / δ) with hKδ
  have hKδ0 : 0 ≤ Kδ := by positivity
  set J : ℝ := ∫ θ in farSet δ, 1 / angleOrd θ ∂ν with hJ
  have hJi := integrableOn_inv_angleOrd_farSet (ν := ν) hδ
  have key : ∀ T : ℝ, 1 ≤ T → J ≤ Kδ * M / (D ^ 2 * T ^ 4) + δ * M - c := by
    intro T hT
    have hT0 : 0 < T := by linarith
    have hT2 : 0 < T ^ 2 := by positivity
    have hW := hpos T hT
    rw [re_weilFullFunctional_eq_integral_spectralWeight_sub hsl hΨd hΨe hsupp hrep (contDiff_dilate T)
      (hasCompactSupport_dilate hT0), paperFT_dilate_zero hT0, Complex.norm_real, Real.norm_eq_abs,
      sq_abs] at hW
    have hDeq : ∫ x, refProfile x = refMass := rfl
    rw [hDeq] at hW
    -- the bound function
    set b : ℝ → ℝ := fun θ =>
      (farSet δ).indicator (fun θ => Kδ / T ^ 2 - T ^ 2 * D ^ 2 / angleOrd θ) θ +
        (farSet δ)ᶜ.indicator (fun _ => T ^ 2 * δ * D ^ 2) θ with hb
    have hae : ∀ᵐ θ ∂ν, oddSpectralWeight (dilate T) (circleMap 0 1 θ) ≤ b θ := by
      filter_upwards [ae_support_of_measure_eq_zero hsupp] with θ hθ
      simp only [hb]
      by_cases hc : θ ∈ farSet δ
      · rw [Set.indicator_of_mem hc, Set.indicator_of_notMem (by simpa using hc), add_zero]
        obtain ⟨h1, hγ⟩ := hc
        have hγ0 : 0 < circleOrd (circleMap 0 1 θ) := by change 0 < angleOrd θ; linarith
        have h := spectralWeight_dilate_le_of_pos_decay hT0 hN' (norm_circleMap_one θ) h1 hγ0
        have hγ' : δ ≤ circleOrd (circleMap 0 1 θ) := hγ
        have hfrac : (1 + circleOrd (circleMap 0 1 θ) ^ 2) * N₂ ^ 2 /
            (T ^ 2 * circleOrd (circleMap 0 1 θ) ^ 3) ≤ Kδ / T ^ 2 := by
          rw [hKδ, div_le_div_iff₀ (by positivity) hT2]
          have hγ3 : δ ^ 3 ≤ circleOrd (circleMap 0 1 θ) ^ 3 := pow_le_pow_left₀ hδ.le hγ' 3
          have e : (1 + circleOrd (circleMap 0 1 θ) ^ 2) * N₂ ^ 2 * T ^ 2 =
              T ^ 2 * N₂ ^ 2 * (1 + circleOrd (circleMap 0 1 θ) ^ 2) := by ring
          rw [e]
          have hγδ : 1 / δ ^ 3 + 1 / δ ≥ (1 + circleOrd (circleMap 0 1 θ) ^ 2) /
              circleOrd (circleMap 0 1 θ) ^ 3 := by
            rw [ge_iff_le, div_le_iff₀ (by positivity)]
            have h1' : 1 ≤ 1 / δ ^ 3 * circleOrd (circleMap 0 1 θ) ^ 3 := by
              rw [show 1 / δ ^ 3 * circleOrd (circleMap 0 1 θ) ^ 3 =
                circleOrd (circleMap 0 1 θ) ^ 3 / δ ^ 3 by ring, le_div_iff₀ (by positivity)]
              linarith
            have h2' : circleOrd (circleMap 0 1 θ) ^ 2 ≤ 1 / δ * circleOrd (circleMap 0 1 θ) ^ 3 := by
              rw [show 1 / δ * circleOrd (circleMap 0 1 θ) ^ 3 =
                circleOrd (circleMap 0 1 θ) ^ 3 / δ by ring, le_div_iff₀ hδ]
              nlinarith
            nlinarith
          rw [ge_iff_le, div_le_iff₀ (by positivity)] at hγδ
          have hTN : (0 : ℝ) ≤ T ^ 2 * N₂ ^ 2 := by positivity
          exact le_trans (mul_le_mul_of_nonneg_left hγδ hTN) (le_of_eq (by ring))
        change oddSpectralWeight (dilate T) (circleMap 0 1 θ) ≤
          Kδ / T ^ 2 - T ^ 2 * D ^ 2 / circleOrd (circleMap 0 1 θ)
        linarith
      · rw [Set.indicator_of_notMem hc, Set.indicator_of_mem (by simpa using hc), zero_add]
        have hpos' : 0 ≤ T ^ 2 * δ * D ^ 2 := by positivity
        by_cases h1 : circleMap 0 1 θ = 1
        · rw [h1, oddSpectralWeight_one (contDiff_dilate T) (hasCompactSupport_dilate hT0)]
          exact hpos'
        · have hγ : -(1 / 4) ≤ circleOrd (circleMap 0 1 θ) := hθ.resolve_left h1
          have hlt : circleOrd (circleMap 0 1 θ) < δ := by
            by_contra h
            exact hc ⟨h1, not_lt.mp h⟩
          rcases lt_trichotomy (circleOrd (circleMap 0 1 θ)) 0 with hneg | hzero | hposγ
          · exact (spectralWeight_dilate_nonpos_of_cut hT0 (norm_circleMap_one θ) h1 hγ hneg).trans hpos'
          · have : circleMap 0 1 θ = -1 := by
              rw [eq_bdryPt_circleOrd (norm_circleMap_one θ) h1, hzero, bdryPt_zero]
            rw [this]
            refine (spectralWeight_dilate_neg_one_le hT).trans ?_
            have : 0 ≤ T ^ 4 * refMass / 6 := by positivity
            linarith
          · have := spectralWeight_dilate_le_mul_of_pos hT0 (norm_circleMap_one θ) h1 hposγ
            have : T ^ 2 * circleOrd (circleMap 0 1 θ) * refMass ^ 2 ≤ T ^ 2 * δ * D ^ 2 := by
              rw [hDdef]
              have : 0 ≤ T ^ 2 * refMass ^ 2 := by positivity
              nlinarith
            linarith
    -- integrability and the value of `∫ b`
    have hfar : IntegrableOn (fun θ => Kδ / T ^ 2 - T ^ 2 * D ^ 2 / angleOrd θ) (farSet δ) ν := by
      have : (fun θ => Kδ / T ^ 2 - T ^ 2 * D ^ 2 / angleOrd θ) =
          fun θ => Kδ / T ^ 2 - T ^ 2 * D ^ 2 * (1 / angleOrd θ) := by
        funext θ; ring
      rw [this]
      exact (integrableOn_const (C := Kδ / T ^ 2) (by simp)).sub (hJi.const_mul _)
    have hb1 : Integrable ((farSet δ).indicator fun θ => Kδ / T ^ 2 - T ^ 2 * D ^ 2 / angleOrd θ) ν :=
      (integrable_indicator_iff (measurableSet_farSet δ)).mpr hfar
    have hb2 : Integrable ((farSet δ)ᶜ.indicator fun _ => T ^ 2 * δ * D ^ 2) ν :=
      (integrable_const _).indicator (measurableSet_farSet δ).compl
    have hbi : Integrable b ν := hb1.add hb2
    have hle := integral_mono_ae (integrable_spectralWeight_circleMap hsupp (contDiff_dilate T)
      (hasCompactSupport_dilate hT0)) hbi hae
    have hbint : ∫ θ, b θ ∂ν =
        (Kδ / T ^ 2) * ν.real (farSet δ) - T ^ 2 * D ^ 2 * J +
          T ^ 2 * δ * D ^ 2 * ν.real (farSet δ)ᶜ := by
      simp only [hb]
      rw [integral_add hb1 hb2, integral_indicator (measurableSet_farSet δ),
        integral_indicator_const _ (measurableSet_farSet δ).compl, smul_eq_mul]
      have e : ∫ θ in farSet δ, (Kδ / T ^ 2 - T ^ 2 * D ^ 2 / angleOrd θ) ∂ν =
          (Kδ / T ^ 2) * ν.real (farSet δ) - T ^ 2 * D ^ 2 * J := by
        have : (fun θ => Kδ / T ^ 2 - T ^ 2 * D ^ 2 / angleOrd θ) =
            fun θ => Kδ / T ^ 2 - T ^ 2 * D ^ 2 * (1 / angleOrd θ) := by
          funext θ; ring
        rw [this, integral_sub (integrableOn_const (C := Kδ / T ^ 2) (by simp)) (hJi.const_mul _),
          setIntegral_const, integral_const_mul, smul_eq_mul, hJ]
        ring
      rw [e]
      ring
    rw [hbint] at hle
    have hfarM : ν.real (farSet δ) ≤ M := measureReal_mono (subset_univ _)
    have hfarcM : ν.real (farSet δ)ᶜ ≤ M := measureReal_mono (subset_univ _)
    have hfar0 : 0 ≤ ν.real (farSet δ) := measureReal_nonneg
    -- `T² D² J ≤ Kδ M / T² + T² δ D² M − c T² D²`
    have h1 : T ^ 2 * D ^ 2 * J ≤ Kδ / T ^ 2 * M + T ^ 2 * δ * D ^ 2 * M - c * (T * D) ^ 2 := by
      have hq1 : Kδ / T ^ 2 * ν.real (farSet δ) ≤ Kδ / T ^ 2 * M :=
        mul_le_mul_of_nonneg_left hfarM (by positivity)
      have hq2 : T ^ 2 * δ * D ^ 2 * ν.real (farSet δ)ᶜ ≤ T ^ 2 * δ * D ^ 2 * M :=
        mul_le_mul_of_nonneg_left hfarcM (by positivity)
      linarith
    have hT4 : 0 < D ^ 2 * T ^ 4 := by positivity
    have hD0 : D ≠ 0 := hD.ne'
    have hT0' : T ≠ 0 := hT0.ne'
    rw [show Kδ * M / (D ^ 2 * T ^ 4) + δ * M - c =
        (Kδ / T ^ 2 * M + T ^ 2 * δ * D ^ 2 * M - c * (T * D) ^ 2) / (T ^ 2 * D ^ 2) by
      field_simp, le_div_iff₀ (by positivity)]
    linarith
  -- let `T → ∞`
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hKM : 0 ≤ Kδ * M / D ^ 2 := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (Kδ * M / D ^ 2 / ε + 1)
  have hn1 : (1 : ℝ) ≤ n := by
    have : 0 ≤ Kδ * M / D ^ 2 / ε := by positivity
    linarith
  have hk := key n hn1
  have hn4 : Kδ * M / D ^ 2 / ε < (n : ℝ) ^ 4 := by
    have h3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1
    nlinarith
  have hsmall : Kδ * M / (D ^ 2 * (n : ℝ) ^ 4) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hn4
    have hD2 : 0 < D ^ 2 := by positivity
    have := mul_lt_mul_of_pos_right hn4 hD2
    rw [div_mul_cancel₀ _ hD2.ne'] at this
    linarith
  linarith

/-! ## Positivity of the extension on the real half-line -/

theorem integrable_nevKernel_circleMap {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hcut : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < 0} = 0) {z : ℂ} (hz : z ∈ offNegAxis) :
    Integrable (fun θ => nevKernel z (circleMap 0 1 θ)) ν := by
  obtain ⟨ε, hε, hball⟩ := exists_ball_bound_of_mem_offNegAxis hz
  set R : ℝ := ‖z‖ + ε with hR
  have hR0 : 0 ≤ R := by positivity
  have hae := ae_support_of_cut_eq_zero hcut
  have hzball : z ∈ Metric.ball z ε := Metric.mem_ball_self hε
  have hγ0 : ∀ ζ : ℂ, (ζ = 1 ∨ 0 ≤ circleOrd ζ) → 0 ≤ circleOrd ζ := fun ζ h => by
    rcases h with h | h
    · rw [h, circleOrd_one]
    · exact h
  refine Integrable.mono' (integrable_const (((2 * R + 1) * ‖z‖ + 1) / ε + 2 * ‖z‖ + 2))
    (measurable_nevKernel_circleMap z).aestronglyMeasurable ?_
  filter_upwards [hae] with θ hθ
  exact norm_nevKernel_le hε hR0 hθ (fun _ => (hball z hzball _ (hγ0 _ hθ)).1)
    (fun _ => (hball z hzball _ (hγ0 _ hθ)).2)

/-- The real part of the kernel at a real point, at `ζ = 1`. -/
theorem re_nevKernel_ofReal_one (z : ℝ) : (nevKernel (z : ℂ) 1).re = z := by
  simp [nevKernel]

/-- The real part of the kernel at a real point, off `ζ = 1`. -/
theorem re_nevKernel_ofReal_of_ne (z : ℝ) {ζ : ℂ} (h1 : ζ ≠ 1) :
    (nevKernel (z : ℂ) ζ).re = (circleOrd ζ * z - 1) / (z + circleOrd ζ) := by
  simp only [nevKernel, h1, if_false]
  have : ((circleOrd ζ : ℂ) * (z : ℂ) - 1) / ((z : ℂ) + circleOrd ζ) =
      (((circleOrd ζ * z - 1) / (z + circleOrd ζ) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

theorem le_re_nevKernel_of_le {z γ δ : ℝ} (hz : 0 < z) (hγ : δ ≤ γ) (hδ : 0 < δ) :
    -(1 / γ) ≤ (γ * z - 1) / (z + γ) := by
  have hγ0 : 0 < γ := lt_of_lt_of_le hδ hγ
  rw [le_div_iff₀ (by linarith), neg_mul, neg_le_iff_add_nonneg]
  have : (γ * z - 1) + 1 / γ * (z + γ) = z * (γ + 1 / γ) := by field_simp; ring
  nlinarith [one_div_pos.mpr hγ0]

theorem le_re_nevKernel_of_nonneg {z γ : ℝ} (hz : 0 < z) (hγ : 0 ≤ γ) :
    -(1 / z) ≤ (γ * z - 1) / (z + γ) := by
  rw [le_div_iff₀ (by linarith), neg_mul, neg_le_iff_add_nonneg]
  have : (γ * z - 1) + 1 / z * (z + γ) = γ * (z + 1 / z) := by field_simp; ring
  rw [this]
  have : 0 < z + 1 / z := by positivity
  positivity

/-- The near sets shrink to a null set. -/
theorem tendsto_measureReal_nearSet {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hcut : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < 0} = 0)
    (hcen : ν {θ : ℝ | circleMap 0 1 θ = -1} = 0) :
    Tendsto (fun n : ℕ => ν.real (nearSet (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  have hanti : Antitone fun n : ℕ => nearSet (1 / ((n : ℝ) + 1)) := by
    intro m n hmn θ hθ
    refine ⟨hθ.1, lt_of_lt_of_le hθ.2 ?_⟩
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
  have hinter : ν (⋂ n : ℕ, nearSet (1 / ((n : ℝ) + 1))) = 0 := by
    refine measure_mono_null (fun θ hθ => ?_) (measure_union_null hcut hcen)
    rw [Set.mem_iInter] at hθ
    have h1 : circleMap 0 1 θ ≠ 1 := (hθ 0).1
    have hle : angleOrd θ ≤ 0 := by
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
      have := (hθ n).2
      have hn' : 1 / ((n : ℝ) + 1) < ε := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hε] at hn
        linarith
      linarith
    rcases hle.lt_or_eq with hlt | heq
    · exact Or.inl ⟨h1, hlt⟩
    · right
      show circleMap 0 1 θ = -1
      rw [eq_bdryPt_circleOrd (norm_circleMap_one θ) h1]
      have heq' : circleOrd (circleMap 0 1 θ) = 0 := heq
      rw [heq', bdryPt_zero]
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (measurableSet_nearSet _).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at h
  have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at h'
  exact h'

/-- **The kernel integral dominates the constant**: `c ≤ Re ∫ k(z, ζ) dν(ζ)` for real `z > 0`. -/
theorem le_re_integral_nevKernel {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hcut : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < 0} = 0)
    (hcen : ν {θ : ℝ | circleMap 0 1 θ = -1} = 0)
    (hfar : ∀ δ : ℝ, 0 < δ → ∫ θ in farSet δ, 1 / angleOrd θ ∂ν ≤ δ * ν.real univ - c)
    {z : ℝ} (hz : 0 < z) :
    c ≤ (∫ θ, nevKernel (z : ℂ) (circleMap 0 1 θ) ∂ν).re := by
  have hzo : (z : ℂ) ∈ offNegAxis := Or.inr (by simpa using hz)
  have hi := integrable_nevKernel_circleMap hcut hzo
  have hre : (∫ θ, nevKernel (z : ℂ) (circleMap 0 1 θ) ∂ν).re =
      ∫ θ, (nevKernel (z : ℂ) (circleMap 0 1 θ)).re ∂ν := by
    have h := integral_re hi
    simp only [RCLike.re_to_complex] at h
    exact h.symm
  rw [hre]
  set M : ℝ := ν.real univ with hM
  -- the a.e. support: `ζ = 1 ∨ 0 < γ`
  have hae : ∀ᵐ θ ∂ν, circleMap 0 1 θ = 1 ∨ 0 < circleOrd (circleMap 0 1 θ) := by
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) (measure_union_null hcut hcen)
    simp only [Set.mem_setOf_eq, not_or, not_lt] at hθ
    rcases hθ.2.lt_or_eq with hlt | heq
    · exact Or.inl ⟨hθ.1, hlt⟩
    · right
      show circleMap 0 1 θ = -1
      rw [eq_bdryPt_circleOrd (norm_circleMap_one θ) hθ.1, heq, bdryPt_zero]
  -- lower bound for every `δ`
  have hlow : ∀ δ : ℝ, 0 < δ →
      c - δ * M - ν.real (nearSet δ) / z ≤ ∫ θ, (nevKernel (z : ℂ) (circleMap 0 1 θ)).re ∂ν := by
    intro δ hδ
    set L : ℝ → ℝ := fun θ => -((farSet δ).indicator (fun θ => 1 / angleOrd θ) θ +
      (nearSet δ).indicator (fun _ => 1 / z) θ) with hL
    have hJi := integrableOn_inv_angleOrd_farSet (ν := ν) hδ
    have hL1 : Integrable ((farSet δ).indicator fun θ => 1 / angleOrd θ) ν :=
      (integrable_indicator_iff (measurableSet_farSet δ)).mpr hJi
    have hL2 : Integrable ((nearSet δ).indicator fun _ => 1 / z) ν :=
      (integrable_const _).indicator (measurableSet_nearSet δ)
    have hLi : Integrable L ν := (hL1.add hL2).neg
    have hpt : ∀ᵐ θ ∂ν, L θ ≤ (nevKernel (z : ℂ) (circleMap 0 1 θ)).re := by
      filter_upwards [hae] with θ hθ
      simp only [hL]
      rcases hθ with h1 | hγ
      · rw [h1, re_nevKernel_ofReal_one]
        have hf : θ ∉ farSet δ := fun h => h.1 h1
        have hn : θ ∉ nearSet δ := fun h => h.1 h1
        rw [Set.indicator_of_notMem hf, Set.indicator_of_notMem hn, add_zero, neg_zero]
        exact hz.le
      · have h1 : circleMap 0 1 θ ≠ 1 := by
          intro h; rw [h, circleOrd_one] at hγ; exact lt_irrefl _ hγ
        rw [re_nevKernel_ofReal_of_ne _ h1]
        by_cases hfar' : δ ≤ angleOrd θ
        · have hf : θ ∈ farSet δ := ⟨h1, hfar'⟩
          have hn : θ ∉ nearSet δ := fun h => absurd h.2 (not_lt.mpr hfar')
          rw [Set.indicator_of_mem hf, Set.indicator_of_notMem hn, add_zero]
          exact le_re_nevKernel_of_le hz hfar' hδ
        · have hn : θ ∈ nearSet δ := ⟨h1, not_le.mp hfar'⟩
          have hf : θ ∉ farSet δ := fun h => hfar' h.2
          rw [Set.indicator_of_notMem hf, Set.indicator_of_mem hn, zero_add]
          exact le_re_nevKernel_of_nonneg hz hγ.le
    have hmono := integral_mono_ae hLi (hi.re) hpt
    simp only [RCLike.re_to_complex] at hmono
    have hLint : ∫ θ, L θ ∂ν =
        -((∫ θ in farSet δ, 1 / angleOrd θ ∂ν) + ν.real (nearSet δ) * (1 / z)) := by
      simp only [hL]
      rw [integral_neg, integral_add hL1 hL2, integral_indicator (measurableSet_farSet δ),
        integral_indicator_const _ (measurableSet_nearSet δ), smul_eq_mul]
    rw [hLint] at hmono
    have hf : ∫ θ in farSet δ, 1 / angleOrd θ ∂ν ≤ δ * M - c := hfar δ hδ
    have : ν.real (nearSet δ) * (1 / z) = ν.real (nearSet δ) / z := by ring
    linarith
  -- let `δ → 0`
  by_contra hlt
  push Not at hlt
  set X := ∫ θ, (nevKernel (z : ℂ) (circleMap 0 1 θ)).re ∂ν with hX
  set ε := c - X with hε
  have hε0 : 0 < ε := by linarith
  have hnear := tendsto_measureReal_nearSet hcut hcen
  have hev1 : ∀ᶠ n : ℕ in atTop, ν.real (nearSet (1 / ((n : ℝ) + 1))) < ε * z / 2 :=
    hnear.eventually (gt_mem_nhds (by positivity))
  have hev2 : ∀ᶠ n : ℕ in atTop, (1 / ((n : ℝ) + 1)) * M < ε / 2 := by
    have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * M) atTop (𝓝 (0 * M)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mul_const M
    rw [zero_mul] at h0
    exact h0.eventually (gt_mem_nhds (by positivity))
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hl := hlow _ hδ
  have h3 : ν.real (nearSet (1 / ((n : ℝ) + 1))) / z < ε / 2 := by
    rw [div_lt_iff₀ hz]; linarith
  linarith

/-- **The cut-free extension is nonnegative on `(½, ∞)`.** -/
theorem re_cutFreeExtension_nonneg {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hcut : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < 0} = 0)
    (hcen : ν {θ : ℝ | circleMap 0 1 θ = -1} = 0)
    (hfar : ∀ δ : ℝ, 0 < δ → ∫ θ in farSet δ, 1 / angleOrd θ ∂ν ≤ δ * ν.real univ - c)
    {x : ℝ} (hx : 1 / 2 < x) : 0 ≤ (cutFreeExtension ν c x).re := by
  have ha : 0 < x - 1 / 2 := by linarith
  have hz : 0 < (x - 1 / 2) ^ 2 := by positivity
  have hsq : ((x : ℂ) - 1 / 2) ^ 2 = (((x - 1 / 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hden : (x : ℂ) - 1 / 2 = ((x - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  unfold cutFreeExtension
  rw [hsq, hden, Complex.div_ofReal_re, Complex.sub_re, Complex.ofReal_re]
  have := le_re_integral_nevKernel hcut hcen hfar hz
  exact div_nonneg (by linarith) ha.le

/-! ## The dilation-ray criterion -/

/-- **Odd positivity and positivity on the dilation ray of one bump give `λ = Λ` and RH.** -/
theorem eq_vonMangoldt_and_riemannHypothesis_of_dilationRay_nonneg {lam : ℕ → ℝ}
    (hW : WeilPositiveOdd lam)
    (hpos : ∀ T : ℝ, 1 ≤ T →
      0 ≤ (weilFullFunctional lam (EF.weilTest (dilate T) (dilate T))).re) :
    (∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  obtain ⟨Ψ, hΨd, hΨe, -, ν, hν, c, hsupp, hrep⟩ := exists_nevanlinna_measure_of_weilPositiveOdd hW
  have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := fun σ hσ =>
    OddSector.summable_abs_div_rpow_of_weilPositiveOddAt_anyWeight
      (weilPositiveOddAt_one_iff.mpr hW) hσ
  have hcut := cut_measure_eq_zero_of_dilationRay hsl hΨd hΨe hsupp hrep hpos
  have hcen := measure_centre_eq_zero_of_dilationRay hsl hΨd hΨe hsupp hrep hpos
  have hfar : ∀ δ : ℝ, 0 < δ →
      ∫ θ in farSet δ, 1 / angleOrd θ ∂ν ≤ δ * ν.real univ - c := fun δ hδ =>
    integral_farSet_inv_le_of_dilationRay hsl hΨd hΨe hsupp hrep hpos hδ
  refine eq_vonMangoldt_and_riemannHypothesis_of_weilPositiveOdd_of_extension hW
    (differentiableOn_cutFreeExtension hcut c)
    (fun s hs => cutFreeExtension_eq_weilFunction hΨd hΨe hcut hrep hs)
    fun x hx => re_cutFreeExtension_nonneg hcut hcen hfar hx

/-- **RH is the existence of an odd Weil-positive weight that is Weil-positive on the dilation ray
of one bump.** -/
theorem riemannHypothesis_iff_exists_weilPositiveOdd_dilationRay :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveOdd lam ∧ ∀ T : ℝ, 1 ≤ T →
      0 ≤ (weilFullFunctional lam (EF.weilTest (dilate T) (dilate T))).re := by
  constructor
  · intro hRH
    have hF := riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH
    refine ⟨_, weilPositiveOdd_of_weilPositiveFull hF, fun T hT => ?_⟩
    exact hF _ (contDiff_dilate T) (hasCompactSupport_dilate (by linarith))
  · rintro ⟨lam, hW, hpos⟩
    exact (eq_vonMangoldt_and_riemannHypothesis_of_dilationRay_nonneg hW hpos).2

end RHTower.OddResolvent
