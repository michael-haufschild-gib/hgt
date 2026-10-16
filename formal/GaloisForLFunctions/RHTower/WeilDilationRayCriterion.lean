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

end RHTower.OddResolvent
