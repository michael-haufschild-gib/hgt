import GaloisForLFunctions.RHTower.Suzuki.SuzukiRWCHMDQuotientCoordinates
import GaloisForLFunctions.RHTower.CHMDBirmanSchwingerBound
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaSlepianStrictSource
import GaloisForLFunctions.RHTower.GaussianEvenCarrier

/-!
# On a fixed aperture the CHMD graph norm is the restricted Weil form norm

For a real smooth source `u` supported in `[−r, r]`, `r < a`, the CHMD lift `p = testLift u` has the
inverse-Doob source `u/Φ` in the theta–cosh mass space, and its graph norm obeys the exact identity

`‖p‖² = W(u) + 2‖u/Φ‖²_μ − 2⟨u/Φ, 1⟩²_μ + 2⟨u/Φ, tanh(x/2)⟩²_μ`,

while the restricted Weil form is `W(u) = ‖u‖²_W + ⟨B u, u⟩` with a bounded remainder `B`. The mass
norm `‖u/Φ‖²_μ = ∫ u² cosh(x/2)/Φ` is comparable to `∫ u²` on the aperture, from above by
`cosh(a/2)/min_{[−a,a]} Φ` and from below by `1/max Φ`. Hence there are `c, C > 0` depending only on
`a` with

`c ‖u‖²_W ≤ ‖testLift u‖² ≤ C ‖u‖²_W`        (`exists_testLift_norm_sq_equiv_weilFormNorm`).

So on a fixed aperture the CHMD graph completion of the common core and the restricted Weil form
domain carry equivalent norms, and the CHMD signed-radical quotient coordinate is continuous for the
Weil form norm (`exists_norm_suzukiCoreSignedQuotient_le`). Whether the quotient norm is bounded
below on the aperture core is not decided here.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

open GaloisForLFunctions.RHTower
noncomputable section
namespace RHTower

open CHMDDoobGraph CHMDPolar

/-- The CHMD lift of a real Suzuki source. -/
abbrev suzukiCoreTestLift (a : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    SourceGraph :=
  testLift u (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) u.hasCompactSupport

theorem weilForm_suzukiCoreTestLift (a : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore a.1) :
    weilForm (suzukiCoreTestLift a u) =
      (ccmRestrictedWeilForm a (suzukiRestrictedWeilCoreCCMFormVector a u)
        (suzukiRestrictedWeilCoreCCMFormVector a u)).re := by
  have h := suzukiCoreSignedQuotient_weil a u
  rwa [suzukiCoreSignedQuotient, quotientWeilForm_mk] at h

/-- The CHMD graph norm is the Weil form plus the shifted mass and the two polar moments. -/
theorem norm_sq_eq_weilForm_add (p : SourceGraph) :
    ‖p‖ ^ 2 = weilForm p + 2 * ‖p.val.fst‖ ^ 2 - 2 * ⟪p.val.fst, oneL⟫_ℝ ^ 2 +
      2 * ⟪p.val.fst, tanhL⟫_ℝ ^ 2 := by
  rw [weilForm_eq_weilBilin, weilBilin, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

theorem re_ccmRestrictedWeilForm_self (a : SuzukiPositiveAperture) (q : CCMArchimedeanFormDomain a) :
    (ccmRestrictedWeilForm a q q).re = ‖q‖ ^ 2 +
      (inner ℂ (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a q))
        (ccmArchimedeanFormToAperture a q)).re := by
  rw [ccmRestrictedWeilForm, Complex.add_re]
  congr 1
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) q

theorem abs_re_inner_boundedRemainder_le (a : SuzukiPositiveAperture) (q : CCMArchimedeanFormDomain a) :
    |(inner ℂ (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a q))
        (ccmArchimedeanFormToAperture a q)).re| ≤
      ‖ccmRestrictedWeilBoundedRemainder a‖ * ‖ccmArchimedeanFormToAperture a q‖ ^ 2 := by
  refine (Complex.abs_re_le_norm _).trans
    ((norm_inner_le_norm (𝕜 := ℂ) (E := suzukiApertureHilbert a) _ _).trans ?_)
  rw [sq, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)

/-- The aperture norm of the Weil form vector of a real source is its `L²` norm on the line. -/
theorem norm_sq_ccmArchimedeanFormToAperture_suzukiCore (a : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore a.1) :
    ‖ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a u)‖ ^ 2 =
      ∫ x, u x ^ 2 := by
  change ‖(ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a u) : SoninL2)‖ ^ 2 = _
  rw [norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn a u]
    with x hx
  rw [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The mass norm of the inverse-Doob source is `∫ u² cosh(x/2)/Φ`. -/
theorem norm_sq_suzukiCoreTestLift_fst (a : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore a.1) :
    ‖(suzukiCoreTestLift a u).val.fst‖ ^ 2 =
      ∫ x, Real.cosh (x / 2) * u x ^ 2 / riemannKernelReal x := by
  rw [CHMDPolar.norm_sq_eq_integral]
  have h : (∫ x, ((suzukiCoreTestLift a u).val.fst : ℝ → ℝ) x ^ 2 ∂massMeasure) =
      ∫ x, phiDoobInv u x ^ 2 ∂massMeasure := by
    apply integral_congr_ae
    filter_upwards [testLift_source u (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top))
      u.hasCompactSupport] with x hx
    rw [hx]
  rw [h, CHMDPolar.integral_mass]
  congr 1
  funext x
  have hΦ := (riemannKernelReal_pos x).ne'
  rw [massDensity, phiDoobInv]
  field_simp

/-- **Graph norm versus Weil form norm.** On a fixed aperture the CHMD graph norm of the lift of a
real source and the restricted Weil form norm of its Weil vector are uniformly equivalent. -/
theorem exists_testLift_norm_sq_equiv_weilFormNorm (a : SuzukiPositiveAperture) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : SuzukiRestrictedWeilCore a.1,
      c * ‖suzukiRestrictedWeilCoreCCMFormVector a u‖ ^ 2 ≤ ‖suzukiCoreTestLift a u‖ ^ 2 ∧
        ‖suzukiCoreTestLift a u‖ ^ 2 ≤ C * ‖suzukiRestrictedWeilCoreCCMFormVector a u‖ ^ 2 := by
  -- a global upper bound and an aperture lower bound for the Riemann kernel
  obtain ⟨K₀, hK₀, hK₀b⟩ := exists_riemannKernelReal_le
  set K : ℝ := K₀ + 1
  have hK : 0 < K := by linarith
  have hΦK : ∀ x, riemannKernelReal x ≤ K := fun x => by
    have := hK₀b x
    have he : Real.exp (-(4 * |x|)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    nlinarith
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_Icc (a := -a.1) (b := a.1)).exists_isMinOn
    ⟨0, by constructor <;> linarith [a.2]⟩ continuous_riemannKernelReal.continuousOn
  set m := riemannKernelReal x₀
  have hm : 0 < m := riemannKernelReal_pos x₀
  set M : ℝ := Real.cosh (a.1 / 2) / m
  have hM : 0 < M := by positivity
  set β := ‖ccmRestrictedWeilBoundedRemainder a‖
  set O := ‖oneL‖
  set T := ‖tanhL‖
  have hβ : 0 ≤ β := norm_nonneg (ccmRestrictedWeilBoundedRemainder a)
  have hc : 0 < 1 + 2 * O ^ 2 + β * K := by positivity
  refine ⟨1 / (1 + 2 * O ^ 2 + β * K), 1 + β + (2 + 2 * T ^ 2) * M, one_div_pos.mpr hc,
    by positivity, fun u => ?_⟩
  set q := suzukiRestrictedWeilCoreCCMFormVector a u
  set p := suzukiCoreTestLift a u
  set F := p.val.fst
  -- the two `L²` sizes of the source
  have hu2 := norm_sq_ccmArchimedeanFormToAperture_suzukiCore a u
  have hF := norm_sq_suzukiCoreTestLift_fst a u
  have hcont : Continuous fun x => u x ^ 2 := (u.smooth.continuous).pow 2
  have hcs : HasCompactSupport fun x => u x ^ 2 :=
    u.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hint : Integrable fun x => u x ^ 2 := hcont.integrable_of_hasCompactSupport hcs
  have hpt : ∀ x, u x ^ 2 / K ≤ Real.cosh (x / 2) * u x ^ 2 / riemannKernelReal x ∧
      Real.cosh (x / 2) * u x ^ 2 / riemannKernelReal x ≤ M * u x ^ 2 := by
    intro x
    have hΦ := riemannKernelReal_pos x
    constructor
    · rw [div_le_div_iff₀ hK hΦ]
      have h1 := mul_le_mul_of_nonneg_left (hΦK x) (sq_nonneg (u x))
      have h2 := mul_le_mul_of_nonneg_right (Real.one_le_cosh (x / 2))
        (mul_nonneg (sq_nonneg (u x)) hK.le)
      nlinarith
    · by_cases hux : u x = 0
      · simp [hux]
      · have hxs : x ∈ Icc (-a.1) a.1 := by
          have hx := u.support_subset hux
          exact ⟨by linarith [hx.1, u.supportRadius_lt_aperture],
            by linarith [hx.2, u.supportRadius_lt_aperture]⟩
        have hmx : m ≤ riemannKernelReal x := hmin hxs
        have hcosh : Real.cosh (x / 2) ≤ Real.cosh (a.1 / 2) := by
          rw [Real.cosh_le_cosh, abs_div, abs_div, abs_two, abs_of_pos a.2]
          exact div_le_div_of_nonneg_right (abs_le.mpr ⟨hxs.1, hxs.2⟩) (by norm_num)
        rw [div_le_iff₀ hΦ]
        calc Real.cosh (x / 2) * u x ^ 2 ≤ Real.cosh (a.1 / 2) * u x ^ 2 :=
              mul_le_mul_of_nonneg_right hcosh (sq_nonneg _)
          _ = M * m * u x ^ 2 := by rw [div_mul_cancel₀ _ hm.ne']
          _ ≤ M * u x ^ 2 * riemannKernelReal x := by
            nlinarith [mul_le_mul_of_nonneg_left hmx (mul_nonneg hM.le (sq_nonneg (u x)))]
  have hmeas : AEStronglyMeasurable (fun x => Real.cosh (x / 2) * u x ^ 2 / riemannKernelReal x) :=
    ((Real.continuous_cosh.comp (continuous_id.div_const 2)).mul hcont).div
      continuous_riemannKernelReal (fun x => (riemannKernelReal_pos x).ne') |>.aestronglyMeasurable
  have hgint : Integrable fun x => Real.cosh (x / 2) * u x ^ 2 / riemannKernelReal x :=
    (hint.const_mul M).mono' hmeas (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        have := (hpt x).1; have : 0 ≤ u x ^ 2 / K := by positivity
        linarith)]
      exact (hpt x).2)
  have hlow : (∫ x, u x ^ 2) ≤ K * ‖F‖ ^ 2 := by
    rw [hF, ← div_le_iff₀' hK, ← integral_div]
    exact integral_mono (hint.div_const K) hgint fun x => (hpt x).1
  have hup : ‖F‖ ^ 2 ≤ M * ∫ x, u x ^ 2 := by
    rw [hF, ← integral_const_mul]
    exact integral_mono hgint (hint.const_mul M) fun x => (hpt x).2
  -- the exact identities
  set R := (inner ℂ (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a q))
    (ccmArchimedeanFormToAperture a q)).re
  have hgraph : ‖p‖ ^ 2 = ‖q‖ ^ 2 + R + 2 * ‖F‖ ^ 2 - 2 * ⟪F, oneL⟫_ℝ ^ 2 +
      2 * ⟪F, tanhL⟫_ℝ ^ 2 := by
    have h := norm_sq_eq_weilForm_add p
    rw [weilForm_suzukiCoreTestLift, re_ccmRestrictedWeilForm_self] at h
    exact h
  have hB : |R| ≤ β * ∫ x, u x ^ 2 := by
    have h := abs_re_inner_boundedRemainder_le a q
    rw [hu2] at h
    exact h
  have hιq : (∫ x, u x ^ 2) ≤ ‖q‖ ^ 2 := by
    rw [← hu2]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_ccmArchimedeanFormToAperture_le a q) 2
  have hO : ⟪F, oneL⟫_ℝ ^ 2 ≤ ‖F‖ ^ 2 * O ^ 2 := by
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
  have hT : ⟪F, tanhL⟫_ℝ ^ 2 ≤ ‖F‖ ^ 2 * T ^ 2 := by
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
  have hFp : ‖F‖ ^ 2 ≤ ‖p‖ ^ 2 := by
    have h2 : ‖p‖ ^ 2 = ‖F‖ ^ 2 + ‖p.val.snd‖ ^ 2 := by
      change ‖p.val‖ ^ 2 = _
      exact WithLp.prod_norm_sq_eq_of_L2 _
    nlinarith [sq_nonneg ‖p.val.snd‖]
  have hI0 : 0 ≤ ∫ x, u x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hab := abs_le.mp hB
  have hF0 : 0 ≤ ‖F‖ ^ 2 := sq_nonneg _
  constructor
  · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀' hc]
    have h1 := mul_le_mul_of_nonneg_left hlow hβ
    have h2 := mul_le_mul_of_nonneg_left hFp (by positivity : (0 : ℝ) ≤ β * K + 2 * O ^ 2)
    nlinarith [sq_nonneg ⟪F, tanhL⟫_ℝ]
  · have hT0 : (0 : ℝ) ≤ 2 + 2 * T ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hup hT0
    have h2 := mul_le_mul_of_nonneg_left hιq hβ
    have h3 := mul_le_mul_of_nonneg_left hιq (mul_nonneg hT0 hM.le)
    nlinarith [sq_nonneg ⟪F, oneL⟫_ℝ]

/-- The CHMD quotient coordinate of the common core is continuous for the Weil form norm. -/
theorem exists_norm_suzukiCoreSignedQuotient_le (a : SuzukiPositiveAperture) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : SuzukiRestrictedWeilCore a.1,
      ‖suzukiCoreSignedQuotient a u‖ ≤ C * ‖suzukiRestrictedWeilCoreCCMFormVector a u‖ := by
  obtain ⟨c, C, -, hC, h⟩ := exists_testLift_norm_sq_equiv_weilFormNorm a
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, fun u => ?_⟩
  refine (Submodule.Quotient.norm_mk_le signedRadical (suzukiCoreTestLift a u)).trans ?_
  rw [← Real.sqrt_sq (norm_nonneg (suzukiCoreTestLift a u)),
    ← Real.sqrt_sq (norm_nonneg (suzukiRestrictedWeilCoreCCMFormVector a u)), ← Real.sqrt_mul hC.le]
  exact Real.sqrt_le_sqrt (h u).2

end RHTower
