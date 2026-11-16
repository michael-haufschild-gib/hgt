import GaloisForLFunctions.HTGeometry.CompactTestTransformOrder
import GaloisForLFunctions.RHTower.EigenPairFrequencyInversion
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineWeakEquation
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroSeriesIsTheStateLeftOfTheWallAndThePrimeSideBeyond

/-!
# The explicit formula holds at the state against smooth tests

For a smooth test `ψ` of compact support put `ψ̂(p) = ∫ ψ(u) e^{−pu} du`. For the critical state `F`,

  `Σ_z L F(z) ψ̂(z) = a (∫_{x>0} ψ(x) F⁺(x) dx − ∫_{u<0} ψ(u) e^{−8u} F(u) du)`,

the sum over the centred zeros with multiplicity. This is the identity of distributions

  `Σ_z L F(z) e^{−zu} = a (F⁺(u) 1_{u>0} − e^{−8u} F(u) 1_{u<0})`

tested against `ψ`. Consequences:

* a test supported left of the wall reads the state: `Σ_z L F(z) ψ̂(z) = −a ∫ ψ(u) e^{−8u} F(u) du`;
* a test supported beyond the wall reads the prime side: `Σ_z L F(z) ψ̂(z) = a ∫ ψ(x) F⁺(x) dx`;
* for a real smooth test `G` of compact support in `u < 0`, Weil's bare form of the pair is its zero
  side: `W(F, G) = Σ_z L F(z) L G(−z)`.

Mechanism. `ψ̂` is entire and decays faster than every power on vertical strips, so the two lines
`Re p = 5` and `Re p = −2` weigh the zero values against it. On each line the transform of the state
is a Laplace integral, and `∫ ψ̂(σ + it) e^{(σ + it)x} dt = 2π ψ(x)` by Fourier inversion, so by
Fubini each line integral is a pairing with `ψ`. The last statement adds the weak equation of the
state, which turns the confinement pairing into Weil's form.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology
open scoped FourierTransform ContDiff

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The transform of a smooth test -/

/-- The two-sided Laplace transform of a test, `∫ ψ(u) e^{−pu} du`. -/
def laplaceTest (ψ : ℝ → ℂ) (p : ℂ) : ℂ := testTransform ψ (I * p)

theorem laplaceTest_eq_integral (ψ : ℝ → ℂ) (p : ℂ) :
    laplaceTest ψ p = ∫ u : ℝ, ψ u * Complex.exp (-(p * u)) := by
  unfold laplaceTest testTransform
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show ψ u * Complex.exp (I * (I * p) * (u : ℂ)) = ψ u * Complex.exp (-(p * u))
  have h : I * (I * p) * (u : ℂ) = -(p * u) := by
    linear_combination p * (u : ℂ) * Complex.I_mul_I
  rw [h]

theorem differentiable_laplaceTest {ψ : ℝ → ℂ} (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    Differentiable ℂ (laplaceTest ψ) := by
  unfold laplaceTest
  exact (differentiable_testTransform hc hs).comp (differentiable_id.const_mul I)

/-- Fourth-order decay of the transform of a smooth test, uniformly on a vertical strip. -/
theorem exists_laplaceTest_decay {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ)
    (a b : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ σ t : ℝ, a ≤ σ → σ ≤ b →
      ‖laplaceTest ψ (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_testTransform_decay_order hψ hs a b 4
  refine ⟨C, hC0, fun σ t h1 h2 => ?_⟩
  have him : (I * ((σ : ℂ) + t * I)).im = σ := by simp
  have hmem : (I * ((σ : ℂ) + t * I)).im ∈ uIcc a b := by
    rw [him]
    exact Set.mem_uIcc.mpr (Or.inl ⟨h1, h2⟩)
  have h := hC _ hmem
  have hn : ‖I * ((σ : ℂ) + t * I)‖ = ‖(σ : ℂ) + t * I‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have him2 : ((σ : ℂ) + t * I).im = t := by simp
  have ht : |t| ≤ ‖(σ : ℂ) + t * I‖ := by
    have h3 := Complex.abs_im_le_norm ((σ : ℂ) + t * I)
    rwa [him2] at h3
  have h0 := norm_nonneg ((σ : ℂ) + t * I)
  have ht2 : t ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 := by
    rw [← sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hq1 : 1 + t ^ 2 ≤ (1 + ‖(σ : ℂ) + t * I‖) ^ 2 := by
    have e : (1 + ‖(σ : ℂ) + t * I‖) ^ 2 =
        1 + 2 * ‖(σ : ℂ) + t * I‖ + ‖(σ : ℂ) + t * I‖ ^ 2 := by ring
    rw [e]
    linarith
  have hq : (1 + t ^ 2) ^ 2 ≤ (1 + ‖I * ((σ : ℂ) + t * I)‖) ^ 4 := by
    rw [hn]
    calc (1 + t ^ 2) ^ 2 ≤ ((1 + ‖(σ : ℂ) + t * I‖) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hq1 2
      _ = (1 + ‖(σ : ℂ) + t * I‖) ^ 4 := by ring
  unfold laplaceTest
  exact h.trans (div_le_div_of_nonneg_left hC0 (by positivity) hq)

/-- On a vertical line the transform is the Fourier transform of the damped test. -/
theorem fourier_dampedTest (ψ : ℝ → ℂ) (σ ξ : ℝ) :
    𝓕 (fun u : ℝ => ψ u * Complex.exp (-((σ : ℂ) * u))) ξ =
      laplaceTest ψ ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul, laplaceTest_eq_integral]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  show Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * I) •
      (ψ v * Complex.exp (-((σ : ℂ) * v))) =
    ψ v * Complex.exp (-(((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) * v))
  have hx : ((-2 * Real.pi * v * ξ : ℝ) : ℂ) * I + -((σ : ℂ) * v) =
      -(((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) * v) := by
    push_cast
    ring
  rw [smul_eq_mul, mul_left_comm, ← Complex.exp_add, hx]

theorem integrable_fourier_dampedTest {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (σ : ℝ) :
    Integrable (𝓕 (fun u : ℝ => ψ u * Complex.exp (-((σ : ℂ) * u)))) := by
  obtain ⟨D, hD0, hD⟩ := exists_laplaceTest_decay hψ hs σ σ
  have hfun : 𝓕 (fun u : ℝ => ψ u * Complex.exp (-((σ : ℂ) * u))) = fun ξ : ℝ =>
      laplaceTest ψ ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) :=
    funext fun ξ => fourier_dampedTest ψ σ ξ
  rw [hfun]
  have hmaj : Integrable fun ξ : ℝ => D * (1 + ξ ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul _
  have hl : Continuous fun ξ : ℝ => (σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I := by fun_prop
  refine hmaj.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact ((differentiable_laplaceTest hψ.continuous hs).continuous.comp hl).aestronglyMeasurable
  · show ‖laplaceTest ψ ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ≤ D * (1 + ξ ^ 2)⁻¹
    refine (hD σ (2 * Real.pi * ξ) le_rfl le_rfl).trans ?_
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hD0
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by
      have := Real.pi_gt_three
      linarith
    have hpi2 : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := one_le_pow₀ hpi
    have hx : ξ ^ 2 ≤ (2 * Real.pi * ξ) ^ 2 := by
      rw [mul_pow]
      have := mul_le_mul_of_nonneg_right hpi2 (sq_nonneg ξ)
      linarith
    have hq : 1 + ξ ^ 2 ≤ (1 + (2 * Real.pi * ξ) ^ 2) ^ 2 := by
      nlinarith [hx, sq_nonneg ((2 * Real.pi * ξ) ^ 2), sq_nonneg (2 * Real.pi * ξ)]
    exact inv_anti₀ (by positivity) hq

/-- **Inversion on a vertical line.** `∫ ψ̂(σ + it) e^{(σ + it)x} dt = 2π ψ(x)` for every `σ`. -/
theorem integral_laplaceTest_mul_cexp {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (σ x : ℝ) :
    ∫ t : ℝ, laplaceTest ψ (σ + t * I) * Complex.exp (((σ : ℂ) + t * I) * x) =
      2 * Real.pi * ψ x := by
  have hcont : Continuous fun u : ℝ => ψ u * Complex.exp (-((σ : ℂ) * u)) :=
    hψ.continuous.mul (by fun_prop)
  have hcs : HasCompactSupport fun u : ℝ => ψ u * Complex.exp (-((σ : ℂ) * u)) := hs.mul_right
  have hint : Integrable fun u : ℝ => ψ u * Complex.exp (-((σ : ℂ) * u)) :=
    hcont.integrable_of_hasCompactSupport hcs
  have hinv := integral_exp_mul_fourier_rescale hcont hint
    (integrable_fourier_dampedTest hψ hs σ) (-x)
  have hpt : ∀ t : ℝ, laplaceTest ψ (σ + t * I) * Complex.exp (((σ : ℂ) + t * I) * x) =
      Complex.exp ((σ : ℂ) * x) * (Complex.exp (-(t : ℂ) * ((-x : ℝ) : ℂ) * I) *
        𝓕 (fun u : ℝ => ψ u * Complex.exp (-((σ : ℂ) * u))) (t / (2 * Real.pi))) := by
    intro t
    have h2 : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
    have hexp : ((σ : ℂ) + t * I) * x = (σ : ℂ) * x + -(t : ℂ) * ((-x : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [fourier_dampedTest, h2, hexp, Complex.exp_add]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, hinv, neg_neg]
  have he : Complex.exp ((σ : ℂ) * x) * Complex.exp (-((σ : ℂ) * x)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * ψ x) * he

/-! ### A line integral of a Laplace integral -/

/-- **Parseval on a vertical line.** Let `H` be continuous with `|H(σ + it)| ≤ D/(1 + t²)` and
`∫ H(σ + it) e^{(σ + it)x} dt = 2π G(x)` for every `x`. If `e^{σx} |φ(x)|` is integrable for `μ`, then
`∫ H(p) (∫ e^{px} φ(x) dμ) dt = 2π ∫ G(x) φ(x) dμ` along `p = σ + it`. -/
theorem integral_line_mul_laplace_of_inversion {H : ℂ → ℂ} (hH : Continuous H) {σ D : ℝ}
    (hD : ∀ t : ℝ, ‖H (σ + t * I)‖ ≤ D / (1 + t ^ 2)) {G : ℝ → ℂ}
    (hinv : ∀ x : ℝ, ∫ t : ℝ, H (σ + t * I) * Complex.exp (((σ : ℂ) + t * I) * x) =
      2 * Real.pi * G x)
    {μ : Measure ℝ} [SFinite μ] {φ : ℝ → ℂ} (hφm : AEStronglyMeasurable φ μ)
    (hφ : Integrable (fun x => Real.exp (σ * x) * ‖φ x‖) μ) :
    ∫ t : ℝ, H (σ + t * I) * ∫ x : ℝ, Complex.exp (((σ : ℂ) + t * I) * x) * φ x ∂μ =
      2 * Real.pi * ∫ x : ℝ, G x * φ x ∂μ := by
  have hG : Integrable (Function.uncurry fun (t x : ℝ) =>
      H (σ + t * I) * (Complex.exp (((σ : ℂ) + t * I) * x) * φ x))
      ((volume : Measure ℝ).prod μ) := by
    have hg1 : Integrable (fun t : ℝ => D * (1 + t ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul _
    have hmaj := hg1.mul_prod hφ
    refine hmaj.mono' ?_ (Eventually.of_forall fun z => ?_)
    · have hK : Continuous fun z : ℝ × ℝ =>
          H (σ + z.1 * I) * Complex.exp (((σ : ℂ) + z.1 * I) * z.2) :=
        (hH.comp (by fun_prop : Continuous fun z : ℝ × ℝ => (σ : ℂ) + z.1 * I)).mul (by fun_prop)
      have hm := (hK.aestronglyMeasurable (μ := (volume : Measure ℝ).prod μ)).mul hφm.comp_snd
      refine hm.congr (Eventually.of_forall fun z => ?_)
      show H (σ + z.1 * I) * Complex.exp (((σ : ℂ) + z.1 * I) * z.2) * φ z.2 =
        H (σ + z.1 * I) * (Complex.exp (((σ : ℂ) + z.1 * I) * z.2) * φ z.2)
      ring
    · show ‖H (σ + z.1 * I) * (Complex.exp (((σ : ℂ) + z.1 * I) * z.2) * φ z.2)‖ ≤
        D * (1 + z.1 ^ 2)⁻¹ * (Real.exp (σ * z.2) * ‖φ z.2‖)
      have hre : (((σ : ℂ) + z.1 * I) * z.2).re = σ * z.2 := by simp
      rw [norm_mul, norm_mul, Complex.norm_exp, hre, ← div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hD z.1)
        (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  calc ∫ t : ℝ, H (σ + t * I) * ∫ x : ℝ, Complex.exp (((σ : ℂ) + t * I) * x) * φ x ∂μ
      = ∫ t : ℝ, ∫ x : ℝ, H (σ + t * I) *
          (Complex.exp (((σ : ℂ) + t * I) * x) * φ x) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ x : ℝ, (∫ t : ℝ, H (σ + t * I) *
          (Complex.exp (((σ : ℂ) + t * I) * x) * φ x)) ∂μ := integral_integral_swap hG
    _ = ∫ x : ℝ, 2 * Real.pi * G x * φ x ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show (∫ t : ℝ, H (σ + t * I) * (Complex.exp (((σ : ℂ) + t * I) * x) * φ x)) =
          2 * Real.pi * G x * φ x
        rw [← hinv x, ← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        show H (σ + t * I) * (Complex.exp (((σ : ℂ) + t * I) * x) * φ x) =
          H (σ + t * I) * Complex.exp (((σ : ℂ) + t * I) * x) * φ x
        ring
    _ = 2 * Real.pi * ∫ x : ℝ, G x * φ x ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show 2 * Real.pi * G x * φ x = 2 * Real.pi * (G x * φ x)
        ring

/-- The line integral of the transform of a smooth test against a Laplace integral. -/
theorem integral_laplaceTest_mul_laplace {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (σ : ℝ) {μ : Measure ℝ} [SFinite μ] {φ : ℝ → ℂ}
    (hφm : AEStronglyMeasurable φ μ) (hφ : Integrable (fun x => Real.exp (σ * x) * ‖φ x‖) μ) :
    ∫ t : ℝ, laplaceTest ψ (σ + t * I) * ∫ x : ℝ, Complex.exp (((σ : ℂ) + t * I) * x) * φ x ∂μ =
      2 * Real.pi * ∫ x : ℝ, ψ x * φ x ∂μ := by
  obtain ⟨D, hD0, hD⟩ := exists_laplaceTest_decay hψ hs σ σ
  refine integral_line_mul_laplace_of_inversion
    (differentiable_laplaceTest hψ.continuous hs).continuous (D := D) (fun t => ?_)
    (integral_laplaceTest_mul_cexp hψ hs σ) hφm hφ
  refine (hD σ t le_rfl le_rfl).trans (div_le_div_of_nonneg_left hD0 (by positivity) ?_)
  nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) (sq_nonneg t)]

theorem laplaceTest_eq_laplace_neg (ψ : ℝ → ℂ) (p : ℂ) :
    laplaceTest ψ p = negativeHalfLineLaplace ψ (-p) := by
  rw [laplaceTest_eq_integral]
  unfold negativeHalfLineLaplace
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show ψ u * Complex.exp (-(p * u)) = Complex.exp (-p * (u : ℂ)) * ψ u
  rw [neg_mul, mul_comm]

/-! ### The two pairings -/

/-- The pairing of a test with the state in the weight of the confinement,
`∫ ψ(u) e^{−8u} F(u) du`. -/
def statePairing (F : ℝ → ℝ) (ψ : ℝ → ℂ) : ℂ :=
  ∫ u : ℝ, ψ u * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ)

/-- The pairing of a test with the profile beyond the wall, `∫_{x>0} ψ(x) F⁺(x) dx`. -/
def beyondWallPairing (W₀ : ℝ) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (ψ : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ in Ioi (0 : ℝ), ψ x * beyondWallProfile W₀ hF x

/-- Against a real test the pairing with the state is the confinement pairing. -/
theorem statePairing_cx {F : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0) (G : ℝ → ℝ) :
    statePairing F (cx G) =
      ((∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8 * u)) : ℝ) : ℂ) := by
  have h1 : (∫ u : ℝ, ((F u * G u * Real.exp (-(8 * u)) : ℝ) : ℂ)) =
      ((∫ u : ℝ, F u * G u * Real.exp (-(8 * u)) : ℝ) : ℂ) := integral_ofReal
  have h2 : (∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8 * u))) =
      ∫ u : ℝ, F u * G u * Real.exp (-(8 * u)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      have hu' : 0 ≤ u := not_lt.mp fun h => hu (mem_Iio.mpr h)
      rw [hF u hu', zero_mul, zero_mul]
  rw [h2, ← h1]
  unfold statePairing
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show ((G u : ℝ) : ℂ) * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ) =
    ((F u * G u * Real.exp (-(8 * u)) : ℝ) : ℂ)
  push_cast
  ring

/-- Right of `Re p = 4` the line integral of `ψ̂` against the shifted transform is the pairing with
the state. -/
theorem integral_laplaceTest_mul_laplace_right {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ) {b : ℝ} (hb : 4 < b) :
    ∫ t : ℝ, laplaceTest ψ (b + t * I) * negativeHalfLineLaplace (cx F) (b + t * I - 8) =
      2 * Real.pi * statePairing F ψ := by
  have h := integral_laplaceTest_mul_laplace hψ hs b (μ := volume)
    (aestronglyMeasurable_dampedState hF) (integrable_exp_mul_dampedState hF hb)
  unfold statePairing
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show laplaceTest ψ (b + t * I) * negativeHalfLineLaplace (cx F) (b + t * I - 8) =
    laplaceTest ψ (b + t * I) *
      ∫ u : ℝ, Complex.exp (((b : ℂ) + t * I) * u) * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ)
  rw [laplace_sub_eight_eq_integral F b t]

/-- Left of `Re p = −1` the line integral of `ψ̂` against the continuation is the pairing with the
profile beyond the wall. -/
theorem integral_laplaceTest_mul_stateMeromorphic_left {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) {a : ℝ} (ha : a < -1) :
    ∫ t : ℝ, laplaceTest ψ (a + t * I) * stateMeromorphic W₀ F (a + t * I - 8) =
      2 * Real.pi * beyondWallPairing W₀ hF ψ := by
  have h := integral_laplaceTest_mul_laplace hψ hs a (μ := volume.restrict (Ioi (0 : ℝ)))
    (φ := beyondWallProfile W₀ hF) (aestronglyMeasurable_beyondWallProfile W₀ hF)
    (integrable_exp_mul_beyondWallProfile W₀ hF ha)
  unfold beyondWallPairing
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show laplaceTest ψ (a + t * I) * stateMeromorphic W₀ F (a + t * I - 8) =
    laplaceTest ψ (a + t * I) *
      ∫ x : ℝ in Ioi (0 : ℝ), Complex.exp (((a : ℂ) + t * I) * x) * beyondWallProfile W₀ hF x
  rw [stateMeromorphic_eq_integral_beyondWallProfile hF ha t]

/-! ### The zero series as a distribution -/

/-- **The zero series against a smooth test.** For the critical state and every smooth test `ψ` of
compact support:
`Σ_z L F(z) ψ̂(z) = a (∫_{x>0} ψ(x) F⁺(x) dx − ∫_{u<0} ψ(u) e^{−8u} F(u) du)`. -/
theorem criticalState_hasSum_zeroSeries_test {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) * laplaceTest ψ (centredZero q))
      ((criticalAliasCoefficient W₀ : ℂ) *
        (beyondWallPairing W₀ (criticalHalfLineEnergyDomain_of_groundState hF) ψ -
          statePairing F ψ)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨D, -, hD⟩ := exists_laplaceTest_decay hψ hs (-2) 5
  have h := criticalState_hasSum_zeroValues_two_lines hW hthreshold hF
    (differentiable_laplaceTest hψ.continuous hs) (a := -2) (b := 5) (by norm_num) (by norm_num)
    (fun σ t h1 h2 => hD σ t h1 h2)
  have hR := integral_laplaceTest_mul_laplace_right hd hψ hs (b := 5) (by norm_num)
  have hL := integral_laplaceTest_mul_stateMeromorphic_left (W₀ := W₀) hd hψ hs (a := -2)
    (by norm_num)
  rw [hR, hL] at h
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : (criticalAliasCoefficient W₀ : ℂ) / (2 * Real.pi) * (2 * Real.pi) =
      (criticalAliasCoefficient W₀ : ℂ) := by
    field_simp
  convert h using 1
  linear_combination (statePairing F ψ - beyondWallPairing W₀ hd ψ) * hc

/-- **Left of the wall the zero series is the state.** For a test vanishing on `x > 0`:
`Σ_z L F(z) ψ̂(z) = −a ∫ ψ(u) e^{−8u} F(u) du`. -/
theorem criticalState_hasSum_zeroSeries_test_left {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 < x → ψ x = 0) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) * laplaceTest ψ (centredZero q))
      (-((criticalAliasCoefficient W₀ : ℂ) * statePairing F ψ)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h := criticalState_hasSum_zeroSeries_test hW hthreshold hF hψ hs
  have e : (∫ x : ℝ in Ioi (0 : ℝ), ψ x * beyondWallProfile W₀ hd x) =
      ∫ x : ℝ in Ioi (0 : ℝ), (0 : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      show ψ x * beyondWallProfile W₀ hd x = 0
      rw [hψ0 x hx, zero_mul]
  have h0 : beyondWallPairing W₀ hd ψ = 0 := by
    unfold beyondWallPairing
    rw [e, integral_zero]
  rw [h0, zero_sub, mul_neg] at h
  exact h

/-- **Beyond the wall the zero series is the prime side.** For a test vanishing on `u < 0`:
`Σ_z L F(z) ψ̂(z) = a ∫ ψ(x) F⁺(x) dx`. -/
theorem criticalState_hasSum_zeroSeries_test_right {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (hψ0 : ∀ u, u < 0 → ψ u = 0) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) * laplaceTest ψ (centredZero q))
      ((criticalAliasCoefficient W₀ : ℂ) *
        beyondWallPairing W₀ (criticalHalfLineEnergyDomain_of_groundState hF) ψ) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h := criticalState_hasSum_zeroSeries_test hW hthreshold hF hψ hs
  have e : (fun u : ℝ => ψ u * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ)) = fun _ => 0 := by
    funext u
    rcases lt_or_ge u 0 with hu | hu
    · rw [hψ0 u hu, zero_mul]
    · rw [hd.support u hu, mul_zero, Complex.ofReal_zero, mul_zero]
  have h0 : statePairing F ψ = 0 := by
    unfold statePairing
    rw [e, integral_zero]
  rw [h0, sub_zero] at h
  exact h

/-! ### Weil's form of the state and a test is its zero side -/

/-- **The explicit formula at the state.** For a real smooth test `G` of compact support in
`u < 0`, Weil's bare form of the state and the test is the zero side:
`W(F, G) = Σ_z L F(z) L G(−z)`, the sum over the centred zeros with multiplicity. -/
theorem criticalState_hasSum_bareMixedEnergy {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (hG0 : ∀ u, 0 ≤ u → G u = 0) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q))
      ((bareMixedEnergy F G : ℝ) : ℂ) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hψ : ContDiff ℝ ∞ (cx G) := Complex.ofRealCLM.contDiff.comp hG
  have hs : HasCompactSupport (cx G) := hc.comp_left Complex.ofReal_zero
  have h := criticalState_hasSum_zeroSeries_test_left hW hthreshold hF hψ hs fun x hx => by
    show ((G x : ℝ) : ℂ) = 0
    rw [hG0 x hx.le, Complex.ofReal_zero]
  have hle : (2 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hGd : CriticalHalfLineEnergyDomain G :=
    criticalHalfLineEnergyDomain_of_compact_negative (hG.of_le hle) hc hG0
  -- the weak equation of the state turns the confinement pairing into Weil's form
  have hw := criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hGd
  rw [criticalHalfLineMixedEnergy_eq_bare_add] at hw
  have hb : bareMixedEnergy F G = -(criticalAliasCoefficient W₀ *
      ∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8 * u))) := by linarith
  have hval : -((criticalAliasCoefficient W₀ : ℂ) * statePairing F (cx G)) =
      ((bareMixedEnergy F G : ℝ) : ℂ) := by
    rw [statePairing_cx hd.support G, hb]
    push_cast
    ring
  have hfun : (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q)) = fun q : XiZeroCopy =>
      negativeHalfLineLaplace (cx F) (centredZero q) * laplaceTest (cx G) (centredZero q) :=
    funext fun q => by rw [laplaceTest_eq_laplace_neg]
  rw [hfun, ← hval]
  exact h

end GaloisForLFunctions.ExclusionOfTheCriticalState
