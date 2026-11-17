import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLogarithmicDerivativeOfZetaIsSublogarithmicRightOfTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroCauchyTransformIsSquareIntegrableUpToALogarithm
import GaloisForLFunctions.HTGeometry.PaleyWienerHalfPlane
import GaloisForLFunctions.HTGeometry.HardyBoundary.NegativeHalfLineLaplaceHardy
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.RHTower.MobiusDampingJetsOnTheAdmittedRange
import GaloisForLFunctions.RHTower.MellinLinePolarization

/-!
# The forward prime-minus-pole wave is bounded in mean square

For a profile `F` on the negative half-line the prime form splits by the direction of the shift.
The forward half `Σ Λ(n) n^{-1/2} ∫ G(t) F(t + log n) dt` pairs `G` with `F` further to the right,
where `F` is large, and so does the half `u > v` of the pole term
`∫∫ G(v) e^{-v/2} F(u) e^{u/2} du dv`. Their difference is the pairing of `G` with the forward
prime-minus-pole wave

  `A(v) = Σ Λ(n) n^{-1/2} F(v + log n) - e^{-v/2} ∫_{u > v} F(u) e^{u/2} du`,

whose transform is `-N(1/2 + p) L F(p)`, `N` the regular part of `ζ'/ζ`: the Euler sum and the
pole wave carry the same pole `1/(p - 1/2)`. If every centred zero has `Re z ≤ κ` and
`κ < σ < 1`, then

  `(forward prime form - forward pole form)² ≤
     (1/2π) ∫ |N(1/2 + σ + it)|² |L F(σ + it)|² dt · ∫ G(v)² e^{-2σv} dv`.

Mechanism. `Φ(w) = -N(1/2 + σ + w) L F(σ + w)` lies in the Hardy space of `Re w > 0`: Jensen's
inequality for the Poisson average, applied to `Φ(w)/(1 + εw)` with `ε → 0`, bounds the mass of
every vertical line by the mass of the boundary line. By Paley–Wiener `Φ` is the Laplace
transform of a datum `h ∈ L²(0, ∞)` of mass at most the boundary mass. On the line `Re p = 1`,
where the Euler sum converges absolutely, polarized Plancherel turns each shift of `F`, the pole
wave and the datum into pairings with `G`; the difference of the two forms is
`∫ e^{σx} G(-x) h(x) dx`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology
open scoped FourierTransform Convolution

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Poisson averages preserve the integral -/

theorem halfPlanePoisson_sub_comm (d a b : ℝ) :
    halfPlanePoisson d (a - b) = halfPlanePoisson d (b - a) := by
  unfold halfPlanePoisson
  rw [show (a - b) ^ (2 : ℕ) = (b - a) ^ (2 : ℕ) by ring]

theorem halfPlanePoisson_le_inv {d : ℝ} (hd : 0 < d) (x : ℝ) :
    halfPlanePoisson d x ≤ 1 / (Real.pi * d) := by
  unfold halfPlanePoisson
  have hπ := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hπ.le (sq_nonneg x)]

theorem integrable_halfPlanePoisson_sub_mul {B : ℝ → ℝ} (hB : Integrable B) {d : ℝ} (hd : 0 < d)
    (γ : ℝ) : Integrable fun t : ℝ => halfPlanePoisson d (t - γ) * B t := by
  refine (hB.norm.const_mul (1 / (Real.pi * d))).mono'
    (((continuous_halfPlanePoisson hd).comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable.mul hB.aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Real.norm_of_nonneg (halfPlanePoisson_pos hd _).le]
  exact mul_le_mul_of_nonneg_right (halfPlanePoisson_le_inv hd _) (norm_nonneg _)

/-- The Poisson average of an integrable function is integrable, with the same integral. -/
theorem integrable_integral_halfPlanePoisson_mul {B : ℝ → ℝ} (hB : Integrable B) {d : ℝ}
    (hd : 0 < d) :
    Integrable (fun γ : ℝ => ∫ t : ℝ, halfPlanePoisson d (t - γ) * B t) ∧
      (∫ γ : ℝ, ∫ t : ℝ, halfPlanePoisson d (t - γ) * B t) = ∫ t : ℝ, B t := by
  have hP := integrable_halfPlanePoisson hd
  have e : (fun γ : ℝ => ∫ t : ℝ, halfPlanePoisson d (t - γ) * B t) =
      (B ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] halfPlanePoisson d) := by
    funext γ
    show _ = ∫ t : ℝ, B t * halfPlanePoisson d (γ - t)
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show halfPlanePoisson d (t - γ) * B t = B t * halfPlanePoisson d (γ - t)
    rw [halfPlanePoisson_sub_comm, mul_comm]
  rw [e]
  refine ⟨hB.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hP, ?_⟩
  rw [MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hB hP,
    integral_halfPlanePoisson hd]
  show (∫ x : ℝ, B x) * 1 = _
  rw [mul_one]

/-! ### The transform of the wave lies in the Hardy space -/

/-- The transform of the forward prime-minus-pole wave of a datum on the ray:
`-N(1/2 + p) L f(p)`. -/
def primeWaveTransform (f : ℝ → ℂ) (p : ℂ) : ℂ :=
  -(zetaRegularLogDeriv (1 / 2 + p) * laplaceRay f p)

/-- The transform of the wave, recentred at the line `Re p = σ`. -/
def primeWaveHardy (f : ℝ → ℂ) (σ : ℝ) (w : ℂ) : ℂ := primeWaveTransform f ((σ : ℂ) + w)

theorem differentiableAt_primeWaveTransform {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) {p : ℂ} (hp : κ < p.re) :
    DifferentiableAt ℂ (primeWaveTransform f) p := by
  have h1 := differentiableAt_zetaRegularLogDeriv_half_add hκ hzero hp
  have h2 : DifferentiableAt ℂ (laplaceRay f) p :=
    (differentiableOn_laplaceRay hf).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hκ.trans_lt hp))
  exact (h1.mul h2).neg

theorem re_one_add_mul_sub (ε σ : ℝ) (p : ℂ) :
    (1 + (ε : ℂ) * (p - (σ : ℂ))).re = 1 + ε * (p.re - σ) := by simp

theorem im_one_add_mul_sub (ε σ : ℝ) (p : ℂ) :
    (1 + (ε : ℂ) * (p - (σ : ℂ))).im = ε * p.im := by simp

/-- The regulator `1/(1 + ε (p - σ))` absorbs the logarithmic growth of `N`: the regulated
transform is bounded on `Re p ≥ σ`. -/
theorem exists_norm_primeWaveTransform_mul_inv_le {κ σ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hσ : κ < σ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ p : ℂ, σ ≤ p.re →
      ‖primeWaveTransform f p * (1 + (ε : ℂ) * (p - (σ : ℂ)))⁻¹‖ ≤ M := by
  obtain ⟨C, hC, hN⟩ := exists_norm_zetaRegularLogDeriv_half_add_le_log hκ hzero hσ
  have hσ0 : 0 < σ := hκ.trans_lt hσ
  refine ⟨C * (3 + 1 / ε) * (rayL2Norm f / Real.sqrt (2 * σ)), fun p hp => ?_⟩
  have hq1 : 1 ≤ ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖ := by
    have h := Complex.re_le_norm (1 + (ε : ℂ) * (p - (σ : ℂ)))
    rw [re_one_add_mul_sub] at h
    linarith [mul_nonneg hε.le (sub_nonneg.mpr hp)]
  have hq2 : ε * |p.im| ≤ ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖ := by
    have h := Complex.abs_im_le_norm (1 + (ε : ℂ) * (p - (σ : ℂ)))
    rwa [im_one_add_mul_sub, abs_mul, abs_of_pos hε] at h
  have hq0 : 0 < ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖ := by linarith
  have hlog : Real.log (|p.im| + 4) ≤ (3 + 1 / ε) * ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖ := by
    have h1 : Real.log (|p.im| + 4) ≤ |p.im| + 3 := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < |p.im| + 4)
      linarith
    have h2 : |p.im| ≤ ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖ / ε := by
      rw [le_div_iff₀ hε]
      linarith
    have h3 : (3 + 1 / ε) * ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖ =
        3 * ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖ + ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖ / ε := by ring
    linarith
  have hL : ‖laplaceRay f p‖ ≤ rayL2Norm f / Real.sqrt (2 * σ) := by
    refine (norm_laplaceRay_le hf (hσ0.trans_le hp)).trans ?_
    exact div_le_div_of_nonneg_left (rayL2Norm_nonneg f) (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_le_sqrt (by linarith))
  have h1 : ‖zetaRegularLogDeriv (1 / 2 + p)‖ ≤
      C * ((3 + 1 / ε) * ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖) :=
    (hN p hp).trans (mul_le_mul_of_nonneg_left hlog hC)
  have hCq : 0 ≤ C * ((3 + 1 / ε) * ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖) :=
    mul_nonneg hC (mul_nonneg (by positivity) hq0.le)
  unfold primeWaveTransform
  rw [norm_mul, norm_neg, norm_mul, norm_inv]
  calc ‖zetaRegularLogDeriv (1 / 2 + p)‖ * ‖laplaceRay f p‖ * ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖⁻¹
      ≤ C * ((3 + 1 / ε) * ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖) * (rayL2Norm f / Real.sqrt (2 * σ)) *
          ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 hL (norm_nonneg _) hCq) (inv_nonneg.mpr hq0.le)
    _ = C * (3 + 1 / ε) * (rayL2Norm f / Real.sqrt (2 * σ)) *
          (‖1 + (ε : ℂ) * (p - (σ : ℂ))‖ * ‖1 + (ε : ℂ) * (p - (σ : ℂ))‖⁻¹) := by ring
    _ = C * (3 + 1 / ε) * (rayL2Norm f / Real.sqrt (2 * σ)) := by
        rw [mul_inv_cancel₀ hq0.ne', mul_one]

/-- **Poisson majorization from the boundary line.** Inside the half-plane `Re p > σ` the square
of the transform is at most the Poisson average of its square on `Re p = σ`. -/
theorem norm_sq_primeWaveTransform_le_integral_halfPlanePoisson {κ σ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hσ : κ < σ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))))
    (hB : Integrable fun t : ℝ => ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) {d : ℝ}
    (hd : 0 < d) (γ : ℝ) :
    ‖primeWaveTransform f ((σ : ℂ) + (d : ℂ) + (γ : ℂ) * I)‖ ^ 2 ≤
      ∫ t : ℝ, halfPlanePoisson d (t - γ) * ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hP0 : ∀ t : ℝ, 0 ≤ halfPlanePoisson d (t - γ) := fun t => (halfPlanePoisson_pos hd _).le
  have hPB : Integrable fun t : ℝ => halfPlanePoisson d (t - γ) *
      ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    integrable_halfPlanePoisson_sub_mul hB hd γ
  have key : ∀ ε : ℝ, 0 < ε → ‖primeWaveTransform f ((σ : ℂ) + (d : ℂ) + (γ : ℂ) * I)‖ ^ 2 ≤
      ((1 + ε * d) ^ 2 + (ε * γ) ^ 2) * ∫ t : ℝ, halfPlanePoisson d (t - γ) *
        ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro ε hε
    obtain ⟨M, hM⟩ := exists_norm_primeWaveTransform_mul_inv_le hκ hzero hσ hf hε
    have hne : ∀ p : ℂ, σ ≤ p.re → 1 + (ε : ℂ) * (p - (σ : ℂ)) ≠ 0 := fun p hp h => by
      have h1 := congrArg Complex.re h
      rw [re_one_add_mul_sub, Complex.zero_re] at h1
      linarith [mul_nonneg hε.le (sub_nonneg.mpr hp)]
    have hdiff : ∀ p : ℂ, σ ≤ p.re → DifferentiableAt ℂ
        (fun p : ℂ => primeWaveTransform f p * (1 + (ε : ℂ) * (p - (σ : ℂ)))⁻¹) p := fun p hp =>
      (differentiableAt_primeWaveTransform hκ hzero hf (hσ.trans_le hp)).mul
        ((by fun_prop : DifferentiableAt ℂ (fun p : ℂ => 1 + (ε : ℂ) * (p - (σ : ℂ))) p).inv
          (hne p hp))
    have hJen := norm_sq_apply_le_integral_halfPlanePoisson hdiff hM hd γ
    beta_reduce at hJen
    have hQ : ‖1 + (ε : ℂ) * ((σ : ℂ) + (d : ℂ) + (γ : ℂ) * I - (σ : ℂ))‖ ^ 2 =
        (1 + ε * d) ^ 2 + (ε * γ) ^ 2 := by
      have e1 : ((σ : ℂ) + (d : ℂ) + (γ : ℂ) * I).re = σ + d := by simp
      have e2 : ((σ : ℂ) + (d : ℂ) + (γ : ℂ) * I).im = γ := by simp
      rw [Complex.sq_norm, Complex.normSq_apply, re_one_add_mul_sub, im_one_add_mul_sub, e1, e2]
      ring
    have hQpos : 0 < (1 + ε * d) ^ 2 + (ε * γ) ^ 2 := by positivity
    rw [norm_mul, norm_inv, mul_pow, inv_pow, hQ] at hJen
    have hR : (∫ t : ℝ, halfPlanePoisson d (t - γ) *
        ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I) *
          (1 + (ε : ℂ) * ((σ : ℂ) + (t : ℂ) * I - (σ : ℂ)))⁻¹‖ ^ 2) ≤
        ∫ t : ℝ, halfPlanePoisson d (t - γ) *
          ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
      refine integral_mono_of_nonneg
        (Eventually.of_forall fun t => mul_nonneg (hP0 t) (sq_nonneg _)) hPB
        (Eventually.of_forall fun t => mul_le_mul_of_nonneg_left ?_ (hP0 t))
      rw [norm_mul, mul_pow]
      have h1 : ‖(1 + (ε : ℂ) * ((σ : ℂ) + (t : ℂ) * I - (σ : ℂ)))⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        refine inv_le_one_of_one_le₀ ?_
        have h := Complex.re_le_norm (1 + (ε : ℂ) * ((σ : ℂ) + (t : ℂ) * I - (σ : ℂ)))
        have e1 : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
        rw [re_one_add_mul_sub, e1, sub_self, mul_zero, add_zero] at h
        exact h
      exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) h1)
    have h4 := hJen.trans hR
    rw [← div_eq_mul_inv, div_le_iff₀ hQpos] at h4
    exact h4.trans (le_of_eq (mul_comm _ _))
  generalize (∫ t : ℝ, halfPlanePoisson d (t - γ) *
    ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) = J at key ⊢
  -- let the regulator tend to one
  have hc : Continuous fun ε : ℝ => ((1 + ε * d) ^ 2 + (ε * γ) ^ 2) * J := by fun_prop
  have hlim : Tendsto (fun ε : ℝ => ((1 + ε * d) ^ 2 + (ε * γ) ^ 2) * J) (𝓝[>] 0)
      (𝓝 (((1 + (0 : ℝ) * d) ^ 2 + ((0 : ℝ) * γ) ^ 2) * J)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have e : ((1 + (0 : ℝ) * d) ^ 2 + ((0 : ℝ) * γ) ^ 2) * J = J := by ring
  rw [e] at hlim
  exact ge_of_tendsto hlim (eventually_mem_nhdsWithin.mono fun ε hε => key ε hε)

theorem continuous_primeWaveHardy_line {κ σ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hσ : κ < σ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) {d : ℝ} (hd : 0 < d) :
    Continuous fun ξ : ℝ => primeWaveHardy f σ (rayLine d ξ) := by
  refine continuous_iff_continuousAt.mpr fun ξ => ?_
  have h1 : DifferentiableAt ℂ (primeWaveTransform f) ((σ : ℂ) + rayLine d ξ) :=
    differentiableAt_primeWaveTransform hκ hzero hf (by
      rw [Complex.add_re, Complex.ofReal_re, rayLine_re]
      linarith)
  have h2 : ContinuousAt (fun ξ : ℝ => (σ : ℂ) + rayLine d ξ) ξ := by
    unfold rayLine
    fun_prop
  exact ContinuousAt.comp (g := primeWaveTransform f) h1.continuousAt h2

/-- **The transform of the wave is a Hardy function.** If its boundary values on `Re p = σ`,
a line to the right of the zeros, are square-integrable, then `w ↦ -N(1/2 + σ + w) L f(σ + w)`
lies in the Hardy space of the right half-plane, with the boundary mass as bound. -/
theorem isHalfPlaneHardy_primeWaveHardy {κ σ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hσ : κ < σ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))))
    (hB : Integrable fun t : ℝ => ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :
    IsHalfPlaneHardy (primeWaveHardy f σ)
      ((2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  have hline : ∀ d : ℝ, 0 < d →
      Integrable (fun ξ : ℝ => ‖primeWaveHardy f σ (rayLine d ξ)‖ ^ 2) ∧
        (∫ ξ : ℝ, ‖primeWaveHardy f σ (rayLine d ξ)‖ ^ 2) ≤
          (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro d hd
    obtain ⟨hJi, hJe⟩ := integrable_integral_halfPlanePoisson_mul hB hd
    have hJe' : (∫ γ : ℝ, ∫ t : ℝ, halfPlanePoisson d (t - γ) *
        ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) =
        ∫ t : ℝ, ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := hJe
    have hJξ : Integrable fun ξ : ℝ => ∫ t : ℝ, halfPlanePoisson d (t - 2 * Real.pi * ξ) *
        ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := hJi.comp_mul_left' h2π
    have hle : ∀ ξ : ℝ, ‖primeWaveHardy f σ (rayLine d ξ)‖ ^ 2 ≤ ∫ t : ℝ,
        halfPlanePoisson d (t - 2 * Real.pi * ξ) *
          ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
      intro ξ
      have e : (σ : ℂ) + rayLine d ξ =
          (σ : ℂ) + (d : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I := by
        unfold rayLine
        ring
      show ‖primeWaveTransform f ((σ : ℂ) + rayLine d ξ)‖ ^ 2 ≤ _
      rw [e]
      exact norm_sq_primeWaveTransform_le_integral_halfPlanePoisson hκ hzero hσ hf hB hd
        (2 * Real.pi * ξ)
    have hcont := continuous_primeWaveHardy_line hκ hzero hσ hf hd
    have hint : Integrable fun ξ : ℝ => ‖primeWaveHardy f σ (rayLine d ξ)‖ ^ 2 :=
      hJξ.mono' (hcont.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun ξ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hle ξ)
    refine ⟨hint, ?_⟩
    calc (∫ ξ : ℝ, ‖primeWaveHardy f σ (rayLine d ξ)‖ ^ 2)
        ≤ ∫ ξ : ℝ, ∫ t : ℝ, halfPlanePoisson d (t - 2 * Real.pi * ξ) *
            ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := integral_mono hint hJξ hle
      _ = |(2 * Real.pi)⁻¹| • ∫ γ : ℝ, ∫ t : ℝ, halfPlanePoisson d (t - γ) *
            ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
          MeasureTheory.Measure.integral_comp_mul_left (fun γ : ℝ => ∫ t : ℝ,
            halfPlanePoisson d (t - γ) * ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
            (2 * Real.pi)
      _ = (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖primeWaveTransform f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
          rw [hJe', abs_of_pos (by positivity), smul_eq_mul]
  refine ⟨fun w hw => ?_, fun d hd => ?_, fun d hd => (hline d hd).2⟩
  · have h1 : DifferentiableAt ℂ (primeWaveTransform f) ((σ : ℂ) + w) :=
      differentiableAt_primeWaveTransform hκ hzero hf (by
        rw [Complex.add_re, Complex.ofReal_re]
        have : 0 < w.re := hw
        linarith)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (σ : ℂ) + w) w := by fun_prop
    exact (DifferentiableAt.comp (g := primeWaveTransform f) w h1 h2).differentiableWithinAt
  · exact (memLp_two_iff_integrable_sq_norm
      (continuous_primeWaveHardy_line hκ hzero hσ hf hd).aestronglyMeasurable).mpr (hline d hd).1

/-! ### Shifts and the pole wave on the ray -/

theorem expRay_ofReal (r x : ℝ) : expRay ((r : ℝ) : ℂ) x = ((Real.exp (-(r * x)) : ℝ) : ℂ) := by
  unfold expRay
  rw [← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_exp]

theorem laplaceRay_eq_integral_of_support {φ : ℝ → ℂ} (h0 : ∀ x : ℝ, x ≤ 0 → φ x = 0) (w : ℂ) :
    laplaceRay φ w = ∫ x : ℝ, φ x * expRay w x := by
  unfold laplaceRay
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  rw [h0 x (not_lt.mp hx), zero_mul]

/-- A shift of the datum multiplies its transform by `e^{-wℓ}`. -/
theorem laplaceRay_translate {φ : ℝ → ℂ} (h0 : ∀ x : ℝ, x ≤ 0 → φ x = 0) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (w : ℂ) : laplaceRay (fun x : ℝ => φ (x - ℓ)) w = expRay w ℓ * laplaceRay φ w := by
  rw [laplaceRay_eq_integral_of_support (fun x hx => h0 _ (by linarith)),
    laplaceRay_eq_integral_of_support h0, ← integral_const_mul,
    ← integral_sub_right_eq_self (fun y : ℝ => expRay w ℓ * (φ y * expRay w y)) ℓ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show φ (x - ℓ) * expRay w x = expRay w ℓ * (φ (x - ℓ) * expRay w (x - ℓ))
  have e : expRay w x = expRay w ℓ * expRay w (x - ℓ) := by
    unfold expRay
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  ring

theorem memLp_translate_restrict {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume : Measure ℝ)) (ℓ : ℝ) :
    MemLp (fun x : ℝ => φ (x - ℓ)) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (hφ.comp_measurePreserving (measurePreserving_sub_right volume ℓ)).restrict _

/-- The pole wave on the ray: `w(x) = ∫_0^x e^{(x - y)/2} f(y) dy`. -/
def poleWaveRay (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (x / 2) * ∫ y in (0 : ℝ)..x, Real.exp (-(y / 2)) * f y

theorem integrable_exp_neg_half_mul {f : ℝ → ℝ} (hfm : Measurable f) (hf1 : Integrable f)
    (hf0 : ∀ x : ℝ, x ≤ 0 → f x = 0) : Integrable fun y : ℝ => Real.exp (-(y / 2)) * f y := by
  refine hf1.norm.mono'
    ((Real.measurable_exp.comp (measurable_id.div_const 2).neg).mul hfm).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rcases le_or_gt y 0 with hy | hy
  · simp [hf0 y hy]
  · rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))

theorem continuous_poleWaveRay {f : ℝ → ℝ}
    (hφi : Integrable fun y : ℝ => Real.exp (-(y / 2)) * f y) : Continuous (poleWaveRay f) := by
  show Continuous fun x : ℝ => Real.exp (x / 2) * ∫ y in (0 : ℝ)..x, Real.exp (-(y / 2)) * f y
  exact (Real.continuous_exp.comp (continuous_id.div_const 2)).mul
    (intervalIntegral.continuous_primitive (fun a b => hφi.intervalIntegrable) 0)

theorem abs_poleWaveRay_le {f : ℝ → ℝ}
    (hφi : Integrable fun y : ℝ => Real.exp (-(y / 2)) * f y) {x : ℝ} (hx : 0 ≤ x) :
    |poleWaveRay f x| ≤ Real.exp (x / 2) * ∫ y : ℝ, ‖Real.exp (-(y / 2)) * f y‖ := by
  unfold poleWaveRay
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have h1 := intervalIntegral.norm_integral_le_integral_norm
    (f := fun y : ℝ => Real.exp (-(y / 2)) * f y) (μ := volume) hx
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  rw [intervalIntegral.integral_of_le hx]
  exact setIntegral_le_integral hφi.norm (Eventually.of_forall fun y => norm_nonneg _)

/-- The pole wave carries the pole of the Euler sum: its transform is `L f(p)/(p - 1/2)`. -/
theorem laplaceRay_poleWaveRay {f : ℝ → ℝ} (hfm : Measurable f) (hf1 : Integrable f)
    (hf0 : ∀ x : ℝ, x ≤ 0 → f x = 0) {p : ℂ} (hp : 1 / 2 < p.re) :
    laplaceRay (cx (poleWaveRay f)) p = (p - 1 / 2)⁻¹ * laplaceRay (cx f) p := by
  have hφm : Measurable fun y : ℝ => Real.exp (-(y / 2)) * f y :=
    (Real.measurable_exp.comp (measurable_id.div_const 2).neg).mul hfm
  have hφi := integrable_exp_neg_half_mul hfm hf1 hf0
  have hz : 0 < (p - 1 / 2).re := by
    rw [Complex.sub_re, re_one_half]
    linarith
  have hV := integral_Ioi_expVolterra_laplace_of_integrable (b := 0) le_rfl hz hφm
    hφi.integrableOn
  have e1 : (∫ x in Ioi (0 : ℝ), cx (poleWaveRay f) x * expRay p x) =
      ∫ t in Ioi (0 : ℝ), cexp (-((p - 1 / 2) * (t : ℂ))) *
        ((∫ h in Ioc (0 : ℝ) t, Real.exp (-(0 * (t - h))) * (Real.exp (-(h / 2)) * f h) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := (mem_Ioi.mp ht).le
    have e : (∫ h in Ioc (0 : ℝ) t, Real.exp (-(0 * (t - h))) * (Real.exp (-(h / 2)) * f h)) =
        ∫ y in (0 : ℝ)..t, Real.exp (-(y / 2)) * f y := by
      rw [intervalIntegral.integral_of_le ht0]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      simp
    show ((poleWaveRay f t : ℝ) : ℂ) * expRay p t = _
    rw [e]
    unfold poleWaveRay expRay
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    have e2 : cexp (-((p - 1 / 2) * (t : ℂ))) = cexp (((t / 2 : ℝ) : ℂ)) * cexp (-(p * (t : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e2]
    ring
  have e2 : (∫ h in Ioi (0 : ℝ), cexp (-((p - 1 / 2) * (h : ℂ))) *
        ((Real.exp (-(h / 2)) * f h : ℝ) : ℂ)) = ∫ x in Ioi (0 : ℝ), cx f x * expRay p x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
    show cexp (-((p - 1 / 2) * (h : ℂ))) * ((Real.exp (-(h / 2)) * f h : ℝ) : ℂ) =
      ((f h : ℝ) : ℂ) * expRay p h
    unfold expRay
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    have e3 : cexp (-((p - 1 / 2) * (h : ℂ))) * cexp (((-(h / 2) : ℝ) : ℂ)) =
        cexp (-(p * (h : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← e3]
    ring
  unfold laplaceRay
  rw [e1]
  refine hV.trans ?_
  rw [e2]
  simp

/-- The damped pole wave is integrable and square-integrable: it grows at most like `e^{x/2}`. -/
theorem integrable_and_memLp_rayDamp_poleWaveRay {f : ℝ → ℝ}
    (hφi : Integrable fun y : ℝ => Real.exp (-(y / 2)) * f y) :
    Integrable (rayDamp (cx (poleWaveRay f)) 1) ∧
      MemLp (rayDamp (cx (poleWaveRay f)) 1) 2 volume := by
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ∫ y : ℝ, ‖Real.exp (-(y / 2)) * f y‖ := ⟨_, rfl⟩
  have hcont : Continuous fun x : ℝ => cx (poleWaveRay f) x * expRay ((1 : ℝ) : ℂ) x :=
    (Complex.continuous_ofReal.comp (continuous_poleWaveRay hφi)).mul (continuous_expRay _)
  have hm : AEStronglyMeasurable (rayDamp (cx (poleWaveRay f)) 1) volume :=
    hcont.aestronglyMeasurable.indicator measurableSet_Ioi
  have hbd : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) →
      ‖rayDamp (cx (poleWaveRay f)) 1 x‖ ≤ C * Real.exp (-(1 / 2 * x)) := by
    intro x hx
    simp only [rayDamp, Set.indicator_apply, if_pos hx]
    rw [norm_mul, norm_expRay, Complex.ofReal_re]
    show ‖((poleWaveRay f x : ℝ) : ℂ)‖ * Real.exp (-(1 * x)) ≤ C * Real.exp (-(1 / 2 * x))
    rw [Complex.norm_real, Real.norm_eq_abs, hCdef]
    have h1 := abs_poleWaveRay_le hφi (mem_Ioi.mp hx).le
    have h2 : Real.exp (x / 2) * Real.exp (-(1 * x)) = Real.exp (-(1 / 2 * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc |poleWaveRay f x| * Real.exp (-(1 * x))
        ≤ Real.exp (x / 2) * (∫ y : ℝ, ‖Real.exp (-(y / 2)) * f y‖) * Real.exp (-(1 * x)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = (∫ y : ℝ, ‖Real.exp (-(y / 2)) * f y‖) * Real.exp (-(1 / 2 * x)) := by
          rw [← h2]
          ring
  have hzero : ∀ x : ℝ, x ∉ Ioi (0 : ℝ) → rayDamp (cx (poleWaveRay f)) 1 x = 0 := fun x hx => by
    simp only [rayDamp, Set.indicator_apply, if_neg hx]
  have hI1 : IntegrableOn (fun x : ℝ => C * Real.exp (-(1 / 2 * x))) (Ioi 0) :=
    (HTGeometry.integrableOn_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2) 0).const_mul C
  have hI2 : IntegrableOn (fun x : ℝ => C ^ 2 * Real.exp (-(1 * x))) (Ioi 0) :=
    (HTGeometry.integrableOn_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1) 0).const_mul (C ^ 2)
  constructor
  · refine (hI1.integrable_indicator measurableSet_Ioi).mono' hm (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx]
      exact hbd x hx
    · rw [Set.indicator_apply, if_neg hx, hzero x hx, norm_zero]
  · refine (memLp_two_iff_integrable_sq_norm hm).mpr ?_
    refine (hI2.integrable_indicator measurableSet_Ioi).mono' (hm.norm.pow 2)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx]
      calc ‖rayDamp (cx (poleWaveRay f)) 1 x‖ ^ 2 ≤ (C * Real.exp (-(1 / 2 * x))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hbd x hx) 2
        _ = C ^ 2 * Real.exp (-(1 * x)) := by
            rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
            congr 2
            ring
    · rw [Set.indicator_apply, if_neg hx, hzero x hx, norm_zero]
      norm_num

/-! ### Polarized Plancherel on the line `Re p = 1` -/

/-- The complexified test profile on the ray, weighted by `e^{2x}`. -/
def rayTest (g : ℝ → ℝ) (x : ℝ) : ℂ := ((Real.exp (2 * x) * g x : ℝ) : ℂ)

/-- **Polarized Plancherel.** The transform of the weighted test on `Re p = 1` against the
transform of a datum on `Re p = s` is the pairing of the test with the datum, weighted by
`e^{(1 - s) x}`. -/
theorem integral_conj_laplaceRay_rayTest_mul {g : ℝ → ℝ}
    (hψ : MemLp (rayTest g) 2 (volume.restrict (Ioi (0 : ℝ)))) {φ : ℝ → ℂ} {s : ℝ}
    (hφ1 : Integrable (rayDamp φ s)) (hφ2 : MemLp (rayDamp φ s) 2 volume) :
    (∫ ξ : ℝ, (starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
        laplaceRay φ (rayLine s ξ)) =
      ∫ x in Ioi (0 : ℝ), ((Real.exp ((1 - s) * x) * g x : ℝ) : ℂ) * φ x := by
  have h := integral_conj_fourier_mul_fourier (integrable_rayDamp hψ one_pos)
    (memLp_two_rayDamp hψ zero_le_one) hφ1 hφ2
  simp only [fourierIntegral_rayDamp] at h
  rw [h, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · simp only [rayDamp, Set.indicator_apply, if_pos hx, rayTest]
    rw [map_mul, Complex.conj_ofReal, expRay_ofReal, Complex.conj_ofReal, expRay_ofReal]
    have e : Real.exp ((1 - s) * x) * g x =
        Real.exp (2 * x) * g x * Real.exp (-(1 * x)) * Real.exp (-(s * x)) := by
      have e1 : Real.exp ((1 - s) * x) =
          Real.exp (2 * x) * Real.exp (-(1 * x)) * Real.exp (-(s * x)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [e1]
      ring
    rw [e]
    push_cast
    ring
  · simp only [rayDamp, Set.indicator_apply, if_neg hx, map_zero, zero_mul]

/-- A shift of the datum against the test. -/
theorem integral_conj_rayTest_mul_translate {f g : ℝ → ℝ}
    (hf2 : MemLp (cx f) 2 (volume : Measure ℝ)) (hf0 : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hψ : MemLp (rayTest g) 2 (volume.restrict (Ioi (0 : ℝ)))) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (∫ ξ : ℝ, (starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
        (expRay (rayLine 1 ξ) ℓ * laplaceRay (cx f) (rayLine 1 ξ))) =
      ((∫ x in Ioi (0 : ℝ), g x * f (x - ℓ) : ℝ) : ℂ) := by
  have hφ : MemLp (fun x : ℝ => cx f (x - ℓ)) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    memLp_translate_restrict hf2 ℓ
  have hc0 : ∀ x : ℝ, x ≤ 0 → cx f x = 0 := fun x hx => by
    show ((f x : ℝ) : ℂ) = 0
    rw [hf0 x hx, Complex.ofReal_zero]
  have h := integral_conj_laplaceRay_rayTest_mul hψ (integrable_rayDamp hφ one_pos)
    (memLp_two_rayDamp hφ zero_le_one)
  have e : ∀ ξ : ℝ, laplaceRay (fun x : ℝ => cx f (x - ℓ)) (rayLine 1 ξ) =
      expRay (rayLine 1 ξ) ℓ * laplaceRay (cx f) (rayLine 1 ξ) := fun ξ =>
    laplaceRay_translate hc0 hℓ _
  simp only [e] at h
  rw [h, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show ((Real.exp ((1 - 1) * x) * g x : ℝ) : ℂ) * ((f (x - ℓ) : ℝ) : ℂ) =
    ((g x * f (x - ℓ) : ℝ) : ℂ)
  rw [sub_self, zero_mul, Real.exp_zero, one_mul, Complex.ofReal_mul]

/-- The pole wave against the test. -/
theorem integral_conj_rayTest_mul_poleWaveRay {f g : ℝ → ℝ} (hfm : Measurable f)
    (hf1 : Integrable f) (hf0 : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hψ : MemLp (rayTest g) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (∫ ξ : ℝ, (starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
        ((rayLine 1 ξ - 1 / 2)⁻¹ * laplaceRay (cx f) (rayLine 1 ξ))) =
      ((∫ x in Ioi (0 : ℝ), g x * poleWaveRay f x : ℝ) : ℂ) := by
  obtain ⟨h1, h2⟩ := integrable_and_memLp_rayDamp_poleWaveRay
    (integrable_exp_neg_half_mul hfm hf1 hf0)
  have h := integral_conj_laplaceRay_rayTest_mul hψ h1 h2
  have e : ∀ ξ : ℝ, laplaceRay (cx (poleWaveRay f)) (rayLine 1 ξ) =
      (rayLine 1 ξ - 1 / 2)⁻¹ * laplaceRay (cx f) (rayLine 1 ξ) := fun ξ =>
    laplaceRay_poleWaveRay hfm hf1 hf0 (by rw [rayLine_re]; norm_num)
  simp only [e] at h
  rw [h, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show ((Real.exp ((1 - 1) * x) * g x : ℝ) : ℂ) * ((poleWaveRay f x : ℝ) : ℂ) =
    ((g x * poleWaveRay f x : ℝ) : ℂ)
  rw [sub_self, zero_mul, Real.exp_zero, one_mul, Complex.ofReal_mul]

/-- **The forward prime sum on the line `Re p = 1`.** The shifts sum to the Euler sum
`1/(p - 1/2) - N(1/2 + p)` under the integral: the series converges absolutely there. -/
theorem ofReal_tsum_forwardRay {f g : ℝ → ℝ} (hf2 : MemLp (cx f) 2 (volume : Measure ℝ))
    (hf0 : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hψ : MemLp (rayTest g) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    ((∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ), g x * f (x - Real.log n) : ℝ) : ℂ) =
      ∫ ξ : ℝ, (starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
        (((rayLine 1 ξ - 1 / 2)⁻¹ - zetaRegularLogDeriv (1 / 2 + rayLine 1 ξ)) *
          laplaceRay (cx f) (rayLine 1 ξ)) := by
  have hA := memLp_two_laplaceRay_line (hf2.restrict (Ioi (0 : ℝ))) one_pos
  have hB := memLp_two_laplaceRay_line hψ one_pos
  have hBA : Integrable fun ξ : ℝ => ‖laplaceRay (rayTest g) (rayLine 1 ξ)‖ *
      ‖laplaceRay (cx f) (rayLine 1 ξ)‖ :=
    HTGeometry.integrable_mul_of_sq_integrable hB.aestronglyMeasurable.norm
      hA.aestronglyMeasurable.norm
      ((memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).mp hB)
      ((memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mp hA)
  have hconjm : AEStronglyMeasurable (fun ξ : ℝ =>
      (starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
        laplaceRay (cx f) (rayLine 1 ξ)) volume :=
    (Complex.continuous_conj.comp_aestronglyMeasurable hB.aestronglyMeasurable).mul
      hA.aestronglyMeasurable
  have hnorm : ∀ (n : ℕ) (ξ : ℝ),
      ‖(((vonMangoldtAtom n : ℝ) : ℂ) * expRay (rayLine 1 ξ) (Real.log n)) *
        ((starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
          laplaceRay (cx f) (rayLine 1 ξ))‖ =
      vonMangoldtAtom n * Real.exp (-(1 * Real.log n)) *
        (‖laplaceRay (rayTest g) (rayLine 1 ξ)‖ * ‖laplaceRay (cx f) (rayLine 1 ξ)‖) := by
    intro n ξ
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (vonMangoldtAtom_nonneg n), norm_expRay, rayLine_re, RCLike.norm_conj]
  have hFint : ∀ n : ℕ, Integrable fun ξ : ℝ =>
      (((vonMangoldtAtom n : ℝ) : ℂ) * expRay (rayLine 1 ξ) (Real.log n)) *
        ((starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
          laplaceRay (cx f) (rayLine 1 ξ)) := by
    intro n
    have hc : Continuous fun ξ : ℝ =>
        ((vonMangoldtAtom n : ℝ) : ℂ) * expRay (rayLine 1 ξ) (Real.log n) := by
      unfold expRay rayLine
      fun_prop
    exact (hBA.const_mul (vonMangoldtAtom n * Real.exp (-(1 * Real.log n)))).mono'
      (hc.aestronglyMeasurable.mul hconjm) (Eventually.of_forall fun ξ => (hnorm n ξ).le)
  have hsumΛ : Summable fun n : ℕ => vonMangoldtAtom n * Real.exp (-(1 * Real.log n)) :=
    summable_vonMangoldt_div_threeHalves.congr fun n => by
      rw [vonMangoldtAtom_mul_exp_eq]
      norm_num
  have hsum : Summable fun n : ℕ => ∫ ξ : ℝ,
      ‖(((vonMangoldtAtom n : ℝ) : ℂ) * expRay (rayLine 1 ξ) (Real.log n)) *
        ((starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
          laplaceRay (cx f) (rayLine 1 ξ))‖ := by
    simp_rw [hnorm, integral_const_mul]
    exact hsumΛ.mul_right _
  have hsumF := hasSum_integral_of_summable_integral_norm hFint hsum
  have htsum : ∀ ξ : ℝ, (∑' n : ℕ,
      (((vonMangoldtAtom n : ℝ) : ℂ) * expRay (rayLine 1 ξ) (Real.log n)) *
        ((starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
          laplaceRay (cx f) (rayLine 1 ξ))) =
      (starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
        (((rayLine 1 ξ - 1 / 2)⁻¹ - zetaRegularLogDeriv (1 / 2 + rayLine 1 ξ)) *
          laplaceRay (cx f) (rayLine 1 ξ)) := by
    intro ξ
    rw [tsum_mul_right]
    have h' : (∑' n : ℕ, ((vonMangoldtAtom n : ℝ) : ℂ) * expRay (rayLine 1 ξ) (Real.log n)) =
        (rayLine 1 ξ - 1 / 2)⁻¹ - zetaRegularLogDeriv (1 / 2 + rayLine 1 ξ) :=
      tsum_vonMangoldtAtom_mul_cexp_neg (p := rayLine 1 ξ) (by rw [rayLine_re]; norm_num)
    rw [h']
    ring
  have hint : ∀ n : ℕ, (∫ ξ : ℝ,
      (((vonMangoldtAtom n : ℝ) : ℂ) * expRay (rayLine 1 ξ) (Real.log n)) *
        ((starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
          laplaceRay (cx f) (rayLine 1 ξ))) =
      ((vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ), g x * f (x - Real.log n) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_mul, ← integral_conj_rayTest_mul_translate hf2 hf0 hψ
      (Real.log_natCast_nonneg n), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    beta_reduce
    ring
  rw [Complex.ofReal_tsum]
  calc (∑' n : ℕ, ((vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ), g x * f (x - Real.log n) : ℝ) : ℂ))
      = ∑' n : ℕ, ∫ ξ : ℝ,
          (((vonMangoldtAtom n : ℝ) : ℂ) * expRay (rayLine 1 ξ) (Real.log n)) *
            ((starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
              laplaceRay (cx f) (rayLine 1 ξ)) := tsum_congr fun n => (hint n).symm
    _ = ∫ ξ : ℝ, ∑' n : ℕ,
          (((vonMangoldtAtom n : ℝ) : ℂ) * expRay (rayLine 1 ξ) (Real.log n)) *
            ((starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
              laplaceRay (cx f) (rayLine 1 ξ)) := hsumF.tsum_eq
    _ = _ := integral_congr_ae (Eventually.of_forall htsum)

/-! ### The mean-square bound on the ray -/

/-- **The forward prime-minus-pole form on the ray.** The difference of the forward prime sum and
the pole wave, paired with `g`, is the pairing of `e^{σx} g` with the Paley–Wiener datum of the
transform `-N(1/2 + p) L f(p)`; its square is at most the boundary mass on `Re p = σ` times
`∫ e^{2σx} g²`. -/
theorem sq_forwardRay_sub_poleRay_le {κ σ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκσ : κ < σ) (hσ1 : σ < 1)
    {f g : ℝ → ℝ} (hfm : Measurable f) (hf1 : Integrable f)
    (hf2 : MemLp (cx f) 2 (volume : Measure ℝ)) (hf0 : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hgm : Measurable g) (hψ : MemLp (rayTest g) 2 (volume.restrict (Ioi (0 : ℝ))))
    (hB : Integrable fun t : ℝ => ‖primeWaveTransform (cx f) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :
    ((∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ), g x * f (x - Real.log n)) -
        ∫ x in Ioi (0 : ℝ), g x * poleWaveRay f x) ^ 2 ≤
      ((2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖primeWaveTransform (cx f) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) *
        ∫ x in Ioi (0 : ℝ), (Real.exp (σ * x) * g x) ^ 2 := by
  have hf2r : MemLp (cx f) 2 (volume.restrict (Ioi (0 : ℝ))) := hf2.restrict _
  have hΦ := isHalfPlaneHardy_primeWaveHardy hκ hzero hκσ hf2r hB
  have hh2 := memLp_two_hardyDatum hΦ
  have hmass := integral_norm_sq_hardyDatum_le hΦ
  have h1σ : 0 < 1 - σ := by linarith
  -- on the line `Re p = 1` the transform of the wave is the transform of its datum
  have hwave : ∀ ξ : ℝ, laplaceRay (hardyDatum (primeWaveHardy (cx f) σ) hΦ)
      (rayLine (1 - σ) ξ) = primeWaveTransform (cx f) (rayLine 1 ξ) := by
    intro ξ
    have h := isHalfPlaneHardy_eq_laplaceRay hΦ (w := rayLine (1 - σ) ξ)
      (by rw [rayLine_re]; exact h1σ)
    have e : (σ : ℂ) + rayLine (1 - σ) ξ = rayLine 1 ξ := by
      unfold rayLine
      push_cast
      ring
    rw [← h]
    show primeWaveTransform (cx f) ((σ : ℂ) + rayLine (1 - σ) ξ) = _
    rw [e]
  have hBm := memLp_two_laplaceRay_line hψ one_pos
  have hAm := memLp_two_laplaceRay_line hf2r one_pos
  have hHm := memLp_two_laplaceRay_line hh2 h1σ
  have hBsq := (memLp_two_iff_integrable_sq_norm hBm.aestronglyMeasurable).mp hBm
  have hconjB : AEStronglyMeasurable (fun ξ : ℝ =>
      (starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ))) volume :=
    Complex.continuous_conj.comp_aestronglyMeasurable hBm.aestronglyMeasurable
  have hYint : Integrable fun ξ : ℝ => (starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
      laplaceRay (hardyDatum (primeWaveHardy (cx f) σ) hΦ) (rayLine (1 - σ) ξ) := by
    refine (HTGeometry.integrable_mul_of_sq_integrable hBm.aestronglyMeasurable.norm
      hHm.aestronglyMeasurable.norm hBsq
      ((memLp_two_iff_integrable_sq_norm hHm.aestronglyMeasurable).mp hHm)).mono'
      (hconjB.mul hHm.aestronglyMeasurable) (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, RCLike.norm_conj]
  have hXint : Integrable fun ξ : ℝ => (starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
      ((rayLine 1 ξ - 1 / 2)⁻¹ * laplaceRay (cx f) (rayLine 1 ξ)) := by
    have hne : ∀ ξ : ℝ, rayLine 1 ξ - 1 / 2 ≠ 0 := fun ξ h => by
      have h1 := congrArg Complex.re h
      rw [Complex.sub_re, rayLine_re, re_one_half, Complex.zero_re] at h1
      norm_num at h1
    have hcinv : Continuous fun ξ : ℝ => (rayLine 1 ξ - 1 / 2)⁻¹ :=
      Continuous.inv₀ (by unfold rayLine; fun_prop) hne
    refine ((HTGeometry.integrable_mul_of_sq_integrable hBm.aestronglyMeasurable.norm
      hAm.aestronglyMeasurable.norm hBsq
      ((memLp_two_iff_integrable_sq_norm hAm.aestronglyMeasurable).mp hAm)).const_mul 2).mono'
      (hconjB.mul (hcinv.aestronglyMeasurable.mul hAm.aestronglyMeasurable))
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, norm_mul, RCLike.norm_conj, norm_inv]
    have h2 : ‖rayLine 1 ξ - 1 / 2‖⁻¹ ≤ 2 := by
      have h1 := Complex.re_le_norm (rayLine 1 ξ - 1 / 2)
      rw [Complex.sub_re, rayLine_re, re_one_half] at h1
      refine inv_le_of_inv_le₀ (by norm_num) ?_
      rw [show (2 : ℝ)⁻¹ = 1 - 1 / 2 by norm_num]
      exact h1
    nlinarith [mul_nonneg (sub_nonneg.mpr h2)
      (mul_nonneg (norm_nonneg (laplaceRay (rayTest g) (rayLine 1 ξ)))
        (norm_nonneg (laplaceRay (cx f) (rayLine 1 ξ))))]
  -- the three pairings
  have hY := integral_conj_laplaceRay_rayTest_mul hψ (integrable_rayDamp hh2 h1σ)
    (memLp_two_rayDamp hh2 h1σ.le)
  rw [show (1 : ℝ) - (1 - σ) = σ by ring] at hY
  have hX := integral_conj_rayTest_mul_poleWaveRay hfm hf1 hf0 hψ
  have hZ := ofReal_tsum_forwardRay hf2 hf0 hψ
  have hsplit : (∫ ξ : ℝ, (starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
        (((rayLine 1 ξ - 1 / 2)⁻¹ - zetaRegularLogDeriv (1 / 2 + rayLine 1 ξ)) *
          laplaceRay (cx f) (rayLine 1 ξ))) =
      (∫ ξ : ℝ, (starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
        ((rayLine 1 ξ - 1 / 2)⁻¹ * laplaceRay (cx f) (rayLine 1 ξ))) +
      ∫ ξ : ℝ, (starRingEnd ℂ) (laplaceRay (rayTest g) (rayLine 1 ξ)) *
        laplaceRay (hardyDatum (primeWaveHardy (cx f) σ) hΦ) (rayLine (1 - σ) ξ) := by
    rw [← integral_add hXint hYint]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    beta_reduce
    rw [hwave ξ]
    unfold primeWaveTransform
    ring
  have hD : (((∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ), g x * f (x - Real.log n)) -
        ∫ x in Ioi (0 : ℝ), g x * poleWaveRay f x : ℝ) : ℂ) =
      ∫ x in Ioi (0 : ℝ), ((Real.exp (σ * x) * g x : ℝ) : ℂ) *
        hardyDatum (primeWaveHardy (cx f) σ) hΦ x := by
    rw [Complex.ofReal_sub, hZ, ← hX, hsplit, add_sub_cancel_left, hY]
  -- Cauchy–Schwarz against the datum
  have hk2 : Integrable (fun x : ℝ => (Real.exp (σ * x) * g x) ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine ((memLp_two_iff_integrable_sq_norm hψ.aestronglyMeasurable).mp hψ).mono'
      (((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul hgm).pow_const
        2).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    show (Real.exp (σ * x) * g x) ^ 2 ≤ ‖((Real.exp (2 * x) * g x : ℝ) : ℂ)‖ ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, mul_pow]
    have hx0 : (0 : ℝ) < x := hx
    have h1 : Real.exp (σ * x) ≤ Real.exp (2 * x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le h1 2) (sq_nonneg _)
  have hkm : AEStronglyMeasurable (fun x : ℝ => |Real.exp (σ * x) * g x|)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      hgm).abs.aestronglyMeasurable
  have hcs := HTGeometry.sq_integral_mul_le (μ := volume.restrict (Ioi (0 : ℝ))) hkm
    hh2.aestronglyMeasurable.norm (by simpa only [sq_abs] using hk2)
    (integrableOn_norm_sq_of_memLp hh2)
  have hnorm : ‖∫ x in Ioi (0 : ℝ), ((Real.exp (σ * x) * g x : ℝ) : ℂ) *
        hardyDatum (primeWaveHardy (cx f) σ) hΦ x‖ ≤
      ∫ x in Ioi (0 : ℝ), |Real.exp (σ * x) * g x| *
        ‖hardyDatum (primeWaveHardy (cx f) σ) hΦ x‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ‖((Real.exp (σ * x) * g x : ℝ) : ℂ) * hardyDatum (primeWaveHardy (cx f) σ) hΦ x‖ =
      |Real.exp (σ * x) * g x| * ‖hardyDatum (primeWaveHardy (cx f) σ) hΦ x‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ((∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ), g x * f (x - Real.log n)) -
        ∫ x in Ioi (0 : ℝ), g x * poleWaveRay f x) ^ 2
      = ‖(((∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ), g x * f (x - Real.log n)) -
          ∫ x in Ioi (0 : ℝ), g x * poleWaveRay f x : ℝ) : ℂ)‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ ≤ (∫ x in Ioi (0 : ℝ), |Real.exp (σ * x) * g x| *
          ‖hardyDatum (primeWaveHardy (cx f) σ) hΦ x‖) ^ 2 := by
        rw [hD]
        exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∫ x in Ioi (0 : ℝ), |Real.exp (σ * x) * g x| ^ 2) *
          ∫ x in Ioi (0 : ℝ), ‖hardyDatum (primeWaveHardy (cx f) σ) hΦ x‖ ^ 2 := hcs
    _ = (∫ x in Ioi (0 : ℝ), (Real.exp (σ * x) * g x) ^ 2) *
          ∫ x in Ioi (0 : ℝ), ‖hardyDatum (primeWaveHardy (cx f) σ) hΦ x‖ ^ 2 := by
        simp only [sq_abs]
    _ ≤ (∫ x in Ioi (0 : ℝ), (Real.exp (σ * x) * g x) ^ 2) *
          ((2 * Real.pi)⁻¹ *
            ∫ t : ℝ, ‖primeWaveTransform (cx f) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmass (integral_nonneg fun x => sq_nonneg _)
    _ = _ := mul_comm _ _

/-! ### The forward forms of a profile on the negative half-line -/

/-- The forward half of the prime form: `Σ Λ(n) n^{-1/2} ∫ G(t) F(t + log n) dt`. -/
def forwardPrimeForm (F G : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * ∫ t : ℝ, G t * F (t + Real.log n)

/-- The forward pole wave `e^{-v/2} ∫_{u > v} F(u) e^{u/2} du`. -/
def forwardPoleWave (F : ℝ → ℝ) (v : ℝ) : ℝ :=
  Real.exp (-(v / 2)) * ∫ u in Ioi v, F u * Real.exp (u / 2)

/-- The forward half of the pole form: the part `u > v` of `∫∫ G(v) e^{-v/2} F(u) e^{u/2}`. -/
def forwardPoleForm (F G : ℝ → ℝ) : ℝ := ∫ v : ℝ, G v * forwardPoleWave F v

theorem forwardPoleWave_neg {F : ℝ → ℝ} (hF0 : ∀ u : ℝ, 0 ≤ u → F u = 0) {x : ℝ} (hx : 0 ≤ x) :
    forwardPoleWave F (-x) = poleWaveRay (fun y : ℝ => F (-y)) x := by
  have h1 := integral_comp_neg_Ioi (-x) (fun y : ℝ => Real.exp (-(y / 2)) * F (-y))
  rw [neg_neg] at h1
  have h2 : (∫ u in Ioi (-x), F u * Real.exp (u / 2)) =
      ∫ u in Ioi (-x), Real.exp (-(-u / 2)) * F (- -u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    show F u * Real.exp (u / 2) = Real.exp (-(-u / 2)) * F (- -u)
    rw [neg_neg, show -(-u / 2) = u / 2 by ring, mul_comm]
  have h3 : (∫ u in Ioi (-x), F u * Real.exp (u / 2)) =
      ∫ y in Iic x, Real.exp (-(y / 2)) * F (-y) := h2.trans h1
  have h4 : (∫ y in Iic x, Real.exp (-(y / 2)) * F (-y)) =
      ∫ y in Ioc (0 : ℝ) x, Real.exp (-(y / 2)) * F (-y) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic Ioc_subset_Iic_self
      fun y hy => ?_
    have hy0 : y ≤ 0 := by
      by_contra hcon
      exact hy.2 ⟨not_le.mp hcon, hy.1⟩
    rw [hF0 (-y) (by linarith), mul_zero]
  show Real.exp (-(-x / 2)) * (∫ u in Ioi (-x), F u * Real.exp (u / 2)) =
    Real.exp (x / 2) * ∫ y in (0 : ℝ)..x, Real.exp (-(y / 2)) * F (-y)
  rw [h3, h4, intervalIntegral.integral_of_le hx, show -(-x / 2) = x / 2 by ring]

/-- **The forward prime-minus-pole form is bounded in mean square.** If every centred zero has
`Re z ≤ κ` and `κ < σ < 1`, then for profiles `F`, `G` of the energy domain

  `(forward prime form - forward pole form)² ≤
     (1/2π) ∫ |N(1/2 + σ + it)|² |L F(σ + it)|² dt · ∫ G(v)² e^{-2σv} dv`. -/
theorem sq_forwardPrimeForm_sub_forwardPoleForm_le {κ σ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκσ : κ < σ) (hσ1 : σ < 1)
    {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hB : Integrable fun t : ℝ => ‖zetaRegularLogDeriv (1 / 2 + ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2 *
      ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :
    (forwardPrimeForm F G - forwardPoleForm F G) ^ 2 ≤
      ((2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖zetaRegularLogDeriv (1 / 2 + ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2 *
        ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) *
        ∫ v : ℝ, G v ^ 2 * Real.exp (-(2 * σ * v)) := by
  have hfm : Measurable fun x : ℝ => F (-x) := hF.meas.comp measurable_neg
  have hf1 : Integrable fun x : ℝ => F (-x) := hF.integrable.comp_neg
  have hf2 : MemLp (cx fun x : ℝ => F (-x)) 2 (volume : Measure ℝ) :=
    memLp_cx_of_sq hf1 hF.sq.comp_neg
  have hf0 : ∀ x : ℝ, x ≤ 0 → F (-x) = 0 := fun x hx => hF.support (-x) (by linarith)
  have hgm : Measurable fun x : ℝ => G (-x) := hG.meas.comp measurable_neg
  have hg0 : ∀ x : ℝ, x ≤ 0 → G (-x) = 0 := fun x hx => hG.support (-x) (by linarith)
  have hψ : MemLp (rayTest fun x : ℝ => G (-x)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
    have hm : AEStronglyMeasurable (rayTest fun x : ℝ => G (-x))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (Complex.measurable_ofReal.comp ((Real.measurable_exp.comp
        (measurable_const.mul measurable_id)).mul hgm)).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).mpr ?_
    refine hG.exponential.comp_neg.restrict.mono' (hm.norm.pow 2)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    show ‖((Real.exp (2 * x) * G (-x) : ℝ) : ℂ)‖ ^ 2 ≤ G (-x) ^ 2 * Real.exp (-(8 * -x))
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [sq, ← Real.exp_add]
    have hx0 : (0 : ℝ) < x := hx
    exact Real.exp_le_exp.mpr (by linarith)
  have hlap : ∀ z : ℂ, laplaceRay (cx fun x : ℝ => F (-x)) z = negativeHalfLineLaplace (cx F) z :=
    fun z => (negativeHalfLineLaplace_eq_laplaceRay_reflect (cx F) (fun u hu => by
      show ((F u : ℝ) : ℂ) = 0
      rw [hF.support u hu, Complex.ofReal_zero]) z).symm
  have hpw : ∀ t : ℝ, ‖primeWaveTransform (cx fun x : ℝ => F (-x)) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      ‖zetaRegularLogDeriv (1 / 2 + ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2 *
        ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := fun t => by
    unfold primeWaveTransform
    rw [norm_neg, norm_mul, mul_pow, hlap]
  have hB' : Integrable fun t : ℝ =>
      ‖primeWaveTransform (cx fun x : ℝ => F (-x)) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    hB.congr (Eventually.of_forall fun t => (hpw t).symm)
  have hcore : ((∑' n : ℕ, vonMangoldtAtom n *
        ∫ x in Ioi (0 : ℝ), G (-x) * F (-(x - Real.log n))) -
        ∫ x in Ioi (0 : ℝ), G (-x) * poleWaveRay (fun y : ℝ => F (-y)) x) ^ 2 ≤
      ((2 * Real.pi)⁻¹ * ∫ t : ℝ,
        ‖primeWaveTransform (cx fun x : ℝ => F (-x)) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) *
        ∫ x in Ioi (0 : ℝ), (Real.exp (σ * x) * G (-x)) ^ 2 :=
    sq_forwardRay_sub_poleRay_le hκ hzero hκσ hσ1 hfm hf1 hf2 hf0 hgm hψ hB'
  -- back to the negative half-line
  have efwd : (∑' n : ℕ, vonMangoldtAtom n *
      ∫ x in Ioi (0 : ℝ), G (-x) * F (-(x - Real.log n))) = forwardPrimeForm F G := by
    unfold forwardPrimeForm
    refine tsum_congr fun n => ?_
    congr 1
    have e1 : (∫ x in Ioi (0 : ℝ), G (-x) * F (-(x - Real.log n))) =
        ∫ x : ℝ, G (-x) * F (-(x - Real.log n)) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hg0 x (not_lt.mp hx), zero_mul]
    have e2 : (∫ x : ℝ, G (-x) * F (-x + Real.log n)) = ∫ t : ℝ, G t * F (t + Real.log n) :=
      integral_neg_eq_self (fun t : ℝ => G t * F (t + Real.log n)) volume
    rw [e1, ← e2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show G (-x) * F (-(x - Real.log n)) = G (-x) * F (-x + Real.log n)
    rw [neg_sub, sub_eq_neg_add]
  have epole : (∫ x in Ioi (0 : ℝ), G (-x) * poleWaveRay (fun y : ℝ => F (-y)) x) =
      forwardPoleForm F G := by
    have e1 : (∫ x in Ioi (0 : ℝ), G (-x) * poleWaveRay (fun y : ℝ => F (-y)) x) =
        ∫ x in Ioi (0 : ℝ), G (-x) * forwardPoleWave F (-x) :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx => by
        show G (-x) * poleWaveRay (fun y : ℝ => F (-y)) x = G (-x) * forwardPoleWave F (-x)
        rw [forwardPoleWave_neg hF.support (mem_Ioi.mp hx).le]
    have e2 : (∫ x in Ioi (0 : ℝ), G (-x) * forwardPoleWave F (-x)) =
        ∫ x : ℝ, G (-x) * forwardPoleWave F (-x) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hg0 x (not_lt.mp hx), zero_mul]
    have e3 : (∫ x : ℝ, G (-x) * forwardPoleWave F (-x)) = ∫ v : ℝ, G v * forwardPoleWave F v :=
      integral_neg_eq_self (fun v : ℝ => G v * forwardPoleWave F v) volume
    exact e1.trans (e2.trans e3)
  have erhs : (∫ x in Ioi (0 : ℝ), (Real.exp (σ * x) * G (-x)) ^ 2) =
      ∫ v : ℝ, G v ^ 2 * Real.exp (-(2 * σ * v)) := by
    have e1 : (∫ x in Ioi (0 : ℝ), (Real.exp (σ * x) * G (-x)) ^ 2) =
        ∫ x in Ioi (0 : ℝ), G (-x) ^ 2 * Real.exp (-(2 * σ * -x)) :=
      setIntegral_congr_fun measurableSet_Ioi fun x _ => by
        show (Real.exp (σ * x) * G (-x)) ^ 2 = G (-x) ^ 2 * Real.exp (-(2 * σ * -x))
        rw [mul_pow, sq (Real.exp _), ← Real.exp_add, mul_comm]
        congr 2
        ring
    have e2 : (∫ x in Ioi (0 : ℝ), G (-x) ^ 2 * Real.exp (-(2 * σ * -x))) =
        ∫ x : ℝ, G (-x) ^ 2 * Real.exp (-(2 * σ * -x)) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hg0 x (not_lt.mp hx)]
        ring
    have e3 : (∫ x : ℝ, G (-x) ^ 2 * Real.exp (-(2 * σ * -x))) =
        ∫ v : ℝ, G v ^ 2 * Real.exp (-(2 * σ * v)) :=
      integral_neg_eq_self (fun v : ℝ => G v ^ 2 * Real.exp (-(2 * σ * v))) volume
    exact e1.trans (e2.trans e3)
  have eint : (∫ t : ℝ,
      ‖primeWaveTransform (cx fun x : ℝ => F (-x)) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      ∫ t : ℝ, ‖zetaRegularLogDeriv (1 / 2 + ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2 *
        ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    integral_congr_ae (Eventually.of_forall hpw)
  rw [efwd, epole, erhs, eint] at hcore
  exact hcore

end GaloisForLFunctions.ExclusionOfTheCriticalState
