import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel
import GaloisForLFunctions.HTGeometry.CauchyKernelFourier
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.RHTower.LorentzianZeroMass
import GaloisForLFunctions.RHTower.RiemannKernelStripLPMaximality
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointCoercivity
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundedWeilEnergyUpgradesL1LimitsToStrongLimits
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroSumOfAProfileConvergesAfterOneSubtraction
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheEnergyDomainIsStableUnderLipschitzMultipliers

/-!
# The energy norm controls the values at the zeros

For a profile `H` of the energy domain and points `w_ρ` attached to the zeros `ρ` of `ξ` with
`1/2 ≤ Re w_ρ ≤ 3/2` and `Im w_ρ = ± Im ρ`,

  `Σ_ρ |L H(w_ρ)|² ≤ (16/π) ∫ (C + log(|t| + 4)) |L H(it)|² dt < ∞`,

the sum over the zeros with multiplicity. The transform of a profile of the domain is
square-summable on the zero set at unit depth inside its half-plane, and the logarithmic (Gamma)
energy is the norm that controls it. In particular a profile `G` whose unit tilt `e^{-u} G` lies in
the domain has square-summable values `L G(z)` and `L G(-z)` at the centred zeros `z = ρ - 1/2`.

Mechanism. `H` lives on `u ≤ 0`, so `e^{du} = e^{-d|u|}` on its support and `L H(d + iγ)` is the
Poisson average `∫ P_d(x) L H(i(γ + x)) dx` of the boundary values. Jensen's inequality gives
`|L H(d + iγ)|² ≤ ∫ P_d(t - γ) |L H(it)|² dt`, and `P_d(τ) ≤ (2/π)/(1 + τ²)` for
`1/2 ≤ d ≤ 3/2`. Summed over the zeros the kernels add up to the Lorentzian zero mass
`Σ_ρ 1/(1 + (t - γ_ρ)²) ≤ 8 (C + log(|t| + 4))`, and the Gamma bracket dominates the logarithm.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The Poisson representation -/

theorem ofReal_halfPlanePoisson (d x : ℝ) :
    ((halfPlanePoisson d x : ℝ) : ℂ) =
      ((d / Real.pi : ℝ) : ℂ) * ((d ^ (2 : ℕ) + x ^ (2 : ℕ) : ℝ) : ℂ)⁻¹ := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, halfPlanePoisson, div_mul_eq_div_div,
    div_eq_mul_inv (d / Real.pi)]

/-- The Poisson kernel has transform `e^{-d|u|}`. -/
theorem integral_halfPlanePoisson_mul_cexp {d : ℝ} (hd : 0 < d) (u : ℝ) :
    (∫ x : ℝ, ((halfPlanePoisson d x : ℝ) : ℂ) * cexp (I * (x : ℂ) * (u : ℂ))) =
      ((Real.exp (-(d * |u|)) : ℝ) : ℂ) := by
  have h := integral_cexp_mul_inv_sq_add_sq hd u
  have e : ∀ x : ℝ, ((halfPlanePoisson d x : ℝ) : ℂ) * cexp (I * (x : ℂ) * (u : ℂ)) =
      ((d / Real.pi : ℝ) : ℂ) * (cexp (((x * u : ℝ) : ℂ) * I) *
        ((d ^ (2 : ℕ) + x ^ (2 : ℕ) : ℝ) : ℂ)⁻¹) := by
    intro x
    have h1 : I * (x : ℂ) * (u : ℂ) = ((x * u : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [h1, ofReal_halfPlanePoisson]
    ring
  simp_rw [e]
  rw [integral_const_mul, h, ← Complex.ofReal_mul]
  congr 1
  rw [← mul_assoc, div_mul_div_comm, mul_comm d Real.pi,
    div_self (mul_ne_zero Real.pi_ne_zero hd.ne'), one_mul]

/-- **Poisson representation.** A profile on the negative half-line has `e^{du} = e^{-d|u|}` on
its support, so its transform at `d + iγ` is the Poisson average of the boundary values. -/
theorem laplace_eq_integral_halfPlanePoisson_mul_paperFT {H : ℝ → ℝ} (hm : Measurable H)
    (hi : Integrable H) (hs : ∀ u, 0 ≤ u → H u = 0) {d : ℝ} (hd : 0 < d) (γ : ℝ) :
    negativeHalfLineLaplace (cx H) ((d : ℂ) + (γ : ℂ) * I) =
      ∫ x : ℝ, ((halfPlanePoisson d x : ℝ) : ℂ) * paperFT (cx H) ((γ + x : ℝ) : ℂ) := by
  have hF : Integrable (Function.uncurry fun (x u : ℝ) => ((halfPlanePoisson d x : ℝ) : ℂ) *
      (cx H u * cexp (I * ((γ + x : ℝ) : ℂ) * (u : ℂ)))) (volume.prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => halfPlanePoisson d p.1 * ‖H p.2‖)
        (volume.prod volume) := (integrable_halfPlanePoisson hd).mul_prod hi.norm
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (((Complex.measurable_ofReal.comp
        ((continuous_halfPlanePoisson hd).measurable.comp measurable_fst)).mul
        ((Complex.measurable_ofReal.comp (hm.comp measurable_snd)).mul
          (by fun_prop : Continuous fun p : ℝ × ℝ =>
            cexp (I * ((γ + p.1 : ℝ) : ℂ) * (p.2 : ℂ))).measurable))).aestronglyMeasurable
    · have h1 : I * ((γ + p.1 : ℝ) : ℂ) * (p.2 : ℂ) = (((γ + p.1) * p.2 : ℝ) : ℂ) * I := by
        push_cast
        ring
      show ‖((halfPlanePoisson d p.1 : ℝ) : ℂ) *
        (cx H p.2 * cexp (I * ((γ + p.1 : ℝ) : ℂ) * (p.2 : ℂ)))‖ ≤
          halfPlanePoisson d p.1 * ‖H p.2‖
      rw [norm_mul, norm_mul, h1, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (halfPlanePoisson_pos hd _).le,
        show ‖cx H p.2‖ = ‖H p.2‖ from Complex.norm_real _]
  have hswap := integral_integral_swap hF
  have hinner : ∀ u : ℝ, (∫ x : ℝ, ((halfPlanePoisson d x : ℝ) : ℂ) *
      (cx H u * cexp (I * ((γ + x : ℝ) : ℂ) * (u : ℂ)))) =
      cexp (((d : ℂ) + (γ : ℂ) * I) * (u : ℂ)) * cx H u := by
    intro u
    have e : ∀ x : ℝ, ((halfPlanePoisson d x : ℝ) : ℂ) *
        (cx H u * cexp (I * ((γ + x : ℝ) : ℂ) * (u : ℂ))) =
        (cx H u * cexp (I * (γ : ℂ) * (u : ℂ))) *
          (((halfPlanePoisson d x : ℝ) : ℂ) * cexp (I * (x : ℂ) * (u : ℂ))) := by
      intro x
      have h1 : I * ((γ + x : ℝ) : ℂ) * (u : ℂ) =
          I * (γ : ℂ) * (u : ℂ) + I * (x : ℂ) * (u : ℂ) := by
        push_cast
        ring
      rw [h1, Complex.exp_add]
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_halfPlanePoisson_mul_cexp hd u]
    rcases le_or_gt 0 u with hu | hu
    · have h0 : cx H u = 0 := by simp only [cx, hs u hu, Complex.ofReal_zero]
      rw [h0]
      ring
    · have e2 : cexp (((d : ℂ) + (γ : ℂ) * I) * (u : ℂ)) =
          cexp (I * (γ : ℂ) * (u : ℂ)) * ((Real.exp (-(d * |u|)) : ℝ) : ℂ) := by
        rw [abs_of_neg hu, Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [e2]
      ring
  calc negativeHalfLineLaplace (cx H) ((d : ℂ) + (γ : ℂ) * I)
      = ∫ u : ℝ, ∫ x : ℝ, ((halfPlanePoisson d x : ℝ) : ℂ) *
          (cx H u * cexp (I * ((γ + x : ℝ) : ℂ) * (u : ℂ))) :=
        (integral_congr_ae (Eventually.of_forall fun u => hinner u)).symm
    _ = ∫ x : ℝ, ∫ u : ℝ, ((halfPlanePoisson d x : ℝ) : ℂ) *
          (cx H u * cexp (I * ((γ + x : ℝ) : ℂ) * (u : ℂ))) := hswap.symm
    _ = ∫ x : ℝ, ((halfPlanePoisson d x : ℝ) : ℂ) * paperFT (cx H) ((γ + x : ℝ) : ℂ) :=
        integral_congr_ae (Eventually.of_forall fun x => integral_const_mul _ _)

/-! ### Jensen's inequality for the Poisson average -/

theorem integrable_norm_sq_paperFT_cx {H : ℝ → ℝ} (hi : Integrable H)
    (h2 : Integrable fun u => H u ^ 2) : Integrable fun t : ℝ => ‖paperFT (cx H) (t : ℂ)‖ ^ 2 :=
  KernelStrip.integrable_norm_sq_paperFT (hi.ofReal (𝕜 := ℂ)) (memLp_cx_of_sq hi h2)

/-- `|L H(d + iγ)|² ≤ ∫ P_d(x) |L H(i(γ + x))|² dx`. -/
theorem norm_sq_laplace_le_integral_halfPlanePoisson {H : ℝ → ℝ} (hm : Measurable H)
    (hi : Integrable H) (hs : ∀ u, 0 ≤ u → H u = 0) {d : ℝ} (hd : 0 < d) (γ : ℝ) :
    ‖negativeHalfLineLaplace (cx H) ((d : ℂ) + (γ : ℂ) * I)‖ ^ 2 ≤
      ∫ x : ℝ, halfPlanePoisson d x * ‖paperFT (cx H) ((γ + x : ℝ) : ℂ)‖ ^ 2 := by
  rw [laplace_eq_integral_halfPlanePoisson_mul_paperFT hm hi hs hd γ]
  have hBc : Continuous fun x : ℝ => paperFT (cx H) ((γ + x : ℝ) : ℂ) :=
    (continuous_paperFT_cx hi).comp (continuous_const.add continuous_id)
  have hP := integrable_halfPlanePoisson hd
  have hPc := continuous_halfPlanePoisson hd
  have hP0 : ∀ x, 0 ≤ halfPlanePoisson d x := fun x => (halfPlanePoisson_pos hd x).le
  have hwg2 : Integrable fun x : ℝ =>
      halfPlanePoisson d x * ‖paperFT (cx H) ((γ + x : ℝ) : ℂ)‖ ^ 2 := by
    refine (hP.mul_const ((∫ u, ‖H u‖) ^ 2)).mono'
      (hPc.mul (hBc.norm.pow 2)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hP0 x) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_paperFT_le H (γ + x)) 2) (hP0 x)
  have h1 : ‖∫ x : ℝ, ((halfPlanePoisson d x : ℝ) : ℂ) * paperFT (cx H) ((γ + x : ℝ) : ℂ)‖ ≤
      ∫ x : ℝ, halfPlanePoisson d x * ‖paperFT (cx H) ((γ + x : ℝ) : ℂ)‖ := by
    refine (norm_integral_le_integral_norm _).trans
      (le_of_eq (integral_congr_ae (Eventually.of_forall fun x => ?_)))
    show ‖((halfPlanePoisson d x : ℝ) : ℂ) * paperFT (cx H) ((γ + x : ℝ) : ℂ)‖ =
      halfPlanePoisson d x * ‖paperFT (cx H) ((γ + x : ℝ) : ℂ)‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hP0 x)]
  have h2 := sq_integral_weighted_le (μ := volume) (w := halfPlanePoisson d)
    (g := fun x => ‖paperFT (cx H) ((γ + x : ℝ) : ℂ)‖) hP0 hPc.aestronglyMeasurable
    hBc.norm.aestronglyMeasurable hP hwg2
  rw [integral_halfPlanePoisson hd, one_mul] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-! ### Unit depth: the Lorentzian kernel -/

theorem halfPlanePoisson_le_lorentz {d : ℝ} (hd1 : 1 / 2 ≤ d) (hd2 : d ≤ 3 / 2) (τ : ℝ) :
    halfPlanePoisson d τ ≤ 2 / Real.pi * (1 + τ ^ 2)⁻¹ := by
  have hd0 : 0 < d := by linarith
  have hπ := Real.pi_pos
  have h1 : (0 : ℝ) < 1 + τ ^ 2 := by positivity
  have hD : (0 : ℝ) < d ^ (2 : ℕ) + τ ^ (2 : ℕ) := by positivity
  have key : d * (1 + τ ^ 2) ≤ 2 * (d ^ (2 : ℕ) + τ ^ (2 : ℕ)) := by
    nlinarith [mul_nonneg hd0.le (by linarith : (0 : ℝ) ≤ 2 * d - 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - d) (sq_nonneg τ)]
  unfold halfPlanePoisson
  rw [← div_eq_mul_inv, ← div_mul_eq_div_div, div_le_div_iff₀ (mul_pos hπ hD) (mul_pos hπ h1)]
  have := mul_le_mul_of_nonneg_left key hπ.le
  linarith

theorem integrable_lorentz_mul_norm_sq_paperFT {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H)
    (γ : ℝ) : Integrable fun t : ℝ => (1 + (t - γ) ^ 2)⁻¹ * ‖paperFT (cx H) (t : ℂ)‖ ^ 2 := by
  have hB2 := integrable_norm_sq_paperFT_cx hH.integrable hH.sq
  have hBc := continuous_paperFT_cx hH.integrable
  refine hB2.mono' ((measurable_const.add ((measurable_id.sub_const γ).pow_const 2)).inv.mul
    (hBc.measurable.norm.pow_const 2)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have h1 : (1 + (t - γ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (t - γ)])
  have h0 : 0 ≤ (1 + (t - γ) ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
  exact (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)).trans_eq (one_mul _)

/-- At depth `1/2 ≤ d ≤ 3/2` the value `|L H(d + iγ)|²` is at most a Lorentzian average of the
boundary energy density around `γ`. -/
theorem norm_sq_laplace_le_integral_lorentz {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H)
    {d : ℝ} (hd1 : 1 / 2 ≤ d) (hd2 : d ≤ 3 / 2) (γ : ℝ) :
    ‖negativeHalfLineLaplace (cx H) ((d : ℂ) + (γ : ℂ) * I)‖ ^ 2 ≤
      2 / Real.pi * ∫ t : ℝ, (1 + (t - γ) ^ 2)⁻¹ * ‖paperFT (cx H) (t : ℂ)‖ ^ 2 := by
  have hd : 0 < d := by linarith
  have h1 := norm_sq_laplace_le_integral_halfPlanePoisson hH.meas hH.integrable hH.support hd γ
  have htr : (∫ x : ℝ, halfPlanePoisson d x * ‖paperFT (cx H) ((γ + x : ℝ) : ℂ)‖ ^ 2) =
      ∫ t : ℝ, halfPlanePoisson d (t - γ) * ‖paperFT (cx H) (t : ℂ)‖ ^ 2 := by
    rw [← integral_sub_right_eq_self
      (fun x : ℝ => halfPlanePoisson d x * ‖paperFT (cx H) ((γ + x : ℝ) : ℂ)‖ ^ 2) γ]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show halfPlanePoisson d (t - γ) * ‖paperFT (cx H) ((γ + (t - γ) : ℝ) : ℂ)‖ ^ 2 = _
    rw [add_sub_cancel]
  have hLi := integrable_lorentz_mul_norm_sq_paperFT hH γ
  have hle : (∫ t : ℝ, halfPlanePoisson d (t - γ) * ‖paperFT (cx H) (t : ℂ)‖ ^ 2) ≤
      ∫ t : ℝ, 2 / Real.pi * ((1 + (t - γ) ^ 2)⁻¹ * ‖paperFT (cx H) (t : ℂ)‖ ^ 2) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => ?_) (hLi.const_mul _)
      (Eventually.of_forall fun t => ?_)
    · exact mul_nonneg (halfPlanePoisson_pos hd _).le (sq_nonneg _)
    · show halfPlanePoisson d (t - γ) * ‖paperFT (cx H) (t : ℂ)‖ ^ 2 ≤
        2 / Real.pi * ((1 + (t - γ) ^ 2)⁻¹ * ‖paperFT (cx H) (t : ℂ)‖ ^ 2)
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (halfPlanePoisson_le_lorentz hd1 hd2 _) (sq_nonneg _)
  rw [integral_const_mul] at hle
  exact h1.trans (htr.le.trans hle)

/-! ### The Lorentzian zero mass and the Gamma bracket -/

theorem inv_one_add_sq_eq_lorentzMassTerm {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (t : ℝ)
    (q : XiZeroCopy) :
    (1 + (t - ε * (q.1 : ℂ).im) ^ 2)⁻¹ = lorentzMassTerm (ε * t) q := by
  unfold lorentzMassTerm
  rw [one_div]
  congr 2
  rcases hε with rfl | rfl <;> ring

/-- The logarithmic weight of the zero density is paid by the Gamma energy of the domain. -/
theorem integrable_log_mul_norm_sq_paperFT {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H) :
    Integrable fun t : ℝ => (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
      ‖paperFT (cx H) (t : ℂ)‖ ^ 2 := by
  have hB2 := integrable_norm_sq_paperFT_cx hH.integrable hH.sq
  have hBc := continuous_paperFT_cx hH.integrable
  have hdom : Integrable fun t : ℝ =>
      (xiLineTwoLogDerivConstant + Real.log 2 + 10 + Real.log 4) * ‖paperFT (cx H) (t : ℂ)‖ ^ 2 +
        ‖paperFT (cx H) (t : ℂ)‖ ^ 2 * EF.gammaBracket t := (hB2.const_mul _).add hH.gamma
  refine hdom.mono' ((measurable_const.add (Real.measurable_log.comp
    (continuous_abs.measurable.add_const 4))).mul
      (hBc.measurable.norm.pow_const 2)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hlog0 : 0 ≤ Real.log (|t| + 4) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog : Real.log (|t| + 4) ≤ Real.log 2 + 10 + Real.log 4 + EF.gammaBracket t := by
    have h1 : Real.log (|t| + 4) ≤ Real.log (2 * (2 + |t|)) :=
      Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
    rw [Real.log_mul (by norm_num) (by positivity)] at h1
    linarith [WeilWorkPBAP.joint_gamma_lower_log t]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (add_nonneg xiLineTwoLogDerivConstant_nonneg hlog0) (sq_nonneg _))]
  nlinarith [mul_le_mul_of_nonneg_right hlog (sq_nonneg ‖paperFT (cx H) (t : ℂ)‖)]

/-! ### Sampling on the zero set -/

/-- **Sampling on the zero set**, finite form. -/
theorem sum_norm_sq_laplace_zeros_le {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (w : XiZeroCopy → ℂ) (hre1 : ∀ q, 1 / 2 ≤ (w q).re)
    (hre2 : ∀ q, (w q).re ≤ 3 / 2) (him : ∀ q, (w q).im = ε * (q.1 : ℂ).im)
    (S : Finset XiZeroCopy) :
    ∑ q ∈ S, ‖negativeHalfLineLaplace (cx H) (w q)‖ ^ 2 ≤
      16 / Real.pi * ∫ t : ℝ, (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
        ‖paperFT (cx H) (t : ℂ)‖ ^ 2 := by
  have hterm : ∀ q, ‖negativeHalfLineLaplace (cx H) (w q)‖ ^ 2 ≤
      2 / Real.pi * ∫ t : ℝ, lorentzMassTerm (ε * t) q * ‖paperFT (cx H) (t : ℂ)‖ ^ 2 := by
    intro q
    have h := norm_sq_laplace_le_integral_lorentz hH (hre1 q) (hre2 q) (w q).im
    rw [Complex.re_add_im, him q] at h
    simpa only [inv_one_add_sq_eq_lorentzMassTerm hε] using h
  have hLi : ∀ q, Integrable fun t : ℝ =>
      lorentzMassTerm (ε * t) q * ‖paperFT (cx H) (t : ℂ)‖ ^ 2 := by
    intro q
    have h := integrable_lorentz_mul_norm_sq_paperFT hH (ε * (q.1 : ℂ).im)
    simpa only [inv_one_add_sq_eq_lorentzMassTerm hε] using h
  have hlog := integrable_log_mul_norm_sq_paperFT hH
  have hpt : ∀ t : ℝ, ∑ q ∈ S, lorentzMassTerm (ε * t) q * ‖paperFT (cx H) (t : ℂ)‖ ^ 2 ≤
      8 * ((xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
        ‖paperFT (cx H) (t : ℂ)‖ ^ 2) := by
    intro t
    rw [← Finset.sum_mul]
    have h1 : ∑ q ∈ S, lorentzMassTerm (ε * t) q ≤ lorentzMass (ε * t) :=
      (summable_lorentzMassTerm (ε * t)).sum_le_tsum S fun q _ => lorentzMassTerm_nonneg _ q
    have h2 := lorentzMass_le_log (ε * t)
    have habs : |ε * t| = |t| := by
      rcases hε with rfl | rfl
      · rw [one_mul]
      · rw [neg_one_mul, abs_neg]
    rw [habs] at h2
    calc (∑ q ∈ S, lorentzMassTerm (ε * t) q) * ‖paperFT (cx H) (t : ℂ)‖ ^ 2
        ≤ (8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4))) *
            ‖paperFT (cx H) (t : ℂ)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg _)
      _ = 8 * ((xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
            ‖paperFT (cx H) (t : ℂ)‖ ^ 2) := by ring
  calc ∑ q ∈ S, ‖negativeHalfLineLaplace (cx H) (w q)‖ ^ 2
      ≤ ∑ q ∈ S, 2 / Real.pi *
          ∫ t : ℝ, lorentzMassTerm (ε * t) q * ‖paperFT (cx H) (t : ℂ)‖ ^ 2 :=
        Finset.sum_le_sum fun q _ => hterm q
    _ = 2 / Real.pi *
          ∫ t : ℝ, ∑ q ∈ S, lorentzMassTerm (ε * t) q * ‖paperFT (cx H) (t : ℂ)‖ ^ 2 := by
        rw [← Finset.mul_sum, integral_finsetSum S fun q _ => hLi q]
    _ ≤ 2 / Real.pi * ∫ t : ℝ, 8 * ((xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
          ‖paperFT (cx H) (t : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (integral_mono (integrable_finsetSum S fun q _ => hLi q)
          (hlog.const_mul 8) hpt) (by positivity)
    _ = 16 / Real.pi * ∫ t : ℝ, (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
          ‖paperFT (cx H) (t : ℂ)‖ ^ 2 := by
        rw [integral_const_mul]
        ring

/-- **The energy norm controls the values at the zeros.** The transform of a profile of the
domain is square-summable over the zeros at unit depth. -/
theorem summable_norm_sq_laplace_zeros {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (w : XiZeroCopy → ℂ) (hre1 : ∀ q, 1 / 2 ≤ (w q).re)
    (hre2 : ∀ q, (w q).re ≤ 3 / 2) (him : ∀ q, (w q).im = ε * (q.1 : ℂ).im) :
    Summable fun q : XiZeroCopy => ‖negativeHalfLineLaplace (cx H) (w q)‖ ^ 2 :=
  summable_of_sum_le (fun _ => sq_nonneg _) (sum_norm_sq_laplace_zeros_le hH hε w hre1 hre2 him)

theorem tsum_norm_sq_laplace_zeros_le {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (w : XiZeroCopy → ℂ) (hre1 : ∀ q, 1 / 2 ≤ (w q).re)
    (hre2 : ∀ q, (w q).re ≤ 3 / 2) (him : ∀ q, (w q).im = ε * (q.1 : ℂ).im) :
    ∑' q : XiZeroCopy, ‖negativeHalfLineLaplace (cx H) (w q)‖ ^ 2 ≤
      16 / Real.pi * ∫ t : ℝ, (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
        ‖paperFT (cx H) (t : ℂ)‖ ^ 2 :=
  Real.tsum_le_of_sum_le (fun _ => sq_nonneg _)
    (sum_norm_sq_laplace_zeros_le hH hε w hre1 hre2 him)

/-! ### Profiles with a unit tilt in the domain -/

/-- A tilt of the profile is a shift of the transform. -/
theorem laplace_eq_laplace_exp_mul (G : ℝ → ℝ) (c : ℝ) (z : ℂ) :
    negativeHalfLineLaplace (cx G) z =
      negativeHalfLineLaplace (cx fun u => Real.exp (-(c * u)) * G u) (z + (c : ℂ)) := by
  unfold negativeHalfLineLaplace
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show cexp (z * (u : ℂ)) * ((G u : ℝ) : ℂ) =
    cexp ((z + (c : ℂ)) * (u : ℂ)) * ((Real.exp (-(c * u)) * G u : ℝ) : ℂ)
  rw [Complex.ofReal_mul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem im_centredZero (q : XiZeroCopy) : (centredZero q).im = (q.1 : ℂ).im := by
  simp [centredZero]

/-- The values at the centred zeros of a profile whose unit tilt lies in the domain are
square-summable. -/
theorem summable_norm_sq_laplace_centredZero {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain (fun u => Real.exp (-(1 * u)) * G u)) :
    Summable fun q : XiZeroCopy => ‖negativeHalfLineLaplace (cx G) (centredZero q)‖ ^ 2 := by
  have h := summable_norm_sq_laplace_zeros hG (ε := 1) (Or.inl rfl)
    (fun q => centredZero q + ((1 : ℝ) : ℂ))
    (fun q => by
      have := abs_lt.mp (abs_re_centredZero_lt q)
      rw [Complex.add_re, Complex.ofReal_re]
      linarith [this.1])
    (fun q => by
      have := abs_lt.mp (abs_re_centredZero_lt q)
      rw [Complex.add_re, Complex.ofReal_re]
      linarith [this.2])
    (fun q => by rw [Complex.add_im, Complex.ofReal_im, add_zero, im_centredZero, one_mul])
  refine h.congr fun q => ?_
  rw [laplace_eq_laplace_exp_mul G 1 (centredZero q)]

/-- The same at the reflected points `-z`. -/
theorem summable_norm_sq_laplace_neg_centredZero {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain (fun u => Real.exp (-(1 * u)) * G u)) :
    Summable fun q : XiZeroCopy => ‖negativeHalfLineLaplace (cx G) (-centredZero q)‖ ^ 2 := by
  have h := summable_norm_sq_laplace_zeros hG (ε := -1) (Or.inr rfl)
    (fun q => -centredZero q + ((1 : ℝ) : ℂ))
    (fun q => by
      have := abs_lt.mp (abs_re_centredZero_lt q)
      rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
      linarith [this.2])
    (fun q => by
      have := abs_lt.mp (abs_re_centredZero_lt q)
      rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
      linarith [this.1])
    (fun q => by
      rw [Complex.add_im, Complex.neg_im, Complex.ofReal_im, add_zero, im_centredZero,
        neg_one_mul])
  refine h.congr fun q => ?_
  rw [laplace_eq_laplace_exp_mul G 1 (-centredZero q)]

end GaloisForLFunctions.ExclusionOfTheCriticalState
