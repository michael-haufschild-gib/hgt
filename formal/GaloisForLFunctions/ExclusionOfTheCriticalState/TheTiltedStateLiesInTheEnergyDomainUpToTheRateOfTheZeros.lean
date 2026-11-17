import GaloisForLFunctions.ExclusionOfTheCriticalState.TheMomentsOfTheStateHaveAPoleAtTheExponentOfEveryZero
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroPairingOfTheStateConvergesAbsolutely

/-!
# The tilted state lies in the energy domain up to the rate of the zeros

Let `F` be the critical state and `Θ` the supremum of the real parts of the zeros of `ζ`. The
tilted profile `e^{-cu} F` lies in the energy domain for every `c < 9/2 - Θ`
(`criticalHalfLineEnergyDomain_exp_mul_groundState_of_lt`), and `9/2 - Θ` is the supremum of such
tilts (`isLUB_tilt_mem_energyDomain`); when `Θ` is attained the tilt lies in the domain exactly for
`c < 9/2 - Θ`. In centred zeros: every `Re z ≤ κ` iff all tilts `c < 4 - κ` lie in the domain
(`forall_re_centredZero_le_iff_tilt_mem_energyDomain`). This is the decay law in the energy norm:
not only the square moments but the Gamma energy survives every weight below the rate of the zeros.

Consequences. The transform has finite logarithmic energy `∫ log(|t| + 4) |L F(s + it)|² dt` on
every line `Re w = s > Θ - 9/2` (`integrable_log_mul_norm_sq_laplace_line_of_lt`). The tilts are
admissible tests of the weak equation: for `c < 7/2 - Θ` the values `L F(z - c)` at the shifted
zeros are square-summable and

  `Σ_z L F(z) L F(-z - c) = -a ∫ F² e^{-(8 + c)u} du`,

absolutely convergent (`criticalState_hasSum_shifted_zeroPairing`): the square moments of the state
are zero pairings of its transform with its shifts, and `c = 0` is the one-point identity of the
state.

Mechanism (Agmon at the rate of the zeros). For the truncated weight `φ = e^{-c max(u, -N)}` the
jump energy of `φF` is the Gamma pairing of `F` with `φ²F` up to a commutator bounded by the
moment `∫ F² e^{-4cu}`. The weak equation replaces the Gamma pairing by prime and pole terms minus a
confinement term of favourable sign. The backward halves are bounded by moments; the forward halves
combine to the prime-minus-pole wave, bounded by its mass on a line `Re p = s` just right of the
zeros times `∫ F² e^{-(4c + 2s)u}`. Every moment used lies below `16 - 2κ` exactly when
`c < 4 - κ`. Fatou's lemma passes to the limit `N → ∞`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The Agmon bound at the rate of the zeros -/

/-- **The Gamma pairing of the state with its weighted copy is bounded above uniformly in the
truncation.** Let `Re p = s < 1` be a line right of the zeros on which the wave has finite mass
`∫ |N|² |L F|²`, and let `c ≥ 1` with `∫ F² e^{-(4c + 2s)u} < ∞`. The weak equation against
`φ²F`, `φ = e^{-c max(u, -N)}`, replaces the Gamma pairing by prime and pole terms minus a
confinement term of favourable sign. -/
theorem exists_gammaMixedForm_truncatedTilt_le_of_line_mass {κ s c : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκs : κ < s) (hs1 : s < 1)
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (hB : Integrable fun t : ℝ =>
      ‖zetaRegularLogDeriv (1 / 2 + ((s : ℂ) + (t : ℂ) * I))‖ ^ 2 *
        ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2)
    (hc1 : 1 ≤ c) (h4 : Integrable fun u => F u ^ 2 * Real.exp (-(4 * c * u)))
    (hZ : Integrable fun u => F u ^ 2 * Real.exp (-((4 * c + 2 * s) * u))) :
    ∃ K : ℝ, ∀ N : ℝ, gammaMixedForm F (fun u => truncatedTilt (2 * c) N u * F u) ≤ K := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h2c0 : (0 : ℝ) ≤ 2 * c := by linarith
  have h2 : Integrable fun u => F u ^ 2 * Real.exp (-(2 * c * u)) :=
    integrable_sq_mul_exp_of_le hd.meas hd.support h4 (by linarith)
  have hJa : Integrable fun u => |F u| * Real.exp (-(1 * u)) :=
    integrable_abs_mul_exp_neg_of_decay hd.meas hd.support h4 (by linarith)
  have hJ1 : Integrable fun v => |F v| * Real.exp (-((2 * c - 1) * v)) :=
    integrable_abs_mul_exp_neg_of_decay hd.meas hd.support h4 (by linarith)
  have hJ2 : Integrable fun v => |F v| * Real.exp (-((2 * c - 1 / 2) * v)) :=
    integrable_abs_mul_exp_neg_of_decay hd.meas hd.support h4 (by linarith)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
      ‖zetaRegularLogDeriv (1 / 2 + ((s : ℂ) + (t : ℂ) * I))‖ ^ 2 *
        ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (by positivity)
      (integral_nonneg fun t => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hJa0 : 0 ≤ ∫ u, |F u| * Real.exp (-(1 * u)) :=
    integral_nonneg fun u => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  refine ⟨(1 + M * ∫ u, F u ^ 2 * Real.exp (-((4 * c + 2 * s) * u))) / 2 +
    (∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(1 * Real.log n))) *
      (∫ u, F u ^ 2 * Real.exp (-(2 * c * u))) +
    (∫ u, |F u| * Real.exp (-(1 * u))) * (∫ v, |F v| * Real.exp (-((2 * c - 1) * v))) +
    |∫ u, F u * Real.exp (-(u / 2))| * (∫ v, |F v| * Real.exp (-((2 * c - 1 / 2) * v))),
    fun N => ?_⟩
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hd h2c0 N
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = criticalAliasCoefficient W₀ := ⟨_, rfl⟩
  have ha : 0 < a := by
    rw [hadef]
    exact criticalAliasCoefficient_positive hW
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ,
      Y = ∫ u, truncatedTilt (2 * c) N u * (F u ^ 2 * Real.exp (-(8 * u))) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by
    rw [hYdef]
    exact integral_nonneg fun u => mul_nonneg (truncatedTilt_pos _ _ _).le
      (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have haY : 0 ≤ a * Y := mul_nonneg ha.le hY0
  -- the weak equation against the weighted copy
  have hw := criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hG
  unfold criticalHalfLineMixedEnergy at hw
  rw [primeMixedForm_symm (fun u => truncatedTilt (2 * c) N u * F u) F, ← hadef] at hw
  have e1 : (∫ u in Iio (0 : ℝ), F u * (truncatedTilt (2 * c) N u * F u) *
      Real.exp (-(8 * u))) =
      ∫ u, F u * (truncatedTilt (2 * c) N u * F u) * Real.exp (-(8 * u)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      rw [hd.support u (not_lt.mp hu)]
      ring
  have hconf : (∫ u in Iio (0 : ℝ), F u * (truncatedTilt (2 * c) N u * F u) *
      Real.exp (-(8 * u))) = Y := by
    rw [e1, hYdef]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show F u * (truncatedTilt (2 * c) N u * F u) * Real.exp (-(8 * u)) =
      truncatedTilt (2 * c) N u * (F u ^ 2 * Real.exp (-(8 * u)))
    ring
  rw [hconf] at hw
  -- prime and pole terms: forward halves and backward moments
  have hP := primeMixedForm_truncatedTilt_le hd hc1 h2 N
  have hpole := two_cosh_mul_sub_two_sinh_mul hd hG
  have hG1 := integrable_abs_truncatedTilt_mul_mul_exp hd.meas h2c0 N 1 hJ1
  have hGh := integrable_abs_truncatedTilt_mul_mul_exp hd.meas h2c0 N (1 / 2) hJ2
  have hC2 := (abs_expMoment_mul_sub_forwardPoleForm_le hd hG (m := 1) (by norm_num) hJa
    hG1.1).trans (mul_le_mul_of_nonneg_left hG1.2 hJa0)
  have hC2a := (abs_le.mp hC2).1
  have hEp : |∫ v, truncatedTilt (2 * c) N v * F v * Real.exp (v / 2)| ≤
      ∫ v, |F v| * Real.exp (-((2 * c - 1 / 2) * v)) := by
    have h := norm_integral_le_of_norm_le
      (f := fun v : ℝ => truncatedTilt (2 * c) N v * F v * Real.exp (v / 2)) hGh.1
      (Eventually.of_forall fun v => le_of_eq (by
        show ‖truncatedTilt (2 * c) N v * F v * Real.exp (v / 2)‖ =
          |truncatedTilt (2 * c) N v * F v| * Real.exp (1 / 2 * v)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le,
          show v / 2 = 1 / 2 * v by ring]))
    rw [Real.norm_eq_abs] at h
    exact h.trans hGh.2
  have hEm : -(|∫ u, F u * Real.exp (-(u / 2))| *
      ∫ v, |F v| * Real.exp (-((2 * c - 1 / 2) * v))) ≤
      (∫ u, F u * Real.exp (-(u / 2))) *
        ∫ v, truncatedTilt (2 * c) N v * F v * Real.exp (v / 2) := by
    have h1 := neg_abs_le ((∫ u, F u * Real.exp (-(u / 2))) *
      ∫ v, truncatedTilt (2 * c) N v * F v * Real.exp (v / 2))
    rw [abs_mul] at h1
    have h3 := mul_le_mul_of_nonneg_left hEp (abs_nonneg (∫ u, F u * Real.exp (-(u / 2))))
    linarith only [h1, h3]
  -- the forward halves combine to the wave on the line `Re p = s`
  have hD := sq_forwardPrimeForm_sub_forwardPoleForm_le hκ hzero hκs hs1 hd hG hB
  rw [← hMdef] at hD
  have hGZ : (∫ v, (truncatedTilt (2 * c) N v * F v) ^ 2 * Real.exp (-(2 * s * v))) ≤
      ∫ u, F u ^ 2 * Real.exp (-((4 * c + 2 * s) * u)) := by
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun v => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hZ
      (Eventually.of_forall fun v => ?_)
    have hψ := truncatedTilt_le_exp_neg h2c0 N v
    have hψ0 := (truncatedTilt_pos (2 * c) N v).le
    have e : Real.exp (-(2 * c * v)) ^ 2 * Real.exp (-(2 * s * v)) =
        Real.exp (-((4 * c + 2 * s) * v)) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    show (truncatedTilt (2 * c) N v * F v) ^ 2 * Real.exp (-(2 * s * v)) ≤
      F v ^ 2 * Real.exp (-((4 * c + 2 * s) * v))
    calc (truncatedTilt (2 * c) N v * F v) ^ 2 * Real.exp (-(2 * s * v))
        = F v ^ 2 * (truncatedTilt (2 * c) N v ^ 2 * Real.exp (-(2 * s * v))) := by ring
      _ ≤ F v ^ 2 * (Real.exp (-(2 * c * v)) ^ 2 * Real.exp (-(2 * s * v))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ hψ0 hψ 2) (Real.exp_pos _).le) (sq_nonneg _)
      _ = _ := by rw [e]
  have hD' : (forwardPrimeForm F (fun u => truncatedTilt (2 * c) N u * F u) -
      forwardPoleForm F (fun u => truncatedTilt (2 * c) N u * F u)) ^ 2 ≤
        M * ∫ u, F u ^ 2 * Real.exp (-((4 * c + 2 * s) * u)) :=
    hD.trans (mul_le_mul_of_nonneg_left hGZ hM0)
  have hx : forwardPrimeForm F (fun u => truncatedTilt (2 * c) N u * F u) -
      forwardPoleForm F (fun u => truncatedTilt (2 * c) N u * F u) ≤
        (1 + M * ∫ u, F u ^ 2 * Real.exp (-((4 * c + 2 * s) * u))) / 2 := by
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = forwardPrimeForm F (fun u => truncatedTilt (2 * c) N u * F u) -
        forwardPoleForm F (fun u => truncatedTilt (2 * c) N u * F u) := ⟨_, rfl⟩
    rw [← hX] at hD' ⊢
    nlinarith only [sq_nonneg (X - 1), hD']
  linarith only [hw, hpole, hP, hC2a, hEm, hx, haY]

/-- **The Agmon bound at the rate of the zeros.** If every centred zero has `Re z ≤ κ < 1/2`, the
jump energies of the truncated tilts `e^{-c max(u, -N)} F`, `1 ≤ c < 4 - κ`, of the critical state
are bounded uniformly in the truncation. -/
theorem exists_levyEnergy_truncatedTilt_le_of_zero_abscissa {κ : ℝ} (hκ : 0 ≤ κ)
    (hκ2 : κ < 1 / 2) (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ} (hc1 : 1 ≤ c)
    (hc : c < 4 - κ) :
    ∃ K : ℝ, ∀ N : ℝ, (∫ x in Ioi (0 : ℝ), archLevyDensity x *
      ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) ≤ K := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have h2c0 : (0 : ℝ) ≤ 2 * c := by linarith
  have hdec : ∀ b < 16 - 2 * κ, Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) :=
    fun b hb => integrable_sq_mul_exp_of_zero_abscissa_sharp hκ hzero hW hthreshold hF hb
  -- a line `s` just right of the zeros, and an auxiliary line `s + δ` for the mass of the wave
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min ((1 / 2 - κ) / 2) (4 - κ - c) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hεdef]
    exact lt_min (by linarith) (by linarith)
  have hε1 : ε ≤ (1 / 2 - κ) / 2 := by
    rw [hεdef]
    exact min_le_left _ _
  have hε2 : ε ≤ 4 - κ - c := by
    rw [hεdef]
    exact min_le_right _ _
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = κ + ε := ⟨_, rfl⟩
  have hκs : κ < s := by linarith
  have hs2 : s < 1 / 2 := by linarith
  have hs0 : 0 < s := by linarith
  have hsκ : 0 < s * (s - κ) := mul_pos hs0 (by linarith)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min ((1 / 2 - s) / 2) (s * (s - κ)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min (by linarith) hsκ
  have hδ1 : δ ≤ (1 / 2 - s) / 2 := by
    rw [hδdef]
    exact min_le_left _ _
  have hδ2 : δ ≤ s * (s - κ) := by
    rw [hδdef]
    exact min_le_right _ _
  have hstep : (1 / 2 + κ) * (s + δ) < s * (1 / 2 - κ + 2 * (s + δ)) := by
    have h1 : δ * (1 / 2 + κ - 2 * s) ≤ δ * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hδ0.le
    nlinarith only [h1, hδ2, hsκ]
  have hB := integrable_norm_sq_zetaRegularLogDeriv_mul_laplace_of_decay hκ hzero hκs
    (by linarith : s < s + δ) (by linarith : s + δ < 1 / 2) hstep hW hthreshold hF
    (fun b hb => hdec b (by linarith))
  -- moments below the rate of the zeros
  have h4 : Integrable fun u => F u ^ 2 * Real.exp (-(4 * c * u)) := hdec _ (by linarith)
  have h2 : Integrable fun u => F u ^ 2 * Real.exp (-(2 * c * u)) :=
    integrable_sq_mul_exp_of_le hd.meas hd.support h4 (by linarith)
  have hZ : Integrable fun u => F u ^ 2 * Real.exp (-((4 * c + 2 * s) * u)) :=
    hdec _ (by linarith)
  obtain ⟨KΓ, hKΓ⟩ := exists_gammaMixedForm_truncatedTilt_le_of_line_mass hκ hzero hκs
    (by linarith : s < 1) hW hthreshold hF hB hc1 h4 hZ
  refine ⟨KΓ + 2 * |gammaHardyPhaseRate 0| * (∫ u, F u ^ 2 * Real.exp (-(2 * c * u))) +
    (3 * c ^ 2 + 2) * (((∫ u, F u ^ 2 * Real.exp (-(4 * c * u))) + ∫ u, F u ^ 2) / 2) *
      ∫ x in Ioi (0 : ℝ), Real.exp (-(x / 2)), fun N => ?_⟩
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hd h2c0 N
  have hA := hKΓ N
  -- the jump energy is the Gamma pairing up to the commutator and the mass term
  have hlev := levyEnergy_truncatedTilt_sub_levyMixed_le_of_decay hd hc0 h4 N
  have hL := gammaMixedForm_eq_levy hd hG
  have hI0 : 0 ≤ ∫ u, F u * (truncatedTilt (2 * c) N u * F u) :=
    integral_nonneg fun u => mul_truncatedTilt_mul_nonneg (2 * c) N F u
  have hI1 : (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) ≤
      ∫ u, F u ^ 2 * Real.exp (-(2 * c * u)) := by
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun u => mul_truncatedTilt_mul_nonneg (2 * c) N F u) h2
      (Eventually.of_forall fun u => ?_)
    show F u * (truncatedTilt (2 * c) N u * F u) ≤ F u ^ 2 * Real.exp (-(2 * c * u))
    have e : F u * (truncatedTilt (2 * c) N u * F u) = F u ^ 2 * truncatedTilt (2 * c) N u := by
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (truncatedTilt_le_exp_neg h2c0 N u) (sq_nonneg _)
  have hθ1 : -(gammaHardyPhaseRate 0) * (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) ≤
      |gammaHardyPhaseRate 0| * (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) :=
    mul_le_mul_of_nonneg_right (neg_le_abs _) hI0
  have hθ2 : |gammaHardyPhaseRate 0| * (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) ≤
      |gammaHardyPhaseRate 0| * ∫ u, F u ^ 2 * Real.exp (-(2 * c * u)) :=
    mul_le_mul_of_nonneg_left hI1 (abs_nonneg _)
  linarith only [hlev, hL, hA, hθ1, hθ2]

/-! ### From the Agmon bound to the domain -/

/-- **A profile whose truncated tilts have bounded jump energy has its tilt in the domain.** Let
`F` lie in the energy domain with `∫ F² e^{-(8 + 2c)u} < ∞`, `c ≥ 0`. If the jump energies of
`e^{-c max(u, -N)} F` are bounded uniformly in `N`, then `e^{-cu} F` lies in the domain (Fatou in
the lag). -/
theorem criticalHalfLineEnergyDomain_exp_mul_of_levyEnergy_truncatedTilt_le {F : ℝ → ℝ}
    (hd : CriticalHalfLineEnergyDomain F) {c : ℝ} (hc0 : 0 ≤ c)
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-((8 + 2 * c) * u))) {K : ℝ}
    (hK : ∀ N : ℝ, (∫ x in Ioi (0 : ℝ), archLevyDensity x *
      ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) ≤ K) :
    CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c * u)) * F u) := by
  have hmeas : Measurable fun u => Real.exp (-(c * u)) * F u :=
    (by fun_prop : Measurable fun u : ℝ => Real.exp (-(c * u))).mul hd.meas
  have hint : Integrable fun u => Real.exp (-(c * u)) * F u := by
    refine (integrable_abs_mul_exp_neg_of_decay hd.meas hd.support hb
      (by linarith : 2 * c < 8 + 2 * c)).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_comm _ _).le
  have hsq : Integrable fun u => (Real.exp (-(c * u)) * F u) ^ 2 := by
    refine (integrable_sq_mul_exp_of_le hd.meas hd.support hb
      (by linarith : 2 * c ≤ 8 + 2 * c)).congr (Eventually.of_forall fun u => ?_)
    show F u ^ 2 * Real.exp (-(2 * c * u)) = (Real.exp (-(c * u)) * F u) ^ 2
    have e : Real.exp (-(2 * c * u)) = Real.exp (-(c * u)) ^ 2 := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [e]
    ring
  have hexp : Integrable fun u => (Real.exp (-(c * u)) * F u) ^ 2 * Real.exp (-(8 * u)) := by
    refine hb.congr (Eventually.of_forall fun u => ?_)
    show F u ^ 2 * Real.exp (-((8 + 2 * c) * u)) =
      (Real.exp (-(c * u)) * F u) ^ 2 * Real.exp (-(8 * u))
    have e : Real.exp (-((8 + 2 * c) * u)) = Real.exp (-(c * u)) ^ 2 * Real.exp (-(8 * u)) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [e]
    ring
  refine ⟨hmeas, hint, hsq, hexp, fun u hu => by rw [hd.support u hu, mul_zero], ?_⟩
  refine integrable_gamma_of_lintegral_levy_ne_top hint hsq ?_
  -- the truncated tilts converge to the tilt, dominated by it
  have hHN : ∀ N : ℕ, CriticalHalfLineEnergyDomain (fun u => truncatedTilt c N u * F u) :=
    fun N => criticalHalfLineEnergyDomain_truncatedTilt_mul hd hc0 N
  have hpt : ∀ u : ℝ, Tendsto (fun N : ℕ => truncatedTilt c N u * F u) atTop
      (𝓝 (Real.exp (-(c * u)) * F u)) := by
    intro u
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈-u⌉₊] with N hN
    rw [truncatedTilt_eq_exp_neg (by linarith [Nat.ceil_le.mp hN])]
  have hbd : ∀ (N : ℕ) (u : ℝ), (truncatedTilt c N u * F u) ^ 2 ≤
      (Real.exp (-(c * u)) * F u) ^ 2 := fun N u => by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (truncatedTilt_pos c N u).le
      (truncatedTilt_le_exp_neg hc0 N u) 2) (sq_nonneg _)
  have hlim : ∀ x : ℝ, Tendsto (fun N : ℕ => ∫ u,
      (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) atTop
      (𝓝 (∫ u, (Real.exp (-(c * u)) * F u - Real.exp (-(c * (u + x))) * F (u + x)) ^ 2)) := by
    intro x
    refine tendsto_integral_of_dominated_convergence
      (fun u => 2 * (Real.exp (-(c * u)) * F u) ^ 2 +
        2 * (Real.exp (-(c * (u + x))) * F (u + x)) ^ 2) (fun N => ?_) ?_ (fun N => ?_) ?_
    · exact (((hHN N).meas.sub ((hHN N).meas.comp (measurable_id.add_const x))).pow_const
        2).aestronglyMeasurable
    · exact (hsq.const_mul 2).add ((hsq.comp_add_right x).const_mul 2)
    · refine Eventually.of_forall fun u => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hbd N u, hbd N (u + x), sq_nonneg (truncatedTilt c N u * F u +
        truncatedTilt c N (u + x) * F (u + x))]
    · exact Eventually.of_forall fun u => ((hpt u).sub (hpt (u + x))).pow 2
  -- Fatou in the lag
  have hfat : (∫⁻ x in Ioi (0 : ℝ), liminf (fun N : ℕ => ENNReal.ofReal (archLevyDensity x *
      ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2)) atTop) ≤
      liminf (fun N : ℕ => ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x *
        ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2)) atTop :=
    lintegral_liminf_le' (fun N => ENNReal.measurable_ofReal.comp_aemeasurable
      (hHN N).aestronglyMeasurable_levyIntegrand.aemeasurable)
  have hliminf : ∀ x : ℝ, liminf (fun N : ℕ => ENNReal.ofReal (archLevyDensity x *
      ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2)) atTop =
        ENNReal.ofReal (archLevyDensity x *
          ∫ u, (Real.exp (-(c * u)) * F u - Real.exp (-(c * (u + x))) * F (u + x)) ^ 2) :=
    fun x => ((ENNReal.continuous_ofReal.tendsto _).comp
      ((hlim x).const_mul (archLevyDensity x))).liminf_eq
  have hEq : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x *
      ∫ u, (Real.exp (-(c * u)) * F u - Real.exp (-(c * (u + x))) * F (u + x)) ^ 2)) =
      ∫⁻ x in Ioi (0 : ℝ), liminf (fun N : ℕ => ENNReal.ofReal (archLevyDensity x *
        ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2)) atTop :=
    lintegral_congr fun x => (hliminf x).symm
  have hN : ∀ N : ℕ, (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x *
      ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2)) ≤
        ENNReal.ofReal K := fun N => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hHN N).integrableOn_levyIntegrand
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx =>
        mul_nonneg (archLevyDensity_pos hx).le (integral_nonneg fun u => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hK N)
  exact ((hEq.le.trans (hfat.trans (liminf_le_of_frequently_le'
    (Frequently.of_forall hN)))).trans_lt ENNReal.ofReal_lt_top).ne

/-! ### The decay law in the energy norm -/

/-- **The tilted state lies in the energy domain up to the rate of the zeros.** If every centred
zero has `Re z ≤ κ`, then `e^{-cu} F` lies in the energy domain for every `c < 4 - κ`. -/
theorem criticalHalfLineEnergyDomain_exp_mul_groundState_of_zero_abscissa {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ} (hc : c < 4 - κ) :
    CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c * u)) * F u) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  rcases le_total c 0 with hc0 | hc0
  · -- a damped copy of the state
    have e : (fun u => Real.exp (-(c * u)) * F u) =
        fun u => Real.exp (-c * min u 0) * F u := by
      funext u
      rcases le_or_gt 0 u with hu | hu
      · rw [hd.support u hu, mul_zero, mul_zero]
      · rw [min_eq_left hu.le, neg_mul]
    rw [e]
    exact criticalHalfLineEnergyDomain_exp_min_mul hd (by linarith)
  rcases le_total c 1 with hc1 | hc1
  · exact criticalHalfLineEnergyDomain_exp_mul_groundState hW hthreshold hF hc0 hc1
  -- beyond the unit tilt: the Agmon bound at the rate of the zeros
  have hκ' : (0 : ℝ) ≤ min κ (8999 / 24000) := le_min hκ (by norm_num)
  have hzero' : ∀ q : XiZeroCopy, (centredZero q).re ≤ min κ (8999 / 24000) := fun q =>
    le_min (hzero q) (re_centredZero_le_seed q)
  have hcκ : c < 4 - min κ (8999 / 24000) := by
    linarith [min_le_left κ (8999 / 24000 : ℝ)]
  obtain ⟨K, hK⟩ := exists_levyEnergy_truncatedTilt_le_of_zero_abscissa hκ'
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) hzero' hW hthreshold hF hc1 hcκ
  exact criticalHalfLineEnergyDomain_exp_mul_of_levyEnergy_truncatedTilt_le hd hc0
    (integrable_sq_mul_exp_of_zero_abscissa_sharp hκ hzero hW hthreshold hF (by linarith)) hK

/-- The tilt `e^{-cu} F` of the critical state lies in the energy domain for `c < 9/2 - Θ`. -/
theorem criticalHalfLineEnergyDomain_exp_mul_groundState_of_lt {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ}
    (hc : c < 9 / 2 - zetaZeroAbscissa) :
    CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c * u)) * F u) := by
  refine criticalHalfLineEnergyDomain_exp_mul_groundState_of_zero_abscissa
    (κ := zetaZeroAbscissa - 1 / 2) (by linarith [half_le_zetaZeroAbscissa]) (fun q => ?_)
    hW hthreshold hF (by linarith)
  have h3 : (centredZero q).re = ((q.1 : ℂ)).re - 1 / 2 := by simp [centredZero]
  have h := re_le_zetaZeroAbscissa (riemannZeta_xiZeroCopy_eq_zero q)
  rw [h3]
  linarith

/-- A tilt in the energy domain carries the square moment `∫ F² e^{-(8 + 2c)u}`. -/
theorem integrable_sq_mul_exp_of_tilt_mem_energyDomain {F : ℝ → ℝ} {c : ℝ}
    (hG : CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c * u)) * F u)) :
    Integrable fun u => F u ^ 2 * Real.exp (-((8 + 2 * c) * u)) := by
  refine hG.exponential.congr (Eventually.of_forall fun u => ?_)
  show (Real.exp (-(c * u)) * F u) ^ 2 * Real.exp (-(8 * u)) =
    F u ^ 2 * Real.exp (-((8 + 2 * c) * u))
  have e : Real.exp (-((8 + 2 * c) * u)) = Real.exp (-(c * u)) ^ 2 * Real.exp (-(8 * u)) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e]
  ring

/-- **The tilts are a ruler for the zeros.** If `e^{-cu} F` lies in the energy domain, every zero
of `ζ` right of the critical line satisfies `Re ρ < 9/2 - c`. -/
theorem zero_re_lt_of_tilt_mem_energyDomain {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ}
    (hG : CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c * u)) * F u)) {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (hρ : 1 / 2 < ρ.re) : ρ.re < 9 / 2 - c := by
  have h := zero_re_lt_of_integrable_sq_mul_exp hW hthreshold hF
    (integrable_sq_mul_exp_of_tilt_mem_energyDomain hG) hζ hρ
  linarith

/-- **The decay law in the energy norm.** For `κ ≥ 0`, every centred zero has `Re z ≤ κ` if and
only if every tilt `e^{-cu} F`, `c < 4 - κ`, of the critical state lies in the energy domain. -/
theorem forall_re_centredZero_le_iff_tilt_mem_energyDomain {κ : ℝ} (hκ : 0 ≤ κ) {W₀ : ℝ}
    (hW : 0 < W₀) (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    (∀ q : XiZeroCopy, (centredZero q).re ≤ κ) ↔
      ∀ c < 4 - κ, CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c * u)) * F u) := by
  refine ⟨fun hzero c hc =>
    criticalHalfLineEnergyDomain_exp_mul_groundState_of_zero_abscissa hκ hzero hW hthreshold hF hc,
    fun htilt q => ?_⟩
  by_contra hq
  have hlt : κ < (centredZero q).re := not_le.mp hq
  have h3 : (centredZero q).re = ((q.1 : ℂ)).re - 1 / 2 := by simp [centredZero]
  have h := zero_re_lt_of_tilt_mem_energyDomain hW hthreshold hF
    (htilt (4 - (κ + (centredZero q).re) / 2) (by linarith))
    (riemannZeta_xiZeroCopy_eq_zero q) (by linarith)
  linarith

/-- **The energy threshold of the tilts is `9/2 - Θ`**: the exponents `c` with `e^{-cu} F` in
the energy domain have supremum `9/2 - Θ`. -/
theorem isLUB_tilt_mem_energyDomain {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    IsLUB {c : ℝ | CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c * u)) * F u)}
      (9 / 2 - zetaZeroAbscissa) := by
  constructor
  · intro c hc
    have h := (isLUB_integrable_sq_mul_exp hW hthreshold hF).1
      (integrable_sq_mul_exp_of_tilt_mem_energyDomain hc)
    linarith
  · intro d hd
    by_contra hlt
    have hlt' : d < 9 / 2 - zetaZeroAbscissa := not_le.mp hlt
    have hmem : (d + (9 / 2 - zetaZeroAbscissa)) / 2 ∈
        {c : ℝ | CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c * u)) * F u)} :=
      criticalHalfLineEnergyDomain_exp_mul_groundState_of_lt hW hthreshold hF (by linarith)
    have hle := hd hmem
    linarith

/-- **When the abscissa of the zeros is attained, the tilts of the domain are exactly those below
the threshold**: if some zero has `Re ρ = Θ`, then `e^{-cu} F` lies in the energy domain iff
`c < 9/2 - Θ`. -/
theorem tilt_mem_energyDomain_iff_of_attained {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hΘ : ρ.re = zetaZeroAbscissa) (c : ℝ) :
    CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c * u)) * F u) ↔
      c < 9 / 2 - zetaZeroAbscissa := by
  refine ⟨fun hG => ?_, fun hc =>
    criticalHalfLineEnergyDomain_exp_mul_groundState_of_lt hW hthreshold hF hc⟩
  have h := (integrable_sq_mul_exp_iff_of_attained hW hthreshold hF hζ hΘ (8 + 2 * c)).mp
    (integrable_sq_mul_exp_of_tilt_mem_energyDomain hG)
  linarith

/-! ### The transform on the lines left of the axis -/

/-- The tilt `e^{-cu} F` shifts the transform. -/
theorem laplace_exp_neg_mul (F : ℝ → ℝ) (c : ℝ) (z : ℂ) :
    negativeHalfLineLaplace (cx fun u => Real.exp (-(c * u)) * F u) z =
      negativeHalfLineLaplace (cx F) (z - (c : ℂ)) := by
  show (∫ u : ℝ, cexp (z * (u : ℂ)) * cx (fun u => Real.exp (-(c * u)) * F u) u) =
    ∫ u : ℝ, cexp ((z - (c : ℂ)) * (u : ℂ)) * cx F u
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show cexp (z * (u : ℂ)) * ((Real.exp (-(c * u)) * F u : ℝ) : ℂ) =
    cexp ((z - (c : ℂ)) * (u : ℂ)) * ((F u : ℝ) : ℂ)
  have e : (z - (c : ℂ)) * (u : ℂ) = z * (u : ℂ) + ((-(c * u) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_exp]
  ring

/-- **One logarithm on every line right of `Θ - 9/2`.** The transform of the critical state has
finite logarithmic energy `∫ log(|t| + 4) |L F(s + it)|² dt` for every `s > Θ - 9/2`. -/
theorem integrable_log_mul_norm_sq_laplace_line_of_lt {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {s : ℝ}
    (hs : zetaZeroAbscissa - 9 / 2 < s) :
    Integrable fun t : ℝ => Real.log (|t| + 4) *
      ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hG := criticalHalfLineEnergyDomain_exp_mul_groundState_of_lt hW hthreshold hF
    (c := -s) (by linarith)
  refine (integrable_log_mul_norm_sq_laplace_line hG (σ := 0) le_rfl).congr
    (Eventually.of_forall fun t => ?_)
  show Real.log (|t| + 4) * ‖negativeHalfLineLaplace (cx fun u => Real.exp (-(-s * u)) * F u)
    (((0 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 = Real.log (|t| + 4) *
      ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2
  have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I - ((-s : ℝ) : ℂ) = (s : ℂ) + (t : ℂ) * I := by
    push_cast
    ring
  rw [laplace_exp_neg_mul, e]

/-! ### The moments as zero pairings -/

/-- The unit tilt of `e^{-cu} F` lies in the energy domain for `c < 7/2 - Θ`. -/
theorem criticalHalfLineEnergyDomain_unitTilt_exp_mul_groundState {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ}
    (hc : c < 7 / 2 - zetaZeroAbscissa) :
    CriticalHalfLineEnergyDomain
      (fun u => Real.exp (-(1 * u)) * (Real.exp (-(c * u)) * F u)) := by
  have e : (fun u => Real.exp (-(1 * u)) * (Real.exp (-(c * u)) * F u)) =
      fun u => Real.exp (-((c + 1) * u)) * F u := by
    funext u
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [e]
  exact criticalHalfLineEnergyDomain_exp_mul_groundState_of_lt hW hthreshold hF (by linarith)

/-- **The values of the transform at the shifted zeros are square-summable**:
`Σ_z |L F(z - c)|² < ∞` for every `c < 7/2 - Θ`. -/
theorem criticalState_summable_norm_sq_shifted_zeroValues {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ}
    (hc : c < 7 / 2 - zetaZeroAbscissa) :
    Summable fun q : XiZeroCopy =>
      ‖negativeHalfLineLaplace (cx F) (centredZero q - (c : ℂ))‖ ^ 2 := by
  have h := summable_norm_sq_laplace_centredZero
    (criticalHalfLineEnergyDomain_unitTilt_exp_mul_groundState hW hthreshold hF hc)
  simpa only [laplace_exp_neg_mul] using h

/-- **The square moments of the state are zero pairings of its transform with its shifts.** For
`c < 7/2 - Θ`,

  `Σ_z L F(z) L F(-z - c) = -a ∫ F² e^{-(8 + c)u} du`,

absolutely convergent: the weak equation of the state against its own tilt. -/
theorem criticalState_hasSum_shifted_zeroPairing {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ}
    (hc : c < 7 / 2 - zetaZeroAbscissa) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q - (c : ℂ)))
      (-((criticalAliasCoefficient W₀ : ℂ) *
        ((∫ u, F u ^ 2 * Real.exp (-((8 + c) * u)) : ℝ) : ℂ))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hG := criticalHalfLineEnergyDomain_exp_mul_groundState_of_lt hW hthreshold hF
    (c := c) (by linarith)
  have hG1 := criticalHalfLineEnergyDomain_unitTilt_exp_mul_groundState hW hthreshold hF hc
  have h := criticalState_hasSum_zeroPairing hW hthreshold hF hG hG1
  have hreal : (∫ u in Iio (0 : ℝ), F u * (Real.exp (-(c * u)) * F u) * Real.exp (-(8 * u))) =
      ∫ u, F u ^ 2 * Real.exp (-((8 + c) * u)) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      rw [hd.support u (not_lt.mp hu)]
      ring]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show F u * (Real.exp (-(c * u)) * F u) * Real.exp (-(8 * u)) =
      F u ^ 2 * Real.exp (-((8 + c) * u))
    have e : Real.exp (-((8 + c) * u)) = Real.exp (-(c * u)) * Real.exp (-(8 * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e]
    ring
  have hval : ((bareMixedEnergy F (fun u => Real.exp (-(c * u)) * F u) : ℝ) : ℂ) =
      -((criticalAliasCoefficient W₀ : ℂ) *
        ((∫ u, F u ^ 2 * Real.exp (-((8 + c) * u)) : ℝ) : ℂ)) := by
    rw [criticalState_bareMixedEnergy_eq_neg_statePairing hW hthreshold hF hG,
      statePairing_cx hd.support, ← hreal]
  have hfun : (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
      negativeHalfLineLaplace (cx F) (-centredZero q - (c : ℂ))) =
      fun q => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx fun u => Real.exp (-(c * u)) * F u) (-centredZero q) := by
    funext q
    rw [laplace_exp_neg_mul]
  rw [hfun, ← hval]
  exact h

end GaloisForLFunctions.ExclusionOfTheCriticalState
