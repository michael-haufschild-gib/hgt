import GaloisForLFunctions.RHTower.ReflectedBiHeatFixedRegulatorHolomorphy
import GaloisForLFunctions.RHTower.PolarizedAdditiveHeatSharpRemainder
import GaloisForLFunctions.RHTower.ZetaStandardTwistDichotomy
import GaloisForLFunctions.RHTower.ZetaLogDerivLineBound

/-!
# Holomorphy of the reflected phase integral

This module supplies parameter-uniform Jonquière bounds and uses Cauchy-dominated integration to
make the fixed-positive-regulator phase integral holomorphic across the full reflected strip.
-/

open Complex Filter Set Topology
open HurwitzZeta MeasureTheory

namespace RHTower

noncomputable section

/-- Real p-series occurring in the explicit Jonquière remainder constant. -/
def jonquierePSeries (s : ℂ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 - s).re - 1)

/-- The remainder p-series varies continuously as long as its exponent stays above one. -/
theorem continuousAt_jonquierePSeries {s₀ : ℂ} (hs₀ : s₀.re < 1) :
    ContinuousAt jonquierePSeries s₀ := by
  let r : ℝ := (1 - s₀.re) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let M : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-r - 1)
  have hM : Summable M := by
    refine (summable_nat_add_one_rpow_neg (c := r + 1) (by linarith)).congr ?_
    intro n
    dsimp [M]
    congr 1
    ring
  have hbound : ∀ n : ℕ, ∀ s ∈ Metric.closedBall s₀ r,
      ‖((n : ℝ) + 1) ^ (-(1 - s).re - 1)‖ ≤ M n := by
    intro n s hs
    have hdist : ‖s - s₀‖ ≤ r := by
      simpa [Complex.dist_eq] using hs
    have hre : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa using Complex.abs_re_le_norm (s - s₀)
    have hsr : s.re - s₀.re ≤ r := le_trans (le_abs_self _) (hre.trans hdist)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [r] at hsr ⊢
    linarith
  have huniform := tendstoUniformlyOn_tsum hM hbound
  have hcont : ContinuousOn jonquierePSeries (Metric.closedBall s₀ r) := by
    exact huniform.continuousOn
      (Filter.Eventually.frequently (Filter.Eventually.of_forall fun S =>
        continuousOn_finsetSum S fun n _ =>
          ((Real.continuous_const_rpow (by positivity : (n : ℝ) + 1 ≠ 0)).comp
            (by fun_prop : Continuous fun s : ℂ => -(1 - s).re - 1)).continuousOn))
  apply hcont.continuousAt
  exact mem_of_superset (Metric.ball_mem_nhds s₀ hr) Metric.ball_subset_closedBall

/-- Continuity of the exact Jonquière error constant on the open unit strip. -/
theorem continuousAt_jonquiereConst_of_openStrip {s₀ : ℂ}
    (_hs₀0 : 0 < s₀.re) (hs₀1 : s₀.re < 1) :
    ContinuousAt jonquiereConst s₀ := by
  have hgamma : ContinuousAt (fun s : ℂ => Complex.Gamma (1 - s)) s₀ := by
    apply (Complex.continuousAt_Gamma (1 - s₀) ?_).comp
    · fun_prop
    · intro m hm
      have hre := congrArg Complex.re hm
      norm_num at hre
      linarith [hs₀1, Nat.cast_nonneg (α := ℝ) m]
  rw [show jonquiereConst = fun s : ℂ =>
      ‖((2 * (Real.pi : ℂ))) ^ (-(1 - s))‖ * ‖Complex.Gamma (1 - s)‖
        * (‖Complex.exp (↑Real.pi * I * (1 - s) / 2)‖
            + ‖Complex.exp (-↑Real.pi * I * (1 - s) / 2)‖)
        * (‖(1 - s)‖ * 2 ^ ((1 - s).re + 1) * jonquierePSeries s)
        / (2 * Real.pi) by
      funext s
      rw [jonquiereConst, jonquierePSeries]]
  have hpow : ContinuousAt (fun s : ℂ =>
      ((2 * (Real.pi : ℂ))) ^ (-(1 - s))) s₀ :=
    (continuousAt_const_cpow (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).comp
      (by fun_prop)
  have hrpow : ContinuousAt (fun s : ℂ => (2 : ℝ) ^ ((1 - s).re + 1)) s₀ :=
    (Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp
      (by fun_prop)
  have hexpPos : ContinuousAt (fun s : ℂ => ‖Complex.exp
      (↑Real.pi * I * (1 - s) / 2)‖) s₀ := by fun_prop
  have hexpNeg : ContinuousAt (fun s : ℂ => ‖Complex.exp
      (-↑Real.pi * I * (1 - s) / 2)‖) s₀ := by fun_prop
  have hnorm : ContinuousAt (fun s : ℂ => ‖1 - s‖) s₀ := by fun_prop
  exact (((hpow.norm.mul hgamma.norm).mul (hexpPos.add hexpNeg)).mul
    ((hnorm.mul hrpow).mul (continuousAt_jonquierePSeries hs₀1))).div_const _

/-- Coefficient in the standard pointwise Jonquière profile bound. -/
def phaseGermProfileCoeff (s : ℂ) : ℝ :=
  ‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖
    + jonquiereConst s * Real.pi

theorem phaseGermProfileCoeff_nonneg (s : ℂ) : 0 ≤ phaseGermProfileCoeff s := by
  rw [phaseGermProfileCoeff]
  nlinarith [norm_nonneg (jonquiereLead s), norm_nonneg (jonquiereLeadNeg s),
    norm_nonneg (riemannZeta s),
    mul_nonneg (jonquiereConst_nonneg s) Real.pi_pos.le]

theorem continuousAt_phaseGermProfileCoeff_of_openStrip {s₀ : ℂ}
    (hs₀0 : 0 < s₀.re) (hs₀1 : s₀.re < 1) :
    ContinuousAt phaseGermProfileCoeff s₀ := by
  have hgamma : ContinuousAt (fun s : ℂ => Complex.Gamma (1 - s)) s₀ := by
    apply (Complex.continuousAt_Gamma (1 - s₀) ?_).comp
    · fun_prop
    · intro m hm
      have hre := congrArg Complex.re hm
      norm_num at hre
      linarith [hs₀1, Nat.cast_nonneg (α := ℝ) m]
  have hlead : ContinuousAt jonquiereLead s₀ := by
    rw [show jonquiereLead = fun s : ℂ =>
      Complex.Gamma (1 - s) * Complex.exp (↑Real.pi * I * (1 - s) / 2) by rfl]
    exact hgamma.mul (by fun_prop)
  have hleadNeg : ContinuousAt jonquiereLeadNeg s₀ := by
    rw [show jonquiereLeadNeg = fun s : ℂ =>
      Complex.Gamma (1 - s) * Complex.exp (-↑Real.pi * I * (1 - s) / 2) by rfl]
    exact hgamma.mul (by fun_prop)
  have hzeta : ContinuousAt riemannZeta s₀ :=
    (differentiableAt_riemannZeta (by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith)).continuousAt
  change ContinuousAt (fun s : ℂ =>
    ‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖
      + jonquiereConst s * Real.pi) s₀
  exact (((hlead.norm.add hleadNeg.norm).add hzeta.norm).add
    ((continuousAt_jonquiereConst_of_openStrip hs₀0 hs₀1).mul
      (continuousAt_const : ContinuousAt (fun _ : ℂ => Real.pi) s₀)))

/-- The Jonquière profile coefficient has one nonnegative bound on every closed ball contained in
the open unit strip. -/
theorem exists_phaseGermProfileCoeff_bound_closedBall
    {s₀ : ℂ} {R : ℝ} (hR : 0 < R) (hlower : R < s₀.re) (hupper : s₀.re + R < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Metric.closedBall s₀ R, phaseGermProfileCoeff s ≤ C := by
  have hstrip : ∀ s ∈ Metric.closedBall s₀ R, 0 < s.re ∧ s.re < 1 := by
    intro s hs
    have hdist : ‖s - s₀‖ ≤ R := by simpa [Complex.dist_eq] using hs
    have hre : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa using Complex.abs_re_le_norm (s - s₀)
    have habs : |s.re - s₀.re| ≤ R := hre.trans hdist
    exact ⟨by linarith [(abs_le.mp habs).1], by linarith [(abs_le.mp habs).2]⟩
  have hcont : ContinuousOn phaseGermProfileCoeff (Metric.closedBall s₀ R) := by
    intro s hs
    exact (continuousAt_phaseGermProfileCoeff_of_openStrip
      (hstrip s hs).1 (hstrip s hs).2).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall s₀ R).exists_bound_of_continuousOn hcont
  have hcenter := hC s₀ (Metric.mem_closedBall_self hR.le)
  have hC0 : 0 ≤ C := by
    rw [Real.norm_of_nonneg (phaseGermProfileCoeff_nonneg s₀)] at hcenter
    exact (phaseGermProfileCoeff_nonneg s₀).trans hcenter
  refine ⟨C, hC0, fun s hs => ?_⟩
  have := hC s hs
  rwa [Real.norm_of_nonneg (phaseGermProfileCoeff_nonneg s)] at this

/-- A lower real-part margin gives one uniform singular-power profile on the phase window. -/
theorem phase_rpow_add_one_le_uniform {θ eta sigma : ℝ}
    (hθ0 : θ ≠ 0) (heta : 0 < eta) (hetaSigma : eta ≤ sigma) (hsigma : sigma < 1) :
    |θ| ^ (sigma - 1) + 1 ≤ |θ| ^ (eta - 1) + 2 := by
  have hθ : 0 < |θ| := abs_pos.mpr hθ0
  by_cases hle : |θ| ≤ 1
  · have hp : |θ| ^ (sigma - 1) ≤ |θ| ^ (eta - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hθ hle (by linarith)
    linarith
  · have hbase : 1 ≤ |θ| := (lt_of_not_ge hle).le
    have hp0 : |θ| ^ (sigma - 1) ≤ |θ| ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    have hp : |θ| ^ (sigma - 1) ≤ 1 := by simpa using hp0
    have hetapow : 0 ≤ |θ| ^ (eta - 1) := Real.rpow_nonneg hθ.le _
    calc
      |θ| ^ (sigma - 1) + 1 ≤ 1 + 1 := by
        simpa [add_comm] using add_le_add_right hp 1
      _ = 2 := by norm_num
      _ ≤ |θ| ^ (eta - 1) + 2 := by linarith

/-- A nonzero phase in the fundamental window is non-spectral on the additive circle. -/
theorem phaseCircle_ne_zero {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) (hθ0 : θ ≠ 0) :
    (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) ≠ 0 := by
  intro hzero
  obtain ⟨m, hm⟩ := (coe_unitAddCircle_eq_zero_iff (θ / (2 * Real.pi))).mp hzero
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlower : -(1 / 2 : ℝ) < θ / (2 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith [hθ.1]
  have hupper : θ / (2 * Real.pi) ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hθ.2]
  have habsQ : |θ / (2 * Real.pi)| < 1 :=
    abs_lt.mpr ⟨by linarith [hlower], lt_of_le_of_lt hupper (by norm_num)⟩
  have habs : |(m : ℝ)| < 1 := by simpa only [hm] using habsQ
  have hmlo : (-1 : ℤ) < m := by exact_mod_cast (abs_lt.mp habs).1
  have hmhi : m < (1 : ℤ) := by exact_mod_cast (abs_lt.mp habs).2
  have hm0 : m = 0 := by omega
  rw [hm0] at hm
  norm_num at hm
  apply hθ0
  have hden : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  exact (div_eq_zero_iff.mp hm.symm).resolve_right hden

/-- Reflection of the phase variable preserves measurability on the symmetric window. -/
theorem aestronglyMeasurable_phaseGerm_neg_window
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    AEStronglyMeasurable (fun θ : ℝ => phaseGerm s (-θ))
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
  have hpres := (Measure.measurePreserving_neg volume).restrict_preimage_emb
    (measurableEmbedding_neg : MeasurableEmbedding (Neg.neg : ℝ → ℝ))
    (Ioc (-Real.pi) Real.pi)
  have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioc (-Real.pi) Real.pi =
      Ico (-Real.pi) Real.pi := by
    ext θ
    simp
  rw [hpre] at hpres
  have hcomp := (aestronglyMeasurable_phaseGerm hs0 hs1).comp_quasiMeasurePreserving
    hpres.quasiMeasurePreserving
  change AEStronglyMeasurable (fun θ : ℝ => phaseGerm s (-θ))
    (volume.restrict (Ico (-Real.pi) Real.pi)) at hcomp
  rw [Measure.restrict_congr_set (MeasureTheory.Ico_ae_eq_Ioc :
    Ico (-Real.pi) Real.pi =ᵐ[volume] Ioc (-Real.pi) Real.pi)] at hcomp
  exact hcomp

/-- Holomorphic dependence of a boundary germ on any affine order staying in the open strip. -/
theorem differentiableOn_phaseGerm_comp_of_openStrip
    {f : ℂ → ℂ} {U : Set ℂ} (hf : Differentiable ℂ f)
    (hstrip : ∀ z ∈ U, 0 < (f z).re ∧ (f z).re < 1)
    {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    DifferentiableOn ℂ (fun z : ℂ => phaseGerm (f z) θ) U := by
  intro z hz
  by_cases hθ0 : θ = 0
  · subst θ
    have hne : f z ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith [(hstrip z hz).2]
    have hlocal : (fun w : ℂ => phaseGerm (f w) 0) =
        fun w : ℂ => riemannZeta (f w) := by
      funext w
      simp [phaseGerm, expZeta_zero]
    rw [hlocal]
    exact ((differentiableAt_riemannZeta hne).comp z (hf z)).differentiableWithinAt
  · have hphase := phaseCircle_ne_zero hθ hθ0
    have hentire : Differentiable ℂ
        (expZeta (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle)) :=
      (differentiable_expZeta_iff _).mpr hphase
    rw [show (fun w : ℂ => phaseGerm (f w) θ) =
      fun w : ℂ => expZeta (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) (f w) by rfl]
    exact ((hentire (f z)).comp z (hf z)).differentiableWithinAt

/-- Reflected-phase version of `differentiableOn_phaseGerm_comp_of_openStrip`. -/
theorem differentiableOn_phaseGerm_neg_comp_of_openStrip
    {f : ℂ → ℂ} {U : Set ℂ} (hf : Differentiable ℂ f)
    (hstrip : ∀ z ∈ U, 0 < (f z).re ∧ (f z).re < 1)
    {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    DifferentiableOn ℂ (fun z : ℂ => phaseGerm (f z) (-θ)) U := by
  intro z hz
  by_cases hθ0 : θ = 0
  · subst θ
    simpa using (differentiableOn_phaseGerm_comp_of_openStrip hf hstrip
      (show (0 : ℝ) ∈ Ioc (-Real.pi) Real.pi by constructor <;> linarith [Real.pi_pos])) z hz
  · have hphase : (((-θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) ≠ 0 := by
      have hpos := phaseCircle_ne_zero hθ hθ0
      intro hzero
      apply hpos
      have hneg : ((-((θ / (2 * Real.pi) : ℝ)) : ℝ) : UnitAddCircle) = 0 := by
        simpa [neg_div] using hzero
      simpa using congrArg Neg.neg hneg
    have hentire : Differentiable ℂ
        (expZeta (((-θ / (2 * Real.pi) : ℝ)) : UnitAddCircle)) :=
      (differentiable_expZeta_iff _).mpr hphase
    rw [show (fun w : ℂ => phaseGerm (f w) (-θ)) =
      fun w : ℂ => expZeta (((-θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) (f w) by
        funext w
        rw [phaseGerm]]
    exact ((hentire (f z)).comp z (hf z)).differentiableWithinAt

/-- One coefficient and one lower strip margin uniformly control a boundary germ. -/
theorem norm_phaseGerm_le_uniform
    {s : ℂ} {theta eta C : ℝ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (htheta : theta ∈ Ioc (-Real.pi) Real.pi) (htheta0 : theta ≠ 0)
    (heta0 : 0 < eta) (heta : eta ≤ s.re)
    (hC : phaseGermProfileCoeff s ≤ C) :
    ‖phaseGerm s theta‖ ≤ C * (|theta| ^ (eta - 1) + 2) := by
  calc
    ‖phaseGerm s theta‖
        ≤ phaseGermProfileCoeff s * (|theta| ^ (s.re - 1) + 1) := by
          simpa [phaseGermProfileCoeff] using norm_phaseGerm_le hs0 hs1 theta htheta htheta0
    _ ≤ C * (|theta| ^ (s.re - 1) + 1) := by
          exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ C * (|theta| ^ (eta - 1) + 2) := by
          exact mul_le_mul_of_nonneg_left
            (phase_rpow_add_one_le_uniform htheta0 heta0 heta hs1)
            ((phaseGermProfileCoeff_nonneg s).trans hC)

/-- Reflected phase integrand for a fixed positive regulator. -/
def reflectedBiHeatFixedRegulatorPhaseIntegrand
    (Q : ReflectedBiHeatPositiveSlice) (z : ℂ) (theta : ℝ) : ℂ :=
  phaseGerm (Q.leftOrder z) theta * phaseGerm (Q.rightOrder z) (-theta) *
    heatMultiplier Q.x theta

/-- The fixed-regulator phase integral whose analytic continuation will be welded to the row sum. -/
def reflectedBiHeatFixedRegulatorPhaseEnergy
    (Q : ReflectedBiHeatPositiveSlice) (z : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ theta in Ioc (-Real.pi) Real.pi,
      reflectedBiHeatFixedRegulatorPhaseIntegrand Q z theta

/-- Four-term power majorant produced by multiplying the two one-sided Jonquière profiles. -/
def reflectedBiHeatPhaseMajorant
    (K etaLeft etaRight : ℝ) (theta : ℝ) : ℝ :=
  K * |theta| ^ (etaLeft + etaRight - 2) +
    (2 * K) * |theta| ^ (etaLeft - 1) +
    (2 * K) * |theta| ^ (etaRight - 1) + 4 * K

theorem integrableOn_reflectedBiHeatPhaseMajorant
    {K etaLeft etaRight : ℝ}
    (hetaLeft : 0 < etaLeft) (hetaRight : 0 < etaRight)
    (hetaSum : 1 < etaLeft + etaRight) :
    IntegrableOn (reflectedBiHeatPhaseMajorant K etaLeft etaRight)
      (Ioc (-Real.pi) Real.pi) := by
  have hcross := integrableOn_abs_rpow_window
    (show -1 < etaLeft + etaRight - 2 by linarith)
  have hleft := integrableOn_abs_rpow_window
    (show -1 < etaLeft - 1 by linarith)
  have hright := integrableOn_abs_rpow_window
    (show -1 < etaRight - 1 by linarith)
  have hconst : IntegrableOn (fun _ : ℝ => 4 * K) (Ioc (-Real.pi) Real.pi) := by
    change Integrable (fun _ : ℝ => 4 * K)
      (volume.restrict (Ioc (-Real.pi) Real.pi))
    simpa using
      (integrableOn_abs_rpow_window (r := 0) (by norm_num)).const_mul (4 * K)
  exact (((hcross.const_mul K).add (hleft.const_mul (2 * K))).add
    (hright.const_mul (2 * K))).add hconst

/-- The reflected phase energy is holomorphic at every point where both shifted orders lie in the
open unit strip. -/
theorem differentiableAt_reflectedBiHeatFixedRegulatorPhaseEnergy
    (Q : ReflectedBiHeatPositiveSlice) {z0 : ℂ} (hz0 : z0 ∈ Q.domain) :
    DifferentiableAt ℂ (reflectedBiHeatFixedRegulatorPhaseEnergy Q) z0 := by
  let leftGap : ℝ := z0.re - Q.delta / 2
  let rightGap : ℝ := 1 - Q.delta / 2 - z0.re
  let R : ℝ := min (Q.delta / 8) (min (leftGap / 2) (rightGap / 2))
  have hleftGap : 0 < leftGap := by
    dsimp [leftGap]
    linarith [hz0.1]
  have hrightGap : 0 < rightGap := by
    dsimp [rightGap]
    linarith [hz0.2]
  have hR : 0 < R := by
    dsimp [R]
    exact lt_min (by linarith [Q.delta_pos])
      (lt_min (by linarith [hleftGap]) (by linarith [hrightGap]))
  have hRdelta : R ≤ Q.delta / 8 := by
    dsimp [R]
    exact min_le_left _ _
  have hRleft : R ≤ leftGap / 2 := by
    dsimp [R]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hRright : R ≤ rightGap / 2 := by
    dsimp [R]
    exact (min_le_right _ _).trans (min_le_right _ _)
  let leftCenter : ℂ := Q.leftOrder z0
  let rightCenter : ℂ := Q.rightOrder z0
  let etaLeft : ℝ := leftCenter.re - R
  let etaRight : ℝ := rightCenter.re - R
  have hleftCenter0 : R < leftCenter.re := by
    dsimp [leftCenter, ReflectedBiHeatPositiveSlice.leftOrder]
    norm_num [Complex.add_re, Complex.div_re]
    dsimp [leftGap] at hRleft
    linarith [hleftGap, Q.delta_pos]
  have hleftCenter1 : leftCenter.re + R < 1 := by
    dsimp [leftCenter, ReflectedBiHeatPositiveSlice.leftOrder]
    norm_num [Complex.add_re, Complex.div_re]
    dsimp [rightGap] at hRright
    linarith [hrightGap]
  have hrightCenter0 : R < rightCenter.re := by
    dsimp [rightCenter, ReflectedBiHeatPositiveSlice.rightOrder]
    norm_num [Complex.add_re, Complex.sub_re, Complex.div_re]
    dsimp [rightGap] at hRright
    linarith [hrightGap, Q.delta_pos]
  have hrightCenter1 : rightCenter.re + R < 1 := by
    dsimp [rightCenter, ReflectedBiHeatPositiveSlice.rightOrder]
    norm_num [Complex.add_re, Complex.sub_re, Complex.div_re]
    dsimp [leftGap] at hRleft
    linarith [hleftGap]
  have hetaLeft : 0 < etaLeft := by
    dsimp [etaLeft]
    exact sub_pos.mpr hleftCenter0
  have hetaRight : 0 < etaRight := by
    dsimp [etaRight]
    exact sub_pos.mpr hrightCenter0
  have hetaSum : 1 < etaLeft + etaRight := by
    dsimp [etaLeft, etaRight, leftCenter, rightCenter,
      ReflectedBiHeatPositiveSlice.leftOrder,
      ReflectedBiHeatPositiveSlice.rightOrder]
    norm_num [Complex.add_re, Complex.sub_re, Complex.div_re]
    linarith [hRdelta, Q.delta_pos]
  obtain ⟨CLeft, hCLeft0, hCLeft⟩ :=
    exists_phaseGermProfileCoeff_bound_closedBall hR hleftCenter0 hleftCenter1
  obtain ⟨CRight, hCRight0, hCRight⟩ :=
    exists_phaseGermProfileCoeff_bound_closedBall hR hrightCenter0 hrightCenter1
  obtain ⟨H, hH⟩ := (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi)).exists_bound_of_continuousOn
    (continuous_heatMultiplier Q.x_pos).continuousOn
  have hH0 : 0 ≤ H := by
    exact (norm_nonneg (heatMultiplier Q.x 0)).trans
      (hH 0 (by constructor <;> linarith [Real.pi_pos]))
  have hleftStrip : ∀ z ∈ Metric.ball z0 R,
      0 < (Q.leftOrder z).re ∧ (Q.leftOrder z).re < 1 := by
    intro z hz
    have hdist : ‖z - z0‖ < R := by simpa [Complex.dist_eq] using hz
    have hre : |z.re - z0.re| < R :=
      lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (z - z0)) hdist
    constructor
    · dsimp [ReflectedBiHeatPositiveSlice.leftOrder]
      norm_num [Complex.add_re, Complex.div_re]
      dsimp [leftCenter, ReflectedBiHeatPositiveSlice.leftOrder] at hleftCenter0
      norm_num [Complex.add_re, Complex.div_re] at hleftCenter0
      linarith [(abs_lt.mp hre).1]
    · dsimp [ReflectedBiHeatPositiveSlice.leftOrder]
      norm_num [Complex.add_re, Complex.div_re]
      dsimp [leftCenter, ReflectedBiHeatPositiveSlice.leftOrder] at hleftCenter1
      norm_num [Complex.add_re, Complex.div_re] at hleftCenter1
      linarith [(abs_lt.mp hre).2]
  have hrightStrip : ∀ z ∈ Metric.ball z0 R,
      0 < (Q.rightOrder z).re ∧ (Q.rightOrder z).re < 1 := by
    intro z hz
    have hdist : ‖z - z0‖ < R := by simpa [Complex.dist_eq] using hz
    have hre : |z.re - z0.re| < R :=
      lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (z - z0)) hdist
    constructor
    · dsimp [ReflectedBiHeatPositiveSlice.rightOrder]
      norm_num [Complex.add_re, Complex.sub_re, Complex.div_re]
      dsimp [rightCenter, ReflectedBiHeatPositiveSlice.rightOrder] at hrightCenter0
      norm_num [Complex.add_re, Complex.sub_re, Complex.div_re] at hrightCenter0
      linarith [(abs_lt.mp hre).2]
    · dsimp [ReflectedBiHeatPositiveSlice.rightOrder]
      norm_num [Complex.add_re, Complex.sub_re, Complex.div_re]
      dsimp [rightCenter, ReflectedBiHeatPositiveSlice.rightOrder] at hrightCenter1
      norm_num [Complex.add_re, Complex.sub_re, Complex.div_re] at hrightCenter1
      linarith [(abs_lt.mp hre).1]
  have hleftBall : ∀ z ∈ Metric.ball z0 R,
      Q.leftOrder z ∈ Metric.closedBall leftCenter R := by
    intro z hz
    have hle : dist z z0 ≤ R := le_of_lt hz
    simpa [leftCenter, ReflectedBiHeatPositiveSlice.leftOrder, Complex.dist_eq] using hle
  have hrightBall : ∀ z ∈ Metric.ball z0 R,
      Q.rightOrder z ∈ Metric.closedBall rightCenter R := by
    intro z hz
    have hle : dist z z0 ≤ R := le_of_lt hz
    rw [Metric.mem_closedBall, Complex.dist_eq]
    calc
      ‖Q.rightOrder z - rightCenter‖ = ‖-(z - z0)‖ := by
        congr 1
        dsimp [rightCenter, ReflectedBiHeatPositiveSlice.rightOrder]
        ring
      _ = ‖z - z0‖ := norm_neg _
      _ ≤ R := by simpa [Complex.dist_eq] using hle
  let K : ℝ := CLeft * CRight * H
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  let F : ℂ → ℝ → ℂ := fun z theta =>
    (Ioo (-Real.pi) Real.pi).indicator
      (reflectedBiHeatFixedRegulatorPhaseIntegrand Q z) theta
  let bound : ℝ → ℝ := fun theta =>
    (Ioo (-Real.pi) Real.pi).indicator
      (reflectedBiHeatPhaseMajorant K etaLeft etaRight) theta
  have hmeas : ∀ z ∈ Metric.ball z0 R,
      AEStronglyMeasurable (F z)
        (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    intro z hz
    have hraw : AEStronglyMeasurable
        (reflectedBiHeatFixedRegulatorPhaseIntegrand Q z)
        (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
      (((aestronglyMeasurable_phaseGerm (hleftStrip z hz).1 (hleftStrip z hz).2).mul
        (aestronglyMeasurable_phaseGerm_neg_window
          (hrightStrip z hz).1 (hrightStrip z hz).2)).mul
        ((continuous_heatMultiplier Q.x_pos).continuousOn.aestronglyMeasurable
          measurableSet_Ioc))
    apply hraw.congr
    have hnePi : ∀ᵐ theta ∂(volume : Measure ℝ), theta ≠ Real.pi :=
      MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton Real.pi)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
      MeasureTheory.ae_restrict_of_ae hnePi] with theta htheta hthetaPi
    have hthetaOpen : theta ∈ Ioo (-Real.pi) Real.pi := ⟨htheta.1, lt_of_le_of_ne htheta.2 hthetaPi⟩
    simp [F, Set.indicator_of_mem hthetaOpen]
  have hdiff : ∀ theta : ℝ,
      DifferentiableOn ℂ (fun z : ℂ => F z theta) (Metric.ball z0 R) := by
    intro theta
    by_cases htheta : theta ∈ Ioo (-Real.pi) Real.pi
    · have hthetaPos : theta ∈ Ioc (-Real.pi) Real.pi := ⟨htheta.1, htheta.2.le⟩
      have hnegTheta : -theta ∈ Ioc (-Real.pi) Real.pi := by
        constructor <;> linarith [htheta.1, htheta.2]
      have hleftDiff := differentiableOn_phaseGerm_comp_of_openStrip
        (by
          rw [show (Q.leftOrder : ℂ → ℂ) = fun z : ℂ => z + (Q.delta : ℂ) / 2 by rfl]
          fun_prop) hleftStrip hthetaPos
      have hrightDiff := differentiableOn_phaseGerm_neg_comp_of_openStrip
        (by
          rw [show (Q.rightOrder : ℂ → ℂ) = fun z : ℂ => 1 - z + (Q.delta : ℂ) / 2 by rfl]
          fun_prop) hrightStrip hthetaPos
      simpa [F, Set.indicator_of_mem htheta,
        reflectedBiHeatFixedRegulatorPhaseIntegrand] using
        (hleftDiff.mul hrightDiff).mul_const (heatMultiplier Q.x theta)
    · simp [F, Set.indicator_of_notMem htheta]
  have hbound : ∀ theta : ℝ, ∀ z ∈ Metric.ball z0 R,
      ‖F z theta‖ ≤ bound theta := by
    intro theta z hz
    by_cases htheta : theta ∈ Ioo (-Real.pi) Real.pi
    · rw [show F z theta = reflectedBiHeatFixedRegulatorPhaseIntegrand Q z theta by
          simp [F, Set.indicator_of_mem htheta],
        show bound theta = reflectedBiHeatPhaseMajorant K etaLeft etaRight theta by
          simp [bound, Set.indicator_of_mem htheta]]
      have hthetaPos : theta ∈ Ioc (-Real.pi) Real.pi := ⟨htheta.1, htheta.2.le⟩
      have hnegTheta : -theta ∈ Ioc (-Real.pi) Real.pi := by
        constructor <;> linarith [htheta.1, htheta.2]
      have hleftEta : etaLeft ≤ (Q.leftOrder z).re := by
        have hdist : ‖z - z0‖ < R := by simpa [Complex.dist_eq] using hz
        have hre : |z.re - z0.re| < R :=
          lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (z - z0)) hdist
        dsimp [etaLeft, leftCenter, ReflectedBiHeatPositiveSlice.leftOrder]
        norm_num [Complex.add_re, Complex.div_re]
        linarith [(abs_lt.mp hre).1]
      have hrightEta : etaRight ≤ (Q.rightOrder z).re := by
        have hdist : ‖z - z0‖ < R := by simpa [Complex.dist_eq] using hz
        have hre : |z.re - z0.re| < R :=
          lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (z - z0)) hdist
        dsimp [etaRight, rightCenter, ReflectedBiHeatPositiveSlice.rightOrder]
        norm_num [Complex.add_re, Complex.sub_re, Complex.div_re]
        linarith [(abs_lt.mp hre).2]
      have hleftCoeff := hCLeft (Q.leftOrder z) (hleftBall z hz)
      have hrightCoeff := hCRight (Q.rightOrder z) (hrightBall z hz)
      have hheat : ‖heatMultiplier Q.x theta‖ ≤ H :=
        hH theta ⟨htheta.1.le, htheta.2.le⟩
      by_cases htheta0 : theta = 0
      · have hleftZeta : ‖phaseGerm (Q.leftOrder z) theta‖ ≤ CLeft := by
          subst theta
          calc
            ‖phaseGerm (Q.leftOrder z) 0‖ = ‖riemannZeta (Q.leftOrder z)‖ := by
              simp [phaseGerm, expZeta_zero]
            _ ≤ phaseGermProfileCoeff (Q.leftOrder z) := by
              rw [phaseGermProfileCoeff]
              nlinarith [norm_nonneg (jonquiereLead (Q.leftOrder z)),
                norm_nonneg (jonquiereLeadNeg (Q.leftOrder z)),
                mul_nonneg (jonquiereConst_nonneg (Q.leftOrder z)) Real.pi_pos.le]
            _ ≤ CLeft := hleftCoeff
        have hrightZeta : ‖phaseGerm (Q.rightOrder z) (-theta)‖ ≤ CRight := by
          subst theta
          calc
            ‖phaseGerm (Q.rightOrder z) (-0)‖ = ‖riemannZeta (Q.rightOrder z)‖ := by
              simp [phaseGerm, expZeta_zero]
            _ ≤ phaseGermProfileCoeff (Q.rightOrder z) := by
              rw [phaseGermProfileCoeff]
              nlinarith [norm_nonneg (jonquiereLead (Q.rightOrder z)),
                norm_nonneg (jonquiereLeadNeg (Q.rightOrder z)),
                mul_nonneg (jonquiereConst_nonneg (Q.rightOrder z)) Real.pi_pos.le]
            _ ≤ CRight := hrightCoeff
        rw [reflectedBiHeatFixedRegulatorPhaseIntegrand, norm_mul, norm_mul]
        calc
          ‖phaseGerm (Q.leftOrder z) theta‖ * ‖phaseGerm (Q.rightOrder z) (-theta)‖ *
              ‖heatMultiplier Q.x theta‖
              ≤ CLeft * CRight * H := by gcongr
          _ ≤ reflectedBiHeatPhaseMajorant K etaLeft etaRight theta := by
            subst theta
            rw [reflectedBiHeatPhaseMajorant]
            dsimp [K]
            nlinarith [Real.rpow_nonneg (abs_nonneg (0 : ℝ)) (etaLeft + etaRight - 2),
              Real.rpow_nonneg (abs_nonneg (0 : ℝ)) (etaLeft - 1),
              Real.rpow_nonneg (abs_nonneg (0 : ℝ)) (etaRight - 1)]
      · have hleftNorm := norm_phaseGerm_le_uniform
          (hleftStrip z hz).1 (hleftStrip z hz).2 hthetaPos htheta0
          hetaLeft hleftEta hleftCoeff
        have hrightNorm := norm_phaseGerm_le_uniform
          (hrightStrip z hz).1 (hrightStrip z hz).2 hnegTheta (neg_ne_zero.mpr htheta0)
          hetaRight hrightEta hrightCoeff
        have hrightNorm' : ‖phaseGerm (Q.rightOrder z) (-theta)‖ ≤
            CRight * (|theta| ^ (etaRight - 1) + 2) := by
          simpa [abs_neg] using hrightNorm
        have habs : 0 < |theta| := abs_pos.mpr htheta0
        have hpow : |theta| ^ (etaLeft - 1) * |theta| ^ (etaRight - 1) =
            |theta| ^ (etaLeft + etaRight - 2) := by
          rw [← Real.rpow_add habs]
          congr 1
          ring
        rw [reflectedBiHeatFixedRegulatorPhaseIntegrand, norm_mul, norm_mul]
        calc
          ‖phaseGerm (Q.leftOrder z) theta‖ * ‖phaseGerm (Q.rightOrder z) (-theta)‖ *
              ‖heatMultiplier Q.x theta‖
              ≤ (CLeft * (|theta| ^ (etaLeft - 1) + 2)) *
                  (CRight * (|theta| ^ (etaRight - 1) + 2)) * H := by
                gcongr
          _ = reflectedBiHeatPhaseMajorant K etaLeft etaRight theta := by
            rw [reflectedBiHeatPhaseMajorant]
            dsimp [K]
            rw [← hpow]
            ring
    · simp [F, bound, Set.indicator_of_notMem htheta]
  have hboundInt : Integrable bound
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    have hraw := integrableOn_reflectedBiHeatPhaseMajorant
      (K := K) hetaLeft hetaRight hetaSum
    apply hraw.congr
    have hnePi : ∀ᵐ theta ∂(volume : Measure ℝ), theta ≠ Real.pi :=
      MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton Real.pi)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
      MeasureTheory.ae_restrict_of_ae hnePi] with theta htheta hthetaPi
    have hthetaOpen : theta ∈ Ioo (-Real.pi) Real.pi := ⟨htheta.1, lt_of_le_of_ne htheta.2 hthetaPi⟩
    simp [bound, Set.indicator_of_mem hthetaOpen]
  have hIntegral :=
    GaloisForLFunctions.HTGeometry.differentiableAt_integral_of_cauchy_dominated
      (μ := volume.restrict (Ioc (-Real.pi) Real.pi)) hR hmeas hdiff hbound hboundInt
  have hfun : (fun z : ℂ => ∫ theta : ℝ, F z theta
        ∂(volume.restrict (Ioc (-Real.pi) Real.pi))) =
      fun z : ℂ => ∫ theta in Ioc (-Real.pi) Real.pi,
        reflectedBiHeatFixedRegulatorPhaseIntegrand Q z theta := by
    funext z
    apply integral_congr_ae
    have hnePi : ∀ᵐ theta ∂(volume : Measure ℝ), theta ≠ Real.pi :=
      MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton Real.pi)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
      MeasureTheory.ae_restrict_of_ae hnePi] with theta htheta hthetaPi
    have hthetaOpen : theta ∈ Ioo (-Real.pi) Real.pi := ⟨htheta.1, lt_of_le_of_ne htheta.2 hthetaPi⟩
    simp [F, Set.indicator_of_mem hthetaOpen]
  rw [hfun] at hIntegral
  change DifferentiableAt ℂ (fun z : ℂ => (1 / (2 * (Real.pi : ℂ))) *
    ∫ theta in Ioc (-Real.pi) Real.pi,
      reflectedBiHeatFixedRegulatorPhaseIntegrand Q z theta) z0
  exact (differentiableAt_const (c := (1 / (2 * (Real.pi : ℂ))))).mul hIntegral

theorem differentiableOn_reflectedBiHeatFixedRegulatorPhaseEnergy
    (Q : ReflectedBiHeatPositiveSlice) :
    DifferentiableOn ℂ (reflectedBiHeatFixedRegulatorPhaseEnergy Q) Q.domain := by
  intro z hz
  exact (differentiableAt_reflectedBiHeatFixedRegulatorPhaseEnergy Q hz).differentiableWithinAt

end


end RHTower
