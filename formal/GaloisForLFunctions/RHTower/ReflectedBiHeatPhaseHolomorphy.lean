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

end


end RHTower
