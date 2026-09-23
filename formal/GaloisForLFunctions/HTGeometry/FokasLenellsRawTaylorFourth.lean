import GaloisForLFunctions.HTGeometry.FokasLenellsRawQuinticKernel

/-!
# Fourth-order remainder of the actual spatial scattering flow

The exact quintic kernel identity extends the constructed cubic expansion.
Whole-line Schwartz majorants control the fourth integrand and its primitive,
including a single bound valid near zero frequency at every spatial point.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawFourthIntegrand (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  rawDividedOperator q 0 x (rawThirdSlope q k v x)+
    rawCubicOperator q 0 x (rawSolutionSlope q k v x)+
    (k : ℂ) • rawQuinticOperator q k x (rawInteractionSolution q k v x)

def rawFourthDensity (q : SchwartzMap ℝ ℂ) (k x : ℝ) : ℝ :=
  ((rawInteractionMass q^(2 : ℕ)+|k| * rawCubicMass q)*rawInteractionMass q+rawCubicMass q)*rawInteractionDensity q x+
    rawInteractionMass q*rawCubicDensity q x+|k| * rawQuinticDensity q x

theorem rawFourthDensity_nonneg (q : SchwartzMap ℝ ℂ) (k x : ℝ) : 0 ≤ rawFourthDensity q k x := by
  have hM := rawInteractionMass_nonneg q
  have hN := rawCubicMass_nonneg q
  have hρ := rawInteractionDensity_nonneg q x
  have hσ := rawCubicDensity_nonneg q x
  have hτ := rawQuinticDensity_nonneg q x
  unfold rawFourthDensity
  positivity

theorem rawFourthDensity_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) : Integrable (rawFourthDensity q k) :=
  (((rawInteractionDensity_integrable q).const_mul _).add
    ((rawCubicDensity_integrable q).const_mul _)).add ((rawQuinticDensity_integrable q).const_mul _)

theorem rawFourthDensity_eventually_bound (q : SchwartzMap ℝ ℂ) :
    ∀ᶠ k : ℝ in 𝓝 0, ∀ x : ℝ, rawFourthDensity q k x ≤ rawFourthDensity q 1 x := by
  have hk : ∀ᶠ k : ℝ in 𝓝 0, |k| < 1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  filter_upwards [hk] with k hk
  intro x
  unfold rawFourthDensity
  simp only [abs_one,one_mul]
  have hM := rawInteractionMass_nonneg q
  have hN := rawCubicMass_nonneg q
  have hρ := rawInteractionDensity_nonneg q x
  have hτ := rawQuinticDensity_nonneg q x
  gcongr
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hk.le hN
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hk.le hτ

theorem continuous_rawFourthIntegrand (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Continuous (rawFourthIntegrand q k v) :=
  (((continuous_rawDividedOperator q 0).clm_apply (continuous_rawThirdSlope q k v)).add
    ((continuous_rawCubicOperator q 0).clm_apply (continuous_rawSolutionSlope q k v))).add
    (((continuous_rawQuinticOperator q k).clm_apply (continuous_rawInteractionSolution q k v)).const_smul (k : ℂ))

theorem rawFourthIntegrand_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawFourthIntegrand q k v x‖ ≤
      (‖v‖*Real.exp (|k| * rawInteractionMass q))*rawFourthDensity q k x := by
  have hL := ((rawDividedOperator q 0 x).le_opNorm (rawThirdSlope q k v x)).trans
    (mul_le_mul (rawDividedOperator_bound q 0 x) (rawThirdSlope_bound q k v x)
      (norm_nonneg _) (rawInteractionDensity_nonneg q x))
  have hC := ((rawCubicOperator q 0 x).le_opNorm (rawSolutionSlope q k v x)).trans
    (mul_le_mul (rawCubicOperator_bound q 0 x) (rawSolutionSlope_bound q k v x)
      (norm_nonneg _) (rawCubicDensity_nonneg q x))
  have hE := ((rawQuinticOperator q k x).le_opNorm (rawInteractionSolution q k v x)).trans
    (mul_le_mul (rawQuinticOperator_bound q k x) (rawInteractionSolution_global_bound q k v x)
      (norm_nonneg _) (rawQuinticDensity_nonneg q x))
  have hn : ‖rawFourthIntegrand q k v x‖ ≤
      ‖rawDividedOperator q 0 x (rawThirdSlope q k v x)‖+
      ‖rawCubicOperator q 0 x (rawSolutionSlope q k v x)‖+
      |k| * ‖rawQuinticOperator q k x (rawInteractionSolution q k v x)‖ := by
    unfold rawFourthIntegrand
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _)
      (by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]))
  exact hn.trans ((add_le_add (add_le_add hL hC)
    (mul_le_mul_of_nonneg_left hE (abs_nonneg k))).trans_eq (by unfold rawFourthDensity; ring))

theorem rawFourthIntegrand_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Integrable (rawFourthIntegrand q k v) :=
  ((rawFourthDensity_integrable q k).const_mul (‖v‖*Real.exp (|k| * rawInteractionMass q))).mono'
    (continuous_rawFourthIntegrand q k v).aestronglyMeasurable
    (Eventually.of_forall (rawFourthIntegrand_bound q k v))

theorem rawFourthIntegrand_eventually_bound (q : SchwartzMap ℝ ℂ) (v : SpectralVector) :
    ∀ᶠ k : ℝ in 𝓝 0, ∀ x : ℝ, ‖rawFourthIntegrand q k v x‖ ≤
      (‖v‖*Real.exp (rawInteractionMass q))*rawFourthDensity q 1 x := by
  have hk : ∀ᶠ k : ℝ in 𝓝 0, |k| < 1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  filter_upwards [hk,rawFourthDensity_eventually_bound q] with k hk hd
  intro x
  have hm : |k| * rawInteractionMass q ≤ rawInteractionMass q := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hk.le (rawInteractionMass_nonneg q)
  exact (rawFourthIntegrand_bound q k v x).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hm) (norm_nonneg v)) (hd x)
      (rawFourthDensity_nonneg q k x) (mul_nonneg (norm_nonneg v) (Real.exp_pos _).le))

/-- One more exact divided equation, with its frequency-zero coefficient taken from the actual flow. -/
theorem rawThirdIntegrand_fourth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawThirdIntegrand q k v x = rawThirdIntegrand q 0 v x+(k : ℂ) • rawFourthIntegrand q k v x := by
  unfold rawThirdIntegrand rawFourthIntegrand
  rw [rawSecondSlope_third_factor,rawCubicOperator_fifth_factor]
  simp only [_root_.add_apply,_root_.smul_apply,map_add,map_smul,
    rawInteractionSolution_zero_frequency]
  rw [rawInteractionSolution_first_factor]
  simp only [map_add,map_smul]
  module

def rawFourthSlope (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  ∫ s in (0 : ℝ)..x, rawFourthIntegrand q k v s

theorem continuous_rawFourthSlope (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Continuous (rawFourthSlope q k v) := (rawFourthIntegrand_integrable q k v).continuous_primitive 0

theorem rawThirdSlope_fourth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawThirdSlope q k v x = rawThirdSlope q 0 v x+(k : ℂ) • rawFourthSlope q k v x := by
  have he : (fun s => rawThirdIntegrand q k v s) =
      fun s => rawThirdIntegrand q 0 v s+(k : ℂ) • rawFourthIntegrand q k v s := by
    funext s
    exact rawThirdIntegrand_fourth_factor q k v s
  rw [rawThirdSlope,he]
  have hz : IntervalIntegrable (fun s => rawThirdIntegrand q 0 v s) volume 0 x :=
    (rawThirdIntegrand_integrable q 0 v).intervalIntegrable
  have hs : IntervalIntegrable (fun s => (k : ℂ) • rawFourthIntegrand q k v s) volume 0 x :=
    ((rawFourthIntegrand_integrable q k v).smul (k : ℂ)).intervalIntegrable
  rw [intervalIntegral.integral_add hz hs,intervalIntegral.integral_smul]
  rfl

def rawFourthMass (q : SchwartzMap ℝ ℂ) (k : ℝ) : ℝ := ∫ x : ℝ, rawFourthDensity q k x

theorem rawFourthMass_nonneg (q : SchwartzMap ℝ ℂ) (k : ℝ) : 0 ≤ rawFourthMass q k :=
  integral_nonneg (rawFourthDensity_nonneg q k)

theorem rawFourthMass_eventually_bound (q : SchwartzMap ℝ ℂ) :
    ∀ᶠ k : ℝ in 𝓝 0, rawFourthMass q k ≤ rawFourthMass q 1 := by
  filter_upwards [rawFourthDensity_eventually_bound q] with k hk
  exact integral_mono (rawFourthDensity_integrable q k) (rawFourthDensity_integrable q 1) hk

theorem rawFourthSlope_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawFourthSlope q k v x‖ ≤ (‖v‖*Real.exp (|k| * rawInteractionMass q))*rawFourthMass q k := by
  have h1 : ‖rawFourthSlope q k v x‖ ≤ ∫ s : ℝ, ‖rawFourthIntegrand q k v s‖ :=
    intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (setIntegral_le_integral (rawFourthIntegrand_integrable q k v).norm
        (Eventually.of_forall fun s => norm_nonneg (rawFourthIntegrand q k v s)))
  have h2 := integral_mono (rawFourthIntegrand_integrable q k v).norm
    ((rawFourthDensity_integrable q k).const_mul (‖v‖*Real.exp (|k| * rawInteractionMass q)))
    (rawFourthIntegrand_bound q k v)
  rw [integral_const_mul] at h2
  exact h1.trans h2

theorem rawFourthIntegrand_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    Tendsto (fun k => rawFourthIntegrand q k v x) (𝓝 0) (𝓝 (rawFourthIntegrand q 0 v x)) := by
  have hL := ((rawDividedOperator q 0 x).continuous.tendsto _).comp (rawThirdSlope_tendsto_zero q v x)
  have hC := ((rawCubicOperator q 0 x).continuous.tendsto _).comp (rawSolutionSlope_tendsto_zero q v x)
  have hc : Continuous (fun k : ℝ => rawQuinticOperator q k x) := by
    have hp : Continuous (fun k : ℝ => (k,x)) := continuous_id.prodMk continuous_const
    have hh := (continuous_rawQuinticOperator_parameters q).comp hp
    exact hh
  have hE := (hc.continuousAt.clm_apply (continuousAt_rawInteractionSolution_zero_frequency q v x)).tendsto
  exact (hL.add hC).add ((Complex.continuous_ofReal.tendsto 0).smul hE)

theorem rawFourthSlope_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    Tendsto (fun k => rawFourthSlope q k v x) (𝓝 0) (𝓝 (rawFourthSlope q 0 v x)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun s => (‖v‖*Real.exp (rawInteractionMass q))*rawFourthDensity q 1 s)
    (Eventually.of_forall fun k => (rawFourthIntegrand_integrable q k v).aestronglyMeasurable.restrict)
    ?_ ((rawFourthDensity_integrable q 1).const_mul _).intervalIntegrable ?_
  · filter_upwards [rawFourthIntegrand_eventually_bound q v] with k hk
    exact Eventually.of_forall fun s _ => hk s
  · exact Eventually.of_forall fun s _ => rawFourthIntegrand_tendsto_zero q v s

end
end GaloisForLFunctions.HTGeometry.FokasLenells
