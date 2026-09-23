import GaloisForLFunctions.HTGeometry.FokasLenellsRawTaylorFourth

/-!
# Fifth-order remainder of the actual spatial scattering flow

The exact quintic kernel identity extends the constructed cubic expansion.
Whole-line Schwartz majorants control the fifth integrand and its primitive,
including a single bound valid near zero frequency at every spatial point.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawFifthIntegrand (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  rawDividedOperator q 0 x (rawFourthSlope q k v x)+
    rawCubicOperator q 0 x (rawSecondSlope q k v x)+
    rawQuinticOperator q k x (rawInteractionSolution q k v x)

def rawFifthDensity (q : SchwartzMap ℝ ℂ) (k x : ℝ) : ℝ :=
  rawFourthMass q k*rawInteractionDensity q x+
    (rawInteractionMass q^(2 : ℕ)+|k| * rawCubicMass q)*rawCubicDensity q x+rawQuinticDensity q x

theorem rawFifthDensity_nonneg (q : SchwartzMap ℝ ℂ) (k x : ℝ) : 0 ≤ rawFifthDensity q k x := by
  have hM := rawInteractionMass_nonneg q
  have hN := rawCubicMass_nonneg q
  have hF := rawFourthMass_nonneg q k
  have hρ := rawInteractionDensity_nonneg q x
  have hσ := rawCubicDensity_nonneg q x
  have hτ := rawQuinticDensity_nonneg q x
  unfold rawFifthDensity
  positivity

theorem rawFifthDensity_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) : Integrable (rawFifthDensity q k) :=
  (((rawInteractionDensity_integrable q).const_mul _).add
    ((rawCubicDensity_integrable q).const_mul _)).add (rawQuinticDensity_integrable q)

theorem rawFifthDensity_eventually_bound (q : SchwartzMap ℝ ℂ) :
    ∀ᶠ k : ℝ in 𝓝 0, ∀ x : ℝ, rawFifthDensity q k x ≤ rawFifthDensity q 1 x := by
  have hk : ∀ᶠ k : ℝ in 𝓝 0, |k| < 1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  filter_upwards [hk,rawFourthMass_eventually_bound q] with k hk hFk
  intro x
  unfold rawFifthDensity
  simp only [abs_one,one_mul]
  have hM := rawInteractionMass_nonneg q
  have hN := rawCubicMass_nonneg q
  have hF := rawFourthMass_nonneg q k
  have hρ := rawInteractionDensity_nonneg q x
  have hσ := rawCubicDensity_nonneg q x
  have hτ := rawQuinticDensity_nonneg q x
  gcongr
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hk.le hN

theorem continuous_rawFifthIntegrand (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Continuous (rawFifthIntegrand q k v) :=
  (((continuous_rawDividedOperator q 0).clm_apply (continuous_rawFourthSlope q k v)).add
    ((continuous_rawCubicOperator q 0).clm_apply (continuous_rawSecondSlope q k v))).add
    ((continuous_rawQuinticOperator q k).clm_apply (continuous_rawInteractionSolution q k v))

theorem rawFifthIntegrand_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawFifthIntegrand q k v x‖ ≤
      (‖v‖*Real.exp (|k| * rawInteractionMass q))*rawFifthDensity q k x := by
  have hL := ((rawDividedOperator q 0 x).le_opNorm (rawFourthSlope q k v x)).trans
    (mul_le_mul (rawDividedOperator_bound q 0 x) (rawFourthSlope_bound q k v x)
      (norm_nonneg _) (rawInteractionDensity_nonneg q x))
  have hC := ((rawCubicOperator q 0 x).le_opNorm (rawSecondSlope q k v x)).trans
    (mul_le_mul (rawCubicOperator_bound q 0 x) (rawSecondSlope_bound q k v x)
      (norm_nonneg _) (rawCubicDensity_nonneg q x))
  have hE := ((rawQuinticOperator q k x).le_opNorm (rawInteractionSolution q k v x)).trans
    (mul_le_mul (rawQuinticOperator_bound q k x) (rawInteractionSolution_global_bound q k v x)
      (norm_nonneg _) (rawQuinticDensity_nonneg q x))
  have hn : ‖rawFifthIntegrand q k v x‖ ≤
      ‖rawDividedOperator q 0 x (rawFourthSlope q k v x)‖+
      ‖rawCubicOperator q 0 x (rawSecondSlope q k v x)‖+
      ‖rawQuinticOperator q k x (rawInteractionSolution q k v x)‖ := by
    unfold rawFifthIntegrand
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  exact hn.trans ((add_le_add (add_le_add hL hC)
    hE).trans_eq (by unfold rawFifthDensity; ring))

theorem rawFifthIntegrand_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Integrable (rawFifthIntegrand q k v) :=
  ((rawFifthDensity_integrable q k).const_mul (‖v‖*Real.exp (|k| * rawInteractionMass q))).mono'
    (continuous_rawFifthIntegrand q k v).aestronglyMeasurable
    (Eventually.of_forall (rawFifthIntegrand_bound q k v))

theorem rawFifthIntegrand_eventually_bound (q : SchwartzMap ℝ ℂ) (v : SpectralVector) :
    ∀ᶠ k : ℝ in 𝓝 0, ∀ x : ℝ, ‖rawFifthIntegrand q k v x‖ ≤
      (‖v‖*Real.exp (rawInteractionMass q))*rawFifthDensity q 1 x := by
  have hk : ∀ᶠ k : ℝ in 𝓝 0, |k| < 1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  filter_upwards [hk,rawFifthDensity_eventually_bound q] with k hk hd
  intro x
  have hm : |k| * rawInteractionMass q ≤ rawInteractionMass q := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hk.le (rawInteractionMass_nonneg q)
  exact (rawFifthIntegrand_bound q k v x).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hm) (norm_nonneg v)) (hd x)
      (rawFifthDensity_nonneg q k x) (mul_nonneg (norm_nonneg v) (Real.exp_pos _).le))

/-- The fifth divided equation, derived from both actual preceding primitive identities. -/
theorem rawFourthIntegrand_fifth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawFourthIntegrand q k v x = rawFourthIntegrand q 0 v x+(k : ℂ) • rawFifthIntegrand q k v x := by
  unfold rawFourthIntegrand rawFifthIntegrand
  rw [rawThirdSlope_fourth_factor,rawSolutionSlope_second_factor]
  simp only [rawSolutionSlope_zero,Complex.ofReal_zero,zero_smul,add_zero,map_add,map_smul]
  module

def rawFifthSlope (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  ∫ s in (0 : ℝ)..x, rawFifthIntegrand q k v s

theorem continuous_rawFifthSlope (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Continuous (rawFifthSlope q k v) := (rawFifthIntegrand_integrable q k v).continuous_primitive 0

theorem rawFourthSlope_fifth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawFourthSlope q k v x = rawFourthSlope q 0 v x+(k : ℂ) • rawFifthSlope q k v x := by
  have he : (fun s => rawFourthIntegrand q k v s) =
      fun s => rawFourthIntegrand q 0 v s+(k : ℂ) • rawFifthIntegrand q k v s := by
    funext s
    exact rawFourthIntegrand_fifth_factor q k v s
  rw [rawFourthSlope,he]
  have hz : IntervalIntegrable (fun s => rawFourthIntegrand q 0 v s) volume 0 x :=
    (rawFourthIntegrand_integrable q 0 v).intervalIntegrable
  have hs : IntervalIntegrable (fun s => (k : ℂ) • rawFifthIntegrand q k v s) volume 0 x :=
    ((rawFifthIntegrand_integrable q k v).smul (k : ℂ)).intervalIntegrable
  rw [intervalIntegral.integral_add hz hs,intervalIntegral.integral_smul]
  rfl

def rawFifthMass (q : SchwartzMap ℝ ℂ) (k : ℝ) : ℝ := ∫ x : ℝ, rawFifthDensity q k x

theorem rawFifthMass_nonneg (q : SchwartzMap ℝ ℂ) (k : ℝ) : 0 ≤ rawFifthMass q k :=
  integral_nonneg (rawFifthDensity_nonneg q k)

theorem rawFifthMass_eventually_bound (q : SchwartzMap ℝ ℂ) :
    ∀ᶠ k : ℝ in 𝓝 0, rawFifthMass q k ≤ rawFifthMass q 1 := by
  filter_upwards [rawFifthDensity_eventually_bound q] with k hk
  exact integral_mono (rawFifthDensity_integrable q k) (rawFifthDensity_integrable q 1) hk

theorem rawFifthSlope_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawFifthSlope q k v x‖ ≤ (‖v‖*Real.exp (|k| * rawInteractionMass q))*rawFifthMass q k := by
  have h1 : ‖rawFifthSlope q k v x‖ ≤ ∫ s : ℝ, ‖rawFifthIntegrand q k v s‖ :=
    intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (setIntegral_le_integral (rawFifthIntegrand_integrable q k v).norm
        (Eventually.of_forall fun s => norm_nonneg (rawFifthIntegrand q k v s)))
  have h2 := integral_mono (rawFifthIntegrand_integrable q k v).norm
    ((rawFifthDensity_integrable q k).const_mul (‖v‖*Real.exp (|k| * rawInteractionMass q)))
    (rawFifthIntegrand_bound q k v)
  rw [integral_const_mul] at h2
  exact h1.trans h2

theorem rawFifthIntegrand_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    Tendsto (fun k => rawFifthIntegrand q k v x) (𝓝 0) (𝓝 (rawFifthIntegrand q 0 v x)) := by
  have hL := ((rawDividedOperator q 0 x).continuous.tendsto _).comp (rawFourthSlope_tendsto_zero q v x)
  have hC := ((rawCubicOperator q 0 x).continuous.tendsto _).comp (rawSecondSlope_tendsto_zero q v x)
  have hc : Continuous (fun k : ℝ => rawQuinticOperator q k x) := by
    have hp : Continuous (fun k : ℝ => (k,x)) := continuous_id.prodMk continuous_const
    have hh := (continuous_rawQuinticOperator_parameters q).comp hp
    exact hh
  have hE := (hc.continuousAt.clm_apply (continuousAt_rawInteractionSolution_zero_frequency q v x)).tendsto
  exact (hL.add hC).add hE

theorem rawFifthSlope_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    Tendsto (fun k => rawFifthSlope q k v x) (𝓝 0) (𝓝 (rawFifthSlope q 0 v x)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun s => (‖v‖*Real.exp (rawInteractionMass q))*rawFifthDensity q 1 s)
    (Eventually.of_forall fun k => (rawFifthIntegrand_integrable q k v).aestronglyMeasurable.restrict)
    ?_ ((rawFifthDensity_integrable q 1).const_mul _).intervalIntegrable ?_
  · filter_upwards [rawFifthIntegrand_eventually_bound q v] with k hk
    exact Eventually.of_forall fun s _ => hk s
  · exact Eventually.of_forall fun s _ => rawFifthIntegrand_tendsto_zero q v s

end
end GaloisForLFunctions.HTGeometry.FokasLenells
