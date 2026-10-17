import GaloisForLFunctions.RHTower.PaperThetaCompactMeyerRealization
import GaloisForLFunctions.RHTower.DeningerMeyerGaussianSourceApproximation
import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogOperatorContinuity
import GaloisForLFunctions.RHTower.DeningerMeyerFullXiJetAdmissionBoundary

/-! # The finite native normalization cannot extend continuously

First causal Xi sources tend to zero in every original weighted-derivative
gauge along the actual Xi escape sequence. In the literal Poisson quotient,
even every polynomial spectral multiple tends to zero. In contrast, their
normalized native theta images have tail trace `-1` and uniform norm at least
one. Thus no continuous linear realization of the whole original quotient
can retain the existing finite native normalization.

This does not assert divergence of a particular Gaussian family on a fixed
source, or rule out discontinuous maps. The positive survivor is the exact
all-order source-topology vanishing law for continuous observations.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction

namespace RHTower
open scoped DeningerMeyerNaturalTopology

private theorem first_causal_mellin (rho : XiDivisorSupport) (s : ℂ)
    (hs : s - (rho : ℂ) ≠ 0) :
    deningerMeyerStrongLogMellin
      (deningerMeyerXiCausalSource rho 1 (xiSupportMultiplicity_pos rho)) s =
        xi s / (s - (rho : ℂ)) := by
  apply (eq_div_iff hs).mpr
  simpa only [pow_one, mul_comm] using
    (deningerMeyerXiCausalSource_factor rho 1 (xiSupportMultiplicity_pos rho) s).symm

private theorem exterior_line_distance (rho : XiDivisorSupport) (k : ℤ)
    (hk : k ≤ -1 ∨ 2 ≤ k) (y : ℝ) :
    1 ≤ ‖(k : ℂ) + y * I - (rho : ℂ)‖ := by
  have hr := xi_divisor_support_re_mem_open_unit rho
  have hb := Complex.abs_re_le_norm ((k : ℂ) + y * I - (rho : ℂ))
  have he : (((k : ℂ) + y * I - (rho : ℂ)) : ℂ).re = (k : ℝ) - (rho : ℂ).re := by
    simp
  rw [he] at hb
  rcases hk with hk | hk
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast hk
    rw [abs_of_nonpos (by linarith)] at hb
    linarith
  · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith)] at hb
    linarith

private theorem escape_distance_tendsto (s : ℂ) :
    Tendsto (fun m => ‖s - (deningerMeyerXiVerticalEscape m : ℂ)‖) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (b + ‖s‖)
  refine ⟨N, fun m hm => ?_⟩
  have hnm : (N : ℝ) ≤ m := by exact_mod_cast hm
  have hρ := deningerMeyerXiVerticalEscape_norm_gt m
  have hd := norm_sub_norm_le (deningerMeyerXiVerticalEscape m : ℂ) s
  rw [norm_sub_rev] at hd
  linarith

private theorem first_causal_line_tendsto (n : ℕ) (k : ℤ)
    (hk : k ≤ -1 ∨ 2 ≤ k) :
    Tendsto (fun m : ℕ => ∫ y : ℝ,
      ‖(-((k : ℂ) + y * I)) ^ n * deningerMeyerStrongLogMellin
        (deningerMeyerXiCausalSource (deningerMeyerXiVerticalEscape m) 1
          (xiSupportMultiplicity_pos _)) ((k : ℂ) + y * I)‖) atTop (𝓝 0) := by
  let B := deningerMeyerStrongLogSumLM deningerMeyerXiCapSource
  let P : ℂ → ℂ := fun s => (-s) ^ n * xi s
  have hB (s : ℂ) : deningerMeyerStrongLogMellin B s = xi s :=
    deningerMeyerXiCapSource_mellin s
  have hP : DeningerEntireMellinRegular P := by
    convert (deningerMeyerStrongLogMellin_entireRegular B).signedPow n using 1
    funext s
    rw [hB]
  have hi := (hP ((k : ℝ) - 1) ((k : ℝ) + 1)).integrable_line
    (c := (k : ℝ)) (by linarith) (by linarith)
  have hs (rho : XiDivisorSupport) (y : ℝ) : (k : ℂ) + y * I - (rho : ℂ) ≠ 0 := by
    have hd := exterior_line_distance rho k hk y
    intro he
    rw [he, norm_zero] at hd
    norm_num at hd
  have he (m : ℕ) (y : ℝ) :
      (-((k : ℂ) + y * I)) ^ n * deningerMeyerStrongLogMellin
        (deningerMeyerXiCausalSource (deningerMeyerXiVerticalEscape m) 1
          (xiSupportMultiplicity_pos _)) ((k : ℂ) + y * I) =
        P ((k : ℂ) + y * I) /
          ((k : ℂ) + y * I - (deningerMeyerXiVerticalEscape m : ℂ)) := by
    rw [first_causal_mellin _ _ (hs _ y), mul_div_assoc]
  have hd := tendsto_integral_of_dominated_convergence
    (fun y : ℝ => ‖P ((k : ℂ) + y * I)‖) (f := fun _ => (0 : ℝ))
    (F := fun (m : ℕ) (y : ℝ) =>
      ‖(-((k : ℂ) + y * I)) ^ n * deningerMeyerStrongLogMellin
        (deningerMeyerXiCausalSource (deningerMeyerXiVerticalEscape m) 1
          (xiSupportMultiplicity_pos _)) ((k : ℂ) + y * I)‖)
    (fun m => (show Continuous (fun y : ℝ =>
      ‖(-((k : ℂ) + y * I)) ^ n * deningerMeyerStrongLogMellin
        (deningerMeyerXiCausalSource (deningerMeyerXiVerticalEscape m) 1
          (xiSupportMultiplicity_pos _)) ((k : ℂ) + y * I)‖) from by
        have := (deningerMeyerStrongLogMellin_entireRegular
          (deningerMeyerXiCausalSource (deningerMeyerXiVerticalEscape m) 1
            (xiSupportMultiplicity_pos _))).differentiable.continuous
        fun_prop).aestronglyMeasurable)
    (by simpa only [Complex.ofReal_intCast] using hi.norm)
    (fun m => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_norm, he, norm_div]
      exact div_le_self (norm_nonneg _) (exterior_line_distance _ k hk y))
    (Eventually.of_forall fun y => by
      simp_rw [he, norm_div, div_eq_mul_inv]
      simpa using (tendsto_inv_atTop_zero.comp
        (escape_distance_tendsto ((k : ℂ) + y * I))).const_mul
          ‖P ((k : ℂ) + y * I)‖)
  simpa only [integral_zero] using hd

private theorem gauge_between_le (g : DeningerMeyerStrongLogTarget) (n : ℕ)
    {a k b : ℤ} (ha : a ≤ k) (hb : k ≤ b) :
    ‖deningerMeyerStrongLogGauge n k g‖ ≤
      ‖deningerMeyerStrongLogGauge n a g‖ + ‖deningerMeyerStrongLogGauge n b g‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  have hw : Real.exp t ^ (k : ℝ) ≤ Real.exp t ^ (a : ℝ) + Real.exp t ^ (b : ℝ) := by
    simp only [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
    have ha' : (a : ℝ) ≤ k := by exact_mod_cast ha
    have hb' : (k : ℝ) ≤ b := by exact_mod_cast hb
    by_cases ht : 0 ≤ t
    · have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb' ht)
      linarith [Real.exp_pos (t * (a : ℝ))]
    · have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ha' (le_of_not_ge ht))
      linarith [Real.exp_pos (t * (b : ℝ))]
  have hn (j : ℤ) : ‖deningerMeyerStrongLogGauge n j g t‖ =
      Real.exp t ^ (j : ℝ) * ‖iteratedDeriv n (g : ℝ → ℂ) t‖ := by
    rw [deningerMeyerStrongLogGauge_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) _)]
  rw [hn]
  calc
    _ ≤ (Real.exp t ^ (a : ℝ) + Real.exp t ^ (b : ℝ)) *
        ‖iteratedDeriv n (g : ℝ → ℂ) t‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = ‖deningerMeyerStrongLogGauge n a g t‖ +
        ‖deningerMeyerStrongLogGauge n b g t‖ := by rw [hn, hn]; ring
    _ ≤ _ := add_le_add (BoundedContinuousFunction.norm_coe_le_norm _ _)
      (BoundedContinuousFunction.norm_coe_le_norm _ _)

/-- Actual first causal sources vanish in every original weighted derivative gauge. -/
theorem deningerMeyerXiFirstCausalSource_escape_tendsto :
    Tendsto (fun m => deningerMeyerXiCausalSource (deningerMeyerXiVerticalEscape m) 1
      (xiSupportMultiplicity_pos _)) atTop (𝓝 0) := by
  have exterior (n : ℕ) (k : ℤ) (hk : k ≤ -1 ∨ 2 ≤ k) :
      Tendsto (fun m => ‖deningerMeyerStrongLogGauge n k
        (deningerMeyerXiCausalSource (deningerMeyerXiVerticalEscape m) 1
          (xiSupportMultiplicity_pos _))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun m => deningerMeyerStrongLogGauge_le_mellin _ n k)
    simpa using (first_causal_line_tendsto n k hk).const_mul (1 / (2 * Real.pi))
  change Tendsto _ _ (@nhds _ (⨅ i : ℕ × ℤ, TopologicalSpace.induced
    (deningerMeyerStrongLogGaugeLinear i.1 i.2) inferInstance) 0)
  rw [nhds_iInf, tendsto_iInf]
  intro i
  rw [nhds_induced, map_zero, tendsto_comap_iff, tendsto_zero_iff_norm_tendsto_zero]
  change Tendsto (fun m => ‖deningerMeyerStrongLogGauge i.1 i.2
    (deningerMeyerXiCausalSource (deningerMeyerXiVerticalEscape m) 1
      (xiSupportMultiplicity_pos _))‖) atTop (𝓝 0)
  by_cases hk : i.2 ≤ -1 ∨ 2 ≤ i.2
  · exact exterior i.1 i.2 hk
  · apply squeeze_zero (fun _ => norm_nonneg _)
      (fun m => gauge_between_le _ i.1 (a := -1) (b := 2) (by omega) (by omega))
    simpa using (exterior i.1 (-1) (Or.inl le_rfl)).add
      (exterior i.1 2 (Or.inr le_rfl))

private theorem first_causal_generator_iterate (rho : XiDivisorSupport) (N : ℕ) :
    (deningerMeyerCohomologyGenerator^[N])
      (deningerMeyerXiCausalClass rho 1 (xiSupportMultiplicity_pos rho)) =
        (rho : ℂ)^N • deningerMeyerXiCausalClass rho 1 (xiSupportMultiplicity_pos rho) := by
  have he : deningerMeyerCohomologyGenerator
      (deningerMeyerXiCausalClass rho 1 (xiSupportMultiplicity_pos rho)) =
        (rho : ℂ) • deningerMeyerXiCausalClass rho 1 (xiSupportMultiplicity_pos rho) := by
    simpa only [deningerMeyerXiCausalClass_zero, add_zero] using
      deningerMeyerXiCausalClass_generator rho 0 (xiSupportMultiplicity_pos rho)
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply', ih, map_smul, he, smul_smul, pow_succ]

/-- Every polynomial spectral multiple of these literal quotient classes still vanishes. -/
theorem deningerMeyerXiFirstCausalClass_polynomial_escape (N : ℕ) :
    Tendsto (fun m => (deningerMeyerXiVerticalEscape m : ℂ)^N •
      deningerMeyerXiCausalClass (deningerMeyerXiVerticalEscape m) 1
        (xiSupportMultiplicity_pos _)) atTop (𝓝 0) := by
  have hq : Tendsto (fun m => deningerMeyerXiCausalClass (deningerMeyerXiVerticalEscape m) 1
      (xiSupportMultiplicity_pos _)) atTop (𝓝 0) := by
    have hc : Continuous (fun g : DeningerMeyerStrongLogTarget =>
        (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology)) := continuous_quot_mk
    simpa only [deningerMeyerXiCausalClass, Function.comp_def, Submodule.Quotient.mk_zero] using
      (hc.tendsto 0).comp deningerMeyerXiFirstCausalSource_escape_tendsto
  have hz : (deningerMeyerCohomologyGenerator^[N]) 0 = 0 := by
    induction N with
    | zero => rfl
    | succ N ih => rw [Function.iterate_succ_apply', ih, map_zero]
  have hg := ((deningerMeyerCohomologyGenerator_continuous.iterate N).tendsto 0).comp hq
  simpa only [Function.comp_def, first_causal_generator_iterate, hz] using hg

/-- The phase used by the existing Hedenmalm realization preserves the all-order vanishing. -/
theorem deningerMeyerFirstHedenmalmClass_polynomial_escape (N : ℕ) :
    Tendsto (fun m => (deningerMeyerXiVerticalEscape m : ℂ)^N •
      deningerMeyerHedenmalmClass (deningerMeyerXiVerticalEscape m)
        ⟨1, Nat.succ_lt_succ (xiSupportMultiplicity_pos _)⟩) atTop (𝓝 0) := by
  have he : (fun m => (deningerMeyerXiVerticalEscape m : ℂ)^N •
      deningerMeyerHedenmalmClass (deningerMeyerXiVerticalEscape m)
        ⟨1, Nat.succ_lt_succ (xiSupportMultiplicity_pos _)⟩) =
      (fun m => I • ((deningerMeyerXiVerticalEscape m : ℂ)^N •
        deningerMeyerXiCausalClass (deningerMeyerXiVerticalEscape m) 1
          (xiSupportMultiplicity_pos _))) := by
    funext m
    rw [deningerMeyerHedenmalmClass_eq, pow_one]
    exact smul_comm _ _ _
  rw [he]
  simpa only [smul_zero] using
    (deningerMeyerXiFirstCausalClass_polynomial_escape N).const_smul I

/-- Every continuous observation must respect the polynomial source-topology vanishing. -/
theorem deningerMeyerFirstHedenmalmClass_continuous_observation
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
    (T : DeningerMeyerStrongLogCohomology →L[ℂ] E) (N : ℕ) :
    Tendsto (fun m => (deningerMeyerXiVerticalEscape m : ℂ)^N •
      T (deningerMeyerHedenmalmClass (deningerMeyerXiVerticalEscape m)
        ⟨1, Nat.succ_lt_succ (xiSupportMultiplicity_pos _)⟩)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, map_smul, map_zero] using
    (T.continuous.tendsto 0).comp (deningerMeyerFirstHedenmalmClass_polynomial_escape N)

namespace PaperThetaEndpoint

/-- The existing first native packet retains its nonzero tail trace at every Xi divisor. -/
theorem one_le_norm_nativeThetaDivisorJet_zero (rho : XiDivisorSupport) :
    1 ≤ ‖nativeThetaDivisorJet rho ⟨0, xiSupportMultiplicity_pos rho⟩‖ := by
  have ht := (tendsto_flatParameterJet_atTop 0 (xiSpectralPointSupport rho)).norm
  have hb := le_of_tendsto ht (Eventually.of_forall fun x =>
    (nativeThetaDivisorJet rho ⟨0, xiSupportMultiplicity_pos rho⟩).norm_coe_le_norm x)
  simpa [parameterEndpointTrace] using hb

/-- The exact finite native normalization has no continuous whole-source extension. -/
theorem no_continuous_unregularized_native_realization :
    ¬ ∃ T : DeningerMeyerStrongLogCohomology →L[ℂ] NativeContinuousSpace,
      ∀ rho : XiDivisorSupport,
        T (deningerMeyerHedenmalmClass rho
          ⟨1, Nat.succ_lt_succ (xiSupportMultiplicity_pos rho)⟩) =
          nativeThetaDivisorJet rho ⟨0, xiSupportMultiplicity_pos rho⟩ := by
  rintro ⟨T, hT⟩
  have ht := (deningerMeyerFirstHedenmalmClass_continuous_observation T 0).norm
  simp only [pow_zero, one_smul, norm_zero] at ht
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto ht (Eventually.of_forall fun m => by
    rw [hT]
    exact one_le_norm_nativeThetaDivisorJet_zero _)
  norm_num at hbad

/-- In particular, the already constructed finite full-multiplicity synthesis maps
cannot be the restrictions of one continuous map on the original quotient. -/
theorem no_continuous_extension_of_nativeFiniteSynthesis :
    ¬ ∃ T : DeningerMeyerStrongLogCohomology →L[ℂ] NativeContinuousSpace,
      ∀ (S : Finset XiDivisorSupport) (c : DeningerMeyerFiniteXiJetPacket S),
        T (meyerFiniteHedenmalmSynthesis S c) = nativeFiniteSynthesis S c := by
  rintro ⟨T, hT⟩
  apply no_continuous_unregularized_native_realization
  refine ⟨T, fun rho => ?_⟩
  let S : Finset XiDivisorSupport := {rho}
  let q : DeningerMeyerFiniteXiJetSlot S :=
    ⟨⟨rho, by simp [S]⟩, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
  have h := hT S (Pi.single q 1)
  simpa [meyerFiniteHedenmalmSynthesis, nativeFiniteSynthesis, q] using h

end PaperThetaEndpoint
end RHTower
