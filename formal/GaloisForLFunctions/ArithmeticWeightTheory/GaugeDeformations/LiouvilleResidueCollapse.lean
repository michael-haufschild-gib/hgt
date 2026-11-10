import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.LiouvilleCutoffAsymptotic
import GaloisForLFunctions.RHTower.Sieve.MoebiusDoubleLogRealCutoff
import GaloisForLFunctions.HTGeometry.WindowRpowIntegral

/-!
# Logarithmic collapse of the Liouville boundary residue

The pole residue along exp(iπ t^p) vanishes at exactly logarithmic-square
speed. This is too slow for any holomorphic joint regularization at the
endpoint, independently of bounds on the individual prime coordinates.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- The moving prime cutoff at the reciprocal distance to the endpoint. -/
def liouvilleTransitionCutoff (t : ℝ) : ℕ := ⌊(1 - t)⁻¹⌋₊

/-- The actual interior residue; only its restriction to the open unit interval is used. -/
def liouvilleBoundaryResidue (t : ℝ) : ℂ :=
  jointGaugeRegularization liouvilleBoundaryPhase ((t : ℂ), 1)

/-- The nonzero leading coefficient of the boundary residue. -/
def liouvilleResidueConstant : ℂ :=
  riemannZeta 2 * (Real.exp (-2 * Real.eulerMascheroniConstant) : ℂ)

private theorem tendsto_endpoint_distance :
    Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [sub_self] using
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝 (1 - 1)))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < 1 - t
    exact sub_pos.mpr ht

theorem tendsto_endpoint_reciprocal :
    Tendsto (fun t : ℝ => (1 - t)⁻¹) (𝓝[<] 1) atTop :=
  tendsto_inv_nhdsGT_zero.comp tendsto_endpoint_distance

theorem tendsto_liouvilleTransitionCutoff :
    Tendsto liouvilleTransitionCutoff (𝓝[<] 1) atTop :=
  tendsto_nat_floor_atTop.comp tendsto_endpoint_reciprocal

/-- Rounding the reciprocal distance changes its scale by a factor tending to one. -/
theorem tendsto_endpoint_mul_cutoff :
    Tendsto (fun t : ℝ => (1 - t) * (liouvilleTransitionCutoff t : ℝ))
      (𝓝[<] 1) (𝓝 1) := by
  have hh := tendsto_nat_floor_div_atTop.comp tendsto_endpoint_reciprocal
  simpa only [Function.comp_def, liouvilleTransitionCutoff, div_inv_eq_mul, mul_comm] using hh

theorem tendsto_endpoint_log_ratio :
    Tendsto (fun t : ℝ => Real.log ((1 - t)⁻¹) /
      Real.log (liouvilleTransitionCutoff t : ℝ)) (𝓝[<] 1) (𝓝 1) := by
  have hh := (_root_.RHTower.Sieve.tendsto_log_natFloor_div_log_one.comp
    tendsto_endpoint_reciprocal).inv₀ one_ne_zero
  simpa only [Function.comp_def, liouvilleTransitionCutoff, inv_div, inv_one] using hh

/-- The moving sharp cutoff approximates the entire complex residue logarithm. -/
theorem tendsto_boundaryExponent_sub_cutoff_zero :
    Tendsto (fun t : ℝ => jointDeformationExponent liouvilleBoundaryPhase ((t : ℂ), 1) -
      liouvilleCutoffLog (liouvilleTransitionCutoff t)) (𝓝[<] 1) (𝓝 0) := by
  have hcount := tendsto_primeCounting_div_nat_zero.comp tendsto_liouvilleTransitionCutoff
  have hfirst := (tendsto_endpoint_mul_cutoff.mul hcount).const_mul (2 * Real.pi)
  have hsecond := (tendsto_endpoint_mul_cutoff.inv₀ one_ne_zero).mul
    tendsto_normalized_primeAbelMass_zero
  have hbound := hfirst.add (hsecond.const_mul (2 * Real.pi))
  simp only [mul_zero, add_zero] at hbound
  have hbound' : Tendsto (fun t : ℝ =>
      2 * Real.pi * (1 - t) * Nat.primeCounting (liouvilleTransitionCutoff t) +
      (2 * Real.pi / liouvilleTransitionCutoff t) * primeAbelMass t)
      (𝓝[<] 1) (𝓝 0) := by
    refine hbound.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      tendsto_liouvilleTransitionCutoff.eventually (eventually_gt_atTop 0)] with t ht hN
    have hd : (1 - t) ≠ 0 := (sub_pos.mpr ht).ne'
    have hNr : (liouvilleTransitionCutoff t : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    change 2 * Real.pi * ((1 - t) * (liouvilleTransitionCutoff t : ℝ) *
      (Nat.primeCounting (liouvilleTransitionCutoff t) / (liouvilleTransitionCutoff t : ℝ))) +
      2 * Real.pi * (((1 - t) * (liouvilleTransitionCutoff t : ℝ))⁻¹ *
        ((1 - t) * primeAbelMass t)) = _
    field_simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _ hbound'
  filter_upwards [self_mem_nhdsWithin,
    (lt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds,
    tendsto_liouvilleTransitionCutoff.eventually (eventually_gt_atTop 0)] with t ht ht0 hN
  exact norm_boundaryExponent_sub_cutoff_le ht0.le ht hN

/-- Exact complex asymptotic of the actual pole residue on approach to the Liouville endpoint. -/
theorem tendsto_liouvilleBoundaryResidue_normalized :
    Tendsto (fun t : ℝ => (Real.log ((1 - t)⁻¹) : ℂ) ^ 2 * liouvilleBoundaryResidue t)
      (𝓝[<] 1) (𝓝 liouvilleResidueConstant) := by
  have hE := Complex.continuous_exp.continuousAt.tendsto.comp
    tendsto_boundaryExponent_sub_cutoff_zero
  simp only [Complex.exp_zero] at hE
  have hP := tendsto_liouvilleCutoffProduct_normalized.comp tendsto_liouvilleTransitionCutoff
  have hR := Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_endpoint_log_ratio
  have hh := (hE.mul hP).mul (hR.pow 2)
  simp only [Complex.ofReal_one, one_pow, mul_one, one_mul] at hh
  refine hh.congr' ?_
  filter_upwards [tendsto_liouvilleTransitionCutoff.eventually (eventually_gt_atTop 1)] with t hN
  have hlog : Real.log (liouvilleTransitionCutoff t : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  have hlogC : (Real.log (liouvilleTransitionCutoff t : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hlog
  change Complex.exp (_ - _) * ((Real.log (liouvilleTransitionCutoff t : ℝ) : ℂ) ^ 2 *
    Complex.exp (liouvilleCutoffLog (liouvilleTransitionCutoff t))) *
      ((Real.log ((1 - t)⁻¹) / Real.log (liouvilleTransitionCutoff t : ℝ) : ℝ) : ℂ) ^ 2 = _
  rw [liouvilleBoundaryResidue, jointGaugeRegularization, zetaResidueFactor_one, one_mul,
    Complex.exp_sub, Complex.ofReal_div]
  field_simp

theorem liouvilleResidueConstant_ne_zero : liouvilleResidueConstant ≠ 0 := by
  apply mul_ne_zero
  · exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

/-- The interior pole residues tend to zero at the Liouville endpoint. -/
theorem tendsto_liouvilleBoundaryResidue_zero :
    Tendsto liouvilleBoundaryResidue (𝓝[<] 1) (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_endpoint_reciprocal
  have hI := Complex.continuous_ofReal.continuousAt.tendsto.comp hlog.inv_tendsto_atTop
  have hh := tendsto_liouvilleBoundaryResidue_normalized.mul (hI.pow 2)
  simp only [Complex.ofReal_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero] at hh
  refine hh.congr' ?_
  filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with t ht
  have hn : (Real.log ((1 - t)⁻¹) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  change (Real.log ((1 - t)⁻¹) : ℂ) ^ 2 * liouvilleBoundaryResidue t *
    (((Real.log ((1 - t)⁻¹))⁻¹ : ℝ) : ℂ) ^ 2 = _
  rw [Complex.ofReal_inv]
  calc
    _ = ((Real.log ((1 - t)⁻¹) : ℂ) * (Real.log ((1 - t)⁻¹) : ℂ)⁻¹) ^ 2 *
        liouvilleBoundaryResidue t := by ring
    _ = _ := by rw [mul_inv_cancel₀ hn, one_pow, one_mul]

private theorem tendsto_endpoint_power_log_sq {α : ℝ} (hα : 0 < α) :
    Tendsto (fun t : ℝ => (1 - t) ^ α * Real.log ((1 - t)⁻¹) ^ 2)
      (𝓝[<] 1) (𝓝 0) := by
  have hh := (_root_.HTGeometry.tendsto_logPow_div_rpow hα 2).comp
    tendsto_endpoint_reciprocal
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change Real.log ((1 - t)⁻¹) ^ 2 / ((1 - t)⁻¹) ^ α = _
  rw [Real.inv_rpow (sub_pos.mpr ht).le, div_inv_eq_mul, mul_comm]

/-- Residue collapse is slower than every positive power of the endpoint distance. -/
theorem tendsto_liouvilleBoundaryResidue_div_power {α : ℝ} (hα : 0 < α) :
    Tendsto (fun t : ℝ => ‖liouvilleBoundaryResidue t‖ / (1 - t) ^ α)
      (𝓝[<] 1) atTop := by
  have hD : Tendsto (fun t : ℝ => (1 - t) ^ α * Real.log ((1 - t)⁻¹) ^ 2)
      (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_endpoint_power_log_sq hα, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (Real.tendsto_log_atTop.comp tendsto_endpoint_reciprocal).eventually
        (eventually_gt_atTop 0)] with t ht hlog
    exact mul_pos (Real.rpow_pos_of_pos (sub_pos.mpr ht) _) (sq_pos_of_pos hlog)
  have hI := tendsto_inv_nhdsGT_zero.comp hD
  have hh := Filter.Tendsto.pos_mul_atTop
    (norm_pos_iff.mpr liouvilleResidueConstant_ne_zero)
    tendsto_liouvilleBoundaryResidue_normalized.norm hI
  refine hh.congr' ?_
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_endpoint_reciprocal).eventually
      (eventually_gt_atTop 0)] with t hlog
  change 0 < Real.log ((1 - t)⁻¹) at hlog
  change ‖(Real.log ((1 - t)⁻¹) : ℂ) ^ 2 * liouvilleBoundaryResidue t‖ *
    ((1 - t) ^ α * Real.log ((1 - t)⁻¹) ^ 2)⁻¹ = _
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  calc
    _ = (‖liouvilleBoundaryResidue t‖ / (1 - t) ^ α) *
        (Real.log ((1 - t)⁻¹) ^ 2 * (Real.log ((1 - t)⁻¹) ^ 2)⁻¹) := by
      rw [mul_inv, div_eq_mul_inv]
      ring
    _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero 2 hlog.ne'), mul_one]

/-- Even one-sided real Euler agreement cannot be realized by a joint holomorphic endpoint germ. -/
theorem liouvilleBoundary_no_joint_endpoint_regularization :
    ¬ ∃ U : ℂ × ℂ → ℂ, AnalyticAt ℂ U (1, 1) ∧
      ∀ᶠ t : ℝ in 𝓝[<] 1, ∀ᶠ σ : ℝ in 𝓝[>] 1,
        U ((t : ℂ), (σ : ℂ)) =
          ((σ : ℂ) - 1) * gaugeFibre (liouvilleBoundaryGauge t) (σ : ℂ) := by
  rintro ⟨U, hU, hagree⟩
  have hreal : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[<] 1) (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.continuousAt.tendsto :
        Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 1) (𝓝 ((1 : ℝ) : ℂ))).mono_left
          nhdsWithin_le_nhds
  have hpath : Tendsto (fun t : ℝ => ((t : ℂ), (1 : ℂ))) (𝓝[<] 1) (𝓝 (1, 1)) :=
    hreal.prodMk_nhds tendsto_const_nhds
  have heq : ∀ᶠ t : ℝ in 𝓝[<] 1,
      U ((t : ℂ), 1) = liouvilleBoundaryResidue t := by
    filter_upwards [hagree, hpath.eventually hU.eventually_analyticAt, self_mem_nhdsWithin,
      (lt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with t ha hUt ht ht0
    have habs : |t| < 1 := by rw [abs_of_pos ht0]; exact ht
    obtain ⟨hW, _, hWe⟩ := liouvilleBoundary_interior_poles t habs
    have hc : ContinuousAt (fun σ : ℝ => ((t : ℂ), (σ : ℂ))) 1 := by fun_prop
    have hUc : ContinuousAt (fun σ : ℝ => U ((t : ℂ), (σ : ℂ))) 1 := by
      exact hUt.continuousAt.comp (f := fun σ : ℝ => ((t : ℂ), (σ : ℂ))) (g := U) hc
    have hWc : ContinuousAt
        (fun σ : ℝ => jointGaugeRegularization liouvilleBoundaryPhase ((t : ℂ), (σ : ℂ))) 1 := by
      exact hW.continuousAt.comp (f := fun σ : ℝ => ((t : ℂ), (σ : ℂ)))
        (g := jointGaugeRegularization liouvilleBoundaryPhase) hc
    have he : (fun σ : ℝ => U ((t : ℂ), (σ : ℂ))) =ᶠ[𝓝[>] 1]
        (fun σ : ℝ => jointGaugeRegularization liouvilleBoundaryPhase ((t : ℂ), (σ : ℂ))) := by
      filter_upwards [ha, self_mem_nhdsWithin] with σ hσ hσ1
      exact hσ.trans (hWe (σ : ℂ) (by exact_mod_cast hσ1)).symm
    exact tendsto_nhds_unique
      ((hUc.tendsto.mono_left nhdsWithin_le_nhds).congr' he)
      (hWc.tendsto.mono_left nhdsWithin_le_nhds)
  have hzero : U (1, 1) = 0 :=
    tendsto_nhds_unique ((hU.continuousAt.tendsto.comp hpath).congr' heq)
      tendsto_liouvilleBoundaryResidue_zero
  have hF : AnalyticAt ℂ (fun z : ℂ => U (z, 1)) 1 :=
    hU.comp (g := U) (f := fun z : ℂ => (z, (1 : ℂ)))
      (analyticAt_id.prod analyticAt_const)
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hF.differentiableAt.hasDerivAt.isBigO_sub
  have hgrowth : Tendsto (fun t : ℝ => ‖liouvilleBoundaryResidue t‖ / (1 - t))
      (𝓝[<] 1) atTop := by
    simpa only [Real.rpow_one] using tendsto_liouvilleBoundaryResidue_div_power
      (by norm_num : (0 : ℝ) < 1)
  have hfalse : ∀ᶠ t : ℝ in 𝓝[<] 1, False := by
    filter_upwards [hreal.eventually hC, heq, self_mem_nhdsWithin,
      hgrowth.eventually (eventually_gt_atTop C)] with t hb he ht hgt
    have hdist : ‖(t : ℂ) - 1‖ = 1 - t := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_neg (sub_neg.mpr ht)]
      ring
    change ‖U ((t : ℂ), 1) - U (1, 1)‖ ≤ C * ‖(t : ℂ) - 1‖ at hb
    rw [hzero, sub_zero, he, hdist] at hb
    have hle := (div_le_iff₀ (sub_pos.mpr ht)).mpr hb
    exact (not_lt_of_ge hle) hgt
  exact hfalse.exists.elim (fun _ hf => hf)

#print axioms tendsto_boundaryExponent_sub_cutoff_zero
#print axioms tendsto_liouvilleBoundaryResidue_normalized
#print axioms tendsto_liouvilleBoundaryResidue_zero
#print axioms tendsto_liouvilleBoundaryResidue_div_power
#print axioms liouvilleBoundary_no_joint_endpoint_regularization

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
