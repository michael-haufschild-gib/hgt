import GaloisForLFunctions.BiScaleUncertainty.ConfinedCoherentPlasticGap

/-!
# Bounded annular lifting of full coherent data

The actual tent partition reproduces folded square energy exactly. Its inverse
sinh lift gives uniform source-energy bounds and stability for the canonical
annular representative. The original signed plastic functional is controlled
by coherent price together with the explicit zero-fold component's cost.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.AnnularCoherentEnergyBounds
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open _root_.RHTower.WeilLevyCoshCrossover _root_.RHTower.WeilLevyPoleGauss
open GaloisForLFunctions.RHTower
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
open CoherentSourceProjection LocalCoherentFilter FiniteFilterSchurResidual
open FoldedHyperbolicCellDefect CoherentMomentAttainment AnnularCoherentRetraction
open CoherentKernelSplitting PlasticCoherentLineMinimizer CoherentFiberPlasticInfimum
open ConfinedCoherentPlasticGap
noncomputable section

private abbrev d := Real.log 2
private theorem d_pos : 0 < d := Real.log_pos (by norm_num : (1 : ℝ) < 2)
private abbrev unitSource := attainingSource 1
private def unitProfile : C_c(ℝ, ℝ) := sinhCompact (1 / 2) unitSource
private def P (f : C_c(ℝ, ℝ)) : C(ℝ, ℝ) := cellFold (oddCompactSource f)
private def cells : Finset ℤ := Finset.Icc (-4) 4

private theorem unit_profile_apply (u : ℝ) : unitProfile u = attainmentProfile u := by
  simpa only [unitProfile, one_mul] using sinhCompact_attainingSource 1 u

private theorem unit_apply (u : ℝ) : unitSource u = unitProfile u / Real.sinh (u / 2) := by
  rw [unit_profile_apply, attainingSource_apply, one_mul]

private theorem unit_fold (x : ℝ) : cellFold unitSource x = 1 := by
  obtain ⟨y, hy, he⟩ := (cellFold_periodic unitSource).exists_mem_Ico₀
    (by norm_num : (0 : ℝ) < 1) x
  rw [he]
  exact cellFold_attainingSource 1 y ⟨hy.1, hy.2.le⟩

private theorem unit_representative : representative unitSource = unitSource := by
  ext u
  rw [representative_apply, oddCompactSource_attainingSource, unit_fold, mul_one]

private theorem unit_support (u : ℝ) (hu : unitSource u ≠ 0) : d < |u| ∧ |u| < 3 * d := by
  have hs := representative_support unitSource
  rw [unit_representative] at hs
  exact hs hu

private theorem profile_bounds (u : ℝ) : 0 ≤ unitProfile u ∧ unitProfile u ≤ 1 := by
  rw [unit_profile_apply]
  unfold attainmentProfile
  have hl := GaloisForLFunctions.HTGeometry.tentReal_nonneg 1 (u / d - 2)
  have hr := GaloisForLFunctions.HTGeometry.tentReal_nonneg 1 (u / d + 2)
  have hl' := GaloisForLFunctions.HTGeometry.tentReal_le_one 1 (u / d - 2)
  have hr' := GaloisForLFunctions.HTGeometry.tentReal_le_one 1 (u / d + 2)
  constructor <;> linarith only [hl, hr, hl', hr']

private theorem profile_zero_outside (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (k : ℤ)
    (hk : k ∉ cells) : unitProfile (d * (x + k)) = 0 := by
  by_contra hn
  have hu : unitSource (d * (x + k)) ≠ 0 := by
    intro hz
    exact hn (by change Real.sinh _ * unitSource _ = 0; rw [hz, mul_zero])
  have hb := abs_lt.mp (unit_support _ hu).2
  have hxlo := mul_le_mul_of_nonneg_left hx.1 d_pos.le
  have hxhi := mul_le_mul_of_nonneg_left hx.2 d_pos.le
  have hlo : (-4 : ℝ) < (k : ℝ) := (mul_lt_mul_iff_right₀ d_pos).mp (by
    nlinarith only [hb.1, hxhi])
  have hhi : (k : ℝ) < (4 : ℝ) := (mul_lt_mul_iff_right₀ d_pos).mp (by
    nlinarith only [hb.2, hxlo, d_pos])
  apply hk
  rw [cells, Finset.mem_Icc]
  exact ⟨by exact_mod_cast hlo.le, by exact_mod_cast hhi.le⟩

private theorem profile_sum (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (∑ k ∈ cells, unitProfile (d * (x + k))) = 1 := by
  have he := cellFold_attainingSource 1 x hx
  rw [cellFold_apply] at he
  change (∑' k : ℤ, unitProfile (d * (x + k))) = 1 at he
  rw [tsum_eq_sum (s := cells) (fun k hk => profile_zero_outside x hx k hk)] at he
  exact he

private theorem fold_add_int (f : C_c(ℝ, ℝ)) (x : ℝ) (k : ℤ) : P f (x + k) = P f x := by
  simpa only [P, mul_one] using (cellFold_periodic (oddCompactSource f)).int_mul k x

private def physicalEnergy (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => unitProfile u * P f (u / d) ^ 2,
    unitProfile.continuous.mul (((P f).continuous.comp (continuous_id.div_const d)).pow 2)⟩,
    by
      change HasCompactSupport ((unitProfile : ℝ → ℝ) * fun u : ℝ => P f (u / d) ^ 2)
      exact unitProfile.hasCompactSupport.mul_right⟩

private def cellEnergy (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨fun x => unitProfile (d * x) * P f x ^ 2,
    (unitProfile.continuous.comp (continuous_const.mul continuous_id)).mul ((P f).continuous.pow 2)⟩,
    by
      change HasCompactSupport ((fun x : ℝ => unitProfile (d * x)) * fun x : ℝ => P f x ^ 2)
      exact (unitProfile.hasCompactSupport.comp_homeomorph
        (Homeomorph.mulLeft₀ d d_pos.ne')).mul_right⟩

private theorem cell_energy_apply (f : C_c(ℝ, ℝ)) (x : ℝ) :
    cellEnergy f x = unitProfile (d * x) * P f x ^ 2 := rfl

private theorem cell_energy_sum (f : C_c(ℝ, ℝ)) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (∑ k ∈ cells, cellEnergy f (x + k)) = P f x ^ 2 := by
  simp only [cell_energy_apply, fold_add_int]
  rw [← Finset.sum_mul, profile_sum x hx, one_mul]

private theorem cell_energy_integral (f : C_c(ℝ, ℝ)) :
    (∫ x, cellEnergy f x) = ∫ x in (0 : ℝ)..1, P f x ^ 2 := by
  have hs := (cellEnergy f).continuous.integrable_of_hasCompactSupport
    (cellEnergy f).hasCompactSupport |>.hasSum_intervalIntegral_comp_add_int.tsum_eq
  change (∑' k : ℤ, ∫ x in (0 : ℝ)..1, cellEnergy f (x + k)) =
    (∫ x, cellEnergy f x) at hs
  have hz (k : ℤ) (hk : k ∉ cells) : (∫ x in (0 : ℝ)..1, cellEnergy f (x + k)) = 0 := by
    calc
      (∫ x in (0 : ℝ)..1, cellEnergy f (x + k)) = ∫ _x in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        change cellEnergy f (x + k) = 0
        rw [cell_energy_apply, profile_zero_outside x hx k hk, zero_mul]
      _ = 0 := by simp
  rw [tsum_eq_sum (s := cells) hz] at hs
  have hi := intervalIntegral.integral_finsetSum (s := cells)
    (f := fun k : ℤ => fun x : ℝ => cellEnergy f (x + k)) (fun k _ =>
      ((cellEnergy f).continuous.comp (continuous_add_const (k : ℝ))).intervalIntegrable (μ := volume) 0 1)
  have he : (∫ x in (0 : ℝ)..1, ∑ k ∈ cells, cellEnergy f (x + k)) =
      ∫ x in (0 : ℝ)..1, P f x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact cell_energy_sum f x hx
  exact hs.symm.trans (hi.symm.trans he)

private theorem physical_energy_integral (f : C_c(ℝ, ℝ)) :
    (∫ u, physicalEnergy f u) = coherentPrice f := by
  have hs := Measure.integral_comp_mul_left (fun u : ℝ => physicalEnergy f u) d
  change (∫ x, unitProfile (d * x) * P f (d * x / d) ^ 2) =
    |d⁻¹| • (∫ u, physicalEnergy f u) at hs
  simp only [mul_div_cancel_left₀ _ d_pos.ne', abs_of_pos (inv_pos.mpr d_pos), smul_eq_mul] at hs
  change (∫ x, cellEnergy f x) = d⁻¹ * (∫ u, physicalEnergy f u) at hs
  have he := hs.symm.trans ((cell_energy_integral f).trans (integral_cellFold_sq f))
  change d⁻¹ * (∫ u, physicalEnergy f u) = coherentPrice f / d at he
  field_simp [d_pos.ne'] at he
  exact he

/-- The actual compact tent partition reproduces the complete folded square energy exactly. -/
theorem integral_profile_fold_sq (f : C_c(ℝ, ℝ)) :
    (∫ u, attainmentProfile u * cellFold (oddCompactSource f) (u / Real.log 2) ^ 2) = coherentPrice f := by
  have he := physical_energy_integral f
  change (∫ u, unitProfile u * P f (u / d) ^ 2) = coherentPrice f at he
  simpa only [unit_profile_apply, P] using he

/-- Uniform original-energy cost of the canonical annular inverse sinh lift. -/
def annularEnergyFactor : ℝ := 1 / Real.sinh (Real.log 2 / 2) ^ 2

theorem annularEnergyFactor_pos : 0 < annularEnergyFactor :=
  div_pos (by norm_num) (sq_pos_of_pos (Real.sinh_pos_iff.mpr (by linarith [d_pos])))

private theorem unit_energy_bound (u : ℝ) : unitSource u ^ 2 ≤ annularEnergyFactor * unitProfile u := by
  have hp := profile_bounds u
  have hc : 0 < Real.sinh (d / 2) := Real.sinh_pos_iff.mpr (by linarith [d_pos])
  by_cases hz : unitProfile u = 0
  · rw [unit_apply, hz]
    simp
  have hu : unitSource u ≠ 0 := by
    intro he
    exact hz (by change Real.sinh _ * unitSource u = 0; rw [he, mul_zero])
  have hb := (unit_support u hu).1
  have ha : Real.sinh (d / 2) ≤ |Real.sinh (u / 2)| := by
    rw [Real.abs_sinh, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Real.sinh_le_sinh.mpr (by linarith only [hb])
  have hden : Real.sinh (d / 2) ^ 2 ≤ Real.sinh (u / 2) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hc.le (abs_nonneg (Real.sinh (u / 2)))).mpr ha
  have hs : 0 < Real.sinh (u / 2) ^ 2 := (sq_pos_of_pos hc).trans_le hden
  rw [unit_apply, div_pow]
  change unitProfile u ^ 2 / Real.sinh (u / 2) ^ 2 ≤
    (1 / Real.sinh (d / 2) ^ 2) * unitProfile u
  rw [show 1 / Real.sinh (d / 2) ^ 2 * unitProfile u = unitProfile u / Real.sinh (d / 2) ^ 2 by ring]
  apply (div_le_div_iff₀ hs (sq_pos_of_pos hc)).mpr
  calc
    unitProfile u ^ 2 * Real.sinh (d / 2) ^ 2 ≤ unitProfile u * Real.sinh (d / 2) ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hp.1, hp.2]) (sq_nonneg _)
    _ ≤ unitProfile u * Real.sinh (u / 2) ^ 2 := mul_le_mul_of_nonneg_left hden hp.1

/-- Unconditional energy upper bound for the explicit actual representative. -/
theorem representative_energy_upper (f : C_c(ℝ, ℝ)) :
    autocorr (representative f) 0 ≤ annularEnergyFactor * coherentPrice f := by
  have hp (u : ℝ) : representative f u ^ 2 ≤ annularEnergyFactor * physicalEnergy f u := by
    rw [representative_apply, mul_pow]
    have he := mul_le_mul_of_nonneg_right (unit_energy_bound u) (sq_nonneg (P f (u / d)))
    change unitSource u ^ 2 * P f (u / d) ^ 2 ≤ annularEnergyFactor * (unitProfile u * P f (u / d) ^ 2)
    nlinarith only [he]
  have hi : Integrable (fun u : ℝ => representative f u ^ 2) :=
    integrable_sq (representative f).continuous (representative f).hasCompactSupport
  have hj : Integrable (fun u : ℝ => annularEnergyFactor * physicalEnergy f u) :=
    ((physicalEnergy f).continuous.integrable_of_hasCompactSupport (physicalEnergy f).hasCompactSupport).const_mul _
  have he := integral_mono hi hj hp
  rw [integral_sq_eq_autocorr_zero, integral_const_mul, physical_energy_integral] at he
  exact he

private theorem odd_add_smul (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    oddCompactSource (f + t • g) = oddCompactSource f + t • oddCompactSource g := by
  ext u
  change ((f u + t * g u) - (f (-u) + t * g (-u))) / 2 =
    (f u - f (-u)) / 2 + t * ((g u - g (-u)) / 2)
  ring

/-- The canonical actual-source lift respects every real linear combination. -/
theorem representative_add_smul (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    representative (f + t • g) = representative f + t • representative g := by
  ext u
  simp only [representative_apply, odd_add_smul, cellFold_add_smul,
    ContinuousMap.add_apply, ContinuousMap.smul_apply,
    CompactlySupportedContinuousMap.add_apply, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  ring

private theorem sub_eq_add_neg_smul (f g : C_c(ℝ, ℝ)) : f - g = f + (-1 : ℝ) • g := by
  ext u
  change f u - g u = f u + -1 * g u
  ring

private theorem representative_sub (f g : C_c(ℝ, ℝ)) :
    representative (f - g) = representative f - representative g := by
  rw [sub_eq_add_neg_smul, representative_add_smul, ← sub_eq_add_neg_smul]

theorem coherentPrice_representative (f : C_c(ℝ, ℝ)) : coherentPrice (representative f) = coherentPrice f := by
  unfold coherentPrice
  rw [oddCompactSource_representative]
  exact exactBudget_representative f

private theorem representative_mem_confined (f : C_c(ℝ, ℝ)) : representative f ∈ confinedFiber f 5 := by
  refine ⟨⟨oddCompactSource_representative f, cellFold_representative f⟩, ?_⟩
  intro u hu
  have hb := (representative_support f hu).2
  change |u| < ((5 : ℝ) + 1) * d / 2
  linarith only [hb]

/-- Uniform two-sided energy equivalence between realized coherent data and its annular lift. -/
theorem representative_energy_bounds (f : C_c(ℝ, ℝ)) :
    coherentPrice f / confinementCost 5 ≤ autocorr (representative f) 0 ∧
      autocorr (representative f) 0 ≤ annularEnergyFactor * coherentPrice f := by
  have hw := (representative_mem_confined f).2
  have hl := coherentPrice_le_confinedEnergy (representative f) 5 (by
    simpa only [oddCompactSource_representative] using hw)
  rw [coherentPrice_representative, oddCompactSource_representative] at hl
  refine ⟨(div_le_iff₀ (confinementCost_pos 5)).mpr ?_, representative_energy_upper f⟩
  simpa only [mul_comm] using hl

private theorem price_sub (f g : C_c(ℝ, ℝ)) :
    coherentPrice (f - g) = d * ∫ x in (0 : ℝ)..1, (P f x - P g x) ^ 2 := by
  have hf : cellFold (oddCompactSource (f - g)) = P f - P g := by
    rw [sub_eq_add_neg_smul, odd_add_smul, cellFold_add_smul]
    ext x
    change P f x + -1 * P g x = P f x - P g x
    ring
  have hi := integral_cellFold_sq (f - g)
  rw [hf] at hi
  change (∫ x in (0 : ℝ)..1, (P f x - P g x) ^ 2) = coherentPrice (f - g) / d at hi
  field_simp [d_pos.ne'] at hi
  nlinarith only [hi]

/-- Both-sided stability in the exact folded-profile square distance. -/
theorem representative_difference_bounds (f g : C_c(ℝ, ℝ)) :
    (Real.log 2 * ∫ x in (0 : ℝ)..1,
      (cellFold (oddCompactSource f) x - cellFold (oddCompactSource g) x) ^ 2) /
        confinementCost 5 ≤ autocorr (representative f - representative g : C_c(ℝ, ℝ)) 0 ∧
      autocorr (representative f - representative g : C_c(ℝ, ℝ)) 0 ≤
        annularEnergyFactor * Real.log 2 * ∫ x in (0 : ℝ)..1,
          (cellFold (oddCompactSource f) x - cellFold (oddCompactSource g) x) ^ 2 := by
  have he := representative_energy_bounds (f - g)
  rw [representative_sub, price_sub] at he
  simpa only [P, mul_assoc] using he

/-- The actual representative's full plastic excess is uniformly equivalent to coherent price. -/
theorem representative_plastic_bounds (f : C_c(ℝ, ℝ)) :
    confinementGap f 5 ≤ plasticCrossover (representative f) + 2 * fiberMoment f ^ 2 ∧
      plasticCrossover (representative f) + 2 * fiberMoment f ^ 2 ≤
        2 * levyCoshPotential screwSignThreshold * annularEnergyFactor * coherentPrice f := by
  have hg := representative_mem_confined f
  have he := plastic_eq_of_mem f (representative f) hg.1
  have hj := (plasticJumpEnergy_bounds (representative f)).2
  have hb := representative_energy_upper f
  refine ⟨confined_plastic_gap f (representative f) 5 hg, ?_⟩
  calc
    plasticCrossover (representative f) + 2 * fiberMoment f ^ 2 =
        2 * plasticJumpEnergy (representative f) := by rw [he]; ring
    _ ≤ 2 * (2 * (∫ x in Ioi 0, levyCoshKernel screwSignThreshold x) * autocorr (representative f) 0) :=
      mul_le_mul_of_nonneg_left hj (by norm_num)
    _ = 2 * levyCoshPotential screwSignThreshold * autocorr (representative f) 0 := by
      rw [integral_levyCoshKernel_Ioi screwSignThreshold_pos]
      ring
    _ ≤ 2 * levyCoshPotential screwSignThreshold * (annularEnergyFactor * coherentPrice f) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num) (levyCoshPotential_pos screwSignThreshold_pos).le)
    _ = _ := by ring

/-- Original signed plastic control retains the explicitly constructed zero-fold component cost. -/
theorem odd_plastic_coherent_kernel_upper (f : C_c(ℝ, ℝ)) :
    plasticCrossover (oddCompactSource f) + 2 * fiberMoment f ^ 2 ≤
      4 * levyCoshPotential screwSignThreshold * annularEnergyFactor * coherentPrice f +
        2 * plasticCrossover (kernelPart f) := by
  have hr : coherentRay f f (-1) = representative f := by
    ext u
    change oddCompactSource f u + -1 * kernelPart f u = representative f u
    rw [kernelPart_apply]
    ring
  have h1 := plastic_coherentRay f f (-1)
  have h2 := plastic_coherentRay f f (-2)
  rw [hr] at h1
  have hl := plastic_lower_bound f (coherentRay f f (-2))
    ⟨oddCompactSource_coherentRay f f (-2), cellFold_coherentRay f f (-2)⟩
  have hu := (representative_plastic_bounds f).2
  norm_num at h1 h2
  nlinarith only [h1, h2, hl, hu]

end
end GaloisForLFunctions.BiScaleUncertainty.AnnularCoherentEnergyBounds
