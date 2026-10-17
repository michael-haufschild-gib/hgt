import GaloisForLFunctions.BiScaleUncertainty.OutwardCoherentEscape

/-!
# Sharp plastic infimum in every actual odd coherent class

The outward producer preserves the full fold and approaches the exact moment
floor at an explicit inverse-square rate. The floor is attained precisely in
the zero-fold class; negative members exist precisely for nonzero moment.
-/

open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.CoherentFiberPlasticInfimum
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open _root_.RHTower.WeilLevyCoshCrossover _root_.RHTower.WeilLevyPoleGauss
open GaloisForLFunctions.RHTower
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
open CoherentSourceProjection LocalCoherentFilter FiniteFilterSchurResidual
open FoldedHyperbolicCellDefect AnnularCoherentRetraction HyperbolicVarianceRigidity
open OutwardCoherentEscape
noncomputable section

private abbrev d := Real.log 2
private theorem d_pos : 0 < d := Real.log_pos (by norm_num : (1 : ℝ) < 2)
private abbrev mass : ℝ := ∫ x in Ioi 0, levyCoshKernel screwSignThreshold x

private theorem mass_nonneg : 0 ≤ mass := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro x hx
  exact (levyCoshKernel_pos hx).le

/-- Full coherent fiber inside actual compact continuous odd sources. -/
def coherentFiber (f : C_c(ℝ, ℝ)) : Set C_c(ℝ, ℝ) :=
  {g | oddCompactSource g = g ∧ cellFold g = cellFold (oddCompactSource f)}

/-- Signed hyperbolic moment fixed by the entire coherent fold. -/
def fiberMoment (f : C_c(ℝ, ℝ)) : ℝ := ∫ u, oddCompactSource f u * Real.sinh (u / 2)

/-- Explicit coefficient in the producer's plastic error bound. -/
def plasticEscapeConstant (f : C_c(ℝ, ℝ)) : ℝ :=
  8 * (∫ x in Ioi 0, levyCoshKernel screwSignThreshold x) * escapeEnergy f / (Real.log 2) ^ 2

theorem plasticEscapeConstant_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ plasticEscapeConstant f :=
  div_nonneg (mul_nonneg (mul_nonneg (by norm_num) mass_nonneg) (escapeEnergy_nonneg f)) (sq_nonneg _)

/-- The kernel mass in the coefficient is exactly the known plastic origin potential. -/
theorem plasticEscapeConstant_eq (f : C_c(ℝ, ℝ)) :
    plasticEscapeConstant f =
      4 * levyCoshPotential screwSignThreshold * escapeEnergy f / (Real.log 2) ^ 2 := by
  unfold plasticEscapeConstant
  rw [integral_levyCoshKernel_Ioi screwSignThreshold_pos]
  ring

/-- Unconditional jump bound for every actual compact continuous source. -/
theorem plasticJumpEnergy_bounds (g : C_c(ℝ, ℝ)) :
    0 ≤ plasticJumpEnergy g ∧ plasticJumpEnergy g ≤
      2 * (∫ x in Ioi 0, levyCoshKernel screwSignThreshold x) * autocorr g 0 := by
  constructor
  · apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact mul_nonneg (autocorr_sub_nonneg g.hasCompactSupport g.continuous x)
      (levyCoshKernel_pos hx).le
  · have hi : IntegrableOn (fun x => (2 * autocorr g 0) * levyCoshKernel screwSignThreshold x) (Ioi 0) :=
      (integrableOn_levyCoshKernel_Ioi screwSignThreshold_pos).const_mul _
    have hh := integral_mono_ae (integrableOn_plasticJumpIntegrand g) hi (show
        (fun x => (autocorr g 0 - autocorr g x) * levyCoshKernel screwSignThreshold x) ≤ᵐ[volume.restrict (Ioi 0)]
          (fun x => (2 * autocorr g 0) * levyCoshKernel screwSignThreshold x) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hb := (abs_le.mp (abs_autocorr_le_zero g.hasCompactSupport g.continuous x)).1
      exact mul_le_mul_of_nonneg_right (by linarith only [hb]) (levyCoshKernel_pos hx).le)
    rw [integral_const_mul] at hh
    change plasticJumpEnergy g ≤ 2 * mass * autocorr g 0
    change plasticJumpEnergy g ≤ (2 * autocorr g 0) * mass at hh
    nlinarith only [hh]

theorem escapingSource_mem (f : C_c(ℝ, ℝ)) (n : ℕ) : escapingSource f n ∈ coherentFiber f :=
  ⟨oddCompactSource_escapingSource f n, cellFold_escapingSource f n⟩

theorem moment_eq_of_mem (f g : C_c(ℝ, ℝ)) (hg : g ∈ coherentFiber f) :
    (∫ u, g u * Real.sinh (u / 2)) = fiberMoment f := by
  have he : cellMean g = cellMean (oddCompactSource f) := by
    rw [← integral_cellFold, ← integral_cellFold, hg.2]
  unfold cellMean at he
  field_simp [d_pos.ne'] at he
  exact he

theorem plastic_eq_of_mem (f g : C_c(ℝ, ℝ)) (hg : g ∈ coherentFiber f) :
    plasticCrossover g = 2 * plasticJumpEnergy g - 2 * fiberMoment f ^ 2 := by
  have hm := hyperbolicMomentEnergy_oddSource g
  rw [hg.1, moment_eq_of_mem f g hg] at hm
  rw [plasticCrossover_eq_jump_add_moment, hm]
  ring

theorem plastic_lower_bound (f g : C_c(ℝ, ℝ)) (hg : g ∈ coherentFiber f) :
    -2 * fiberMoment f ^ 2 ≤ plasticCrossover g := by
  rw [plastic_eq_of_mem f g hg]
  linarith only [(plasticJumpEnergy_bounds g).1]

/-- A concrete producer, with zero fold error and an unconditional full-functional error bound. -/
theorem escapingSource_plastic_error (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ plasticCrossover (escapingSource f n) + 2 * fiberMoment f ^ 2 ∧
      plasticCrossover (escapingSource f n) + 2 * fiberMoment f ^ 2 ≤
        plasticEscapeConstant f / ((n : ℝ) + 1) ^ 2 := by
  have he := plastic_eq_of_mem f (escapingSource f n) (escapingSource_mem f n)
  have hj := plasticJumpEnergy_bounds (escapingSource f n)
  change 0 ≤ plasticJumpEnergy (escapingSource f n) ∧
    plasticJumpEnergy (escapingSource f n) ≤ 2 * mass * autocorr (escapingSource f n) 0 at hj
  have hb := escapingSource_energy_bound f n
  have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) mass_nonneg)
  have hc : plasticEscapeConstant f / ((n : ℝ) + 1) ^ 2 =
      4 * mass * (2 * escapeEnergy f / (((n : ℝ) + 1) * d) ^ 2) := by
    unfold plasticEscapeConstant
    dsimp [mass, d]
    field_simp [d_pos.ne', (show (n : ℝ) + 1 ≠ 0 by positivity)]
    ring
  rw [hc]
  constructor <;> nlinarith only [he, hj.1, hj.2, hm]

/-- Every requested accuracy is reached by an explicit member of the outward family. -/
theorem exists_escapingSource_lt (f : C_c(ℝ, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, plasticCrossover (escapingSource f n) < -2 * fiberMoment f ^ 2 + ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (plasticEscapeConstant f / ε)
  have hn' : plasticEscapeConstant f < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
  have hs : (n : ℝ) < ((n : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hp : 0 < ((n : ℝ) + 1) ^ 2 := sq_pos_of_pos (by positivity)
  have he : plasticEscapeConstant f / ((n : ℝ) + 1) ^ 2 < ε := by
    apply (div_lt_iff₀ hp).mpr
    nlinarith only [hn', mul_lt_mul_of_pos_right hs hε]
  exact ⟨n, by linarith only [(escapingSource_plastic_error f n).2, he]⟩

/-- Exact greatest lower bound of the original plastic functional in every full coherent class. -/
theorem plastic_coherentFiber_isGLB (f : C_c(ℝ, ℝ)) :
    IsGLB (plasticCrossover '' coherentFiber f) (-2 * fiberMoment f ^ 2) := by
  constructor
  · rintro y ⟨g, hg, rfl⟩
    exact plastic_lower_bound f g hg
  · intro b hb
    by_contra hn
    have hp : 0 < b - (-2 * fiberMoment f ^ 2) := sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨n, he⟩ := exists_escapingSource_lt f (b - (-2 * fiberMoment f ^ 2)) hp
    have hl := hb ⟨escapingSource f n, escapingSource_mem f n, rfl⟩
    linarith only [he, hl]

private theorem jump_zero_iff (f : C_c(ℝ, ℝ)) : plasticJumpEnergy f = 0 ↔ f = 0 := by
  constructor
  · intro hz
    have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun x => (autocorr f 0 - autocorr f x) * levyCoshKernel screwSignThreshold x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (autocorr_sub_nonneg f.hasCompactSupport f.continuous x)
        (levyCoshKernel_pos hx).le
    have hae := (integral_eq_zero_iff_of_nonneg_ae hn (integrableOn_plasticJumpIntegrand f)).mp hz
    have hΔ : (fun x => autocorr f 0 - autocorr f x) =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
      filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with x hx hpos
      exact (mul_eq_zero.mp hx).resolve_right (levyCoshKernel_pos hpos).ne'
    have he := Measure.eqOn_of_ae_eq hΔ
      (continuous_const.sub (continuous_autocorr_compact f)).continuousOn
      continuous_const.continuousOn (show Ioi (0 : ℝ) ⊆ closure (interior (Ioi (0 : ℝ))) by
        rw [isOpen_Ioi.interior_eq]; exact subset_closure)
    let x := 2 * multiplierSourceRadius f + 1
    have hx : x ∈ Ioi (0 : ℝ) := by
      change 0 < 2 * multiplierSourceRadius f + 1
      linarith [multiplierSourceRadius_pos f]
    have hc : autocorr f x = 0 := by
      unfold autocorr
      have hp (u : ℝ) : f u * f (u + x) = 0 := by
        by_cases hu : f u = 0
        · rw [hu, zero_mul]
        by_cases hv : f (u + x) = 0
        · rw [hv, mul_zero]
        have hb := abs_le.mp (abs_le_multiplierSourceRadius f u hu)
        have hb' := abs_le.mp (abs_le_multiplierSourceRadius f (u + x) hv)
        dsimp [x] at hb'
        linarith only [hb.1, hb'.2]
      simp_rw [hp]
      simp
    have hr : autocorr f 0 = 0 := by simpa only [hc, sub_zero, Pi.zero_apply] using he hx
    exact (source_energy_eq_zero_iff f).mp hr
  · intro hz
    subst f
    simp [plasticJumpEnergy, autocorr]

private theorem fold_zero : cellFold (0 : C_c(ℝ, ℝ)) = 0 := by
  ext x
  simp [cellFold_apply, sinhCompact, sinhMultiplier]

private theorem odd_zero : oddCompactSource (0 : C_c(ℝ, ℝ)) = 0 := by
  ext u
  change ((0 : ℝ) - 0) / 2 = 0
  ring

/-- Nonzero full-fold classes have no global minimizer; the zero-fold class has the zero source. -/
theorem plastic_coherentFiber_attainment_iff (f : C_c(ℝ, ℝ)) :
    (∃ g ∈ coherentFiber f, plasticCrossover g = -2 * fiberMoment f ^ 2) ↔
      cellFold (oddCompactSource f) = 0 := by
  constructor
  · rintro ⟨g, hg, he⟩
    have hz : plasticJumpEnergy g = 0 := by linarith only [plastic_eq_of_mem f g hg, he]
    have hgz := (jump_zero_iff g).mp hz
    have hf := hg.2.symm
    rw [hgz, fold_zero] at hf
    exact hf
  · intro hf
    have hz : (0 : C_c(ℝ, ℝ)) ∈ coherentFiber f := ⟨odd_zero, fold_zero.trans hf.symm⟩
    have hm := moment_eq_of_mem f 0 hz
    simp only [CompactlySupportedContinuousMap.zero_apply, zero_mul, integral_zero] at hm
    refine ⟨0, hz, ?_⟩
    simp [plasticCrossover, autocorr, ← hm]

/-- A full coherent class contains negative plastic sources exactly when its signed moment is nonzero. -/
theorem plastic_coherentFiber_negative_iff (f : C_c(ℝ, ℝ)) :
    (∃ g ∈ coherentFiber f, plasticCrossover g < 0) ↔ fiberMoment f ≠ 0 := by
  constructor
  · rintro ⟨g, hg, hn⟩ hz
    have hl := plastic_lower_bound f g hg
    rw [hz] at hl
    nlinarith only [hn, hl]
  · intro hm
    obtain ⟨n, hn⟩ := exists_escapingSource_lt f (fiberMoment f ^ 2) (sq_pos_of_ne_zero hm)
    refine ⟨escapingSource f n, escapingSource_mem f n, ?_⟩
    nlinarith only [hn, sq_nonneg (fiberMoment f)]

end
end GaloisForLFunctions.BiScaleUncertainty.CoherentFiberPlasticInfimum
