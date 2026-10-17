import GaloisForLFunctions.BiScaleUncertainty.CoherentKernelSplitting

/-!
# Exact plastic minimization along actual coherent-kernel directions

The original signed plastic functional has positive curvature on every nonzero
zero-fold direction. Its exact minimizing source preserves the complete coherent
fold and transfers a quantified gain into the original optimized plastic bound.
All constructions include the zero-direction case without extra premises.
-/

open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.PlasticCoherentLineMinimizer
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open _root_.RHTower.WeilLevyCoshCrossover _root_.RHTower.WeilLevyPoleGauss
open GaloisForLFunctions.RHTower
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
open CoherentSourceProjection LocalCoherentFilter FiniteFilterSchurResidual
open FoldedHyperbolicCellDefect CoherentMomentAttainment AnnularCoherentRetraction
open HyperbolicVarianceRigidity CoherentKernelSplitting
noncomputable section

private abbrev d := Real.log 2
private theorem d_pos : 0 < d := Real.log_pos (by norm_num : (1 : ℝ) < 2)

private theorem plastic_zero : plasticCrossover (0 : C_c(ℝ, ℝ)) = 0 := by
  simp [plasticCrossover, autocorr]

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

private theorem kernel_plastic_jump (g : C_c(ℝ, ℝ)) :
    plasticCrossover (kernelPart g) = 2 * plasticJumpEnergy (kernelPart g) := by
  have hm := hyperbolicMomentEnergy_oddSource (kernelPart g)
  rw [oddCompactSource_kernelPart, moment_kernelPart] at hm
  rw [plasticCrossover_eq_jump_add_moment, hm]
  ring

/-- The actual kernel has no nonzero plastic-null direction. -/
theorem plastic_kernelPart_eq_zero_iff (g : C_c(ℝ, ℝ)) :
    plasticCrossover (kernelPart g) = 0 ↔ kernelPart g = 0 := by
  rw [kernel_plastic_jump, mul_eq_zero, jump_zero_iff]
  norm_num

theorem plastic_kernelPart_pos_iff (g : C_c(ℝ, ℝ)) :
    0 < plasticCrossover (kernelPart g) ↔ kernelPart g ≠ 0 := by
  constructor
  · intro hp hz
    have he := (plastic_kernelPart_eq_zero_iff g).mpr hz
    linarith only [hp, he]
  · intro hn
    apply lt_of_le_of_ne (plastic_kernelPart_nonneg g)
    intro hz
    exact hn ((plastic_kernelPart_eq_zero_iff g).mp hz.symm)

private def originIntegrand (f : C_c(ℝ, ℝ)) (u : ℝ) : ℝ := f u * f u

private theorem origin_integrable (f : C_c(ℝ, ℝ)) : Integrable (originIntegrand f) :=
  (f.continuous.mul f.continuous).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right

private theorem origin_quadratic (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    autocorr (f + t • g : C_c(ℝ, ℝ)) 0 = (1 - t) * autocorr f 0 +
      (t ^ 2 - t) * autocorr g 0 + t * autocorr (f + g : C_c(ℝ, ℝ)) 0 := by
  have he (u : ℝ) : originIntegrand (f + t • g) u = (1 - t) * originIntegrand f u +
      (t ^ 2 - t) * originIntegrand g u + t * originIntegrand (f + g) u := by
    change (f u + t * g u) * (f u + t * g u) =
      (1 - t) * (f u * f u) + (t ^ 2 - t) * (g u * g u) + t * ((f u + g u) * (f u + g u))
    ring
  have hi : (∫ u, originIntegrand (f + t • g) u) =
      (1 - t) * (∫ u, originIntegrand f u) + (t ^ 2 - t) * (∫ u, originIntegrand g u) +
        t * (∫ u, originIntegrand (f + g) u) := by
    have h1 : Integrable (fun u : ℝ => (1 - t) * originIntegrand f u) := (origin_integrable f).const_mul _
    have h2 : Integrable (fun u : ℝ => (t ^ 2 - t) * originIntegrand g u) := (origin_integrable g).const_mul _
    have h3 : Integrable (fun u : ℝ => t * originIntegrand (f + g) u) := (origin_integrable (f + g)).const_mul _
    have h12 : Integrable (fun u : ℝ => (1 - t) * originIntegrand f u +
        (t ^ 2 - t) * originIntegrand g u) := h1.add h2
    simp_rw [he]
    rw [integral_add h12 h3, integral_add h1 h2]
    simp only [integral_const_mul]
  simpa only [autocorr, add_zero, originIntegrand] using hi

private def residualPair (f : C_c(ℝ, ℝ)) (p : ℝ × ℝ) : ℝ :=
  f p.1 * f p.2 *
    (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|)

private theorem pair_integrable (f : C_c(ℝ, ℝ)) : Integrable (residualPair f) :=
  integrable_plasticResidualPair f

private theorem pair_quadratic (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    (∫ p, residualPair (f + t • g) p) = (1 - t) * (∫ p, residualPair f p) +
      (t ^ 2 - t) * (∫ p, residualPair g p) + t * (∫ p, residualPair (f + g) p) := by
  have he (p : ℝ × ℝ) : residualPair (f + t • g) p = (1 - t) * residualPair f p +
      (t ^ 2 - t) * residualPair g p + t * residualPair (f + g) p := by
    simp only [residualPair, CompactlySupportedContinuousMap.add_apply,
      CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
    ring
  have h1 : Integrable (fun p : ℝ × ℝ => (1 - t) * residualPair f p) := (pair_integrable f).const_mul _
  have h2 : Integrable (fun p : ℝ × ℝ => (t ^ 2 - t) * residualPair g p) := (pair_integrable g).const_mul _
  have h3 : Integrable (fun p : ℝ × ℝ => t * residualPair (f + g) p) := (pair_integrable (f + g)).const_mul _
  have h12 : Integrable (fun p : ℝ × ℝ => (1 - t) * residualPair f p +
      (t ^ 2 - t) * residualPair g p) := h1.add h2
  simp_rw [he]
  rw [integral_add h12 h3, integral_add h1 h2]
  simp only [integral_const_mul]

/-- Exact quadratic law for the original signed pair functional, with integrability discharged. -/
theorem plastic_add_smul (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    plasticCrossover (f + t • g) = (1 - t) * plasticCrossover f +
      (t ^ 2 - t) * plasticCrossover g + t * plasticCrossover (f + g) := by
  have hp := pair_quadratic f g t
  have ho := origin_quadratic f g t
  unfold plasticCrossover
  change _ + (∫ p, residualPair (f + t • g) p) =
    (1 - t) * (_ + (∫ p, residualPair f p)) +
      (t ^ 2 - t) * (_ + (∫ p, residualPair g p)) + t * (_ + (∫ p, residualPair (f + g) p))
  rw [hp, ho]
  ring

private theorem sample_summable (f : C_c(ℝ, ℝ)) (x : ℝ) :
    Summable (fun k : ℤ => sinhCompact (1 / 2) f (d * (x + k))) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (multiplierSourceRadius f / d + |x|)
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) N)).subset
  intro k hk
  have hf : f (d * (x + k)) ≠ 0 := by
    intro hz
    exact hk (by change Real.sinh _ * f _ = 0; rw [hz, mul_zero])
  have hb := abs_le.mp (abs_le_multiplierSourceRadius f _ hf)
  have hNd : multiplierSourceRadius f + |x| * d < (N : ℝ) * d := by
    have h := mul_lt_mul_of_pos_right hN d_pos
    rw [add_mul, div_mul_cancel₀ _ d_pos.ne'] at h
    exact h
  have hxlo := mul_le_mul_of_nonneg_left (neg_le_abs x) d_pos.le
  have hxhi := mul_le_mul_of_nonneg_left (le_abs_self x) d_pos.le
  have hlo : -(N : ℝ) < (k : ℝ) := (mul_lt_mul_iff_right₀ d_pos).mp (by nlinarith only [hb.1, hNd, hxhi])
  have hhi : (k : ℝ) < (N : ℝ) := (mul_lt_mul_iff_right₀ d_pos).mp (by nlinarith only [hb.2, hNd, hxlo])
  rw [Finset.mem_coe, Finset.mem_Icc]
  exact ⟨by exact_mod_cast hlo.le, by exact_mod_cast hhi.le⟩

theorem cellFold_add_smul (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    cellFold (f + t • g) = cellFold f + t • cellFold g := by
  ext x
  simp only [cellFold_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  have he (k : ℤ) : sinhCompact (1 / 2) (f + t • g) (d * (x + k)) =
      sinhCompact (1 / 2) f (d * (x + k)) + t * sinhCompact (1 / 2) g (d * (x + k)) := by
    change _ * (f _ + t * g _) = _ * f _ + t * (_ * g _)
    ring
  simp_rw [he]
  rw [(sample_summable f x).tsum_add (Summable.mul_left t (sample_summable g x)), tsum_mul_left]

/-- An actual compact odd line contained in one full coherent fold class. -/
def coherentRay (f g : C_c(ℝ, ℝ)) (t : ℝ) : C_c(ℝ, ℝ) := oddCompactSource f + t • kernelPart g

theorem coherentRay_odd (f g : C_c(ℝ, ℝ)) (t u : ℝ) :
    coherentRay f g t (-u) = -coherentRay f g t u := by
  change oddCompactSource f (-u) + t * kernelPart g (-u) =
    -(oddCompactSource f u + t * kernelPart g u)
  have hf := oddCompactSource_odd f u
  have hg := kernelPart_odd g u
  change oddCompactSource f (-u) = -(oddCompactSource f u) at hf
  change kernelPart g (-u) = -(kernelPart g u) at hg
  rw [hf, hg]
  ring

theorem oddCompactSource_coherentRay (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    oddCompactSource (coherentRay f g t) = coherentRay f g t := by
  ext u
  change (coherentRay f g t u - coherentRay f g t (-u)) / 2 = _
  rw [coherentRay_odd]
  ring

theorem cellFold_coherentRay (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    cellFold (coherentRay f g t) = cellFold (oddCompactSource f) := by
  rw [coherentRay, cellFold_add_smul, cellFold_kernelPart, smul_zero, add_zero]

theorem moment_coherentRay (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    (∫ u, coherentRay f g t u * Real.sinh (u / 2)) =
      ∫ u, oddCompactSource f u * Real.sinh (u / 2) := by
  have he : cellMean (coherentRay f g t) = cellMean (oddCompactSource f) := by
    rw [← integral_cellFold, ← integral_cellFold, cellFold_coherentRay]
  unfold cellMean at he
  field_simp [d_pos.ne'] at he
  exact he

theorem exactBudget_coherentRay (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    localBudget (coherentRay f g t) - schurResidualGain (coherentRay f g t) =
      localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f) := by
  have hr := integral_cellFold_sq (coherentRay f g t)
  rw [oddCompactSource_coherentRay, cellFold_coherentRay] at hr
  have he := hr.symm.trans (integral_cellFold_sq f)
  field_simp [d_pos.ne'] at he
  exact he

/-- The exact mixed plastic coefficient of the original odd source and actual kernel direction. -/
def directionPair (f g : C_c(ℝ, ℝ)) : ℝ :=
  (plasticCrossover (oddCompactSource f + kernelPart g) - plasticCrossover (oddCompactSource f) -
    plasticCrossover (kernelPart g)) / 2

theorem plastic_coherentRay (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    plasticCrossover (coherentRay f g t) = plasticCrossover (oddCompactSource f) +
      2 * t * directionPair f g + t ^ 2 * plasticCrossover (kernelPart g) := by
  rw [coherentRay, plastic_add_smul]
  unfold directionPair
  ring

/-- The exact step, with total division handling the zero source direction. -/
def optimalStep (f g : C_c(ℝ, ℝ)) : ℝ := -directionPair f g / plasticCrossover (kernelPart g)

/-- The attained minimizing source on the prescribed actual coherent line. -/
def correctedSource (f g : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) := coherentRay f g (optimalStep f g)

/-- The exact recovered plastic energy, not an estimated receiver slack. -/
def correctionGain (f g : C_c(ℝ, ℝ)) : ℝ := directionPair f g ^ 2 / plasticCrossover (kernelPart g)

private theorem pair_zero (f g : C_c(ℝ, ℝ)) (hg : kernelPart g = 0) : directionPair f g = 0 := by
  rw [directionPair, hg, add_zero, plastic_zero]
  ring

private theorem ray_zero (f g : C_c(ℝ, ℝ)) (t : ℝ) (hg : kernelPart g = 0) :
    coherentRay f g t = oddCompactSource f := by
  rw [coherentRay, hg, smul_zero, add_zero]

theorem correctionGain_nonneg (f g : C_c(ℝ, ℝ)) : 0 ≤ correctionGain f g :=
  div_nonneg (sq_nonneg _) (plastic_kernelPart_nonneg g)

theorem cellFold_correctedSource (f g : C_c(ℝ, ℝ)) :
    cellFold (correctedSource f g) = cellFold (oddCompactSource f) := cellFold_coherentRay _ _ _

theorem moment_correctedSource (f g : C_c(ℝ, ℝ)) :
    (∫ u, correctedSource f g u * Real.sinh (u / 2)) =
      ∫ u, oddCompactSource f u * Real.sinh (u / 2) := moment_coherentRay _ _ _

theorem exactBudget_correctedSource (f g : C_c(ℝ, ℝ)) :
    localBudget (correctedSource f g) - schurResidualGain (correctedSource f g) =
      localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f) := exactBudget_coherentRay _ _ _

/-- The constructed source realizes the exact full-functional correction gain. -/
theorem plastic_correctedSource (f g : C_c(ℝ, ℝ)) :
    plasticCrossover (correctedSource f g) = plasticCrossover (oddCompactSource f) - correctionGain f g := by
  by_cases hg : kernelPart g = 0
  · rw [correctedSource, ray_zero f g _ hg]
    simp only [correctionGain, pair_zero f g hg, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, sub_zero]
  · have hq := (plastic_kernelPart_pos_iff g).mpr hg
    rw [correctedSource, plastic_coherentRay]
    unfold optimalStep correctionGain
    field_simp [hq.ne']
    ring

/-- An exact square defect certifies the global minimum along the whole signed source line. -/
theorem plastic_coherentRay_square (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    plasticCrossover (coherentRay f g t) = plasticCrossover (correctedSource f g) +
      plasticCrossover (kernelPart g) * (t - optimalStep f g) ^ 2 := by
  by_cases hg : kernelPart g = 0
  · rw [ray_zero f g t hg, correctedSource, ray_zero f g _ hg, hg, plastic_zero]
    ring
  · have hq := (plastic_kernelPart_pos_iff g).mpr hg
    rw [plastic_coherentRay, plastic_correctedSource]
    unfold correctionGain optimalStep
    field_simp [hq.ne']
    ring

theorem correctedSource_minimal (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    plasticCrossover (correctedSource f g) ≤ plasticCrossover (coherentRay f g t) := by
  rw [plastic_coherentRay_square]
  have h := mul_nonneg (plastic_kernelPart_nonneg g) (sq_nonneg (t - optimalStep f g))
  linarith only [h]

theorem coherentRay_minimal_iff (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    plasticCrossover (coherentRay f g t) = plasticCrossover (correctedSource f g) ↔
      kernelPart g = 0 ∨ t = optimalStep f g := by
  rw [plastic_coherentRay_square]
  constructor
  · intro h
    have hz : plasticCrossover (kernelPart g) * (t - optimalStep f g) ^ 2 = 0 := by linarith only [h]
    rcases mul_eq_zero.mp hz with hq | ht
    · exact Or.inl ((plastic_kernelPart_eq_zero_iff g).mp hq)
    · exact Or.inr (sub_eq_zero.mp (sq_eq_zero_iff.mp ht))
  · rintro (hg | ht)
    · rw [(plastic_kernelPart_eq_zero_iff g).mpr hg]
      ring
    · rw [ht]
      ring

theorem correctionGain_pos_iff (f g : C_c(ℝ, ℝ)) : 0 < correctionGain f g ↔ directionPair f g ≠ 0 := by
  constructor
  · intro hp hz
    simp only [correctionGain, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div] at hp
    exact (lt_irrefl 0) hp
  · intro hb
    have hg : kernelPart g ≠ 0 := fun h => hb (pair_zero f g h)
    have hs : 0 < directionPair f g ^ 2 := by
      apply lt_of_le_of_ne (sq_nonneg _)
      intro hz
      exact hb (sq_eq_zero_iff.mp hz.symm)
    exact div_pos hs ((plastic_kernelPart_pos_iff g).mpr hg)

theorem correctedSource_strict_iff (f g : C_c(ℝ, ℝ)) :
    plasticCrossover (correctedSource f g) < plasticCrossover (oddCompactSource f) ↔ directionPair f g ≠ 0 := by
  rw [plastic_correctedSource, ← correctionGain_pos_iff]
  constructor <;> intro h <;> linarith only [h]

/-- The actual minimizing source transfers its exact gain to the original full plastic receiver. -/
theorem odd_plastic_corrected_bound (f g : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (correctedSource f g) N (-y)) +
      plasticRemainderEnergy (correctedSource f g) -
      2 * (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 + correctionGain f g ≤
        plasticCrossover (oddCompactSource f) := by
  have hp := odd_plasticCrossover_ge_optimized (correctedSource f g) N
  have ho : oddCompactSource (correctedSource f g) = correctedSource f g := oddCompactSource_coherentRay _ _ _
  rw [ho, moment_correctedSource, plastic_correctedSource] at hp
  linarith only [hp]

end
end GaloisForLFunctions.BiScaleUncertainty.PlasticCoherentLineMinimizer
