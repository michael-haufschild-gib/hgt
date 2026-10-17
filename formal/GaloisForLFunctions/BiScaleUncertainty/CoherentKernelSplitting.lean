import GaloisForLFunctions.BiScaleUncertainty.AnnularCoherentRetraction

/-!
# The actual coherent kernel and plastic-positive source splitting

Every compact odd source splits into its annular representative and a compact
odd zero-fold source. The latter has no moment penalty and satisfies the full
optimized plastic bound. A concrete nonzero kernel family shows that coherent
price cannot control original source energy.
-/

open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.CoherentKernelSplitting
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
open CoherentSourceProjection LocalCoherentFilter FiniteFilterSchurResidual
open FoldedHyperbolicCellDefect CoherentMomentAttainment AnnularCoherentRetraction
open HyperbolicVarianceRigidity
noncomputable section

private abbrev d := Real.log 2
private theorem d_pos : 0 < d := Real.log_pos (by norm_num : (1 : ℝ) < 2)

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
  constructor
  · exact_mod_cast hlo.le
  · exact_mod_cast hhi.le

private theorem fold_add (f g : C_c(ℝ, ℝ)) : cellFold (f + g) = cellFold f + cellFold g := by
  ext x
  simp only [cellFold_apply, ContinuousMap.add_apply]
  have he (k : ℤ) : sinhCompact (1 / 2) (f + g) (d * (x + k)) =
      sinhCompact (1 / 2) f (d * (x + k)) + sinhCompact (1 / 2) g (d * (x + k)) := by
    change _ * (f _ + g _) = _ * f _ + _ * g _
    ring
  simp_rw [he]
  exact (sample_summable f x).tsum_add (sample_summable g x)

private theorem fold_sub (f g : C_c(ℝ, ℝ)) : cellFold (f - g) = cellFold f - cellFold g := by
  ext x
  simp only [cellFold_apply, ContinuousMap.sub_apply]
  change (∑' k : ℤ, Real.sinh ((1 / 2 : ℝ) * (d * (x + k))) *
    (f (d * (x + k)) - g (d * (x + k)))) = _
  simp_rw [mul_sub]
  exact (sample_summable f x).tsum_sub (sample_summable g x)

private theorem fold_smul (a : ℝ) (f : C_c(ℝ, ℝ)) : cellFold (a • f) = a • cellFold f := by
  ext x
  simp only [cellFold_apply, ContinuousMap.smul_apply, smul_eq_mul]
  change (∑' k : ℤ, Real.sinh ((1 / 2 : ℝ) * (d * (x + k))) *
    (a * f (d * (x + k)))) = _
  simp_rw [mul_left_comm _ a]
  rw [tsum_mul_left]
  rfl

private theorem odd_add (f g : C_c(ℝ, ℝ)) :
    oddCompactSource (f + g) = oddCompactSource f + oddCompactSource g := by
  ext u
  change ((f u + g u) - (f (-u) + g (-u))) / 2 =
    (f u - f (-u)) / 2 + (g u - g (-u)) / 2
  ring

private theorem odd_smul (a : ℝ) (f : C_c(ℝ, ℝ)) :
    oddCompactSource (a • f) = a • oddCompactSource f := by
  ext u
  change (a * f u - a * f (-u)) / 2 = a * ((f u - f (-u)) / 2)
  ring

private theorem odd_idempotent (f : C_c(ℝ, ℝ)) :
    oddCompactSource (oddCompactSource f) = oddCompactSource f := by
  ext u
  change (oddCompactSource f u - oddCompactSource f (-u)) / 2 = _
  rw [oddCompactSource_odd]
  ring

private theorem rep_add (f g : C_c(ℝ, ℝ)) : representative (f + g) = representative f + representative g := by
  ext u
  simp only [representative_apply, odd_add, fold_add, ContinuousMap.add_apply,
    CompactlySupportedContinuousMap.add_apply, mul_add]

private theorem rep_smul (a : ℝ) (f : C_c(ℝ, ℝ)) : representative (a • f) = a • representative f := by
  ext u
  simp only [representative_apply, odd_smul, fold_smul, ContinuousMap.smul_apply,
    CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  ring

private theorem rep_odd (f : C_c(ℝ, ℝ)) : representative (oddCompactSource f) = representative f := by
  ext u
  simp only [representative_apply, odd_idempotent]

/-- The actual odd component invisible to the entire coherent fold. -/
def kernelPart (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) := oddCompactSource f - representative f

theorem kernelPart_apply (f : C_c(ℝ, ℝ)) (u : ℝ) :
    kernelPart f u = oddCompactSource f u - representative f u := rfl

theorem kernelPart_odd (f : C_c(ℝ, ℝ)) (u : ℝ) : kernelPart f (-u) = -kernelPart f u := by
  simp only [kernelPart_apply, oddCompactSource_odd, representative_odd]
  ring

theorem oddCompactSource_kernelPart (f : C_c(ℝ, ℝ)) : oddCompactSource (kernelPart f) = kernelPart f := by
  ext u
  change (kernelPart f u - kernelPart f (-u)) / 2 = _
  rw [kernelPart_odd]
  ring

theorem cellFold_kernelPart (f : C_c(ℝ, ℝ)) : cellFold (kernelPart f) = 0 := by
  rw [kernelPart, fold_sub, cellFold_representative, sub_self]

theorem representative_kernelPart (f : C_c(ℝ, ℝ)) : representative (kernelPart f) = 0 := by
  ext u
  simp only [representative_apply, oddCompactSource_kernelPart, cellFold_kernelPart,
    ContinuousMap.zero_apply, mul_zero, CompactlySupportedContinuousMap.zero_apply]

theorem kernelPart_representative (f : C_c(ℝ, ℝ)) : kernelPart (representative f) = 0 := by
  rw [kernelPart, oddCompactSource_representative, representative_idempotent, sub_self]

theorem kernelPart_idempotent (f : C_c(ℝ, ℝ)) : kernelPart (kernelPart f) = kernelPart f := by
  rw [kernelPart, oddCompactSource_kernelPart, representative_kernelPart, sub_zero]

/-- The projection fixes exactly the actual odd sources with zero coherent fold. -/
theorem kernelPart_eq_oddSource_iff (f : C_c(ℝ, ℝ)) :
    kernelPart f = oddCompactSource f ↔ cellFold (oddCompactSource f) = 0 := by
  constructor
  · intro h
    rw [← h, cellFold_kernelPart]
  · intro h
    have hr : representative f = 0 := by
      ext u
      simp only [representative_apply, h, ContinuousMap.zero_apply, mul_zero,
        CompactlySupportedContinuousMap.zero_apply]
    rw [kernelPart, hr, sub_zero]

private theorem kernel_add (f g : C_c(ℝ, ℝ)) : kernelPart (f + g) = kernelPart f + kernelPart g := by
  simp only [kernelPart, odd_add, rep_add]
  abel

private theorem kernel_smul (a : ℝ) (f : C_c(ℝ, ℝ)) : kernelPart (a • f) = a • kernelPart f := by
  rw [kernelPart, odd_smul, rep_smul]
  ext u
  change a * oddCompactSource f u - a * representative f u =
    a * (oddCompactSource f u - representative f u)
  ring

private theorem kernel_odd (f : C_c(ℝ, ℝ)) : kernelPart (oddCompactSource f) = kernelPart f := by
  rw [kernelPart, odd_idempotent, rep_odd]
  rfl

/-- Reconstruction separates full coherent data from its actual zero-fold component. -/
theorem oddSource_decomposition (f : C_c(ℝ, ℝ)) :
    oddCompactSource f = representative f + kernelPart f := by
  unfold kernelPart
  abel

/-- The two actual source coordinates determine the decomposition uniquely. -/
theorem decomposition_eq_iff (f g h : C_c(ℝ, ℝ)) :
    oddCompactSource f = representative g + kernelPart h ↔
      representative f = representative g ∧ kernelPart f = kernelPart h := by
  constructor
  · intro he
    constructor
    · simpa only [rep_odd, rep_add, representative_idempotent, representative_kernelPart, add_zero]
        using congrArg representative he
    · simpa only [kernel_odd, kernel_add, kernelPart_representative, kernelPart_idempotent, zero_add]
        using congrArg kernelPart he
  · rintro ⟨hr, hk⟩
    rw [oddSource_decomposition f, hr, hk]

theorem moment_kernelPart (f : C_c(ℝ, ℝ)) :
    (∫ u, kernelPart f u * Real.sinh (u / 2)) = 0 := by
  have he := integral_cellFold (kernelPart f)
  rw [cellFold_kernelPart] at he
  simp only [ContinuousMap.zero_apply, intervalIntegral.integral_zero, cellMean] at he
  exact (div_eq_zero_iff.mp he.symm).resolve_right d_pos.ne'

theorem exactBudget_kernelPart (f : C_c(ℝ, ℝ)) :
    localBudget (kernelPart f) - schurResidualGain (kernelPart f) = 0 := by
  have he := integral_cellFold_sq (kernelPart f)
  rw [oddCompactSource_kernelPart, cellFold_kernelPart] at he
  simp only [ContinuousMap.zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    intervalIntegral.integral_zero] at he
  exact (div_eq_zero_iff.mp he.symm).resolve_right d_pos.ne'

theorem cellResidualEnergy_kernelPart (f : C_c(ℝ, ℝ)) : cellResidualEnergy (kernelPart f) = 0 := by
  simp only [cellResidualEnergy, cellMean, moment_kernelPart, zero_div, cellFold_kernelPart,
    ContinuousMap.zero_apply, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    intervalIntegral.integral_zero]

/-- The full plastic value of the constructed kernel source has no signed moment term. -/
theorem plastic_kernelPart_eq (f : C_c(ℝ, ℝ)) :
    plasticCrossover (kernelPart f) =
      biScaleSecantEnergy (kernelPart f) + plasticRemainderEnergy (kernelPart f) := by
  have hm := hyperbolicMomentEnergy_oddSource (kernelPart f)
  rw [oddCompactSource_kernelPart, moment_kernelPart] at hm
  rw [plasticCrossover_eq_secant_add_remainder_add_moment, hm]
  ring

/-- Every actual kernel source receives all optimized multiplier bounds without a moment penalty. -/
theorem plastic_kernelPart_bound (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (kernelPart f) N (-y)) +
      plasticRemainderEnergy (kernelPart f) ≤ plasticCrossover (kernelPart f) := by
  have h := odd_plasticCrossover_ge_optimized (kernelPart f) N
  simpa only [oddCompactSource_kernelPart, moment_kernelPart, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, sub_zero] using h

theorem plastic_kernelPart_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ plasticCrossover (kernelPart f) := by
  have hi : 0 ≤ ∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (kernelPart f) 0 (-y) :=
    intervalIntegral.integral_nonneg d_pos.le (fun y _ => optimizedCollar_nonneg _ _ _)
  exact (add_nonneg hi (plasticRemainderEnergy_nonneg _)).trans (plastic_kernelPart_bound f 0)

private def escapedSeed : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => attainingSource 1 ((1 / 2 : ℝ) * u),
    (attainingSource 1).continuous.comp (continuous_const.mul continuous_id)⟩,
    (attainingSource 1).hasCompactSupport.comp_homeomorph
      (Homeomorph.mulLeft₀ (1 / 2 : ℝ) (by norm_num))⟩

private theorem odd_seed : oddCompactSource escapedSeed = escapedSeed := by
  ext u
  change (attainingSource 1 ((1 / 2 : ℝ) * u) - attainingSource 1 ((1 / 2 : ℝ) * -u)) / 2 = _
  rw [mul_neg, attainingSource_odd]
  change (_ - -_) / 2 = attainingSource 1 ((1 / 2 : ℝ) * u)
  ring

private theorem kernel_seed_ne_zero : kernelPart escapedSeed ≠ 0 := by
  have hrep : representative escapedSeed (4 * d) = 0 := by
    by_contra hn
    have hs := (representative_support escapedSeed) hn
    change d < |4 * d| ∧ |4 * d| < 3 * d at hs
    rw [abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 4) d_pos)] at hs
    linarith only [hs.2, d_pos]
  have hA : attainingSource 1 (2 * d) ≠ 0 := by
    rw [attainingSource_apply]
    apply div_ne_zero
    · norm_num [attainmentProfile, mul_div_cancel_right₀ _ d_pos.ne',
        GaloisForLFunctions.HTGeometry.tentReal]
    · apply Real.sinh_ne_zero.mpr
      nlinarith only [d_pos]
  intro hz
  have he := congrArg (fun f : C_c(ℝ, ℝ) => f (4 * d)) hz
  rw [kernelPart_apply, odd_seed, hrep, sub_zero] at he
  change attainingSource 1 ((1 / 2 : ℝ) * (4 * d)) = 0 at he
  rw [show (1 / 2 : ℝ) * (4 * d) = 2 * d by ring] at he
  exact hA he

/-- Explicit amplitude family of nontrivial zero-fold sources. -/
def invisibleSource (a : ℝ) : C_c(ℝ, ℝ) := kernelPart (a • escapedSeed)

private theorem invisible_smul (a : ℝ) : invisibleSource a = a • kernelPart escapedSeed := kernel_smul a _

theorem oddCompactSource_invisibleSource (a : ℝ) : oddCompactSource (invisibleSource a) = invisibleSource a :=
  oddCompactSource_kernelPart _

theorem cellFold_invisibleSource (a : ℝ) : cellFold (invisibleSource a) = 0 := cellFold_kernelPart _

theorem invisibleSource_eq_zero_iff (a : ℝ) : invisibleSource a = 0 ↔ a = 0 := by
  rw [invisible_smul]
  constructor
  · intro h
    by_contra ha
    apply kernel_seed_ne_zero
    ext u
    have he := congrArg (fun f : C_c(ℝ, ℝ) => f u) h
    change a * kernelPart escapedSeed u = 0 at he
    exact (mul_eq_zero.mp he).resolve_left ha
  · intro h
    subst a
    ext u
    change 0 * kernelPart escapedSeed u = 0
    ring

/-- Source energy varies quadratically while the complete coherent fold stays zero. -/
theorem energy_invisibleSource (a : ℝ) :
    autocorr (invisibleSource a) 0 = a ^ 2 * autocorr (invisibleSource 1) 0 := by
  rw [invisible_smul a, invisible_smul 1, one_smul]
  unfold autocorr
  change (∫ u, (a * kernelPart escapedSeed u) * (a * kernelPart escapedSeed (u + 0))) = _
  simp_rw [show ∀ u : ℝ, (a * kernelPart escapedSeed u) * (a * kernelPart escapedSeed (u + 0)) =
    a ^ 2 * (kernelPart escapedSeed u * kernelPart escapedSeed (u + 0)) by intro u; ring]
  exact integral_const_mul _ _

theorem energy_invisibleSource_pos_iff (a : ℝ) : 0 < autocorr (invisibleSource a) 0 ↔ a ≠ 0 := by
  constructor
  · intro hp ha
    have hz := (source_energy_eq_zero_iff (invisibleSource a)).mpr
      ((invisibleSource_eq_zero_iff a).mpr ha)
    linarith only [hp, hz]
  · intro ha
    apply lt_of_le_of_ne (autocorr_zero_nonneg _)
    intro hz
    exact ha ((invisibleSource_eq_zero_iff a).mp
      ((source_energy_eq_zero_iff (invisibleSource a)).mp hz.symm))

theorem exactBudget_invisibleSource (a : ℝ) :
    localBudget (invisibleSource a) - schurResidualGain (invisibleSource a) = 0 := exactBudget_kernelPart _

theorem plastic_invisibleSource_bound (a : ℝ) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (invisibleSource a) N (-y)) +
      plasticRemainderEnergy (invisibleSource a) ≤ plasticCrossover (invisibleSource a) :=
  plastic_kernelPart_bound _ N

theorem plastic_invisibleSource_nonneg (a : ℝ) : 0 ≤ plasticCrossover (invisibleSource a) :=
  plastic_kernelPart_nonneg _

/-- No universal scalar multiple of coherent price controls the original odd source energy. -/
theorem not_energy_le_coherentPrice (c : ℝ) :
    ¬ ∀ f : C_c(ℝ, ℝ), autocorr (oddCompactSource f) 0 ≤
      c * (localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f)) := by
  intro h
  have hb := h (invisibleSource 1)
  rw [oddCompactSource_invisibleSource, exactBudget_invisibleSource, mul_zero] at hb
  have hp := (energy_invisibleSource_pos_iff 1).mpr (by norm_num)
  linarith only [hb, hp]

end
end GaloisForLFunctions.BiScaleUncertainty.CoherentKernelSplitting
