import GaloisForLFunctions.BiScaleUncertainty.FiniteFilterSchurResidual
import Mathlib.Topology.ContinuousMap.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The exact coherent moment defect as an actual cell variance

Folding the actual sinh multiplier over its dyadic lattice produces a continuous
periodic source. Its cell variance is exactly the remaining signed coherent
moment slack. This energy supplies an unconditional correction to the full
odd plastic bound and classifies equality by constancy of the folded source.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.FoldedHyperbolicCellDefect
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
open CoherentSourceProjection LocalCoherentFilter FiniteFilterSchurResidual
noncomputable section

private def translate (g : C_c(ℝ, ℝ)) (k : ℤ) : C(ℝ, ℝ) :=
  ⟨fun x => g (x + k), g.continuous.comp (continuous_add_const _)⟩

private theorem finite_translates (g : C_c(ℝ, ℝ)) (K : Set ℝ) (hK : IsCompact K) :
    ∃ s : Finset ℤ, ∀ k ∉ s, ∀ x ∈ K, g (x + k) = 0 := by
  classical
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt (multiplierSourceRadius g + R)
  refine ⟨Finset.Icc (-(N : ℤ)) N, ?_⟩
  intro k hk x hx
  by_contra hg
  have hg' := abs_le.mp (abs_le_multiplierSourceRadius g (x + k) hg)
  have hx' := abs_le.mp (show |x| ≤ R by simpa only [Real.norm_eq_abs] using hR x hx)
  apply hk
  rw [Finset.mem_Icc]
  constructor
  · have : -(N : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  · have : (k : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this

private theorem local_norm_summable (g : C_c(ℝ, ℝ)) (K : TopologicalSpace.Compacts ℝ) :
    Summable (fun k : ℤ => ‖(translate g k).restrict K‖) := by
  classical
  obtain ⟨s, hs⟩ := finite_translates g K K.isCompact
  apply summable_of_hasFiniteSupport
  apply s.finite_toSet.subset
  intro k hk
  by_contra hn
  have hz : (translate g k).restrict K = 0 := by
    ext x
    exact hs k hn x x.property
  exact hk (by simp [hz])

private def fold (g : C_c(ℝ, ℝ)) : C(ℝ, ℝ) := ∑' k : ℤ, translate g k

private theorem fold_apply (g : C_c(ℝ, ℝ)) (x : ℝ) :
    fold g x = ∑' k : ℤ, g (x + k) := by
  exact (ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm
    (local_norm_summable g)) x).symm

private theorem fold_periodic (g : C_c(ℝ, ℝ)) : Function.Periodic (fold g) 1 := by
  have he : fold g = ∑' k : ℤ, g.toContinuousMap.comp (ContinuousMap.addRight (k • (1 : ℝ))) := by
    apply tsum_congr
    intro k
    ext x
    simp [translate]
  rw [he]
  exact ContinuousMap.periodic_tsum_comp_add_zsmul g.toContinuousMap (1 : ℝ)

private theorem integral_fold (g : C_c(ℝ, ℝ)) :
    (∫ x in (0 : ℝ)..1, fold g x) = ∫ x, g x := by
  simp_rw [fold_apply]
  change (∫ x in (0 : ℝ)..1, ∑' k : ℤ, translate g k x) = _
  rw [← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm (f := translate g)
    (local_norm_summable g _)]
  exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
    |>.hasSum_intervalIntegral_comp_add_int.tsum_eq

private theorem integral_fold_sq (g : C_c(ℝ, ℝ)) :
    (∫ x in (0 : ℝ)..1, (fold g x) ^ 2) = ∑' k : ℤ, autocorr g k := by
  classical
  let h : C_c(ℝ, ℝ) := ⟨⟨fun x => g x * fold g x,
    g.continuous.mul (fold g).continuous⟩, g.hasCompactSupport.mul_right⟩
  have hp (x : ℝ) : fold h x = (fold g x) ^ 2 := by
    rw [fold_apply]
    have he (k : ℤ) : h (x + k) = g (x + k) * fold g x := by
      change g (x + k) * fold g (x + k) = _
      rw [show x + (k : ℝ) = x + (k : ℝ) * 1 by ring, (fold_periodic g).int_mul k]
    simp_rw [he]
    rw [tsum_mul_right, ← fold_apply, pow_two]
  rw [show (fun x => (fold g x) ^ 2) = (fun x => fold h x) from funext fun x => (hp x).symm,
    integral_fold]
  obtain ⟨s, hs⟩ := finite_translates g (tsupport (g : ℝ → ℝ)) g.hasCompactSupport
  have he (x : ℝ) : h x = ∑ k ∈ s, g x * g (x + k) := by
    change g x * fold g x = _
    by_cases hx : g x = 0
    · simp [hx]
    · rw [fold_apply, tsum_eq_sum (fun k hk => hs k hk x (subset_tsupport _ hx)),
        Finset.mul_sum]
  simp_rw [he]
  have hi (k : ℤ) : Integrable (fun x => g x * g (x + k)) :=
    (g.continuous.mul (translate g k).continuous).integrable_of_hasCompactSupport
      g.hasCompactSupport.mul_right
  rw [integral_finsetSum s (fun k _ => hi k)]
  symm
  apply tsum_eq_sum
  intro k hk
  unfold autocorr
  have hz (x : ℝ) : g x * g (x + k) = 0 := by
    by_cases hx : g x = 0
    · simp [hx]
    · rw [hs k hk x (subset_tsupport _ hx), mul_zero]
  simp_rw [hz]
  simp

private theorem d_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)

private def scaledSinh (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨fun x => sinhCompact (1 / 2) f (Real.log 2 * x),
    (sinhCompact (1 / 2) f).continuous.comp (continuous_const.mul continuous_id)⟩,
    (sinhCompact (1 / 2) f).hasCompactSupport.comp_homeomorph
      (Homeomorph.mulLeft₀ (Real.log 2) d_pos.ne')⟩

/-- The actual sinh multiplier folded onto the unit cell of the dyadic lattice. -/
def cellFold (f : C_c(ℝ, ℝ)) : C(ℝ, ℝ) := fold (scaledSinh f)

/-- Mean of the folded source, with the actual signed odd hyperbolic moment. -/
def cellMean (f : C_c(ℝ, ℝ)) : ℝ :=
  (∫ u, f u * Real.sinh (u / 2)) / Real.log 2

/-- Energy of the concrete continuous residual on a single lattice cell. -/
def cellResidualEnergy (f : C_c(ℝ, ℝ)) : ℝ :=
  ∫ x in (0 : ℝ)..1, (cellFold f x - cellMean f) ^ 2

theorem cellFold_apply (f : C_c(ℝ, ℝ)) (x : ℝ) :
    cellFold f x = ∑' k : ℤ, sinhCompact (1 / 2) f (Real.log 2 * (x + k)) :=
  fold_apply (scaledSinh f) x

theorem cellFold_periodic (f : C_c(ℝ, ℝ)) : Function.Periodic (cellFold f) 1 :=
  fold_periodic (scaledSinh f)

theorem integral_cellFold (f : C_c(ℝ, ℝ)) :
    (∫ x in (0 : ℝ)..1, cellFold f x) = cellMean f := by
  rw [cellFold, integral_fold]
  change (∫ x, sinhCompact (1 / 2) f (Real.log 2 * x)) = _
  rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr d_pos), smul_eq_mul,
    integral_sinhCompact_eq_moment]
  simp only [cellMean, div_eq_mul_inv, mul_comm]

private theorem scaled_autocorr (f : C_c(ℝ, ℝ)) (x : ℝ) :
    autocorr (scaledSinh f) x = (Real.log 2)⁻¹ *
      autocorr (sinhCompact (1 / 2) f) (Real.log 2 * x) := by
  unfold autocorr
  change (∫ u, sinhCompact (1 / 2) f (Real.log 2 * u) *
    sinhCompact (1 / 2) f (Real.log 2 * (u + x))) = _
  simp_rw [mul_add]
  simpa only [abs_of_pos (inv_pos.mpr d_pos), smul_eq_mul] using
    Measure.integral_comp_mul_left
      (fun u => sinhCompact (1 / 2) f u * sinhCompact (1 / 2) f (u + Real.log 2 * x))
      (Real.log 2)

private theorem sinh_lag_zero (f : C_c(ℝ, ℝ)) (k : ℕ) (hk : sourceCutoff f ≤ k) :
    autocorr (sinhCompact (1 / 2) f) (((k : ℝ) + 1) * Real.log 2) = 0 := by
  have hkc : (sourceCutoff f : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hgap := sourceCutoff_gap f
  have hd := d_pos
  have hx : 2 * multiplierSourceRadius f < ((k : ℝ) + 1) * Real.log 2 := by
    nlinarith only [hkc, hgap, hd]
  unfold autocorr
  have hz (u : ℝ) : sinhCompact (1 / 2) f u *
      sinhCompact (1 / 2) f (u + ((k : ℝ) + 1) * Real.log 2) = 0 := by
    by_cases hu : f u = 0
    · change (_ * f u) * _ = 0
      rw [hu, mul_zero, zero_mul]
    by_cases hv : f (u + ((k : ℝ) + 1) * Real.log 2) = 0
    · change _ * (_ * f _) = 0
      rw [hv, mul_zero, mul_zero]
    have hb := abs_le.mp (abs_le_multiplierSourceRadius f u hu)
    have hc := abs_le.mp (abs_le_multiplierSourceRadius f _ hv)
    linarith only [hx, hb.1, hc.2]
  simp_rw [hz]
  simp

private theorem odd_signed_sum (f : C_c(ℝ, ℝ)) :
    (∑' k : ℤ, sourceSample (sinhCompact (1 / 2) (oddCompactSource f)) k) =
      localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f) := by
  rw [localBudget_sub_residualGain]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat
    (sourceSample_neg (sinhCompact (1 / 2) (oddCompactSource f)))
    (summable_of_hasFiniteSupport (sourceSample_finite _))]
  rw [tsum_pnat_eq_tsum_succ (f := fun k : ℕ => sourceSample
    (sinhCompact (1 / 2) (oddCompactSource f)) (k : ℤ))]
  simp only [sourceSample, Int.cast_zero, zero_mul, nsmul_eq_mul]
  push_cast
  rw [tsum_eq_sum (s := Finset.range (sourceCutoff (oddCompactSource f))) (by
    intro k hk
    exact sinh_lag_zero (oddCompactSource f) k (by have := Finset.mem_range.not.mp hk; omega))]
  have he := odd_filter_pairing_identity f
  change _ + _ = _ + _ + centeredFilterPairing (oddCompactSource f)
  change _ = _ + _ + (∫ u, centeredSource (oddCompactSource f) (1 / 2)
    (sourceMean (oddCompactSource f) (1 / 2)) u * sourceFilter (oddCompactSource f) u)
  linarith only [he]

/-- The full signed coherent slope is the square energy of the actual folded multiplier. -/
theorem integral_cellFold_sq (f : C_c(ℝ, ℝ)) :
    (∫ x in (0 : ℝ)..1, (cellFold (oddCompactSource f) x) ^ 2) =
      (localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f)) / Real.log 2 := by
  rw [cellFold, integral_fold_sq]
  simp_rw [scaled_autocorr, mul_comm (Real.log 2)]
  rw [tsum_mul_left]
  change (Real.log 2)⁻¹ * (∑' k : ℤ, sourceSample
    (sinhCompact (1 / 2) (oddCompactSource f)) k) = _
  rw [odd_signed_sum]
  ring

private theorem residual_energy_expand (f : C_c(ℝ, ℝ)) :
    cellResidualEnergy f = (∫ x in (0 : ℝ)..1, (cellFold f x) ^ 2) - cellMean f ^ 2 := by
  have hi : IntervalIntegrable (fun x => cellFold f x) volume 0 1 :=
    (cellFold f).continuous.intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun x => (cellFold f x) ^ 2) volume 0 1 :=
    ((cellFold f).continuous.pow 2).intervalIntegrable 0 1
  have hlin : IntervalIntegrable (fun x => 2 * cellMean f * cellFold f x) volume 0 1 :=
    hi.const_mul _
  have he (x : ℝ) : (cellFold f x - cellMean f) ^ 2 =
      (cellFold f x) ^ 2 - 2 * cellMean f * cellFold f x + cellMean f ^ 2 := by ring
  unfold cellResidualEnergy
  simp_rw [he]
  rw [intervalIntegral.integral_add (hi2.sub hlin) intervalIntegrable_const,
    intervalIntegral.integral_sub hi2 hlin, intervalIntegral.integral_const_mul,
    integral_cellFold, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, one_mul]
  ring

/-- Exact remaining coherent slack, produced by a concrete nonnegative cell energy. -/
theorem cellResidualEnergy_identity (f : C_c(ℝ, ℝ)) :
    (Real.log 2) ^ 2 * cellResidualEnergy (oddCompactSource f) =
      Real.log 2 * (localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f)) -
        (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 := by
  rw [residual_energy_expand, integral_cellFold_sq, cellMean]
  field_simp [d_pos.ne']

theorem cellResidualEnergy_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ cellResidualEnergy f :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)

/-- Equality is constancy of the actual folded source on the closed cell. -/
theorem cellResidualEnergy_eq_zero_iff (f : C_c(ℝ, ℝ)) :
    cellResidualEnergy f = 0 ↔ ∀ x ∈ Icc (0 : ℝ) 1, cellFold f x = cellMean f := by
  have hc : Continuous (fun x => (cellFold f x - cellMean f) ^ 2) :=
    ((cellFold f).continuous.sub continuous_const).pow 2
  constructor
  · intro h
    have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
      (by norm_num : (0 : ℝ) ≤ 1) (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (hc.intervalIntegrable (μ := volume) 0 1)).mp h
    rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc] at hae
    have he := Measure.eqOn_of_ae_eq hae hc.continuousOn continuous_const.continuousOn
      (show Icc (0 : ℝ) 1 ⊆ closure (interior (Icc (0 : ℝ) 1)) by
        rw [closure_interior_Icc (by norm_num : (0 : ℝ) ≠ 1)])
    intro x hx
    have hz : (cellFold f x - cellMean f) ^ 2 = 0 := he hx
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro h
    apply (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
      (by norm_num : (0 : ℝ) ≤ 1) (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (hc.intervalIntegrable (μ := volume) 0 1)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    change (cellFold f x - cellMean f) ^ 2 = 0
    rw [h x (Ioc_subset_Icc_self hx), sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- The precise equality domain of the coherent moment bound. -/
theorem odd_coherent_moment_eq_iff (f : C_c(ℝ, ℝ)) :
    (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 =
      Real.log 2 * (localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f)) ↔
      ∀ x ∈ Icc (0 : ℝ) 1, cellFold (oddCompactSource f) x = cellMean (oddCompactSource f) := by
  rw [← cellResidualEnergy_eq_zero_iff]
  have he := cellResidualEnergy_identity f
  have hd := d_pos
  constructor
  · intro h
    have hz : (Real.log 2) ^ 2 * cellResidualEnergy (oddCompactSource f) = 0 := by linarith only [he, h]
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hd.ne')
  · intro h
    rw [h, mul_zero] at he
    linarith only [he]

/-- Both concrete residuals recover all moment slack in the full odd plastic receiver. -/
theorem odd_plastic_cell_residual_bound (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) - 2 * Real.log 2 * localBudget (oddCompactSource f) +
      2 * Real.log 2 * schurResidualGain (oddCompactSource f) +
      2 * (Real.log 2) ^ 2 * cellResidualEnergy (oddCompactSource f) ≤
        plasticCrossover (oddCompactSource f) := by
  have hp := odd_plasticCrossover_ge_optimized f N
  have he := cellResidualEnergy_identity f
  nlinarith only [hp, he]

end
end GaloisForLFunctions.BiScaleUncertainty.FoldedHyperbolicCellDefect
