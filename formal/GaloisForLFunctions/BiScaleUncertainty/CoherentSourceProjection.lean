import GaloisForLFunctions.BiScaleUncertainty.SignedCoherentMomentReceiver

/-!
# An explicit coherent producer cancels the leading source component

Normalize the actual dyadic difference packet and subtract its limiting source
component. Compact correlation support gives an exact affine covariance law,
and the producer has an unconditional signed inverse-length energy error.
Its asymptotic energy improves the odd moment and full plastic bounds.
-/

open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported Topology

namespace GaloisForLFunctions.BiScaleUncertainty.CoherentSourceProjection
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicMultiplierFrame DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
noncomputable section

private def covarianceSample (f : C_c(ℝ, ℝ)) (k : ℕ) : ℝ :=
  sourceSample f ((k : ℤ) + 1) / Real.cosh ((((k : ℝ) + 1) * Real.log 2) / 2)

/-- Leading covariance of the uniform difference packet per source site. -/
def covarianceMass (f : C_c(ℝ, ℝ)) : ℝ := ∑' k : ℕ, covarianceSample f k

/-- Exact finite boundary intercept in the source covariance. -/
def covarianceFirstMoment (f : C_c(ℝ, ℝ)) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) + 1) * covarianceSample f k

private theorem covariance_support_finite (f : C_c(ℝ, ℝ)) :
    (Function.support (covarianceSample f)).Finite := by
  apply ((sourceSample_finite f).preimage (f := fun k : ℕ => (k : ℤ) + 1) (by
    intro a _ b _ h
    change (a : ℤ) + 1 = (b : ℤ) + 1 at h
    omega)).subset
  intro k hk
  change sourceSample f ((k : ℤ) + 1) ≠ 0
  intro hz
  exact hk (by simp [covarianceSample, hz])

private theorem covariance_eq_triangle (f : C_c(ℝ, ℝ)) (N : ℕ) :
    packetCovariance f (pairSet N)
      (differenceWeight (1 / 2) (fun _ => 1) (chainNode (Real.log 2)))
      (differenceNode (chainNode (Real.log 2))) =
        ∑ k ∈ Finset.range N, ((N : ℝ) - k) * covarianceSample f k := by
  let a := lagAmplitude N (1 / 2) (Real.log 2) (fun _ => 1)
  let H := fun r => a r * autocorr f (lagNode N (Real.log 2) r)
  have hrev : (∑ r ∈ Finset.range N, H r) =
      ∑ k ∈ Finset.range N, H (N + (k + 1)) := by
    rw [← Finset.sum_range_reflect H N]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have ha := lagAmplitude_reflect N (1 / 2) (Real.log 2) (fun _ => 1)
      (N - 1 - k) (by omega)
    rw [show 2 * N - (N - 1 - k) = N + (k + 1) by omega] at ha
    have hn : lagNode N (Real.log 2) (N - 1 - k) =
        -lagNode N (Real.log 2) (N + (k + 1)) := by
      unfold lagNode
      rw [show N - 1 - k = N - (k + 1) by omega, Nat.cast_sub (by omega)]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    dsimp [H, a]
    rw [hn, autocorr_neg, ha]
  have ht : (∑ r ∈ Finset.range (N + 1), H (N + r)) =
      ∑ k ∈ Finset.range N, H (N + (k + 1)) := by
    rw [Finset.sum_range_succ']
    simp [H, a, lagAmplitude_center]
  have hsum := Finset.sum_range_add H N (N + 1)
  rw [show N + (N + 1) = 2 * N + 1 by omega, ht] at hsum
  rw [packetCovariance_eq_lags]
  change (∑ r ∈ Finset.range (2 * N + 1), H r) = _
  rw [hsum, hrev, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  dsimp [H, a]
  rw [lagAmplitude_positive_one _ _ _ _ (by omega) (by omega)]
  have hn : lagNode N (Real.log 2) (N + (k + 1)) = ((k : ℝ) + 1) * Real.log 2 := by
    simp only [lagNode, Nat.cast_add, Nat.cast_one]
    ring
  rw [hn]
  simp only [covarianceSample, sourceSample, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [Nat.cast_sub (by omega : k + 1 ≤ N + 1)]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (1 / 2 : ℝ) * (((k : ℝ) + 1) * Real.log 2) =
    (((k : ℝ) + 1) * Real.log 2) / 2 by ring]
  ring

/-- Once source support is exhausted, covariance is exactly affine in length. -/
theorem covariance_eventually_affine (f : C_c(ℝ, ℝ)) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      packetCovariance f (pairSet N)
        (differenceWeight (1 / 2) (fun _ => 1) (chainNode (Real.log 2)))
        (differenceNode (chainNode (Real.log 2))) =
          ((N : ℝ) + 1) * covarianceMass f - covarianceFirstMoment f := by
  obtain ⟨M, hM⟩ := (covariance_support_finite f).bddAbove
  refine ⟨M + 1, ?_⟩
  intro N hN
  have hz (k : ℕ) (hk : k ∉ Finset.range N) : covarianceSample f k = 0 := by
    by_contra hn
    have hb := hM (Function.mem_support.mpr hn)
    have := Finset.mem_range.not.mp hk
    omega
  have hs : covarianceMass f = ∑ k ∈ Finset.range N, covarianceSample f k := tsum_eq_sum hz
  have ht : covarianceFirstMoment f =
      ∑ k ∈ Finset.range N, ((k : ℝ) + 1) * covarianceSample f k :=
    tsum_eq_sum (by intro k hk; rw [hz k hk, mul_zero])
  rw [covariance_eq_triangle, hs, ht, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

private def compactPacket {ι : Type*} (f : C_c(ℝ, ℝ)) (s : Finset ι)
    (w t : ι → ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => ∑ i ∈ s, w i * f (u + t i),
    continuous_finsetSum s fun i _ =>
      continuous_const.mul (f.continuous.comp (continuous_add_const (t i)))⟩, by
    have hs := HasCompactSupport.finset_sum (s := s)
      (f := fun i u => w i * f (u + t i))
      (fun i _ => (hasCompactSupport_comp_add f.hasCompactSupport (t i)).mul_left)
    have he : (∑ i ∈ s, fun u => w i * f (u + t i)) =
        (fun u => ∑ i ∈ s, w i * f (u + t i)) := by
      funext u
      simp only [Finset.sum_apply]
    rwa [he] at hs⟩

/-- Actual dyadic difference packet before normalization and source cancellation. -/
def differencePacket (f : C_c(ℝ, ℝ)) (N : ℕ) : C_c(ℝ, ℝ) :=
  compactPacket f (pairSet N)
    (differenceWeight (1 / 2) (fun _ => 1) (chainNode (Real.log 2)))
    (differenceNode (chainNode (Real.log 2)))

/-- A concrete producer: normalize the difference packet and cancel its leading source part. -/
def coherentProducer (f : C_c(ℝ, ℝ)) (N : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => differencePacket f N u / ((N : ℝ) + 1) - covarianceMass f / autocorr f 0 * f u,
    ((differencePacket f N).continuous.div_const _).sub (continuous_const.mul f.continuous)⟩,
    by
      change HasCompactSupport (fun u => differencePacket f N u * ((N : ℝ) + 1)⁻¹ -
        covarianceMass f / autocorr f 0 * f u)
      exact (differencePacket f N).hasCompactSupport.mul_right.sub f.hasCompactSupport.mul_left⟩

private theorem pairing_packet {ι : Type*} (f q : C_c(ℝ, ℝ))
    (s : Finset ι) (w t : ι → ℝ) :
    (∫ u, q u * compactPacket f s w t u) =
      ∑ i ∈ s, w i * (∫ u, q u * f (u + t i)) := by
  have hi (i : ι) : Integrable (fun u => w i * (q u * f (u + t i))) :=
    ((q.continuous.mul (f.continuous.comp (continuous_add_const (t i)))).integrable_of_hasCompactSupport
      q.hasCompactSupport.mul_right).const_mul _
  have he : (fun u => q u * compactPacket f s w t u) =
      fun u => ∑ i ∈ s, w i * (q u * f (u + t i)) := by
    funext u
    change q u * (∑ i ∈ s, w i * f (u + t i)) = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [he, integral_finsetSum _ (fun i _ => hi i)]
  exact Finset.sum_congr rfl fun _ _ => integral_const_mul _ _

private theorem packet_energy (f : C_c(ℝ, ℝ)) (N : ℕ) :
    autocorr (differencePacket f N) 0 =
      translationGramEnergy f (pairSet N)
        (differenceWeight (1 / 2) (fun _ => 1) (chainNode (Real.log 2)))
        (differenceNode (chainNode (Real.log 2))) := by
  rw [← integral_sq_eq_autocorr_zero, translationGramEnergy_eq_integral]
  rfl

private theorem producer_pairing (f q : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ u, q u * coherentProducer f N u) =
      (∫ u, q u * differencePacket f N u) / ((N : ℝ) + 1) -
        covarianceMass f / autocorr f 0 * (∫ u, q u * f u) := by
  have hp : Integrable (fun u => q u * differencePacket f N u) :=
    (q.continuous.mul (differencePacket f N).continuous).integrable_of_hasCompactSupport
      q.hasCompactSupport.mul_right
  have hf : Integrable (fun u => q u * f u) :=
    (q.continuous.mul f.continuous).integrable_of_hasCompactSupport q.hasCompactSupport.mul_right
  have he : (fun u => q u * coherentProducer f N u) =
      fun u => (q u * differencePacket f N u) / ((N : ℝ) + 1) -
        covarianceMass f / autocorr f 0 * (q u * f u) := by
    funext u
    change q u * (_ / _ - _ * _) = _
    ring
  rw [he, integral_sub (hp.div_const _) (hf.const_mul _), integral_div, integral_const_mul]

/-- Exact energy of the actual producer, including all signed covariance terms. -/
theorem coherentProducer_energy (f : C_c(ℝ, ℝ)) (N : ℕ) :
    autocorr (coherentProducer f N) 0 =
      autocorr (differencePacket f N) 0 / ((N : ℝ) + 1) ^ 2 -
        2 * (covarianceMass f / autocorr f 0) *
          packetCovariance f (pairSet N)
            (differenceWeight (1 / 2) (fun _ => 1) (chainNode (Real.log 2)))
            (differenceNode (chainNode (Real.log 2))) / ((N : ℝ) + 1) +
        covarianceMass f ^ 2 / autocorr f 0 := by
  have he (p q : C_c(ℝ, ℝ)) : (∫ u, p u * q u) = ∫ u, q u * p u := by
    simp only [mul_comm]
  have hs (p : C_c(ℝ, ℝ)) : (∫ u, p u * p u) = autocorr p 0 := by
    simp only [autocorr, add_zero]
  rw [← hs, producer_pairing, he (coherentProducer f N), producer_pairing,
    he (coherentProducer f N), producer_pairing, hs, hs, he (differencePacket f N) f]
  have hp : (∫ u, f u * differencePacket f N u) =
      packetCovariance f (pairSet N)
        (differenceWeight (1 / 2) (fun _ => 1) (chainNode (Real.log 2)))
        (differenceNode (chainNode (Real.log 2))) := by
    rw [differencePacket, pairing_packet]
    rfl
  rw [hp]
  by_cases hR : autocorr f 0 = 0
  · simp only [hR, div_zero, zero_mul, mul_zero, zero_div, sub_zero, add_zero, div_div, pow_two]
  · field_simp
    ring

/-- The asymptotic source-orthogonal energy price. -/
def projectedEnergy (f : C_c(ℝ, ℝ)) : ℝ :=
  2 * correlationMass f - covarianceMass f ^ 2 / autocorr f 0

/-- Signed coefficient of the explicit inverse-length producer error. -/
def producerBoundary (f : C_c(ℝ, ℝ)) : ℝ :=
  2 * covarianceMass f * covarianceFirstMoment f / autocorr f 0

/-- Unconditional energy error for the explicit producer; the boundary term keeps its sign. -/
theorem coherentProducer_eventually_energy_le (f : C_c(ℝ, ℝ)) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      autocorr (coherentProducer f N) 0 ≤ projectedEnergy f + producerBoundary f / ((N : ℝ) + 1) := by
  obtain ⟨M, hM⟩ := covariance_eventually_affine f
  refine ⟨M, ?_⟩
  intro N hN
  have hm : 0 < (N : ℝ) + 1 := by positivity
  have hG := (differenceGram_le_lattice f N (fun _ => 1)).trans
    (mul_le_mul_of_nonneg_left (dyadic_collisionEnergy_le N (fun _ => 1))
      (correlationMass_nonneg f))
  simp only [weightEnergy, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] at hG
  have hdiv : autocorr (differencePacket f N) 0 / ((N : ℝ) + 1) ^ 2 ≤ 2 * correlationMass f := by
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    rw [packet_energy]
    nlinarith only [hG]
  have he : autocorr (coherentProducer f N) 0 =
      autocorr (differencePacket f N) 0 / ((N : ℝ) + 1) ^ 2 -
        covarianceMass f ^ 2 / autocorr f 0 + producerBoundary f / ((N : ℝ) + 1) := by
    rw [coherentProducer_energy, hM N hN]
    unfold producerBoundary
    by_cases hR : autocorr f 0 = 0
    · simp [hR]
    · field_simp
      ring
  rw [he]
  unfold projectedEnergy
  linarith only [hdiv]

private theorem inverse_length_tendsto :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

private theorem boundary_tendsto (a b : ℝ) :
    Tendsto (fun N : ℕ => a + b / ((N : ℝ) + 1)) atTop (𝓝 a) := by
  simpa only [div_eq_mul_inv, mul_zero, add_zero] using
    tendsto_const_nhds.add (inverse_length_tendsto.const_mul b)

/-- Nonnegative limiting price is forced by the constructed producers, not assumed. -/
theorem projectedEnergy_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ projectedEnergy f := by
  obtain ⟨M, hM⟩ := coherentProducer_eventually_energy_le f
  apply ge_of_tendsto (boundary_tendsto (projectedEnergy f) (producerBoundary f))
  exact eventually_atTop.mpr ⟨M, fun N hN => (autocorr_zero_nonneg _).trans (hM N hN)⟩

/-- Improved coherent moment price obtained from the explicit producers. -/
def projectedBudget (f : C_c(ℝ, ℝ)) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 + signedCorrectionMass f +
    Real.sqrt (autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * projectedEnergy f)

private theorem odd_gram_le_producer (f : C_c(ℝ, ℝ)) (N : ℕ) :
    translationGramEnergy (sinhCompact (1 / 2) (oddCompactSource f))
      (Finset.range (N + 1)) (fun _ => 1) (chainNode (Real.log 2)) / ((N : ℝ) + 1) ≤
        autocorr (sinhCompact (1 / 2) (oddCompactSource f)) 0 +
          sourceCorrection (oddCompactSource f) (1 / 2) (sourceMean (oddCompactSource f) (1 / 2))
            (Finset.range (N + 1)) (fun _ => 1) (chainNode (Real.log 2)) / ((N : ℝ) + 1) +
          Real.sqrt (autocorr (centeredSource (oddCompactSource f) (1 / 2)
            (sourceMean (oddCompactSource f) (1 / 2))) 0 *
              autocorr (coherentProducer (oddCompactSource f) N) 0) := by
  let F := oddCompactSource f
  let q := centeredSource F (1 / 2) (sourceMean F (1 / 2))
  let p := coherentProducer F N
  have hm : (N : ℝ) + 1 ≠ 0 := by positivity
  have hp : (∫ u, q u * p u) =
      (∑ i ∈ pairSet N, differenceWeight (1 / 2) (fun _ => 1) (chainNode (Real.log 2)) i *
        (∫ u, q u * F (u + differenceNode (chainNode (Real.log 2)) i))) / ((N : ℝ) + 1) := by
    dsimp [p]
    rw [producer_pairing, centered_source_orthogonal, mul_zero, sub_zero,
      differencePacket, pairing_packet]
  have hcs := HTGeometry.sq_integral_mul_le (f := (q : ℝ → ℝ)) (g := (p : ℝ → ℝ))
    q.continuous.aestronglyMeasurable p.continuous.aestronglyMeasurable
    (integrable_sq q.continuous q.hasCompactSupport) (integrable_sq p.continuous p.hasCompactSupport)
  rw [integral_sq_eq_autocorr_zero, integral_sq_eq_autocorr_zero] at hcs
  have hle : (∫ u, q u * p u) ≤ Real.sqrt (autocorr q 0 * autocorr p 0) :=
    (le_abs_self _).trans (by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hcs)
  rw [hp] at hle
  rw [sinhGram_eq_diagonal_add_defect, odd_defect_eq_source f (1 / 2) (sourceMean F (1 / 2))]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Nat.cast_add, Nat.cast_one]
  change (_ * ((N : ℝ) + 1) + (_ + _)) / ((N : ℝ) + 1) ≤ _
  rw [add_div, add_div, mul_div_cancel_right₀ _ hm]
  dsimp only [F, q, p, pairSet] at hle ⊢
  linarith only [hle]

private def momentBound (f : C_c(ℝ, ℝ)) (N : ℕ) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 + signedCorrectionMass f -
    correctionFirstMoment f / ((N : ℝ) + 1) +
      Real.sqrt (autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 *
        (projectedEnergy f + producerBoundary f / ((N : ℝ) + 1)))

private theorem momentBound_tendsto (f : C_c(ℝ, ℝ)) :
    Tendsto (momentBound f) atTop (𝓝 (projectedBudget f)) := by
  have ht : Tendsto (fun N : ℕ => correctionFirstMoment f / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using inverse_length_tendsto.const_mul (correctionFirstMoment f)
  have he := ((boundary_tendsto (projectedEnergy f) (producerBoundary f)).const_mul
    (autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0)).sqrt
  unfold momentBound projectedBudget
  simpa only [sub_zero] using (tendsto_const_nhds.sub ht).add he

private theorem odd_gram_eventually_le (f : C_c(ℝ, ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      translationGramEnergy (sinhCompact (1 / 2) (oddCompactSource f))
        (Finset.range (N + 1)) (fun _ => 1) (chainNode (Real.log 2)) / ((N : ℝ) + 1) ≤
          momentBound (oddCompactSource f) N := by
  let F := oddCompactSource f
  obtain ⟨M, hM⟩ := coherentProducer_eventually_energy_le F
  obtain ⟨L, hL⟩ := sourceCorrection_one_eventually_affine F
  apply eventually_atTop.mpr
  refine ⟨max M L, ?_⟩
  intro N hN
  have h := odd_gram_le_producer f N
  have he := hL N ((le_max_right _ _).trans hN)
  change sourceCorrection F _ _ _ _ _ = _ at he
  change _ ≤ autocorr (sinhCompact (1 / 2) F) 0 + sourceCorrection F _ _ _ _ _ / _ + _ at h
  rw [he] at h
  have hm : (N : ℝ) + 1 ≠ 0 := by positivity
  rw [sub_div, mul_div_cancel_left₀ _ hm] at h
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (hM N ((le_max_left _ _).trans hN))
    (autocorr_zero_nonneg (centeredSource F (1 / 2) (sourceMean F (1 / 2)))))
  change _ ≤ momentBound F N
  unfold momentBound
  linarith only [h, hs]

private theorem span_tendsto (g : C_c(ℝ, ℝ)) :
    Tendsto (fun N : ℕ => chainSpan g N / ((N : ℝ) + 1)) atTop (𝓝 (Real.log 2)) := by
  apply (boundary_tendsto (Real.log 2) (2 * (multiplierSourceRadius g + 1) - Real.log 2)).congr
  intro N
  unfold chainSpan
  have hm : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Exact endpoint moment bound, with no producer, support or source-zero hypothesis. -/
theorem odd_moment_sq_le_projectedBudget (f : C_c(ℝ, ℝ)) :
    (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
      Real.log 2 * projectedBudget (oddCompactSource f) := by
  rw [← integral_sinhCompact_eq_moment]
  let F := oddCompactSource f
  let g := sinhCompact (1 / 2) F
  apply ge_of_tendsto ((span_tendsto g).mul (momentBound_tendsto F))
  filter_upwards [odd_gram_eventually_le f] with N hN
  have hm : 0 < (N : ℝ) + 1 := by positivity
  have hh := integral_sq_le_chain_gram g N
  have hnorm : (∫ u, g u) ^ 2 ≤ chainSpan g N / ((N : ℝ) + 1) *
      (translationGramEnergy g (Finset.range (N + 1)) (fun _ => 1)
        (chainNode (Real.log 2)) / ((N : ℝ) + 1)) := by
    rw [div_mul_div_comm, ← sq]
    apply (le_div_iff₀ (sq_pos_of_pos hm)).mpr
    nlinarith only [hh]
  exact hnorm.trans (mul_le_mul_of_nonneg_left hN
    (div_nonneg (chainSpan_pos g N).le hm.le))

theorem odd_projectedBudget_nonneg (f : C_c(ℝ, ℝ)) :
    0 ≤ projectedBudget (oddCompactSource f) := by
  have h := (sq_nonneg _).trans (odd_moment_sq_le_projectedBudget f)
  have hd := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith only [h, hd]

/-- Full plastic transfer of the unconditional producer energy bound. -/
theorem odd_plasticCrossover_ge_projectedBudget (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * Real.log 2 * projectedBudget (oddCompactSource f) ≤ plasticCrossover (oddCompactSource f) := by
  have hp := odd_plasticCrossover_ge_optimized f N
  have hm := odd_moment_sq_le_projectedBudget f
  nlinarith only [hp, hm]

/-- Source cancellation never worsens the previous signed coherent price. -/
theorem projectedBudget_le_coherentBudget (f : C_c(ℝ, ℝ)) :
    projectedBudget f ≤ coherentBudget f := by
  have hE : projectedEnergy f ≤ 2 * correlationMass f :=
    sub_le_self _ (div_nonneg (sq_nonneg _) (autocorr_zero_nonneg f))
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hE
    (autocorr_zero_nonneg (centeredSource f (1 / 2) (sourceMean f (1 / 2)))))
  rw [show autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 *
      (2 * correlationMass f) =
    2 * autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * correlationMass f by ring] at hs
  unfold projectedBudget coherentBudget
  linarith only [hs]

/-- Exact recovered source energy behind the improvement of the moment price. -/
theorem budget_gap_product (f : C_c(ℝ, ℝ)) :
    (coherentBudget f - projectedBudget f) *
      (Real.sqrt (2 * autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * correlationMass f) +
        Real.sqrt (autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * projectedEnergy f)) =
      autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 *
        (covarianceMass f ^ 2 / autocorr f 0) := by
  let Q := autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0
  have hQ : 0 ≤ Q := autocorr_zero_nonneg _
  have hΓ := correlationMass_nonneg f
  have hD := projectedEnergy_nonneg f
  have ha := Real.sq_sqrt (by positivity : 0 ≤ 2 * Q * correlationMass f)
  have hb := Real.sq_sqrt (mul_nonneg hQ hD)
  unfold coherentBudget projectedBudget
  change (_ + Real.sqrt (2 * Q * correlationMass f) -
    (_ + Real.sqrt (Q * projectedEnergy f))) *
      (Real.sqrt (2 * Q * correlationMass f) + Real.sqrt (Q * projectedEnergy f)) = _
  calc
    _ = Real.sqrt (2 * Q * correlationMass f) ^ 2 -
        Real.sqrt (Q * projectedEnergy f) ^ 2 := by ring
    _ = Q * (covarianceMass f ^ 2 / autocorr f 0) := by rw [ha, hb]; unfold projectedEnergy; ring

/-- Exact gain is retained in the same full plastic certificate. -/
theorem odd_plasticCrossover_ge_projection_gain (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * Real.log 2 * coherentBudget (oddCompactSource f) +
          2 * Real.log 2 * (coherentBudget (oddCompactSource f) - projectedBudget (oddCompactSource f)) ≤
            plasticCrossover (oddCompactSource f) := by
  have h := odd_plasticCrossover_ge_projectedBudget f N
  nlinarith only [h]

end
end GaloisForLFunctions.BiScaleUncertainty.CoherentSourceProjection
