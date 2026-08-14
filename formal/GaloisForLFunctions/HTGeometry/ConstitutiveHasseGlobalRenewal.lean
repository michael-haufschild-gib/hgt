import GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry
import GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalSharpness
import GaloisForLFunctions.HTGeometry.ConstitutiveHassePacketFormation

/-!
# Hasse geometric-history global renewal

The pointwise Hasse recovery weights are upgraded to a measurable Markov kernel over an arbitrary
positive measurable scale profile.  Their uniform ratio bound by `1/2` gives the literal packet a
common exponential depth moment.  The generic cofinal-renewal laws then apply to every correlated
finite-KL renewal of the full Hasse packet.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real InformationTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal Topology

noncomputable section

/-- Measurable positive Mellin-scale profile on an observer space. -/
structure HasseHistoryProfile (X : Type*) [MeasurableSpace X] where
  scale : X → ℝ
  measurable_scale : Measurable scale
  scale_pos : ∀ x, 0 < scale x

variable {X : Type*} [MeasurableSpace X]

theorem measurable_uncurry_hasseHistoryDensity (T : HasseHistoryProfile X) :
    Measurable (Function.uncurry fun x n =>
      ENNReal.ofReal (hassePacketRecovery (T.scale x) n)) := by
  apply measurable_from_prod_countable_left
  intro n
  change Measurable (fun x : X =>
    ENNReal.ofReal (hassePacketRecovery (T.scale x) n))
  apply Measurable.ennreal_ofReal
  unfold hassePacketRecovery hassePacketRatio
  have ht := T.measurable_scale
  fun_prop

/-- Literal Hasse geometric-history recovery kernel. -/
noncomputable def HasseHistoryProfile.kernel (T : HasseHistoryProfile X) : Kernel X ℕ :=
  Kernel.withDensity (Kernel.const X Measure.count)
    (fun x n => ENNReal.ofReal (hassePacketRecovery (T.scale x) n))

theorem HasseHistoryProfile.kernel_apply_singleton
    (T : HasseHistoryProfile X) (x : X) (n : ℕ) :
    T.kernel x {n} = ENNReal.ofReal (hassePacketRecovery (T.scale x) n) := by
  rw [HasseHistoryProfile.kernel,
    Kernel.withDensity_apply' _ (measurable_uncurry_hasseHistoryDensity T) x]
  simp

instance (T : HasseHistoryProfile X) : IsMarkovKernel T.kernel := by
  constructor
  intro x
  rw [MeasureTheory.isProbabilityMeasure_iff]
  rw [HasseHistoryProfile.kernel,
    Kernel.withDensity_apply' _ (measurable_uncurry_hasseHistoryDensity T) x]
  rw [Kernel.const_apply, MeasureTheory.setLIntegral_univ, MeasureTheory.lintegral_count]
  have hsum := hasSum_hassePacketRecovery (T.scale_pos x)
  have hnonneg : ∀ n, 0 ≤ hassePacketRecovery (T.scale x) n := by
    intro n
    unfold hassePacketRecovery
    have hr := hassePacketRatio_mem_Ioo (T.scale_pos x)
    exact mul_nonneg (sub_nonneg.mpr hr.2.le) (pow_nonneg hr.1.le n)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum.summable, hsum.tsum_eq,
    ENNReal.ofReal_one]

theorem hassePacketRatio_lt_half (t : ℝ) :
    hassePacketRatio t < (1 / 2 : ℝ) := by
  unfold hassePacketRatio
  have he := Real.exp_pos (-t)
  linarith

/-- Every positive-scale Hasse recovery atom of depth `n + 1` is bounded by the common geometric
law of ratio `1/2`. -/
theorem hassePacketRecovery_succ_le_uniformGeometric
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    hassePacketRecovery t (n + 1) ≤
      Real.exp (-Real.log 2 * ((n + 1 : ℕ) : ℝ)) := by
  have hr := hassePacketRatio_mem_Ioo ht
  have hhalf := hassePacketRatio_lt_half t
  have hpow : hassePacketRatio t ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ hr.1.le hhalf.le (n + 1)
  have hone : 1 - hassePacketRatio t ≤ 1 := sub_le_self 1 hr.1.le
  calc
    hassePacketRecovery t (n + 1) =
        (1 - hassePacketRatio t) * hassePacketRatio t ^ (n + 1) := rfl
    _ ≤ 1 * (1 / 2 : ℝ) ^ (n + 1) :=
      mul_le_mul hone hpow (pow_nonneg hr.1.le _) (by linarith)
    _ = Real.exp (-Real.log 2 * ((n + 1 : ℕ) : ℝ)) := by
      rw [one_mul, show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by
        rw [Real.exp_neg, Real.exp_log (by linarith : (0 : ℝ) < 2)]
        simp [div_eq_mul_inv],
        ← Real.exp_nat_mul]
      congr 1
      ring

/-- Positive-depth history aperture in the full formed packet. -/
def hasseHistoryAperture (n : ℕ) : Set (X × ℕ) := Set.univ ×ˢ {n + 1}

theorem measurableSet_hasseHistoryAperture (n : ℕ) :
    MeasurableSet (hasseHistoryAperture (X := X) n) := by
  exact MeasurableSet.univ.prod (MeasurableSet.singleton _)

omit [MeasurableSpace X] in
theorem pairwise_disjoint_hasseHistoryAperture :
    Pairwise fun n m =>
      Disjoint (hasseHistoryAperture (X := X) n) (hasseHistoryAperture (X := X) m) := by
  intro n m hnm
  rw [Set.disjoint_left]
  rintro ⟨x, k⟩ hx hy
  have hkn : k = n + 1 := by simpa [hasseHistoryAperture] using hx.2
  have hkm : k = m + 1 := by simpa [hasseHistoryAperture] using hy.2
  exact hnm (Nat.add_right_cancel (hkn.symm.trans hkm))

/-- Literal formed Hasse packet. -/
noncomputable def HasseHistoryProfile.packet
    (T : HasseHistoryProfile X) (mu : Measure X) : Measure (X × ℕ) :=
  mu ⊗ₘ T.kernel

instance (T : HasseHistoryProfile X) (mu : Measure X) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (T.packet mu) := by
  dsimp [HasseHistoryProfile.packet]
  infer_instance

/-- Uniform exponential evacuation of each literal Hasse depth aperture. -/
theorem HasseHistoryProfile.packet_real_hasseHistoryAperture_le
    (T : HasseHistoryProfile X) (mu : Measure X) [IsProbabilityMeasure mu] (n : ℕ) :
    (T.packet mu).real (hasseHistoryAperture (X := X) n) ≤
      Real.exp (-Real.log 2 * ((n + 1 : ℕ) : ℝ)) := by
  let b : ℝ := Real.exp (-Real.log 2 * ((n + 1 : ℕ) : ℝ))
  have hpoint (x : X) : T.kernel x {n + 1} ≤ ENNReal.ofReal b := by
    rw [T.kernel_apply_singleton]
    exact ENNReal.ofReal_le_ofReal
      (hassePacketRecovery_succ_le_uniformGeometric (T.scale_pos x) n)
  have hmeasure : T.packet mu (hasseHistoryAperture (X := X) n) ≤ ENNReal.ofReal b := by
    rw [HasseHistoryProfile.packet, hasseHistoryAperture,
      Measure.compProd_apply_prod MeasurableSet.univ (MeasurableSet.singleton _)]
    calc
      (∫⁻ x in Set.univ, T.kernel x {n + 1} ∂mu) ≤
          ∫⁻ _x in Set.univ, ENNReal.ofReal b ∂mu :=
        lintegral_mono fun x => hpoint x
      _ = ENNReal.ofReal b := by simp
  have hb0 : 0 ≤ b := (Real.exp_pos _).le
  rw [measureReal_def]
  change (T.packet mu (hasseHistoryAperture (X := X) n)).toReal ≤ b
  calc
    (T.packet mu (hasseHistoryAperture (X := X) n)).toReal ≤
        (ENNReal.ofReal b).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
    _ = b := ENNReal.toReal_ofReal hb0

private theorem exp_div_two_mem_Ioo {lambda : ℝ}
    (hlt : lambda < Real.log 2) : Real.exp lambda / 2 ∈ Set.Ioo 0 1 := by
  have he2 : Real.exp lambda < 2 := by
    calc
      Real.exp lambda < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hlt
      _ = 2 := Real.exp_log (by linarith)
  constructor
  · positivity
  · linarith

private theorem hasse_uniform_partition_series
    {lambda : ℝ} (hlt : lambda < Real.log 2) :
    1 + ∑' n : ℕ, Real.exp
        (-((Real.log 2 - lambda) * ((n + 1 : ℕ) : ℝ))) =
      (1 - Real.exp lambda / 2)⁻¹ := by
  let r : ℝ := Real.exp lambda / 2
  have hr := exp_div_two_mem_Ioo hlt
  have hterm (n : ℕ) :
      Real.exp (-((Real.log 2 - lambda) * ((n + 1 : ℕ) : ℝ))) = r ^ (n + 1) := by
    rw [show -((Real.log 2 - lambda) * ((n + 1 : ℕ) : ℝ)) =
        ((n + 1 : ℕ) : ℝ) * (lambda - Real.log 2) by ring,
      Real.exp_nat_mul]
    congr 1
    dsimp [r]
    rw [Real.exp_sub, Real.exp_log (by linarith : (0 : ℝ) < 2)]
  simp_rw [hterm]
  rw [show (fun n : ℕ => r ^ (n + 1)) = fun n => r * r ^ n by
    funext n
    rw [pow_succ']]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr.1.le hr.2]
  dsimp [r]
  have he2 : Real.exp lambda < 2 := by
    calc
      Real.exp lambda < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hlt
      _ = 2 := Real.exp_log (by linarith)
  field_simp [ne_of_gt (sub_pos.mpr he2)]
  ring

/-- Every literal Hasse packet has the common exponential history partition bound from `(HGH.6)`.
The height is zero at depth zero and equals the positive depth otherwise. -/
theorem HasseHistoryProfile.partition_entropyMoment
    (T : HasseHistoryProfile X) (mu : Measure X) [IsProbabilityMeasure mu]
    (Q : Measure (X × ℕ)) [IsProbabilityMeasure Q]
    {lambda : ℝ} (hlambda : 0 < lambda) (hlt : lambda < Real.log 2)
    (hfin : klDiv Q (T.packet mu) ≠ ⊤) :
    let H := apertureGauge (hasseHistoryAperture (X := X))
      (fun n => ((n + 1 : ℕ) : ℝ))
    Integrable (fun z => Real.exp (lambda * H z)) (T.packet mu) ∧
      (∫ z, Real.exp (lambda * H z) ∂T.packet mu) ≤
        (1 - Real.exp lambda / 2)⁻¹ ∧
      Summable (fun n => ((n + 1 : ℕ) : ℝ) *
        Q.real (hasseHistoryAperture (X := X) n)) ∧
      lambda * (∑' n, ((n + 1 : ℕ) : ℝ) *
        Q.real (hasseHistoryAperture (X := X) n)) ≤
        (klDiv Q (T.packet mu)).toReal +
          Real.log (∫ z, Real.exp (lambda * H z) ∂T.packet mu) := by
  dsimp only
  have h := stretchedAperture_partition_entropyMoment (T.packet mu) Q
    (hasseHistoryAperture (X := X)) measurableSet_hasseHistoryAperture
    pairwise_disjoint_hasseHistoryAperture 1 (Real.log 2) 1 lambda
    (by linarith) (by positivity) hlambda hlt
    (fun n => by
      simpa [Real.rpow_one] using T.packet_real_hasseHistoryAperture_le mu n)
    hfin
  refine ⟨(by simpa [Real.rpow_one] using h.1), ?_, ?_, ?_⟩
  · calc
      (∫ z, Real.exp (lambda * apertureGauge (hasseHistoryAperture (X := X))
          (fun n => ((n + 1 : ℕ) : ℝ)) z) ∂T.packet mu) ≤
          1 + ∑' n : ℕ, Real.exp
            (-((Real.log 2 - lambda) * ((n + 1 : ℕ) : ℝ))) := by
        simpa [Real.rpow_one] using h.2.2.1
      _ = (1 - Real.exp lambda / 2)⁻¹ :=
        hasse_uniform_partition_series hlt
  · simpa using h.2.2.2.2.1
  · simpa using h.2.2.2.2.2

/-- Finite packet action and persistent polynomial history current force work degree strictly
greater than two. -/
theorem HasseHistoryProfile.persistentCurrent_workDegree_gt_two
    (T : HasseHistoryProfile X) (mu : Measure X) [IsProbabilityMeasure mu]
    (Q : Measure (X × ℕ)) [IsProbabilityMeasure Q]
    (W : ℕ → ℝ) {lambda K c d : ℝ}
    (hlambda : 0 < lambda) (hlt : lambda < Real.log 2)
    (hK : 0 < K) (hc : 0 < c) (hW : ∀ n, 0 ≤ W n)
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ Q.real (hasseHistoryAperture (X := X) n) * W n)
    (hfin : klDiv Q (T.packet mu) ≠ ⊤) :
    2 < d := by
  have h := stretchedAperture_persistentCurrent_workDegree_gt
    (T.packet mu) Q (hasseHistoryAperture (X := X)) measurableSet_hasseHistoryAperture
    pairwise_disjoint_hasseHistoryAperture W 1 (Real.log 2) 1 lambda K c d
    (by linarith) (by positivity) hlambda hlt hK hc hW
    (fun n => by
      simpa [Real.rpow_one] using T.packet_real_hasseHistoryAperture_le mu n)
    hwork hcurrent hfin
  linarith

/-- Every finite-action linear history current is summable, with the literal Hasse packet
partition on the right-hand side. -/
theorem HasseHistoryProfile.totalLinearHistoryCurrent_bound
    (T : HasseHistoryProfile X) (mu : Measure X) [IsProbabilityMeasure mu]
    (Q : Measure (X × ℕ)) [IsProbabilityMeasure Q]
    (W : ℕ → ℝ) {lambda K : ℝ}
    (hlambda : 0 < lambda) (hlt : lambda < Real.log 2) (hK : 0 ≤ K)
    (hW : ∀ n, 0 ≤ W n)
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ))
    (hfin : klDiv Q (T.packet mu) ≠ ⊤) :
    Summable (fun n => Q.real (hasseHistoryAperture (X := X) n) * W n) ∧
      (∑' n, Q.real (hasseHistoryAperture (X := X) n) * W n) ≤
        (K / lambda) *
          ((klDiv Q (T.packet mu)).toReal +
            Real.log (∫ z, Real.exp (lambda * apertureGauge
              (hasseHistoryAperture (X := X)) (fun n => ((n + 1 : ℕ) : ℝ)) z) ∂
                T.packet mu)) := by
  exact exponentialAperture_totalLinearCurrent_bound
    (T.packet mu) Q (hasseHistoryAperture (X := X)) measurableSet_hasseHistoryAperture
    pairwise_disjoint_hasseHistoryAperture W 1 (Real.log 2) lambda K
    (by linarith) hlambda hlt hK hW
    (fun n => by
      simpa using T.packet_real_hasseHistoryAperture_le mu n)
    hwork hfin

/-- Fixed-scale Hasse recovery is exactly the geometric sharpness baseline. -/
theorem hassePacketRecovery_eq_geometricBaselineMass (t : ℝ) (n : ℕ) :
    hassePacketRecovery t n = geometricBaselineMass (hassePacketRatio t) n := rfl

/-- Cubic-and-higher work is class-sharp inside the literal fixed-scale Hasse species.  The
renewed law is a genuine PMF, has finite KL action over the Hasse law, and carries exactly the
constant current `c` at every positive depth. -/
theorem hasseHistory_cubic_classSharp
    {t K c d : ℝ} (ht : 0 < t) (hK : 0 < K) (hc : 0 < c) (hd : 2 < d)
    (htotal : ∑' n, polynomialRenewalTail (c / K) d n < 1) :
    let P := geometricBaselinePMF (hassePacketRatio t)
      (hassePacketRatio_mem_Ioo ht).1.le (hassePacketRatio_mem_Ioo ht).2
    let Q := polynomialRenewalPMF (c / K) d (div_nonneg hc.le hK.le)
      (by linarith) htotal
    (∀ n, P n = ENNReal.ofReal (hassePacketRecovery t n)) ∧
      (∀ n, Q (n + 1) =
        ENNReal.ofReal ((c / K) * (((n + 1 : ℕ) : ℝ) ^ (-d)))) ∧
      klDiv Q.toMeasure P.toMeasure ≠ ⊤ ∧
      ∀ n, (Q (n + 1)).toReal *
        (K * (((n + 1 : ℕ) : ℝ) ^ d)) = c := by
  simpa only [hassePacketRecovery_eq_geometricBaselineMass] using
    geometricPolynomialRenewal_cubicSharp
      (hassePacketRatio_mem_Ioo ht).1 (hassePacketRatio_mem_Ioo ht).2
      hK hc hd htotal

end


end GaloisForLFunctions.HTGeometry
