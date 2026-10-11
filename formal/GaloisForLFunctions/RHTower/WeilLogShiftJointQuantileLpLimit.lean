import GaloisForLFunctions.RHTower.WeilLogShiftJointQuantileMomentLimit

/-! The same explicit joint quantile realization converges in every finite Lp order. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem finiteWeilCanonicalJointQuantile_eLpNorm_nat_eq (r t p : ℕ) :
    eLpNorm (fun u : ℝ => finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t) u -
      finiteWeilDiagonalGaussianQuantile u) ((p + 1 : ℕ) : ENNReal)
      (volume.restrict (Ioo (0 : ℝ) 1)) =
      (ENNReal.ofReal (∫ u : ℝ, dist
        (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t) u)
        (finiteWeilDiagonalGaussianQuantile u) ^ (p + 1)
          ∂(volume.restrict (Ioo (0 : ℝ) 1)))) ^ (1 / ((p + 1 : ℕ) : ℝ)) := by
  have hI := ofReal_integral_eq_lintegral_ofReal
    (finiteWeilCanonicalJointQuantile_distance_pow_integrable r t (p + 1))
    (Eventually.of_forall fun u => pow_nonneg dist_nonneg (p + 1))
  have hlin : (∫⁻ u : ℝ, ‖finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t) u -
      finiteWeilDiagonalGaussianQuantile u‖ₑ ^ (p + 1)
        ∂(volume.restrict (Ioo (0 : ℝ) 1))) =
      ENNReal.ofReal (∫ u : ℝ, dist
        (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t) u)
        (finiteWeilDiagonalGaussianQuantile u) ^ (p + 1)
          ∂(volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [hI]
    apply lintegral_congr_ae
    exact Eventually.of_forall fun u => by
      dsimp only
      rw [dist_eq_norm, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) (by simp)]
  simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast]
  rw [hlin]

theorem tendsto_finiteWeilCanonicalJointQuantile_eLpNorm_nat_zero (t : ℕ → ℕ) (p : ℕ) :
    Tendsto (fun r => eLpNorm (fun u : ℝ =>
      finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) u -
        finiteWeilDiagonalGaussianQuantile u) ((p + 1 : ℕ) : ENNReal)
          (volume.restrict (Ioo (0 : ℝ) 1))) atTop (𝓝 0) := by
  have hI := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
    (tendsto_finiteWeilCanonicalJointQuantile_moment_gap_zero t p)
  rw [ENNReal.ofReal_zero] at hI
  have hpow := (ENNReal.continuous_rpow_const (y := 1 / ((p + 1 : ℕ) : ℝ))).tendsto
    (0 : ENNReal) |>.comp hI
  rw [ENNReal.zero_rpow_of_pos (by positivity : (0 : ℝ) < 1 / ((p + 1 : ℕ) : ℝ))] at hpow
  exact hpow.congr fun r => (finiteWeilCanonicalJointQuantile_eLpNorm_nat_eq r (t r) p).symm

theorem tendsto_finiteWeilCanonicalJointQuantile_eLpNorm_zero (t : ℕ → ℕ) (q : NNReal) :
    Tendsto (fun r => eLpNorm (fun u : ℝ =>
      finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) u -
        finiteWeilDiagonalGaussianQuantile u) (q : ENNReal)
          (volume.restrict (Ioo (0 : ℝ) 1))) atTop (𝓝 0) := by
  letI := isProbabilityMeasure_restrict_Ioo_zero_one
  obtain ⟨p, hp⟩ := exists_nat_ge (q : ℝ)
  have hqR : (q : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := hp.trans (by exact_mod_cast Nat.le_succ p)
  have hq : (q : ENNReal) ≤ ((p + 1 : ℕ) : ENNReal) := by exact_mod_cast hqR
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_finiteWeilCanonicalJointQuantile_eLpNorm_nat_zero t p) (fun _ => bot_le)
  intro r
  exact eLpNorm_le_eLpNorm_of_exponent_le hq
    ((finiteWeilCanonicalJointQuantile_measurable r (2 * (r + 1) ^ 2 + t r)).sub
      finiteWeilDiagonalGaussianQuantile_measurable).aestronglyMeasurable

theorem finiteWeilCanonicalJointQuantile_eLpNorm_coupling (r k : ℕ) (q : ENNReal) :
    eLpNorm (fun u : ℝ => finiteWeilCanonicalJointQuantile r k u -
      finiteWeilDiagonalGaussianQuantile u) q (volume.restrict (Ioo (0 : ℝ) 1)) =
      eLpNorm (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => z.1 - z.2) q
        (finiteWeilCanonicalJointGaussianCoupling r k : Measure _) := by
  have hm := (finiteWeilCanonicalJointQuantile_measurable r k).prodMk
    finiteWeilDiagonalGaussianQuantile_measurable
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => z.1 - z.2) :=
    continuous_fst.sub continuous_snd
  have h := eLpNorm_map_measure (μ := volume.restrict (Ioo (0 : ℝ) 1)) (p := q)
    hc.aestronglyMeasurable hm.aemeasurable
  rw [finiteWeilCanonicalJointQuantile_pair_law] at h
  exact h.symm

theorem tendsto_finiteWeilCanonicalJointGaussianCoupling_eLpNorm_zero (t : ℕ → ℕ) (q : NNReal) :
    Tendsto (fun r => eLpNorm
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => z.1 - z.2) (q : ENNReal)
      (finiteWeilCanonicalJointGaussianCoupling r (2 * (r + 1) ^ 2 + t r) : Measure _)) atTop (𝓝 0) :=
  (tendsto_finiteWeilCanonicalJointQuantile_eLpNorm_zero t q).congr fun r =>
    finiteWeilCanonicalJointQuantile_eLpNorm_coupling r (2 * (r + 1) ^ 2 + t r) (q : ENNReal)

end RHTower
