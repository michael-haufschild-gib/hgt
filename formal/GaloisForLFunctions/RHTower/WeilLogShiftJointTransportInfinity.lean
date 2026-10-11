import GaloisForLFunctions.HTGeometry.BoundedTransportInfinity
import GaloisForLFunctions.RHTower.WeilLogShiftJointInfinityMarginals
import GaloisForLFunctions.RHTower.WeilLogShiftJointQuantileLpLimit

/-! Every joint coupling has infinite infinity cost. The explicit coupling
converges to zero exactly at the finite exponents. -/

open MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem finiteWeilCanonicalJointCoupling_eLpNorm_top (r k : ℕ)
    (π : {π : Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) //
      IsCoupling (finiteWeilCanonicalJointProbabilityLaw r k : Measure _)
        (finiteWeilDiagonalGaussian : Measure _) π}) :
    eLpNorm (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => z.1 - z.2)
      ⊤ π.val = ⊤ :=
  eLpNorm_coupling_top_eq_top_of_memLp_not_memLp
    (finiteWeilCanonicalJointProbabilityLaw_id_memLp_top r k)
    finiteWeilDiagonalGaussian_id_not_memLp_top π

theorem finiteWeilCanonicalJointGaussianCoupling_eLpNorm_top (r k : ℕ) :
    eLpNorm (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => z.1 - z.2) ⊤
      (finiteWeilCanonicalJointGaussianCoupling r k : Measure _) = ⊤ :=
  finiteWeilCanonicalJointCoupling_eLpNorm_top r k
    ⟨_, finiteWeilCanonicalJointGaussianCoupling_isCoupling r k⟩

theorem finiteWeilCanonicalJointQuantile_eLpNorm_top (r k : ℕ) :
    eLpNorm (fun u : ℝ => finiteWeilCanonicalJointQuantile r k u -
      finiteWeilDiagonalGaussianQuantile u) ⊤ (volume.restrict (Ioo (0 : ℝ) 1)) = ⊤ := by
  rw [finiteWeilCanonicalJointQuantile_eLpNorm_coupling,
    finiteWeilCanonicalJointGaussianCoupling_eLpNorm_top]

theorem tendsto_finiteWeilCanonicalJointGaussianCoupling_eLpNorm_zero_iff
    (t : ℕ → ℕ) (q : ENNReal) :
    Tendsto (fun r => eLpNorm
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => z.1 - z.2) q
      (finiteWeilCanonicalJointGaussianCoupling r (2 * (r + 1) ^ 2 + t r) : Measure _))
      atTop (𝓝 0) ↔ q ≠ ⊤ := by
  constructor
  · intro h hq
    subst q
    simp only [finiteWeilCanonicalJointGaussianCoupling_eLpNorm_top] at h
    exact ENNReal.top_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)
  · intro hq
    simpa only [ENNReal.coe_toNNReal hq] using
      tendsto_finiteWeilCanonicalJointGaussianCoupling_eLpNorm_zero t q.toNNReal

theorem tendsto_finiteWeilCanonicalJointQuantile_eLpNorm_zero_iff
    (t : ℕ → ℕ) (q : ENNReal) :
    Tendsto (fun r => eLpNorm (fun u : ℝ =>
      finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) u -
        finiteWeilDiagonalGaussianQuantile u) q (volume.restrict (Ioo (0 : ℝ) 1)))
      atTop (𝓝 0) ↔ q ≠ ⊤ := by
  constructor
  · intro h hq
    subst q
    simp only [finiteWeilCanonicalJointQuantile_eLpNorm_top] at h
    exact ENNReal.top_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)
  · intro hq
    simpa only [ENNReal.coe_toNNReal hq] using
      tendsto_finiteWeilCanonicalJointQuantile_eLpNorm_zero t q.toNNReal

end RHTower
