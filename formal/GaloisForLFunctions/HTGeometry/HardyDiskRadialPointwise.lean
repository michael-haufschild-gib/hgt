import GaloisForLFunctions.HTGeometry.DominatedSeriesToLp
import GaloisForLFunctions.HTGeometry.HardyDiskBoundary
import GaloisForLFunctions.HTGeometry.MultiplierClosedGraph
import GaloisForLFunctions.HTGeometry.SzegoBoundaryH2

/-!
# Pointwise radial limits for Hardy-disk vectors

The coefficient-defined Hardy function on every canonical radial circle represents the abstract
Abel synthesis in circle `L²`.  Strong radial convergence therefore admits an almost-everywhere
convergent cofinal subsequence to the exact Riesz--Fischer boundary representative.
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal NNReal lp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Literal radial value of an arbitrary Hardy-disk vector on the circle. -/
def hardyDiskRadialBoundaryFun (n : ℕ) (f : HardyDisk) (z : Circle) : ℂ :=
  hardyFun f ((hardyDiskAbelRadius n : ℂ) * (z : ℂ))

theorem memLp_hardyDiskRadialBoundaryFun (n : ℕ) (f : HardyDisk) :
    MemLp (hardyDiskRadialBoundaryFun n f) 2 circleLebesgue := by
  let r := hardyDiskAbelRadius n
  have harg : ∀ z : Circle, (r : ℂ) * (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    intro z
    rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hardyDiskAbelRadius_nonneg n)]
    simpa [r] using hardyDiskAbelRadius_lt_one n
  have hcont : Continuous (hardyDiskRadialBoundaryFun n f) := by
    change Continuous (hardyFun f ∘ fun z : Circle => (r : ℂ) * (z : ℂ))
    exact (differentiableOn_hardyFun f).continuousOn.comp_continuous
      (continuous_const.mul continuous_subtype_val) harg
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  apply MemLp.of_bound hcont.aestronglyMeasurable C
  filter_upwards with z
  exact hC z (Set.mem_univ z)

/-- Literal radial evaluation and coefficient radial synthesis define the same circle `L²`
vector. -/
theorem hardyDiskRadialBoundaryFun_toLp_eq (n : ℕ) (f : HardyDisk) :
    (memLp_hardyDiskRadialBoundaryFun n f).toLp
        (hardyDiskRadialBoundaryFun n f) =
      hardyDiskRadialBoundary n f := by
  let r := hardyDiskAbelRadius n
  let term : ℕ → Circle → ℂ := fun k z =>
    ((r : ℂ) ^ k * f k) * (z : ℂ) ^ k
  let g : ℕ → ℝ := fun k => ‖f‖ * r ^ k
  have hgsum : Summable g := by
    exact (summable_geometric_of_lt_one (hardyDiskAbelRadius_nonneg n)
      (hardyDiskAbelRadius_lt_one n)).mul_left ‖f‖
  have hgnn : ∀ k, 0 ≤ g k := fun k => by
    exact mul_nonneg (norm_nonneg _) (pow_nonneg (hardyDiskAbelRadius_nonneg n) _)
  have hbd : ∀ k, ∀ᵐ z ∂circleLebesgue, ‖term k z‖ ≤ g k := by
    intro k
    filter_upwards with z
    change ‖((r : ℂ) ^ k * f k) * (z : ℂ) ^ k‖ ≤ ‖f‖ * r ^ k
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hardyDiskAbelRadius_nonneg n)]
    simp only [Circle.norm_coe, one_pow, mul_one]
    simpa [mul_comm, r] using
      mul_le_mul_of_nonneg_right (hardyDisk_norm_coord_le f k)
        (pow_nonneg (hardyDiskAbelRadius_nonneg n) k)
  have hpt : ∀ᵐ z ∂circleLebesgue,
      HasSum (fun k => term k z) (hardyDiskRadialBoundaryFun n f z) := by
    filter_upwards with z
    have harg : ‖(r : ℂ) * (z : ℂ)‖ < 1 := by
      rw [norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hardyDiskAbelRadius_nonneg n)]
      simpa [r] using hardyDiskAbelRadius_lt_one n
    have hs := (summable_hardyDisk_terms f harg).hasSum
    change HasSum (fun k => f k * ((r : ℂ) * (z : ℂ)) ^ k)
      (hardyFun f ((r : ℂ) * (z : ℂ))) at hs
    change HasSum (fun k => term k z)
      (hardyFun f ((r : ℂ) * (z : ℂ)))
    exact hs.congr_fun fun k => by
      change ((r : ℂ) ^ k * f k) * (z : ℂ) ^ k =
        f k * ((r : ℂ) * (z : ℂ)) ^ k
      rw [mul_pow]
      ring
  have hmem : ∀ k, MemLp (term k) 2 circleLebesgue := by
    intro k
    exact (circleMonomial_memLp circleLebesgue k).const_mul ((r : ℂ) ^ k * f k)
  have hactual := hasSum_toLp_of_ae_dominated hgsum hgnn hbd hpt hmem
    (memLp_hardyDiskRadialBoundaryFun n f)
  have htermLp : ∀ k,
      (hmem k).toLp (term k) =
        ((r : ℂ) ^ k * f k) • circleMonomialLp circleLebesgue k := by
    intro k
    apply Lp.ext
    filter_upwards [(hmem k).coeFn_toLp,
      Lp.coeFn_smul ((r : ℂ) ^ k * f k) (circleMonomialLp circleLebesgue k),
      circleMonomialLp_coeFn_ae circleLebesgue k] with z hz hsmul hmono
    rw [hz, hsmul]
    change term k z = ((r : ℂ) ^ k * f k) *
      ((circleMonomialLp circleLebesgue k : Circle → ℂ) z)
    rw [hmono]
  have hrcoeff : Memℓp (fun k => (r : ℂ) ^ k * f k) 2 := by
    have hrle : ∀ k, ‖(r : ℂ) ^ k‖ ≤ 1 := by
      intro k
      rw [norm_pow, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hardyDiskAbelRadius_nonneg n)]
      exact pow_le_one₀ (hardyDiskAbelRadius_nonneg n)
        (hardyDiskAbelRadius_lt_one n).le
    exact (lp.memℓp f).mono' (fun k => by
      rw [norm_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hrle k) (norm_nonneg (f k)))
  have habstract := hasSum_circleMonomial_smul_circleRieszFischerOfNat
    (fun k => (r : ℂ) ^ k * f k) hrcoeff
  have hriesz :
      circleRieszFischerOfNat (fun k => (r : ℂ) ^ k * f k) hrcoeff =
        hardyDiskRadialBoundary n f := by
    rw [hardyDiskRadialBoundary, circleRieszFischerOfNat]
    congr 3
    funext k
    cases k with
    | ofNat k => simp [r, radialMult]
    | negSucc k => simp [radialMult]
  rw [hriesz] at habstract
  symm
  apply tendsto_nhds_unique habstract
  exact hactual.congr_fun fun k => (htermLp k).symm

/-- A cofinal radial subsequence converges almost everywhere to the exact Hardy boundary. -/
theorem exists_hardyDiskRadialBoundary_subseq_ae (f : HardyDisk) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂circleLebesgue,
        Tendsto (fun i => hardyDiskRadialBoundaryFun (ns i) f z)
          atTop (𝓝 ((hardyDiskBoundary f : Circle → ℂ) z)) := by
  have hL2 : Tendsto
      (fun n => (memLp_hardyDiskRadialBoundaryFun n f).toLp
        (hardyDiskRadialBoundaryFun n f))
      atTop (𝓝 (hardyDiskBoundary f)) := by
    convert tendsto_hardyDiskRadialBoundary f using 1
    funext n
    exact hardyDiskRadialBoundaryFun_toLp_eq n f
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_tendsto hL2
  have hcoe : ∀ᵐ z ∂circleLebesgue, ∀ i : ℕ,
      (((memLp_hardyDiskRadialBoundaryFun (ns i) f).toLp
        (hardyDiskRadialBoundaryFun (ns i) f) :
          Lp ℂ 2 circleLebesgue) : Circle → ℂ) z =
        hardyDiskRadialBoundaryFun (ns i) f z := by
    rw [ae_all_iff]
    intro i
    exact (memLp_hardyDiskRadialBoundaryFun (ns i) f).coeFn_toLp
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, hcoe] with z hz hzc
  convert hz using 1
  funext i
  exact (hzc i).symm

end

end GaloisForLFunctions.HTGeometry
