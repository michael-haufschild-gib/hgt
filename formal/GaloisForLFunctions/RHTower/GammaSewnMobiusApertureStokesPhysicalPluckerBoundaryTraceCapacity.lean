import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalPluckerFirstTraceNoGo
import GaloisForLFunctions.RHTower.FrankensteinThetaPluckerBoundaryAnomalyRecovery
import GaloisForLFunctions.RHTower.HedenmalmStokesOrientedFirstTraceQuantizedJump

/-!
# Boundary-trace capacity of the physical Pluecker operator

P-G99 proves that every fixed-positive-node Bernoulli reweighting has global source trace at most
`1/50`, strictly below completed Xi's first coefficient.  P-G97 nevertheless supplies a canonical
node-changing operation: the continuous-zero boundary transfer `T (eps + T)⁻¹`.

This module proves that, on every fixed physical coordinate face of size `n`, its diagonal sum
converges to exactly `n` as `eps` tends to zero from the right.  Consequently no finite scalar
bounds all finite-face traces uniformly near the singular boundary.  The old `1/50` ceiling is
therefore not a global source-capacity shortage; it is a fixed-node trace wall.  Singular boundary
spectralization supplies unlimited cofinal capacity, but precisely for that reason cannot by itself
produce a finite completed first trace.  More strongly, adding any scalar countercurrent with a
finite boundary limit remains non-uniformly bounded across finite faces.  This includes the existing
polar countercurrent with limit `-4`.  The source itself selects the lawful ordering: normalized
physical block weights applied before the singular limit give finite trace quantum exactly `4`,
which polar countercurrent cancels.  Thus label-dependent weighted descent followed by signed
relative finite part exists; its next curvature/divisor identification remains open.

No RH premise, Xi-zero computation, numerical estimate, or added axiom enters.
-/

open Filter Topology Set
open scoped InnerProductSpace ContinuousFunctionalCalculus BigOperators

noncomputable section
namespace RHTower.HedenmalmThetaSource

local instance gammaSewnMobiusApertureStokesPhysicalPluckerBoundaryTraceCapacityLocalInst1 : Nontrivial GammaSewnCriticalPhysicalPluckerHilbert := by
  refine ⟨⟨gammaSewnCriticalPhysicalPluckerBasis (0, 0), 0, ?_⟩⟩
  intro h
  have hn := congrArg norm h
  rw [norm_gammaSewnCriticalPhysicalPluckerBasis, norm_zero] at hn
  norm_num at hn

/-- Trace seen by the first `n` physical coordinate vectors after the canonical zero-boundary
transfer. -/
def gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace
    (n : ℕ) (eps : ℝ) : ℂ :=
  ∑ i : Fin n,
    inner ℂ (gammaSewnCriticalPhysicalPluckerBasis (i, 0))
      (boundaryTransfer eps
        (gammaSewnCriticalPhysicalPluckerBasis (i, 0)))

/-- Four-coordinate trace on one literal physical Pluecker packet. -/
def gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace
    (z : ℕ × ℕ) (eps : ℝ) : ℂ :=
  ∑ i : Fin 4,
    inner ℂ
      (gammaSewnCriticalPhysicalPluckerBasis
        (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
      (boundaryTransfer eps
        (gammaSewnCriticalPhysicalPluckerBasis
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)))

/-- Four-coordinate regularized-inverse trace on one physical packet. -/
def gammaSewnCriticalPhysicalPluckerBoundaryInversePacketTrace
    (z : ℕ × ℕ) (eps : ℝ) : ℂ :=
  ∑ i : Fin 4,
    inner ℂ
      (gammaSewnCriticalPhysicalPluckerBasis
        (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
      (boundaryInverse eps
        (gammaSewnCriticalPhysicalPluckerBasis
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)))

/-- Source-normalized packet-weighted boundary trace. -/
def gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace
    (eps : ℝ) : ℂ :=
  ∑' z : ℕ × ℕ,
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
      gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace z eps

/-- Source-normalized packet-weighted regularized-inverse trace. -/
def gammaSewnCriticalPhysicalPluckerWeightedBoundaryInversePacketTrace
    (eps : ℝ) : ℂ :=
  ∑' z : ℕ × ℕ,
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
      gammaSewnCriticalPhysicalPluckerBoundaryInversePacketTrace z eps

/-- Source-weighted boundary trace with completed polar countercurrent. -/
def gammaSewnCriticalPhysicalPluckerWeightedPolarRelativeBoundaryTrace
    (eps : ℝ) : ℂ :=
  gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace eps +
    (gammaSewnMobiusApertureStokesOrientedPolarCountercurrent eps : ℂ)

/-- At fixed finite rank, singular boundary transfer recovers one unit of trace per coordinate. -/
theorem tendsto_gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace
    (n : ℕ) :
    Tendsto
      (gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (n : ℂ)) := by
  rw [show (n : ℂ) = ∑ _i : Fin n, (1 : ℂ) by simp]
  apply tendsto_finsetSum
  intro i _
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ)
    (f := fun _eps : ℝ => gammaSewnCriticalPhysicalPluckerBasis ((i : ℕ), 0))
    (g := fun eps : ℝ => boundaryTransfer eps
      (gammaSewnCriticalPhysicalPluckerBasis ((i : ℕ), 0)))
    tendsto_const_nhds
    (boundaryTransfer_tendsto_id
      (gammaSewnCriticalPhysicalPluckerBasis ((i : ℕ), 0)))
  convert hinner using 1
  rw [inner_gammaSewnCriticalPhysicalPluckerBasis]
  simp

/-- Every fixed physical packet recovers exactly its four coordinate units at the boundary. -/
theorem tendsto_gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace
    (z : ℕ × ℕ) :
    Tendsto
      (gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (4 : ℂ)) := by
  rw [show (4 : ℂ) = ∑ _i : Fin 4, (1 : ℂ) by simp]
  apply tendsto_finsetSum
  intro i _
  let v := gammaSewnCriticalPhysicalPluckerBasis
    (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ)
    (f := fun _eps : ℝ => v)
    (g := fun eps : ℝ => boundaryTransfer eps v)
    tendsto_const_nhds (boundaryTransfer_tendsto_id v)
  convert hinner using 1
  rw [inner_gammaSewnCriticalPhysicalPluckerBasis]
  simp

/-- Packetwise exact resolvent defect: missing boundary capacity is regularization scale times
inverse trace. -/
theorem gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace_add_smul_inverse_eq_four
    (z : ℕ × ℕ) (eps : ℝ) (heps : 0 < eps) :
    gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace z eps +
        (eps : ℂ) * gammaSewnCriticalPhysicalPluckerBoundaryInversePacketTrace z eps =
      4 := by
  have hop : boundaryTransfer eps + eps • boundaryInverse eps =
      ContinuousLinearMap.id ℂ GammaSewnCriticalPhysicalPluckerHilbert := by
    change GaloisForLFunctions.RHTower.positiveBoundaryTransfer
        gammaSewnCriticalPhysicalPluckerSpectralOperator eps +
      eps • GaloisForLFunctions.RHTower.positiveBoundaryInverse
        gammaSewnCriticalPhysicalPluckerSpectralOperator eps = _
    exact
      GaloisForLFunctions.RHTower.positiveBoundaryTransfer_add_smul_inverse_eq_id
        gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.isSelfAdjoint
        spectrum_real_subset eps heps
  rw [gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace,
    gammaSewnCriticalPhysicalPluckerBoundaryInversePacketTrace,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    ∑ i : Fin 4,
        (inner ℂ
            (gammaSewnCriticalPhysicalPluckerBasis
              (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
            (boundaryTransfer eps
              (gammaSewnCriticalPhysicalPluckerBasis
                (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))) +
          (eps : ℂ) *
            inner ℂ
              (gammaSewnCriticalPhysicalPluckerBasis
                (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
              (boundaryInverse eps
                (gammaSewnCriticalPhysicalPluckerBasis
                  (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)))) =
        ∑ _i : Fin 4, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro i _
          let v := gammaSewnCriticalPhysicalPluckerBasis
            (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)
          have happ := congrArg
            (fun A : GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
              GammaSewnCriticalPhysicalPluckerHilbert => inner ℂ v (A v)) hop
          have hsmul : eps • boundaryInverse eps v =
              (eps : ℂ) • boundaryInverse eps v :=
            (IsScalarTower.algebraMap_smul ℂ eps (boundaryInverse eps v)).symm
          simp only [add_apply, smul_apply] at happ
          rw [hsmul] at happ
          dsimp only [v] at happ
          simpa only [inner_add_right, inner_smul_right, ContinuousLinearMap.id_apply,
            inner_gammaSewnCriticalPhysicalPluckerBasis, if_pos rfl, if_true] using happ
    _ = 4 := by simp

private theorem norm_boundaryTransfer_le_one (eps : ℝ) (heps : 0 < eps) :
    ‖boundaryTransfer eps‖ ≤ 1 := by
  simpa only [boundaryTransfer] using
    GaloisForLFunctions.RHTower.norm_positiveBoundaryTransfer_le_one
      gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.isSelfAdjoint
      spectrum_real_subset eps heps

private theorem norm_gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace_le_four
    (z : ℕ × ℕ) (eps : ℝ) (heps : 0 < eps) :
    ‖gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace z eps‖ ≤ 4 := by
  rw [gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ i : Fin 4,
        ‖inner ℂ
          (gammaSewnCriticalPhysicalPluckerBasis
            (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
          (boundaryTransfer eps
            (gammaSewnCriticalPhysicalPluckerBasis
              (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)))‖
        ≤ ∑ _i : Fin 4, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          let v := gammaSewnCriticalPhysicalPluckerBasis
            (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)
          have hv : ‖v‖ = 1 := norm_gammaSewnCriticalPhysicalPluckerBasis _
          have happ : ‖boundaryTransfer eps v‖ ≤ 1 := calc
            ‖boundaryTransfer eps v‖ ≤ ‖boundaryTransfer eps‖ * ‖v‖ :=
              (boundaryTransfer eps).le_opNorm v
            _ ≤ 1 * 1 := mul_le_mul (norm_boundaryTransfer_le_one eps heps)
              hv.le (norm_nonneg _) (by norm_num)
            _ = 1 := by norm_num
          calc
            ‖inner ℂ v (boundaryTransfer eps v)‖ ≤
                ‖v‖ * ‖boundaryTransfer eps v‖ := norm_inner_le_norm _ _
            _ ≤ 1 * 1 := mul_le_mul hv.le happ (norm_nonneg _) (by norm_num)
            _ = 1 := by norm_num
    _ = 4 := by simp

private theorem norm_gammaSewnCriticalPhysicalPluckerBoundaryInversePacketTrace_le
    (z : ℕ × ℕ) (eps : ℝ) (heps : 0 < eps) :
    ‖gammaSewnCriticalPhysicalPluckerBoundaryInversePacketTrace z eps‖ ≤ 4 / eps := by
  rw [gammaSewnCriticalPhysicalPluckerBoundaryInversePacketTrace]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ i : Fin 4,
        ‖inner ℂ
          (gammaSewnCriticalPhysicalPluckerBasis
            (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
          (boundaryInverse eps
            (gammaSewnCriticalPhysicalPluckerBasis
              (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)))‖
        ≤ ∑ _i : Fin 4, (1 / eps : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          let v := gammaSewnCriticalPhysicalPluckerBasis
            (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)
          have hv : ‖v‖ = 1 := norm_gammaSewnCriticalPhysicalPluckerBasis _
          have happ : ‖boundaryInverse eps v‖ ≤ 1 / eps := calc
            ‖boundaryInverse eps v‖ ≤ ‖boundaryInverse eps‖ * ‖v‖ :=
              (boundaryInverse eps).le_opNorm v
            _ = (1 / eps) * 1 := by rw [norm_boundaryInverse eps heps, hv]
            _ = 1 / eps := by ring
          calc
            ‖inner ℂ v (boundaryInverse eps v)‖ ≤
                ‖v‖ * ‖boundaryInverse eps v‖ := norm_inner_le_norm _ _
            _ ≤ 1 * (1 / eps) :=
              mul_le_mul hv.le happ (norm_nonneg _) (by positivity)
            _ = 1 / eps := by ring
    _ = 4 / eps := by simp; ring

private theorem summable_weightedBoundaryPacketTrace
    (eps : ℝ) (heps : 0 < eps) :
    Summable (fun z : ℕ × ℕ =>
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
        gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace z eps) := by
  apply Summable.of_norm_bounded
    (summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.mul_right 4)
  intro z
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z)]
  exact mul_le_mul_of_nonneg_left
    (norm_gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace_le_four z eps heps)
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le

private theorem summable_weightedBoundaryInversePacketTrace
    (eps : ℝ) (heps : 0 < eps) :
    Summable (fun z : ℕ × ℕ =>
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
        gammaSewnCriticalPhysicalPluckerBoundaryInversePacketTrace z eps) := by
  apply Summable.of_norm_bounded
    (summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.mul_right (4 / eps))
  intro z
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z)]
  exact mul_le_mul_of_nonneg_left
    (norm_gammaSewnCriticalPhysicalPluckerBoundaryInversePacketTrace_le z eps heps)
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le

/-- Exact weighted resolvent-defect identity.  Source-normalized finite boundary deficit is
regularization scale times a literal weighted inverse trace. -/
theorem gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace_add_smul_inverse_eq_four
    (eps : ℝ) (heps : 0 < eps) :
    gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace eps +
        (eps : ℂ) * gammaSewnCriticalPhysicalPluckerWeightedBoundaryInversePacketTrace eps =
      4 := by
  let f : ℕ × ℕ → ℂ := fun z =>
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
      gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace z eps
  let g : ℕ × ℕ → ℂ := fun z =>
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
      gammaSewnCriticalPhysicalPluckerBoundaryInversePacketTrace z eps
  have hf : Summable f := summable_weightedBoundaryPacketTrace eps heps
  have hg : Summable g := summable_weightedBoundaryInversePacketTrace eps heps
  have hterm : ∀ z : ℕ × ℕ,
      f z + (eps : ℂ) * g z =
        (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) * 4 := by
    intro z
    have hp :=
      gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace_add_smul_inverse_eq_four
        z eps heps
    dsimp only [f, g]
    calc
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
            gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace z eps +
          (eps : ℂ) *
            ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
              gammaSewnCriticalPhysicalPluckerBoundaryInversePacketTrace z eps) =
          (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
            (gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace z eps +
              (eps : ℂ) *
                gammaSewnCriticalPhysicalPluckerBoundaryInversePacketTrace z eps) := by ring
      _ = (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) * 4 := by rw [hp]
  rw [gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace,
    gammaSewnCriticalPhysicalPluckerWeightedBoundaryInversePacketTrace]
  change (∑' z, f z) + (eps : ℂ) * ∑' z, g z = 4
  rw [← tsum_mul_left, ← hf.tsum_add (hg.mul_left (eps : ℂ))]
  calc
    ∑' z, (f z + (eps : ℂ) * g z) =
        ∑' z, (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) * 4 :=
      tsum_congr hterm
    _ = (∑' z : ℕ × ℕ,
        (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ)) * 4 := by
      rw [tsum_mul_right]
    _ = ((∑' z : ℕ × ℕ,
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℝ) : ℂ) * 4 := by
      rw [Complex.ofReal_tsum]
    _ = 4 := by
      rw [tsum_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight]
      norm_num

/-- Defect form of the weighted resolvent law. -/
theorem four_sub_gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace_eq_smul_inverse
    (eps : ℝ) (heps : 0 < eps) :
    4 - gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace eps =
      (eps : ℂ) * gammaSewnCriticalPhysicalPluckerWeightedBoundaryInversePacketTrace eps := by
  rw [← gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace_add_smul_inverse_eq_four
    eps heps]
  ring

/-- Weighted cofinal descent before the boundary limit has finite trace quantum exactly four. -/
theorem tendsto_gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace :
    Tendsto gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (4 : ℂ)) := by
  let majorant : ℕ × ℕ → ℝ := fun z =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z * 4
  have hmajorant : Summable majorant := by
    exact (summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.mul_right 4).congr
      (fun z => by rfl)
  have hpoint : ∀ z : ℕ × ℕ, Tendsto
      (fun eps : ℝ =>
        (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
          gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace z eps)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) * 4)) := by
    intro z
    exact (tendsto_gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace z).const_mul _
  have hdom : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
      ∀ z : ℕ × ℕ,
        ‖(gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
          gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace z eps‖ ≤ majorant z := by
    filter_upwards [self_mem_nhdsWithin] with eps heps z
    change 0 < eps at heps
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z)]
    exact mul_le_mul_of_nonneg_left
      (norm_gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace_le_four z eps heps)
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le
  have hlim := tendsto_tsum_of_dominated_convergence hmajorant hpoint hdom
  have htarget :
      ∑' z : ℕ × ℕ,
          (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) * 4 =
        4 := by
    calc
      ∑' z : ℕ × ℕ,
          (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) * 4 =
          (∑' z : ℕ × ℕ,
            (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ)) * 4 := by
              rw [tsum_mul_right]
      _ = ((∑' z : ℕ × ℕ,
            gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℝ) : ℂ) * 4 := by
              rw [Complex.ofReal_tsum]
      _ = 4 := by
        rw [tsum_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight]
        norm_num
  change Tendsto
    (fun eps : ℝ => ∑' z : ℕ × ℕ,
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
        gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace z eps)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (4 : ℂ))
  rw [← htarget]
  exact hlim

/-- Physical four-coordinate boundary capacity and completed polar residue cancel after source-
normalized cofinal descent. -/
theorem tendsto_gammaSewnCriticalPhysicalPluckerWeightedPolarRelativeBoundaryTrace :
    Tendsto gammaSewnCriticalPhysicalPluckerWeightedPolarRelativeBoundaryTrace
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hpolar : Tendsto
      (fun eps : ℝ =>
        (gammaSewnMobiusApertureStokesOrientedPolarCountercurrent eps : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((-4 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsGT_zero
  have hadd := tendsto_gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace.add hpolar
  change Tendsto
    (fun eps : ℝ =>
      gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace eps +
        (gammaSewnMobiusApertureStokesOrientedPolarCountercurrent eps : ℂ))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  simpa using hadd

/-- For each finite face, its boundary trace is eventually within `1/2` below its dimension. -/
theorem eventually_gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace_re_gt
    (n : ℕ) :
    ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
      (n : ℝ) - 1 / 2 <
        (gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace n eps).re := by
  have hre : Tendsto
      (fun eps : ℝ =>
        (gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace n eps).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (n : ℝ)) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace n)
  exact hre.eventually (Ioi_mem_nhds (by norm_num))

/-- No finite scalar bounds all finite-coordinate traces uniformly near the singular boundary. -/
theorem gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace_not_uniformly_bounded
    (C : ℝ) :
    ∃ n : ℕ, ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
      C < (gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace n eps).re := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C + 1)
  refine ⟨n,
    (eventually_gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace_re_gt n).mono ?_⟩
  intro eps heps
  have hCn : C < (n : ℝ) - 1 / 2 := by linarith
  exact hCn.trans heps

/-- Adding any scalar countercurrent with a finite boundary limit cannot uniformly renormalize the
cofinal coordinate traces. -/
theorem gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace_add_counter_not_uniformly_bounded
    (counter : ℝ → ℂ) (L : ℂ)
    (hcounter : Tendsto counter (nhdsWithin 0 (Set.Ioi 0)) (nhds L))
    (C : ℝ) :
    ∃ n : ℕ, ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
      C < (gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace n eps +
        counter eps).re := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C - L.re + 2)
  have hcounterRe : Tendsto (fun eps : ℝ => (counter eps).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L.re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hcounter
  have hcounterLower : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
      L.re - 1 < (counter eps).re :=
    hcounterRe.eventually (Ioi_mem_nhds (by norm_num))
  refine ⟨n, ?_⟩
  filter_upwards
    [eventually_gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace_re_gt n,
      hcounterLower] with eps htrace hcounter'
  rw [Complex.add_re]
  nlinarith

/-- The existing scalar polar countercurrent cancels a four-unit oriented residue, but cannot
uniformly renormalize the cofinal boundary-transfer trace. -/
theorem gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace_add_polarCountercurrent_not_uniformly_bounded
    (C : ℝ) :
    ∃ n : ℕ, ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
      C < (gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace n eps +
        (gammaSewnMobiusApertureStokesOrientedPolarCountercurrent eps : ℂ)).re := by
  have hcounter : Tendsto
      (fun eps : ℝ =>
        (gammaSewnMobiusApertureStokesOrientedPolarCountercurrent eps : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((-4 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsGT_zero
  exact
    gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace_add_counter_not_uniformly_bounded
      (fun eps : ℝ =>
        (gammaSewnMobiusApertureStokesOrientedPolarCountercurrent eps : ℂ))
      ((-4 : ℝ) : ℂ) hcounter C

/-- **Capacity-escape capstone.** Fixed-node physical trace is bounded by `1/50`, while canonical
continuous-zero boundary transfer has arbitrarily large finite-face trace near the boundary. -/
theorem gammaSewnCriticalPhysicalPlucker_fixedNodeWall_and_boundaryCapacityEscape :
    gammaSewnCriticalPhysicalPluckerNuclearTraceMass ≤ (1 / 50 : ℝ) ∧
      ∀ C : ℝ, ∃ n : ℕ, ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
        C < (gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace n eps).re :=
  ⟨gammaSewnCriticalPhysicalPluckerNuclearTraceMass_le_one_div_fifty,
    gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace_not_uniformly_bounded⟩

end RHTower.HedenmalmThetaSource
