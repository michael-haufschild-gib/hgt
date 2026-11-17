import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeSpectralMapping
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeWalkBoundaryModes
import GaloisForLFunctions.RepresentationLifting.Actions.OperatorDeterminant

/-!
# Characteristic polynomial of the finite reflection walk

The ordinary probe Gram rank and the two reflection-sector ranks determine
exact endpoint factors. Sylvester determinant interchange expresses the
remaining characteristic polynomial through the compressed signal.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open RepresentationLifting.OperatorDeterminant
variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})

/-- Orthogonal compression from the reflection hull to the original probe span. -/
def hullCompression : reflectionHull p →ₗ[ℂ] probeSpace p where
  toFun x := ⟨probeProjection p x, (probeSpace p).starProjection_apply_mem x⟩
  map_add' x y := Subtype.ext (map_add (probeProjection p) (x : ZeroSpace) (y : ZeroSpace))
  map_smul' c x := Subtype.ext (map_smul (probeProjection p) c (x : ZeroSpace))

private theorem compression_inclusion :
    (hullCompression p).comp (Submodule.inclusion (probeSpace_le_reflectionHull p)) = 1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact Submodule.starProjection_eq_self_iff.mpr v.property

private theorem compression_signal :
    ((hullCompression p).comp (hullReflection p)).comp
      (Submodule.inclusion (probeSpace_le_reflectionHull p)) = probeSignal p := rfl

private theorem reflection_walk_factor :
    hullWalk p = hullReflection p * ((2 : ℂ) •
      (Submodule.inclusion (probeSpace_le_reflectionHull p)).comp (hullCompression p) - 1) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change zeroReflection (probeProjection p x + probeProjection p x - (x : ZeroSpace)) =
    zeroReflection ((2 : ℂ) • probeProjection p x - (x : ZeroSpace))
  rw [two_smul]

private theorem positive_kernel_dimension :
    Module.finrank ℂ (LinearMap.ker (hullPositive p)) = (negativeProbeGram p).rank := by
  have hr := LinearMap.finrank_range_add_finrank_ker (hullPositive p)
  rw [← positiveProbeGram_rank_hull, reflectionHull_finrank_eq_sector_ranks] at hr
  omega

/-- The reflection determinant is read directly from the two sector Gram ranks. -/
theorem reflection_pencil_det (t : ℂ) :
    LinearMap.det (t • 1 + hullReflection p) =
      (t + 1) ^ (positiveProbeGram p).rank * (t - 1) ^ (negativeProbeGram p).rank := by
  have he : t • (1 : Module.End ℂ (reflectionHull p)) + hullReflection p =
      (t - 1) • 1 + (2 : ℂ) • hullPositive p := by
    unfold hullPositive
    module
  rw [he, det_projection_pencil _ (hullPositive_idempotent p),
    ← positiveProbeGram_rank_hull, positive_kernel_dimension]
  congr 2
  ring

/-- The walk determinant reduces exactly to a quadratic pencil of the compressed signal. -/
theorem walk_signal_determinant_of_ne_endpoints (t : ℂ) (ht : t ^ 2 ≠ 1) :
    LinearMap.det (t • 1 - hullWalk p) *
        (t ^ 2 - 1) ^ (hilbertProbeGram p).rank =
      (t + 1) ^ (positiveProbeGram p).rank * (t - 1) ^ (negativeProbeGram p).rank *
        LinearMap.det ((t ^ 2 + 1) • 1 - (2 * t) • probeSignal p) := by
  rw [hilbertProbeGram_rank_space, reflection_walk_factor]
  rw [det_reflection_walk _ (hullReflection_sq p) _ _ (compression_inclusion p) t ht,
    compression_signal, reflection_pencil_det]

open _root_.Polynomial

/-- The full polynomial identity includes the two reflection endpoints. -/
theorem walk_signal_polynomial :
    (hullWalk p).charpoly * (X ^ 2 - 1) ^ (hilbertProbeGram p).rank =
      (X + 1) ^ (positiveProbeGram p).rank * (X - 1) ^ (negativeProbeGram p).rank *
        quadraticPencil (probeSignal p) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : ({(1 : ℂ), -1} : Set ℂ)ᶜ.Infinite := (Set.toFinite _).infinite_compl
  apply hinf.mono
  intro t ht
  have hn : t ≠ 1 ∧ t ≠ -1 := by simpa only [Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] using ht
  have hs : t ^ 2 ≠ 1 := by
    intro h
    have hz : (t - 1) * (t + 1) = 0 := by
      calc
        _ = t ^ 2 - 1 := by ring
        _ = 0 := by rw [h, sub_self]
    rcases mul_eq_zero.mp hz with hz | hz
    · exact hn.1 (sub_eq_zero.mp hz)
    · exact hn.2 (eq_neg_of_add_eq_zero_left hz)
  change Polynomial.eval t _ = Polynomial.eval t _
  simp only [eval_mul, eval_pow, eval_sub, eval_add, eval_X, eval_one,
    LinearMap.eval_charpoly, Algebra.algebraMap_eq_smul_one, quadraticPencil_eval]
  exact walk_signal_determinant_of_ne_endpoints p t hs

/-- The quadratic pencil recovers the characteristic polynomial with exact endpoint corrections. -/
theorem quadraticPencil_eq_walk_charpoly :
    quadraticPencil (probeSignal p) = (hullWalk p).charpoly *
      (X - 1) ^ ((hilbertProbeGram p).rank - (negativeProbeGram p).rank) *
      (X + 1) ^ ((hilbertProbeGram p).rank - (positiveProbeGram p).rank) := by
  have hn : (negativeProbeGram p).rank ≤ (hilbertProbeGram p).rank := by
    have h := stationary_dimension_add_negative_rank p
    omega
  have hp : (positiveProbeGram p).rank ≤ (hilbertProbeGram p).rank := by
    have h := alternating_dimension_add_positive_rank p
    omega
  have hA : (X - 1 : ℂ[X]) ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.eval (0 : ℂ)) h
    norm_num at he
  have hB : (X + 1 : ℂ[X]) ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.eval (0 : ℂ)) h
    norm_num at he
  apply mul_left_cancel₀ (show
    (X + 1 : ℂ[X]) ^ (positiveProbeGram p).rank *
      (X - 1) ^ (negativeProbeGram p).rank ≠ 0 from
        mul_ne_zero (pow_ne_zero _ hB) (pow_ne_zero _ hA))
  calc
    _ = (hullWalk p).charpoly * (X ^ 2 - 1) ^ (hilbertProbeGram p).rank :=
      (walk_signal_polynomial p).symm
    _ = (hullWalk p).charpoly *
        ((X - 1) ^ (hilbertProbeGram p).rank * (X + 1) ^ (hilbertProbeGram p).rank) := by
      rw [show (X ^ 2 - 1 : ℂ[X]) = (X - 1) * (X + 1) by ring, mul_pow]
    _ = ((X + 1) ^ (positiveProbeGram p).rank * (X - 1) ^ (negativeProbeGram p).rank) *
        ((hullWalk p).charpoly *
          (X - 1) ^ ((hilbertProbeGram p).rank - (negativeProbeGram p).rank) *
          (X + 1) ^ ((hilbertProbeGram p).rank - (positiveProbeGram p).rank)) := by
      calc
        _ = (hullWalk p).charpoly *
          ((X - 1) ^ ((negativeProbeGram p).rank +
              ((hilbertProbeGram p).rank - (negativeProbeGram p).rank)) *
            (X + 1) ^ ((positiveProbeGram p).rank +
              ((hilbertProbeGram p).rank - (positiveProbeGram p).rank))) := by
          rw [Nat.add_sub_of_le hn, Nat.add_sub_of_le hp]
        _ = _ := by rw [pow_add, pow_add]; ring

#print axioms walk_signal_polynomial
#print axioms quadraticPencil_eq_walk_charpoly
#print axioms reflection_pencil_det
#print axioms walk_signal_determinant_of_ne_endpoints
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
