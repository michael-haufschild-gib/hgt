import GaloisForLFunctions.HTGeometry.PolarDecomposition
import GaloisForLFunctions.HTGeometry.SplitRecoveryFormationCapital

/-!
# Polar normalization identifies the active source

The existing polar map has exactly the original operator's kernel. In finite
dimension its initial projection is therefore the existing coimage projection.
Normalization preserves precisely the norm of the active representative, even
for singular operators. This applies the support normalization of Du,
Proposition 3.16, without assuming invertibility.
-/

noncomputable section
open scoped InnerProductSpace
open ContinuousLinearMap GaloisForLFunctions.HTGeometry

namespace HilbertMetric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

local instance : CompleteSpace H := FiniteDimensional.complete ℂ H

/-- Polar normalization of any finite-dimensional operator. -/
def finitePolar (T : H →L[ℂ] H) : H →L[ℂ] H :=
  polarMap T (isCompactOperator_of_locallyCompactSpace_dom T)

/-- Polar normalization removes singular values but retains exactly the kernel. -/
theorem finitePolar_eq_zero_iff (T : H →L[ℂ] H) (x : H) :
    finitePolar T x = 0 ↔ T x = 0 := by
  let hc := isCompactOperator_of_locallyCompactSpace_dom T
  change polarMap T hc x = 0 ↔ T x = 0
  constructor
  · intro hx
    apply apply_eq_zero_of_forall_inner_svVec_energyOp hc
    intro n
    by_cases hn : singVal T n = 0
    · have hμ : svVal (energyOp T) n = 0 := by
        rw [← singVal_sq T n, hn, pow_two, mul_zero]
      rw [svVec_eq_zero_of_svVal_eq_zero _ hμ, inner_zero_left]
    · rw [← adjoint_polarMap_apply_svdVec hc hn, adjoint_inner_left,
        hx, inner_zero_right]
  · intro hx
    apply polarMap_apply_eq_zero_of_orth hc
    intro n
    by_cases hn : svVal (energyOp T) n = 0
    · rw [svVec_eq_zero_of_svVal_eq_zero _ hn, inner_zero_left]
    · have hzero : energyOp T x = 0 := by
        change T.adjoint (T x) = 0
        rw [hx, map_zero]
      have he := energyOp_symmetric T (svVec (energyOp T) n) x
      change inner ℂ (energyOp T (svVec (energyOp T) n)) x =
        inner ℂ (svVec (energyOp T) n) (energyOp T x) at he
      rw [apply_svVec, inner_smul_left, hzero, inner_zero_right] at he
      have he' : (svVal (energyOp T) n : ℂ) * inner ℂ (svVec (energyOp T) n) x = 0 := by
        simpa using he
      exact (mul_eq_zero.mp he').resolve_left (Complex.ofReal_ne_zero.mpr hn)

theorem finitePolar_ker (T : H →L[ℂ] H) : (finitePolar T).ker = T.ker := by
  ext x
  exact finitePolar_eq_zero_iff T x

/-- The polar initial projection is exactly the source projection used in minimal recovery. -/
theorem finitePolar_initial_projection (T : H →L[ℂ] H) :
    (finitePolar T).adjoint ∘L finitePolar T = coimageProjection T := by
  have hp : IsStarProjection ((finitePolar T).adjoint ∘L finitePolar T) :=
    ⟨adjoint_polarMap_comp_polarMap_idempotent _,
      ContinuousLinearMap.isSelfAdjoint_iff'.mpr (adjoint_adjoint_polarMap_comp_polarMap _)⟩
  obtain ⟨K, hK, heq⟩ := isStarProjection_iff_eq_starProjection.mp hp
  have hker : Kᗮ = T.ker := by
    rw [← Submodule.ker_starProjection, ← heq,
      ContinuousLinearMap.ker_adjoint_comp_self, finitePolar_ker]
  have hspace : K = T.kerᗮ := by
    rw [← hker, Submodule.orthogonal_orthogonal]
  simpa only [hspace, coimageProjection] using heq

/-- The normalized map preserves exactly the norm of the active representative. -/
theorem finitePolar_norm_sq (T : H →L[ℂ] H) (x : H) :
    ‖finitePolar T x‖ ^ 2 = ‖coimageProjection T x‖ ^ 2 := by
  have he : inner ℂ (finitePolar T x) (finitePolar T x) =
      inner ℂ (coimageProjection T x) (coimageProjection T x) := by
    rw [← adjoint_inner_right]
    change inner ℂ x (((finitePolar T).adjoint ∘L finitePolar T) x) = _
    rw [finitePolar_initial_projection]
    change inner ℂ x (T.kerᗮ.starProjection x) =
      inner ℂ (T.kerᗮ.starProjection x) (T.kerᗮ.starProjection x)
    have hfix : T.kerᗮ.starProjection (T.kerᗮ.starProjection x) = T.kerᗮ.starProjection x :=
      Submodule.starProjection_eq_self_iff.mpr (coimageProjection_mem T x)
    rw [Submodule.inner_starProjection_left_eq_right, hfix]
  have hre := congrArg Complex.re he
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
  change ((‖finitePolar T x‖ : ℂ) ^ 2).re = ((‖coimageProjection T x‖ : ℂ) ^ 2).re at hre
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re] at hre
  exact hre

/-- Polar normalization retains the entire output space, including at rank drops. -/
theorem finitePolar_range (T : H →L[ℂ] H) : (finitePolar T).range = T.range := by
  have hle : T.range ≤ (finitePolar T).range := by
    rintro y ⟨x, rfl⟩
    refine ⟨absOp T x, ?_⟩
    exact DFunLike.congr_fun (polarMap_comp_absOp
      (isCompactOperator_of_locallyCompactSpace_dom T)) x
  have hT := LinearMap.finrank_range_add_finrank_ker T.toLinearMap
  have hU := LinearMap.finrank_range_add_finrank_ker (finitePolar T).toLinearMap
  change Module.finrank ℂ (finitePolar T).range + Module.finrank ℂ (finitePolar T).ker = _ at hU
  rw [finitePolar_ker] at hU
  exact (Submodule.eq_of_le_of_finrank_eq hle (Nat.add_right_cancel (hT.trans hU.symm))).symm

/-- The final polar projection is the orthogonal projection onto the actual output range. -/
theorem finitePolar_final_projection (T : H →L[ℂ] H) :
    finitePolar T ∘L (finitePolar T).adjoint = T.range.starProjection := by
  have hUP : finitePolar T ∘L coimageProjection T = finitePolar T := by
    ext x
    have hker : coimageProjection T = coimageProjection (finitePolar T) := by
      simp only [coimageProjection, finitePolar_ker]
    rw [comp_apply, hker, comp_coimageProjection]
  have hp : IsStarProjection (finitePolar T ∘L (finitePolar T).adjoint) := by
    constructor
    · change (finitePolar T ∘L (finitePolar T).adjoint) ∘L
        (finitePolar T ∘L (finitePolar T).adjoint) = _
      calc
        _ = (finitePolar T ∘L ((finitePolar T).adjoint ∘L finitePolar T)) ∘L
            (finitePolar T).adjoint := by simp only [comp_assoc]
        _ = _ := by rw [finitePolar_initial_projection, hUP]
    · apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
      rw [adjoint_comp, adjoint_adjoint]
  obtain ⟨K, hK, heq⟩ := isStarProjection_iff_eq_starProjection.mp hp
  have hrange : K = (finitePolar T).range := by
    calc
      K = K.starProjection.range := (Submodule.range_starProjection K).symm
      _ = (finitePolar T ∘L (finitePolar T).adjoint).range := by rw [heq]
      _ = (finitePolar T).range := by
        apply le_antisymm
        · rintro y ⟨x, rfl⟩
          exact ⟨(finitePolar T).adjoint x, rfl⟩
        · rintro y ⟨x, rfl⟩
          refine ⟨finitePolar T x, ?_⟩
          change finitePolar T (((finitePolar T).adjoint ∘L finitePolar T) x) = _
          rw [finitePolar_initial_projection]
          exact DFunLike.congr_fun hUP x
  simpa only [hrange, finitePolar_range] using heq

#print axioms finitePolar_eq_zero_iff
#print axioms finitePolar_ker
#print axioms finitePolar_initial_projection
#print axioms finitePolar_norm_sq
#print axioms finitePolar_range
#print axioms finitePolar_final_projection

end HilbertMetric
