import GaloisForLFunctions.HTGeometry.HilbertSchmidtBadModeCount

/-!
# Counting energy from modes an operator nearly preserves

Family domination bounds a finite orthonormal family's total image energy by the operator's
Hilbert--Schmidt energy.  A lower bound on each image therefore forces the energy up: `N` members
each of image at least `c` cost `N c²`.

The form used in practice replaces the lower bound on the image by proximity to a unit vector: if
the operator carries each member to within `η` of *some* unit vector, each image has norm at least
`1 - η`, so `N` such members force energy `N (1 - η)²`.  Nothing requires the unit targets to be
related to each other, or the operator to be near an isometry anywhere else.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Family domination over a finite subset.**  The index type need not be finite. -/
theorem sum_finset_norm_sq_apply_le_hsNormSq {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {ι : Type*} {e : ι → E} (he : Orthonormal 𝕜 e) (S : Finset ι) :
    ∑ i ∈ S, ‖T (e i)‖ ^ 2 ≤ hsNormSq T := by
  classical
  have hortho : Orthonormal 𝕜 fun i : S => e (i : ι) :=
    he.comp _ Subtype.val_injective
  have hsum := sum_norm_sq_apply_le_hsNormSq hT hortho
  rwa [Finset.sum_coe_sort S fun i => ‖T (e i)‖ ^ 2] at hsum

/-- **Energy from uncontracted modes.**  A finite subset of an orthonormal family on which the
operator's image never falls below `c` costs `card * c²` of Hilbert--Schmidt energy. -/
theorem card_mul_sq_le_hsNormSq_of_le_norm_apply {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {ι : Type*} {e : ι → E} (he : Orthonormal 𝕜 e) (S : Finset ι) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i ∈ S, c ≤ ‖T (e i)‖) :
    (S.card : ℝ) * c ^ 2 ≤ hsNormSq T := by
  classical
  refine le_trans ?_ (sum_finset_norm_sq_apply_le_hsNormSq hT he S)
  have hconst : (S.card : ℝ) * c ^ 2 = ∑ _i ∈ S, c ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  refine Finset.sum_le_sum fun i hi => ?_
  nlinarith [h i hi, hc]

/-- **Energy from nearly preserved modes.**  If the operator carries each member of a finite subset
of an orthonormal family to within `η` of a unit vector, the Hilbert--Schmidt energy is at least
`card * (1 - η)²`. -/
theorem card_mul_sq_le_hsNormSq_of_near_unit {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {ι : Type*} {e : ι → E} (he : Orthonormal 𝕜 e) (S : Finset ι) (u : ι → F)
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (η : ℝ) (hη : η ≤ 1)
    (h : ∀ i ∈ S, ‖T (e i) - u i‖ ≤ η) :
    (S.card : ℝ) * (1 - η) ^ 2 ≤ hsNormSq T := by
  refine card_mul_sq_le_hsNormSq_of_le_norm_apply hT he S (1 - η) (by linarith) fun i hi => ?_
  have hrev : ‖u i‖ - ‖T (e i)‖ ≤ ‖u i - T (e i)‖ := norm_sub_norm_le _ _
  have hsym : ‖u i - T (e i)‖ = ‖T (e i) - u i‖ := norm_sub_rev _ _
  have hbound := h i hi
  rw [hsym, hu i hi] at hrev
  linarith

end RHTower
