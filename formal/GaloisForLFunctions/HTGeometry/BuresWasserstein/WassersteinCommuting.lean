import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinEquation

/-!
# Consistency of the Wasserstein mean with commuting families

If the data commute, the Wasserstein equation is solved by the square of the weighted arithmetic
mean of the square roots.  In the commuting case the geometric mean `Aᵢ # X⁻¹` collapses to the
product `Aᵢ^{1/2} X^{-1/2}`, which is recognised by the Riccati uniqueness `gm_unique`.
-/

open scoped NNReal Ring BigOperators

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*}

omit [PartialOrder A] [StarOrderedRing A] in
/-- Commutation passes to the ring inverse. -/
lemma commute_ringInverse_left {a b : A} (hu : IsUnit a) (h : Commute a b) :
    Commute (a⁻¹ʳ : A) b := by
  obtain ⟨v, rfl⟩ := hu
  rw [Ring.inverse_unit]
  exact h.units_inv_left

/-- Commutation passes to the half power. -/
lemma commute_rpow_left {a b : A} (h : Commute a b) (y : ℝ) : Commute (a ^ y) b := by
  rw [CFC.rpow_def]
  exact Commute.cfc_nnreal h _

/-- **Proposition 6.1(1) (Kim–Mer–Pálfia): consistency with scalars.**  For a commuting family
the square of the weighted arithmetic mean of the square roots is a Wasserstein point.  The
normalisation `∑ wᵢ = 1` is not needed. -/
theorem isWassersteinPoint_of_commute {s : Finset ι} (hs : s.Nonempty) {w : ι → ℝ}
    {Av : ι → A} (hw : ∀ i ∈ s, 0 < w i)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, Commute (Av i) (Av j)) :
    IsWassersteinPoint s w Av ((∑ i ∈ s, w i • (Av i) ^ (1/2 : ℝ))
      * (∑ i ∈ s, w i • (Av i) ^ (1/2 : ℝ))) := by
  classical
  set S : A := ∑ i ∈ s, w i • (Av i) ^ (1/2 : ℝ) with hSdef
  have hrp : ∀ i ∈ s, IsStrictlyPositive ((Av i) ^ (1/2 : ℝ)) :=
    fun i hi => (hA i hi).rpow _ _
  have hSpos : IsStrictlyPositive S := isStrictlyPositive_sum_smul hs hw hrp
  have hSsa : IsSelfAdjoint S := hSpos.isSelfAdjoint
  -- commutation bookkeeping
  have hcAS : ∀ i ∈ s, Commute (Av i) S := by
    intro i hi
    rw [hSdef]
    exact Commute.sum_right _ _ _ fun j hj =>
      ((commute_rpow_left (hcomm j hj i hi) (1/2 : ℝ)).symm).smul_right _
  have hcSinvA : ∀ i ∈ s, Commute (S⁻¹ʳ : A) (Av i) := fun i hi =>
    commute_ringInverse_left hSpos.isUnit (hcAS i hi).symm
  have hcSinvRp : ∀ i ∈ s, Commute (S⁻¹ʳ : A) ((Av i) ^ (1/2 : ℝ)) := fun i hi =>
    (commute_rpow_left (hcSinvA i hi).symm (1/2 : ℝ)).symm
  have hcSinvInv : ∀ i ∈ s, Commute (S⁻¹ʳ : A) ((Av i)⁻¹ʳ) := fun i hi =>
    (commute_ringInverse_left (hA i hi).isUnit (hcSinvA i hi).symm).symm
  have hcInvRp : ∀ i ∈ s, Commute ((Av i)⁻¹ʳ : A) ((Av i) ^ (1/2 : ℝ)) := fun i hi =>
    commute_ringInverse_left (hA i hi).isUnit
      (commute_rpow_left (Commute.refl (Av i)) (1/2 : ℝ)).symm
  -- the candidate
  have hXpos : IsStrictlyPositive (S * S) := by
    refine ⟨?_, hSpos.isUnit.mul hSpos.isUnit⟩
    nth_rewrite 1 [← hSsa.star_eq]
    exact star_mul_self_nonneg S
  have hXinv : ((S * S)⁻¹ʳ : A) = S⁻¹ʳ * S⁻¹ʳ := Ring.inverse_mul (Or.inl hSpos.isUnit)
  have hgm : ∀ i ∈ s, gm (Av i) ((S * S)⁻¹ʳ) = (Av i) ^ (1/2 : ℝ) * S⁻¹ʳ := by
    intro i hi
    refine (gm_unique (hA i hi) ?_ ?_).symm
    · exact (commute_iff_mul_nonneg (hrp i hi).nonneg hSpos.ringInverse.nonneg).mp
        (hcSinvRp i hi).symm
    · have hpp : ((Av i) ^ (1/2 : ℝ) : A) * (Av i) ^ (1/2 : ℝ) = Av i :=
        rpow_half_mul_rpow_half (hA i hi)
      calc ((Av i) ^ (1/2 : ℝ) * S⁻¹ʳ : A) * (Av i)⁻¹ʳ * ((Av i) ^ (1/2 : ℝ) * S⁻¹ʳ)
          = (Av i) ^ (1/2 : ℝ) * (S⁻¹ʳ * (Av i)⁻¹ʳ) * ((Av i) ^ (1/2 : ℝ) * S⁻¹ʳ) := by
            noncomm_ring
        _ = (Av i) ^ (1/2 : ℝ) * ((Av i)⁻¹ʳ * S⁻¹ʳ) * ((Av i) ^ (1/2 : ℝ) * S⁻¹ʳ) := by
            rw [(hcSinvInv i hi).eq]
        _ = (Av i) ^ (1/2 : ℝ) * (Av i)⁻¹ʳ * (S⁻¹ʳ * (Av i) ^ (1/2 : ℝ)) * S⁻¹ʳ := by
            noncomm_ring
        _ = (Av i) ^ (1/2 : ℝ) * (Av i)⁻¹ʳ * ((Av i) ^ (1/2 : ℝ) * S⁻¹ʳ) * S⁻¹ʳ := by
            rw [(hcSinvRp i hi).eq]
        _ = (Av i) ^ (1/2 : ℝ) * ((Av i)⁻¹ʳ * (Av i) ^ (1/2 : ℝ)) * (S⁻¹ʳ * S⁻¹ʳ) := by
            noncomm_ring
        _ = ((Av i) ^ (1/2 : ℝ) * (Av i) ^ (1/2 : ℝ)) * (Av i)⁻¹ʳ * (S⁻¹ʳ * S⁻¹ʳ) := by
            rw [(hcInvRp i hi).eq]; noncomm_ring
        _ = (S⁻¹ʳ : A) * S⁻¹ʳ := by
            rw [hpp, Ring.mul_inverse_cancel _ (hA i hi).isUnit, one_mul]
        _ = ((S * S)⁻¹ʳ : A) := hXinv.symm
  refine ⟨hXpos, ?_⟩
  calc ∑ i ∈ s, w i • gm (Av i) ((S * S)⁻¹ʳ)
      = ∑ i ∈ s, w i • ((Av i) ^ (1/2 : ℝ) * S⁻¹ʳ) :=
        Finset.sum_congr rfl fun i hi => by rw [hgm i hi]
    _ = (∑ i ∈ s, w i • (Av i) ^ (1/2 : ℝ)) * S⁻¹ʳ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (smul_mul_assoc _ _ _).symm
    _ = 1 := by rw [← hSdef, Ring.mul_inverse_cancel _ hSpos.isUnit]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
