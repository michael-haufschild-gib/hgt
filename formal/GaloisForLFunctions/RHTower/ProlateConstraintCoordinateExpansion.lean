import GaloisForLFunctions.RHTower.ProlateSignedSlepianBasis

/-!
# The constraint functional in signed Slepian coordinates

Expanding a carrier vector in the signed Slepian basis and applying the continuous linear functional
`y ↦ ⟪1_{[-a,a]}, y⟫` term by term shows that the zero-integral constraint is exactly the vanishing
of the coordinate series against `evenProlateConstraintCoord`, which is the constraint sequence `ℓ`
of the constrained-prolate transfer theorems.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- **The constraint functional expands in the signed Slepian coordinates.** -/
theorem hasSum_inner_evenCentralIndicator {a : ℝ} (ha : 0 < a)
    (x : evenTimeLimitedSubspace a) :
    HasSum (fun n : signedLiveIndex a =>
        (signedCarrierBasis a ha).repr x n * evenProlateConstraintCoord a n.1)
      (inner ℂ (evenCentralIndicator a) ((x : evenTimeLimitedSubspace a) : evenSubspace)) := by
  have hrepr := (signedCarrierBasis a ha).hasSum_repr x
  set f : evenTimeLimitedSubspace a →L[ℂ] ℂ :=
    (innerSL ℂ (evenCentralIndicator a)).comp (evenTimeLimitedSubspace a).subtypeL with hfdef
  have hmap := f.hasSum hrepr
  have hterm : ∀ n : signedLiveIndex a,
      f ((signedCarrierBasis a ha).repr x n • (signedCarrierBasis a ha) n)
        = (signedCarrierBasis a ha).repr x n * evenProlateConstraintCoord a n.1 := by
    intro n
    rw [map_smul, signedCarrierBasis_apply]
    have hval : f (signedCarrierMode a n)
        = evenProlateConstraintCoord a n.1 := rfl
    rw [hval, smul_eq_mul]
  have hfun : (fun n : signedLiveIndex a =>
      f ((signedCarrierBasis a ha).repr x n • (signedCarrierBasis a ha) n))
      = fun n : signedLiveIndex a =>
        (signedCarrierBasis a ha).repr x n * evenProlateConstraintCoord a n.1 := funext hterm
  rw [hfun] at hmap
  exact hmap

/-- **The zero-integral constraint in coordinates.** -/
theorem mem_constrainedProlateSubspace_iff_tsum {a : ℝ} (ha : 0 < a)
    (x : evenTimeLimitedSubspace a) :
    ((x : evenTimeLimitedSubspace a) : evenSubspace) ∈ constrainedProlateSubspace a
      ↔ (∑' n : signedLiveIndex a,
          (signedCarrierBasis a ha).repr x n * evenProlateConstraintCoord a n.1) = 0 := by
  have hsum := hasSum_inner_evenCentralIndicator ha x
  rw [hsum.tsum_eq]
  rw [constrainedProlateSubspace, Submodule.mem_inf,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨x.2, h⟩

end RHTower

end
