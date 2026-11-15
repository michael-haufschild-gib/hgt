import GaloisForLFunctions.RepresentationLifting.CyclicIntegralGluing
import GaloisForLFunctions.HTGeometry.SingularIntegralCokernel

/-!
# Integral coinvariants of the moving cyclic lattice

For the integral regular representation of a finite cyclic group, let `K` be
the norm kernel and `Δ` translation by a generator minus the identity. Exactness
gives `ΔL = K`, but restricting the domain changes the cokernel:
`K / ΔK ≃ ℤ/|G|ℤ`. The difference map identifies this quotient with the gluing
group `L / (ker Δ + K)`. This is the integral comparison in Lemma 1.3 of the
cyclotomic Artin–Tate argument (https://arxiv.org/abs/2611.13468).
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

variable (G : Type) [CommGroup G] [Fintype G] [IsCyclic G]

/-- The moving integral lattice is the kernel of the cyclic norm. -/
abbrev CyclicIntegralMoving := LinearMap.ker (cyclicRegularNorm ℤ G)

/-- The cyclic difference, with its codomain restricted to the moving lattice. -/
def cyclicDeltaToMoving : CyclicRegular ℤ G →ₗ[ℤ] CyclicIntegralMoving G :=
  (cyclicRegularDelta ℤ G).codRestrict _ fun x => by
    change cyclicRegularDelta ℤ G x ∈ LinearMap.ker (cyclicRegularNorm ℤ G)
    rw [← cyclicRegular_delta_norm_exact]
    exact ⟨x, rfl⟩

/-- Difference restricted to the moving lattice in both domain and codomain. -/
def cyclicMovingDelta : Module.End ℤ (CyclicIntegralMoving G) :=
  (cyclicDeltaToMoving G).comp (CyclicIntegralMoving G).subtype

/-- Integral coinvariants of the moving cyclic lattice. -/
abbrev CyclicMovingCoinvariants :=
  CyclicIntegralMoving G ⧸ LinearMap.range (cyclicMovingDelta G)

/-- Difference followed by passage to the moving coinvariants. -/
def cyclicMovingQuotientMap : CyclicRegular ℤ G →ₗ[ℤ] CyclicMovingCoinvariants G :=
  (LinearMap.range (cyclicMovingDelta G)).mkQ.comp (cyclicDeltaToMoving G)

/-- The ambiguity in lifting a moving coinvariant is exactly the gluing lattice. -/
theorem cyclicMovingQuotientMap_ker :
    (cyclicMovingQuotientMap G).ker = cyclicIntegralGluingSubmodule G := by
  ext x
  change cyclicDeltaToMoving G x ∈
    LinearMap.ker (LinearMap.range (cyclicMovingDelta G)).mkQ ↔ _
  rw [Submodule.ker_mkQ]
  constructor
  · rintro ⟨y, hy⟩
    have hd : cyclicRegularDelta ℤ G (y : CyclicRegular ℤ G) =
        cyclicRegularDelta ℤ G x := congrArg Subtype.val hy
    refine Submodule.mem_sup.mpr ⟨x - y, ?_, y, y.property, sub_add_cancel _ _⟩
    change cyclicRegularDelta ℤ G (x - y) = 0
    rw [map_sub, hd, sub_self]
  · intro hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
    change cyclicRegularDelta ℤ G v = cyclicRegularDelta ℤ G (u + v)
    rw [map_add, hu, zero_add]

/-- Every moving coinvariant is represented by a cyclic difference. -/
theorem cyclicMovingQuotientMap_surjective :
    Function.Surjective (cyclicMovingQuotientMap G) := by
  intro q
  obtain ⟨y, rfl⟩ := (LinearMap.range (cyclicMovingDelta G)).mkQ_surjective q
  have hy : (y : CyclicRegular ℤ G) ∈ LinearMap.range (cyclicRegularDelta ℤ G) := by
    rw [cyclicRegular_delta_norm_exact]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, congrArg (LinearMap.range (cyclicMovingDelta G)).mkQ (Subtype.ext hx)⟩

/-- The cyclic difference identifies the integral gluing group with moving coinvariants. -/
def cyclicMovingGluingEquiv :
    (CyclicRegular ℤ G ⧸ cyclicIntegralGluingSubmodule G) ≃ₗ[ℤ]
      CyclicMovingCoinvariants G :=
  (Submodule.quotEquivOfEq _ _ (cyclicMovingQuotientMap_ker G).symm).trans
    ((cyclicMovingQuotientMap G).quotKerEquivOfSurjective
      (cyclicMovingQuotientMap_surjective G))

/-- The restricted difference has exactly one cyclic integral defect of order `|G|`. -/
def cyclicMovingCoinvariantsEquiv :
    CyclicMovingCoinvariants G ≃ₗ[ℤ] ZMod (Fintype.card G) :=
  (cyclicMovingGluingEquiv G).symm.trans (cyclicIntegralGluingEquiv G)

/-- The moving coinvariants have order equal to the cyclic group order. -/
theorem card_cyclicMovingCoinvariants :
    Nat.card (CyclicMovingCoinvariants G) = Fintype.card G := by
  rw [Nat.card_congr (cyclicMovingCoinvariantsEquiv G).toEquiv, Nat.card_zmod]

/-- The absolute determinant of the difference on the moving lattice is the group order. -/
theorem cyclicMovingDelta_det_natAbs :
    (LinearMap.det (cyclicMovingDelta G)).natAbs = Fintype.card G := by
  rw [← LinearMap.card_quotient_range_eq_natAbs_det_all]
  exact card_cyclicMovingCoinvariants G

#print axioms cyclicMovingDelta_det_natAbs

#print axioms cyclicMovingQuotientMap_ker
#print axioms cyclicMovingCoinvariantsEquiv

end GaloisForLFunctions.RepresentationLifting
