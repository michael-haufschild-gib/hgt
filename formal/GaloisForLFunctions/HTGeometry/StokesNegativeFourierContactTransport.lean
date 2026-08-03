import GaloisForLFunctions.HTGeometry.StokesFormalContactInvariance

/-!
# Exact negative-Fourier transport of Laurent contact geometry

This capstone combines three source layers: a genuine coefficient-one Laurent realization of an
Airy characteristic, the exact reciprocal local-Fourier coordinate, and valuation invariance of
tangent formal automorphisms.  It proves in one statement that the negative Airy branch strictly
drops ramification, normalizes the reciprocal Fourier coordinate to an exact power, and preserves
every pairwise Laurent contact and the entire threshold hierarchy when irregular values are
re-expressed in that coordinate.
-/

open scoped PowerSeries

namespace GaloisForLFunctions
namespace IrregularStokes
namespace Characteristic

open FormalUniformizer LaurentFourier

noncomputable section

/-- **Exact negative-Fourier contact-transport law.**  For the canonical Laurent realization of
every Airy tower, the first negative Fourier step has new ramification
`E = nextRamification < R`.  Its reciprocal Fourier coordinate is exactly the image of `X^E`
under a tangent Laurent automorphism.  Re-expression by the inverse automorphism preserves every
pairwise contact and the full contact-threshold hierarchy for every family of Laurent irregular
values. -/
theorem airyTower_negativeFourier_contact_transport
    {R beta : ℕ} (c : Characteristic R beta) (hc : c.IsAiryTower) :
    ∃ u : PowerSeries ℂ, u.constantCoeff = 1 ∧
      ∃ phi : LaurentSeries ℂ ≃ₐ[ℂ] LaurentSeries ℂ,
      c.nextRamification < R ∧
      c.canonicalLaurent = normalizedIrregularValue R c.nextRamification u ∧
      (localFourierCoordinate R c.canonicalLaurent).order =
        -(c.nextRamification : ℤ) ∧
      (localFourierReciprocalCoordinate R c.canonicalLaurent).order =
        (c.nextRamification : ℤ) ∧
      localFourierReciprocalCoordinate R c.canonicalLaurent =
        phi ((PowerSeries.X ^ c.nextRamification : PowerSeries ℂ) :
          LaurentSeries ℂ) ∧
      ∀ (ι : Type) (q : ι → LaurentSeries ℂ),
        (∀ i j,
          laurentContactMatrix (fun k => phi.symm (q k)) i j =
            laurentContactMatrix q i j) ∧
        laurentContactHierarchy (fun k => phi.symm (q k)) =
          laurentContactHierarchy q := by
  let u := c.canonicalLaurent.powerSeriesPart
  have hu : u.constantCoeff = 1 :=
    c.canonicalLaurent_powerSeriesPart_constantCoeff
  let v := u⁻¹
  have hv : v.constantCoeff = 1 := by simp [v, hu]
  let phi : LaurentSeries ℂ ≃ₐ[ℂ] LaurentSeries ℂ :=
    laurentAlgReparametrization c.nextRamification v hv
  have hform : c.canonicalLaurent =
      normalizedIrregularValue R c.nextRamification u :=
    c.canonicalLaurent_eq_normalizedIrregularValue
      (c.isAiryTower_firstExponent_eq hc)
  have hcoordinate : localFourierReciprocalCoordinate R c.canonicalLaurent =
      phi ((PowerSeries.X ^ c.nextRamification : PowerSeries ℂ) :
        LaurentSeries ℂ) := by
    rw [hform, localFourierReciprocalCoordinate_normalized
      R c.nextRamification u hu]
    exact (laurentAlgReparametrization_X_pow c.nextRamification_pos v hv).symm
  refine ⟨u, hu, phi, c.nextRamification_lt, hform, ?_, ?_, hcoordinate, ?_⟩
  · rw [hform]
    exact localFourierCoordinate_normalized_order R c.nextRamification u hu
  · rw [hform]
    exact localFourierReciprocalCoordinate_normalized_order
      R c.nextRamification u hu
  · intro ι q
    constructor
    · intro i j
      exact laurentAlgReparametrization_symm_contactTop
        c.nextRamification v hv (q i) (q j)
    · exact laurentContactHierarchy_symm_reparametrization
        c.nextRamification v hv q

end
end Characteristic
end IrregularStokes
end GaloisForLFunctions
