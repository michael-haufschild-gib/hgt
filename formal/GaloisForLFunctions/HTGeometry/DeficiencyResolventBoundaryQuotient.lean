import GaloisForLFunctions.HTGeometry.ResolventCompactness
import GaloisForLFunctions.HTGeometry.VonNeumannDeficiency

/-!
# Boundary quotient for an actual self-adjoint deficiency resolvent

At a nonreal spectral parameter, the resolvent of a self-adjoint deficiency extension has an
exact decomposition into a closure-domain term and one boundary term.  The boundary coefficient
is the reciprocal of the literal Green boundary pairing of an adjoint eigenvector.  No spectral
measure, compact-resolvent assumption, or finite-dimensional model enters.
-/

open Complex
open scoped InnerProductSpace LinearPMap

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The nonreal resolvent of a self-adjoint deficiency extension has an exact boundary quotient.

The adjoint eigenvector `w` has eigenvalue `star z`; its Green pairing against the extension
boundary generator is therefore the sole denominator in the boundary component of
`(A - z)⁻¹ v`. -/
theorem exists_resolvent_boundary_quotient
    {S : H →ₗ.[ℂ] H} (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (p m : S.adjoint.domain) (u : ℂ)
    (hSelf : IsSelfAdjoint (LinearPMap.deficiencyExtension hDense hSymm p m u))
    {z : ℂ} (hz : z.im ≠ 0) (w : S.adjoint.domain)
    (hw : S.adjoint w = star z • (w : H))
    (hboundary : LinearPMap.adjointBoundaryPairing S w (p + u • m) ≠ 0)
    (v : H) :
    ∃ c : S.closure.domain,
      resolventLinear hSelf hz v = (c : H) +
        (-inner ℂ (w : H) v / LinearPMap.adjointBoundaryPairing S w (p + u • m)) •
          LinearPMap.deficiencyBoundaryVector p m u := by
  let A := LinearPMap.deficiencyExtension hDense hSymm p m u
  let r : H := resolventLinear hSelf hz v
  let rd : A.domain := ⟨r, resolventLinear_mem hSelf hz v⟩
  let hrAdj : S.adjoint.domain :=
    ⟨r, LinearPMap.deficiencyExtensionDomain_le_adjoint hDense hSymm p m u rd.property⟩
  have hhr : (hrAdj : H) = r := rfl
  have hshift : A rd - z • r = v := by
    simpa only [A, r, rd] using shiftedMap_resolventLinear hSelf hz v
  have hAeq : A rd = S.adjoint hrAdj := by
    change S.adjoint ⟨(rd : H), _⟩ = S.adjoint hrAdj
    congr 1
  have hAr : S.adjoint hrAdj = v + z • r := by
    rw [← hAeq]
    exact sub_eq_iff_eq_add.mp hshift
  obtain ⟨c, q, hdec⟩ :=
    LinearPMap.exists_closure_add_smul_boundary p m u rd.property
  let cAdj : S.adjoint.domain :=
    ⟨(c : H), (LinearPMap.closure_le_adjoint hDense hSymm).1 c.property⟩
  have hradjdec : hrAdj = cAdj + q • (p + u • m) := by
    apply Subtype.ext
    rw [hhr]
    change r = (c : H) + q • LinearPMap.deficiencyBoundaryVector p m u
    exact hdec
  have hpair : LinearPMap.adjointBoundaryPairing S w hrAdj = -inner ℂ (w : H) v := by
    rw [LinearPMap.adjointBoundaryPairing, hw, hAr, inner_smul_left,
      inner_add_right, inner_smul_right]
    rw [hhr]
    simp only [starRingEnd_apply, star_star]
    ring
  have hpairdec : LinearPMap.adjointBoundaryPairing S w hrAdj =
      q * LinearPMap.adjointBoundaryPairing S w (p + u • m) := by
    rw [hradjdec, LinearPMap.adjointBoundaryPairing_add_right,
      LinearPMap.adjointBoundaryPairing_smul_right,
      LinearPMap.adjointBoundaryPairing_closure_right hDense hSymm]
    ring
  have hq : q = -inner ℂ (w : H) v /
      LinearPMap.adjointBoundaryPairing S w (p + u • m) := by
    apply (eq_div_iff hboundary).2
    rw [← hpairdec]
    exact hpair
  refine ⟨c, ?_⟩
  change r = _
  simpa only [rd] using hdec.trans (by rw [hq])

end GaloisForLFunctions.HTGeometry
