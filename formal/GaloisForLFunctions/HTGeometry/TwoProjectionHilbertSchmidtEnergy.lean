/-
# Hilbert--Schmidt energy splitting for two quantum projections

The supersymmetric calculus of two projections separates a zero-mode-corrected complement into
two orthogonal transition channels.  If

`C = Z - (1 - P - R)`

and

`D = (1 - R)(1 - P) - Z`,

then `C = RP - D`.  For orthogonal projections the two summands are Hilbert--Schmidt orthogonal:
the range of `RP` lies in the `R` sector, whereas the range of `D` lies in the complementary
sector after removal of the joint zero mode.  Consequently

`||C||_HS^2 = ||RP||_HS^2 + ||D||_HS^2`.

This is the trace-energy form of the two-projection supersymmetry used for pairs of Fermi
projections.  It is a static value relation and needs no spectral decomposition.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.HTGeometry.TwoProjectionSupersymmetry

noncomputable section

namespace HTGeometry

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The overlap of the complementary projection sectors after subtracting the specified joint
zero-mode projection. -/
def twoProjectionExteriorOverlap
    (P R Z : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 - R) * (1 - P) - Z

/-- The zero-mode-corrected complement is the difference of the interior and exterior overlap
channels. -/
theorem twoProjection_correctedComplement_eq_overlap_sub_exterior
    (P R Z : H →L[ℂ] H) :
    Z - (1 - P - R) = R * P - twoProjectionExteriorOverlap P R Z := by
  rw [twoProjectionExteriorOverlap]
  noncomm_ring

/-- If the corrected complement and the interior overlap are Hilbert--Schmidt, then so is the
zero-mode-subtracted exterior overlap. -/
theorem twoProjectionExteriorOverlap_isHilbertSchmidt
    (P R Z : H →L[ℂ] H)
    (hC : IsHilbertSchmidt (Z - (1 - P - R)))
    (hRP : IsHilbertSchmidt (R * P)) :
    IsHilbertSchmidt (twoProjectionExteriorOverlap P R Z) := by
  have hEq : twoProjectionExteriorOverlap P R Z = R * P - (Z - (1 - P - R)) := by
    rw [twoProjectionExteriorOverlap]
    noncomm_ring
  rw [hEq]
  exact hRP.sub hC

/-- The interior overlap `RP` is Hilbert--Schmidt orthogonal to the corrected exterior overlap.
Only the projection law for `R`, self-adjointness of `P,R`, and removal of the `R`-zero mode are
used. -/
theorem hsInner_twoProjection_overlap_exterior_eq_zero
    (P R Z : H →L[ℂ] H)
    (hR : IsIdempotentElem R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hRZ : R * Z = 0) :
    hsInner (R * P) (twoProjectionExteriorOverlap P R Z) = 0 := by
  have hAdj : ContinuousLinearMap.adjoint (R * P) = P * R := by
    change ContinuousLinearMap.adjoint (R ∘L P) = P ∘L R
    rw [ContinuousLinearMap.adjoint_comp, hPadj, hRadj]
  have hzero :
      ContinuousLinearMap.adjoint (R * P) ∘L
          twoProjectionExteriorOverlap P R Z = 0 := by
    rw [hAdj]
    change (P * R) * ((1 - R) * (1 - P) - Z) = 0
    have hRR : R * R = R := hR
    noncomm_ring [hRR, hRZ]
  have htrace :
      opTrace
          (ContinuousLinearMap.adjoint (R * P) ∘L
            twoProjectionExteriorOverlap P R Z) =
        hsInner (R * P) (twoProjectionExteriorOverlap P R Z) := by
    simpa using opTrace_comp_eq_hsInner
      (ContinuousLinearMap.adjoint (R * P))
      (twoProjectionExteriorOverlap P R Z)
  calc
    hsInner (R * P) (twoProjectionExteriorOverlap P R Z) =
        opTrace
          (ContinuousLinearMap.adjoint (R * P) ∘L
            twoProjectionExteriorOverlap P R Z) := htrace.symm
    _ = opTrace 0 := congrArg opTrace hzero
    _ = 0 := by simp [opTrace]

/-- **Two-projection Hilbert--Schmidt energy split.**  The energy of the zero-mode-corrected
supersymmetric partner is exactly the sum of its interior and exterior transition energies.
This replaces an opaque correction norm by two positive overlap values. -/
theorem hsNormSq_twoProjection_correctedComplement_eq_overlap_add_exterior
    (P R Z : H →L[ℂ] H)
    (hR : IsIdempotentElem R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hRZ : R * Z = 0)
    (hC : IsHilbertSchmidt (Z - (1 - P - R)))
    (hRP : IsHilbertSchmidt (R * P)) :
    hsNormSq (Z - (1 - P - R)) =
      hsNormSq (R * P) + hsNormSq (twoProjectionExteriorOverlap P R Z) := by
  have hD := twoProjectionExteriorOverlap_isHilbertSchmidt P R Z hC hRP
  have horth := hsInner_twoProjection_overlap_exterior_eq_zero
    P R Z hR hPadj hRadj hRZ
  rw [twoProjection_correctedComplement_eq_overlap_sub_exterior]
  exact hsNormSq_sub_eq_add_of_hsInner_eq_zero hRP hD horth

end

end HTGeometry
