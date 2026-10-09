import GaloisForLFunctions.HTGeometry.PaperStabilizedPolynomialClock
import GaloisForLFunctions.HTGeometry.PaperComplexSliceFibers

/-!
Canonical fibres of the actual stabilized polynomial clock.
Every level is the same complex algebra of clock constants. Requiring transport
to preserve these constants determines the map uniquely, with exact composition.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open StableCoordinate

abbrev paperStabilizedClockConstants : Subalgebra ℂ (R 5) :=
  complexDerivationKernel paperStabilizedClock

def paperStabilizedClockFiberIdeal (c : ℂ) : Ideal (R 5) :=
  Ideal.span {stabilize f - algebraMap ℂ (R 5) c}

abbrev paperStabilizedClockFiber (c : ℂ) := R 5 ⧸ paperStabilizedClockFiberIdeal c

/-- A fixed constant algebra identifies all scalar fibres, including zero. -/
def paperStabilizedClockFiberEquiv (c : ℂ) :
    paperStabilizedClockFiber c ≃ₐ[ℂ] paperStabilizedClockConstants :=
  complexSliceFiberEquiv paperStabilizedClock paperStabilizedClock_slice
    paperStabilizedClock_locallyNilpotent c

@[simp] theorem paperStabilizedClockFiberEquiv_constant (c : ℂ)
    (x : paperStabilizedClockConstants) :
    paperStabilizedClockFiberEquiv c
      (Ideal.Quotient.mk (paperStabilizedClockFiberIdeal c) (x : R 5)) = x :=
  complexSliceFiberEquiv_constant paperStabilizedClock paperStabilizedClock_slice
    paperStabilizedClock_locallyNilpotent c x

theorem paperStabilizedClockFiber_unique_constant (c : ℂ) (z : paperStabilizedClockFiber c) :
    ∃! x : paperStabilizedClockConstants,
      Ideal.Quotient.mk (paperStabilizedClockFiberIdeal c) (x : R 5) = z :=
  complexSliceFiber_unique_constant paperStabilizedClock paperStabilizedClock_slice
    paperStabilizedClock_locallyNilpotent c z

/-- A clock constant vanishes in a level fibre exactly when it is zero already. -/
theorem paperStabilizedClockConstant_mem_fiber_iff_zero (c : ℂ)
    (x : paperStabilizedClockConstants) :
    (x : R 5) ∈ paperStabilizedClockFiberIdeal c ↔ x = 0 :=
  complexSliceKernel_mem_fiber_iff_zero paperStabilizedClock paperStabilizedClock_slice
    paperStabilizedClock_locallyNilpotent c x

theorem paperStabilizedClockFiber_constants_eq_iff (c : ℂ)
    (x y : paperStabilizedClockConstants) :
    Ideal.Quotient.mk (paperStabilizedClockFiberIdeal c) (x : R 5) =
      Ideal.Quotient.mk (paperStabilizedClockFiberIdeal c) (y : R 5) ↔ x = y := by
  constructor
  · intro h
    have he := congrArg (paperStabilizedClockFiberEquiv c) h
    simpa only [paperStabilizedClockFiberEquiv_constant] using he
  · rintro rfl
    rfl

def paperStabilizedClockFiberTransport (c d : ℂ) :
    paperStabilizedClockFiber c ≃ₐ[ℂ] paperStabilizedClockFiber d :=
  complexSliceFiberTransport paperStabilizedClock paperStabilizedClock_slice
    paperStabilizedClock_locallyNilpotent c d

@[simp] theorem paperStabilizedClockFiberTransport_constant (c d : ℂ)
    (x : paperStabilizedClockConstants) :
    paperStabilizedClockFiberTransport c d
      (Ideal.Quotient.mk (paperStabilizedClockFiberIdeal c) (x : R 5)) =
        Ideal.Quotient.mk (paperStabilizedClockFiberIdeal d) (x : R 5) :=
  complexSliceFiberTransport_constant paperStabilizedClock paperStabilizedClock_slice
    paperStabilizedClock_locallyNilpotent c d x

theorem paperStabilizedClockFiberTransport_cocycle (c d e : ℂ) :
    (paperStabilizedClockFiberTransport c d).trans (paperStabilizedClockFiberTransport d e) =
      paperStabilizedClockFiberTransport c e :=
  complexSliceFiberTransport_cocycle paperStabilizedClock paperStabilizedClock_slice
    paperStabilizedClock_locallyNilpotent c d e

@[simp] theorem paperStabilizedClockFiberTransport_refl (c : ℂ) :
    paperStabilizedClockFiberTransport c c = AlgEquiv.refl := by
  ext z
  change (paperStabilizedClockFiberEquiv c).symm (paperStabilizedClockFiberEquiv c z) = z
  exact (paperStabilizedClockFiberEquiv c).symm_apply_apply z

/-- Fixing the actual clock constants uniquely determines transport between any two fibres. -/
theorem paperStabilizedClockFiber_unique_transport (c d : ℂ) :
    ∃! φ : paperStabilizedClockFiber c →ₐ[ℂ] paperStabilizedClockFiber d,
      ∀ x : paperStabilizedClockConstants,
        φ (Ideal.Quotient.mk (paperStabilizedClockFiberIdeal c) (x : R 5)) =
          Ideal.Quotient.mk (paperStabilizedClockFiberIdeal d) (x : R 5) := by
  refine ⟨(paperStabilizedClockFiberTransport c d).toAlgHom,
    paperStabilizedClockFiberTransport_constant c d, ?_⟩
  intro φ hφ
  ext z
  obtain ⟨x, hx, _⟩ := paperStabilizedClockFiber_unique_constant c z
  rw [← hx, hφ x]
  exact (paperStabilizedClockFiberTransport_constant c d x).symm

end
end GaloisForLFunctions.HTGeometry
