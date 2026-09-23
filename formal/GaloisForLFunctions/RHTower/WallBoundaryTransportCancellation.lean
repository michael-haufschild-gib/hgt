import GaloisForLFunctions.RHTower.WallBlockSourceExpansion
import GaloisForLFunctions.RHTower.StripPropagatorCancellation

/-!
# The transport cancels at the moving endpoint

The boundary terms produced by the two-fold integration by parts sit at the moving endpoint, where
they are multiplied by the propagator that variation of constants places in front of the whole
integral.  Since the phase map is the inverse propagator times a unimodular phase, that product is
exactly the phase:

`H(x+iσ)·E(x,L) = e^{-ixL}·I`.

So the propagated boundary terms carry no transport factor at all — the first is `C(x,L)^{-1}` and
the second `C^{-1}(C^{-1})'(x,L)`, each against the pure phase.  This is why the first boundary term
of the card's `(18)` does not decay and needs the accretive Laplace representation, while the second
already carries one power of the resolvent derivative and is square integrable on a ray by itself.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [Nontrivial X] in
/-- **The transport cancels at the moving endpoint.**  The boundary terms of the expansion, once
propagated, carry no transport factor at all: only the phase and the resolvent survive. -/
theorem stripPropagator_mul_wallPhaseMap
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ (2 : ℕ) = gammaRatio z)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (L x : ℝ) :
    stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) * wallPhaseMap E T σ L x
      = Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) • (1 : X →L[ℂ] X) := by
  have hz : ((x : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := shift_ne_zero hσ0 x
  have hEz : E ((x : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := branch_ne_zero hE hσ0 hσ1 x
  ext v
  show stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) (wallPhaseMap E T σ L x v) = _
  rw [wallPhaseMap, smul_apply, map_smul, stripPropagator_stripPropagatorInv hz hEz]
  simp

omit [Nontrivial X] in
/-- **The propagated boundary terms are transport-free.**  Whatever operator the expansion places
after the phase map at the moving endpoint survives multiplication by the propagator unchanged, up to
the pure phase. -/
theorem stripPropagator_mul_wallPhaseMap_mul
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ (2 : ℕ) = gammaRatio z)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (L x : ℝ) (A : X →L[ℂ] X) :
    stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) * (wallPhaseMap E T σ L x * A)
      = Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) • A := by
  rw [← mul_assoc, stripPropagator_mul_wallPhaseMap hE hσ0 hσ1, smul_mul_assoc, one_mul]

omit [Nontrivial X] in
/-- The propagated boundary term has exactly the norm of the resolvent factor. -/
theorem norm_stripPropagator_mul_wallPhaseMap_mul
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ (2 : ℕ) = gammaRatio z)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (L x : ℝ) (A : X →L[ℂ] X) :
    ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) * (wallPhaseMap E T σ L x * A)‖
      = ‖A‖ := by
  rw [stripPropagator_mul_wallPhaseMap_mul hE hσ0 hσ1, norm_smul, norm_expPhase, one_mul]

end GaloisForLFunctions.RHTower
