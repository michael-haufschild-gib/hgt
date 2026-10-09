import GaloisForLFunctions.HTGeometry.PaperPolynomialPointEquiv
import GaloisForLFunctions.HTGeometry.PaperStabilizedAdditiveAction

/-!
# The stabilized clock as a polynomial flow of complex points

The actual additive action supplies polynomial coordinates and polynomial
inverses at every complex time. Its distinguished level increases at unit
speed, so every orbit meets every level exactly once.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate CoactionLND MvPolynomial

noncomputable section

/-- Polynomial witnesses for the stabilized time map and its inverse. -/
def paperStabilizedPointCoordinates (t : ℂ) :
    AmbientMaps.PolynomialEquiv ℂ (Fin 5) (Fin 5) :=
  AmbientMaps.PolynomialEquiv.ofAlgEquiv (paperStabilizedTranslation t)

/-- The actual stabilized clock acts bijectively on ordinary complex points. -/
def paperStabilizedPointFlow (t : ℂ) : (Fin 5 → ℂ) ≃ (Fin 5 → ℂ) :=
  (paperStabilizedPointCoordinates t).toEquiv

/-- Each coordinate is the evaluation of its displayed time-specialized polynomial. -/
theorem paperStabilizedPointFlow_apply (t : ℂ) (x : Fin 5 → ℂ) (i : Fin 5) :
    paperStabilizedPointFlow t x i = aeval x (paperStabilizedTranslation t (X i)) := rfl

/-- Evaluation along the flow is exactly the original algebra action. -/
theorem paperStabilizedPointFlow_aeval (t : ℂ) (x : Fin 5 → ℂ) (p : R 5) :
    aeval (paperStabilizedPointFlow t x) p = aeval x (paperStabilizedTranslation t p) :=
  AmbientMaps.aeval_pointMap (paperStabilizedTranslation t).toAlgHom x p

/-- Time zero fixes every complex point. -/
theorem paperStabilizedPointFlow_zero (x : Fin 5 → ℂ) : paperStabilizedPointFlow 0 x = x := by
  funext i
  rw [paperStabilizedPointFlow_apply, paperStabilizedTranslation_zero, aeval_X]

/-- The point maps satisfy the exact additive flow law. -/
theorem paperStabilizedPointFlow_add (s t : ℂ) (x : Fin 5 → ℂ) :
    paperStabilizedPointFlow s (paperStabilizedPointFlow t x) =
      paperStabilizedPointFlow (s + t) x := by
  funext i
  rw [paperStabilizedPointFlow_apply, paperStabilizedPointFlow_aeval,
    paperStabilizedTranslation_add, add_comm t s, paperStabilizedPointFlow_apply]

/-- The stabilized polynomial is an exact unit-speed level coordinate. -/
theorem paperStabilizedPointFlow_level (t : ℂ) (x : Fin 5 → ℂ) :
    aeval (paperStabilizedPointFlow t x) (stabilize f) = aeval x (stabilize f) + t := by
  rw [paperStabilizedPointFlow_aeval, paperStabilizedTranslation_f, map_add, aeval_C]
  rfl

/-- The action has no point stabilizers: distinct times move every point distinctly. -/
theorem paperStabilizedPointFlow_free (x : Fin 5 → ℂ) :
    Function.Injective (fun t => paperStabilizedPointFlow t x) := by
  intro s t h
  have hh := congrArg (fun y => aeval y (stabilize f)) h
  rw [paperStabilizedPointFlow_level, paperStabilizedPointFlow_level] at hh
  exact add_left_cancel hh

/-- Every orbit meets every complex level once, with explicit time `c-f(x)`. -/
theorem paperStabilizedPointFlow_unique_level (x : Fin 5 → ℂ) (c : ℂ) :
    ∃! t : ℂ, aeval (paperStabilizedPointFlow t x) (stabilize f) = c := by
  refine ⟨c - aeval x (stabilize f), ?_, ?_⟩
  · dsimp only
    rw [paperStabilizedPointFlow_level]
    ring
  · intro t ht
    rw [paperStabilizedPointFlow_level] at ht
    calc
      t = (aeval x (stabilize f) + t) - aeval x (stabilize f) := by ring
      _ = c - aeval x (stabilize f) := by rw [ht]

/-- The full time dependence is polynomial, witnessed by the original coaction. -/
theorem paperStabilizedPointFlow_jointPolynomial (t : ℂ) (x : Fin 5 → ℂ) (i : Fin 5) :
    paperStabilizedPointFlow t x i =
      (paperStabilizedAction.toAlgHom (X i)).eval₂ (aeval x).toRingHom t := by
  rw [paperStabilizedPointFlow_apply]
  change aeval x (paperStabilizedAction.specialize t (X i)) = _
  rw [PolynomialAdditiveAction.specialize_apply]
  have he := Polynomial.eval₂_at_apply (p := paperStabilizedAction.toAlgHom (X i))
    (aeval x).toRingHom (algebraMap ℂ (R 5) t)
  have hc : (aeval x).toRingHom (algebraMap ℂ (R 5) t) = t := (aeval x).commutes t
  rw [hc] at he
  exact he.symm

end

end GaloisForLFunctions.HTGeometry
