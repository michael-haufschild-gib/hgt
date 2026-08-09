import GaloisForLFunctions.HTGeometry.GammaPhaseCompletion

/-!
# A non-vacuous realization of the projective-boundary interface

`HasPolynomialFunctionalProjectiveBoundary` was previously known to hold only for the empty
coefficient class, which satisfies it vacuously.  The class of constant functions satisfies it with
a nonzero limit vector: a constant is its own translate, so the identity normalization already
converges locally uniformly to the constant polynomial it names.

This does not capture the Gamma-ratio content of the interface — that is the first-stage Poincaré
theorem — but it does show the interface is inhabited by a class carrying nonzero data, so every
theorem quantified over it is non-vacuous.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The constant functions, as a coefficient class. -/
def constantFunctionClass : Set (ℂ → ℂ) := {f | ∃ c : ℂ, f = fun _ => c}

theorem hasPolynomialFunctionalProjectiveBoundary_constantFunctionClass :
    HasPolynomialFunctionalProjectiveBoundary constantFunctionClass := by
  classical
  intro r a haK ha S hS
  choose c hc using fun j => haK j
  obtain ⟨j0, hj0⟩ := ha
  refine ⟨id, strictMono_id, fun _ _ => 1, fun j => Polynomial.C (c j), ?_, ?_⟩
  · refine ⟨j0, ?_⟩
    intro hzero
    apply hj0
    have hc0 : c j0 = 0 := by
      have := congrArg (fun p : Polynomial ℂ => p.coeff 0) hzero
      simpa using this
    rw [hc j0, hc0]
    rfl
  · intro j
    have hfun : (fun (k : ℕ) (z : ℂ) => (1 : ℂ) * a j (z + Complex.I * (S (id k) : ℂ)))
        = fun (_ : ℕ) (_ : ℂ) => c j := by
      funext k z
      rw [hc j]
      simp
    have hlim : (fun z : ℂ => (Polynomial.C (c j)).eval z) = fun _ : ℂ => c j := by
      funext z
      simp
    rw [hfun, hlim]
    intro u hu x
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    filter_upwards with n z _
    simpa using refl_mem_uniformity hu

end GaloisForLFunctions.HTGeometry
