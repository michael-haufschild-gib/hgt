import GaloisForLFunctions.HTGeometry.PolynomialCircuitParametrisation
import GaloisForLFunctions.HTGeometry.SpectralOrbitTrigForm

/-!
# The times at which an orbit is circuit-reachable are finite

Combining the two halves: the states a depth-`s` circuit prepares from a fixed rational input are
the values of *fixed* polynomials in the gate entries, and a trigonometric orbit through a point
with enough algebraically independent coordinates meets any such polynomial image only finitely
often on a compact time set.

The parameter count is `s · r²` — one indeterminate per entry of each gate — and the hypothesis is
that it stays below the number `k` of independent coordinates.  Nothing is assumed about the gates
beyond being real matrices: unitarity, locality, and support patterns only shrink the parameter
set, which can only shrink the image.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- The fixed coordinates of a depth-`s` circuit applied to a rational input vector. -/
noncomputable def circuitCoords (s r : ℕ) (v : Fin r → ℚ) :
    Fin r → MvPolynomial (Fin (s * (r * r))) ℚ :=
  fun i => ((List.ofFn (genericMatrix s r)).prod.mulVec (fun j => MvPolynomial.C (v j))) i

/-- Evaluating those coordinates at the entries of a real gate sequence returns the prepared
state. -/
theorem aeval_circuitCoords (s r : ℕ) (v : Fin r → ℚ) (M : Fin s → Matrix (Fin r) (Fin r) ℝ)
    (i : Fin r) :
    MvPolynomial.aeval (paramOf s r M) (circuitCoords s r v i)
      = ((List.ofFn M).prod.mulVec (fun j => ((v j : ℚ) : ℝ))) i := by
  have hcm := circuit_mem_image s r M (fun j => MvPolynomial.C (v j)) i
  rw [circuitCoords, ← hcm]
  congr 1
  funext j
  simp

/-- **The times at which a trigonometric orbit is reachable by a depth-`s` circuit are finite.**
If `k` of the orbit's coordinates are algebraically independent over `ℚ` at one time and the gate
parameter count `s · r²` is below `k`, then on any compact time set the orbit is circuit-reachable
only finitely often. -/
theorem finite_circuit_exceptional_times {r k n s : ℕ} (hs : s * (r * r) < k)
    (σ : Fin k → Fin r) (v : Fin r → ℚ)
    (a b : Fin r → Fin n → ℝ) (lam : Fin n → ℝ) {t₀ : ℝ}
    (hP : AlgebraicIndependent ℚ (fun i : Fin k =>
      ∑ j, (a (σ i) j * Real.cos (lam j * t₀) + b (σ i) j * Real.sin (lam j * t₀))))
    {S : Set ℝ} (hS : IsCompact S) :
    {t ∈ S | ∃ M : Fin s → Matrix (Fin r) (Fin r) ℝ, ∀ i : Fin r,
      (∑ j, (a i j * Real.cos (lam j * t) + b i j * Real.sin (lam j * t)))
        = ((List.ofFn M).prod.mulVec (fun j => ((v j : ℚ) : ℝ))) i}.Finite := by
  refine Set.Finite.subset (finite_meets_image_subfamily (m := s * (r * r)) hs σ
    (circuitCoords s r v)
    (fun i t => ∑ j, (a i j * Real.cos (lam j * t) + b i j * Real.sin (lam j * t)))
    (fun i => analyticOnNhd_trigSum (a i) (b i) lam) hP hS) ?_
  rintro t ⟨htS, M, hM⟩
  refine ⟨htS, paramOf s r M, fun i => ?_⟩
  rw [hM i, aeval_circuitCoords]

end GaloisForLFunctions.HTGeometry
