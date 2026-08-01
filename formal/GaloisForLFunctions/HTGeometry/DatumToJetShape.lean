import GaloisForLFunctions.HTGeometry.DigammaLogPowers
import GaloisForLFunctions.HTGeometry.PolyCoeffJetResidue

/-!
# From a datum to the residue interface of the law

The finite-phase law consumes its coefficients as residues against a jet shape: it asks for
`F(s)/polyJetShape σ a dP b → c` with `c ≠ 0`.  A datum in the form produced by the expansion
machinery — `s^p·F(s)/(log t + iπ/2)^a → c` — is the same statement for the shape `L^a/s^p`, since
the shape is a quotient of exactly those two factors.

This closes the loop: the unquantified datum of a jet polynomial is an admissible coefficient datum
for the law.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **A datum is a residue against the corresponding jet shape.** -/
theorem tendsto_div_polyJetShape_of_datum (_hσ : 0 < σ) {f : ℝ → ℂ} {a p : ℕ} {c : ℂ}
    (h : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * f t / vertLog t ^ a)
      atTop (nhds c)) :
    Tendsto (fun t : ℝ => f t / polyJetShape σ a 0 p t) atTop (nhds c) := by
  refine h.congr' ?_
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hL hs
  have hLa : vertLog t ^ a ≠ 0 := pow_ne_zero _ hL
  have hsp : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p ≠ 0 := pow_ne_zero _ hs
  rw [polyJetShape, pow_zero, mul_one]
  field_simp

/-- The logarithm-free case: a plain datum is a residue against a pure power shape. -/
theorem tendsto_div_polyJetShape_of_datum_zero (hσ : 0 < σ) {f : ℝ → ℂ} {p : ℕ} {c : ℂ}
    (h : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * f t) atTop (nhds c)) :
    Tendsto (fun t : ℝ => f t / polyJetShape σ 0 0 p t) atTop (nhds c) := by
  refine tendsto_div_polyJetShape_of_datum hσ (a := 0) ?_
  simpa using h

end GaloisForLFunctions
