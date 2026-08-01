import GaloisForLFunctions.HTGeometry.JetDatumFromNonFlat
import GaloisForLFunctions.HTGeometry.PolygammaDepthExpansion

/-!
# Every non-flat jet polynomial has a datum

A polynomial in the positive-order digamma jets, with constant coefficients, is approximated to every
depth by a standard rational function of the minimal monomial weight.  If it is not flat — if it
fails to decay faster than some fixed power on the line — then the dichotomy of the approximation
gives it a datum:

`s^p · P(ψ′,ψ″,…)(s) → c ≠ 0`.

This is the residue of eq. (19) for the constant-coefficient case, with no presentation supplied:
only the polynomial and its non-flatness go in.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **The datum of a non-flat jet polynomial.** -/
theorem exists_jetPoly_datum (hσ : 0 < σ) (N M W : ℕ) (e : Fin M → Fin N → ℕ) (a : Fin M → ℂ)
    (hW : ∀ α : Fin M, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i) {n : ℕ}
    (hnotflat : ¬ IsLineBigO σ n (fun t : ℝ => ∑ α : Fin M, a α * ∏ i : Fin N,
      iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧
      Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
        * ∑ α : Fin M, a α * ∏ i : Fin N,
          iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
        atTop (nhds c) := by
  refine exists_datum_of_not_flat hσ W (fun K => ?_) hnotflat
  obtain ⟨F, A, hFstd, hA, hFbound⟩ := exists_jetPoly_package N M K W e a hW
  obtain ⟨P, l, hdeg, hval⟩ := hFstd
  refine ⟨P, l, A, hdeg, le_trans zero_le_one hA, fun t ht => ?_⟩
  have hsre : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  have hFval := hval ((σ : ℂ) + (t : ℂ) * Complex.I) hsre
  rw [← hFval]
  exact hFbound σ t hσ ht

end GaloisForLFunctions
