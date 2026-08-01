import GaloisForLFunctions.HTGeometry.GammaFieldShapeConvergence
import Mathlib

/-!
# Clearing denominators and the numerator slot of a shape

Two pieces of bookkeeping for coefficients in `ℂ(s)`.

First, a finite family of rational functions has a common polynomial denominator, so multiplying a
jet polynomial by one nonzero polynomial makes all its coefficients polynomials.

Second, the shape `polyJetShape σ a dP b` carries its own numerator power `dP`: multiplying a
function by `s^K` and its shape by the same power leaves the residue unchanged.  Together these move
between "coefficients in `ℂ(s)`" and the bounded coefficients `p(s)/s^d` the residue estimates use,
with no negative exponent anywhere.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **A common polynomial denominator for a finite family of rational functions.** -/
theorem exists_common_denom_poly {M : ℕ} (k : Fin M → RatFunc ℂ) :
    ∃ (q : Polynomial ℂ) (p : Fin M → Polynomial ℂ), q ≠ 0 ∧
      ∀ α, algebraMap (Polynomial ℂ) (RatFunc ℂ) q * k α
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p α) := by
  classical
  refine ⟨∏ β : Fin M, (k β).denom,
    fun α => (k α).num * ∏ β ∈ Finset.univ.erase α, (k β).denom,
    Finset.prod_ne_zero_iff.mpr fun β _ => (k β).denom_ne_zero, fun α => ?_⟩
  have hden : algebraMap (Polynomial ℂ) (RatFunc ℂ) (k α).denom ≠ 0 := fun h =>
    (k α).denom_ne_zero (RatFunc.algebraMap_injective ℂ (by rw [h, map_zero]))
  have hnum : k α * algebraMap (Polynomial ℂ) (RatFunc ℂ) (k α).denom
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (k α).num := by
    nth_rewrite 1 [← RatFunc.num_div_denom (k α)]
    exact div_mul_cancel₀ _ hden
  have hsplit : (∏ β : Fin M, (k β).denom)
      = (k α).denom * ∏ β ∈ Finset.univ.erase α, (k β).denom :=
    (Finset.mul_prod_erase Finset.univ (fun β => (k β).denom) (Finset.mem_univ α)).symm
  rw [hsplit, map_mul, map_mul, mul_comm (algebraMap (Polynomial ℂ) (RatFunc ℂ) (k α).denom),
    mul_assoc, mul_comm (algebraMap (Polynomial ℂ) (RatFunc ℂ) (k α).denom) (k α), hnum]
  ring

/-- The numerator slot of a shape is a power of the coordinate. -/
theorem polyJetShape_num_pow (σ : ℝ) (a K b : ℕ) (t : ℝ) :
    polyJetShape σ a K b t = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ K * polyJetShape σ a 0 b t := by
  rw [polyJetShape, polyJetShape, pow_zero, mul_one]
  ring

/-- **The residue is unchanged by a common power in numerator and shape.** -/
theorem tendsto_div_polyJetShape_num_pow {f : ℝ → ℂ} {a K b : ℕ} {r : ℂ} (hσ : 0 < σ)
    (h : Tendsto (fun t : ℝ => f t / polyJetShape σ a 0 b t) atTop (nhds r)) :
    Tendsto (fun t : ℝ => (((σ : ℂ) + (t : ℂ) * Complex.I) ^ K * f t) / polyJetShape σ a K b t)
      atTop (nhds r) := by
  refine h.congr' ?_
  filter_upwards [eventually_vertical_ne_zero σ, eventually_polyJetShape_ne_zero hσ a 0 b]
    with t hs hshape
  have hpow : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ K ≠ 0 := pow_ne_zero _ hs
  rw [polyJetShape_num_pow σ a K b t]
  field_simp

end GaloisForLFunctions
