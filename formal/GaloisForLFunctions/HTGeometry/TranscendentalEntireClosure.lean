import GaloisForLFunctions.HTGeometry.CascadePolynomialSharpness

/-!
# Stability of transcendence under polynomial operations

Adding a polynomial, scaling by a nonzero constant, and precomposing with an invertible affine map all
preserve transcendence of an entire function: in each case a polynomial value would be carried back to
a polynomial by the inverse operation.

These are the operations under which the differential order is itself invariant, so the class the
unit-cost law applies to is closed under them.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- **Adding a polynomial preserves transcendence.** -/
theorem transcendentalEntire_add_polynomial {g : ℂ → ℂ} (hg : TranscendentalEntire g)
    (p : Polynomial ℂ) : TranscendentalEntire (fun z => g z + p.eval z) := by
  refine ⟨hg.1.add (Polynomial.differentiable p), ?_⟩
  rintro ⟨q, hq⟩
  refine hg.2 ⟨q - p, fun z => ?_⟩
  have hz := hq z
  rw [Polynomial.eval_sub]
  linear_combination hz

/-- **Scaling by a nonzero constant preserves transcendence.** -/
theorem transcendentalEntire_const_smul {g : ℂ → ℂ} (hg : TranscendentalEntire g)
    {c : ℂ} (hc : c ≠ 0) : TranscendentalEntire (fun z => c * g z) := by
  refine ⟨(differentiable_const c).mul hg.1, ?_⟩
  rintro ⟨q, hq⟩
  refine hg.2 ⟨Polynomial.C c⁻¹ * q, fun z => ?_⟩
  have hz := hq z
  rw [Polynomial.eval_mul, Polynomial.eval_C, ← hz]
  field_simp

/-- **Invertible affine precomposition preserves transcendence.** -/
theorem transcendentalEntire_affine_precomp {g : ℂ → ℂ} (hg : TranscendentalEntire g)
    {a b : ℂ} (ha : a ≠ 0) : TranscendentalEntire (fun z => g (a * z + b)) := by
  refine ⟨hg.1.comp (((differentiable_const a).mul differentiable_id).add
    (differentiable_const b)), ?_⟩
  rintro ⟨q, hq⟩
  refine hg.2 ⟨q.comp (Polynomial.C a⁻¹ * (Polynomial.X - Polynomial.C b)), fun w => ?_⟩
  have hz : g (a * (a⁻¹ * (w - b)) + b) = Polynomial.eval (a⁻¹ * (w - b)) q :=
    hq (a⁻¹ * (w - b))
  have hval : a * (a⁻¹ * (w - b)) + b = w := by
    field_simp
    ring
  rw [hval] at hz
  rw [hz, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]

end GaloisForLFunctions.HTGeometry
