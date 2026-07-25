import Mathlib

/-!
# The two engines of the center-mixed Fourier computation

After the substitution `u = w + t`, `v = w - t` the center-mixed density becomes a double integral
of `(u + v) * Φ u * Φ v` against a product of exponentials.  Two general facts drive the evaluation:

* **factorisation**: the weight `u + v` splits the double integral into a sum of two products of
  single integrals;
* **the shift rule**: multiplying the kernel by a real exponential `exp (c x)` translates its
  transform by `-I c`, with no contour argument.

Both are stated here for an arbitrary integrable kernel.  The doubly exponential decay of the
Riemann theta kernel is what supplies the integrability hypotheses in the application.
-/

open MeasureTheory Complex

namespace HTGeometry

/-- The transform of a kernel at complex argument. -/
noncomputable def kernelTransform (F : ℝ → ℂ) (ζ : ℂ) : ℂ :=
  ∫ x : ℝ, F x * Complex.exp (Complex.I * ζ * x)

/-- **The shift rule.**  Multiplying a kernel by `exp (c x)` for real `c` translates its transform
by `-I c`.  No contour deformation is involved: the identity is pointwise on the integrand. -/
theorem kernelTransform_exp_mul (F : ℝ → ℂ) (c : ℝ) (ζ : ℂ) :
    ∫ x : ℝ, (Complex.exp (c * x) * F x) * Complex.exp (Complex.I * ζ * x)
      = kernelTransform F (ζ - Complex.I * c) := by
  unfold kernelTransform
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hexp : Complex.exp (Complex.I * (ζ - Complex.I * c) * x)
      = Complex.exp (c * x) * Complex.exp (Complex.I * ζ * x) := by
    rw [← Complex.exp_add]
    congr 1
    have hsplit : Complex.I * (ζ - Complex.I * (c : ℂ)) * (x : ℂ)
        = Complex.I * ζ * (x : ℂ) - Complex.I ^ 2 * (c : ℂ) * (x : ℂ) := by ring
    rw [hsplit, Complex.I_sq]
    ring
  simp only [hexp]
  ring

/-- **Factorisation of the `u + v` weight.**  The double integral of `(u+v) F u G v` over the plane
splits into two products of single integrals. -/
theorem integral_prod_add_weight (F G : ℝ → ℂ)
    (hF : Integrable F) (hG : Integrable G)
    (huF : Integrable fun u : ℝ => (u : ℂ) * F u)
    (hvG : Integrable fun v : ℝ => (v : ℂ) * G v) :
    ∫ p : ℝ × ℝ, ((p.1 : ℂ) + (p.2 : ℂ)) * (F p.1 * G p.2)
      = (∫ u : ℝ, (u : ℂ) * F u) * (∫ v : ℝ, G v)
        + (∫ u : ℝ, F u) * (∫ v : ℝ, (v : ℂ) * G v) := by
  have hsplit : ∀ p : ℝ × ℝ, ((p.1 : ℂ) + (p.2 : ℂ)) * (F p.1 * G p.2)
      = ((p.1 : ℂ) * F p.1) * G p.2 + F p.1 * ((p.2 : ℂ) * G p.2) := by
    intro p
    ring
  have h1 : Integrable fun p : ℝ × ℝ => ((p.1 : ℂ) * F p.1) * G p.2 :=
    (huF.mul_prod hG)
  have h2 : Integrable fun p : ℝ × ℝ => F p.1 * ((p.2 : ℂ) * G p.2) :=
    (hF.mul_prod hvG)
  calc ∫ p : ℝ × ℝ, ((p.1 : ℂ) + (p.2 : ℂ)) * (F p.1 * G p.2)
      = ∫ p : ℝ × ℝ, (((p.1 : ℂ) * F p.1) * G p.2 + F p.1 * ((p.2 : ℂ) * G p.2)) := by
        exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
    _ = (∫ p : ℝ × ℝ, ((p.1 : ℂ) * F p.1) * G p.2)
          + ∫ p : ℝ × ℝ, F p.1 * ((p.2 : ℂ) * G p.2) := integral_add h1 h2
    _ = (∫ u : ℝ, (u : ℂ) * F u) * (∫ v : ℝ, G v)
          + (∫ u : ℝ, F u) * (∫ v : ℝ, (v : ℂ) * G v) := by
        rw [Measure.volume_eq_prod ℝ ℝ,
          integral_prod_mul (fun u : ℝ => (u : ℂ) * F u) G,
          integral_prod_mul F (fun v : ℝ => (v : ℂ) * G v)]

end HTGeometry
