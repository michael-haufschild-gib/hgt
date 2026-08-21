import GaloisForLFunctions.HTGeometry.GaussBonnetOrthogonalPatch

/-!
# Global Gauss--Bonnet on the torus

A doubly periodic orthogonal Riemannian metric on the plane is exactly a (coordinate-orthogonal)
Riemannian metric on the two-torus `T² = ℝ²/(pℤ × qℤ)`.  For such a metric the boundary of a period
rectangle cancels against itself, so the Liouville boundary term of the local Gauss--Bonnet
identity vanishes and

```text
∫∫_{T²} K dA = 0 = 2π · χ(T²).
```

This is a genuinely global Gauss--Bonnet theorem: no rotational symmetry, no flatness, no
curvature sign condition — an arbitrary smooth doubly periodic orthogonal metric.  The proof is the
Green identity of `GaussBonnetOrthogonalPatch` together with the periodicity of the partial
derivatives.
-/

open MeasureTheory intervalIntegral
open scoped Real ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

/-- A partial derivative inherits the periodicity of its field. -/
theorem px_periodic {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {p : ℝ}
    (h : ∀ u v, F (u + p, v) = F (u, v)) (u v : ℝ) : px F (u + p, v) = px F (u, v) := by
  have hshift : HasDerivAt (fun t : ℝ => F (t + p, v)) (px F (u + p, v)) u := by
    have h1 : HasDerivAt (fun t : ℝ => t + p) 1 u := (hasDerivAt_id u).add_const p
    have h2 := (hasDerivAt_px hF (u + p) v).comp u h1
    simpa [Function.comp_def] using h2
  have heq : (fun t : ℝ => F (t + p, v)) = fun t : ℝ => F (t, v) := funext fun t => h t v
  rw [heq] at hshift
  exact hshift.unique (hasDerivAt_px hF u v)

/-- A partial derivative inherits the periodicity of its field. -/
theorem py_periodic {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {q : ℝ}
    (h : ∀ u v, F (u, v + q) = F (u, v)) (u v : ℝ) : py F (u, v + q) = py F (u, v) := by
  have hshift : HasDerivAt (fun t : ℝ => F (u, t + q)) (py F (u, v + q)) v := by
    have h1 : HasDerivAt (fun t : ℝ => t + q) 1 v := (hasDerivAt_id v).add_const q
    have h2 := (hasDerivAt_py hF u (v + q)).comp v h1
    simpa [Function.comp_def] using h2
  have heq : (fun t : ℝ => F (u, t + q)) = fun t : ℝ => F (u, t) := funext fun t => h u t
  rw [heq] at hshift
  exact hshift.unique (hasDerivAt_py hF u v)

/-- A partial derivative in one direction inherits periodicity in the *other* direction. -/
theorem px_periodic_snd {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {q : ℝ}
    (h : ∀ u v, F (u, v + q) = F (u, v)) (u v : ℝ) : px F (u, v + q) = px F (u, v) := by
  have h1 : HasDerivAt (fun t : ℝ => F (t, v + q)) (px F (u, v + q)) u := hasDerivAt_px hF u (v + q)
  have heq : (fun t : ℝ => F (t, v + q)) = fun t : ℝ => F (t, v) := funext fun t => h t v
  rw [heq] at h1
  exact h1.unique (hasDerivAt_px hF u v)

/-- A partial derivative in one direction inherits periodicity in the *other* direction. -/
theorem py_periodic_fst {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {p : ℝ}
    (h : ∀ u v, F (u + p, v) = F (u, v)) (u v : ℝ) : py F (u + p, v) = py F (u, v) := by
  have h1 : HasDerivAt (fun t : ℝ => F (u + p, t)) (py F (u + p, v)) v := hasDerivAt_py hF (u + p) v
  have heq : (fun t : ℝ => F (u + p, t)) = fun t : ℝ => F (u, t) := funext fun t => h u t
  rw [heq] at h1
  exact h1.unique (hasDerivAt_py hF u v)

namespace OrthogonalPatch

variable (M : OrthogonalPatch) {p q : ℝ}

variable (hEu : ∀ u v, M.E (u + p, v) = M.E (u, v))
variable (hEv : ∀ u v, M.E (u, v + q) = M.E (u, v))
variable (hGu : ∀ u v, M.G (u + p, v) = M.G (u, v))
variable (hGv : ∀ u v, M.G (u, v + q) = M.G (u, v))

include hEu hGu in
theorem P_periodic_fst (u v : ℝ) : M.P (u + p, v) = M.P (u, v) := by
  unfold P area uSpeed vSpeed
  rw [px_periodic M.smoothG hGu u v, hEu u v, hGu u v]

include hEv hGv in
theorem Q_periodic_snd (u v : ℝ) : M.Q (u, v + q) = M.Q (u, v) := by
  unfold Q area uSpeed vSpeed
  rw [py_periodic M.smoothE hEv u v, hEv u v, hGv u v]

include hEu hEv hGu hGv in
/-- **Gauss--Bonnet on the torus.**  Every smooth doubly periodic orthogonal Riemannian metric —
that is, every coordinate-orthogonal Riemannian metric on the two-torus — has total curvature
`0 = 2π·χ(T²)` over a period rectangle. -/
theorem gauss_bonnet_torus (a c : ℝ) :
    M.totalCurvature a (a + p) c (c + q) = 2 * π * 0 := by
  rw [M.totalCurvature_eq a (a + p) c (c + q)]
  have h1 : (∫ v in c..(c + q), M.P (a + p, v) - M.P (a, v)) = 0 := by
    have : (∫ v in c..(c + q), M.P (a + p, v) - M.P (a, v)) = ∫ _v in c..(c + q), (0 : ℝ) :=
      intervalIntegral.integral_congr fun v _ => by
        rw [M.P_periodic_fst hEu hGu a v]; ring
    simpa using this
  have h2 : (∫ u in a..(a + p), M.Q (u, c + q) - M.Q (u, c)) = 0 := by
    have : (∫ u in a..(a + p), M.Q (u, c + q) - M.Q (u, c)) = ∫ _u in a..(a + p), (0 : ℝ) :=
      intervalIntegral.integral_congr fun u _ => by
        rw [M.Q_periodic_snd hEv hGv u c]; ring
    simpa using this
  rw [h1, h2]
  ring

include hEu hEv hGu hGv in
/-- The same statement in Gauss--Bonnet shape: total curvature plus total boundary turning equals
`2π·χ(T²) = 0`, the boundary turning of a closed surface being zero. -/
theorem gauss_bonnet_torus_closed (a c : ℝ) :
    M.totalCurvature a (a + p) c (c + q) + 0 = 2 * π * 0 := by
  rw [add_zero]
  exact M.gauss_bonnet_torus hEu hEv hGu hGv a c

end OrthogonalPatch

end GaloisForLFunctions.HTGeometry.GaussBonnet
