import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Hyperbolic radial zero jet

The literal radial equation
`sinh² d · f'' + sinh d cosh d · f' = sinh² d · p · (f + g)`
forces its regular zero-radius second jet.  This isolates the exact local
calculus needed by the cyclic Peierls full-circle cap; it adds no boundary
condition or asymptotic hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

noncomputable section
set_option autoImplicit false

/-- A smooth complex solution of the literal hyperbolic radial equation has
the forced regular radius-zero second jet. -/
theorem second_deriv_zero_of_hyperbolic_radial_eq
    (f g : ℝ → ℂ) (p : ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hode : ∀ d : ℝ,
      (Real.sinh d : ℂ) * (Real.sinh d : ℂ) * deriv (deriv f) d +
        (Real.sinh d : ℂ) * (Real.cosh d : ℂ) * deriv f d =
          (Real.sinh d : ℂ) * (Real.sinh d : ℂ) * p * (f d + g d)) :
    deriv (deriv f) 0 = p * (f 0 + g 0) / 2 := by
  let s : ℝ → ℂ := fun x => (Real.sinh x : ℂ)
  let c : ℝ → ℂ := fun x => (Real.cosh x : ℂ)
  let A : ℝ → ℂ := s * s
  let B : ℝ → ℂ := s * c
  let f1 : ℝ → ℂ := deriv f
  let f2 : ℝ → ℂ := deriv f1
  let f3 : ℝ → ℂ := deriv f2
  let f4 : ℝ → ℂ := deriv f3
  let g1 : ℝ → ℂ := deriv g
  let g2 : ℝ → ℂ := deriv g1
  let Q : ℝ → ℂ := fun x => p * (f x + g x)
  let L : ℝ → ℂ := A * f2 + B * f1
  let R : ℝ → ℂ := A * Q
  have hs (x : ℝ) : HasDerivAt s (c x) x := by
    exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (Real.hasDerivAt_sinh x)
  have hc (x : ℝ) : HasDerivAt c (s x) x := by
    exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (Real.hasDerivAt_cosh x)
  have hA (x : ℝ) : HasDerivAt A (c x * s x + s x * c x) x := by
    simpa [A] using (hs x).mul (hs x)
  have hB (x : ℝ) : HasDerivAt B (c x * c x + s x * s x) x := by
    simpa [B] using (hs x).mul (hc x)
  have hA_deriv : deriv A = c * s + s * c := by
    funext x
    exact (hA x).deriv
  have hB_deriv : deriv B = c * c + s * s := by
    funext x
    exact (hB x).deriv
  have hA2 (x : ℝ) : HasDerivAt (deriv A)
      (s x * s x + c x * c x + c x * c x + s x * s x) x := by
    rw [hA_deriv]
    simpa only [Pi.add_apply, Pi.mul_apply, add_assoc] using
      ((hc x).mul (hs x)).add ((hs x).mul (hc x))
  have hB2 (x : ℝ) : HasDerivAt (deriv B)
      (s x * c x + c x * s x + c x * s x + s x * c x) x := by
    rw [hB_deriv]
    simpa only [Pi.add_apply, Pi.mul_apply, add_assoc] using
      ((hc x).mul (hc x)).add ((hs x).mul (hs x))
  have hA2' (x : ℝ) : HasDerivAt (c * s + s * c)
      (s x * s x + c x * c x + c x * c x + s x * s x) x := by
    rw [← hA_deriv]
    exact hA2 x
  have hB2' (x : ℝ) : HasDerivAt (c * c + s * s)
      (s x * c x + c x * s x + c x * s x + s x * c x) x := by
    rw [← hB_deriv]
    exact hB2 x
  have hf1 : ContDiff ℝ ∞ f1 := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 : ContDiff ℝ ∞ f2 := (contDiff_infty_iff_deriv.mp hf1).2
  have hf3 : ContDiff ℝ ∞ f3 := (contDiff_infty_iff_deriv.mp hf2).2
  have hg1 : ContDiff ℝ ∞ g1 := (contDiff_infty_iff_deriv.mp hg).2
  have hfD (x : ℝ) : HasDerivAt f (f1 x) x :=
    ((hf.differentiable (by simp)).differentiableAt).hasDerivAt
  have hf1D (x : ℝ) : HasDerivAt f1 (f2 x) x :=
    ((hf1.differentiable (by simp)).differentiableAt).hasDerivAt
  have hf2D (x : ℝ) : HasDerivAt f2 (f3 x) x :=
    ((hf2.differentiable (by simp)).differentiableAt).hasDerivAt
  have hf3D (x : ℝ) : HasDerivAt f3 (f4 x) x :=
    ((hf3.differentiable (by simp)).differentiableAt).hasDerivAt
  have hgD (x : ℝ) : HasDerivAt g (g1 x) x :=
    ((hg.differentiable (by simp)).differentiableAt).hasDerivAt
  have hg1D (x : ℝ) : HasDerivAt g1 (g2 x) x :=
    ((hg1.differentiable (by simp)).differentiableAt).hasDerivAt
  have hQ (x : ℝ) : HasDerivAt Q (p * (f1 x + g1 x)) x := by
    exact ((hfD x).add (hgD x)).const_mul p
  have hQ_deriv : deriv Q = fun x => p * (f1 x + g1 x) := by
    funext x
    exact (hQ x).deriv
  have hQ2 (x : ℝ) : HasDerivAt (deriv Q) (p * (f2 x + g2 x)) x := by
    rw [hQ_deriv]
    exact ((hf1D x).add (hg1D x)).const_mul p
  have hQ2' (x : ℝ) : HasDerivAt (fun y => p * (f1 y + g1 y))
      (p * (f2 x + g2 x)) x := by
    rw [← hQ_deriv]
    exact hQ2 x
  have hL (x : ℝ) : HasDerivAt L
      ((c x * s x + s x * c x) * f2 x + A x * f3 x +
        (c x * c x + s x * s x) * f1 x + B x * f2 x) x := by
    simpa [L, add_assoc] using ((hA x).mul (hf2D x)).add ((hB x).mul (hf1D x))
  have hL_deriv : deriv L =
      (c * s + s * c) * f2 + A * f3 + (c * c + s * s) * f1 + B * f2 := by
    funext x
    exact (hL x).deriv
  have hL2raw : HasDerivAt (deriv L)
      ((s 0 * s 0 + c 0 * c 0 + c 0 * c 0 + s 0 * s 0) * f2 0 +
        (c 0 * s 0 + s 0 * c 0) * f3 0 +
        (c 0 * s 0 + s 0 * c 0) * f3 0 + A 0 * f4 0 +
        (s 0 * c 0 + c 0 * s 0 + c 0 * s 0 + s 0 * c 0) * f1 0 +
        (c 0 * c 0 + s 0 * s 0) * f2 0 +
        (c 0 * c 0 + s 0 * s 0) * f2 0 + B 0 * f3 0) 0 := by
    rw [hL_deriv]
    simpa [add_assoc] using (((hA2' 0).mul (hf2D 0)).add ((hA 0).mul (hf3D 0))).add
      (((hB2' 0).mul (hf1D 0)).add ((hB 0).mul (hf2D 0)))
  have hL2 : HasDerivAt (deriv L) (4 * f2 0) 0 := by
    convert hL2raw using 1
    simp [A, B, s, c]
    ring
  have hR (x : ℝ) : HasDerivAt R
      ((c x * s x + s x * c x) * Q x + A x * (p * (f1 x + g1 x))) x := by
    simpa [R] using (hA x).mul (hQ x)
  have hR_deriv : deriv R =
      (c * s + s * c) * Q + A * (fun x => p * (f1 x + g1 x)) := by
    funext x
    exact (hR x).deriv
  have hR2raw : HasDerivAt (deriv R)
      ((s 0 * s 0 + c 0 * c 0 + c 0 * c 0 + s 0 * s 0) * Q 0 +
        (c 0 * s 0 + s 0 * c 0) * (p * (f1 0 + g1 0)) +
        (c 0 * s 0 + s 0 * c 0) * (p * (f1 0 + g1 0)) +
        A 0 * (p * (f2 0 + g2 0))) 0 := by
    rw [hR_deriv]
    simpa [add_assoc] using ((hA2' 0).mul (hQ 0)).add ((hA 0).mul (hQ2' 0))
  have hR2 : HasDerivAt (deriv R) (2 * p * (f 0 + g 0)) 0 := by
    convert hR2raw using 1
    simp [A, Q, s, c]
    ring
  have hfun : L = R := by
    funext x
    dsimp [L, R, A, B, Q, f1, f2, s, c]
    convert hode x using 1
    ring
  have hderiv : deriv L = deriv R := congrArg deriv hfun
  have hsecond : deriv (deriv L) 0 = deriv (deriv R) 0 :=
    congrArg (fun z : ℝ → ℂ => deriv z 0) hderiv
  rw [hL2.deriv, hR2.deriv] at hsecond
  change f2 0 = p * (f 0 + g 0) / 2
  linear_combination hsecond / 4

end

end GaloisForLFunctions.HTGeometry
