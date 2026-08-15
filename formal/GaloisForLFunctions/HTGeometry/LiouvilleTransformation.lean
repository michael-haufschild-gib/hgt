import GaloisForLFunctions.HTGeometry.PerturbedOscillatorVolterra

/-!
# The Liouville transformation

An equation `y'' + (c² f + g) y = 0` with `f > 0` becomes the normal form `W'' + (c² + ψ) W = 0`
under the change of variable `ξ = ∫ √f` together with the amplitude factor `f^{1/4}`.  Two
conditions do all the work:

* `X'² = 1/f(X)` — the new variable moves at the speed the equation prescribes;
* `2 A' X' + A X'' = 0`, equivalently `A² X'` constant — the amplitude kills the first-order term.

Given those two, the transformed equation drops out of the product and chain rules alone, with

```text
ψ = g(X)/f(X) − A''/A .
```

Stating the two conditions as hypotheses rather than constructing `X` and `A` from `f` keeps the
lemma free of inverse functions and fractional powers: in every application `X` and `A` are
explicit, and checking the two identities is a computation with the formulas at hand.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **The Liouville transformation.**  The transformed amplitude solves the normal form. -/
theorem hasDerivAt_liouvilleTransform {c : ℝ} {f g y y' X X' X'' A A' A'' : ℝ → ℝ}
    (hy : ∀ x, HasDerivAt y (y' x) x)
    (hy' : ∀ x, HasDerivAt y' (-(c ^ 2 * f x + g x) * y x) x)
    (hX : ∀ ξ, HasDerivAt X (X' ξ) ξ) (hX' : ∀ ξ, HasDerivAt X' (X'' ξ) ξ)
    (hA : ∀ ξ, HasDerivAt A (A' ξ) ξ) (hA' : ∀ ξ, HasDerivAt A' (A'' ξ) ξ)
    (ξ : ℝ) (hAne : A ξ ≠ 0) (hfne : f (X ξ) ≠ 0)
    (hspeed : X' ξ ^ 2 = 1 / f (X ξ))
    (hamp : 2 * A' ξ * X' ξ + A ξ * X'' ξ = 0) :
    HasDerivAt (fun η => A' η * y (X η) + A η * (y' (X η) * X' η))
      (-(c ^ 2 + (g (X ξ) / f (X ξ) - A'' ξ / A ξ)) * (A ξ * y (X ξ))) ξ := by
  have hyX : HasDerivAt (fun η => y (X η)) (y' (X ξ) * X' ξ) ξ :=
    HasDerivAt.comp ξ (hy (X ξ)) (hX ξ)
  have hy'X : HasDerivAt (fun η => y' (X η)) (-(c ^ 2 * f (X ξ) + g (X ξ)) * y (X ξ) * X' ξ) ξ :=
    HasDerivAt.comp ξ (hy' (X ξ)) (hX ξ)
  have h1 : HasDerivAt (fun η => A' η * y (X η))
      (A'' ξ * y (X ξ) + A' ξ * (y' (X ξ) * X' ξ)) ξ := (hA' ξ).mul hyX
  have h2 : HasDerivAt (fun η => y' (X η) * X' η)
      (-(c ^ 2 * f (X ξ) + g (X ξ)) * y (X ξ) * X' ξ * X' ξ + y' (X ξ) * X'' ξ) ξ :=
    hy'X.mul (hX' ξ)
  have h3 : HasDerivAt (fun η => A η * (y' (X η) * X' η))
      (A' ξ * (y' (X ξ) * X' ξ)
        + A ξ * (-(c ^ 2 * f (X ξ) + g (X ξ)) * y (X ξ) * X' ξ * X' ξ + y' (X ξ) * X'' ξ)) ξ :=
    (hA ξ).mul h2
  have h := h1.add h3
  have hsq : X' ξ * X' ξ = 1 / f (X ξ) := by
    rw [← sq]
    exact hspeed
  have hval : A'' ξ * y (X ξ) + A' ξ * (y' (X ξ) * X' ξ)
      + (A' ξ * (y' (X ξ) * X' ξ)
        + A ξ * (-(c ^ 2 * f (X ξ) + g (X ξ)) * y (X ξ) * X' ξ * X' ξ + y' (X ξ) * X'' ξ))
      = -(c ^ 2 + (g (X ξ) / f (X ξ) - A'' ξ / A ξ)) * (A ξ * y (X ξ)) := by
    have hrw : A ξ * (-(c ^ 2 * f (X ξ) + g (X ξ)) * y (X ξ) * (X' ξ * X' ξ))
        = -(c ^ 2 + g (X ξ) / f (X ξ)) * (A ξ * y (X ξ)) := by
      rw [hsq]
      field_simp
    have hzero : (2 * A' ξ * X' ξ + A ξ * X'' ξ) * y' (X ξ) = 0 := by
      rw [hamp]
      ring
    have hAdiv : A'' ξ * y (X ξ) = (A'' ξ / A ξ) * (A ξ * y (X ξ)) := by
      field_simp
    calc A'' ξ * y (X ξ) + A' ξ * (y' (X ξ) * X' ξ)
          + (A' ξ * (y' (X ξ) * X' ξ)
            + A ξ * (-(c ^ 2 * f (X ξ) + g (X ξ)) * y (X ξ) * X' ξ * X' ξ + y' (X ξ) * X'' ξ))
        = A'' ξ * y (X ξ)
          + (2 * A' ξ * X' ξ + A ξ * X'' ξ) * y' (X ξ)
          + A ξ * (-(c ^ 2 * f (X ξ) + g (X ξ)) * y (X ξ) * (X' ξ * X' ξ)) := by ring
      _ = A'' ξ * y (X ξ) + -(c ^ 2 + g (X ξ) / f (X ξ)) * (A ξ * y (X ξ)) := by
          rw [hzero, hrw]
          ring
      _ = -(c ^ 2 + (g (X ξ) / f (X ξ) - A'' ξ / A ξ)) * (A ξ * y (X ξ)) := by
          rw [hAdiv]
          ring
  rwa [hval] at h

/-- The first derivative of the transformed amplitude. -/
theorem hasDerivAt_liouvilleAmplitude {y y' X X' A A' : ℝ → ℝ}
    (hy : ∀ x, HasDerivAt y (y' x) x)
    (hX : ∀ ξ, HasDerivAt X (X' ξ) ξ) (hA : ∀ ξ, HasDerivAt A (A' ξ) ξ) (ξ : ℝ) :
    HasDerivAt (fun η => A η * y (X η))
      (A' ξ * y (X ξ) + A ξ * (y' (X ξ) * X' ξ)) ξ := by
  have hyX : HasDerivAt (fun η => y (X η)) (y' (X ξ) * X' ξ) ξ :=
    HasDerivAt.comp ξ (hy (X ξ)) (hX ξ)
  exact (hA ξ).mul hyX

end GaloisForLFunctions.HTGeometry
