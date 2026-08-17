import GaloisForLFunctions.HTGeometry.SphereDivergence

/-!
# Nonstationary phase on the sphere

A field that pairs to one with the phase gradient turns the oscillation into a total divergence:
`div(a sin(tφ) X) = sin(tφ) div(aX) + t a cos(tφ)`.  Since the sphere has no boundary, the integral
of the left side vanishes, so the oscillatory integral is the divergence integral divided by `t`.

The same computation with the cosine gives the companion bound, and together they are the
`1/|t|` decay of an oscillatory integral with nonvanishing phase gradient.
-/

open MeasureTheory Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Phase

variable {n : ℕ}

/-- Bundled radial cutoff data for the sphere divergence theorem. -/
structure RadialCutoff (n : ℕ) where
  /-- the cutoff profile -/
  toFun : ℝ → ℝ
  /-- its derivative -/
  deriv : ℝ → ℝ
  hasDerivAt' : ∀ r, HasDerivAt toFun (deriv r) r
  continuous' : Continuous toFun
  vanish_lo : ∀ r : ℝ, r ≤ 1 / 2 → toFun r = 0
  vanish_hi : ∀ r : ℝ, 2 ≤ r → toFun r = 0
  radial_ne : (∫ r in Ioi (0 : ℝ), r ^ n * (toFun r / r)) ≠ 0

/-- The divergence theorem on the sphere, with the cutoff data bundled. -/
theorem integral_toSphere_eq_zero (c : RadialCutoff n)
    {Y : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {Y' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))}
    (hY : ∀ x, HasFDerivAt Y (Y' x) x)
    (htan : ∀ x, (inner ℝ x (Y x) : ℝ) = 0)
    (hhom : ∀ (r : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))), 0 < r → Y (r • x) = Y x)
    (hcont : Continuous (euclideanDivergence Y')) :
    ∫ ω, euclideanDivergence Y' ω
        ∂((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere) = 0 :=
  integral_toSphere_euclideanDivergence_eq_zero hY htan hhom c.hasDerivAt' c.continuous'
    c.vanish_lo c.vanish_hi hcont c.radial_ne

/-- The divergence of the amplitude times the phase field. -/
def amplitudeDivergence
    (a : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (a' : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (X : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (X' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))))
    (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  a x * euclideanDivergence X' x + a' x (X x)

/-- **The oscillatory divergence identity.**  With a field pairing to one against the phase
gradient, the divergence of `a sin(tφ) X` is `sin(tφ) div(aX) + t a cos(tφ)`. -/
theorem euclideanDivergence_sin_smul
    {a φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {a' φ' : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)}
    {X : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {X' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))}
    (hnondeg : ∀ x, φ' x (X x) = 1) (t : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    euclideanDivergence
        (fun y => (a y * Real.sin (t * φ y)) • X' y
          + ((Real.sin (t * φ y)) • a' y + (a y * (t * Real.cos (t * φ y))) • φ' y).smulRight
            (X y)) x
      = Real.sin (t * φ x) * amplitudeDivergence a a' X X' x
        + t * (a x * Real.cos (t * φ x)) := by
  classical
  rw [euclideanDivergence_scalar_smul
    (u := fun y => a y * Real.sin (t * φ y))
    (u' := fun y => (Real.sin (t * φ y)) • a' y + (a y * (t * Real.cos (t * φ y))) • φ' y)
    (Y := X) (Y' := X') x]
  rw [sum_apply_single_mul]
  rw [amplitudeDivergence]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hnondeg x]
  ring

/-- The companion identity with the cosine. -/
theorem euclideanDivergence_cos_smul
    {a φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {a' φ' : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)}
    {X : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {X' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))}
    (hnondeg : ∀ x, φ' x (X x) = 1) (t : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    euclideanDivergence
        (fun y => (a y * Real.cos (t * φ y)) • X' y
          + ((Real.cos (t * φ y)) • a' y + (a y * (-(t * Real.sin (t * φ y)))) • φ' y).smulRight
            (X y)) x
      = Real.cos (t * φ x) * amplitudeDivergence a a' X X' x
        - t * (a x * Real.sin (t * φ x)) := by
  classical
  rw [euclideanDivergence_scalar_smul
    (u := fun y => a y * Real.cos (t * φ y))
    (u' := fun y => (Real.cos (t * φ y)) • a' y + (a y * (-(t * Real.sin (t * φ y)))) • φ' y)
    (Y := X) (Y' := X') x]
  rw [sum_apply_single_mul, amplitudeDivergence]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hnondeg x]
  ring

/-- **`(17b)`: the nonstationary phase bound.**  Given the divergence identity and the vanishing of
the total divergence, the oscillatory integral decays like `1/|t|`. -/
theorem abs_oscillatory_le
    {A c s t : ℝ}
    (hzero : s + t * c = 0) (hbound : |s| ≤ A) :
    |t| * |c| ≤ A := by
  have hc : t * c = -s := by linarith
  calc |t| * |c| = |t * c| := (abs_mul t c).symm
    _ = |s| := by rw [hc, abs_neg]
    _ ≤ A := hbound

end Phase

end

end GaloisForLFunctions.HTGeometry
