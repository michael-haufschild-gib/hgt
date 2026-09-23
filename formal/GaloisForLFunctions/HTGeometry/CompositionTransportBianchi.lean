import GaloisForLFunctions.HTGeometry.ProjectiveSourceVisibilityParity

/-!
# Composition transport and comparison holonomy obey one triangle law

This file gives the first exact algebraic bridge for the composition-curvature programme.

At each event, let `μ` be a bilinear rule of composition.  Along an event comparison `T`, the
composition-transport defect is

```
T (μ x y) - ν (T x) (T y).
```

For a triangle of comparisons, these edge defects do not vary independently of the failure of the
two-step comparison to equal the direct comparison.  Bilinearity forces an exact nonlinear
triangle identity.  Its flat specialization is a cocycle law.

The projective version has an additional central term `(a - a^(2 : ℕ)) • μ₂ (T₀₂ x) (T₀₂ y)`.  Hence a
nonzero neutral binary composition is incompatible with a nontrivial nonzero scalar path phase.
The positive replacement is central-weight balance: at every nonzero bilinear composition, the
output central weight equals the product of the two input weights.

These are elementary parent-algebra identities.  They prove no force law or physics.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R V : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- A curried bilinear composition law on an `R`-module. -/
abbrev BilinearComposition (R V : Type*)
    [CommRing R] [AddCommGroup V] [Module R V] :=
  V →ₗ[R] V →ₗ[R] V

/-- Failure of a comparison to transport one bilinear composition law to another. -/
def compositionTransportDefect
    (T : V →ₗ[R] V)
    (μ ν : BilinearComposition R V)
    (x y : V) : V :=
  T (μ x y) - ν (T x) (T y)

/-- Failure of a two-edge comparison path to equal the direct comparison. -/
def comparisonPathDefect
    (T₀₁ T₁₂ T₀₂ : V →ₗ[R] V) : V →ₗ[R] V :=
  T₁₂.comp T₀₁ - T₀₂

/--
Exact coupled triangle identity for composition transport and comparison-path defects.

The last term is quadratic in the path defect.  It is mandatory at finite transport and disappears
only in an infinitesimal linearization.
-/
theorem compositionTransportDefect_triangle_bianchi
    (μ₀ μ₁ μ₂ : BilinearComposition R V)
    (T₀₁ T₁₂ T₀₂ : V →ₗ[R] V)
    (x y : V) :
    T₁₂ (compositionTransportDefect T₀₁ μ₀ μ₁ x y) +
        compositionTransportDefect T₁₂ μ₁ μ₂ (T₀₁ x) (T₀₁ y) -
        compositionTransportDefect T₀₂ μ₀ μ₂ x y =
      comparisonPathDefect T₀₁ T₁₂ T₀₂ (μ₀ x y) -
        μ₂ (comparisonPathDefect T₀₁ T₁₂ T₀₂ x) (T₀₂ y) -
        μ₂ (T₀₂ x) (comparisonPathDefect T₀₁ T₁₂ T₀₂ y) -
        μ₂ (comparisonPathDefect T₀₁ T₁₂ T₀₂ x)
          (comparisonPathDefect T₀₁ T₁₂ T₀₂ y) := by
  simp only [compositionTransportDefect, comparisonPathDefect,
    LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  abel

/-- On a flat comparison triangle, composition-transport defects satisfy an exact cocycle law. -/
theorem compositionTransportDefect_flat_triangle
    (μ₀ μ₁ μ₂ : BilinearComposition R V)
    (T₀₁ T₁₂ T₀₂ : V →ₗ[R] V)
    (hflat : T₁₂.comp T₀₁ = T₀₂)
    (x y : V) :
    T₁₂ (compositionTransportDefect T₀₁ μ₀ μ₁ x y) +
        compositionTransportDefect T₁₂ μ₁ μ₂ (T₀₁ x) (T₀₁ y) =
      compositionTransportDefect T₀₂ μ₀ μ₂ x y := by
  have hK : comparisonPathDefect T₀₁ T₁₂ T₀₂ = 0 := sub_eq_zero.mpr hflat
  have h := compositionTransportDefect_triangle_bianchi
    μ₀ μ₁ μ₂ T₀₁ T₁₂ T₀₂ x y
  simp [hK] at h
  exact sub_eq_zero.mp h

/-- Failure of a two-edge comparison path to equal a scalar multiple of the direct comparison. -/
def projectiveComparisonPathDefect
    (a : R) (T₀₁ T₁₂ T₀₂ : V →ₗ[R] V) : V →ₗ[R] V :=
  T₁₂.comp T₀₁ - a • T₀₂

/--
Projective coupled triangle identity.

The central term `(a - a^(2 : ℕ)) • μ₂ (T₀₂ x) (T₀₂ y)` is the exact mismatch between a phase acting
once on the output and twice through the two inputs of a bilinear composition.
-/
theorem compositionTransportDefect_projective_triangle_bianchi
    (a : R)
    (μ₀ μ₁ μ₂ : BilinearComposition R V)
    (T₀₁ T₁₂ T₀₂ : V →ₗ[R] V)
    (x y : V) :
    T₁₂ (compositionTransportDefect T₀₁ μ₀ μ₁ x y) +
        compositionTransportDefect T₁₂ μ₁ μ₂ (T₀₁ x) (T₀₁ y) -
        a • compositionTransportDefect T₀₂ μ₀ μ₂ x y =
      projectiveComparisonPathDefect a T₀₁ T₁₂ T₀₂ (μ₀ x y) +
        (a - a ^ (2 : ℕ)) • μ₂ (T₀₂ x) (T₀₂ y) -
        a • μ₂ (projectiveComparisonPathDefect a T₀₁ T₁₂ T₀₂ x) (T₀₂ y) -
        a • μ₂ (T₀₂ x) (projectiveComparisonPathDefect a T₀₁ T₁₂ T₀₂ y) -
        μ₂ (projectiveComparisonPathDefect a T₀₁ T₁₂ T₀₂ x)
          (projectiveComparisonPathDefect a T₀₁ T₁₂ T₀₂ y) := by
  simp only [compositionTransportDefect, projectiveComparisonPathDefect,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    map_sub, LinearMap.map_smul]
  module

/--
Nonzero neutral binary composition excludes a nontrivial scalar phase on a projectively flat
comparison triangle.

The conclusion `a = 0 ∨ a = 1` becomes `a = 1` whenever the path scalar is known to be nonzero,
as it is for a phase.
-/
theorem projectiveComposition_phase_idempotent
    {K W : Type*}
    [Field K] [AddCommGroup W] [Module K W]
    (a : K)
    (μ₀ μ₁ μ₂ : BilinearComposition K W)
    (T₀₁ T₁₂ T₀₂ : W →ₗ[K] W)
    (x y : W)
    (hproj : T₁₂.comp T₀₁ = a • T₀₂)
    (h₀₁ : compositionTransportDefect T₀₁ μ₀ μ₁ x y = 0)
    (h₁₂ : compositionTransportDefect T₁₂ μ₁ μ₂ (T₀₁ x) (T₀₁ y) = 0)
    (h₀₂ : compositionTransportDefect T₀₂ μ₀ μ₂ x y = 0)
    (hnonzero : μ₂ (T₀₂ x) (T₀₂ y) ≠ 0) :
    a = 0 ∨ a = 1 := by
  have hK : projectiveComparisonPathDefect a T₀₁ T₁₂ T₀₂ = 0 :=
    sub_eq_zero.mpr hproj
  have h := compositionTransportDefect_projective_triangle_bianchi
    a μ₀ μ₁ μ₂ T₀₁ T₁₂ T₀₂ x y
  rw [h₀₁, h₁₂, h₀₂, hK] at h
  simp at h
  have hscalar : a - a ^ (2 : ℕ) = 0 := by
    exact (smul_eq_zero.mp h.symm).resolve_right hnonzero
  rw [show a - a ^ (2 : ℕ) = a * (1 - a) by ring] at hscalar
  rcases mul_eq_zero.mp hscalar with ha | ha
  · exact Or.inl ha
  · exact Or.inr (sub_eq_zero.mp ha).symm

/--
Central weights balance at every nonzero bilinear composition.

If the two inputs have central weights `a` and `b`, covariance forces the output weight to be
`a * b`.  This is the multiplicative form of additive charge conservation.
-/
theorem nonzeroComposition_centralWeight_balance
    {K W : Type*}
    [Field K] [AddCommGroup W] [Module K W]
    (μ : BilinearComposition K W)
    (a b c : K) (x y : W)
    (hnonzero : μ x y ≠ 0)
    (hcovariant : c • μ x y = μ (a • x) (b • y)) :
    c = a * b := by
  have hweighted : c • μ x y = (a * b) • μ x y := by
    simpa [smul_smul, mul_comm] using hcovariant
  have hzero : (c - a * b) • μ x y = 0 := by
    rw [sub_smul, hweighted, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hnonzero)

end GaloisForLFunctions.HTGeometry
