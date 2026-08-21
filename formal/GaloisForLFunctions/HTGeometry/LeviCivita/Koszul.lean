import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# The Koszul form of a Riemannian manifold

For vector fields `X`, `Y`, `Z` on a Riemannian manifold `M` the *Koszul form* is

```text
K(X, Y, Z) = X⟪Y, Z⟫ + Y⟪Z, X⟫ - Z⟪X, Y⟫ + ⟪[X, Y], Z⟫ - ⟪[X, Z], Y⟫ - ⟪[Y, Z], X⟫.
```

It is the right-hand side of the *Koszul formula* `2⟪∇_X Y, Z⟫ = K(X, Y, Z)`, which is forced by
metric compatibility and vanishing torsion.  This file establishes the purely algebraic properties
of `K` needed for both halves of the fundamental theorem of Riemannian geometry:

* `koszulForm_sub_swap` — `K(X, Y, Z) - K(Y, X, Z) = 2⟪[X, Y], Z⟫` (the torsion identity);
* `koszulForm_add_swap` — `K(X, Y, Z) + K(X, Z, Y) = 2 X⟪Y, Z⟫` (the metric identity);
* `koszulForm_add_middle`, `koszulForm_smul_middle` — additivity and the Leibniz rule in the
  middle slot, which make `Y ↦ K(X, Y, Z)` a derivation;
* `tensorialAt_koszulForm_left`, `tensorialAt_koszulForm_right` — `K` is tensorial (i.e.
  `C^∞`-linear) in its outer slots, so it descends to a bilinear form on each tangent space.

The two outer tensorialities are what let the Koszul form be converted into an actual connection in
`GaloisForLFunctions.HTGeometry.LeviCivita.Connection`.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.LeviCivita

open Bundle NormedSpace Set VectorField FiberBundle
open scoped Manifold ContDiff Bundle

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

variable {X X' Y Y' Z Z' : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}

/-! ## The metric pairing of two vector fields -/

/-- The pointwise Riemannian pairing of two vector fields, as a real-valued function on `M`. -/
noncomputable def gPair (Y Z : Π x : M, TangentSpace I x) : M → ℝ :=
  fun y ↦ inner ℝ (Y y) (Z y)

@[simp] lemma gPair_apply (Y Z : Π x : M, TangentSpace I x) (y : M) :
    gPair Y Z y = inner ℝ (Y y) (Z y) := rfl

lemma gPair_def (Y Z : Π x : M, TangentSpace I x) :
    gPair Y Z = fun y ↦ (inner ℝ (Y y) (Z y) : ℝ) := rfl

lemma gPair_comm (Y Z : Π x : M, TangentSpace I x) : gPair Y Z = gPair Z Y := by
  funext y; exact real_inner_comm _ _

lemma gPair_add_left (Y Y' Z : Π x : M, TangentSpace I x) :
    gPair (Y + Y') Z = gPair Y Z + gPair Y' Z := by
  funext y; simp [gPair, inner_add_left]

lemma gPair_add_right (Y Z Z' : Π x : M, TangentSpace I x) :
    gPair Y (Z + Z') = gPair Y Z + gPair Y Z' := by
  funext y; simp [gPair, inner_add_right]

lemma gPair_smul_left (f : M → ℝ) (Y Z : Π x : M, TangentSpace I x) :
    gPair (f • Y) Z = f * gPair Y Z := by
  funext y; simp [gPair, real_inner_smul_left]

lemma gPair_smul_right (f : M → ℝ) (Y Z : Π x : M, TangentSpace I x) :
    gPair Y (f • Z) = f * gPair Y Z := by
  funext y; simp [gPair, real_inner_smul_right]

/-- The Riemannian pairing of two vector fields differentiable at `x` is differentiable at `x`. -/
lemma mdifferentiableAt_gPair (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDiffAt (gPair Y Z) x :=
  MDifferentiableAt.inner_bundle (E := fun (x : M) ↦ TangentSpace I x) (b := fun y : M ↦ y) hY hZ

/-! ## The Koszul form -/

/-- The **Koszul form** of a Riemannian manifold:
`K(X, Y, Z) = X⟪Y, Z⟫ + Y⟪Z, X⟫ - Z⟪X, Y⟫ + ⟪[X, Y], Z⟫ - ⟪[X, Z], Y⟫ - ⟪[Y, Z], X⟫`. -/
noncomputable def koszulForm (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  mvfderiv I (gPair Y Z) x (X x) + mvfderiv I (gPair Z X) x (Y x)
    - mvfderiv I (gPair X Y) x (Z x)
    + inner ℝ (mlieBracket I X Y x) (Z x)
    - inner ℝ (mlieBracket I X Z x) (Y x)
    - inner ℝ (mlieBracket I Y Z x) (X x)

/-! ### The two structural identities

Neither of these needs any differentiability: they follow from symmetry of the metric and
antisymmetry of the Lie bracket alone. -/

/-- **Torsion identity.**  `K(X, Y, Z) - K(Y, X, Z) = 2⟪[X, Y], Z⟫`. -/
lemma koszulForm_sub_swap (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszulForm X Y Z x - koszulForm Y X Z x = 2 * inner ℝ (mlieBracket I X Y x) (Z x) := by
  have h1 : gPair Z X = gPair X Z := gPair_comm _ _
  have h2 : gPair Y X = gPair X Y := gPair_comm _ _
  have h3 : gPair Y Z = gPair Z Y := gPair_comm _ _
  have hb : mlieBracket I Y X x = - mlieBracket I X Y x := mlieBracket_swap_apply ..
  simp only [koszulForm, h1, h2, h3, hb, inner_neg_left]
  ring

/-- **Metric identity.**  `K(X, Y, Z) + K(X, Z, Y) = 2 X⟪Y, Z⟫`. -/
lemma koszulForm_add_swap (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszulForm X Y Z x + koszulForm X Z Y x = 2 * mvfderiv I (gPair Y Z) x (X x) := by
  have h1 : gPair Z Y = gPair Y Z := gPair_comm _ _
  have h2 : gPair Y X = gPair X Y := gPair_comm _ _
  have h3 : gPair X Z = gPair Z X := gPair_comm _ _
  have hb : mlieBracket I Z Y x = - mlieBracket I Y Z x := mlieBracket_swap_apply ..
  simp only [koszulForm, h1, h2, h3, hb, inner_neg_left]
  ring

/-! ### Derivation property in the middle slot -/

/-- The Koszul form is additive in its middle slot. -/
lemma koszulForm_add_middle (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    koszulForm X (Y + Y') Z x = koszulForm X Y Z x + koszulForm X Y' Z x := by
  simp only [koszulForm, gPair_add_left, gPair_add_right,
    mvfderiv_add (mdifferentiableAt_gPair hY hZ) (mdifferentiableAt_gPair hY' hZ),
    mvfderiv_add (mdifferentiableAt_gPair hX hY) (mdifferentiableAt_gPair hX hY'),
    mlieBracket_add_right hY hY', mlieBracket_add_left hY hY',
    add_apply, Pi.add_apply, inner_add_left, inner_add_right, map_add]
  ring

/-- The Koszul form obeys the Leibniz rule in its middle slot. -/
lemma koszulForm_smul_middle (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    koszulForm X (f • Y) Z x
      = f x * koszulForm X Y Z x + 2 * mvfderiv I f x (X x) * inner ℝ (Y x) (Z x) := by
  have c1 : (inner ℝ (Y x) (X x) : ℝ) = inner ℝ (X x) (Y x) := real_inner_comm _ _
  simp only [koszulForm, gPair_smul_left, gPair_smul_right,
    mvfderiv_mul hf (mdifferentiableAt_gPair hY hZ),
    mvfderiv_mul hf (mdifferentiableAt_gPair hX hY),
    mlieBracket_smul_right hf hY, mlieBracket_smul_left hf hY,
    add_apply, smul_apply, Pi.smul_apply', map_smul,
    inner_add_left, real_inner_smul_left, real_inner_smul_right, smul_eq_mul, gPair_apply]
  linear_combination (mvfderiv I f x (Z x)) * c1

/-! ### Tensoriality in the outer slots -/

/-- The Koszul form is tensorial in its first slot. -/
lemma tensorialAt_koszulForm_left (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun X ↦ koszulForm X Y Z x) x where
  smul {f} {X} hf hX := by
    have c1 : (inner ℝ (Z x) (X x) : ℝ) = inner ℝ (X x) (Z x) := real_inner_comm _ _
    simp only [koszulForm, gPair_smul_left, gPair_smul_right,
      mvfderiv_mul hf (mdifferentiableAt_gPair hZ hX),
      mvfderiv_mul hf (mdifferentiableAt_gPair hX hY),
      mlieBracket_smul_left hf hX,
      add_apply, smul_apply, Pi.smul_apply', map_smul,
      inner_add_left, real_inner_smul_left, real_inner_smul_right, smul_eq_mul,
      gPair_apply]
    linear_combination (mvfderiv I f x (Y x)) * c1
  add {X} {X'} hX hX' := by
    simp only [koszulForm, gPair_add_left, gPair_add_right,
      mvfderiv_add (mdifferentiableAt_gPair hZ hX) (mdifferentiableAt_gPair hZ hX'),
      mvfderiv_add (mdifferentiableAt_gPair hX hY) (mdifferentiableAt_gPair hX' hY),
      mlieBracket_add_left hX hX',
      add_apply, Pi.add_apply, inner_add_left, inner_add_right, map_add]
    ring

/-- The Koszul form is tensorial in its last slot. -/
lemma tensorialAt_koszulForm_right (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun Z ↦ koszulForm X Y Z x) x where
  smul {f} {Z} hf hZ := by
    have c1 : (inner ℝ (Y x) (Z x) : ℝ) = inner ℝ (Z x) (Y x) := real_inner_comm _ _
    simp only [koszulForm, gPair_smul_left, gPair_smul_right,
      mvfderiv_mul hf (mdifferentiableAt_gPair hY hZ),
      mvfderiv_mul hf (mdifferentiableAt_gPair hZ hX),
      mlieBracket_smul_right hf hZ,
      add_apply, smul_apply, Pi.smul_apply', map_smul,
      inner_add_left, real_inner_smul_left, real_inner_smul_right, smul_eq_mul,
      gPair_apply]
    linear_combination (mvfderiv I f x (X x)) * c1
  add {Z} {Z'} hZ hZ' := by
    simp only [koszulForm, gPair_add_left, gPair_add_right,
      mvfderiv_add (mdifferentiableAt_gPair hY hZ) (mdifferentiableAt_gPair hY hZ'),
      mvfderiv_add (mdifferentiableAt_gPair hZ hX) (mdifferentiableAt_gPair hZ' hX),
      mlieBracket_add_right hZ hZ',
      add_apply, Pi.add_apply, inner_add_left, inner_add_right, map_add]
    ring

end GaloisForLFunctions.HTGeometry.LeviCivita
