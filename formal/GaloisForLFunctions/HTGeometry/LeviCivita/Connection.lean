import GaloisForLFunctions.HTGeometry.FiltrationNumberForm
import GaloisForLFunctions.HTGeometry.LeviCivita.Koszul

/-!
# The Levi-Civita connection

This file constructs, on an arbitrary Riemannian manifold, the covariant derivative determined by
the Koszul formula

```text
2⟪∇_X Y, Z⟫ = K(X, Y, Z),
```

and shows that it is a genuine covariant derivative on the tangent bundle.  The Koszul form `K` is
tensorial in `X` and `Z` (`GaloisForLFunctions.HTGeometry.LeviCivita.Koszul`), so for a section `σ`
differentiable at `x` it descends to a bilinear form on `TangentSpace I x`; the Riesz
representation of one half of that form is `∇σ x`.

## Main definitions and results

* `covLC` — the Levi-Civita covariant derivative as a bare map on sections;
* `inner_covLC` — the Koszul formula, i.e. the defining property of `covLC`;
* `isCovariantDerivativeOn_covLC` — `covLC` satisfies the axioms of a covariant derivative.
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

/-- The fibres of the tangent bundle of a manifold modelled on a finite-dimensional space are
finite dimensional. -/
lemma finiteDimensional_tangentSpace (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  VectorBundle.finiteDimensional ℝ E (fun x : M ↦ TangentSpace I x) x

attribute [local instance] finiteDimensional_tangentSpace

variable {X X' Y Y' Z Z' σ σ' τ : Π x : M, TangentSpace I x} {f g : M → ℝ} {x : M}

/-! ## Construction -/

open Classical in
/-- The **Levi-Civita covariant derivative**, as a bare map from sections of the tangent bundle to
sections of `Hom(TM, TM)`.  At a point where the section is differentiable it is the Riesz
representative of half the Koszul form; elsewhere it is junk (`0`), exactly as the axioms of a
covariant derivative allow. -/
noncomputable def covLC (σ : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  if hσ : MDiffAt (T% σ) x then
    formRiesz ((2 : ℝ)⁻¹ • TensorialAt.mkHom₂ (fun X Z ↦ koszulForm X σ Z x) x
      (fun _ hZ ↦ tensorialAt_koszulForm_left hσ hZ)
      (fun _ hX ↦ tensorialAt_koszulForm_right hX hσ))
  else 0

/-- **The Koszul formula.**  This is the defining property of `covLC`. -/
lemma inner_covLC (hσ : MDiffAt (T% σ) x) (hX : MDiffAt (T% X) x) (hZ : MDiffAt (T% Z) x) :
    (inner ℝ (covLC σ x (X x)) (Z x) : ℝ) = (2 : ℝ)⁻¹ * koszulForm X σ Z x := by
  rw [covLC, dif_pos hσ, inner_formRiesz]
  rw [smul_apply, smul_apply, smul_eq_mul,
    TensorialAt.mkHom₂_apply _ _ hX hZ]

/-- The Koszul formula, applied to arbitrary tangent vectors via the canonical extensions. -/
lemma inner_covLC_extend (hσ : MDiffAt (T% σ) x) (u v : TangentSpace I x) :
    (inner ℝ (covLC σ x u) v : ℝ)
      = (2 : ℝ)⁻¹ * koszulForm (extend E u) σ (extend E v) x := by
  have h := inner_covLC hσ (mdifferentiableAt_extend I E u) (mdifferentiableAt_extend I E v)
  simpa using h

/-- Two continuous endomorphisms of a tangent space agree as soon as all their inner products
against a second vector agree. -/
lemma clm_ext_of_inner {A B : TangentSpace I x →L[ℝ] TangentSpace I x}
    (h : ∀ u v : TangentSpace I x, (inner ℝ (A u) v : ℝ) = inner ℝ (B u) v) : A = B := by
  ext u
  exact ext_inner_right ℝ (h u)

/-! ## `covLC` is a covariant derivative -/

lemma covLC_add (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) :
    covLC (σ + σ') x = covLC σ x + covLC σ' x := by
  refine clm_ext_of_inner fun u v ↦ ?_
  rw [inner_covLC_extend (mdifferentiableAt_add_section hσ hσ') u v,
    koszulForm_add_middle (mdifferentiableAt_extend I E u) hσ hσ'
      (mdifferentiableAt_extend I E v),
    add_apply, inner_add_left, inner_covLC_extend hσ u v,
    inner_covLC_extend hσ' u v]
  ring

lemma covLC_smul (hσ : MDiffAt (T% σ) x) (hf : MDiffAt f x) :
    covLC (f • σ) x = f x • covLC σ x + (mvfderiv I f x).smulRight (σ x) := by
  refine clm_ext_of_inner fun u v ↦ ?_
  rw [inner_covLC_extend (hf.smul_section hσ) u v,
    koszulForm_smul_middle hf (mdifferentiableAt_extend I E u) hσ
      (mdifferentiableAt_extend I E v),
    add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, inner_covLC_extend hσ u v]
  simp only [extend_apply_self]
  ring

/-- `covLC` satisfies the axioms of a covariant derivative on the tangent bundle. -/
lemma isCovariantDerivativeOn_covLC :
    IsCovariantDerivativeOn E (covLC (I := I) (M := M)) Set.univ where
  add hσ hσ' _ := covLC_add hσ hσ'
  leibniz hσ hf _ := covLC_smul hσ hf

variable (I M) in
/-- The **Levi-Civita connection** of a Riemannian manifold, as a bundled covariant derivative on
the tangent bundle. -/
noncomputable def leviCivita : CovariantDerivative I E (fun x : M ↦ TangentSpace I x) where
  toFun := covLC
  isCovariantDerivativeOnUniv := isCovariantDerivativeOn_covLC

@[simp] lemma leviCivita_apply (σ : Π x : M, TangentSpace I x) (x : M) :
    leviCivita I M σ x = covLC σ x := rfl

end GaloisForLFunctions.HTGeometry.LeviCivita
