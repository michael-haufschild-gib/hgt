import GaloisForLFunctions.HTGeometry.SeibergWitten.FlatDirac

/-!
# Flat spinor connection on Euclidean four-space

The constant positive spinor bundle has a closed covariant derivative in mathlib: in its global
trivialization, differentiate the coefficient function by `mvfderiv`.  The only geometric bridge
needed for the Leibniz laws is that differentiability of a section of a trivial vector bundle is
equivalent to differentiability of its fiber-valued coefficient function.

Consequently, constant spinors are parallel and their chiral Dirac image is zero.  This is a
genuine connection on the smooth flat bundle, while remaining a flat Euclidean model rather than
a construction on every oriented four-manifold.
-/

noncomputable section

open scoped Manifold

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- A differentiable section of a trivial flat bundle has a differentiable coefficient function in
its global trivialization. -/
private theorem mdifferentiableAt_of_flatTrivialSection
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    {sigma : ∀ x, Bundle.Trivial FourSpace F x} {x : FourSpace}
    (hsigma : MDifferentiableAt fourModel (fourModel.prod 𝓘(ℝ, F)) (fun y =>
      (⟨y, sigma y⟩ : Bundle.TotalSpace F (Bundle.Trivial FourSpace F))) x) :
    MDifferentiableAt fourModel 𝓘(ℝ, F) sigma x := by
  letI : MemTrivializationAtlas (Bundle.Trivial.trivialization FourSpace F) :=
    ⟨by change Bundle.Trivial.trivialization FourSpace F ∈
      {Bundle.Trivial.trivialization FourSpace F}; simp⟩
  have htotal :=
    ((Bundle.Trivial.trivialization FourSpace F).mdifferentiableAt_totalSpace_iff
      fourModel (fun y => (⟨y, sigma y⟩ : Bundle.TotalSpace F
        (Bundle.Trivial FourSpace F))) (by simp)).mp hsigma
  simpa using htotal.2

/-- Standard flat covariant derivative on every constant real normed vector bundle. -/
noncomputable def flatTrivialCovariantDerivative
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    CovariantDerivative fourModel F (Bundle.Trivial FourSpace F) where
  toFun := fun sigma => mvfderiv fourModel sigma
  isCovariantDerivativeOnUniv := by
    constructor
    · intro sigma tau x hsigma htau _
      change MDifferentiableAt fourModel (fourModel.prod 𝓘(ℝ, F))
        (fun y => (⟨y, sigma y⟩ : Bundle.TotalSpace F (Bundle.Trivial FourSpace F))) x at hsigma
      change MDifferentiableAt fourModel (fourModel.prod 𝓘(ℝ, F))
        (fun y => (⟨y, tau y⟩ : Bundle.TotalSpace F (Bundle.Trivial FourSpace F))) x at htau
      simpa only [Pi.add_apply] using
        mvfderiv_add (mdifferentiableAt_of_flatTrivialSection F hsigma)
          (mdifferentiableAt_of_flatTrivialSection F htau)
    · intro sigma g x hsigma hg _
      change MDifferentiableAt fourModel (fourModel.prod 𝓘(ℝ, F))
        (fun y => (⟨y, sigma y⟩ : Bundle.TotalSpace F (Bundle.Trivial FourSpace F))) x at hsigma
      exact mvfderiv_smul hg (mdifferentiableAt_of_flatTrivialSection F hsigma)

/-- Standard flat covariant derivative on the constant positive spinor bundle. -/
noncomputable def flatPositiveSpinorCovariantDerivative :
    CovariantDerivative fourModel (Fin 2 → ℂ) flatPositiveSpinorBundle :=
  flatTrivialCovariantDerivative (Fin 2 → ℂ)

/-- Standard flat covariant derivative on the constant negative spinor bundle. -/
noncomputable def flatNegativeSpinorCovariantDerivative :
    CovariantDerivative fourModel (Fin 2 → ℂ) flatNegativeSpinorBundle :=
  flatTrivialCovariantDerivative (Fin 2 → ℂ)

/-- Standard flat covariant derivative on the determinant line of the flat Spinᶜ bundle. -/
noncomputable def flatDeterminantLineCovariantDerivative :
    CovariantDerivative fourModel ℂ flatDeterminantLineBundle :=
  flatTrivialCovariantDerivative ℂ

/-- The actual flat positive-spinor connection. -/
noncomputable def flatPositiveSpinorConnection :
    SmoothSpinorConnection FourSpace flatPositiveSpinorBundle where
  covariantDerivative := flatPositiveSpinorCovariantDerivative

/-- The actual flat negative-spinor connection. -/
noncomputable def flatNegativeSpinorConnection :
    SmoothSpinorConnection FourSpace flatNegativeSpinorBundle where
  covariantDerivative := flatNegativeSpinorCovariantDerivative

/-- Joint flat connection data on the positive and negative spinor bundles and determinant line.
This is the vector-bundle connection prelude induced by the trivial flat Spinᶜ model; integrating
it back to a connection on the algebraic principal `SpinC4` torsor is a separate global layer. -/
structure FlatSpinCConnectionPrelude where
  positive : SmoothSpinorConnection FourSpace flatPositiveSpinorBundle
  negative : SmoothSpinorConnection FourSpace flatNegativeSpinorBundle
  determinant : CovariantDerivative fourModel ℂ flatDeterminantLineBundle

/-- Closed flat Spinᶜ connection prelude, with all three associated-bundle connections. -/
noncomputable def flatSpinCConnectionPrelude : FlatSpinCConnectionPrelude where
  positive := flatPositiveSpinorConnection
  negative := flatNegativeSpinorConnection
  determinant := flatDeterminantLineCovariantDerivative

/-- Constant positive spinor section of the flat bundle. -/
def flatConstantPositiveSpinorSection (psi : Fin 2 → ℂ) :
    ∀ x : FourSpace, flatPositiveSpinorBundle x :=
  fun _ => psi

/-- Constant determinant-line section of the flat Spinᶜ bundle. -/
def flatConstantDeterminantLineSection (z : ℂ) :
    ∀ x : FourSpace, flatDeterminantLineBundle x :=
  fun _ => z

/-- Constant flat spinors are parallel for the constructed connection. -/
theorem flatPositiveSpinorCovariantDerivative_constant
    (psi : Fin 2 → ℂ) (x : FourSpace) :
    flatPositiveSpinorCovariantDerivative (flatConstantPositiveSpinorSection psi) x = 0 := by
  change mvfderiv fourModel (fun _ : FourSpace => psi) x = 0
  exact mvfderiv_const psi

/-- Constant determinant sections are parallel for the constructed determinant connection. -/
theorem flatDeterminantLineCovariantDerivative_constant
    (z : ℂ) (x : FourSpace) :
    flatDeterminantLineCovariantDerivative (flatConstantDeterminantLineSection z) x = 0 := by
  change mvfderiv fourModel (fun _ : FourSpace => z) x = 0
  exact mvfderiv_const z

/-- The chiral Dirac operator of the flat connection annihilates every constant spinor. -/
theorem flatChiralDirac_flatConstant
    (psi : Fin 2 → ℂ) (x : FourSpace) :
    flatChiralDirac flatPositiveSpinorConnection (flatConstantPositiveSpinorSection psi) x = 0 := by
  rw [flatChiralDirac_apply]
  simp [flatPositiveSpinorConnection, flatPositiveSpinorCovariantDerivative_constant]

/-- The chiral Dirac equation for the constructed flat Spinᶜ connection. -/
def flatChiralDiracEquation (sigma : ∀ x : FourSpace, flatPositiveSpinorBundle x) : Prop :=
  ∀ x, flatChiralDirac flatPositiveSpinorConnection sigma x = 0

/-- Every constant spinor solves the actual flat chiral Dirac equation. -/
theorem flatConstant_solves_flatChiralDiracEquation (psi : Fin 2 → ℂ) :
    flatChiralDiracEquation (flatConstantPositiveSpinorSection psi) :=
  fun x => flatChiralDirac_flatConstant psi x

end GaloisForLFunctions.HTGeometry.SeibergWitten
