import GaloisForLFunctions.HTGeometry.MvPolynomialJacobianFDeriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# The compact-open Baire space of multivariate entire sources

We use the affine-line model: a source on `ℂᵈ` is continuous and its restriction to every affine
complex line is entire.  This condition is closed for compact-open convergence by the one-variable
Weierstrass theorem on each line.  Consequently the source space is completely metrizable and
Baire.  The definition is invariant under affine automorphisms and contains every
Fréchet-holomorphic function, in particular every multivariable polynomial.

For finite-dimensional complex spaces this continuous Gâteaux-entire model is classically
equivalent to Fréchet holomorphy.  The determinant and interpolation argument below needs only the
affine-line formulation and its intrinsic directional jets.
-/

open Filter Function Set TopologicalSpace Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The affine complex line `z ↦ x + z v`. -/
def affineComplexLine {d : ℕ} (x v : Fin d → ℂ) :
    C(ℂ, Fin d → ℂ) where
  toFun z := x + z • v
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact continuous_const.add (continuous_id.smul continuous_const)

/-- A continuous source on `ℂᵈ` is line-entire when every affine complex-line restriction is
an entire one-variable function. -/
def LineEntire {d : ℕ} (f : C(Fin d → ℂ, ℂ)) : Prop :=
  ∀ (x v : Fin d → ℂ), Differentiable ℂ (fun z : ℂ => f (x + z • v))

/-- Line-entire sources form a complex linear subspace of the compact-open continuous-map
space. -/
def multivariateEntireSubmodule (d : ℕ) :
    Submodule ℂ C(Fin d → ℂ, ℂ) where
  carrier := {f | LineEntire f}
  zero_mem' := by
    intro x v
    simp
  add_mem' := by
    intro f g hf hg x v
    simpa using! (hf x v).add (hg x v)
  smul_mem' := by
    intro c f hf x v
    simpa using! (hf x v).const_smul c

/-- Compact-open multivariate entire sources, in the coordinate-line model. -/
abbrev MultivariateEntire (d : ℕ) := multivariateEntireSubmodule d

theorem differentiable_affineComplexLine {d : ℕ}
    (x v : Fin d → ℂ) :
    Differentiable ℂ (affineComplexLine x v) := by
  rw [differentiable_pi]
  intro i
  simp [affineComplexLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Fréchet-holomorphic functions are line-entire. -/
theorem lineEntire_of_differentiable {d : ℕ}
    (f : C(Fin d → ℂ, ℂ)) (hf : Differentiable ℂ f) :
    LineEntire f := by
  intro x v
  exact hf.comp (differentiable_affineComplexLine x v)

/-- Multivariable polynomials are members of the compact-open entire-source space. -/
def mvPolynomialMultivariateEntire {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) : MultivariateEntire d :=
  ⟨⟨fun x => MvPolynomial.eval x P,
      (differentiable_mvPolynomial_eval_complex P).continuous⟩,
    lineEntire_of_differentiable _
      (differentiable_mvPolynomial_eval_complex P)⟩

/-- Line-entire sources are sequentially closed under compact-open convergence. -/
theorem isSeqClosed_lineEntire (d : ℕ) :
    IsSeqClosed {f : C(Fin d → ℂ, ℂ) | LineEntire f} := by
  intro u f hu huf x v
  let line := affineComplexLine x v
  have hcomp : Tendsto (fun n => (u n).comp line) atTop (𝓝 (f.comp line)) :=
    ((ContinuousMap.uniformContinuous_comp_left line).continuous.tendsto f).comp huf
  have hloc : TendstoLocallyUniformly
      (fun n z => (u n).comp line z) (f.comp line) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hcomp
  have hdiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun z => (u n).comp line z) Set.univ := by
    filter_upwards [] with n
    exact (hu n x v).differentiableOn
  have hlimit := hloc.tendstoLocallyUniformlyOn.differentiableOn hdiff isOpen_univ
  have hd : Differentiable ℂ (f.comp line) := by
    intro z
    simpa only [differentiableWithinAt_univ] using hlimit z (Set.mem_univ z)
  simpa [line, affineComplexLine, Function.comp_def] using hd

/-- The line-entire locus is closed in the compact-open continuous-map space. -/
theorem isClosed_lineEntire (d : ℕ) :
    IsClosed {f : C(Fin d → ℂ, ℂ) | LineEntire f} :=
  (isSeqClosed_lineEntire d).isClosed

noncomputable instance multivariateEntire_complete (d : ℕ) :
    CompleteSpace (MultivariateEntire d) :=
  (isClosed_lineEntire d).completeSpace_coe

noncomputable instance multivariateEntire_completelyMetrizable (d : ℕ) :
    IsCompletelyMetrizableSpace (MultivariateEntire d) :=
  (isClosed_lineEntire d).isCompletelyMetrizableSpace

/-- The compact-open multivariate entire-source space is Baire. -/
noncomputable instance multivariateEntire_baire (d : ℕ) :
    BaireSpace (MultivariateEntire d) := by
  infer_instance

end

end GaloisForLFunctions.HTGeometry
