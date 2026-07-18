import GaloisForLFunctions.HTGeometry.MvPolynomialJacobianFDeriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# The compact-open Baire space of multivariate entire sources

We use the classical coordinate-line model: a source on `ℂᵈ` is continuous and its restriction to
every complex coordinate line is entire.  This condition is closed for compact-open convergence,
by the one-variable Weierstrass theorem on each line.  Consequently the source space is completely
metrizable and Baire.  Every Fréchet-holomorphic function, and in particular every multivariable
polynomial, belongs to it.

The converse identification with Fréchet holomorphy is the several-complex-variables Hartogs
theorem; the category and interpolation arguments only use the coordinate-line formulation.
-/

open Filter Function Set TopologicalSpace Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The affine complex line through `x` in coordinate `i`. -/
def coordinateComplexLine {d : ℕ} (i : Fin d) (x : Fin d → ℂ) :
    C(ℂ, Fin d → ℂ) where
  toFun z := Function.update x i z
  continuous_toFun := by
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa [Function.update_apply] using continuous_id
    · simpa [Function.update_apply, hji] using continuous_const

/-- A continuous source on `ℂᵈ` is coordinate-entire when every affine coordinate slice is an
entire one-variable function. -/
def CoordinateEntire {d : ℕ} (f : C(Fin d → ℂ, ℂ)) : Prop :=
  ∀ i x, Differentiable ℂ (fun z => f (Function.update x i z))

/-- Coordinate-entire sources form a complex linear subspace of the compact-open continuous-map
space. -/
def multivariateEntireSubmodule (d : ℕ) :
    Submodule ℂ C(Fin d → ℂ, ℂ) where
  carrier := {f | CoordinateEntire f}
  zero_mem' := by
    intro i x
    simpa using (differentiable_const (c := (0 : ℂ)) :
      Differentiable ℂ (fun _ : ℂ => 0))
  add_mem' := by
    intro f g hf hg i x
    simpa using (hf i x).add (hg i x)
  smul_mem' := by
    intro c f hf i x
    simpa using (hf i x).const_smul c

/-- Compact-open multivariate entire sources, in the coordinate-line model. -/
abbrev MultivariateEntire (d : ℕ) := multivariateEntireSubmodule d

theorem differentiable_coordinateComplexLine {d : ℕ}
    (i : Fin d) (x : Fin d → ℂ) :
    Differentiable ℂ (coordinateComplexLine i x) := by
  rw [differentiable_pi]
  intro j
  by_cases hji : j = i
  · subst j
    simpa [coordinateComplexLine, Function.update_apply] using
      (differentiable_id : Differentiable ℂ (fun z : ℂ => z))
  · simpa [coordinateComplexLine, Function.update_apply, hji] using
      (differentiable_const (c := x j) : Differentiable ℂ (fun _ : ℂ => x j))

/-- Fréchet-holomorphic functions are coordinate-entire. -/
theorem coordinateEntire_of_differentiable {d : ℕ}
    (f : C(Fin d → ℂ, ℂ)) (hf : Differentiable ℂ f) :
    CoordinateEntire f := by
  intro i x
  exact hf.comp (differentiable_coordinateComplexLine i x)

/-- Multivariable polynomials are members of the compact-open entire-source space. -/
def mvPolynomialMultivariateEntire {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) : MultivariateEntire d :=
  ⟨⟨fun x => MvPolynomial.eval x P,
      (differentiable_mvPolynomial_eval_complex P).continuous⟩,
    coordinateEntire_of_differentiable _
      (differentiable_mvPolynomial_eval_complex P)⟩

/-- Coordinate-entire sources are sequentially closed under compact-open convergence. -/
theorem isSeqClosed_coordinateEntire (d : ℕ) :
    IsSeqClosed {f : C(Fin d → ℂ, ℂ) | CoordinateEntire f} := by
  intro u f hu huf
  intro i x
  let line := coordinateComplexLine i x
  have hcomp : Tendsto (fun n => (u n).comp line) atTop (𝓝 (f.comp line)) :=
    ((ContinuousMap.uniformContinuous_comp_left line).continuous.tendsto f).comp huf
  have hloc : TendstoLocallyUniformly
      (fun n z => (u n).comp line z) (f.comp line) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hcomp
  have hdiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun z => (u n).comp line z) Set.univ := by
    filter_upwards [] with n
    exact (hu n i x).differentiableOn
  have hlimit := hloc.tendstoLocallyUniformlyOn.differentiableOn hdiff isOpen_univ
  have hd : Differentiable ℂ (f.comp line) := by
    intro z
    simpa only [differentiableWithinAt_univ] using hlimit z (Set.mem_univ z)
  simpa [line, coordinateComplexLine, Function.comp_def] using hd

/-- The coordinate-entire locus is closed in the compact-open continuous-map space. -/
theorem isClosed_coordinateEntire (d : ℕ) :
    IsClosed {f : C(Fin d → ℂ, ℂ) | CoordinateEntire f} :=
  (isSeqClosed_coordinateEntire d).isClosed

noncomputable instance multivariateEntire_complete (d : ℕ) :
    CompleteSpace (MultivariateEntire d) :=
  (isClosed_coordinateEntire d).completeSpace_coe

noncomputable instance multivariateEntire_completelyMetrizable (d : ℕ) :
    IsCompletelyMetrizableSpace (MultivariateEntire d) :=
  (isClosed_coordinateEntire d).isCompletelyMetrizableSpace

/-- The compact-open multivariate entire-source space is Baire. -/
noncomputable instance multivariateEntire_baire (d : ℕ) :
    BaireSpace (MultivariateEntire d) := by
  infer_instance

end

end GaloisForLFunctions.HTGeometry
