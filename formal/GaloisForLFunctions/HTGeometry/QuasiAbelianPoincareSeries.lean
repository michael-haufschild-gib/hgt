import GaloisForLFunctions.HTGeometry.QuasiAbelianAutomorphicForms
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Poincare series for a fixed quasi-Abelian automorphic factor

The literal Poincare term attached to a seed `f` and lattice element `γ` is

`ψ(γ,x)⁻¹ f(x+γ)`.

Local normal convergence makes its sum line-entire. Reindexing the sum by lattice translation
and applying the factor cocycle proves the exact fixed-factor automorphy law. No convergence or
jet-surjectivity conclusion is stored in the factor structure: every constructed section carries
its own local-normal-convergence proof.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One term of the Poincare series generated from `seed` by the fixed factor `ψ`. -/
def poincareTerm {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (γ : Γ) (x : Fin d → ℂ) : ℂ :=
  ((ψ.factor γ).1 x)⁻¹ * seed.1 (x + γ.1)

/-- Each Poincare term is continuous. -/
theorem continuous_poincareTerm {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d) (γ : Γ) :
    Continuous (poincareTerm ψ seed γ) := by
  apply Continuous.mul
  · exact (ψ.factor γ).1.continuous.inv₀ (ψ.nowhereZero γ)
  · exact seed.1.continuous.comp (continuous_id.add continuous_const)

/-- Each Poincare term remains entire on every affine complex line. -/
theorem lineEntire_poincareTerm {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d) (γ : Γ) :
    LineEntire ⟨poincareTerm ψ seed γ, continuous_poincareTerm ψ seed γ⟩ := by
  intro x v
  have hf : Differentiable ℂ
      (fun z : ℂ => ((ψ.factor γ).1 (x + z • v))⁻¹) :=
    ((ψ.factor γ).property x v).inv fun z => ψ.nowhereZero γ (x + z • v)
  have hs := seed.property (x + γ.1) v
  change Differentiable ℂ (fun z : ℂ =>
    ((ψ.factor γ).1 (x + z • v))⁻¹ * seed.1 (x + z • v + γ.1))
  apply hf.mul
  simpa only [add_assoc, add_left_comm, add_comm] using hs

/-- One Poincare summand as a compact-open entire source. -/
def poincareTermEntire {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d) (γ : Γ) :
    MultivariateEntire d :=
  ⟨⟨poincareTerm ψ seed γ, continuous_poincareTerm ψ seed γ⟩,
    lineEntire_poincareTerm ψ seed γ⟩

/-- Pointwise Poincare sum over the complete translation lattice. -/
def poincareSeries {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (x : Fin d → ℂ) : ℂ :=
  ∑' γ, poincareTerm ψ seed γ x

/-- The factor cocycle transports one Poincare term to its shifted lattice index. -/
theorem poincareTerm_shift {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (γ δ : Γ) (x : Fin d → ℂ) :
    poincareTerm ψ seed γ (x + δ.1) =
      (ψ.factor δ).1 x * poincareTerm ψ seed (γ + δ) x := by
  rw [poincareTerm, poincareTerm]
  have hc := ψ.cocycle γ δ x
  have hγ := ψ.nowhereZero γ (x + δ.1)
  have hδ := ψ.nowhereZero δ x
  rw [hc]
  field_simp
  congr 1
  ext i
  simp [add_comm, add_left_comm]

/-- Reindexing the complete sum gives the fixed-factor automorphy law. -/
theorem poincareSeries_shift {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (δ : Γ) (x : Fin d → ℂ) :
    poincareSeries ψ seed (x + δ.1) =
      (ψ.factor δ).1 x * poincareSeries ψ seed x := by
  simp_rw [poincareSeries, poincareTerm_shift ψ seed]
  rw [tsum_mul_left]
  exact congrArg ((ψ.factor δ).1 x * ·)
    ((Equiv.addRight δ).tsum_eq (fun γ => poincareTerm ψ seed γ x))

/-- A locally normally convergent Poincare sum is continuous. -/
theorem continuous_poincareSeries_of_summableLocallyUniformly
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun γ => poincareTerm ψ seed γ) Set.univ) :
    Continuous (poincareSeries ψ seed) := by
  rw [← continuousOn_univ]
  apply hnormal.hasSumLocallyUniformlyOn.continuousOn
  exact (Filter.Eventually.of_forall fun S =>
    (continuous_finsetSum S fun γ _ =>
      continuous_poincareTerm ψ seed γ).continuousOn).frequently

/-- A locally normally convergent Poincare sum is entire on every affine complex line. -/
theorem lineEntire_poincareSeries_of_summableLocallyUniformly
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun γ => poincareTerm ψ seed γ) Set.univ) :
    LineEntire ⟨poincareSeries ψ seed,
      continuous_poincareSeries_of_summableLocallyUniformly ψ seed hnormal⟩ := by
  intro x v
  let line := affineComplexLine x v
  have hline : SummableLocallyUniformlyOn
      (fun γ z => poincareTerm ψ seed γ (line z)) Set.univ :=
    hnormal.comp line (mapsTo_univ _ _) line.continuous.continuousOn
  have hd : DifferentiableOn ℂ
      (fun z => ∑' γ, poincareTerm ψ seed γ (line z)) Set.univ := by
    apply hline.hasSumLocallyUniformlyOn.differentiableOn
    · exact Filter.Eventually.of_forall fun S =>
        (Differentiable.fun_sum fun γ _ =>
          lineEntire_poincareTerm ψ seed γ x v).differentiableOn
    · exact isOpen_univ
  simpa [poincareSeries, line, affineComplexLine] using
    (differentiableOn_univ.mp hd)

/-- A locally normally convergent Poincare series as a line-entire source. -/
def poincareSeriesEntire {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun γ => poincareTerm ψ seed γ) Set.univ) :
    MultivariateEntire d :=
  ⟨⟨poincareSeries ψ seed,
      continuous_poincareSeries_of_summableLocallyUniformly ψ seed hnormal⟩,
    lineEntire_poincareSeries_of_summableLocallyUniformly ψ seed hnormal⟩

/-- **Poincare construction.** Every locally normally convergent Poincare series belongs to the
fixed automorphic-factor section space. -/
def poincareSeriesAutomorphicForm {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun γ => poincareTerm ψ seed γ) Set.univ) : ψ.forms :=
  ⟨poincareSeriesEntire ψ seed hnormal,
    fun γ x => poincareSeries_shift ψ seed γ x⟩

end

end GaloisForLFunctions.HTGeometry
