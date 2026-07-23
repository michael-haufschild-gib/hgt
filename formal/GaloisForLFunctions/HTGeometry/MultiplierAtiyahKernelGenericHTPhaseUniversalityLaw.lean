import GaloisForLFunctions.HTGeometry.AtiyahKernelProjectiveFinitenessUniversalityLaw
import GaloisForLFunctions.HTGeometry.ProjectiveDirectionalFullMeasure

/-!
# Multiplier Atiyah kernel versus generic projective hypertranscendence

The multiplier Atiyah class and the complete projective finite-law filtration live on the same
two-direction law space.  Combining their terminal dichotomies gives a phase law that neither
statement sees alone: unless some finite jet order collapses every projective direction, the
Atiyah kernel is finite while complete-hypertranscendental directions are dense, residual, and
conull in every standard projective chart.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped LinearAlgebra.Projectivization

variable {G K L : Type*} [Group G] [Field K] [Field L]
  [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
  [CharZero K]

/-- **Atiyah-kernel/generic-HT phase law.**  In a compatible two-direction multiplier system,
either a finite directional jet order is universal, or the projectivized zero locus of the
multiplier Atiyah class is finite and every standard chart has a dense residual complete-HT locus
with Lebesgue-null complement. -/
theorem multiplierAtiyahKernel_projectiveCollapse_or_finiteConullHT
    (rhoK : G →* (K ≃+* K)) (rhoL : G →* (L ≃+* L))
    (hfix : ∀ g c, rhoK g (algebraMap ℂ K c) = algebraMap ℂ K c)
    (hcomp : ∀ g y, rhoL g (algebraMap K L y) = algebraMap K L (rhoK g y))
    (hfixed : ∀ z : L, (∀ g, rhoL g z = z) → ∃ q : K, algebraMap K L q = z)
    (D0 : Fin 2 → equivariantDerivations rhoK hfix)
    (δ : Fin 2 → Derivation ℂ L L)
    (hDcomp : ∀ i y, δ i (algebraMap K L y) = algebraMap K L ((D0 i).1 y))
    (hDcomm : ∀ i g y, δ i (rhoL g y) = rhoL g (δ i y))
    (hfixL : ∀ g c, rhoL g (algebraMap ℂ L c) = algebraMap ℂ L c)
    (a : G → Kˣ)
    (ha : ∀ g h, (a (g * h) : K) = rhoK g (a h : K) * (a g : K))
    (X : L) (hX : X ≠ 0)
    (hmul : ∀ g, rhoL g X = algebraMap K L (a g : K) * X) :
    (∃ N, projectiveDirectionalFiniteLawLocus (K := K) δ X N = Set.univ) ∨
      (({p : ℙ ℂ (Fin 2 → ℂ) |
          multiplierAtiyahClassMap rhoK hfix a ha
            (∑ i, p.rep i • D0 i) = 0} : Set (ℙ ℂ (Fin 2 → ℂ))).Finite ∧
        ∀ i : Fin 2,
          Dense {c : Fin 1 → ℂ |
            projectiveChartPoint i c ∈ projectiveDirectionalHTLocus (K := K) δ X} ∧
          {c : Fin 1 → ℂ |
            projectiveChartPoint i c ∈ projectiveDirectionalHTLocus (K := K) δ X} ∈
              residual (Fin 1 → ℂ) ∧
          volume {c : Fin 1 → ℂ |
            projectiveChartPoint i c ∉ projectiveDirectionalHTLocus (K := K) δ X} = 0) := by
  rcases complexProjectiveDirectionalFiniteLaw_exactDichotomy
      (K := K) 1 δ X with hcollapse | hgeneric
  · exact Or.inl hcollapse
  · right
    rcases multiplierAtiyahKernel_orderOne_universal_or_projectivelyFinite
        rhoK rhoL hfix hcomp hfixed D0 δ hDcomp hDcomm hfixL
        a ha X hX hmul with horderOne | hkernel
    · exact False.elim (hgeneric.1 ⟨1, horderOne⟩)
    · exact ⟨hkernel, hgeneric.2⟩

end

end GaloisForLFunctions.HTGeometry
