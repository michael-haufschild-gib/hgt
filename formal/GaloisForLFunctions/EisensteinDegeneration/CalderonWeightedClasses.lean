import GaloisForLFunctions.EisensteinDegeneration.ComplementaryWeights
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPoissonCalderonGraph

/-!
# Complementary weighting on the Meyer–Poisson quotient

The reflected collar defect is an actual regulator with an explicitly
computed kernel and quotient. Complementary weighting therefore produces
equal quotient classes, even when some defect values vanish. Before taking
the quotient, their difference lies on the Poisson graph and is killed by
every first-suspension-mode regulator.
-/

namespace GaloisForLFunctions.EisensteinDegeneration

open _root_.RHTower
open scoped BigOperators

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Weighted collar differences satisfy the concrete reflected Poisson boundary condition. -/
theorem weightedCollar_difference_mem_graph (r : ℝ) (u : ι → ℂ × ℂ) (i j : ι) :
    weightedComponent (deningerMeyerReflectedCollarDefect r) u i -
      weightedComponent (deningerMeyerReflectedCollarDefect r) u j ∈
        deningerMeyerPoissonCalderonGraph r :=
  weightedComponent_difference_mem_kernel _ u i j

/-- The weighted collars define the same class in the actual Calderón quotient. -/
theorem weightedCollar_quotient_eq (r : ℝ) (u : ι → ℂ × ℂ) (i j : ι) :
    (Submodule.Quotient.mk
        (weightedComponent (deningerMeyerReflectedCollarDefect r) u i) :
      (ℂ × ℂ) ⧸ deningerMeyerPoissonCalderonGraph r) =
    Submodule.Quotient.mk
      (weightedComponent (deningerMeyerReflectedCollarDefect r) u j) :=
  weightedComponent_quotient_eq _ u i j

/-- The explicit quotient equivalence determines the common weighted class from the product
of its regulator values. No injectivity assumption is needed. -/
theorem weightedCalderonClass_eq (r : ℝ)
    (c : ι → (ℂ × ℂ) ⧸ deningerMeyerPoissonCalderonGraph r) (i : ι) :
    weightedComponent (deningerMeyerPoissonCalderonQuotientEquiv r).toLinearMap c i =
      (deningerMeyerPoissonCalderonQuotientEquiv r).symm
        (∏ j, deningerMeyerPoissonCalderonQuotientEquiv r (c j)) := by
  apply (deningerMeyerPoissonCalderonQuotientEquiv r).injective
  rw [LinearEquiv.apply_symm_apply]
  exact weightedComponent_regulator _ c i

/-- All first-mode regulators annihilate the weighted comparison, including the zero packet. -/
theorem weightedCollar_firstMode_zero (p : Nat.Primes)
    (packet : DeningerPrimePacketComplexHaarL2 p) (u : ι → ℂ × ℂ) (i j : ι) :
    deningerMeyerReflectedFirstModeRegulator p packet
      (weightedComponent (deningerMeyerReflectedCollarDefect (p : ℝ)) u i -
        weightedComponent (deningerMeyerReflectedCollarDefect (p : ℝ)) u j) = 0 := by
  rw [deningerMeyerReflectedFirstModeRegulator_apply, map_sub,
    weightedComponent_regulator, weightedComponent_regulator, sub_self, zero_smul]

/-- Iterated degenerations yield the same weighted collar as the full product indexing.
In particular, two binary decompositions give the four complementary triple products. -/
theorem weightedCollar_nested (r : ℝ) (u : ι → κ → ℂ × ℂ) (i : ι) (j : κ) :
    complementaryWeight
        (fun a => ∏ b, deningerMeyerReflectedCollarDefect r (u a b)) i •
      weightedComponent (deningerMeyerReflectedCollarDefect r) (u i) j =
    weightedComponent (deningerMeyerReflectedCollarDefect r)
      (fun p : ι × κ => u p.1 p.2) (i, j) :=
  nested_weightedComponent _ u i j

end

end GaloisForLFunctions.EisensteinDegeneration
