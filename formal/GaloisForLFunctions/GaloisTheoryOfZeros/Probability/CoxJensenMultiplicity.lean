import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.CoxResidualClassification
import GaloisForLFunctions.GaloisTheoryOfZeros.CenteredJensenDiscriminant

/-!
# Gamma–Cox detection of Jensen root collisions

The even and odd centered quotient discriminant criteria turn scalar detection
into nonseparability classification. The forced central root in odd degree
contributes no spurious collision.
-/

open scoped Classical
open Filter Topology
open FiniteFreeProbability
namespace GaloisForLFunctions.GaloisTheoryOfZeros
open GammaCox
noncomputable section

/-- Even Jensen discriminants detect repeated roots in the centered quotient. -/
theorem cox_evenJensen_collision (n : ℕ) :
    Tendsto (fun K => detection K (xiJensenReal (2 * n)).discr) atTop
      (𝓝 (if ¬ (evenCenteredQuotient n).Separable then 1 else 0)) := by
  simpa only [evenJensen_discr_zero_iff] using
    tendsto_detection (xiJensenReal (2 * n)).discr

/-- Odd Jensen discriminants detect quotient collisions, not their forced simple root. -/
theorem cox_oddJensen_collision (n : ℕ) :
    Tendsto (fun K => detection K (xiJensenReal (2 * n + 1)).discr) atTop
      (𝓝 (if ¬ (oddCenteredQuotient n).Separable then 1 else 0)) := by
  simpa only [oddJensen_discr_zero_iff] using
    tendsto_detection (xiJensenReal (2 * n + 1)).discr

/-- A finite list of even degrees is classified simultaneously. -/
theorem cox_evenJensen_family {ι : Type*} [Fintype ι] (n : ι → ℕ) :
    Tendsto (fun K => (binaryLaw K (fun i => (xiJensenReal (2 * n i)).discr)).real
      {b | b ≠ fun i => decide (¬ (evenCenteredQuotient (n i)).Separable)}) atTop (𝓝 0) := by
  exact tendsto_classification_error (fun i => (xiJensenReal (2 * n i)).discr)
    (fun i => ¬ (evenCenteredQuotient (n i)).Separable) fun i => by
    simp only [evenJensen_discr_zero_iff]

/-- A finite list of odd degrees is classified simultaneously. -/
theorem cox_oddJensen_family {ι : Type*} [Fintype ι] (n : ι → ℕ) :
    Tendsto (fun K => (binaryLaw K (fun i => (xiJensenReal (2 * n i + 1)).discr)).real
      {b | b ≠ fun i => decide (¬ (oddCenteredQuotient (n i)).Separable)}) atTop (𝓝 0) := by
  exact tendsto_classification_error (fun i => (xiJensenReal (2 * n i + 1)).discr)
    (fun i => ¬ (oddCenteredQuotient (n i)).Separable) fun i => by
    simp only [oddJensen_discr_zero_iff]

end
end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.cox_evenJensen_collision
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.cox_oddJensen_collision
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.cox_evenJensen_family
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.cox_oddJensen_family
