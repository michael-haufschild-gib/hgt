import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedProbeAtoms
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.TorsionPrimePairKernel
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedTorsionOperators

/-!
# Prime-pair probes for the actual completed torsion form

Unit conductor atoms realize the arithmetic kernel inside every weighted Hilbert
carrier. Their prime-pair sums retain the exact finite energy, and distinct
odd-prime pairs are orthogonal for the original continuous limiting form.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticIntersectionTheory

/-- The actual Hilbert probe with unit coefficients at a prime and its double. -/
def spacingPrimePairProbe (δ : ℝ) (p : Nat.Primes) : WeightedProbe δ :=
  weightedConductorAtom δ ⟨p.val,p.property.pos⟩ +
    weightedConductorAtom δ ⟨2*p.val,by have h:=p.property.pos; omega⟩

/-- A prime conductor defines a positive arithmetic atom. -/
def spacingPrimeProbe (δ : ℝ) (p : Nat.Primes) : WeightedProbe δ :=
  weightedConductorAtom δ ⟨p.val,p.property.pos⟩

/-- The continuous arithmetic form reads the original kernel on conductor atoms. -/
theorem spacingLimitOperator_conductorAtoms (δ : ℝ) (hδ : 0<δ) (m n : ℕ+) :
    spacingLimitOperator δ hδ (weightedConductorAtom δ m) (weightedConductorAtom δ n) =
      spacingLimitKernel m.val n.val := by
  rw [spacingLimitOperator_apply,weightedKernelPairing_conductorAtoms]

/-- The prime-pair probe retains the exact finite arithmetic energy. -/
theorem spacingPrimePairProbe_energy (δ : ℝ) (hδ : 0<δ) (p : Nat.Primes)
    (hp2 : 2<p.val) :
    spacingLimitOperator δ hδ (spacingPrimePairProbe δ p) (spacingPrimePairProbe δ p) =
      2*tameDifferent p.val+Real.log 2-2*spacingPrimePairCoupling := by
  unfold spacingPrimePairProbe
  simp only [map_add,add_apply,spacingLimitOperator_conductorAtoms]
  change spacingLimitKernel p.val p.val+spacingLimitKernel (2*p.val) p.val+
    (spacingLimitKernel p.val (2*p.val)+spacingLimitKernel (2*p.val) (2*p.val))=_
  calc _ = spacingLimitKernel p.val p.val+spacingLimitKernel p.val (2*p.val)+
        spacingLimitKernel (2*p.val) p.val+spacingLimitKernel (2*p.val) (2*p.val) := by ring
       _ = _ := spacingLimitKernel_primePair_sum p.val p.property hp2

/-- Distinct odd prime-pair probes are orthogonal for the actual limiting form. -/
theorem spacingPrimePairProbe_orthogonal (δ : ℝ) (hδ : 0<δ) (p q : Nat.Primes)
    (hp2 : 2<p.val) (hq2 : 2<q.val) (hpq : p≠q) :
    spacingLimitOperator δ hδ (spacingPrimePairProbe δ p) (spacingPrimePairProbe δ q)=0 := by
  have hne : p.val≠q.val := fun h => hpq (Subtype.ext h)
  have h := spacingLimitKernel_primePairs_orthogonal p.val q.val p.property q.property hp2 hq2 hne
  unfold spacingPrimePairProbe
  simp only [map_add,add_apply,spacingLimitOperator_conductorAtoms]
  change spacingLimitKernel p.val q.val+spacingLimitKernel (2*p.val) q.val+
    (spacingLimitKernel p.val (2*q.val)+spacingLimitKernel (2*p.val) (2*q.val))=0
  calc _ = (0:ℝ)+0+(0+0) := congrArg₂ (fun a b : ℝ => a+b)
        (congrArg₂ (fun a b : ℝ => a+b) (h false false) (h true false))
        (congrArg₂ (fun a b : ℝ => a+b) (h false true) (h true true))
       _ = 0 := by ring

/-- A prime probe has positive energy. -/
theorem spacingPrimeProbe_energy_pos (δ : ℝ) (hδ : 0<δ) (p : Nat.Primes) :
    0<spacingLimitOperator δ hδ (spacingPrimeProbe δ p) (spacingPrimeProbe δ p) := by
  rw [spacingPrimeProbe,spacingLimitOperator_conductorAtoms]
  exact spacingLimitKernel_prime_self_pos p.val p.property

/-- Distinct odd prime probes are orthogonal for the limiting form. -/
theorem spacingPrimeProbe_orthogonal (δ : ℝ) (hδ : 0<δ) (p q : Nat.Primes)
    (hp2 : 2<p.val) (hq2 : 2<q.val) (hpq : p≠q) :
    spacingLimitOperator δ hδ (spacingPrimeProbe δ p) (spacingPrimeProbe δ q)=0 := by
  rw [spacingPrimeProbe,spacingPrimeProbe,spacingLimitOperator_conductorAtoms]
  exact spacingLimitKernel_primePairs_orthogonal p.val q.val p.property q.property hp2 hq2
    (fun h => hpq (Subtype.ext h)) false false

#print axioms spacingLimitOperator_conductorAtoms
#print axioms spacingPrimePairProbe_energy
#print axioms spacingPrimePairProbe_orthogonal
#print axioms spacingPrimeProbe_energy_pos
#print axioms spacingPrimeProbe_orthogonal
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
