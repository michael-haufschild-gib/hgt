import GaloisForLFunctions.HTGeometry.PeriodIntegralIndependenceWitness

/-!
# The bottom-face packet is unconditionally differentially independent

Bottom-layer atomicity of the elliptic gamma hierarchy carries two arithmetic hypotheses on the
periods: no integral relation with `1` across the whole family, and rational independence of `1`
with the two surviving parameters.  Both hold for the imaginary logarithms of two distinct primes,
so the packet of the empty face on that period pair is differentially independent over every
differentially algebraic extension of the constants, with no hypothesis left.

* `twoLogPrimePeriods`, `twoLogPrimePeriods_im_pos`;
* **`multipleEllipticGammaFacePacket_diffIndepOn_logPrime`** — the unconditional bottom-layer
  statement.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

namespace HTGeometry

/-- The two-parameter period family `(i log p, i log r)`. -/
def twoLogPrimePeriods (p r : Nat.Primes) : Bool → ℂ :=
  logPrimePeriod (fun x : Bool => if x then p else r)

theorem twoLogPrimePeriods_im_pos (p r : Nat.Primes) (i : Bool) :
    0 < (twoLogPrimePeriods p r i).im :=
  logPrimePeriod_im_pos _ i

theorem periodsIntegrallyIndependent_twoLogPrimePeriods {p r : Nat.Primes} (hpr : p ≠ r) :
    PeriodsIntegrallyIndependent (twoLogPrimePeriods p r) := by
  refine periodsIntegrallyIndependent_logPrimePeriod ?_
  intro x y hxy
  cases x <;> cases y <;> simp_all

/-- **Unconditional bottom-layer atomicity.**  On the period pair `(i log p, i log r)` for distinct
primes the empty-face packet is differentially independent over the differential adjunction of any
family of differentially algebraic meromorphic functions. -/
theorem multipleEllipticGammaFacePacket_diffIndepOn_logPrime {p r : Nat.Primes} (hpr : p ≠ r)
    {G : Set (meroField (Set.univ : Set ℂ))} (hG : ∀ g ∈ G, DifferentialAlgebraicOver ℂ g) :
    DiffIndepOn ↥(differentialAdjoin ℂ G)
      (multipleEllipticGammaFacePacket (twoLogPrimePeriods p r)
        (twoLogPrimePeriods_im_pos p r) ∅) :=
  multipleEllipticGammaFacePacket_diffIndepOn_bottom (twoLogPrimePeriods p r)
    (twoLogPrimePeriods_im_pos p r) (periodsIntegrallyIndependent_twoLogPrimePeriods hpr) ∅
    (a := true) (b := false) (by simp) (by simp) (by simp)
    (fun i _ => Bool.eq_false_or_eq_true i)
    (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent
      (twoLogPrimePeriods p r) (periodsIntegrallyIndependent_twoLogPrimePeriods hpr) (by simp)) hG

/-- **Universal bottom-layer law.**  Over any finite index there is a period family in the upper half
plane whose bottom-face packets are differentially independent over every differentially algebraic
extension of the constants — simultaneously for every face with exactly two surviving parameters. -/
theorem exists_periods_bottom_faces_diffIndepOn (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∃ (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im),
      ∀ (J : Finset ι) {a b : ι}, a ∉ J → b ∉ J → a ≠ b → (∀ i, i ∉ J → i = a ∨ i = b) →
        ∀ {G : Set (meroField (Set.univ : Set ℂ))}, (∀ g ∈ G, DifferentialAlgebraicOver ℂ g) →
          DiffIndepOn ↥(differentialAdjoin ℂ G) (multipleEllipticGammaFacePacket τ hτ J) := by
  classical
  set e : ι ↪ Nat.Primes :=
    ((Fintype.equivFin ι).toEmbedding.trans Fin.valEmbedding).trans
      (Infinite.natEmbedding Nat.Primes) with he
  refine ⟨logPrimePeriod e, logPrimePeriod_im_pos e, ?_⟩
  intro J a b haJ hbJ hab hJ G hG
  exact multipleEllipticGammaFacePacket_diffIndepOn_bottom _ _
    (periodsIntegrallyIndependent_logPrimePeriod e.injective) J haJ hbJ hab hJ
    (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent _
      (periodsIntegrallyIndependent_logPrimePeriod e.injective) hab) hG

end HTGeometry

end

end GaloisForLFunctions
