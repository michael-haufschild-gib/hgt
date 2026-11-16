import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularDyadicBlocks

/-!
# Exact angular phases in physical rows

The reflected denominator character separates across fixed conductor, row and slot ideals.
Together with the column character, these are exactly the bounded weights admitted by
physical reflected energy estimates.
-/

open scoped BigOperators Classical ContDiff ComplexConjugate
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CompletedDyadic CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection
open CanonicalQuadraticSieve InverseMoment
namespace InverseReflectedPhase
noncomputable section
local notation "Eis" => Eisenstein.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def angularLiteralDyadicRow (ℓ : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    angularCuspDenominatorPhase ℓ (c*∏ j,(F.reflected K hK (S P.val.val)).generator j)*
    angularLiteralDyadicBlock ℓ (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc
      (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) X u i

theorem angularLiteralDyadicRow_eq_physical (ℓ : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0< QK) (hQP : 0< QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK)
    (hprod : ∀ P∈Pset, (∏ j,(S P).ideal j)=P)
    (hPr : ∀ P∈Pset, QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤ QP)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) :
    angularLiteralDyadicRow ℓ F K hK S jF Pset D s hc u i W θ X r aw=
      angularWeightedFinitePhysicalKernelRow ℓ F K hK S jF Pset (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
        D s hc u i.1 (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
        W θ X
          (fun K => r K*angularIdealPhase ℓ (Ideal.span {c}*∏ j,F.ideal j)*angularIdealPhase ℓ K)
          (fun P => aw P*angularIdealPhase ℓ P) (angularCuspColumnPhase ℓ u i.1) := by
  unfold angularLiteralDyadicRow angularWeightedFinitePhysicalKernelRow CoprimeSourceIndex
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro P hP
  have hp : QP/2≤(Ideal.absNorm (∏ j,(S P.val.val).ideal j):ℝ) ∧
      (Ideal.absNorm (∏ j,(S P.val.val).ideal j):ℝ)≤ QP := by
    rw [hprod P.val.val P.val.property]
    exact hPr P.val.val P.val.property
  rw [angularLiteralDyadicBlock_eq_filtered_source ℓ F K hK (S P.val.val) jF (D P.val P.property)
    s hc u i QK QP hQK hQP hKr hp W θ X]
  rw [angular_reflected_denominator_phase,hprod P.val.val P.val.property]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  ring

end
end InverseReflectedPhase
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
