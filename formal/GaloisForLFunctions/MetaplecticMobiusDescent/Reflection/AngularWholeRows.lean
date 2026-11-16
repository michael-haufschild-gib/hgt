import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularDyadicRows

/-!
# Whole angular reflected rows

Absolute convergence permits dyadic and slot summation to commute. The original
shape factor separates as before; the angular denominator stays inside each dyadic row.
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

def angularLiteralWholeRow (ℓ : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    angularMixedReflectedValue ℓ (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
      (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X


theorem angularLiteralWholeRow_eq_dyadic (ℓ : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then lambda^2∣a-1 else lambda^2∣c-1)
    (hchar : ∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2)
    (hj : ∀ i,jF i<6) (hprod : ∀ P∈Pset,(∏ j,(S P).ideal j)=P)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0< lo) (hWs : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (θ X : ℝ) (hX : 0< X) (r aw : Ideal Eis→ℂ) :
    angularLiteralWholeRow ℓ F K hK S jF Pset D s hc W θ X r aw=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryIdealGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,
          angularLiteralDyadicRow ℓ F K hK S jF Pset D s hc u i W θ X
            (fun K => r K*shapeArgument (primaryIdealGenerator K))
            (fun P => aw P*shapeArgument (primaryIdealGenerator P)) := by
  let : Finite Eisˣ := cubic_units_finite
  let : Fintype Eisˣ := Fintype.ofFinite _
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hts := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) u i => angularLiteralDyadicBlock ℓ (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let wt := fun P : L => (r K*shapeArgument (primaryIdealGenerator K))*(aw P.val.val*shapeArgument (primaryIdealGenerator P.val.val))*
    angularCuspDenominatorPhase ℓ (c*∏ j,(F.reflected K hK (S P.val.val)).generator j)
  have hs (P : L) (u : Eisˣ) : Summable (fun i => wt P*block P u i) :=
    (angularLiteralDyadicBlock_summable ℓ (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX u).mul_left _
  have hp (P : L) : r K*aw P.val.val*
      angularMixedReflectedValue ℓ (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
        (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
        (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryIdealGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,wt P*block P u i := by
    rw [angularMixedReflectedValue_eq_dyadic ℓ (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX,
      actual_shape_separation,hprod P.val.val P.val.property]
    simp only [tsum_mul_left]
    dsimp only [wt,block]
    rw [angularCuspDenominatorPhase_eq_psiSix]
    ring
  unfold angularLiteralWholeRow
  simp_rw [hp]
  rw [←Finset.mul_sum,sum_tsum_tsum_finite_middle Finset.univ (fun P u i => wt P*block P u i) (fun P _ u => hs P u)]
  rfl
end
end InverseReflectedPhase
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
