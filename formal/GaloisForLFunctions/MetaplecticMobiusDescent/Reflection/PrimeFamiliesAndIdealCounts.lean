/-
Prime families and ideal counts adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.FixedCuspShapes

/-!
# Prime families and ideal counts

Prime families `InverseReflectedPhase.PrimeFamily` with good generators and separated sectors.
Integral norm balls inject into coordinate squares, giving a uniform ideal-count constant
(`EisensteinLatticeCount`).
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
structure PrimeFamily (ι : Type*) where
  ideal : ι → Ideal Eis
  maximal : ∀ i, (ideal i).IsMaximal
  good : ∀ i, lambda ∉ ideal i

namespace PrimeFamily
variable {ι : Type*} (G : PrimeFamily ι)
instance idealMaximal (i : ι) : (G.ideal i).IsMaximal := G.maximal i

def generator (i : ι) : Eis := primaryIdealPrime (G.ideal i)

lemma generator_ne_zero (i : ι) : G.generator i ≠ 0 := primaryIdealPrime_ne_zero _ (G.good i)
lemma generator_span (i : ι) : Ideal.span {G.generator i} = G.ideal i :=
  (primaryIdealPrime_spec _ (G.generator_ne_zero i)).2.2.1
lemma generator_primary (i : ι) : lambda^2 ∣ G.generator i-1 :=
  (primaryIdealPrime_spec _ (G.generator_ne_zero i)).2.2.2
instance generatorMaximal (i : ι) : (Ideal.span {G.generator i}).IsMaximal :=
  G.generator_span i ▸ G.maximal i
lemma generator_good (i : ι) : lambda ∉ Ideal.span {G.generator i} := by
  rw [G.generator_span]
  exact G.good i

lemma generator_product [Fintype ι] :
    (∏ i, G.generator i) = primaryIdealGenerator (∏ i, G.ideal i) := by
  change _ = primaryIdealGeneratorHom (∏ i, G.ideal i)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  change G.generator i = primaryIdealGenerator (G.ideal i)
  rw [←G.generator_span i,
    primaryIdealGenerator_span _ (G.generator_ne_zero i) (G.generator_primary i)]

lemma generator_product_primary [Fintype ι] : lambda^2 ∣ (∏ i, G.generator i)-1 :=
  primary_finset_product Finset.univ G.generator (fun i _ => G.generator_primary i)

lemma generator_coprime_period (N : Eis)
    (hN : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) (i : ι) :
    IsCoprime N (G.generator i) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [G.generator_span]
  exact hN i

lemma generator_product_coprime_period [Fintype ι] (N c : Eis) (hc : c ∣ N)
    (hN : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) :
    IsCoprime (∏ i, G.generator i) (N*c) := by
  have hh : IsCoprime N (∏ i, G.generator i) :=
    IsCoprime.prod_right (fun i _ => G.generator_coprime_period N hN i)
  exact hh.symm.mul_right (hh.symm.of_isCoprime_of_dvd_right hc)

theorem exists_controlled [Fintype ι] (N a c : Eis) (mode : Bool)
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then lambda^2 ∣ a-1 else lambda^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : Pairwise (Function.onFun IsCoprime G.ideal))
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) :
    Nonempty (ControlledStratumArithmetic G.generator N a c mode) := by
  apply exists_controlledStratumArithmetic G.generator G.generator_ne_zero
  · intro i k hik
    simpa only [G.generator_span] using hcop hik
  · exact G.generator_primary
  · exact hc
  · exact hN
  · exact hbase
  · exact hac
  · exact G.generator_coprime_period N hNp

end PrimeFamily

end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped BigOperators Classical
open NormalizedReflection
noncomputable section

lemma scalar_inverse_pair (a b c d : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : c*a*b=d) : a⁻¹*b⁻¹ = d⁻¹*c := by
  field_simp
  linear_combination -h

theorem marked_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (B z : F)
    (he : B*z*(σ : F)*(ε : F) = -1) :
    ((χ⁻¹)^2) σ * phase χ ψ 0 ε =
      (-tau χ ψ 2)*(χ (-1))⁻¹^2*(χ B)^2*(χ z)^2 := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  simp only [phase, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte,
    MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv']
  calc
    _ = (-tau χ ψ 2)*((χ σ)⁻¹*(χ ε)⁻¹)^2 := by ring
    _ = _ := by rw [hi]; ring

theorem residual_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A B z : F)
    (hsigma : (σ : F) = A*z) (he : B*z*(σ : F)*(ε : F) = -1) :
    ((χ⁻¹)^2) σ * phase χ ψ 1 ε =
      (tau χ (ψ.mulShift (-1)) 1*tau χ ψ 3)*
        (χ (-1))⁻¹^3*(χ A)*(χ B)^3*(χ z)^4 := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  have hsig : χ (σ : F) = χ A*χ z := by rw [hsigma,map_mul]
  simp only [phase, show (1 : ℕ) ≠ 4 by decide, show (1 : ℕ) ≠ 0 by decide,
    ↓reduceIte, show (1 : ℕ)+2 = 3 by decide,
    MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv']
  have hid : (χ σ)⁻¹^2*(χ ε)⁻¹^3 = (χ σ)*((χ σ)⁻¹*(χ ε)⁻¹)^3 := by
    field_simp
  calc
    _ = (tau χ (ψ.mulShift (-1)) 1*tau χ ψ 3)*((χ σ)⁻¹^2*(χ ε)⁻¹^3) := by ring
    _ = _ := by rw [hid,hi,hsig]; ring

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped BigOperators Classical
open Eisenstein CompletedGauss 
open NormalizedReflection 
noncomputable section
noncomputable local instance phaseField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance phaseFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def markedPrimeScalar (p c0 : Eis) [hP : (Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : lambda ∉ Ideal.span {p}) : ℂ :=
  let χ := complexSexticChar (Ideal.span {p}) hg
  (-tau χ (residueTraceQuotientChar 1 p hp) 2)*(χ (-1))⁻¹^2*
    (χ (Ideal.Quotient.mk _ (traceLambda^3*c0)))^2

def residualPrimeScalar (p c0 : Eis) [hP : (Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : lambda ∉ Ideal.span {p}) : ℂ :=
  let χ := complexSexticChar (Ideal.span {p}) hg
  (tau χ ((residueTraceQuotientChar 1 p hp).mulShift (-1)) 1*tau χ (residueTraceQuotientChar 1 p hp) 3)*
    (χ (-1))⁻¹^3*(χ (Ideal.Quotient.mk _ (traceLambda^2*c0)))*
      (χ (Ideal.Quotient.mk _ (traceLambda^3*c0)))^3

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

theorem controlled_marked_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i : ι) :
    (((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (complexSexticChar (Ideal.span {p i}) (hg i)) (residueTraceQuotientChar 1 (p i) (hp i)) 0 (D.epsilon i) =
        markedPrimeScalar (p i) c0 (hp i) (hg i)*
          ∏ k ∈ Finset.univ.erase i, FirstPassCubeLabels.crossSymbol p hg i k ^ 2 := by
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (traceLambda^3*c0)*
      Ideal.Quotient.mk _ (cuspPrimeCofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  rw [marked_local_phase _ _ _ _ _ _ he]
  change _ = _
  simp only [markedPrimeScalar, cuspPrimeCofactor, map_prod, Finset.prod_pow,
    FirstPassCubeLabels.crossSymbol]

theorem controlled_residual_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i : ι) :
    (((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (complexSexticChar (Ideal.span {p i}) (hg i)) (residueTraceQuotientChar 1 (p i) (hp i)) 1 (D.epsilon i) =
        residualPrimeScalar (p i) c0 (hp i) (hg i)*
          ∏ k ∈ Finset.univ.erase i, FirstPassCubeLabels.crossSymbol p hg i k ^ 4 := by
  have hs : (D.sigma i : Eis ⧸ Ideal.span {p i}) =
      Ideal.Quotient.mk _ (traceLambda^2*c0)*Ideal.Quotient.mk _ (cuspPrimeCofactor p i) := by
    simpa only [map_mul] using D.sigma_value i
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (traceLambda^3*c0)*
      Ideal.Quotient.mk _ (cuspPrimeCofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  rw [residual_local_phase _ _ _ _ _ _ _ hs he]
  simp only [residualPrimeScalar, cuspPrimeCofactor, map_prod, Finset.prod_pow,
    FirstPassCubeLabels.crossSymbol]

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein  CompletedGauss
open NormalizedReflection 
noncomputable section

lemma scalar_phase_power (a b : ℂ) (ha : a ≠ 0) (j : ℕ) :
    a⁻¹^2*b⁻¹^(j+2) = a^j*(a⁻¹*b⁻¹)^(j+2) := by
  symm
  calc
    _ = (a^j*(a⁻¹)^j)*(a⁻¹)^2*(b⁻¹)^(j+2) := by rw [mul_pow,pow_add]; ring
    _ = _ := by rw [← mul_pow,mul_inv_cancel₀ ha,one_pow,one_mul]

theorem general_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A B z : F)
    (hsigma : (σ : F) = A*z) (he : B*z*(σ : F)*(ε : F) = -1)
    (j : ℕ) (hj0 : j ≠ 0) (hj4 : j ≠ 4) :
    ((χ⁻¹)^2) σ * phase χ ψ j ε =
      (tau χ (ψ.mulShift (-1)) j*tau χ ψ (j+2)) *
        (χ (-1))⁻¹^(j+2)*(χ A)^j*(χ B)^(j+2)*(χ z)^(2*j+2) := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  have hsig : χ (σ : F) = χ A*χ z := by rw [hsigma,map_mul]
  simp only [phase,hj4,hj0,↓reduceIte,MulChar.pow_apply_coe,MulChar.inv_apply_eq_inv']
  calc
    _ = (tau χ (ψ.mulShift (-1)) j*tau χ ψ (j+2))*((χ σ)⁻¹^2*(χ ε)⁻¹^(j+2)) := by ring
    _ = _ := by
      rw [scalar_phase_power _ _ hs j,hi,hsig]
      simp only [mul_pow,pow_add,show 2*j=j+j by omega]
      ring

theorem exceptional_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A z : F)
    (hsigma : (σ : F) = A*z) :
    ((χ⁻¹)^2) σ * phase χ ψ 4 ε =
      (tau χ (ψ.mulShift (-1)) 4*(χ A)⁻¹^2)*(χ z)⁻¹^2 := by
  simp only [phase,↓reduceIte,hsigma,map_mul,
    ]
  simp only [MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv']
  ring

noncomputable local instance frozenField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance frozenFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def frozenPrimeScalar (p c : Eis) [(Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : lambda ∉ Ideal.span {p}) (j : ℕ) : ℂ :=
  let χ := complexSexticChar (Ideal.span {p}) hg
  if j=4 then tau χ ((residueTraceQuotientChar 1 p hp).mulShift (-1)) 4*
      (χ (Ideal.Quotient.mk _ (traceLambda^2*c)))⁻¹^2
  else if j=0 then markedPrimeScalar p c hp hg
  else (tau χ ((residueTraceQuotientChar 1 p hp).mulShift (-1)) j*tau χ (residueTraceQuotientChar 1 p hp) (j+2)) *
    (χ (-1))⁻¹^(j+2)*(χ (Ideal.Quotient.mk _ (traceLambda^2*c)))^j*
    (χ (Ideal.Quotient.mk _ (traceLambda^3*c)))^(j+2)

def frozenCofactorCharacter (P : Ideal Eis) [P.IsMaximal]
    (hg : lambda ∉ P) (j : ℕ) : Eis →* ℂ :=
  (if j=4 then ((complexSexticChar P hg)⁻¹)^2 else (complexSexticChar P hg)^(2*j+2)).toMonoidHom.comp
    (Ideal.Quotient.mk P).toMonoidHom

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

theorem controlled_frozen_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i : ι) (j : ℕ) :
    (((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (complexSexticChar (Ideal.span {p i}) (hg i)) (residueTraceQuotientChar 1 (p i) (hp i)) j (D.epsilon i) =
    frozenPrimeScalar (p i) c (hp i) (hg i) j *
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (cuspPrimeCofactor p i) := by
  have hs : (D.sigma i : Eis ⧸ Ideal.span {p i}) =
      Ideal.Quotient.mk _ (traceLambda^2*c)*Ideal.Quotient.mk _ (cuspPrimeCofactor p i) := by
    simpa only [map_mul] using D.sigma_value i
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (traceLambda^3*c)*
      Ideal.Quotient.mk _ (cuspPrimeCofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  by_cases hj4 : j=4
  · subst j
    rw [exceptional_local_phase _ _ _ _ _ _ hs]
    simp only [frozenPrimeScalar,frozenCofactorCharacter,↓reduceIte,MonoidHom.comp_apply,
      RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv']
    rfl
  · by_cases hj0 : j=0
    · subst j
      rw [marked_local_phase _ _ _ _ _ _ he]
      simp [frozenPrimeScalar,frozenCofactorCharacter,markedPrimeScalar,
        MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0)]
    · rw [general_local_phase _ _ _ _ _ _ _ hs he j hj0 hj4]
      simp only [frozenPrimeScalar,frozenCofactorCharacter,hj4,hj0,↓reduceIte,
        MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,
        MulChar.coe_toMonoidHom,MulChar.pow_apply' _ (by omega : 2*j+2 ≠ 0)]
      rfl

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped BigOperators Classical
noncomputable section

theorem ordered_cross_partition_on {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (A B U : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = U) :
    (∏ i ∈ U, ((∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ a * x k i ^ b) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ A.erase i, x i k ^ a) * (∏ k ∈ B, x i k ^ a) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : U.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, if_pos hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ B.erase i, x i k ^ b) * (∏ k ∈ A, x i k ^ b) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : U.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, if_neg hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ U.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ a) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ U.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ b) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ U.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ U.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB]
      rw [Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

theorem ordered_cross_frozen_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F)
    (hu : (R ∪ P) ∪ F = Finset.univ) :
    (∏ i ∈ R ∪ P, (∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ R then a else b))*l i) =
      (∏ i ∈ R, (∏ k ∈ R.erase i, x i k^a)*(l i*∏ k ∈ F, x i k^a)) *
      (∏ i ∈ P, (∏ k ∈ P.erase i, x i k^b)*(l i*∏ k ∈ F, x i k^b)) *
      (∏ i ∈ R, ∏ k ∈ P, x i k^a*x k i^b) := by
  let ll := fun i => l i*∏ k ∈ F, x i k ^ (if i ∈ R then a else b)
  have hx : (∏ i ∈ R ∪ P, (∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ R then a else b))*l i) =
      ∏ i ∈ R ∪ P, (∏ k ∈ (R ∪ P).erase i,
        x i k ^ (if i ∈ R then a else b))*ll i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ F := fun hf => Finset.disjoint_left.mp hF hi hf
    have he : Finset.univ.erase i = (R ∪ P).erase i ∪ F := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk,or_assoc]
    rw [he,Finset.prod_union (hF.mono_left (Finset.erase_subset _ _))]
    dsimp [ll]
    ring
  rw [hx,ordered_cross_partition_on x ll a b R P (R ∪ P) hRP rfl]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    simp [ll,hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ R := fun hr => Finset.disjoint_left.mp hRP hr hi
    simp [ll,hn]

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein  
noncomputable section

theorem separate_product_congruence {A : Type*} [CommRing A]
    (M f r r₀ P P₀ : A) (hr : M^2 ∣ r-r₀) (hP : M^2 ∣ P-P₀) :
    M^2 ∣ f*r*P-f*r₀*P₀ := by
  have h := dvd_add (dvd_mul_of_dvd_left hr P) (dvd_mul_of_dvd_right hP r₀)
  convert dvd_mul_of_dvd_right h f using 1 ; ring

def separateSector (M r P : Eis) :
    (Eis ⧸ Ideal.span {M^2}) × (Eis ⧸ Ideal.span {M^2}) :=
  (Ideal.Quotient.mk _ r, Ideal.Quotient.mk _ P)

theorem separateSector_product (M f r r₀ P P₀ : Eis)
    (h : separateSector M r P = separateSector M r₀ P₀) :
    M^2 ∣ f*r*P-f*r₀*P₀ := by
  apply separate_product_congruence
  · exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (congrArg Prod.fst h))
  · exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (congrArg Prod.snd h))

theorem controlled_bad_phase_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} {p₀ : κ → Eis} {N a c : Eis} {mode : Bool}
    (D : ControlledStratumArithmetic p N a c mode)
    (D₀ : ControlledStratumArithmetic p₀ N a c mode) (hc : c ≠ 0)
    (hbad : traceLambda^3*c ∣ N)
    (hr : N ∣ (∏ i, p i)-(∏ i, p₀ i))
    (hd : N ∣ D.matrix (fun _ => 1) 1 1 - D₀.matrix (fun _ => 1) 1 1) :
    cuspBadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U =
      cuspBadPhase c hc (D₀.matrix (fun _ => 1) 1 1) D₀.U := by
  have hu : traceLambda^3*c ∣ D.U*(∏ i, p i)-1 := by
    refine ⟨-D.w, ?_⟩
    linear_combination D.bezout
  have hu₀ : traceLambda^3*c ∣ D₀.U*(∏ i, p₀ i)-1 := by
    refine ⟨-D₀.w, ?_⟩
    linear_combination D₀.bezout
  have hcop : IsCoprime (traceLambda^3*c) (∏ i, p i) := by
    refine ⟨D.w,D.U,?_⟩
    linear_combination D.bezout
  have he := inverse_weight_residue_congr
    (traceLambda^3*c) (∏ i, p i) (∏ i, p₀ i) D.U D₀.U
    (D.matrix (fun _ => 1) 1 1) (D₀.matrix (fun _ => 1) 1 1)
    hcop (hbad.trans hr) hu hu₀ (hbad.trans hd)
  rw [cuspBadPhase_as_fixed_residue, cuspBadPhase_as_fixed_residue]
  congr 1
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr he)

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein  CompletedGauss 
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {p : ι → Eis} {p₀ : κ → Eis} {N a c : Eis} {mode : Bool}

theorem controlled_fixedFactor_eq
    (D : ControlledStratumArithmetic p N a c mode)
    (D₀ : ControlledStratumArithmetic p₀ N a c mode)
    (hN : (9:Eis)*c ∣ N)
    (hr : lambda^2 ∣ (∏ i, p i)-1) (hr₀ : lambda^2 ∣ (∏ i, p₀ i)-1)
    (hbase : if mode then lambda^2 ∣ a-1 else lambda^2 ∣ c-1)
    (ha : N ∣ D.matrix (fun _ => 1) 0 0 - D₀.matrix (fun _ => 1) 0 0)
    (hb : N ∣ D.matrix (fun _ => 1) 0 1 - D₀.matrix (fun _ => 1) 0 1) :
    D.fixedFactor = D₀.fixedFactor := by
  have h9N : (9:Eis) ∣ N := (dvd_mul_right 9 c).trans hN
  have hcN : c ∣ N := (dvd_mul_left c 9).trans hN
  have h3N : (3:Eis) ∣ N := (show (3:Eis) ∣ 9 from ⟨3,by norm_num⟩).trans h9N
  cases mode
  · exact congrArg ringComplex (cuspSymbol_weyl_fixed_congr N c _ _ hcN ha)
  · apply congrArg ringComplex
    exact cuspSymbol_ramified_fixed_congr N 1 c _ _ _ _ h9N (one_dvd _) hcN
      (D.numerator_primary h3N hr hbase _) (D₀.numerator_primary h3N hr₀ hbase _)
      (lowerCusp_relative_primary _ c (D.ramified_relative h3N hr hbase c (by simp) _))
      (lowerCusp_relative_primary _ c (D₀.ramified_relative h3N hr₀ hbase c (by simp) _)) ha hb

theorem controlled_static_array_eq
    (D : ControlledStratumArithmetic p N a c mode)
    (D₀ : ControlledStratumArithmetic p₀ N a c mode) (hc : c ≠ 0)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hbad : traceLambda^3*c ∣ N)
    (hr : N ∣ (∏ i, p i)-(∏ i, p₀ i))
    (hd : N ∣ D.matrix (fun _ => 1) 1 1 - D₀.matrix (fun _ => 1) 1 1)
    (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) :
    fixedCuspArrayWithPhase s.index u
      (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1)*D.U))
        (s.modelDualNumerator u) u) m I J =
    fixedCuspArrayWithPhase s.index u
      (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D₀.matrix (fun _ => 1) 1 1)*D₀.U))
        (s.modelDualNumerator u) u) m I J := by
  rw [s.fixedCuspArrayWithPhase_reflectionStaticPhase, s.fixedCuspArrayWithPhase_reflectionStaticPhase]
  have he := congrFun (controlled_bad_phase_eq D D₀ hc hbad hr hd) (s.modelDualNumerator u m I J)
  rw [cuspBadPhase_as_fixed_residue,cuspBadPhase_as_fixed_residue] at he
  rw [he]

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators MatrixGroups
open Eisenstein    CompletedGauss
noncomputable section

theorem simultaneous_controlled_matrices_dependent {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (hc : c ≠ 0) (h9N : (9:Eis) ∣ N) (hcN : c ∣ N)
    (hprimary : ∀ x, lambda^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then lambda^2 ∣ a-1 else lambda^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i)) :
    ∃ mat : ∀ x, (∀ i, (Eis ⧸ Ideal.span {p x i})ˣ) → SL(2,Eis),
      (∀ x v, mat x v 0 0 = (D x).matrix v 0 0) ∧
      (∀ x v, mat x v 1 0 = c*∏ i, p x i) ∧
      (∀ x v, if mode then (9:Eis) ∣ mat x v 0 1 ∧ (3:Eis) ∣ mat x v 1 1-1
        else (3:Eis) ∣ mat x v 0 1+1 ∧ (9:Eis) ∣ mat x v 1 1) ∧
      ∀ x y v w, sector x = sector y → ∀ i j, N ∣ mat x v i j-mat y w i j := by
  have h3N : (3:Eis)∣N := (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N
  have hlocal (q:Q) : ∃ C:SL(2,Eis), ∀ x, sector x=q →
      ∀ v, ∃ M:SL(2,Eis),
        M 0 0=(D x).matrix v 0 0 ∧ M 1 0=c*∏i,p x i ∧
        (if mode then (9:Eis)∣M 0 1 ∧ (3:Eis)∣M 1 1-1
          else (3:Eis)∣M 0 1+1 ∧ (9:Eis)∣M 1 1) ∧
        ∀ i j, N∣M i j-C i j := by
    by_cases hq:∃x,sector x=q
    · obtain ⟨y,hy⟩:=hq
      let C := (D y).matrix (fun _=>1)
      refine ⟨C,?_⟩
      intro x hx v
      have hrr : N∣(∏i,p x i)-(∏i,p y i) :=
        (dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (hsector x y (hx.trans hy.symm))
      have ha : N∣(D x).matrix v 0 0-C 0 0 := by
        have h1 := (D x).numerator_congruence v
        have h0 := (D y).numerator_congruence (fun _=>1)
        convert dvd_sub (dvd_add h1 (dvd_mul_of_dvd_right hrr a)) h0 using 1 <;> ring
      have hden : N∣(c*∏i,p x i)-C 1 0 := by
        change N∣(c*∏i,p x i)-(D y).matrix (fun _=>1) 1 0
        rw [(D y).denominator]
        convert dvd_mul_of_dvd_right hrr c using 1 <;> ring
      have hac : IsCoprime ((D x).matrix v 0 0) (c*∏i,p x i) :=
        ⟨(D x).matrix v 1 1,-(D x).matrix v 0 1,by
          linear_combination (D x).determinant v⟩
      obtain ⟨M,hm0,hm1,hm⟩ := primitiveColumn_congruent_completion C
        ((D x).matrix v 0 0) (c*∏i,p x i) N hac ha hden
      refine ⟨M,hm0,hm1,?_,hm⟩
      have hcnd := (D y).conditions (fun _=>1)
      cases mode
      · simp only [Bool.false_eq_true,↓reduceIte] at hcnd ⊢
        constructor
        · convert dvd_add (h3N.trans (hm 0 1)) hcnd.1 using 1 <;> ring
        · convert dvd_add (h9N.trans (hm 1 1)) hcnd.2 using 1 <;> ring
      · simp only [↓reduceIte] at hcnd ⊢
        constructor
        · convert dvd_add (h9N.trans (hm 0 1)) hcnd.1 using 1 <;> ring
        · convert dvd_add (h3N.trans (hm 1 1)) hcnd.2 using 1 <;> ring
    · exact ⟨1,fun x hx=>False.elim (hq ⟨x,hx⟩)⟩
  choose C hC using hlocal
  have hex (x:α) (v:∀i,(Eis⧸Ideal.span {p x i})ˣ) := hC (sector x) x rfl v
  choose mat ha hd hcond hm using hex
  refine ⟨mat,ha,hd,hcond,?_⟩
  intro x y v w hxy i j
  have h1 := hm x v i j
  have h0 := hm y w i j
  rw [hxy] at h1
  convert dvd_sub h1 h0 using 1 <;> ring


theorem exists_sector_controlled_arithmetic_dependent {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (hc : c ≠ 0) (h9N : (9:Eis) ∣ N) (hcN : c ∣ N)
    (hprimary : ∀ x, lambda^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then lambda^2 ∣ a-1 else lambda^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i)) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧
      (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧
      (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∀ x y v w, sector x = sector y → ∀ i j,
        N ∣ (E x).matrix v i j-(E y).matrix w i j := by
  obtain ⟨mat,ha,hr,hcond,hfixed⟩ := simultaneous_controlled_matrices_dependent
    p N a c mode D hc h9N hcN hprimary hbase hcop sector hsector
  let E : ∀ x, ControlledStratumArithmetic (p x) N a c mode := fun x =>
    { D x with
      matrix := mat x
      numerator := fun v => (ha x v).trans ((D x).numerator v)
      denominator := hr x
      matrix_fixed := fun v i j => hfixed x x v (fun _ => 1) rfl i j
      conditions := hcond x }
  exact ⟨E,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,hfixed⟩

theorem exists_sector_templates {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hprimary : ∀ x, lambda^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then lambda^2 ∣ a-1 else lambda^2 ∣ c-1)
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i))
    (hmatrix : ∀ x y, sector x = sector y → ∀ i j,
      N ∣ (D x).matrix (fun _ => 1) i j-(D y).matrix (fun _ => 1) i j) :
    ∃ (κ : Q → ℂ) (β : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
      (∀ x, (D x).fixedFactor = κ (sector x)) ∧
      ∀ x u m n b,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c hc
            (Ideal.Quotient.mk _ (-((D x).matrix (fun _ => 1) 1 1)*(D x).U))
            (s.modelDualNumerator u) u) m n b = β (sector x) u m n b := by
  have hbad : traceLambda^3*c ∣ N := by
    apply (show traceLambda^3*c ∣ (9:Eis)*c from ?_).trans hN
    refine ⟨traceLambda,?_⟩
    rw [← traceLambda_pow_four]
    ring
  let A := fun x (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) =>
    fixedCuspArrayWithPhase s.index u
      (s.reflectionStaticPhase c hc
        (Ideal.Quotient.mk _ (-((D x).matrix (fun _ => 1) 1 1)*(D x).U))
        (s.modelDualNumerator u) u) m n b
  have hf : (fun x => (D x).fixedFactor).FactorsThrough sector := by
    intro x y hxy
    exact controlled_fixedFactor_eq (D x) (D y) hN (hprimary x) (hprimary y) hbase
      (hmatrix x y hxy 0 0) (hmatrix x y hxy 0 1)
  have ha : A.FactorsThrough sector := by
    intro x y hxy
    funext u m n b
    exact controlled_static_array_eq (D x) (D y) hc s hbad
      ((dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x y hxy))
      (hmatrix x y hxy 1 1) u m n b
  obtain ⟨κ,hκ⟩ := (Function.factorsThrough_iff _).mp hf
  obtain ⟨β,hβ⟩ := (Function.factorsThrough_iff A).mp ha
  refine ⟨κ,β,fun x => congrFun hκ x,?_⟩
  intro x u m n b
  exact congrFun (congrFun (congrFun (congrFun (congrFun hβ x) u) m) n) b

theorem exists_separate_ray_templates {α : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hprimary : ∀ x, lambda^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then lambda^2 ∣ a-1 else lambda^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (f : Eis) (r P : α → Eis) (hprod : ∀ x, (∏ i, p x i) = f*r x*P x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧
      (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧
      (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∃ (κ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x, (E x).fixedFactor = κ (separateSector N (r x) (P x))) ∧
        ∀ x u m n b,
          fixedCuspArrayWithPhase s.index u
            (s.reflectionStaticPhase c hc
              (Ideal.Quotient.mk _ (-((E x).matrix (fun _ => 1) 1 1)*(E x).U))
              (s.modelDualNumerator u) u) m n b = β (separateSector N (r x) (P x)) u m n b := by
  let sector := fun x => separateSector N (r x) (P x)
  have hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i) := by
    intro x y hxy
    rw [hprod x,hprod y]
    exact separateSector_product N f (r x) (r y) (P x) (P y) hxy
  obtain ⟨E,hlift,hU,hσ,hε,hmat⟩ := exists_sector_controlled_arithmetic_dependent p N a c mode D
    hc ((dvd_mul_right 9 c).trans hN) ((dvd_mul_left c 9).trans hN)
    hprimary hbase hcop sector hsector
  refine ⟨E,hlift,hU,hσ,hε,?_⟩
  exact exists_sector_templates p N a c mode E s hc hN hprimary hbase sector hsector
    (fun x y hxy => hmat x y (fun _ => 1) (fun _ => 1) hxy)

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein
open scoped BigOperators Classical
namespace EisensteinLatticeCount
def q (x : ℤ × ℤ) : ℤ := x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

theorem coordinate_squares (a b D : ℤ) (hD : 0 ≤ D)
    (h : a ^ 2 - a * b + b ^ 2 ≤ D) :
    a ^ 2 ≤ 2 * D ∧ b ^ 2 ≤ 2 * D := by
  constructor <;> nlinarith only [h, hD, sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b)]

theorem finite_lattice_count (S : Finset (ℤ × ℤ)) (D R : ℕ)
    (hR : 2 * D < R ^ 2)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ (2 * R + 1) ^ 2 := by
  let I : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)
  have hbox : S ⊆ I.product I := by
    intro x hx
    rcases x with ⟨a, b⟩
    have hD : (0 : ℤ) ≤ D := by positivity
    obtain ⟨ha, hb⟩ := coordinate_squares a b D hD (hS (a, b) hx)
    have hR' : 2 * (D : ℤ) < (R : ℤ) ^ 2 := by exact_mod_cast hR
    have hRnonneg : (0 : ℤ) ≤ R := by positivity
    apply Finset.mem_product.mpr
    constructor <;> simp only [I, Finset.mem_Icc] <;> constructor <;>
      nlinarith only [ha, hb, hR', hRnonneg, sq_nonneg (a - R),
      sq_nonneg (a + R), sq_nonneg (b - R), sq_nonneg (b + R)]
  have hI : I.card = 2 * R + 1 := by
    dsimp [I]
    rw [Int.card_Icc]
    have hcast : (R : ℤ) + 1 + (R : ℤ) = ((R + 1 + R : ℕ) : ℤ) := by
      push_cast
      ring
    rw [sub_neg_eq_add, hcast, Int.toNat_natCast]
    ring
  calc
    S.card ≤ (I.product I).card := Finset.card_le_card hbox
    _ = I.card * I.card := Finset.card_product _ _
    _ = (2 * R + 1) ^ 2 := by rw [hI]; ring

theorem finite_lattice_count_linear (S : Finset (ℤ × ℤ)) (D : ℕ)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ 64 * (D + 1) := by
  have hR : 2 * D < (Nat.sqrt (2 * D) + 1) ^ 2 := by
    exact Nat.lt_succ_sqrt' _
  have hcount := finite_lattice_count S D (Nat.sqrt (2 * D) + 1) hR hS
  have hsquare : (Nat.sqrt (2 * D)) ^ 2 ≤ 2 * D := Nat.sqrt_le' _
  have hroot : Nat.sqrt (2 * D) ≤ 2 * D := Nat.sqrt_le_self _
  nlinarith only [hcount, hsquare, hroot]

/-- An integral norm ball injects into a coordinate square. -/
theorem finite_norm_ball_card (S : Finset O) (D : ℕ)
    (hS : ∀ x ∈ S, ‖ringComplex x‖ ^ 2 ≤ D) :
    S.card ≤ 64 * (D + 1) := by
  rw [←Finset.card_image_of_injective S Coordinates.coordinateEquiv.injective]
  apply finite_lattice_count_linear
  intro v hv
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
  have hn := Coordinates.complex_norm_eval_sq (Coordinates.coords x).1 (Coordinates.coords x).2
  rw [Coordinates.eval_coords] at hn
  have he : ((q (Coordinates.coords x) : ℤ) : ℝ) = ‖ringComplex x‖ ^ 2 := by
    simpa only [q, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow] using hn.symm
  change q (Coordinates.coords x) ≤ D
  exact_mod_cast he.trans_le (hS x hx)

theorem finite_ideal_card (S : Finset (Ideal O)) (D : ℕ)
    (hS : ∀ I ∈ S, Ideal.absNorm I ≤ D) : S.card ≤ 64 * (D+1) := by
  rw [←Finset.card_image_of_injective S cubicIdealGenerator_injective]
  apply finite_norm_ball_card
  intro z hz
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hz
  rw [ringComplex_norm_sq_eq_absNorm_span,span_cubicIdealGenerator]
  exact_mod_cast hS I hI

/-- A uniform explicit ideal-count constant for real norm intervals. -/
theorem finite_ideal_count_real (S : Finset (Ideal O)) (H : ℝ) (hH : 1 ≤ H)
    (_hpos : ∀ I ∈ S, I ≠ ⊥)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 128*H := by
  have hc := finite_ideal_card S ⌊H⌋₊ (fun I hI => Nat.le_floor (hN I hI))
  have hf : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le (by linarith only [hH])
  have hr : (S.card : ℝ) ≤ 64*((⌊H⌋₊ : ℝ)+1) := by exact_mod_cast hc
  linarith only [hr,hf,hH]

end EisensteinLatticeCount
end

noncomputable section
open Eisenstein
open scoped BigOperators Classical
namespace EisensteinLatticeCount

def unitCoordinates : Finset (ℤ × ℤ) :=
  {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)}

theorem q_eq_one_iff_unitCoordinates (z : ℤ × ℤ) : q z = 1 ↔ z ∈ unitCoordinates := by
  rcases z with ⟨a, b⟩
  constructor
  · intro h
    have hs := coordinate_squares a b 1 (by norm_num) (le_of_eq h)
    have ha : -1 ≤ a ∧ a ≤ 1 := by
      constructor <;> nlinarith only [hs.1, sq_nonneg (a-1), sq_nonneg (a+1)]
    have hb : -1 ≤ b ∧ b ≤ 1 := by
      constructor <;> nlinarith only [hs.2, sq_nonneg (b-1), sq_nonneg (b+1)]
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    interval_cases a <;> interval_cases b <;> norm_num [q, unitCoordinates] at *
  · intro h
    simp only [unitCoordinates, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h <;> rw [h] <;> norm_num [q]

theorem unit_coordinate_mem (u : Oˣ) : Coordinates.coords u.val ∈ unitCoordinates := by
  apply (q_eq_one_iff_unitCoordinates _).mp
  have he := ramifiedElement_absNorm u 0
  simp only [pow_zero, mul_one] at he
  have hn := Coordinates.complex_norm_eval_sq
    (Coordinates.coords u.val).1 (Coordinates.coords u.val).2
  rw [Coordinates.eval_coords, ringComplex_norm_sq_eq_absNorm_span, he, Nat.cast_one] at hn
  exact_mod_cast hn.symm

/-- Each unit has one of six integral coordinate pairs. -/
theorem card_units_le_six [Fintype Oˣ] : Fintype.card Oˣ ≤ 6 := by
  let f : Oˣ → unitCoordinates := fun u => ⟨Coordinates.coords u.val, unit_coordinate_mem u⟩
  have hf : Function.Injective f := by
    intro u v h
    apply Units.ext
    exact Coordinates.coordinateEquiv.injective (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hf
  norm_num [Fintype.card_coe, unitCoordinates] at hc
  exact hc

end EisensteinLatticeCount
end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
