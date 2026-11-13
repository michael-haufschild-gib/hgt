/-
Central repeated products adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.PrimeRows.DyadicRowBands

/-!
# Central repeated products

Row costs of central repeated products, fixed radical conductor constants and central
exponents; raw twisted conductors of ray character families; repeated subsets, phase slots and
phase bins.
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
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeRowRadicalConductor
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open UniqueFactorizationMonoid
local notation "O" => Eisenstein.O

theorem canonicalPrimePower_descent (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) {c : ℕ} (hc : 1 ≤ c) (x : O ⧸ P ^ c) :
    CenteredMomentCanonical.canonicalPrimePowerCharacter P hg hc x =
      (complexSexticChar P hg ^ c)
        (CenteredMomentCorrelation.primePowerReduction P hc x) := rfl

theorem idealRowHom_congr_radical (I : Ideal O) (x y : O)
    (hxy : x-y ∈ I.radical) : idealRowHom x I = idealRowHom y I := by
  by_cases hI : I = 0
  · subst I
    simp only [map_zero]
  change (if I=0 then 0 else _) = (if I=0 then 0 else _)
  rw [if_neg hI, if_neg hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  have hp := Ideal.isPrime_of_prime (prime_of_normalized_factor P hP)
  have hle : I.radical ≤ P := hp.radical_le_iff.mpr
    (((Ideal.mem_normalizedFactors_iff hI).mp hP).2)
  unfold localRowValue
  split_ifs with hg
  · let : P.IsMaximal := hg.1
    congr 1
    exact Ideal.Quotient.eq.mpr (hle hxy)
  · rfl

theorem radical_ne_bot (I : Ideal O) (hI : I ≠ ⊥) : I.radical ≠ ⊥ := by
  intro h
  exact hI (bot_unique (h ▸ I.le_radical))

theorem movingNumeratorRow_radical_periodic (r : O)
    (hr : quadraticSupported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {r}).radical
      (movingNumeratorRow r hr) := idealRowHom_congr_radical _

theorem actualPeriodicRow_radical_periodic (Ψ : O →* ℂ) (Q : Ideal O)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (m : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : quadraticSupported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo
      (Q * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical)
      (actualPeriodicRow Ψ m u a b r hr) := by
  intro x y hxy
  have hQ : x-y ∈ Q := Ideal.mul_le_right (Ideal.mul_le_right (Ideal.mul_le_right hxy))
  have hm : x-y ∈ Ideal.span {m} := Ideal.mul_le_left (Ideal.mul_le_right (Ideal.mul_le_right hxy))
  have h72 : x-y ∈ Ideal.span {(72 : O)} := Ideal.mul_le_left (Ideal.mul_le_right hxy)
  have hrxy : x-y ∈ (Ideal.span {r}).radical := Ideal.mul_le_left hxy
  change ((Ψ x * coprimalityMask m x) * numeratorBadTwist u a b r hr x) *
      movingNumeratorRow r hr x =
    ((Ψ y * coprimalityMask m y) * numeratorBadTwist u a b r hr y) *
      movingNumeratorRow r hr y
  rw [hΨ x y hQ, coprimalityMask_periodic m x y hm,
    numeratorBadTwist_periodic u a b r hr x y h72,
    movingNumeratorRow_radical_periodic r hr x y hrxy]

theorem rowTwist_radical_periodic (η : Character) (m f z : O)
    (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : quadraticSupported (Ideal.span {r}))
    (hpr : lambda ^ 2 ∣ r-1) (hx : f^4*z = (u : O)*lambda^a*(2 : O)^b*r) :
    CanonicalCoefficientClass.FactorsModulo
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical)
      (rowTwist (elementHom η) m f z) := by
  refine periodic_of_primary _ ?_ _ (actualPeriodicRow (elementHom η) m u a b r hr)
    (actualPeriodicRow_radical_periodic _ _ (elementHom_periodic η) _ _ _ _ _ hr)
    (rowTwist_unit_mul η m f z) ?_ ?_
  · have hd3 : lambda ^ 2 ∣ (3 : O) := Eisenstein.lambda_sq_dvd_three
    have hd72 : lambda ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact (Ideal.mul_le_right.trans Ideal.mul_le_left).trans
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hd72))
  · intro n hn
    apply rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2
    intro hs
    exact ((CanonicalRowCompletion.supported_span_iff n).mp hs).1 hn
  · exact rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx

theorem rowTwist_nonzero_radical_unit (η : Character) (m f z n : O)
    (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*lambda^a*(2 : O)^b*r)
    (hn : rowTwist (elementHom η) m f z n ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical) n) := by
  have hu := rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx hn
  have hle : η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r} ≤
      η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical :=
    Ideal.mul_mono_right (Ideal.span {r}).le_radical
  exact hu.map (Ideal.Quotient.factor hle)

theorem exists_row_character_radical (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character,
      χ.modulus.absNorm ≤ η.modulus.absNorm * (Ideal.span {m}).absNorm *
        (Ideal.span {(72 : O)}).absNorm * (Ideal.span {f^4*z}).radical.absNorm ∧
      ∀ n : O, elementCoeff χ n = rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, _, _, _, _⟩ :=
    exists_actual_periodic_row (elementHom η) η.modulus η.modulus_ne_bot
      (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  change f^4*z = (u : O)*lambda^a*(2 : O)^b*r at hx
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical
  have hM : M ≠ ⊥ := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot
      (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    (radical_ne_bot _ (primaryIdealGenerator_ne_zero_ideal _ hr.1))
  have hG := rowTwist_radical_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨HeckeRowClosure.rowCharacter M hM _ hG (rowTwist_unit η m f z), ?_, ?_⟩
  · change M.absNorm ≤ _
    have hfr : Ideal.span {f^4*z} ≤ (Ideal.span {r} : Ideal O) := by
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact Ideal.mem_span_singleton.mpr ⟨(u : O)*lambda^a*(2 : O)^b, by rw [hx]; ring⟩
    have hF : (Ideal.span {f^4*z} : Ideal O).radical ≠ ⊥ :=
      radical_ne_bot _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (pow_ne_zero _ hf) hz))
    let : Finite (O ⧸ (Ideal.span {f^4*z} : Ideal O).radical) :=
      Ring.HasFiniteQuotients.finiteQuotient hF
    have hn := FiniteConductor.absNorm_le_of_le (Ideal.radical_mono hfr)
    simpa only [M, map_mul] using Nat.mul_le_mul_left
      (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm) hn
  · intro n
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · exact Eq.symm (not_not.mp (fun h => hn
        (rowTwist_nonzero_radical_unit η m f z n hmLam hm2 u a b r hx h)))

theorem periodic_sup (G : O →* ℂ) (I J : Ideal O)
    (hI : CanonicalCoefficientClass.FactorsModulo I G)
    (hJ : CanonicalCoefficientClass.FactorsModulo J G) :
    CanonicalCoefficientClass.FactorsModulo (I ⊔ J) G := by
  intro x y hxy
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxy
  calc
    G x = G (x-a) := hI _ _ (by convert ha using 1; ring)
    _ = G y := hJ _ _ (by convert hb using 1; linear_combination -hab)

theorem primitive_of_equal_elements (χ θ : Character)
    (hel : ∀ n : O, elementCoeff χ n = elementCoeff θ n) :
    ∃ ψ : Character, χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ θ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  have hθ : CanonicalCoefficientClass.FactorsModulo θ.modulus (elementHom χ) := by
    intro x y hxy
    change elementCoeff χ x = elementCoeff χ y
    rw [hel x, hel y]
    exact elementHom_periodic θ x y hxy
  let M := χ.modulus ⊔ θ.modulus
  have hM : M ≠ ⊥ := fun h => χ.modulus_ne_bot (bot_unique (h ▸ le_sup_left))
  have hG := periodic_sup (elementHom χ) χ.modulus θ.modulus (elementHom_periodic χ) hθ
  have hu : ∀ u : Oˣ, elementHom χ (u : O) = 1 := fun u => χ.unit_trivial u
  let ρ := HeckeRowClosure.rowCharacter M hM (elementHom χ) hG hu
  have hr (n : O) : elementCoeff ρ n = elementCoeff χ n := by
    change elementCoeff (HeckeRowClosure.rowCharacter M hM _ hG hu) n = _
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · have hz : elementCoeff χ n = 0 := by
        by_contra hne
        have hu : IsUnit (Ideal.Quotient.mk χ.modulus n) := MulChar.apply_ne_zero_iff.mp hne
        exact hn (hu.map (Ideal.Quotient.factor (show χ.modulus ≤ M from le_sup_left)))
      exact hz.symm
  obtain ⟨ψ, hψ, hp, hn, hmask⟩ := exists_primitive_character ρ
  refine ⟨ψ, le_sup_left.trans hψ, hp, ?_, ?_⟩
  · let : Finite (O ⧸ θ.modulus) := Ring.HasFiniteQuotients.finiteQuotient θ.modulus_ne_bot
    exact hn.trans (FiniteConductor.absNorm_le_of_le (show θ.modulus ≤ M from le_sup_right))
  · intro I
    by_cases hI : I = 0
    · subst I
      simp only [map_zero, ite_self]
    let n := cubicIdealGenerator I
    have hn0 : n ≠ 0 := cubicIdealGenerator_ne_zero I hI
    have hs : Ideal.span {n} = I := span_cubicIdealGenerator I
    have hre : idealCoeff ρ I = idealCoeff χ I := by
      rw [← hs, idealCoeff_span _ hn0, idealCoeff_span _ hn0, hr]
    by_cases hc : IsCoprime I χ.modulus
    · have hu : IsUnit (Ideal.Quotient.mk χ.modulus n) :=
        (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr (hs.symm ▸ hc)
      have huM : IsUnit (Ideal.Quotient.mk M n) :=
        hu.map (Ideal.Quotient.factor (show χ.modulus ≤ M from le_sup_left))
      have hcM : IsCoprime I M := hs ▸ (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp huM
      simpa only [hre, show ρ.modulus = M from rfl, hcM, hc, ite_true] using hmask I
    · rw [if_neg hc]
      have hc' : ¬IsUnit (Ideal.Quotient.mk χ.modulus n) := by
        intro hu
        exact hc (hs ▸ (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp hu)
      rw [←hs, idealCoeff_span χ hn0]
      exact not_not.mp (fun hn => hc' (MulChar.apply_ne_zero_iff.mp hn))

theorem rawRow_small_presentation (u : HeckeInverseAmplification.FreeRow) :
    ∃ θ : Character,
      θ.modulus.absNorm ≤ ProbeHighRowFamily.conductorConstant *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ n : O, elementCoeff (ProbeHighRowFamily.rawRow u) n = elementCoeff θ n := by
  obtain ⟨θ, hn, he⟩ := exists_row_character_radical
    (ProbePhysical.fixedSourcePrincipal ∅ (by simp)) ProbeHighRowFamily.rowMaskElement 1 u.val
    ProbeHighRowFamily.rowMaskElement_ne_zero one_ne_zero u.property.1
    (dvd_mul_left _ _) (dvd_mul_right _ _)
  refine ⟨θ, ?_, ?_⟩
  · simpa [ProbeHighRowFamily.conductorConstant, ProbePhysical.fixedSourcePrincipal,
      HeckeRayFamily.character, Character.ofResidue] using hn
  · intro n
    have ho := (Classical.choose_spec
      (exists_row_character_with_conductor (ProbePhysical.fixedSourcePrincipal ∅ (by simp))
        ProbeHighRowFamily.rowMaskElement 1 u.val ProbeHighRowFamily.rowMaskElement_ne_zero
        one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2 n
    exact ho.trans (he n).symm

theorem rawRow_primitive_radical (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rawRow u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ ProbeHighRowFamily.conductorConstant *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rawRow u) I =
        if IsCoprime I (ProbeHighRowFamily.rawRow u).modulus then idealCoeff ψ I else 0 := by
  obtain ⟨θ, hn, he⟩ := rawRow_small_presentation u
  obtain ⟨ψ, hle, hp, hb, hmask⟩ := primitive_of_equal_elements _ θ he
  exact ⟨ψ, hle, hp, hb.trans hn, hmask⟩

theorem equal_elements_excludePrimes (χ θ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff θ n)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (n : O) :
    elementCoeff (χ.excludePrimes S hS) n = elementCoeff (θ.excludePrimes S hS) n := by
  have hc : IsCoprime (Ideal.span {n}) χ.modulus ↔ IsCoprime (Ideal.span {n}) θ.modulus := by
    have huχ : elementCoeff χ n ≠ 0 ↔ IsCoprime (Ideal.span {n}) χ.modulus :=
      MulChar.apply_ne_zero_iff.trans (IdealCharacter.isUnit_mk_iff_isCoprime _ _)
    have huθ : elementCoeff θ n ≠ 0 ↔ IsCoprime (Ideal.span {n}) θ.modulus :=
      MulChar.apply_ne_zero_iff.trans (IdealCharacter.isUnit_mk_iff_isCoprime _ _)
    rw [he n] at huχ
    exact huχ.symm.trans huθ
  simp only [Character.excludePrimes, elementCoeff_refineModulus,
    IdealCharacter.isUnit_mk_iff_isCoprime, IsCoprime.mul_right_iff, hc, he n]

def fixedConductorConstant (S : Finset (Ideal O)) : ℕ :=
  ProbeHighRowFamily.conductorConstant * (∏ P ∈ S, P).absNorm

theorem rowCharacter_primitive_radical (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0 := by
  obtain ⟨θ, hn, he⟩ := rawRow_small_presentation u
  obtain ⟨ψ, hle, hp, hb, hmask⟩ := primitive_of_equal_elements
    (ProbeHighRowFamily.rowCharacter S hS u) (θ.excludePrimes S hS)
    (equal_elements_excludePrimes _ θ he S hS)
  refine ⟨ψ, hle, hp, hb.trans ?_, hmask⟩
  change (θ.modulus * ∏ P ∈ S, P).absNorm ≤ _
  rw [map_mul]
  simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm] using
    Nat.mul_le_mul_right ((∏ P ∈ S, P).absNorm) hn

theorem prod_le_radical_prod_pow {ι : Type*} (T : Finset ι)
    (P : ι → Ideal O) (e : ι → ℕ) (he : ∀ i ∈ T, 1 ≤ e i) :
    (∏ i ∈ T, P i) ≤ (∏ i ∈ T, P i ^ e i).radical := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hei : e i ≠ 0 := by have := he i (Finset.mem_insert_self i T); omega
    have hpow : (P i ^ e i).radical = (P i).radical := Ideal.radical_pow (P i) hei
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Ideal.radical_mul, hpow]
    exact Ideal.mul_le_inf.trans (inf_le_inf (P i).le_radical
      (ih (fun j hj => he j (Finset.mem_insert_of_mem hj))))

theorem radical_norm_selected_deficit {ι : Type*} [Fintype ι]
    (I : Ideal O) (hI : I ≠ 0) (P : ι → Ideal O)
    (hP : ∀ i, Prime (P i)) (hdis : Function.Injective P)
    (e : ι → ℕ) (he : ∀ i, 1 ≤ e i) (hdiv : ∀ i, P i ^ e i ∣ I) :
    I.radical.absNorm * ∏ i, (P i).absNorm ^ (e i - 1) ≤ I.absNorm := by
  let (i : ι) : (P i).IsMaximal := (Ideal.isPrime_of_prime (hP i)).isMaximal (hP i).ne_zero
  have hcop : Pairwise (fun i j => IsCoprime (P i ^ e i) (P j ^ e j)) := by
    intro i j hij
    exact (Ideal.isCoprime_of_isMaximal (hdis.ne hij)).pow
  obtain ⟨B, hB⟩ := Fintype.prod_dvd_of_coprime hcop hdiv
  have hB0 : B ≠ 0 := by
    intro hz
    apply hI
    rw [hB, hz, mul_zero]
  have hsmall0 : (∏ i, P i) * B ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => (hP i).ne_zero)) hB0
  have hsmall : (∏ i, P i) * B ≤ I.radical := by
    rw [hB, Ideal.radical_mul]
    exact Ideal.mul_le_inf.trans (inf_le_inf
      (prod_le_radical_prod_pow Finset.univ P e (fun i _ => he i)) B.le_radical)
  let : Finite (O ⧸ (∏ i, P i) * B) := Ring.HasFiniteQuotients.finiteQuotient hsmall0
  have hn := FiniteConductor.absNorm_le_of_le hsmall
  have hprod : (∏ i, P i) * (∏ i, P i ^ (e i-1)) = ∏ i, P i ^ e i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_succ']
    congr 1
    exact Nat.sub_add_cancel (he i)
  calc
    I.radical.absNorm * ∏ i, (P i).absNorm ^ (e i-1) ≤
        ((∏ i, P i) * B).absNorm * (∏ i, P i ^ (e i-1)).absNorm := by
      simpa only [map_prod, map_pow] using Nat.mul_le_mul_right
        (∏ i, (P i).absNorm ^ (e i-1)) hn
    _ = I.absNorm := by
      rw [← map_mul]
      congr 1
      calc
        ((∏ i, P i) * B) * (∏ i, P i ^ (e i-1)) =
            ((∏ i, P i) * (∏ i, P i ^ (e i-1))) * B := by ring
        _ = I := by rw [hprod, ← hB]

theorem rowCharacter_primitive_selected_deficit (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
          (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
          ψ.modulus.absNorm * ∏ i, (P i).absNorm ^ (e i-1) ≤
            fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).absNorm := by
  obtain ⟨ψ, hle, hp, hn, hm⟩ := rowCharacter_primitive_radical S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis e he hdiv
  have hb := radical_norm_selected_deficit (Ideal.span {u.val})
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1) P hP hdis e
    (fun i => (by have := he i; omega)) hdiv
  calc
    _ ≤ (fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).radical.absNorm) *
        ∏ i, (P i).absNorm ^ (e i-1) := Nat.mul_le_mul_right _ hn
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left (fixedConductorConstant S) hb

theorem canonicalCRT_radical_congr {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) (x y : O)
    (hxy : x-y ∈ (∏ i, P i ^ e i).radical) :
    CenteredMomentCanonical.canonicalCRTCharacter P hg e he hcop
        (Ideal.Quotient.mk (∏ i, P i ^ e i) x) =
      CenteredMomentCanonical.canonicalCRTCharacter P hg e he hcop
        (Ideal.Quotient.mk (∏ i, P i ^ e i) y) := by
  rw [CenteredMomentCanonical.canonicalCRTCharacter_mk,
    CenteredMomentCanonical.canonicalCRTCharacter_mk]
  exact idealRowHom_congr_radical _ x y hxy

theorem fixedConductorConstant_pos (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : 0 < fixedConductorConstant S := by
  have hnorm (I : Ideal O) (hI : I ≠ 0) : 0 < I.absNorm :=
    Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  unfold fixedConductorConstant ProbeHighRowFamily.conductorConstant
  exact mul_pos (mul_pos
    (hnorm _ (Ideal.span_singleton_eq_bot.not.mpr ProbeHighRowFamily.rowMaskElement_ne_zero))
    (hnorm _ (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))))
    (hnorm _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)))

theorem sourceRow_primitive_radical (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (hbad : CanonicalRowCompletion.fixedBadPrimes ⊆ S)
    (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, ProbePhysical.highExclusion S hS I * idealRowHom u.val I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0 := by
  obtain ⟨ψ, hle, hp, hn, hm⟩ := rowCharacter_primitive_radical S hS u
  refine ⟨ψ, hle, hp, hn, ?_⟩
  intro I
  rw [← ProbeHighRowFamily.rowCharacter_coeff S hS hbad u I]
  exact hm I

theorem rowCharacter_primitive_selected_div (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
          (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
          (ψ.modulus.absNorm : ℝ) ≤
            ((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) /
              ∏ i, ((P i).absNorm : ℝ) ^ (e i-1) := by
  obtain ⟨ψ, hle, hp, hm, hb⟩ := rowCharacter_primitive_selected_deficit S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis e he hdiv
  have hpos : 0 < ∏ i, ((P i).absNorm : ℝ) ^ (e i-1) := by
    apply Finset.prod_pos
    intro i _
    apply pow_pos
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hP i).ne_zero)
  apply (le_div_iff₀ hpos).mpr
  exact_mod_cast hb k P hP hdis e he hdiv

end ProbeRowRadicalConductor

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology ComplexConjugate
open Set Complex
namespace ProbeRowReflectedAllocation
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeFiniteDeletion HeckeReciprocalGrowth HeckeDeletionBounds
open ProbeRowRadicalConductor
local notation "O" => Eisenstein.O

lemma prod_rpow_nonneg {ι : Type*} (T : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ T, 0 ≤ q i) (A : ℝ) :
    (∏ i ∈ T, q i) ^ A = ∏ i ∈ T, (q i) ^ A := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      Real.mul_rpow (hq i (Finset.mem_insert_self i T))
        (Finset.prod_nonneg (fun j hj => hq j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hq j (Finset.mem_insert_of_mem hj))]

lemma selected_exponent_allocation {a e : ℝ} (ha : 51/100 ≤ a)
    (he : 0 < e) {j : ℕ} (hj : 2 ≤ j) :
    -(1-a-6*e) ≤ (j-1 : ℕ)*(a-1/2+6*e)-1/2 := by
  have hA : 0 ≤ a-1/2+6*e := by linarith
  have hj' : (1 : ℝ) ≤ (j-1 : ℕ) := by exact_mod_cast (show 1 ≤ j-1 by omega)
  nlinarith [mul_le_mul_of_nonneg_right hj' hA]

theorem allocation_of_deficit {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ i, 1 ≤ q i) (j : Fin k → ℕ) (hj : ∀ i, 2 ≤ j i)
    (N D a e : ℝ) (hN : 0 ≤ N) (ha : 51/100 ≤ a) (he : 0 < e)
    (hdef : N * ∏ i, q i ^ (j i-1) ≤ D) :
    N ^ (a-1/2+6*e) * ∏ i, q i ^ (-(1-a-6*e)) ≤
      D ^ (a-1/2+6*e) * ∏ i, q i ^ (-(1/2 : ℝ)) := by
  let A := a-1/2+6*e
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hq0 (i) : 0 ≤ q i := (by linarith [hq i])
  have hlocal (i) : q i ^ (-(1-a-6*e)) ≤
      (q i ^ (j i-1)) ^ A * q i ^ (-(1/2 : ℝ)) := by
    rw [← Real.rpow_natCast_mul (hq0 i), ← Real.rpow_add (by linarith [hq i])]
    apply Real.rpow_le_rpow_of_exponent_le (hq i)
    exact selected_exponent_allocation ha he (hj i)
  have hprod := Finset.prod_le_prod (s := Finset.univ) (fun i _ => Real.rpow_nonneg (hq0 i) _)
    (fun i _ => hlocal i)
  rw [Finset.prod_mul_distrib, ← prod_rpow_nonneg Finset.univ
    (fun i => q i ^ (j i-1)) (fun i _ => pow_nonneg (hq0 i) _) A] at hprod
  have hD0 : 0 ≤ ∏ i, q i ^ (j i-1) := Finset.prod_nonneg (fun i _ => pow_nonneg (hq0 i) _)
  calc
    _ ≤ N ^ A * ((∏ i, q i ^ (j i-1)) ^ A * ∏ i, q i ^ (-(1/2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hN _)
    _ = (N * ∏ i, q i ^ (j i-1)) ^ A * ∏ i, q i ^ (-(1/2 : ℝ)) := by
      rw [Real.mul_rpow hN hD0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (mul_nonneg hN hD0) hdef hA)
      (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hq0 i) _))

lemma prime_norm_ge_one (P : Ideal O) (hP : Prime P) : (1 : ℝ) ≤ P.absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)

lemma original_row_conductor_le (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ((rowCharacter S hS u).modulus.absNorm : ℝ) ≤
      (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm := by
  exact_mod_cast (by simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm]
    using rowCharacter_conductor S hS u)

lemma original_row_deletion_radical_le (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ((HeckeDeletionBounds.radical (rowCharacter S hS u).modulus).absNorm : ℝ) ≤
      (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm :=
  by
    let χ := rowCharacter S hS u
    have hd : HeckeDeletionBounds.radical χ.modulus ∣ χ.modulus := by
      unfold HeckeDeletionBounds.radical HeckeIdealSeries.primeProduct
      rw [HeckeIdealSeries.prod_primeSet χ.modulus (fun J : Ideal O => J)]
      exact support_product_dvd χ.modulus_ne_bot (Finset.Subset.refl _)
    have hn : ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) ≤ χ.modulus.absNorm := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)) (map_dvd Ideal.absNorm hd)
    exact hn.trans (original_row_conductor_le S hS u)

theorem row_same_primitive_allocation (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ∃ ψ : Character, (rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (rowCharacter S hS u) I =
        if IsCoprime I (rowCharacter S hS u).modulus then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (j : Fin k → ℕ), (∀ i, 2 ≤ j i) →
          (∀ i, P i ^ j i ∣ Ideal.span {u.val}) →
          ∀ a e : ℝ, 51/100 ≤ a → 0 < e →
          (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
              ∏ i, ((P i).absNorm : ℝ) ^ (-(1-a-6*e)) ≤
            ((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) ^
              (a-1/2+6*e) * ∏ i, ((P i).absNorm : ℝ) ^ (-(1/2 : ℝ)) := by
  obtain ⟨ψ, hle, hp, hm, hdef⟩ := rowCharacter_primitive_selected_deficit S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis j hj hdiv a e ha he
  apply allocation_of_deficit _ (fun i => prime_norm_ge_one _ (hP i)) j hj
    _ _ a e (by positivity) ha he
  exact_mod_cast hdef k P hP hdis j hj hdiv

lemma actual_multiplicity_divisor (u : FreeRow) (p : O) (hp : Prime p) :
    (Ideal.span {p} : Ideal O) ^ multiplicity p u.val ∣ Ideal.span {u.val} ∧
      multiplicity p u.val < 6 := by
  refine ⟨⟨Ideal.span {unitPart u p hp}, ?_⟩, multiplicity_lt_six u p hp⟩
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  exact congrArg (fun x : O => (Ideal.span {x} : Ideal O)) (unitPart_spec u p hp).1

lemma actual_ideal_multiplicity (u : FreeRow) (P : Ideal O) (hP : Prime P) :
    P ^ multiplicity P (Ideal.span {u.val} : Ideal O) ∣ Ideal.span {u.val} ∧
      multiplicity P (Ideal.span {u.val} : Ideal O) < 6 := by
  refine ⟨pow_multiplicity_dvd _ _, ?_⟩
  rw [UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors hP.irreducible
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1), normalize_eq]
  exact u.property.2 P

theorem buffered_reflected_right_bound (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
      detectorMaximum χ (3*(i+1 : ℕ)*B) < a+2*e →
      ∀ (j : ι), (χ j).residue ≠ 1 →
      ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
      ‖LFunction (χ j) (1-conj w)‖ ≤
        C * (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨C, hC, hb⟩ := buffered_regular_control e ε he he' hε
  refine ⟨C, hC, ?_⟩
  intro ι _ χ B a i hB ha ha1 hmax j hχ w hw hwi
  have hwr : (1-conj w).re = a+6*e := by simp; linarith
  have hwm : (1-conj w).im = w.im := by simp
  have hz : 1-conj w ∈ Metric.closedBall ((2 : ℂ)+w.im*I) (2-a-6*e) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : 1-conj w-((2 : ℂ)+w.im*I) = ((a+6*e-2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp; linarith
      · simp
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have h := hb χ B a i hB ha ha1 hmax j w.im hwi (1-conj w) hz
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal _ hχ] at h
  have hH : 0 ≤ (3*i+2 : ℕ)*B := (abs_nonneg _).trans hwi
  have hc : presentationComplexity (χ j) w.im ≤
      presentationComplexity (χ j) ((3*i+2 : ℕ)*B) := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    rw [abs_of_nonneg hH]
    gcongr
  apply (le_trans (le_add_of_nonneg_right (norm_nonneg _)) h).trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by
    unfold presentationComplexity HeckeLogarithmic.complexity; positivity) hc hε.le) hC.le

theorem central_deletion_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ ψ : Character) (a e : ℝ),
      0 < e → 51/100 ≤ a → a ≤ 1 →
      ∀ w : ℂ, w.re = 1-a-6*e →
      ‖factors χ.modulus ψ w‖ * ‖(factors χ.modulus ψ (1-conj w))⁻¹‖ ≤
        C * ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) ^ (6*e+2*ε) := by
  obtain ⟨Cl, hCl, hl⟩ := factors_any_re_subpower_bound ε hε
  obtain ⟨Cr, hCr, hr⟩ := factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Cl*Cr, mul_pos hCl hCr, ?_⟩
  intro χ ψ a e he ha ha1 w hw
  have hR := HeckeDyadic.radical_norm_ge_one χ.modulus
  have hR0 : 0 < ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) := by linarith
  have hleft : ‖factors χ.modulus ψ w‖ ≤
      Cl * ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) ^ (6*e+ε) := by
    apply (hl χ.modulus ψ w).trans
    apply mul_le_mul_of_nonneg_left _ hCl.le
    apply Real.rpow_le_rpow_of_exponent_le hR
    have hm : max (-w.re) 0 ≤ 6*e := max_le (by rw [hw]; linarith) (by positivity)
    linarith
  have hright : ‖(factors χ.modulus ψ (1-conj w))⁻¹‖ ≤
      Cr * ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) ^ ε := by
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans
      (hr χ.modulus ψ (1-conj w) (by simp; linarith))
  calc
    _ ≤ (Cl * ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) ^ (6*e+ε)) *
        (Cr * ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) ^ ε) :=
      mul_le_mul hleft hright (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hR0]
      congr 2
      ring

theorem buffered_same_primitive_reflected (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
      detectorMaximum χ (3*(i+1 : ℕ)*B) < a+2*e →
      ∀ (j : ι) (ψ : Character), FiniteFourier.IsPrimitiveOnIdeals ψ.residue →
      (χ j).residue ≠ 1 →
      (∀ I : Ideal O, idealCoeff (χ j) I =
        if IsCoprime I (χ j).modulus then idealCoeff ψ I else 0) →
      ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
      ‖LFunction (χ j) w‖ ≤ C * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
        ((HeckeDeletionBounds.radical (χ j).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
        (3+(3*i+2 : ℕ)*B)^2 *
        (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨Cg, hCg, hg⟩ := HeckeDyadicReflection.original_reflected_bound
  obtain ⟨Cb, hCb, hb⟩ := buffered_reflected_right_bound e ε he he' hε
  obtain ⟨Cd, hCd, hd⟩ := central_deletion_bound ε hε
  refine ⟨Cg*Cb*Cd, by positivity, ?_⟩
  intro ι _ χ B a i hB ha ha1 hmax j ψ hp hχ hm w hw hwi
  have hr := hg (χ j) ψ hp hχ hm w (by rw [hw]; linarith) (by rw [hw]; linarith)
  have hexp : 1/2-w.re = a-1/2+6*e := by rw [hw]; ring
  rw [hexp] at hr
  have hright := hb χ B a i hB ha ha1 hmax j hχ w hw hwi
  have hdel := hd (χ j) ψ a e he ha ha1 w hw
  have hpc0 : 0 ≤ presentationComplexity (χ j) ((3*i+2 : ℕ)*B) := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity
  calc
    _ ≤ Cg * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) * (3+|w.im|)^2 *
        ‖LFunction (χ j) (1-conj w)‖ *
        (‖factors (χ j).modulus ψ w‖ * ‖(factors (χ j).modulus ψ (1-conj w))⁻¹‖) := hr
    _ ≤ Cg * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) * (3+(3*i+2 : ℕ)*B)^2 *
        (Cb * (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε) *
        (Cd * ((HeckeDeletionBounds.radical (χ j).modulus).absNorm : ℝ) ^ (6*e+2*ε)) := by
      gcongr
    _ = _ := by ring

theorem source_calibrated_reflected_allocation (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
      (hmaxS : ∀ P ∈ S, P.IsMaximal)
      (_hbad : CanonicalRowCompletion.fixedBadPrimes ⊆ S)
      (u : FreeRow), u.val ≠ 1 →
      ∃ ψ : Character, (rowCharacter S hS u).modulus ≤ ψ.modulus ∧
        FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        (∀ I : Ideal O, idealCoeff (rowCharacter S hS u) I =
          if IsCoprime I (rowCharacter S hS u).modulus then idealCoeff ψ I else 0) ∧
        (((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val ≠ 0) →
          (rowCharacter S hS u).residue ≠ 1 ∧ ψ.residue ≠ 1) ∧
        ∀ {ι : Type*} [Fintype ι] (η : Character) (twists : ι → Character)
          (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
          detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1 : ℕ)*B) < a+2*e →
          ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ j, Prime (P j)) → Function.Injective P →
          ∀ (v : Fin k → ℕ), (∀ j, 2 ≤ v j) →
            (∀ j, P j ^ v j ∣ Ideal.span {u.val}) →
            ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
            ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val) *
                HeckeOrigin.continued (rowCharacter S hS u) w‖ *
                ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) ≤
              C * (((fixedConductorConstant S : ℝ) *
                (Ideal.span {u.val} : Ideal O).absNorm) ^ (a-1/2+6*e) *
                ∏ j, ((P j).absNorm : ℝ) ^ (-(1/2 : ℝ))) *
                ((HeckeDeletionBounds.radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
                (3+(3*i+2 : ℕ)*B)^2 *
                (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨C, hC, hb⟩ := buffered_same_primitive_reflected e ε he he' hε
  refine ⟨C, hC, ?_⟩
  intro S hS hmaxS hbad u hu
  obtain ⟨ψ, hle, hp, hm, hall⟩ := row_same_primitive_allocation S hS u
  have hactive (hc : (ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val ≠ 0) :
      (rowCharacter S hS u).residue ≠ 1 ∧ ψ.residue ≠ 1 := by
    have hn := calibrated_row_nonprincipal S hS hmaxS hbad u hu hc
    exact ⟨hn, fun h => hn ((principal_iff_of_mask _ ψ hm).mpr h)⟩
  refine ⟨ψ, hle, hp, hm, hactive, ?_⟩
  intro ι _ η twists B a i hB ha ha1 hbin k P hP hdis v hv hdiv w hw hwi
  have hpc0 : 0 ≤ presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B) := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity
  by_cases hc : (ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val = 0
  · simp only [hc, star_zero, zero_mul, norm_zero]
    positivity
  · have hn := (hactive hc).1
    have hL := hb (sourceDetectorFamily S hS η u twists) B a i hB ha ha1 hbin
      (Sum.inl true) ψ hp hn hm w hw hwi
    simp only [sourceDetectorFamily_numerator] at hL
    have hcal : ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val)‖ ≤ 1 := by
      rw [norm_star]
      exact (ProbePhysical.calibrationForSet S hmaxS).residueMonoid_norm_le_one _
    have hweighted : ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val) *
        HeckeOrigin.continued (rowCharacter S hS u) w‖ ≤ ‖LFunction (rowCharacter S hS u) w‖ := by
      rw [HeckeOrigin.continued, if_neg hn, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hcal
    have hal := hall k P hP hdis v hv hdiv a e ha he
    rw [← hw] at hal
    have hprod0 : 0 ≤ ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) :=
      Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (by positivity) _)
    calc
      _ ≤ (C * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
          ((HeckeDeletionBounds.radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
          (3+(3*i+2 : ℕ)*B)^2 *
          (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε) *
          ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) :=
        mul_le_mul_of_nonneg_right (hweighted.trans hL) hprod0
      _ = (C * ((HeckeDeletionBounds.radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
          (3+(3*i+2 : ℕ)*B)^2 *
          (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε) *
          ((ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
          ∏ j, ((P j).absNorm : ℝ) ^ (-w.re)) := by ring
      _ ≤ (C * ((HeckeDeletionBounds.radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
          (3+(3*i+2 : ℕ)*B)^2 *
          (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε) *
          ((((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) ^
            (a-1/2+6*e)) * ∏ j, ((P j).absNorm : ℝ) ^ (-(1/2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hal (by positivity)
      _ = _ := by ring

theorem source_actual_valuation_reflection (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
      (hmaxS : ∀ P ∈ S, P.IsMaximal)
      (_hbad : CanonicalRowCompletion.fixedBadPrimes ⊆ S)
      (u : FreeRow), u.val ≠ 1 →
      ∃ ψ : Character, (rowCharacter S hS u).modulus ≤ ψ.modulus ∧
        FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        (∀ I : Ideal O, idealCoeff (rowCharacter S hS u) I =
          if IsCoprime I (rowCharacter S hS u).modulus then idealCoeff ψ I else 0) ∧
        (((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val ≠ 0) →
          (rowCharacter S hS u).residue ≠ 1 ∧ ψ.residue ≠ 1) ∧
        ∀ {ι : Type*} [Fintype ι] (η : Character) (twists : ι → Character)
          (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
          detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1 : ℕ)*B) < a+2*e →
          ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ j, Prime (P j)) → Function.Injective P →
          (∀ j, 2 ≤ multiplicity (P j) (Ideal.span {u.val} : Ideal O)) →
          (∀ j, multiplicity (P j) (Ideal.span {u.val} : Ideal O) < 6) ∧
          ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
            ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val) *
                HeckeOrigin.continued (rowCharacter S hS u) w‖ *
                ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) ≤
              C * (((fixedConductorConstant S : ℝ) *
                (Ideal.span {u.val} : Ideal O).absNorm) ^ (a-1/2+6*e) *
                ∏ j, ((P j).absNorm : ℝ) ^ (-(1/2 : ℝ))) *
                ((HeckeDeletionBounds.radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
                (3+(3*i+2 : ℕ)*B)^2 *
                (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨C, hC, hb⟩ := source_calibrated_reflected_allocation e ε he he' hε
  refine ⟨C, hC, ?_⟩
  intro S hS hmaxS hbad u hu
  obtain ⟨ψ, hle, hp, hm, hactive, hbound⟩ := hb S hS hmaxS hbad u hu
  refine ⟨ψ, hle, hp, hm, hactive, ?_⟩
  intro ι _ η twists B a i hB ha ha1 hbin k P hP hdis hv
  refine ⟨fun j => (actual_ideal_multiplicity u (P j) (hP j)).2, ?_⟩
  exact hbound η twists B a i hB ha ha1 hbin k P hP hdis
    (fun j => multiplicity (P j) (Ideal.span {u.val} : Ideal O)) hv
    (fun j => (actual_ideal_multiplicity u (P j) (hP j)).1)

end ProbeRowReflectedAllocation

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeCentralRepeatedProduct
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CompletedGauss ProbeRowReflectedAllocation
open HeckeDeletionBounds HeckeReciprocalGrowth
local notation "O" => Eisenstein.O

def rowCost (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (a e eps T : ℝ) : ℝ :=
  ((ProbeRowRadicalConductor.fixedConductorConstant S:ℝ)*(Ideal.span {u.val}:Ideal O).absNorm)^(a-1/2+6*e)*
    ((HeckeDeletionBounds.radical (rowCharacter S hS u).modulus).absNorm:ℝ)^(6*e+2*eps)*
    (3+T)^2*(presentationComplexity (rowCharacter S hS u) T)^eps

lemma rowCost_nonneg (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (a e eps T : ℝ) : 0≤ rowCost S hS u a e eps T := by
  unfold rowCost presentationComplexity HeckeLogarithmic.complexity
  positivity

lemma repeated_weight_bound (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (a e B Y : ℝ) (W : ℝ→ℂ) (x w z : ℂ)
    (hB : 0≤ B) (hW : ∀t,‖W t‖≤ B)
    (hQ : (480:ℝ)≤ P.val.absNorm) (hsmall : 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2)
    (ha : (51/100:ℝ)≤ a) (ha1 : a≤1) (he : 0< e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hr : repeatedRowPrime u P) :
    ‖W ((P.val.absNorm:ℝ)/Y)*(P.val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u P hs x w z‖≤
      (812*B*(P.val.absNorm:ℝ)^z.re)*(P.val.absNorm:ℝ)^(-w.re) := by
  have hp : (0:ℝ)< P.val.absNorm := by linarith
  have hb := (central_actual_local_bounds η u P hs hη a e x w z hQ hsmall ha ha1 he he1 hx hw hz).2.2
  rw [if_pos hr] at hb
  have hn : ‖(P.val.absNorm:ℂ)^(z-1)‖=(P.val.absNorm:ℝ)^(z.re-1) := by
    rw [show (P.val.absNorm:ℂ)=(((P.val.absNorm:ℝ):ℂ)) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp
  rw [norm_mul,norm_mul,hn]
  calc
    _ ≤ B*(P.val.absNorm:ℝ)^(z.re-1)*(812*(P.val.absNorm:ℝ)^(1-w.re)) := by
      gcongr
      exact hW _
    _ = _ := by
      calc
        _ = 812*B*((P.val.absNorm:ℝ)^(z.re-1)*(P.val.absNorm:ℝ)^(1-w.re)) := by ring
        _ = 812*B*(P.val.absNorm:ℝ)^(z.re-w.re) := by rw [←Real.rpow_add hp];congr 2;ring
        _ = _ := by rw [show z.re-w.re=z.re+(-w.re) by ring,Real.rpow_add hp];ring

theorem selected_repeated_product (e eps : ℝ) (he : 0< e) (he1 : e<1/1000)
    (heps : 0< eps) :
    ∃C : ℝ,0< C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T a : ℝ) (i : ℕ),2< T → 51/100≤ a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T)< a+2*e →
    ∀(k : ℕ) (P : Fin k→HeckeIdealSeries.PrimeIdeal) (hs : ∀j,Supported (P j).val),
      Function.Injective P → (∀j,IsCoprime (P j).val η.modulus) →
      (∀j,(480:ℝ)≤(P j).val.absNorm) →
      (∀j,198*((P j).val.absNorm:ℝ)^(-10*e)≤1/2) →
      (∀j,repeatedRowPrime u (P j)) →
    ∀(B : ℝ) (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),0≤ B → (∀j t,‖W j t‖≤ B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ∏j,‖W j (((P j).val.absNorm:ℝ)/Y j)*((P j).val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u (P j) (hs j) x w z‖ ≤
        C*(812*B)^k*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*
          ∏j,((P j).val.absNorm:ℝ)^(z.re-1/2) := by
  obtain ⟨C,hC,hbound⟩ := source_calibrated_reflected_allocation e eps he he1 heps
  refine ⟨C,hC,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T a i hT ha ha1 hbin k P hs hdis hη hQ hsmall hr B W Y hB hW x w z hx hw hz hwi
  obtain ⟨ψ,hle,hprim,hmask,hactive,hb⟩ := hbound S hS hmax hbad u hu
  have hi : Function.Injective (fun j=>(P j).val) := fun j l h=> hdis (Subtype.ext h)
  have hdiv (j : Fin k) := actual_multiplicity_divisor u (primaryIdealGenerator (P j).val) (supported_primeGenerator_prime (P j) (hs j))
  have hspan (j : Fin k) : (Ideal.span {primaryIdealGenerator (P j).val}:Ideal O)=(P j).val := CenteredMomentSourceRow.primary_span_supported (P j).val (hs j)
  have hb' := hb η twists T a i hT ha ha1 hbin k (fun j=>(P j).val) (fun j=>(P j).property) hi
    (fun j=> multiplicity (primaryIdealGenerator (P j).val) u.val) (fun j=>(hr j).2)
    (fun j=> by have hd := (hdiv j).1;rw [hspan j] at hd;exact hd) w hw hwi
  let q : Fin k→ℝ := fun j=>(P j).val.absNorm
  have hq (j : Fin k) : 0< q j := by dsimp [q];have := hQ j;linarith
  have hp : (∏j,‖W j (q j/Y j)*((P j).val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u (P j) (hs j) x w z‖)≤
      (812*B)^k*(∏j,q j^z.re)*(∏j,q j^(-w.re)) := by
    have ht := Finset.prod_le_prod (s:=Finset.univ) (fun j (_:j∈Finset.univ)=> norm_nonneg _)
      (fun j (_:j∈Finset.univ)=> repeated_weight_bound η u (P j) (hs j) (hη j)
        a e B (Y j) (W j) x w z hB (hW j) (hQ j) (hsmall j) ha ha1 he he1.le hx hw hz (hr j))
    simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow] using ht
  have hbc :
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ∏j,q j^(-w.re) ≤ C*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*∏j,q j^(-(1/2:ℝ)) := by
    convert hb' using 1 <;> first | rfl | (dsimp only [rowCost,q]; ring)
  have heq : (∏j,q j^z.re)*(∏j,q j^(-(1/2:ℝ)))=∏j,q j^(z.re-1/2) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [←Real.rpow_add (hq j)]
    congr 1
  calc
    _ ≤ ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ((812*B)^k*(∏j,q j^z.re)*(∏j,q j^(-w.re))) := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = ((812*B)^k*(∏j,q j^z.re))*(‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS u) w‖*∏j,q j^(-w.re)) := by ring
    _ ≤ ((812*B)^k*(∏j,q j^z.re))*(C*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*∏j,q j^(-(1/2:ℝ))) :=
      mul_le_mul_of_nonneg_left hbc (by positivity)
    _ = _ := by rw [show ((812*B)^k*(∏j,q j^z.re))*(C*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*∏j,q j^(-(1/2:ℝ)))=
      C*(812*B)^k*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*((∏j,q j^z.re)*(∏j,q j^(-(1/2:ℝ)))) by ring,heq]
end ProbeCentralRepeatedProduct

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeRaySlots
open HeckeFamily ProbePhysical PNT.AnnularPrimeMass
local notation "Id" => Ideal Eisenstein.O

lemma pool_sum_complex (C : Set Id) (S : Finset Id) (a b x : ℝ) (f : Id→ℂ) :
    (∑P∈pool C S a b x,f P.val)=∑P∈annularPrimeIdeals C a b x\S,f P := by
  apply Finset.sum_bij (fun P _=> P.val)
  · intro P hP;exact Finset.mem_subtype.mp hP
  · intro P hP Q hQ he;exact Subtype.ext he
  · intro P hP
    have hp : Prime P := ((mem_annularPrimeIdeals C a b x P).mp (Finset.mem_sdiff.mp hP).1).2.1
    exact ⟨⟨P,hp⟩,Finset.mem_subtype.mpr hP,rfl⟩
  · intro P hP;rfl

theorem weighted_pool_eq_annular (C : Set Id) (S : Finset Id)
    (W : ℝ→ℂ) (a b D : ℝ) (ha : 0< a) (_hab : a≤ b) (hD : 0< D)
    (hW : Function.support W⊆Set.Ioo a b)
    (hS : ∀P∈S,(P.absNorm:ℝ)≤ a*D) (g : Id→ℂ) :
    (∑P∈pool C S a b D,W ((P.val.absNorm:ℝ)/D)*g P.val)=
      ∑P∈(HeckePrimeAnnular.annulusSet b D).filter (fun P=> Prime P ∧ P∈C),
        W ((P.absNorm:ℝ)/D)*g P := by
  rw [pool_sum_complex C S a b D (fun P=> W ((P.absNorm:ℝ)/D)*g P)]
  have hsub : annularPrimeIdeals C a b D\S⊆
      (HeckePrimeAnnular.annulusSet b D).filter (fun P=> Prime P ∧ P∈C) := by
    intro P hP
    have hp := (mem_annularPrimeIdeals C a b D P).mp (Finset.mem_sdiff.mp hP).1
    apply Finset.mem_filter.mpr
    refine ⟨?_,hp.2.1,hp.1⟩
    apply HeckeInverseAmplification.mem_idealsUpTo.mpr
    refine ⟨Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1.ne_zero),?_⟩
    apply hp.2.2.2.trans
    apply Nat.floor_mono
    nlinarith [le_max_right (1:ℝ) b]
  apply Finset.sum_subset hsub
  intro P hP hnot
  have hw : W ((P.absNorm:ℝ)/D)=0 := by
    by_contra hn
    have hy := hW hn
    have hp := (Finset.mem_filter.mp hP).2
    apply hnot
    apply Finset.mem_sdiff.mpr
    constructor
    · apply (mem_annularPrimeIdeals C a b D P).mpr
      refine ⟨hp.2,hp.1,?_,?_⟩
      · apply (Nat.floor_lt (mul_nonneg hD.le ha.le)).mpr
        have := (lt_div_iff₀ hD).mp hy.1
        nlinarith
      · apply Nat.le_floor
        have := (div_lt_iff₀ hD).mp hy.2
        nlinarith
    · intro hs
      have := hS P hs
      have := (lt_div_iff₀ hD).mp hy.1
      linarith
  simp only [hw,zero_mul]

theorem central_phase_eq_amplitude (M : Id) [NeZero M]
    [Finite (Eisenstein.O ⧸ M)] (H : Subgroup (Eisenstein.O ⧸ M)ˣ)
    (S : Finset Id) (u : Eisenstein.O) (W : ℝ→ℂ) (a b D : ℝ)
    (ha : 0< a) (hab : a≤ b) (hD : 0< D) (hW : Function.support W⊆Set.Ioo a b)
    (hS : ∀P∈S,(P.absNorm:ℝ)≤ a*D) (z : ℂ) :
    (∑P∈pool (RayQuotient.identityClass M H) S a b D,
      W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
        (-star (CanonicalRowCompletion.idealRowHom u P.val)))=
      -(D:ℂ)^(z-1/2)*HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z := by
  have he := weighted_pool_eq_annular (RayQuotient.identityClass M H) S W a b D ha hab hD hW hS
    (fun P=>(P.absNorm:ℂ)^(z-1)*(-star (CanonicalRowCompletion.idealRowHom u P)))
  simp_rw [mul_assoc] at ⊢
  rw [he]
  unfold HeckePrimeRow.canonicalPrimeAmplitude
  rw [←mul_assoc,neg_mul,←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  have hexp : (z-(1/2:ℂ)) + -(1/2:ℂ)=z-1 := by ring
  rw [hexp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  have hprime := (Finset.mem_filter.mp hP).2.1
  have hn : (0:ℝ)< P.absNorm := by exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hprime.ne_zero)
  rw [positive_div_cpow _ _ hn.le hD]
  have hd : (D:ℂ)^(z-1)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  field_simp
  simp only [starRingEnd_apply,Complex.ofReal_natCast]
  ring

theorem central_phase_norm (M : Id) [NeZero M]
    [Finite (Eisenstein.O ⧸ M)] (H : Subgroup (Eisenstein.O ⧸ M)ˣ)
    (S : Finset Id) (u : Eisenstein.O) (W : ℝ→ℂ) (a b D : ℝ)
    (ha : 0< a) (hab : a≤ b) (hD : 0< D) (hW : Function.support W⊆Set.Ioo a b)
    (hS : ∀P∈S,(P.absNorm:ℝ)≤ a*D) (z : ℂ) :
    ‖∑P∈pool (RayQuotient.identityClass M H) S a b D,
      W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
        (-star (CanonicalRowCompletion.idealRowHom u P.val))‖=
      D^(z.re-1/2)*‖HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z‖ := by
  rw [central_phase_eq_amplitude M H S u W a b D ha hab hD hW hS z,
    norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos hD]
  norm_num

theorem power_fixed_exclusions (S : Finset Id) (a ellMin : ℝ) (ha : 0< a) (hmin : 0< ellMin)
    {ι : Type*} (ell : ι→ℝ) (hell : ∀j,ellMin≤ ell j) :
    ∀ᶠZ : ℝ in Filter.atTop,∀j,∀P∈S,(P.absNorm:ℝ)≤ a*Z^(ell j) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop ha
  filter_upwards [ht.eventually (Filter.eventually_ge_atTop (∑P∈S,(P.absNorm:ℝ))),
    Filter.eventually_ge_atTop (1:ℝ)] with Z hnorm hZ j P hP
  calc
    (P.absNorm:ℝ) ≤ ∑Q∈S,(Q.absNorm:ℝ) := Finset.single_le_sum (fun Q _=> Nat.cast_nonneg _) hP
    _ ≤ a*Z^ellMin := hnorm
    _ ≤ a*Z^(ell j) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) ha.le

end ProbeRaySlots
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace ProbeRayCharacterFamily
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion UniqueFactorizationMonoid
local notation "O" => Eisenstein.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

def fixedTwistSupport : Finset (Ideal O) :=
  (normalizedFactors (M*Ideal.span {rowMaskElement}*Ideal.span {(72:O)})).toFinset

omit [NeZero M] in
theorem fixedTwistSupport_prime : ∀P∈fixedTwistSupport M,Prime P := by
  intro P hP
  exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma inverse_twist_base_modulus (θ : RayQuotient.Characters M H) :
    ((fixedSourcePrincipal ∅ (by simp)).product
      (HeckeRayQuotient.character M H hH θ).inverse).modulus=M := by
  change (1:Ideal O)⊓M=M
  simp

theorem large_supported_twists_nonprincipal (u : FreeRow)
    (hs : Supported (Ideal.span {u.val}))
    (hl : (HeckeExceptionalRows.bound (fixedTwistSupport M):ℝ)< rowNorm u)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue≠1 := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val ((supported_iff_native _).mp hs)
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hs
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*lambda^0*(2:O)^0*r := by simp [r]
  let η := (fixedSourcePrincipal ∅ (by simp)).product
    (HeckeRayQuotient.character M H hH θ).inverse
  let χ := (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).inverse
  have hχ : ∀n,elementCoeff χ n=rowTwist (HeckeRowClosure.elementHom η) rowMaskElement 1 u.val n :=
    HeckePrimeNonprincipal.inverse_twist_elementCoeff _ _ _ _ _ _ (rawRow_elementCoeff u)
  intro hp
  have hprincipal : χ.residue=1 := by
    change (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue⁻¹=1
    exact congrArg Inv.inv hp |>.trans inv_one
  have hfixed := HeckeRowNonprincipal.principal_row_fixed_support η χ rowMaskElement 1 u.val
    rowMaskElement_ne_zero (dvd_mul_left _ _) (dvd_mul_right _ _) v⁻¹ 0 0 r hr hv hx hχ hprincipal
    (fun P _=> hspan.symm ▸ u.property.2 P)
  have hη : η.modulus=M := inverse_twist_base_modulus M H hH θ
  rw [hη] at hfixed
  have hn := HeckeExceptionalRows.row_norm_bound (fixedTwistSupport M) (fixedTwistSupport_prime M) hfixed
  rw [hspan] at hn
  exact not_lt_of_ge (show rowNorm u≤(HeckeExceptionalRows.bound (fixedTwistSupport M):ℝ) by unfold rowNorm;exact_mod_cast hn) hl

theorem raw_twisted_conductor (u : FreeRow) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm≤
      conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm := by
  have ht := HeckePrimeScale.twisted_modulus_bound M H hH (rawRow u).inverse θ
  change _≤(rawRow u).modulus.absNorm*M.absNorm at ht
  exact ht.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using
    Nat.mul_le_mul_right M.absNorm (rawRow_conductor u))
omit [NeZero M] in
theorem canonical_amplitude_raw (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (W : ℝ→ℂ) (a b D : ℝ)
    (hD : 0< D) (hW : Function.support W⊆Set.Ioo a b)
    (hsmall : ∀P∈S,(P.absNorm:ℝ)≤ a*D) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H u.val W b D z=
      HeckePrimeRay.rayPrimePolynomial M H (rawRow u).inverse W b D (1-z.re) z.im := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude HeckePrimeRay.rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  have hp := (Finset.mem_filter.mp hP).2.1
  have he : -HeckeDyadic.shift (1-z.re) z.im=z-1 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  simp only [HeckePrimeAnnular.annularWeight,he]
  by_cases hw : W ((P.absNorm:ℝ)/D)=0
  · simp [hw]
  have hPS : P∉S := by
    intro hPS
    have hh := (lt_div_iff₀ hD).mp (hW hw).1
    have := hsmall P hPS
    linarith
  rw [idealCoeff_inverse_conj,rawRow_prime_outside S hS hbad u ⟨P,hp⟩ hPS]
  exact mul_assoc _ _ _

omit H hH in
theorem large_supported_twists_eventually (d : ℝ) (hd : 0< d) :
    ∀ᶠZ : ℝ in Filter.atTop,∀u : FreeRow,Z^d≤ rowNorm u →
      Supported (Ideal.span {u.val}) → ∀(H : Subgroup (O ⧸ M)ˣ)
      (hH : RayOrthogonality.globalUnits M≤ H) (θ : RayQuotient.Characters M H),
      (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue≠1 := by
  filter_upwards [(tendsto_rpow_atTop hd).eventually
    (Filter.eventually_gt_atTop (HeckeExceptionalRows.bound (fixedTwistSupport M):ℝ))]
    with Z hZ u hu hs H hH θ
  exact large_supported_twists_nonprincipal M H hH u hs (hZ.trans_le hu) θ

omit M H hH in
theorem source_maximum_dominates {ι : Type*} [Fintype ι]
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) (u : FreeRow)
    (ψ : ι→ Character) (T : ℝ) :
    detectorMaximum ψ T≤ detectorMaximum (sourceDetectorFamily S hS η u ψ) T := by
  rcases lt_or_ge (51/100:ℝ) (detectorMaximum ψ T) with hm|hm
  · obtain ⟨j,s,hz,hpole,ht,heq⟩ := detectorMaximum_attained ψ T hm
    rw [←heq]
    exact detector_zero_re_le_maximum (sourceDetectorFamily S hS η u ψ) T (Sum.inr j)
      (by rw [heq];exact hm.le) ht hz hpole
  · exact hm.trans (detectorMaximum_bounds _ T).1

omit M H hH in
theorem source_nonprincipal_maximum_dominates {ι : Type*} [Fintype ι]
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) (u : FreeRow)
    (ψ : ι→ Character) (hψ : ∀j,(ψ j).residue≠1) (T : ℝ) :
    HeckeDetectorZeros.zeroMaximum ψ hψ T≤ detectorMaximum (sourceDetectorFamily S hS η u ψ) T := by
  rw [←detectorMaximum_eq_nonprincipal ψ hψ T]
  exact source_maximum_dominates S hS η u ψ T

end ProbeRayCharacterFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators
namespace ProbeCentralExponent

def sourceExponent (a d R q : ℝ) : ℝ :=
  (17/48)*(1/2-17/50)+a+17/50-1-a*(23/48)-d*(17/50)+d*R+
    d*(a-1/2)+(1/6)*(17/50-1/2+q)

def relativeExponent (δ d R q : ℝ) : ℝ :=
  -1/48+(2/3)*δ+q/6-(13/16)*(1-R)+(d-13/16)*(R+δ/2-17/50)

lemma original_exponent_identity (a d R q : ℝ) :
    sourceExponent a d R q=3/16+relativeExponent (2*a-1) d R q := by
  unfold sourceExponent relativeExponent
  ring

lemma frequency_slope_bounds (δ R : ℝ) (_hδ : 0≤δ) (hδ1 : δ≤1)
    (hRlo : 1-δ≤ R) (hRhi : R≤139/96) :
    4/25≤ R+δ/2-17/50 ∧ R+δ/2-17/50≤2 := by
  constructor <;> linarith

lemma relative_extend (δ d R q ζ : ℝ) (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤ R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    relativeExponent δ d R q≤ relativeExponent δ (13/16) R q+2*ζ := by
  have hh := mul_le_mul_of_nonneg_right (show d-13/16≤ζ by linarith) hslo
  have hh' := mul_le_mul_of_nonneg_left hshi hζ
  unfold relativeExponent
  nlinarith

lemma balanced_source_margin (δ x R Δ loss ζ d : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤5/6) (hx : 0≤ x) (hx1 : x≤1/2)
    (hR : R≤ Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤ R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    sourceExponent ((1+δ)/2) d R (δ*x)-(3/16+Δ)≤
      -49/440640-(51/64)*Δ+(13/16)*loss+2*ζ := by
  have hb := Endpoint.balanced_endpoint_margin hδ hδ1
    (show 0≤1/2-x by linarith) (show 1/2-x≤1/2 by linarith)
  have he := relative_extend δ d R (δ*x) ζ hζ hd hslo hshi
  rw [original_exponent_identity]
  have hid : 2*((1+δ)/2)-1=δ := by ring
  rw [hid]
  unfold Endpoint.balancedExponent at hb
  unfold relativeExponent at he ⊢
  nlinarith

lemma high_source_margin (δ R q Δ loss ζ d : ℝ)
    (hq : q≤δ/2) (hR : R≤1-δ+loss)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤ R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    sourceExponent ((1+δ)/2) d R q-(3/16+Δ)≤
      -1/48-δ/16-Δ+(13/16)*loss+2*ζ := by
  have he := relative_extend δ d R q ζ hζ hd hslo hshi
  rw [original_exponent_identity]
  have hid : 2*((1+δ)/2)-1=δ := by ring
  rw [hid]
  unfold relativeExponent at he ⊢
  nlinarith

lemma floor_source_margin (q Δ ζ d : ℝ) (hq : q≤1/100)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ) :
    sourceExponent (51/100) d 1 q-(3/16+Δ)≤-7/1200-Δ+2*ζ := by
  have he := relative_extend (1/50) d 1 q ζ hζ hd (by norm_num) (by norm_num)
  rw [original_exponent_identity]
  norm_num only at *
  unfold relativeExponent at he ⊢
  nlinarith

lemma intermediate_source_margin (δ q Δ d : ℝ) (_hδ : 0≤δ) (hδ1 : δ≤5/6)
    (hq : q≤δ/2) (hd : d≤1/2) :
    sourceExponent ((1+δ)/2) d (76/75-(2/3)*δ) q-(3/16+Δ)≤-49/14400-Δ := by
  have hs : 0≤(76/75-(2/3)*δ)+δ/2-17/50 := by linarith
  have hm := mul_le_mul_of_nonneg_right hd hs
  unfold sourceExponent
  nlinarith

def realLoss (N : ℕ) (d e eps heightLoss mesh : ℝ) : ℝ :=
  (105/8)*e+12*d*e+d*eps*(N+8)+heightLoss+mesh/6

lemma realLoss_bound (N : ℕ) (d e eps heightLoss mesh : ℝ)
    (hd : d≤1) (he : 0≤ e) (heps : 0≤ eps) :
    realLoss N d e eps heightLoss mesh≤26*e+(N+8)*eps+heightLoss+mesh/6 := by
  have h1 := mul_le_mul_of_nonneg_right hd he
  have h2 := mul_le_mul_of_nonneg_right hd (show 0≤ eps*(N+8) by positivity)
  unfold realLoss
  nlinarith

lemma physical_scale_identity (Z a e : ℝ) (hZ : 0< Z) :
    (Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e)=
      Z^((25/48)*a-181/300+(105/8)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring
end ProbeCentralExponent

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeCentralBranchProduct

theorem coupled_product_bound {ι : Type*} [Fintype ι]
    (L R : ℝ) (f g y : ι→ℝ) (hf : ∀i,0≤ f i)
    (hsub : ∀J : Finset ι,L*(∏j ∈ J,g j)≤ R*(∏j ∈ J,y j)) :
    L*(∏j : ι, (f j+g j))≤ R*(∏j : ι, (f j+y j)) := by
  rw [Finset.prod_add,Finset.prod_add,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro J hJ
  calc
    _ = (∏j ∈ J,f j)*(L*∏j ∈ Finset.univ\J,g j) := by ring
    _ ≤ (∏j ∈ J,f j)*(R*∏j ∈ Finset.univ\J,y j) :=
      mul_le_mul_of_nonneg_left (hsub _) (Finset.prod_nonneg (fun j _=> hf j))
    _ = _ := by ring

theorem three_branch_bound {N : ℕ} (L R E : ℝ)
    (A B T : Fin N→ℂ) (y p : Fin N→ℝ)
    (hL : 0≤ L) (hR : 0≤ R) (hE : 0≤ E) (hy : ∀j,0≤ y j) (hp : ∀j,1≤ p j)
    (hA : ∀j,‖A j‖≤ y j*p j) (hB : ∀j,‖B j‖≤ y j*E)
    (hT : ∀J : Finset (Fin N),L*(∏j ∈ J,‖T j‖)≤ R*(∏j ∈ J,y j)) :
    L*‖∏j : Fin N, (A j+B j+T j)‖≤ R*(E+2)^N*(∏j : Fin N, y j)*(∏j : Fin N,p j) := by
  have hnorm : ‖∏j : Fin N, (A j+B j+T j)‖≤∏j : Fin N,((‖A j‖+‖B j‖)+‖T j‖) := by
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _=> norm_nonneg _)
    intro j _
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hc := coupled_product_bound L R (fun j=>‖A j‖+‖B j‖) (fun j=>‖T j‖) y
    (fun j=> add_nonneg (norm_nonneg _) (norm_nonneg _)) hT
  have hpoint (j : Fin N) : (‖A j‖+‖B j‖)+y j≤ y j*((E+2)*p j) := by
    have h := hp j
    have hp0 : 0≤ p j := zero_le_one.trans h
    have he := mul_nonneg (show 0≤ E+1 by linarith) (show 0≤ p j-1 by linarith)
    have hm := mul_nonneg (hy j) he
    nlinarith [hA j,hB j]
  calc
    _ ≤ L*(∏j : Fin N,((‖A j‖+‖B j‖)+‖T j‖)) := mul_le_mul_of_nonneg_left hnorm hL
    _ ≤ R*(∏j : Fin N,((‖A j‖+‖B j‖)+y j)) := hc
    _ ≤ R*(∏j : Fin N, y j*((E+2)*p j)) := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.prod_le_prod (fun j _=> add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (hy j)) (fun j _=> hpoint j)
    _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin];ring
end ProbeCentralBranchProduct

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeCentralRepeatedChoices
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
local notation "O" => Eisenstein.O

def activeChoices {k : ℕ} (u : FreeRow) (T : Fin k→ Finset HeckeIdealSeries.PrimeIdeal)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) : Finset (∀j,T j) :=
  Finset.univ.filter (fun P=>∀j,repeatedRowPrime u (P j).val ∧
    W j (((P j).val.val.absNorm:ℝ)/Y j)≠0)

lemma active_card_le_divisors {k : ℕ} (u : FreeRow) (T : Fin k→ Finset HeckeIdealSeries.PrimeIdeal)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) :
    (activeChoices u T W Y).card≤(idealDivisors (Ideal.span {u.val})).card^k := by
  let U : Ideal O := Ideal.span {u.val}
  have hU : U≠0 := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  let f : activeChoices u T W Y→(Fin k→ idealDivisors U) :=
    fun P j=>⟨(P.val j).val.val,(mem_idealDivisors hU).mpr
      (((Finset.mem_filter.mp P.property).2 j).1.1)⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    funext j
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun g=>(g j).val) h
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using hc

theorem active_card_subpower (N : ℕ) (eps : ℝ) (heps : 0< eps) :
    ∃C : ℝ,0< C ∧ ∀k : ℕ,k≤ N → ∀(u : FreeRow) (T : Fin k→ Finset HeckeIdealSeries.PrimeIdeal)
      (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),
      ((activeChoices u T W Y).card:ℝ)≤ C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps := by
  let δ := eps/(N+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨(max 1 D)^N,by positivity,?_⟩
  intro k hk u T W Y
  have hU : (Ideal.span {u.val}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  have hU1 : (1:ℝ)≤(Ideal.span {u.val}:Ideal O).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU)
  have hd := hdiv (Ideal.span {u.val}) hU
  have hcard : ((activeChoices u T W Y).card:ℝ)≤
      ((idealDivisors (Ideal.span {u.val})).card:ℝ)^k := by
    exact_mod_cast active_card_le_divisors u T W Y
  have hpow : D^k≤(max 1 D)^N :=
    (pow_le_pow_left₀ hD.le (le_max_right 1 D) k).trans (pow_le_pow_right₀ (le_max_left 1 D) hk)
  have hke : δ*k≤ eps := by
    have hn : (k:ℝ)≤ N := by exact_mod_cast hk
    have he : δ*(N+1)=eps := by dsimp [δ];field_simp
    nlinarith
  calc
    _ ≤ ((idealDivisors (Ideal.span {u.val})).card:ℝ)^k := hcard
    _ ≤ (D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ)^k := pow_le_pow_left₀ (by positivity) hd k
    _ = D^k*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(δ*k) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
    _ ≤ _ := mul_le_mul hpow (Real.rpow_le_rpow_of_exponent_le hU1 hke)
      (by positivity) (by positivity)

lemma sum_products_restrict {k : ℕ} (η : Character) (u : FreeRow)
    (T : Fin k→ Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀j P,P∈T j→ _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported P.val)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) (x w z : ℂ) :
    (∏j,∑P:T j,‖W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hT j P.val P.property) x w z‖)=
    ∑P∈activeChoices u T W Y,∏j,‖W j (((P j).val.val.absNorm:ℝ)/Y j)*((P j).val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u (P j).val (hT j (P j).val (P j).property) x w z‖ := by
  rw [Fintype.prod_sum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro P _ hp
  have hn : ¬∀j,repeatedRowPrime u (P j).val ∧ W j (((P j).val.val.absNorm:ℝ)/Y j)≠0 := by
    simpa only [activeChoices,Finset.mem_filter,Finset.mem_univ,true_and] using hp
  push_neg at hn
  obtain ⟨j,hj⟩ := hn
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  by_cases hr : repeatedRowPrime u (P j).val
  · simp [hj hr]
  · simp [centralRepeatedTerm,hr]
end ProbeCentralRepeatedChoices

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeCentralRepeatedSum
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve ProbeCentralRepeatedProduct ProbeCentralRepeatedChoices
open ProbeSelectedPrimeSums
local notation "O" => Eisenstein.O

theorem actual_repeated_sum (N : ℕ) (e eps c d B : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps)
    (hc : 0< c) (hd : 0< d) (hB : 0≤ B) :
    ∃C : ℝ,0< C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→ Character)
      (T0 a : ℝ) (i : ℕ),2< T0 → 51/100≤ a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)< a+2*e →
    ∀(k : ℕ),k≤ N → ∀(T : Fin k→ Finset HeckeIdealSeries.PrimeIdeal)
      (hs : ∀j P,P∈T j→ Supported P.val),
      (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
      (∀j P,P∈T j→ IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤ P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),
      (∀j,1≤ Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤ B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        (∏j,∑P:T j,‖W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u P.val (hs j P.val P.property) x w z‖) ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏j,(Y j)^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hprod⟩ := selected_repeated_product e eps he he1 heps
  obtain ⟨D,hD,hcount⟩ := active_card_subpower N eps heps
  let A := annularPower c d (-(4/25:ℝ))
  let E := (max 1 (812*B*A))^N
  have hA : 0≤ A := annularPower_nonneg c d _ hc
  have hE : 0< E := by dsimp [E];positivity
  refine ⟨D*C*E,by positivity,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin k hk T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi
  let R := rowCost S hS u a e eps ((3*i+2:ℕ)*T0)
  let L := ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖
  have hR : 0≤ R := rowCost_nonneg _ _ _ _ _ _ _
  have hY0 (j : Fin k) : 0< Y j := zero_lt_one.trans_le (hY j)
  have hYY : 0≤∏j,(Y j)^(-(4/25:ℝ)) := Finset.prod_nonneg (fun j _=> Real.rpow_nonneg (hY0 j).le _)
  have hterm (P : ∀j,T j) (hP : P∈activeChoices u T W Y) :
      L*(∏j,‖W j (((P j).val.val.absNorm:ℝ)/Y j)*((P j).val.val.absNorm:ℂ)^(z-1)*
        centralRepeatedTerm η u (P j).val (hs j (P j).val (P j).property) x w z‖)≤
      C*E*R*∏j,(Y j)^(-(4/25:ℝ)) := by
    have hp := (Finset.mem_filter.mp hP).2
    have hb := hprod S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin k
      (fun j=>(P j).val) (fun j=> hs j (P j).val (P j).property) (hdis P)
      (fun j=> hη j (P j).val (P j).property) (fun j=> hQ j (P j).val (P j).property)
      (fun j=> hsmall j (P j).val (P j).property) (fun j=>(hp j).1)
      B W Y hB hW x w z hx hw hz hwi
    have hpow : (∏j,((P j).val.val.absNorm:ℝ)^(z.re-1/2))≤ A^k*∏j,(Y j)^(-(4/25:ℝ)) := by
      have hh := Finset.prod_le_prod (s:=Finset.univ) (fun j _=> Real.rpow_nonneg (show (0:ℝ)≤(P j).val.val.absNorm by positivity) (-(4/25:ℝ)))
        (fun j (_:j∈Finset.univ)=> annular_rpow c d (Y j) ((P j).val.val.absNorm:ℝ) (-(4/25:ℝ)) hc hd (hY0 j)
          ((le_div_iff₀ (hY0 j)).mp (hWS j (hp j).2).1)
          ((div_le_iff₀ (hY0 j)).mp (hWS j (hp j).2).2))
      norm_num only [hz,show (17/50:ℝ)-1/2=-(4/25:ℝ) by norm_num] at ⊢
      simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
    have hEbound : (812*B)^k*A^k≤ E := by
      rw [←mul_pow]
      exact (pow_le_pow_left₀ (by positivity) (le_max_right 1 (812*B*A)) k).trans
        (pow_le_pow_right₀ (le_max_left 1 _) hk)
    calc
      _ ≤ C*(812*B)^k*R*∏j,((P j).val.val.absNorm:ℝ)^(z.re-1/2) := hb
      _ ≤ C*(812*B)^k*R*(A^k*∏j,(Y j)^(-(4/25:ℝ))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = C*((812*B)^k*A^k)*R*∏j,(Y j)^(-(4/25:ℝ)) := by ring
      _ ≤ _ := by gcongr
  rw [sum_products_restrict η u T hs W Y x w z,Finset.mul_sum]
  have hh := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  apply hh.trans
  calc
    _ ≤ (D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps)*(C*E*R*∏j,(Y j)^(-(4/25:ℝ))) :=
      mul_le_mul_of_nonneg_right (hcount k hk u T W Y) (by positivity)
    _ = _ := by dsimp [R];ring
end ProbeCentralRepeatedSum

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeCentralRepeatedSubset
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve ProbeCentralRepeatedProduct ProbeCentralRepeatedSum
local notation "O" => Eisenstein.O

theorem actual_repeated_subset (N : ℕ) (e eps c d B : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps)
    (hc : 0< c) (hd : 0< d) (hB : 0≤ B) :
    ∃C : ℝ,0< C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→ Character)
      (T0 a : ℝ) (i : ℕ),2< T0 → 51/100≤ a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)< a+2*e →
    ∀(T : Fin N→ Finset HeckeIdealSeries.PrimeIdeal) (hs : ∀j P,P∈T j→ Supported P.val),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→ IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤ P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤ Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤ B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀J : Finset (Fin N),
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        (∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖) ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏j:J,(Y j.val)^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hmain⟩ := actual_repeated_sum N e eps c d B he he1 heps hc hd hB
  refine ⟨C,hC,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi J
  let k := Fintype.card J
  let E : J≃Fin k := Fintype.equivFin J
  let idx : Fin k→ Fin N := fun j=>(E.symm j).val
  have hi : Function.Injective idx := fun j l h=> E.symm.injective (Subtype.ext h)
  have hk : k≤ N := by
    dsimp [k]
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using J.card_le_univ
  have hd' (P : ∀j,T (idx j)) : Function.Injective (fun j=>(P j).val) := by
    intro j l heq
    change (P j).val=(P l).val at heq
    by_contra hne
    have hdiff : idx j≠idx l := fun h=> hne (hi h)
    exact Finset.disjoint_left.mp (hdis _ _ hdiff) (P j).property (by rw [heq];exact (P l).property)
  have hb := hmain S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin k hk
    (fun j=> T (idx j)) (fun j P hP=> hs (idx j) P hP) hd'
    (fun j P hP=> hη (idx j) P hP) (fun j P hP=> hQ (idx j) P hP)
    (fun j P hP=> hsmall (idx j) P hP) (fun j=> W (idx j)) (fun j=> Y (idx j))
    (fun j=> hY (idx j)) (fun j=> hWS (idx j)) (fun j=> hW (idx j)) x w z hx hw hz hwi
  have hleft : (∏j:Fin k,∑P:T (idx j),‖W (idx j) ((P.val.val.absNorm:ℝ)/Y (idx j))*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hs (idx j) P.val P.property) x w z‖)=
      ∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖ :=
    Fintype.prod_equiv E.symm _ _ (fun _=> rfl)
  have hright : (∏j:Fin k,(Y (idx j))^(-(4/25:ℝ)))=∏j:J,(Y j.val)^(-(4/25:ℝ)) :=
    Fintype.prod_equiv E.symm _ _ (fun _=> rfl)
  rw [hleft,hright] at hb
  exact hb
end ProbeCentralRepeatedSubset

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeCentralAllSlots
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion ProbeCentralRepeatedProduct
open ProbeCentralRepeatedSubset ProbeCentralBranchProduct
local notation "O" => Eisenstein.O

/-- The prime sum carrying the normalized cubic row phase. -/
def phaseSlot (u : FreeRow) (T : Finset HeckeIdealSeries.PrimeIdeal) (W : ℝ→ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  ∑P:T,W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*(-star (idealRowHom u.val P.val.val))

theorem actual_three_branch_slots (N : ℕ) (e eps c d B : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps)
    (hc : 0< c) (hd : 0< d) (hB : 0≤ B) :
    ∃C : ℝ,0< C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→ Character)
      (T0 a : ℝ) (i : ℕ),2< T0 → 51/100≤ a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)< a+2*e →
    ∀(T : Fin N→ Finset HeckeIdealSeries.PrimeIdeal) (hs : ∀j P,P∈T j→ Supported P.val),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→ IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤ P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤ Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤ B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀p : Fin N→ℝ,(∀j,1≤ p j) → (∀j,‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j) →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ‖∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u P.val (hs j P.val P.property) x w z‖ ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by
  obtain ⟨Cr,hCr,hregular⟩ := central_regular_slot_sum eps c d B heps hc hd hB
  obtain ⟨Ct,hCt,hrepeated⟩ := actual_repeated_subset N e eps c d B he he1 heps hc hd hB
  refine ⟨Ct*(Cr+2)^N,by positivity,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi p hp hphase
  let L := ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖
  let U : ℝ := (Ideal.span {u.val}:Ideal O).absNorm
  let R := Ct*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*U^eps
  let A : Fin N→ℂ := fun j=> phaseSlot u (T j) (W j) (Y j) z
  let E : Fin N→ℂ := fun j=>∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
    centralRegularError η u P.val (hs j P.val P.property) x w z
  let F : Fin N→ℂ := fun j=>∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
    centralRepeatedTerm η u P.val (hs j P.val P.property) x w z
  let yy : Fin N→ℝ := fun j=>(Y j)^(-(4/25:ℝ))
  have hU : 1≤ U := by dsimp [U];exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hUp : 1≤ U^eps := Real.one_le_rpow hU heps.le
  have hR : 0≤ R := by dsimp [R];exact mul_nonneg (mul_nonneg hCt.le (rowCost_nonneg _ _ _ _ _ _ _)) (Real.rpow_nonneg (zero_le_one.trans hU) _)
  have hyy (j : Fin N) : 0≤ yy j := Real.rpow_nonneg (zero_le_one.trans (hY j)) _
  have hE (j : Fin N) : ‖E j‖≤ yy j*(Cr*U^eps) := by
    have hb := hregular η u (T j) (fun P hP=>⟨hs j P hP,hQ j P hP,hη j P hP⟩)
      (Y j) (hY j) (W j) (hWS j) (hW j) a e x w z ha ha1 he he1.le hx hw hz (hsmall j)
    exact (norm_sum_le _ _).trans (hb.trans_eq (by dsimp [yy,U];ring))
  have hF (J : Finset (Fin N)) : L*(∏j∈J,‖F j‖)≤ R*(∏j∈J,yy j) := by
    have hb := hrepeated S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall
      W Y hY hWS hW x w z hx hw hz hwi J
    have hp' : (∏j:J,‖F j.val‖)≤∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*
        (P.val.val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖ := by
      apply Finset.prod_le_prod (fun _ _=> norm_nonneg _)
      intro j _
      exact norm_sum_le _ _
    have hh := (mul_le_mul_of_nonneg_left hp' (show 0≤ L from norm_nonneg _)).trans hb
    rw [Finset.prod_coe_sort J (fun j=>‖F j‖),
      Finset.prod_coe_sort J (fun j=>(Y j)^(-(4/25:ℝ)))] at hh
    exact hh
  have hb := three_branch_bound L R (Cr*U^eps) A E F yy p (norm_nonneg _) hR (by positivity) hyy hp hphase hE hF
  have heq : (∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralNormalizedSlot η u P.val (hs j P.val P.property) x w z)=∏j,(A j+E j+F j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [A,E,F,phaseSlot,centralNormalizedSlot_split,mul_add,Finset.sum_add_distrib]
  rw [heq]
  apply hb.trans
  have hcoef : (Cr*U^eps+2)^N≤(Cr+2)^N*U^(eps*N) := by
    have hh : Cr*U^eps+2≤(Cr+2)*U^eps := by nlinarith
    have hp' := pow_le_pow_left₀ (show 0≤ Cr*U^eps+2 by positivity) hh N
    rw [mul_pow] at hp'
    have heq : (U^eps)^N=U^(eps*N) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hU)]
    rwa [heq] at hp'
  have hyprod : 0≤∏j,yy j := Finset.prod_nonneg (fun j _=> hyy j)
  have hpprod : 0≤∏j,p j := Finset.prod_nonneg (fun j _=> zero_le_one.trans (hp j))
  calc
    _ ≤ R*((Cr+2)^N*U^(eps*N))*(∏j,yy j)*(∏j,p j) := by gcongr
    _ = _ := by
      dsimp [R,yy]
      have hh : U^eps*U^(eps*N)=U^(eps*(N+1)) := by rw [←Real.rpow_add (zero_lt_one.trans_le hU)];congr 1;ring
      calc
        _ = Ct*(Cr+2)^N*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*(U^eps*U^(eps*N))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by ring
        _ = _ := by rw [hh]
end ProbeCentralAllSlots

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace ProbeRayPhaseBins
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbeRayCharacterFamily
open HeckePrimeAmplitudeBins ProbeRaySlots
local notation "O" => Eisenstein.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The canonical ray amplitude admits bins controlled by the detector maximum. -/
theorem actual_phase_bins (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0< A) (hAB : A≤ B)
    (hWs : Function.support W⊆Ioo A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ cost mesh σmin σmax δ : ℝ)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0< e) (he' : e<1/1000)
    (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤ d → d≤ dmax → 2≤ Z^d → 2< Z^τ →
    ∀(η : Character) (u : FreeRow),Z^δ≤ rowNorm u →
      _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported (Ideal.span {u.val}) →
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^d →
    ∀(a : ℝ) (i : ℕ),51/100≤ a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u
        (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse)) (3*(i+1:ℕ)*Z^τ)< a+2*e →
    ∀(r : ℝ) (z : ℂ),rmin≤ r → r≤ R → σmin≤1-z.re → 1-z.re≤σmax →
      |z.im|+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^cost →
    let D := (Z^d)^r
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H u.val W B D z
    let g := amplitude D (a-1/2) mesh Q
    0≤ g ∧ g≤ a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤ D^(g+mesh) ∧ (0< g → (Z^d)^(2*r*g)≤‖Q‖^2) ∧
      ‖∑P∈pool (RayQuotient.identityClass M H) S A B D,
        W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val))‖≤ D^(z.re-1/2+g+mesh) := by
  have hb := HeckePrimeAmplitudeActual.ray_amplitude_bins M H hH W A B hA
    (hWs.trans Ioo_subset_Icc_self) hW R dmin dmax rmin τ ε e κ cost mesh σmin σmax
    hR hdmin hdmax hrmin hτ hε he he' hκ hcost hmesh hbudget hgap
  have hn := large_supported_twists_eventually M δ hδ
  have ht := ProbeRaySlots.power_fixed_exclusions S A (dmin*rmin) hA (mul_pos hdmin hrmin)
    (fun p : {p : ℝ×ℝ // dmin≤ p.1 ∧ rmin≤ p.2}=> p.val.1*p.val.2)
    (fun p=> mul_le_mul p.property.1 p.property.2 hrmin.le (hdmin.trans_le p.property.1).le)
  filter_upwards [hb,hn,ht,eventually_ge_atTop (1:ℝ)] with Z hb hn ht hZ
  intro d hd hd' hU hT η u hu hs hcond a i ha ha' hbin r z hr hr' hσ hσ' hf hh
  have hZp : 0< Z := zero_lt_one.trans_le hZ
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _
  have hsmall : ∀P∈S,(P.absNorm:ℝ)≤ A*(Z^d)^r := by
    intro P hP
    rw [←Real.rpow_mul hZp.le]
    exact ht ⟨(d,r),hd,hr⟩ P hP
  have hnp := hn u hu hs H hH
  have hzmax := (source_nonprincipal_maximum_dominates S hS η u
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse) hnp _).trans_lt hbin
  have hq (θ : RayQuotient.Characters M H) :
      ((HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm:ℝ)≤ Z^d :=
    (show ((HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm:ℝ)≤
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ) by
        exact_mod_cast raw_twisted_conductor M H hH u θ).trans hcond
  have heq := canonical_amplitude_raw M H S hS hbad u W A B ((Z^d)^r) hD hWs hsmall z
  have hbins := hb d hd hd' hU hT (rawRow u).inverse hnp a i ha ha' hzmax
    r (1-z.re) z.im hr hr' hσ hσ' hq hf hh
  rw [←heq] at hbins
  refine ⟨hbins.1,hbins.2.1,hbins.2.2.1,hbins.2.2.2.1,hbins.2.2.2.2,?_⟩
  rw [central_phase_norm M H S u.val W A B ((Z^d)^r) hA hAB hD hWs hsmall z]
  calc
    _ ≤ ((Z^d)^r)^(z.re-1/2)*((Z^d)^r)^(_+mesh) :=
      mul_le_mul_of_nonneg_left hbins.2.2.2.1 (Real.rpow_nonneg hD.le _)
    _ = _ := by rw [←Real.rpow_add hD];congr 1;ring
end ProbeRayPhaseBins

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
