/-
The cubic multiplier product law is adapted from OpenAI’s formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheRamifiedCubicPhaseLivesModuloNine
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Index

/-!
# A nontrivial cubic character on the level-three group

Cubic reciprocity and the ramified denominator law show that `(c/a)₃` is
multiplicative on determinant-one matrices congruent to the identity modulo
three. A prime-factor shift removes the auxiliary coprimality restriction.
An explicit matrix has value `ω`, so the character maps onto all cubic roots.
Its kernel has index three in the level-three group and finite index in `SL₂(O)`.
-/

noncomputable section
open scoped BigOperators Classical MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent
namespace CubicJacobi
open Eisenstein CubicRamified
private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

lemma primary_isUnit_eq_one (a : O) (ha : IsUnit a) (hprimary : lambda ^ 2 ∣ a-1) : a = 1 := by
  obtain ⟨u,rfl⟩ := ha
  exact primary_unit_eq_one u hprimary

theorem primary_mul (a b : O) (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) :
    lambda ^ 2 ∣ a*b-1 := by
  have h := dvd_add (dvd_mul_of_dvd_left ha b) hb
  convert h using 1 ; ring

theorem primary_add_multiple_three (a c t : O) (ha : lambda ^ 2 ∣ a-1) :
    lambda ^ 2 ∣ (a+3*t*c)-1 := by
  have h := dvd_add ha (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left lambda_sq_dvd_three t) c)
  convert h using 1 ; ring

/-- The determinant relation and denominator congruence give the product law when cancellation is available. -/
theorem kubota_mul_of_isCoprime (a b c d e g : O)
    (hdet : a*d-b*c=1) (ha : lambda ^ 2 ∣ a-1) (he : lambda ^ 2 ∣ e-1)
    (hb : (3 : O) ∣ b) (hg : (3 : O) ∣ g) (hag : IsCoprime a g) :
    symbol (c*e+d*g) (a*e+b*g) = symbol c a * symbol g e := by
  let productA := a*e+b*g
  let productC := c*e+d*g
  have hA : lambda ^ 2 ∣ productA-1 := by
    have h := dvd_add (primary_mul a e ha he)
      (dvd_mul_of_dvd_left (lambda_sq_dvd_three.trans hb) g)
    convert h using 1 ; dsimp [productA] ; ring
  have hrelation : a*productC-c*productA=g := by
    dsimp [productA,productC]
    linear_combination g*hdet
  have hcop : IsCoprime a productA := by
    obtain ⟨r,s,hrs⟩ := hag
    refine ⟨r+s*productC,-s*c,?_⟩
    linear_combination hrs + s*hrelation
  have hnonzero := symbol_ne_zero_of_isCoprime a productA hA hcop
  have h1 : symbol a productA * symbol productC productA = symbol g productA := by
    rw [← symbol_mul_numerator _ _ productA]
    exact symbol_congr ⟨c, by linear_combination hrelation⟩
  have h2 : symbol a productA * symbol c a = symbol g a := by
    rw [symbol_reciprocity a productA ha hA,
      ← symbol_mul_numerator _ _ a]
    calc
      symbol (productA*c) a = symbol (-g) a := by
        apply symbol_congr
        refine ⟨productC,?_⟩
        linear_combination -hrelation
      _ = symbol g a := symbol_neg_numerator g a ha
  have h3 : symbol g productA = symbol g a * symbol g e := by
    rw [← symbol_mul_denominator]
    apply symbol_denominator_congr g productA (a*e) hA (primary_mul a e ha he)
    · obtain ⟨b0,hb0⟩ := hb
      obtain ⟨g0,hg0⟩ := hg
      refine ⟨b0*g0,?_⟩
      dsimp [productA]
      rw [hb0,hg0]
      ring
    · exact ⟨b,by dsimp [productA];ring⟩
  change symbol productC productA = _
  apply mul_left_cancel₀ hnonzero
  rw [h1,h3,← h2]
  ring

lemma three_dvd_primary_sub_one (a : O) (ha : lambda ^ 2 ∣ a-1) : (3 : O) ∣ a-1 := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  rw [primaryCoord_eq]
  exact ⟨(A : O)+(B : O)*omega,by ring⟩

/-- A product of selected prime factors shifts the upper row into coprime position. -/
theorem exists_coprime_three_shift (a c g : O)
    (ha : lambda ^ 2 ∣ a-1) (hac : IsCoprime a c) (hg0 : g ≠ 0) :
    ∃ t : O, IsCoprime (a+3*t*c) g := by
  classical
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := (UniqueFactorizationMonoid.normalizedFactors g).filter (fun p => ¬p ∣ a)
  refine ⟨s.prod, ?_⟩
  apply IsCoprime.symm
  apply isCoprime_of_prime_dvd (by rintro ⟨h,-⟩; exact hg0 h)
  intro p hp hpg hpnew
  by_cases hpa : p ∣ a
  · have hp3 : ¬p ∣ (3 : O) := by
      intro h3
      have hsub : p ∣ a-1 := h3.trans (three_dvd_primary_sub_one a ha)
      have hone : p ∣ (1 : O) := by
        convert dvd_sub hpa hsub using 1 ; ring
      exact hp.not_dvd_one hone
    have hpc : ¬p ∣ c := by
      intro hpc
      exact hp.2.1 (hac.isUnit_of_dvd' hpa hpc)
    have hps : ¬p ∣ s.prod := by
      intro hdiv
      obtain ⟨q,hqs,hpq⟩ := hp.exists_mem_multiset_dvd hdiv
      have hqs' : q ∈ UniqueFactorizationMonoid.normalizedFactors g ∧ ¬q ∣ a :=
        Multiset.mem_filter.mp hqs
      have hqprime := UniqueFactorizationMonoid.prime_of_normalized_factor q hqs'.1
      have hqp : q ∣ p := (hp.associated_of_dvd hqprime hpq).dvd'
      exact hqs'.2 (hqp.trans hpa)
    have hpterm : p ∣ 3*s.prod*c := by
      convert dvd_sub hpnew hpa using 1 ; ring
    rcases hp.dvd_or_dvd hpterm with hleft | hright
    · rcases hp.dvd_or_dvd hleft with h3 | hs
      · exact hp3 h3
      · exact hps hs
    · exact hpc hright
  · obtain ⟨q,hq,hpq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
      hg0 hp.irreducible hpg
    have hqa : ¬q ∣ a := fun hqa => hpa (hpq.dvd.trans hqa)
    have hqs : q ∈ s := Multiset.mem_filter.mpr ⟨hq,hqa⟩
    have hps : p ∣ s.prod := hpq.dvd.trans (Multiset.dvd_prod hqs)
    have hpterm : p ∣ 3*s.prod*c :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hps 3) c
    have hpa' : p ∣ a := by
      convert dvd_sub hpnew hpterm using 1 ; ring
    exact hpa hpa'

/-- A level-three row operation preserves the cubic multiplier. -/
lemma symbol_three_shift (c a t : O) (ha : lambda ^ 2 ∣ a-1) (hc : (3 : O) ∣ c) :
    symbol c (a+3*t*c) = symbol c a := by
  apply symbol_denominator_congr c (a+3*t*c) a (primary_add_multiple_three a c t ha) ha
  · obtain ⟨c0,hc0⟩ := hc
    refine ⟨t*c0,?_⟩
    rw [hc0]
    ring
  · exact ⟨3*t,by ring⟩

/-- Shifting the upper row removes the auxiliary coprimality restriction from the matrix product law. -/
theorem kubota_mul (a b c d e f g h : O)
    (hdet : a*d-b*c=1) (hdet' : e*h-f*g=1)
    (ha : lambda ^ 2 ∣ a-1) (he : lambda ^ 2 ∣ e-1)
    (hb : (3 : O) ∣ b) (hc : (3 : O) ∣ c) (hg : (3 : O) ∣ g) :
    symbol (c*e+d*g) (a*e+b*g) = symbol c a * symbol g e := by
  by_cases hg0 : g = 0
  · have heh : e*h=1 := by simpa only [hg0,mul_zero,sub_zero] using hdet'
    have he1 : e=1 := primary_isUnit_eq_one e (IsUnit.of_mul_eq_one h heh) he
    simp only [hg0,he1,mul_one,mul_zero,add_zero,symbol_one]
  have hac : IsCoprime a c := by
    refine ⟨d,-b,?_⟩
    linear_combination hdet
  obtain ⟨t,ht⟩ := exists_coprime_three_shift a c g ha hac hg0
  have hdetShift : (a+3*t*c)*d-(b+3*t*d)*c=1 := by linear_combination hdet
  have hbShift : (3 : O) ∣ b+3*t*d :=
    dvd_add hb (dvd_mul_of_dvd_left (dvd_mul_right 3 t) d)
  have hcalc := kubota_mul_of_isCoprime (a+3*t*c) (b+3*t*d) c d e g
    hdetShift (primary_add_multiple_three a c t ha) he hbShift hg ht
  have hC : (3 : O) ∣ c*e+d*g :=
    dvd_add (dvd_mul_of_dvd_left hc e) (dvd_mul_of_dvd_right hg d)
  have hA : lambda ^ 2 ∣ (a*e+b*g)-1 := by
    have hh := dvd_add (primary_mul a e ha he)
      (dvd_mul_of_dvd_left (lambda_sq_dvd_three.trans hb) g)
    convert hh using 1 ; ring
  calc
    symbol (c*e+d*g) (a*e+b*g) =
        symbol (c*e+d*g) ((a*e+b*g)+3*t*(c*e+d*g)) :=
      (symbol_three_shift _ _ _ hA hC).symm
    _ = symbol c (a+3*t*c) * symbol g e := by
      convert hcalc using 1 ; congr 1 ; ring
    _ = symbol c a * symbol g e := by rw [symbol_three_shift c a t ha hc]


end CubicJacobi
namespace CubicKubota
open Eisenstein CubicJacobi CubicRamified
/-- The principal congruence subgroup of level three. -/
def levelThree : Subgroup (SL(2, O)) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)}))).ker

lemma levelThree_entry (M : levelThree) (i j : Fin 2) :
    (3 : O) ∣ (M : SL(2,O)) i j - (if i=j then 1 else 0) := by
  have hm : Matrix.SpecialLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3 : O)})) (M : SL(2,O)) = 1 := M.property
  have h := congrArg (fun N : SL(2, O ⧸ (Ideal.span {(3 : O)})) => N i j) hm
  change (Ideal.Quotient.mk (Ideal.span {(3 : O)})) ((M : SL(2,O)) i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ (Ideal.span {(3 : O)}))) i j at h
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using h

lemma levelThree_primary (M : levelThree) :
    lambda ^ 2 ∣ (M : SL(2,O)) 0 0 - 1 := by
  exact lambda_sq_dvd_three.trans (by simpa using levelThree_entry M 0 0)
lemma levelThree_upper (M : levelThree) : (3 : O) ∣ (M : SL(2,O)) 0 1 := by
  simpa using levelThree_entry M 0 1
lemma levelThree_lower (M : levelThree) : (3 : O) ∣ (M : SL(2,O)) 1 0 := by
  simpa using levelThree_entry M 1 0

/-- The cubic symbol of the lower-left entry against the upper-left entry. -/
def value (M : levelThree) : O :=
  symbol ((M : SL(2,O)) 1 0) ((M : SL(2,O)) 0 0)

/-- The cubic symbol defines a group multiplier. -/
theorem value_mul (M N : levelThree) : value (M*N) = value M * value N := by
  have hM : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  have hN : (N : SL(2,O)) 0 0 * (N : SL(2,O)) 1 1 -
      (N : SL(2,O)) 0 1 * (N : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (N : SL(2,O)).property
  have hh := kubota_mul ((M : SL(2,O)) 0 0) ((M : SL(2,O)) 0 1)
    ((M : SL(2,O)) 1 0) ((M : SL(2,O)) 1 1)
    ((N : SL(2,O)) 0 0) ((N : SL(2,O)) 0 1)
    ((N : SL(2,O)) 1 0) ((N : SL(2,O)) 1 1) hM hN
    (levelThree_primary M) (levelThree_primary N)
    (levelThree_upper M) (levelThree_lower M) (levelThree_lower N)
  change symbol (((M : SL(2,O)) * (N : SL(2,O))) 1 0)
    (((M : SL(2,O)) * (N : SL(2,O))) 0 0) = _
  simpa only [value, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] using hh

@[simp] theorem value_one : value 1 = 1 := by
  change symbol (0 : O) 1 = 1
  exact symbol_one 0

/-- The integral cubic Kubota character. -/
def character : levelThree →* O where
  toFun := value
  map_one' := value_one
  map_mul' := value_mul

theorem value_isUnit (M : levelThree) : IsUnit (value M) :=
  (Group.isUnit M).map character

theorem value_zero_lower_left (M : levelThree) (hc : (M : SL(2,O)) 1 0 = 0) :
    value M = 1 := by
  have hm : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 = 1 := by
    have hd := (M : SL(2,O)).property
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using hd
  have ha := primary_isUnit_eq_one _ (IsUnit.of_mul_eq_one _ hm) (levelThree_primary M)
  simp only [value, hc, ha, symbol_one]

theorem value_cube (M : levelThree) : value M ^ 3 = 1 := by
  apply symbol_cube_of_isCoprime _ _ (levelThree_primary M)
  have hd : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  refine ⟨-(M : SL(2,O)) 0 1, (M : SL(2,O)) 1 1, ?_⟩
  linear_combination hd

/-- The cubic Kubota character in the fixed complex embedding. -/
def complexCharacter : levelThree →* ℂ :=
  ringComplex.toMonoidHom.comp character

theorem complexCharacter_cube (M : levelThree) : complexCharacter M ^ 3 = 1 := by
  change ringComplex (value M) ^ 3 = 1
  rw [← map_pow, value_cube, map_one]

theorem norm_complexCharacter (M : levelThree) : ‖complexCharacter M‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp
  simpa only [norm_pow, norm_one] using congrArg norm (complexCharacter_cube M)


/-- An explicit level-three matrix detecting the nontrivial cubic character. -/
def cubicGenerator : levelThree := by
  let M : SL(2,O) := ⟨!![1+3*omega, -3*omega^2; 3, 1-3*omega], by
    rw [Matrix.det_fin_two]
    change (1+3*omega)*(1-3*omega)-(-3*omega^2)*3 = 1
    ring⟩
  refine ⟨M, ?_⟩
  change Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)})) M = 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Matrix.SpecialLinearGroup.map_apply_coe, map_add, map_sub, map_mul,
      map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (3 : O))]

/-- The explicit generator has primitive cubic multiplier. -/
theorem value_cubicGenerator : value cubicGenerator = omega := by
  change symbol 3 sevenPrime = omega
  have hthree : (3 : O) = -(lambda^2 * omega^2) := by
    rw [lambda_sq_eq]
    calc
      (3 : O) = 3*omega^3 := by rw [omega_primitive.pow_eq_one]; ring
      _ = -(-3*omega*omega^2) := by ring
  change idealSymbol sevenIdeal 3 = omega
  rw [idealSymbol_prime sevenIdeal sevenIdeal_good]
  rw [hthree, map_neg, map_mul, map_pow, map_pow, neg_eq_neg_one_mul, map_mul,
    cubicChar_neg_one, one_mul, map_mul, map_pow, map_pow,
    cubicValue_lambda_seven, cubicValue_omega_seven]
  simpa only [one_pow, one_mul, ← pow_mul] using omega_four

/-- The multiplier takes values in the finite group of cubic roots. -/
def finiteCharacter : levelThree →* rootsOfUnity 3 O where
  toFun M := ⟨character.toHomUnits M,
    (mem_rootsOfUnity' 3 _).mpr (value_cube M)⟩
  map_one' := by
    apply Subtype.ext
    exact character.toHomUnits.map_one
  map_mul' M N := by
    apply Subtype.ext
    exact character.toHomUnits.map_mul M N

/-- Every cubic root occurs as a multiplier. -/
theorem finiteCharacter_surjective : Function.Surjective finiteCharacter := by
  intro η
  have hη : ((η : Oˣ) : O)^3 = 1 := (mem_rootsOfUnity' 3 (η : Oˣ)).mp η.property
  obtain ⟨j,_,hj⟩ := omega_primitive.eq_pow_of_pow_eq_one hη
  refine ⟨cubicGenerator^j, ?_⟩
  apply rootsOfUnity.coe_injective
  change value (cubicGenerator^j) = ((η : Oˣ) : O)
  change character (cubicGenerator^j) = _
  rw [map_pow]
  change value cubicGenerator ^ j = _
  rw [value_cubicGenerator]
  exact hj

/-- The cubic multiplier cuts out a subgroup of index three inside the level-three group. -/
theorem finiteCharacter_kernel_index : finiteCharacter.ker.index = 3 := by
  change Nat.card (levelThree ⧸ finiteCharacter.ker) = 3
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    finiteCharacter finiteCharacter_surjective).toEquiv]
  exact omega_primitive.card_rootsOfUnity

/-- Reduction modulo three has finite image. -/
theorem levelThree_finiteIndex : levelThree.FiniteIndex := by
  letI : Finite (O ⧸ Ideal.span {(3 : O)}) :=
    (Ideal.span {(3 : O)}).finiteQuotientOfFreeOfNeBot
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  unfold levelThree
  infer_instance

/-- The integral metaplectic kernel inside the full special linear group. -/
def globalKubotaKernel : Subgroup (SL(2,O)) := finiteCharacter.ker.map levelThree.subtype

/-- The integral metaplectic kernel has finite index. -/
theorem globalKubotaKernel_finiteIndex : globalKubotaKernel.FiniteIndex := by
  letI : levelThree.FiniteIndex := levelThree_finiteIndex
  letI : finiteCharacter.ker.FiniteIndex := inferInstance
  constructor
  rw [globalKubotaKernel, Subgroup.index_map_subtype]
  exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := finiteCharacter.ker))
    (Subgroup.FiniteIndex.index_ne_zero (H := levelThree))

theorem finiteCharacter_eq_one (M : levelThree) :
    finiteCharacter M = 1 ↔ complexCharacter M = 1 := by
  constructor
  · intro h
    have hc := congrArg (fun z : rootsOfUnity 3 O => ((z : Oˣ) : O)) h
    change value M = 1 at hc
    change ringComplex (value M) = 1
    rw [hc, map_one]
  · intro h
    apply rootsOfUnity.coe_injective
    change value M = 1
    apply ringComplex_injective
    change ringComplex (value M) = 1 at h
    simpa only [map_one] using h

/-- Kernel membership is the actual cubic symbol equation on a level-three matrix. -/
theorem globalKubotaKernel_mem (M : SL(2,O)) :
    M ∈ globalKubotaKernel ↔ ∃ hM : M ∈ levelThree, complexCharacter ⟨M,hM⟩ = 1 := by
  constructor
  · rintro ⟨N,hN,hNM⟩
    subst M
    exact ⟨N.property, (finiteCharacter_eq_one N).mp hN⟩
  · rintro ⟨hM,hc⟩
    exact ⟨⟨M,hM⟩, (finiteCharacter_eq_one ⟨M,hM⟩).mpr hc, rfl⟩

end CubicKubota
end GaloisForLFunctions.MetaplecticMobiusDescent

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicJacobi.kubota_mul
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicKubota.value_mul
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicKubota.complexCharacter_cube
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicKubota.value_cubicGenerator
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicKubota.finiteCharacter_surjective
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicKubota.finiteCharacter_kernel_index
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicKubota.globalKubotaKernel_finiteIndex
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicKubota.globalKubotaKernel_mem
