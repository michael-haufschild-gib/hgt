/-
Cubic constant-term arithmetic adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicConstantResidueCharacters

/-!
# The cubic constant term is supported exactly on cubes

The unramified prime exponents are multiples of three. The ramified
supplement then removes the remaining lambda exponent and forces the
unit factor to be a sign. Conversely each nonzero cube has residue sum
equal to the positive number of admissible classes.
-/
noncomputable section
open MeasureTheory Set Filter UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

private instance cubicCubeSupportCyclotomic : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance cubicCubeSupportPID : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

lemma multiset_cube_remainder {α : Type*} [DecidableEq α] (s : Multiset α) (p : α)
    (hdiv : ∀ q, q ≠ p → 3 ∣ s.count q) :
    ∃ t : Multiset α, s=(s.count p % 3) • {p} + 3 • t := by
  let t := Finsupp.toMultiset (s.toFinsupp.mapRange (fun n : ℕ => n/3) (by decide))
  refine ⟨t,?_⟩
  apply Multiset.ext.mpr
  intro q
  simp only [Multiset.count_add,Multiset.count_nsmul,Multiset.count_singleton,
    t,Finsupp.count_toMultiset,Finsupp.mapRange_apply,Multiset.toFinsupp_apply]
  by_cases hq : q=p
  · subst q
    simp only [ite_true,mul_one]
    omega
  · simp only [hq,ite_false,mul_zero,zero_add]
    exact (Nat.mul_div_cancel' (hdiv q hq)).symm

lemma residue_lambda_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

lemma constant_coefficient_unramified_count [NormalizationMonoid O]
    (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0)
    (q : O) (hq : q ≠ normalize lambda) : 3 ∣ (normalizedFactors c).count q := by
  by_cases hmem : q ∈ normalizedFactors c
  · have hprime := prime_of_normalized_factor q hmem
    let P : Ideal O := Ideal.span {q}
    let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
    have hg : lambda ∉ P := by
      intro hl
      have ha : Associated q lambda :=
        hprime.associated_of_dvd residue_lambda_prime (Ideal.mem_span_singleton.mp hl)
      apply hq
      exact (normalize_normalized_factor q hmem).symm.trans
        (normalize_eq_normalize_iff_associated.mpr ha)
    obtain ⟨p,hP,hprimary,-⟩ := cubicJacobi_exists_primary_generator P hg
    have hqp : Associated q p := Ideal.span_singleton_eq_span_singleton.mp hP
    have hp : Prime p := hqp.prime_iff.mp hprime
    obtain ⟨b,hfactor,hpb⟩ := (FiniteMultiplicity.of_prime_left hp hc).exists_eq_pow_mul_and_not_dvd
    have hd := constant_coefficient_primary_prime_exponent c p b (multiplicity p c)
      hc hlevel hp hprimary hpb hfactor hA
    have hcount := multiplicity_eq_count_normalizedFactors hprime.irreducible hc
    rw [normalize_normalized_factor q hmem] at hcount
    rw [← hcount,← multiplicity_eq_of_associated_left hqp]
    exact hd
  · rw [Multiset.count_eq_zero.mpr hmem]
    exact dvd_zero _

theorem constant_coefficient_cube_reduction (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) :
    ∃ (u : Oˣ) (r : ℕ) (a : O), r < 3 ∧ c=(u:O)*lambda^r*a^3 := by
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := normalizedFactors c
  obtain ⟨t,ht⟩ := multiset_cube_remainder s (normalize lambda)
    (constant_coefficient_unramified_count c hc hlevel hA)
  let r := s.count (normalize lambda) % 3
  have hprod : s.prod=(normalize lambda)^r*t.prod^3 := by
    rw [ht,Multiset.prod_add,Multiset.prod_nsmul,Multiset.prod_singleton,Multiset.prod_nsmul]
  have hassoc : Associated (lambda^r*t.prod^3) c := by
    have hnorm : Associated ((normalize lambda)^r*t.prod^3) (lambda^r*t.prod^3) :=
      (normalize_associated lambda).pow_pow.mul_right _
    apply hnorm.symm.trans
    rw [← hprod]
    exact prod_normalizedFactors hc
  obtain ⟨u,hu⟩ := hassoc
  refine ⟨u,r,t.prod,Nat.mod_lt _ (by decide),?_⟩
  rw [← hu]
  ring


lemma constant_coefficient_ramified_equation (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c)
    (hA : arithmeticResidueSum 0 c ≠ 0) (u : Oˣ) (r : ℕ) (a : O) (ha : a ≠ 0)
    (hfactor : c=(u:O)*lambda^r*a^3) (A B : ℤ) :
    symbol (u:O) (primaryCoord A B)*(cubicExp A)^r=1 := by
  let t0 := primaryCoord A B
  have ht0 : lambda^2 ∣ t0-1 := primaryCoord_primary A B
  obtain ⟨w,hw⟩ := exists_coprime_three_shift t0 3 a ht0 (primary_coprime_three t0 ht0) ha
  let t := t0+3*w*3
  have ht : lambda^2 ∣ t-1 := primary_add_multiple_three t0 3 w ht0
  have h9 : (9:O) ∣ t-t0 := ⟨w,by dsimp [t]; ring⟩
  have hat : IsCoprime a t := hw.symm
  have hlt : IsCoprime lambda t :=
    coprime_of_dvd_sub_one lambda t ((show lambda ∣ lambda^2 from ⟨lambda,by ring⟩).trans ht)
  have hct : IsCoprime c t := by
    rw [hfactor,show (u:O)*lambda^r*a^3=(u:O)*(lambda^r*a^3) by ring]
    apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
    exact hlt.pow_left.mul_left hat.pow_left
  have htriv := arithmeticResidueSum_ne_zero_forces_trivial c hc hlevel hA t
    ⟨hct,three_dvd_primary_sub_one t ht⟩
  have hacube : symbol (a^3) t=1 := by
    rw [symbol_pow_numerator a t ht 3]
    exact symbol_cube_of_isCoprime a t ht hat
  rw [hfactor,symbol_mul_numerator _ _ t,symbol_mul_numerator _ _ t,
    symbol_pow_numerator lambda t ht r,hacube,mul_one,
    symbol_unit_congr_mod_nine (u:O) t t0 u.isUnit ht ht0 h9,
    symbol_lambda_congr_mod_nine t t0 ht ht0 h9,
    symbol_lambda_eq_linearRay t0 ht0] at htriv
  simpa only [t0,linearRay_primaryCoord,one_mul,zero_mul,add_zero] using htriv

lemma unit_eq_sign_of_symbol_class (u : Oˣ)
    (hu : symbol (u:O) (primaryCoord 0 1)=1) : (u:O)=1 ∨ (u:O)=-1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η:O)=omega := rfl
  have hlist : u ∈ ([1,-1,η,-η,η^2,-η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hω : symbol omega (primaryCoord 0 1)=omega^2 := by
    rw [symbol_omega_eq_linearRay _ (primaryCoord_primary 0 1),linearRay_primaryCoord]
    norm_num [cubicExp]
    rfl
  have hω2 : symbol (omega^2) (primaryCoord 0 1)=omega^4 := by
    rw [symbol_pow_numerator omega _ (primaryCoord_primary 0 1) 2,hω,← pow_mul]
  have hn2 : omega^2 ≠ 1 := (omega_primitive.pow_eq_one_iff_dvd 2).not.mpr (by decide)
  have hn4 : omega^4 ≠ 1 := (omega_primitive.pow_eq_one_iff_dvd 4).not.mpr (by decide)
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h | h | h | h | h | h
  · exact Or.inl (by rw [h,Units.val_one])
  · exact Or.inr (by rw [h,Units.val_neg,Units.val_one])
  · exact False.elim (hn2 (by simpa only [h,hη,hω] using hu))
  · exact False.elim (hn2 (by simpa only [h,Units.val_neg,hη,
      (symbol_neg_numerator _ _ (primaryCoord_primary 0 1)),hω] using hu))
  · exact False.elim (hn4 (by simpa only [h,Units.val_pow_eq_pow_val,hη,hω2] using hu))
  · exact False.elim (hn4 (by simpa only [h,Units.val_neg,Units.val_pow_eq_pow_val,hη,
      (symbol_neg_numerator _ _ (primaryCoord_primary 0 1)),hω2] using hu))

theorem arithmeticResidueSum_ne_zero_implies_cube (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) : ∃ a : O,c=a^3 := by
  obtain ⟨u,r,a,hr,hfactor⟩ := constant_coefficient_cube_reduction c hc hlevel hA
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by decide : (3:ℕ) ≠ 0),mul_zero] at hfactor
    exact hc hfactor
  have h01 := constant_coefficient_ramified_equation c hc hlevel hA u r a ha hfactor 0 1
  have husign := unit_eq_sign_of_symbol_class u (by
    simpa only [cubicExp_zero,one_pow,mul_one] using h01)
  have h10 := constant_coefficient_ramified_equation c hc hlevel hA u r a ha hfactor 1 0
  have hωr : omega^r=1 := by
    rcases husign with hu | hu
    · simpa only [hu,symbol_one_numerator _ (primaryCoord_primary 1 0),one_mul,
        cubicExp,Int.reduceMod,Int.toNat_one,pow_one] using h10
    · simpa only [hu,symbol_neg_one _ (primaryCoord_primary 1 0),one_mul,
        cubicExp,Int.reduceMod,Int.toNat_one,pow_one] using h10
  have hdiv : 3 ∣ r := (omega_primitive.pow_eq_one_iff_dvd r).mp hωr
  have hr0 : r=0 := by omega
  rw [hr0,pow_zero,mul_one] at hfactor
  rcases husign with hu | hu
  · refine ⟨a,?_⟩
    simpa only [hu,one_mul] using hfactor
  · refine ⟨-a,?_⟩
    rw [hfactor,hu]
    ring


theorem arithmeticResidueSum_ne_zero_iff_cube (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    arithmeticResidueSum 0 c ≠ 0 ↔ ∃ a : O,c=a^3 := by
  constructor
  · exact arithmeticResidueSum_ne_zero_implies_cube c hc hlevel
  · rintro ⟨a,rfl⟩
    have ha : a ≠ 0 := fun h => hc (by rw [h]; norm_num)
    exact arithmeticResidueSum_cube_ne_zero a ha

theorem arithmeticResidueSum_constant_formula (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    arithmeticResidueSum 0 c=
      if ∃ a : O,c=a^3 then (Nat.card (AdmissibleResidue c):ℂ) else 0 := by
  split_ifs with hcube
  · obtain ⟨a,rfl⟩ := hcube
    exact arithmeticResidueSum_cube a (fun h => hc (by rw [h]; norm_num))
  · exact not_ne_iff.mp (fun hA => hcube (arithmeticResidueSum_ne_zero_implies_cube c hc hlevel hA))


#print axioms arithmeticResidueSum_ne_zero_iff_cube
#print axioms arithmeticResidueSum_constant_formula
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
