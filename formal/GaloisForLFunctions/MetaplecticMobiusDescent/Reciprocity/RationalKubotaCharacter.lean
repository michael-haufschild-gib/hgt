/-
The Kubota character on rational matrices adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicScatteringContinuation
import GaloisForLFunctions.MetaplecticMobiusDescent.WeightedCubicWhittakerAverages
import GaloisForLFunctions.MetaplecticMobiusDescent.CompactCubicQuotientPullbacks

/-!
# The Kubota character on rational matrices

The integral special linear group embeds in the Eisenstein group, and the cubic Kubota
character extends to the rational extension `rationalExtension` of the level-three kernel.
Invariance under the rational generators extends to every rational matrix.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise

namespace RationalSource
open CubicJacobi CubicRamified
private instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

/-- The integral special linear group embedded in the Eisenstein group. -/
def rationalEmbedding : SL(2,ℤ)→*SL(2,O) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom O)

def levelThreeConjugate (g : SL(2,O)) (M : levelThree) : levelThree :=
  ⟨g*(M:SL(2,O))*g⁻¹,by
    change Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:O)})) _=1
    rw [map_mul,map_mul,map_inv,M.property,mul_one,mul_inv_cancel]⟩

lemma levelThree_bottom_primary (M : levelThree) : lambda^2∣(M:SL(2,O)) 1 1-1 :=
  lambda_sq_dvd_three.trans (by simpa using levelThree_entry M 1 1)

lemma value_inverse_formula (M : levelThree) :
    value M⁻¹=symbol ((M:SL(2,O)) 1 0) ((M:SL(2,O)) 1 1) := by
  have hd := levelThree_bottom_primary M
  change symbol (((M:SL(2,O))⁻¹) 1 0) (((M:SL(2,O))⁻¹) 0 0)=_
  simp only [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  exact symbol_neg_numerator _ _ hd

/-- The determinant relation reads the multiplier from the upper-right and lower-right entries. -/
lemma value_upper_formula (M : levelThree) :
    value M=symbol ((M:SL(2,O)) 0 1) ((M:SL(2,O)) 1 1) := by
  have hd := levelThree_bottom_primary M
  have hdet : (M:SL(2,O)) 0 0*(M:SL(2,O)) 1 1-
      (M:SL(2,O)) 0 1*(M:SL(2,O)) 1 0=1 := by
    simpa only [Matrix.det_fin_two] using (M:SL(2,O)).property
  have hprod : symbol ((M:SL(2,O)) 0 1) ((M:SL(2,O)) 1 1)*
      symbol ((M:SL(2,O)) 1 0) ((M:SL(2,O)) 1 1)=1 := by
    rw [←symbol_mul_numerator _ _ _]
    calc
      _ = symbol (-1) ((M:SL(2,O)) 1 1) := by
        apply symbol_congr
        refine ⟨(M:SL(2,O)) 0 0,?_⟩
        linear_combination -hdet
      _ = 1 := symbol_neg_one _ hd
  have hinv : value M*symbol ((M:SL(2,O)) 1 0) ((M:SL(2,O)) 1 1)=1 := by
    rw [←value_inverse_formula,←value_mul,mul_inv_cancel,value_one]
  calc
    value M = value M*1 := by rw [mul_one]
    _ = value M*(symbol ((M:SL(2,O)) 0 1) ((M:SL(2,O)) 1 1)*
      symbol ((M:SL(2,O)) 1 0) ((M:SL(2,O)) 1 1)) := by rw [hprod]
    _ = symbol ((M:SL(2,O)) 0 1) ((M:SL(2,O)) 1 1)*
      (value M*symbol ((M:SL(2,O)) 1 0) ((M:SL(2,O)) 1 1)) := by ring
    _ = _ := by rw [hinv,mul_one]

theorem value_conjugate_S (M : levelThree) :
    value (levelThreeConjugate (rationalEmbedding ModularGroup.S) M)=value M := by
  rw [value_upper_formula M]
  change symbol (((rationalEmbedding ModularGroup.S)*(M:SL(2,O))*(rationalEmbedding ModularGroup.S)⁻¹) 1 0)
    (((rationalEmbedding ModularGroup.S)*(M:SL(2,O))*(rationalEmbedding ModularGroup.S)⁻¹) 0 0)=_
  simp only [rationalEmbedding,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.coe_inv,ModularGroup.coe_S,Matrix.adjugate_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two]
  simpa using symbol_neg_numerator ((M:SL(2,O)) 0 1) ((M:SL(2,O)) 1 1) (levelThree_bottom_primary M)

theorem complexCharacter_conjugate_S (M : levelThree) :
    complexCharacter (levelThreeConjugate (rationalEmbedding ModularGroup.S) M)=complexCharacter M :=
  congrArg ringComplex (value_conjugate_S M)


open CubicRamified
theorem symbol_shift_by_self (c a : O) (ha : lambda^2∣a-1) (hc : (3:O)∣c) :
    symbol c (a+c)=symbol c a := by
  have hA : lambda^2∣a+c-1 := by
    convert dvd_add ha (lambda_sq_dvd_three.trans hc) using 1 ; ring
  calc
    symbol c (a+c)=symbol (-a) (a+c) := by
      apply symbol_congr
      refine ⟨1,?_⟩
      ring
    _ = symbol a (a+c) := symbol_neg_numerator a (a+c) hA
    _ = symbol (a+c) a := symbol_reciprocity a (a+c) ha hA
    _ = symbol c a := by
      apply symbol_congr
      refine ⟨1,?_⟩
      ring

open CubicJacobi CubicRamified
theorem value_conjugate_T (M : levelThree) :
    value (levelThreeConjugate (rationalEmbedding ModularGroup.T) M)=value M := by
  change symbol (((rationalEmbedding ModularGroup.T)*(M:SL(2,O))*(rationalEmbedding ModularGroup.T)⁻¹) 1 0)
    (((rationalEmbedding ModularGroup.T)*(M:SL(2,O))*(rationalEmbedding ModularGroup.T)⁻¹) 0 0)=_
  simp only [rationalEmbedding,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.coe_inv,ModularGroup.coe_T,Matrix.adjugate_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two]
  simpa [value] using symbol_shift_by_self ((M:SL(2,O)) 1 0) ((M:SL(2,O)) 0 0)
    (levelThree_primary M) (levelThree_lower M)

lemma levelThreeConjugate_one (M : levelThree) : levelThreeConjugate 1 M=M := by
  apply Subtype.ext
  simp [levelThreeConjugate]

lemma levelThreeConjugate_mul (g h : SL(2,O)) (M : levelThree) :
    levelThreeConjugate (g*h) M=levelThreeConjugate g (levelThreeConjugate h M) := by
  apply Subtype.ext
  simp [levelThreeConjugate,mul_assoc]

def characterConjugationStabilizer : Subgroup (SL(2,O)) where
  carrier g := ∀M : levelThree,value (levelThreeConjugate g M)=value M
  one_mem' M := by rw [levelThreeConjugate_one]
  mul_mem' hg hh M := by rw [levelThreeConjugate_mul,hg,hh]
  inv_mem' {g} hg M := by
    have h := hg (levelThreeConjugate g⁻¹ M)
    rw [←levelThreeConjugate_mul,mul_inv_cancel,levelThreeConjugate_one] at h
    exact h.symm

/-- Invariance under the rational generators extends to every rational matrix. -/
theorem value_conjugate_rational (g : SL(2,ℤ)) (M : levelThree) :
    value (levelThreeConjugate (rationalEmbedding g) M)=value M := by
  have htop : characterConjugationStabilizer.comap rationalEmbedding=⊤ := by
    apply top_unique
    rw [←SpecialLinearGroup.SL2Z_generators]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with (rfl|rfl)
    · exact value_conjugate_S
    · exact value_conjugate_T
  have hg : g∈characterConjugationStabilizer.comap rationalEmbedding := by rw [htop];trivial
  exact hg M

theorem complexCharacter_conjugate_rational (g : SL(2,ℤ)) (M : levelThree) :
    complexCharacter (levelThreeConjugate (rationalEmbedding g) M)=complexCharacter M :=
  congrArg ringComplex (value_conjugate_rational g M)


open CubicRamified
/-- Choose the primary sign of a rational integer away from three. -/
def rationalPrimary (n : ℕ) : O := if n%3=1 then (n:O) else -(n:O)

lemma rationalPrimary_coord (n : ℕ) (hn : ¬3∣n) : ∃A : ℤ,rationalPrimary n=primaryCoord A 0 := by
  have hm : n%3=1 ∨ n%3=2 := by
    have hl := Nat.mod_lt n (by decide : 0<3)
    have h0 : n%3≠0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
    omega
  rcases hm with hm|hm
  · refine ⟨(n/3:ℕ),?_⟩
    have he : n=1+3*(n/3) := by omega
    rw [rationalPrimary,if_pos hm,primaryCoord_eq]
    conv_lhs => rw [he]
    simp only [Int.cast_natCast,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,]
    ring
  · refine ⟨-((n/3:ℕ):ℤ)-1,?_⟩
    have he : n=2+3*(n/3) := by omega
    rw [rationalPrimary,if_neg (by omega),primaryCoord_eq]
    conv_lhs => rw [he]
    simp only [Int.cast_sub,Int.cast_neg,Int.cast_natCast,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,]
    ring

lemma rationalPrimary_primary (n : ℕ) (hn : ¬3∣n) : lambda^2∣rationalPrimary n-1 := by
  obtain ⟨A,hA⟩ := rationalPrimary_coord n hn
  rw [hA]
  exact primaryCoord_primary A 0

lemma rationalPrimary_denominator (x : O) (n : ℕ) : symbol x (rationalPrimary n)=symbol x (n:O) := by
  unfold rationalPrimary
  split_ifs
  · rfl
  · simp only [symbol,Ideal.span_singleton_neg]

lemma rationalPrimary_numerator (m n : ℕ) (hn : ¬3∣n) :
    symbol (rationalPrimary m) (rationalPrimary n)=symbol (m:O) (rationalPrimary n) := by
  change symbol (if m%3=1 then (m:O) else -(m:O)) (rationalPrimary n)=_
  split_ifs
  · rfl
  · exact symbol_neg_numerator _ _ (rationalPrimary_primary n hn)

lemma rational_symbol_mul (a b n : ℕ) :
    symbol ((a*b : ℕ) : O) (n : O) = symbol (a : O) (n : O) * symbol (b : O) (n : O) := by
  rw [Nat.cast_mul]
  exact symbol_mul_numerator _ _ _

lemma rational_symbol_three (n : ℕ) (hn : ¬3∣n) : symbol (3:O) (n:O)=1 := by
  rw [←rationalPrimary_denominator _ n]
  obtain ⟨A,hA⟩ := rationalPrimary_coord n hn
  rw [hA]
  have hprimary := primaryCoord_primary A 0
  have hthree : (3:O)=-((1+2*omega)^2) := by
    have hw : omega^2=-omega-1 := by
      change (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger^2=
        -(IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger-1
      exact IsCyclotomicExtension.Rat.Three.eta_sq (IsCyclotomicExtension.zeta_spec 3 ℚ K)
    linear_combination 4*hw
  have htrace := symbol_traceLambda_eq_linearRay (primaryCoord A 0) hprimary
  change symbol (1+2*omega) (primaryCoord A 0)=_ at htrace
  rw [hthree,symbol_neg_numerator _ _ hprimary,symbol_pow_numerator _ _ hprimary,
    htrace,linearRay_primaryCoord]
  simp

lemma rational_symbol_reciprocity (m n : ℕ) (hm : ¬3∣m) (hn : ¬3∣n) :
    symbol (m:O) (n:O)=symbol (n:O) (m:O) := by
  calc
    _ = symbol (rationalPrimary m) (rationalPrimary n) := by
      rw [rationalPrimary_numerator m n hn,rationalPrimary_denominator]
    _ = symbol (rationalPrimary n) (rationalPrimary m) :=
      symbol_reciprocity _ _ (rationalPrimary_primary m hm) (rationalPrimary_primary n hn)
    _ = _ := by rw [rationalPrimary_numerator n m hm,rationalPrimary_denominator]

lemma rational_symbol_mod (m n : ℕ) : symbol (m:O) (n:O)=symbol ((m%n:ℕ):O) (n:O) := by
  apply symbol_congr
  refine ⟨(m/n:ℕ),?_⟩
  have he : m=m%n+n*(m/n) := (Nat.mod_add_div m n).symm
  have hh : (m:O)=(m%n:ℕ)+ (n:O)*(m/n:ℕ) := by exact_mod_cast he
  linear_combination hh

/-- Euclidean reduction and the supplementary law make coprime rational cubic symbols trivial. -/
theorem rational_symbol_eq_one (n : ℕ) (hn : ¬3∣n) (m : ℕ) (hmn : Nat.Coprime m n) :
    symbol (m:O) (n:O)=1 := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    by_cases hn1 : n=1
    · subst n
      simpa only [Nat.cast_one] using symbol_one (m:O)
    have hn0 : 0<n := Nat.pos_of_ne_zero (fun h => hn (by rw [h];exact dvd_zero 3))
    have hsmall : ∀r : ℕ,r<n → Nat.Coprime r n → symbol (r:O) (n:O)=1 := by
      intro r
      induction r using Nat.strong_induction_on with
      | h r ihr =>
        intro hrn hcop
        by_cases hr0 : r=0
        · subst r
          have : n=1 := by simpa using hcop
          exact False.elim (hn1 this)
        by_cases hr3 : 3∣r
        · have hquot : r/3<r := Nat.div_lt_self (Nat.pos_of_ne_zero hr0) (by decide)
          have hfactor : r=3*(r/3) := (Nat.mul_div_cancel' hr3).symm
          have hqc : Nat.Coprime (r/3) n := hcop.of_dvd_left (Nat.div_dvd_of_dvd hr3)
          rw [hfactor,rational_symbol_mul _ _ n]
          norm_num only [Nat.cast_ofNat]
          rw [rational_symbol_three n hn,one_mul]
          exact ihr (r/3) hquot (lt_trans hquot hrn) hqc
        · rw [rational_symbol_reciprocity r n hr3 hn]
          exact ih r hrn hr3 n hcop.symm
    rw [rational_symbol_mod]
    apply hsmall (m%n) (Nat.mod_lt m hn0)
    change Nat.gcd (m%n) n=1
    rw [←Nat.gcd_rec n m]
    exact hmn.symm


lemma primary_int_natAbs_not_three (a : ℤ) (ha : lambda^2∣(a:O)-1) : ¬3∣a.natAbs := by
  intro h
  have hInt : (3:ℤ)∣a := Int.natCast_dvd.mpr h
  have hO : (3:O)∣(a:O) := by
    rcases hInt with ⟨b,hb⟩
    refine ⟨(b:O),?_⟩
    simpa only [Int.cast_mul,Int.cast_ofNat] using congrArg (fun z : ℤ => (z:O)) hb
  have hL2 : lambda∣lambda^2 := dvd_pow_self _ (by decide : (2:ℕ)≠0)
  have hLa := (hL2.trans lambda_sq_dvd_three).trans hO
  have hLa1 := hL2.trans ha
  have h1 : lambda∣(1:O) := by
    convert dvd_sub hLa hLa1 using 1 ; ring
  exact lambda_not_dvd_two (h1.trans (one_dvd 2))

/-- Signs do not affect a rational cubic symbol with primary denominator. -/
theorem integer_symbol_eq_one (c a : ℤ) (ha : lambda^2∣(a:O)-1)
    (hcop : Nat.Coprime c.natAbs a.natAbs) : symbol (c:O) (a:O)=1 := by
  have hnum : symbol (c:O) (a:O)=symbol (c.natAbs:O) (a:O) := by
    rcases Int.natAbs_eq c with h|h
    · have he : (c:O)=(c.natAbs:O) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:O)) h
      exact congrArg (fun z : O => symbol z (a:O)) he
    · have he : (c:O)=-(c.natAbs:O) := by
        simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun z : ℤ => (z:O)) h
      exact (congrArg (fun z : O => symbol z (a:O)) he).trans
        (symbol_neg_numerator _ _ ha)
  rw [hnum]
  have hden : symbol (c.natAbs:O) (a:O)=symbol (c.natAbs:O) (a.natAbs:O) := by
    rcases Int.natAbs_eq a with h|h
    · have he : (a:O)=(a.natAbs:O) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:O)) h
      exact congrArg (symbol (c.natAbs:O)) he
    · have he : (a:O)=-(a.natAbs:O) := by
        simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun z : ℤ => (z:O)) h
      rw [he]
      simp only [symbol,Ideal.span_singleton_neg]
  rw [hden]
  exact rational_symbol_eq_one a.natAbs (primary_int_natAbs_not_three a ha) c.natAbs hcop

open CubicJacobi CubicRamified
theorem value_rational_intersection (g : SL(2,ℤ)) (hg : rationalEmbedding g∈levelThree) :
    value ⟨rationalEmbedding g,hg⟩=1 := by
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hcop : IsCoprime (g 1 0) (g 0 0) := by
    refine ⟨-(g 0 1),g 1 1,?_⟩
    linear_combination hdet
  have hp := levelThree_primary ⟨rationalEmbedding g,hg⟩
  change lambda^2∣((g 0 0:ℤ):O)-1 at hp
  change symbol ((g 1 0:ℤ):O) ((g 0 0:ℤ):O)=1
  exact integer_symbol_eq_one (g 1 0) (g 0 0) hp (Int.isCoprime_iff_nat_coprime.mp hcop)

theorem complexCharacter_rational_intersection (g : SL(2,ℤ)) (hg : rationalEmbedding g∈levelThree) :
    complexCharacter ⟨rationalEmbedding g,hg⟩=1 := by
  change ringComplex (value ⟨rationalEmbedding g,hg⟩)=1
  rw [value_rational_intersection g hg,map_one]

/-- The product subgroup `Γ(3) · SL₂(ℤ)`. -/
def rationalExtension : Subgroup (SL(2,O)) where
  carrier g := ∃n : levelThree,∃r : SL(2,ℤ),(n:SL(2,O))*rationalEmbedding r=g
  one_mem' := ⟨1,1,by simp⟩
  mul_mem' := by
    rintro g h ⟨n,r,rfl⟩ ⟨m,s,rfl⟩
    refine ⟨n*levelThreeConjugate (rationalEmbedding r) m,r*s,?_⟩
    simp [levelThreeConjugate,map_mul,mul_assoc]
  inv_mem' := by
    rintro g ⟨n,r,rfl⟩
    refine ⟨levelThreeConjugate (rationalEmbedding r⁻¹) n⁻¹,r⁻¹,?_⟩
    simp [levelThreeConjugate,map_inv,mul_assoc]

lemma levelThree_le_rationalExtension : levelThree≤rationalExtension := by
  intro g hg
  exact ⟨⟨g,hg⟩,1,by simp⟩

lemma rational_mem_rationalExtension (r : SL(2,ℤ)) : rationalEmbedding r∈rationalExtension :=
  ⟨1,r,by simp⟩

lemma rationalExtension_eq_sup : rationalExtension=levelThree⊔rationalEmbedding.range := by
  apply le_antisymm
  · rintro g ⟨n,r,rfl⟩
    exact Subgroup.mul_mem _
      ((show levelThree≤levelThree⊔rationalEmbedding.range from le_sup_left) n.property)
      ((show rationalEmbedding.range≤levelThree⊔rationalEmbedding.range from le_sup_right) ⟨r,rfl⟩)
  · apply sup_le levelThree_le_rationalExtension
    rintro g ⟨r,rfl⟩
    exact rational_mem_rationalExtension r

/-- Triviality on the rational intersection makes the extension independent of decomposition. -/
lemma complexCharacter_product_well_defined (n m : levelThree) (r s : SL(2,ℤ))
    (h : (n:SL(2,O))*rationalEmbedding r=(m:SL(2,O))*rationalEmbedding s) :
    complexCharacter n=complexCharacter m := by
  have he : ((m⁻¹*n:levelThree):SL(2,O))=rationalEmbedding (s*r⁻¹) := by
    have hh := congrArg (fun g : SL(2,O)=>(m:SL(2,O))⁻¹*g*(rationalEmbedding r)⁻¹) h
    simpa [map_mul,map_inv,mul_assoc] using hh
  have hm : rationalEmbedding (s*r⁻¹)∈levelThree := he ▸ (m⁻¹*n).property
  have hv : complexCharacter (m⁻¹*n)=1 := by
    have he' : (m⁻¹*n:levelThree)=⟨rationalEmbedding (s*r⁻¹),hm⟩ := Subtype.ext he
    rw [he']
    exact complexCharacter_rational_intersection (s*r⁻¹) hm
  calc
    complexCharacter n=complexCharacter (m*(m⁻¹*n)) := by rw [mul_inv_cancel_left]
    _ = complexCharacter m*complexCharacter (m⁻¹*n) := map_mul _ _ _
    _ = complexCharacter m := by rw [hv,mul_one]

def rationalExtensionLeft (g : rationalExtension) : levelThree := g.property.choose

def rationalExtensionRight (g : rationalExtension) : SL(2,ℤ) := g.property.choose_spec.choose

lemma rationalExtension_product (g : rationalExtension) :
    (rationalExtensionLeft g:SL(2,O))*rationalEmbedding (rationalExtensionRight g)=(g:SL(2,O)) :=
  g.property.choose_spec.choose_spec

def rationalExtensionValue (g : rationalExtension) : ℂ := complexCharacter (rationalExtensionLeft g)

lemma rationalExtensionValue_of_product (g : rationalExtension) (n : levelThree) (r : SL(2,ℤ))
    (h : (n:SL(2,O))*rationalEmbedding r=(g:SL(2,O))) : rationalExtensionValue g=complexCharacter n :=
  complexCharacter_product_well_defined (rationalExtensionLeft g) n (rationalExtensionRight g) r
    ((rationalExtension_product g).trans h.symm)

/-- The extended cubic character, trivial on rational matrices. -/
def extendedComplexCharacter : rationalExtension→*ℂ where
  toFun := rationalExtensionValue
  map_one' := by
    rw [rationalExtensionValue_of_product 1 1 1 (by simp),map_one]
  map_mul' g h := by
    have hp :
        ((rationalExtensionLeft g*levelThreeConjugate (rationalEmbedding (rationalExtensionRight g)) (rationalExtensionLeft h):levelThree):SL(2,O))*
          rationalEmbedding (rationalExtensionRight g*rationalExtensionRight h)=((g*h:rationalExtension):SL(2,O)) := by
      simp only [Subgroup.coe_mul,levelThreeConjugate,map_mul]
      simp only [mul_assoc,inv_mul_cancel_left]
      rw [←rationalExtension_product g,←rationalExtension_product h]
      group
    rw [rationalExtensionValue_of_product (g*h) _ _ hp,map_mul,complexCharacter_conjugate_rational]
    rfl

lemma extendedComplexCharacter_restrict (n : levelThree) :
    extendedComplexCharacter ⟨(n:SL(2,O)),levelThree_le_rationalExtension n.property⟩=complexCharacter n := by
  exact rationalExtensionValue_of_product _ n 1 (by simp)

lemma extendedComplexCharacter_rational (r : SL(2,ℤ)) :
    extendedComplexCharacter ⟨rationalEmbedding r,rational_mem_rationalExtension r⟩=1 := by
  exact (rationalExtensionValue_of_product _ 1 r (by simp)).trans (map_one _)

lemma extendedComplexCharacter_cube (g : rationalExtension) : extendedComplexCharacter g^3=1 :=
  complexCharacter_cube (rationalExtensionLeft g)

lemma norm_extendedComplexCharacter (g : rationalExtension) : ‖extendedComplexCharacter g‖=1 :=
  norm_complexCharacter (rationalExtensionLeft g)

/-- The rational extension normalizes the integral metaplectic kernel. -/
theorem globalKubotaKernel_conjugate (g : rationalExtension) (k : SL(2,O))
    (hk : k∈globalKubotaKernel) :
    (g:SL(2,O))*k*(g:SL(2,O))⁻¹∈globalKubotaKernel := by
  obtain ⟨hk3,hkv⟩ := (globalKubotaKernel_mem k).mp hk
  let n : levelThree := ⟨k,hk3⟩
  let n2 : rationalExtension := ⟨k,levelThree_le_rationalExtension hk3⟩
  let cn := levelThreeConjugate (g:SL(2,O)) n
  refine (globalKubotaKernel_mem _).mpr ⟨cn.property,?_⟩
  change complexCharacter cn=1
  rw [←extendedComplexCharacter_restrict cn]
  have he : (⟨(cn:SL(2,O)),levelThree_le_rationalExtension cn.property⟩:rationalExtension)=g*n2*g⁻¹ :=
    Subtype.ext rfl
  rw [he,map_mul,map_mul]
  have hn : extendedComplexCharacter n2=1 :=
    (extendedComplexCharacter_restrict n).trans hkv
  rw [hn,mul_one,←map_mul,mul_inv_cancel,map_one]

end RationalSource

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
