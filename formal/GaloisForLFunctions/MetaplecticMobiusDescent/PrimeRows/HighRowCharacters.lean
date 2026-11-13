/-
Characters of the high rows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.HighRowsClosedForms

/-!
# Characters of the high rows

Row characters, target rows and continued corrections of the high row family; mark exclusions,
conductor constants and raw rows; removing marked primes from the Euler product gives the
spectral compensated row.
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
open scoped Classical
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification UniqueFactorizationMonoid

def unitPart (u : FreeRow) (p : O) (hp : Prime p) : O :=
  Classical.choose ((FiniteMultiplicity.of_prime_left hp u.property.1).exists_eq_pow_mul_and_not_dvd)

theorem unitPart_spec (u : FreeRow) (p : O) (hp : Prime p) :
    u.val=p^(multiplicity p u.val)*unitPart u p hp ∧ ¬p∣unitPart u p hp :=
  Classical.choose_spec ((FiniteMultiplicity.of_prime_left hp u.property.1).exists_eq_pow_mul_and_not_dvd)

theorem unitPart_coprime (u : FreeRow) (p : O) (hp : Prime p) : IsCoprime (unitPart u p hp) p :=
  (hp.irreducible.coprime_iff_not_dvd.mpr (unitPart_spec u p hp).2).symm

theorem unitPart_ne_zero (u : FreeRow) (p : O) (hp : Prime p) : unitPart u p hp≠0 := by
  intro he
  have hu := (unitPart_spec u p hp).1
  rw [he,mul_zero] at hu
  exact u.property.1 hu

theorem multiplicity_lt_six (u : FreeRow) (p : O) (hp : Prime p) : multiplicity p u.val<6 := by
  let P : Ideal O := Ideal.span {p}
  have hP0 : P≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  have hP : Prime P := Ideal.prime_of_isPrime hP0 (Ideal.isPrime_span_singleton_of_prime hp)
  have hb : (Ideal.span {unitPart u p hp}:Ideal O)≠0 :=
    Ideal.span_singleton_eq_bot.not.mpr (unitPart_ne_zero u p hp)
  have he : (Ideal.span {u.val}:Ideal O)=P^(multiplicity p u.val)*Ideal.span {unitPart u p hp} := by
    conv_lhs => rw [(unitPart_spec u p hp).1]
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow]
  have hf := u.property.2 P
  rw [he,normalizedFactors_mul (pow_ne_zero _ hP0) hb,normalizedFactors_pow,
    normalizedFactors_irreducible hP.irreducible] at hf
  simp only [normalize_eq,Multiset.count_add,Multiset.count_nsmul,
    Multiset.count_singleton_self,mul_one] at hf
  omega

theorem canonical_decomposition (u : FreeRow) (p : O) (hp : Prime p) :
    u.val=unitPart u p hp*p^(multiplicity p u.val) ∧
      IsCoprime (unitPart u p hp) p ∧ multiplicity p u.val<6 := by
  exact ⟨(unitPart_spec u p hp).1.trans (mul_comm _ _),unitPart_coprime u p hp,
    multiplicity_lt_six u p hp⟩

theorem idealRowHighLocalFactor_canonical (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : lambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hprimary : lambda^2∣p-1)
    (hs : CanonicalQuadraticSieve.Supported (Ideal.span {p})) (x w z : ℂ) :
    ProbePhysical.idealRowHighLocalFactor η u.val (Ideal.span {p}) x w z=
      ∑ e : Fin 2,∑' l,∑' k,∑' m,
        ProbeEuler.sourceRowTerm p hp hg (ProbeRow.targetMonoid η p) (ProbeEuler.actualACube η p)
          (complexSexticChar (Ideal.span {p}) hg
            (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val) e.val l k m := by
  conv_lhs => rw [(canonical_decomposition u p hp).1]
  exact ProbePhysical.idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs
    (unitPart u p hp) (unitPart_coprime u p hp) (multiplicity p u.val) x w z

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve ProbePhysical
local notation "O" => Eisenstein.O

def rowMaskElement : O := 2*lambda

theorem rowMaskElement_ne_zero : rowMaskElement≠0 :=
  mul_ne_zero (by norm_num) residue_lambda_prime.ne_zero

def rawRow (u : FreeRow) : Character := Classical.choose
  (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
    rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))

theorem rawRow_coeff (u : FreeRow) (I : Ideal O) :
    idealCoeff (rawRow u) I=idealCoeff (fixedSourcePrincipal ∅ (by simp)) I*
      idealRowHom (rowMaskElement^6*u.val) I := by
  have he := (Classical.choose_spec
    (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
      rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2
  simpa only [one_pow,mul_one] using idealCoeff_eq_row _ (rawRow u) rowMaskElement 1 u.val he I

theorem outside_good_coprime (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (P : HeckeIdealSeries.PrimeIdeal) (hP : P.val∉S) :
    lambda∉P.val ∧ IsCoprime P.val (Ideal.span {rowMaskElement}) := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have hn : P.val∉fixedBadPrimes := fun hh => hP (hbad hh)
  have hg := (prime_good_iff_not_bad P.val).mpr hn
  refine ⟨hg.1,?_⟩
  have hc := (prime_coprime_fixedProduct S hS P).mpr hP
  rw [IsCoprime.prod_right_iff] at hc
  have hLam : Ideal.span {lambda}∈S := hbad (Finset.mem_insert_self _ _)
  have h2 : Ideal.span {(2 : O)}∈S := hbad (by simp [fixedBadPrimes,ramifiedIdeal,cubicTwoIdeal,Ideal.span_singleton_neg])
  unfold rowMaskElement
  rw [←Ideal.span_singleton_mul_span_singleton]
  exact (hc _ h2).mul_right (hc _ hLam)

theorem rawRow_prime_outside (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (hP : P.val∉S) :
    idealCoeff (rawRow u) P.val=idealRowHom u.val P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  obtain ⟨hg,hc⟩ := outside_good_coprime S hS hbad P hP
  rw [rawRow_coeff,fixedSourcePrincipal_prime]
  rw [if_neg (by simp),one_mul]
  rw [idealRowHom_argument_mul,idealRowHom_prime_sixth_mask rowMaskElement P.val hg,
    if_pos hc,one_mul]

def rowCharacter (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) : Character :=
  (rawRow u).excludePrimes S hS

def sourceRowCoeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) : Ideal O→*₀ℂ where
  toFun I := highExclusion S hS I*idealRowHom u.val I
  map_zero' := by rw [(idealRowHom u.val).map_zero, mul_zero]
  map_one' := by rw [map_one,map_one,mul_one]
  map_mul' I J := by simp only [map_mul]; ring

theorem hom_eq_of_primes (f g : Ideal O→*₀ℂ) (h : ∀P : HeckeIdealSeries.PrimeIdeal,f P.val=g P.val) : f=g := by
  ext I
  by_cases hI : I=0
  · subst I; rw [map_zero,map_zero]
  have hf := congrArg (fun F : Ideal O→*₀ℂ => F I) (IdealEuler.primeValueHom_eq f)
  have hg := congrArg (fun F : Ideal O→*₀ℂ => F I) (IdealEuler.primeValueHom_eq g)
  rw [←hf,←hg]
  change (if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map f).prod)=
    (if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map g).prod)
  rw [if_neg hI,if_neg hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  exact h ⟨P,UniqueFactorizationMonoid.prime_of_normalized_factor P hP⟩

theorem rowCharacter_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    idealCoeff (rowCharacter S hS u) I=highExclusion S hS I*idealRowHom u.val I := by
  have he : idealCoeff (rowCharacter S hS u)=sourceRowCoeff S hS u := by
    apply hom_eq_of_primes
    intro P
    change idealCoeff ((rawRow u).excludePrimes S hS) P.val=
      highExclusion S hS P.val*idealRowHom u.val P.val
    rw [excludedTarget_prime,highExclusion_prime]
    by_cases hP : P.val∈S
    · simp only [if_pos hP,zero_mul]
    · simp only [if_neg hP,one_mul]
      exact rawRow_prime_outside S hS hbad u P hP
  exact congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem target_inverseRow_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) :
    idealCoeff ((η.product (rawRow u).inverse).excludePrimes S hS) P.val=
      if P.val∈S then 0 else idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val) := by
  rw [excludedTarget_prime,idealCoeff_product,idealCoeff_inverse_conj]
  by_cases hP : P.val∈S
  · simp only [if_pos hP]
  · rw [if_neg hP,if_neg hP,rawRow_prime_outside S hS hbad u P hP]

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalRowCompletion
local notation "O" => Eisenstein.O

def targetRow (η : Character) (u : FreeRow) : Character := η.product (rawRow u).inverse

theorem rowCharacter_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (u : FreeRow)
    (s : ℂ) (hs : 1< s.re) :
    HasProd (fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} =>
      (1-idealRowHom u.val P.val.val*fullIdealWeight s P.val.val)⁻¹)
      (LFunction (rowCharacter S hS u) s) := by
  apply LFunction_hasProd_outside (rowCharacter S hS u) S (idealRowHom u.val) _ s hs
  intro P
  rw [rowCharacter_coeff S hS hbad,highExclusion_prime]
  split_ifs <;> simp only [zero_mul,one_mul]

theorem targetRow_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (s : ℂ) (hs : 1< s.re) :
    HasProd (fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} =>
      (1-idealCoeff η P.val.val*starRingEnd ℂ (idealRowHom u.val P.val.val)*
        fullIdealWeight s P.val.val)⁻¹)
      (LFunction ((targetRow η u).excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S (fun P => idealCoeff η P*starRingEnd ℂ (idealRowHom u.val P))
    (target_inverseRow_coeff S hS hbad η u) s hs

def localCorrection (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowHighLocalFactor η u.val P.val x w z *
    (1-fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*fullIdealWeight x P.val)

def globalCorrection (S : Finset (Ideal O)) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S},localCorrection η u P.val x w z

theorem localCorrection_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    HasProd (fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} => localCorrection η u P.val x w z)
      (markedIdealHighSeries S 1 η u.val x w z *
        (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹ * (LFunction (rowCharacter S hS u) w)⁻¹ *
          LFunction ((targetRow η u).excludePrimes S hS) x) := by
  have hx1 : 1< x.re := by linarith
  have hw1 : 1< w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re]; linarith
  have hF := excludedIdealHighSeries_row_hasProd_outside S hS η u.val x w z hx hw hz
  have hZ : HasProd (fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} =>
      ((1-fullIdealWeight (6*z) P.val.val)⁻¹)⁻¹)
      (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹ := by
    have h := fixedSourcePrincipal_hasProd S hS (6*z) hz1
    rw [HasProd] at h ⊢
    simpa only [Finset.prod_inv_distrib] using
      h.inv₀ (LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1)
  have hW : HasProd (fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} =>
      ((1-idealRowHom u.val P.val.val*fullIdealWeight w P.val.val)⁻¹)⁻¹)
      (LFunction (rowCharacter S hS u) w)⁻¹ := by
    have h := rowCharacter_hasProd S hS hbad u w hw1
    rw [HasProd] at h ⊢
    simpa only [Finset.prod_inv_distrib] using
      h.inv₀ (LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1)
  have hD := targetRow_hasProd S hS hbad η u x hx1
  have he := ((hF.mul hZ).mul hW).mul hD
  simpa only [localCorrection,inv_inv,div_eq_mul_inv] using he

theorem globalCorrection_multipliable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    Multipliable (fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} => localCorrection η u P.val x w z) :=
  (localCorrection_hasProd S hS hbad η u x w z hx hw hz).multipliable

theorem high_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    markedIdealHighSeries S 1 η u.val x w z=
      LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (rowCharacter S hS u) w /
        LFunction ((targetRow η u).excludePrimes S hS) x * globalCorrection S η u x w z := by
  have hx1 : 1< x.re := by linarith
  have hw1 : 1< w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re]; linarith
  have hZ := LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := LFunction_ne_zero_of_one_lt_re ((targetRow η u).excludePrimes S hS) hx1
  rw [globalCorrection,(localCorrection_hasProd S hS hbad η u x w z hx hw hz).tprod_eq]
  field_simp

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure ProbePhysical
local notation "O" => Eisenstein.O

def conductorConstant : ℕ :=
  (Ideal.span {rowMaskElement}:Ideal O).absNorm*(Ideal.span {(72 : O)}:Ideal O).absNorm

theorem rawRow_conductor (u : FreeRow) :
    (rawRow u).modulus.absNorm≤ conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm := by
  have hb := (Classical.choose_spec
    (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
      rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).1
  change (rawRow u).modulus.absNorm≤ _ at hb
  simpa [rowConductorBound,conductorConstant,fixedSourcePrincipal,HeckeRayFamily.character,
    Character.ofResidue] using hb

theorem rowCharacter_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) :
    (rowCharacter S hS u).modulus.absNorm≤
      conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm*(∏P∈S,P).absNorm := by
  change ((rawRow u).modulus*(∏P∈S,P)).absNorm≤ _
  rw [map_mul]
  exact Nat.mul_le_mul_right _ (rawRow_conductor u)

theorem targetRow_conductor (η : Character) (u : FreeRow) :
    (targetRow η u).modulus.absNorm≤η.modulus.absNorm*conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Finite (O ⧸ (rawRow u).modulus) := Ring.HasFiniteQuotients.finiteQuotient (rawRow u).modulus_ne_bot
  change (η.modulus⊓(rawRow u).modulus).absNorm≤ _
  calc
    _ ≤ η.modulus.absNorm*(rawRow u).modulus.absNorm :=
      FiniteConductor.absNorm_inf_le_mul _ _
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left η.modulus.absNorm (rawRow_conductor u)

theorem targetRow_excluded_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) :
    ((targetRow η u).excludePrimes S hS).modulus.absNorm≤
      η.modulus.absNorm*conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm*(∏P∈S,P).absNorm := by
  change ((targetRow η u).modulus*(∏P∈S,P)).absNorm≤ _
  rw [map_mul]
  exact Nat.mul_le_mul_right _ (targetRow_conductor η u)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ComplexConjugate
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

theorem localCorrection_coordinates (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p}) (x w z : ℂ) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ u.val)
    localCorrection η u ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ x w z=
      idealRowHighLocalFactor η u.val (Ideal.span {p}) x w z *
        (1-coordV Q z)*(1-coordW Q rho w)/(1-coordD Q (targetMonoid η p) rho x) := by
  dsimp only
  have hP0 : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  unfold localCorrection coordV coordW coordD
  simp only [fullIdealWeight,hP0,ite_false,Complex.ofReal_natCast]
  rw [idealCoeff_span η hp.ne_zero,idealRowHom_prime u.val (Ideal.span {p}) hg]
  rw [show -(6*z)=(-6 : ℂ)*z by ring]
  rfl

theorem localCorrection_unramified (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : CanonicalQuadraticSieve.Supported (Ideal.span {p})) (hu : IsCoprime u.val p)
    (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    localCorrection η u ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ x w z=
      actualUnramifiedClosed η p u.val hg x w z := by
  rw [localCorrection_coordinates η u p hp hg]
  rw [idealRowHighLocalFactor_unramified η p hp hg hc hprimary hs u.val hu x w z hx hw hz]
  have hgeom := row_initial_geometric η p hp hg hc u.val hu x w z hx hw hz
  dsimp only at hgeom
  have hV := one_sub_ne_zero_of_norm_lt_one _ hgeom.1
  have hW := one_sub_ne_zero_of_norm_lt_one _ hgeom.2.2.1
  have hD := one_sub_ne_zero_of_norm_lt_one _ hgeom.2.2.2
  unfold actualUnramifiedClosed
  change _=unramifiedClosed _ _ (targetMonoid η p) _ x w z
  field_simp

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ComplexConjugate
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => Eisenstein.O

def idealUnramifiedCorrection (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (x w z : ℂ) : ℂ :=
  unramifiedClosed P.val.absNorm (actualAPhase η (primaryIdealGenerator P.val))
    (idealCoeff η P.val) (idealRowHom u.val P.val) x w z

theorem localCorrection_unramified_ideal (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hcop : IsCoprime P.val (Ideal.span {u.val}))
    (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    localCorrection η u P x w z=idealUnramifiedCorrection η u P x w z := by
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)
  have hprimary := (primaryIdealGenerator_spec P.val (supported_primaryIdealGenerator_ne_zero P.val hs)).2
  have hu : IsCoprime u.val p := ((Ideal.isCoprime_span_singleton_iff p u.val).mp
    (by rw [hspan]; exact hcop)).symm
  have he := localCorrection_unramified η u p hp hg.1 hg.2 hprimary hsp hu x w z hx hw hz
  have hP : (⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ : HeckeIdealSeries.PrimeIdeal)=P := Subtype.ext hspan
  rw [hP] at he
  unfold actualUnramifiedClosed at he
  rw [←idealCoeff_span η hp.ne_zero,←idealRowHom_prime u.val (Ideal.span {p}) hg.1,hspan] at he
  exact he

theorem localCorrection_outside_unramified (S : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (P : HeckeIdealSeries.PrimeIdeal) (hP : P.val∉S) (hcop : IsCoprime P.val (Ideal.span {u.val}))
    (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    localCorrection η u P x w z=idealUnramifiedCorrection η u P x w z :=
  localCorrection_unramified_ideal η u P (outside_prime_supported S hbad P hP) hcop x w z hx hw hz

theorem localCorrection_ramified (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    localCorrection η u P x w z=
      idealRowHighLocalFactor η u.val P.val x w z*(1-fullIdealWeight (6*z) P.val) := by
  have hu : u.val∈P.val := (Ideal.dvd_iff_le.mp hP) (Ideal.subset_span (by simp))
  have hr : idealRowHom u.val P.val=0 := idealRowHom_zero_of_dvd u.val P.property (dvd_refl _) hu
  simp only [localCorrection,hr,map_zero,mul_zero,zero_mul,sub_zero,mul_one,div_one]

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

def ramifiedCorrection (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  let p := primaryIdealGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  letI : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (CenteredMomentSourceRow.primary_span_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)).1
  ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    x w z (multiplicity p u.val)

theorem ramifiedCorrection_bound (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤ P.val.absNorm) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤ x.re) (hw : (19/20 : ℝ)≤ w.re) (hz : (33/200 : ℝ)≤ z.re) :
    ‖ramifiedCorrection η u P hs x w z‖≤193 := by
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  exact ramifiedClosed_bound p hp hg.1 hg.2 _ _ _ x w z
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) ha
    (complexSexticChar_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz _

theorem localCorrection_eq_ramified (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hPu : P.val∣Ideal.span {u.val})
    (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    localCorrection η u P x w z=ramifiedCorrection η u P hs x w z := by
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)
  have hprimary := (primaryIdealGenerator_spec P.val (supported_primaryIdealGenerator_ne_zero P.val hs)).2
  have hdiv : p∣u.val := Ideal.span_singleton_le_span_singleton.mp
    (by rw [hspan]; exact Ideal.dvd_iff_le.mp hPu)
  have hj0 : multiplicity p u.val≠0 := ne_of_gt (multiplicity_pos_of_dvd hdiv)
  have hρ := complexSexticChar_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)
  have hgeom := row_initial_geometric η p hp hg.1 hg.2 (unitPart u p hp)
    (unitPart_coprime u p hp) x w z hx hw hz
  dsimp only at hgeom
  have hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    have hpos : (0 : ℝ)< Ideal.absNorm (Ideal.span {p}) :=
      HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
    have he := evenRatio_eq_coordR _ hpos (actualACube η p) x z
    simp only [Complex.ofReal_natCast] at he
    rw [he]
    exact hgeom.2.1
  rw [localCorrection_ramified η u P hPu,←hspan,
    idealRowHighLocalFactor_canonical η u p hp hg.1 hg.2 hprimary hsp]
  have he := sourceRowSeries_ramified p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p) _ x w z hρ hgeom.1 hR
    hgeom.2.2.1 (multiplicity p u.val) hj0 (multiplicity_lt_six u p hp)
  have hP0 : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  convert he using 1
  · simp only [ProbeEuler.sourceRowSeries,fullIdealWeight,
      hP0,ite_false,Complex.ofReal_natCast,coordV]
    rw [show -(6*z)=(-6 : ℂ)*z by ring]
  · rfl

def ramifiedPrimes (S : Finset (Ideal O)) (u : FreeRow) : Finset HeckeIdealSeries.PrimeIdeal :=
  (HeckeIdealSeries.primeSet (Ideal.span {u.val})).filter (fun P => P.val∉S)

theorem ramified_product_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : Character) (u : FreeRow) (x w z : ℂ),
      (7/8 : ℝ)≤ x.re → (19/20 : ℝ)≤ w.re → (33/200 : ℝ)≤ z.re →
      ‖∏ P∈(ramifiedPrimes S u).attach,
        ramifiedCorrection η u P.val
          (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound 193 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro S hS η u x w z hx hw hz
  rw [norm_prod]
  calc
    _ ≤ ∏ P∈(ramifiedPrimes S u).attach,(193 : ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro P hP
      exact ramifiedCorrection_bound η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w z hx hw hz
    _ = (193 : ℝ)^(ramifiedPrimes S u).card := by simp
    _ ≤ (193 : ℝ)^(primeSupport (Ideal.span {u.val})).card := by
      apply pow_le_pow_right₀ (by norm_num)
      rw [←HeckeDeletionBounds.primeSet_card]
      exact Finset.card_filter_le _ _
    _ ≤ _ := hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => Eisenstein.O

def unramifiedFactor (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (x w z : ℂ) : ℂ :=
  if P.val∣Ideal.span {u.val} then 1 else idealUnramifiedCorrection η u P x w z

def unramifiedProduct (S : Finset (Ideal O)) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S},unramifiedFactor η u P.val x w z

theorem unramifiedFactor_defect (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hP : 4≤ P.val.absNorm) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤ x.re) (hw : (9/10 : ℝ)≤ w.re) (hz : (4/25 : ℝ)≤ z.re) :
    ‖unramifiedFactor η u P x w z-1‖≤ globalPrimeDefectBound P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using globalPrimeDefectBound_nonneg P
  · apply unramifiedClosed_open_region_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact hx
    · exact hw
    · exact hz

theorem unramifiedProduct_defect (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤ x.re) (hw : (9/10 : ℝ)≤ w.re) (hz : (4/25 : ℝ)≤ z.re) :
    ‖unramifiedProduct S η u x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P => unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

theorem unramifiedProduct_multipliable (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤ x.re) (hw : (9/10 : ℝ)≤ w.re) (hz : (4/25 : ℝ)≤ z.re) :
    Multipliable (fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} => unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} => unramifiedFactor η u P.val x w z
  let B := fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} => globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤ B P :=
    unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem unramifiedProduct_analytic_x (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (w z : ℂ) (hw : (9/10 : ℝ)≤ w.re) (hz : (4/25 : ℝ)≤ z.re) :
    AnalyticOnNhd ℂ (fun x => unramifiedProduct S η u x w z) {x : ℂ | 7/8< x.re} := by
  apply normalProduct_analytic _ _ _ (isOpen_lt continuous_const Complex.continuous_re) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,if_pos h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [unramifiedFactor,if_neg h]
      apply unramifiedClosed_analytic_x
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hz
  · intro P x hx
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem unramifiedProduct_analytic_w (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x z : ℂ) (hx : (7/8 : ℝ)≤ x.re) (hz : (4/25 : ℝ)≤ z.re) :
    AnalyticOnNhd ℂ (fun w => unramifiedProduct S η u x w z) {w : ℂ | 9/10< w.re} := by
  apply normalProduct_analytic _ _ _ (isOpen_lt continuous_const Complex.continuous_re) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,if_pos h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [unramifiedFactor,if_neg h]
      apply unramifiedClosed_analytic_w
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hx
      · exact hz
  · intro P w hw
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem unramifiedProduct_analytic_z (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w : ℂ) (hx : (7/8 : ℝ)≤ x.re) (hw : (9/10 : ℝ)≤ w.re) :
    AnalyticOnNhd ℂ (fun z => unramifiedProduct S η u x w z) {z : ℂ | 4/25< z.re} := by
  apply normalProduct_analytic _ _ _ (isOpen_lt continuous_const Complex.continuous_re) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ => if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,if_pos h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [if_neg h]
      apply unramifiedClosed_analytic_z
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hx
  · intro P z hz
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => Eisenstein.O

lemma actualACube_norm_le (η : Character) (p : O) : ‖actualACube η p‖≤1 := by
  have h := actualAPhase_norm_le_one η p
  rw [←actualACube_sq,norm_pow] at h
  nlinarith [norm_nonneg (actualACube η p)]

theorem ramifiedCorrection_analytic_x (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤ P.val.absNorm) (w z : ℂ) (hz : (4/25 : ℝ)≤ z.re) :
    AnalyticOnNhd ℂ (fun x => ramifiedCorrection η u P hs x w z) {x : ℂ | 7/8< x.re} := by
  let : (Ideal.span {primaryIdealGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_x
  · simpa only [CenteredMomentSourceRow.primary_span_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hz

theorem ramifiedCorrection_analytic_w (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤ P.val.absNorm) (x z : ℂ)
    (hx : (7/8 : ℝ)≤ x.re) (hz : (4/25 : ℝ)≤ z.re) :
    Differentiable ℂ (fun w => ramifiedCorrection η u P hs x w z) := by
  let : (Ideal.span {primaryIdealGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_w
  · simpa only [CenteredMomentSourceRow.primary_span_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx
  · exact hz

theorem ramifiedCorrection_analytic_z (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤ P.val.absNorm) (x w : ℂ) (hx : (7/8 : ℝ)≤ x.re) :
    AnalyticOnNhd ℂ (fun z => ramifiedCorrection η u P hs x w z) {z : ℂ | 4/25< z.re} := by
  let : (Ideal.span {primaryIdealGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_z
  · simpa only [CenteredMomentSourceRow.primary_span_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx

def ramifiedProduct (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏ P∈(ramifiedPrimes S u).attach,ramifiedCorrection η u P.val
    (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z

def continuedCorrection (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ramifiedProduct S hS η u x w z*unramifiedProduct S η u x w z

theorem continuedCorrection_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : Character) (u : FreeRow) (x w z : ℂ),
      (7/8 : ℝ)≤ x.re → (19/20 : ℝ)≤ w.re → (33/200 : ℝ)≤ z.re →
      ‖continuedCorrection S hS η u x w z‖≤ C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := ramified_product_subpower ε hε
  refine ⟨C*(3/2),by positivity,?_⟩
  intro S hS η u x w z hx hw hz
  have hR := hbound S hS η u x w z hx hw hz
  have hU := unramifiedProduct_defect S hS.tail η u x w z hx (by linarith) (by linarith)
  have hnorm : ‖unramifiedProduct S η u x w z‖≤3/2 := by
    have hh := norm_add_le (unramifiedProduct S η u x w z-1) (1 : ℂ)
    simp only [sub_add_cancel,norm_one] at hh
    linarith
  rw [continuedCorrection,norm_mul]
  apply (mul_le_mul hR hnorm (norm_nonneg _) (by positivity)).trans
  exact le_of_eq (by ring)

theorem continuedCorrection_analytic_x (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (w z : ℂ) (hw : (9/10 : ℝ)≤ w.re) (hz : (4/25 : ℝ)≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedCorrection S hS η u x w z) {x : ℂ | 7/8< x.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_x S hS.tail η u w z hw hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact ramifiedCorrection_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) w z hz

theorem continuedCorrection_analytic_w (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (hx : (7/8 : ℝ)≤ x.re) (hz : (4/25 : ℝ)≤ z.re) :
    AnalyticOnNhd ℂ (fun w => continuedCorrection S hS η u x w z) {w : ℂ | 9/10< w.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_w S hS.tail η u x z hx hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact (ramifiedCorrection_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x z hx hz).differentiableOn.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)

theorem continuedCorrection_analytic_z (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w : ℂ) (hx : (7/8 : ℝ)≤ x.re) (hw : (9/10 : ℝ)≤ w.re) :
    AnalyticOnNhd ℂ (fun z => continuedCorrection S hS η u x w z) {z : ℂ | 4/25< z.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_z S hS.tail η u x w hx hw)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact ramifiedCorrection_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w hx

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => Eisenstein.O

def ramifiedIndices (S : Finset (Ideal O)) (u : FreeRow) : Finset {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} :=
  (HeckeIdealSeries.primeSet (Ideal.span {u.val})).subtype (fun P => P.val∉S)

theorem mem_ramifiedIndices (S : Finset (Ideal O)) (u : FreeRow)
    (P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S}) : P∈ramifiedIndices S u ↔ P.val.val∣Ideal.span {u.val} := by
  simp only [ramifiedIndices,Finset.mem_subtype,HeckeIdealSeries.mem_primeSet,
    primeSupport,Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff
      (show (Ideal.span {u.val}:Ideal O)≠0 from Ideal.span_singleton_eq_bot.not.mpr u.property.1),
    P.val.property,true_and]

def ramifiedFactor (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S}) (x w z : ℂ) : ℂ :=
  if P.val.val∣Ideal.span {u.val} then
    ramifiedCorrection η u P.val (outside_prime_supported S hS.bad P.val P.property) x w z else 1

theorem ramifiedFactor_hasProd (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    HasProd (fun P => ramifiedFactor S hS η u P x w z) (ramifiedProduct S hS η u x w z) := by
  have he : (∏ P∈ramifiedIndices S u,ramifiedFactor S hS η u P x w z)=
      ramifiedProduct S hS η u x w z := by
    unfold ramifiedProduct
    apply Finset.prod_bij (fun P hP =>
      (⟨P.val,Finset.mem_filter.mpr ⟨Finset.mem_subtype.mp hP,P.property⟩⟩ : ramifiedPrimes S u))
    · intro P hP; exact Finset.mem_attach _ _
    · intro P hP Q hQ heq
      exact Subtype.ext (congrArg (fun R : ramifiedPrimes S u => R.val) heq)
    · intro P hP
      refine ⟨⟨P.val,(Finset.mem_filter.mp P.property).2⟩,?_,?_⟩
      · exact Finset.mem_subtype.mpr (Finset.mem_filter.mp P.property).1
      · rfl
    · intro P hP
      simp only [ramifiedFactor,if_pos ((mem_ramifiedIndices S u P).mp hP)]
  rw [←he]
  apply hasProd_prod_of_ne_finset_one
  intro P hP
  exact if_neg (fun hd => hP ((mem_ramifiedIndices S u P).mpr hd))

theorem supported_prime_coprime (P : HeckeIdealSeries.PrimeIdeal) (hs : Supported P.val) (u : O)
    (hn : ¬P.val∣Ideal.span {u}) : IsCoprime P.val (Ideal.span {u}) := by
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have he : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  have hnot : ¬p∣u := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←he,Ideal.span_singleton_le_span_singleton]
    exact hd
  rw [←he,Ideal.isCoprime_span_singleton_iff]
  exact hp.irreducible.coprime_iff_not_dvd.mpr hnot

theorem continuedCorrection_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    continuedCorrection S hS η u x w z=globalCorrection S η u x w z := by
  have hr := ramifiedFactor_hasProd S hS η u x w z
  have hu := (unramifiedProduct_multipliable S hS.tail η u x w z
    (by linarith) (by linarith) (by linarith)).hasProd
  have he := hr.mul hu
  have hlocal (P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S}) :
      ramifiedFactor S hS η u P x w z*unramifiedFactor η u P.val x w z=
        localCorrection η u P.val x w z := by
    have hs := outside_prime_supported S hS.bad P.val P.property
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simp only [ramifiedFactor,unramifiedFactor,if_pos h,mul_one]
      exact (localCorrection_eq_ramified η u P.val hs h x w z hx hw hz).symm
    · simp only [ramifiedFactor,unramifiedFactor,if_neg h,one_mul]
      exact (localCorrection_unramified_ideal η u P.val hs
        (supported_prime_coprime P.val hs u.val h) x w z hx hw hz).symm
  have hh : HasProd (fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} => localCorrection η u P.val x w z)
      (continuedCorrection S hS η u x w z) := by
    simpa only [hlocal,continuedCorrection,unramifiedProduct] using he
  exact hh.tprod_eq.symm

theorem high_L_factorization_continued (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    markedIdealHighSeries S 1 η u.val x w z=
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (rowCharacter S hS.prime u) w /
        LFunction ((targetRow η u).excludePrimes S hS.prime) x*continuedCorrection S hS η u x w z := by
  rw [continuedCorrection_eq_initial S hS η u x w z hx hw hz]
  exact high_L_factorization S hS.prime hS.bad η u x w z hx hw hz

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

def continuedSeries (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (rowCharacter S hS.prime u) w*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x*
      continuedCorrection S hS η u x w z

theorem continuedSeries_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    continuedSeries S hS η u x w z=markedIdealHighSeries S 1 η u.val x w z := by
  have hx0 : x≠0 := by intro h; simp only [h,Complex.zero_re] at hx; linarith
  have hx1 : x≠1 := by intro h; simp only [h,Complex.one_re] at hx; linarith
  rw [continuedSeries,HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,
    high_L_factorization_continued S hS η u x w z hx hw hz,div_eq_mul_inv]

theorem continuedSeries_differentiableAt_x (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)< x.re) (hbeta : HeckeZeroSupremum.beta< x.re)
    (hw : (9/10 : ℝ)≤ w.re) (hz : (4/25 : ℝ)≤ z.re) :
    DifferentiableAt ℂ (fun x => continuedSeries S hS η u x w z) x := by
  exact ((HeckeReciprocal.reciprocal_differentiableAt _ hbeta).const_mul _).mul
    ((continuedCorrection_analytic_x S hS η u w z hw hz) x hx).differentiableAt

theorem continuedSeries_differentiableAt_w (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤ x.re) (hw : (9/10 : ℝ)< w.re) (hz : (4/25 : ℝ)≤ z.re)
    (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w => continuedSeries S hS η u x w z) w := by
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw; linarith
  exact (((LFunction_differentiableAt (rowCharacter S hS.prime u) hw0 hpole).const_mul _).mul_const _).mul
    ((continuedCorrection_analytic_w S hS η u x z hx hz) w hw).differentiableAt

theorem continuedSeries_differentiableAt_z (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤ x.re) (hw : (9/10 : ℝ)≤ w.re) (hz : (4/25 : ℝ)< z.re)
    (hpole : 6*z≠1) :
    DifferentiableAt ℂ (fun z => continuedSeries S hS η u x w z) z := by
  have hz0 : 6*z≠0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.mul_re] at he
    linarith
  exact ((((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) hz0 (Or.inl hpole)).comp z
    (differentiableAt_id.const_mul 6)).mul_const _).mul_const _).mul
      ((continuedCorrection_analytic_z S hS η u x w hx hw) z hz).differentiableAt

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => Eisenstein.O

theorem unramifiedFactor_first_defect (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hP : 4≤ P.val.absNorm) (x w z : ℂ) (eps : ℝ) (heps : 0< eps)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hw : -(1/100:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    ‖unramifiedFactor η u P x w z-1‖≤ firstPrimeDefectBound eps P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using firstPrimeDefectBound_nonneg eps P
  · apply unramifiedClosed_first_region_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact heps
    · exact hx
    · exact hz
    · exact hw
    · exact hxw

theorem unramifiedProduct_first_defect (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hw : -(1/100:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    ‖unramifiedProduct S η u x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P => unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw hxw) hS.half hS.small

theorem unramifiedProduct_first_multipliable (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hw : -(1/100:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    Multipliable (fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S}=> unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S}=> unramifiedFactor η u P.val x w z
  let B := fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S}=> firstPrimeDefectBound eps P.val
  have hB (P) : ‖F P-1‖≤ B P :=
    unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw hxw
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => Eisenstein.O

theorem unramifiedProduct_first_analytic_x (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (w z : ℂ)
    (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> unramifiedProduct S η u x w z)
      {x : ℂ | max (51/100:ℝ) (1+eps-w.re)< x.re} := by
  apply normalProduct_analytic _ _ _ (isOpen_lt continuous_const Complex.continuous_re) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,if_pos h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,if_neg h]
      apply (unramifiedClosed_first_analytic_x _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro x hx
      change max (51/100:ℝ) (1+eps-w.re)< x.re at hx
      have hx' := (lt_of_le_of_lt (le_max_left (51/100:ℝ) (1+eps-w.re)) hx)
      change (1/2:ℝ)< x.re
      linarith
  · intro P x hx
    have hx' := (lt_of_le_of_lt (le_max_left (51/100:ℝ) (1+eps-w.re)) hx)
    have hxw := (lt_of_le_of_lt (le_max_right (51/100:ℝ) (1+eps-w.re)) hx)
    exact unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx'.le hz hw (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_analytic_w (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> unramifiedProduct S η u x w z)
      {w : ℂ | max (-(1/100:ℝ)) (1+eps-x.re)< w.re} := by
  apply normalProduct_analytic _ _ _ (isOpen_lt continuous_const Complex.continuous_re) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,if_pos h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,if_neg h]
      exact (unramifiedClosed_first_analytic_w _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith) (by linarith)).mono
          (Set.subset_univ _)
  · intro P w hw
    have hw' := (lt_of_le_of_lt (le_max_left (-(1/100:ℝ)) (1+eps-x.re)) hw)
    have hxw := (lt_of_le_of_lt (le_max_right (-(1/100:ℝ)) (1+eps-x.re)) hw)
    exact unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw'.le (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_analytic_z (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    AnalyticOnNhd ℂ (fun z=> unramifiedProduct S η u x w z) {z : ℂ | (17/50:ℝ)< z.re} := by
  apply normalProduct_analytic _ _ _ (isOpen_lt continuous_const Complex.continuous_re) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ=> if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [if_pos h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [if_neg h]
      apply (unramifiedClosed_first_analytic_z _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro z hz
      change (17/50:ℝ)< z.re at hz
      change (1/3:ℝ)< z.re
      linarith
  · intro P z hz
    exact unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz.le hw hxw
  · exact hS.half

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

theorem ramifiedCorrection_first_analytic_x (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤ P.val.absNorm) (w z : ℂ) (hz : (1/3 : ℝ)≤ z.re) :
    AnalyticOnNhd ℂ (fun x => ramifiedCorrection η u P hs x w z) {x : ℂ | 1/2< x.re} := by
  let : (Ideal.span {primaryIdealGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_first_analytic_x
  · simpa only [CenteredMomentSourceRow.primary_span_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hz

theorem ramifiedCorrection_first_analytic_w (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤ P.val.absNorm) (x z : ℂ)
    (hx : (1/2 : ℝ)≤ x.re) (hz : (1/3 : ℝ)≤ z.re) :
    Differentiable ℂ (fun w => ramifiedCorrection η u P hs x w z) := by
  let : (Ideal.span {primaryIdealGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_first_analytic_w
  · simpa only [CenteredMomentSourceRow.primary_span_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx
  · exact hz

theorem ramifiedCorrection_first_analytic_z (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤ P.val.absNorm) (x w : ℂ) (hx : (1/2 : ℝ)≤ x.re) :
    AnalyticOnNhd ℂ (fun z => ramifiedCorrection η u P hs x w z) {z : ℂ | 1/3< z.re} := by
  let : (Ideal.span {primaryIdealGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_first_analytic_z
  · simpa only [CenteredMomentSourceRow.primary_span_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx

theorem ramifiedCorrection_first_bound (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤ P.val.absNorm) (x w z : ℂ)
    (hx : (51/100 : ℝ)≤ x.re) (hw : -(1/100 : ℝ)≤ w.re) (hz : (17/50 : ℝ)≤ z.re) (hxw : 1≤ x.re+w.re) :
    ‖ramifiedCorrection η u P hs x w z‖≤193 := by
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  exact ramifiedClosed_first_region_bound p hp hg.1 hg.2 _ _ _ x w z
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) ha
    (complexSexticChar_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz hxw _ (multiplicity_lt_six u p hp)

theorem ramified_product_first_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : Character) (u : FreeRow) (x w z : ℂ),
      (51/100 : ℝ)≤ x.re → -(1/100 : ℝ)≤ w.re → (17/50 : ℝ)≤ z.re → 1≤ x.re+w.re →
      ‖∏ P∈(ramifiedPrimes S u).attach,
        ramifiedCorrection η u P.val
          (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound 193 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro S hS η u x w z hx hw hz hxw
  rw [norm_prod]
  calc
    _ ≤ ∏ P∈(ramifiedPrimes S u).attach,(193 : ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro P hP
      exact ramifiedCorrection_first_bound η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w z hx hw hz hxw
    _ = (193 : ℝ)^(ramifiedPrimes S u).card := by simp
    _ ≤ (193 : ℝ)^(primeSupport (Ideal.span {u.val})).card := by
      apply pow_le_pow_right₀ (by norm_num)
      rw [←HeckeDeletionBounds.primeSet_card]
      exact Finset.card_filter_le _ _
    _ ≤ _ := hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1)

theorem continuedCorrection_first_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (η : Character) (u : FreeRow) (x w z : ℂ),
      (51/100:ℝ)≤ x.re → -(1/100:ℝ)≤ w.re → (17/50:ℝ)≤ z.re →
      1+eps≤ x.re+w.re →
      ‖continuedCorrection S hS η u x w z‖≤ C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := ramified_product_first_subpower ε hε
  refine ⟨C*(3/2),by positivity,?_⟩
  intro eps S hS hfirst η u x w z hx hw hz hxw
  have hR := hbound S hS η u x w z hx hw hz (by linarith [hfirst.positive])
  have hU := unramifiedProduct_first_defect eps S hfirst η u x w z hx hz hw hxw
  have hnorm : ‖unramifiedProduct S η u x w z‖≤3/2 := by
    have hh := norm_add_le (unramifiedProduct S η u x w z-1) (1:ℂ)
    simp only [sub_add_cancel,norm_one] at hh
    linarith
  rw [continuedCorrection,norm_mul]
  apply (mul_le_mul hR hnorm (norm_nonneg _) (by positivity)).trans
  exact le_of_eq (by ring)

theorem continuedCorrection_first_analytic_x (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (w z : ℂ)
    (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> continuedCorrection S hS η u x w z)
      {x : ℂ | max (51/100:ℝ) (1+eps-w.re)< x.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_first_analytic_x eps S hfirst η u w z hw hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  apply (ramifiedCorrection_first_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    w z (by linarith)).mono
  intro x hx
  change max (51/100:ℝ) (1+eps-w.re)< x.re at hx
  have hh := (lt_of_le_of_lt (le_max_left (51/100:ℝ) (1+eps-w.re)) hx)
  change (1/2:ℝ)< x.re
  linarith

theorem continuedCorrection_first_analytic_w (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> continuedCorrection S hS η u x w z)
      {w : ℂ | max (-(1/100:ℝ)) (1+eps-x.re)< w.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_first_analytic_w eps S hfirst η u x z hx hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact (ramifiedCorrection_first_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x z (by linarith) (by linarith)).differentiableOn.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

theorem continuedCorrection_first_analytic_z (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    AnalyticOnNhd ℂ (fun z=> continuedCorrection S hS η u x w z) {z : ℂ | (17/50:ℝ)< z.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_first_analytic_z eps S hfirst η u x w hx hw hxw)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  apply (ramifiedCorrection_first_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x w (by linarith)).mono
  intro z hz
  change (17/50:ℝ)< z.re at hz
  change (1/3:ℝ)< z.re
  linarith

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => Eisenstein.O

theorem unramifiedFactor_first_neighborhood_defect (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hP : 4≤ P.val.absNorm) (x w z : ℂ) (eps : ℝ) (heps : 0< eps)
    (hx : (101/200:ℝ)≤ x.re) (hz : (27/80:ℝ)≤ z.re)
    (hw : -(3/200:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    ‖unramifiedFactor η u P x w z-1‖≤ firstPrimeDefectBound eps P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using firstPrimeDefectBound_nonneg eps P
  · apply unramifiedClosed_first_neighborhood_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact heps
    · exact hx
    · exact hz
    · exact hw
    · exact hxw

theorem unramifiedProduct_first_neighborhood_analytic_x (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (w z : ℂ)
    (hw : -(3/200:ℝ)≤ w.re) (hz : (27/80:ℝ)≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> unramifiedProduct S η u x w z)
      {x : ℂ | max (101/200:ℝ) (1+eps-w.re)< x.re} := by
  apply normalProduct_analytic _ _ _ (isOpen_lt continuous_const Complex.continuous_re) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,if_pos h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,if_neg h]
      apply (unramifiedClosed_first_analytic_x _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro x hx
      change max (101/200:ℝ) (1+eps-w.re)< x.re at hx
      have hx' := (lt_of_le_of_lt (le_max_left (101/200:ℝ) (1+eps-w.re)) hx)
      change (1/2:ℝ)< x.re
      linarith
  · intro P x hx
    have hx' := (lt_of_le_of_lt (le_max_left (101/200:ℝ) (1+eps-w.re)) hx)
    have hxw := (lt_of_le_of_lt (le_max_right (101/200:ℝ) (1+eps-w.re)) hx)
    exact unramifiedFactor_first_neighborhood_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx'.le hz hw (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_neighborhood_analytic_w (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (101/200:ℝ)≤ x.re) (hz : (27/80:ℝ)≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> unramifiedProduct S η u x w z)
      {w : ℂ | max (-(3/200:ℝ)) (1+eps-x.re)< w.re} := by
  apply normalProduct_analytic _ _ _ (isOpen_lt continuous_const Complex.continuous_re) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,if_pos h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,if_neg h]
      exact (unramifiedClosed_first_analytic_w _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith) (by linarith)).mono
          (Set.subset_univ _)
  · intro P w hw
    have hw' := (lt_of_le_of_lt (le_max_left (-(3/200:ℝ)) (1+eps-x.re)) hw)
    have hxw := (lt_of_le_of_lt (le_max_right (-(3/200:ℝ)) (1+eps-x.re)) hw)
    exact unramifiedFactor_first_neighborhood_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw'.le (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_neighborhood_analytic_z (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (101/200:ℝ)≤ x.re) (hw : -(3/200:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    AnalyticOnNhd ℂ (fun z=> unramifiedProduct S η u x w z) {z : ℂ | (27/80:ℝ)< z.re} := by
  apply normalProduct_analytic _ _ _ (isOpen_lt continuous_const Complex.continuous_re) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ=> if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [if_pos h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [if_neg h]
      apply (unramifiedClosed_first_analytic_z _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro z hz
      change (27/80:ℝ)< z.re at hz
      change (1/3:ℝ)< z.re
      linarith
  · intro P z hz
    exact unramifiedFactor_first_neighborhood_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz.le hw hxw
  · exact hS.half

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

def continuedHighSeries (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeOrigin.continued (rowCharacter S hS.prime u) w*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x*
    continuedCorrection S hS η u x w z

theorem continuedHighSeries_eq_series (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) (hw0 : w≠0) (hw1 : w≠1) :
    continuedHighSeries S hS η u x w z=continuedSeries S hS η u x w z := by
  rw [continuedHighSeries,HeckeOrigin.continued_eq _ hw0 hw1,continuedSeries]

theorem continuedHighSeries_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    continuedHighSeries S hS η u x w z=markedIdealHighSeries S 1 η u.val x w z := by
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw; linarith
  have hw1 : w≠1 := by intro h; simp only [h,Complex.one_re] at hw; linarith
  rw [continuedHighSeries_eq_series S hS η u x w z hw0 hw1,
    continuedSeries_eq_initial S hS η u x w z hx hw hz]

theorem continuedHighSeries_first_differentiableAt_w (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hw : max (-(1/100:ℝ)) (1+eps-x.re)< w.re)
    (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=> continuedHighSeries S hS η u x w z) w := by
  exact (((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _).mul
    ((continuedCorrection_first_analytic_w eps S hS hfirst η u x z hx hz) w hw).differentiableAt

theorem continuedHighSeries_first_differentiableAt_x (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hx : max (51/100:ℝ) (1+eps-w.re)< x.re)
    (hbeta : HeckeZeroSupremum.beta< x.re) :
    DifferentiableAt ℂ (fun x=> continuedHighSeries S hS η u x w z) x := by
  exact ((HeckeReciprocal.reciprocal_differentiableAt _ hbeta).const_mul _).mul
    ((continuedCorrection_first_analytic_x eps S hS hfirst η u w z hw hz) x hx).differentiableAt

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem continuedCorrection_first_boundary_x (eps : ℝ) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re) :
    AnalyticAt ℂ (fun x=> continuedCorrection S hS η u x w z) x := by
  apply AnalyticAt.mul _ ((unramifiedProduct_first_neighborhood_analytic_x (eps/2) S hfirst
    η u w z (by linarith) (by linarith)) x (by change max (101/200:ℝ) (1+eps/2-w.re)< x.re; exact max_lt (by linarith) (by linarith)))
  apply Finset.analyticAt_fun_prod
  intro P hP
  exact (ramifiedCorrection_first_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    w z (by linarith)) x (by change (1/2:ℝ)< x.re; linarith)

theorem continuedCorrection_first_boundary_w (eps : ℝ) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re) :
    AnalyticAt ℂ (fun w=> continuedCorrection S hS η u x w z) w := by
  apply AnalyticAt.mul _ ((unramifiedProduct_first_neighborhood_analytic_w (eps/2) S hfirst
    η u x z (by linarith) (by linarith)) w (by change max (-(3/200:ℝ)) (1+eps/2-x.re)< w.re; exact max_lt (by linarith) (by linarith)))
  apply Finset.analyticAt_fun_prod
  intro P hP
  exact ((ramifiedCorrection_first_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x z (by linarith) (by linarith)).differentiableOn.analyticOnNhd
      (isOpen_univ : IsOpen (Set.univ : Set ℂ))) w (Set.mem_univ w)

theorem continuedCorrection_first_boundary_z (eps : ℝ) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re) :
    AnalyticAt ℂ (fun z=> continuedCorrection S hS η u x w z) z := by
  apply AnalyticAt.mul _ ((unramifiedProduct_first_neighborhood_analytic_z (eps/2) S hfirst
    η u x w (by linarith) (by linarith) (by linarith)) z (by change (27/80:ℝ)< z.re; linarith))
  apply Finset.analyticAt_fun_prod
  intro P hP
  exact (ramifiedCorrection_first_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x w (by linarith)) z (by change (1/3:ℝ)< z.re; linarith)

theorem continuedHighSeries_first_boundary_w (eps : ℝ) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re) (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=> continuedHighSeries S hS η u x w z) w := by
  exact (((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _).mul
    (continuedCorrection_first_boundary_w eps heps S hS hfirst η u x w z hx hw hz hxw).differentiableAt

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open Eisenstein ProbeEulerFinsupp ProbePhysical
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def excludedRowArray (S : Finset Id) (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (a : HighIdeal) : ℂ :=
  markedIdealHighSummand S 1 η u x w z a.1.1 a.1.2 a.2.1 a.2.2

lemma excludedRowArray_one (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ) : excludedRowArray S η u x w z 1=1 := by
  simp only [excludedRowArray,Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
    highIdealMask_unmarked_one S hS,bareIdealHighSummand_row_one,one_mul]

lemma excludedRowArray_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (a b : HighIdeal)
    (hc : IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2)) :
    excludedRowArray S η u x w z (a*b)=excludedRowArray S η u x w z a*excludedRowArray S η u x w z b := by
  simp only [excludedRowArray,Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
    highIdealMask_unmarked_mul S hS a b,
    bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc]
  ring

def excludedRowPrimeTerm (S : Finset Id) (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : HeckeIdealSeries.PrimeIdeal) (b : HighValuation) : ℂ :=
  excludedRowArray S η u x w z ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))

lemma excludedRowArray_prod (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (v : HeckeIdealSeries.PrimeIdeal→₀HighValuation) :
    excludedRowArray S η u x w z (highIdeals v)=v.prod (excludedRowPrimeTerm S η u x w z) :=
  highArray_val_prod _ (excludedRowArray_one S hS η u x w z) (excludedRowArray_mul S hS η u x w z) v

lemma markedRowArray_val (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset HeckeIdealSeries.PrimeIdeal)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (v : HeckeIdealSeries.PrimeIdeal→₀HighValuation) :
    markedIdealHighSummand S (∏P∈T,P.val) η u x w z
      (highIdeals v).1.1 (highIdeals v).1.2 (highIdeals v).2.1 (highIdeals v).2.2=
        markedArray T completedValuationMark (excludedRowPrimeTerm S η u x w z) v := by
  rw [markedIdealHighSummand_mark,markedArray,completedValuationMark_product]
  change _*excludedRowArray S η u x w z (highIdeals v)=_
  rw [excludedRowArray_prod S hS]

theorem markedRowSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    HasProd (fun P : HeckeIdealSeries.PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedRowPrimeTerm S η u x w z) P b)
      (markedIdealHighSeries S (∏P∈T,P.val) η u x w z) := by
  have h0 (P : HeckeIdealSeries.PrimeIdeal) : excludedRowPrimeTerm S η u x w z P 0=1 := by
    simp only [excludedRowPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero]
    exact excludedRowArray_one S hS η u x w z
  have hs := (markedIdealHighSummand_summable S 1 η u x w z hx hw hz).norm.comp_injective highIdeals_injective
  change Summable (fun v=>‖excludedRowArray S η u x w z (highIdeals v)‖) at hs
  simp only [excludedRowArray_prod S hS] at hs
  have he := marked_hasProd T completedValuationMark (excludedRowPrimeTerm S η u x w z) h0 hs
    (fun P _ b=> completedValuationMark_norm P b)
  have hsum : (∑'v : HeckeIdealSeries.PrimeIdeal→₀HighValuation,
      markedArray T completedValuationMark (excludedRowPrimeTerm S η u x w z) v)=
      markedIdealHighSeries S (∏P∈T,P.val) η u x w z := by
    simp only [←markedRowArray_val S hS T η u x w z]
    unfold markedIdealHighSeries
    apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
      markedIdealHighSummand S (∏P∈T,P.val) η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
    intro a ha
    have hh : bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hc := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hc.2.1.1⟩,⟨a.1.2,hc.2.2.1.1⟩),(⟨a.2.1,hc.2.2.2.1.1⟩,⟨a.2.2,hc.2.2.2.2.1⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [hsum] using he

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open ProbePhysical Eisenstein CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ProbeEuler ProbeRow 
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def idealRowMarkedLocalFactor (η : HeckeFamily.Character) (u : O) (P : HeckeIdealSeries.PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∑e : Fin 2,∑'l,∑'k,∑'m,
    completedValuationMark P ((e.val,l),(k,m))*rowHighPrimeTerm η u x w z P ((e.val,l),(k,m))

lemma markedRowPrimeTerm_summable_norm (η : HeckeFamily.Character) (u : O) (P : HeckeIdealSeries.PrimeIdeal) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    Summable (fun b : HighValuation=>‖completedValuationMark P b*rowHighPrimeTerm η u x w z P b‖) := by
  apply Summable.of_nonneg_of_le (fun _=> norm_nonneg _) _ (rowHighPrimeTerm_summable_norm η u x w z hx hw hz P)
  intro b
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (completedValuationMark_norm P b)

lemma markedRowPrimeTerm_tsum (η : HeckeFamily.Character) (u : O) (P : HeckeIdealSeries.PrimeIdeal) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    (∑'b : HighValuation,completedValuationMark P b*rowHighPrimeTerm η u x w z P b)=
      idealRowMarkedLocalFactor η u P x w z := by
  have hs := (markedRowPrimeTerm_summable_norm η u P x w z hx hw hz).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) : (∑'b : ℕ×ℕ,completedValuationMark P ((e,l),b)*rowHighPrimeTerm η u x w z P ((e,l),b))=
      ∑'k,∑'m,completedValuationMark P ((e,l),(k,m))*rowHighPrimeTerm η u x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=> by
    have hh : 2≤ e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [rowHighPrimeTerm_zero_of_two_le η u x w z P e _ _ _ hh,mul_zero,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

lemma selectedRowLocal_outside (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset HeckeIdealSeries.PrimeIdeal)
    (η : HeckeFamily.Character) (u : O) (P : HeckeIdealSeries.PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    (∑'b : HighValuation,ProbeEulerFinsupp.markedLocal T completedValuationMark
      (excludedRowPrimeTerm S η u x w z) P b)=
      if P∈T then idealRowMarkedLocalFactor η u P x w z else idealRowHighLocalFactor η u P.val x w z := by
  have he (b : HighValuation) : excludedRowPrimeTerm S η u x w z P b=rowHighPrimeTerm η u x w z P b := by
    simp only [excludedRowPrimeTerm,excludedRowArray,markedIdealHighSummand,
      highIdealMask_prime_outside S hS P hP,one_mul,rowHighPrimeTerm]
  simp only [ProbeEulerFinsupp.markedLocal,he]
  by_cases hPT : P∈T
  · simp only [if_pos hPT]
    exact markedRowPrimeTerm_tsum η u P x w z hx hw hz
  · simp only [if_neg hPT,one_mul]
    exact rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz P

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp
local notation "O" => Eisenstein.O

/-- Remove the marked primes from the infinite Euler product. -/
def markExclusions (S : Finset (Ideal O)) (T : Finset HeckeIdealSeries.PrimeIdeal) : Finset (Ideal O) :=
  S∪T.image Subtype.val

theorem markExclusions_prime (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset HeckeIdealSeries.PrimeIdeal) : ∀P∈markExclusions S T,Prime P := by
  intro P hP
  rcases Finset.mem_union.mp hP with hP|hP
  · exact hS P hP
  · obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    exact Q.property

@[simp] theorem mem_markExclusions (S : Finset (Ideal O)) (T : Finset HeckeIdealSeries.PrimeIdeal) (P : HeckeIdealSeries.PrimeIdeal) :
    P.val∈markExclusions S T ↔ P.val∈S ∨ P∈T := by
  simp only [markExclusions,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro (h|⟨Q,hQ,he⟩)
    · exact Or.inl h
    · exact Or.inr ((Subtype.ext he : Q=P) ▸ hQ)
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr ⟨P,h,rfl⟩

theorem markedRowSeries_eq_finite_replacement (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : O) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u x w z=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,idealRowMarkedLocalFactor η u P x w z := by
  let R := fun P : HeckeIdealSeries.PrimeIdeal=> if P∈T then idealRowMarkedLocalFactor η u P x w z else 1
  have hR : HasProd R (∏P∈T,idealRowMarkedLocalFactor η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional HeckeIdealSeries.PrimeIdeal) (fun P hP=> if_neg hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := (excludedIdealHighSeries_row_hasProd (markExclusions S T)
    (markExclusions_prime S hS T) η u x w z hx hw hz).mul hR
  have heq (P : HeckeIdealSeries.PrimeIdeal) :
      (∑'b : HighValuation,markedIdealHighSummand (markExclusions S T) 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*R P=
      ∑'b : HighValuation,markedLocal T completedValuationMark
        (excludedRowPrimeTerm S η u x w z) P b := by
    rw [excludedRowHighLocalFactor _ (markExclusions_prime S hS T) η u x w z hx hw hz]
    by_cases hP : P∈T
    · rw [if_pos ((mem_markExclusions S T P).mpr (Or.inr hP)),
        selectedRowLocal_outside S hS T η u P (hT P hP) x w z hx hw hz,if_pos hP]
      simp only [R,if_pos hP,one_mul]
    · simp only [R,if_neg hP,mul_one,markedLocal,one_mul]
      change _=∑'b : HighValuation,markedIdealHighSummand S 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)
      rw [excludedRowHighLocalFactor S hS η u x w z hx hw hz]
      simp only [mem_markExclusions,hP,or_false]
  have he' : HasProd (fun P : HeckeIdealSeries.PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedRowPrimeTerm S η u x w z) P b)
      (markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,idealRowMarkedLocalFactor η u P x w z) := by
    convert he using 1
    funext P
    exact (heq P).symm
  exact (markedRowSeries_hasProd S hS T η u x w z hx hw hz).unique he'

theorem markedRowSeries_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    let S' := markExclusions S T
    let hS' := markExclusions_prime S hS T
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z=
      (LFunction (fixedSourcePrincipal S' hS') (6*z)*LFunction (rowCharacter S' hS' u) w/
        LFunction ((targetRow η u).excludePrimes S' hS') x*globalCorrection S' η u x w z)*
        ∏P∈T,idealRowMarkedLocalFactor η u.val P x w z := by
  dsimp only
  rw [markedRowSeries_eq_finite_replacement S hS T hT η u.val x w z hx hw hz,
    high_L_factorization (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz]

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp CanonicalRowCompletion
local notation "O" => Eisenstein.O

def localNormalization (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (x w z : ℂ) : ℂ :=
  (1-fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*fullIdealWeight x P.val)

def markedLocalCorrection (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowMarkedLocalFactor η u.val P x w z*localNormalization η u P x w z

theorem localCorrection_eq_normalization (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (x w z : ℂ) :
    localCorrection η u P x w z=idealRowHighLocalFactor η u.val P.val x w z*
      localNormalization η u P x w z := by
  unfold localCorrection localNormalization
  ring

lemma lift_outside_hasProd (S : Finset (Ideal O)) (f : HeckeIdealSeries.PrimeIdeal→ℂ) (a : ℂ)
    (h : HasProd (fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S}=> f P.val) a) :
    HasProd (fun P : HeckeIdealSeries.PrimeIdeal=> if P.val∈S then 1 else f P) a := by
  have hh := (hasProd_subtype_iff_mulIndicator (s:={P : HeckeIdealSeries.PrimeIdeal | P.val∉S}) (f:=f)).mp h
  convert hh using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_setOf_eq]
  split_ifs <;> simp_all

theorem localNormalization_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 1< x.re) (hw : 1< w.re) (hz : 1<(6*z).re) :
    HasProd (fun P : HeckeIdealSeries.PrimeIdeal=> if P.val∈S then 1 else localNormalization η u P x w z)
      ((LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
        (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x) := by
  apply lift_outside_hasProd
  have hZ : HasProd (fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} =>
      ((1-fullIdealWeight (6*z) P.val.val)⁻¹)⁻¹)
      (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹ := by
    have h := fixedSourcePrincipal_hasProd S hS (6*z) hz
    rw [HasProd] at h ⊢
    simpa only [Finset.prod_inv_distrib] using
      h.inv₀ (LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz)
  have hW : HasProd (fun P : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S} =>
      ((1-idealRowHom u.val P.val.val*fullIdealWeight w P.val.val)⁻¹)⁻¹)
      (LFunction (rowCharacter S hS u) w)⁻¹ := by
    have h := rowCharacter_hasProd S hS hbad u w hw
    rw [HasProd] at h ⊢
    simpa only [Finset.prod_inv_distrib] using
      h.inv₀ (LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw)
  have hD := targetRow_hasProd S hS hbad η u x hx
  simpa only [localNormalization,inv_inv,div_eq_mul_inv] using (hZ.mul hW).mul hD

theorem markedRowSeries_normalized (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z*
      ((LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
        (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x)=
      globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,markedLocalCorrection η u P x w z := by
  have hx1 : 1< x.re := by linarith
  have hw1 : 1< w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hleft := (markedRowSeries_hasProd S hS T η u.val x w z hx hw hz).mul
    (localNormalization_hasProd S hS hbad η u x w z hx1 hw1 hz1)
  have hbase := lift_outside_hasProd (markExclusions S T) (fun P=> localCorrection η u P x w z) _
    (globalCorrection_multipliable (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz).hasProd
  let R := fun P : HeckeIdealSeries.PrimeIdeal=> if P∈T then markedLocalCorrection η u P x w z else 1
  have hR : HasProd R (∏P∈T,markedLocalCorrection η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional HeckeIdealSeries.PrimeIdeal) (fun P hP=> if_neg hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have heq (P : HeckeIdealSeries.PrimeIdeal) :
      (∑'b : HighValuation,markedLocal T completedValuationMark (excludedRowPrimeTerm S η u.val x w z) P b)*
        (if P.val∈S then 1 else localNormalization η u P x w z)=
      (if P.val∈markExclusions S T then 1 else localCorrection η u P x w z)*R P := by
    by_cases hP : P∈T
    · rw [selectedRowLocal_outside S hS T η u.val P (hT P hP) x w z hx hw hz,
        if_pos hP,if_neg (hT P hP),if_pos ((mem_markExclusions S T P).mpr (Or.inr hP))]
      simp only [R,if_pos hP,one_mul,markedLocalCorrection]
    · simp only [markedLocal,if_neg hP,one_mul,R,mul_one]
      change (∑'b : HighValuation,markedIdealHighSummand S 1 η u.val x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*_=_
      rw [excludedRowHighLocalFactor S hS η u.val x w z hx hw hz]
      simp only [mem_markExclusions,hP,or_false]
      by_cases hPS : P.val∈S
      · simp only [if_pos hPS,one_mul]
      · simp only [if_neg hPS,localCorrection_eq_normalization]
  have hright := hbase.mul hR
  apply hleft.unique
  convert hright using 1
  · funext P
    exact heq P
  · rfl

theorem markedRowSeries_original_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z=
      (LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (rowCharacter S hS u) w/
        LFunction ((targetRow η u).excludePrimes S hS) x)*
      (globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,markedLocalCorrection η u P x w z) := by
  have hx1 : 1< x.re := by linarith
  have hw1 : 1< w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hZ := LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := LFunction_ne_zero_of_one_lt_re ((targetRow η u).excludePrimes S hS) hx1
  rw [←markedRowSeries_normalized S hS hbad T hT η u x w z hx hw hz]
  field_simp

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp
local notation "O" => Eisenstein.O

theorem markedRowSeries_subset_replacement (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T J : Finset HeckeIdealSeries.PrimeIdeal) (hJ : J⊆T) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : O) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    markedIdealHighSeries S (∏P∈T\J,P.val) η u x w z=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        (∏P∈T\J,idealRowMarkedLocalFactor η u P x w z)*
        (∏P∈J,idealRowHighLocalFactor η u P.val x w z) := by
  let A := fun P : HeckeIdealSeries.PrimeIdeal=> if P∈T\J then idealRowMarkedLocalFactor η u P x w z else 1
  let B := fun P : HeckeIdealSeries.PrimeIdeal=> if P∈J then idealRowHighLocalFactor η u P.val x w z else 1
  have hA : HasProd A (∏P∈T\J,idealRowMarkedLocalFactor η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T\J) (f:=A)
      (L:=SummationFilter.unconditional HeckeIdealSeries.PrimeIdeal) (fun P hP=> if_neg hP)
    simpa only [A,Finset.prod_ite_mem,Finset.inter_self] using hh
  have hB : HasProd B (∏P∈J,idealRowHighLocalFactor η u P.val x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=J) (f:=B)
      (L:=SummationFilter.unconditional HeckeIdealSeries.PrimeIdeal) (fun P hP=> if_neg hP)
    simpa only [B,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := ((excludedIdealHighSeries_row_hasProd (markExclusions S T)
    (markExclusions_prime S hS T) η u x w z hx hw hz).mul hA).mul hB
  have heq (P : HeckeIdealSeries.PrimeIdeal) :
      ((∑'b : HighValuation,markedIdealHighSummand (markExclusions S T) 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*A P)*B P=
      ∑'b : HighValuation,markedLocal (T\J) completedValuationMark
        (excludedRowPrimeTerm S η u x w z) P b := by
    rw [excludedRowHighLocalFactor _ (markExclusions_prime S hS T) η u x w z hx hw hz]
    by_cases hPJ : P∈J
    · have hPT := hJ hPJ
      have hPA : P∉T\J := by simp only [Finset.mem_sdiff]; tauto
      rw [if_pos ((mem_markExclusions S T P).mpr (Or.inr hPT)),
        selectedRowLocal_outside S hS (T\J) η u P (hT P hPT) x w z hx hw hz,if_neg hPA]
      simp only [A,B,if_neg hPA,if_pos hPJ,one_mul]
    · by_cases hPT : P∈T
      · have hPA : P∈T\J := Finset.mem_sdiff.mpr ⟨hPT,hPJ⟩
        rw [if_pos ((mem_markExclusions S T P).mpr (Or.inr hPT)),
          selectedRowLocal_outside S hS (T\J) η u P (hT P hPT) x w z hx hw hz,if_pos hPA]
        simp only [A,B,if_pos hPA,if_neg hPJ,one_mul,mul_one]
      · have hPA : P∉T\J := fun h=> hPT (Finset.mem_sdiff.mp h).1
        simp only [A,B,if_neg hPA,if_neg hPJ,mul_one,markedLocal,one_mul]
        change _=∑'b : HighValuation,markedIdealHighSummand S 1 η u x w z
          (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)
        rw [excludedRowHighLocalFactor S hS η u x w z hx hw hz]
        simp only [mem_markExclusions,hPT,or_false]
  apply (markedRowSeries_hasProd S hS (T\J) η u x w z hx hw hz).unique
  convert he using 1
  funext P
  exact (heq P).symm

def spectralCompensatedRow (S : Finset (Ideal O)) (T : Finset HeckeIdealSeries.PrimeIdeal)
    (η : Character) (u : O) (x w z : ℂ) (B q : HeckeIdealSeries.PrimeIdeal→ℂ) : ℂ :=
  ∑J∈T.powerset,(-1:ℂ)^J.card*(∏P∈J,q P)*(∏P∈T\J,B P)*
    markedIdealHighSeries S (∏P∈T\J,P.val) η u x w z

theorem spectralCompensatedRow_eq_product (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : O)
    (x w z : ℂ) (B q : HeckeIdealSeries.PrimeIdeal→ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    spectralCompensatedRow S T η u x w z B q=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,(B P*idealRowMarkedLocalFactor η u P x w z-
          q P*idealRowHighLocalFactor η u P.val x w z) := by
  rw [spectralCompensatedRow,Finset.prod_sub,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [markedRowSeries_subset_replacement S hS T J (Finset.mem_powerset.mp hJ) hT η u x w z hx hw hz]
  simp only [Finset.prod_mul_distrib]
  ring

theorem indexedCompensatedHigh_eq_spectral {K : ℕ} (η : Character) (S : Finset (Ideal O))
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P)
    (hs : ∀i,CanonicalQuadraticSieve.Supported (P i).val) (u : O) (x w z : ℂ) :
    indexedCompensatedHigh η S (fun i=> primaryIdealGenerator (P i).val) u x w z=
      spectralCompensatedRow S (Finset.univ.image P) η u x w z
        (fun Q=> star (idealCoeff η Q.val)*(Q.val.absNorm:ℂ)^x)
        (fun Q=>(Q.val.absNorm:ℂ)^(-w)) := by
  unfold indexedCompensatedHigh spectralCompensatedRow
  rw [Finset.powerset_image,Finset.sum_image (Finset.image_injective hP).injOn]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.card_image_of_injective J hP,←Finset.image_sdiff _ _ hP]
  simp only [Finset.prod_image hP.injOn]
  have hnorm (i : Fin K) : (elementNorm (primaryIdealGenerator (P i).val):ℂ)=
      ((P i).val.absNorm:ℂ) := by
    rw [primaryTuple_norm (P i) (hs i)]
    norm_cast
  have hc (i : Fin K) : elementCoeff η (primaryIdealGenerator (P i).val)=
      idealCoeff η (P i).val := targetMonoid_primaryIdealGenerator η (P i).val (hs i)
  simp only [tupleIndexedCoefficient,hnorm,hc,span_tupleProduct,
    CenteredMomentSourceRow.primary_span_supported _ (hs _)]

end ProbeHighRowFamily

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
