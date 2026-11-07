/-
Cubic denominator reindexing adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicUnramifiedZetaSeries

/-!
# Cube denominators and the ramified geometric ratio

Every nonzero ideal factors uniquely into a ramified prime power and an
unramified ideal. Cubing removes the threefold unit ambiguity, leaving
a sign. Thus the nonzero cube denominators divisible by three are indexed
by a sign, a positive ramified exponent, and a primary unramified ideal.
Their constant terms factor as a geometric weight times an ideal totient.
-/
noncomputable section
open MeasureTheory Set Filter UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

private instance cubicCubeColumnCyclotomic : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance cubicCubeColumnPID : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

/-- A generator of each ideal, used only for ideal reindexing. -/
def cubicIdealGenerator (I : Ideal O) : O := Submodule.IsPrincipal.generator I

lemma span_cubicIdealGenerator (I : Ideal O) : Ideal.span {cubicIdealGenerator I} = I :=
  Submodule.IsPrincipal.span_singleton_generator I

lemma cubicIdealGenerator_injective : Function.Injective cubicIdealGenerator := by
  intro I J h
  rw [← span_cubicIdealGenerator I, ← span_cubicIdealGenerator J, h]

lemma cubicIdealGenerator_ne_zero (I : Ideal O) (hI : I ≠ 0) : cubicIdealGenerator I ≠ 0 := by
  intro hz
  have h := span_cubicIdealGenerator I
  rw [hz, Ideal.span_singleton_zero] at h
  exact hI h.symm

def ramifiedIdeal : Ideal O := Ideal.span {lambda}

lemma ramifiedIdeal_prime : Prime ramifiedIdeal := by
  exact Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr residue_lambda_prime.ne_zero)
    ((Ideal.span_singleton_prime residue_lambda_prime.ne_zero).mpr residue_lambda_prime)

lemma goodIdeal_iff_not_ramified (I : Ideal O) :
    primaryIdealGenerator I ≠ 0 ↔ ¬ ramifiedIdeal ∣ I := by
  rw [← span_cubicIdealGenerator I,
    primaryIdealGenerator_span_ne_zero_iff,
    Ideal.dvd_iff_le,ramifiedIdeal,Ideal.span_singleton_le_span_singleton]

lemma ramifiedIdeal_absNorm : Ideal.absNorm ramifiedIdeal=3 := absNorm_span_lambda

lemma prime_power_remainder_multiplicity {R : Type*} [CommMonoidWithZero R]
    [IsCancelMulZero R] {p a : R} (hp : Prime p) (ha : ¬ p ∣ a) (n : ℕ) :
    multiplicity p (p^n*a)=n := by
  apply multiplicity_eq_of_dvd_of_not_dvd ⟨a,rfl⟩
  intro hd
  rw [pow_succ] at hd
  exact ha ((mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero)).mp hd)

abbrev NonzeroIdeal := {I : Ideal O // I ≠ 0}

def lambdaFactorMap (p : ℕ × GoodIdeal) : NonzeroIdeal :=
  ⟨ramifiedIdeal^p.1*p.2.1,mul_ne_zero (pow_ne_zero _ ramifiedIdeal_prime.ne_zero)
    (primaryIdealGenerator_ne_zero_ideal _ p.2.2)⟩

lemma lambdaFactorMap_bijective : Function.Bijective lambdaFactorMap := by
  constructor
  · rintro ⟨n,I⟩ ⟨m,J⟩ heq
    have hh : ramifiedIdeal^n*I.1=ramifiedIdeal^m*J.1 := congrArg Subtype.val heq
    have hn : n=m := by
      have hm := congrArg (multiplicity ramifiedIdeal) hh
      rw [prime_power_remainder_multiplicity ramifiedIdeal_prime
        ((goodIdeal_iff_not_ramified I.1).mp I.2),
        prime_power_remainder_multiplicity ramifiedIdeal_prime
        ((goodIdeal_iff_not_ramified J.1).mp J.2)] at hm
      exact hm
    subst m
    have hIJ : I=J := Subtype.ext (mul_left_cancel₀ (pow_ne_zero n ramifiedIdeal_prime.ne_zero) hh)
    subst J
    rfl
  · intro I
    obtain ⟨J,hJ,hnot⟩ := (FiniteMultiplicity.of_prime_left ramifiedIdeal_prime I.2).exists_eq_pow_mul_and_not_dvd
    refine ⟨(multiplicity ramifiedIdeal I.1,⟨J,(goodIdeal_iff_not_ramified J).mpr hnot⟩), ?_⟩
    exact Subtype.ext hJ.symm

def lambdaFactorEquiv : ℕ × GoodIdeal ≃ NonzeroIdeal :=
  Equiv.ofBijective lambdaFactorMap lambdaFactorMap_bijective

lemma ideal_pow_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun I : Ideal O => I^n) := by
  intro I J h
  dsimp only at h
  apply le_antisymm
  · apply Ideal.dvd_iff_le.mp
    apply (pow_dvd_pow_iff_dvd hn).mp
    rw [h]
  · apply Ideal.dvd_iff_le.mp
    apply (pow_dvd_pow_iff_dvd hn).mp
    rw [h]

lemma lambdaFactor_generator_span (n : ℕ) (I : GoodIdeal) :
    Ideal.span {lambda^n*primaryIdealGenerator I.1}=ramifiedIdeal^n*I.1 := by
  rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
    (primaryIdealGenerator_spec I.1 I.2).1]
  rfl

lemma three_dvd_lambda_sq : (3:O) ∣ lambda^2 := by
  have h := three_dvd_primary_sub_one (lambda^2+1) (show lambda^2 ∣ lambda^2+1-1 by simp)
  simpa only [add_sub_cancel_right] using h

lemma unit_cube_eq_sign (u : Oˣ) : (u:O)^3=1 ∨ (u:O)^3= -1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η:O)=omega := rfl
  have hlist : u ∈ ([1,-1,η,-η,η^2,-η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h | h | h | h | h | h
  · left; simp [h]
  · right; norm_num [h]
  · left; simpa only [h,hη] using omega_primitive.pow_eq_one
  · right
    rw [h,Units.val_neg,hη]
    have hh := omega_primitive.pow_eq_one
    linear_combination -hh
  · left
    rw [h,Units.val_pow_eq_pow_val,hη,show (omega^2)^3=(omega^3)^2 by ring,omega_primitive.pow_eq_one]
    simp
  · right
    rw [h,Units.val_neg,Units.val_pow_eq_pow_val,hη]
    simp only [neg_pow,show (-1:O)^3= -1 by norm_num,
      show (omega^2)^3=(omega^3)^2 by ring,omega_primitive.pow_eq_one,one_pow,mul_one]

def cubeSign : Bool → O
  | false => 1
  | true => -1

lemma cubeSign_isUnit (b : Bool) : IsUnit (cubeSign b) := by
  cases b <;> simp [cubeSign]

lemma cubeSign_cube (b : Bool) : (cubeSign b)^3=cubeSign b := by
  cases b <;> norm_num [cubeSign]

lemma cubeSign_injective : Function.Injective cubeSign := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals norm_num [cubeSign] at h

def cubeBase (n : ℕ) (I : GoodIdeal) : O := lambda^(n+1)*primaryIdealGenerator I.1

def cubeColumn (b : Bool) (n : ℕ) (I : GoodIdeal) : O := cubeSign b*(cubeBase n I)^3

lemma cubeBase_ne_zero (n : ℕ) (I : GoodIdeal) : cubeBase n I ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ residue_lambda_prime.ne_zero) I.2

lemma cubeColumn_ne_zero (b : Bool) (n : ℕ) (I : GoodIdeal) : cubeColumn b n I ≠ 0 :=
  mul_ne_zero (cubeSign_isUnit b).ne_zero (pow_ne_zero 3 (cubeBase_ne_zero n I))

lemma cubeColumn_cube (b : Bool) (n : ℕ) (I : GoodIdeal) :
    cubeColumn b n I=(cubeSign b*cubeBase n I)^3 := by
  rw [mul_pow,cubeSign_cube]
  rfl

lemma cubeColumn_level (b : Bool) (n : ℕ) (I : GoodIdeal) : (3:O) ∣ cubeColumn b n I := by
  have h3 : (3:O) ∣ lambda^(3*(n+1)) := three_dvd_lambda_sq.trans (pow_dvd_pow lambda (by omega))
  have heq : cubeColumn b n I=cubeSign b*(lambda^(3*(n+1))*(primaryIdealGenerator I.1)^3) := by
    simp only [cubeColumn,cubeBase,mul_pow,← pow_mul]
    congr 2
    ring
  rw [heq]
  exact (h3.mul_right _).mul_left _

lemma cubeColumn_span (b : Bool) (n : ℕ) (I : GoodIdeal) :
    Ideal.span {cubeColumn b n I}=(ramifiedIdeal^(n+1)*I.1)^3 := by
  rw [cubeColumn,Ideal.span_singleton_mul_left_unit (cubeSign_isUnit b),
    ← Ideal.span_singleton_pow]
  change (Ideal.span {lambda^(n+1)*primaryIdealGenerator I.1})^3=_
  rw [lambdaFactor_generator_span]

abbrev CubeLower := {c : LevelLower // c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3}

def cubeColumnMap (p : Bool × ℕ × GoodIdeal) : CubeLower :=
  ⟨⟨cubeColumn p.1 p.2.1 p.2.2,cubeColumn_level p.1 p.2.1 p.2.2⟩,
    cubeColumn_ne_zero p.1 p.2.1 p.2.2,⟨cubeSign p.1*cubeBase p.2.1 p.2.2,
      cubeColumn_cube p.1 p.2.1 p.2.2⟩⟩

lemma cubeColumnMap_injective : Function.Injective cubeColumnMap := by
  rintro ⟨b,n,I⟩ ⟨d,m,J⟩ h
  have hc : cubeColumn b n I=cubeColumn d m J := congrArg (fun c : CubeLower => c.1.1) h
  have hs := congrArg (fun a : O => Ideal.span {a}) hc
  rw [cubeColumn_span,cubeColumn_span] at hs
  have hr := ideal_pow_injective (by decide : (3:ℕ) ≠ 0) hs
  have hp : lambdaFactorMap (n+1,I)=lambdaFactorMap (m+1,J) := Subtype.ext hr
  have he := lambdaFactorMap_bijective.1 hp
  have hnm : n=m := Nat.succ.inj (congrArg Prod.fst he)
  have hIJ : I=J := congrArg Prod.snd he
  subst m; subst J
  have hbd : b=d := cubeSign_injective (mul_right_cancel₀
    (pow_ne_zero 3 (cubeBase_ne_zero n I)) hc)
  subst d
  rfl

lemma cubeColumnMap_surjective : Function.Surjective cubeColumnMap := by
  intro c
  obtain ⟨a,ha⟩ := c.2.2
  have ha0 : a ≠ 0 := by intro h; rw [h,zero_pow (by decide)] at ha; exact c.2.1 ha
  let A : NonzeroIdeal := ⟨Ideal.span {a},Ideal.span_singleton_eq_bot.not.mpr ha0⟩
  obtain ⟨⟨k,I⟩,hAI⟩ := lambdaFactorMap_bijective.2 A
  have hfact : ramifiedIdeal^k*I.1=Ideal.span {a} := congrArg Subtype.val hAI
  have hla : lambda ∣ a := by
    apply residue_lambda_prime.dvd_of_dvd_pow
    have hlam3 : lambda ∣ (3:O) :=
      (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
    rw [← ha]
    exact hlam3.trans c.1.2
  have hk : k ≠ 0 := by
    intro hk
    have hIeq : I.1=Ideal.span {a} := by simpa only [hk,pow_zero,one_mul] using hfact
    apply (goodIdeal_iff_not_ramified I.1).mp I.2
    rw [hIeq,Ideal.dvd_iff_le,ramifiedIdeal,Ideal.span_singleton_le_span_singleton]
    exact hla
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hspan : Ideal.span {cubeBase n I}=Ideal.span {a} :=
    (lambdaFactor_generator_span (n+1) I).trans hfact
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  rcases unit_cube_eq_sign u with hu1 | hum1
  · refine ⟨(false,n,I),Subtype.ext (Subtype.ext ?_)⟩
    change cubeColumn false n I=c.1.1
    rw [ha,← hu,mul_pow,hu1,mul_one]
    simp only [cubeColumn,cubeSign,one_mul]
  · refine ⟨(true,n,I),Subtype.ext (Subtype.ext ?_)⟩
    change cubeColumn true n I=c.1.1
    rw [ha,← hu,mul_pow,hum1]
    simp only [cubeColumn,cubeSign]
    ring

def cubeColumnEquiv : Bool × ℕ × GoodIdeal ≃ CubeLower :=
  Equiv.ofBijective cubeColumnMap ⟨cubeColumnMap_injective,cubeColumnMap_surjective⟩

lemma cubeColumn_expanded (b : Bool) (n : ℕ) (I : GoodIdeal) :
    cubeColumn b n I=lambda^(3*(n+1))*(cubeSign b*primaryIdealGenerator I.1)^3 := by
  simp only [cubeColumn,cubeBase,mul_pow,cubeSign_cube,← pow_mul]
  rw [Nat.mul_comm (n+1) 3]
  ring

lemma cubeColumn_arithmetic_sum (b : Bool) (n : ℕ) (I : GoodIdeal) :
    arithmeticResidueSum 0 (cubeColumn b n I)=
      (3^(3*(n+1))*Ideal.absNorm I.1^2*idealTotient I.1:ℕ) := by
  have ha : cubeSign b*cubeBase n I ≠ 0 :=
    mul_ne_zero (cubeSign_isUnit b).ne_zero (cubeBase_ne_zero n I)
  have hA := arithmeticResidueSum_cube _ ha
  rw [← cubeColumn_cube] at hA
  rw [hA,cubeColumn_expanded]
  have hc : IsCoprime (cubeSign b*primaryIdealGenerator I.1) (3:O) :=
    (isCoprime_mul_unit_left_left (cubeSign_isUnit b) _ _).mpr
      (primary_coprime_three _ (primaryIdealGenerator_spec I.1 I.2).2)
  have hs : Ideal.span {cubeSign b*primaryIdealGenerator I.1}=I.1 := by
    rw [Ideal.span_singleton_mul_left_unit (cubeSign_isUnit b),(primaryIdealGenerator_spec I.1 I.2).1]
  rw [card_admissible_cube_product (n+1) _ (mul_ne_zero (cubeSign_isUnit b).ne_zero I.2) hc,hs]

lemma cubeColumn_norm (b : Bool) (n : ℕ) (I : GoodIdeal) :
    Ideal.absNorm (Ideal.span {cubeColumn b n I})=3^(3*(n+1))*Ideal.absNorm I.1^3 := by
  rw [cubeColumn_span,map_pow,map_mul,map_pow,ramifiedIdeal_absNorm,mul_pow,← pow_mul]
  rw [Nat.mul_comm (n+1) 3]

def ramifiedRatio (s : ℂ) : ℂ := (3:ℂ)^(3-3*s)

lemma cube_norm_weight_algebra (s : ℂ) (n N : ℕ) (hN : N ≠ 0) :
    ((3^(3*(n+1))*N^3:ℕ):ℂ)^(-s) * (3^(3*(n+1))*N^2:ℕ) =
      ramifiedRatio s^(n+1) * (N:ℂ)^(-(3*s-2)) := by
  have hNc : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hsplit : ((3:ℂ)^(3*(n+1):ℕ)*(N:ℂ)^3)^(-s)=
      (3:ℂ)^((3*(n+1):ℕ)*(-s))*(N:ℂ)^(3*(-s)) := by
    have hm := Complex.natCast_mul_natCast_cpow (3^(3*(n+1))) (N^3) (-s)
    simp only [Nat.cast_pow,Nat.cast_ofNat] at hm
    rw [hm]
    have h3 : ((3:ℂ)^(3*(n+1):ℕ))^(-s)=(3:ℂ)^((3*(n+1):ℕ)*(-s)) := by
      simpa only [Nat.cast_ofNat] using
        (Complex.natCast_cpow_natCast_mul 3 (3*(n+1)) (-s)).symm
    have hN' : ((N:ℂ)^3)^(-s)=(N:ℂ)^(3*(-s)) := by
      simpa only [Nat.cast_ofNat] using (Complex.natCast_cpow_natCast_mul N 3 (-s)).symm
    rw [h3,hN']
  rw [hsplit]
  have hpoly : (3:ℂ)^(3*(n+1):ℕ)*(N:ℂ)^2 =
      (3:ℂ)^((3*(n+1):ℕ):ℂ)*(N:ℂ)^(2:ℂ) := by
    norm_num only [Complex.cpow_natCast,Complex.cpow_ofNat]
  rw [hpoly]
  calc
    _ = ((3:ℂ)^((3*(n+1):ℕ)*(-s))*(3:ℂ)^((3*(n+1):ℕ):ℂ))*
        ((N:ℂ)^(3*(-s))*(N:ℂ)^(2:ℂ)) := by ring
    _ = (3:ℂ)^((3*(n+1):ℕ)*(-s)+(3*(n+1):ℕ)) * (N:ℂ)^(3*(-s)+2) := by
      rw [← Complex.cpow_add _ _ (by norm_num : (3:ℂ) ≠ 0),← Complex.cpow_add _ _ hNc]
    _ = ramifiedRatio s^(n+1) * (N:ℂ)^(-(3*s-2)) := by
      unfold ramifiedRatio
      rw [← Complex.cpow_mul_nat]
      congr 1 <;> congr 1 <;> push_cast <;> ring

lemma cubeColumn_dirichletTerm (s : ℂ) (b : Bool) (n : ℕ) (I : GoodIdeal) :
    arithmeticDirichletTerm s 0 (cubeColumnMap (b,n,I)).1 =
      ramifiedRatio s^(n+1) * ((idealTotient I.1:ℂ)*unramifiedNormWeight (3*s-2) I.1) := by
  have hI : Ideal.absNorm I.1 ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (primaryIdealGenerator_ne_zero_ideal I.1 I.2)
  change (if cubeColumn b n I=0 then 0 else
    ((‖ringComplex (cubeColumn b n I)‖^2:ℝ):ℂ)^(-s)*
      arithmeticResidueSum 0 (cubeColumn b n I)) = _
  rw [if_neg (cubeColumn_ne_zero b n I),ringComplex_norm_sq_eq_absNorm_span,
    Complex.ofReal_natCast,cubeColumn_norm,cubeColumn_arithmetic_sum,
    unramifiedNormWeight_of_good _ _ I.2]
  calc
    _ = (((3^(3*(n+1))*Ideal.absNorm I.1^3:ℕ):ℂ)^(-s) *
        (3^(3*(n+1))*Ideal.absNorm I.1^2:ℕ))*(idealTotient I.1:ℂ) := by
      push_cast
      ring
    _ = (ramifiedRatio s^(n+1)*(Ideal.absNorm I.1:ℂ)^(-(3*s-2)))*(idealTotient I.1:ℂ) := by
      rw [cube_norm_weight_algebra s n (Ideal.absNorm I.1) hI]
    _ = _ := by ring


#print axioms lambdaFactorEquiv
#print axioms cubeColumnEquiv
#print axioms cubeColumn_dirichletTerm
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
