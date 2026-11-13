/-
Actual cusp fibers adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.GoodMaskRows
import GaloisForLFunctions.MetaplecticMobiusDescent.GaussSums.ReflectionFiberRows

/-!
# Actual cusp fibers

Completed arithmetic rows have the primary prime-family form required by reflection. Complete
active sets, nonresidual pool equivalences and inactive weights; residual parts of actual cusp
fibers (`ActualCuspFiber`).
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

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss UniqueFactorizationMonoid
open scoped BigOperators Classical

lemma good_odd_prime_two_not_mem (P : Ideal O) [P.IsMaximal]
    (hodd : ringChar (O⧸P)≠2) : (2:O)∉P := by
  intro ht
  apply Ring.two_ne_zero hodd
  simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr ht

lemma count_span_eq_zero_of_not_mem (P : Ideal O) (x : O) (hx : x∉P) :
    (normalizedFactors (Ideal.span {x})).count P=0 := by
  apply Multiset.count_eq_zero.mpr
  intro hm
  exact hx (Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hm) (Ideal.mem_span_singleton_self x))

lemma good_factor_count (P : Ideal O) [P.IsMaximal]
    (hgood : lambda∉P) (hodd : ringChar (O⧸P)≠2)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : quadraticSupported (Ideal.span {r})) :
    (normalizedFactors (Ideal.span {(u:O)*lambda^a*(2:O)^b*r})).count P=
      (normalizedFactors (Ideal.span {r})).count P := by
  have hl : (Ideal.span {lambda}:Ideal O)≠0 :=
    Ideal.span_singleton_eq_bot.not.mpr residue_lambda_prime.ne_zero
  have ht : (Ideal.span {(2:O)}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hcl := count_span_eq_zero_of_not_mem P lambda hgood
  have hct := count_span_eq_zero_of_not_mem P 2 (good_odd_prime_two_not_mem P hodd)
  rw [show (u:O)*lambda^a*(2:O)^b*r=(u:O)*(lambda^a*(2:O)^b*r) by ring,
    Ideal.span_singleton_mul_left_unit u.isUnit,
    ←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_pow,←Ideal.span_singleton_pow,
    normalizedFactors_mul (mul_ne_zero (pow_ne_zero _ hl) (pow_ne_zero _ ht))
      (primaryIdealGenerator_ne_zero_ideal _ hr.1),
    normalizedFactors_mul (pow_ne_zero _ hl) (pow_ne_zero _ ht)]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,hcl,hct,mul_zero,zero_add]

theorem goodMaskMovingIdeal_count (I F : Ideal O) (hI : I≠0) (hF : F≠0)
    (m f z : O) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (um : Oˣ) (am bm : ℕ) (g : O) (hg : quadraticSupported (Ideal.span {g}))
    (hm : m=(um:O)*lambda^am*(2:O)^bm*g)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : quadraticSupported (Ideal.span {r}))
    (hx : f^4*z=(u:O)*lambda^a*(2:O)^b*r)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda∉P) (hodd : ringChar (O⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P=
      6*(normalizedFactors (Ideal.span {m})).count P+
        4*(normalizedFactors F).count P+(normalizedFactors I).count P := by
  have hmc : (normalizedFactors (Ideal.span {m})).count P=(normalizedFactors (Ideal.span {g})).count P := by
    rw [hm]
    exact good_factor_count P hgood hodd um am bm g hg
  have hrc : (normalizedFactors (Ideal.span {r})).count P=
      4*(normalizedFactors F).count P+(normalizedFactors I).count P := by
    have hh := good_factor_count P hgood hodd u a b r hr
    rw [←hx,←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow,hf,hz,
      normalizedFactors_mul (pow_ne_zero 4 hF) hI] at hh
    simpa only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul] using hh.symm
  rw [goodMaskMovingIdeal,normalizedFactors_mul
    (pow_ne_zero 6 (primaryIdealGenerator_ne_zero_ideal _ hg.1)) (primaryIdealGenerator_ne_zero_ideal _ hr.1)]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,←hmc,hrc]
  omega

lemma squarefree_prime_count_indicator (F P : Ideal O) (hF : Squarefree F) (hP : Prime P) :
    (normalizedFactors F).count P=if P∣F then 1 else 0 := by
  have hle := Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hF.ne_zero).mp hF) P
  by_cases hPF : P∣F
  · rw [if_pos hPF]
    have hp := Multiset.count_pos.mpr
      ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hF.ne_zero).mpr ⟨hP,hPF⟩)
    omega
  · rw [if_neg hPF]
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact hPF ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hF.ne_zero).mp hm).2

theorem GoodMaskRowData.moving_count {m f z : O} (D : GoodMaskRowData m f z)
    (I F : Ideal O) (hI : I≠0) (hF : F≠0)
    (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda∉P) (hodd : ringChar (O⧸P)≠2) :
    (normalizedFactors D.movingIdeal).count P=6*(normalizedFactors (Ideal.span {m})).count P+
      4*(normalizedFactors F).count P+(normalizedFactors I).count P :=
  goodMaskMovingIdeal_count I F hI hF m f z hf hz
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorFactor P hgood hodd

/-- Sixth-power mask factors vanish modulo six; a squarefree fourth power contributes four. -/
theorem GoodMaskRowData.moving_exponent {m f z : O} (D : GoodMaskRowData m f z)
    (I F : Ideal O) (hI : I≠0) (hF : Squarefree F)
    (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda∉P) (hodd : ringChar (O⧸P)≠2) :
    (normalizedFactors D.movingIdeal).count P%6=completedLocalExponent I F P := by
  change (normalizedFactors (goodMaskMovingIdeal D.maskGood D.numeratorGood)).count P%6=_
  rw [goodMaskMovingIdeal_count I F hI hF.ne_zero m f z hf hz
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported D.numeratorFactor P hgood hodd,
    squarefree_prime_count_indicator F P hF (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance)]
  unfold completedLocalExponent
  omega

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss UniqueFactorizationMonoid
open scoped BigOperators Classical

lemma prime_dvd_iff_factor_count_pos (P A : Ideal O) (hP : Prime P) (hA : A≠0) :
    P∣A ↔ 0<(normalizedFactors A).count P := by
  simp only [Multiset.count_pos,UniqueFactorizationMonoid.mem_normalizedFactors_iff hA,hP,true_and]

namespace GoodMaskRowData
variable {m f z : O} (D : GoodMaskRowData m f z)

theorem moving_dvd_iff (I F : Ideal O) (hI : I≠0) (hF : F≠0) (hm : m≠0)
    (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda∉P) (hodd : ringChar (O⧸P)≠2) :
    P∣D.movingIdeal ↔ P∣I*(Ideal.span {m}*F) := by
  have hP : Prime P := Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have hmI : (Ideal.span {m}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hm
  rw [prime_dvd_iff_factor_count_pos P _ hP
      (primaryIdealGenerator_ne_zero_ideal _ D.movingSupported.1),
    prime_dvd_iff_factor_count_pos P _ hP (mul_ne_zero hI (mul_ne_zero hmI hF)),
    D.moving_count I F hI hF hf hz P hgood hodd,
    normalizedFactors_mul hI (mul_ne_zero hmI hF),normalizedFactors_mul hmI hF]
  simp only [Multiset.count_add]
  omega

theorem moving_primeSupport (I F : Ideal O) (hI : I≠0) (hF : F≠0) (hm : m≠0)
    (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I) :
    primeSupport D.movingIdeal=(primeSupport (I*(Ideal.span {m}*F))).filter
      (fun P => lambda∉P ∧ ringChar (O⧸P)≠2) := by
  have hmI : (Ideal.span {m}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hm
  have hprod := mul_ne_zero hI (mul_ne_zero hmI hF)
  have hd0 := primaryIdealGenerator_ne_zero_ideal _ D.movingSupported.1
  ext P
  simp only [primeSupport,Finset.mem_filter,Multiset.mem_toFinset]
  constructor
  · intro hP
    obtain ⟨hmax,hgood,hodd⟩ := supported_factors_good _ D.movingSupported P hP
    letI : P.IsMaximal := hmax
    have hp := prime_of_normalized_factor P hP
    have hd := ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hd0).mp hP).2
    exact ⟨(UniqueFactorizationMonoid.mem_normalizedFactors_iff hprod).mpr
      ⟨hp,(D.moving_dvd_iff I F hI hF hm hf hz P hgood hodd).mp hd⟩,hgood,hodd⟩
  · rintro ⟨hP,hgood,hodd⟩
    have hp := prime_of_normalized_factor P hP
    letI : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hd := ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hprod).mp hP).2
    exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hd0).mpr
      ⟨hp,(D.moving_dvd_iff I F hI hF hm hf hz P hgood hodd).mpr hd⟩

theorem moving_residual_exponent (I F : Ideal O) (hI : I≠0) (hF : Squarefree F)
    (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda∉P) (hodd : ringChar (O⧸P)≠2)
    (hP : P∈normalizedFactors (rowResidualPart I (Ideal.span {m}*F))) :
    (normalizedFactors D.movingIdeal).count P%6=1 := by
  have hr := rowResidualPart_prime_exponent I (Ideal.span {m}*F) P hP
  have hPF : ¬P∣F := fun hp => hr.2.2 (dvd_mul_of_dvd_right hp _)
  rw [D.moving_exponent I F hI hF hf hz P hgood hodd,completedLocalExponent,hr.2.1,if_neg hPF]

end GoodMaskRowData
end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss UniqueFactorizationMonoid
open scoped BigOperators Classical

def freePrimePool (lengthScale Q0:Ideal O) : Finset (Ideal O) :=
  (primeSupport lengthScale).filter (fun P=>¬Q0≤P)

lemma mem_freePrimePool (lengthScale Q0 P:Ideal O) :
    P∈freePrimePool lengthScale Q0 ↔ P∈primeSupport lengthScale ∧ ¬Q0≤P := by
  simp only [freePrimePool,Finset.mem_filter]

lemma residual_nonresidual_disjoint (I Q Q0:Ideal O) :
    Disjoint (primeSupport (rowResidualPart I Q)) (FreeReflection.pool I Q Q0) := by
  apply Finset.disjoint_left.mpr
  intro P hP ht
  exact FreeReflection.pool_nonresidual I Q Q0 ⟨P,ht⟩
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))

theorem freePrimePool_eq_residual_union (lengthScale I Q Q0:Ideal O)
    (hI:I≠0) (hQ:Q≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hcop:IsCoprime Q0 (rowResidualPart I Q))
    (hs:primeSupport lengthScale=
      (primeSupport (I*Q)).filter
        (fun P=>lambda∉P ∧ ringChar (O⧸P)≠2)) :
    freePrimePool lengthScale Q0=
      primeSupport (rowResidualPart I Q) ∪ FreeReflection.pool I Q Q0 := by
  have hk:=rowResidualPart_admissible I Q hbad
  ext P
  constructor
  · intro hP
    obtain ⟨hL,hfree⟩:=Finset.mem_filter.mp hP
    rw [hs] at hL
    obtain ⟨hprod,hgood,hodd⟩:=Finset.mem_filter.mp hL
    have hp:Prime P:=prime_of_normalized_factor P (Multiset.mem_toFinset.mp hprod)
    by_cases hr:P∣rowResidualPart I Q
    · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
        ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hk.2.1.ne_zero).mpr ⟨hp,hr⟩))
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_filter.mpr ⟨hprod,hgood,hodd,hr⟩,hfree⟩
  · intro hP
    rcases Finset.mem_union.mp hP with hr|ht
    · have hfactor:=Multiset.mem_toFinset.mp hr
      have hp:Prime P:=prime_of_normalized_factor P hfactor
      have hrow:=rowResidualPart_prime_exponent I Q P hfactor
      have hgood:=(supported_factors_good _ ⟨hk.1,hk.2.2⟩ P hfactor).2
      have hfree:¬Q0≤P:=by
        intro hQP
        exact hp.2.1 (hcop.isUnit_of_dvd'
          (Ideal.dvd_iff_le.mpr hQP) (dvd_of_mem_normalizedFactors hfactor))
      apply Finset.mem_filter.mpr
      refine ⟨?_,hfree⟩
      rw [hs]
      apply Finset.mem_filter.mpr
      exact ⟨Multiset.mem_toFinset.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (mul_ne_zero hI hQ)).mpr
        ⟨hp,dvd_mul_of_dvd_left (dvd_of_mem_normalizedFactors hrow.1) Q⟩),hgood⟩
    · obtain ⟨hpool,hfree⟩:=Finset.mem_filter.mp ht
      obtain ⟨hprod,hgood,hodd,_⟩:=Finset.mem_filter.mp hpool
      apply Finset.mem_filter.mpr
      refine ⟨?_,hfree⟩
      rw [hs]
      exact Finset.mem_filter.mpr ⟨hprod,hgood,hodd⟩

def primeUnionToFree (lengthScale Q0 k:Ideal O) (T:Finset (Ideal O))
    (hs:freePrimePool lengthScale Q0=primeSupport k∪T) :
    primeSupport k ⊕ T → FreePrimeIndex lengthScale Q0 := fun P=>by
  have hm:(Sum.elim Subtype.val Subtype.val P)∈freePrimePool lengthScale Q0:=by
    rw [hs]
    cases P with
    | inl P=>exact Finset.mem_union_left _ P.property
    | inr P=>exact Finset.mem_union_right _ P.property
  exact ⟨⟨Sum.elim Subtype.val Subtype.val P,(Finset.mem_filter.mp hm).1⟩,
    (Finset.mem_filter.mp hm).2⟩

lemma primeUnionToFree_val (lengthScale Q0 k:Ideal O) (T:Finset (Ideal O))
    (hs:freePrimePool lengthScale Q0=primeSupport k∪T) (P:primeSupport k⊕T) :
    (primeUnionToFree lengthScale Q0 k T hs P).val.val=Sum.elim Subtype.val Subtype.val P := rfl

lemma primeUnionToFree_bijective (lengthScale Q0 k:Ideal O) (T:Finset (Ideal O))
    (hs:freePrimePool lengthScale Q0=primeSupport k∪T)
    (hd:Disjoint (primeSupport k) T) :
    Function.Bijective (primeUnionToFree lengthScale Q0 k T hs) := by
  constructor
  · intro P R he
    have hv:=congrArg (fun S:FreePrimeIndex lengthScale Q0=>S.val.val) he
    change Sum.elim Subtype.val Subtype.val P=Sum.elim Subtype.val Subtype.val R at hv
    cases P with
    | inl P=>cases R with
      | inl R=>exact congrArg Sum.inl (Subtype.ext hv)
      | inr R=>
        change P.val=R.val at hv
        exact (Finset.disjoint_left.mp hd P.property (hv.symm ▸ R.property)).elim
    | inr P=>cases R with
      | inl R=>
        change P.val=R.val at hv
        exact (Finset.disjoint_left.mp hd R.property (hv ▸ P.property)).elim
      | inr R=>exact congrArg Sum.inr (Subtype.ext hv)
  · intro P
    have hm:P.val.val∈primeSupport k∪T:=by
      rw [←hs]
      exact Finset.mem_filter.mpr ⟨P.val.property,P.property⟩
    rcases Finset.mem_union.mp hm with hl|hr
    · exact ⟨Sum.inl ⟨P.val.val,hl⟩,Subtype.ext (Subtype.ext rfl)⟩
    · exact ⟨Sum.inr ⟨P.val.val,hr⟩,Subtype.ext (Subtype.ext rfl)⟩

noncomputable def primeUnionEquiv (lengthScale Q0 k:Ideal O) (T:Finset (Ideal O))
    (hs:freePrimePool lengthScale Q0=primeSupport k∪T)
    (hd:Disjoint (primeSupport k) T) :
    primeSupport k⊕T ≃ FreePrimeIndex lengthScale Q0 :=
  Equiv.ofBijective (primeUnionToFree lengthScale Q0 k T hs) (primeUnionToFree_bijective lengthScale Q0 k T hs hd)

lemma primeUnionEquiv_val (lengthScale Q0 k:Ideal O) (T:Finset (Ideal O))
    (hs:freePrimePool lengthScale Q0=primeSupport k∪T)
    (hd:Disjoint (primeSupport k) T) (P:primeSupport k⊕T) :
    (primeUnionEquiv lengthScale Q0 k T hs hd P).val.val=Sum.elim Subtype.val Subtype.val P := rfl

theorem prod_freePrimeIndex_eq {M:Type*} [CommMonoid M]
    (lengthScale Q0 k:Ideal O) (T:Finset (Ideal O))
    (hs:freePrimePool lengthScale Q0=primeSupport k∪T)
    (hd:Disjoint (primeSupport k) T) (f:Ideal O → M) :
    (∏P:FreePrimeIndex lengthScale Q0,f P.val.val)=(∏P:primeSupport k,f P.val)*(∏P:T,f P.val) := by
  calc
    _=(∏P:primeSupport k⊕T,f (Sum.elim Subtype.val Subtype.val P)):=
      (Fintype.prod_equiv (primeUnionEquiv lengthScale Q0 k T hs hd) _ _ (fun P=>rfl)).symm
    _=_:=Fintype.prod_sum_type _

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss UniqueFactorizationMonoid
open scoped BigOperators Classical

namespace GoodMaskRowData
variable {m f z : O} (D : GoodMaskRowData m f z)
variable (I F Q0 : Ideal O) (hI : I≠0) (hF : Squarefree F) (hm : m≠0)
    (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
include D I F Q0 hI hF hm hf hz hbad hcop

theorem freePrimePool_eq : freePrimePool D.movingIdeal Q0=
    primeSupport (rowResidualPart I (Ideal.span {m}*F))∪FreeReflection.pool I (Ideal.span {m}*F) Q0 := by
  apply freePrimePool_eq_residual_union _ _ _ _ hI
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero) hbad hcop
  exact D.moving_primeSupport I F hI hF.ne_zero hm hf hz

def freePrimeEquiv :
    primeSupport (rowResidualPart I (Ideal.span {m}*F))⊕FreeReflection.pool I (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex D.movingIdeal Q0 :=
  primeUnionEquiv _ _ _ _ (D.freePrimePool_eq I F Q0 hI hF hm hf hz hbad hcop)
    (residual_nonresidual_disjoint I (Ideal.span {m}*F) Q0)

lemma freePrimeEquiv_val
    (P : primeSupport (rowResidualPart I (Ideal.span {m}*F))⊕FreeReflection.pool I (Ideal.span {m}*F) Q0) :
    (D.freePrimeEquiv I F Q0 hI hF hm hf hz hbad hcop P).val.val=Sum.elim Subtype.val Subtype.val P := rfl

theorem freePrimeEquiv_exponent
    (P : primeSupport (rowResidualPart I (Ideal.span {m}*F))⊕FreeReflection.pool I (Ideal.span {m}*F) Q0) :
    (normalizedFactors D.movingIdeal).count
      (D.freePrimeEquiv I F Q0 hI hF hm hf hz hbad hcop P).val.val%6=
        Sum.elim (fun _ => 1) (fun S => completedLocalExponent I F S.val) P := by
  cases P with
  | inl P =>
    have hk := rowResidualPart_admissible I (Ideal.span {m}*F) hbad
    have hp := supported_factors_good _ ⟨hk.1,hk.2.2⟩ P.val (Multiset.mem_toFinset.mp P.property)
    letI : P.val.IsMaximal := hp.1
    exact D.moving_residual_exponent I F hI hF hf hz P.val hp.2.1 hp.2.2
      (Multiset.mem_toFinset.mp P.property)
  | inr P =>
    letI : P.val.IsMaximal := FreeReflection.pool_maximal I (Ideal.span {m}*F) Q0 P
    exact D.moving_exponent I F hI hF hf hz P.val
      (FreeReflection.pool_good I (Ideal.span {m}*F) Q0 P)
      (FreeReflection.pool_odd I (Ideal.span {m}*F) Q0 P)

end GoodMaskRowData

def nonresidualPoolEquiv (R I Q Q0 : Ideal O) (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hA : rowPowerfulPart R=rowPowerfulPart I) (hT : rowMaskPart R Q=rowMaskPart I Q) :
    FreeReflection.pool R Q Q0 ≃ FreeReflection.pool I Q Q0 := by
  have he := FreeReflection.pool_eq_on_fiber R I Q Q0 hR hI hQ hA hT
  exact {
    toFun := fun P => ⟨P.val,he ▸ P.property⟩
    invFun := fun P => ⟨P.val,he.symm ▸ P.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma nonresidualPoolEquiv_exponent (R I F Q Q0 : Ideal O) (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hA : rowPowerfulPart R=rowPowerfulPart I) (hT : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q0) :
    completedLocalExponent I F (nonresidualPoolEquiv R I Q Q0 hR hI hQ hA hT P).val=
      completedLocalExponent R F P.val :=
  (completedReflectionPool_exponent_eq R I F Q hR hI hQ hA hT
    ⟨P.val,FreeReflection.pool_subset R Q Q0 P.property⟩).symm

namespace GoodMaskRowData
variable {m f z : O} (D : GoodMaskRowData m f z)
variable (R I F Q0 : Ideal O) (hR : R≠0) (hI : I≠0) (hF : Squarefree F) (hm : m≠0)
    (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA : rowPowerfulPart R=rowPowerfulPart I)
    (hT : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include D R I F Q0 hR hI hF hm hf hz hbad hcop hA hT

def freePrimeFiberEquiv :
    primeSupport (rowResidualPart I (Ideal.span {m}*F))⊕FreeReflection.pool R (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex D.movingIdeal Q0 :=
  (Equiv.sumCongr (Equiv.refl _)
    (nonresidualPoolEquiv R I (Ideal.span {m}*F) Q0 hR hI
      (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero) hA hT)).trans
    (D.freePrimeEquiv I F Q0 hI hF hm hf hz hbad hcop)

lemma freePrimeFiberEquiv_val
    (P : primeSupport (rowResidualPart I (Ideal.span {m}*F))⊕FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (D.freePrimeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT P).val.val=
      Sum.elim Subtype.val Subtype.val P := by cases P <;> rfl

theorem freePrimeFiberEquiv_exponent
    (P : primeSupport (rowResidualPart I (Ideal.span {m}*F))⊕FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (normalizedFactors D.movingIdeal).count
      (D.freePrimeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT P).val.val%6=
        Sum.elim (fun _ => 1) (fun S => completedLocalExponent R F S.val) P := by
  cases P with
  | inl P => exact D.freePrimeEquiv_exponent I F Q0 hI hF hm hf hz hbad hcop (Sum.inl P)
  | inr P =>
    exact (D.freePrimeEquiv_exponent I F Q0 hI hF hm hf hz hbad hcop
      (Sum.inr (nonresidualPoolEquiv R I (Ideal.span {m}*F) Q0 hR hI
        (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero) hA hT P))).trans
      (nonresidualPoolEquiv_exponent R I F (Ideal.span {m}*F) Q0 hR hI
        (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero) hA hT P)

end GoodMaskRowData
end CanonicalRowCompletion

namespace CanonicalRowCompletion
open scoped BigOperators Classical
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def residualActivePrimes (e:α⊕β ≃ γ) : Finset γ :=
  Finset.univ.image (fun a:α=>e (Sum.inl a))

omit [Fintype β] [Fintype γ] in
lemma residualActivePrimes_not_inr (e:α⊕β ≃ γ) (b:β) :
    e (Sum.inr b)∉residualActivePrimes e := by
  intro h
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp h
  cases e.injective ha

def nonresidualComplementMap (e:α⊕β ≃ γ) : β → {g:γ // g∉residualActivePrimes e} :=
  fun b=>⟨e (Sum.inr b),residualActivePrimes_not_inr e b⟩

omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementMap_bijective (e:α⊕β ≃ γ) :
    Function.Bijective (nonresidualComplementMap e) := by
  constructor
  · intro a b hab
    exact Sum.inr.inj (e.injective (congrArg Subtype.val hab))
  · intro g
    obtain ⟨x,hx⟩:=e.surjective g.val
    cases x with
    | inl a=>
      exact (g.property (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,hx⟩)).elim
    | inr b=>exact ⟨b,Subtype.ext hx⟩

noncomputable def nonresidualComplementEquiv (e:α⊕β ≃ γ) :
    β ≃ {g:γ // g∉residualActivePrimes e} :=
  Equiv.ofBijective (nonresidualComplementMap e) (nonresidualComplementMap_bijective e)

omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementEquiv_val (e:α⊕β ≃ γ) (b:β) :
    (nonresidualComplementEquiv e b).val=e (Sum.inr b) := rfl

omit [Fintype β] [Fintype γ] in
lemma complementActive_image (e:α⊕β ≃ γ) (B:Finset β) :
    (B.map (nonresidualComplementEquiv e).toEmbedding).image Subtype.val=
      B.image (fun b=>e (Sum.inr b)) := by
  simp only [Finset.map_eq_image,Finset.image_image,Function.comp_def,
    Equiv.toEmbedding_apply,nonresidualComplementEquiv_val]

lemma inactive_product_nonresidual (e:α⊕β ≃ γ) (z:γ → ℂ) (B:Finset β) :
    (∏g∈(Finset.univ:Finset {g:γ // g∉residualActivePrimes e})\
      B.map (nonresidualComplementEquiv e).toEmbedding,z g.val)=
      ∏b∈(Finset.univ:Finset β)\B,z (e (Sum.inr b)) := by
  symm
  apply Finset.prod_equiv (nonresidualComplementEquiv e)
  · intro b
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_map_equiv,
      Equiv.symm_apply_apply]
  · intro b hb
    rfl

theorem inactive_weight_nonresidual_subsets (e:α⊕β ≃ γ) (z:γ → ℂ)
    (hz:∀a:α,z (e (Sum.inl a))=0) (F:Finset γ → ℂ) :
    (∑A:Finset γ,(∏g∈(Finset.univ:Finset γ)\A,z g)*F A)=
      ∑B:Finset β,(∏b∈(Finset.univ:Finset β)\B,z (e (Sum.inr b)))*
        F (residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))) := by
  have hres:∀g∈residualActivePrimes e,z g=0:=by
    intro g hg
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hg
    exact hz a
  rw [CompletedGauss.inactive_weight_optional_active (residualActivePrimes e) z hres F]
  symm
  apply Fintype.sum_equiv (nonresidualComplementEquiv e).finsetCongr
  intro B
  change _=(∏g∈(Finset.univ:Finset {g:γ // g∉residualActivePrimes e})\
    B.map (nonresidualComplementEquiv e).toEmbedding,z g.val)*
    F (residualActivePrimes e∪(B.map (nonresidualComplementEquiv e).toEmbedding).image Subtype.val)
  rw [inactive_product_nonresidual,complementActive_image]

def optionalPrimeActive (e:α⊕β ≃ γ) (A:Finset γ) : Finset β :=
  Finset.univ.filter (fun b=>e (Sum.inr b)∈A)

omit [Fintype α] [Fintype γ] in
lemma mem_optionalPrimeActive (e:α⊕β ≃ γ) (A:Finset γ) (b:β) :
    b∈optionalPrimeActive e A ↔ e (Sum.inr b)∈A := by
  simp only [optionalPrimeActive,Finset.mem_filter,Finset.mem_univ,true_and]

def activePrimeUnionMap (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : α⊕optionalPrimeActive e A → A :=
  Sum.elim (fun a=>⟨e (Sum.inl a),hA a⟩)
    (fun b=>⟨e (Sum.inr b.val),(mem_optionalPrimeActive e A b.val).mp b.property⟩)

omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionMap_bijective (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : Function.Bijective (activePrimeUnionMap e A hA) := by
  constructor
  · intro x y hxy
    have hv:=congrArg Subtype.val hxy
    cases x with
    | inl x=>cases y with
      | inl y=>exact congrArg Sum.inl (Sum.inl.inj (e.injective hv))
      | inr y=>cases e.injective hv
    | inr x=>cases y with
      | inl y=>cases e.injective hv
      | inr y=>exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj (e.injective hv)))
  · intro a
    obtain ⟨x,hx⟩:=e.surjective a.val
    cases x with
    | inl x=>exact ⟨Sum.inl x,Subtype.ext hx⟩
    | inr x=>
      have hm:x∈optionalPrimeActive e A:=(mem_optionalPrimeActive e A x).mpr (hx.symm ▸ a.property)
      exact ⟨Sum.inr ⟨x,hm⟩,Subtype.ext hx⟩

noncomputable def activePrimeUnionEquiv (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : α⊕optionalPrimeActive e A ≃ A :=
  Equiv.ofBijective (activePrimeUnionMap e A hA) (activePrimeUnionMap_bijective e A hA)

omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionEquiv_inl (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) (a:α) :
    (activePrimeUnionEquiv e A hA (Sum.inl a)).val=e (Sum.inl a) := rfl

omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionEquiv_inr (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) (b:optionalPrimeActive e A) :
    (activePrimeUnionEquiv e A hA (Sum.inr b)).val=e (Sum.inr b.val) := rfl

omit [Fintype γ] in
theorem prod_activePrimeUnionEquiv {M:Type*} [CommMonoid M]
    (e:α⊕β ≃ γ) (A:Finset γ) (hA:∀a:α,e (Sum.inl a)∈A) (f:A → M) :
    (∏a:A,f a)=
      (∏a:α,f (activePrimeUnionEquiv e A hA (Sum.inl a)))*
        (∏b:optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA (Sum.inr b))) := by
  calc
    _=(∏x:α⊕optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA x)):=
      (Fintype.prod_equiv (activePrimeUnionEquiv e A hA) _ _ (fun _=>rfl)).symm
    _=_:=Fintype.prod_sum_type _

omit [Fintype γ] in
theorem sum_activePrimeUnionEquiv {M:Type*} [AddCommMonoid M]
    (e:α⊕β ≃ γ) (A:Finset γ) (hA:∀a:α,e (Sum.inl a)∈A) (f:A → M) :
    (∑a:A,f a)=
      (∑a:α,f (activePrimeUnionEquiv e A hA (Sum.inl a)))+
        (∑b:optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA (Sum.inr b))) := by
  calc
    _=(∑x:α⊕optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA x)):=
      (Fintype.sum_equiv (activePrimeUnionEquiv e A hA) _ _ (fun _=>rfl)).symm
    _=_:=Fintype.sum_sum_type _

theorem sum_prime_active_sets {M:Type*} [AddCommMonoid M]
    (e:α⊕β ≃ γ) (f:Finset γ → M) :
    (∑A:Finset γ,f A)=∑A:Finset (α⊕β),f (A.map e.toEmbedding) := by
  exact (Fintype.sum_equiv e.finsetCongr _ _ (fun _=>rfl)).symm
def completeActiveSet (e:α⊕β ≃ γ) (B:Finset β) : Finset γ :=
  residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))

omit [Fintype β] [Fintype γ] in
lemma completeActiveSet_residual (e:α⊕β ≃ γ) (B:Finset β) (a:α) :
    e (Sum.inl a)∈completeActiveSet e B :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩)

omit [Fintype γ] in
lemma optionalPrimeActive_completeActiveSet (e:α⊕β ≃ γ) (B:Finset β) :
    optionalPrimeActive e (completeActiveSet e B)=B := by
  ext b
  rw [mem_optionalPrimeActive]
  change e (Sum.inr b)∈residualActivePrimes e∪B.image (fun b=>e (Sum.inr b)) ↔ b∈B
  simp only [Finset.mem_union,residualActivePrimes_not_inr,false_or,Finset.mem_image]
  constructor
  · rintro ⟨b',hb',he⟩
    have hb:b'=b:=Sum.inr.inj (e.injective he)
    exact hb ▸ hb'
  · intro hb
    exact ⟨b,hb,rfl⟩

noncomputable def selectedActiveEquiv (e:α⊕β ≃ γ) (B:Finset β) :
    α⊕B ≃ completeActiveSet e B := by
  let t : B ≃ optionalPrimeActive e (completeActiveSet e B):={
    toFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    invFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  exact (Equiv.sumCongr (Equiv.refl _) t).trans
    (activePrimeUnionEquiv e (completeActiveSet e B) (completeActiveSet_residual e B))

omit [Fintype γ] in
lemma selectedActiveEquiv_inl (e:α⊕β ≃ γ) (B:Finset β) (a:α) :
    (selectedActiveEquiv e B (Sum.inl a)).val=e (Sum.inl a) := rfl

omit [Fintype γ] in
lemma selectedActiveEquiv_inr (e:α⊕β ≃ γ) (B:Finset β) (b:B) :
    (selectedActiveEquiv e B (Sum.inr b)).val=e (Sum.inr b.val) := rfl

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss UniqueFactorizationMonoid
open scoped BigOperators Classical
/-- The mandatory residual primes leave only the nonresidual inactive weights. -/
def inactiveReindexedSum {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (E : α⊕β≃γ) (z : β→ℂ) (w : Finset γ→ℂ) : ℂ :=
  ∑B : Finset β,(∏P∈Finset.univ\B,z P)*w (completeActiveSet E B)

lemma inactiveReindexedSum_eq {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (E : α⊕β≃γ) (z : γ→ℂ) (v : β→ℂ)
    (hz : ∀P : α,z (E (Sum.inl P))=0) (hv : ∀P : β,z (E (Sum.inr P))=v P)
    (w : Finset γ→ℂ) :
    (∑A : Finset γ,(∏P∈Finset.univ\A,z P)*w A)=inactiveReindexedSum E v w := by
  rw [inactive_weight_nonresidual_subsets E z hz w]
  simp only [hv,inactiveReindexedSum,completeActiveSet]

namespace GoodMaskRowData
variable {m f z : O} (D : GoodMaskRowData m f z)

def inactiveSourceSum (Q0 : Ideal O)
    (w : Finset (FreePrimeIndex D.movingIdeal Q0)→ℂ) : ℂ := by
  letI : ∀P : FreePrimeIndex D.movingIdeal Q0,
      (Ideal.span {freePrimaryPrime D.movingIdeal Q0 P}:Ideal O).IsMaximal:=
        freePrimaryPrime_maximal D.movingIdeal Q0 D.movingSupported
  exact ∑A : Finset (FreePrimeIndex D.movingIdeal Q0),
    primeInactiveFourierWeight (freePrimaryPrime D.movingIdeal Q0)
      (freePrimaryPrime_ne_zero D.movingIdeal Q0 D.movingSupported)
      (freePrimaryPrime_good D.movingIdeal Q0 D.movingSupported)
      (fun P=>(normalizedFactors D.movingIdeal).count P.val.val%6) A*w A

lemma inactiveSourceSum_formula (Q0 : Ideal O)
    (w : Finset (FreePrimeIndex D.movingIdeal Q0)→ℂ) :
    D.inactiveSourceSum Q0 w=
      ∑A : Finset (FreePrimeIndex D.movingIdeal Q0),
        (∏P∈Finset.univ\A,idealInactiveWeight P.val.val
          ((normalizedFactors D.movingIdeal).count P.val.val%6))*w A := by
  letI : ∀P : FreePrimeIndex D.movingIdeal Q0,
      (Ideal.span {freePrimaryPrime D.movingIdeal Q0 P}:Ideal O).IsMaximal:=
        freePrimaryPrime_maximal D.movingIdeal Q0 D.movingSupported
  unfold inactiveSourceSum
  apply Finset.sum_congr rfl
  intro A hA
  rw [primeInactiveFourierWeight_formula _ _ _
    (freePrimaryPrime_odd D.movingIdeal Q0 D.movingSupported) _ (fun _=>Nat.mod_lt _ (by decide : 0<6))]
  simp only [freePrimaryPrime_span D.movingIdeal Q0 D.movingSupported]
  apply congrArg (fun S : Finset (FreePrimeIndex D.movingIdeal Q0)=>
    (∏P∈S,idealInactiveWeight P.val.val ((normalizedFactors D.movingIdeal).count P.val.val%6))*w A)
  ext P
  simp only [Finset.mem_sdiff]

variable (R I F Q0 : Ideal O) (hR : R≠0) (hI : I≠0) (hF : Squarefree F) (hm : m≠0)
    (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA : rowPowerfulPart R=rowPowerfulPart I)
    (hT : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include D R I F Q0 hR hI hF hm hf hz hbad hcop hA hT

/-- Every residual prime is active; only the fixed nonresidual pool remains optional. -/
theorem inactive_source_reindex (w : Finset (FreePrimeIndex D.movingIdeal Q0)→ℂ) :
    D.inactiveSourceSum Q0 w=
      inactiveReindexedSum
        (D.freePrimeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT)
        (fun P : FreeReflection.pool R (Ideal.span {m}*F) Q0=>
          idealInactiveWeight P.val (completedLocalExponent R F P.val)) w := by
  let E:=D.freePrimeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT
  let Z : FreePrimeIndex D.movingIdeal Q0→ℂ:=fun P=>
    idealInactiveWeight P.val.val ((normalizedFactors D.movingIdeal).count P.val.val%6)
  have hzero (P : primeSupport (rowResidualPart I (Ideal.span {m}*F))) : Z (E (Sum.inl P))=0 := by
    dsimp only [Z]
    rw [D.freePrimeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inl P)]
    exact if_neg (by decide : (1:ℕ)≠0)
  have hnonres (P : FreeReflection.pool R (Ideal.span {m}*F) Q0) :
      Z (E (Sum.inr P))=idealInactiveWeight P.val (completedLocalExponent R F P.val) := by
    dsimp only [Z]
    rw [D.freePrimeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inr P),
      D.freePrimeFiberEquiv_val R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inr P)]
    rfl
  rw [D.inactiveSourceSum_formula Q0 w]
  convert inactiveReindexedSum_eq E Z _ hzero hnonres w using 1
  apply Finset.sum_congr rfl
  intro A hA
  apply congrArg (fun S : Finset (FreePrimeIndex D.movingIdeal Q0)=>(∏P∈S,Z P)*w A)
  ext P
  simp only [Finset.mem_sdiff]

end GoodMaskRowData
end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss UniqueFactorizationMonoid
open scoped BigOperators Classical

namespace GoodMaskRowData
variable {m f z : O} (D : GoodMaskRowData m f z)
variable (R I F Q0 : Ideal O) (hR : R≠0) (hI : I≠0) (hF : Squarefree F) (hm : m≠0)
    (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA : rowPowerfulPart R=rowPowerfulPart I)
    (hT : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include D R I F Q0 hR hI hF hm hf hz hbad hcop hA hT


def activeFiberEquiv (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q0)) :
    primeSupport (rowResidualPart I (Ideal.span {m}*F))⊕B ≃
      completeActiveSet (D.freePrimeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT) B :=
  selectedActiveEquiv (D.freePrimeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT) B

lemma activeFiberEquiv_span (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q0))
    (P : primeSupport (rowResidualPart I (Ideal.span {m}*F))⊕B) :
    Ideal.span {freePrimaryPrime D.movingIdeal Q0
      (D.activeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B P).val}=
      Sum.elim Subtype.val (fun P : B=>P.val.val) P := by
  cases P with
  | inl P =>
    dsimp only [activeFiberEquiv]
    rw [selectedActiveEquiv_inl,freePrimaryPrime_span D.movingIdeal Q0 D.movingSupported,
      D.freePrimeFiberEquiv_val R I F Q0 hR hI hF hm hf hz hbad hcop hA hT]
    rfl
  | inr P =>
    dsimp only [activeFiberEquiv]
    rw [selectedActiveEquiv_inr,freePrimaryPrime_span D.movingIdeal Q0 D.movingSupported,
      D.freePrimeFiberEquiv_val R I F Q0 hR hI hF hm hf hz hbad hcop hA hT]
    rfl

lemma activeFiberEquiv_exponent (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q0))
    (P : primeSupport (rowResidualPart I (Ideal.span {m}*F))⊕B) :
    (normalizedFactors D.movingIdeal).count
      (D.activeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B P).val.val.val%6=
      Sum.elim (fun _=>1) (fun P : B=>completedLocalExponent R F P.val.val) P := by
  cases P with
  | inl P =>
    exact D.freePrimeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inl P)
  | inr P =>
    exact D.freePrimeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inr P.val)

/-- The active branch of an actual completed row is a residual quadratic row times a fixed prime branch. -/
theorem activeFiberBranch_coefficient
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q0))
    (e : B→Fin 3) (n b : O) :
    let A:=completeActiveSet (D.freePrimeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT) B
    let E:=D.activeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B
    letI : ∀P : A,(Ideal.span {freePrimaryPrime D.movingIdeal Q0 P.val}:Ideal O).IsMaximal:=
      fun P=>freePrimaryPrime_maximal D.movingIdeal Q0 D.movingSupported P.val
    letI : ∀P : B,P.val.val.IsMaximal:=fun P=>FreeReflection.pool_maximal R (Ideal.span {m}*F) Q0 P.val
    reflectedBranch (fun P : A=>Ideal.span {freePrimaryPrime D.movingIdeal Q0 P.val})
      (fun P=>freePrimaryPrime_good D.movingIdeal Q0 D.movingSupported P.val)
      (fun P=>(normalizedFactors D.movingIdeal).count P.val.val.val%6) (residualLabelVia E e) n b=
      (canonicalQuadraticRowOfIdeal (rowResidualPart I (Ideal.span {m}*F)) n*
        canonicalQuadraticRowOfIdeal (rowResidualPart I (Ideal.span {m}*F)) b)*
      reflectedBranch (fun P : B=>P.val.val)
        (fun P=>FreeReflection.pool_good R (Ideal.span {m}*F) Q0 P.val)
        (fun P=>completedLocalExponent R F P.val.val) e n b := by
  dsimp only
  letI : ∀P : completeActiveSet (D.freePrimeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT) B,
      (Ideal.span {freePrimaryPrime D.movingIdeal Q0 P.val}:Ideal O).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal Q0 D.movingSupported P.val
  letI : ∀P : B,P.val.val.IsMaximal:=fun P=>FreeReflection.pool_maximal R (Ideal.span {m}*F) Q0 P.val
  exact reflectedBranch_residual_coefficient _ (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
    _ _ _ _ (D.activeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B)
    (fun P=>D.activeFiberEquiv_span R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B (Sum.inl P))
    (fun P=>D.activeFiberEquiv_span R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B (Sum.inr P)) _ _
    (fun P=>D.activeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B (Sum.inl P))
    (fun P=>D.activeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B (Sum.inr P)) e n b

end GoodMaskRowData
end CanonicalRowCompletion

namespace CanonicalRowCompletion.GoodMaskRowData
open Eisenstein SchwartzPlanePoisson CompletedGauss
open scoped BigOperators Classical
variable {m f z : O} (D : GoodMaskRowData m f z)

lemma fixedFourierCoefficient_norm (Ψ : O→*ℂ) (Q : Ideal O) (c : O) (hc : c≠0)
    (hspan : Ideal.span {c}=Q*Ideal.span {(72:O)})
    (hΨ : ∀x y : O,x-y∈Q→Ψ x=Ψ y) (hn : ∀n,‖Ψ n‖≤1)
    [Fintype (O⧸Ideal.span {9*c})] (k : O⧸Ideal.span {9*c}) :
    ‖finiteAdditiveFourierCoeff
      (residueTraceQuotientChar 1 (9*c) (mul_ne_zero (by norm_num) hc))
      (finiteThetaTwist c (D.fixedQuotient Ψ Q c hspan hΨ)) k‖≤1 :=
  finiteAdditiveFourierCoeff_norm_le_one _ _
    (finiteThetaTwist_norm_le_one c _ (D.fixedQuotient_norm Ψ Q c hspan hΨ hn)) k

end CanonicalRowCompletion.GoodMaskRowData

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss
open scoped BigOperators Classical

abbrev RowIndex (m : O) (rows : Finset (Ideal O)) (R F : Ideal O) :=
  representativeRowFiber rows R (Ideal.span {m}*F)

/-- Each ideal row uses its actual unit multiple of a principal generator. -/
def data (m : O) (hm : m≠0) (rows : Finset (Ideal O)) (R F : Ideal O)
    (hF : Squarefree F) (hrows : ∀I∈rows,I≠0) (u : Oˣ) (J : RowIndex m rows R F) :
    GoodMaskRowData m (cubicIdealGenerator F) ((u:O)*cubicIdealGenerator J.val) :=
  goodMaskRowData m (cubicIdealGenerator F) ((u:O)*cubicIdealGenerator J.val) hm
    (cubicIdealGenerator_ne_zero F hF.ne_zero)
    (mul_ne_zero u.ne_zero (cubicIdealGenerator_ne_zero J.val
      (hrows J.val (Finset.mem_filter.mp J.property).1)))

lemma rowGenerator_span (u : Oˣ) (J : Ideal O) :
    Ideal.span {((u:O)*cubicIdealGenerator J : O)}=J := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit,span_cubicIdealGenerator]

/-- The actual moving prime set splits into residual primes and the fixed optional pool. -/
def splitIndex (m : O) (hm : m≠0) (rows : Finset (Ideal O)) (R F Q0 : Ideal O)
    (hR : R≠0) (hF : Squarefree F) (hrows : ∀I∈rows,I≠0) (u : Oˣ)
    (hbad : ∀P∈fixedBadPrimes,P∣Ideal.span {m}*F) (J : RowIndex m rows R F)
    (hcop : IsCoprime Q0 (rowResidualPart J.val (Ideal.span {m}*F))) :
    primeSupport (rowResidualPart J.val (Ideal.span {m}*F))⊕FreeReflection.pool R (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex (data m hm rows R F hF hrows u J).movingIdeal Q0 :=
  (data m hm rows R F hF hrows u J).freePrimeFiberEquiv R J.val F Q0 hR
    (hrows J.val (Finset.mem_filter.mp J.property).1) hF hm
    (span_cubicIdealGenerator F) (rowGenerator_span u J.val) hbad hcop
    (representativeFiber_parts rows R (Ideal.span {m}*F) J).1.symm
    (representativeFiber_parts rows R (Ideal.span {m}*F) J).2.symm

def activeSet (m : O) (hm : m≠0) (rows : Finset (Ideal O)) (R F Q0 : Ideal O)
    (hR : R≠0) (hF : Squarefree F) (hrows : ∀I∈rows,I≠0) (u : Oˣ)
    (hbad : ∀P∈fixedBadPrimes,P∣Ideal.span {m}*F) (J : RowIndex m rows R F)
    (hcop : IsCoprime Q0 (rowResidualPart J.val (Ideal.span {m}*F)))
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q0)) :
    Finset (FreePrimeIndex (data m hm rows R F hF hrows u J).movingIdeal Q0) :=
  completeActiveSet (splitIndex m hm rows R F Q0 hR hF hrows u hbad J hcop) B

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion.GoodMaskRowData
open Eisenstein SchwartzPlanePoisson CompletedGauss UniqueFactorizationMonoid
open scoped BigOperators Classical
variable {m f z : O} (D : GoodMaskRowData m f z)

/-- The actual finite Fourier reflection has optional choices only at fixed nonresidual primes. -/
theorem canonicalReflectedSum_nonresidual (R I F : Ideal O) (hR : R≠0) (hI : I≠0)
    (hF : Squarefree F) (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (c : O) (hc : c≠0) (hcop : IsCoprime (Ideal.span {c}) (rowResidualPart I (Ideal.span {m}*F)))
    (hA : rowPowerfulPart R=rowPowerfulPart I)
    (hT : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
    [Fintype (O⧸Ideal.span {9*c})] (φ : (O⧸Ideal.span {c})→*ℂ)
    (c₀ : (O⧸Ideal.span {9*c})→O)
    (sector : (O⧸Ideal.span {9*c})→Finset (FreePrimeIndex D.movingIdeal (Ideal.span {c}))→FixedCuspSector)
    (b : (O⧸Ideal.span {9*c})→Finset (FreePrimeIndex D.movingIdeal (Ideal.span {c}))→(O⧸Ideal.span {243*c}))
    (phase : (O⧸Ideal.span {9*c})→Finset (FreePrimeIndex D.movingIdeal (Ideal.span {c}))→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    let p:=freePrimaryPrime D.movingIdeal (Ideal.span {c})
    let j:=fun P : FreePrimeIndex D.movingIdeal (Ideal.span {c})=>
      (normalizedFactors D.movingIdeal).count P.val.val%6
    letI : ∀P : FreePrimeIndex D.movingIdeal (Ideal.span {c}),(Ideal.span {p P}:Ideal O).IsMaximal:=
      freePrimaryPrime_maximal D.movingIdeal (Ideal.span {c}) D.movingSupported
    canonicalReflectedSum p (freePrimaryPrime_ne_zero D.movingIdeal (Ideal.span {c}) D.movingSupported)
      (freePrimaryPrime_good D.movingIdeal (Ideal.span {c}) D.movingSupported)
      (243*c) c hc φ j c₀ sector b phase W X=
    thetaDerivativeScalar⁻¹*∑k : O⧸Ideal.span {9*c},
      finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9*c) (mul_ne_zero (by norm_num) hc))
        (finiteThetaTwist c φ) k*
      inactiveReindexedSum
        (D.freePrimeFiberEquiv R I F (Ideal.span {c}) hR hI hF hm hf hz hbad hcop hA hT)
        (fun P : FreeReflection.pool R (Ideal.span {m}*F) (Ideal.span {c})=>
          idealInactiveWeight P.val (completedLocalExponent R F P.val))
        (cuspStratumValue p (freePrimaryPrime_good D.movingIdeal (Ideal.span {c}) D.movingSupported)
          j (243*c) (c₀ k) (sector k) (b k) (phase k) (Vstar W) X) := by
  letI : ∀P : FreePrimeIndex D.movingIdeal (Ideal.span {c}),
      (Ideal.span {freePrimaryPrime D.movingIdeal (Ideal.span {c}) P}:Ideal O).IsMaximal:=
    freePrimaryPrime_maximal D.movingIdeal (Ideal.span {c}) D.movingSupported
  dsimp only
  unfold canonicalReflectedSum
  apply congrArg (fun x : ℂ=>thetaDerivativeScalar⁻¹*x)
  apply Finset.sum_congr rfl
  intro k hk
  apply congrArg (fun x : ℂ=>finiteAdditiveFourierCoeff
    (residueTraceQuotientChar 1 (9*c) (mul_ne_zero (by norm_num) hc)) (finiteThetaTwist c φ) k*x)
  rw [←D.inactive_source_reindex R I F (Ideal.span {c}) hR hI hF hm hf hz hbad hcop hA hT]
  simp only [inactiveSourceSum,cuspStratumValue,primeInactiveFourierWeight,mul_assoc]

end CanonicalRowCompletion.GoodMaskRowData

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss
open scoped BigOperators Classical
local instance (I Q Q0 : Ideal O) : DecidableEq (FreeReflection.pool I Q Q0):=
  Classical.typeDecidableEq _
private abbrev fixedPoolSubsets (I Q Q0 : Ideal O) :
    Fintype (Finset (FreeReflection.pool I Q Q0)):=inferInstance

/-- The generic inactive-prime reindexing uses the concrete fixed-pool weights. -/
lemma inactiveReindexedSum_fixed_pool {α γ : Type*} [Fintype α] [Fintype γ]
    (I F Q Q0 : Ideal O) [subsets : Fintype (Finset (FreeReflection.pool I Q Q0))]
    (E : α⊕FreeReflection.pool I Q Q0≃γ) (w : Finset γ→ℂ) :
    inactiveReindexedSum E
      (fun P : FreeReflection.pool I Q Q0=>idealInactiveWeight P.val (completedLocalExponent I F P.val)) w=
    ∑B : Finset (FreeReflection.pool I Q Q0),
      FreeReflection.reflectionInactiveStratumWeight I F Q Q0 B*w (completeActiveSet E B) := by
  have hsubsets : subsets=fixedPoolSubsets I Q Q0:=Subsingleton.elim _ _
  cases hsubsets
  unfold inactiveReindexedSum
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun z : ℂ=>z*w (completeActiveSet E B))
  unfold FreeReflection.reflectionInactiveStratumWeight
  apply Finset.prod_congr
  · ext P
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
  · intro P hP
    rfl

end CanonicalRowCompletion

namespace CanonicalRowCompletion.GoodMaskRowData
open Eisenstein SchwartzPlanePoisson CompletedGauss NormalizedReflection UniqueFactorizationMonoid
open scoped BigOperators Classical ContDiff
local instance : Finite Oˣ:=cubic_units_finite
local instance : Fintype Oˣ:=Fintype.ofFinite _
local instance (R Q Q0 : Ideal O) (B : Finset (FreeReflection.pool R Q Q0)) :
    DecidableEq B:=Classical.typeDecidableEq B
private abbrev cuspStratumLabelFintype (R Q Q0 : Ideal O)
    (B : Finset (FreeReflection.pool R Q Q0)) : Fintype (B → Fin 3):=inferInstance
variable {m f z : O} (D : GoodMaskRowData m f z)

/-- Each actual active stratum is the finite sum of its residual quadratic branches. -/
theorem cuspStratumValue_raw
    (R I F Q0 : Ideal O) (hR : R≠0) (hI : I≠0) (hF : Squarefree F) (hm : m≠0)
    (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA : rowPowerfulPart R=rowPowerfulPart I)
    (hT : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q0))
    [labelFintype : Fintype (B → Fin 3)]
    (N c : O) (hc : c≠0) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (γ : ℂ)
    (V : ℝ→ ℂ) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support V⊆Set.Icc lo hi)
    (hV : ContDiff ℝ ∞ V) (K X : ℝ)
    (hK : 0<completedResidualScale K R (Ideal.span {m}*F)) (hX : 0<X) :
    let A:=completeActiveSet (D.freePrimeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT) B
    let p:=fun P : A=>freePrimaryPrime D.movingIdeal Q0 P.val
    let j:=fun P : A=>(normalizedFactors D.movingIdeal).count P.val.val.val%6
    letI : ∀P : A,(Ideal.span {p P}:Ideal O).IsMaximal:=
      fun P=>freePrimaryPrime_maximal D.movingIdeal Q0 D.movingSupported P.val
    letI : ∀P : B,P.val.val.IsMaximal:=fun P=>FreeReflection.pool_maximal R (Ideal.span {m}*F) Q0 P.val
    γ*fixedCuspDivisorSeries p (fun P=>freePrimaryPrime_good D.movingIdeal Q0 D.movingSupported P.val)
      N c s b j V X=
      (4*(γ/(gaussScale (fun P=>O⧸Ideal.span {p P}) j:ℂ))*(completedCuspArrayConstant s:ℂ))*
      ∑u : Oˣ,∑e : B→ Fin 3,
        canonicalCuspRawValue (fun P : B=>P.val.val)
          (fun P=>FreeReflection.pool_good R (Ideal.span {m}*F) Q0 P.val)
          (fun P=>completedLocalExponent R F P.val.val) e N c s b u
          (ramifiedBracketPhase (fun P=>Ideal.span {p P})
            (fun P=>freePrimaryPrime_good D.movingIdeal Q0 D.movingSupported P.val) j u)
          (rowResidualPart I (Ideal.span {m}*F)) V
          ((completedBranchScale K (X/(fixedCuspReflectionScale s c 1)⁻¹) R F (Ideal.span {m}*F)
            (fun P : B=>P.val.val) e)⁻¹*
              (completedResidualScale K R (Ideal.span {m}*F)/
                (Ideal.absNorm (rowResidualPart I (Ideal.span {m}*F)):ℝ))^2) := by
  have hlabels : labelFintype=cuspStratumLabelFintype R (Ideal.span {m}*F) Q0 B:=Subsingleton.elim _ _
  cases hlabels
  intro A p j
  letI : ∀P : A,(Ideal.span {p P}:Ideal O).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal Q0 D.movingSupported P.val
  letI : ∀P : B,P.val.val.IsMaximal:=fun P=>FreeReflection.pool_maximal R (Ideal.span {m}*F) Q0 P.val
  have hp : Pairwise (fun P T : A=>IsCoprime (Ideal.span {p P}) (Ideal.span {p T})) := by
    intro P T hPT
    dsimp only [p]
    rw [freePrimaryPrime_span D.movingIdeal Q0 D.movingSupported,
      freePrimaryPrime_span D.movingIdeal Q0 D.movingSupported]
    exact freePrimeIndex_pairwise_coprime D.movingIdeal Q0 (Subtype.val_injective.ne hPT)
  let E : primeSupport (rowResidualPart I (Ideal.span {m}*F))⊕B≃A:=
    D.activeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B
  have hres (P : primeSupport (rowResidualPart I (Ideal.span {m}*F))) :
      Ideal.span {p (E (Sum.inl P))}=P.val:=
    D.activeFiberEquiv_span R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B (Sum.inl P)
  have hnonres (P : B) : Ideal.span {p (E (Sum.inr P))}=P.val.val:=
    D.activeFiberEquiv_span R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B (Sum.inr P)
  have hjres (P : primeSupport (rowResidualPart I (Ideal.span {m}*F))) : j (E (Sum.inl P))=1:=
    D.activeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B (Sum.inl P)
  have hjnonres (P : B) : j (E (Sum.inr P))=completedLocalExponent R F P.val.val:=
    D.activeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT B (Sum.inr P)
  exact fixedCuspDivisorSeries_raw_branches (ι:=A) (β:=B)
    p
    (fun P=>freePrimaryPrime_ne_zero D.movingIdeal Q0 D.movingSupported P.val)
    (fun P=>freePrimaryPrime_good D.movingIdeal Q0 D.movingSupported P.val) hp
    (fun P : B=>P.val.val) (fun P=>FreeReflection.pool_good R (Ideal.span {m}*F) Q0 P.val)
    R F (Ideal.span {m}*F) (rowResidualPart I (Ideal.span {m}*F))
    (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
    E hres hnonres j (fun _=>Nat.mod_lt _ (by decide : 0<6)) hjres hjnonres
    N c hc s b V lo hi hlo hs hV K X hK hX γ

end CanonicalRowCompletion.GoodMaskRowData

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss NormalizedReflection UniqueFactorizationMonoid
open scoped BigOperators Classical ContDiff
local instance : Finite Oˣ:=cubic_units_finite
local instance : Fintype Oˣ:=Fintype.ofFinite _

/-- A common finite cusp family represents every actual completed row in a fixed ideal fiber. -/
theorem exists_actual_cusp_fiber
    (m : O) (hm : m≠0) (rows : Finset (Ideal O)) (R F : Ideal O)
    (hR : R≠0) (hF : Squarefree F) (K : ℝ)
    (hrows : ∀J∈rows,J≠0 ∧ K/2≤ (Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤ K)
    (v : Oˣ) (Ψ : O→*ℂ) (Qbase : Ideal O) (c : O) (hc : c≠0)
    (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hperiod : ∀x y : O,x-y∈Qbase→ Ψ x=Ψ y) (hnorm : ∀n,‖Ψ n‖≤ 1)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (hbad : ∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop : ∀J : RowIndex m rows R F,
      IsCoprime (Ideal.span {c}) (rowResidualPart J.val (Ideal.span {m}*F)))
    [Fintype (O⧸Ideal.span {9*c})] :
    ∃d : ReflectedFiberData (fixedCuspRayCount c hc) (fixedCuspLevelBound c hc)
        K R F (Ideal.span {m}*F),
      ∀(J : RowIndex m rows R F) (W : ℝ→ ℂ) (a b : ℝ),
        0<a→ Function.support W⊆Set.Icc a b→  ContDiff ℝ ∞ W→ ∀X : ℝ,0<X→ 
        completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J.val)) W X=
          (thetaDerivativeScalar⁻¹*(36*(fixedCuspArrayBound:ℂ)))*
            d.idealValue W X 1 completedRamifiedStep (rowResidualPart J.val (Ideal.span {m}*F)) := by
  let Q:=Ideal.span {m}*F
  let Q0:=Ideal.span {c}
  have hQ : Q≠0:=mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  let hzero:=fun J hJ=>(hrows J hJ).1
  let hupper : ∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤ K:=
    fun J hJ=>⟨(hrows J hJ).1,(hrows J hJ).2.2⟩
  let D:=data m hm rows R F hF hzero v
  have hI (J : RowIndex m rows R F) : J.val≠0:=hzero J.val (Finset.mem_filter.mp J.property).1
  have hA (J : RowIndex m rows R F) : rowPowerfulPart R=rowPowerfulPart J.val:=
    (representativeFiber_parts rows R Q J).1.symm
  have hT (J : RowIndex m rows R F) : rowMaskPart R Q=rowMaskPart J.val Q:=
    (representativeFiber_parts rows R Q J).2.symm
  let A (J : RowIndex m rows R F) (B : Finset (FreeReflection.pool R Q Q0)):=
    completeActiveSet ((D J).freePrimeFiberEquiv R J.val F Q0 hR (hI J) hF hm
      (span_cubicIdealGenerator F) (rowGenerator_span v J.val) hbad (hcop J) (hA J) (hT J)) B
  letI (J : RowIndex m rows R F) :
      ∀P : FreePrimeIndex (D J).movingIdeal Q0,
        (Ideal.span {freePrimaryPrime (D J).movingIdeal Q0 P}:Ideal O).IsMaximal:=
    freePrimaryPrime_maximal (D J).movingIdeal Q0 (D J).movingSupported
  let p (J : RowIndex m rows R F) (B : Finset (FreeReflection.pool R Q Q0)) (P : A J B):=
    freePrimaryPrime (D J).movingIdeal Q0 P.val
  let j (J : RowIndex m rows R F) (B : Finset (FreeReflection.pool R Q Q0)) (P : A J B):=
    (normalizedFactors (D J).movingIdeal).count P.val.val.val%6
  letI (J : RowIndex m rows R F) (B : Finset (FreeReflection.pool R Q Q0)) :
      ∀P : A J B,(Ideal.span {p J B P}:Ideal O).IsMaximal:=
    fun P=>freePrimaryPrime_maximal (D J).movingIdeal Q0 (D J).movingSupported P.val
  let good (J : RowIndex m rows R F) (B : Finset (FreeReflection.pool R Q Q0)) (P : A J B):
      lambda∉Ideal.span {p J B P}:=
    freePrimaryPrime_good (D J).movingIdeal Q0 (D J).movingSupported P.val
  have href:=fun J : RowIndex m rows R F=>
    (D J).completedT_canonical_reflection Ψ Qbase c hc hspan hperiod hmLam hm2
  dsimp only at href
  choose c0 sector residue phase hden hphase hreflect using href
  let fourier (J : RowIndex m rows R F) (h : O⧸Ideal.span {9*c}):=
    finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9*c) (mul_ne_zero (by norm_num) hc))
      (finiteThetaTwist c ((D J).fixedQuotient Ψ Qbase c hspan hperiod)) h
  let α (J : RowIndex m rows R F) (h : O⧸Ideal.span {9*c})
      (B : Finset (FreeReflection.pool R Q Q0)):=
    normalizedCuspRowScalar (fourier J h) (phase J h (A J B))
      (gaussScale (fun P=>O⧸Ideal.span {p J B P}) (j J B)) (sector J h (A J B))
  have hα (J : RowIndex m rows R F) (h : O⧸Ideal.span {9*c})
      (B : Finset (FreeReflection.pool R Q Q0)) : ‖α J h B‖≤ 1:=
    normalizedCuspRowScalar_norm _ _ _ _
      ((D J).fixedFourierCoefficient_norm Ψ Qbase c hc hspan hperiod hnorm h)
      (normalized_phase_bound _ _ _ (hphase J h (A J B)))
  let τ (J : RowIndex m rows R F) (B : Finset (FreeReflection.pool R Q Q0)) (u : Oˣ):=
    ramifiedBracketPhase (fun P=>Ideal.span {p J B P}) (good J B) (j J B) u
  let chosen (J : RowIndex m rows R F) (h : O⧸Ideal.span {9*c})
      (B : Finset (FreeReflection.pool R Q Q0)) :
      fixedCuspDenominators c×FixedCuspSector×(O⧸Ideal.span {243*c}):=
    (⟨c0 J h,(mem_fixedCuspDenominators c hc _).mpr (hden J h)⟩,
      sector J h (A J B),residue J h (A J B))
  let selected (J : RowIndex m rows R F) (r : FixedCuspRay c)
      (B : Finset (FreeReflection.pool R Q Q0)) : Prop:=
    r.2.1=(chosen J r.1 B).1 ∧ r.2.2.1=(chosen J r.1 B).2.1 ∧
      r.2.2.2.1=(chosen J r.1 B).2.2
  let scalar (a : FreeReflection.FixedCuspBranchIndex c R Q Q0×ℕ) (J : RowIndex m rows R F):=
    if selected J a.1.1 (reflectionSixSupport a.1.2) then
      FreeReflection.cuspRowScalar R F Q Q0 a.1.2 (α J a.1.1.1 (reflectionSixSupport a.1.2))
        (τ J (reflectionSixSupport a.1.2) a.1.1.2.2.2.2 a.2) (rowResidualPart J.val Q)
    else 0
  have hscalar (a : FreeReflection.FixedCuspBranchIndex c R Q Q0×ℕ) (J : RowIndex m rows R F) :
      ‖scalar a J‖≤ 1 := by
    dsimp only [scalar]
    split_ifs
    · exact FreeReflection.cuspRowScalar_norm _ _ _ _ _ _ _ _ (hα _ _ _)
        (ramifiedBracketPhase_norm _ _ _ _ _).le
    · simp only [norm_zero,zero_le_one]
  let d:=FreeReflection.fixedCuspFiberFromRows c hc rows R F Q Q0 hR hQ K scalar hscalar
  refine ⟨d,?_⟩
  intro J W lo hi hlo hs hW X hX
  let k:=fiberResidualIndex rows R Q K hbad hupper J
  have hshell:=representativeFiber_residual_shell rows R Q K hrows J
  letI : Fintype (FixedCuspRay c):=fixedCuspRayFintype c hc
  letI : Finite (O⧸Ideal.span {243*c}):=
    (Ideal.span {243*c}).finiteQuotientOfFreeOfNeBot
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (by norm_num) hc))
  letI : Fintype (O⧸Ideal.span {243*c}):=Fintype.ofFinite _
  letI : Fintype FixedCuspSector:=Fintype.ofFinite _
  letI (B : Finset (FreeReflection.pool R Q Q0)) : ∀P : B,P.val.val.IsMaximal:=
    fun P=>FreeReflection.pool_maximal R Q Q0 P.val
  let core (h : O⧸Ideal.span {9*c}) (u : Oˣ)
      (B : Finset (FreeReflection.pool R Q Q0)) (e : B→ Fin 3):=
    canonicalCuspRawValue (fun P : B=>P.val.val) (fun P=>FreeReflection.pool_good R Q Q0 P.val)
      (fun P=>completedLocalExponent R F P.val.val) e (243*c) (c0 J h) (sector J h (A J B))
      (residue J h (A J B)) u (τ J B u) k.val (Vstar W)
      ((completedBranchScale K (X/(fixedCuspReflectionScale (sector J h (A J B)) (c0 J h) 1)⁻¹)
        R F Q (fun P : B=>P.val.val) e)⁻¹*(completedResidualScale K R Q/(Ideal.absNorm k.val:ℝ))^2)
  let branch (r : FixedCuspRay c) (B : Finset (FreeReflection.pool R Q Q0)) (e : B→ Fin 3):=
    (d.branch (fixedCuspRayEquiv c hc r,encodeReflectionSix ⟨B,e⟩)).value
      W X 1 completedRamifiedStep k
  have hbranch (r : FixedCuspRay c) (B : Finset (FreeReflection.pool R Q Q0)) (e : B→ Fin 3) :
      branch r B e=if selected J r B then α J r.1 B*core r.1 r.2.2.2.2 B e else 0 := by
    by_cases hsel : selected J r B
    · rw [if_pos hsel]
      have hrow (n : ℕ) : scalar ((r,encodeReflectionSix ⟨B,e⟩),n) J=
          FreeReflection.cuspRowScalar R F Q Q0 (encodeReflectionSix ⟨B,e⟩)
            (α J r.1 B) (τ J B r.2.2.2.2 n) k.val := by
        simp only [scalar,reflectionSixSupport_encode,if_pos hsel]
        rfl
      have hb:=FreeReflection.fixedCuspFiberFromRows_branch_cusp_value c hc rows R F Q Q0 hR hQ K
        scalar hscalar hbad hupper J r (encodeReflectionSix ⟨B,e⟩) (α J r.1 B)
        (τ J B r.2.2.2.2) hrow W lo hi hlo hs hW X hX hshell.1 hshell.2
      dsimp only at hb
      change branch r B e=_ at hb
      rw [hb,←FreeReflection.canonicalCuspRawValue_encoded]
      rcases r with ⟨h,c',s',b',u⟩
      rcases hsel with ⟨hd,hs',hb'⟩
      dsimp only at hd hs' hb'
      subst c'
      subst s'
      subst b'
      rfl
    · rw [if_neg hsel]
      have hrow (n : ℕ) : scalar ((r,encodeReflectionSix ⟨B,e⟩),n) J=
          FreeReflection.cuspRowScalar R F Q Q0 (encodeReflectionSix ⟨B,e⟩)
            0 (τ J B r.2.2.2.2 n) k.val := by
        simp only [scalar,reflectionSixSupport_encode,if_neg hsel,FreeReflection.cuspRowScalar,zero_mul]
      have hb:=FreeReflection.fixedCuspFiberFromRows_branch_cusp_value c hc rows R F Q Q0 hR hQ K
        scalar hscalar hbad hupper J r (encodeReflectionSix ⟨B,e⟩) 0
        (τ J B r.2.2.2.2) hrow W lo hi hlo hs hW X hX hshell.1 hshell.2
      exact hb.trans (zero_mul _)
  have hvalue : d.value W X 1 completedRamifiedStep k=
      ∑h : O⧸Ideal.span {9*c},∑B : Finset (FreeReflection.pool R Q Q0),
        FreeReflection.reflectionInactiveStratumWeight R F Q Q0 B*
          ∑u : Oˣ,∑e : B→ Fin 3,α J h B*core h u B e := by
    calc
      _=∑r : FixedCuspRay c,∑B : Finset (FreeReflection.pool R Q Q0),
          FreeReflection.reflectionInactiveStratumWeight R F Q Q0 B*∑e : B→ Fin 3,branch r B e :=
        FreeReflection.fixedCuspFiberFromRows_branch_sum c hc rows R F Q Q0 hR hQ K
          scalar hscalar W X 1 completedRamifiedStep k
      _=_:=finite_selected_cusp_branch_collection
        (H:=O⧸Ideal.span {9*c}) (D:=fixedCuspDenominators c)
        (S:=FixedCuspSector) (B:=O⧸Ideal.span {243*c}) (U:=Oˣ)
        (A:=Finset (FreeReflection.pool R Q Q0)) (E:=fun B=>B→Fin 3)
        branch (fun h u B e=>α J h B*core h u B e)
        (chosen J) (FreeReflection.reflectionInactiveStratumWeight R F Q Q0)
        (by
          intro r B e
          have hh:=hbranch r B e
          dsimp only [selected] at hh
          split_ifs at hh ⊢ with hsel
          · exact hh
          · exact hh)

  have hsource (h : O⧸Ideal.span {9*c}) (B : Finset (FreeReflection.pool R Q Q0)) :
      fourier J h*cuspStratumValue (freePrimaryPrime (D J).movingIdeal Q0)
        (freePrimaryPrime_good (D J).movingIdeal Q0 (D J).movingSupported)
        (fun P=>(normalizedFactors (D J).movingIdeal).count P.val.val%6)
        (243*c) (c0 J h) (sector J h) (residue J h) (phase J h) (Vstar W) X (A J B)=
      (36*(fixedCuspArrayBound:ℂ))*∑u : Oˣ,∑e : B→ Fin 3,α J h B*core h u B e := by
    have he:=(D J).cuspStratumValue_raw R J.val F Q0 hR (hI J) hF hm
      (span_cubicIdealGenerator F) (rowGenerator_span v J.val) hbad (hcop J) (hA J) (hT J)
      B (243*c) (c0 J h) (hden J h).1 (sector J h (A J B)) (residue J h (A J B))
      (phase J h (A J B)) (Vstar W) lo hi hlo (Vstar_support W lo hi hs)
      (Vstar_contDiff W lo hi hlo hs hW) K X hshell.1 hX
    change fourier J h*(phase J h (A J B)*_)=_
    rw [he]
    change fourier J h*((4*(phase J h (A J B)/
      (gaussScale (fun P=>O⧸Ideal.span {p J B P}) (j J B):ℂ))*
        (completedCuspArrayConstant (sector J h (A J B)):ℂ))*∑u : Oˣ,∑e : B→ Fin 3,core h u B e)=_
    rw [←mul_assoc,←normalizedCuspRowScalar_reconstruct]
    simp only [α,Finset.mul_sum,mul_assoc]
  have hnon:=(D J).canonicalReflectedSum_nonresidual R J.val F hR (hI J) hF hm
    (span_cubicIdealGenerator F) (rowGenerator_span v J.val) hbad c hc (hcop J) (hA J) (hT J)
    ((D J).fixedQuotient Ψ Qbase c hspan hperiod) (c0 J) (sector J) (residue J) (phase J) W X
  have he:=(hreflect J W lo hi hlo hs hW X hX).trans hnon
  simp only [inactiveReindexedSum_fixed_pool] at he
  refine he.trans ?_
  change thetaDerivativeScalar⁻¹*(∑h : O⧸Ideal.span {9*c},fourier J h*
    ∑B : Finset (FreeReflection.pool R Q Q0),
      FreeReflection.reflectionInactiveStratumWeight R F Q Q0 B*
      cuspStratumValue _ _ _ _ _ _ _ _ _ _ (A J B))=_
  have hk : rowResidualPart J.val Q=k.val:=rfl
  rw [hk,ReflectedFiberData.idealValue_at,hvalue]
  rw [mul_assoc]
  apply congrArg (fun z : ℂ=>thetaDerivativeScalar⁻¹*z)
  calc
    _=∑h : O⧸Ideal.span {9*c},∑B : Finset (FreeReflection.pool R Q Q0),
        FreeReflection.reflectionInactiveStratumWeight R F Q Q0 B*
          (fourier J h*cuspStratumValue _ _ _ _ _ _ _ _ _ _ (A J B)) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      ring
    _=∑h : O⧸Ideal.span {9*c},∑B : Finset (FreeReflection.pool R Q Q0),
        (36*(fixedCuspArrayBound:ℂ))*(FreeReflection.reflectionInactiveStratumWeight R F Q Q0 B*
          ∑u : Oˣ,∑e : B→ Fin 3,α J h B*core h u B e) := by
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro B hB
      rw [hsource]
      ring
    _=_ := by simp only [Finset.mul_sum]

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss
open scoped BigOperators Classical ContDiff

/-- The completed rows inherit the reflected quadratic energy bound on each ideal fiber. -/
theorem actual_cusp_fiber_energy
    (c : O) (hc : c≠0) [Fintype (O⧸Ideal.span {9*c})]
    (W : ℝ→ ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(K X : ℝ),1≤ K→ 1≤ X→ ∀(m : O),m≠0→ 
    ∀(rows : Finset (Ideal O)) (R F : Ideal O),R∈rows→ Squarefree F→ 
    (∀J∈rows,J≠0 ∧ K/2≤ (Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤ K)→ 
    ∀(v : Oˣ) (Ψ : O→*ℂ) (Qbase : Ideal O),
    Ideal.span {c}=Qbase*Ideal.span {(72:O)}→ 
    (∀x y : O,x-y∈Qbase→ Ψ x=Ψ y)→ (∀n,‖Ψ n‖≤ 1)→ lambda∣m→ (2:O)∣m→ 
    (∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)→ 
    (∀J : RowIndex m rows R F,IsCoprime (Ideal.span {c}) (rowResidualPart J.val (Ideal.span {m}*F)))→ 
      (∑J : RowIndex m rows R F,
        ‖completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J.val)) W X‖^2)≤ 
      C*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+ε)*
        (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)/X)/(Ideal.absNorm (rowPowerfulPart R):ℝ) := by
  obtain ⟨C,hC,henergy⟩:=ReflectedFiberData.energy_bound W a b ha hs hW δ ε 1
    completedRamifiedStep (fixedCuspLevelBound c hc) hδ hε zero_lt_one
    completedRamifiedStep_gt_one (fixedCuspLevelBound_ge_one c hc)
  let S : ℂ:=thetaDerivativeScalar⁻¹*(36*(fixedCuspArrayBound:ℂ))
  refine ⟨1+‖S‖^2*C*(fixedCuspRayCount c hc:ℝ)^2,by positivity,?_⟩
  intro K X hK hX m hm rows R F hR hF hrows v Ψ Qbase hspan hperiod hnorm hmLam hm2 hbad hcop
  let Q:=Ideal.span {m}*F
  have hR0:=(hrows R hR).1
  have hRK:=(hrows R hR).2.2
  have hQ : Q≠0:=mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  obtain ⟨d,hd⟩:=exists_actual_cusp_fiber m hm rows R F hR0 hF K hrows v Ψ Qbase c hc
    hspan hperiod hnorm hmLam hm2 hbad hcop
  let hupper : ∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤ K:=
    fun J hJ=>⟨(hrows J hJ).1,(hrows J hJ).2.2⟩
  let ι:=fiberResidualIndex rows R Q K hbad hupper
  have hi:=fiberResidualIndex_injective rows R Q K hbad hupper
  have he:=henergy (fixedCuspRayCount c hc) K X hK hX R F Q hR0 hQ hRK
    (one_le_completedResidualScale K R Q hR0 hRK) d
  have hsum : (∑J : RowIndex m rows R F,‖d.value W X 1 completedRamifiedStep (ι J)‖^2)≤ 
      ∑k,‖d.value W X 1 completedRamifiedStep k‖^2 := by
    calc
      _=∑k∈Finset.univ.image ι,‖d.value W X 1 completedRamifiedStep k‖^2 :=
        (Finset.sum_image (fun J _ L _ he=>hi he)).symm
      _≤ _:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _=>sq_nonneg _)
  have heq : (∑J : RowIndex m rows R F,
      ‖completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J.val)) W X‖^2)=
      ‖S‖^2*∑J : RowIndex m rows R F,‖d.value W X 1 completedRamifiedStep (ι J)‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [hd J W a b ha hs hW X (lt_of_lt_of_le zero_lt_one hX)]
    have hk : rowResidualPart J.val Q=(ι J).val:=rfl
    rw [hk,ReflectedFiberData.idealValue_at,norm_mul,mul_pow]
  rw [heq]
  apply (mul_le_mul_of_nonneg_left (hsum.trans he) (sq_nonneg ‖S‖)).trans
  let shape:=(K*(Ideal.absNorm Q:ℝ))^(10*δ+ε)*
    (K+K^2*(Ideal.absNorm Q:ℝ)/X)/(Ideal.absNorm (rowPowerfulPart R):ℝ)
  have hshape : 0≤  shape:=by dsimp only [shape]; positivity
  calc
    _=(‖S‖^2*C*(fixedCuspRayCount c hc:ℝ)^2)*shape := by dsimp only [shape]; ring
    _≤ (1+‖S‖^2*C*(fixedCuspRayCount c hc:ℝ)^2)*shape :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hshape
    _=_ := by dsimp only [shape,Q]; ring

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss
open scoped BigOperators Classical ContDiff

/-- Summing the powerful and mask fibers gives the completed energy of an entire ideal shell. -/
theorem actual_cusp_shell_energy
    (c : O) (hc : c≠0) [Fintype (O⧸Ideal.span {9*c})]
    (W : ℝ→ ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(K X : ℝ),1≤ K→ 1≤ X→ ∀(m : O),m≠0→ 
    ∀(rows : Finset (Ideal O)) (F : Ideal O),Squarefree F→ 
    (∀J∈rows,J≠0 ∧ K/2≤ (Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤ K)→ 
    ∀(v : Oˣ) (Ψ : O→*ℂ) (Qbase : Ideal O),
    Ideal.span {c}=Qbase*Ideal.span {(72:O)}→ 
    (∀x y : O,x-y∈Qbase→ Ψ x=Ψ y)→ (∀n,‖Ψ n‖≤ 1)→ lambda∣m→ (2:O)∣m→ 
    (∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)→ 
    (∀J∈rows,IsCoprime (Ideal.span {c}) (rowResidualPart J (Ideal.span {m}*F)))→ 
      (∑J∈rows,
        ‖completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J)) W X‖^2)≤ 
      C*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+2*ε)*
        (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)/X) := by
  obtain ⟨C,hC,hfiber⟩:=actual_cusp_fiber_energy c hc W a b ha hs hW δ ε hδ hε
  obtain ⟨D,hD,houter⟩:=completed_outer_row_small_power ε hε
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro K X hK hX m hm rows F hF hrows v Ψ Qbase hspan hperiod hnorm hmLam hm2 hbad hcop
  let Q:=Ideal.span {m}*F
  have hQ : Q≠0:=mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  let f (J : Ideal O):=
    ‖completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J)) W X‖^2
  let B:=C*(K*(Ideal.absNorm Q:ℝ))^(10*δ+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)
  have hB : 0≤ B:=by dsimp only [B]; positivity
  have hblocks (A : Ideal O) (hA : A∈rows.image rowPowerfulPart)
      (T : Ideal O) (hT : T∈rows.image (fun I=>rowMaskPart I Q)) :
      (∑I∈completedRowFiber rows Q A T,f I)≤ B/(Ideal.absNorm A:ℝ) := by
    by_cases hempty : completedRowFiber rows Q A T=∅
    · rw [hempty,Finset.sum_empty]
      exact div_nonneg hB (Nat.cast_nonneg _)
    · obtain ⟨R,hR⟩:=Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨hRrows,hRA,hRT⟩:=Finset.mem_filter.mp hR
      have hb:=hfiber K X hK hX m hm rows R F hRrows hF hrows v Ψ Qbase hspan hperiod hnorm
        hmLam hm2 hbad (fun J=>hcop J.val (Finset.mem_filter.mp J.property).1)
      change (∑J : representativeRowFiber rows R Q,f J.val) ≤ _ at hb
      rw [Finset.sum_coe_sort (s:=representativeRowFiber rows R Q) (f:=f)] at hb
      change (∑I∈representativeRowFiber rows R Q,f I)≤ B/(Ideal.absNorm (rowPowerfulPart R):ℝ) at hb
      simpa only [representativeRowFiber,hRA,hRT] using hb
  have hb:=houter rows Q hQ f B hB hblocks
  have hnormQ : 0<(Ideal.absNorm Q:ℝ):=nonzeroDualIdeal_norm_pos ⟨Q,hQ⟩
  have hKQ : 0<K*(Ideal.absNorm Q:ℝ):=mul_pos (lt_of_lt_of_le zero_lt_one hK) hnormQ
  have hp : (Ideal.absNorm Q:ℝ)^ε≤ (K*(Ideal.absNorm Q:ℝ))^ε:=
    Real.rpow_le_rpow hnormQ.le (le_mul_of_one_le_left hnormQ.le hK) hε.le
  calc
    _≤ D*(Ideal.absNorm Q:ℝ)^ε*B:=hb
    _≤ D*(K*(Ideal.absNorm Q:ℝ))^ε*B:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hD.le) hB
    _=_ := by
      dsimp only [B]
      rw [show 10*δ+2*ε=ε+(10*δ+ε) by ring,Real.rpow_add hKQ ε (10*δ+ε)]
      dsimp only [Q]
      ring

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss
open scoped BigOperators Classical ContDiff

/-- Dyadic summation extends the completed shell estimate to every bounded finite ideal family. -/
theorem actual_cusp_row_energy
    (c : O) (hc : c≠0) [Fintype (O⧸Ideal.span {9*c})]
    (W : ℝ→ ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(K X : ℝ),1≤ K→ 1≤ X→ ∀(m : O),m≠0→ 
    ∀(rows : Finset (Ideal O)) (F : Ideal O),Squarefree F→ 
    (∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤ K)→ 
    ∀(v : Oˣ) (Ψ : O→*ℂ) (Qbase : Ideal O),
    Ideal.span {c}=Qbase*Ideal.span {(72:O)}→ 
    (∀x y : O,x-y∈Qbase→ Ψ x=Ψ y)→ (∀n,‖Ψ n‖≤ 1)→ lambda∣m→ (2:O)∣m→ 
    (∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)→ 
    (∀J∈rows,IsCoprime (Ideal.span {c}) (rowResidualPart J (Ideal.span {m}*F)))→ 
      (∑J∈rows,
        ‖completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J)) W X‖^2)≤ 
      C*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+2*ε)*
        (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)/X) := by
  obtain ⟨C,hC,hS⟩:=actual_cusp_shell_energy c hc W a b ha hs hW δ ε hδ hε
  let s:=10*δ+2*ε
  refine ⟨C*(16*(2:ℝ)^s),by positivity,?_⟩
  intro K X hK hX m hm rows F hF hrows v Ψ Qbase hspan hperiod hnorm hmLam hm2 hbad hcop
  let Q:=Ideal.span {m}*F
  have hQ : Q≠0:=mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  have hnormQ : 0<(Ideal.absNorm Q:ℝ):=nonzeroDualIdeal_norm_pos ⟨Q,hQ⟩
  let f (J : Ideal O):=
    ‖completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J)) W X‖^2
  have hd (j : ℕ) :
      (∑I∈completedRowDyad rows j,f I)≤ 
        C*((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
          ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X) := by
    exact hS ((2:ℝ)^j) X (one_le_pow₀ (by norm_num)) hX m hm (completedRowDyad rows j) F hF
      (completedRowDyad_bounds rows j (fun I hI=>(hrows I hI).1)) v Ψ Qbase
      hspan hperiod hnorm hmLam hm2 hbad
      (fun I hI=>hcop I (Finset.mem_filter.mp hI).1)
  have hb:=completedRowDyadic_shape s K X (Ideal.absNorm Q:ℝ) (by dsimp only [s]; positivity)
    hK (lt_of_lt_of_le zero_lt_one hX) hnormQ
  calc
    _=∑j∈Finset.range (completedRowDyadicLength K+1),∑I∈completedRowDyad rows j,f I:=
      (completedRowDyad_sum rows K (le_trans zero_le_one hK) (fun I hI=>(hrows I hI).2) f).symm
    _≤ ∑j∈Finset.range (completedRowDyadicLength K+1),
        C*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
          ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_assoc] using hd j
    _=C*∑j∈Finset.range (completedRowDyadicLength K+1),
        ((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
          ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X):=(Finset.mul_sum _ _ _).symm
    _≤ C*((16*(2:ℝ)^s)*(K*(Ideal.absNorm Q:ℝ))^s*(K+K^2*(Ideal.absNorm Q:ℝ)/X)):=
      mul_le_mul_of_nonneg_left hb hC.le
    _=_:=by dsimp only [s,Q]; ring

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss
open SchwartzPlanePoisson.CanonicalQuadraticSieve SecondPassArithmetic
open scoped BigOperators Classical ContDiff

/-- The short cube inverse has a uniform arithmetic energy bound on actual ideal rows. -/
theorem actual_short_row_energy
    (c : O) (hc : c≠0) [Fintype (O⧸Ideal.span {9*c})]
    (W : ℝ→ ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(K X H₀ : ℝ),1≤ K→ 1≤ H₀→ H₀^3≤ X→ ∀(m : O),m≠0→ 
    ∀(rows : Finset (Ideal O)) (F : Ideal O),Squarefree F→ 
    (∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤ K)→ 
    ∀(v : Oˣ) (Ψ : O→*ℂ) (Qbase : Ideal O),
    Ideal.span {c}=Qbase*Ideal.span {(72:O)}→ 
    (∀x y : O,x-y∈Qbase→ Ψ x=Ψ y)→ (∀n,‖Ψ n‖≤ 1)→ lambda∣m→ (2:O)∣m→ 
    (∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)→ 
    (∀J∈rows,IsCoprime (Ideal.span {c}) (rowResidualPart J (Ideal.span {m}*F)))→ 
      (∑J∈rows,
        ‖shortCompletedSum (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J)) W X H₀‖^2)≤ 
      (C*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+2*ε)*
        (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)*H₀^3/X))*
          (descentLatticeConstant*Real.exp 1*(normLogBin H₀+1:ℝ))^2 := by
  obtain ⟨C,hC,hcompleted⟩:=actual_cusp_row_energy c hc W a b ha hs hW δ ε hδ hε
  refine ⟨C,hC,?_⟩
  intro K X H₀ hK hH₀ hX m hm rows F hF hrows v Ψ Qbase hspan hperiod hnorm hmLam hm2 hbad hcop
  let Q:=Ideal.span {m}*F
  let row (J : rows):=rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J.val)
  let E:=C*(K*(Ideal.absNorm Q:ℝ))^(10*δ+2*ε)*
    (K+K^2*(Ideal.absNorm Q:ℝ)*H₀^3/X)
  have hX0 : 0<X:=(pow_pos (lt_of_lt_of_le zero_lt_one hH₀) 3).trans_le hX
  have hE : 0≤ E:=by dsimp only [E]; positivity
  have hWc : HasCompactSupport W:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  have hbound (H : Ideal O) (hH : H∈shortCubeRange H₀) :
      (∑J : rows,‖completedIdealT (row J) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤ E := by
    have hh:=(mem_shortCubeRange H₀ H).mp hH
    have hn : 0<(Ideal.absNorm H:ℝ):=nonzeroDualIdeal_norm_pos ⟨H,hh.1⟩
    have hp : (Ideal.absNorm H:ℝ)^3≤ H₀^3:=pow_le_pow_left₀ hn.le hh.2.le 3
    have hY : 1≤ X/(Ideal.absNorm H:ℝ)^3:=
      (le_div_iff₀ (pow_pos hn 3)).mpr (by simpa only [one_mul] using hp.trans hX)
    have hb:=hcompleted K (X/(Ideal.absNorm H:ℝ)^3) hK hY m hm rows F hF hrows v Ψ Qbase
      hspan hperiod hnorm hmLam hm2 hbad hcop
    simp_rw [completedIdealT_eq_completedT _ W hWc _ (div_pos hX0 (pow_pos hn 3))]
    dsimp only [row]
    rw [Finset.sum_coe_sort (s:=rows) (f:=fun J => ‖completedT (rowTwist Ψ m (cubicIdealGenerator F)
      ((v:O)*cubicIdealGenerator J)) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)]
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add le_rfl
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by positivity : 0≤ K^2*(Ideal.absNorm Q:ℝ))) hX0.le
  have hb:=short_completed_energy row
    (fun J n=>rowTwist_norm Ψ hnorm m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J.val) n)
    W X H₀ E hE hbound
  dsimp only [row] at hb
  rw [Finset.sum_coe_sort (s:=rows) (f:=fun J =>
    ‖shortCompletedSum (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J)) W X H₀‖^2)] at hb
  exact hb

end CanonicalRowCompletion.ActualCuspFiber

open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss CanonicalCoefficientClass RayFourExpansion
open UniqueFactorizationMonoid
open scoped BigOperators Classical

lemma rowTwist_normHeight (Ψ : O →* ℂ) (θ : ℝ) (m f z : O) :
    rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ) m f z =
      SecondPassArithmetic.normHeightTwist (rowTwist Ψ m f z) θ := by
  unfold rowTwist
  exact (SecondPassArithmetic.normHeightTwist_mul _ _ θ).symm

/-- A character modulo four preserves the fixed periodicity of its base character. -/
lemma baseRayTwist_periodic (Qbase : Ideal O) (h4 : Qbase≤Ideal.span {(4:O)})
    (base Ψ : O →* ℂ) (hΨ : IsBaseRayTwist base Ψ)
    (hbase : ∀x y : O,x-y∈Qbase → base x=base y) :
    ∀x y : O,x-y∈Qbase → Ψ x=Ψ y := by
  intro x y hxy
  have hquot : Ideal.Quotient.mk (Ideal.span {(4:O)}) x=
      Ideal.Quotient.mk (Ideal.span {(4:O)}) y := by
    apply sub_eq_zero.mp
    rw [←map_sub]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (h4 hxy)
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hbase x y hxy
  · simp only [MonoidHom.mul_apply,rayMonoid_apply,hquot,hbase x y hxy]

/-- Removing all prime factors of a conductor from a row leaves a coprime residual ideal. -/
lemma rowResidualPart_coprime_conductor (c : O) (hc : c≠0) (I Q : Ideal O)
    (hsupport : ∀P∈primeSupport (Ideal.span {c}),P∣Q) :
    IsCoprime (Ideal.span {c}) (rowResidualPart I Q) := by
  have hcI : (Ideal.span {c}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr hc
  apply ideals_coprime_of_relprime
  apply (isRelPrime_iff_no_prime_factors hcI).mpr
  intro P hp hr hP
  have hpc : P∈primeSupport (Ideal.span {c}):=Multiset.mem_toFinset.mpr
    ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hcI).mpr ⟨hP,hp⟩)
  have hpr : P∈normalizedFactors (rowResidualPart I Q):=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff (rowResidualPart_squarefree I Q).ne_zero).mpr ⟨hP,hr⟩
  rw [rowResidualPart,normalizedFactors_squarefreeResidualPart] at hpr
  exact (Multiset.mem_filter.mp hpr).2 (hsupport P hpc)

/-- The excluded-prime mask supplies all ramified, parity, and conductor coprimality inputs. -/
theorem excluded_mask_inputs (S : Finset (Ideal O))
    (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (c : O) (hc : c≠0) (hsupport : primeSupport (Ideal.span {c})⊆S)
    (m : O) (hm : m≠0) (F : Ideal O) :
    m*excludedGenerator S≠0 ∧ lambda∣m*excludedGenerator S ∧ (2:O)∣m*excludedGenerator S ∧
      (∀P∈fixedBadPrimes,P∣Ideal.span {m*excludedGenerator S}*F) ∧
      ∀I : Ideal O,IsCoprime (Ideal.span {c})
        (rowResidualPart I (Ideal.span {m*excludedGenerator S}*F)) := by
  have he : excludedGenerator S≠0:=cubicIdealGenerator_ne_zero _
    (Finset.prod_ne_zero_iff.mpr (fun P hP=>(hSp P hP).ne_zero))
  have hLam : lambda∣excludedGenerator S := by
    apply Ideal.mem_span_singleton.mp
    exact excludedGenerator_mem S (hbad (Finset.mem_insert_self _ _))
  have h2 : (2:O)∣excludedGenerator S := by
    have he2 : excludedGenerator S∈cubicTwoIdeal:=
      excludedGenerator_mem S (hbad (Finset.mem_insert_of_mem (Finset.mem_singleton_self cubicTwoIdeal)))
    have hd : -(2:O)∣excludedGenerator S:=Ideal.mem_span_singleton.mp he2
    obtain ⟨r,hr⟩:=hd
    refine ⟨-r,?_⟩
    rw [hr]
    ring
  have hp (P : Ideal O) (hP : P∈S) : P∣Ideal.span {m*excludedGenerator S}*F := by
    apply dvd_mul_of_dvd_left
    apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_le.mpr
    exact Set.singleton_subset_iff.mpr (P.mul_mem_left m (excludedGenerator_mem S hP))
  refine ⟨mul_ne_zero hm he,dvd_mul_of_dvd_right hLam m,dvd_mul_of_dvd_right h2 m,
    fun P hP=>hp P (hbad hP),?_⟩
  intro I
  exact rowResidualPart_coprime_conductor c hc I _ (fun P hP=>hp P (hsupport hP))

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion
/-- The rank margin converts the completed short energy to its global mass scale. -/
theorem shortEnergy_scalar_normalization (C H R Z K X F G ε : ℝ)
    (hC : 0≤C) (hH : 0≤H) (hR : 0≤R) (hZ : 1≤Z) (hK : 0≤K)
    (hX : 0<X) (hF : 0≤F) (hG : 1≤G) (hε : 0≤ε)
    (hFZ : F≤Z^3) (hmass : X*F≤Z^3)
    (hmargin : (2*K)*G≤X*F*Z^(-((1:ℝ)/40))) :
    2*X*((C*H)*R*((2*K)*G*F)^ε*(K*F)*Z^ε)≤
      (C*H)*R*(X*F)^2*Z^(7*ε-(1:ℝ)/40) := by
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hs : Z^(-((1:ℝ)/40))≤1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : -((1:ℝ)/40)≤0)
  have hp : (2*K)*G*F≤Z^6 := by
    calc
      _ ≤ (X*F*Z^(-((1:ℝ)/40)))*F:=mul_le_mul_of_nonneg_right hmargin hF
      _ ≤ (X*F)*F:=mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (mul_one _)) hF
      _ ≤ (Z^3)*(Z^3):=mul_le_mul hmass hFZ hF (by positivity)
      _ = _:=by ring
  have hpow : ((2*K)*G*F)^ε≤Z^(6*ε) := by
    apply (Real.rpow_le_rpow (by positivity) hp hε).trans_eq
    rw [←Real.rpow_natCast_mul hZ0.le]
    norm_num
  have hrow : 2*K≤X*F*Z^(-((1:ℝ)/40)) :=
    (le_mul_of_one_le_right (by positivity) hG).trans hmargin
  have hnorm : 2*X*(K*F)≤(X*F)^2*Z^(-((1:ℝ)/40)) := by
    calc
      _ = (X*F)*(2*K):=by ring
      _ ≤ (X*F)*(X*F*Z^(-((1:ℝ)/40))):=mul_le_mul_of_nonneg_left hrow (by positivity)
      _ = _:=by ring
  calc
    _ = (C*H)*R*((2*K)*G*F)^ε*(2*X*(K*F))*Z^ε:=by ring
    _ ≤ (C*H)*R*Z^(6*ε)*((X*F)^2*Z^(-((1:ℝ)/40)))*Z^ε:=by gcongr
    _ = _:=by
      rw [show 7*ε-(1:ℝ)/40=6*ε+(-((1:ℝ)/40))+ε by ring,
        Real.rpow_add hZ0,Real.rpow_add hZ0]
      ring


end CanonicalRowCompletion

namespace CanonicalRowCompletion
open SecondPassArithmetic
theorem cubeLogRange_sq_small_power (b ε : ℝ) (_hb : 0≤b) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀X Z : ℝ,0≤X → 1≤Z → X≤Z^3 →
      ((cubeLogRange b X).card:ℝ)^2≤C*Z^ε := by
  let B:=max 1 b
  let deltaLoss:=ε/2
  let C₀:=1+Real.log B+3/deltaLoss
  have hB : 1≤B:=le_max_left _ _
  have hB0 : 0<B:=zero_lt_one.trans_le hB
  have hδ : 0<deltaLoss:=by dsimp [deltaLoss];positivity
  have hlogB : 0≤Real.log B:=Real.log_nonneg hB
  have hC₀ : 0<C₀:=by dsimp [C₀];positivity
  refine ⟨C₀^2,by positivity,?_⟩
  intro X Z hX hZ hXZ
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hZ3 : 1≤Z^3:=one_le_pow₀ hZ
  have hY : 1≤B*Z^3:=one_le_mul_of_one_le_of_one_le hB hZ3
  have hxY : max 1 (b*X)≤B*Z^3 := by
    apply max_le hY
    calc
      b*X ≤ B*X:=mul_le_mul_of_nonneg_right (le_max_right _ _) hX
      _ ≤ B*Z^3:=mul_le_mul_of_nonneg_left hXZ hB0.le
  have hcard : ((cubeLogRange b X).card:ℝ)≤1+Real.log B+3*Real.log Z := by
    rw [cubeLogRange_card,Nat.cast_add,Nat.cast_one]
    have hlog:=normLogBin_le_log_upper (max 1 (b*X)) (B*Z^3)
      (zero_le_one.trans (le_max_left _ _)) hxY hY
    rw [Real.log_mul hB0.ne' (pow_pos hZ0 3).ne',Real.log_pow] at hlog
    norm_num at hlog
    linarith
  have hr : 1≤Z^deltaLoss:=Real.one_le_rpow hZ hδ.le
  have hl : Real.log Z≤Z^deltaLoss/deltaLoss:=Real.log_le_rpow_div hZ0.le hδ
  have hc : 1+Real.log B+3*Real.log Z≤C₀*Z^deltaLoss := by
    calc
      _ ≤ (1+Real.log B)*Z^deltaLoss+3*(Z^deltaLoss/deltaLoss) := by
        gcongr
        exact le_mul_of_one_le_right (by linarith) hr
      _ = _:=by dsimp [C₀];ring
  calc
    _ ≤ (C₀*Z^deltaLoss)^2:=pow_le_pow_left₀ (Nat.cast_nonneg _) (hcard.trans hc) 2
    _ = C₀^2*Z^ε:=by
      rw [mul_pow,←Real.rpow_natCast (Z^deltaLoss) 2,←Real.rpow_mul hZ0.le]
      congr 1
      dsimp [deltaLoss]
      congr 1
      ring

end CanonicalRowCompletion

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
