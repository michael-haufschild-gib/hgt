/-
Good mask row data adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.CoprimalityMasksAndSexticRows

/-!
# Good mask row data

Good mask row data `GoodMaskRowData`, free prime indices and the sextic reciprocity phase. The
quadratic supplement at the ramified prime; unit and ramified numerator factors have a fixed
modulus; the canonical completed reflection.
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
open Eisenstein SchwartzPlanePoisson QuadraticPhase.Eisenstein
open scoped BigOperators Classical

/-- Two distinct prime rows are the two singleton rows of the common-family reciprocity law. -/
theorem quadratic_prime_reciprocity (p q : O) (hp : p≠0) (hq : q≠0)
    [(Ideal.span {p}).IsMaximal] [(Ideal.span {q}).IsMaximal]
    (hoddp : ringChar (O⧸Ideal.span {p})≠2) (hoddq : ringChar (O⧸Ideal.span {q})≠2)
    (hne : (Ideal.span {p}:Ideal O)≠Ideal.span {q}) :
    complexQuadraticChar (Ideal.span {p}) (Ideal.Quotient.mk (Ideal.span {p}) q)=
      FixedRayArithmetic.quadraticPhase p q*
        complexQuadraticChar (Ideal.span {q}) (Ideal.Quotient.mk (Ideal.span {q}) p) := by
  let r : Bool→O := fun b => cond b q p
  let : ∀b,(Ideal.span {r b}).IsMaximal := by intro b;cases b <;> dsimp [r] <;> infer_instance
  have hr : ∀b,r b≠0 := by intro b;cases b <;> assumption
  have ho : ∀b,ringChar (O⧸Ideal.span {r b})≠2 := by intro b;cases b <;> assumption
  have hi : Function.Injective (fun b => (Ideal.span {r b}:Ideal O)) := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exact False.elim (hne h)
    · exact False.elim (hne h.symm)
    · rfl
  have he := quadraticSubsetSymbol_reciprocity r hr hi ho {false} {true}
  simp only [quadraticSubsetSymbol,primeSubsetRow,Finset.prod_singleton] at he
  dsimp only [r,cond] at he
  exact he

namespace FixedRayArithmetic

lemma quadraticPhase_one (a : O) (ha : a∉Ideal.span {(2:O)}) : quadraticPhase a 1=1 := by
  rw [quadraticPhase,mul_one,fixedDualAverage_one,mul_one,div_self (gamma_ne_zero ha)]

lemma quadraticPhase_mul_right {a b c : O} (ha : a∉Ideal.span {(2:O)})
    (hb : b∉Ideal.span {(2:O)}) (hc : c∉Ideal.span {(2:O)}) :
    quadraticPhase a (b*c)=quadraticPhase a b*quadraticPhase a c := by
  rw [quadraticPhase_comm a (b*c),quadraticPhase_mul_left hb hc ha,
    quadraticPhase_comm b a,quadraticPhase_comm c a]

lemma quadraticPhase_norm {a b : O} (ha : a∉Ideal.span {(2:O)})
    (hb : b∉Ideal.span {(2:O)}) : ‖quadraticPhase a b‖=1 := by
  have h := congrArg norm (quadraticPhase_sq ha hb)
  rw [norm_pow,norm_one] at h
  nlinarith only [h,norm_nonneg (quadraticPhase a b)]

lemma quadraticPhase_congr_right (a x y : O) (hxy : (4:O)∣x-y) :
    quadraticPhase a x=quadraticPhase a y := by
  have h : Ideal.Quotient.mk (Ideal.span {(4:O)}) x=Ideal.Quotient.mk (Ideal.span {(4:O)}) y :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hxy)
  have hh : Ideal.Quotient.mk (Ideal.span {(4:O)}) (a*x)=Ideal.Quotient.mk (Ideal.span {(4:O)}) (a*y) := by
    rw [map_mul,map_mul,h]
  rw [quadraticPhase,quadraticPhase,fixedDualAverage_eq_of_mod_four x y h,
    fixedDualAverage_eq_of_mod_four (a*x) (a*y) hh]

lemma lambda_odd : lambda∉Ideal.span {(2:O)} := by
  simpa only [cubicTwoIdeal,Ideal.span_singleton_neg] using cubicTwoIdeal_good

lemma lambda_residue_odd : ringChar (O⧸Ideal.span {lambda})≠2 := by
  change ringChar (O⧸ramifiedIdeal)≠2
  intro h
  have he := (prime_ideal_char_two_iff ramifiedIdeal ramifiedIdeal_prime).mp h
  apply cubicTwoIdeal_good
  rw [←he]
  exact Ideal.mem_span_singleton_self lambda

theorem quadratic_lambda_primary (p : O) (hp : p≠0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (hc : ringChar (O⧸Ideal.span {p})≠2)
    (hprimary : lambda^2∣p-1) :
    complexQuadraticChar (Ideal.span {p}) (Ideal.Quotient.mk (Ideal.span {p}) lambda)=
      quadraticPhase lambda p := by
  let : (Ideal.span {lambda}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible residue_lambda_prime.irreducible
  have hne : (Ideal.span {p}:Ideal O)≠Ideal.span {lambda} := by
    intro h
    apply hg
    rw [h]
    exact Ideal.mem_span_singleton_self lambda
  have he := quadratic_prime_reciprocity p lambda hp residue_lambda_prime.ne_zero hc lambda_residue_odd hne
  have hres : Ideal.Quotient.mk (Ideal.span {lambda}) p=1 := by
    rw [←map_one (Ideal.Quotient.mk (Ideal.span {lambda}))]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
      ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hprimary))
  rw [hres,map_one,mul_one,quadraticPhase_comm p lambda] at he
  exact he

end FixedRayArithmetic
end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CubicJacobi CubicRamified UniqueFactorizationMonoid
open FixedRayArithmetic
open scoped BigOperators Classical

lemma localRowValue_square (x : O) (P : Ideal O) :
    localRowValue x P^2=ringComplex (primeValue P x) := by
  unfold localRowValue primeValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    change (complexSexticChar P h.2 (Ideal.Quotient.mk P x))^2=_
    rw [←MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),(complexSexticChar_powers P h.2).1]
    rfl
  · simp

theorem idealRowHom_square (x : O) (I : Ideal O) :
    idealRowHom x I ^ 2=ringComplex (idealSymbol I x) := by
  have hm (s : Multiset (Ideal O)) :
      (s.map (localRowValue x)).prod^2=ringComplex ((s.map (fun P => primeValue P x)).prod) := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,mul_pow,map_mul,localRowValue_square,ih]
  by_cases hI : I=0
  · subst I
    simp only [map_zero,idealSymbol_zero,zero_pow (by decide : (2:ℕ)≠0)]
  · change (if I=0 then 0 else _)^2=ringComplex (if I=0 then 0 else _)
    simp only [if_neg hI]
    exact hm _

lemma two_dvd_mul_iff (x y : O) : (2:O)∣x*y ↔ (2:O)∣x ∨ (2:O)∣y := by
  simpa only [neg_dvd] using negative_two_prime.dvd_mul (a:=x) (b:=y)

/-- The quadratic supplement at the ramified prime, extended by zero on even elements. -/
def lambdaQuadraticCharacter : O→*ℂ where
  toFun n := if (2:O)∣n then 0 else quadraticPhase lambda n
  map_one' := by
    have h2 : ¬(2:O)∣1 := by
      intro h
      exact negative_two_prime.2.1 (isUnit_of_dvd_one (by simpa only [neg_dvd] using h))
    rw [if_neg h2,quadraticPhase_one lambda lambda_odd]
  map_mul' x y := by
    rw [two_dvd_mul_iff]
    by_cases hx : (2:O)∣x <;> by_cases hy : (2:O)∣y
    · simp only [hx,hy,true_or,if_true,zero_mul]
    · simp only [hx,hy,true_or,if_true,if_false,zero_mul]
    · simp only [hx,hy,or_true,if_true,if_false,mul_zero]
    · simp only [hx,hy,false_or,if_false]
      exact quadraticPhase_mul_right lambda_odd
        (fun h => hx (Ideal.mem_span_singleton.mp h))
        (fun h => hy (Ideal.mem_span_singleton.mp h))

lemma lambdaQuadraticCharacter_periodic (x y : O) (hxy : (4:O)∣x-y) :
    lambdaQuadraticCharacter x=lambdaQuadraticCharacter y := by
  have h2 : (2:O)∣x-y := (show (2:O)∣4 from ⟨2,by norm_num⟩).trans hxy
  have hd : (2:O)∣x ↔ (2:O)∣y := by
    constructor
    · intro hx
      convert dvd_sub hx h2 using 1 <;> ring
    · intro hy
      convert dvd_add h2 hy using 1 <;> ring
  change (if (2:O)∣x then 0 else _)=(if (2:O)∣y then 0 else _)
  rw [hd,quadraticPhase_congr_right lambda x y hxy]

lemma lambdaQuadraticCharacter_sq (n : O) (hn : ¬(2:O)∣n) :
    lambdaQuadraticCharacter n^2=1 := by
  change (if (2:O)∣n then (0:ℂ) else quadraticPhase lambda n)^2=1
  rw [if_neg hn]
  exact quadraticPhase_sq lambda_odd (fun h => hn (Ideal.mem_span_singleton.mp h))

lemma idealRowHom_lambda_prime_cube (p : O) (hp : Prime p) (hprimary : lambda^2∣p-1)
    (hs : quadraticSupported (Ideal.span {p})) :
    idealRowHom lambda (Ideal.span {p})^3=lambdaQuadraticCharacter p := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmem : Ideal.span {p}∈normalizedFactors (Ideal.span {p}) :=
    (Ideal.mem_normalizedFactors_iff (primaryIdealGenerator_ne_zero_ideal _ hs.1)).mpr ⟨inferInstance,le_rfl⟩
  have hd := supported_factors_good _ hs _ hmem
  rw [idealRowHom_prime lambda _ hd.2.1,
    ←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),(complexSexticChar_powers _ _).2.1,
    quadratic_lambda_primary p hp.ne_zero hd.2.1 hd.2.2 hprimary]
  change quadraticPhase lambda p=(if (2:O)∣p then 0 else quadraticPhase lambda p)
  rw [if_neg ((supported_span_iff p).mp hs).2]

theorem idealRowHom_lambda_cube (n : O) (hn : lambda^2∣n-1)
    (hs : quadraticSupported (Ideal.span {n})) :
    idealRowHom lambda (Ideal.span {n})^3=lambdaQuadraticCharacter n := by
  have hn0 : n≠0 := by
    intro h
    exact primaryIdealGenerator_ne_zero_ideal _ hs.1 (by simp [h])
  obtain ⟨s,hprod,hfactors⟩ := exists_primary_prime_factorization n hn0 hn
  rw [←hprod] at hs ⊢
  clear hprod hn hn0 n
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,one_pow]
  | @cons p s ih =>
    have hp := hfactors p (Multiset.mem_cons_self _ _)
    have htail : ∀q∈s,Prime q ∧ lambda^2∣q-1 := fun q hq => hfactors q (Multiset.mem_cons_of_mem hq)
    have hsplit : quadraticSupported (Ideal.span {p}) ∧ quadraticSupported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,quadraticSupported_mul] using hs
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,mul_pow,
      idealRowHom_lambda_prime_cube p hp.1 hp.2 hsplit.1,ih hsplit.2 htail,map_mul]

theorem idealRowHom_lambda_formula (n : O) (hn : lambda^2∣n-1)
    (hs : quadraticSupported (Ideal.span {n})) :
    idealRowHom lambda (Ideal.span {n})=
      ringComplex (linearRay 1 0 n)^2*lambdaQuadraticCharacter n := by
  have htwo := idealRowHom_square lambda (Ideal.span {n})
  change idealRowHom lambda (Ideal.span {n})^2=ringComplex (symbol lambda n) at htwo
  rw [symbol_lambda_eq_linearRay n hn] at htwo
  have hthree := idealRowHom_lambda_cube n hn hs
  have hq := lambdaQuadraticCharacter_sq n ((supported_span_iff n).mp hs).2
  have hsix : idealRowHom lambda (Ideal.span {n})^6=1 := by
    calc
      _ = (idealRowHom lambda (Ideal.span {n})^3)^2 := by ring
      _ = 1 := by rw [hthree,hq]
  calc
    _ = idealRowHom lambda (Ideal.span {n})*idealRowHom lambda (Ideal.span {n})^6 := by rw [hsix,mul_one]
    _ = (idealRowHom lambda (Ideal.span {n})^2)^2*idealRowHom lambda (Ideal.span {n})^3 := by ring
    _ = _ := by rw [htwo,hthree]

theorem idealRowHom_lambda_mod_thirty_six (x y : O)
    (hx : lambda^2∣x-1) (hy : lambda^2∣y-1)
    (hsx : quadraticSupported (Ideal.span {x})) (hsy : quadraticSupported (Ideal.span {y}))
    (hxy : (36:O)∣x-y) :
    idealRowHom lambda (Ideal.span {x})=idealRowHom lambda (Ideal.span {y}) := by
  rw [idealRowHom_lambda_formula x hx hsx,idealRowHom_lambda_formula y hy hsy,
    linearRay_congr_mod_nine 1 0 x y hx hy ((show (9:O)∣36 from ⟨4,by norm_num⟩).trans hxy),
    lambdaQuadraticCharacter_periodic x y ((show (4:O)∣36 from ⟨9,by norm_num⟩).trans hxy)]

lemma exists_supported_primary_unit (x : O) (hx : quadraticSupported (Ideal.span {x})) :
    ∃u : Oˣ,lambda^2∣(u:O)*x-1 := by
  have hp := primaryIdealGenerator_spec (Ideal.span {x}) hx.1
  have ha : Associated x (primaryIdealGenerator (Ideal.span {x})) :=
    Ideal.span_singleton_eq_span_singleton.mp hp.1.symm
  obtain ⟨u,hu⟩ := ha
  refine ⟨u,?_⟩
  have he : (u:O)*x=primaryIdealGenerator (Ideal.span {x}) := by simpa only [mul_comm] using hu
  rw [he]
  exact hp.2

theorem supportedIdealRow_lambda_periodic (x y : O)
    (hxy : x-y∈Ideal.span {(36:O)}) : supportedIdealRow lambda x=supportedIdealRow lambda y := by
  have hs := supported_span_congruent_mod_thirty_six x y hxy
  change (if quadraticSupported (Ideal.span {x}) then _ else 0)=
    (if quadraticSupported (Ideal.span {y}) then _ else 0)
  by_cases hx : quadraticSupported (Ideal.span {x})
  · have hy := hs.mp hx
    rw [if_pos hx,if_pos hy]
    obtain ⟨u,hux⟩ := exists_supported_primary_unit x hx
    have h36 : (36:O)∣(u:O)*x-(u:O)*y := by
      convert dvd_mul_of_dvd_right (Ideal.mem_span_singleton.mp hxy) (u:O) using 1 <;> ring
    have hl : lambda^2∣(u:O)*x-(u:O)*y :=
      lambda_sq_dvd_three.trans ((show (3:O)∣36 from ⟨12,by norm_num⟩).trans h36)
    have huy : lambda^2∣(u:O)*y-1 := by
      convert dvd_sub hux hl using 1 <;> ring
    have hsp (z : O) : Ideal.span {(u:O)*z}=Ideal.span {z} :=
      Ideal.span_singleton_mul_left_unit u.isUnit z
    have he := idealRowHom_lambda_mod_thirty_six ((u:O)*x) ((u:O)*y) hux huy
      (by rwa [hsp]) (by rwa [hsp]) h36
    simpa only [hsp] using he
  · rw [if_neg hx,if_neg (fun hy => hx (hs.mpr hy))]

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped BigOperators Classical

def cubicTwoSupplement : O→*ℂ :=
  (complexCubicChar cubicTwoIdeal cubicTwoIdeal_good).toMonoidHom.comp
    (Ideal.Quotient.mk cubicTwoIdeal).toMonoidHom

def quadraticTwoSupplement : O→*ℂ where
  toFun n := (ZMod.χ₈ (Ideal.absNorm (Ideal.span {n}):ZMod 8):ℂ)
  map_one' := by simp
  map_mul' x y := by
    rw [←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,map_mul,Int.cast_mul]

def twoSupplement : O→*ℂ := cubicTwoSupplement^2*quadraticTwoSupplement

lemma cubicTwoSupplement_norm (n : O) : ‖cubicTwoSupplement n‖≤1 :=
  FiniteRayExpansion.norm_char_le_one (complexCubicChar cubicTwoIdeal cubicTwoIdeal_good) _

lemma quadraticTwoSupplement_norm (n : O) : ‖quadraticTwoSupplement n‖≤1 :=
  FiniteRayExpansion.norm_char_le_one (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)) _

lemma twoSupplement_norm (n : O) : ‖twoSupplement n‖≤1 := by
  change ‖cubicTwoSupplement n^2*quadraticTwoSupplement n‖≤1
  rw [norm_mul,norm_pow]
  apply (mul_le_of_le_one_left (norm_nonneg _) _).trans (quadraticTwoSupplement_norm n)
  exact pow_le_one₀ (norm_nonneg _) (cubicTwoSupplement_norm n)

lemma cubicTwoSupplement_periodic (x y : O) (hxy : x-y∈Ideal.span {(8:O)}) :
    cubicTwoSupplement x=cubicTwoSupplement y := by
  have h2 : x-y∈cubicTwoIdeal := by
    obtain ⟨k,hk⟩ := Ideal.mem_span_singleton.mp hxy
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-4*k,?_⟩
    change x-y=(-2:O)*(-4*k)
    rw [hk]
    ring
  change complexCubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal x)=
    complexCubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal y)
  rw [Ideal.Quotient.eq.mpr h2]

lemma twoSupplement_periodic (x y : O) (hxy : x-y∈Ideal.span {(8:O)}) :
    twoSupplement x=twoSupplement y := by
  change cubicTwoSupplement x^2*quadraticTwoSupplement x=
    cubicTwoSupplement y^2*quadraticTwoSupplement y
  rw [cubicTwoSupplement_periodic x y hxy]
  congr 1
  change (ZMod.χ₈ (Ideal.absNorm (Ideal.span {x}):ZMod 8):ℂ)=
    (ZMod.χ₈ (Ideal.absNorm (Ideal.span {y}):ZMod 8):ℂ)
  have he : (Ideal.absNorm (Ideal.span {x}):ZMod 8)=(Ideal.absNorm (Ideal.span {y}):ZMod 8) :=
    (ZMod.natCast_eq_natCast_iff' _ _ 8).mpr (norm_residue_congruent 8 x y hxy)
  rw [he]

lemma idealRowHom_two_prime (p : O) (hp : Prime p) (hprimary : lambda^2∣p-1)
    (hs : quadraticSupported (Ideal.span {p})) :
    idealRowHom (2:O) (Ideal.span {p})=twoSupplement p := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmem : Ideal.span {p}∈normalizedFactors (Ideal.span {p}) :=
    (Ideal.mem_normalizedFactors_iff (primaryIdealGenerator_ne_zero_ideal _ hs.1)).mpr ⟨inferInstance,le_rfl⟩
  have hd := supported_factors_good _ hs _ hmem
  have hgen : primaryGenerator (Ideal.span {p}) hd.2.1=p := by
    have hspec := primaryGenerator_spec (Ideal.span {p}) hd.2.1
    exact primary_associated_eq _ _ (Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm)
      hspec.2 hprimary
  have h2 : idealRowHom (2:O) (Ideal.span {p})^2=cubicTwoSupplement p := by
    rw [idealRowHom_prime _ _ hd.2.1]
    have he := complexSextic_four_eq_fixed_two (Ideal.span {p}) hd.2.1 hd.2.2
    have hfour : (4:O⧸Ideal.span {p})=(Ideal.Quotient.mk (Ideal.span {p}) (2:O))^2 := by
      norm_num [map_ofNat]
    rw [hfour,map_pow,hgen] at he
    exact he
  have h3 : idealRowHom (2:O) (Ideal.span {p})^3=quadraticTwoSupplement p := by
    rw [idealRowHom_prime _ _ hd.2.1,
      ←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),(complexSexticChar_powers _ _).2.1]
    change (quadraticChar (O⧸Ideal.span {p}) (Ideal.Quotient.mk _ (2:O)):ℂ)=_
    simp only [map_ofNat]
    rw [quadraticChar_two hd.2.2]
    have hn : Ideal.absNorm (Ideal.span {p})=Fintype.card (O⧸Ideal.span {p}) := by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    change (ZMod.χ₈ (Fintype.card (O⧸Ideal.span {p})):ℂ)=
      (ZMod.χ₈ (Ideal.absNorm (Ideal.span {p})):ℂ)
    rw [hn]
  have h6 : idealRowHom (2:O) (Ideal.span {p})^6=1 := by
    rw [idealRowHom_prime _ _ hd.2.1,
      ←MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),(complexSexticChar_powers _ _).2.2]
    have hne : Ideal.Quotient.mk (Ideal.span {p}) (2:O)≠0 := by
      simpa only [map_ofNat] using Ring.two_ne_zero hd.2.2
    exact MulChar.one_apply_coe (Units.mk0 _ hne)
  calc
    _ = idealRowHom (2:O) (Ideal.span {p})*idealRowHom (2:O) (Ideal.span {p})^6 := by rw [h6,mul_one]
    _ = idealRowHom (2:O) (Ideal.span {p})^3*(idealRowHom (2:O) (Ideal.span {p})^2)^2 := by ring
    _ = twoSupplement p := by
      rw [h2,h3]
      change quadraticTwoSupplement p*cubicTwoSupplement p^2=cubicTwoSupplement p^2*quadraticTwoSupplement p
      ring

theorem idealRowHom_two_formula (n : O) (hn : lambda^2∣n-1)
    (hs : quadraticSupported (Ideal.span {n})) : idealRowHom (2:O) (Ideal.span {n})=twoSupplement n := by
  have hn0 : n≠0 := by
    intro h
    exact primaryIdealGenerator_ne_zero_ideal _ hs.1 (by simp [h])
  obtain ⟨s,hprod,hfactors⟩ := exists_primary_prime_factorization n hn0 hn
  rw [←hprod] at hs ⊢
  clear hprod hn hn0 n
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one]
  | @cons p s ih =>
    have hp := hfactors p (Multiset.mem_cons_self _ _)
    have htail : ∀q∈s,Prime q ∧ lambda^2∣q-1 := fun q hq => hfactors q (Multiset.mem_cons_of_mem hq)
    have hsplit : quadraticSupported (Ideal.span {p}) ∧ quadraticSupported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,quadraticSupported_mul] using hs
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,
      idealRowHom_two_prime p hp.1 hp.2 hsplit.1,ih hsplit.2 htail,map_mul]

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CubicJacobi UniqueFactorizationMonoid
open FixedRayArithmetic
open scoped BigOperators Classical

def sexticReciprocityPhase (a b : O) : ℂ :=
  if (2:O)∣a ∨ (2:O)∣b then 0 else quadraticPhase a b

lemma sexticReciprocityPhase_good (a b : O) (ha : ¬(2:O)∣a) (hb : ¬(2:O)∣b) :
    sexticReciprocityPhase a b=quadraticPhase a b := by
  rw [sexticReciprocityPhase,if_neg (not_or.mpr ⟨ha,hb⟩)]

lemma sexticReciprocityPhase_comm (a b : O) :
    sexticReciprocityPhase a b=sexticReciprocityPhase b a := by
  simp only [sexticReciprocityPhase,or_comm,quadraticPhase_comm a b]

lemma sexticReciprocityPhase_mul_left (a b c : O) :
    sexticReciprocityPhase (a*b) c=sexticReciprocityPhase a c*sexticReciprocityPhase b c := by
  unfold sexticReciprocityPhase
  rw [two_dvd_mul_iff]
  by_cases ha : (2:O)∣a <;> by_cases hb : (2:O)∣b <;> by_cases hc : (2:O)∣c
  all_goals simp only [ha,hb,hc,true_or,or_true,false_or,if_true,if_false,mul_zero,zero_mul]
  exact quadraticPhase_mul_left (fun h => ha (Ideal.mem_span_singleton.mp h))
    (fun h => hb (Ideal.mem_span_singleton.mp h)) (fun h => hc (Ideal.mem_span_singleton.mp h))

lemma sexticReciprocityPhase_mul_right (a b c : O) :
    sexticReciprocityPhase a (b*c)=sexticReciprocityPhase a b*sexticReciprocityPhase a c := by
  rw [sexticReciprocityPhase_comm a (b*c),sexticReciprocityPhase_mul_left,
    sexticReciprocityPhase_comm b a,sexticReciprocityPhase_comm c a]

lemma sexticReciprocityPhase_one_right (a : O) (ha : quadraticSupported (Ideal.span {a})) :
    sexticReciprocityPhase a 1=1 := by
  have h2 : ¬(2:O)∣1 := by
    intro h
    exact negative_two_prime.2.1 (isUnit_of_dvd_one (by simpa only [neg_dvd] using h))
  rw [sexticReciprocityPhase_good a 1 ((supported_span_iff a).mp ha).2 h2]
  exact quadraticPhase_one a (fun h => ((supported_span_iff a).mp ha).2 (Ideal.mem_span_singleton.mp h))

lemma sexticReciprocityPhase_one_left (a : O) (ha : quadraticSupported (Ideal.span {a})) :
    sexticReciprocityPhase 1 a=1 := by
  rw [sexticReciprocityPhase_comm,sexticReciprocityPhase_one_right a ha]

lemma sexticReciprocityPhase_norm (a b : O) : ‖sexticReciprocityPhase a b‖≤1 := by
  unfold sexticReciprocityPhase
  split_ifs with h
  · simp
  · obtain ⟨ha,hb⟩ := not_or.mp h
    rw [quadraticPhase_norm (fun h => ha (Ideal.mem_span_singleton.mp h))
      (fun h => hb (Ideal.mem_span_singleton.mp h))]

lemma sexticReciprocityPhase_congr_right (a x y : O) (hxy : (4:O)∣x-y) :
    sexticReciprocityPhase a x=sexticReciprocityPhase a y := by
  have h2 : (2:O)∣x-y := (show (2:O)∣4 from ⟨2,by norm_num⟩).trans hxy
  have hd : (2:O)∣x ↔ (2:O)∣y := by
    constructor
    · intro hx
      convert dvd_sub hx h2 using 1 <;> ring
    · intro hy
      convert dvd_add h2 hy using 1 <;> ring
  simp only [sexticReciprocityPhase,hd,quadraticPhase_congr_right a x y hxy]

lemma supported_prime_data (p : O) (hp : Prime p) (hs : quadraticSupported (Ideal.span {p})) :
    lambda∉(Ideal.span {p}:Ideal O) ∧ ringChar (O⧸Ideal.span {p})≠2 := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  exact (supported_factors_good _ hs _
    ((Ideal.mem_normalizedFactors_iff (primaryIdealGenerator_ne_zero_ideal _ hs.1)).mpr
      ⟨inferInstance,le_rfl⟩)).2

theorem idealRowHom_prime_reciprocity (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : lambda^2∣p-1) (hprimaryQ : lambda^2∣q-1)
    (hsP : quadraticSupported (Ideal.span {p})) (hsQ : quadraticSupported (Ideal.span {q})) :
    idealRowHom q (Ideal.span {p})=sexticReciprocityPhase p q*idealRowHom p (Ideal.span {q}) := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let : (Ideal.span {q}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hq.irreducible
  obtain ⟨hgP,hcP⟩ := supported_prime_data p hp hsP
  obtain ⟨hgQ,hcQ⟩ := supported_prime_data q hq hsQ
  by_cases he : (Ideal.span {p}:Ideal O)=Ideal.span {q}
  · have hqp : q∈(Ideal.span {p}:Ideal O) := by rw [he];exact Ideal.mem_span_singleton_self q
    have hpq : p∈(Ideal.span {q}:Ideal O) := by rw [←he];exact Ideal.mem_span_singleton_self p
    rw [idealRowHom_prime q _ hgP,idealRowHom_prime p _ hgQ,
      Ideal.Quotient.eq_zero_iff_mem.mpr hqp,Ideal.Quotient.eq_zero_iff_mem.mpr hpq]
    simp only [MulChar.map_zero,mul_zero]
  · have hcop : IsCoprime (Ideal.span {p}:Ideal O) (Ideal.span {q}) := Ideal.isCoprime_of_isMaximal he
    have hqp : q∉(Ideal.span {p}:Ideal O) := (prime_coprime_span_iff _ q).mp hcop
    have hpq : p∉(Ideal.span {q}:Ideal O) := (prime_coprime_span_iff _ p).mp hcop.symm
    have h2 : idealRowHom q (Ideal.span {p})^2=idealRowHom p (Ideal.span {q})^2 := by
      rw [idealRowHom_square,idealRowHom_square]
      exact congrArg ringComplex (symbol_reciprocity q p hprimaryQ hprimaryP)
    have ha6 : idealRowHom q (Ideal.span {p})^6=1 := by
      rw [←idealRowHom_argument_pow q 6 _ hsP.1,idealRowHom_prime_sixth_mask q _ hgP,if_pos hcop]
    have hb6 : idealRowHom p (Ideal.span {q})^6=1 := by
      rw [←idealRowHom_argument_pow p 6 _ hsQ.1,idealRowHom_prime_sixth_mask p _ hgQ,if_pos hcop.symm]
    have h3 : idealRowHom q (Ideal.span {p})^3=
        sexticReciprocityPhase p q*idealRowHom p (Ideal.span {q})^3 := by
      rw [idealRowHom_prime q _ hgP,idealRowHom_prime p _ hgQ,
        ←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),
        ←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),
        (complexSexticChar_powers _ _).2.1,(complexSexticChar_powers _ _).2.1,
        sexticReciprocityPhase_good p q ((supported_span_iff p).mp hsP).2 ((supported_span_iff q).mp hsQ).2]
      exact quadratic_prime_reciprocity p q hp.ne_zero hq.ne_zero hcP hcQ he
    calc
      _ = idealRowHom q (Ideal.span {p})*idealRowHom q (Ideal.span {p})^6 := by rw [ha6,mul_one]
      _ = idealRowHom q (Ideal.span {p})^3*(idealRowHom q (Ideal.span {p})^2)^2 := by ring
      _ = (sexticReciprocityPhase p q*idealRowHom p (Ideal.span {q})^3)*
          (idealRowHom p (Ideal.span {q})^2)^2 := by rw [h3,h2]
      _ = sexticReciprocityPhase p q*(idealRowHom p (Ideal.span {q})*idealRowHom p (Ideal.span {q})^6) := by ring
      _ = _ := by rw [hb6,mul_one]

lemma idealRowHom_prime_primary_reciprocity (p b : O) (hp : Prime p)
    (hprimaryP : lambda^2∣p-1) (hprimaryB : lambda^2∣b-1)
    (hsP : quadraticSupported (Ideal.span {p})) (hsB : quadraticSupported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {p})=sexticReciprocityPhase p b*idealRowHom p (Ideal.span {b}) := by
  have hb0 : b≠0 := by intro h;exact primaryIdealGenerator_ne_zero_ideal _ hsB.1 (by simp [h])
  obtain ⟨s,hprod,hfactors⟩ := exists_primary_prime_factorization b hb0 hprimaryB
  rw [←hprod] at hsB ⊢
  clear hprod hb0 hprimaryB b
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,
      idealRowHom_one_good _ hsP.1,sexticReciprocityPhase_one_right p hsP,mul_one]
  | @cons q s ih =>
    have hq := hfactors q (Multiset.mem_cons_self _ _)
    have htail : ∀r∈s,Prime r ∧ lambda^2∣r-1 := fun r hr => hfactors r (Multiset.mem_cons_of_mem hr)
    have hsplit : quadraticSupported (Ideal.span {q}) ∧ quadraticSupported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,quadraticSupported_mul] using hsB
    rw [Multiset.prod_cons,idealRowHom_argument_mul,←Ideal.span_singleton_mul_span_singleton,
      map_mul,sexticReciprocityPhase_mul_right,
      idealRowHom_prime_reciprocity p q hp hq.1 hprimaryP hq.2 hsP hsplit.1,ih hsplit.2 htail]
    ring

theorem idealRowHom_primary_reciprocity (a b : O)
    (hprimaryA : lambda^2∣a-1) (hprimaryB : lambda^2∣b-1)
    (hsA : quadraticSupported (Ideal.span {a})) (hsB : quadraticSupported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {a})=sexticReciprocityPhase a b*idealRowHom a (Ideal.span {b}) := by
  have ha0 : a≠0 := by intro h;exact primaryIdealGenerator_ne_zero_ideal _ hsA.1 (by simp [h])
  obtain ⟨s,hprod,hfactors⟩ := exists_primary_prime_factorization a ha0 hprimaryA
  rw [←hprod] at hsA ⊢
  clear hprod ha0 hprimaryA a
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,
      idealRowHom_one_good _ hsB.1,sexticReciprocityPhase_one_left b hsB,one_mul]
  | @cons p s ih =>
    have hp := hfactors p (Multiset.mem_cons_self _ _)
    have htail : ∀r∈s,Prime r ∧ lambda^2∣r-1 := fun r hr => hfactors r (Multiset.mem_cons_of_mem hr)
    have hsplit : quadraticSupported (Ideal.span {p}) ∧ quadraticSupported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,quadraticSupported_mul] using hsA
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,
      idealRowHom_argument_mul,sexticReciprocityPhase_mul_left,
      idealRowHom_prime_primary_reciprocity p b hp.1 hp.2 hprimaryB hsplit.1 hsB,ih hsplit.2 htail]
    ring

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

def reciprocityPhaseMonoid (r : O) (hr : quadraticSupported (Ideal.span {r})) : O→*ℂ where
  toFun n := sexticReciprocityPhase r n
  map_one' := sexticReciprocityPhase_one_right r hr
  map_mul' := sexticReciprocityPhase_mul_right r

/-- The unit and ramified numerator factors have a fixed modulus, independent of the row. -/
def numeratorBadTwist (u : Oˣ) (a b : ℕ) (r : O)
    (hr : quadraticSupported (Ideal.span {r})) : O→*ℂ :=
  unitSupplement u * supportedIdealRow lambda^a * twoSupplement^b * reciprocityPhaseMonoid r hr

lemma numeratorBadTwist_norm (u : Oˣ) (a b : ℕ) (r : O)
    (hr : quadraticSupported (Ideal.span {r})) (n : O) :
    ‖numeratorBadTwist u a b r hr n‖≤1 := by
  change ‖((unitSupplement u n*(supportedIdealRow lambda n)^a)*(twoSupplement n)^b)*
    sexticReciprocityPhase r n‖≤1
  simp only [norm_mul,norm_pow]
  have hu := unitSupplement_norm u n
  have ha : ‖supportedIdealRow lambda n‖^a≤1 :=
    pow_le_one₀ (norm_nonneg _) (supportedIdealRow_norm lambda n)
  have hb : ‖twoSupplement n‖^b≤1 :=
    pow_le_one₀ (norm_nonneg _) (twoSupplement_norm n)
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _)
    ((mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) hu).trans ha)).trans hb)).trans
      (sexticReciprocityPhase_norm r n)

theorem numeratorBadTwist_periodic (u : Oˣ) (a b : ℕ) (r : O)
    (hr : quadraticSupported (Ideal.span {r})) (x y : O)
    (hxy : x-y∈Ideal.span {(72:O)}) :
    numeratorBadTwist u a b r hr x=numeratorBadTwist u a b r hr y := by
  have h72 : (72:O)∣x-y := Ideal.mem_span_singleton.mp hxy
  have h36 : x-y∈(Ideal.span {(36:O)}:Ideal O) :=
    Ideal.mem_span_singleton.mpr ((show (36:O)∣72 from ⟨2,by norm_num⟩).trans h72)
  have h8 : x-y∈(Ideal.span {(8:O)}:Ideal O) :=
    Ideal.mem_span_singleton.mpr ((show (8:O)∣72 from ⟨9,by norm_num⟩).trans h72)
  have h4 : (4:O)∣x-y := (show (4:O)∣72 from ⟨18,by norm_num⟩).trans h72
  change ((unitSupplement u x*(supportedIdealRow lambda x)^a)*(twoSupplement x)^b)*
      sexticReciprocityPhase r x=
    ((unitSupplement u y*(supportedIdealRow lambda y)^a)*(twoSupplement y)^b)*
      sexticReciprocityPhase r y
  rw [unitSupplement_periodic u x y h36,supportedIdealRow_lambda_periodic x y h36,
    twoSupplement_periodic x y h8,sexticReciprocityPhase_congr_right r x y h4]

def movingNumeratorRow (r : O) (hr : quadraticSupported (Ideal.span {r})) : O→*ℂ where
  toFun n := idealRowHom n (Ideal.span {r})
  map_one' := idealRowHom_one_good _ hr.1
  map_mul' a b := idealRowHom_argument_mul a b _

lemma movingNumeratorRow_norm (r : O) (hr : quadraticSupported (Ideal.span {r})) (n : O) :
    ‖movingNumeratorRow r hr n‖≤1 := idealRowHom_norm n _

lemma movingNumeratorRow_periodic (r : O) (hr : quadraticSupported (Ideal.span {r}))
    (x y : O) (hxy : x-y∈Ideal.span {r}) :
    movingNumeratorRow r hr x=movingNumeratorRow r hr y := idealRowHom_congr_mod _ x y hxy

theorem idealRowHom_factor_numerator (u : Oˣ) (a b : ℕ) (r n : O)
    (hr : quadraticSupported (Ideal.span {r})) (hpr : lambda^2∣r-1)
    (hn : quadraticSupported (Ideal.span {n})) (hpn : lambda^2∣n-1) :
    idealRowHom ((u:O)*lambda^a*(2:O)^b*r) (Ideal.span {n})=
      numeratorBadTwist u a b r hr n*movingNumeratorRow r hr n := by
  have hu : unitSupplement u n=idealRowHom (u:O) (Ideal.span {n}) := by
    change (if quadraticSupported (Ideal.span {n}) then _ else 0)=_
    rw [if_pos hn]
  have hl : supportedIdealRow lambda n=idealRowHom lambda (Ideal.span {n}) := by
    change (if quadraticSupported (Ideal.span {n}) then _ else 0)=_
    rw [if_pos hn]
  have hrec := idealRowHom_primary_reciprocity n r hpn hpr hn hr
  rw [sexticReciprocityPhase_comm n r] at hrec
  change _=(((unitSupplement u n*(supportedIdealRow lambda n)^a)*(twoSupplement n)^b)*
    sexticReciprocityPhase r n)*idealRowHom n (Ideal.span {r})
  rw [idealRowHom_argument_mul,idealRowHom_argument_mul,idealRowHom_argument_mul,
    idealRowHom_argument_pow _ _ _ hn.1,idealRowHom_argument_pow _ _ _ hn.1,
    hu,hl,←idealRowHom_two_formula n hpn hn,hrec]
  ring

lemma numeratorBadTwist_zero_of_not_supported (u : Oˣ) (a b : ℕ) (r : O)
    (hr : quadraticSupported (Ideal.span {r})) (n : O)
    (hn : ¬quadraticSupported (Ideal.span {n})) : numeratorBadTwist u a b r hr n=0 := by
  have hu : unitSupplement u n=0 := by
    change (if quadraticSupported (Ideal.span {n}) then _ else 0)=0
    rw [if_neg hn]
  change ((unitSupplement u n*_)*_)*_=0
  rw [hu,zero_mul,zero_mul,zero_mul]

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

lemma coprimalityMask_good_part (u : Oˣ) (a b : ℕ) (r n : O)
    (hn : quadraticSupported (Ideal.span {n})) :
    coprimalityMask ((u:O)*lambda^a*(2:O)^b*r) n=coprimalityMask r n := by
  have hl : IsCoprime lambda n := residue_lambda_prime.irreducible.coprime_iff_not_dvd.mpr
    ((supported_span_iff n).mp hn).1
  have ht : IsCoprime (-2:O) n := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have h2 : IsCoprime (2:O) n := ht.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  have hu : IsCoprime (u:O) n := ⟨(u⁻¹:Oˣ),0,by simp⟩
  have hla : IsCoprime (lambda^a) n := hl.pow_left
  have htb : IsCoprime ((2:O)^b) n := h2.pow_left
  change (if IsCoprime ((u:O)*lambda^a*(2:O)^b*r) n then (1:ℂ) else 0)=_
  rw [IsCoprime.mul_left_iff,IsCoprime.mul_left_iff,IsCoprime.mul_left_iff]
  simp only [hu,hla,htb,true_and]
  rfl

lemma idealRowHom_sixth_denominator_mask (r n : O)
    (hr : quadraticSupported (Ideal.span {r})) :
    idealRowHom n ((Ideal.span {r})^6)=coprimalityMask r n := by
  rw [map_pow,←idealRowHom_argument_pow n 6 _ hr.1,idealRowHom_sixth_eq_mask n r hr]
  change (if IsCoprime n r then (1:ℂ) else 0)=(if IsCoprime r n then 1 else 0)
  rw [isCoprime_comm]

def goodMaskMovingIdeal (g r : O) : Ideal O := (Ideal.span {g})^6*Ideal.span {r}

lemma goodMaskMovingIdeal_supported (g r : O)
    (hg : quadraticSupported (Ideal.span {g})) (hr : quadraticSupported (Ideal.span {r})) :
    quadraticSupported (goodMaskMovingIdeal g r) :=
  (quadraticSupported_mul _ _).mpr ⟨CanonicalQuadraticSieve.quadraticSupported_pow hg 6,hr⟩

lemma mask_times_good_row (m : O) (u : Oˣ) (a b : ℕ) (g r n : O)
    (hg : quadraticSupported (Ideal.span {g})) (hm : m=(u:O)*lambda^a*(2:O)^b*g)
    (hn : quadraticSupported (Ideal.span {n})) :
    coprimalityMask m n*idealRowHom n (Ideal.span {r})=idealRowHom n (goodMaskMovingIdeal g r) := by
  rw [goodMaskMovingIdeal,hm,coprimalityMask_good_part u a b g n hn,map_mul,
    idealRowHom_sixth_denominator_mask g n hg]

/-- The sixth-power mask becomes part of the moving ideal; all bad-prime phases stay fixed. -/
theorem rowTwist_eq_fixed_times_good_row_primary
    (Ψ : O→*ℂ) (m f z : O) (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (um : Oˣ) (am bm : ℕ) (g : O) (hg : quadraticSupported (Ideal.span {g}))
    (hm : m=(um:O)*lambda^am*(2:O)^bm*g)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : quadraticSupported (Ideal.span {r}))
    (hpr : lambda^2∣r-1) (hx : f^4*z=(u:O)*lambda^a*(2:O)^b*r)
    (n : O) (hpn : lambda^2∣n-1) :
    rowTwist Ψ m f z n=(Ψ*numeratorBadTwist u a b r hr) n*idealRowHom n (goodMaskMovingIdeal g r) := by
  by_cases hn : quadraticSupported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask Ψ m f z n hn,hx,
      idealRowHom_factor_numerator u a b r n hr hpr hn hpn]
    change Ψ n*coprimalityMask m n*(numeratorBadTwist u a b r hr n*idealRowHom n (Ideal.span {r}))=
      (Ψ n*numeratorBadTwist u a b r hr n)*_
    rw [show Ψ n*coprimalityMask m n*(numeratorBadTwist u a b r hr n*idealRowHom n (Ideal.span {r}))=
      (Ψ n*numeratorBadTwist u a b r hr n)*(coprimalityMask m n*idealRowHom n (Ideal.span {r})) by ring,
      mask_times_good_row m um am bm g r n hg hm hn]
  · rw [rowTwist_zero_of_not_supported Ψ m f z n hmLam hm2 hn]
    change 0=(Ψ n*numeratorBadTwist u a b r hr n)*_
    rw [numeratorBadTwist_zero_of_not_supported u a b r hr n hn,mul_zero,zero_mul]

lemma fixedNumeratorTwist_periodic (Ψ : O→*ℂ) (Q : Ideal O)
    (hΨ : ∀x y : O,x-y∈Q→Ψ x=Ψ y)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : quadraticSupported (Ideal.span {r}))
    (x y : O) (hxy : x-y∈Q*Ideal.span {(72:O)}) :
    (Ψ*numeratorBadTwist u a b r hr) x=(Ψ*numeratorBadTwist u a b r hr) y := by
  change Ψ x*numeratorBadTwist u a b r hr x=Ψ y*numeratorBadTwist u a b r hr y
  have hQ : x-y∈Q := (Ideal.mul_le_right : Q*Ideal.span {(72:O)}≤Q) hxy
  have h72 : x-y∈Ideal.span {(72:O)} :=
    (Ideal.mul_le_left : Q*Ideal.span {(72:O)}≤Ideal.span {(72:O)}) hxy
  rw [hΨ x y hQ,numeratorBadTwist_periodic u a b r hr x y h72]

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped BigOperators Classical

abbrev BasePrimeIndex (I Q : Ideal O) := {P : primeSupport I // Q≤P.val}
abbrev FreePrimeIndex (I Q : Ideal O) := {P : primeSupport I // ¬Q≤P.val}

local instance basePrimeMaximal (I Q : Ideal O) (P : BasePrimeIndex I Q) : P.val.val.IsMaximal :=
  (Ideal.isPrime_of_prime (support_prime P.val.property)).isMaximal (support_prime P.val.property).ne_zero

local instance freePrimeMaximal (I Q : Ideal O) (P : FreePrimeIndex I Q) : P.val.val.IsMaximal :=
  (Ideal.isPrime_of_prime (support_prime P.val.property)).isMaximal (support_prime P.val.property).ne_zero

def basePrimeRow (I : Ideal O) (hI : quadraticSupported I) (Q : Ideal O) : O→*ℂ where
  toFun n := ∏P : BasePrimeIndex I Q,
    (complexSexticChar P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

def freePrimeRow (I : Ideal O) (hI : quadraticSupported I) (Q : Ideal O) : O→*ℂ where
  toFun n := ∏P : FreePrimeIndex I Q,
    (complexSexticChar P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

lemma basePrimeRow_norm (I : Ideal O) (hI : quadraticSupported I) (Q : Ideal O) (n : O) :
    ‖basePrimeRow I hI Q n‖≤1 := by
  change ‖∏P : BasePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

lemma freePrimeRow_norm (I : Ideal O) (hI : quadraticSupported I) (Q : Ideal O) (n : O) :
    ‖freePrimeRow I hI Q n‖≤1 := by
  change ‖∏P : FreePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

lemma basePrimeRow_periodic (I : Ideal O) (hI : quadraticSupported I) (Q : Ideal O)
    (x y : O) (hxy : x-y∈Q) : basePrimeRow I hI Q x=basePrimeRow I hI Q y := by
  change (∏P : BasePrimeIndex I Q,_)=∏P : BasePrimeIndex I Q,_
  apply Finset.prod_congr rfl
  intro P hP
  rw [Ideal.Quotient.eq.mpr (P.property hxy)]

/-- Prime factors meeting the fixed modulus are absorbed into its periodic coefficient. -/
theorem idealRowHom_fixed_conductor_split (I : Ideal O) (hI : quadraticSupported I)
    (Q : Ideal O) (n : O) : idealRowHom n I=basePrimeRow I hI Q n*freePrimeRow I hI Q n := by
  rw [idealRowHom_prime_character_product I hI n]
  letI (P : primeSupport I) : P.val.IsMaximal :=
    (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).1
  exact (Fintype.prod_subtype_mul_prod_subtype (fun P : primeSupport I => Q≤P.val)
    (fun P : primeSupport I =>
      (complexSexticChar P.val ((supported_factors_good I hI P.val
        (Multiset.mem_toFinset.mp P.property)).2.1)^((normalizedFactors I).count P.val%6))
        (Ideal.Quotient.mk P.val n))).symm

lemma freePrimeIndex_pairwise_coprime (I Q : Ideal O) :
    Pairwise (Function.onFun IsCoprime (fun P : FreePrimeIndex I Q => P.val.val)) := by
  intro P R hPR
  exact Ideal.isCoprime_of_isMaximal (fun he => hPR (Subtype.ext (Subtype.ext he)))

lemma freePrimeIndex_coprime (I Q : Ideal O) (P : FreePrimeIndex I Q) : IsCoprime Q P.val.val := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra ht
  have he : P.val.val=Q⊔P.val.val :=
    (show P.val.val.IsMaximal from inferInstance).eq_of_le ht le_sup_right
  exact P.property (le_sup_left.trans he.symm.le)

lemma freePrimeRow_periodic (I : Ideal O) (hI : quadraticSupported I) (Q : Ideal O)
    (x y : O) (hxy : x-y∈∏P : FreePrimeIndex I Q,P.val.val) :
    freePrimeRow I hI Q x=freePrimeRow I hI Q y := by
  change (∏P : FreePrimeIndex I Q,_)=∏P : FreePrimeIndex I Q,_
  apply Finset.prod_congr rfl
  intro P hP
  have hm : x-y∈P.val.val :=
    (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ P))) hxy
  rw [Ideal.Quotient.eq.mpr hm]

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

/-- Factorizations separate the two ramified primes from the moving good-prime ideal. -/
structure GoodMaskRowData (m f z : O) where
  maskUnit : Oˣ
  maskLambda : ℕ
  maskTwo : ℕ
  maskGood : O
  maskSupported : quadraticSupported (Ideal.span {maskGood})
  maskPrimary : lambda^2∣maskGood-1
  maskFactor : m=(maskUnit:O)*lambda^maskLambda*(2:O)^maskTwo*maskGood
  numeratorUnit : Oˣ
  numeratorLambda : ℕ
  numeratorTwo : ℕ
  numeratorGood : O
  numeratorSupported : quadraticSupported (Ideal.span {numeratorGood})
  numeratorPrimary : lambda^2∣numeratorGood-1
  numeratorFactor : f^4*z=(numeratorUnit:O)*lambda^numeratorLambda*(2:O)^numeratorTwo*numeratorGood

theorem exists_goodMaskRowData (m f z : O) (hm : m≠0) (hf : f≠0) (hz : z≠0) :
    Nonempty (GoodMaskRowData m f z) := by
  obtain ⟨um,am,bm,g,hg,hpg,hmf⟩ := exists_supported_numerator_factorization m hm
  obtain ⟨u,a,b,r,hr,hpr,hxf⟩ := exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  exact ⟨⟨um,am,bm,g,hg,hpg,hmf,u,a,b,r,hr,hpr,hxf⟩⟩

def goodMaskRowData (m f z : O) (hm : m≠0) (hf : f≠0) (hz : z≠0) : GoodMaskRowData m f z :=
  Classical.choice (exists_goodMaskRowData m f z hm hf hz)

namespace GoodMaskRowData
variable {m f z : O} (D : GoodMaskRowData m f z)

def movingIdeal : Ideal O := goodMaskMovingIdeal D.maskGood D.numeratorGood

lemma movingSupported : quadraticSupported D.movingIdeal :=
  goodMaskMovingIdeal_supported D.maskGood D.numeratorGood D.maskSupported D.numeratorSupported

def fixedFactor (Ψ : O→*ℂ) (Q : Ideal O) : O→*ℂ :=
  (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported)*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:O)})

lemma fixedFactor_periodic (Ψ : O→*ℂ) (Q : Ideal O)
    (hΨ : ∀x y : O,x-y∈Q→Ψ x=Ψ y) (x y : O) (hxy : x-y∈Q*Ideal.span {(72:O)}) :
    D.fixedFactor Ψ Q x=D.fixedFactor Ψ Q y := by
  change (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported) x*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:O)}) x=
    (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported) y*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:O)}) y
  rw [fixedNumeratorTwist_periodic Ψ Q hΨ D.numeratorUnit D.numeratorLambda
    D.numeratorTwo D.numeratorGood D.numeratorSupported x y hxy,
    basePrimeRow_periodic D.movingIdeal D.movingSupported _ x y hxy]

lemma fixedFactor_norm (Ψ : O→*ℂ) (Q : Ideal O) (hΨ : ∀n,‖Ψ n‖≤1) (n : O) :
    ‖D.fixedFactor Ψ Q n‖≤1 := by
  change ‖(Ψ n*numeratorBadTwist _ _ _ _ _ n)*(basePrimeRow _ _ _ n)‖≤1
  rw [norm_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) (hΨ n)).trans
      (numeratorBadTwist_norm _ _ _ _ _ n))).trans (basePrimeRow_norm _ _ _ n)

theorem row_primary (Ψ : O→*ℂ) (Q : Ideal O) (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (n : O) (hpn : lambda^2∣n-1) :
    rowTwist Ψ m f z n=D.fixedFactor Ψ Q n*
      freePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:O)}) n := by
  rw [rowTwist_eq_fixed_times_good_row_primary Ψ m f z hmLam hm2
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn]
  change (Ψ*numeratorBadTwist _ _ _ _ _) n*idealRowHom n D.movingIdeal=_
  rw [idealRowHom_fixed_conductor_split D.movingIdeal D.movingSupported (Q*Ideal.span {(72:O)}) n]
  simp only [fixedFactor,MonoidHom.mul_apply]
  ring

end GoodMaskRowData
end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped BigOperators Classical

local instance freeRowPrimeMaximal (I Q : Ideal O) (P : FreePrimeIndex I Q) : P.val.val.IsMaximal :=
  (Ideal.isPrime_of_prime (support_prime P.val.property)).isMaximal (support_prime P.val.property).ne_zero

def freePrimaryPrime (I Q : Ideal O) (P : FreePrimeIndex I Q) : O := primaryIdealPrime P.val.val

lemma freePrimaryPrime_ne_zero (I Q : Ideal O) (hI : quadraticSupported I) (P : FreePrimeIndex I Q) :
    freePrimaryPrime I Q P≠0 :=
  primaryIdealPrime_ne_zero P.val.val
    (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

lemma freePrimaryPrime_span (I Q : Ideal O) (hI : quadraticSupported I) (P : FreePrimeIndex I Q) :
    Ideal.span {freePrimaryPrime I Q P}=P.val.val :=
  (primaryIdealPrime_spec P.val.val (freePrimaryPrime_ne_zero I Q hI P)).2.2.1

lemma freePrimaryPrime_primary (I Q : Ideal O) (hI : quadraticSupported I) (P : FreePrimeIndex I Q) :
    lambda^2∣freePrimaryPrime I Q P-1 :=
  (primaryIdealPrime_spec P.val.val (freePrimaryPrime_ne_zero I Q hI P)).2.2.2

lemma freePrimaryPrime_maximal (I Q : Ideal O) (hI : quadraticSupported I) (P : FreePrimeIndex I Q) :
    (Ideal.span {freePrimaryPrime I Q P}:Ideal O).IsMaximal := by
  rw [freePrimaryPrime_span I Q hI P]
  infer_instance

lemma freePrimaryPrime_good (I Q : Ideal O) (hI : quadraticSupported I) (P : FreePrimeIndex I Q) :
    lambda∉(Ideal.span {freePrimaryPrime I Q P}:Ideal O) := by
  rw [freePrimaryPrime_span I Q hI P]
  exact (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

lemma freePrimaryPrime_odd (I Q : Ideal O) (hI : quadraticSupported I) (P : FreePrimeIndex I Q) :
    ringChar (O⧸Ideal.span {freePrimaryPrime I Q P})≠2 := by
  rw [freePrimaryPrime_span I Q hI P]
  exact (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.2

lemma freePrimaryPrime_coprime (I Q : Ideal O) (hI : quadraticSupported I) :
    Pairwise (Function.onFun IsCoprime (freePrimaryPrime I Q)) := by
  intro P R hPR
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [freePrimaryPrime_span I Q hI P,freePrimaryPrime_span I Q hI R]
  exact freePrimeIndex_pairwise_coprime I Q hPR

lemma freePrimaryPrime_coprime_fixed (I : Ideal O) (hI : quadraticSupported I)
    (c : O) (P : FreePrimeIndex I (Ideal.span {c})) : IsCoprime c (freePrimaryPrime I (Ideal.span {c}) P) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [freePrimaryPrime_span I (Ideal.span {c}) hI P]
  exact freePrimeIndex_coprime I (Ideal.span {c}) P

lemma sextic_power_transport (P R : Ideal O) [P.IsMaximal] [R.IsMaximal]
    (hP : lambda∉P) (hR : lambda∉R) (he : P=R) (j : ℕ) (n : O) :
    (complexSexticChar P hP^j) (Ideal.Quotient.mk P n)=
      (complexSexticChar R hR^j) (Ideal.Quotient.mk R n) := by
  subst R
  rfl

theorem freePrimeRow_eq_primary_family (I Q : Ideal O) (hI : quadraticSupported I) :
    letI : ∀P : FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal O).IsMaximal :=
      freePrimaryPrime_maximal I Q hI
    freePrimeRow I hI Q=primeCuspRowCharacter (freePrimaryPrime I Q)
      (fun P => complexSexticChar (Ideal.span {freePrimaryPrime I Q P})
        (freePrimaryPrime_good I Q hI P)^((normalizedFactors I).count P.val.val%6)) := by
  letI : ∀P : FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal O).IsMaximal :=
    freePrimaryPrime_maximal I Q hI
  ext n
  change (∏P : FreePrimeIndex I Q,_)=∏P : FreePrimeIndex I Q,_
  apply Finset.prod_congr rfl
  intro P hP
  exact sextic_power_transport _ _ _ _ (freePrimaryPrime_span I Q hI P).symm _ n

end CanonicalRowCompletion

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

lemma completedT_congr_primary (Ψ Φ : O→*ℂ)
    (h : ∀n : O,lambda^2∣n-1→Ψ n=Φ n) (W : ℝ→ℂ) (X : ℝ) :
    completedT Ψ W X=completedT Φ W X := by
  unfold completedT
  apply tsum_congr
  intro p
  rw [completedMellinCoefficient,completedMellinCoefficient,
    h _ (primaryIdealGenerator_spec p.1.val p.1.property.2).2,
    h _ (primaryIdealGenerator_spec p.2.val p.2.property).2]

end CompletedGauss

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss
open scoped BigOperators Classical

def periodicQuotientHom (c : O) (Ψ : O→*ℂ)
    (hΨ : ∀x y : O,x-y∈Ideal.span {c}→Ψ x=Ψ y) : (O⧸Ideal.span {c})→*ℂ where
  toFun x := Ψ (qrep x)
  map_one' := by
    have h := hΨ (qrep (1:O⧸Ideal.span {c})) 1
      (Ideal.Quotient.eq.mp (by rw [mk_qrep,map_one]))
    exact h.trans Ψ.map_one
  map_mul' x y := by
    have h := hΨ (qrep (x*y)) (qrep x*qrep y)
      (Ideal.Quotient.eq.mp (by rw [mk_qrep,map_mul,mk_qrep,mk_qrep]))
    exact h.trans (Ψ.map_mul _ _)

lemma periodicQuotientHom_mk (c : O) (Ψ : O→*ℂ)
    (hΨ : ∀x y : O,x-y∈Ideal.span {c}→Ψ x=Ψ y) (n : O) :
    periodicQuotientHom c Ψ hΨ (Ideal.Quotient.mk (Ideal.span {c}) n)=Ψ n :=
  hΨ _ _ (Ideal.Quotient.eq.mp (mk_qrep _))

lemma periodicQuotientHom_comp (c : O) (Ψ : O→*ℂ)
    (hΨ : ∀x y : O,x-y∈Ideal.span {c}→Ψ x=Ψ y) :
    (periodicQuotientHom c Ψ hΨ).comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom=Ψ := by
  ext n
  exact periodicQuotientHom_mk c Ψ hΨ n

lemma periodicQuotientHom_norm (c : O) (Ψ : O→*ℂ)
    (hΨ : ∀x y : O,x-y∈Ideal.span {c}→Ψ x=Ψ y) (hn : ∀n,‖Ψ n‖≤1)
    (x : O⧸Ideal.span {c}) : ‖periodicQuotientHom c Ψ hΨ x‖≤1 := hn (qrep x)

namespace GoodMaskRowData
variable {m f z : O} (D : GoodMaskRowData m f z)

theorem completedT_eq_fixedFactor (Ψ : O→*ℂ) (Q : Ideal O)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m) (W : ℝ→ℂ) (X : ℝ) :
    completedT (rowTwist Ψ m f z) W X=
      completedT (D.fixedFactor Ψ Q*freePrimeRow D.movingIdeal D.movingSupported
        (Q*Ideal.span {(72:O)})) W X :=
  completedT_congr_primary _ _ (D.row_primary Ψ Q hmLam hm2) W X

end GoodMaskRowData
end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss UniqueFactorizationMonoid
open scoped BigOperators Classical

namespace GoodMaskRowData
variable {m f z : O} (D : GoodMaskRowData m f z)

def fixedQuotient (Ψ : O→*ℂ) (Q : Ideal O) (c : O)
    (hc : Ideal.span {c}=Q*Ideal.span {(72:O)})
    (hΨ : ∀x y : O,x-y∈Q→Ψ x=Ψ y) : (O⧸Ideal.span {c})→*ℂ :=
  periodicQuotientHom c (D.fixedFactor Ψ Q)
    (fun x y hxy => D.fixedFactor_periodic Ψ Q hΨ x y (by rwa [←hc]))

lemma fixedQuotient_comp (Ψ : O→*ℂ) (Q : Ideal O) (c : O)
    (hc : Ideal.span {c}=Q*Ideal.span {(72:O)})
    (hΨ : ∀x y : O,x-y∈Q→Ψ x=Ψ y) :
    (D.fixedQuotient Ψ Q c hc hΨ).comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom=
      D.fixedFactor Ψ Q := periodicQuotientHom_comp _ _ _

lemma fixedQuotient_norm (Ψ : O→*ℂ) (Q : Ideal O) (c : O)
    (hc : Ideal.span {c}=Q*Ideal.span {(72:O)})
    (hΨ : ∀x y : O,x-y∈Q→Ψ x=Ψ y) (hn : ∀n,‖Ψ n‖≤1) (x : O⧸Ideal.span {c}) :
    ‖D.fixedQuotient Ψ Q c hc hΨ x‖≤1 := D.fixedFactor_norm Ψ Q hn (qrep x)

/-- Completed arithmetic rows have exactly the primary prime-family form required by reflection. -/
theorem completedT_eq_primary_family (Ψ : O→*ℂ) (Q : Ideal O) (c : O)
    (hc : Ideal.span {c}=Q*Ideal.span {(72:O)})
    (hΨ : ∀x y : O,x-y∈Q→Ψ x=Ψ y)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m) (W : ℝ→ℂ) (X : ℝ) :
    letI : ∀P : FreePrimeIndex D.movingIdeal (Ideal.span {c}),
        (Ideal.span {freePrimaryPrime D.movingIdeal (Ideal.span {c}) P}:Ideal O).IsMaximal :=
      freePrimaryPrime_maximal D.movingIdeal (Ideal.span {c}) D.movingSupported
    completedT (rowTwist Ψ m f z) W X=
      completedT ((D.fixedQuotient Ψ Q c hc hΨ).comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom*
        primeCuspRowCharacter (freePrimaryPrime D.movingIdeal (Ideal.span {c}))
          (fun P => complexSexticChar (Ideal.span {freePrimaryPrime D.movingIdeal (Ideal.span {c}) P})
            (freePrimaryPrime_good D.movingIdeal (Ideal.span {c}) D.movingSupported P)^
              ((normalizedFactors D.movingIdeal).count P.val.val%6))) W X := by
  letI : ∀P : FreePrimeIndex D.movingIdeal (Ideal.span {c}),
      (Ideal.span {freePrimaryPrime D.movingIdeal (Ideal.span {c}) P}:Ideal O).IsMaximal :=
    freePrimaryPrime_maximal D.movingIdeal (Ideal.span {c}) D.movingSupported
  have hrow : freePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:O)})=
      freePrimeRow D.movingIdeal D.movingSupported (Ideal.span {c}) := by rw [hc]
  rw [D.completedT_eq_fixedFactor Ψ Q hmLam hm2 W X,hrow,
    freePrimeRow_eq_primary_family,D.fixedQuotient_comp]

end GoodMaskRowData
end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap ContDiff

lemma freePrimaryPrime_coprime_reflection (I : Ideal O) (hI : quadraticSupported I)
    (c : O) (P : FreePrimeIndex I (Ideal.span {c})) :
    IsCoprime (243*c) (freePrimaryPrime I (Ideal.span {c}) P) := by
  have h3 : IsCoprime ((3:O)^5) (freePrimaryPrime I (Ideal.span {c}) P) :=
    (primary_coprime_three _ (freePrimaryPrime_primary I (Ideal.span {c}) hI P)).symm.pow_left
  have h243 : IsCoprime (243:O) (freePrimaryPrime I (Ideal.span {c}) P) := by
    simpa only [show (3:O)^5=243 by norm_num] using h3
  exact h243.mul_left (freePrimaryPrime_coprime_fixed I hI c P)

/-- The finite Fourier sum of the canonical cusp divisor series. -/
def canonicalReflectedSum {ι : Type*} [Fintype ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hg : ∀i,lambda∉Ideal.span {p i}) (N c : O) (hc : c≠0)
    [Fintype (O⧸Ideal.span {9*c})] (φ : (O⧸Ideal.span {c})→*ℂ) (j : ι→ℕ)
    (c₀ : (O⧸Ideal.span {9*c})→O)
    (sector : (O⧸Ideal.span {9*c})→Finset ι→FixedCuspSector)
    (b : (O⧸Ideal.span {9*c})→Finset ι→(O⧸Ideal.span {N}))
    (phase : (O⧸Ideal.span {9*c})→Finset ι→ℂ) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  thetaDerivativeScalar⁻¹*∑k : O⧸Ideal.span {9*c},
    finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9*c) (mul_ne_zero (by norm_num) hc))
      (finiteThetaTwist c φ) k*
    ∑s : Finset ι,
      (∏P : {P // P∉s},finiteAdditiveFourierCoeff
        (residueTraceQuotientChar 1 (p P.val) (hp P.val))
        (complexSexticChar (Ideal.span {p P.val}) (hg P.val)^j P.val :
          MulChar (O⧸Ideal.span {p P.val}) ℂ) 0)*
      phase k s*fixedCuspDivisorSeries (fun P : s=>p P.val) (fun P=>hg P.val)
        N (c₀ k) (sector k s) (b k s) (fun P=>j P.val) (Vstar W) X

namespace GoodMaskRowData
variable {m f z : O} (D : GoodMaskRowData m f z)

/-- Native completed rows admit the explicit cusp reflection with a fixed residue modulus. -/
theorem completedT_canonical_reflection (Ψ : O→*ℂ) (Q : Ideal O) (c : O) (hc : c≠0)
    (hspan : Ideal.span {c}=Q*Ideal.span {(72:O)})
    (hΨ : ∀x y : O,x-y∈Q→Ψ x=Ψ y)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m) [Fintype (O⧸Ideal.span {9*c})] :
    let p := freePrimaryPrime D.movingIdeal (Ideal.span {c})
    let j := fun P : FreePrimeIndex D.movingIdeal (Ideal.span {c}) =>
      (normalizedFactors D.movingIdeal).count P.val.val%6
    let φ := D.fixedQuotient Ψ Q c hspan hΨ
    letI : ∀P : FreePrimeIndex D.movingIdeal (Ideal.span {c}),(Ideal.span {p P}:Ideal O).IsMaximal :=
      freePrimaryPrime_maximal D.movingIdeal (Ideal.span {c}) D.movingSupported
    ∃ (c₀ : (O⧸Ideal.span {9*c})→O)
      (sector : (O⧸Ideal.span {9*c})→Finset (FreePrimeIndex D.movingIdeal (Ideal.span {c}))→FixedCuspSector)
      (b : (O⧸Ideal.span {9*c})→Finset (FreePrimeIndex D.movingIdeal (Ideal.span {c}))→(O⧸Ideal.span {243*c}))
      (phase : (O⧸Ideal.span {9*c})→Finset (FreePrimeIndex D.movingIdeal (Ideal.span {c}))→ℂ),
      (∀k,c₀ k≠0 ∧ c₀ k∣9*c) ∧
      (∀k s,‖phase k s‖^2≤81*∏P : s,
        if j P.val=0 ∨ j P.val=4 then (Fintype.card (O⧸Ideal.span {p P.val}):ℝ)⁻¹ else 1) ∧
      ∀(W : ℝ→ℂ) (A B : ℝ),0<A → Function.support W⊆Set.Icc A B → ContDiff ℝ ∞ W →
        ∀X : ℝ,0<X→completedT (rowTwist Ψ m f z) W X=
          canonicalReflectedSum p
            (freePrimaryPrime_ne_zero D.movingIdeal (Ideal.span {c}) D.movingSupported)
            (freePrimaryPrime_good D.movingIdeal (Ideal.span {c}) D.movingSupported)
            (243*c) c hc φ j c₀ sector b phase W X := by
  letI : ∀P : FreePrimeIndex D.movingIdeal (Ideal.span {c}),
      (Ideal.span {freePrimaryPrime D.movingIdeal (Ideal.span {c}) P}:Ideal O).IsMaximal :=
    freePrimaryPrime_maximal D.movingIdeal (Ideal.span {c}) D.movingSupported
  obtain ⟨c₀,sector,b,phase,hc₀,hphase,he⟩ := completedT_canonical_divisor_reflection (freePrimaryPrime D.movingIdeal (Ideal.span {c}))
    (freePrimaryPrime_ne_zero D.movingIdeal (Ideal.span {c}) D.movingSupported)
    (freePrimaryPrime_good D.movingIdeal (Ideal.span {c}) D.movingSupported)
    (freePrimaryPrime_primary D.movingIdeal (Ideal.span {c}) D.movingSupported)
    (freePrimaryPrime_odd D.movingIdeal (Ideal.span {c}) D.movingSupported)
    (freePrimaryPrime_coprime D.movingIdeal (Ideal.span {c}) D.movingSupported)
    (243*c) c hc (dvd_refl _) (freePrimaryPrime_coprime_reflection D.movingIdeal D.movingSupported c)
    (D.fixedQuotient Ψ Q c hspan hΨ)
    (fun P => (normalizedFactors D.movingIdeal).count P.val.val%6)
    (fun P => Nat.mod_lt _ (by decide : 0<6))
  refine ⟨c₀,sector,b,phase,hc₀,hphase,?_⟩
  intro W A B hA hs hW X hX
  rw [D.completedT_eq_primary_family Ψ Q c hspan hΨ hmLam hm2]
  exact he W A B hA hs hW X hX

end GoodMaskRowData
end CanonicalRowCompletion

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
