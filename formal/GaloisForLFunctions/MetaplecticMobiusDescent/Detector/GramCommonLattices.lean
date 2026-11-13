/-
Common Gram lattices adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.LowGramProfiles

/-!
# Common Gram lattices

Lattice points of the Gram lattice decay, supported ideals and joint fixed moduli; Bézout
coefficients parametrize the correlation constraint; annular weighted lattice bounds.
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
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]
abbrev ResidueQ (a : A) := A⧸Ideal.span {a}

def condition (C n₁ n₂ k : A) (p : ResidueQ (C*n₁) × ResidueQ (C*n₂)) : Prop :=
  scaledResidue (C*n₁) (C*n₂) ((C*n₁)*(C*n₂)) rfl p.1-
    scaledResidue (C*n₂) (C*n₁) ((C*n₁)*(C*n₂)) (mul_comm _ _) p.2=
    Ideal.Quotient.mk (Ideal.span {(C*n₁)*(C*n₂)}) (C*k)

abbrev Solutions (C n₁ n₂ k : A) := {p : ResidueQ (C*n₁) × ResidueQ (C*n₂) // condition C n₁ n₂ k p}

def leftParam (C n₁ b k : A) (t : ResidueQ C) : ResidueQ (C*n₁) :=
  Ideal.Quotient.mk _ (b*k)+scaledResidue C n₁ (C*n₁) rfl t

def rightParam (C n₂ a k : A) (t : ResidueQ C) : ResidueQ (C*n₂) :=
  Ideal.Quotient.mk _ (-a*k)+scaledResidue C n₂ (C*n₂) rfl t

omit [IsDomain A] in
@[simp] lemma leftParam_mk (C n₁ b k t : A) :
    leftParam C n₁ b k (Ideal.Quotient.mk _ t)=Ideal.Quotient.mk _ (b*k+n₁*t) := by
  simp only [leftParam,scaledResidue_mk,map_add]

omit [IsDomain A] in
@[simp] lemma rightParam_mk (C n₂ a k t : A) :
    rightParam C n₂ a k (Ideal.Quotient.mk _ t)=Ideal.Quotient.mk _ (-a*k+n₂*t) := by
  simp only [rightParam,scaledResidue_mk,map_add]

omit [IsDomain A] in
lemma param_condition (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    condition C n₁ n₂ k (leftParam C n₁ b k t,rightParam C n₂ a k t) := by
  obtain ⟨t,rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [leftParam_mk,rightParam_mk]
  unfold condition
  rw [scaledResidue_congruence]
  have he : C*n₂*(b*k+n₁*t)-C*n₁*(-a*k+n₂*t)-C*k=C*k*(a*n₁+b*n₂-1) := by ring
  rw [he,hab,sub_self,mul_zero]
  exact dvd_zero _

def param (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (t : ResidueQ C) : Solutions C n₁ n₂ k :=
  ⟨(leftParam C n₁ b k t,rightParam C n₂ a k t),param_condition C n₁ n₂ a b k hab t⟩

lemma param_injective (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (hn₁ : n₁≠0) :
    Function.Injective (param C n₁ n₂ a b k hab) := by
  intro t u he
  have hl : leftParam C n₁ b k t=leftParam C n₁ b k u := congrArg (fun p=> p.val.1) he
  apply scaledResidue_injective C n₁ (C*n₁) rfl hn₁
  exact add_left_cancel hl

lemma condition_divided (C n₁ n₂ k x y : A) (hC : C≠0)
    (hc : condition C n₁ n₂ k (Ideal.Quotient.mk _ x,Ideal.Quotient.mk _ y)) :
    C*n₁*n₂∣n₂*x-n₁*y-k := by
  unfold condition at hc
  rw [scaledResidue_congruence] at hc
  have hh : C*(C*n₁*n₂)∣C*(n₂*x-n₁*y-k) := by convert hc using 1 <;> ring
  exact (mul_dvd_mul_iff_left hC).mp hh

lemma param_surjective (C n₁ n₂ a b k : A) (hC : C≠0) (hab : a*n₁+b*n₂=1) :
    Function.Surjective (param C n₁ n₂ a b k hab) := by
  intro p
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective p.val.1
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective p.val.2
  have hc : condition C n₁ n₂ k (Ideal.Quotient.mk _ x,Ideal.Quotient.mk _ y) := by
    rw [hx,hy]
    exact p.property
  have hd := condition_divided C n₁ n₂ k x y hC hc
  refine ⟨Ideal.Quotient.mk _ (a*x+b*y),?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change leftParam C n₁ b k (Ideal.Quotient.mk _ (a*x+b*y))=p.val.1
    rw [leftParam_mk,←hx,Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    have hh : C*n₁∣n₂*x-n₁*y-k := (dvd_mul_right (C*n₁) n₂).trans hd
    have he : b*k+n₁*(a*x+b*y)-x= -b*(n₂*x-n₁*y-k) := by
      linear_combination x*hab
    rw [he]
    exact dvd_mul_of_dvd_right hh _
  · change rightParam C n₂ a k (Ideal.Quotient.mk _ (a*x+b*y))=p.val.2
    rw [rightParam_mk,←hy,Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    have hh : C*n₂∣n₂*x-n₁*y-k := by
      apply dvd_trans _ hd
      exact ⟨n₁,by ring⟩
    have he : -a*k+n₂*(a*x+b*y)-y=a*(n₂*x-n₁*y-k) := by
      linear_combination y*hab
    rw [he]
    exact dvd_mul_of_dvd_right hh _

/-- Bézout coefficients parametrize the correlation constraint modulo the common factor. -/
def solutionEquiv (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) : ResidueQ C≃Solutions C n₁ n₂ k :=
  Equiv.ofBijective (param C n₁ n₂ a b k hab)
    ⟨param_injective C n₁ n₂ a b k hab hn₁,param_surjective C n₁ n₂ a b k hC hab⟩

@[simp] lemma solutionEquiv_val (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    (solutionEquiv C n₁ n₂ a b k hC hn₁ hab t).val=(leftParam C n₁ b k t,rightParam C n₂ a k t) := rfl

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open CenteredMomentCorrelation
variable {R : Type*} [CommRing R]

def bezoutPairEquiv (n₁ n₂ a b : R) (hab : a*n₁+b*n₂=1) : R×R≃R×R where
  toFun p := (b*p.2+n₁*p.1,-a*p.2+n₂*p.1)
  invFun p := (a*p.1+b*p.2,n₂*p.1-n₁*p.2)
  left_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab
  right_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab

theorem fullCorrelation_bezout [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) :
    fullCorrelation (fun x=> n₂*x) (fun y=> n₁*y) f g k=
      ∑t : R,f (b*k+n₁*t)*star (g (-a*k+n₂*t)) := by
  unfold fullCorrelation
  rw [←Fintype.sum_prod_type (fun p : R×R=> if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0)]
  have he := (Fintype.sum_equiv (bezoutPairEquiv n₁ n₂ a b hab)
    (fun p : R×R=> if p.2=k then f (b*p.2+n₁*p.1)*star (g (-a*p.2+n₂*p.1)) else 0)
    (fun p : R×R=> if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0) (by
      intro p
      have hh : n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=p.2 := by
        linear_combination p.2*hab
      change (if p.2=k then _ else 0)=(if n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=k then _ else 0)
      rw [hh]
      rfl)).symm
  rw [he,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem fullCorrelation_bezout_norm [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) (hf : ∀x,‖f x‖≤1) (hg : ∀x,‖g x‖≤1) :
    ‖fullCorrelation (fun x=> n₂*x) (fun y=> n₁*y) f g k‖≤(Fintype.card R:ℝ) := by
  rw [fullCorrelation_bezout n₁ n₂ a b k hab]
  calc
    _ ≤ ∑t : R,‖f (b*k+n₁*t)*star (g (-a*k+n₂*t))‖ := norm_sum_le _ _
    _ ≤ ∑_t : R,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul,norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hg _)
    _ = _ := by simp

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
lemma fullModulusCorrelation_solutions (C n₁ n₂ k : A)
    [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑p : Solutions C n₁ n₂ k,χ p.val.1*star (ψ p.val.2) := by
  unfold fullModulusCorrelation fullCorrelation
  change (∑x : ResidueQ (C*n₁),∑y : ResidueQ (C*n₂),
    if condition C n₁ n₂ k (x,y) then χ x*star (ψ y) else 0)=_
  rw [←Fintype.sum_prod_type (fun p : ResidueQ (C*n₁)×ResidueQ (C*n₂)=>
    if condition C n₁ n₂ k p then χ p.1*star (ψ p.2) else 0)]
  change (∑p : ResidueQ (C*n₁)×ResidueQ (C*n₂),
    if condition C n₁ n₂ k p then χ p.1*star (ψ p.2) else 0)=_
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem fullModulusCorrelation_parameter (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1)
    [Fintype (ResidueQ C)] [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑t : ResidueQ C,χ (leftParam C n₁ b k t)*star (ψ (rightParam C n₂ a k t)) := by
  rw [fullModulusCorrelation_solutions]
  symm
  exact Fintype.sum_equiv (solutionEquiv C n₁ n₂ a b k hC hn₁ hab) _ _ (fun _=> rfl)

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

def actualCommon (C : O) (hC : Supported (Ideal.span {C})) (n₁ n₂ k : O) : ℂ := by
  letI := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero C hC)
  letI : Fintype (ResidueQ C) := Fintype.ofFinite _
  exact fullCorrelation (fun x : ResidueQ C=> Ideal.Quotient.mk _ n₂*x)
    (fun y : ResidueQ C=> Ideal.Quotient.mk _ n₁*y)
    (supportedModulusCharacter C hC) (supportedModulusCharacter C hC) (Ideal.Quotient.mk _ k)

lemma actualCommon_parameter (C : O) (hC : Supported (Ideal.span {C})) (n₁ n₂ a b k : O)
    (hab : a*n₁+b*n₂=1) :
    letI := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero C hC)
    letI : Fintype (ResidueQ C) := Fintype.ofFinite _
    actualCommon C hC n₁ n₂ k=
      ∑t : ResidueQ C,
        supportedModulusCharacter C hC (Ideal.Quotient.mk _ (b*k)+Ideal.Quotient.mk _ n₁*t)*
          star (supportedModulusCharacter C hC (Ideal.Quotient.mk _ (-a*k)+Ideal.Quotient.mk _ n₂*t)) := by
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero C hC)
  let : Fintype (ResidueQ C) := Fintype.ofFinite _
  have hh : Ideal.Quotient.mk (Ideal.span {C}) a*Ideal.Quotient.mk _ n₁+
      Ideal.Quotient.mk _ b*Ideal.Quotient.mk _ n₂=1 := by rw [←map_mul,←map_mul,←map_add,hab,map_one]
  rw [actualCommon,fullCorrelation_bezout _ _ _ _ _ hh]
  simp only [map_mul,map_neg]

theorem actualCommon_norm (C : O) (hC : Supported (Ideal.span {C})) (n₁ n₂ k : O)
    (hn : IsCoprime n₁ n₂) : ‖actualCommon C hC n₁ n₂ k‖≤(Ideal.absNorm (Ideal.span {C}):ℝ) := by
  obtain ⟨a,b,hab⟩ := hn
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero C hC)
  let : Fintype (ResidueQ C) := Fintype.ofFinite _
  have hh : Ideal.Quotient.mk (Ideal.span {C}) a*Ideal.Quotient.mk _ n₁+
      Ideal.Quotient.mk _ b*Ideal.Quotient.mk _ n₂=1 := by rw [←map_mul,←map_mul,←map_add,hab,map_one]
  have hc (x : ResidueQ C) : ‖supportedModulusCharacter C hC x‖≤1 := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact idealRowHom_norm _ _
  have hd := fullCorrelation_bezout_norm (Ideal.Quotient.mk (Ideal.span {C}) n₁)
    (Ideal.Quotient.mk _ n₂) _ _ (Ideal.Quotient.mk _ k) hh
    (supportedModulusCharacter C hC) (supportedModulusCharacter C hC) hc hc
  simpa only [actualCommon,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hd

theorem actual_common_lift_bezout (C n₁ n₂ a b k : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (hab : a*n₁+b*n₂=1) :
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) (C*k)=
      (idealRowHom (b*k) (Ideal.span {n₁})*star (idealRowHom (-a*k) (Ideal.span {n₂})))*
        actualCommon C hC n₁ n₂ k := by
  have hc := supported_element_ne_zero C hC
  have h₁n := supported_element_ne_zero n₁ h₁
  have h₂n := supported_element_ne_zero n₂ h₂
  let := finiteEisensteinQuotientOfNonzero hc
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero hc h₁n)
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero hc h₂n)
  let : Fintype (ResidueQ C) := Fintype.ofFinite _
  let : Fintype (ResidueQ (C*n₁)) := Fintype.ofFinite _
  let : Fintype (ResidueQ (C*n₂)) := Fintype.ofFinite _
  change fullModulusCorrelation (C*n₁) (C*n₂) _ _ (C*k)=_
  rw [fullModulusCorrelation_parameter C n₁ n₂ a b k hc h₁n hab,
    actualCommon_parameter C hC n₁ n₂ a b k hab,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨t,rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [leftParam_mk,rightParam_mk,supportedModulusCharacter_mul C n₁ hC h₁,
    supportedModulusCharacter_mul C n₂ hC h₂]
  have hleft : idealRowHom (b*k+n₁*t) (Ideal.span {n₁})=idealRowHom (b*k) (Ideal.span {n₁}) := by
    apply idealRowHom_congr_mod
    exact Ideal.mem_span_singleton.mpr ⟨t,by ring⟩
  have hright : idealRowHom (-a*k+n₂*t) (Ideal.span {n₂})=idealRowHom (-a*k) (Ideal.span {n₂}) := by
    apply idealRowHom_congr_mod
    exact Ideal.mem_span_singleton.mpr ⟨t,by ring⟩
  simp only [←map_mul,←map_add]
  simp only [supportedModulusCharacter_mk,hleft,hright,star_mul]
  ring

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation CenteredMomentCommonSupport
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

lemma supported_bezout_inverse (n m a b : O) (hn : Supported (Ideal.span {n}))
    (hab : a*n+b*m=1) :
    idealRowHom b (Ideal.span {n})=star (idealRowHom m (Ideal.span {n})) := by
  have he : idealRowHom (b*m) (Ideal.span {n})=1 := by
    rw [←idealRowHom_one_supported (Ideal.span {n}) hn]
    apply idealRowHom_congr_mod
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-a,?_⟩
    linear_combination hab
  rw [idealRowHom_argument_mul] at he
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero n hn)
  let : Fintype (ResidueQ n) := Fintype.ofFinite _
  change supportedModulusCharacter n hn (Ideal.Quotient.mk _ b)=
    star (supportedModulusCharacter n hn (Ideal.Quotient.mk _ m))
  rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']
  exact eq_inv_of_mul_eq_one_left he

theorem actual_common_lift (C n₁ n₂ k : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂}))
    (hp₁ : lambda^2∣n₁-1)
    (hp₂ : lambda^2∣n₂-1) (hn : IsCoprime n₁ n₂) :
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) (C*k)=
      idealRowHom k (Ideal.span {n₁})*star (idealRowHom (-k) (Ideal.span {n₂}))*
        sexticReciprocityPhase n₁ n₂*actualCommon C hC n₁ n₂ k := by
  obtain ⟨a,b,hab⟩ := hn
  rw [actual_common_lift_bezout C n₁ n₂ a b k hC h₁ h₂ hab]
  have h₁b := supported_bezout_inverse n₁ n₂ a b h₁ hab
  have h₂a := supported_bezout_inverse n₂ n₁ b a h₂ (by simpa only [add_comm] using hab)
  have he : idealRowHom (-a*k) (Ideal.span {n₂})=
      idealRowHom a (Ideal.span {n₂})*idealRowHom (-k) (Ideal.span {n₂}) := by
    rw [show -a*k=a*(-k) by ring,idealRowHom_argument_mul]
  rw [idealRowHom_argument_mul,he,h₁b,h₂a,star_mul,star_star]
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero n₁ h₁)
  let : Fintype (ResidueQ n₁) := Fintype.ofFinite _
  have hphase := supported_opposite_phase n₁ n₂ h₁ h₂ hp₁ hp₂ ⟨a,b,hab⟩
  calc
    _ = idealRowHom k (Ideal.span {n₁})*star (idealRowHom (-k) (Ideal.span {n₂}))*
        (idealRowHom n₁ (Ideal.span {n₂})*star (idealRowHom n₂ (Ideal.span {n₁})))*actualCommon C hC n₁ n₂ k := by ring
    _ = _ := by rw [hphase]

theorem actual_common_norm (C n₁ n₂ k : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (hn : IsCoprime n₁ n₂) :
    ‖actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) (C*k)‖≤(Ideal.absNorm (Ideal.span {C}):ℝ) := by
  obtain ⟨a,b,hab⟩ := hn
  rw [actual_common_lift_bezout C n₁ n₂ a b k hC h₁ h₂ hab,norm_mul,norm_mul,norm_star]
  have hc := actualCommon_norm C hC n₁ n₂ k ⟨a,b,hab⟩
  have hp : ‖idealRowHom (b*k) (Ideal.span {n₁})‖*‖idealRowHom (-a*k) (Ideal.span {n₂})‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans (idealRowHom_norm _ _)
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (by simpa using hc)

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open Eisenstein _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open   CenteredMomentCorrelation CenteredMomentCanonical
local notation "O" => Eisenstein.O

lemma finiteField_local_norm {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (u v k : F) (huv : u≠0 ∨ v≠0) :
    ‖localCorrelation χ u v k‖≤(Fintype.card F:ℝ) := by
  rcases huv with hu|hv
  · exact fullCorrelation_bezout_norm u v u⁻¹ 0 k (by simp [hu]) χ χ
      (FiniteRayExpansion.norm_char_le_one χ) (FiniteRayExpansion.norm_char_le_one χ)
  · exact fullCorrelation_bezout_norm u v 0 v⁻¹ k (by simp [hv]) χ χ
      (FiniteRayExpansion.norm_char_le_one χ) (FiniteRayExpansion.norm_char_le_one χ)

def localExtension (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (c : ℕ) (n₁ n₂ k : O) : ℂ := by
  letI : Fintype (O⧸P) := Fintype.ofFinite _
  letI : Field (O⧸P) := Ideal.Quotient.field P
  exact if n₁∈P ∧ n₂∈P then 0 else (Ideal.absNorm P:ℂ)^(c-1)*
    localCorrelation (complexSexticChar P hg^c) (Ideal.Quotient.mk P n₁)
      (Ideal.Quotient.mk P n₂) (Ideal.Quotient.mk P k)

lemma localExtension_both_zero (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (c : ℕ) (n₁ n₂ k : O) (h₁ : n₁∈P) (h₂ : n₂∈P) :
    localExtension P hg c n₁ n₂ k=0 := by simp [localExtension,h₁,h₂]

theorem localExtension_periodic (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (c : ℕ) (n₁ n₂ m₁ m₂ k l : O)
    (h₁ : n₁-m₁∈P) (h₂ : n₂-m₂∈P) (hk : k-l∈P) :
    localExtension P hg c n₁ n₂ k=localExtension P hg c m₁ m₂ l := by
  have he₁ := Ideal.Quotient.eq.mpr h₁
  have he₂ := Ideal.Quotient.eq.mpr h₂
  have hek := Ideal.Quotient.eq.mpr hk
  have hm₁ : n₁∈P↔m₁∈P := by
    rw [←Ideal.Quotient.eq_zero_iff_mem,he₁,Ideal.Quotient.eq_zero_iff_mem]
  have hm₂ : n₂∈P↔m₂∈P := by
    rw [←Ideal.Quotient.eq_zero_iff_mem,he₂,Ideal.Quotient.eq_zero_iff_mem]
  simp only [localExtension,hm₁,hm₂,he₁,he₂,hek]

theorem localExtension_norm (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (c : ℕ) (hc : 1≤ c) (n₁ n₂ k : O) :
    ‖localExtension P hg c n₁ n₂ k‖≤(Ideal.absNorm P:ℝ)^c := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  let : Field (O⧸P) := Ideal.Quotient.field P
  unfold localExtension
  split_ifs with hn
  · simp only [norm_zero]
    positivity
  have huv : Ideal.Quotient.mk P n₁≠0 ∨ Ideal.Quotient.mk P n₂≠0 := by
    by_contra hh
    push_neg at hh
    exact hn ⟨Ideal.Quotient.eq_zero_iff_mem.mp hh.1,Ideal.Quotient.eq_zero_iff_mem.mp hh.2⟩
  have hh := finiteField_local_norm (complexSexticChar P hg^c) (Ideal.Quotient.mk P n₁)
    (Ideal.Quotient.mk P n₂) (Ideal.Quotient.mk P k) huv
  rw [norm_mul,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ (Ideal.absNorm P:ℝ)^(c-1)*(Ideal.absNorm P:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hh
    _ = _ := by rw [←pow_succ,Nat.sub_add_cancel hc]

theorem primePower_common_extension (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (c : ℕ) (hc : 1≤ c) [Fintype (O⧸P^c)] (n₁ n₂ k : O)
    (hn : n₁∉P ∨ n₂∉P) :
    fullCorrelation (fun x : O⧸P^c=> Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸P^c=> Ideal.Quotient.mk _ n₁*y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) (Ideal.Quotient.mk _ k)=
      localExtension P hg c n₁ n₂ k := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  let : Field (O⧸P) := Ideal.Quotient.field P
  have hn' : ¬(n₁∈P ∧ n₂∈P) := by tauto
  rw [localExtension,if_neg hn']
  rcases hn with h₁|h₂
  · have hu : IsUnit (Ideal.Quotient.mk (P^c) n₁) :=
      (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
        (isUnit_iff_ne_zero.mpr (fun hz=> h₁ (Ideal.Quotient.eq_zero_iff_mem.mp hz)))
    obtain ⟨u,hu⟩ := hu
    rw [←hu]
    unfold primePowerRow
    rw [primePower_localCorrelation]
    simp only [primePowerReduction,Ideal.Quotient.factor_mk,hu]
  · have hv : IsUnit (Ideal.Quotient.mk (P^c) n₂) :=
      (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
        (isUnit_iff_ne_zero.mpr (fun hz=> h₂ (Ideal.Quotient.eq_zero_iff_mem.mp hz)))
    obtain ⟨v,hv⟩ := hv
    rw [←hv]
    unfold primePowerRow
    rw [fullCorrelation_reduction_unit_left _ (primePowerReduction_surjective P hc),
      primePowerReduction_multiplicity,Nat.cast_pow]
    change (Ideal.absNorm P:ℂ)^(c-1)*localCorrelation (complexSexticChar P hg^c)
      (primePowerReduction P hc (Ideal.Quotient.mk _ n₁)) (primePowerReduction P hc v)
      (primePowerReduction P hc (Ideal.Quotient.mk _ k))=_
    simp only [hv,primePowerReduction,Ideal.Quotient.factor_mk]

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open Eisenstein  
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCorrelation CenteredMomentCanonical CenteredMomentSupportedCorrelation
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

/-- Product of prime-power correlations, extended by zero when both coefficients vanish. -/
def globalExtension (P : ι→ Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,lambda∉P i) (c : ι→ℕ) (n₁ n₂ k : O) : ℂ :=
  ∏i,localExtension (P i) (hg i) (c i) n₁ n₂ k

lemma globalExtension_norm (P : ι→ Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,lambda∉P i) (c : ι→ℕ) (hc : ∀i,1≤ c i) (n₁ n₂ k : O) :
    ‖globalExtension P hg c n₁ n₂ k‖≤(Ideal.absNorm (∏i,P i^c i):ℝ) := by
  rw [globalExtension,norm_prod]
  calc
    _ ≤ ∏i,(Ideal.absNorm (P i):ℝ)^c i :=
      Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> localExtension_norm (P i) (hg i) (c i) (hc i) n₁ n₂ k)
    _ = _ := by simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow]

theorem globalExtension_periodic (P : ι→ Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,lambda∉P i) (c : ι→ℕ) (n₁ n₂ m₁ m₂ k l : O)
    (h₁ : n₁-m₁∈∏i,P i) (h₂ : n₂-m₂∈∏i,P i) (hk : k-l∈∏i,P i) :
    globalExtension P hg c n₁ n₂ k=globalExtension P hg c m₁ m₂ l := by
  apply Finset.prod_congr rfl
  intro i hi
  have hle : (∏i,P i)≤ P i := Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))
  exact localExtension_periodic (P i) (hg i) (c i) n₁ n₂ m₁ m₂ k l (hle h₁) (hle h₂) (hle hk)

theorem canonical_common_extension (P : ι→ Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,lambda∉P i) (c : ι→ℕ) (hc : ∀i,1≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ k : O) (hn : IsCoprime n₁ n₂) :
    fullCorrelation (fun x : O⧸∏i,P i^c i=> Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸∏i,P i^c i=> Ideal.Quotient.mk _ n₁*y)
      (canonicalCRTCharacter P hg c hc hcop) (canonicalCRTCharacter P hg c hc hcop)
      (Ideal.Quotient.mk _ k)=globalExtension P hg c n₁ n₂ k := by
  have hpc : Pairwise (Function.onFun IsCoprime (fun i => P i ^ c i)) := by
    intro i j hij
    exact (hcop hij).pow
  have he := canonicalCRTCorrelation P hg c hc hcop
    (Ideal.Quotient.mk _ n₁) (Ideal.Quotient.mk _ n₂) (Ideal.Quotient.mk _ k)
  have hprod : fullCorrelation (fun x : O⧸∏i,P i^c i=> Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸∏i,P i^c i=> Ideal.Quotient.mk _ n₁*y)
      (canonicalCRTCharacter P hg c hc hcop) (canonicalCRTCharacter P hg c hc hcop)
      (Ideal.Quotient.mk _ k) =
      ∏i,fullCorrelation (fun x : O⧸P i^c i=> Ideal.Quotient.mk _ n₂*x)
        (fun y : O⧸P i^c i=> Ideal.Quotient.mk _ n₁*y)
        (primePowerRow (P i) (hg i) (hc i)) (primePowerRow (P i) (hg i) (hc i))
        (Ideal.Quotient.mk _ k) := by
    simpa only [IdealGaussCRT.quotientProdEquivPi_mk
      (fun i => P i ^ c i) hpc] using he
  rw [hprod]
  apply Finset.prod_congr rfl
  intro i hi
  apply primePower_common_extension
  by_contra h
  push_neg at h
  obtain ⟨a,b,hab⟩ := hn
  have hmem : (1:O)∈P i := by
    rw [←hab]
    exact (P i).add_mem ((P i).mul_mem_left a h.1) ((P i).mul_mem_left b h.2)
  exact (Ideal.IsMaximal.ne_top (I:=P i) inferInstance) ((Ideal.eq_top_iff_one (P i)).mpr hmem)

theorem actualCommon_eq_globalExtension (C : O) (hC : Supported (Ideal.span {C}))
    (P : ι→ Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (c : ι→ℕ) (hc : ∀i,1≤ c i) (hcop : Pairwise (Function.onFun IsCoprime P))
    (he : Ideal.span {C}=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ k : O) (hn : IsCoprime n₁ n₂) :
    actualCommon C hC n₁ n₂ k=globalExtension P hg c n₁ n₂ k := by
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero C hC)
  let : Fintype (O⧸Ideal.span {C}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq he
  have hchar : (supportedModulusCharacter C hC : (O⧸Ideal.span {C})→ℂ)=
      (fun x=> canonicalCRTCharacter P hg c hc hcop (e x)) := by
    funext x
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [show e (Ideal.Quotient.mk _ x)=Ideal.Quotient.mk _ x from Ideal.quotEquivOfEq_mk he x,
      canonicalCRTCharacter_mk,supportedModulusCharacter_mk,he]
  rw [actualCommon,hchar,fullCorrelation_ringEquiv e]
  simp only [e,Ideal.quotEquivOfEq_mk]
  exact canonical_common_extension P hg c hc hcop n₁ n₂ k hn

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open Eisenstein CompletedGauss  
open CenteredMomentCorrelation CenteredMomentCanonical
local notation "O" => Eisenstein.O

lemma complexSexticChar_power_nonprincipal (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (hchar : ringChar (O⧸P)≠2) (e : ℕ) (he : ¬6∣e) :
    complexSexticChar P hg^e≠1 := by
  intro h
  have hd := (orderOf_dvd_iff_pow_eq_one).mpr h
  rw [complexSexticChar_order_six P hg hchar] at hd
  exact he hd

theorem primePower_mean_zero (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤ c) (he : ¬6∣e) [Fintype (O⧸P^c)] (d : O) :
    (∑x : O⧸P^c,(complexSexticChar P hg^e)
      (Ideal.Quotient.mk P d*primePowerReduction P hc x))=0 := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  simp_rw [map_mul]
  rw [←Finset.mul_sum,sum_reduction _ (primePowerReduction_surjective P hc),
    MulChar.sum_eq_zero_of_ne_one (complexSexticChar_power_nonprincipal P hg hchar e he),mul_zero,mul_zero]

theorem crt_joint_mean_zero (Q P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤ c) (he : ¬6∣e) (hcop : IsCoprime Q (P^c))
    [Fintype (O⧸Q)] [Fintype (O⧸P^c)] [Fintype (O⧸Q*P^c)]
    (F : (O⧸Q)→(O⧸Q*P^c)→ℂ) (d : O) :
    (∑x : O⧸Q*P^c,∑y : O⧸Q*P^c,
      (complexSexticChar P hg^e) (Ideal.Quotient.mk P d*
        primePowerReduction P hc ((Ideal.quotientMulEquivQuotientProd Q (P^c) hcop x).2))*
      F ((Ideal.quotientMulEquivQuotientProd Q (P^c) hcop x).1) y)=0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y hy
  let E := Ideal.quotientMulEquivQuotientProd Q (P^c) hcop
  have heq := E.toEquiv.sum_comp (fun p : (O⧸Q)×(O⧸P^c)=>
    (complexSexticChar P hg^e) (Ideal.Quotient.mk P d*primePowerReduction P hc p.2)*F p.1 y)
  change (∑x : O⧸Q*P^c,(complexSexticChar P hg^e)
    (Ideal.Quotient.mk P d*primePowerReduction P hc (E x).2)*F (E x).1 y)=0
  calc
    _ = ∑p : (O⧸Q)×(O⧸P^c),(complexSexticChar P hg^e)
        (Ideal.Quotient.mk P d*primePowerReduction P hc p.2)*F p.1 y := heq
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      simp_rw [←Finset.sum_mul,primePower_mean_zero P hg hchar c e hc he d,zero_mul]
      simp

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open Eisenstein CompletedGauss  
open CenteredMomentCorrelation CanonicalCoefficientClass
local notation "O" => Eisenstein.O

theorem joint_mean_of_local_factor (Q P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤ c) (he : ¬6∣e) (hcop : IsCoprime Q (P^c))
    [Fintype (O⧸Q)] [Fintype (O⧸P^c)] [Fintype (O⧸Q*P^c)]
    (F : O→ O→ℂ) (hF : ∀x z y,x-z∈Q → F x y=F z y) (d : O) :
    (∑x : O⧸Q*P^c,∑y : O⧸Q*P^c,
      (complexSexticChar P hg^e) (Ideal.Quotient.mk P (d*x.out))*F x.out y.out)=0 := by
  let E := Ideal.quotientMulEquivQuotientProd Q (P^c) hcop
  have hE (x : O⧸Q*P^c) : E x=(Ideal.Quotient.mk Q x.out,Ideal.Quotient.mk (P^c) x.out) := by
    conv_lhs => rw [←Ideal.Quotient.mk_out x]
    rfl
  have hf (x : O⧸Q*P^c) (y : O) : F x.out y=F (E x).1.out y := by
    apply hF
    apply Ideal.Quotient.eq.mp
    rw [Ideal.Quotient.mk_out,hE]
  have hp (x : O⧸Q*P^c) : Ideal.Quotient.mk P (d*x.out)=
      Ideal.Quotient.mk P d*primePowerReduction P hc (E x).2 := by
    rw [map_mul,hE]
    rfl
  have hz := crt_joint_mean_zero Q P hg hchar c e hc he hcop
    (fun x y=> F x.out y.out) d
  convert hz using 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [hp,hf]

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

def numeratorExtension (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) : O→*ℂ :=
  numeratorBadTwist u a b r ((supported_iff_native _).mp hr)*movingNumeratorRow r ((supported_iff_native _).mp hr)

lemma numeratorExtension_norm (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n : O) :
    ‖numeratorExtension u a b r hr n‖≤1 := by
  rw [numeratorExtension,MonoidHom.mul_apply,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (numeratorBadTwist_norm _ _ _ _ _ _)).trans (movingNumeratorRow_norm _ _ _)

lemma numeratorExtension_periodic (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(72:O)}*Ideal.span {r})
      (numeratorExtension u a b r hr) := by
  intro x y hxy
  change numeratorBadTwist u a b r ((supported_iff_native _).mp hr) x*movingNumeratorRow r ((supported_iff_native _).mp hr) x=
    numeratorBadTwist u a b r ((supported_iff_native _).mp hr) y*movingNumeratorRow r ((supported_iff_native _).mp hr) y
  rw [numeratorBadTwist_periodic _ _ _ _ _ x y (Ideal.mul_le_right hxy),
    movingNumeratorRow_periodic _ _ x y (Ideal.mul_le_left hxy)]

lemma numeratorExtension_primary (u : Oˣ) (a b : ℕ) (r k n : O)
    (hr : Supported (Ideal.span {r})) (hpr : lambda^2∣r-1)
    (hk : k=u.val*lambda^a*(2:O)^b*r)
    (hn : Supported (Ideal.span {n})) (hpn : lambda^2∣n-1) :
    numeratorExtension u a b r hr n=idealRowHom k (Ideal.span {n}) := by
  rw [hk]
  exact (idealRowHom_factor_numerator u a b r n ((supported_iff_native _).mp hr) hpr ((supported_iff_native _).mp hn) hpn).symm

lemma numeratorExtension_neg_primary (u : Oˣ) (a b : ℕ) (r k n : O)
    (hr : Supported (Ideal.span {r})) (hpr : lambda^2∣r-1)
    (hk : k=u.val*lambda^a*(2:O)^b*r)
    (hn : Supported (Ideal.span {n})) (hpn : lambda^2∣n-1) :
    numeratorExtension (-u) a b r hr n=idealRowHom (-k) (Ideal.span {n}) := by
  apply numeratorExtension_primary _ _ _ _ _ _ hr hpr _ hn hpn
  simp only [Units.val_neg,hk]
  ring

lemma numerator_good_norm_le (u : Oˣ) (a b : ℕ) (r k : O)
    (hk : k=u.val*lambda^a*(2:O)^b*r) (hk0 : k≠0) :
    Ideal.absNorm (Ideal.span {r})≤ Ideal.absNorm (Ideal.span {k}) := by
  apply Nat.le_of_dvd
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hk0))
  · apply map_dvd Ideal.absNorm
    rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    exact ⟨u.val*lambda^a*(2:O)^b,by rw [hk];ring⟩

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open ProbePhysical _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def primaryCoefficient (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) : ℂ :=
  if lambda^2∣n-1 then gramCoefficientExtension S hS σ n else 0

lemma primaryCoefficient_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) :
    ‖primaryCoefficient S hS σ n‖≤1 := by
  unfold primaryCoefficient
  split_ifs
  · exact gramCoefficientExtension_norm _ _ _ _
  · simp

def jointFixedModulus (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  gramFixedModulus S hS*Ideal.span {lambda^2}*Ideal.span {(72:O)}

lemma jointFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : jointFixedModulus S hS≠0 := by
  apply mul_ne_zero
  · apply mul_ne_zero (gramFixedModulus_nonzero S hS)
    exact Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ residue_lambda_prime.ne_zero)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

lemma primaryCoefficient_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (x y : O) (hxy : x-y∈jointFixedModulus S hS) :
    primaryCoefficient S hS σ x=primaryCoefficient S hS σ y := by
  have hg := gramCoefficientExtension_periodic S hS σ x y (Ideal.mul_le_right (Ideal.mul_le_right hxy))
  have hp : lambda^2∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_left (Ideal.mul_le_right hxy))
  have hi : (lambda^2∣x-1)↔(lambda^2∣y-1) := by
    constructor
    · intro h
      convert dvd_sub h hp using 1 ; ring
    · intro h
      convert dvd_add hp h using 1 ; ring
  simp only [primaryCoefficient,hi,hg]

def jointFixed (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ : O) : ℂ :=
  primaryCoefficient S hS σ (C*n₁)*star (primaryCoefficient S hS σ (C*n₂))*
    numeratorBadTwist u a b r ((supported_iff_native _).mp hr) n₁*star (numeratorBadTwist (-u) a b r ((supported_iff_native _).mp hr) n₂)*
      sexticReciprocityPhase n₁ n₂

lemma jointFixed_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ : O) :
    ‖jointFixed S hS σ C u a b r hr n₁ n₂‖≤1 := by
  unfold jointFixed
  simp only [norm_mul,norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (sexticReciprocityPhase_norm _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (numeratorBadTwist_norm _ _ _ _ _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (numeratorBadTwist_norm _ _ _ _ _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (primaryCoefficient_norm _ _ _ _)).trans (primaryCoefficient_norm _ _ _ _)

lemma jointFixed_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ m₁ m₂ : O)
    (h₁ : n₁-m₁∈jointFixedModulus S hS) (h₂ : n₂-m₂∈jointFixedModulus S hS) :
    jointFixed S hS σ C u a b r hr n₁ n₂=jointFixed S hS σ C u a b r hr m₁ m₂ := by
  have hc₁ := primaryCoefficient_periodic S hS σ (C*n₁) (C*m₁)
    (by rw [←mul_sub];exact (jointFixedModulus S hS).mul_mem_left C h₁)
  have hc₂ := primaryCoefficient_periodic S hS σ (C*n₂) (C*m₂)
    (by rw [←mul_sub];exact (jointFixedModulus S hS).mul_mem_left C h₂)
  have hb₁ := numeratorBadTwist_periodic u a b r ((supported_iff_native _).mp hr) n₁ m₁ (Ideal.mul_le_left h₁)
  have hb₂ := numeratorBadTwist_periodic (-u) a b r ((supported_iff_native _).mp hr) n₂ m₂ (Ideal.mul_le_left h₂)
  have hfour (x y : O) (h : x-y∈jointFixedModulus S hS) : (4:O)∣x-y :=
    (show (4:O)∣72 from ⟨18,by norm_num⟩).trans (Ideal.mem_span_singleton.mp (Ideal.mul_le_left h))
  have hp : sexticReciprocityPhase n₁ n₂=sexticReciprocityPhase m₁ m₂ := by
    rw [sexticReciprocityPhase_congr_right n₁ n₂ m₂ (hfour _ _ h₂),
      sexticReciprocityPhase_comm n₁ m₂,
      sexticReciprocityPhase_congr_right m₂ n₁ m₁ (hfour _ _ h₁),
      sexticReciprocityPhase_comm m₂ m₁]
  simp only [jointFixed,hc₁,hc₂,hb₁,hb₂,hp]

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open ProbePhysical _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

def jointExtension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ) (n₁ n₂ : O) : ℂ :=
  jointFixed S hS σ C u a b r hr n₁ n₂*
    (idealRowHom n₁ (Ideal.span {r})*star (idealRowHom n₂ (Ideal.span {r})))*
      globalExtension P hg c n₁ n₂ k

lemma jointExtension_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ) (hc : ∀i,1≤ c i)
    (n₁ n₂ : O) : ‖jointExtension S hS σ C k u a b r hr P hg c n₁ n₂‖≤ Ideal.absNorm (∏i,P i^c i) := by
  rw [jointExtension,norm_mul]
  have ha : ‖jointFixed S hS σ C u a b r hr n₁ n₂*
      (idealRowHom n₁ (Ideal.span {r})*star (idealRowHom n₂ (Ideal.span {r})))‖≤1 := by
    rw [norm_mul,norm_mul,norm_star]
    exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (jointFixed_norm _ _ _ _ _ _ _ _ _ _ _)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans (idealRowHom_norm _ _))
  exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using globalExtension_norm P hg c hc n₁ n₂ k)

def jointPeriod (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (P : ι→ Id) (r : O) : Id :=
  jointFixedModulus S hS*(∏i,P i)*Ideal.span {r}

lemma jointExtension_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (n₁ n₂ m₁ m₂ : O) (h₁ : n₁-m₁∈jointPeriod S hS P r) (h₂ : n₂-m₂∈jointPeriod S hS P r) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      jointExtension S hS σ C k u a b r hr P hg c m₁ m₂ := by
  have hf := jointFixed_periodic S hS σ C u a b r hr n₁ n₂ m₁ m₂
    (Ideal.mul_le_right (Ideal.mul_le_right h₁)) (Ideal.mul_le_right (Ideal.mul_le_right h₂))
  have hm₁ := idealRowHom_congr_mod (Ideal.span {r}) n₁ m₁ (Ideal.mul_le_left h₁)
  have hm₂ := idealRowHom_congr_mod (Ideal.span {r}) n₂ m₂ (Ideal.mul_le_left h₂)
  have he := globalExtension_periodic P hg c n₁ n₂ m₁ m₂ k k
    (Ideal.mul_le_left (Ideal.mul_le_right h₁)) (Ideal.mul_le_left (Ideal.mul_le_right h₂)) (by simp)
  simp only [jointExtension,hf,hm₁,hm₂,he]

lemma jointExtension_dilation_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (d n₁ n₂ m₁ m₂ : O) (h₁ : n₁-m₁∈jointPeriod S hS P r) (h₂ : n₂-m₂∈jointPeriod S hS P r) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)=
      jointExtension S hS σ C k u a b r hr P hg c (d*m₁) (d*m₂) := by
  apply jointExtension_periodic
  · rw [←mul_sub];exact (jointPeriod S hS P r).mul_mem_left d h₁
  · rw [←mul_sub];exact (jointPeriod S hS P r).mul_mem_left d h₂

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open ProbePhysical _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation CenteredMomentCorrelation
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

theorem jointExtension_source (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (hC : Supported (Ideal.span {C}))
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : lambda^2∣r-1) (hk : k=u.val*lambda^a*(2:O)^b*r)
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (hcop : Pairwise (Function.onFun IsCoprime P))
    (he : Ideal.span {C}=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ : O) (h₁ : Supported (Ideal.span {n₁})) (h₂ : Supported (Ideal.span {n₂}))
    (hp₁ : lambda^2∣n₁-1) (hp₂ : lambda^2∣n₂-1) (hn : IsCoprime n₁ n₂) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      primaryCoefficient S hS σ (C*n₁)*star (primaryCoefficient S hS σ (C*n₂))*
        actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
          (supported_mul_elements C n₂ hC h₂) (C*k) := by
  rw [actual_common_lift C n₁ n₂ k hC h₁ h₂ hp₁ hp₂ hn,
    actualCommon_eq_globalExtension C hC P hg c hc hcop he n₁ n₂ k hn,
    ←numeratorExtension_primary u a b r k n₁ hr hpr hk h₁ hp₁,
    ←numeratorExtension_neg_primary u a b r k n₂ hr hpr hk h₂ hp₂]
  simp only [jointExtension,jointFixed,numeratorExtension,MonoidHom.mul_apply,
    movingNumeratorRow,MonoidHom.coe_mk,OneHom.coe_mk,star_mul]
  ring

lemma lowGramCoefficient_eq_primary (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (s : {I : Id // Supported I}) :
    lowGramCoefficient (calibrationForSet S hS) σ s=
      primaryCoefficient S hS σ (primaryIdealGenerator s.val) := by
  have hp : lambda^2∣primaryIdealGenerator s.val-1 := (primaryIdealGenerator_spec s.val
    (supported_primaryIdealGenerator_ne_zero s.val s.property)).2
  rw [primaryCoefficient,if_pos hp]
  exact lowGramCoefficient_eq_extension S hS hbad σ s

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open ProbePhysical _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open  CenteredMomentCorrelation
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

def jointRemainder (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (J : Id) (n₁ n₂ : O) : ℂ :=
  jointFixed S hS σ C u a b r hr n₁ n₂*
    (idealRowHom n₁ J*star (idealRowHom n₂ (Ideal.span {r})))*globalExtension P hg c n₁ n₂ k

theorem jointExtension_local_factor (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (J p : Id) [p.IsMaximal] (hgp : lambda∉p) (e : ℕ) (he : e≠0)
    (hfactor : Ideal.span {r}=J*p^e) (n₁ n₂ : O) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      (complexSexticChar p hgp^e) (Ideal.Quotient.mk p n₁)*
        jointRemainder S hS σ C k u a b r hr P hg c J n₁ n₂ := by
  have hf : idealRowHom n₁ (Ideal.span {r})=
      idealRowHom n₁ J*(complexSexticChar p hgp^e) (Ideal.Quotient.mk p n₁) := by
    rw [hfactor,map_mul,map_pow,idealRowHom_prime n₁ p hgp,MulChar.pow_apply' _ he]
  rw [jointExtension,hf,jointRemainder]
  ring

lemma jointRemainder_periodic_first (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (J : Id) (n m y : O) (h : n-m∈jointFixedModulus S hS*(∏i,P i)*J) :
    jointRemainder S hS σ C k u a b r hr P hg c J n y=
      jointRemainder S hS σ C k u a b r hr P hg c J m y := by
  have hf := jointFixed_periodic S hS σ C u a b r hr n y m y
    (Ideal.mul_le_right (Ideal.mul_le_right h)) (by simp)
  have hm := idealRowHom_congr_mod J n m (Ideal.mul_le_left h)
  have hg' := globalExtension_periodic P hg c n y m y k k
    (Ideal.mul_le_left (Ideal.mul_le_right h)) (by simp) (by simp)
  simp only [jointRemainder,hf,hm,hg']

theorem jointExtension_mean_zero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (J p : Id) [p.IsMaximal] (hgp : lambda∉p) (hchar : ringChar (O⧸p)≠2)
    (e : ℕ) (he : ¬6∣e) (hfactor : Ideal.span {r}=J*p^e)
    (hcop : IsCoprime (jointFixedModulus S hS*(∏i,P i)*J) (p^e))
    [Fintype (O⧸jointFixedModulus S hS*(∏i,P i)*J)] [Fintype (O⧸p^e)]
    [Fintype (O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e)] (d : O) :
    (∑x : O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e,
      ∑y : O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e,
        jointExtension S hS σ C k u a b r hr P hg c (d*x.out) (d*y.out))=0 := by
  have he0 : e≠0 := by intro h;exact he (h ▸ dvd_zero 6)
  have he1 : 1≤ e := Nat.one_le_iff_ne_zero.mpr he0
  simp_rw [jointExtension_local_factor S hS σ C k u a b r hr P hg c J p hgp e he0 hfactor]
  apply joint_mean_of_local_factor _ p hgp hchar e e he1 he hcop
    (fun x y=> jointRemainder S hS σ C k u a b r hr P hg c J (d*x) (d*y)) _ d
  intro x z y hxz
  apply jointRemainder_periodic_first
  rw [←mul_sub]
  exact (jointFixedModulus S hS*(∏i,P i)*J).mul_mem_left d hxz

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

lemma common_radical_norm_le (C : O) (hC : C≠0) (P : ι→ Id) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (∏i,P i)≤ Ideal.absNorm (Ideal.span {C}) := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hC)))
  apply map_dvd Ideal.absNorm
  rw [he]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=> dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (hc i)))

lemma jointPeriod_norm_bound (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hk : k=u.val*lambda^a*(2:O)^b*r) (P : ι→ Id) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (jointPeriod S hS P r)≤
      Ideal.absNorm (jointFixedModulus S hS)*Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) := by
  rw [jointPeriod,map_mul,map_mul]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (common_radical_norm_le C hC P c hc he))
    (numerator_good_norm_le u a b r k hk hk0)

lemma jointPeriod_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C : O) (hC : C≠0) (P : ι→ Id) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (he : Ideal.span {C}=∏i,P i^c i) (r : O) (hr : r≠0) :
    jointPeriod S hS P r≠0 := by
  have hp : ∏i,P i≠(0:Id) := by
    intro hz
    have hd : (∏i,P i)∣Ideal.span {C} := by
      rw [he]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=> dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (hc i)))
    rw [hz,zero_dvd_iff] at hd
    exact hC (Ideal.span_singleton_eq_bot.mp hd)
  exact mul_ne_zero (mul_ne_zero (jointFixedModulus_nonzero S hS) hp)
    (Ideal.span_singleton_eq_bot.not.mpr hr)

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open UniqueFactorizationMonoid
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma maximal_coprime_of_not_dvd (p J : Id) [p.IsMaximal] (h : ¬p∣J) : IsCoprime J p := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  have he : p=J⊔p := Ideal.IsMaximal.eq_of_le inferInstance htop le_sup_right
  apply h
  apply Ideal.dvd_iff_le.mpr
  rw [he]
  exact le_sup_left

theorem exists_prime_separation (I p : Id) (hI : I≠0) [p.IsMaximal] (hp0 : p≠0) :
    ∃J : Id,I=J*p^((normalizedFactors I).count p) ∧ IsCoprime J p ∧ J≠0 := by
  have hp : Prime p := Ideal.prime_of_isPrime hp0 inferInstance
  obtain ⟨J,hJ,hnd⟩ := (FiniteMultiplicity.of_prime_left hp hI).exists_eq_pow_mul_and_not_dvd
  have he : multiplicity p I=(normalizedFactors I).count p := by
    simpa only [normalize_eq] using multiplicity_eq_count_normalizedFactors hp.irreducible hI
  refine ⟨J,?_,maximal_coprime_of_not_dvd p J hnd,?_⟩
  · rw [←he,mul_comm]
    exact hJ
  · intro hz
    rw [hz,mul_zero] at hJ
    exact hI hJ

theorem exists_nonexceptional_separation (L R I p : Id) (hI : I≠0)
    [p.IsMaximal] (hp0 : p≠0) (hL : ¬p∣L) (hR : ¬p∣R) :
    ∃J : Id,I=J*p^((normalizedFactors I).count p) ∧
      IsCoprime (L*R*J) (p^((normalizedFactors I).count p)) ∧ J≠0 := by
  obtain ⟨J,hJ,hcop,hJ0⟩ := exists_prime_separation I p hI hp0
  exact ⟨J,hJ,((maximal_coprime_of_not_dvd p L hL).mul_left
    (maximal_coprime_of_not_dvd p R hR)).mul_left hcop |>.pow_right,hJ0⟩

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open  UniqueFactorizationMonoid
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

theorem exists_nonexceptional_residue (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : Supported (Ideal.span {r})) (hk : k=u.val*lambda^a*(2:O)^b*r)
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (hfac : Ideal.span {C}=∏i,P i^c i)
    (p : Id) [p.IsMaximal] (hp0 : p≠0) (hgp : lambda∉p)
    (hchar : ringChar (O⧸p)≠2) (hfixed : ¬p∣jointFixedModulus S hS) (hcommon : ¬p∣∏i,P i)
    (he : ¬6∣(normalizedFactors (Ideal.span {r})).count p) :
    ∃(M : Id)(hM : M≠0),
      Ideal.absNorm M≤ Ideal.absNorm (jointFixedModulus S hS)*
        Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) ∧
      letI : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient hM
      letI : Fintype (O⧸M):=Fintype.ofFinite _
      ∀d : O,∃A : (O⧸M)→(O⧸M)→ℂ,
        (∀n₁ n₂,A (Ideal.Quotient.mk M n₁) (Ideal.Quotient.mk M n₂)=
          jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)) ∧
        (∀x y,‖A x y‖≤ Ideal.absNorm (Ideal.span {C})) ∧
        (∑x,∑y,A x y)=0 := by
  obtain ⟨J,hJ,hcop,hJ0⟩ := exists_nonexceptional_separation (jointFixedModulus S hS)
    (∏i,P i) (Ideal.span {r}) p hr.1 hp0 hfixed hcommon
  let e := (normalizedFactors (Ideal.span {r})).count p
  let M : Id := (jointFixedModulus S hS*(∏i,P i)*J)*p^e
  have hMperiod : M=jointPeriod S hS P r := by
    rw [jointPeriod,hJ]
    dsimp [M,e]
    ring
  have hM0 : M≠0 := hMperiod ▸ jointPeriod_nonzero S hS C hC P c hc hfac r
    (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr)
  refine ⟨M,hM0,?_,?_⟩
  · rw [hMperiod]
    exact jointPeriod_norm_bound S hS C k hC hk0 u a b r hk P c hc hfac
  · let : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM0
    let : Fintype (O⧸M) := Fintype.ofFinite _
    let : Finite (O⧸jointFixedModulus S hS*(∏i,P i)*J) :=
      Ring.HasFiniteQuotients.finiteQuotient (left_ne_zero_of_mul hM0)
    let : Fintype (O⧸jointFixedModulus S hS*(∏i,P i)*J) := Fintype.ofFinite _
    let : Finite (O⧸p^e) := Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ hp0)
    let : Fintype (O⧸p^e) := Fintype.ofFinite _
    intro d
    let A : (O⧸M)→(O⧸M)→ℂ := fun x y=>
      jointExtension S hS σ C k u a b r hr P hg c (d*x.out) (d*y.out)
    refine ⟨A,?_,?_,?_⟩
    · intro n₁ n₂
      apply jointExtension_dilation_periodic
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk M n₁))
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk M n₂))
    · intro x y
      rw [hfac]
      exact jointExtension_norm S hS σ C k u a b r hr P hg c hc _ _
    · exact jointExtension_mean_zero S hS σ C k u a b r hr P hg c J p hgp hchar e he hJ hcop d

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
abbrev SupportedIdeal := {I : Id // Supported I}

lemma gram_supported_divisor (I D : Id) (hI : Supported I) (hd : D∣I) : Supported D := by
  obtain ⟨J,rfl⟩ := hd
  exact (supported_mul_iff D J).mp hI |>.1

lemma gram_supported_quotient (I D : Id) (hI : Supported I) (hd : D∣I) :
    Supported (quadraticIdealQuotient D I) := gram_supported_divisor I _ hI (quadraticIdealQuotient_dvd hd)

def gcdCommon (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨gcd I.val J.val,gram_supported_divisor I.val _ I.property (gcd_dvd_left _ _)⟩

def gcdLeft (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨quadraticIdealQuotient (gcdCommon I J).val I.val,
    gram_supported_quotient I.val _ I.property (gcd_dvd_left _ _)⟩

def gcdRight (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨quadraticIdealQuotient (gcdCommon I J).val J.val,
    gram_supported_quotient J.val _ J.property (gcd_dvd_right _ _)⟩

lemma gcd_residual_coprime (I J : SupportedIdeal) : IsCoprime (gcdLeft I J).val (gcdRight I J).val :=
  (CubicSieve.gcd_eq_iff_quotient_coprime _ _ _ (gcdCommon I J).property.1
    (gcd_dvd_left _ _) (gcd_dvd_right _ _)).mp rfl

lemma gcd_common_left (I J : SupportedIdeal) : (gcdCommon I J).val*(gcdLeft I J).val=I.val :=
  quadraticIdeal_mul_quotient (gcd_dvd_left _ _)

lemma gcd_common_right (I J : SupportedIdeal) : (gcdCommon I J).val*(gcdRight I J).val=J.val :=
  quadraticIdeal_mul_quotient (gcd_dvd_right _ _)

abbrev CoprimeTriple := {t : SupportedIdeal×SupportedIdeal×SupportedIdeal // IsCoprime t.2.1.val t.2.2.val}

def gcdTriple (p : SupportedIdeal×SupportedIdeal) : CoprimeTriple :=
  ⟨(gcdCommon p.1 p.2,gcdLeft p.1 p.2,gcdRight p.1 p.2),gcd_residual_coprime p.1 p.2⟩

def multiplyTriple (t : CoprimeTriple) : SupportedIdeal×SupportedIdeal :=
  (⟨t.val.1.val*t.val.2.1.val,(supported_mul_iff _ _).mpr ⟨t.val.1.property,t.val.2.1.property⟩⟩,
   ⟨t.val.1.val*t.val.2.2.val,(supported_mul_iff _ _).mpr ⟨t.val.1.property,t.val.2.2.property⟩⟩)

lemma multiply_gcdTriple (p : SupportedIdeal×SupportedIdeal) : multiplyTriple (gcdTriple p)=p := by
  apply Prod.ext <;> apply Subtype.ext
  · exact gcd_common_left _ _
  · exact gcd_common_right _ _

lemma gcdTriple_multiply (t : CoprimeTriple) : gcdTriple (multiplyTriple t)=t := by
  have he : gcd (t.val.1.val*t.val.2.1.val) (t.val.1.val*t.val.2.2.val)=t.val.1.val := by
    rw [_root_.gcd_mul_left,normalize_eq,Ideal.isCoprime_iff_gcd.mp t.property,mul_one]
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext he
  · apply Prod.ext <;> apply Subtype.ext
    · change quadraticIdealQuotient (gcd _ _) (t.val.1.val*t.val.2.1.val)=t.val.2.1.val
      dsimp only [multiplyTriple]
      rw [he]
      exact mul_left_cancel₀ t.val.1.property.1 (quadraticIdeal_mul_quotient (dvd_mul_right _ _))
    · change quadraticIdealQuotient (gcd _ _) (t.val.1.val*t.val.2.2.val)=t.val.2.2.val
      dsimp only [multiplyTriple]
      rw [he]
      exact mul_left_cancel₀ t.val.1.property.1 (quadraticIdeal_mul_quotient (dvd_mul_right _ _))

/-- Separate a pair of supported ideals into its gcd and coprime residual factors. -/
def gcdPairEquiv : (SupportedIdeal×SupportedIdeal)≃CoprimeTriple where
  toFun := gcdTriple
  invFun := multiplyTriple
  left_inv := multiply_gcdTriple
  right_inv := gcdTriple_multiply

lemma gcdPair_tsum (f : SupportedIdeal×SupportedIdeal→ℂ) :
    (∑'p,f p)=∑'t : CoprimeTriple,f (multiplyTriple t) := by
  exact (gcdPairEquiv.symm.tsum_eq f).symm

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation
local notation "O" => Eisenstein.O

lemma actual_common_frequency_zero (C n₁ n₂ j : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (hj : ¬C∣j) :
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) j=0 := by
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero (supported_element_ne_zero C hC) (supported_element_ne_zero n₁ h₁))
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero (supported_element_ne_zero C hC) (supported_element_ne_zero n₂ h₂))
  let : Fintype (O⧸Ideal.span {C*n₁}) := Fintype.ofFinite _
  let : Fintype (O⧸Ideal.span {C*n₂}) := Fintype.ofFinite _
  exact fullModulusCorrelation_eq_zero_of_common_not_dvd _ _ C j _ _
    (dvd_mul_right _ _) (dvd_mul_right _ _) hj

lemma tsum_element_divisible (C : O) (hC : C≠0) (f : O→ℂ) :
    (∑'j : O,if C∣j then f j else 0)=∑'k : O,f (C*k) := by
  have hinj : Function.Injective (fun k : O=> C*k) := fun _ _ h=> mul_left_cancel₀ hC h
  have hs : Function.support (fun j : O=> if C∣j then f j else 0)⊆Set.range (fun k : O=> C*k) := by
    intro j hj
    have hd : C∣j := by by_contra h;simp [h] at hj
    obtain ⟨k,rfl⟩ := hd
    exact ⟨k,rfl⟩
  have ht := hinj.tsum_eq hs
  calc
    _ = ∑'k : O,if C∣C*k then f (C*k) else 0 := ht.symm
    _ = _ := by simp only [dvd_mul_right,ite_true]

theorem actual_common_frequency_tsum (C n₁ n₂ : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (W : O→ℂ) :
    (∑'j : O,actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) j*W j)=
      ∑'k : O,actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
        (supported_mul_elements C n₂ hC h₂) (C*k)*W (C*k) := by
  rw [←tsum_element_divisible C (supported_element_ne_zero C hC) (fun j=>
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) j*W j)]
  apply tsum_congr
  intro j
  by_cases hj : C∣j
  · rw [if_pos hj]
  · rw [if_neg hj,actual_common_frequency_zero C n₁ n₂ j hC h₁ h₂ hj,zero_mul]

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation SchwartzPlanePoisson
local notation "O" => Eisenstein.O

lemma gcd_generator_left (I J : SupportedIdeal) :
    primaryIdealGenerator I.val=primaryIdealGenerator (gcdCommon I J).val*primaryIdealGenerator (gcdLeft I J).val := by
  rw [←primaryIdealGenerator_mul,gcd_common_left]

lemma gcd_generator_right (I J : SupportedIdeal) :
    primaryIdealGenerator J.val=primaryIdealGenerator (gcdCommon I J).val*primaryIdealGenerator (gcdRight I J).val := by
  rw [←primaryIdealGenerator_mul,gcd_common_right]

lemma gcd_generator_coprime (I J : SupportedIdeal) :
    IsCoprime (primaryIdealGenerator (gcdLeft I J).val) (primaryIdealGenerator (gcdRight I J).val) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [(primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ (gcdLeft I J).property)).1,
    (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ (gcdRight I J).property)).1]
  exact gcd_residual_coprime I J

theorem actual_gcd_lift (I J : SupportedIdeal) (k : O) :
    let C:=primaryIdealGenerator (gcdCommon I J).val
    let n₁:=primaryIdealGenerator (gcdLeft I J).val
    let n₂:=primaryIdealGenerator (gcdRight I J).val
    actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
      ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
      ((supported_span_primaryIdealGenerator_iff _).mpr J.property) (C*k)=
      idealRowHom k (gcdLeft I J).val*star (idealRowHom (-k) (gcdRight I J).val)*
        sexticReciprocityPhase n₁ n₂*
          actualCommon C ((supported_span_primaryIdealGenerator_iff _).mpr (gcdCommon I J).property) n₁ n₂ k := by
  dsimp only
  have h₁ := (supported_span_primaryIdealGenerator_iff _).mpr (gcdLeft I J).property
  have h₂ := (supported_span_primaryIdealGenerator_iff _).mpr (gcdRight I J).property
  have hp₁ : lambda^2∣primaryIdealGenerator (gcdLeft I J).val-1 :=
    (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ (gcdLeft I J).property)).2
  have hp₂ : lambda^2∣primaryIdealGenerator (gcdRight I J).val-1 :=
    (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ (gcdRight I J).property)).2
  have hh := actual_common_lift (primaryIdealGenerator (gcdCommon I J).val)
    (primaryIdealGenerator (gcdLeft I J).val) (primaryIdealGenerator (gcdRight I J).val) k
    ((supported_span_primaryIdealGenerator_iff _).mpr (gcdCommon I J).property) h₁ h₂ hp₁ hp₂
    (gcd_generator_coprime I J)
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J,
    (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ (gcdLeft I J).property)).1,
    (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ (gcdRight I J).property)).1] using hh

theorem actual_gcd_frequency_source (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    (∑'h : O,actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
      ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
      ((supported_span_primaryIdealGenerator_iff _).mpr J.property) (-h)*
      paperRadialFourier U (Q*‖ringComplex h‖^2/‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2))=
      ∑'k : O,actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
        ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
        ((supported_span_primaryIdealGenerator_iff _).mpr J.property) (primaryIdealGenerator (gcdCommon I J).val*k)*
        paperRadialFourier U (Q*‖ringComplex (primaryIdealGenerator (gcdCommon I J).val*k)‖^2/
          ‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2) := by
  have hneg := (Equiv.neg O).tsum_eq (fun h : O=>
    actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
      ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
      ((supported_span_primaryIdealGenerator_iff _).mpr J.property) h*
      paperRadialFourier U (Q*‖ringComplex h‖^2/‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2))
  simp only [Equiv.neg_apply,map_neg,norm_neg] at hneg
  rw [hneg]
  have hh := actual_common_frequency_tsum (primaryIdealGenerator (gcdCommon I J).val)
    (primaryIdealGenerator (gcdLeft I J).val) (primaryIdealGenerator (gcdRight I J).val)
    ((supported_span_primaryIdealGenerator_iff _).mpr (gcdCommon I J).property)
    ((supported_span_primaryIdealGenerator_iff _).mpr (gcdLeft I J).property)
    ((supported_span_primaryIdealGenerator_iff _).mpr (gcdRight I J).property)
    (fun h=> paperRadialFourier U (Q*‖ringComplex h‖^2/
      ‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2))
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J] using hh

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

abbrev DivisibleSupported (D : SupportedIdeal) := {I : SupportedIdeal // D.val∣I.val}

def supportedIdealProduct (D J : SupportedIdeal) : SupportedIdeal :=
  ⟨D.val*J.val,(supported_mul_iff _ _).mpr ⟨D.property,J.property⟩⟩

def supportedDilationEquiv (D : SupportedIdeal) : SupportedIdeal≃DivisibleSupported D where
  toFun J := ⟨supportedIdealProduct D J,dvd_mul_right _ _⟩
  invFun I := ⟨quadraticIdealQuotient D.val I.val.val,gram_supported_quotient I.val.val D.val I.val.property I.property⟩
  left_inv J := by
    apply Subtype.ext
    exact mul_left_cancel₀ D.property.1 (quadraticIdeal_mul_quotient (dvd_mul_right D.val J.val))
  right_inv I := by
    apply Subtype.ext
    apply Subtype.ext
    exact quadraticIdeal_mul_quotient I.property

lemma supported_dilation_generator (D J : SupportedIdeal) :
    primaryIdealGenerator (supportedIdealProduct D J).val=primaryIdealGenerator D.val*primaryIdealGenerator J.val :=
  primaryIdealGenerator_mul _ _

lemma supported_dilation_norm (D J : SupportedIdeal) :
    Ideal.absNorm (supportedIdealProduct D J).val=Ideal.absNorm D.val*Ideal.absNorm J.val :=
  map_mul Ideal.absNorm _ _

theorem supported_divisor_tsum (D : SupportedIdeal) (f : SupportedIdeal→ℂ) :
    (∑'I : SupportedIdeal,if D.val∣I.val then f I else 0)=
      ∑'J : SupportedIdeal,f (supportedIdealProduct D J) := by
  change (∑'I : SupportedIdeal,({I : SupportedIdeal | D.val∣I.val}.indicator f) I)=_
  rw [←tsum_subtype (s:={I : SupportedIdeal | D.val∣I.val}) (f:=f)]
  exact (supportedDilationEquiv D).tsum_eq (fun I : DivisibleSupported D=> f I.val) |>.symm

theorem supported_divisor_pair_tsum (D : SupportedIdeal) (f : SupportedIdeal→ SupportedIdeal→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      if D.val∣I.val ∧ D.val∣J.val then f I J else 0)=
      ∑'I : SupportedIdeal,∑'J : SupportedIdeal,
        f (supportedIdealProduct D I) (supportedIdealProduct D J) := by
  have hinner (I : SupportedIdeal) : (∑'J : SupportedIdeal,if D.val∣I.val ∧ D.val∣J.val then f I J else 0)=
      if D.val∣I.val then ∑'J : SupportedIdeal,f I (supportedIdealProduct D J) else 0 := by
    by_cases hI : D.val∣I.val
    · simp only [hI,true_and,ite_true]
      exact supported_divisor_tsum D (f I)
    · simp [hI]
  simp_rw [hinner]
  exact supported_divisor_tsum D (fun I=>∑'J : SupportedIdeal,f I (supportedIdealProduct D J))

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramLatticeDecay
open Eisenstein  SchwartzPlanePoisson
local notation "O" => Eisenstein.O

abbrev Joint := WithLp 2 (ℂ × ℂ)

def point (x y : ℂ) : Joint := WithLp.toLp 2 (x,y)

def sourceControl (S : Finset (ℕ × ℕ)) (W : 𝓢(Joint, ℂ)) : ℝ :=
  S.sup (schwartzSeminormFamily ℝ Joint ℂ) W

theorem sourceControl_nonneg (S : Finset (ℕ × ℕ)) (W : 𝓢(Joint, ℂ)) :
    0 ≤ sourceControl S W := apply_nonneg _ _

@[simp] theorem norm_point_sq (x y : ℂ) :
    ‖point x y‖^2 = ‖x‖^2 + ‖y‖^2 := WithLp.prod_norm_sq_eq_of_L2 _

theorem product_decay (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ((1+‖x‖^2)^2 * (1+‖y‖^2)^2) * ‖W (point x y)‖ ≤
      (2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W := by
  have hx := WithLp.norm_fst_le ℂ (point x y)
  have hy := WithLp.norm_snd_le ℂ (point x y)
  change ‖x‖ ≤ ‖point x y‖ at hx
  change ‖y‖ ≤ ‖point x y‖ at hy
  have hx2 : 1+‖x‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hy2 : 1+‖y‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hpow : (1+‖x‖^2)^2 * (1+‖y‖^2)^2 ≤ (1+‖point x y‖)^8 := by
    calc
      _ ≤ ((1+‖point x y‖)^2)^2 * ((1+‖point x y‖)^2)^2 := by gcongr
      _ = _ := by ring
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (8,0)) (k := 8) (n := 0) le_rfl le_rfl W (point x y)
  simp only [norm_iteratedFDeriv_zero] at h
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans h

def physicalPoint (N : ℝ) (m : O × O) : Joint :=
  point (ringComplex m.1 / (Real.sqrt N : ℂ))
    (ringComplex m.2 / (Real.sqrt N : ℂ))

theorem physicalPoint_eq_smul (N : ℝ) (m : O × O) :
    physicalPoint N m = (Real.sqrt N)⁻¹ • point (ringComplex m.1) (ringComplex m.2) := by
  apply WithLp.ofLp_injective
  simp [physicalPoint, point, div_eq_mul_inv, Algebra.smul_def, mul_comm]

theorem physical_summable (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N) :
    Summable (fun m : O × O => ‖W (physicalPoint N m)‖) := by
  let g : O → ℝ := fun m => ((1+N⁻¹*‖ringComplex m‖^2)^2)⁻¹
  have hg : Summable g := scaled_eisenstein_cauchy_summable _ (inv_pos.mpr hN)
  have hp := hg.mul_of_nonneg hg (fun _ => by dsimp [g]; positivity)
    (fun _ => by dsimp [g]; positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hp.mul_left ((2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W))
  intro m
  have hb := product_decay W (ringComplex m.1 / (Real.sqrt N : ℂ))
    (ringComplex m.2 / (Real.sqrt N : ℂ))
  have hnorm (m : O) : ‖ringComplex m / (Real.sqrt N : ℂ)‖^2 = N⁻¹*‖ringComplex m‖^2 := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hN.le]
    ring
  simp only [hnorm] at hb
  change ‖W (physicalPoint N m)‖ ≤ ((2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W) * (g m.1*g m.2)
  dsimp only [g]
  rw [ ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [physicalPoint, mul_comm] using hb

theorem physical_lattice_bound :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (N : ℝ), 1 ≤ N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2 := by
  refine ⟨Finset.Iic (8,0), (2:ℝ)^8 * (4*(1+Real.pi)^2)^2, by positivity, ?_⟩
  intro W N hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let g : O → ℝ := fun m => ((1+N⁻¹*‖ringComplex m‖^2)^2)⁻¹
  have hg : Summable g := scaled_eisenstein_cauchy_summable _ (inv_pos.mpr hNp)
  have hp := hg.mul_of_nonneg hg (fun _ => by dsimp [g]; positivity)
    (fun _ => by dsimp [g]; positivity)
  have hpoint (m : O × O) : ‖W (physicalPoint N m)‖ ≤
      ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W) * (g m.1*g m.2) := by
    have hb := product_decay W (ringComplex m.1 / (Real.sqrt N : ℂ))
      (ringComplex m.2 / (Real.sqrt N : ℂ))
    have hn (m : O) : ‖ringComplex m / (Real.sqrt N : ℂ)‖^2 = N⁻¹*‖ringComplex m‖^2 := by
      rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hNp.le]
      ring
    simp only [hn] at hb
    dsimp only [g]
    rw [ ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    simpa only [physicalPoint, mul_comm] using hb
  have hmass : (∑' m : O, g m) ≤ (4*(1+Real.pi)^2)*N := by
    have h := scaled_eisenstein_cauchy_small N⁻¹ (inv_pos.mpr hNp) ((inv_le_one₀ hNp).mpr hN)
    have hh := mul_le_mul_of_nonneg_left h hNp.le
    simpa only [g, ← mul_assoc, mul_inv_cancel₀ hNp.ne', one_mul, mul_comm] using hh
  calc
    _ ≤ ∑' m : O × O, ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(g m.1*g m.2) :=
      (physical_summable W N hNp).tsum_le_tsum hpoint (hp.mul_left _)
    _ = ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(∑' m : O, g m)^2 := by
      rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, pow_two]
    _ ≤ ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*((4*(1+Real.pi)^2)*N)^2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (sourceControl_nonneg _ _))
      exact pow_le_pow_left₀ (tsum_nonneg (fun _ => by dsimp [g]; positivity)) hmass 2
    _ = _ := by ring

abbrev DualIndex := (ℤ × ℤ) × (ℤ × ℤ)

def dualPoint (p : DualIndex) : Joint :=
  point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)

def dualRow (p : DualIndex) : Fin 2 → O :=
  ![dualFrequencyEquiv p.1, dualFrequencyEquiv p.2]

def dualCoordinates (p : DualIndex) : (Fin 2 × Fin 2) → ℤ :=
  CubicEisenstein.rowCoordinates (dualRow p)

theorem dualCoordinates_injective : Function.Injective dualCoordinates := by
  intro p q hp
  have h := CubicEisenstein.rowCoordinates_injective hp
  apply Prod.ext
  · exact dualFrequencyEquiv.injective (congrFun h 0)
  · exact dualFrequencyEquiv.injective (congrFun h 1)

@[simp] theorem dualCoordinates_zero : dualCoordinates 0 = 0 := by
  have hzero : Eisenstein.Coordinates.coords (0 : O) = (0,0) := by
    simpa [Eisenstein.Coordinates.eval] using Eisenstein.Coordinates.coords_eval 0 0
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [dualCoordinates, CubicEisenstein.rowCoordinates, dualRow,
      dualFrequencyEquiv, Eisenstein.Coordinates.coordinateEquiv, Eisenstein.Coordinates.eval, hzero]

theorem dualCoordinates_norm_le (p : DualIndex) :
    ‖dualCoordinates p‖ ≤ 2 * ‖dualPoint p‖ := by
  have hc := CubicEisenstein.coordinates_norm_bound (dualRow p)
  have hp : ‖fun i => ringComplex (dualRow p i)‖ ≤ ‖dualPoint p‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h1 := explicitDualFrequency_norm_sq 1 p.1
    have h2 := explicitDualFrequency_norm_sq 1 p.2
    norm_num only [norm_one, one_pow, div_one] at h1 h2
    have hq := norm_point_sq (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)
    fin_cases i
    · change ‖ringComplex (dualFrequencyEquiv p.1)‖ ≤ ‖dualPoint p‖
      dsimp only [dualPoint]
      nlinarith [sq_nonneg ‖ringComplex (dualFrequencyEquiv p.2)‖,
        norm_nonneg (point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)),
        norm_nonneg (ringComplex (dualFrequencyEquiv p.1))]
    · change ‖ringComplex (dualFrequencyEquiv p.2)‖ ≤ ‖dualPoint p‖
      dsimp only [dualPoint]
      nlinarith [sq_nonneg ‖ringComplex (dualFrequencyEquiv p.1)‖,
        norm_nonneg (point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)),
        norm_nonneg (ringComplex (dualFrequencyEquiv p.2))]
  exact hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num))

theorem dualPoint_norm_pos (p : DualIndex) (hp : p ≠ 0) : 0 < ‖dualPoint p‖ := by
  have hc : dualCoordinates p ≠ 0 := by
    intro h
    exact hp (dualCoordinates_injective (h.trans dualCoordinates_zero.symm))
  have hh := norm_pos_iff.mpr hc
  have hb := dualCoordinates_norm_le p
  linarith

theorem dual_power_summable (k : ℝ) (hk : 4 < k) :
    Summable (fun p : {p : DualIndex // p ≠ 0} => ‖dualPoint p.val‖ ^ (-k)) := by
  have hs : Summable (fun p : {p : DualIndex // p ≠ 0} => ‖dualCoordinates p.val‖ ^ (-k)) :=
    (CubicEisenstein.summable_integer_four_rpow k hk).comp_injective
    (dualCoordinates_injective.comp (Subtype.val_injective))
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _) _
    (hs.mul_left ((2:ℝ)^k))
  intro p
  have hc : 0 < ‖dualCoordinates p.val‖ := norm_pos_iff.mpr (by
    intro h
    exact p.property (dualCoordinates_injective (h.trans dualCoordinates_zero.symm)))
  have h := Real.rpow_le_rpow_of_nonpos (half_pos hc)
    (by have := dualCoordinates_norm_le p.val; linarith : ‖dualCoordinates p.val‖ / 2 ≤ ‖dualPoint p.val‖)
    (by linarith : -k ≤ 0)
  calc
    _ ≤ (‖dualCoordinates p.val‖ / 2) ^ (-k) := h
    _ = (2:ℝ)^k * ‖dualCoordinates p.val‖ ^ (-k) := by
      rw [Real.div_rpow (norm_nonneg _) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      simp only [div_inv_eq_mul, mul_comm]

def scaledDualPoint (L : ℝ) (u : ℂ) (p : DualIndex) : Joint :=
  point (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)

theorem norm_scaledDualPoint (L : ℝ) (hL : 0 ≤ L) (u : ℂ) (hu : ‖u‖ = 1)
    (p : DualIndex) : ‖scaledDualPoint L u p‖ = L * ‖dualPoint p‖ := by
  have h1 := norm_point_sq (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)
  have h2 := norm_point_sq (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)
  simp only [norm_mul, hu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL,
    one_mul] at h1
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  change ‖point (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)‖^2 =
      (L*‖point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)‖)^2
  simp only [h1, mul_pow, h2]
  ring

theorem fourier_seminorm_control (k : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(Joint, ℂ),
      SchwartzMap.seminorm ℝ k 0 (𝓕 W) ≤ C * sourceControl S W := by
  let T : 𝓢(Joint, ℂ) →L[ℝ] 𝓢(Joint, ℂ) := SchwartzMap.fourierTransformCLM ℝ
  let q : Seminorm ℝ 𝓢(Joint, ℂ) := (SchwartzMap.seminorm ℝ k 0).comp T.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ Joint ℂ).continuous_seminorm (k,0)).comp T.continuous
  obtain ⟨S,C,hC,hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ Joint ℂ) q hq
  refine ⟨S,C,?_,?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W
    exact Seminorm.le_def.mp hbound W

theorem scaledDual_decay (F : 𝓢(Joint, ℂ)) (k : ℕ) (L : ℝ) (hL : 0 < L)
    (u : ℂ) (hu : ‖u‖ = 1) (p : DualIndex) (hp : p ≠ 0) :
    ‖F (scaledDualPoint L u p)‖ ≤ SchwartzMap.seminorm ℝ k 0 F *
      L^(-(k:ℝ)) * ‖dualPoint p‖^(-(k:ℝ)) := by
  have hn : 0 < ‖scaledDualPoint L u p‖ := by
    rw [norm_scaledDualPoint L hL.le u hu]
    exact mul_pos hL (dualPoint_norm_pos p hp)
  have hb := SchwartzMap.norm_pow_mul_le_seminorm ℝ F k (scaledDualPoint L u p)
  have hh : ‖F (scaledDualPoint L u p)‖ ≤
      SchwartzMap.seminorm ℝ k 0 F * ‖scaledDualPoint L u p‖^(-(k:ℝ)) := by
    rw [Real.rpow_neg hn.le, Real.rpow_natCast, ← div_eq_mul_inv,
      le_div_iff₀ (pow_pos hn k)]
    simpa only [mul_comm] using hb
  rw [norm_scaledDualPoint L hL.le u hu,
    Real.mul_rpow hL.le (norm_nonneg _)] at hh
  simpa only [mul_assoc] using hh

theorem dual_fourier_summable (A : ℕ) (hA : 2 < A)
    (W : 𝓢(Joint, ℂ)) (L : ℝ) (hL : 0 < L) (u : ℂ) (hu : ‖u‖ = 1) :
    Summable (fun p : {p : DualIndex // p ≠ 0} => ‖(𝓕 W) (scaledDualPoint L u p.val)‖) := by
  have hdim : (4:ℝ) < ((2*A:ℕ):ℝ) := by exact_mod_cast (by omega : 4 < 2*A)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((dual_power_summable ((2*A:ℕ):ℝ) hdim).mul_left
      (SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ))))
  intro p
  exact scaledDual_decay (𝓕 W) (2*A) L hL u hu p.val p.property

theorem dual_fourier_lattice_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (L : ℝ), 1 ≤ L → ∀ (u : ℂ), ‖u‖ = 1 →
        (∑' p : {p : DualIndex // p ≠ 0}, ‖(𝓕 W) (scaledDualPoint L u p.val)‖) ≤
          C * sourceControl S W * L^(-((2*A:ℕ):ℝ)) := by
  obtain ⟨S,C,hC,hbound⟩ := fourier_seminorm_control (2*A)
  let mass : ℝ := ∑' p : {p : DualIndex // p ≠ 0}, ‖dualPoint p.val‖^(-((2*A:ℕ):ℝ))
  have hm : 0 ≤ mass := tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨S,C*(mass+1),mul_pos hC (by positivity),?_⟩
  intro W L hL u hu
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hdim : (4:ℝ) < ((2*A:ℕ):ℝ) := by exact_mod_cast (by omega : 4 < 2*A)
  calc
    _ ≤ ∑' p : {p : DualIndex // p ≠ 0},
        (SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ))) *
          ‖dualPoint p.val‖^(-((2*A:ℕ):ℝ)) :=
      (dual_fourier_summable A hA W L hLp u hu).tsum_le_tsum
        (fun p => scaledDual_decay (𝓕 W) (2*A) L hLp u hu p.val p.property)
        ((dual_power_summable ((2*A:ℕ):ℝ) hdim).mul_left _)
    _ = SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ)) * mass := tsum_mul_left
    _ ≤ (C * sourceControl S W) * L^(-((2*A:ℕ):ℝ)) * (mass+1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hbound W) (Real.rpow_nonneg hLp.le _)
      · linarith
      · exact hm
      · exact mul_nonneg (mul_nonneg hC.le (sourceControl_nonneg S W)) (Real.rpow_nonneg hLp.le _)
    _ = _ := by ring

theorem sourceControl_mono {S T : Finset (ℕ × ℕ)} (hST : S ⊆ T)
    (W : 𝓢(Joint, ℂ)) : sourceControl S W ≤ sourceControl T W :=
  Seminorm.le_def.mp (Finset.sup_mono hST) W

/-- A common finite family of Schwartz seminorms controls physical lattice mass and dual tails. -/
theorem joint_lattice_bounds (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      (∀ (W : 𝓢(Joint, ℂ)) (N : ℝ), 1 ≤ N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2) ∧
      (∀ (W : 𝓢(Joint, ℂ)) (L : ℝ), 1 ≤ L → ∀ (u : ℂ), ‖u‖ = 1 →
        (∑' p : {p : DualIndex // p ≠ 0}, ‖(𝓕 W) (scaledDualPoint L u p.val)‖) ≤
          C * sourceControl S W * L^(-((2*A:ℕ):ℝ))) := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩ := physical_lattice_bound
  obtain ⟨S₂,C₂,hC₂,h₂⟩ := dual_fourier_lattice_bound A hA
  refine ⟨S₁∪S₂,C₁+C₂,add_pos hC₁ hC₂,?_,?_⟩
  · intro W N hN
    apply (h₁ W N hN).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (le_add_of_nonneg_right hC₂.le)
      (sourceControl_mono Finset.subset_union_left W) (sourceControl_nonneg _ _) (by positivity)
  · intro W L hL u hu
    apply (h₂ W L hL u hu).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact mul_le_mul (le_add_of_nonneg_left hC₁.le)
      (sourceControl_mono Finset.subset_union_right W) (sourceControl_nonneg _ _) (by positivity)

end ProbeGramLatticeDecay

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramAnnularLattice
open ProbeGramLatticeDecay Eisenstein  SchwartzPlanePoisson
local notation "O" => Eisenstein.O

def AnnularSupport (a b : ℝ) (W : 𝓢(Joint, ℂ)) : Prop :=
  Function.support W ⊆ {z : Joint | a ≤ ‖z.fst‖^2 ∧ ‖z.fst‖^2 ≤ b ∧
    a ≤ ‖z.snd‖^2 ∧ ‖z.snd‖^2 ≤ b}

theorem scaled_embedding_norm_sq (m : O) (N : ℝ) (hN : 0 ≤ N) :
    ‖ringComplex m / (Real.sqrt N : ℂ)‖^2 = ‖ringComplex m‖^2 / N := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hN]

theorem physical_sample_eq_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (W : 𝓢(Joint, ℂ)) (hW : AnnularSupport a b W)
    (N : ℝ) (hN : 0 < N) (hsmall : N < b⁻¹) (m : O × O) :
    W (physicalPoint N m) = 0 := by
  by_contra h
  have hw := hW h
  change a ≤ ‖ringComplex m.1 / (Real.sqrt N : ℂ)‖^2 ∧
    ‖ringComplex m.1 / (Real.sqrt N : ℂ)‖^2 ≤ b ∧ _ at hw
  have hm : m.1 ≠ 0 := by
    intro hz
    have hh := hw.1
    rw [hz, map_zero, zero_div, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hh
    linarith
  have hl := one_le_eisenstein_norm_sq m.1 hm
  have hu := hw.2.1
  rw [scaled_embedding_norm_sq m.1 N hN.le, div_le_iff₀ hN] at hu
  have hs : b*N < 1 := by
    have hh := mul_lt_mul_of_pos_left hsmall hb
    simpa only [mul_inv_cancel₀ hb.ne'] using hh
  linarith

def cauchyWeight (m : O) : ℝ := ((1+‖ringComplex m‖^2)^2)⁻¹

theorem cauchyWeight_summable : Summable cauchyWeight := by
  change Summable (fun m : O => ((1+‖ringComplex m‖^2)^2)⁻¹)
  simpa only [one_mul] using scaled_eisenstein_cauchy_summable 1 zero_lt_one

theorem cauchyWeight_mass_le : (∑' m : O, cauchyWeight m) ≤ 4*(1+Real.pi)^2 := by
  simpa only [cauchyWeight, one_mul] using scaled_eisenstein_cauchy_small 1 zero_lt_one le_rfl

theorem physical_subunit_majorant (W : 𝓢(Joint, ℂ))
    (N : ℝ) (hN : 0 < N) (hN1 : N ≤ 1) (m : O × O) :
    ‖W (physicalPoint N m)‖ ≤ (2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W *
      (cauchyWeight m.1 * cauchyWeight m.2) := by
  have hn (m : O) : ‖ringComplex m‖^2 ≤ ‖ringComplex m / (Real.sqrt N : ℂ)‖^2 := by
    rw [scaled_embedding_norm_sq m N hN.le, le_div_iff₀ hN]
    exact mul_le_of_le_one_right (sq_nonneg _) hN1
  have hd : (1+‖ringComplex m.1‖^2)^2 * (1+‖ringComplex m.2‖^2)^2 ≤
      (1+‖ringComplex m.1 / (Real.sqrt N : ℂ)‖^2)^2 *
        (1+‖ringComplex m.2 / (Real.sqrt N : ℂ)‖^2)^2 := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) (hn m.1)) 2)
      (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) (hn m.2)) 2) (by positivity) (by positivity)
  have hp := (mul_le_mul_of_nonneg_right hd (norm_nonneg (W (physicalPoint N m)))).trans
    (product_decay W (ringComplex m.1 / (Real.sqrt N : ℂ))
      (ringComplex m.2 / (Real.sqrt N : ℂ)))
  dsimp only [cauchyWeight]
  rw [← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using hp

theorem physical_subunit_bound (W : 𝓢(Joint, ℂ))
    (N : ℝ) (hN : 0 < N) (hN1 : N ≤ 1) :
    (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤
      ((2:ℝ)^8*(4*(1+Real.pi)^2)^2) * sourceControl (Finset.Iic (8,0)) W := by
  have hg := cauchyWeight_summable
  have hp := hg.mul_of_nonneg hg (fun _ => by unfold cauchyWeight; positivity)
    (fun _ => by unfold cauchyWeight; positivity)
  calc
    _ ≤ ∑' m : O × O, ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*
        (cauchyWeight m.1*cauchyWeight m.2) :=
      (physical_summable W N hN).tsum_le_tsum (physical_subunit_majorant W N hN hN1)
        (hp.mul_left _)
    _ = ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(∑' m : O, cauchyWeight m)^2 := by
      rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, pow_two]
    _ ≤ ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(4*(1+Real.pi)^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (sourceControl_nonneg _ _))
      exact pow_le_pow_left₀ (tsum_nonneg (fun _ => by unfold cauchyWeight; positivity))
        cauchyWeight_mass_le 2
    _ = _ := by ring

theorem annular_lattice_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), AnnularSupport a b W → ∀ (N : ℝ), 0 < N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2 := by
  obtain ⟨S₀,C₀,hC₀,h₀⟩ := physical_lattice_bound
  let K : ℝ := (2:ℝ)^8*(4*(1+Real.pi)^2)^2
  have hK : 0 < K := by dsimp [K]; positivity
  have hb : 0 < b := ha.trans hab
  refine ⟨S₀ ∪ Finset.Iic (8,0),C₀ + K*b^2,by positivity,?_⟩
  intro W hW N hN
  have hS₀ := sourceControl_mono (S := S₀) (T := S₀ ∪ Finset.Iic (8,0)) Finset.subset_union_left W
  have hS₁ := sourceControl_mono (S := Finset.Iic (8,0))
    (T := S₀ ∪ Finset.Iic (8,0)) Finset.subset_union_right W
  by_cases hN1 : 1 ≤ N
  · apply (h₀ W N hN1).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (le_add_of_nonneg_right (by positivity)) hS₀
      (sourceControl_nonneg _ _) (by positivity)
  · by_cases hs : N < b⁻¹
    · have hz : (∑' m : O × O, ‖W (physicalPoint N m)‖) = 0 := by
        calc
          _ = ∑' _m : O × O, (0:ℝ) := tsum_congr (fun m => by
            rw [physical_sample_eq_zero a b ha hb W hW N hN hs m, norm_zero])
          _ = 0 := tsum_zero
      rw [hz]
      exact mul_nonneg (mul_nonneg (by positivity) (sourceControl_nonneg _ _)) (sq_nonneg _)
    · have hBN : 1 ≤ b*N := by
        have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hs) hb.le
        simpa only [mul_inv_cancel₀ hb.ne'] using hh
      have hBN2 : 1 ≤ b^2*N^2 := by nlinarith [sq_nonneg (b*N-1)]
      calc
        _ ≤ K * sourceControl (Finset.Iic (8,0)) W :=
          physical_subunit_bound W N hN (le_of_not_ge hN1)
        _ ≤ K * sourceControl (S₀ ∪ Finset.Iic (8,0)) W :=
          mul_le_mul_of_nonneg_left hS₁ hK.le
        _ ≤ (K * sourceControl (S₀ ∪ Finset.Iic (8,0)) W) * (b^2*N^2) :=
          le_mul_of_one_le_right (mul_nonneg hK.le (sourceControl_nonneg _ _)) hBN2
        _ = (K*b^2) * sourceControl (S₀ ∪ Finset.Iic (8,0)) W * N^2 := by ring
        _ ≤ (C₀+K*b^2) * sourceControl (S₀ ∪ Finset.Iic (8,0)) W * N^2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀.le)
              (sourceControl_nonneg _ _)) (sq_nonneg _)

theorem weighted_summable (W : 𝓢(Joint, ℂ)) (d : O × O → ℂ) (B : ℝ)
    (hd : ∀ m, ‖d m‖ ≤ B) (N : ℝ) (hN : 0 < N) :
    Summable (fun m : O × O => d m * W (physicalPoint N m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((physical_summable W N hN).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)

theorem annular_weighted_lattice_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), AnnularSupport a b W →
      ∀ (d : O × O → ℂ) (B : ℝ), 0 ≤ B → (∀ m, ‖d m‖ ≤ B) →
      ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O => d m * W (physicalPoint N m)) ∧
        ‖∑' m : O × O, d m * W (physicalPoint N m)‖ ≤ C * sourceControl S W * B * N^2 := by
  obtain ⟨S,C,hC,hbound⟩ := annular_lattice_bound a b ha hab
  refine ⟨S,C,hC,?_⟩
  intro W hW d B hB hd N hN
  refine ⟨weighted_summable W d B hd N hN,?_⟩
  calc
    _ ≤ ∑' m : O × O, B * ‖W (physicalPoint N m)‖ := by
      apply (norm_tsum_le_tsum_norm ((weighted_summable W d B hd N hN).norm)).trans
      apply ((weighted_summable W d B hd N hN).norm).tsum_le_tsum _
        ((physical_summable W N hN).mul_left B)
      intro m
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)
    _ = B * ∑' m : O × O, ‖W (physicalPoint N m)‖ := tsum_mul_left
    _ ≤ B * (C * sourceControl S W * N^2) := mul_le_mul_of_nonneg_left (hbound W hW N hN) hB
    _ = _ := by ring

end ProbeGramAnnularLattice

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
