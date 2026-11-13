/-
Canonical characters and loss parameters adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.SectorLocalization
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.DetectorSlotSelection

/-!
# Canonical characters and loss parameters

The canonical sextic CRT and prime-power characters; exponents of the first–second input
gates, loss depths and successor paid parameters; slot removal and whole-slot deletion costs.
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
open scoped BigOperators Classical
local notation "O" => Eisenstein.O
namespace CenteredMomentCanonical
open Eisenstein CompletedGauss  
open CenteredMomentCorrelation

theorem complexSexticChar_order_six (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (complexSexticChar P hg) = 6 := by
  apply (orderOf_eq_iff (by decide : 0 < 6)).mpr
  exact ⟨(complexSexticChar_powers P hg).2.2,
    fun j hj hj0 => complexSexticChar_pow_ne_one P hg hchar j hj (Nat.ne_of_gt hj0)⟩

def canonicalPrimePowerCharacter (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) {c : ℕ} (hc : 1 ≤ c) : MulChar (O ⧸ P ^ c) ℂ :=
  primePowerCharacter P hc (complexSexticChar P hg ^ c)

theorem canonicalPrimePowerCharacter_mk (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) {c : ℕ} (hc : 1 ≤ c) (x : O) :
    canonicalPrimePowerCharacter P hg hc (Ideal.Quotient.mk (P ^ c) x) =
      CanonicalRowCompletion.idealRowHom x (P ^ c) := by
  change (complexSexticChar P hg ^ c) (Ideal.Quotient.mk P x) = _
  rw [MulChar.pow_apply' _ (by omega), map_pow,
    CanonicalRowCompletion.idealRowHom_prime x P hg]

private theorem pairwise_isCoprime_pow {ι : Type*}
    (P : ι → Ideal O) (c : ι → ℕ)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    Pairwise (Function.onFun IsCoprime (fun i => P i ^ c i)) := by
  intro i j hij
  exact (hcop hij).pow

def canonicalCRTCharacter {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    MulChar (O ⧸ ∏ i, P i ^ c i) ℂ :=
  crtCharacter (IdealGaussCRT.quotientProdEquivPi (fun i => P i ^ c i)
    (pairwise_isCoprime_pow P c hcop))
    (fun i => canonicalPrimePowerCharacter (P i) (hg i) (hc i))

theorem canonicalCRTCharacter_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    canonicalCRTCharacter P hg c hc hcop (Ideal.Quotient.mk (∏ i, P i ^ c i) x) =
      CanonicalRowCompletion.idealRowHom x (∏ i, P i ^ c i) := by
  simp only [canonicalCRTCharacter, crtCharacter_apply,
    IdealGaussCRT.quotientProdEquivPi_mk, canonicalPrimePowerCharacter_mk, map_prod]


end CenteredMomentCanonical
end

end

noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentFirstSecondLossParameters
def depth (Mcap σ:ℝ):ℕ:=⌈2*Mcap/σ⌉₊+1

lemma depth_covers (Mcap σ:ℝ)(hσ:0<σ):Mcap<(depth Mcap σ:ℝ)*σ/2 := by
  have hh:=Nat.le_ceil (2*Mcap/σ)
  have hn:2*Mcap≤(⌈2*Mcap/σ⌉₊:ℝ)*σ:=(div_le_iff₀ hσ).mp hh
  simp only [depth,Nat.cast_add,Nat.cast_one]
  nlinarith


end CenteredMomentFirstSecondLossParameters
end

noncomputable section

namespace CenteredMomentSuccessorPaidParameters
open CenteredMomentFirstSecondLossParameters

def edge (epsChild epsRemove delta epsilon delta1 delta2 theta kappa mesh : ℝ) : ℝ :=
  epsChild+epsRemove+2*delta+epsilon+delta2+delta1/6+kappa*mesh+7*theta/3

def exceptional (sigma deltafr epsilon delta B theta : ℝ) : ℝ :=
  3*sigma+5*deltafr/6+2*epsilon+2*delta+2*(5*B+1)*theta

def diagonal (sigma delta reserve epsilon A : ℝ) : ℝ :=
  2*sigma+delta+reserve+epsilon*A

lemma paid_normalization (Z shortening allowance paid : ℝ) (hZ : 0< Z) :
    Z^(-shortening-allowance)*Z^(shortening+paid)=Z^(paid-allowance) := by
  rw [←Real.rpow_add hZ]
  congr 1
  ring

lemma paid_normalization_with_ratio (Z shortening allowance paid ratio : ℝ)
    (hZ : 0< Z) :
    Z^(-shortening-allowance)*(Z^(shortening+paid)*ratio^((1:ℝ)/6))=
      Z^(paid-allowance)*ratio^((1:ℝ)/6) := by
  rw [←mul_assoc,paid_normalization Z shortening allowance paid hZ]

lemma declared_parent_deficit (actual declared loss : ℝ) (h : actual≤ declared) :
    actual+(declared-actual)/6+loss≤ declared+loss := by linarith

lemma paired_declared_parent (actual declared left right loss : ℝ)
    (h : actual≤ declared)
    (hl : left≤(declared-actual)/6+loss)
    (hr : right≤(declared-actual)/6+loss) :
    actual+(left+right)/2≤ declared+loss := by linarith

lemma mesh_cost (kappa reserve : ℝ) (hk : 0≤ kappa) (hr : 0≤ reserve) :
    kappa*(reserve/(kappa+1))≤ reserve := by
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0< kappa+1)).mpr
  nlinarith

theorem simultaneous_parameters (Mcap B kappa epsilonTarget : ℝ)
    (hM : 0≤ Mcap) (hB : 0≤ B) (hk : 0≤ kappa) (he : 0< epsilonTarget) :
    ∃ sigma reserve mesh : ℝ,
      0< sigma ∧ sigma≤1 ∧ sigma≤ epsilonTarget/1000 ∧
      0< reserve ∧ 0< mesh ∧ mesh≤ reserve ∧ kappa*mesh≤ reserve ∧
      20*reserve≤ sigma/2 ∧
      Mcap<(depth Mcap sigma:ℝ)*sigma/2 ∧
      (∀ epsChild epsRemove delta epsilon delta1 delta2 theta,
        epsChild≤ reserve → epsRemove≤ reserve → delta≤ reserve → epsilon≤ reserve →
        delta1≤ reserve → delta2≤ reserve → theta≤ reserve →
        (depth Mcap sigma:ℝ)*edge epsChild epsRemove delta epsilon delta1 delta2 theta kappa mesh
          ≤ epsilonTarget/16) ∧
      (∀ deltafr epsilon delta theta,
        deltafr≤ reserve → epsilon≤ reserve → delta≤ reserve → theta≤ reserve →
        exceptional sigma deltafr epsilon delta B theta≤ epsilonTarget/16) ∧
      (∀ delta other epsilon A,
        delta≤ reserve → other≤ reserve → 0≤ epsilon → epsilon≤ reserve → A≤ Mcap →
        diagonal sigma delta other epsilon A≤ epsilonTarget/16) := by
  let sigma : ℝ := min 1 (epsilonTarget/1000)
  have hs : 0< sigma := lt_min (by norm_num) (by positivity)
  have hs1 : sigma≤1 := min_le_left _ _
  have hse : sigma≤ epsilonTarget/1000 := min_le_right _ _
  let n := depth Mcap sigma
  let L : ℝ := (n:ℝ)+Mcap+10*B+30
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hL : 0< L := by dsimp [L]; positivity
  let reserve : ℝ := min (sigma/100) (epsilonTarget/(1000*L))
  have hr : 0< reserve := lt_min (by positivity) (by positivity)
  have hrs : reserve≤ sigma/100 := min_le_left _ _
  have hre : reserve≤ epsilonTarget/(1000*L) := min_le_right _ _
  have hbudget : reserve*(1000*L)≤ epsilonTarget := (le_div_iff₀ (by positivity)).mp hre
  have hnres : (n:ℝ)*reserve≤ epsilonTarget/1000 := by
    have hx : (n:ℝ)*reserve≤ L*reserve := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr.le
    nlinarith
  have hbRes : (10*B+20)*reserve≤ epsilonTarget/1000 := by
    have hx : (10*B+20)*reserve≤ L*reserve := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr.le
    nlinarith
  have hmRes : (Mcap+2)*reserve≤ epsilonTarget/1000 := by
    have hx : (Mcap+2)*reserve≤ L*reserve := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr.le
    nlinarith
  let mesh : ℝ := reserve/(kappa+1)
  have hm : 0< mesh := by dsimp [mesh]; positivity
  have hmr : mesh≤ reserve := by
    dsimp [mesh]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hkm : kappa*mesh≤ reserve := mesh_cost kappa reserve hk hr.le
  refine ⟨sigma,reserve,mesh,hs,hs1,hse,hr,hm,hmr,hkm,by linarith,
    depth_covers Mcap sigma hs,?_,?_,?_⟩
  · intro ec er d e d1 d2 t hec her hd he hd1 hd2 ht
    have hedge : edge ec er d e d1 d2 t kappa mesh≤10*reserve := by
      unfold edge
      linarith
    have hp := mul_le_mul_of_nonneg_left hedge hn
    change (n:ℝ)*edge ec er d e d1 d2 t kappa mesh≤ epsilonTarget/16
    nlinarith
  · intro df e d t hdf he hd ht
    have htheta : 2*(5*B+1)*t≤2*(5*B+1)*reserve :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    unfold exceptional
    nlinarith
  · intro d other e A hd ho he0 he hA
    have hmul : e*A≤ reserve*Mcap := (mul_le_mul_of_nonneg_left hA he0).trans
      (mul_le_mul_of_nonneg_right he hM)
    unfold diagonal
    nlinarith

end CenteredMomentSuccessorPaidParameters

end

noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentSlotRemoval

theorem whole_slot_removal {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧
      (∑ i ∈ R, length i) ≤ min (∑ i ∈ s, length i) (F/(6*κ)+η) ∧
      (R=s ∨ F ≤ 6*κ*(∑ i ∈ R, length i)) := by
  have hthreshold : 0 ≤ F/(6*κ) := div_nonneg hF (by positivity)
  by_cases htotal : (∑ i ∈ s, length i) ≤ F/(6*κ)
  · refine ⟨s,Finset.Subset.refl _,le_min le_rfl ?_,Or.inl rfl⟩
    linarith
  · have htarget : 0 ≤ (∑ i ∈ s, length i)-F/(6*κ) := by linarith
    obtain ⟨T,hTs,hTupper,hTlower⟩ := HeckeDetectorSlotSelection.whole_slots
      s length (fun _ => 1) 1 η (by norm_num) hη hL hmesh
      (by intros; norm_num) (by intros; norm_num) 1
      ((∑ i ∈ s, length i)-F/(6*κ)) (by norm_num) (by norm_num)
      htarget (by linarith) (by simp)
    simp only [one_mul,mul_one] at hTlower
    have hsum : (∑ i ∈ s, length i)=(∑ i ∈ s\T, length i)+(∑ i ∈ T, length i) :=
      (Finset.sum_sdiff hTs).symm
    have hTnonneg : 0 ≤ ∑ i ∈ T, length i := Finset.sum_nonneg (fun i hi => hL i (hTs hi))
    refine ⟨s\T,Finset.sdiff_subset,le_min (by linarith) (by linarith),Or.inr ?_⟩
    have hremove : F/(6*κ) ≤ ∑ i ∈ s\T, length i := by linarith
    exact (div_le_iff₀ (by positivity : 0 < 6*κ)).mp hremove |>.trans_eq (mul_comm _ _)

theorem removal_cost {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧
      κ*(∑ i ∈ R, length i) ≤ F/6+κ*η ∧
      (R=s ∨ F-6*κ*(∑ i ∈ R, length i) ≤ 0) := by
  obtain ⟨R,hRs,hR,hpay⟩ := whole_slot_removal s length η κ F hη hκ hF hL hmesh
  refine ⟨R,hRs,?_,hpay.imp_right sub_nonpos.mpr⟩
  have hh := mul_le_mul_of_nonneg_left (hR.trans (min_le_right _ _)) hκ.le
  have he : κ*(F/(6*κ)+η)=F/6+κ*η := by field_simp
  rwa [he] at hh

theorem actual_product_removal {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧ (R=s ∨ F-6*κ*(∑ i ∈ R, length i) ≤ 0) ∧
      ∀ (Z : ℝ), 1 ≤ Z → ∀ (C : α → ℝ), (∀ i ∈ s, 0 ≤ C i) →
      ∀ (Q : α → ℂ), (∀ i ∈ s, ‖Q i‖^2 ≤ C i*Z^(κ*length i)) →
      ‖∏ i ∈ s, Q i‖^2 ≤
        (∏ i ∈ R, C i)*Z^(F/6+κ*η)*‖∏ i ∈ s\R, Q i‖^2 := by
  obtain ⟨R,hRs,hcost,hpay⟩ := removal_cost s length η κ F hη hκ hF hL hmesh
  refine ⟨R,hRs,hpay,?_⟩
  intro Z hZ C hC Q hQ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hremoved : ‖∏ i ∈ R, Q i‖^2 ≤ (∏ i ∈ R, C i)*Z^(F/6+κ*η) := by
    rw [norm_prod,← Finset.prod_pow]
    calc
      _ ≤ ∏ i ∈ R, C i*Z^(κ*length i) :=
        Finset.prod_le_prod (fun i hi => sq_nonneg _) (fun i hi => hQ i (hRs hi))
      _ = (∏ i ∈ R, C i)*Z^(κ*(∑ i ∈ R, length i)) := by
        rw [Finset.prod_mul_distrib,Finset.mul_sum,Real.rpow_sum_of_pos hZpos]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ hcost) (Finset.prod_nonneg (fun i hi => hC i (hRs hi)))
  have he : (∏ i ∈ s, Q i)=(∏ i ∈ s\R, Q i)*(∏ i ∈ R, Q i) :=
    (Finset.prod_sdiff hRs).symm
  rw [he,norm_mul,mul_pow,mul_comm (‖∏ i ∈ s\R, Q i‖^2)]
  exact mul_le_mul_of_nonneg_right hremoved (sq_nonneg _)

end CenteredMomentSlotRemoval

end

noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentWholeSlotDeletion
theorem whole_removal {α:Type*} (S:Finset α) (w:α→ℝ) (F κ mesh:ℝ)
    (hF:0≤ F) (hκ:0<κ) (hm:0≤ mesh)
    (hw:∀i∈S,0≤ w i) (hwm:∀i∈S,w i≤ mesh) :
    ∃R:Finset α,R⊆S ∧
      (∑i∈R,w i)≤ min (∑i∈S,w i) (F/(6*κ)+mesh) ∧
      (R=S ∨ F≤6*κ*(∑i∈R,w i)) ∧
      κ*(∑i∈R,w i)≤ F/6+κ*mesh := by
  obtain ⟨R,hR,hbound,hpay⟩:=CenteredMomentSlotRemoval.whole_slot_removal S w mesh κ F hm hκ hF hw hwm
  refine ⟨R,hR,hbound,hpay,?_⟩
  have hh:=mul_le_mul_of_nonneg_left (hbound.trans (min_le_right _ _)) hκ.le
  have he:κ*(F/(6*κ)+mesh)=F/6+κ*mesh:=by field_simp
  rwa [he] at hh


end CenteredMomentWholeSlotDeletion
end

noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentLiveCapacity

 def excess {ι:Type*} (J:Finset ι) (w:ι→ℝ) (n₁ n₂ M κ:ℝ) : ℝ :=
  max (n₁+n₂+6*κ*(∑i∈J,w i)-M) 0

 theorem remaining_capacity {ι:Type*} [DecidableEq ι]
    (J R:Finset ι) (hR:R⊆J) (w:ι→ℝ) (n₁ n₂ M κ:ℝ)
    (hpay:R=J ∨ excess J w n₁ n₂ M κ≤6*κ*(∑i∈R,w i)) :
    R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤ M := by
  rcases hpay with h|h
  · exact Or.inl h
  · right
    have hs:=Finset.sum_sdiff hR (f:=w)
    have hm:=le_max_left (n₁+n₂+6*κ*(∑i∈J,w i)-M) (0:ℝ)
    change max _ _≤ _ at h
    have hh:=hm.trans h
    rw [←hs] at hh
    nlinarith

 theorem removal_excess_cost {ι:Type*} [DecidableEq ι]
    (J:Finset ι) (w:ι→ℝ) (n₁ n₂ M κ mesh:ℝ)
    (hκ:0<κ) (hm:0≤ mesh) (hw:∀i∈J,0≤ w i) (hwm:∀i∈J,w i≤ mesh) :
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤ M) ∧
      κ*(∑i∈R,w i)≤ excess J w n₁ n₂ M κ/6+κ*mesh := by
  obtain ⟨R,hR,hbound,hpay,hcost⟩:=CenteredMomentWholeSlotDeletion.whole_removal
    J w (excess J w n₁ n₂ M κ) κ mesh (le_max_right _ _) hκ hm hw hwm
  exact ⟨R,hR,remaining_capacity J R hR w n₁ n₂ M κ hpay,hcost⟩

end CenteredMomentLiveCapacity

end

noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentFirstSecondInputGates
def exponent (A D P q ε ξ:ℝ):ℝ:=
  max (A+ε) (max (2*A+D+ε+ξ/2) (max (A+P+ε) q))


end CenteredMomentFirstSecondInputGates
end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
