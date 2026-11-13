/-
Allocated natural sources adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.CommonRadialData

/-!
# Allocated natural sources

Plain profiles, slot coefficients, children and raw scales of allocated natural sources;
source control of finite exceptional profiles; whole divisor shells and their Möbius pairs.
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
open scoped Classical BigOperators SchwartzMap ContDiff
namespace CenteredMomentAllocatedNaturalSource
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained
local notation "O" => Eisenstein.O

structure Plain where
  W : ℝ→ℂ
  a : ℝ
  b : ℝ
  a_pos : 0< a
  support : Function.support W⊆Set.Icc a b
  smooth : ContDiff ℝ ∞ W

def Plain.profile (V : Plain) (U : ℝ) (hU : 0< U) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  if h : 1≤ U*V.b then retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t else 0

lemma Plain.profile_retained (V : Plain) (U : ℝ) (hU : 0< U) (t : ℝ) (h : 1≤ U*V.b) :
    V.profile U hU t=retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t := by
  simp [Plain.profile,h]

lemma Plain.profile_zero (V : Plain) (U : ℝ) (hU : 0< U) (t : ℝ) (h : U*V.b<1) :
    V.profile U hU t=0 := by simp [Plain.profile,not_le.mpr h]

lemma polynomial_zero (χ : Character) (X : ℝ) :
    HeckeDyadic.polynomial χ false (0 : 𝓢(ℝ,ℂ)) X 0 0=0 := by
  simp [HeckeDyadic.polynomial,HeckeDyadic.summand]

theorem retained_normalized (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    {α : Type*} [Fintype α] [DecidableEq α] (V₁ V₂ : Plain)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0< P i)
    (t U₁ U₂ : ℝ) (hU₁ : 0< U₁) (hU₂ : 0< U₂) :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R)
      1 z V₁.W V₂.W pool β P t U₁ U₂=
      (((clippedScale U₁):ℂ)^(Complex.I*t)*((clippedScale U₂):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile U₁ hU₁ t) (clippedScale U₁) 0 0 *
         HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile U₂ hU₂ t) (clippedScale U₂) 0 0 *
         ∏i,naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  by_cases h₁ : 1≤ U₁*V₁.b
  · by_cases h₂ : 1≤ U₂*V₂.b
    · rw [V₁.profile_retained U₁ hU₁ t h₁,V₂.profile_retained U₂ hU₂ t h₂]
      exact original_retained_normalized (naturalRow η z hz) R hR _ _ _ _ _ _ V₁.a_pos V₂.a_pos
        V₁.support V₂.support V₁.smooth V₂.smooth pool β P hP t U₁ U₂ hU₁ hU₂ h₁ h₂
    · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
        (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
        (Or.inr (lt_of_not_ge h₂)),V₂.profile_zero U₂ hU₂ t (lt_of_not_ge h₂),polynomial_zero]
      simp
  · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
      (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
      (Or.inl (lt_of_not_ge h₁)),V₁.profile_zero U₁ hU₁ t (lt_of_not_ge h₁),polynomial_zero]
    simp

variable {α : Type*} [Fintype α] [DecidableEq α]

def rawScale (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) (X : ℝ) (j : Fin 2) : ℝ :=
  X/Ideal.absNorm (selectedPlain D a j)

lemma rawScale_pos (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (X : ℝ) (hX : 0< X) (j : Fin 2) : 0< rawScale D a X j := by
  apply div_pos hX
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (selectedDivisor_ne_zero D Finset.univ a _))

lemma raw_same_product (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (X₁ X₂ Y₁ Y₂ : ℝ) (h : X₁*X₂=Y₁*Y₂) :
    rawScale D a X₁ 0*rawScale D a X₂ 1=rawScale D a Y₁ 0*rawScale D a Y₂ 1 := by
  simp only [rawScale,div_mul_div_comm,h]

theorem allocated_normalized (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0< P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) :
    allocatedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R)
      1 z t pool β P D a V₁.W V₂.W X₁ X₂=
      (((clippedScale (rawScale D a X₁ 0)):ℂ)^(Complex.I*t)*
       ((clippedScale (rawScale D a X₂ 1)):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t) (clippedScale (rawScale D a X₁ 0)) 0 0 *
         HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t) (clippedScale (rawScale D a X₂ 1)) 0 0 *
         ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
           (pool i) (heightCoefficient (β i) t) (P i)) := by
  have h:=retained_normalized η z hz R hR V₁ V₂
    (fun i : liveIndices D a=> pool i) (fun i : liveIndices D a=>β i) (fun i : liveIndices D a=> P i)
    (fun i=> hP i) t _ _ (rawScale_pos D a X₁ hX₁ 0) (rawScale_pos D a X₂ hX₂ 1)
  have hp': (∏i : liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i))=
      ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i) := Finset.prod_coe_sort (liveIndices D a) (fun i : α=> naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i))
  rw [hp'] at h
  exact h

omit [Fintype α] [DecidableEq α] in

theorem slot_controls (ν : α→Ideal O→ℂ) (W : α→ℝ→ℂ) (P b M : α→ℝ)
    (hP : ∀i,0< P i) (hν : ∀i I,‖ν i I‖≤1)
    (hW : ∀i x,‖W i x‖≤ M i) (hs : ∀i,Function.support (W i)⊆Set.Iic (b i)) :
    (∀i I,‖ν i I*W i ((I.absNorm:ℝ)/P i)‖≤ M i) ∧
    (∀i I,ν i I*W i ((I.absNorm:ℝ)/P i)≠0 → (I.absNorm:ℝ)≤ b i*P i) := by
  constructor
  · intro i I
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hν i I) (norm_nonneg _)).trans (by simpa using hW i _)
  · intro i I hn
    exact (div_le_iff₀ (hP i)).mp (hs i (right_ne_zero_of_mul hn))

def SharedBound (F : Finset α) (b M : α→ℝ) (C ε : ℝ) : Prop :=
    ∀{ι : Type*} [Fintype ι],
      ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)(χ : ι→Character)
        (W₁ W₂ : ι→𝓢(ℝ,ℂ))(X₁ X₂ : ι→ℝ)
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ),
      (∀i,0< X₁ i) → (∀i,0< X₂ i) →
      (∀i j,j∈F → ∀I∈pool i j,Prime I) → (∀i j,j∈F → 0< P i j) →
      (∀i j,j∈F → ∀I∈pool i j,‖β i j I‖≤ M j) →
      (∀i j,j∈F → ∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤ b j*P i j) →
      ∀E : ℝ,0≤ E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false (W₁ i)
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false (W₂ i)
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ i) (pool i j) (β i j) (P i j)‖^2)≤ E) →
      (∑i,‖HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
        HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
        ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j)‖^2)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

theorem uniform_shared (b M : α→ℝ) (hM : ∀i,0≤ M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀F : Finset α,SharedBound F b M C ε := by
  have he (F : Finset α) : ∃C : ℝ,0< C ∧ SharedBound F b M C ε :=
    actual_shared_energy F b M (fun i _=> hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑F : Finset α,C F
  have hsum : 0≤∑F : Finset α,C F:=Finset.sum_nonneg (fun F _=>(hC F).le)
  refine ⟨B,by dsimp [B];linarith,?_⟩
  intro F ι _ R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE hchild
  have hCB : C F≤ B := by
    have hh:=Finset.single_le_sum (fun G _=>(hC G).le) (Finset.mem_univ F)
    dsimp [B]
    linarith
  exact (hb F R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

lemma primeSupport_product_radical (R : Ideal O) (hR : R≠0) :
    (∏I∈primeSupport R,I)=R.radical := by
  ext x
  change x∈(∏I∈primeSupport R,I) ↔ ∃n : ℕ,x^n∈R
  simp_rw [←Ideal.span_singleton_le_iff_mem,←Ideal.dvd_iff_le,←Ideal.span_singleton_pow]
  exact (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd hR).symm

def child (χ : Character) (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (D₁ D₂ : Finset (Ideal O)) (J : Finset α) : ℂ :=
  HeckeDyadic.polynomial χ false (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
  HeckeDyadic.polynomial χ false (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
  ∏i∈liveIndices D a\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)

def AllocatedBound (b M : α→ℝ) (C ε : ℝ) : Prop :=
  ∀(D : Ideal O)(a : Allocation D (Finset.univ : Finset (α⊕Fin 2))),
  ∀{ι : Type*} [Fintype ι],∀(η : ι→Character)(z : ι→O)(hz : ∀i,z i≠0)
    (R : Ideal O),R≠0 → ∀(V₁ V₂ : ι→Plain)
    (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ)(t X₁ X₂ : ι→ℝ)
    (hX₁ : ∀i,0< X₁ i)(hX₂ : ∀i,0< X₂ i),
    (∀i j,∀I∈pool i j,Prime I) → (∀i j,0< P i j) →
    (∀i j,∀I∈pool i j,‖β i j I‖≤ M j) →
    (∀i j,∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤ b j*P i j) →
    ∀E : ℝ,0≤ E →
    (∀D₁∈(primeSupport R).powerset,
     ∀D₂∈(primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (η i) (z i) (hz i)).character D a (V₁ i) (V₂ i)
         (pool i) (β i) (P i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i) D₁ D₂ J‖^2)≤ E) →
    (∑i,‖allocatedPositiveRow (η i)
      (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R)
      1 (z i) (t i) (pool i) (β i) (P i) D a (V₁ i).W (V₂ i).W (X₁ i) (X₂ i)‖^2)≤
      C*(Ideal.absNorm R.radical:ℝ)^ε*E

theorem allocated_energy (b M : α→ℝ) (hM : ∀i,0≤ M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ AllocatedBound b M C ε := by
  obtain ⟨C,hC,hbound⟩:=uniform_shared b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro D a ι _ η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild
  have hh:=hbound (liveIndices D a) (primeSupport R) (fun _ h => support_prime h)
    (fun i=>(naturalRow (η i) (z i) (hz i)).character)
    (fun i=>(V₁ i).profile _ (rawScale_pos D a (X₁ i) (hX₁ i) 0) (t i))
    (fun i=>(V₂ i).profile _ (rawScale_pos D a (X₂ i) (hX₂ i) 1) (t i))
    (fun i=> clippedScale (rawScale D a (X₁ i) 0)) (fun i=> clippedScale (rawScale D a (X₂ i) 1))
    pool (fun i j=> heightCoefficient (β i j) (t i)) P
    (fun _=> by unfold clippedScale;positivity) (fun _=> by unfold clippedScale;positivity)
    (fun i j _=> hp i j) (fun i j _=> hP i j)
    (fun i j _ I hi=> by rw [heightCoefficient_norm _ _ _ (hp i j I hi).ne_zero];exact hβ i j I hi)
    (fun i j _ I hi hn=> hs i j I hi (left_ne_zero_of_mul hn)) E hE hchild
  have he (i : ι):=allocated_normalized (η i) (z i) (hz i) R hR D a (V₁ i) (V₂ i)
    (pool i) (β i) (P i) (hP i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
  have hphase (U t : ℝ) : ‖((clippedScale U):ℂ)^(Complex.I*t)‖=1 :=
    positive_height_phase_norm _ _ (by unfold clippedScale;positivity)
  simp_rw [he,norm_mul,hphase,one_mul]
  rw [←primeSupport_product_radical R hR]
  simpa only [SharedBound,excluded,norm_mul] using hh

theorem uniform_allocated_energy (b M : α→ℝ) (hM : ∀i,0≤ M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀T : Finset α,
      AllocatedBound (fun i : T=> b i) (fun i : T=> M i) C ε := by
  have he (T : Finset α) : ∃C : ℝ,0< C ∧ AllocatedBound (fun i : T=> b i) (fun i : T=> M i) C ε :=
    allocated_energy (fun i : T=> b i) (fun i : T=> M i) (fun i=> hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑T : Finset α,C T
  have hsum : 0≤∑T : Finset α,C T:=Finset.sum_nonneg (fun T _=>(hC T).le)
  refine ⟨B,by dsimp [B];linarith,?_⟩
  intro T D a ι _ η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild
  have hCB : C T≤ B := by
    have hh:=Finset.single_le_sum (fun G _=>(hC G).le) (Finset.mem_univ T)
    dsimp [B]
    linarith
  exact (hb T D a η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

theorem natural_nonprincipal_width (η : Character) (z : O) (hz : z≠0)
    (Q R : Ideal O) (hR : R≠0)
    (hex : ¬CenteredExceptionalProfile.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R) 1 z)
    (Z m q Cz : ℝ) (hZ : 0< Z) (hCz : 0≤ Cz)
    (hη : (η.modulus.absNorm:ℝ)≤ Z^m) (hrow : ((Ideal.span {z}).absNorm:ℝ)≤ Cz*Z^q) :
    (naturalRow η z hz).character.residue≠1 ∧
    ((naturalRow η z hz).character.modulus.absNorm:ℝ)≤(fixedConductorFactor:ℝ)*Cz*Z^(m+q) :=
  ⟨(naturalRow η z hz).nonprincipal hz Q R hR hex,
    (naturalRow η z hz).modulus_power_bound Z m q Cz hZ hCz hη hrow⟩

structure Slots (α : Type*) (b M : α→ℝ) where
  pool : α→Finset (Ideal O)
  ν : α→Ideal O→ℂ
  W : α→ℝ→ℂ
  P : α→ℝ
  prime : ∀i,∀I∈pool i,Prime I
  P_pos : ∀i,0< P i
  ν_bound : ∀i I,‖ν i I‖≤1
  W_bound : ∀i x,‖W i x‖≤ M i
  support : ∀i,Function.support (W i)⊆Set.Iic (b i)

def Slots.coefficient {b M : α→ℝ} (s : Slots α b M) (i : α) (I : Ideal O) : ℂ :=
  s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)

omit [Fintype α] [DecidableEq α] in
lemma Slots.controls {b M : α→ℝ} (s : Slots α b M) :
    (∀i I,‖s.coefficient i I‖≤ M i) ∧
    (∀i I,s.coefficient i I≠0 → (I.absNorm:ℝ)≤ b i*s.P i) :=
  slot_controls s.ν s.W s.P b M s.P_pos s.ν_bound s.W_bound s.support

structure Row (α : Type*) (b M : α→ℝ) where
  η : Character
  z : O
  z_ne : z≠0
  plain₁ : Plain
  plain₂ : Plain
  slots : Slots α b M
  t : ℝ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  X₁_pos : 0< X₁
  X₂_pos : 0< X₂
  Y₁_pos : 0< Y₁
  Y₂_pos : 0< Y₂
  same_product : X₁*X₂=Y₁*Y₂

lemma Row.extracted_same_product {b M : α→ℝ} (s : Row α b M)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) :
    rawScale D a s.X₁ 0*rawScale D a s.X₂ 1=rawScale D a s.Y₁ 0*rawScale D a s.Y₂ 1 :=
  raw_same_product D a _ _ _ _ s.same_product

theorem uniform_paired_nuW_energy (b M : α→ℝ) (hM : ∀i,0≤ M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀T : Finset α,
    ∀(D : Ideal O)(a : Allocation D (Finset.univ : Finset (T⊕Fin 2))),
    ∀{ι : Type*} [Fintype ι],∀s : ι→Row T (fun i=> b i) (fun i=> M i),
    ∀(R : Ideal O),R≠0 → ∀E₁ E₂ : ℝ,0≤ E₁ → 0≤ E₂ →
    (∀D₁∈(primeSupport R).powerset,
     ∀D₂∈(primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (s i).η (s i).z (s i).z_ne).character D a
         (s i).plain₁ (s i).plain₂ (s i).slots.pool (s i).slots.coefficient (s i).slots.P
         (s i).t (s i).X₁ (s i).X₂ (s i).X₁_pos (s i).X₂_pos D₁ D₂ J‖^2)≤ E₁) →
    (∀D₁∈(primeSupport R).powerset,
     ∀D₂∈(primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (s i).η (s i).z (s i).z_ne).character D a
         (s i).plain₁ (s i).plain₂ (s i).slots.pool (s i).slots.coefficient (s i).slots.P
         (s i).t (s i).Y₁ (s i).Y₂ (s i).Y₁_pos (s i).Y₂_pos D₁ D₂ J‖^2)≤ E₂) →
    (∑i,(‖allocatedPositiveRow (s i).η
      (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R)
      1 (s i).z (s i).t (s i).slots.pool (s i).slots.coefficient (s i).slots.P D a
      (s i).plain₁.W (s i).plain₂.W (s i).X₁ (s i).X₂‖^2+
      ‖allocatedPositiveRow (s i).η
      (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R)
      1 (s i).z (s i).t (s i).slots.pool (s i).slots.coefficient (s i).slots.P D a
      (s i).plain₁.W (s i).plain₂.W (s i).Y₁ (s i).Y₂‖^2))≤
      C*(Ideal.absNorm R.radical:ℝ)^ε*(E₁+E₂) := by
  obtain ⟨C,hC,hbound⟩:=uniform_allocated_energy b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro T D a ι _ s R hR E₁ E₂ hE₁ hE₂ hleft hright
  have hl:=hbound T D a (fun i=>(s i).η) (fun i=>(s i).z) (fun i=>(s i).z_ne) R hR
    (fun i=>(s i).plain₁) (fun i=>(s i).plain₂) (fun i=>(s i).slots.pool)
    (fun i=>(s i).slots.coefficient) (fun i=>(s i).slots.P) (fun i=>(s i).t)
    (fun i=>(s i).X₁) (fun i=>(s i).X₂) (fun i=>(s i).X₁_pos) (fun i=>(s i).X₂_pos)
    (fun i=>(s i).slots.prime) (fun i=>(s i).slots.P_pos)
    (fun i j I _=>(s i).slots.controls.1 j I) (fun i j I _=>(s i).slots.controls.2 j I)
    E₁ hE₁ hleft
  have hr:=hbound T D a (fun i=>(s i).η) (fun i=>(s i).z) (fun i=>(s i).z_ne) R hR
    (fun i=>(s i).plain₁) (fun i=>(s i).plain₂) (fun i=>(s i).slots.pool)
    (fun i=>(s i).slots.coefficient) (fun i=>(s i).slots.P) (fun i=>(s i).t)
    (fun i=>(s i).Y₁) (fun i=>(s i).Y₂) (fun i=>(s i).Y₁_pos) (fun i=>(s i).Y₂_pos)
    (fun i=>(s i).slots.prime) (fun i=>(s i).slots.P_pos)
    (fun i j I _=>(s i).slots.controls.1 j I) (fun i j I _=>(s i).slots.controls.2 j I)
    E₂ hE₂ hright
  rw [Finset.sum_add_distrib,mul_add]
  exact add_le_add hl hr

def inputSlots (s : CenteredMomentCommonRadialData.Input α) : Slots α s.hi s.M where
  pool:=s.slots
  ν:=s.ν
  W:=s.W
  P:=s.P
  prime:=s.prime
  P_pos:=s.P_pos
  ν_bound:=s.ν_bound
  W_bound:=s.W_bound
  support:=fun i _ hx=>(s.support i hx).2

omit [DecidableEq α] in
lemma inputSlots_coefficient (s : CenteredMomentCommonRadialData.Input α) :
    (inputSlots s).coefficient=s.toData.coefficient := rfl

def commonSlots (s : CenteredMomentCommonRadialData.Input α) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    Slots (CenteredMomentCommonProfile.liveIndices B.val) (fun i=> s.hi i) (fun i=> s.M i) where
  pool:=fun i=> s.slots i
  ν:=fun i=> s.ν i
  W:=fun i=> s.W i
  P:=fun i=> s.P i
  prime:=fun i=> s.prime i
  P_pos:=fun i=> s.P_pos i
  ν_bound:=fun i=> s.ν_bound i
  W_bound:=fun i=> s.W_bound i
  support:=fun i _ hx=>(s.support i hx).2

omit [DecidableEq α] in
lemma commonSlots_coefficient (s : CenteredMomentCommonRadialData.Input α) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    (commonSlots s C B).coefficient=(CenteredMomentCommonRadialData.commonData s C R B).coefficient := rfl

end CenteredMomentAllocatedNaturalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace CenteredMomentNaturalMaskedFloor
open HeckeFamily HeckeDyadic  InversePrincipalEnergy
open CenteredMomentPlainPositiveEnergy CenteredMomentPlainGlobalEnergy
open CenteredMomentCommonMaskRadialEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentCoreFloor CenteredMomentLattice CenteredMomentTwist
open CenteredMomentAllocatedNaturalSource HeckeInverseAmplification
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => Eisenstein.O

theorem excluded_pair (a b ε : ℝ) (ha : 0< a) (hb : 0≤ b) (hε : 0<ε) :
    ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0< C ∧
    ∀ (W₁ W₂ : 𝓢(ℝ,ℂ)), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀ (χ : O→Character) (r : Radial) (R : Ideal O) (Q X₁ X₂ : ℝ), R≠0 →
      0≤ Q → 0< X₁ → 0< X₂ →
      (∀z,r.keep z→(χ z).residue≠1) →
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤ Q) →
    radialEnergy (fun z=> polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
      polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Q^4 := by
  obtain ⟨S,C,hC,hpair⟩ := actual_radial_pair_bound a b ha
  obtain ⟨Cd,hCd,hdel⟩ := actual_radial_shared_energy (∅ : Finset (Fin 0))
    (fun _=>0) (fun _=>0) (by simp) ε hε
  refine ⟨S,Cd*C*3^8,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ χ r R Q X₁ X₂ hR hQ hX₁ hX₂ hχ hmod
  let E := C*diagonalControl r.profile*max 1 r.scale*
    ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Q^4*3^8
  have hdiag := diagonalControl_nonneg r.profile
  have hE : 0≤ E := by dsimp [E]; positivity
  have hh := hdel (primeSupport R) (fun _ h => support_prime h) χ W₁ W₂
    X₁ X₂ a b a b (fun _=>∅) (fun _ _=>0) (fun _=>1) r.keep r.profile r.scale E
    hX₁ hX₂ hb hb hs₁ hs₂ (by simp) (by simp) (by simp) (by simp)
    r.scale_pos r.nonneg hE ?_
  · simp only [Finset.prod_empty,mul_one] at hh
    rw [primeSupport_product_radical R hR] at hh
    change radialEnergy (fun z=> polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
      polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤ _ at hh
    exact hh.trans_eq (by dsimp [E]; ring)
  · intro D₁ hD₁ D₂ hD₂ J hJ
    have hn (D : Finset (Ideal O)) (hD : D∈(primeSupport R).powerset) :
        0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hi=>(support_prime (Finset.mem_powerset.mp hD hi)).ne_zero)))
    have he := hpair W₁ W₂ hs₁ hs₂ χ r Q
      (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0
      hQ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂)) hχ hmod
    norm_num only [abs_zero,add_zero,show (3:ℝ)^4=81 by norm_num] at he
    simpa only [Finset.empty_sdiff,Finset.prod_empty,mul_one] using he.trans_eq (by dsimp [E]; ring)

lemma twist_polynomial (χ : Character) (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0< a)
    (hs : Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (t X : ℝ) :
    polynomial χ false (normPowerProfile W a b ha hs (W.smooth ⊤) t) X 0 0 =
      polynomial χ false W X 0 t := by
  have hp : (normPowerProfile W a b ha hs (W.smooth ⊤) t:ℝ→ℂ)=twistProfile W 0 t := by
    funext x
    rw [normPowerProfile_apply]
    unfold twistProfile HeckeDyadic.shift
    simp only [Complex.ofReal_zero,zero_sub,neg_neg]
    rw [mul_comm Complex.I (t:ℂ)]
    ring
  rw [hp,polynomial_twistProfile]

theorem natural_masked_floor (a b ε : ℝ) (ha : 0< a) (hb : 0≤ b) (hε : 0<ε) :
    ∃ n : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0< C ∧
    ∀ (W₁ W₂ : 𝓢(ℝ,ℂ)), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀ (η : Character) (Q R : Ideal O) (r : Radial) (bΦ : ℝ), R≠0 → 0≤ bΦ →
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η Q (fixedBadMask*cubicIdealGenerator R) 1 z) →
    ∀ (Z m q ρ t X₁ X₂ : ℝ), 1≤ Z → 0≤ m → 0≤ q → r.scale=Z^m →
      m+q≤ρ → 0< X₁ → 0< X₂ → (η.modulus.absNorm:ℝ)≤ Z^q →
    zeroEnergy η (fixedBadMask*cubicIdealGenerator R) 1 t W₁ W₂ X₁ X₂ r ≤
      C*(R.radical.absNorm:ℝ)^ε*bΦ^4*diagonalControl r.profile*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*(1+‖t‖)^n*Z^(m+q+4*ρ) := by
  obtain ⟨S,C,hC,hpair⟩ := excluded_pair a b ε ha hb hε
  obtain ⟨n,T,Ct,hCt,ht⟩ :=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a b ha S
  let F : ℝ := fixedConductorFactor
  have hF : 0< F := by
    unfold F fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨4*n,T,C*Ct^4*F^4,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ η Q R r bΦ hR hbΦ hsΦ hz hex Z m q ρ t X₁ X₂ hZ hm hq hscale hρ hX₁ hX₂ hη
  let r' : Radial := {r with keep := fun z=> r.keep z ∧ r.profile (‖ringComplex z‖^2/r.scale)≠0}
  let χ : O→Character := fun z=> if hz:z≠0 then (naturalRow η z hz).character else η
  have hχ (z:O) (h:r'.keep z) : (χ z).residue≠1 := by
    have hn := hz z h.1
    have hc : χ z=(naturalRow η z hn).character := by simp [χ,hn]
    exact (congrArg (fun ψ : Character=>ψ.residue≠1) hc).mpr
      ((naturalRow η z hn).nonprincipal hn Q R hR (hex z h.1))
  have hmod (z:O) (h:r'.keep z) : ((χ z).modulus.absNorm:ℝ)≤ F*bΦ*Z^(m+q) := by
    have hn := hz z h.1
    have hh : ((Ideal.span {z}).absNorm:ℝ)≤ bΦ*Z^m := by
      rw [←ringComplex_norm_sq_eq_absNorm_span,←hscale]
      exact (div_le_iff₀ r.scale_pos).mp (hsΦ h.2)
    simpa only [χ,dif_pos hn,add_comm q m] using
      (naturalRow η z hn).modulus_power_bound Z q m bΦ (zero_lt_one.trans_le hZ) hbΦ hη hh
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t
  have hv₁ : Function.support (V₁:ℝ→ℂ)⊆Set.Icc a b := (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t).trans hs₁
  have hv₂ : Function.support (V₂:ℝ→ℂ)⊆Set.Icc a b := (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t).trans hs₂
  have he := hpair V₁ V₂ hv₁ hv₂ χ r' R (F*bΦ*Z^(m+q)) X₁ X₂ hR
    (by positivity) hX₁ hX₂ hχ hmod
  have hid : zeroEnergy η (fixedBadMask*cubicIdealGenerator R) 1 t W₁ W₂ X₁ X₂ r =
      radialEnergy (fun z=> polynomial (excluded (χ z) R) false V₁ X₁ 0 0 *
        polynomial (excluded (χ z) R) false V₂ X₂ 0 0) r'.keep r'.profile r'.scale := by
    unfold zeroEnergy radialEnergy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · by_cases hp : r.profile (‖ringComplex z‖^2/r.scale)=0
      · simp [r',hk,hp]
      · have hn := hz z hk
        simp only [r',hk,true_and,ite_true]
        rw [zero_row_norm η (excluded (χ z) R) _ 1 z
          (by simpa only [χ,dif_pos hn,one_mul] using (naturalRow η z hn).masked_element R hR)
          W₁ W₂ a b ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤) t X₁ X₂ hX₁ hX₂]
        rw [norm_mul,twist_polynomial,twist_polynomial]
        split_ifs with h
        · rfl
        · exact False.elim (h hp)
    · simp [r',hk]
  rw [←hid] at he
  have hB₁ := ht W₁ hs₁ t
  have hB₂ := ht W₂ hs₂ t
  have hprod : (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₁ * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₂)^2 ≤
      (Ct^4*(T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+‖t‖)^(4*n) := by
    have hh := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (mul_le_mul hB₁ hB₂ (apply_nonneg _ _) (by positivity)) 2
    exact hh.trans_eq (by dsimp [V₁,V₂]; rw [Nat.mul_comm 4 n,pow_mul]; ring)
  have hp : Z^m*(Z^(m+q))^4≤ Z^(m+q+4*ρ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hZ),←Real.rpow_add (zero_lt_one.trans_le hZ)]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  have hd := diagonalControl_nonneg r.profile
  dsimp only [r'] at he
  rw [hscale,max_eq_right (Real.one_le_rpow hZ hm)] at he
  apply he.trans
  calc
    _ ≤ C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*Z^m*
      ((Ct^4*(T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+‖t‖)^(4*n))*(F*bΦ*Z^(m+q))^4 := by
        gcongr
    _ = (C*Ct^4*F^4*(R.radical.absNorm:ℝ)^ε*bΦ^4*diagonalControl r.profile*
      (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2*(1+‖t‖)^(4*n))*(Z^m*(Z^(m+q))^4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end CenteredMomentNaturalMaskedFloor

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentExceptionalCappedAmplitude
open HeckeFamily CenteredMomentHeckeTwist CenteredMomentTwist CenteredMomentLattice
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentCounting CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => Eisenstein.O
theorem rowTwistedSum_absolute (η : Character) (m A z : O) (W : ℝ→ℂ)
    (b M t X : ℝ) (hb : 0≤ b) (hM : 0≤ M) (hX : 0< X)
    (hs : Function.support W⊆Set.Iic b) (hW : ∀x,‖W x‖≤ M) :
    ‖rowTwistedSum η m A z W t X‖≤(128*b*M)*X := by
  have hh := norm_tsum_ideal_ball
    (fun I : Ideal O => (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
      (Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)) (b*X) M
    (mul_nonneg hb hX.le) hM (by
      change (idealCoeff η (0:Ideal O)*_)*_*_=0
      rw [map_zero,zero_mul,zero_mul,zero_mul]) (by
      intro I
      by_cases hI : I=0
      · subst I; simpa only [map_zero,zero_mul,mul_zero,norm_zero] using hM
      · rw [norm_mul]
        exact (mul_le_mul (row_twisted_coefficient_norm η m A z t I hI) (hW _)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul M)) (by
      intro I hI
      exact (div_le_iff₀ hX).mp (hs (right_ne_zero_of_mul hI)))
  exact hh.trans_eq (by ring)

theorem normalized_rectangle_absolute (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ M₁ M₂ : ℝ)
    (hb₁ : 0≤ b₁) (hb₂ : 0≤ b₂) (hM₁ : 0≤ M₁) (hM₂ : 0≤ M₂)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hW₁ : ∀x,‖W₁ x‖≤ M₁) (hW₂ : ∀x,‖W₂ x‖≤ M₂)
    (t X₁ X₂ Y₁ Y₂ T : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂)
    (hY₁ : 0< Y₁) (hY₂ : 0< Y₂) (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) :
    ‖(Real.sqrt T:ℂ)⁻¹ *
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)‖≤
      (2*(128*b₁*M₁)*(128*b₂*M₂))*Real.sqrt T := by
  have hT : 0< T := hpX ▸ mul_pos hX₁ hX₂
  have hsq : 0< Real.sqrt T := Real.sqrt_pos.2 hT
  have hprod (U V : ℝ) (hU : 0< U) (hV : 0< V) :
      ‖rowTwistedSum η m A z W₁ t U*rowTwistedSum η m A z W₂ t V‖≤
        ((128*b₁*M₁)*(128*b₂*M₂))*(U*V) := by
    rw [norm_mul]
    apply (mul_le_mul (rowTwistedSum_absolute η m A z W₁ b₁ M₁ t U hb₁ hM₁ hU hs₁ hW₁)
      (rowTwistedSum_absolute η m A z W₂ b₂ M₂ t V hb₂ hM₂ hV hs₂ hW₂)
      (norm_nonneg _) (by positivity)).trans_eq
    ring
  have hraw := (norm_sub_le
    (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)
    (rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)).trans
      (add_le_add (hprod X₁ X₂ hX₁ hX₂) (hprod Y₁ Y₂ hY₁ hY₂))
  rw [hpX,hpY] at hraw
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsq.le]
  apply (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hsq.le)).trans_eq
  have he := Real.sq_sqrt hT.le
  field_simp
  rw [he]
  ring

theorem max_raw_reduction (Z Rred r : ℝ) (hZ : 1< Z) (hR : 0< Rred) :
    max 1 (Z^r/Rred)=Z^(max (r-Real.logb Z Rred) 0) := by
  have hz : 0< Z := zero_lt_one.trans hZ
  have he : Z^r/Rred=Z^(r-Real.logb Z Rred) := by
    rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hR]
  rw [he]
  by_cases h : 0≤ r-Real.logb Z Rred
  · rw [max_eq_left h,max_eq_right (Real.one_le_rpow hZ.le h)]
  · rw [max_eq_right (le_of_not_ge h),Real.rpow_zero,
      max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ.le (le_of_not_ge h))]

theorem reciprocal_max_raw_reduction (Z Rred r : ℝ) (hZ : 1< Z) (hR : 0< Rred) :
    1/max 1 (Z^r/Rred)=Z^(-max (r-Real.logb Z Rred) 0) := by
  rw [max_raw_reduction Z Rred r hZ hR,Real.rpow_neg (zero_le_one.trans hZ.le),one_div]

theorem allocation_reciprocal_max {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : CenteredMomentActiveDivisorShell.Source ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (Z r : ℝ) (hZ : 1< Z) :
    1/max 1 (Z^r/formalReductionFactor D a s.P)=
      Z^(-max (r-Real.logb Z (formalReductionFactor D a s.P)) 0) := by
  apply reciprocal_max_raw_reduction Z _ r hZ
  exact mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=> s.P_pos i))

end CenteredMomentExceptionalCappedAmplitude

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentLattice CenteredMomentHeckeVolume
open CenteredMomentHeckeCancellation CenteredMomentHeckeHeight
open CenteredMomentMask
open InversePrincipalEnergy SchwartzPlanePoisson
local notation "O" => Eisenstein.O

theorem volumeControl_source_control (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character,
      (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B → ∀ t : ℝ,
      volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * Z^ε * (1+‖t‖)^n := by
  obtain ⟨n,T,C,hC,hprofile⟩ := normPowerProfile_source_control a b ha pvSeminorms
  obtain ⟨D,hD,hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  let S := insert (0,0) T
  refine ⟨n,S,by simp [S],?_⟩
  intro Q
  let mass : ℝ := Nat.card (O ⧸ Ideal.span {fixedPeriod Q})
  let A := D*mass*pvConstant*C
  have hmass : 0 ≤ mass := Nat.cast_nonneg _
  have hpv := pvConstant_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨1+A,by positivity,?_⟩
  intro W hs Z hZ χ hnorm t
  have hTS : T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro z hz
    exact Seminorm.le_finset_sup_apply (Finset.mem_insert_of_mem hz)
  have hp := (hprofile W hs t).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTS hC.le) (by positivity))
  have herr : volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
      (D*Z^ε)*(mass*(pvConstant*(C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(1+‖t‖)^n))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hnorm)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg hpv.le (apply_nonneg _ _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  calc
    _ ≤ _ := herr
    _ = A*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by dsimp [A]; ring
    _ ≤ (1+A)*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by
      gcongr
      linarith

theorem retained_volumeControl_source_control (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character,
      (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B →
      ∀ X : ℝ, ∀ hX : 0< X, ∀ hret : 1≤ X*b, ∀ t : ℝ,
      volumeControl Q χ (CenteredMomentRetainedProfile.retainedProfile
        W a b ha hs (W.smooth ⊤) X hX hret t) ≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by
  obtain ⟨n,S,hS,hbound⟩ := volumeControl_source_control a b ε B ha hε hB
  refine ⟨n,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hCbound⟩ := hbound Q
  refine ⟨(max 1 b)^(pvSeminorms.sup Prod.snd)*C,by positivity,?_⟩
  intro W hs Z hZ χ hχ X hX hret t
  exact (CenteredMomentRetainedProfile.retained_volumeControl_le
    Q χ W a b ha hs (W.smooth ⊤) X hX hret t).trans
    ((mul_le_mul_of_nonneg_left (hCbound W hs Z hZ χ hχ t) (by positivity)).trans_eq (by ring))
end CenteredMomentFiniteProfileExceptional

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeTwist
open CenteredMomentHeckeCancellation CenteredMomentLattice
local notation "O" => Eisenstein.O

theorem rectangle_source_unit (a b ε B : ℝ)
    (ha : 0< a) (hb : 0≤ b) (hε : 0<ε) (hB : 0≤ B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0< C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁≤1 →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂≤1 →
      ∀ Z : ℝ, 1≤ Z → ∀ η χ ψ : Character,
      (Ideal.absNorm χ.modulus:ℝ)≤ Z^B → Q≤ψ.modulus →
      CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A z : O, lambda∣m → (2:O)∣m →
      (∀ n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0< L →
      L≤ X₁ → L≤ X₂ → L≤ Y₁ → L≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
        twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂)‖ ≤
        C*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,S,hS,hvol⟩ := volumeControl_source_control a b ε B ha hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨D,hD,hDvol⟩ := hvol Q
  let V := 128*(b+b)
  have hV : 0≤ V := by dsimp [V]; positivity
  refine ⟨1+8*D*V,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ hS₁ hS₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hbound₁ (y:ℝ) : ‖W₁ y‖≤1 :=
    (SchwartzMap.norm_le_seminorm ℝ W₁ y).trans
      ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans hS₁)
  have hbound₂ (y:ℝ) : ‖W₂ y‖≤1 :=
    (SchwartzMap.norm_le_seminorm ℝ W₂ y).trans
      ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans hS₂)
  have herr (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
      (hS':S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤1) :
      volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        D*Z^ε*(1+‖t‖)^J := by
    apply (hDvol W hs Z hZ χ hnorm t).trans
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hS' hD.le) (Real.rpow_nonneg (by linarith) _))
        (show 0≤(1+‖t‖)^J by positivity)
  have hraw := actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A z hml hm2 hrow
    W₁ W₂ a b a b 1 1 ha ha hb hb zero_le_one zero_le_one hs₁ hs₂
    (W₁.smooth ⊤) (W₂.smooth ⊤) hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0< T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hn := CenteredMoment.normalized_centered_saving _ T L V _ hT (by
    simpa only [mul_one] using hraw)
  have hE := add_le_add (herr W₁ hs₁ hS₁) (herr W₂ hs₂ hS₂)
  have hr : 0≤ Real.sqrt T/L := div_nonneg (Real.sqrt_nonneg _) hL.le
  calc
    _ ≤ _ := hn
    _ ≤ 4*(D*Z^ε*(1+‖t‖)^J+D*Z^ε*(1+‖t‖)^J)*V*(Real.sqrt T/L) := by
      gcongr
    _ = (8*D*V)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by ring
    _ ≤ (1+8*D*V)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
      gcongr
      linarith
end CenteredMomentFiniteProfileExceptional

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

def sourceControl (S : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W

def normalizedProfile (S : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  (sourceControl S W)⁻¹ • W

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤ sourceControl S W := apply_nonneg _ _

theorem sourceControl_zero (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (W : 𝓢(ℝ,ℂ)) (hW : sourceControl S W=0) : W=0 := by
  ext x
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact (SchwartzMap.norm_le_seminorm ℝ W x).trans
    ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans_eq hW)

theorem normalizedProfile_control (S) (W : 𝓢(ℝ,ℂ)) :
    sourceControl S (normalizedProfile S W)≤1 := by
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((sourceControl S W)⁻¹ • W)≤1
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (sourceControl_nonneg S W))]
  change (sourceControl S W)⁻¹*sourceControl S W≤1
  by_cases h : sourceControl S W=0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem normalizedProfile_support (S) (W : 𝓢(ℝ,ℂ)) :
    Function.support (normalizedProfile S W:ℝ→ℂ)⊆Function.support (W:ℝ→ℂ) := by
  intro x hx hw
  apply hx
  simp [normalizedProfile,smul_apply,hw]

theorem normalizedProfile_reconstruct (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (W : 𝓢(ℝ,ℂ)) : sourceControl S W • normalizedProfile S W=W := by
  by_cases h : sourceControl S W=0
  · rw [sourceControl_zero S hS W h]
    simp [sourceControl,normalizedProfile]
  · simp [normalizedProfile,smul_smul,h]

theorem twistedIdealSum_profile_smul (χ : Character) (W : 𝓢(ℝ,ℂ))
    (c t X : ℝ) : twistedIdealSum χ (c • W : 𝓢(ℝ,ℂ)) t X = (c:ℂ)*twistedIdealSum χ W t X := by
  unfold twistedIdealSum
  rw [←tsum_mul_left]
  apply tsum_congr
  intro I
  change _ * ((c:ℂ) * W _) = (c:ℂ) * (_ * W _)
  ring

theorem twistedIdealSum_normalized (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (χ : Character) (W : 𝓢(ℝ,ℂ)) (t X : ℝ) :
    twistedIdealSum χ W t X = (sourceControl S W:ℂ)*
      twistedIdealSum χ (normalizedProfile S W) t X := by
  rw [←twistedIdealSum_profile_smul,normalizedProfile_reconstruct S hS W]
end CenteredMomentFiniteProfileExceptional

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeTwist
open CenteredMomentHeckeCancellation CenteredMomentLattice
local notation "O" => Eisenstein.O

theorem rectangle_source_control (a b ε B : ℝ)
    (ha : 0< a) (hb : 0≤ b) (hε : 0<ε) (hB : 0≤ B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0< C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤ Z → ∀ η χ ψ : Character,
      (Ideal.absNorm χ.modulus:ℝ)≤ Z^B → Q≤ψ.modulus →
      CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A z : O, lambda∣m → (2:O)∣m →
      (∀ n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0< L →
      L≤ X₁ → L≤ X₂ → L≤ Y₁ → L≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
        twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,S,hS,hunit⟩ := rectangle_source_unit a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hunit Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have h := hbound (normalizedProfile S W₁) (normalizedProfile S W₂)
    ((normalizedProfile_support S W₁).trans hs₁)
    ((normalizedProfile_support S W₂).trans hs₂)
    (normalizedProfile_control S W₁) (normalizedProfile_control S W₂)
    Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have heq : (Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
      twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂) =
      ((sourceControl S W₁*sourceControl S W₂:ℝ):ℂ)*
      ((Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ (normalizedProfile S W₁) t X₁*
        twistedIdealSum χ (normalizedProfile S W₂) t X₂-
        twistedIdealSum χ (normalizedProfile S W₁) t Y₁*
        twistedIdealSum χ (normalizedProfile S W₂) t Y₂)) := by
    rw [twistedIdealSum_normalized S hS χ W₁ t X₁,
      twistedIdealSum_normalized S hS χ W₂ t X₂,
      twistedIdealSum_normalized S hS χ W₁ t Y₁,
      twistedIdealSum_normalized S hS χ W₂ t Y₂]
    push_cast
    ring
  rw [heq,norm_mul,Complex.norm_real,Real.norm_of_nonneg
    (mul_nonneg (sourceControl_nonneg S W₁) (sourceControl_nonneg S W₂))]
  exact (mul_le_mul_of_nonneg_left h
    (mul_nonneg (sourceControl_nonneg S W₁) (sourceControl_nonneg S W₂))).trans_eq (by ring)
end CenteredMomentFiniteProfileExceptional

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeVolume
open CenteredMomentHeckeTwist CenteredMomentExceptionalCappedAmplitude
local notation "O" => Eisenstein.O
theorem row_rectangle_source_control
    (a b ε B : ℝ) (ha : 0< a) (hb : 0≤ b) (hε : 0<ε) (hB : 0≤ B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0< C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤ Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (lambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,S,hS,hJ⟩ := rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η m A₀ z hm hA hz hmLam hm2 hcond hex t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  obtain ⟨χ,ψ,hχ,hprim,hind,hQψ,hrow⟩ := fixedInducingRow_controlled η Q m A₀ z hm hA hz hmLam hm2 hex
  have hχnorm : (Ideal.absNorm χ.modulus:ℝ) ≤ Z^B :=
    (show (Ideal.absNorm χ.modulus:ℝ) ≤ HeckeRowClosure.rowConductorBound η m 1 (A₀*z) by exact_mod_cast hχ).trans hcond
  simp_rw [rowTwistedSum_eq η χ m A₀ z hrow]
  exact hbound W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hχnorm hQψ hind m A₀ z hmLam hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

end CenteredMomentFiniteProfileExceptional

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeVolume
open CenteredMomentHeckeTwist CenteredMomentExceptionalCappedAmplitude
local notation "O" => Eisenstein.O
theorem capped_rectangle_source_control
    (a b ε B : ℝ) (ha : 0< a) (hb : 0≤ b) (hε : 0<ε) (hB : 0≤ B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0< C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤ Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (lambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/max 1 L) := by
  obtain ⟨J,S,hS,hJ⟩ := row_rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcancel⟩ := hJ Q hQ
  let D : ℝ := 2*(128*b)*(128*b)
  have hD : 0≤ D := by dsimp [D]; positivity
  refine ⟨C+D,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hcond hex
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let P₁ := sourceControl S W₁
  let P₂ := sourceControl S W₂
  have hP₁ : 0≤ P₁ := sourceControl_nonneg S W₁
  have hP₂ : 0≤ P₂ := sourceControl_nonneg S W₂
  have hw₁ (x:ℝ) : ‖W₁ x‖≤ P₁ :=
    (SchwartzMap.norm_le_seminorm ℝ W₁ x).trans
      (Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
        (s := S) (x := W₁) (i := (0, 0)) hS)
  have hw₂ (x:ℝ) : ‖W₂ x‖≤ P₂ :=
    (SchwartzMap.norm_le_seminorm ℝ W₂ x).trans
      (Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
        (s := S) (x := W₂) (i := (0, 0)) hS)
  by_cases hlarge : 1≤ L
  · rw [max_eq_right hlarge]
    apply (hcancel W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hcond hex
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY).trans
    gcongr
    exact le_add_of_nonneg_right hD
  · rw [max_eq_left (le_of_not_ge hlarge),div_one]
    have habs := normalized_rectangle_absolute η m A z W₁ W₂ b b P₁ P₂ hb hb hP₁ hP₂
      (fun _ hx=>(hs₁ hx).2) (fun _ hx=>(hs₂ hx).2) hw₁ hw₂
      t X₁ X₂ Y₁ Y₂ T (hL.trans_le hX₁) (hL.trans_le hX₂)
      (hL.trans_le hY₁) (hL.trans_le hY₂) hpX hpY
    have hc : D ≤ (C+D)*Z^ε*(1+‖t‖)^J := by
      calc
        _ ≤ C+D := le_add_of_nonneg_left hC.le
        _ ≤ (C+D)*Z^ε := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hε.le)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith [norm_nonneg t]))
    apply habs.trans
    calc
      _ = D*(P₁*P₂)*Real.sqrt T := by dsimp [D]; ring
      _ ≤ ((C+D)*Z^ε*(1+‖t‖)^J)*(P₁*P₂)*Real.sqrt T := by
        gcongr
      _ = _ := by dsimp [P₁,P₂]; ring
end CenteredMomentFiniteProfileExceptional

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots

local notation "O" => Eisenstein.O
theorem capped_slots_source_control
    (a b ε B : ℝ) (ha : 0< a) (hb : 0≤ b) (hε : 0<ε) (hB : 0≤ B) :
    ∃J : ℕ, ∃ R : Finset (ℕ×ℕ), (0,0)∈R ∧
      ∀Q : Ideal O,Q≠0 → ∃C : ℝ,0< C ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀(ι : Type*) [Fintype ι],∀Z : ℝ,1≤ Z →
      ∀(η : Character)(m A z : O),m≠0 → A≠0 → z≠0 → lambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S : ι→Finset (Ideal O))(β : ι→Ideal O→ℂ)(P b M : ι→ℝ),
      (∀i,0< P i) → (∀i,0≤ b i) → (∀i,0≤ M i) →
      (∀i,∀I∈S i,‖β i I‖≤ M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤ b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0< L → L≤ X₁ → L≤ X₂ → L≤ Y₁ → L≤ Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
        C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖t‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,P i)/max 1 L) := by
  obtain ⟨J,R,hR,hJ⟩ := capped_rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι _ Z hZ η m A z hm hA hz hml hm2 hc he S β P b M hP hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hR₁ := sourceControl_nonneg R W₁
  have hR₂ := sourceControl_nonneg R W₂
  have hT : 0< T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖≤(128*b i*M i)*P i := by
    convert rowSlot_bound η m A z (S i) (β i) t (b i*P i) (M i)
      (mul_nonneg (hb i) (hP i).le) (hM i) (hβ i) (hN i) using 1; ring
  exact whole_product_normalization _ (fun i=> rowSlot η m A z (S i) (β i) t)
    (fun i=>128*b i*M i) P (C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖t‖)^J) T (max 1 L) (by positivity) hT
    (zero_lt_one.trans_le (le_max_left _ _))
    (fun i=> mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hP hslots
    (hbound W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end CenteredMomentFiniteProfileExceptional

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentAllocatedCenteredCapped
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
lemma plain_norm_le_reduction (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,1≤ P i) (j:Fin 2):
    (Ideal.absNorm (selectedPlain L a j):ℝ)≤ formalReductionFactor L a P:=by
  have hN (k:Fin 2):(1:ℝ)≤ Ideal.absNorm (selectedPlain L a k):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr k)))
  have hh:(Ideal.absNorm (selectedPlain L a j):ℝ)≤ selectedNorm L a:=by
    fin_cases j
    · exact le_mul_of_one_le_right (by positivity) (hN 1)
    · exact le_mul_of_one_le_left (by positivity) (hN 0)
  exact hh.trans (le_mul_of_one_le_right (selectedNorm_pos L a).le
    (Finset.one_le_prod (fun i _=> hP i)))

lemma allocated_lower (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,1≤ P i) (Z r X:ℝ) (hZ:0< Z) (hX:Z^r≤ X) (j:Fin 2):
    Z^r/formalReductionFactor L a P≤ X/(Ideal.absNorm (selectedPlain L a j):ℝ):=by
  have hn:(0:ℝ)< Ideal.absNorm (selectedPlain L a j):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr j)))
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hZ.le _) hn
    (plain_norm_le_reduction L a P hP j)).trans (div_le_div_of_nonneg_right hX hn.le)

lemma remaining_volume (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,0< P i) (T:ℝ):
    (T/selectedNorm L a)*(∏i:liveIndices L a,P i)=
      (T*∏i,P i)/formalReductionFactor L a P:=by
  rw [Finset.prod_coe_sort]
  apply (eq_div_iff (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=> hP i))).ne').mpr
  exact raw_scale_identity L a T P


end CenteredMomentAllocatedCenteredCapped

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentExceptionalAllocationShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentDivisorBoundary CenteredMomentSlotRatios
open CenteredMomentUniformDivisorShell
local notation "O" => Eisenstein.O

lemma exact_max_cancellation (r r₁ : ℝ) :
    -r₁-max (r-r₁) 0 = -max r r₁ := by
  by_cases h : r ≤ r₁
  · rw [max_eq_right (by linarith : r-r₁≤0),max_eq_right h]
    ring
  · rw [max_eq_left (by linarith : 0≤ r-r₁),max_eq_left (le_of_not_ge h)]
    ring

def exceptionalWeight {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (s : Source ι) (v : Source κ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ⊕Fin 2))) (Z r : ℝ) : ℝ :=
  Z^(-Real.logb Z (formalReductionFactor D a s.P)-
    Real.logb Z (formalReductionFactor D b v.P)-
    max (r-Real.logb Z (formalReductionFactor D a s.P)) 0)

theorem active_exceptional_weight {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (s : Source ι) (v : Source κ) (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ⊕Fin 2)))
    (_ha : a∈s.active D) (hb : b∈v.active D) (Z r : ℝ) (hZ : 1< Z) :
    exceptionalWeight s v D a b Z r ≤ Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ) := by
  have hz : 0< Z := zero_lt_one.trans hZ
  have hn : (0:ℝ)< Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hv := v.active_boundary D hD b hb Z hZ
  have hm := exact_max_cancellation r (Real.logb Z (formalReductionFactor D a s.P))
  have he : -Real.logb Z (formalReductionFactor D a s.P)-
      Real.logb Z (formalReductionFactor D b v.P)-
      max (r-Real.logb Z (formalReductionFactor D a s.P)) 0 ≤
      v.allowance Z-r-Real.logb Z (Ideal.absNorm D:ℝ) := by
    linarith [le_max_left r (Real.logb Z (formalReductionFactor D a s.P))]
  unfold exceptionalWeight
  apply (Real.rpow_le_rpow_of_exponent_le hZ.le he).trans_eq
  rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hn]

theorem actual_exceptional_shell {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (N : ℕ) (hι : Fintype.card ι≤ N) (hκ : Fintype.card κ≤ N) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀(s : Source ι) (v : Source κ) (Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,1≤ T → 1< Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r) ≤
        C*(2*T)^(2*ε)*Z^(v.allowance Z-r) := by
  obtain ⟨C₁,hC₁,hcard₁⟩ := CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  obtain ⟨C₂,hC₂,hcard₂⟩ := CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=κ⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨256*C₁*C₂,by positivity,?_⟩
  intro s v Ds hD T Z r hT hZ hlo hhi
  have ht : 0< T := zero_lt_one.trans_le hT
  have hz : 0< Z := zero_lt_one.trans hZ
  have hc₁ (D : Ideal O) (hd : D∈Ds) : ((s.active D).card:ℝ)≤ C₁*(Ideal.absNorm D:ℝ)^ε := by
    apply (show ((s.active D).card:ℝ)≤ Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₁ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hc₂ (D : Ideal O) (hd : D∈Ds) : ((v.active D).card:ℝ)≤ C₂*(Ideal.absNorm D:ℝ)^ε := by
    apply (show ((v.active D).card:ℝ)≤ Fintype.card (Allocation D (Finset.univ:Finset (κ⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₂ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hp (D : Ideal O) (hd : D∈Ds) :
      (∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤
        (C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T) := by
    have hn : (0:ℝ)< Ideal.absNorm D := ht.trans_le (hlo D hd)
    have he : (Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε=(Ideal.absNorm D:ℝ)^(2*ε) := by
      rw [←Real.rpow_add hn]; congr 1; ring
    have hpow : (Ideal.absNorm D:ℝ)^(2*ε)≤(2*T)^(2*ε) :=
      Real.rpow_le_rpow hn.le (hhi D hd).le (by positivity)
    calc
      _ ≤ ∑_a∈s.active D,∑_b∈v.active D,Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ) :=
        Finset.sum_le_sum (fun a ha=> Finset.sum_le_sum (fun b hb=>
          active_exceptional_weight s v D (hD D hd) a b ha hb Z r hZ))
      _ = ((s.active D).card:ℝ)*((v.active D).card:ℝ)*(Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) := by simp; ring
      _ ≤ (C₁*(Ideal.absNorm D:ℝ)^ε)*(C₂*(Ideal.absNorm D:ℝ)^ε)*
          (Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hc₁ D hd) (hc₂ D hd) (by positivity) (by positivity)) (by positivity)
      _ = (C₁*C₂)*(Ideal.absNorm D:ℝ)^(2*ε)*(Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) := by rw [←he]; ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity))
        (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) ht (hlo D hd)) (by positivity) (by positivity)
  calc
    _ ≤ ∑_D∈Ds,(C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T) := Finset.sum_le_sum hp
    _ = (Ds.card:ℝ)*((C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T)) := by simp
    _ ≤ (256*T)*((C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T)) :=
      mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT (fun D hd=>(hD D hd).ne_zero) hhi) (by positivity)
    _ = (256*C₁*C₂)*(2*T)^(2*ε)*Z^(v.allowance Z-r) := by field_simp

def ShellBound (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C ε : ℝ) : Prop := ∀(s : Source ι) (v : Source κ) (Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,1≤ T → 1< Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r) ≤
        C*(2*T)^(2*ε)*Z^(v.allowance Z-r)

theorem uniform_subset_shell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ℝ) (hε : 0<ε) : ∃C : ℝ,0< C ∧ ∀J L : Finset ι,ShellBound J L C ε := by
  have he (p : Finset ι×Finset ι) : ∃C : ℝ,0< C ∧ ShellBound p.1 p.2 C ε :=
    actual_exceptional_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B : ℝ := 1+∑p : Finset ι×Finset ι,C p
  have hs : 0≤∑p : Finset ι×Finset ι,C p := Finset.sum_nonneg (fun p _=>(hC p).le)
  refine ⟨B,by dsimp [B]; linarith,?_⟩
  intro J L s v Ds hD T Z r hT hZ hlo hhi
  have hc : C (J,L)≤ B := by
    have hp := Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]; linarith
  exact (hbound (J,L) s v Ds hD T Z r hT hZ hlo hhi).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _))

theorem exceptional_shell_subpower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι→ℝ) (B δ : ℝ) (hB : 0≤ B) (hδ : 0<δ) :
    ∃C : ℝ,0< C ∧ ∀(J L : Finset ι) (s : Source J) (v : Source L),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds : Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,
      1≤ T → 1< Z → T≤ Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤ C*Z^(δ-r) := by
  let ε : ℝ := δ/(2*(B+1))
  have hε : 0<ε := div_pos hδ (by positivity)
  have he : 2*B*ε≤δ := by
    have hh : ε*(2*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := uniform_subset_shell (ι:=ι) ε hε
  let E : ℝ := Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(2*ε)*E,by dsimp [E]; positivity,?_⟩
  intro J L s v hvlo hvhi Ds hD T Z r hT hZ hTZ hlo hhi
  have ht : 0< T := zero_lt_one.trans_le hT
  have hz : 0< Z := zero_lt_one.trans hZ
  have hh := hbound J L s v Ds hD T Z r hT hZ hlo hhi
  have hv : Z^(v.allowance Z-r)≤ E*Z^(-r) := by
    calc
      _≤ Z^((∑i,logWindow (lo i) (hi i))/Real.log Z-r) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le
          (sub_le_sub_right (subset_allowance L v lo hi hvlo hvhi Z hZ) r)
      _=E*Z^(-r) := by rw [sub_eq_add_neg,Real.rpow_add hz,numerical_allowance Z _ hZ]
  have hpow : T^(2*ε)≤ Z^δ := by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith [he])
  apply hh.trans
  calc
    _≤ C*(2*T)^(2*ε)*(E*Z^(-r)) := mul_le_mul_of_nonneg_left hv (by positivity)
    _=(C*2^(2*ε)*E)*T^(2*ε)*Z^(-r) := by
      rw [Real.mul_rpow (by norm_num : 0≤(2:ℝ)) ht.le]; ring
    _≤(C*2^(2*ε)*E)*Z^δ*Z^(-r) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by dsimp [E]; positivity)) (by positivity)
    _=(C*2^(2*ε)*E)*Z^(δ-r) := by rw [mul_assoc,←Real.rpow_add hz]; rfl

end CenteredMomentExceptionalAllocationShell

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorRectangle CenteredMomentAllocatedCenteredCapped
open  CenteredMomentExceptionalCappedAmplitude
local notation "O" => Eisenstein.O
theorem allocated_source_control (lo hi ε B:ℝ) (hlo:0< lo) (hhi:0≤ hi) (hε:0<ε) (hB:0≤ B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0< C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ), Function.support (W₁:ℝ→ℂ)⊆Set.Icc lo hi →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc lo hi →
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀Z:ℝ,1< Z → ∀η:Character,∀m A z:O,m≠0 → A≠0 → z≠0 → lambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b M:ι→ℝ),
      (∀i,1≤ P i) → (∀i,0≤ b i) → (∀i,0≤ M i) →
      (∀i,∀I∈S i,‖β i I‖≤ M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤ b i*P i) →
      ∀(L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2))),
      ∀h X₁ X₂ Y₁ Y₂ T r:ℝ,Z^r≤ X₁ → Z^r≤ X₂ → Z^r≤ Y₁ → Z^r≤ Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖residualCenteredRow η m A z h S β P L a
        W₁ W₂ X₁ X₂ Y₁ Y₂ T‖≤
      C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖h‖)^J*(∏i:liveIndices L a,128*b i*M i)*
        (Real.sqrt ((T*∏i,P i)/formalReductionFactor L a P)/
          Z^(max (r-Real.logb Z (formalReductionFactor L a P)) 0)):=by
  obtain ⟨J,R,hR,hJ⟩:=capped_slots_source_control lo hi ε B hlo hhi hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι _ _ Z hZ η m A z hm hA hz hmLam hm2 hcond hex S β P b M hP hb hM hβ hN
    L a h X₁ X₂ Y₁ Y₂ T r hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hp (i:ι):0< P i:=zero_lt_one.trans_le (hP i)
  have hred:0< formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=> hp i))
  have hh:=hbound W₁ W₂ hs₁ hs₂ (liveIndices L a) Z hZ.le η m A z hm hA hz hmLam hm2 hcond hex
    (fun i=> S i) (fun i=>β i) (fun i=> P i) (fun i=> b i) (fun i=> M i)
    (fun i=> hp i) (fun i=> hb i) (fun i=> hM i) (fun i=> hβ i) (fun i=> hN i)
    h
    (X₁/Ideal.absNorm (selectedPlain L a 0)) (X₂/Ideal.absNorm (selectedPlain L a 1))
    (Y₁/Ideal.absNorm (selectedPlain L a 0)) (Y₂/Ideal.absNorm (selectedPlain L a 1))
    (T/selectedNorm L a) (Z^r/formalReductionFactor L a P)
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hred)
    (allocated_lower L a P hP Z r X₁ (zero_lt_one.trans hZ) hX₁ 0)
    (allocated_lower L a P hP Z r X₂ (zero_lt_one.trans hZ) hX₂ 1)
    (allocated_lower L a P hP Z r Y₁ (zero_lt_one.trans hZ) hY₁ 0)
    (allocated_lower L a P hP Z r Y₂ (zero_lt_one.trans hZ) hY₂ 1)
    (by rw [div_mul_div_comm,hXT];rfl) (by rw [div_mul_div_comm,hYT];rfl)
  rw [remaining_volume L a P hp T,max_raw_reduction Z _ r hZ hred] at hh
  exact hh

end CenteredMomentFiniteProfileExceptional

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentRadialPointwiseEnergy
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentSlotRatios CenteredMomentUniformDivisorShell
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma inverse_reduction (s:Data ι) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (ha:a∈s.toSource.active D)
    (Z:ℝ) (hZ:1< Z) :
    1/formalReductionFactor D a s.P≤ Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ) := by
  have hh:=s.toSource.active_pair_weight s.toSource D hD a a ha ha Z hZ
  rw [show formalReductionFactor D a s.P*formalReductionFactor D a s.P=
    (formalReductionFactor D a s.P)^2 by ring,Real.sqrt_sq (s.reduction_pos D a).le] at hh
  convert hh using 1
  congr 2
  ring

 theorem actual_pointwise_divisor (N:ℕ) (hι:Fintype.card ι≤ N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0< C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
      ∀E Z:ℝ,0≤ E → 1< Z → (∀a∈s.toSource.active D,childEnergy s r D a≤ E) →
      energy s r D≤ C*(Ideal.absNorm D:ℝ)^(2*ε)*Z^(s.toSource.allowance Z)*
        (s.profileFactor*E)/(Ideal.absNorm D:ℝ) := by
  obtain ⟨C₁,hC₁,henergy⟩:=CenteredMomentRadialEligibleEnergy.actual_source_from_children N hι ε hε
  obtain ⟨C₂,hC₂,hcard⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro s r D hD E Z hE hZ hc
  have hn:0<(Ideal.absNorm D:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg hn.le _
  have hsz:((s.toSource.active D).card:ℝ)≤ C₂*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((s.toSource.active D).card:ℝ)≤ Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard D hD.ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hs:(∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)≤
      (C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ)):=by
    calc
      _≤∑a∈s.toSource.active D,Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ):=
        Finset.sum_le_sum (fun a ha=> inverse_reduction s D hD a ha Z hZ)
      _=((s.toSource.active D).card:ℝ)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ)):=by simp
      _≤ _:=mul_le_mul_of_nonneg_right hsz (div_nonneg (Real.rpow_nonneg (by linarith) _) hn.le)
  apply (henergy s r D hD E hE hc).trans
  calc
    _≤ C₁*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ((C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ))):=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg (mul_nonneg hC₁.le hp) s.profile_nonneg) hE)
    _=_:=by
      have he:(Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε=(Ideal.absNorm D:ℝ)^(2*ε):=by
        rw [←Real.rpow_add hn];congr 1;ring
      calc
        _=(C₁*C₂)*((Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε)*
          Z^(s.toSource.allowance Z)*(s.profileFactor*E)/(Ideal.absNorm D:ℝ):=by ring
        _=_:=by rw [he]

end CenteredMomentRadialPointwiseEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentRadialPointwiseUniform
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentRadialPointwiseEnergy CenteredMomentUniformDivisorShell
open CenteredMomentSlotRatios
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Bound (ι:Type*) [Fintype ι] [DecidableEq ι] (C ε:ℝ) : Prop :=
  ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
    ∀E Z:ℝ,0≤ E → 1< Z → (∀a∈s.toSource.active D,childEnergy s r D a≤ E) →
    energy s r D≤ C*(Ideal.absNorm D:ℝ)^(2*ε)*Z^(s.toSource.allowance Z)*
      (s.profileFactor*E)/(Ideal.absNorm D:ℝ)

 theorem uniform_subset (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0< C ∧ ∀J:Finset ι,Bound J C ε := by
  have he (J:Finset ι):∃C:ℝ,0< C ∧ Bound J C ε:=
    actual_pointwise_divisor (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose C hC hb using he
  let D:ℝ:=1+∑J:Finset ι,C J
  have hs:0≤∑J:Finset ι,C J:=Finset.sum_nonneg (fun J _=>(hC J).le)
  refine ⟨D,by dsimp [D];linarith,?_⟩
  intro J s r I hI E Z hE hZ hc
  have hd:C J≤ D:=by
    have hh:=Finset.single_le_sum (fun J _=>(hC J).le) (Finset.mem_univ J)
    dsimp [D];linarith
  apply (hb J s r I hI E Z hE hZ hc).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg s.profile_nonneg hE)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
  exact mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (Nat.cast_nonneg _) _)

 theorem actual_uniform_divisor (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C:ℝ,0< C ∧ ∀(J:Finset ι) (s:Data J),(∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      ∀(r:Radial) (D:Ideal O),Squarefree D → ∀E Z:ℝ,0≤ E → 1< Z →
      (Ideal.absNorm D:ℝ)≤ Z^B → (∀a∈s.toSource.active D,childEnergy s r D a≤ E) →
      energy s r D≤ C*Z^δ*(s.profileFactor*E)/(Ideal.absNorm D:ℝ) := by
  let ε:ℝ:=δ/(2*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  obtain ⟨C,hC,hbound⟩:=uniform_subset (ι:=ι) ε hε
  let A:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*A,by dsimp [A];positivity,?_⟩
  intro J s hlo hhi r D hD E Z hE hZ hN hc
  have hz:0< Z:=zero_lt_one.trans hZ
  have ha:Z^(s.toSource.allowance Z)≤ A:=by
    dsimp [A]
    rw [←numerical_allowance Z _ hZ]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (subset_allowance J s.toSource lo hi hlo hhi Z hZ)
  have hp:(Ideal.absNorm D:ℝ)^(2*ε)≤ Z^δ:=by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    have he:ε*(2*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  apply (hbound J s r D hD E Z hE hZ hc).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg s.profile_nonneg hE)
  calc
    _≤ C*Z^δ*A:=mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) ha
      (Real.rpow_nonneg hz.le _) (by positivity)
    _=_:=by ring

end CenteredMomentRadialPointwiseUniform

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentCommonRadialCost
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentAllocationCost
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma sqrt_nat_le_add_one (n:ℕ) : Real.sqrt (n:ℝ)≤(n:ℝ)+1 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]

omit [DecidableEq ι] in
 theorem paired_card_subpower (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C0:ℝ,0< C0 ∧ ∀(s:Input ι) (C D:Ideal O),C≠0 → D≠0 →
      ∀Z:ℝ,1< Z → (Ideal.absNorm C:ℝ)≤ Z^B → (Ideal.absNorm D:ℝ)≤ Z^B →
      (Real.sqrt ((actualAllocations s.pools C).card:ℝ)*Real.sqrt ((actualAllocations s.pools D).card:ℝ))*
        (((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ))≤ C0*Z^δ := by
  let ε:ℝ:=δ/(4*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  obtain ⟨D0,hD0,hcard⟩:=actualAllocations_uniform_small_power (Fintype.card (ι⊕Fin 2)) ε hε
  refine ⟨(D0+1)^4,by positivity,?_⟩
  intro s C D hC hD Z hZ hNC hND
  have hz:0< Z:=zero_lt_one.trans hZ
  have bound (I:Ideal O) (hI:I≠0) (hn:(Ideal.absNorm I:ℝ)≤ Z^B):
      ((actualAllocations s.pools I).card:ℝ)+1≤(D0+1)*Z^(B*ε):=by
    have hi:(1:ℝ)≤ Ideal.absNorm I:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have hh:=hcard (le_refl (Fintype.card (ι⊕Fin 2))) s.pools I hI
    have hp:(Ideal.absNorm I:ℝ)^ε≤ Z^(B*ε):=by
      apply (Real.rpow_le_rpow (by positivity) hn hε.le).trans_eq
      rw [←Real.rpow_mul hz.le]
    have hone:1≤ Z^(B*ε):=Real.one_le_rpow hZ.le (mul_nonneg hB hε.le)
    nlinarith [mul_le_mul_of_nonneg_left hp hD0.le]
  have hc:=bound C hC hNC
  have hd:=bound D hD hND
  have hSc:Real.sqrt ((actualAllocations s.pools C).card:ℝ)≤(D0+1)*Z^(B*ε):=
    (sqrt_nat_le_add_one _).trans hc
  have hSd:Real.sqrt ((actualAllocations s.pools D).card:ℝ)≤(D0+1)*Z^(B*ε):=
    (sqrt_nat_le_add_one _).trans hd
  have hcc:((actualAllocations s.pools C).card:ℝ)≤(D0+1)*Z^(B*ε):=by linarith
  have hdd:((actualAllocations s.pools D).card:ℝ)≤(D0+1)*Z^(B*ε):=by linarith
  calc
    _≤(((D0+1)*Z^(B*ε))*((D0+1)*Z^(B*ε)))*
        (((D0+1)*Z^(B*ε))*((D0+1)*Z^(B*ε))):=by gcongr
    _=(D0+1)^4*Z^(4*B*ε):=by
      rw [show ((D0+1)*Z^(B*ε)*((D0+1)*Z^(B*ε)))*
        ((D0+1)*Z^(B*ε)*((D0+1)*Z^(B*ε)))=(D0+1)^4*(Z^(B*ε))^4 by ring]
      rw [←Real.rpow_mul_natCast hz.le]
      congr 2
      ring
    _≤ _:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have he:ε*(4*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
      nlinarith

omit [DecidableEq ι] in
 theorem card_squared_subpower (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C0:ℝ,0< C0 ∧ ∀(s:Input ι) (C:Ideal O),C≠0 →
      ∀Z:ℝ,1< Z → (Ideal.absNorm C:ℝ)≤ Z^B →
      ((actualAllocations s.pools C).card:ℝ)^2≤ C0*Z^δ := by
  obtain ⟨C0,hC0,hbound⟩:=paired_card_subpower (ι:=ι) B δ hB hδ
  refine ⟨C0,hC0,?_⟩
  intro s C hC Z hZ hn
  have hh:=hbound s C C hC hC Z hZ hn hn
  have he:Real.sqrt ((actualAllocations s.pools C).card:ℝ)*
      Real.sqrt ((actualAllocations s.pools C).card:ℝ)=((actualAllocations s.pools C).card:ℝ):=by
    rw [←pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [he] at hh
  by_cases hz:(actualAllocations s.pools C).card=0
  · rw [hz,Nat.cast_zero,zero_pow (by decide)]
    positivity
  · have hc:(1:ℝ)≤(actualAllocations s.pools C).card:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    apply le_trans ?_ hh
    nlinarith [sq_nonneg ((actualAllocations s.pools C).card:ℝ)]

end CenteredMomentCommonRadialCost

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Filter

namespace CenteredMomentWholeDivisorShell
open  UniqueFactorizationMonoid
open CenteredMomentMobiusRegroup CenteredMomentDyadicCount CenteredMomentSectorLocalization
local notation "O" => Eisenstein.O

lemma divisorPool_nonzero_norm {α : Type*} (T : Finset α) (B : α→Ideal O)
    (hB : ∀j∈T,B j≠0) (Y : ℝ) (hY : ∀j∈T,(Ideal.absNorm (B j):ℝ)≤ Y)
    (D : Ideal O) (hD : D∈divisorPool T B) : D≠0 ∧ (D.absNorm:ℝ)≤ Y := by
  obtain ⟨j,hj,hd⟩:=Finset.mem_biUnion.mp hD
  have hdiv := (mem_idealDivisors (hB j hj)).mp hd
  have hn : 0<(B j).absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hB j hj))
  have hle : (D.absNorm:ℝ)≤(B j).absNorm := by
    exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hdiv)
  exact ⟨IdealDivisorBound.divisor_ne_zero (hB j hj) hd,hle.trans (hY j hj)⟩

lemma moebius_norm_le_one (D : Ideal O) : ‖(moebius D:ℂ)‖≤1 := by
  by_cases hD : Squarefree D
  · simp only [hD.moebius_eq,Int.cast_pow,Int.cast_neg,Int.cast_one,norm_pow,norm_neg,norm_one,one_pow,le_refl]
  · simp only [moebius_of_not_squarefree hD,Int.cast_zero,norm_zero,zero_le_one]

lemma squarefree_of_moebius_ne_zero (D : Ideal O) (hD : (moebius D:ℂ)≠0) : Squarefree D := by
  by_contra hn
  exact hD (by rw [moebius_of_not_squarefree hn,Int.cast_zero])

def live (Ds : Finset (Ideal O)) : Finset (Ideal O) := Ds.filter (fun D=>(moebius D:ℂ)≠0)

lemma mem_live (Ds : Finset (Ideal O)) (D : Ideal O) :
    D∈live Ds ↔ D∈Ds ∧ (moebius D:ℂ)≠0 := Finset.mem_filter

lemma live_squarefree (Ds : Finset (Ideal O)) (D : Ideal O) (hD : D∈live Ds) : Squarefree D :=
  squarefree_of_moebius_ne_zero D ((mem_live Ds D).mp hD).2

lemma live_norm_one (Ds : Finset (Ideal O)) (D : Ideal O) (hD : D∈live Ds) : 1≤(D.absNorm:ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (live_squarefree Ds D hD).ne_zero)

theorem sum_moebius_live (Ds : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑D∈Ds,(moebius D:ℂ)*f D)=∑D∈live Ds,(moebius D:ℂ)*f D := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro D hD hn
  have hz : (moebius D:ℂ)=0 := by
    by_contra hne
    exact hn ((mem_live Ds D).mpr ⟨hD,hne⟩)
  rw [hz,zero_mul]

theorem sum_norm_moebius_live (Ds : Finset (Ideal O)) (f : Ideal O→ℝ) :
    (∑D∈Ds,‖(moebius D:ℂ)‖*f D)=∑D∈live Ds,‖(moebius D:ℂ)‖*f D := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro D hD hn
  have hz : (moebius D:ℂ)=0 := by
    by_contra hne
    exact hn ((mem_live Ds D).mpr ⟨hD,hne⟩)
  rw [hz,norm_zero,zero_mul]

def normKey (D : Ideal O) : ℤ := ⌊Real.logb 2 (D.absNorm:ℝ)⌋
def shell (Ds : Finset (Ideal O)) (n : ℤ) : Finset (Ideal O) := (live Ds).filter (fun D=> normKey D=n)
def selectedShells (Ds : Finset (Ideal O)) : Finset ℤ := (live Ds).image normKey

lemma normKey_eq_iff (D : Ideal O) (hD : D≠0) (n : ℤ) :
    normKey D=n ↔ dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  have hn : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hl := Real.logb_le_logb (by norm_num : (1:ℝ)<2) (dyadicScale_pos n) hn
  have hu := Real.logb_lt_logb_iff (by norm_num : (1:ℝ)<2) hn (dyadicScale_pos (n+1))
  simp only [logb_dyadicScale,Int.cast_add,Int.cast_one] at hl hu
  rw [normKey,Int.floor_eq_iff,←hl,←dyadicScale_add,←hu]

lemma mem_shell_iff (Ds : Finset (Ideal O)) (n : ℤ) (D : Ideal O) :
    D∈shell Ds n ↔ D∈Ds ∧ (moebius D:ℂ)≠0 ∧
      dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  rw [shell,Finset.mem_filter]
  constructor
  · rintro ⟨hd,hk⟩
    exact ⟨((mem_live Ds D).mp hd).1,((mem_live Ds D).mp hd).2,
      (normKey_eq_iff D (live_squarefree Ds D hd).ne_zero n).mp hk⟩
  · rintro ⟨hd,hm,hlo,hhi⟩
    exact ⟨(mem_live Ds D).mpr ⟨hd,hm⟩,
      (normKey_eq_iff D (squarefree_of_moebius_ne_zero D hm).ne_zero n).mpr ⟨hlo,hhi⟩⟩

lemma shell_disjoint (Ds : Finset (Ideal O)) (m n : ℤ) (hmn : m≠n) :
    Disjoint (shell Ds m) (shell Ds n) := by
  apply Finset.disjoint_left.mpr
  intro D hm hn
  exact hmn ((Finset.mem_filter.mp hm).2.symm.trans (Finset.mem_filter.mp hn).2)

lemma shell_nonempty_iff (Ds : Finset (Ideal O)) (n : ℤ) :
    (shell Ds n).Nonempty ↔ n∈selectedShells Ds := by
  constructor
  · rintro ⟨D,hD⟩
    exact Finset.mem_image.mpr ⟨D,(Finset.mem_filter.mp hD).1,(Finset.mem_filter.mp hD).2⟩
  · rintro hn
    obtain ⟨D,hD,hk⟩:=Finset.mem_image.mp hn
    exact ⟨D,Finset.mem_filter.mpr ⟨hD,hk⟩⟩

lemma biUnion_shell (Ds : Finset (Ideal O)) :
    (selectedShells Ds).biUnion (shell Ds)=live Ds := by
  ext D
  simp only [Finset.mem_biUnion,shell,Finset.mem_filter]
  constructor
  · rintro ⟨n,hn,hd,hk⟩;exact hd
  · intro hd
    exact ⟨normKey D,Finset.mem_image.mpr ⟨D,hd,rfl⟩,hd,rfl⟩

theorem sum_moebius_shells (Ds : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑D∈Ds,(moebius D:ℂ)*f D)=
      ∑n∈selectedShells Ds,∑D∈shell Ds n,(moebius D:ℂ)*f D := by
  rw [sum_moebius_live]
  exact (Finset.sum_fiberwise_of_maps_to (fun D hD=> Finset.mem_image.mpr ⟨D,hD,rfl⟩) _).symm

theorem sum_norm_moebius_shells (Ds : Finset (Ideal O)) (f : Ideal O→ℝ) :
    (∑D∈Ds,‖(moebius D:ℂ)‖*f D)=
      ∑n∈selectedShells Ds,∑D∈shell Ds n,‖(moebius D:ℂ)‖*f D := by
  rw [sum_norm_moebius_live]
  exact (Finset.sum_fiberwise_of_maps_to (fun D hD=> Finset.mem_image.mpr ⟨D,hD,rfl⟩) _).symm

lemma selected_scale_bounds (Ds : Finset (Ideal O)) (Y : ℝ)
    (hY : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤ Y)
    (n : ℤ) (hn : n∈selectedShells Ds) :
    1≤ dyadicScale n ∧ dyadicScale n≤ Y := by
  obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hn
  have hd:=live_squarefree Ds D hD
  have hnorm:=live_norm_one Ds D hD
  have hkey : 0≤ normKey D := Int.floor_nonneg.mpr
    (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hnorm)
  have hscale : 1≤ dyadicScale (normKey D) := by
    simpa only [dyadicScale,zpow_zero] using
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hkey
  exact ⟨hscale,((normKey_eq_iff D hd.ne_zero _).mp rfl).1.trans
    (hY D ((mem_live Ds D).mp hD).1 ((mem_live Ds D).mp hD).2)⟩

lemma selected_subset_indices (Ds : Finset (Ideal O)) (Y : ℝ) (hY : 1≤ Y)
    (hbound : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤ Y) :
    selectedShells Ds⊆indices 1 Y := by
  intro n hn
  have hh:=selected_scale_bounds Ds Y hbound n hn
  exact (mem_indices_iff_scale 1 Y (by norm_num) (zero_lt_one.trans_le hY) n).mpr
    ⟨hh.1,hh.2.trans (by linarith)⟩

theorem selected_card_log (B Z : ℝ) (hB : 0≤ B) (hZ : 1≤ Z)
    (Ds : Finset (Ideal O))
    (hbound : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤ Z^B) :
    ((selectedShells Ds).card:ℝ)≤(3+B/Real.log 2)*(1+Real.log Z) := by
  have hY : 1≤ Z^B := Real.one_le_rpow hZ hB
  have hc : ((selectedShells Ds).card:ℝ)≤(indices 1 (Z^B)).card := by
    exact_mod_cast Finset.card_le_card (selected_subset_indices Ds (Z^B) hY hbound)
  have hi:=indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY
    (by simp only [div_one,one_mul,le_refl])
  exact hc.trans (by simpa only [Real.logb_one,add_zero] using hi)

theorem selected_card_subpower (B δ : ℝ) (hB : 0≤ B) (hδ : 0<δ) :
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀Ds:Finset (Ideal O),
      (∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤ Z^B) →
      ((selectedShells Ds).card:ℝ)≤ C*Z^δ := by
  let C:=2*(3+B/Real.log 2)
  have hC : 0< C := by
    have hh:=div_nonneg hB (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [C];linarith
  have ht:=(isLittleO_log_rpow_rpow_atTop (1:ℝ) hδ).bound (by norm_num : (0:ℝ)<1)
  refine ⟨C,hC,?_⟩
  filter_upwards [ht,eventually_ge_atTop (Real.exp 1)] with Z ht hZ
  have hz : 1< Z := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hZ
  have hl : 1≤ Real.log Z := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hZ
  have hp : Real.log Z≤ Z^δ := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤ Real.log Z),
      abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hz).le _),one_mul] using ht
  refine ⟨hz,?_⟩
  intro Ds hb
  apply (selected_card_log B Z hB hz.le Ds hb).trans
  have hk : 0≤3+B/Real.log 2 := by positivity
  dsimp [C]
  nlinarith [mul_le_mul_of_nonneg_left hp hk]

theorem divisorPool_card_log {α : Type*} (T : Finset α) (B : α→Ideal O)
    (hB : ∀j∈T,B j≠0) (L Z : ℝ) (hL : 0≤ L) (hZ : 1≤ Z)
    (hN : ∀j∈T,(Ideal.absNorm (B j):ℝ)≤ Z^L) :
    ((selectedShells (divisorPool T B)).card:ℝ)≤(3+L/Real.log 2)*(1+Real.log Z) :=
  selected_card_log L Z hL hZ _ (fun D hD _=>(divisorPool_nonzero_norm T B hB _ hN D hD).2)

theorem divisorPool_card_subpower (L δ : ℝ) (hL : 0≤ L) (hδ : 0<δ) :
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀{α:Type*}(T:Finset α)(B:α→Ideal O),
      (∀j∈T,B j≠0) → (∀j∈T,(Ideal.absNorm (B j):ℝ)≤ Z^L) →
      ((selectedShells (divisorPool T B)).card:ℝ)≤ C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower L δ hL hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro α T B hB hN
  exact hz.2 _ (fun D hD _=>(divisorPool_nonzero_norm T B hB _ hN D hD).2)

lemma shell_member_data (Ds : Finset (Ideal O)) (n : ℤ) (D : Ideal O)
    (hD : D∈shell Ds n) :
    D∈Ds ∧ (moebius D:ℂ)≠0 ∧ Squarefree D ∧ D≠0 ∧
      dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  have hh:=(mem_shell_iff Ds n D).mp hD
  have hs:=squarefree_of_moebius_ne_zero D hh.2.1
  exact ⟨hh.1,hh.2.1,hs,hs.ne_zero,hh.2.2⟩

theorem finite_pair_mobius_shells {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α→Ideal O) (B : β→Ideal O) (hB : ∀j∈T,B j≠0) (F : α→β→ℂ) :
    (∑i∈S,∑j∈T,if IsCoprime (A i) (B j) then F i j else 0)=
      ∑n∈selectedShells (divisorPool T B),∑D∈shell (divisorPool T B) n,
        (moebius D:ℂ)*∑i∈S,∑j∈T,if D∣A i ∧ D∣B j then F i j else 0 := by
  rw [finite_pair_mobius S T A B hB F]
  exact sum_moebius_shells _ _

theorem divisorPool_weighted_shells {α : Type*} (T : Finset α) (B : α→Ideal O)
    (f : Ideal O→ℝ) :
    (∑D∈divisorPool T B,‖(moebius D:ℂ)‖*f D)=
      ∑n∈selectedShells (divisorPool T B),∑D∈shell (divisorPool T B) n,
        ‖(moebius D:ℂ)‖*f D := sum_norm_moebius_shells _ _

end CenteredMomentWholeDivisorShell

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
