/-
First common rows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.FirstPhysicalHeights
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.FirstCoreRayAttachment

/-!
# First common rows

Common indices, norms and weights of the first descent block; finite prime-mark bounds; first
physical common rows and their integrals.
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

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
noncomputable section
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O

theorem finite_primeSupport_card {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (U : Finset ι) :
    (primeSupport (Ideal.span {∏ i ∈ U, p i})).card = U.card := by
  have hinj : Function.Injective (fun i => (Ideal.span {p i} : Ideal Eis)) := by
    intro i j hij
    by_contra hne
    have ht := (hcop hne).sup_eq
    rw [hij, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
  have hf := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    (m := U.val.map (fun i => (Ideal.span {p i} : Ideal Eis))) (by
      intro P hP
      obtain ⟨i,hi,rfl⟩ := Multiset.mem_map.mp hP
      exact Ideal.prime_of_isPrime (NeZero.ne _) inferInstance)
  change UniqueFactorizationMonoid.normalizedFactors (∏ i ∈ U, Ideal.span {p i}) = _ at hf
  have he : primeSupport (Ideal.span {∏ i ∈ U, p i}) = U.image (fun i => Ideal.span {p i}) := by
    simp only [primeSupport, span_finset_prime_product, hf, Multiset.toFinset_map, Finset.val_toFinset]
  rw [he, Finset.card_image_of_injective U hinj]

theorem finite_primeMark_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) → ∀ U : Finset ι,
      ‖primeMark slots lists a U‖ ≤ C * (primeProductNorm p U)^ε := by
  obtain ⟨C,hC,hb⟩ := CompletedGauss.prime_support_subsets_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha U
  have hI : (Ideal.span {∏ i ∈ U, p i} : Ideal Eis) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  have hh := hb (Ideal.span {∏ i ∈ U, p i}) hI
  rw [finite_primeSupport_card p hcop U] at hh
  have hn : (Ideal.absNorm (Ideal.span {∏ i ∈ U, p i}) : ℝ) = primeProductNorm p U :=
    (ringComplex_norm_sq_eq_absNorm_span _).symm
  rw [hn] at hh
  exact (primeMark_norm_le_divisor_count slots lists a U hslots ha).trans hh

theorem finite_primeMark_extracted_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) → ∀ A U : Finset ι,
      ‖primeMark slots lists a (A ∪ U)‖ ≤ (2:ℝ)^A.card * C * (primeProductNorm p U)^ε := by
  obtain ⟨C,hC,hb⟩ := CompletedGauss.prime_support_subsets_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A U
  have hI : (Ideal.span {∏ i ∈ U, p i} : Ideal Eis) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  have hh := hb (Ideal.span {∏ i ∈ U, p i}) hI
  rw [finite_primeSupport_card p hcop U] at hh
  have hn : (Ideal.absNorm (Ideal.span {∏ i ∈ U, p i}) : ℝ) = primeProductNorm p U :=
    (ringComplex_norm_sq_eq_absNorm_span _).symm
  rw [hn] at hh
  calc
    _ ≤ (2:ℝ)^(A ∪ U).card := primeMark_norm_le_divisor_count _ _ _ _ hslots ha
    _ ≤ (2:ℝ)^(A.card+U.card) := pow_le_pow_right₀ (by norm_num) (Finset.card_union_le _ _)
    _ = (2:ℝ)^A.card * (2:ℝ)^U.card := pow_add _ _ _
    _ ≤ (2:ℝ)^A.card * (C * (primeProductNorm p U)^ε) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O

def markedColumn {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (C : Finset ι → ℂ) (U : Finset ι) : ℂ :=
  primeMark slots lists a (A ∪ U) * C U

lemma markedColumn_source_support {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (C : Finset ι → ℂ) (U : Finset ι)
    (h : markedColumn slots lists a A C U ≠ 0) : C U ≠ 0 :=
  (mul_ne_zero_iff.mp h).2

theorem markedColumn_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (C : Finset ι → ℂ) (G X M : ℝ),
      0 ≤ G → 0 < X →
      (∀ U ∈ F.powerset, ‖C U‖ ≤ G) →
      (∀ U ∈ F.powerset, C U ≠ 0 → columnLog p X U ≤ M) →
      ∀ U ∈ F.powerset, ‖markedColumn slots lists a A C U‖ ≤
        (2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_extracted_bound ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A F C G X M hG hX hC hsupport U hU
  by_cases hz : C U = 0
  · simp only [markedColumn,hz,mul_zero,norm_zero]
    positivity
  · have hn := columnLog_norm_upper p hp X M hX U (hsupport U hU hz)
    rw [markedColumn,norm_mul]
    have hm := hmark p hp hcop slots lists a hslots ha A U
    have hnorm : 0 < primeProductNorm p U := primeProductNorm_pos p hp U
    apply (mul_le_mul hm (hC U hU) (norm_nonneg _) (by positivity)).trans
    gcongr

theorem marked_first_kernel_remainder (ε : ℝ) (hε : 0 < ε) (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct Cm : ℝ), 0 < Ct ∧ 0 < Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
      (F B A₁ A₂ : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool), Disjoint F B →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
        (a₁ a₂ : σ → ι → ℂ),
      (slots₁ : Set σ).PairwiseDisjoint lists₁ → (slots₂ : Set σ).PairwiseDisjoint lists₂ →
      (∀ i ∈ slots₁, ∀ k ∈ lists₁ i, ‖a₁ i k‖ ≤ 1) →
      (∀ i ∈ slots₂, ∀ k ∈ lists₂ i, ‖a₂ i k‖ ≤ 1) →
      ∀ (C₁ C₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0 ≤ G₁ → 0 ≤ G₂ → 0 < X₁ → 0 < X₂ → 0 < K → 0 ≤ P →
      (∀ U ∈ F.powerset, ‖C₁ U‖ ≤ G₁) → (∀ U ∈ F.powerset, ‖C₂ U‖ ≤ G₂) →
      (∀ U ∈ F.powerset, C₁ U ≠ 0 → columnLog p X₁ U ≤ M₁) →
      (∀ U ∈ F.powerset, C₂ U ≠ 0 → columnLog p X₂ U ≤ M₂) →
      ∀ d : Eis, d ≠ 0 →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let G₁' := (2:ℝ)^A₁.card * Cm * U₁^ε * G₁
      let G₂' := (2:ℝ)^A₂.card * Cm * U₂^ε * G₂
      let slow := K/(‖ringComplex d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑' h : {h : Eis // h ∉ T}, actualFirstKernel p hp hg F B v ε₁ ε₂
        (markedColumn slots₁ lists₁ a₁ A₁ C₁) (markedColumn slots₂ lists₂ a₂ A₂ C₂)
        W (fun _ => 1) (fun _ => 1) X₁ X₂ K d h.val‖ ≤
      ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁'*G₂'*K) *
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_actualFirstKernel_disk_remainder order
  obtain ⟨Cm,hCm,hmark⟩ := markedColumn_uniform_bound ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc F B A₁ A₂ v ε₁ ε₂ hFB
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ hl₁ hl₂ ha₁ ha₂ C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂
    hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hs₁ hs₂ d hd
  apply htail p hp hinj hcop hg hc F B v ε₁ ε₂ hFB _ _ W _ _ X₁ X₂ K P M₁ M₂
    (by positivity) (by positivity) hX₁ hX₂ hK hP
  · exact hmark p hp hcop slots₁ lists₁ a₁ hl₁ ha₁ A₁ F C₁ G₁ X₁ M₁ hG₁ hX₁ hC₁ hs₁
  · exact hmark p hp hcop slots₂ lists₂ a₂ hl₂ ha₂ A₂ F C₂ G₂ X₂ M₂ hG₂ hX₂ hC₂ hs₂
  · intro U hU hn
    exact hs₁ U hU (markedColumn_source_support _ _ _ _ _ _ hn)
  · intro U hU hn
    exact hs₂ U hU (markedColumn_source_support _ _ _ _ _ _ hn)
  · exact hd

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem full_first_supported_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),Disjoint F B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0≤ G₁ → 0≤ G₂ → 0<X₁ → 0<X₂ → 0<K → 0≤ P →
      (∀N∈F.powerset,‖C₁ N‖≤ G₁) → (∀N∈F.powerset,‖C₂ N‖≤ G₂) →
      (∀N∈F.powerset,C₁ N≠0 → columnLog p X₁ N≤ M₁) →
      (∀N∈F.powerset,C₂ N≠0 → columnLog p X₂ N≤ M₂) →
      ∀(d : O),d≠0 → ∀ T : Finset O,
      (∀ N∈F.powerset,∀ Q∈F.powerset,Disjoint N Q → C₁ N≠0 → C₂ Q≠0 →
        ∀ h : O,h∉T → P≤(K/(‖ringComplex d‖^2*
          primeProductNorm p ((N∪Q)∪cubeActiveSupport B v ε₁ ε₂)))*‖ringComplex h‖^2) →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let slow := K/(‖ringComplex d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val‖≤
      ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁*G₂*K)*
        ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+P)^A)) := by
  have hdc := diagonalControl_nonneg sieveCutoff
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc F B v ε₁ ε₂ hFB C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂ hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hS₁ hS₂ d hd T hT
  dsimp only
  let U₁:=X₁*Real.exp M₁
  let U₂:=X₂*Real.exp M₂
  let S:=cubeActiveSupport B v ε₁ ε₂
  let slow:=K/(‖ringComplex d‖^2*primeProductNorm p S*U₁*U₂)
  let tail:ℝ:=(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 slow)^2*(1+P)^A)
  let Q:ℝ:=G₁*G₂*K*tail
  have hU₁:0<U₁:=mul_pos hX₁ (Real.exp_pos _)
  have hU₂:0<U₂:=mul_pos hX₂ (Real.exp_pos _)
  have hNd:0<‖ringComplex d‖^2:=sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hd))
  have hslow:0<slow:=div_pos hK (mul_pos (mul_pos (mul_pos hNd (primeProductNorm_pos p hp S)) hU₁) hU₂)
  have hH:0≤ P:=hP
  have htail:0≤ tail:=by dsimp [tail]; positivity
  have hQ:0≤ Q:=mul_nonneg (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le) htail
  let rem (N R:Finset ι):ℂ:=if Disjoint N R then
    ∑'h:{h:O // h∉T},canonicalPairMode p hp hg N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val else 0
  have hnzero (N R:Finset ι) (hn:C₁ N=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hn]
  have hrzero (N R:Finset ι) (hr:C₂ R=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hr]
  have heq : (∑'h:{h:O // h∉T},actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val)=
      ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,rem N R := by
    rw [actualFirstKernel_complement_eq_pairs p hp hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K hK d hd T]
    change (∑N∈F.powerset,∑R∈F.powerset,rem N R)=_
    calc
      _ = ∑N∈boundedPrimeSupports p F U₁,∑R∈F.powerset,rem N R := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro N hN hn
        have hz:C₁ N=0:=by
          by_contra h
          exact hn (Finset.mem_filter.mpr ⟨hN,columnLog_norm_upper p hp X₁ M₁ hX₁ N (hS₁ N hN h)⟩)
        simp only [hnzero N _ hz,Finset.sum_const_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro N hN
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro R hR hr
        have hz:C₂ R=0:=by
          by_contra h
          exact hr (Finset.mem_filter.mpr ⟨hR,columnLog_norm_upper p hp X₂ M₂ hX₂ R (hS₂ R hR h)⟩)
        exact hrzero N R hz
  have hrem (N:Finset ι) (hN:N∈boundedPrimeSupports p F U₁) (R:Finset ι) (hR:R∈boundedPrimeSupports p F U₂):‖rem N R‖≤ Q:=by
    have hNF: N∈F.powerset:=(Finset.mem_filter.mp hN).1
    have hRF: R∈F.powerset:=(Finset.mem_filter.mp hR).1
    by_cases hn:C₁ N=0
    · rw [hnzero N R hn,norm_zero]; exact hQ
    by_cases hr:C₂ R=0
    · rw [hrzero N R hr,norm_zero]; exact hQ
    by_cases hNR:Disjoint N R
    · have hNB:=hFB.mono_left (Finset.mem_powerset.mp hNF)
      have hRB:=hFB.mono_left (Finset.mem_powerset.mp hRF)
      have hNS:Disjoint N S:=hNB.mono_right (Finset.filter_subset _ _)
      have hRS:Disjoint R S:=hRB.mono_right (Finset.filter_subset _ _)
      have hnorm:primeProductNorm p ((N∪R)∪S)=primeProductNorm p N*primeProductNorm p R*primeProductNorm p S:=by
        rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hNS,hRS⟩),primeProductNorm_union p _ _ hNR]
      have hprod:=mul_le_mul (Finset.mem_filter.mp hN).2 (Finset.mem_filter.mp hR).2
        (primeProductNorm_pos p hp R).le hU₁.le
      have hscale:slow≤ K/(‖ringComplex d‖^2*primeProductNorm p ((N∪R)∪S)):=by
        apply div_le_div_of_nonneg_left hK.le (mul_pos hNd (primeProductNorm_pos p hp _))
        rw [hnorm]
        calc
          _ ≤ ‖ringComplex d‖^2*(U₁*U₂*primeProductNorm p S):=mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
          _ = _ := by ring
      have hnroot:1≤‖ringComplex (∏i∈(N∪R)∪S,p i)‖:=by
        have hx:=primeProductNorm_ge_one p hp ((N∪R)∪S)
        change 1≤‖ringComplex (∏i∈(N∪R)∪S,p i)‖^2 at hx
        nlinarith [norm_nonneg (ringComplex (∏i∈(N∪R)∪S,p i))]
      have hpre:(K/‖ringComplex (∏i∈(N∪R)∪S,p i)‖)*(‖C₁ N‖*‖C₂ R‖)≤ G₁*G₂*K:=by
        calc
          _ ≤ K*(G₁*G₂):=mul_le_mul (div_le_self hK.le hnroot)
            (mul_le_mul (hC₁ N hNF) (hC₂ R hRF) (norm_nonneg _) hG₁)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK.le
          _ = _ := by ring
      have hfrac:(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (K/(‖ringComplex d‖^2*primeProductNorm p ((N∪R)∪S))))^2*(1+P)^A)≤ tail:=by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (sq_pos_of_pos (lt_min (by norm_num) hslow)) (pow_pos (by linarith) _))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_min zero_le_one hslow.le)
          (min_le_min_left 1 hscale) 2) (pow_nonneg (by linarith) _)
      have hpair:=hb p hp hinj hg hc N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1)
        X₁ X₂ K P hK hP d hd T (hT N hNF R hRF hNR hn hr)
      simp only [norm_one,one_mul] at hpair
      dsimp only [rem]
      rw [if_pos hNR]
      exact hpair.trans (mul_le_mul hpre hfrac (by positivity) (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le))
    · simp only [rem,if_neg hNR,norm_zero];exact hQ
  rw [heq]
  calc
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,‖rem N R‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun N hN=>norm_sum_le _ _))
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,Q:=
      Finset.sum_le_sum (fun N hN=>Finset.sum_le_sum (fun R hR=>hrem N hN R hR))
    _ = ((boundedPrimeSupports p F U₁).card:ℝ)*((boundedPrimeSupports p F U₂).card:ℝ)*Q:=by simp;ring
    _ ≤ ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*Q:=mul_le_mul_of_nonneg_right
      (mul_le_mul (boundedPrimeSupports_card_positive p hp hinj F U₁ hU₁)
        (boundedPrimeSupports_card_positive p hp hinj F U₂ hU₂) (Nat.cast_nonneg _) (by positivity)) hQ
    _ = _ := by dsimp [Q,tail,slow,U₁,U₂,S];ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem full_first_physical_tail (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,lambda∉Ideal.span {p i})
      (_hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool S common divisor : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      (∀ i∈S,0<v₁ i+v₂ i) → Disjoint pool S →
      ∀ (f : Ideal O),f≠0 → ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (G₁ G₂ Z M r ell V delta B j eta tau : ℝ),0≤ G₁ → 0≤ G₂ → 0<Z →
      (∀ U∈pool.powerset,‖C₁ U‖≤ G₁) → (∀ U∈pool.powerset,‖C₂ U‖≤ G₂) →
      ‖ringComplex (primeProduct p S v₁)‖^2≤ Z^(ell+eta) →
      ‖ringComplex (primeProduct p S v₂)‖^2≤ Z^(ell+eta) →
      (Ideal.absNorm f : ℝ)≤ Z^(V+eta) → primeProductNorm p divisor≤ Z^(delta+eta) →
      Z^(B-eta)≤ primeProductNorm p common →
      Z^(j-eta)≤‖ringComplex (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2 →
      (∀ N∈pool.powerset,C₁ N≠0 →
        ‖ringComplex (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p N≤ Z^(r+eta)) →
      (∀ Q∈pool.powerset,C₂ Q≠0 →
        ‖ringComplex (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p Q≤ Z^(r+eta)) →
      let U₁ := Z^(r+eta)/(‖ringComplex (aLabel p S ε₂)‖^2*primeProductNorm p common)
      let U₂ := Z^(r+eta)/(‖ringComplex (aLabel p S ε₁)‖^2*primeProductNorm p common)
      let active := cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂
      let slow := Z^M/(primeProductNorm p divisor*primeProductNorm p active*U₁*U₂)
      let T := childFrequencyBall (firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f)
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
      ‖∑' h : {h : O // h∉T},actualFirstKernel p hp hg pool S (fun i=>v₁ i+v₂ i) ε₁ ε₂
        C₁ C₂ W (fun _=>1) (fun _=>1) 1 1 (Z^M)
        ((∏ i ∈ divisor,p i)) h.val‖ ≤
      ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁*G₂*Z^M)*
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 slow)^2*(1+Z^tau)^order)) := by
  obtain ⟨s,Ct,hCt,hfull⟩ := full_first_supported_remainder order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hinj hcop hg hchar pool S common divisor v₁ v₂ ε₁ ε₂ hv hpool f hf0
    C₁ C₂ W G₁ G₂ Z M r ell V delta B j eta tau hG₁ hG₂ hZ hC₁ hC₂ hb₁ hb₂ hf hd hc hj hcol₁ hcol₂
    U₁ U₂ active slow T
  have hA (ε : ι→Bool) : 0<‖ringComplex (aLabel p S ε)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  have hU₁ : 0<U₁ := div_pos (Real.rpow_pos_of_pos hZ _)
    (mul_pos (hA ε₂) (primeProductNorm_pos p hp _))
  have hU₂ : 0<U₂ := div_pos (Real.rpow_pos_of_pos hZ _)
    (mul_pos (hA ε₁) (primeProductNorm_pos p hp _))
  have hlog₁ (N : Finset ι) (hN : N∈pool.powerset) (hn : C₁ N≠0) : columnLog p 1 N≤ Real.log U₁ := by
    unfold columnLog
    rw [div_one]
    apply Real.log_le_log (primeProductNorm_pos p hp _)
    apply (le_div_iff₀ (mul_pos (hA ε₂) (primeProductNorm_pos p hp _))).mpr
    simpa only [mul_comm] using hcol₁ N hN hn
  have hlog₂ (N : Finset ι) (hN : N∈pool.powerset) (hn : C₂ N≠0) : columnLog p 1 N≤ Real.log U₂ := by
    unfold columnLog
    rw [div_one]
    apply Real.log_le_log (primeProductNorm_pos p hp _)
    apply (le_div_iff₀ (mul_pos (hA ε₁) (primeProductNorm_pos p hp _))).mpr
    simpa only [mul_comm] using hcol₂ N hN hn
  have hb := hfull p hp hinj hcop hg hchar pool S (fun i=>v₁ i+v₂ i) ε₁ ε₂ hpool C₁ C₂ W
    G₁ G₂ 1 1 (Z^M) (Z^tau) (Real.log U₁) (Real.log U₂) hG₁ hG₂ zero_lt_one zero_lt_one
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _).le hC₁ hC₂ hlog₁ hlog₂
    ((∏ i ∈ divisor,p i)) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) T
    (fun N hN Q hQ hNQ hn hq h hout=>by
      simpa only [primeProductNorm, Finset.union_comm] using
        first_physical_cutoff_raw_tail p hp S Q N v₁ v₂ ε₁ ε₂ hv hNQ.symm
          (hpool.mono_left (Finset.mem_powerset.mp hQ)) (hpool.mono_left (Finset.mem_powerset.mp hN))
          common divisor f hf0 h Z M r ell V delta B j eta tau hZ hb₁ hb₂ hf hd hc hj
          (hcol₂ Q hQ hq) (hcol₁ N hN hn) hout)
  simpa only [Real.exp_log hU₁,Real.exp_log hU₂,one_mul,slow,active,primeProductNorm]
    using hb

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O

variable {ι : Type*} [DecidableEq ι]

theorem cube_whole_column_norm (p : ι→O) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C N : Finset ι) (hC : Disjoint C b.support) (hN : Disjoint N (b.support∪C))
    (negative : Bool) :
    primeProductNorm p (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N) =
      ‖ringComplex (aLabel p b.support (if negative then b.rightBit else b.leftBit))‖^2 *
        primeProductNorm p C * primeProductNorm p N := by
  have hd : (if negative then b.rightDivisor else b.leftDivisor) ⊆ b.support := by
    cases negative
    · exact hb.1
    · exact hb.2
  rw [primeProductNorm_union p _ _ (hN.symm.mono_left (Finset.union_subset_union hd (Finset.Subset.refl C))),
    primeProductNorm_union p _ _ (hC.symm.mono_left hd)]
  congr 2
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [CubeCoordinates.aLabel_left p b hb]; rfl
  · rw [CubeCoordinates.aLabel_right p b hb]; rfl

def wholeMarkedTest {σ : Type*} [DecidableEq σ] (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (test : Finset ι→ℂ) (U : Finset ι) : ℂ :=
  primeMark slots lists a U * test U

theorem whole_marked_test_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ, 0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test : Finset ι→ℂ) (G L : ℝ),0≤ G → 0≤ L →
      (∀ U,‖test U‖≤ G) → (∀ U,test U≠0 → primeProductNorm p U≤ L) →
      ∀ U,‖wholeMarkedTest slots lists a test U‖≤ Cm*L^ε*G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha test G L hG hL hb hs U
  by_cases hz : test U=0
  · simp only [wholeMarkedTest,hz,mul_zero,norm_zero]; positivity
  · have hn0 := (primeProductNorm_pos p hp U).le
    rw [wholeMarkedTest,norm_mul]
    calc
      _ ≤ (Cm*(primeProductNorm p U)^ε)*G :=
        mul_le_mul (hmark p hp hcop slots lists a hslots ha U) (hb U) (norm_nonneg _) (by positivity)
      _ ≤ Cm*L^ε*G := by gcongr; exact hs U hz

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda∉Ideal.span {p i})

theorem canonical_residual_norm (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (hΨ : ∀ u,‖Ψ u‖≤1) (m f : O) (H : Finset ι→ℂ) (N : Finset ι) :
    ‖canonicalCubeResidual p hg b C negative Ψ m f H N‖ ≤
      ‖H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N)‖ := by
  exact originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit negative
    Ψ hΨ m (∏i∈C,p i) f _ N

theorem canonical_residual_test_nonzero (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) (N : Finset ι)
    (hn : canonicalCubeResidual p hg b C negative Ψ m f H N≠0) :
    H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N)≠0 := by
  exact originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit negative
    Ψ m (∏i∈C,p i) f _ N hn

theorem canonical_marked_residual_support {σ : Type*} [DecidableEq σ]
    (b : CubeCoordinates ι) (hb : b.Admissible) (C N : Finset ι)
    (hC : Disjoint C b.support) (hN : Disjoint N (b.support∪C)) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (test : Finset ι→ℂ) (L : ℝ) (hs : ∀ U,test U≠0 → primeProductNorm p U≤ L)
    (hn : canonicalCubeResidual p hg b C negative Ψ m f (wholeMarkedTest slots lists a test) N≠0) :
    ‖ringComplex (aLabel p b.support (if negative then b.rightBit else b.leftBit))‖^2 *
      primeProductNorm p C * primeProductNorm p N≤ L := by
  have ht := canonical_residual_test_nonzero p hg b C negative Ψ m f _ N hn
  have htest := (mul_ne_zero_iff.mp ht).2
  simpa only [cube_whole_column_norm p b hb C N hC hN negative] using hs _ htest

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels JointLogSeparation
open MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O

def firstCoordinates (a : Fin 7 → ℝ) (x y : ℝ) : Fin 9 → ℝ :=
  ![a 0,a 1,a 2,a 3,a 4,a 5,a 6,x,y]

def firstOuterPhase (h : Fin 9 → ℝ) (a : Fin 7 → ℝ) : ℂ :=
  ∏ i : Fin 7, kernelLogPhase (h ⟨i.val, by omega⟩) (a i)

theorem first_mode_split (a : Fin 7 → ℝ) (x y : ℝ)
    (v : Frequency × (Fin 9 → ℝ)) :
    pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstCoordinates a x y) v.1 v.2 =
      firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2) a *
      kernelLogPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2 7) x *
      kernelLogPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2 8) y := by
  rw [pureProfileMode_height]
  simp [Fin.prod_univ_succ,firstCoordinates,firstOuterPhase]
  ring

def firstColumnMode (negative : Bool) {ι : Type*} (C : Finset ι → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * if negative then star (kernelLogPhase t (y S)) else kernelLogPhase t (y S)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem threeGaussRowFactor_first_mode (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (y₁ y₂ : Finset ι → ℝ) (t₁ t₂ : ℝ) (d h : Eis) :
    threeGaussRowFactor p hp hg N P B v ε₁ ε₂
      (firstColumnMode true C₁ y₁ t₁) (firstColumnMode false C₂ y₂ t₂) d h =
    kernelLogPhase t₁ (y₁ N) * kernelLogPhase t₂ (y₂ P) *
      threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  simp only [threeGaussRowFactor,firstColumnMode,Bool.false_eq_true,ite_false,ite_true,
    star_mul,star_star]
  ring

include hcop in
theorem actual_first_mode_ideal_rows
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) :
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
          (firstCoordinates a (y₁ N) (y₂ P)) z.1 z.2 else 0) =
    firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a *
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg F
        (cubeMinusCoefficient p hg B v ε₁ ε₂
          (firstColumnMode true C₁ y₁ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)) d)
        (cubePlusCoefficient p hg B v ε₁ ε₂
          (firstColumnMode false C₂ y₂ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)) d) h := by
  rw [mul_assoc, ← sum_threeGaussRowFactor_eq_ideal_rows p hp hinj hcop hg hc hpr F B hFB]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hd : Disjoint N P
  · simp only [hd,ite_true]
    rw [first_mode_split,threeGaussRowFactor_first_mode]
    ring
  · simp [hd]

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap ContDiff
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels JointLogSeparation
open MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def firstModeIdealRows (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (C₁ C₂ : Finset ι → ℂ) (d h : Eis) (a : Fin 7 → ℝ)
    (y₁ y₂ : Finset ι → ℝ) (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a *
    cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
    idealPairReindex p hg F
      (cubeMinusCoefficient p hg B v ε₁ ε₂
        (firstColumnMode true C₁ y₁ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)) d)
      (cubePlusCoefficient p hg B v ε₁ ε₂
        (firstColumnMode false C₂ y₂ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)) d) h

include hcop in
theorem first_gauss_common_integral
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ) (R : ℝ)
    (g : Fin 9 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R y =
      ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2) :
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h *
        firstPoissonProfile W₁ W₂ Φ V R (firstCoordinates a (y₁ N) (y₂ P)) else 0) =
    ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
      firstModeIdealRows p hp hg F B v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ z := by
  let coeff := fun j : Finset ι × Finset ι => if Disjoint j.1 j.2 then
    threeGaussRowFactor p hp hg j.1 j.2 B v ε₁ ε₂ C₁ C₂ d h else 0
  let coord := fun j : Finset ι × Finset ι => firstCoordinates a (y₁ j.1) (y₂ j.2)
  calc
    _ = ∑ j ∈ F.powerset ×ˢ F.powerset, coeff j *
        ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (coord j) z.1 z.2 := by
      simp only [Finset.sum_product,coeff,coord]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro P hP
      by_cases hd : Disjoint N P <;> simp [hd,he]
    _ = ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
        ∑ j ∈ F.powerset ×ˢ F.powerset, coeff j *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (coord j) z.1 z.2 :=
      full_density_finite_sum _ g b₁ b₂ b₃ _ _ _ coeff coord
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      congr 1
      simp only [Finset.sum_product,coeff,coord,ite_mul,zero_mul]
      exact actual_first_mode_ideal_rows p hp hcop hg hinj hc hpr F B hFB
        v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ z

include hcop in
theorem first_gauss_uniform_common_measure
    (W₁ W₂ : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hs₁ : Function.support W₁ ⊆ Set.Icc lo hi)
    (hs₂ : Function.support W₂ ⊆ Set.Icc lo hi)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ) (M : Fin 9 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ,ℂ)) (C : ℝ), 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b₃ : 𝓢(ℝ,ℂ),
      (∀ (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F B : Finset ι), Disjoint F B → ∀ (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (C₁ C₂ : Finset ι → ℂ) (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ),
        (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
          threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h *
            firstPoissonProfile W₁ W₂ Φ V R (firstCoordinates a (y₁ N) (y₂ P)) else 0) =
        ∫ z : Frequency × (Fin 9 → ℝ),
          fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z *
          firstModeIdealRows p hp hg F B v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ z) ∧
      Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
        tripleHeight J z.1 * coordinateHeight J z.2 *
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z‖) ∧
      (1+R)^A * (∫ z : Frequency × (Fin 9 → ℝ),
        tripleHeight J z.1 * coordinateHeight J z.2 *
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hs⟩ := first_full_profile_common_measure
    W₁ W₂ lo hi hlo hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,he,hI,hB⟩ := hs R hR
  refine ⟨b₃,?_,hI,hB⟩
  intro hinj hc hpr F B hFB v ε₁ ε₂ C₁ C₂ d h a y₁ y₂
  apply first_gauss_common_integral p hp hcop hg hinj hc hpr F B hFB
    v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ W₁ W₂ Φ V R
    (firstRootSchwartz V hV hS) b₁ b₂ b₃
  intro y
  rw [full_density_mode_fubini]
  simpa only [pureProfileMode_height] using he y

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open RayFourExpansion
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp hcop in
omit [DecidableEq σ] in
theorem marked_dilatedCoreRow_eq_input_family
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : Eis) (t : ℝ) (z : Eis) :
    dilatedCoreRow p hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A ∪ U) * H U))
      V y c d t z =
    ∑ r : FirstCoreIndex, firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
      firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (fun U => primeMark slots lists a (A ∪ U) * H U) V y c d r t z :=
  dilatedCoreRow_eq_input_family p hp hcop hg hc hpr F D B v ε₁ ε₂ negative χ Ψ m _ V y c d t z

theorem firstCoreInputRow_marked_priority
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : Eis) (r : FirstCoreIndex) (t : ℝ) (z : Eis) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
      (fun U => primeMark slots lists a (A ∪ U) * H U) V y c d r t z =
    ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ D) *
      firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (fun U => primeMark (slots \ J) (fun i => lists i \ (A ∪ D)) a U * H U)
        V y c d r t z := by
  unfold InverseFirstRayAttachment.firstCoreInputRow inputConjugateRow supportConjugateSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  have he := primeMark_priority slots lists a (A ∪ D) U
  simp only [primeMark_residual_lists] at he
  have hset : (D ∪ U) \ (A ∪ D) = U \ (A ∪ D) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  simp only [secondInputCoefficient, firstCoreTest, ← Finset.union_assoc]
  rw [he]
  simp only [Finset.sum_mul, Finset.mul_sum, ← primeMark_residual_lists, hset]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

theorem firstCoreInputRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : Eis) (r : FirstCoreIndex) (t : ℝ) (z : Eis) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z =
      inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F (firstCoreTwist negative χ Ψ r)
        ((m * b0Label p B v ε₁ ε₂) * ∏ i ∈ D, p i)
        (c * jLabel p B v ε₁ ε₂) d (firstCoreTest H V y negative t D)
        (if negative then -z else z) :=
  inputConjugateRow_fixed_pool p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hinj F D _ _ _ _ _ _

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def firstModeCubeCoefficient (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : Eis) :
    Finset ι → ℂ :=
  if negative then cubeMinusCoefficient p hg B v ε₁ ε₂
    (firstColumnMode true C y t) d
  else cubePlusCoefficient p hg B v ε₁ ε₂
    (firstColumnMode false C y t) d

theorem firstModeCubeCoefficient_eq (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : Eis) :
    firstModeCubeCoefficient p hg B v ε₁ ε₂ negative C y t d =
      cubeLogCoefficient p hg B v ε₁ ε₂ negative C (fun _ => 1) y (-t) d := by
  have ht (u : ℝ) : kernelLogPhase (-t) (-u) = kernelLogPhase t u := by
    unfold kernelLogPhase
    congr 1
    push_cast
    ring
  have hm : firstColumnMode true C y t = logTwistMinus C (fun _ => 1) y (-t) := by
    funext S
    simp only [firstColumnMode,logTwistMinus,ite_true,one_mul,ht]
  have hp' : firstColumnMode false C y t = logTwistPlus C (fun _ => 1) y (-t) := by
    funext S
    simp only [firstColumnMode,logTwistPlus,Bool.false_eq_true,ite_false,one_mul,ht]
  cases negative <;>
    simp only [firstModeCubeCoefficient,cubeLogCoefficient,Bool.false_eq_true,ite_false,ite_true,hm,hp']

include hp hcop in
omit [DecidableEq σ] in
theorem actual_first_mode_marked_input
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (negative : Bool) (χ : RayCharacter)
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : Finset ι → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : Eis) :
    rayIdealRow p hg F
      (firstModeCubeCoefficient p hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A ∪ U)*H U)) c f)
        y t d) negative χ D h =
    beforeDilationLabel p hg p B v ε₁ ε₂ negative c d f D *
      ∑ r : FirstCoreIndex, firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
        firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
          (fun U => primeMark slots lists a (A ∪ U)*H U) (fun _ => 1) y c d r (-t)
          (h*f^2*dilationLabel p B v ε₁ ε₂) := by
  rw [firstModeCubeCoefficient_eq,
    rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv]
  congr 1
  exact marked_dilatedCoreRow_eq_input_family p hp hcop hg hc hpr F D B A v ε₁ ε₂
    negative χ Ψ m slots lists a H (fun _ => 1) y c d (-t) _

include hp hcop in
theorem actual_first_mode_priority_input
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (negative : Bool) (χ : RayCharacter)
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : Finset ι → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : Eis) :
    rayIdealRow p hg F
      (firstModeCubeCoefficient p hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A ∪ U)*H U)) c f)
        y t d) negative χ D h =
    beforeDilationLabel p hg p B v ε₁ ε₂ negative c d f D *
      ∑ r : FirstCoreIndex, firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
        ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ D) *
          firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
            (fun U => primeMark (slots \ J) (fun i => lists i \ (A ∪ D)) a U*H U)
            (fun _ => 1) y c d r (-t) (h*f^2*dilationLabel p B v ε₁ ε₂) := by
  rw [actual_first_mode_marked_input p hp hcop hg hinj hc hpr F D B A v ε₁ ε₂ hv]
  simp_rw [firstCoreInputRow_marked_priority]

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation Eisenstein FirstPassCubeLabels
open RayFourExpansion (RayCharacter)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
theorem full_rayIdealRow_continuous {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hC : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) :
    Continuous (fun t => rayIdealRow p hg F (C t) negative χ D h) := by
  simp only [rayIdealRow, supportConjugateSum]
  fun_prop

theorem full_rayIdealRow_uniform_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hC : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖rayIdealRow p hg F (C t) negative χ D h‖ ≤ M := by
  let T := fun (t : Frequency × (Fin 9 → ℝ)) (U : Finset ι) =>
    supportMobius U * ((if negative then star (supportRay p χ U) else supportRay p χ U) *
      C t (D ∪ U)) * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U h)
  refine ⟨∑ U ∈ (F \ D).powerset, ‖T 0 U‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro t
  change ‖∑ U ∈ (F \ D).powerset, T t U‖ ≤ _
  apply (norm_sum_le _ (T t)).trans_eq
  apply Finset.sum_congr rfl
  intro U hU
  simp only [T, norm_mul, hC]

theorem full_rayIdealEnergy_continuous {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hC : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (h : O) :
    Continuous (fun t => rayIdealEnergy p hg F (C t) negative h) := by
  unfold rayIdealEnergy
  apply continuous_finsetSum _
  intro r hr
  apply continuous_finsetSum _
  intro D hD
  exact continuous_const.mul ((full_rayIdealRow_continuous p hg F C hC negative _ D h).norm.pow 2)

theorem full_rayIdealEnergy_uniform_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hC : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, rayIdealEnergy p hg F (C t) negative h ≤ M := by
  choose M hM hbound using fun (r : RayCharacter × RayCharacter) (D : Finset ι) =>
    full_rayIdealRow_uniform_bound p hg F C hC negative (if negative then r.1 else r.2) D h
  refine ⟨∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖rayPairWeight p r D h‖ * (M r D)^2, by positivity, ?_⟩
  intro t
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound r D t) 2)
    (norm_nonneg _)

theorem full_integrable_rayIdealEnergy {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => C t S))
    (hn : ∀ t S, ‖C t S‖ = ‖C 0 S‖) (negative : Bool) (h : O) (b : (Frequency × (Fin 9 → ℝ)) → ℂ) (hb : Integrable b) :
    Integrable (fun t : Frequency × (Fin 9 → ℝ) => ‖b t‖ * rayIdealEnergy p hg F (C t) negative h) volume := by
  obtain ⟨M, hM, hbnd⟩ := full_rayIdealEnergy_uniform_bound p hg F C hn negative h
  apply hb.norm.mul_bdd (c := M)
  · exact (full_rayIdealEnergy_continuous p hg F C hc negative h).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (rayIdealEnergy_nonneg p hg F (C t) negative h)]
      exact hbnd t)

theorem full_cube_integral_norm_le_energy {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F : Finset ι)
    (C₁ C₂ : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ)
    (hc₁ : ∀ S, Continuous (fun t => C₁ t S))
    (hc₂ : ∀ S, Continuous (fun t => C₂ t S))
    (hn₁ : ∀ t S, ‖C₁ t S‖ = ‖C₁ 0 S‖)
    (hn₂ : ∀ t S, ‖C₂ t S‖ = ‖C₂ 0 S‖)
    (h : O) (b : (Frequency × (Fin 9 → ℝ)) → ℂ)
    (hb : Integrable b) (hbc : Continuous b) (a : ℂ) :
    ‖∫ t : Frequency × (Fin 9 → ℝ), b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₁ t) true h) *
      Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₂ t) false h) := by
  let E₁ := fun t => rayIdealEnergy p hg F (C₁ t) true h
  let E₂ := fun t => rayIdealEnergy p hg F (C₂ t) false h
  let w := fun t : Frequency × (Fin 9 → ℝ) => ‖b t‖ * ‖a‖
  have hE₁ : ∀ t, 0 ≤ E₁ t := fun t => rayIdealEnergy_nonneg p hg F (C₁ t) true h
  have hE₂ : ∀ t, 0 ≤ E₂ t := fun t => rayIdealEnergy_nonneg p hg F (C₂ t) false h
  have hw : ∀ t, 0 ≤ w t := fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have i₁ : Integrable (fun t => w t * E₁ t) volume := by
    convert (full_integrable_rayIdealEnergy p hg F C₁ hc₁ hn₁ true h b hb).mul_const ‖a‖ using 1 <;> first | rfl | (funext t; dsimp only [w, E₁]; ring)
  have i₂ : Integrable (fun t => w t * E₂ t) volume := by
    convert (full_integrable_rayIdealEnergy p hg F C₂ hc₂ hn₂ false h b hb).mul_const ‖a‖ using 1 <;> first | rfl | (funext t; dsimp only [w, E₂]; ring)
  let f := fun t => Real.sqrt (w t * E₁ t)
  let g := fun t => Real.sqrt (w t * E₂ t)
  have hf : Continuous f :=
    Real.continuous_sqrt.comp (((hbc.norm.mul_const ‖a‖).mul
      (full_rayIdealEnergy_continuous p hg F C₁ hc₁ true h)))
  have hg' : Continuous g :=
    Real.continuous_sqrt.comp (((hbc.norm.mul_const ‖a‖).mul
      (full_rayIdealEnergy_continuous p hg F C₂ hc₂ false h)))
  have hfsq (t : Frequency × (Fin 9 → ℝ)) : f t ^ 2 = w t * E₁ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₁ t))
  have hgsq (t : Frequency × (Fin 9 → ℝ)) : g t ^ 2 = w t * E₂ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₂ t))
  have mf : MemLp f 2 volume := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (by simpa only [hfsq] using i₁)
  have mg : MemLp g 2 volume := (memLp_two_iff_integrable_sq hg'.aestronglyMeasurable).mpr
    (by simpa only [hgsq] using i₂)
  have hfg (t : Frequency × (Fin 9 → ℝ)) : f t * g t = w t * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by
    dsimp only [f, g]
    rw [Real.sqrt_mul (hw t), Real.sqrt_mul (hw t)]
    calc
      _ = (Real.sqrt (w t))^2 * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw t)]
  have hnorm : ‖∫ t : Frequency × (Fin 9 → ℝ), b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      ∫ t : Frequency × (Fin 9 → ℝ), f t * g t := by
    apply norm_integral_le_of_norm_le (mf.integrable_mul mg)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Pi.mul_apply]
      rw [hfg, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (idealPairReindex_norm_le p hg F (C₁ t) (C₂ t) h) (hw t))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₁ t)))
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₂ t)))
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) volume by simpa using mf)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) volume by simpa using mg)
  have hfinal : (∫ t : Frequency × (Fin 9 → ℝ), f t * g t) ≤
      Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), w t * E₁ t) * Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), w t * E₂ t) := by
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
    change (∫ t : Frequency × (Fin 9 → ℝ), f t * g t) ≤
      Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), f t ^ 2) * Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), g t ^ 2) at hh
    simpa only [hfsq, hgsq] using hh
  exact hnorm.trans hfinal

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation Eisenstein FirstPassCubeLabels
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def firstModeEnergyCoefficient (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (d : Eis)
    (z : Frequency × (Fin 9 → ℝ)) : Finset ι → ℂ :=
  firstModeCubeCoefficient p hg B v ε₁ ε₂ negative C y
    (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 (if negative then 7 else 8)) d

theorem firstModeEnergyCoefficient_continuous (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (d : Eis) (S : Finset ι) :
    Continuous (fun z => firstModeEnergyCoefficient p hg B v ε₁ ε₂ negative C y d z S) := by
  simp only [firstModeEnergyCoefficient,firstModeCubeCoefficient_eq]
  apply (cubeLogCoefficient_continuous p hg B v ε₁ ε₂ negative C (fun _ => 1) y d S).comp
  unfold profileHeight
  fun_prop

theorem firstModeEnergyCoefficient_norm (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (d : Eis)
    (z : Frequency × (Fin 9 → ℝ)) (S : Finset ι) :
    ‖firstModeEnergyCoefficient p hg B v ε₁ ε₂ negative C y d z S‖ =
      ‖firstModeEnergyCoefficient p hg B v ε₁ ε₂ negative C y d 0 S‖ := by
  simp only [firstModeEnergyCoefficient,firstModeCubeCoefficient_eq]
  exact (cubeLogCoefficient_norm_time p hg B v ε₁ ε₂ negative C (fun _ => 1) y _ d S).trans
    (cubeLogCoefficient_norm_time p hg B v ε₁ ε₂ negative C (fun _ => 1) y _ d S).symm

theorem firstOuterPhase_norm (h : Fin 9 → ℝ) (a : Fin 7 → ℝ) :
    ‖firstOuterPhase h a‖ = 1 := by
  simp [firstOuterPhase,norm_prod,kernelLogPhase_norm]

theorem actual_first_common_energy (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ)
    (g : Fin 9 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
      firstModeIdealRows p hp hg F B v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ z‖ ≤
    Real.sqrt (∫ z : Frequency × (Fin 9 → ℝ), ‖fullProfileDensity g b₁ b₂ b₃ z‖ *
      ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
      rayIdealEnergy p hg F (firstModeEnergyCoefficient p hg B v ε₁ ε₂ true C₁ y₁ d z) true h) *
    Real.sqrt (∫ z : Frequency × (Fin 9 → ℝ), ‖fullProfileDensity g b₁ b₂ b₃ z‖ *
      ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
      rayIdealEnergy p hg F (firstModeEnergyCoefficient p hg B v ε₁ ε₂ false C₂ y₂ d z) false h) := by
  let b := fun z : Frequency × (Fin 9 → ℝ) => fullProfileDensity g b₁ b₂ b₃ z *
    firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a
  have hphase : Continuous (fun z : Frequency × (Fin 9 → ℝ) =>
      firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a) := by
    unfold firstOuterPhase profileHeight kernelLogPhase
    fun_prop
  have hb : Integrable b := (full_density_integrable g b₁ b₂ b₃).mul_bdd
    hphase.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => (firstOuterPhase_norm _ _).le))
  have hbc : Continuous b := by
    apply Continuous.mul _ hphase
    unfold fullProfileDensity coordinateDensity tripleCoefficient
    fun_prop
  have hbn (z : Frequency × (Fin 9 → ℝ)) : ‖b z‖ = ‖fullProfileDensity g b₁ b₂ b₃ z‖ := by
    simp only [b,norm_mul,firstOuterPhase_norm,mul_one]
  have hh := full_cube_integral_norm_le_energy p hg F
    (firstModeEnergyCoefficient p hg B v ε₁ ε₂ true C₁ y₁ d)
    (firstModeEnergyCoefficient p hg B v ε₁ ε₂ false C₂ y₂ d)
    (firstModeEnergyCoefficient_continuous p hg B v ε₁ ε₂ true C₁ y₁ d)
    (firstModeEnergyCoefficient_continuous p hg B v ε₁ ε₂ false C₂ y₂ d)
    (firstModeEnergyCoefficient_norm p hg B v ε₁ ε₂ true C₁ y₁ d)
    (firstModeEnergyCoefficient_norm p hg B v ε₁ ε₂ false C₂ y₂ d)
    h b hb hbc (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  simp only [hbn] at hh
  convert hh using 1
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  simp only [firstModeIdealRows,firstModeEnergyCoefficient,firstModeCubeCoefficient,
    Bool.false_eq_true,ite_false,ite_true,b]
  ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels CoprimeMobiusExtension
open RayFourExpansion
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O

theorem first_coprime_coupled_reindex {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (C₁ C₂ : Finset ι → ℂ) (H : Finset ι → Finset ι → ℂ) (h : Eis) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then
      H S T * star (supportMobius S * C₁ S * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S h)) *
        (supportMobius T * C₂ T * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T h)) else 0) =
    ∑ D ∈ B.powerset, supportMobius D * primeCoprimeMask p D h *
      ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
        H (D ∪ U) (D ∪ V) *
          star (supportMobius U * C₁ (D ∪ U) * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U h)) *
            (supportMobius V * C₂ (D ∪ V) * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V h)) := by
  rw [double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro D hD
  change supportMobius D * _ = _
  rw [mul_assoc]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  have hdV : Disjoint D V := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right
  have he := supportPairTerm_union p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) C₁ C₂ h D U V hdU hdV
  calc
    _ = H (D ∪ U) (D ∪ V) * supportPairTerm p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) C₁ C₂ h (D ∪ U) (D ∪ V) := by unfold supportPairTerm; ring
    _ = _ := by rw [he]; unfold supportPairTerm; ring

theorem first_quadratic_coupled_reindex {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (B : Finset ι)
    (C₁ C₂ : Finset ι → ℂ) (H : Finset ι → Finset ι → ℂ) (h : Eis) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then
      H S T * quadraticCrossPhase p hg S T *
        star (supportMobius S * C₁ S * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S h)) *
        (supportMobius T * C₂ T * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T h)) else 0) =
    ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset, supportMobius D * primeCoprimeMask p D h *
        ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
          H (D ∪ U) (D ∪ V) *
          star (supportMobius U *
            (star (supportRay p r.1 (D ∪ U))*C₁ (D ∪ U)) * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U h)) *
          (supportMobius V *
            (supportRay p r.2 (D ∪ V)*C₂ (D ∪ V)) * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V h)) := by
  let P := fun i => Ideal.span {p i}
  have hcop : Pairwise (Function.onFun IsCoprime P) := by
    intro i j hij
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hij)
  have hprime (i : ι) : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  let T := fun (r : RayCharacter × RayCharacter) (S V : Finset ι) => if Disjoint S V then
    H S V * star (supportMobius S * (star (supportRay p r.1 S)*C₁ S) * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S h)) *
      (supportMobius V * (supportRay p r.2 V*C₂ V) * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V h)) else 0
  have he (S V : Finset ι) :
      (if Disjoint S V then H S V * quadraticCrossPhase p hg S V *
        star (supportMobius S*C₁ S*star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S h)) *
          (supportMobius V*C₂ V*star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V h)) else 0) =
      ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2*T r S V := by
    by_cases hd : Disjoint S V
    · rw [if_pos hd,quadraticCrossPhase_eq_ray p hp hinj hg hc S V hd, cross_phase_expansion _ _ (prime_product_unit_mod_four p hc S) (prime_product_unit_mod_four p hc V)]
      simp only [Fintype.sum_prod_type,T,if_pos hd,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro η hη
      simp only [supportRay,star_mul,star_star]
      ring
    · simp [T,hd]
  calc
    _ = ∑ S ∈ B.powerset, ∑ V ∈ B.powerset,
        ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2*T r S V := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun V hV => he S V)
    _ = ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
        ∑ S ∈ B.powerset, ∑ V ∈ B.powerset, T r S V := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ r : RayCharacter × RayCharacter,
            ∑ V ∈ B.powerset, crossCoeff r.1 r.2*T r S V := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      exact first_coprime_coupled_reindex p hg B _ _ H h

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O

theorem firstNormProfile_common_support (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C D R T H X₁ X₂ K : ℝ) (hT : 0 ≤ T) :
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K ![A₁,A₂,C,D,R,1,H,T*X₁,T*X₂] =
      firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K ![A₁,A₂,C,D,R,T,H,X₁,X₂] := by
  have hroot : Real.sqrt (T*X₁)*Real.sqrt (T*X₂) =
      T*Real.sqrt X₁*Real.sqrt X₂ := by
    rw [Real.sqrt_mul hT,Real.sqrt_mul hT]
    calc
      _ = (Real.sqrt T)^2*Real.sqrt X₁*Real.sqrt X₂ := by ring
      _ = _ := by rw [Real.sq_sqrt hT]
  unfold firstNormProfile
  simp only [Finset.prod_const_one,one_mul,Matrix.cons_val_zero,
    Fin.isValue,]
  change W₁ (A₁*C*1*(T*X₁))*W₂ (A₂*C*1*(T*X₂))*
      SchwartzPlanePoisson.paperRadialFourier Φ (K*H/(D*R*1^2*(T*X₁)*(T*X₂))) /
        ((D:ℂ)*(Real.sqrt R:ℂ)*(1:ℂ)*(Real.sqrt (T*X₁):ℂ)*(Real.sqrt (T*X₂):ℂ)) =
    W₁ (A₁*C*T*X₁)*W₂ (A₂*C*T*X₂)*
      SchwartzPlanePoisson.paperRadialFourier Φ (K*H/(D*R*T^2*X₁*X₂)) /
        ((D:ℂ)*(Real.sqrt R:ℂ)*(T:ℂ)*(Real.sqrt X₁:ℂ)*(Real.sqrt X₂:ℂ))
  simp only [mul_one,one_pow]
  rw [show A₁*C*(T*X₁) = A₁*C*T*X₁ from by ring,
    show A₂*C*(T*X₂) = A₂*C*T*X₂ from by ring,
    show K*H/(D*R*(T*X₁)*(T*X₂)) = K*H/(D*R*T^2*X₁*X₂) from by ring]
  have hc : (Real.sqrt (T*X₁):ℂ)*(Real.sqrt (T*X₂):ℂ) =
      (T:ℂ)*(Real.sqrt X₁:ℂ)*(Real.sqrt X₂:ℂ) := by exact_mod_cast hroot
  rw [show (D:ℂ)*(Real.sqrt R:ℂ)*(Real.sqrt (T*X₁):ℂ)*(Real.sqrt (T*X₂):ℂ) =
    (D:ℂ)*(Real.sqrt R:ℂ)*((Real.sqrt (T*X₁):ℂ)*(Real.sqrt (T*X₂):ℂ)) from by ring,hc]
  ring

theorem firstNormProfile_actual_common {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) (D U V : Finset ι)
    (hDU : Disjoint D U) (hDV : Disjoint D V)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C E R H K : ℝ) :
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
      ![A₁,A₂,C,E,R,1,H,primeProductNorm p (D∪U),primeProductNorm p (D∪V)] =
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
      ![A₁,A₂,C,E,R,primeProductNorm p D,H,primeProductNorm p U,primeProductNorm p V] := by
  rw [primeProductNorm_union p D U hDU,primeProductNorm_union p D V hDV]
  exact firstNormProfile_common_support W₁ W₂ Φ A₁ A₂ C E R _ H _ _ K
    (primeProductNorm_pos p hp D).le

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def firstCoupledRayColumns (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (H : Finset ι → Finset ι → ℂ) (h : Eis) : ℂ :=
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, supportMobius D * primeCoprimeMask p D h *
      ∑ U ∈ (F \ D).powerset, ∑ V ∈ (F \ D).powerset,
        H (D ∪ U) (D ∪ V) *
        star (supportMobius U *
          (star (supportRay p r.1 (D ∪ U))*C₁ (D ∪ U)) * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U h)) *
        (supportMobius V *
          (supportRay p r.2 (D ∪ V)*C₂ (D ∪ V)) * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V h))

include hcop in
theorem actual_first_gauss_coupled_reindex
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (H : Finset ι → Finset ι → ℂ) (d h : Eis) :
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      H N P * threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      firstCoupledRayColumns p hg F
        (cubeMinusCoefficient p hg B v ε₁ ε₂ C₁ d)
        (cubePlusCoefficient p hg B v ε₁ ε₂ C₂ d) H h := by
  rw [firstCoupledRayColumns, ← first_quadratic_coupled_reindex p hp hinj hg hc]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hd : Disjoint N P
  · simp only [hd,ite_true]
    rw [threeGaussRowFactor_eq_ray_columns p hp hinj hcop hg hc hpr N P B hd
      (hFB.mono_left (Finset.mem_powerset.mp hN)) (hFB.mono_left (Finset.mem_powerset.mp hP))]
    rw [←quadraticCrossPhase_eq_ray p hp hinj hg hc N P hd]
    unfold supportPairTerm
    ring
  · simp [hd]

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def firstCommonCoefficient (C₁ C₂ : Finset ι → ℂ)
    (r : RayCharacter × RayCharacter) (D U V : Finset ι) (h : Eis) : ℂ :=
  star (supportMobius U *
    (star (supportRay p r.1 (D ∪ U))*C₁ (D ∪ U)) *
      star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U h)) *
  (supportMobius V *
    (supportRay p r.2 (D ∪ V)*C₂ (D ∪ V)) *
      star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V h))

def firstPhysicalCommonRows (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : Eis) : ℂ :=
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, supportMobius D *
      primeCoprimeMask p D h *
      ∑ U ∈ (F \ D).powerset, ∑ V ∈ (F \ D).powerset,
        firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
          ![A₁,A₂,C,‖ringComplex d‖^2,R,primeProductNorm p D,
            ‖ringComplex h‖^2,primeProductNorm p U,primeProductNorm p V] *
          firstCommonCoefficient p hg C₁ C₂ r D U V h

include hcop in
theorem actual_first_physical_common
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C K : ℝ) (d h : Eis) :
    (‖ringComplex d‖^2 : ℂ)⁻¹ *
      (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        canonicalPairMode p hp hg N P B v ε₁ ε₂ C₁ C₂ Φ
          (fun y => W₁ (A₁*C*Real.exp y)) (fun y => W₂ (A₂*C*Real.exp y)) 1 1 K d h else 0) =
    (K:ℂ) * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      firstPhysicalCommonRows p hg F
        (cubeMinusCoefficient p hg B v ε₁ ε₂ C₁ d)
        (cubePlusCoefficient p hg B v ε₁ ε₂ C₂ d)
        W₁ W₂ Φ A₁ A₂ C (primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)) K d h := by
  let R := primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)
  let H := fun N P : Finset ι => firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
    ![A₁,A₂,C,‖ringComplex d‖^2,R,1,‖ringComplex h‖^2,primeProductNorm p N,primeProductNorm p P]
  calc
    _ = (K:ℂ) * (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        H N P*threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro P hP
      by_cases hd : Disjoint N P
      · simp only [hd,ite_true]
        simpa only [H,R,mul_assoc] using canonicalPairMode_whole_profile p hp hcop hg
          N P B hd (hFB.mono_left (Finset.mem_powerset.mp hN))
          (hFB.mono_left (Finset.mem_powerset.mp hP)) v ε₁ ε₂ C₁ C₂ W₁ W₂ Φ A₁ A₂ C K d h
      · simp [hd]
    _ = _ := by
      rw [actual_first_gauss_coupled_reindex p hp hcop hg hinj hc hpr F B hFB]
      rw [mul_assoc]
      apply congrArg (fun z : ℂ => (K:ℂ)*(cubeBaseFactor p hp hg B v ε₁ ε₂ d h*z))
      unfold firstCoupledRayColumns firstPhysicalCommonRows
      apply Finset.sum_congr rfl
      intro r hr
      apply congrArg (fun z : ℂ => crossCoeff r.1 r.2*z)
      apply Finset.sum_congr rfl
      intro D hD
      apply congrArg (fun z : ℂ => supportMobius D *
        primeCoprimeMask p D h*z)
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      have hDU : Disjoint D U := Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
      have hDV : Disjoint D V := Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right
      dsimp only [H]
      rw [firstNormProfile_actual_common p hp D U V hDU hDV]
      simp only [firstCommonCoefficient,R,mul_assoc]

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

theorem canonical_residual_mul_test (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H test : Finset ι→ℂ) (N : Finset ι) :
    canonicalCubeResidual p hg b C negative Ψ m f (fun U=>H U*test U) N =
      canonicalCubeResidual p hg b C negative Ψ m f H N *
        test (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N) := by
  simp only [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn]
  ring

theorem actual_first_kernel_window_transport
    (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ A₁ A₂ : Finset ι→ℂ) (V₁ V₂ : ℝ→ℂ)
    (hC₁ : ∀ N∈F.powerset,C₁ N=A₁ N*star (V₁ (columnLog p 1 N)))
    (hC₂ : ∀ N∈F.powerset,C₂ N=A₂ N*V₂ (columnLog p 1 N))
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (d h : O) :
    actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) 1 1 K d h =
    ∑ N∈F.powerset,∑ Q∈F.powerset,if Disjoint N Q then
      canonicalPairMode p hp hg N Q B v ε₁ ε₂ A₁ A₂ W V₁ V₂ 1 1 K d h else 0 := by
  unfold actualFirstKernel
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro Q hQ
  by_cases hd : Disjoint N Q
  · simp only [hd,ite_true,canonicalPairMode,threeGaussRowFactor,hC₁ N hN,hC₂ Q hQ,star_mul,star_star]
    ring
  · simp only [hd,ite_false]

include hcop in
theorem canonical_first_kernel_physical
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (d h : O) :
    let F := pool\(b.support∪C)
    let A₁ := ‖ringComplex (aLabel p b.support b.rightBit)‖^2
    let A₂ := ‖ringComplex (aLabel p b.support b.leftBit)‖^2
    let B₁ := canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁
    let B₂ := canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂
    (‖ringComplex d‖^2:ℂ)⁻¹ * actualFirstKernel p hp hg F b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun U=>H₁ U*W₁ (primeProductNorm p U)))
      (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun U=>H₂ U*W₂ (primeProductNorm p U)))
      Φ (fun _=>1) (fun _=>1) 1 1 K d h =
    (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d h *
      firstPhysicalCommonRows p hg F
        (cubeMinusCoefficient p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit B₁ d)
        (cubePlusCoefficient p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit B₂ d)
        (fun x=>star (W₁ x)) W₂ Φ A₁ A₂ (primeProductNorm p C)
        (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d h := by
  intro F A₁ A₂ B₁ B₂
  have hdis : Disjoint F (b.support∪C) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi2
    exact (Finset.mem_sdiff.mp hi).2 hi2
  have hwindow (negative : Bool) (Ψ : O→*ℂ) (m : O) (H : Finset ι→ℂ) (W : ℝ→ℂ)
      (N : Finset ι) (hN : N∈F.powerset) :
      canonicalCubeResidual p hg b C negative Ψ m f (fun U=>H U*W (primeProductNorm p U)) N =
      canonicalCubeResidual p hg b C negative Ψ m f H N *
        W (‖ringComplex (aLabel p b.support (if negative then b.rightBit else b.leftBit))‖^2 *
          primeProductNorm p C*Real.exp (columnLog p 1 N)) := by
    rw [canonical_residual_mul_test p hg, cube_whole_column_norm p b hb C N hC
      (hdis.mono_left (Finset.mem_powerset.mp hN)) negative]
    simp only [columnLog,div_one,Real.exp_log (primeProductNorm_pos p hp N)]
  rw [actual_first_kernel_window_transport p hp hg F b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit _ _ B₁ B₂
    (fun y=>star (W₁ (A₁*primeProductNorm p C*Real.exp y)))
    (fun y=>W₂ (A₂*primeProductNorm p C*Real.exp y))
    (fun N hN=>by simpa only [star_star,ite_true,A₁,B₁] using hwindow true Ψ₁ m₁ H₁ W₁ N hN)
    (fun N hN=>by simpa only [Bool.false_eq_true,ite_false,A₂,B₂] using hwindow false Ψ₂ m₂ H₂ W₂ N hN)]
  exact actual_first_physical_common p hp hcop hg hinj hc hpr F b.support
    (hdis.mono_right Finset.subset_union_left) _ _ _ B₁ B₂
    (fun x=>star (W₁ x)) W₂ Φ A₁ A₂ (primeProductNorm p C) K d h

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

def firstCubePhysicalMode (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (d h : O) : ℂ :=
  (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d h *
    firstPhysicalCommonRows p hg (pool\(b.support∪C))
      (cubeMinusCoefficient p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁) d)
      (cubePlusCoefficient p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂) d)
      (fun x=>star (W₁ x)) W₂ Φ
      (‖ringComplex (aLabel p b.support b.rightBit)‖^2)
      (‖ringComplex (aLabel p b.support b.leftBit)‖^2)
      (primeProductNorm p C)
      (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d h

include hcop in
theorem canonical_retained_physical
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (T : Finset ι→Finset O) :
    canonicalCubeDualFinite p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun U=>H₁ U*W₁ (primeProductNorm p U)) (fun U=>H₂ U*W₂ (primeProductNorm p U)) Φ K T =
    canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ f *
      ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        supportMobius D*
        ∑ h∈(T D).erase 0,firstCubePhysicalMode p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂
          W₁ W₂ Φ K ((∏ i ∈ D,p i)) h := by
  unfold canonicalCubeDualFinite
  apply congrArg
  apply Finset.sum_congr rfl
  intro D hD
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have he := canonical_first_kernel_physical p hp hcop hg hinj hc hpr pool b hb C hC
    Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W₁ W₂ Φ K ((∏ i ∈ D,p i)) h
  change (‖ringComplex ((∏ i ∈ D,p i))‖^2:ℂ)⁻¹ * _ =
    firstCubePhysicalMode p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W₁ W₂ Φ K _ h at he
  rw [←Complex.ofReal_pow] at he
  change (primeProductNorm p D : ℂ)⁻¹ * _ =
    firstCubePhysicalMode p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W₁ W₂ Φ K _ h at he
  rw [div_eq_mul_inv,mul_assoc,he]

include hcop in
theorem canonical_first_physical_split
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ : O) (f : Ideal O) (hf : f≠0) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (R : Finset ι→ℝ)
    (hR : ∀ D,0≤ R D) :
    let fgen := cubicIdealGenerator f
    let H₁' := fun U=>H₁ U*W₁ (primeProductNorm p U)
    let H₂' := fun U=>H₂ U*W₂ (primeProductNorm p U)
    let T := fun D=>childFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R D)
    canonicalCubeBeforePoisson p hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K =
      canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K +
      (canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ fgen *
        ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          supportMobius D*
          ∑ h∈(T D).erase 0,firstCubePhysicalMode p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁ H₂
            W₁ W₂ Φ K ((∏ i ∈ D,p i)) h) +
      canonicalCubeDualTail p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K T := by
  intro fgen H₁' H₂' T
  rw [canonicalCubeBeforePoisson_split p hp hg hinj hc pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K hK T]
  · rw [canonical_retained_physical p hp hcop hg hinj hc hpr pool b hb C hC]
  · intro D hD
    apply (mem_childFrequencyBall _ (firstPhysicalMultiplier_ne_zero p hp _ _ _ _ _ f hf) _ _).mpr
    simpa only [mul_zero,map_zero,norm_zero,zero_pow (by decide : 2≠0)] using hR D

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory JointLogSeparation
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment

def firstRelativeLog (q s : Fin 9 → ℝ) (i : Fin 9) : ℝ := Real.log (q i/s i)

theorem first_fresh_kernel_common_measure
    (W₁ W₂ : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hs₁ : Function.support W₁ ⊆ Set.Icc lo hi) (hs₂ : Function.support W₂ ⊆ Set.Icc lo hi)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ) (M : Fin 9 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ,ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ s : Fin 9 → ℝ, (∀ i, 0 < s i) → ∀ K : ℝ, 0 < K → ∃ b₃ : 𝓢(ℝ,ℂ),
      (∀ (omega₁ omega₂ : ℝ → ℂ) (q : Fin 9 → ℝ), (∀ i, 0 < q i) →
        (W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) ≠ 0 → omega₁ (q 7/s 7) = 1) →
        (W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) ≠ 0 → omega₂ (q 8/s 8) = 1) →
        (omega₁ (q 7/s 7) ≠ 0 → omega₂ (q 8/s 8) ≠ 0 → ∀ i, V i (firstRelativeLog q s i) = 1) →
        firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
          (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
        (firstRootScale s:ℂ)⁻¹ * (omega₁ (q 7/s 7)*omega₂ (q 8/s 8)) *
          ∫ z : Frequency × (Fin 9 → ℝ),
            fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z *
            pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2) ∧
      Integrable (fun z : Frequency × (Fin 9 → ℝ) => tripleHeight J z.1*coordinateHeight J z.2*
        ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z‖) ∧
      (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^A *
        (∫ z : Frequency × (Fin 9 → ℝ), tripleHeight J z.1*coordinateHeight J z.2*
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hs⟩ := first_full_profile_common_measure
    W₁ W₂ lo hi hlo hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro s hspos K hK
  obtain ⟨b₃,he,hI,hB⟩ := hs (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))
    (div_pos (mul_pos hK (hspos 6))
      (mul_pos (mul_pos (mul_pos (mul_pos (hspos 3) (hspos 4))
        (sq_pos_of_pos (hspos 5))) (hspos 7)) (hspos 8)))
  refine ⟨b₃,?_,hI,hB⟩
  intro omega₁ omega₂ q hq homega₁ homega₂ hcut
  by_cases hw₁ : omega₁ (q 7/s 7) = 0
  · have hh : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) = 0 := by
      by_contra hn
      have := homega₁ hn
      simp only [hw₁,zero_ne_one] at this
    simp only [firstNormProfile,hh,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : omega₂ (q 8/s 8) = 0
  · have hh : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) = 0 := by
      by_contra hn
      have := homega₂ hn
      simp only [hw₂,zero_ne_one] at this
    simp only [firstNormProfile,hh,hw₂,mul_zero,zero_mul,zero_div]
  have hcut' := hcut hw₁ hw₂
  have hnom := firstNormProfile_nominal W₁ W₂ Φ (fun _ _ => 1) s q hspos hq K
  have hfull : firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
      (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) =
      ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2 := by
    rw [full_density_mode_fubini]
    rw [show firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) =
        firstPoissonProfile W₁ W₂ Φ V (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (firstRelativeLog q s) from by
      unfold firstRelativeLog
      rw [firstPoissonProfile_log W₁ W₂ Φ V _ _ (fun i => div_pos (hq i) (hspos i))]
      simp only [firstRelativeLog] at hcut'
      simp only [firstNormProfile,hcut',Finset.prod_const_one]]
    simpa only [pureProfileMode_height] using he (firstRelativeLog q s)
  have hm : firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
      (omega₁ (q 7/s 7)*omega₂ (q 8/s 8)) *
      firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
        (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q := by
    by_cases h1 : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) = 0
    · simp only [firstNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) = 0
    · simp only [firstNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [homega₁ h1,homega₂ h2,one_mul]
  rw [hm,hnom,hfull]
  ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open JointLogSeparation MeasureTheory
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O

abbrev FirstCommonIndex (ι : Type*) :=
  (RayCharacter × RayCharacter) × (Σ _ : Finset ι, Finset ι × Finset ι)

def firstCommonIndices {ι : Type*} [DecidableEq ι] (F : Finset ι) : Finset (FirstCommonIndex ι) :=
  Finset.univ ×ˢ F.powerset.sigma (fun D => (F\D).powerset ×ˢ (F\D).powerset)

def firstCommonNorms {ι : Type*} (p : ι → Eis) (A₁ A₂ C R : ℝ) (d h : Eis)
    (j : FirstCommonIndex ι) : Fin 9 → ℝ :=
  ![A₁,A₂,C,‖ringComplex d‖^2,R,primeProductNorm p j.2.1,
    ‖ringComplex h‖^2,primeProductNorm p j.2.2.1,primeProductNorm p j.2.2.2]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def firstCommonWeight (C₁ C₂ : Finset ι → ℂ) (h : Eis) (j : FirstCommonIndex ι) : ℂ :=
  crossCoeff j.1.1 j.1.2 * supportMobius j.2.1 *
    primeCoprimeMask p j.2.1 h *
    firstCommonCoefficient p hg C₁ C₂ j.1 j.2.1 j.2.2.1 j.2.2.2 h

theorem firstPhysicalCommonRows_indexed (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : Eis) :
    firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
    ∑ j ∈ firstCommonIndices F, firstCommonWeight p hg C₁ C₂ h j *
      firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K (firstCommonNorms p A₁ A₂ C R d h j) := by
  simp only [firstPhysicalCommonRows,firstCommonIndices,Finset.sum_product,Finset.sum_sigma,
    firstCommonWeight,firstCommonNorms,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  ring

theorem firstPhysicalCommonRows_integral (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ omega₁ omega₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : Eis)
    (s : Fin 9 → ℝ) (g : Fin 9 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ j ∈ firstCommonIndices F,
      firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
        (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K
        (firstCommonNorms p A₁ A₂ C R d h j) =
      (firstRootScale s:ℂ)⁻¹ *
        (omega₁ (primeProductNorm p j.2.2.1/s 7)*omega₂ (primeProductNorm p j.2.2.2/s 8)) *
        ∫ z : Frequency × (Fin 9 → ℝ),fullProfileDensity g b₁ b₂ b₃ z *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
            (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) :
    firstPhysicalCommonRows p hg F C₁ C₂
      (fun x => W₁ (x/(s 0*s 2*s 5*s 7))) (fun x => W₂ (x/(s 1*s 2*s 5*s 8)))
      Φ A₁ A₂ C R K d h =
    (firstRootScale s:ℂ)⁻¹ * ∫ z : Frequency × (Fin 9 → ℝ),fullProfileDensity g b₁ b₂ b₃ z *
      ∑ j ∈ firstCommonIndices F,firstCommonWeight p hg C₁ C₂ h j *
        (omega₁ (primeProductNorm p j.2.2.1/s 7)*omega₂ (primeProductNorm p j.2.2.2/s 8)) *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
          (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2 := by
  rw [firstPhysicalCommonRows_indexed]
  calc
    _ = (firstRootScale s:ℂ)⁻¹ * ∑ j ∈ firstCommonIndices F,
        (firstCommonWeight p hg C₁ C₂ h j *
          (omega₁ (primeProductNorm p j.2.2.1/s 7)*omega₂ (primeProductNorm p j.2.2.2/s 8))) *
        ∫ z : Frequency × (Fin 9 → ℝ),fullProfileDensity g b₁ b₂ b₃ z *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
            (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [he j hj]
      ring
    _ = _ := by
      rw [full_density_finite_sum]

end
end InverseMoment

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
