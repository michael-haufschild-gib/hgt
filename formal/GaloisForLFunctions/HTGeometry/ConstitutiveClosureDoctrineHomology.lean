import GaloisForLFunctions.HTGeometry.ConstitutiveCarrierComposition

/-!
# Closure-doctrine serial carrier homology

A completion or admission doctrine replaces raw ranges by larger submodules.  Two independent
homology defects then measure failure of the algebraic primary--secondary birth sequence.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

section AlgebraicDoctrine

variable {𝕜 : Type u} {K : Type v} {A : Type w}
variable [Field 𝕜]
variable [AddCommGroup K] [Module 𝕜 K]
variable [AddCommGroup A] [Module 𝕜 A]

/-- Secondary-to-composite transport after a doctrine has enlarged the discarded layers. -/
def doctrineSecondaryMap (T : K →ₗ[𝕜] A) (R : Submodule 𝕜 K) (P : Submodule 𝕜 A)
    (hRP : R ≤ P.comap T) : (K ⧸ R) →ₗ[𝕜] (A ⧸ P) :=
  R.mapQ P T hRP

/-- Composite-to-primary transition between two doctrine layers. -/
def doctrinePrimaryMap (P Q : Submodule 𝕜 A) (hPQ : P ≤ Q) :
    (A ⧸ P) →ₗ[𝕜] (A ⧸ Q) :=
  Submodule.factor hPQ

@[simp]
theorem doctrineSecondaryMap_mkQ
    (T : K →ₗ[𝕜] A) (R : Submodule 𝕜 K) (P : Submodule 𝕜 A)
    (hRP : R ≤ P.comap T) (k : K) :
    doctrineSecondaryMap T R P hRP (R.mkQ k) = P.mkQ (T k) :=
  Submodule.mapQ_apply R P T k

@[simp]
theorem doctrinePrimaryMap_mkQ
    (P Q : Submodule 𝕜 A) (hPQ : P ≤ Q) (a : A) :
    doctrinePrimaryMap P Q hPQ (P.mkQ a) = Q.mkQ a :=
  Submodule.factor_mk hPQ a

/-- Source-side completion homology: kernel is the completed composite preimage modulo the
declared inner layer. -/
theorem ker_doctrineSecondaryMap
    (T : K →ₗ[𝕜] A) (R : Submodule 𝕜 K) (P : Submodule 𝕜 A)
    (hRP : R ≤ P.comap T) :
    LinearMap.ker (doctrineSecondaryMap T R P hRP) =
      (P.comap T).map R.mkQ := by
  exact Submodule.ker_mapQ R P T hRP

/-- The secondary map is injective exactly when completion creates no extra composite preimage. -/
theorem doctrineSecondaryMap_injective_iff
    (T : K →ₗ[𝕜] A) (R : Submodule 𝕜 K) (P : Submodule 𝕜 A)
    (hRP : R ≤ P.comap T) :
    Function.Injective (doctrineSecondaryMap T R P hRP) ↔
      P.comap T = R := by
  constructor
  · intro hinj
    apply le_antisymm
    · intro k hk
      have hz : doctrineSecondaryMap T R P hRP (R.mkQ k) = 0 := by
        rw [doctrineSecondaryMap_mkQ]
        exact (Submodule.Quotient.mk_eq_zero _).2 hk
      have hq : R.mkQ k = 0 := hinj (hz.trans (map_zero _).symm)
      exact (Submodule.Quotient.mk_eq_zero _).1 hq
    · exact hRP
  · intro heq x y hxy
    induction x using Submodule.Quotient.induction_on with | _ k => ?_
    induction y using Submodule.Quotient.induction_on with | _ k' => ?_
    change doctrineSecondaryMap T R P hRP (R.mkQ k) =
      doctrineSecondaryMap T R P hRP (R.mkQ k') at hxy
    change R.mkQ k = R.mkQ k'
    rw [doctrineSecondaryMap_mkQ, doctrineSecondaryMap_mkQ] at hxy
    rw [show P.mkQ (T k) = P.mkQ (T k') ↔ _ from Submodule.Quotient.eq P] at hxy
    rw [show R.mkQ k = R.mkQ k' ↔ _ from Submodule.Quotient.eq R]
    have hkmem : k - k' ∈ P.comap T := by
      change T (k - k') ∈ P
      simpa only [map_sub] using hxy
    rwa [heq] at hkmem

/-- The primary transition is always surjective. -/
theorem doctrinePrimaryMap_surjective
    (P Q : Submodule 𝕜 A) (hPQ : P ≤ Q) :
    Function.Surjective (doctrinePrimaryMap P Q hPQ) :=
  Submodule.factor_surjective hPQ

/-- The doctrine maps form a complex once every outer carrier lies in the primary layer. -/
theorem doctrineSerial_complex
    (T : K →ₗ[𝕜] A) (R : Submodule 𝕜 K) (P Q : Submodule 𝕜 A)
    (hRP : R ≤ P.comap T) (hPQ : P ≤ Q) (hTQ : LinearMap.range T ≤ Q) :
    (doctrinePrimaryMap P Q hPQ).comp (doctrineSecondaryMap T R P hRP) = 0 := by
  ext k
  change doctrinePrimaryMap P Q hPQ
    (doctrineSecondaryMap T R P hRP (R.mkQ k)) = 0
  rw [doctrineSecondaryMap_mkQ, doctrinePrimaryMap_mkQ]
  exact (Submodule.Quotient.mk_eq_zero _).2 (hTQ ⟨k, rfl⟩)

/-- Target-side completion homology vanishes exactly when the completed outer layer is generated
by actual outer carriers and the completed composite layer. -/
theorem doctrineSerial_exact_middle_iff
    (T : K →ₗ[𝕜] A) (R : Submodule 𝕜 K) (P Q : Submodule 𝕜 A)
    (hRP : R ≤ P.comap T) (hPQ : P ≤ Q) (hTQ : LinearMap.range T ≤ Q) :
    LinearMap.range (doctrineSecondaryMap T R P hRP) =
        LinearMap.ker (doctrinePrimaryMap P Q hPQ) ↔
      Q = LinearMap.range T ⊔ P := by
  constructor
  · intro hexact
    apply le_antisymm
    · intro a haQ
      have hker : P.mkQ a ∈ LinearMap.ker (doctrinePrimaryMap P Q hPQ) := by
        rw [LinearMap.mem_ker, doctrinePrimaryMap_mkQ]
        exact (Submodule.Quotient.mk_eq_zero _).2 haQ
      rw [← hexact] at hker
      obtain ⟨x, hx⟩ := hker
      induction x using Submodule.Quotient.induction_on with | _ k => ?_
      change doctrineSecondaryMap T R P hRP (R.mkQ k) = P.mkQ a at hx
      rw [doctrineSecondaryMap_mkQ] at hx
      have hdiff : T k - a ∈ P := (Submodule.Quotient.eq P).1 hx
      rw [Submodule.mem_sup]
      refine ⟨T k, ⟨k, rfl⟩, a - T k, ?_, ?_⟩
      · have : a - T k = -(T k - a) := by abel
        rw [this]
        exact P.neg_mem hdiff
      · abel
    · exact sup_le hTQ hPQ
  · intro hQ
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using Submodule.Quotient.induction_on with | _ k => ?_
      change doctrineSecondaryMap T R P hRP (R.mkQ k) ∈
        LinearMap.ker (doctrinePrimaryMap P Q hPQ)
      rw [LinearMap.mem_ker, doctrineSecondaryMap_mkQ, doctrinePrimaryMap_mkQ]
      exact (Submodule.Quotient.mk_eq_zero _).2 (hTQ ⟨k, rfl⟩)
    · intro x hx
      induction x using Submodule.Quotient.induction_on with | _ a => ?_
      change P.mkQ a ∈ LinearMap.ker (doctrinePrimaryMap P Q hPQ) at hx
      rw [LinearMap.mem_ker, doctrinePrimaryMap_mkQ] at hx
      change Submodule.Quotient.mk a = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero, hQ, Submodule.mem_sup] at hx
      obtain ⟨t, ⟨k, hk⟩, p, hp, hsum⟩ := hx
      refine ⟨R.mkQ k, ?_⟩
      change doctrineSecondaryMap T R P hRP (R.mkQ k) = P.mkQ a
      rw [doctrineSecondaryMap_mkQ]
      apply (Submodule.Quotient.eq P).2
      change T k - a ∈ P
      rw [show T k = t from hk, ← hsum]
      have heq : t - (t + p) = -p := by abel
      rw [heq]
      exact P.neg_mem hp

/-- **Two-defect completion-homology law.** The doctrine sequence is short exact exactly when its
source preimage defect and target attainment defect both vanish. -/
theorem doctrineSerial_shortExact_iff
    (T : K →ₗ[𝕜] A) (R : Submodule 𝕜 K) (P Q : Submodule 𝕜 A)
    (hRP : R ≤ P.comap T) (hPQ : P ≤ Q) (hTQ : LinearMap.range T ≤ Q) :
    (Function.Injective (doctrineSecondaryMap T R P hRP) ∧
      LinearMap.range (doctrineSecondaryMap T R P hRP) =
        LinearMap.ker (doctrinePrimaryMap P Q hPQ) ∧
      Function.Surjective (doctrinePrimaryMap P Q hPQ)) ↔
    (P.comap T = R ∧ Q = LinearMap.range T ⊔ P) := by
  rw [doctrineSecondaryMap_injective_iff,
    doctrineSerial_exact_middle_iff T R P Q hRP hPQ hTQ]
  simp [doctrinePrimaryMap_surjective P Q hPQ]

end AlgebraicDoctrine

section TopologicalDoctrine

variable {𝕜 : Type u} {E : Type v} {K : Type w} {A : Type*}
variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup K] [NormedSpace 𝕜 K]
variable [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]

def serialInnerClosure (S : E →L[𝕜] K) (T : K →L[𝕜] A) : Submodule 𝕜 K :=
  (LinearMap.range S.toLinearMap ⊔ LinearMap.ker T.toLinearMap).topologicalClosure

def serialCompositeClosure (S : E →L[𝕜] K) (T : K →L[𝕜] A) : Submodule 𝕜 A :=
  (LinearMap.range (T.comp S).toLinearMap).topologicalClosure

def serialOuterClosure (T : K →L[𝕜] A) : Submodule 𝕜 A :=
  (LinearMap.range T.toLinearMap).topologicalClosure

theorem serialInnerClosure_le_comapCompositeClosure
    (S : E →L[𝕜] K) (T : K →L[𝕜] A) :
    serialInnerClosure S T ≤ (serialCompositeClosure S T).comap T.toLinearMap := by
  apply Submodule.topologicalClosure_minimal
  · rw [sup_le_iff]
    constructor
    · rintro k ⟨e, rfl⟩
      change T (S e) ∈ serialCompositeClosure S T
      apply Submodule.le_topologicalClosure
      exact ⟨e, rfl⟩
    · intro k hk
      change T k ∈ serialCompositeClosure S T
      have hk0 : T k = 0 := LinearMap.mem_ker.mp hk
      rw [hk0]
      exact Submodule.zero_mem _
  · change IsClosed (T ⁻¹' (serialCompositeClosure S T : Set A))
    exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous

theorem serialCompositeClosure_le_outerClosure
    (S : E →L[𝕜] K) (T : K →L[𝕜] A) :
    serialCompositeClosure S T ≤ serialOuterClosure T := by
  apply Submodule.topologicalClosure_mono
  rintro a ⟨e, he⟩
  refine ⟨S e, ?_⟩
  change T (S e) = a at he
  exact he

theorem range_le_serialOuterClosure (T : K →L[𝕜] A) :
    LinearMap.range T.toLinearMap ≤ serialOuterClosure T :=
  Submodule.le_topologicalClosure _

def separatedSerialSecondaryMap (S : E →L[𝕜] K) (T : K →L[𝕜] A) :
    (K ⧸ serialInnerClosure S T) →ₗ[𝕜] (A ⧸ serialCompositeClosure S T) :=
  doctrineSecondaryMap T.toLinearMap (serialInnerClosure S T) (serialCompositeClosure S T)
    (serialInnerClosure_le_comapCompositeClosure S T)

def separatedSerialPrimaryMap (S : E →L[𝕜] K) (T : K →L[𝕜] A) :
    (A ⧸ serialCompositeClosure S T) →ₗ[𝕜] (A ⧸ serialOuterClosure T) :=
  doctrinePrimaryMap (serialCompositeClosure S T) (serialOuterClosure T)
    (serialCompositeClosure_le_outerClosure S T)

/-- Hausdorff-separated serial birth is exact precisely when both closure-exchange identities
hold. -/
theorem separatedSerial_shortExact_iff
    (S : E →L[𝕜] K) (T : K →L[𝕜] A) :
    (Function.Injective (separatedSerialSecondaryMap S T) ∧
      LinearMap.range (separatedSerialSecondaryMap S T) =
        LinearMap.ker (separatedSerialPrimaryMap S T) ∧
      Function.Surjective (separatedSerialPrimaryMap S T)) ↔
    ((serialCompositeClosure S T).comap T.toLinearMap = serialInnerClosure S T ∧
      serialOuterClosure T =
        LinearMap.range T.toLinearMap ⊔ serialCompositeClosure S T) := by
  exact doctrineSerial_shortExact_iff T.toLinearMap
    (serialInnerClosure S T) (serialCompositeClosure S T) (serialOuterClosure T)
    (serialInnerClosure_le_comapCompositeClosure S T)
    (serialCompositeClosure_le_outerClosure S T) (range_le_serialOuterClosure T)

end TopologicalDoctrine

section IndependenceCells

def pairIdentity : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := LinearMap.id

theorem sourceCompletionDefect_without_targetDefect :
    ((⊤ : Submodule ℝ (ℝ × ℝ)).comap pairIdentity ≠
      LinearMap.range firstCarrierEmbedding) ∧
    (⊤ : Submodule ℝ (ℝ × ℝ)) =
      LinearMap.range pairIdentity ⊔ (⊤ : Submodule ℝ (ℝ × ℝ)) := by
  constructor
  · intro h
    have hv : ((0, 1) : ℝ × ℝ) ∈ LinearMap.range firstCarrierEmbedding := by
      rw [← h]
      trivial
    exact verticalLift_not_mem_firstCarrierRange hv
  · simp

theorem targetCompletionDefect_without_sourceDefect :
    ((⊥ : Submodule ℝ (ℝ × ℝ)).comap firstCarrierEmbedding =
      (⊥ : Submodule ℝ ℝ)) ∧
    (⊤ : Submodule ℝ (ℝ × ℝ)) ≠
      LinearMap.range firstCarrierEmbedding ⊔ (⊥ : Submodule ℝ (ℝ × ℝ)) := by
  constructor
  · rw [Submodule.comap_bot, LinearMap.ker_eq_bot]
    intro x y hxy
    exact congrArg Prod.fst hxy
  · simpa using (Ne.symm (show LinearMap.range firstCarrierEmbedding ≠
      (⊤ : Submodule ℝ (ℝ × ℝ)) by
        intro h
        apply verticalLift_not_mem_firstCarrierRange
        rw [h]
        trivial))

theorem completionHomologyDefects_independent :
    (((⊤ : Submodule ℝ (ℝ × ℝ)).comap pairIdentity ≠
        LinearMap.range firstCarrierEmbedding) ∧
      (⊤ : Submodule ℝ (ℝ × ℝ)) =
        LinearMap.range pairIdentity ⊔ (⊤ : Submodule ℝ (ℝ × ℝ))) ∧
    (((⊥ : Submodule ℝ (ℝ × ℝ)).comap firstCarrierEmbedding =
        (⊥ : Submodule ℝ ℝ)) ∧
      (⊤ : Submodule ℝ (ℝ × ℝ)) ≠
        LinearMap.range firstCarrierEmbedding ⊔ (⊥ : Submodule ℝ (ℝ × ℝ))) :=
  ⟨sourceCompletionDefect_without_targetDefect,
    targetCompletionDefect_without_sourceDefect⟩

abbrev CompletionGammaSpace := lp (fun _ : ℕ => ℂ) 2

/-- The certified compact dense Gamma reporter realizes a genuine target-side completion defect
while its source-side preimage identity remains exact. -/
theorem gammaReporter_targetCompletionDefect_only :
    ((serialCompositeClosure
        (0 : CompletionGammaSpace →L[ℂ] CompletionGammaSpace)
        (gammaRadialReporter (1 : ℝ))).comap
          (gammaRadialReporter (1 : ℝ)).toLinearMap =
      serialInnerClosure
        (0 : CompletionGammaSpace →L[ℂ] CompletionGammaSpace)
        (gammaRadialReporter (1 : ℝ))) ∧
    serialOuterClosure (gammaRadialReporter (1 : ℝ)) ≠
      LinearMap.range (gammaRadialReporter (1 : ℝ)).toLinearMap ⊔
        serialCompositeClosure
          (0 : CompletionGammaSpace →L[ℂ] CompletionGammaSpace)
          (gammaRadialReporter (1 : ℝ)) := by
  have hcell := gammaRadialReporter_compact_injective_dense_nonsurjective
    (rho := (1 : ℝ)) one_ne_zero
  have hinj := hcell.2.1
  have hdense := hcell.2.2.1
  have hnsurj := hcell.2.2.2
  have hker : LinearMap.ker (gammaRadialReporter (1 : ℝ)).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have hcomp : serialCompositeClosure
      (0 : CompletionGammaSpace →L[ℂ] CompletionGammaSpace)
      (gammaRadialReporter (1 : ℝ)) = ⊥ := by
    simp [serialCompositeClosure]
  have hinner : serialInnerClosure
      (0 : CompletionGammaSpace →L[ℂ] CompletionGammaSpace)
      (gammaRadialReporter (1 : ℝ)) = ⊥ := by
    rw [serialInnerClosure, hker]
    simp
  have houter : serialOuterClosure (gammaRadialReporter (1 : ℝ)) = ⊤ := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mp
    change Dense
      (LinearMap.range (gammaRadialReporter (1 : ℝ)).toLinearMap :
        Set CompletionGammaSpace)
    have hrange : Set.range (gammaRadialReporter (1 : ℝ)) =
        (LinearMap.range (gammaRadialReporter (1 : ℝ)).toLinearMap :
          Set CompletionGammaSpace) := by
      ext x
      constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, rfl⟩
    rwa [← hrange]
  constructor
  · rw [hcomp, hinner, Submodule.comap_bot, hker]
  · intro heq
    have hrangeTop :
        LinearMap.range (gammaRadialReporter (1 : ℝ)).toLinearMap = ⊤ := by
      rw [houter, hcomp, sup_bot_eq] at heq
      exact heq.symm
    exact hnsurj (LinearMap.range_eq_top.mp hrangeTop)

end IndependenceCells

end


end GaloisForLFunctions.HTGeometry

