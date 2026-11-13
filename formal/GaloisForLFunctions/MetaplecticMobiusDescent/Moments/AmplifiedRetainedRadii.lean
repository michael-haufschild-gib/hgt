/-
Amplified retained radii adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.AmplificationChildSourceCaps
import GaloisForLFunctions.MetaplecticMobiusDescent.Energy.FirstStageLossBudgets
import GaloisForLFunctions.MetaplecticMobiusDescent.Energy.ChildEnvelopeFitting

/-!
# Amplified retained radii

Error and main common radii of the amplified retained radius; nonexceptional child envelopes;
the first saving of the descent ledger; original images of the allocated ray dictionary; mixed
normalization references.
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
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentAllocatedRayDictionary
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeCancellation
local notation "O" => Eisenstein.O

variable {α : Type*} [Fintype α] [DecidableEq α]

def originalEmbedding (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) :
    CenteredMomentCommonProfile.liveIndices B.val ↪ α :=
  ⟨Subtype.val, Subtype.val_injective⟩

def remaining (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Finset (CenteredMomentCommonProfile.liveIndices B.val) :=
  CenteredMomentDivisorRaw.liveIndices (ι := CenteredMomentCommonProfile.liveIndices B.val) L a \ J

def originalImage (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : Finset α :=
  (remaining s C B L a J).map (originalEmbedding s C B)

lemma projection_injective (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Function.Injective (fun i : remaining s C B L a J => i.val.val) := by
  intro i j h
  exact Subtype.ext (Subtype.ext h)

lemma mem_originalImage (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) (i : α) :
    i ∈ originalImage s C B L a J ↔
      ∃ j ∈ remaining s C B L a J, j.val = i := by
  simp only [originalImage, Finset.mem_map, originalEmbedding, Function.Embedding.coeFn_mk]

lemma originalImage_card (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    (originalImage s C B L a J).card = (remaining s C B L a J).card := Finset.card_map _

def commonFirst (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : ℝ :=
  if left then (commonData s C R B).X₁ else (commonData s C R B).Y₁

def commonSecond (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : ℝ :=
  if left then (commonData s C R B).X₂ else (commonData s C R B).Y₂

omit [DecidableEq α] in
lemma commonFirst_pos (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : 0 < commonFirst s C R B left := by
  unfold commonFirst
  split
  · exact (commonData s C R B).X₁_pos
  · exact (commonData s C R B).Y₁_pos

omit [DecidableEq α] in
lemma commonSecond_pos (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : 0 < commonSecond s C R B left := by
  unfold commonSecond
  split
  · exact (commonData s C R B).X₂_pos
  · exact (commonData s C R B).Y₂_pos

section RayData
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

variable {M H hH}
variable {s : Input α} {η₀ : Character} {θ : α → RayQuotient.Characters M H}
  {w σ freq : α → ℝ} {W : ℝ → ℂ} {bslot Z : ℝ}
  (h : Matches M H hH s η₀ θ w σ freq W bslot Z)

include h

omit [DecidableEq α] in
lemma common_coefficient (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (i : CenteredMomentCommonProfile.liveIndices B.val)
    (I : Ideal O) :
    (commonData (withHeight s τ v) C R B).coefficient i I =
      idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
        annularWeight W (Z^(w i.val)) (σ i.val) (freq i.val) I := by
  change s.ν i.val I * s.W i.val ((I.absNorm : ℝ) / s.P i.val) = _
  rw [h.character, h.profile, h.scale]
  rfl

omit [DecidableEq α] in
lemma common_height_coefficient (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (i : CenteredMomentCommonProfile.liveIndices B.val)
    (I : Ideal O) (hI : I ≠ 0) :
    heightCoefficient ((commonData (withHeight s τ v) C R B).coefficient i) v I =
      ((Z^(w i.val) : ℝ) : ℂ)^(Complex.I*v) *
        (idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
          annularWeight W (Z^(w i.val)) (σ i.val) (v+freq i.val) I) := by
  have he : (commonData (withHeight s τ v) C R B).coefficient i =
      fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
        annularWeight W (Z^(w i.val)) (σ i.val) (freq i.val) I :=
    funext (common_coefficient h τ v C R B i)
  rw [he]
  exact CenteredMomentEnergySlotHeight.height_coefficient _ W _ _ _ v
    (h.scale i.val ▸ s.P_pos i.val) I hI

omit [DecidableEq α] in
lemma scale_phase_norm (i : α) (v : ℝ) :
    ‖((Z^(w i) : ℝ) : ℂ)^(Complex.I*v)‖ = 1 := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos (h.scale i ▸ s.P_pos i) (Complex.I*v)

theorem common_energy (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (m A : O) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d := commonData (withHeight s τ v) C R B
    energy τ m A 0 W₁ W₂
      (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) X₁ X₂ keep Φ K =
    energy τ m A 0 W₁ W₂
      (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) X₁ X₂ keep Φ K := by
  dsimp only
  have hc : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).coefficient i.val) =
      fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i.val.val)) I *
        annularWeight W (Z^(w i.val.val)) (σ i.val.val) (freq i.val.val) I := by
    funext i I
    exact common_coefficient h τ v C R B i.val I
  have hp : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).P i.val) = fun i => Z^(w i.val.val) := by
    funext i
    exact h.scale i.val.val
  have hs : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).slots i.val) =
      fun i => primePool M H bslot (Z^(w i.val.val)) := by
    funext i
    exact h.pool i.val.val
  have hhc := congrArg (fun f => fun i : remaining s C B L a J => heightCoefficient (f i) v) hc
  rw [hhc, hp, hs]
  rw [CenteredMomentEnergySlotHeight.inherited_height_energy τ m A W₁ W₂ _ _ _ _ _ _
    (fun i => h.scale i.val.val ▸ s.P_pos i.val.val)
    (fun i I hI => (s.prime i.val.val I (by rw [h.pool]; exact hI)).ne_zero)
    v 0 X₁ X₂ keep Φ K]
  exact CenteredMomentEnergyReindex.energy_subset_map (originalEmbedding s C B)
    (remaining s C B L a J) τ m A W₁ W₂
    (fun i => primePool M H bslot (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
    (fun i => Z^(w i)) 0 X₁ X₂ keep Φ K

theorem common_clipped_energy (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (V₁ V₂ : Plain) (X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂)
    (D₁ D₂ : Finset (Ideal O)) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d := commonData (withHeight s τ v) C R B
    let W₁ := V₁.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ hX₁ 0) v
    let W₂ := V₂.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ hX₂ 1) v
    let Y₁ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)
    let Y₂ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator 1) 1 0
      W₁ W₂ (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) Y₁ Y₂ keep Φ K =
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator 1) 1 0
      W₁ W₂ (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) Y₁ Y₂ keep Φ K :=
  common_energy h τ v C R B L a J _ 1 _ _ _ _ keep Φ K

theorem both_common_rectangles (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (V₁ V₂ : Plain) (left : Bool)
    (D₁ D₂ : Finset (Ideal O)) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let X₁ := commonFirst s C R B left
    let X₂ := commonSecond s C R B left
    let hX₁ := commonFirst_pos s C R B left
    let hX₂ := commonSecond_pos s C R B left
    let d := commonData (withHeight s τ v) C R B
    let W₁ := V₁.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ hX₁ 0) v
    let W₂ := V₂.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ hX₂ 1) v
    let Y₁ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)
    let Y₂ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator 1) 1 0
      W₁ W₂ (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) Y₁ Y₂ keep Φ K =
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator 1) 1 0
      W₁ W₂ (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) Y₁ Y₂ keep Φ K :=
  common_clipped_energy h τ v C R B L a J V₁ V₂
    (commonFirst s C R B left) (commonSecond s C R B left)
    (commonFirst_pos s C R B left) (commonSecond_pos s C R B left) D₁ D₂ keep Φ K

omit h

lemma deleted_clipped_scale_pos (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (X : ℝ) (j : Fin 2) (D : Finset (Ideal O)) (hD : ∀I∈D,I≠0) :
    0 < clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X j)/(Ideal.absNorm (∏I∈D,I):ℝ) := by
  apply div_pos (zero_lt_one.trans_le (clippedScale_ge_one _))
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Finset.prod_ne_zero_iff.mpr hD))

lemma originalImage_fixedQ (Q : Ideal O) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (i : originalImage s C B L a J) :
    Q ≤ (relativeCharacter M H hH η₀ (θ i)).modulus :=
  relativeCharacter_fixedQ M H hH η₀ (θ i) Q hQM hQη

lemma originalImage_bounds (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (Lslot lo hi height heightShift v : ℝ)
    (hw : ∀i,0 ≤ w i) (hwL : ∀i,w i ≤ Lslot)
    (hσlo : ∀i,lo ≤ σ i) (hσhi : ∀i,σ i ≤ hi)
    (hf : ∀i,|freq i| ≤ height) (hv : |v| ≤ heightShift) :
    ∀i : originalImage s C B L a J,
      0 ≤ w i ∧ w i ≤ Lslot ∧ lo ≤ σ i ∧ σ i ≤ hi ∧ |v+freq i| ≤ height+heightShift := by
  intro i
  refine ⟨hw i, hwL i, hσlo i, hσhi i, ?_⟩
  exact (abs_add_le v (freq i)).trans (by linarith [hf i])

lemma originalImage_scale_bounds (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (hZ : 1< Z) (Lslot : ℝ) (hw : ∀i,0 ≤ w i) (hwL : ∀i,w i ≤ Lslot) :
    ∀i : originalImage s C B L a J, 1 ≤ Z^(w i) ∧ Z^(w i) ≤ Z^Lslot := by
  intro i
  exact ⟨Real.one_le_rpow hZ.le (hw i), Real.rpow_le_rpow_of_exponent_le hZ.le (hwL i)⟩

end RayData
end CenteredMomentAllocatedRayDictionary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Filter

namespace CenteredMomentFirstSourceConductorCaps
open Eisenstein   HeckeFamily
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentChildRows
open CenteredMomentSecondHeightFamily
local notation "O"=> Eisenstein.O

lemma divisor_norm_le (I C : Ideal O) (hC : C≠0) (h : I∣C) :
    (I.absNorm:ℝ)≤ C.absNorm := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC))
    (map_dvd Ideal.absNorm h)

lemma original_factor_caps (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) :
    ‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2≤ C.absNorm ∧
    ‖ringComplex (activeConductor C D)‖^2≤ C.absNorm := by
  rw [ringComplex_norm_sq_eq_absNorm_span,ringComplex_norm_sq_eq_absNorm_span]
  exact ⟨divisor_norm_le _ C hC.1 ((subsetGenerator_span_dvd C D E).trans (commonPart_dvd C D hC.1)),
    divisor_norm_le _ C hC.1 ((activeConductor_span_dvd C D).trans (commonPart_dvd C D hC.1))⟩

theorem fixed_pair_caps (η : Character) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    (F.left.modulus.absNorm:ℝ)≤ fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 ∧
    (F.right.modulus.absNorm:ℝ)≤ fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
  have h:=original_factor_caps C D hC E
  have hb : fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
      ‖ringComplex (activeConductor C D)‖^2≤
      fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
    have hf:=fixedPresentationCost_pos.le
    nlinarith [mul_le_mul h.1 h.2 (sq_nonneg _) (Nat.cast_nonneg C.absNorm),
      mul_nonneg hf (Nat.cast_nonneg η.modulus.absNorm)]
  exact ⟨F.conductor_caps.1.trans hb,F.conductor_caps.2.trans hb⟩


end CenteredMomentFirstSourceConductorCaps

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSecondNonexceptionalScalar
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRadicalBudget CenteredMomentSourceBlockWindows
open CenteredMomentSourceDyadicShell CenteredMomentHeckeColumnWindow
local notation "O" => Eisenstein.O

lemma scalar_cancel (K G V U c d x y h q M:ℝ)
    (hc:0< c)(hd:0< d)(hx:0< x)(hy:0< y)(hU:0< U)(hq:0≤ q) :
    (K/(Real.sqrt c*Real.sqrt d*Real.sqrt x*Real.sqrt y))*(G/U)/Real.sqrt (c*d)*
      (M*U*V*h)/(1+q)=M*((K*G*V/(c*d))*h/(x*y))/(1+q)*Real.sqrt (x*y) := by
  rw [Real.sqrt_mul hc.le,Real.sqrt_mul hx.le]
  have hc':Real.sqrt c≠0:=(Real.sqrt_pos.mpr hc).ne'
  have hd':Real.sqrt d≠0:=(Real.sqrt_pos.mpr hd).ne'
  have hx':Real.sqrt x≠0:=(Real.sqrt_pos.mpr hx).ne'
  have hy':Real.sqrt y≠0:=(Real.sqrt_pos.mpr hy).ne'
  have hq':1+q≠0:=by positivity
  field_simp
  ; ring_nf
  ; simp [Real.sq_sqrt,hc.le,hd.le,hx.le,hy.le]

theorem physical_effective_scale (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K<
      dyadicScale (n 0) := by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    have h0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1).1
    exact (dyadicWeight_support (n 0) h0).2
  · exact False.elim (hz rfl)

def childEnvelope (η:Character)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ :=
  (fixedFactor:ℝ)*η.modulus.absNorm*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)

theorem family_child_envelope {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(hf:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)(χ:RayCharacter) :
    ((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)≤ childEnvelope η C D U n := by
  have hh := (hf.physical_budget t S β R rows W K hK n hne χ).1
  have hh' : ((τ χ).modulus.absNorm:ℝ)≤
      (fixedFactor:ℝ)*η.modulus.absNorm*(∏P∈U,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by
    have hhcast : ((τ χ).modulus.absNorm:ℝ)≤
        (η.modulus.absNorm:ℝ)*fixedFactor*(∏P∈U,P.val).absNorm*
          (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by exact_mod_cast hh
    simpa only [mul_comm (η.modulus.absNorm:ℝ) (fixedFactor:ℝ)] using hhcast
  exact mul_le_mul_of_nonneg_right hh' (dyadicScale_pos _).le

theorem actual_envelope_scalar (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(_hK:0< K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    (fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) := by
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hu:0<((∏P∈U,P.val).absNorm:ℝ):=by
    rw [map_prod,Nat.cast_prod]
    apply Finset.prod_pos
    intro P hP
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by rw [←commonPrime_span C D hC P]; exact (commonPrime_supported C D hC P).1))
  have hn (i:Fin 4):0< dyadicScale (n i):=dyadicScale_pos _
  let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hr:0< r:=div_pos (mul_pos (hn 0) (hn 1)) (mul_pos (hn 2) (hn 3))
  have hscale := (physical_effective_scale η t S β C D hC hD U R rows W K n hne).le
  have he : secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.span {commonFrequencyGenerator C D}).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm/((C.absNorm:ℝ)*D.absNorm) := by
    rw [secondEffectiveScale,←normValue_eq_embedding,normValue_mul]
    dsimp only [normValue]
    ring
  have hrat : secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
      dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))≤ r := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscale (dyadicScale_pos _).le) (mul_pos (hn 2) (hn 3)).le
  have hfrac : (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
      dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))/(1+r)≤1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  rw [outerScalar,normalizer,actual_partitionNormalizer C D hC]
  change _≤(fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))
  rw [childEnvelope,scalar_cancel _ _ _ _ _ _ _ _ _ r _ hc hd
    (dyadicScale_pos _) (dyadicScale_pos _) hu hr.le]
  rw [←he]
  calc
    _=((fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
      ((secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
        dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))/(1+r)):=by ring
    _≤ _:=by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac
        (show 0≤(fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) by positivity)

theorem actual_residual_sqrt_cap (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤ Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))≤
      4*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm) := by
  obtain ⟨I,J,hI,hJ,hwi,hwj⟩:=physicalBlock_column_witnesses η t S β C D hC hD U R rows W K n hne
  have hH:0≤ Hsource:=(Nat.cast_nonneg ((C*(I:Ideal O)).absNorm)).trans (hsource _ hI)
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hx:dyadicScale (n 2)≤4*Hsource/(C.absNorm:ℝ):=
    (residual_window_bounds C I hC.1 0 Hsource (n 2) (Nat.cast_nonneg _) (hsource _ hI) hwi).2
  have hy:dyadicScale (n 3)≤4*Hsource/(D.absNorm:ℝ):=
    (residual_window_bounds D J hD.1 0 Hsource (n 3) (Nat.cast_nonneg _) (hsource _ hJ) hwj).2
  have hh:=Real.sqrt_le_sqrt (mul_le_mul hx hy (dyadicScale_pos _).le (by positivity))
  have he:(4*Hsource/(C.absNorm:ℝ))*(4*Hsource/(D.absNorm:ℝ))=
      (4*Hsource)^2/((C.absNorm:ℝ)*D.absNorm):=by ring
  rw [he,Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (by positivity)] at hh
  exact hh

theorem actual_source_envelope_scalar (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤ Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm) := by
  apply (actual_envelope_scalar η t S β C D hC hD U R rows W K hK n hne).trans
  have hh:=mul_le_mul_of_nonneg_left
    (actual_residual_sqrt_cap η t S β C D hC hD U R rows W K n Hsource hsource hne)
    (show 0≤(fixedFactor:ℝ)*η.modulus.absNorm by positivity)
  convert hh using 1 ; ring

theorem actual_source_envelope_scalar_extra (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤ Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (Eextra:ℝ)(hEextra:0≤ Eextra) :
    ((outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))*Eextra≤
    (4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm))*Eextra :=
  mul_le_mul_of_nonneg_right
    (actual_source_envelope_scalar η t S β C D hC hD U R rows W K hK n Hsource hsource hne) hEextra
end CenteredMomentSecondNonexceptionalScalar

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSecondCapacitySourceShift
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondNonexceptionalScalar CenteredMomentSecondPhysicalLedger
open CenteredMomentSectorLocalization CenteredMomentSourceBlockWindows
open CenteredMomentSecondPhysicalCost CenteredMomentSecondRadicalBudget
open CenteredMomentSupport CenteredMomentSecondWholeKernel  CenteredMomentSourceRow
local notation "O"=> Eisenstein.O

theorem effective_upper (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    dyadicScale (n 0)≤4*secondEffectiveScale C D
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K:=by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    have h0:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1).1
    have hh:=(dyadicWeight_support (n 0) h0).1
    linarith
  · exact False.elim (hz rfl)

lemma adjusted_row_lower (k h x y:ℝ)(hk:0< k)(hh:0< h)(hx:0< x)(hy:0< y):
    x*y/k≤ h*max 1 (1/(k*h/(x*y))):=by
  calc
    _=h*(1/(k*h/(x*y))):=by field_simp
    _≤ _:=mul_le_mul_of_nonneg_left (le_max_right _ _) hh.le

lemma scalar_capacity_shift (Z F q U V H K a c d k h x y:ℝ)
    (hZ:1< Z)(hF:0< F)(hq:0< q)(hU:1≤ U)(hV:0< V)(hH:0< H)(hK:0< K)(ha:0< a)
    (hc:0< c)(hd:0< d)(hk:0< k)(hh:0< h)(hx:0< x)(hy:0< y)
    (g:ℝ)(hg:0< g)(hgc:g≤ c)
    (hscale:k≤4*(K*g*V/(c*d)))(hleft:a*H/c≤ x)(hright:a*H/d≤ y):
    Real.logb Z (H/c)-Real.logb Z (F*q*U*V*h*max 1 (1/(k*h/(x*y))))≤
      Real.logb Z K-Real.logb Z q-Real.logb Z H+Real.logb Z (4/(F*a^2)):=by
  have hu:0< U:=zero_lt_one.trans_le hU
  have hl:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hc) hleft
  have hr:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hd) hright
  have hs:=Real.logb_le_logb_of_le hZ hk hscale
  have hg':=Real.logb_le_logb_of_le hZ hg hgc
  have hu':0≤ Real.logb Z U:=Real.logb_nonneg hZ hU
  have hrow:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos hx hy) hk)
    (adjusted_row_lower k h x y hk hh hx hy)
  have hm:0< max 1 (1/(k*h/(x*y))):=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow] at hl hr hs hrow ⊢
  linarith

def adjustedEnvelope (η:Character)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  childEnvelope η C D U n*
    max 1 (1/(dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))

def adjustedEnvelopeRef (qref:ℝ)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  (fixedFactor:ℝ)*qref*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)*
    max 1 (1/(dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))

theorem actual_capacity_shift_reference (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K H a Z qref:ℝ)(n:Fin 4→ℤ)
    (hq:0< qref)(hK:0< K)(hH:0< H)(ha:0< a)(hZ:1< Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(I.absNorm:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (H/(C.absNorm:ℝ))-Real.logb Z (adjustedEnvelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z H+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)):=by
  have hc:=CenteredMomentFirstScale.norm_pos C hC.1
  have hd:=CenteredMomentFirstScale.norm_pos D hD.1
  have hg:=CenteredMomentFirstScale.norm_pos (Ideal.span {commonFrequencyGenerator C D})
    (Ideal.span_singleton_eq_bot.not.mpr (commonFrequencyGenerator_ne_zero C D hC))
  have hv:=CenteredMomentFirstScale.norm_pos (Ideal.span {nonunitFrequencyGenerator C D U})
    (Ideal.span_singleton_eq_bot.not.mpr (nonunitFrequencyGenerator_ne_zero C D hC U))
  have hu:=common_product_pos C D hC U
  have hu1:1≤((∏P∈U,P.val).absNorm:ℝ):=by exact_mod_cast (show 1≤(∏P∈U,P.val).absNorm from by exact_mod_cast hu)
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hdiv:Ideal.span {commonFrequencyGenerator C D}∣C:=by
    have hh:=Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (commonFrequencyGenerator_dvd C D hC hD hCD).1
    simpa only [primary_span_supported C hC] using hh
  have hgc:=CenteredMomentFirstSourceConductorCaps.divisor_norm_le _ C hC.1 hdiv
  have hh:=physicalBlock_scale_lower η t S β C D hC hD U R rows W K n a H ha hlower hne
  have hl:a*H/(C.absNorm:ℝ)≤ dyadicScale (n 2):=by
    have hv':=(le_div_iff₀ ha).mp hh.1
    convert hv' using 1 <;> first | rfl | ring
  have hr:a*H/(D.absNorm:ℝ)≤ dyadicScale (n 3):=by
    have hv':=(le_div_iff₀ ha).mp hh.2
    convert hv' using 1 <;> first | rfl | ring
  have hs:=effective_upper η t S β C D hC hD U R rows W K n hne
  have he:secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)*
        Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U})/((C.absNorm:ℝ)*D.absNorm):=by
    simp only [secondEffectiveScale,map_mul,norm_mul,mul_pow,
      ringComplex_norm_sq_eq_absNorm_span]
    ring
  rw [he] at hs
  exact scalar_capacity_shift Z (fixedFactor:ℝ) qref
    ((∏P∈U,P.val).absNorm:ℝ) ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ)
    H K a (C.absNorm:ℝ) (D.absNorm:ℝ) (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 2)) (dyadicScale (n 3)) hZ hf hq hu1 hv hH hK ha hc hd
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    ((Ideal.span {commonFrequencyGenerator C D}).absNorm:ℝ) hg hgc hs hl hr

theorem actual_capacity_shift_reference_right (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K H a Z qref:ℝ)(n:Fin 4→ℤ)
    (hq:0< qref)(hK:0< K)(hH:0< H)(ha:0< a)(hZ:1< Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(I.absNorm:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (H/(D.absNorm:ℝ))-Real.logb Z (adjustedEnvelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z H+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)):=by
  have hc:=CenteredMomentFirstScale.norm_pos C hC.1
  have hd:=CenteredMomentFirstScale.norm_pos D hD.1
  have hg:=CenteredMomentFirstScale.norm_pos (Ideal.span {commonFrequencyGenerator C D})
    (Ideal.span_singleton_eq_bot.not.mpr (commonFrequencyGenerator_ne_zero C D hC))
  have hv:=CenteredMomentFirstScale.norm_pos (Ideal.span {nonunitFrequencyGenerator C D U})
    (Ideal.span_singleton_eq_bot.not.mpr (nonunitFrequencyGenerator_ne_zero C D hC U))
  have hu:=common_product_pos C D hC U
  have hu1:1≤((∏P∈U,P.val).absNorm:ℝ):=by exact_mod_cast (show 1≤(∏P∈U,P.val).absNorm from by exact_mod_cast hu)
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hdiv:Ideal.span {commonFrequencyGenerator C D}∣D:=by
    have hh:=Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (commonFrequencyGenerator_dvd C D hC hD hCD).2
    simpa only [primary_span_supported D hD] using hh
  have hgc:=CenteredMomentFirstSourceConductorCaps.divisor_norm_le _ D hD.1 hdiv
  have hh:=physicalBlock_scale_lower η t S β C D hC hD U R rows W K n a H ha hlower hne
  have hl:a*H/(C.absNorm:ℝ)≤ dyadicScale (n 2):=by
    have hv':=(le_div_iff₀ ha).mp hh.1
    convert hv' using 1 <;> first | rfl | ring
  have hr:a*H/(D.absNorm:ℝ)≤ dyadicScale (n 3):=by
    have hv':=(le_div_iff₀ ha).mp hh.2
    convert hv' using 1 <;> first | rfl | ring
  have hs:=effective_upper η t S β C D hC hD U R rows W K n hne
  have he:secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)*
        Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U})/((C.absNorm:ℝ)*D.absNorm):=by
    simp only [secondEffectiveScale,map_mul,norm_mul,mul_pow,
      ringComplex_norm_sq_eq_absNorm_span]
    ring
  rw [he] at hs
  have hs':dyadicScale (n 0)≤4*(K*(Ideal.span {commonFrequencyGenerator C D}).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm/((D.absNorm:ℝ)*C.absNorm)):=by
    simpa only [mul_comm (C.absNorm:ℝ) (D.absNorm:ℝ)] using hs
  have hh':=scalar_capacity_shift Z (fixedFactor:ℝ) qref
    ((∏P∈U,P.val).absNorm:ℝ) ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ)
    H K a (D.absNorm:ℝ) (C.absNorm:ℝ) (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 3)) (dyadicScale (n 2)) hZ hf hq hu1 hv hH hK ha hd hc
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    ((Ideal.span {commonFrequencyGenerator C D}).absNorm:ℝ) hg hgc hs' hr hl
  simpa only [adjustedEnvelopeRef,mul_comm (dyadicScale (n 3)) (dyadicScale (n 2))] using hh'

theorem actual_capacity_shift (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K H a Z:ℝ)(n:Fin 4→ℤ)
    (hK:0< K)(hH:0< H)(ha:0< a)(hZ:1< Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(I.absNorm:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (H/(C.absNorm:ℝ))-Real.logb Z (adjustedEnvelope η C D U n)≤
      Real.logb Z K-Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z H+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)):=
  actual_capacity_shift_reference η t S β C D hC hD hCD U R rows W K H a Z
    (η.modulus.absNorm:ℝ) n (CenteredMomentFirstScale.norm_pos η.modulus η.modulus_ne_bot)
    hK hH ha hZ hlower hne

end CenteredMomentSecondCapacitySourceShift

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstAmplifiedCapacityCommon
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn
open CenteredMomentSecondCapacitySourceShift CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondNonexceptionalScalar
open CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondPhysicalCost CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentAllocatedChildCapacity CenteredMomentFirstScale
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def envelopeRef (qref:ℝ)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  (fixedFactor:ℝ)*qref*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)

lemma envelope_pos (qref:ℝ)(hq:0< qref)(C D:Ideal O)(hC:Supported C)
    (U:Finset (CommonIndex C D))(n:Fin 4→ℤ):0< envelopeRef qref C D U n:=by
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hu:=CenteredMomentSecondPhysicalLedger.common_product_pos C D hC U
  have hv:=norm_pos (Ideal.span {nonunitFrequencyGenerator C D U})
    (Ideal.span_singleton_eq_bot.not.mpr (nonunitFrequencyGenerator_ne_zero C D hC U))
  have hn:=dyadicScale_pos (n 1)
  unfold envelopeRef
  positivity

lemma adjusted_log (Z qref:ℝ)(hq:0< qref)(C D:Ideal O)(hC:Supported C)
    (U:Finset (CommonIndex C D))(n:Fin 4→ℤ):
    Real.logb Z (adjustedEnvelopeRef qref C D U n)=
      Real.logb Z (envelopeRef qref C D U n)+Real.logb Z (ratioPenalty n):=by
  exact Real.logb_mul (envelope_pos qref hq C D hC U n).ne'
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).ne'

theorem common_raw_reference_shift (s:Input ι)(υ:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (B:actualAllocations s.pools C)(hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K a Z qref:ℝ)(n:Fin 4→ℤ)(hq:0< qref)(hK:0< K)(ha:0< a)(hZ:1< Z)
    (hlower:∀I:Ideal O,β I≠0→a*volume s≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s υ t) C R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
        (Fintype.card ι:ℝ)*Real.logb Z (max 1 s.upper)+Real.logb Z (ratioPenalty n) := by
  have hg:=actual_capacity_shift_reference υ t S β C D hC hD hCD U R rows W K
    (volume s) a Z qref n hq hK (volume_pos s) ha hZ hlower hne
  have hu:=common_volume_le (Fintype.card ι) (max 1 s.upper) (le_max_left _ _) s
    le_rfl (le_max_right _ _) C R0 B υ t hB
  have hc:=norm_pos C hC.1
  have hl:=Real.logb_le_logb_of_le hZ (volume_pos (child s C R0 B υ t)) hu
  have hb:0< max 1 s.upper:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [Real.logb_div (mul_pos (pow_pos hb _) (volume_pos s)).ne' hc.ne',
    Real.logb_mul (pow_pos hb _).ne' (volume_pos s).ne',Real.logb_pow] at hl
  rw [adjusted_log Z qref hq C D hC U n,Real.logb_div (volume_pos s).ne' hc.ne'] at hg
  have he:preVolume (commonData (withHeight s υ t) C R0 B)=volume (child s C R0 B υ t):=rfl
  rw [he]
  linarith

theorem common_raw_reference_shift_right (s:Input ι)(υ:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (B:actualAllocations s.pools D)(hB:frozenCoefficient B.val D R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K a Z qref:ℝ)(n:Fin 4→ℤ)(hq:0< qref)(hK:0< K)(ha:0< a)(hZ:1< Z)
    (hlower:∀I:Ideal O,β I≠0→a*volume s≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s υ t) D R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
        (Fintype.card ι:ℝ)*Real.logb Z (max 1 s.upper)+Real.logb Z (ratioPenalty n) := by
  have hg:=actual_capacity_shift_reference_right υ t S β C D hC hD hCD U R rows W K
    (volume s) a Z qref n hq hK (volume_pos s) ha hZ hlower hne
  have hu:=common_volume_le (Fintype.card ι) (max 1 s.upper) (le_max_left _ _) s
    le_rfl (le_max_right _ _) D R0 B υ t hB
  have hc:=norm_pos D hD.1
  have hl:=Real.logb_le_logb_of_le hZ (volume_pos (child s D R0 B υ t)) hu
  have hb:0< max 1 s.upper:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [Real.logb_div (mul_pos (pow_pos hb _) (volume_pos s)).ne' hc.ne',
    Real.logb_mul (pow_pos hb _).ne' (volume_pos s).ne',Real.logb_pow] at hl
  rw [adjusted_log Z qref hq C D hC U n,Real.logb_div (volume_pos s).ne' hc.ne'] at hg
  have he:preVolume (commonData (withHeight s υ t) D R0 B)=volume (child s D R0 B υ t):=rfl
  rw [he]
  linarith

theorem actual_width_le_reference {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayFourExpansion.RayCharacter→Character}
    (hf:Family η C D hC hD U τ)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (qref Z:ℝ)(hq:(η.modulus.absNorm:ℝ)≤ qref)(hZ:1< Z)(χ:RayFourExpansion.RayCharacter):
    Real.logb Z ((τ χ).modulus.absNorm:ℝ)+Real.logb Z (dyadicScale (n 1))≤
      Real.logb Z (envelopeRef qref C D U n) := by
  have hqpos:=norm_pos (τ χ).modulus (τ χ).modulus_ne_bot
  have he:=family_child_envelope hf t S β R rows W K hK n hne χ
  have hb:childEnvelope η C D U n≤ envelopeRef qref C D U n:=by
    unfold childEnvelope envelopeRef
    gcongr
    exact (dyadicScale_pos _).le
  have hh:=Real.logb_le_logb_of_le hZ (mul_pos hqpos (dyadicScale_pos _)) (he.trans hb)
  rwa [Real.logb_mul hqpos.ne' (dyadicScale_pos _).ne'] at hh

end CenteredMomentFirstAmplifiedCapacityCommon

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentDescentLedger
open CanonicalQuadraticSieve CenteredMomentSecondLedger CenteredMomentPartitionNorm
local notation "O" => Eisenstein.O

def firstSaving (c D₀ w q wo B g ell : ℝ) : ℝ :=
  c/6+5*D₀/6+w/3+q/6+wo+B-5*g/6+ell

theorem firstSaving_lower (c d D₀ w q R wo B g ell σ δ : ℝ)
    (hc : 0 ≤ c) (hw : 0 ≤ w) (hq : 0 ≤ q) (hwo : 0 ≤ wo)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hδ : 0 ≤ δ)
    (hR : R ≤ q) (hBcost : max (3*c-5*d-R) 0/6 ≤ B)
    (hD : d-δ ≤ D₀) (hg : g ≤ max (D₀-c-2*w+wo) 0+2*σ)
    (hell : 0 ≤ ell) (hwσ : w ≤ 7*σ/3) :
    2*(c+w)/3-3*σ-5*δ/6 ≤ firstSaving c D₀ w q wo B g ell := by
  have hraw : 3*c-5*d-R ≤ 6*B := by
    have hm := le_max_left (3*c-5*d-R) 0
    linarith
  have hmax : max (3*c-5*D₀) 0/6-5*δ/6 ≤ B+q/6 := by
    apply (max_le_iff.mpr ⟨?_,?_⟩ : max (3*c-5*D₀) 0 ≤ 6*(B+q/6)+5*δ) |> fun h => by linarith
    · linarith
    · positivity
  unfold firstSaving
  by_cases hJ : 0 ≤ D₀-c-2*w+wo
  · rw [max_eq_left hJ] at hg
    linarith
  · rw [max_eq_right (le_of_not_ge hJ)] at hg
    have hm := le_max_left (3*c-5*D₀) 0
    linarith

section ActualSecond
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem common_log_ge_unit (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm (unitIdeal p U) : ℝ) ≤
      Real.logb Z (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  rw [unitIdeal,log_norm_radical p hp,commonIdeal,log_norm_power_product p hp]
  calc
    _ ≤ ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      intro i hi hni
      apply Real.logb_nonneg hZ
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hn : 0 ≤ Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
        Real.logb_nonneg hZ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))
      have hm : (1:ℝ) ≤ (min (c i) (d i) : ℕ) := by exact_mod_cast le_min (hc i) (hd i)
      nlinarith

omit [DecidableEq ι] in
theorem half_product_log_ge_radical (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ) ≤
      (Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ)+
       Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ))/2 := by
  rw [log_norm_radical p hp,log_norm_power_product p hp,log_norm_power_product p hp,
    ← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  have hn : 0 ≤ Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
    Real.logb_nonneg hZ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))
  have hcr : (1:ℝ) ≤ c i := by exact_mod_cast hc i
  have hdr : (1:ℝ) ≤ d i := by exact_mod_cast hd i
  nlinarith
end ActualSecond

theorem child_allowance_lower (b₂ p₂ w B ell : ℝ)
    (hbp : p₂ ≤ b₂) (hB : 0 ≤ B) :
    w+ell ≤ b₂-p₂+w+B+ell := by linarith

theorem exceptional_excess_identity
    (A m q c d R E K w wo B g ell b₂ p₂ g₂ t₂ V f : ℝ) :
    let a₀ := A-c-w
    let K₀ := 2*A-c-d+R+E-m
    let m' := 2*a₀-K-g-g₂-V
    let q' := q+R+E+wo+t₂+V
    (m'-f)/6+a₀-b₂-(m'+q'+(b₂-p₂+w+B+ell)) =
      A-5*(m+q)/6-firstSaving c (d+K₀-K) w (q+R+E) wo B g ell -
        (2*b₂-5*g₂/6-p₂+t₂+V/6+f/6) := by
  dsimp only [firstSaving]
  ring

theorem inner_allowance_identity
    (a₀ q wo w B s₀ K g ell p₂ g₂ t₂ b₂ V : ℝ) :
    (a₀+q+wo+w+B-s₀)-(K+g-ell-a₀+p₂-s₀+g₂-t₂-b₂) =
      (2*a₀-K-g-g₂-V)+(q+wo+t₂+V)+(b₂-p₂+w+B+ell) := by ring

theorem exceptional_excess_bound
    (A M c w b₂ F₁ F₂ σ δ : ℝ)
    (hF₁ : 2*(c+w)/3-3*σ-5*δ/6 ≤ F₁)
    (hF₂ : 2*b₂/3 ≤ F₂) :
    A-5*M/6-F₁-F₂ ≤ A-5*M/6-2*(c+w+b₂)/3+3*σ+5*δ/6 := by linarith

theorem uncentered_exceptional_bound
    (A M c w b₂ F₁ F₂ σ δ : ℝ)
    (hA : A ≤ 5*M/6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb : 0 ≤ b₂)
    (hF₁ : 2*(c+w)/3-3*σ-5*δ/6 ≤ F₁)
    (hF₂ : 2*b₂/3 ≤ F₂) :
    A-5*M/6-F₁-F₂ ≤ 3*σ+5*δ/6 := by
  have hh := exceptional_excess_bound A M c w b₂ F₁ F₂ σ δ hF₁ hF₂
  linarith

end CenteredMomentDescentLedger

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

namespace CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon

lemma exceptional_core_nominal (K V E R C D A : ℝ)
    (hK:0< K)(hV:0< V)(hE:0< E)(hR:0< R)(hC:0< C)(hD:0< D)(hA:0< A):
    K*Real.sqrt (C*D)/(E*Real.sqrt R*V^2)*
      (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*A^((5:ℝ)/6) =
    V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(E^((1:ℝ)/6)*C*D)*
      (A/(E*R*V^2/(K*C*D)))^((5:ℝ)/6) := by
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi]; positivity
  · simp only [Set.mem_Ioi]; positivity
  · simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_rpow,
      Real.log_sqrt,Real.log_pow]
    ring

lemma amplified_nominal_ratio (Z T j g : ℝ)(hZ:1< Z)(hT:0< T):
    (Z^(j+g)/T)^((5:ℝ)/6)=Z^(5*(j-Real.logb Z T+g)/6) := by
  have hz:0< Z:=zero_lt_one.trans hZ
  rw [show j-Real.logb Z T+g=j+g-Real.logb Z T by ring]
  rw [show 5*(j+g-Real.logb Z T)/6=(j+g-Real.logb Z T)*((5:ℝ)/6) by ring,
    Real.rpow_mul hz.le,Real.rpow_sub hz,Real.rpow_logb hz (ne_of_gt hZ) hT]

theorem exceptional_core_log (K V E R C D Z j g : ℝ)
    (hK:0< K)(hV:0< V)(hE:0< E)(hR:0< R)(hC:0< C)(hD:0< D)(hZ:1< Z):
    K*Real.sqrt (C*D)/(E*Real.sqrt R*V^2)*
      (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6) =
    V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(E^((1:ℝ)/6)*C*D)*
      Z^(5*(j-Real.logb Z (E*R*V^2/(K*C*D))+g)/6) := by
  rw [exceptional_core_nominal K V E R C D (Z^(j+g)) hK hV hE hR hC hD
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)]
  rw [amplified_nominal_ratio Z _ j g hZ (by positivity)]

theorem scalar_exceptional_bound (s μ H K V E R C D Z j g : ℝ)
    (hK:0< K)(hV:0< V)(hE:0< E)(hR:0< R)(hC:0< C)(hD:0< D)(hZ:1< Z)
    (hs:s*V≤μ*H*K*Real.sqrt (C*D)/(E*Real.sqrt R)):
    s/V*(V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6) ≤
    μ*H*(V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(E^((1:ℝ)/6)*C*D)*
      Z^(5*(j-Real.logb Z (E*R*V^2/(K*C*D))+g)/6)) := by
  have hdiv:=div_le_div_of_nonneg_right hs (sq_nonneg V)
  have he:s*V/V^2=s/V:=by field_simp
  rw [he] at hdiv
  calc
    _≤(μ*H*K*Real.sqrt (C*D)/(E*Real.sqrt R)/V^2)*
        (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6):=by
      gcongr
    _=μ*H*(K*Real.sqrt (C*D)/(E*Real.sqrt R*V^2)*
        (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)):=by ring
    _=_:=by rw [exceptional_core_log K V E R C D Z j g hK hV hE hR hC hD hZ]

theorem actual_nominal_cancellation
    (I J E : Ideal Eisenstein.O) (hE:E≠0)
    (K V Z j g : ℝ)(hK:0< K)(hV:0< V)(hZ:1< Z):
    let C : ℝ := (commonPart I J).absNorm;
    let D : ℝ := (commonPart J I).absNorm;
    let N : ℝ := E.absNorm;
    let R : ℝ := (Ideal.span {activeConductor I J}).absNorm;
    K*Real.sqrt (C*D)/(N*Real.sqrt R*V^2)*
      (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6) =
    V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(N^((1:ℝ)/6)*C*D)*
      Z^(5*(j-Real.logb Z (firstNominalScale I J E K V)+g)/6) := by
  exact exceptional_core_log K V _ _ _ _ Z j g hK hV (norm_pos E hE)
    (active_norm_pos I J) (norm_pos _ (commonPart_ne_zero I J))
    (norm_pos _ (commonPart_ne_zero J I)) hZ

end CenteredMomentFirstExceptionalPrefactor

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstExceptionalPrefactor
open Eisenstein   CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
open CenteredMomentFirstNonexceptionalPrefactor CenteredMomentFirstScale 
local notation "O"=> Eisenstein.O

lemma commonPart_of_equal_support (C D:Ideal O)(hC:C≠0)
    (hCD:primeSupport C=primeSupport D):commonPart C D=C := by
  have he:commonPart C D=commonPart C C:=by
    simp only [commonPart,commonSupport,←hCD]
  exact he.trans (commonPart_self C hC)

lemma nominal_equal_support (C D E:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D)(K V:ℝ):
    firstNominalScale C D E K V=
      (E.absNorm:ℝ)*(Ideal.span {activeConductor C D}).absNorm*V^2/
        (K*(C.absNorm:ℝ)*D.absNorm) := by
  rw [firstNominalScale,commonPart_of_equal_support C D hC hCD,
    commonPart_of_equal_support D C hD hCD.symm]

theorem actual_scalar_exceptional (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K A₀ B₀ a V M Z j g:ℝ)(hK:0< K)(hA:0< A₀)(hB:0< B₀)
    (ha:0< a)(hV:0< V)(hZ:1< Z)
    (hl:a*V≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*V≤(D.absNorm:ℝ)*Real.exp M*B₀):
    let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E;
    let NE:ℝ:=(Ideal.span {e}).absNorm;
    let NR:ℝ:=(Ideal.span {activeConductor C D}).absNorm;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (V/(C.absNorm:ℝ))^((2:ℝ)/3)*(V/(D.absNorm:ℝ))^((2:ℝ)/3)*
        (Z^(j+g))^((5:ℝ)/6) ≤
    ‖inactiveWeight C D E‖*(Real.exp M/a)*
      (V*K^((1:ℝ)/6)*NR^((1:ℝ)/3)/(NE^((1:ℝ)/6)*(C.absNorm:ℝ)*D.absNorm)*
        Z^(5*(j-Real.logb Z (firstNominalScale C D (Ideal.span {e}) K V)+g)/6)) := by
  dsimp only
  have hNE:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hNR:=active_norm_pos C D
  have hNC:=norm_pos C hC.1
  have hND:=norm_pos D hD.1
  have hroot:Real.sqrt ((Ideal.span {activeConductor C D}).absNorm:ℝ)=
      ‖ringComplex (activeConductor C D)‖:=by
    rw [←ringComplex_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)]
  have hs:=weighted_scalar_volume C D hC E K A₀ B₀ a V M hK hA hB ha hV hl hr
  rw [ringComplex_norm_sq_eq_absNorm_span,←hroot] at hs
  have hh:=scalar_exceptional_bound _ _ (Real.exp M/a) K V _ _ _ _ Z j g
    hK hV hNE hNR hNC hND hZ hs
  rw [nominal_equal_support C D _ hC.1 hD.1 hCD K V]
  exact hh

open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentSupportedCorrelation

theorem original_scalar_exceptional {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0< a₁)(ha₂:0< a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤ x)(hs₂:∀x,s.W₂ x≠0→a₂≤ x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z j g:ℝ)(hK:0< K)(hA:0< A₀)(hB:0< B₀)(hZ:1< Z)
    (hwin:∀i y,U i y≠0→|y|≤ M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E;
    let NE:ℝ:=(Ideal.span {e}).absNorm;
    let NR:ℝ:=(Ideal.span {activeConductor C D}).absNorm;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (V/(C.absNorm:ℝ))^((2:ℝ)/3)*(V/(D.absNorm:ℝ))^((2:ℝ)/3)*
        (Z^(j+g))^((5:ℝ)/6) ≤
    ‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*
      (V*K^((1:ℝ)/6)*NR^((1:ℝ)/3)/(NE^((1:ℝ)/6)*(C.absNorm:ℝ)*D.absNorm)*
        Z^(5*(j-Real.logb Z (firstNominalScale C D (Ideal.span {e}) K V)+g)/6)) := by
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=> s.lo_pos i)) ha₁) ha₂
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W U
    K K₀ H₀ A₀ B₀ ((∏i,s.lo i)*a₁*a₂) (volume s.toData) M hA hB
    (fun I hi=> original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  exact actual_scalar_exceptional C D hC hD hCD E K A₀ B₀ _ _ M Z j g
    hK hA hB ha (volume_pos s.toData) hZ hl hr

end CenteredMomentFirstExceptionalPrefactor

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentAmplifiedRetainedRadius
open HeckeFamily CanonicalQuadraticSieve 
open CenteredMomentFirstAmplificationChoice CenteredMomentGaussEnergy
open CenteredMomentSmoothedWindowEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentGaussNormalization
local notation "O" => Eisenstein.O

theorem ballProfile_radius_le (x Y V : ℝ) (hx : 0≤ x) (hY : 0< Y) (hV : 0< V)
    (hscale : 2*Y≤ V) : (ballProfile (x/Y)).re≤(ballProfile (x/V)).re := by
  by_cases hz : ballProfile (x/Y)=0
  · simpa only [hz,Complex.zero_re] using ballProfile_nonneg (x/V)
  have hs := ballProfile_support_upper (x/Y) (div_nonneg hx hY.le) hz
  have hxy : x≤ V := ((div_lt_iff₀ hY).mp hs).le.trans hscale
  rw [ballProfile_one (x/V) (div_nonneg hx hV.le) ((div_le_one hV).mpr hxy)]
  exact ballProfile_le_one _

theorem gaussEnergy_radius_le {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (Y V : ℝ) (hY : 0< Y) (hV : 0< V) (hscale : 2*Y≤ V) :
    (gaussEnergy S a ha c ballProfile Y).re≤(gaussEnergy S a ha c ballProfile V).re := by
  have h1 := gaussEnergy_hasSum_re S a ha c ballProfile Y hY
  have h2 := gaussEnergy_hasSum_re S a ha c ballProfile V hV
  rw [←h1.tsum_eq,←h2.tsum_eq]
  apply Summable.tsum_le_tsum _ h1.summable h2.summable
  intro z
  exact mul_le_mul_of_nonneg_left
    (ballProfile_radius_le _ Y V (sq_nonneg _) hY hV hscale) (sq_nonneg _)

theorem sourceGaussEnergy_radius_le (Q : Finset (Ideal O)) (c f : Ideal O→ℂ)
    (Y V : ℝ) (hY : 0< Y) (hV : 0< V) (hscale : 2*Y≤ V) :
    (sourceGaussEnergy Q c f ballProfile Y).re≤(sourceGaussEnergy Q c f ballProfile V).re :=
  gaussEnergy_radius_le _ _ _ _ Y V hY hV hscale

theorem childEnergy_radius_le {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (τ : RayFourExpansion.RayCharacter→Character) (p : O) (n : ℕ)
    (t T Y V : ℝ) (hT : 0≤ T) (hY : 0< Y) (hV : 0< V) (hscale : 2*Y≤ V) :
    D.childEnergy τ p n t T Y≤ D.childEnergy τ p n t T V := by
  unfold OriginalData.childEnergy
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by positivity) (localErrorCost_nonneg p n))
  apply div_le_div_of_nonneg_right _ (div_nonneg hT (by positivity))
  apply Finset.sum_le_sum
  intro χ _
  apply Finset.sum_le_sum
  intro B _
  exact sourceGaussEnergy_radius_le _ _ _ Y V hY hV hscale

lemma exponent_max (d K0 j c g : ℝ) :
    j+(max (d+K0-j-c) 0+g)=max (j+g) (d+K0-c+g) := by
  by_cases h : d+K0-j-c≤0
  · rw [max_eq_right h,max_eq_left (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_right (by linarith)]
    ring

lemma rpow_exponent_max (Z a b : ℝ) (hZ : 1≤ Z) :
    Z^(max a b)=max (Z^a) (Z^b) := by
  rcases le_total a b with h|h
  · rw [max_eq_right h,max_eq_right (Real.rpow_le_rpow_of_exponent_le hZ h)]
  · rw [max_eq_left h,max_eq_left (Real.rpow_le_rpow_of_exponent_le hZ h)]

theorem main_radius_identity (Z d K0 j c sigma : ℝ) (hZ : 1≤ Z) :
    Z^(j+mainGain (d+K0-j) c sigma)=
      max (Z^(j+2*sigma)) (Z^(d+K0-c+2*sigma)) := by
  rw [mainGain,exponent_max,rpow_exponent_max Z _ _ hZ]

theorem error_radius_identity (Z d K0 j c sigma : ℝ) (p : O) (k : ℕ) (hZ : 1≤ Z) :
    Z^(j+errorGain (d+K0-j) c sigma Z p k)=
      max (Z^(j+sigma))
        (Z^(d+K0-c-2*errorRemoval p Z k+errorMoving p Z k+sigma)) := by
  have he := exponent_max d K0 j (c+2*errorRemoval p Z k-errorMoving p Z k) sigma
  have hbase : j+errorGain (d+K0-j) c sigma Z p k=
      max (j+sigma) (d+K0-c-2*errorRemoval p Z k+errorMoving p Z k+sigma) := by
    unfold errorGain
    convert he using 1 <;> first | rfl | ring_nf
  rw [hbase,rpow_exponent_max Z _ _ hZ]

lemma envelope_exponent (d K0 j c g δ : ℝ) (hδ : 0≤δ) (hj : j≤ K0+δ) :
    j+(max (d+K0-j-c) 0+g)≤ K0+max (d-c) 0+g+δ := by
  rw [exponent_max]
  apply max_le
  · linarith [le_max_right (d-c) (0:ℝ)]
  · linarith [le_max_left (d-c) (0:ℝ)]

theorem main_exponent_envelope (d K0 j c sigma δ : ℝ) (hδ : 0≤δ) (hj : j≤ K0+δ) :
    j+mainGain (d+K0-j) c sigma≤ K0+max (d-c) 0+2*sigma+δ :=
  envelope_exponent d K0 j c (2*sigma) δ hδ hj

theorem error_exponent_envelope (d K0 j c sigma δ Z : ℝ) (p : O) (k : ℕ)
    (hδ : 0≤δ) (hj : j≤ K0+δ) :
    j+errorGain (d+K0-j) c sigma Z p k≤
      K0+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+δ := by
  have he := envelope_exponent d K0 j (c+2*errorRemoval p Z k-errorMoving p Z k) sigma δ hδ hj
  unfold errorGain
  convert he using 1 <;> first | rfl | ring_nf

theorem eventually_support_reserve (reserve : ℝ) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ 2≤ Z^reserve := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hreserve).eventually (eventually_ge_atTop (2:ℝ))] with Z hZ hpow
  exact ⟨hZ,hpow⟩

lemma doubled_radius_le (Z a b reserve : ℝ) (hZ : 1< Z) (hab : a≤ b)
    (hreserve : 2≤ Z^reserve) : 2*Z^a≤ Z^(b+reserve) := by
  rw [Real.rpow_add (zero_lt_one.trans hZ)]
  calc
    _≤2*Z^b := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hab) (by norm_num)
    _≤ Z^b*Z^reserve := by
      rw [mul_comm (Z^b)]
      exact mul_le_mul_of_nonneg_right hreserve (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

theorem unamplified_radius_identity (Z d K0 j c sigma : ℝ) (hZ : 1≤ Z) :
    Z^(j+(max (d+K0-j-c) 0+sigma))=
      max (Z^(j+sigma)) (Z^(d+K0-c+sigma)) := by
  rw [exponent_max,rpow_exponent_max Z _ _ hZ]

def mainCommonRadius (Z d K0 c sigma δ reserve : ℝ) : ℝ :=
  Z^(K0+max (d-c) 0+2*sigma+δ+reserve)

def errorCommonRadius (Z d K0 c sigma δ reserve : ℝ) (p : O) (k : ℕ) : ℝ :=
  Z^(K0+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+δ+reserve)

theorem main_energy_common {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (coeff : α→ℂ)
    (Z d K0 j c sigma δ reserve : ℝ) (hZ : 1< Z) (hδ : 0≤δ)
    (hj : j≤ K0+δ) (hreserve : 2≤ Z^reserve) :
    (gaussEnergy S a ha coeff ballProfile (Z^(j+mainGain (d+K0-j) c sigma))).re≤
      (gaussEnergy S a ha coeff ballProfile (mainCommonRadius Z d K0 c sigma δ reserve)).re := by
  apply gaussEnergy_radius_le _ _ _ _ _ _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (main_exponent_envelope d K0 j c sigma δ hδ hj) hreserve

theorem child_energy_common {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (τ : RayFourExpansion.RayCharacter→Character) (p : O) (n : ℕ)
    (t T Z d K0 j c sigma δ reserve : ℝ) (hT : 0≤ T) (hZ : 1< Z) (hδ : 0≤δ)
    (hj : j≤ K0+δ) (hreserve : 2≤ Z^reserve) :
    D.childEnergy τ p n t T (Z^(j+errorGain (d+K0-j) c sigma Z p (n+1)))≤
      D.childEnergy τ p n t T (errorCommonRadius Z d K0 c sigma δ reserve p (n+1)) := by
  apply childEnergy_radius_le D τ p n t T _ _ hT
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (error_exponent_envelope d K0 j c sigma δ Z p (n+1) hδ hj) hreserve

theorem errorCommonRadius_six (Z d K0 c sigma δ reserve : ℝ) (p : O) :
    errorCommonRadius Z d K0 c sigma δ reserve p 6=
      Z^(K0+max (d-c-2*errorRemoval p Z 6) 0+sigma+δ+reserve) := by
  simp only [errorCommonRadius,errorMoving,ite_true,add_zero]

open CenteredMomentFirstScale

theorem retained_nominal_upper (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi : ℝ) (hK : 0< K) (hX : 0< X) (hZ : 1< Z)
    (hC : 0< Csec) (hsec : Tsec≤ Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) :
    Real.logb Z (dyadicScale n)≤ nominalLog I J E K X Z+frequencyLoss Z Csec xi := by
  apply retained_first_dyad_enclosure Tsec Z Csec (nominalLog I J E K X Z) xi hZ hC _ n hn
  rw [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
    (firstNominalScale_pos I J E hE K X hK hX)]
  exact hsec

theorem actual_retained_radii (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi d c sigma reserve : ℝ)
    (hK : 0< K) (hX : 0< X) (hZ : 1< Z) (hC : 1≤ Csec) (hxi : 0≤ xi)
    (hsec : Tsec≤ Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) (hreserve : 2≤ Z^reserve) :
    let K0 := nominalLog I J E K X Z
    let j := Real.logb Z (dyadicScale n)
    let δ := frequencyLoss Z Csec xi
    2*Z^(j+mainGain (d+K0-j) c sigma)≤ mainCommonRadius Z d K0 c sigma δ reserve ∧
      ∀(p:O)(k:ℕ),2*Z^(j+errorGain (d+K0-j) c sigma Z p k)≤
        errorCommonRadius Z d K0 c sigma δ reserve p k := by
  dsimp only
  have hj := retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn
  have hδ := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  constructor
  · exact doubled_radius_le Z _ _ reserve hZ (main_exponent_envelope _ _ _ _ _ _ hδ hj) hreserve
  · intro p k
    exact doubled_radius_le Z _ _ reserve hZ (error_exponent_envelope _ _ _ _ _ _ Z p k hδ hj) hreserve


end CenteredMomentAmplifiedRetainedRadius

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentCommonRadiusSaving
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentDescentLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical  Eisenstein
local notation "O" => Eisenstein.O

theorem common_saving_identity (c d x w q wo B sigma branch delta reserve ell : ℝ) :
    firstSaving c (d+x) w q wo B
      (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell =
      c/6+5*d/6+w/3+q/6+wo+B-5*max (d-c-2*w+wo) 0/6-
        5*branch*sigma/6-5*(delta+reserve)/6+ell := by
  unfold firstSaving
  ring

theorem common_saving_lower (c d x w q wo B sigma branch delta reserve ell : ℝ)
    (hc : 0≤ c) (hw : 0≤ w) (hq : 0≤ q) (hwo : 0≤ wo) (hB : 0≤ B)
    (hallow : 3*c-5*d≤6*B+q) :
    2*(c+w)/3-max (w/3-wo) 0-5*branch*sigma/6-5*(delta+reserve)/6+ell≤
      firstSaving c (d+x) w q wo B
        (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell := by
  rw [common_saving_identity]
  have hm0 := le_max_right (w/3-wo) (0:ℝ)
  have hm1 := le_max_left (w/3-wo) (0:ℝ)
  by_cases h : 0≤ d-c-2*w+wo
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

theorem main_saving_lower (c d x q B sigma delta reserve : ℝ)
    (hc : 0≤ c) (hq : 0≤ q) (hB : 0≤ B) (hallow : 3*c-5*d≤6*B+q) :
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+x) 0 q 0 B
        (x+max (d-c) 0+2*sigma+delta+reserve) (sigma/3) := by
  have hh := common_saving_lower c d x 0 q 0 B sigma 2 delta reserve (sigma/3)
    hc (by norm_num) hq (by norm_num) hB hallow
  norm_num only [zero_div,sub_zero,add_zero,mul_zero,max_self] at hh
  linarith

theorem error_penalty_le (l sigma : ℝ) (hl : 0≤ l) (hu : l≤ sigma/3)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    max (((k:ℝ)*l)/3-(if k=6 then 0 else l)) 0≤2*sigma/3 := by
  rcases hk with rfl|rfl|rfl <;> norm_num only [Nat.cast_ofNat,ite_false,ite_true,
    one_mul,sub_zero] <;> apply max_le <;> linarith

def errorLoss (sigma : ℝ) (k : ℕ) : ℝ :=
  if k=1 then 5*sigma/6 else if k=6 then 3*sigma/2 else 23*sigma/18

theorem error_penalty_refined (l sigma : ℝ) (hl : 0≤ l) (hu : l≤ sigma/3)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    max (((k:ℝ)*l)/3-(if k=6 then 0 else l)) 0+5*sigma/6≤ errorLoss sigma k := by
  have hs : 0≤ sigma := by linarith
  rcases hk with rfl|rfl|rfl
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_one,one_mul]
    have hm : max (l/3-l) 0=0 := max_eq_right (by linarith)
    rw [hm,zero_add]
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_ofNat,sub_zero]
    have hm : max (6*l/3) 0≤2*sigma/3 := max_le (by linarith) (by linarith)
    linarith
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_ofNat]
    have hm : max (7*l/3-l) 0≤4*sigma/9 := max_le (by linarith) (by linarith)
    linarith

theorem errorLoss_le (sigma : ℝ) (hs : 0≤ sigma) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7) : errorLoss sigma k≤3*sigma/2 := by
  rcases hk with rfl|rfl|rfl <;> norm_num only [errorLoss,ite_true,ite_false] <;> linarith

theorem error_saving_refined (c d x q B sigma delta reserve l : ℝ)
    (hc : 0≤ c) (hq : 0≤ q) (hB : 0≤ B) (hallow : 3*c-5*d≤6*B+q)
    (hl : 0≤ l) (hu : l≤ sigma/3) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    2*(c+(k:ℝ)*l)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+x) ((k:ℝ)*l) q (if k=6 then 0 else l) B
        (x+max (d-c-2*((k:ℝ)*l)+(if k=6 then 0 else l)) 0+
          sigma+delta+reserve) 0 := by
  have hw : 0≤(k:ℝ)*l := mul_nonneg (Nat.cast_nonneg k) hl
  have hwo : 0≤(if k=6 then (0:ℝ) else l) := by split_ifs <;> linarith
  have hh := common_saving_lower c d x ((k:ℝ)*l) q (if k=6 then 0 else l)
    B sigma 1 delta reserve 0 hc hw hq hwo hB hallow
  simp only [one_mul,add_zero] at hh
  linarith [error_penalty_refined l sigma hl hu k hk]

theorem error_saving_lower (c d x q B sigma delta reserve l : ℝ)
    (hc : 0≤ c) (hq : 0≤ q) (hB : 0≤ B) (hallow : 3*c-5*d≤6*B+q)
    (hl : 0≤ l) (hu : l≤ sigma/3) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    2*(c+(k:ℝ)*l)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+x) ((k:ℝ)*l) q (if k=6 then 0 else l) B
        (x+max (d-c-2*((k:ℝ)*l)+(if k=6 then 0 else l)) 0+
          sigma+delta+reserve) 0 := by
  have hw : 0≤(k:ℝ)*l := mul_nonneg (Nat.cast_nonneg k) hl
  have hwo : 0≤(if k=6 then (0:ℝ) else l) := by split_ifs <;> linarith
  have hh := common_saving_lower c d x ((k:ℝ)*l) q (if k=6 then 0 else l)
    B sigma 1 delta reserve 0 hc hw hq hwo hB hallow
  simp only [one_mul,add_zero] at hh
  linarith [error_penalty_le l sigma hl hu k hk]

theorem common_gain_width (d x c w wo sigma delta reserve branch : ℝ)
    (hs : 0≤ sigma) (hd : 0≤ delta) (hr : 0≤ reserve) (hb : 1≤ branch)
    (hx : -delta≤ x) :
    0≤ x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve ∧
    (d+x)-c-2*w+wo+sigma≤
      x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve := by
  have h0 := le_max_right (d-c-2*w+wo) (0:ℝ)
  have h1 := le_max_left (d-c-2*w+wo) (0:ℝ)
  constructor <;> nlinarith

theorem saving_power_factor (Z F c w sigma delta reserve : ℝ) (hZ : 1≤ Z)
    (hF : 2*(c+w)/3-3*sigma/2-5*(delta+reserve)/6≤ F) :
    Z^(-F)≤ Z^(-2*(c+w)/3+3*sigma/2+5*(delta+reserve)/6) := by
  apply Real.rpow_le_rpow_of_exponent_le hZ
  linarith

theorem main_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1< Z) :
    Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j=
      (K0-j)+max (d-c) 0+2*sigma+delta+reserve := by
  rw [mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

theorem error_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1< Z)
    (p : O) (k : ℕ) :
    Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j=
      (K0-j)+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+
        sigma+delta+reserve := by
  rw [errorCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

theorem canonical_saving_gates (η τ : Character) (m : O)
    (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let q := Real.logb Z (τ.modulus.absNorm:ℝ)
    let B := c+d-2*p-R
    0≤ c ∧ 0≤ q ∧ 0≤ B ∧ 3*c-5*d≤6*B+q := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hh := actual_extracted_common_support_allowance I J hI hJ Z hZ
  dsimp only at hh
  have hc : 0≤ Real.logb Z ((commonPart I J).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J))
  have h0 := le_max_right (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  have h1 := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  have h2 := le_max_right (3*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    5*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  exact ⟨hc,hq.1,by linarith,by linarith [hq.2]⟩

theorem actual_main_common_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3) := by
  dsimp only
  rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  convert main_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    hc hq hB hallow using 1
  congr 1
  ring

theorem actual_error_common_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_error_common_saving_refined (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_refined _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_main_common_factor (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z) (hs : 0≤ sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    Z^(-firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3))≤
      Z^(-2*c/3+3*sigma/2+5*(delta+reserve)/6) := by
  dsimp only
  have hh := actual_main_common_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod
  dsimp only at hh
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

theorem actual_error_common_factor (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    Z^(-firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0)≤
      Z^(-2*(c+errorRemoval p0 Z k)/3+3*sigma/2+5*(delta+reserve)/6) := by
  dsimp only
  have hh := actual_error_common_saving η τ m I J E hI hJ A K X Z j sigma delta reserve
    hZ hmod M H Sbad hbad p0 hp0 k hk
  dsimp only at hh
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

open CenteredMomentFirstScale

theorem actual_common_radius_widths (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi sigma reserve : ℝ)
    (hK : 0< K) (hX : 0< X) (hZ : 1< Z) (hC : 1≤ Csec)
    (hxi : 0≤ xi) (hs : 0≤ sigma) (hr : 0≤ reserve)
    (hsec : Tsec≤ Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    let j := Real.logb Z (dyadicScale n)
    let delta := frequencyLoss Z Csec xi
    let gm := Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j
    (0≤ gm ∧ d+K0-j-c+sigma≤ gm) ∧
    ∀p : O,∀k : ℕ,
      let ge := Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j
      0≤ ge ∧ d+K0-j-c-2*errorRemoval p Z k+errorMoving p Z k+sigma≤ ge := by
  dsimp only
  have hj := retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn
  have hd := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have hx : -frequencyLoss Z Csec xi≤ nominalLog I J E K X Z-Real.logb Z (dyadicScale n) := by
    linarith
  constructor
  · rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
    have hg := common_gain_width
      (Real.logb Z ((commonPart J I).absNorm:ℝ))
      (nominalLog I J E K X Z-Real.logb Z (dyadicScale n))
      (Real.logb Z ((commonPart I J).absNorm:ℝ)) 0 0 sigma
      (frequencyLoss Z Csec xi) reserve 2 hs hd hr (by norm_num) hx
    simp only [mul_zero,sub_zero,add_zero] at hg
    exact ⟨hg.1,by linarith [hg.2]⟩
  · intro p k
    rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
    have hg := common_gain_width
      (Real.logb Z ((commonPart J I).absNorm:ℝ))
      (nominalLog I J E K X Z-Real.logb Z (dyadicScale n))
      (Real.logb Z ((commonPart I J).absNorm:ℝ)) (errorRemoval p Z k) (errorMoving p Z k)
      sigma (frequencyLoss Z Csec xi) reserve 1 hs hd hr (by norm_num) hx
    simp only [one_mul] at hg
    exact ⟨hg.1,by linarith [hg.2]⟩

end CenteredMomentCommonRadiusSaving

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstMixedCommonRadius
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentDescentLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical  Eisenstein
open CenteredMomentFirstMixedAllowance CenteredMomentCommonRadiusSaving
local notation "O" => Eisenstein.O

theorem column_saving_gates (η τ : Character) (m : O)
    (I J : Ideal O) (A : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let q := Real.logb Z (τ.modulus.absNorm:ℝ)
    0≤ c ∧ 0≤ q ∧ 0≤ extractedAllowance I J Z ∧
      3*c-5*d≤6*extractedAllowance I J Z+q := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hc : 0≤ Real.logb Z ((commonPart I J).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J))
  have hm := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  refine ⟨hc,hq.1,?_,?_⟩
  · unfold extractedAllowance; positivity
  · unfold extractedAllowance; linarith [hq.2]

theorem actual_main_column_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (extractedAllowance I J Z)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3) := by
  dsimp only
  rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  convert main_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    hc hq hB hallow using 1
  congr 1
  ring

theorem actual_error_column_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_error_column_saving_refined (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_refined _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

end CenteredMomentFirstMixedCommonRadius

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstMixedNormalization
open CenteredMomentDescentLedger CenteredMomentSectorLocalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
local notation "O" => Eisenstein.O

theorem exceptional_reference_identity (Z V C D NE NR K Q w wo B j g ell:ℝ)
    (hZ:1< Z)(hV:0< V)(hC:0< C)(hD:0< D)(hE:0< NE)(hR:0< NR)(hK:0< K)(hQ:0< Q):
    let c:=Real.logb Z C;
    let d:=Real.logb Z D;
    let q:=Real.logb Z Q;
    let K0:=Real.logb Z (NE*NR*V^2/(K*C*D));
    let M:=Real.logb Z K+q-Real.logb Z NE-Real.logb Z NR;
    (V/C)*Z^(-wo)*(V/C/Z^w)^((1:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)*Z^(-ell)/
      (Q*(V/C)^2*Z^B)=
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) w q wo B g ell):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hzlog:Real.log Z≠0:=ne_of_gt (Real.log_pos hZ)
  dsimp only
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi];positivity
  · simp only [Set.mem_Ioi];positivity
  · simp (disch := positivity) only [Real.log_div,Real.log_mul,Real.log_rpow,Real.log_pow]
    unfold firstSaving Real.logb
    rw [Real.log_div,Real.log_mul,Real.log_mul,Real.log_pow,
      Real.log_mul,Real.log_mul] <;> try positivity
    field_simp
    ; ring

theorem actual_error_weight (p:O)(hp:p≠0)(Z:ℝ)(hZ:1< Z)(k:ℕ)
    (hk:k=1 ∨ k=6 ∨ k=7):
    localErrorCost p (k-1)≤ Z^(-errorMoving p Z k):=by
  have hn:1≤ normValue p:=normValue_ge_one p hp
  have hnpos:0< normValue p:=normValue_pos p hp
  have he:Z^(-(Real.logb Z (normValue p)))=(normValue p)⁻¹:=by
    rw [Real.rpow_neg (zero_lt_one.trans hZ).le,
      Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hnpos]
  rcases hk with rfl|rfl|rfl
  · simpa [localErrorCost,errorMoving,normValue] using he.ge
  · norm_num only [Nat.reduceSub,localErrorCost,errorMoving,ite_true,neg_zero,Real.rpow_zero]
    change (1-(normValue p)⁻¹)^2≤1
    have hi:0≤(normValue p)⁻¹:=inv_nonneg.mpr hnpos.le
    have hu:(normValue p)⁻¹≤1:=inv_le_one_of_one_le₀ hn
    nlinarith
  · simpa [localErrorCost,errorMoving,normValue] using he.ge

end CenteredMomentFirstMixedNormalization

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstMixedNormalizationActual
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedAllowance
open CenteredMomentDescentLedger CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentFirstScale 
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
local notation "O"=> Eisenstein.O

theorem actual_reference_width (η τ:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(K Z:ℝ)(_hK:0< K)(_hZ:1< Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D}):
    Real.logb Z K+Real.logb Z (τ.modulus.absNorm:ℝ)-
      Real.logb Z ((Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)=
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost:=by
  have hE:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR:=active_norm_pos C D
  have hq:=norm_pos _ η.modulus_ne_bot
  have hfixed:=fixedPresentationCost_pos
  rw [fixed_presentation_norm η τ C D E hmod]
  simp only [ringComplex_norm_sq_eq_absNorm_span]
  simp (disch := positivity) only [Real.logb_mul]
  ring

theorem actual_exceptional_reference (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z j g w wo ell:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let q:=Real.logb Z (τ.modulus.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V);
    let M:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost;
    (V/(C.absNorm:ℝ))*Z^(-wo)*(V/(C.absNorm:ℝ)/Z^w)^((1:ℝ)/3)*
      (Z^(j+g))^((5:ℝ)/6)*Z^(-ell)/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))=
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) w q wo (allowance C D Z) g ell):=by
  have hh:=exceptional_reference_identity Z V (C.absNorm:ℝ) (D.absNorm:ℝ)
    ((Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}).absNorm:ℝ)
    ((Ideal.span {activeConductor C D}).absNorm:ℝ) K (τ.modulus.absNorm:ℝ)
    w wo (allowance C D Z) j g ell hZ hV (norm_pos C hC.1) (norm_pos D hD.1)
    (norm_pos _ (subsetGenerator_supported C D hC E).1) (active_norm_pos C D) hK
    (norm_pos _ τ.modulus_ne_bot)
  dsimp only at hh ⊢
  rw [actual_reference_width η τ C D hC E K Z hK hZ hmod] at hh
  rw [nominal_equal_support C D _ hC.1 hD.1 hCD K V]
  exact hh

theorem actual_error_reference_le (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z j g:ℝ)(hK:0< K)(hV:0< V)(hZ:1< Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let q:=Real.logb Z (τ.modulus.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V);
    let M:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost;
    (V/(C.absNorm:ℝ))*localErrorCost p (k-1)*
      (V/(C.absNorm:ℝ)/(normValue p)^k)^((1:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) (errorRemoval p Z k) q
        (errorMoving p Z k) (allowance C D Z) g 0):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hCpos:=norm_pos C hC.1
  have hqpos:=norm_pos _ τ.modulus_ne_bot
  have hnpos:=normValue_pos p hp
  have hh:=actual_exceptional_reference η τ C D hC hD hCD E K V Z j g
    (errorRemoval p Z k) (errorMoving p Z k) 0 hK hV hZ hmod
  dsimp only at hh ⊢
  rw [errorRemoval_power p hp Z hZ k,neg_zero,Real.rpow_zero,mul_one] at hh
  rw [←hh]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (actual_error_weight p hp Z hZ k hk) (by positivity)

end CenteredMomentFirstMixedNormalizationActual

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
