import GaloisForLFunctions.HeckeLFunctions.Characters.ResidueExtensionCount
import GaloisForLFunctions.HeckeLFunctions.HeckeFiniteCharactersHavePrimitiveConductors

/-!
# Class twists preserve all local character data

Multiplying a Hecke character by an ordinary class character changes neither its
finite residue character nor its real sign character. In particular the finite
conductor and every real parity are unchanged. Conversely, two Hecke characters
with the same residue and sign data differ by a unique ordinary class character.
This makes the extension ambiguity in Proposition 3.12 of arXiv:2610.23742 explicit.
-/

noncomputable section
open NumberField
namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- An ordinary class character twists the global Hecke character through `Cl_𝔪 → Cl_K`. -/
def classTwist (ψ : HeckeCharacter 𝔪) (χ : ClassGroup (𝓞 K) →* ℂˣ) : HeckeCharacter 𝔪 :=
  ψ * χ.comp (toClassGroup 𝔪)

/-- Ordinary class characters are invisible to finite residues and real signs. -/
theorem rayResidueCharacter_classTwist (ψ : HeckeCharacter 𝔪)
    (χ : ClassGroup (𝓞 K) →* ℂˣ) :
    rayResidueCharacter 𝔪 (classTwist 𝔪 ψ χ) = rayResidueCharacter 𝔪 ψ := by
  apply MonoidHom.ext
  intro g
  change ψ (fullRayResidueClass 𝔪 g) * χ (toClassGroup 𝔪 (fullRayResidueClass 𝔪 g)) =
    ψ (fullRayResidueClass 𝔪 g)
  have hg : toClassGroup 𝔪 (fullRayResidueClass 𝔪 g) = 1 :=
    (principalRayResidueMap 𝔪 g).property
  rw [hg, map_one, mul_one]

theorem finiteResidueCharacter_classTwist (ψ : HeckeCharacter 𝔪)
    (χ : ClassGroup (𝓞 K) →* ℂˣ) :
    finiteResidueCharacter 𝔪 (classTwist 𝔪 ψ χ) = finiteResidueCharacter 𝔪 ψ := by
  unfold finiteResidueCharacter
  rw [rayResidueCharacter_classTwist]

theorem infiniteSignCharacter_classTwist (ψ : HeckeCharacter 𝔪)
    (χ : ClassGroup (𝓞 K) →* ℂˣ) :
    infiniteSignCharacter 𝔪 (classTwist 𝔪 ψ χ) = infiniteSignCharacter 𝔪 ψ := by
  unfold infiniteSignCharacter
  rw [rayResidueCharacter_classTwist]

/-- Every individual real-place parity is constant throughout a class-character family. -/
theorem heckeParity_classTwist (ψ : HeckeCharacter 𝔪)
    (χ : ClassGroup (𝓞 K) →* ℂˣ) (w : 𝔪.inf) :
    heckeParity 𝔪 (classTwist 𝔪 ψ χ) w = heckeParity 𝔪 ψ w := by
  unfold heckeParity
  rw [infiniteSignCharacter_classTwist]

theorem finiteHeckeWeight_classTwist (ψ : HeckeCharacter 𝔪)
    (χ : ClassGroup (𝓞 K) →* ℂˣ) :
    finiteHeckeWeight 𝔪 (classTwist 𝔪 ψ χ) = finiteHeckeWeight 𝔪 ψ := by
  unfold finiteHeckeWeight
  rw [finiteResidueCharacter_classTwist]

/-- Class twists preserve the actual integral finite conductor, not just a conductor bound. -/
theorem heckeFiniteConductor_classTwist (ψ : HeckeCharacter 𝔪)
    (χ : ClassGroup (𝓞 K) →* ℂˣ) :
    heckeFiniteConductor 𝔪 (classTwist 𝔪 ψ χ) = heckeFiniteConductor 𝔪 ψ := by
  unfold heckeFiniteConductor
  rw [finiteHeckeWeight_classTwist]

/-- Matching local data is equivalent to a unique global class-character twist. -/
theorem same_residue_iff_unique_class_twist (ψ₀ ψ₁ : HeckeCharacter 𝔪) :
    rayResidueCharacter 𝔪 ψ₁ = rayResidueCharacter 𝔪 ψ₀ ↔
      ∃! χ : ClassGroup (𝓞 K) →* ℂˣ, ψ₁ = classTwist 𝔪 ψ₀ χ := by
  constructor
  · intro h
    have hk : (toClassGroup 𝔪).ker ≤ (ψ₁ / ψ₀).ker := by
      intro c hc
      obtain ⟨g, hg⟩ := principalRayResidueMap_surjective 𝔪 ⟨c, hc⟩
      have hfull : fullRayResidueClass 𝔪 g = c := congrArg Subtype.val hg
      have heq := congrArg (fun φ => φ g) h
      change ψ₁ (fullRayResidueClass 𝔪 g) = ψ₀ (fullRayResidueClass 𝔪 g) at heq
      rw [hfull] at heq
      change ψ₁ c / ψ₀ c = 1
      rw [heq]
      exact div_self' (ψ₀ c)
    let e : {ψ : HeckeCharacter 𝔪 // (toClassGroup 𝔪).ker ≤ ψ.ker} ≃
        (ClassGroup (𝓞 K) →* ℂˣ) :=
      (toClassGroup 𝔪).liftOfSurjective (toClassGroup_surjective 𝔪)
    let χ := e ⟨ψ₁ / ψ₀, hk⟩
    have hχ : χ.comp (toClassGroup 𝔪) = ψ₁ / ψ₀ :=
      congrArg Subtype.val (e.symm_apply_apply ⟨ψ₁ / ψ₀, hk⟩)
    have hrepr : ψ₁ = classTwist 𝔪 ψ₀ χ := by
      rw [classTwist, hχ]
      exact ((_root_.mul_comm ψ₀ (ψ₁ / ψ₀)).trans (_root_.div_mul_cancel ψ₁ ψ₀)).symm
    refine ⟨χ, hrepr, ?_⟩
    intro η hη
    apply MonoidHom.ext
    intro k
    obtain ⟨c, rfl⟩ := toClassGroup_surjective 𝔪 k
    have he := congrArg (fun ψ : HeckeCharacter 𝔪 => ψ c) (hη.symm.trans hrepr)
    change ψ₀ c * η (toClassGroup 𝔪 c) = ψ₀ c * χ (toClassGroup 𝔪 c) at he
    exact mul_left_cancel he
  · rintro ⟨χ, rfl, _⟩
    exact rayResidueCharacter_classTwist 𝔪 ψ₀ χ

#print axioms heckeParity_classTwist
#print axioms heckeFiniteConductor_classTwist
#print axioms same_residue_iff_unique_class_twist

end GaloisForLFunctions.HeckeLFunctions
