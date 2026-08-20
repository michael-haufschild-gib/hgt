import GaloisForLFunctions.HTGeometry.EllipticGammaDefectFieldEscape
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicBaseChange
import GaloisForLFunctions.HTGeometry.DifferentialMatroidRank

/-!
# The order-one translation orbit along an arbitrary separated shift set

The corpus's order-one packet theorem
`ellipticGammaTranslatePacket_diffIndepOn_of_separated` asks for shifts that are *individually*
nonresonant, because it is phrased with the untranslated logarithmic derivative as a distinguished
base point.  The all-depth argument needs the base-point-free form: a family of translates
`T_s Ψ`, `s ∈ S`, is differentially independent as soon as the *differences* of distinct shifts are
nonresonant.  One of the shifts may then lie in the period lattice itself.

The upgrade is a rebasing.  Translation by a chosen `s₀ ∈ S` is a differential automorphism of the
meromorphic field fixing the constants, and it carries the base-pointed packet at the shift set
`{s - s₀ : s ∈ S, s ≠ s₀}` onto the orbit at `S`.

* **`ellipticGammaTranslateOrbit`** — the orbit of the order-one logarithmic derivative;
* **`ellipticGammaTranslateOrbit_diffIndepOn_of_pairwiseSeparated`** — the base-point-free
  independence theorem over the constants;
* **`ellipticGammaTranslateOrbit_diffIndepOn_daExtension_of_pairwiseSeparated`** — and over every
  differentially algebraic extension of them.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {sigma tau : ℂ}

/-- The translation orbit of the order-one elliptic-gamma logarithmic derivative along a set of
complex shifts. -/
def ellipticGammaTranslateOrbit (S : Set ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im) : Set (meroField (Set.univ : Set ℂ)) :=
  (fun s => addTranslationMeroEquiv s (ellipticGammaLogDerivMero sigma tau hsigma htau)) '' S

theorem mem_ellipticGammaTranslateOrbit_iff {S : Set ℂ}
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    {y : meroField (Set.univ : Set ℂ)} :
    y ∈ ellipticGammaTranslateOrbit S sigma tau hsigma htau ↔
      ∃ s ∈ S, addTranslationMeroEquiv s
        (ellipticGammaLogDerivMero sigma tau hsigma htau) = y := by
  simp [ellipticGammaTranslateOrbit, Set.mem_image]

theorem ellipticGammaTranslateOrbit_mono {S S' : Set ℂ} (h : S ⊆ S')
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ellipticGammaTranslateOrbit S sigma tau hsigma htau ⊆
      ellipticGammaTranslateOrbit S' sigma tau hsigma htau :=
  Set.image_mono h

/-- The base-pointed packet of the corpus is the orbit at the shift set enlarged by `0`. -/
theorem ellipticGammaTranslateOrbit_insert_zero (A : Finset ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ellipticGammaTranslateOrbit (insert (0 : ℂ) (↑A : Set ℂ)) sigma tau hsigma htau =
      insert (ellipticGammaLogDerivMero sigma tau hsigma htau)
        (Set.range (ellipticGammaTranslateFamily (fun a : {x // x ∈ A} => (a : ℂ))
          sigma tau hsigma htau)) := by
  classical
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    rcases hs with rfl | hsA
    · show addTranslationMeroEquiv (0 : ℂ)
        (ellipticGammaLogDerivMero sigma tau hsigma htau) ∈ _
      rw [addTranslationMeroEquiv_zero_apply]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨⟨s, hsA⟩, rfl⟩
  · rintro (rfl | ⟨a, rfl⟩)
    · exact ⟨0, Set.mem_insert _ _, addTranslationMeroEquiv_zero_apply _⟩
    · exact ⟨(a : ℂ), Set.mem_insert_of_mem _ a.2, rfl⟩

/-- Translation carries orbits to orbits. -/
theorem addTranslationMeroAlgEquiv_image_ellipticGammaTranslateOrbit (c : ℂ) (S : Set ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    (⇑(addTranslationMeroDifferentialAlgEquiv c).toAlgEquiv) ''
        ellipticGammaTranslateOrbit S sigma tau hsigma htau =
      ellipticGammaTranslateOrbit ((fun s => c + s) '' S) sigma tau hsigma htau := by
  classical
  have happ : ∀ x : meroField (Set.univ : Set ℂ),
      (addTranslationMeroDifferentialAlgEquiv c).toAlgEquiv x =
        addTranslationMeroEquiv c x := fun _ => rfl
  ext y
  constructor
  · rintro ⟨x, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨c + s, ⟨s, hs, rfl⟩, ?_⟩
    rw [happ, addTranslationMeroEquiv_add]
  · rintro ⟨t, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨addTranslationMeroEquiv s
      (ellipticGammaLogDerivMero sigma tau hsigma htau), ⟨s, hs, rfl⟩, ?_⟩
    rw [happ, addTranslationMeroEquiv_add]

/-- **The base-point-free order-one orbit theorem, finite shift set.** -/
theorem ellipticGammaTranslateOrbit_diffIndepOn_finset
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (S : Finset ℂ)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ThetaTranslationNonresonant tau sigma (a - b)) :
    DiffIndepOn ℂ (ellipticGammaTranslateOrbit (↑S : Set ℂ) sigma tau hsigma htau) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · simpa [ellipticGammaTranslateOrbit] using
      (diffIndepOn_empty (k := ℂ) (K := meroField (Set.univ : Set ℂ)))
  · set A : Finset ℂ := (S.erase s₀).image (fun s => s - s₀) with hA
    have hAmem : ∀ a ∈ A, ∃ s ∈ S, s ≠ s₀ ∧ a = s - s₀ := by
      intro a ha
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨s, Finset.mem_of_mem_erase hs, Finset.ne_of_mem_erase hs, rfl⟩
    have hnonresA : ∀ a ∈ A, ThetaTranslationNonresonant tau sigma a := by
      intro a ha
      obtain ⟨s, hs, hne, rfl⟩ := hAmem a ha
      exact hsep s hs s₀ hs₀ hne
    have hsepA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
        ThetaTranslationNonresonant tau sigma (a - b) := by
      intro a ha b hb hab
      obtain ⟨s, hs, -, rfl⟩ := hAmem a ha
      obtain ⟨t, ht, -, rfl⟩ := hAmem b hb
      have hst : s ≠ t := by
        intro h
        exact hab (by rw [h])
      have hdiff : s - s₀ - (t - s₀) = s - t := by ring
      rw [hdiff]
      exact hsep s hs t ht hst
    have hbase := ellipticGammaTranslatePacket_diffIndepOn_of_separated
      hsigma htau hindependent A hnonresA hsepA
    rw [← ellipticGammaTranslateOrbit_insert_zero A hsigma htau] at hbase
    have himage := (addTranslationMeroDifferentialAlgEquiv s₀).diffIndepOn_image hbase
    rw [addTranslationMeroAlgEquiv_image_ellipticGammaTranslateOrbit s₀ _ hsigma htau] at himage
    have hset : (fun s => s₀ + s) '' (insert (0 : ℂ) (↑A : Set ℂ)) = (↑S : Set ℂ) := by
      ext s
      constructor
      · rintro ⟨a, ha, rfl⟩
        rcases ha with rfl | haA
        · simpa using hs₀
        · obtain ⟨t, ht, -, rfl⟩ := hAmem a haA
          show s₀ + (t - s₀) ∈ (↑S : Set ℂ)
          have hst : s₀ + (t - s₀) = t := by ring
          rw [hst]
          exact ht
      · intro hs
        by_cases hss : s = s₀
        · exact ⟨0, Set.mem_insert _ _, by simp [hss]⟩
        · refine ⟨s - s₀, Set.mem_insert_of_mem _ ?_, by ring⟩
          exact Finset.mem_coe.mpr
            (Finset.mem_image.mpr ⟨s, Finset.mem_erase.mpr ⟨hss, Finset.mem_coe.mp hs⟩, rfl⟩)
    rwa [hset] at himage

/-- **The base-point-free order-one orbit theorem.**  A family of translates of the order-one
elliptic-gamma logarithmic derivative is differentially independent over the constants as soon as
the differences of distinct shifts are nonresonant.  No shift is required to be nonresonant on its
own, so the family may contain a period translate of the logarithmic derivative itself. -/
theorem ellipticGammaTranslateOrbit_diffIndepOn_of_pairwiseSeparated
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (S : Set ℂ)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ThetaTranslationNonresonant tau sigma (a - b)) :
    DiffIndepOn ℂ (ellipticGammaTranslateOrbit S sigma tau hsigma htau) := by
  classical
  refine diffIndepOn_of_forall_finite ?_
  intro T hTsub hTfin
  have hchoice : ∀ y ∈ T, ∃ s : ℂ, s ∈ S ∧
      addTranslationMeroEquiv s (ellipticGammaLogDerivMero sigma tau hsigma htau) = y := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := hTsub hy
    exact ⟨s, hs, hsy⟩
  set sh : meroField (Set.univ : Set ℂ) → ℂ :=
    fun y => if h : y ∈ T then (hchoice y h).choose else 0 with hshdef
  have hsh : ∀ y (hy : y ∈ T), sh y ∈ S ∧
      addTranslationMeroEquiv (sh y) (ellipticGammaLogDerivMero sigma tau hsigma htau) = y := by
    intro y hy
    have hd : sh y = (hchoice y hy).choose := dif_pos hy
    rw [hd]
    exact (hchoice y hy).choose_spec
  set S₀ : Finset ℂ := hTfin.toFinset.image sh with hS₀
  have hS₀sub : (↑S₀ : Set ℂ) ⊆ S := by
    intro s hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hs)
    exact (hsh y (hTfin.mem_toFinset.mp hy)).1
  have hfin := ellipticGammaTranslateOrbit_diffIndepOn_finset hsigma htau hindependent S₀
    (fun a ha b hb hab => hsep a (hS₀sub (Finset.mem_coe.mpr ha)) b
      (hS₀sub (Finset.mem_coe.mpr hb)) hab)
  refine hfin.subset ?_
  intro y hy
  exact ⟨sh y, Finset.mem_coe.mpr (Finset.mem_image.mpr
    ⟨y, hTfin.mem_toFinset.mpr hy, rfl⟩), (hsh y hy).2⟩

/-- The same statement over every differentially algebraic extension of the constants. -/
theorem ellipticGammaTranslateOrbit_diffIndepOn_daExtension_of_pairwiseSeparated
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (S : Set ℂ)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ThetaTranslationNonresonant tau sigma (a - b))
    {G : Set (meroField (Set.univ : Set ℂ))}
    (hG : ∀ g ∈ G, DifferentialAlgebraicOver ℂ g) :
    DiffIndepOn ↥(differentialAdjoin ℂ G)
      (ellipticGammaTranslateOrbit S sigma tau hsigma htau) :=
  diffIndepOn_differentialAdjoin_of_differentialAlgebraicOver
    (ellipticGammaTranslateOrbit_diffIndepOn_of_pairwiseSeparated
      hsigma htau hindependent S hsep) hG

end

end GaloisForLFunctions
