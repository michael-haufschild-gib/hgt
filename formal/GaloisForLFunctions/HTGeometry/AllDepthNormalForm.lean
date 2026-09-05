import GaloisForLFunctions.HTGeometry.AllDepthCarrierSpan
import GaloisForLFunctions.HTGeometry.AllDepthCompleteness
import GaloisForLFunctions.HTGeometry.TripticNormalForm
import GaloisForLFunctions.HTGeometry.EllipticGammaJetRealization

/-!
# The universal cyclic normal form of the all-depth class

Every member of the all-depth mixed-constraint class of a finite direction set differs, by a
differentially algebraic germ, from a finite constant-coefficient differential-translation operator
applied to the universal carrier of that set.

At depth two this is the corpus's triptic normal form: the source differs from an explicit finite
combination of elliptic gamma jets by a differentially algebraic function, and the carrier is a
translate of the order-one elliptic gamma logarithmic derivative.  At depth `d ≥ 3` the bottom
charge is realized by a jet combination of the carrier, the difference lies in the class of one
fewer direction, and the carrier of that smaller set is the translation defect of the carrier of the
larger one.

* **`exists_carrierSpan_normal_form`**.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The depth-two carrier is a translate of the elliptic gamma logarithmic derivative.** -/
theorem universalCarrierMero_pair (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) {i j : ι} (hij : i ≠ j) :
    universalCarrierMero τ hτ ({i, j} : Finset ι)
      = addTranslationMeroEquiv (-(1 + τ i) / 2)
          (ellipticGammaLogDerivMero (τ j) (τ i) (hτ j) (hτ i)) := by
  classical
  have haJ : j ∉ (Finset.univ : Finset ι) \ ({i, j} : Finset ι) := by
    simp
  have hbJ : i ∉ (Finset.univ : Finset ι) \ ({i, j} : Finset ι) := by
    simp
  have hJ : ∀ m : ι, m ∉ (Finset.univ : Finset ι) \ ({i, j} : Finset ι) → m = j ∨ m = i := by
    intro m hm
    have hmem : m ∈ ({i, j} : Finset ι) := by
      by_contra hcon
      exact hm (Finset.mem_sdiff.mpr ⟨Finset.mem_univ m, hcon⟩)
    have h2 : m = i ∨ m = j := by simpa using hmem
    exact h2.symm
  rw [universalCarrierMero]
  exact multipleEllipticGammaLogDerivFaceMero_two_surviving τ hτ _ haJ hbJ (Ne.symm hij) hJ

/-- Every jet of a translate of the depth-two elliptic gamma lies in the carrier span. -/
theorem jet_ellipticGamma_mem_carrierSpan (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) {i j : ι}
    (hij : i ≠ j) (n : ℕ) (b : ℂ) :
    differentialJet n (addTranslationMeroEquiv b
        (ellipticGammaLogDerivMero (τ j) (τ i) (hτ j) (hτ i)))
      ∈ carrierSpan τ hτ ({i, j} : Finset ι) := by
  have hmem := mem_carrierSpan_of_jet τ hτ ({i, j} : Finset ι) n (b + (1 + τ i) / 2)
  rw [universalCarrierMero_pair τ hτ hij, addTranslationMeroEquiv_add,
    show b + (1 + τ i) / 2 + -(1 + τ i) / 2 = b from by ring] at hmem
  exact hmem

set_option synthInstance.maxHeartbeats 800000 in
/-- **The depth-two normal form.** -/
theorem exists_carrierSpan_normal_form_pair
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {i j : ι} (hij : i ≠ j)
    {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ} {f : ℂ → ℂ} (hf : RealizesMero x f)
    (hper : PeriodicOneGerm f) (hmixed : MixedConstGermSet τ ({i, j} : Finset ι) f Cst) :
    ∃ y ∈ carrierSpan τ hτ ({i, j} : Finset ι), DifferentialAlgebraicOver ℂ (x - y) := by
  classical
  have hFmero : MeromorphicOn f (Set.univ : Set ℂ) := meromorphicOn_of_realizesMero hf
  have hpair : MixedConstGerm f (τ j) (τ i) Cst := (mixedConstGermSet_pair_iff hij).mp hmixed
  obtain ⟨P, J, -, hDA⟩ := exists_gammaCorrection_differentiallyAlgebraic hFmero hper hpair
    (hτ j) (hτ i) (indepPeriods_of_periodsIntegrallyIndependent τ hQ hij)
    (linearIndependent_one_of_im_pos (hτ j)) (linearIndependent_one_of_im_pos (hτ i))
  have hterm : ∀ (n : ℕ) (q : ℂ),
      RealizesMero
        (algebraMap ℂ (meroField (Set.univ : Set ℂ))
            (gammaCorrectionCoeff (τ j) (τ i) f P q n) *
          differentialJet n (addTranslationMeroEquiv (-(gammaPresentationShift (τ i) + q))
            (ellipticGammaLogDerivMero (τ j) (τ i) (hτ j) (hτ i))))
        (fun z => gammaCorrectionCoeff (τ j) (τ i) f P q n *
          gammaJetSource (τ j) (τ i) q n z) := by
    intro n q
    have hbase := realizesMero_gammaJetSource (hτ j) (hτ i)
      (-(gammaPresentationShift (τ i) + q)) n
    rw [show -(gammaPresentationShift (τ i) + -(gammaPresentationShift (τ i) + q)) = q from by
      ring] at hbase
    exact realizesMero_const_mul _ hbase
  have hyreal : RealizesMero
      (∑ n ∈ Finset.range J, ∑ q ∈ P,
        algebraMap ℂ (meroField (Set.univ : Set ℂ))
            (gammaCorrectionCoeff (τ j) (τ i) f P q n) *
          differentialJet n (addTranslationMeroEquiv (-(gammaPresentationShift (τ i) + q))
            (ellipticGammaLogDerivMero (τ j) (τ i) (hτ j) (hτ i))))
      (gammaCorrection (τ j) (τ i) f P J) := by
    have h := realizesMero_sum (Finset.range J) _ _
      (fun n _ => realizesMero_sum P _ _ (fun q _ => hterm n q))
    exact h
  refine ⟨∑ n ∈ Finset.range J, ∑ q ∈ P,
      algebraMap ℂ (meroField (Set.univ : Set ℂ))
          (gammaCorrectionCoeff (τ j) (τ i) f P q n) *
        differentialJet n (addTranslationMeroEquiv (-(gammaPresentationShift (τ i) + q))
          (ellipticGammaLogDerivMero (τ j) (τ i) (hτ j) (hτ i))), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun n _ => Submodule.sum_mem _ fun q _ => ?_
    have hmem := jet_ellipticGamma_mem_carrierSpan τ hτ hij n
      (-(gammaPresentationShift (τ i) + q))
    have hsmul := Submodule.smul_mem (carrierSpan τ hτ ({i, j} : Finset ι))
      (gammaCorrectionCoeff (τ j) (τ i) f P q n) hmem
    rwa [Algebra.smul_def] at hsmul
  · refine differentialAlgebraicOver_complex_of_ratFunc
      (differentialAlgebraicOver_of_realizesMero (f := fun z =>
        f z - gammaCorrection (τ j) (τ i) f P J z) (realizesMero_sub hf hyreal) hDA)

set_option synthInstance.maxHeartbeats 800000 in
/-- **The universal cyclic normal form.**  Every member of the all-depth mixed-constraint class
differs, by a differentially algebraic germ, from a finite constant-coefficient
differential-translation operator applied to the universal carrier. -/
theorem exists_carrierSpan_normal_form
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ) :
    ∀ (n : ℕ) (s : Finset ι), s.card = n → 2 ≤ n →
      ∀ (x : meroField (Set.univ : Set ℂ)) (Cst : ℂ) (f : ℂ → ℂ), RealizesMero x f →
        PeriodicOneGerm f → MixedConstGermSet τ s f Cst →
        ∃ y ∈ carrierSpan τ hτ s, DifferentialAlgebraicOver ℂ (x - y) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hcard hn x Cst f hf hper hmixed
  have hFmero : MeromorphicOn f (Set.univ : Set ℂ) := meromorphicOn_of_realizesMero hf
  rcases eq_or_lt_of_le hn with hn2 | hn3
  · obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp (by omega : s.card = 2)
    subst hs
    exact exists_carrierSpan_normal_form_pair τ hτ hQ hij hf hper hmixed
  · obtain ⟨k, hk⟩ : ∃ k, k ∈ s := Finset.card_pos.mp (by omega)
    have hcard' : (s \ {k}).card = n - 1 := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hk, hcard]
    obtain ⟨a, ha'⟩ : ∃ a, a ∈ s \ {k} := Finset.card_pos.mp (by omega)
    have hak : a ≠ k := by simpa using (Finset.mem_sdiff.mp ha').2
    have hVmero : MeromorphicOn (bottomWitnessFun τ s k f) (Set.univ : Set ℂ) :=
      meromorphicOn_diffCube τ _ hFmero
    have hone : ∀ ℓ : ℤ, ∀ z : ℂ,
        laurentCoeff (bottomWitnessFun τ s k f) (z + 1) ℓ
          = laurentCoeff (bottomWitnessFun τ s k f) z ℓ :=
      fun ℓ z => laurentCoeff_bottomWitnessFun_add_one τ s k hFmero hper z ℓ
    have htau : ∀ ℓ : ℤ, ℓ < 0 → ∀ z : ℂ,
        laurentCoeff (bottomWitnessFun τ s k f) (z + τ k) ℓ
          = laurentCoeff (bottomWitnessFun τ s k f) z ℓ :=
      fun ℓ hℓ z => laurentCoeff_bottomWitnessFun_add_tau τ s k hk hFmero hmixed z hℓ
    have hlat : ∀ ℓ : ℤ, ℓ < 0 → ∀ z g : ℂ, g ∈ lineLattice (τ k) →
        laurentCoeff (bottomWitnessFun τ s k f) (z + g) ℓ
          = laurentCoeff (bottomWitnessFun τ s k f) z ℓ :=
      fun ℓ hℓ z g hg => laurentCoeff_lineLattice_of_periods (hone ℓ) (htau ℓ hℓ) z hg
    obtain ⟨P, hP⟩ := exists_finset_bottomCharge_pole_classes τ hτ s k hk hFmero hper hmixed
    have hP' : ∀ z : ℂ, meromorphicOrderAt (bottomWitnessFun τ s k f) z < 0 →
        ∃ q ∈ P, sameLine (τ k) q z := by
      intro z hz
      obtain ⟨m, nn, hmem⟩ := hP z hz
      refine ⟨z - (m • (1 : ℂ) + nn • τ k), hmem, m, nn, ?_⟩
      simp only [zsmul_eq_mul]
      ring
    obtain ⟨N, hN⟩ := exists_order_bound_of_lineLattice_invariant hVmero hlat hP'
    obtain ⟨R, cc, hmatch⟩ := exists_multiAtomRealization_matching (hτ k)
      (fun ℓ p => laurentCoeff (bottomWitnessFun τ s k f) p ℓ) N
      (fun ℓ hℓ p g hg => hlat ℓ hℓ p g hg) (fun ℓ hℓ p => hN ℓ hℓ p)
      (fun ℓ hℓ => ⟨P, fun p hp => hP' p (meromorphicOrderAt_neg_of_laurentCoeff_ne_zero
        (hVmero p (Set.mem_univ p)) hℓ hp)⟩)
    obtain ⟨g, CstG, hgreal, hgper, hgmixed, hgbot⟩ :=
      exists_class_member_with_prescribed_bottomCharge τ hτ s hk hak N R cc
    have hgmero : MeromorphicOn g (Set.univ : Set ℂ) := meromorphicOn_of_realizesMero hgreal
    have hEreal : RealizesMero (x - carrierAtomCombination τ hτ s k N R cc)
        (fun z => f z - g z) := realizesMero_sub hf hgreal
    have hEper : PeriodicOneGerm (fun z => f z - g z) := periodicOneGerm_sub hper hgper
    have hcubeE : HTGeometry.diffCube τ s (fun z => f z - g z)
        = fun z => HTGeometry.diffCube τ s f z - HTGeometry.diffCube τ s g z :=
      HTGeometry.diffCube_sub τ s f g
    have hEmixed : MixedConstGermSet τ s (fun z => f z - g z) (Cst - CstG) := by
      intro z
      filter_upwards [hmixed z, hgmixed z] with w h1 h2
      rw [hcubeE]
      show HTGeometry.diffCube τ s f w - HTGeometry.diffCube τ s g w = Cst - CstG
      rw [h1, h2]
    have hbotsplit : bottomWitnessFun τ s k (fun z => f z - g z)
        = fun z => bottomWitnessFun τ s k f z - bottomWitnessFun τ s k g z :=
      HTGeometry.diffCube_sub τ _ f g
    have hgbotmero : MeromorphicOn (bottomWitnessFun τ s k g) (Set.univ : Set ℂ) :=
      meromorphicOn_diffCube τ (s \ {k}) hgmero
    have hEbot : ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
        laurentCoeff (bottomWitnessFun τ s k (fun z => f z - g z)) p ℓ = 0 := by
      intro p ℓ hℓ
      rw [hbotsplit, laurentCoeff_sub (hVmero p (Set.mem_univ p))
        (hgbotmero p (Set.mem_univ p)), hgbot p ℓ hℓ, hmatch ℓ hℓ p, sub_self]
    obtain ⟨-, c₀, hEmixed'⟩ := exists_mixedConstGermSet_erase_of_bottomCharge_eq_zero
      τ hτ s k hk (meromorphicOn_of_realizesMero hEreal) hEper hEmixed hEbot
    obtain ⟨y', hy'mem, hy'DA⟩ := ih (n - 1) (by omega) (s \ {k}) hcard' (by omega)
      (x - carrierAtomCombination τ hτ s k N R cc) c₀ (fun z => f z - g z) hEreal hEper hEmixed'
    refine ⟨carrierAtomCombination τ hτ s k N R cc + y', ?_, ?_⟩
    · exact Submodule.add_mem _ (carrierAtomCombination_mem_carrierSpan τ hτ s k N R cc)
        (carrierSpan_erase_le τ hτ s hk hy'mem)
    · have hrw : x - (carrierAtomCombination τ hτ s k N R cc + y')
          = (x - carrierAtomCombination τ hτ s k N R cc) - y' := by ring
      rw [hrw]
      exact hy'DA

end

end GaloisForLFunctions
