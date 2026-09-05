import GaloisForLFunctions.HTGeometry.AllDepthCarrierJets

/-!
# The span of the jets of translates of the universal carrier

Every finite constant-coefficient differential-translation operator applied to the universal
carrier lies in one `ℂ`-subspace of the meromorphic germ field, and the carrier of a smaller
direction set lies in the carrier span of a larger one, because the coface law exhibits it as a
translation defect.

* `carrierSpan`, `carrierAtomCombination_mem_carrierSpan`;
* **`carrierSpan_erase_le`** — deleting a direction keeps the span;
* `exists_multiAtomRealization_matching` — an atom sum with exactly a prescribed lattice-invariant
  divisor of bounded order.
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

/-- The `ℂ`-span of all jets of all translates of the universal carrier of a direction set. -/
def carrierSpan (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι) :
    Submodule ℂ (meroField (Set.univ : Set ℂ)) :=
  Submodule.span ℂ
    {y | ∃ (j : ℕ) (b : ℂ),
      y = differentialJet j (addTranslationMeroEquiv b (universalCarrierMero τ hτ s))}

theorem mem_carrierSpan_of_jet (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι)
    (j : ℕ) (b : ℂ) :
    differentialJet j (addTranslationMeroEquiv b (universalCarrierMero τ hτ s))
      ∈ carrierSpan τ hτ s :=
  Submodule.subset_span ⟨j, b, rfl⟩

theorem carrierAtomCombination_mem_carrierSpan (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (s : Finset ι) (k : ι) (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) :
    carrierAtomCombination τ hτ s k N R c ∈ carrierSpan τ hτ s := by
  classical
  rw [carrierAtomCombination]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun q _ => ?_
  have hmem := mem_carrierSpan_of_jet τ hτ s j ((1 + τ k) - q)
  have hsmul := Submodule.smul_mem (carrierSpan τ hτ s)
    (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) hmem
  rwa [Algebra.smul_def] at hsmul

/-- **Deleting a direction keeps the carrier span.**  The carrier of the smaller set is the
translation defect of the carrier of the larger one. -/
theorem carrierSpan_erase_le (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι) {k : ι}
    (hk : k ∈ s) : carrierSpan τ hτ (s \ {k}) ≤ carrierSpan τ hτ s := by
  classical
  have hdefect : universalCarrierMero τ hτ (s \ {k})
      = addTranslationMeroEquiv (τ k) (universalCarrierMero τ hτ s)
        - universalCarrierMero τ hτ s := by
    have hqJ : k ∉ (Finset.univ : Finset ι) \ s := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
      exact hk
    have hco := multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ
      ((Finset.univ : Finset ι) \ s) k hqJ
    have hunion : insert k ((Finset.univ : Finset ι) \ s) = (Finset.univ : Finset ι) \ (s \ {k}) := by
      ext m
      simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton, not_and, not_not]
      constructor
      · rintro (rfl | hm)
        · intro _
          rfl
        · intro hms
          exact absurd hms hm
      · intro hm
        by_cases hms : m ∈ s
        · exact Or.inl (hm hms)
        · exact Or.inr hms
    rw [universalCarrierMero, universalCarrierMero, ← hunion, ← hco]
  rw [carrierSpan]
  refine Submodule.span_le.mpr ?_
  rintro y ⟨j, b, rfl⟩
  rw [hdefect, map_sub, differentialJet_sub, addTranslationMeroEquiv_add]
  exact Submodule.sub_mem _ (mem_carrierSpan_of_jet τ hτ s j (b + τ k))
    (mem_carrierSpan_of_jet τ hτ s j b)

/-! ## An atom sum with a prescribed divisor -/

/-- **Every lattice-invariant divisor of bounded order with finitely many classes is the exact
Laurent datum of an atom sum.** -/
theorem exists_multiAtomRealization_matching {σ : ℂ} (hσ : 0 < σ.im) (D : ℤ → ℂ → ℂ) (N : ℕ)
    (hinv : ∀ ℓ : ℤ, ℓ < 0 → ∀ p g : ℂ, g ∈ lineLattice σ → D ℓ (p + g) = D ℓ p)
    (htop : ∀ ℓ : ℤ, ℓ < -(N : ℤ) → ∀ p, D ℓ p = 0)
    (hfin : ∀ ℓ : ℤ, ℓ < 0 → ∃ S : Finset ℂ, ∀ p, D ℓ p ≠ 0 → ∃ q ∈ S, sameLine σ q p) :
    ∃ (R : Finset ℂ) (c : ℕ → ℂ → ℂ),
      ∀ ℓ : ℤ, ℓ < 0 → ∀ p, laurentCoeff (multiAtomRealization σ N R c) p ℓ = D ℓ p := by
  classical
  choose S hS using fun j : ℕ => hfin (-((j : ℤ) + 1)) (by omega)
  set mkq : ℂ → (ℂ ⧸ lineLattice σ) := fun z => QuotientAddGroup.mk z with hmkq
  have hmk_eq : ∀ a b : ℂ, mkq a = mkq b ↔ a - b ∈ lineLattice σ := fun a b =>
    QuotientAddGroup.eq_iff_sub_mem
  have hout : ∀ x : ℂ ⧸ lineLattice σ, mkq (Quotient.out x) = x := fun x =>
    QuotientAddGroup.out_eq' x
  set R : Finset ℂ := ((Finset.range N).biUnion S).image (fun q => Quotient.out (mkq q)) with hR
  have hRform : ∀ q ∈ R, ∃ x : ℂ ⧸ lineLattice σ, q = Quotient.out x := by
    intro q hq
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨mkq t, rfl⟩
  have hdist : ∀ q ∈ R, ∀ r ∈ R, sameLine σ q r → q = r := by
    intro q hq r hr hqr
    obtain ⟨x, rfl⟩ := hRform q hq
    obtain ⟨y, rfl⟩ := hRform r hr
    have hmem : Quotient.out y - Quotient.out x ∈ lineLattice σ := hqr
    have hneg := neg_mem hmem
    rw [neg_sub] at hneg
    have hxy : mkq (Quotient.out x) = mkq (Quotient.out y) := (hmk_eq _ _).mpr hneg
    rw [hout, hout] at hxy
    rw [hxy]
  refine ⟨R, fun j q => D (-((j : ℤ) + 1)) q, ?_⟩
  intro ℓ hℓ p
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, ℓ = -((j : ℤ) + 1) := ⟨(-ℓ - 1).toNat, by omega⟩
  by_cases hjN : j < N
  · by_cases hcase : ∃ q ∈ R, sameLine σ q p
    · obtain ⟨q, hq, hqp⟩ := hcase
      rw [laurentCoeff_multiAtomRealization_line hσ R _ hdist hq hqp hjN]
      have hmem : p - q ∈ lineLattice σ := hqp
      have hval := hinv (-((j : ℤ) + 1)) (by omega) q (p - q) hmem
      rw [show q + (p - q) = p from by ring] at hval
      exact hval.symm
    · push Not at hcase
      rw [laurentCoeff_multiAtomRealization_off hσ N R _ hcase (by omega)]
      by_contra hne
      obtain ⟨q, hq, hqp⟩ := hS j p (Ne.symm hne)
      have hqT : q ∈ (Finset.range N).biUnion S :=
        Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjN, hq⟩
      have hoR : Quotient.out (mkq q) ∈ R := Finset.mem_image.mpr ⟨q, hqT, rfl⟩
      refine hcase _ hoR ?_
      show p - Quotient.out (mkq q) ∈ lineLattice σ
      refine (hmk_eq p (Quotient.out (mkq q))).mp ?_
      rw [hout]
      have hmem2 : p - q ∈ lineLattice σ := hqp
      exact ((hmk_eq p q).mpr hmem2)
  · have hbig : -((j : ℤ) + 1) < -(N : ℤ) := by omega
    rw [laurentCoeff_multiAtomRealization_of_lt hσ N R _ p hbig]
    exact (htop _ hbig p).symm

end

end GaloisForLFunctions
