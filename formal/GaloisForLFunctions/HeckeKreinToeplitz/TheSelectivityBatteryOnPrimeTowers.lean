import GaloisForLFunctions.HeckeKreinToeplitz.TheHeckeOrbitKernelOfAZeroConfiguration
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheDyadicSignOfAPoleFreeGeneratorIsRH

/-!
# The selectivity battery on prime towers

A weight `λ` (prime weights on `n ≥ 2`, with the archimedean and pole terms of `ζ`) and a generator
`g` give the **tower kernel** `n ↦ W_λ(T_{−nℓ}(g ⋆ g̃))` on `ℤ` (`towerKernel`): its Gram matrices are
the Weil Gram matrices of the tower `g, T_ℓ g, T_{2ℓ} g, …` (`gram_towerKernel`). Positivity along
the tower is exactly index zero of this kernel (`towerPositive_iff_negIndex_towerKernel_eq_zero`).

In this language the corpus's acceptance tests become statements about kernels on one prime tower:

* **Selectivity** (`not_negIndex_towerKernel_liouville_and_vonMangoldt`): `Λ` and its Liouville
  twin never both have tower kernels of index zero along a nonnegative generator.
* **Precision** (`not_negIndex_towerKernel_and_perturbed`): `λ` and `λ + εn^{−η}`, `0 < η < ½`, never
  both have index zero, although their interval sums agree up to relative error `o(1)`. An index
  argument stable under such errors cannot decide the sign.
* **Unbounded aperture** (`riemannHypothesis_iff_negIndex_towerKernel_poleFree`): RH holds iff the
  tower kernel of `Λ` has index zero for every pole-free generator supported in `[−ε, ε]`, at every
  prime and every `ε > 0`: narrowing the generator does not shorten the tower.

The tool `negIndex_le_of_finset` computes the index on distinct points only.
-/

open Complex Finset
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (weilGram cx)
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (TowerPositive lagW
  weilGram_tower_apply not_towerPositive_and_perturbed not_towerPositive_liouvilleTwin_and_vonMangoldt
  riemannHypothesis_iff_towerPositive_poleFree_small)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

local notation "Tr" => ArithmeticCastelnuovoSeveri.translate

/-- The index can be computed on families of distinct points. -/
theorem negIndex_le_of_finset {G : Type*} [Group G] [DecidableEq G] (k : G → ℂ) {m : ℕ∞}
    (h : ∀ s : Finset G, (hermNegIndex (gram k fun g : s => (g : G)) : ℕ∞) ≤ m) :
    negIndex k ≤ m :=
  negIndex_le_iff.mpr fun _ x => (Nat.cast_le.mpr (hermNegIndex_gram_le_image k x)).trans (h _)

/-- The tower kernel `n ↦ W_λ(T_{−nℓ}(g ⋆ g̃))` of a weight on `ℤ`. -/
def towerKernel (lam : ℕ → ℝ) (g : ℝ → ℂ) (ℓ : ℝ) : Multiplicative ℤ → ℂ :=
  fun n => lagW lam g (-((Multiplicative.toAdd n : ℤ) : ℝ) * ℓ)

/-- The Gram matrices of the tower kernel are the Weil Gram matrices of the tower. -/
theorem gram_towerKernel (lam : ℕ → ℝ) (g : ℝ → ℂ) (ℓ : ℝ) (K : Finset ℤ) :
    gram (towerKernel lam g ℓ) (fun k : K => Multiplicative.ofAdd (k : ℤ)) =
      weilGram lam fun k : K => Tr ((k : ℤ) * ℓ) g := by
  ext i j
  rw [weilGram_tower_apply, gram, towerKernel]
  congr 1
  simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, Int.cast_add, Int.cast_neg]
  ring

/-- **Tower positivity is index zero of the tower kernel.** -/
theorem towerPositive_iff_negIndex_towerKernel_eq_zero (lam : ℕ → ℝ) (g : ℝ → ℂ) (ℓ : ℝ) :
    TowerPositive lam g ℓ ↔ negIndex (towerKernel lam g ℓ) = 0 := by
  classical
  constructor
  · intro h
    refine nonpos_iff_eq_zero.mp (negIndex_le_of_finset _ fun s => ?_)
    set K : Finset ℤ := s.image Multiplicative.toAdd
    let e : s ≃ K := Equiv.ofBijective (fun g => ⟨Multiplicative.toAdd (g : Multiplicative ℤ),
      mem_image_of_mem _ g.2⟩)
      ⟨fun a b hab => by
          have h := congrArg (fun z : K => (z : ℤ)) hab
          exact Subtype.ext (Multiplicative.toAdd.injective h),
        fun k => by
          obtain ⟨g, hg, hk⟩ := mem_image.mp k.2
          exact ⟨⟨g, hg⟩, Subtype.ext hk⟩⟩
    have hgram : gram (towerKernel lam g ℓ) (fun x : s => (x : Multiplicative ℤ)) =
        (gram (towerKernel lam g ℓ) fun k : K => Multiplicative.ofAdd (k : ℤ)).submatrix e e := rfl
    have hle : hermNegIndex (gram (towerKernel lam g ℓ) fun x : s => (x : Multiplicative ℤ)) ≤
        hermNegIndex (weilGram lam fun k : K => Tr ((k : ℤ) * ℓ) g) := by
      rw [hgram, ← gram_towerKernel]
      exact hermNegIndex_le_of_hermQuad_eq _ _ (LinearMap.funLeft ℂ ℂ e.symm) fun c => by
        rw [hermQuad_submatrix_equiv]; rfl
    rw [h K] at hle
    exact_mod_cast hle
  · intro h K
    have := hermNegIndex_gram_le_negIndex (towerKernel lam g ℓ)
      (fun k : K => Multiplicative.ofAdd (k : ℤ))
    rw [h, gram_towerKernel, nonpos_iff_eq_zero, Nat.cast_eq_zero] at this
    exact this

/-- **Selectivity on a tower.** `Λ` and its Liouville twin never both have tower kernels of index
zero along a nonnegative generator. -/
theorem not_negIndex_towerKernel_liouville_and_vonMangoldt {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 (cx f)) (hfc : HasCompactSupport (cx f)) (hf0 : ∀ x, 0 ≤ f x)
    (hne : ∃ x, f x ≠ 0) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ¬ (negIndex (towerKernel ArithmeticCorrespondencePositivity.liouvilleTwin (cx f) ℓ) = 0 ∧
      negIndex (towerKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (cx f) ℓ) = 0) := by
  rw [← towerPositive_iff_negIndex_towerKernel_eq_zero,
    ← towerPositive_iff_negIndex_towerKernel_eq_zero]
  exact not_towerPositive_liouvilleTwin_and_vonMangoldt hf hfc hf0 hne hℓ

/-- **Precision on a tower.** `λ` and `λ + ε n^{−η}`, `0 < η < ½`, never both have tower kernels of
index zero along a nonnegative generator. -/
theorem not_negIndex_towerKernel_and_perturbed (lam : ℕ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 (cx f)) (hfc : HasCompactSupport (cx f)) (hf0 : ∀ x, 0 ≤ f x)
    (hne : ∃ x, f x ≠ 0) {ε η ℓ : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη2 : η < 1 / 2) (hℓ : 0 < ℓ) :
    ¬ (negIndex (towerKernel lam (cx f) ℓ) = 0 ∧
      negIndex (towerKernel (fun n => lam n + ε * (n : ℝ) ^ (-η)) (cx f) ℓ) = 0) := by
  rw [← towerPositive_iff_negIndex_towerKernel_eq_zero,
    ← towerPositive_iff_negIndex_towerKernel_eq_zero]
  exact not_towerPositive_and_perturbed lam hf hfc hf0 hne hε hη hη2 hℓ

/-- **Unbounded aperture.** RH holds iff, at a prime `p` and any `ε > 0`, the tower kernel of `Λ`
has index zero for every pole-free generator supported in `[−ε, ε]`. -/
theorem riemannHypothesis_iff_negIndex_towerKernel_poleFree {p : ℕ} (hp : p.Prime) {ε : ℝ}
    (hε : 0 < ε) :
    RiemannHypothesis ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Set.Icc (-ε) ε →
      paperFT g (I / 2) = 0 → paperFT g (-(I / 2)) = 0 →
        negIndex (towerKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g
          (Real.log p)) = 0 := by
  rw [riemannHypothesis_iff_towerPositive_poleFree_small hp hε]
  simp only [towerPositive_iff_negIndex_towerKernel_eq_zero]

end GaloisForLFunctions.HeckeKreinToeplitz
