import GaloisForLFunctions.HeckeKreinToeplitz.TheSelectivityBatteryOnPrimeTowers
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OnePrimeSeesTheWholeDefectOfZeta

/-!
# One prime tower counts the distinct Frobenius values

The one-prime law for the Weil kernel of `ζ`, in kernel language.

**Windows compute the index** (`negIndex_towerKernel_eq_iSup`). The index of a tower kernel on `ℤ`
is the supremum over finite windows `K ⊆ ℤ` of the negative squares of the Weil Gram matrices of
the tower `g(· − kℓ)`, `k ∈ K`.

**The one-prime law** (`iSup_negIndex_towerKernel_eq_outerEig`). At every prime `p`, the supremum
over `C²` compactly supported generators of the index of the tower kernel of `Λ` along `p` is the
number of distinct values `p^{ρ−1/2}` over the zeros right of the line. The zeros of `ζ` are
deep-sparse, so for a suitable generator the tower reads every distinct value; zeros with equal
value alias into one negative square. This is the arithmetic instance of the aliasing law: one prime
tower sees the right zeros up to `p^{ρ−1/2}`, two primes see them all.
-/

open Complex Finset
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (weilGram towerGram outerEig weilGram_eq_zeroGram
  translate_contDiff translate_hasCompactSupport zeta_one_prime_tower_law)
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (TowerPositive)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

local notation "Tr" => ArithmeticCastelnuovoSeveri.translate

/-- **The index of a tower kernel is computed on windows.** -/
theorem negIndex_towerKernel_eq_iSup (lam : ℕ → ℝ) (g : ℝ → ℂ) (ℓ : ℝ) :
    negIndex (towerKernel lam g ℓ) =
      ⨆ K : Finset ℤ, (hermNegIndex (weilGram lam fun k : K => Tr ((k : ℤ) * ℓ) g) : ℕ∞) := by
  classical
  refine le_antisymm (negIndex_le_of_finset _ fun s => ?_) (iSup_le fun K => ?_)
  · set K : Finset ℤ := s.image Multiplicative.toAdd
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
    exact (Nat.cast_le.mpr hle).trans (le_iSup (fun K : Finset ℤ =>
      (hermNegIndex (weilGram lam fun k : K => Tr ((k : ℤ) * ℓ) g) : ℕ∞)) K)
  · rw [← gram_towerKernel]
    exact hermNegIndex_gram_le_negIndex _ _

/-- **The one-prime law for `ζ`.** -/
theorem iSup_negIndex_towerKernel_eq_outerEig {p : ℕ} (hp : p.Prime) :
    (⨆ (g : ℝ → ℂ) (_ : ContDiff ℝ 2 g ∧ HasCompactSupport g),
        negIndex (towerKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g (Real.log p))) =
      (outerEig zetaZeroConfig (Real.log p)).encard := by
  have hw : ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g → ∀ K : Finset ℤ,
      weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (fun k : K => Tr ((k : ℤ) * Real.log p) g) = towerGram zetaZeroConfig g (Real.log p) K :=
    fun g hg hgc K => weilGram_eq_zeroGram _ (fun _ => translate_contDiff hg _)
      (fun _ => translate_hasCompactSupport hgc _)
  refine le_antisymm (iSup₂_le fun g hg => ?_) (ENat.forall_natCast_le_iff_le.mp fun n hn => ?_)
  · rw [negIndex_towerKernel_eq_iSup]
    refine iSup_le fun K => ENat.forall_natCast_le_iff_le.mp fun m hm => ?_
    rw [hw g hg.1 hg.2 K] at hm
    exact (zeta_one_prime_tower_law hp m).mp ⟨g, hg.1, hg.2, K, by exact_mod_cast hm⟩
  · obtain ⟨g, hg, hgc, K, hK⟩ := (zeta_one_prime_tower_law hp n).mpr hn
    refine le_trans ?_ (le_iSup₂ (f := fun (g : ℝ → ℂ) (_ : ContDiff ℝ 2 g ∧ HasCompactSupport g) =>
      negIndex (towerKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g (Real.log p)))
      g ⟨hg, hgc⟩)
    rw [negIndex_towerKernel_eq_iSup]
    refine le_trans ?_ (le_iSup (fun K : Finset ℤ => (hermNegIndex (weilGram
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) fun k : K =>
        Tr ((k : ℤ) * Real.log p) g) : ℕ∞)) K)
    rw [hw g hg hgc K]
    exact_mod_cast hK

end GaloisForLFunctions.HeckeKreinToeplitz
