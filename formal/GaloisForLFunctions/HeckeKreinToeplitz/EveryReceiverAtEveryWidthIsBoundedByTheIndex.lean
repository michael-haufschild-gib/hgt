import GaloisForLFunctions.HeckeKreinToeplitz.IntegerFamiliesCarryTheWholeIndex
import GaloisForLFunctions.HeckeKreinToeplitz.TheArchimedeanCompletionCarriesTheSameIndex

/-!
# Every receiver at every width is bounded by the index

The positivity receivers of the corpus are Weil Gram matrices of finitely many real shifts of one
real test. This covers atomic families at any width (the atomic Weil form is the quadratic form of
the Gram matrix of the shifts `φ_w(· − log n)`), spline windows and Hecke orbits. In index language
each of them is a Gram matrix of the archimedean orbit kernel of its test.

**The uniform bound** (`hermNegIndex_weilGram_le_negIndex_zetaKernel`). Take any `C²` compactly
supported real test and any finite family of real shifts. The Weil Gram matrix of the shifts has
at most `κ(K_ζ)` negative squares, the number of zeros right of the line. The bound holds at every
width at once, so atomic families whose width shrinks with `N` are bounded by the index of the Weil
kernel with no regularization of the diagonal.

**The index is the index of the receiver class** (`negIndex_zetaKernel_eq_iSup_receivers`).
`κ(K_ζ)` is the supremum of the negative squares of all receivers, and the integer windows of the
cubic spline already attain it. No receiver sees more negative squares than there are right zeros,
and every negative square of a receiver is paid by a right zero.
-/

open Complex Finset
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests weilGram weilGram_eq_zeroGram
  cx_contDiff cx_hasCompactSupport translate_contDiff translate_hasCompactSupport zeroGram rightZeros)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri renaming translate → shiftTest
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- **The uniform bound.** Every Weil Gram matrix of real shifts of a real test has at most
`κ(K_ζ)` negative squares. -/
theorem hermNegIndex_weilGram_le_negIndex_zetaKernel {f : ℝ → ℝ} (hf : f ∈ realTests)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ι → ℝ) :
    (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      fun a => shiftTest (h a) (cx f)) : ℕ∞) ≤ negIndex zetaKernel := by
  rw [weilGram_eq_zeroGram _ (fun a => translate_contDiff (cx_contDiff hf.1) _)
    (fun a => translate_hasCompactSupport (cx_hasCompactSupport hf.2) _)]
  have hg : zeroGram zetaZeroConfig (fun a => shiftTest (h a) (cx f)) =
      gram (realOrbitKernel zetaZeroConfig f) fun a => Multiplicative.ofAdd (h a) := by
    rw [gram_realOrbitKernel]
    rfl
  rw [hg]
  refine (hermNegIndex_gram_le_negIndex _ _).trans ?_
  rw [negIndex_realOrbitKernel zetaZeroConfig temperedConfig_zetaZeroConfig hf,
    negIndex_zetaKernel]
  exact Set.encard_le_encard fun ρ hρ => ⟨hρ.1, hρ.2.1⟩

/-- **The index of the Weil kernel is the index of the receiver class.** -/
theorem negIndex_zetaKernel_eq_iSup_receivers :
    negIndex zetaKernel = ⨆ (f : ℝ → ℝ) (_ : f ∈ realTests) (n : ℕ) (h : Fin n → ℝ),
      (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        fun a => shiftTest (h a) (cx f)) : ℕ∞) := by
  refine le_antisymm ?_ (iSup₂_le fun f hf => iSup₂_le fun n h =>
    hermNegIndex_weilGram_le_negIndex_zetaKernel hf h)
  rw [negIndex_zetaKernel, negIndex_zetaKernel_eq_iSup_integerAtoms]
  refine iSup_le fun N => ?_
  exact le_iSup₂_of_le cubicSpline cubicSpline_mem_realTests
    (le_iSup₂_of_le N (fun i : Fin N => Real.log ((i : ℝ) + 1)) le_rfl)

/-- **Finite off-line support is a uniform bound on all receivers.** -/
theorem rightZeros_finite_iff_receivers_bounded :
    (rightZeros zetaZeroConfig).Finite ↔ ∃ C : ℕ, ∀ f ∈ realTests, ∀ (n : ℕ) (h : Fin n → ℝ),
      hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        fun a => shiftTest (h a) (cx f)) ≤ C := by
  rw [← Set.encard_lt_top_iff, ← negIndex_zetaKernel]
  constructor
  · intro hlt
    obtain ⟨C, hC⟩ := ENat.ne_top_iff_exists.mp hlt.ne
    exact ⟨C, fun f hf n h => by
      exact_mod_cast (hermNegIndex_weilGram_le_negIndex_zetaKernel hf h).trans hC.ge⟩
  · rintro ⟨C, hC⟩
    rw [negIndex_zetaKernel_eq_iSup_receivers]
    refine lt_of_le_of_lt (iSup₂_le fun f hf => iSup₂_le fun n h => ?_) (ENat.coe_lt_top C)
    exact_mod_cast hC f hf n h

end GaloisForLFunctions.HeckeKreinToeplitz
