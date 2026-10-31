import GaloisForLFunctions.RenormalizedIntersectionTheory.TheRenormalizedHodgeIndex
import GaloisForLFunctions.HeckeKreinToeplitz.EveryFlipSetHasInfiniteIndexOnTheHeckeLattice

/-!
# The glued index selects ζ among its flip twins

For a prime weight `λ` and a real test `g` the Weil kernel `K_{λ,g}` on `ℚ_{>0}` is the
explicit-formula functional of `g` against its Hecke translates (`HeckeKreinToeplitz.weightKernel`).
Gluing it to the archimedean successor gives the state `K_{λ,g}(|a|) − c|a|^{−1/2}|b|`. The
**glued test index** of `λ` is the supremum of the glued indices over all real `C²` tests of compact
support.

* **Flip twins** (`gluedTestIndex_finiteFlip_eq_top`): for every nonempty finite set of primes `S`,
  the weight that flips the sign of `Λ` at the primes of `S` has glued test index `∞`,
  unconditionally.
* **ζ** (`gluedTestIndex_vonMangoldt`): the glued test index of `Λ` is `κ(K_ζ) + 1`, the number of
  zeros right of the line plus the successor's square; it is attained at the cubic spline.
* **RH** (`riemannHypothesis_iff_gluedTestIndex_eq_one`): RH holds iff the glued test index of `Λ`
  is one.

The glued index is blind to the pole and to unitary twists, but not to the prime data: the
renormalized pairing of the scaling surface separates `ζ` from every finite flip twin, finite
against infinite, exactly on the finite stratum of `ζ`.
-/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
  GaloisForLFunctions.AdelicKreinGeometry GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (finiteFlipWeight)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- The **glued test index** of a weight: the supremum over real `C²` tests of compact support of
the index of the Weil kernel glued to the archimedean successor. -/
def gluedTestIndex (lam : ℕ → ℝ) (c : ℝ) : ℕ∞ :=
  ⨆ (g : ℝ → ℝ) (_ : ContDiff ℝ 2 g ∧ HasCompactSupport g),
    negIndex (archGlue (weightKernel lam g ∘ posUnitsToHecke) c)

/-- Gluing never loses a square: the glued test index dominates the test index. -/
theorem iSup_negIndex_weightKernel_le_gluedTestIndex (lam : ℕ → ℝ) (c : ℝ) :
    (⨆ (g : ℝ → ℝ) (_ : ContDiff ℝ 2 g ∧ HasCompactSupport g), negIndex (weightKernel lam g)) ≤
      gluedTestIndex lam c := by
  refine iSup₂_le fun g hg => ?_
  calc negIndex (weightKernel lam g)
      = negIndex (weightKernel lam g ∘ posUnitsToHecke) :=
        (negIndex_comp_of_surjective _ _ posUnitsToHecke_surjective).symm
    _ ≤ negIndex (archGlue (weightKernel lam g ∘ posUnitsToHecke) c) :=
        negIndex_le_negIndex_archGlue _ c
    _ ≤ gluedTestIndex lam c :=
        le_iSup₂ (f := fun (g : ℝ → ℝ) (_ : ContDiff ℝ 2 g ∧ HasCompactSupport g) =>
          negIndex (archGlue (weightKernel lam g ∘ posUnitsToHecke) c)) g hg

/-- **Every finite flip twin has infinite glued test index.** -/
theorem gluedTestIndex_finiteFlip_eq_top {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hne : S.Nonempty) (c : ℝ) : gluedTestIndex (finiteFlipWeight S) c = ⊤ := by
  have h := iSup_negIndex_weightKernel_le_gluedTestIndex (finiteFlipWeight S) c
  rw [iSup_negIndex_weightKernel_finiteFlip_eq_top hS hne] at h
  exact top_le_iff.mp h

/-- **The glued test index of `ζ` is the index of Weil's kernel plus the successor's square.** -/
theorem gluedTestIndex_vonMangoldt {c : ℝ} (hc : 0 < c) :
    gluedTestIndex (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) c = negIndex zetaKernel + 1 := by
  refine le_antisymm (iSup₂_le fun g hg => ?_) ?_
  · calc negIndex (archGlue (weightKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g ∘
          posUnitsToHecke) c)
        ≤ boostPolarIndex (weightKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g ∘
            posUnitsToHecke) + 1 := negIndex_archGlue_le _ hc.le
      _ ≤ negIndex (weightKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g ∘
            posUnitsToHecke) + 1 := add_le_add (boostPolarIndex_le_negIndex _) le_rfl
      _ = negIndex (weightKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g) + 1 := by
          rw [negIndex_comp_of_surjective _ _ posUnitsToHecke_surjective]
      _ ≤ negIndex zetaKernel + 1 := by
          refine add_le_add ?_ le_rfl
          rw [← iSup_negIndex_weightKernel_vonMangoldt]
          exact le_iSup₂ (f := fun (g : ℝ → ℝ) (_ : ContDiff ℝ 2 g ∧ HasCompactSupport g) =>
            negIndex (weightKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g)) g hg
  · have hB : weightKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) cubicSpline ∘
        posUnitsToHecke = ratCorr := by
      rw [weightKernel_vonMangoldt cubicSpline_mem_realTests, ratCorr_eq_comp, zetaKernel]
    calc negIndex zetaKernel + 1 = negIndex (archGlue ratCorr c) := by
          rw [← weilArchState_eq_archGlue, negIndex_weilArchState_eq_add_one hc]
      _ ≤ gluedTestIndex (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) c := by
          rw [← hB]
          exact le_iSup₂ (f := fun (g : ℝ → ℝ) (_ : ContDiff ℝ 2 g ∧ HasCompactSupport g) =>
            negIndex (archGlue (weightKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g ∘
              posUnitsToHecke) c)) cubicSpline cubicSpline_mem_realTests

/-- **RH is glued test index one.** -/
theorem riemannHypothesis_iff_gluedTestIndex_eq_one {c : ℝ} (hc : 0 < c) :
    RiemannHypothesis ↔ gluedTestIndex (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) c = 1 := by
  rw [gluedTestIndex_vonMangoldt hc, riemannHypothesis_iff_negIndex_zetaKernel_eq_zero]
  constructor
  · intro h; rw [h, zero_add]
  · intro h
    have h' : negIndex zetaKernel + 1 = 0 + 1 := by rw [h, zero_add]
    exact WithTop.add_right_cancel ENat.one_ne_top h'

end GaloisForLFunctions.RenormalizedIntersectionTheory
