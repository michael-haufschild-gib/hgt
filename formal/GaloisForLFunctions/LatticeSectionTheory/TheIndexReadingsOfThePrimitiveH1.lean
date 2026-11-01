import GaloisForLFunctions.LatticeSectionTheory.HeckeCorrespondencesAreSimilitudesOfThePrimitiveH1
import GaloisForLFunctions.LatticeSectionTheory.TheSiegelMajorantIsTheHodgeIndex
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheIndexExit

/-!
# The index readings of the primitive `h¹`

Quantization is the integer side of the theory. The primitive `h¹ = ½δ` of the Künneth count has a
number of negative directions — the Hodge defect — which the corpus reads as the number of distinct
zeros right of the critical line (ACS `pontryagin_law`, AOG `zeta_orientationIndex_law`). Zeros
right of the line come in pairs, so the reading is even, and its first quantum is RH.

**Consistency of the readings** (`riemannHypothesis_primitiveH1_tfae`). On the scaling surface the
following are equivalent:
1. RH;
2. the primitive `h¹` is nonnegative on every class;
3. the Künneth count is an effectivity function;
4. every nonzero primitive class has a convergent Gaussian (Siegel) count;
5. fewer than two zeros of `ζ` lie right of the line (AOG, the index exit).

So a reading of the primitive `h¹` index with precision better than `2` — an `O(1)` statement about
an even integer — is RH, while every reading by sections (Künneth, Siegel) is the sign itself.
-/

noncomputable section

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory ArithmeticOrientationGeometry

/-- The primitive `h¹` is nonnegative everywhere iff the Hodge index holds. -/
theorem forall_primitiveH1_nonneg_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : PolarSurface E) : (∀ x, 0 ≤ primitiveH1 S x) ↔ S.HodgeIndex := by
  rw [S.hodgeIndex_iff_castelnuovoSeveri, S.castelnuovoSeveri_iff_defect_nonneg]
  refine forall_congr' fun x => ?_
  rw [primitiveH1_eq]
  constructor <;> intro h <;> linarith

/-- **The index readings of the primitive `h¹` are one statement.** -/
theorem riemannHypothesis_primitiveH1_tfae (u : ℝ) {t : ℝ} (ht : 0 < t) :
    List.TFAE
      [ RiemannHypothesis,
        ∀ x : ScalingCycle, 0 ≤ primitiveH1 scalingSurface x,
        RiemannInequality scalingSurface 0 0 (kunnethH0 scalingSurface) ∧
          DegreeBounded scalingSurface (kunnethH0 scalingSurface),
        ∀ x : ScalingCycle, scalingSurface.pair x scalingSurface.H = 0 →
          scalingSurface.pair x scalingSurface.V = 0 → x ≠ 0 →
            Summable (siegelTerm scalingSurface u t x),
        (rightZeros zetaZeroConfig).encard < 2 ] := by
  tfae_have 1 ↔ 2 :=
    scalingSurface_hodgeIndex_iff.symm.trans (forall_primitiveH1_nonneg_iff scalingSurface).symm
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_kunneth_effectivity
  tfae_have 1 ↔ 4 := riemannHypothesis_iff_forall_summable_siegelTerm u ht
  tfae_have 1 ↔ 5 := riemannHypothesis_iff_encard_rightZeros_lt_two
  tfae_finish

end GaloisForLFunctions.LatticeSectionTheory
