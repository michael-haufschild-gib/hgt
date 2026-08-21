/-
# Chen--Gupta--Li Lemma 4.2

This module states CGL's singular-value bound for its literal smoothed
character matrix.  The packet uses `Fin (R + 1)`, so its cardinality is
internally positive and the source trace averages have no caller premise.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma41

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RHTower

/-- Certified data of the nonempty matrix packet in CGL Lemma 4.2. -/
structure CGLLemma42Packet where
  length : CGLPositiveLength
  modulus : CGLPositiveModulus
  cutoff : CGLSmoothBump
  rowTail : ℕ
  rows : Fin (rowTail + 1) → CGLCharacterDyadicRowData modulus.value

/-- The literal CGL smoothing weight `w(n/N)` on the source dyadic block. -/
noncomputable def cglLemma42Weight (P : CGLLemma42Packet) (j : Fin P.length.value) : ℂ :=
  P.cutoff.value ((cglCharacterDyadicIndex P.length.value j : ℝ) / P.length.value)

/-- The exact CGL matrix `M_W` used in Lemma 4.2. -/
noncomputable def cglLemma42Matrix (P : CGLLemma42Packet) :
    Matrix (Fin (P.rowTail + 1)) (Fin P.length.value) ℂ :=
  cglCharacterDyadicWeightedEvaluationMatrix P.length.value P.modulus.value (P.rowTail + 1)
    (cglLemma42Weight P) P.rows

/-- **CGL Lemma 4.2.** The largest singular value of the literal source
matrix is controlled by its centered cubic trace and Hilbert--Schmidt trace. -/
theorem cglLemma42_source_bound (P : CGLLemma42Packet) :
    ‖cglLemma42Matrix P‖ ≤
      2 * (((cglLemma42Matrix P * (cglLemma42Matrix P)ᴴ) ^ 3).trace.re -
        ((cglLemma42Matrix P * (cglLemma42Matrix P)ᴴ).trace.re ^ 3) /
          (P.rowTail + 1 : ℝ) ^ 2) ^ (1 / 6 : ℝ) +
      2 * √((cglLemma42Matrix P * (cglLemma42Matrix P)ᴴ).trace.re /
        (P.rowTail + 1 : ℝ)) := by
  have h := cglCharacterDyadicWeighted_operatorNorm_le_centeredGramTrace
    P.length.value P.modulus.value P.rowTail (cglLemma42Weight P) P.rows
  rw [norm_cglCharacterDyadicWeightedEvaluationOperator_eq_matrix] at h
  rw [← cglCharacterDyadicWeightedEvaluationMatrix_self_mul_conjTranspose_eq_gram] at h
  exact h

end RHTower
