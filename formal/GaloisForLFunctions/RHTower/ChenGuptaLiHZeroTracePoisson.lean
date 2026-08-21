import GaloisForLFunctions.RHTower.ChenGuptaLiHZeroResiduePartition

open Matrix
open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- Complexification of the positive coprime mass is the CGL `w²` kernel on
the reduced nonnegative residue progressions. -/
theorem cglRealSmoothBumpDyadicCoprimeTerm_ofReal_tsum_eq_reducedResidueNatHZeroSum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    (↑(∑' n : ℕ,
      cglSmoothBumpDyadicCoprimeTerm w.toCGLSmoothBump N Q n) : ℂ) =
      ∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
        ∑' m : ℕ, cglRealSmoothBumpAffineHZeroTerm w N Q a (m : ℤ) := by
  rw [cglSmoothBumpDyadicCoprimeTerm_tsum_eq_reducedResidueNatSum]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro m
  have harg : ((a.val + Q.value * m : ℕ) : ℝ) / N.value =
      ((a.val : ℝ) + Q.value * ((m : ℤ) : ℝ)) / N.value := by
    simp only [Int.cast_natCast, Nat.cast_add, Nat.cast_mul]
  unfold cglRealSmoothBumpAffineHZeroTerm
  rw [w.normSq_value_eq_realValue_sq]
  rw [← harg]
  rw [Complex.ofReal_pow]
  exact (w.value_mul_self_eq_realValue_sq _).symm

/-- The CGL weighted character Gram trace, embedded in `ℂ`, equals its reduced-residue
nonnegative `w²` progression mass. -/
theorem cglRealSmoothBumpDyadicWeighted_trace_re_ofReal_eq_card_mul_reducedResidueNatHZeroSum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    (((cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows *
      (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows)ᴴ).trace).re : ℂ) =
      (R : ℂ) * ∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
        ∑' m : ℕ, cglRealSmoothBumpAffineHZeroTerm w N Q a (m : ℤ) := by
  have htrace :=
    cglSmoothBumpDyadicWeighted_trace_self_mul_conjTranspose_re_eq_card_mul_dyadicCoprimeSum
      w.toCGLSmoothBump N Q R rows
  have hsum := cglSmoothBumpDyadicCoprimeTerm_tsum_eq_dyadicCoprimeSum
    w.toCGLSmoothBump N Q
  have htrace' :
      ((cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows *
        (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
          (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows)ᴴ).trace).re =
        (R : ℝ) * ∑' n : ℕ,
          cglSmoothBumpDyadicCoprimeTerm w.toCGLSmoothBump N Q n := by
    calc
      ((cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows *
        (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
          (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows)ᴴ).trace).re =
          (R : ℝ) * ∑ n ∈ cglCharacterDyadicBlock N,
            ‖w.toCGLSmoothBump.value ((n : ℝ) / N.value)‖ ^ 2 *
              if n.Coprime Q.value then 1 else 0 := htrace
      _ = _ := by rw [← hsum]
  have htraceC := congrArg (fun x : ℝ => (x : ℂ)) htrace'
  calc
    (((cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows *
        (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
          (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows)ᴴ).trace).re : ℂ) =
        (R : ℂ) * (↑(∑' n : ℕ,
          cglSmoothBumpDyadicCoprimeTerm w.toCGLSmoothBump N Q n) : ℂ) := by
      simpa using htraceC
    _ = _ := by
      rw [cglRealSmoothBumpDyadicCoprimeTerm_ofReal_tsum_eq_reducedResidueNatHZeroSum]

/-- Compact support removes every negative affine lattice term in the trace formula. -/
theorem cglRealSmoothBumpDyadicWeighted_trace_re_ofReal_eq_card_mul_reducedResidueIntHZeroSum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    (((cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows *
      (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows)ᴴ).trace).re : ℂ) =
      (R : ℂ) * ∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
        ∑' k : ℤ, cglRealSmoothBumpAffineHZeroTerm w N Q a k := by
  calc
    (((cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows *
        (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
          (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows)ᴴ).trace).re : ℂ) =
        (R : ℂ) * ∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
          ∑' m : ℕ, cglRealSmoothBumpAffineHZeroTerm w N Q a (m : ℤ) :=
      cglRealSmoothBumpDyadicWeighted_trace_re_ofReal_eq_card_mul_reducedResidueNatHZeroSum
        w N Q R rows
    _ = _ := by
      congr 2
      funext a
      exact (cglRealSmoothBumpAffineHZero_tsum_eq_natSum w N Q a).symm

/-- **CGL Lemma 4.4, finite trace-to-Poisson identity.** The source weighted character
Gram trace is exactly the reduced-residue Ramanujan/Fourier expansion of the literal `w²` kernel. -/
theorem cglRealSmoothBumpDyadicWeighted_trace_re_ofReal_eq_card_mul_ramanujanFourier
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    (((cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows *
      (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows)ᴴ).trace).re : ℂ) =
      (R : ℂ) * ∑' ell : ℤ, cglRamanujanAdditiveSum Q (ell : ZMod Q.value) *
        ((cglAffineFourierScale N Q : ℂ) *
          𝓕 (fun u => w.toCGLSmoothBump.value u * w.toCGLSmoothBump.value u)
            (cglAffineFourierScale N Q * (ell : ℝ))) := by
  calc
    (((cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows *
        (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
          (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows)ᴴ).trace).re : ℂ) =
        (R : ℂ) * ∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
          ∑' k : ℤ, cglRealSmoothBumpAffineHZeroTerm w N Q a k :=
      cglRealSmoothBumpDyadicWeighted_trace_re_ofReal_eq_card_mul_reducedResidueIntHZeroSum
        w N Q R rows
    _ = _ := by
      simpa only [cglRealSmoothBumpAffineHZeroTerm] using
        congrArg (fun z : ℂ => (R : ℂ) * z)
          (cglSmoothBumpHZero_reducedResidue_tsum_eq_tsum_ramanujan
            w.toCGLSmoothBump N Q)

end RHTower
