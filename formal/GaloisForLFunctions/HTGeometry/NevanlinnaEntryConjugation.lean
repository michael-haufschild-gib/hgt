import GaloisForLFunctions.HTGeometry.NevanlinnaWeylDiscPole

/-!
# Conjugation symmetry of the limiting Nevanlinna matrix

The four limiting entries are built from complex evaluations of real-coefficient orthogonal and
second-kind polynomials, weighted by real moment norms.  Complex conjugation therefore commutes
with every entry: `E(z̄) = conj (E z)`.  Combined with the Weyl-disc pole theorem — the pole
`D/B` lies strictly below the real axis over the upper half-plane — the symmetry places the pole
strictly *above* the real axis over the lower half-plane.  This is the mapping property the
maximal-translation transversality chain consumes after its evaluation nodes move to the lower
half-plane.
-/

namespace HTGeometry

open scoped ComplexConjugate

variable {s : ℕ → ℝ}

/-- Real coefficients make the second-kind complex evaluation commute with conjugation. -/
theorem secondKindC_conj (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    secondKindC s n (starRingEnd ℂ z) = starRingEnd ℂ (secondKindC s n z) := by
  simpa [secondKindC] using
    Polynomial.aeval_algHom_apply (Complex.conjAe.toAlgHom) z (secondKind s n)

/-- Conjugation fixes the value of the monic orthogonal polynomial at a real point encoded in
`ℂ`. -/
theorem conj_monicOrthoC_zero (s : ℕ → ℝ) (k : ℕ) :
    starRingEnd ℂ (monicOrthoC s k 0) = monicOrthoC s k 0 := by
  rw [← monicOrthoC_conj]
  simp

/-- Conjugation fixes the value of the second-kind polynomial at a real point encoded in `ℂ`. -/
theorem conj_secondKindC_zero (s : ℕ → ℝ) (k : ℕ) :
    starRingEnd ℂ (secondKindC s k 0) = secondKindC s k 0 := by
  rw [← secondKindC_conj]
  simp

/-- `B` commutes with conjugation. -/
theorem nevBinf_conj (s : ℕ → ℝ) (z : ℂ) :
    nevBinf s (starRingEnd ℂ z) = starRingEnd ℂ (nevBinf s z) := by
  unfold nevBinf
  rw [map_add, map_mul, map_mul, Complex.conj_ofReal]
  congr 1
  · simp
  · congr 1
    rw [← tsum_star]
    refine tsum_congr fun k => ?_
    rw [starRingEnd_apply] at *
    rw [← starRingEnd_apply, map_div₀, map_mul, monicOrthoC_conj,
      conj_secondKindC_zero, Complex.conj_ofReal, starRingEnd_apply]

/-- `D` commutes with conjugation. -/
theorem nevDinf_conj (s : ℕ → ℝ) (z : ℂ) :
    nevDinf s (starRingEnd ℂ z) = starRingEnd ℂ (nevDinf s z) := by
  unfold nevDinf
  rw [map_mul, map_mul, Complex.conj_ofReal]
  congr 1
  rw [← tsum_star]
  refine tsum_congr fun k => ?_
  rw [← starRingEnd_apply, map_div₀, map_mul, monicOrthoC_conj,
    conj_monicOrthoC_zero, Complex.conj_ofReal, mul_comm, starRingEnd_apply]

/-- **The Weyl-disc pole lies strictly above the real axis over the lower half-plane.** -/
theorem nevInf_quotient_im_pos_of_im_neg (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) {z : ℂ} (hz : z.im < 0) :
    0 < (nevDinf s z / nevBinf s z).im := by
  have hzc : 0 < (starRingEnd ℂ z).im := by
    rw [Complex.conj_im]
    linarith
  have hneg := nevInf_quotient_im_neg h h0b h0 hzc
  have hD : starRingEnd ℂ (nevDinf s (starRingEnd ℂ z)) = nevDinf s z := by
    rw [← nevDinf_conj]
    simp
  have hB : starRingEnd ℂ (nevBinf s (starRingEnd ℂ z)) = nevBinf s z := by
    rw [← nevBinf_conj]
    simp
  have hquot : nevDinf s z / nevBinf s z =
      starRingEnd ℂ (nevDinf s (starRingEnd ℂ z) / nevBinf s (starRingEnd ℂ z)) := by
    rw [map_div₀, hD, hB]
  rw [hquot, Complex.conj_im]
  linarith

/-- **The flipped mapping property for the constructed carrier family**: the projective pole of
the Weyl-disc Möbius map sends the open lower half-plane into the open upper half-plane.  This is
the `upperMap` field of `MaximalTranslationInputs` in its corrected orientation. -/
theorem analyticNevCarrierFamily_lowerMap (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    ∀ z : ℂ, z.im < 0 → 0 < ((analyticNevCarrierFamily h h0b h0).quotient z).im := by
  intro z hz
  rw [analyticNevCarrierFamily_quotient h h0b h0 z]
  exact nevInf_quotient_im_pos_of_im_neg h h0b h0 hz

end HTGeometry
