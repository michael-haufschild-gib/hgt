import GaloisForLFunctions.RHTower.PrimeGammaCauchyCubicSignedEulerianCurvature

/-!
# Cauchy-cubic separation inside the first type-B top fibre

The scalar physical prime--Gamma word carrier identifies the signed words `3142` and `3241`.
Route P's Cauchy-cubic edge has the opposite minimal property required of a survivor: its literal
descent-edge word weight separates those two words, even though their complete type-B top
signatures agree.  The difference is exactly the four-label Cauchy-cubic curvature.

Thus the missing SP-E-to-P lift cannot factor through top signatures or scalar word products.  It
must retain ordered descent-bottom incidence.  This file proves that the P target itself carries
that incidence; it deliberately does not assert the still-open source-faithful lift.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Route-P Cauchy-cubic weight of all descending adjacent edges of a signed word. -/
def primeGammaCauchyCubicSignedEulerianWordWeight
    (x : ℕ → ℝ) (word : List ℤ) : ℝ :=
  signedWordDescentEdgeWeight (primeGammaCauchyCubicDescentKernel x) word

/-- The exact `3142`/`3241` word-weight gap is the signed-Eulerian four-label curvature. -/
theorem primeGammaCauchyCubicSignedEulerianWordWeight_3142_sub_3241
    (x : ℕ → ℝ) :
    primeGammaCauchyCubicSignedEulerianWordWeight x signedWord3142 -
      primeGammaCauchyCubicSignedEulerianWordWeight x signedWord3241 =
        signedEulerianFourLabelCurvature (primeGammaCauchyCubicDescentKernel x) := by
  simp [primeGammaCauchyCubicSignedEulerianWordWeight,
    signedWordDescentEdgeWeight, signedWordDescentEdgeWeightAux,
    signedWord3142, signedWord3241, signedEulerianFourLabelCurvature]

/-- On every strictly ordered positive four-packet, Route P distinguishes the first pair of
signed Eulerian histories that collide under the type-B top statistic. -/
theorem primeGammaCauchyCubicSignedEulerianWordWeight_3241_lt_3142
    (x : ℕ → ℝ) (hx0 : 0 < x 1) (hx12 : x 1 < x 2)
    (hx23 : x 2 < x 3) (hx34 : x 3 < x 4) :
    primeGammaCauchyCubicSignedEulerianWordWeight x signedWord3241 <
      primeGammaCauchyCubicSignedEulerianWordWeight x signedWord3142 := by
  simpa [primeGammaCauchyCubicSignedEulerianWordWeight,
    signedWordDescentEdgeWeight, signedWordDescentEdgeWeightAux,
    signedWord3142, signedWord3241, signedEulerianFourLabelCurvature] using
    (signedEulerianFourLabelCurvature_primeGammaCauchyCubic_pos
      x hx0 hx12 hx23 hx34)

/-- The Cauchy-cubic descent weight is a strict refinement of the complete type-B top signature
at its first nontrivial fibre collision. -/
theorem primeGammaCauchyCubicSignedEulerianWordWeight_separates_firstTypeBTopFiber
    (x : ℕ → ℝ) (hx0 : 0 < x 1) (hx12 : x 1 < x 2)
    (hx23 : x 2 < x 3) (hx34 : x 3 < x 4) :
    typeBTopSignature signedWord3142 = typeBTopSignature signedWord3241 ∧
      primeGammaCauchyCubicSignedEulerianWordWeight x signedWord3241 <
        primeGammaCauchyCubicSignedEulerianWordWeight x signedWord3142 := by
  exact ⟨typeBTopSignature_signedWord3142_eq_signedWord3241,
    primeGammaCauchyCubicSignedEulerianWordWeight_3241_lt_3142
      x hx0 hx12 hx23 hx34⟩

/-- Consequently the actual Cauchy-cubic word weight cannot factor through the complete type-B
top signature on any strictly ordered positive four-packet. -/
theorem not_factorsThroughTypeBTopSignature_primeGammaCauchyCubicSignedEulerianWordWeight
    (x : ℕ → ℝ) (hx0 : 0 < x 1) (hx12 : x 1 < x 2)
    (hx23 : x 2 < x 3) (hx34 : x 3 < x 4) :
    ¬ FactorsThroughTypeBTopSignature
      (primeGammaCauchyCubicSignedEulerianWordWeight x) := by
  intro hfactor
  have hsame := hfactor signedWord3142 signedWord3241
    typeBTopSignature_signedWord3142_eq_signedWord3241
  exact (ne_of_gt
    (primeGammaCauchyCubicSignedEulerianWordWeight_3241_lt_3142
      x hx0 hx12 hx23 hx34)) hsame

end

end GaloisForLFunctions.HTGeometry
