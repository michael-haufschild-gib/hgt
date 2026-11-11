import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCorrectedRowDerivativesHaveVanishingCorrectionTerms

/-!
# Limits of the first two corrected polynomial jets

Directional differentiation preserves polynomial profiles. Correction
derivatives vanish in the coupled limit; the remaining three operations
are insertion of the harmonic logarithm and multiplication of either
profile by `1−x`. The resulting formulas concern actual derivatives of
the finite arithmetic sums.
-/

open Filter Set Topology Polynomial

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Polynomial multiplication representing a coefficient-power derivative. -/
def complementPolynomial (P : ℝ[X]) : ℝ[X] := (1 - Polynomial.X) * P

theorem complementPolynomial_eval (P : ℝ[X]) :
    (complementPolynomial P).eval = logComplementProfile P.eval := by
  funext x
  simp only [complementPolynomial, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, logComplementProfile]

theorem complementPolynomial_eval_zero (P : ℝ[X]) (hP : P.eval 0 = 0) :
    (complementPolynomial P).eval 0 = 0 := by
  rw [complementPolynomial_eval]
  simp only [logComplementProfile, hP, mul_zero]

/-- The exact first directional derivative of a corrected row. -/
def correctedProfileFirstJet (P Q : ℝ → ℝ) (N : ℕ) (c v κ ν : ℝ) (k j : ℕ) : ℝ :=
  κ * correctedProfileJetSum P Q N c v k (j + 1) +
    κ * correctedProfileJetSum P Q N c v (k + 1) j +
    ν * correctedProfileJetSum (logComplementProfile P) Q N c v k j +
    ν * correctedProfileJetSum P (logComplementProfile Q) N c v k j

/-- The same four operations give the exact second directional derivative. -/
def correctedProfileSecondJet (P Q : ℝ → ℝ) (N : ℕ) (c v κ ν : ℝ) (k j : ℕ) : ℝ :=
  κ * correctedProfileFirstJet P Q N c v κ ν k (j + 1) +
    κ * correctedProfileFirstJet P Q N c v κ ν (k + 1) j +
    ν * correctedProfileFirstJet (logComplementProfile P) Q N c v κ ν k j +
    ν * correctedProfileFirstJet P (logComplementProfile Q) N c v κ ν k j

theorem hasDerivAt_correctedProfileFirstJet_direction
    (P Q : ℝ → ℝ) (N k j : ℕ) (c v κ ν z : ℝ) :
    HasDerivAt (fun y => correctedProfileFirstJet P Q N (c + κ * y) (v + ν * y) κ ν k j)
      (correctedProfileSecondJet P Q N (c + κ * z) (v + ν * z) κ ν k j) z := by
  exact (((hasDerivAt_correctedProfileJetSum_direction P Q N k (j + 1) c v κ ν z).const_mul κ).add
    ((hasDerivAt_correctedProfileJetSum_direction P Q N (k + 1) j c v κ ν z).const_mul κ) |>.add
    ((hasDerivAt_correctedProfileJetSum_direction (logComplementProfile P) Q N k j c v κ ν z).const_mul ν) |>.add
    ((hasDerivAt_correctedProfileJetSum_direction P (logComplementProfile Q) N k j c v κ ν z).const_mul ν))

/-- First and second jets are the literal derivatives along the specified direction. -/
theorem correctedProfile_derivatives (P Q : ℝ → ℝ) (N k j : ℕ) (c v κ ν : ℝ) :
    deriv (fun z => correctedProfileJetSum P Q N (c + κ * z) (v + ν * z) k j) 0 =
      correctedProfileFirstJet P Q N c v κ ν k j ∧
    iteratedDeriv 2 (fun z => correctedProfileJetSum P Q N (c + κ * z) (v + ν * z) k j) 0 =
      correctedProfileSecondJet P Q N c v κ ν k j := by
  have hfirst : deriv (fun z => correctedProfileJetSum P Q N (c + κ * z) (v + ν * z) k j) =
      fun z => correctedProfileFirstJet P Q N (c + κ * z) (v + ν * z) κ ν k j := by
    funext z
    exact (hasDerivAt_correctedProfileJetSum_direction P Q N k j c v κ ν z).deriv
  constructor
  · simp only [hfirst, mul_zero, add_zero]
  · rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, hfirst]
    simpa only [mul_zero, add_zero] using
      (hasDerivAt_correctedProfileFirstJet_direction P Q N k j c v κ ν 0).deriv

/-- The coupled polynomial integral at a specified logarithmic weight. -/
def polynomialProfilePairIntegral (P Q : ℝ[X]) (v : ℝ) (k : ℕ) : ℝ :=
  ∫ t : ℝ in 0..1, t ^ k *
    ((P.derivative.eval (1 - t) - v * P.eval (1 - t)) *
      (Q.derivative.eval (1 - t) - v * Q.eval (1 - t)))

/-- First limiting jet after the vanishing correction derivative is removed. -/
def polynomialProfileFirstLimit (P Q : ℝ[X]) (v κ ν : ℝ) (k : ℕ) : ℝ :=
  κ * polynomialProfilePairIntegral P Q v (k + 1) +
    ν * polynomialProfilePairIntegral (complementPolynomial P) Q v k +
    ν * polynomialProfilePairIntegral P (complementPolynomial Q) v k

/-- Second limiting jet, expressed by the same polynomial operations. -/
def polynomialProfileSecondLimit (P Q : ℝ[X]) (v κ ν : ℝ) (k : ℕ) : ℝ :=
  κ * polynomialProfileFirstLimit P Q v κ ν (k + 1) +
    ν * polynomialProfileFirstLimit (complementPolynomial P) Q v κ ν k +
    ν * polynomialProfileFirstLimit P (complementPolynomial Q) v κ ν k

private theorem tendsto_zeroCorrectionJet (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) (k : ℕ) :
    Tendsto (fun N => correctedProfileJetSum P.eval Q.eval N (-2 * v N) (v N) k 0)
      atTop (𝓝 (polynomialProfilePairIntegral P Q v₀ k)) := by
  simpa only [correctedProfileJetSum_zero_coupled, polynomialProfilePairIntegral] using
    tendsto_correctedCoupledProfileSum P Q hP hQ hv k

/-- The first derivative converges for every convergent normalized shift. -/
theorem tendsto_correctedProfileFirstJet (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) (κ ν : ℝ) (k : ℕ) :
    Tendsto (fun N => correctedProfileFirstJet P.eval Q.eval N (-2 * v N) (v N) κ ν k 0)
      atTop (𝓝 (polynomialProfileFirstLimit P Q v₀ κ ν k)) := by
  have h0 := (tendsto_correctedProfileJetSum_succ_coupled P Q hP hQ hv k 0).const_mul κ
  have h1 := (tendsto_zeroCorrectionJet P Q hP hQ hv (k + 1)).const_mul κ
  have h2 := (tendsto_zeroCorrectionJet (complementPolynomial P) Q
    (complementPolynomial_eval_zero P hP) hQ hv k).const_mul ν
  have h3 := (tendsto_zeroCorrectionJet P (complementPolynomial Q)
    hP (complementPolynomial_eval_zero Q hQ) hv k).const_mul ν
  simpa only [correctedProfileFirstJet, polynomialProfileFirstLimit,
    complementPolynomial_eval, mul_zero, zero_add] using ((h0.add h1).add h2).add h3

/-- A further directional derivative does not restore a vanished correction jet. -/
theorem tendsto_correctedProfileFirstJet_succ (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) (κ ν : ℝ) (k j : ℕ) :
    Tendsto (fun N => correctedProfileFirstJet P.eval Q.eval N (-2 * v N) (v N) κ ν k (j + 1))
      atTop (𝓝 0) := by
  have h0 := (tendsto_correctedProfileJetSum_succ_coupled P Q hP hQ hv k (j + 1)).const_mul κ
  have h1 := (tendsto_correctedProfileJetSum_succ_coupled P Q hP hQ hv (k + 1) j).const_mul κ
  have h2 := (tendsto_correctedProfileJetSum_succ_coupled (complementPolynomial P) Q
    (complementPolynomial_eval_zero P hP) hQ hv k j).const_mul ν
  have h3 := (tendsto_correctedProfileJetSum_succ_coupled P (complementPolynomial Q)
    hP (complementPolynomial_eval_zero Q hQ) hv k j).const_mul ν
  simpa only [correctedProfileFirstJet, complementPolynomial_eval, mul_zero, zero_add] using
    ((h0.add h1).add h2).add h3

/-- The second derivative converges to the polynomial second-jet integral. -/
theorem tendsto_correctedProfileSecondJet (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) (κ ν : ℝ) (k : ℕ) :
    Tendsto (fun N => correctedProfileSecondJet P.eval Q.eval N (-2 * v N) (v N) κ ν k 0)
      atTop (𝓝 (polynomialProfileSecondLimit P Q v₀ κ ν k)) := by
  have h0 := (tendsto_correctedProfileFirstJet_succ P Q hP hQ hv κ ν k 0).const_mul κ
  have h1 := (tendsto_correctedProfileFirstJet P Q hP hQ hv κ ν (k + 1)).const_mul κ
  have h2 := (tendsto_correctedProfileFirstJet (complementPolynomial P) Q
    (complementPolynomial_eval_zero P hP) hQ hv κ ν k).const_mul ν
  have h3 := (tendsto_correctedProfileFirstJet P (complementPolynomial Q)
    hP (complementPolynomial_eval_zero Q hQ) hv κ ν k).const_mul ν
  simpa only [correctedProfileSecondJet, polynomialProfileSecondLimit,
    complementPolynomial_eval, mul_zero, zero_add] using ((h0.add h1).add h2).add h3

end GaloisForLFunctions.MultiscaleMollifiedZetaField
