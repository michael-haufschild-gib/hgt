import GaloisForLFunctions.RHTower.VonMangoldtGammaClockDescent
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# The depth-one von Mangoldt--Gamma anomaly has a positive Cauchy Gram

At Gamma depth one the Taylor shadow is the identity.  The descent anomaly of a finite resolved
exponential source therefore has the exact coefficient

`weight p * (1 - exp (-frequency p))`.

Taking its elementary resolvent gives a source-defined Cauchy feature.  This file constructs the
finite packet Gram of those features and proves it positive semidefinite.  For the actual von
Mangoldt source the square-root amplitude has square `Lambda(n) / n`, so the Gram retains the
unsquared positive arithmetic mass.

The theorem is finite and unconditional.  It does not identify the cofinal reduced Gram with the
universal Hardy Cauchy kernel and does not identify a limiting response with the Xi Ward current.
-/

open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Exact coordinate formula for the first Gamma descent anomaly of a finite exponential
source. -/
theorem finiteExponentialGammaAnomaly_one_apply
    {P : Type*} [Fintype P]
    (weight frequency : P → ℂ) (x : ℂ) (a : P → ℂ) :
    finiteExponentialGammaAnomaly weight frequency x 1 a 0 =
      ∑ p : P, weight p * a p *
        (1 - Complex.exp (-frequency p)) * Complex.exp (-x * frequency p) := by
  rw [finiteExponentialGammaAnomaly, clockDescentAnomaly_apply]
  simp [gammaClockTranslation, gammaClockTranslationCoefficient,
    finiteExponentialJetObservation, finiteExponentialSourceShift]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The source coefficient exposed by the first Gamma descent anomaly. -/
def finiteExponentialDepthOneAnomalyCoefficient
    {P : Type*} (weight frequency : P → ℂ) (p : P) : ℂ :=
  weight p * (1 - Complex.exp (-frequency p))

/-- Resolvent/Laplace coordinate of the first Gamma descent anomaly. -/
def finiteExponentialDepthOneCauchyFeature
    {P : Type*} (weight frequency : P → ℂ) (w : ℂ) (p : P) : ℂ :=
  finiteExponentialDepthOneAnomalyCoefficient weight frequency p /
    (w + frequency p)

lemma finiteExponentialDepthOneCauchyFeature_mul
    {P : Type*} (weight frequency : P → ℂ) (w : ℂ) (p : P)
    (hden : w + frequency p ≠ 0) :
    finiteExponentialDepthOneCauchyFeature weight frequency w p *
        (w + frequency p) =
      finiteExponentialDepthOneAnomalyCoefficient weight frequency p := by
  rw [finiteExponentialDepthOneCauchyFeature]
  exact div_mul_cancel₀ _ hden

/-- Finite source vector whose Gram is the depth-one anomaly response kernel. -/
def finiteExponentialDepthOneCauchyVector
    {P : Type*} [Fintype P]
    (weight frequency : P → ℂ) (w : ℂ) : EuclideanSpace ℂ P :=
  WithLp.toLp 2 fun p =>
    star (finiteExponentialDepthOneCauchyFeature weight frequency w p)

/-- Positive finite packet Gram of the depth-one source anomaly. -/
def finiteExponentialDepthOneCauchyGram
    {P : Type*} [Fintype P] {N : ℕ}
    (weight frequency : P → ℂ) (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.gram ℂ (fun i => finiteExponentialDepthOneCauchyVector weight frequency (w i))

lemma finiteExponentialDepthOneCauchyGram_apply
    {P : Type*} [Fintype P] {N : ℕ}
    (weight frequency : P → ℂ) (w : Fin N → ℂ) (i j : Fin N) :
    finiteExponentialDepthOneCauchyGram weight frequency w i j =
      ∑ p : P,
        finiteExponentialDepthOneCauchyFeature weight frequency (w i) p *
          star (finiteExponentialDepthOneCauchyFeature weight frequency (w j) p) := by
  rw [finiteExponentialDepthOneCauchyGram, Matrix.gram_apply, PiLp.inner_apply]
  simp only [finiteExponentialDepthOneCauchyVector, WithLp.ofLp_toLp,
    RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro p hp
  change star (finiteExponentialDepthOneCauchyFeature weight frequency (w j) p) *
      star (star (finiteExponentialDepthOneCauchyFeature weight frequency (w i) p)) = _
  rw [star_star]
  ring

/-- Every finite depth-one anomaly response Gram is positive semidefinite before any cofinal or
continued limit is taken. -/
theorem finiteExponentialDepthOneCauchyGram_posSemidef
    {P : Type*} [Fintype P] {N : ℕ}
    (weight frequency : P → ℂ) (w : Fin N → ℂ) :
    (finiteExponentialDepthOneCauchyGram weight frequency w).PosSemidef :=
  Matrix.posSemidef_gram ℂ _

/-- Positive square-root amplitude of the resolved von Mangoldt mass `Lambda(n)/n`. -/
def finiteVonMangoldtDepthOneAmplitude (n : ℕ) : ℂ :=
  (Real.sqrt (ArithmeticFunction.vonMangoldt n / n) : ℂ)

lemma finiteVonMangoldtDepthOneAmplitude_sq
    {n : ℕ} (hn : n ≠ 0) :
    finiteVonMangoldtDepthOneAmplitude n ^ 2 = finiteVonMangoldtWeight n := by
  rw [finiteVonMangoldtDepthOneAmplitude, finiteVonMangoldtWeight,
    LSeries.term_of_ne_zero hn]
  have hnonneg : 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  rw [Complex.cpow_one]
  norm_cast
  simpa using Real.sq_sqrt hnonneg

lemma exp_neg_finiteVonMangoldtFrequency
    {n : ℕ} (hn : n ≠ 0) :
    Complex.exp (-finiteVonMangoldtFrequency n) = (n : ℂ)⁻¹ := by
  rw [finiteVonMangoldtFrequency]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg,
    Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hn)]
  rw [Complex.ofReal_inv, Complex.ofReal_natCast]

/-- Actual resolved von Mangoldt specialization of the depth-one anomaly Cauchy feature. -/
def finiteVonMangoldtDepthOneCauchyFeature (w : ℂ) (n : ℕ) : ℂ :=
  finiteExponentialDepthOneCauchyFeature
    finiteVonMangoldtDepthOneAmplitude finiteVonMangoldtFrequency w n

lemma finiteVonMangoldtDepthOneCauchyFeature_eq
    {n : ℕ} (hn : n ≠ 0) (w : ℂ) :
    finiteVonMangoldtDepthOneCauchyFeature w n =
      finiteVonMangoldtDepthOneAmplitude n * (1 - (n : ℂ)⁻¹) /
        (w + finiteVonMangoldtFrequency n) := by
  rw [finiteVonMangoldtDepthOneCauchyFeature,
    finiteExponentialDepthOneCauchyFeature,
    finiteExponentialDepthOneAnomalyCoefficient,
    exp_neg_finiteVonMangoldtFrequency hn]

/-- Finite positive von Mangoldt/Gamma depth-one Cauchy Gram on the natural-number aperture
`{2, ..., M+1}`. -/
def finiteVonMangoldtDepthOneCauchyGram
    (M : ℕ) {N : ℕ} (w : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  finiteExponentialDepthOneCauchyGram
    (fun n : Fin M => finiteVonMangoldtDepthOneAmplitude (n + 2))
    (fun n : Fin M => finiteVonMangoldtFrequency (n + 2)) w

/-- Every finite actual von Mangoldt/Gamma depth-one anomaly packet has a positive Cauchy response
Gram. -/
theorem finiteVonMangoldtDepthOneCauchyGram_posSemidef
    (M : ℕ) {N : ℕ} (w : Fin N → ℂ) :
    (finiteVonMangoldtDepthOneCauchyGram M w).PosSemidef :=
  finiteExponentialDepthOneCauchyGram_posSemidef _ _ _

end


end RHTower
