import GaloisForLFunctions.RHTower.VonMangoldtGammaClockDescent
import GaloisForLFunctions.HTGeometry.DepthOneJuliaDefect
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

/-- Coordinate Julia defect of a finite positive exponential source shift. -/
def finiteExponentialJuliaDefect
    {P : Type*} [Fintype P] (rate : P → ℝ) : (P → ℂ) →ₗ[ℂ] (P → ℂ) where
  toFun a p := (Real.sqrt (1 - Real.exp (-rate p) ^ 2) : ℂ) * a p
  map_add' _ _ := by
    funext p
    simp [mul_add]
  map_smul' c a := by
    funext p
    change (Real.sqrt (1 - Real.exp (-rate p) ^ 2) : ℂ) * (c * a p) =
      c * ((Real.sqrt (1 - Real.exp (-rate p) ^ 2) : ℂ) * a p)
    ring

/-- Contractive residual coordinate following the Julia defect. -/
def finiteExponentialJuliaResidual
    {P : Type*} [Fintype P] (rate : P → ℝ) : (P → ℂ) →ₗ[ℂ] (P → ℂ) where
  toFun a p :=
    (Real.sqrt ((1 - Real.exp (-rate p)) / (1 + Real.exp (-rate p))) : ℂ) * a p
  map_add' _ _ := by
    funext p
    simp [mul_add]
  map_smul' c a := by
    funext p
    change (Real.sqrt ((1 - Real.exp (-rate p)) / (1 + Real.exp (-rate p))) : ℂ) *
        (c * a p) =
      c * ((Real.sqrt ((1 - Real.exp (-rate p)) / (1 + Real.exp (-rate p))) : ℂ) * a p)
    ring

/-- The coordinate source displacement is the Julia defect followed by its contractive residual. -/
theorem finiteExponentialJuliaDefect_comp_residual
    {P : Type*} [Fintype P] (rate : P → ℝ) (hrate : ∀ p, 0 ≤ rate p) :
    (finiteExponentialJuliaDefect rate).comp (finiteExponentialJuliaResidual rate) =
      LinearMap.id - finiteExponentialSourceShift (fun p => (rate p : ℂ)) := by
  ext a p
  change
    (Real.sqrt (1 - Real.exp (-rate p) ^ 2) : ℂ) *
        ((Real.sqrt ((1 - Real.exp (-rate p)) / (1 + Real.exp (-rate p))) : ℂ) * a p) =
      a p - Complex.exp (-(rate p : ℂ)) * a p
  rw [← mul_assoc]
  rw [← Complex.ofReal_mul, depthOneExponentialShift_julia_factor (hrate p)]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
  push_cast
  ring

/-- At depth one the complete finite Gamma descent anomaly is the source observation of the
canonical Julia defect followed by a contraction. -/
theorem finiteExponentialGammaAnomaly_one_eq_observation_comp_julia
    {P : Type*} [Fintype P] (weight : P → ℂ) (rate : P → ℝ)
    (hrate : ∀ p, 0 ≤ rate p) (x : ℂ) :
    finiteExponentialGammaAnomaly weight (fun p => (rate p : ℂ)) x 1 =
      (finiteExponentialJetObservation weight (fun p => (rate p : ℂ)) x 1).comp
        ((finiteExponentialJuliaDefect rate).comp (finiteExponentialJuliaResidual rate)) := by
  rw [finiteExponentialJuliaDefect_comp_residual rate hrate]
  ext a i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  rw [finiteExponentialGammaAnomaly_one_apply weight (fun p => (rate p : ℂ)) x a]
  change
    (∑ p : P, weight p * a p * (1 - Complex.exp (-(rate p : ℂ))) *
        Complex.exp (-x * (rate p : ℂ))) =
      ∑ p : P, weight p * (a p - Complex.exp (-(rate p : ℂ)) * a p) *
        (-(rate p : ℂ)) ^ (0 : ℕ) * Complex.exp (-x * (rate p : ℂ))
  simp only [pow_zero, mul_one]
  apply Finset.sum_congr rfl
  intro p hp
  simp
  ring

/-- At every Gamma depth the anomaly is the sum of universal clock displacement and the
source-Julia Markov leg.  This separates clock topology from positive source geometry exactly. -/
theorem finiteExponentialGammaAnomaly_eq_clockDisplacement_add_observation_comp_julia
    {P : Type*} [Fintype P] (weight : P → ℂ) (rate : P → ℝ)
    (hrate : ∀ p, 0 ≤ rate p) (x : ℂ) (N : ℕ) :
    finiteExponentialGammaAnomaly weight (fun p => (rate p : ℂ)) x N =
      (gammaClockTranslation N - LinearMap.id).comp
          (finiteExponentialJetObservation weight (fun p => (rate p : ℂ)) x N) +
        (finiteExponentialJetObservation weight (fun p => (rate p : ℂ)) x N).comp
          ((finiteExponentialJuliaDefect rate).comp (finiteExponentialJuliaResidual rate)) := by
  rw [finiteExponentialGammaAnomaly,
    clockDescentAnomaly_eq_clockDisplacement_add_sourceDisplacement,
    finiteExponentialJuliaDefect_comp_residual rate hrate]

/-- The source-Julia leg is strictly compatible under adjacent Gamma-clock truncation.  Hence it
has zero Bianchi defect; all anomaly curvature belongs to the universal clock-displacement leg. -/
theorem finiteExponentialJuliaObservation_truncate
    {P : Type*} [Fintype P] (weight : P → ℂ) (rate : P → ℝ)
    (x : ℂ) (N : ℕ) :
    (gammaClockTruncate N).comp
        ((finiteExponentialJetObservation weight (fun p => (rate p : ℂ)) x (N + 1)).comp
          ((finiteExponentialJuliaDefect rate).comp (finiteExponentialJuliaResidual rate))) =
      (finiteExponentialJetObservation weight (fun p => (rate p : ℂ)) x N).comp
        ((finiteExponentialJuliaDefect rate).comp (finiteExponentialJuliaResidual rate)) := by
  ext a i
  change
    (gammaClockTruncate N)
        (finiteExponentialJetObservation weight (fun p => (rate p : ℂ)) x (N + 1)
          (((finiteExponentialJuliaDefect rate).comp
            (finiteExponentialJuliaResidual rate)) a)) i =
      finiteExponentialJetObservation weight (fun p => (rate p : ℂ)) x N
        (((finiteExponentialJuliaDefect rate).comp
          (finiteExponentialJuliaResidual rate)) a) i
  have h := LinearMap.congr_fun
    (finiteExponentialJetObservation_truncate weight (fun p => (rate p : ℂ)) x N)
    (((finiteExponentialJuliaDefect rate).comp (finiteExponentialJuliaResidual rate)) a)
  exact congrFun h i

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

/-- Any depth-one resolvent whose source frequency is a nonnegative real number is a Stieltjes
cell: its possible denominator zero lies on the nonpositive real axis. -/
theorem depthOneStieltjes_denominator_zero_location
    {lambda : ℝ} (hlambda : 0 ≤ lambda) {w : ℂ}
    (hzero : w + (lambda : ℂ) = 0) :
    w.im = 0 ∧ w.re ≤ 0 := by
  have him := congrArg Complex.im hzero
  have hre := congrArg Complex.re hzero
  simp only [Complex.add_im, Complex.ofReal_im, Complex.zero_im, add_zero] at him
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
  exact ⟨him, by linarith⟩

/-- The raw von Mangoldt/Gamma depth-one resolvent is a Stieltjes cell: a vanishing
denominator can occur only on the nonpositive real axis.  Hence this cell alone cannot carry the
off-axis phase of a Xi zero; any such phase must enter through a later Mellin/Laurent reduction. -/
theorem finiteVonMangoldtDepthOne_denominator_zero_location
    {n : ℕ} (hn : 1 ≤ n) {w : ℂ}
    (hzero : w + finiteVonMangoldtFrequency n = 0) :
    w.im = 0 ∧ w.re ≤ 0 := by
  change w + (Real.log n : ℂ) = 0 at hzero
  exact depthOneStieltjes_denominator_zero_location
    (Real.log_nonneg (by exact_mod_cast hn)) hzero

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
