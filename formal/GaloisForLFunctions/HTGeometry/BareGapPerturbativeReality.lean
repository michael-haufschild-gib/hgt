import GaloisForLFunctions.HTGeometry.StaticGaussianCrossingMemoryLaw
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Reality of finite bare Born expansions inside a gap

The denominator obstruction in section II.4.2 of arXiv:2608.26494 is
realized for arbitrary finite-dimensional Hermitian Born words. Excitation
energies include a mandatory gap, electron--hole pair costs, and squared
nonnegative excess energies. The zero imaginary diagonal is proved both
on the real axis and as a regulator limit. This concerns finite Born
polynomials, not a formalization of every electron--phonon diagram.
-/

open Filter Topology
open scoped BigOperators Matrix ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry


/-- An addition/removal sector has one unpaired excitation, nonnegative pair costs,
and nonnegative phonon or excess energies. -/
def bareGapExcitationEnergy {k : ℕ} (gap : ℝ) (pairs : ℕ) (excess : Fin k → ℝ) : ℝ :=
  (2 * (pairs : ℝ) + 1) * Real.exp gap + ∑ i, excess i ^ 2

theorem bareGapExcitationEnergy_ge_edge {k : ℕ} (gap : ℝ) (pairs : ℕ)
    (excess : Fin k → ℝ) : Real.exp gap ≤ bareGapExcitationEnergy gap pairs excess := by
  have hs : 0 ≤ ∑ i, excess i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hp : 0 ≤ (pairs : ℝ) := by positivity
  unfold bareGapExcitationEnergy
  nlinarith [Real.exp_pos gap]

theorem bareGapExcitationEnergy_pos {k : ℕ} (gap : ℝ) (pairs : ℕ)
    (excess : Fin k → ℝ) : 0 < bareGapExcitationEnergy gap pairs excess :=
  (Real.exp_pos gap).trans_le (bareGapExcitationEnergy_ge_edge gap pairs excess)

/-- Allowed bare poles lie on the two sides of an open gap around the tested energy. -/
def bareGapPole {k : ℕ} (x gap : ℝ) (addition : Bool) (pairs : ℕ)
    (excess : Fin k → ℝ) : ℝ :=
  if addition then x + bareGapExcitationEnergy gap pairs excess
  else x - bareGapExcitationEnergy gap pairs excess

/-- No zero-temperature excitation denominator can vanish at the tested in-gap energy. -/
theorem bareGapPole_ne_center {k : ℕ} (x gap : ℝ) (addition : Bool) (pairs : ℕ)
    (excess : Fin k → ℝ) : bareGapPole x gap addition pairs excess ≠ x := by
  have he := bareGapExcitationEnergy_pos gap pairs excess
  cases addition <;> simp only [bareGapPole, Bool.false_eq_true, if_false, if_true] <;> linarith

/-- Real-axis bare resolvent, with a regulator retained for boundary-limit statements. -/
def bareGapResolvent {d k : ℕ} (x gap : ℝ) (addition : Fin d → Bool)
    (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ) (eta : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i =>
    ((x : ℂ) + (eta : ℂ) * Complex.I - (bareGapPole x gap (addition i) (pairs i) (excess i) : ℂ))⁻¹)

theorem bareGapResolvent_zero_hermitian {d k : ℕ} (x gap : ℝ) (addition : Fin d → Bool)
    (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ) :
    (bareGapResolvent x gap addition pairs excess 0)ᴴ =
      bareGapResolvent x gap addition pairs excess 0 := by
  simp [bareGapResolvent]

/-- An unrestricted matrix produces a Hermitian interaction by adjoining its adjoint. -/
def bareGapInteraction {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  H + Hᴴ

theorem bareGapInteraction_hermitian {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) :
    (bareGapInteraction H)ᴴ = bareGapInteraction H := by
  simp [bareGapInteraction, add_comm]

/-- The order-`n` bare Born word, with all propagators kept at the bare spectrum. -/
def bareGapBornTerm {d k : ℕ} (x gap : ℝ) (addition : Fin d → Bool)
    (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ)
    (H : Matrix (Fin d) (Fin d) ℂ) (eta : ℝ) (n : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  bareGapResolvent x gap addition pairs excess eta *
    (bareGapInteraction H * bareGapResolvent x gap addition pairs excess eta) ^ n

/-- Every order remains Hermitian in the bare gap, including noncommuting complex interactions. -/
theorem bareGapBornTerm_zero_hermitian {d k : ℕ} (x gap : ℝ) (addition : Fin d → Bool)
    (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ)
    (H : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    (bareGapBornTerm x gap addition pairs excess H 0 n)ᴴ =
      bareGapBornTerm x gap addition pairs excess H 0 n := by
  simp only [bareGapBornTerm, Matrix.conjTranspose_mul, Matrix.conjTranspose_pow,
    bareGapResolvent_zero_hermitian, bareGapInteraction_hermitian]
  exact mul_pow_mul _ _ _

/-- Any finite real-weighted perturbative truncation has the same reality obstruction. -/
def bareGapBornPolynomial {d k : ℕ} (x gap : ℝ) (addition : Fin d → Bool)
    (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ)
    (H : Matrix (Fin d) (Fin d) ℂ) (w : ℕ → ℝ) (N : ℕ) (eta : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ n ∈ Finset.range N, (w n : ℂ) • bareGapBornTerm x gap addition pairs excess H eta n

theorem bareGapBornPolynomial_zero_hermitian {d k : ℕ} (x gap : ℝ)
    (addition : Fin d → Bool) (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ)
    (H : Matrix (Fin d) (Fin d) ℂ) (w : ℕ → ℝ) (N : ℕ) :
    (bareGapBornPolynomial x gap addition pairs excess H w N 0)ᴴ =
      bareGapBornPolynomial x gap addition pairs excess H w N 0 := by
  simp only [bareGapBornPolynomial, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, bareGapBornTerm_zero_hermitian]

/-- The diagonal spectral weight of every finite bare Born truncation vanishes in the gap. -/
theorem bareGapBornPolynomial_zero_diag_im {d k : ℕ} (x gap : ℝ)
    (addition : Fin d → Bool) (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ)
    (H : Matrix (Fin d) (Fin d) ℂ) (w : ℕ → ℝ) (N : ℕ) (i : Fin d) :
    (bareGapBornPolynomial x gap addition pairs excess H w N 0 i i).im = 0 := by
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => (M i i).im)
    (bareGapBornPolynomial_zero_hermitian x gap addition pairs excess H w N)
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im] at h
  linarith

/-- Exclusion of in-gap poles makes the regulated bare resolvent continuous at zero regulator. -/
theorem continuousAt_bareGapResolvent_zero {d k : ℕ} (x gap : ℝ)
    (addition : Fin d → Bool) (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ) :
    ContinuousAt (bareGapResolvent x gap addition pairs excess) 0 := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  by_cases hij : i = j
  · subst j
    simp only [bareGapResolvent, Matrix.diagonal_apply_eq]
    apply ContinuousAt.inv₀ (by fun_prop)
    simp only [Complex.ofReal_zero, zero_mul, add_zero, ne_eq, sub_eq_zero]
    exact fun h => bareGapPole_ne_center x gap (addition i) (pairs i) (excess i)
      (Complex.ofReal_injective h.symm)
  · simpa [bareGapResolvent, Matrix.diagonal_apply_ne _ hij] using
      (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℂ)) 0)

/-- The vanishing is an actual regulator limit, not evaluation using Lean's totalized inverse. -/
theorem tendsto_bareGapBornPolynomial_diag_im_zero {d k : ℕ} (x gap : ℝ)
    (addition : Fin d → Bool) (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ)
    (H : Matrix (Fin d) (Fin d) ℂ) (w : ℕ → ℝ) (N : ℕ) (i : Fin d) :
    Tendsto (fun eta : ℝ => (bareGapBornPolynomial x gap addition pairs excess H w N eta i i).im)
      (𝓝 0) (𝓝 0) := by
  have hR := continuousAt_bareGapResolvent_zero x gap addition pairs excess
  have h : ContinuousAt (bareGapBornPolynomial x gap addition pairs excess H w N) 0 := by
    unfold bareGapBornPolynomial bareGapBornTerm
    fun_prop
  have hi : ContinuousAt
      (fun eta : ℝ => (bareGapBornPolynomial x gap addition pairs excess H w N eta i i).im) 0 := by
    exact Complex.continuous_im.continuousAt.comp
      (continuousAt_pi.mp (continuousAt_pi.mp h i) i)
  simpa only [bareGapBornPolynomial_zero_diag_im] using hi.tendsto

end GaloisForLFunctions.HTGeometry
