import GaloisForLFunctions.HTGeometry.LongRangeNonHermitianSpectra
import GaloisForLFunctions.HTGeometry.RabiHatanoNelsonApplications
import GaloisForLFunctions.RHTower.RabiHatanoNelsonApplications
import GaloisForLFunctions.RHTower.SupercriticalSharpnessCorpusApplications
import GaloisForLFunctions.RHTower.RationalExponentialDecay
import GaloisForLFunctions.RHTower.RydbergFirstOrderChannelAdditivity

/-!
# Long-range non-Hermitian applications in the arithmetic corpus

The squeeze laws of arXiv:2608.28577 act mechanically on four existing corpus carriers:

* exact Hatano--Nelson skin recurrences;
* Suzuki lattice and prime-step nonreciprocal symbols;
* exponential propagator response; and
* Anderson-localization geometric tail budgets.

Every theorem is closed without external hypotheses.  The paper's admissible interval is enforced
by `longRangeSqueezedExponent`, and existing corpus theorems are then applied at that exponent.
-/

open scoped BigOperators Matrix

open Filter Topology Asymptotics Polynomial Bornology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.RabiHatanoNelson

/-- Skin/localization exponent clamped to the long-range convergence interval. -/
def longRangeSqueezedExponent (α κ : ℝ) : ℝ :=
  squeezedLogModulus α κ

/-- Long-range hopping caps the magnitude of every squeezed localization exponent by `|α|`. -/
theorem abs_longRangeSqueezedExponent_le (α κ : ℝ) :
    |longRangeSqueezedExponent α κ| ≤ |α| := by
  rw [abs_le]
  exact (squeezedLogModulus α κ).property

/-- Existing normalized Hatano--Nelson recurrence survives after the paper's exponent squeeze. -/
theorem longRangeSqueezed_exponentialSkinMode_recurrence_normalized
    (α κ k : ℝ) (n : ℕ) :
    Real.exp (longRangeSqueezedExponent α κ) *
          skinSineMode (Real.exp (longRangeSqueezedExponent α κ)) k n +
        Real.exp (-longRangeSqueezedExponent α κ) *
          skinSineMode (Real.exp (longRangeSqueezedExponent α κ)) k (n + 2) =
      2 * Real.cos k *
        skinSineMode (Real.exp (longRangeSqueezedExponent α κ)) k (n + 1) :=
  exponentialSkinMode_recurrence_normalized (longRangeSqueezedExponent α κ) k n

/-- Squeezed Suzuki symbol remains the corpus's directional-hopping symbol. -/
theorem longRangeSqueezed_hatanoNelsonSymbol_eq_directionalHoppingSymbol
    (α κ θ : ℝ) :
    hatanoNelsonSymbol (longRangeSqueezedExponent α κ) θ =
      directionalHoppingSymbol
        (Real.cosh (longRangeSqueezedExponent α κ))
        (Real.sinh (longRangeSqueezedExponent α κ)) θ :=
  hatanoNelsonSymbol_eq_directionalHoppingSymbol (longRangeSqueezedExponent α κ) θ

/-- Exact real part of the squeezed non-Hermitian ellipse. -/
theorem longRangeSqueezed_hatanoNelsonSymbol_re (α κ θ : ℝ) :
    (hatanoNelsonSymbol (longRangeSqueezedExponent α κ) θ).re =
      2 * Real.cosh (longRangeSqueezedExponent α κ) * Real.cos θ :=
  hatanoNelsonSymbol_re (longRangeSqueezedExponent α κ) θ

/-- Exact imaginary part of the squeezed non-Hermitian ellipse. -/
theorem longRangeSqueezed_hatanoNelsonSymbol_im (α κ θ : ℝ) :
    (hatanoNelsonSymbol (longRangeSqueezedExponent α κ) θ).im =
      2 * Real.sinh (longRangeSqueezedExponent α κ) * Real.sin θ :=
  hatanoNelsonSymbol_im (longRangeSqueezedExponent α κ) θ

/-- At quarter turn, the squeezed ellipse is exactly its imaginary semiaxis. -/
theorem longRangeSqueezed_hatanoNelsonSymbol_quarter_eq (α κ : ℝ) :
    hatanoNelsonSymbol (longRangeSqueezedExponent α κ) (Real.pi / 2) =
      2 * Real.sinh (longRangeSqueezedExponent α κ) * Complex.I :=
  hatanoNelsonSymbol_quarter_eq (longRangeSqueezedExponent α κ)

/-- Corpus propagator-modulus law at the squeezed Hatano--Nelson exponent. -/
theorem longRangeSqueezed_norm_exp_neg_mul_symbol (α κ x θ : ℝ) :
    ‖Complex.exp (-((x : ℂ) * Complex.I) *
        hatanoNelsonSymbol (longRangeSqueezedExponent α κ) θ)‖ =
      Real.exp (x *
        (hatanoNelsonSymbol (longRangeSqueezedExponent α κ) θ).im) :=
  norm_exp_neg_mul_symbol x (longRangeSqueezedExponent α κ) θ

/-- Every finite Suzuki lattice symbol inherits the long-range squeezed directional decomposition. -/
theorem longRangeSqueezed_latticeLimitSymbol_eq_directionalHoppingSum {d : ℕ}
    (α : ℝ) (c₀ : ℝ) (Q : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ)
    (κ : ℝ) (θ : Fin d → ℝ) :
    latticeLimitSymbol c₀ Q c (longRangeSqueezedExponent α κ) θ = (c₀ : ℂ) +
      ∑ q ∈ Q, (c q : ℂ) *
        directionalHoppingSymbol
          (Real.cosh (longRangeSqueezedExponent α κ * (orbitLength q : ℝ)))
          (Real.sinh (longRangeSqueezedExponent α κ * (orbitLength q : ℝ)))
          (∑ i, ((q i : ℤ) : ℝ) * θ i) :=
  latticeLimitSymbol_eq_directionalHoppingSum c₀ Q c
    (longRangeSqueezedExponent α κ) θ

/-- Every finite prime-step symbol inherits the squeezed directional decomposition. -/
theorem longRangeSqueezed_primeStepSymbol_eq_directionalHoppingSum
    {ι : Type*} [Fintype ι] (α : ℝ) (c₀ : ℝ) (Q : Finset (ι → ℤ))
    (c : (ι → ℤ) → ℝ) (κ : ℝ) (θ : ι → ℝ) :
    primeStepSymbol c₀ Q c (longRangeSqueezedExponent α κ) θ = (c₀ : ℂ) +
      ∑ q ∈ Q, (c q : ℂ) *
        directionalHoppingSymbol
          (Real.cosh (longRangeSqueezedExponent α κ * (latticeL1 q : ℝ)))
          (Real.sinh (longRangeSqueezedExponent α κ * (latticeL1 q : ℝ)))
          (∑ i, (q i : ℝ) * θ i) :=
  primeStepSymbol_eq_directionalHoppingSum c₀ Q c
    (longRangeSqueezedExponent α κ) θ

/-- Nonnegative effective Anderson localization exponent after long-range squeezing. -/
def longRangeEffectiveLocalizationExponent (α μ : ℝ) : ℝ :=
  |longRangeSqueezedExponent α μ|

theorem longRangeEffectiveLocalizationExponent_nonneg (α μ : ℝ) :
    0 ≤ longRangeEffectiveLocalizationExponent α μ := abs_nonneg _

/-- Effective Anderson exponent obeys the same long-range cap. -/
theorem longRangeEffectiveLocalizationExponent_le (α μ : ℝ) :
    longRangeEffectiveLocalizationExponent α μ ≤ |α| :=
  abs_longRangeSqueezedExponent_le α μ

/-- Capping localization exponent raises the slowest admissible squared-amplitude decay factor. -/
theorem longRange_localizationDecayFactor_ge (α μ : ℝ) :
    Real.exp (-2 * |α|) ≤
      Real.exp (-2 * longRangeEffectiveLocalizationExponent α μ) := by
  rw [Real.exp_le_exp]
  nlinarith [longRangeEffectiveLocalizationExponent_le α μ]

/-- Existing Anderson tail budget keeps its exact multi-radius recurrence after squeezing. -/
theorem longRange_finiteLocalizationGeometricTailBound_add
    (α C μ A B : ℝ) (R k : ℕ) :
    finiteLocalizationGeometricTailBound C
        (longRangeEffectiveLocalizationExponent α μ) A B (R + k) =
      (B * Real.exp (-2 * longRangeEffectiveLocalizationExponent α μ)) ^ k *
        finiteLocalizationGeometricTailBound C
          (longRangeEffectiveLocalizationExponent α μ) A B R :=
  finiteLocalizationGeometricTailBound_add C
    (longRangeEffectiveLocalizationExponent α μ) A B R k

/-- One-radius version of the squeezed Anderson tail recurrence. -/
theorem longRange_finiteLocalizationGeometricTailBound_succ
    (α C μ A B : ℝ) (R : ℕ) :
    finiteLocalizationGeometricTailBound C
        (longRangeEffectiveLocalizationExponent α μ) A B (R + 1) =
      (B * Real.exp (-2 * longRangeEffectiveLocalizationExponent α μ)) *
        finiteLocalizationGeometricTailBound C
          (longRangeEffectiveLocalizationExponent α μ) A B R :=
  finiteLocalizationGeometricTailBound_succ C
    (longRangeEffectiveLocalizationExponent α μ) A B R

/-! ## Long-range Lindblad channel families -/

/-- Finite Lindblad families weighted by the paper's strict hopping tail remain trace preserving. -/
theorem trace_longRangeLindbladFamilyDissipator {N d : ℕ}
    (α : ℝ) (jump : Fin N → QuantumMatrix d) (X : QuantumMatrix d) :
    Matrix.trace (finiteLindbladFamilyDissipator
      (fun i : Fin N => strictLongRangeRatio α ^ (i.val + 1)) jump X) = 0 :=
  trace_finiteLindbladFamilyDissipator
    (fun i : Fin N => strictLongRangeRatio α ^ (i.val + 1)) jump X

/-- Exact channel additivity for finite Lindblad forcing with long-range geometric weights. -/
theorem longRangeLindbladFamilyObservableResponse_eq_sum {N d : ℕ}
    (α : ℝ) (jump : Fin N → QuantumMatrix d) (A X : QuantumMatrix d) :
    finiteLindbladFamilyObservableResponse
        (fun i : Fin N => strictLongRangeRatio α ^ (i.val + 1)) jump A X =
      ∑ i : Fin N, strictLongRangeRatio α ^ (i.val + 1) *
        finiteLindbladObservableResponse (jump i) A X :=
  finiteLindbladFamilyObservableResponse_eq_sum
    (fun i : Fin N => strictLongRangeRatio α ^ (i.val + 1)) jump A X

end RHTower

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## Wilson-loop transport -/

/-- Long-range squeezing gives the exact passive-reciprocity criterion for a four-link
Hatano--Nelson plaquette. -/
theorem longRangeSqueezedPlaquette_reverseAdjoint_iff (α J κ : ℝ) :
    (∀ i j, rabiHatanoNelsonPlaquetteLink J
        (longRangeSqueezedExponent α κ) j i =
      (rabiHatanoNelsonPlaquetteLink J
        (longRangeSqueezedExponent α κ) i j)ᴴ) ↔
      longRangeSqueezedExponent α κ = 0 :=
  rabiHatanoNelsonPlaquetteLink_reverseAdjoint_iff J
    (longRangeSqueezedExponent α κ)

/-- Exact squeezed clockwise/counterclockwise Wilson-loop contrast. -/
theorem longRangeSqueezed_Wilson_orientation_contrast (α J κ : ℝ) :
    reverseDirectionalWilsonPlaquetteTrace
        (rabiHatanoNelsonPlaquetteLink J (longRangeSqueezedExponent α κ)) 0 1 2 3 -
      directionalWilsonPlaquetteTrace
        (rabiHatanoNelsonPlaquetteLink J (longRangeSqueezedExponent α κ)) 0 1 2 3 =
      -8 * (J : ℂ) * longRangeSqueezedExponent α κ *
        (J ^ (2 : ℕ) + longRangeSqueezedExponent α κ ^ (2 : ℕ)) :=
  rabiHatanoNelson_Wilson_orientation_contrast J
    (longRangeSqueezedExponent α κ)

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

/-! ## Euler--Wick orientation application -/

/-- Squeezed directional hopping still produces the exact Euler--Wick Wilson contrast. -/
theorem longRangeSqueezed_ewqDirectionalWilsonContrast
    (α J κ : ℝ) :
    ewqDirectionalWilsonSignedContrast
        ((J + _root_.RHTower.longRangeSqueezedExponent α κ) -
          (J - _root_.RHTower.longRangeSqueezedExponent α κ)) =
      8 * _root_.RHTower.longRangeSqueezedExponent α κ :=
  ewqDirectionalWilsonContrast_of_directionalHopping J
    (_root_.RHTower.longRangeSqueezedExponent α κ)

/-! ## Exact separation from algebraic tails -/

/-- A nonzero constant rational response cannot be dominated by the strict long-range
exponential tail.  This prevents replacing the paper's exponential mechanism by an algebraic
surrogate even in the simplest rational case. -/
theorem constant_not_isBigO_strictLongRangeExp (α : ℝ) :
    ¬ (fun _x : ℝ => (1 : ℂ)) =O[atTop]
      (fun x : ℝ => (Real.exp (-(|α| + 1) * x) : ℂ)) := by
  have h := complexPolynomial_div_not_isBigO_exp_neg
    (p := (1 : Polynomial ℂ)) (q := (1 : Polynomial ℂ))
    (by norm_num) (by norm_num) (eta := |α| + 1) (by linarith [abs_nonneg α])
  simpa using h

end GaloisForLFunctions.RHTower
