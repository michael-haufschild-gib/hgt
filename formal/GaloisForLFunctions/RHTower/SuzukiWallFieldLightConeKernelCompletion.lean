import GaloisForLFunctions.RHTower.SuzukiWallFieldAntidiagonalGramLift
import GaloisForLFunctions.RHTower.SuzukiXiRealFEBipolarizationCompletion

/-!
# Suzuki wall-field light-cone kernel completion

The critical wall field has two fixed reflected combinations

`ellPlus(t)  = (omega(t) + I * omega(-t)) / 2`,
`ellMinus(t) = (omega(t) - I * omega(-t)) / 2`.

Their rank-one Gram kernels are exactly the positive and negative light forms already forced by
the Xi-real quarter-turn and functional-equation reflection.  Their difference is the reflected
far-current kernel; adding the negative Gram therefore completes that current to the positive
Gram.  The two light legs are unique once their difference and Euclidean wall sum are fixed.

The construction survives arbitrary finite prime-power and height packets: both light matrices
are literal finite-dimensional Gram matrices and the completion identity holds entrywise after
source summation.  Off the spectral center it gives an exact nonnegative completion of the real
delayed-hinge atom.

No RH premise, estimate, numerical computation, infinite prime sum, or cofinal convergence is
used.  This theorem identifies the source-level completion channel; it does not assert that the
full Robin/Gamma/holonomy carrier supplies that channel in the cofinal limit.
-/

open Complex
open scoped BigOperators ComplexConjugate ComplexOrder
open GaloisForLFunctions GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Reflected light amplitudes and kernels -/

/-- Positive-light combination of one critical wall field and its reflected height. -/
def suzukiCriticalWallPositiveLightAmplitude
    (t : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  (suzukiCriticalWallField t p e + I * suzukiCriticalWallField (-t) p e) / 2

/-- Negative-light combination forced by the same wall field and reflection. -/
def suzukiCriticalWallNegativeLightAmplitude
    (t : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  (suzukiCriticalWallField t p e - I * suzukiCriticalWallField (-t) p e) / 2

/-- Rank-one positive-light kernel. -/
def suzukiCriticalWallPositiveLightKernel
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  suzukiCriticalWallPositiveLightAmplitude t p e *
    star (suzukiCriticalWallPositiveLightAmplitude u p e)

/-- Rank-one negative-light kernel. -/
def suzukiCriticalWallNegativeLightKernel
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  suzukiCriticalWallNegativeLightAmplitude t p e *
    star (suzukiCriticalWallNegativeLightAmplitude u p e)

/-- FE-reflected current extracted from the two anti-diagonal wall-kernel orientations. -/
def suzukiCriticalWallReflectedCurrentKernel
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  I / 2 *
    (suzukiCriticalWallFieldGramKernel (-t) u p e -
      suzukiCriticalWallFieldGramKernel t (-u) p e)

/-- Reflection is complex conjugation on the critical wall field. -/
theorem suzukiCriticalWallField_neg_eq_star
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallField (-t) p e =
      star (suzukiCriticalWallField t p e) := by
  have h := congrArg star (star_suzukiCriticalWallField_neg t p e)
  simpa only [star_star] using h

private theorem star_suzukiCriticalWallPositiveLightAmplitude
    (u : ℝ) (p : Nat.Primes) (e : ℕ) :
    star (suzukiCriticalWallPositiveLightAmplitude u p e) =
      (star (suzukiCriticalWallField u p e) -
        I * star (suzukiCriticalWallField (-u) p e)) / 2 := by
  rw [suzukiCriticalWallPositiveLightAmplitude]
  change (starRingEnd ℂ)
      ((suzukiCriticalWallField u p e + I * suzukiCriticalWallField (-u) p e) / 2) = _
  rw [map_div₀, map_add, map_mul, Complex.conj_I, map_ofNat]
  simp only [starRingEnd_apply]
  ring

private theorem star_suzukiCriticalWallNegativeLightAmplitude
    (u : ℝ) (p : Nat.Primes) (e : ℕ) :
    star (suzukiCriticalWallNegativeLightAmplitude u p e) =
      (star (suzukiCriticalWallField u p e) +
        I * star (suzukiCriticalWallField (-u) p e)) / 2 := by
  rw [suzukiCriticalWallNegativeLightAmplitude]
  change (starRingEnd ℂ)
      ((suzukiCriticalWallField u p e - I * suzukiCriticalWallField (-u) p e) / 2) = _
  rw [map_div₀, map_sub, map_mul, Complex.conj_I, map_ofNat]
  simp only [starRingEnd_apply]
  ring

/-- **Reflected-current factorization.**  Far current is positive light minus negative light. -/
theorem suzukiCriticalWallPositiveLightKernel_sub_negative_eq_reflectedCurrent
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallPositiveLightKernel t u p e -
        suzukiCriticalWallNegativeLightKernel t u p e =
      suzukiCriticalWallReflectedCurrentKernel t u p e := by
  rw [suzukiCriticalWallPositiveLightKernel, suzukiCriticalWallNegativeLightKernel,
    suzukiCriticalWallReflectedCurrentKernel,
    star_suzukiCriticalWallPositiveLightAmplitude,
    star_suzukiCriticalWallNegativeLightAmplitude,
    suzukiCriticalWallPositiveLightAmplitude,
    suzukiCriticalWallNegativeLightAmplitude,
    suzukiCriticalWallFieldGramKernel]
  simp only [suzukiCriticalWallFieldGramKernel]
  ring

/-- Sum of light kernels is the FE-symmetrized Euclidean wall Gram. -/
theorem suzukiCriticalWallPositiveLightKernel_add_negative_eq_symmetrizedGram
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallPositiveLightKernel t u p e +
        suzukiCriticalWallNegativeLightKernel t u p e =
      (suzukiCriticalWallFieldGramKernel t u p e +
        suzukiCriticalWallFieldGramKernel (-t) (-u) p e) / 2 := by
  rw [suzukiCriticalWallPositiveLightKernel, suzukiCriticalWallNegativeLightKernel,
    star_suzukiCriticalWallPositiveLightAmplitude,
    star_suzukiCriticalWallNegativeLightAmplitude,
    suzukiCriticalWallPositiveLightAmplitude,
    suzukiCriticalWallNegativeLightAmplitude,
    suzukiCriticalWallFieldGramKernel]
  simp only [suzukiCriticalWallFieldGramKernel]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Exact local Ward completion.**  Negative light Gram pays the reflected-current debt and
leaves positive light Gram. -/
theorem suzukiCriticalWallReflectedCurrentKernel_add_negative_eq_positive
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallReflectedCurrentKernel t u p e +
        suzukiCriticalWallNegativeLightKernel t u p e =
      suzukiCriticalWallPositiveLightKernel t u p e := by
  rw [← suzukiCriticalWallPositiveLightKernel_sub_negative_eq_reflectedCurrent]
  ring

/-- The two light kernels are uniquely forced by their reflected difference and Euclidean sum. -/
theorem suzukiCriticalWallLightKernels_unique
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) (P N : ℂ)
    (hdiff : P - N = suzukiCriticalWallReflectedCurrentKernel t u p e)
    (hsum : P + N =
      (suzukiCriticalWallFieldGramKernel t u p e +
        suzukiCriticalWallFieldGramKernel (-t) (-u) p e) / 2) :
    P = suzukiCriticalWallPositiveLightKernel t u p e ∧
      N = suzukiCriticalWallNegativeLightKernel t u p e := by
  have hd :=
    suzukiCriticalWallPositiveLightKernel_sub_negative_eq_reflectedCurrent t u p e
  have hs :=
    suzukiCriticalWallPositiveLightKernel_add_negative_eq_symmetrizedGram t u p e
  constructor
  · linear_combination (hdiff - hd + hsum - hs) / 2
  · linear_combination (hsum - hdiff - hs + hd) / 2

/-! ## Literal realization of the corpus Xi-real/FE light plane -/

/-- Real wall-source vector underlying the complex wall field. -/
def suzukiCriticalWallPlaneVector
    (t : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ × ℝ :=
  ((suzukiCriticalWallField t p e).re, (suzukiCriticalWallField t p e).im)

/-- Positive amplitude lies on fixed positive light ray. -/
theorem suzukiCriticalWallPositiveLightAmplitude_eq_ray
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallPositiveLightAmplitude t p e =
      (((suzukiCriticalWallField t p e).re +
        (suzukiCriticalWallField t p e).im : ℝ) : ℂ) * (1 + I) / 2 := by
  rw [suzukiCriticalWallPositiveLightAmplitude,
    suzukiCriticalWallField_neg_eq_star]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Negative amplitude lies on opposite fixed light ray. -/
theorem suzukiCriticalWallNegativeLightAmplitude_eq_ray
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallNegativeLightAmplitude t p e =
      (((suzukiCriticalWallField t p e).re -
        (suzukiCriticalWallField t p e).im : ℝ) : ℂ) * (1 - I) / 2 := by
  rw [suzukiCriticalWallNegativeLightAmplitude,
    suzukiCriticalWallField_neg_eq_star]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;>
    ring

/-- FE reflection on the actual wall plane is negative height reflection. -/
theorem weldFEReflectionLinear_suzukiCriticalWallPlaneVector
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    weldFEReflectionLinear (suzukiCriticalWallPlaneVector t p e) =
      -suzukiCriticalWallPlaneVector (-t) p e := by
  have hneg := suzukiCriticalWallField_neg_eq_star t p e
  ext <;> simp [suzukiCriticalWallPlaneVector, weldFEReflectionLinear, hneg]

/-- Positive complex Gram is literally the corpus positive-light real form on wall vectors. -/
theorem suzukiCriticalWallPositiveLightKernel_eq_weldPositiveLightForm
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallPositiveLightKernel t u p e =
      ((suzukiWeldPositiveLightForm 1
        (suzukiCriticalWallPlaneVector t p e)
        (suzukiCriticalWallPlaneVector u p e) : ℝ) : ℂ) := by
  rw [suzukiCriticalWallPositiveLightKernel,
    suzukiCriticalWallPositiveLightAmplitude_eq_ray,
    suzukiCriticalWallPositiveLightAmplitude_eq_ray]
  apply Complex.ext <;>
    simp [suzukiWeldPositiveLightForm_apply, suzukiCriticalWallPlaneVector,
      Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Negative complex Gram is literally the corpus forced completion form on wall vectors. -/
theorem suzukiCriticalWallNegativeLightKernel_eq_weldNegativeLightForm
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallNegativeLightKernel t u p e =
      ((suzukiWeldNegativeLightForm 1
        (suzukiCriticalWallPlaneVector t p e)
        (suzukiCriticalWallPlaneVector u p e) : ℝ) : ℂ) := by
  rw [suzukiCriticalWallNegativeLightKernel,
    suzukiCriticalWallNegativeLightAmplitude_eq_ray,
    suzukiCriticalWallNegativeLightAmplitude_eq_ray]
  apply Complex.ext <;>
    simp [suzukiWeldNegativeLightForm_apply, suzukiCriticalWallPlaneVector,
      Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Reflected wall current is literally the corpus FE Krein form on actual source vectors. -/
theorem suzukiCriticalWallReflectedCurrentKernel_eq_weldFEKreinQ
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallReflectedCurrentKernel t u p e =
      ((weldFEKreinQ 1
        (suzukiCriticalWallPlaneVector t p e)
        (suzukiCriticalWallPlaneVector u p e) : ℝ) : ℂ) := by
  rw [suzukiCriticalWallReflectedCurrentKernel]
  simp only [suzukiCriticalWallFieldGramKernel]
  rw [suzukiCriticalWallField_neg_eq_star t p e,
    suzukiCriticalWallField_neg_eq_star u p e]
  apply Complex.ext <;>
    simp [weldFEKreinQ_apply, suzukiCriticalWallPlaneVector,
      Complex.mul_re, Complex.mul_im] <;>
    ring

/-! ## Diagonal delayed-hinge completion -/

/-- Diagonal reflected current is the imaginary part of the complex bilinear wall square. -/
theorem suzukiCriticalWallReflectedCurrentKernel_diagonal
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallReflectedCurrentKernel t t p e =
      (((suzukiCriticalWallField t p e) ^ 2).im : ℂ) := by
  rw [suzukiCriticalWallReflectedCurrentKernel_eq_weldFEKreinQ,
    weldFEKreinQ_apply]
  simp [suzukiCriticalWallPlaneVector, pow_two, Complex.mul_im]

/-- Difference of the two diagonal light energies is the far-current numerator. -/
theorem normSq_suzukiCriticalWallPositiveLightAmplitude_sub_negative
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    normSq (suzukiCriticalWallPositiveLightAmplitude t p e) -
        normSq (suzukiCriticalWallNegativeLightAmplitude t p e) =
      ((suzukiCriticalWallField t p e) ^ 2).im := by
  rw [suzukiCriticalWallPositiveLightAmplitude_eq_ray,
    suzukiCriticalWallNegativeLightAmplitude_eq_ray]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  ring

/-- Sum of the light energies recovers the full Euclidean wall energy. -/
theorem normSq_suzukiCriticalWallPositiveLightAmplitude_add_negative
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    normSq (suzukiCriticalWallPositiveLightAmplitude t p e) +
        normSq (suzukiCriticalWallNegativeLightAmplitude t p e) =
      normSq (suzukiCriticalWallField t p e) := by
  rw [suzukiCriticalWallPositiveLightAmplitude_eq_ray,
    suzukiCriticalWallNegativeLightAmplitude_eq_ray]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- Total light energy is exact positive von-Mangoldt wall mass. -/
theorem normSq_suzukiCriticalWallLightAmplitudes_eq_vonMangoldt_div_sqrt
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    normSq (suzukiCriticalWallPositiveLightAmplitude t p e) +
        normSq (suzukiCriticalWallNegativeLightAmplitude t p e) =
      ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
        Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) := by
  rw [normSq_suzukiCriticalWallPositiveLightAmplitude_add_negative]
  have h := congrArg Complex.re
    (suzukiCriticalWallFieldGramKernel_diagonal t p e)
  simpa [suzukiCriticalWallFieldGramKernel, Complex.normSq_apply,
    Complex.mul_re] using h

/-- **Division-matched delayed-hinge completion.**  Off center, the exact negative-light energy
completes real far atom to the positive-light energy. -/
theorem suzukiCriticalDelayedHingeJumpAtom_re_add_negativeLight_eq_positiveLight
    (t : ℝ) (p : Nat.Primes) (e : ℕ) (ht : t ≠ 0) :
    t ^ 2 *
          (suzukiCriticalDelayedHingeJumpAtom
            (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
              Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ))
            (Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) (t : ℂ)).re +
        normSq (suzukiCriticalWallNegativeLightAmplitude t p e) =
      normSq (suzukiCriticalWallPositiveLightAmplitude t p e) := by
  have h := congrArg Complex.re
    (sq_mul_suzukiCriticalDelayedHingeJumpAtom_eq_neg_I_mul_wallField_sq t p e ht)
  have hre :
      t ^ 2 *
          (suzukiCriticalDelayedHingeJumpAtom
            (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
              Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ))
            (Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) (t : ℂ)).re =
        ((suzukiCriticalWallField t p e) ^ 2).im := by
    simpa [Complex.mul_re, pow_two] using h
  rw [hre]
  linarith [normSq_suzukiCriticalWallPositiveLightAmplitude_sub_negative t p e]

/-- Completed real delayed-hinge atom is unconditionally nonnegative off center. -/
theorem suzukiCriticalDelayedHingeJumpAtom_re_add_negativeLight_nonneg
    (t : ℝ) (p : Nat.Primes) (e : ℕ) (ht : t ≠ 0) :
    0 ≤ t ^ 2 *
          (suzukiCriticalDelayedHingeJumpAtom
            (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
              Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ))
            (Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) (t : ℂ)).re +
        normSq (suzukiCriticalWallNegativeLightAmplitude t p e) := by
  rw [suzukiCriticalDelayedHingeJumpAtom_re_add_negativeLight_eq_positiveLight t p e ht]
  exact Complex.normSq_nonneg _

/-! ## Arbitrary finite source and height packets -/

/-- Positive-light feature vector over a finite packet of prime-power sources. -/
def suzukiCriticalWallPositiveLightPacketFeature {M : ℕ}
    (source : Fin M → Nat.Primes × ℕ) (t : ℝ) : EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 fun a =>
    star (suzukiCriticalWallPositiveLightAmplitude t (source a).1 (source a).2)

/-- Negative-light feature vector over the same finite source packet. -/
def suzukiCriticalWallNegativeLightPacketFeature {M : ℕ}
    (source : Fin M → Nat.Primes × ℕ) (t : ℝ) : EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 fun a =>
    star (suzukiCriticalWallNegativeLightAmplitude t (source a).1 (source a).2)

/-- Finite multi-source positive-light matrix on a finite height packet. -/
def suzukiCriticalWallPositiveLightPacketMatrix {M N : ℕ}
    (source : Fin M → Nat.Primes × ℕ) (height : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ := fun i j =>
  ∑ a, suzukiCriticalWallPositiveLightKernel
    (height i) (height j) (source a).1 (source a).2

/-- Finite multi-source negative-light matrix. -/
def suzukiCriticalWallNegativeLightPacketMatrix {M N : ℕ}
    (source : Fin M → Nat.Primes × ℕ) (height : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ := fun i j =>
  ∑ a, suzukiCriticalWallNegativeLightKernel
    (height i) (height j) (source a).1 (source a).2

/-- Finite multi-source reflected-current matrix. -/
def suzukiCriticalWallReflectedCurrentPacketMatrix {M N : ℕ}
    (source : Fin M → Nat.Primes × ℕ) (height : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ := fun i j =>
  ∑ a, suzukiCriticalWallReflectedCurrentKernel
    (height i) (height j) (source a).1 (source a).2

/-- Positive packet matrix is a literal Gram matrix in finite source-coordinate space. -/
theorem suzukiCriticalWallPositiveLightPacketMatrix_eq_gram {M N : ℕ}
    (source : Fin M → Nat.Primes × ℕ) (height : Fin N → ℝ) :
    suzukiCriticalWallPositiveLightPacketMatrix source height =
      Matrix.gram ℂ
        (fun i => suzukiCriticalWallPositiveLightPacketFeature source (height i)) := by
  ext i j
  rw [Matrix.gram_apply, PiLp.inner_apply]
  simp only [suzukiCriticalWallPositiveLightPacketFeature, WithLp.ofLp_toLp,
    RCLike.inner_apply, suzukiCriticalWallPositiveLightPacketMatrix]
  apply Finset.sum_congr rfl
  intro a ha
  change suzukiCriticalWallPositiveLightAmplitude
        (height i) (source a).1 (source a).2 *
      star (suzukiCriticalWallPositiveLightAmplitude
        (height j) (source a).1 (source a).2) =
    star (suzukiCriticalWallPositiveLightAmplitude
        (height j) (source a).1 (source a).2) *
      star (star (suzukiCriticalWallPositiveLightAmplitude
        (height i) (source a).1 (source a).2))
  rw [star_star]
  ring

/-- Every finite positive-light source/height packet is positive semidefinite. -/
theorem suzukiCriticalWallPositiveLightPacketMatrix_posSemidef {M N : ℕ}
    (source : Fin M → Nat.Primes × ℕ) (height : Fin N → ℝ) :
    (suzukiCriticalWallPositiveLightPacketMatrix source height).PosSemidef := by
  rw [suzukiCriticalWallPositiveLightPacketMatrix_eq_gram]
  exact Matrix.posSemidef_gram ℂ _

/-- Negative packet matrix is a literal Gram matrix in the same source-coordinate space. -/
theorem suzukiCriticalWallNegativeLightPacketMatrix_eq_gram {M N : ℕ}
    (source : Fin M → Nat.Primes × ℕ) (height : Fin N → ℝ) :
    suzukiCriticalWallNegativeLightPacketMatrix source height =
      Matrix.gram ℂ
        (fun i => suzukiCriticalWallNegativeLightPacketFeature source (height i)) := by
  ext i j
  rw [Matrix.gram_apply, PiLp.inner_apply]
  simp only [suzukiCriticalWallNegativeLightPacketFeature, WithLp.ofLp_toLp,
    RCLike.inner_apply, suzukiCriticalWallNegativeLightPacketMatrix]
  apply Finset.sum_congr rfl
  intro a ha
  change suzukiCriticalWallNegativeLightAmplitude
        (height i) (source a).1 (source a).2 *
      star (suzukiCriticalWallNegativeLightAmplitude
        (height j) (source a).1 (source a).2) =
    star (suzukiCriticalWallNegativeLightAmplitude
        (height j) (source a).1 (source a).2) *
      star (star (suzukiCriticalWallNegativeLightAmplitude
        (height i) (source a).1 (source a).2))
  rw [star_star]
  ring

/-- Every finite negative-light source/height packet is positive semidefinite. -/
theorem suzukiCriticalWallNegativeLightPacketMatrix_posSemidef {M N : ℕ}
    (source : Fin M → Nat.Primes × ℕ) (height : Fin N → ℝ) :
    (suzukiCriticalWallNegativeLightPacketMatrix source height).PosSemidef := by
  rw [suzukiCriticalWallNegativeLightPacketMatrix_eq_gram]
  exact Matrix.posSemidef_gram ℂ _

/-- **Finite cofinal assembly law.**  Source summation preserves exact light-cone completion. -/
theorem suzukiCriticalWallReflectedCurrentPacketMatrix_add_negative_eq_positive {M N : ℕ}
    (source : Fin M → Nat.Primes × ℕ) (height : Fin N → ℝ) :
    suzukiCriticalWallReflectedCurrentPacketMatrix source height +
        suzukiCriticalWallNegativeLightPacketMatrix source height =
      suzukiCriticalWallPositiveLightPacketMatrix source height := by
  ext i j
  simp only [suzukiCriticalWallReflectedCurrentPacketMatrix,
    suzukiCriticalWallNegativeLightPacketMatrix,
    suzukiCriticalWallPositiveLightPacketMatrix, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [suzukiCriticalWallReflectedCurrentKernel_add_negative_eq_positive]

end

end RHTower
