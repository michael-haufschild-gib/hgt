import GaloisForLFunctions.RHTower.XiShiftedHalfDensityMobiusSourceConnection
import GaloisForLFunctions.RHTower.PolynomialTruncation
import GaloisForLFunctions.HTGeometry.AdaptiveOrthogonalSourceGaussDecomposition

/-!
# Source-first half-density admission boundary port

The shifted-Xi half-density generator raises degree by one.  Coefficient truncation first identifies
the loss exactly: on an amplitude retaining degrees through `n`, the generator has one and only one
excluded coefficient,

`((n : ℝ) + 1 / 2) * P.coeff n`.

Coefficient truncation is still a fixed reporter, so it is not the final producer.  The actual
adaptive construction uses the current monic orthogonal flag and splits

`K P_n = A_n + (n+1/2) P_(n+1)`,  `deg A_n <= n`.

The admitted landing `A_n` depends on the current moments.  Its pairing with `X P_n` is itself a
strictly positive Jacobi energy, while the terminal port is `(2n+1) ||P_(n+1)||^2`.  Therefore the
completed adaptive `P^sharp` aggregate is exactly a sum of three positive, source-first channels:
multiplication Gram bulk, adaptive admitted landing, and terminal boundary port.  Formation occurs
before reflection; no orientation map or fixed linear reporter enters the final identity.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- Coefficientwise action of the shifted-Xi half-density generator. -/
theorem coeff_xiShiftedMobiusHalfDensityGenerator_succ
    (P : Polynomial ℝ) (k : ℕ) :
    (xiShiftedMobiusHalfDensityGenerator P).coeff (k + 1) =
      ((k : ℝ) + 1 / 2) * P.coeff k := by
  cases k with
  | zero =>
      simp [xiShiftedMobiusHalfDensityGenerator, xiShiftedMobiusDensityGenerator,
        Polynomial.coeff_X_pow_mul', Polynomial.smul_eq_C_mul]
  | succ k =>
      simp only [xiShiftedMobiusHalfDensityGenerator, xiShiftedMobiusDensityGenerator,
        Polynomial.coeff_add, Polynomial.coeff_smul]
      rw [Polynomial.coeff_X_pow_mul', if_pos (by omega)]
      rw [show k + 1 + 1 - 2 = k by omega, Polynomial.coeff_derivative,
        Polynomial.coeff_X_mul]
      push_cast
      ring

/-- **Exact one-port finite-admission law.**  The half-density source of an amplitude admitted
through degree `n` is its re-admitted part plus one terminal monomial.  There is no further tail. -/
theorem xiShiftedMobiusHalfDensityGenerator_lowTrunc_eq_admitted_add_boundaryPort
    (P : Polynomial ℝ) (n : ℕ) :
    xiShiftedMobiusHalfDensityGenerator
        (PolynomialTruncation.lowTrunc P (n + 1)) =
      PolynomialTruncation.lowTrunc
          (xiShiftedMobiusHalfDensityGenerator
            (PolynomialTruncation.lowTrunc P (n + 1))) (n + 1) +
        (((n : ℝ) + 1 / 2) * P.coeff n) •
          (X : Polynomial ℝ) ^ (n + 1) := by
  apply Polynomial.ext
  intro k
  rcases lt_trichotomy k (n + 1) with hk | rfl | hk
  · rw [Polynomial.coeff_add,
      PolynomialTruncation.coeff_lowTrunc_of_lt _ hk]
    simp [Polynomial.coeff_X_pow, ne_of_lt hk]
  · rw [Polynomial.coeff_add,
      PolynomialTruncation.coeff_lowTrunc_eq_zero_of_le _ (le_refl (n + 1)),
      coeff_xiShiftedMobiusHalfDensityGenerator_succ,
      PolynomialTruncation.coeff_lowTrunc_of_lt P (by omega)]
    simp
  · cases k with
    | zero => omega
    | succ k =>
        rw [coeff_xiShiftedMobiusHalfDensityGenerator_succ,
          PolynomialTruncation.coeff_lowTrunc_eq_zero_of_le P (by omega),
          Polynomial.coeff_add,
          PolynomialTruncation.coeff_lowTrunc_eq_zero_of_le _ (by omega)]
        simp [Polynomial.coeff_X_pow, show k ≠ n by omega]

/-- Every moment pairing sees finite-admission loss through the same single bilinear terminal
port.  This universal algebraic statement has no positivity or analytic premise. -/
theorem momentInner_xiShiftedMobiusHalfDensityGenerator_lowTrunc_eq_boundaryPort
    (s : ℕ → ℝ) (P : Polynomial ℝ) (n : ℕ) :
    HTGeometry.momentInner s
        (xiShiftedMobiusHalfDensityGenerator
          (PolynomialTruncation.lowTrunc P (n + 1)))
        (X * PolynomialTruncation.lowTrunc P (n + 1)) =
      HTGeometry.momentInner s
          (PolynomialTruncation.lowTrunc
            (xiShiftedMobiusHalfDensityGenerator
              (PolynomialTruncation.lowTrunc P (n + 1))) (n + 1))
          (X * PolynomialTruncation.lowTrunc P (n + 1)) +
        (((n : ℝ) + 1 / 2) * P.coeff n) *
          HTGeometry.momentInner s ((X : Polynomial ℝ) ^ (n + 1))
            (X * PolynomialTruncation.lowTrunc P (n + 1)) := by
  have h := congrArg
    (fun R : Polynomial ℝ => HTGeometry.momentInner s R
      (X * PolynomialTruncation.lowTrunc P (n + 1)))
    (xiShiftedMobiusHalfDensityGenerator_lowTrunc_eq_admitted_add_boundaryPort P n)
  rw [HTGeometry.momentInner_add_left, HTGeometry.momentInner_smul_left] at h
  exact h

/-- The literal completed adaptive mixed source of a finite amplitude has exactly one excluded
half-density source port.  Arithmetic formation occurs before reflection aggregation. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_lowTrunc_eq_halfDensityBoundaryPort
    {w : ℝ} (hw : 1 / 2 < w) (P : Polynomial ℝ) (n : ℕ) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (PolynomialTruncation.lowTrunc P (n + 1)) =
      HTGeometry.momentInner (xiShiftedRealMomentSequence w)
          (X * PolynomialTruncation.lowTrunc P (n + 1))
          (X * PolynomialTruncation.lowTrunc P (n + 1)) +
        2 * HTGeometry.momentInner (xiShiftedRealMomentSequence w)
          (PolynomialTruncation.lowTrunc
            (xiShiftedMobiusHalfDensityGenerator
              (PolynomialTruncation.lowTrunc P (n + 1))) (n + 1))
          (X * PolynomialTruncation.lowTrunc P (n + 1)) +
        ((2 : ℝ) * n + 1) * P.coeff n *
          HTGeometry.momentInner (xiShiftedRealMomentSequence w)
            ((X : Polynomial ℝ) ^ (n + 1))
            (X * PolynomialTruncation.lowTrunc P (n + 1)) := by
  rw [xiShiftedAdaptiveMixedCompletedArithmeticSource_eq_halfDensityLanding hw,
    momentInner_xiShiftedMobiusHalfDensityGenerator_lowTrunc_eq_boundaryPort]
  ring

/-- **Admission-sensitive completed `P^sharp` arithmetic source law.**  The adaptive odd packet's
completed aggregate consists exactly of visible Gram bulk, admitted half-density landing, and the
single terminal arithmetic port carrying the first excluded degree. -/
theorem xiShiftedCompletedMomentAggregate_lowTrunc_eq_halfDensityBoundaryPort
    {w : ℝ} (hw : 1 / 2 < w) (P : Polynomial ℝ) (n : ℕ) :
    xiShiftedCompletedMomentAggregate (w ^ 2) 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket
            (PolynomialTruncation.lowTrunc P (n + 1)))) =
      HTGeometry.momentInner (xiShiftedRealMomentSequence w)
          (X * PolynomialTruncation.lowTrunc P (n + 1))
          (X * PolynomialTruncation.lowTrunc P (n + 1)) +
        2 * HTGeometry.momentInner (xiShiftedRealMomentSequence w)
          (PolynomialTruncation.lowTrunc
            (xiShiftedMobiusHalfDensityGenerator
              (PolynomialTruncation.lowTrunc P (n + 1))) (n + 1))
          (X * PolynomialTruncation.lowTrunc P (n + 1)) +
        ((2 : ℝ) * n + 1) * P.coeff n *
          HTGeometry.momentInner (xiShiftedRealMomentSequence w)
            ((X : Polynomial ℝ) ^ (n + 1))
            (X * PolynomialTruncation.lowTrunc P (n + 1)) := by
  rw [xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource hw,
    xiShiftedAdaptiveMixedCompletedArithmeticSource_lowTrunc_eq_halfDensityBoundaryPort hw]

/-- **Canonical adaptive `P^sharp` source producer.**  For the actual monic moment admission,
the terminal coefficient is one.  Its completed arithmetic source therefore has the universal
port weight `2n+1`, with no frozen comparator and no additional positivity premise. -/
theorem xiShiftedCompletedMomentAggregate_canonicalAdmission_eq_halfDensityBoundaryPort
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    let A := HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n
    xiShiftedCompletedMomentAggregate (w ^ 2) 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket A)) =
      HTGeometry.momentInner (xiShiftedRealMomentSequence w) (X * A) (X * A) +
        2 * HTGeometry.momentInner (xiShiftedRealMomentSequence w)
          (PolynomialTruncation.lowTrunc
            (xiShiftedMobiusHalfDensityGenerator A) (n + 1)) (X * A) +
        ((2 : ℝ) * n + 1) *
          HTGeometry.momentInner (xiShiftedRealMomentSequence w)
            ((X : Polynomial ℝ) ^ (n + 1)) (X * A) := by
  dsimp only
  let A := HTGeometry.monicMomentAdmissionPolynomial
    (xiShiftedRealMomentSequence w) n
  have htrunc : PolynomialTruncation.lowTrunc A (n + 1) = A := by
    apply Polynomial.ext
    intro k
    by_cases hk : k < n + 1
    · exact PolynomialTruncation.coeff_lowTrunc_of_lt A hk
    · rw [PolynomialTruncation.coeff_lowTrunc_eq_zero_of_le A (by omega)]
      symm
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [show A.natDegree = n by
        exact HTGeometry.monicMomentAdmissionPolynomial_natDegree _ _]
      omega
  have htop : A.coeff n = 1 := by
    have h := (HTGeometry.monicMomentAdmissionPolynomial_monic
      (xiShiftedRealMomentSequence w) n).coeff_natDegree
    simpa only [HTGeometry.monicMomentAdmissionPolynomial_natDegree] using h
  have h := xiShiftedCompletedMomentAggregate_lowTrunc_eq_halfDensityBoundaryPort
    hw A n
  rw [htrunc, htop, mul_one] at h
  exact h

/-! ## Adaptive orthogonal landing: the source-native producer -/

/-- Current-flag part of the half-density source after removing its unique next orthogonal
direction.  Unlike coefficient truncation, this landing depends on the admitted moment form. -/
def xiShiftedAdaptiveHalfDensityLanding (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  xiShiftedMobiusHalfDensityGenerator (HTGeometry.monicOrtho s n) -
    ((n : ℝ) + 1 / 2) • HTGeometry.monicOrtho s (n + 1)

/-- Exact adaptive orthogonal split of the half-density source. -/
theorem xiShiftedMobiusHalfDensityGenerator_monicOrtho_eq_adaptiveLanding_add_boundary
    (s : ℕ → ℝ) (n : ℕ) :
    xiShiftedMobiusHalfDensityGenerator (HTGeometry.monicOrtho s n) =
      xiShiftedAdaptiveHalfDensityLanding s n +
        ((n : ℝ) + 1 / 2) • HTGeometry.monicOrtho s (n + 1) := by
  unfold xiShiftedAdaptiveHalfDensityLanding
  module

/-- The moment-adaptive landing lies inside the current degree-`n` admission. -/
theorem natDegree_xiShiftedAdaptiveHalfDensityLanding_le (s : ℕ → ℝ) (n : ℕ) :
    (xiShiftedAdaptiveHalfDensityLanding s n).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  by_cases htop : k = n + 1
  · subst k
    have hc : (HTGeometry.monicOrtho s (n + 1)).coeff (n + 1) = 1 :=
      HTGeometry.coeff_monicOrtho_self s (n + 1)
    rw [xiShiftedAdaptiveHalfDensityLanding, Polynomial.coeff_sub,
      Polynomial.coeff_smul, coeff_xiShiftedMobiusHalfDensityGenerator_succ,
      HTGeometry.coeff_monicOrtho_self, hc]
    ring
  · have hhigh : n + 1 < k := by omega
    cases k with
    | zero => omega
    | succ k =>
        rw [xiShiftedAdaptiveHalfDensityLanding, Polynomial.coeff_sub,
          Polynomial.coeff_smul, coeff_xiShiftedMobiusHalfDensityGenerator_succ]
        have hk0 : (HTGeometry.monicOrtho s n).coeff k = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [HTGeometry.natDegree_monicOrtho]
          omega
        have hk1 : (HTGeometry.monicOrtho s (n + 1)).coeff (k + 1) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [HTGeometry.natDegree_monicOrtho]
          omega
        rw [hk0, hk1]
        ring

/-- The adaptive terminal direction pairs with `X P_n` as exactly the next monic norm. -/
theorem momentInner_monicOrtho_succ_X_monicOrtho_eq_norm_below
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hnN : n + 2 ≤ N) :
    HTGeometry.momentInner s (HTGeometry.monicOrtho s (n + 1))
        (X * HTGeometry.monicOrtho s n) =
      HTGeometry.monicOrthoNormSq s (n + 1) := by
  rw [HTGeometry.X_mul_monicOrtho_below h (by omega),
    HTGeometry.momentInner_add_right, HTGeometry.momentInner_add_right,
    HTGeometry.momentInner_smul_right, HTGeometry.momentInner_smul_right]
  have hsame : HTGeometry.momentInner s (HTGeometry.monicOrtho s (n + 1))
      (HTGeometry.monicOrtho s n) = 0 :=
    HTGeometry.monicOrtho_inner_eq_zero_below h (by omega) (by omega) (by omega)
  have hlow : HTGeometry.momentInner s (HTGeometry.monicOrtho s (n + 1))
      (HTGeometry.monicOrtho s (n - 1)) = 0 :=
    HTGeometry.monicOrtho_inner_eq_zero_below h (by omega) (by omega) (by omega)
  rw [hsame, hlow]
  simp [HTGeometry.monicOrthoNormSq]

/-- The half-density connection cost is the adaptive admitted landing plus one positive terminal
norm channel. -/
theorem momentInner_xiShiftedMobiusHalfDensityGenerator_monicOrtho_eq_adaptiveLanding_add_boundary
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hnN : n + 2 ≤ N) :
    HTGeometry.momentInner s
        (xiShiftedMobiusHalfDensityGenerator (HTGeometry.monicOrtho s n))
        (X * HTGeometry.monicOrtho s n) =
      HTGeometry.momentInner s (xiShiftedAdaptiveHalfDensityLanding s n)
          (X * HTGeometry.monicOrtho s n) +
        ((n : ℝ) + 1 / 2) * HTGeometry.monicOrthoNormSq s (n + 1) := by
  have hp := congrArg
    (fun R : Polynomial ℝ => HTGeometry.momentInner s R
      (X * HTGeometry.monicOrtho s n))
    (xiShiftedMobiusHalfDensityGenerator_monicOrtho_eq_adaptiveLanding_add_boundary s n)
  rw [HTGeometry.momentInner_add_left, HTGeometry.momentInner_smul_left,
    momentInner_monicOrtho_succ_X_monicOrtho_eq_norm_below h hnN] at hp
  exact hp

/-- Source-first completed arithmetic landing in the adaptive orthogonal flag. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_eq_adaptiveLanding_add_boundary
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w)
      (n + 2)).PosDef) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) =
      HTGeometry.momentInner (xiShiftedRealMomentSequence w)
          (X * HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n)
          (X * HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) +
        2 * HTGeometry.momentInner (xiShiftedRealMomentSequence w)
          (xiShiftedAdaptiveHalfDensityLanding (xiShiftedRealMomentSequence w) n)
          (X * HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) +
        ((2 : ℝ) * n + 1) * HTGeometry.monicOrthoNormSq
          (xiShiftedRealMomentSequence w) (n + 1) := by
  let h := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [xiShiftedAdaptiveMixedCompletedArithmeticSource_eq_halfDensityLanding hw,
    momentInner_xiShiftedMobiusHalfDensityGenerator_monicOrtho_eq_adaptiveLanding_add_boundary
      h (by omega)]
  ring

/-- Multiplication Gram bulk in the orthogonal frame. -/
theorem momentInner_X_monicOrtho_sq_eq_norm_mul_jacobi_below
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    HTGeometry.momentInner s (X * HTGeometry.monicOrtho s n)
        (X * HTGeometry.monicOrtho s n) =
      HTGeometry.monicOrthoNormSq s n *
        (HTGeometry.monicOrthoBeta s (n + 1) +
          HTGeometry.monicOrthoAlpha s n ^ 2 +
          HTGeometry.monicOrthoBeta s n) := by
  rw [HTGeometry.X_mul_monicOrtho_below h (by omega)]
  simp only [HTGeometry.momentInner_add_left, HTGeometry.momentInner_add_right,
    HTGeometry.momentInner_smul_left, HTGeometry.momentInner_smul_right]
  have h10 : HTGeometry.momentInner s (HTGeometry.monicOrtho s (n + 1))
      (HTGeometry.monicOrtho s n) = 0 :=
    HTGeometry.monicOrtho_inner_eq_zero_below h (by omega) (by omega) (by omega)
  have h1m : HTGeometry.momentInner s (HTGeometry.monicOrtho s (n + 1))
      (HTGeometry.monicOrtho s (n - 1)) = 0 :=
    HTGeometry.monicOrtho_inner_eq_zero_below h (by omega) (by omega) (by omega)
  have h0m : HTGeometry.momentInner s (HTGeometry.monicOrtho s n)
      (HTGeometry.monicOrtho s (n - 1)) = 0 :=
    HTGeometry.monicOrtho_inner_eq_zero_below h (by omega) (by omega) (by omega)
  have h01 := HTGeometry.momentInner_comm s
    (HTGeometry.monicOrtho s n) (HTGeometry.monicOrtho s (n + 1))
  have hm1 := HTGeometry.momentInner_comm s
    (HTGeometry.monicOrtho s (n - 1)) (HTGeometry.monicOrtho s (n + 1))
  have hm0 := HTGeometry.momentInner_comm s
    (HTGeometry.monicOrtho s (n - 1)) (HTGeometry.monicOrtho s n)
  rw [h10] at h01
  rw [h1m] at hm1
  rw [h0m] at hm0
  simp only [mul_zero, add_zero, zero_add, h10, h1m, h0m, h01, hm1, hm0]
  rw [show HTGeometry.momentInner s (HTGeometry.monicOrtho s (n + 1))
      (HTGeometry.monicOrtho s (n + 1)) =
      HTGeometry.monicOrthoNormSq s (n + 1) by rfl,
    show HTGeometry.momentInner s (HTGeometry.monicOrtho s n)
      (HTGeometry.monicOrtho s n) = HTGeometry.monicOrthoNormSq s n by rfl,
    show HTGeometry.momentInner s (HTGeometry.monicOrtho s (n - 1))
      (HTGeometry.monicOrtho s (n - 1)) =
      HTGeometry.monicOrthoNormSq s (n - 1) by rfl]
  have hnext := HTGeometry.monicOrthoNormSq_mul_nextBeta (n := n) h
    (by omega : n + 1 < N)
  have hprev : HTGeometry.monicOrthoNormSq s (n - 1) *
      HTGeometry.monicOrthoBeta s n = HTGeometry.monicOrthoNormSq s n := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      (HTGeometry.monicOrthoNormSq_mul_nextBeta (n := n - 1) h (by omega))
  rw [← hnext, ← hprev]
  ring

/-- Positive energy carried by the part of `K P_n` that remains inside the adaptive flag. -/
def xiShiftedAdaptiveHalfDensityLandingEnergy (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n,
      (HTGeometry.monicOrthoAlpha s j + HTGeometry.monicOrthoAlpha s n / 2) ^ 2) +
    (3 * (n : ℝ) / 4 + 1 / 2) * HTGeometry.monicOrthoAlpha s n ^ 2 +
    2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
    ((n : ℝ) + 1 / 2) * HTGeometry.monicOrthoBeta s n

/-- Universal polynomial source identity behind the adaptive landing energy. -/
theorem two_mul_momentFunctional_adaptiveOrthoSourcePolynomial_eq_halfDensityLanding
    (s : ℕ → ℝ) (n : ℕ) :
    2 * HTGeometry.momentFunctional s (HTGeometry.adaptiveOrthoSourcePolynomial s n) =
      HTGeometry.momentInner s (X * HTGeometry.monicOrtho s n)
          (X * HTGeometry.monicOrtho s n) +
        2 * HTGeometry.momentInner s
          (xiShiftedMobiusHalfDensityGenerator (HTGeometry.monicOrtho s n))
          (X * HTGeometry.monicOrtho s n) := by
  rw [← HTGeometry.momentFunctional_smul, HTGeometry.momentInner_def,
    HTGeometry.momentInner_def, ← HTGeometry.momentFunctional_smul,
    ← HTGeometry.momentFunctional_add]
  apply congrArg (HTGeometry.momentFunctional s)
  simp only [HTGeometry.adaptiveOrthoSourcePolynomial,
    xiShiftedMobiusHalfDensityGenerator, xiShiftedMobiusDensityGenerator,
    Polynomial.smul_eq_C_mul]
  have hhalf : Polynomial.C (2 : ℝ) * Polynomial.C (1 / 2 : ℝ) = 1 := by
    rw [← Polynomial.C_mul]
    norm_num
  have htwo : (2 : Polynomial ℝ) = Polynomial.C (2 : ℝ) := by
    ext k
    cases k <;> simp
  linear_combination
    (-(X ^ 2 * HTGeometry.monicOrtho s n ^ 2)) * hhalf +
    (-(X ^ 2 * HTGeometry.monicOrtho s n ^ 2)) * htwo

/-- Exact evaluation of the adaptive admitted landing as norm times a positive Jacobi energy. -/
theorem momentInner_xiShiftedAdaptiveHalfDensityLanding_eq_norm_mul_energy_below
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    HTGeometry.momentInner s (xiShiftedAdaptiveHalfDensityLanding s n)
        (X * HTGeometry.monicOrtho s n) =
      HTGeometry.monicOrthoNormSq s n *
        xiShiftedAdaptiveHalfDensityLandingEnergy s n := by
  have hsource :=
    two_mul_momentFunctional_adaptiveOrthoSourcePolynomial_eq_halfDensityLanding s n
  rw [HTGeometry.momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy_below
      h hn hnN,
    momentInner_X_monicOrtho_sq_eq_norm_mul_jacobi_below h hn hnN,
    momentInner_xiShiftedMobiusHalfDensityGenerator_monicOrtho_eq_adaptiveLanding_add_boundary
      h hnN] at hsource
  have hnext := HTGeometry.monicOrthoNormSq_mul_nextBeta (n := n) h
    (by omega : n + 1 < N)
  rw [← hnext] at hsource
  unfold xiShiftedAdaptiveHalfDensityLandingEnergy
  unfold HTGeometry.adaptiveOrthoJacobiEnergy at hsource
  linear_combination (norm := ring) (-1 / 2 : ℝ) * hsource

/-- Strict positivity of the adaptive admitted landing energy. -/
theorem xiShiftedAdaptiveHalfDensityLandingEnergy_pos_below
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    0 < xiShiftedAdaptiveHalfDensityLandingEnergy s n := by
  have hsquares :
      0 ≤ ∑ j ∈ Finset.range n,
        (HTGeometry.monicOrthoAlpha s j + HTGeometry.monicOrthoAlpha s n / 2) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdiag :
      0 ≤ (3 * (n : ℝ) / 4 + 1 / 2) * HTGeometry.monicOrthoAlpha s n ^ 2 := by
    positivity
  have hinterior :
      0 ≤ 2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hlast :
      0 < ((n : ℝ) + 1 / 2) * HTGeometry.monicOrthoBeta s n :=
    mul_pos (by positivity) (HTGeometry.monicOrthoBeta_pos_below h hn (by omega))
  unfold xiShiftedAdaptiveHalfDensityLandingEnergy
  linarith

/-- The source-native landing remaining inside the current flag is itself strictly positive. -/
theorem momentInner_xiShiftedAdaptiveHalfDensityLanding_pos_below
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    0 < HTGeometry.momentInner s (xiShiftedAdaptiveHalfDensityLanding s n)
      (X * HTGeometry.monicOrtho s n) := by
  rw [momentInner_xiShiftedAdaptiveHalfDensityLanding_eq_norm_mul_energy_below h hn hnN]
  exact mul_pos (HTGeometry.monicOrthoNorm_pos_below h (by omega))
    (xiShiftedAdaptiveHalfDensityLandingEnergy_pos_below h hn hnN)

/-- **Three-positive-channel completed source law.**  Current adaptive admission splits the literal
completed mixed source into multiplication Gram bulk, strictly positive admitted landing energy,
and strictly positive terminal boundary norm. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_eq_threePositiveChannels
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w)
      (n + 2)).PosDef) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) =
      HTGeometry.momentInner (xiShiftedRealMomentSequence w)
          (X * HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n)
          (X * HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) +
        2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
          xiShiftedAdaptiveHalfDensityLandingEnergy (xiShiftedRealMomentSequence w) n +
        ((2 : ℝ) * n + 1) * HTGeometry.monicOrthoNormSq
          (xiShiftedRealMomentSequence w) (n + 1) := by
  let h := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_eq_adaptiveLanding_add_boundary
      hw hH,
    momentInner_xiShiftedAdaptiveHalfDensityLanding_eq_norm_mul_energy_below
      h hn (by omega)]
  ring

/-- **Missing adaptive completed `P^sharp` producer.**  The actual completed odd packet is the same
three-positive-channel source formed from the current monic orthogonal admission before reflection
aggregation. -/
theorem xiShiftedCompletedMomentAggregate_monicOrtho_eq_threePositiveHalfDensityChannels
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w)
      (n + 2)).PosDef) :
    let A := HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n
    xiShiftedCompletedMomentAggregate (w ^ 2) 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket A)) =
      HTGeometry.momentInner (xiShiftedRealMomentSequence w) (X * A) (X * A) +
        2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
          xiShiftedAdaptiveHalfDensityLandingEnergy (xiShiftedRealMomentSequence w) n +
        ((2 : ℝ) * n + 1) * HTGeometry.monicOrthoNormSq
          (xiShiftedRealMomentSequence w) (n + 1) := by
  dsimp only
  rw [xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource hw,
    xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_eq_threePositiveChannels
      hw hn hH]

/-- All three summands in the adaptive completed source law are individually strictly positive. -/
theorem xiShiftedAdaptiveHalfDensity_threeChannels_pos_below
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    0 < HTGeometry.momentInner s (X * HTGeometry.monicOrtho s n)
        (X * HTGeometry.monicOrtho s n) ∧
      0 < 2 * HTGeometry.monicOrthoNormSq s n *
        xiShiftedAdaptiveHalfDensityLandingEnergy s n ∧
      0 < ((2 : ℝ) * n + 1) * HTGeometry.monicOrthoNormSq s (n + 1) := by
  have hbulk : 0 < HTGeometry.momentInner s (X * HTGeometry.monicOrtho s n)
      (X * HTGeometry.monicOrtho s n) := by
    apply HTGeometry.PositiveMomentFormBelow.self_pos h
    · exact mul_ne_zero Polynomial.X_ne_zero (HTGeometry.monicOrtho_ne_zero s n)
    · rw [Polynomial.natDegree_mul Polynomial.X_ne_zero
          (HTGeometry.monicOrtho_ne_zero s n), Polynomial.natDegree_X,
        HTGeometry.natDegree_monicOrtho_eq]
      omega
  have hlanding : 0 < 2 * HTGeometry.monicOrthoNormSq s n *
      xiShiftedAdaptiveHalfDensityLandingEnergy s n := by
    exact mul_pos (mul_pos (by norm_num)
      (HTGeometry.monicOrthoNorm_pos_below h (by omega)))
      (xiShiftedAdaptiveHalfDensityLandingEnergy_pos_below h hn hnN)
  have hterminal : 0 < ((2 : ℝ) * n + 1) *
      HTGeometry.monicOrthoNormSq s (n + 1) := by
    exact mul_pos (by positivity)
      (HTGeometry.monicOrthoNorm_pos_below h (by omega))
  exact ⟨hbulk, hlanding, hterminal⟩

end

end RHTower
