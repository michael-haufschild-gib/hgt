import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveMixedSourceShear
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryPadeContactParity

/-!
# Adaptive shear and the first even Padé defect

At odd contact the source-selected adaptive shear is not an unspecified orientation scalar.  It
depends on exactly two normal coordinates: the first odd Padé defect and its first even successor.
This module proves that classification, identifies the two universal polynomial coefficients, and
shows sharply that odd-contact data alone cannot orient the shear because the successor coordinate
is free.
-/

open Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Polynomial carrying the even adaptive landing of an odd crossing amplitude. -/
def xiShiftedBoundaryAdaptiveShearPolynomial (A : Polynomial ℝ) : Polynomial ℝ :=
  (X * A) * (X * xiShiftedBoundaryShiftedEuler 1 A)

/-- The adaptive shear is one half of the Euler derivative of the squared odd amplitude. -/
theorem two_smul_xiShiftedBoundaryAdaptiveShearPolynomial
    (A : Polynomial ℝ) :
    (2 : ℝ) • xiShiftedBoundaryAdaptiveShearPolynomial A =
      X * ((X * A) ^ 2).derivative := by
  simp only [xiShiftedBoundaryAdaptiveShearPolynomial,
    xiShiftedBoundaryShiftedEuler, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_X, one_mul,
    C_1, Polynomial.smul_eq_C_mul]
  ring_nf

/-- A sequence vanishing below `K` sees only the top two coefficients of a polynomial whose degree
is at most `K+1`. -/
theorem momentFunctional_eq_two_top_of_sequence_eq_zero_below
    {a : ℕ → ℝ} {K : ℕ} (hzero : ∀ k < K, a k = 0)
    {Q : Polynomial ℝ} (hQdeg : Q.natDegree ≤ K + 1) :
    HTGeometry.momentFunctional a Q =
      Q.coeff K * a K + Q.coeff (K + 1) * a (K + 1) := by
  classical
  rw [HTGeometry.momentFunctional_eq_support_sum]
  calc
    (∑ k ∈ Q.support, Q.coeff k * a k) =
        ∑ k ∈ Q.support,
          if K = k then Q.coeff K * a K
          else if K + 1 = k then Q.coeff (K + 1) * a (K + 1)
          else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkK : k = K
      · subst k
        simp
      by_cases hkK1 : k = K + 1
      · subst k
        simp
      have hkcoeff : Q.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
      have hkle : k ≤ Q.natDegree := Polynomial.le_natDegree_of_ne_zero hkcoeff
      have hklt : k < K := by omega
      rw [hzero k hklt, mul_zero]
      simp [Ne.symm hkK, Ne.symm hkK1]
    _ = Q.coeff K * a K + Q.coeff (K + 1) * a (K + 1) := by
      calc
        (∑ k ∈ Q.support,
            if K = k then Q.coeff K * a K
            else if K + 1 = k then Q.coeff (K + 1) * a (K + 1)
            else 0) =
            (∑ k ∈ Q.support, if K = k then Q.coeff K * a K else 0) +
              ∑ k ∈ Q.support,
                if K + 1 = k then Q.coeff (K + 1) * a (K + 1) else 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkK : K = k
          · subst k
            simp
          by_cases hkK1 : K + 1 = k
          · subst k
            simp
          simp [hkK, hkK1]
        _ = Q.coeff K * a K + Q.coeff (K + 1) * a (K + 1) := by
          by_cases hK : Q.coeff K = 0 <;>
            by_cases hK1 : Q.coeff (K + 1) = 0 <;>
              simp [Polynomial.mem_support_iff, hK, hK1]

/-- Degree bound needed by the adjacent-defect reduction. -/
theorem natDegree_xiShiftedBoundaryAdaptiveShearPolynomial_le
    {A : Polynomial ℝ} {N : ℕ} (hA : A.Monic) (hAdeg : A.natDegree = N) :
    (xiShiftedBoundaryAdaptiveShearPolynomial A).natDegree ≤ 2 * N + 2 := by
  by_cases hN : N = 0
  · have hAone : A = 1 :=
      Polynomial.eq_one_of_monic_natDegree_zero hA (hAdeg.trans hN)
    subst N
    simp [hAone, xiShiftedBoundaryAdaptiveShearPolynomial,
      xiShiftedBoundaryShiftedEuler]
  have hderiv : A.derivative.natDegree ≤ N - 1 := by
    simpa only [hAdeg] using Polynomial.natDegree_derivative_le A
  have hXderiv : (X * A.derivative).natDegree ≤ N := by
    calc
      (X * A.derivative).natDegree ≤ X.natDegree + A.derivative.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ N := by simp; omega
  have hEuler : (xiShiftedBoundaryShiftedEuler 1 A).natDegree ≤ N := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le hXderiv ?_)
    simp only [Polynomial.C_1, one_mul]
    exact hAdeg.le
  have hXA : (X * A).natDegree ≤ N + 1 := by
    calc
      (X * A).natDegree ≤ X.natDegree + A.natDegree := Polynomial.natDegree_mul_le
      _ ≤ N + 1 := by simp [hAdeg]; omega
  have hXE : (X * xiShiftedBoundaryShiftedEuler 1 A).natDegree ≤ N + 1 := by
    calc
      (X * xiShiftedBoundaryShiftedEuler 1 A).natDegree ≤
          X.natDegree + (xiShiftedBoundaryShiftedEuler 1 A).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ N + 1 := by simp; omega
  calc
    (xiShiftedBoundaryAdaptiveShearPolynomial A).natDegree ≤
        (X * A).natDegree +
          (X * xiShiftedBoundaryShiftedEuler 1 A).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 2 * N + 2 := by omega

/-- Top adaptive-shear coefficient for a monic degree-`N` amplitude. -/
theorem coeff_xiShiftedBoundaryAdaptiveShearPolynomial_top
    {A : Polynomial ℝ} {N : ℕ} (hA : A.Monic) (hAdeg : A.natDegree = N) :
    (xiShiftedBoundaryAdaptiveShearPolynomial A).coeff (2 * N + 2) = N + 1 := by
  let B : Polynomial ℝ := (X * A) ^ 2
  have hXA : (X * A).Monic := Polynomial.monic_X.mul hA
  have hB : B.Monic := hXA.pow 2
  have hXAdeg : (X * A).natDegree = N + 1 := by
    calc
      (X * A).natDegree = X.natDegree + A.natDegree :=
        Polynomial.monic_X.natDegree_mul hA
      _ = N + 1 := by simp [hAdeg, Nat.add_comm]
  have hBdeg : B.natDegree = 2 * N + 2 := by
    dsimp only [B]
    rw [Polynomial.natDegree_pow, hXAdeg]
    omega
  have hcoeffB : B.coeff (2 * N + 2) = 1 := by
    rw [← hBdeg]
    exact hB.coeff_natDegree
  have hid := congrArg (fun Q : Polynomial ℝ => Q.coeff (2 * N + 2))
    (two_smul_xiShiftedBoundaryAdaptiveShearPolynomial A)
  change (2 : ℝ) * (xiShiftedBoundaryAdaptiveShearPolynomial A).coeff (2 * N + 2) =
    (X * B.derivative).coeff (2 * N + 2) at hid
  rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
    show 2 * N + 1 + 1 = 2 * N + 2 by omega, hcoeffB] at hid
  norm_num at hid ⊢
  linarith

/-- Subleading adaptive-shear coefficient. `nextCoeff` is the null-root barycenter coefficient and
also handles constant amplitudes without a separate edge case. -/
theorem coeff_xiShiftedBoundaryAdaptiveShearPolynomial_next
    {A : Polynomial ℝ} {N : ℕ} (hA : A.Monic) (hAdeg : A.natDegree = N) :
    (xiShiftedBoundaryAdaptiveShearPolynomial A).coeff (2 * N + 1) =
      (2 * N + 1 : ℕ) * A.nextCoeff := by
  let B : Polynomial ℝ := (X * A) ^ 2
  have hXA : (X * A).Monic := Polynomial.monic_X.mul hA
  have hB : B.Monic := hXA.pow 2
  have hXAdeg : (X * A).natDegree = N + 1 := by
    calc
      (X * A).natDegree = X.natDegree + A.natDegree :=
        Polynomial.monic_X.natDegree_mul hA
      _ = N + 1 := by simp [hAdeg, Nat.add_comm]
  have hBdeg : B.natDegree = 2 * N + 2 := by
    dsimp only [B]
    rw [Polynomial.natDegree_pow, hXAdeg]
    omega
  have hBpos : 0 < B.natDegree := by omega
  have hnextXA : (X * A).nextCoeff = A.nextCoeff := by
    rw [Polynomial.monic_X.nextCoeff_mul hA]
    norm_num [Polynomial.nextCoeff]
  have hnextB : B.nextCoeff = 2 * A.nextCoeff := by
    dsimp only [B]
    rw [hXA.nextCoeff_pow, hnextXA]
    simp
  have hcoeffB : B.coeff (2 * N + 1) = 2 * A.nextCoeff := by
    have hidx : 2 * N + 2 - 1 = 2 * N + 1 := by omega
    calc
      B.coeff (2 * N + 1) = B.nextCoeff := by
        rw [Polynomial.nextCoeff_of_natDegree_pos hBpos, hBdeg, hidx]
      _ = 2 * A.nextCoeff := hnextB
  have hid := congrArg (fun Q : Polynomial ℝ => Q.coeff (2 * N + 1))
    (two_smul_xiShiftedBoundaryAdaptiveShearPolynomial A)
  change (2 : ℝ) * (xiShiftedBoundaryAdaptiveShearPolynomial A).coeff (2 * N + 1) =
    (X * B.derivative).coeff (2 * N + 1) at hid
  rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, hcoeffB] at hid
  push_cast at hid ⊢
  linarith

/-- Multiplying a monic polynomial by a power of `X` does not change its second-highest
coefficient. This is the null-root barycenter retained by every parity lift. -/
theorem nextCoeff_mul_X_pow_of_monic
    {P : Polynomial ℝ} (hP : P.Monic) (m : ℕ) :
    (P * X ^ m).nextCoeff = P.nextCoeff := by
  rw [hP.nextCoeff_mul (Polynomial.monic_X_pow m)]
  have hXnext : (X : Polynomial ℝ).nextCoeff = 0 := by
    norm_num [Polynomial.nextCoeff]
  rw [Polynomial.monic_X.nextCoeff_pow, hXnext]
  simp

/-- Canonical flat quadrature vanishes on every polynomial with one null-polynomial factor. -/
theorem momentFunctional_finiteHankelBoundaryPadeDefect_null_mul
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (Q : Polynomial ℝ) :
    HTGeometry.momentFunctional
        (HTGeometry.finiteHankelBoundaryPadeDefect s c)
        (HTGeometry.finiteHankelNullMonicPolynomial c * Q) =
      HTGeometry.momentFunctional s
        (HTGeometry.finiteHankelNullMonicPolynomial c * Q) := by
  let q : ℕ → ℝ := fun k =>
    ∑ x ∈ HTGeometry.finiteHankelBoundaryNodes c,
      HTGeometry.finiteHankelBoundaryWeight s c x * x ^ k
  have hq : HTGeometry.momentFunctional q
      (HTGeometry.finiteHankelNullMonicPolynomial c * Q) = 0 := by
    rw [momentFunctional_finiteAtomicMoment]
    apply Finset.sum_eq_zero
    intro x hx
    rw [eval_mul,
      HTGeometry.finiteHankelNullMonicPolynomial_eval_eq_zero_of_mem c hx]
    simp
  change HTGeometry.momentFunctional (fun k => s k - q k)
      (HTGeometry.finiteHankelNullMonicPolynomial c * Q) = _
  rw [momentFunctional_sequence_sub, hq, sub_zero]

/-- **Adjacent-defect classification.** At odd contact the full adaptive shear is exactly the
affine combination of the first odd defect and its first even successor. -/
theorem xiShiftedHankelBoundary_adaptiveShear_eq_adjacentDefects
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (xiShiftedBoundaryAdaptiveShearPolynomial A) =
      ((2 * (n + m) + 1 : ℕ) : ℝ) * P.nextCoeff *
          xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1)) +
        ((n + m + 1 : ℕ) : ℝ) *
          xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1) + 1) := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  let K := 2 * n + (2 * m + 1)
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hA : A.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hAdeg : A.natDegree = n + m := by
    dsimp only [A]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m), hPdeg,
      Polynomial.natDegree_X_pow]
  have hfactor : ∃ Q : Polynomial ℝ,
      xiShiftedBoundaryAdaptiveShearPolynomial A = P * Q := by
    refine ⟨X ^ (m + 1) * (X * xiShiftedBoundaryShiftedEuler 1 A), ?_⟩
    dsimp only [xiShiftedBoundaryAdaptiveShearPolynomial, A]
    ring
  obtain ⟨Q, hQ⟩ := hfactor
  have hdefect : HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re)
      (xiShiftedBoundaryAdaptiveShearPolynomial A) =
    HTGeometry.momentFunctional (xiShiftedHankelBoundaryPadeDefect y c)
      (xiShiftedBoundaryAdaptiveShearPolynomial A) := by
    rw [hQ]
    exact (momentFunctional_finiteHankelBoundaryPadeDefect_null_mul
      (fun k => (xiShiftedReciprocalMoment y k).re) c Q).symm
  rw [hdefect]
  have hdeg : (xiShiftedBoundaryAdaptiveShearPolynomial A).natDegree ≤ K + 1 := by
    apply (natDegree_xiShiftedBoundaryAdaptiveShearPolynomial_le hA hAdeg).trans
    dsimp only [K]
    omega
  rw [momentFunctional_eq_two_top_of_sequence_eq_zero_below hzero hdeg]
  rw [show 2 * n + (2 * m + 1) = 2 * (n + m) + 1 by omega,
    coeff_xiShiftedBoundaryAdaptiveShearPolynomial_next hA hAdeg,
    show 2 * (n + m) + 1 + 1 = 2 * (n + m) + 2 by omega,
    coeff_xiShiftedBoundaryAdaptiveShearPolynomial_top hA hAdeg,
    nextCoeff_mul_X_pow_of_monic hP m]
  push_cast
  ring

/-- **Completed arithmetic source law.** The adaptive mixed-amplitude packet selected by one mass
derivative is twice the adjacent odd/even Padé-defect scalar. -/
theorem xiShiftedCompletedMomentAggregate_adaptiveNullPacket_eq_adjacentDefects
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    xiShiftedCompletedMomentAggregate y 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket A)) =
      2 *
        (((2 * (n + m) + 1 : ℕ) : ℝ) * P.nextCoeff *
            xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1)) +
          ((n + m + 1 : ℕ) : ℝ) *
            xiShiftedHankelBoundaryPadeDefect y c
              (2 * n + (2 * m + 1) + 1)) := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  rw [xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_two_shear hy]
  rw [HTGeometry.momentInner_def]
  change 2 * HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re)
      (xiShiftedBoundaryAdaptiveShearPolynomial A) = _
  rw [xiShiftedHankelBoundary_adaptiveShear_eq_adjacentDefects c hlast hzero]

/-- Source-only prime--Gamma form of the same adjacent-defect law in the negative-binomial
convergence window. -/
theorem primeArch_adaptiveShear_eq_adjacentDefects
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    HTGeometry.momentFunctional
        (fun k => (primeArchShiftedReciprocalMoment y k).re)
        (xiShiftedBoundaryAdaptiveShearPolynomial A) =
      ((2 * (n + m) + 1 : ℕ) : ℝ) * P.nextCoeff *
          xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1)) +
        ((n + m + 1 : ℕ) : ℝ) *
          xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1) + 1) := by
  dsimp only
  have hseq : (fun k => (primeArchShiftedReciprocalMoment y k).re) =
      (fun k => (xiShiftedReciprocalMoment y k).re) := by
    funext k
    rw [xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy.le hymax]
  rw [hseq]
  exact xiShiftedHankelBoundary_adaptiveShear_eq_adjacentDefects c hlast hzero

/-- **Admission-sensitive source derivative.** At odd contact, differentiation of actual admitted
null current lands directly on the adjacent-defect scalar. -/
theorem hasDerivAt_xiShiftedMomentInner_admittedOddContact_eq_adjacentDefects
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re) A (X * A))
      (-2 *
        (((2 * (n + m) + 1 : ℕ) : ℝ) * P.nextCoeff *
            xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1)) +
          ((n + m + 1 : ℕ) : ℝ) *
            xiShiftedHankelBoundaryPadeDefect y c
              (2 * n + (2 * m + 1) + 1))) y := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  have hderiv := hasDerivAt_xiShiftedMomentInner_oddCrossing_eq_adaptiveShear hy A
  have hclass := xiShiftedHankelBoundary_adaptiveShear_eq_adjacentDefects
    c hlast hzero
  rw [HTGeometry.momentInner_def] at hderiv
  change HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re)
      ((X * A) * (X * xiShiftedBoundaryShiftedEuler 1 A)) = _ at hclass
  rw [hclass] at hderiv
  exact hderiv

/-- A one-coordinate perturbation at the first even successor changes adaptive shear by exactly
`(N+1)δ`. -/
theorem momentFunctional_momentCoordinatePerturbation_adaptiveShear
    (a : ℕ → ℝ) {A : Polynomial ℝ} {N : ℕ}
    (hA : A.Monic) (hAdeg : A.natDegree = N) (δ : ℝ) :
    HTGeometry.momentFunctional
        (HTGeometry.momentCoordinatePerturbation a (2 * N + 2) δ)
        (xiShiftedBoundaryAdaptiveShearPolynomial A) =
      HTGeometry.momentFunctional a (xiShiftedBoundaryAdaptiveShearPolynomial A) +
        δ * (N + 1) := by
  rw [HTGeometry.momentFunctional_momentCoordinatePerturbation,
    coeff_xiShiftedBoundaryAdaptiveShearPolynomial_top hA hAdeg]

/-- **Sharp odd-contact orientation no-go.** Keeping every defect coordinate through the first odd
contact fixed, the adaptive shear can be assigned any prescribed real value by changing only its
first even successor. -/
theorem exists_sequence_eq_below_adaptiveShear_eq
    (a : ℕ → ℝ) {A : Polynomial ℝ} {N : ℕ}
    (hA : A.Monic) (hAdeg : A.natDegree = N) (r : ℝ) :
    ∃ t : ℕ → ℝ,
      (∀ k < 2 * N + 2, t k = a k) ∧
        HTGeometry.momentFunctional t
          (xiShiftedBoundaryAdaptiveShearPolynomial A) = r := by
  let δ : ℝ :=
    (r - HTGeometry.momentFunctional a
      (xiShiftedBoundaryAdaptiveShearPolynomial A)) / (N + 1)
  refine ⟨HTGeometry.momentCoordinatePerturbation a (2 * N + 2) δ, ?_, ?_⟩
  · intro k hk
    simp [HTGeometry.momentCoordinatePerturbation, Nat.ne_of_lt hk]
  · rw [momentFunctional_momentCoordinatePerturbation_adaptiveShear
      a hA hAdeg δ]
    dsimp only [δ]
    have hne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hne]
    ring

end

end RHTower
