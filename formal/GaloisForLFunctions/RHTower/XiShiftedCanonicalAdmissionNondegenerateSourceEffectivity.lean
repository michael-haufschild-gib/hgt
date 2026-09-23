import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdjacentEdgeArithmeticAction
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionDegreeCenteredArithmeticSource

/-!
# Nondegenerate adaptive arithmetic source pays admission effectivity

Gaussian observation is not needed to pay motion of current admission.  The adjacent
nondegenerate null-flag completion already contains, inside its source polynomial, the admitted
trace square, current diagonal square, lower Jacobi history, and a unit reserve.

The sharp two-coordinate Cauchy weight therefore controls current logarithmic norm velocity by
the literal adjacent-amplitude rational--Gamma/von-Mangoldt `P^sharp` source.  Admission of both
amplitudes occurs before completed aggregation.  The final law is division-free.
-/

open Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Sharp dual quadratic weight for admitted trace and current diagonal channels. -/
def xiShiftedNondegenerateSourceEffectivityWeight (n : ℕ) : ℝ :=
  (2 * n + 1 : ℝ) ^ (2 : ℕ) + 2

theorem xiShiftedNondegenerateSourceEffectivityWeight_pos (n : ℕ) :
    0 < xiShiftedNondegenerateSourceEffectivityWeight n := by
  unfold xiShiftedNondegenerateSourceEffectivityWeight
  positivity

/-- Unit odd channel forces one full normalized source quantum. -/
theorem one_le_nondegenerateNullFlagCompletedJacobiHistory
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hnN : n ≤ N) :
    1 ≤ HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s n := by
  have hsquares : 0 ≤ ∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  unfold HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
  nlinarith [sq_nonneg (HTGeometry.monicOrthoFirstCoeff s n),
    sq_nonneg (HTGeometry.monicOrthoAlpha s n)]

/-- Removing exactly the unit null-flag vacuum leaves nonnegative causal history. -/
theorem nonneg_nondegenerateNullFlagCompletedJacobiHistory_sub_one
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hnN : n ≤ N) :
    0 ≤ HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s n - 1 :=
  sub_nonneg.mpr (one_le_nondegenerateNullFlagCompletedJacobiHistory h hnN)

/-- **Universal null-flag source/effectivity coercivity.**  Nondegenerate completed causal
history pays squared effectivity and one full unit reserve.  This is algebra on actual Jacobi
coordinates, not an orientation or observation theorem. -/
theorem jacobiEffectivity_sq_add_weight_le_weight_mul_nondegenerateHistory
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hnN : n ≤ N) :
    (-2 * HTGeometry.monicOrthoFirstCoeff s n +
          (2 * n + 1 : ℝ) * HTGeometry.monicOrthoAlpha s n) ^ (2 : ℕ) +
        xiShiftedNondegenerateSourceEffectivityWeight n ≤
      xiShiftedNondegenerateSourceEffectivityWeight n *
        HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s n := by
  let f := HTGeometry.monicOrthoFirstCoeff s n
  let a := HTGeometry.monicOrthoAlpha s n
  let c : ℝ := 2 * n + 1
  let K := xiShiftedNondegenerateSourceEffectivityWeight n
  have hK : 0 ≤ K := (xiShiftedNondegenerateSourceEffectivityWeight_pos n).le
  have hsquares : 0 ≤ ∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hdual : (-2 * f + c * a) ^ (2 : ℕ) ≤ K * (2 * f ^ (2 : ℕ) + a ^ (2 : ℕ)) := by
    have hsq := sq_nonneg (c * f + a)
    dsimp only [K, c]
    unfold xiShiftedNondegenerateSourceEffectivityWeight
    nlinarith
  have hhistory :
      2 * f ^ (2 : ℕ) + a ^ (2 : ℕ) + 1 ≤
        HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s n := by
    unfold HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
    dsimp only [f, a]
    nlinarith
  have hweighted := mul_le_mul_of_nonneg_left hhistory hK
  dsimp only [f, a, c, K] at hdual hweighted ⊢
  nlinarith

/-- **Vacuum-free universal coercivity.**  Unit channel is not needed to pay effectivity: after
subtracting it inside source, remaining causal squares and positive edges still control full
admission rate. -/
theorem jacobiEffectivity_sq_le_weight_mul_nondegenerateHistory_sub_one
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hnN : n ≤ N) :
    (-2 * HTGeometry.monicOrthoFirstCoeff s n +
          (2 * n + 1 : ℝ) * HTGeometry.monicOrthoAlpha s n) ^ (2 : ℕ) ≤
      xiShiftedNondegenerateSourceEffectivityWeight n *
        (HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s n - 1) := by
  let f := HTGeometry.monicOrthoFirstCoeff s n
  let a := HTGeometry.monicOrthoAlpha s n
  let c : ℝ := 2 * n + 1
  let K := xiShiftedNondegenerateSourceEffectivityWeight n
  have hK : 0 ≤ K := (xiShiftedNondegenerateSourceEffectivityWeight_pos n).le
  have hsquares : 0 ≤ ∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hdual : (-2 * f + c * a) ^ (2 : ℕ) ≤ K * (2 * f ^ (2 : ℕ) + a ^ (2 : ℕ)) := by
    have hsq := sq_nonneg (c * f + a)
    dsimp only [K, c]
    unfold xiShiftedNondegenerateSourceEffectivityWeight
    nlinarith
  have hhistory :
      2 * f ^ (2 : ℕ) + a ^ (2 : ℕ) ≤
        HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s n - 1 := by
    unfold HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
    dsimp only [f, a]
    nlinarith
  have hweighted := mul_le_mul_of_nonneg_left hhistory hK
  dsimp only [f, a, c, K] at hdual hweighted ⊢
  exact hdual.trans hweighted

/-! ## Unit-renormalized source formed before completed aggregation -/

/-- Remove unit null-flag vacuum inside adaptive adjacent-amplitude shear polynomial. -/
def xiShiftedBoundaryUnitRenormalizedNondegenerateNullFlagShearPolynomial
    (n : ℕ) (A B : Polynomial ℝ) : Polynomial ℝ :=
  xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial n A B - A ^ (2 : ℕ)

/-- Literal unit-renormalized rational--Gamma/von-Mangoldt source.  Subtraction is performed on
source polynomial before completed aggregation. -/
def xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource
    (w : ℝ) (n : ℕ) (A B : Polynomial ℝ) : ℝ :=
  2 * xiShiftedPolynomialCompletedArithmeticSource w
    (xiShiftedBoundaryUnitRenormalizedNondegenerateNullFlagShearPolynomial n A B)

/-- Actual square-mass producer from two current inverse-Hankel admissions. -/
def xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass
    (y : ℝ) (n : ℕ) : ℝ :=
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  2 * HTGeometry.momentFunctional s
    (xiShiftedBoundaryUnitRenormalizedNondegenerateNullFlagShearPolynomial n
      (HTGeometry.monicMomentAdmissionPolynomial s n)
      (HTGeometry.monicMomentAdmissionPolynomial s (n + 1)))

/-- Unit renormalization is exactly full nondegenerate source minus twice current norm. -/
theorem xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass_eq_sub_norm
    (y : ℝ) (n : ℕ) :
    xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n =
      xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass y n -
        2 * xiShiftedCanonicalAdmissionNorm y n := by
  simp only [xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass,
    xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass,
    xiShiftedBoundaryUnitRenormalizedNondegenerateNullFlagShearPolynomial,
    xiShiftedCanonicalAdmissionNorm]
  rw [HTGeometry.momentFunctional_sub, HTGeometry.momentInner_def]
  ring

/-- At physical square mass, unit-renormalized mass source is literal completed arithmetic
formation of renormalized adjacent-amplitude polynomial. -/
theorem xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass_sq_eq_arithmetic
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass (w ^ (2 : ℕ)) n =
      xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n)
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) (n + 1)) := by
  rw [xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw]
  rfl

/-- **Vacuum-free odd-to-even null-flag landing.**  Removing the unit vacuum inside the source
polynomial does not weaken singular-face production: `A²` has zero moment on the visible null
flag, so the first odd Padé defect still lands with nonzero coefficient two in the even adaptive
mixed/completed `P^sharp` aggregate.  Adjacent amplitude is arbitrary and chosen before completed
aggregation. -/
theorem xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource_liftedNull_eq_two_mul_firstOddDefect
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c k = 0)
    (B : Polynomial ℝ) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource w (n + m) A B =
      2 * xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c
        (2 * n + (2 * m + 1)) := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hA : A.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hAdeg : A.natDegree = n + m := by
    dsimp only [A]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m), hPdeg,
      Polynomial.natDegree_X_pow]
  have hAsqFactor : ∃ R : Polynomial ℝ, A ^ (2 : ℕ) = P * R := by
    refine ⟨P * X ^ (2 * m), ?_⟩
    dsimp only [A]
    ring
  have hAsqMoment :
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) (A ^ (2 : ℕ)) = 0 := by
    obtain ⟨R, hAR⟩ := hAsqFactor
    have hdefect :
        HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) (A ^ (2 : ℕ)) =
          HTGeometry.momentFunctional
            (xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c) (A ^ (2 : ℕ)) := by
      rw [hAR]
      exact (momentFunctional_finiteHankelBoundaryPadeDefect_null_mul
        (xiShiftedRealMomentSequence w) c R).symm
    rw [hdefect]
    apply HTGeometry.momentFunctional_eq_zero_of_sequence_eq_zero_below hzero
    rw [hA.natDegree_pow, hAdeg]
    omega
  have hfull :=
    xiShiftedNondegenerateNullFlagCompletedArithmeticSource_liftedNull_eq_two_mul_firstOddDefect
      hw hn c hlast hzero B
  dsimp only at hfull
  rw [xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_momentFunctional hw] at hfull
  rw [xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw,
    xiShiftedBoundaryUnitRenormalizedNondegenerateNullFlagShearPolynomial,
    HTGeometry.momentFunctional_sub, hAsqMoment]
  simpa only [sub_zero] using hfull

/-- Exact current-admission realization of nondegenerate source as norm times manifest Jacobi
history.  Both adjacent inverse-Hankel amplitudes are chosen before source formation. -/
theorem xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_eq_norm_mul_history
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef) :
    xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass y n =
      2 * xiShiftedCanonicalAdmissionNorm y n *
        HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
          (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  change (HTGeometry.momentHankelMatrix s (n + 2)).PosDef at hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hPn : HTGeometry.monicMomentAdmissionPolynomial s n =
      HTGeometry.monicOrtho s n :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef
      (xiShiftedMomentHankel_posDef_of_le (by omega) hH)
  have hPnext : HTGeometry.monicMomentAdmissionPolynomial s (n + 1) =
      HTGeometry.monicOrtho s (n + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef
      (xiShiftedMomentHankel_posDef_of_le (by omega) hH)
  rw [xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass,
    hPn, hPnext,
    xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial_monicOrtho
      hbelow hn (by omega : n + 2 ≤ n + 2),
    HTGeometry.momentFunctional_nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial_eq_history_below
      hbelow hn (by omega : n + 2 ≤ n + 2),
    xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
  dsimp only [s]
  ring

/-- Exact vacuum-free source law in current Jacobi coordinates. -/
theorem xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass_eq_norm_mul_history_sub_one
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef) :
    xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n =
      2 * xiShiftedCanonicalAdmissionNorm y n *
        (HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
          (fun k => (xiShiftedReciprocalMoment y k).re) n - 1) := by
  rw [xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass_eq_sub_norm,
    xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_eq_norm_mul_history
      hn hH]
  ring

/-- Vacuum-free source is nonnegative on every positive adjacent chamber. -/
theorem xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass_nonneg
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef) :
    0 ≤ xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  change (HTGeometry.momentHankelMatrix s (n + 2)).PosDef at hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : 0 ≤ xiShiftedCanonicalAdmissionNorm y n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
    exact (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)).le
  have hhistory := nonneg_nondegenerateNullFlagCompletedJacobiHistory_sub_one
    hbelow (n := n) (by omega : n ≤ n + 2)
  rw [xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass_eq_norm_mul_history_sub_one
    hn hH]
  positivity

/-- **Division-free vacuum-free effectivity law.**  Renormalized adaptive mixed/completed source
pays squared logarithmic admission velocity with no constant source floor. -/
theorem two_mul_norm_mul_effectivity_sq_le_weight_mul_unitRenormalizedSourceMass
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef) :
    2 * xiShiftedCanonicalAdmissionNorm y n *
        xiShiftedCanonicalAdmissionEffectivityRate y n ^ (2 : ℕ) ≤
      xiShiftedNondegenerateSourceEffectivityWeight n *
        xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  change (HTGeometry.momentHankelMatrix s (n + 2)).PosDef at hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : 0 ≤ xiShiftedCanonicalAdmissionNorm y n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
    exact (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)).le
  have hcoercive :=
    jacobiEffectivity_sq_le_weight_mul_nondegenerateHistory_sub_one
      hbelow (n := n) (by omega : n ≤ n + 2)
  rw [xiShiftedCanonicalAdmissionEffectivityRate,
    xiShiftedCanonicalAdmissionFirstCoeff_eq_monicOrthoFirstCoeff hn hH,
    xiShiftedCanonicalAdmissionAlpha_eq_monicOrthoAlpha hH]
  rw [xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass_eq_norm_mul_history_sub_one
    hn hH]
  have hfactor : 0 ≤ 2 * xiShiftedCanonicalAdmissionNorm y n :=
    mul_nonneg (by norm_num) hnorm
  have hscaled := mul_le_mul_of_nonneg_left hcoercive hfactor
  dsimp only [s] at hscaled
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Quotient source has no vacuum term and directly pays effectivity wherever admission is
positive. -/
theorem effectivity_sq_le_weight_mul_unitRenormalizedSourceMass_div_norm
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionEffectivityRate y n ^ (2 : ℕ) ≤
      xiShiftedNondegenerateSourceEffectivityWeight n *
        (xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n /
          (2 * xiShiftedCanonicalAdmissionNorm y n)) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  change (HTGeometry.momentHankelMatrix s (n + 2)).PosDef at hH
  have hnorm : 0 < xiShiftedCanonicalAdmissionNorm y n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
  have hsource :=
    two_mul_norm_mul_effectivity_sq_le_weight_mul_unitRenormalizedSourceMass hn hH
  calc
    xiShiftedCanonicalAdmissionEffectivityRate y n ^ (2 : ℕ) ≤
        (xiShiftedNondegenerateSourceEffectivityWeight n *
          xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n) /
            (2 * xiShiftedCanonicalAdmissionNorm y n) := by
      apply (le_div_iff₀ (mul_pos (by norm_num) hnorm)).2
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hsource
    _ = xiShiftedNondegenerateSourceEffectivityWeight n *
        (xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n /
          (2 * xiShiftedCanonicalAdmissionNorm y n)) := by ring

/-- Literal source-first square-mass capstone for vacuum-free producer. -/
theorem literal_unitRenormalizedAdaptiveMixedSource_pays_admissionEffectivity
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    2 * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
        xiShiftedCanonicalAdmissionEffectivityRate (w ^ (2 : ℕ)) n ^ (2 : ℕ) ≤
      xiShiftedNondegenerateSourceEffectivityWeight n *
        xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource w n
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n)
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) (n + 1)) := by
  have hmass : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 2)).PosDef := hH
  have hsource :=
    two_mul_norm_mul_effectivity_sq_le_weight_mul_unitRenormalizedSourceMass hn hmass
  rw [xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass_sq_eq_arithmetic
    hw n] at hsource
  exact hsource

/-- **Normalized-budget no-go.**  Unit null-flag channel makes source at least twice current
admitted norm in every positive chamber.  Thus source divided by `2N_n` has a universal floor
one and cannot be integrated over an infinite mass ray as a finite budget. -/
theorem two_mul_norm_le_xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef) :
    2 * xiShiftedCanonicalAdmissionNorm y n ≤
      xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  change (HTGeometry.momentHankelMatrix s (n + 2)).PosDef at hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : 0 ≤ xiShiftedCanonicalAdmissionNorm y n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
    exact (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)).le
  have hfloor := one_le_nondegenerateNullFlagCompletedJacobiHistory
    hbelow (n := n) (by omega : n ≤ n + 2)
  rw [xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_eq_norm_mul_history
    hn hH]
  nlinarith

/-- Quotient form of normalized-budget no-go. -/
theorem one_le_xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_div_norm
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef) :
    1 ≤ xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass y n /
      (2 * xiShiftedCanonicalAdmissionNorm y n) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  change (HTGeometry.momentHankelMatrix s (n + 2)).PosDef at hH
  have hnorm : 0 < xiShiftedCanonicalAdmissionNorm y n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
  apply (le_div_iff₀ (mul_pos (by norm_num) hnorm)).2
  simpa only [one_mul] using
    (two_mul_norm_le_xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass hn hH)

/-- **Division-free adaptive mixed/completed `P^sharp` effectivity law.**  Actual adjacent
admissions form nondegenerate null-flag source before rational--Gamma/von-Mangoldt aggregation.
That arithmetic producer pays squared logarithmic norm velocity and a unit reserve. -/
theorem two_mul_norm_mul_effectivity_sq_add_weight_le_weight_mul_nondegenerateSourceMass
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef) :
    2 * xiShiftedCanonicalAdmissionNorm y n *
        (xiShiftedCanonicalAdmissionEffectivityRate y n ^ (2 : ℕ) +
          xiShiftedNondegenerateSourceEffectivityWeight n) ≤
      xiShiftedNondegenerateSourceEffectivityWeight n *
        xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  change (HTGeometry.momentHankelMatrix s (n + 2)).PosDef at hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : 0 < xiShiftedCanonicalAdmissionNorm y n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
    exact HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hcoercive :=
    jacobiEffectivity_sq_add_weight_le_weight_mul_nondegenerateHistory
      hbelow (n := n) (by omega : n ≤ n + 2)
  rw [xiShiftedCanonicalAdmissionEffectivityRate,
    xiShiftedCanonicalAdmissionFirstCoeff_eq_monicOrthoFirstCoeff hn hH,
    xiShiftedCanonicalAdmissionAlpha_eq_monicOrthoAlpha hH]
  rw [xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_eq_norm_mul_history
    hn hH]
  have hfactor : 0 ≤ 2 * xiShiftedCanonicalAdmissionNorm y n :=
    mul_nonneg (by norm_num) hnorm.le
  have hscaled := mul_le_mul_of_nonneg_left hcoercive hfactor
  dsimp only [s] at hscaled
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Literal square-mass form: current and next canonical amplitudes enter the completed
`P^sharp` aggregate itself.  No Gaussian observer, orientation character, or fixed reporter
appears. -/
theorem literal_nondegenerateAdaptiveMixedSource_pays_admissionEffectivity
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    2 * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
        (xiShiftedCanonicalAdmissionEffectivityRate (w ^ (2 : ℕ)) n ^ (2 : ℕ) +
          xiShiftedNondegenerateSourceEffectivityWeight n) ≤
      xiShiftedNondegenerateSourceEffectivityWeight n *
        xiShiftedNondegenerateNullFlagCompletedArithmeticSource w n
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n)
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) (n + 1)) := by
  have hmass : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 2)).PosDef := by
    exact hH
  have hsource :=
    two_mul_norm_mul_effectivity_sq_add_weight_le_weight_mul_nondegenerateSourceMass
      hn hmass
  rw [xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_sq_eq_arithmetic hw] at hsource
  exact hsource

set_option maxHeartbeats 600000 in
/-- **Adjacent division-free arithmetic action.**  Weighting neighboring source laws by the
opposite admitted norm produces one symmetric degree-renewal aggregate.  It pays shared-edge
logarithmic velocity and two unit reserves without ever dividing by a collapsing norm. -/
theorem adjacent_norm_product_mul_effectivity_difference_sq_add_reserve_le_mixed_sources
    {y : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hH : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionNorm y n *
          xiShiftedCanonicalAdmissionNorm y (n - 1) *
          (xiShiftedCanonicalAdmissionEffectivityRate y (n - 1) -
            xiShiftedCanonicalAdmissionEffectivityRate y n) ^ (2 : ℕ) +
        2 * (xiShiftedNondegenerateSourceEffectivityWeight n +
            xiShiftedNondegenerateSourceEffectivityWeight (n - 1)) *
          xiShiftedCanonicalAdmissionNorm y n *
          xiShiftedCanonicalAdmissionNorm y (n - 1) ≤
      xiShiftedNondegenerateSourceEffectivityWeight n *
          xiShiftedCanonicalAdmissionNorm y (n - 1) *
          xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass y n +
        xiShiftedNondegenerateSourceEffectivityWeight (n - 1) *
          xiShiftedCanonicalAdmissionNorm y n *
          xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass y (n - 1) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hH' : (HTGeometry.momentHankelMatrix s (n + 2)).PosDef := hH
  have hHprev' : (HTGeometry.momentHankelMatrix s ((n - 1) + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH'
  have hHprev : (xiShiftedMomentHankelMatrix y ((n - 1) + 2)).PosDef := hHprev'
  have hN : 0 ≤ xiShiftedCanonicalAdmissionNorm y n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH']
    exact (HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH') (by omega)).le
  have hP : 0 ≤ xiShiftedCanonicalAdmissionNorm y (n - 1) := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hHprev']
    exact (HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hHprev') (by omega)).le
  have hcur :=
    two_mul_norm_mul_effectivity_sq_add_weight_le_weight_mul_nondegenerateSourceMass
      (y := y) (n := n) (by omega) hH
  have hprev :=
    two_mul_norm_mul_effectivity_sq_add_weight_le_weight_mul_nondegenerateSourceMass
      (y := y) (n := n - 1) (by omega) hHprev
  let Nn := xiShiftedCanonicalAdmissionNorm y n
  let Np := xiShiftedCanonicalAdmissionNorm y (n - 1)
  let Rn := xiShiftedCanonicalAdmissionEffectivityRate y n
  let Rp := xiShiftedCanonicalAdmissionEffectivityRate y (n - 1)
  let Kn := xiShiftedNondegenerateSourceEffectivityWeight n
  let Kp := xiShiftedNondegenerateSourceEffectivityWeight (n - 1)
  let Sn := xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass y n
  let Sp := xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass y (n - 1)
  change 2 * Nn * (Rn ^ (2 : ℕ) + Kn) ≤ Kn * Sn at hcur
  change 2 * Np * (Rp ^ (2 : ℕ) + Kp) ≤ Kp * Sp at hprev
  have hcurScaled : Np * (2 * Nn * (Rn ^ (2 : ℕ) + Kn)) ≤ Np * (Kn * Sn) :=
    mul_le_mul_of_nonneg_left hcur hP
  have hprevScaled : Nn * (2 * Np * (Rp ^ (2 : ℕ) + Kp)) ≤ Nn * (Kp * Sp) :=
    mul_le_mul_of_nonneg_left hprev hN
  have hdiff :
      (Rp - Rn) ^ (2 : ℕ) ≤ 2 * (Rp ^ (2 : ℕ) + Rn ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg (Rp + Rn)]
  have hNP : 0 ≤ Nn * Np := mul_nonneg hN hP
  have hdiffScaled : Nn * Np * (Rp - Rn) ^ (2 : ℕ) ≤
      Nn * Np * (2 * (Rp ^ (2 : ℕ) + Rn ^ (2 : ℕ))) :=
    mul_le_mul_of_nonneg_left hdiff hNP
  change Nn * Np * (Rp - Rn) ^ (2 : ℕ) + 2 * (Kn + Kp) * Nn * Np ≤
    Kn * Np * Sn + Kp * Nn * Sp
  calc
    Nn * Np * (Rp - Rn) ^ (2 : ℕ) + 2 * (Kn + Kp) * Nn * Np ≤
        Nn * Np * (2 * (Rp ^ (2 : ℕ) + Rn ^ (2 : ℕ))) +
          2 * (Kn + Kp) * Nn * Np :=
      add_le_add hdiffScaled (le_refl _)
    _ = Np * (2 * Nn * (Rn ^ (2 : ℕ) + Kn)) +
          Nn * (2 * Np * (Rp ^ (2 : ℕ) + Kp)) := by ring
    _ ≤ Np * (Kn * Sn) + Nn * (Kp * Sp) :=
      add_le_add hcurScaled hprevScaled
    _ = Kn * Np * Sn + Kp * Nn * Sp := by ring

set_option maxHeartbeats 600000 in
/-- Literal square-mass form of adjacent division-free action.  Right side is a bilinear landing
of two actual adjacent-amplitude completed `P^sharp` sources, formed before any reflection or
degree reporter. -/
theorem literal_adjacent_nondegenerateAdaptiveMixedSources_pay_edgeEffectivity
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n - 1) *
          (xiShiftedCanonicalAdmissionEffectivityRate (w ^ (2 : ℕ)) (n - 1) -
            xiShiftedCanonicalAdmissionEffectivityRate (w ^ (2 : ℕ)) n) ^ (2 : ℕ) +
        2 * (xiShiftedNondegenerateSourceEffectivityWeight n +
            xiShiftedNondegenerateSourceEffectivityWeight (n - 1)) *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n - 1) ≤
      xiShiftedNondegenerateSourceEffectivityWeight n *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n - 1) *
          xiShiftedNondegenerateNullFlagCompletedArithmeticSource w n
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) n)
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) (n + 1)) +
        xiShiftedNondegenerateSourceEffectivityWeight (n - 1) *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedNondegenerateNullFlagCompletedArithmeticSource w (n - 1)
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) (n - 1))
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) n) := by
  have hmass : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 2)).PosDef := hH
  have haction :=
    adjacent_norm_product_mul_effectivity_difference_sq_add_reserve_le_mixed_sources
      hn hmass
  rw [xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_sq_eq_arithmetic
      hw n,
    xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_sq_eq_arithmetic
      hw (n - 1)] at haction
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using haction

/-- **Source-paid adjacent curvature capstone.**  Exact logarithmic motion of shared Jacobi edge
is the effectivity difference controlled by preceding literal adjacent-amplitude `P^sharp`
aggregate. -/
theorem hasDerivAt_log_adjacentEdge_and_literal_nondegenerateSource_action
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    HasDerivAt
        (fun y => Real.log (xiShiftedCanonicalAdmissionAdjacentEdge y n))
        (xiShiftedCanonicalAdmissionEffectivityRate (w ^ (2 : ℕ)) (n - 1) -
          xiShiftedCanonicalAdmissionEffectivityRate (w ^ (2 : ℕ)) n) (w ^ (2 : ℕ)) ∧
      xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
            xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n - 1) *
            (xiShiftedCanonicalAdmissionEffectivityRate (w ^ (2 : ℕ)) (n - 1) -
              xiShiftedCanonicalAdmissionEffectivityRate (w ^ (2 : ℕ)) n) ^ (2 : ℕ) +
          2 * (xiShiftedNondegenerateSourceEffectivityWeight n +
              xiShiftedNondegenerateSourceEffectivityWeight (n - 1)) *
            xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
            xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n - 1) ≤
        xiShiftedNondegenerateSourceEffectivityWeight n *
            xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n - 1) *
            xiShiftedNondegenerateNullFlagCompletedArithmeticSource w n
              (HTGeometry.monicMomentAdmissionPolynomial
                (xiShiftedRealMomentSequence w) n)
              (HTGeometry.monicMomentAdmissionPolynomial
                (xiShiftedRealMomentSequence w) (n + 1)) +
          xiShiftedNondegenerateSourceEffectivityWeight (n - 1) *
            xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
            xiShiftedNondegenerateNullFlagCompletedArithmeticSource w (n - 1)
              (HTGeometry.monicMomentAdmissionPolynomial
                (xiShiftedRealMomentSequence w) (n - 1))
              (HTGeometry.monicMomentAdmissionPolynomial
                (xiShiftedRealMomentSequence w) n) := by
  have hw0 : 0 < w := lt_trans (by norm_num) hw
  have hmass : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef := hH
  constructor
  · exact hasDerivAt_log_xiShiftedCanonicalAdmissionAdjacentEdge
      (sq_pos_of_pos hw0) (by omega) hmass
  · exact literal_adjacent_nondegenerateAdaptiveMixedSources_pay_edgeEffectivity
      hw hn hH

end

end RHTower
