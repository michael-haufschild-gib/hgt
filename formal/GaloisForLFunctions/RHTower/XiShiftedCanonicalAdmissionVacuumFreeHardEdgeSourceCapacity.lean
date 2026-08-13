import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionNondegenerateSourceEffectivity
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionFlatContactSourceTransmutation

/-!
# Vacuum-free adjacent-admission hard-edge source capacity

The unit-renormalized nondegenerate source is formed from current and adjacent inverse-Hankel
amplitudes before completed rational--Gamma/von-Mangoldt aggregation.  After reciprocal clearing,
all completion channels beyond the adaptive mixed source are divisible by the square of the current
cleared amplitude.  They therefore change chamber coercivity but have zero first transverse jet at
every current hard root.

Consequently the literal two-amplitude vacuum-free source inherits the exact hard-root capacity,
Padé-residue conservation, and compact normalization of the adaptive mixed `P^sharp` source.  This
is a source-first mixed-amplitude law, not a fixed reporter or a post-aggregation orientation.
-/

open Complex Matrix Polynomial Filter Topology

namespace RHTower

noncomputable section

/-- Quadratic hard-edge correction left after removing the diagonal adaptive mixed source from
the doubled unit-renormalized nondegenerate source polynomial. -/
def xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection
    (n : ℕ) (A B : Polynomial ℝ) : Polynomial ℝ :=
  (-2 * (n + 1 : ℝ)) • X ^ 2 +
    (2 * (1 + A.nextCoeff)) • X +
    C (4 * A.nextCoeff ^ 2 +
      2 * ((A.nextCoeff - B.nextCoeff) ^ 2 -
        (A.nextCoeff - B.nextCoeff)))

theorem natDegree_xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection_le
    (n : ℕ) (A B : Polynomial ℝ) :
    (xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B).natDegree ≤ 2 := by
  simp only [xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection]
  apply le_trans (Polynomial.natDegree_add_le _ _)
  apply max_le
  · apply le_trans (Polynomial.natDegree_add_le _ _)
    apply max_le
    · exact le_trans (Polynomial.natDegree_smul_le _ _) (by simp)
    · exact le_trans (Polynomial.natDegree_smul_le _ _) (by simp)
  · rw [Polynomial.natDegree_C]
    omega

/-- Exact source-polynomial factorization.  Every chamber-completion and vacuum-removal term not
already in the adaptive mixed source carries the square of the current admitted amplitude. -/
theorem two_smul_unitRenormalizedNondegenerateShear_eq_adaptiveBilinear_add_sq_mul_correction
    (n : ℕ) (A B : Polynomial ℝ) :
    (2 : ℝ) •
        xiShiftedBoundaryUnitRenormalizedNondegenerateNullFlagShearPolynomial n A B =
      xiShiftedBoundaryAdaptiveBilinearShearPolynomial A A +
        A ^ 2 * xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B := by
  rw [xiShiftedBoundaryUnitRenormalizedNondegenerateNullFlagShearPolynomial,
    xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial,
    xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial,
    xiShiftedBoundaryDegreeCenteredShearPolynomial_eq_adaptive_sub_square]
  simp only [xiShiftedBoundaryAdaptiveBilinearShearPolynomial,
    xiShiftedBoundaryAdaptiveShearPolynomial,
    xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection,
    Polynomial.smul_eq_C_mul]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat]
  ring

/-- Literal two-amplitude vacuum-free producer in the reciprocal hard coordinate.  Doubling is
part of source formation and matches the completed `P^sharp` arithmetic normalization. -/
def xiShiftedUnitRenormalizedNondegenerateHardEdgeSource
    (y : ℝ) (n : ℕ) (A B : Polynomial ℝ) : Polynomial ℝ :=
  xiShiftedHardEdgeReciprocalClearing y (2 * n + 2)
    ((2 : ℝ) •
      xiShiftedBoundaryUnitRenormalizedNondegenerateNullFlagShearPolynomial n A B)

/-- Hard-edge factorization of the literal vacuum-free source.  The adjacent amplitude enters the
source before clearing, but its extra contribution has double current-root vanishing. -/
theorem xiShiftedUnitRenormalizedNondegenerateHardEdgeSource_eq_adaptive_add_sq_mul_correction
    {A B : Polynomial ℝ} {n : ℕ} (hA : A.natDegree ≤ n) (y : ℝ) :
    xiShiftedUnitRenormalizedNondegenerateHardEdgeSource y n A B =
      xiShiftedHardEdgeAdaptiveBilinearSource y n n A A +
        (xiShiftedHardEdgeReciprocalClearing y n A) ^ 2 *
          xiShiftedHardEdgeReciprocalClearing y 2
            (xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B) := by
  have hAsq : (A ^ 2).natDegree ≤ n + n := by
    calc
      (A ^ 2).natDegree ≤ 2 * A.natDegree := Polynomial.natDegree_pow_le
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 hA
      _ = n + n := by omega
  have hcorrection :
      xiShiftedHardEdgeReciprocalClearing y (2 * n + 2)
          (A ^ 2 * xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B) =
        (xiShiftedHardEdgeReciprocalClearing y n A) ^ 2 *
          xiShiftedHardEdgeReciprocalClearing y 2
            (xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B) := by
    rw [show 2 * n + 2 = (n + n) + 2 by omega,
      xiShiftedHardEdgeReciprocalClearing_mul hAsq
        (natDegree_xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection_le n A B) y]
    rw [show A ^ 2 = A * A by ring,
      xiShiftedHardEdgeReciprocalClearing_mul hA hA y]
    ring
  have hcorrection' :
      xiShiftedHardEdgeReciprocalClearing y (n + n + 2)
          (A ^ 2 * xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B) =
        (xiShiftedHardEdgeReciprocalClearing y n A) ^ 2 *
          xiShiftedHardEdgeReciprocalClearing y 2
            (xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B) := by
    simpa only [show n + n = 2 * n by omega] using hcorrection
  rw [xiShiftedUnitRenormalizedNondegenerateHardEdgeSource,
    two_smul_unitRenormalizedNondegenerateShear_eq_adaptiveBilinear_add_sq_mul_correction]
  calc
    xiShiftedHardEdgeReciprocalClearing y (2 * n + 2)
        (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A A +
          A ^ 2 * xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B) =
      xiShiftedHardEdgeReciprocalClearing y (2 * n + 2)
          (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A A) +
        xiShiftedHardEdgeReciprocalClearing y (2 * n + 2)
          (A ^ 2 * xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B) := by
            simp [xiShiftedHardEdgeReciprocalClearing]
    _ = xiShiftedHardEdgeAdaptiveBilinearSource y n n A A +
        (xiShiftedHardEdgeReciprocalClearing y n A) ^ 2 *
          xiShiftedHardEdgeReciprocalClearing y 2
            (xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B) := by
      rw [show 2 * n + 2 = n + n + 2 by omega,
        xiShiftedHardEdgeReciprocalClearing_adaptiveBilinearShear hA hA,
        hcorrection']

/-- The literal vacuum-free producer vanishes at every nonzero current admitted hard root. -/
theorem xiShiftedUnitRenormalizedNondegenerateHardEdgeSource_eval_centeredReciprocal_eq_zero
    {A B : Polynomial ℝ} {n : ℕ} (hA : A.natDegree ≤ n)
    (y : ℝ) {x : ℝ} (hx : x ≠ 0) (hroot : A.eval x = 0) :
    (xiShiftedUnitRenormalizedNondegenerateHardEdgeSource y n A B).eval (x⁻¹ - y) = 0 := by
  rw [xiShiftedUnitRenormalizedNondegenerateHardEdgeSource_eq_adaptive_add_sq_mul_correction
    hA y]
  have hS := xiShiftedHardEdgeReciprocalClearing_eval_centeredReciprocal_eq_zero
    hA y hx hroot
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, hS]
  simp [xiShiftedHardEdgeAdaptiveBilinearSource_eval_centeredReciprocal_eq_zero
    y hA hx hroot]

/-- **Vacuum-free mixed-source transverse jet law.**  Every additional adjacent-admission
completion has double current-root vanishing, so the first transverse jet is exactly the adaptive
mixed `P^sharp` jet and is independent of the adjacent amplitude only after source formation. -/
theorem derivative_xiShiftedUnitRenormalizedNondegenerateHardEdgeSource_eval_centeredReciprocal
    {A B : Polynomial ℝ} {n : ℕ} (hA : A.natDegree ≤ n)
    (y : ℝ) {x : ℝ} (hx : x ≠ 0) (hroot : A.eval x = 0) :
    let S := xiShiftedHardEdgeReciprocalClearing y n A
    (xiShiftedUnitRenormalizedNondegenerateHardEdgeSource y n A B).derivative.eval
        (x⁻¹ - y) =
      -2 * x⁻¹ * (S.derivative.eval (x⁻¹ - y)) ^ 2 := by
  dsimp only
  rw [xiShiftedUnitRenormalizedNondegenerateHardEdgeSource_eq_adaptive_add_sq_mul_correction
    hA y, Polynomial.derivative_add]
  have hS := xiShiftedHardEdgeReciprocalClearing_eval_centeredReciprocal_eq_zero
    hA y hx hroot
  have hcorrection :
      ((xiShiftedHardEdgeReciprocalClearing y n A) ^ 2 *
        xiShiftedHardEdgeReciprocalClearing y 2
          (xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B)).derivative.eval
            (x⁻¹ - y) = 0 := by
    rw [show (xiShiftedHardEdgeReciprocalClearing y n A) ^ 2 *
        xiShiftedHardEdgeReciprocalClearing y 2
          (xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B) =
      (xiShiftedHardEdgeReciprocalClearing y n A *
        xiShiftedHardEdgeReciprocalClearing y n A) *
          xiShiftedHardEdgeReciprocalClearing y 2
            (xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection n A B) by ring,
      Polynomial.derivative_mul, Polynomial.derivative_mul]
    simp [hS]
  rw [Polynomial.eval_add, hcorrection, add_zero]
  exact derivative_xiShiftedHardEdgeAdaptiveBilinearSource_eval_centeredReciprocal
    y hA hx hroot

/-- Admission-sensitive transverse capacity of the literal two-amplitude vacuum-free source. -/
def xiShiftedUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity
    (y : ℝ) (n : ℕ) (A B : Polynomial ℝ) (x : ℝ) : ℝ :=
  -(x / 2) *
    (xiShiftedUnitRenormalizedNondegenerateHardEdgeSource y n A B).derivative.eval (x⁻¹ - y)

/-- Exact capacity landing: vacuum-free two-amplitude source capacity is the cleared current
amplitude derivative square. -/
theorem xiShiftedUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity_eq_sq
    {A B : Polynomial ℝ} {n : ℕ} (hA : A.natDegree ≤ n)
    (y : ℝ) {x : ℝ} (hx : x ≠ 0) (hroot : A.eval x = 0) :
    xiShiftedUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity y n A B x =
      ((xiShiftedHardEdgeReciprocalClearing y n A).derivative.eval (x⁻¹ - y)) ^ 2 := by
  rw [xiShiftedUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity,
    derivative_xiShiftedUnitRenormalizedNondegenerateHardEdgeSource_eval_centeredReciprocal
      hA y hx hroot]
  field_simp

/-- The vacuum-free two-amplitude capacity equals the diagonal adaptive source capacity at every
current hard root.  Equality is proved from source polynomials, not imposed by a reporter. -/
theorem xiShiftedUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity_eq_adaptive
    {A B : Polynomial ℝ} {n : ℕ} (hA : A.natDegree ≤ n)
    (y : ℝ) {x : ℝ} (hx : x ≠ 0) (hroot : A.eval x = 0) :
    xiShiftedUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity y n A B x =
      xiShiftedHardEdgeAdaptiveSourceTransverseCapacity y n A x := by
  rw [xiShiftedUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity_eq_sq
      hA y hx hroot,
    xiShiftedHardEdgeAdaptiveSourceTransverseCapacity_eq_sq y hA hx hroot]

/-! ## Literal shifted-Xi canonical specialization -/

/-- Actual current/adjacent inverse-Hankel amplitudes inserted into the vacuum-free source before
hard-edge clearing. -/
def xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSource
    (w : ℝ) (n : ℕ) : Polynomial ℝ :=
  xiShiftedUnitRenormalizedNondegenerateHardEdgeSource (w ^ 2) n
    (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n)
    (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) (n + 1))

/-- The canonical hard-edge producer lands exactly on the literal unit-renormalized
rational--Gamma/von-Mangoldt source aggregate. -/
theorem xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource_canonicalAdmission_eq_hardEdgeLanding
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n)
        (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) (n + 1)) =
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w)
        (xiShiftedHardEdgeReciprocalUnclearing (w ^ 2) (2 * n + 2)
          (xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSource w n)) := by
  rw [xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw]
  simp only [xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSource,
    xiShiftedUnitRenormalizedNondegenerateHardEdgeSource,
    xiShiftedHardEdgeReciprocalUnclearing_clearing]
  rw [HTGeometry.momentFunctional_smul]

/-- Transverse capacity of the actual current/adjacent completed source. -/
def xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity
    (w : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  -(x / 2) *
    (xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSource w n).derivative.eval
      (x⁻¹ - w ^ 2)

/-- Effective compact hard-edge capacity of the actual two-amplitude source. -/
def xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
    (w : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (w ^ 2) * x ^ (2 * n + 1) *
    xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity
      w n x

/-- Canonical vacuum-free capacity equals canonical adaptive capacity at every current admitted
root, despite depending on both admissions before source formation. -/
theorem xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity_eq_adaptive
    {w : ℝ} {n : ℕ} {x : ℝ} (hx : x ≠ 0)
    (hroot :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n).eval x = 0) :
    xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity
        w n x =
      xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity w n x := by
  let A := HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n
  let B := HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) (n + 1)
  have hA : A.natDegree ≤ n := by
    dsimp only [A]
    rw [HTGeometry.monicMomentAdmissionPolynomial_natDegree]
  simpa only [xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity,
    xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSource,
    xiShiftedUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity,
    xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity,
    xiShiftedCanonicalAdmissionHardEdgeSource,
    xiShiftedHardEdgeAdaptiveSourceTransverseCapacity, A, B] using
    xiShiftedUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity_eq_adaptive
      hA (w ^ 2) hx hroot

/-- Effective capacity of the literal two-amplitude source has no new degree normalization. -/
theorem xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity_eq_adaptive
    {w : ℝ} {n : ℕ} {x : ℝ} (hx : x ≠ 0)
    (hroot :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n).eval x = 0) :
    xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
        w n x =
      xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity w n x := by
  rw [xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity,
    xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity,
    xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity_eq_adaptive
      hx hroot]

/-- **Literal vacuum-free source-capacity/Padé-residue law.**  Canonical Padé residue times
endogenous capacity of the actual current/adjacent completed `P^sharp` aggregate equals finite hard
terminal mass.  Admission, degree, source, and reciprocal chart vary together. -/
theorem xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_unitRenormalizedNondegenerateEffectiveSourceCapacity_eq_terminalMass
    {w : ℝ} {n : ℕ} {x : ℝ} (hx : x ≠ 0)
    (hroot :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n).eval x = 0) :
    xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n x *
        xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
          w n x =
      xiShiftedCanonicalAdmissionHardEdgeGaussTerminalMass w n x := by
  rw [xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity_eq_adaptive
    hx hroot]
  exact xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_effectiveSourceCapacity_eq_terminalMass
    hx hroot

/-- **Vacuum-free mixed-source worldline conservation.**  Actual reciprocal hard-root speed times
Padé residue times capacity of the same current/adjacent completed source equals current norm
forcing.  No diagonal source is substituted until source-polynomial jet equality has been proved. -/
theorem xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_residue_mul_unitRenormalizedNondegenerateSourceCapacity_eq_normSq
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ 2))
    (hx0 : x (w ^ 2) ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds (w ^ 2)]
          fun _ => 0) :
    (-xdot / (x (w ^ 2)) ^ 2 - 1) *
        (xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n (x (w ^ 2)) *
          xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
            w n (x (w ^ 2))) =
      2 * (n : ℝ) * (w ^ 2) * (x (w ^ 2)) ^ 2 *
        HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n := by
  have hroot0 :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n).eval (x (w ^ 2)) = 0 := by
    exact hroot.eq_of_nhds
  rw [xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity_eq_adaptive
    hx0 hroot0]
  unfold xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue
  unfold xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity
  unfold xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity
  unfold xiShiftedCanonicalAdmissionHardEdgeSource
  unfold xiShiftedRealMomentSequence at hH ⊢
  exact xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_residue_mul_sourceCapacity_eq_normSq
    (sq_pos_of_pos (lt_trans (by norm_num) hw)) hn hH hx hx0 hroot

/-- Parabolic square-root-mass form of the same literal mixed-source conservation law. -/
theorem xiShiftedCanonicalAdmissionParabolicHardEdgeWorldline_mul_residue_mul_unitRenormalizedNondegenerateSourceCapacity_eq_normSq
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ 2))
    (hx0 : x (w ^ 2) ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds (w ^ 2)]
          fun _ => 0) :
    (2 * w * (-xdot / (x (w ^ 2)) ^ 2 - 1)) *
        (xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n (x (w ^ 2)) *
          xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
            w n (x (w ^ 2))) =
      4 * (n : ℝ) * w ^ 3 * (x (w ^ 2)) ^ 2 *
        HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n := by
  have hworld :=
    xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_residue_mul_unitRenormalizedNondegenerateSourceCapacity_eq_normSq
      hw hn hH hx hx0 hroot
  nlinarith [hworld]

/-- **Two-face source capstone.**  One literal current/adjacent vacuum-free `P^sharp` formation
simultaneously pays chamber effectivity and, at each current hard root, conserves absolute Padé
visibility against finite hard terminal mass. -/
theorem literal_unitRenormalizedNondegenerateSource_pays_effectivity_and_hardRootCapacity
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ} (hx : x ≠ 0)
    (hroot :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n).eval x = 0) :
    (2 * xiShiftedCanonicalAdmissionNorm (w ^ 2) n *
          xiShiftedCanonicalAdmissionEffectivityRate (w ^ 2) n ^ 2 ≤
        xiShiftedNondegenerateSourceEffectivityWeight n *
          xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource w n
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) n)
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) (n + 1))) ∧
      (xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n x *
          xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
            w n x =
        xiShiftedCanonicalAdmissionHardEdgeGaussTerminalMass w n x) := by
  exact ⟨literal_unitRenormalizedAdaptiveMixedSource_pays_admissionEffectivity hw hn hH,
    xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_unitRenormalizedNondegenerateEffectiveSourceCapacity_eq_terminalMass
      hx hroot⟩

/-- **Flat-contact jet separation.**  At a canonical flat face, every simple current hard-root
worldline freezes to first order while the same literal current/adjacent vacuum-free source has
strictly positive first transverse capacity.  Vanishing carrier motion therefore cannot erase
source production; it shifts the obstruction to terminal mass/contact order. -/
theorem xiShiftedCanonicalAdmission_flatHardRoot_freezes_but_unitRenormalizedSourceCapacity_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ 2) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ 2) (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n = 0)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ 2))
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds (w ^ 2)]
          fun _ => 0)
    (hx0 : x (w ^ 2) ≠ 0)
    (hsimple : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).derivative.eval (x (w ^ 2)) ≠ 0) :
    HasDerivAt (fun v => (x v)⁻¹ - v) 0 (w ^ 2) ∧
      0 < xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity
        w n (x (w ^ 2)) := by
  have hy : 0 < w ^ 2 := sq_pos_of_pos (lt_trans (by norm_num) hw)
  have hroot0 : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).eval (x (w ^ 2)) = 0 := by
    exact hroot.eq_of_nhds
  have hdegree : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).natDegree ≤ n := by
    rw [HTGeometry.monicMomentAdmissionPolynomial_natDegree]
  have hcleared :
      (xiShiftedHardEdgeReciprocalClearing (w ^ 2) n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n)).derivative.eval
            ((x (w ^ 2))⁻¹ - w ^ 2) ≠ 0 := by
    intro hzero
    have hrelation :=
      pow_mul_derivative_xiShiftedHardEdgeReciprocalClearing_eval_centeredReciprocal
        hdegree (w ^ 2) hx0 hroot0
    rw [hzero, mul_zero] at hrelation
    have hproduct : (x (w ^ 2)) ^ 2 *
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n).derivative.eval (x (w ^ 2)) = 0 := by
      linarith only [hrelation]
    rcases mul_eq_zero.mp hproduct with hsquare | hderiv
    · exact hx0 (sq_eq_zero_iff.mp hsquare)
    · exact hsimple hderiv
  constructor
  · apply hasDerivAt_xiShiftedCanonicalAdmission_reciprocalHardRoot_zero_of_flatFace
      hy hn hhead hflat hx hroot hx0
    change (HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n).derivative.eval
        (x (w ^ 2)) ≠ 0 at hsimple
    exact hsimple
  · rw [xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity_eq_adaptive
      hx0 hroot0,
    xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity_eq_sq hx0 hroot0]
    exact sq_pos_of_ne_zero hcleared

/-- Compact moving-degree limit of the two-amplitude source capacity.  The adjacent completion and
vacuum removal cannot create a hidden capacity escape. -/
theorem tendsto_xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
    {w : ℕ → ℝ} {n : ℕ → ℕ} {x u : ℕ → ℝ} {d : ℝ}
    (hw : ∀ k, 1 / 2 < w k)
    (hdenom : ∀ k, w k ^ 2 + u k ≠ 0)
    (hx : ∀ k, x k = (w k ^ 2 + u k)⁻¹)
    (hroot : ∀ k,
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence (w k)) (n k)).eval (x k) = 0)
    (hsmall : Tendsto
      (fun k => ((2 * n k + 1 : ℕ) : ℝ) *
        |u k / (w k ^ 2 + u k)|) atTop (nhds 0))
    (hderiv : Tendsto
      (fun k =>
        (xiShiftedCanonicalAdmissionHardEdgeNormalizedClearing
          (w k) (n k)).derivative.eval ((x k)⁻¹ - w k ^ 2))
      atTop (nhds d)) :
    Tendsto
      (fun k =>
        xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
          (w k) (n k) (x k))
      atTop (nhds (d ^ 2)) := by
  have heq :
      (fun k =>
        xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
          (w k) (n k) (x k)) =ᶠ[atTop]
      (fun k =>
        xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity
          (w k) (n k) (x k)) := by
    filter_upwards with k
    exact xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity_eq_adaptive
      (by rw [hx k]; exact inv_ne_zero (hdenom k)) (hroot k)
  exact (tendsto_xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity
    hw hdenom hx hroot hsmall hderiv).congr' heq.symm

end

end RHTower
