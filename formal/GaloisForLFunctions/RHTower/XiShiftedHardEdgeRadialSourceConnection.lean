import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionHardEdgeSourceLaw

/-!
# Radial source connection on the complete hard-edge Hausdorff diagonal

Inverse reciprocal clearing does more than identify a static Hausdorff diagonal.  When the
hard-edge polynomial is admitted first and then held fixed, every channel

`L_y(X^k (1-yX)^r)`

obeys one homogeneous source equation of weight `k+r+1`.  On a complete diagonal `k+r=D`, all
channels therefore have the same radial weight `D+1`.  Consequently the entire admission-selected
completed source satisfies a single depth-raising differential law before any scalar reflection
report is made.

The final capstones specialize this connection to the actual adaptive bilinear producer and to
canonical inverse-Hankel `P^sharp` admission.  No positivity assumption is used.
-/

open Complex Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One raw hard-edge Hausdorff channel.  Unlike a fixed reporter, both its moment tower and its
endpoint polynomial move with the squared mass. -/
def xiShiftedHardEdgeRadialChannel (y : ℝ) (k r : ℕ) : ℝ :=
  HTGeometry.momentFunctional
    (fun n => (xiShiftedReciprocalMoment y n).re)
    (X ^ k * (1 - C y * X) ^ r)

/-- Adding one endpoint factor is the exact radial difference of two adjacent channels. -/
theorem xiShiftedHardEdgeRadialChannel_succ
    (y : ℝ) (k r : ℕ) :
    xiShiftedHardEdgeRadialChannel y k (r + 1) =
      xiShiftedHardEdgeRadialChannel y k r -
        y * xiShiftedHardEdgeRadialChannel y (k + 1) r := by
  rw [xiShiftedHardEdgeRadialChannel, xiShiftedHardEdgeRadialChannel,
    xiShiftedHardEdgeRadialChannel]
  rw [show X ^ k * (1 - C y * X) ^ (r + 1) =
      X ^ k * (1 - C y * X) ^ r -
        y • (X ^ (k + 1) * (1 - C y * X) ^ r) by
    simp only [pow_succ, Polynomial.smul_eq_C_mul]
    ring,
    HTGeometry.momentFunctional_sub, HTGeometry.momentFunctional_smul]

/-- **Homogeneous hard-edge source equation.**  Differentiating one moving endpoint channel
raises its longitudinal moment degree and multiplies by its total homogeneous degree. -/
theorem hasDerivAt_xiShiftedHardEdgeRadialChannel
    {y : ℝ} (hy : 0 < y) (k r : ℕ) :
    HasDerivAt (fun v => xiShiftedHardEdgeRadialChannel v k r)
      (-((k + r + 1 : ℕ) : ℝ) *
        xiShiftedHardEdgeRadialChannel y (k + 1) r) y := by
  induction r generalizing k with
  | zero =>
      have h := hasDerivAt_re_xiShiftedReciprocalMoment hy k
      simp only [xiShiftedHardEdgeRadialChannel, pow_zero, mul_one,
        HTGeometry.momentFunctional_X_pow]
      refine h.congr_deriv ?_
      push_cast
      ring
  | succ r ih =>
      have hfun :
          (fun v => xiShiftedHardEdgeRadialChannel v k (r + 1)) =
            (fun v => xiShiftedHardEdgeRadialChannel v k r -
              v * xiShiftedHardEdgeRadialChannel v (k + 1) r) := by
        funext v
        exact xiShiftedHardEdgeRadialChannel_succ v k r
      rw [hfun]
      have hleft := ih k
      have hright := (hasDerivAt_id y).mul (ih (k + 1))
      have hraw := hleft.sub hright
      have heq :
          (fun v => xiShiftedHardEdgeRadialChannel v k r) -
              id * (fun v => xiShiftedHardEdgeRadialChannel v (k + 1) r) =
            (fun v => xiShiftedHardEdgeRadialChannel v k r -
              v * xiShiftedHardEdgeRadialChannel v (k + 1) r) := by
        funext v
        rfl
      rw [heq] at hraw
      simp only [id_eq, one_mul] at hraw
      refine hraw.congr_deriv ?_
      rw [xiShiftedHardEdgeRadialChannel_succ y (k + 1) r]
      push_cast
      ring

/-- A depth-`D` hard-edge polynomial after source-first admission, represented on its complete
raw Hausdorff diagonal. -/
def xiShiftedHardEdgeRadialAggregate
    (y : ℝ) (D : ℕ) (T : Polynomial ℝ) : ℝ :=
  T.support.sum (fun j =>
    T.coeff j * xiShiftedHardEdgeRadialChannel y (D - j) j)

/-- Endpoint-raised aggregate: every admitted hard-edge coefficient acquires one additional
factor `1-yX` before aggregation. -/
def xiShiftedHardEdgeEndpointRaisedRadialAggregate
    (y : ℝ) (D : ℕ) (T : Polynomial ℝ) : ℝ :=
  T.support.sum (fun j =>
    T.coeff j * xiShiftedHardEdgeRadialChannel y (D - j) (j + 1))

/-- Raw radial channels are exactly the scaled-Hausdorff entries used by inverse clearing. -/
theorem xiShiftedHardEdgeRadialChannel_eq_scaledHausdorff
    {y : ℝ} (hy : 0 < y) (k r : ℕ) :
    xiShiftedHardEdgeRadialChannel y k r =
      y ^ r * scaledHausdorffMomentDifference (1 / y)
        (fun n => (xiShiftedReciprocalMoment y n).re) k r := by
  have h := momentFunctional_hardEdgeUnclearing_X_pow_eq_scaledHausdorff
    (fun n => (xiShiftedReciprocalMoment y n).re)
    hy (D := k + r) (j := r) (by omega : r ≤ k + r)
  rw [xiShiftedHardEdgeReciprocalUnclearing_X_pow (by omega : r ≤ k + r)] at h
  have hkr : k + r - r = k := by omega
  rw [hkr] at h
  simpa only [xiShiftedHardEdgeRadialChannel] using h

/-- The radial aggregate is the literal inverse-cleared moment landing. -/
theorem xiShiftedHardEdgeRadialAggregate_eq_unclearing
    {y : ℝ} (hy : 0 < y) {D : ℕ} {T : Polynomial ℝ}
    (hT : T.natDegree ≤ D) :
    xiShiftedHardEdgeRadialAggregate y D T =
      HTGeometry.momentFunctional
        (fun n => (xiShiftedReciprocalMoment y n).re)
        (xiShiftedHardEdgeReciprocalUnclearing y D T) := by
  rw [momentFunctional_hardEdgeUnclearing_eq_completeHausdorffDiagonal
    (fun n => (xiShiftedReciprocalMoment y n).re) hy hT]
  unfold xiShiftedHardEdgeRadialAggregate
  apply Finset.sum_congr rfl
  intro j hj
  rw [xiShiftedHardEdgeRadialChannel_eq_scaledHausdorff hy]

/-- **Complete-diagonal radial source law.**  After admission, every coefficient on depth `D`
evolves with the same weight `D+1`; differentiation raises only longitudinal depth. -/
theorem hasDerivAt_xiShiftedHardEdgeRadialAggregate
    {y : ℝ} (hy : 0 < y) {D : ℕ} {T : Polynomial ℝ}
    (hT : T.natDegree ≤ D) :
    HasDerivAt (fun v => xiShiftedHardEdgeRadialAggregate v D T)
      (-((D + 1 : ℕ) : ℝ) *
        xiShiftedHardEdgeRadialAggregate y (D + 1) T) y := by
  unfold xiShiftedHardEdgeRadialAggregate
  have hjD (j : ℕ) (hj : j ∈ T.support) : j ≤ D :=
    (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hj)).trans hT
  have hsum := HasDerivAt.sum (u := T.support) (fun j hj =>
    (hasDerivAt_xiShiftedHardEdgeRadialChannel hy (D - j) j).const_mul
      (T.coeff j))
  have hfun :
      (∑ j ∈ T.support,
        fun v => T.coeff j * xiShiftedHardEdgeRadialChannel v (D - j) j) =
        (fun v => ∑ j ∈ T.support,
          T.coeff j * xiShiftedHardEdgeRadialChannel v (D - j) j) := by
    funext v
    simp only [Finset.sum_apply]
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjD' := hjD j hj
  rw [show D - j + j + 1 = D + 1 by omega,
    show D + 1 - j = D - j + 1 by omega]
  ring

/-- Raising the endpoint factor is exactly radial aggregate minus mass times its depth raise. -/
theorem xiShiftedHardEdgeEndpointRaisedRadialAggregate_eq_sub_depthRaise
    {y : ℝ} {D : ℕ} {T : Polynomial ℝ} (hT : T.natDegree ≤ D) :
    xiShiftedHardEdgeEndpointRaisedRadialAggregate y D T =
      xiShiftedHardEdgeRadialAggregate y D T -
        y * xiShiftedHardEdgeRadialAggregate y (D + 1) T := by
  unfold xiShiftedHardEdgeEndpointRaisedRadialAggregate
    xiShiftedHardEdgeRadialAggregate
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjD : j ≤ D :=
    (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hj)).trans hT
  rw [show D + 1 - j = D - j + 1 by omega,
    xiShiftedHardEdgeRadialChannel_succ y (D - j) j]
  ring

/-- Endpoint raising moves the admitted source to the next complete scaled-Hausdorff diagonal;
no coordinate is discarded. -/
theorem xiShiftedHardEdgeEndpointRaisedRadialAggregate_eq_completeHausdorffDiagonal
    {y : ℝ} (hy : 0 < y) (D : ℕ) (T : Polynomial ℝ) :
    xiShiftedHardEdgeEndpointRaisedRadialAggregate y D T =
      T.support.sum (fun j => T.coeff j *
        (y ^ (j + 1) *
          scaledHausdorffMomentDifference (1 / y)
            (fun n => (xiShiftedReciprocalMoment y n).re)
            (D - j) (j + 1))) := by
  unfold xiShiftedHardEdgeEndpointRaisedRadialAggregate
  apply Finset.sum_congr rfl
  intro j _
  rw [xiShiftedHardEdgeRadialChannel_eq_scaledHausdorff hy]

/-- **Integrated radial-flux law.**  Multiplying the admitted completed aggregate by its forced
homogeneous mass weight makes its derivative exactly the endpoint-raised arithmetic source. -/
theorem hasDerivAt_xiShiftedHardEdgeRadialPrimitive
    {y : ℝ} (hy : 0 < y) {D : ℕ} {T : Polynomial ℝ}
    (hT : T.natDegree ≤ D) :
    HasDerivAt
      (fun v => v ^ (D + 1) * xiShiftedHardEdgeRadialAggregate v D T)
      (((D + 1 : ℕ) : ℝ) * y ^ D *
        xiShiftedHardEdgeEndpointRaisedRadialAggregate y D T) y := by
  have hpow := (hasDerivAt_id y).pow (D + 1)
  have haggregate := hasDerivAt_xiShiftedHardEdgeRadialAggregate hy hT
  have hraw := hpow.mul haggregate
  have heq :
      id ^ (D + 1) * (fun v => xiShiftedHardEdgeRadialAggregate v D T) =
        (fun v => v ^ (D + 1) * xiShiftedHardEdgeRadialAggregate v D T) := by
    funext v
    rfl
  rw [heq] at hraw
  simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel] at hraw
  refine hraw.congr_deriv ?_
  rw [xiShiftedHardEdgeEndpointRaisedRadialAggregate_eq_sub_depthRaise hT]
  push_cast
  ring

/-- The static hard-edge landing of the actual bilinear source is its new radial aggregate. -/
theorem xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_radialAggregate
    {w : ℝ} (hw : 1 / 2 < w) {A B : Polynomial ℝ} {M N : ℕ}
    (hA : A.natDegree ≤ M) (hB : B.natDegree ≤ N) :
    xiShiftedAdaptiveBilinearCompletedArithmeticSource w A B =
      xiShiftedHardEdgeRadialAggregate (w ^ (2 : ℕ)) (M + N + 2)
        (xiShiftedHardEdgeAdaptiveBilinearSource (w ^ (2 : ℕ)) M N A B) := by
  rw [xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_hardEdgeLanding
    hw hA hB]
  symm
  apply xiShiftedHardEdgeRadialAggregate_eq_unclearing
    (sq_pos_of_pos (by linarith : 0 < w))
  exact (natDegree_xiShiftedHardEdgeAdaptiveBilinearSource_le
    hA hB (w ^ (2 : ℕ))).trans (by omega)

/-- **Admission-sensitive bilinear radial producer.**  Freeze the source polynomial only after
the two amplitudes and their actual depth have been admitted.  Its whole completed aggregate then
obeys the homogeneous depth-raising source law, without a positivity or Hankel-chamber premise. -/
theorem hasDerivAt_xiShiftedAdaptiveBilinearHardEdgeRadialAggregate
    {y : ℝ} (hy : 0 < y) {A B : Polynomial ℝ} {M N : ℕ}
    (hA : A.natDegree ≤ M) (hB : B.natDegree ≤ N) :
    let T := xiShiftedHardEdgeAdaptiveBilinearSource y M N A B
    HasDerivAt
      (fun v => xiShiftedHardEdgeRadialAggregate v (M + N + 2) T)
      (-((M + N + 3 : ℕ) : ℝ) *
        xiShiftedHardEdgeRadialAggregate y (M + N + 3) T) y := by
  dsimp only
  apply hasDerivAt_xiShiftedHardEdgeRadialAggregate hy
  exact (natDegree_xiShiftedHardEdgeAdaptiveBilinearSource_le hA hB y).trans
    (by omega)

/-- **Canonical completed `P^sharp` radial source law.**  Current inverse-Hankel admission first
selects `P^sharp` and its bilinear reverse-Euler producer.  Holding that selected source fixed,
the literal completed aggregate has radial derivative `-(2n+3)` times the next complete diagonal.
This is an unconditional arithmetic formation law, not a fixed linear report. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionHardEdgeRadialAggregate
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    let T := xiShiftedCanonicalAdmissionHardEdgeSource w n
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) =
        xiShiftedHardEdgeRadialAggregate (w ^ (2 : ℕ)) (2 * n + 2) T ∧
      HasDerivAt
        (fun v => xiShiftedHardEdgeRadialAggregate v (2 * n + 2) T)
        (-((2 * n + 3 : ℕ) : ℝ) *
          xiShiftedHardEdgeRadialAggregate (w ^ (2 : ℕ)) (2 * n + 3) T) (w ^ (2 : ℕ)) := by
  dsimp only
  let A := HTGeometry.monicMomentAdmissionPolynomial
    (xiShiftedRealMomentSequence w) n
  have hA : A.natDegree ≤ n := by
    dsimp only [A]
    rw [HTGeometry.monicMomentAdmissionPolynomial_natDegree]
  constructor
  · rw [← xiShiftedAdaptiveBilinearCompletedArithmeticSource_self_eq_mixed hw]
    simpa only [show n + n + 2 = 2 * n + 2 by omega,
      xiShiftedCanonicalAdmissionHardEdgeSource, A] using
      xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_radialAggregate
        hw hA hA
  · have hy : 0 < w ^ (2 : ℕ) := sq_pos_of_pos (by linarith : 0 < w)
    simpa only [show n + n + 2 = 2 * n + 2 by omega,
      show n + n + 3 = 2 * n + 3 by omega,
      xiShiftedCanonicalAdmissionHardEdgeSource, A] using
      hasDerivAt_xiShiftedAdaptiveBilinearHardEdgeRadialAggregate
        hy hA hA

/-- Canonical `P^sharp` specialization of the integrated radial-flux law.  The right-hand side is
formed by adding the endpoint factor to the already admitted bilinear source, not by observing a
fixed scalar after reflection. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionHardEdgeRadialPrimitive
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    let T := xiShiftedCanonicalAdmissionHardEdgeSource w n
    HasDerivAt
      (fun v => v ^ (2 * n + 3) *
        xiShiftedHardEdgeRadialAggregate v (2 * n + 2) T)
      (((2 * n + 3 : ℕ) : ℝ) * (w ^ (2 : ℕ)) ^ (2 * n + 2) *
        xiShiftedHardEdgeEndpointRaisedRadialAggregate
          (w ^ (2 : ℕ)) (2 * n + 2) T) (w ^ (2 : ℕ)) := by
  dsimp only
  let A := HTGeometry.monicMomentAdmissionPolynomial
    (xiShiftedRealMomentSequence w) n
  have hA : A.natDegree ≤ n := by
    dsimp only [A]
    rw [HTGeometry.monicMomentAdmissionPolynomial_natDegree]
  have hT : (xiShiftedCanonicalAdmissionHardEdgeSource w n).natDegree ≤ 2 * n + 2 := by
    dsimp only [xiShiftedCanonicalAdmissionHardEdgeSource]
    exact (natDegree_xiShiftedHardEdgeAdaptiveBilinearSource_le hA hA (w ^ (2 : ℕ))).trans
      (by omega)
  exact hasDerivAt_xiShiftedHardEdgeRadialPrimitive
    (sq_pos_of_pos (by linarith : 0 < w)) hT

end

end RHTower
