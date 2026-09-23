import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionHardEdgeWorldlineSourceLaw
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionSingularSourceLaw

/-!
# Flat-contact transmutation of the canonical shifted-Xi source

At a flat canonical Hankel face, actual inverse-Hankel coefficient velocity is exactly the
degree-lowered Möbius tangent. Consequently every simple Gauss root follows `x' = -x²`, so its
hard coordinate `x⁻¹-y` is first-order frozen. Arithmetic forcing has not vanished: at tangential
contact the actual division-free norm flux differentiates to the adaptive completed `P^sharp`
aggregate formed before reflection aggregation.
-/

open Complex Matrix Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Head-positive version of canonical adjoint source transport. Only the block used by the monic
inverse-Hankel solve is required; no positivity beyond the singular face is assumed. -/
theorem momentInner_xiShiftedCanonicalAdmissionCovariantVelocity_eq_generatorAdjoint_of_headPosDef
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hhead : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef)
    {Q : Polynomial ℝ} (hQnat : Q.natDegree < n) :
    HTGeometry.momentInner (fun k => (xiShiftedReciprocalMoment y k).re)
        (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n) -
          xiShiftedMobiusHalfDensityGenerator
            (HTGeometry.monicMomentAdmissionPolynomial
              (fun k => (xiShiftedReciprocalMoment y k).re) n)) Q =
      HTGeometry.momentInner (fun k => (xiShiftedReciprocalMoment y k).re)
        (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment y k).re) n)
        (xiShiftedMobiusHalfDensityGenerator Q) := by
  let d : Fin (n + 1) → ℝ → ℝ := fun i _ => Polynomial.toFn (n + 1) Q i
  let dd : Fin (n + 1) → ℝ := fun _ => 0
  have hQwindow : Q.natDegree < n + 1 := by omega
  have hdcurve (v : ℝ) : finitePolynomialCurve d v = Q := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hQwindow
  have hdvelocity : finitePolynomialVelocity dd = 0 := by
    simp [finitePolynomialVelocity, dd, Polynomial.ofFn_eq_sum_monomial]
  have hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0 :=
    ne_of_gt hhead.det_pos
  have hc : ∀ i : Fin (n + 1),
      HasDerivAt (xiShiftedCanonicalAdmissionCurve n i)
        (xiShiftedCanonicalAdmissionVelocity y n i) y :=
    hasDerivAt_xiShiftedCanonicalAdmissionCurve hy n hdet
  have hd : ∀ i : Fin (n + 1), HasDerivAt (d i) (dd i) y := by
    intro i
    exact hasDerivAt_const (x := y) (Polynomial.toFn (n + 1) Q i)
  have hcross := hasDerivAt_xiShiftedMomentInner_movingCross hy
    (xiShiftedCanonicalAdmissionCurve n) d
    (xiShiftedCanonicalAdmissionVelocity y n) dd hc hd
  have hcross' : HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n) Q)
      (-HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (X * xiShiftedBoundaryShiftedEuler 1
            (HTGeometry.monicMomentAdmissionPolynomial
              (fun k => (xiShiftedReciprocalMoment y k).re) n * Q)) +
        HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n)) Q) y := by
    simpa only [finitePolynomialCurve_xiShiftedCanonicalAdmission,
      hdcurve, hdvelocity, HTGeometry.momentInner_zero_right, add_zero] using hcross
  have hposAdd := eventually_posDef_xiShiftedMomentHankelMatrix_add hy hhead
  have hshift : Tendsto (fun v : ℝ => v - y) (nhds y) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr tendsto_id
  have hpos : ∀ᶠ v in nhds y,
      (xiShiftedMomentHankelMatrix v n).PosDef := by
    filter_upwards [hshift.eventually hposAdd] with v hv
    have heq : y + (v - y) = v := by ring
    rw [heq] at hv
    exact hv
  have hevent :
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n) Q) =ᶠ[nhds y]
        (fun _ => (0 : ℝ)) := by
    filter_upwards [hpos] with v hv
    have hv' : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) n).PosDef := by
      rw [show HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment v k).re) n =
        xiShiftedMomentHankelMatrix v n by
          ext i j
          rfl]
      exact hv
    exact HTGeometry.momentInner_monicMomentAdmission_lower_eq_zero
      (ne_of_gt hv'.det_pos) hQnat
  have hzero : HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n) Q) 0 y :=
    (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hevent
  have hderiv := hcross'.unique hzero
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let P := HTGeometry.monicMomentAdmissionPolynomial s n
  have hsourcePoly := congrArg (HTGeometry.momentFunctional s)
    (xiShiftedMobiusHalfDensityGenerator_product P Q)
  have hsource :
      HTGeometry.momentFunctional s
          (X * xiShiftedBoundaryShiftedEuler 1 (P * Q)) =
        HTGeometry.momentInner s (xiShiftedMobiusHalfDensityGenerator P) Q +
          HTGeometry.momentInner s P (xiShiftedMobiusHalfDensityGenerator Q) := by
    simpa only [HTGeometry.momentInner, HTGeometry.momentFunctional_add] using hsourcePoly.symm
  change -HTGeometry.momentFunctional s
      (X * xiShiftedBoundaryShiftedEuler 1 (P * Q)) +
      HTGeometry.momentInner s
        (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n)) Q = 0 at hderiv
  rw [hsource] at hderiv
  rw [HTGeometry.momentInner_sub_left]
  linarith

/-- At a flat face, actual inverse-Hankel coefficient velocity is exactly the degree-lowered
Möbius tangent `X²P' - nXP + [X^(n-1)]P · P`. -/
theorem finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_normRemainder_of_flatFace
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0) :
    finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n) =
      HTGeometry.monicMomentAdmissionNormRemainder
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let P := HTGeometry.monicMomentAdmissionPolynomial s n
  let V := finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n)
  let R := HTGeometry.monicMomentAdmissionNormRemainder s n
  let D := V - R
  have hhead' : (HTGeometry.momentHankelMatrix s n).PosDef := by
    rw [show HTGeometry.momentHankelMatrix s n =
      xiShiftedMomentHankelMatrix y n by
        ext i j
        rfl]
    exact hhead
  have hVdeg : V.natDegree < n := by
    exact natDegree_finitePolynomialVelocity_xiShiftedCanonicalAdmission_lt hn y
  have hRdeg : R.natDegree < n := by
    by_cases hRzero : R = 0
    · rw [hRzero, Polynomial.natDegree_zero]
      exact hn
    · exact (Polynomial.natDegree_lt_iff_degree_lt hRzero).mpr (by
        simpa only [R] using HTGeometry.monicMomentAdmissionNormRemainder_degree_lt s hn)
  have hDdeg : D.natDegree < n := by
    exact lt_of_le_of_lt (Polynomial.natDegree_sub_le V R) (max_lt hVdeg hRdeg)
  have hflat' : HTGeometry.momentHankelMatrix s (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector s n = 0 := by
    rw [show HTGeometry.momentHankelMatrix s (n + 1) =
      xiShiftedMomentHankelMatrix y (n + 1) by
        ext i j
        rfl]
    simpa only [s] using hflat
  have hflatOrth {Q : Polynomial ℝ} (hQdeg : Q.natDegree < n + 1) :
      HTGeometry.momentInner s P Q = 0 := by
    exact HTGeometry.momentInner_finiteHankelNullPolynomial_eq_zero_of_kernel
      hflat' hQdeg
  have hKDdeg : (xiShiftedMobiusHalfDensityGenerator D).natDegree < n + 1 :=
    lt_of_le_of_lt (natDegree_xiShiftedMobiusHalfDensityGenerator_le_add_one D)
      (Nat.add_lt_add_right hDdeg 1)
  have hadjoint :=
    momentInner_xiShiftedCanonicalAdmissionCovariantVelocity_eq_generatorAdjoint_of_headPosDef
      hy hhead' (Q := D) hDdeg
  have hadjoint' : HTGeometry.momentInner s
      (V - xiShiftedMobiusHalfDensityGenerator P) D =
        HTGeometry.momentInner s P (xiShiftedMobiusHalfDensityGenerator D) := by
    simpa only [s, P, V] using hadjoint
  have hright :
      HTGeometry.momentInner s P (xiShiftedMobiusHalfDensityGenerator D) = 0 :=
    hflatOrth hKDdeg
  have hPD : HTGeometry.momentInner s P D = 0 :=
    hflatOrth (hDdeg.trans (Nat.lt_succ_self n))
  have hXDdeg : (X * D).natDegree < n + 1 := by
    calc
      (X * D).natDegree ≤ X.natDegree + D.natDegree := Polynomial.natDegree_mul_le
      _ = 1 + D.natDegree := by rw [Polynomial.natDegree_X]
      _ < 1 + n := Nat.add_lt_add_left hDdeg 1
      _ = n + 1 := by omega
  have hPXD : HTGeometry.momentInner s P (X * D) = 0 := hflatOrth hXDdeg
  have hXPD : HTGeometry.momentInner s (X * P) D = 0 := by
    rw [HTGeometry.momentInner_def] at hPXD ⊢
    rw [show (X * P) * D = P * (X * D) by ring]
    exact hPXD
  have hpoly :
      V - xiShiftedMobiusHalfDensityGenerator P =
        D - ((n : ℝ) + 1 / 2) • (X * P) + P.coeff (n - 1) • P := by
    simp only [D, R, P, HTGeometry.monicMomentAdmissionNormRemainder,
      xiShiftedMobiusHalfDensityGenerator, xiShiftedMobiusDensityGenerator,
      Polynomial.smul_eq_C_mul]
    rw [Polynomial.C_add]
    ring
  have hleft : HTGeometry.momentInner s
      (V - xiShiftedMobiusHalfDensityGenerator P) D =
        HTGeometry.momentInner s D D := by
    rw [hpoly, HTGeometry.momentInner_add_left, HTGeometry.momentInner_sub_left,
      HTGeometry.momentInner_smul_left, HTGeometry.momentInner_smul_left,
      hXPD, hPD]
    ring
  rw [hleft, hright] at hadjoint'
  have hDzero : D = 0 := by
    by_contra hDne
    have hpos := HTGeometry.momentInner_self_pos_of_natDegree_lt hhead' hDne hDdeg
    linarith
  have hVR : V = R := sub_eq_zero.mp hDzero
  simpa only [V, R] using hVR

/-- Flat canonical coefficient transport evaluates as pure Möbius root transport. -/
theorem finitePolynomialVelocity_xiShiftedCanonicalAdmission_eval_root_of_flatFace
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    {x : ℝ}
    (hroot : (HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) n).eval x = 0) :
    (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n)).eval x =
      x ^ (2 : ℕ) * (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment y k).re) n).derivative.eval x := by
  rw [finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_normRemainder_of_flatFace
    hy hn hhead hflat]
  simp only [HTGeometry.monicMomentAdmissionNormRemainder, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_smul, smul_eq_mul, hroot, mul_zero, add_zero, sub_zero]

/-- Every differentiable simple flat Gauss-root branch follows the atomic Möbius root velocity. -/
theorem xiShiftedCanonicalAdmission_flatRootCurve_deriv_eq_neg_sq
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds y]
          fun _ => 0)
    (hsimple : (HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) n).derivative.eval (x y) ≠ 0) :
    xdot = -(x y) ^ (2 : ℕ) := by
  have hhead' : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef := by
    rw [show HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) n =
      xiShiftedMomentHankelMatrix y n by
        ext i j
        rfl]
    exact hhead
  have hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0 :=
    ne_of_gt hhead'.det_pos
  have hroot_y : (HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) n).eval (x y) = 0 := by
    simpa using hroot.self_of_nhds
  have hvelocity :=
    finitePolynomialVelocity_xiShiftedCanonicalAdmission_eval_root_of_flatFace
      hy hn hhead hflat hroot_y
  have hchain := xiShiftedCanonicalAdmission_rootCurve_chain hy n hdet hx hroot
  rw [hvelocity] at hchain
  have hproduct : ((x y) ^ (2 : ℕ) + xdot) *
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment y k).re) n).derivative.eval (x y) = 0 := by
    nlinarith only [hchain]
  rcases mul_eq_zero.mp hproduct with hzero | hzero
  · linarith
  · exact (hsimple hzero).elim

/-- Hard coordinate is first-order blind at every simple canonical flat root. -/
theorem hasDerivAt_xiShiftedCanonicalAdmission_reciprocalHardRoot_zero_of_flatFace
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds y]
          fun _ => 0)
    (hx0 : x y ≠ 0)
    (hsimple : (HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) n).derivative.eval (x y) ≠ 0) :
    HasDerivAt (fun v => (x v)⁻¹ - v) 0 y := by
  have hxdot := xiShiftedCanonicalAdmission_flatRootCurve_deriv_eq_neg_sq
    hy hn hhead hflat hx hroot hsimple
  have hhard := hasDerivAt_reciprocalHardRoot hx hx0
  rw [hxdot] at hhard
  refine hhard.congr_deriv ?_
  field_simp
  ring

/-- **Contact-order source transmutation.** At a tangential flat face, every simple hard-root
observer freezes to first order while actual admission norm flux differentiates to adaptive
completed `P^sharp` source formed before reflection aggregation. -/
theorem xiShiftedCanonicalAdmission_flatTangent_hardRootFreeze_and_completedSource
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n = 0)
    (htangent : xiShiftedHankelBoundaryMonicRemainder (w ^ (2 : ℕ))
      (HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n) = 0)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ (2 : ℕ)))
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds (w ^ (2 : ℕ))]
          fun _ => 0)
    (hx0 : x (w ^ (2 : ℕ)) ≠ 0)
    (hsimple : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).derivative.eval (x (w ^ (2 : ℕ))) ≠ 0) :
    HasDerivAt (fun v => (x v)⁻¹ - v) 0 (w ^ (2 : ℕ)) ∧
      (let P := HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n
       HasDerivAt (fun v => xiShiftedCanonicalAdmissionNormFlux v n)
        (((2 * n + 1 : ℕ) : ℝ) *
          xiShiftedCompletedMomentAggregate (w ^ (2 : ℕ)) 2
            (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
              (xiShiftedOddCrossingCoefficientPacket P))) (w ^ (2 : ℕ))) := by
  have hy : 0 < w ^ (2 : ℕ) := sq_pos_of_pos (by linarith : 0 < w)
  constructor
  · apply hasDerivAt_xiShiftedCanonicalAdmission_reciprocalHardRoot_zero_of_flatFace
      hy hn hhead hflat hx hroot hx0
    change (HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n).derivative.eval
        (x (w ^ (2 : ℕ))) ≠ 0 at hsimple
    exact hsimple
  · exact hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_eq_completedAggregate_of_flatTangent
      hw hn hhead hflat htangent

end

end RHTower
