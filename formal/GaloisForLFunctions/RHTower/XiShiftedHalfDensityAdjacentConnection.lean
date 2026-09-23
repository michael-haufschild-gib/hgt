import GaloisForLFunctions.RHTower.XiShiftedAdaptiveHalfDensityCanonicalMismatch

open Complex Matrix Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Polarized moving-frame product rule for two finite polynomial curves. -/
theorem hasDerivAt_xiShiftedMomentInner_movingCross
    {y : ℝ} (hy : 0 < y) {N : ℕ}
    (c d : Fin N → ℝ → ℝ) (dc dd : Fin N → ℝ)
    (hc : ∀ i : Fin N, HasDerivAt (c i) (dc i) y)
    (hd : ∀ i : Fin N, HasDerivAt (d i) (dd i) y) :
    HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (finitePolynomialCurve d v))
      (-HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (X * xiShiftedBoundaryShiftedEuler 1
            (finitePolynomialCurve c y * finitePolynomialCurve d y)) +
        HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (finitePolynomialVelocity dc) (finitePolynomialCurve d y) +
        HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (finitePolynomialCurve c y) (finitePolynomialVelocity dd)) y := by
  let s : ℝ → ℕ → ℝ := fun v k => (xiShiftedReciprocalMoment v k).re
  let md : ℕ → ℝ := fun k => -((k : ℝ) + 1) * s y (k + 1)
  let move : ℝ := ∑ i : Fin N, ∑ j : Fin N,
    (dc i * d j y + c i y * dd j) * s y ((i : ℕ) + (j : ℕ))
  let fixed : ℝ := ∑ i : Fin N, ∑ j : Fin N,
    (c i y * d j y) * md ((i : ℕ) + (j : ℕ))
  have htotal : HasDerivAt
      (fun v => ∑ i : Fin N, ∑ j : Fin N,
        c i v * d j v * s v ((i : ℕ) + (j : ℕ)))
      (move + fixed) y := by
    have hraw := HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
      (fun i _ => HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
        (fun j _ => ((hc i).mul (hd j)).mul
          (hasDerivAt_re_xiShiftedReciprocalMoment hy
            ((i : ℕ) + (j : ℕ)))))
    have hfun :
        (∑ i : Fin N, ∑ j : Fin N,
          c i * d j *
            (fun v => (xiShiftedReciprocalMoment v
              ((i : ℕ) + (j : ℕ))).re)) =
          (fun v => ∑ i : Fin N, ∑ j : Fin N,
            c i v * d j v * s v ((i : ℕ) + (j : ℕ))) := by
      funext v
      simp only [s, Finset.sum_apply, Pi.mul_apply]
    rw [hfun] at hraw
    simpa only [s, md, move, fixed, Nat.cast_add,
      Finset.sum_add_distrib, Pi.mul_apply] using hraw
  have htotal' : HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (finitePolynomialCurve d v))
      (move + fixed) y := by
    rw [show (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (finitePolynomialCurve d v)) =
      (fun v => ∑ i : Fin N, ∑ j : Fin N,
        c i v * d j v * s v ((i : ℕ) + (j : ℕ))) by
      funext v
      exact momentInner_finitePolynomialCurve_curve (s v) c d v]
    exact htotal
  have hfixedDirect : HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c y) (finitePolynomialCurve d y)) fixed y := by
    rw [show (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c y) (finitePolynomialCurve d y)) =
      (fun v => ∑ i : Fin N, ∑ j : Fin N,
        c i y * d j y * s v ((i : ℕ) + (j : ℕ))) by
      funext v
      exact momentInner_finitePolynomialCurve_curve (s v) c d y]
    have hraw := HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
      (fun i _ => HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
        (fun j _ => (hasDerivAt_re_xiShiftedReciprocalMoment hy
          ((i : ℕ) + (j : ℕ))).const_mul (c i y * d j y)))
    have hfun :
        (∑ i : Fin N, ∑ j : Fin N,
          (fun v => c i y * d j y *
            (xiShiftedReciprocalMoment v ((i : ℕ) + (j : ℕ))).re)) =
          (fun v => ∑ i : Fin N, ∑ j : Fin N,
            c i y * d j y * s v ((i : ℕ) + (j : ℕ))) := by
      funext v
      simp only [s, Finset.sum_apply]
    rw [hfun] at hraw
    simpa only [s, md, fixed, Nat.cast_add, Finset.sum_apply] using hraw
  have hfixedSource := hasDerivAt_xiShiftedMomentFunctional_sourceConnection hy
    (finitePolynomialCurve c y * finitePolynomialCurve d y)
  have hfixed : fixed =
      -HTGeometry.momentFunctional (s y)
        (X * xiShiftedBoundaryShiftedEuler 1
          (finitePolynomialCurve c y * finitePolynomialCurve d y)) := by
    apply hfixedDirect.unique
    simpa only [HTGeometry.momentInner] using hfixedSource
  have hmove : move =
      HTGeometry.momentInner (s y)
        (finitePolynomialVelocity dc) (finitePolynomialCurve d y) +
      HTGeometry.momentInner (s y)
        (finitePolynomialCurve c y) (finitePolynomialVelocity dd) := by
    change (∑ i : Fin N, ∑ j : Fin N,
      (dc i * d j y + c i y * dd j) * s y ((i : ℕ) + (j : ℕ))) = _
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [← momentInner_finitePolynomialVelocity_curve (s y) dc d y]
    let e : Fin N → ℝ → ℝ := fun i _ => dd i
    have hsecond := momentInner_finitePolynomialCurve_curve (s y) c e y
    change HTGeometry.momentInner (s y) (finitePolynomialCurve c y)
      (finitePolynomialVelocity dd) = _ at hsecond
    rw [← hsecond]
  rw [hmove, hfixed] at htotal'
  apply htotal'.congr_deriv
  ring

/-- The half-density generator raises degree by at most one. -/
theorem natDegree_xiShiftedMobiusHalfDensityGenerator_le_add_one
    (P : Polynomial ℝ) :
    (xiShiftedMobiusHalfDensityGenerator P).natDegree ≤ P.natDegree + 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  cases k with
  | zero =>
      simp [xiShiftedMobiusHalfDensityGenerator, xiShiftedMobiusDensityGenerator]
  | succ k =>
      rw [coeff_xiShiftedMobiusHalfDensityGenerator_succ]
      have hPk : P.coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
      rw [hPk, mul_zero]

/-- Metric compatibility identifies canonical covariant velocity with the half-density generator
in the adjoint slot against every lower polynomial. -/
theorem momentInner_xiShiftedCanonicalAdmissionCovariantVelocity_eq_generatorAdjoint
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {Q : Polynomial ℝ} (hQnat : Q.natDegree < n) :
    HTGeometry.momentInner (fun k => (xiShiftedReciprocalMoment y k).re)
        (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n) -
          xiShiftedMobiusHalfDensityGenerator
            (HTGeometry.monicOrtho
              (fun k => (xiShiftedReciprocalMoment y k).re) n)) Q =
      HTGeometry.momentInner (fun k => (xiShiftedReciprocalMoment y k).re)
        (HTGeometry.monicOrtho
          (fun k => (xiShiftedReciprocalMoment y k).re) n)
        (xiShiftedMobiusHalfDensityGenerator Q) := by
  let d : Fin (n + 1) → ℝ → ℝ := fun i _ => Polynomial.toFn (n + 1) Q i
  let dd : Fin (n + 1) → ℝ := fun _ => 0
  have hQwindow : Q.natDegree < n + 1 := by omega
  have hdcurve (v : ℝ) : finitePolynomialCurve d v = Q := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hQwindow
  have hdvelocity : finitePolynomialVelocity dd = 0 := by
    simp [finitePolynomialVelocity, dd, Polynomial.ofFn_eq_sum_monomial]
  have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH
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
            (HTGeometry.monicOrtho
              (fun k => (xiShiftedReciprocalMoment y k).re) n * Q)) +
        HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n)) Q) y := by
    simpa only [finitePolynomialCurve_xiShiftedCanonicalAdmission,
      hdcurve, hdvelocity, HTGeometry.momentInner_zero_right, add_zero,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH] using hcross
  have hposAdd := eventually_posDef_xiShiftedMomentHankelMatrix_add hy hH
  have hshift : Tendsto (fun v : ℝ => v - y) (nhds y) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr tendsto_id
  have hpos : ∀ᶠ v in nhds y,
      (xiShiftedMomentHankelMatrix v (n + 2)).PosDef := by
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
    have hdetv := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hv
    exact HTGeometry.momentInner_monicMomentAdmission_lower_eq_zero hdetv
      hQnat
  have hzero : HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n) Q) 0 y :=
    (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hevent
  have hderiv := hcross'.unique hzero
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let P := HTGeometry.monicOrtho s n
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

/-- Actual canonical covariant velocity is orthogonal to every polynomial two levels below. -/
theorem momentInner_xiShiftedCanonicalAdmissionCovariantVelocity_lower_eq_zero
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {Q : Polynomial ℝ} (hQdeg : Q.degree < ((n - 1 : ℕ) : WithBot ℕ)) :
    HTGeometry.momentInner (fun k => (xiShiftedReciprocalMoment y k).re)
        (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n) -
          xiShiftedMobiusHalfDensityGenerator
            (HTGeometry.monicOrtho
              (fun k => (xiShiftedReciprocalMoment y k).re) n)) Q = 0 := by
  by_cases hQzero : Q = 0
  · simp [hQzero]
  have hQnat : Q.natDegree < n - 1 :=
    (Polynomial.natDegree_lt_iff_degree_lt hQzero).mpr hQdeg
  have hadjoint :=
    momentInner_xiShiftedCanonicalAdmissionCovariantVelocity_eq_generatorAdjoint
      hy hH (Q := Q) (hQnat.trans (by omega))
  have hKnat : (xiShiftedMobiusHalfDensityGenerator Q).natDegree < n :=
    lt_of_le_of_lt (natDegree_xiShiftedMobiusHalfDensityGenerator_le_add_one Q) (by omega)
  have hKdeg : (xiShiftedMobiusHalfDensityGenerator Q).degree < (n : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hKnat)
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hPK : HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re)
      (HTGeometry.monicOrtho (fun k => (xiShiftedReciprocalMoment y k).re) n)
      (xiShiftedMobiusHalfDensityGenerator Q) = 0 :=
    HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below hbelow (by omega) hKdeg
  rw [hadjoint, hPK]

/-- The adjoint half-density generator sees exactly the previous Jacobi norm channel. -/
theorem momentInner_monicOrtho_mobiusHalfDensityGenerator_prev_eq
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 1 ≤ N) :
    HTGeometry.momentInner s (HTGeometry.monicOrtho s n)
        (xiShiftedMobiusHalfDensityGenerator
          (HTGeometry.monicOrtho s (n - 1))) =
      ((n : ℝ) - 1 / 2) * HTGeometry.monicOrthoNormSq s n := by
  let c : ℝ := (n : ℝ) - 1 / 2
  let R : Polynomial ℝ :=
    xiShiftedMobiusHalfDensityGenerator (HTGeometry.monicOrtho s (n - 1)) -
      c • HTGeometry.monicOrtho s n
  have hRdeg : R.degree < (n : WithBot ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    have hnk : n ≤ k := by exact_mod_cast hk
    by_cases hkn : k = n
    · subst k
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      dsimp only [R]
      rw [Polynomial.coeff_sub, Polynomial.coeff_smul,
        coeff_xiShiftedMobiusHalfDensityGenerator_succ]
      simp only [Nat.succ_sub_one, HTGeometry.coeff_monicOrtho_self]
      dsimp only [c]
      push_cast
      ring
    · have hhigh : n < k := lt_of_le_of_ne hnk (Ne.symm hkn)
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      dsimp only [R]
      rw [Polynomial.coeff_sub, Polynomial.coeff_smul,
        coeff_xiShiftedMobiusHalfDensityGenerator_succ]
      have hprev : (HTGeometry.monicOrtho s (n - 1)).coeff m = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [HTGeometry.natDegree_monicOrtho]
        omega
      have hself : (HTGeometry.monicOrtho s n).coeff (m + 1) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [HTGeometry.natDegree_monicOrtho]
        omega
      rw [hprev, hself]
      ring
  have hRorth : HTGeometry.momentInner s (HTGeometry.monicOrtho s n) R = 0 :=
    HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below h (by omega) hRdeg
  dsimp only [R] at hRorth
  rw [HTGeometry.momentInner_sub_right, HTGeometry.momentInner_smul_right] at hRorth
  dsimp only [c] at hRorth
  change HTGeometry.momentInner s (HTGeometry.monicOrtho s n)
      (xiShiftedMobiusHalfDensityGenerator (HTGeometry.monicOrtho s (n - 1))) =
    ((n : ℝ) - 1 / 2) *
      HTGeometry.momentInner s (HTGeometry.monicOrtho s n) (HTGeometry.monicOrtho s n)
  linarith

/-- **Exact monic nearest-neighbor connection.**  Actual inverse-Hankel admission velocity differs
from the source-native monic landing by one previous orthogonal direction and no other tangent. -/
theorem finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_monicHalfDensityLanding_add_prev
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n) =
      xiShiftedAdaptiveMonicHalfDensityLanding
          (fun k => (xiShiftedReciprocalMoment y k).re) n +
        (((n : ℝ) - 1 / 2) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) n) •
          HTGeometry.monicOrtho
            (fun k => (xiShiftedReciprocalMoment y k).re) (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let V := finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y (m + 1))
  let M := xiShiftedAdaptiveMonicHalfDensityLanding s (m + 1)
  let P := HTGeometry.monicOrtho s (m + 1)
  let Pprev := HTGeometry.monicOrtho s m
  let beta := HTGeometry.monicOrthoBeta s (m + 1)
  let c : ℝ := (m + 1 : ℕ) - 1 / 2
  let W := V - M
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hVdeg : V.natDegree < m + 1 := by
    exact natDegree_finitePolynomialVelocity_xiShiftedCanonicalAdmission_lt
      (by omega) y
  have hMdeg : M.natDegree < m + 1 := by
    exact natDegree_xiShiftedAdaptiveMonicHalfDensityLanding_lt hbelow (by omega) (by omega)
  have hWdeg : W.natDegree < m + 1 := by
    exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hVdeg hMdeg)
  have hadjoint :=
    momentInner_xiShiftedCanonicalAdmissionCovariantVelocity_eq_generatorAdjoint
      hy hH (Q := Pprev) (by
        dsimp only [Pprev, s]
        rw [HTGeometry.natDegree_monicOrtho]
        omega)
  have hprevGenerator :=
    momentInner_monicOrtho_mobiusHalfDensityGenerator_prev_eq
      hbelow (n := m + 1) (by omega) (by omega)
  have hadjoint' : HTGeometry.momentInner s
      (V - xiShiftedMobiusHalfDensityGenerator P) Pprev =
        c * HTGeometry.monicOrthoNormSq s (m + 1) := by
    simpa only [s, V, P, Pprev, c] using hadjoint.trans hprevGenerator
  have hnextOrth : HTGeometry.momentInner s
      (HTGeometry.monicOrtho s (m + 2)) Pprev = 0 :=
    HTGeometry.monicOrtho_inner_eq_zero_below hbelow (by omega) (by omega) (by omega)
  have hselfOrth : HTGeometry.momentInner s P Pprev = 0 := by
    dsimp only [P, Pprev]
    exact HTGeometry.monicOrtho_inner_eq_zero_below hbelow (by omega) (by omega) (by omega)
  have hMpair : HTGeometry.momentInner s M Pprev =
      HTGeometry.momentInner s (xiShiftedMobiusHalfDensityGenerator P) Pprev := by
    dsimp only [M, P, Pprev]
    unfold xiShiftedAdaptiveMonicHalfDensityLanding
      xiShiftedAdaptiveHalfDensityLanding
    rw [HTGeometry.momentInner_sub_left, HTGeometry.momentInner_sub_left,
      HTGeometry.momentInner_smul_left, HTGeometry.momentInner_smul_left,
      hnextOrth, hselfOrth, mul_zero, sub_zero]
    ring
  have hWpair : HTGeometry.momentInner s W Pprev =
      c * HTGeometry.monicOrthoNormSq s (m + 1) := by
    dsimp only [W]
    rw [HTGeometry.momentInner_sub_left, hMpair]
    rw [HTGeometry.momentInner_sub_left] at hadjoint'
    linarith
  have hWcoeffPair := momentInner_lowerPolynomial_prevMonic_eq_coeff_mul_norm_below
    hbelow (n := m + 1) (by omega) (by omega) hWdeg
  have hprevpos : 0 < HTGeometry.monicOrthoNormSq s m :=
    HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hprevne : HTGeometry.monicOrthoNormSq s m ≠ 0 := ne_of_gt hprevpos
  have hWcoeff : W.coeff m = c * beta := by
    rw [Nat.succ_sub_one] at hWcoeffPair
    rw [hWpair] at hWcoeffPair
    dsimp only [beta]
    simp only [HTGeometry.monicOrthoBeta]
    field_simp [hprevne]
    nlinarith
  let D := W - (c * beta) • Pprev
  have hDdeg : D.degree < (m : WithBot ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    have hmk : m ≤ k := by exact_mod_cast hk
    by_cases hkm : k = m
    · subst k
      dsimp only [D]
      rw [Polynomial.coeff_sub, Polynomial.coeff_smul, hWcoeff]
      have hmonic : Pprev.coeff m = 1 := by
        dsimp only [Pprev]
        exact HTGeometry.coeff_monicOrtho_self s m
      rw [hmonic]
      ring
    · have hmks : m + 1 ≤ k := by omega
      have hWzero : W.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (hWdeg.trans_le hmks)
      have hPzero : Pprev.coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        dsimp only [Pprev]
        rw [HTGeometry.natDegree_monicOrtho]
        omega
      dsimp only [D]
      rw [Polynomial.coeff_sub, Polynomial.coeff_smul, hWzero, hPzero]
      ring
  have hVD : HTGeometry.momentInner s
      (V - xiShiftedMobiusHalfDensityGenerator P) D = 0 := by
    simpa only [s, V, P] using
      momentInner_xiShiftedCanonicalAdmissionCovariantVelocity_lower_eq_zero
        hy (by omega) hH hDdeg
  have hnextD : HTGeometry.momentInner s
      (HTGeometry.monicOrtho s (m + 2)) D = 0 :=
    HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below hbelow (by omega)
      (hDdeg.trans (by exact_mod_cast (by omega : m < m + 2)))
  have hselfD : HTGeometry.momentInner s P D = 0 := by
    dsimp only [P]
    exact HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below hbelow (by omega)
      (hDdeg.trans (by exact_mod_cast (by omega : m < m + 1)))
  have hMD : HTGeometry.momentInner s
      (M - xiShiftedMobiusHalfDensityGenerator P) D = 0 := by
    dsimp only [M, P]
    unfold xiShiftedAdaptiveMonicHalfDensityLanding
      xiShiftedAdaptiveHalfDensityLanding
    rw [HTGeometry.momentInner_sub_left, HTGeometry.momentInner_sub_left,
      HTGeometry.momentInner_sub_left, HTGeometry.momentInner_smul_left,
      HTGeometry.momentInner_smul_left, hnextD, hselfD, mul_zero]
    ring
  have hWD : HTGeometry.momentInner s W D = 0 := by
    dsimp only [W]
    rw [HTGeometry.momentInner_sub_left]
    rw [HTGeometry.momentInner_sub_left] at hVD hMD
    linarith
  have hprevD : HTGeometry.momentInner s Pprev D = 0 := by
    dsimp only [Pprev]
    exact HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below hbelow (by omega) hDdeg
  have hDD : HTGeometry.momentInner s D D = 0 := by
    dsimp only [D]
    rw [HTGeometry.momentInner_sub_left, HTGeometry.momentInner_smul_left, hWD, hprevD]
    ring
  have hDzero : D = 0 := by
    by_contra hDne
    have hDnat : D.natDegree < m :=
      (Polynomial.natDegree_lt_iff_degree_lt hDne).mpr hDdeg
    have hDpos := hbelow.pos_of_ne_zero_of_natDegree_lt D hDne (hDnat.trans (by omega))
    linarith
  change V = M + (c * beta) • Pprev
  change W - (c * beta) • Pprev = 0 at hDzero
  dsimp only [W] at hDzero
  linear_combination hDzero

/-- The formerly open visible mismatch is exactly the previous Jacobi edge. -/
theorem xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch_eq_prevJacobiEdge
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch y n =
      ((n : ℝ) - 1 / 2) * HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  rw [xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch,
    finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_monicHalfDensityLanding_add_prev
      hy hn hH]
  simp only [add_sub_cancel_left, Polynomial.coeff_smul]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one, HTGeometry.coeff_monicOrtho_self, smul_eq_mul, mul_one]

/-- Actual subleading canonical velocity is an explicit positive Jacobi energy. -/
theorem coeff_finitePolynomialVelocity_xiShiftedCanonicalAdmission_prev_eq_jacobiEnergy
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    (finitePolynomialVelocity
      (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1) =
      (∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) j ^ (2 : ℕ)) +
        2 * (∑ j ∈ Finset.range n,
          HTGeometry.monicOrthoBeta
            (fun k => (xiShiftedReciprocalMoment y k).re) j) +
        2 * (n : ℝ) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  have hmismatch :=
    xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch_eq_velocityCoeff_sub_energy
      hn hH
  have hedge :=
    xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch_eq_prevJacobiEdge hy hn hH
  rw [hedge] at hmismatch
  simp only [xiShiftedAdaptiveMonicHalfDensityLandingEnergy] at hmismatch
  linarith

/-- Strict positivity of every actual subleading canonical coefficient velocity. -/
theorem coeff_finitePolynomialVelocity_xiShiftedCanonicalAdmission_prev_pos
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 < (finitePolynomialVelocity
      (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hsquares : 0 ≤ ∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below hbelow (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hlast : 0 < 2 * (n : ℝ) * HTGeometry.monicOrthoBeta s n :=
    mul_pos (mul_pos (by norm_num) (by positivity))
      (HTGeometry.monicOrthoBeta_pos_below hbelow hn (by omega))
  rw [coeff_finitePolynomialVelocity_xiShiftedCanonicalAdmission_prev_eq_jacobiEnergy
    hy hn hH]
  change 0 < (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
    2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
    2 * (n : ℝ) * HTGeometry.monicOrthoBeta s n
  positivity

/-- Canonical monic first coefficient increases strictly inside every positive chamber. -/
theorem deriv_xiShiftedCanonicalAdmissionFirstCoeff_pos
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 < deriv (fun v => xiShiftedCanonicalAdmissionFirstCoeff v n) y := by
  have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH
  rw [(hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff hy hn hdet).deriv]
  exact coeff_finitePolynomialVelocity_xiShiftedCanonicalAdmission_prev_pos hy hn hH

/-- After eliminating the canonical mismatch, raw dissipation reserve is one terminal Jacobi
Riccati defect; no hidden lower-coordinate term remains. -/
theorem xiShiftedCanonicalAdmissionHalfDensityDissipationReserve_eq_terminalJacobiDefect
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionHalfDensityDissipationReserve y n =
      (n + 1 : ℝ) * HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) n ^ (2 : ℕ) +
        HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) n *
          (∑ j ∈ Finset.range n,
            HTGeometry.monicOrthoAlpha
              (fun k => (xiShiftedReciprocalMoment y k).re) j) +
        (1 - (n : ℝ)) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) n +
        (n + 1 : ℝ) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let alpha := HTGeometry.monicOrthoAlpha s n
  have hsquares :
      (∑ j ∈ Finset.range n,
          (HTGeometry.monicOrthoAlpha s j + alpha / 2) ^ (2 : ℕ)) =
        (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
          alpha * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
          (n : ℝ) * alpha ^ (2 : ℕ) / 4 := by
    have hpoint (j : ℕ) :
        (HTGeometry.monicOrthoAlpha s j + alpha / 2) ^ (2 : ℕ) =
          HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ) +
            alpha * HTGeometry.monicOrthoAlpha s j + alpha ^ (2 : ℕ) / 4 := by ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [xiShiftedCanonicalAdmissionHalfDensityDissipationReserve,
    xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch_eq_prevJacobiEdge hy hn hH]
  simp only [HTGeometry.adaptiveOrthoJacobiEnergy,
    xiShiftedAdaptiveMonicHalfDensityLandingEnergy]
  change
      ((∑ j ∈ Finset.range n,
          (HTGeometry.monicOrthoAlpha s j + alpha / 2) ^ (2 : ℕ)) +
        (3 * (n : ℝ) / 4 + 1) * alpha ^ (2 : ℕ) +
        2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
        (n + 1 : ℝ) *
          (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1))) -
      ((∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
        2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
        ((n : ℝ) + 1 / 2) * HTGeometry.monicOrthoBeta s n) -
      ((n : ℝ) - 1 / 2) * HTGeometry.monicOrthoBeta s n = _
  rw [hsquares]
  ring

/-- Diagonal shadow of the nonisospectral Jacobi Lax law. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionAlpha_eq_adjacentJacobiFlow
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionAlpha v n)
      (2 * ((n : ℝ) - 1) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) n -
        2 * ((n : ℝ) + 1) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) -
        HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) n ^ (2 : ℕ)) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let alpha := HTGeometry.monicOrthoAlpha s n
  let Vcoeff := (finitePolynomialVelocity
    (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1)
  have hmismatch :=
    xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch_eq_velocityCoeff_sub_energy
      hn hH
  have hedge :=
    xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch_eq_prevJacobiEdge hy hn hH
  have hVcoeff : Vcoeff =
      xiShiftedAdaptiveMonicHalfDensityLandingEnergy s n +
        ((n : ℝ) - 1 / 2) * HTGeometry.monicOrthoBeta s n := by
    dsimp only [Vcoeff, s]
    linarith
  have hflow := hasDerivAt_xiShiftedCanonicalAdmissionAlpha_eq_sourceConnection
    hy hn hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hfirst := HTGeometry.monicOrthoFirstCoeff_eq_neg_sum_below hbelow
    (by omega : n ≤ n + 2)
  have hsquares :
      (∑ j ∈ Finset.range n,
          (HTGeometry.monicOrthoAlpha s j + alpha / 2) ^ (2 : ℕ)) =
        (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
          alpha * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
          (n : ℝ) * alpha ^ (2 : ℕ) / 4 := by
    have hpoint (j : ℕ) :
        (HTGeometry.monicOrthoAlpha s j + alpha / 2) ^ (2 : ℕ) =
          HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ) +
            alpha * HTGeometry.monicOrthoAlpha s j + alpha ^ (2 : ℕ) / 4 := by ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  apply hflow.congr_deriv
  change
      -2 * HTGeometry.adaptiveOrthoJacobiEnergy s n + 2 * Vcoeff -
        alpha *
          (2 * HTGeometry.monicOrthoFirstCoeff s n -
            ((2 * n + 1 : ℕ) : ℝ) * alpha) = _
  rw [hVcoeff, hfirst]
  simp only [HTGeometry.adaptiveOrthoJacobiEnergy,
    xiShiftedAdaptiveMonicHalfDensityLandingEnergy]
  rw [hsquares]
  push_cast
  ring

/-- Terminal diagonal growth relative to the cumulative current and forced quadratic drift. -/
def xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect (y : ℝ) (n : ℕ) : ℝ :=
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  2 * (n : ℝ) * HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ) +
    HTGeometry.monicOrthoAlpha s n *
      xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n -
    (2 * ((n : ℝ) - 1) * HTGeometry.monicOrthoBeta s n -
      2 * ((n : ℝ) + 1) * HTGeometry.monicOrthoBeta s (n + 1) -
      HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ))

/-- The reserve is exactly half the terminal diagonal Riccati defect. -/
theorem two_mul_xiShiftedCanonicalAdmissionHalfDensityDissipationReserve_eq_terminalRiccatiDefect
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    2 * xiShiftedCanonicalAdmissionHalfDensityDissipationReserve y n =
      xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect y n := by
  rw [xiShiftedCanonicalAdmissionHalfDensityDissipationReserve_eq_terminalJacobiDefect
    hy hn hH, xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect,
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_trace hn hH]
  ring

/-- Raw canonical odd-current drift is negative norm times the terminal Jacobi Riccati defect. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_neg_norm_mul_terminalRiccatiDefect
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n)
        (X * HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n))
      (-HTGeometry.monicOrthoNormSq
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
        xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect y n) y := by
  have h :=
    hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_neg_two_norm_mul_halfDensityReserve
      hy hn hH
  have hreserve :=
    two_mul_xiShiftedCanonicalAdmissionHalfDensityDissipationReserve_eq_terminalRiccatiDefect
      hy hn hH
  apply h.congr_deriv
  rw [← hreserve]
  ring

end

end RHTower
