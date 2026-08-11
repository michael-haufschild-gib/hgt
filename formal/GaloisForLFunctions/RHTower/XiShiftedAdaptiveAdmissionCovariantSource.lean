import GaloisForLFunctions.RHTower.XiShiftedAdaptiveOrthogonalSourceJacobiEnergy
import GaloisForLFunctions.HTGeometry.MomentFiniteCoordinateValue

/-!
# Covariant source law for moving shifted-Xi admission

For a finite coefficient curve `P(v)`, the derivative of the odd current
`L_v(P(v) X P(v))` splits exactly into the fixed-amplitude adaptive source and one moving-frame
term.  At a monic orthogonal admission the three-term recurrence collapses that term to the
subleading coefficient velocity times the orthogonal norm.  Subtracting this intrinsic connection
leaves `-2` times the strictly positive Jacobi source energy.

This proves a covariant Lyapunov law.  It also proves why ordinary monotonicity is false without
connection control: monicity removes the top velocity coefficient, but not the degree-`n-1`
coefficient seen by `X P_n`.
-/

open Complex Matrix MeasureTheory Set Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Polynomial curve represented by one fixed finite coefficient window. -/
def finitePolynomialCurve {N : ℕ} (c : Fin N → ℝ → ℝ) (v : ℝ) : Polynomial ℝ :=
  Polynomial.ofFn N (fun i => c i v)

/-- Polynomial tangent represented in the same finite coefficient window. -/
def finitePolynomialVelocity {N : ℕ} (dc : Fin N → ℝ) : Polynomial ℝ :=
  Polynomial.ofFn N dc

lemma momentInner_finitePolynomialCurve_X_curve
    (s : ℕ → ℝ) {N : ℕ} (c d : Fin N → ℝ → ℝ) (v : ℝ) :
    HTGeometry.momentInner s (finitePolynomialCurve c v)
        (X * finitePolynomialCurve d v) =
      ∑ i : Fin N, ∑ j : Fin N,
        c i v * d j v * s ((i : ℕ) + (j : ℕ) + 1) := by
  simp only [finitePolynomialCurve]
  rw [HTGeometry.momentInner_def, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.ofFn_eq_sum_monomial, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [HTGeometry.momentFunctional_finset_sum]
  simp_rw [HTGeometry.momentFunctional_finset_sum]
  simp only [X_mul_monomial, Polynomial.monomial_mul_monomial,
    HTGeometry.momentFunctional_monomial]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show (i : ℕ) + ((j : ℕ) + 1) = (i : ℕ) + (j : ℕ) + 1 by omega]

lemma momentInner_finitePolynomialCurve_X_self
    (s : ℕ → ℝ) {N : ℕ} (c : Fin N → ℝ → ℝ) (v : ℝ) :
    HTGeometry.momentInner s (finitePolynomialCurve c v)
        (X * finitePolynomialCurve c v) =
      ∑ i : Fin N, ∑ j : Fin N,
        c i v * c j v * s ((i : ℕ) + (j : ℕ) + 1) :=
  momentInner_finitePolynomialCurve_X_curve s c c v

lemma momentInner_finitePolynomialVelocity_X_curve
    (s : ℕ → ℝ) {N : ℕ} (dc : Fin N → ℝ) (c : Fin N → ℝ → ℝ) (v : ℝ) :
    HTGeometry.momentInner s (finitePolynomialVelocity dc)
        (X * finitePolynomialCurve c v) =
      ∑ i : Fin N, ∑ j : Fin N,
        dc i * c j v * s ((i : ℕ) + (j : ℕ) + 1) := by
  let d : Fin N → ℝ → ℝ := fun i _ => dc i
  simpa only [finitePolynomialCurve, finitePolynomialVelocity, d] using
    (momentInner_finitePolynomialCurve_X_curve s d c v)

/-- A polynomial tangent below degree `n` couples to `X P_n` through only its degree-`n-1`
coefficient.  This is the exact Gram--Schmidt connection coefficient. -/
lemma momentInner_lowerPolynomial_prevMonic_eq_coeff_mul_norm_below
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n ≤ N) {V : Polynomial ℝ} (hVdeg : V.natDegree < n) :
    HTGeometry.momentInner s V (HTGeometry.monicOrtho s (n - 1)) =
      V.coeff (n - 1) * HTGeometry.monicOrthoNormSq s (n - 1) := by
  let R := V - V.coeff (n - 1) • HTGeometry.monicOrtho s (n - 1)
  have hRdeg : R.degree < ((n - 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    have hkge : n - 1 ≤ k := by exact_mod_cast hk
    by_cases hkeq : k = n - 1
    · subst k
      have hPcoeff : (HTGeometry.monicOrtho s (n - 1)).coeff (n - 1) = 1 := by
        simpa only [HTGeometry.natDegree_monicOrtho_eq] using
          (HTGeometry.monicOrtho_monic s (n - 1)).coeff_natDegree
      simp only [R, Polynomial.coeff_sub, Polynomial.coeff_smul]
      rw [hPcoeff]
      ring
    · have hkn : n ≤ k := by omega
      have hVzero : V.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (hVdeg.trans_le hkn)
      have hPzero : (HTGeometry.monicOrtho s (n - 1)).coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [HTGeometry.natDegree_monicOrtho_eq]
        omega
      simp [R, hVzero, hPzero]
  have hRorth : HTGeometry.momentInner s R (HTGeometry.monicOrtho s (n - 1)) = 0 := by
    rw [HTGeometry.momentInner_comm]
    exact HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below h
      (by omega) hRdeg
  dsimp only [R] at hRorth
  rw [HTGeometry.momentInner_sub_left,
    HTGeometry.momentInner_smul_left] at hRorth
  rw [HTGeometry.monicOrthoNormSq.eq_def]
  linarith

lemma momentInner_velocity_X_monicOrtho_eq_norm_mul_coeff_below
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 1 ≤ N) {V : Polynomial ℝ} (hVdeg : V.natDegree < n) :
    HTGeometry.momentInner s V (X * HTGeometry.monicOrtho s n) =
      HTGeometry.monicOrthoNormSq s n * V.coeff (n - 1) := by
  rw [HTGeometry.X_mul_monicOrtho_below h hnN,
    HTGeometry.momentInner_add_right, HTGeometry.momentInner_add_right,
    HTGeometry.momentInner_smul_right, HTGeometry.momentInner_smul_right]
  have hhigh : HTGeometry.momentInner s V (HTGeometry.monicOrtho s (n + 1)) = 0 := by
    rw [HTGeometry.momentInner_comm]
    apply HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below h (by omega)
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by
      exact_mod_cast hVdeg.trans (Nat.lt_succ_self n))
  have hsame : HTGeometry.momentInner s V (HTGeometry.monicOrtho s n) = 0 := by
    rw [HTGeometry.momentInner_comm]
    apply HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below h (by omega)
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hVdeg)
  rw [hhigh, hsame, mul_zero, zero_add,
    momentInner_lowerPolynomial_prevMonic_eq_coeff_mul_norm_below h hn (by omega) hVdeg]
  rcases n with _ | n
  · omega
  · simp only [HTGeometry.monicOrthoBeta.eq_def, Nat.succ_sub_one]
    have hprev : HTGeometry.monicOrthoNormSq s n ≠ 0 :=
      ne_of_gt (HTGeometry.monicOrthoNorm_pos_below h (by omega))
    field_simp [hprev]
    ring

/-- Product rule for a moving finite polynomial and the shifted-Xi moment source connection. -/
theorem hasDerivAt_xiShiftedMomentInner_movingOddCurrent
    {y : ℝ} (hy : 0 < y) {N : ℕ}
    (c : Fin N → ℝ → ℝ) (dc : Fin N → ℝ)
    (hc : ∀ i : Fin N, HasDerivAt (c i) (dc i) y) :
    HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (X * finitePolynomialCurve c v))
      (-2 * HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (X * finitePolynomialCurve c y)
          (X * xiShiftedBoundaryShiftedEuler 1 (finitePolynomialCurve c y)) +
        2 * HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (finitePolynomialVelocity dc) (X * finitePolynomialCurve c y)) y := by
  let s : ℝ → ℕ → ℝ := fun v k => (xiShiftedReciprocalMoment v k).re
  let md : ℕ → ℝ := fun k => -((k : ℝ) + 1) * s y (k + 1)
  let move : ℝ := ∑ i : Fin N, ∑ j : Fin N,
    (dc i * c j y + c i y * dc j) * s y ((i : ℕ) + (j : ℕ) + 1)
  let fixed : ℝ := ∑ i : Fin N, ∑ j : Fin N,
    (c i y * c j y) * md ((i : ℕ) + (j : ℕ) + 1)
  have htotal : HasDerivAt
      (fun v => ∑ i : Fin N, ∑ j : Fin N,
        c i v * c j v * s v ((i : ℕ) + (j : ℕ) + 1))
      (move + fixed) y := by
    have hraw := HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
      (fun i _ => HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
        (fun j _ => ((hc i).mul (hc j)).mul
          (hasDerivAt_re_xiShiftedReciprocalMoment hy
            ((i : ℕ) + (j : ℕ) + 1))))
    have hfun :
        (∑ i : Fin N, ∑ j : Fin N,
          c i * c j *
            (fun v => (xiShiftedReciprocalMoment v
              ((i : ℕ) + (j : ℕ) + 1)).re)) =
          (fun v => ∑ i : Fin N, ∑ j : Fin N,
            c i v * c j v * s v ((i : ℕ) + (j : ℕ) + 1)) := by
      funext v
      simp only [s, Finset.sum_apply, Pi.mul_apply]
    rw [hfun] at hraw
    simpa only [s, md, move, fixed, Nat.cast_add, Nat.cast_one,
      Finset.sum_add_distrib, Pi.mul_apply] using hraw
  have htotal' : HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (X * finitePolynomialCurve c v))
      (move + fixed) y := by
    rw [show (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (X * finitePolynomialCurve c v)) =
      (fun v => ∑ i : Fin N, ∑ j : Fin N,
        c i v * c j v * s v ((i : ℕ) + (j : ℕ) + 1)) by
      funext v
      exact momentInner_finitePolynomialCurve_X_self (s v) c v]
    exact htotal
  have hfixedDirect : HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c y) (X * finitePolynomialCurve c y))
      fixed y := by
    rw [show (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c y) (X * finitePolynomialCurve c y)) =
      (fun v => ∑ i : Fin N, ∑ j : Fin N,
        c i y * c j y * s v ((i : ℕ) + (j : ℕ) + 1)) by
      funext v
      exact momentInner_finitePolynomialCurve_X_self (s v) c y]
    have hraw := HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
      (fun i _ => HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
        (fun j _ => (hasDerivAt_re_xiShiftedReciprocalMoment hy
          ((i : ℕ) + (j : ℕ) + 1)).const_mul (c i y * c j y)))
    have hfun :
        (∑ i : Fin N, ∑ j : Fin N,
          (fun v => c i y * c j y *
            (xiShiftedReciprocalMoment v ((i : ℕ) + (j : ℕ) + 1)).re)) =
          (fun v => ∑ i : Fin N, ∑ j : Fin N,
            c i y * c j y * s v ((i : ℕ) + (j : ℕ) + 1)) := by
      funext v
      simp only [s, Finset.sum_apply]
    rw [hfun] at hraw
    simpa only [s, md, fixed, Nat.cast_add, Nat.cast_one,
      Finset.sum_apply] using hraw
  have hfixedSource :=
    hasDerivAt_xiShiftedMomentInner_oddCrossing_eq_adaptiveShear hy
      (finitePolynomialCurve c y)
  have hfixed : fixed =
      -2 * HTGeometry.momentInner (s y)
        (X * finitePolynomialCurve c y)
        (X * xiShiftedBoundaryShiftedEuler 1 (finitePolynomialCurve c y)) :=
    hfixedDirect.unique hfixedSource
  have hmove : move =
      2 * HTGeometry.momentInner (s y)
        (finitePolynomialVelocity dc) (X * finitePolynomialCurve c y) := by
    have hcomm : HTGeometry.momentInner (s y)
        (finitePolynomialCurve c y) (X * finitePolynomialVelocity dc) =
      HTGeometry.momentInner (s y)
        (finitePolynomialVelocity dc) (X * finitePolynomialCurve c y) := by
      simp only [HTGeometry.momentInner_def]
      congr 1
      ring
    change (∑ i : Fin N, ∑ j : Fin N,
      (dc i * c j y + c i y * dc j) *
        s y ((i : ℕ) + (j : ℕ) + 1)) = _
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [← momentInner_finitePolynomialVelocity_X_curve (s y) dc c y]
    let d : Fin N → ℝ → ℝ := fun i _ => dc i
    have hsecond := momentInner_finitePolynomialCurve_X_curve (s y) c d y
    change HTGeometry.momentInner (s y) (finitePolynomialCurve c y)
      (X * finitePolynomialVelocity dc) = _ at hsecond
    rw [← hsecond, hcomm]
    ring
  rw [hmove, hfixed] at htotal'
  simpa only [s, add_comm] using htotal'

/-- At an admitted monic orthogonal flag, the full current derivative is positive-energy
dissipation plus exactly one subleading Gram--Schmidt connection coefficient. -/
theorem hasDerivAt_xiShiftedMovingAdmissionOddCurrent_eq_jacobiEnergy
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    (c : Fin (n + 1) → ℝ → ℝ) (dc : Fin (n + 1) → ℝ)
    (hc : ∀ i : Fin (n + 1), HasDerivAt (c i) (dc i) y)
    (hPy : finitePolynomialCurve c y =
      HTGeometry.monicOrtho (fun k => (xiShiftedReciprocalMoment y k).re) n)
    (hvelocity : (finitePolynomialVelocity dc).natDegree < n) :
    HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (X * finitePolynomialCurve c v))
      (-2 * HTGeometry.monicOrthoNormSq
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
          HTGeometry.adaptiveOrthoJacobiEnergy
            (fun k => (xiShiftedReciprocalMoment y k).re) n +
        2 * HTGeometry.monicOrthoNormSq
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
          (finitePolynomialVelocity dc).coeff (n - 1)) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hsource :=
    HTGeometry.momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy_below
      hbelow hn (le_refl (n + 2))
  have hsourceInner : HTGeometry.momentInner s
      (X * HTGeometry.monicOrtho s n)
      (X * xiShiftedBoundaryShiftedEuler 1 (HTGeometry.monicOrtho s n)) =
    HTGeometry.monicOrthoNormSq s n *
      HTGeometry.adaptiveOrthoJacobiEnergy s n := by
    rw [HTGeometry.momentInner_def]
    simpa only [xiShiftedBoundaryShiftedEuler, C_1, one_mul,
      HTGeometry.adaptiveOrthoSourcePolynomial] using hsource
  have hconnection :=
    momentInner_velocity_X_monicOrtho_eq_norm_mul_coeff_below
      hbelow hn (by omega) hvelocity
  have hmoving := hasDerivAt_xiShiftedMomentInner_movingOddCurrent hy c dc hc
  rw [hPy, hsourceInner, hconnection] at hmoving
  simpa only [s] using hmoving.congr_deriv (by ring)

/-- **Covariant Lyapunov law.** Subtracting the subleading admission connection from the actual
odd-current derivative leaves a strictly negative scalar.  Positivity of only `H_(n+2)` is used. -/
theorem xiShiftedMovingAdmissionOddCurrent_covariantDerivative_neg
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    (c : Fin (n + 1) → ℝ → ℝ) (dc : Fin (n + 1) → ℝ)
    (hc : ∀ i : Fin (n + 1), HasDerivAt (c i) (dc i) y)
    (hPy : finitePolynomialCurve c y =
      HTGeometry.monicOrtho (fun k => (xiShiftedReciprocalMoment y k).re) n)
    (hvelocity : (finitePolynomialVelocity dc).natDegree < n)
    {Bdot : ℝ}
    (hB : HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (X * finitePolynomialCurve c v)) Bdot y) :
    Bdot - 2 * HTGeometry.monicOrthoNormSq
        (fun k => (xiShiftedReciprocalMoment y k).re) n *
        (finitePolynomialVelocity dc).coeff (n - 1) < 0 := by
  have hcanonical :=
    hasDerivAt_xiShiftedMovingAdmissionOddCurrent_eq_jacobiEnergy
      hy hn hH c dc hc hPy hvelocity
  have hBdot := hB.unique hcanonical
  rw [hBdot]
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm := HTGeometry.monicOrthoNorm_pos_below hbelow (n := n) (by omega)
  have henergy := HTGeometry.adaptiveOrthoJacobiEnergy_pos_below
    hbelow hn (n := n) (le_refl (n + 2))
  nlinarith

end

end RHTower
