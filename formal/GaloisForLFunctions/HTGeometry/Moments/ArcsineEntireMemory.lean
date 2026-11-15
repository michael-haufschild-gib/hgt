import GaloisForLFunctions.HTGeometry.Moments.AnalyticLeadingMinors
import GaloisForLFunctions.HTGeometry.Moments.FiniteStateLeadingMinors
import GaloisForLFunctions.HTGeometry.ArcsineHankelPositiveDefinite
import GaloisForLFunctions.HTGeometry.PRecursiveDFinite

/-!
# An entire arcsine response with infinite constant-coefficient memory

The normalized central-binomial moments are bounded by one, so their exponential
generating series is entire and recovers every moment as a derivative at zero.
Strict positivity of the native arcsine Hankel tower then excludes every finite
state-space realization and every nonzero local constant-coefficient ODE.

The positive replacement is explicit: the moment recurrence gives the global
second-order equation `z f'' + (1 - z) f' - (1/2) f = 0`. Thus bounded derivative
jets and a polynomial-coefficient differential equation coexist with infinite
constant-coefficient differential order. The leading-minor criterion supplies
the exact obstruction, without an additional analytic or convergence premise.
-/

open Filter Topology
open _root_.HTGeometry.FiniteHankel

namespace GaloisForLFunctions.HTGeometry

private theorem arcsineMoment_norm_le_one (n : ℕ) :
    ‖(normalizedCentralBinom n : ℂ)‖ ≤ 1 := by
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (normalizedCentralBinom_nonneg n)]
  apply (div_le_one (by positivity : (0 : ℝ) < 4 ^ n)).mpr
  exact_mod_cast Nat.centralBinom_le_four_pow n

private theorem arcsineMoment_jetRecurrence (n : ℕ) :
    ((n : ℂ) + 1) * (normalizedCentralBinom (n + 1) : ℂ) =
      ((n : ℂ) + 1 / 2) * (normalizedCentralBinom n : ℂ) := by
  have hr : ((n : ℝ) + 1) * normalizedCentralBinom (n + 1) =
      ((n : ℝ) + 1 / 2) * normalizedCentralBinom n := by
    rw [normalizedCentralBinom_succ]
    have hn : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hn]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  push_cast at hc
  exact hc

/-- Entire function whose derivative sequence at zero is the native arcsine moment sequence. -/
noncomputable def arcsineEntireResponse : ℂ → ℂ :=
  responseTaylorFun (fun n => (normalizedCentralBinom n : ℂ))

private theorem arcsineResponse_radius :
    (FormalMultilinearSeries.ofScalars ℂ
      (responseTaylorCoeff (fun n => (normalizedCentralBinom n : ℂ)))).radius = ⊤ := by
  apply radius_ofScalars_taylorCoeff_eq_top (C := 1) (R := 1) zero_le_one le_rfl
  intro n
  simpa only [one_pow, one_mul] using arcsineMoment_norm_le_one n

/-- The canonical exponential generating series of arcsine moments is entire. -/
theorem arcsineEntireResponse_entire (z : ℂ) : AnalyticAt ℂ arcsineEntireResponse z := by
  exact (hasFPowerSeriesOnBall_taylorFun arcsineResponse_radius).analyticOnNhd z (by
    rw [Metric.mem_eball]
    exact edist_lt_top _ _)

/-- Every derivative at zero is the corresponding normalized central-binomial moment. -/
theorem arcsineEntireResponse_jet (n : ℕ) :
    iteratedDeriv n arcsineEntireResponse 0 = (normalizedCentralBinom n : ℂ) :=
  iteratedDeriv_taylorFun arcsineResponse_radius n

/-- All raw derivative jets at zero have norm at most one. -/
theorem arcsineEntireResponse_jet_bound (n : ℕ) :
    ‖iteratedDeriv n arcsineEntireResponse 0‖ ≤ 1 := by
  rw [arcsineEntireResponse_jet]
  exact arcsineMoment_norm_le_one n

/-- Every leading derivative Hankel block is nonsingular, including the empty block. -/
theorem arcsineEntireResponse_leadingDet_ne_zero (n : ℕ) :
    leadingDet (respSeq arcsineEntireResponse) n ≠ 0 := by
  have hj : respSeq arcsineEntireResponse = fun k => (normalizedCentralBinom k : ℂ) :=
    funext arcsineEntireResponse_jet
  rw [hj]
  have hmap : leadingDet (fun k => (normalizedCentralBinom k : ℂ)) n =
      ((_root_.HTGeometry.momentHankelMatrix normalizedCentralBinom n).det : ℂ) :=
    (RingHom.map_det Complex.ofRealHom
      (_root_.HTGeometry.momentHankelMatrix normalizedCentralBinom n)).symm
  rw [hmap]
  exact_mod_cast (normalizedCentralBinom_momentHankelMatrix_det_pos n).ne'

/-- No finite-dimensional complex state space realizes the derivative sequence. -/
theorem arcsineEntireResponse_no_finiteState (d : ℕ) :
    ¬ _root_.HTGeometry.AlgebraicStateSpaceDimensionAtMost d (respSeq arcsineEntireResponse) := by
  intro h
  exact arcsineEntireResponse_leadingDet_ne_zero (d + 1)
    (leading_tail_zero_of_stateSpace h _ (Nat.lt_succ_self _))

/-- Every nonzero constant-coefficient differential operator fails even near zero. -/
theorem arcsineEntireResponse_no_local_constantODE (p : Polynomial ℂ) (hp : p ≠ 0) :
    ¬ (∀ᶠ z in 𝓝 (0 : ℂ), odeSum p.coeff p.natDegree arcsineEntireResponse z = 0) := by
  intro hode
  have ht := (leading_tail_zero_respSeq_iff_localODE (arcsineEntireResponse_entire 0)
    p.natDegree).mpr ⟨p, hp, le_rfl, hode⟩
  exact arcsineEntireResponse_leadingDet_ne_zero (p.natDegree + 1)
    (ht _ (Nat.lt_succ_self _))

/-- The only constant-coefficient operator annihilating the analytic germ is the zero operator. -/
theorem arcsineEntireResponse_localODE_iff (p : Polynomial ℂ) :
    (∀ᶠ z in 𝓝 (0 : ℂ), odeSum p.coeff p.natDegree arcsineEntireResponse z = 0) ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp
    exact arcsineEntireResponse_no_local_constantODE p hp h
  · rintro rfl
    exact Filter.Eventually.of_forall fun z => by simp [odeSum]

/-- The analytic germ cannot be an exponential polynomial. -/
theorem arcsineEntireResponse_not_germExpPoly : ¬ GermExpPoly arcsineEntireResponse := by
  intro h
  obtain ⟨_, B, ht⟩ := (germExpPoly_iff_analytic_leading_tail _).mp h
  exact arcsineEntireResponse_leadingDet_ne_zero (B + 1) (ht _ (Nat.lt_succ_self _))

/-- The entire arcsine response is not an exponential polynomial. -/
theorem arcsineEntireResponse_not_expPoly : arcsineEntireResponse ∉ expPolySpaceC := by
  intro h
  obtain ⟨_, B, ht⟩ := (mem_expPolySpaceC_iff_entire_leading_tail _).mp h
  exact arcsineEntireResponse_leadingDet_ne_zero (B + 1) (ht _ (Nat.lt_succ_self _))

/-- The arcsine recurrence gives a global second-order polynomial-coefficient ODE. -/
theorem arcsineEntireResponse_variableODE (z : ℂ) :
    z * deriv (deriv arcsineEntireResponse) z +
      (1 - z) * deriv arcsineEntireResponse z - (1 / 2 : ℂ) * arcsineEntireResponse z = 0 := by
  let f := arcsineEntireResponse
  have hf : Differentiable ℂ f := fun w => (arcsineEntireResponse_entire w).differentiableAt
  have hd : Differentiable ℂ (deriv f) := hf.deriv
  have hdd : Differentiable ℂ (deriv (deriv f)) := hd.deriv
  let a := fun w : ℂ => w * deriv (deriv f) w
  let b := fun w : ℂ => w * deriv f w
  let c := fun w : ℂ => (1 / 2 : ℂ) * f w
  have ha : Differentiable ℂ a := differentiable_id.mul hdd
  have hb : Differentiable ℂ b := differentiable_id.mul hd
  have hc : Differentiable ℂ c := hf.const_mul _
  have hres : Differentiable ℂ (a + deriv f - b - c) := ((ha.add hd).sub hb).sub hc
  -- Leibniz reduces each residual jet to the scalar moment recurrence.
  have hzero : ∀ n, iteratedDeriv n (a + deriv f - b - c) 0 = 0 := by
    intro n
    rw [iteratedDeriv_sub (contDiffAt_of_differentiable ((ha.add hd).sub hb) n 0)
        (contDiffAt_of_differentiable hc n 0),
      iteratedDeriv_sub (contDiffAt_of_differentiable (ha.add hd) n 0)
        (contDiffAt_of_differentiable hb n 0),
      iteratedDeriv_add (contDiffAt_of_differentiable ha n 0)
        (contDiffAt_of_differentiable hd n 0)]
    dsimp only [a, b, c]
    rw [iteratedDeriv_const_mul _ (contDiffAt_of_differentiable hf n 0)]
    cases n with
    | zero =>
      simp only [iteratedDeriv_zero, zero_mul, zero_add, sub_zero]
      change deriv arcsineEntireResponse 0 - (1 / 2 : ℂ) * arcsineEntireResponse 0 = 0
      rw [← iteratedDeriv_one, arcsineEntireResponse_jet]
      have hj0 : arcsineEntireResponse 0 = (normalizedCentralBinom 0 : ℂ) :=
        arcsineEntireResponse_jet 0
      rw [hj0]
      have hr := arcsineMoment_jetRecurrence 0
      norm_num only [Nat.cast_zero, zero_add, one_mul] at hr
      exact sub_eq_zero.mpr hr
    | succ n =>
      rw [iteratedDeriv_id_mul_zero hdd n, iteratedDeriv_id_mul_zero hd n]
      simp only [← iteratedDeriv_succ']
      change ((n : ℂ) + 1) * iteratedDeriv (n + 1 + 1) arcsineEntireResponse 0 +
          iteratedDeriv (n + 1 + 1) arcsineEntireResponse 0 -
          ((n : ℂ) + 1) * iteratedDeriv (n + 1) arcsineEntireResponse 0 -
          (1 / 2 : ℂ) * iteratedDeriv (n + 1) arcsineEntireResponse 0 = 0
      simp only [arcsineEntireResponse_jet]
      have hr := arcsineMoment_jetRecurrence (n + 1)
      push_cast at hr
      linear_combination hr
  have hz := entire_eq_zero_of_iteratedDeriv_zero hres hzero z
  change z * deriv (deriv arcsineEntireResponse) z + deriv arcsineEntireResponse z -
    z * deriv arcsineEntireResponse z - (1 / 2 : ℂ) * arcsineEntireResponse z = 0 at hz
  linear_combination hz

#print axioms arcsineEntireResponse_leadingDet_ne_zero
#print axioms arcsineEntireResponse_no_finiteState
#print axioms arcsineEntireResponse_localODE_iff
#print axioms arcsineEntireResponse_variableODE

end GaloisForLFunctions.HTGeometry
