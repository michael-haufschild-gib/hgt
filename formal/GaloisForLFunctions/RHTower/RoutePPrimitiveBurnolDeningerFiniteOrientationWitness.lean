import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolDeningerFourLegCollapseRigidity

/-!
# Route P primitive Burnol / Deninger finite orientation witness

P-G203 shows that equality of the upper squared-Cauchy graph leg and P-G202's conjugate-lower
fourth leg is RH-equivalent.  This file preserves their difference instead of trying to collapse
it.  The difference is exactly anti-fixed by critical-line reflection, so its unconditional Weil
quadratic is the negative of its complete Hilbert norm square.

Both legs already have explicit source-only two-atom secant approximations.  Subtracting those
approximations gives finite mixed upper/conjugate-lower prime--Gamma source vectors converging
strongly to the reflection-odd graph channel.  Their Weil energies converge to its negative norm
square.  Consequently failure of RH produces an actually finite negative source packet, and is
equivalent to these explicit finite source energies having a strictly negative limit.

This replaces W-H184's unbounded target domination problem by a finite source sign problem.  It
does not assume source positivity, RH, zero location, simplicity, or a divisor-selected packet.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

theorem xiWeilLineConjLinearIsometry_twice
    (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    xiWeilLineConjLinearIsometry (xiWeilLineConjLinearIsometry v) = v := by
  apply Subtype.ext
  funext q
  simp [xiWeilLineConjLinearIsometry_apply, xiWeilLineConjLp_apply,
    DeningerMeyerGaussianGreen.xiZeroCopyLineConjEquiv_apply_apply]

/-- Reflection-odd graph channel exposed by keeping P-G202's upper and fourth legs distinct. -/
def routePDeningerFourLegOrientationDefectJet
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  (show lp (fun _ : XiZeroCopy => ℂ) 2 from
    routePDeningerUpperSquaredCauchyJet A w) -
  (show lp (fun _ : XiZeroCopy => ℂ) 2 from
    routePDeningerUpperFourLegHodgeMate A w)

@[simp] theorem routePDeningerFourLegOrientationDefectJet_apply
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (q : XiZeroCopy) :
    routePDeningerFourLegOrientationDefectJet A w q =
      -routePDeningerFourLegCollapseDefect A w q := by
  change
    routePDeningerUpperSquaredCauchyJet A w q -
        routePDeningerUpperFourLegHodgeMate A w q =
      -(routePDeningerUpperFourLegHodgeMate A w q -
        routePDeningerUpperSquaredCauchyJet A w q)
  ring

/-- The four-leg orientation defect is exactly anti-fixed by critical-line reindexing. -/
theorem xiWeilLineConj_fourLegOrientationDefectJet
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    xiWeilLineConjLinearIsometry
        (routePDeningerFourLegOrientationDefectJet A w) =
      -routePDeningerFourLegOrientationDefectJet A w := by
  let x : lp (fun _ : XiZeroCopy => ℂ) 2 :=
    routePDeningerUpperSquaredCauchyJet A w
  have hx : routePDeningerUpperSquaredCauchyJet A w = x := rfl
  have hmate : routePDeningerUpperFourLegHodgeMate A w =
      xiWeilLineConjLinearIsometry x := by
    simpa only [x, xiWeilLineConjLinearIsometry_apply] using
      routePDeningerUpperFourLegHodgeMate_eq_lineConj A w
  rw [routePDeningerFourLegOrientationDefectJet, hx, hmate,
    map_sub, xiWeilLineConjLinearIsometry_twice]
  abel

/-- The defect is a pure negative Krein/Weil channel: its quadratic energy is minus its complete
Hilbert norm square. -/
theorem xiWeilHilbertQuadratic_fourLegOrientationDefectJet
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    xiWeilHilbertQuadratic
        (routePDeningerFourLegOrientationDefectJet A w) =
      -‖routePDeningerFourLegOrientationDefectJet A w‖ ^ 2 := by
  rw [xiWeilHilbertQuadratic,
    xiWeilLineConj_fourLegOrientationDefectJet,
    inner_neg_left, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- For nonzero amplitude, disappearance of the reflection-odd graph channel is exactly RH. -/
theorem routePDeningerFourLegOrientationDefectJet_eq_zero_iff_riemannHypothesis
    {A : ℂ} (hA : A ≠ 0) (w : DeningerPrimeGammaUpperPoint) :
    routePDeningerFourLegOrientationDefectJet A w = 0 ↔
      RiemannHypothesis := by
  rw [routePDeningerFourLegOrientationDefectJet]
  constructor
  · intro hzero
    apply
      (routePDeningerUpperFourLegHodgeMate_eq_upperSquaredCauchyJet_iff_riemannHypothesis
        hA w).mp
    exact (sub_eq_zero.mp hzero).symm
  · intro hRH
    apply sub_eq_zero.mpr
    exact
      ((routePDeningerUpperFourLegHodgeMate_eq_upperSquaredCauchyJet_iff_riemannHypothesis
        hA w).mpr hRH).symm

/-- At one nonzero primitive graph amplitude, nonnegativity of the defect channel is already
equivalent to RH. -/
theorem xiWeilHilbertQuadratic_fourLegOrientationDefectJet_nonneg_iff_riemannHypothesis
    {A : ℂ} (hA : A ≠ 0) (w : DeningerPrimeGammaUpperPoint) :
    0 ≤ xiWeilHilbertQuadratic
        (routePDeningerFourLegOrientationDefectJet A w) ↔
      RiemannHypothesis := by
  rw [xiWeilHilbertQuadratic_fourLegOrientationDefectJet]
  constructor
  · intro h
    have hnorm : ‖routePDeningerFourLegOrientationDefectJet A w‖ = 0 := by
      nlinarith [norm_nonneg (routePDeningerFourLegOrientationDefectJet A w)]
    exact
      (routePDeningerFourLegOrientationDefectJet_eq_zero_iff_riemannHypothesis
        hA w).mp (norm_eq_zero.mp hnorm)
  · intro hRH
    have hzero :=
      (routePDeningerFourLegOrientationDefectJet_eq_zero_iff_riemannHypothesis
        hA w).mpr hRH
    rw [hzero, norm_zero]
    norm_num

/-- Off RH, the completed finite-source defect channel has strictly negative Weil energy. -/
theorem xiWeilHilbertQuadratic_fourLegOrientationDefectJet_neg_iff_not_riemannHypothesis
    {A : ℂ} (hA : A ≠ 0) (w : DeningerPrimeGammaUpperPoint) :
    xiWeilHilbertQuadratic
        (routePDeningerFourLegOrientationDefectJet A w) < 0 ↔
      ¬RiemannHypothesis := by
  rw [xiWeilHilbertQuadratic_fourLegOrientationDefectJet]
  constructor
  · intro hneg hRH
    have hzero :=
      (routePDeningerFourLegOrientationDefectJet_eq_zero_iff_riemannHypothesis
        hA w).mpr hRH
    rw [hzero, norm_zero] at hneg
    norm_num at hneg
  · intro hnot
    have hne : routePDeningerFourLegOrientationDefectJet A w ≠ 0 := by
      intro hzero
      exact hnot
        ((routePDeningerFourLegOrientationDefectJet_eq_zero_iff_riemannHypothesis
          hA w).mp hzero)
    have hnorm : 0 < ‖routePDeningerFourLegOrientationDefectJet A w‖ :=
      norm_pos_iff.mpr hne
    nlinarith

/-- Explicit finite mixed upper/conjugate-lower prime--Gamma secant realization of the
reflection-odd graph channel. -/
def routePDeningerFiniteFourLegOrientationDefectJet
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  (show lp (fun _ : XiZeroCopy => ℂ) 2 from
    deningerPrimeGammaUpperToJetHilbert
      (routePDeningerUpperSecantPacket A w n)) -
  (show lp (fun _ : XiZeroCopy => ℂ) 2 from
    star (deningerPrimeGammaLowerToJetHilbert
      (routePDeningerLowerSecantPacket ((starRingEnd ℂ) A)
        (deningerPrimeGammaPointConjEquiv.symm w) n)))

/-- The explicit finite mixed source secants converge strongly to the full reflection-odd graph
channel. -/
theorem tendsto_routePDeningerFiniteFourLegOrientationDefectJet
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    Tendsto
      (routePDeningerFiniteFourLegOrientationDefectJet A w)
      atTop
      (nhds (routePDeningerFourLegOrientationDefectJet A w)) := by
  exact
    (tendsto_routePDeningerUpperSecantPacket_to_squaredCauchyJet A w).sub
      (tendsto_routePDeningerConjugateLowerSecantPacket_to_fourLegHodgeMate A w)

/-- Their finite source Weil energies converge to the negative squared norm of the orientation
defect. -/
theorem tendsto_xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    Tendsto
      (fun n => xiWeilHilbertQuadratic
        (routePDeningerFiniteFourLegOrientationDefectJet A w n))
      atTop
      (nhds (-‖routePDeningerFourLegOrientationDefectJet A w‖ ^ 2)) := by
  have h := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp
    (tendsto_routePDeningerFiniteFourLegOrientationDefectJet A w)
  rwa [xiWeilHilbertQuadratic_fourLegOrientationDefectJet] at h

/-- Failure of RH forces an actually finite mixed prime--Gamma source witness with negative Weil
energy; no divisor-selected packet or closure premise is used. -/
theorem exists_finiteFourLegOrientationDefectJet_weil_negative_of_not_riemannHypothesis
    {A : ℂ} (hA : A ≠ 0) (w : DeningerPrimeGammaUpperPoint)
    (hnot : ¬RiemannHypothesis) :
    ∃ n : ℕ,
      xiWeilHilbertQuadratic
          (routePDeningerFiniteFourLegOrientationDefectJet A w n) < 0 := by
  have hlimit :=
    (xiWeilHilbertQuadratic_fourLegOrientationDefectJet_neg_iff_not_riemannHypothesis
      hA w).mpr hnot
  have htend := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp
    (tendsto_routePDeningerFiniteFourLegOrientationDefectJet A w)
  exact (htend.eventually_lt_const hlimit).exists

/-- Exact finite-source endpoint: failure of RH is equivalent to convergence of the explicit
mixed prime--Gamma secant energies to some strictly negative limit. -/
theorem exists_negative_limit_finiteFourLegOrientationDefectJet_iff_not_riemannHypothesis
    {A : ℂ} (hA : A ≠ 0) (w : DeningerPrimeGammaUpperPoint) :
    (∃ E : ℝ, E < 0 ∧
      Tendsto
        (fun n => xiWeilHilbertQuadratic
          (routePDeningerFiniteFourLegOrientationDefectJet A w n))
        atTop (nhds E)) ↔
      ¬RiemannHypothesis := by
  constructor
  · rintro ⟨E, hE, hEtend⟩
    have hcanonical :=
      tendsto_xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet A w
    have hEq : E = -‖routePDeningerFourLegOrientationDefectJet A w‖ ^ 2 :=
      tendsto_nhds_unique hEtend hcanonical
    apply
      (xiWeilHilbertQuadratic_fourLegOrientationDefectJet_neg_iff_not_riemannHypothesis
        hA w).mp
    rw [xiWeilHilbertQuadratic_fourLegOrientationDefectJet, ← hEq]
    exact hE
  · intro hnot
    refine ⟨-‖routePDeningerFourLegOrientationDefectJet A w‖ ^ 2, ?_, ?_⟩
    · rw [← xiWeilHilbertQuadratic_fourLegOrientationDefectJet]
      exact
        (xiWeilHilbertQuadratic_fourLegOrientationDefectJet_neg_iff_not_riemannHypothesis
          hA w).mpr hnot
    · exact tendsto_xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet A w

end

end RHTower
