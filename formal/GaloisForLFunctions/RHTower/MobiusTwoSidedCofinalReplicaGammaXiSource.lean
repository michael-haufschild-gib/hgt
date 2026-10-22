import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusTwoSidedApertureWall
import GaloisForLFunctions.RHTower.MobiusCofinalReplicaOneCorner

/-!
# Bilateral cofinal Möbius source through the completed Xi trace

The existing cofinal-replica transport was formulated only for inward `u ≥ 0`, although the
literal squarefree Möbius source remains an actual Hilbert vector for `u > -1/2`.  The apparent
one-sidedness came from an old collision wrapper which was defined as zero for `u < 0`.

This module keeps the collision as its literal absolutely summable source series.  It proves that
one and the same strict-lower replicated source, without divisor selection, has all three of:

* `ORIENT`: a genuine open two-sided source aperture `u > -1/2`;
* `COF`: cofinal evacuation of the atomic collision in the strict-lower replica corner;
* `LAND`: exact convergence through Gamma completion and the doubled prime correction to
  `continuedPrimeArchSourceRelativeTrace`.

No critical-boundary extension, Xi-divisor selection, or RH conclusion is asserted.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace RHTower

private theorem bilateral_damping_mul_probability_eq_boundaryLayerTerm
    {sigma u : ℝ} (n : ℕ) :
    mobiusCriticalDampingCoordinate sigma u n *
        squarefreeMobiusProbability sigma n =
      squarefreeMobiusBoundaryLayerTerm sigma u n := by
  by_cases hsq : Squarefree n
  · have hn0 : n ≠ 0 := fun hn => by subst n; exact not_squarefree_zero hsq
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    unfold mobiusCriticalDampingCoordinate squarefreeMobiusBoundaryLayerTerm
    calc
      Real.exp (-(u * (sigma - 1) * Real.log n)) *
          squarefreeMobiusProbability sigma n =
        squarefreeMobiusProbability sigma n *
          Real.exp (-(u * (sigma - 1) * Real.log n)) := by ring
      _ = squarefreeMobiusProbability sigma n *
          Real.exp (Real.log n * (-(u * (sigma - 1)))) := by
            congr 1
            ring
      _ = _ := by rw [Real.rpow_def_of_pos hnpos]
  · simp [mobiusCriticalDampingCoordinate, squarefreeMobiusBoundaryLayerTerm,
      squarefreeMobiusProbability, squarefreeMobiusMass, hsq]

private theorem bilateral_summable_probability_mul_damping
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    Summable (fun n : ℕ =>
      squarefreeMobiusProbability sigma n *
        mobiusCriticalDampingCoordinate sigma u n) := by
  have hshift : 1 < mobiusCriticalBoundaryParameter sigma u := by
    rw [mobiusCriticalBoundaryParameter]
    nlinarith
  have hsum := (summable_squarefreeMobiusMass hshift).div_const
    (squarefreeMobiusTotal sigma)
  apply hsum.congr
  intro n
  rw [← squarefreeMobiusBoundaryLayerTerm_eq,
    ← bilateral_damping_mul_probability_eq_boundaryLayerTerm]
  ring

private theorem bilateral_summable_mass_mul_centeredLog
    {tau sigma : ℝ} (htau : 1 < tau) :
    Summable (fun n : ℕ => squarefreeMobiusMass tau n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma)) := by
  have hlog := summable_squarefreeMobiusLogMoment 1 htau
  have hmass := summable_squarefreeMobiusMass htau
  have hraw : Summable (fun n : ℕ =>
      squarefreeMobiusMass tau n * Real.log n) := by
    have hz := (squarefreeMobiusTotal_pos htau).ne'
    have hscaled := hlog.mul_left (squarefreeMobiusTotal tau)
    convert hscaled using 1
    all_goals try rfl
    funext n
    rw [squarefreeMobiusProbability]
    field_simp [hz]
  apply (hraw.sub (hmass.mul_left _)).congr
  intro n
  ring

private theorem bilateral_tsum_mass_mul_centeredLog
    {tau sigma : ℝ} (htau : 1 < tau) :
    (∑' n : ℕ, squarefreeMobiusMass tau n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma)) =
      squarefreeMobiusTotal tau *
        (squarefreeMobiusLogMoment 1 tau -
          squarefreeMobiusLogMoment 1 sigma) := by
  have hlog := summable_squarefreeMobiusLogMoment 1 htau
  have hmass := summable_squarefreeMobiusMass htau
  have hraw : Summable (fun n : ℕ =>
      squarefreeMobiusMass tau n * Real.log n) := by
    have hz := (squarefreeMobiusTotal_pos htau).ne'
    have hscaled := hlog.mul_left (squarefreeMobiusTotal tau)
    convert hscaled using 1
    all_goals try rfl
    funext n
    rw [squarefreeMobiusProbability]
    field_simp [hz]
  rw [show (fun n : ℕ => squarefreeMobiusMass tau n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma)) =
      fun n => squarefreeMobiusMass tau n * Real.log n -
        squarefreeMobiusLogMoment 1 sigma * squarefreeMobiusMass tau n by
    funext n
    ring]
  rw [Summable.tsum_sub hraw (hmass.mul_left _), tsum_mul_left]
  have hmoment :
      (∑' n : ℕ, squarefreeMobiusMass tau n * Real.log n) =
        squarefreeMobiusTotal tau * squarefreeMobiusLogMoment 1 tau := by
    have hz := (squarefreeMobiusTotal_pos htau).ne'
    rw [squarefreeMobiusLogMoment]
    rw [show (fun n : ℕ =>
        squarefreeMobiusProbability tau n * Real.log n ^ 1) =
        fun n => squarefreeMobiusMass tau n * Real.log n /
          squarefreeMobiusTotal tau by
      funext n
      rw [squarefreeMobiusProbability]
      simp only [pow_one]
      ring]
    rw [tsum_div_const]
    field_simp [hz]
  rw [hmoment, show (∑' n : ℕ, squarefreeMobiusMass tau n) =
    squarefreeMobiusTotal tau by rfl]
  ring

private theorem bilateral_probability_fisher_damping_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    squarefreeMobiusProbability sigma n *
        mobiusCriticalFisherCoordinate sigma n *
          mobiusCriticalDampingCoordinate sigma u n =
      (-2 * (sigma - 1) / squarefreeMobiusTotal sigma) *
        (squarefreeMobiusMass (mobiusCriticalBoundaryParameter sigma u) n *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma)) := by
  have hz := (squarefreeMobiusTotal_pos hsigma).ne'
  rw [mobiusCriticalFisherCoordinate]
  calc
    squarefreeMobiusProbability sigma n *
        (-2 * (sigma - 1) *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma)) *
          mobiusCriticalDampingCoordinate sigma u n =
      (-2 * (sigma - 1) *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma)) *
        (mobiusCriticalDampingCoordinate sigma u n *
          squarefreeMobiusProbability sigma n) := by ring
    _ = (-2 * (sigma - 1) *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma)) *
        squarefreeMobiusBoundaryLayerTerm sigma u n := by
      rw [bilateral_damping_mul_probability_eq_boundaryLayerTerm]
    _ = _ := by
      rw [squarefreeMobiusBoundaryLayerTerm_eq]
      field_simp [hz]

private theorem bilateral_summable_probability_mul_fisher_damping
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    Summable (fun n : ℕ =>
      squarefreeMobiusProbability sigma n *
        mobiusCriticalFisherCoordinate sigma n *
          mobiusCriticalDampingCoordinate sigma u n) := by
  have hshift : 1 < mobiusCriticalBoundaryParameter sigma u := by
    rw [mobiusCriticalBoundaryParameter]
    nlinarith
  let c : ℝ := -2 * (sigma - 1) / squarefreeMobiusTotal sigma
  have hsum := bilateral_summable_mass_mul_centeredLog
    (tau := mobiusCriticalBoundaryParameter sigma u) (sigma := sigma) hshift
  refine (hsum.mul_left c).congr ?_
  intro n
  exact (bilateral_probability_fisher_damping_eq hsigma n).symm

private theorem bilateral_tsum_probability_mul_fisher_damping
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    (∑' n : ℕ, squarefreeMobiusProbability sigma n *
      mobiusCriticalFisherCoordinate sigma n *
        mobiusCriticalDampingCoordinate sigma u n) =
      (-2 * (sigma - 1) / squarefreeMobiusTotal sigma) *
        (squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma u) *
          (squarefreeMobiusLogMoment 1 (mobiusCriticalBoundaryParameter sigma u) -
            squarefreeMobiusLogMoment 1 sigma)) := by
  have hshift : 1 < mobiusCriticalBoundaryParameter sigma u := by
    rw [mobiusCriticalBoundaryParameter]
    nlinarith
  rw [show (fun n : ℕ =>
      squarefreeMobiusProbability sigma n *
        mobiusCriticalFisherCoordinate sigma n *
          mobiusCriticalDampingCoordinate sigma u n) =
      fun n => (-2 * (sigma - 1) / squarefreeMobiusTotal sigma) *
        (squarefreeMobiusMass (mobiusCriticalBoundaryParameter sigma u) n *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma)) by
    funext n
    exact bilateral_probability_fisher_damping_eq hsigma n]
  rw [tsum_mul_left, bilateral_tsum_mass_mul_centeredLog hshift]

private theorem bilateral_ofReal_tsum_probability_mul_fisher_damping_eq_score
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    (((∑' n : ℕ, squarefreeMobiusProbability sigma n *
      mobiusCriticalFisherCoordinate sigma n *
        mobiusCriticalDampingCoordinate sigma u n : ℝ) : ℂ)) =
      GaloisForLFunctions.squarefreeFisherScore
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) := by
  have hshift : 1 < mobiusCriticalBoundaryParameter sigma u := by
    rw [mobiusCriticalBoundaryParameter]
    nlinarith
  have hsigmaC : 1 < (sigma : ℂ).re := by simpa using hsigma
  have hshiftC :
      1 < ((sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ)).re := by
    have hcoord :
        ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
          (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
      exact_mod_cast (show mobiusCriticalBoundaryParameter sigma u =
        sigma + u * (sigma - 1) by rfl)
    rw [← hcoord]
    simpa using hshift
  have hcoord :
      ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
    exact_mod_cast (show mobiusCriticalBoundaryParameter sigma u =
      sigma + u * (sigma - 1) by rfl)
  have hpartSigma : (squarefreeMobiusTotal sigma : ℂ) =
      GaloisForLFunctions.squarefreePartition (sigma : ℂ) := by
    rw [ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma]
    rfl
  have hpartShift :
      (squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma u) : ℂ) =
        GaloisForLFunctions.squarefreePartition
          (mobiusCriticalBoundaryParameter sigma u : ℂ) := by
    rw [ofReal_squarefreeMobiusTotal_eq_zetaRatio hshift]
    rfl
  have hoverlap :
      GaloisForLFunctions.squarefreeBoundaryOverlap
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) =
        (squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma u) : ℂ) /
          (squarefreeMobiusTotal sigma : ℂ) := by
    rw [GaloisForLFunctions.squarefreeBoundaryOverlap, ← hcoord,
      ← hpartShift, ← hpartSigma]
  rw [bilateral_tsum_probability_mul_fisher_damping hsigma hu,
    GaloisForLFunctions.squarefreeFisherScore_eq_fixedCurrent_difference
      hsigmaC hshiftC,
    hoverlap,
    ← hcoord,
    ← ofReal_squarefreeMobiusLogMoment_one_eq_fixedCurrent hsigma,
    ← ofReal_squarefreeMobiusLogMoment_one_eq_fixedCurrent hshift]
  push_cast
  have htotal := (squarefreeMobiusTotal_pos hsigma).ne'
  field_simp [htotal]
  ring

private theorem bilateral_mass_sq_mul_damping
    {sigma u : ℝ} (n : ℕ) :
    squarefreeMobiusMass sigma n ^ 2 *
        mobiusCriticalDampingCoordinate sigma u n =
      squarefreeMobiusMass (mobiusDiffuseCollisionParameter sigma u) n := by
  rw [squarefreeMobiusMass, squarefreeMobiusMass]
  split_ifs with hn
  · have hn0 : n ≠ 0 := by
      intro h
      subst n
      exact not_squarefree_zero hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn0
    have hdamp :
        Real.exp (-(u * (sigma - 1) * Real.log n)) =
          (n : ℝ) ^ (-(u * (sigma - 1))) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    rw [mobiusCriticalDampingCoordinate, hdamp,
      ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le,
      ← Real.rpow_add hnpos]
    congr 1
    dsimp [mobiusDiffuseCollisionParameter]
    ring
  · simp

private theorem bilateral_collision_parameter_gt_one
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    1 < mobiusDiffuseCollisionParameter sigma u := by
  dsimp [mobiusDiffuseCollisionParameter]
  nlinarith

private theorem bilateral_collision_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    squarefreeMobiusProbability sigma n ^ 2 *
        mobiusCriticalFisherCoordinate sigma n *
          mobiusCriticalDampingCoordinate sigma u n =
      (-2 * (sigma - 1) / squarefreeMobiusTotal sigma ^ 2) *
        (squarefreeMobiusMass (mobiusDiffuseCollisionParameter sigma u) n *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma)) := by
  have hz := (squarefreeMobiusTotal_pos hsigma).ne'
  rw [squarefreeMobiusProbability, mobiusCriticalFisherCoordinate]
  calc
    (squarefreeMobiusMass sigma n / squarefreeMobiusTotal sigma) ^ 2 *
        (-2 * (sigma - 1) *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma)) *
          mobiusCriticalDampingCoordinate sigma u n =
      (-2 * (sigma - 1) / squarefreeMobiusTotal sigma ^ 2) *
        (squarefreeMobiusMass sigma n ^ 2 *
          mobiusCriticalDampingCoordinate sigma u n) *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma) := by
        field_simp [hz]
    _ = _ := by
      rw [bilateral_mass_sq_mul_damping]
      ring

private theorem bilateral_summable_collision
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    Summable (fun n : ℕ =>
      squarefreeMobiusProbability sigma n ^ 2 *
        mobiusCriticalFisherCoordinate sigma n *
          mobiusCriticalDampingCoordinate sigma u n) := by
  have htau := bilateral_collision_parameter_gt_one hsigma hu
  let c : ℝ := -2 * (sigma - 1) / squarefreeMobiusTotal sigma ^ 2
  have hsum := bilateral_summable_mass_mul_centeredLog
    (tau := mobiusDiffuseCollisionParameter sigma u) (sigma := sigma) htau
  refine (hsum.mul_left c).congr ?_
  intro n
  exact (bilateral_collision_eq hsigma n).symm

/-- Literal strict-lower replica cofinality on the entire two-sided source aperture. -/
theorem bilateral_tendsto_ofReal_mobiusCofinalReplicaFisherOneCornerCodiagonal
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    Tendsto
      (fun k : ℕ =>
        (mobiusCofinalReplicaFisherOneCornerCodiagonal
          (k + 1) sigma u : ℂ))
      atTop
      (𝓝 (GaloisForLFunctions.squarefreeFisherScore
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ))) := by
  have hreal := tendsto_cofinalReplicaFisherOneCornerCodiagonal
    (summable_squarefreeMobiusProbability hsigma)
    (summable_mobius_probability_mul_fisherCoordinate hsigma)
    (bilateral_summable_probability_mul_damping hsigma hu)
    (bilateral_summable_probability_mul_fisher_damping hsigma hu)
    (bilateral_summable_collision hsigma hu)
    (tsum_squarefreeMobiusProbability hsigma)
    (tsum_mobius_probability_mul_fisherCoordinate_zero hsigma)
  have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  rw [bilateral_ofReal_tsum_probability_mul_fisher_damping_eq_score hsigma hu] at hcast
  exact hcast.congr' (Filter.Eventually.of_forall (fun k => rfl))

private theorem bilateral_boundaryLayerLaplace_eq_squarefreeBoundaryOverlap
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    squarefreeMobiusBoundaryLayerLaplace sigma u =
      GaloisForLFunctions.squarefreeBoundaryOverlap
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) := by
  have hshift : 1 < mobiusCriticalBoundaryParameter sigma u := by
    rw [mobiusCriticalBoundaryParameter]
    nlinarith
  have hcoord :
      ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
    exact_mod_cast (show mobiusCriticalBoundaryParameter sigma u =
      sigma + u * (sigma - 1) by rfl)
  have hpartSigma : (squarefreeMobiusTotal sigma : ℂ) =
      GaloisForLFunctions.squarefreePartition (sigma : ℂ) := by
    rw [ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma]
    rfl
  have hpartShift :
      (squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma u) : ℂ) =
        GaloisForLFunctions.squarefreePartition
          (mobiusCriticalBoundaryParameter sigma u : ℂ) := by
    rw [ofReal_squarefreeMobiusTotal_eq_zetaRatio hshift]
    rfl
  rw [squarefreeMobiusBoundaryLayerLaplace,
    GaloisForLFunctions.squarefreeBoundaryOverlap, ← hcoord,
    ← hpartShift, ← hpartSigma]

/-- The same bilateral strict-lower source remains faithful through Gamma completion. -/
theorem bilateral_tendsto_squarefreeMobiusCofinalReplicaGammaCurrentTransportV
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    Tendsto
      (fun k : ℕ =>
        squarefreeMobiusCofinalReplicaGammaCurrentTransportV
          (k + 1) sigma u)
      atTop
      (𝓝 (GaloisForLFunctions.completedSquarefreeFixedCurrent
        (mobiusCriticalBoundaryParameter sigma u : ℂ))) := by
  have hscore :=
    bilateral_tendsto_ofReal_mobiusCofinalReplicaFisherOneCornerCodiagonal
      hsigma hu
  have htransport : Tendsto
      (fun k : ℕ =>
        2 * GaloisForLFunctions.squarefreeFixedCurrent sigma -
          (mobiusCofinalReplicaFisherOneCornerCodiagonal
            (k + 1) sigma u : ℂ) /
            (((sigma - 1 : ℝ) : ℂ) *
              squarefreeMobiusBoundaryLayerLaplace sigma u) -
          2 * logDeriv archFactor
            (mobiusCriticalBoundaryParameter sigma u))
      atTop
      (𝓝 (2 * GaloisForLFunctions.squarefreeFixedCurrent sigma -
        GaloisForLFunctions.squarefreeFisherScore
            (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) /
          (((sigma - 1 : ℝ) : ℂ) *
            squarefreeMobiusBoundaryLayerLaplace sigma u) -
        2 * logDeriv archFactor
          (mobiusCriticalBoundaryParameter sigma u))) := by
    exact
      (tendsto_const_nhds.sub
        (hscore.div_const
          (((sigma - 1 : ℝ) : ℂ) *
            squarefreeMobiusBoundaryLayerLaplace sigma u))).sub
        tendsto_const_nhds
  have hsigmaC : 1 < (sigma : ℂ).re := by simpa using hsigma
  have hshift : 1 < mobiusCriticalBoundaryParameter sigma u := by
    rw [mobiusCriticalBoundaryParameter]
    nlinarith
  have hshiftC :
      1 < ((sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ)).re := by
    have hcoord :
        ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
          (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
      exact_mod_cast (show mobiusCriticalBoundaryParameter sigma u =
        sigma + u * (sigma - 1) by rfl)
    rw [← hcoord]
    simpa using hshift
  have hepsilon : ((sigma - 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hsigma.ne'
  have hfull := squarefreeMobiusGammaCurrentTransportV_eq_completedCurrent
    hsigmaC hshiftC hepsilon
  have hoverlap := bilateral_boundaryLayerLaplace_eq_squarefreeBoundaryOverlap
    hsigma hu
  have hcoord :
      ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
    exact_mod_cast (show mobiusCriticalBoundaryParameter sigma u =
      sigma + u * (sigma - 1) by rfl)
  rw [hcoord, ← hfull]
  simpa only [squarefreeMobiusCofinalReplicaGammaCurrentTransportV,
    squarefreeMobiusGammaCurrentTransportV, hcoord, hoverlap] using htransport

/-- **Source `ORIENT+COF+LAND`.** A literal bilateral strict-lower source reaches the
completed prime--Gamma trace without a zero/divisor selection. -/
theorem bilateral_tendsto_squarefreeMobiusCofinalReplicaGammaXiWardTransportV
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    Tendsto
      (fun k : ℕ =>
        squarefreeMobiusCofinalReplicaGammaXiWardTransportV
          (k + 1) sigma u)
      atTop
      (𝓝 (continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate
          (mobiusCriticalBoundaryParameter sigma u : ℂ)))) := by
  have hcurrent :=
    bilateral_tendsto_squarefreeMobiusCofinalReplicaGammaCurrentTransportV
      hsigma hu
  let correction : ℂ :=
    4 * infinitePrimeFlux
      (2 * (mobiusCriticalBoundaryParameter sigma u : ℂ))
  have h : Tendsto
      (fun k : ℕ =>
        (-I / 2) *
          (squarefreeMobiusCofinalReplicaGammaCurrentTransportV
            (k + 1) sigma u + correction))
      atTop
      (𝓝 ((-I / 2) *
        (GaloisForLFunctions.completedSquarefreeFixedCurrent
            (mobiusCriticalBoundaryParameter sigma u : ℂ) +
          correction))) :=
    (hcurrent.add tendsto_const_nhds).const_mul (-I / 2)
  have hsource :=
    continuedPrimeArchSourceRelativeTrace_eq_completedSquarefree_add_correction
      (xiWardCenteredCoordinate
        (mobiusCriticalBoundaryParameter sigma u : ℂ))
  rw [xiWardCenteredCoordinate_source] at hsource
  simpa only [squarefreeMobiusCofinalReplicaGammaXiWardTransportV,
    correction, hsource] using h

/-- The single bilateral source law records both orientations explicitly. -/
theorem bilateral_cofinalReplicaGammaXiWard_sourceProducer
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∀ u : ℝ, -(1 / 2 : ℝ) < u →
      Tendsto
        (fun k : ℕ =>
          squarefreeMobiusCofinalReplicaGammaXiWardTransportV
            (k + 1) sigma u)
        atTop
        (𝓝 (continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            (mobiusCriticalBoundaryParameter sigma u : ℂ))))) ∧
    (∀ u : ℝ, 0 < u → u < 1 / 2 →
      Tendsto
        (fun k : ℕ =>
          squarefreeMobiusCofinalReplicaGammaXiWardTransportV
            (k + 1) sigma u)
        atTop
        (𝓝 (continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            (mobiusCriticalBoundaryParameter sigma u : ℂ)))) ∧
      Tendsto
        (fun k : ℕ =>
          squarefreeMobiusCofinalReplicaGammaXiWardTransportV
            (k + 1) sigma (-u))
        atTop
        (𝓝 (continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            (mobiusCriticalBoundaryParameter sigma (-u) : ℂ))))) := by
  constructor
  · intro u hu
    exact bilateral_tendsto_squarefreeMobiusCofinalReplicaGammaXiWardTransportV
      hsigma hu
  · intro u hu0 huHalf
    refine ⟨bilateral_tendsto_squarefreeMobiusCofinalReplicaGammaXiWardTransportV
      hsigma (by linarith), ?_⟩
    exact bilateral_tendsto_squarefreeMobiusCofinalReplicaGammaXiWardTransportV
      hsigma (by linarith)

end RHTower
