import GaloisForLFunctions.RHTower.SoninCofinalMobiusGammaXiIncidence
import GaloisForLFunctions.RHTower.MobiusCoMovingDiffuseCodiagonal
import GaloisForLFunctions.RHTower.MobiusCofinalReplicaOneCorner

/-!
# Fixed-Euler diagonal anomaly in the Möbius one-corner transport

The strict lower one-corner collision is negligible when the damping speed is
fixed.  The CCM fixed-Euler path is different: its damping speed diverges as
the normal coordinate collapses.  On that double-singular path the collision
survives at exactly the Gamma graph scale.

This file computes the surviving term unconditionally.  It is the correction
that any physical one-corner realization of the fixed-Euler CCM transport must
carry.
-/

open Complex Filter Set Topology

noncomputable section

namespace RHTower

/-- Exact real diagonal anomaly left by the Möbius collision on the fixed-Euler path. -/
def fixedEulerMobiusCollisionAnomaly (s : ℝ) : ℝ :=
  2 * (riemannZeta (2 : ℂ)).re *
    squarefreeMobiusTotal (s + 1) / squarefreeMobiusTotal s

/-- The fixed-Euler collision anomaly is strictly positive throughout the
Euler half-line. -/
theorem fixedEulerMobiusCollisionAnomaly_pos
    {s : ℝ} (hs : 1 < s) :
    0 < fixedEulerMobiusCollisionAnomaly s := by
  have hzetaTwo : 0 < (riemannZeta (2 : ℂ)).re := by
    rw [riemannZeta_two]
    norm_num [Complex.div_re, Complex.normSq, pow_two, Complex.mul_re]
  rw [fixedEulerMobiusCollisionAnomaly]
  exact div_pos
    (mul_pos
      (mul_pos (by norm_num) hzetaTwo)
      (squarefreeMobiusTotal_pos (by linarith : 1 < s + 1)))
    (squarefreeMobiusTotal_pos hs)

/-- The squared-probability Euler parameter on the fixed-Euler path is
`fixedEulerCofinalSigma s n + s`. -/
theorem mobiusDiffuseCollisionParameter_fixedEuler
    (s : ℝ) (n : ℕ) :
    mobiusDiffuseCollisionParameter
        (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n) =
      fixedEulerCofinalSigma s n + s := by
  rw [show mobiusDiffuseCollisionParameter
      (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n) =
        fixedEulerCofinalSigma s n +
          mobiusCriticalBoundaryParameter
            (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n) by
    simp only [mobiusDiffuseCollisionParameter, mobiusCriticalBoundaryParameter]
    ring]
  rw [fixedEulerCofinal_boundaryParameter]

private theorem tendsto_fixedEulerCollisionParameter
    (s : ℝ) :
    Tendsto (fun n =>
      mobiusDiffuseCollisionParameter
        (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n))
      atTop (𝓝 (s + 1)) := by
  have h := (tendsto_fixedEulerCofinalSigma s).add_const s
  simpa only [mobiusDiffuseCollisionParameter_fixedEuler, add_comm] using h

private theorem tendsto_squarefreeMobiusTotal_fixedEulerCollision
    {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n =>
      squarefreeMobiusTotal
        (mobiusDiffuseCollisionParameter
          (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n)))
      atTop (𝓝 (squarefreeMobiusTotal (s + 1))) := by
  have htauR := tendsto_fixedEulerCollisionParameter s
  have htauC : Tendsto (fun n =>
      ((mobiusDiffuseCollisionParameter
        (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n) : ℝ) : ℂ))
      atTop (𝓝 ((s + 1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp htauR
  have hpart :=
    (GaloisForLFunctions.differentiableAt_squarefreePartition
      (s := ((s + 1 : ℝ) : ℂ)) (by simp; linarith)).continuousAt.tendsto.comp htauC
  have heq :
      (fun n =>
        (squarefreeMobiusTotal
          (mobiusDiffuseCollisionParameter
            (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n)) : ℂ)) =ᶠ[
              atTop]
      fun n =>
        GaloisForLFunctions.squarefreePartition
          (mobiusDiffuseCollisionParameter
            (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n) : ℂ) := by
    filter_upwards
      [htauR (Ioi_mem_nhds (by linarith : (1 : ℝ) < s + 1))]
      with n htau
    simpa [GaloisForLFunctions.squarefreePartition] using
      ofReal_squarefreeMobiusTotal_eq_zetaRatio htau
  have hcast := hpart.congr' heq.symm
  have htarget :
      GaloisForLFunctions.squarefreePartition ((s + 1 : ℝ) : ℂ) =
        (squarefreeMobiusTotal (s + 1) : ℂ) := by
    simpa [GaloisForLFunctions.squarefreePartition] using
      (ofReal_squarefreeMobiusTotal_eq_zetaRatio
        (by linarith : (1 : ℝ) < s + 1)).symm
  rw [htarget] at hcast
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcast
  simpa [Function.comp_def] using hre

private theorem tendsto_squarefreeMobiusLogMoment_fixedEulerCollision
    {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n =>
      squarefreeMobiusLogMoment 1
        (mobiusDiffuseCollisionParameter
          (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n)))
      atTop (𝓝 (squarefreeMobiusLogMoment 1 (s + 1))) := by
  have htauR := tendsto_fixedEulerCollisionParameter s
  have htauC : Tendsto (fun n =>
      ((mobiusDiffuseCollisionParameter
        (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n) : ℝ) : ℂ))
      atTop (𝓝 ((s + 1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp htauR
  have hflux_eq :
      infinitePrimeFlux =
        fun z : ℂ => -deriv riemannZeta z / riemannZeta z := by
    funext z
    simp only [infinitePrimeFlux, logDeriv_apply, neg_div]
  have hflux :
      DifferentiableAt ℂ infinitePrimeFlux (((s + 1 : ℝ) : ℂ)) := by
    rw [hflux_eq]
    exact differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re
      (s := ((s + 1 : ℝ) : ℂ)) (by simp; linarith)
  have hfluxTwo :
      DifferentiableAt ℂ infinitePrimeFlux (2 * (((s + 1 : ℝ) : ℂ))) := by
    rw [hflux_eq]
    exact differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re
      (s := 2 * (((s + 1 : ℝ) : ℂ))) (by simp; linarith)
  have hcomp : DifferentiableAt ℂ
      (fun z : ℂ => infinitePrimeFlux (2 * z)) (((s + 1 : ℝ) : ℂ)) :=
    hfluxTwo.comp (((s + 1 : ℝ) : ℂ)) (by fun_prop)
  have hcurrent :
      ContinuousAt GaloisForLFunctions.squarefreeFixedCurrent
        (((s + 1 : ℝ) : ℂ)) := by
    change ContinuousAt
      (fun z : ℂ => infinitePrimeFlux z - 2 * infinitePrimeFlux (2 * z))
      (((s + 1 : ℝ) : ℂ))
    exact hflux.continuousAt.sub (hcomp.const_mul (2 : ℂ)).continuousAt
  have hlimit := hcurrent.tendsto.comp htauC
  have heq :
      (fun n =>
        (squarefreeMobiusLogMoment 1
          (mobiusDiffuseCollisionParameter
            (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n)) : ℂ)) =ᶠ[
              atTop]
      fun n =>
        GaloisForLFunctions.squarefreeFixedCurrent
          (mobiusDiffuseCollisionParameter
            (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n) : ℂ) := by
    filter_upwards
      [htauR (Ioi_mem_nhds (by linarith : (1 : ℝ) < s + 1))]
      with n htau
    exact ofReal_squarefreeMobiusLogMoment_one_eq_fixedCurrent htau
  have hcast := hlimit.congr' heq.symm
  rw [← ofReal_squarefreeMobiusLogMoment_one_eq_fixedCurrent
    (by linarith : (1 : ℝ) < s + 1)] at hcast
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcast
  simpa [Function.comp_def] using hre

/-- **Fixed-Euler collision anomaly law.**  After division by the exact
Gamma graph scale, the physical diagonal collision has a nonzero universal
limit.  Fixed-speed collision disappearance therefore does not extend to the
double-singular CCM path. -/
theorem tendsto_fixedEuler_diffuseFisherCollisionResidual_div_graphScale
    {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n =>
      diffuseFisherCollisionResidual
          (squarefreeMobiusProbability (fixedEulerCofinalSigma s n))
          (mobiusCriticalFisherCoordinate (fixedEulerCofinalSigma s n))
          (mobiusCriticalDampingCoordinate
            (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n)) /
        ((fixedEulerCofinalSigma s n - 1) *
          (squarefreeMobiusTotal s /
            squarefreeMobiusTotal (fixedEulerCofinalSigma s n))))
      atTop (𝓝 (fixedEulerMobiusCollisionAnomaly s)) := by
  let sigma : ℕ → ℝ := fixedEulerCofinalSigma s
  let tau : ℕ → ℝ := fun n =>
    mobiusDiffuseCollisionParameter (sigma n) (fixedEulerCofinalDamping n)
  let epsilon : ℕ → ℝ := fun n => sigma n - 1
  have hsigma (n : ℕ) : 1 < sigma n :=
    fixedEulerCofinalSigma_gt_one hs n
  have hsigmaWithin :
      Tendsto sigma atTop (𝓝[>] (1 : ℝ)) := by
    simpa only [sigma] using tendsto_fixedEulerCofinalSigma_nhdsWithin hs
  have hepsilon : Tendsto epsilon atTop (𝓝 0) := by
    simpa only [epsilon, sigma, sub_self] using
      (tendsto_fixedEulerCofinalSigma s).sub_const 1
  have htotal :
      Tendsto (fun n => squarefreeMobiusTotal (tau n))
        atTop (𝓝 (squarefreeMobiusTotal (s + 1))) := by
    simpa only [tau, sigma] using
      tendsto_squarefreeMobiusTotal_fixedEulerCollision hs
  have hfarMoment :
      Tendsto (fun n => squarefreeMobiusLogMoment 1 (tau n))
        atTop (𝓝 (squarefreeMobiusLogMoment 1 (s + 1))) := by
    simpa only [tau, sigma] using
      tendsto_squarefreeMobiusLogMoment_fixedEulerCollision hs
  have hfarScaled :
      Tendsto (fun n =>
        epsilon n * squarefreeMobiusLogMoment 1 (tau n))
        atTop (𝓝 0) := by
    simpa using hepsilon.mul hfarMoment
  have hcritical :
      Tendsto (fun n =>
        epsilon n * squarefreeMobiusLogMoment 1 (sigma n))
        atTop (𝓝 1) := by
    change Tendsto (fun n =>
      (sigma n - 1) * squarefreeMobiusLogMoment 1 (sigma n))
      atTop (𝓝 1)
    convert
      tendsto_squarefreeMobiusLogMoment_one_critical.comp hsigmaWithin
        using 1
    funext n
    rfl
  have hmomentDifference :
      Tendsto (fun n =>
        epsilon n *
          (squarefreeMobiusLogMoment 1 (tau n) -
            squarefreeMobiusLogMoment 1 (sigma n)))
        atTop (𝓝 (-1)) := by
    have h := hfarScaled.sub hcritical
    convert h using 1 <;> ring
  have hinvScale :
      Tendsto (fun n =>
        (squarefreeMobiusTotal (sigma n))⁻¹ / epsilon n)
        atTop (𝓝 (riemannZeta (2 : ℂ)).re) := by
    change Tendsto (fun n =>
      (squarefreeMobiusTotal (sigma n))⁻¹ / (sigma n - 1))
      atTop (𝓝 (riemannZeta (2 : ℂ)).re)
    convert
      tendsto_inv_squarefreeMobiusTotal_div_sub_one.comp hsigmaWithin
        using 1
    funext n
    rfl
  have htwo :
      Tendsto (fun _ : ℕ => (-2 : ℝ)) atTop (𝓝 (-2 : ℝ)) :=
    tendsto_const_nhds
  have hmainBase :=
    (((htwo.mul htotal).mul hinvScale).mul hmomentDifference)
  have hmain :=
    hmainBase.div_const (squarefreeMobiusTotal s)
  have hmain' : Tendsto (fun n =>
      ((-2) * squarefreeMobiusTotal (tau n) *
          ((squarefreeMobiusTotal (sigma n))⁻¹ / epsilon n) *
          (epsilon n *
            (squarefreeMobiusLogMoment 1 (tau n) -
              squarefreeMobiusLogMoment 1 (sigma n)))) /
        squarefreeMobiusTotal s)
      atTop (𝓝 (fixedEulerMobiusCollisionAnomaly s)) := by
    have hlimit :
        (-2) * squarefreeMobiusTotal (s + 1) *
              (riemannZeta (2 : ℂ)).re * (-1) /
            squarefreeMobiusTotal s =
          fixedEulerMobiusCollisionAnomaly s := by
      simp only [fixedEulerMobiusCollisionAnomaly]
      ring
    rw [hlimit] at hmain
    exact hmain
  apply hmain'.congr'
  filter_upwards with n
  have heps : epsilon n ≠ 0 := sub_ne_zero.mpr (hsigma n).ne'
  have hsigmaz := (squarefreeMobiusTotal_pos (hsigma n)).ne'
  have hsz := (squarefreeMobiusTotal_pos hs).ne'
  rw [diffuseFisherCollisionResidual_mobius_eq
    (hsigma n) (fixedEulerCofinalDamping_nonneg n)]
  simp only [sigma, tau, epsilon]
  field_simp [heps, hsigmaz, hsz]

/-- Complex form of the anomaly on the exact singular Gamma denominator. -/
theorem tendsto_fixedEuler_mobiusDiffuseCollisionResidual_div_graphScale
    {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n =>
      mobiusDiffuseCollisionResidual
          (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n) /
        (((fixedEulerCofinalSigma s n - 1 : ℝ) : ℂ) *
          squarefreeMobiusBoundaryLayerLaplace
            (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n)))
      atTop (𝓝 (fixedEulerMobiusCollisionAnomaly s : ℂ)) := by
  have hreal :=
    tendsto_fixedEuler_diffuseFisherCollisionResidual_div_graphScale hs
  have hcast : Tendsto (fun n =>
      ((diffuseFisherCollisionResidual
          (squarefreeMobiusProbability (fixedEulerCofinalSigma s n))
          (mobiusCriticalFisherCoordinate (fixedEulerCofinalSigma s n))
          (mobiusCriticalDampingCoordinate
            (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n)) /
        ((fixedEulerCofinalSigma s n - 1) *
          (squarefreeMobiusTotal s /
            squarefreeMobiusTotal (fixedEulerCofinalSigma s n))) : ℝ) : ℂ))
      atTop (𝓝 (fixedEulerMobiusCollisionAnomaly s : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply hcast.congr'
  filter_upwards with n
  rw [← ofReal_diffuseFisherCollisionResidual_eq_mobiusDiffuseCollisionResidual
    (fixedEulerCofinalSigma_gt_one hs n)
    (fixedEulerCofinalDamping_nonneg n)]
  simp only [squarefreeMobiusBoundaryLayerLaplace,
    fixedEulerCofinal_boundaryParameter]
  push_cast
  rfl

/-- The physical strict-lower Gamma current acquires exactly twice the
collision anomaly on every fixed Euler point. -/
theorem tendsto_fixedEuler_oneCornerGammaCurrent_sub_completed
    {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n =>
      squarefreeMobiusOneCornerGammaCurrentTransportV
          (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n) -
        GaloisForLFunctions.completedSquarefreeFixedCurrent (s : ℂ))
      atTop (𝓝 (2 * (fixedEulerMobiusCollisionAnomaly s : ℂ))) := by
  have hcollision :=
    (tendsto_fixedEuler_mobiusDiffuseCollisionResidual_div_graphScale hs).const_mul 2
  apply hcollision.congr'
  filter_upwards with n
  rw [squarefreeMobiusOneCornerGammaCurrentTransportV_eq_completed_add_collision
    (fixedEulerCofinalSigma_gt_one hs n)
    (fixedEulerCofinalDamping_nonneg n)]
  simp only [fixedEulerCofinal_boundaryParameter]
  ring

/-- **Continued-Xi diagonal anomaly.**  The uncorrected physical one-corner
transport misses the fixed-Euler continued Xi source trace by the nonzero
purely imaginary term `-I * fixedEulerMobiusCollisionAnomaly s`. -/
theorem tendsto_fixedEuler_oneCornerGammaXiWard_sub_continuedSource
    {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n =>
      squarefreeMobiusOneCornerGammaXiWardTransportV
          (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n) -
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate (s : ℂ)))
      atTop (𝓝 (-I * (fixedEulerMobiusCollisionAnomaly s : ℂ))) := by
  have h :=
    (tendsto_fixedEuler_oneCornerGammaCurrent_sub_completed hs).const_mul
      (-I / 2)
  have h' : Tendsto (fun n =>
      (-I / 2) *
        (squarefreeMobiusOneCornerGammaCurrentTransportV
            (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n) -
          GaloisForLFunctions.completedSquarefreeFixedCurrent (s : ℂ)))
      atTop (𝓝 (-I * (fixedEulerMobiusCollisionAnomaly s : ℂ))) := by
    convert h using 1 <;> ring
  apply h'.congr'
  filter_upwards with n
  simpa only [fixedEulerCofinal_boundaryParameter] using
    (squarefreeMobiusOneCornerGammaXiWardTransportV_sub_continuedSource
      (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n)).symm

/-- The continued-Xi anomaly cannot vanish at an admissible fixed Euler point. -/
theorem fixedEuler_oneCornerGammaXiWard_anomaly_ne_zero
    {s : ℝ} (hs : 1 < s) :
    -I * (fixedEulerMobiusCollisionAnomaly s : ℂ) ≠ 0 := by
  exact mul_ne_zero (by simp)
    (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (fixedEulerMobiusCollisionAnomaly_pos hs)))

/-- Cofinal orthogonal replication cancels the diagonal anomaly on the
double-singular fixed-Euler path.  No rate coupling with the collapsing
normal coordinate is needed: any unbounded replica count suffices. -/
theorem tendsto_fixedEuler_cofinalReplicaGammaCurrent_sub_completed
    {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n =>
      squarefreeMobiusCofinalReplicaGammaCurrentTransportV
          (n + 1) (fixedEulerCofinalSigma s n)
          (fixedEulerCofinalDamping n) -
        GaloisForLFunctions.completedSquarefreeFixedCurrent (s : ℂ))
      atTop (𝓝 0) := by
  have hcollision :=
    tendsto_fixedEuler_mobiusDiffuseCollisionResidual_div_graphScale hs
  have hinvR :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hinvC : Tendsto (fun n : ℕ =>
      ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
      atTop (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hinvR
  have hscale : Tendsto (fun n : ℕ =>
      (2 / ((n + 1 : ℕ) : ℂ)))
      atTop (𝓝 0) := by
    have h := hinvC.const_mul (2 : ℂ)
    convert h using 1 <;> norm_num [div_eq_mul_inv]
  have herror := hscale.mul hcollision
  have herror' : Tendsto (fun n =>
      ((2 / ((n + 1 : ℕ) : ℂ)) *
          mobiusDiffuseCollisionResidual
            (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n)) /
        (((fixedEulerCofinalSigma s n - 1 : ℝ) : ℂ) *
          squarefreeMobiusBoundaryLayerLaplace
            (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n)))
      atTop (𝓝 0) := by
    convert herror using 1 <;> ring
  apply herror'.congr'
  filter_upwards with n
  rw [squarefreeMobiusCofinalReplicaGammaCurrentTransportV_eq_completed_add_collision
    (Nat.succ_pos n)
    (fixedEulerCofinalSigma_gt_one hs n)
    (fixedEulerCofinalDamping_nonneg n)]
  simp only [fixedEulerCofinal_boundaryParameter]
  ring

/-- **Double-singular replicated Xi incidence.**  One cofinal family of
strict-lower replicated Möbius corners reconstructs the continued completed
Xi trace at every fixed Euler point.  This is the constructive resolution of
the diagonal anomaly above. -/
theorem tendsto_fixedEuler_cofinalReplicaGammaXiWard_sub_continuedSource
    {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n =>
      squarefreeMobiusCofinalReplicaGammaXiWardTransportV
          (n + 1) (fixedEulerCofinalSigma s n)
          (fixedEulerCofinalDamping n) -
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate (s : ℂ)))
      atTop (𝓝 0) := by
  have h :=
    (tendsto_fixedEuler_cofinalReplicaGammaCurrent_sub_completed hs).const_mul
      (-I / 2)
  have h' : Tendsto (fun n =>
      (-I / 2) *
        (squarefreeMobiusCofinalReplicaGammaCurrentTransportV
            (n + 1) (fixedEulerCofinalSigma s n)
            (fixedEulerCofinalDamping n) -
          GaloisForLFunctions.completedSquarefreeFixedCurrent (s : ℂ)))
      atTop (𝓝 0) := by
    simpa using h
  apply h'.congr'
  filter_upwards with n
  rw [squarefreeMobiusCofinalReplicaGammaXiWardTransportV,
    continuedPrimeArchSourceRelativeTrace_eq_completedSquarefree_add_correction,
    xiWardCenteredCoordinate_source]
  simp only [fixedEulerCofinal_boundaryParameter]
  ring

end RHTower
