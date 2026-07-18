import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinPurityJacobian
import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinInverseScaleSelection

/-!
# Scale-covariant Bernstein--Abel tomography

This file bundles the source chart, its exact atomic realization, the finite square-root Abel
selection, and the confocal recession law into one observation theorem.  Every clause concerns the
same scale-covariant field

`P(N,R) = bernsteinScalePurityPolynomial m N` evaluated at `R⁻¹`.
-/

open Complex Filter Topology
open scoped BigOperators Real ComplexOrder

namespace RHTower

noncomputable section

/-- The complete conclusion carried by one scale-covariant Bernstein--Abel observation field. -/
structure ScaleCovariantBernsteinAbelTomographyLaw
    {I : Type*} (c z : I → ℂ) (m : ℕ → ℝ) (M : ℝ) : Prop where
  /-- The cofinal family of finite scale polynomials recovers the complete pointed source. -/
  source_faithful :
    ∀ m' : ℕ → ℝ, 0 < m' 0 →
      (∀ N, bernsteinScalePurityPolynomial m' N =
        bernsteinScalePurityPolynomial m N) → m' = m
  /-- Every finite source chart has an explicit nonvanishing coordinate Jacobian. -/
  source_noncritical :
    ∀ N, (bernsteinPurityJetJacobian N m).det ≠ 0
  /-- At every positive scale the observation is literally the square energy of the same atomic
  source after inverse radial scaling. -/
  atomic_realization :
    ∀ {R : ℝ}, 0 < R → ∀ N : ℕ,
      scaleCovariantBernsteinObservation m N R =
        atomicBernsteinPacketSquareEnergy c (inverseScaleAtomicNode z R) N
  /-- Every transverse occupied atom selects a finite positive maximal packet, a sharp coefficient
  half-order law, and the corresponding square-root Abel boundary. -/
  finite_boundary_selection :
    ∀ {R : ℝ}, 2 * M < R → ∀ {i0 : I}, (z i0).im ≠ 0 →
      ∃ D : Finset I, ∃ B beta L : ℝ,
        B = HTGeometry.confocalAmplitudeEnvelope (Set.range z) R ∧
        1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
        (∀ i ∈ D,
          atomicBernsteinAmplitude (inverseScaleAtomicNode z R) i = B) ∧
        (∀ i ∉ D,
          atomicBernsteinAmplitude (inverseScaleAtomicNode z R) i ≤ beta) ∧
        L = ∑ v ∈ D.image (inverseScaleAtomicNode z R),
          ‖finiteExponentialFiberCoefficient D c (inverseScaleAtomicNode z R) v‖ ^ 2 *
            bernsteinAffineRowHalfOrderConstant v ∧
        0 < L ∧
        Tendsto
          (fun N : ℕ => Real.sqrt N *
            scaleCovariantBernsteinObservation m N R / (B ^ 2) ^ N)
          atTop (nhds L) ∧
        Tendsto
          (fun t : ℝ => Real.sqrt (1 - B ^ 2 * t) *
            scaleCovariantBernsteinAbelField m R t)
          (nhdsWithin (1 / B ^ 2) (Set.Ico 0 (1 / B ^ 2)))
          (nhds (Real.sqrt Real.pi * L))
  /-- Unit Abel radius is exactly positivity of every occupied coordinate. -/
  exact_radical :
    ∀ {R : ℝ}, M < R →
      (HTGeometry.confocalAbelRadius (Set.range z) R = 1 ↔
        ∀ i, (0 : ℂ) ≤ z i)
  /-- The squared-amplitude recession extracts twice the intrinsic transverse defect. -/
  amplitude_recession :
    Tendsto
      (fun R : ℝ => R *
        (HTGeometry.confocalAmplitudeEnvelope (Set.range z) R ^ 2 - 1))
      atTop
      (nhds (2 * HTGeometry.transverseDefectEnvelope (Set.range z)))
  /-- The Abel-radius recession extracts the same intrinsic transverse defect. -/
  abel_radius_recession :
    Tendsto
      (fun R : ℝ => R *
        (1 - HTGeometry.confocalAbelRadius (Set.range z) R))
      atTop
      (nhds (2 * HTGeometry.transverseDefectEnvelope (Set.range z)))

/-- **Scale-covariant Bernstein--Abel tomography theorem.**  A bounded summable atomic source with
pointed real moments, injective occupied coordinates, cofinally vanishing support, and no negative
real atom is completely recovered by one scale-covariant purity field.  The same field has an exact
atomic square-energy realization, selects every transverse phase through a finite positive
square-root packet, and has a confocal boundary flow whose first recession is twice the intrinsic
transverse defect. -/
theorem scaleCovariantBernsteinAbel_tomography
    {I : Type*} [Nonempty I] (c z : I → ℂ) (m : ℕ → ℝ)
    (hc : Summable c)
    (hz0 : Tendsto z cofinite (nhds 0))
    (hzinj : Function.Injective z)
    (hcne : ∀ i, c i ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, ‖z i‖ ≤ M)
    (hreal : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hmoment : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hm0 : 0 < m 0) :
    ScaleCovariantBernsteinAbelTomographyLaw c z m M := by
  let S : Set ℂ := Set.range z
  have hSne : S.Nonempty := Set.range_nonempty z
  have hSbound : ∀ w ∈ S, ‖w‖ ≤ M := by
    rintro w ⟨i, rfl⟩
    exact hbound i
  refine {
    source_faithful := ?_
    source_noncritical := ?_
    atomic_realization := ?_
    finite_boundary_selection := ?_
    exact_radical := ?_
    amplitude_recession := ?_
    abel_radius_recession := ?_ }
  · intro m' hm' hpoly
    funext r
    exact bernsteinScalePurityPolynomial_injectiveOn_pointed hm' hm0
      (hpoly r) r (le_refl r)
  · intro N
    exact det_bernsteinPurityJetJacobian_ne_zero N hm0.ne'
  · intro R hR N
    exact scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
      hc hbound hmoment hR N
  · intro R hR i0 hi0
    have hRpos : 0 < R := by linarith
    obtain ⟨D, B, beta, L, hBconf, hB, hbeta1, hbeta, hDne, hD, hDsub,
        hL, hLpos, hhalf⟩ :=
      exists_positive_halfOrder_inverseScaleAtomicPacket
        c z hc hz0 hzinj hcne hM hbound hR hreal hi0
    have hobs : Tendsto
        (fun N : ℕ => Real.sqrt N *
          scaleCovariantBernsteinObservation m N R / (B ^ 2) ^ N)
        atTop (nhds L) := by
      apply hhalf.congr'
      filter_upwards with N
      rw [scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
        hc hbound hmoment hRpos]
    have habel := tendsto_scaleCovariantBernsteinAbelField_of_atomic_halfOrder
      hc hbound hmoment hRpos (lt_trans zero_lt_one hB) hhalf
    exact ⟨D, B, beta, L, hBconf, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hL, hLpos, hobs, habel⟩
  · intro R hRM
    rw [HTGeometry.confocalAbelRadius_eq_one_iff hSne hM hRM hSbound,
      HTGeometry.transverseDefectEnvelope_eq_zero_iff hSne hSbound]
    simp only [S, Set.forall_mem_range]
  · exact HTGeometry.tendsto_mul_confocalAmplitudeEnvelope_sq_sub_one
      hSne hM hSbound
  · exact HTGeometry.tendsto_mul_one_sub_confocalAbelRadius
      hSne hM hSbound

end

end RHTower
