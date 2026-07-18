import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinAtomicObservation
import GaloisForLFunctions.RHTower.FiniteExponentialPencilUniformGap
import GaloisForLFunctions.RHTower.BernsteinEllipseMixedModeGap

/-!
# Generic finite-packet selection for a small atomic Bernstein source

An injectively indexed, absolutely summable atomic source whose nodes tend cofinally to zero has a
finite maximal Bernstein packet whenever one node is nonreal.  If every real node is nonnegative
and all nodes lie in the open half disk, reflection collisions are impossible.  The maximal packet
therefore has a positive half-order energy and controls the complete atomic packet.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

noncomputable section

/-- Affine Bernstein amplitude of one normalized atomic node. -/
def atomicBernsteinAmplitude {I : Type*} (u : I → ℂ) (i : I) : ℝ :=
  ‖u i‖ + ‖1 - u i‖

/-- Cofinally vanishing nodes have cofinally neutral affine amplitude. -/
theorem tendsto_atomicBernsteinAmplitude_cofinite_one
    {I : Type*} {u : I → ℂ} (hu : Tendsto u cofinite (nhds 0)) :
    Tendsto (atomicBernsteinAmplitude u) cofinite (nhds 1) := by
  have hone : Tendsto (fun _ : I => (1 : ℂ)) cofinite (nhds 1) :=
    tendsto_const_nhds
  have h := hu.norm.add (hone.sub hu).norm
  simpa only [atomicBernsteinAmplitude, norm_zero, sub_zero, norm_one,
    zero_add] using h

/-- In the half disk, a nonnegative real node has neutral affine amplitude.  Hence every
superunit node is nonreal. -/
theorem im_ne_zero_of_one_lt_atomicBernsteinAmplitude
    {u : ℂ} (hhalf : ‖u‖ < 1 / 2)
    (hreal : u.im = 0 → 0 ≤ u.re)
    (hA : 1 < ‖u‖ + ‖1 - u‖) :
    u.im ≠ 0 := by
  intro him
  have hre0 : 0 ≤ u.re := hreal him
  have hrelt : u.re < 1 := by
    have hrele : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
    rw [abs_of_nonneg hre0] at hrele
    linarith
  have hnormu : ‖u‖ = u.re := by
    rw [Complex.norm_def, Complex.normSq_apply, him]
    rw [show u.re * u.re + 0 * 0 = u.re ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg hre0]
  have hnormsub : ‖1 - u‖ = 1 - u.re := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      him, sub_zero]
    rw [show (1 - u.re) * (1 - u.re) + 0 * 0 = (1 - u.re) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (sub_nonneg.mpr hrelt.le)]
  rw [hnormu, hnormsub] at hA
  linarith

/-- Injective coordinates make every occupied finite fiber coefficient equal to its unique
weight. -/
theorem finiteExponentialFiberCoefficient_eq_of_injective
    {I : Type*} {D : Finset I} {c u : I → ℂ}
    (hu : Function.Injective u) {i : I} (hi : i ∈ D) :
    finiteExponentialFiberCoefficient D c u (u i) = c i := by
  classical
  rw [finiteExponentialFiberCoefficient]
  change ∑ j ∈ D.filter (fun j => u j = u i), c j = c i
  rw [Finset.sum_eq_single i]
  · intro j hj hji
    have huji : u j = u i := (Finset.mem_filter.mp hj).2
    exact (hji (hu huji)).elim
  · simp [hi]

/-- Distinct equal-amplitude nodes in the open half disk have distinct maximizing ellipse phases. -/
theorem bernsteinEllipsePhase_ne_of_small_distinct_equalAmplitude
    {u v : ℂ} (huim : u.im ≠ 0) (hvim : v.im ≠ 0)
    (huhalf : ‖u‖ < 1 / 2) (hvhalf : ‖v‖ < 1 / 2)
    (huv : u ≠ v)
    (hamp : ‖v‖ + ‖1 - v‖ = ‖u‖ + ‖1 - u‖) :
    bernsteinEllipsePhase u ≠ bernsteinEllipsePhase v := by
  intro hphase
  rcases eq_or_eq_one_sub_conj_of_bernsteinEllipsePhase_eq_of_amplitude_eq
      huim hvim hphase.symm hamp with heq | hreflect
  · exact huv heq.symm
  · have hone : (1 : ℝ) ≤ ‖v‖ + ‖u‖ := by
      have hsum : v + star u = 1 := by rw [hreflect]; ring
      calc
        1 = ‖v + star u‖ := by rw [hsum]; norm_num
        _ ≤ ‖v‖ + ‖star u‖ := norm_add_le _ _
        _ = ‖v‖ + ‖u‖ := by rw [norm_star]
    linarith

/-- **Generic positive maximal-packet theorem.**  The complete square energy of a small,
pre-aggregated atomic source has a positive sharp half-order law at one finite source-attained
amplitude packet. -/
theorem exists_positive_halfOrder_atomicBernsteinPacket_of_small_source
    {I : Type*} (c u : I → ℂ) (hc : Summable c)
    (hu0 : Tendsto u cofinite (nhds 0))
    (huinj : Function.Injective u)
    (hcne : ∀ i, c i ≠ 0)
    (hhalf : ∀ i, ‖u i‖ < 1 / 2)
    (hreal : ∀ i, (u i).im = 0 → 0 ≤ (u i).re)
    {i0 : I} (hi0 : (u i0).im ≠ 0) :
    ∃ D : Finset I, ∃ B beta L : ℝ,
      1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
      (∀ i ∈ D, atomicBernsteinAmplitude u i = B) ∧
      (∀ i ∉ D, atomicBernsteinAmplitude u i ≤ beta) ∧
      L = ∑ v ∈ D.image u,
        ‖finiteExponentialFiberCoefficient D c u v‖ ^ 2 *
          bernsteinAffineRowHalfOrderConstant v ∧
      0 < L ∧
      Tendsto
        (fun n : ℕ => Real.sqrt n *
          atomicBernsteinPacketSquareEnergy c u n / (B ^ 2) ^ n)
        atTop (nhds L) := by
  classical
  let A : I → ℝ := atomicBernsteinAmplitude u
  let a : I → ℂ := fun i => (A i : ℂ)
  have hA : Tendsto A cofinite (nhds 1) :=
    tendsto_atomicBernsteinAmplitude_cofinite_one hu0
  have ha : Tendsto a cofinite (nhds 1) := by
    simpa only [a, Complex.ofReal_one] using
      Complex.continuous_ofReal.tendsto 1 |>.comp hA
  have hAnonneg (i : I) : 0 ≤ A i :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hnorma (i : I) : ‖a i‖ = A i := by
    dsimp only [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hAnonneg i)]
  have hi0A : 1 < A i0 := by
    dsimp only [A, atomicBernsteinAmplitude]
    simpa only [add_comm] using one_lt_norm_add_norm_one_sub hi0
  have hi0a : 1 < ‖a i0‖ := by rw [hnorma]; exact hi0A
  obtain ⟨D, B, beta, hB, hbeta1, hbeta, hDne, hD, hDsub⟩ :=
    exists_finite_maximal_norm_packet_uniformly_separated a ha hi0a
  have hDamp : ∀ i ∈ D, atomicBernsteinAmplitude u i = B := by
    intro i hi
    simpa only [hnorma, A] using hD i hi
  have hDsubAmp : ∀ i ∉ D, atomicBernsteinAmplitude u i ≤ beta := by
    intro i hi
    simpa only [hnorma, A] using hDsub i hi
  let U : Finset ℂ := D.image u
  let C : ℂ → ℂ := finiteExponentialFiberCoefficient D c u
  let L : ℝ := ∑ v ∈ U,
    ‖C v‖ ^ 2 * bernsteinAffineRowHalfOrderConstant v
  have hUne : U.Nonempty := hDne.image u
  have hamp : ∀ v ∈ U, ‖v‖ + ‖1 - v‖ = B := by
    intro v hv
    obtain ⟨i, hiD, hiv⟩ := Finset.mem_image.mp hv
    rw [← hiv]
    exact hDamp i hiD
  have hvhalf : ∀ v ∈ U, ‖v‖ < 1 / 2 := by
    intro v hv
    obtain ⟨i, hiD, hiv⟩ := Finset.mem_image.mp hv
    rw [← hiv]
    exact hhalf i
  have hvim : ∀ v ∈ U, v.im ≠ 0 := by
    intro v hv
    obtain ⟨i, hiD, hiv⟩ := Finset.mem_image.mp hv
    rw [← hiv]
    exact im_ne_zero_of_one_lt_atomicBernsteinAmplitude
      (hhalf i) (hreal i) (hB.trans_eq (hDamp i hiD).symm)
  have hv0 : ∀ v ∈ U, v ≠ 0 := by
    intro v hv hvzero
    exact hvim v hv (by rw [hvzero]; rfl)
  have hv1 : ∀ v ∈ U, v ≠ 1 := by
    intro v hv hvone
    have := hvhalf v hv
    rw [hvone] at this
    norm_num at this
  have hmixed : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ∃ gamma : ℝ, 0 ≤ gamma ∧ gamma < B ^ 2 ∧
        ∀ n : ℕ, ‖reflectedBernsteinCrossMoment v w n‖ ≤ gamma ^ n := by
    intro v hv w hw hvw
    obtain ⟨gamma, hgamma0, hgamma, hpoint⟩ :=
      exists_uniform_reflectedBernsteinProduct_gap_of_phase_ne
        (hvim v hv) (hvim w hw) (hamp v hv) (hamp w hw)
        (bernsteinEllipsePhase_ne_of_small_distinct_equalAmplitude
          (hvim v hv) (hvim w hw) (hvhalf v hv) (hvhalf w hw) hvw
          ((hamp w hw).trans (hamp v hv).symm))
    exact ⟨gamma, hgamma0, hgamma,
      norm_reflectedBernsteinCrossMoment_le_pow hpoint⟩
  have hfinite :=
    tendsto_sqrtNat_mul_finiteBernsteinCoordinatePacketEnergy_div_pow
      U C (lt_trans zero_lt_one hB) hamp hv0 hv1 hmixed
  have hCne : ∀ v ∈ U, C v ≠ 0 := by
    intro v hv
    obtain ⟨i, hiD, hiv⟩ := Finset.mem_image.mp hv
    rw [← hiv]
    dsimp only [C]
    rw [finiteExponentialFiberCoefficient_eq_of_injective huinj hiD]
    exact hcne i
  have htermpos : ∀ v ∈ U,
      0 < ‖C v‖ ^ 2 * bernsteinAffineRowHalfOrderConstant v := by
    intro v hv
    exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (hCne v hv)))
      (bernsteinAffineRowHalfOrderConstant_pos (hv0 v hv) (hv1 v hv))
  have hLpos : 0 < L := by
    dsimp only [L]
    apply Finset.sum_pos' (fun v hv => (htermpos v hv).le)
    obtain ⟨v, hv⟩ := hUne
    exact ⟨v, hv, htermpos v hv⟩
  have hfull :=
    tendsto_atomicBernsteinPacketSquareEnergy_of_finiteCoordinatePacket
      D c u hc (lt_trans zero_lt_one hB) (zero_le_one.trans hbeta1.le) hbeta
      (fun i hi => (hDamp i hi).le) hDsubAmp (by
        simpa only [U, C, L] using hfinite)
  exact ⟨D, B, beta, L, hB, hbeta1, hbeta, hDne, hDamp, hDsubAmp,
    rfl, hLpos, hfull⟩

end

end RHTower
