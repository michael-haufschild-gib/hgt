import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinAggregateSource
import GaloisForLFunctions.HTGeometry.ConfocalExposedOrbitTomography

/-!
# Presentation rigidity of scale-covariant Bernstein tomography

The pointed real moment sequence need not determine an arbitrary complex atomic presentation.
Nevertheless, inside the defect-neutral transverse class it determines the confocal amplitude at
every common admissible scale.  The recession law then makes the limiting transverse-defect
envelope presentation-independent as well.
-/

open Complex Filter Topology
open scoped BigOperators Real ComplexOrder

namespace RHTower

noncomputable section

/-- **Local scale-germ source faithfulness.**  The complete pointed moment sequence is already
determined by the positive purity observations on any nonempty open scale-coordinate interval.
For each degree `N`, only the restriction of the degree-`N` observation to that one interval is
used to recover the first `N + 1` moments. -/
theorem bernsteinScalePurityField_interval_source_faithful
    {m m' : ℕ → ℝ} (hm0 : 0 < m 0) (hm0' : 0 < m' 0)
    {a b : ℝ} (hab : a < b)
    (hobs : ∀ N : ℕ, ∀ x ∈ Set.Ioo a b,
      bernsteinCoefficientPurity (fun r => x ^ r * m r) N =
        bernsteinCoefficientPurity (fun r => x ^ r * m' r) N) :
    m = m' := by
  funext r
  exact bernsteinScalePurity_interval_tomography hm0 hm0' hab
    (fun x hx => hobs r x hx) r (le_refl r)

/-- The same local source-faithfulness statement written directly for the scale polynomials. -/
theorem bernsteinScalePurityPolynomial_interval_source_faithful
    {m m' : ℕ → ℝ} (hm0 : 0 < m 0) (hm0' : 0 < m' 0)
    {a b : ℝ} (hab : a < b)
    (hobs : ∀ N : ℕ, ∀ x ∈ Set.Ioo a b,
      (bernsteinScalePurityPolynomial m N).eval x =
        (bernsteinScalePurityPolynomial m' N).eval x) :
    m = m' := by
  apply bernsteinScalePurityField_interval_source_faithful hm0 hm0' hab
  intro N x hx
  simpa only [eval_bernsteinScalePurityPolynomial] using hobs N x hx

/-- Two nonreal confocal branches that agree on one nonempty open radius interval have the same
real coordinate and the same absolute imaginary coordinate.  Thus the branch determines exactly
the conjugation orbit of its source point. -/
theorem confocalBranch_orbit_eq_of_eqOn_Ioo
    {x y x' y' a b : ℝ} (hy : y ≠ 0) (hy' : y' ≠ 0) (hab : a < b)
    (hbranch : Set.EqOn (HTGeometry.confocalBranch x y)
      (HTGeometry.confocalBranch x' y') (Set.Ioo a b)) :
    x = x' ∧ |y| = |y'| := by
  let R : ℝ := (a + b) / 2
  have hR : R ∈ Set.Ioo a b := by
    constructor <;> dsimp only [R] <;> linarith
  have hslope : Set.EqOn (HTGeometry.confocalBranchSlope x y)
      (HTGeometry.confocalBranchSlope x' y') (Set.Ioo a b) := by
    intro T hT
    have hlocal : HTGeometry.confocalBranch x y =ᶠ[nhds T]
        HTGeometry.confocalBranch x' y' :=
      hbranch.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hT)
    exact (HTGeometry.hasDerivAt_confocalBranch (R := T) hy).unique
      ((HTGeometry.hasDerivAt_confocalBranch (R := T) hy').congr_of_eventuallyEq hlocal)
  have hp : HTGeometry.confocalBranchSlope x y R =
      HTGeometry.confocalBranchSlope x' y' R := hslope hR
  have hslopeLocal : HTGeometry.confocalBranchSlope x y =ᶠ[nhds R]
      HTGeometry.confocalBranchSlope x' y' :=
    hslope.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hR)
  have hq : HTGeometry.confocalBranchCurvature x y R =
      HTGeometry.confocalBranchCurvature x' y' R :=
    (HTGeometry.hasDerivAt_confocalBranchSlope (R := R) hy).unique
      ((HTGeometry.hasDerivAt_confocalBranchSlope (R := R) hy').congr_of_eventuallyEq
        hslopeLocal)
  constructor
  · calc
      x = R - ((1 - HTGeometry.confocalBranchSlope x y R ^ 2) /
            HTGeometry.confocalBranchCurvature x y R) *
            HTGeometry.confocalBranchSlope x y R :=
        (HTGeometry.confocalBranch_reconstruct_re (R := R) hy).symm
      _ = R - ((1 - HTGeometry.confocalBranchSlope x' y' R ^ 2) /
            HTGeometry.confocalBranchCurvature x' y' R) *
            HTGeometry.confocalBranchSlope x' y' R := by rw [hp, hq]
      _ = x' := HTGeometry.confocalBranch_reconstruct_re (R := R) hy'
  · calc
      |y| = ((1 - HTGeometry.confocalBranchSlope x y R ^ 2) /
            HTGeometry.confocalBranchCurvature x y R) *
            Real.sqrt (1 - HTGeometry.confocalBranchSlope x y R ^ 2) :=
        (HTGeometry.confocalBranch_reconstruct_abs_im (R := R) hy).symm
      _ = ((1 - HTGeometry.confocalBranchSlope x' y' R ^ 2) /
            HTGeometry.confocalBranchCurvature x' y' R) *
            Real.sqrt (1 - HTGeometry.confocalBranchSlope x' y' R ^ 2) := by rw [hp, hq]
      _ = |y'| := HTGeometry.confocalBranch_reconstruct_abs_im (R := R) hy'

/-- **Fixed-scale presentation rigidity.**  Two defect-neutral transverse atomic presentations of
the same pointed real moments have the same confocal amplitude at every radius exceeding both
support bounds.  Thus the positive square-energy growth selects an intrinsic scale even when the
underlying atomic presentation is not known to be unique. -/
theorem confocalAmplitudeEnvelope_eq_of_common_pointed_moments
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    (hzinj : Function.Injective z) (hwinj : Function.Injective w)
    (hcne : ∀ i, c i ≠ 0) (hdne : ∀ j, d j ≠ 0)
    {M N R : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hRM : M < R) (hRN : N < R)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m n : ℂ) = atomicPowerMoment d w n)
    {i0 : I} (hi0 : (z i0).im ≠ 0)
    {j0 : J} (hj0 : (w j0).im ≠ 0) :
    HTGeometry.confocalAmplitudeEnvelope (Set.range z) R =
      HTGeometry.confocalAmplitudeEnvelope (Set.range w) R := by
  have hRpos : 0 < R := hM.trans_lt hRM
  obtain ⟨Bz, hBzConf, hBz, hlimZ⟩ :=
    exists_tendsto_inverseScaleAtomicBernsteinRpowEnergy_of_transverse_neutral
      c z hc htransZ hzinj hcne hM hboundZ hRM (by norm_num : (0 : ℝ) < 2)
      hrealZ hi0
  obtain ⟨Bw, hBwConf, hBw, hlimW⟩ :=
    exists_tendsto_inverseScaleAtomicBernsteinRpowEnergy_of_transverse_neutral
      d w hd htransW hwinj hdne hN hboundW hRN (by norm_num : (0 : ℝ) < 2)
      hrealW hj0
  have hobsZ : Tendsto
      (fun n : ℕ => scaleCovariantBernsteinObservation m n R ^ ((n : ℝ)⁻¹))
      atTop (nhds (Bz ^ (2 : ℝ))) := by
    apply hlimZ.congr'
    filter_upwards with n
    have hobs := scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
      hc hboundZ hmomentZ hRpos n
    rw [hobs, atomicBernsteinPacketSquareEnergy,
      ← finitePacketRpowEnergy_two_eq_squareEnergy]
  have hobsW : Tendsto
      (fun n : ℕ => scaleCovariantBernsteinObservation m n R ^ ((n : ℝ)⁻¹))
      atTop (nhds (Bw ^ (2 : ℝ))) := by
    apply hlimW.congr'
    filter_upwards with n
    have hobs := scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
      hd hboundW hmomentW hRpos n
    rw [hobs, atomicBernsteinPacketSquareEnergy,
      ← finitePacketRpowEnergy_two_eq_squareEnergy]
  have hsq : Bz ^ (2 : ℝ) = Bw ^ (2 : ℝ) :=
    tendsto_nhds_unique hobsZ hobsW
  have hsq' : Bz ^ (2 : ℕ) = Bw ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using hsq
  have hBz0 : 0 ≤ Bz := (by norm_num : (0 : ℝ) ≤ 1).trans hBz.le
  have hBw0 : 0 ≤ Bw := (by norm_num : (0 : ℝ) ≤ 1).trans hBw.le
  have hBeq : Bz = Bw := (sq_eq_sq₀ hBz0 hBw0).mp hsq'
  rw [← hBzConf, ← hBwConf, hBeq]

/-- **Exposed-orbit presentation rigidity.**  Suppose two admissible presentations of the same
pointed moments each have one nonreal node exposing their common confocal envelope throughout a
nonempty exterior radius interval.  Then those exposed nodes have the same real coordinate and
the same absolute imaginary coordinate.  The positive scale field therefore reconstructs the
entire conjugation orbit of every stably exposed atom, not only its maximal amplitude. -/
theorem exposed_confocal_orbit_eq_of_common_pointed_moments
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    (hzinj : Function.Injective z) (hwinj : Function.Injective w)
    (hcne : ∀ i, c i ≠ 0) (hdne : ∀ j, d j ≠ 0)
    {M N a b : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hMa : max M N < a) (hab : a < b)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m n : ℂ) = atomicPowerMoment d w n)
    {i0 : I} (hi0 : (z i0).im ≠ 0)
    {j0 : J} (hj0 : (w j0).im ≠ 0)
    (hexposedZ : Set.EqOn
      (fun R : ℝ => R * HTGeometry.confocalAmplitudeEnvelope (Set.range z) R)
      (HTGeometry.confocalBranch (z i0).re (z i0).im) (Set.Ioo a b))
    (hexposedW : Set.EqOn
      (fun R : ℝ => R * HTGeometry.confocalAmplitudeEnvelope (Set.range w) R)
      (HTGeometry.confocalBranch (w j0).re (w j0).im) (Set.Ioo a b)) :
    (z i0).re = (w j0).re ∧ |(z i0).im| = |(w j0).im| := by
  apply confocalBranch_orbit_eq_of_eqOn_Ioo hi0 hj0 hab
  intro R hR
  have hRM : M < R := (le_max_left M N).trans_lt (hMa.trans hR.1)
  have hRN : N < R := (le_max_right M N).trans_lt (hMa.trans hR.1)
  calc
    HTGeometry.confocalBranch (z i0).re (z i0).im R =
        R * HTGeometry.confocalAmplitudeEnvelope (Set.range z) R :=
      (hexposedZ hR).symm
    _ = R * HTGeometry.confocalAmplitudeEnvelope (Set.range w) R := by
      rw [confocalAmplitudeEnvelope_eq_of_common_pointed_moments
        c z d w m hc hd htransZ htransW hzinj hwinj hcne hdne hM hN
        hboundZ hboundW hRM hRN hrealZ hrealW hmomentZ hmomentW hi0 hj0]
    _ = HTGeometry.confocalBranch (w j0).re (w j0).im R := hexposedW hR

/-- The sharp quadratic coefficient is presentation-rigid as well: the common positive
observation has one common half-order asymptotic, normalized by the common selected amplitude. -/
theorem exists_common_halfOrder_limit_of_common_pointed_moments
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    (hzinj : Function.Injective z) (hwinj : Function.Injective w)
    (hcne : ∀ i, c i ≠ 0) (hdne : ∀ j, d j ≠ 0)
    {M N R : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hRM : M < R) (hRN : N < R)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m n : ℂ) = atomicPowerMoment d w n)
    {i0 : I} (hi0 : (z i0).im ≠ 0)
    {j0 : J} (hj0 : (w j0).im ≠ 0) :
    ∃ B L : ℝ,
      B = HTGeometry.confocalAmplitudeEnvelope (Set.range z) R ∧
      B = HTGeometry.confocalAmplitudeEnvelope (Set.range w) R ∧
      1 < B ∧ 0 < L ∧
      Tendsto
        (fun n : ℕ => Real.sqrt n *
          scaleCovariantBernsteinObservation m n R / (B ^ 2) ^ n)
        atTop (nhds L) := by
  have hRpos : 0 < R := hM.trans_lt hRM
  obtain ⟨D, B, beta, L, hBz, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hLdef, hL, hhalf⟩ :=
    exists_positive_halfOrder_inverseScaleAtomicPacket_of_transverse_neutral
      c z hc htransZ hzinj hcne hM hboundZ hRM hrealZ hi0
  have hBzw := confocalAmplitudeEnvelope_eq_of_common_pointed_moments
    c z d w m hc hd htransZ htransW hzinj hwinj hcne hdne hM hN
    hboundZ hboundW hRM hRN hrealZ hrealW hmomentZ hmomentW hi0 hj0
  have hobs : Tendsto
      (fun n : ℕ => Real.sqrt n *
        scaleCovariantBernsteinObservation m n R / (B ^ 2) ^ n)
      atTop (nhds L) := by
    apply hhalf.congr'
    filter_upwards with n
    rw [scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
      hc hboundZ hmomentZ hRpos n]
  exact ⟨B, L, hBz, hBz.trans hBzw, hB, hL, hobs⟩

/-- A source supported on the nonnegative real axis has subexponential scale-covariant square
energy at every exterior radius.  More precisely, normalization by every base greater than one
vanishes. -/
theorem tendsto_scaleCovariantBernsteinObservation_div_pow_of_positive_source
    {I : Type*} (c z : I → ℂ) (m : ℕ → ℝ)
    (hc : Summable c)
    {M R r : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, ‖z i‖ ≤ M)
    (hRM : M < R) (hr : 1 < r)
    (hpos : ∀ i, (0 : ℂ) ≤ z i)
    (hmoment : ∀ n, (m n : ℂ) = atomicPowerMoment c z n) :
    Tendsto
      (fun n : ℕ => scaleCovariantBernsteinObservation m n R / r ^ n)
      atTop (nhds 0) := by
  let u : I → ℂ := inverseScaleAtomicNode z R
  let A : ℝ := atomicWeightL1 c
  have hRpos : 0 < R := hM.trans_lt hRM
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hA : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hamp : ∀ i, atomicBernsteinAmplitude u i = 1 := by
    intro i
    have hzi := hpos i
    have him : (z i).im = 0 := hzi.2.symm
    have hre : 0 ≤ (z i).re := hzi.1
    have hreM : (z i).re ≤ M := (Complex.re_le_norm (z i)).trans (hbound i)
    have hRz : 0 ≤ R - (z i).re := by linarith
    have hdef : HTGeometry.confocalDefect R (z i) = 0 := by
      rw [HTGeometry.confocalDefect, Complex.norm_def, Complex.norm_def]
      simp [Complex.normSq_apply, him, hre, hRz]
    simp only [atomicBernsteinAmplitude, u, inverseScaleAtomicNode_eq_div]
    rw [HTGeometry.affineAmplitude_eq_one_add_confocalDefect_div hRpos, hdef]
    simp
  have hl1 : ∀ n : ℕ,
      finitePacketL1 (atomicBernsteinPacket c u) n ≤ A := by
    intro n
    have h := finitePacketL1_atomicBernsteinPacket_le hc
      (fun i => (hamp i).le) n
    simpa only [one_pow, mul_one, A] using h
  let q : ℝ := 1 / r
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    exact (div_lt_one hrpos).2 hr
  have hgeom := tendsto_natCast_add_one_mul_pow_nhds_zero hq0 hq1
  have hmajor : Tendsto
      (fun n : ℕ => A ^ 2 * ((n + 1 : ℝ) * q ^ n))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hgeom
  apply squeeze_zero
    (fun n => div_nonneg ?_ (pow_nonneg hrpos.le n))
    (fun n => ?_) hmajor
  · rw [scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
      hc hbound hmoment hRpos n, atomicBernsteinPacketSquareEnergy,
      ← finitePacketRpowEnergy_two_eq_squareEnergy]
    exact finitePacketRpowEnergy_nonneg _ 2 n
  · have hobs : scaleCovariantBernsteinObservation m n R =
        finitePacketRpowEnergy (atomicBernsteinPacket c u) 2 n := by
      rw [scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
        hc hbound hmoment hRpos n, atomicBernsteinPacketSquareEnergy,
        ← finitePacketRpowEnergy_two_eq_squareEnergy]
    have henergy := finitePacketRpowEnergy_le_card_mul_l1_rpow
      (atomicBernsteinPacket c u) (by norm_num : (0 : ℝ) < 2) n
    have hl1nonneg : 0 ≤ finitePacketL1 (atomicBernsteinPacket c u) n :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsquare : finitePacketL1 (atomicBernsteinPacket c u) n ^ (2 : ℕ) ≤ A ^ 2 := by
      nlinarith [hl1 n]
    have hupper : scaleCovariantBernsteinObservation m n R ≤
        (n + 1 : ℝ) * A ^ 2 := by
      rw [hobs]
      calc
        finitePacketRpowEnergy (atomicBernsteinPacket c u) 2 n ≤
            (n + 1 : ℝ) *
              finitePacketL1 (atomicBernsteinPacket c u) n ^ (2 : ℝ) := henergy
        _ = (n + 1 : ℝ) *
              finitePacketL1 (atomicBernsteinPacket c u) n ^ (2 : ℕ) := by
            rw [Real.rpow_two]
        _ ≤ (n + 1 : ℝ) * A ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare (by positivity)
    calc
      scaleCovariantBernsteinObservation m n R / r ^ n ≤
          ((n + 1 : ℝ) * A ^ 2) / r ^ n :=
        div_le_div_of_nonneg_right hupper (pow_nonneg hrpos.le n)
      _ = A ^ 2 * ((n + 1 : ℝ) * q ^ n) := by
        dsimp only [q]
        rw [one_div, inv_pow, div_eq_mul_inv]
        ring

/-- A nonnegative-real presentation and a transverse defect-neutral presentation cannot carry the
same real moment sequence.  The former has subexponential positive energy, while the latter has a
strictly superunit exact exponential exponent. -/
theorem no_common_pointed_moments_of_positive_and_transverse_presentations
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    (hwinj : Function.Injective w) (hdne : ∀ j, d j ≠ 0)
    {M N R : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hRM : M < R) (hRN : N < R)
    (hposZ : ∀ i, (0 : ℂ) ≤ z i)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m n : ℂ) = atomicPowerMoment d w n)
    {j0 : J} (hj0 : (w j0).im ≠ 0) : False := by
  have hRpos : 0 < R := hM.trans_lt hRM
  obtain ⟨D, B, beta, L, hBconf, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hLdef, hL, hhalf⟩ :=
    exists_positive_halfOrder_inverseScaleAtomicPacket_of_transverse_neutral
      d w hd htransW hwinj hdne hN hboundW hRN hrealW hj0
  let u : J → ℂ := inverseScaleAtomicNode w R
  let A : ℝ := atomicWeightL1 d
  have hA : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hamp : ∀ j, ‖u j‖ + ‖1 - u j‖ ≤ B := by
    intro j
    by_cases hj : j ∈ D
    · simpa only [u, atomicBernsteinAmplitude] using (hD j hj).le
    · exact (hDsub j hj).trans hbeta.le
  have hupper : ∀ n : ℕ,
      finitePacketL1 (atomicBernsteinPacket d u) n ≤ A * B ^ n := by
    intro n
    exact finitePacketL1_atomicBernsteinPacket_le hd hamp n
  have hhalf' : Tendsto
      (fun n : ℕ => Real.sqrt n *
        finitePacketRpowEnergy (atomicBernsteinPacket d u) 2 n / (B ^ 2) ^ n)
      atTop (nhds L) := by
    simpa only [finitePacketRpowEnergy_two_eq_squareEnergy,
      atomicBernsteinPacketSquareEnergy, u] using hhalf
  have hexact := finitePacketRpowEnergy_exactExponent_of_positive_square_halfOrder
    (atomicBernsteinPacket d u) (by norm_num : (0 : ℝ) < 2) hA
      (lt_trans zero_lt_one hB) hL hupper hhalf'
  let E : ℝ := B ^ (2 : ℝ)
  let r : ℝ := (1 + E) / 2
  have hE : 1 < E := by
    dsimp only [E]
    rw [Real.rpow_two]
    nlinarith
  have hr1 : 1 < r := by dsimp only [r]; linarith
  have hrE : r < E := by dsimp only [r]; linarith
  have hr0 : 0 < r := zero_lt_one.trans hr1
  have hdivW : Tendsto
      (fun n : ℕ => scaleCovariantBernsteinObservation m n R / r ^ n)
      atTop atTop := by
    have hdiv := hexact.2.2 r hr0 hrE
    apply hdiv.congr'
    filter_upwards with n
    rw [scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
      hd hboundW hmomentW hRpos n, atomicBernsteinPacketSquareEnergy,
      ← finitePacketRpowEnergy_two_eq_squareEnergy]
  have hzeroZ := tendsto_scaleCovariantBernsteinObservation_div_pow_of_positive_source
    c z m hc hM hboundZ hRM hr1 hposZ hmomentZ
  have hlarge : ∀ᶠ n : ℕ in atTop,
      1 < scaleCovariantBernsteinObservation m n R / r ^ n :=
    hdivW.eventually (eventually_gt_atTop 1)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      scaleCovariantBernsteinObservation m n R / r ^ n < 1 :=
    hzeroZ.eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨n, hnlarge, hnsmall⟩ := (hlarge.and hsmall).exists
  linarith

/-- **Universal admissible-stratum law.**  For two admissible presentations of the same real
moments at a common exterior scale, existence of an occupied transverse node is
presentation-independent.  Hence the radical/transverse alternative is intrinsic before the
finer confocal invariants are compared. -/
theorem transverse_occupied_iff_of_common_pointed_moments
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    (hzinj : Function.Injective z) (hwinj : Function.Injective w)
    (hcne : ∀ i, c i ≠ 0) (hdne : ∀ j, d j ≠ 0)
    {M N R : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hRM : M < R) (hRN : N < R)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m n : ℂ) = atomicPowerMoment d w n) :
    (∃ i, (z i).im ≠ 0) ↔ ∃ j, (w j).im ≠ 0 := by
  constructor
  · rintro ⟨i0, hi0⟩
    by_contra hnot
    push_neg at hnot
    have hposW : ∀ j, (0 : ℂ) ≤ w j := by
      intro j
      exact ⟨hrealW j (hnot j), (hnot j).symm⟩
    exact no_common_pointed_moments_of_positive_and_transverse_presentations
      d w c z m hd hc htransZ hzinj hcne hN hM hboundW hboundZ
      hRN hRM hposW hrealZ hmomentW hmomentZ hi0
  · rintro ⟨j0, hj0⟩
    by_contra hnot
    push_neg at hnot
    have hposZ : ∀ i, (0 : ℂ) ≤ z i := by
      intro i
      exact ⟨hrealZ i (hnot i), (hnot i).symm⟩
    exact no_common_pointed_moments_of_positive_and_transverse_presentations
      c z d w m hc hd htransW hwinj hdne hM hN hboundZ hboundW
      hRM hRN hposZ hrealW hmomentZ hmomentW hj0

/-- **Recession-level presentation rigidity.**  Under the same admissibility hypotheses, the
transverse-defect envelope is determined by the pointed real moment sequence.  This is the
first-order invariant obtained by letting the common selected confocal amplitude recede to the
boundary at infinity. -/
theorem transverseDefectEnvelope_eq_of_common_pointed_moments
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    (hzinj : Function.Injective z) (hwinj : Function.Injective w)
    (hcne : ∀ i, c i ≠ 0) (hdne : ∀ j, d j ≠ 0)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m n : ℂ) = atomicPowerMoment d w n)
    {i0 : I} (hi0 : (z i0).im ≠ 0)
    {j0 : J} (hj0 : (w j0).im ≠ 0) :
    HTGeometry.transverseDefectEnvelope (Set.range z) =
      HTGeometry.transverseDefectEnvelope (Set.range w) := by
  have hneZ : (Set.range z).Nonempty := ⟨z i0, ⟨i0, rfl⟩⟩
  have hneW : (Set.range w).Nonempty := ⟨w j0, ⟨j0, rfl⟩⟩
  have hlimZ := HTGeometry.tendsto_mul_confocalAmplitudeEnvelope_sq_sub_one
    hneZ hM (by rintro _ ⟨i, rfl⟩; exact hboundZ i)
  have hlimW := HTGeometry.tendsto_mul_confocalAmplitudeEnvelope_sq_sub_one
    hneW hN (by rintro _ ⟨j, rfl⟩; exact hboundW j)
  have heq :
      (fun R : ℝ => R *
        (HTGeometry.confocalAmplitudeEnvelope (Set.range z) R ^ 2 - 1)) =ᶠ[atTop]
      (fun R : ℝ => R *
        (HTGeometry.confocalAmplitudeEnvelope (Set.range w) R ^ 2 - 1)) := by
    filter_upwards [eventually_gt_atTop (max M N)] with R hR
    have hRM : M < R := (le_max_left M N).trans_lt hR
    have hRN : N < R := (le_max_right M N).trans_lt hR
    rw [confocalAmplitudeEnvelope_eq_of_common_pointed_moments
      c z d w m hc hd htransZ htransW hzinj hwinj hcne hdne hM hN
      hboundZ hboundW hRM hRN hrealZ hrealW hmomentZ hmomentW hi0 hj0]
  have hsame := hlimZ.congr' heq
  have htwice :
      2 * HTGeometry.transverseDefectEnvelope (Set.range z) =
        2 * HTGeometry.transverseDefectEnvelope (Set.range w) :=
    tendsto_nhds_unique hsame hlimW
  linarith

/-- **Raw-source presentation rigidity after canonical aggregation.**  Repeated nodes, zero
fibres, and fibrewise cancellations are allowed in both raw sources.  After passage to their
nonzero aggregate supports, common pointed real moments determine both the selected confocal
amplitude at every common admissible scale and the transverse-defect recession invariant. -/
theorem aggregatePresentationRigidity_of_common_pointed_moments
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    {M N R : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hRM : M < R) (hRN : N < R)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m n : ℂ) = atomicPowerMoment d w n)
    {u0 : AtomicAggregateSupport c z}
    (hu0 : (atomicAggregateNode c z u0).im ≠ 0)
    {v0 : AtomicAggregateSupport d w}
    (hv0 : (atomicAggregateNode d w v0).im ≠ 0) :
    HTGeometry.confocalAmplitudeEnvelope
          (Set.range (atomicAggregateNode c z)) R =
        HTGeometry.confocalAmplitudeEnvelope
          (Set.range (atomicAggregateNode d w)) R ∧
      HTGeometry.transverseDefectEnvelope
          (Set.range (atomicAggregateNode c z)) =
        HTGeometry.transverseDefectEnvelope
          (Set.range (atomicAggregateNode d w)) := by
  let cz := atomicAggregateCoefficient c z
  let zz := atomicAggregateNode c z
  let dw := atomicAggregateCoefficient d w
  let ww := atomicAggregateNode d w
  have hcz : Summable cz := summable_atomicAggregateCoefficient hc
  have hdw : Summable dw := summable_atomicAggregateCoefficient hd
  have htz : Tendsto (fun u => HTGeometry.transverseDefect (zz u))
      cofinite (nhds 0) :=
    tendsto_atomicAggregateNode_transverseDefect_cofinite_zero htransZ
  have htw : Tendsto (fun v => HTGeometry.transverseDefect (ww v))
      cofinite (nhds 0) :=
    tendsto_atomicAggregateNode_transverseDefect_cofinite_zero htransW
  have hbz : ∀ u, ‖zz u‖ ≤ M := norm_atomicAggregateNode_le hboundZ
  have hbw : ∀ v, ‖ww v‖ ≤ N := norm_atomicAggregateNode_le hboundW
  have hrz : ∀ u, (zz u).im = 0 → 0 ≤ (zz u).re :=
    atomicAggregateNode_re_nonneg_of_im_eq_zero hrealZ
  have hrw : ∀ v, (ww v).im = 0 → 0 ≤ (ww v).re :=
    atomicAggregateNode_re_nonneg_of_im_eq_zero hrealW
  have hmz : ∀ n, (m n : ℂ) = atomicPowerMoment cz zz n := by
    intro n
    exact (hmomentZ n).trans
      (atomicPowerMoment_eq_atomicAggregatePowerMoment hc hboundZ n)
  have hmw : ∀ n, (m n : ℂ) = atomicPowerMoment dw ww n := by
    intro n
    exact (hmomentW n).trans
      (atomicPowerMoment_eq_atomicAggregatePowerMoment hd hboundW n)
  constructor
  · exact confocalAmplitudeEnvelope_eq_of_common_pointed_moments
      cz zz dw ww m hcz hdw htz htw
      (atomicAggregateNode_injective c z) (atomicAggregateNode_injective d w)
      (atomicAggregateCoefficient_ne_zero c z) (atomicAggregateCoefficient_ne_zero d w)
      hM hN hbz hbw hRM hRN hrz hrw hmz hmw hu0 hv0
  · exact transverseDefectEnvelope_eq_of_common_pointed_moments
      cz zz dw ww m hcz hdw htz htw
      (atomicAggregateNode_injective c z) (atomicAggregateNode_injective d w)
      (atomicAggregateCoefficient_ne_zero c z) (atomicAggregateCoefficient_ne_zero d w)
      hM hN hbz hbw hrz hrw hmz hmw hu0 hv0

/-- **Complete admissible moment-fibre classification after aggregation.**  For arbitrary raw
presentations with repeated nodes and fibrewise cancellations, the common pointed moments first
decide whether the intrinsic occupied support lies in the nonnegative-real radical or in the
transverse stratum.  At every common exterior scale they then determine the confocal amplitude,
and globally they determine the transverse-defect envelope.  No transversality assumption is
needed in the conclusion: in the radical stratum both invariants are exactly `1` and `0`. -/
theorem aggregatePresentationFullRigidity_of_common_pointed_moments
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    {M N R : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hRM : M < R) (hRN : N < R)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m n : ℂ) = atomicPowerMoment d w n)
    (hm0 : 0 < m 0) :
    ((∃ u : AtomicAggregateSupport c z,
        (atomicAggregateNode c z u).im ≠ 0) ↔
      ∃ v : AtomicAggregateSupport d w,
        (atomicAggregateNode d w v).im ≠ 0) ∧
      HTGeometry.confocalAmplitudeEnvelope
          (Set.range (atomicAggregateNode c z)) R =
        HTGeometry.confocalAmplitudeEnvelope
          (Set.range (atomicAggregateNode d w)) R ∧
      HTGeometry.transverseDefectEnvelope
          (Set.range (atomicAggregateNode c z)) =
        HTGeometry.transverseDefectEnvelope
          (Set.range (atomicAggregateNode d w)) := by
  classical
  let cz := atomicAggregateCoefficient c z
  let zz := atomicAggregateNode c z
  let dw := atomicAggregateCoefficient d w
  let ww := atomicAggregateNode d w
  letI : Nonempty (AtomicAggregateSupport c z) :=
    nonempty_atomicAggregateSupport_of_positive_real_moment
      hc hboundZ hmomentZ hm0
  letI : Nonempty (AtomicAggregateSupport d w) :=
    nonempty_atomicAggregateSupport_of_positive_real_moment
      hd hboundW hmomentW hm0
  have hcz : Summable cz := summable_atomicAggregateCoefficient hc
  have hdw : Summable dw := summable_atomicAggregateCoefficient hd
  have htz : Tendsto (fun u => HTGeometry.transverseDefect (zz u))
      cofinite (nhds 0) :=
    tendsto_atomicAggregateNode_transverseDefect_cofinite_zero htransZ
  have htw : Tendsto (fun v => HTGeometry.transverseDefect (ww v))
      cofinite (nhds 0) :=
    tendsto_atomicAggregateNode_transverseDefect_cofinite_zero htransW
  have hbz : ∀ u, ‖zz u‖ ≤ M := norm_atomicAggregateNode_le hboundZ
  have hbw : ∀ v, ‖ww v‖ ≤ N := norm_atomicAggregateNode_le hboundW
  have hrz : ∀ u, (zz u).im = 0 → 0 ≤ (zz u).re :=
    atomicAggregateNode_re_nonneg_of_im_eq_zero hrealZ
  have hrw : ∀ v, (ww v).im = 0 → 0 ≤ (ww v).re :=
    atomicAggregateNode_re_nonneg_of_im_eq_zero hrealW
  have hmz : ∀ n, (m n : ℂ) = atomicPowerMoment cz zz n := by
    intro n
    exact (hmomentZ n).trans
      (atomicPowerMoment_eq_atomicAggregatePowerMoment hc hboundZ n)
  have hmw : ∀ n, (m n : ℂ) = atomicPowerMoment dw ww n := by
    intro n
    exact (hmomentW n).trans
      (atomicPowerMoment_eq_atomicAggregatePowerMoment hd hboundW n)
  have hstratum : (∃ u, (zz u).im ≠ 0) ↔ ∃ v, (ww v).im ≠ 0 :=
    transverse_occupied_iff_of_common_pointed_moments
      cz zz dw ww m hcz hdw htz htw
      (atomicAggregateNode_injective c z) (atomicAggregateNode_injective d w)
      (atomicAggregateCoefficient_ne_zero c z) (atomicAggregateCoefficient_ne_zero d w)
      hM hN hbz hbw hRM hRN hrz hrw hmz hmw
  change ((∃ u, (zz u).im ≠ 0) ↔ ∃ v, (ww v).im ≠ 0) ∧
    HTGeometry.confocalAmplitudeEnvelope (Set.range zz) R =
      HTGeometry.confocalAmplitudeEnvelope (Set.range ww) R ∧
    HTGeometry.transverseDefectEnvelope (Set.range zz) =
      HTGeometry.transverseDefectEnvelope (Set.range ww)
  refine ⟨hstratum, ?_⟩
  by_cases hoccZ : ∃ u, (zz u).im ≠ 0
  · obtain ⟨u0, hu0⟩ := hoccZ
    obtain ⟨v0, hv0⟩ := hstratum.mp ⟨u0, hu0⟩
    exact aggregatePresentationRigidity_of_common_pointed_moments
      c z d w m hc hd htransZ htransW hM hN hboundZ hboundW hRM hRN
      hrealZ hrealW hmomentZ hmomentW hu0 hv0
  · have hoccW : ¬ ∃ v, (ww v).im ≠ 0 := by
      intro hw
      exact hoccZ (hstratum.mpr hw)
    have hposZ : ∀ u, (0 : ℂ) ≤ zz u := by
      intro u
      have him : (zz u).im = 0 := by
        by_contra hu
        exact hoccZ ⟨u, hu⟩
      exact ⟨hrz u him, him.symm⟩
    have hposW : ∀ v, (0 : ℂ) ≤ ww v := by
      intro v
      have him : (ww v).im = 0 := by
        by_contra hv
        exact hoccW ⟨v, hv⟩
      exact ⟨hrw v him, him.symm⟩
    have hneZ : (Set.range zz).Nonempty := Set.range_nonempty zz
    have hneW : (Set.range ww).Nonempty := Set.range_nonempty ww
    have hbzSet : ∀ q ∈ Set.range zz, ‖q‖ ≤ M := by
      rintro _ ⟨u, rfl⟩
      exact hbz u
    have hbwSet : ∀ q ∈ Set.range ww, ‖q‖ ≤ N := by
      rintro _ ⟨v, rfl⟩
      exact hbw v
    have hzeroZ : HTGeometry.transverseDefectEnvelope (Set.range zz) = 0 :=
      (HTGeometry.transverseDefectEnvelope_eq_zero_iff hneZ hbzSet).mpr
        (by rintro _ ⟨u, rfl⟩; exact hposZ u)
    have hzeroW : HTGeometry.transverseDefectEnvelope (Set.range ww) = 0 :=
      (HTGeometry.transverseDefectEnvelope_eq_zero_iff hneW hbwSet).mpr
        (by rintro _ ⟨v, rfl⟩; exact hposW v)
    constructor
    · rw [(HTGeometry.confocalAmplitudeEnvelope_eq_one_iff
          hneZ hM hRM hbzSet).mpr hzeroZ,
        (HTGeometry.confocalAmplitudeEnvelope_eq_one_iff
          hneW hN hRN hbwSet).mpr hzeroW]
    · rw [hzeroZ, hzeroW]

end

end RHTower
