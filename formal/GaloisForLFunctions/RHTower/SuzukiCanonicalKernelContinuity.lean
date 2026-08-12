import GaloisForLFunctions.RHTower.SuzukiCanonicalCompressedHankel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of Suzuki's literal arithmetic kernel

Suzuki's Lemma 4.5 uses the pointwise assertion that `h_omega` is continuous when
`omega > 1`.  This module proves that assertion for the literal incomplete-beta and
floor-truncated kernels.  The key endpoint is `g_omega(1) = 0`: it makes every new
arithmetic summand enter continuously when the floor in equation (204) jumps.
-/

open ArithmeticFunction Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

set_option maxHeartbeats 1000000

private def suzukiBetaIntegrand (omega : ℝ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ ((1 / 2 - omega : ℝ) : ℂ) *
    (1 - (t : ℂ)) ^ ((omega : ℂ) - 1)

/-- The literal incomplete-beta tail varies continuously with its lower endpoint on every
compact subinterval separated from zero. -/
theorem continuousOn_suzukiBetaTail_Icc
    {omega delta : ℝ} (homega : 0 < omega) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ContinuousOn (suzukiBetaTail omega) (Icc delta 1) := by
  let F := suzukiBetaIntegrand omega
  have hFoc : IntegrableOn F (Ioc (delta ^ 2) 1) := by
    exact integrableOn_suzukiBetaIntegrand_Ioc homega hdelta hdelta1
  have hFcc : IntegrableOn F (Icc (delta ^ 2) 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr hFoc
  have htail : ContinuousOn (fun u : ℝ => ∫ t in u..1, F t) (Icc (delta ^ 2) 1) := by
    have hsq1 : delta ^ 2 ≤ 1 := by nlinarith
    have hFu : IntegrableOn F (uIcc (delta ^ 2) 1) := by
      simpa only [uIcc_of_le hsq1] using hFcc
    simpa only [uIcc_of_le hsq1] using
      intervalIntegral.continuousOn_primitive_interval_left hFu
  have hsq : MapsTo (fun x : ℝ => x ^ 2) (Icc delta 1) (Icc (delta ^ 2) 1) := by
    intro x hx
    constructor <;> nlinarith [hx.1, hx.2, hdelta]
  have hcomp : ContinuousOn (fun x : ℝ => ∫ t in x ^ 2..1, F t) (Icc delta 1) :=
    htail.comp (continuous_pow 2).continuousOn hsq
  refine hcomp.congr ?_
  intro x hx
  rw [suzukiBetaTail]
  change (∫ t in Ioc (x ^ 2) 1, F t) = ∫ t in x ^ 2..1, F t
  have hx0 : 0 ≤ x := le_trans hdelta.le hx.1
  have hsq : x ^ 2 ≤ (1 : ℝ) ^ 2 := (sq_le_sq₀ hx0 zero_le_one).2 hx.2
  simpa only [one_pow] using (intervalIntegral.integral_of_le hsq).symm

private def suzukiSourceGContinuousFormula (omega : ℝ) (x : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) ^ (omega : ℂ) /
      Complex.Gamma (omega : ℂ)) *
    ((((x ^ (2 - omega : ℝ) : ℝ) : ℂ) *
        (((1 - x ^ 2) ^ (omega - 1 : ℝ) : ℝ) : ℂ)) -
      (omega : ℂ) * (((x ^ (omega - 1 : ℝ) : ℝ) : ℂ)) *
        suzukiBetaTail omega x)

private theorem continuousOn_suzukiSourceGContinuousFormula
    {omega delta : ℝ} (homega : 1 < omega) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ContinuousOn (suzukiSourceGContinuousFormula omega) (Icc delta 1) := by
  have hxpow : ContinuousOn (fun x : ℝ => x ^ (2 - omega : ℝ)) (Icc delta 1) :=
    continuousOn_id.rpow_const (fun x hx =>
      Or.inl (ne_of_gt (lt_of_lt_of_le hdelta hx.1)))
  have honepow : Continuous (fun x : ℝ => (1 - x ^ 2) ^ (omega - 1 : ℝ)) :=
    (Real.continuous_rpow_const (by linarith)).comp
      (continuous_const.sub (continuous_pow 2))
  have homegapow : ContinuousOn (fun x : ℝ => x ^ (omega - 1 : ℝ)) (Icc delta 1) :=
    continuousOn_id.rpow_const (fun _ _ => Or.inr (by linarith))
  have hbeta := continuousOn_suzukiBetaTail_Icc (omega := omega) (delta := delta)
    (by linarith) hdelta hdelta1
  exact continuousOn_const.mul
    (((Complex.continuous_ofReal.comp_continuousOn hxpow).mul
        (Complex.continuous_ofReal.comp honepow).continuousOn).sub
      ((continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn homegapow)).mul hbeta))

private theorem suzukiSourceG_eq_continuousFormula
    {omega delta x : ℝ} (homega : 1 < omega) (hdelta : 0 < delta)
    (hx : x ∈ Icc delta 1) :
    suzukiSourceG omega x = suzukiSourceGContinuousFormula omega x := by
  have hx0 : 0 < x := lt_of_lt_of_le hdelta hx.1
  rcases hx.2.eq_or_lt with rfl | hx1
  · rw [suzukiSourceG, if_neg (by simp), suzukiSourceGContinuousFormula,
      suzukiBetaTail]
    simp [Real.zero_rpow (by linarith : omega - 1 ≠ 0)]
  · rw [suzukiSourceG, if_pos ⟨hx0, hx1⟩, suzukiSourceGContinuousFormula]
    have hbase : 0 ≤ 1 - x ^ 2 := by nlinarith
    rw [← Complex.ofReal_cpow hx0.le (2 - omega),
      ← Complex.ofReal_one, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
      ← Complex.ofReal_cpow hx0.le (omega - 1)]
    have hone : ((omega : ℂ) - ((1 : ℝ) : ℂ)) =
        ((omega - 1 : ℝ) : ℂ) := by rw [← Complex.ofReal_sub]
    rw [hone, ← Complex.ofReal_cpow hbase (omega - 1)]

/-- Suzuki's literal `g_omega`, including its totalized value at `1`, is continuous from the
left up to `1` when `omega > 1`. -/
theorem continuousOn_suzukiSourceG_Icc_one
    {omega delta : ℝ} (homega : 1 < omega) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ContinuousOn (suzukiSourceG omega) (Icc delta 1) := by
  exact (continuousOn_suzukiSourceGContinuousFormula homega hdelta hdelta1).congr
    (fun x hx => suzukiSourceG_eq_continuousFormula homega hdelta hx)

/-- For `omega > 1`, Suzuki's literal incomplete-beta kernel is continuous at every positive
argument, including the support endpoint `1`. -/
theorem continuousAt_suzukiSourceG
    {omega x : ℝ} (homega : 1 < omega) (hx0 : 0 < x) :
    ContinuousAt (suzukiSourceG omega) x := by
  rcases lt_trichotomy x 1 with hx1 | rfl | hx1
  · let delta := x / 2
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have hxdelta : delta < x := by dsimp [delta]; linarith
    have hcont := continuousOn_suzukiSourceG_Icc_one homega hdelta (by
      dsimp [delta]
      linarith)
    exact (hcont x ⟨hxdelta.le, hx1.le⟩).continuousAt
      (Icc_mem_nhds hxdelta hx1)
  · apply continuousAt_iff_continuous_left_right.mpr
    let delta : ℝ := 1 / 2
    have hdelta : 0 < delta := by norm_num [delta]
    have hdelta1 : delta < 1 := by norm_num [delta]
    have hleftLocal :=
      (continuousOn_suzukiSourceG_Icc_one homega hdelta hdelta1) 1
        ⟨hdelta1.le, le_rfl⟩
    have hmem : Icc delta 1 ∈ 𝓝[Iic (1 : ℝ)] 1 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hdelta1),
        self_mem_nhdsWithin] with z hz hzone
      exact ⟨hz.le, hzone⟩
    refine ⟨hleftLocal.mono_of_mem_nhdsWithin hmem, ?_⟩
    have hconst : ContinuousWithinAt (fun _ : ℝ => (0 : ℂ)) (Ici 1) 1 :=
      continuousWithinAt_const
    refine hconst.congr ?_ ?_
    · intro z hz
      rw [suzukiSourceG, if_neg]
      exact fun h => (not_lt_of_ge hz) h.2
    · simp [suzukiSourceG]
  · have hev : suzukiSourceG omega =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hx1] with z hz
      rw [suzukiSourceG, if_neg]
      exact fun h => (not_lt_of_ge hz.le) h.2
    have hconst : ContinuousAt (fun _ : ℝ => (0 : ℂ)) x := continuousAt_const
    exact hconst.congr_of_eventuallyEq hev

/-- The literal kernel `g_omega` is continuous on the positive half-line for `omega > 1`. -/
theorem continuousOn_suzukiSourceG_Ioi
    {omega : ℝ} (homega : 1 < omega) :
    ContinuousOn (suzukiSourceG omega) (Ioi 0) :=
  fun x hx => (continuousAt_suzukiSourceG (x := x) homega hx).continuousWithinAt

private theorem suzukiSourceG_eq_zero_of_one_le
    (omega : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    suzukiSourceG omega x = 0 := by
  rw [suzukiSourceG, if_neg]
  exact fun h => (not_lt_of_ge hx) h.2

/-- A fixed finite sum represents the floor-truncated arithmetic kernel whenever its cutoff is
at least the current floor.  Terms beyond the floor vanish because `g_omega` is supported in
`(0,1)`. -/
theorem suzukiSourceHFinite_eq_fixedSum
    {omega x : ℝ} {N : ℕ} (hx0 : 0 < x) (hN : ⌊x⌋₊ ≤ N) :
    suzukiSourceHFinite omega x =
      (1 / (x : ℂ)) * ∑ n ∈ Finset.Icc 1 N,
        ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
          suzukiSourceG omega (n / x) := by
  by_cases hx1 : 1 < x
  · rw [suzukiSourceHFinite, if_pos hx1]
    congr 1
    apply Finset.sum_subset
    · exact Finset.Icc_subset_Icc_right hN
    · intro n hnBig hnSmall
      have hnFloor : ⌊x⌋₊ < n := by
        have hnOne : 1 ≤ n := (Finset.mem_Icc.mp hnBig).1
        simpa only [Finset.mem_Icc, hnOne, true_and, not_le] using hnSmall
      have hxn : x < n := by
        calc
          x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
          _ ≤ n := by exact_mod_cast Nat.succ_le_iff.mpr hnFloor
      rw [suzukiSourceG_eq_zero_of_one_le omega]
      · simp
      · apply (le_div_iff₀ hx0).2
        simpa only [one_mul] using hxn.le
  · rw [suzukiSourceHFinite, if_neg hx1]
    have hzero : (∑ n ∈ Finset.Icc 1 N,
        ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
          suzukiSourceG omega (n / x)) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [suzukiSourceG_eq_zero_of_one_le omega]
      · simp
      · have hnOne : (1 : ℝ) ≤ n := by
          exact_mod_cast (Finset.mem_Icc.mp hn).1
        apply (le_div_iff₀ hx0).2
        simpa only [one_mul] using (le_trans (le_of_not_gt hx1) hnOne)
    rw [hzero, mul_zero]

/-- For `omega > 1`, Suzuki's literal floor-truncated arithmetic kernel `h_omega` is continuous
at every positive argument.  Continuity at integer breakpoints follows from `g_omega(1)=0`. -/
theorem continuousAt_suzukiSourceHFinite
    {omega x : ℝ} (homega : 1 < omega) (hx0 : 0 < x) :
    ContinuousAt (suzukiSourceHFinite omega) x := by
  let B := x + 1
  let N := ⌊B⌋₊
  let fixed : ℝ → ℂ := fun z =>
    (1 / (z : ℂ)) * ∑ n ∈ Finset.Icc 1 N,
      ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
        suzukiSourceG omega (n / z)
  have hfixed : ContinuousAt fixed x := by
    have hsum : ContinuousAt (fun z : ℝ => ∑ n ∈ Finset.Icc 1 N,
        ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
          suzukiSourceG omega (n / z)) x := by
      apply tendsto_finsetSum
      intro n hn
      have hnOne : (1 : ℝ) ≤ n := by
        exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hratio0 : 0 < (n : ℝ) / x :=
        div_pos (lt_of_lt_of_le zero_lt_one hnOne) hx0
      exact continuousAt_const.mul
        ((continuousAt_suzukiSourceG homega hratio0).comp
          (continuousAt_const.div continuousAt_id hx0.ne'))
    exact (continuousAt_const.div
      Complex.continuous_ofReal.continuousAt
      (Complex.ofReal_ne_zero.mpr hx0.ne')).mul hsum
  have hev : suzukiSourceHFinite omega =ᶠ[𝓝 x] fixed := by
    have hB : x < B := by dsimp [B]; linarith
    filter_upwards [Ioi_mem_nhds hx0, Iio_mem_nhds hB] with z hz0 hzB
    apply suzukiSourceHFinite_eq_fixedSum hz0
    dsimp only [N]
    exact Nat.floor_mono hzB.le
  exact hfixed.congr_of_eventuallyEq hev

/-- Suzuki's literal arithmetic kernel is continuous on `(0,∞)` for `omega > 1`. -/
theorem continuousOn_suzukiSourceHFinite_Ioi
    {omega : ℝ} (homega : 1 < omega) :
    ContinuousOn (suzukiSourceHFinite omega) (Ioi 0) :=
  fun x hx => (continuousAt_suzukiSourceHFinite (x := x) homega hx).continuousWithinAt

end RHTower
