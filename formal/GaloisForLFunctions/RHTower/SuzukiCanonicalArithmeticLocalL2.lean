import GaloisForLFunctions.RHTower.SuzukiCanonicalKernelLocalL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Local `L²` regularity of Suzuki's arithmetic Hankel kernel

This file propagates the sharp local `L²` theorem for Suzuki's literal beta kernel through every
inverse Mellin dilation in equation (204), then through the locally finite arithmetic sum.  The
change of variables is the source substitution `u = n / x`, with its exact Jacobian `n / x²`.
-/

open ArithmeticFunction Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- Exact inverse-dilation transport of the sharp local `L²` theorem. -/
theorem intervalIntegrable_sq_norm_inverseMellinDilate_suzukiSourceG
    {omega : ℝ} (homega : 1 / 2 < omega) {n : ℕ} (hn : 0 < n)
    {a : ℝ} (hna : (n : ℝ) < a) :
    IntervalIntegrable (fun x : ℝ =>
      ‖inverseMellinDilate (suzukiSourceG omega) n x‖ ^ 2) volume n a := by
  let phi : ℝ → ℝ := (fun _x : ℝ => (n : ℝ)) / id
  let dphi : ℝ → ℝ := fun x => -(n : ℝ) / x ^ 2
  let q : ℝ → ℝ := fun u => ‖suzukiSourceG omega u‖ ^ 2
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdelta : 0 < (n : ℝ) / a := div_pos hnR (lt_trans hnR hna)
  have hdelta1 : (n : ℝ) / a < 1 := (div_lt_one (lt_trans hnR hna)).2 hna
  have hG := memLp_suzukiSourceG_local_two homega hdelta hdelta1
  have hqI : IntegrableOn q (Ioc ((n : ℝ) / a) 1) :=
    (memLp_two_iff_integrable_sq_norm
      (measurable_suzukiSourceG omega).aestronglyMeasurable).mp hG
  have hqInt : IntervalIntegrable q volume ((n : ℝ) / a) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hdelta1.le).mpr hqI
  have hphiCont : ContinuousOn phi (uIcc (n : ℝ) a) := by
    refine continuousOn_of_forall_continuousAt fun x hx => ?_
    exact continuousAt_const.div continuousAt_id
      (ne_of_gt (lt_of_lt_of_le hnR (uIcc_of_le hna.le ▸ hx).1))
  have hderiv : ∀ x ∈ Ioo (n : ℝ) a, HasDerivAt phi (dphi x) x := by
    intro x hx
    dsimp only [dphi]
    have h := (hasDerivAt_const x (n : ℝ)).div (hasDerivAt_id x)
      (ne_of_gt (lt_trans hnR hx.1))
    simpa only [phi, zero_mul, mul_one, zero_sub, id_eq] using h
  have hdnonpos : ∀ x ∈ Ioo (n : ℝ) a, dphi x ≤ 0 := by
    intro x _hx
    dsimp only [dphi]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnR.le) (sq_nonneg x)
  have hcomp : IntervalIntegrable (fun x => (q ∘ phi) x * dphi x)
      volume n a := by
    apply (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
      hphiCont (by simpa [min_eq_left hna.le, max_eq_right hna.le] using hderiv)
      (by simpa [min_eq_left hna.le, max_eq_right hna.le] using hdnonpos)).2
    simpa [phi, hnR.ne'] using hqInt.symm
  have hscaled := hcomp.const_mul (-(1 / (n : ℝ)))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hna.le] at hscaled ⊢
  refine hscaled.congr_fun ?_ measurableSet_Ioc
  intro x hx
  have hx0 : 0 < x := lt_trans hnR hx.1
  dsimp only [q, phi, dphi, Function.comp_apply, Pi.div_apply, id_eq]
  rw [inverseMellinDilate, norm_div, norm_real, Real.norm_of_nonneg hx0.le]
  field_simp

/-- Every positive arithmetic inverse dilation belongs to `L²((1,a),dx)`.  When `n ≥ a`, its
source kernel vanishes identically on the interval; when `n < a`, the preceding exact substitution
applies. -/
theorem memLp_inverseMellinDilate_suzukiSourceG_local_two
    {omega : ℝ} (homega : 1 / 2 < omega) {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : 1 < a) :
    MemLp (inverseMellinDilate (suzukiSourceG omega) n) 2
      (volume.restrict (Ioc 1 a)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmeas : Measurable (inverseMellinDilate (suzukiSourceG omega) n) := by
    have harg : Measurable fun x : ℝ => (n : ℝ) / x := by fun_prop
    exact ((measurable_suzukiSourceG omega).comp harg).div (by fun_prop)
  have hzero (b : ℝ) (h1b : 1 ≤ b) (hb : b ≤ n) :
      IntervalIntegrable (fun x : ℝ =>
        ‖inverseMellinDilate (suzukiSourceG omega) n x‖ ^ 2) volume 1 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h1b]
    refine integrableOn_zero.congr_fun ?_ measurableSet_Ioc
    intro x hx
    have hxb : x ≤ n := le_trans hx.2 hb
    change 0 = ‖suzukiSourceG omega ((n : ℝ) / x) / x‖ ^ 2
    by_cases hx0 : x ≤ 0
    · have harg : (n : ℝ) / x ≤ 0 := div_nonpos_of_nonneg_of_nonpos hnR.le hx0
      rw [suzukiSourceG_eq_zero_of_nonpos omega harg]
      simp
    · have hxpos : 0 < x := lt_of_not_ge hx0
      have hratio : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hxpos).2 (by simpa using hxb)
      rw [suzukiSourceG, if_neg]
      · simp
      · exact fun h => (not_lt_of_ge hratio) h.2
  have hint : IntervalIntegrable (fun x : ℝ =>
      ‖inverseMellinDilate (suzukiSourceG omega) n x‖ ^ 2) volume 1 a := by
    by_cases hlt : (n : ℝ) < a
    · exact (hzero n hn1 le_rfl).trans
        (intervalIntegrable_sq_norm_inverseMellinDilate_suzukiSourceG homega hn hlt)
    · exact hzero a ha.le (le_of_not_gt hlt)
  exact (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp hint)

/-- Suzuki's arithmetic source kernel is measurable directly from its locally finite series model. -/
theorem measurable_suzukiSourceH (omega : ℝ) : Measurable (suzukiSourceH omega) := by
  rw [suzukiSourceH]
  unfold suzukiArithmeticH
  apply Measurable.tsum
  intro n
  have harg : Measurable fun x : ℝ => (n : ℝ) / x := by fun_prop
  have hinv : Measurable (inverseMellinDilate (suzukiSourceG omega) n) :=
    ((measurable_suzukiSourceG omega).comp harg).div (by fun_prop)
  exact measurable_const.mul hinv

/-- **Sharp local `L²` theorem for Suzuki's full arithmetic kernel `h_ω`.**  On every bounded
interval, the infinite series reduces to one fixed finite sum of inverse dilations, so no
summability premise is needed. -/
theorem memLp_suzukiSourceH_local_two
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a) :
    MemLp (suzukiSourceH omega) 2 (volume.restrict (Ioc 1 a)) := by
  let S : Finset ℕ := Finset.Icc 1 ⌊a⌋₊
  let F : ℕ → ℝ → ℂ := fun n x =>
    ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
      inverseMellinDilate (suzukiSourceG omega) n x
  have hF : ∀ n ∈ S, MemLp (F n) 2 (volume.restrict (Ioc 1 a)) := by
    intro n hnS
    have hn : 0 < n := by
      dsimp only [S] at hnS
      exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnS).1
    exact (memLp_inverseMellinDilate_suzukiSourceG_local_two homega hn ha).const_mul
      (((suzukiShiftedCoefficient omega n : ℝ) : ℂ))
  have hsum : MemLp (fun x => ∑ n ∈ S, F n x) 2
      (volume.restrict (Ioc 1 a)) := memLp_finsetSum S hF
  refine hsum.congr_norm (measurable_suzukiSourceH omega).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  congr 1
  rw [suzukiSourceH]
  unfold suzukiArithmeticH
  rw [tsum_eq_sum (s := S)]
  intro n hnS
  dsimp only [S] at hnS
  simp only [Finset.mem_Icc, not_and_or, not_le] at hnS
  rcases hnS with hnzero | hnlarge
  · have hn0 : n = 0 := by omega
    subst n
    rw [inverseMellinDilate, suzukiSourceG_eq_zero_of_nonpos omega (by norm_num)]
    simp
  · have halt : a < (n : ℝ) :=
      (Nat.floor_lt (le_trans zero_le_one ha.le)).mp hnlarge
    have hx0 : 0 < x := lt_trans zero_lt_one hx.1
    have hxlt : x < (n : ℝ) := lt_of_le_of_lt hx.2 halt
    have hratio : 1 < (n : ℝ) / x := (one_lt_div hx0).2 hxlt
    have hg : suzukiSourceG omega ((n : ℝ) / x) = 0 := by
      rw [suzukiSourceG, if_neg]
      exact fun h => (not_lt_of_ge hratio.le) h.2
    rw [inverseMellinDilate, hg]
    simp

/-- The same sharp local `L²` theorem for Suzuki's literal floor-truncated equation (204). -/
theorem memLp_suzukiSourceHFinite_local_two
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a) :
    MemLp (suzukiSourceHFinite omega) 2 (volume.restrict (Ioc 1 a)) := by
  have heq : suzukiSourceHFinite omega = suzukiSourceH omega := by
    funext x
    exact (suzukiSourceH_eq_finite omega x).symm
  rw [heq]
  exact memLp_suzukiSourceH_local_two homega ha

end RHTower

