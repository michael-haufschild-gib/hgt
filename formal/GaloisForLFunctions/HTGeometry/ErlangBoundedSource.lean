import GaloisForLFunctions.HTGeometry.ErlangWignerSmithPacket

/-!
# Bounded first-order sources are Erlang-recovery admissible

The half-line Erlang recovery identities are stated for sources satisfying a seventeen-field
analytic admissibility bundle: integrability of the three normalized Erlang kernels against the
source and its derivative, the boundary limits at both ends of the half line, and differentiation
under the integral for the three Erlang averages.

Every source with a globally bounded derivative satisfies all of it.  The three kernels are
`s ^ k · exp (-s / ε)` up to a normalizing constant, so integrability is a Gamma moment, the
boundary limit at `0` is continuity, the boundary limit at `∞` is exponential decay against a
bounded source, and differentiation under the integral is dominated by the kernel times the
derivative bound.  The sine source is an explicit instance, which makes the third-order recovery
identity `(1 - εD)³ R = f` unconditional.
-/

open Filter MeasureTheory Real Set
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Normalized Erlang kernel of order `k + 1`: `s ^ k · exp (-s / ε) / c`. -/
def erlangPowKernel (ε : ℝ) (k : ℕ) (c s : ℝ) : ℝ :=
  s ^ k * Real.exp (-s / ε) / c

theorem erlangOneKernel_eq_powKernel (ε s : ℝ) :
    erlangOneKernel ε s = erlangPowKernel ε 0 ε s := by
  simp [erlangOneKernel, erlangPowKernel]

theorem erlangTwoKernel_eq_powKernel (ε s : ℝ) :
    erlangTwoKernel ε s = erlangPowKernel ε 1 (ε ^ 2) s := by
  simp [erlangTwoKernel, erlangPowKernel]

theorem erlangThreeKernel_eq_powKernel (ε s : ℝ) :
    erlangThreeKernel ε s = erlangPowKernel ε 2 (2 * ε ^ 3) s := by
  simp [erlangThreeKernel, erlangPowKernel]

theorem continuous_erlangPowKernel (ε : ℝ) (k : ℕ) (c : ℝ) :
    Continuous (erlangPowKernel ε k c) := by
  unfold erlangPowKernel
  fun_prop

theorem erlangPowKernel_nonneg {ε c : ℝ} (hc : 0 < c) (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ erlangPowKernel ε k c s :=
  div_nonneg (mul_nonneg (pow_nonneg hs k) (Real.exp_pos _).le) hc.le

/-- Every normalized Erlang kernel is a convergent Gamma moment on the half line. -/
theorem integrableOn_erlangPowKernel {ε : ℝ} (hε : 0 < ε) (k : ℕ) (c : ℝ) :
    IntegrableOn (erlangPowKernel ε k c) (Ioi 0) := by
  have hmoment : IntegrableOn
      (fun s : ℝ => s ^ k * Real.exp (-ε⁻¹ * s)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (k : ℝ)) (b := ε⁻¹)
      (by have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith)
      le_rfl (inv_pos.mpr hε)
    apply h.congr_fun _ measurableSet_Ioi
    intro s _
    simp [Real.rpow_one, Real.rpow_natCast]
  have hscaled : IntegrableOn
      (fun s : ℝ => 1 / c * (s ^ k * Real.exp (-ε⁻¹ * s))) (Ioi 0) :=
    hmoment.const_mul (1 / c)
  apply hscaled.congr_fun _ measurableSet_Ioi
  intro s _
  unfold erlangPowKernel
  rw [show -s / ε = -ε⁻¹ * s by field_simp]
  ring

/-- A bounded measurable source is integrable against every normalized Erlang kernel. -/
theorem integrableOn_erlangPowKernel_mul {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (k : ℕ)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ y, |g y| ≤ M) (x : ℝ) :
    IntegrableOn (fun s => erlangPowKernel ε k c s * g (x + s)) (Ioi 0) := by
  have hbound : IntegrableOn
      (fun s => M * erlangPowKernel ε k c s) (Ioi 0) :=
    (integrableOn_erlangPowKernel hε k c).const_mul M
  refine hbound.mono' ?_ ?_
  · exact (((continuous_erlangPowKernel ε k c).measurable).mul
      (hg.comp (measurable_const_add x))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hk : 0 ≤ erlangPowKernel ε k c s :=
      erlangPowKernel_nonneg hc k (le_of_lt hs)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM _) hk

/-- Exponential decay of every normalized Erlang kernel. -/
theorem tendsto_erlangPowKernel_atTop {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    Tendsto (fun s : ℝ => s ^ k * Real.exp (-s / ε)) atTop (𝓝 0) := by
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  have hdiv : Tendsto (fun s : ℝ => s / ε) atTop atTop :=
    Filter.Tendsto.atTop_div_const hε tendsto_id
  have hscale := (hbase.comp hdiv).const_mul (ε ^ k)
  rw [mul_zero] at hscale
  apply hscale.congr
  intro s
  simp only [Function.comp_apply]
  rw [div_pow, ← mul_assoc, show -(s / ε) = -s / ε by ring]
  field_simp

/-- At the far end of the half line every kernel average of a bounded source vanishes. -/
theorem tendsto_erlangPowKernel_mul_atTop {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (k : ℕ)
    {g : ℝ → ℝ} {M : ℝ} (hM : ∀ y, |g y| ≤ M) (x : ℝ) :
    Tendsto (fun s => erlangPowKernel ε k c s * g (x + s)) atTop (𝓝 0) := by
  have hker := (tendsto_erlangPowKernel_atTop hε k).const_mul (M / c)
  rw [mul_zero] at hker
  apply squeeze_zero_norm' _ hker
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  have hk : 0 ≤ erlangPowKernel ε k c s := erlangPowKernel_nonneg hc k hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  have hstep : erlangPowKernel ε k c s * |g (x + s)| ≤
      erlangPowKernel ε k c s * M :=
    mul_le_mul_of_nonneg_left (hM _) hk
  calc erlangPowKernel ε k c s * |g (x + s)| ≤ erlangPowKernel ε k c s * M := hstep
    _ = M / c * (s ^ k * Real.exp (-s / ε)) := by
        unfold erlangPowKernel
        ring

/-- At the near end of the half line the kernel average of a continuous source converges to the
kernel value at the origin. -/
theorem tendsto_erlangPowKernel_mul_nhdsGT {ε c : ℝ} (k : ℕ)
    {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    Tendsto (fun s => erlangPowKernel ε k c s * g (x + s)) (𝓝[>] 0)
      (𝓝 (erlangPowKernel ε k c 0 * g x)) := by
  have hcont : ContinuousAt
      (fun s => erlangPowKernel ε k c s * g (x + s)) 0 :=
    ((continuous_erlangPowKernel ε k c).mul
      (hg.comp (continuous_const.add continuous_id))).continuousAt
  have hwithin : Tendsto (fun s => erlangPowKernel ε k c s * g (x + s)) (𝓝[>] 0)
      (𝓝 (erlangPowKernel ε k c 0 * g (x + 0))) :=
    hcont.continuousWithinAt
  simpa using hwithin

/-- Measurability of the derivative of a differentiable source. -/
theorem measurable_of_hasDerivAt {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) : Measurable f' := by
  have hEq : f' = deriv f := funext fun x => ((hf x).deriv).symm
  rw [hEq]
  exact measurable_deriv f

/-- Continuity of a differentiable source. -/
theorem continuous_of_hasDerivAt_erlangBoundedSource {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x => (hf x).differentiableAt.continuousAt

/-- **Differentiation under the Erlang integral.**  A bounded derivative dominates the parametric
derivative of every normalized Erlang average. -/
theorem hasDerivAt_erlangPowKernel_integral {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (k : ℕ)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    {M : ℝ} (hMf : ∀ y, |f y| ≤ M) (hMf' : ∀ y, |f' y| ≤ M) (x₀ : ℝ) :
    HasDerivAt (fun x => ∫ s in Ioi 0, erlangPowKernel ε k c s * f (x + s))
      (∫ s in Ioi 0, erlangPowKernel ε k c s * f' (x₀ + s)) x₀ := by
  have hfmeas : Measurable f := (continuous_of_hasDerivAt_erlangBoundedSource hf).measurable
  have hf'meas : Measurable f' := measurable_of_hasDerivAt hf
  have hFmeas : ∀ x : ℝ, AEStronglyMeasurable
      (fun s => erlangPowKernel ε k c s * f (x + s))
      (volume.restrict (Ioi 0)) := fun x =>
    (((continuous_erlangPowKernel ε k c).measurable).mul
      (hfmeas.comp (measurable_const_add x))).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable
      (fun s => erlangPowKernel ε k c s * f' (x₀ + s))
      (volume.restrict (Ioi 0)) :=
    (((continuous_erlangPowKernel ε k c).measurable).mul
      (hf'meas.comp (measurable_const_add x₀))).aestronglyMeasurable
  have hFint : IntegrableOn
      (fun s => erlangPowKernel ε k c s * f (x₀ + s)) (Ioi 0) :=
    integrableOn_erlangPowKernel_mul hε hc k hfmeas hMf x₀
  have hboundint : IntegrableOn
      (fun s => M * erlangPowKernel ε k c s) (Ioi 0) :=
    (integrableOn_erlangPowKernel hε k c).const_mul M
  have hbound : ∀ᵐ s ∂(volume.restrict (Ioi 0)), ∀ x ∈ (Set.univ : Set ℝ),
      ‖erlangPowKernel ε k c s * f' (x + s)‖ ≤ M * erlangPowKernel ε k c s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro x _
    have hk : 0 ≤ erlangPowKernel ε k c s :=
      erlangPowKernel_nonneg hc k (le_of_lt hs)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hMf' _) hk
  have hdiff : ∀ᵐ s ∂(volume.restrict (Ioi 0)), ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun x => erlangPowKernel ε k c s * f (x + s))
        (erlangPowKernel ε k c s * f' (x + s)) x := by
    filter_upwards with s
    intro x _
    have hshift : HasDerivAt (fun y : ℝ => y + s) 1 x :=
      (hasDerivAt_id x).add_const s
    have hcomp := (hf (x + s)).comp x hshift
    rw [mul_one] at hcomp
    exact hcomp.const_mul (erlangPowKernel ε k c s)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x s => erlangPowKernel ε k c s * f (x + s))
    (F' := fun x s => erlangPowKernel ε k c s * f' (x + s))
    (bound := fun s => M * erlangPowKernel ε k c s)
    Filter.univ_mem (Filter.Eventually.of_forall hFmeas) hFint hF'meas
    hbound hboundint hdiff).2

/-! ## The bounded first-order source class -/

/-- A source with a globally bounded value and a globally bounded derivative. -/
structure ErlangBoundedSource (f f' : ℝ → ℝ) (M : ℝ) : Prop where
  hasDeriv : ∀ x, HasDerivAt f (f' x) x
  abs_le : ∀ x, |f x| ≤ M
  abs_deriv_le : ∀ x, |f' x| ≤ M

/-- **Bounded first-order sources are Erlang-recovery admissible.**  All seventeen analytic fields
follow from the two global bounds: integrability from the Gamma moments of the kernels, the near
boundary from continuity, the far boundary from exponential decay, and the three parametric
derivatives from kernel domination. -/
theorem erlangRecoveryAdmissible_of_boundedSource {ε : ℝ} (hε : 0 < ε)
    {f f' : ℝ → ℝ} {M : ℝ} (hsrc : ErlangBoundedSource f f' M) :
    ErlangRecoveryAdmissible ε f f' := by
  have hfcont : Continuous f := continuous_of_hasDerivAt_erlangBoundedSource hsrc.hasDeriv
  have hfmeas : Measurable f := hfcont.measurable
  have hf'meas : Measurable f' := measurable_of_hasDerivAt hsrc.hasDeriv
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hε3 : (0 : ℝ) < 2 * ε ^ 3 := by positivity
  refine
    { source_hasDeriv := hsrc.hasDeriv
      integrable_one := fun x => ?_
      integrable_one_deriv := fun x => ?_
      integrable_two := fun x => ?_
      integrable_two_deriv := fun x => ?_
      integrable_three := fun x => ?_
      integrable_three_deriv := fun x => ?_
      boundary_one_zero := fun x => ?_
      boundary_two_zero := fun x => ?_
      boundary_three_zero := fun x => ?_
      boundary_one_top := fun x => ?_
      boundary_two_top := fun x => ?_
      boundary_three_top := fun x => ?_
      average_one_hasDeriv := fun x => ?_
      average_two_hasDeriv := fun x => ?_
      average_three_hasDeriv := fun x => ?_ }
  · simpa [erlangOneKernel_eq_powKernel] using
      integrableOn_erlangPowKernel_mul hε hε 0 hfmeas hsrc.abs_le x
  · simpa [erlangOneKernel_eq_powKernel] using
      integrableOn_erlangPowKernel_mul hε hε 0 hf'meas hsrc.abs_deriv_le x
  · simpa [erlangTwoKernel_eq_powKernel] using
      integrableOn_erlangPowKernel_mul hε hε2 1 hfmeas hsrc.abs_le x
  · simpa [erlangTwoKernel_eq_powKernel] using
      integrableOn_erlangPowKernel_mul hε hε2 1 hf'meas hsrc.abs_deriv_le x
  · simpa [erlangThreeKernel_eq_powKernel] using
      integrableOn_erlangPowKernel_mul hε hε3 2 hfmeas hsrc.abs_le x
  · simpa [erlangThreeKernel_eq_powKernel] using
      integrableOn_erlangPowKernel_mul hε hε3 2 hf'meas hsrc.abs_deriv_le x
  · have h := tendsto_erlangPowKernel_mul_nhdsGT (ε := ε) (c := ε) 0 hfcont x
    have hval : erlangPowKernel ε 0 ε 0 * f x = f x / ε := by
      simp [erlangPowKernel]
      ring
    rw [hval] at h
    simpa [erlangOneKernel_eq_powKernel] using h
  · have h := tendsto_erlangPowKernel_mul_nhdsGT (ε := ε) (c := ε ^ 2) 1 hfcont x
    have hval : erlangPowKernel ε 1 (ε ^ 2) 0 * f x = 0 := by
      simp [erlangPowKernel]
    rw [hval] at h
    simpa [erlangTwoKernel_eq_powKernel] using h
  · have h := tendsto_erlangPowKernel_mul_nhdsGT (ε := ε) (c := 2 * ε ^ 3) 2 hfcont x
    have hval : erlangPowKernel ε 2 (2 * ε ^ 3) 0 * f x = 0 := by
      simp [erlangPowKernel]
    rw [hval] at h
    simpa [erlangThreeKernel_eq_powKernel] using h
  · simpa [erlangOneKernel_eq_powKernel] using
      tendsto_erlangPowKernel_mul_atTop hε hε 0 hsrc.abs_le x
  · simpa [erlangTwoKernel_eq_powKernel] using
      tendsto_erlangPowKernel_mul_atTop hε hε2 1 hsrc.abs_le x
  · simpa [erlangThreeKernel_eq_powKernel] using
      tendsto_erlangPowKernel_mul_atTop hε hε3 2 hsrc.abs_le x
  · have h : HasDerivAt (fun y => ∫ s in Ioi 0, erlangOneKernel ε s * f (y + s))
        (∫ s in Ioi 0, erlangOneKernel ε s * f' (x + s)) x := by
      simpa [erlangOneKernel_eq_powKernel] using
        hasDerivAt_erlangPowKernel_integral hε hε 0 hsrc.hasDeriv
          hsrc.abs_le hsrc.abs_deriv_le x
    exact h
  · have h : HasDerivAt (fun y => ∫ s in Ioi 0, erlangTwoKernel ε s * f (y + s))
        (∫ s in Ioi 0, erlangTwoKernel ε s * f' (x + s)) x := by
      simpa [erlangTwoKernel_eq_powKernel] using
        hasDerivAt_erlangPowKernel_integral hε hε2 1 hsrc.hasDeriv
          hsrc.abs_le hsrc.abs_deriv_le x
    exact h
  · have h : HasDerivAt (fun y => ∫ s in Ioi 0, erlangThreeKernel ε s * f (y + s))
        (∫ s in Ioi 0, erlangThreeKernel ε s * f' (x + s)) x := by
      simpa [erlangThreeKernel_eq_powKernel] using
        hasDerivAt_erlangPowKernel_integral hε hε3 2 hsrc.hasDeriv
          hsrc.abs_le hsrc.abs_deriv_le x
    exact h

/-- **Unconditional third-order recovery for bounded first-order sources.**  `(1 - εD)³` inverts the
third-order Erlang average on the whole class. -/
theorem erlangAverageThree_exact_recovery_of_boundedSource {ε : ℝ} (hε : 0 < ε)
    {f f' : ℝ → ℝ} {M : ℝ} (hsrc : ErlangBoundedSource f f' M) :
    erlangFirstOrderRecover ε
        (erlangFirstOrderRecover ε
          (erlangFirstOrderRecover ε (erlangAverageThree ε f))) = f :=
  erlangAverageThree_exact_recovery hε (erlangRecoveryAdmissible_of_boundedSource hε hsrc)

/-! ## An explicit source -/

theorem erlangBoundedSource_sin : ErlangBoundedSource Real.sin Real.cos 1 where
  hasDeriv := fun x => Real.hasDerivAt_sin x
  abs_le := fun x => Real.abs_sin_le_one x
  abs_deriv_le := fun x => Real.abs_cos_le_one x

theorem erlangRecoveryAdmissible_sin {ε : ℝ} (hε : 0 < ε) :
    ErlangRecoveryAdmissible ε Real.sin Real.cos :=
  erlangRecoveryAdmissible_of_boundedSource hε erlangBoundedSource_sin

/-- The third-order Erlang recovery identity for the sine source, with no analytic premise. -/
theorem erlangAverageThree_exact_recovery_sin {ε : ℝ} (hε : 0 < ε) :
    erlangFirstOrderRecover ε
        (erlangFirstOrderRecover ε
          (erlangFirstOrderRecover ε (erlangAverageThree ε Real.sin))) = Real.sin :=
  erlangAverageThree_exact_recovery_of_boundedSource hε erlangBoundedSource_sin

end

end GaloisForLFunctions.HTGeometry
