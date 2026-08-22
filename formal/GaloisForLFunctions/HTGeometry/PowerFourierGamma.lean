import GaloisForLFunctions.HTGeometry.DampedPowerOscillation
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation

/-!
# The Fourier–Mellin evaluation of a power

For `0 < Re s < 1` and a positive frequency `L`,

`lim_{T→∞} ∫_0^T t^{-s} e^{itL} dt = Γ(1-s) · (-iL)^{s-1}`.

The improper integral is only conditionally convergent, so the evaluation goes through Abel
regularisation: for `ε > 0` the damped integral is the Euler integral
`∫_0^∞ t^{-s} e^{-(ε - iL)t} dt = Γ(1-s)(ε - iL)^{s-1}`, and the tail estimate of
`DampedPowerOscillation` is **uniform in `ε`**, which is exactly what lets `ε ↓ 0` and `T → ∞` be
interchanged.

This is the classical identity behind the `χ`-factor of the functional equation, and behind
Burnol's kernel `C_a(u, 1-s)` (arXiv:math/0203120, via his C. R. note [6]).

## Main results

* `integral_damped_Ioi` — the Abel-regularised evaluation.
* `norm_integral_damped_tail_le` — the uniform tail bound.
* `tendsto_integral_powerOsc` — the improper evaluation for a positive frequency.
* `tendsto_integral_powerOsc_ne` — the same for any nonzero real frequency.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

/-- The damped oscillatory integrand is the Euler integrand at the complex rate `ε - iL`. -/
theorem dampedPowerAmp_mul_osc (s : ℂ) (ε L t : ℝ) :
    dampedPowerAmp s ε t * Complex.exp ((t * L : ℝ) * Complex.I)
      = (t : ℂ) ^ (-s) * Complex.exp (-(((ε : ℂ) - (L : ℂ) * Complex.I) * (t : ℂ))) := by
  rw [dampedPowerAmp, mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrableOn_damped {s : ℂ} (hs1 : s.re < 1) {ε L : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => dampedPowerAmp s ε t * Complex.exp ((t * L : ℝ) * Complex.I))
      (Set.Ioi (0 : ℝ)) volume := by
  have hre : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hw : 0 < ((ε : ℂ) - (L : ℂ) * Complex.I).re := by
    simp [Complex.sub_re, Complex.mul_re]
    exact hε
  have h := integrableOn_cpow_mul_exp_neg_mul_Ioi hre hw
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  show (t : ℂ) ^ (1 - s - 1) * Complex.exp (-(((ε : ℂ) - (L : ℂ) * Complex.I) * (t : ℂ)))
      = dampedPowerAmp s ε t * Complex.exp ((t * L : ℝ) * Complex.I)
  rw [dampedPowerAmp_mul_osc]
  congr 2
  ring

/-- **The Abel-regularised evaluation.** -/
theorem integral_damped_Ioi {s : ℂ} (hs1 : s.re < 1) {ε L : ℝ} (hε : 0 < ε) :
    (∫ t in Set.Ioi (0 : ℝ),
        dampedPowerAmp s ε t * Complex.exp ((t * L : ℝ) * Complex.I))
      = Complex.Gamma (1 - s) * ((ε : ℂ) - (L : ℂ) * Complex.I) ^ (s - 1) := by
  have hre : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hw : 0 < ((ε : ℂ) - (L : ℂ) * Complex.I).re := by
    simp [Complex.sub_re, Complex.mul_re]
    exact hε
  have h := integral_cpow_mul_exp_neg_mul_Ioi hre hw
  have hcong : (∫ t in Set.Ioi (0 : ℝ),
      dampedPowerAmp s ε t * Complex.exp ((t * L : ℝ) * Complex.I))
      = ∫ t in Set.Ioi (0 : ℝ),
        (t : ℂ) ^ ((1 - s) - 1) * Complex.exp (-(((ε : ℂ) - (L : ℂ) * Complex.I) * (t : ℂ))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [dampedPowerAmp_mul_osc]
    congr 2
    ring
  rw [hcong, h]
  congr 1
  congr 1
  ring

/-- For a fixed truncation the damping can be removed. -/
theorem tendsto_dampedTrunc {s : ℂ} (hs1 : s.re < 1) {L T : ℝ} (hT : 0 < T) :
    Tendsto (fun ε : ℝ => ∫ t in (0 : ℝ)..T,
        dampedPowerAmp s ε t * Complex.exp ((t * L : ℝ) * Complex.I)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in (0 : ℝ)..T, (t : ℂ) ^ (-s) * Complex.exp ((t * L : ℝ) * Complex.I))) := by
  have hIoc : Set.uIoc (0 : ℝ) T = Set.Ioc (0 : ℝ) T := by
    rw [Set.uIoc_of_le hT.le]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => t ^ (-s.re)) ?_ ?_ ?_ ?_
  · filter_upwards with ε
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    rw [hIoc]
    refine ContinuousOn.mul ?_ (by fun_prop)
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (-s)) t :=
      Complex.continuousAt_ofReal_cpow_const t (-s) (Or.inr ht.1.ne')
    have h2 : ContinuousAt (fun x : ℝ => Complex.exp (-(ε : ℂ) * (x : ℂ))) t := by fun_prop
    exact h1.mul h2
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards with t ht
    rw [hIoc] at ht
    rw [norm_mul, norm_dampedPowerAmp ht.1 s ε, Complex.norm_exp]
    have hphase : (((t * L : ℝ) : ℂ) * Complex.I).re = 0 := by simp
    rw [hphase, Real.exp_zero, mul_one]
    have hexp : Real.exp (-(ε * t)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : 0 ≤ ε * t := mul_nonneg (le_of_lt hε) ht.1.le
      linarith
    have hnn : (0:ℝ) ≤ t ^ (-s.re) := Real.rpow_nonneg ht.1.le _
    calc t ^ (-s.re) * Real.exp (-(ε * t)) ≤ t ^ (-s.re) * 1 :=
          mul_le_mul_of_nonneg_left hexp hnn
      _ = t ^ (-s.re) := mul_one _
  · refine intervalIntegral.intervalIntegrable_rpow' ?_
    linarith
  · filter_upwards with t ht
    rw [hIoc] at ht
    have hcont : Continuous (fun ε : ℝ => -(ε : ℂ) * (t : ℂ)) :=
      (Complex.continuous_ofReal.neg).mul continuous_const
    have hbase : Tendsto (fun ε : ℝ => -(ε : ℂ) * (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      have hc := (hcont.continuousAt (x := (0 : ℝ))).tendsto
      have h0 : -((0 : ℝ) : ℂ) * (t : ℂ) = 0 := by simp
      rw [h0] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    have hcexp : Tendsto (fun ε : ℝ => Complex.exp (-(ε : ℂ) * (t : ℂ))) (𝓝[>] (0 : ℝ))
        (𝓝 (1 : ℂ)) := by
      have hc := (Complex.continuous_exp.continuousAt (x := (0 : ℂ))).tendsto.comp hbase
      simpa [Function.comp_def] using hc
    have h := (hcexp.const_mul ((t : ℂ) ^ (-s))).mul_const
      (Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
    simpa [dampedPowerAmp] using h

/-- The tail of the Abel-regularised integral obeys the uniform bound. -/
theorem norm_integral_damped_tail_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {ε L T : ℝ} (hε : 0 < ε) (hL : 0 < L) (hT : 0 < T) :
    ‖(∫ t in Set.Ioi (0 : ℝ), dampedPowerAmp s ε t * Complex.exp ((t * L : ℝ) * Complex.I))
        - (∫ t in (0 : ℝ)..T, dampedPowerAmp s ε t * Complex.exp ((t * L : ℝ) * Complex.I))‖
      ≤ (3 * T ^ (-s.re) + ‖s‖ * T ^ (-s.re) / s.re) / L := by
  set F : ℝ → ℂ := fun t => dampedPowerAmp s ε t * Complex.exp ((t * L : ℝ) * Complex.I) with hF
  have hint : IntegrableOn F (Set.Ioi (0 : ℝ)) volume := integrableOn_damped hs1 hε
  have hintT : IntegrableOn F (Set.Ioi T) volume :=
    hint.mono_set (Set.Ioi_subset_Ioi hT.le)
  have hintIoc : IntegrableOn F (Set.Ioc (0 : ℝ) T) volume :=
    hint.mono_set (fun x hx => hx.1)
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) T) (Set.Ioi T) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx' (not_lt.2 hx.2)
  have hunion := MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hintIoc hintT
  rw [Set.Ioc_union_Ioi_eq_Ioi hT.le] at hunion
  have hsub : (∫ t in Set.Ioi (0 : ℝ), F t) - (∫ t in (0 : ℝ)..T, F t)
      = ∫ t in Set.Ioi T, F t := by
    rw [intervalIntegral.integral_of_le hT.le, hunion]
    ring
  rw [hsub]
  have htend : Tendsto (fun T' : ℝ => ∫ t in T..T', F t) atTop (𝓝 (∫ t in Set.Ioi T, F t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi T hintT tendsto_id
  refine le_of_tendsto htend.norm ?_
  filter_upwards [eventually_ge_atTop T] with T' hT'
  exact norm_integral_dampedPowerAmp_le hT hT' hs0 hε.le hL

/-- **The Fourier–Mellin evaluation of a power.**  For `0 < Re s < 1` and `L > 0`,
`∫_0^∞ t^{-s} e^{itL} dt = Γ(1-s)(-iL)^{s-1}`, the integral being the improper limit. -/
theorem tendsto_integral_powerOsc {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        (t : ℂ) ^ (-s) * Complex.exp ((t * L : ℝ) * Complex.I)) atTop
      (𝓝 (Complex.Gamma (1 - s) * (-((L : ℂ) * Complex.I)) ^ (s - 1))) := by
  set G : ℂ := Complex.Gamma (1 - s) * (-((L : ℂ) * Complex.I)) ^ (s - 1) with hG
  set J : ℝ → ℂ := fun T => ∫ t in (0 : ℝ)..T,
    (t : ℂ) ^ (-s) * Complex.exp ((t * L : ℝ) * Complex.I) with hJ
  set Jd : ℝ → ℝ → ℂ := fun ε T => ∫ t in (0 : ℝ)..T,
    dampedPowerAmp s ε t * Complex.exp ((t * L : ℝ) * Complex.I) with hJd
  have hPhi : Tendsto (fun ε : ℝ => Complex.Gamma (1 - s) *
      ((ε : ℂ) - (L : ℂ) * Complex.I) ^ (s - 1)) (𝓝[>] (0 : ℝ)) (𝓝 G) := by
    have hslit : (-((L : ℂ) * Complex.I)) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      simp
      exact hL.ne'
    have hcont : ContinuousAt (fun w : ℂ => Complex.Gamma (1 - s) * w ^ (s - 1))
        (-((L : ℂ) * Complex.I)) :=
      (((Complex.hasStrictDerivAt_cpow_const (c := s - 1) hslit).hasDerivAt).continuousAt).const_mul
        (Complex.Gamma (1 - s))
    have hmap : Tendsto (fun ε : ℝ => ((ε : ℂ) - (L : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (-((L : ℂ) * Complex.I))) := by
      have h1 : Tendsto (fun ε : ℝ => ((ε : ℂ) - (L : ℂ) * Complex.I)) (𝓝 (0 : ℝ))
          (𝓝 (((0 : ℝ) : ℂ) - (L : ℂ) * Complex.I)) :=
        (Complex.continuous_ofReal.continuousAt).tendsto.sub tendsto_const_nhds
      have h2 : (((0 : ℝ) : ℂ) - (L : ℂ) * Complex.I) = -((L : ℂ) * Complex.I) := by
        push_cast
        ring
      rw [h2] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    exact hcont.tendsto.comp hmap
  have hfix : ∀ T : ℝ, 0 < T → Tendsto (fun ε : ℝ => Jd ε T) (𝓝[>] (0 : ℝ)) (𝓝 (J T)) :=
    fun T hT => tendsto_dampedTrunc hs1 hT
  set K : ℝ := (3 + ‖s‖ / s.re) / L with hK
  have hbound : ∀ T : ℝ, 0 < T → ‖J T - G‖ ≤ T ^ (-s.re) * K := by
    intro T hT
    refine le_of_forall_pos_le_add ?_
    intro δ hδ
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖J T - Jd ε T‖ < δ / 2 := by
      have hs := (hfix T hT).const_sub (J T)
      have h0 : Tendsto (fun ε : ℝ => J T - Jd ε T) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using hs
      have h0' : Tendsto (fun ε : ℝ => ‖J T - Jd ε T‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using h0.norm
      exact h0'.eventually (gt_mem_nhds (by linarith))
    have h2 : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
        ‖Complex.Gamma (1 - s) * ((ε : ℂ) - (L : ℂ) * Complex.I) ^ (s - 1) - G‖ < δ / 2 := by
      have h0 : Tendsto
          (fun ε : ℝ => Complex.Gamma (1 - s) * ((ε : ℂ) - (L : ℂ) * Complex.I) ^ (s - 1) - G)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using hPhi.sub (tendsto_const_nhds (x := G))
      have h0' : Tendsto
          (fun ε : ℝ =>
            ‖Complex.Gamma (1 - s) * ((ε : ℂ) - (L : ℂ) * Complex.I) ^ (s - 1) - G‖)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using h0.norm
      exact h0'.eventually (gt_mem_nhds (by linarith))
    obtain ⟨ε, ⟨⟨hε1, hε2⟩, hεpos⟩⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
    have hεpos' : (0 : ℝ) < ε := hεpos
    have hmid : ‖Jd ε T - Complex.Gamma (1 - s) * ((ε : ℂ) - (L : ℂ) * Complex.I) ^ (s - 1)‖
        ≤ T ^ (-s.re) * K := by
      have htail := norm_integral_damped_tail_le hs0 hs1 hεpos' hL hT
      rw [integral_damped_Ioi hs1 hεpos'] at htail
      rw [← norm_neg]
      have heq : -(Jd ε T - Complex.Gamma (1 - s) * ((ε : ℂ) - (L : ℂ) * Complex.I) ^ (s - 1))
          = Complex.Gamma (1 - s) * ((ε : ℂ) - (L : ℂ) * Complex.I) ^ (s - 1) - Jd ε T := by ring
      rw [heq]
      refine htail.trans (le_of_eq ?_)
      rw [hK]
      field_simp
    have htri : ‖J T - G‖ ≤ ‖J T - Jd ε T‖
        + ‖Jd ε T - Complex.Gamma (1 - s) * ((ε : ℂ) - (L : ℂ) * Complex.I) ^ (s - 1)‖
        + ‖Complex.Gamma (1 - s) * ((ε : ℂ) - (L : ℂ) * Complex.I) ^ (s - 1) - G‖ := by
      have ha := norm_sub_le_norm_sub_add_norm_sub (J T)
        (Complex.Gamma (1 - s) * ((ε : ℂ) - (L : ℂ) * Complex.I) ^ (s - 1)) G
      have hb := norm_sub_le_norm_sub_add_norm_sub (J T) (Jd ε T)
        (Complex.Gamma (1 - s) * ((ε : ℂ) - (L : ℂ) * Complex.I) ^ (s - 1))
      linarith
    linarith
  have hzero : Tendsto (fun T : ℝ => T ^ (-s.re) * K) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hs0).mul_const K
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero' ?_ ?_ hzero
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T _ using norm_nonneg _
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT using hbound T hT

/-- Conjugating a positive-real power flips the exponent. -/
theorem conj_cpow_ofReal_base {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (starRingEnd ℂ) ((t : ℂ) ^ w) = (t : ℂ) ^ ((starRingEnd ℂ) w) := by
  have harg : ((t : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact Ne.symm (ne_of_gt Real.pi_pos)
  have h := Complex.conj_cpow ((t : ℝ) : ℂ) ((starRingEnd ℂ) w) harg
  rw [Complex.conj_ofReal, Complex.conj_conj] at h
  exact h.symm

/-- **The Fourier–Mellin evaluation of a power, for any nonzero real frequency.** -/
theorem tendsto_integral_powerOsc_ne {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {L : ℝ}
    (hL : L ≠ 0) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        (t : ℂ) ^ (-s) * Complex.exp ((t * L : ℝ) * Complex.I)) atTop
      (𝓝 (Complex.Gamma (1 - s) * (-((L : ℂ) * Complex.I)) ^ (s - 1))) := by
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · have hs0' : 0 < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
    have hs1' : ((starRingEnd ℂ) s).re < 1 := by rwa [Complex.conj_re]
    have hL' : (0 : ℝ) < -L := by linarith
    have hbase := tendsto_integral_powerOsc hs0' hs1' hL'
    have hconj := (Complex.continuous_conj.tendsto _).comp hbase
    have hw : (-((((-L : ℝ)) : ℂ) * Complex.I)) = ((L : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have harg : (((L : ℝ) : ℂ) * Complex.I).arg ≠ Real.pi := by
      have hval : ((L : ℝ) : ℂ) * Complex.I = ((|L| : ℝ) : ℂ) * (-Complex.I) := by
        rw [abs_of_neg hneg]
        push_cast
        ring
      rw [hval, Complex.arg_real_mul _ (abs_pos.2 hL), Complex.arg_neg_I]
      intro h
      have := Real.pi_pos
      linarith
    have hpt : (starRingEnd ℂ) (Complex.Gamma (1 - (starRingEnd ℂ) s)
          * (-((((-L : ℝ)) : ℂ) * Complex.I)) ^ ((starRingEnd ℂ) s - 1))
        = Complex.Gamma (1 - s) * (-((L : ℂ) * Complex.I)) ^ (s - 1) := by
      rw [map_mul, hw]
      congr 1
      · rw [← Complex.Gamma_conj]
        congr 1
        simp
      · have hcc := Complex.conj_cpow (((L : ℝ) : ℂ) * Complex.I) (s - 1) harg
        have hconjLI : (starRingEnd ℂ) (((L : ℝ) : ℂ) * Complex.I)
            = -((L : ℂ) * Complex.I) := by
          rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
          ring
        rw [hconjLI] at hcc
        have hn : (starRingEnd ℂ) (s - 1) = (starRingEnd ℂ) s - 1 := by
          rw [map_sub, map_one]
        rw [hn] at hcc
        exact hcc.symm
    rw [← hpt]
    refine Filter.Tendsto.congr' ?_ hconj
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    show (starRingEnd ℂ) (∫ t in (0 : ℝ)..T, ((t : ℂ) ^ (-(starRingEnd ℂ) s)
        * Complex.exp ((t * (-L) : ℝ) * Complex.I)))
      = ∫ t in (0 : ℝ)..T, (t : ℂ) ^ (-s) * Complex.exp ((t * L : ℝ) * Complex.I)
    rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT,
      ← _root_.integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [map_mul, conj_cpow_ofReal_base ht.1, ← Complex.exp_conj]
    congr 1
    · congr 1
      simp
    · rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
  · exact tendsto_integral_powerOsc hs0 hs1 hpos

end

end GaloisForLFunctions.HTGeometry
