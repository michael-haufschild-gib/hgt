import GaloisForLFunctions.ArithmeticCriticalityTheory.DoobSourcePoleMomentLawAtInfinity

/-!
# The folded source at the origin is the jump-measure moment of the profile

For a profile `M ∈ C¹` with `M(0) = 0` and `|M|, |M'| ≤ Ce^{−8|y|}`, and its gauge `ω = M/Φ`
(`tendsto_foldedSource_div_nhdsGT_zero`):

    (𝓛_N ω − Φ cosh(x/2) ω)(x) / Φ(x)  →  −2 ∫ M dm = −2 [∫_0^∞ ω(t) M(t) dt + Σ_n Λ(n) n^{−1/2} M(log n)]

as `x → 0⁺`, where `dm` is the jump measure (`jumpMeasureMoment`). By the exact folded source
`−Φ 𝒲(M(|·|))` this is the value of the pole-free Weil operator of the fold at the origin: every jump
from `0` lands at distance `t` on one side or the other, and the fold reads both landing points as
`M(t)`.

Together with the law at infinity (`tendsto_foldedSource_div`, weight `Φ(x) e^{x/2}`, limit
`−2 ∫_0^∞ M cosh(r/2)`), the folded source of every profile is governed at the two ends of the half
line by two moments of `M`: the jump-measure moment at the origin and the cosh moment at infinity. A
gauge that is a folded supersolution near both ends must have both moments `≤ 0`
(`jumpMeasureMoment_nonpos_of_foldedSupersolution_near_zero`,
`coshMoment_nonpos_of_foldedSupersolution_near_infinity`). For a nonnegative profile, nonzero on
`(0, ∞)`, both moments are positive (`jumpMeasureMoment_pos`, `coshMoment_pos`), so it is a strict
folded subsolution near the origin and on a half line
(`exists_origin_and_infinity_windows_foldedGenerator_lt_potential`), with no domination by a
translate of `Φ` and no condition at `log 2`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The moment `∫ M dm` of a profile against the jump measure. -/
def jumpMeasureMoment (M : ℝ → ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * M t) + ∑' n : ℕ, vonMangoldtAtom n * M (Real.log n)

/-- The pole-free Weil operator of the fold at the origin is twice the jump-measure moment. -/
theorem tendsto_poleFreeWeilOperator_abs_nhdsGT_zero {M : ℝ → ℝ} {C : ℝ} (hM : ContDiff ℝ 1 M)
    (hM0 : M 0 = 0) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) :
    Tendsto (fun x => poleFreeWeilOperator (fun y => M (|y|)) x) (𝓝[>] 0)
      (𝓝 (2 * jumpMeasureMoment M)) := by
  have hC0 := nonneg_of_abs_le_mul_exp hdec
  have hMc : Continuous fun y => M (|y|) := hM.continuous.comp continuous_abs
  have hLip := abs_comp_abs_sub_le (hM.differentiable one_ne_zero) hdec'
  have hMb : ∀ y, |M (|y|)| ≤ C := fun y => (hdec _).trans
    (mul_le_of_le_one_right hC0 (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg (|y|)])))
  -- the prime sum
  have hP : Tendsto (fun x => profilePrimeSum (fun y => M (|y|)) x) (𝓝[>] 0)
      (𝓝 (∑' n : ℕ, vonMangoldtAtom n * (M (Real.log n) + M (Real.log n)))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n =>
      vonMangoldtAtom n * (2 * (C * Real.exp (8 * 1) * Real.exp (-(8 * Real.log n)))))
      ((summable_atom_mul_exp_neg_eight_log.mul_left (2 * (C * Real.exp (8 * 1)))).congr
        fun n => by ring) (fun n => ?_) ?_
    · have hc : Continuous fun x => vonMangoldtAtom n * (M (|x + Real.log n|) + M (|x - Real.log n|)) :=
        continuous_const.mul ((hMc.comp (continuous_id.add continuous_const)).add
          (hMc.comp (continuous_id.sub continuous_const)))
      have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa only [zero_add, zero_sub, abs_neg, abs_of_nonneg (Real.log_natCast_nonneg n)] using h
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with x hx n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
      refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n)
      have hx1 : |x| ≤ 1 := by rw [abs_of_pos hx.1]; exact hx.2.le
      have hl := Real.log_natCast_nonneg n
      have h1 := abs_le_of_decay_of_le hdec (x := 1) (y := |x + Real.log n|) (n := n) (by
        rw [abs_abs, abs_one]
        have := abs_sub_abs_le_abs_sub (Real.log n) (-x)
        rw [abs_of_nonneg hl, abs_neg, sub_neg_eq_add, add_comm] at this
        linarith)
      have h2 := abs_le_of_decay_of_le hdec (x := 1) (y := |x - Real.log n|) (n := n) (by
        rw [abs_abs, abs_one, abs_sub_comm]
        have := abs_sub_abs_le_abs_sub (Real.log n) x
        rw [abs_of_nonneg hl] at this
        linarith)
      rw [abs_one] at h1 h2
      calc |M (|x + Real.log n|) + M (|x - Real.log n|)| ≤
          |M (|x + Real.log n|)| + |M (|x - Real.log n|)| := abs_add_le _ _
        _ ≤ _ := by linarith
  -- the archimedean integral
  have hA : Tendsto (fun x => ∫ u in Ioi (0 : ℝ), profileArchTerm (fun y => M (|y|)) x u) (𝓝[>] 0)
      (𝓝 (∫ u in Ioi (0 : ℝ), -(2 * (archLevyDensity u * M u)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => (2 * C + 3 * C) * (archLevyDensity u * u)) ?_ ?_
      (integrableOn_archLevyDensity_mul_id.const_mul _) ?_
    · exact Eventually.of_forall fun x =>
        (integrableOn_profileArchTerm hMc hLip x).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      rw [Real.norm_eq_abs]
      refine (abs_profileArchTerm_le hLip x hu).trans (mul_le_mul_of_nonneg_right ?_
        (mul_nonneg (archLevyDensity_pos hu).le (le_of_lt hu)))
      linarith [hMb x]
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have hc : Continuous fun x => profileArchTerm (fun y => M (|y|)) x u := by
        unfold profileArchTerm
        exact (continuous_const.mul hMc).sub (continuous_const.mul
          ((hMc.comp (continuous_id.add continuous_const)).add
            (hMc.comp (continuous_id.sub continuous_const))))
      have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      have e : profileArchTerm (fun y => M (|y|)) 0 u = -(2 * (archLevyDensity u * M u)) := by
        unfold profileArchTerm
        simp only [abs_zero, hM0, zero_add, zero_sub, abs_neg, abs_of_pos (show (0 : ℝ) < u from hu)]
        ring
      rwa [e] at h
  have hMx : Tendsto (fun x => 2 * archConstantReal * M (|x|)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun x => 2 * archConstantReal * M (|x|) := continuous_const.mul hMc
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [hM0] using h
  have hsum := (hP.sub hA).add hMx
  have hval : (∑' n : ℕ, vonMangoldtAtom n * (M (Real.log n) + M (Real.log n))) -
      (∫ u in Ioi (0 : ℝ), -(2 * (archLevyDensity u * M u))) + 0 = 2 * jumpMeasureMoment M := by
    have ht : (∑' n : ℕ, vonMangoldtAtom n * (M (Real.log n) + M (Real.log n))) =
        2 * ∑' n : ℕ, vonMangoldtAtom n * M (Real.log n) := by
      rw [← tsum_mul_left]
      exact tsum_congr fun n => by ring
    unfold jumpMeasureMoment
    rw [integral_neg, integral_const_mul, ht]
    ring
  rw [hval] at hsum
  exact hsum.congr fun x => rfl

/-- **The origin law.** For `M ∈ C¹` with `M(0) = 0` and `|M|, |M'| ≤ Ce^{−8|y|}`,
`(𝓛_N ω − Φ cosh(x/2) ω)(x)/Φ(x) → −2 ∫ M dm` as `x → 0⁺`, `ω = M/Φ`. -/
theorem tendsto_foldedSource_div_nhdsGT_zero {M : ℝ → ℝ} {C : ℝ} (hM : ContDiff ℝ 1 M)
    (hM0 : M 0 = 0) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) :
    Tendsto (fun x => (foldedGenerator (fun y => M y / riemannKernelReal y) x -
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x)) /
          riemannKernelReal x) (𝓝[>] 0) (𝓝 (-(2 * jumpMeasureMoment M))) := by
  refine (tendsto_poleFreeWeilOperator_abs_nhdsGT_zero hM hM0 hdec hdec').neg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [foldedGenerator_profileGauge_sub_potential_of_decay (hM.differentiable one_ne_zero) hdec
    hdec' (le_of_lt hx), neg_div, mul_div_cancel_left₀ _ (riemannKernelReal_pos x).ne']

/-- A folded supersolution near the origin has nonpositive jump-measure moment. -/
theorem jumpMeasureMoment_nonpos_of_foldedSupersolution_near_zero {M : ℝ → ℝ} {C : ℝ}
    (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) {δ : ℝ} (hδ : 0 < δ)
    (hsup : ∀ x ∈ Ioo 0 δ, riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) ≤
      foldedGenerator (fun y => M y / riemannKernelReal y) x) :
    jumpMeasureMoment M ≤ 0 := by
  have h := tendsto_foldedSource_div_nhdsGT_zero hM hM0 hdec hdec'
  have hge : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 ≤ (foldedGenerator (fun y => M y / riemannKernelReal y) x -
      riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x)) / riemannKernelReal x := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
    exact div_nonneg (sub_nonneg.mpr (hsup x hx)) (riemannKernelReal_pos x).le
  have := ge_of_tendsto h hge
  linarith

/-- A folded supersolution on a half line has nonpositive half-line cosh moment. -/
theorem coshMoment_nonpos_of_foldedSupersolution_near_infinity {M : ℝ → ℝ} {C : ℝ}
    (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) {X : ℝ}
    (hsup : ∀ x, X ≤ x → riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) ≤
      foldedGenerator (fun y => M y / riemannKernelReal y) x) :
    (∫ r in Ioi (0 : ℝ), M r * Real.cosh (r / 2)) ≤ 0 := by
  have h := tendsto_foldedSource_div hM hM0 hdec hdec'
  have hge : ∀ᶠ x in atTop, 0 ≤ (foldedGenerator (fun y => M y / riemannKernelReal y) x -
      riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x)) /
        (riemannKernelReal x * Real.exp (x / 2)) := by
    filter_upwards [eventually_ge_atTop X] with x hx
    exact div_nonneg (sub_nonneg.mpr (hsup x hx))
      (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)).le
  have := ge_of_tendsto h hge
  linarith

/-! ### Positive profiles -/

/-- The half-line integral of a continuous nonnegative integrable function that is positive at some
`y₀ > 0` is positive. -/
theorem setIntegral_Ioi_pos_of_pos_at {g : ℝ → ℝ} {y₀ : ℝ} (hg : ContinuousAt g y₀)
    (hgi : IntegrableOn g (Ioi 0))
    (hnn : ∀ y, 0 < y → 0 ≤ g y) (hy₀ : 0 < y₀) (hgy₀ : 0 < g y₀) :
    0 < ∫ y in Ioi (0 : ℝ), g y := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => hnn y hy) hgi]
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hg (g y₀ / 2) (by linarith)
  set a := max 0 (y₀ - δ)
  have hsub : Ioo a (y₀ + δ) ⊆ Function.support g ∩ Ioi 0 := fun y hy => by
    have ha0 : 0 < y := lt_of_le_of_lt (le_max_left _ _) hy.1
    have hd : dist y y₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right 0 (y₀ - δ), hy.1, hy.2]
    have := hball hd
    rw [Real.dist_eq] at this
    refine ⟨?_, ha0⟩
    have : g y₀ / 2 < g y := by linarith [neg_abs_le (g y - g y₀)]
    exact (by linarith : 0 < g y).ne'
  have hlt : a < y₀ + δ := max_lt (by linarith) (by linarith)
  calc (0 : ENNReal) < volume (Ioo a (y₀ + δ)) := by
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
    _ ≤ _ := measure_mono hsub

/-- A nonnegative profile, positive at some `y₀ > 0`, has positive jump-measure moment. -/
theorem jumpMeasureMoment_pos {M : ℝ → ℝ} {C : ℝ} (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0)
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) (hnn : ∀ y, 0 ≤ y → 0 ≤ M y) {y₀ : ℝ}
    (hy₀ : 0 < y₀) (hM₀ : 0 < M y₀) : 0 < jumpMeasureMoment M := by
  have hlin : ∀ t, |M t| ≤ C * |t| := fun t => by
    simpa [hM0] using abs_sub_le_of_decay hM hdec' t 0
  have hint : IntegrableOn (fun t => archLevyDensity t * M t) (Ioi 0) := by
    refine (integrableOn_archLevyDensity_mul_id.const_mul C).mono'
      (measurable_archLevyDensity.mul hM.continuous.measurable).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have ht0 : 0 < t := mem_Ioi.mp ht
    have hω := archLevyDensity_pos ht0
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hω]
    have := hlin t
    rw [abs_of_pos ht0] at this
    nlinarith
  have hcont : ContinuousAt (fun t => archLevyDensity t * M t) y₀ := by
    refine ContinuousAt.mul ?_ hM.continuous.continuousAt
    unfold archLevyDensity
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    have : Real.exp (-2 * y₀) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have harch := setIntegral_Ioi_pos_of_pos_at hcont hint
    (fun t ht => mul_nonneg (archLevyDensity_pos ht).le (hnn t ht.le)) hy₀
    (mul_pos (archLevyDensity_pos hy₀) hM₀)
  have hprime : 0 ≤ ∑' n : ℕ, vonMangoldtAtom n * M (Real.log n) :=
    tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (hnn _ (Real.log_natCast_nonneg n))
  unfold jumpMeasureMoment
  linarith

/-- A nonnegative profile, positive at some `y₀ > 0`, has positive half-line cosh moment. -/
theorem coshMoment_pos {M : ℝ → ℝ} {C : ℝ} (hM : Continuous M)
    (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|))) (hnn : ∀ y, 0 ≤ y → 0 ≤ M y) {y₀ : ℝ}
    (hy₀ : 0 < y₀) (hM₀ : 0 < M y₀) : 0 < ∫ r in Ioi (0 : ℝ), M r * Real.cosh (r / 2) := by
  obtain ⟨hp, hm, -, -⟩ := integral_exp_half_add_exp_neg_half hM
    (fun r hr => abs_le_exp_neg_two_of_decay hdec hr)
  have hint : IntegrableOn (fun r => M r * Real.cosh (r / 2)) (Ioi 0) := by
    refine IntegrableOn.congr_fun ((hp.add hm).div_const 2) (fun r _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Real.cosh_eq, neg_div]
    ring
  exact setIntegral_Ioi_pos_of_pos_at (hM.mul (Real.continuous_cosh.comp
    (continuous_id.div_const 2))).continuousAt hint
    (fun r hr => mul_nonneg (hnn r hr.le) (Real.cosh_pos _).le) hy₀
    (mul_pos hM₀ (Real.cosh_pos _))

/-- **Positive profiles fail at both ends.** A nonnegative profile `M ∈ C¹`, positive at some
`y₀ > 0`, with `M(0) = 0` and `|M|, |M'| ≤ Ce^{−8|y|}`, is a strict folded subsolution on an origin
window `(0, δ)` and on a half line `[X, ∞)`. -/
theorem exists_origin_and_infinity_windows_foldedGenerator_lt_potential {M : ℝ → ℝ} {C : ℝ}
    (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) (hnn : ∀ y, 0 ≤ y → 0 ≤ M y)
    {y₀ : ℝ} (hy₀ : 0 < y₀) (hM₀ : 0 < M y₀) :
    (∃ δ > 0, ∀ x ∈ Ioo 0 δ, foldedGenerator (fun y => M y / riemannKernelReal y) x <
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x)) ∧
      ∃ X : ℝ, ∀ x, X ≤ x → foldedGenerator (fun y => M y / riemannKernelReal y) x <
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) := by
  refine ⟨?_, exists_infinity_window_foldedGenerator_lt_potential_of_coshMoment_pos hM hM0 hdec
    hdec' (coshMoment_pos hM.continuous hdec hnn hy₀ hM₀)⟩
  have hJ := jumpMeasureMoment_pos hM hM0 hdec' hnn hy₀ hM₀
  have hev := (tendsto_foldedSource_div_nhdsGT_zero hM hM0 hdec hdec').eventually
    (gt_mem_nhds (by linarith : -(2 * jumpMeasureMoment M) < 0))
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have h := hsub hx
  simp only [Set.mem_setOf_eq] at h
  rw [div_lt_iff₀ (riemannKernelReal_pos x), zero_mul] at h
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
