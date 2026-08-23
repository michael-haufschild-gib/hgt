import GaloisForLFunctions.RHTower.SoninBandSinc
import GaloisForLFunctions.HTGeometry.TruncatedMellinEntire

/-!
# Mellin tails of kernels with inverse-linear decay

A vector of `L²(ℝ)` whose values obey `‖g(t)‖ ≤ C/|t|` has an *absolutely* convergent Mellin tail

`decayTailMellin g T s = ∫_T^∞ g(t) · t^{-s} dt`   (`T > 0`, `Re s > 0`),

holomorphic on the whole right half-plane: no oscillatory cancellation is needed, because the extra
`1/t` already makes the integrand `O(t^{-Re s - 1})`.  The sinc kernel `fourierBandIndicator a` is
the example that matters for the extended Sonine space.

## Main results

* `HasInverseDecay`, `hasInverseDecay_fourierBandIndicator`
* `integrableOn_decayTail`, `norm_decayTail_le`
* `differentiableOn_decayTailMellin` — holomorphy on `Re s > 0`
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- A square-integrable kernel with inverse-linear decay. -/
structure HasInverseDecay (g : SoninL2) (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  bound : ∀ᵐ t ∂(volume : Measure ℝ), ‖(g : ℝ → ℂ) t‖ ≤ C / |t|

theorem hasInverseDecay_fourierBandIndicator {a : ℝ} (ha : 0 < a) :
    HasInverseDecay (fourierBandIndicator a) (1 / Real.pi) where
  nonneg := by positivity
  bound := by
    filter_upwards [norm_coeFn_fourierBandIndicator_le ha] with t ht
    refine ht.trans (le_of_eq ?_)
    rw [one_div, one_div, div_eq_mul_inv, ← mul_inv]

theorem HasInverseDecay.sub {g h : SoninL2} {C D : ℝ}
    (hg : HasInverseDecay g C) (hh : HasInverseDecay h D) :
    HasInverseDecay (g - h) (C + D) where
  nonneg := by linarith [hg.nonneg, hh.nonneg]
  bound := by
    filter_upwards [hg.bound, hh.bound, Lp.coeFn_sub g h] with t h1 h2 h3
    rw [h3, Pi.sub_apply]
    refine (norm_sub_le _ _).trans ?_
    rw [add_div]
    exact add_le_add h1 h2

/-- The Mellin tail. -/
def decayTailMellin (g : SoninL2) (T : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi T, (g : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s)

/-- The truncated Mellin tails. -/
def decayTailMellinSeq (g : SoninL2) (T : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Ioo T (T + (n : ℝ)), (g : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s)

theorem norm_decayKernel_mul_cpow_le {g : SoninL2} {C : ℝ} (hg : HasInverseDecay g C)
    {T : ℝ} (hT : 0 < T) (s : ℂ) :
    ∀ᵐ t ∂(volume.restrict (Ioi T)),
      ‖(g : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s)‖ ≤ C * t ^ (-s.re - 1) := by
  filter_upwards [ae_restrict_of_ae hg.bound, ae_restrict_mem measurableSet_Ioi] with t ht hmem
  have htpos : 0 < t := lt_trans hT hmem
  have habs : |t| = t := abs_of_pos htpos
  rw [habs] at ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re]
  have h2 : (0 : ℝ) < t ^ (-s.re) := Real.rpow_pos_of_pos htpos _
  have h3 : C * t ^ (-s.re - 1) = (C / t) * t ^ (-s.re) := by
    rw [Real.rpow_sub htpos, Real.rpow_one]
    field_simp
  rw [h3]
  exact mul_le_mul_of_nonneg_right ht h2.le

theorem integrableOn_rpow_tail {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Ioi T) volume :=
  integrableOn_Ioi_rpow_of_lt (by linarith) hT

theorem integral_rpow_tail {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    (∫ t in Ioi T, t ^ (-σ - 1)) = T ^ (-σ) / σ := by
  rw [integral_Ioi_rpow_of_lt (by linarith) hT]
  have h : -σ - 1 + 1 = -σ := by ring
  rw [h]
  field_simp

theorem integrableOn_decayTail {g : SoninL2} {C : ℝ} (hg : HasInverseDecay g C)
    {T : ℝ} (hT : 0 < T) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (g : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s)) (Ioi T) volume := by
  have hmaj : IntegrableOn (fun t : ℝ => C * t ^ (-s.re - 1)) (Ioi T) volume :=
    (integrableOn_rpow_tail hs hT).const_mul _
  refine Integrable.mono' hmaj ?_ (norm_decayKernel_mul_cpow_le hg hT s)
  refine ((Lp.aestronglyMeasurable g).restrict).mul ?_
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const t (-s)
    (Or.inr (ne_of_gt (lt_trans hT ht)))).continuousWithinAt

/-- **The uniform tail bound.** -/
theorem norm_decayTail_le {g : SoninL2} {C : ℝ} (hg : HasInverseDecay g C)
    {T : ℝ} (hT : 0 < T) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Ioi T, (g : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s)‖ ≤ C * (T ^ (-s.re) / s.re) := by
  have hmaj : IntegrableOn (fun t : ℝ => C * t ^ (-s.re - 1)) (Ioi T) volume :=
    (integrableOn_rpow_tail hs hT).const_mul _
  have h := norm_integral_le_of_norm_le hmaj (norm_decayKernel_mul_cpow_le hg hT s)
  refine h.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_rpow_tail hs hT]

theorem integrableOn_decayKernel_Ioo {g : SoninL2} {C : ℝ} (hg : HasInverseDecay g C)
    {T : ℝ} (hT : 0 < T) (b : ℝ) :
    IntegrableOn (g : ℝ → ℂ) (Ioo T b) volume := by
  have hfin : IntegrableOn (fun _ : ℝ => (C / T : ℝ)) (Ioo T b) volume :=
    integrableOn_const measure_Ioo_lt_top.ne
  refine Integrable.mono' hfin ((Lp.aestronglyMeasurable g).restrict) ?_
  filter_upwards [ae_restrict_of_ae hg.bound, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  have htpos : 0 < t := lt_trans hT hmem.1
  have habs : |t| = t := abs_of_pos htpos
  rw [habs] at ht
  refine ht.trans ?_
  exact div_le_div_of_nonneg_left hg.nonneg hT (le_of_lt hmem.1)

theorem differentiable_decayTailMellinSeq {g : SoninL2} {C : ℝ} (hg : HasInverseDecay g C)
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    Differentiable ℂ (decayTailMellinSeq g T n) := by
  have hab : T ≤ T + (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact differentiable_truncatedMellin hT hab (integrableOn_decayKernel_Ioo hg hT (T + (n : ℝ)))

theorem decayTailMellin_sub_seq {g : SoninL2} {C : ℝ} (hg : HasInverseDecay g C)
    {T : ℝ} (hT : 0 < T) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    decayTailMellin g T s - decayTailMellinSeq g T n s
      = ∫ t in Ioi (T + (n : ℝ)), (g : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s) := by
  have hab : T ≤ T + (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hint1 : IntegrableOn (fun t : ℝ => (g : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s))
      (Ioc T (T + (n : ℝ))) volume :=
    (integrableOn_decayTail hg hT hs).mono_set Set.Ioc_subset_Ioi_self
  have hint2 : IntegrableOn (fun t : ℝ => (g : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s))
      (Ioi (T + (n : ℝ))) volume := integrableOn_decayTail hg (lt_of_lt_of_le hT hab) hs
  have hunion : Set.Ioc T (T + (n : ℝ)) ∪ Set.Ioi (T + (n : ℝ)) = Set.Ioi T :=
    Set.Ioc_union_Ioi_eq_Ioi hab
  have hsplit : (∫ t in Ioi T, (g : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s))
      = (∫ t in Ioc T (T + (n : ℝ)), (g : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s))
        + ∫ t in Ioi (T + (n : ℝ)), (g : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s) := by
    rw [← hunion]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint1 hint2
  rw [decayTailMellin, decayTailMellinSeq, hsplit, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  ring

theorem norm_decayTailMellin_sub_seq_le {g : SoninL2} {C : ℝ} (hg : HasInverseDecay g C)
    {T : ℝ} (hT : 0 < T) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖decayTailMellin g T s - decayTailMellinSeq g T n s‖
      ≤ C * ((T + (n : ℝ)) ^ (-s.re) / s.re) := by
  have hab : T ≤ T + (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [decayTailMellin_sub_seq hg hT hs n]
  exact norm_decayTail_le hg (lt_of_lt_of_le hT hab) hs

theorem tendstoLocallyUniformlyOn_decayTailMellinSeq {g : SoninL2} {C : ℝ}
    (hg : HasInverseDecay g C) {T : ℝ} (hT : 0 < T) :
    TendstoLocallyUniformlyOn (fun n : ℕ => decayTailMellinSeq g T n) (decayTailMellin g T)
      atTop {s : ℂ | 0 < s.re} := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε s₀ hs₀
  have hs₀re : 0 < s₀.re := hs₀
  set σ₀ : ℝ := s₀.re / 2 with hσ₀
  have hσ₀pos : 0 < σ₀ := by rw [hσ₀]; linarith
  refine ⟨{s : ℂ | σ₀ < s.re}, ?_, ?_⟩
  · refine mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds ?_ ?_)
    · exact isOpen_lt continuous_const Complex.continuous_re
    · simp only [Set.mem_setOf_eq, hσ₀]
      linarith
  · have hbase : Tendsto (fun n : ℕ => C * ((T + (n : ℝ)) ^ (-σ₀) / σ₀)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => T + (n : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_left _ T tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun n : ℕ => (T + (n : ℝ)) ^ (-σ₀)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop hσ₀pos).comp h1
      simpa using (h2.div_const σ₀).const_mul C
    have hev1 : ∀ᶠ n : ℕ in atTop, C * ((T + (n : ℝ)) ^ (-σ₀) / σ₀) < ε :=
      hbase.eventually (gt_mem_nhds hε)
    have hev2 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ T + (n : ℝ) := by
      filter_upwards [eventually_ge_atTop ⌈(1 : ℝ)⌉₊] with n hn
      have h1 : ((⌈(1 : ℝ)⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
      have h2 : (1 : ℝ) ≤ (⌈(1 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      linarith
    filter_upwards [hev1, hev2] with n hn1 hn2
    intro y hy
    have hyre : σ₀ < y.re := hy
    have hy0 : 0 < y.re := lt_trans hσ₀pos hyre
    have h1 : (T + (n : ℝ)) ^ (-y.re) ≤ (T + (n : ℝ)) ^ (-σ₀) :=
      Real.rpow_le_rpow_of_exponent_le hn2 (by linarith)
    have h2 : (T + (n : ℝ)) ^ (-y.re) / y.re ≤ (T + (n : ℝ)) ^ (-σ₀) / σ₀ := by
      have hpos : (0 : ℝ) < (T + (n : ℝ)) ^ (-y.re) := Real.rpow_pos_of_pos (by linarith) _
      have hpos2 : (0 : ℝ) < (T + (n : ℝ)) ^ (-σ₀) := Real.rpow_pos_of_pos (by linarith) _
      gcongr
    rw [Complex.dist_eq]
    calc ‖decayTailMellin g T y - decayTailMellinSeq g T n y‖
        ≤ C * ((T + (n : ℝ)) ^ (-y.re) / y.re) := norm_decayTailMellin_sub_seq_le hg hT hy0 n
      _ ≤ C * ((T + (n : ℝ)) ^ (-σ₀) / σ₀) := mul_le_mul_of_nonneg_left h2 hg.nonneg
      _ < ε := hn1

/-- **A Mellin tail with inverse-linear decay is holomorphic on the right half-plane.** -/
theorem differentiableOn_decayTailMellin {g : SoninL2} {C : ℝ} (hg : HasInverseDecay g C)
    {T : ℝ} (hT : 0 < T) :
    DifferentiableOn ℂ (decayTailMellin g T) {s : ℂ | 0 < s.re} := by
  refine TendstoLocallyUniformlyOn.differentiableOn
    (tendstoLocallyUniformlyOn_decayTailMellinSeq hg hT) ?_
    (isOpen_lt continuous_const Complex.continuous_re)
  filter_upwards with n
  exact (differentiable_decayTailMellinSeq hg hT n).differentiableOn

end RHTower

end
