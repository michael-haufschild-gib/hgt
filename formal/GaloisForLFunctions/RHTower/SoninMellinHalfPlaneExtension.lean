import GaloisForLFunctions.RHTower.SoninTruncatedMellinFamily

/-!
# The Mellin transform of a Sonine vector continues holomorphically past the critical line

For `f` in the Sonine carrier `K_a` the truncated Mellin transforms `∫_a^T t^{-s} f(t) dt` are
entire in `s` and form a locally uniform Cauchy family on the half plane `Re s > 0` — with the
uniform-in-`T` decay supplied by one integration by parts against the frequency tail of `f`.  Their
limit is therefore holomorphic on `Re s > 0`, which is strictly larger than the half plane
`Re s > 1/2` of absolute convergence.  This is the analytic half of the de Branges entirety theorem
(Burnol, arXiv:math/0203120, Thm. 2.1); the reflected statement on `Re s < 1` and the weld across
the critical line follow from the Fourier–Mellin functional equation.

## Main results

* `soninMellinExtension` — the extension.
* `differentiableOn_soninMellinExtension` — holomorphy on `{Re s > 0}`.
* `tendsto_soninTruncMellin_soninMellinExtension` — it is the limit of the truncations.
-/

noncomputable section

open MeasureTheory Set Complex Real Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- A negative power is antitone in the base. -/
theorem rpow_neg_le_rpow_neg_of_le {x y c : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hc : 0 ≤ c) :
    y ^ (-c) ≤ x ^ (-c) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hx]
  refine Real.exp_le_exp.2 ?_
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
  nlinarith [mul_nonneg (sub_nonneg.2 hlog) hc]

/-- The constant in the Cauchy estimate, as a function of the spectral parameter. -/
def soninMellinTailConstant (a : ℝ) (f : SoninL2) (s : ℂ) : ℝ :=
  ((2 + ‖s‖ / s.re) / (2 * Real.pi)) * invAbsTailNorm a * ‖f‖

theorem soninMellinTailConstant_nonneg {a : ℝ} (f : SoninL2) {s : ℂ} (hs : 0 < s.re) :
    0 ≤ soninMellinTailConstant a f s := by
  rw [soninMellinTailConstant]
  have h1 : (0:ℝ) ≤ (2 + ‖s‖ / s.re) / (2 * Real.pi) := by positivity
  have h2 : (0:ℝ) ≤ invAbsTailNorm a := invAbsTailNorm_nonneg a
  positivity

/-- The Cauchy estimate in factored form. -/
theorem norm_soninTruncMellin_sub_le' {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) {T T' : ℝ} (haT : a ≤ T) (hTT' : T ≤ T') {s : ℂ}
    (hs : 0 < s.re) :
    ‖soninTruncMellin f a T' s - soninTruncMellin f a T s‖
      ≤ T ^ (-s.re) * soninMellinTailConstant a f s := by
  refine (norm_soninTruncMellin_sub_le ha hf haT hTT' hs).trans (le_of_eq ?_)
  rw [soninMellinTailConstant]
  field_simp

/-- The truncation sequence. -/
def soninMellinSeq (f : SoninL2) (a : ℝ) (n : ℕ) : ℂ → ℂ :=
  soninTruncMellin f a (a + n)

theorem differentiable_soninMellinSeq {a : ℝ} (ha : 0 < a) (f : SoninL2) (n : ℕ) :
    Differentiable ℂ (soninMellinSeq f a n) := by
  refine differentiable_soninTruncMellin ha ?_ f
  have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem cauchySeq_soninMellinSeq {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) {s : ℂ} (hs : 0 < s.re) :
    CauchySeq fun n : ℕ => soninMellinSeq f a n s := by
  refine cauchySeq_of_le_tendsto_0
    (fun N : ℕ => (a + N) ^ (-s.re) * soninMellinTailConstant a f s) ?_ ?_
  · intro n m N hn hm
    have hgen : ∀ p q : ℕ, N ≤ p → p ≤ q →
        dist (soninMellinSeq f a p s) (soninMellinSeq f a q s)
          ≤ (a + N) ^ (-s.re) * soninMellinTailConstant a f s := by
      intro p q hNp hpq
      have hap : a ≤ a + (p : ℝ) := by have := Nat.cast_nonneg (α := ℝ) p; linarith
      have hpq' : a + (p : ℝ) ≤ a + (q : ℝ) := by
        have : (p : ℝ) ≤ (q : ℝ) := Nat.cast_le.2 hpq
        linarith
      have hb := norm_soninTruncMellin_sub_le' ha hf hap hpq' hs
      have hd : dist (soninMellinSeq f a p s) (soninMellinSeq f a q s)
          = ‖soninTruncMellin f a (a + (q : ℝ)) s - soninTruncMellin f a (a + (p : ℝ)) s‖ := by
        rw [dist_eq_norm, soninMellinSeq, soninMellinSeq, ← norm_neg]
        ring_nf
      rw [hd]
      refine hb.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (soninMellinTailConstant_nonneg f hs)
      refine rpow_neg_le_rpow_neg_of_le (by linarith [Nat.cast_nonneg (α := ℝ) N]) ?_ hs.le
      have : (N : ℝ) ≤ (p : ℝ) := Nat.cast_le.2 hNp
      linarith
    rcases le_total n m with h | h
    · exact hgen n m hn h
    · rw [dist_comm]
      exact hgen m n hm h
  · have hbase : Tendsto (fun N : ℕ => (a + (N : ℝ)) ^ (-s.re)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => a + (N : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_left _ a tendsto_natCast_atTop_atTop
      exact (tendsto_rpow_neg_atTop hs).comp h1
    simpa using hbase.mul_const (soninMellinTailConstant a f s)

/-- The holomorphic continuation of the Mellin transform of a Sonine vector to `Re s > 0`. -/
def soninMellinExtension (f : SoninL2) (a : ℝ) (s : ℂ) : ℂ :=
  limUnder atTop fun n : ℕ => soninMellinSeq f a n s

theorem tendsto_soninMellinSeq {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => soninMellinSeq f a n s) atTop (𝓝 (soninMellinExtension f a s)) :=
  (cauchySeq_soninMellinSeq ha hf hs).tendsto_limUnder

theorem norm_soninMellinExtension_sub_le {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖soninMellinExtension f a s - soninMellinSeq f a n s‖
      ≤ (a + n) ^ (-s.re) * soninMellinTailConstant a f s := by
  have hlim : Tendsto (fun m : ℕ => ‖soninMellinSeq f a m s - soninMellinSeq f a n s‖) atTop
      (𝓝 ‖soninMellinExtension f a s - soninMellinSeq f a n s‖) := by
    exact ((tendsto_soninMellinSeq ha hf hs).sub tendsto_const_nhds).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  have han : a ≤ a + (n : ℝ) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hnm : a + (n : ℝ) ≤ a + (m : ℝ) := by
    have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hm
    linarith
  exact norm_soninTruncMellin_sub_le' ha hf han hnm hs

/-- The truncations converge locally uniformly on the right half plane `Re s > 0`. -/
theorem tendstoLocallyUniformlyOn_soninMellinSeq {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) :
    TendstoLocallyUniformlyOn (fun n : ℕ => soninMellinSeq f a n)
      (soninMellinExtension f a) atTop {s : ℂ | 0 < s.re} := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε s₀ hs₀
  have hs₀re : 0 < s₀.re := hs₀
  set σ₀ : ℝ := s₀.re / 2 with hσ₀
  have hσ₀pos : 0 < σ₀ := by rw [hσ₀]; linarith
  set R : ℝ := ‖s₀‖ + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  set B₀ : ℝ := ((2 + R / σ₀) / (2 * Real.pi)) * invAbsTailNorm a * ‖f‖ with hB₀
  have hB₀0 : 0 ≤ B₀ := by
    have h1 : (0:ℝ) ≤ (2 + R / σ₀) / (2 * Real.pi) := by positivity
    have h2 : (0:ℝ) ≤ invAbsTailNorm a := invAbsTailNorm_nonneg a
    rw [hB₀]
    positivity
  refine ⟨{s : ℂ | σ₀ < s.re} ∩ Metric.ball s₀ 1, ?_, ?_⟩
  · refine mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds ?_ ?_)
    · exact (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
    · refine ⟨?_, Metric.mem_ball_self one_pos⟩
      simp only [Set.mem_setOf_eq, hσ₀]
      linarith
  · have hbase : Tendsto (fun n : ℕ => (a + (n : ℝ)) ^ (-σ₀) * B₀) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => a + (n : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_left _ a tendsto_natCast_atTop_atTop
      simpa using ((tendsto_rpow_neg_atTop hσ₀pos).comp h1).mul_const B₀
    have hev1 : ∀ᶠ n : ℕ in atTop, (a + (n : ℝ)) ^ (-σ₀) * B₀ < ε :=
      hbase.eventually (gt_mem_nhds hε)
    have hev2 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ a + (n : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    filter_upwards [hev1, hev2] with n hn1 hn2
    intro y hy
    have hyre : σ₀ < y.re := hy.1
    have hy0 : 0 < y.re := lt_trans hσ₀pos hyre
    have hynorm : ‖y‖ ≤ R := by
      have hd : ‖y - s₀‖ < 1 := by
        simpa [Complex.dist_eq] using Metric.mem_ball.1 hy.2
      have h3 : ‖y‖ - ‖s₀‖ ≤ ‖y - s₀‖ := norm_sub_norm_le y s₀
      rw [hR]; linarith
    have hb := norm_soninMellinExtension_sub_le ha hf hy0 n
    have h1 : (a + (n : ℝ)) ^ (-y.re) ≤ (a + (n : ℝ)) ^ (-σ₀) :=
      Real.rpow_le_rpow_of_exponent_le hn2 (by linarith)
    have h2 : soninMellinTailConstant a f y ≤ B₀ := by
      rw [soninMellinTailConstant, hB₀]
      have hdiv : ‖y‖ / y.re ≤ R / σ₀ := by gcongr
      have hN : (0:ℝ) ≤ invAbsTailNorm a := invAbsTailNorm_nonneg a
      have hpi : (0:ℝ) < 2 * Real.pi := by positivity
      gcongr
    rw [Complex.dist_eq]
    calc ‖soninMellinExtension f a y - soninMellinSeq f a n y‖
        ≤ (a + (n : ℝ)) ^ (-y.re) * soninMellinTailConstant a f y := hb
      _ ≤ (a + (n : ℝ)) ^ (-σ₀) * B₀ := by
          refine mul_le_mul h1 h2 (soninMellinTailConstant_nonneg f hy0) ?_
          exact Real.rpow_nonneg (by linarith) _
      _ < ε := hn1

/-- **The Mellin transform of a Sonine vector is holomorphic on `Re s > 0`.** -/
theorem differentiableOn_soninMellinExtension {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) :
    DifferentiableOn ℂ (soninMellinExtension f a) {s : ℂ | 0 < s.re} := by
  refine TendstoLocallyUniformlyOn.differentiableOn
    (tendstoLocallyUniformlyOn_soninMellinSeq ha hf) ?_
    (isOpen_lt continuous_const Complex.continuous_re)
  filter_upwards with n
  exact (differentiable_soninMellinSeq ha f n).differentiableOn

/-- The union of the truncation windows is the whole ray beyond the aperture. -/
theorem iUnion_Ioo_add_nat (a : ℝ) : (⋃ n : ℕ, Set.Ioo a (a + (n : ℝ))) = Set.Ioi a := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · rintro ⟨n, hn, -⟩
    exact hn
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt (x - a)
    exact ⟨n, hx, by linarith⟩

/-- On the half plane of absolute convergence the extension is the Mellin integral itself. -/
theorem soninMellinExtension_eq_soninMellinIntegral {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) {s : ℂ} (hs : 1 / 2 < s.re) :
    soninMellinExtension f a s = soninMellinIntegral f s := by
  have hsupp := physical_indicator_ae_zero_of_mem_centralSoninCarrier hf
  have hzeroae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0 := by
    filter_upwards [hsupp] with t ht hmem
    simpa [Set.indicator_of_mem hmem] using ht
  have hint0 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
      (Set.Ioi (0 : ℝ)) volume := soninMellin_integrableOn ha hsupp hs
  have hintA : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
      (Set.Ioi a) volume := hint0.mono_set (Set.Ioi_subset_Ioi ha.le)
  -- the integral over the band vanishes
  have hband : ∫ t in Set.Ioc (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hzeroae] with t ht hft
    have hmem : t ∈ centralInterval a := by
      rw [centralInterval, Set.mem_Icc]
      exact ⟨by linarith [ht.1, ha], ht.2⟩
    rw [hft hmem, mul_zero]
    rfl
  have hsplit : ∫ t in Set.Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t
      = ∫ t in Set.Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
    have hu : Set.Ioc (0 : ℝ) a ∪ Set.Ioi a = Set.Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi ha.le
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) a) (Set.Ioi a) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx' (not_lt.2 hx.2)
    have := MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
      (hint0.mono_set (fun x hx => lt_of_lt_of_le hx.1 le_rfl)) hintA
    rw [hu] at this
    rw [this, hband, zero_add]
  -- the truncations converge to the integral over the ray
  have hmono : Monotone fun n : ℕ => Set.Ioo a (a + (n : ℝ)) := by
    intro m n hmn
    refine Set.Ioo_subset_Ioo le_rfl ?_
    have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
    linarith
  have htend := MeasureTheory.tendsto_setIntegral_of_monotone
    (μ := (volume : Measure ℝ)) (f := fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
    (s := fun n : ℕ => Set.Ioo a (a + (n : ℝ))) (fun _ => measurableSet_Ioo) hmono
    (by rw [iUnion_Ioo_add_nat]; exact hintA)
  rw [iUnion_Ioo_add_nat] at htend
  have hseq : (fun n : ℕ => ∫ t in Set.Ioo a (a + (n : ℝ)),
      ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t) = fun n : ℕ => soninMellinSeq f a n s := rfl
  rw [hseq] at htend
  have hs0 : 0 < s.re := by linarith
  have := tendsto_nhds_unique (tendsto_soninMellinSeq ha hf hs0) htend
  rw [this, soninMellinIntegral, ← hsplit]

/-- The empty truncation contributes nothing. -/
@[simp] theorem soninMellinSeq_zero (f : SoninL2) (a : ℝ) (s : ℂ) :
    soninMellinSeq f a 0 s = 0 := by
  rw [soninMellinSeq, soninTruncMellin]
  simp

/-- **The continued Mellin evaluation is a bounded functional on the Sonine carrier.**  This is the
continuity half of de Branges' Theorem 2.1 (Burnol, arXiv:math/0203120, Thm. 2.1), and it holds on
the whole half plane `Re s > 0`, past the critical line. -/
theorem norm_soninMellinExtension_le {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) {s : ℂ} (hs : 0 < s.re) :
    ‖soninMellinExtension f a s‖
      ≤ a ^ (-s.re) * (((2 + ‖s‖ / s.re) / (2 * Real.pi)) * invAbsTailNorm a) * ‖f‖ := by
  have h := norm_soninMellinExtension_sub_le ha hf hs 0
  rw [soninMellinSeq_zero, sub_zero] at h
  refine h.trans (le_of_eq ?_)
  rw [soninMellinTailConstant]
  push_cast
  ring

end RHTower
