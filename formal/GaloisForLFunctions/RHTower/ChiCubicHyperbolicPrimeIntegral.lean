import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimePeriods

/-!
# Integrals on the actual ordered hyperbolic support

Every prime-pair contribution is integrated on its literal sharp support.
Complete bulk cells retain the central ordering hole, while the frozen outer
period cancels exactly. The resulting estimates keep the original amplitude.
-/

noncomputable section

namespace RHTower

open Finset MeasureTheory

/-- The integral of one literal ordered prime-pair contribution. -/
def chiCubicHyperbolicPrimePairIntegral (N : ℝ) (M : ℕ) (pr : ℕ × ℕ) : ℂ :=
  ∫ x in chiCubicHyperbolicPrimeSupport N M pr, chiCubicHyperbolicPrimeAmplitude N pr x

private theorem hyperbolic_support_subset_band (N : ℝ) (M : ℕ) (pr : ℕ × ℕ) :
    chiCubicHyperbolicPrimeSupport N M pr ⊆ Set.Icc N (2 * N) :=
  fun _ hx => ⟨hx.1.1.le, hx.1.2⟩

private theorem gap_pos {p r : ℕ} (hne : p ≠ r) : 0 < |(p : ℝ) - r| :=
  abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))

private theorem hyperbolic_support_subset_outer (N : ℝ) (M : ℕ) {p r : ℕ}
    (hne : p ≠ r) :
    chiCubicHyperbolicPrimeSupport N M (p, r) ⊆
      Set.Icc ((r : ℝ) - (M : ℝ) * r / |(p : ℝ) - r|)
        ((r : ℝ) + (M : ℝ) * r / |(p : ℝ) - r|) := by
  intro x hx
  have hrad : |x - r| ≤ (M : ℝ) * r / |(p : ℝ) - r| :=
    (le_div_iff₀ (gap_pos hne)).2 (by simpa [mul_comm] using hx.2.2)
  have h := abs_le.1 hrad
  exact ⟨by linarith, by linarith⟩

/-- Every actual pair integral is defined by an integrable amplitude. -/
theorem integrableOn_chiCubicHyperbolicPrimePair {N : ℝ} (hN : 1 < N)
    (M : ℕ) (pr : ℕ × ℕ) :
    IntegrableOn (chiCubicHyperbolicPrimeAmplitude N pr)
      (chiCubicHyperbolicPrimeSupport N M pr) volume :=
  (chiCubicHyperbolicPrimeAmplitude_continuousOn hN pr).integrableOn_Icc.mono_set
    (hyperbolic_support_subset_band N M pr)

/-- Exact finite integral decomposition of the original continuous kernel. -/
theorem chiCubicHyperbolicPrimeKernel_integral_eq {N : ℝ} (hN : 1 < N) (M : ℕ) :
    (∫ x in Set.Icc N (2 * N), chiCubicHyperbolicPrimeKernel N M x) =
      ∑ pr ∈ ((primeProfileBand N).product (primeProfileBand N)).filter
        (fun pr => pr.1 ≠ pr.2), chiCubicHyperbolicPrimePairIntegral N M pr := by
  classical
  unfold chiCubicHyperbolicPrimeKernel
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro pr _
    rw [setIntegral_indicator (chiCubicHyperbolicPrimeSupport_measurable N M pr),
      Set.inter_eq_right.mpr (hyperbolic_support_subset_band N M pr)]
    rfl
  · intro pr _
    exact (chiCubicHyperbolicPrimeAmplitude_continuousOn hN pr).integrableOn_Icc.indicator
      (chiCubicHyperbolicPrimeSupport_measurable N M pr)

/-- Cells whose gap already exceeds the hyperbolic radius are empty. -/
theorem chiCubicHyperbolicPrimePairIntegral_zero_of_inactive (N : ℝ) (M : ℕ)
    {p r : ℕ} (hne : p ≠ r)
    (hinactive : (M : ℝ) * r < |(p : ℝ) - r| ^ 2) :
    chiCubicHyperbolicPrimePairIntegral N M (p, r) = 0 := by
  have hs : chiCubicHyperbolicPrimeSupport N M (p, r) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have h := mul_lt_mul_of_pos_left hx.2.1 (gap_pos hne)
    nlinarith [hx.2.2]
  simp [chiCubicHyperbolicPrimePairIntegral, hs]

/-- Support length controls every actual pair integral, including cells cut by
the original band endpoints. -/
theorem norm_chiCubicHyperbolicPrimePairIntegral_le {N : ℝ} (hN : 1 < N) (M : ℕ)
    {p r : ℕ} (hp : p ∈ primeProfileBand N) (hr : r ∈ primeProfileBand N) (hne : p ≠ r) :
    ‖chiCubicHyperbolicPrimePairIntegral N M (p, r)‖ ≤
      8 * Real.pi * M / (|(p : ℝ) - r| * Real.log N) := by
  let R : ℝ := (M : ℝ) * r / |(p : ℝ) - r|
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN
  have hd := gap_pos hne
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hrN := (primeProfileBand_mem hN0.le hr).2
  have hRle : R ≤ 2 * M * N / |(p : ℝ) - r| := by
    dsimp [R]
    calc
      _ ≤ (M : ℝ) * (2 * N) / |(p : ℝ) - r| := by
        gcongr
        exact hrN.2
      _ = _ := by ring
  have hsub := hyperbolic_support_subset_outer N M hne
  have hvol : volume.real (Set.Icc ((r : ℝ) - R) ((r : ℝ) + R)) = 2 * R := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  have hfinite : volume (chiCubicHyperbolicPrimeSupport N M (p, r)) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) isCompact_Icc.measure_lt_top
  calc
    _ ≤ (2 * Real.pi / (N * Real.log N)) *
        volume.real (chiCubicHyperbolicPrimeSupport N M (p, r)) :=
      norm_setIntegral_le_of_norm_le_const hfinite (fun x hx =>
        norm_chiCubicHyperbolicPrimeAmplitude_le hN hp hr
          (hyperbolic_support_subset_band N M (p, r) hx))
    _ ≤ (2 * Real.pi / (N * Real.log N)) *
        volume.real (Set.Icc ((r : ℝ) - R) ((r : ℝ) + R)) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub isCompact_Icc.measure_lt_top.ne)
        (by positivity)
    _ = (2 * Real.pi / (N * Real.log N)) * (2 * R) := by rw [hvol]
    _ ≤ (2 * Real.pi / (N * Real.log N)) *
        (2 * (2 * M * N / |(p : ℝ) - r|)) := by gcongr
    _ = _ := by field_simp; ring

private theorem hyperbolic_support_eq_outer_sdiff_inner {N : ℝ} (M : ℕ)
    {p r : ℕ} (hne : p ≠ r)
    (hleft : N < (r : ℝ) - (M : ℝ) * r / |(p : ℝ) - r|)
    (hright : (r : ℝ) + (M : ℝ) * r / |(p : ℝ) - r| ≤ 2 * N) :
    chiCubicHyperbolicPrimeSupport N M (p, r) =
      Set.Icc ((r : ℝ) - (M : ℝ) * r / |(p : ℝ) - r|)
        ((r : ℝ) + (M : ℝ) * r / |(p : ℝ) - r|) \
      Set.Icc ((r : ℝ) - |(p : ℝ) - r|) ((r : ℝ) + |(p : ℝ) - r|) := by
  ext x
  constructor
  · intro hx
    refine ⟨hyperbolic_support_subset_outer N M hne hx, ?_⟩
    intro hi
    have hbound : |x - r| ≤ |(p : ℝ) - r| := abs_le.2 ⟨by linarith [hi.1], by linarith [hi.2]⟩
    exact (not_lt_of_ge hbound) hx.2.1
  · rintro ⟨hx, hi⟩
    have hg : |(p : ℝ) - r| < |x - r| := by
      by_contra h
      have hb := abs_le.1 (le_of_not_gt h)
      exact hi ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have hrad : |x - r| ≤ (M : ℝ) * r / |(p : ℝ) - r| :=
      abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
    refine ⟨⟨hleft.trans_le hx.1, hx.2.trans hright⟩, hg, ?_⟩
    simpa [mul_comm] using (le_div_iff₀ (gap_pos hne)).1 hrad

/-- Exact outer-minus-hole identity on each complete active bulk cell. -/
theorem chiCubicHyperbolicPrimePairIntegral_bulk_eq {N : ℝ} (hN : 1 < N) (M : ℕ)
    {p r : ℕ} (hne : p ≠ r)
    (hleft : N < (r : ℝ) - (M : ℝ) * r / |(p : ℝ) - r|)
    (hright : (r : ℝ) + (M : ℝ) * r / |(p : ℝ) - r| ≤ 2 * N)
    (hactive : |(p : ℝ) - r| ≤ (M : ℝ) * r / |(p : ℝ) - r|) :
    chiCubicHyperbolicPrimePairIntegral N M (p, r) =
      (∫ x in Set.Icc ((r : ℝ) - (M : ℝ) * r / |(p : ℝ) - r|)
        ((r : ℝ) + (M : ℝ) * r / |(p : ℝ) - r|), chiCubicHyperbolicPrimeAmplitude N (p, r) x) -
      ∫ x in Set.Icc ((r : ℝ) - |(p : ℝ) - r|) ((r : ℝ) + |(p : ℝ) - r|),
        chiCubicHyperbolicPrimeAmplitude N (p, r) x := by
  rw [chiCubicHyperbolicPrimePairIntegral, hyperbolic_support_eq_outer_sdiff_inner M hne hleft hright]
  apply setIntegral_sdiff measurableSet_Icc
  · exact (chiCubicHyperbolicPrimeAmplitude_continuousOn hN (p, r)).integrableOn_Icc.mono_set
      (fun x hx => ⟨hleft.le.trans hx.1, hx.2.trans hright⟩)
  · intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Actual bulk cancellation after retaining the complete ordering hole. The
constant comes from the literal profile, not from an amplitude hypothesis. -/
theorem exists_chiCubicHyperbolicPrimePairIntegral_bulk_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 < N → 1 ≤ Real.log N → ∀ M : ℕ,
      ∀ p ∈ primeProfileBand N, ∀ r ∈ primeProfileBand N, p ≠ r →
      N < (r : ℝ) - (M : ℝ) * r / |(p : ℝ) - r| →
      (r : ℝ) + (M : ℝ) * r / |(p : ℝ) - r| ≤ 2 * N →
      ‖chiCubicHyperbolicPrimePairIntegral N M (p, r)‖ ≤
        C * (M : ℝ) ^ 2 / (|(p : ℝ) - r| ^ 2 * Real.log N) +
          4 * Real.pi * |(p : ℝ) - r| / (N * Real.log N) := by
  obtain ⟨C, hC, hf⟩ := exists_chiCubicHyperbolicPrimeAmplitude_freeze
  refine ⟨8 * C, by positivity, ?_⟩
  intro N hN hlog M p hp r hr hne hleft hright
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := by linarith
  let d := |(p : ℝ) - r|
  let R : ℝ := (M : ℝ) * r / d
  have hd : 0 < d := gap_pos hne
  have hR : 0 ≤ R := by dsimp [R, d]; positivity
  by_cases hactive : d ≤ R
  swap
  · have hinactive : (M : ℝ) * r < |(p : ℝ) - r| ^ 2 := by
      have h := (div_lt_iff₀ hd).1 (lt_of_not_ge hactive)
      nlinarith
    rw [chiCubicHyperbolicPrimePairIntegral_zero_of_inactive N M hne hinactive, norm_zero]
    positivity
  have houter : Set.Icc ((r : ℝ) - R) ((r : ℝ) + R) ⊆ Set.Icc N (2 * N) :=
    fun _ hx => ⟨hleft.le.trans hx.1, hx.2.trans hright⟩
  have hinner : Set.Icc ((r : ℝ) - d) ((r : ℝ) + d) ⊆ Set.Icc N (2 * N) := by
    intro x hx
    apply houter
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  let F := fun x : ℝ => chiCubicHyperbolicPrimeAmplitude N (p, r) r *
    bourgainOscillation (2 * Real.pi * (((p : ℝ) - r) * (x - r) / r))
  have hFi : IntegrableOn F (Set.Icc ((r : ℝ) - R) ((r : ℝ) + R)) volume := by
    have hFc : Continuous F := by dsimp [F]; unfold bourgainOscillation; fun_prop
    exact hFc.continuousOn.integrableOn_Icc
  have hAi : IntegrableOn (chiCubicHyperbolicPrimeAmplitude N (p, r))
      (Set.Icc ((r : ℝ) - R) ((r : ℝ) + R)) volume :=
    (chiCubicHyperbolicPrimeAmplitude_continuousOn hN (p, r)).integrableOn_Icc.mono_set houter
  have hzero : (∫ x in Set.Icc ((r : ℝ) - R) ((r : ℝ) + R), F x) = 0 :=
    chiCubicHyperbolicPrimeAmplitude_frozen_period N M p r
  have herr : ‖∫ x in Set.Icc ((r : ℝ) - R) ((r : ℝ) + R),
        chiCubicHyperbolicPrimeAmplitude N (p, r) x‖ ≤
      (C / (N ^ 2 * Real.log N) * R) * (2 * R) := by
    have hb : ∀ x ∈ Set.Icc ((r : ℝ) - R) ((r : ℝ) + R),
        ‖chiCubicHyperbolicPrimeAmplitude N (p, r) x - F x‖ ≤ C / (N ^ 2 * Real.log N) * R := by
      intro x hx
      exact (hf N hN hlog p hp r hr x (houter hx)).trans
        (mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩) (by positivity))
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) isCompact_Icc.measure_lt_top hb
    rw [integral_sub hAi hFi, hzero, sub_zero,
      Real.volume_real_Icc_of_le (by linarith)] at h
    convert h using 1; ring
  have hRle : R ≤ 2 * M * N / d := by
    have hrN := (primeProfileBand_mem hN0.le hr).2.2
    dsimp [R]
    calc
      _ ≤ (M : ℝ) * (2 * N) / d := by gcongr
      _ = _ := by ring
  have hout : ‖∫ x in Set.Icc ((r : ℝ) - R) ((r : ℝ) + R),
        chiCubicHyperbolicPrimeAmplitude N (p, r) x‖ ≤
      (8 * C) * (M : ℝ) ^ 2 / (d ^ 2 * Real.log N) := by
    calc
      _ ≤ (C / (N ^ 2 * Real.log N) * R) * (2 * R) := herr
      _ ≤ (C / (N ^ 2 * Real.log N) * (2 * M * N / d)) *
          (2 * (2 * M * N / d)) := by gcongr
      _ = _ := by field_simp; ring
  have hin : ‖∫ x in Set.Icc ((r : ℝ) - d) ((r : ℝ) + d),
        chiCubicHyperbolicPrimeAmplitude N (p, r) x‖ ≤
      4 * Real.pi * d / (N * Real.log N) := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Set.Icc ((r : ℝ) - d) ((r : ℝ) + d)) isCompact_Icc.measure_lt_top
      (fun x hx => norm_chiCubicHyperbolicPrimeAmplitude_le hN hp hr (hinner hx))
    rw [Real.volume_real_Icc_of_le (by linarith)] at h
    convert h using 1; ring
  rw [chiCubicHyperbolicPrimePairIntegral_bulk_eq hN M hne hleft hright hactive]
  exact (norm_sub_le _ _).trans (add_le_add hout hin)

end RHTower
