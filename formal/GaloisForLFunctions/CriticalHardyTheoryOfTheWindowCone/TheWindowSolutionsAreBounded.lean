import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilRieszVectorsLocalizeToTheLogarithmicHalfLine

/-!
# Window solutions are bounded, and have an exact edge

Consider the logarithmic equation on a window `[−a, a]`,

  `E(f, u) = ⟨f, g⟩` for all finite-energy `f` supported in the window,

where the forcing is dominated by constants and translates of the solution:
`|g(x)| ≤ C₀ + Σ_j c_j |u(x − ℓ_j)|`. This covers eigenfunctions and Riesz vectors of `W_λ` for every weight, since
the scalar, the bounded convolutions and the jumps of length `log n` are all of this type.

**Theorem** (`exists_ae_norm_le_of_window_equation`). Every such energy solution is essentially bounded.

The Green operator does not map `L²` to `L^∞`, because the causal kernel `K` is not square integrable. But `K` is
integrable and antitone, so it splits as a part `K 1_{(0,ε)}` of small mass and a bounded part. The bounded part
maps `L¹` to `L^∞`, and the small part is absorbed in `L¹` after truncating at a high level.

**Theorem** (`tendsto_window_left_edge`, `tendsto_window_right_edge`). Consequently the forcing of each endpoint
localization is bounded, and the solution has the exact edge law

  `u(−a + t) √log(1/t) → ∫ K f_L`,   `u(a − t) √log(1/t) → ∫ K f_R`,

with `f_L`, `f_R` the localized forcings. The factor is the half-line factor with constant one, on every window,
for every weight.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower CanonicalSystemOfTheWindowTower HTGeometry

/-! ### Causal averages -/

/-- The causal kernel as a density. -/
def causalDensity (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (logarithmicCausalKernel x)

theorem measurable_causalDensity : Measurable causalDensity :=
  ENNReal.measurable_ofReal.comp measurable_logarithmicCausalKernel

theorem lintegral_causalDensity : ∫⁻ x, causalDensity x = 1 := by
  obtain ⟨hi, hm⟩ := logarithmicCausalKernel_mass_one
  unfold causalDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall logarithmicCausalKernel_nonneg),
    hm, ENNReal.ofReal_one]

theorem causalDensity_of_nonpos {x : ℝ} (hx : x ≤ 0) : causalDensity x = 0 := by
  unfold causalDensity
  rw [logarithmicCausalKernel_of_nonpos hx, ENNReal.ofReal_zero]

/-- Forward average: `(A₊ h)(x) = ∫ k(r) h(x + r) dr`. -/
def fwdAvg (k h : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ := ∫⁻ r, k r * h (x + r)

/-- Backward average: `(A₋ h)(x) = ∫ k(t) h(x − t) dt`. -/
def bwdAvg (k h : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ := ∫⁻ t, k t * h (x - t)

theorem measurable_fwdAvg {k h : ℝ → ℝ≥0∞} (hk : Measurable k) (hh : Measurable h) :
    Measurable (fwdAvg k h) :=
  Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ => k p.2 * h (p.1 + p.2))
    ((hk.comp measurable_snd).mul (hh.comp (measurable_fst.add measurable_snd)))

theorem measurable_bwdAvg {k h : ℝ → ℝ≥0∞} (hk : Measurable k) (hh : Measurable h) :
    Measurable (bwdAvg k h) :=
  Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ => k p.2 * h (p.1 - p.2))
    ((hk.comp measurable_snd).mul (hh.comp (measurable_fst.sub measurable_snd)))

theorem lintegral_fwdAvg {k h : ℝ → ℝ≥0∞} (hk : Measurable k) (hh : Measurable h) :
    ∫⁻ x, fwdAvg k h x = (∫⁻ r, k r) * ∫⁻ x, h x := by
  unfold fwdAvg
  rw [lintegral_lintegral_swap (f := fun x r => k r * h (x + r))
    ((hk.comp measurable_snd).mul (hh.comp (measurable_fst.add measurable_snd))).aemeasurable]
  have e : ∀ r, ∫⁻ x, k r * h (x + r) = k r * ∫⁻ x, h x := fun r =>
    (lintegral_const_mul (k r) (hh.comp (measurable_add_const r))).trans
      (by simp only [Function.comp_def]; rw [lintegral_add_right_eq_self h r])
  simp_rw [e]
  rw [lintegral_mul_const _ hk]

theorem lintegral_bwdAvg {k h : ℝ → ℝ≥0∞} (hk : Measurable k) (hh : Measurable h) :
    ∫⁻ x, bwdAvg k h x = (∫⁻ r, k r) * ∫⁻ x, h x := by
  unfold bwdAvg
  rw [lintegral_lintegral_swap (f := fun x r => k r * h (x - r))
    ((hk.comp measurable_snd).mul (hh.comp (measurable_fst.sub measurable_snd))).aemeasurable]
  have e : ∀ r, ∫⁻ x, k r * h (x - r) = k r * ∫⁻ x, h x := fun r =>
    (lintegral_const_mul (k r) (hh.comp (measurable_sub_const r))).trans
      (by simp only [Function.comp_def]; rw [lintegral_sub_right_eq_self h r])
  simp_rw [e]
  rw [lintegral_mul_const _ hk]

theorem fwdAvg_mono (k : ℝ → ℝ≥0∞) {h h' : ℝ → ℝ≥0∞} (hle : ∀ y, h y ≤ h' y) (x : ℝ) :
    fwdAvg k h x ≤ fwdAvg k h' x :=
  lintegral_mono fun _ => by gcongr; exact hle _

theorem bwdAvg_mono (k : ℝ → ℝ≥0∞) {h h' : ℝ → ℝ≥0∞} (hle : ∀ y, h y ≤ h' y) (x : ℝ) :
    bwdAvg k h x ≤ bwdAvg k h' x :=
  lintegral_mono fun _ => by gcongr; exact hle _

theorem fwdAvg_add_const {k : ℝ → ℝ≥0∞} (hk : Measurable k) (h : ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (x : ℝ) : fwdAvg k (fun y => C + h y) x = (∫⁻ r, k r) * C + fwdAvg k h x := by
  unfold fwdAvg
  simp_rw [mul_add]
  rw [lintegral_add_left (hk.mul_const C), lintegral_mul_const _ hk]

theorem bwdAvg_add_const {k : ℝ → ℝ≥0∞} (hk : Measurable k) (h : ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (x : ℝ) : bwdAvg k (fun y => C + h y) x = (∫⁻ r, k r) * C + bwdAvg k h x := by
  unfold bwdAvg
  simp_rw [mul_add]
  rw [lintegral_add_left (hk.mul_const C), lintegral_mul_const _ hk]

/-- The finite sum of translates `Σ_j c_j h(y − ℓ_j)`. -/
def transSum {ι : Type*} (J : Finset ι) (c : ι → ℝ≥0∞) (ℓ : ι → ℝ) (h : ℝ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∑ j ∈ J, c j * h (y - ℓ j)

theorem measurable_transSum {ι : Type*} (J : Finset ι) (c : ι → ℝ≥0∞) (ℓ : ι → ℝ) {h : ℝ → ℝ≥0∞}
    (hh : Measurable h) : Measurable (transSum J c ℓ h) := by
  unfold transSum
  exact Finset.measurable_sum _ fun j _ => (hh.comp (measurable_sub_const _)).const_mul _

theorem lintegral_transSum {ι : Type*} (J : Finset ι) (c : ι → ℝ≥0∞) (ℓ : ι → ℝ) {h : ℝ → ℝ≥0∞}
    (hh : Measurable h) : ∫⁻ y, transSum J c ℓ h y = (∑ j ∈ J, c j) * ∫⁻ y, h y := by
  unfold transSum
  have hm : ∀ j ∈ J, Measurable fun y => c j * h (y - ℓ j) := fun j _ =>
    (hh.comp (measurable_sub_const _)).const_mul _
  rw [lintegral_finsetSum _ hm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (lintegral_const_mul (c j) (hh.comp (measurable_sub_const _))).trans
    (by simp only [Function.comp_def]; rw [lintegral_sub_right_eq_self h])

theorem transSum_le_of_le {ι : Type*} (J : Finset ι) (c : ι → ℝ≥0∞) (ℓ : ι → ℝ) {h v : ℝ → ℝ≥0∞}
    {m : ℝ≥0∞} (hle : ∀ y, h y ≤ v y + m) (y : ℝ) :
    transSum J c ℓ h y ≤ (∑ j ∈ J, c j) * m + transSum J c ℓ v y := by
  unfold transSum
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  calc c j * h (y - ℓ j) ≤ c j * (v (y - ℓ j) + m) := by gcongr; exact hle _
    _ = _ := by rw [mul_add, add_comm]

/-- **Absorption.** If `w` is integrable and `w ≤ C + K̃ K (C₀ + Σ_j c_j τ_j w)` almost everywhere, with the causal
kernel on both sides, then `w` is essentially bounded. The part of `K` near `0` has small mass and is absorbed in
`L¹`; the rest is bounded and maps `L¹` to `L^∞`. -/
theorem exists_ae_le_of_absorption {ι : Type*} {w : ℝ → ℝ≥0∞} (hw : Measurable w)
    (hwf : ∫⁻ x, w x ≠ ∞) (J : Finset ι) {c : ι → ℝ≥0∞} (hc : ∀ j ∈ J, c j ≠ ∞) (ℓ : ι → ℝ)
    {C C₀ : ℝ≥0∞} (hC : C ≠ ∞) (hC₀ : C₀ ≠ ∞)
    (h : ∀ᵐ x, w x ≤ C + bwdAvg causalDensity
      (fwdAvg causalDensity fun y => C₀ + transSum J c ℓ w y) x) :
    ∃ C' : ℝ≥0∞, C' ≠ ∞ ∧ ∀ᵐ x, w x ≤ C' := by
  have hK := measurable_causalDensity
  have hK1 := lintegral_causalDensity
  obtain ⟨M, hM⟩ : ∃ M, M = ∑ j ∈ J, c j := ⟨_, rfl⟩
  have hMf : M ≠ ∞ := by
    rw [hM]
    exact ENNReal.sum_ne_top.mpr hc
  -- the small mass
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ≥0∞, δ = (2 * (M + 1))⁻¹ := ⟨_, rfl⟩
  have hM1 : M + 1 ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hMf, ENNReal.one_ne_top⟩
  have hδ0 : δ ≠ 0 := by
    rw [hδ]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.mul_ne_top (by norm_num) hM1)
  have hδM : δ * M ≤ 2⁻¹ := by
    have h1 : δ * (M + 1) = 2⁻¹ := by
      have hne : M + 1 ≠ 0 := by simp
      rw [hδ, ENNReal.mul_inv (Or.inr hM1) (Or.inr hne), mul_assoc,
        ENNReal.inv_mul_cancel hne hM1, mul_one]
    calc δ * M ≤ δ * (M + 1) := by gcongr; exact le_self_add
      _ = _ := h1
  obtain ⟨ρ, hρ0, hρ⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    (f := causalDensity) (μ := volume) (by rw [hK1]; exact ENNReal.one_ne_top) hδ0
  obtain ⟨ε, hε0, h0lt, hερ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hρ0
  have hε : 0 < ε := ENNReal.ofReal_pos.mp h0lt
  -- the two parts of the kernel
  obtain ⟨k₁, hk₁⟩ : ∃ k₁, k₁ = (Ioc 0 ε).indicator causalDensity := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k₂, k₂ = (Ioi ε).indicator causalDensity := ⟨_, rfl⟩
  have hk₁m : Measurable k₁ := by rw [hk₁]; exact hK.indicator measurableSet_Ioc
  have hk₂m : Measurable k₂ := by rw [hk₂]; exact hK.indicator measurableSet_Ioi
  have hsplit : ∀ t, causalDensity t = k₁ t + k₂ t := by
    intro t
    rw [hk₁, hk₂]
    rcases le_or_gt t 0 with h0 | h0
    · rw [indicator_of_notMem (by simp [h0]), indicator_of_notMem (by
        simp only [mem_Ioi, not_lt]; linarith), causalDensity_of_nonpos h0, add_zero]
    · rcases le_or_gt t ε with h1 | h1
      · have hmem : t ∈ Ioc 0 ε := ⟨h0, h1⟩
        rw [indicator_of_mem hmem, indicator_of_notMem (by simpa using h1), add_zero]
      · have hmem : t ∈ Ioi ε := h1
        rw [indicator_of_notMem (by simp only [mem_Ioc, not_and, not_le]; exact fun _ => h1),
          indicator_of_mem hmem, zero_add]
  have hk₁mass : ∫⁻ t, k₁ t ≤ δ := by
    rw [hk₁, lintegral_indicator measurableSet_Ioc]
    refine (hρ (Ioc 0 ε) ?_).le
    rw [Real.volume_Ioc, sub_zero]
    exact hερ
  obtain ⟨A, hA⟩ : ∃ A, A = causalDensity ε := ⟨_, rfl⟩
  have hAf : A ≠ ∞ := by rw [hA]; exact ENNReal.ofReal_ne_top
  have hk₂bd : ∀ t, k₂ t ≤ A := by
    intro t
    rw [hk₂]
    by_cases ht : t ∈ Ioi ε
    · rw [indicator_of_mem ht, hA]
      have ht' : ε < t := ht
      have hmε : ε ∈ Ioi (0 : ℝ) := hε
      have hmt : t ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (hε.trans ht')
      exact ENNReal.ofReal_le_ofReal (antitoneOn_logarithmicCausalKernel hmε hmt ht'.le)
    · rw [indicator_of_notMem ht]
      exact zero_le _
  have hsm := measurable_transSum J c ℓ hw
  obtain ⟨F, hF⟩ : ∃ F, F = fwdAvg causalDensity (transSum J c ℓ w) := ⟨_, rfl⟩
  have hFm : Measurable F := by rw [hF]; exact measurable_fwdAvg hK hsm
  have hFmass : ∫⁻ y, F y = M * ∫⁻ x, w x := by
    rw [hF, lintegral_fwdAvg hK hsm, hK1, one_mul, lintegral_transSum J c ℓ hw, ← hM]
  obtain ⟨C₃, hC₃⟩ : ∃ C₃, C₃ = C + C₀ + A * (M * ∫⁻ x, w x) := ⟨_, rfl⟩
  have hC₃f : C₃ ≠ ∞ := by
    rw [hC₃]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hC, hC₀⟩,
      ENNReal.mul_ne_top hAf (ENNReal.mul_ne_top hMf hwf)⟩
  -- splitting the double average
  have hfirst : ∀ᵐ x, w x ≤ C₃ + bwdAvg k₁ F x := by
    filter_upwards [h] with x hx
    refine hx.trans ?_
    have e1 : (fwdAvg causalDensity fun y => C₀ + transSum J c ℓ w y) = fun y => C₀ + F y := by
      funext y
      rw [fwdAvg_add_const hK, hK1, one_mul, hF]
    have e2 : bwdAvg causalDensity F x = bwdAvg k₁ F x + bwdAvg k₂ F x := by
      unfold bwdAvg
      have hmeas : Measurable fun t => k₁ t * F (x - t) :=
        hk₁m.mul (hFm.comp (measurable_const.sub measurable_id))
      rw [← lintegral_add_left hmeas]
      refine lintegral_congr fun t => ?_
      rw [hsplit t, add_mul]
    have e3 : bwdAvg k₂ F x ≤ A * (M * ∫⁻ x, w x) := by
      rw [← hFmass, ← lintegral_sub_left_eq_self F x]
      calc bwdAvg k₂ F x ≤ ∫⁻ t, A * F (x - t) :=
            lintegral_mono fun t => by gcongr; exact hk₂bd t
        _ = _ := lintegral_const_mul _ (hFm.comp (measurable_const.sub measurable_id))
    rw [e1, bwdAvg_add_const hK, hK1, one_mul, e2, hC₃]
    calc C + (C₀ + (bwdAvg k₁ F x + bwdAvg k₂ F x))
        = C + C₀ + bwdAvg k₂ F x + bwdAvg k₁ F x := by ring
      _ ≤ C + C₀ + A * (M * ∫⁻ x, w x) + bwdAvg k₁ F x := by gcongr
  -- the truncation
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * C₃ := ⟨_, rfl⟩
  have hmf : m ≠ ∞ := by rw [hm]; exact ENNReal.mul_ne_top (by norm_num) hC₃f
  obtain ⟨v, hv⟩ : ∃ v, v = fun x => w x - m := ⟨_, rfl⟩
  have hvm : Measurable v := by rw [hv]; exact hw.sub measurable_const
  have hwv : ∀ y, w y ≤ v y + m := fun y => by rw [hv]; exact le_tsub_add
  obtain ⟨F', hF'⟩ : ∃ F', F' = fwdAvg causalDensity (transSum J c ℓ v) := ⟨_, rfl⟩
  have hsv := measurable_transSum J c ℓ hvm
  have hF'm : Measurable F' := by rw [hF']; exact measurable_fwdAvg hK hsv
  have hFle : ∀ y, F y ≤ M * m + F' y := by
    intro y
    rw [hF, hF', ← one_mul (M * m), ← hK1, ← fwdAvg_add_const hK]
    refine fwdAvg_mono _ (fun z => ?_) y
    rw [hM]
    exact transSum_le_of_le J c ℓ hwv z
  have hsecond : ∀ x, bwdAvg k₁ F x ≤ C₃ + bwdAvg k₁ F' x := by
    intro x
    have h1 : bwdAvg k₁ F x ≤ (∫⁻ r, k₁ r) * (M * m) + bwdAvg k₁ F' x := by
      rw [← bwdAvg_add_const hk₁m]
      exact bwdAvg_mono _ hFle x
    refine h1.trans ?_
    gcongr
    calc (∫⁻ r, k₁ r) * (M * m) ≤ δ * (M * m) := by gcongr
      _ = (δ * M) * m := by ring
      _ ≤ 2⁻¹ * m := by gcongr
      _ = C₃ := by
          rw [hm, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have hvle : ∀ᵐ x, v x ≤ bwdAvg k₁ F' x := by
    filter_upwards [hfirst] with x hx
    rw [hv]
    refine tsub_le_iff_left.mpr ?_
    calc w x ≤ C₃ + bwdAvg k₁ F x := hx
      _ ≤ C₃ + (C₃ + bwdAvg k₁ F' x) := by gcongr; exact hsecond x
      _ = _ := by rw [hm, ← add_assoc, two_mul]
  -- the absorption in `L¹`
  have hvf : ∫⁻ x, v x ≠ ∞ := by
    refine ne_top_of_le_ne_top hwf (lintegral_mono fun x => ?_)
    rw [hv]
    exact tsub_le_self
  have hint : ∫⁻ x, v x ≤ 2⁻¹ * ∫⁻ x, v x := by
    calc ∫⁻ x, v x ≤ ∫⁻ x, bwdAvg k₁ F' x := lintegral_mono_ae hvle
      _ = (∫⁻ r, k₁ r) * (M * ∫⁻ x, v x) := by
          rw [lintegral_bwdAvg hk₁m hF'm, hF', lintegral_fwdAvg hK hsv, hK1, one_mul,
            lintegral_transSum J c ℓ hvm, ← hM]
      _ ≤ δ * (M * ∫⁻ x, v x) := by gcongr
      _ = (δ * M) * ∫⁻ x, v x := by ring
      _ ≤ 2⁻¹ * ∫⁻ x, v x := by gcongr
  have hzero : ∫⁻ x, v x = 0 := by
    by_contra hne
    have hlt := ENNReal.half_lt_self hne hvf
    rw [div_eq_mul_inv, mul_comm] at hlt
    exact absurd hint (not_le.mpr hlt)
  refine ⟨m, hmf, ?_⟩
  filter_upwards [(lintegral_eq_zero_iff hvm).mp hzero] with x hx
  have : w x - m = 0 := by
    rw [hv] at hx
    exact hx
  exact tsub_eq_zero_iff_le.mp this

/-! ### The Green representative and its forcing -/

theorem enorm_kernel_mul (t : ℝ) (z : ℂ) :
    ‖(logarithmicCausalKernel t : ℂ) * z‖ₑ = causalDensity t * ‖z‖ₑ := by
  rw [enorm_mul]
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg t)]
  rfl

theorem enorm_backward_le (f : ℝ → ℂ) (y : ℝ) :
    ‖logarithmicBackwardConvolution f y‖ₑ ≤ fwdAvg causalDensity (fun z => ‖f z‖ₑ) y := by
  unfold logarithmicBackwardConvolution fwdAvg
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  simp_rw [enorm_kernel_mul]
  rw [← lintegral_add_left_eq_self (fun z => causalDensity (z - y) * ‖f z‖ₑ) y]
  simp only [add_sub_cancel_left]

theorem enorm_rep_le (f : LogarithmicHalfLineL2) (x : ℝ) :
    ‖logarithmicGreenRepresentative f x‖ₑ ≤
      bwdAvg causalDensity (fwdAvg causalDensity fun z => ‖(f : RealLineL2) z‖ₑ) x := by
  unfold logarithmicGreenRepresentative
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  simp_rw [enorm_kernel_mul]
  refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun t => ?_)
  gcongr
  exact enorm_backward_le _ _

private theorem aperture_zero (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∀ᵐ x ∂volume, x ∉ centralInterval a.1 → (f : RealLineL2) x = 0 := by
  have hc := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hc
  filter_upwards [hc] with x hx hn
  rw [hx, indicator_of_notMem hn]

/-- The size of a function on the window, as an `L¹` mass. -/
theorem lintegral_enorm_aperture_ne_top (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∫⁻ x, ‖(f : RealLineL2) x‖ₑ ≠ ∞ := by
  have hms := measurableSet_centralInterval a.1
  have hfin : volume (centralInterval a.1) ≠ ∞ := by
    unfold centralInterval
    exact (isCompact_Icc.measure_lt_top).ne
  haveI : IsFiniteMeasure (volume.restrict (centralInterval a.1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have hint : Integrable (f : RealLineL2) (volume.restrict (centralInterval a.1)) :=
    ((Lp.memLp (f : RealLineL2)).restrict _).integrable (by norm_num)
  have e : ∫⁻ x, ‖(f : RealLineL2) x‖ₑ = ∫⁻ x in centralInterval a.1, ‖(f : RealLineL2) x‖ₑ := by
    rw [← lintegral_indicator hms]
    refine lintegral_congr_ae ?_
    filter_upwards [aperture_zero a f] with x hx
    by_cases hmem : x ∈ centralInterval a.1
    · rw [indicator_of_mem hmem]
    · rw [indicator_of_notMem hmem, hx hmem, enorm_zero]
  rw [e]
  exact hint.hasFiniteIntegral.ne

/-- The forcing of the left localization is the translated forcing plus a bounded commutator term. -/
theorem ae_enorm_leftForcing_le (a : SuzukiPositiveAperture) (u g : suzukiApertureHilbert a) :
    ∀ᵐ y ∂volume, ‖(logarithmicApertureLeftForcing a u g : RealLineL2) y‖ₑ ≤
      ‖(g : RealLineL2) (y - a.1)‖ₑ +
        ENNReal.ofReal (2 / a.1 / 2) * ∫⁻ z, ‖(u : RealLineL2) z‖ₑ := by
  have hLip : 0 ≤ 2 / a.1 := div_nonneg (by norm_num) a.2.le
  obtain ⟨s, hs⟩ : ∃ s : RealLineL2, s = logTranslationCLM (-a.1) (u : RealLineL2) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : RealLineL2, P =
      logarithmicApertureEndpointCutoff a (logTranslationCLM (-a.1) (g : RealLineL2)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : RealLineL2, Q = (logarithmicApertureEndpointCommutator a).op s := ⟨_, rfl⟩
  have hF : ((logarithmicApertureLeftForcing a u g : LogarithmicHalfLineL2) : RealLineL2) =
      indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici (P + Q) := by
    rw [hP, hQ, hs]
    rfl
  have hsz : ∫⁻ z, ‖s z‖ₑ = ∫⁻ z, ‖(u : RealLineL2) z‖ₑ := by
    have ht := logarithmicTranslation_coeFn (-a.1) (u : RealLineL2)
    rw [← hs] at ht
    rw [← lintegral_add_right_eq_self (fun z => ‖(u : RealLineL2) z‖ₑ) (-a.1)]
    refine lintegral_congr_ae (ht.mono fun z hz => ?_)
    change ‖s z‖ₑ = ‖(u : RealLineL2) (z + -a.1)‖ₑ
    rw [hz]
  have hQb : ∀ᵐ y ∂volume, ‖Q y‖ₑ ≤
      ENNReal.ofReal (2 / a.1 / 2) * ∫⁻ z, ‖(u : RealLineL2) z‖ₑ := by
    rw [hQ]
    filter_upwards [(logarithmicApertureEndpointCommutator a).op_coeFn s] with y hy
    rw [hy, ← hsz]
    change ‖∫ z : ℝ, logarithmicCutoffKernel (logarithmicEndpointCutoff a.1) y z * s z‖ₑ ≤ _
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    rw [enorm_mul]
    gcongr
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (norm_logarithmicCutoffKernel_le hLip (logarithmicEndpointCutoff_lipschitz a.2) y z).trans ?_
    have h1 : Real.exp (-|y - z|) ≤ 1 := Real.exp_le_one_iff.mpr (by have := abs_nonneg (y - z); linarith)
    have h2 : 0 ≤ 2 / a.1 / 2 := by positivity
    nlinarith
  have hPb : ∀ᵐ y ∂volume, ‖P y‖ₑ ≤ ‖(g : RealLineL2) (y - a.1)‖ₑ := by
    rw [hP]
    filter_upwards [logarithmicApertureEndpointCutoff_coeFn a
      (logTranslationCLM (-a.1) (g : RealLineL2)),
      logarithmicTranslation_coeFn (-a.1) (g : RealLineL2)] with y h1 h2
    rw [h1, h2, enorm_mul, sub_eq_add_neg]
    have hχ : ‖(logarithmicEndpointCutoff a.1 y : ℂ)‖ₑ ≤ 1 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_one.mpr (logarithmicEndpointCutoff_abs_le a.1 y)
    calc _ ≤ 1 * ‖(g : RealLineL2) (y + -a.1)‖ₑ := by gcongr
      _ = _ := one_mul _
  rw [hF]
  filter_upwards [indicatorCutoff_ae (Ici (0 : ℝ)) measurableSet_Ici (P + Q),
    Lp.coeFn_add P Q, hPb, hQb] with y h1 h2 h3 h4
  rw [h1]
  refine (enorm_indicator_le_enorm_self _ _).trans ?_
  change ‖(P + Q) y‖ₑ ≤ _
  rw [h2, Pi.add_apply]
  exact (enorm_add_le _ _).trans (add_le_add h3 h4)

/-! ### From the equation to the pointwise inequality -/

theorem fwdAvg_mono_ae {k h h' : ℝ → ℝ≥0∞} (hle : ∀ᵐ y ∂volume, h y ≤ h' y) (x : ℝ) :
    fwdAvg k h x ≤ fwdAvg k h' x := by
  have hs := (measurePreserving_add_left (volume : Measure ℝ) x).quasiMeasurePreserving.ae hle
  refine lintegral_mono_ae (hs.mono fun r hr => ?_)
  gcongr

/-- The double causal average. -/
def causalGamma (h : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ := bwdAvg causalDensity (fwdAvg causalDensity h)

theorem causalGamma_mono_ae {h h' : ℝ → ℝ≥0∞} (hle : ∀ᵐ y ∂volume, h y ≤ h' y) (x : ℝ) :
    causalGamma h x ≤ causalGamma h' x :=
  bwdAvg_mono _ (fwdAvg_mono_ae hle) x

/-- **The left half of the window.** The solution near the left edge is dominated by the double causal average of
the forcing. -/
theorem ae_left_bound (a : SuzukiPositiveAperture) (u g : suzukiApertureHilbert a)
    (hu : HasLogarithmicEnergy (u : RealLineL2))
    (hsolve : ∀ f : suzukiApertureHilbert a, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) (u : RealLineL2) =
        inner ℂ (f : RealLineL2) (g : RealLineL2)) :
    ∀ᵐ x ∂volume, x ≤ 0 → ‖(u : RealLineL2) x‖ₑ ≤
      ENNReal.ofReal (2 / a.1 / 2) * (∫⁻ z, ‖(u : RealLineL2) z‖ₑ) +
        causalGamma (fun z => ‖(g : RealLineL2) z‖ₑ) x := by
  have hK := measurable_causalDensity
  have hK1 := lintegral_causalDensity
  obtain ⟨hen, hsol⟩ := logarithmicApertureLeftLocalized_solves a u g hu hsolve
  have hgreen := logarithmicHalfLineGreenOperator_unique _ _ hen hsol
  have hrep := logarithmicHalfLineGreenOperator_eq_representative
    (logarithmicApertureLeftForcing a u g)
  rw [← hgreen] at hrep
  have hcoe := logarithmicApertureLeftLocalized_coeFn a u
  have hboth : ∀ᵐ t ∂volume, logarithmicGreenRepresentative (logarithmicApertureLeftForcing a u g) t =
      (logarithmicEndpointCutoff a.1 t : ℂ) * (u : RealLineL2) (t - a.1) := by
    filter_upwards [hrep, hcoe] with t h1 h2
    rw [← h1, h2]
  have hshift := (measurePreserving_add_right (volume : Measure ℝ) a.1).quasiMeasurePreserving.ae hboth
  obtain ⟨Cu, hCu⟩ : ∃ Cu, Cu = ENNReal.ofReal (2 / a.1 / 2) * (∫⁻ z, ‖(u : RealLineL2) z‖ₑ) := ⟨_, rfl⟩
  rw [← hCu]
  have hgm : Measurable fun z => ‖(g : RealLineL2) z‖ₑ :=
    (Lp.stronglyMeasurable (g : RealLineL2)).measurable.enorm
  filter_upwards [hshift] with x hx hx0
  have hχ : logarithmicEndpointCutoff a.1 (x + a.1) = 1 :=
    logarithmicEndpointCutoff_eq_one a.2 (by linarith)
  rw [hχ, add_sub_cancel_right] at hx
  have hu1 : (u : RealLineL2) x =
      logarithmicGreenRepresentative (logarithmicApertureLeftForcing a u g) (x + a.1) := by
    rw [hx]
    simp
  rw [hu1]
  refine (enorm_rep_le _ _).trans ?_
  have hf := ae_enorm_leftForcing_le a u g
  rw [← hCu] at hf
  -- translating the bound back
  have hmono : ∀ y, fwdAvg causalDensity
      (fun z => ‖(logarithmicApertureLeftForcing a u g : RealLineL2) z‖ₑ) y ≤
      Cu + fwdAvg causalDensity (fun z => ‖(g : RealLineL2) z‖ₑ) (y - a.1) := by
    intro y
    have h1 := fwdAvg_mono_ae (k := causalDensity) (hf.mono fun z hz => by
      rw [add_comm] at hz
      exact hz) y
    refine h1.trans (le_of_eq ?_)
    rw [fwdAvg_add_const hK, hK1, one_mul]
    congr 1
    unfold fwdAvg
    refine lintegral_congr fun r => ?_
    simp only []
    rw [show y + r - a.1 = y - a.1 + r by ring]
  refine (bwdAvg_mono _ hmono _).trans (le_of_eq ?_)
  rw [bwdAvg_add_const hK, hK1, one_mul]
  congr 1
  unfold causalGamma bwdAvg
  refine lintegral_congr fun t => ?_
  simp only []
  rw [show x + a.1 - t - a.1 = x - t by ring]

/-- The double causal average is symmetric under reflection. -/
theorem causalGamma_reflect {G : ℝ → ℝ≥0∞} (hG : Measurable G) (x : ℝ) :
    causalGamma (fun z => G (-z)) (-x) = causalGamma G x := by
  have hK := measurable_causalDensity
  unfold causalGamma bwdAvg fwdAvg
  have h1 : ∀ t, ∫⁻ r, causalDensity r * G (-(-x - t + r)) = ∫⁻ r, causalDensity r * G (x + t - r) := by
    intro t
    refine lintegral_congr fun r => ?_
    rw [show -(-x - t + r) = x + t - r by ring]
  simp_rw [h1]
  have h2 : ∀ t, causalDensity t * ∫⁻ r, causalDensity r * G (x + t - r) =
      ∫⁻ r, causalDensity t * (causalDensity r * G (x + t - r)) := fun t =>
    (lintegral_const_mul _ (hK.mul (hG.comp (measurable_const.sub measurable_id)))).symm
  have h3 : ∀ t, causalDensity t * ∫⁻ r, causalDensity r * G (x - t + r) =
      ∫⁻ r, causalDensity t * (causalDensity r * G (x - t + r)) := fun t =>
    (lintegral_const_mul _ (hK.mul (hG.comp (measurable_const.add measurable_id)))).symm
  simp_rw [h2, h3]
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun r => lintegral_congr fun t => ?_
    rw [show x + t - r = x - r + t by ring]
    ring
  · exact ((hK.comp measurable_fst).mul ((hK.comp measurable_snd).mul
      (hG.comp ((measurable_const.add measurable_fst).sub measurable_snd)))).aemeasurable

/-- **The pointwise inequality on the whole window.** -/
theorem exists_ae_enorm_le_causalGamma (a : SuzukiPositiveAperture) (u g : suzukiApertureHilbert a)
    (hu : HasLogarithmicEnergy (u : RealLineL2))
    (hsolve : ∀ f : suzukiApertureHilbert a, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) (u : RealLineL2) =
        inner ℂ (f : RealLineL2) (g : RealLineL2)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ᵐ x ∂volume, ‖(u : RealLineL2) x‖ₑ ≤
      C + causalGamma (fun z => ‖(g : RealLineL2) z‖ₑ) x := by
  obtain ⟨ur, hur⟩ : ∃ ur, ur = logarithmicApertureReflection a u := ⟨_, rfl⟩
  obtain ⟨gr, hgr⟩ : ∃ gr, gr = logarithmicApertureReflection a g := ⟨_, rfl⟩
  have huu : HasLogarithmicEnergy (ur : RealLineL2) := by
    rw [hur]
    exact hasLogarithmicEnergy_reflection hu
  have hse := logarithmic_interval_equation_reflection a u g hsolve
  rw [← hur, ← hgr] at hse
  have hL := ae_left_bound a u g hu hsolve
  have hR := ae_left_bound a ur gr huu hse
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, C₁ = ENNReal.ofReal (2 / a.1 / 2) * (∫⁻ z, ‖(u : RealLineL2) z‖ₑ) := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂, C₂ = ENNReal.ofReal (2 / a.1 / 2) * (∫⁻ z, ‖(ur : RealLineL2) z‖ₑ) := ⟨_, rfl⟩
  rw [← hC₁] at hL
  rw [← hC₂] at hR
  have hC₁f : C₁ ≠ ∞ := by
    rw [hC₁]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_enorm_aperture_ne_top a u)
  have hC₂f : C₂ ≠ ∞ := by
    rw [hC₂]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_enorm_aperture_ne_top a ur)
  have hgm : Measurable fun z => ‖(g : RealLineL2) z‖ₑ :=
    (Lp.stronglyMeasurable (g : RealLineL2)).measurable.enorm
  have hneg := fun {p : ℝ → Prop} (h : ∀ᵐ x ∂(volume : Measure ℝ), p x) =>
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h
  have hur' : ∀ᵐ x ∂(volume : Measure ℝ), (ur : RealLineL2) x = (u : RealLineL2) (-x) := by
    rw [hur]
    exact l2Reflection_ae (u : RealLineL2)
  have hgr' : ∀ᵐ x ∂(volume : Measure ℝ), ‖(gr : RealLineL2) x‖ₑ = ‖(g : RealLineL2) (-x)‖ₑ := by
    rw [hgr]
    exact (l2Reflection_ae (g : RealLineL2)).mono fun x hx => by
      change ‖l2Reflection (g : RealLineL2) x‖ₑ = _
      rw [hx]
  refine ⟨C₁ + C₂, ENNReal.add_ne_top.mpr ⟨hC₁f, hC₂f⟩, ?_⟩
  have hsame : ∀ x, causalGamma (fun z => ‖(gr : RealLineL2) z‖ₑ) (-x) =
      causalGamma (fun z => ‖(g : RealLineL2) z‖ₑ) x := by
    intro x
    have h1 : causalGamma (fun z => ‖(gr : RealLineL2) z‖ₑ) (-x) ≤
        causalGamma (fun z => ‖(g : RealLineL2) (-z)‖ₑ) (-x) :=
      causalGamma_mono_ae (hgr'.mono fun z hz => hz.le) _
    have h2 : causalGamma (fun z => ‖(g : RealLineL2) (-z)‖ₑ) (-x) ≤
        causalGamma (fun z => ‖(gr : RealLineL2) z‖ₑ) (-x) :=
      causalGamma_mono_ae (hgr'.mono fun z hz => hz.ge) _
    rw [le_antisymm h1 h2]
    exact causalGamma_reflect hgm x
  filter_upwards [hL, hneg hR, hneg hur'] with x h1 h2 h3
  rcases le_total x 0 with hx | hx
  · refine (h1 hx).trans ?_
    gcongr
    exact le_self_add
  · have h4 := h2 (by linarith)
    rw [h3, neg_neg, hsame] at h4
    refine h4.trans ?_
    gcongr
    exact le_add_self

/-! ### Boundedness -/

/-- **Window solutions are bounded.** An energy solution of the logarithmic equation on a window, whose forcing is
dominated by a constant and finitely many translates of the solution, is essentially bounded. -/
theorem exists_ae_norm_le_of_window_equation {ι : Type*} (a : SuzukiPositiveAperture)
    (u g : suzukiApertureHilbert a) (hu : HasLogarithmicEnergy (u : RealLineL2))
    (hsolve : ∀ f : suzukiApertureHilbert a, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) (u : RealLineL2) =
        inner ℂ (f : RealLineL2) (g : RealLineL2))
    (J : Finset ι) {c : ι → ℝ} (ℓ : ι → ℝ) (hc : ∀ j, 0 ≤ c j) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hg : ∀ᵐ x ∂volume, ‖(g : RealLineL2) x‖ ≤
      C₀ + ∑ j ∈ J, c j * ‖(u : RealLineL2) (x - ℓ j)‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂volume, ‖(u : RealLineL2) x‖ ≤ C := by
  obtain ⟨C₁, hC₁f, hb⟩ := exists_ae_enorm_le_causalGamma a u g hu hsolve
  obtain ⟨w, hw⟩ : ∃ w, w = fun x => ‖(u : RealLineL2) x‖ₑ := ⟨_, rfl⟩
  have hwm : Measurable w := by
    rw [hw]
    exact (Lp.stronglyMeasurable (u : RealLineL2)).measurable.enorm
  have hwf : ∫⁻ x, w x ≠ ∞ := by
    rw [hw]
    exact lintegral_enorm_aperture_ne_top a u
  have hdom : ∀ᵐ x ∂(volume : Measure ℝ), ‖(g : RealLineL2) x‖ₑ ≤
      ENNReal.ofReal C₀ + transSum J (fun j => ENNReal.ofReal (c j)) ℓ w x := by
    filter_upwards [hg] with x hx
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal hx).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add hC₀ (Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (norm_nonneg _)),
      ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hc j) (norm_nonneg _)]
    congr 1
    unfold transSum
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_mul (hc j), ofReal_norm, hw]
  have hmain : ∀ᵐ x ∂volume, w x ≤ C₁ + bwdAvg causalDensity (fwdAvg causalDensity fun y =>
      ENNReal.ofReal C₀ + transSum J (fun j => ENNReal.ofReal (c j)) ℓ w y) x := by
    filter_upwards [hb] with x hx
    rw [hw]
    refine hx.trans ?_
    gcongr
    rw [← hw]
    exact causalGamma_mono_ae hdom x
  obtain ⟨C', hC'f, hC'⟩ := exists_ae_le_of_absorption hwm hwf J (fun j _ => ENNReal.ofReal_ne_top) ℓ
    hC₁f ENNReal.ofReal_ne_top hmain
  refine ⟨C'.toReal, ENNReal.toReal_nonneg, ?_⟩
  filter_upwards [hC'] with x hx
  rw [hw] at hx
  have := ENNReal.toReal_mono hC'f hx
  rwa [toReal_enorm] at this

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
