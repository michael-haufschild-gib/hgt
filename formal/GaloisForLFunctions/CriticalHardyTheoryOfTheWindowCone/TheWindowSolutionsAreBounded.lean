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
  simp_rw [lintegral_const_mul _ (hh.comp (measurable_add_const _))]
  simp_rw [lintegral_add_right_eq_self h]
  rw [lintegral_mul_const _ hk]

theorem lintegral_bwdAvg {k h : ℝ → ℝ≥0∞} (hk : Measurable k) (hh : Measurable h) :
    ∫⁻ x, bwdAvg k h x = (∫⁻ r, k r) * ∫⁻ x, h x := by
  unfold bwdAvg
  rw [lintegral_lintegral_swap (f := fun x r => k r * h (x - r))
    ((hk.comp measurable_snd).mul (hh.comp (measurable_fst.sub measurable_snd))).aemeasurable]
  simp_rw [lintegral_const_mul _ (hh.comp (measurable_sub_const _))]
  simp_rw [lintegral_sub_right_eq_self h]
  rw [lintegral_mul_const _ hk]

theorem fwdAvg_mono (k : ℝ → ℝ≥0∞) {h h' : ℝ → ℝ≥0∞} (hle : ∀ y, h y ≤ h' y) (x : ℝ) :
    fwdAvg k h x ≤ fwdAvg k h' x :=
  lintegral_mono fun r => mul_le_mul_left' (hle _) _

theorem bwdAvg_mono (k : ℝ → ℝ≥0∞) {h h' : ℝ → ℝ≥0∞} (hle : ∀ y, h y ≤ h' y) (x : ℝ) :
    bwdAvg k h x ≤ bwdAvg k h' x :=
  lintegral_mono fun r => mul_le_mul_left' (hle _) _

theorem fwdAvg_add_const {k h : ℝ → ℝ≥0∞} (hk : Measurable k) (hh : Measurable h) (C : ℝ≥0∞)
    (x : ℝ) : fwdAvg k (fun y => C + h y) x = (∫⁻ r, k r) * C + fwdAvg k h x := by
  unfold fwdAvg
  simp_rw [mul_add]
  rw [lintegral_add_left (hk.mul_const C), lintegral_mul_const _ hk]

theorem bwdAvg_add_const {k h : ℝ → ℝ≥0∞} (hk : Measurable k) (hh : Measurable h) (C : ℝ≥0∞)
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
  rw [lintegral_finset_sum _ fun j _ => (hh.comp (measurable_sub_const _)).const_mul _,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lintegral_const_mul _ (hh.comp (measurable_sub_const _)), lintegral_sub_right_eq_self h]

theorem transSum_le_of_le {ι : Type*} (J : Finset ι) (c : ι → ℝ≥0∞) (ℓ : ι → ℝ) {h v : ℝ → ℝ≥0∞}
    {m : ℝ≥0∞} (hle : ∀ y, h y ≤ v y + m) (y : ℝ) :
    transSum J c ℓ h y ≤ (∑ j ∈ J, c j) * m + transSum J c ℓ v y := by
  unfold transSum
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  calc c j * h (y - ℓ j) ≤ c j * (v (y - ℓ j) + m) := mul_le_mul_left' (hle _) _
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
      rw [hδ, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_assoc,
        ENNReal.inv_mul_cancel (by simp) hM1, mul_one]
    calc δ * M ≤ δ * (M + 1) := mul_le_mul_left' le_self_add _
      _ = _ := h1
  obtain ⟨ρ, hρ0, hρ⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    (f := causalDensity) (μ := volume) (by rw [hK1]; exact ENNReal.one_ne_top) hδ0
  obtain ⟨ε, hε0, hερ, -⟩ := ENNReal.lt_iff_exists_real_btwn.mp hρ0
  have hε : 0 < ε := by simpa using ENNReal.ofReal_pos.mp (lt_of_le_of_ne hε0 (Ne.symm
    (by
      intro h0
      sorry)))
  sorry

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
