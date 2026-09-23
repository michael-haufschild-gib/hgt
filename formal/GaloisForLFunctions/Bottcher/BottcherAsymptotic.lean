/-
# Böttcher tower — the normalization asymptotic `φ_c(z) − z → 0` (E2 input)

The Böttcher coordinate is tangent to the identity at `∞`: `φ_c(z) − z → 0` as `z → ∞`. This is the
analytic heart of brick E2 (the filled Julia set / Green's function determines the parameter `c`):
combined with the functional equation `φ_c(z²+c) = φ_c(z)²`, if `φ_{c₁} = φ_{c₂}` then
`φ(u+c₁) = φ(u+c₂)` for large `u`, and the difference `→ c₁ − c₂`, forcing `c₁ = c₂`.

Proof: `φ_c(z) = z·exp(S(z))` with `S = ∑ₖ termₖ` and `‖S‖ ≤ 2‖c‖/‖z‖²`
(`norm_bottcherLog_sub_log_le`); so `‖φ_c(z) − z‖ = ‖z‖·‖exp S − 1‖ ≤ ‖z‖·2‖S‖ ≤ 4‖c‖/‖z‖ → 0`.

New file (hRigid connected lane); consumes `BottcherCoord`.
-/
import GaloisForLFunctions.Bottcher.BottcherCoord

open Filter Topology Metric Bornology

namespace Bottcher

/-- **Normalization asymptotic** `φ_c(z) − z → 0` as `z → ∞`. -/
theorem tendsto_bottcherCoord_sub_id (c : ℂ) :
    Tendsto (fun z => bottcherCoord c z - z) (cobounded ℂ) (𝓝 0) := by
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (cobounded ℂ) atTop := tendsto_norm_cobounded_atTop
  have hbd : Tendsto (fun z : ℂ => 4 * ‖c‖ / ‖z‖) (cobounded ℂ) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnorm
  refine squeeze_zero_norm' ?_ hbd
  filter_upwards [hnorm.eventually_gt_atTop (max 2 ‖c‖), hnorm.eventually_gt_atTop 0]
    with z hz hz0
  have hc : ‖c‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz)
  have hz2 : 2 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hzpos : (0 : ℝ) < ‖z‖ := hz0
  have hzne : z ≠ 0 := by intro h; rw [h, norm_zero] at hz0; linarith
  have hzn0 : ‖z‖ ≠ 0 := ne_of_gt hzpos
  set S := ∑' k, bottcherLogTerm c z k with hSdef
  have hSbd : ‖S‖ ≤ 2 * ‖c‖ / ‖z‖ ^ (2 : ℕ) := by
    have h := norm_bottcherLog_sub_log_le hc hz2
    rw [bottcherLog, add_sub_cancel_left] at h
    rw [hSdef]; exact h
  have hSle1 : ‖S‖ ≤ 1 := by
    have h2 : 2 * ‖c‖ / ‖z‖ ^ (2 : ℕ) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [hc, hz2, norm_nonneg z]
    linarith
  rw [bottcherCoord_eq_mul_exp hzne, ← hSdef,
    show z * Complex.exp S - z = z * (Complex.exp S - 1) by ring, norm_mul]
  calc ‖z‖ * ‖Complex.exp S - 1‖
      ≤ ‖z‖ * (2 * ‖S‖) := by gcongr; exact Complex.norm_exp_sub_one_le hSle1
    _ ≤ ‖z‖ * (2 * (2 * ‖c‖ / ‖z‖ ^ (2 : ℕ))) := by gcongr
    _ = 4 * ‖c‖ / ‖z‖ := by field_simp; ring

/-- `z ↦ z²+c` tends to `∞` (cobounded → cobounded): `‖z²+c‖ ≥ ‖z‖²−‖c‖ → ∞`. -/
theorem tendsto_sq_add_cobounded (c : ℂ) :
    Tendsto (fun z : ℂ => z ^ (2 : ℕ) + c) (cobounded ℂ) (cobounded ℂ) := by
  have hz : Tendsto (fun z : ℂ => ‖z‖) (cobounded ℂ) atTop := tendsto_norm_cobounded_atTop
  have hsq : Tendsto (fun z : ℂ => ‖z‖ ^ (2 : ℕ) - ‖c‖) (cobounded ℂ) atTop := by
    have h := tendsto_atTop_add_const_right (cobounded ℂ) (-‖c‖)
      ((tendsto_pow_atTop two_ne_zero).comp hz)
    simpa [sub_eq_add_neg] using h
  have hlow : ∀ z : ℂ, ‖z‖ ^ (2 : ℕ) - ‖c‖ ≤ ‖z ^ (2 : ℕ) + c‖ := fun z => by
    have h := norm_sub_le (z ^ (2 : ℕ) + c) c
    rw [add_sub_cancel_right, norm_pow] at h
    linarith
  have h1 : Tendsto (fun z : ℂ => ‖z ^ (2 : ℕ) + c‖) (cobounded ℂ) atTop :=
    tendsto_atTop_mono hlow hsq
  exact tendsto_norm_atTop_iff_cobounded.mp h1

/-- **E2 functional-equation core.** If `φ_{c₁} = φ_{c₂}` on the deep exterior, then `c₁ = c₂`. From the
functional equation `φ_c(z²+c)=φ_c(z)²`, equal coordinates force `φ_{c₂}(z²+c₁)=φ_{c₂}(z²+c₂)` for all
deep `z`; since `φ_{c₂}(w)−w → 0` at `∞`, the difference of the two sides tends to `c₁−c₂` yet is `0`,
so `c₁=c₂`. The hypothesis `φ_{c₁}=φ_{c₂}` on the germ is supplied (separately) by equal Green's
functions. -/
theorem c_eq_of_bottcherCoord_eqOn {c₁ c₂ : ℂ}
    (heq : ∀ z : ℂ, max 2 (max ‖c₁‖ ‖c₂‖) < ‖z‖ → bottcherCoord c₁ z = bottcherCoord c₂ z) :
    c₁ = c₂ := by
  set R : ℝ := max 2 (max ‖c₁‖ ‖c₂‖) with hRdef
  have hR2 : (2 : ℝ) ≤ R := le_max_left _ _
  have hc1R : ‖c₁‖ ≤ R := le_trans (le_max_left _ _) (le_max_right 2 _)
  have hc2R : ‖c₂‖ ≤ R := le_trans (le_max_right _ _) (le_max_right 2 _)
  set F : ℂ → ℂ := fun z => (bottcherCoord c₂ (z ^ (2 : ℕ) + c₁) - (z ^ (2 : ℕ) + c₁))
      - (bottcherCoord c₂ (z ^ (2 : ℕ) + c₂) - (z ^ (2 : ℕ) + c₂)) with hFdef
  -- F → 0 at ∞
  have hF0 : Tendsto F (cobounded ℂ) (𝓝 0) := by
    have hA : Tendsto (fun z : ℂ => bottcherCoord c₂ (z ^ (2 : ℕ) + c₁) - (z ^ (2 : ℕ) + c₁))
        (cobounded ℂ) (𝓝 0) := (tendsto_bottcherCoord_sub_id c₂).comp (tendsto_sq_add_cobounded c₁)
    have hB : Tendsto (fun z : ℂ => bottcherCoord c₂ (z ^ (2 : ℕ) + c₂) - (z ^ (2 : ℕ) + c₂))
        (cobounded ℂ) (𝓝 0) := (tendsto_bottcherCoord_sub_id c₂).comp (tendsto_sq_add_cobounded c₂)
    simpa [hFdef] using hA.sub hB
  -- F is eventually the constant -(c₁-c₂)
  have hev : F =ᶠ[cobounded ℂ] (fun _ => -(c₁ - c₂)) := by
    have hRev : ∀ᶠ z in cobounded ℂ, R < ‖z‖ :=
      tendsto_norm_cobounded_atTop.eventually_gt_atTop R
    filter_upwards [hRev] with z hz
    have hc1z : ‖c₁‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt hc1R hz)
    have hc2z : ‖c₂‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt hc2R hz)
    have h2z : (2 : ℝ) < ‖z‖ := lt_of_le_of_lt hR2 hz
    have hzsq : R ^ (2 : ℕ) < ‖z‖ ^ (2 : ℕ) := by nlinarith [hz, hR2]
    have hlow1 : ‖z‖ ^ (2 : ℕ) - ‖c₁‖ ≤ ‖z ^ (2 : ℕ) + c₁‖ := by
      have h := norm_sub_le (z ^ (2 : ℕ) + c₁) c₁
      rw [add_sub_cancel_right, norm_pow] at h; linarith
    have hlow2 : ‖z‖ ^ (2 : ℕ) - ‖c₂‖ ≤ ‖z ^ (2 : ℕ) + c₂‖ := by
      have h := norm_sub_le (z ^ (2 : ℕ) + c₂) c₂
      rw [add_sub_cancel_right, norm_pow] at h; linarith
    have hdeep1 : R < ‖z ^ (2 : ℕ) + c₁‖ := by nlinarith [hlow1, hzsq, hc1R, hR2]
    have hdeep2 : R < ‖z ^ (2 : ℕ) + c₂‖ := by nlinarith [hlow2, hzsq, hc2R, hR2]
    -- φ_{c₂}(z²+c₁) = φ_{c₂}(z²+c₂)
    have hqe1 : bottcherCoord c₁ (z ^ (2 : ℕ) + c₁) = bottcherCoord c₁ z ^ (2 : ℕ) :=
      bottcherCoord_quadratic hc1z h2z
    have hqe2 : bottcherCoord c₂ (z ^ (2 : ℕ) + c₂) = bottcherCoord c₂ z ^ (2 : ℕ) :=
      bottcherCoord_quadratic hc2z h2z
    have hAB : bottcherCoord c₂ (z ^ (2 : ℕ) + c₁) = bottcherCoord c₂ (z ^ (2 : ℕ) + c₂) := by
      rw [← heq (z ^ (2 : ℕ) + c₁) hdeep1, hqe1, heq z hz, ← hqe2]
    simp only [hFdef]
    rw [hAB]; ring
  -- the eventual constant must be 0
  have hconst : Tendsto (fun _ : ℂ => -(c₁ - c₂)) (cobounded ℂ) (𝓝 0) :=
    hF0.congr' hev
  have hz0 : (0 : ℂ) = -(c₁ - c₂) := tendsto_nhds_unique hconst tendsto_const_nhds
  exact sub_eq_zero.mp (neg_eq_zero.mp hz0.symm)


end Bottcher

namespace Bottcher

/-- **Parameter-defect asymptotic.** For the `c₂` Böttcher coordinate, the two quadratic inputs with
parameters `c₁` and `c₂` differ asymptotically by exactly `c₁-c₂`:
`φ₂(z²+c₁)-φ₂(z²+c₂) → c₁-c₂` as `z → ∞`.

This is the leading valuation term behind the direct transition-function route. -/
theorem tendsto_bottcherCoord_quadratic_parameter_defect (c₁ c₂ : ℂ) :
    Tendsto (fun z => bottcherCoord c₂ (quadratic c₁ z) - bottcherCoord c₂ (quadratic c₂ z))
      (cobounded ℂ) (𝓝 (c₁ - c₂)) := by
  let E₁ : ℂ → ℂ := fun z => bottcherCoord c₂ (quadratic c₁ z) - quadratic c₁ z
  let E₂ : ℂ → ℂ := fun z => bottcherCoord c₂ (quadratic c₂ z) - quadratic c₂ z
  have hE₁ : Tendsto E₁ (cobounded ℂ) (𝓝 0) :=
    (tendsto_bottcherCoord_sub_id c₂).comp (tendsto_sq_add_cobounded c₁)
  have hE₂ : Tendsto E₂ (cobounded ℂ) (𝓝 0) :=
    (tendsto_bottcherCoord_sub_id c₂).comp (tendsto_sq_add_cobounded c₂)
  have hmain : Tendsto (fun z => E₁ z - E₂ z + (c₁ - c₂)) (cobounded ℂ) (𝓝 (c₁ - c₂)) := by
    simpa using (hE₁.sub hE₂).add tendsto_const_nhds
  convert hmain using 1
  funext z
  simp [E₁, E₂, quadratic]
  ring

end Bottcher
