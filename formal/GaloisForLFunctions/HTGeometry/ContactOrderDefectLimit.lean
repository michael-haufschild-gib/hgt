import GaloisForLFunctions.HTGeometry.ContactOrderEulerIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The contact-order defect limit

A regularized capacity `C_τ(κ) = τ/(N(κ-κ₀) + τ R_τ(κ))` whose ground term `N` vanishes to order
`2m` at `κ₀` concentrates there at width `τ^{1/(2m)}`.  Rescaling by that width turns the
localized integral into an integral of

`w(κ₀ + τ^{1/(2m)}s) · (N(τ^{1/(2m)}s)/τ + R_τ)⁻¹`,

whose integrand is dominated by the τ-independent profile `M/(α s^{2m} + β)` — the rescaling
exactly cancels the τ in the numerator — and converges pointwise to `w(κ₀)/(c s^{2m} + r)`.
Dominated convergence therefore evaluates the limit as Euler's integral, giving the mass

`K_m w(κ₀) c^{-1/(2m)} r^{1/(2m)-1)}`,  `K_m = (π/m) csc(π/(2m))`.

Away from the contact the capacity is `O(τ)` pointwise, so the contact carries the whole defect.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The concentration width of a contact of order `m`. -/
def contactScale (m : ℕ) (τ : ℝ) : ℝ := τ ^ (2 * (m : ℝ))⁻¹

theorem contactScale_pos (m : ℕ) {τ : ℝ} (hτ : 0 < τ) : 0 < contactScale m τ :=
  Real.rpow_pos_of_pos hτ _

theorem contactScale_pow {m : ℕ} (hm : 1 ≤ m) {τ : ℝ} (hτ : 0 < τ) :
    (contactScale m τ) ^ (2 * m) = τ := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hne : (2 * (m : ℝ)) ≠ 0 := by linarith
  rw [contactScale, ← Real.rpow_natCast (τ ^ (2 * (m : ℝ))⁻¹) (2 * m),
    ← Real.rpow_mul hτ.le]
  have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  rw [hcast, inv_mul_cancel₀ hne, Real.rpow_one]

/-- **The rescaling identity.**  Translating and scaling the integration variable turns the
localized capacity integral into the rescaled one. -/
theorem integral_comp_affine (F : ℝ → ℝ) (κ₀ lam : ℝ) (hlam : 0 < lam) :
    (∫ s : ℝ, F (κ₀ + lam * s)) = lam⁻¹ * ∫ κ : ℝ, F κ := by
  have hG : (∫ s : ℝ, F (κ₀ + lam * s)) = |lam⁻¹| • ∫ y : ℝ, F (κ₀ + y) :=
    MeasureTheory.Measure.integral_comp_mul_left (fun y => F (κ₀ + y)) lam
  rw [hG, integral_add_left_eq_self F κ₀, abs_of_pos (inv_pos.2 hlam), smul_eq_mul]

/-- **(HCD.8) Away from the contact the capacity is `O(τ)`.** -/
theorem capacity_le_of_ground_bound {τ ε n R : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hn : ε ≤ n) (hR : 0 ≤ R) : (n / τ + R)⁻¹ ≤ τ / ε := by
  have hpos : 0 < ε / τ := div_pos hε hτ
  have h1 : ε / τ ≤ n / τ := by gcongr
  have hle : ε / τ ≤ n / τ + R := by linarith
  have h2 := inv_anti₀ hpos hle
  rwa [inv_div] at h2

set_option maxHeartbeats 1000000 in
/-- **(HCD.6) The contact-order defect limit.**  The rescaled localized capacity integral converges
to the weight at the contact times Euler's contact mass. -/
theorem tendsto_rescaled_contact_integral {m : ℕ} (hm : 1 ≤ m)
    {κ₀ η α β c r M L : ℝ} {w N : ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) (hr : 0 < r)
    (hwmeas : Measurable w) (hNmeas : Measurable N) (hRmeas : ∀ τ : ℝ, Measurable (R τ))
    (hwbdd : ∀ κ, |w κ| ≤ M)
    (hwsupp : ∀ κ, η < |κ - κ₀| → w κ = 0)
    (hNlow : ∀ h : ℝ, |h| ≤ η → α * h ^ (2 * m) ≤ N h)
    (hRlow : ∀ τ : ℝ, 0 < τ → ∀ κ, β ≤ R τ κ)
    (hNlim : ∀ s : ℝ, Tendsto (fun τ : ℝ => N (contactScale m τ * s) / τ) (𝓝[>] 0)
      (𝓝 (c * s ^ (2 * m))))
    (hRlim : ∀ s : ℝ, Tendsto (fun τ : ℝ => R τ (κ₀ + contactScale m τ * s)) (𝓝[>] 0) (𝓝 r))
    (hwlim : ∀ s : ℝ, Tendsto (fun τ : ℝ => w (κ₀ + contactScale m τ * s)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun τ : ℝ => ∫ s : ℝ, w (κ₀ + contactScale m τ * s)
        * (N (contactScale m τ * s) / τ + R τ (κ₀ + contactScale m τ * s))⁻¹) (𝓝[>] 0)
      (𝓝 (L * (Real.pi / (m : ℝ) / Real.sin (Real.pi / (2 * (m : ℝ)))
        * (c ^ (-(2 * (m : ℝ))⁻¹) * r ^ ((2 * (m : ℝ))⁻¹ - 1))))) := by
  classical
  have hM : 0 ≤ M := le_trans (abs_nonneg (w κ₀)) (hwbdd κ₀)
  have hbound : Integrable fun s : ℝ => M * (α * s ^ (2 * m) + β)⁻¹ :=
    (integrable_contactProfile_order hm hα hβ).const_mul M
  have hmeas : ∀ᶠ τ : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun s : ℝ => w (κ₀ + contactScale m τ * s)
        * (N (contactScale m τ * s) / τ + R τ (κ₀ + contactScale m τ * s))⁻¹) volume := by
    filter_upwards [self_mem_nhdsWithin] with τ _
    refine Measurable.aestronglyMeasurable ?_
    have h1 : Measurable fun s : ℝ => w (κ₀ + contactScale m τ * s) :=
      hwmeas.comp ((measurable_id.const_mul (contactScale m τ)).const_add κ₀)
    have h2 : Measurable fun s : ℝ => N (contactScale m τ * s) / τ :=
      (hNmeas.comp (measurable_id.const_mul (contactScale m τ))).div_const τ
    have h3 : Measurable fun s : ℝ => R τ (κ₀ + contactScale m τ * s) :=
      (hRmeas τ).comp ((measurable_id.const_mul (contactScale m τ)).const_add κ₀)
    exact h1.mul (h2.add h3).inv
  have hdom : ∀ᶠ τ : ℝ in 𝓝[>] 0, ∀ᵐ s : ℝ,
      ‖w (κ₀ + contactScale m τ * s)
        * (N (contactScale m τ * s) / τ + R τ (κ₀ + contactScale m τ * s))⁻¹‖
        ≤ M * (α * s ^ (2 * m) + β)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : (0 : ℝ) < τ := hτ
    filter_upwards with s
    have hprofile : 0 < α * s ^ (2 * m) + β := contactProfile_order_pos hα hβ s
    by_cases hs : |contactScale m τ * s| ≤ η
    · have hNge : α * (contactScale m τ * s) ^ (2 * m) ≤ N (contactScale m τ * s) :=
        hNlow _ hs
      have hpowsplit : (contactScale m τ * s) ^ (2 * m) = τ * s ^ (2 * m) := by
        rw [mul_pow, contactScale_pow hm hτ']
      rw [hpowsplit] at hNge
      have hden : α * s ^ (2 * m) + β
          ≤ N (contactScale m τ * s) / τ + R τ (κ₀ + contactScale m τ * s) := by
        have h1 : α * s ^ (2 * m) ≤ N (contactScale m τ * s) / τ := by
          rw [le_div_iff₀ hτ']
          nlinarith
        have h2 : β ≤ R τ (κ₀ + contactScale m τ * s) := hRlow τ hτ' _
        linarith
      have hinv : (N (contactScale m τ * s) / τ + R τ (κ₀ + contactScale m τ * s))⁻¹
          ≤ (α * s ^ (2 * m) + β)⁻¹ := inv_anti₀ hprofile hden
      have hinvpos : 0 ≤ (N (contactScale m τ * s) / τ + R τ (κ₀ + contactScale m τ * s))⁻¹ :=
        inv_nonneg.2 (le_trans hprofile.le hden)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hinvpos]
      exact mul_le_mul (hwbdd _) hinv hinvpos hM
    · have hzero : w (κ₀ + contactScale m τ * s) = 0 := by
        refine hwsupp _ ?_
        rw [add_sub_cancel_left]
        exact lt_of_not_ge hs
      rw [hzero, zero_mul, norm_zero]
      positivity
  have hptw : ∀ᵐ s : ℝ, Tendsto (fun τ : ℝ => w (κ₀ + contactScale m τ * s)
      * (N (contactScale m τ * s) / τ + R τ (κ₀ + contactScale m τ * s))⁻¹) (𝓝[>] 0)
      (𝓝 (L * (c * s ^ (2 * m) + r)⁻¹)) := by
    filter_upwards with s
    have hsum : Tendsto (fun τ : ℝ => N (contactScale m τ * s) / τ
        + R τ (κ₀ + contactScale m τ * s)) (𝓝[>] 0) (𝓝 (c * s ^ (2 * m) + r)) :=
      (hNlim s).add (hRlim s)
    have hne : c * s ^ (2 * m) + r ≠ 0 := ne_of_gt (contactProfile_order_pos hc hr s)
    exact (hwlim s).mul (hsum.inv₀ hne)
  have hdct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun s : ℝ => M * (α * s ^ (2 * m) + β)⁻¹) hmeas hdom hbound hptw
  have hval : (∫ s : ℝ, L * (c * s ^ (2 * m) + r)⁻¹)
      = L * (Real.pi / (m : ℝ) / Real.sin (Real.pi / (2 * (m : ℝ)))
        * (c ^ (-(2 * (m : ℝ))⁻¹) * r ^ ((2 * (m : ℝ))⁻¹ - 1))) := by
    rw [integral_const_mul, integral_contactProfile_order hm hc hr]
  rwa [hval] at hdct

/-- **(HCD.6) positivity.**  A contact whose weight is positive carries a strictly positive defect
mass, so the rescaled integral cannot vanish in the limit. -/
theorem contact_defect_mass_pos {m : ℕ} (hm : 1 ≤ m) {c r L : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hL : 0 < L) :
    0 < L * (Real.pi / (m : ℝ) / Real.sin (Real.pi / (2 * (m : ℝ)))
      * (c ^ (-(2 * (m : ℝ))⁻¹) * r ^ ((2 * (m : ℝ))⁻¹ - 1))) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpi : 0 < Real.pi := Real.pi_pos
  have harg : 0 < Real.pi / (2 * (m : ℝ)) := by positivity
  have harg2 : Real.pi / (2 * (m : ℝ)) < Real.pi := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hsin : 0 < Real.sin (Real.pi / (2 * (m : ℝ))) :=
    Real.sin_pos_of_pos_of_lt_pi harg harg2
  have hcp : 0 < c ^ (-(2 * (m : ℝ))⁻¹) := Real.rpow_pos_of_pos hc _
  have hrp : 0 < r ^ ((2 * (m : ℝ))⁻¹ - 1) := Real.rpow_pos_of_pos hr _
  have hfrac : 0 < Real.pi / (m : ℝ) / Real.sin (Real.pi / (2 * (m : ℝ))) := by
    apply div_pos (by positivity) hsin
  positivity

set_option maxHeartbeats 1000000 in
/-- **(HCD.6) The contact-order defect limit, unrescaled form.**  The localized capacity integral
divided by the contact width converges to the weight at the contact times Euler's contact mass. -/
theorem tendsto_contact_defect_integral {m : ℕ} (hm : 1 ≤ m)
    {κ₀ η α β c r M L : ℝ} {w N : ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) (hr : 0 < r)
    (hwmeas : Measurable w) (hNmeas : Measurable N) (hRmeas : ∀ τ : ℝ, Measurable (R τ))
    (hwbdd : ∀ κ, |w κ| ≤ M)
    (hwsupp : ∀ κ, η < |κ - κ₀| → w κ = 0)
    (hNlow : ∀ h : ℝ, |h| ≤ η → α * h ^ (2 * m) ≤ N h)
    (hRlow : ∀ τ : ℝ, 0 < τ → ∀ κ, β ≤ R τ κ)
    (hNlim : ∀ s : ℝ, Tendsto (fun τ : ℝ => N (contactScale m τ * s) / τ) (𝓝[>] 0)
      (𝓝 (c * s ^ (2 * m))))
    (hRlim : ∀ s : ℝ, Tendsto (fun τ : ℝ => R τ (κ₀ + contactScale m τ * s)) (𝓝[>] 0) (𝓝 r))
    (hwlim : ∀ s : ℝ, Tendsto (fun τ : ℝ => w (κ₀ + contactScale m τ * s)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun τ : ℝ => (contactScale m τ)⁻¹
        * ∫ κ : ℝ, w κ * (N (κ - κ₀) / τ + R τ κ)⁻¹) (𝓝[>] 0)
      (𝓝 (L * (Real.pi / (m : ℝ) / Real.sin (Real.pi / (2 * (m : ℝ)))
        * (c ^ (-(2 * (m : ℝ))⁻¹) * r ^ ((2 * (m : ℝ))⁻¹ - 1))))) := by
  have hmain := tendsto_rescaled_contact_integral hm hα hβ hc hr hwmeas hNmeas hRmeas hwbdd
    hwsupp hNlow hRlow hNlim hRlim hwlim
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ' : (0 : ℝ) < τ := hτ
  have hlam := contactScale_pos m hτ'
  have haff := integral_comp_affine (fun κ => w κ * (N (κ - κ₀) / τ + R τ κ)⁻¹) κ₀
    (contactScale m τ) hlam
  simpa using haff

/-- **(HCD.23)-(HCD.24) The sharp extinction criterion.**  If the rescaled capacity integral tends
to zero, the weight at the contact vanishes: no ground contact of order `m` can carry positive
weight. -/
theorem weight_eq_zero_of_tendsto_zero {m : ℕ} (hm : 1 ≤ m)
    {κ₀ η α β c r M L : ℝ} {w N : ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) (hr : 0 < r)
    (hwmeas : Measurable w) (hNmeas : Measurable N) (hRmeas : ∀ τ : ℝ, Measurable (R τ))
    (hwbdd : ∀ κ, |w κ| ≤ M)
    (hwsupp : ∀ κ, η < |κ - κ₀| → w κ = 0)
    (hNlow : ∀ h : ℝ, |h| ≤ η → α * h ^ (2 * m) ≤ N h)
    (hRlow : ∀ τ : ℝ, 0 < τ → ∀ κ, β ≤ R τ κ)
    (hNlim : ∀ s : ℝ, Tendsto (fun τ : ℝ => N (contactScale m τ * s) / τ) (𝓝[>] 0)
      (𝓝 (c * s ^ (2 * m))))
    (hRlim : ∀ s : ℝ, Tendsto (fun τ : ℝ => R τ (κ₀ + contactScale m τ * s)) (𝓝[>] 0) (𝓝 r))
    (hwlim : ∀ s : ℝ, Tendsto (fun τ : ℝ => w (κ₀ + contactScale m τ * s)) (𝓝[>] 0) (𝓝 L))
    (hzero : Tendsto (fun τ : ℝ => (contactScale m τ)⁻¹
      * ∫ κ : ℝ, w κ * (N (κ - κ₀) / τ + R τ κ)⁻¹) (𝓝[>] 0) (𝓝 0)) :
    L = 0 := by
  have hlimit := tendsto_contact_defect_integral hm hα hβ hc hr hwmeas hNmeas hRmeas hwbdd
    hwsupp hNlow hRlow hNlim hRlim hwlim
  have heq := tendsto_nhds_unique hlimit hzero
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have harg : 0 < Real.pi / (2 * (m : ℝ)) := by positivity
  have harg2 : Real.pi / (2 * (m : ℝ)) < Real.pi := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi / (2 * (m : ℝ))) :=
    Real.sin_pos_of_pos_of_lt_pi harg harg2
  have hcp : 0 < c ^ (-(2 * (m : ℝ))⁻¹) := Real.rpow_pos_of_pos hc _
  have hrp : 0 < r ^ ((2 * (m : ℝ))⁻¹ - 1) := Real.rpow_pos_of_pos hr _
  have hK : 0 < Real.pi / (m : ℝ) / Real.sin (Real.pi / (2 * (m : ℝ)))
      * (c ^ (-(2 * (m : ℝ))⁻¹) * r ^ ((2 * (m : ℝ))⁻¹ - 1)) := by
    have hfrac : 0 < Real.pi / (m : ℝ) / Real.sin (Real.pi / (2 * (m : ℝ))) := by
      apply div_pos (by positivity) hsin
    positivity
  rcases mul_eq_zero.1 heq with h | h
  · exact h
  · exact absurd h (ne_of_gt hK)

/-- **(HCD.10) A higher contact overshoots the simple normalization.**  Under the simple-contact
width `√τ`, a contact of order `m ≥ 2` with positive mass diverges. -/
theorem tendsto_atTop_simple_normalization {m : ℕ} (hm : 2 ≤ m) {A : ℝ → ℝ} {v : ℝ} (hv : 0 < v)
    (hA : Tendsto (fun τ : ℝ => (contactScale m τ)⁻¹ * A τ) (𝓝[>] 0) (𝓝 v)) :
    Tendsto (fun τ : ℝ => (contactScale 1 τ)⁻¹ * A τ) (𝓝[>] 0) atTop := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hexp : (2 * (m : ℝ))⁻¹ - (2 : ℝ)⁻¹ < 0 := by
    have hm4 : (4 : ℝ) ≤ 2 * (m : ℝ) := by linarith
    have h1 : (2 * (m : ℝ))⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hm4
    have h2 : (4 : ℝ)⁻¹ < (2 : ℝ)⁻¹ := by norm_num
    linarith
  have hpow : Tendsto (fun τ : ℝ => τ ^ ((2 * (m : ℝ))⁻¹ - (2 : ℝ)⁻¹)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero hexp
  have hprod := hpow.atTop_mul_pos hv hA
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ' : (0 : ℝ) < τ := hτ
  have h1 : (contactScale 1 τ)⁻¹ = τ ^ (-(2 : ℝ)⁻¹) := by
    rw [contactScale, ← Real.rpow_neg hτ'.le]
    norm_num
  have h2 : (contactScale m τ)⁻¹ = τ ^ (-(2 * (m : ℝ))⁻¹) := by
    rw [contactScale, ← Real.rpow_neg hτ'.le]
  rw [h1, h2, ← mul_assoc, ← Real.rpow_add hτ']
  ring_nf

/-! ## The simple contact -/

/-- The contact-order constant at a simple contact is `π`, and the profile factor is
`1/√(c r)`. -/
theorem contact_mass_simple {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    Real.pi / ((1 : ℕ) : ℝ) / Real.sin (Real.pi / (2 * ((1 : ℕ) : ℝ)))
        * (c ^ (-(2 * ((1 : ℕ) : ℝ))⁻¹) * r ^ ((2 * ((1 : ℕ) : ℝ))⁻¹ - 1))
      = Real.pi / Real.sqrt (c * r) := by
  have hsin : Real.sin (Real.pi / (2 * ((1 : ℕ) : ℝ))) = 1 := by
    norm_num
  have hexp : (2 * ((1 : ℕ) : ℝ))⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [hsin, hexp, Nat.cast_one]
  have hcp : c ^ (-(2 : ℝ)⁻¹) = (Real.sqrt c)⁻¹ := by
    rw [Real.rpow_neg hc.le, Real.sqrt_eq_rpow]
    norm_num
  have hrp : r ^ ((2 : ℝ)⁻¹ - 1) = (Real.sqrt r)⁻¹ := by
    have : ((2 : ℝ)⁻¹ - 1) = -(2 : ℝ)⁻¹ := by norm_num
    rw [this, Real.rpow_neg hr.le, Real.sqrt_eq_rpow]
    norm_num
  rw [hcp, hrp, Real.sqrt_mul hc.le]
  field_simp

/-- **(HCD.9) The simple-contact atom.**  At a simple ground contact the rescaled capacity integral
converges to `π w(κ₀)/√(c r)`. -/
theorem tendsto_simple_contact_atom
    {κ₀ η α β c r M L : ℝ} {w N : ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) (hr : 0 < r)
    (hwmeas : Measurable w) (hNmeas : Measurable N) (hRmeas : ∀ τ : ℝ, Measurable (R τ))
    (hwbdd : ∀ κ, |w κ| ≤ M)
    (hwsupp : ∀ κ, η < |κ - κ₀| → w κ = 0)
    (hNlow : ∀ h : ℝ, |h| ≤ η → α * h ^ (2 * 1) ≤ N h)
    (hRlow : ∀ τ : ℝ, 0 < τ → ∀ κ, β ≤ R τ κ)
    (hNlim : ∀ s : ℝ, Tendsto (fun τ : ℝ => N (contactScale 1 τ * s) / τ) (𝓝[>] 0)
      (𝓝 (c * s ^ (2 * 1))))
    (hRlim : ∀ s : ℝ, Tendsto (fun τ : ℝ => R τ (κ₀ + contactScale 1 τ * s)) (𝓝[>] 0) (𝓝 r))
    (hwlim : ∀ s : ℝ, Tendsto (fun τ : ℝ => w (κ₀ + contactScale 1 τ * s)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun τ : ℝ => (contactScale 1 τ)⁻¹
        * ∫ κ : ℝ, w κ * (N (κ - κ₀) / τ + R τ κ)⁻¹) (𝓝[>] 0)
      (𝓝 (L * (Real.pi / Real.sqrt (c * r)))) := by
  have hmain := tendsto_contact_defect_integral (m := 1) le_rfl hα hβ hc hr hwmeas hNmeas hRmeas
    hwbdd hwsupp hNlow hRlow hNlim hRlim hwlim
  rwa [contact_mass_simple hc hr] at hmain

/-- **(HCD.21) The Route-U atom weight.**  With reduced response `r = ρ⁻¹` the atom weight is
`π √(ρ/c)`. -/
theorem simple_contact_atom_eq {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    Real.pi / Real.sqrt (c * ρ⁻¹) = Real.pi * Real.sqrt (ρ / c) := by
  have hcr : Real.sqrt (c * ρ⁻¹) = Real.sqrt c / Real.sqrt ρ := by
    rw [Real.sqrt_mul hc.le, Real.sqrt_inv, div_eq_mul_inv]
  have hrc : Real.sqrt (ρ / c) = Real.sqrt ρ / Real.sqrt c := Real.sqrt_div' ρ hc.le
  rw [hcr, hrc]
  have h1 : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  have h2 : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hρ)
  field_simp

/-! ## The analytic feeds -/

/-- **(HCD.13) The scalar resolvent gap bound.**  On a spectrum bounded below by `δ` the
regularized resolvent differs from the reduced inverse by at most `τ/(δ(δ+τ))`. -/
theorem resolvent_gap_bound {δ τ b : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) (hb : δ ≤ b) :
    |(b + τ)⁻¹ - b⁻¹| ≤ τ / (δ * (δ + τ)) := by
  have hb0 : 0 < b := lt_of_lt_of_le hδ hb
  have hbt : 0 < b + τ := by linarith
  have hval : (b + τ)⁻¹ - b⁻¹ = -(τ / (b * (b + τ))) := by
    field_simp
    ring
  rw [hval, abs_neg, abs_of_nonneg (by positivity)]
  have hden : δ * (δ + τ) ≤ b * (b + τ) := by nlinarith
  exact div_le_div_of_nonneg_left hτ.le (by positivity) hden

/-- **(HCD.13) Uniform convergence transports a moving point.**  If `R_τ → R₀` uniformly, `R₀` is
continuous at `κ₀`, and the evaluation point tends to `κ₀`, then `R_τ` at the moving point tends to
`R₀(κ₀)`. -/
theorem tendsto_of_tendstoUniformly_of_continuousAt {R : ℝ → ℝ → ℝ} {R₀ g : ℝ → ℝ} {κ₀ r : ℝ}
    (hunif : ∀ ε : ℝ, 0 < ε → ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ κ, |R τ κ - R₀ κ| ≤ ε)
    (hcont : ContinuousAt R₀ κ₀) (hR₀ : R₀ κ₀ = r)
    (hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 κ₀)) :
    Tendsto (fun τ => R τ (g τ)) (𝓝[>] (0 : ℝ)) (𝓝 r) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hcomp : Tendsto (fun τ => R₀ (g τ)) (𝓝[>] (0 : ℝ)) (𝓝 r) := by
    rw [← hR₀]
    exact hcont.tendsto.comp hg
  have hcomp' : ∀ᶠ τ in 𝓝[>] (0 : ℝ), dist (R₀ (g τ)) r < ε / 2 :=
    Metric.tendsto_nhds.1 hcomp _ hhalf
  filter_upwards [hunif (ε / 2) hhalf, hcomp'] with τ h1 h2
  have hd : dist (R τ (g τ)) (R₀ (g τ)) ≤ ε / 2 := by
    rw [Real.dist_eq]
    exact h1 (g τ)
  calc dist (R τ (g τ)) r ≤ dist (R τ (g τ)) (R₀ (g τ)) + dist (R₀ (g τ)) r := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

section Contact

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **(HCD.14) The rescaled ground profile.**  A ground family vanishing to order `m` at `κ₀` has
rescaled squared norm converging to `‖a‖² s^{2m}`. -/
theorem tendsto_normSq_contact_path {G : ℝ → H} {a : H} {κ₀ : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (h0 : G κ₀ = 0)
    (hcontact : Tendsto (fun h : ℝ => (h ^ m)⁻¹ • G (κ₀ + h)) (𝓝[≠] (0 : ℝ)) (𝓝 a))
    (s : ℝ) :
    Tendsto (fun τ : ℝ => ‖G (κ₀ + contactScale m τ * s)‖ ^ 2 / τ) (𝓝[>] (0 : ℝ))
      (𝓝 (‖a‖ ^ 2 * s ^ (2 * m))) := by
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    have hfun : ∀ τ : ℝ, ‖G (κ₀ + contactScale m τ * 0)‖ ^ 2 / τ = 0 := by
      intro τ
      simp [h0]
    simp only [hfun]
    have hz : ‖a‖ ^ 2 * (0 : ℝ) ^ (2 * m) = 0 := by
      have : (0 : ℝ) ^ (2 * m) = 0 := zero_pow (by omega)
      rw [this, mul_zero]
    rw [hz]
    exact tendsto_const_nhds
  · have hpath : Tendsto (fun τ : ℝ => contactScale m τ * s) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hexp : (0 : ℝ) < (2 * (m : ℝ))⁻¹ := by
          have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          positivity
        have hcont : ContinuousAt (fun x : ℝ => x ^ ((2 * (m : ℝ))⁻¹)) 0 :=
          Real.continuousAt_rpow_const 0 _ (Or.inr hexp.le)
        have hzr : (0 : ℝ) ^ ((2 * (m : ℝ))⁻¹) = 0 := Real.zero_rpow (ne_of_gt hexp)
        have hsc0 := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        rw [hzr] at hsc0
        have hsc : Tendsto (fun τ : ℝ => contactScale m τ) (𝓝[>] (0 : ℝ)) (𝓝 0) := hsc0
        simpa using hsc.mul_const s
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        have hτ' : (0 : ℝ) < τ := hτ
        simpa using mul_ne_zero (ne_of_gt (contactScale_pos m hτ')) hs
    have hnorm : Tendsto (fun τ : ℝ => ‖(((contactScale m τ * s) ^ m)⁻¹) • G (κ₀ + contactScale m τ * s)‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (‖a‖ ^ 2)) := ((hcontact.comp hpath).norm).pow 2
    have hval : ∀ τ : ℝ, 0 < τ →
        ‖(((contactScale m τ * s) ^ m)⁻¹) • G (κ₀ + contactScale m τ * s)‖ ^ 2 * s ^ (2 * m)
          = ‖G (κ₀ + contactScale m τ * s)‖ ^ 2 / τ := by
      intro τ hτ
      have hlam : 0 < contactScale m τ := contactScale_pos m hτ
      have hne : (contactScale m τ * s) ^ m ≠ 0 := pow_ne_zero m (mul_ne_zero (ne_of_gt hlam) hs)
      have hsq : ((contactScale m τ * s) ^ m) ^ 2 = τ * s ^ (2 * m) := by
        rw [← pow_mul, mul_comm m 2, mul_pow, contactScale_pow hm hτ]
      rw [norm_smul, norm_inv, Real.norm_eq_abs, mul_pow, inv_pow, ← abs_pow, hsq]
      have hspos : (0 : ℝ) < s ^ (2 * m) := by
        have hrw : s ^ (2 * m) = (s ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
        rw [hrw]
        exact pow_two_pos_of_ne_zero (pow_ne_zero m hs)
      have habs : |τ * s ^ (2 * m)| = τ * s ^ (2 * m) := abs_of_pos (by positivity)
      rw [habs]
      field_simp
    have hmul := hnorm.mul_const (s ^ (2 * m))
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact hval τ hτ

/-- **(HCD.15) The ground lower bound near a contact.**  An order-`m` contact with nonzero velocity
bounds the ground profile below by a fixed multiple of `h^{2m}` on a fixed neighbourhood. -/
theorem exists_contact_lower_bound {G : ℝ → H} {a : H} {κ₀ : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (h0 : G κ₀ = 0) (ha : a ≠ 0)
    (hcontact : Tendsto (fun h : ℝ => (h ^ m)⁻¹ • G (κ₀ + h)) (𝓝[≠] (0 : ℝ)) (𝓝 a)) :
    ∃ η > 0, ∀ h : ℝ, |h| ≤ η → ‖a‖ ^ 2 / 4 * h ^ (2 * m) ≤ ‖G (κ₀ + h)‖ ^ 2 := by
  have hanorm : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnormlim : Tendsto (fun h : ℝ => ‖(h ^ m)⁻¹ • G (κ₀ + h)‖) (𝓝[≠] (0 : ℝ)) (𝓝 ‖a‖) :=
    hcontact.norm
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖a‖ / 2 < ‖(h ^ m)⁻¹ • G (κ₀ + h)‖ :=
    Tendsto.eventually_const_lt (by linarith) hnormlim
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨η₀, hη₀, hbound⟩ := hev
  refine ⟨η₀ / 2, by linarith, fun h hh => ?_⟩
  rcases eq_or_ne h 0 with hzero | hzero
  · subst hzero
    have hp : (0 : ℝ) ^ (2 * m) = 0 := zero_pow (by omega)
    rw [hp, mul_zero, add_zero, h0]
    positivity
  · have hdist : dist h (0 : ℝ) < η₀ := by
      rw [Real.dist_eq, sub_zero]
      calc |h| ≤ η₀ / 2 := hh
        _ < η₀ := by linarith
    have hlt := hbound hdist (by simpa using hzero)
    have hne : (h ^ m) ≠ 0 := pow_ne_zero m hzero
    rw [norm_smul, norm_inv, Real.norm_eq_abs] at hlt
    have habs : (0 : ℝ) < |h ^ m| := abs_pos.2 hne
    have hstep : ‖a‖ / 2 * |h ^ m| ≤ ‖G (κ₀ + h)‖ := by
      rw [inv_mul_eq_div, lt_div_iff₀ habs] at hlt
      linarith
    have hsq : (‖a‖ / 2 * |h ^ m|) ^ 2 ≤ ‖G (κ₀ + h)‖ ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hstep
    have hnn : (0 : ℝ) ≤ h ^ (2 * m) := by
      have hrw : h ^ (2 * m) = (h ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [hrw]
      positivity
    have hexp : (‖a‖ / 2 * |h ^ m|) ^ 2 = ‖a‖ ^ 2 / 4 * h ^ (2 * m) := by
      rw [mul_pow, ← abs_pow, ← pow_mul, mul_comm m 2, abs_of_nonneg hnn]
      ring
    rw [hexp] at hsq
    exact hsq

end Contact

end GaloisForLFunctions.HTGeometry

end
