import GaloisForLFunctions.RHTower.HamburgerStabilityCriticalLine
import GaloisForLFunctions.RHTower.WeilFractionalMassPolynomialTailRigidity

/-!
# Two unequal coefficients floor the Abel mass of the defect

A Dirichlet series `Z(s) = Σ a_n n^{-s}` **continues to the critical line in the Hamburger strip
class** with pole parameter `β` and critical-line FE defect `g` (`HamburgerStripDefect`) when there
is `E`, continuous on `1/2 ≤ Re s ≤ 3/2`, holomorphic inside and `O(1/(1 + t²))`, with
`Γ_ℝ(s) Z(s) = E(s) + β Γ_ℝ(s - 1)` on `Re s = 3/2` and

`E(s) - E(1 - s) = -β (Γ_ℝ(s - 1) - Γ_ℝ(-s)) + Γ_ℝ(s) g(Im s / 2)`   on `Re s = 1/2`,

with `g` measurable and polynomially bounded.

* **Hamburger identity** (`hamburgerSeries_eq_defect`).  On `Re τ > 0`
  `L_a(τ) = F_a(τ) - β/(πτ) + β + J_g(τ)`, where `L_a(τ) = Σ a_n τ/(π(n² + τ²))`,
  `F_a(τ) = Σ a_n e^{-2πnτ}` (`expSeries`) and `J_g` is the defect Laplace transform.
* **Abel floor** (`eventually_le_mul_abelMass_of_coeff_ne`).  For `1 ≤ m₁ ≤ m₂`,
  `liminf_{δ→0⁺} δ ∫ ‖g(t)‖ e^{-δ|t|} dt ≥ ‖a_{m₂} - a_{m₁}‖ / (3(m₂ + 1))`.
  `F_a` is `i`-periodic, so `L_a(ε + i m₂) - L_a(ε + i m₁)` is the difference of the two defect
  values plus polar terms; `ε L_a(ε + i m) → a_m/(2π)` is Hamburger's residue, and
  `ε ‖J_g(ε + i m)‖` is bounded by the Abel mass at `δ = 2ε/(m₂ + 1)`.
* **No decaying defect** (`not_tendsto_zero_of_coeff_ne`, `not_le_rpow_neg_of_coeff_ne`).  If two
  coefficients differ, `g` is not Abel-sublinear, does not tend to `0`, and in particular is not
  `O((1 + |t|)^{-α})` for any `α > 0`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower.HamburgerStability GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.EulerFETransportTheory

/-- **Hamburger strip continuation with a critical-line FE defect.**  `Z` continues to the
critical line in the Hamburger strip class with pole parameter `β` and defect `g`. -/
def HamburgerStripDefect (Z : ℂ → ℂ) (β : ℂ) (g : ℝ → ℂ) : Prop :=
  ∃ E : ℂ → ℂ, ∃ C : ℝ,
    ContinuousOn E (HTGeometry.verticalStrip (1 / 2) (3 / 2)) ∧
    DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2} ∧
    (∀ s ∈ HTGeometry.verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2)) ∧
    (∀ s : ℂ, s.re = 3 / 2 → Complex.Gammaℝ s * Z s = E s + β * Complex.Gammaℝ (s - 1)) ∧
    (∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) +
        Complex.Gammaℝ s * g (s.im / 2)) ∧
    Measurable g ∧ ∃ Cg : ℝ, ∃ N : ℕ, ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ N

/-- The exponential series `F_a(τ) = Σ_{n ≥ 1} a_n e^{-2πnτ}`. -/
def expSeries (a : ℕ → ℂ) (τ : ℂ) : ℂ :=
  ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ))

/-- `F_a` is `i`-periodic. -/
theorem expSeries_add_nat_mul_I (a : ℕ → ℂ) (τ : ℂ) (k : ℕ) :
    expSeries a (τ + (k : ℂ) * I) = expSeries a τ := by
  unfold expSeries
  refine tsum_congr fun n => ?_
  rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (τ + (k : ℂ) * I)) =
    -(2 * Real.pi * ((n : ℂ) + 1) * τ) + ((-(((n : ℤ) + 1) * k) : ℤ) : ℂ) * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The Hamburger identity with a defect.**  On `Re τ > 0`,
`L_a(τ) = F_a(τ) - β/(πτ) + β + J_g(τ)`. -/
theorem hamburgerSeries_eq_defect {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {τ : ℂ} (hτ : 0 < τ.re) :
    hamburgerSeries a τ = expSeries a τ - β / (Real.pi * τ) + β + defectLaplace g τ := by
  obtain ⟨E, C, hEc, hEd, hdecay, hR, hC, hgm, Cg, N, hgb⟩ := hH
  have hgm' := hgm.aestronglyMeasurable (μ := volume)
  have hθc : ContinuousOn (coeffTheta a) (Ioi 0) := continuousOn_coeffTheta a (ha 2 (by norm_num))
  have hθm : MellinConvergent (coeffTheta a) (3 / 4) :=
    mellinConvergent_coeffTheta a ha (by norm_num) (by norm_num)
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      mellin (coeffTheta a) (s / 2) = E s + β * Complex.Gammaℝ (s - 1) := by
    intro s hs
    rw [mellin_coeffTheta a ha (by rw [hs]; norm_num)]
    exact hR s hs
  have him : ∀ t : ℝ, (2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2 = t := fun t => by simp
  have hdint : Integrable fun t : ℝ => Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) *
      g ((2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2) := by
    simp only [him]
    exact integrable_Gammaℝ_mul hgm' hgb
  have htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      1 * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        defectKernel g x := by
    intro x hx
    have h := critical_line_even_theta_relation_defect
      (d := fun s => Complex.Gammaℝ s * g (s.im / 2)) hθc hθm hEc hEd hdecay hR' hC hdint hx
    simp only [him] at h
    unfold defectKernel
    linear_combination h
  have h := hamburgerSeries_eq_of_coeffTheta_relation_defect a a ha ha htheta
    (fun τ hτ => (defectKernel_laplace hgm hgb hτ).1)
    (differentiableOn_defectLaplace hgm' hgb)
    (fun τ hτ => (defectKernel_laplace hgm hgb hτ).2) hτ
  rw [h]
  unfold expSeries
  ring

/-- **Hamburger's residue along a horizontal ray.**  `ε L_a(ε + i m) → a_m/(2π)` as `ε → 0⁺`. -/
theorem tendsto_mul_hamburgerSeries_radial {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * hamburgerSeries a ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0)
      (𝓝 (a m / (2 * Real.pi))) := by
  have hres := tendsto_sub_mul_hamburgerSeries ha hm
  have hpath : Tendsto (fun ε : ℝ => (ε : ℂ) + (m : ℂ) * I) (𝓝[>] 0) (𝓝[≠] ((m : ℂ) * I)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => (ε : ℂ) + (m : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) + (m : ℂ) * I)) :=
        ((Complex.continuous_ofReal.add continuous_const).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      intro h
      have h' := congrArg Complex.re h
      simp at h'
      exact (ne_of_gt hε) h'
  refine (hres.comp hpath).congr fun ε => ?_
  simp only [Function.comp_apply, add_sub_cancel_right]

/-- `ε ‖J_g(ε + i m)‖` is controlled by the Abel mass at `2ε/(M + 1)` for `1 ≤ m ≤ M`,
`0 < ε < 1`. -/
theorem mul_norm_defectLaplace_le_abelMass {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ε * ‖defectLaplace g ((ε : ℂ) + (m : ℂ) * I)‖ ≤
      3 / (2 * Real.pi) * (ε * abelMass g (2 * ε / ((M : ℝ) + 1))) := by
  have hpi := Real.pi_pos
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hre : τ.re = ε := by simp [hτ]
  have him : τ.im = m := by simp [hτ]
  have hτre : 0 < τ.re := by rw [hre]; exact hε
  have hb := norm_defectLaplace_le hgm hgb hτre
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmM' : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hn1 : 1 ≤ ‖τ‖ := by
    have := Complex.abs_im_le_norm τ
    rw [him, abs_of_nonneg (by positivity)] at this
    linarith
  have hn2 : ‖τ‖ ≤ (M : ℝ) + 1 := by
    have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, norm_mul, Complex.norm_natCast,
      Complex.norm_I, mul_one] at h
    linarith
  have hpow : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hδ : 2 * ε / ((M : ℝ) + 1) ≤ 2 * (τ.re / ‖τ‖) := by
    rw [hre, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hε.le (by linarith) hn2)
      (by norm_num)
  have hmono := abelMass_antitone hgm hgb (div_pos (mul_pos two_pos hε) hM1) hδ
  have hM0 : 0 ≤ abelMass g (2 * (τ.re / ‖τ‖)) := integral_nonneg fun t => by positivity
  calc ε * ‖defectLaplace g τ‖
      ≤ ε * (3 / (2 * Real.pi) * ‖τ‖ ^ (-(1 / 2 : ℝ)) * abelMass g (2 * (τ.re / ‖τ‖))) := by
        gcongr
    _ ≤ ε * (3 / (2 * Real.pi) * 1 * abelMass g (2 * ε / ((M : ℝ) + 1))) := by gcongr
    _ = 3 / (2 * Real.pi) * (ε * abelMass g (2 * ε / ((M : ℝ) + 1))) := by ring

/-- **Abel floor from two unequal coefficients.**  If `1 ≤ m₁ ≤ m₂`, then
`liminf_{δ→0⁺} δ ∫ ‖g(t)‖ e^{-δ|t|} dt ≥ ‖a_{m₂} - a_{m₁}‖ / (3(m₂ + 1))`. -/
theorem eventually_le_mul_abelMass_of_coeff_ne {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₁₂ : m₁ ≤ m₂) {c : ℝ}
    (hc : c < ‖a m₂ - a m₁‖ / (3 * ((m₂ : ℝ) + 1))) :
    ∀ᶠ δ in 𝓝[>] 0, c ≤ δ * abelMass g δ := by
  have hpi := Real.pi_pos
  obtain ⟨-, -, -, -, -, -, -, hgm, Cg, N, hgb⟩ := id hH
  have hgm' := hgm.aestronglyMeasurable (μ := volume)
  have hm₂ : 1 ≤ m₂ := hm₁.trans hm₁₂
  have hM1 : (0 : ℝ) < (m₂ : ℝ) + 1 := by positivity
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    simpa using summable_sq_of_forall_rpow ha
  -- the radial difference of the defect values, and the polar terms
  set Ψ : ℝ → ℂ := fun ε => (ε : ℂ) * (defectLaplace g ((ε : ℂ) + (m₂ : ℂ) * I) -
    defectLaplace g ((ε : ℂ) + (m₁ : ℂ) * I)) with hΨ
  set P : ℝ → ℂ := fun ε => (ε : ℂ) * (-β / (Real.pi * ((ε : ℂ) + (m₂ : ℂ) * I)) +
    β / (Real.pi * ((ε : ℂ) + (m₁ : ℂ) * I))) with hP
  have hpole : ∀ m : ℕ, 1 ≤ m → ∀ ε : ℝ, (Real.pi : ℂ) * ((ε : ℂ) + (m : ℂ) * I) ≠ 0 := by
    intro m hm ε h
    rcases mul_eq_zero.mp h with h | h
    · exact Real.pi_ne_zero (by exact_mod_cast h)
    · have h' := congrArg Complex.im h
      simp at h'
      omega
  have hPt : Tendsto P (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous P := by
      refine Complex.continuous_ofReal.mul ?_
      refine (continuous_const.div (continuous_const.mul
        (Complex.continuous_ofReal.add continuous_const)) fun ε => hpole m₂ hm₂ ε).add
        (continuous_const.div (continuous_const.mul
          (Complex.continuous_ofReal.add continuous_const)) fun ε => hpole m₁ hm₁ ε)
    have := hcont.tendsto 0
    simp only [hP, Complex.ofReal_zero, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hL₂ := tendsto_mul_hamburgerSeries_radial ha2 hm₂
  have hL₁ := tendsto_mul_hamburgerSeries_radial ha2 hm₁
  -- `F_a` cancels by periodicity, so `Ψ` carries the two residues
  have hΨt : Tendsto Ψ (𝓝[>] 0) (𝓝 ((a m₂ - a m₁) / (2 * Real.pi))) := by
    have h := (hL₂.sub hL₁).sub hPt
    rw [sub_zero, ← sub_div] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    have hre : ∀ m : ℕ, 0 < ((ε : ℂ) + (m : ℂ) * I).re := fun m => by simpa using hε'
    have hper : expSeries a ((ε : ℂ) + (m₂ : ℂ) * I) = expSeries a ((ε : ℂ) + (m₁ : ℂ) * I) := by
      rw [expSeries_add_nat_mul_I, expSeries_add_nat_mul_I]
    simp only [hΨ, hP]
    rw [hamburgerSeries_eq_defect ha hH (hre m₂), hamburgerSeries_eq_defect ha hH (hre m₁), hper]
    ring
  -- the threshold, rescaled to the radial variable
  have hK : (0 : ℝ) < 3 * ((m₂ : ℝ) + 1) / (2 * Real.pi) := by positivity
  have hnorm2pi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hlim : c * (3 * ((m₂ : ℝ) + 1) / (2 * Real.pi)) <
      ‖(a m₂ - a m₁) / (2 * Real.pi)‖ := by
    rw [norm_div, hnorm2pi]
    have h3 : c * (3 * ((m₂ : ℝ) + 1)) < ‖a m₂ - a m₁‖ := by
      rwa [lt_div_iff₀ (by positivity)] at hc
    calc c * (3 * ((m₂ : ℝ) + 1) / (2 * Real.pi)) = c * (3 * ((m₂ : ℝ) + 1)) / (2 * Real.pi) := by
          ring
      _ < ‖a m₂ - a m₁‖ / (2 * Real.pi) := div_lt_div_of_pos_right h3 (by positivity)
  have hev : ∀ᶠ ε in 𝓝[>] 0, c * (3 * ((m₂ : ℝ) + 1) / (2 * Real.pi)) < ‖Ψ ε‖ :=
    hΨt.norm.eventually (lt_mem_nhds hlim)
  have hev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hevε : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c ≤ 2 * ε / ((m₂ : ℝ) + 1) * abelMass g (2 * ε / ((m₂ : ℝ) + 1)) := by
    filter_upwards [hev, hev1, self_mem_nhdsWithin] with ε h1 h2 h3
    have h3' : (0 : ℝ) < ε := h3
    have hb₂ := mul_norm_defectLaplace_le_abelMass hgm' hgb hm₂ le_rfl h3' h2
    have hb₁ := mul_norm_defectLaplace_le_abelMass hgm' hgb hm₁ hm₁₂ h3' h2
    have hΨle : ‖Ψ ε‖ ≤ ε * ‖defectLaplace g ((ε : ℂ) + (m₂ : ℂ) * I)‖ +
        ε * ‖defectLaplace g ((ε : ℂ) + (m₁ : ℂ) * I)‖ := by
      simp only [hΨ]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h3', ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) h3'.le
    have hkey : 3 / Real.pi * (ε * abelMass g (2 * ε / ((m₂ : ℝ) + 1))) =
        3 * ((m₂ : ℝ) + 1) / (2 * Real.pi) *
          (2 * ε / ((m₂ : ℝ) + 1) * abelMass g (2 * ε / ((m₂ : ℝ) + 1))) := by
      field_simp
    have hlt : c * (3 * ((m₂ : ℝ) + 1) / (2 * Real.pi)) <
        3 * ((m₂ : ℝ) + 1) / (2 * Real.pi) *
          (2 * ε / ((m₂ : ℝ) + 1) * abelMass g (2 * ε / ((m₂ : ℝ) + 1))) := by
      rw [← hkey]
      have : 3 / (2 * Real.pi) * (ε * abelMass g (2 * ε / ((m₂ : ℝ) + 1))) +
          3 / (2 * Real.pi) * (ε * abelMass g (2 * ε / ((m₂ : ℝ) + 1))) =
          3 / Real.pi * (ε * abelMass g (2 * ε / ((m₂ : ℝ) + 1))) := by
        field_simp; ring
      linarith
    rw [mul_comm c] at hlt
    exact (lt_of_mul_lt_mul_left hlt hK.le).le
  -- change variables `ε = δ (m₂ + 1)/2`
  have hmap : Tendsto (fun δ : ℝ => δ * ((m₂ : ℝ) + 1) / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : Continuous fun δ : ℝ => δ * ((m₂ : ℝ) + 1) / 2 := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ' : (0 : ℝ) < δ := hδ
      exact div_pos (mul_pos hδ' hM1) two_pos
  filter_upwards [hmap.eventually hevε] with δ hδ
  have he : 2 * (δ * ((m₂ : ℝ) + 1) / 2) / ((m₂ : ℝ) + 1) = δ := by
    field_simp
  rwa [he] at hδ

/-- **Two unequal coefficients exclude an Abel-sublinear defect.** -/
theorem not_tendsto_mul_abelMass_of_coeff_ne {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₁₂ : m₁ ≤ m₂) (hne : a m₁ ≠ a m₂) :
    ¬ Tendsto (fun δ => δ * abelMass g δ) (𝓝[>] 0) (𝓝 0) := by
  intro ht
  have hpos : 0 < ‖a m₂ - a m₁‖ / (3 * ((m₂ : ℝ) + 1)) :=
    div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)) (by positivity)
  have h1 := eventually_le_mul_abelMass_of_coeff_ne ha hH hm₁ hm₁₂ (half_lt_self hpos)
  have h2 := ht.eventually (gt_mem_nhds (half_pos hpos))
  obtain ⟨δ, hδ1, hδ2⟩ := (h1.and h2).exists
  linarith

/-- **Two unequal coefficients exclude a defect tending to zero.** -/
theorem not_tendsto_zero_of_coeff_ne {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₁₂ : m₁ ≤ m₂) (hne : a m₁ ≠ a m₂) :
    ¬ ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R ≤ |t| → ‖g t‖ ≤ ε := by
  intro hlim
  obtain ⟨-, -, -, -, -, -, -, hgm, Cg, N, hgb⟩ := id hH
  obtain ⟨R, hR0, hR⟩ := hlim 1 one_pos
  -- a defect tending to zero is bounded
  have hM : ∀ t, ‖g t‖ ≤ max (Cg * (1 + R) ^ N) 1 := by
    intro t
    by_cases ht : R ≤ |t|
    · exact (hR t ht).trans (le_max_right _ _)
    · push Not at ht
      have hCg : 0 ≤ Cg := by have := (norm_nonneg _).trans (hgb 0); simpa using this
      refine (hgb t).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (by linarith) N) hCg).trans (le_max_left _ _))
  exact not_tendsto_mul_abelMass_of_coeff_ne ha hH hm₁ hm₁₂ hne
    (RHTower.FractionalMassPolynomialTailRigidity.tendsto_mul_abelMass_of_tendsto_zero hM
      hgm.aestronglyMeasurable hlim)

/-- **No power-decaying defect.**  If two coefficients differ, `g` is not
`O((1 + |t|)^{-α})` for any `α > 0`; in particular not `O(|t|^{-1/2+ε})` for `ε < 1/2`. -/
theorem not_le_rpow_neg_of_coeff_ne {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₁₂ : m₁ ≤ m₂) (hne : a m₁ ≠ a m₂)
    {α : ℝ} (hα : 0 < α) (C₁ : ℝ) :
    ¬ ∀ t : ℝ, ‖g t‖ ≤ C₁ * (1 + |t|) ^ (-α) := by
  intro hb
  refine not_tendsto_zero_of_coeff_ne ha hH hm₁ hm₁₂ hne fun ε hε => ?_
  -- `(1 + R)^{-α} ≤ ε / (|C₁| + 1)` for `R` large
  have ht : Tendsto (fun R : ℝ => (1 + R) ^ (-α)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hα).comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
  obtain ⟨R, hR⟩ := (ht.eventually (gt_mem_nhds (div_pos hε
    (by positivity : (0 : ℝ) < |C₁| + 1)))).and (eventually_ge_atTop 0) |>.exists
  refine ⟨R, hR.2, fun t htR => ?_⟩
  have h1 : (1 + |t|) ^ (-α) ≤ (1 + R) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [hR.2]) (by linarith) (by linarith)
  have h0 : 0 ≤ (1 + |t|) ^ (-α) := by positivity
  calc ‖g t‖ ≤ C₁ * (1 + |t|) ^ (-α) := hb t
    _ ≤ |C₁| * (1 + |t|) ^ (-α) := mul_le_mul_of_nonneg_right (le_abs_self _) h0
    _ ≤ (|C₁| + 1) * (1 + R) ^ (-α) := by gcongr; linarith
    _ ≤ (|C₁| + 1) * (ε / (|C₁| + 1)) := by gcongr; exact hR.1.le
    _ = ε := by field_simp

end GaloisForLFunctions.EulerFETransportTheory
