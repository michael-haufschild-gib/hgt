import GaloisForLFunctions.RHTower.WeilBoundedDenominatorLockPeriodicity
import GaloisForLFunctions.HTGeometry.BohrParseval
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Symmetric Rational Zero-Relocation Preserves the Functional Equation but Destroys Vertical Bohr Almost Periodicity

Can a one-off off-line zero quartet `{ρ₀, conj ρ₀, 1 − ρ₀, 1 − conj ρ₀}` be implanted into `ζ(s)`
by multiplying `ξ(s)` by a rational factor `R(s)` that preserves the exact `s ↔ 1 − s` functional
equation, critical-line reality, and `1 + O(|t|^{−1})` vertical asymptotics?

This module constructs the canonical `s ↔ 1 − s` symmetric degree-4 rational zero-relocation factor
`zeroRelocationFactor ρ₀ γ₁ γ₂` and proves the exact structural obstruction separating it from `ζ`:

1. **Asymptotically unitary multiplier rigidity for Bohr almost-periodic functions**
   (`isBohrAlmostPeriodic_mul_iff_eq_zero_of_tendsto_one`,
   `not_isBohrAlmostPeriodic_mul_of_tendsto_one`):
   If `F, m : ℝ → ℂ` are continuous with `F` Bohr almost periodic and `m(t) → 1` as `t → +∞`, then
   `F · m` is Bohr almost periodic if and only if `F(t) (m(t) − 1) = 0` for all `t ∈ ℝ`.

2. **Vertical Bohr almost periodicity of `ζ` on `Re s > 1` and ordinary Dirichlet-series no-go**
   (`isBohrAlmostPeriodic_riemannZeta_vertical`,
   `not_isBohrAlmostPeriodic_riemannZeta_mul_vertical`,
   `no_summable_LSeries_eq_riemannZeta_mul_vertical`):
   On every vertical line `Re s = σ > 1`, `t ↦ ζ(σ + it)` is continuous, nowhere zero, and Bohr
   almost periodic; multiplying `ζ` by any continuous factor `M(σ + it) → 1` not identically `1` on
   `Re s = σ` destroys vertical Bohr almost periodicity and rules out any absolutely convergent
   ordinary Dirichlet series representation `LSeries a` at abscissa `σ`.

3. **Symmetric rational zero-relocation factor and complete Bohr obstruction**
   (`zeroRelocationFactor_one_sub`, `completedRiemannZeta_mul_zeroRelocationFactor_one_sub`,
   `zeroRelocationFactor_eq_zero_iff_of_half_lt_re`,
   `tendsto_zeroRelocationFactor_vertical_atTop`,
   `exists_vertical_zeroRelocationFactor_ne_one`,
   `zeroRelocation_destroys_vertical_bohr_and_LSeries`,
   `zeroRelocationFactor_two_mul_sub_one_eq_zero`):
   `completedRiemannZeta s * zeroRelocationFactor ρ₀ γ₁ γ₂ s` satisfies the exact Riemann
   functional equation and carries the isolated right-half-plane zero set `{ρ₀, conj ρ₀}`, yet on
   **every** vertical line `Re s = σ > 1` it fails to be Bohr almost periodic (hence admits no
   ordinary Dirichlet series of any finite abscissa of absolute convergence `σ > 1`), and vanishes
   at the half-shifted Eisenstein scattering argument `2 s_* − 1` for `s_* = (1 + ρ₀) / 2 ∈ (3/4, 1)`.
-/

open Complex Filter Topology Set
open HTGeometry

namespace GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

/-! ### 1. Asymptotically unitary multiplier rigidity for Bohr almost-periodic functions -/

/-- **Asymptotically unitary multiplier rigidity.** Let `F, m : ℝ → ℂ` be continuous with `F` Bohr
almost periodic and `m(t) → 1` as `t → +∞`. Then `t ↦ F(t) m(t)` is Bohr almost periodic if and
only if `F(t) (m(t) − 1) = 0` for all `t ∈ ℝ`. -/
theorem isBohrAlmostPeriodic_mul_iff_eq_zero_of_tendsto_one {F m : ℝ → ℂ}
    (hFc : Continuous F) (hFa : IsBohrAlmostPeriodic F) (hmc : Continuous m)
    (hlim : Tendsto m atTop (𝓝 1)) :
    IsBohrAlmostPeriodic (fun t => F t * m t) ↔ ∀ t : ℝ, F t * (m t - 1) = 0 := by
  constructor
  · intro hG
    obtain ⟨C, hC⟩ := GaloisForLFunctions.exists_bound_of_isBohrAlmostPeriodic hFc hFa
    have hH_ap : IsBohrAlmostPeriodic (fun t => F t * m t - F t) :=
      GaloisForLFunctions.isBohrAlmostPeriodic_sub (hFc.mul hmc) hG hFc hFa
    have hsub0 : Tendsto (fun t => ‖m t - 1‖) atTop (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : ℂ)).comp (tendsto_sub_nhds_zero_iff.mpr hlim)
    have hH_lim : Tendsto (fun t => F t * m t - F t) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun t => max C 0 * ‖m t - 1‖) (fun t => ?_) ?_
      · rw [show F t * m t - F t = F t * (m t - 1) by ring, norm_mul]
        exact mul_le_mul_of_nonneg_right ((hC t).trans (le_max_left _ _)) (norm_nonneg _)
      · simpa [mul_zero] using hsub0.const_mul (max C 0)
    intro t
    have h0 := HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero hH_ap hH_lim t
    linear_combination h0
  · intro hall
    have heq : (fun t => F t * m t) = F := by
      funext t
      linear_combination hall t
    rwa [heq]

/-- Multiplying a nonvanishing continuous Bohr almost-periodic function by a nontrivial continuous
multiplier `m(t) → 1` destroys Bohr almost periodicity. -/
theorem not_isBohrAlmostPeriodic_mul_of_tendsto_one {F m : ℝ → ℂ}
    (hFc : Continuous F) (hFa : IsBohrAlmostPeriodic F) (hFne : ∀ t : ℝ, F t ≠ 0)
    (hmc : Continuous m) (hlim : Tendsto m atTop (𝓝 1)) (hne : ∃ t₀ : ℝ, m t₀ ≠ 1) :
    ¬ IsBohrAlmostPeriodic (fun t => F t * m t) := by
  rw [isBohrAlmostPeriodic_mul_iff_eq_zero_of_tendsto_one hFc hFa hmc hlim]
  push Not
  obtain ⟨t₀, ht₀⟩ := hne
  exact ⟨t₀, mul_ne_zero (hFne t₀) (sub_ne_zero.mpr ht₀)⟩

/-! ### 2. Vertical Bohr almost periodicity of `riemannZeta` on `Re s > 1` -/

/-- On every vertical line `Re s = σ > 1`, `t ↦ riemannZeta (σ + t * I)` is Bohr almost periodic. -/
theorem isBohrAlmostPeriodic_riemannZeta_vertical {σ : ℝ} (hσ : 1 < σ) :
    IsBohrAlmostPeriodic (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I)) := by
  have hsum : LSeriesSummable 1 (σ : ℂ) := LSeriesSummable_one_iff.mpr (by simpa using hσ)
  have hap := RHTower.isBohrAlmostPeriodic_LSeries_vertical hsum
  have heq : (fun y : ℝ => LSeries 1 ((σ : ℂ) + (y : ℂ) * I)) =
      fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) := by
    funext t
    exact LSeries_one_eq_riemannZeta (by simp [hσ])
  rwa [heq] at hap

theorem continuous_riemannZeta_vertical {σ : ℝ} (hσ : 1 < σ) :
    Continuous (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I)) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hne1 : (σ : ℂ) + (t : ℂ) * I ≠ 1 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hd : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + (t : ℂ) * I) :=
    differentiableAt_riemannZeta hne1
  exact hd.continuousAt.comp (by fun_prop)

/-- Multiplying `riemannZeta` on `Re s = σ > 1` by any continuous factor `m(t) → 1` not identically
`1` destroys Bohr almost periodicity. -/
theorem not_isBohrAlmostPeriodic_riemannZeta_mul_vertical {σ : ℝ} (hσ : 1 < σ) {m : ℝ → ℂ}
    (hmc : Continuous m) (hlim : Tendsto m atTop (𝓝 1)) (hne : ∃ t₀ : ℝ, m t₀ ≠ 1) :
    ¬ IsBohrAlmostPeriodic (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) * m t) :=
  not_isBohrAlmostPeriodic_mul_of_tendsto_one
    (continuous_riemannZeta_vertical hσ)
    (isBohrAlmostPeriodic_riemannZeta_vertical hσ)
    (fun t => riemannZeta_ne_zero_of_one_lt_re (by simp [hσ]))
    hmc hlim hne

/-- No absolutely convergent ordinary Dirichlet series `LSeries a` at `σ > 1` can equal
`riemannZeta (σ + it) * m(t)` along `Re s = σ` when `m` is continuous, `m(t) → 1`, and `m ≠ 1`. -/
theorem no_summable_LSeries_eq_riemannZeta_mul_vertical {σ : ℝ} (hσ : 1 < σ) {m : ℝ → ℂ}
    (hmc : Continuous m) (hlim : Tendsto m atTop (𝓝 1)) (hne : ∃ t₀ : ℝ, m t₀ ≠ 1)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ : ℂ)) :
    ¬ ∀ t : ℝ, LSeries a ((σ : ℂ) + (t : ℂ) * I) =
        riemannZeta ((σ : ℂ) + (t : ℂ) * I) * m t := by
  intro heq
  have hap := RHTower.isBohrAlmostPeriodic_LSeries_vertical ha
  rw [funext heq] at hap
  exact not_isBohrAlmostPeriodic_riemannZeta_mul_vertical hσ hmc hlim hne hap

/-! ### 3. The `s ↔ 1 − s` symmetric rational zero-relocation factor -/

/-- Degree-4 monic numerator vanishing on the symmetric off-line quartet
`{ρ₀, conj ρ₀, 1 − ρ₀, 1 − conj ρ₀}`. -/
def zeroRelocationNum (ρ₀ s : ℂ) : ℂ :=
  (s - ρ₀) * (s - starRingEnd ℂ ρ₀) * (s - (1 - ρ₀)) * (s - (1 - starRingEnd ℂ ρ₀))

/-- Degree-4 monic denominator vanishing at the two critical-line pairs `1/2 ± iγ₁`, `1/2 ± iγ₂`. -/
def zeroRelocationDen (γ₁ γ₂ : ℝ) (s : ℂ) : ℂ :=
  (s - (1 / 2 + I * γ₁)) * (s - (1 / 2 - I * γ₁)) *
    (s - (1 / 2 + I * γ₂)) * (s - (1 / 2 - I * γ₂))

/-- The `s ↔ 1 − s` and conjugate-symmetric rational zero-relocation factor. -/
def zeroRelocationFactor (ρ₀ : ℂ) (γ₁ γ₂ : ℝ) (s : ℂ) : ℂ :=
  zeroRelocationNum ρ₀ s / zeroRelocationDen γ₁ γ₂ s

theorem zeroRelocationNum_one_sub (ρ₀ s : ℂ) :
    zeroRelocationNum ρ₀ (1 - s) = zeroRelocationNum ρ₀ s := by
  unfold zeroRelocationNum
  ring

theorem zeroRelocationDen_one_sub (γ₁ γ₂ : ℝ) (s : ℂ) :
    zeroRelocationDen γ₁ γ₂ (1 - s) = zeroRelocationDen γ₁ γ₂ s := by
  unfold zeroRelocationDen
  ring

/-- **Exact `s ↔ 1 − s` functional equation invariance** of `zeroRelocationFactor`. -/
theorem zeroRelocationFactor_one_sub (ρ₀ : ℂ) (γ₁ γ₂ : ℝ) (s : ℂ) :
    zeroRelocationFactor ρ₀ γ₁ γ₂ (1 - s) = zeroRelocationFactor ρ₀ γ₁ γ₂ s := by
  rw [zeroRelocationFactor, zeroRelocationFactor, zeroRelocationNum_one_sub,
    zeroRelocationDen_one_sub]

/-- Dressing `completedRiemannZeta` by `zeroRelocationFactor` preserves the exact `s ↔ 1 − s`
functional equation on all of `ℂ`. -/
theorem completedRiemannZeta_mul_zeroRelocationFactor_one_sub (ρ₀ : ℂ) (γ₁ γ₂ : ℝ) (s : ℂ) :
    completedRiemannZeta (1 - s) * zeroRelocationFactor ρ₀ γ₁ γ₂ (1 - s) =
      completedRiemannZeta s * zeroRelocationFactor ρ₀ γ₁ γ₂ s := by
  rw [completedRiemannZeta_one_sub, zeroRelocationFactor_one_sub]

/-- Conjugate symmetry `R(conj s) = conj(R(s))`. -/
theorem zeroRelocationFactor_conj (ρ₀ : ℂ) (γ₁ γ₂ : ℝ) (s : ℂ) :
    zeroRelocationFactor ρ₀ γ₁ γ₂ (starRingEnd ℂ s) =
      starRingEnd ℂ (zeroRelocationFactor ρ₀ γ₁ γ₂ s) := by
  unfold zeroRelocationFactor zeroRelocationNum zeroRelocationDen
  simp only [map_div₀, map_mul, map_sub, map_add, map_one, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

/-- Critical-line reality: `zeroRelocationFactor ρ₀ γ₁ γ₂ (1/2 + it)` is real for all `t ∈ ℝ`. -/
theorem im_zeroRelocationFactor_criticalLine (ρ₀ : ℂ) (γ₁ γ₂ t : ℝ) :
    (zeroRelocationFactor ρ₀ γ₁ γ₂ (1 / 2 + I * t)).im = 0 := by
  have h1 : 1 - ((1 / 2 : ℂ) + I * (t : ℂ)) = starRingEnd ℂ ((1 / 2 : ℂ) + I * (t : ℂ)) := by
    simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  have hsym := (zeroRelocationFactor_one_sub ρ₀ γ₁ γ₂ ((1 / 2 : ℂ) + I * (t : ℂ))).symm.trans
    (h1 ▸ zeroRelocationFactor_conj ρ₀ γ₁ γ₂ ((1 / 2 : ℂ) + I * (t : ℂ)))
  exact Complex.conj_eq_iff_im.mp hsym.symm

/-- `zeroRelocationDen γ₁ γ₂` is nonvanishing off `Re s = 1/2` (in particular on `Re s > 1/2`). -/
theorem zeroRelocationDen_ne_zero_of_re_ne_half (γ₁ γ₂ : ℝ) {s : ℂ} (hs : s.re ≠ 1 / 2) :
    zeroRelocationDen γ₁ γ₂ s ≠ 0 := by
  unfold zeroRelocationDen
  have hfactor : ∀ c : ℂ, c.re = 1 / 2 → s - c ≠ 0 := fun c hc h0 =>
    hs (by rw [sub_eq_zero.mp h0, hc])
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
    exact hfactor _ (by simp)

/-- Holomorphy of `zeroRelocationFactor` on `{s : ℂ | s.re ≠ 1/2}`. -/
theorem differentiableAt_zeroRelocationFactor (ρ₀ : ℂ) (γ₁ γ₂ : ℝ) {s : ℂ} (hs : s.re ≠ 1 / 2) :
    DifferentiableAt ℂ (zeroRelocationFactor ρ₀ γ₁ γ₂) s := by
  unfold zeroRelocationFactor zeroRelocationNum zeroRelocationDen
  exact DifferentiableAt.div (by fun_prop) (by fun_prop)
    (zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ hs)

/-- **Exact isolated right-half-plane zero set `{ρ₀, conj ρ₀}`.** When `1/2 < Re ρ₀`, on
`Re s > 1/2` the rational factor is holomorphic and vanishes precisely at `ρ₀` and `conj ρ₀`. -/
theorem zeroRelocationFactor_eq_zero_iff_of_half_lt_re {ρ₀ : ℂ} (hρ₀ : 1 / 2 < ρ₀.re)
    (γ₁ γ₂ : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    zeroRelocationFactor ρ₀ γ₁ γ₂ s = 0 ↔ s = ρ₀ ∨ s = starRingEnd ℂ ρ₀ := by
  have hden : zeroRelocationDen γ₁ γ₂ s ≠ 0 :=
    zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ hs.ne'
  rw [zeroRelocationFactor, div_eq_zero_iff]
  simp only [hden, or_false, zeroRelocationNum]
  have h3 : s - (1 - ρ₀) ≠ 0 := fun h => by
    have := congrArg Complex.re (sub_eq_zero.mp h)
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  have h4 : s - (1 - starRingEnd ℂ ρ₀) ≠ 0 := fun h => by
    have := congrArg Complex.re (sub_eq_zero.mp h)
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at this
    linarith
  simp only [mul_eq_zero, h3, h4, or_false, sub_eq_zero]

/-- Monic linear factor normalized along vertical lines: `(σ + it − a) / (σ + it) → 1` as `t → +∞`. -/
private theorem tendsto_vertical_sub_div_self (σ : ℝ) (a : ℂ) :
    Tendsto (fun t : ℝ => (((σ : ℂ) + (t : ℂ) * I) - a) / ((σ : ℂ) + (t : ℂ) * I))
      atTop (𝓝 1) := by
  have hinv : Tendsto (fun t : ℝ => a / ((σ : ℂ) + (t : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      (by simpa [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul ‖a‖)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have him : t ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := by
      have h := Complex.abs_im_le_norm ((σ : ℂ) + (t : ℂ) * I)
      simpa [abs_of_pos ht] using h
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg a) ht him
  have hlim : Tendsto (fun t : ℝ => (1 : ℂ) - a / ((σ : ℂ) + (t : ℂ) * I)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hne : (σ : ℂ) + (t : ℂ) * I ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  rw [sub_div, div_self hne]

/-- **Asymptotically unitary vertical limit.** On every vertical line `Re s = σ`,
`zeroRelocationFactor ρ₀ γ₁ γ₂ (σ + it) → 1` as `t → +∞`. -/
theorem tendsto_zeroRelocationFactor_vertical_atTop (ρ₀ : ℂ) (γ₁ γ₂ σ : ℝ) :
    Tendsto (fun t : ℝ => zeroRelocationFactor ρ₀ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I))
      atTop (𝓝 1) := by
  have hprod4 : ∀ a₁ a₂ a₃ a₄ : ℂ,
      Tendsto (fun t : ℝ =>
        ((((σ : ℂ) + (t : ℂ) * I - a₁) * ((σ : ℂ) + (t : ℂ) * I - a₂) *
          ((σ : ℂ) + (t : ℂ) * I - a₃) * ((σ : ℂ) + (t : ℂ) * I - a₄)) /
          ((σ : ℂ) + (t : ℂ) * I) ^ 4)) atTop (𝓝 1) := by
    intro a₁ a₂ a₃ a₄
    have h4 : Tendsto (fun t : ℝ =>
        ((((σ : ℂ) + (t : ℂ) * I - a₁) / ((σ : ℂ) + (t : ℂ) * I)) *
          (((σ : ℂ) + (t : ℂ) * I - a₂) / ((σ : ℂ) + (t : ℂ) * I))) *
          ((((σ : ℂ) + (t : ℂ) * I - a₃) / ((σ : ℂ) + (t : ℂ) * I)) *
            (((σ : ℂ) + (t : ℂ) * I - a₄) / ((σ : ℂ) + (t : ℂ) * I)))) atTop (𝓝 1) := by
      simpa using ((tendsto_vertical_sub_div_self σ a₁).mul
        (tendsto_vertical_sub_div_self σ a₂)).mul
        ((tendsto_vertical_sub_div_self σ a₃).mul (tendsto_vertical_sub_div_self σ a₄))
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t _
    ring
  have hnum := hprod4 ρ₀ (starRingEnd ℂ ρ₀) (1 - ρ₀) (1 - starRingEnd ℂ ρ₀)
  have hden := hprod4 (1 / 2 + I * γ₁) (1 / 2 - I * γ₁) (1 / 2 + I * γ₂) (1 / 2 - I * γ₂)
  have hquot : Tendsto (fun t : ℝ =>
      (zeroRelocationNum ρ₀ ((σ : ℂ) + (t : ℂ) * I) / ((σ : ℂ) + (t : ℂ) * I) ^ 4) /
        (zeroRelocationDen γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) / ((σ : ℂ) + (t : ℂ) * I) ^ 4))
      atTop (𝓝 1) := by
    simpa using hnum.div hden one_ne_zero
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hne : (σ : ℂ) + (t : ℂ) * I ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hpow_ne : ((σ : ℂ) + (t : ℂ) * I) ^ 4 ≠ 0 := pow_ne_zero 4 hne
  rw [zeroRelocationFactor, div_div_div_cancel_right₀ hpow_ne]

/-- **Nontriviality on every vertical line off `Re s = 1/2`.** Whenever `1/2 < Re ρ₀`, on every
vertical line `Re s = σ ≠ 1/2`, `zeroRelocationFactor ρ₀ γ₁ γ₂ (σ + it)` is not identically `1`. -/
theorem exists_vertical_zeroRelocationFactor_ne_one {ρ₀ : ℂ} (hρ₀ : 1 / 2 < ρ₀.re)
    (γ₁ γ₂ : ℝ) {σ : ℝ} (hσ : σ ≠ 1 / 2) :
    ∃ t₀ : ℝ, zeroRelocationFactor ρ₀ γ₁ γ₂ ((σ : ℂ) + (t₀ : ℂ) * I) ≠ 1 := by
  by_contra hall
  push Not at hall
  set P : ℂ → ℂ := fun z => zeroRelocationNum ρ₀ z - zeroRelocationDen γ₁ γ₂ z
  have hP_diff : Differentiable ℂ P := by
    unfold P zeroRelocationNum zeroRelocationDen
    fun_prop
  have hP_analytic : AnalyticOnNhd ℂ P Set.univ :=
    hP_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hline : ∀ t : ℝ, P ((σ : ℂ) + (t : ℂ) * I) = 0 := by
    intro t
    have hden : zeroRelocationDen γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) ≠ 0 :=
      zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ (by simpa using hσ)
    have h1 := (div_eq_one_iff_eq hden).mp (hall t)
    exact sub_eq_zero.mpr h1
  have hfreq : ∃ᶠ z in 𝓝[≠] (σ : ℂ), P z = 0 := by
    rw [Filter.frequently_iff_seq_forall]
    refine ⟨fun n : ℕ => (σ : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I, ?_, fun n => hline _⟩
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have hinv : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 0) := by
        simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp
          tendsto_one_div_add_atTop_nhds_zero_nat).mul_const I
      simpa using tendsto_const_nhds.add hinv
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add] at him
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hzero_all := hP_analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (mem_univ (σ : ℂ)) hfreq (mem_univ ρ₀)
  have hnum0 : zeroRelocationNum ρ₀ ρ₀ = 0 := by simp [zeroRelocationNum]
  have hden_ne : zeroRelocationDen γ₁ γ₂ ρ₀ ≠ 0 :=
    zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ hρ₀.ne'
  exact hden_ne (by linear_combination -hzero_all + hnum0)

/-- **Half-shift Eisenstein scattering obstruction.** At `s_* = (1 + ρ₀) / 2`, which satisfies
`3/4 < Re s_* < 1` whenever `1/2 < Re ρ₀ < 1`, the half-shifted argument `2 s_* − 1` equals `ρ₀`,
forcing `zeroRelocationFactor ρ₀ γ₁ γ₂ (2 s_* − 1) = 0`. -/
theorem zeroRelocationFactor_two_mul_sub_one_eq_zero {ρ₀ : ℂ} (hρ₀_gt : 1 / 2 < ρ₀.re)
    (hρ₀_lt : ρ₀.re < 1) (γ₁ γ₂ : ℝ) :
    3 / 4 < ((1 + ρ₀) / 2).re ∧ ((1 + ρ₀) / 2).re < 1 ∧
      zeroRelocationFactor ρ₀ γ₁ γ₂ (2 * ((1 + ρ₀) / 2) - 1) = 0 := by
  have hre : ((1 + ρ₀) / 2).re = (1 + ρ₀.re) / 2 := by
    simp [add_div]
  refine ⟨by rw [hre]; linarith, by rw [hre]; linarith, ?_⟩
  have harg : 2 * ((1 + ρ₀) / 2) - 1 = ρ₀ := by ring
  rw [harg]
  exact (zeroRelocationFactor_eq_zero_iff_of_half_lt_re hρ₀_gt γ₁ γ₂ hρ₀_gt).mpr (Or.inl rfl)

/-- **Complete Bohr and ordinary Dirichlet-series obstruction for symmetric rational zero relocation.**
For every off-line target `ρ₀` (`1/2 < Re ρ₀ < 1`), every `γ₁, γ₂ ∈ ℝ`, and every abscissa `σ > 1`:
1. `completedRiemannZeta · zeroRelocationFactor ρ₀ γ₁ γ₂` satisfies the exact `s ↔ 1 − s`
   functional equation and carries the isolated right-half-plane zero set `{ρ₀, conj ρ₀}` on
   `zeroRelocationFactor`;
2. on the vertical line `Re s = σ`, `riemannZeta (σ + it) * zeroRelocationFactor ρ₀ γ₁ γ₂ (σ + it)`
   is **not** Bohr almost periodic;
3. no absolutely convergent ordinary Dirichlet series `LSeries a` at `σ` can represent
   `riemannZeta · zeroRelocationFactor ρ₀ γ₁ γ₂` on `Re s = σ`. -/
theorem zeroRelocation_destroys_vertical_bohr_and_LSeries {ρ₀ : ℂ} (hρ₀_gt : 1 / 2 < ρ₀.re)
    (γ₁ γ₂ : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (∀ s : ℂ, completedRiemannZeta (1 - s) * zeroRelocationFactor ρ₀ γ₁ γ₂ (1 - s) =
      completedRiemannZeta s * zeroRelocationFactor ρ₀ γ₁ γ₂ s) ∧
    ¬ IsBohrAlmostPeriodic
      (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        zeroRelocationFactor ρ₀ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I)) ∧
    (∀ a : ℕ → ℂ, LSeriesSummable a (σ : ℂ) →
      ¬ ∀ t : ℝ, LSeries a ((σ : ℂ) + (t : ℂ) * I) =
          riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
            zeroRelocationFactor ρ₀ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I)) := by
  have hmc : Continuous (fun t : ℝ => zeroRelocationFactor ρ₀ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (differentiableAt_zeroRelocationFactor ρ₀ γ₁ γ₂
      (by simp; linarith)).continuousAt.comp (by fun_prop)
  have hlim := tendsto_zeroRelocationFactor_vertical_atTop ρ₀ γ₁ γ₂ σ
  have hne := exists_vertical_zeroRelocationFactor_ne_one hρ₀_gt γ₁ γ₂ (by linarith : σ ≠ 1 / 2)
  exact ⟨completedRiemannZeta_mul_zeroRelocationFactor_one_sub ρ₀ γ₁ γ₂,
    not_isBohrAlmostPeriodic_riemannZeta_mul_vertical hσ hmc hlim hne,
    fun a ha => no_summable_LSeries_eq_riemannZeta_mul_vertical hσ hmc hlim hne a ha⟩

end

end GaloisForLFunctions.ArithmeticPositiveDuality
