import GaloisForLFunctions.RHTower.BagchiConditionedTailGap
import GaloisForLFunctions.RHTower.CarlsonZetaMeanSquare
import GaloisForLFunctions.RHTower.Sieve.ZetaTruncated

/-!
# The Bagchi–Carlson–Abel centered-tail bridge in the critical strip

This module connects three components of the Bagchi self-return programme (`BAG`):
1. the conditioned-tail decomposition of `BagchiConditionedTailGap.lean` (`centeredZetaTail`,
   `centeredZetaTailReturnSet`),
2. Carlson's vertical mean-square formula of `CarlsonZetaMeanSquare.lean` (`zetaDirichletTail`,
   `carlson_zeta_tail_meanSquare`, `tendsto_zetaCoefficientTailMass`), and
3. the truncated Abel fractional-part formula of `Sieve/ZetaTruncated.lean`
   (`Sieve.riemannZeta_eq_sum_add_tail`, `Sieve.norm_integral_Ioi_fract_cpow_le`).

For the unsmoothed Dirichlet head `edPoly (fun _ => 1) (Finset.Icc 1 M)`, combining these three
components yields the exact three-term identity (`centeredZetaTail_eq_shiftedTail_add_pole_add_fract`)
$$\mathrm{centeredZetaTail}\ 1\ [1,M]\ z\ \tau
  = \mathrm{zetaDirichletTail}\ M\ (\mathrm{Re}\,z)\ (\mathrm{Im}\,z + \tau)
    + \frac{M^{1-z}}{1-z}
    + z \int_M^\infty \{t\}\,t^{-(z+1)}\,dt.$$

This decomposition exposes a sharp dichotomy on $1/2 < \mathrm{Re}\,z < 1$:
* **Unsmoothed centered-tail blowup and density-zero collapse**: While the shifted tail
  $\tau \mapsto \mathrm{zetaDirichletTail}\ M\ (\mathrm{Re}\,z)\ (\mathrm{Im}\,z + \tau)$ has
  limiting vertical mean square $\sum_{n > M} n^{-2\,\mathrm{Re}\,z} \to 0$ as $M \to \infty$
  (`carlson_zeta_tail_shifted_meanSquare`), the fixed base-point tail retains the $\tau$-independent
  Abel pole $M^{1-z}/(1-z)$ of norm $M^{1-\mathrm{Re}\,z}/\|1-z\| \to +\infty$
  (`tendsto_norm_zetaDirichletTail_base_atTop`). Consequently, as $M \to \infty$, the vertical
  $L^2$ mean square of `centeredZetaTail (fun _ => 1) (Finset.Icc 1 M) z` diverges to $+\infty$
  (`centeredZetaTail_L2_divergence`), and for every compact $K$ containing $z$ the return set
  `centeredZetaTailReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε` (and its intersection with
  `edPolyReturnSet`) collapses to asymptotic density zero
  (`eventually_eventually_volume_centeredZetaTailReturnSet_le`,
  `eventually_eventually_volume_headReturn_inter_centeredTailReturn_le`).
* **Positive survivor 1 (`abelCenteredZetaTail`)**: Subtracting the explicit base-point Abel pole
  $M^{1-z}/(1-z)$ defines `abelCenteredZetaTail M z τ`, which differs from the shifted Carlson tail
  by at most $\|z\| M^{-\mathrm{Re}\,z} / \mathrm{Re}\,z$ uniformly in $\tau$
  (`norm_abelCenteredZetaTail_sub_shiftedTail_le`). Unlike `centeredZetaTail`,
  `abelCenteredZetaTail M z` has vanishing vertical $L^2$ mean square as $M \to \infty$
  (`abelCenteredZetaTail_L2_approximation`), its complement bad set has asymptotic density zero
  (`eventually_eventually_volume_abelCenteredZetaTail_ge_le`), and conditioned transfer on
  `edPolyReturnSet` controls $\zeta(z + i\tau) - \zeta(z) - M^{1-z}/(1-z)$
  (`exists_density_with_abelCenteredTail_transfer`).
* **Positive survivor 2 (Two-shift base cancellation)**: Taking the difference between two shifts
  $\tau_1, \tau_2$ (`centeredZetaTail_sub_centeredZetaTail_eq`) cancels the base-point tail and its
  Abel pole identically, reducing the re-anchored centered tail at $z + i\tau_1$ to the difference
  of two shifted Carlson tails (`norm_centeredZetaTail_shift_lt_of_zetaDirichletTail`).
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

/-! ## 1. Exact bridge between `centeredZetaTail`, `zetaDirichletTail`, and Abel truncation -/

theorem edPoly_one_Icc_eq_zetaDirichletHead (M : ℕ) (z : ℂ) :
    edPoly (fun _ => 1) (Finset.Icc 1 M) z = zetaDirichletHead M z.re z.im := by
  unfold zetaDirichletHead
  rw [Complex.re_add_im]

theorem riemannZeta_sub_edPoly_one_Icc_eq_zetaDirichletTail (M : ℕ) (z : ℂ) :
    riemannZeta z - edPoly (fun _ => 1) (Finset.Icc 1 M) z =
      zetaDirichletTail M z.re z.im := by
  unfold zetaDirichletTail
  rw [edPoly_one_Icc_eq_zetaDirichletHead, Complex.re_add_im]

theorem riemannZeta_shift_sub_edPoly_one_Icc_eq_zetaDirichletTail (M : ℕ) (z : ℂ) (τ : ℝ) :
    riemannZeta (z + (τ : ℂ) * I) - edPoly (fun _ => 1) (Finset.Icc 1 M) (z + (τ : ℂ) * I) =
      zetaDirichletTail M z.re (z.im + τ) := by
  rw [riemannZeta_sub_edPoly_one_Icc_eq_zetaDirichletTail]
  congr 1 <;> simp

/-- For the unsmoothed Dirichlet head `edPoly (fun _ => 1) (Finset.Icc 1 M)`, the Bagchi centered
tail is the difference between the shifted Carlson tail at `z.im + τ` and the fixed base-point
Carlson tail at `z.im`. -/
theorem centeredZetaTail_one_Icc_eq_sub (M : ℕ) (z : ℂ) (τ : ℝ) :
    centeredZetaTail (fun _ => 1) (Finset.Icc 1 M) z τ =
      zetaDirichletTail M z.re (z.im + τ) - zetaDirichletTail M z.re z.im := by
  unfold centeredZetaTail
  rw [riemannZeta_shift_sub_edPoly_one_Icc_eq_zetaDirichletTail,
    riemannZeta_sub_edPoly_one_Icc_eq_zetaDirichletTail]

/-- Two-shift cocycle identity: taking the difference of `centeredZetaTail` at two shifts `τ₁, τ₂`
cancels the fixed base-point tail at `z` and re-anchors the centered tail at `z + i τ₁`. -/
theorem centeredZetaTail_sub_centeredZetaTail_eq
    (a : ℕ → ℂ) (s : Finset ℕ) (z : ℂ) (τ₁ τ₂ : ℝ) :
    centeredZetaTail a s z τ₂ - centeredZetaTail a s z τ₁ =
      centeredZetaTail a s (z + (τ₁ : ℂ) * I) (τ₂ - τ₁) := by
  unfold centeredZetaTail
  have hshift : z + (τ₁ : ℂ) * I + ((τ₂ - τ₁ : ℝ) : ℂ) * I = z + (τ₂ : ℂ) * I := by
    push_cast
    ring
  rw [hshift]
  ring

/-- Re-anchoring at a shift `τ₁` where the Carlson tail is `< ε₁` bounds the centered tail at
`τ₂ - τ₁` by `ε₁ + ε₂` whenever the Carlson tail at `τ₂` is `< ε₂`, with no base-point pole. -/
theorem norm_centeredZetaTail_shift_lt_of_zetaDirichletTail
    (M : ℕ) (z : ℂ) {τ₁ τ₂ ε₁ ε₂ : ℝ}
    (h₁ : ‖zetaDirichletTail M z.re (z.im + τ₁)‖ < ε₁)
    (h₂ : ‖zetaDirichletTail M z.re (z.im + τ₂)‖ < ε₂) :
    ‖centeredZetaTail (fun _ => 1) (Finset.Icc 1 M) (z + (τ₁ : ℂ) * I) (τ₂ - τ₁)‖ <
      ε₂ + ε₁ := by
  rw [← centeredZetaTail_sub_centeredZetaTail_eq, centeredZetaTail_one_Icc_eq_sub,
    centeredZetaTail_one_Icc_eq_sub, sub_sub_sub_cancel_right]
  exact (norm_sub_le _ _).trans_lt (add_lt_add h₂ h₁)

/-- Exact Abel fractional-part representation of the Carlson tail at `z`. -/
theorem zetaDirichletTail_eq_pole_sub_fractIntegral {M : ℕ} (hM : 1 ≤ M)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) :
    zetaDirichletTail M z.re z.im =
      ((M : ℝ) : ℂ) ^ (1 - z) / (z - 1) -
        z * ∫ t in Ioi (M : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1)) := by
  rw [← riemannZeta_sub_edPoly_one_Icc_eq_zetaDirichletTail,
    Sieve.riemannZeta_eq_sum_add_tail hz0 hz1 hM]
  unfold edPoly
  simp only [one_mul]
  ring

/-- Exact three-term decomposition of `centeredZetaTail` into the shifted Carlson tail, the
deterministic base-point Abel pole `M^(1 - z) / (1 - z)`, and the base-point fractional-part
integral. -/
theorem centeredZetaTail_eq_shiftedTail_add_pole_add_fract {M : ℕ} (hM : 1 ≤ M)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) (τ : ℝ) :
    centeredZetaTail (fun _ => 1) (Finset.Icc 1 M) z τ =
      zetaDirichletTail M z.re (z.im + τ) + ((M : ℝ) : ℂ) ^ (1 - z) / (1 - z) +
        z * ∫ t in Ioi (M : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1)) := by
  rw [centeredZetaTail_one_Icc_eq_sub, zetaDirichletTail_eq_pole_sub_fractIntegral hM hz0 hz1]
  have hpole : -(((M : ℝ) : ℂ) ^ (1 - z) / (z - 1)) = ((M : ℝ) : ℂ) ^ (1 - z) / (1 - z) := by
    rw [← div_neg, neg_sub]
  linear_combination hpole

/-! ## 2. The Abel-centered zeta tail and base-point pole divergence -/

/-- The centered zeta tail with the deterministic base-point Abel pole `(M : ℂ)^(1 - z) / (1 - z)`
removed. -/
def abelCenteredZetaTail (M : ℕ) (z : ℂ) (τ : ℝ) : ℂ :=
  centeredZetaTail (fun _ => 1) (Finset.Icc 1 M) z τ - ((M : ℝ) : ℂ) ^ (1 - z) / (1 - z)

/-- Shifts `τ` where the Abel-centered zeta tail is `< ε` uniformly on `K`. -/
def abelCenteredZetaTailReturnSet (M : ℕ) (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {τ | ∀ z ∈ K, ‖abelCenteredZetaTail M z τ‖ < ε}

theorem abelCenteredZetaTail_eq_shiftedTail_add_fract {M : ℕ} (hM : 1 ≤ M)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) (τ : ℝ) :
    abelCenteredZetaTail M z τ =
      zetaDirichletTail M z.re (z.im + τ) +
        z * ∫ t in Ioi (M : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1)) := by
  unfold abelCenteredZetaTail
  rw [centeredZetaTail_eq_shiftedTail_add_pole_add_fract hM hz0 hz1 τ]
  ring

theorem zeta_self_difference_eq_head_add_pole_add_abelCenteredTail
    (M : ℕ) (z : ℂ) (τ : ℝ) :
    riemannZeta (z + (τ : ℂ) * I) - riemannZeta z =
      (edPoly (fun _ => 1) (Finset.Icc 1 M) (z + (τ : ℂ) * I) -
        edPoly (fun _ => 1) (Finset.Icc 1 M) z) +
        ((M : ℝ) : ℂ) ^ (1 - z) / (1 - z) +
          abelCenteredZetaTail M z τ := by
  rw [zeta_self_difference_eq_head_add_centeredTail (fun _ => 1) (Finset.Icc 1 M) z τ]
  unfold abelCenteredZetaTail
  ring

theorem norm_zeta_shift_sub_pole_lt_of_mem_edPolyReturnSet_and_abelCenteredTail
    {M : ℕ} {K : Set ℂ} {z : ℂ} (hz : z ∈ K) {ε η τ : ℝ}
    (hhead : τ ∈ edPolyReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε)
    (habel : ‖abelCenteredZetaTail M z τ‖ < η) :
    ‖(riemannZeta (z + (τ : ℂ) * I) - riemannZeta z) -
        ((M : ℝ) : ℂ) ^ (1 - z) / (1 - z)‖ < ε + η := by
  have hid : (riemannZeta (z + (τ : ℂ) * I) - riemannZeta z) -
      ((M : ℝ) : ℂ) ^ (1 - z) / (1 - z) =
    (edPoly (fun _ => 1) (Finset.Icc 1 M) (z + (τ : ℂ) * I) -
      edPoly (fun _ => 1) (Finset.Icc 1 M) z) + abelCenteredZetaTail M z τ := by
    rw [zeta_self_difference_eq_head_add_pole_add_abelCenteredTail M z τ]
    ring
  rw [hid]
  exact (norm_add_le _ _).trans_lt (add_lt_add (hhead z hz) habel)

/-- Conditioned density transfer for the Abel-centered tail: losing at most half of the
finite-head return density to `abelCenteredZetaTailReturnSet M K ε` yields a positive-density
set of shifts `τ` on which `ζ(z + iτ) - ζ(z)` lies within `2 * ε` of the base-point Abel pole
`(M : ℂ)^(1 - z) / (1 - z)` uniformly on `K`. -/
theorem exists_density_with_abelCenteredTail_transfer (M : ℕ) {K : Set ℂ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ᶠ T : ℝ in atTop,
        ENNReal.ofReal (κ * T) ≤
          volume (edPolyReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε ∩ Icc 0 T)) ∧
      ((∀ᶠ T : ℝ in atTop,
        volume ((edPolyReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε \
          abelCenteredZetaTailReturnSet M K ε) ∩ Icc 0 T) ≤
            ENNReal.ofReal (κ / 2 * T)) →
        ∀ᶠ T : ℝ in atTop,
          ENNReal.ofReal (κ / 2 * T) ≤
            volume ({τ : ℝ | ∀ z ∈ K,
              ‖(riemannZeta (z + (τ : ℂ) * I) - riemannZeta z) -
                ((M : ℝ) : ℂ) ^ (1 - z) / (1 - z)‖ < 2 * ε} ∩ Icc 0 T)) := by
  have hs : ∀ n ∈ Finset.Icc 1 M, 1 ≤ n := fun _ hn => (Finset.mem_Icc.mp hn).1
  obtain ⟨κ, hκ, hhead⟩ := exists_pos_density_edPolyReturnSet (fun _ => 1) hs hK hε
  refine ⟨κ, hκ, hhead, fun htail => ?_⟩
  filter_upwards [hhead, htail, eventually_ge_atTop (0 : ℝ)] with T hH hL hT
  let P := {τ : ℝ | ∀ z ∈ K,
    ‖(riemannZeta (z + (τ : ℂ) * I) - riemannZeta z) - ((M : ℝ) : ℂ) ^ (1 - z) / (1 - z)‖ < 2 * ε}
  have hsplit : volume (edPolyReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε ∩ Icc 0 T) ≤
      volume (P ∩ Icc 0 T) +
        volume ((edPolyReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε \
          abelCenteredZetaTailReturnSet M K ε) ∩ Icc 0 T) := by
    apply (measure_mono ?_).trans (measure_union_le _ _)
    rintro τ ⟨hh, hτT⟩
    by_cases hab : τ ∈ abelCenteredZetaTailReturnSet M K ε
    · refine Or.inl ⟨fun z hz => ?_, hτT⟩
      rw [show 2 * ε = ε + ε by ring]
      exact norm_zeta_shift_sub_pole_lt_of_mem_edPolyReturnSet_and_abelCenteredTail hz hh (hab z hz)
    · exact Or.inr ⟨⟨hh, hab⟩, hτT⟩
  have hsum := hH.trans (hsplit.trans (add_le_add le_rfl hL))
  have hnonneg : 0 ≤ κ / 2 * T := by positivity
  have hdouble : ENNReal.ofReal (κ * T) =
      ENNReal.ofReal (κ / 2 * T) + ENNReal.ofReal (κ / 2 * T) := by
    rw [← ENNReal.ofReal_add hnonneg hnonneg]
    congr 1
    ring
  rw [hdouble] at hsum
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hsum

/-- Uniform-in-`τ` bound between the Abel-centered tail and the shifted Carlson tail. -/
theorem norm_abelCenteredZetaTail_sub_shiftedTail_le {M : ℕ} (hM : 1 ≤ M)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) (τ : ℝ) :
    ‖abelCenteredZetaTail M z τ - zetaDirichletTail M z.re (z.im + τ)‖ ≤
      ‖z‖ * ((M : ℝ) ^ (-z.re) / z.re) := by
  rw [abelCenteredZetaTail_eq_shiftedTail_add_fract hM hz0 hz1 τ, add_sub_cancel_left, norm_mul]
  exact mul_le_mul_of_nonneg_left (Sieve.norm_integral_Ioi_fract_cpow_le hz0 hM) (norm_nonneg z)

theorem norm_zetaDirichletTail_add_pole_le {M : ℕ} (hM : 1 ≤ M)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) :
    ‖zetaDirichletTail M z.re z.im + ((M : ℝ) : ℂ) ^ (1 - z) / (1 - z)‖ ≤
      ‖z‖ * ((M : ℝ) ^ (-z.re) / z.re) := by
  have heq : zetaDirichletTail M z.re z.im + ((M : ℝ) : ℂ) ^ (1 - z) / (1 - z) =
      -(z * ∫ t in Ioi (M : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1))) := by
    rw [zetaDirichletTail_eq_pole_sub_fractIntegral hM hz0 hz1]
    have hpole : ((M : ℝ) : ℂ) ^ (1 - z) / (z - 1) = -(((M : ℝ) : ℂ) ^ (1 - z) / (1 - z)) := by
      rw [← div_neg, neg_sub]
    linear_combination hpole
  rw [heq, norm_neg, norm_mul]
  exact mul_le_mul_of_nonneg_left (Sieve.norm_integral_Ioi_fract_cpow_le hz0 hM) (norm_nonneg z)

/-- Explicit non-asymptotic lower bound on the fixed base-point tail `zetaDirichletTail M z.re z.im`
from the Abel pole `M^(1 - z) / (1 - z)`. -/
theorem norm_zetaDirichletTail_base_ge {M : ℕ} (hM : 1 ≤ M)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) :
    (M : ℝ) ^ (1 - z.re) / ‖1 - z‖ - ‖z‖ * ((M : ℝ) ^ (-z.re) / z.re) ≤
      ‖zetaDirichletTail M z.re z.im‖ := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hpole : ‖((M : ℝ) : ℂ) ^ (1 - z) / (1 - z)‖ = (M : ℝ) ^ (1 - z.re) / ‖1 - z‖ := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hM0]
    simp
  have htri : ‖((M : ℝ) : ℂ) ^ (1 - z) / (1 - z)‖ ≤
      ‖zetaDirichletTail M z.re z.im + ((M : ℝ) : ℂ) ^ (1 - z) / (1 - z)‖ +
        ‖zetaDirichletTail M z.re z.im‖ := by
    calc ‖((M : ℝ) : ℂ) ^ (1 - z) / (1 - z)‖
        = ‖(zetaDirichletTail M z.re z.im + ((M : ℝ) : ℂ) ^ (1 - z) / (1 - z)) -
            zetaDirichletTail M z.re z.im‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  have hbd := norm_zetaDirichletTail_add_pole_le hM hz0 hz1
  linarith

/-- Inside the critical strip `0 < Re z < 1`, the fixed base-point tail norm
`‖zetaDirichletTail M z.re z.im‖` diverges to `+∞` as `M → ∞`. -/
theorem tendsto_norm_zetaDirichletTail_base_atTop {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    Tendsto (fun M : ℕ => ‖zetaDirichletTail M z.re z.im‖) atTop atTop := by
  have hzne1 : z ≠ 1 := fun h => by rw [h] at hz1; simp at hz1
  have h1z : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne1.symm)
  have hgrow : Tendsto (fun M : ℕ => (M : ℝ) ^ (1 - z.re) / ‖1 - z‖) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith : 0 < 1 - z.re)).comp
      tendsto_natCast_atTop_atTop).atTop_div_const h1z
  have hdecay : Tendsto (fun M : ℕ => ‖z‖ * ((M : ℝ) ^ (-z.re) / z.re)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun M : ℕ => (M : ℝ) ^ (-z.re)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hz0).comp tendsto_natCast_atTop_atTop
    simpa using (h0.div_const z.re).const_mul ‖z‖
  have hdiff : Tendsto (fun M : ℕ =>
      (M : ℝ) ^ (1 - z.re) / ‖1 - z‖ - ‖z‖ * ((M : ℝ) ^ (-z.re) / z.re)) atTop atTop :=
    Tendsto.atTop_add hgrow (hdecay.neg)
  refine tendsto_atTop_mono' atTop ?_ hdiff
  filter_upwards [eventually_ge_atTop 1] with M hM
  exact norm_zetaDirichletTail_base_ge hM hz0 hzne1

/-! ## 3. Translation-invariant Carlson mean square and Chebyshev measure bounds -/

/-- Carlson's vertical mean-square formula is invariant under arbitrary base-height shifts `t₀`. -/
theorem carlson_zeta_tail_shifted_meanSquare (M : ℕ) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (t₀ : ℝ) :
    Tendsto (fun T => (∫ τ in (0 : ℝ)..T, ‖zetaDirichletTail M σ (t₀ + τ)‖ ^ 2) / T)
      atTop (𝓝 (zetaCoefficientTailMass M σ)) := by
  let g : ℝ → ℝ := fun t => ‖zetaDirichletTail M σ t‖ ^ 2
  have hg : Continuous g := (continuous_zetaDirichletTail M (ne_of_lt hσ1)).norm.pow 2
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hg.intervalIntegrable a b
  have hshift_top : Tendsto (fun T : ℝ => t₀ + T) atTop atTop :=
    tendsto_atTop_add_const_left _ t₀ tendsto_id
  have hmain := (carlson_zeta_tail_meanSquare M hσ hσ1).comp hshift_top
  have hratio : Tendsto (fun T : ℝ => 1 + t₀ / T) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  have hconst : Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..t₀, g t) / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hcomb := (hmain.mul hratio).sub hconst
  simp only [add_zero, mul_one, sub_zero, Function.comp_apply] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop (max (-t₀) 0)] with T hT
  have hT0 : 0 < T := (le_max_right _ _).trans_lt hT
  have htT : 0 < t₀ + T := by linarith [(le_max_left _ _).trans_lt hT]
  have hcomp : (∫ τ in (0 : ℝ)..T, g (t₀ + τ)) = ∫ t in t₀..(t₀ + T), g t := by
    simp [intervalIntegral.integral_comp_add_left]
  have hsub : (∫ t in t₀..(t₀ + T), g t) =
      (∫ t in (0 : ℝ)..(t₀ + T), g t) - ∫ t in (0 : ℝ)..t₀, g t := by
    rw [← intervalIntegral.integral_interval_sub_left (hgi 0 (t₀ + T)) (hgi 0 t₀)]
  change ((∫ t in (0 : ℝ)..(t₀ + T), g t) / (t₀ + T)) * (1 + t₀ / T) -
      (∫ t in (0 : ℝ)..t₀, g t) / T =
    (∫ τ in (0 : ℝ)..T, g (t₀ + τ)) / T
  rw [hcomp, hsub]
  have h1 : t₀ + T ≠ 0 := htT.ne'
  have h2 : T ≠ 0 := hT0.ne'
  field_simp
  ring

/-- Chebyshev/Markov inequality on `[0, T]` for the `L²` norm of a continuous complex function. -/
theorem volume_ge_norm_le_of_continuous {f : ℝ → ℂ} (hf : Continuous f)
    {η T : ℝ} (hη : 0 < η) (hT : 0 ≤ T) :
    volume ({τ : ℝ | η ≤ ‖f τ‖} ∩ Icc 0 T) ≤
      ENNReal.ofReal ((∫ τ in (0 : ℝ)..T, ‖f τ‖ ^ 2) / η ^ 2) := by
  let E := {τ : ℝ | η ≤ ‖f τ‖} ∩ Icc 0 T
  have hEm : MeasurableSet E :=
    (isClosed_le continuous_const hf.norm).measurableSet.inter measurableSet_Icc
  have hind : IntegrableOn (E.indicator (fun _ : ℝ => η ^ 2)) (Icc 0 T) volume :=
    (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)).indicator hEm
  have hf2 : IntegrableOn (fun τ => ‖f τ‖ ^ 2) (Icc 0 T) volume :=
    (hf.norm.pow 2).continuousOn.integrableOn_Icc
  have hle : ∫ τ in Icc 0 T, E.indicator (fun _ : ℝ => η ^ 2) τ ≤
      ∫ τ in Icc 0 T, ‖f τ‖ ^ 2 := by
    refine setIntegral_mono_on hind hf2 measurableSet_Icc fun τ hτ => ?_
    by_cases hτE : τ ∈ E
    · rw [indicator_of_mem hτE]
      exact pow_le_pow_left₀ hη.le hτE.1 2
    · rw [indicator_of_notMem hτE]
      positivity
  rw [setIntegral_indicator hEm, inter_eq_self_of_subset_right inter_subset_right,
    setIntegral_const, smul_eq_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hT] at hle
  have hfin : volume E < ⊤ :=
    (measure_mono inter_subset_right).trans_lt isCompact_Icc.measure_lt_top
  rw [← ENNReal.ofReal_toReal hfin.ne]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (sq_pos_of_pos hη), ← MeasureTheory.measureReal_def]
  exact hle

theorem eventually_volume_zetaDirichletTail_ge_le (M : ℕ) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (t₀ : ℝ) {η c : ℝ} (hη : 0 < η)
    (hc : zetaCoefficientTailMass M σ / η ^ 2 < c) :
    ∀ᶠ T : ℝ in atTop,
      volume ({τ : ℝ | η ≤ ‖zetaDirichletTail M σ (t₀ + τ)‖} ∩ Icc 0 T) ≤
        ENNReal.ofReal (c * T) := by
  have hcont : Continuous (fun τ : ℝ => zetaDirichletTail M σ (t₀ + τ)) :=
    (continuous_zetaDirichletTail M (ne_of_lt hσ1)).comp (continuous_const.add continuous_id)
  have hlim : Tendsto (fun T => ((∫ τ in (0 : ℝ)..T,
      ‖zetaDirichletTail M σ (t₀ + τ)‖ ^ 2) / T) / η ^ 2)
      atTop (𝓝 (zetaCoefficientTailMass M σ / η ^ 2)) :=
    (carlson_zeta_tail_shifted_meanSquare M hσ hσ1 t₀).div_const (η ^ 2)
  filter_upwards [hlim.eventually_lt_const hc, eventually_ge_atTop (0 : ℝ)] with T hT hT0
  refine (volume_ge_norm_le_of_continuous hcont hη hT0).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : (∫ τ in (0 : ℝ)..T, ‖zetaDirichletTail M σ (t₀ + τ)‖ ^ 2) / η ^ 2 =
      (((∫ τ in (0 : ℝ)..T, ‖zetaDirichletTail M σ (t₀ + τ)‖ ^ 2) / T) / η ^ 2) * T := by
    rcases eq_or_lt_of_le hT0 with rfl | hTpos
    · simp
    · have : T ≠ 0 := hTpos.ne'
      field_simp
  rw [h1]
  exact mul_le_mul_of_nonneg_right hT.le hT0

theorem eventually_eventually_volume_zetaDirichletTail_ge_le {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (t₀ : ℝ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume ({τ : ℝ | η ≤ ‖zetaDirichletTail M σ (t₀ + τ)‖} ∩ Icc 0 T) ≤
        ENNReal.ofReal (δ * T) := by
  have hlim : Tendsto (fun M => zetaCoefficientTailMass M σ / η ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_zetaCoefficientTailMass hσ).div_const (η ^ 2)
  filter_upwards [hlim.eventually_lt_const hδ] with M hM
  exact eventually_volume_zetaDirichletTail_ge_le M hσ hσ1 t₀ hη hM

/-! ## 4. Full-measure return and L² approximation of the Abel-centered tail -/

/-- Once the base-point Abel pole is removed, the set of shifts `τ ∈ [0, T]` where
`‖abelCenteredZetaTail M z τ‖ ≥ ε` has arbitrarily small asymptotic density for large `M`. -/
theorem eventually_eventually_volume_abelCenteredZetaTail_ge_le {z : ℂ}
    (hσ : 1 / 2 < z.re) (hσ1 : z.re < 1) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume ({τ : ℝ | ε ≤ ‖abelCenteredZetaTail M z τ‖} ∩ Icc 0 T) ≤
        ENNReal.ofReal (δ * T) := by
  have hzne1 : z ≠ 1 := fun h => by rw [h] at hσ1; simp at hσ1
  have hz0 : 0 < z.re := by linarith
  have hdecay : Tendsto (fun M : ℕ => ‖z‖ * ((M : ℝ) ^ (-z.re) / z.re)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun M : ℕ => (M : ℝ) ^ (-z.re)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hz0).comp tendsto_natCast_atTop_atTop
    simpa using (h0.div_const z.re).const_mul ‖z‖
  filter_upwards [eventually_ge_atTop 1,
    hdecay.eventually_lt_const (half_pos hε),
    eventually_eventually_volume_zetaDirichletTail_ge_le hσ hσ1 z.im (half_pos hε) hδ]
    with M hM hrem htail
  refine htail.mono fun T hT => (measure_mono ?_).trans hT
  rintro τ ⟨hτ, hτT⟩
  refine ⟨?_, hτT⟩
  have hbd := norm_abelCenteredZetaTail_sub_shiftedTail_le hM hz0 hzne1 τ
  have htri := norm_add_le (abelCenteredZetaTail M z τ - zetaDirichletTail M z.re (z.im + τ))
    (zetaDirichletTail M z.re (z.im + τ))
  rw [sub_add_cancel] at htri
  dsimp at hτ ⊢
  linarith

/-- The Abel-centered tail `abelCenteredZetaTail M z` can be made arbitrarily small in limiting
vertical square mean on `1/2 < Re z < 1`. -/
theorem abelCenteredZetaTail_L2_approximation {z : ℂ} (hσ : 1 / 2 < z.re) (hσ1 : z.re < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      (∫ τ in (0 : ℝ)..T, ‖abelCenteredZetaTail M z τ‖ ^ 2) / T < ε := by
  have hzne1 : z ≠ 1 := fun h => by rw [h] at hσ1; simp at hσ1
  have hz0 : 0 < z.re := by linarith
  have hdecay : Tendsto (fun M : ℕ => 2 * (‖z‖ * ((M : ℝ) ^ (-z.re) / z.re)) ^ 2)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun M : ℕ => (M : ℝ) ^ (-z.re)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hz0).comp tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun M : ℕ => ‖z‖ * ((M : ℝ) ^ (-z.re) / z.re)) atTop (𝓝 0) := by
      simpa using (h0.div_const z.re).const_mul ‖z‖
    simpa using (h1.pow 2).const_mul 2
  have htail : Tendsto (fun M : ℕ => 2 * zetaCoefficientTailMass M z.re) atTop (𝓝 0) := by
    simpa using (tendsto_zetaCoefficientTailMass hσ).const_mul 2
  filter_upwards [eventually_ge_atTop 1,
    hdecay.eventually_lt_const (half_pos hε),
    htail.eventually_lt_const (half_pos hε)] with M hM hrem hmass
  have hlim : Tendsto (fun T => 2 * ((∫ τ in (0 : ℝ)..T,
      ‖zetaDirichletTail M z.re (z.im + τ)‖ ^ 2) / T))
      atTop (𝓝 (2 * zetaCoefficientTailMass M z.re)) :=
    (carlson_zeta_tail_shifted_meanSquare M hσ hσ1 z.im).const_mul 2
  filter_upwards [hlim.eventually_lt_const hmass, eventually_gt_atTop (0 : ℝ)] with T hT hT0
  have hcont_abel : Continuous (fun τ : ℝ => abelCenteredZetaTail M z τ) := by
    unfold abelCenteredZetaTail centeredZetaTail
    have h1 : Continuous (fun τ : ℝ => riemannZeta (z + (τ : ℂ) * I) -
        edPoly (fun _ => 1) (Finset.Icc 1 M) (z + (τ : ℂ) * I)) := by
      simp_rw [riemannZeta_shift_sub_edPoly_one_Icc_eq_zetaDirichletTail]
      exact (continuous_zetaDirichletTail M (ne_of_lt hσ1)).comp
        (continuous_const.add continuous_id)
    exact (h1.sub continuous_const).sub continuous_const
  have hcont_tail : Continuous (fun τ : ℝ => zetaDirichletTail M z.re (z.im + τ)) :=
    (continuous_zetaDirichletTail M (ne_of_lt hσ1)).comp (continuous_const.add continuous_id)
  have ha₂ : Continuous (fun τ : ℝ => ‖abelCenteredZetaTail M z τ‖ ^ 2) :=
    hcont_abel.norm.pow 2
  have hf₂ : Continuous (fun τ : ℝ => ‖zetaDirichletTail M z.re (z.im + τ)‖ ^ 2) :=
    hcont_tail.norm.pow 2
  let R : ℝ := ‖z‖ * ((M : ℝ) ^ (-z.re) / z.re)
  have hpt : ∀ τ : ℝ, ‖abelCenteredZetaTail M z τ‖ ^ 2 ≤
      2 * ‖zetaDirichletTail M z.re (z.im + τ)‖ ^ 2 + 2 * R ^ 2 := by
    intro τ
    have hbd : ‖abelCenteredZetaTail M z τ - zetaDirichletTail M z.re (z.im + τ)‖ ≤ R :=
      norm_abelCenteredZetaTail_sub_shiftedTail_le hM hz0 hzne1 τ
    have htri := norm_add_le (abelCenteredZetaTail M z τ - zetaDirichletTail M z.re (z.im + τ))
      (zetaDirichletTail M z.re (z.im + τ))
    rw [sub_add_cancel] at htri
    have hle : ‖abelCenteredZetaTail M z τ‖ ≤ ‖zetaDirichletTail M z.re (z.im + τ)‖ + R := by
      linarith
    have hR0 : 0 ≤ R := by positivity
    nlinarith [sq_nonneg (‖zetaDirichletTail M z.re (z.im + τ)‖ - R),
      norm_nonneg (abelCenteredZetaTail M z τ),
      norm_nonneg (zetaDirichletTail M z.re (z.im + τ))]
  have hint := intervalIntegral.integral_mono_on (μ := volume) hT0.le
    (ha₂.intervalIntegrable 0 T)
    (((continuous_const.mul hf₂).add continuous_const).intervalIntegrable 0 T)
    (fun τ _ => hpt τ)
  change (∫ τ in (0 : ℝ)..T, ‖abelCenteredZetaTail M z τ‖ ^ 2) ≤
    ∫ τ in (0 : ℝ)..T, 2 * ‖zetaDirichletTail M z.re (z.im + τ)‖ ^ 2 + 2 * R ^ 2 at hint
  have hgi : IntervalIntegrable (fun τ => 2 * ‖zetaDirichletTail M z.re (z.im + τ)‖ ^ 2)
      volume 0 T := (continuous_const.mul hf₂).intervalIntegrable 0 T
  rw [intervalIntegral.integral_add hgi (continuous_const.intervalIntegrable 0 T),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at hint
  have hdiv := div_le_div_of_nonneg_right hint hT0.le
  have hsplit : ((2 * ∫ x in (0 : ℝ)..T, ‖zetaDirichletTail M z.re (z.im + x)‖ ^ 2) +
      T * (2 * R ^ 2)) / T =
      2 * ((∫ x in (0 : ℝ)..T, ‖zetaDirichletTail M z.re (z.im + x)‖ ^ 2) / T) +
        2 * R ^ 2 := by
    have : T ≠ 0 := hT0.ne'
    field_simp
  dsimp [R] at hsplit hdiv
  linarith [hdiv, hsplit]

/-! ## 5. Unsmoothed centered-tail obstruction: density-zero collapse and L² divergence -/

/-- Every shift in `centeredZetaTailReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε` forces the
shifted Carlson tail at `z ∈ K` to have norm at least `‖zetaDirichletTail M z.re z.im‖ - ε`. -/
theorem centeredZetaTailReturnSet_subset_zetaDirichletTail_ge
    (M : ℕ) {K : Set ℂ} {z : ℂ} (hz : z ∈ K) (ε : ℝ) :
    centeredZetaTailReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε ⊆
      {τ : ℝ | ‖zetaDirichletTail M z.re z.im‖ - ε ≤ ‖zetaDirichletTail M z.re (z.im + τ)‖} := by
  intro τ hτ
  have h := hτ z hz
  rw [centeredZetaTail_one_Icc_eq_sub] at h
  have htri := norm_sub_norm_le (zetaDirichletTail M z.re z.im)
    (zetaDirichletTail M z.re (z.im + τ))
  rw [norm_sub_rev] at htri
  change ‖zetaDirichletTail M z.re z.im‖ - ε ≤ ‖zetaDirichletTail M z.re (z.im + τ)‖
  linarith [htri]

/-- Quantitative fixed-`M` upper density bound for `centeredZetaTailReturnSet` in terms of
`zetaCoefficientTailMass M z.re` and the base-point tail norm `‖zetaDirichletTail M z.re z.im‖`. -/
theorem eventually_volume_centeredZetaTailReturnSet_le_tailMass
    (M : ℕ) {K : Set ℂ} {z : ℂ} (hz : z ∈ K) (hσ : 1 / 2 < z.re) (hσ1 : z.re < 1)
    {ε c : ℝ} (hε : ε < ‖zetaDirichletTail M z.re z.im‖)
    (hc : zetaCoefficientTailMass M z.re /
      (‖zetaDirichletTail M z.re z.im‖ - ε) ^ 2 < c) :
    ∀ᶠ T : ℝ in atTop,
      volume (centeredZetaTailReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε ∩ Icc 0 T) ≤
        ENNReal.ofReal (c * T) := by
  have hη : 0 < ‖zetaDirichletTail M z.re z.im‖ - ε := sub_pos.mpr hε
  refine (eventually_volume_zetaDirichletTail_ge_le M hσ hσ1 z.im hη hc).mono fun T hT => ?_
  refine (measure_mono ?_).trans hT
  exact inter_subset_inter_left _ (centeredZetaTailReturnSet_subset_zetaDirichletTail_ge M hz ε)

/-- For any set `K` containing a point `z` in `1/2 < Re z < 1`, the unsmoothed centered-tail
return set `centeredZetaTailReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε` has asymptotic density
arbitrarily close to zero for all sufficiently large `M`. -/
theorem eventually_eventually_volume_centeredZetaTailReturnSet_le
    {K : Set ℂ} {z : ℂ} (hz : z ∈ K) (hσ : 1 / 2 < z.re) (hσ1 : z.re < 1)
    (ε : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume (centeredZetaTailReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε ∩ Icc 0 T) ≤
        ENNReal.ofReal (δ * T) := by
  have hbase := (tendsto_norm_zetaDirichletTail_base_atTop (by linarith : 0 < z.re) hσ1).eventually
    (eventually_ge_atTop (ε + 1))
  filter_upwards [hbase,
    eventually_eventually_volume_zetaDirichletTail_ge_le hσ hσ1 z.im zero_lt_one hδ]
    with M hM htail
  refine htail.mono fun T hT => (measure_mono ?_).trans hT
  rintro τ ⟨hτ, hτT⟩
  have hge := centeredZetaTailReturnSet_subset_zetaDirichletTail_ge M hz ε hτ
  exact ⟨by dsimp at hge ⊢; linarith, hτT⟩

/-- Consequently, the joint return set `edPolyReturnSet ∩ centeredZetaTailReturnSet` of
`BagchiConditionedTailGap.headReturn_inter_centeredTailReturn_subset_zetaReturn` for the
unsmoothed Dirichlet head `edPoly (fun _ => 1) (Finset.Icc 1 M)` has asymptotic density
tending to zero as `M → ∞`. -/
theorem eventually_eventually_volume_headReturn_inter_centeredTailReturn_le
    {K : Set ℂ} {z : ℂ} (hz : z ∈ K) (hσ : 1 / 2 < z.re) (hσ1 : z.re < 1)
    (ε η : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume ((edPolyReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε ∩
        centeredZetaTailReturnSet (fun _ => 1) (Finset.Icc 1 M) K η) ∩ Icc 0 T) ≤
          ENNReal.ofReal (δ * T) := by
  refine (eventually_eventually_volume_centeredZetaTailReturnSet_le hz hσ hσ1 η hδ).mono
    fun M hM => hM.mono fun T hT => (measure_mono ?_).trans hT
  exact inter_subset_inter_left _ inter_subset_right

/-- In contrast to `carlson_zeta_L2_approximation` and `abelCenteredZetaTail_L2_approximation`,
the vertical `L²` mean square of the unadjusted `centeredZetaTail (fun _ => 1) (Finset.Icc 1 M) z`
diverges to `+∞` as `M → ∞` at every point `z` in `1/2 < Re z < 1`. -/
theorem centeredZetaTail_L2_divergence {z : ℂ} (hσ : 1 / 2 < z.re) (hσ1 : z.re < 1)
    (B : ℝ) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      B < (∫ τ in (0 : ℝ)..T,
        ‖centeredZetaTail (fun _ => 1) (Finset.Icc 1 M) z τ‖ ^ 2) / T := by
  have hbase : Tendsto (fun M : ℕ => ‖zetaDirichletTail M z.re z.im‖ ^ 2 / 2) atTop atTop :=
    ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
      (tendsto_norm_zetaDirichletTail_base_atTop (by linarith) hσ1)).atTop_div_const two_pos
  have htail : Tendsto (fun M : ℕ => zetaCoefficientTailMass M z.re) atTop (𝓝 0) :=
    tendsto_zetaCoefficientTailMass hσ
  filter_upwards [hbase.eventually_gt_atTop (B + 1),
    htail.eventually_lt_const zero_lt_one] with M hM hmass
  have hlim := carlson_zeta_tail_shifted_meanSquare M hσ hσ1 z.im
  filter_upwards [hlim.eventually_lt_const hmass, eventually_gt_atTop (0 : ℝ)] with T hT hT0
  have hcont_cent : Continuous (fun τ : ℝ =>
      centeredZetaTail (fun _ => 1) (Finset.Icc 1 M) z τ) := by
    simp_rw [centeredZetaTail_one_Icc_eq_sub]
    exact ((continuous_zetaDirichletTail M (ne_of_lt hσ1)).comp
      (continuous_const.add continuous_id)).sub continuous_const
  have hcont_tail : Continuous (fun τ : ℝ => zetaDirichletTail M z.re (z.im + τ)) :=
    (continuous_zetaDirichletTail M (ne_of_lt hσ1)).comp (continuous_const.add continuous_id)
  have hc₂ : Continuous (fun τ : ℝ =>
      ‖centeredZetaTail (fun _ => 1) (Finset.Icc 1 M) z τ‖ ^ 2) :=
    hcont_cent.norm.pow 2
  have hf₂ : Continuous (fun τ : ℝ => ‖zetaDirichletTail M z.re (z.im + τ)‖ ^ 2) :=
    hcont_tail.norm.pow 2
  let b : ℝ := ‖zetaDirichletTail M z.re z.im‖
  have hpt : ∀ τ : ℝ, b ^ 2 / 2 - ‖zetaDirichletTail M z.re (z.im + τ)‖ ^ 2 ≤
      ‖centeredZetaTail (fun _ => 1) (Finset.Icc 1 M) z τ‖ ^ 2 := by
    intro τ
    rw [centeredZetaTail_one_Icc_eq_sub]
    have htri := norm_sub_norm_le (zetaDirichletTail M z.re z.im)
      (zetaDirichletTail M z.re (z.im + τ))
    rw [norm_sub_rev] at htri
    let c := ‖zetaDirichletTail M z.re (z.im + τ) - zetaDirichletTail M z.re z.im‖
    let a := ‖zetaDirichletTail M z.re (z.im + τ)‖
    have hle : b ≤ c + a := by dsimp [a, b, c]; linarith [htri]
    have hb0 : 0 ≤ b := norm_nonneg _
    nlinarith [sq_nonneg (c - a)]
  have hint := intervalIntegral.integral_mono_on (μ := volume) hT0.le
    ((continuous_const.sub hf₂).intervalIntegrable 0 T)
    (hc₂.intervalIntegrable 0 T)
    (fun τ _ => hpt τ)
  change (∫ τ in (0 : ℝ)..T, b ^ 2 / 2 - ‖zetaDirichletTail M z.re (z.im + τ)‖ ^ 2) ≤
    ∫ τ in (0 : ℝ)..T, ‖centeredZetaTail (fun _ => 1) (Finset.Icc 1 M) z τ‖ ^ 2 at hint
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 T)
      (hf₂.intervalIntegrable 0 T),
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint
  have hdiv := div_le_div_of_nonneg_right hint hT0.le
  have hsplit : (T * (b ^ 2 / 2) -
      ∫ x in (0 : ℝ)..T, ‖zetaDirichletTail M z.re (z.im + x)‖ ^ 2) / T =
      b ^ 2 / 2 - (∫ x in (0 : ℝ)..T, ‖zetaDirichletTail M z.re (z.im + x)‖ ^ 2) / T := by
    have : T ≠ 0 := hT0.ne'
    field_simp
  dsimp [b] at hsplit hdiv
  linarith [hdiv, hsplit]

end RHTower
