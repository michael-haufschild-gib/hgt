import GaloisForLFunctions.RHTower.WoldEulerActivationSquare

/-!
# The pencil at shift one is not a Dirichlet series

The pencil `ξ(s+1) + ξ(s−1)` has the functional equation of `ξ`. It is the simplest of the
objects built from `ξ` that are candidates for certificates: a dominant half `ξ(s+1)`, which
has an Euler product, and its reflection. The quotient of the two halves is explicit,

`ξ(s−1)/ξ(s+1) = 2π (s−2)/(s(s+1)) · ζ(s−1)/ζ(s+1)`, `Re s > 2`:

a rational function times a Dirichlet series. On the real axis it decays like `2π/σ`, while a
Dirichlet series without constant term decays like `2^{−σ}`. So the pencil divided by its
dominant half is not a Dirichlet series. Its prime side is not carried by the logarithms of the
integers: the rational factor is the Laplace transform of a density that starts at `u = 0`.

* `xi_sub_one_div_xi_add_one`: the quotient of the two halves.
* `tendsto_mul_xi_sub_one_div_xi_add_one`: `σ ξ(σ−1)/ξ(σ+1) → 2π`.
* `not_exists_lSeries_pencil`: the pencil over its dominant half is the L-series of no
  sequence.
-/

open Complex Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open _root_.RHTower

/-- Right of `Re s = 1`, `ξ(s) = ½ s (s − 1) ζ(s) Γ_ℝ(s)`. -/
theorem xi_eq_zeta_mul_gammaR {s : ℂ} (hs : 1 < s.re) :
    xi s = s * (s - 1) / 2 * (riemannZeta s * Gammaℝ s) := by
  have h0 : s ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hs
    linarith only [hs]
  have h1 : s ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith only [hs])
  rw [xi_eq_half_mul h0 h1, riemannZeta_def_of_ne_zero h0, div_mul_cancel₀ _ hG]

theorem xi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : xi s ≠ 0 := by
  have h0 : s ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hs
    linarith only [hs]
  have h1 : s - 1 ≠ 0 := fun h => by
    rw [sub_eq_zero.mp h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  rw [xi_eq_zeta_mul_gammaR hs]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h0 h1) two_ne_zero)
    (mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re hs)
      (Gammaℝ_ne_zero_of_re_pos (by linarith only [hs])))

/-- **The quotient of the two halves of the pencil.** -/
theorem xi_sub_one_div_xi_add_one {s : ℂ} (hs : 2 < s.re) :
    xi (s - 1) / xi (s + 1) =
      2 * π * (s - 2) / (s * (s + 1)) * (riemannZeta (s - 1) / riemannZeta (s + 1)) := by
  have hm : 1 < (s - 1).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith only [hs]
  have hp : 1 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith only [hs]
  have h0 : s ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hs
    linarith only [hs]
  have hs1 : s - 1 ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hm
    linarith only [hm]
  have hsp : s + 1 ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hp
    linarith only [hp]
  have hG : Gammaℝ (s - 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith only [hm])
  have hζ : riemannZeta (s + 1) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hp
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hGp : Gammaℝ (s + 1) = Gammaℝ (s - 1) * (s - 1) / 2 / π := by
    rw [show s + 1 = s - 1 + 2 by ring, Gammaℝ_add_two hs1]
  rw [xi_eq_zeta_mul_gammaR hm, xi_eq_zeta_mul_gammaR hp, hGp,
    show s + 1 - 1 = s by ring, show s - 1 - 1 = s - 2 by ring]
  field_simp

/-- **The quotient decays like `2π/σ` on the real axis.** -/
theorem tendsto_mul_xi_sub_one_div_xi_add_one :
    Tendsto (fun σ : ℝ => (σ : ℂ) * (xi ((σ : ℂ) - 1) / xi ((σ : ℂ) + 1))) atTop
      (𝓝 (2 * π)) := by
  -- the two zeta factors tend to one
  have hζm : Tendsto (fun σ : ℝ => riemannZeta ((σ : ℂ) - 1)) atTop (𝓝 1) :=
    tendsto_riemannZeta_of_re_atTop_filter (by
      have : (fun σ : ℝ => ((σ : ℂ) - 1).re) = fun σ => σ - 1 := by
        funext σ
        simp
      rw [this]
      exact tendsto_atTop_add_const_right atTop (-1) tendsto_id)
  have hζp : Tendsto (fun σ : ℝ => riemannZeta ((σ : ℂ) + 1)) atTop (𝓝 1) :=
    tendsto_riemannZeta_of_re_atTop_filter (by
      have : (fun σ : ℝ => ((σ : ℂ) + 1).re) = fun σ => σ + 1 := by
        funext σ
        simp
      rw [this]
      exact tendsto_atTop_add_const_right atTop 1 tendsto_id)
  -- the rational factor tends to one
  have hrat : Tendsto (fun σ : ℝ => ((σ : ℂ) - 2) / ((σ : ℂ) + 1)) atTop (𝓝 1) := by
    have hreal : Tendsto (fun σ : ℝ => 1 - 3 / (σ + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub
        (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_id))
    rw [sub_zero] at hreal
    have hc := (Complex.continuous_ofReal.tendsto 1).comp hreal
    rw [Complex.ofReal_one] at hc
    refine hc.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
    have hne : (σ : ℂ) + 1 ≠ 0 := by
      have : ((σ + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith only [hσ])
      simpa using this
    simp only [Function.comp_apply]
    push_cast
    field_simp
    ring
  have hquot : Tendsto (fun σ : ℝ => riemannZeta ((σ : ℂ) - 1) / riemannZeta ((σ : ℂ) + 1))
      atTop (𝓝 1) := by
    have h := hζm.div hζp one_ne_zero
    rw [div_one] at h
    exact h
  have hlim := (hrat.mul hquot).const_mul (2 * (π : ℂ))
  rw [mul_one, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with σ hσ
  have hs : 2 < ((σ : ℂ)).re := by simpa using hσ
  have h0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith only [hσ])
  have hp : (σ : ℂ) + 1 ≠ 0 := by
    have : ((σ + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith only [hσ])
    simpa using this
  rw [xi_sub_one_div_xi_add_one hs]
  field_simp

/-- The quotient tends to zero on the real axis. -/
theorem tendsto_xi_sub_one_div_xi_add_one :
    Tendsto (fun σ : ℝ => xi ((σ : ℂ) - 1) / xi ((σ : ℂ) + 1)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun σ : ℝ => ((σ⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    rwa [Complex.ofReal_zero] at h
  have h := hinv.mul tendsto_mul_xi_sub_one_div_xi_add_one
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
  have h0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]

/-- **The pencil over its dominant half is not a Dirichlet series.** There is no sequence `a`
whose L-series converges somewhere and equals `(ξ(σ+1) + ξ(σ−1))/ξ(σ+1)` for all large real
`σ`. -/
theorem not_exists_lSeries_pencil :
    ¬ ∃ (a : ℕ → ℂ) (σ₀ : ℝ), LSeriesSummable a σ₀ ∧ ∀ σ : ℝ, σ₀ ≤ σ →
      (xi ((σ : ℂ) + 1) + xi ((σ : ℂ) - 1)) / xi ((σ : ℂ) + 1) = LSeries a σ := by
  rintro ⟨a, σ₀, hsum, heq⟩
  have hfin : LSeries.abscissaOfAbsConv a < ⊤ :=
    hsum.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  -- the pencil over its dominant half is `1` plus the quotient
  have hsplit : ∀ᶠ σ : ℝ in atTop,
      LSeries a σ = 1 + xi ((σ : ℂ) - 1) / xi ((σ : ℂ) + 1) := by
    filter_upwards [eventually_ge_atTop σ₀, eventually_gt_atTop (0 : ℝ)] with σ hσ hσ0
    have hne : xi ((σ : ℂ) + 1) ≠ 0 := xi_ne_zero_of_one_lt_re (by
      rw [Complex.add_re, Complex.ofReal_re, Complex.one_re]
      linarith only [hσ0])
    rw [← heq σ hσ, add_div, div_self hne]
  -- the constant coefficient is one
  have ha1 : a 1 = 1 := by
    have h1 := LSeries.tendsto_atTop hfin
    have h2 : Tendsto (fun σ : ℝ => 1 + xi ((σ : ℂ) - 1) / xi ((σ : ℂ) + 1)) atTop
        (𝓝 (1 + 0)) := tendsto_const_nhds.add tendsto_xi_sub_one_div_xi_add_one
    rw [add_zero] at h2
    exact tendsto_nhds_unique h1 (h2.congr' (hsplit.mono fun σ h => h.symm))
  -- remove the constant coefficient
  have hδ : ∀ s : ℂ, LSeriesSummable LSeries.delta s := fun s =>
    (LSeriesSummable_congr' s (f := 0) (g := LSeries.delta) (by
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hn1 : n ≠ 1 := by omega
      simp [LSeries.delta, hn1])).mp (LSeriesSummable_zero)
  let f : ℕ → ℂ := fun n => if n = 0 then 0 else (a - LSeries.delta) n
  have hfg : ∀ {n : ℕ}, n ≠ 0 → f n = (a - LSeries.delta) n := fun {n} hn => if_neg hn
  have hf01 : ∀ m ≤ 1, f m = 0 := by
    intro m hm
    interval_cases m
    · exact if_pos rfl
    · rw [hfg one_ne_zero, Pi.sub_apply, ha1]
      simp [LSeries.delta]
  have hffin : LSeries.abscissaOfAbsConv f < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_congr hfg]
    exact (hsum.sub (hδ _)).abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  have hfval : ∀ᶠ σ : ℝ in atTop, LSeries f σ = xi ((σ : ℂ) - 1) / xi ((σ : ℂ) + 1) := by
    filter_upwards [hsplit, eventually_ge_atTop σ₀] with σ hσ hσ0
    have hsumσ : LSeriesSummable a σ :=
      hsum.of_re_le_re (by simpa using hσ0)
    rw [LSeries_congr hfg, LSeries_sub hsumσ (hδ _), LSeries_delta, hσ, Pi.one_apply]
    ring
  -- `2^σ` times the quotient converges, although `σ` times it tends to `2π`
  have hconv := LSeries.tendsto_cpow_mul_atTop hf01 hffin
  have hnorm := hconv.norm
  have hgrow : Tendsto (fun σ : ℝ =>
      ‖((1 : ℕ) + 1 : ℂ) ^ (σ : ℂ) * LSeries f σ‖) atTop atTop := by
    have hσR : Tendsto (fun σ : ℝ => ‖(σ : ℂ) * (xi ((σ : ℂ) - 1) / xi ((σ : ℂ) + 1))‖) atTop
        (𝓝 ‖(2 * π : ℂ)‖) := tendsto_mul_xi_sub_one_div_xi_add_one.norm
    have hpos : 0 < ‖(2 * π : ℂ)‖ := norm_pos_iff.mpr
      (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    -- `2^σ/σ → ∞`
    have hexp : Tendsto (fun σ : ℝ => Real.exp (Real.log 2 * σ) / σ) atTop atTop := by
      have h1 := (Real.tendsto_exp_div_pow_atTop 1).comp
        (tendsto_id.const_mul_atTop (Real.log_pos one_lt_two))
      have h2 := h1.const_mul_atTop (Real.log_pos one_lt_two)
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
      simp only [Function.comp_apply, pow_one, id]
      have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
      field_simp
    have hprod := hexp.atTop_mul_pos hpos hσR
    refine hprod.congr' ?_
    filter_upwards [hfval, eventually_gt_atTop (0 : ℝ)] with σ hσ hσ0
    have h2 : ‖((1 : ℕ) + 1 : ℂ) ^ (σ : ℂ)‖ = Real.exp (Real.log 2 * σ) := by
      have h3 : ((1 : ℕ) + 1 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
      rw [h3, Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.ofReal_re,
        Real.rpow_def_of_pos two_pos]
    rw [hσ, norm_mul, norm_mul, h2, Complex.norm_real, Real.norm_of_nonneg hσ0.le]
    field_simp
  exact not_tendsto_nhds_of_tendsto_atTop hgrow _ hnorm

end GaloisForLFunctions.FloorFreeArithmetic
