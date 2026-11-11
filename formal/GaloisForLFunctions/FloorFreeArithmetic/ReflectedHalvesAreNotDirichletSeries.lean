import GaloisForLFunctions.FloorFreeArithmetic.ThePencilAtShiftOneIsNotADirichletSeries
import GaloisForLFunctions.InfiniteRankPurityTheory.TheEisensteinConstantTermIsPureByParity

/-!
# Reflected halves are not Dirichlet series

The objects of the corpus with all non-real zeros on the critical line and the Gamma factor of
`ζ` are sums of a dominant half, which has an Euler product, and its reflection:

* the pencil `ξ(s+h) + ξ(s−h)` at a shift `h > 0`;
* the cleared constant term of the Eisenstein series at height `Y`,
  `(s−1) ξ(2s) Y^s + s ξ(2s−1) Y^{1−s}`.

A certificate in the sense of feasibility needs a prime side carried by the logarithms of the
integers, that is, the object divided by its dominant half must be a Dirichlet series. It is
not, for a reason that does not depend on the object.

**The first coefficient test** (`not_lSeries_of_slow_amplitude`). A Dirichlet series has an
exponential scale at its first nonzero coefficient: `n^σ L(σ) → a_n ≠ 0`. So a function `c + R`
on the real axis with `‖R(σ)‖ = B^{−σ} g(σ)`, where the amplitude `g` tends to zero but more
slowly than every exponential, is the L-series of no sequence.

**The amplitude of a reflected half.** The quotient of the two halves is a quotient of Gamma
factors times a Dirichlet series. By the logarithmic convexity of `Γ`,
`(z−1)^h Γ(z) ≤ Γ(z+h) ≤ (z+h)^h Γ(z)`, so the amplitude is of exact order `σ^{−h}`: the Laplace
transform of the density `u^{h−1}`, which starts at first contact.

* `not_exists_lSeries_pencil_shift`: for every `h > 0` the pencil over its dominant half is the
  L-series of no sequence.
* `not_exists_lSeries_constantTerm`: for every height `Y > 0` the cleared constant term over its
  dominant half is the L-series of no sequence; here `B = Y²` and the amplitude has order
  `σ^{−1/2}`.
-/

open Complex Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open _root_.RHTower GaloisForLFunctions.InfiniteRankPurityTheory

/-! ### The first coefficient test -/

/-- **The first coefficient test.** If `‖R(σ)‖ = B^{−σ} g(σ)` for large real `σ`, where `g`
tends to zero and `e^{εσ} g(σ) → ∞` for every `ε > 0`, then `c + R` is the L-series of no
sequence: at the first nonzero coefficient `n` of `R` the product `n^σ R(σ)` would have a finite
nonzero limit, while `(n/B)^σ g(σ)` tends to `0` for `n ≤ B` and to `∞` for `n > B`. -/
theorem not_lSeries_of_slow_amplitude {R : ℝ → ℂ} {B : ℝ} (hB : 0 < B) {g : ℝ → ℝ}
    (hnorm : ∀ᶠ σ : ℝ in atTop, ‖R σ‖ = B ^ (-σ) * g σ)
    (hg0 : Tendsto g atTop (𝓝 0))
    (hg : ∀ ε : ℝ, 0 < ε → Tendsto (fun σ : ℝ => Real.exp (ε * σ) * g σ) atTop atTop)
    (c : ℂ) :
    ¬ ∃ (a : ℕ → ℂ) (σ₀ : ℝ), LSeriesSummable a σ₀ ∧ ∀ σ : ℝ, σ₀ ≤ σ →
      c + R σ = LSeries a σ := by
  rintro ⟨a, σ₀, hsum, heq⟩
  -- remove the constant coefficient
  have hδ : ∀ s : ℂ, LSeriesSummable (c • LSeries.delta) s := fun s =>
    (LSeriesSummable_congr' s (f := 0) (g := c • LSeries.delta) (by
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hn1 : n ≠ 1 := by omega
      simp [LSeries.delta, hn1])).mp (LSeriesSummable_zero)
  let f : ℕ → ℂ := fun n => if n = 0 then 0 else (a - c • LSeries.delta) n
  have hfg : ∀ {n : ℕ}, n ≠ 0 → f n = (a - c • LSeries.delta) n := fun {n} hn => if_neg hn
  have hffin : LSeries.abscissaOfAbsConv f < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_congr hfg]
    exact (hsum.sub (hδ _)).abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  have hfval : ∀ᶠ σ : ℝ in atTop, LSeries f σ = R σ := by
    filter_upwards [eventually_ge_atTop σ₀] with σ hσ0
    have hsumσ : LSeriesSummable a σ := hsum.of_re_le_re (by simpa using hσ0)
    rw [LSeries_congr hfg, LSeries_sub hsumσ (hδ _), LSeries_smul, LSeries_delta, ← heq σ hσ0,
      Pi.one_apply]
    ring
  -- the amplitude is eventually positive
  have hgpos : ∀ᶠ σ : ℝ in atTop, 0 < g σ := by
    filter_upwards [(hg 1 one_pos).eventually_gt_atTop 0] with σ hσ
    by_contra hneg
    exact absurd hσ (not_lt.mpr
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (not_lt.mp hneg)))
  -- some coefficient does not vanish
  have hex : ∃ n : ℕ, n ≠ 0 ∧ f n ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨σ, hσ1, hσ2, hσ3⟩ := (hfval.and (hgpos.and hnorm)).exists
    rw [LSeries_congr (g := 0) (fun {n} hn => by rw [Pi.zero_apply]; exact hall n hn),
      LSeries_zero, Pi.zero_apply] at hσ1
    rw [← hσ1, norm_zero] at hσ3
    exact absurd hσ3 (mul_pos (Real.rpow_pos_of_pos hB _) hσ2).ne
  classical
  -- the first one
  obtain ⟨hN0, hNf⟩ := Nat.find_spec hex
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hfm : ∀ m ≤ k, f m = 0 := by
    intro m hm
    by_cases hm0 : m = 0
    · rw [hm0]
      exact if_pos rfl
    · by_contra hne
      have := Nat.find_min' hex ⟨hm0, hne⟩
      omega
  rw [hk] at hNf
  have hconv := (LSeries.tendsto_cpow_mul_atTop hfm hffin).norm
  have hD : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set ε : ℝ := Real.log ((k : ℝ) + 1) - Real.log B with hε
  have hprod : ∀ᶠ σ : ℝ in atTop,
      ‖((k : ℂ) + 1) ^ (σ : ℂ) * LSeries f σ‖ = Real.exp (ε * σ) * g σ := by
    filter_upwards [hfval, hnorm] with σ hσ1 hσ2
    have hb : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [norm_mul, hσ1, hσ2, hb, Complex.norm_cpow_eq_rpow_re_of_pos hD, Complex.ofReal_re,
      Real.rpow_def_of_pos hD, Real.rpow_def_of_pos hB, ← mul_assoc, ← Real.exp_add]
    congr 2
    rw [hε]
    ring
  rcases le_or_gt ε 0 with hε0 | hε0
  · -- `n ≤ B`: the product is at most the amplitude and tends to zero
    have hzero : Tendsto (fun σ : ℝ => ‖((k : ℂ) + 1) ^ (σ : ℂ) * LSeries f σ‖) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg0
        (Eventually.of_forall fun σ => norm_nonneg _) ?_
      filter_upwards [hprod, hgpos, eventually_ge_atTop (0 : ℝ)] with σ hσ hσg hσ0
      rw [hσ]
      exact mul_le_of_le_one_left hσg.le
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hε0 hσ0))
    exact hNf (norm_eq_zero.mp (tendsto_nhds_unique hconv hzero))
  · -- `n > B`: the product tends to infinity
    exact not_tendsto_nhds_of_tendsto_atTop
      ((hg ε hε0).congr' (hprod.mono fun σ h => h.symm)) _ hconv

/-! ### Quotients of the Gamma function -/

/-- Logarithmic convexity of `Γ`, lower side: `(z − 1)^h Γ(z) ≤ Γ(z + h)`. -/
theorem rpow_mul_gamma_le {z h : ℝ} (hz : 1 < z) (hh : 0 < h) :
    (z - 1) ^ h * Real.Gamma z ≤ Real.Gamma (z + h) := by
  have hs := Real.convexOn_log_Gamma.slope_mono_adjacent (x := z - 1) (y := z) (z := z + h)
    (by rw [Set.mem_Ioi]; linarith) (by rw [Set.mem_Ioi]; linarith) (by linarith) (by linarith)
  simp only [Function.comp_apply] at hs
  have hz1 : 0 < z - 1 := by linarith
  have hGm : 0 < Real.Gamma (z - 1) := Real.Gamma_pos_of_pos hz1
  have hGz : 0 < Real.Gamma z := Real.Gamma_pos_of_pos (by linarith)
  have hGh : 0 < Real.Gamma (z + h) := Real.Gamma_pos_of_pos (by linarith)
  have hG : Real.Gamma z = (z - 1) * Real.Gamma (z - 1) := by
    have := Real.Gamma_add_one hz1.ne'
    rwa [sub_add_cancel] at this
  have hlog : Real.log (Real.Gamma z) - Real.log (Real.Gamma (z - 1)) = Real.log (z - 1) := by
    rw [hG, Real.log_mul hz1.ne' hGm.ne']
    ring
  rw [hlog, show z - (z - 1) = 1 by ring, div_one, show z + h - z = h by ring,
    le_div_iff₀ hh] at hs
  calc (z - 1) ^ h * Real.Gamma z
      = Real.exp (Real.log (z - 1) * h + Real.log (Real.Gamma z)) := by
        rw [Real.exp_add, Real.exp_log hGz, Real.rpow_def_of_pos hz1]
    _ ≤ Real.exp (Real.log (Real.Gamma (z + h))) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.Gamma (z + h) := Real.exp_log hGh

/-- Logarithmic convexity of `Γ`, upper side: `Γ(z + h) ≤ (z + h)^h Γ(z)`. -/
theorem gamma_le_rpow_mul_gamma {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    Real.Gamma (z + h) ≤ (z + h) ^ h * Real.Gamma z := by
  have hs := Real.convexOn_log_Gamma.slope_mono_adjacent (x := z) (y := z + h)
    (z := z + h + 1) (by rw [Set.mem_Ioi]; exact hz) (by rw [Set.mem_Ioi]; linarith)
    (by linarith) (by linarith)
  simp only [Function.comp_apply] at hs
  have hzh : 0 < z + h := by linarith
  have hGz : 0 < Real.Gamma z := Real.Gamma_pos_of_pos hz
  have hGh : 0 < Real.Gamma (z + h) := Real.Gamma_pos_of_pos hzh
  have hlog : Real.log (Real.Gamma (z + h + 1)) - Real.log (Real.Gamma (z + h)) =
      Real.log (z + h) := by
    rw [Real.Gamma_add_one hzh.ne', Real.log_mul hzh.ne' hGh.ne']
    ring
  rw [hlog, show z + h - z = h by ring, show z + h + 1 - (z + h) = 1 by ring, div_one,
    div_le_iff₀ hh] at hs
  calc Real.Gamma (z + h) = Real.exp (Real.log (Real.Gamma (z + h))) := (Real.exp_log hGh).symm
    _ ≤ Real.exp (Real.log (z + h) * h + Real.log (Real.Gamma z)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = (z + h) ^ h * Real.Gamma z := by
        rw [Real.exp_add, Real.exp_log hGz, Real.rpow_def_of_pos hzh]

theorem gamma_quotient_le {z h : ℝ} (hz : 1 < z) (hh : 0 < h) :
    Real.Gamma z / Real.Gamma (z + h) ≤ (z - 1) ^ (-h) := by
  have hGh := Real.Gamma_pos_of_pos (show 0 < z + h by linarith)
  have hzp : 0 < (z - 1) ^ h := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith), div_le_iff₀ hGh, ← div_eq_inv_mul, le_div_iff₀ hzp]
  linarith [rpow_mul_gamma_le hz hh]

theorem le_gamma_quotient {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    (z + h) ^ (-h) ≤ Real.Gamma z / Real.Gamma (z + h) := by
  have hGh := Real.Gamma_pos_of_pos (show 0 < z + h by linarith)
  have hzp : 0 < (z + h) ^ h := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith), le_div_iff₀ hGh, ← div_eq_inv_mul, div_le_iff₀ hzp]
  linarith [gamma_le_rpow_mul_gamma hz hh]

/-- The Gamma quotient of a shift tends to zero. -/
theorem tendsto_gamma_quotient_zero {h : ℝ} (hh : 0 < h) :
    Tendsto (fun σ : ℝ => Real.Gamma ((σ - h) / 2) / Real.Gamma ((σ - h) / 2 + h)) atTop
      (𝓝 0) := by
  have hlin : Tendsto (fun σ : ℝ => (σ - h) / 2 - 1) atTop atTop := by
    have h1 := tendsto_atTop_add_const_right atTop (-(h / 2 + 1))
      (tendsto_id.atTop_div_const (two_pos : (0 : ℝ) < 2))
    refine h1.congr fun σ => ?_
    simp only [id]
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((tendsto_rpow_neg_atTop hh).comp hlin) ?_ ?_
  · filter_upwards [eventually_gt_atTop (h + 2)] with σ hσ
    exact div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le
      (Real.Gamma_pos_of_pos (by linarith)).le
  · filter_upwards [eventually_gt_atTop (h + 2)] with σ hσ
    exact gamma_quotient_le (by linarith) hh

/-- The Gamma quotient of a shift decays more slowly than every exponential. -/
theorem tendsto_exp_mul_gamma_quotient {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) :
    Tendsto (fun σ : ℝ => Real.exp (ε * σ) *
      (Real.Gamma ((σ - h) / 2) / Real.Gamma ((σ - h) / 2 + h))) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_exp_mul_div_rpow_atTop h ε hε)
  filter_upwards [eventually_gt_atTop (h + 2)] with σ hσ
  have hσ0 : 0 < σ := by linarith
  have hzh : 0 < (σ - h) / 2 + h := by linarith
  have hpow : σ ^ (-h) ≤ ((σ - h) / 2 + h) ^ (-h) := by
    rw [Real.rpow_neg hσ0.le, Real.rpow_neg hzh.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hzh _)
      (Real.rpow_le_rpow hzh.le (by linarith) hh.le)
  calc Real.exp (ε * σ) / σ ^ h = Real.exp (ε * σ) * σ ^ (-h) := by
        rw [Real.rpow_neg hσ0.le, div_eq_mul_inv]
    _ ≤ Real.exp (ε * σ) * (Real.Gamma ((σ - h) / 2) / Real.Gamma ((σ - h) / 2 + h)) :=
        mul_le_mul_of_nonneg_left (hpow.trans (le_gamma_quotient (by linarith) hh))
          (Real.exp_pos _).le

/-! ### The amplitude of a reflected half -/

/-- `Γ_ℝ` on the real axis. -/
theorem gammaR_ofReal (x : ℝ) :
    Gammaℝ (x : ℂ) = ((π ^ (-x / 2) * Real.Gamma (x / 2) : ℝ) : ℂ) := by
  have h1 : (-(x : ℂ) / 2) = ((-x / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
  have h2 : ((x : ℂ) / 2) = ((x / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [Complex.Gammaℝ_def, h1, h2, Complex.Gamma_ofReal, ← Complex.ofReal_cpow Real.pi_pos.le,
    ← Complex.ofReal_mul]

theorem norm_gammaR_ofReal {x : ℝ} (hx : 0 < x) :
    ‖Gammaℝ (x : ℂ)‖ = π ^ (-x / 2) * Real.Gamma (x / 2) := by
  rw [gammaR_ofReal, Complex.norm_real, Real.norm_of_nonneg]
  exact mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
    (Real.Gamma_pos_of_pos (by linarith)).le

/-- The quotient of two values of `Γ_ℝ` at distance `2h`. -/
theorem norm_gammaR_quotient {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    ‖Gammaℝ (x : ℂ)‖ / ‖Gammaℝ ((x + 2 * h : ℝ) : ℂ)‖ =
      π ^ h * (Real.Gamma (x / 2) / Real.Gamma (x / 2 + h)) := by
  have hπ : π ^ (-x / 2) = π ^ h * π ^ (-(x + 2 * h) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  have hp : π ^ (-(x + 2 * h) / 2) ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  have hG : Real.Gamma (x / 2 + h) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [norm_gammaR_ofReal hx, norm_gammaR_ofReal (by positivity), hπ,
    show (x + 2 * h) / 2 = x / 2 + h by ring]
  field_simp

/-- `‖ξ‖` on the real axis right of `1`. -/
theorem norm_xi_ofReal {x : ℝ} (hx : 1 < x) :
    ‖xi (x : ℂ)‖ = x * (x - 1) / 2 * (‖riemannZeta (x : ℂ)‖ * ‖Gammaℝ (x : ℂ)‖) := by
  have h1 : ‖(x : ℂ)‖ = x := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have h2 : ‖(x : ℂ) - 1‖ = x - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [xi_eq_zeta_mul_gammaR (by simpa using hx), norm_mul, norm_mul, norm_div, norm_mul, h1, h2]
  norm_num

/-- **The amplitude of the reflected half of a pencil**: a coefficient that tends to `π^h`
times the Gamma quotient. -/
theorem norm_xi_shift_quotient {σ h : ℝ} (hh : 0 < h) (hσ : 1 + h < σ) :
    ‖xi ((σ - h : ℝ) : ℂ) / xi ((σ + h : ℝ) : ℂ)‖ =
      (σ - h) * (σ - h - 1) / ((σ + h) * (σ + h - 1)) *
        (‖riemannZeta ((σ - h : ℝ) : ℂ)‖ / ‖riemannZeta ((σ + h : ℝ) : ℂ)‖) * π ^ h *
        (Real.Gamma ((σ - h) / 2) / Real.Gamma ((σ - h) / 2 + h)) := by
  have hG := norm_gammaR_quotient (x := σ - h) (by linarith) hh
  rw [show σ - h + 2 * h = σ + h by ring] at hG
  rw [norm_div, norm_xi_ofReal (by linarith), norm_xi_ofReal (by linarith),
    mul_assoc _ (π ^ h) _, ← hG]
  ring

/-- The coefficient of the amplitude tends to `π^h`. -/
theorem tendsto_shiftCoefficient {h : ℝ} :
    Tendsto (fun σ : ℝ => (σ - h) * (σ - h - 1) / ((σ + h) * (σ + h - 1)) *
      (‖riemannZeta ((σ - h : ℝ) : ℂ)‖ / ‖riemannZeta ((σ + h : ℝ) : ℂ)‖) * π ^ h) atTop
      (𝓝 (π ^ h)) := by
  have hr : Tendsto (fun σ : ℝ => (σ - h) * (σ - h - 1) / ((σ + h) * (σ + h - 1))) atTop
      (𝓝 1) := by
    have h1 : Tendsto (fun σ : ℝ => 1 - 2 * h / (σ + h)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub
        (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop h tendsto_id))
    have h2 : Tendsto (fun σ : ℝ => 1 - 2 * h / (σ + (h - 1))) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub
        (tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right atTop (h - 1) tendsto_id))
    have h12 := h1.mul h2
    rw [sub_zero, one_mul] at h12
    refine h12.congr' ?_
    filter_upwards [eventually_gt_atTop (|h| + 1)] with σ hσ
    have ha : -|h| ≤ h := neg_abs_le h
    have hp1 : σ + h ≠ 0 := (by linarith : (0 : ℝ) < σ + h).ne'
    have hp2 : σ + (h - 1) ≠ 0 := (by linarith : (0 : ℝ) < σ + (h - 1)).ne'
    have hp3 : σ + h - 1 ≠ 0 := (by linarith : (0 : ℝ) < σ + h - 1).ne'
    field_simp
    ring
  have hζ : ∀ t : ℝ, Tendsto (fun σ : ℝ => ‖riemannZeta ((σ + t : ℝ) : ℂ)‖) atTop (𝓝 1) := by
    intro t
    have := (tendsto_riemannZeta_of_re_atTop_filter (w := fun σ : ℝ => ((σ + t : ℝ) : ℂ))
      (by
        simp only [Complex.ofReal_re]
        exact tendsto_atTop_add_const_right atTop t tendsto_id)).norm
    rwa [norm_one] at this
  have hm : Tendsto (fun σ : ℝ => ‖riemannZeta ((σ - h : ℝ) : ℂ)‖) atTop (𝓝 1) := by
    simpa only [sub_eq_add_neg] using hζ (-h)
  have hlim := (hr.mul (hm.div (hζ h) one_ne_zero)).mul_const (π ^ h)
  rwa [div_one, mul_one, one_mul] at hlim

theorem tendsto_norm_xi_shift_quotient_zero {h : ℝ} (hh : 0 < h) :
    Tendsto (fun σ : ℝ => ‖xi ((σ - h : ℝ) : ℂ) / xi ((σ + h : ℝ) : ℂ)‖) atTop (𝓝 0) := by
  have hlim := (tendsto_shiftCoefficient (h := h)).mul (tendsto_gamma_quotient_zero hh)
  rw [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 + h)] with σ hσ
  exact (norm_xi_shift_quotient hh hσ).symm

theorem tendsto_exp_mul_norm_xi_shift_quotient {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) :
    Tendsto (fun σ : ℝ => Real.exp (ε * σ) *
      ‖xi ((σ - h : ℝ) : ℂ) / xi ((σ + h : ℝ) : ℂ)‖) atTop atTop := by
  have hlim := (tendsto_exp_mul_gamma_quotient hh hε).atTop_mul_pos
    (Real.rpow_pos_of_pos Real.pi_pos h) (tendsto_shiftCoefficient (h := h))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 + h)] with σ hσ
  rw [norm_xi_shift_quotient hh hσ]
  ring

/-! ### Pencils at every shift -/

/-- **The pencil at any shift over its dominant half is not a Dirichlet series.** For `h > 0`
there is no sequence whose L-series converges somewhere and equals
`(ξ(σ+h) + ξ(σ−h))/ξ(σ+h)` for all large real `σ`. -/
theorem not_exists_lSeries_pencil_shift {h : ℝ} (hh : 0 < h) :
    ¬ ∃ (a : ℕ → ℂ) (σ₀ : ℝ), LSeriesSummable a σ₀ ∧ ∀ σ : ℝ, σ₀ ≤ σ →
      (xi ((σ : ℂ) + h) + xi ((σ : ℂ) - h)) / xi ((σ : ℂ) + h) = LSeries a σ := by
  rintro ⟨a, σ₀, hsum, heq⟩
  have e1 : ∀ σ : ℝ, (σ : ℂ) + h = ((σ + h : ℝ) : ℂ) := fun σ => (Complex.ofReal_add σ h).symm
  have e2 : ∀ σ : ℝ, (σ : ℂ) - h = ((σ - h : ℝ) : ℂ) := fun σ => (Complex.ofReal_sub σ h).symm
  simp only [e1, e2] at heq
  refine not_lSeries_of_slow_amplitude
    (R := fun σ : ℝ => xi ((σ - h : ℝ) : ℂ) / xi ((σ + h : ℝ) : ℂ)) (B := 1) one_pos
    (g := fun σ : ℝ => ‖xi ((σ - h : ℝ) : ℂ) / xi ((σ + h : ℝ) : ℂ)‖)
    (Eventually.of_forall fun σ => by rw [Real.one_rpow, one_mul])
    (tendsto_norm_xi_shift_quotient_zero hh)
    (fun ε hε => tendsto_exp_mul_norm_xi_shift_quotient hh hε) 1
    ⟨a, max σ₀ 1, hsum.of_re_le_re (by simp), fun σ hσ => ?_⟩
  have hne : xi ((σ + h : ℝ) : ℂ) ≠ 0 := xi_ne_zero_of_one_lt_re (by
    rw [Complex.ofReal_re]
    linarith [le_max_right σ₀ 1])
  rw [← heq σ ((le_max_left _ _).trans hσ)]
  show (1 : ℂ) + xi ((σ - h : ℝ) : ℂ) / xi ((σ + h : ℝ) : ℂ) = _
  rw [add_div, div_self hne]

/-! ### The cleared Eisenstein constant term -/

/-- The amplitude of the reflected half of the constant term: `B = Y²` and the pencil
amplitude at shift `½`. -/
theorem norm_constantTerm_quotient {Y σ : ℝ} (hY : 0 < Y) (hσ : 1 < σ) :
    ‖(σ : ℂ) * constantTermDual Y σ / (((σ : ℂ) - 1) * constantTermHalf Y σ)‖ =
      (Y ^ 2) ^ (-σ) * (Y * (σ / (σ - 1)) *
        ‖xi ((2 * σ - 1 / 2 - 1 / 2 : ℝ) : ℂ) / xi ((2 * σ - 1 / 2 + 1 / 2 : ℝ) : ℂ)‖) := by
  have e1 : (2 * (σ : ℂ) - 1) = ((2 * σ - 1 / 2 - 1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have e2 : (2 * (σ : ℂ)) = ((2 * σ - 1 / 2 + 1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hn1 : ‖(σ : ℂ)‖ = σ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hn2 : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hY1 : ‖(Y : ℂ) ^ (1 - (σ : ℂ))‖ = Y / Y ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Real.rpow_sub hY, Real.rpow_one]
  have hY2 : ‖(Y : ℂ) ^ (σ : ℂ)‖ = Y ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY, Complex.ofReal_re]
  have hYs : (Y ^ 2) ^ (-σ) = (Y ^ σ * Y ^ σ)⁻¹ := by
    rw [Real.rpow_neg (by positivity), sq, Real.mul_rpow hY.le hY.le]
  have hYp : Y ^ σ ≠ 0 := (Real.rpow_pos_of_pos hY σ).ne'
  have hx : ‖xi ((2 * σ - 1 / 2 + 1 / 2 : ℝ) : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (xi_ne_zero_of_one_lt_re (by
      rw [Complex.ofReal_re]
      linarith))
  have hσ1 : σ - 1 ≠ 0 := (sub_pos.mpr hσ).ne'
  rw [constantTermDual, constantTermHalf, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
    hn1, hn2, hY1, hY2, e1, e2, hYs, norm_div]
  field_simp

/-- **The cleared Eisenstein constant term over its dominant half is not a Dirichlet series**,
at every height `Y > 0`. -/
theorem not_exists_lSeries_constantTerm {Y : ℝ} (hY : 0 < Y) :
    ¬ ∃ (a : ℕ → ℂ) (σ₀ : ℝ), LSeriesSummable a σ₀ ∧ ∀ σ : ℝ, σ₀ ≤ σ →
      constantTerm Y σ / (((σ : ℂ) - 1) * constantTermHalf Y σ) = LSeries a σ := by
  rintro ⟨a, σ₀, hsum, heq⟩
  have hx : Tendsto (fun σ : ℝ => 2 * σ - 1 / 2) atTop atTop := by
    have h1 := tendsto_atTop_add_const_right atTop (-(1 / 2 : ℝ))
      (tendsto_id.const_mul_atTop (two_pos : (0 : ℝ) < 2))
    refine h1.congr fun σ => ?_
    simp only [id]
    ring
  have hfrac : Tendsto (fun σ : ℝ => Y * (σ / (σ - 1))) atTop (𝓝 Y) := by
    have h1 : Tendsto (fun σ : ℝ => 1 + 1 / (σ + -1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (-1) tendsto_id))
    have h2 := h1.const_mul Y
    rw [add_zero, mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
    have hσ1 : σ + -1 ≠ 0 := by linarith
    have hσ2 : σ - 1 ≠ 0 := by linarith
    field_simp
    ring
  refine not_lSeries_of_slow_amplitude
    (R := fun σ : ℝ => (σ : ℂ) * constantTermDual Y σ / (((σ : ℂ) - 1) * constantTermHalf Y σ))
    (B := Y ^ 2) (by positivity)
    (g := fun σ : ℝ => Y * (σ / (σ - 1)) *
      ‖xi ((2 * σ - 1 / 2 - 1 / 2 : ℝ) : ℂ) / xi ((2 * σ - 1 / 2 + 1 / 2 : ℝ) : ℂ)‖)
    ?_ ?_ ?_ 1 ⟨a, max σ₀ 2, hsum.of_re_le_re (by simp), fun σ hσ => ?_⟩
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
    exact norm_constantTerm_quotient hY hσ
  · have hlim := hfrac.mul
      ((tendsto_norm_xi_shift_quotient_zero (h := 1 / 2) (by norm_num)).comp hx)
    rw [mul_zero] at hlim
    exact hlim
  · intro ε hε
    have h1 := (tendsto_exp_mul_norm_xi_shift_quotient (h := 1 / 2) (ε := ε / 2) (by norm_num)
      (by linarith)).comp hx
    have h2 : Tendsto (fun σ : ℝ => Real.exp (ε / 4) * (Y * (σ / (σ - 1)))) atTop
        (𝓝 (Real.exp (ε / 4) * Y)) := hfrac.const_mul _
    refine (h1.atTop_mul_pos (mul_pos (Real.exp_pos _) hY) h2).congr' ?_
    filter_upwards with σ
    simp only [Function.comp_apply]
    have hexp : Real.exp (ε * σ) = Real.exp (ε / 2 * (2 * σ - 1 / 2)) * Real.exp (ε / 4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  · have hσ2 : (2 : ℝ) ≤ σ := (le_max_right _ _).trans hσ
    have hσ1 : (σ : ℂ) - 1 ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (by linarith)
    have hhalf : constantTermHalf Y σ ≠ 0 := constantTermHalf_ne_zero hY (by
      show (1 : ℝ) / 2 < ((σ : ℂ)).re
      rw [Complex.ofReal_re]
      linarith)
    rw [← heq σ ((le_max_left _ _).trans hσ)]
    show (1 : ℂ) + (σ : ℂ) * constantTermDual Y σ / (((σ : ℂ) - 1) * constantTermHalf Y σ) = _
    rw [constantTerm, add_div, div_self (mul_ne_zero hσ1 hhalf)]

end GaloisForLFunctions.FloorFreeArithmetic
