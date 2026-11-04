import GaloisForLFunctions.ZeroConfigurationGeometry.PerturbedLatticeProducts
import GaloisForLFunctions.RHTower.ThetaRenewalProbabilityPhase
import GaloisForLFunctions.HTGeometry.SineVerticalDecay

/-!
# Products over a perturbed lattice on the strip

`PerturbedLatticeProducts` bounds `sin((π/h)(x − θh)) Π_{k ∈ S} r_k(x)` on the real line. The local
camera needs the same product off the line, because the far points of a cluster may be tilted.
For `|Im z| ≤ 1/2` the bound reduces to the real one at `x = Re z`:

* `|z − i| ≤ (3/2)|x − i|`, `|z − μ_k| ≥ |x − μ_k|` and `|i − ν_k| ≥ |i − Re ν_k|/2`, so
  `|r_k(z) − 1| ≤ 3L |x − i|/(|x − μ_k| |i − Re ν_k|)` (`norm_pertFactor_sub_one_le_strip`), the
  summand of the real near/far estimate;
* near the nearest lattice point `|sin u| ≤ |u| e^{|Im u|}` (`RHTower.norm_csin_le_norm_mul_exp`).

Hence `|sin · Π r_k(z)| ≤ K (1 + |Re z|)^p` uniformly in `S`
(`norm_sin_mul_prod_pertFactor_le_strip`), with `K = B e^{3L C}` and `p = 12L(1 + L)/h`.

**The product at an isolated point** (`norm_prod_pertFactor_ge_strip`). If `z` is at distance
`≥ η` from every `ν_k` and `Re z` at distance `≥ h/4` from every lattice point, the product is
bounded below uniformly in `S`. Every factor is at least `c₀ = η/((η + L)(1 + L))`
(`isoConst_le_norm_pertFactor`). A factor with `|r_k − 1| ≤ 1/2` is at least `e^{−2|r_k − 1|}`, and
the others are at most `6L Σ T_k` in number, where `Σ T_k` is the near/far sum. So
`|Π r_k(z)| ≥ c₀ e^{−κC} (1 + |Re z|)^{−4κ(1 + L)/h}`, `κ = 6L(1 + log(1/c₀))`.
-/

open Complex Set Filter Topology Finset
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- The sine is unchanged in norm by a shift by an integer multiple of `π`. -/
theorem norm_sin_add_int_mul_pi (w : ℂ) (k : ℤ) :
    ‖Complex.sin (w + k * π)‖ = ‖Complex.sin w‖ := by
  rw [Complex.sin_add, show ((k : ℂ) * π) = ((k * π : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos, Real.sin_int_mul_pi, Real.cos_int_mul_pi,
    Complex.ofReal_zero, mul_zero, add_zero, norm_mul]
  have : ‖(((-1 : ℝ) ^ k : ℝ) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_zpow, abs_neg, abs_one, one_zpow]
  rw [this, mul_one]

/-- **The factors off the line.** For `|Im z| ≤ 1/2` the deviation `|r_k(z) − 1|` is at most `3L`
times the summand of the real near/far estimate at `x = Re z`. -/
theorem norm_pertFactor_sub_one_le_strip {h θ L : ℝ} {ν : ℤ → ℂ}
    (hL : ∀ k, ‖ν k - latPt h θ k‖ ≤ L) (him : ∀ k, |(ν k).im| ≤ 1 / 2) (k : ℤ) {z : ℂ}
    (hzim : |z.im| ≤ 1 / 2) (hx : z.re ≠ latPt h θ k) :
    ‖pertFactor h θ ν k z - 1‖ ≤
      3 * L * (‖(z.re : ℂ) - I‖ / (|z.re - latPt h θ k| * ‖I - (((ν k).re : ℝ) : ℂ)‖)) := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hzk : z ≠ latPt h θ k := fun e => hx (by rw [e, Complex.ofReal_re])
  have h1 := norm_pertFactor_sub_one_le hL k (I_sub_ne_zero (him k)) hzk
  have hd : 0 < |z.re - latPt h θ k| := abs_pos.mpr (sub_ne_zero.mpr hx)
  have hb := half_le_norm_I_sub (him k)
  have hb' : 1 ≤ ‖I - (((ν k).re : ℝ) : ℂ)‖ := one_le_norm_I_sub_ofReal _
  have h2 := norm_I_sub_re_le (him k)
  -- `|z − i| ≤ (3/2)|x − i|`
  have hzi : ‖z - I‖ ≤ 3 / 2 * ‖(z.re : ℂ) - I‖ := by
    have hxi : 1 ≤ ‖(z.re : ℂ) - I‖ := by
      have := one_le_norm_I_sub_ofReal z.re
      rwa [norm_sub_rev] at this
    have hsplit : z - I = ((z.re : ℂ) - I) + (z.im : ℂ) * I := by
      apply Complex.ext
      · simp
      · simp; ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith
  -- `|z − μ_k| ≥ |x − μ_k|`
  have hzμ : |z.re - latPt h θ k| ≤ ‖z - latPt h θ k‖ := by
    have := Complex.abs_re_le_norm (z - latPt h θ k)
    simpa using this
  refine h1.trans ?_
  have hA : 0 ≤ L * ‖z - I‖ := by positivity
  calc L * ‖z - I‖ / (‖z - latPt h θ k‖ * ‖I - ν k‖)
      ≤ L * (3 / 2 * ‖(z.re : ℂ) - I‖) / (|z.re - latPt h θ k| * (‖I - (((ν k).re : ℝ) : ℂ)‖ / 2)) := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hzi hL0) (by positivity)
        exact mul_le_mul hzμ (by linarith) (by positivity) (norm_nonneg _)
    _ = 3 * L * (‖(z.re : ℂ) - I‖ / (|z.re - latPt h θ k| * ‖I - (((ν k).re : ℝ) : ℂ)‖)) := by
        field_simp

/-- The constant of the sine and the nearest factor on the strip. -/
def nearestConstStrip (h L : ℝ) : ℝ :=
  (π / h * (h / 2 + 1 / 2 + L) * (1 + 2 * L) + 1) * Real.exp (π / (2 * h))

/-- **The uniform bound on the strip.** For `|Im z| ≤ 1/2`, `z` off the lattice, and every finite
`S`, `|sin((π/h)(z − θh)) Π_{k ∈ S} r_k(z)| ≤ K (1 + |Re z|)^p`. -/
theorem norm_sin_mul_prod_pertFactor_le_strip {h θ L : ℝ} (hh : 0 < h) (hθ : |θ| ≤ 1)
    {ν : ℤ → ℂ} (hL : ∀ k, ‖ν k - latPt h θ k‖ ≤ L) (him : ∀ k, |(ν k).im| ≤ 1 / 2)
    (S : Finset ℤ) {z : ℂ} (hzim : |z.im| ≤ 1 / 2) (hz : ∀ k, z ≠ latPt h θ k) :
    ‖Complex.sin (((π / h : ℝ) : ℂ) * (z - ((θ * h : ℝ) : ℂ))) * ∏ k ∈ S, pertFactor h θ ν k z‖ ≤
      nearestConstStrip h L * Real.exp (3 * L * nearFarConst h L) *
        (1 + |z.re|) ^ (3 * L * (4 * (1 + L) / h)) := by
  classical
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hLre : ∀ k, |(ν k).re - latPt h θ k| ≤ L := fun k =>
    (abs_re_sub_le_norm (ν k) (latPt h θ k)).trans (hL k)
  set x := z.re with hxdef
  set k₀ : ℤ := round (x / h - θ) with hk₀
  set μ₀ := latPt h θ k₀ with hμ₀
  have hnear : |x - μ₀| ≤ h / 2 := by
    have := abs_sub_round (x / h - θ)
    rw [← hk₀] at this
    have e : x - μ₀ = h * (x / h - θ - k₀) := by rw [hμ₀, latPt]; field_simp; ring
    rw [e, abs_mul, abs_of_pos hh]
    nlinarith
  -- the sine is `± sin((π/h)(z − μ₀))`, of size at most `(π/h)|z − μ₀| e^{π/(2h)}`
  have hexp : Real.exp |((((π / h : ℝ) : ℂ) * (z - (μ₀ : ℂ))).im)| ≤ Real.exp (π / (2 * h)) := by
    apply Real.exp_le_exp.mpr
    have e : ((((π / h : ℝ) : ℂ) * (z - (μ₀ : ℂ))).im) = π / h * z.im := by simp
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < π / h)]
    calc π / h * |z.im| ≤ π / h * (1 / 2) := mul_le_mul_of_nonneg_left hzim (by positivity)
      _ = π / (2 * h) := by field_simp
  have hsinz : ‖Complex.sin (((π / h : ℝ) : ℂ) * (z - ((θ * h : ℝ) : ℂ)))‖ =
      ‖Complex.sin (((π / h : ℝ) : ℂ) * (z - (μ₀ : ℂ)))‖ := by
    have e : ((π / h : ℝ) : ℂ) * (z - ((θ * h : ℝ) : ℂ)) =
        ((π / h : ℝ) : ℂ) * (z - (μ₀ : ℂ)) + k₀ * π := by
      rw [hμ₀, latPt]
      have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
      push_cast
      field_simp
      ring
    rw [e, norm_sin_add_int_mul_pi]
  have hsin1 : ‖Complex.sin (((π / h : ℝ) : ℂ) * (z - ((θ * h : ℝ) : ℂ)))‖ ≤
      Real.exp (π / (2 * h)) := by
    rw [hsinz]
    exact (HTGeometry.norm_csin_le_exp_abs_im _).trans hexp
  have hzμ₀ : ‖z - (μ₀ : ℂ)‖ ≤ h / 2 + 1 / 2 := by
    have hsplit : z - (μ₀ : ℂ) = ((x - μ₀ : ℝ) : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp [hxdef]
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    linarith
  -- the other factors are `h/2`-far from `x`
  have hfar : ∀ k ∈ S.erase k₀, h / 2 ≤ |x - latPt h θ k| := by
    intro k hk
    have hne := Finset.ne_of_mem_erase hk
    have := latPt_sep (θ := θ) hh hne
    have h2 := abs_sub_le (latPt h θ k) x μ₀
    rw [abs_sub_comm (latPt h θ k) x] at h2
    linarith
  have hsum := sum_dist_near_far_le hh hθ (ν := fun k => (ν k).re) hLre x (S.erase k₀) hfar
  have hrest : ‖∏ k ∈ S.erase k₀, pertFactor h θ ν k z‖ ≤
      Real.exp (3 * L * (nearFarConst h L + 4 * (1 + L) / h * Real.log (1 + |x|))) := by
    rw [norm_prod]
    calc ∏ k ∈ S.erase k₀, ‖pertFactor h θ ν k z‖
        ≤ ∏ k ∈ S.erase k₀, Real.exp ‖pertFactor h θ ν k z - 1‖ := by
          refine Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => ?_
          have := norm_sub_norm_le (pertFactor h θ ν k z) 1
          rw [norm_one] at this
          linarith [Real.add_one_le_exp ‖pertFactor h θ ν k z - 1‖]
      _ = Real.exp (∑ k ∈ S.erase k₀, ‖pertFactor h θ ν k z - 1‖) := by rw [Real.exp_sum]
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          calc ∑ k ∈ S.erase k₀, ‖pertFactor h θ ν k z - 1‖
              ≤ ∑ k ∈ S.erase k₀,
                  3 * L * (‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - (((ν k).re : ℝ) : ℂ)‖)) :=
                Finset.sum_le_sum fun k hk =>
                  norm_pertFactor_sub_one_le_strip hL him k hzim (fun e => by
                    have := hfar k hk
                    rw [← hxdef, e, sub_self, abs_zero] at this
                    linarith)
            _ = 3 * L * ∑ k ∈ S.erase k₀,
                  ‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - (((ν k).re : ℝ) : ℂ)‖) := by
                rw [Finset.mul_sum]
            _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  -- the sine and the nearest factor
  have hfirst : ‖Complex.sin (((π / h : ℝ) : ℂ) * (z - ((θ * h : ℝ) : ℂ))) *
      (if k₀ ∈ S then pertFactor h θ ν k₀ z else 1)‖ ≤ nearestConstStrip h L := by
    have hE : 1 ≤ Real.exp (π / (2 * h)) := Real.one_le_exp (by positivity)
    have hB1 : Real.exp (π / (2 * h)) ≤ nearestConstStrip h L := by
      unfold nearestConstStrip
      have : 0 ≤ π / h * (h / 2 + 1 / 2 + L) * (1 + 2 * L) := by positivity
      nlinarith
    rw [norm_mul]
    split_ifs with hk
    · have hzk₀ : z ≠ (μ₀ : ℂ) := hz k₀
      have hpos : 0 < ‖z - (μ₀ : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzk₀)
      rw [pertFactor, norm_mul, norm_div, norm_div]
      have hxν : ‖z - ν k₀‖ ≤ h / 2 + 1 / 2 + L := by
        have := norm_sub_le_norm_sub_add_norm_sub z (μ₀ : ℂ) (ν k₀)
        rw [norm_sub_rev (μ₀ : ℂ)] at this
        linarith [hL k₀]
      have hb1 := half_le_norm_I_sub (him k₀)
      have hratio : ‖I - (latPt h θ k₀ : ℂ)‖ / ‖I - ν k₀‖ ≤ 1 + 2 * L := by
        rw [div_le_iff₀ (by linarith)]
        have := norm_sub_le_norm_sub_add_norm_sub I (ν k₀) (latPt h θ k₀ : ℂ)
        nlinarith [hL k₀]
      have hs : ‖Complex.sin (((π / h : ℝ) : ℂ) * (z - ((θ * h : ℝ) : ℂ)))‖ ≤
          π / h * ‖z - (μ₀ : ℂ)‖ * Real.exp (π / (2 * h)) := by
        rw [hsinz]
        refine (_root_.RHTower.norm_csin_le_norm_mul_exp _).trans ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < π / h)]
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
      calc ‖Complex.sin (((π / h : ℝ) : ℂ) * (z - ((θ * h : ℝ) : ℂ)))‖ *
            (‖z - ν k₀‖ / ‖z - (latPt h θ k₀ : ℂ)‖ * (‖I - (latPt h θ k₀ : ℂ)‖ / ‖I - ν k₀‖))
          ≤ (π / h * ‖z - (μ₀ : ℂ)‖ * Real.exp (π / (2 * h))) *
              (‖z - ν k₀‖ / ‖z - (μ₀ : ℂ)‖ * (1 + 2 * L)) := by gcongr
        _ = π / h * ‖z - ν k₀‖ * (1 + 2 * L) * Real.exp (π / (2 * h)) := by field_simp
        _ ≤ π / h * (h / 2 + 1 / 2 + L) * (1 + 2 * L) * Real.exp (π / (2 * h)) := by gcongr
        _ ≤ nearestConstStrip h L := by
            unfold nearestConstStrip
            nlinarith [Real.exp_pos (π / (2 * h))]
    · rw [norm_one, mul_one]; linarith
  have hsplit : ∏ k ∈ S, pertFactor h θ ν k z =
      (if k₀ ∈ S then pertFactor h θ ν k₀ z else 1) * ∏ k ∈ S.erase k₀, pertFactor h θ ν k z := by
    split_ifs with hk
    · exact (Finset.mul_prod_erase S (fun k => pertFactor h θ ν k z) hk).symm
    · rw [Finset.erase_eq_of_notMem hk, one_mul]
  rw [hsplit, ← mul_assoc, norm_mul]
  have hpow : Real.exp (3 * L * (nearFarConst h L + 4 * (1 + L) / h * Real.log (1 + |x|))) =
      Real.exp (3 * L * nearFarConst h L) * (1 + |x|) ^ (3 * L * (4 * (1 + L) / h)) := by
    rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
    congr 1; ring
  have hB0 : 0 ≤ nearestConstStrip h L := by unfold nearestConstStrip; positivity
  calc _ ≤ nearestConstStrip h L * Real.exp (3 * L * (nearFarConst h L + 4 * (1 + L) / h *
        Real.log (1 + |x|))) := mul_le_mul hfirst hrest (norm_nonneg _) hB0
    _ = _ := by rw [hpow]; ring

/-! ### The product at an isolated point -/

theorem exp_neg_two_mul_le_one_sub {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    Real.exp (-(2 * u)) ≤ 1 - u := by
  have h := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * u)
  have h1 : 1 ≤ (1 - u) * Real.exp (2 * u) := by
    have h2 : (1 - u) * (1 + 2 * u + (2 * u) ^ 2 / 2) ≤ (1 - u) * Real.exp (2 * u) :=
      mul_le_mul_of_nonneg_left h (by linarith)
    nlinarith [mul_nonneg hu0 (by nlinarith : (0 : ℝ) ≤ 1 - 2 * u ^ 2)]
  have he : Real.exp (-(2 * u)) * Real.exp (2 * u) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos (-(2 * u)), Real.exp_pos (2 * u)]

/-- The floor `c₀ = η/((η + L)(1 + L))` of one factor at a point `η`-far from its `ν_k`. -/
def isoConst (L η : ℝ) : ℝ := η / ((η + L) * (1 + L))

/-- The rate `κ = 6L(1 + log(1/c₀))` of the product floor. -/
def isoRate (L η : ℝ) : ℝ := 6 * L * (1 + Real.log (1 / isoConst L η))

theorem isoConst_pos {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) : 0 < isoConst L η := by
  unfold isoConst; positivity

theorem isoConst_le_one {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) : isoConst L η ≤ 1 := by
  unfold isoConst
  rw [div_le_one (by positivity)]
  nlinarith

/-- **One factor at an isolated point.** -/
theorem isoConst_le_norm_pertFactor {h θ L η : ℝ} {ν : ℤ → ℂ}
    (hL : ∀ k, ‖ν k - latPt h θ k‖ ≤ L) (him : ∀ k, |(ν k).im| ≤ 1 / 2) (k : ℤ) {z : ℂ}
    (hη : 0 < η) (hzν : η ≤ ‖z - ν k‖) (hzk : z ≠ latPt h θ k) :
    isoConst L η ≤ ‖pertFactor h θ ν k z‖ := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hzμ : 0 < ‖z - (latPt h θ k : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzk)
  have hiν : 0 < ‖I - ν k‖ := norm_pos_iff.mpr (I_sub_ne_zero (him k))
  have hiμ : 1 ≤ ‖I - (latPt h θ k : ℂ)‖ := one_le_norm_I_sub_ofReal _
  have h1 : ‖z - (latPt h θ k : ℂ)‖ ≤ ‖z - ν k‖ + L := by
    have := norm_sub_le_norm_sub_add_norm_sub z (ν k) (latPt h θ k : ℂ)
    linarith [hL k]
  have h2 : ‖I - ν k‖ ≤ ‖I - (latPt h θ k : ℂ)‖ * (1 + L) := by
    have := norm_sub_le_norm_sub_add_norm_sub I (latPt h θ k : ℂ) (ν k)
    rw [norm_sub_rev (latPt h θ k : ℂ)] at this
    nlinarith [hL k]
  have hA : η / (η + L) ≤ ‖z - ν k‖ / ‖z - (latPt h θ k : ℂ)‖ := by
    rw [div_le_div_iff₀ (by positivity) hzμ]
    nlinarith
  have hB : 1 / (1 + L) ≤ ‖I - (latPt h θ k : ℂ)‖ / ‖I - ν k‖ := by
    rw [div_le_div_iff₀ (by positivity) hiν]
    linarith
  rw [pertFactor, norm_mul, norm_div, norm_div]
  calc isoConst L η = η / (η + L) * (1 / (1 + L)) := by unfold isoConst; field_simp
    _ ≤ _ := mul_le_mul hA hB (by positivity) (by positivity)

/-- **The product at an isolated point.** -/
theorem norm_prod_pertFactor_ge_strip {h θ L η : ℝ} (hh : 0 < h) (hθ : |θ| ≤ 1) {ν : ℤ → ℂ}
    (hL : ∀ k, ‖ν k - latPt h θ k‖ ≤ L) (him : ∀ k, |(ν k).im| ≤ 1 / 2) (S : Finset ℤ)
    {z : ℂ} (hzim : |z.im| ≤ 1 / 2) (hzlat : ∀ k, h / 4 ≤ |z.re - latPt h θ k|) (hη : 0 < η)
    (hzν : ∀ k, η ≤ ‖z - ν k‖) :
    isoConst L η * Real.exp (-(isoRate L η * nearFarConst h L)) *
        (1 + |z.re|) ^ (-(isoRate L η * (4 * (1 + L) / h))) ≤
      ‖∏ k ∈ S, pertFactor h θ ν k z‖ := by
  classical
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hLre : ∀ k, |(ν k).re - latPt h θ k| ≤ L := fun k =>
    (abs_re_sub_le_norm (ν k) (latPt h θ k)).trans (hL k)
  set c₀ := isoConst L η with hc₀
  have hc0 : 0 < c₀ := isoConst_pos hL0 hη
  have hc1 : c₀ ≤ 1 := isoConst_le_one hL0 hη
  have hlog : 0 ≤ Real.log (1 / c₀) := Real.log_nonneg (by rw [le_div_iff₀ hc0]; linarith)
  set κ := isoRate L η with hκ
  have hκ6 : 6 * L ≤ κ := by
    rw [hκ, isoRate, ← hc₀]; nlinarith
  set x := z.re with hxdef
  have hzx : ∀ k, z ≠ latPt h θ k := fun k e => by
    have := hzlat k
    rw [hxdef, e, Complex.ofReal_re, sub_self, abs_zero] at this
    linarith
  have hxk : ∀ k, x ≠ latPt h θ k := fun k e => by
    have := hzlat k
    rw [e, sub_self, abs_zero] at this
    linarith
  set k₀ : ℤ := round (x / h - θ) with hk₀
  set μ₀ := latPt h θ k₀ with hμ₀
  have hnear : |x - μ₀| ≤ h / 2 := by
    have := abs_sub_round (x / h - θ)
    rw [← hk₀] at this
    have e : x - μ₀ = h * (x / h - θ - k₀) := by rw [hμ₀, latPt]; field_simp; ring
    rw [e, abs_mul, abs_of_pos hh]
    nlinarith
  have hfar : ∀ k ∈ S.erase k₀, h / 2 ≤ |x - latPt h θ k| := by
    intro k hk
    have hne := Finset.ne_of_mem_erase hk
    have := latPt_sep (θ := θ) hh hne
    have h2 := abs_sub_le (latPt h θ k) x μ₀
    rw [abs_sub_comm (latPt h θ k) x] at h2
    linarith
  have hsum := sum_dist_near_far_le hh hθ (ν := fun k => (ν k).re) hLre x (S.erase k₀) hfar
  set T : ℤ → ℝ := fun k => ‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - (((ν k).re : ℝ) : ℂ)‖)
    with hT
  have hT0 : ∀ k, 0 ≤ T k := fun k => by rw [hT]; positivity
  -- each far factor is at least `e^{−κ T_k}`
  have hfac : ∀ k, Real.exp (-(κ * T k)) ≤ ‖pertFactor h θ ν k z‖ := by
    intro k
    have hdev := norm_pertFactor_sub_one_le_strip hL him k hzim (hxk k)
    rw [← hxdef] at hdev
    change ‖pertFactor h θ ν k z - 1‖ ≤ 3 * L * T k at hdev
    by_cases hsmall : 3 * L * T k ≤ 1 / 2
    · have h1 : 1 - 3 * L * T k ≤ ‖pertFactor h θ ν k z‖ := by
        have := norm_sub_norm_le (1 : ℂ) (pertFactor h θ ν k z)
        rw [norm_one, norm_sub_rev] at this
        linarith
      have h2 := exp_neg_two_mul_le_one_sub (by positivity : 0 ≤ 3 * L * T k) hsmall
      have h3 : Real.exp (-(κ * T k)) ≤ Real.exp (-(2 * (3 * L * T k))) :=
        Real.exp_le_exp.mpr (by nlinarith [hT0 k])
      linarith
    · push Not at hsmall
      have hlt : Real.exp (-(κ * T k)) < c₀ := by
        have h1 : Real.log (1 / c₀) < κ * T k := by
          have : 1 < 6 * L * T k := by linarith
          rw [hκ, isoRate, ← hc₀]
          nlinarith
        have h2 : Real.exp (-(κ * T k)) < Real.exp (-Real.log (1 / c₀)) :=
          Real.exp_lt_exp.mpr (by linarith)
        have e : Real.exp (-Real.log (1 / c₀)) = c₀ := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div, div_one]
        rwa [e] at h2
      exact hlt.le.trans (isoConst_le_norm_pertFactor hL him k hη (hzν k) (hzx k))
  have hrest : Real.exp (-(κ * (nearFarConst h L + 4 * (1 + L) / h * Real.log (1 + |x|)))) ≤
      ‖∏ k ∈ S.erase k₀, pertFactor h θ ν k z‖ := by
    rw [norm_prod]
    calc Real.exp (-(κ * (nearFarConst h L + 4 * (1 + L) / h * Real.log (1 + |x|))))
        ≤ Real.exp (-(κ * ∑ k ∈ S.erase k₀, T k)) := by
          apply Real.exp_le_exp.mpr
          have : ∑ k ∈ S.erase k₀, T k ≤ nearFarConst h L + 4 * (1 + L) / h * Real.log (1 + |x|) :=
            hsum
          nlinarith
      _ = ∏ k ∈ S.erase k₀, Real.exp (-(κ * T k)) := by
          rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ ∏ k ∈ S.erase k₀, ‖pertFactor h θ ν k z‖ :=
          Finset.prod_le_prod (fun k _ => (Real.exp_pos _).le) fun k _ => hfac k
  have hfirst : c₀ ≤ ‖(if k₀ ∈ S then pertFactor h θ ν k₀ z else 1)‖ := by
    split_ifs
    · exact isoConst_le_norm_pertFactor hL him k₀ hη (hzν k₀) (hzx k₀)
    · rw [norm_one]; exact hc1
  have hsplit : ∏ k ∈ S, pertFactor h θ ν k z =
      (if k₀ ∈ S then pertFactor h θ ν k₀ z else 1) * ∏ k ∈ S.erase k₀, pertFactor h θ ν k z := by
    split_ifs with hk
    · exact (Finset.mul_prod_erase S (fun k => pertFactor h θ ν k z) hk).symm
    · rw [Finset.erase_eq_of_notMem hk, one_mul]
  rw [hsplit, norm_mul]
  have hpow : Real.exp (-(κ * (nearFarConst h L + 4 * (1 + L) / h * Real.log (1 + |x|)))) =
      Real.exp (-(κ * nearFarConst h L)) * (1 + |x|) ^ (-(κ * (4 * (1 + L) / h))) := by
    rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
    congr 1; ring
  rw [mul_assoc, ← hpow]
  exact mul_le_mul hfirst hrest (Real.exp_pos _).le (norm_nonneg _)

end GaloisForLFunctions.ZeroConfigurationGeometry
