import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilySeesAttainedTopsAtAnExplicitLag
import GaloisForLFunctions.RHTower.LowHeightWeilTests

/-!
# Isolated twins of `ζ` cannot hide

`zeta_near_top_twin_tight_or_triple` leaves two alternatives for a hidden near-top record: two
further zeros within `2r`, or one companion exponentially close to it. The second is impossible.

A companion within `ε ≪ 1/V` of the record does not cancel it: the coefficients of the modulated
family are `D_c(z) = m(h_w(−iz − c)² + conj h_w(−iz̄ − c)²)` (`evenCoeff_modScaledBump_eq_mult_mul`), the
reflected part is small (`norm_reflected_le`), and `h_w` is Lipschitz on the strip
(`norm_paperFT_scaledBump_sub_le`, from `RHTower.norm_paperFT_sub_le`). Two nearby values of a smooth
transform, squared, keep a coherent phase (`re_coherent_squares_nonneg`):
`Re((h₂² + ε₂) conj(h₁² + ε₁)) ≥ 0` once `|h₂ − h₁| ≤ |h₁|/4` and `|εⱼ| ≤ |h₁|²/16`, so
`Re(D(z) conj D(z*)) ≥ 0` (`re_evenCoeff_mul_conj_nonneg`, both half planes in
`re_twin_mul_conj_nonneg` via `D(z̄) = conj D(z)`). The kernel moves little across `ε`
(`norm_fejerPowWin_sub_ofReal_le`: `|K_k(x) − K_k(θ)| ≤ 2|x − θ|V|K_k(θ)|`), hence the pair adds
(`norm_coherent_pair_ge`): `|D(z*)K(θ) + D(z)K(x)| ≥ |D(z*)|K(θ)/2`. Against the cluster law for the
isolated pair this is a quiet-record contradiction (`quiet_record_arith`).

**Theorem** (`zeta_isolated_twins_cannot_hide`). For a near-top zero above `T_w` and explicit
conditions on `V`, `r`, `k` (the tightness radius `twinTightRadius` small against `1/V`, `1/w`,
`H₀/(8we^{w/2}J_w)` and `a_w²/(8eV · 80 log(180(Γ+1))(e^{w/2}B_w)²)`, and
`2(4/3)^k A_w log(180(Γ+6))(1 + 4π²k²)^k < (Vr)^{2k+1}`), positivity of the modulated difference tests
on `[0, V]` forces two further zeros within `2r` of the Legendre record. A pair can hide a record
only with a third zero nearby: the twin alternative is reduced to clusters of at least three zeros.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Nearby exponents: kernels and coefficients -/

/-- **The kernel is Lipschitz near a real point.** For real `θ` and `|x − θ| V ≤ 1`,
`|K_k(x) − K_k(θ)| ≤ 2|x − θ| V |K_k(θ)|`. -/
theorem norm_fejerPowWin_sub_ofReal_le {V : ℝ} (hV : 0 ≤ V) (k : ℕ) (θ : ℝ) {x : ℂ}
    (hx : ‖x - θ‖ * V ≤ 1) :
    ‖fejerPowWin k V x - fejerPowWin k V θ‖ ≤ 2 * ‖x - θ‖ * V * ‖fejerPowWin k V θ‖ := by
  set ω : ℝ → ℝ := fun u => Real.sin (π * u / V) ^ (2 * k) with hω
  have hreal : fejerPowWin k V θ = ((∫ u in (0 : ℝ)..V, ω u * Real.exp (θ * u) : ℝ) : ℂ) := by
    rw [fejerPowWin, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hω]; push_cast; rfl
  have hint0 : 0 ≤ ∫ u in (0 : ℝ)..V, ω u * Real.exp (θ * u) :=
    intervalIntegral.integral_nonneg hV fun u _ => mul_nonneg (sin_pow_nonneg _ k) (Real.exp_pos _).le
  have hnorm : ‖fejerPowWin k V θ‖ = ∫ u in (0 : ℝ)..V, ω u * Real.exp (θ * u) := by
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hint0]
  have hdiff : fejerPowWin k V x - fejerPowWin k V θ = ∫ u in (0 : ℝ)..V,
      ((ω u : ℝ) : ℂ) * cexp ((θ : ℂ) * u) * (cexp ((x - θ) * u) - 1) := by
    rw [fejerPowWin, fejerPowWin, ← intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun u : ℝ => ((Real.sin (π * u / V) ^ (2 * k) : ℝ) : ℂ) *
        cexp (x * u)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun u : ℝ => ((Real.sin (π * u / V) ^ (2 * k) : ℝ) : ℂ) *
        cexp ((θ : ℂ) * u)).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hω]
    rw [mul_sub, mul_one, mul_assoc, ← Complex.exp_add]
    congr 3; ring
  rw [hdiff, hnorm]
  refine (intervalIntegral.norm_integral_le_integral_norm hV).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hV ((by fun_prop : Continuous fun u : ℝ =>
      ‖((ω u : ℝ) : ℂ) * cexp ((θ : ℂ) * u) * (cexp ((x - θ) * u) - 1)‖).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u : ℝ => 2 * ‖x - θ‖ * V * (ω u * Real.exp (θ * u))).intervalIntegrable
      _ _) fun u hu => ?_
  have hω0 : 0 ≤ ω u := sin_pow_nonneg _ k
  have hsmall : ‖(x - θ) * (u : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
    exact le_trans (mul_le_mul_of_nonneg_left hu.2 (norm_nonneg _)) hx
  have h1 := Complex.norm_exp_sub_one_le hsmall
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hω0, Complex.norm_exp]
  have e : ((θ : ℂ) * (u : ℂ)).re = θ * u := by simp
  rw [e]
  have h2 : ‖(x - θ) * (u : ℂ)‖ ≤ ‖x - θ‖ * V := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
    exact mul_le_mul_of_nonneg_left hu.2 (norm_nonneg _)
  calc ω u * Real.exp (θ * u) * ‖cexp ((x - θ) * u) - 1‖
      ≤ ω u * Real.exp (θ * u) * (2 * (‖x - θ‖ * V)) :=
        mul_le_mul_of_nonneg_left (h1.trans (by linarith)) (by positivity)
    _ = 2 * ‖x - θ‖ * V * (ω u * Real.exp (θ * u)) := by ring

/-- `|a| ≤ |a + b|` when `Re(b ā) ≥ 0`. -/
theorem norm_le_norm_add_of_re_mul_conj_nonneg {a b : ℂ} (h : 0 ≤ (b * conj a).re) :
    ‖a‖ ≤ ‖a + b‖ := by
  have e : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (b * conj a).re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_add]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have : ‖a‖ ^ 2 ≤ ‖a + b‖ ^ 2 := by rw [e]; nlinarith [sq_nonneg ‖b‖]
  exact le_of_sq_le_sq (by simpa using this) (norm_nonneg _) |>.trans le_rfl

/-- **Coherent squares.** If `|h₂ − h₁| ≤ |h₁|/4` and `|ε₁|, |ε₂| ≤ |h₁|²/16`, then
`Re((h₂² + ε₂) conj(h₁² + ε₁)) ≥ 0`: nearby values of a transform, squared, cannot cancel. -/
theorem re_coherent_squares_nonneg {h₁ h₂ ε₁ ε₂ : ℂ} (hh : ‖h₂ - h₁‖ ≤ ‖h₁‖ / 4)
    (he₁ : ‖ε₁‖ ≤ ‖h₁‖ ^ 2 / 16) (he₂ : ‖ε₂‖ ≤ ‖h₁‖ ^ 2 / 16) :
    0 ≤ ((h₂ ^ 2 + ε₂) * conj (h₁ ^ 2 + ε₁)).re := by
  set H := ‖h₁‖ with hH
  set Δ := h₂ - h₁ with hΔ
  have hh₂ : h₂ = h₁ + Δ := by rw [hΔ]; ring
  -- the main term `Re((h₂ conj h₁)²) ≥ H⁴/2`
  have hmain : H ^ 4 / 2 ≤ (h₂ ^ 2 * conj (h₁ ^ 2)).re := by
    have e : h₂ ^ 2 * conj (h₁ ^ 2) = (((H ^ 2 : ℝ) : ℂ) + Δ * conj h₁) ^ 2 := by
      rw [hh₂, map_pow]
      have : h₁ * conj h₁ = ((H ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      linear_combination (h₁ * conj h₁ + ((H ^ 2 : ℝ) : ℂ) + 2 * Δ * conj h₁) * this
    rw [e]
    set q := Δ * conj h₁ with hq
    have hqn : ‖q‖ ≤ H ^ 2 / 4 := by
      calc ‖q‖ = ‖Δ‖ * H := by rw [hq, norm_mul, Complex.norm_conj]
        _ ≤ H / 4 * H := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
        _ = H ^ 2 / 4 := by ring
    have hre : |q.re| ≤ ‖q‖ := Complex.abs_re_le_norm q
    have him : |q.im| ≤ ‖q‖ := Complex.abs_im_le_norm q
    have e2 : ((((H ^ 2 : ℝ) : ℂ) + q) ^ 2).re = (H ^ 2 + q.re) ^ 2 - q.im ^ 2 := by
      simp [sq, Complex.mul_re]
    rw [e2]
    have h1 : H ^ 2 * 3 / 4 ≤ H ^ 2 + q.re := by linarith [neg_abs_le q.re]
    have h2 : q.im ^ 2 ≤ (H ^ 2 / 4) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (him.trans hqn) 2
    have h3 : (H ^ 2 * 3 / 4) ^ 2 ≤ (H ^ 2 + q.re) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  -- the cross terms are small
  have hh2n : ‖h₂‖ ≤ 5 / 4 * H := by
    have := norm_add_le h₁ Δ; rw [← hh₂] at this; linarith
  have hcross : ‖h₂ ^ 2 * conj ε₁ + ε₂ * conj (h₁ ^ 2) + ε₂ * conj ε₁‖ ≤ 42 / 256 * H ^ 4 := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    simp only [norm_mul, Complex.norm_conj, norm_pow]
    have hH0 : 0 ≤ H := norm_nonneg _
    have a1 : ‖h₂‖ ^ 2 * ‖ε₁‖ ≤ (5 / 4 * H) ^ 2 * (H ^ 2 / 16) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hh2n 2) he₁ (norm_nonneg _) (by positivity)
    have a2 : ‖ε₂‖ * H ^ 2 ≤ H ^ 2 / 16 * H ^ 2 := mul_le_mul_of_nonneg_right he₂ (by positivity)
    have a3 : ‖ε₂‖ * ‖ε₁‖ ≤ H ^ 2 / 16 * (H ^ 2 / 16) := mul_le_mul he₂ he₁ (norm_nonneg _) (by positivity)
    nlinarith
  have hexp : (h₂ ^ 2 + ε₂) * conj (h₁ ^ 2 + ε₁) = h₂ ^ 2 * conj (h₁ ^ 2) +
      (h₂ ^ 2 * conj ε₁ + ε₂ * conj (h₁ ^ 2) + ε₂ * conj ε₁) := by
    rw [map_add]; ring
  rw [hexp, Complex.add_re]
  have := (Complex.re_le_norm _).trans hcross
  have := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hcross)
  nlinarith [pow_nonneg (norm_nonneg h₁) 4]

/-- `J_w = ∫ |κ(u/(4w))| du`, the mass of the bump of width `w`. -/
def bumpMass (w : ℝ) : ℝ := ∫ u, |weilBump (u / (4 * w))|

/-- **The transform is Lipschitz on the strip.** For `w|x − y| ≤ 1` and `|Im y| ≤ ½`,
`|h_w(x) − h_w(y)| ≤ 2w e^{w/2} J_w |x − y|`. -/
theorem norm_paperFT_scaledBump_sub_le {w : ℝ} (hw : 0 < w) {x y : ℂ} (hxy : w * ‖x - y‖ ≤ 1)
    (hy : |y.im| ≤ 1 / 2) :
    ‖paperFT (scaledBump w) x - paperFT (scaledBump w) y‖ ≤
      2 * w * Real.exp (w / 2) * bumpMass w * ‖x - y‖ := by
  have e : scaledBump w = fun u => ((weilBump (u / (4 * w)) : ℝ) : ℂ) := funext fun u => rfl
  have hcont : Continuous fun u : ℝ => weilBump (u / (4 * w)) :=
    weilBump.continuous.comp (continuous_id.div_const _)
  have hsupp : ∀ u, weilBump (u / (4 * w)) ≠ 0 → |u| ≤ w := fun u hu =>
    scaledBump_support' hw u (by rw [e]; simp only []; exact_mod_cast hu)
  rw [e]
  refine (norm_paperFT_sub_le hcont hsupp hxy).trans (le_of_eq_of_le rfl ?_)
  have hJ : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have h1 : Real.exp (|y.im| * w) ≤ Real.exp (w / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg y.im])
  rw [bumpMass] at hJ ⊢
  calc 2 * w * ‖x - y‖ * Real.exp (|y.im| * w) * ∫ u, |weilBump (u / (4 * w))|
      ≤ 2 * w * ‖x - y‖ * Real.exp (w / 2) * ∫ u, |weilBump (u / (4 * w))| := by gcongr
    _ = _ := by ring

/-- **Coefficients of the modulated family.** For a zero `½ + z`,
`D_c(z) = m (h_w(−iz − c)² + conj h_w(−i z̄ − c)²)`. -/
theorem evenCoeff_modScaledBump_eq_mult_mul {w : ℝ} (hw : 0 < w) (c : ℝ) {z : ℂ}
    (hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier) :
    evenCoeff zetaZeroConfig (modScaledBump w c) z = (zetaZeroConfig.mult (1 / 2 + z) : ℂ) *
      (paperFT (scaledBump w) (-(I * z) - c) ^ 2 +
        conj (paperFT (scaledBump w) (-(I * conj z) - c) ^ 2)) := by
  have hzc : (1 / 2 + conj z) ∈ zetaZeroConfig.carrier := by
    have := conj_mem_zetaZeroConfig hz
    have e : conj (1 / 2 + z) = 1 / 2 + conj z := by apply Complex.ext <;> simp
    rwa [e] at this
  have hmc : zetaZeroConfig.mult (1 / 2 + conj z) = zetaZeroConfig.mult (1 / 2 + z) := by
    have := mult_conj_zetaZeroConfig hz
    have e : conj (1 / 2 + z) = 1 / 2 + conj z := by apply Complex.ext <;> simp
    rwa [e] at this
  rw [evenCoeff, lagCoeff_modScaledBump zetaZeroConfig hw c hz,
    lagCoeff_modScaledBump zetaZeroConfig hw c hzc, hmc, map_mul, Complex.conj_natCast]
  ring

/-- The reflected term is small: `|h_w(−i z̄ − c)|² ≤ (e^{w/2}B_w)²/(1 + c)⁴` for `Im z ≥ 0`, `c ≥ 0`,
`|Re z| ≤ ½`. -/
theorem norm_reflected_le {w : ℝ} (hw : 0 < w) {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (him : 0 ≤ z.im)
    (hre : |z.re| ≤ 1 / 2) :
    ‖conj (paperFT (scaledBump w) (-(I * conj z) - c) ^ 2)‖ ≤
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + c) ^ 4 := by
  rw [Complex.norm_conj, norm_pow]
  have hx : |(-(I * conj z) - (c : ℂ)).im| ≤ 1 / 2 := by simpa using hre
  have h := norm_paperFT_scaledBump_le hw hx
  have hre' : |(-(I * conj z) - (c : ℂ)).re| = z.im + c := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re]
    rw [show 0 * z.re - 1 * -z.im = z.im by ring, show -z.im - c = -(z.im + c) by ring, abs_neg,
      abs_of_nonneg (by linarith)]
  rw [hre'] at h
  have hB : 0 ≤ Real.exp (w / 2) * scaledBumpDecay w := by
    have := bumpDecayConstant_nonneg (scaledBump w); positivity
  have hd : (1 + c) ^ 2 ≤ (1 + (z.im + c)) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : ‖paperFT (scaledBump w) (-(I * conj z) - c)‖ ≤
      Real.exp (w / 2) * scaledBumpDecay w / (1 + c) ^ 2 :=
    h.trans (div_le_div_of_nonneg_left hB (by positivity) hd)
  calc ‖paperFT (scaledBump w) (-(I * conj z) - c)‖ ^ 2
      ≤ (Real.exp (w / 2) * scaledBumpDecay w / (1 + c) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = _ := by rw [div_pow, ← pow_mul]

/-- **Nearby coefficients are coherent.** For two zeros `½ + z₁`, `½ + z₂` in the upper half plane
with `|h_w(−iz₁ − c)| ≥ H₀ > 0`, `(e^{w/2}B_w)²/(1 + c)⁴ ≤ H₀²/16` and
`8w e^{w/2} J_w |z₂ − z₁| ≤ H₀`, `w|z₂ − z₁| ≤ 1`: `Re(D_c(z₂) conj D_c(z₁)) ≥ 0`. -/
theorem re_evenCoeff_mul_conj_nonneg {w : ℝ} (hw : 0 < w) {c : ℝ} (hc : 0 ≤ c) {z₁ z₂ : ℂ}
    (hz₁ : (1 / 2 + z₁) ∈ zetaZeroConfig.carrier) (hz₂ : (1 / 2 + z₂) ∈ zetaZeroConfig.carrier)
    (him₁ : 0 ≤ z₁.im) (him₂ : 0 ≤ z₂.im) {H₀ : ℝ} (hH₀ : 0 < H₀)
    (hh₁ : H₀ ≤ ‖paperFT (scaledBump w) (-(I * z₁) - c)‖)
    (hK : (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + c) ^ 4 ≤ H₀ ^ 2 / 16)
    (hL : 8 * w * Real.exp (w / 2) * bumpMass w * ‖z₂ - z₁‖ ≤ H₀) (hwz : w * ‖z₂ - z₁‖ ≤ 1) :
    0 ≤ (evenCoeff zetaZeroConfig (modScaledBump w c) z₂ *
      conj (evenCoeff zetaZeroConfig (modScaledBump w c) z₁)).re := by
  have hstrip : ∀ z, (1 / 2 + z) ∈ zetaZeroConfig.carrier → |z.re| ≤ 1 / 2 := fun z hz => by
    have := zetaZeroConfig.strip _ hz
    have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  rw [evenCoeff_modScaledBump_eq_mult_mul hw c hz₁, evenCoeff_modScaledBump_eq_mult_mul hw c hz₂]
  set h₁ := paperFT (scaledBump w) (-(I * z₁) - c) with hh₁def
  set h₂ := paperFT (scaledBump w) (-(I * z₂) - c) with hh₂def
  set ε₁ := conj (paperFT (scaledBump w) (-(I * conj z₁) - c) ^ 2) with hε₁
  set ε₂ := conj (paperFT (scaledBump w) (-(I * conj z₂) - c) ^ 2) with hε₂
  have hdiff : ‖h₂ - h₁‖ ≤ ‖h₁‖ / 4 := by
    have hxy : w * ‖(-(I * z₂) - (c : ℂ)) - (-(I * z₁) - c)‖ ≤ 1 := by
      rw [show (-(I * z₂) - (c : ℂ)) - (-(I * z₁) - c) = -I * (z₂ - z₁) by ring, norm_mul,
        norm_neg, Complex.norm_I, one_mul]
      exact hwz
    have hy : |(-(I * z₁) - (c : ℂ)).im| ≤ 1 / 2 := by simpa using hstrip z₁ hz₁
    have h := norm_paperFT_scaledBump_sub_le hw hxy hy
    rw [show (-(I * z₂) - (c : ℂ)) - (-(I * z₁) - c) = -I * (z₂ - z₁) by ring, norm_mul,
      norm_neg, Complex.norm_I, one_mul] at h
    have : 2 * w * Real.exp (w / 2) * bumpMass w * ‖z₂ - z₁‖ ≤ H₀ / 4 := by linarith
    linarith
  have hH1 : H₀ ^ 2 ≤ ‖h₁‖ ^ 2 := pow_le_pow_left₀ hH₀.le hh₁ 2
  have he₁ : ‖ε₁‖ ≤ ‖h₁‖ ^ 2 / 16 :=
    ((norm_reflected_le hw hc him₁ (hstrip z₁ hz₁)).trans hK).trans (by linarith)
  have he₂ : ‖ε₂‖ ≤ ‖h₁‖ ^ 2 / 16 :=
    ((norm_reflected_le hw hc him₂ (hstrip z₂ hz₂)).trans hK).trans (by linarith)
  have hcoh := re_coherent_squares_nonneg hdiff he₁ he₂
  have e : (zetaZeroConfig.mult (1 / 2 + z₂) : ℂ) * (h₂ ^ 2 + ε₂) *
      conj ((zetaZeroConfig.mult (1 / 2 + z₁) : ℂ) * (h₁ ^ 2 + ε₁)) =
      (((zetaZeroConfig.mult (1 / 2 + z₂) * zetaZeroConfig.mult (1 / 2 + z₁) : ℕ) : ℝ) : ℂ) *
        ((h₂ ^ 2 + ε₂) * conj (h₁ ^ 2 + ε₁)) := by
    rw [map_mul, Complex.conj_natCast]; push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg _) hcoh

/-- **Coherent neighbours add.** If `Re(D₂ D̄₁) ≥ 0`, `|K(x₂) − t| ≤ 2εV t` with `t = K(θ) > 0` real
and `2εV |D₂| ≤ |D₁|/2`, then `|D₁ t + D₂ K(x₂)| ≥ |D₁| t/2`. -/
theorem norm_coherent_pair_ge {D₁ D₂ K₂ : ℂ} {t εV : ℝ} (ht : 0 ≤ t)
    (hre : 0 ≤ (D₂ * conj D₁).re) (hK : ‖K₂ - t‖ ≤ 2 * εV * t)
    (hsmall : 2 * εV * ‖D₂‖ ≤ ‖D₁‖ / 2) :
    ‖D₁‖ * t / 2 ≤ ‖D₁ * t + D₂ * K₂‖ := by
  have h1 : ‖D₁‖ ≤ ‖D₁ + D₂‖ := norm_le_norm_add_of_re_mul_conj_nonneg hre
  have e : D₁ * t + D₂ * K₂ = (D₁ + D₂) * t + D₂ * (K₂ - t) := by ring
  rw [e]
  have h2 : ‖(D₁ + D₂) * (t : ℂ)‖ = ‖D₁ + D₂‖ * t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have h3 : ‖D₂ * (K₂ - t)‖ ≤ ‖D₂‖ * (2 * εV * t) := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hK (norm_nonneg _)
  have h4 := norm_sub_norm_le ((D₁ + D₂) * (t : ℂ)) (-(D₂ * (K₂ - t)))
  rw [sub_neg_eq_add, norm_neg, h2] at h4
  have h5 : ‖D₂‖ * (2 * εV * t) ≤ ‖D₁‖ / 2 * t := by
    have := mul_le_mul_of_nonneg_right hsmall ht; linarith
  have h6 : ‖D₁‖ * t ≤ ‖D₁ + D₂‖ * t := mul_le_mul_of_nonneg_right h1 ht
  linarith

/-! ### Isolated twins -/

/-- For real `θ`, `K_k(θ)` is the nonnegative real number `|K_k(θ)|`. -/
theorem fejerPowWin_ofReal_eq_norm {V : ℝ} (hV : 0 ≤ V) (k : ℕ) (θ : ℝ) :
    fejerPowWin k V θ = ((‖fejerPowWin k V θ‖ : ℝ) : ℂ) := by
  have hreal : fejerPowWin k V θ =
      ((∫ u in (0 : ℝ)..V, Real.sin (π * u / V) ^ (2 * k) * Real.exp (θ * u) : ℝ) : ℂ) := by
    rw [fejerPowWin, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun u _ => ?_
    push_cast; rfl
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..V, Real.sin (π * u / V) ^ (2 * k) * Real.exp (θ * u) :=
    intervalIntegral.integral_nonneg hV fun u _ => mul_nonneg (sin_pow_nonneg _ k) (Real.exp_pos _).le
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]

/-- `D(z̄) = conj D(z)`. -/
theorem evenCoeff_conj (Z : ZeroConfig) (b : ℝ → ℂ) (z : ℂ) :
    evenCoeff Z b (conj z) = conj (evenCoeff Z b z) := by
  rw [evenCoeff, evenCoeff, Complex.conj_conj, map_add, Complex.conj_conj, add_comm]

/-- **A loud coefficient has a large transform.** For a zero `½ + y`, `Im y ≥ 0`, `|Im y| ≤ Γ'`,
`|D_c(y)| ≥ ε₀`, `c ≥ 0` and `H₀² ≤ ε₀/(40 log(180Γ')) − (e^{w/2}B_w)²/(1 + c)⁴`:
`|h_w(−iy − c)| ≥ H₀`. -/
theorem le_norm_paperFT_of_loud {w : ℝ} (hw : 0 < w) {c : ℝ} (hc : 0 ≤ c) {y : ℂ}
    (hy : (1 / 2 + y) ∈ zetaZeroConfig.carrier) (him : 0 ≤ y.im) {Γ' ε₀ H₀ : ℝ}
    (hΓ' : |y.im| ≤ Γ')
    (hD : ε₀ ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w c) y‖)
    (hH : H₀ ^ 2 ≤ ε₀ / (40 * Real.log (180 * Γ')) -
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + c) ^ 4) :
    H₀ ≤ ‖paperFT (scaledBump w) (-(I * y) - c)‖ := by
  have hstrip := zetaZeroConfig.strip _ hy
  have hre : |y.re| ≤ 1 / 2 := by
    have e : (1 / 2 + y).re = 1 / 2 + y.re := by simp
    rw [abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
  have h4 : 4 ≤ |(1 / 2 + y).im| := four_le_abs_im_of_mem_zetaCarrier hy
  have him' : (1 / 2 + y).im = y.im := by simp
  rw [him'] at h4
  have hm := mult_le_log_zeta hy
  rw [him'] at hm
  have hmΓ : (zetaZeroConfig.mult (1 / 2 + y) : ℝ) ≤ 40 * Real.log (180 * Γ') :=
    hm.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) (by norm_num))
  have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult (1 / 2 + y) := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ hy
  have hdec := evenCoeff_modScaledBump_eq_mult_mul hw c hy
  set h := paperFT (scaledBump w) (-(I * y) - c) with hh
  set ε := conj (paperFT (scaledBump w) (-(I * conj y) - c) ^ 2) with hε
  have hεn := norm_reflected_le hw hc him hre
  rw [← hε] at hεn
  have hDn : ‖evenCoeff zetaZeroConfig (modScaledBump w c) y‖ ≤
      (zetaZeroConfig.mult (1 / 2 + y) : ℝ) * (‖h‖ ^ 2 + ‖ε‖) := by
    rw [hdec, norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (le_of_eq ?_)) (Nat.cast_nonneg _)
    rw [norm_pow]
  have hL : 0 < 40 * Real.log (180 * Γ') := lt_of_lt_of_le (by norm_num) hm1 |>.trans_le hmΓ
  have h1 : ε₀ / (40 * Real.log (180 * Γ')) ≤ ‖h‖ ^ 2 + ‖ε‖ := by
    rw [div_le_iff₀ hL]
    have := hD.trans hDn
    have h2 : (zetaZeroConfig.mult (1 / 2 + y) : ℝ) * (‖h‖ ^ 2 + ‖ε‖) ≤
        40 * Real.log (180 * Γ') * (‖h‖ ^ 2 + ‖ε‖) :=
      mul_le_mul_of_nonneg_right hmΓ (by positivity)
    linarith
  have h2 : H₀ ^ 2 ≤ ‖h‖ ^ 2 := by linarith
  exact le_of_sq_le_sq (by simpa using h2) (norm_nonneg _) |>.trans le_rfl

/-- **Coherence of a record and its near twin, both signs.** For two zeros `½ + z₁`, `½ + z` of the
family modulated to `c = γ₀ > 0`, with `|Im z₁| ≥ γ₀/2`, `|z − z₁| ≤ 1/2 ≤ γ₀/2`, `|D(z₁)| ≥ ε₀`,
`|Im z₁| ≤ Γ`, `H₀² ≤ ε₀/(40 log(180Γ)) − (e^{w/2}B_w)²/(1 + γ₀)⁴`, `(e^{w/2}B_w)²/(1 + γ₀)⁴ ≤ H₀²/16`,
`8w e^{w/2} J_w |z − z₁| ≤ H₀` and `w|z − z₁| ≤ 1`: `Re(D(z) conj D(z₁)) ≥ 0`. -/
theorem re_twin_mul_conj_nonneg {w : ℝ} (hw : 0 < w) {γ₀ : ℝ} (hγ₀ : 1 ≤ γ₀) {z₁ z : ℂ}
    (hz₁ : (1 / 2 + z₁) ∈ zetaZeroConfig.carrier) (hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier)
    (hlow : γ₀ / 2 ≤ |z₁.im|) (hzz : ‖z - z₁‖ ≤ 1 / 2) {Γ ε₀ H₀ : ℝ} (hH₀ : 0 < H₀)
    (hup : |z₁.im| ≤ Γ) (hD : ε₀ ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w γ₀) z₁‖)
    (hH : H₀ ^ 2 ≤ ε₀ / (40 * Real.log (180 * Γ)) -
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + γ₀) ^ 4)
    (hK : (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + γ₀) ^ 4 ≤ H₀ ^ 2 / 16)
    (hL : 8 * w * Real.exp (w / 2) * bumpMass w * ‖z - z₁‖ ≤ H₀) (hwz : w * ‖z - z₁‖ ≤ 1) :
    0 ≤ (evenCoeff zetaZeroConfig (modScaledBump w γ₀) z *
      conj (evenCoeff zetaZeroConfig (modScaledBump w γ₀) z₁)).re := by
  have hc : (0 : ℝ) ≤ γ₀ := by linarith
  have hconjmem : ∀ y, (1 / 2 + y) ∈ zetaZeroConfig.carrier →
      (1 / 2 + conj y) ∈ zetaZeroConfig.carrier := fun y hy => by
    have := conj_mem_zetaZeroConfig hy
    have e : conj (1 / 2 + y) = 1 / 2 + conj y := by apply Complex.ext <;> simp
    rwa [e] at this
  have himz : |z.im - z₁.im| ≤ 1 / 2 := by
    have := Complex.abs_im_le_norm (z - z₁); rw [Complex.sub_im] at this; linarith
  rcases le_or_gt 0 z₁.im with hpos | hneg
  · -- the record in the upper half plane
    have him₁ : 0 ≤ z₁.im := hpos
    have him : 0 ≤ z.im := by
      rw [abs_of_nonneg hpos] at hlow; rw [abs_le] at himz; linarith
    have hh₁ := le_norm_paperFT_of_loud hw hc hz₁ him₁ hup hD hH
    exact re_evenCoeff_mul_conj_nonneg hw hc hz₁ hz him₁ him hH₀ hh₁ hK hL hwz
  · -- the record in the lower half plane: pass to the conjugates
    have him₁ : 0 ≤ (conj z₁).im := by rw [Complex.conj_im]; linarith
    have him : 0 ≤ (conj z).im := by
      rw [Complex.conj_im]; rw [abs_of_neg hneg] at hlow; rw [abs_le] at himz; linarith
    have hD' : ε₀ ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w γ₀) (conj z₁)‖ := by
      rw [evenCoeff_conj, Complex.norm_conj]; exact hD
    have hup' : |(conj z₁).im| ≤ Γ := by rw [Complex.conj_im, abs_neg]; exact hup
    have hzz' : ‖conj z - conj z₁‖ = ‖z - z₁‖ := by rw [← map_sub, Complex.norm_conj]
    have hh₁ := le_norm_paperFT_of_loud hw hc (hconjmem z₁ hz₁) him₁ hup' hD' hH
    have h := re_evenCoeff_mul_conj_nonneg hw hc (hconjmem z₁ hz₁) (hconjmem z hz) him₁ him hH₀
      hh₁ hK (by rw [hzz']; exact hL) (by rw [hzz']; exact hwz)
    rw [evenCoeff_conj, evenCoeff_conj, Complex.conj_conj, show conj (evenCoeff zetaZeroConfig
      (modScaledBump w γ₀) z) * evenCoeff zetaZeroConfig (modScaledBump w γ₀) z₁ =
      conj (evenCoeff zetaZeroConfig (modScaledBump w γ₀) z *
        conj (evenCoeff zetaZeroConfig (modScaledBump w γ₀) z₁)) by
      rw [map_mul, Complex.conj_conj], Complex.conj_re] at h
    exact h

/-- The final arithmetic: a record term `≥ u(e − 1)V^{2k+1}/(2Q)` against a noise
`≤ u X (e − 1)/r^{2k+1}` forces `(Vr)^{2k+1} ≤ 2XQ`. -/
theorem quiet_record_arith {D t u X Q V r : ℝ} {k : ℕ} (hD : 0 < D) (hu : 0 < u) (hQ : 0 < Q)
    (hr : 0 < r)
    (ht : u * (Real.exp 1 - 1) * V ^ (2 * k + 1) / Q ≤ t)
    (h : D * t / 2 ≤ u * ((4 / 3) ^ k * (X * (D * (Real.exp 1 - 1))) / r ^ (2 * k + 1))) :
    (V * r) ^ (2 * k + 1) ≤ 2 * ((4 / 3) ^ k * X) * Q := by
  have he1 : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have hr0 : 0 < r ^ (2 * k + 1) := by positivity
  have h1 : D * (u * (Real.exp 1 - 1) * V ^ (2 * k + 1) / Q) / 2 ≤
      u * ((4 / 3) ^ k * (X * (D * (Real.exp 1 - 1))) / r ^ (2 * k + 1)) :=
    le_trans (by gcongr) h
  have e1 : D * (u * (Real.exp 1 - 1) * V ^ (2 * k + 1) / Q) / 2 =
      (u * D * (Real.exp 1 - 1)) * (V ^ (2 * k + 1) / (2 * Q)) := by ring
  have e2 : u * ((4 / 3) ^ k * (X * (D * (Real.exp 1 - 1))) / r ^ (2 * k + 1)) =
      (u * D * (Real.exp 1 - 1)) * ((4 / 3) ^ k * X / r ^ (2 * k + 1)) := by ring
  rw [e1, e2] at h1
  have h2 := le_of_mul_le_mul_left h1 (by positivity)
  rw [div_le_div_iff₀ (by positivity) hr0] at h2
  rw [mul_pow]; linarith

/-- The tightness radius `ε_b = (4/3) A_w log(180(Γ + 6))(4 + 2π(k + 1))/(3^k V)` of
`zeta_near_top_twin_tight_or_triple`. -/
def twinTightRadius (w γ₀ V : ℝ) (k : ℕ) : ℝ :=
  4 / 3 * twinTightConstant w * Real.log (180 * (recordHeightEnvelope w γ₀ + 6)) *
    (4 + 2 * π * (k + 1)) / (3 ^ k * V)

/-- **Isolated twins of `ζ` cannot hide.** Under the hypotheses of
`zeta_near_top_twin_tight_or_triple`, let `ε_b = twinTightRadius w γ₀ V k`, `2/V ≤ r`, `H₀ > 0` with
`H₀² ≤ (a_w²/(2e))/(40 log(180Γ)) − (e^{w/2}B_w)²/(1 + γ₀)⁴`, `(e^{w/2}B_w)²/(1 + γ₀)⁴ ≤ H₀²/16`,
`ε_b V ≤ 1`, `w ε_b ≤ 1`, `8w e^{w/2} J_w ε_b ≤ H₀`, `4 ε_b V · 80 log(180(Γ + 1))(e^{w/2}B_w)² ≤ a_w²/(2e)`
and `2(4/3)^k A_w log(180(Γ + 6))(1 + 4π²k²)^k < (Vr)^{2k+1}`. If the difference tests of the bump
modulated to `γ₀` are Weil nonnegative on `[0, V]`, the Legendre record has two other zeros within
`2r`: a hiding near-top record needs at least a triple. -/
theorem zeta_isolated_twins_cannot_hide {w V : ℝ} (hw : 0 < w) (hV : 0 < V) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re)
    (hVlag : hidingLag w z₀ ≤ V) {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hrδ : r + 4 / V ≤ z₀.re / 2)
    (hVR : 2 * (twinRadiusNumerator w z₀.im + uniformTwinDepth w) ≤ V * r)
    (hVk : 2 * (4 + 2 * π * (k + 1)) ≤ V * r) (h2V : 2 / V ≤ r) {H₀ : ℝ} (hH₀ : 0 < H₀)
    (hH : H₀ ^ 2 ≤ centerAmplitude w ^ 2 / (2 * Real.exp 1) /
        (40 * Real.log (180 * recordHeightEnvelope w z₀.im)) -
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4)
    (hK : (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4 ≤ H₀ ^ 2 / 16)
    (hεV : twinTightRadius w z₀.im V k * V ≤ 1) (hεw : w * twinTightRadius w z₀.im V k ≤ 1)
    (hεL : 8 * w * Real.exp (w / 2) * bumpMass w * twinTightRadius w z₀.im V k ≤ H₀)
    (hεD : 4 * twinTightRadius w z₀.im V k * V * (80 * Real.log (180 * (recordHeightEnvelope w z₀.im + 1)) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2) ≤ centerAmplitude w ^ 2 / (2 * Real.exp 1))
    (hquiet : 2 * ((4 / 3) ^ k * (twinTightConstant w *
      Real.log (180 * (recordHeightEnvelope w z₀.im + 6)))) * (1 + 4 * π ^ 2 * (k : ℕ) ^ 2) ^ k <
      (V * r) ^ (2 * k + 1)) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧
      ∃ z z', z ≠ z₁ ∧ z' ≠ z₁ ∧ z ≠ z' ∧
        evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 ∧
        evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z' ≠ 0 ∧
        ‖z - z₁‖ < 2 * r ∧ ‖z' - z₁‖ < 2 * r := by
  classical
  obtain ⟨z₁, hz₁, hre₁, hlow, hup, hD₁, hrec, H⟩ :=
    zeta_near_top_twin_tight_or_triple hw hV hz₀ hre₀ hTw htop hm hVlag hk hr hr1 hrδ hVR hVk
  refine ⟨z₁, hz₁, ?_⟩
  rcases H with htrip | ⟨z, hz, hDz, hzz⟩
  · exact htrip
  set D := evenCoeff zetaZeroConfig (modScaledBump w z₀.im) with hDdef
  set εb := twinTightRadius w z₀.im V k with hεb
  replace hzz : ‖z - z₁‖ ≤ εb := by rw [hεb, twinTightRadius]; exact hzz
  have hεb1V : εb ≤ 1 / V := by rw [le_div_iff₀ hV]; exact hεV
  have hεbr : εb ≤ r / 2 := by
    have : 1 / V ≤ r / 2 := by rw [div_le_iff₀ hV]; rw [div_le_iff₀ hV] at h2V; linarith
    linarith
  by_contra hno
  -- isolation of the pair
  have hiso2 : ∀ z', z' ≠ z₁ → z' ≠ z → D z' ≠ 0 → 2 * r ≤ ‖z' - z₁‖ := by
    intro z' h1 h2 h3
    by_contra h; push Not at h
    exact hno ⟨z, z', hz, h1, fun e => h2 e.symm, hDz, h3, by linarith, h⟩
  -- the cluster law for the pair at depth one
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hπk0 : 0 ≤ π * (k + 1) := mul_nonneg Real.pi_pos.le (by positivity)
  have hVrV : V * r ≤ V := mul_le_of_le_one_right hV.le hr1
  have hπk : π * k ≤ V := by nlinarith [Real.pi_pos]
  have h4πk : 4 * π * k ≤ V * r := by nlinarith [Real.pi_pos]
  have hrσ : r ≤ z₁.re - 1 / V := by
    have : 1 / V ≤ 4 / V := div_le_div_of_nonneg_right (by norm_num) hV.le
    linarith
  have hσ : 0 < z₁.re - 1 / V := lt_of_lt_of_le hr hrσ
  set s : ℂ := ((z₁.re - 1 / V : ℝ) : ℂ) + z₁.im * I with hs
  have hθ : z₁ - s = ((1 / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
  have hz₁s : ‖z₁ - s‖ = 1 / V := by
    rw [hθ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1Vr : 1 / V ≤ r / 2 := by rw [div_le_iff₀ hV]; rw [div_le_iff₀ hV] at h2V; linarith
  have hisoS : ∀ y, y ∉ ({z₁, z} : Finset ℂ) → D y ≠ 0 → r ≤ ‖y - ((z₁.re - 1 / V : ℝ) + z₁.im * I)‖ := by
    intro y hy hDy
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    have h1 := hiso2 y hy.1 hy.2 hDy
    have h2 := norm_sub_le_norm_sub_add_norm_sub y s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h2
    rw [← hs]; linarith
  have hcl := zeta_powCluster_le (contDiff_modScaledBump_two w _) (modScaledBump_support hw _) hk hπk
    hm hz₁ hrec (κ := 1) one_pos hσ hr (by linarith) h4πk {z₁, z} hisoS
  rw [Finset.sum_pair hz.symm, ← hs] at hcl
  set M : ℝ := 2 * (lagStructure zetaZeroConfig (modScaledBump w z₀.im) 0).re with hM
  set W : ℝ := ∑' y : ℂ, ‖D y‖ with hW
  set L : ℝ := Real.log (180 * (|z₁.im| + 6)) with hL
  have hW0 : 0 ≤ W := tsum_nonneg fun y => norm_nonneg _
  have hL0 : 0 ≤ L := Real.log_nonneg (by have := abs_nonneg z₁.im; linarith only [this])
  have hbr := clusterBracket_le (j := k) hk (M := M) (W := W) (D := ‖D z₁‖) (κ := 1) z₁.im hW0
    (norm_nonneg _) hr hr1 hrσ
  rw [← hL] at hbr
  have hpos₀ : 0 < z₀.im := lt_of_lt_of_le (by unfold nearTopHeight; positivity) hTw
  have hMW := mass_le_of_record_height hw hpos₀ hlow
  rw [← hL] at hMW
  have hΞ := xi_ratio_le hw le_rfl hD₁ hL0 hMW
  set u : ℝ := (2 * k).factorial * (π / V) ^ (2 * k) with hu
  have hu0 : 0 < u := by
    rw [hu]; exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (div_pos Real.pi_pos hV) _)
  have hnoise : ‖D z₁ * fejerPowWin k V (z₁ - s) + D z * fejerPowWin k V (z - s)‖ ≤
      u * ((4 / 3) ^ k * (twinTightConstant w * L * (‖D z₁‖ * (Real.exp 1 - 1))) / r ^ (2 * k + 1)) := by
    refine hcl.trans ?_
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) (hbr.trans ?_)) hu0.le
    · rfl
    · have hr0 : 0 < r ^ (2 * k + 1) := by positivity
      have hc0 : (0 : ℝ) ≤ (4 / 3) ^ k := by positivity
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΞ hc0) hr0.le
  -- the pair adds up
  set t : ℝ := ‖fejerPowWin k V ((1 / V : ℝ) : ℂ)‖ with ht
  have hKθ : fejerPowWin k V (z₁ - s) = (t : ℂ) := by
    rw [hθ, ht]; exact fejerPowWin_ofReal_eq_norm hV.le k _
  have hzz1 : ‖(z - s) - ((1 / V : ℝ) : ℂ)‖ = ‖z - z₁‖ := by
    rw [← hθ]; congr 1; ring
  have hKpert : ‖fejerPowWin k V (z - s) - t‖ ≤ 2 * (‖z - z₁‖ * V) * t := by
    have h := norm_fejerPowWin_sub_ofReal_le hV.le k (1 / V) (x := z - s)
      (by rw [hzz1]; exact le_trans (mul_le_mul_of_nonneg_right hzz hV.le) hεV)
    have hKr : fejerPowWin k V ((1 / V : ℝ) : ℂ) = (t : ℂ) := fejerPowWin_ofReal_eq_norm hV.le k _
    rw [hzz1, hKr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
    calc ‖fejerPowWin k V (z - s) - t‖ ≤ 2 * ‖z - z₁‖ * V * t := h
      _ = 2 * (‖z - z₁‖ * V) * t := by ring
  have hmem : ∀ x : ℂ, D x ≠ 0 → (1 / 2 + x) ∈ zetaZeroConfig.carrier := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · exact h
    · have := conj_mem_zetaZeroConfig h
      have e : conj (1 / 2 + conj x) = 1 / 2 + x := by apply Complex.ext <;> simp
      rwa [e] at this
  have hγ₀1 : 1 ≤ z₀.im := le_trans (by
    unfold nearTopHeight
    have : 0 ≤ 700000 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2 := by
      positivity
    linarith) hTw
  have hre := re_twin_mul_conj_nonneg hw hγ₀1 (hmem z₁ hz₁) (hmem z hDz) hlow
    (by linarith) hH₀ hup hD₁ hH hK
    (le_trans (mul_le_mul_of_nonneg_left hzz (mul_nonneg (by positivity)
      (integral_nonneg fun u => abs_nonneg _))) hεL)
    (le_trans (mul_le_mul_of_nonneg_left hzz hw.le) hεw)
  have hDzmax : ‖D z‖ ≤ 80 * Real.log (180 * (recordHeightEnvelope w z₀.im + 1)) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := by
    refine (norm_evenCoeff_modScaledBump_le_log hw z₀.im hDz).trans ?_
    have h4 := four_le_abs_im_of_evenCoeff_zeta hDz
    have himz : |z.im| ≤ |z₁.im| + 1 := by
      have := Complex.abs_im_le_norm (z - z₁); rw [Complex.sub_im] at this
      have := abs_sub_abs_le_abs_sub z.im z₁.im
      linarith
    have : Real.log (180 * |z.im|) ≤ Real.log (180 * (recordHeightEnvelope w z₀.im + 1)) :=
      Real.log_le_log (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num)) (by positivity)
  have hsmall : 2 * (‖z - z₁‖ * V) * ‖D z‖ ≤ ‖D z₁‖ / 2 := by
    have h1 : 2 * (‖z - z₁‖ * V) * ‖D z‖ ≤ 2 * (εb * V) * (80 * Real.log (180 *
        (recordHeightEnvelope w z₀.im + 1)) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2) := by
      have hεV0 : 0 ≤ ‖z - z₁‖ * V := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hzz hV.le)
        (by norm_num)) hDzmax (norm_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg ((norm_nonneg _).trans hzz) hV.le))
    linarith
  have hpair := norm_coherent_pair_ge (norm_nonneg _) hre hKpert hsmall
  rw [← hKθ] at hpair
  -- the record term
  have hlow' : u * (Real.exp 1 - 1) * V ^ (2 * k + 1) / (1 + 4 * π ^ 2 * (k : ℕ) ^ 2) ^ k ≤ t := by
    refine le_trans (le_of_eq ?_) (norm_fejerPowWin_ofReal_ge hV k (show 0 < 1 / V by positivity))
    have hVne : V ≠ 0 := hV.ne'
    have e : (1 / V) ^ 2 + (2 * π * (k : ℝ) / V) ^ 2 = (1 + 4 * π ^ 2 * (k : ℕ) ^ 2) / V ^ 2 := by
      field_simp; ring
    rw [e, show 1 / V * V = 1 by field_simp, hu, div_pow, div_pow, ← pow_mul V 2 k, pow_succ]
    field_simp
  have hQ0 : 0 < (1 + 4 * π ^ 2 * ((k : ℕ) : ℝ) ^ 2) ^ k := by positivity
  have hfin := quiet_record_arith (norm_pos_iff.mpr hz₁) hu0 hQ0 hr hlow' (hpair.trans hnoise)
  have hLL : L ≤ Real.log (180 * (recordHeightEnvelope w z₀.im + 6)) := by
    rw [hL]; exact Real.log_le_log (by positivity) (by linarith only [hup])
  have hA0 := twinTightConstant_nonneg hw
  have h3 : 2 * ((4 / 3) ^ k * (twinTightConstant w * L)) * (1 + 4 * π ^ 2 * ((k : ℕ) : ℝ) ^ 2) ^ k ≤
      2 * ((4 / 3) ^ k * (twinTightConstant w *
        Real.log (180 * (recordHeightEnvelope w z₀.im + 6)))) * (1 + 4 * π ^ 2 * ((k : ℕ) : ℝ) ^ 2) ^ k := by
    gcongr
  linarith only [hfin, h3, hquiet]

end GaloisForLFunctions.SquareRootThreshold
