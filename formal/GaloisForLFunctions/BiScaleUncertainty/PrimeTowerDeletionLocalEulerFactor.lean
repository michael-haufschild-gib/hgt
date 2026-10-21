import GaloisForLFunctions.BiScaleUncertainty.PrimePowerDeletionPriceEulerAdditivity

/-!
# Deleting whole prime towers: the blind cone reads the local Euler factors

Delete from the prime-power blind cone every power of the primes in a finite set `P`.

**Theorem.** On the nonnegative combinations blind at every prime power whose prime is not in `P`,
the normalized deviation `(A − W)/‖c‖²` lies in the open interval

`(−Σ_{p∈P} 2 log p/(√p + 1),  Σ_{p∈P} 2 log p/(√p − 1))`,

both ends are approached and neither is attained (`isGLB_towerDeviations`, `isLUB_towerDeviations`,
`towerDeviations_subset_Ioo`). Each end is the sum over `p ∈ P` of an extreme value of the local
factor `t ↦ 2 Re(−ζ_p'/ζ_p)(½ + it)`, `ζ_p(s) = (1 − p^{−s})^{−1}`, on the critical line.

**Mechanism.**
* *Spectral identity* (`integral_spectral_mul_eulerSymbol`). For every combination and every
  integer `q ≥ 2`, `π Σ_{k≥1} L_{q^k}(c) = ∫ G_c(r) S_x(r log q) dr` with `x = q^{−1/2}` and the
  Poisson symbol `S_x(θ) = Σ_{k≥1} x^k cos kθ = (x cos θ − x²)/(1 − 2x cos θ + x²)`; the node values
  vanish beyond the support, so the series on the left is a finite sum. Since
  `log q · 2S_x(t log q) = 2 Re(−ζ_q'/ζ_q)(½ + it)` for a prime `q`, the tower reads the local
  Euler factor on the critical line.
* *Bounds* (`tower_sum_bounds`). `−x/(1+x) ≤ S_x ≤ x/(1−x)` and `G_c ≥ 0` give
  `−2/(√q+1) ‖c‖² ≤ Σ_k L_{q^k}(c) ≤ 2/(√q−1) ‖c‖²` for every nonnegative combination, with no
  blindness assumption at all.
* *Sharpness.* The divisor train `Σ_{d ∣ M} σ^{Ω(d)} b(u − log d)`, `M = Π_{p∈P} p^{N−1}`, has
  phase density a product of Fejér kernels; its deviation is
  `Σ_p log p Σ_{k<N} 2(σ/√p)^k (1 − k/N)`, which tends to `Σ_p 2σ log p/(√p − σ)`.

Compared with a single node (`Λ(p)/√p`, `PrimePowerNodeDeletionPrice`) and the pair `{p, p²}`
(`PrimePowerTowerDeletionInteraction`), the whole tower costs `2 log p/(√p+1)` from below and
`2 log p/(√p−1)` from above; summed over all primes both diverge, as `ζ'/ζ` is unbounded on the
critical line.
-/

open MeasureTheory Set Complex Finsupp Filter Topology
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped ComplexConjugate Real

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. The Poisson symbol -/

/-- The Poisson symbol `S_x(θ) = Σ_{k≥1} x^k cos kθ`. -/
def eulerSymbol (x θ : ℝ) : ℝ := (x * Real.cos θ - x ^ 2) / (1 - 2 * x * Real.cos θ + x ^ 2)

theorem eulerSymbol_denom_pos {x : ℝ} (hx1 : x < 1) (θ : ℝ) (hx0 : 0 ≤ x) :
    0 < 1 - 2 * x * Real.cos θ + x ^ 2 := by
  nlinarith [Real.cos_le_one θ, sq_nonneg (1 - x)]

theorem neg_le_eulerSymbol {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (θ : ℝ) :
    -(x / (1 + x)) ≤ eulerSymbol x θ := by
  have hD := eulerSymbol_denom_pos hx1 θ hx0
  rw [eulerSymbol, neg_le, ← neg_div, div_le_div_iff₀ hD (by linarith)]
  nlinarith [Real.neg_one_le_cos θ, mul_nonneg hx0 (sub_nonneg.mpr hx1.le),
    mul_nonneg (mul_nonneg hx0 (sub_nonneg.mpr hx1.le)) (by linarith [Real.neg_one_le_cos θ] :
      (0 : ℝ) ≤ 1 + Real.cos θ)]

theorem eulerSymbol_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (θ : ℝ) :
    eulerSymbol x θ ≤ x / (1 - x) := by
  have hD := eulerSymbol_denom_pos hx1 θ hx0
  rw [eulerSymbol, div_le_div_iff₀ hD (by linarith)]
  nlinarith [Real.cos_le_one θ, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 1 + x),
    mul_nonneg (mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 1 + x))
      (by linarith [Real.cos_le_one θ] : (0 : ℝ) ≤ 1 - Real.cos θ)]

/-- The geometric series of the Poisson symbol. -/
theorem hasSum_eulerSymbol {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (θ : ℝ) :
    HasSum (fun k : ℕ => x ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ)) (eulerSymbol x θ) := by
  set z : ℂ := (x : ℂ) * Complex.exp (θ * Complex.I) with hz
  have hnorm : ‖z‖ < 1 := by
    rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx0]
    exact hx1
  have h := Complex.hasSum_re ((hasSum_geometric_of_norm_lt_one hnorm).mul_left z)
  have hterm : ∀ k : ℕ, (z * z ^ k).re = x ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
    intro k
    rw [← pow_succ', hz, mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow,
      show ((k + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I) = (((k + 1 : ℕ) : ℝ) * θ : ℝ) * Complex.I by
        push_cast; ring, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hre : (z * (1 - z)⁻¹).re = eulerSymbol x θ := by
    have hzr : z.re = x * Real.cos θ := by
      rw [hz, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    have hzi : z.im = x * Real.sin θ := by
      rw [hz, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    rw [← div_eq_mul_inv, Complex.div_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, hzr, hzi, eulerSymbol]
    have hs := Real.sin_sq_add_cos_sq θ
    have hD : (1 - x * Real.cos θ) * (1 - x * Real.cos θ) + (0 - x * Real.sin θ) * (0 - x * Real.sin θ) =
        1 - 2 * x * Real.cos θ + x ^ 2 := by linear_combination x ^ 2 * hs
    rw [hD, ← add_div]
    congr 1
    linear_combination -(x ^ 2) * hs
  simp only [hterm, hre] at h
  exact h

/-! ### 2. The spectral identity of a tower -/

theorem sqrt_natCast_pow (q k : ℕ) : Real.sqrt ((q ^ k : ℕ) : ℝ) = Real.sqrt q ^ k := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) k), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_pow]

theorem two_le_pow_succ {q : ℕ} (hq : 2 ≤ q) (k : ℕ) : 2 ≤ q ^ (k + 1) :=
  le_trans hq (Nat.le_self_pow (by omega) q)

/-- The node value at `q^{k+1}` through the spectral density. -/
theorem integral_spectral_mul_cos_eq_nodeAt (c : WeilTestFn →₀ ℝ) {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    ∫ r, combinationSpectralDensity c r * Real.cos (((k + 1 : ℕ) : ℝ) * (r * Real.log q)) =
      π * Real.sqrt q ^ (k + 1) * nodeAt c (q ^ (k + 1)) := by
  rw [nodeAt, dif_pos (two_le_pow_succ hq k), ← sqrt_natCast_pow,
    ← integral_combinationSpectralDensity_mul_cos_pow c hq (j := k + 1) (by omega)]
  congr 1; funext r; congr 2; ring

/-- **The spectral identity of a tower.** If the node values at `q^{k+1}` vanish for `k ≥ K`, then
`π Σ_{k<K} L_{q^{k+1}}(c) = ∫ G_c(r) S_x(r log q) dr` with `x = 1/√q`. -/
theorem integral_spectral_mul_eulerSymbol (c : WeilTestFn →₀ ℝ) {q : ℕ} (hq : 2 ≤ q) {K : ℕ}
    (hK : ∀ k, K ≤ k → nodeAt c (q ^ (k + 1)) = 0) :
    ∫ r, combinationSpectralDensity c r * eulerSymbol (Real.sqrt q)⁻¹ (r * Real.log q) =
      π * ∑ k ∈ Finset.range K, nodeAt c (q ^ (k + 1)) := by
  set x : ℝ := (Real.sqrt q)⁻¹ with hx
  have hsq : 1 < Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast (by omega : 1 < q))
  have hx0 : 0 ≤ x := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ hsq
  set G := combinationSpectralDensity c
  have hG := integrable_combinationSpectralDensity c
  have hGc := continuous_combinationSpectralDensity c
  have hsum := hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun (k : ℕ) r => G r * (x ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * (r * Real.log q))))
    (f := fun r => G r * eulerSymbol x (r * Real.log q))
    (fun k r => |G r| * x ^ (k + 1))
    (fun k => (hGc.mul (continuous_const.mul (Real.continuous_cos.comp
      (continuous_const.mul (continuous_id.mul continuous_const))))).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hx0 _)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (pow_nonneg hx0 _) (Real.abs_cos_le_one _)) (abs_nonneg _))
    (Eventually.of_forall fun r =>
      ((summable_geometric_of_lt_one hx0 hx1).mul_left (|G r| * x)).congr fun k => by ring)
    (by
      have : (fun r => ∑' k : ℕ, |G r| * x ^ (k + 1)) = fun r => |G r| * (x * (1 - x)⁻¹) := by
        funext r
        rw [tsum_mul_left, show (fun k : ℕ => x ^ (k + 1)) = fun k => x * x ^ k from
          funext fun k => pow_succ' x k, tsum_mul_left, tsum_geometric_of_lt_one hx0 hx1]
      rw [this]
      exact hG.abs.mul_const _)
    (Eventually.of_forall fun r => (hasSum_eulerSymbol hx0 hx1 _).mul_left (G r))
  have hterm : ∀ k : ℕ, ∫ r, G r * (x ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * (r * Real.log q))) =
      π * nodeAt c (q ^ (k + 1)) := by
    intro k
    have e : (fun r => G r * (x ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * (r * Real.log q)))) =
        fun r => x ^ (k + 1) * (G r * Real.cos (((k + 1 : ℕ) : ℝ) * (r * Real.log q))) := by
      funext r; ring
    rw [e, integral_const_mul, integral_spectral_mul_cos_eq_nodeAt c hq k, hx, inv_pow]
    have : Real.sqrt q ^ (k + 1) ≠ 0 := pow_ne_zero _ (by linarith)
    field_simp
  simp only [hterm] at hsum
  have hfin : HasSum (fun k : ℕ => π * nodeAt c (q ^ (k + 1)))
      (∑ k ∈ Finset.range K, π * nodeAt c (q ^ (k + 1))) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by
      rw [hK k (by simpa using hk), mul_zero]
  rw [hsum.unique hfin, Finset.mul_sum]

/-! ### 3. The tower bounds -/

theorem inv_sqrt_div_one_add {q : ℝ} (hq : 1 < Real.sqrt q) :
    2 * ((Real.sqrt q)⁻¹ / (1 + (Real.sqrt q)⁻¹)) = 2 / (Real.sqrt q + 1) := by
  have : Real.sqrt q ≠ 0 := by linarith
  field_simp

theorem inv_sqrt_div_one_sub {q : ℝ} (hq : 1 < Real.sqrt q) :
    2 * ((Real.sqrt q)⁻¹ / (1 - (Real.sqrt q)⁻¹)) = 2 / (Real.sqrt q - 1) := by
  have : Real.sqrt q ≠ 0 := by linarith
  have : Real.sqrt q - 1 ≠ 0 := by linarith
  field_simp

/-- **The tower bounds.** For every nonnegative combination and every integer `q ≥ 2`,
`−2/(√q+1) ‖c‖² ≤ Σ_{k≥1} L_{q^k}(c) ≤ 2/(√q−1) ‖c‖²`. No blindness is assumed. -/
theorem tower_sum_bounds {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) {q : ℕ} (hq : 2 ≤ q) {K : ℕ}
    (hK : ∀ k, K ≤ k → nodeAt c (q ^ (k + 1)) = 0) :
    -(2 / (Real.sqrt q + 1)) * massOf c ≤ ∑ k ∈ Finset.range K, nodeAt c (q ^ (k + 1)) ∧
      ∑ k ∈ Finset.range K, nodeAt c (q ^ (k + 1)) ≤ 2 / (Real.sqrt q - 1) * massOf c := by
  have hsq : 1 < Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast (by omega : 1 < q))
  set x : ℝ := (Real.sqrt q)⁻¹ with hx
  have hx0 : 0 ≤ x := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ hsq
  have hid := integral_spectral_mul_eulerSymbol c hq hK
  have hmass := integral_combinationSpectralDensity c
  have hG := integrable_combinationSpectralDensity c
  have hGn := combinationSpectralDensity_nonneg hc
  have hcont : Continuous fun r : ℝ => eulerSymbol x (r * Real.log q) := by
    have hcos : Continuous fun r : ℝ => Real.cos (r * Real.log q) :=
      Real.continuous_cos.comp (continuous_id.mul continuous_const)
    exact ((continuous_const.mul hcos).sub continuous_const).div
      ((continuous_const.sub (continuous_const.mul hcos)).add continuous_const)
      fun r => (eulerSymbol_denom_pos hx1 _ hx0).ne'
  have hint : Integrable fun r => combinationSpectralDensity c r * eulerSymbol x (r * Real.log q) :=
    hG.mul_bdd (c := max (x / (1 + x)) (x / (1 - x))) hcont.aestronglyMeasurable
      (Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · linarith [neg_le_eulerSymbol hx0 hx1 (r * Real.log q), le_max_left (x / (1 + x)) (x / (1 - x))]
        · linarith [eulerSymbol_le hx0 hx1 (r * Real.log q), le_max_right (x / (1 + x)) (x / (1 - x))])
  have hlow : ∫ r, combinationSpectralDensity c r * (-(x / (1 + x))) ≤
      ∫ r, combinationSpectralDensity c r * eulerSymbol x (r * Real.log q) :=
    integral_mono (hG.mul_const _) hint fun r =>
      mul_le_mul_of_nonneg_left (neg_le_eulerSymbol hx0 hx1 _) (hGn r)
  have hup : ∫ r, combinationSpectralDensity c r * eulerSymbol x (r * Real.log q) ≤
      ∫ r, combinationSpectralDensity c r * (x / (1 - x)) :=
    integral_mono hint (hG.mul_const _) fun r =>
      mul_le_mul_of_nonneg_left (eulerSymbol_le hx0 hx1 _) (hGn r)
  rw [integral_mul_const, hmass, hid] at hlow
  rw [integral_mul_const, hmass, hid] at hup
  rw [← inv_sqrt_div_one_add hsq, ← inv_sqrt_div_one_sub hsq, ← hx]
  constructor <;> nlinarith [Real.pi_pos]

/-! ### 4. Neither bound is attained -/

theorem neg_lt_eulerSymbol {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {θ : ℝ} (hθ : Real.cos θ ≠ -1) :
    -(x / (1 + x)) < eulerSymbol x θ := by
  have hD := eulerSymbol_denom_pos hx1 θ hx0.le
  have hc : 0 < 1 + Real.cos θ := by
    rcases (Real.neg_one_le_cos θ).lt_or_eq with h | h
    · linarith
    · exact absurd h.symm hθ
  rw [eulerSymbol, neg_lt, ← neg_div, div_lt_div_iff₀ hD (by linarith)]
  nlinarith [mul_pos (mul_pos hx0 (sub_pos.mpr hx1)) hc]

theorem eulerSymbol_lt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {θ : ℝ} (hθ : Real.cos θ ≠ 1) :
    eulerSymbol x θ < x / (1 - x) := by
  have hD := eulerSymbol_denom_pos hx1 θ hx0.le
  have hc : 0 < 1 - Real.cos θ := by
    rcases (Real.cos_le_one θ).lt_or_eq with h | h
    · linarith
    · exact absurd h hθ
  rw [eulerSymbol, div_lt_div_iff₀ hD (by linarith)]
  nlinarith [mul_pos (mul_pos hx0 (by linarith : (0 : ℝ) < 1 + x)) hc]

/-- A nonnegative density of positive mass against a weight positive off a countable set. -/
theorem integral_mul_pos_of_pos_off_countable {G φ : ℝ → ℝ} (hG : Integrable G) (hG0 : ∀ r, 0 ≤ G r)
    (hGpos : 0 < ∫ r, G r) (hφ0 : ∀ r, 0 ≤ φ r) {Z : Set ℝ} (hZ : Z.Countable)
    (hφ : ∀ r ∉ Z, 0 < φ r) (hint : Integrable fun r => G r * φ r) : 0 < ∫ r, G r * φ r := by
  rw [integral_pos_iff_support_of_nonneg (fun r => mul_nonneg (hG0 r) (hφ0 r)) hint]
  rw [integral_pos_iff_support_of_nonneg hG0 hG] at hGpos
  calc 0 < volume (Function.support G) := hGpos
    _ = volume (Function.support G \ Z) := (measure_sdiff_null (hZ.measure_zero _)).symm
    _ ≤ volume (Function.support fun r => G r * φ r) :=
        measure_mono fun r ⟨hr, hrZ⟩ => mul_ne_zero hr (hφ r hrZ).ne'

/-- **Strict tower bounds.** For a nonnegative combination of positive mass both tower bounds are
strict: the phase density of a compact combination is a trigonometric polynomial and cannot
concentrate at the extremal phase `π` (resp. `0`). -/
theorem tower_sum_bounds_strict {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (hm : 0 < massOf c)
    {q : ℕ} (hq : 2 ≤ q) {K : ℕ} (hK : ∀ k, K ≤ k → nodeAt c (q ^ (k + 1)) = 0) :
    -(2 / (Real.sqrt q + 1)) * massOf c < ∑ k ∈ Finset.range K, nodeAt c (q ^ (k + 1)) ∧
      ∑ k ∈ Finset.range K, nodeAt c (q ^ (k + 1)) < 2 / (Real.sqrt q - 1) * massOf c := by
  have hsq : 1 < Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast (by omega : 1 < q))
  set x : ℝ := (Real.sqrt q)⁻¹ with hx
  have hx0 : 0 < x := inv_pos.mpr (by linarith)
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ hsq
  have hl : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hid := integral_spectral_mul_eulerSymbol c hq hK
  have hmass := integral_combinationSpectralDensity c
  have hG := integrable_combinationSpectralDensity c
  have hGn := combinationSpectralDensity_nonneg hc
  have hGpos : 0 < ∫ r, combinationSpectralDensity c r := by rw [hmass]; positivity
  have hcont : Continuous fun r : ℝ => eulerSymbol x (r * Real.log q) := by
    have hcos : Continuous fun r : ℝ => Real.cos (r * Real.log q) :=
      Real.continuous_cos.comp (continuous_id.mul continuous_const)
    exact ((continuous_const.mul hcos).sub continuous_const).div
      ((continuous_const.sub (continuous_const.mul hcos)).add continuous_const)
      fun r => (eulerSymbol_denom_pos hx1 _ hx0.le).ne'
  have hbdd : ∀ b : ℝ, Integrable fun r =>
      combinationSpectralDensity c r * (eulerSymbol x (r * Real.log q) + b) := by
    intro b
    refine hG.mul_bdd (c := max (x / (1 + x)) (x / (1 - x)) + |b|)
      (hcont.add continuous_const).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs]
    have hS : |eulerSymbol x (r * Real.log q)| ≤ max (x / (1 + x)) (x / (1 - x)) := by
      rw [abs_le]
      constructor
      · linarith [neg_le_eulerSymbol hx0.le hx1 (r * Real.log q), le_max_left (x / (1 + x)) (x / (1 - x))]
      · linarith [eulerSymbol_le hx0.le hx1 (r * Real.log q), le_max_right (x / (1 + x)) (x / (1 - x))]
    linarith [abs_add_le (eulerSymbol x (r * Real.log q)) b]
  have hsplit : ∀ b : ℝ, ∫ r, combinationSpectralDensity c r * (eulerSymbol x (r * Real.log q) + b) =
      π * ∑ k ∈ Finset.range K, nodeAt c (q ^ (k + 1)) + b * (2 * π * massOf c) := by
    intro b
    have e : (fun r => combinationSpectralDensity c r * (eulerSymbol x (r * Real.log q) + b)) =
        fun r => combinationSpectralDensity c r * eulerSymbol x (r * Real.log q) +
          b * combinationSpectralDensity c r := by funext r; ring
    have hint : Integrable fun r => combinationSpectralDensity c r * eulerSymbol x (r * Real.log q) := by
      simpa using hbdd 0
    rw [e, integral_add hint (hG.const_mul b), integral_const_mul, hmass, hid]
  -- the extremal phases form countable sets
  have hZ1 : {r : ℝ | Real.cos (r * Real.log q) = -1}.Countable :=
    (Set.countable_range fun k : ℤ => (π + k * (2 * π)) / Real.log q).mono fun r hr => by
      obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.mp hr
      refine ⟨k, ?_⟩
      show (π + (k : ℝ) * (2 * π)) / Real.log q = r
      rw [hk]; field_simp
  have hZ2 : {r : ℝ | Real.cos (r * Real.log q) = 1}.Countable :=
    (Set.countable_range fun k : ℤ => (k * (2 * π)) / Real.log q).mono fun r hr => by
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hr
      refine ⟨k, ?_⟩
      show (k : ℝ) * (2 * π) / Real.log q = r
      rw [hk]; field_simp
  have h1 := integral_mul_pos_of_pos_off_countable hG hGn hGpos
    (fun r => by linarith [neg_le_eulerSymbol hx0.le hx1 (r * Real.log q)]) hZ1
    (fun r hr => by linarith [neg_lt_eulerSymbol hx0 hx1 (θ := r * Real.log q) hr])
    (hbdd (x / (1 + x)))
  have e2 : (fun r => combinationSpectralDensity c r * (x / (1 - x) - eulerSymbol x (r * Real.log q))) =
      fun r => -(combinationSpectralDensity c r * (eulerSymbol x (r * Real.log q) + -(x / (1 - x)))) := by
    funext r; ring
  have h2 := integral_mul_pos_of_pos_off_countable hG hGn hGpos
    (φ := fun r => x / (1 - x) - eulerSymbol x (r * Real.log q))
    (fun r => by linarith [eulerSymbol_le hx0.le hx1 (r * Real.log q)]) hZ2
    (fun r hr => by linarith [eulerSymbol_lt hx0 hx1 (θ := r * Real.log q) hr])
    (by rw [e2]; exact (hbdd _).neg)
  rw [hsplit] at h1
  rw [e2, integral_neg, hsplit] at h2
  rw [← inv_sqrt_div_one_add hsq, ← inv_sqrt_div_one_sub hsq, ← hx]
  constructor <;> nlinarith [Real.pi_pos]

/-! ### 5. Deleting the towers of a set of primes -/

/-- The powers `p^{k+1}` of the primes in `P`. -/
def towerNodes (P : Finset ℕ) : Set ℕ := {n | ∃ p ∈ P, ∃ k : ℕ, n = p ^ (k + 1)}

/-- A bound past which every node value of `c` vanishes. -/
def nodeBound (c : WeilTestFn →₀ ℝ) : ℕ := (nodeVector c).support.sup fun j => (j : ℕ)

theorem nodeAt_eq_zero_of_lt {c : WeilTestFn →₀ ℝ} {n : ℕ} (hn : nodeBound c < n) :
    nodeAt c n = 0 := by
  unfold nodeAt
  split_ifs with h
  · by_contra hne
    have hmem : (⟨n, h⟩ : LogIndex) ∈ (nodeVector c).support := Finsupp.mem_support_iff.mpr hne
    have := Finset.le_sup (f := fun j : LogIndex => (j : ℕ)) hmem
    simp only at this
    exact absurd (lt_of_le_of_lt this hn) (lt_irrefl _)
  · rfl

theorem nodeAt_pow_eq_zero {c : WeilTestFn →₀ ℝ} {q : ℕ} (hq : 2 ≤ q) {k : ℕ}
    (hk : nodeBound c ≤ k) : nodeAt c (q ^ (k + 1)) = 0 :=
  nodeAt_eq_zero_of_lt (lt_of_le_of_lt hk (lt_trans (Nat.lt_succ_self k) (Nat.lt_pow_self (by omega))))

/-- **The tower deletion identity.** On the cone blind at every prime power outside the towers of
`P`, `A − W = Σ_{p∈P} log p Σ_{k<K} L_{p^{k+1}}` for every `K` past which the tower node values
vanish. -/
theorem nodeArchEnergy_sub_weilEnergy_eq_towers {c : WeilTestFn →₀ ℝ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hb : BlindOn (primePowerNodes \ towerNodes P) c) {K : ℕ}
    (hK : ∀ p ∈ P, ∀ k, K ≤ k → nodeAt c (p ^ (k + 1)) = 0) :
    nodeArchEnergy c - weilEnergy c =
      ∑ p ∈ P, Real.log p * ∑ k ∈ Finset.range K, nodeAt c (p ^ (k + 1)) := by
  classical
  set D : Finset ℕ := (P ×ˢ Finset.range K).image fun pk => pk.1 ^ (pk.2 + 1)
  have hinj : Set.InjOn (fun pk : ℕ × ℕ => pk.1 ^ (pk.2 + 1)) ↑(P ×ˢ Finset.range K) := by
    intro a ha b hb' h
    rw [Finset.mem_coe, Finset.mem_product] at ha hb'
    obtain ⟨h1, h2⟩ := eq_of_prime_pow_eq (hP a.1 ha.1) (hP b.1 hb'.1) (by omega) h
    exact Prod.ext h1 (by omega)
  have hbD : BlindOn (primePowerNodes \ ↑D) c := by
    intro j ⟨hpp, hjD⟩
    by_cases ht : (j : ℕ) ∈ towerNodes P
    · obtain ⟨p, hp, k, hk⟩ := ht
      have hkK : K ≤ k := by
        by_contra hlt
        exact hjD (Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨(p, k), Finset.mem_product.mpr ⟨hp, Finset.mem_range.mpr (by omega)⟩, hk.symm⟩))
      have := hK p hp k hkK
      rw [nodeAt, dif_pos (hk ▸ j.2)] at this
      rwa [show j = ⟨p ^ (k + 1), hk ▸ j.2⟩ from Subtype.ext hk]
    · exact hb j ⟨hpp, ht⟩
  rw [nodeArchEnergy_eq_weilEnergy_add_finset D hbD, add_sub_cancel_left, Finset.sum_image hinj,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime (hP p hp)]

/-- The price from below `Σ_{p∈P} 2 log p/(√p + 1)`. -/
def towerPriceBelow (P : Finset ℕ) : ℝ := ∑ p ∈ P, 2 * Real.log p / (Real.sqrt p + 1)

/-- The price from above `Σ_{p∈P} 2 log p/(√p − 1)`. -/
def towerPriceAbove (P : Finset ℕ) : ℝ := ∑ p ∈ P, 2 * Real.log p / (Real.sqrt p - 1)

/-- **The tower deletion bounds**, strict for a nonempty set of primes. -/
theorem towerDeviation_bounds {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (hm : 0 < massOf c)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hPne : P.Nonempty)
    (hb : BlindOn (primePowerNodes \ towerNodes P) c) :
    -towerPriceBelow P * massOf c < nodeArchEnergy c - weilEnergy c ∧
      nodeArchEnergy c - weilEnergy c < towerPriceAbove P * massOf c := by
  have hK : ∀ p ∈ P, ∀ k, nodeBound c ≤ k → nodeAt c (p ^ (k + 1)) = 0 :=
    fun p hp k hk => nodeAt_pow_eq_zero (hP p hp).two_le hk
  rw [nodeArchEnergy_sub_weilEnergy_eq_towers hP hb hK, towerPriceBelow, towerPriceAbove, neg_mul,
    Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  have hb' := fun p (hp : p ∈ P) =>
    tower_sum_bounds_strict hc hm (hP p hp).two_le (hK p hp)
  have hl : ∀ p ∈ P, 0 < Real.log p := fun p hp =>
    Real.log_pos (by exact_mod_cast (hP p hp).one_lt)
  constructor
  · refine Finset.sum_lt_sum_of_nonempty hPne fun p hp => ?_
    have := mul_lt_mul_of_pos_left (hb' p hp).1 (hl p hp)
    calc -(2 * Real.log p / (Real.sqrt p + 1) * massOf c)
        = Real.log p * (-(2 / (Real.sqrt p + 1)) * massOf c) := by ring
      _ < _ := this
  · refine Finset.sum_lt_sum_of_nonempty hPne fun p hp => ?_
    have := mul_lt_mul_of_pos_left (hb' p hp).2 (hl p hp)
    calc _ < Real.log p * (2 / (Real.sqrt p - 1) * massOf c) := this
      _ = 2 * Real.log p / (Real.sqrt p - 1) * massOf c := by ring

/-! ### 6. Divisor trains -/

/-- The divisor train `Σ_{d ∣ M} σ^{Ω(d)} b(u − log d)` with the narrow bump of index `M`. -/
def divisorTrain (M : ℕ) (σ : ℝ) (u : ℝ) : ℂ :=
  ∑ d ∈ M.divisors, ((σ ^ ArithmeticFunction.cardFactors d : ℝ) : ℂ) * narrowBumpC M (u - Real.log d)

theorem contDiff_divisorTrain (M : ℕ) (σ : ℝ) : ContDiff ℝ 2 (divisorTrain M σ) :=
  ContDiff.sum fun _ _ => contDiff_const.mul
    (((contDiff_narrowBumpC _).of_le (by norm_cast)).comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_divisorTrain (M : ℕ) (σ : ℝ) : HasCompactSupport (divisorTrain M σ) :=
  hasCompactSupport_finsetSum _ fun _ _ =>
    ((hasCompactSupport_narrowBumpC _).comp_homeomorph (Homeomorph.subRight _)).mul_left

/-- The divisor train as a Weil test. -/
def divisorTrainFn (M : ℕ) (σ : ℝ) : WeilTestFn :=
  ⟨divisorTrain M σ, contDiff_divisorTrain M σ, hasCompactSupport_divisorTrain M σ⟩

/-- Integer logarithm gaps beat the radius of the bump of index `M`. -/
theorem log_lag_sep {M n a b : ℕ} (hn : 1 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b) (haM : a ≤ M)
    (hbM : b ≤ M) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hne : Real.log a - Real.log b ≠ s * Real.log n) :
    1 / (2 * ((M : ℝ) + 1)) < |s * Real.log n - Real.log a + Real.log b| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have key : ∀ X Y : ℕ, 1 ≤ X → 1 ≤ Y → X ≠ Y → Y ≤ M →
      1 / (2 * ((M : ℝ) + 1)) < |Real.log X - Real.log Y| := by
    intro X Y hX hY hXY hYM
    refine lt_of_lt_of_le ?_ (WeilExcess.inv_succ_le_abs_log_sub hX hY hXY)
    have : (Y : ℝ) ≤ M := by exact_mod_cast hYM
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  rcases hs with rfl | rfl
  · rw [one_mul] at hne ⊢
    have hne' : n * b ≠ a := fun h => hne (by
      rw [← h, Nat.cast_mul, Real.log_mul hn'.ne' hb'.ne']; ring)
    have := key (n * b) a (by nlinarith) ha hne' haM
    rw [Nat.cast_mul, Real.log_mul hn'.ne' hb'.ne'] at this
    rwa [show Real.log n - Real.log a + Real.log b = Real.log n + Real.log b - Real.log a by ring]
  · rw [neg_one_mul] at hne ⊢
    have hne' : n * a ≠ b := fun h => hne (by
      rw [← h, Nat.cast_mul, Real.log_mul hn'.ne' ha'.ne']; ring)
    have := key (n * a) b (by nlinarith) hb hne' hbM
    rw [Nat.cast_mul, Real.log_mul hn'.ne' ha'.ne'] at this
    rwa [show -Real.log n - Real.log a + Real.log b = -(Real.log n + Real.log a - Real.log b) by ring,
      abs_neg]

/-- The coefficient of the lag `y` in the autocorrelation of the divisor train. -/
def divisorCoeff (M : ℕ) (σ y : ℝ) : ℝ :=
  ∑ a ∈ M.divisors, ∑ b ∈ M.divisors, if Real.log a - Real.log b = y then
    σ ^ ArithmeticFunction.cardFactors a * σ ^ ArithmeticFunction.cardFactors b else 0

theorem one_le_of_mem_divisors {M d : ℕ} (hd : d ∈ M.divisors) : 1 ≤ d :=
  Nat.pos_of_mem_divisors hd

/-- The autocorrelation of the divisor train at `±log n`. -/
theorem weilTest_divisorTrain (M : ℕ) (σ : ℝ) {n : ℕ} (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (divisorTrain M σ) (divisorTrain M σ) (s * Real.log n) =
      (divisorCoeff M σ (s * Real.log n) : ℂ) * ((∫ t, (narrowBump M t) ^ 2 : ℝ) : ℂ) :=
  weilTest_train_select M.divisors (fun d => σ ^ ArithmeticFunction.cardFactors d)
    (fun d => Real.log d) M _ fun _ ha _ hb hne =>
      log_lag_sep hn (one_le_of_mem_divisors ha) (one_le_of_mem_divisors hb)
        (Nat.divisor_le ha) (Nat.divisor_le hb) s hs hne

theorem divisorCoeff_neg (M : ℕ) (σ y : ℝ) : divisorCoeff M σ (-y) = divisorCoeff M σ y := by
  unfold divisorCoeff
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : Real.log a - Real.log b = y
  · rw [if_pos h, if_pos (by linarith), mul_comm]
  · rw [if_neg h, if_neg fun h' => h (by linarith)]

theorem log_sub_log_eq_log_iff {a b n : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hn : 1 ≤ n) :
    Real.log a - Real.log b = Real.log n ↔ a = n * b := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [sub_eq_iff_eq_add, ← Real.log_mul hn'.ne' hb'.ne']
  constructor
  · intro h
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr ha') (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < n * b)) h
    exact_mod_cast this
  · intro h; rw [h]; push_cast; ring_nf

/-- **The divisor coefficient.** At the lag `log n`, `n ≥ 1`, the coefficient is
`σ^{Ω(n)} τ(M/n)` when `n ∣ M` and `0` otherwise: the pairs are `(nb, b)` with `b ∣ M/n`. -/
theorem divisorCoeff_log {M : ℕ} (hM : M ≠ 0) {σ : ℝ} (hσ : σ ^ 2 = 1) {n : ℕ} (hn : 1 ≤ n) :
    divisorCoeff M σ (Real.log n) =
      σ ^ ArithmeticFunction.cardFactors n * (if n ∣ M then ((M / n).divisors.card : ℝ) else 0) := by
  classical
  unfold divisorCoeff
  rw [Finset.sum_comm]
  have hinner : ∀ b ∈ M.divisors, (∑ a ∈ M.divisors, if Real.log a - Real.log b = Real.log n then
      σ ^ ArithmeticFunction.cardFactors a * σ ^ ArithmeticFunction.cardFactors b else 0) =
        if n * b ∈ M.divisors then σ ^ ArithmeticFunction.cardFactors n else 0 := by
    intro b hb
    have hb1 := one_le_of_mem_divisors hb
    rw [Finset.sum_congr rfl fun a ha => if_congr
      (log_sub_log_eq_log_iff (one_le_of_mem_divisors ha) hb1 hn) rfl rfl,
      Finset.sum_ite_eq' M.divisors (n * b)]
    refine if_congr Iff.rfl ?_ rfl
    rw [ArithmeticFunction.cardFactors_mul (by omega) (by omega), pow_add, mul_assoc, ← pow_add,
      ← two_mul, pow_mul, hσ, one_pow, mul_one]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  split_ifs with hnM
  · have hfilt : M.divisors.filter (fun b => n * b ∈ M.divisors) = (M / n).divisors := by
      ext b
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨_, hnb, _⟩
        exact ⟨(Nat.dvd_div_iff_mul_dvd hnM).mpr hnb,
          (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hnM) (by omega)).ne'⟩
      · rintro ⟨hb, _⟩
        have hnb := (Nat.dvd_div_iff_mul_dvd hnM).mp hb
        exact ⟨⟨(Dvd.intro_left n rfl).trans hnb, hM⟩, hnb, hM⟩
    rw [hfilt]
  · have : M.divisors.filter (fun b => n * b ∈ M.divisors) = ∅ := by
      ext b
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.notMem_empty, iff_false, not_and]
      intro _ hnb
      exact absurd ((Dvd.intro b rfl).trans hnb) hnM
    rw [this, Finset.card_empty, Nat.cast_zero]

theorem divisorCoeff_zero {M : ℕ} (hM : M ≠ 0) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    divisorCoeff M σ (Real.log (1 : ℕ)) = (M.divisors.card : ℝ) := by
  rw [divisorCoeff_log hM hσ le_rfl, ArithmeticFunction.cardFactors_one, pow_zero, one_mul,
    if_pos (one_dvd M), Nat.div_one]

/-- The mass of the divisor train is `τ(M) ∫ h²`. -/
theorem massOf_single_divisorTrainFn {M : ℕ} (hM : M ≠ 0) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    massOf (Finsupp.single (divisorTrainFn M σ) 1) =
      (M.divisors.card : ℝ) * ∫ t, (narrowBump M t) ^ 2 := by
  have hk := weilTest_divisorTrain M σ (n := 1) le_rfl 1 (Or.inl rfl)
  rw [one_mul, divisorCoeff_zero hM hσ, Nat.cast_one, Real.log_one,
    RHTower.weilTest_zero_eq_integral_norm_sq] at hk
  have hm : ∫ u, ‖divisorTrain M σ u‖ ^ 2 =
      (M.divisors.card : ℝ) * ∫ t, (narrowBump M t) ^ 2 := by exact_mod_cast hk
  rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
  exact hm

/-- **The node values of the divisor train**: `L_n = 2σ^{Ω(n)} τ(M/n) ∫h²/√n` if `n ∣ M`, else `0`. -/
theorem nodeAt_single_divisorTrainFn {M : ℕ} (hM : M ≠ 0) {σ : ℝ} (hσ : σ ^ 2 = 1) {n : ℕ}
    (hn : 2 ≤ n) :
    nodeAt (Finsupp.single (divisorTrainFn M σ) 1) n =
      2 * (σ ^ ArithmeticFunction.cardFactors n *
        (if n ∣ M then ((M / n).divisors.card : ℝ) else 0)) *
          (∫ t, (narrowBump M t) ^ 2) / Real.sqrt n := by
  have e1 := weilTest_divisorTrain M σ (n := n) (by omega) 1 (Or.inl rfl)
  have e2 := weilTest_divisorTrain M σ (n := n) (by omega) (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul, divisorCoeff_neg] at e2
  rw [nodeAt, dif_pos hn, nodeVector_single_test, logVector_apply]
  change logValue (divisorTrain M σ) n = _
  rw [logValue, e1, e2, divisorCoeff_log hM hσ (by omega), ← add_mul, ← Complex.ofReal_add,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-! ### 7. Box moduli -/

/-- The number of divisors of a product of prime powers. -/
theorem card_divisors_subProd {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (e : ℕ → ℕ) :
    (subProd e P).divisors.card = ∏ p ∈ P, (e p + 1) := by
  classical
  rw [Nat.card_divisors (subProd_pos hP).ne']
  refine (Finset.prod_subset ?_ ?_).trans (Finset.prod_congr rfl fun p hp => ?_)
  · intro x hx
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_subProd hP] at hx
    by_contra h
    exact hx (if_neg h)
  · intro x _ hx
    rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hx
    rw [hx]; rfl
  · rw [factorization_subProd hP, if_pos hp]

/-- Splitting off `p^j` from a product of prime powers. -/
theorem subProd_eq_pow_mul {P : Finset ℕ} (e : ℕ → ℕ) {p : ℕ} (hp : p ∈ P) {j : ℕ}
    (hj : j ≤ e p) : subProd e P = p ^ j * subProd (Function.update e p (e p - j)) P := by
  classical
  unfold subProd
  rw [← Finset.mul_prod_erase P _ hp, ← Finset.mul_prod_erase P _ hp, Function.update_self,
    ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]
  congr 1
  exact Finset.prod_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]

/-- The box modulus `M_n = Π_{p∈P} p^n`. -/
abbrev boxModulus (P : Finset ℕ) (n : ℕ) : ℕ := subProd (fun _ => n) P

section Box

variable {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)

include hP in
theorem boxModulus_ne_zero (n : ℕ) : boxModulus P n ≠ 0 := (subProd_pos hP).ne'

include hP in
/-- `p^{k+1}` divides the box modulus exactly when `k < n`. -/
theorem pow_succ_dvd_boxModulus_iff {p : ℕ} (hp : p ∈ P) (n k : ℕ) :
    p ^ (k + 1) ∣ boxModulus P n ↔ k < n := by
  rw [(hP p hp).pow_dvd_iff_le_factorization (boxModulus_ne_zero hP n), factorization_subProd hP,
    if_pos hp]
  omega

include hP in
/-- A prime outside `P`: `q^m ∤ M_n` for `m ≥ 1`. -/
theorem not_pow_dvd_boxModulus {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ¬ q ^ m ∣ boxModulus P n := by
  rw [hq.pow_dvd_iff_le_factorization (boxModulus_ne_zero hP n), factorization_subProd hP, if_neg hqP]
  omega

include hP in
/-- **The Fejér weight of the box.** `(n+1) τ(M_n/p^{k+1}) = (n − k) τ(M_n)` for `k < n`. -/
theorem card_divisors_boxModulus_div {p : ℕ} (hp : p ∈ P) {n k : ℕ} (hk : k < n) :
    (n + 1) * (boxModulus P n / p ^ (k + 1)).divisors.card =
      (n - k) * (boxModulus P n).divisors.card := by
  classical
  have hsplit := subProd_eq_pow_mul (P := P) (fun _ => n) hp (j := k + 1) (by omega)
  have hpos : 0 < p ^ (k + 1) := pow_pos (hP p hp).pos _
  have hq : boxModulus P n / p ^ (k + 1) = subProd (Function.update (fun _ => n) p (n - (k + 1))) P := by
    rw [show boxModulus P n = _ from hsplit, Nat.mul_div_cancel_left _ hpos]
  rw [hq, card_divisors_subProd hP, card_divisors_subProd hP, ← Finset.mul_prod_erase P _ hp,
    ← Finset.mul_prod_erase P (fun _ => n + 1) hp, Function.update_self]
  rw [Finset.prod_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]]
  rw [show n - (k + 1) + 1 = n - k by omega]
  ring

/-- The box train of sign `σ` and exponent `n`. -/
def boxTrain (P : Finset ℕ) (σ : ℝ) (n : ℕ) : WeilTestFn →₀ ℝ :=
  Finsupp.single (divisorTrainFn (boxModulus P n) σ) 1

theorem nodeAt_val (c : WeilTestFn →₀ ℝ) (j : LogIndex) : nodeAt c j = nodeVector c j :=
  dif_pos j.2

include hP in
theorem blindOn_boxTrain {σ : ℝ} (hσ : σ ^ 2 = 1) (n : ℕ) :
    BlindOn (primePowerNodes \ towerNodes P) (boxTrain P σ n) := by
  intro j ⟨hpp, hj⟩
  obtain ⟨q, m, hq, hm, hqm⟩ := (isPrimePow_nat_iff _).mp hpp
  have hqP : q ∉ P := fun hqP => hj ⟨q, hqP, m - 1, by rw [← hqm]; congr 1; omega⟩
  rw [← nodeAt_val, boxTrain, nodeAt_single_divisorTrainFn (boxModulus_ne_zero hP n) hσ j.2,
    if_neg (hqm ▸ not_pow_dvd_boxModulus hP hq hqP hm n)]
  simp

include hP in
theorem massOf_boxTrain_pos {σ : ℝ} (hσ : σ ^ 2 = 1) (n : ℕ) : 0 < massOf (boxTrain P σ n) := by
  rw [boxTrain, massOf_single_divisorTrainFn (boxModulus_ne_zero hP n) hσ]
  have : (0 : ℝ) < (boxModulus P n).divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (boxModulus_ne_zero hP n)⟩
  exact mul_pos this (integral_narrowBump_sq_pos _)

/-- The deviation of the box train: `Σ_{p∈P} log p Σ_{k<n} 2(σ/√p)^{k+1}(n − k)/(n + 1)`. -/
def boxDeviation (P : Finset ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, Real.log p * ∑ k ∈ Finset.range n,
    2 * (σ / Real.sqrt p) ^ (k + 1) * (((n : ℝ) - k) / ((n : ℝ) + 1))

include hP in
/-- **The box deviation.** -/
theorem boxTrain_deviation {σ : ℝ} (hσ : σ ^ 2 = 1) (n : ℕ) :
    (nodeArchEnergy (boxTrain P σ n) - weilEnergy (boxTrain P σ n)) / massOf (boxTrain P σ n) =
      boxDeviation P σ n := by
  have hM := boxModulus_ne_zero hP n
  have hnode : ∀ p ∈ P, ∀ k, nodeAt (boxTrain P σ n) (p ^ (k + 1)) =
      2 * (σ ^ (k + 1) * (if k < n then ((boxModulus P n / p ^ (k + 1)).divisors.card : ℝ) else 0)) *
        (∫ t, (narrowBump (boxModulus P n) t) ^ 2) / Real.sqrt p ^ (k + 1) := by
    intro p hp k
    rw [boxTrain, nodeAt_single_divisorTrainFn hM hσ (two_le_pow_succ (hP p hp).two_le k),
      ArithmeticFunction.cardFactors_apply_prime_pow (hP p hp), sqrt_natCast_pow]
    simp only [pow_succ_dvd_boxModulus_iff hP hp n k]
  have hK : ∀ p ∈ P, ∀ k, n ≤ k → nodeAt (boxTrain P σ n) (p ^ (k + 1)) = 0 := by
    intro p hp k hk
    rw [hnode p hp k, if_neg (by omega)]
    simp
  rw [nodeArchEnergy_sub_weilEnergy_eq_towers hP (blindOn_boxTrain hP hσ n) hK, Finset.sum_div,
    boxDeviation]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k < n := Finset.mem_range.mp hk
  rw [hnode p hp k, if_pos hkn, boxTrain, massOf_single_divisorTrainFn hM hσ]
  have hcard := card_divisors_boxModulus_div hP hp hkn
  have h1 : ((n + 1 : ℕ) : ℝ) * ((boxModulus P n / p ^ (k + 1)).divisors.card : ℝ) =
      ((n - k : ℕ) : ℝ) * (boxModulus P n).divisors.card := by exact_mod_cast hcard
  rw [Nat.cast_sub hkn.le] at h1
  push_cast at h1
  have hcard' : ((boxModulus P n / p ^ (k + 1)).divisors.card : ℝ) =
      ((n : ℝ) - k) / ((n : ℝ) + 1) * (boxModulus P n).divisors.card := by
    rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
    linarith
  have hI := integral_narrowBump_sq_pos (boxModulus P n)
  have hτ : (0 : ℝ) < (boxModulus P n).divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hM⟩
  have hs : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (hP p hp).pos)).ne'
  rw [hcard', div_pow]
  field_simp

end Box

/-! ### 8. Both ends are approached -/

/-- **Fejér-weighted geometric sums.** `Σ_{k<n} y^{k+1}(n − k)/(n + 1) → y/(1 − y)` for `|y| < 1`. -/
theorem tendsto_fejer_geometric {y : ℝ} (hy : |y| < 1) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, y ^ (k + 1) * (((n : ℝ) - k) / ((n : ℝ) + 1)))
      atTop (nhds (y / (1 - y))) := by
  have hgeo : HasSum (fun k : ℕ => y ^ (k + 1)) (y / (1 - y)) := by
    have := (hasSum_geometric_of_abs_lt_one hy).mul_left y
    simpa only [← pow_succ', div_eq_mul_inv] using this
  have hsum : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * |y| ^ (k + 1) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := |y|)
      (by rwa [Real.norm_eq_abs, abs_abs])
    have := (summable_nat_add_iff 1).mpr h
    simpa only [pow_one] using this
  set C := ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * |y| ^ (k + 1)
  have hsplit : ∀ n : ℕ, ∑ k ∈ Finset.range n, y ^ (k + 1) * (((n : ℝ) - k) / ((n : ℝ) + 1)) =
      ∑ k ∈ Finset.range n, y ^ (k + 1) -
        (∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) * y ^ (k + 1)) / ((n : ℝ) + 1) := by
    intro n
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have htail : Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) * y ^ (k + 1)) / ((n : ℝ) + 1)) atTop (nhds 0) := by
    refine squeeze_zero_norm (a := fun n : ℕ => C / ((n : ℝ) + 1)) (fun n => ?_) ?_
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq_of_le
        (Finset.sum_congr rfl fun k _ => by rw [abs_mul, abs_pow, Nat.abs_cast]) ?_)
      exact hsum.sum_le_tsum _ fun k _ => by positivity
    · have := (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have := hgeo.tendsto_sum_nat.sub htail
  rw [sub_zero] at this
  exact this.congr fun n => (hsplit n).symm

/-- The box deviations converge to `Σ_{p∈P} 2 log p · y_p/(1 − y_p)`, `y_p = σ/√p`. -/
theorem tendsto_boxDeviation {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {σ : ℝ} (hσ : |σ| = 1) :
    Tendsto (boxDeviation P σ) atTop
      (nhds (∑ p ∈ P, Real.log p * (2 * ((σ / Real.sqrt p) / (1 - σ / Real.sqrt p))))) := by
  unfold boxDeviation
  refine tendsto_finsetSum _ fun p hp => ?_
  have hs : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast (hP p hp).one_lt)
  have hy : |σ / Real.sqrt p| < 1 := by
    rw [abs_div, hσ, abs_of_pos (by linarith), div_lt_one (by linarith)]
    exact hs
  refine (((tendsto_fejer_geometric hy).const_mul 2).const_mul (Real.log p)).congr fun n => ?_
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The normalized deviations `(A − W)/‖c‖²` on the cone blind at every prime power outside the
towers of `P`. -/
def towerDeviations (P : Finset ℕ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn (primePowerNodes \ towerNodes P) c ∧
    0 < massOf c ∧ x = (nodeArchEnergy c - weilEnergy c) / massOf c}

/-- **No deviation reaches either end.** -/
theorem towerDeviations_subset_Ioo {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hPne : P.Nonempty) :
    towerDeviations P ⊆ Ioo (-towerPriceBelow P) (towerPriceAbove P) := by
  rintro x ⟨c, hc, hb, hm, rfl⟩
  obtain ⟨h1, h2⟩ := towerDeviation_bounds hc hm hP hPne hb
  exact ⟨by rwa [lt_div_iff₀ hm], by rwa [div_lt_iff₀ hm]⟩

theorem boxDeviation_mem {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {σ : ℝ} (hσ : σ ^ 2 = 1) (n : ℕ) :
    boxDeviation P σ n ∈ towerDeviations P := by
  classical
  refine ⟨boxTrain P σ n, fun f => ?_, blindOn_boxTrain hP hσ n, massOf_boxTrain_pos hP hσ n,
    (boxTrain_deviation hP hσ n).symm⟩
  rw [boxTrain, Finsupp.single_apply]
  split_ifs <;> norm_num

theorem limit_below_eq {p : ℕ} (hp : p.Prime) :
    Real.log p * (2 * ((-1 / Real.sqrt p) / (1 - -1 / Real.sqrt p))) =
      -(2 * Real.log p / (Real.sqrt p + 1)) := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have h1 : Real.sqrt p + 1 ≠ 0 := by positivity
  have h2 : (1 + Real.sqrt p) * (1 + Real.sqrt p)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  field_simp
  linear_combination (-Real.log p) * h2

theorem limit_above_eq {p : ℕ} (hp : p.Prime) :
    Real.log p * (2 * ((1 / Real.sqrt p) / (1 - 1 / Real.sqrt p))) =
      2 * Real.log p / (Real.sqrt p - 1) := by
  have hs : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast hp.one_lt)
  have : Real.sqrt p - 1 ≠ 0 := by linarith
  have : Real.sqrt p ≠ 0 := by linarith
  field_simp

/-- **The whole-tower price from below.** On the cone blind at every prime power outside the towers
of `P`, the infimum of `(A − W)/‖c‖²` is `−Σ_{p∈P} 2 log p/(√p + 1)`, and it is not attained. -/
theorem isGLB_towerDeviations {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hPne : P.Nonempty) :
    IsGLB (towerDeviations P) (-towerPriceBelow P) := by
  refine ⟨fun x hx => (towerDeviations_subset_Ioo hP hPne hx).1.le, fun b hb => ?_⟩
  have hlim := tendsto_boxDeviation hP (σ := -1) (by norm_num)
  rw [Finset.sum_congr rfl fun p hp => limit_below_eq (hP p hp), Finset.sum_neg_distrib] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall fun n =>
    hb (boxDeviation_mem hP (σ := -1) (by norm_num) n))

/-- **The whole-tower price from above.** The supremum of `(A − W)/‖c‖²` on the same cone is
`Σ_{p∈P} 2 log p/(√p − 1)`, and it is not attained. -/
theorem isLUB_towerDeviations {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hPne : P.Nonempty) :
    IsLUB (towerDeviations P) (towerPriceAbove P) := by
  refine ⟨fun x hx => (towerDeviations_subset_Ioo hP hPne hx).2.le, fun b hb => ?_⟩
  have hlim := tendsto_boxDeviation hP (σ := 1) (by norm_num)
  rw [Finset.sum_congr rfl fun p hp => limit_above_eq (hP p hp)] at hlim
  exact le_of_tendsto hlim (Eventually.of_forall fun n =>
    hb (boxDeviation_mem hP (σ := 1) (by norm_num) n))

/-- **Two multiplicatively independent integers.** With the towers of `2` and `3` deleted, the exact
infimum of `(A − W)/‖c‖²` is `−(2 log 2/(√2 + 1) + 2 log 3/(√3 + 1))`. -/
theorem isGLB_towerDeviations_two_three :
    IsGLB (towerDeviations {2, 3})
      (-(2 * Real.log 2 / (Real.sqrt 2 + 1) + 2 * Real.log 3 / (Real.sqrt 3 + 1))) := by
  have h := isGLB_towerDeviations (P := {2, 3})
    (by intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        exacts [Nat.prime_two, Nat.prime_three]) ⟨2, by simp⟩
  rwa [towerPriceBelow, Finset.sum_pair (by norm_num), Nat.cast_ofNat, Nat.cast_ofNat] at h

/-- The whole tower costs strictly more than its first node from below: `log p/√p < 2 log p/(√p+1)`. -/
theorem single_price_lt_tower_price {p : ℕ} (hp : p.Prime) :
    Real.log p / Real.sqrt p < 2 * Real.log p / (Real.sqrt p + 1) := by
  have hs : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast hp.one_lt)
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end

end GaloisForLFunctions.BiScaleUncertainty
