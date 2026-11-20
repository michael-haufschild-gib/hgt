import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.HammingSquareCompensationOfTheSmallPrimes
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHalfScaleOfTheRate
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# The half rate under the Riemann hypothesis and exact resolution of the floor obstruction

Combining the taut-string Mellin–Plancherel smooth stencil with bipartite Hamming-square clusters
and the subset-product CRT ramp closes the polynomial rate scale across the entire critical strip:

* **Full-strip achievability (`hasRate_of_zeroFree_exact`).** For every `Θ ∈ [1/2, 1)`, if
  `ζ(s) ≠ 0` on `Re s > Θ`, then `HasRate (fun K => K^{-a})` holds for every `a ∈ (0, 1 - Θ)`.
* **Exact zero-free equivalence (`zeroFree_iff_forall_hasRate`).** `ζ(s) ≠ 0` on `Re s > Θ` if
  and only if `HasRate (fun K => K^{-a})` holds for every `a ∈ (0, 1 - Θ)`.
* **Riemann Hypothesis equivalence (`riemannHypothesis_iff_forall_hasRate_half`).**
  `RiemannHypothesis ↔ ∀ a ∈ (0, 1/2), HasRate (fun K => K^{-a})`.
* **Unconditional exact rate-exponent law (`tendsto_log_bestRate_div_log`).**
  `lim_{K → ∞} log(bestRate K) / log K = Θ_ζ - 1`, where `Θ_ζ = zetaZeroAbscissa`.
* **Resolution of the integer floor-alphabet obstruction
  (`exists_strict_floor_obstruction_iff_not_riemannHypothesis`).** For every `a₀ ∈ [0, 1/2)` (in
  particular `a₀ = 1/4`), the existence of `a_* ∈ (a₀, 1/2)` such that eventually every integer
  producer on `[1, K]` has `rate c m B > K^{-a_*}` is equivalent to `¬ RiemannHypothesis`.
-/

open Finset Filter Topology
open scoped Classical
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-! ### Part 1: Asymptotic rpow-logarithmic dominance helpers -/

private lemma tendsto_one_add_log_mul_rpow_neg {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => (1 + Real.log x) * x ^ (-δ)) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_neg_atTop hδ
  have h2 := (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_neg hx.le]
  field_simp

private lemma tendsto_one_add_log_pow_mul_rpow_neg (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => (1 + Real.log x) ^ k * x ^ (-δ)) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using tendsto_rpow_neg_atTop hδ
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsub := (tendsto_one_add_log_mul_rpow_neg (div_pos hδ hkR)).pow k
  rw [zero_pow hk.ne'] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [mul_pow, ← Real.rpow_natCast ((x : ℝ) ^ (-(δ / (k : ℝ)))) k, ← Real.rpow_mul hx.le]
  congr 2
  field_simp [hkR.ne']

private lemma eventually_const_log_pow_rpow_le (C : ℝ) (k : ℕ) {p q : ℝ} (hpq : p < q) :
    ∀ᶠ K : ℕ in atTop, C * (1 + Real.log (K : ℝ)) ^ k * (K : ℝ) ^ p ≤ (K : ℝ) ^ q := by
  set C' : ℝ := max C 0 + 1
  have hC'_pos : 0 < C' := by dsimp [C']; positivity
  have hC_le : C ≤ C' := (le_max_left C 0).trans (by dsimp [C']; linarith)
  have hδ : 0 < q - p := sub_pos.mpr hpq
  have hlim := ((tendsto_one_add_log_pow_mul_rpow_neg k hδ).const_mul C').comp
    tendsto_natCast_atTop_atTop
  rw [mul_zero] at hlim
  filter_upwards [eventually_ge_atTop 1, hlim.eventually (gt_mem_nhds zero_lt_one)] with K hK1 hlt
  simp only [Function.comp] at hlt
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hlog_nn : 0 ≤ 1 + Real.log (K : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hK1 : (1 : ℝ) ≤ (K : ℝ))
    linarith
  have hmul_q := mul_le_mul_of_nonneg_right hlt.le (Real.rpow_nonneg hK_pos.le q)
  rw [one_mul, mul_assoc, mul_assoc, ← Real.rpow_add hK_pos] at hmul_q
  have hexp : -(q - p) + q = p := by ring
  rw [hexp, ← mul_assoc] at hmul_q
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC_le (pow_nonneg hlog_nn k))
    (Real.rpow_nonneg hK_pos.le p)).trans hmul_q

private lemma eventually_const_rpow_le (C : ℝ) {p q : ℝ} (hpq : p < q) :
    ∀ᶠ K : ℕ in atTop, C * (K : ℝ) ^ p ≤ (K : ℝ) ^ q := by
  filter_upwards [eventually_const_log_pow_rpow_le C 0 hpq] with K hK
  simpa using hK

private lemma eventually_floor_rpow_bounds {c α : ℝ} (hc : 0 < c) (hα : 0 < α) :
    ∀ᶠ K : ℕ in atTop,
      2 ≤ ⌊c * (K : ℝ) ^ α⌋₊ ∧
      (c / 2) * (K : ℝ) ^ α ≤ (⌊c * (K : ℝ) ^ α⌋₊ : ℝ) ∧
      (⌊c * (K : ℝ) ^ α⌋₊ : ℝ) ≤ c * (K : ℝ) ^ α := by
  have hlim : Tendsto (fun K : ℕ => c * (K : ℝ) ^ α) atTop atTop :=
    ((tendsto_rpow_atTop hα).const_mul_atTop hc).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop 2] with K hge2
  have hnn : 0 ≤ c * (K : ℝ) ^ α := by linarith
  have hfl_ge2 : 2 ≤ ⌊c * (K : ℝ) ^ α⌋₊ := Nat.le_floor (by exact_mod_cast hge2)
  have hfl_le : (⌊c * (K : ℝ) ^ α⌋₊ : ℝ) ≤ c * (K : ℝ) ^ α := Nat.floor_le hnn
  have hfl_gt := Nat.lt_floor_add_one (c * (K : ℝ) ^ α)
  refine ⟨hfl_ge2, ?_, hfl_le⟩
  linarith

/-! ### Part 2: Uniform supercritical floor from a single zero and above `1 - Θ_ζ` -/

/-- **Uniform supercritical floor from a single zero.** If `ζ(ρ) = 0` and `1 - a < Re ρ` with
`a ∈ (0, 1/2]`, then for all sufficiently large `K`, every integer producer `(c, m, B)` on `[1, K]`
satisfies `K^{-a} < rate c m B`. -/
theorem eventually_rate_gt_of_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    {a : ℝ} (ha0 : 0 < a) (ha_half : a ≤ 1 / 2) (hre : 1 - a < ρ.re) :
    ∀ᶠ K : ℕ in atTop, ∀ (c : ℕ →₀ ℤ) (m B : ℕ),
      IsProducer c m B → AlphabetLE c K → (K : ℝ) ^ (-a) < rate c m B := by
  have hβ1 : ρ.re ≤ 1 := by
    by_contra hgt
    exact riemannZeta_ne_zero_of_one_le_re (not_le.mp hgt).le hρ
  have hβ : 1 / 2 ≤ ρ.re := by linarith
  obtain ⟨β, hβ_def⟩ : ∃ β : ℝ, β = ρ.re := ⟨_, rfl⟩
  rw [← hβ_def] at hβ hβ1 hre
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = β + a - 1 := ⟨_, rfl⟩
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  have hlim := (((tendsto_one_add_log_mul_rpow_neg (half_pos hδ_pos)).pow 2).const_mul
    (4800 * ‖ρ‖)).comp tendsto_natCast_atTop_atTop
  rw [show (4800 * ‖ρ‖) * (0 : ℝ) ^ 2 = 0 by simp] at hlim
  filter_upwards [eventually_ge_atTop 1, hlim.eventually (gt_mem_nhds zero_lt_one)] with
    K hK1 hKlt c m B hP hal
  simp only [Function.comp] at hKlt
  by_contra hr_le
  push Not at hr_le
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hl0 : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
  have hpow1 : (K : ℝ) ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hKR (by linarith)
  have hr1 : rate c m B ≤ 1 := hr_le.trans hpow1
  have hε := hP.rate_pos
  have hlaw := hP.zero_law hr1 hρ (hβ_def ▸ hβ) (hβ_def ▸ hβ1)
  rw [← hβ_def] at hlaw
  have hKa : (K : ℝ) * rate c m B ≤ (K : ℝ) ^ (1 - a) := by
    have hsplit : (K : ℝ) ^ (1 - a) = (K : ℝ) * (K : ℝ) ^ (-a) := by
      rw [sub_eq_add_neg, Real.rpow_add hK0, Real.rpow_one]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hr_le hK0.le
  have hK1a : 1 ≤ (K : ℝ) ^ (1 - a) := Real.one_le_rpow hKR (by linarith)
  have hx : IsProducer.peakRatio c m ≤ 200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (1 - a) := by
    refine (hP.peakRatio_le hal hK1).trans ?_
    have hsum : (K : ℝ) * rate c m B + 1 ≤ 2 * (K : ℝ) ^ (1 - a) := by linarith
    calc 100 * (1 + Real.log (K : ℝ)) ^ 2 * ((K : ℝ) * rate c m B + 1)
        ≤ 100 * (1 + Real.log (K : ℝ)) ^ 2 * (2 * (K : ℝ) ^ (1 - a)) := by gcongr
      _ = _ := by ring
  have hx1 := hP.one_le_peakRatio
  have hexp : 0 ≤ 1 - β := by linarith
  have hL : 1 ≤ 200 * (1 + Real.log (K : ℝ)) ^ 2 := by
    have : 1 ≤ (1 + Real.log (K : ℝ)) ^ 2 := one_le_pow₀ (by linarith)
    linarith
  have hp1 : IsProducer.peakRatio c m ^ (1 - β) ≤
      200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ ((1 - a) * (1 - β)) := by
    calc IsProducer.peakRatio c m ^ (1 - β)
        ≤ (200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (1 - a)) ^ (1 - β) :=
          Real.rpow_le_rpow (by linarith) hx hexp
      _ = (200 * (1 + Real.log (K : ℝ)) ^ 2) ^ (1 - β) * (K : ℝ) ^ ((1 - a) * (1 - β)) := by
          rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_mul hK0.le]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc _ ≤ (200 * (1 + Real.log (K : ℝ)) ^ 2) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hL (by linarith)
            _ = _ := Real.rpow_one _
  have hp2 : rate c m B ^ β ≤ (K : ℝ) ^ (-(a * β)) := by
    calc rate c m B ^ β ≤ ((K : ℝ) ^ (-a)) ^ β := Real.rpow_le_rpow hε.le hr_le (by linarith)
      _ = _ := by rw [← Real.rpow_mul hK0.le]; congr 1; ring
  have hprod : IsProducer.peakRatio c m ^ (1 - β) * rate c m B ^ β ≤
      200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (-δ) := by
    have hcomb : (K : ℝ) ^ ((1 - a) * (1 - β)) * (K : ℝ) ^ (-(a * β)) = (K : ℝ) ^ (-δ) := by
      rw [← Real.rpow_add hK0, hδ_def]; congr 1; ring
    calc _ ≤ (200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ ((1 - a) * (1 - β))) *
            (K : ℝ) ^ (-(a * β)) := mul_le_mul hp1 hp2 (by positivity) (by positivity)
      _ = 200 * (1 + Real.log (K : ℝ)) ^ 2 *
          ((K : ℝ) ^ ((1 - a) * (1 - β)) * (K : ℝ) ^ (-(a * β))) := by ring
      _ = _ := by rw [hcomb]
  have hfinal : 1 ≤ 24 * ‖ρ‖ * (200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (-δ)) :=
    hlaw.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
  have hsq : ((1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-(δ / 2))) ^ 2 =
      (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (-δ) := by
    have h3 : ((K : ℝ) ^ (-(δ / 2))) ^ 2 = (K : ℝ) ^ (-δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]; congr 1; push_cast; ring
    rw [mul_pow, h3]
  have hid : 24 * ‖ρ‖ * (200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (-δ)) =
      4800 * ‖ρ‖ * ((1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-(δ / 2))) ^ 2 := by
    rw [hsq]; ring
  rw [hid] at hfinal
  linarith only [hfinal, hKlt]

/-- **Supercritical floor above `1 - Θ_ζ`.** For every `a > 1 - zetaZeroAbscissa`, eventually every
integer producer on `[1, K]` satisfies `K^{-a} < rate c m B`. -/
theorem eventually_rate_gt_of_one_sub_zetaZeroAbscissa_lt {a : ℝ}
    (ha : 1 - RHTower.zetaZeroAbscissa < a) :
    ∀ᶠ K : ℕ in atTop, ∀ (c : ℕ →₀ ℤ) (m B : ℕ),
      IsProducer c m B → AlphabetLE c K → (K : ℝ) ^ (-a) < rate c m B := by
  rcases le_or_gt a (1 / 2) with ha_half | ha_gt
  · have hΘ_le1 := RHTower.zetaZeroAbscissa_le_one
    have ha0 : 0 < a := by linarith
    obtain ⟨ρ, hρ, hre⟩ := RHTower.exists_zetaZero_lt_re (show 1 - a < RHTower.zetaZeroAbscissa by linarith)
    exact eventually_rate_gt_of_zero hρ ha0 ha_half hre
  · obtain ⟨c₁, hc₁, hfloor⟩ := exists_half_floor
    have hδ : 0 < a - 1 / 2 := by linarith
    have hlim := (tendsto_one_add_log_mul_rpow_neg hδ).comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 1, hlim.eventually (gt_mem_nhds hc₁)] with
      K hK1 hKlt c m B hP hal
    simp only [Function.comp] at hKlt
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hK0 : (0 : ℝ) < K := by linarith
    have hl1 : 0 < 1 + Real.log (K : ℝ) := by
      have := Real.log_nonneg hKR; linarith
    have hD : 0 < √(K : ℝ) * (1 + Real.log (K : ℝ)) := by positivity
    have hlt_fl : (K : ℝ) ^ (-a) < c₁ / (√(K : ℝ) * (1 + Real.log (K : ℝ))) := by
      rw [lt_div_iff₀ hD]
      have hsplit : (K : ℝ) ^ (-a) * (√(K : ℝ) * (1 + Real.log (K : ℝ))) =
          (1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-(a - 1 / 2)) := by
        rw [Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hK0]
        have : -a + 1 / 2 = -(a - 1 / 2) := by ring
        rw [this]; ring
      rwa [hsplit]
    exact lt_of_lt_of_le hlt_fl (hfloor K c m B hK1 hP hal)

/-- For every `a > 1 - zetaZeroAbscissa`, eventually `K^{-a} ≤ bestRate K`. -/
theorem eventually_bestRate_ge_of_one_sub_zetaZeroAbscissa_lt {a : ℝ}
    (ha : 1 - RHTower.zetaZeroAbscissa < a) :
    ∀ᶠ K : ℕ in atTop, (K : ℝ) ^ (-a) ≤ bestRate K := by
  filter_upwards [hasRate_vk (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 3 / 5),
    eventually_rate_gt_of_one_sub_zetaZeroAbscissa_lt ha] with K hvk hgt
  obtain ⟨c, m, B, hP, hal, -⟩ := hvk
  refine le_csInf ⟨rate c m B, c, m, B, hP, hal, rfl⟩ ?_
  rintro ε ⟨c', m', B', hP', hal', rfl⟩
  exact (hgt c' m' B' hP' hal').le

/-! ### Part 3: Full-scale rate achievability from any zero-free half-plane -/

private lemma hasRate_rate_tail_le {b : ℕ → ℤ} {T K B₀ M₀ S D_W : ℕ}
    {η₀ C_η₀ C_mass a a' δ e_mass η : ℝ}
    (hK4 : 4 ≤ K) (hT_ge2 : 2 ≤ T) (h2T_le_K : 2 * T ≤ K)
    (hB₀_ge2 : 2 ≤ B₀) (hBK_nat : B₀ ≤ K) (hDW_pos : (0 : ℝ) < (D_W : ℝ))
    (hCη₀_nn : 0 ≤ C_η₀) (hCmass_nn : 0 ≤ C_mass)
    (hδ_pos : 0 < δ) (hem_nn : 0 ≤ e_mass)
    (hη₀_nn : 0 ≤ η₀) (hη₀_bd : η₀ ≤ C_η₀ * (K : ℝ) ^ (-a'))
    (hmass_bd : tautMass b (2 * T) ≤ C_mass * (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass)
    (hB₀_lo_R : (1 / (2 * (D_W : ℝ))) * (K : ℝ) ^ (1 - η) ≤ (B₀ : ℝ))
    (hr1 : (80 * C_η₀) * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (-a') ≤ (K : ℝ) ^ (-(a + δ / 2)))
    (hr2 : (80 * (1 + C_mass)) * (1 + Real.log (K : ℝ)) ^ 5 * (K : ℝ) ^ (e_mass - 2) ≤
      (K : ℝ) ^ (-(a + δ / 2)))
    (hr3 : (2 * (D_W : ℝ) * C_mass * (1 + 16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * 16)) *
      (1 + Real.log (K : ℝ)) ^ 6 * (K : ℝ) ^ (e_mass - (1 - η)) ≤ (K : ℝ) ^ (-(a + δ / 32)))
    (h6pow : (6 : ℝ) * (K : ℝ) ^ (-(a + δ / 32)) ≤ (K : ℝ) ^ (-a)) :
    let Y_n := 2 * η₀ * (1 + Real.log ((K ^ 2 : ℕ) : ℝ)) +
      (1 + tautMass b (2 * T)) / ((K ^ 2 : ℕ) : ℝ)
    2 * (Y_n * (1 + Real.log (B₀ : ℝ)) + 8 * Y_n * Real.log (K : ℝ) +
      tautMass b (2 * T) / (B₀ : ℝ) +
      (16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * Real.log (K : ℝ) / (B₀ : ℝ)) *
        ((Nat.log 2 (2 * T) : ℝ) + 1) ^ 2 * tautMass b (2 * T)) ≤ (K : ℝ) ^ (-a) := by
  intro Y_n
  have hKR_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKR_ge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
  have hlogK_nn : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR_ge1
  have hlogK2 : 1 + Real.log ((K ^ 2 : ℕ) : ℝ) ≤ 2 * (1 + Real.log (K : ℝ)) := by
    push_cast; rw [Real.log_pow]; push_cast; linarith
  have hYn_bd : Y_n ≤
      4 * C_η₀ * (1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-a') +
        (1 + C_mass) * (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ (e_mass - 2) := by
    dsimp [Y_n]
    have hp1 : 2 * η₀ * (1 + Real.log ((K ^ 2 : ℕ) : ℝ)) ≤
        4 * C_η₀ * (1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-a') := by
      calc 2 * η₀ * (1 + Real.log ((K ^ 2 : ℕ) : ℝ))
          ≤ 2 * (C_η₀ * (K : ℝ) ^ (-a')) * (2 * (1 + Real.log (K : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hη₀_bd (by norm_num)) hlogK2
              (by linarith [Real.log_nonneg (by exact_mod_cast Nat.one_le_pow 2 K (by omega) : (1 : ℝ) ≤ ((K ^ 2 : ℕ) : ℝ))])
              (by positivity)
        _ = 4 * C_η₀ * (1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-a') := by ring
    have hp2 : (1 + tautMass b (2 * T)) / ((K ^ 2 : ℕ) : ℝ) ≤
        (1 + C_mass) * (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ (e_mass - 2) := by
      have h1_le_em : 1 ≤ (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith))
          (Real.one_le_rpow hKR_ge1 hem_nn)
      have hnum : 1 + tautMass b (2 * T) ≤
          (1 + C_mass) * (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass := by
        calc 1 + tautMass b (2 * T)
            ≤ (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass +
                C_mass * (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass :=
              add_le_add h1_le_em hmass_bd
          _ = _ := by ring
      have hdiv_eq : (K : ℝ) ^ e_mass / ((K ^ 2 : ℕ) : ℝ) = (K : ℝ) ^ (e_mass - 2) := by
        push_cast
        rw [sub_eq_add_neg, Real.rpow_add hKR_pos, Real.rpow_neg hKR_pos.le,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      calc (1 + tautMass b (2 * T)) / ((K ^ 2 : ℕ) : ℝ)
          ≤ ((1 + C_mass) * (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass) / ((K ^ 2 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)
        _ = (1 + C_mass) * (1 + Real.log (K : ℝ)) ^ 3 * ((K : ℝ) ^ e_mass / ((K ^ 2 : ℕ) : ℝ)) :=
            mul_div_assoc _ _ _
        _ = _ := by rw [hdiv_eq]
    exact add_le_add hp1 hp2
  have hlogB_le : 1 + Real.log (B₀ : ℝ) + 8 * Real.log (K : ℝ) ≤ 10 * (1 + Real.log (K : ℝ)) := by
    have hBK : (B₀ : ℝ) ≤ (K : ℝ) := by exact_mod_cast hBK_nat
    have hB_pos : (0 : ℝ) < (B₀ : ℝ) := by exact_mod_cast (by omega : 0 < B₀)
    linarith [Real.log_le_log hB_pos hBK]
  have hYn_part : 2 * (Y_n * (1 + Real.log (B₀ : ℝ)) + 8 * Y_n * Real.log (K : ℝ)) ≤
      2 * (K : ℝ) ^ (-(a + δ / 32)) := by
    have hYn_nn : 0 ≤ Y_n := by dsimp [Y_n]; have := tautMass_nonneg b (2 * T); positivity
    have hfactor : 2 * (Y_n * (1 + Real.log (B₀ : ℝ)) + 8 * Y_n * Real.log (K : ℝ)) ≤
        20 * Y_n * (1 + Real.log (K : ℝ)) := by
      calc 2 * (Y_n * (1 + Real.log (B₀ : ℝ)) + 8 * Y_n * Real.log (K : ℝ))
          = 2 * Y_n * (1 + Real.log (B₀ : ℝ) + 8 * Real.log (K : ℝ)) := by ring
        _ ≤ 2 * Y_n * (10 * (1 + Real.log (K : ℝ))) :=
            mul_le_mul_of_nonneg_left hlogB_le (by positivity)
        _ = 20 * Y_n * (1 + Real.log (K : ℝ)) := by ring
    have h2_le_32 : (K : ℝ) ^ (-(a + δ / 2)) ≤ (K : ℝ) ^ (-(a + δ / 32)) :=
      Real.rpow_le_rpow_of_exponent_le hKR_ge1 (by linarith)
    calc 2 * (Y_n * (1 + Real.log (B₀ : ℝ)) + 8 * Y_n * Real.log (K : ℝ))
        ≤ 20 * (4 * C_η₀ * (1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-a') +
            (1 + C_mass) * (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ (e_mass - 2)) *
            (1 + Real.log (K : ℝ)) :=
          hfactor.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hYn_bd (by norm_num)) (by linarith))
      _ ≤ (80 * C_η₀) * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (-a') +
            (80 * (1 + C_mass)) * (1 + Real.log (K : ℝ)) ^ 5 * (K : ℝ) ^ (e_mass - 2) := by
          have hlog35 : (1 + Real.log (K : ℝ)) ^ 4 ≤ (1 + Real.log (K : ℝ)) ^ 5 :=
            pow_le_pow_right₀ (by linarith) (by omega)
          have hpos_m : 0 ≤ (1 + C_mass) * (K : ℝ) ^ (e_mass - 2) := by positivity
          have hm1 : 20 * (1 + C_mass) * (1 + Real.log (K : ℝ)) ^ 4 * (K : ℝ) ^ (e_mass - 2) ≤
              (80 * (1 + C_mass)) * (1 + Real.log (K : ℝ)) ^ 5 * (K : ℝ) ^ (e_mass - 2) := by
            calc 20 * (1 + C_mass) * (1 + Real.log (K : ℝ)) ^ 4 * (K : ℝ) ^ (e_mass - 2)
                = (20 * ((1 + C_mass) * (K : ℝ) ^ (e_mass - 2))) * (1 + Real.log (K : ℝ)) ^ 4 := by ring
              _ ≤ (80 * ((1 + C_mass) * (K : ℝ) ^ (e_mass - 2))) * (1 + Real.log (K : ℝ)) ^ 5 :=
                  mul_le_mul (by linarith only [hpos_m]) hlog35 (by positivity) (by positivity)
              _ = _ := by ring
          linarith only [hm1]
      _ ≤ (K : ℝ) ^ (-(a + δ / 2)) + (K : ℝ) ^ (-(a + δ / 2)) := add_le_add hr1 hr2
      _ ≤ 2 * (K : ℝ) ^ (-(a + δ / 32)) := by linarith only [h2_le_32]
  have hmass_part : 2 * (tautMass b (2 * T) / (B₀ : ℝ) +
      (16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * Real.log (K : ℝ) / (B₀ : ℝ)) *
        ((Nat.log 2 (2 * T) : ℝ) + 1) ^ 2 * tautMass b (2 * T)) ≤
      2 * (K : ℝ) ^ (-(a + δ / 32)) := by
    have hlog2_bd : (Nat.log 2 (2 * T) : ℝ) + 1 ≤ 4 * (1 + Real.log (K : ℝ)) := by
      have h1 : 2 ^ Nat.log 2 (2 * T) ≤ K :=
        (Nat.pow_log_le_self 2 (by omega)).trans h2T_le_K
      have h2 := Real.log_le_log (by positivity) (by exact_mod_cast h1 : ((2 : ℝ)) ^ Nat.log 2 (2 * T) ≤ K)
      rw [Real.log_pow] at h2
      have hl2 : (2 / 3 : ℝ) * (Nat.log 2 (2 * T) : ℝ) ≤
          (Nat.log 2 (2 * T) : ℝ) * Real.log 2 := by
        rw [mul_comm (2 / 3 : ℝ)]
        exact mul_le_mul_of_nonneg_left (by linarith [Real.log_two_gt_d9]) (Nat.cast_nonneg _)
      linarith only [h2, hl2]
    have hsq_log2 : ((Nat.log 2 (2 * T) : ℝ) + 1) ^ 2 ≤ 16 * (1 + Real.log (K : ℝ)) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hlog2_bd 2
      linarith
    have hB_inv : 1 / (B₀ : ℝ) ≤ (2 * (D_W : ℝ)) * (K : ℝ) ^ (-(1 - η)) := by
      have hB_pos : (0 : ℝ) < (B₀ : ℝ) := by exact_mod_cast (by omega : 0 < B₀)
      rw [div_le_iff₀ hB_pos]
      have hcan : (2 * (D_W : ℝ)) * (K : ℝ) ^ (-(1 - η)) *
          ((1 / (2 * (D_W : ℝ))) * (K : ℝ) ^ (1 - η)) = 1 := by
        have hp : (K : ℝ) ^ (-(1 - η)) * (K : ℝ) ^ (1 - η) = 1 := by
          rw [← Real.rpow_add hKR_pos]; simp
        calc _ = ((2 * (D_W : ℝ)) * (1 / (2 * (D_W : ℝ)))) *
              ((K : ℝ) ^ (-(1 - η)) * (K : ℝ) ^ (1 - η)) := by ring
          _ = 1 := by rw [mul_one_div_cancel (by positivity), hp, mul_one]
      calc (1 : ℝ) = (2 * (D_W : ℝ)) * (K : ℝ) ^ (-(1 - η)) *
              ((1 / (2 * (D_W : ℝ))) * (K : ℝ) ^ (1 - η)) := hcan.symm
        _ ≤ (2 * (D_W : ℝ)) * (K : ℝ) ^ (-(1 - η)) * (B₀ : ℝ) :=
            mul_le_mul_of_nonneg_left hB₀_lo_R (by positivity)
    have hm_div_B : tautMass b (2 * T) / (B₀ : ℝ) ≤
        (2 * (D_W : ℝ) * C_mass) * (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ (e_mass - (1 - η)) := by
      calc tautMass b (2 * T) / (B₀ : ℝ)
          = tautMass b (2 * T) * (1 / (B₀ : ℝ)) := div_eq_mul_one_div _ _
        _ ≤ (C_mass * (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass) *
              ((2 * (D_W : ℝ)) * (K : ℝ) ^ (-(1 - η))) :=
            mul_le_mul hmass_bd hB_inv (by positivity) (by positivity)
        _ = (2 * (D_W : ℝ) * C_mass) * (1 + Real.log (K : ℝ)) ^ 3 *
              ((K : ℝ) ^ e_mass * (K : ℝ) ^ (-(1 - η))) := by ring
        _ = (2 * (D_W : ℝ) * C_mass) * (1 + Real.log (K : ℝ)) ^ 3 *
              (K : ℝ) ^ (e_mass - (1 - η)) := by
            rw [← Real.rpow_add hKR_pos, ← sub_eq_add_neg]
    set Q_mult : ℝ := 16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ)
    have hQ_nn : 0 ≤ Q_mult := by dsimp [Q_mult]; positivity
    have hbrack : 1 + Q_mult * Real.log (K : ℝ) * ((Nat.log 2 (2 * T) : ℝ) + 1) ^ 2 ≤
        (1 + Q_mult * 16) * (1 + Real.log (K : ℝ)) ^ 3 := by
      have hlog_le1 : Real.log (K : ℝ) ≤ 1 + Real.log (K : ℝ) := by linarith
      have h1_le3 : 1 ≤ (1 + Real.log (K : ℝ)) ^ 3 := one_le_pow₀ (by linarith)
      have hmul_l : Real.log (K : ℝ) * ((Nat.log 2 (2 * T) : ℝ) + 1) ^ 2 ≤
          16 * (1 + Real.log (K : ℝ)) ^ 3 := by
        calc Real.log (K : ℝ) * ((Nat.log 2 (2 * T) : ℝ) + 1) ^ 2
            ≤ (1 + Real.log (K : ℝ)) * (16 * (1 + Real.log (K : ℝ)) ^ 2) :=
              mul_le_mul hlog_le1 hsq_log2 (by positivity) (by linarith)
          _ = 16 * (1 + Real.log (K : ℝ)) ^ 3 := by ring
      calc 1 + Q_mult * Real.log (K : ℝ) * ((Nat.log 2 (2 * T) : ℝ) + 1) ^ 2
          = 1 + Q_mult * (Real.log (K : ℝ) * ((Nat.log 2 (2 * T) : ℝ) + 1) ^ 2) := by ring
        _ ≤ (1 + Real.log (K : ℝ)) ^ 3 + Q_mult * (16 * (1 + Real.log (K : ℝ)) ^ 3) :=
            add_le_add h1_le3 (mul_le_mul_of_nonneg_left hmul_l hQ_nn)
        _ = (1 + Q_mult * 16) * (1 + Real.log (K : ℝ)) ^ 3 := by ring
    have hcomb_m : tautMass b (2 * T) / (B₀ : ℝ) +
        (Q_mult * Real.log (K : ℝ) / (B₀ : ℝ)) *
          ((Nat.log 2 (2 * T) : ℝ) + 1) ^ 2 * tautMass b (2 * T) ≤
        (2 * (D_W : ℝ) * C_mass * (1 + Q_mult * 16)) *
          (1 + Real.log (K : ℝ)) ^ 6 * (K : ℝ) ^ (e_mass - (1 - η)) := by
      calc tautMass b (2 * T) / (B₀ : ℝ) +
            (Q_mult * Real.log (K : ℝ) / (B₀ : ℝ)) *
              ((Nat.log 2 (2 * T) : ℝ) + 1) ^ 2 * tautMass b (2 * T)
          = (tautMass b (2 * T) / (B₀ : ℝ)) *
              (1 + Q_mult * Real.log (K : ℝ) * ((Nat.log 2 (2 * T) : ℝ) + 1) ^ 2) := by ring
        _ ≤ ((2 * (D_W : ℝ) * C_mass) * (1 + Real.log (K : ℝ)) ^ 3 *
              (K : ℝ) ^ (e_mass - (1 - η))) *
              ((1 + Q_mult * 16) * (1 + Real.log (K : ℝ)) ^ 3) :=
            mul_le_mul hm_div_B hbrack (by positivity) (by positivity)
        _ = (2 * (D_W : ℝ) * C_mass * (1 + Q_mult * 16)) *
              (1 + Real.log (K : ℝ)) ^ 6 * (K : ℝ) ^ (e_mass - (1 - η)) := by ring
    have hcomb_le := hcomb_m.trans hr3
    dsimp [Q_mult] at hcomb_le
    linarith only [hcomb_le]
  have hsum_all : 2 * (Y_n * (1 + Real.log (B₀ : ℝ)) + 8 * Y_n * Real.log (K : ℝ) +
      tautMass b (2 * T) / (B₀ : ℝ) +
      (16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * Real.log (K : ℝ) / (B₀ : ℝ)) *
        ((Nat.log 2 (2 * T) : ℝ) + 1) ^ 2 * tautMass b (2 * T)) ≤
      6 * (K : ℝ) ^ (-(a + δ / 32)) := by
    have hpos : 0 ≤ (K : ℝ) ^ (-(a + δ / 32)) := by positivity
    linarith only [hYn_part, hmass_part, hpos]
  exact hsum_all.trans h6pow

/-- Tracking-error bound `C₂ * (1 / y + T^{-(1 - Θ - ε)}) ≤ (4 * C₂) * K^{-a'}` at `(y, T)`. -/
private lemma hasRate_eta_bd {K y T : ℕ} {Θ ε a' τ_exp C₂ : ℝ}
    (hKR_pos : (0 : ℝ) < (K : ℝ)) (hy_pos : 0 < y)
    (hy_lo_R : (1 / 2 : ℝ) * (K : ℝ) ^ a' ≤ (y : ℝ))
    (hT_lo_R : (1 / 2 : ℝ) / 2 * (K : ℝ) ^ τ_exp ≤ (T : ℝ))
    (hden_pos : 0 < 1 - Θ - ε) (hden_le_half : 1 - Θ - ε ≤ 1 / 2)
    (hτ_mert : τ_exp * (1 - Θ - ε) = a') (hC₂ : 0 < C₂) :
    C₂ * (1 / (y : ℝ) + (T : ℝ) ^ (-(1 - Θ - ε))) ≤ (4 * C₂) * (K : ℝ) ^ (-a') := by
  have hy_inv : 1 / (y : ℝ) ≤ 2 * (K : ℝ) ^ (-a') := by
    have hy_pos_R : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy_pos
    rw [div_le_iff₀ hy_pos_R]
    have hcan : (K : ℝ) ^ (-a') * (K : ℝ) ^ a' = 1 := by
      rw [← Real.rpow_add hKR_pos, neg_add_cancel, Real.rpow_zero]
    calc (1 : ℝ) = 2 * (K : ℝ) ^ (-a') * ((1 / 2) * (K : ℝ) ^ a') := by
          calc (1 : ℝ) = (K : ℝ) ^ (-a') * (K : ℝ) ^ a' := hcan.symm
            _ = _ := by ring
      _ ≤ 2 * (K : ℝ) ^ (-a') * (y : ℝ) :=
          mul_le_mul_of_nonneg_left hy_lo_R (by positivity)
  have hT_pow_bd : (T : ℝ) ^ (-(1 - Θ - ε)) ≤ 2 * (K : ℝ) ^ (-a') := by
    have hT_ge_q : (1 / 4 : ℝ) * (K : ℝ) ^ τ_exp ≤ (T : ℝ) := by
      linarith only [hT_lo_R]
    have h1 : (T : ℝ) ^ (-(1 - Θ - ε)) ≤
        ((1 / 4 : ℝ) * (K : ℝ) ^ τ_exp) ^ (-(1 - Θ - ε)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hT_ge_q (by linarith)
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hKR_pos.le] at h1
    have hexp_eq : τ_exp * -(1 - Θ - ε) = -a' := by linarith [hτ_mert]
    have h4_le : (1 / 4 : ℝ) ^ (-(1 - Θ - ε)) ≤ 2 := by
      have h4eq : (1 / 4 : ℝ) ^ (-(1 - Θ - ε)) = (4 : ℝ) ^ (1 - Θ - ε) := by
        rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
      rw [h4eq]
      calc (4 : ℝ) ^ (1 - Θ - ε) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hden_le_half
        _ = 2 := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
              ← Real.rpow_mul (by norm_num)]
            norm_num
    rw [hexp_eq] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h4_le (by positivity))
  calc C₂ * (1 / (y : ℝ) + (T : ℝ) ^ (-(1 - Θ - ε)))
      ≤ C₂ * (2 * (K : ℝ) ^ (-a') + 2 * (K : ℝ) ^ (-a')) :=
        mul_le_mul_of_nonneg_left (add_le_add hy_inv hT_pow_bd) hC₂.le
    _ = (4 * C₂) * (K : ℝ) ^ (-a') := by ring

/-- Taut-mass bound `tautMass b (2 * T) ≤ (3 * C₁) * (1 + log K)^3 * K^{e_mass}`. -/
private lemma hasRate_tautMass_bd {b : ℕ → ℤ} {K y T : ℕ} {Θ ε a' τ_exp e_mass C₁ : ℝ}
    (hK4 : 4 ≤ K) (hy_pos : 0 < y) (hT_ge2 : 2 ≤ T) (h2T_le_K : 2 * T ≤ K)
    (hΘ : 1 / 2 ≤ Θ) (hε_pos : 0 < ε) (hC₁ : 0 < C₁)
    (hy_lo_R : (1 / 2 : ℝ) * (K : ℝ) ^ a' ≤ (y : ℝ))
    (hy_hi_R : (y : ℝ) ≤ (K : ℝ) ^ a')
    (hT_hi_R : (T : ℝ) ≤ (1 / 2 : ℝ) * (K : ℝ) ^ τ_exp)
    (hτ_sub_a' : τ_exp - a' = τ_exp * (Θ + ε))
    (he1_le : a' * (1 + 2 * ε) + τ_exp * (2 * (Θ + ε) - 1) ≤ e_mass)
    (he2_le : τ_exp * (Θ + ε) ≤ e_mass)
    (hmass_raw : ∑ k ∈ Icc 1 (2 * T), |(b k : ℝ)| ≤
      C₁ * ((1 + Real.log (T : ℝ)) ^ 3 * (y : ℝ) ^ (1 + 2 * ε) *
        (T : ℝ) ^ (2 * (Θ + ε) - 1) +
        (1 + Real.log (T : ℝ)) * ((T : ℝ) / (y : ℝ)) + (T : ℝ) ^ (Θ + ε))) :
    tautMass b (2 * T) ≤ (3 * C₁) * (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass := by
  have hKR_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKR_ge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
  have hlogK_nn : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR_ge1
  have hsub_Icc : tautMass b (2 * T) ≤ ∑ k ∈ Icc 1 (2 * T), |(b k : ℝ)| :=
    sum_le_sum_of_subset_of_nonneg
      (fun k hk => mem_Icc.mpr ⟨by have := (mem_Icc.mp hk).1; omega, (mem_Icc.mp hk).2⟩)
      fun _ _ _ => abs_nonneg _
  have hTK_le : (T : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : T ≤ K)
  have hT_pos_R : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hlogT_le : 1 + Real.log (T : ℝ) ≤ 1 + Real.log (K : ℝ) := by
    linarith [Real.log_le_log hT_pos_R hTK_le]
  have hT_pow_K : (T : ℝ) ≤ (K : ℝ) ^ τ_exp :=
    hT_hi_R.trans (by linarith [Real.rpow_pos_of_pos hKR_pos τ_exp])
  have ht1 : (1 + Real.log (T : ℝ)) ^ 3 * (y : ℝ) ^ (1 + 2 * ε) *
      (T : ℝ) ^ (2 * (Θ + ε) - 1) ≤
      (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass := by
    have hp_log : (1 + Real.log (T : ℝ)) ^ 3 ≤ (1 + Real.log (K : ℝ)) ^ 3 :=
      pow_le_pow_left₀
        (by linarith [Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T) : (1 : ℝ) ≤ T)])
        hlogT_le 3
    have hp_y : (y : ℝ) ^ (1 + 2 * ε) ≤ (K : ℝ) ^ (a' * (1 + 2 * ε)) := by
      calc (y : ℝ) ^ (1 + 2 * ε) ≤ ((K : ℝ) ^ a') ^ (1 + 2 * ε) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hy_hi_R (by positivity)
        _ = (K : ℝ) ^ (a' * (1 + 2 * ε)) := (Real.rpow_mul hKR_pos.le _ _).symm
    have hp_T : (T : ℝ) ^ (2 * (Θ + ε) - 1) ≤ (K : ℝ) ^ (τ_exp * (2 * (Θ + ε) - 1)) := by
      calc (T : ℝ) ^ (2 * (Θ + ε) - 1) ≤ ((K : ℝ) ^ τ_exp) ^ (2 * (Θ + ε) - 1) :=
            Real.rpow_le_rpow hT_pos_R.le hT_pow_K (by linarith)
        _ = (K : ℝ) ^ (τ_exp * (2 * (Θ + ε) - 1)) := (Real.rpow_mul hKR_pos.le _ _).symm
    have hp_yT : (y : ℝ) ^ (1 + 2 * ε) * (T : ℝ) ^ (2 * (Θ + ε) - 1) ≤ (K : ℝ) ^ e_mass := by
      calc _ ≤ (K : ℝ) ^ (a' * (1 + 2 * ε)) * (K : ℝ) ^ (τ_exp * (2 * (Θ + ε) - 1)) :=
            mul_le_mul hp_y hp_T (by positivity) (by positivity)
        _ = (K : ℝ) ^ (a' * (1 + 2 * ε) + τ_exp * (2 * (Θ + ε) - 1)) :=
            (Real.rpow_add hKR_pos _ _).symm
        _ ≤ (K : ℝ) ^ e_mass := Real.rpow_le_rpow_of_exponent_le hKR_ge1 he1_le
    calc (1 + Real.log (T : ℝ)) ^ 3 * (y : ℝ) ^ (1 + 2 * ε) * (T : ℝ) ^ (2 * (Θ + ε) - 1)
        = (1 + Real.log (T : ℝ)) ^ 3 *
            ((y : ℝ) ^ (1 + 2 * ε) * (T : ℝ) ^ (2 * (Θ + ε) - 1)) := by ring
      _ ≤ (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass :=
          mul_le_mul hp_log hp_yT (by positivity) (by positivity)
  have ht2 : (1 + Real.log (T : ℝ)) * ((T : ℝ) / (y : ℝ)) ≤
      (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass := by
    have hTy : (T : ℝ) / (y : ℝ) ≤ (K : ℝ) ^ e_mass := by
      have hy_pos_R : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy_pos
      have hdiv : (T : ℝ) / (y : ℝ) ≤
          ((1 / 2 : ℝ) * (K : ℝ) ^ τ_exp) / ((1 / 2 : ℝ) * (K : ℝ) ^ a') :=
        div_le_div₀ (by positivity) hT_hi_R (by positivity) hy_lo_R
      have hcan : ((1 / 2 : ℝ) * (K : ℝ) ^ τ_exp) / ((1 / 2 : ℝ) * (K : ℝ) ^ a') =
          (K : ℝ) ^ (τ_exp - a') := by
        rw [mul_div_mul_left _ _ (by norm_num), sub_eq_add_neg, Real.rpow_add hKR_pos,
          Real.rpow_neg hKR_pos.le]
        ring
      rw [hcan, hτ_sub_a'] at hdiv
      exact hdiv.trans (Real.rpow_le_rpow_of_exponent_le hKR_ge1 he2_le)
    have hlog13 : 1 + Real.log (T : ℝ) ≤ (1 + Real.log (K : ℝ)) ^ 3 := by
      have h1 : 1 ≤ (1 + Real.log (K : ℝ)) ^ 2 := one_le_pow₀ (by linarith)
      calc 1 + Real.log (T : ℝ) ≤ (1 + Real.log (K : ℝ)) * 1 := by linarith
        _ ≤ (1 + Real.log (K : ℝ)) * (1 + Real.log (K : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = (1 + Real.log (K : ℝ)) ^ 3 := by ring
    exact mul_le_mul hlog13 hTy (by positivity) (by positivity)
  have ht3 : (T : ℝ) ^ (Θ + ε) ≤ (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass := by
    have hp : (T : ℝ) ^ (Θ + ε) ≤ (K : ℝ) ^ e_mass := by
      calc (T : ℝ) ^ (Θ + ε) ≤ ((K : ℝ) ^ τ_exp) ^ (Θ + ε) :=
            Real.rpow_le_rpow hT_pos_R.le hT_pow_K (by linarith)
        _ = (K : ℝ) ^ (τ_exp * (Θ + ε)) := (Real.rpow_mul hKR_pos.le _ _).symm
        _ ≤ (K : ℝ) ^ e_mass := Real.rpow_le_rpow_of_exponent_le hKR_ge1 he2_le
    have h1 : 1 ≤ (1 + Real.log (K : ℝ)) ^ 3 := one_le_pow₀ (by linarith)
    calc (T : ℝ) ^ (Θ + ε) = 1 * (T : ℝ) ^ (Θ + ε) := (one_mul _).symm
      _ ≤ (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass :=
          mul_le_mul h1 hp (by positivity) (by positivity)
  calc tautMass b (2 * T) ≤ ∑ k ∈ Icc 1 (2 * T), |(b k : ℝ)| := hsub_Icc
    _ ≤ C₁ * ((1 + Real.log (T : ℝ)) ^ 3 * (y : ℝ) ^ (1 + 2 * ε) *
          (T : ℝ) ^ (2 * (Θ + ε) - 1) +
          (1 + Real.log (T : ℝ)) * ((T : ℝ) / (y : ℝ)) + (T : ℝ) ^ (Θ + ε)) := hmass_raw
    _ ≤ C₁ * (3 * ((1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass)) :=
        mul_le_mul_of_nonneg_left (by linarith only [ht1, ht2, ht3]) hC₁.le
    _ = (3 * C₁) * (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass := by ring

/-- Scale-compatibility bounds for `(y, T, W, B₀)` at a fixed large alphabet bound `K`. -/
private lemma hasRate_scale_checks {K y T W d M₀ S D_W B₀ : ℕ} {a' τ_exp η : ℝ}
    (hK4 : 4 ≤ K) (ha'_pos : 0 < a') (hτ_lt1 : τ_exp < 1) (hS_pos : 1 ≤ S)
    (hDW_pos_nat : 0 < D_W) (hW_ge2 : 2 ≤ W)
    (hy_def : y = ⌊(K : ℝ) ^ a'⌋₊) (hB₀_def : B₀ = K / (D_W * W))
    (hy_lo_R : (1 / 2 : ℝ) * (K : ℝ) ^ a' ≤ (y : ℝ)) (hy_hi_R : (y : ℝ) ≤ (K : ℝ) ^ a')
    (hT_lo_R : (1 / 2 : ℝ) / 2 * (K : ℝ) ^ τ_exp ≤ (T : ℝ))
    (hT_hi_R : (T : ℝ) ≤ (1 / 2 : ℝ) * (K : ℝ) ^ τ_exp)
    (hW_lo_R : (1 / 2 : ℝ) * (K : ℝ) ^ η ≤ (W : ℝ)) (hW_hi_R : (W : ℝ) ≤ (K : ℝ) ^ η)
    (hymin : (tautStencilMinY d : ℝ) + 1 ≤ (K : ℝ) ^ a')
    (hyT : 4 * (smoothJumpBase d : ℝ) * (K : ℝ) ^ a' ≤ (K : ℝ) ^ τ_exp)
    (hTyd : (2 : ℝ) ^ (d + 1) * (K : ℝ) ^ τ_exp ≤ (K : ℝ) ^ (a' * ((d + 1 : ℕ) : ℝ)))
    (hmlo : ((2 ^ S : ℕ) : ℝ) * (K : ℝ) ^ η ≤ (K : ℝ))
    (hmhi : 2 * (K : ℝ) ≤ (K : ℝ) ^ (η * (M₀ : ℝ)))
    (hB₀_ev : 4 * (D_W : ℝ) * (K : ℝ) ^ η ≤ (K : ℝ))
    (hsq_ev : ((2 ^ (2 * S + 2) : ℕ) : ℝ) * ((smoothJumpPrimeBound d + 1 : ℕ) : ℝ) *
      (K : ℝ) ^ (2 * η + a') ≤ (K : ℝ)) :
    tautStencilMinY d ≤ y ∧ smoothJumpBase d * y ≤ T ∧ T ≤ y ^ (d + 1) ∧
      2 * T ≤ K ∧ 1 ≤ Nat.log (2 ^ S * W) K ∧ Nat.log (2 ^ S * W) K < M₀ ∧
      2 ≤ B₀ ∧ (1 / (2 * (D_W : ℝ))) * (K : ℝ) ^ (1 - η) ≤ (B₀ : ℝ) ∧
      2 ^ (2 * S + 2) * W ^ 2 * (smoothJumpPrimeBound d * y + 1) ≤ K := by
  have hKR_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKR_ge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
  have hDW_pos : (0 : ℝ) < (D_W : ℝ) := by exact_mod_cast hDW_pos_nat
  have hy_min : tautStencilMinY d ≤ y := by
    rw [hy_def]
    exact Nat.le_floor ((by linarith : (tautStencilMinY d : ℝ) ≤ tautStencilMinY d + 1).trans hymin)
  have hT_lo : smoothJumpBase d * y ≤ T := by
    have hR : ((smoothJumpBase d * y : ℕ) : ℝ) ≤ (T : ℝ) := by
      push_cast
      calc (smoothJumpBase d : ℝ) * (y : ℝ)
          ≤ (smoothJumpBase d : ℝ) * (K : ℝ) ^ a' :=
            mul_le_mul_of_nonneg_left hy_hi_R (Nat.cast_nonneg _)
        _ ≤ (1 / 4 : ℝ) * (K : ℝ) ^ τ_exp := by linarith only [hyT]
        _ ≤ (T : ℝ) := by linarith only [hT_lo_R]
    exact_mod_cast hR
  have hT_hi : T ≤ y ^ (d + 1) := by
    have hR : (T : ℝ) ≤ ((y ^ (d + 1) : ℕ) : ℝ) := by
      push_cast
      have hpow_y : ((1 / 2 : ℝ) * (K : ℝ) ^ a') ^ (d + 1) ≤ (y : ℝ) ^ (d + 1) :=
        pow_le_pow_left₀ (by positivity) hy_lo_R (d + 1)
      rw [mul_pow, ← Real.rpow_natCast ((K : ℝ) ^ a') (d + 1), ← Real.rpow_mul hKR_pos.le] at hpow_y
      have h1 : (T : ℝ) ≤ (K : ℝ) ^ τ_exp :=
        hT_hi_R.trans (by linarith [Real.rpow_pos_of_pos hKR_pos τ_exp])
      have h2 : (K : ℝ) ^ τ_exp ≤ (1 / 2 : ℝ) ^ (d + 1) * (K : ℝ) ^ (a' * ((d + 1 : ℕ) : ℝ)) := by
        have hp := mul_le_mul_of_nonneg_left hTyd ((pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (d + 1)).le)
        have hcan : (1 / 2 : ℝ) ^ (d + 1) * ((2 : ℝ) ^ (d + 1) * (K : ℝ) ^ τ_exp) =
            (K : ℝ) ^ τ_exp := by
          rw [← mul_assoc, ← mul_pow]; norm_num
        rwa [hcan] at hp
      exact h1.trans (h2.trans hpow_y)
    exact_mod_cast hR
  have h2T_le_K : 2 * T ≤ K := by
    have hR : ((2 * T : ℕ) : ℝ) ≤ (K : ℝ) := by
      push_cast
      calc 2 * (T : ℝ) ≤ 2 * ((1 / 2 : ℝ) * (K : ℝ) ^ τ_exp) :=
            mul_le_mul_of_nonneg_left hT_hi_R (by norm_num)
        _ = (K : ℝ) ^ τ_exp := by ring
        _ ≤ (K : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hKR_ge1 hτ_lt1.le
        _ = (K : ℝ) := Real.rpow_one _
    exact_mod_cast hR
  have hm_lo : 1 ≤ Nat.log (2 ^ S * W) K := by
    refine Nat.le_log_of_pow_le (by
      calc 1 < 1 * 2 := by omega
        _ ≤ 2 ^ S * W := Nat.mul_le_mul Nat.one_le_two_pow hW_ge2) ?_
    rw [pow_one]
    have hR : ((2 ^ S * W : ℕ) : ℝ) ≤ (K : ℝ) := by
      push_cast at hmlo ⊢
      exact (mul_le_mul_of_nonneg_left hW_hi_R (by positivity)).trans hmlo
    exact_mod_cast hR
  have hm_hi : Nat.log (2 ^ S * W) K < M₀ := by
    refine Nat.log_lt_of_lt_pow (by omega) ?_
    have hR : (K : ℝ) < (((2 ^ S * W) ^ M₀ : ℕ) : ℝ) := by
      push_cast
      have h2S_ge2 : (2 : ℝ) ≤ (2 : ℝ) ^ S := by
        calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ) := (pow_one 2).symm
          _ ≤ (2 : ℝ) ^ S := pow_le_pow_right₀ (by norm_num) hS_pos
      have hbase_ge : (K : ℝ) ^ η ≤ (2 : ℝ) ^ S * (W : ℝ) := by
        calc (K : ℝ) ^ η = 2 * ((1 / 2 : ℝ) * (K : ℝ) ^ η) := by ring
          _ ≤ (2 : ℝ) ^ S * (W : ℝ) :=
              mul_le_mul h2S_ge2 hW_lo_R (by positivity) (by positivity)
      have hpow_ge : (K : ℝ) ^ (η * (M₀ : ℝ)) ≤ ((2 : ℝ) ^ S * (W : ℝ)) ^ M₀ := by
        rw [Real.rpow_mul hKR_pos.le, Real.rpow_natCast]
        exact pow_le_pow_left₀ (by positivity) hbase_ge M₀
      have hlt2 : (K : ℝ) < 2 * (K : ℝ) := by linarith
      exact lt_of_lt_of_le hlt2 (hmhi.trans hpow_ge)
    exact_mod_cast hR
  have hDW_W_le : (D_W : ℝ) * (W : ℝ) ≤ (D_W : ℝ) * (K : ℝ) ^ η :=
    mul_le_mul_of_nonneg_left hW_hi_R hDW_pos.le
  have hB₀_ge2 : 2 ≤ B₀ := by
    rw [hB₀_def]
    refine (Nat.le_div_iff_mul_le (Nat.mul_pos hDW_pos_nat (by omega))).mpr ?_
    have hR : ((2 * (D_W * W) : ℕ) : ℝ) ≤ (K : ℝ) := by
      push_cast
      calc 2 * ((D_W : ℝ) * (W : ℝ)) ≤ 4 * (D_W : ℝ) * (K : ℝ) ^ η := by
            linarith [hDW_W_le, mul_nonneg hDW_pos.le (Real.rpow_nonneg hKR_pos.le η)]
        _ ≤ (K : ℝ) := hB₀_ev
    exact_mod_cast hR
  have hB₀_lo_R : (1 / (2 * (D_W : ℝ))) * (K : ℝ) ^ (1 - η) ≤ (B₀ : ℝ) := by
    have hden_R : 0 < (D_W : ℝ) * (W : ℝ) := mul_pos hDW_pos (by exact_mod_cast (by omega : 0 < W))
    have hlt_succ : (K : ℝ) < ((D_W * W : ℕ) : ℝ) * ((B₀ : ℝ) + 1) := by
      rw [hB₀_def]
      exact_mod_cast Nat.lt_mul_div_succ K (Nat.mul_pos hDW_pos_nat (by omega))
    have hdiv_le : (K : ℝ) / ((D_W : ℝ) * (K : ℝ) ^ η) ≤ (B₀ : ℝ) + 1 := by
      calc (K : ℝ) / ((D_W : ℝ) * (K : ℝ) ^ η)
          ≤ (K : ℝ) / ((D_W : ℝ) * (W : ℝ)) :=
            div_le_div_of_nonneg_left hKR_pos.le hden_R hDW_W_le
        _ ≤ (B₀ : ℝ) + 1 := by
            rw [div_le_iff₀ hden_R]
            push_cast at hlt_succ
            linarith only [hlt_succ]
    have hdiv_eq : (K : ℝ) / ((D_W : ℝ) * (K : ℝ) ^ η) =
        (1 / (D_W : ℝ)) * (K : ℝ) ^ (1 - η) := by
      rw [sub_eq_add_neg, Real.rpow_add hKR_pos, Real.rpow_one, Real.rpow_neg hKR_pos.le]
      field_simp [hDW_pos.ne']
    rw [hdiv_eq] at hdiv_le
    have hge2 : 2 ≤ (1 / (D_W : ℝ)) * (K : ℝ) ^ (1 - η) := by
      have hm := mul_le_mul_of_nonneg_left hB₀_ev
        (by positivity : 0 ≤ (1 / (D_W : ℝ)) * (K : ℝ) ^ (-η))
      have hcan : (K : ℝ) ^ (-η) * (K : ℝ) ^ η = 1 := by
        rw [← Real.rpow_add hKR_pos, neg_add_cancel, Real.rpow_zero]
      have heq1 : (1 / (D_W : ℝ)) * (K : ℝ) ^ (-η) * (4 * (D_W : ℝ) * (K : ℝ) ^ η) = 4 := by
        calc (1 / (D_W : ℝ)) * (K : ℝ) ^ (-η) * (4 * (D_W : ℝ) * (K : ℝ) ^ η)
            = 4 * ((1 / (D_W : ℝ)) * (D_W : ℝ)) * ((K : ℝ) ^ (-η) * (K : ℝ) ^ η) := by ring
          _ = 4 := by rw [one_div_mul_cancel hDW_pos.ne', hcan]; ring
      have heq2 : (1 / (D_W : ℝ)) * (K : ℝ) ^ (-η) * (K : ℝ) =
          (1 / (D_W : ℝ)) * (K : ℝ) ^ (1 - η) := by
        rw [sub_eq_add_neg, Real.rpow_add hKR_pos, Real.rpow_one]; ring
      rw [heq1, heq2] at hm
      linarith only [hm]
    have hhalf_eq : (1 / (2 * (D_W : ℝ))) * (K : ℝ) ^ (1 - η) =
        (1 / 2 : ℝ) * ((1 / (D_W : ℝ)) * (K : ℝ) ^ (1 - η)) := by ring
    rw [hhalf_eq]
    linarith only [hdiv_le, hge2]
  have hK_sq : 2 ^ (2 * S + 2) * W ^ 2 * (smoothJumpPrimeBound d * y + 1) ≤ K := by
    have hR : ((2 ^ (2 * S + 2) * W ^ 2 * (smoothJumpPrimeBound d * y + 1) : ℕ) : ℝ) ≤ (K : ℝ) := by
      push_cast
      have hW2 : (W : ℝ) ^ 2 ≤ (K : ℝ) ^ (2 * η) := by
        calc (W : ℝ) ^ 2 ≤ ((K : ℝ) ^ η) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hW_hi_R 2
          _ = (K : ℝ) ^ (2 * η) := by
              rw [← Real.rpow_natCast ((K : ℝ) ^ η) 2, ← Real.rpow_mul hKR_pos.le]
              congr 1; push_cast; ring
      have hy_p : (smoothJumpPrimeBound d : ℝ) * (y : ℝ) + 1 ≤
          ((smoothJumpPrimeBound d + 1 : ℕ) : ℝ) * (K : ℝ) ^ a' := by
        have h1a : 1 ≤ (K : ℝ) ^ a' := Real.one_le_rpow hKR_ge1 ha'_pos.le
        push_cast
        calc (smoothJumpPrimeBound d : ℝ) * (y : ℝ) + 1
            ≤ (smoothJumpPrimeBound d : ℝ) * (K : ℝ) ^ a' + (K : ℝ) ^ a' :=
              add_le_add (mul_le_mul_of_nonneg_left hy_hi_R (Nat.cast_nonneg _)) h1a
          _ = ((smoothJumpPrimeBound d : ℝ) + 1) * (K : ℝ) ^ a' := by ring
      calc (2 ^ (2 * S + 2) : ℝ) * (W : ℝ) ^ 2 * ((smoothJumpPrimeBound d : ℝ) * (y : ℝ) + 1)
          ≤ (2 ^ (2 * S + 2) : ℝ) * (K : ℝ) ^ (2 * η) *
              (((smoothJumpPrimeBound d + 1 : ℕ) : ℝ) * (K : ℝ) ^ a') :=
            mul_le_mul (mul_le_mul_of_nonneg_left hW2 (by positivity)) hy_p
              (by positivity) (by positivity)
        _ = (((2 ^ (2 * S + 2) : ℕ) : ℝ) * ((smoothJumpPrimeBound d + 1 : ℕ) : ℝ)) *
              ((K : ℝ) ^ (2 * η) * (K : ℝ) ^ a') := by push_cast; ring
        _ = (((2 ^ (2 * S + 2) : ℕ) : ℝ) * ((smoothJumpPrimeBound d + 1 : ℕ) : ℝ)) *
              (K : ℝ) ^ (2 * η + a') := by rw [← Real.rpow_add hKR_pos]
        _ ≤ (K : ℝ) := hsq_ev
    exact_mod_cast hR
  exact ⟨hy_min, hT_lo, hT_hi, h2T_le_K, hm_lo, hm_hi, hB₀_ge2, hB₀_lo_R, hK_sq⟩

/-- **Full-scale rate from a zero-free half-plane.** If `Θ ∈ [1/2, 1)` satisfies `ζ(s) ≠ 0` on
`Re s > Θ`, then `HasRate (fun K => K^{-a})` holds for every `a ∈ (0, 1 - Θ)`. -/
theorem hasRate_of_zeroFree_exact {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzf : ∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 - Θ) :
    HasRate fun K => (K : ℝ) ^ (-a) := by
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = 1 - Θ - a := ⟨_, rfl⟩
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  obtain ⟨a', ha'_def⟩ : ∃ a' : ℝ, a' = 1 - Θ - δ / 4 := ⟨_, rfl⟩
  have ha'_pos : 0 < a' := by rw [ha'_def, hδ_def]; linarith
  have ha'_le_half : a' ≤ 1 / 2 := by rw [ha'_def]; linarith
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = δ / 64 := ⟨_, rfl⟩
  have hε_pos : 0 < ε := by rw [hε_def]; positivity
  have hε_le4 : ε ≤ 1 / 4 := by rw [hε_def, hδ_def]; linarith
  have hΘε : Θ + ε < 1 := by rw [hε_def, hδ_def]; linarith
  have hden_pos : 0 < 1 - Θ - ε := by linarith
  have hden_le_half : 1 - Θ - ε ≤ 1 / 2 := by linarith
  obtain ⟨τ_exp, hτ_def⟩ : ∃ τ_exp : ℝ, τ_exp = a' / (1 - Θ - ε) := ⟨_, rfl⟩
  have hτ_pos : 0 < τ_exp := by rw [hτ_def]; positivity
  have hτ_gt_a' : a' < τ_exp := by
    have h2 : 2 * a' ≤ τ_exp := by
      rw [hτ_def, le_div_iff₀ hden_pos]
      calc 2 * a' * (1 - Θ - ε) ≤ 2 * a' * (1 / 2) :=
            mul_le_mul_of_nonneg_left hden_le_half (by positivity)
        _ = a' := by ring
    linarith
  have hτ_le_sub : τ_exp ≤ 1 - δ / 4 := by
    rw [hτ_def, div_le_iff₀ hden_pos]
    have h1 : (1 - δ / 4) * (1 - Θ - ε) =
        1 - Θ - ε - (δ / 4) * (1 - Θ) + (δ / 4) * ε := by ring
    have h2 : (δ / 4) * (1 - Θ) ≤ δ / 8 := by
      calc (δ / 4) * (1 - Θ) ≤ (δ / 4) * (1 / 2) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = δ / 8 := by ring
    have h3 : 0 ≤ (δ / 4) * ε := by positivity
    rw [hε_def] at h1 h3
    rw [ha'_def, hε_def]
    linarith only [h1, h2, h3, hδ_pos]
  have hτ_lt1 : τ_exp < 1 := by linarith
  have hτ_mert : τ_exp * (1 - Θ - ε) = a' := by
    rw [hτ_def, div_mul_cancel₀ _ hden_pos.ne']
  have hτ_sub_a' : τ_exp - a' = τ_exp * (Θ + ε) := by
    calc τ_exp - a' = τ_exp - τ_exp * (1 - Θ - ε) := by rw [hτ_mert]
      _ = τ_exp * (Θ + ε) := by ring
  obtain ⟨d, hd_def⟩ : ∃ d : ℕ, d = ⌈1 / (1 - Θ - ε)⌉₊ + 1 := ⟨_, rfl⟩
  have hd1 : 1 ≤ d := by rw [hd_def]; omega
  have hτ_lt_ad1 : τ_exp < a' * ((d + 1 : ℕ) : ℝ) := by
    have hceil : 1 / (1 - Θ - ε) ≤ (⌈1 / (1 - Θ - ε)⌉₊ : ℝ) := Nat.le_ceil _
    have hle_d : τ_exp ≤ a' * (⌈1 / (1 - Θ - ε)⌉₊ : ℝ) := by
      rw [hτ_def, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hceil ha'_pos.le
    have hd_gt : (⌈1 / (1 - Θ - ε)⌉₊ : ℝ) < ((d + 1 : ℕ) : ℝ) := by
      rw [hd_def]; push_cast; linarith
    exact lt_of_le_of_lt hle_d (mul_lt_mul_of_pos_left hd_gt ha'_pos)
  obtain ⟨C₁, C₂, hC₁, hC₂, hstencil⟩ :=
    exists_taut_mertens_stencil hΘ hΘ1 hzf hε_pos hε_le4 hΘε hd1
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = δ / 32 := ⟨_, rfl⟩
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  obtain ⟨M₀, hM₀_def⟩ : ∃ M₀ : ℕ, M₀ = ⌈1 / η⌉₊ + 2 := ⟨_, rfl⟩
  have hM₀_ge2 : 2 ≤ M₀ := by rw [hM₀_def]; omega
  have hη_M₀ : 1 < η * (M₀ : ℝ) := by
    have hceil : 1 / η ≤ (⌈1 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h1 : 1 ≤ η * (⌈1 / η⌉₊ : ℝ) := by
      have := mul_le_mul_of_nonneg_left hceil hη_pos.le
      rwa [mul_one_div_cancel hη_pos.ne'] at this
    rw [hM₀_def]; push_cast; linarith
  obtain ⟨S, hS_def⟩ : ∃ S : ℕ, S = 16 * M₀ + 4 := ⟨_, rfl⟩
  have hS_pos : 1 ≤ S := by rw [hS_def]; omega
  obtain ⟨D_W, hDW_def⟩ : ∃ D_W : ℕ, D_W = 2 ^ (S * (M₀ + 1) + 2) := ⟨_, rfl⟩
  have hDW_pos_nat : 0 < D_W := by rw [hDW_def]; positivity
  have hDW_pos : (0 : ℝ) < (D_W : ℝ) := by exact_mod_cast hDW_pos_nat
  obtain ⟨e_mass, hem_def⟩ : ∃ e_mass : ℝ, e_mass = Θ - 3 * δ / 32 := ⟨_, rfl⟩
  have he1_le : a' * (1 + 2 * ε) + τ_exp * (2 * (Θ + ε) - 1) ≤ e_mass := by
    have hp1 : a' * (1 + 2 * ε) ≤ a' + 2 * ε := by
      have : a' * (2 * ε) ≤ (1 / 2) * (2 * ε) :=
        mul_le_mul_of_nonneg_right ha'_le_half (by positivity)
      linarith
    have hp2 : τ_exp * (2 * (Θ + ε) - 1) ≤ 2 * Θ - 1 + 2 * ε := by
      have h1 : τ_exp * (2 * Θ - 1) ≤ 1 * (2 * Θ - 1) :=
        mul_le_mul_of_nonneg_right hτ_lt1.le (by linarith)
      have h2 : τ_exp * (2 * ε) ≤ 1 * (2 * ε) :=
        mul_le_mul_of_nonneg_right hτ_lt1.le (by positivity)
      linarith
    rw [ha'_def, hε_def] at hp1
    rw [hε_def] at hp2
    rw [hem_def, ha'_def, hε_def]
    linarith only [hp1, hp2, hδ_pos]
  have he2_le : τ_exp * (Θ + ε) ≤ e_mass := by
    have hexp : τ_exp * (Θ + ε) = τ_exp * Θ + τ_exp * ε := mul_add _ _ _
    have hp1 : τ_exp * Θ ≤ (1 - δ / 4) * Θ :=
      mul_le_mul_of_nonneg_right hτ_le_sub (by linarith)
    have hp2 : (1 - δ / 4) * Θ ≤ Θ - δ / 8 := by
      have : (δ / 4) * (1 / 2) ≤ (δ / 4) * Θ :=
        mul_le_mul_of_nonneg_left hΘ (by positivity)
      linarith
    have hp3 : τ_exp * ε ≤ ε := by
      calc τ_exp * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right hτ_lt1.le hε_pos.le
        _ = ε := one_mul _
    rw [hε_def] at hp3 hexp
    rw [hem_def, hε_def]
    linarith only [hexp, hp1, hp2, hp3, hδ_pos]
  obtain ⟨C_mass, hCmass_def⟩ : ∃ C_mass : ℝ, C_mass = 3 * C₁ := ⟨_, rfl⟩
  obtain ⟨C_η₀, hCη₀_def⟩ : ∃ C_η₀ : ℝ, C_η₀ = 4 * C₂ := ⟨_, rfl⟩
  filter_upwards [eventually_ge_atTop 4,
    eventually_floor_rpow_bounds (c := 1) zero_lt_one ha'_pos,
    eventually_floor_rpow_bounds (c := 1 / 2) (by norm_num) hτ_pos,
    eventually_floor_rpow_bounds (c := 1) zero_lt_one hη_pos,
    (eventually_const_rpow_le (tautStencilMinY d + 1 : ℝ) ha'_pos :
      ∀ᶠ K : ℕ in atTop, (tautStencilMinY d + 1 : ℝ) * (K : ℝ) ^ (0 : ℝ) ≤ (K : ℝ) ^ a'),
    eventually_const_rpow_le (4 * (smoothJumpBase d : ℝ)) hτ_gt_a',
    eventually_const_rpow_le ((2 : ℝ) ^ (d + 1)) hτ_lt_ad1,
    (eventually_const_rpow_le ((2 ^ S : ℕ) : ℝ) (by rw [hη_def, hδ_def]; linarith) :
      ∀ᶠ K : ℕ in atTop, ((2 ^ S : ℕ) : ℝ) * (K : ℝ) ^ η ≤ (K : ℝ) ^ (1 : ℝ)),
    eventually_const_rpow_le 2 hη_M₀,
    (eventually_const_rpow_le (4 * (D_W : ℝ)) (by rw [hη_def, hδ_def]; linarith) :
      ∀ᶠ K : ℕ in atTop, (4 * (D_W : ℝ)) * (K : ℝ) ^ η ≤ (K : ℝ) ^ (1 : ℝ)),
    (eventually_const_rpow_le
        (((2 ^ (2 * S + 2) : ℕ) : ℝ) * ((smoothJumpPrimeBound d + 1 : ℕ) : ℝ))
        (by rw [hη_def, ha'_def, hδ_def]; linarith) :
      ∀ᶠ K : ℕ in atTop,
        (((2 ^ (2 * S + 2) : ℕ) : ℝ) * ((smoothJumpPrimeBound d + 1 : ℕ) : ℝ)) *
          (K : ℝ) ^ (2 * η + a') ≤ (K : ℝ) ^ (1 : ℝ)),
    eventually_const_log_pow_rpow_le (80 * C_η₀) 2 (by rw [ha'_def, hδ_def]; linarith :
      -(a + δ / 2) > -a'),
    eventually_const_log_pow_rpow_le (80 * (1 + C_mass)) 5 (by rw [hem_def, hδ_def]; linarith :
      -(a + δ / 2) > e_mass - 2),
    eventually_const_log_pow_rpow_le
      (2 * D_W * C_mass * (1 + 16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * 16)) 6
      (by rw [hem_def, hη_def, hδ_def]; linarith : -(a + δ / 32) > e_mass - (1 - η)),
    eventually_const_rpow_le (6 : ℝ) (by linarith : -a > -(a + δ / 32))] with
    K hK4 hy_b hT_b hW_b hymin hyT hTyd hmlo hmhi hB₀_ev hsq_ev hr1 hr2 hr3 h6pow
  simp only [one_mul, Real.rpow_zero, mul_one, Real.rpow_one] at hy_b hW_b hymin hmlo hmhi hB₀_ev hsq_ev
  have hKR_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  obtain ⟨y, hy_def⟩ : ∃ y : ℕ, y = ⌊(K : ℝ) ^ a'⌋₊ := ⟨_, rfl⟩
  obtain ⟨T, hT_def⟩ : ∃ T : ℕ, T = ⌊(1 / 2 : ℝ) * (K : ℝ) ^ τ_exp⌋₊ := ⟨_, rfl⟩
  obtain ⟨W, hW_def⟩ : ∃ W : ℕ, W = ⌊(K : ℝ) ^ η⌋₊ := ⟨_, rfl⟩
  rw [← hy_def] at hy_b
  rw [← hT_def] at hT_b
  rw [← hW_def] at hW_b
  obtain ⟨hy_ge2, hy_lo_R, hy_hi_R⟩ := hy_b
  obtain ⟨hT_ge2, hT_lo_R, hT_hi_R⟩ := hT_b
  obtain ⟨hW_ge2, hW_lo_R, hW_hi_R⟩ := hW_b
  obtain ⟨B₀, hB₀_def⟩ : ∃ B₀ : ℕ, B₀ = K / (D_W * W) := ⟨_, rfl⟩
  obtain ⟨hy_min, hT_lo, hT_hi, h2T_le_K, hm_lo, hm_hi, hB₀_ge2, hB₀_lo_R, hK_sq⟩ :=
    hasRate_scale_checks hK4 ha'_pos hτ_lt1 hS_pos hDW_pos_nat hW_ge2 hy_def hB₀_def
      hy_lo_R hy_hi_R hT_lo_R hT_hi_R hW_lo_R hW_hi_R hymin hyT hTyd hmlo hmhi hB₀_ev hsq_ev
  obtain ⟨b, -, hb1, hb2, hb_supp, hb_smooth, hmass_raw, htrack_raw⟩ :=
    hstencil y T hy_min hT_lo hT_hi
  obtain ⟨η₀, hη₀_def⟩ : ∃ η₀ : ℝ, η₀ = C₂ * (1 / (y : ℝ) + (T : ℝ) ^ (-(1 - Θ - ε))) := ⟨_, rfl⟩
  have hη₀_nn : 0 ≤ η₀ := by rw [hη₀_def]; positivity
  have hB₀_eq : K / (2 ^ ((16 * M₀ + 4) * (M₀ + 1) + 2) * W) = B₀ := by
    rw [← hS_def, ← hDW_def, hB₀_def]
  obtain ⟨c, m, hP, halph, hrate_raw⟩ := exists_hamming_compensated_producer
    (b := b) (N := 2 * T) (P_max := smoothJumpPrimeBound d * y)
    (M₀ := M₀) (W := W) (K := K) (X := K ^ 2) (η₀ := η₀)
    (by omega) hb1 hb2 hb_supp (fun k hk2 _ hbk => hb_smooth k hk2 hbk) hη₀_nn
    (fun x hx => by rw [hη₀_def]; exact htrack_raw x hx)
    hM₀_ge2 hW_ge2 h2T_le_K (Nat.le_self_pow (by norm_num) K)
    (by rwa [← hS_def]) (by rwa [← hS_def]) (by rwa [hB₀_eq]) (by rwa [← hS_def])
  rw [hB₀_eq] at hP hrate_raw
  rw [← hS_def] at hrate_raw
  refine ⟨c, m, B₀, hP, halph, hrate_raw.trans ?_⟩
  have hη₀_bd : η₀ ≤ C_η₀ * (K : ℝ) ^ (-a') := by
    rw [hη₀_def, hCη₀_def]
    exact hasRate_eta_bd hKR_pos (by omega) hy_lo_R hT_lo_R hden_pos hden_le_half hτ_mert hC₂
  have hmass_bd : tautMass b (2 * T) ≤ C_mass * (1 + Real.log (K : ℝ)) ^ 3 * (K : ℝ) ^ e_mass := by
    rw [hCmass_def]
    exact hasRate_tautMass_bd hK4 (by omega) hT_ge2 h2T_le_K hΘ hε_pos hC₁
      hy_lo_R hy_hi_R hT_hi_R hτ_sub_a' he1_le he2_le hmass_raw
  exact hasRate_rate_tail_le hK4 hT_ge2 h2T_le_K hB₀_ge2
    (by rw [hB₀_def]; exact Nat.div_le_self K (D_W * W)) hDW_pos
    (by rw [hCη₀_def]; positivity) (by rw [hCmass_def]; positivity)
    hδ_pos (by rw [hem_def, hδ_def]; linarith) hη₀_nn hη₀_bd hmass_bd hB₀_lo_R hr1 hr2 hr3 h6pow

/-! ### Part 4: Exact zero-free equivalences, RH equivalence, rate law, and Question 18 -/

/-- Unconditionally, every subcritical rate `K^{-a}` with `0 < a < 1 - zetaZeroAbscissa` is
achieved by balanced integer floor producers. -/
theorem hasRate_of_lt_one_sub_zetaZeroAbscissa {a : ℝ} (ha0 : 0 < a)
    (ha : a < 1 - RHTower.zetaZeroAbscissa) :
    HasRate fun K => (K : ℝ) ^ (-a) :=
  hasRate_of_zeroFree_exact RHTower.half_le_zetaZeroAbscissa (by linarith)
    (fun _ hs => RHTower.riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hs) ha0 ha

/-- **Exact full-strip equivalence.** For any `Θ ∈ [1/2, 1)`, `ζ(s) ≠ 0` on `Re s > Θ` if and only
if `HasRate (fun K => K^{-a})` holds for all `a ∈ (0, 1 - Θ)`. -/
theorem zeroFree_iff_forall_hasRate {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1) :
    (∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0) ↔
      ∀ a : ℝ, 0 < a → a < 1 - Θ → HasRate fun K => (K : ℝ) ^ (-a) := by
  constructor
  · intro hzf a ha0 ha
    exact hasRate_of_zeroFree_exact hΘ hΘ1 hzf ha0 ha
  · intro hall s hs hzero
    by_cases hs1 : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re hs1 hzero
    push Not at hs1
    have hre := re_le_of_hasRate_rpow_half (a := ((1 - s.re) + (1 - Θ)) / 2)
      (by linarith) (hall _ (by linarith) (by linarith)) hzero
    linarith

/-- Cofinal `bestRate` characterization of a zero-free half-plane `Re s > Θ`. -/
theorem zeroFree_iff_forall_frequently_bestRate_le {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1) :
    (∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0) ↔
      ∀ a : ℝ, 0 < a → a < 1 - Θ → ∃ᶠ K : ℕ in atTop, bestRate K ≤ (K : ℝ) ^ (-a) := by
  constructor
  · intro hzf a ha0 ha
    refine (Filter.Eventually.mono (hasRate_of_zeroFree_exact hΘ hΘ1 hzf ha0 ha) fun K hK => ?_).frequently
    obtain ⟨c, m, B, hP, hal, hr⟩ := hK
    have hbdd : BddBelow (rateSet K) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨_, _, _, hP', _, rfl⟩
      exact hP'.rate_pos.le
    exact (csInf_le hbdd ⟨c, m, B, hP, hal, rfl⟩).trans hr
  · intro hfreq s hs hzero
    by_cases hs1 : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re hs1 hzero
    push Not at hs1
    have hs_ge_half : 1 / 2 ≤ s.re := by linarith
    set a' : ℝ := ((1 - s.re) + (1 - Θ)) / 2
    set a'' : ℝ := (1 - s.re + a') / 2
    have ha''0 : 0 < a'' := by dsimp [a'', a']; linarith
    have ha''_half : a'' ≤ 1 / 2 := by dsimp [a'', a']; linarith
    have hre_gt : 1 - a'' < s.re := by dsimp [a'', a']; linarith
    have hev_gt := eventually_rate_gt_of_zero hzero ha''0 ha''_half hre_gt
    have hev_best : ∀ᶠ K : ℕ in atTop, (K : ℝ) ^ (-a') < bestRate K := by
      have hev_pow : ∀ᶠ K : ℕ in atTop, (2 : ℝ) * (K : ℝ) ^ (-a') ≤ (K : ℝ) ^ (-a'') :=
        eventually_const_rpow_le 2 (by dsimp [a'', a']; linarith)
      filter_upwards [hasRate_vk (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 3 / 5),
        hev_gt, hev_pow, eventually_ge_atTop 1] with K hvk hgt hpow hK1
      obtain ⟨c, m, B, hP, hal, -⟩ := hvk
      have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
      have hpos_a' : 0 < (K : ℝ) ^ (-a') := Real.rpow_pos_of_pos hK_pos _
      have hle_inf : (K : ℝ) ^ (-a'') ≤ bestRate K := by
        refine le_csInf ⟨rate c m B, c, m, B, hP, hal, rfl⟩ ?_
        rintro ε ⟨c', m', B', hP', hal', rfl⟩
        exact (hgt c' m' B' hP' hal').le
      linarith
    exact ((hfreq a' (by dsimp [a']; linarith) (by dsimp [a']; linarith)).and_eventually
      hev_best).exists.elim fun K ⟨hle, hlt⟩ => (hlt.not_ge hle).elim

/-- **Under the Riemann Hypothesis, every rate `K^{-a}` with `0 < a < 1/2` is achieved.** -/
theorem hasRate_of_riemannHypothesis_half (hRH : RiemannHypothesis)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    HasRate fun K => (K : ℝ) ^ (-a) := by
  have hzf : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → riemannZeta s ≠ 0 := by
    intro s hs
    by_cases hs1 : s.re < 1
    · exact (RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mp hRH) s hs hs1
    · exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hs1)
  exact hasRate_of_zeroFree_exact le_rfl (by norm_num) hzf ha0 (by linarith)

/-- **Exact rate characterization of the Riemann Hypothesis.** -/
theorem riemannHypothesis_iff_forall_hasRate_half :
    RiemannHypothesis ↔ ∀ a : ℝ, 0 < a → a < 1 / 2 → HasRate fun K => (K : ℝ) ^ (-a) :=
  ⟨fun hRH _ ha0 ha => hasRate_of_riemannHypothesis_half hRH ha0 ha,
   riemannHypothesis_of_hasRate_half⟩

/-- **Unconditional exact rate-exponent law.**
`lim_{K → ∞} log(bestRate K) / log K = zetaZeroAbscissa - 1`. -/
theorem tendsto_log_bestRate_div_log :
    Tendsto (fun K : ℕ => Real.log (bestRate K) / Real.log (K : ℝ))
      atTop (𝓝 (RHTower.zetaZeroAbscissa - 1)) := by
  rw [tendsto_order]
  obtain ⟨c₁, hc₁, hbrack⟩ :=
    exists_half_bracket_bestRate (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 3 / 5)
  constructor
  · intro L hL
    set a' : ℝ := ((1 - RHTower.zetaZeroAbscissa) + (-L)) / 2
    have ha'_gt : 1 - RHTower.zetaZeroAbscissa < a' := by dsimp [a']; linarith
    have hL_lt : L < -a' := by dsimp [a']; linarith
    filter_upwards [eventually_ge_atTop 2, eventually_bestRate_ge_of_one_sub_zetaZeroAbscissa_lt ha'_gt]
      with K hK2 hbest
    have hKR_gt1 : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK2
    have hKR_pos : (0 : ℝ) < (K : ℝ) := by linarith
    have hlogK_pos : 0 < Real.log (K : ℝ) := Real.log_pos hKR_gt1
    have hpow_pos : 0 < (K : ℝ) ^ (-a') := Real.rpow_pos_of_pos hKR_pos _
    have hlog_le : -a' * Real.log (K : ℝ) ≤ Real.log (bestRate K) := by
      have := Real.log_le_log hpow_pos hbest
      rwa [Real.log_rpow hKR_pos] at this
    exact lt_of_lt_of_le hL_lt ((le_div_iff₀ hlogK_pos).mpr hlog_le)
  · intro U hU
    rcases lt_or_ge 0 U with hU_pos | hU_np
    · filter_upwards [eventually_ge_atTop 2, hbrack] with K hK2 ⟨hlo, hhi⟩
      have hKR_gt1 : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK2
      have hlogK_pos : 0 < Real.log (K : ℝ) := Real.log_pos hKR_gt1
      have hD_pos : 0 < √(K : ℝ) * (1 + Real.log (K : ℝ)) := by positivity
      have hbest_pos : 0 < bestRate K := lt_of_lt_of_le (div_pos hc₁ hD_pos) hlo
      have hbest_le1 : bestRate K ≤ 1 :=
        hhi.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
      have hlog_np : Real.log (bestRate K) ≤ 0 := Real.log_nonpos hbest_pos.le hbest_le1
      exact lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg hlog_np hlogK_pos.le) hU_pos
    · set u' : ℝ := (RHTower.zetaZeroAbscissa - 1 + U) / 2
      have hu'_lt_U : u' < U := by dsimp [u']; linarith
      set a' : ℝ := -u'
      have ha'0 : 0 < a' := by dsimp [a', u']; linarith
      have ha'_lt : a' < 1 - RHTower.zetaZeroAbscissa := by dsimp [a', u']; linarith
      filter_upwards [eventually_ge_atTop 2, hbrack,
        hasRate_of_lt_one_sub_zetaZeroAbscissa ha'0 ha'_lt] with K hK2 ⟨hlo, _⟩ ⟨c, m, B, hP, hal, hr⟩
      have hKR_gt1 : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK2
      have hKR_pos : (0 : ℝ) < (K : ℝ) := by linarith
      have hlogK_pos : 0 < Real.log (K : ℝ) := Real.log_pos hKR_gt1
      have hD_pos : 0 < √(K : ℝ) * (1 + Real.log (K : ℝ)) := by positivity
      have hbest_pos : 0 < bestRate K := lt_of_lt_of_le (div_pos hc₁ hD_pos) hlo
      have hbdd : BddBelow (rateSet K) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨_, _, _, hP', _, rfl⟩
        exact hP'.rate_pos.le
      have hbest_le : bestRate K ≤ (K : ℝ) ^ (-a') :=
        (csInf_le hbdd ⟨c, m, B, hP, hal, rfl⟩).trans hr
      have hlog_le : Real.log (bestRate K) ≤ u' * Real.log (K : ℝ) := by
        have := Real.log_le_log hbest_pos hbest_le
        rw [Real.log_rpow hKR_pos] at this
        dsimp [a'] at this
        linarith
      exact lt_of_le_of_lt ((div_le_iff₀ hlogK_pos).mpr hlog_le) hu'_lt_U

/-- **Exact resolution of the strict floor-alphabet obstruction.** For every `a₀ ∈ [0, 1/2)`,
there exists `a_* ∈ (a₀, 1/2)` such that eventually every integer producer `(c, m, B)` supported in
`[1, K]` satisfies `K^{-a_*} < rate c m B` if and only if `¬ RiemannHypothesis`. -/
theorem exists_strict_floor_obstruction_iff_not_riemannHypothesis {a₀ : ℝ}
    (ha₀_nn : 0 ≤ a₀) (ha₀_lt : a₀ < 1 / 2) :
    (∃ a_star : ℝ, a₀ < a_star ∧ a_star < 1 / 2 ∧
      ∀ᶠ K : ℕ in atTop, ∀ (c : ℕ →₀ ℤ) (m B : ℕ),
        IsProducer c m B → AlphabetLE c K → (K : ℝ) ^ (-a_star) < rate c m B) ↔
      ¬ RiemannHypothesis := by
  constructor
  · rintro ⟨a_star, ha₀_a, ha_half, hev_gt⟩ hRH
    have hrate := hasRate_of_riemannHypothesis_half hRH (by linarith) ha_half
    obtain ⟨K, hgt, c, m, B, hP, hal, hr_le⟩ := (hev_gt.and hrate).exists
    exact (hgt c m B hP hal).not_ge hr_le
  · intro hnotRH
    rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip] at hnotRH
    push Not at hnotRH
    obtain ⟨ρ, hρ_gt, hρ_lt1, hρ_zero⟩ := hnotRH
    set a_star : ℝ := (max a₀ (1 - ρ.re) + 1 / 2) / 2
    have ha_gt_a₀ : a₀ < a_star := by
      have : a₀ ≤ max a₀ (1 - ρ.re) := le_max_left _ _
      dsimp [a_star]; linarith
    have ha_lt_half : a_star < 1 / 2 := by
      have : max a₀ (1 - ρ.re) < 1 / 2 := max_lt ha₀_lt (by linarith)
      dsimp [a_star]; linarith
    have hre_gt : 1 - a_star < ρ.re := by
      have : 1 - ρ.re ≤ max a₀ (1 - ρ.re) := le_max_right _ _
      dsimp [a_star]; linarith
    exact ⟨a_star, ha_gt_a₀, ha_lt_half,
      eventually_rate_gt_of_zero hρ_zero (by linarith) ha_lt_half.le hre_gt⟩

/-- **Question 18 specialized to `a₀ = 1/4`.** The existence of `a_* ∈ (1/4, 1/2)` such that
eventually every admissible balanced integer floor producer on `[1, K]` has `rate c m B > K^{-a_*}`
is logically equivalent to `¬ RiemannHypothesis`. -/
theorem strict_floor_obstruction_quarter_iff_not_riemannHypothesis :
    (∃ a_star : ℝ, 1 / 4 < a_star ∧ a_star < 1 / 2 ∧
      ∀ᶠ K : ℕ in atTop, ∀ (c : ℕ →₀ ℤ) (m B : ℕ),
        IsProducer c m B → AlphabetLE c K → (K : ℝ) ^ (-a_star) < rate c m B) ↔
      ¬ RiemannHypothesis :=
  exists_strict_floor_obstruction_iff_not_riemannHypothesis (by norm_num) (by norm_num)

#print axioms hasRate_of_zeroFree_exact
#print axioms zeroFree_iff_forall_hasRate
#print axioms zeroFree_iff_forall_frequently_bestRate_le
#print axioms riemannHypothesis_iff_forall_hasRate_half
#print axioms tendsto_log_bestRate_div_log
#print axioms exists_strict_floor_obstruction_iff_not_riemannHypothesis
#print axioms strict_floor_obstruction_quarter_iff_not_riemannHypothesis

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
