import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerLogarithmicSigns
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.ANonRealPairAloneOnTopOfATwoSidedEdit
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# Four-Factor Log-Positivity Dichotomy, Bernoulli–Möbius Convergence, and Composite Dipoles

This module establishes three unconditional theorems in the analytic theory of Dirichlet series,
Euler products, and half-plane zero configurations:

1. **Four-factor de la Vallée Poussin log-weight dichotomy (`fourFactorLogWeight_ofReal_eq_four_cos_sq`,
   `twoSidedEdit_fourFactor_vanishes_on_real_axis`,
   `positiveFiniteEuler_fourFactor_neg_at_prime_sq`,
   `positiveRootEuler_fourFactor_neg_at_prime`):**
   - For any real Dirichlet log-weight `b : ℕ → ℝ` and vertical shift `γ ∈ ℝ`, the four-factor
     combination `Re(2 b(n) + b(n) (n^{-iγ} + n^{iγ}))` equals `4 cos²(γ log n / 2) b(n)` (`≥ 0`
     whenever `b(n) ≥ 0`).
   - On two-sided prime edits `editSystem (edit ρ₀)` (`1/2 < Re ρ₀ < 14/15`, `Im ρ₀ ≠ 0`), every
     prime-power log-multiplicity `1 + edit ρ₀ p ∈ {0, 1, 2}` is nonnegative, yet the four-factor
     holomorphic product `((s - 1) ζ_B(s))² ((s + iγ₀ - 1) ζ_B(s + iγ₀)) ((s - iγ₀ - 1) ζ_B(s - iγ₀))`
     at `γ₀ = Im ρ₀` vanishes on the real axis at `s = Re ρ₀` because the pole order at `s = 1` is
     only `2 < 4` (two poles sit at `1 ± iγ₀`).
   - Conversely, on single-prime quadratic Euler modifications, four-factor log-positivity fails
     already at a single prime power: for `PositiveFiniteEuler` `(1 + A p^{-s} + p^{1-2s}) / (1 - p^{-s})`
     (`A = r + p/r`, `r > 0`) at `γ₀ = π / log p`, the `p²` four-factor log-weight is
     `2(1 - r² - (p/r)²) ≤ 2(1 - 2p) ≤ -6 < 0`; and for positive-root factors
     `(1 - p^σ p^{-s})(1 - p^{1-σ} p^{-s}) / (1 - p^{-s})` at `γ₀ = 2π / log p`, the `p¹`
     four-factor log-weight is `4(1 - p^σ - p^{1-σ}) ≤ 4(1 - 2√p) < 0`.

2. **Bernoulli–Möbius Fourier mode square-summability on `Re s > 1/2`
   (`bernoulliMoebiusMode_prime`, `norm_bernoulliMoebiusMode_le`,
   `summable_sq_norm_bernoulliMoebiusMode`):**
   The `m`-th periodic Bernoulli–Möbius mode
   `c_m(s) = m^{-s} ∑_{d ∣ m} μ(d) d^{s - 2}` satisfies `|c_m(s)| ≤ d(m) m^{-min(Re s, 2)}` for all
   `m ≥ 1` and `∑_{m=1}^∞ ‖c_m(s)‖² < ∞` across the entire open half-plane `Re s > 1/2`.

3. **Composite-supported Dirichlet log-dipole with `O_ε(1)` tail and exact zero pair
   (`dipoleLogCoeff_uniform_bound`, `exists_exp_dipoleLogCoeff_continuation`):**
   For `Re ρ₁ < 1/2 < Re ρ₀ < 1`, the ordinary Dirichlet series `L_{ρ₀, ρ₁}(s)` with coefficients
   `((k^{ρ₁ - 1} - k^{ρ₀ - 1} + k^{conj ρ₁ - 1} - k^{conj ρ₀ - 1}) / log k)` (`k ≥ 2`) converges
   absolutely and is uniformly bounded on `Re s ≥ Re ρ₀ + ε` for every `ε > 0`, while
   `exp(L_{ρ₀, ρ₁}(s))` continues holomorphically across `Re s = 1/2` to `{Re s > Re ρ₁}` with
   exact zero set `{ρ₀, conj ρ₀}`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.SelbergClass

/-! ## 1. Four-factor de la Vallée Poussin log-weight dichotomy -/

/-- The `3-4-1` / four-factor real logarithmic weight `Re(2 b(n) + b(n) (n^{-iγ} + n^{iγ}))`
corresponding to `F(s)² F(s + iγ) F(s - iγ)`. -/
def fourFactorLogWeight (b : ℕ → ℂ) (γ : ℝ) (n : ℕ) : ℝ :=
  (2 * b n + b n * ((n : ℂ) ^ (-((γ : ℂ) * I)) + (n : ℂ) ^ ((γ : ℂ) * I))).re

private theorem natCast_cpow_mul_I_add_neg {n : ℕ} (hn : 1 ≤ n) (γ : ℝ) :
    (n : ℂ) ^ (-((γ : ℂ) * I)) + (n : ℂ) ^ ((γ : ℂ) * I) =
      ((2 * Real.cos (γ * Real.log n) : ℝ) : ℂ) := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn_pos.le]
  have hpos_i : (n : ℂ) ^ ((γ : ℂ) * I) =
      Complex.cos ((γ * Real.log n : ℝ) : ℂ) + Complex.sin ((γ * Real.log n : ℝ) : ℂ) * I := by
    rw [Complex.cpow_def_of_ne_zero hn_ne, hlog,
      show (Real.log n : ℂ) * ((γ : ℂ) * I) = ((γ * Real.log n : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I]
  have hneg_i : (n : ℂ) ^ (-((γ : ℂ) * I)) =
      Complex.cos ((γ * Real.log n : ℝ) : ℂ) - Complex.sin ((γ * Real.log n : ℝ) : ℂ) * I := by
    rw [Complex.cpow_def_of_ne_zero hn_ne, hlog,
      show (Real.log n : ℂ) * -((γ : ℂ) * I) = ((- (γ * Real.log n) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [hneg_i, hpos_i, ← Complex.ofReal_cos]
  push_cast; ring

/-- **Exact `4 cos²` identity:** for any real sequence `b : ℕ → ℝ` and `n ≥ 1`,
`fourFactorLogWeight b γ n = 4 cos²(γ log n / 2) b(n)`. -/
theorem fourFactorLogWeight_ofReal_eq_four_cos_sq (b : ℕ → ℝ) (γ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    fourFactorLogWeight (fun k => (b k : ℂ)) γ n =
      4 * Real.cos (γ * Real.log n / 2) ^ 2 * b n := by
  unfold fourFactorLogWeight
  rw [natCast_cpow_mul_I_add_neg hn γ]
  have hre : (2 * (b n : ℂ) + (b n : ℂ) * ((2 * Real.cos (γ * Real.log n) : ℝ) : ℂ)).re =
      (2 + 2 * Real.cos (γ * Real.log n)) * b n := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, Complex.ofReal_re]
    ring
  rw [hre]
  have hcos : Real.cos (γ * Real.log n) = 2 * Real.cos (γ * Real.log n / 2) ^ 2 - 1 := by
    conv_lhs => rw [show γ * Real.log n = 2 * (γ * Real.log n / 2) by ring]
    exact Real.cos_two_mul (γ * Real.log n / 2)
  rw [hcos]; ring

theorem fourFactorLogWeight_ofReal_nonneg {b : ℕ → ℝ} (γ : ℝ) {n : ℕ}
    (hn : 1 ≤ n) (hb : 0 ≤ b n) :
    0 ≤ fourFactorLogWeight (fun k => (b k : ℂ)) γ n := by
  rw [fourFactorLogWeight_ofReal_eq_four_cos_sq b γ hn]
  positivity

/-- **Insufficient pole multiplicity obstructs four-factor positivity on `{1/2 < Re s < 1}`.**
For `1/2 < Re ρ₀ < 14/15` with `Im ρ₀ ≠ 0`, the greedy two-sided prime edit `B = editSystem (edit ρ₀)`
has nonnegative prime-power log-multiplicities `1 + edit ρ₀ p ≥ 0` (so nonnegative four-factor
log-weights at `γ₀ = Im ρ₀`), yet the holomorphic continuation `F₄` of
`((s - 1) ζ_B(s))² ((s + iγ₀ - 1) ζ_B(s + iγ₀)) ((s - iγ₀ - 1) ζ_B(s - iγ₀))` to `{Re s > 1/2}`
vanishes on the real axis at `s = Re ρ₀`. -/
theorem twoSidedEdit_fourFactor_vanishes_on_real_axis {ρ₀ : ℂ}
    (hre : 1 / 2 < ρ₀.re) (hlt : ρ₀.re < 14 / 15) :
    let e := WorldsOfTheZeroConfiguration.PrimeEdits.edit ρ₀
    let B := WorldsOfTheZeroConfiguration.TwoSidedEdits.editSystem e
    let γ₀ := ρ₀.im
    (∀ k : ℕ, 1 ≤ k →
      0 ≤ fourFactorLogWeight (fun n => (((1 + e n : ℤ) : ℝ) : ℂ)) γ₀ k) ∧
    ∃ F₄ : ℂ → ℂ,
      DifferentiableOn ℂ F₄ {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        F₄ s = ((s - 1) * B.zetaSeriesC s) ^ 2 *
          ((s + (γ₀ : ℂ) * I - 1) * B.zetaSeriesC (s + (γ₀ : ℂ) * I)) *
          ((s - (γ₀ : ℂ) * I - 1) * B.zetaSeriesC (s - (γ₀ : ℂ) * I))) ∧
      F₄ (ρ₀.re : ℂ) = 0 := by
  dsimp only
  have he := WorldsOfTheZeroConfiguration.isEdit_edit ρ₀
  refine ⟨fun k hk => fourFactorLogWeight_ofReal_nonneg _ hk ?_, ?_⟩
  · rcases he.range k with h | h | h <;> rw [h] <;> norm_num
  · obtain ⟨C, H, _, hdiffG, hfacG⟩ :=
      (WorldsOfTheZeroConfiguration.isPairTwin_editSystem hre hlt).exists_continuation
    set G : ℂ → ℂ := fun s =>
      RHTower.zetaResidueUnit s * (C * (s - ρ₀) * (s - conj ρ₀) * Complex.exp (H s))
    set γ₀ : ℝ := ρ₀.im
    set F₄ : ℂ → ℂ := fun s => G s ^ 2 * G (s + (γ₀ : ℂ) * I) * G (s - (γ₀ : ℂ) * I)
    have hshift_pos : DifferentiableOn ℂ (fun s => G (s + (γ₀ : ℂ) * I)) {s : ℂ | 1 / 2 < s.re} :=
      hdiffG.comp (differentiableOn_id.add_const _) fun s hs => by
        show 1 / 2 < (s + (γ₀ : ℂ) * I).re; simp [hs.out]
    have hshift_neg : DifferentiableOn ℂ (fun s => G (s - (γ₀ : ℂ) * I)) {s : ℂ | 1 / 2 < s.re} :=
      hdiffG.comp (differentiableOn_id.sub_const _) fun s hs => by
        show 1 / 2 < (s - (γ₀ : ℂ) * I).re; simp [hs.out]
    refine ⟨F₄, ((hdiffG.pow 2).mul hshift_pos).mul hshift_neg, fun s hs => ?_, ?_⟩
    · have hs_p : 1 < (s + (γ₀ : ℂ) * I).re := by simp [hs]
      have hs_m : 1 < (s - (γ₀ : ℂ) * I).re := by simp [hs]
      dsimp [F₄, G]
      rw [← hfacG s hs, ← hfacG _ hs_p, ← hfacG _ hs_m]
    · have hhit : ((ρ₀.re : ℂ) + (γ₀ : ℂ) * I) = ρ₀ := by
        dsimp [γ₀]; exact Complex.re_add_im ρ₀
      have hG0 : G ρ₀ = 0 := by dsimp [G]; simp
      dsimp [F₄]
      rw [hhit, hG0, mul_zero, zero_mul]

/-- **Single-prime quadratic Euler twin violates four-factor log-positivity at `p²`.**
For any prime `p` and any `r > 0`, the reciprocal local modification with roots `-r, -p/r` has
four-factor log-weight `2(1 - r² - (p/r)²) ≤ 2(1 - 2p) ≤ -6 < 0` at `n = p²` and `γ₀ = π / log p`. -/
theorem positiveFiniteEuler_fourFactor_neg_at_prime_sq {p : ℕ} (hp : p.Prime) {r : ℝ} (hr : 0 < r) :
    fourFactorLogWeight
      (PositiveFiniteEuler.eulerLogCoeff p (-(r : ℂ)) (-(((p : ℝ) / r : ℝ) : ℂ)))
      (Real.pi / Real.log p) (p ^ 2) = 2 * (1 - r ^ 2 - ((p : ℝ) / r) ^ 2) ∧
    fourFactorLogWeight
      (PositiveFiniteEuler.eulerLogCoeff p (-(r : ℂ)) (-(((p : ℝ) / r : ℝ) : ℂ)))
      (Real.pi / Real.log p) (p ^ 2) ≤ 2 * (1 - 2 * (p : ℝ)) ∧
    fourFactorLogWeight
      (PositiveFiniteEuler.eulerLogCoeff p (-(r : ℂ)) (-(((p : ℝ) / r : ℝ) : ℂ)))
      (Real.pi / Real.log p) (p ^ 2) ≤ -6 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlog_ne : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hp_sq_ge1 : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp.pos
  have hcoeff : PositiveFiniteEuler.eulerLogCoeff p (-(r : ℂ)) (-(((p : ℝ) / r : ℝ) : ℂ)) (p ^ 2) =
      (((1 - r ^ 2 - ((p : ℝ) / r) ^ 2) / 2 : ℝ) : ℂ) := by
    rw [PositiveFiniteEuler.eulerLogCoeff_prime_pow hp _ _ (by norm_num : (2 : ℕ) ≠ 0)]
    push_cast; ring
  have hval : fourFactorLogWeight
      (PositiveFiniteEuler.eulerLogCoeff p (-(r : ℂ)) (-(((p : ℝ) / r : ℝ) : ℂ)))
      (Real.pi / Real.log p) (p ^ 2) = 2 * (1 - r ^ 2 - ((p : ℝ) / r) ^ 2) := by
    unfold fourFactorLogWeight
    rw [hcoeff, natCast_cpow_mul_I_add_neg hp_sq_ge1]
    have harg : Real.pi / Real.log p * Real.log ((p ^ 2 : ℕ) : ℝ) = 2 * Real.pi := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; field_simp [hlog_ne]
    rw [harg, Real.cos_two_pi]
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, Complex.ofReal_re]
    ring
  have hamgm : 2 * (p : ℝ) ≤ r ^ 2 + ((p : ℝ) / r) ^ 2 := by
    have hsq : 0 ≤ (r - (p : ℝ) / r) ^ 2 := sq_nonneg _
    have hprod : r * ((p : ℝ) / r) = (p : ℝ) := mul_div_cancel₀ _ hr.ne'
    nlinarith
  exact ⟨hval, by linarith, by linarith⟩

/-- **Positive-root local factor violates four-factor log-positivity already at `p¹`.**
For `(1 - p^σ p^{-s})(1 - p^{1-σ} p^{-s}) / (1 - p^{-s})` at `γ₀ = 2π / log p`, the `n = p`
four-factor log-weight is `4(1 - p^σ - p^{1-σ}) ≤ 4(1 - 2√p) < 0`. -/
theorem positiveRootEuler_fourFactor_neg_at_prime {p : ℕ} (hp : p.Prime) (σ : ℝ) :
    fourFactorLogWeight
      (PositiveFiniteEuler.eulerLogCoeff p (((p : ℝ) ^ σ : ℝ) : ℂ) (((p : ℝ) ^ (1 - σ) : ℝ) : ℂ))
      (2 * Real.pi / Real.log p) p = 4 * (1 - (p : ℝ) ^ σ - (p : ℝ) ^ (1 - σ)) ∧
    fourFactorLogWeight
      (PositiveFiniteEuler.eulerLogCoeff p (((p : ℝ) ^ σ : ℝ) : ℂ) (((p : ℝ) ^ (1 - σ) : ℝ) : ℂ))
      (2 * Real.pi / Real.log p) p ≤ 4 * (1 - 2 * Real.sqrt p) ∧
    fourFactorLogWeight
      (PositiveFiniteEuler.eulerLogCoeff p (((p : ℝ) ^ σ : ℝ) : ℂ) (((p : ℝ) ^ (1 - σ) : ℝ) : ℂ))
      (2 * Real.pi / Real.log p) p < 0 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p : ℝ) := by linarith
  have hlog_ne : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hcoeff : PositiveFiniteEuler.eulerLogCoeff p
      (((p : ℝ) ^ σ : ℝ) : ℂ) (((p : ℝ) ^ (1 - σ) : ℝ) : ℂ) p =
      ((1 - (p : ℝ) ^ σ - (p : ℝ) ^ (1 - σ) : ℝ) : ℂ) := by
    have h1 := PositiveFiniteEuler.eulerLogCoeff_prime_pow hp
      (((p : ℝ) ^ σ : ℝ) : ℂ) (((p : ℝ) ^ (1 - σ) : ℝ) : ℂ) (by norm_num : (1 : ℕ) ≠ 0)
    simpa using h1
  have hval : fourFactorLogWeight
      (PositiveFiniteEuler.eulerLogCoeff p (((p : ℝ) ^ σ : ℝ) : ℂ) (((p : ℝ) ^ (1 - σ) : ℝ) : ℂ))
      (2 * Real.pi / Real.log p) p = 4 * (1 - (p : ℝ) ^ σ - (p : ℝ) ^ (1 - σ)) := by
    unfold fourFactorLogWeight
    rw [hcoeff, natCast_cpow_mul_I_add_neg hp.one_lt.le]
    have harg : 2 * Real.pi / Real.log p * Real.log p = 2 * Real.pi := div_mul_cancel₀ _ hlog_ne
    rw [harg, Real.cos_two_pi, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
    ring
  have hamgm : 2 * Real.sqrt p ≤ (p : ℝ) ^ σ + (p : ℝ) ^ (1 - σ) := by
    have ha : 0 ≤ (p : ℝ) ^ σ := Real.rpow_nonneg hp0.le σ
    have hb : 0 ≤ (p : ℝ) ^ (1 - σ) := Real.rpow_nonneg hp0.le (1 - σ)
    have hprod : (p : ℝ) ^ σ * (p : ℝ) ^ (1 - σ) = (p : ℝ) := by
      rw [← Real.rpow_add hp0, add_sub_cancel, Real.rpow_one]
    have hsq : 0 ≤ (Real.sqrt ((p : ℝ) ^ σ) - Real.sqrt ((p : ℝ) ^ (1 - σ))) ^ 2 := sq_nonneg _
    have hexp : (Real.sqrt ((p : ℝ) ^ σ) - Real.sqrt ((p : ℝ) ^ (1 - σ))) ^ 2 =
        (p : ℝ) ^ σ + (p : ℝ) ^ (1 - σ) - 2 * Real.sqrt p := by
      calc (Real.sqrt ((p : ℝ) ^ σ) - Real.sqrt ((p : ℝ) ^ (1 - σ))) ^ 2
          = Real.sqrt ((p : ℝ) ^ σ) ^ 2 + Real.sqrt ((p : ℝ) ^ (1 - σ)) ^ 2 -
              2 * (Real.sqrt ((p : ℝ) ^ σ) * Real.sqrt ((p : ℝ) ^ (1 - σ))) := by ring
        _ = (p : ℝ) ^ σ + (p : ℝ) ^ (1 - σ) - 2 * Real.sqrt p := by
            rw [Real.sq_sqrt ha, Real.sq_sqrt hb, ← Real.sqrt_mul ha, hprod]
    linarith
  have hsqrt_gt1 : 1 < Real.sqrt p := by
    rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt zero_le_one (by linarith)
  exact ⟨hval, by linarith, by linarith⟩

/-! ## 2. Bernoulli–Möbius Fourier mode square-summability on `Re s > 1/2` -/

/-- The `m`-th Bernoulli–Möbius / Jordan-totient Fourier mode
`c_m(s) = m^{-s} ∑_{d ∣ m} μ(d) d^{s - 2}` (`0` at `m = 0`). -/
def bernoulliMoebiusMode (s : ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0
  else (m : ℂ) ^ (-s) * ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (s - 2)

/-- At every prime `p`, `bernoulliMoebiusMode s p = p^{-s} (1 - p^{s - 2})`. -/
theorem bernoulliMoebiusMode_prime (s : ℂ) {p : ℕ} (hp : p.Prime) :
    bernoulliMoebiusMode s p = (p : ℂ) ^ (-s) * (1 - (p : ℂ) ^ (s - 2)) := by
  unfold bernoulliMoebiusMode
  rw [if_neg hp.ne_zero, hp.divisors, Finset.sum_insert (by simp [hp.ne_one]), Finset.sum_singleton]
  simp [ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- **Uniform divisor-count bound:** for every `s ∈ ℂ` and `m ≥ 1`,
`‖bernoulliMoebiusMode s m‖ ≤ d(m) · m^{-min(Re s, 2)}`. -/
theorem norm_bernoulliMoebiusMode_le (s : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    ‖bernoulliMoebiusMode s m‖ ≤ (m.divisors.card : ℝ) * (m : ℝ) ^ (-min s.re 2) := by
  have hm0 : m ≠ 0 := by omega
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  unfold bernoulliMoebiusMode
  rw [if_neg hm0, norm_mul, Complex.norm_natCast_cpow_of_pos hm, Complex.neg_re]
  have hsum : ‖∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (s - 2)‖ ≤
      ∑ d ∈ m.divisors, (d : ℝ) ^ (s.re - 2) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    rw [norm_mul, Complex.norm_intCast, Complex.norm_natCast_cpow_of_pos hd_pos,
      Complex.sub_re, Complex.ofReal_re]
    have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      rcases ArithmeticFunction.moebius_trichotomy d with h | h | h <;> simp [h]
    exact mul_le_of_le_one_left (by positivity) hmu
  rcases le_total s.re 2 with hle | hge
  · rw [min_eq_left hle]
    have hd_le1 : ∀ d ∈ m.divisors, (d : ℝ) ^ (s.re - 2) ≤ 1 := fun d hd => by
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
      calc (d : ℝ) ^ (s.re - 2) ≤ (d : ℝ) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
        _ = 1 := Real.rpow_zero _
    have hcard : (∑ d ∈ m.divisors, (d : ℝ) ^ (s.re - 2)) ≤ (m.divisors.card : ℝ) := by
      calc (∑ d ∈ m.divisors, (d : ℝ) ^ (s.re - 2))
          ≤ ∑ _d ∈ m.divisors, (1 : ℝ) := Finset.sum_le_sum hd_le1
        _ = (m.divisors.card : ℝ) := by simp
    calc (m : ℝ) ^ (-s.re) * ‖∑ d ∈ m.divisors, _‖
        ≤ (m : ℝ) ^ (-s.re) * (m.divisors.card : ℝ) :=
          mul_le_mul_of_nonneg_left (hsum.trans hcard) (by positivity)
      _ = (m.divisors.card : ℝ) * (m : ℝ) ^ (-s.re) := mul_comm _ _
  · rw [min_eq_right hge]
    have hd_lem : ∀ d ∈ m.divisors, (d : ℝ) ^ (s.re - 2) ≤ (m : ℝ) ^ (s.re - 2) := fun d hd => by
      have hd_le : (d : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.le_of_dvd hm hd.2
      exact Real.rpow_le_rpow (Nat.cast_nonneg d) hd_le (by linarith)
    have hcard : (∑ d ∈ m.divisors, (d : ℝ) ^ (s.re - 2)) ≤
        (m.divisors.card : ℝ) * (m : ℝ) ^ (s.re - 2) := by
      calc (∑ d ∈ m.divisors, (d : ℝ) ^ (s.re - 2))
          ≤ ∑ _d ∈ m.divisors, (m : ℝ) ^ (s.re - 2) := Finset.sum_le_sum hd_lem
        _ = (m.divisors.card : ℝ) * (m : ℝ) ^ (s.re - 2) := by simp
    calc (m : ℝ) ^ (-s.re) * ‖∑ d ∈ m.divisors, _‖
        ≤ (m : ℝ) ^ (-s.re) * ((m.divisors.card : ℝ) * (m : ℝ) ^ (s.re - 2)) :=
          mul_le_mul_of_nonneg_left (hsum.trans hcard) (by positivity)
      _ = (m.divisors.card : ℝ) * ((m : ℝ) ^ (-s.re) * (m : ℝ) ^ (s.re - 2)) := by ring
      _ = (m.divisors.card : ℝ) * (m : ℝ) ^ (-2 : ℝ) := by
          rw [← Real.rpow_add hm_pos]; congr 2; ring

/-- **`L²(ℝ/ℤ)` convergence across the entire right half-plane `Re s > 1/2`:**
`∑_{m=0}^∞ ‖bernoulliMoebiusMode s m‖² < ∞` whenever `1/2 < Re s`. -/
theorem summable_sq_norm_bernoulliMoebiusMode {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun m : ℕ => ‖bernoulliMoebiusMode s m‖ ^ 2) := by
  set σ₀ : ℝ := min s.re 2
  have hσ₀ : 1 / 2 < σ₀ := lt_min hs (by norm_num)
  set ε : ℝ := (σ₀ - 1 / 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hdiv⟩ := RHTower.card_divisors_le_const_mul_rpow hε
  have hmaj : Summable (fun m : ℕ => C ^ 2 * (m : ℝ) ^ (-(σ₀ + 1 / 2))) :=
    (Real.summable_nat_rpow.mpr (by linarith : -(σ₀ + 1 / 2) < -1)).mul_left (C ^ 2)
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m => ?_) hmaj
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [bernoulliMoebiusMode, Real.zero_rpow (show -(σ₀ + 1 / 2) ≠ 0 by linarith)]
  · have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
    have h1 := norm_bernoulliMoebiusMode_le s hm
    have h2 := hdiv m hm
    have hpt : ‖bernoulliMoebiusMode s m‖ ≤ C * (m : ℝ) ^ (ε - σ₀) := by
      calc ‖bernoulliMoebiusMode s m‖
          ≤ (m.divisors.card : ℝ) * (m : ℝ) ^ (-σ₀) := h1
        _ ≤ (C * (m : ℝ) ^ ε) * (m : ℝ) ^ (-σ₀) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = C * ((m : ℝ) ^ ε * (m : ℝ) ^ (-σ₀)) := by ring
        _ = C * (m : ℝ) ^ (ε - σ₀) := by rw [← Real.rpow_add hm_pos]; congr 2; ring
    calc ‖bernoulliMoebiusMode s m‖ ^ 2
        ≤ (C * (m : ℝ) ^ (ε - σ₀)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpt 2
      _ = C ^ 2 * ((m : ℝ) ^ (ε - σ₀)) ^ 2 := by ring
      _ = C ^ 2 * (m : ℝ) ^ (-(σ₀ + 1 / 2)) := by
          rw [← Real.rpow_natCast ((m : ℝ) ^ (ε - σ₀)) 2, ← Real.rpow_mul hm_pos.le]
          congr 2; dsimp [ε]; push_cast; ring

/-! ## 3. Composite-supported Dirichlet log-dipole with `O_ε(1)` tail and exact zero pair -/

/-- Ordinary Dirichlet log-coefficients `((k^{ρ₁ - 1} - k^{ρ₀ - 1} + k^{conj ρ₁ - 1} - k^{conj ρ₀ - 1}) / log k)`
for `k ≥ 2` (`0` for `k ≤ 1`), supported on all integers `k ≥ 2` (primes and composites alike). -/
def dipoleLogCoeff (ρ₀ ρ₁ : ℂ) (k : ℕ) : ℂ :=
  if k ≤ 1 then 0
  else ((k : ℂ) ^ (ρ₁ - 1) - (k : ℂ) ^ (ρ₀ - 1) +
    (k : ℂ) ^ (conj ρ₁ - 1) - (k : ℂ) ^ (conj ρ₀ - 1)) / (Real.log k : ℂ)

private theorem norm_dipoleLogCoeff_le (ρ₀ ρ₁ : ℂ) (k : ℕ) :
    ‖dipoleLogCoeff ρ₀ ρ₁ k‖ ≤
      if k ≤ 1 then 0 else (4 / Real.log 2) * (k : ℝ) ^ (max ρ₀.re ρ₁.re - 1) := by
  unfold dipoleLogCoeff
  split_ifs with hk
  · simp
  · have hk2 : 2 ≤ k := by omega
    have hk_pos : 0 < k := by omega
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlog_le : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) (by exact_mod_cast hk2)
    have hlog_pos : 0 < Real.log k := lt_of_lt_of_le hlog2 hlog_le
    set M : ℝ := max ρ₀.re ρ₁.re
    have hterm : ∀ w : ℂ, w.re ≤ M → ‖(k : ℂ) ^ (w - 1)‖ ≤ (k : ℝ) ^ (M - 1) := fun w hw => by
      rw [Complex.norm_natCast_cpow_of_pos hk_pos, Complex.sub_re, Complex.one_re]
      exact Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
    have hnum : ‖(k : ℂ) ^ (ρ₁ - 1) - (k : ℂ) ^ (ρ₀ - 1) +
        (k : ℂ) ^ (conj ρ₁ - 1) - (k : ℂ) ^ (conj ρ₀ - 1)‖ ≤ 4 * (k : ℝ) ^ (M - 1) := by
      have b1 := hterm ρ₁ (le_max_right _ _)
      have b2 := hterm ρ₀ (le_max_left _ _)
      have b3 := hterm (conj ρ₁) (by rw [Complex.conj_re]; exact le_max_right _ _)
      have b4 := hterm (conj ρ₀) (by rw [Complex.conj_re]; exact le_max_left _ _)
      calc ‖(k : ℂ) ^ (ρ₁ - 1) - (k : ℂ) ^ (ρ₀ - 1) +
              (k : ℂ) ^ (conj ρ₁ - 1) - (k : ℂ) ^ (conj ρ₀ - 1)‖
          ≤ ‖(k : ℂ) ^ (ρ₁ - 1) - (k : ℂ) ^ (ρ₀ - 1) + (k : ℂ) ^ (conj ρ₁ - 1)‖ +
              ‖(k : ℂ) ^ (conj ρ₀ - 1)‖ := norm_sub_le _ _
        _ ≤ (‖(k : ℂ) ^ (ρ₁ - 1) - (k : ℂ) ^ (ρ₀ - 1)‖ + ‖(k : ℂ) ^ (conj ρ₁ - 1)‖) +
              ‖(k : ℂ) ^ (conj ρ₀ - 1)‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ ((‖(k : ℂ) ^ (ρ₁ - 1)‖ + ‖(k : ℂ) ^ (ρ₀ - 1)‖) + ‖(k : ℂ) ^ (conj ρ₁ - 1)‖) +
              ‖(k : ℂ) ^ (conj ρ₀ - 1)‖ := add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
        _ ≤ 4 * (k : ℝ) ^ (M - 1) := by linarith
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog_pos]
    calc _ ≤ (4 * (k : ℝ) ^ (M - 1)) / Real.log k := div_le_div_of_nonneg_right hnum hlog_pos.le
      _ ≤ (4 * (k : ℝ) ^ (M - 1)) / Real.log 2 :=
          div_le_div_of_nonneg_left (by positivity) hlog2 hlog_le
      _ = (4 / Real.log 2) * (k : ℝ) ^ (M - 1) := by ring

/-- **Absolute convergence and uniform `O_ε(1)` vertical-strip bound on `Re s ≥ max(Re ρ₀, Re ρ₁) + ε`.** -/
theorem dipoleLogCoeff_uniform_bound (ρ₀ ρ₁ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ s : ℂ, max ρ₀.re ρ₁.re + ε ≤ s.re →
        LSeriesSummable (dipoleLogCoeff ρ₀ ρ₁) s ∧ ‖LSeries (dipoleLogCoeff ρ₀ ρ₁) s‖ ≤ B := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hsum_maj : Summable (fun k : ℕ => (4 / Real.log 2) * (k : ℝ) ^ (-(1 + ε))) :=
    (Real.summable_nat_rpow.mpr (by linarith : -(1 + ε) < -1)).mul_left _
  refine ⟨∑' k : ℕ, (4 / Real.log 2) * (k : ℝ) ^ (-(1 + ε)),
    tsum_nonneg fun _ => by positivity, fun s hs => ?_⟩
  have hpt : ∀ k : ℕ, ‖LSeries.term (dipoleLogCoeff ρ₀ ρ₁) s k‖ ≤
      (4 / Real.log 2) * (k : ℝ) ^ (-(1 + ε)) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp [Real.zero_rpow (show -(1 + ε) ≠ 0 by linarith)]
    · rw [LSeries.term_of_ne_zero hk_pos.ne', norm_div, Complex.norm_natCast_cpow_of_pos hk_pos]
      by_cases hk1 : k ≤ 1
      · have h0 := norm_dipoleLogCoeff_le ρ₀ ρ₁ k
        rw [if_pos hk1] at h0
        have heq0 : ‖dipoleLogCoeff ρ₀ ρ₁ k‖ = 0 := le_antisymm h0 (norm_nonneg _)
        rw [heq0, zero_div]
        positivity
      · have h0 := norm_dipoleLogCoeff_le ρ₀ ρ₁ k
        rw [if_neg hk1] at h0
        have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
        have hk_posR : 0 < (k : ℝ) := by exact_mod_cast hk_pos
        calc ‖dipoleLogCoeff ρ₀ ρ₁ k‖ / (k : ℝ) ^ s.re
            ≤ ((4 / Real.log 2) * (k : ℝ) ^ (max ρ₀.re ρ₁.re - 1)) / (k : ℝ) ^ s.re :=
              div_le_div_of_nonneg_right h0 (by positivity)
          _ = (4 / Real.log 2) * ((k : ℝ) ^ (max ρ₀.re ρ₁.re - 1) * (k : ℝ) ^ (-s.re)) := by
              rw [div_eq_mul_inv, Real.rpow_neg hk_posR.le]; ring
          _ = (4 / Real.log 2) * (k : ℝ) ^ (max ρ₀.re ρ₁.re - 1 - s.re) := by
              rw [← Real.rpow_add hk_posR]; ring_nf
          _ ≤ (4 / Real.log 2) * (k : ℝ) ^ (-(1 + ε)) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le hk_ge1 (by linarith)) (by positivity)
  have hsumm_norm : Summable (fun k : ℕ => ‖LSeries.term (dipoleLogCoeff ρ₀ ρ₁) s k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsum_maj
  exact ⟨hsumm_norm.of_norm, (norm_tsum_le_tsum_norm hsumm_norm).trans
    (Summable.tsum_le_tsum hpt hsumm_norm hsum_maj)⟩

/-- **Holomorphic continuation of `exp(L_{ρ₀, ρ₁}(s))` across `Re s = 1/2` with exact zero pair
`{ρ₀, conj ρ₀}`.**
For `Re ρ₁ < 1/2 < Re ρ₀ < 1`, `exp(LSeries (dipoleLogCoeff ρ₀ ρ₁) s)` agrees on `Re s > 1` with a
function `F` holomorphic on `{Re s > Re ρ₁}` (containing the closed half-plane `{Re s ≥ 1/2}`) whose
zeros on `{Re s > Re ρ₁}` are precisely `{ρ₀, conj ρ₀}`. -/
theorem exists_exp_dipoleLogCoeff_continuation {ρ₀ ρ₁ : ℂ}
    (h1 : ρ₁.re < 1 / 2) (h0 : 1 / 2 < ρ₀.re) (hlt1 : ρ₀.re < 1) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | ρ₁.re < s.re} ∧
      (∀ s : ℂ, 1 < s.re → F s = Complex.exp (LSeries (dipoleLogCoeff ρ₀ ρ₁) s)) ∧
      (∀ z : ℂ, ρ₁.re < z.re → (F z = 0 ↔ z = ρ₀ ∨ z = conj ρ₀)) := by
  open WorldsOfTheZeroConfiguration.PrimeEdits in
  have hmax_lt1 : max ρ₀.re ρ₁.re < 1 := max_lt hlt1 (by linarith)
  set Φ : ℂ → ℂ := fun s =>
    zetaRegular (s - (ρ₀ - 1)) + zetaRegular (s - (conj ρ₀ - 1)) -
      zetaRegular (s - (ρ₁ - 1)) - zetaRegular (s - (conj ρ₁ - 1))
  have hΦ_diff : Differentiable ℂ Φ :=
    (((differentiable_zetaRegular.comp (differentiable_id.sub_const _)).add
      (differentiable_zetaRegular.comp (differentiable_id.sub_const _))).sub
      (differentiable_zetaRegular.comp (differentiable_id.sub_const _))).sub
      (differentiable_zetaRegular.comp (differentiable_id.sub_const _))
  obtain ⟨K, hK_deriv⟩ :=
    HTGeometry.isExactOn_rightHalfPlane (a := ρ₁.re) hΦ_diff.differentiableOn
  -- `logMul (dipoleLogCoeff ρ₀ ρ₁)` equals `k^{ρ₁ - 1} - k^{ρ₀ - 1} + k^{conj ρ₁ - 1} - k^{conj ρ₀ - 1}`
  -- for ALL `k : ℕ` with `k ≥ 1` (at `k = 1`, `1 - 1 + 1 - 1 = 0`).
  have hlogMul_eq : ∀ s : ℂ, LSeries.term (LSeries.logMul (dipoleLogCoeff ρ₀ ρ₁)) s =
      LSeries.term (fun k : ℕ =>
        (k : ℂ) ^ (ρ₁ - 1) - (k : ℂ) ^ (ρ₀ - 1) +
          (k : ℂ) ^ (conj ρ₁ - 1) - (k : ℂ) ^ (conj ρ₀ - 1)) s := by
    intro s; funext k
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · rw [LSeries.term_of_ne_zero hk0, LSeries.term_of_ne_zero hk0]
      congr 1
      by_cases hk1 : k ≤ 1
      · have hkeq1 : k = 1 := by omega
        subst hkeq1
        simp [LSeries.logMul, dipoleLogCoeff]
      · have hlog_ne : (Real.log k : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast (show 1 < k by omega))).ne'
        simp only [LSeries.logMul, dipoleLogCoeff, if_neg hk1, ← Complex.natCast_log]
        exact div_mul_cancel₀ _ hlog_ne
  -- Derivative of `LSeries (dipoleLogCoeff ρ₀ ρ₁)` on `{Re s > 1}`.
  have habs_le1 : LSeries.abscissaOfAbsConv (dipoleLogCoeff ρ₀ ρ₁) ≤ 1 := by
    refine LSeries.abscissaOfAbsConv_le_of_le_const ⟨4 / Real.log 2, fun n hn => ?_⟩
    have h0 := norm_dipoleLogCoeff_le ρ₀ ρ₁ n
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    split_ifs at h0 with hn1
    · linarith [div_pos (by norm_num : (0 : ℝ) < 4) hlog2]
    · have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hrpow_le1 : (n : ℝ) ^ (max ρ₀.re ρ₁.re - 1) ≤ 1 := by
        calc (n : ℝ) ^ (max ρ₀.re ρ₁.re - 1) ≤ (n : ℝ) ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hn_ge1 (by linarith)
          _ = 1 := Real.rpow_zero _
      exact h0.trans (mul_le_of_le_one_right (by positivity) hrpow_le1)
  have hL_deriv : ∀ s : ℂ, 1 < s.re →
      HasDerivAt (LSeries (dipoleLogCoeff ρ₀ ρ₁))
        ((s - ρ₀)⁻¹ + (s - conj ρ₀)⁻¹ - (s - ρ₁)⁻¹ - (s - conj ρ₁)⁻¹ + Φ s) s := by
    intro s hs
    have habs : LSeries.abscissaOfAbsConv (dipoleLogCoeff ρ₀ ρ₁) < s.re :=
      lt_of_le_of_lt habs_le1 (by exact_mod_cast hs)
    have hd := LSeries_hasDerivAt habs
    have hsum1 := lseriesHasSum_cpow (a := ρ₁ - 1) (s := s) (by simp; linarith)
    have hsum2 := lseriesHasSum_cpow (a := ρ₀ - 1) (s := s) (by simp; linarith)
    have hsum3 := lseriesHasSum_cpow (a := conj ρ₁ - 1) (s := s) (by simp; linarith)
    have hsum4 := lseriesHasSum_cpow (a := conj ρ₀ - 1) (s := s) (by simp; linarith)
    have hcomb := (((hsum1.sub hsum2).add hsum3).sub hsum4).LSeries_eq
    have hL_eq : LSeries (LSeries.logMul (dipoleLogCoeff ρ₀ ρ₁)) s =
        riemannZeta (s - (ρ₁ - 1)) - riemannZeta (s - (ρ₀ - 1)) +
          riemannZeta (s - (conj ρ₁ - 1)) - riemannZeta (s - (conj ρ₀ - 1)) := by
      unfold LSeries at hcomb ⊢
      rw [hlogMul_eq s]
      exact hcomb
    have hne : ∀ w : ℂ, w.re < 1 → s - (w - 1) ≠ 1 := fun w hw h => by
      have := congrArg Complex.re h; simp at this; linarith
    refine hd.congr_deriv ?_
    rw [hL_eq,
      riemannZeta_eq_zetaRegular (hne ρ₁ (by linarith)),
      riemannZeta_eq_zetaRegular (hne ρ₀ hlt1),
      riemannZeta_eq_zetaRegular (hne (conj ρ₁) (by rw [Complex.conj_re]; linarith)),
      riemannZeta_eq_zetaRegular (hne (conj ρ₀) (by rw [Complex.conj_re]; exact hlt1)),
      show s - (ρ₁ - 1) - 1 = s - ρ₁ by ring,
      show s - (ρ₀ - 1) - 1 = s - ρ₀ by ring,
      show s - (conj ρ₁ - 1) - 1 = s - conj ρ₁ by ring,
      show s - (conj ρ₀ - 1) - 1 = s - conj ρ₀ by ring]
    dsimp [Φ]; ring
  -- Rational zero/pole factor `R(s) = ((s - ρ₀)(s - conj ρ₀)) / ((s - ρ₁)(s - conj ρ₁))`.
  set N₀ : ℂ → ℂ := fun s => (s - ρ₀) * (s - conj ρ₀)
  set D₁ : ℂ → ℂ := fun s => (s - ρ₁) * (s - conj ρ₁)
  have hD₁_ne : ∀ {s : ℂ}, ρ₁.re < s.re → D₁ s ≠ 0 := by
    intro s hs
    have hne1 : s - ρ₁ ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hne2 : s - conj ρ₁ ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact mul_ne_zero hne1 hne2
  have hN₀_ne : ∀ {s : ℂ}, 1 < s.re → N₀ s ≠ 0 := by
    intro s hs
    have hne1 : s - ρ₀ ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hne2 : s - conj ρ₀ ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact mul_ne_zero hne1 hne2
  set Q : ℂ → ℂ := fun s =>
    Complex.exp (LSeries (dipoleLogCoeff ρ₀ ρ₁) s - K s) * D₁ s / N₀ s
  have hQ_deriv : ∀ s : ℂ, 1 < s.re → HasDerivAt Q 0 s := by
    intro s hs
    have hs_ρ₁ : ρ₁.re < s.re := by linarith
    have hd_exp := ((hL_deriv s hs).sub (hK_deriv s hs_ρ₁)).cexp
    have hd_D₁ : HasDerivAt D₁ ((s - conj ρ₁) + (s - ρ₁)) s := by
      simpa [D₁, one_mul, mul_one] using
        ((hasDerivAt_id s).sub_const ρ₁).mul ((hasDerivAt_id s).sub_const (conj ρ₁))
    have hd_N₀ : HasDerivAt N₀ ((s - conj ρ₀) + (s - ρ₀)) s := by
      simpa [N₀, one_mul, mul_one] using
        ((hasDerivAt_id s).sub_const ρ₀).mul ((hasDerivAt_id s).sub_const (conj ρ₀))
    have hne_p0 : s - ρ₀ ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
    have hne_c0 : s - conj ρ₀ ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
    have hne_p1 : s - ρ₁ ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
    have hne_c1 : s - conj ρ₁ ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
    refine ((hd_exp.mul hd_D₁).div hd_N₀ (hN₀_ne hs)).congr_deriv ?_
    rw [div_eq_zero_iff]
    left
    dsimp [N₀, D₁]
    field_simp [hne_p0, hne_c0, hne_p1, hne_c1]
    ring
  have hUo : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2U : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  have hQ_const : ∀ s : ℂ, 1 < s.re → Q s = Q 2 := fun s hs =>
    hUo.is_const_of_deriv_eq_zero (convex_halfSpace_re_gt 1).isPreconnected
      (fun z hz => (hQ_deriv z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hQ_deriv z hz).deriv) hs h2U
  have hQ2_ne : Q 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (hD₁_ne (by show ρ₁.re < (2 : ℂ).re; norm_num; linarith)))
      (hN₀_ne h2U)
  set F : ℂ → ℂ := fun s => Q 2 * (N₀ s / D₁ s) * Complex.exp (K s)
  have hK_diffOn : DifferentiableOn ℂ K {s : ℂ | ρ₁.re < s.re} :=
    fun z hz => (hK_deriv z hz).differentiableAt.differentiableWithinAt
  have hN₀_diffOn : DifferentiableOn ℂ N₀ {s : ℂ | ρ₁.re < s.re} :=
    (differentiableOn_id.sub_const ρ₀).mul (differentiableOn_id.sub_const (conj ρ₀))
  have hD₁_diffOn : DifferentiableOn ℂ D₁ {s : ℂ | ρ₁.re < s.re} :=
    (differentiableOn_id.sub_const ρ₁).mul (differentiableOn_id.sub_const (conj ρ₁))
  refine ⟨F, ((differentiableOn_const (Q 2)).mul
    (hN₀_diffOn.div hD₁_diffOn fun z hz => hD₁_ne hz)).mul hK_diffOn.cexp,
    fun s hs => ?_, fun z hz => ?_⟩
  · have hs_ρ₁ : ρ₁.re < s.re := by linarith
    have hQs := hQ_const s hs
    have hrel : Complex.exp (LSeries (dipoleLogCoeff ρ₀ ρ₁) s - K s) = Q 2 * (N₀ s / D₁ s) := by
      rw [← hQs]
      dsimp [Q]
      field_simp [hD₁_ne hs_ρ₁, hN₀_ne hs]
    dsimp [F]
    rw [← hrel, ← Complex.exp_add, sub_add_cancel]
  · dsimp [F, N₀]
    have hDne := hD₁_ne hz
    simp [hQ2_ne, hDne, Complex.exp_ne_zero, sub_eq_zero]

end GaloisForLFunctions.SelbergClass
