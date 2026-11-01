import GaloisForLFunctions.ArithmeticCouplingTheory.TheSingleLatticeCouplingOnTheFiniteStratum
import GaloisForLFunctions.ArithmeticCouplingTheory.OneTwoPrimeLatticeDecidesTheCriticalLine
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The cone coupling has no deepest zero

On the cone `a, b ≥ 0` of one two-prime lattice the base points `aℓ_p + bℓ_q` are discrete, so the
increment transfer of `OneTwoPrimeLatticeDecidesTheCriticalLine` is unavailable. We read the cone
through its generating function instead.

By Hermitian symmetry a bound on the cone `(p^a, q^b)` is a bound on the reflected cone
`(p^{−a}, q^{−b})`, where `C = Σ_ρ w_ρ (X_ρ^a − 1)(Y_ρ^b − 1)` with `X_ρ = p^{ρ−½}`,
`Y_ρ = q^{ρ−½}` (`coupling_negCone`). Its second difference in `(a, b)` is
`R(a, b) = Σ_ρ d_ρ X_ρ^a Y_ρ^b`, `d_ρ = w_ρ (X_ρ − 1)(Y_ρ − 1)`, and `|R| ≤ 4M`.

Suppose a zero `ρ₀` has maximal real part `½ + Θ`, `Θ > 0`. Weight `R` by `x^a y^b` with
`x = X_{ρ₀}⁻¹ p^{−s}`, `y = Y_{ρ₀}⁻¹ q^{−s}`. Every zero has `|X_ρ x| ≤ p^{−s}` because `ρ₀` is
deepest, so the triple sum converges absolutely and

`T(s) = Σ_{a,b} R(a, b) x^a y^b = Σ_ρ d_ρ / ((1 − X_ρ x)(1 − Y_ρ y))`.

The left side is bounded uniformly in `s`, since `|x| ≤ p^{−Θ}`. On the right, the term of `ρ₀` is
`d_{ρ₀}/((1 − p^{−s})(1 − q^{−s})) ∼ d_{ρ₀}/(s² log p log q)`. Every other term is `o(s⁻²)`: a
double pole would need `X_ρ = X_{ρ₀}` and `Y_ρ = Y_{ρ₀}`, i.e. `ρ − ρ₀ ∈ (2πi/log p)ℤ ∩
(2πi/log q)ℤ = {0}`, since `log p/log q` is irrational. Dominated convergence (Tannery) gives
`s² T(s) → d_{ρ₀}/(log p log q) ≠ 0` (the spline sees `ρ₀`), contradicting boundedness.

**Theorem** (`riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling`). If the coupling of
`K_ζ` is bounded on `⟨p⟩₊ × ⟨q⟩₊`, then RH holds or no zero of `ζ` has maximal real part: the zero
width is not attained. On the finite stratum it is attained, which recovers
`riemannHypothesis_of_bounded_singleLatticeCoupling`.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx rightZeros rightZeros_zeta_eq_empty_iff)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

namespace ConeCoupling

/-- The spline weight of a zero of `ζ`. -/
abbrev wt (ρ : zetaZeroConfig.carrier) : ℂ :=
  zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) ρ

/-- The tower multiplier `e^{ℓ(ρ − ½)}` of a zero. -/
abbrev mult (ℓ : ℝ) (ρ : zetaZeroConfig.carrier) : ℂ := cexp ((ℓ : ℂ) * ((ρ : ℂ) - 1 / 2))

theorem norm_mult (ℓ : ℝ) (ρ : zetaZeroConfig.carrier) :
    ‖mult ℓ ρ‖ = Real.exp (ℓ * ((ρ : ℂ).re - 1 / 2)) := by
  rw [mult, Complex.norm_exp]; congr 1; simp

theorem summable_mult_pow (ℓp ℓq : ℝ) (a b : ℕ) :
    Summable fun ρ : zetaZeroConfig.carrier => mult ℓp ρ ^ a * mult ℓq ρ ^ b * wt ρ := by
  refine (summable_cexp_mul_Wsummand zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig cubicSpline_mem_realTests
    (a * ℓp + b * ℓq)).congr fun ρ => ?_
  rw [mult, mult, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem summable_norm_wt : Summable fun ρ : zetaZeroConfig.carrier => ‖wt ρ‖ :=
  ArithmeticCastelnuovoSeveri.summable_norm_Wsummand zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig
    (ArithmeticCastelnuovoSeveri.cx_contDiff cubicSpline_mem_realTests.1)
    (ArithmeticCastelnuovoSeveri.cx_hasCompactSupport cubicSpline_mem_realTests.2)
    (ArithmeticCastelnuovoSeveri.cx_contDiff cubicSpline_mem_realTests.1)
    (ArithmeticCastelnuovoSeveri.cx_hasCompactSupport cubicSpline_mem_realTests.2)

/-- On the strip the multiplier is at most `e^{ℓ/2}`. -/
theorem norm_mult_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (ρ : zetaZeroConfig.carrier) :
    ‖mult ℓ ρ‖ ≤ Real.exp (ℓ / 2) := by
  rw [norm_mult]
  have hs := zetaZeroConfig.strip ρ.1 ρ.2
  exact Real.exp_le_exp.mpr (by nlinarith [hs.1, hs.2])

/-- The Weil kernel of `ζ` as a sum over zeros. -/
theorem zetaKernel_eq_tsum (u : HeckeLattice) :
    zetaKernel u = ∑' ρ : zetaZeroConfig.carrier,
      cexp (-(scale heckeLogScale u : ℂ) * ((ρ : ℂ) - 1 / 2)) * wt ρ := by
  rw [zetaKernel]; exact orbitKernel_eq_tsum _ _ u

/-- On the reflected cone the kernel is `Σ_ρ X_ρ^a Y_ρ^b w_ρ`. -/
theorem zetaKernel_negCone {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (a b : ℕ) :
    zetaKernel (primeElt hp ^ (-(a : ℤ)) * primeElt hq ^ (-(b : ℤ))) =
      ∑' ρ : zetaZeroConfig.carrier,
        mult (Real.log p) ρ ^ a * mult (Real.log q) ρ ^ b * wt ρ := by
  rw [zetaKernel_eq_tsum]
  refine tsum_congr fun ρ => ?_
  rw [scale_mul, scale_zpow, scale_zpow, scale_primeElt, scale_primeElt, mult, mult,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- The coupling on the reflected cone as a sum over zeros. -/
theorem coupling_negCone {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (a b : ℕ) :
    coupling zetaKernel (primeElt hp ^ (-(a : ℤ))) (primeElt hq ^ (-(b : ℤ))) =
      ∑' ρ : zetaZeroConfig.carrier,
        (mult (Real.log p) ρ ^ a - 1) * (mult (Real.log q) ρ ^ b - 1) * wt ρ := by
  have k := zetaKernel_negCone hp hq
  have hu : zetaKernel (primeElt hp ^ (-(a : ℤ))) =
      ∑' ρ : zetaZeroConfig.carrier, mult (Real.log p) ρ ^ a * mult (Real.log q) ρ ^ 0 * wt ρ := by
    rw [← k a 0]; simp
  have hv : zetaKernel (primeElt hq ^ (-(b : ℤ))) =
      ∑' ρ : zetaZeroConfig.carrier, mult (Real.log p) ρ ^ 0 * mult (Real.log q) ρ ^ b * wt ρ := by
    rw [← k 0 b]; simp
  have h1 : zetaKernel 1 =
      ∑' ρ : zetaZeroConfig.carrier, mult (Real.log p) ρ ^ 0 * mult (Real.log q) ρ ^ 0 * wt ρ := by
    rw [← k 0 0]; simp
  have hs := fun m n => (summable_mult_pow (Real.log p) (Real.log q) m n).hasSum
  simp only [coupling]
  rw [k, hu, hv, h1, ← ((((hs a b).sub (hs a 0)).sub (hs 0 b)).add (hs 0 0)).tsum_eq]
  refine tsum_congr fun ρ => ?_
  ring

theorem norm_coupling_inv_inv {G : Type*} [CommGroup G] {K : G → ℂ} (hK : IsHermKernel K)
    (u v : G) : ‖coupling K u⁻¹ v⁻¹‖ = ‖coupling K u v‖ := by
  have hK' : ∀ w, K w⁻¹ = conj (K w) := hK
  have h : coupling K u⁻¹ v⁻¹ = conj (coupling K u v) := by
    simp only [coupling, map_add, map_sub, ← hK', mul_inv, inv_one]
  rw [h, Complex.norm_conj]

/-- `1 − e^{−ℓs} ≥ s(1 − e^{−ℓ})` on `[0, 1]`, by convexity of `exp`. -/
theorem mul_one_sub_exp_le {ℓ s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s * (1 - Real.exp (-ℓ)) ≤ 1 - Real.exp (-(ℓ * s)) := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-ℓ)) (sub_nonneg.mpr hs1) hs0
    (by ring : (1 - s) + s = 1)
  have e : (1 - s) • (0 : ℝ) + s • (-ℓ) = -(ℓ * s) := by simp only [smul_eq_mul]; ring
  rw [e] at h
  simp only [smul_eq_mul, Real.exp_zero, mul_one] at h
  nlinarith

/-- `s/(1 − e^{−ℓs}) → 1/ℓ` as `s → 0⁺`. -/
theorem tendsto_div_one_sub_exp {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (fun s : ℝ => s / (1 - Real.exp (-(ℓ * s)))) (𝓝[>] 0) (𝓝 ℓ⁻¹) := by
  have hd : HasDerivAt (fun s : ℝ => 1 - Real.exp (-(ℓ * s))) ℓ 0 := by
    have h1 : HasDerivAt (fun s : ℝ => -(ℓ * s)) (-ℓ) 0 := by
      have h0 := (hasDerivAt_id (0 : ℝ)).const_mul (-ℓ)
      simp only [id, mul_one] at h0
      simpa only [neg_mul] using h0
    simpa using h1.exp.const_sub 1
  have hs := hasDerivAt_iff_tendsto_slope_zero.mp hd
  simp only [zero_add, mul_zero, neg_zero, Real.exp_zero, sub_self, sub_zero, smul_eq_mul] at hs
  have hs' := (hs.mono_left (nhdsWithin_mono _ fun x (hx : 0 < x) => hx.ne')).inv₀ hℓ.ne'
  refine hs'.congr fun s => ?_
  rw [mul_inv, inv_inv, div_eq_mul_inv]

theorem tendsto_cdiv_one_sub_exp {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (fun s : ℝ => (s : ℂ) / (1 - cexp (-((ℓ : ℂ) * s)))) (𝓝[>] 0) (𝓝 ((ℓ : ℂ)⁻¹)) := by
  have h := (Complex.continuous_ofReal.tendsto ℓ⁻¹).comp (tendsto_div_one_sub_exp hℓ)
  rw [show ((ℓ : ℂ))⁻¹ = ((ℓ⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  refine h.congr fun s => ?_
  simp only [Function.comp_apply]
  push_cast
  rfl

theorem tendsto_cexp_neg_mul (ℓ : ℝ) :
    Tendsto (fun s : ℝ => cexp (-((ℓ : ℂ) * s))) (𝓝[>] 0) (𝓝 1) := by
  have hc : Continuous fun s : ℝ => cexp (-((ℓ : ℂ) * s)) := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem tendsto_ofReal_nhdsGT : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds

/-- A simple factor `(1 − α e^{−ℓs})⁻¹` with `α ≠ 1` stays bounded. -/
theorem tendsto_inv_one_sub {α : ℂ} (hα : α ≠ 1) (ℓ : ℝ) :
    Tendsto (fun s : ℝ => (1 - α * cexp (-((ℓ : ℂ) * s)))⁻¹) (𝓝[>] 0) (𝓝 ((1 - α)⁻¹)) := by
  have h := ((tendsto_cexp_neg_mul ℓ).const_mul α).const_sub 1
  rw [mul_one] at h
  exact h.inv₀ (sub_ne_zero.mpr (Ne.symm hα))

/-- Two zeros with the same multipliers at two primes coincide (`log p / log q ∉ ℚ`). -/
theorem eq_of_mult_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ρ ρ₀ : zetaZeroConfig.carrier}
    (hα : mult (Real.log p) ρ * cexp (-((Real.log p : ℂ) * ((ρ₀ : ℂ) - 1 / 2))) = 1)
    (hβ : mult (Real.log q) ρ * cexp (-((Real.log q : ℂ) * ((ρ₀ : ℂ) - 1 / 2))) = 1) :
    ρ = ρ₀ := by
  have hlp : (Real.log p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hlq : Real.log q ≠ 0 := (Real.log_pos (by exact_mod_cast hq.one_lt)).ne'
  rw [mult, ← Complex.exp_add, Complex.exp_eq_one_iff] at hα hβ
  obtain ⟨m, hm⟩ := hα
  obtain ⟨n, hn⟩ := hβ
  have hm' : (Real.log p : ℂ) * ((ρ : ℂ) - ρ₀) = m * (2 * (Real.pi : ℂ) * I) := by
    rw [← hm]; ring
  have hn' : (Real.log q : ℂ) * ((ρ : ℂ) - ρ₀) = n * (2 * (Real.pi : ℂ) * I) := by
    rw [← hn]; ring
  have h2 : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  have hc : (Real.log q : ℂ) * m = (Real.log p : ℂ) * n := by
    apply mul_right_cancel₀ h2
    linear_combination (-(Real.log q : ℂ)) * hm' + (Real.log p : ℂ) * hn'
  have hrel' : Real.log q * m = Real.log p * n := by exact_mod_cast hc
  have hm0 : m = 0 := by
    by_contra hm0
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [Int.cast_zero, mul_zero, mul_eq_zero] at hrel'
      rcases hrel' with h | h
      · exact hlq h
      · exact hm0 (by exact_mod_cast h)
    have hirr := RHTower.irrational_log_ratio hq hp hpq.symm
    have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hne := (irrational_iff_ne_rational _).mp hirr m n
    apply hne hn0
    rw [div_eq_div_iff hlq hn0']
    linarith
  rw [hm0, Int.cast_zero, zero_mul, mul_eq_zero] at hm'
  rcases hm' with h | h
  · exact absurd (by exact_mod_cast h) hlp
  · exact Subtype.ext (sub_eq_zero.mp h)

theorem exp_lt_one_of_neg {t : ℝ} (ht : t < 0) : Real.exp t < 1 := by
  simpa using Real.exp_lt_exp.mpr ht

/-- **Bounded cone coupling leaves no deepest zero.** If the coupling of `K_ζ` is bounded on
`⟨p⟩₊ × ⟨q⟩₊`, then RH holds or no zero of `ζ` has maximal real part. -/
theorem riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q)
    (hbd : ∃ M : ℝ, ∀ a b : ℕ, ‖coupling zetaKernel (primeElt hp ^ a) (primeElt hq ^ b)‖ ≤ M) :
    RiemannHypothesis ∨
      ∀ ρ₀ ∈ zetaZeroConfig.carrier, ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hRH, ρ₀, hρ₀, hmax⟩ := hcon
  obtain ⟨M, hM⟩ := hbd
  -- a right zero exists, so the deepest zero is right of the line
  have hne : (rightZeros zetaZeroConfig).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h; exact hRH (rightZeros_zeta_eq_empty_iff.mp h)
  obtain ⟨ρ₁, hρ₁, hρ₁re⟩ := hne
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : ℝ, Θ = ρ₀.re - 1 / 2 := ⟨_, rfl⟩
  have hΘ : 0 < Θ := by have := hmax ρ₁ hρ₁; rw [hΘdef]; linarith
  set ℓp := Real.log p
  set ℓq := Real.log q
  have hℓp : 0 < ℓp := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hℓq : 0 < ℓq := Real.log_pos (by exact_mod_cast hq.one_lt)
  set ρ₀' : zetaZeroConfig.carrier := ⟨ρ₀, hρ₀⟩
  set z₀ : ℂ := (ρ₀ : ℂ) - 1 / 2
  set X := mult ℓp
  set Y := mult ℓq
  set d : zetaZeroConfig.carrier → ℂ := fun ρ => (X ρ - 1) * (Y ρ - 1) * wt ρ
  -- the bound on the reflected cone and on the second differences
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0)
  have hM' : ∀ a b : ℕ,
      ‖coupling zetaKernel (primeElt hp ^ (-(a : ℤ))) (primeElt hq ^ (-(b : ℤ)))‖ ≤ M := by
    intro a b
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
      norm_coupling_inv_inv isHermKernel_zetaKernel]
    exact hM a b
  have hsC : ∀ m n : ℕ, Summable fun ρ : zetaZeroConfig.carrier =>
      (X ρ ^ m - 1) * (Y ρ ^ n - 1) * wt ρ := fun m n => by
    have h := (((summable_mult_pow ℓp ℓq m n).sub (summable_mult_pow ℓp ℓq m 0)).sub
      (summable_mult_pow ℓp ℓq 0 n)).add (summable_mult_pow ℓp ℓq 0 0)
    refine h.congr fun ρ => ?_
    simp only [pow_zero]; ring
  have hR : ∀ a b : ℕ, ‖∑' ρ, d ρ * X ρ ^ a * Y ρ ^ b‖ ≤ 4 * M := by
    intro a b
    have e : ∑' ρ, d ρ * X ρ ^ a * Y ρ ^ b =
        coupling zetaKernel (primeElt hp ^ (-((a + 1 : ℕ) : ℤ))) (primeElt hq ^ (-((b + 1 : ℕ) : ℤ))) -
          coupling zetaKernel (primeElt hp ^ (-((a + 1 : ℕ) : ℤ))) (primeElt hq ^ (-(b : ℤ))) -
          coupling zetaKernel (primeElt hp ^ (-(a : ℤ))) (primeElt hq ^ (-((b + 1 : ℕ) : ℤ))) +
          coupling zetaKernel (primeElt hp ^ (-(a : ℤ))) (primeElt hq ^ (-(b : ℤ))) := by
      rw [coupling_negCone, coupling_negCone, coupling_negCone, coupling_negCone,
        ← ((((hsC (a + 1) (b + 1)).hasSum.sub (hsC (a + 1) b).hasSum).sub
          (hsC a (b + 1)).hasSum).add (hsC a b).hasSum).tsum_eq]
      refine tsum_congr fun ρ => ?_
      simp only [d, pow_succ]; ring
    rw [e]
    calc _ ≤ _ := norm_sub_sub_add_le _ _ _ _
      _ ≤ M + M + M + M := add_le_add (add_le_add (add_le_add (hM' _ _) (hM' _ _)) (hM' _ _))
          (hM' _ _)
      _ = 4 * M := by ring
  -- weights of the generating function
  set x : ℝ → ℂ := fun s => cexp (-((ℓp : ℂ) * (z₀ + s)))
  set y : ℝ → ℂ := fun s => cexp (-((ℓq : ℂ) * (z₀ + s)))
  have hre_le : ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≤ ρ₀.re := fun ρ => hmax ρ.1 ρ.2
  have hnx : ∀ s : ℝ, ‖x s‖ = Real.exp (-(ℓp * (Θ + s))) := fun s => by
    simp only [x, Complex.norm_exp]; congr 1; simp [z₀, hΘdef]
  have hny : ∀ s : ℝ, ‖y s‖ = Real.exp (-(ℓq * (Θ + s))) := fun s => by
    simp only [y, Complex.norm_exp]; congr 1; simp [z₀, hΘdef]
  have hnXx : ∀ (ρ : zetaZeroConfig.carrier) (s : ℝ), ‖X ρ * x s‖ ≤ Real.exp (-(ℓp * s)) :=
    fun ρ s => by
      rw [norm_mul, norm_mult, hnx, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by
        linarith [mul_le_mul_of_nonneg_left (hre_le ρ) hℓp.le, congrArg (fun t => ℓp * t) hΘdef])
  have hnYy : ∀ (ρ : zetaZeroConfig.carrier) (s : ℝ), ‖Y ρ * y s‖ ≤ Real.exp (-(ℓq * s)) :=
    fun ρ s => by
      rw [norm_mul, norm_mult, hny, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by
        linarith [mul_le_mul_of_nonneg_left (hre_le ρ) hℓq.le, congrArg (fun t => ℓq * t) hΘdef])
  set rp := Real.exp (-(ℓp * Θ))
  set rq := Real.exp (-(ℓq * Θ))
  have hrp : rp < 1 := exp_lt_one_of_neg (by linarith [mul_pos hℓp hΘ])
  have hrq : rq < 1 := exp_lt_one_of_neg (by linarith [mul_pos hℓq hΘ])
  -- the generating function and its uniform bound
  set T : ℝ → ℂ := fun s => ∑' ab : ℕ × ℕ,
    (∑' ρ, d ρ * X ρ ^ ab.1 * Y ρ ^ ab.2) * x s ^ ab.1 * y s ^ ab.2
  set B := 4 * M * ((1 - rp)⁻¹ * (1 - rq)⁻¹)
  have hgeo : HasSum (fun ab : ℕ × ℕ => rp ^ ab.1 * rq ^ ab.2) ((1 - rp)⁻¹ * (1 - rq)⁻¹) :=
    (hasSum_geometric_of_lt_one (Real.exp_pos _).le hrp).mul
      (hasSum_geometric_of_lt_one (Real.exp_pos _).le hrq)
      ((summable_geometric_of_lt_one (Real.exp_pos _).le hrp).mul_of_nonneg
        (summable_geometric_of_lt_one (Real.exp_pos _).le hrq)
        (fun _ => pow_nonneg (Real.exp_pos _).le _) (fun _ => pow_nonneg (Real.exp_pos _).le _))
  have hTB : ∀ s : ℝ, 0 ≤ s → ‖T s‖ ≤ B := fun s hs => by
    refine tsum_of_norm_bounded (hgeo.mul_left (4 * M)) fun ab => ?_
    have hx : ‖x s‖ ≤ rp := by
      rw [hnx]; exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hℓp.le hs])
    have hy : ‖y s‖ ≤ rq := by
      rw [hny]; exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hℓq.le hs])
    have h4M : 0 ≤ 4 * M := by linarith
    calc ‖(∑' ρ, d ρ * X ρ ^ ab.1 * Y ρ ^ ab.2) * x s ^ ab.1 * y s ^ ab.2‖
        = ‖∑' ρ, d ρ * X ρ ^ ab.1 * Y ρ ^ ab.2‖ * ‖x s‖ ^ ab.1 * ‖y s‖ ^ ab.2 := by
          rw [norm_mul, norm_mul, norm_pow, norm_pow]
      _ ≤ 4 * M * rp ^ ab.1 * rq ^ ab.2 :=
          mul_le_mul (mul_le_mul (hR ab.1 ab.2) (pow_le_pow_left₀ (norm_nonneg _) hx _)
            (pow_nonneg (norm_nonneg _) _) h4M) (pow_le_pow_left₀ (norm_nonneg _) hy _)
            (pow_nonneg (norm_nonneg _) _) (mul_nonneg h4M (pow_nonneg (Real.exp_pos _).le _))
      _ = 4 * M * (rp ^ ab.1 * rq ^ ab.2) := by ring
  -- interchange: T(s) = Σ_ρ d_ρ / ((1 − X_ρ x)(1 − Y_ρ y))
  have hd_le : ∀ ρ, ‖d ρ‖ ≤ (Real.exp (ℓp / 2) + 1) * (Real.exp (ℓq / 2) + 1) * ‖wt ρ‖ :=
    fun ρ => by
      simp only [d, norm_mul]
      refine mul_le_mul_of_nonneg_right (mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity))
        (norm_nonneg _)
      · exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [norm_mult_le hℓp.le ρ])
      · exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [norm_mult_le hℓq.le ρ])
  have hsd : Summable fun ρ => ‖d ρ‖ :=
    (summable_norm_wt.mul_left ((Real.exp (ℓp / 2) + 1) * (Real.exp (ℓq / 2) + 1))).of_nonneg_of_le
      (fun _ => norm_nonneg _) hd_le
  set h : zetaZeroConfig.carrier → ℝ → ℂ := fun ρ s => (1 - X ρ * x s)⁻¹ * (1 - Y ρ * y s)⁻¹
  have hT : ∀ s : ℝ, 0 < s → T s = ∑' ρ, d ρ * h ρ s := fun s hs => by
    set ep := Real.exp (-(ℓp * s))
    set eq := Real.exp (-(ℓq * s))
    have hep : ep < 1 := exp_lt_one_of_neg (by nlinarith)
    have heq : eq < 1 := exp_lt_one_of_neg (by nlinarith)
    set F : zetaZeroConfig.carrier → ℕ × ℕ → ℂ :=
      fun ρ ab => d ρ * ((X ρ * x s) ^ ab.1 * (Y ρ * y s) ^ ab.2)
    have hgs : Summable fun ab : ℕ × ℕ => ep ^ ab.1 * eq ^ ab.2 :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le hep).mul_of_nonneg
        (summable_geometric_of_lt_one (Real.exp_pos _).le heq)
        (fun _ => pow_nonneg (Real.exp_pos _).le _) (fun _ => pow_nonneg (Real.exp_pos _).le _)
    have hFs : Summable (Function.uncurry F) := by
      refine Summable.of_norm_bounded (hsd.mul_of_nonneg hgs (fun _ => norm_nonneg _)
        (fun _ => by positivity)) fun ρab => ?_
      simp only [Function.uncurry, F]
      rw [norm_mul (d _), norm_mul ((X _ * x s) ^ _), norm_pow, norm_pow]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hnXx _ s) _)
        (pow_le_pow_left₀ (norm_nonneg _) (hnYy _ s) _) (by positivity) (by positivity))
        (norm_nonneg _)
    have hrow : ∀ ab : ℕ × ℕ, (∑' ρ, d ρ * X ρ ^ ab.1 * Y ρ ^ ab.2) * x s ^ ab.1 * y s ^ ab.2 =
        ∑' ρ, F ρ ab := fun ab => by
      rw [← tsum_mul_right, ← tsum_mul_right]
      refine tsum_congr fun ρ => ?_
      simp only [F, mul_pow]; ring
    have hcol : ∀ ρ, ∑' ab, F ρ ab = d ρ * h ρ s := fun ρ => by
      have hu : ‖X ρ * x s‖ < 1 := (hnXx ρ s).trans_lt hep
      have hv : ‖Y ρ * y s‖ < 1 := (hnYy ρ s).trans_lt heq
      have hsu : Summable fun n : ℕ => ‖(X ρ * x s) ^ n‖ :=
        (summable_geometric_of_lt_one (norm_nonneg _) hu).congr fun n => (norm_pow _ _).symm
      have hsv : Summable fun n : ℕ => ‖(Y ρ * y s) ^ n‖ :=
        (summable_geometric_of_lt_one (norm_nonneg _) hv).congr fun n => (norm_pow _ _).symm
      simp only [F, h]
      rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm hsu hsv,
        tsum_geometric_of_norm_lt_one hu, tsum_geometric_of_norm_lt_one hv]
    simp only [T]
    rw [tsum_congr hrow, hFs.tsum_comm]
    exact tsum_congr hcol
  -- the limit of `s² T(s)` is `0`
  have hlim1 : Tendsto (fun s : ℝ => (s : ℂ) ^ 2 * T s) (𝓝[>] 0) (𝓝 0) := by
    have hB : Tendsto (fun s : ℝ => s ^ 2 * B) (𝓝[>] 0) (𝓝 0) := by
      have := ((continuous_pow 2).mul continuous_const).tendsto (0 : ℝ) (f := fun s : ℝ => s ^ 2 * B)
      simpa using this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hB
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left (hTB s hs.le) (sq_nonneg _)
  -- the limit of `s² Σ_ρ d_ρ h_ρ(s)` is the `ρ₀`-term `d_{ρ₀}/(ℓ_p ℓ_q)`
  set D := (1 - Real.exp (-ℓp))⁻¹ * (1 - Real.exp (-ℓq))⁻¹
  have hD0 : 0 < 1 - Real.exp (-ℓp) := sub_pos.mpr (exp_lt_one_of_neg (by linarith))
  have hD0' : 0 < 1 - Real.exp (-ℓq) := sub_pos.mpr (exp_lt_one_of_neg (by linarith))
  have hbound : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ∀ ρ, ‖((s : ℝ) : ℂ) ^ 2 * (d ρ * h ρ s)‖ ≤ ‖d ρ‖ * D := by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with s ⟨hs0, hs1⟩ ρ
    have ha := mul_one_sub_exp_le (ℓ := ℓp) hs0.le hs1
    have hb := mul_one_sub_exp_le (ℓ := ℓq) hs0.le hs1
    have hA : 1 - Real.exp (-(ℓp * s)) ≤ ‖1 - X ρ * x s‖ := by
      have := norm_sub_norm_le (1 : ℂ) (X ρ * x s)
      rw [norm_one] at this; linarith [hnXx ρ s]
    have hB' : 1 - Real.exp (-(ℓq * s)) ≤ ‖1 - Y ρ * y s‖ := by
      have := norm_sub_norm_le (1 : ℂ) (Y ρ * y s)
      rw [norm_one] at this; linarith [hnYy ρ s]
    simp only [h, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    calc s ^ 2 * (‖d ρ‖ * (‖1 - X ρ * x s‖⁻¹ * ‖1 - Y ρ * y s‖⁻¹))
        ≤ s ^ 2 * (‖d ρ‖ * ((s * (1 - Real.exp (-ℓp)))⁻¹ * (s * (1 - Real.exp (-ℓq)))⁻¹)) := by
          gcongr
          · exact ha.trans hA
          · exact hb.trans hB'
      _ = ‖d ρ‖ * D := by
          simp only [D]; field_simp
  have hpoint : ∀ ρ, Tendsto (fun s : ℝ => (s : ℂ) ^ 2 * (d ρ * h ρ s)) (𝓝[>] 0)
      (𝓝 (if ρ = ρ₀' then d ρ₀' / ((ℓp : ℂ) * ℓq) else 0)) := by
    intro ρ
    -- `X_ρ x(s) = α e^{−ℓ_p s}` with `α = X_ρ / X_{ρ₀}`
    set α := X ρ * cexp (-((ℓp : ℂ) * z₀))
    set β := Y ρ * cexp (-((ℓq : ℂ) * z₀))
    have hXx : ∀ s : ℝ, X ρ * x s = α * cexp (-((ℓp : ℂ) * s)) := fun s => by
      simp only [x, α, mul_assoc, ← Complex.exp_add]; congr 2; ring
    have hYy : ∀ s : ℝ, Y ρ * y s = β * cexp (-((ℓq : ℂ) * s)) := fun s => by
      simp only [y, β, mul_assoc, ← Complex.exp_add]; congr 2; ring
    have hform : ∀ s : ℝ, (s : ℂ) ^ 2 * (d ρ * h ρ s) =
        d ρ * ((s : ℂ) * (1 - α * cexp (-((ℓp : ℂ) * s)))⁻¹) *
          ((s : ℂ) * (1 - β * cexp (-((ℓq : ℂ) * s)))⁻¹) := fun s => by
      simp only [h, hXx, hYy]; ring
    simp only [hform]
    by_cases hρ : ρ = ρ₀'
    · subst hρ
      have hα : α = 1 := by
        simp only [α, X, ← Complex.exp_add, z₀]; rw [← Complex.exp_zero]; congr 1; ring
      have hβ : β = 1 := by
        simp only [β, Y, ← Complex.exp_add, z₀]; rw [← Complex.exp_zero]; congr 1; ring
      rw [if_pos rfl, hα, hβ]
      simp only [one_mul, ← div_eq_mul_inv]
      have h1 := tendsto_cdiv_one_sub_exp hℓp
      have h2 := tendsto_cdiv_one_sub_exp hℓq
      have := (h1.const_mul (d ρ₀')).mul h2
      convert this using 2
      field_simp
    · rw [if_neg hρ]
      have hnot : ¬ (α = 1 ∧ β = 1) := fun ⟨ha, hb⟩ => hρ (eq_of_mult_eq hp hq hpq ha hb)
      have hs := tendsto_ofReal_nhdsGT
      by_cases hα : α = 1
      · have hβ : β ≠ 1 := fun hb => hnot ⟨hα, hb⟩
        rw [hα]
        simp only [one_mul]
        have := (((tendsto_cdiv_one_sub_exp hℓp).congr fun s => div_eq_mul_inv _ _).const_mul
          (d ρ)).mul (hs.mul (tendsto_inv_one_sub hβ ℓq))
        simpa using this
      · by_cases hβ : β = 1
        · rw [hβ]
          simp only [one_mul]
          have := ((hs.mul (tendsto_inv_one_sub hα ℓp)).const_mul (d ρ)).mul
            ((tendsto_cdiv_one_sub_exp hℓq).congr fun s => by rw [div_eq_mul_inv])
          simpa using this
        · have := ((hs.mul (tendsto_inv_one_sub hα ℓp)).const_mul (d ρ)).mul
            (hs.mul (tendsto_inv_one_sub hβ ℓq))
          simpa using this
  have hlim2 := tendsto_tsum_of_dominated_convergence (hsd.mul_right D) hpoint hbound
  rw [tsum_ite_eq] at hlim2
  -- both limits describe `s² T(s)`
  have heq : (fun s : ℝ => (s : ℂ) ^ 2 * T s) =ᶠ[𝓝[>] 0]
      fun s => ∑' ρ, (s : ℂ) ^ 2 * (d ρ * h ρ s) := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    rw [hT s hs, tsum_mul_left]
  have hzero := tendsto_nhds_unique (hlim1.congr' heq) hlim2
  -- but the deepest zero has a nonzero coefficient
  have hw : wt ρ₀' ≠ 0 :=
    ArithmeticKreinLangerTheory.Wsummand_ne_zero_of_rightZero
      ⟨hρ₀, by have h := hΘ; rw [hΘdef] at h; linarith⟩
  have hX : X ρ₀' ≠ 1 := fun h1 => by
    have := congrArg norm h1
    rw [norm_mult, norm_one] at this
    have : ℓp * ((ρ₀ : ℂ).re - 1 / 2) = 0 := by
      rw [← Real.exp_eq_one_iff]; exact this
    have h3 : ℓp * Θ = 0 := by rw [hΘdef]; exact this
    nlinarith [mul_pos hℓp hΘ]
  have hY : Y ρ₀' ≠ 1 := fun h1 => by
    have := congrArg norm h1
    rw [norm_mult, norm_one] at this
    have : ℓq * ((ρ₀ : ℂ).re - 1 / 2) = 0 := by
      rw [← Real.exp_eq_one_iff]; exact this
    have h3 : ℓq * Θ = 0 := by rw [hΘdef]; exact this
    nlinarith [mul_pos hℓq hΘ]
  have hd0 : d ρ₀' ≠ 0 := mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hX) (sub_ne_zero.mpr hY)) hw
  have hden : (ℓp : ℂ) * ℓq ≠ 0 := mul_ne_zero (by exact_mod_cast hℓp.ne') (by exact_mod_cast hℓq.ne')
  exact hd0 (by rw [eq_comm, div_eq_zero_iff] at hzero; exact hzero.resolve_right hden)

/-- On the finite stratum a deepest zero exists, so bounded cone coupling is RH there. -/
theorem riemannHypothesis_of_bounded_coneCoupling_of_finite {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hfin : (rightZeros zetaZeroConfig).Finite)
    (hbd : ∃ M : ℝ, ∀ a b : ℕ, ‖coupling zetaKernel (primeElt hp ^ a) (primeElt hq ^ b)‖ ≤ M) :
    RiemannHypothesis := by
  rcases riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling hp hq hpq hbd with h | h
  · exact h
  · by_contra hRH
    have hne : (rightZeros zetaZeroConfig).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]; intro he; exact hRH (rightZeros_zeta_eq_empty_iff.mp he)
    obtain ⟨ρ₀, hρ₀, hmax⟩ := Set.exists_max_image _ (fun ρ : ℂ => ρ.re) hfin hne
    obtain ⟨ρ, hρ, hlt⟩ := h ρ₀ hρ₀.1
    have hρR : ρ ∈ rightZeros zetaZeroConfig := ⟨hρ, by linarith [hρ₀.2]⟩
    linarith [hmax ρ hρR]

end ConeCoupling

end GaloisForLFunctions.ArithmeticCouplingTheory
