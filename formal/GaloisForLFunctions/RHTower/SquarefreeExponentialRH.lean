import GaloisForLFunctions.RHTower.SquarefreeExponentialCascade
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.RHTower.FareyDiscrepancyOmega
import GaloisForLFunctions.HTGeometry.TwistedMobiusLambertWittSeries

/-!
# RH is the `t^{-1/4}` law for the exponentially weighted squarefree count

Let `A(t) = Σ_{n ≥ 1} μ(n)² e^{-nt}` and `c = 6/π²`.

**Theorem** (`riemannHypothesis_iff_squarefree_exponential`).
`RH ⟺ ∀ ε > 0, A(t) = c/t + O(t^{-1/4-ε})` on `0 < t ≤ 1`.

The converse direction is the halving cascade (`riemannHypothesis_of_expBound_quarter`). The forward
direction is proved here from Littlewood's Mertens bound, in a general form
(`abs_profile_sub_le_of_mertens`): if `|M(N)| ≤ B (N+1)^θ` for all `N`, with `0 ≤ θ ≤ 1`, then
`|A(t) - c/t| ≤ B (4 + Z) t^{-β}` for `0 < t ≤ 1` and every `β ≤ 1` with `2β > θ`, where
`Z = Σ_j (j+2)^{θ-1-2β}`.

**Proof.** Lambert regrouping over square divisors gives `A(t) = Σ_k μ(k)/(e^{k²t} - 1)`, so
`A(t) - c/t = Σ_k μ(k) h(k²t)` with `h(u) = 1/(eᵘ - 1) - 1/u`. The kernel `h` is increasing on
`(0, ∞)` (because `2 sinh(u/2) ≥ u`), satisfies `-1 ≤ h ≤ 0`, and so `|h(u)| ≤ min(1, 1/u) ≤ u^{-β}`.
Summation by parts against `M` and a second summation by parts against `(k+1)^θ` give the bound.
-/

open Filter Topology MeasureTheory Set Asymptotics Complex
open GaloisForLFunctions.HTGeometry
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace RHTower.SquarefreeExponential

noncomputable section

/-! ## The kernel `h(u) = 1/(eᵘ - 1) - 1/u` -/

/-- `h(u) = 1/(eᵘ - 1) - 1/u`. -/
def kernelH (u : ℝ) : ℝ := 1 / (Real.exp u - 1) - 1 / u

theorem exp_sub_one_pos {u : ℝ} (hu : 0 < u) : 0 < Real.exp u - 1 := by
  linarith [Real.add_one_le_exp u]

theorem kernelH_nonpos {u : ℝ} (hu : 0 < u) : kernelH u ≤ 0 := by
  unfold kernelH
  have h := one_div_le_one_div_of_le hu (show u ≤ Real.exp u - 1 by linarith [Real.add_one_le_exp u])
  linarith

theorem neg_one_le_kernelH {u : ℝ} (hu : 0 < u) : -1 ≤ kernelH u := by
  unfold kernelH
  have he := exp_sub_one_pos hu
  rcases le_or_gt 1 u with h1 | h1
  · have : 1 / u ≤ 1 := by rw [div_le_one hu]; exact h1
    have : 0 ≤ 1 / (Real.exp u - 1) := by positivity
    linarith
  · have hb : (1 - u) * Real.exp u ≤ 1 := by
      have h := Real.add_one_le_exp (-u)
      have he' : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos u, Real.exp_pos (-u)]
    have hkey : 1 / u - 1 ≤ 1 / (Real.exp u - 1) := by
      rw [div_sub_one hu.ne', div_le_div_iff₀ hu he]
      nlinarith
    linarith

theorem neg_inv_le_kernelH {u : ℝ} (hu : 0 < u) : -(1 / u) ≤ kernelH u := by
  unfold kernelH
  have : 0 ≤ 1 / (Real.exp u - 1) := le_of_lt (one_div_pos.mpr (exp_sub_one_pos hu))
  linarith

/-- `|h(u)| ≤ u^{-β}` for `0 ≤ β ≤ 1`. -/
theorem abs_kernelH_le_rpow {u β : ℝ} (hu : 0 < u) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    |kernelH u| ≤ u ^ (-β) := by
  rw [abs_of_nonpos (kernelH_nonpos hu)]
  rcases le_or_gt u 1 with h1 | h1
  · have := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu h1 (by linarith : -β ≤ 0)
    linarith [neg_one_le_kernelH hu]
  · have h2 : u ^ (-1 : ℝ) ≤ u ^ (-β) := Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    rw [Real.rpow_neg_one] at h2
    have := neg_inv_le_kernelH hu
    rw [one_div] at this
    linarith

theorem abs_kernelH_le_inv {u : ℝ} (hu : 0 < u) : |kernelH u| ≤ 1 / u := by
  rw [abs_of_nonpos (kernelH_nonpos hu)]
  linarith [neg_inv_le_kernelH hu]

/-- `(eᵘ - 1)² ≥ u² eᵘ`, from `2 sinh(u/2) ≥ u`. -/
theorem sq_mul_exp_le_sq_exp_sub_one {u : ℝ} (hu : 0 < u) :
    u ^ 2 * Real.exp u ≤ (Real.exp u - 1) ^ 2 := by
  have hs : u / 2 ≤ Real.sinh (u / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  rw [Real.sinh_eq] at hs
  have e1 : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (u / 2) * Real.exp (-(u / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hlin : u * Real.exp (u / 2) ≤ Real.exp u - 1 := by
    have hp := Real.exp_pos (u / 2)
    nlinarith
  have hp := Real.exp_pos (u / 2)
  have h0 : 0 ≤ u * Real.exp (u / 2) := by positivity
  calc u ^ 2 * Real.exp u = (u * Real.exp (u / 2)) ^ 2 := by rw [← e1]; ring
    _ ≤ (Real.exp u - 1) ^ 2 := pow_le_pow_left₀ h0 hlin 2

theorem hasDerivAt_kernelH {u : ℝ} (hu : 0 < u) :
    HasDerivAt kernelH (-(Real.exp u) / (Real.exp u - 1) ^ 2 + 1 / u ^ 2) u := by
  have he := (exp_sub_one_pos hu).ne'
  have h1 := (hasDerivAt_const u (1 : ℝ)).div ((Real.hasDerivAt_exp u).sub_const 1) he
  have h2 := (hasDerivAt_const u (1 : ℝ)).div (hasDerivAt_id' u) hu.ne'
  refine (h1.sub h2).congr_deriv ?_
  field_simp
  ring

/-- `h` is increasing on `(0, ∞)`. -/
theorem monotoneOn_kernelH : MonotoneOn kernelH (Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · intro u hu
    exact (hasDerivAt_kernelH hu).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    exact (hasDerivAt_kernelH hu).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    have hu' : 0 < u := hu
    rw [(hasDerivAt_kernelH hu').deriv]
    have he := exp_sub_one_pos hu'
    have hkey := sq_mul_exp_le_sq_exp_sub_one hu'
    have : Real.exp u / (Real.exp u - 1) ^ 2 ≤ 1 / u ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    rw [neg_div]
    linarith

/-! ## Lambert regrouping over square divisors -/

/-- `A(t) = Σ_k μ(k)/(e^{k²t} - 1)`. -/
theorem profile_eq_tsum {t : ℝ} (ht : 0 < t) :
    profile t = ∑' k : ℕ, (((μ k : ℝ) * (1 / (Real.exp ((k : ℝ) ^ 2 * t) - 1)) : ℝ) : ℂ) := by
  set z : ℂ := ((Real.exp (-t) : ℝ) : ℂ) with hz
  have hz1 : ‖z‖ < 1 := by
    rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  set f : ℕ → ℂ := fun n => ((sqrtPart (μ : ArithmeticFunction ℤ) n : ℤ) : ℂ) with hf
  have hfb : ∀ n, ‖f n‖ ≤ 1 := by
    intro n
    rw [hf]
    simp only [Complex.norm_intCast]
    rw [sqrtPart_apply]
    split_ifs
    · exact_mod_cast abs_moebius_le_one
    · simp
  have hL := tsum_lambert_eq_tsum_divisorSum hfb hz1
  -- the divisor side is the profile
  have hR : ∑' m : ℕ, (∑ d ∈ m.divisors, f d) * z ^ m = profile t := by
    rw [profile, coeffLaplaceProfile]
    refine tsum_congr fun m => ?_
    have hdiv : ∑ d ∈ m.divisors, f d = sqfCoeff m := by
      rw [hf, sqfCoeff, pmul_apply, ← sum_divisors_sqrtPart_moebius m]
      push_cast
      rfl
    rw [hdiv, hz, ← Complex.ofReal_pow, ← Real.exp_nat_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  -- the Lambert side lives on squares
  have hsupp : Function.support (fun n : ℕ => f n * (z ^ n / (1 - z ^ n))) ⊆
      Set.range (fun k : ℕ => k ^ 2) := by
    intro n hn
    by_contra hns
    apply hn
    have hnsq : ¬ IsSquare n := by
      rintro ⟨r, hr⟩
      exact hns ⟨r, by simp only [hr, sq]⟩
    simp only [hf, sqrtPart_apply_of_not_isSquare _ hnsq, Int.cast_zero, zero_mul]
  have hinj : Function.Injective (fun k : ℕ => k ^ 2) :=
    fun a b h => Nat.pow_left_injective (by norm_num) h
  have hsq := hinj.tsum_eq hsupp
  rw [← hR, ← hL, ← hsq]
  refine tsum_congr fun k => ?_
  simp only [hf, sqrtPart_apply_sq]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hkt : 0 < (k : ℝ) ^ 2 * t := by positivity
    have hx : Real.exp (-t) ^ (k ^ 2) * Real.exp ((k : ℝ) ^ 2 * t) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      ring_nf
      simp
    have hpos : 1 < Real.exp ((k : ℝ) ^ 2 * t) := Real.one_lt_exp_iff.mpr hkt
    have hq1 : Real.exp (-t) ^ (k ^ 2) < 1 :=
      pow_lt_one₀ (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
        (pow_ne_zero 2 hk.ne')
    have hq : Real.exp (-t) ^ (k ^ 2) / (1 - Real.exp (-t) ^ (k ^ 2)) =
        1 / (Real.exp ((k : ℝ) ^ 2 * t) - 1) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]
      nlinarith
    rw [hz, ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_div, hq]
    push_cast
    ring

/-- `A(t) - c/t = Σ_k μ(k) h(k²t)`. -/
theorem profile_sub_eq_tsum {t : ℝ} (ht : 0 < t) :
    profile t - density / t = ((∑' k : ℕ, (μ k : ℝ) * kernelH ((k : ℝ) ^ 2 * t) : ℝ) : ℂ) := by
  have hsum1 : Summable fun k : ℕ => (μ k : ℝ) * (1 / (Real.exp ((k : ℝ) ^ 2 * t) - 1)) := by
    refine Summable.of_norm_bounded ((Real.summable_one_div_nat_pow.mpr one_lt_two).div_const t)
      fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hkt : 0 < (k : ℝ) ^ 2 * t := by positivity
      have he := exp_sub_one_pos hkt
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr he)]
      have hm : |(μ k : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      have h1 : 1 / (Real.exp ((k : ℝ) ^ 2 * t) - 1) ≤ 1 / ((k : ℝ) ^ 2 * t) :=
        one_div_le_one_div_of_le hkt (by linarith [Real.add_one_le_exp ((k : ℝ) ^ 2 * t)])
      calc |(μ k : ℝ)| * (1 / (Real.exp ((k : ℝ) ^ 2 * t) - 1))
          ≤ 1 * (1 / ((k : ℝ) ^ 2 * t)) :=
            mul_le_mul hm h1 (le_of_lt (one_div_pos.mpr he)) zero_le_one
        _ = 1 / (k : ℝ) ^ 2 / t := by rw [one_mul, div_div]
  have hsum2 : Summable fun k : ℕ => (μ k : ℝ) / (k : ℝ) ^ 2 / t := by
    refine Summable.of_norm_bounded ((Real.summable_one_div_nat_pow.mpr one_lt_two).div_const t)
      fun k => ?_
    rw [Real.norm_eq_abs, abs_div, abs_div, abs_of_pos ht, abs_of_nonneg (sq_nonneg (k : ℝ))]
    have hm : |(μ k : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk2 : 0 < (k : ℝ) ^ 2 := by positivity
      gcongr
  have hdens : density / t = ((∑' k : ℕ, (μ k : ℝ) / (k : ℝ) ^ 2 / t : ℝ) : ℂ) := by
    rw [density, Sieve.squarefreeDensity, ← Complex.ofReal_div, tsum_div_const]
  rw [profile_eq_tsum ht, hdens, ← Complex.ofReal_tsum, ← Complex.ofReal_sub,
    ← hsum1.tsum_sub hsum2]
  congr 1
  refine tsum_congr fun k => ?_
  unfold kernelH
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hk2 : (k : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp

/-! ## Summation by parts -/

theorem sum_range_mul_sub_eq (f G : ℕ → ℝ) (p : ℕ) :
    ∑ j ∈ Finset.range p, f j * (G (j + 1) - G j) =
      f p * G p - f 0 * G 0 - ∑ j ∈ Finset.range p, (f (j + 1) - f j) * G (j + 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem sum_range_moebius_succ_eq (n : ℕ) :
    ∑ i ∈ Finset.range n, (μ (i + 1) : ℝ) = mertensFunctionReal n := by
  induction n with
  | zero => simp [mertensFunctionReal]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold mertensFunctionReal
    rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

/-- `(x+1)^θ - x^θ ≤ x^{θ-1}` for `x ≥ 1`, `0 ≤ θ ≤ 1`. -/
theorem rpow_add_one_sub_rpow_le {x θ : ℝ} (hx : 1 ≤ x) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (x + 1) ^ θ - x ^ θ ≤ x ^ (θ - 1) := by
  have hx0 : 0 < x := by linarith
  have hb := rpow_one_add_le_one_add_mul_self (s := 1 / x)
    (by have : 0 ≤ 1 / x := by positivity
        linarith) hθ0 hθ1
  have e : x + 1 = x * (1 + 1 / x) := by field_simp
  rw [e, Real.mul_rpow hx0.le (by positivity)]
  have hxθ : 0 ≤ x ^ θ := Real.rpow_nonneg hx0.le _
  have e2 : x ^ θ * (θ * (1 / x)) = θ * x ^ (θ - 1) := by
    rw [Real.rpow_sub_one hx0.ne']; field_simp
  have hle : θ * x ^ (θ - 1) ≤ x ^ (θ - 1) :=
    mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) hθ1
  calc x ^ θ * (1 + 1 / x) ^ θ - x ^ θ ≤ x ^ θ * (1 + θ * (1 / x)) - x ^ θ := by
        gcongr
    _ = x ^ θ * (θ * (1 / x)) := by ring
    _ ≤ x ^ (θ - 1) := by rw [e2]; exact hle

/-- **Bound from a Mertens estimate.** If `|M(N)| ≤ B (N+1)^θ` for all `N`, then
`|A(t) - c/t| ≤ B (4 + Z) t^{-β}` on `0 < t ≤ 1`, for `0 ≤ θ ≤ 1`, `θ < 2β`, `β ≤ 1`. -/
theorem abs_tsum_moebius_kernelH_le {θ β B : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθβ : θ < 2 * β)
    (hβ1 : β ≤ 1) (hB : 0 ≤ B) (hM : ∀ n : ℕ, |mertensFunctionReal n| ≤ B * ((n : ℝ) + 1) ^ θ)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |∑' k : ℕ, (μ k : ℝ) * kernelH ((k : ℝ) ^ 2 * t)| ≤
      B * (4 + ∑' j : ℕ, ((j : ℝ) + 2) ^ (θ - 1 - 2 * β)) * t ^ (-β) := by
  have hβ0 : 0 ≤ β := by linarith
  set p : ℝ := θ - 1 - 2 * β with hp
  have hZs : Summable fun j : ℕ => ((j : ℝ) + 2) ^ p := by
    have h := (Real.summable_nat_rpow (p := p)).mpr (by rw [hp]; linarith)
    have h2 := (summable_nat_add_iff 2).mpr h
    refine h2.congr fun j => ?_
    push_cast; ring_nf
  set Z : ℝ := ∑' j : ℕ, ((j : ℝ) + 2) ^ p with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun j => Real.rpow_nonneg (by positivity) _
  have htβ : 1 ≤ t ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by linarith)
  -- the shifted kernel values
  set G : ℕ → ℝ := fun j => kernelH (((j : ℝ) + 1) ^ 2 * t) with hG
  have hGpos : ∀ j : ℕ, 0 < ((j : ℝ) + 1) ^ 2 * t := fun j => by positivity
  have hGmono : ∀ j : ℕ, G j ≤ G (j + 1) := by
    intro j
    refine monotoneOn_kernelH (hGpos j) (hGpos (j + 1)) ?_
    push_cast
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1 + 1) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this ht.le
  have hGabs : ∀ j : ℕ, |G j| ≤ ((j : ℝ) + 1) ^ (-(2 * β)) * t ^ (-β) := by
    intro j
    have h := abs_kernelH_le_rpow (hGpos j) hβ0 hβ1
    have e : (((j : ℝ) + 1) ^ 2 * t) ^ (-β) = ((j : ℝ) + 1) ^ (-(2 * β)) * t ^ (-β) := by
      rw [Real.mul_rpow (by positivity) ht.le,
        show ((j : ℝ) + 1) ^ 2 = ((j : ℝ) + 1) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast],
        ← Real.rpow_mul (by positivity)]
      congr 2
      push_cast
      ring
    exact h.trans (le_of_eq e)
  have hGle : ∀ j : ℕ, G j ≤ 0 := fun j => kernelH_nonpos (hGpos j)
  -- summability of the series
  have hsum : Summable fun k : ℕ => (μ k : ℝ) * kernelH ((k : ℝ) ^ 2 * t) := by
    refine Summable.of_norm_bounded ((Real.summable_one_div_nat_pow.mpr one_lt_two).div_const t)
      fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [kernelH]
    · have hkt : 0 < (k : ℝ) ^ 2 * t := by positivity
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hm : |(μ k : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      calc |(μ k : ℝ)| * |kernelH ((k : ℝ) ^ 2 * t)| ≤ 1 * (1 / ((k : ℝ) ^ 2 * t)) :=
            mul_le_mul hm (abs_kernelH_le_inv hkt) (abs_nonneg _) zero_le_one
        _ = 1 / (k : ℝ) ^ 2 / t := by rw [one_mul, div_div]
  -- shifted partial sums
  set S : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, (μ (j + 1) : ℝ) * G j with hS
  have hSlim : Tendsto S atTop (𝓝 (∑' k : ℕ, (μ k : ℝ) * kernelH ((k : ℝ) ^ 2 * t))) := by
    have h := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, hS, hG]
    rw [Finset.sum_range_succ']
    simp
  -- the uniform bound on the partial sums
  have hbound : ∀ n : ℕ, |S n| ≤ B * (4 + Z) * t ^ (-β) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hS, Finset.range_zero, Finset.sum_empty, abs_zero]
      have : 0 ≤ 4 + Z := by linarith
      positivity
    -- first summation by parts
    have hparts := Finset.sum_range_by_parts G (fun j => (μ (j + 1) : ℝ)) n
    simp only [smul_eq_mul] at hparts
    have hS' : S n = G (n - 1) * mertensFunctionReal n -
        ∑ j ∈ Finset.range (n - 1), (G (j + 1) - G j) * mertensFunctionReal (j + 1) := by
      rw [hS]
      simp only
      rw [show (∑ j ∈ Finset.range n, (μ (j + 1) : ℝ) * G j) =
          ∑ j ∈ Finset.range n, G j * (μ (j + 1) : ℝ) from
        Finset.sum_congr rfl fun j _ => mul_comm _ _, hparts, sum_range_moebius_succ_eq]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sum_range_moebius_succ_eq]
      push_cast
      rfl
    -- the boundary term
    have hbd : |G (n - 1) * mertensFunctionReal n| ≤ 2 * B * t ^ (-β) := by
      have hn1 : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_mul]
      have h1 := hGabs (n - 1)
      rw [hn1] at h1
      have h2 := hM n
      have hpow : ((n : ℝ) + 1) ^ θ ≤ 2 * (n : ℝ) ^ θ := by
        calc ((n : ℝ) + 1) ^ θ ≤ (2 * n) ^ θ :=
              Real.rpow_le_rpow (by positivity) (by linarith) hθ0
          _ = 2 ^ θ * (n : ℝ) ^ θ := Real.mul_rpow (by norm_num) (by positivity)
          _ ≤ 2 * (n : ℝ) ^ θ := by
              gcongr
              calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
                _ = 2 := Real.rpow_one 2
      have hcomb : (n : ℝ) ^ (-(2 * β)) * (n : ℝ) ^ θ ≤ 1 := by
        rw [← Real.rpow_add (by positivity)]
        exact Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith)
      calc |G (n - 1)| * |mertensFunctionReal n|
          ≤ ((n : ℝ) ^ (-(2 * β)) * t ^ (-β)) * (B * ((n : ℝ) + 1) ^ θ) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ ((n : ℝ) ^ (-(2 * β)) * t ^ (-β)) * (B * (2 * (n : ℝ) ^ θ)) := by gcongr
        _ = 2 * B * t ^ (-β) * ((n : ℝ) ^ (-(2 * β)) * (n : ℝ) ^ θ) := by ring
        _ ≤ 2 * B * t ^ (-β) * 1 := by gcongr
        _ = 2 * B * t ^ (-β) := mul_one _
    -- the interior sum
    set q : ℕ := n - 1 with hq
    have hinner : |∑ j ∈ Finset.range q, (G (j + 1) - G j) * mertensFunctionReal (j + 1)| ≤
        B * ∑ j ∈ Finset.range q, ((j : ℝ) + 2) ^ θ * (G (j + 1) - G j) := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hGmono j))]
      have h := hM (j + 1)
      push_cast at h
      rw [show (j : ℝ) + 1 + 1 = (j : ℝ) + 2 by ring] at h
      calc (G (j + 1) - G j) * |mertensFunctionReal (j + 1)|
          ≤ (G (j + 1) - G j) * (B * ((j : ℝ) + 2) ^ θ) := by
            gcongr
            · exact sub_nonneg.mpr (hGmono j)
        _ = B * (((j : ℝ) + 2) ^ θ * (G (j + 1) - G j)) := by ring
    -- second summation by parts
    have hsecond : ∑ j ∈ Finset.range q, ((j : ℝ) + 2) ^ θ * (G (j + 1) - G j) ≤
        2 + Z * t ^ (-β) := by
      rw [sum_range_mul_sub_eq (fun j : ℕ => ((j : ℝ) + 2) ^ θ) G q]
      have h1 : ((q : ℝ) + 2) ^ θ * G q ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (hGle q)
      have h2 : -(((0 : ℕ) : ℝ) + 2) ^ θ * G 0 ≤ 2 := by
        have hG0 := hGabs 0
        push_cast at hG0 ⊢
        have hG0' : |G 0| ≤ 1 := by
          have := abs_kernelH_le_rpow (u := t) ht hβ0 hβ1
          have hu : G 0 = kernelH t := by simp [hG]
          rw [hu, abs_of_nonpos (kernelH_nonpos ht)]
          linarith [neg_one_le_kernelH ht]
        have h2θ : (2 : ℝ) ^ θ ≤ 2 := by
          calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
            _ = 2 := Real.rpow_one 2
        have hp2 : 0 ≤ (2 : ℝ) ^ θ := by positivity
        simp only [zero_add]
        nlinarith [abs_le.mp hG0', hGle 0]
      have h3 : -∑ j ∈ Finset.range q,
          ((((j + 1 : ℕ) : ℝ) + 2) ^ θ - ((j : ℝ) + 2) ^ θ) * G (j + 1) ≤ Z * t ^ (-β) := by
        rw [← Finset.sum_neg_distrib]
        calc ∑ j ∈ Finset.range q,
              -(((((j + 1 : ℕ) : ℝ) + 2) ^ θ - ((j : ℝ) + 2) ^ θ) * G (j + 1))
            ≤ ∑ j ∈ Finset.range q, ((j : ℝ) + 2) ^ p * t ^ (-β) := by
              refine Finset.sum_le_sum fun j _ => ?_
              have hj2 : (1 : ℝ) ≤ (j : ℝ) + 2 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
              have hd := rpow_add_one_sub_rpow_le hj2 hθ0 hθ1
              have hd0 : 0 ≤ ((j : ℝ) + 2 + 1) ^ θ - ((j : ℝ) + 2) ^ θ :=
                sub_nonneg.mpr (Real.rpow_le_rpow (by positivity) (by linarith) hθ0)
              have hGj := hGabs (j + 1)
              push_cast at hGj ⊢
              rw [show (j : ℝ) + 1 + 1 = (j : ℝ) + 2 by ring] at hGj
              rw [show (j : ℝ) + 1 + 2 = (j : ℝ) + 2 + 1 by ring]
              have hGneg : -G (j + 1) ≤ ((j : ℝ) + 2) ^ (-(2 * β)) * t ^ (-β) := by
                linarith [neg_abs_le (G (j + 1)), abs_le.mp hGj]
              calc -((((j : ℝ) + 2 + 1) ^ θ - ((j : ℝ) + 2) ^ θ) * G (j + 1))
                  = (((j : ℝ) + 2 + 1) ^ θ - ((j : ℝ) + 2) ^ θ) * (-G (j + 1)) := by ring
                _ ≤ ((j : ℝ) + 2) ^ (θ - 1) * (((j : ℝ) + 2) ^ (-(2 * β)) * t ^ (-β)) :=
                    mul_le_mul hd hGneg (by linarith [hGle (j + 1)]) (by positivity)
                _ = ((j : ℝ) + 2) ^ p * t ^ (-β) := by
                    rw [← mul_assoc, ← Real.rpow_add (by positivity), hp]
                    ring_nf
          _ = (∑ j ∈ Finset.range q, ((j : ℝ) + 2) ^ p) * t ^ (-β) := by rw [Finset.sum_mul]
          _ ≤ Z * t ^ (-β) := by
              gcongr
              exact hZs.sum_le_tsum _ fun j _ => Real.rpow_nonneg (by positivity) _
      linarith
    rw [hS']
    calc |G (n - 1) * mertensFunctionReal n -
          ∑ j ∈ Finset.range q, (G (j + 1) - G j) * mertensFunctionReal (j + 1)|
        ≤ |G (n - 1) * mertensFunctionReal n| +
            |∑ j ∈ Finset.range q, (G (j + 1) - G j) * mertensFunctionReal (j + 1)| :=
          abs_sub _ _
      _ ≤ 2 * B * t ^ (-β) + B * (2 + Z * t ^ (-β)) := by
          gcongr
          exact hinner.trans (mul_le_mul_of_nonneg_left hsecond hB)
      _ ≤ B * (4 + Z) * t ^ (-β) := by nlinarith
  exact le_of_tendsto hSlim.abs (Eventually.of_forall hbound)

/-- **Forward direction.** If `|M(N)| ≤ B (N+1)^θ` for all `N` with `0 ≤ θ ≤ 1`, then for every
`β ≤ 1` with `θ < 2β` there is `C` with `‖A(t) - c/t‖ ≤ C t^{-β}` on `(0, 1]`. -/
theorem abs_profile_sub_le_of_mertens {θ β B : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθβ : θ < 2 * β) (hβ1 : β ≤ 1) (hB : 0 ≤ B)
    (hM : ∀ n : ℕ, |mertensFunctionReal n| ≤ B * ((n : ℝ) + 1) ^ θ) :
    ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ C * t ^ (-β) :=
  ⟨_, fun t ht => by
    rw [profile_sub_eq_tsum ht.1, Complex.norm_real, Real.norm_eq_abs]
    exact abs_tsum_moebius_kernelH_le hθ0 hθ1 hθβ hβ1 hB hM ht.1 ht.2⟩

/-- **RH gives the `t^{-1/4-ε}` law.** -/
theorem expBound_quarter_of_riemannHypothesis (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ C * t ^ (-(1 / 4 + ε)) := by
  set δ : ℝ := min ε (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hzf : ∀ z : ℂ, 1 / 2 < z.re → riemannZeta z ≠ 0 :=
    riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH
  obtain ⟨B, hB, hMB⟩ := mobiusMertens_subpower_of_zeroFree (Θ := 1 / 2) le_rfl (by norm_num)
    hzf δ hδ0
  have hM : ∀ n : ℕ, |mertensFunctionReal n| ≤ B * ((n : ℝ) + 1) ^ (1 / 2 + δ) := fun n => by
    rw [← norm_mobiusMertensPartialSum_eq_abs_mertensFunctionReal]; exact hMB n
  obtain ⟨C, hC⟩ := abs_profile_sub_le_of_mertens (θ := 1 / 2 + δ) (β := 1 / 4 + δ) (by linarith)
    (by linarith) (by linarith) (by linarith) hB hM
  refine ⟨|C|, fun t ht => ?_⟩
  calc ‖profile t - density / t‖ ≤ C * t ^ (-(1 / 4 + δ)) := hC t ht
    _ ≤ |C| * t ^ (-(1 / 4 + δ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg ht.1.le _)
    _ ≤ |C| * t ^ (-(1 / 4 + ε)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith)) (abs_nonneg C)

/-- **RH ⟺ the exponential squarefree law at `t^{-1/4}`.** -/
theorem riemannHypothesis_iff_squarefree_exponential :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖profile t - density / t‖ ≤ C * t ^ (-(1 / 4 + ε)) :=
  ⟨fun hRH _ hε => expBound_quarter_of_riemannHypothesis hRH hε,
    riemannHypothesis_of_expBound_quarter⟩

end

end RHTower.SquarefreeExponential
