import GaloisForLFunctions.BezoutValuationIncidence.ThirdOrderCrossScaleLawAndTheCubicBernoulliKernel

/-!
# Smooth large-scale rows and the cancellation of both kernels

**The cubic kernel is odd.** `2Ψ_d - Φ_d = f_d(ρ)` with `f_d(ρ) = ρ³/3 - dρ²/2 + d²ρ/6 = (d³/3) B₃(ρ/d)`
satisfies `f_d(d - ρ) = -f_d(ρ)`. Since `j(d - r) + jr ≡ 0 (mod d)`, the residues of `j(d - r)` and `jr`
are reflections of each other. Hence `Σ_{r < d} (2Ψ_d - Φ_d)(jr) = 0` for every `j`, and the cubic kernel
has zero residue mean:

`Σ_{r < d} 𝔅₃(d, r) = 0`.

**Smooth weights.** A periodic sequence with zero period sums has bounded primitive. For weights `y` on
`[0, b)` with `y(0) = y(b) = 0`, one summation by parts gives

`|Σ_n y(n) 𝔅₃(d, n)| ≤ d⁴ Σ_n |y(n) - y(n+1)|`.

For a prime `p` the kernel `𝔅(p, ·) - m_p`, `m_p = π²(p² - 1)/(72p²)`, also has zero period sums. Its
primitive is periodic, and after centring has a bounded primitive in turn. Two summations by parts
give, for weights `x` vanishing at `0, 1, b, b + 1`,

`|Σ_n x(n)(𝔅(p, n) - m_p)| ≤ (p⁴/2) Σ_n |x(n) - 2x(n+1) + x(n+2)|`.

**The smooth-row law.** With the third-order law, every row `c` on primes and every large-scale row `c'`
supported in `[2, N]`, with `x(n) = c'(n)/n²` and `y(n) = c'(n)/n³`, satisfy

`|B + m R' + β H' - (π²/72) S' Σ_p c(p)(p² - 1)/p³|
  ≤ Σ_p |c(p)| p³ (½ Σ_n |Δ²x(n)| + Σ_n |Δy(n)|) + 6 Σ_p |c(p)| p³ Σ_n |c'(n)|/n⁴`.

For a large-scale weight that is smooth at scale `A`, with `Σ|Δ²x| ≲ S₀/A²` and `Σ|Δy| ≲ S₀/A²`, every
error term is `≍ S₀ Σ_p |c(p)| p³/A²`. Against the diagonal this is diagonal quality for `A ≥ P^{4/3}`:
exponent `θ` up to `3/2`, for arbitrary small-scale coefficients. Sharp cutoffs stop at `θ = 4/3` because
of the boundary terms of `𝔅`. One order of smoothness more at the large scale moves the barrier from `4/3`
to `3/2`.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The cubic kernel is odd -/

/-- `f_d(ρ) = ρ³/3 - dρ²/2 + d²ρ/6`. -/
def cubicDiffPoly (d : ℕ) (ρ : ℝ) : ℝ := ρ ^ 3 / 3 - (d : ℝ) * ρ ^ 2 / 2 + (d : ℝ) ^ 2 * ρ / 6

theorem cubicDiffPoly_reflect (d : ℕ) (ρ : ℝ) : cubicDiffPoly d ((d : ℝ) - ρ) = -cubicDiffPoly d ρ := by
  unfold cubicDiffPoly; ring

theorem cubicDiffPoly_zero (d : ℕ) : cubicDiffPoly d 0 = 0 := by unfold cubicDiffPoly; ring

theorem two_mul_cubicPotential_sub_eq_poly {d : ℕ} (hd : 0 < d) (M : ℕ) :
    2 * cubicPotential d M - residuePotential d M = cubicDiffPoly d ((M % d : ℕ) : ℝ) := by
  rw [two_mul_cubicPotential_sub_eq hd]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold cubicDiffPoly
  field_simp
  ring

/-- Reflection: `(2Ψ_d - Φ_d)(j(d - r)) = -(2Ψ_d - Φ_d)(jr)` for `r ≤ d`. -/
theorem cubicDiff_mul_sub {d : ℕ} (hd : 0 < d) (j : ℕ) {r : ℕ} (hr : r ≤ d) :
    2 * cubicPotential d (j * (d - r)) - residuePotential d (j * (d - r)) =
      -(2 * cubicPotential d (j * r) - residuePotential d (j * r)) := by
  rw [two_mul_cubicPotential_sub_eq_poly hd, two_mul_cubicPotential_sub_eq_poly hd]
  set a := (j * (d - r)) % d
  set b := (j * r) % d
  have ha : a < d := Nat.mod_lt _ hd
  have hb : b < d := Nat.mod_lt _ hd
  have hsum : (a + b) % d = 0 := by
    have : j * (d - r) + j * r = j * d := by rw [← mul_add, Nat.sub_add_cancel hr]
    rw [← Nat.add_mod, this, Nat.mul_mod_left]
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hsum
  rcases k with _ | _ | k
  · have h0 : a = 0 ∧ b = 0 := by omega
    rw [h0.1, h0.2]; simp [cubicDiffPoly_zero]
  · have h1 : a = d - b := by omega
    have : (a : ℝ) = (d : ℝ) - b := by rw [h1, Nat.cast_sub hb.le]
    rw [this, cubicDiffPoly_reflect]
  · nlinarith

/-- `Σ_{r < d} (2Ψ_d - Φ_d)(jr) = 0`. -/
theorem sum_range_cubicDiff_mul {d : ℕ} (hd : 0 < d) (j : ℕ) :
    ∑ r ∈ range d, (2 * cubicPotential d (j * r) - residuePotential d (j * r)) = 0 := by
  set F : ℕ → ℝ := fun r => 2 * cubicPotential d (j * r) - residuePotential d (j * r)
  have hF0 : F 0 = 0 := by
    simp only [F, mul_zero]
    rw [two_mul_cubicPotential_sub_eq_poly hd, Nat.zero_mod, Nat.cast_zero, cubicDiffPoly_zero]
  have hsplit : ∑ r ∈ range d, F r = ∑ r ∈ Ico 1 d, F r := by
    rw [← sum_range_add_sum_Ico F (by omega : 1 ≤ d), sum_range_one, hF0, zero_add]
  have hrefl : ∑ r ∈ Ico 1 d, F (d - r) = ∑ r ∈ Ico 1 d, F r := by
    have := sum_Ico_reflect F 1 (by omega : d ≤ d + 1)
    rwa [show d + 1 - d = 1 by omega, show d + 1 - 1 = d by omega] at this
  have hneg : ∑ r ∈ Ico 1 d, F (d - r) = -∑ r ∈ Ico 1 d, F r := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun r hr => cubicDiff_mul_sub hd j (mem_Ico.mp hr).2.le
  show ∑ r ∈ range d, F r = 0
  rw [hsplit]
  linarith

/-- **The cubic kernel has zero residue mean.** `Σ_{r < d} 𝔅₃(d, r) = 0`. -/
theorem sum_range_cubicKernel {d : ℕ} (hd : 0 < d) : ∑ r ∈ range d, cubicKernel d r = 0 := by
  have hsum := hasSum_sum (s := range d) fun r _ => hasSum_cubicKernel hd r
  have hzero : (fun j : ℕ => ∑ r ∈ range d, (2 * cubicPotential d ((j + 1) * r) -
      residuePotential d ((j + 1) * r)) / ((j : ℝ) + 1) ^ 3) = fun _ => 0 := by
    funext j
    rw [← sum_div, sum_range_cubicDiff_mul hd, zero_div]
  rw [hzero] at hsum
  exact hsum.unique hasSum_zero

/-! ## §2. Periodic sequences with zero period sums -/

theorem sum_Ico_eq_sum_range_of_periodic {g : ℕ → ℝ} {d : ℕ} (hg : ∀ n, g (n + d) = g n) (N : ℕ) :
    ∑ n ∈ Ico N (N + d), g n = ∑ n ∈ range d, g n := by
  induction N with
  | zero => rw [zero_add, range_eq_Ico]
  | succ N ih =>
    rcases Nat.eq_zero_or_pos d with h0 | hd
    · subst h0; simp
    have h1 : ∑ n ∈ Ico N (N + d), g n = g N + ∑ n ∈ Ico (N + 1) (N + d), g n := by
      rw [← sum_Ico_consecutive _ (Nat.le_succ N) (by omega : N + 1 ≤ N + d)]
      simp
    have h2 : ∑ n ∈ Ico (N + 1) (N + 1 + d), g n = ∑ n ∈ Ico (N + 1) (N + d), g n + g (N + d) := by
      rw [show N + 1 + d = N + d + 1 by ring, sum_Ico_succ_top (by omega)]
    rw [h2, ← ih, h1, hg N]
    ring

/-- A `d`-periodic sequence with zero period sum and `|g| ≤ B` has interval sums at most `dB`. -/
theorem abs_sum_Ico_le_of_periodic {g : ℕ → ℝ} {d : ℕ} (hd : 0 < d) (hg : ∀ n, g (n + d) = g n)
    (h0 : ∑ n ∈ range d, g n = 0) {B : ℝ} (hB : ∀ n, |g n| ≤ B) (N K : ℕ) :
    |∑ n ∈ Ico N (N + K), g n| ≤ d * B := by
  induction K using Nat.strong_induction_on generalizing N with
  | _ K ih =>
    by_cases hK : K < d
    · calc |∑ n ∈ Ico N (N + K), g n| ≤ ∑ n ∈ Ico N (N + K), |g n| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Ico N (N + K), B := sum_le_sum fun n _ => hB n
        _ = K * B := by rw [sum_const, Nat.card_Ico]; simp
        _ ≤ d * B := by
          have : (K : ℝ) ≤ d := by exact_mod_cast hK.le
          have : 0 ≤ B := (abs_nonneg _).trans (hB 0)
          nlinarith
    · replace hK := not_lt.mp hK
      rw [show N + K = (N + d) + (K - d) by omega,
        ← sum_Ico_consecutive _ (by omega : N ≤ N + d) (by omega : N + d ≤ N + d + (K - d)),
        sum_Ico_eq_sum_range_of_periodic hg N, h0, zero_add]
      exact ih (K - d) (by omega) (N + d)

/-- Summation by parts with vanishing ends: if `x(0) = x(b) = 0` then
`Σ_{n < b} x(n)(X(n+1) - X(n)) = Σ_{n < b} (x(n) - x(n+1)) X(n+1)`. -/
theorem sum_range_mul_sub_eq (x X : ℕ → ℝ) (b : ℕ) (h0 : x 0 = 0) (hb : x b = 0) :
    ∑ n ∈ range b, x n * (X (n + 1) - X n) = ∑ n ∈ range b, (x n - x (n + 1)) * X (n + 1) := by
  have hshift : ∑ n ∈ range b, x n * X n = ∑ n ∈ range b, x (n + 1) * X (n + 1) := by
    have h1 := Finset.sum_range_succ' (fun n => x n * X n) b
    have h2 := Finset.sum_range_succ (fun n => x n * X n) b
    simp only [h0, hb, zero_mul, add_zero] at h1 h2
    rw [← h2, h1]
  rw [show ∑ n ∈ range b, (x n - x (n + 1)) * X (n + 1) =
      ∑ n ∈ range b, x n * X (n + 1) - ∑ n ∈ range b, x (n + 1) * X (n + 1) by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun n _ => by ring, ← hshift, ← sum_sub_distrib]
  exact sum_congr rfl fun n _ => by ring

/-! ## §3. Both kernels against smooth weights -/

theorem cubicKernel_add_period (d n : ℕ) : cubicKernel d (n + d) = cubicKernel d n := by
  rw [cubicKernel_mod, Nat.add_mod_right, ← cubicKernel_mod]

/-- `|Σ_{n < b} y(n) 𝔅₃(d, n)| ≤ d⁴ Σ_{n < b} |y(n) - y(n+1)|` when `y(0) = y(b) = 0`. -/
theorem abs_sum_mul_cubicKernel_le {d : ℕ} (hd : 0 < d) (y : ℕ → ℝ) (b : ℕ) (h0 : y 0 = 0)
    (hb : y b = 0) :
    |∑ n ∈ range b, y n * cubicKernel d n| ≤ (d : ℝ) ^ 4 * ∑ n ∈ range b, |y n - y (n + 1)| := by
  set X : ℕ → ℝ := fun n => ∑ k ∈ range n, cubicKernel d k
  have hX : ∀ n, X (n + 1) - X n = cubicKernel d n := fun n => by
    simp only [X, Finset.sum_range_succ]; ring
  have hXb : ∀ n, |X n| ≤ (d : ℝ) ^ 4 := fun n => by
    have h := abs_sum_Ico_le_of_periodic hd (cubicKernel_add_period d) (sum_range_cubicKernel hd)
      (B := (d : ℝ) ^ 3) (abs_cubicKernel_le hd) 0 n
    rw [zero_add, ← range_eq_Ico] at h
    calc |X n| ≤ d * (d : ℝ) ^ 3 := h
      _ = (d : ℝ) ^ 4 := by ring
  rw [show ∑ n ∈ range b, y n * cubicKernel d n = ∑ n ∈ range b, y n * (X (n + 1) - X n) from
    sum_congr rfl fun n _ => by rw [hX], sum_range_mul_sub_eq y X b h0 hb, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hXb _) (abs_nonneg _)

/-- The residue mean of the quadratic kernel at a prime, `m_p = π²(p² - 1)/(72p²)`. -/
def primeKernelMean (p : ℕ) : ℝ := Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ) ^ 2)

theorem sum_range_bernoulliKernel_sub_mean {p : ℕ} (hp : p.Prime) :
    ∑ r ∈ range p, (bernoulliKernel p r - primeKernelMean p) = 0 := by
  rw [sum_sub_distrib, sum_range_bernoulliKernel_prime hp, sum_const, card_range, nsmul_eq_mul,
    primeKernelMean]
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  ring

theorem abs_bernoulliKernel_sub_mean_le {p : ℕ} (hp : p.Prime) (n : ℕ) :
    |bernoulliKernel p n - primeKernelMean p| ≤ (p : ℝ) ^ 2 / 4 := by
  have h1 := abs_bernoulliKernel_le_sharp hp.two_le n
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hm0 : 0 ≤ primeKernelMean p := by
    unfold primeKernelMean
    have : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    positivity
  have hm : primeKernelMean p ≤ Real.pi ^ 2 / 72 := by
    unfold primeKernelMean
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos, sq_nonneg Real.pi]
  have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  calc |bernoulliKernel p n - primeKernelMean p|
      ≤ |bernoulliKernel p n| + |primeKernelMean p| := abs_sub _ _
    _ ≤ Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 + Real.pi ^ 2 / 72 := by
        rw [abs_of_nonneg hm0]; exact add_le_add h1 hm
    _ = Real.pi ^ 2 * (p : ℝ) ^ 2 / 72 := by ring
    _ ≤ (p : ℝ) ^ 2 / 4 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [sq_nonneg (p : ℝ)]

theorem bernoulliKernel_add_period (d n : ℕ) : bernoulliKernel d (n + d) = bernoulliKernel d n := by
  rw [bernoulliKernel_mod, Nat.add_mod_right, ← bernoulliKernel_mod]

/-- **Two summations by parts at a prime.** If `x(0) = x(1) = x(b) = x(b+1) = 0` then
`|Σ_{n < b} x(n)(𝔅(p, n) - m_p)| ≤ (p⁴/2) Σ_{n < b} |x(n) - 2x(n+1) + x(n+2)|`. -/
theorem abs_sum_mul_bernoulliKernel_sub_mean_le_second_diff {p : ℕ} (hp : p.Prime) (x : ℕ → ℝ)
    (b : ℕ) (h0 : x 0 = 0) (h1 : x 1 = 0) (hb : x b = 0) (hb1 : x (b + 1) = 0) :
    |∑ n ∈ range b, x n * (bernoulliKernel p n - primeKernelMean p)| ≤
      (p : ℝ) ^ 4 / 2 * ∑ n ∈ range b, |x n - 2 * x (n + 1) + x (n + 2)| := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  set D : ℕ → ℝ := fun n => bernoulliKernel p n - primeKernelMean p
  have hDper : ∀ n, D (n + p) = D n := fun n => by simp only [D, bernoulliKernel_add_period]
  have hD0 : ∑ n ∈ range p, D n = 0 := sum_range_bernoulliKernel_sub_mean hp
  set G₁ : ℕ → ℝ := fun n => ∑ k ∈ range n, D k
  have hG₁ : ∀ n, G₁ (n + 1) - G₁ n = D n := fun n => by simp only [G₁, Finset.sum_range_succ]; ring
  have hG₁b : ∀ n, |G₁ n| ≤ (p : ℝ) ^ 3 / 4 := fun n => by
    have h := abs_sum_Ico_le_of_periodic hp0 hDper hD0 (B := (p : ℝ) ^ 2 / 4)
      (abs_bernoulliKernel_sub_mean_le hp) 0 n
    rw [zero_add, ← range_eq_Ico] at h
    calc |G₁ n| ≤ p * ((p : ℝ) ^ 2 / 4) := h
      _ = (p : ℝ) ^ 3 / 4 := by ring
  have hG₁per : ∀ n, G₁ (n + p) = G₁ n := fun n => by
    simp only [G₁]
    rw [← sum_range_add_sum_Ico _ (by omega : n ≤ n + p), sum_Ico_eq_sum_range_of_periodic hDper n,
      hD0, add_zero]
  set μ : ℝ := (∑ r ∈ range p, G₁ (r + 1)) / p
  have hμ : |μ| ≤ (p : ℝ) ^ 3 / 4 := by
    simp only [μ]
    rw [abs_div, abs_of_pos hpR, div_le_iff₀ hpR]
    calc |∑ r ∈ range p, G₁ (r + 1)| ≤ ∑ r ∈ range p, |G₁ (r + 1)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ range p, (p : ℝ) ^ 3 / 4 := sum_le_sum fun r _ => hG₁b _
      _ = (p : ℝ) ^ 3 / 4 * p := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  set D₂ : ℕ → ℝ := fun n => G₁ (n + 1) - μ
  have hD₂per : ∀ n, D₂ (n + p) = D₂ n := fun n => by
    simp only [D₂]; rw [show n + p + 1 = n + 1 + p by ring, hG₁per]
  have hD₂0 : ∑ n ∈ range p, D₂ n = 0 := by
    simp only [D₂, μ]
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    field_simp
    ring
  have hD₂b : ∀ n, |D₂ n| ≤ (p : ℝ) ^ 3 / 2 := fun n => by
    simp only [D₂]
    calc |G₁ (n + 1) - μ| ≤ |G₁ (n + 1)| + |μ| := abs_sub _ _
      _ ≤ (p : ℝ) ^ 3 / 4 + (p : ℝ) ^ 3 / 4 := add_le_add (hG₁b _) hμ
      _ = (p : ℝ) ^ 3 / 2 := by ring
  set G₂ : ℕ → ℝ := fun n => ∑ k ∈ range n, D₂ k
  have hG₂ : ∀ n, G₂ (n + 1) - G₂ n = D₂ n := fun n => by simp only [G₂, Finset.sum_range_succ]; ring
  have hG₂b : ∀ n, |G₂ n| ≤ (p : ℝ) ^ 4 / 2 := fun n => by
    have h := abs_sum_Ico_le_of_periodic hp0 hD₂per hD₂0 hD₂b 0 n
    rw [zero_add, ← range_eq_Ico] at h
    calc |G₂ n| ≤ p * ((p : ℝ) ^ 3 / 2) := h
      _ = (p : ℝ) ^ 4 / 2 := by ring
  set e : ℕ → ℝ := fun n => x n - x (n + 1)
  have he0 : e 0 = 0 := by simp only [e, h0, h1, sub_zero]
  have heb : e b = 0 := by simp only [e, hb, hb1, sub_zero]
  have hfirst : ∑ n ∈ range b, x n * D n = ∑ n ∈ range b, e n * G₁ (n + 1) := by
    rw [show ∑ n ∈ range b, x n * D n = ∑ n ∈ range b, x n * (G₁ (n + 1) - G₁ n) from
      sum_congr rfl fun n _ => by rw [hG₁], sum_range_mul_sub_eq x G₁ b h0 hb]
  have hcenter : ∑ n ∈ range b, e n * G₁ (n + 1) = ∑ n ∈ range b, e n * D₂ n := by
    have htel : ∑ n ∈ range b, e n = 0 := by
      simp only [e]; rw [sum_range_sub' x b, h0, hb, sub_zero]
    simp only [D₂, mul_sub]
    rw [sum_sub_distrib, ← sum_mul, htel, zero_mul, sub_zero]
  have hsecond : ∑ n ∈ range b, e n * D₂ n = ∑ n ∈ range b, (e n - e (n + 1)) * G₂ (n + 1) := by
    rw [show ∑ n ∈ range b, e n * D₂ n = ∑ n ∈ range b, e n * (G₂ (n + 1) - G₂ n) from
      sum_congr rfl fun n _ => by rw [hG₂], sum_range_mul_sub_eq e G₂ b he0 heb]
  show |∑ n ∈ range b, x n * D n| ≤ _
  rw [hfirst, hcenter, hsecond, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
  rw [abs_mul, mul_comm]
  have : e n - e (n + 1) = x n - 2 * x (n + 1) + x (n + 2) := by simp only [e]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (hG₂b _) (abs_nonneg _)

/-! ## §4. The smooth-row law -/

theorem sum_Icc_eq_sum_range_succ (f : ℕ → ℝ) (N : ℕ) (h0 : f 0 = 0) :
    ∑ n ∈ Icc 1 N, f n = ∑ n ∈ range (N + 1), f n := by
  rw [Finset.sum_range_succ', h0, add_zero, show Icc 1 N = Ico 1 (N + 1) by ext; simp,
    sum_Ico_eq_sum_range, show N + 1 - 1 = N by omega]
  exact sum_congr rfl fun k _ => by rw [add_comm]

/-- **The smooth-row law.** For a row `c` on primes and a large-scale row `c'` supported in `[2, N]`,
with `x(n) = c'(n)/n²`, `y(n) = c'(n)/n³`, `S' = Σ_n c'(n)/n²`:
`|B + m R' + β H' - (π²/72) S' Σ_p c(p)(p² - 1)/p³|
  ≤ Σ_p |c(p)| p³ (½ Σ_n |Δ²x(n)| + Σ_n |Δy(n)|) + 6 Σ_p |c(p)| p³ Σ_n |c'(n)|/n⁴`. -/
theorem abs_rowBilinear_add_mean_add_beta_sub_smooth_le (N : ℕ) {c c' : ℕ → ℝ}
    (hc : ∀ d, c d ≠ 0 → d.Prime) (hc' : ∀ n, c' n ≠ 0 → 2 ≤ n ∧ n ≤ N) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' -
        Real.pi ^ 2 / 72 * (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2) *
          ∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3| ≤
      (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) *
          ((∑ n ∈ range (N + 1), |c' n / (n : ℝ) ^ 2 - 2 * (c' (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2) +
              c' (n + 2) / ((n + 2 : ℕ) : ℝ) ^ 2|) / 2 +
            ∑ n ∈ range (N + 1), |c' n / (n : ℝ) ^ 3 - c' (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 3|) +
        6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 := by
  set x : ℕ → ℝ := fun n => c' n / (n : ℝ) ^ 2
  set y : ℕ → ℝ := fun n => c' n / (n : ℝ) ^ 3
  have hzero : ∀ n, n ∉ Icc 2 N → c' n = 0 := fun n hn => by
    by_contra h; exact hn (mem_Icc.mpr (hc' n h))
  have hx0 : x 0 = 0 := by simp [x]
  have hx1 : x 1 = 0 := by simp only [x]; rw [hzero 1 (by simp)]; simp
  have hxb : x (N + 1) = 0 := by simp only [x]; rw [hzero (N + 1) (by simp)]; simp
  have hxb1 : x (N + 1 + 1) = 0 := by simp only [x]; rw [hzero (N + 1 + 1) (by simp)]; simp
  have hy0 : y 0 = 0 := by simp [y]
  have hyb : y (N + 1) = 0 := by simp only [y]; rw [hzero (N + 1) (by simp)]; simp
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_third_order_le N c c'
  set E := rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c'
  set K := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) *
    (bernoulliKernel d n / (n : ℝ) ^ 2 + cubicKernel d n / (n : ℝ) ^ 3)
  set S' := ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2
  set T₂ := ∑ n ∈ range (N + 1), |c' n / (n : ℝ) ^ 2 - 2 * (c' (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2) +
    c' (n + 2) / ((n + 2 : ℕ) : ℝ) ^ 2|
  set T₃ := ∑ n ∈ range (N + 1), |c' n / (n : ℝ) ^ 3 - c' (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 3|
  -- the kernel term, modulus by modulus
  have hK : K = ∑ d ∈ Icc 1 N, c d / d *
      (∑ n ∈ range (N + 1), x n * bernoulliKernel d n + ∑ n ∈ range (N + 1), y n * cubicKernel d n) := by
    simp only [K]
    rw [sum_comm]
    refine sum_congr rfl fun d _ => ?_
    rw [← sum_Icc_eq_sum_range_succ _ N (by simp [x]), ← sum_Icc_eq_sum_range_succ _ N (by simp [y]),
      ← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun n _ => by simp only [x, y]; ring
  have hS' : S' = ∑ n ∈ range (N + 1), x n := sum_Icc_eq_sum_range_succ _ N hx0
  have hmain : |K - Real.pi ^ 2 / 72 * S' * ∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3| ≤
      (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * (T₂ / 2 + T₃) := by
    have e1 : Real.pi ^ 2 / 72 * S' * ∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3 =
        ∑ d ∈ Icc 1 N, Real.pi ^ 2 / 72 * S' * (c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3) :=
      mul_sum _ _ _
    rw [hK, e1, ← sum_sub_distrib, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
    by_cases hcd : c d = 0
    · simp [hcd]
    have hp := hc d hcd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hp.pos
    have h2 := abs_sum_mul_bernoulliKernel_sub_mean_le_second_diff hp x (N + 1) hx0 hx1 hxb hxb1
    have h3 := abs_sum_mul_cubicKernel_le hp.pos y (N + 1) hy0 hyb
    have hsplit : ∑ n ∈ range (N + 1), x n * bernoulliKernel d n =
        ∑ n ∈ range (N + 1), x n * (bernoulliKernel d n - primeKernelMean d) +
          primeKernelMean d * S' := by
      rw [hS', mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun n _ => by ring
    set X₂ := ∑ n ∈ range (N + 1), x n * (bernoulliKernel d n - primeKernelMean d)
    set X₃ := ∑ n ∈ range (N + 1), y n * cubicKernel d n
    have e : c d / d * (∑ n ∈ range (N + 1), x n * bernoulliKernel d n + X₃) -
        Real.pi ^ 2 / 72 * S' * (c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3) = c d / d * (X₂ + X₃) := by
      rw [hsplit, primeKernelMean]
      field_simp
      ring
    rw [e, abs_mul, abs_div, abs_of_pos hd0]
    have hT₂ : T₂ = ∑ n ∈ range (N + 1), |x n - 2 * x (n + 1) + x (n + 2)| := by
      simp only [T₂, x]
    have hT₃ : T₃ = ∑ n ∈ range (N + 1), |y n - y (n + 1)| := by
      simp only [T₃, y]
    calc |c d| / d * |X₂ + X₃| ≤ |c d| / d * ((d : ℝ) ^ 4 / 2 * T₂ + (d : ℝ) ^ 4 * T₃) := by
          refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (by positivity)
          · rw [hT₂]; exact h2
          · rw [hT₃]; exact h3
      _ = |c d| * (d : ℝ) ^ 3 * (T₂ / 2 + T₃) := by field_simp
  calc |E - Real.pi ^ 2 / 72 * S' * ∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3|
      ≤ |E - K| + |K - Real.pi ^ 2 / 72 * S' * ∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3| :=
        abs_sub_le _ _ _
    _ ≤ 6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 +
          (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * (T₂ / 2 + T₃) := add_le_add hlaw hmain
    _ = _ := by ring

end

end GaloisForLFunctions.BezoutValuationIncidence
