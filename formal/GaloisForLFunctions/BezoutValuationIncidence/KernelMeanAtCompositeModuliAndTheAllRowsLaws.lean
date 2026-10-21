import GaloisForLFunctions.BezoutValuationIncidence.DualNormOfTheCrossScaleFunctional

/-!
# The kernel mean at composite moduli and the all-rows laws

**The residue mean.** Summing the residue averages `Σ_{r < d} Φ_d(jr) = d(gcd(j, d)² - 1)/12` against
`1/j²` gives the residue mean of the Bernoulli kernel at every modulus,

`m_d = (1/d) Σ_{r < d} 𝔅(d, r) = Σ_{j ≥ 1} (gcd(j, d)² - 1)/(12 j²)`.

Every term is nonnegative. Since `gcd(j, d)² ≤ Σ_{e | d, e | j} e²` and the multiples of `e` carry
`Σ_{e | j} e²/j² = ζ(2)`,

`0 ≤ m_d ≤ (π²/72)(τ(d) - 1)`,

with equality `m_p = π²(p² - 1)/(72p²)` at primes. The mean is smaller than the maximum
`𝔅(d, 0) = π²(d² - 1)/72` by the factor `≍ τ(d)/d²`.

**The all-rows laws.** A `d`-periodic sequence with zero period sums and `|D| ≤ B` pairs with weights that
vanish at both ends to second order with loss `2d²B Σ|Δ²x|`. With `|𝔅(d, ·) - m_d| ≤ d²/3` and the odd
cubic kernel this gives, for all rows `c` (every modulus) and large-scale rows `c'` supported in
`[2, N]`:

`|B + m R' + β H' - S' Σ_d (c(d)/d) m_d|
  ≤ Σ_d |c(d)| d³ ((2/3) Σ_n |Δ²x(n)| + Σ_n |Δy(n)|) + 6 Σ_d |c(d)| d³ Σ_n |c'(n)|/n⁴`,

and the dual norm over bounded rows on any set `S` of moduli is `Σ_{d ∈ S} |Λ_d(c')|/d` up to the
fourth-order term, where `Λ_d` uses `m_d`. In particular the smooth-row exponent `θ` up to `3/2`, and
the reduction of Type II to single-modulus statistics, hold for Möbius-type small-scale rows on
integers. Their equidistributed part is `S' Σ_d c(d) m_d/d = O(|S'| Σ_d |c(d)| τ(d)/d)`.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The residue mean -/

/-- The residue mean `m_d = (1/d) Σ_{r < d} 𝔅(d, r)`. -/
def kernelMean (d : ℕ) : ℝ := (∑ r ∈ range d, bernoulliKernel d r) / d

theorem hasSum_kernelMean {d : ℕ} (hd : 0 < d) :
    HasSum (fun j : ℕ => (((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 - 1) / (12 * ((j : ℝ) + 1) ^ 2))
      (kernelMean d) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsum := hasSum_sum (s := range d) fun r _ => hasSum_bernoulliKernel hd r
  have hterm : ∀ j : ℕ, ∑ r ∈ range d, residuePotential d ((j + 1) * r) / ((j : ℝ) + 1) ^ 2 =
      d * (((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 - 1) / 12 / ((j : ℝ) + 1) ^ 2 := fun j => by
    rw [← sum_div, sum_range_residuePotential_mul hd]
  simp_rw [hterm] at hsum
  unfold kernelMean
  refine (hsum.div_const (d : ℝ)).congr_fun fun j => ?_
  field_simp

theorem kernelMean_nonneg {d : ℕ} (hd : 0 < d) : 0 ≤ kernelMean d := by
  refine (hasSum_kernelMean hd).nonneg fun j => div_nonneg ?_ (by positivity)
  have h1 : (1 : ℝ) ≤ ((Nat.gcd (j + 1) d : ℕ) : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left d (Nat.succ_pos j)
  nlinarith

/-- The multiples of `e`: `Σ_{e | j} 1/j² = π²/(6e²)`. -/
theorem hasSum_ite_dvd_inv_sq {e : ℕ} (he : 0 < e) :
    HasSum (fun j : ℕ => if e ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0)
      (Real.pi ^ 2 / 6 / (e : ℝ) ^ 2) := by
  set g : ℕ → ℕ := fun k => e * (k + 1) - 1
  have hg1 : ∀ k, g k + 1 = e * (k + 1) := fun k =>
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  have hginj : Function.Injective g := fun a b h => by
    have ha := hg1 a
    have hb := hg1 b
    have : e * (a + 1) = e * (b + 1) := by rw [← ha, ← hb, h]
    have := Nat.eq_of_mul_eq_mul_left he this
    omega
  have hrange : ∀ x ∉ Set.range g, (if e ∣ x + 1 then 1 / ((x : ℝ) + 1) ^ 2 else 0) = 0 := by
    intro x hx
    rw [if_neg]
    rintro ⟨m, hm⟩
    have hm1 : 1 ≤ m := by
      rcases m with _ | m
      · simp at hm
      · omega
    refine hx ⟨m - 1, ?_⟩
    simp only [g]
    rw [Nat.sub_add_cancel hm1, ← hm]
    omega
  have hz : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hcomp : HasSum ((fun x : ℕ => if e ∣ x + 1 then 1 / ((x : ℝ) + 1) ^ 2 else 0) ∘ g)
      (1 / (e : ℝ) ^ 2 * (Real.pi ^ 2 / 6)) := by
    refine (hz.mul_left (1 / (e : ℝ) ^ 2)).congr_fun fun k => ?_
    have hdvd : e ∣ g k + 1 := ⟨k + 1, hg1 k⟩
    have hcast : ((g k : ℕ) : ℝ) + 1 = (e : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast hg1 k
    simp only [Function.comp, if_pos hdvd, hcast]
    field_simp
  have hval : 1 / (e : ℝ) ^ 2 * (Real.pi ^ 2 / 6) = Real.pi ^ 2 / 6 / (e : ℝ) ^ 2 := by ring
  rw [hval] at hcomp
  exact (hginj.hasSum_iff hrange).mp hcomp

/-- **The residue mean is small.** `m_d ≤ (π²/72)(τ(d) - 1)`. -/
theorem kernelMean_le {d : ℕ} (hd : 0 < d) :
    kernelMean d ≤ Real.pi ^ 2 / 72 * ((d.divisors.card : ℝ) - 1) := by
  have hdiv : ∀ e ∈ d.divisors, HasSum
      (fun j : ℕ => (e : ℝ) ^ 2 * (if e ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0))
      ((e : ℝ) ^ 2 * (Real.pi ^ 2 / 6 / (e : ℝ) ^ 2)) := fun e he =>
    (hasSum_ite_dvd_inv_sq (Nat.pos_of_mem_divisors he)).mul_left _
  have hS := hasSum_sum hdiv
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hR := (hS.sub hz).div_const 12
  have hval : (∑ e ∈ d.divisors, (e : ℝ) ^ 2 * (Real.pi ^ 2 / 6 / (e : ℝ) ^ 2) - Real.pi ^ 2 / 6) / 12 =
      Real.pi ^ 2 / 72 * ((d.divisors.card : ℝ) - 1) := by
    have hval' : ∀ e ∈ d.divisors, (e : ℝ) ^ 2 * (Real.pi ^ 2 / 6 / (e : ℝ) ^ 2) = Real.pi ^ 2 / 6 :=
      fun e he => by
        have : (e : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors he).ne'
        field_simp
    rw [sum_congr rfl hval', sum_const, nsmul_eq_mul]
    ring
  rw [hval] at hR
  refine hasSum_le (fun j => ?_) (hasSum_kernelMean hd) hR
  set g := Nat.gcd (j + 1) d
  have hgd : g ∈ d.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hd.ne'⟩
  have hgj : g ∣ j + 1 := Nat.gcd_dvd_left _ _
  have hsingle : ((g : ℕ) : ℝ) ^ 2 * (1 / ((j : ℝ) + 1) ^ 2) ≤
      ∑ e ∈ d.divisors, (e : ℝ) ^ 2 * (if e ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0) := by
    have := single_le_sum (f := fun e : ℕ => (e : ℝ) ^ 2 *
      (if e ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0)) (fun e _ => by positivity) hgd
    simpa [if_pos hgj] using this
  have hj : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := by positivity
  have e1 : (((g : ℕ) : ℝ) ^ 2 - 1) / (12 * ((j : ℝ) + 1) ^ 2) =
      (((g : ℕ) : ℝ) ^ 2 * (1 / ((j : ℝ) + 1) ^ 2) - 1 / ((j : ℝ) + 1) ^ 2) / 12 := by
    field_simp
  rw [e1]
  gcongr

/-! ## §2. Periodic kernels against weights smooth to second order -/

/-- **Two summations by parts.** A `d`-periodic `D` with zero period sum and `|D| ≤ B`, against weights
vanishing at `0, 1, b, b + 1`: `|Σ_{n < b} x(n) D(n)| ≤ 2d²B Σ_{n < b} |x(n) - 2x(n+1) + x(n+2)|`. -/
theorem abs_sum_mul_periodic_le_second_diff {d : ℕ} (hd : 0 < d) {D : ℕ → ℝ}
    (hper : ∀ n, D (n + d) = D n) (hD0 : ∑ n ∈ range d, D n = 0) {B : ℝ} (hB : ∀ n, |D n| ≤ B)
    (x : ℕ → ℝ) (b : ℕ) (h0 : x 0 = 0) (h1 : x 1 = 0) (hb : x b = 0) (hb1 : x (b + 1) = 0) :
    |∑ n ∈ range b, x n * D n| ≤
      2 * (d : ℝ) ^ 2 * B * ∑ n ∈ range b, |x n - 2 * x (n + 1) + x (n + 2)| := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set G₁ : ℕ → ℝ := fun n => ∑ k ∈ range n, D k
  have hG₁ : ∀ n, G₁ (n + 1) - G₁ n = D n := fun n => by
    simp only [G₁, Finset.sum_range_succ]; ring
  have hG₁b : ∀ n, |G₁ n| ≤ d * B := fun n => by
    have h := abs_sum_Ico_le_of_periodic hd hper hD0 hB 0 n
    rwa [zero_add, ← range_eq_Ico] at h
  have hG₁per : ∀ n, G₁ (n + d) = G₁ n := fun n => by
    simp only [G₁]
    rw [← sum_range_add_sum_Ico _ (by omega : n ≤ n + d), sum_Ico_eq_sum_range_of_periodic hper n,
      hD0, add_zero]
  set μ : ℝ := (∑ r ∈ range d, G₁ (r + 1)) / d
  have hμ : |μ| ≤ d * B := by
    simp only [μ]
    rw [abs_div, abs_of_pos hdR, div_le_iff₀ hdR]
    calc |∑ r ∈ range d, G₁ (r + 1)| ≤ ∑ r ∈ range d, |G₁ (r + 1)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ range d, (d : ℝ) * B := sum_le_sum fun r _ => hG₁b _
      _ = d * B * d := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  set D₂ : ℕ → ℝ := fun n => G₁ (n + 1) - μ
  have hD₂per : ∀ n, D₂ (n + d) = D₂ n := fun n => by
    simp only [D₂]; rw [show n + d + 1 = n + 1 + d by ring, hG₁per]
  have hD₂0 : ∑ n ∈ range d, D₂ n = 0 := by
    simp only [D₂, μ]
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    field_simp
    ring
  have hD₂b : ∀ n, |D₂ n| ≤ 2 * d * B := fun n => by
    simp only [D₂]
    calc |G₁ (n + 1) - μ| ≤ |G₁ (n + 1)| + |μ| := abs_sub _ _
      _ ≤ d * B + d * B := add_le_add (hG₁b _) hμ
      _ = 2 * d * B := by ring
  set G₂ : ℕ → ℝ := fun n => ∑ k ∈ range n, D₂ k
  have hG₂ : ∀ n, G₂ (n + 1) - G₂ n = D₂ n := fun n => by
    simp only [G₂, Finset.sum_range_succ]; ring
  have hG₂b : ∀ n, |G₂ n| ≤ 2 * (d : ℝ) ^ 2 * B := fun n => by
    have h := abs_sum_Ico_le_of_periodic hd hD₂per hD₂0 hD₂b 0 n
    rw [zero_add, ← range_eq_Ico] at h
    calc |G₂ n| ≤ d * (2 * d * B) := h
      _ = 2 * (d : ℝ) ^ 2 * B := by ring
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
  rw [hfirst, hcenter, hsecond, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
  rw [abs_mul, mul_comm]
  have : e n - e (n + 1) = x n - 2 * x (n + 1) + x (n + 2) := by simp only [e]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (hG₂b _) (abs_nonneg _)

/-! ## §3. The centred kernel at every modulus -/

theorem bernoulliKernel_one (n : ℕ) : bernoulliKernel 1 n = 0 := by
  simp [bernoulliKernel, residuePotential, Nat.mod_one]

theorem kernelMean_le_max {d : ℕ} (hd : 2 ≤ d) :
    kernelMean d ≤ Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold kernelMean
  rw [div_le_iff₀ hdR]
  calc ∑ r ∈ range d, bernoulliKernel d r ≤ ∑ _r ∈ range d, Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 :=
        sum_le_sum fun r _ => (le_abs_self _).trans (abs_bernoulliKernel_le_sharp hd r)
    _ = Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 * d := by rw [sum_const, card_range, nsmul_eq_mul]; ring

theorem abs_bernoulliKernel_sub_kernelMean_le {d : ℕ} (hd : 0 < d) (n : ℕ) :
    |bernoulliKernel d n - kernelMean d| ≤ (d : ℝ) ^ 2 / 3 := by
  rcases Nat.lt_or_ge d 2 with h1 | h2
  · have hd1 : d = 1 := by omega
    subst hd1
    simp [kernelMean, bernoulliKernel_one]
  · have hb := abs_bernoulliKernel_le_sharp h2 n
    have hm0 := kernelMean_nonneg hd
    have hm := kernelMean_le_max h2
    have hpi : Real.pi ^ 2 < 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hd1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast h2
      nlinarith
    calc |bernoulliKernel d n - kernelMean d| ≤ |bernoulliKernel d n| + |kernelMean d| := abs_sub _ _
      _ ≤ Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 + Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 := by
          rw [abs_of_nonneg hm0]; exact add_le_add hb hm
      _ ≤ (d : ℝ) ^ 2 / 3 := by nlinarith

theorem sum_range_bernoulliKernel_sub_kernelMean {d : ℕ} (hd : 0 < d) :
    ∑ r ∈ range d, (bernoulliKernel d r - kernelMean d) = 0 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, kernelMean]
  field_simp
  ring

/-! ## §4. The all-rows smooth law -/

/-- **The smooth-row law at every modulus.** For every row `c` and every large-scale row `c'`
supported in `[2, N]`, with `x(n) = c'(n)/n²`, `y(n) = c'(n)/n³`:
`|B + m R' + β H' - S' Σ_d (c(d)/d) m_d|
  ≤ Σ_d |c(d)| d³ ((2/3) Σ_n |Δ²x(n)| + Σ_n |Δy(n)|) + 6 Σ_d |c(d)| d³ Σ_n |c'(n)|/n⁴`. -/
theorem abs_rowBilinear_add_mean_add_beta_sub_smooth_all_le (N : ℕ) {c c' : ℕ → ℝ}
    (hc' : ∀ n, c' n ≠ 0 → 2 ≤ n ∧ n ≤ N) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' -
        (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, c d * kernelMean d / d| ≤
      (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) *
          (2 / 3 * ∑ n ∈ range (N + 1), |c' n / (n : ℝ) ^ 2 -
              2 * (c' (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2) + c' (n + 2) / ((n + 2 : ℕ) : ℝ) ^ 2| +
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
  have hK : K = ∑ d ∈ Icc 1 N, c d / d *
      (∑ n ∈ range (N + 1), x n * bernoulliKernel d n + ∑ n ∈ range (N + 1), y n * cubicKernel d n) := by
    simp only [K]
    rw [sum_comm]
    refine sum_congr rfl fun d _ => ?_
    rw [← sum_Icc_eq_sum_range_succ _ N (by simp [x]), ← sum_Icc_eq_sum_range_succ _ N (by simp [y]),
      ← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun n _ => by simp only [x, y]; ring
  have hS' : S' = ∑ n ∈ range (N + 1), x n := sum_Icc_eq_sum_range_succ _ N hx0
  have hmain : |K - S' * ∑ d ∈ Icc 1 N, c d * kernelMean d / d| ≤
      (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * (2 / 3 * T₂ + T₃) := by
    have e1 : S' * ∑ d ∈ Icc 1 N, c d * kernelMean d / d =
        ∑ d ∈ Icc 1 N, S' * (c d * kernelMean d / d) := mul_sum _ _ _
    rw [hK, e1, ← sum_sub_distrib, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have h2 := abs_sum_mul_periodic_le_second_diff hd0 (D := fun n => bernoulliKernel d n - kernelMean d)
      (fun n => by simp only [bernoulliKernel_add_period]) (sum_range_bernoulliKernel_sub_kernelMean hd0)
      (abs_bernoulliKernel_sub_kernelMean_le hd0) x (N + 1) hx0 hx1 hxb hxb1
    have h3 := abs_sum_mul_cubicKernel_le hd0 y (N + 1) hy0 hyb
    have hsplit : ∑ n ∈ range (N + 1), x n * bernoulliKernel d n =
        ∑ n ∈ range (N + 1), x n * (bernoulliKernel d n - kernelMean d) + kernelMean d * S' := by
      rw [hS', mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun n _ => by ring
    set X₂ := ∑ n ∈ range (N + 1), x n * (bernoulliKernel d n - kernelMean d)
    set X₃ := ∑ n ∈ range (N + 1), y n * cubicKernel d n
    have e : c d / d * (∑ n ∈ range (N + 1), x n * bernoulliKernel d n + X₃) -
        S' * (c d * kernelMean d / d) = c d / d * (X₂ + X₃) := by
      rw [hsplit]; ring
    rw [e, abs_mul, abs_div, abs_of_pos hdR]
    have hT₂ : T₂ = ∑ n ∈ range (N + 1), |x n - 2 * x (n + 1) + x (n + 2)| := by simp only [T₂, x]
    have hT₃ : T₃ = ∑ n ∈ range (N + 1), |y n - y (n + 1)| := by simp only [T₃, y]
    calc |c d| / d * |X₂ + X₃|
        ≤ |c d| / d * (2 * (d : ℝ) ^ 2 * ((d : ℝ) ^ 2 / 3) * T₂ + (d : ℝ) ^ 4 * T₃) := by
          refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (by positivity)
          · rw [hT₂]; exact h2
          · rw [hT₃]; exact h3
      _ = |c d| * (d : ℝ) ^ 3 * (2 / 3 * T₂ + T₃) := by field_simp
  calc |E - S' * ∑ d ∈ Icc 1 N, c d * kernelMean d / d|
      ≤ |E - K| + |K - S' * ∑ d ∈ Icc 1 N, c d * kernelMean d / d| := abs_sub_le _ _ _
    _ ≤ 6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 +
          (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * (2 / 3 * T₂ + T₃) := add_le_add hlaw hmain
    _ = _ := by ring

/-! ## §5. The all-rows dual norm -/

/-- The kernel statistic at any modulus, `Λ_d(c') = Σ_n (c'(n)/n²)(𝔅(d, n) - m_d) + Σ_n (c'(n)/n³) 𝔅₃(d, n)`. -/
def kernelStatisticAll (N : ℕ) (c' : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d) +
    c' n / (n : ℝ) ^ 3 * cubicKernel d n)

/-- The equidistributed main term `S' Σ_d (c(d)/d) m_d`. -/
def kernelMeanMain (N : ℕ) (c c' : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, c d * kernelMean d / d

/-- **The cross-scale form through the kernel statistics, every row.**
`|B + m R' + β H' - S' Σ_d (c(d)/d) m_d - Σ_d (c(d)/d) Λ_d(c')| ≤ 6 Σ_d |c(d)| d³ Σ_n |c'(n)|/n⁴`. -/
theorem abs_rowBilinear_sub_kernelStatisticAll_le (N : ℕ) (c c' : ℕ → ℝ) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c' -
        ∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d| ≤
      6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 := by
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_third_order_le N c c'
  set S' := ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2
  have hK : ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) *
      (bernoulliKernel d n / (n : ℝ) ^ 2 + cubicKernel d n / (n : ℝ) ^ 3) =
      kernelMeanMain N c c' + ∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d := by
    have e1 : kernelMeanMain N c c' = ∑ d ∈ Icc 1 N, S' * (c d * kernelMean d / d) := by
      rw [kernelMeanMain]; exact mul_sum _ _ _
    rw [sum_comm, e1, ← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    have hsplit : ∑ n ∈ Icc 1 N, c' n * (c d / d) *
        (bernoulliKernel d n / (n : ℝ) ^ 2 + cubicKernel d n / (n : ℝ) ^ 3) =
        c d / d * (kernelStatisticAll N c' d + kernelMean d * S') := by
      rw [kernelStatisticAll, show kernelMean d * S' =
          ∑ n ∈ Icc 1 N, kernelMean d * (c' n / (n : ℝ) ^ 2) from mul_sum _ _ _,
        ← sum_add_distrib, mul_sum]
      exact sum_congr rfl fun n _ => by ring
    rw [hsplit]
    ring
  rw [hK] at hlaw
  calc |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c' -
        ∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d|
      = |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
          rowBeta N c * finiteHarmonicSum N c' -
          (kernelMeanMain N c c' + ∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d)| := by
        ring_nf
    _ ≤ _ := hlaw

/-- **The dual norm is attained, every modulus.** For a set `S ⊆ [1, N]` of moduli there is a row
`c` with `|c| ≤ 1`, supported on `S`, with
`B + m R' + β H' - main(c) ≥ Σ_{d ∈ S} |Λ_d(c')|/d - 6 (Σ_{d ∈ S} d³) Σ_n |c'(n)|/n⁴`. -/
theorem exists_rowBilinear_sub_kernelMeanMain_ge (N : ℕ) {S : Finset ℕ} (hS : S ⊆ Icc 1 N)
    (c' : ℕ → ℝ) :
    ∃ c : ℕ → ℝ, (∀ d, |c d| ≤ 1) ∧ (∀ d, c d ≠ 0 → d ∈ S) ∧
      ∑ d ∈ S, |kernelStatisticAll N c' d| / d -
          6 * (∑ d ∈ S, (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 ≤
        rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
          rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c' := by
  classical
  set c : ℕ → ℝ := fun d => if d ∈ S then (if 0 ≤ kernelStatisticAll N c' d then 1 else -1) else 0
  have hcabs : ∀ d, |c d| = if d ∈ S then 1 else 0 := fun d => by
    simp only [c]; split_ifs <;> simp
  have hsupp : ∀ d, c d ≠ 0 → d ∈ S := fun d h => by
    by_contra hd; exact h (by simp [c, hd])
  refine ⟨c, fun d => by rw [hcabs]; split_ifs <;> norm_num, hsupp, ?_⟩
  have h := abs_rowBilinear_sub_kernelStatisticAll_le N c c'
  have hstat : ∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d =
      ∑ d ∈ S, |kernelStatisticAll N c' d| / d := by
    rw [← sum_subset hS fun d _ hd => by simp [c, hd]]
    refine sum_congr rfl fun d hd => ?_
    simp only [c, if_pos hd]
    split_ifs with h0
    · rw [abs_of_nonneg h0]; ring
    · rw [abs_of_neg (not_le.mp h0)]; ring
  have hcube : ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3 = ∑ d ∈ S, (d : ℝ) ^ 3 := by
    rw [← sum_subset hS fun d _ hd => by rw [hcabs, if_neg hd, zero_mul]]
    exact sum_congr rfl fun d hd => by rw [hcabs, if_pos hd, one_mul]
  rw [hstat, hcube] at h
  have := (abs_le.mp h).1
  linarith

/-- **The two-sided bound, every modulus.** For every row `c` with `|c| ≤ 1` supported on `S ⊆ [1, N]`,
`|B + m R' + β H' - main(c)| ≤ Σ_{d ∈ S} |Λ_d(c')|/d + 6 (Σ_{d ∈ S} d³) Σ_n |c'(n)|/n⁴`. -/
theorem abs_rowBilinear_sub_kernelMeanMain_le_dual (N : ℕ) {S : Finset ℕ} (hS : S ⊆ Icc 1 N)
    {c : ℕ → ℝ} (c' : ℕ → ℝ) (hc1 : ∀ d, |c d| ≤ 1) (hsupp : ∀ d, c d ≠ 0 → d ∈ S) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c'| ≤
      ∑ d ∈ S, |kernelStatisticAll N c' d| / d +
        6 * (∑ d ∈ S, (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 := by
  have h := abs_rowBilinear_sub_kernelStatisticAll_le N c c'
  have hvan : ∀ d ∈ Icc 1 N, d ∉ S → c d = 0 := fun d _ hd => by
    by_contra h; exact hd (hsupp d h)
  have hstat : |∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d| ≤
      ∑ d ∈ S, |kernelStatisticAll N c' d| / d := by
    rw [← sum_subset hS fun d hd hdS => by rw [hvan d hd hdS]; simp]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    have hdR : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp (hS hd)).1
    rw [abs_mul, abs_div, abs_of_pos hdR]
    calc |c d| / d * |kernelStatisticAll N c' d| ≤ 1 / d * |kernelStatisticAll N c' d| := by
          gcongr; exact hc1 d
      _ = |kernelStatisticAll N c' d| / d := by ring
  have hcube : ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3 ≤ ∑ d ∈ S, (d : ℝ) ^ 3 := by
    rw [← sum_subset hS fun d hd hdS => by rw [hvan d hd hdS]; simp]
    exact sum_le_sum fun d _ => by
      have := hc1 d
      have : (0 : ℝ) ≤ (d : ℝ) ^ 3 := by positivity
      nlinarith [abs_nonneg (c d)]
  have hS4 : 0 ≤ ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 := sum_nonneg fun n _ => by positivity
  have h2 : |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c' -
        ∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d| ≤
      6 * (∑ d ∈ S, (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 :=
    h.trans (by gcongr)
  have key := abs_sub_abs_le_abs_sub (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c')
    (∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d)
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
