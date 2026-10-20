import GaloisForLFunctions.BezoutValuationIncidence.UniformCofinalMobiusPrefixDiscrepancy
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CenteredSquareCompletionAndMultiBandResidueCancellation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.BuchstabFermiCovarianceAndQuotientChainBridge

/-!
# The Buchstab slope law and dissipation at prime horizons

Dilating a sieve by `m` counts each divisor `d` once per multiple of `d / gcd(d, m)`:
`Σ_{j ≤ B} s_{N,c}(m j) = Σ_{d ≤ N} c(d) ⌊B gcd(d,m)/d⌋`. With the Buchstab step this gives
the exact horizon step of the Möbius `L²` prefix energy at every horizon `m = n + 1`:

`E_m(M) - E_{m-1}(M) = μ(m)² B + 2 μ(m) Σ_{d<m} μ(d) ⌊B gcd(d,m)/d⌋`, `B = ⌊M/m⌋`.

At a squarefree horizon the step is `B` times the **Buchstab slope**
`λ(m) = 1 + 2 μ(m) Σ_{d<m} μ(d) gcd(d,m)/d`, up to an error at most `2(m-1)` independent of `M`.
At a prime the slope is `1 - 2 m(p-1)` with `m(x) = Σ_{d≤x} μ(d)/d`. Composite horizons can
have negative slope: at `m = 6` the step is exactly `-B - 2⌊B/5⌋` for every prefix.

The half-band criterion `|S₂| ≤ (B-2)/2` for a dissipative downward step is therefore, at a
prime horizon, the Möbius-mean bound `Σ_{d<p} μ(d)⌊B/d⌋ ≤ B/2`. The prime number theorem
(`m(x) → 0` and `M(x) = o(x)`) gives it for every ratio `B ≥ 2` at all large primes: every
large prime horizon step increases the prefix energy, at every trans-horizon prefix.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Dilated sieve sums -/

/-- `d ∣ m j` exactly when `d / gcd(d, m)` divides `j`. -/
theorem dvd_mul_iff_div_gcd_dvd {d m : ℕ} (hd : 0 < d) (j : ℕ) :
    d ∣ m * j ↔ d / Nat.gcd d m ∣ j := by
  have hg : 0 < Nat.gcd d m := Nat.gcd_pos_of_pos_left m hd
  have hcop : Nat.Coprime (d / Nat.gcd d m) (m / Nat.gcd d m) :=
    Nat.coprime_div_gcd_div_gcd hg
  set g := Nat.gcd d m
  have hd' : g * (d / g) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)
  have hm' : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_right d m)
  have key : g * (d / g) ∣ g * ((m / g) * j) ↔ d ∣ m * j := by
    rw [hd', ← mul_assoc, hm']
  rw [← key]
  constructor
  · intro h
    exact hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hg h)
  · intro h
    exact Nat.mul_dvd_mul_left g (Dvd.dvd.mul_left h _)

/-- **Dilation formula.** `Σ_{j ≤ B} s_{N,c}(m j) = Σ_{d ≤ N} c(d) ⌊B gcd(d,m)/d⌋`. -/
theorem sum_sieveSeq_mul_eq_sum_floor_gcd (N m B : ℕ) (c : ℕ → ℝ) :
    (∑ j ∈ Icc 1 B, sieveSeq N c (m * j)) =
      ∑ d ∈ Icc 1 N, c d * ((B / (d / Nat.gcd d m) : ℕ) : ℝ) := by
  unfold sieveSeq
  rw [Finset.sum_comm' (t' := Icc 1 N) (s' := fun d => (Icc 1 B).filter (fun j => d ∣ m * j))]
  · apply sum_congr rfl
    intro d hd
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    rw [sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    have hfilt : (Icc 1 B).filter (fun j => d ∣ m * j) =
        (Icc 1 B).filter (fun j => d / Nat.gcd d m ∣ j) :=
      filter_congr fun j _ => dvd_mul_iff_div_gcd_dvd hd0 j
    rw [hfilt, BezoutValuationIncidence.card_filter_dvd_Icc_eq_div]
  · intro j d
    simp only [mem_filter, mem_Icc]
    tauto

/-! ### The exact horizon step and the Buchstab slope -/

/-- **Exact horizon step.** For every horizon `n + 1` and prefix `M`, with `B = ⌊M/(n+1)⌋`,
`E_{n+1}(M) - E_n(M) = μ(n+1)² B + 2 μ(n+1) Σ_{d≤n} μ(d) ⌊B gcd(d,n+1)/d⌋`. -/
theorem sieveL2PrefixEnergy_moebius_horizon_step_eq (n M : ℕ) :
    sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal =
      moebiusReal (n + 1) ^ 2 * ((M / (n + 1) : ℕ) : ℝ) +
        2 * moebiusReal (n + 1) * ∑ d ∈ Icc 1 n,
          moebiusReal d * ((M / (n + 1) / (d / Nat.gcd d (n + 1)) : ℕ) : ℝ) := by
  rw [sieveL2PrefixEnergy_succ_horizon_sub_eq, sum_sieveSeq_mul_eq_sum_floor_gcd]

/-- The Buchstab slope `1 + 2 μ(m) Σ_{d<m} μ(d) gcd(d,m)/d` of the horizon `m`. -/
def buchstabSlope (m : ℕ) : ℝ :=
  1 + 2 * moebiusReal m * ∑ d ∈ Icc 1 (m - 1),
    moebiusReal d * ((Nat.gcd d m : ℕ) : ℝ) / (d : ℝ)

private theorem floor_div_gcd_bounds {d m : ℕ} (hd : 0 < d) (B : ℕ) :
    ((B / (d / Nat.gcd d m) : ℕ) : ℝ) ≤ (B : ℝ) * (Nat.gcd d m : ℝ) / d ∧
      (B : ℝ) * (Nat.gcd d m : ℝ) / d - 1 < ((B / (d / Nat.gcd d m) : ℕ) : ℝ) := by
  have hg : 0 < Nat.gcd d m := Nat.gcd_pos_of_pos_left m hd
  have hdg : 0 < d / Nat.gcd d m := Nat.div_pos (Nat.gcd_le_left m hd) hg
  have he : (d : ℝ) = (d / Nat.gcd d m : ℕ) * (Nat.gcd d m : ℝ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left d m)]
  have hq : (B : ℝ) * (Nat.gcd d m : ℝ) / d = (B : ℝ) / (d / Nat.gcd d m : ℕ) := by
    rw [he]; field_simp
  rw [hq]
  have h1 := Nat.floor_div_eq_div (K := ℝ) B (d / Nat.gcd d m)
  constructor
  · rw [← h1]; exact Nat.floor_le (by positivity)
  · rw [← h1]; exact Nat.sub_one_lt_floor _

/-- **Buchstab slope law.** At every squarefree horizon `m = n + 1`, the horizon step differs
from `B · λ(m)` by at most `2n`, uniformly in the prefix. -/
theorem abs_horizon_step_sub_slope_le {n : ℕ} (hsq : Squarefree (n + 1)) (M : ℕ) :
    |sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal -
      ((M / (n + 1) : ℕ) : ℝ) * buchstabSlope (n + 1)| ≤ 2 * n := by
  rw [sieveL2PrefixEnergy_moebius_horizon_step_eq]
  set B : ℕ := M / (n + 1)
  have hμ : moebiusReal (n + 1) ^ 2 = 1 := by
    unfold moebiusReal
    rw [moebius_apply_of_squarefree hsq]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have habs : |moebiusReal (n + 1)| = 1 := by
    have := sq_abs (moebiusReal (n + 1))
    rw [hμ] at this
    nlinarith [abs_nonneg (moebiusReal (n + 1))]
  have hdiff : |(∑ d ∈ Icc 1 n, moebiusReal d * ((B / (d / Nat.gcd d (n + 1)) : ℕ) : ℝ)) -
      (B : ℝ) * ∑ d ∈ Icc 1 n, moebiusReal d * ((Nat.gcd d (n + 1) : ℕ) : ℝ) / (d : ℝ)| ≤ n := by
    rw [mul_sum, ← sum_sub_distrib]
    calc _ ≤ ∑ d ∈ Icc 1 n, |moebiusReal d * ((B / (d / Nat.gcd d (n + 1)) : ℕ) : ℝ) -
          (B : ℝ) * (moebiusReal d * ((Nat.gcd d (n + 1) : ℕ) : ℝ) / (d : ℝ))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Icc 1 n, (1 : ℝ) := by
          apply sum_le_sum
          intro d hd
          have hd0 : 0 < d := (mem_Icc.mp hd).1
          obtain ⟨hlo, hhi⟩ := floor_div_gcd_bounds (m := n + 1) hd0 B
          have hμd : |moebiusReal d| ≤ 1 := by
            unfold moebiusReal; exact_mod_cast abs_moebius_le_one
          have e : moebiusReal d * ((B / (d / Nat.gcd d (n + 1)) : ℕ) : ℝ) -
              (B : ℝ) * (moebiusReal d * ((Nat.gcd d (n + 1) : ℕ) : ℝ) / (d : ℝ)) =
              moebiusReal d * (((B / (d / Nat.gcd d (n + 1)) : ℕ) : ℝ) -
                (B : ℝ) * (Nat.gcd d (n + 1) : ℝ) / d) := by ring
          rw [e, abs_mul]
          have : |((B / (d / Nat.gcd d (n + 1)) : ℕ) : ℝ) -
              (B : ℝ) * (Nat.gcd d (n + 1) : ℝ) / d| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith
          nlinarith [abs_nonneg (moebiusReal d), abs_nonneg (((B / (d / Nat.gcd d (n + 1)) : ℕ) :
            ℝ) - (B : ℝ) * (Nat.gcd d (n + 1) : ℝ) / d)]
      _ = n := by simp
  unfold buchstabSlope
  rw [show n + 1 - 1 = n by omega, hμ, one_mul]
  have e : (B : ℝ) + 2 * moebiusReal (n + 1) *
      (∑ d ∈ Icc 1 n, moebiusReal d * ((B / (d / Nat.gcd d (n + 1)) : ℕ) : ℝ)) -
      (B : ℝ) * (1 + 2 * moebiusReal (n + 1) *
        ∑ d ∈ Icc 1 n, moebiusReal d * ((Nat.gcd d (n + 1) : ℕ) : ℝ) / (d : ℝ)) =
      2 * moebiusReal (n + 1) *
        ((∑ d ∈ Icc 1 n, moebiusReal d * ((B / (d / Nat.gcd d (n + 1)) : ℕ) : ℝ)) -
          (B : ℝ) * ∑ d ∈ Icc 1 n, moebiusReal d * ((Nat.gcd d (n + 1) : ℕ) : ℝ) / (d : ℝ)) := by
    ring
  rw [e, abs_mul, abs_mul, habs]
  norm_num
  linarith

/-- At a prime horizon the Buchstab slope is `1 - 2 m(p-1)`. -/
theorem buchstabSlope_prime {p : ℕ} (hp : p.Prime) :
    buchstabSlope p = 1 - 2 * finiteHarmonicSum (p - 1) moebiusReal := by
  unfold buchstabSlope finiteHarmonicSum
  have hμ : moebiusReal p = -1 := by
    unfold moebiusReal; rw [moebius_apply_prime hp]; norm_num
  rw [hμ]
  have hsum : (∑ d ∈ Icc 1 (p - 1), moebiusReal d * ((Nat.gcd d p : ℕ) : ℝ) / (d : ℝ)) =
      ∑ d ∈ Icc 1 (p - 1), moebiusReal d / (d : ℝ) := by
    apply sum_congr rfl
    intro d hd
    obtain ⟨h1, h2⟩ := mem_Icc.mp hd
    have hcop : Nat.gcd d p = 1 := by
      have : ¬ p ∣ d := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr this)
    rw [hcop]; simp
  rw [hsum]; ring

/-! ### A composite horizon with negative slope -/

/-- At horizon `6` the step is exactly `-B - 2⌊B/5⌋`: adding `d = 6` lowers the prefix energy
at every trans-horizon prefix. -/
theorem sieveL2PrefixEnergy_moebius_six_step (M : ℕ) :
    sieveL2PrefixEnergy 6 M moebiusReal - sieveL2PrefixEnergy 5 M moebiusReal =
      -((M / 6 : ℕ) : ℝ) - 2 * ((M / 6 / 5 : ℕ) : ℝ) := by
  have h := sieveL2PrefixEnergy_moebius_horizon_step_eq 5 M
  simp only [show (5 : ℕ) + 1 = 6 by rfl] at h
  rw [h]
  have hμ6 : moebiusReal 6 = 1 := by
    unfold moebiusReal
    rw [show (6 : ℕ) = 2 * 3 by rfl, isMultiplicative_moebius.map_mul_of_coprime (by decide),
      moebius_apply_prime Nat.prime_two, moebius_apply_prime Nat.prime_three]
    norm_num
  have hμ1 : moebiusReal 1 = 1 := by unfold moebiusReal; simp
  have hμ2 : moebiusReal 2 = -1 := by unfold moebiusReal; rw [moebius_apply_prime Nat.prime_two]; norm_num
  have hμ3 : moebiusReal 3 = -1 := by
    unfold moebiusReal; rw [moebius_apply_prime Nat.prime_three]; norm_num
  have hμ4 : moebiusReal 4 = 0 :=
    moebiusReal_eq_zero_of_not_squarefree 4 (by decide)
  have hμ5 : moebiusReal 5 = -1 := by
    unfold moebiusReal; rw [moebius_apply_prime (by norm_num : Nat.Prime 5)]; norm_num
  rw [hμ6, show Icc 1 5 = {1, 2, 3, 4, 5} by decide]
  norm_num
  rw [hμ1, hμ2, hμ3, hμ4, hμ5]
  ring

/-! ### Dissipation at all large prime horizons -/

/-- At a prime horizon the exact step is `B - 2 Σ_{d<p} μ(d) ⌊B/d⌋`. -/
theorem sieveL2PrefixEnergy_moebius_prime_step_eq {p : ℕ} (hp : p.Prime) (M : ℕ) :
    sieveL2PrefixEnergy p M moebiusReal - sieveL2PrefixEnergy (p - 1) M moebiusReal =
      ((M / p : ℕ) : ℝ) - 2 * ∑ d ∈ Icc 1 (p - 1), moebiusReal d * ((M / p / d : ℕ) : ℝ) := by
  have h := sieveL2PrefixEnergy_moebius_horizon_step_eq (p - 1) M
  rw [Nat.sub_add_cancel hp.one_lt.le] at h
  rw [h]
  have hμ : moebiusReal p = -1 := by
    unfold moebiusReal; rw [moebius_apply_prime hp]; norm_num
  rw [hμ]
  have hsum : (∑ d ∈ Icc 1 (p - 1), moebiusReal d * ((M / p / (d / Nat.gcd d p) : ℕ) : ℝ)) =
      ∑ d ∈ Icc 1 (p - 1), moebiusReal d * ((M / p / d : ℕ) : ℝ) := by
    apply sum_congr rfl
    intro d hd
    obtain ⟨h1, h2⟩ := mem_Icc.mp hd
    have hcop : Nat.gcd d p = 1 := by
      have : ¬ p ∣ d := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr this)
    rw [hcop, Nat.div_one]
  rw [hsum]
  ring

/-- The Möbius floor sum below the prefix is one: `Σ_{d ≤ B} μ(d) ⌊B/d⌋ = 1` for `B ≥ 1`. -/
private theorem sum_moebius_floor_eq_one {B : ℕ} (hB : 1 ≤ B) :
    (∑ d ∈ Icc 1 B, moebiusReal d * ((B / d : ℕ) : ℝ)) = 1 := by
  have h := sum_sieveSeq_mul_eq_sum_floor_gcd B 1 B moebiusReal
  simp only [one_mul, Nat.gcd_one_right, Nat.div_one] at h
  rw [← h, sum_eq_single_of_mem 1 (mem_Icc.mpr ⟨le_rfl, hB⟩)]
  · rw [sieveSeq_moebiusReal_eq_ite_of_le le_rfl hB, if_pos rfl]
  · intro j hj hj1
    obtain ⟨h1, h2⟩ := mem_Icc.mp hj
    rw [sieveSeq_moebiusReal_eq_ite_of_le h1 h2, if_neg hj1]

/-- Splitting the complete floor identity at `p`: the head sum is one minus the tail. -/
private theorem floor_head_eq_one_sub_tail {p B : ℕ} (hp : 1 ≤ p) (hpB : p ≤ B) :
    (∑ d ∈ Icc 1 (p - 1), moebiusReal d * ((B / d : ℕ) : ℝ)) =
      1 - ∑ d ∈ Icc p B, moebiusReal d * ((B / d : ℕ) : ℝ) := by
  have h := sum_moebius_floor_eq_one (show 1 ≤ B by omega)
  have hsplit : Icc 1 B = Icc 1 (p - 1) ∪ Icc p B := by
    ext d; simp only [mem_Icc, mem_union]; omega
  have hdisj : Disjoint (Icc 1 (p - 1)) (Icc p B) := by
    rw [disjoint_left]; intro d h1 h2; simp only [mem_Icc] at h1 h2; omega
  rw [hsplit, sum_union hdisj] at h
  linarith

/-- On the quadratic window the head sum is one. -/
private theorem floor_head_eq_one_of_lt {p B : ℕ} (hB : 1 ≤ B) (hBp : B < p) :
    (∑ d ∈ Icc 1 (p - 1), moebiusReal d * ((B / d : ℕ) : ℝ)) = 1 := by
  have h := sum_moebius_floor_eq_one hB
  rw [← h]
  have hsub : Icc 1 B ⊆ Icc 1 (p - 1) := by
    intro d hd; simp only [mem_Icc] at hd ⊢; omega
  rw [← sum_subset hsub]
  intro d hd hdB
  simp only [mem_Icc] at hd hdB
  rw [Nat.div_eq_of_lt (by omega)]
  simp

/-- A partial Möbius sum over `[p, y]` is controlled by two values of the Mertens function. -/
private theorem abs_sum_moebius_Icc_le (p y : ℕ) (hp : 1 ≤ p) :
    |∑ d ∈ Icc p y, moebiusReal d| ≤
      |∑ d ∈ Icc 1 (max y (p - 1)), moebiusReal d| + |∑ d ∈ Icc 1 (p - 1), moebiusReal d| := by
  by_cases hy : p ≤ y
  · have hsplit : Icc 1 y = Icc 1 (p - 1) ∪ Icc p y := by
      ext d; simp only [mem_Icc, mem_union]; omega
    have hdisj : Disjoint (Icc 1 (p - 1)) (Icc p y) := by
      rw [disjoint_left]; intro d h1 h2; simp only [mem_Icc] at h1 h2; omega
    have h := sum_union hdisj (f := moebiusReal)
    rw [← hsplit] at h
    rw [max_eq_left (by omega)]
    have : ∑ d ∈ Icc p y, moebiusReal d =
        ∑ d ∈ Icc 1 y, moebiusReal d - ∑ d ∈ Icc 1 (p - 1), moebiusReal d := by linarith
    rw [this]
    exact abs_sub _ _
  · rw [Icc_eq_empty (by omega), sum_empty, abs_zero]
    positivity

/-- **Prime-horizon dissipation.** For all sufficiently large primes `p`, adding `p` to the
horizon does not lower the Möbius `L²` prefix energy at any prefix `M ≥ 2p`. -/
theorem eventually_prime_horizon_step_nonneg :
    ∀ᶠ p : ℕ in atTop, p.Prime → ∀ M : ℕ, 2 ≤ M / p →
      sieveL2PrefixEnergy (p - 1) M moebiusReal ≤ sieveL2PrefixEnergy p M moebiusReal := by
  -- `m(x) ≤ 1/4` eventually
  have hm := (tendsto_finiteHarmonicSum_moebiusReal_zero.comp
    (tendsto_sub_atTop_nat 1)).eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  -- `|M(x)| ≤ (x+1)/24` eventually
  have hM : ∀ᶠ x : ℕ in atTop, |∑ d ∈ Icc 1 x, moebiusReal d| ≤ ((x : ℝ) + 1) / 24 := by
    have hb := (mu_pnt.bound (show (0 : ℝ) < 1 / 24 by norm_num))
    have hb' := (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually hb
    filter_upwards [hb'] with x hx
    simp only [Function.comp, Nat.cast_add, Nat.cast_one] at hx
    rw [show ((x : ℝ) + 1) = ((x + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast] at hx
    have e : (∑ n ∈ range (x + 1), μ n : ℤ) = ∑ d ∈ Icc 1 x, μ d := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < x + 1),
        ArithmeticFunction.map_zero, zero_add, Finset.Ico_add_one_right_eq_Icc]
    have hcast : (∑ d ∈ Icc 1 x, moebiusReal d) = ((∑ d ∈ Icc 1 x, μ d : ℤ) : ℝ) := by
      unfold moebiusReal; push_cast; rfl
    rw [e, Int.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((x + 1 : ℕ) : ℝ))] at hx
    rw [hcast]
    push_cast at hx ⊢
    linarith
  obtain ⟨X, hX⟩ := eventually_atTop.mp hM
  filter_upwards [hm, eventually_ge_atTop (4 * X + 8)] with p hmp hpX
  intro hp M hMp
  simp only [Function.comp] at hmp
  rw [← sub_nonneg, sieveL2PrefixEnergy_moebius_prime_step_eq hp M]
  set B := M / p with hBdef
  have hBr : (2 : ℝ) ≤ B := by exact_mod_cast hMp
  rw [sub_nonneg]
  -- three ranges of the ratio `B`
  by_cases hBp : B < p
  · rw [floor_head_eq_one_of_lt (by omega) hBp]; linarith
  by_cases hB4 : 4 * p ≤ B
  · -- large ratios: the Möbius mean controls the head
    have hfrac : (∑ d ∈ Icc 1 (p - 1), moebiusReal d * ((B / d : ℕ) : ℝ)) ≤
        (B : ℝ) * finiteHarmonicSum (p - 1) moebiusReal + (p - 1 : ℕ) := by
      unfold finiteHarmonicSum
      rw [mul_sum]
      have : (∑ d ∈ Icc 1 (p - 1), moebiusReal d * ((B / d : ℕ) : ℝ)) -
          ∑ d ∈ Icc 1 (p - 1), (B : ℝ) * (moebiusReal d / d) ≤ ∑ _d ∈ Icc 1 (p - 1), (1 : ℝ) := by
        rw [← sum_sub_distrib]
        apply sum_le_sum
        intro d hd
        have hd0 : 0 < d := (mem_Icc.mp hd).1
        obtain ⟨hlo, hhi⟩ := floor_div_gcd_bounds (m := 1) hd0 B
        simp only [Nat.gcd_one_right, Nat.cast_one, mul_one, Nat.div_one] at hlo hhi
        have hμd : |moebiusReal d| ≤ 1 := by
          unfold moebiusReal; exact_mod_cast abs_moebius_le_one
        have e : moebiusReal d * ((B / d : ℕ) : ℝ) - (B : ℝ) * (moebiusReal d / d) =
            moebiusReal d * (((B / d : ℕ) : ℝ) - (B : ℝ) / d) := by ring
        rw [e]
        have h1 : |((B / d : ℕ) : ℝ) - (B : ℝ) / d| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        calc moebiusReal d * (((B / d : ℕ) : ℝ) - (B : ℝ) / d)
            ≤ |moebiusReal d * (((B / d : ℕ) : ℝ) - (B : ℝ) / d)| := le_abs_self _
          _ = |moebiusReal d| * |((B / d : ℕ) : ℝ) - (B : ℝ) / d| := abs_mul _ _
          _ ≤ 1 * 1 := mul_le_mul hμd h1 (abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      simp only [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one] at this
      push_cast at this ⊢
      linarith
    have hpB : ((p - 1 : ℕ) : ℝ) ≤ (B : ℝ) / 4 := by
      have : p - 1 ≤ B / 4 := by omega
      have h4 : ((B / 4 : ℕ) : ℝ) ≤ (B : ℝ) / 4 := by
        rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self B 4
      exact (Nat.cast_le.mpr this).trans h4
    have hB0 : (0 : ℝ) ≤ B := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hmp hB0]
  · -- middle ratios: three Mertens values
    push Not at hBp hB4
    rw [floor_head_eq_one_sub_tail (by omega) hBp]
    have htail : (∑ d ∈ Icc p B, moebiusReal d * ((B / d : ℕ) : ℝ)) =
        ∑ k ∈ ({1, 2, 3} : Finset ℕ), ∑ d ∈ Icc p (B / k), moebiusReal d := by
      have hfloor (d : ℕ) (hd : d ∈ Icc p B) :
          ((B / d : ℕ) : ℝ) = ∑ k ∈ ({1, 2, 3} : Finset ℕ), if d ≤ B / k then (1 : ℝ) else 0 := by
        obtain ⟨h1, h2⟩ := mem_Icc.mp hd
        have hd0 : 0 < d := by omega
        have hlt : B / d < 4 := by
          rw [Nat.div_lt_iff_lt_mul hd0]; omega
        simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
          show (1 : ℕ) ≠ 2 by decide, show (1 : ℕ) ≠ 3 by decide, show (2 : ℕ) ≠ 3 by decide,
          or_self, not_false_eq_true, Finset.sum_singleton]
        have e1 : d ≤ B / 1 := by simp; omega
        have e2 : d ≤ B / 2 ↔ 2 ≤ B / d := by
          rw [Nat.le_div_iff_mul_le (by norm_num), Nat.le_div_iff_mul_le hd0]; ring_nf
        have e3 : d ≤ B / 3 ↔ 3 ≤ B / d := by
          rw [Nat.le_div_iff_mul_le (by norm_num), Nat.le_div_iff_mul_le hd0]; ring_nf
        rw [if_pos e1]
        have hBd1 : 1 ≤ B / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
        rcases (by omega : B / d = 1 ∨ B / d = 2 ∨ B / d = 3) with h | h | h
        · rw [h, if_neg (by rw [e2, h]; omega), if_neg (by rw [e3, h]; omega)]; norm_num
        · rw [h, if_pos (by rw [e2]; omega), if_neg (by rw [e3, h]; omega)]; norm_num
        · rw [h, if_pos (by rw [e2]; omega), if_pos (by rw [e3]; omega)]; norm_num
      rw [sum_congr rfl fun d hd => by rw [hfloor d hd]]
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro k hk
      have hk0 : 0 < k := by simp at hk; omega
      simp only [mul_ite, mul_one, mul_zero]
      rw [← sum_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext d
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, le_trans h3 (Nat.div_le_self B k)⟩, h3⟩
    rw [htail]
    have hXp : X ≤ p - 1 := by omega
    have hbound (k : ℕ) (hk : k ∈ ({1, 2, 3} : Finset ℕ)) :
        |∑ d ∈ Icc p (B / k), moebiusReal d| ≤ 2 * (((B : ℝ) + 1) / 24) := by
      refine (abs_sum_moebius_Icc_le p (B / k) (by omega)).trans ?_
      have h1 := hX (max (B / k) (p - 1)) (le_trans hXp (le_max_right _ _))
      have h2 := hX (p - 1) hXp
      have hmax : ((max (B / k) (p - 1) : ℕ) : ℝ) ≤ B := by
        have : max (B / k) (p - 1) ≤ B := max_le (Nat.div_le_self B k) (by omega)
        exact_mod_cast this
      have hp1 : ((p - 1 : ℕ) : ℝ) ≤ B := by exact_mod_cast (show p - 1 ≤ B by omega)
      linarith
    have hsum : |∑ k ∈ ({1, 2, 3} : Finset ℕ), ∑ d ∈ Icc p (B / k), moebiusReal d| ≤
        3 * (2 * (((B : ℝ) + 1) / 24)) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _k ∈ ({1, 2, 3} : Finset ℕ), 2 * (((B : ℝ) + 1) / 24) := sum_le_sum hbound
        _ = _ := by simp
    have hB5 : (5 : ℝ) ≤ B := by
      have : 5 ≤ B := by omega
      exact_mod_cast this
    have := neg_abs_le (∑ k ∈ ({1, 2, 3} : Finset ℕ), ∑ d ∈ Icc p (B / k), moebiusReal d)
    linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
