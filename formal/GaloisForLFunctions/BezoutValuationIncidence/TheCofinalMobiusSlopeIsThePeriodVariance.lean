import GaloisForLFunctions.BezoutValuationIncidence.TheCofinalMobiusProfileIsAsymptoticallyLinear
import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMoebiusHarmonicSumsDecay
import GaloisForLFunctions.RHTower.SquarefreeCounting

/-!
# The cofinal Möbius slope is the limiting period variance

The period mean square of the Möbius sieve, `C(N) = Σ_{d,e ≤ N} μ(d)μ(e)/[d,e]`
(`moebiusPeriodMeanSquare`), converges to the slope `κ` of the cofinal profile
(`tendsto_moebiusPeriodMeanSquare`):

`lim_N C(N) = κ = lim_B P(B)/B`.

So the quadratic energy density of the literal Möbius source on linear horizons `M = O(N)` is
already its complete-period variance, although generic rows reach their period values only on
windows longer than `N²`.

Mechanism. The gcd parametrization `d = gb`, `e = ga` and `μ(ga)μ(gb) = μ(g)²μ(a)μ(b)[(g,ab)=1]`
give `C(N) = Σ_{g ≤ N} μ(g)²/g · S'_g(⌊N/g⌋)` (`moebiusPeriodMeanSquare_eq`). On the fibre
`⌊N/g⌋ = j` the coprimality weights average to the coprime-squarefree densities
`D(ab) = ρ ab/(σ(a)σ(b))`, so the fibre carries `ρ S(j) log(1+1/j)`, the same weight as the
cofinal band slope. The averaging is quantitative through `μ²[(·,m)=1] = Σ_{d²e ∣ ·} μ(d)μ(e)`
and the Euler–Mascheroni bounds for harmonic fibres (`abs_harmonicFibre_sub_log_le`); fibres with
`j > N^{1/8}` are negligible by `|S'_g(X)| ≪ Π(g)²/(1 + log X)⁴` and `Σ μ(g)²Π(g)²/g ≪ log N`.
-/

open Finset Filter Topology ArithmeticFunction

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### The period mean square in gcd coordinates -/

/-- The period mean square `C(N) = Σ_{d,e ≤ N} μ(d)μ(e)/[d,e]` of the Möbius sieve. -/
def moebiusPeriodMeanSquare (N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N, (moebius d : ℝ) * moebius e / Nat.lcm d e

/-- `μ(ga)μ(gb) = μ(g)²μ(a)μ(b)` when `(g, ab) = 1`, and `0` otherwise. -/
theorem moebius_mul_mul_eq (g a b : ℕ) :
    (moebius (g * b) : ℝ) * moebius (g * a) =
      if Nat.Coprime (a * b) g then (moebius g : ℝ) ^ 2 * (moebius a * moebius b) else 0 := by
  have hz : ∀ x y : ℕ, ¬ Nat.Coprime x y → (moebius (y * x) : ℝ) = 0 := by
    intro x y h
    obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hsq : ¬ Squarefree (y * x) := fun hs =>
      hp.one_lt.ne' (Nat.isUnit_iff.mp (hs p (Nat.mul_dvd_mul hpy hpx)))
    simp [moebius_eq_zero_of_not_squarefree hsq]
  by_cases ha : Nat.Coprime a g <;> by_cases hb : Nat.Coprime b g
  · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨ha, hb⟩),
      isMultiplicative_moebius.map_mul_of_coprime hb.symm,
      isMultiplicative_moebius.map_mul_of_coprime ha.symm]
    push_cast
    ring
  · rw [if_neg (fun h => hb (Nat.coprime_mul_iff_left.mp h).2), hz b g hb, zero_mul]
  · rw [if_neg (fun h => ha (Nat.coprime_mul_iff_left.mp h).1), hz a g ha, mul_zero]
  · rw [if_neg (fun h => ha (Nat.coprime_mul_iff_left.mp h).1), hz a g ha, mul_zero]

/-- **Gcd coordinates.** `C(N) = Σ_{g ≤ N} μ(g)²/g · S'_g(⌊N/g⌋)`. -/
theorem moebiusPeriodMeanSquare_eq (N : ℕ) :
    moebiusPeriodMeanSquare N =
      ∑ g ∈ Icc 1 N, (moebius g : ℝ) ^ 2 / g * coprimePairMoebiusHarmonicSum g (N / g) := by
  have hpt : ∀ q ∈ Icc 1 N, ∀ r ∈ Icc 1 N, (moebius q : ℝ) * moebius r / Nat.lcm q r =
      (moebius (Nat.gcd q r * (q / Nat.gcd q r)) : ℝ) * moebius (Nat.gcd q r * (r / Nat.gcd q r)) /
        ((Nat.gcd q r : ℝ) * ((r / Nat.gcd q r : ℕ) : ℝ) * ((q / Nat.gcd q r : ℕ) : ℝ)) := by
    intro q hq r hr
    have hq0 : 0 < q := (mem_Icc.mp hq).1
    have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq0
    have h1 : Nat.gcd q r * Nat.lcm q r = q * r := Nat.gcd_mul_lcm q r
    have h2 : Nat.gcd q r * (r / Nat.gcd q r) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
    have h3 : Nat.gcd q r * (q / Nat.gcd q r) = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
    have hgR : (0 : ℝ) < Nat.gcd q r := by exact_mod_cast hg
    have h1R : (Nat.gcd q r : ℝ) * Nat.lcm q r = q * r := by exact_mod_cast h1
    have h2R : (Nat.gcd q r : ℝ) * ((r / Nat.gcd q r : ℕ) : ℝ) = r := by exact_mod_cast h2
    have h3R : (Nat.gcd q r : ℝ) * ((q / Nat.gcd q r : ℕ) : ℝ) = q := by exact_mod_cast h3
    have hlcm : (Nat.lcm q r : ℝ) =
        (Nat.gcd q r : ℝ) * ((r / Nat.gcd q r : ℕ) : ℝ) * ((q / Nat.gcd q r : ℕ) : ℝ) := by
      apply mul_left_cancel₀ hgR.ne'
      rw [h1R, ← h2R, ← h3R]
      ring
    rw [h3, h2, hlcm]
  unfold moebiusPeriodMeanSquare
  rw [sum_congr rfl fun q hq => sum_congr rfl fun r hr => hpt q hq r hr,
    sum_gcd_reindex N (fun g a b => (moebius (g * b) : ℝ) * moebius (g * a) /
      ((g : ℝ) * a * b))]
  refine sum_congr rfl fun g _ => ?_
  unfold coprimePairMoebiusHarmonicSum
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [moebius_mul_mul_eq]
  by_cases hab : Nat.Coprime a b
  · by_cases habg : Nat.Coprime (a * b) g
    · rw [if_pos hab, if_pos habg, if_pos ⟨hab, habg⟩]
      field_simp
    · rw [if_pos hab, if_neg habg, if_neg (fun h => habg h.2), zero_div, mul_zero]
  · rw [if_neg hab, if_neg (fun h => hab h.1), mul_zero]

/-! ### Harmonic fibres, quantitatively -/

/-- `0 < H(n) - log n - γ < 1/n`. -/
theorem harmonic_sub_log_sub_gamma_mem {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant ∧
      (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant ≤ 1 / n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have h2 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  rw [Real.eulerMascheroniSeq', if_neg (by omega)] at h1
  rw [Real.eulerMascheroniSeq] at h2
  have hlog : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    have he : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  constructor <;> linarith

/-- `|A_j(n) − log(1 + 1/j)| ≤ 4(j+1)/n` for `n ≥ 2(j+1)`. -/
theorem abs_harmonicFibre_sub_log_le {n j : ℕ} (hj : 1 ≤ j) (hn : 2 * (j + 1) ≤ n) :
    |harmonicFibre n j - Real.log (1 + 1 / (j : ℝ))| ≤ 4 * ((j : ℝ) + 1) / n := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hnR : (2 : ℝ) * ((j : ℝ) + 1) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set a := n / j with ha
  set b := n / (j + 1) with hb
  have hb1 : 1 ≤ b := (Nat.one_le_div_iff (by omega)).mpr (by omega)
  have ha1 : 1 ≤ a := (Nat.one_le_div_iff (by omega)).mpr (by omega)
  have hba : b ≤ a := Nat.div_le_div_left (by omega) (by omega)
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbaR : (b : ℝ) ≤ a := by exact_mod_cast hba
  set x : ℝ := (n : ℝ) / j with hx
  set y : ℝ := (n : ℝ) / (j + 1) with hy
  have hau : (a : ℝ) ≤ x := Nat.cast_div_le
  have hbu : (b : ℝ) ≤ y := by
    have := Nat.cast_div_le (m := n) (n := j + 1) (α := ℝ); push_cast at this; exact this
  have hal : x - 1 ≤ a := by
    have h := Nat.lt_div_mul_add (a := n) (b := j) (by omega)
    have h' : (n : ℝ) < (a : ℝ) * j + j := by exact_mod_cast h
    rw [hx, div_sub_one (by positivity), div_le_iff₀ (by positivity)]; linarith
  have hbl : y - 1 ≤ b := by
    have h := Nat.lt_div_mul_add (a := n) (b := j + 1) (by omega)
    have h' : (n : ℝ) < (b : ℝ) * (j + 1) + (j + 1) := by exact_mod_cast h
    rw [hy, div_sub_one (by positivity), div_le_iff₀ (by positivity)]; linarith
  have hy2 : 2 ≤ y := by rw [hy, le_div_iff₀ (by positivity)]; linarith
  have hy0 : 0 < y := by linarith
  -- `1/b ≤ 2(j+1)/n`
  have hinvb : 1 / (b : ℝ) ≤ 2 * ((j : ℝ) + 1) / n := by
    have hbhalf : y / 2 ≤ b := by linarith
    have hyv : y / 2 = (n : ℝ) / (2 * ((j : ℝ) + 1)) := by rw [hy]; field_simp
    rw [hyv] at hbhalf
    rw [div_le_div_iff₀ (by linarith) hn0, one_mul]
    rw [div_le_iff₀ (by positivity)] at hbhalf
    linarith
  have hinva : 1 / (a : ℝ) ≤ 1 / (b : ℝ) := one_div_le_one_div_of_le (by linarith) hbaR
  -- log comparisons
  have hloga : 0 ≤ Real.log x - Real.log a ∧ Real.log x - Real.log a ≤ 1 / a := by
    constructor
    · linarith [Real.log_le_log (by linarith) hau]
    · rw [← Real.log_div (by linarith) (by linarith)]
      have := Real.log_le_sub_one_of_pos (show 0 < x / a by have : 0 < x := by linarith
                                                              positivity)
      have he : x / a - 1 = (x - a) / a := by field_simp
      have hq : (x - a) / a ≤ 1 / a := div_le_div_of_nonneg_right (by linarith) (by linarith)
      linarith
  have hlogb : 0 ≤ Real.log y - Real.log b ∧ Real.log y - Real.log b ≤ 1 / b := by
    constructor
    · linarith [Real.log_le_log (by linarith) hbu]
    · rw [← Real.log_div (by linarith) (by linarith)]
      have := Real.log_le_sub_one_of_pos (show 0 < y / b by positivity)
      have he : y / b - 1 = (y - b) / b := by field_simp
      have hq : (y - b) / b ≤ 1 / b := div_le_div_of_nonneg_right (by linarith) (by linarith)
      linarith
  have hℓ : Real.log (1 + 1 / (j : ℝ)) = Real.log x - Real.log y := by
    rw [← Real.log_div (by have : 0 < x := by linarith
                          linarith) hy0.ne']
    congr 1
    rw [hx, hy]
    field_simp
  obtain ⟨ha0, ha1'⟩ := harmonic_sub_log_sub_gamma_mem ha1
  obtain ⟨hb0, hb1'⟩ := harmonic_sub_log_sub_gamma_mem hb1
  rw [harmonicFibre_eq hj, ← ha, ← hb, hℓ, abs_le]
  constructor <;> nlinarith

end

end GaloisForLFunctions.BezoutValuationIncidence
