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
    · have hx0 : 0 < x := by linarith
      rw [← Real.log_div hx0.ne' (by linarith)]
      have := Real.log_le_sub_one_of_pos (show 0 < x / a by positivity)
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
    have hx0 : 0 < x := by linarith
    rw [← Real.log_div hx0.ne' hy0.ne']
    congr 1
    rw [hx, hy]
    field_simp
  obtain ⟨ha0, ha1'⟩ := harmonic_sub_log_sub_gamma_mem ha1
  obtain ⟨hb0, hb1'⟩ := harmonic_sub_log_sub_gamma_mem hb1
  have key : 1 / (a : ℝ) + 1 / (b : ℝ) ≤ 4 * ((j : ℝ) + 1) / n := by
    have : 4 * ((j : ℝ) + 1) / n = 2 * (2 * ((j : ℝ) + 1) / n) := by ring
    linarith
  obtain ⟨hla0, hla1⟩ := hloga
  obtain ⟨hlb0, hlb1⟩ := hlogb
  rw [harmonicFibre_eq hj, ← ha, ← hb, hℓ, abs_le]
  constructor <;> linarith

/-- Harmonic fibres are uniformly bounded: `A_j(n) ≤ 3`. -/
theorem harmonicFibre_le_three {n j : ℕ} (hj : 1 ≤ j) : harmonicFibre n j ≤ 3 := by
  rcases Nat.lt_or_ge n j with hnj | hnj
  · have hempty : (Icc 1 n).filter (fun g => n / g = j) = ∅ := by
      refine filter_eq_empty_iff.mpr fun g _ h => ?_
      have := Nat.div_le_self n g
      omega
    rw [harmonicFibre, hempty, sum_empty]; norm_num
  · have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hnR : (j : ℝ) ≤ n := by exact_mod_cast hnj
    have hn0 : (0 : ℝ) < n := by linarith
    rw [harmonicFibre, filter_div_eq_Ioc hj]
    have hpt : ∀ g ∈ Ioc (n / (j + 1)) (n / j), (g : ℝ)⁻¹ ≤ ((j : ℝ) + 1) / n := by
      intro g hg
      have h1 := (Nat.div_lt_iff_lt_mul (by omega)).mp (mem_Ioc.mp hg).1
      have hg0 : (0 : ℝ) < g := by
        have : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
        exact_mod_cast this
      rw [inv_le_comm₀ hg0 (by positivity), inv_div, div_le_iff₀ (by positivity)]
      exact_mod_cast h1.le
    calc ∑ g ∈ Ioc (n / (j + 1)) (n / j), (g : ℝ)⁻¹
        ≤ ∑ _g ∈ Ioc (n / (j + 1)) (n / j), ((j : ℝ) + 1) / n := sum_le_sum hpt
      _ = (#(Ioc (n / (j + 1)) (n / j)) : ℝ) * (((j : ℝ) + 1) / n) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ((n : ℝ) / (j * (j + 1)) + 1) * (((j : ℝ) + 1) / n) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [Nat.card_Ioc, Nat.cast_sub (Nat.div_le_div_left (by omega) (by omega))]
          have hu : ((n / j : ℕ) : ℝ) ≤ n / j := Nat.cast_div_le
          have hl : (n : ℝ) / (j + 1) - 1 ≤ ((n / (j + 1) : ℕ) : ℝ) := by
            have h := Nat.lt_div_mul_add (a := n) (b := j + 1) (by omega)
            have h' : (n : ℝ) < ((n / (j + 1) : ℕ) : ℝ) * (j + 1) + (j + 1) := by exact_mod_cast h
            rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
            linarith
          have he : (n : ℝ) / j - n / (j + 1) = n / (j * (j + 1)) := by field_simp; ring
          linarith
      _ = 1 / j + ((j : ℝ) + 1) / n := by field_simp
      _ ≤ 1 + 2 := by
          have h1 : 1 / (j : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hjR
          have h2 : ((j : ℝ) + 1) / n ≤ 2 := by rw [div_le_iff₀ hn0]; linarith
          linarith
      _ = 3 := by norm_num

/-! ### Squarefree coprime fibres -/

/-- `W_m(N, j) = Σ_{g ≤ N, ⌊N/g⌋ = j} μ(g)² [(g,m)=1]/g`. -/
def coprimeSquarefreeFibre (m N j : ℕ) : ℝ :=
  ∑ g ∈ Icc 1 N with N / g = j, (if Nat.Coprime g m then (moebius g : ℝ) ^ 2 else 0) / g

/-- `μ(g)² [(g,m)=1] = Σ_{d² ∣ g} Σ_{e ∣ (g,m)} μ(d)μ(e)`. -/
theorem moebius_sq_coprime_eq_sum {g m : ℕ} (hg : 1 ≤ g) (hm : m ≠ 0) :
    (if Nat.Coprime g m then (moebius g : ℝ) ^ 2 else 0) =
      ∑ d ∈ (Icc 1 g).filter (fun d => d * d ∣ g), ∑ e ∈ m.divisors.filter (· ∣ g),
        (moebius d : ℝ) * moebius e := by
  rw [← sum_mul_sum]
  have h1 : ∑ d ∈ (Icc 1 g).filter (fun d => d * d ∣ g), (moebius d : ℝ) = (moebius g : ℝ) ^ 2 := by
    have := RHTower.sum_moebius_sq_dvd_Icc hg
    exact_mod_cast this
  have h2 : ∑ e ∈ m.divisors.filter (· ∣ g), (moebius e : ℝ) =
      if Nat.Coprime g m then 1 else 0 := by
    have hset : m.divisors.filter (· ∣ g) = (Nat.gcd g m).divisors := by
      ext e
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hem, -⟩, heg⟩; exact ⟨⟨heg, hem⟩, Nat.gcd_ne_zero_right hm⟩
      · rintro ⟨⟨heg, hem⟩, -⟩; exact ⟨⟨hem, hm⟩, heg⟩
    rw [hset, sum_divisors_moebius_real_eq_ite]
  rw [h1, h2]
  split_ifs <;> ring

/-- Multiples of `L` in a fibre: `Σ_{g ∈ fibre, L ∣ g} 1/g = A_j(⌊N/L⌋)/L`. -/
theorem sum_fibre_multiples {N j L : ℕ} (hL : 0 < L) :
    ∑ g ∈ Icc 1 N with N / g = j ∧ L ∣ g, (g : ℝ)⁻¹ = (L : ℝ)⁻¹ * harmonicFibre (N / L) j := by
  have hbij : (Icc 1 N).filter (fun g => N / g = j ∧ L ∣ g) =
      ((Icc 1 (N / L)).filter (fun g' => N / L / g' = j)).image (fun g' => L * g') := by
    ext g
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hg1, hgN⟩, hj, ⟨g', rfl⟩⟩
      have hg'1 : 1 ≤ g' := by
        rcases Nat.eq_zero_or_pos g' with rfl | h
        · simp at hg1
        · exact h
      refine ⟨g', ⟨⟨hg'1, (Nat.le_div_iff_mul_le hL).mpr (by linarith [mul_comm L g'])⟩, ?_⟩, rfl⟩
      rw [Nat.div_div_eq_div_mul]
      exact hj
    · rintro ⟨g', ⟨⟨hg'1, hg'N⟩, hj⟩, rfl⟩
      have hle := (Nat.le_div_iff_mul_le hL).mp hg'N
      refine ⟨⟨Nat.mul_pos hL hg'1, by linarith [mul_comm L g']⟩, ?_, dvd_mul_right L g'⟩
      rw [← Nat.div_div_eq_div_mul]
      exact hj
  rw [hbij, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hL h), harmonicFibre, mul_sum]
  refine sum_congr rfl fun g' _ => ?_
  push_cast
  rw [mul_inv]

/-- **The fibre convolution.** `W_m(N,j) = Σ_{d ≤ N} Σ_{e ∣ m} μ(d)μ(e)/[d², e] · A_j(⌊N/[d²,e]⌋)`. -/
theorem coprimeSquarefreeFibre_eq {m N j : ℕ} (hm : m ≠ 0) :
    coprimeSquarefreeFibre m N j = ∑ d ∈ Icc 1 N, ∑ e ∈ m.divisors,
      (moebius d : ℝ) * moebius e / Nat.lcm (d * d) e *
        harmonicFibre (N / Nat.lcm (d * d) e) j := by
  unfold coprimeSquarefreeFibre
  have hexp : ∀ g ∈ (Icc 1 N).filter (fun g => N / g = j),
      (if Nat.Coprime g m then (moebius g : ℝ) ^ 2 else 0) / g =
        ∑ d ∈ Icc 1 N, ∑ e ∈ m.divisors,
          if d * d ∣ g ∧ e ∣ g then (moebius d : ℝ) * moebius e * (g : ℝ)⁻¹ else 0 := by
    intro g hg
    obtain ⟨hg1, hgN⟩ := mem_Icc.mp (mem_filter.mp hg).1
    rw [moebius_sq_coprime_eq_sum hg1 hm, sum_div]
    have hdset : (Icc 1 g).filter (fun d => d * d ∣ g) = (Icc 1 N).filter (fun d => d * d ∣ g) := by
      ext d
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2.trans hgN⟩, h3⟩
      · rintro ⟨⟨h1, -⟩, h3⟩
        have := Nat.le_of_dvd (by omega) h3
        exact ⟨⟨h1, by nlinarith⟩, h3⟩
    rw [hdset, sum_filter]
    refine sum_congr rfl fun d _ => ?_
    split_ifs with hdd
    · rw [sum_div, sum_filter]
      refine sum_congr rfl fun e _ => ?_
      by_cases heg : e ∣ g
      · rw [if_pos heg, if_pos ⟨hdd, heg⟩, div_eq_mul_inv]
      · rw [if_neg heg, if_neg (fun h => heg h.2)]
    · exact (sum_eq_zero fun e _ => if_neg fun h => hdd h.1).symm
  rw [sum_congr rfl hexp, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_comm]
  refine sum_congr rfl fun e he => ?_
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have he0 : 0 < e := Nat.pos_of_mem_divisors he
  have hL : 0 < Nat.lcm (d * d) e := Nat.lcm_pos (Nat.mul_pos hd0 hd0) he0
  rw [← sum_filter]
  have hfilter : ((Icc 1 N).filter (fun g => N / g = j)).filter (fun g => d * d ∣ g ∧ e ∣ g) =
      (Icc 1 N).filter (fun g => N / g = j ∧ Nat.lcm (d * d) e ∣ g) := by
    rw [filter_filter]
    congr 1
    funext g
    rw [Nat.lcm_dvd_iff]
  rw [hfilter, ← mul_sum, sum_fibre_multiples hL]
  ring

/-! ### The coprime-squarefree density as a Möbius series -/

/-- The Möbius series term `v_m(d) = Σ_{e ∣ m} μ(d)μ(e)/[d², e]`. -/
def coprimeSquarefreeSeriesTerm (m d : ℕ) : ℝ :=
  ∑ e ∈ m.divisors, (moebius d : ℝ) * moebius e / Nat.lcm (d * d) e

theorem abs_coprimeSquarefreeSeriesTerm_le (m d : ℕ) :
    |coprimeSquarefreeSeriesTerm m d| ≤ (m.divisors.card : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
  unfold coprimeSquarefreeSeriesTerm
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun e he => ?_
  have he0 : 0 < e := Nat.pos_of_mem_divisors he
  have hμ : |(moebius d : ℝ) * moebius e| ≤ 1 := by
    rw [abs_mul]
    have h1 : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    have h2 : |(moebius e : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    nlinarith [abs_nonneg (moebius d : ℝ), abs_nonneg (moebius e : ℝ)]
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp
  have hL : (d : ℝ) ^ 2 ≤ Nat.lcm (d * d) e := by
    have := Nat.le_of_dvd (Nat.lcm_pos (Nat.mul_pos hd0 hd0) he0) (Nat.dvd_lcm_left (d * d) e)
    have : ((d * d : ℕ) : ℝ) ≤ Nat.lcm (d * d) e := by exact_mod_cast this
    push_cast at this
    nlinarith
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < Nat.lcm (d * d) e)]
  calc |(moebius d : ℝ) * moebius e| / Nat.lcm (d * d) e ≤ 1 / Nat.lcm (d * d) e :=
        div_le_div_of_nonneg_right hμ (by linarith)
    _ ≤ 1 / (d : ℝ) ^ 2 := one_div_le_one_div_of_le hd2 hL
    _ = ((d : ℝ) ^ 2)⁻¹ := one_div _

theorem summable_coprimeSquarefreeSeriesTerm (m : ℕ) :
    Summable (coprimeSquarefreeSeriesTerm m) := by
  refine Summable.of_norm_bounded (g := fun d : ℕ => (m.divisors.card : ℝ) * ((d : ℝ) ^ 2)⁻¹) ?_ ?_
  · exact (Real.summable_nat_pow_inv.mpr (by norm_num)).mul_left _
  · intro d; rw [Real.norm_eq_abs]; exact abs_coprimeSquarefreeSeriesTerm_le m d

/-- `#{n ≤ N : n squarefree, (n,m)=1} = Σ_{d ≤ N} Σ_{e ∣ m} μ(d)μ(e)⌊N/[d², e]⌋`. -/
theorem coprimeSquarefreeCount_eq_sum {m : ℕ} (hm0 : m ≠ 0) (N : ℕ) :
    coprimeSquarefreeCount m N = ∑ d ∈ Icc 1 N, ∑ e ∈ m.divisors,
      (moebius d : ℝ) * moebius e * ((N / Nat.lcm (d * d) e : ℕ) : ℝ) := by
  unfold coprimeSquarefreeCount coprimeSquarefreeIndicator
  have hpt : ∀ n ∈ Icc 1 N, (if Nat.Coprime m n then ((moebius n : ℤ) : ℝ) ^ 2 else 0) =
      ∑ d ∈ Icc 1 N, ∑ e ∈ m.divisors,
        if d * d ∣ n ∧ e ∣ n then (moebius d : ℝ) * moebius e else 0 := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hc : (if Nat.Coprime m n then ((moebius n : ℤ) : ℝ) ^ 2 else 0) =
        (if Nat.Coprime n m then (moebius n : ℝ) ^ 2 else 0) := by
      by_cases h : Nat.Coprime m n
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    rw [hc]
    rw [moebius_sq_coprime_eq_sum hn1 hm0]
    have hdset : (Icc 1 n).filter (fun d => d * d ∣ n) = (Icc 1 N).filter (fun d => d * d ∣ n) := by
      ext d
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2.trans hnN⟩, h3⟩
      · rintro ⟨⟨h1, -⟩, h3⟩
        have := Nat.le_of_dvd (by omega) h3
        exact ⟨⟨h1, by nlinarith⟩, h3⟩
    rw [hdset, sum_filter]
    refine sum_congr rfl fun d _ => ?_
    split_ifs with hdd
    · rw [sum_filter]
      refine sum_congr rfl fun e _ => ?_
      by_cases hen : e ∣ n
      · rw [if_pos hen, if_pos ⟨hdd, hen⟩]
      · rw [if_neg hen, if_neg (fun h => hen h.2)]
    · exact (sum_eq_zero fun e _ => if_neg fun h => hdd h.1).symm
  rw [sum_congr rfl hpt, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_comm]
  refine sum_congr rfl fun e he => ?_
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have he0 : 0 < e := Nat.pos_of_mem_divisors he
  have hL : 0 < Nat.lcm (d * d) e := Nat.lcm_pos (Nat.mul_pos hd0 hd0) he0
  rw [← sum_filter]
  have hf : (Icc 1 N).filter (fun n => d * d ∣ n ∧ e ∣ n) =
      (Icc 1 N).filter (fun n => Nat.lcm (d * d) e ∣ n) := by
    congr 1; funext n; rw [Nat.lcm_dvd_iff]
  rw [hf, sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have := TransHorizonIncidenceMechanics.sum_Icc_filter_dvd_eq_sum_Icc_div hL N (fun _ => (1 : ℝ))
  simp only [sum_const, nsmul_eq_mul, mul_one] at this
  have h' : #((Icc 1 N).filter (fun n => Nat.lcm (d * d) e ∣ n)) = N / Nat.lcm (d * d) e := by
    have := (Nat.cast_inj (R := ℝ)).mp this
    rw [this, Nat.card_Icc, Nat.add_sub_cancel]
  exact_mod_cast h'

/-- **`D(m) = Σ_d Σ_{e ∣ m} μ(d)μ(e)/[d², e]`** for squarefree `m`. -/
theorem tsum_coprimeSquarefreeSeriesTerm {m : ℕ} (hm : Squarefree m) :
    ∑' d, coprimeSquarefreeSeriesTerm m d = coprimeSquarefreeDensity m := by
  have hm0 : m ≠ 0 := hm.ne_zero
  -- the normalized counts converge to the series
  set v : ℕ → ℕ → ℝ := fun N d => ∑ e ∈ m.divisors,
    (moebius d : ℝ) * moebius e * (((N / Nat.lcm (d * d) e : ℕ) : ℝ) / N) with hv
  have hcount : ∀ N : ℕ, 1 ≤ N → coprimeSquarefreeCount m N / N = ∑' d, v N d := by
    intro N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hsum := coprimeSquarefreeCount_eq_sum hm0 N
    rw [hsum, sum_div]
    rw [tsum_eq_sum (s := Icc 1 N)]
    · refine sum_congr rfl fun d _ => ?_
      simp only [hv]
      rw [sum_div]
      exact sum_congr rfl fun e _ => by ring
    · intro d hd
      simp only [hv]
      refine sum_eq_zero fun e he => ?_
      have he0 : 0 < e := Nat.pos_of_mem_divisors he
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp
      · have hdN : N < d := by simp only [mem_Icc, not_and, not_le] at hd; exact hd hd0
        have hL : N < Nat.lcm (d * d) e := by
          have := Nat.le_of_dvd (Nat.lcm_pos (Nat.mul_pos hd0 hd0) he0) (Nat.dvd_lcm_left (d * d) e)
          nlinarith
        rw [Nat.div_eq_of_lt hL]
        simp
  have hlim : Tendsto (fun N : ℕ => ∑' d, v N d) atTop (𝓝 (∑' d, coprimeSquarefreeSeriesTerm m d)) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun d : ℕ => (m.divisors.card : ℝ) * ((d : ℝ) ^ 2)⁻¹)
      ((Real.summable_nat_pow_inv.mpr (by norm_num)).mul_left _) ?_ ?_
    · intro d
      simp only [hv, coprimeSquarefreeSeriesTerm]
      refine tendsto_finsetSum _ fun e he => ?_
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp
      have he0 : 0 < e := Nat.pos_of_mem_divisors he
      have hL : 1 ≤ Nat.lcm (d * d) e := Nat.lcm_pos (Nat.mul_pos hd0 hd0) he0
      have h := (tendsto_natDiv_div_self hL).const_mul ((moebius d : ℝ) * moebius e)
      rw [show (moebius d : ℝ) * moebius e / Nat.lcm (d * d) e =
        (moebius d : ℝ) * moebius e * (1 / Nat.lcm (d * d) e) by ring]
      exact h
    · refine Eventually.of_forall fun N d => ?_
      simp only [hv, Real.norm_eq_abs]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum fun e he => ?_
      have he0 : 0 < e := Nat.pos_of_mem_divisors he
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp
      have hL0 : 0 < Nat.lcm (d * d) e := Nat.lcm_pos (Nat.mul_pos hd0 hd0) he0
      have hLR : (d : ℝ) ^ 2 ≤ Nat.lcm (d * d) e := by
        have := Nat.le_of_dvd hL0 (Nat.dvd_lcm_left (d * d) e)
        have : ((d * d : ℕ) : ℝ) ≤ Nat.lcm (d * d) e := by exact_mod_cast this
        push_cast at this
        nlinarith
      have hμ : |(moebius d : ℝ) * moebius e| ≤ 1 := by
        rw [abs_mul]
        have h1 : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        have h2 : |(moebius e : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        nlinarith [abs_nonneg (moebius d : ℝ), abs_nonneg (moebius e : ℝ)]
      have hfrac : |((N / Nat.lcm (d * d) e : ℕ) : ℝ) / N| ≤ ((d : ℝ) ^ 2)⁻¹ := by
        rcases Nat.eq_zero_or_pos N with rfl | hN
        · simp
        have hNR : (0 : ℝ) < N := by exact_mod_cast hN
        rw [abs_of_nonneg (by positivity), div_le_iff₀ hNR]
        have hc : ((N / Nat.lcm (d * d) e : ℕ) : ℝ) ≤ N / Nat.lcm (d * d) e := Nat.cast_div_le
        have hq : (N : ℝ) / Nat.lcm (d * d) e ≤ ((d : ℝ) ^ 2)⁻¹ * N := by
          rw [div_le_iff₀ (by exact_mod_cast hL0)]
          have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
          calc (N : ℝ) = ((d : ℝ) ^ 2)⁻¹ * N * (d : ℝ) ^ 2 := by field_simp
            _ ≤ ((d : ℝ) ^ 2)⁻¹ * N * Nat.lcm (d * d) e :=
                mul_le_mul_of_nonneg_left hLR (by positivity)
        linarith
      rw [abs_mul]
      calc |(moebius d : ℝ) * moebius e| * |((N / Nat.lcm (d * d) e : ℕ) : ℝ) / N|
          ≤ 1 * ((d : ℝ) ^ 2)⁻¹ := mul_le_mul hμ hfrac (abs_nonneg _) zero_le_one
        _ = ((d : ℝ) ^ 2)⁻¹ := one_mul _
  have hdens : Tendsto (fun N : ℕ => coprimeSquarefreeCount m N / N) atTop
      (𝓝 (coprimeSquarefreeDensity m)) := by
    have h := (tendsto_coprimeSquarefreeMean_of_squarefree m hm).comp tendsto_natCast_atTop_atTop
    refine h.congr' (Eventually.of_forall fun N => ?_)
    simp [Function.comp, coprimeSquarefreeMean]
  have hlim' : Tendsto (fun N : ℕ => coprimeSquarefreeCount m N / N) atTop
      (𝓝 (∑' d, coprimeSquarefreeSeriesTerm m d)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hcount N hN).symm
  exact tendsto_nhds_unique hlim' hdens

theorem coprimeSquarefreeDensity_mem {m : ℕ} (hm : Squarefree m) :
    0 ≤ coprimeSquarefreeDensity m ∧ coprimeSquarefreeDensity m ≤ 1 := by
  have h := tendsto_coprimeSquarefreeMean_of_squarefree m hm
  have hb : ∀ x : ℝ, |coprimeSquarefreeMean m x| ≤ 1 := abs_coprimeSquarefreeMean_le_one m
  have h0 : ∀ᶠ x : ℝ in atTop, 0 ≤ coprimeSquarefreeMean m x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact div_nonneg (coprimeSquarefreeCount_bounds _ _).1 hx.le
  exact ⟨ge_of_tendsto h h0, le_of_tendsto h (Eventually.of_forall fun x => (abs_le.mp (hb x)).2)⟩

/-- One term of the fibre convolution against its limit. -/
theorem fibre_term_le {N j L d : ℕ} (hj : 1 ≤ j) (hN : 2 * (j + 1) ≤ N) (hd : 1 ≤ d)
    (hdL : d * d ≤ L) :
    (L : ℝ)⁻¹ * |harmonicFibre (N / L) j - Real.log (1 + 1 / (j : ℝ))| ≤
      8 * ((j : ℝ) + 1) / N * (if d * d ≤ N then 1 else 0) +
        8 * ((j : ℝ) + 1) / (Real.sqrt N * d) := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hNR : (2 : ℝ) * ((j : ℝ) + 1) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL1 : 1 ≤ L := le_trans (Nat.one_le_iff_ne_zero.mpr (by positivity)) hdL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
  have hdLR : (d : ℝ) * d ≤ L := by exact_mod_cast hdL
  have hj0 : 0 ≤ 1 / (j : ℝ) := by positivity
  have hℓ0 : 0 ≤ Real.log (1 + 1 / (j : ℝ)) := Real.log_nonneg (by linarith)
  have hℓ1 : Real.log (1 + 1 / (j : ℝ)) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / j by positivity)
    have : 1 / (j : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hjR
    linarith
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hA0 := harmonicFibre_nonneg (N / L) j
  have hA3 := harmonicFibre_le_three (n := N / L) hj
  have hB : 0 ≤ 8 * ((j : ℝ) + 1) / (Real.sqrt N * d) := by positivity
  by_cases hcase : 2 * (j + 1) * L ≤ N
  · have hn : 2 * (j + 1) ≤ N / L := (Nat.le_div_iff_mul_le hL1).mpr (by linarith)
    have hnR : (2 : ℝ) * ((j : ℝ) + 1) ≤ ((N / L : ℕ) : ℝ) := by exact_mod_cast hn
    have hfib := abs_harmonicFibre_sub_log_le hj hn
    have hdN : d * d ≤ N := by nlinarith
    rw [if_pos hdN, mul_one]
    -- `⌊N/L⌋ ≥ N/(2L)`
    have hfl : (N : ℝ) / (2 * L) ≤ ((N / L : ℕ) : ℝ) := by
      have h := Nat.lt_div_mul_add (a := N) (b := L) hL1
      have h' : (N : ℝ) < ((N / L : ℕ) : ℝ) * L + L := by exact_mod_cast h
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hn0 : (0 : ℝ) < ((N / L : ℕ) : ℝ) := by linarith
    have hstep : (L : ℝ)⁻¹ * (4 * ((j : ℝ) + 1) / ((N / L : ℕ) : ℝ)) ≤ 8 * ((j : ℝ) + 1) / N := by
      rw [inv_mul_eq_div, div_div, div_le_div_iff₀ (by positivity) hN0]
      have : (N : ℝ) ≤ 2 * L * ((N / L : ℕ) : ℝ) := by
        rw [div_le_iff₀ (by positivity)] at hfl; linarith
      nlinarith
    calc (L : ℝ)⁻¹ * |harmonicFibre (N / L) j - Real.log (1 + 1 / (j : ℝ))|
        ≤ (L : ℝ)⁻¹ * (4 * ((j : ℝ) + 1) / ((N / L : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hfib (by positivity)
      _ ≤ 8 * ((j : ℝ) + 1) / N := hstep
      _ ≤ _ := le_add_of_nonneg_right hB
  · push Not at hcase
    have hcaseR : (N : ℝ) < 2 * ((j : ℝ) + 1) * L := by exact_mod_cast hcase
    have habs : |harmonicFibre (N / L) j - Real.log (1 + 1 / (j : ℝ))| ≤ 4 := by
      rw [abs_le]; constructor <;> linarith
    have hkey : (L : ℝ)⁻¹ ≤ 2 * ((j : ℝ) + 1) / (Real.sqrt N * d) := by
      rw [inv_le_comm₀ hLR (by positivity), inv_div, div_le_iff₀ (by positivity)]
      have h1 : (Real.sqrt N * d) ^ 2 ≤ (2 * ((j : ℝ) + 1) * L) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hN0.le]
        have : (N : ℝ) * (d : ℝ) ^ 2 ≤ 2 * ((j : ℝ) + 1) * L * L := by nlinarith
        nlinarith
      have h2 : Real.sqrt N * d ≤ 2 * ((j : ℝ) + 1) * L :=
        (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
      linarith
    have hA : 0 ≤ 8 * ((j : ℝ) + 1) / N * (if d * d ≤ N then 1 else 0) := by
      split_ifs <;> positivity
    calc (L : ℝ)⁻¹ * |harmonicFibre (N / L) j - Real.log (1 + 1 / (j : ℝ))|
        ≤ (L : ℝ)⁻¹ * 4 := mul_le_mul_of_nonneg_left habs (by positivity)
      _ ≤ 2 * ((j : ℝ) + 1) / (Real.sqrt N * d) * 4 := mul_le_mul_of_nonneg_right hkey (by norm_num)
      _ = 8 * ((j : ℝ) + 1) / (Real.sqrt N * d) := by ring
      _ ≤ _ := le_add_of_nonneg_left hA

/-- The convolution terms against their limit:
`Σ_{d ≤ N} Σ_{e ∣ m} |μ(d)μ(e)/[d²,e]| · |A_j(⌊N/[d²,e]⌋) − log(1+1/j)| ≪ τ(m)(j+1)(1 + log N)/√N`. -/
theorem abs_fibre_convolution_sub_le {m N j : ℕ} (hj : 1 ≤ j) (hN : 2 * (j + 1) ≤ N) :
    |∑ d ∈ Icc 1 N, ∑ e ∈ m.divisors, (moebius d : ℝ) * moebius e / Nat.lcm (d * d) e *
        (harmonicFibre (N / Nat.lcm (d * d) e) j - Real.log (1 + 1 / (j : ℝ)))| ≤
      16 * (m.divisors.card : ℝ) * ((j : ℝ) + 1) * (1 + Real.log N) / Real.sqrt N := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hNR : (2 : ℝ) * ((j : ℝ) + 1) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hτ0 : (0 : ℝ) ≤ (m.divisors.card : ℝ) := Nat.cast_nonneg _
  have hpt : ∀ d ∈ Icc 1 N, ∀ e ∈ m.divisors,
      |(moebius d : ℝ) * moebius e / Nat.lcm (d * d) e *
          (harmonicFibre (N / Nat.lcm (d * d) e) j - Real.log (1 + 1 / (j : ℝ)))| ≤
        8 * ((j : ℝ) + 1) / N * (if d * d ≤ N then 1 else 0) +
          8 * ((j : ℝ) + 1) / (Real.sqrt N * d) := by
    intro d hd e he
    have hd1 := (mem_Icc.mp hd).1
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    have hL0 : 0 < Nat.lcm (d * d) e := Nat.lcm_pos (Nat.mul_pos hd1 hd1) he0
    have hdL : d * d ≤ Nat.lcm (d * d) e := Nat.le_of_dvd hL0 (Nat.dvd_lcm_left _ _)
    have hcabs : |(moebius d : ℝ) * moebius e / Nat.lcm (d * d) e| ≤
        (Nat.lcm (d * d) e : ℝ)⁻¹ := by
      rw [abs_div, abs_of_pos (by exact_mod_cast hL0 : (0 : ℝ) < Nat.lcm (d * d) e),
        div_eq_mul_inv]
      have h1 : |(moebius d : ℝ) * moebius e| ≤ 1 := by
        rw [abs_mul]
        have h1 : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        have h2 : |(moebius e : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        nlinarith [abs_nonneg (moebius d : ℝ), abs_nonneg (moebius e : ℝ)]
      exact mul_le_of_le_one_left (by positivity) h1
    rw [abs_mul]
    refine (mul_le_mul_of_nonneg_right hcabs (abs_nonneg _)).trans ?_
    exact fibre_term_le hj hN hd1 hdL
  have hcount : (#((Icc 1 N).filter (fun d => d * d ≤ N)) : ℝ) ≤ Real.sqrt N := by
    have hsub : (Icc 1 N).filter (fun d => d * d ≤ N) ⊆ Icc 1 (Nat.sqrt N) := by
      intro d hd
      simp only [mem_filter, mem_Icc] at hd ⊢
      exact ⟨hd.1.1, Nat.le_sqrt.mpr hd.2⟩
    have := card_le_card hsub
    rw [Nat.card_Icc] at this
    calc (#((Icc 1 N).filter (fun d => d * d ≤ N)) : ℝ) ≤ (Nat.sqrt N : ℝ) := by
          exact_mod_cast (by omega : #((Icc 1 N).filter (fun d => d * d ≤ N)) ≤ Nat.sqrt N)
      _ ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hharm : ∑ d ∈ Icc 1 N, ((d : ℝ))⁻¹ ≤ 1 + Real.log N := by
    have h1 : ∑ d ∈ Icc 1 N, ((d : ℝ))⁻¹ = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; rfl
    rw [h1]; exact harmonic_le_one_add_log N
  have hsumX : ∑ d ∈ Icc 1 N, 8 * ((j : ℝ) + 1) / N * (if d * d ≤ N then 1 else 0) ≤
      8 * ((j : ℝ) + 1) / Real.sqrt N := by
    rw [← mul_sum, sum_boole]
    calc 8 * ((j : ℝ) + 1) / N * (#((Icc 1 N).filter (fun d => d * d ≤ N)) : ℝ)
        ≤ 8 * ((j : ℝ) + 1) / N * Real.sqrt N := mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = 8 * ((j : ℝ) + 1) / Real.sqrt N := by
        rw [div_mul_eq_mul_div, div_eq_div_iff hN0.ne' hsq.ne', mul_assoc,
          Real.mul_self_sqrt hN0.le]
  have hsumY : ∑ d ∈ Icc 1 N, 8 * ((j : ℝ) + 1) / (Real.sqrt N * d) ≤
      8 * ((j : ℝ) + 1) / Real.sqrt N * (1 + Real.log N) := by
    have h : ∑ d ∈ Icc 1 N, 8 * ((j : ℝ) + 1) / (Real.sqrt N * d) =
        8 * ((j : ℝ) + 1) / Real.sqrt N * ∑ d ∈ Icc 1 N, ((d : ℝ))⁻¹ := by
      rw [mul_sum]
      refine sum_congr rfl fun d _ => ?_
      rw [div_mul_eq_div_div, div_eq_mul_inv]
    rw [h]
    exact mul_le_mul_of_nonneg_left hharm (by positivity)
  calc _ ≤ ∑ d ∈ Icc 1 N, ∑ e ∈ m.divisors,
        |(moebius d : ℝ) * moebius e / Nat.lcm (d * d) e *
          (harmonicFibre (N / Nat.lcm (d * d) e) j - Real.log (1 + 1 / (j : ℝ)))| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ d ∈ Icc 1 N, ∑ _e ∈ m.divisors, (8 * ((j : ℝ) + 1) / N * (if d * d ≤ N then 1 else 0) +
          8 * ((j : ℝ) + 1) / (Real.sqrt N * d)) :=
        sum_le_sum fun d hd => sum_le_sum fun e he => hpt d hd e he
    _ = (m.divisors.card : ℝ) * (∑ d ∈ Icc 1 N, 8 * ((j : ℝ) + 1) / N * (if d * d ≤ N then 1 else 0) +
          ∑ d ∈ Icc 1 N, 8 * ((j : ℝ) + 1) / (Real.sqrt N * d)) := by
        simp only [sum_const, nsmul_eq_mul]
        rw [← sum_add_distrib, mul_sum]
    _ ≤ (m.divisors.card : ℝ) * (8 * ((j : ℝ) + 1) / Real.sqrt N +
          8 * ((j : ℝ) + 1) / Real.sqrt N * (1 + Real.log N)) := by gcongr
    _ ≤ 16 * (m.divisors.card : ℝ) * ((j : ℝ) + 1) * (1 + Real.log N) / Real.sqrt N := by
        simp only [div_eq_mul_inv]
        have hi : 0 ≤ (Real.sqrt N)⁻¹ := inv_nonneg.mpr hsq.le
        have hX : 0 ≤ (m.divisors.card : ℝ) * ((j : ℝ) + 1) * (Real.sqrt N)⁻¹ * Real.log N := by
          positivity
        nlinarith [hX]

/-- The tail of the density series: `|Σ_{d > N} v_m(d)| ≤ τ(m) ζ(3/2)/√N`. -/
theorem abs_tsum_coprimeSquarefreeSeriesTerm_tail_le (m : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    |∑' i, coprimeSquarefreeSeriesTerm m (i + (N + 1))| ≤
      (m.divisors.card : ℝ) * (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) / Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hτ0 : (0 : ℝ) ≤ (m.divisors.card : ℝ) := Nat.cast_nonneg _
  have hsumZ : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hsum1 : Summable (fun i : ℕ => ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (summable_nat_add_iff 1).mpr hsumZ
  have hb : ∀ i : ℕ, ‖coprimeSquarefreeSeriesTerm m (i + (N + 1))‖ ≤
      (m.divisors.card : ℝ) * ((Real.sqrt N)⁻¹ * ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
    intro i
    rw [Real.norm_eq_abs]
    refine (abs_coprimeSquarefreeSeriesTerm_le m (i + (N + 1))).trans ?_
    apply mul_le_mul_of_nonneg_left _ hτ0
    have hk : (0 : ℝ) < ((i + (N + 1) : ℕ) : ℝ) := by positivity
    have hkN : (N : ℝ) ≤ ((i + (N + 1) : ℕ) : ℝ) := by push_cast; linarith
    have hki : ((i + 1 : ℕ) : ℝ) ≤ ((i + (N + 1) : ℕ) : ℝ) := by push_cast; linarith
    have hi1 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have e1 : (((i + (N + 1) : ℕ) : ℝ) ^ 2)⁻¹ = ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((i + (N + 1) : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hk, ← Real.rpow_natCast, ← Real.rpow_neg hk.le]; norm_num
    rw [e1]
    have h1 : ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (Real.sqrt N)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hN0.le]
      exact Real.rpow_le_rpow_of_nonpos hN0 hkN (by norm_num)
    have h2 : ((i + (N + 1) : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hi1 hki (by norm_num)
    exact mul_le_mul h1 h2 (Real.rpow_nonneg hk.le _) (inv_nonneg.mpr hsq.le)
  have hbs : Summable (fun i : ℕ =>
      (m.divisors.card : ℝ) * ((Real.sqrt N)⁻¹ * ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    (hsum1.mul_left _).mul_left _
  have hsv : Summable (fun i : ℕ => coprimeSquarefreeSeriesTerm m (i + (N + 1))) :=
    Summable.of_norm_bounded hbs hb
  have htail : ∑' i : ℕ, (m.divisors.card : ℝ) *
      ((Real.sqrt N)⁻¹ * ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) =
      (m.divisors.card : ℝ) * ((Real.sqrt N)⁻¹ * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    rw [tsum_mul_left, tsum_mul_left, hsumZ.tsum_eq_zero_add]
    simp only [Nat.cast_zero, Real.zero_rpow (show -(3 / 2 : ℝ) ≠ 0 by norm_num), zero_add]
  calc |∑' i, coprimeSquarefreeSeriesTerm m (i + (N + 1))|
      ≤ ∑' i, ‖coprimeSquarefreeSeriesTerm m (i + (N + 1))‖ := norm_tsum_le_tsum_norm hsv.norm
    _ ≤ ∑' i : ℕ, (m.divisors.card : ℝ) *
          ((Real.sqrt N)⁻¹ * ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
        Summable.tsum_le_tsum hb hsv.norm hbs
    _ = _ := by rw [htail]; ring

/-- **Equidistribution of squarefree coprime fibres.** For squarefree `m`, `j ≥ 1` and
`N ≥ 2(j+1)`: `|W_m(N,j) − D(m) A_j(N)| ≤ K τ(m)(j+1)(1 + log N)/√N`. -/
theorem abs_coprimeSquarefreeFibre_sub_le {m N j : ℕ} (hm : Squarefree m) (hj : 1 ≤ j)
    (hN : 2 * (j + 1) ≤ N) :
    |coprimeSquarefreeFibre m N j - coprimeSquarefreeDensity m * harmonicFibre N j| ≤
      (20 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) * (m.divisors.card : ℝ) * ((j : ℝ) + 1) *
        (1 + Real.log N) / Real.sqrt N := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hNR : (2 : ℝ) * ((j : ℝ) + 1) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by omega
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hj0 : 0 ≤ 1 / (j : ℝ) := by positivity
  have hℓ0 : 0 ≤ Real.log (1 + 1 / (j : ℝ)) := Real.log_nonneg (by linarith)
  have hℓ1 : Real.log (1 + 1 / (j : ℝ)) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / j by positivity)
    have : 1 / (j : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hjR
    linarith
  have hτ1 : (1 : ℝ) ≤ (m.divisors.card : ℝ) := by
    have : 1 ≤ m.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm0⟩
    exact_mod_cast this
  have hZ0 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨hD0, hD1⟩ := coprimeSquarefreeDensity_mem hm
  have hsumv := summable_coprimeSquarefreeSeriesTerm m
  have hV := tsum_coprimeSquarefreeSeriesTerm hm
  have hv0 : coprimeSquarefreeSeriesTerm m 0 = 0 := by simp [coprimeSquarefreeSeriesTerm]
  have hrange : ∑ i ∈ range (N + 1), coprimeSquarefreeSeriesTerm m i =
      ∑ d ∈ Icc 1 N, coprimeSquarefreeSeriesTerm m d := by
    have h : range (N + 1) = insert 0 (Icc 1 N) := by
      ext n; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [h, sum_insert (by simp), hv0, zero_add]
  have hsplitV := hsumv.sum_add_tsum_nat_add (N + 1)
  rw [hrange, hV] at hsplitV
  have hW : coprimeSquarefreeFibre m N j =
      ∑ d ∈ Icc 1 N, ∑ e ∈ m.divisors, (moebius d : ℝ) * moebius e / Nat.lcm (d * d) e *
        (harmonicFibre (N / Nat.lcm (d * d) e) j - Real.log (1 + 1 / (j : ℝ))) +
      Real.log (1 + 1 / (j : ℝ)) * ∑ d ∈ Icc 1 N, coprimeSquarefreeSeriesTerm m d := by
    rw [coprimeSquarefreeFibre_eq hm0, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    rw [coprimeSquarefreeSeriesTerm, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun e _ => by ring
  have h1 := abs_fibre_convolution_sub_le (m := m) hj hN
  have h2 := abs_tsum_coprimeSquarefreeSeriesTerm_tail_le m hN1
  have h3 : |coprimeSquarefreeDensity m * (harmonicFibre N j - Real.log (1 + 1 / (j : ℝ)))| ≤
      4 * ((j : ℝ) + 1) / N := by
    rw [abs_mul, abs_of_nonneg hD0]
    calc coprimeSquarefreeDensity m * |harmonicFibre N j - Real.log (1 + 1 / (j : ℝ))|
        ≤ 1 * (4 * ((j : ℝ) + 1) / N) :=
          mul_le_mul hD1 (abs_harmonicFibre_sub_log_le hj hN) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h2' : |Real.log (1 + 1 / (j : ℝ)) * ∑' i, coprimeSquarefreeSeriesTerm m (i + (N + 1))| ≤
      (m.divisors.card : ℝ) * (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) / Real.sqrt N := by
    rw [abs_mul, abs_of_nonneg hℓ0]
    calc Real.log (1 + 1 / (j : ℝ)) * |∑' i, coprimeSquarefreeSeriesTerm m (i + (N + 1))|
        ≤ 1 * ((m.divisors.card : ℝ) * (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) / Real.sqrt N) :=
          mul_le_mul hℓ1 h2 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hdecomp : coprimeSquarefreeFibre m N j - coprimeSquarefreeDensity m * harmonicFibre N j =
      ∑ d ∈ Icc 1 N, ∑ e ∈ m.divisors, (moebius d : ℝ) * moebius e / Nat.lcm (d * d) e *
          (harmonicFibre (N / Nat.lcm (d * d) e) j - Real.log (1 + 1 / (j : ℝ))) -
        Real.log (1 + 1 / (j : ℝ)) * ∑' i, coprimeSquarefreeSeriesTerm m (i + (N + 1)) -
        coprimeSquarefreeDensity m * (harmonicFibre N j - Real.log (1 + 1 / (j : ℝ))) := by
    linear_combination hW + Real.log (1 + 1 / (j : ℝ)) * hsplitV
  have hineq : 4 * ((j : ℝ) + 1) / N ≤
      4 * (m.divisors.card : ℝ) * ((j : ℝ) + 1) * (1 + Real.log N) / Real.sqrt N := by
    rw [div_le_div_iff₀ hN0 hsq]
    have hsqN : Real.sqrt N ≤ N := by rw [Real.sqrt_le_left hN0.le]; nlinarith
    have h1 : 1 ≤ (m.divisors.card : ℝ) * (1 + Real.log N) := by nlinarith
    have hc : (0 : ℝ) ≤ 4 * ((j : ℝ) + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsqN hc,
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hc hN0.le)]
  have hineq2 : (m.divisors.card : ℝ) * (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) / Real.sqrt N ≤
      (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) * (m.divisors.card : ℝ) * ((j : ℝ) + 1) *
        (1 + Real.log N) / Real.sqrt N := by
    apply div_le_div_of_nonneg_right _ hsq.le
    have h1 : 1 ≤ ((j : ℝ) + 1) * (1 + Real.log N) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hZ0 (by linarith : (0 : ℝ) ≤
      (m.divisors.card : ℝ)))]
  rw [hdecomp]
  refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h1 h2')) (h3.trans hineq))
    |>.trans ?_
  have e : (20 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) * (m.divisors.card : ℝ) * ((j : ℝ) + 1) *
      (1 + Real.log N) / Real.sqrt N =
      16 * (m.divisors.card : ℝ) * ((j : ℝ) + 1) * (1 + Real.log N) / Real.sqrt N +
      (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) * (m.divisors.card : ℝ) * ((j : ℝ) + 1) *
        (1 + Real.log N) / Real.sqrt N +
      4 * (m.divisors.card : ℝ) * ((j : ℝ) + 1) * (1 + Real.log N) / Real.sqrt N := by ring
  rw [e]
  linarith

/-! ### Fibres of the gcd coordinates -/

/-- `ρ w(a) w(b) = μ(a)/a · μ(b)/b · D(ab)` on coprime `a, b`. -/
theorem squarefreeDensity_mul_moebiusSigma {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) :
    RHTower.Sieve.squarefreeDensity * (moebiusSigma a * moebiusSigma b) =
      (moebius a : ℝ) / a * ((moebius b : ℝ) / b) * coprimeSquarefreeDensity (a * b) := by
  have h := moebiusDilationPairDensity_div (g := 1) hab ha hb
  rw [Nat.cast_one, one_mul, div_one] at h
  rw [← h, moebiusDilationPairDensity]
  unfold moebiusReal
  ring

/-- **Fibre identity.** On the fibre `⌊N/g⌋ = j`,
`Σ_g (μ(g)²/g · S'_g(j) − ρ S(j)/g) = Σ_{a,b ≤ j, (a,b)=1} μ(a)/a · μ(b)/b · (W_{ab}(N,j) − D(ab) A_j(N))`. -/
theorem sum_fibre_sub_eq (N j : ℕ) :
    ∑ g ∈ Icc 1 N with N / g = j, ((moebius g : ℝ) ^ 2 / g * coprimePairMoebiusHarmonicSum g j -
        RHTower.Sieve.squarefreeDensity * (coprimePairMoebiusSigmaSum j / g)) =
      ∑ a ∈ Icc 1 j, ∑ b ∈ Icc 1 j, if Nat.Coprime a b then
        (moebius a : ℝ) / a * ((moebius b : ℝ) / b) *
          (coprimeSquarefreeFibre (a * b) N j -
            coprimeSquarefreeDensity (a * b) * harmonicFibre N j) else 0 := by
  have h1 : ∑ g ∈ Icc 1 N with N / g = j,
      (moebius g : ℝ) ^ 2 / g * coprimePairMoebiusHarmonicSum g j =
      ∑ a ∈ Icc 1 j, ∑ b ∈ Icc 1 j, if Nat.Coprime a b then
        (moebius a : ℝ) / a * ((moebius b : ℝ) / b) * coprimeSquarefreeFibre (a * b) N j
        else 0 := by
    simp only [coprimePairMoebiusHarmonicSum, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    by_cases hab : Nat.Coprime a b
    · rw [if_pos hab, coprimeSquarefreeFibre, mul_sum]
      refine sum_congr rfl fun g _ => ?_
      by_cases hg : Nat.Coprime (a * b) g
      · rw [if_pos ⟨hab, hg⟩, if_pos hg.symm]; ring
      · rw [if_neg (fun h => hg h.2), if_neg (fun h => hg h.symm)]; ring
    · rw [if_neg hab]
      exact sum_eq_zero fun g _ => by rw [if_neg (fun h => hab h.1), mul_zero]
  have h2 : ∑ g ∈ Icc 1 N with N / g = j,
      RHTower.Sieve.squarefreeDensity * (coprimePairMoebiusSigmaSum j / g) =
      ∑ a ∈ Icc 1 j, ∑ b ∈ Icc 1 j, if Nat.Coprime a b then
        (moebius a : ℝ) / a * ((moebius b : ℝ) / b) *
          (coprimeSquarefreeDensity (a * b) * harmonicFibre N j) else 0 := by
    have hA : ∑ g ∈ Icc 1 N with N / g = j,
        RHTower.Sieve.squarefreeDensity * (coprimePairMoebiusSigmaSum j / g) =
        RHTower.Sieve.squarefreeDensity * coprimePairMoebiusSigmaSum j * harmonicFibre N j := by
      rw [harmonicFibre, mul_sum]
      exact sum_congr rfl fun g _ => by ring
    rw [hA, coprimePairMoebiusSigmaSum, mul_sum, sum_mul]
    refine sum_congr rfl fun a ha => ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun b hb => ?_
    by_cases hab : Nat.Coprime a b
    · rw [if_pos hab, if_pos hab,
        squarefreeDensity_mul_moebiusSigma hab (mem_Icc.mp ha).1 (mem_Icc.mp hb).1]
      ring
    · rw [if_neg hab, if_neg hab]; ring
  rw [sum_sub_distrib, h1, h2, ← sum_sub_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

/-- **Fibre bound.** For `j ≥ 1` and `N ≥ 2(j+1)` the fibre `⌊N/g⌋ = j` differs from its
band-slope term by at most `K j²(j+1)(1 + log N)/√N`. -/
theorem abs_sum_fibre_sub_le {N j : ℕ} (hj : 1 ≤ j) (hN : 2 * (j + 1) ≤ N) :
    |∑ g ∈ Icc 1 N with N / g = j, ((moebius g : ℝ) ^ 2 / g * coprimePairMoebiusHarmonicSum g j -
        RHTower.Sieve.squarefreeDensity * (coprimePairMoebiusSigmaSum j / g))| ≤
      (20 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) * (j : ℝ) ^ 2 * ((j : ℝ) + 1) *
        (1 + Real.log N) / Real.sqrt N := by
  have hZ0 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set K := 20 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) with hK
  have hK0 : 0 ≤ K := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  set R := K * ((j : ℝ) + 1) * (1 + Real.log N) / Real.sqrt N with hR
  have hR0 : 0 ≤ R := div_nonneg (mul_nonneg (mul_nonneg hK0 (by positivity)) (by linarith))
    hsq.le
  have hpt : ∀ a ∈ Icc 1 j, ∀ b ∈ Icc 1 j, |if Nat.Coprime a b then
      (moebius a : ℝ) / a * ((moebius b : ℝ) / b) *
        (coprimeSquarefreeFibre (a * b) N j - coprimeSquarefreeDensity (a * b) * harmonicFibre N j)
      else 0| ≤ R := by
    intro a ha b hb
    have ha0 : 0 < a := (mem_Icc.mp ha).1
    have hb0 : 0 < b := (mem_Icc.mp hb).1
    split_ifs with hab
    · by_cases hsf : Squarefree (a * b)
      · have hab0 : (0 : ℝ) < ((a * b : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_pos ha0 hb0
        have hτ : ((a * b).divisors.card : ℝ) ≤ ((a * b : ℕ) : ℝ) := by
          exact_mod_cast Nat.card_divisors_le_self (a * b)
        have hc : |(moebius a : ℝ) / a * ((moebius b : ℝ) / b)| ≤ (((a * b : ℕ) : ℝ))⁻¹ := by
          rw [← moebiusHarmonic_mul hab, abs_div, abs_of_pos hab0, div_eq_mul_inv]
          exact mul_le_of_le_one_left (inv_nonneg.mpr hab0.le)
            (by exact_mod_cast abs_moebius_le_one)
        have hτ' : (((a * b : ℕ) : ℝ))⁻¹ * ((a * b).divisors.card : ℝ) ≤ 1 := by
          rw [inv_mul_le_iff₀ hab0, mul_one]; exact hτ
        rw [abs_mul]
        calc _ ≤ (((a * b : ℕ) : ℝ))⁻¹ * (K * ((a * b).divisors.card : ℝ) * ((j : ℝ) + 1) *
              (1 + Real.log N) / Real.sqrt N) :=
            mul_le_mul hc (abs_coprimeSquarefreeFibre_sub_le hsf hj hN) (abs_nonneg _)
              (inv_nonneg.mpr hab0.le)
          _ = (((a * b : ℕ) : ℝ))⁻¹ * ((a * b).divisors.card : ℝ) * R := by rw [hR]; ring
          _ ≤ 1 * R := mul_le_mul_of_nonneg_right hτ' hR0
          _ = R := one_mul R
      · have h0 : (moebius a : ℝ) * moebius b = 0 := by
          rcases not_and_or.mp (fun h => hsf (Nat.squarefree_mul_iff.mpr ⟨hab, h⟩)) with h | h
          · rw [moebius_eq_zero_of_not_squarefree h]; simp
          · rw [moebius_eq_zero_of_not_squarefree h]; simp
        have : (moebius a : ℝ) / a * ((moebius b : ℝ) / b) = 0 := by
          rw [div_mul_div_comm, h0, zero_div]
        rw [this, zero_mul, abs_zero]; exact hR0
    · rw [abs_zero]; exact hR0
  rw [sum_fibre_sub_eq]
  calc _ ≤ ∑ a ∈ Icc 1 j, ∑ b ∈ Icc 1 j, R :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a ha =>
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b hb => hpt a ha b hb))
    _ = _ := by
        simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        rw [hR]; ring

/-- Splitting `C(N) − γ_N` at the fibre cutoff `J`: the fibres `⌊N/g⌋ ≤ J` and the rest. -/
theorem moebiusPeriodMeanSquare_sub_cofinalBandSlope (N J : ℕ) :
    moebiusPeriodMeanSquare N - cofinalBandSlope N =
      ∑ j ∈ Icc 1 J, ∑ g ∈ Icc 1 N with N / g = j,
          ((moebius g : ℝ) ^ 2 / g * coprimePairMoebiusHarmonicSum g j -
            RHTower.Sieve.squarefreeDensity * (coprimePairMoebiusSigmaSum j / g)) +
        ∑ g ∈ Icc 1 N with ¬ N / g ≤ J,
          ((moebius g : ℝ) ^ 2 / g * coprimePairMoebiusHarmonicSum g (N / g) -
            RHTower.Sieve.squarefreeDensity * (coprimePairMoebiusSigmaSum (N / g) / g)) := by
  rw [moebiusPeriodMeanSquare_eq, cofinalBandSlope_eq, mul_sum, ← sum_sub_distrib,
    ← sum_filter_add_sum_filter_not (Icc 1 N) (fun g => N / g ≤ J)]
  congr 1
  rw [← sum_fiberwise_of_maps_to (s := (Icc 1 N).filter (fun g => N / g ≤ J)) (t := Icc 1 J)
    (g := fun g => N / g) (fun g hg => by
      obtain ⟨hgI, hgJ⟩ := mem_filter.mp hg
      obtain ⟨hg1, hgN⟩ := mem_Icc.mp hgI
      exact mem_Icc.mpr ⟨(Nat.one_le_div_iff (by omega)).mpr hgN, hgJ⟩)]
  refine sum_congr rfl fun j hj => ?_
  rw [filter_filter]
  refine sum_congr (filter_congr fun g _ =>
    ⟨fun h => h.2, fun h => ⟨by rw [h]; exact (mem_Icc.mp hj).2, h⟩⟩) fun g hg => ?_
  rw [(mem_filter.mp hg).2]

/-! ### The fibre cutoff `J(N) = ⌊N^{1/16}⌋` -/

/-- The fibre cutoff `J(N) = ⌊N^{1/16}⌋`, as an iterated integer square root. -/
def fibreCutoff (N : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt N)))

theorem fibreCutoff_pow_le (N : ℕ) : fibreCutoff N ^ 16 ≤ N := by
  have e : fibreCutoff N ^ 16 = (((fibreCutoff N ^ 2) ^ 2) ^ 2) ^ 2 := by ring
  rw [e]
  unfold fibreCutoff
  calc _ ≤ ((Nat.sqrt (Nat.sqrt (Nat.sqrt N)) ^ 2) ^ 2) ^ 2 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.sqrt_le' _) 2) 2) 2
    _ ≤ (Nat.sqrt (Nat.sqrt N) ^ 2) ^ 2 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.sqrt_le' _) 2) 2
    _ ≤ Nat.sqrt N ^ 2 := Nat.pow_le_pow_left (Nat.sqrt_le' _) 2
    _ ≤ N := Nat.sqrt_le' N

theorem lt_fibreCutoff_succ_pow (N : ℕ) : N < (fibreCutoff N + 1) ^ 16 := by
  have e : (fibreCutoff N + 1) ^ 16 = ((((fibreCutoff N + 1) ^ 2) ^ 2) ^ 2) ^ 2 := by ring
  rw [e]
  unfold fibreCutoff
  calc N < (Nat.sqrt N + 1) ^ 2 := Nat.lt_succ_sqrt' N
    _ ≤ ((Nat.sqrt (Nat.sqrt N) + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (Nat.lt_succ_sqrt' _) 2
    _ ≤ (((Nat.sqrt (Nat.sqrt (Nat.sqrt N)) + 1) ^ 2) ^ 2) ^ 2 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.lt_succ_sqrt' _) 2) 2
    _ ≤ _ := Nat.pow_le_pow_left (Nat.pow_le_pow_left
        (Nat.pow_le_pow_left (Nat.lt_succ_sqrt' _) 2) 2) 2

theorem tendsto_fibreCutoff : Tendsto fibreCutoff atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun M => ⟨M ^ 16, fun N hN => ?_⟩
  by_contra h
  have h1 := lt_fibreCutoff_succ_pow N
  have h2 : (fibreCutoff N + 1) ^ 16 ≤ M ^ 16 := Nat.pow_le_pow_left (by omega) 16
  omega

/-! ### Head and tail of the fibre decomposition -/

/-- **Head.** The fibres `j ≤ J` contribute at most `34 K/J³`. -/
theorem abs_sum_head_le {N J : ℕ} (hJ : 1 ≤ J) (hNJ : N < (J + 1) ^ 16) (hJN : J ^ 16 ≤ N)
    (h2 : 2 * (J + 1) ≤ N) :
    |∑ j ∈ Icc 1 J, ∑ g ∈ Icc 1 N with N / g = j,
        ((moebius g : ℝ) ^ 2 / g * coprimePairMoebiusHarmonicSum g j -
          RHTower.Sieve.squarefreeDensity * (coprimePairMoebiusSigmaSum j / g))| ≤
      34 * (20 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) / (J : ℝ) ^ 3 := by
  have hZ0 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set K := 20 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) with hK
  have hK0 : 0 ≤ K := by linarith
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ0 : (0 : ℝ) < J := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hJ8 : (J : ℝ) ^ 8 ≤ Real.sqrt N := by
    have h16 : ((J : ℝ) ^ 8) ^ 2 ≤ N := by
      rw [← pow_mul]; exact_mod_cast hJN
    exact (le_abs_self _).trans (Real.abs_le_sqrt h16)
  have hlog : 1 + Real.log N ≤ 17 * J := by
    have h1 : Real.log N ≤ 16 * Real.log ((J : ℝ) + 1) := by
      calc Real.log N ≤ Real.log (((J : ℝ) + 1) ^ 16) :=
            Real.log_le_log hN0 (by exact_mod_cast hNJ.le)
        _ = 16 * Real.log ((J : ℝ) + 1) := by rw [Real.log_pow]; norm_num
    have h2 : Real.log ((J : ℝ) + 1) ≤ J := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < J + 1 by positivity)
      linarith
    linarith
  have hpt : ∀ j ∈ Icc 1 J, |∑ g ∈ Icc 1 N with N / g = j,
      ((moebius g : ℝ) ^ 2 / g * coprimePairMoebiusHarmonicSum g j -
        RHTower.Sieve.squarefreeDensity * (coprimePairMoebiusSigmaSum j / g))| ≤
      34 * K / (J : ℝ) ^ 4 := by
    intro j hj
    obtain ⟨hj1, hjJ⟩ := mem_Icc.mp hj
    have hjR : (j : ℝ) ≤ J := by exact_mod_cast hjJ
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    refine (abs_sum_fibre_sub_le hj1 (by omega)).trans ?_
    have hKJ : 0 ≤ K * (J : ℝ) ^ 2 * (2 * J) :=
      mul_nonneg (mul_nonneg hK0 (by positivity)) (by positivity)
    have hnum : K * (j : ℝ) ^ 2 * ((j : ℝ) + 1) * (1 + Real.log N) ≤
        K * (J : ℝ) ^ 2 * (2 * J) * (17 * J) := by
      apply mul_le_mul _ hlog (by linarith) hKJ
      apply mul_le_mul _ (by linarith) (by positivity) (mul_nonneg hK0 (by positivity))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hj0 hjR 2) hK0
    calc K * (j : ℝ) ^ 2 * ((j : ℝ) + 1) * (1 + Real.log N) / Real.sqrt N
        ≤ K * (J : ℝ) ^ 2 * (2 * J) * (17 * J) / Real.sqrt N :=
          div_le_div_of_nonneg_right hnum hsq.le
      _ ≤ K * (J : ℝ) ^ 2 * (2 * J) * (17 * J) / (J : ℝ) ^ 8 :=
          div_le_div_of_nonneg_left (mul_nonneg hKJ (by positivity)) (pow_pos hJ0 8) hJ8
      _ = 34 * K / (J : ℝ) ^ 4 := by
          field_simp; ring
  calc _ ≤ ∑ j ∈ Icc 1 J, 34 * K / (J : ℝ) ^ 4 :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
    _ = 34 * K / (J : ℝ) ^ 3 := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        field_simp

/-- A tail term with `⌊N/g⌋ > J` is at most `(C₁ μ(g)²Π(g)²/g + ρC₂/g)/(1 + log(J+1))⁴`. -/
theorem abs_tail_term_le {C₁ C₂ ρ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ g : ℕ, g ≠ 0 → ∀ X : ℕ, 1 ≤ X →
      |coprimePairMoebiusHarmonicSum g X| ≤ C₁ * rankinProduct g ^ 2 / (1 + Real.log X) ^ 4)
    (hC₂0 : 0 ≤ C₂)
    (hC₂ : ∀ X : ℕ, 1 ≤ X → |coprimePairMoebiusSigmaSum X| ≤ C₂ / (1 + Real.log X) ^ 4)
    (hρ0 : 0 ≤ ρ) {N J g : ℕ} (hg1 : 1 ≤ g) (hX : J + 1 ≤ N / g) :
    |(moebius g : ℝ) ^ 2 / g * coprimePairMoebiusHarmonicSum g (N / g) -
        ρ * (coprimePairMoebiusSigmaSum (N / g) / g)| ≤
      (C₁ * ((moebius g : ℝ) ^ 2 * rankinProduct g ^ 2 / g) + ρ * C₂ * (g : ℝ)⁻¹) /
        (1 + Real.log ((J : ℝ) + 1)) ^ 4 := by
  have hX1 : 1 ≤ N / g := by omega
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg1
  have hlJ : 0 ≤ Real.log ((J : ℝ) + 1) :=
    Real.log_nonneg (by have := (Nat.cast_nonneg J : (0 : ℝ) ≤ J); linarith)
  have hL0 : 0 < 1 + Real.log ((J : ℝ) + 1) := by linarith
  have hL4 : 0 < (1 + Real.log ((J : ℝ) + 1)) ^ 4 := pow_pos hL0 4
  have hLX : (1 + Real.log ((J : ℝ) + 1)) ^ 4 ≤ (1 + Real.log ((N / g : ℕ) : ℝ)) ^ 4 := by
    have : Real.log ((J : ℝ) + 1) ≤ Real.log ((N / g : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hX)
    exact pow_le_pow_left₀ hL0.le (by linarith) 4
  have hμ0 : 0 ≤ (moebius g : ℝ) ^ 2 / g := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hA : |(moebius g : ℝ) ^ 2 / g * coprimePairMoebiusHarmonicSum g (N / g)| ≤
      C₁ * ((moebius g : ℝ) ^ 2 * rankinProduct g ^ 2 / g) / (1 + Real.log ((J : ℝ) + 1)) ^ 4 := by
    rw [abs_mul, abs_of_nonneg hμ0]
    calc (moebius g : ℝ) ^ 2 / g * |coprimePairMoebiusHarmonicSum g (N / g)|
        ≤ (moebius g : ℝ) ^ 2 / g *
            (C₁ * rankinProduct g ^ 2 / (1 + Real.log ((J : ℝ) + 1)) ^ 4) := by
          apply mul_le_mul_of_nonneg_left _ hμ0
          refine (hC₁ g (by omega) (N / g) hX1).trans ?_
          exact div_le_div_of_nonneg_left (mul_nonneg hC₁0 (sq_nonneg _)) hL4 hLX
      _ = _ := by ring
  have hB : |ρ * (coprimePairMoebiusSigmaSum (N / g) / g)| ≤
      ρ * C₂ * (g : ℝ)⁻¹ / (1 + Real.log ((J : ℝ) + 1)) ^ 4 := by
    rw [abs_mul, abs_of_nonneg hρ0, abs_div, abs_of_pos hg0]
    calc ρ * (|coprimePairMoebiusSigmaSum (N / g)| / g)
        ≤ ρ * (C₂ / (1 + Real.log ((J : ℝ) + 1)) ^ 4 / g) := by
          apply mul_le_mul_of_nonneg_left _ hρ0
          apply div_le_div_of_nonneg_right _ hg0.le
          exact (hC₂ (N / g) hX1).trans (div_le_div_of_nonneg_left hC₂0 hL4 hLX)
      _ = _ := by ring
  calc _ ≤ _ := abs_sub _ _
    _ ≤ _ := add_le_add hA hB
    _ = _ := by ring

/-- `C₁ Σ μ²Π²/g + ρC₂ Σ 1/g ≤ 16 (C₁E + ρC₂)(1 + log(J+1))` when `N < (J+1)^16`. -/
theorem tail_mass_le {C₁ C₂ ρ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂) (hρ0 : 0 ≤ ρ) {N J : ℕ}
    (hN : 1 ≤ N) (hNJ : N < (J + 1) ^ 16) :
    C₁ * ∑ g ∈ Icc 1 N, (moebius g : ℝ) ^ 2 * rankinProduct g ^ 2 / g +
        ρ * C₂ * ∑ g ∈ Icc 1 N, (g : ℝ)⁻¹ ≤
      16 * (C₁ * Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) + ρ * C₂) *
        (1 + Real.log ((J : ℝ) + 1)) := by
  have hR := mul_le_mul_of_nonneg_left (sum_rankinProduct_sq_div_le N) hC₁0
  have hE0 : 0 ≤ Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) := (Real.exp_pos _).le
  have hharm : ∑ g ∈ Icc 1 N, ((g : ℝ))⁻¹ ≤ 1 + Real.log N := by
    have h1 : ∑ g ∈ Icc 1 N, ((g : ℝ))⁻¹ = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; rfl
    rw [h1]; exact harmonic_le_one_add_log N
  have hH := mul_le_mul_of_nonneg_left hharm (mul_nonneg hρ0 hC₂0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlJ : 0 ≤ Real.log ((J : ℝ) + 1) :=
    Real.log_nonneg (by have := (Nat.cast_nonneg J : (0 : ℝ) ≤ J); linarith)
  have h16 : 1 + Real.log N ≤ 16 * (1 + Real.log ((J : ℝ) + 1)) := by
    have : Real.log N ≤ 16 * Real.log ((J : ℝ) + 1) := by
      calc Real.log N ≤ Real.log (((J : ℝ) + 1) ^ 16) :=
            Real.log_le_log hN0 (by exact_mod_cast hNJ.le)
        _ = 16 * Real.log ((J : ℝ) + 1) := by rw [Real.log_pow]; norm_num
    linarith
  have hT := mul_le_mul_of_nonneg_left h16
    (add_nonneg (mul_nonneg hC₁0 hE0) (mul_nonneg hρ0 hC₂0))
  linarith

/-- **Tail.** The fibres `j > J` contribute at most `16 (C₁E + ρC₂)/(1 + log(J+1))³` when
`N < (J+1)^16`, by the pair decay of `S'_g` and `S` and `Σ μ²Π²/g ≤ (1 + log N) E`. -/
theorem abs_sum_tail_le {C₁ C₂ ρ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ g : ℕ, g ≠ 0 → ∀ X : ℕ, 1 ≤ X →
      |coprimePairMoebiusHarmonicSum g X| ≤ C₁ * rankinProduct g ^ 2 / (1 + Real.log X) ^ 4)
    (hC₂0 : 0 ≤ C₂)
    (hC₂ : ∀ X : ℕ, 1 ≤ X → |coprimePairMoebiusSigmaSum X| ≤ C₂ / (1 + Real.log X) ^ 4)
    (hρ0 : 0 ≤ ρ) {N J : ℕ} (hN : 1 ≤ N) (hNJ : N < (J + 1) ^ 16) :
    |∑ g ∈ Icc 1 N with ¬ N / g ≤ J,
        ((moebius g : ℝ) ^ 2 / g * coprimePairMoebiusHarmonicSum g (N / g) -
          ρ * (coprimePairMoebiusSigmaSum (N / g) / g))| ≤
      16 * (C₁ * Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) + ρ * C₂) /
        (1 + Real.log ((J : ℝ) + 1)) ^ 3 := by
  have hlJ : 0 ≤ Real.log ((J : ℝ) + 1) :=
    Real.log_nonneg (by have := (Nat.cast_nonneg J : (0 : ℝ) ≤ J); linarith)
  have hL0 : 0 < 1 + Real.log ((J : ℝ) + 1) := by linarith
  have hnn : ∀ g ∈ Icc 1 N, 0 ≤
      (C₁ * ((moebius g : ℝ) ^ 2 * rankinProduct g ^ 2 / g) + ρ * C₂ * (g : ℝ)⁻¹) /
        (1 + Real.log ((J : ℝ) + 1)) ^ 4 := by
    intro g _
    have h1 : 0 ≤ (moebius g : ℝ) ^ 2 * rankinProduct g ^ 2 / g :=
      div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _)
    have h2 : 0 ≤ (g : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    exact div_nonneg (add_nonneg (mul_nonneg hC₁0 h1) (mul_nonneg (mul_nonneg hρ0 hC₂0) h2))
      (pow_pos hL0 4).le
  have hpt : ∀ g ∈ (Icc 1 N).filter (fun g => ¬ N / g ≤ J),
      |(moebius g : ℝ) ^ 2 / g * coprimePairMoebiusHarmonicSum g (N / g) -
          ρ * (coprimePairMoebiusSigmaSum (N / g) / g)| ≤
        (C₁ * ((moebius g : ℝ) ^ 2 * rankinProduct g ^ 2 / g) + ρ * C₂ * (g : ℝ)⁻¹) /
          (1 + Real.log ((J : ℝ) + 1)) ^ 4 := fun g hg => by
    obtain ⟨hgI, hgJ⟩ := mem_filter.mp hg
    exact abs_tail_term_le hC₁0 hC₁ hC₂0 hC₂ hρ0 (mem_Icc.mp hgI).1 (by omega)
  have hM := tail_mass_le hC₁0 hC₂0 hρ0 hN hNJ
  calc _ ≤ ∑ g ∈ Icc 1 N with ¬ N / g ≤ J,
        (C₁ * ((moebius g : ℝ) ^ 2 * rankinProduct g ^ 2 / g) + ρ * C₂ * (g : ℝ)⁻¹) /
          (1 + Real.log ((J : ℝ) + 1)) ^ 4 :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
    _ ≤ ∑ g ∈ Icc 1 N,
        (C₁ * ((moebius g : ℝ) ^ 2 * rankinProduct g ^ 2 / g) + ρ * C₂ * (g : ℝ)⁻¹) /
          (1 + Real.log ((J : ℝ) + 1)) ^ 4 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun g hg _ => hnn g hg
    _ = (C₁ * ∑ g ∈ Icc 1 N, (moebius g : ℝ) ^ 2 * rankinProduct g ^ 2 / g +
          ρ * C₂ * ∑ g ∈ Icc 1 N, (g : ℝ)⁻¹) / (1 + Real.log ((J : ℝ) + 1)) ^ 4 := by
        rw [← sum_div, sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ 16 * (C₁ * Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) + ρ * C₂) *
          (1 + Real.log ((J : ℝ) + 1)) / (1 + Real.log ((J : ℝ) + 1)) ^ 4 :=
        div_le_div_of_nonneg_right hM (pow_pos hL0 4).le
    _ = _ := by field_simp

/-- The deviation `C(N) − γ_N` is bounded through the fibre cutoff `J = J(N) ≥ 3`. -/
theorem abs_moebiusPeriodMeanSquare_sub_cofinalBandSlope_le {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ g : ℕ, g ≠ 0 → ∀ X : ℕ, 1 ≤ X →
      |coprimePairMoebiusHarmonicSum g X| ≤ C₁ * rankinProduct g ^ 2 / (1 + Real.log X) ^ 4)
    (hC₂0 : 0 ≤ C₂)
    (hC₂ : ∀ X : ℕ, 1 ≤ X → |coprimePairMoebiusSigmaSum X| ≤ C₂ / (1 + Real.log X) ^ 4)
    {N : ℕ} (hJ : 3 ≤ fibreCutoff N) :
    |moebiusPeriodMeanSquare N - cofinalBandSlope N| ≤
      34 * (20 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) / (fibreCutoff N : ℝ) ^ 3 +
        16 * (C₁ * Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) +
          RHTower.Sieve.squarefreeDensity * C₂) / (1 + Real.log ((fibreCutoff N : ℝ) + 1)) ^ 3 := by
  have hJN := fibreCutoff_pow_le N
  have hNJ := lt_fibreCutoff_succ_pow N
  have hJ2 : fibreCutoff N ^ 2 ≤ fibreCutoff N ^ 16 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2 : 2 * (fibreCutoff N + 1) ≤ N := by nlinarith
  rw [moebiusPeriodMeanSquare_sub_cofinalBandSlope N (fibreCutoff N)]
  have hρ0 : 0 ≤ RHTower.Sieve.squarefreeDensity := by
    rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  exact (abs_add_le _ _).trans (add_le_add (abs_sum_head_le (by omega) hNJ hJN h2)
    (abs_sum_tail_le hC₁0 hC₁ hC₂0 hC₂ hρ0 (by omega) hNJ))

/-! ### The limit -/

/-- **The cofinal slope is the limiting period mean square.**
`C(N) = Σ_{d,e ≤ N} μ(d)μ(e)/[d,e] → κ = ρ Σ_j S(j) log(1 + 1/j)`. -/
theorem tendsto_moebiusPeriodMeanSquare :
    Tendsto moebiusPeriodMeanSquare atTop (𝓝 cofinalMobiusSlope) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_coprimePairMoebiusHarmonicSum_le
  obtain ⟨C₂, hC₂⟩ := exists_abs_coprimePairMoebiusSigmaSum_le
  have hC₂0 : 0 ≤ C₂ := by
    have h1 := hC₂ 1 le_rfl
    rw [Nat.cast_one, Real.log_one, add_zero, one_pow, div_one] at h1
    exact (abs_nonneg _).trans h1
  set K := 34 * (20 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)))
  set T := 16 * (C₁ * Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) +
    RHTower.Sieve.squarefreeDensity * C₂)
  have hB : Tendsto (fun J : ℕ => K / (J : ℝ) ^ 3 + T / (1 + Real.log ((J : ℝ) + 1)) ^ 3)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun J : ℕ => K / (J : ℝ) ^ 3) atTop (𝓝 0) := by
      have h3 := (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp h3).const_mul K
    have h2 : Tendsto (fun J : ℕ => T / (1 + Real.log ((J : ℝ) + 1)) ^ 3) atTop (𝓝 0) := by
      have hl : Tendsto (fun J : ℕ => 1 + Real.log ((J : ℝ) + 1)) atTop atTop :=
        tendsto_atTop_add_const_left _ 1 (Real.tendsto_log_atTop.comp
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
      have h3 := (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hl
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp h3).const_mul T
    simpa using h1.add h2
  have hdiff : Tendsto (fun N => moebiusPeriodMeanSquare N - cofinalBandSlope N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (hB.comp tendsto_fibreCutoff)
    filter_upwards [tendsto_fibreCutoff.eventually (eventually_ge_atTop 3)] with N hN
    rw [Real.norm_eq_abs]
    exact abs_moebiusPeriodMeanSquare_sub_cofinalBandSlope_le hC₁0 hC₁ hC₂0 hC₂ hN
  have h := tendsto_cofinalBandSlope.add hdiff
  rw [add_zero] at h
  exact h.congr fun N => by ring

end

end GaloisForLFunctions.BezoutValuationIncidence
