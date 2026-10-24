import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMertensSawtoothCancellation
import GaloisForLFunctions.BezoutValuationIncidence.TheCofinalMobiusSlopeIsThePeriodVariance

/-!
# The Möbius prefix energy at large band ratio

Let `E_N(M) = Σ_{k ≤ M} s_{N,μ}(k)²` and `C(N) = Σ_{d,e ≤ N} μ(d)μ(e)/[d,e]`. With `B = ⌊M/N⌋`
(`abs_sieveL2PrefixEnergy_div_sub_le_of_le_pow`): if `B ≥ 256` and `N ≤ B¹⁶`, then

`|E_N(M)/M − C(N)| ≤ K/(1 + log B) + 256 (1 + log B)²/√B`

with an absolute constant `K`. So on every horizon `M` with `N ≤ (M/N)¹⁶`, including the
quadratic range `M ≍ N²` where generic rows need the full window sandwich, the Möbius prefix mean
square is its period value up to a function of the band ratio alone.

Mechanism. `E_N(M) = Σ_{d,e} μ(d)μ(e)⌊M/[d,e]⌋` (`sieveL2PrefixEnergy_eq_sum_lcm`), so
`M C(N) − E_N(M) = Σ μ(d)μ(e){M/[d,e]}`. In gcd coordinates `d = gb`, `e = ga` this is
`Σ_g μ(g)² Σ_{(a,g)=1} μ(a) Σ_{b ≤ N/g, (b,ag)=1} μ(b){M/(gab)}` (`sum_moebius_fract_lcm_eq`), and the
inner sum is a sawtooth sum with `t = ⌊M/(ga)⌋ ≥ B` (`exists_abs_sum_coprime_moebius_fract_le`):
`≪ Π(ag) t/(1 + log t)³ + √t`. The Rankin products have bounded harmonic mean, so the total is
`≪ M (1 + log N)²/(1 + log B)³ + M (1 + log N)²/√B`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### The prefix energy as an lcm form -/

theorem card_filter_dvd_Icc (M L : ℕ) : #((Icc 1 M).filter (fun k => L ∣ k)) = M / L := by
  rw [← Nat.card_multiples' M L]
  congr 1
  ext k
  simp only [mem_filter, mem_Icc, mem_range]
  omega

/-- `E_N(M) = Σ_{d,e ≤ N} c(d)c(e)⌊M/[d,e]⌋`. -/
theorem sieveL2PrefixEnergy_eq_sum_lcm (N M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy N M c =
      ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N, c d * c e * ((M / Nat.lcm d e : ℕ) : ℝ) := by
  unfold sieveL2PrefixEnergy sieveSeq
  have hpt : ∀ k : ℕ, (∑ d ∈ (Icc 1 N).filter (fun d => d ∣ k), c d) ^ (2 : ℕ) =
      ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N, if Nat.lcm d e ∣ k then c d * c e else 0 := by
    intro k
    rw [sq, sum_filter, sum_mul_sum]
    refine sum_congr rfl fun d _ => sum_congr rfl fun e _ => ?_
    by_cases hd : d ∣ k <;> by_cases he : e ∣ k <;>
      simp [hd, he, Nat.lcm_dvd_iff]
  simp_rw [hpt]
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, card_filter_dvd_Icc]
  ring

/-- `⌊M/L⌋ = M/L − {M/L}`. -/
theorem natCast_div_eq_sub_fract (M L : ℕ) :
    ((M / L : ℕ) : ℝ) = (M : ℝ) / (L : ℝ) - Int.fract ((M : ℝ) / (L : ℝ)) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have h := Nat.div_add_mod M L
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hR : (L : ℝ) * ((M / L : ℕ) : ℝ) + ((M % L : ℕ) : ℝ) = M := by exact_mod_cast h
  field_simp
  linarith

/-- `E_N(M; μ) = M C(N) − Σ_{d,e} μ(d)μ(e){M/[d,e]}`. -/
theorem sieveL2PrefixEnergy_moebiusReal_eq (N M : ℕ) :
    sieveL2PrefixEnergy N M moebiusReal = M * moebiusPeriodMeanSquare N -
      ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N,
        (moebius d : ℝ) * moebius e * Int.fract ((M : ℝ) / (Nat.lcm d e : ℕ)) := by
  rw [sieveL2PrefixEnergy_eq_sum_lcm, moebiusPeriodMeanSquare, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun e _ => ?_
  rw [natCast_div_eq_sub_fract]
  unfold moebiusReal
  ring

/-! ### Gcd coordinates of the sawtooth form -/

theorem lcm_eq_gcd_mul_div_mul_div (q r : ℕ) (hq : 0 < q) :
    Nat.lcm q r = Nat.gcd q r * (r / Nat.gcd q r) * (q / Nat.gcd q r) := by
  have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq
  have h1 : Nat.gcd q r * Nat.lcm q r = q * r := Nat.gcd_mul_lcm q r
  have h2 : Nat.gcd q r * (r / Nat.gcd q r) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
  have h3 : Nat.gcd q r * (q / Nat.gcd q r) = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
  apply Nat.eq_of_mul_eq_mul_left hg
  have hqr : q * r = Nat.gcd q r * (Nat.gcd q r * (r / Nat.gcd q r) * (q / Nat.gcd q r)) := by
    calc q * r = (Nat.gcd q r * (q / Nat.gcd q r)) * (Nat.gcd q r * (r / Nat.gcd q r)) := by
          rw [h3, h2]
      _ = _ := by ring
  rw [h1, hqr]

/-- **Gcd coordinates.** `Σ_{d,e ≤ N} μ(d)μ(e){M/[d,e]} =
Σ_g μ(g)² Σ_{a ≤ N/g, (a,g)=1} μ(a) Σ_{b ≤ N/g} μ(b)[(b,ag)=1]{M/(gab)}`. -/
theorem sum_moebius_fract_lcm_eq (N M : ℕ) :
    ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N,
        (moebius d : ℝ) * moebius e * Int.fract ((M : ℝ) / (Nat.lcm d e : ℕ)) =
      ∑ g ∈ Icc 1 N, (moebius g : ℝ) ^ 2 * ∑ a ∈ Icc 1 (N / g),
        (if Nat.Coprime a g then (moebius a : ℝ) else 0) * ∑ b ∈ Icc 1 (N / g),
          coprimeMoebiusWeight (a * g) b * Int.fract ((M : ℝ) / ((g * a * b : ℕ) : ℝ)) := by
  have hpt : ∀ q ∈ Icc 1 N, ∀ r ∈ Icc 1 N,
      (moebius q : ℝ) * moebius r * Int.fract ((M : ℝ) / (Nat.lcm q r : ℕ)) =
        (moebius (Nat.gcd q r * (q / Nat.gcd q r)) : ℝ) *
          moebius (Nat.gcd q r * (r / Nat.gcd q r)) *
          Int.fract ((M : ℝ) / ((Nat.gcd q r * (r / Nat.gcd q r) * (q / Nat.gcd q r) : ℕ) : ℝ)) := by
    intro q hq r _
    have hq0 : 0 < q := (mem_Icc.mp hq).1
    rw [← lcm_eq_gcd_mul_div_mul_div q r hq0, Nat.mul_div_cancel' (Nat.gcd_dvd_left q r),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)]
  rw [sum_congr rfl fun q hq => sum_congr rfl fun r hr => hpt q hq r hr,
    sum_gcd_reindex N (fun g a b => (moebius (g * b) : ℝ) * moebius (g * a) *
      Int.fract ((M : ℝ) / ((g * a * b : ℕ) : ℝ)))]
  refine sum_congr rfl fun g _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [moebius_mul_mul_eq]
  unfold coprimeMoebiusWeight
  by_cases hab : Nat.Coprime a b
  · by_cases hag : Nat.Coprime a g
    · by_cases hbg : Nat.Coprime b g
      · have habg : Nat.Coprime (a * b) g := Nat.coprime_mul_iff_left.mpr ⟨hag, hbg⟩
        have hbag : Nat.Coprime b (a * g) := Nat.coprime_mul_iff_right.mpr ⟨hab.symm, hbg⟩
        rw [if_pos hab, if_pos habg, if_pos hag, if_pos hbag]
        ring
      · rw [if_pos hab, if_neg (fun h => hbg (Nat.coprime_mul_iff_left.mp h).2), zero_mul,
          if_neg (fun h => hbg (Nat.coprime_mul_iff_right.mp h).2), zero_mul, mul_zero, mul_zero]
    · rw [if_pos hab, if_neg (fun h => hag (Nat.coprime_mul_iff_left.mp h).1), zero_mul,
        if_neg hag, zero_mul, mul_zero]
  · rw [if_neg hab]
    by_cases hbag : Nat.Coprime b (a * g)
    · have := (Nat.coprime_mul_iff_right.mp hbag).1
      exact absurd this.symm hab
    · rw [if_neg hbag, zero_mul, mul_zero, mul_zero]

/-! ### The bound -/

/-- One `(g, a)` cell: with `t = ⌊M/(ga)⌋ ≥ B = ⌊M/N⌋ ≥ 256`,
`|inner| ≤ (M/(ga)) (K Π(a)Π(g)/(1 + log B)³ + 1/√B)`. -/
theorem abs_cell_le {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ f c M X t : ℕ, f ≠ 0 → 1 ≤ c → M / c = t → 256 ≤ t →
      |∑ b ∈ Icc 1 X, coprimeMoebiusWeight f b * Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| ≤
        K * rankinProduct f * t / (1 + Real.log t) ^ 3 + Real.sqrt t)
    {N M g a : ℕ} (hg : 1 ≤ g) (ha : 1 ≤ a) (hga : g * a ≤ N) (hag : Nat.Coprime a g)
    (hB : 256 ≤ M / N) :
    |∑ b ∈ Icc 1 (N / g), coprimeMoebiusWeight (a * g) b *
        Int.fract ((M : ℝ) / ((g * a * b : ℕ) : ℝ))| ≤
      (M : ℝ) / ((g : ℝ) * a) * (K * rankinProduct a * rankinProduct g /
        (1 + Real.log (M / N : ℕ)) ^ 3 + 1 / Real.sqrt (M / N : ℕ)) := by
  have hc : 1 ≤ g * a := Nat.mul_pos hg ha
  have htB : M / N ≤ M / (g * a) := Nat.div_le_div_left hga (by omega)
  have ht : 256 ≤ M / (g * a) := hB.trans htB
  have h := hK (a * g) (g * a) M (N / g) (M / (g * a)) (Nat.mul_ne_zero (by omega) (by omega))
    hc rfl ht
  rw [rankinProduct_mul hag] at h
  have hBR : (256 : ℝ) ≤ (M / N : ℕ) := by exact_mod_cast hB
  have htR : ((M / N : ℕ) : ℝ) ≤ ((M / (g * a) : ℕ) : ℝ) := by exact_mod_cast htB
  have hlB : 0 ≤ Real.log (M / N : ℕ) := Real.log_nonneg (by linarith)
  have hLB : 0 < (1 + Real.log (M / N : ℕ)) ^ 3 := by positivity
  have hlt : Real.log (M / N : ℕ) ≤ Real.log (M / (g * a) : ℕ) :=
    Real.log_le_log (by linarith) htR
  have hLt : (1 + Real.log (M / N : ℕ)) ^ 3 ≤ (1 + Real.log (M / (g * a) : ℕ)) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have htM : ((M / (g * a) : ℕ) : ℝ) ≤ (M : ℝ) / ((g : ℝ) * a) := by
    have := Nat.cast_div_le (m := M) (n := g * a) (α := ℝ)
    push_cast at this
    exact this
  have hPa := one_le_rankinProduct a
  have hPg := one_le_rankinProduct g
  have hKP : 0 ≤ K * rankinProduct a * rankinProduct g :=
    mul_nonneg (mul_nonneg hK0 (by linarith)) (by linarith)
  have hsqB : 0 < Real.sqrt (M / N : ℕ) := Real.sqrt_pos.mpr (by linarith)
  have ht0 : (0 : ℝ) ≤ ((M / (g * a) : ℕ) : ℝ) := Nat.cast_nonneg _
  -- `√t ≤ t/√B`
  have hsq : Real.sqrt (M / (g * a) : ℕ) ≤ ((M / (g * a) : ℕ) : ℝ) / Real.sqrt (M / N : ℕ) := by
    rw [le_div_iff₀ hsqB]
    calc Real.sqrt (M / (g * a) : ℕ) * Real.sqrt (M / N : ℕ)
        ≤ Real.sqrt (M / (g * a) : ℕ) * Real.sqrt (M / (g * a) : ℕ) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htR) (Real.sqrt_nonneg _)
      _ = ((M / (g * a) : ℕ) : ℝ) := Real.mul_self_sqrt ht0
  refine h.trans ?_
  calc K * (rankinProduct a * rankinProduct g) * ((M / (g * a) : ℕ) : ℝ) /
        (1 + Real.log (M / (g * a) : ℕ)) ^ 3 + Real.sqrt (M / (g * a) : ℕ)
      ≤ K * rankinProduct a * rankinProduct g * ((M / (g * a) : ℕ) : ℝ) /
          (1 + Real.log (M / N : ℕ)) ^ 3 +
        ((M / (g * a) : ℕ) : ℝ) / Real.sqrt (M / N : ℕ) := by
        apply add_le_add _ hsq
        rw [← mul_assoc]
        exact div_le_div_of_nonneg_left (mul_nonneg hKP ht0) hLB hLt
    _ = ((M / (g * a) : ℕ) : ℝ) * (K * rankinProduct a * rankinProduct g /
          (1 + Real.log (M / N : ℕ)) ^ 3 + 1 / Real.sqrt (M / N : ℕ)) := by ring
    _ ≤ (M : ℝ) / ((g : ℝ) * a) * (K * rankinProduct a * rankinProduct g /
          (1 + Real.log (M / N : ℕ)) ^ 3 + 1 / Real.sqrt (M / N : ℕ)) :=
        mul_le_mul_of_nonneg_right htM (by positivity)

/-- `Σ_{g ≤ N} μ(g)² Π(g)/g ≤ (1 + log N) E`. -/
theorem sum_rankinProduct_div_le (N : ℕ) :
    ∑ g ∈ Icc 1 N, (moebius g : ℝ) ^ 2 * rankinProduct g / g ≤
      (1 + Real.log N) * Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) := by
  refine le_trans (sum_le_sum fun g _ => ?_) (sum_rankinProduct_sq_div_le N)
  have hP := one_le_rankinProduct g
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  nlinarith

theorem sum_inv_Icc_le (N : ℕ) : ∑ g ∈ Icc 1 N, ((g : ℝ))⁻¹ ≤ 1 + Real.log N := by
  have h1 : ∑ g ∈ Icc 1 N, ((g : ℝ))⁻¹ = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  rw [h1]; exact harmonic_le_one_add_log N

/-- **The sawtooth form is small.** For `B = ⌊M/N⌋ ≥ 256`:
`|Σ_{d,e} μ(d)μ(e){M/[d,e]}| ≤ M (K E² (1+log N)²/(1+log B)³ + (1+log N)²/√B)`. -/
theorem abs_sum_moebius_fract_lcm_le {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ f c M X t : ℕ, f ≠ 0 → 1 ≤ c → M / c = t → 256 ≤ t →
      |∑ b ∈ Icc 1 X, coprimeMoebiusWeight f b * Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| ≤
        K * rankinProduct f * t / (1 + Real.log t) ^ 3 + Real.sqrt t)
    {N M : ℕ} (hB : 256 ≤ M / N) :
    |∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N,
        (moebius d : ℝ) * moebius e * Int.fract ((M : ℝ) / (Nat.lcm d e : ℕ))| ≤
      M * (K * Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) ^ 2 * (1 + Real.log N) ^ 2 /
          (1 + Real.log (M / N : ℕ)) ^ 3 + (1 + Real.log N) ^ 2 / Real.sqrt (M / N : ℕ)) := by
  set E := Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) with hE
  set L3 := (1 + Real.log (M / N : ℕ)) ^ 3 with hL3
  set S := Real.sqrt (M / N : ℕ) with hS
  have hBR : (256 : ℝ) ≤ (M / N : ℕ) := by exact_mod_cast hB
  have hL30 : 0 < L3 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (M / N : ℕ) by linarith); positivity
  have hS0 : 0 < S := Real.sqrt_pos.mpr (by linarith)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hN1 : ∀ x : ℕ, 0 ≤ 1 + Real.log x := fun x => by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have := Real.log_nonneg (show (1 : ℝ) ≤ x by exact_mod_cast hx); linarith
  have hsumP := sum_rankinProduct_div_le N
  have hsumI := sum_inv_Icc_le N
  -- the cell bound summed over `a`
  have hcellsum : ∀ g ∈ Icc 1 N, |(moebius g : ℝ) ^ 2 * ∑ a ∈ Icc 1 (N / g),
      (if Nat.Coprime a g then (moebius a : ℝ) else 0) * ∑ b ∈ Icc 1 (N / g),
        coprimeMoebiusWeight (a * g) b * Int.fract ((M : ℝ) / ((g * a * b : ℕ) : ℝ))| ≤
      M * (K * ((moebius g : ℝ) ^ 2 * rankinProduct g / g) *
          ∑ a ∈ Icc 1 N, (moebius a : ℝ) ^ 2 * rankinProduct a / a / L3 +
        ((g : ℝ))⁻¹ * ∑ a ∈ Icc 1 N, ((a : ℝ))⁻¹ / S) := by
    intro g hg
    have hg1 : 1 ≤ g := (mem_Icc.mp hg).1
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
    have hμg : (moebius g : ℝ) ^ 2 ≤ 1 := by
      have : |(moebius g : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      nlinarith [abs_nonneg (moebius g : ℝ), sq_abs (moebius g : ℝ)]
    have hpt : ∀ a ∈ Icc 1 (N / g), |(if Nat.Coprime a g then (moebius a : ℝ) else 0) *
        ∑ b ∈ Icc 1 (N / g), coprimeMoebiusWeight (a * g) b *
          Int.fract ((M : ℝ) / ((g * a * b : ℕ) : ℝ))| ≤
        (moebius a : ℝ) ^ 2 * ((M : ℝ) / ((g : ℝ) * a) *
          (K * rankinProduct a * rankinProduct g / L3 + 1 / S)) := by
      intro a ha
      have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
      have hga : g * a ≤ N := by
        have := (mem_Icc.mp ha).2
        calc g * a ≤ g * (N / g) := Nat.mul_le_mul_left g this
          _ ≤ N := Nat.mul_div_le N g
      by_cases hag : Nat.Coprime a g
      · rw [if_pos hag, abs_mul]
        have hμa : |(moebius a : ℝ)| ≤ (moebius a : ℝ) ^ 2 := by
          rcases moebius_eq_or a with h | h | h <;> simp [h]
        exact mul_le_mul hμa (abs_cell_le hK0 hK hg1 ha1 hga hag hB) (abs_nonneg _)
          (sq_nonneg _)
      · rw [if_neg hag, zero_mul, abs_zero]
        have hPa := one_le_rankinProduct a
        have hPg := one_le_rankinProduct g
        have : 0 ≤ K * rankinProduct a * rankinProduct g / L3 + 1 / S :=
          add_nonneg (div_nonneg (mul_nonneg (mul_nonneg hK0 (by linarith)) (by linarith))
            hL30.le) (by positivity)
        positivity
    have hnn : ∀ a ∈ Icc 1 N, 0 ≤ (moebius a : ℝ) ^ 2 *
        ((M : ℝ) / ((g : ℝ) * a) * (K * rankinProduct a * rankinProduct g / L3 + 1 / S)) := by
      intro a _
      have hPa := one_le_rankinProduct a
      have hPg := one_le_rankinProduct g
      have : 0 ≤ K * rankinProduct a * rankinProduct g / L3 + 1 / S :=
        add_nonneg (div_nonneg (mul_nonneg (mul_nonneg hK0 (by linarith)) (by linarith))
          hL30.le) (by positivity)
      positivity
    have hterm : ∀ a ∈ Icc 1 N, (moebius g : ℝ) ^ 2 * ((moebius a : ℝ) ^ 2 *
        ((M : ℝ) / ((g : ℝ) * a) * (K * rankinProduct a * rankinProduct g / L3 + 1 / S))) ≤
        M * (K * ((moebius g : ℝ) ^ 2 * rankinProduct g / g) *
          ((moebius a : ℝ) ^ 2 * rankinProduct a / a / L3) + ((g : ℝ))⁻¹ * (((a : ℝ))⁻¹ / S)) := by
      intro a _
      have hμa : (moebius a : ℝ) ^ 2 ≤ 1 := by
        have : |(moebius a : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        nlinarith [abs_nonneg (moebius a : ℝ), sq_abs (moebius a : ℝ)]
      have hμμ : (moebius g : ℝ) ^ 2 * (moebius a : ℝ) ^ 2 ≤ 1 := by
        have := mul_le_mul hμg hμa (sq_nonneg _) zero_le_one
        linarith
      have hW : 0 ≤ (M : ℝ) * (((g : ℝ))⁻¹ * (((a : ℝ))⁻¹ / S)) := by positivity
      have e1 : (moebius g : ℝ) ^ 2 * ((moebius a : ℝ) ^ 2 *
          ((M : ℝ) / ((g : ℝ) * a) * (K * rankinProduct a * rankinProduct g / L3 + 1 / S))) =
          M * (K * ((moebius g : ℝ) ^ 2 * rankinProduct g / g) *
            ((moebius a : ℝ) ^ 2 * rankinProduct a / a / L3)) +
          (moebius g : ℝ) ^ 2 * (moebius a : ℝ) ^ 2 *
            ((M : ℝ) * (((g : ℝ))⁻¹ * (((a : ℝ))⁻¹ / S))) := by ring
      rw [e1, mul_add]
      have := mul_le_of_le_one_left hW hμμ
      linarith
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc (moebius g : ℝ) ^ 2 * |∑ a ∈ Icc 1 (N / g),
          (if Nat.Coprime a g then (moebius a : ℝ) else 0) * ∑ b ∈ Icc 1 (N / g),
            coprimeMoebiusWeight (a * g) b * Int.fract ((M : ℝ) / ((g * a * b : ℕ) : ℝ))|
        ≤ (moebius g : ℝ) ^ 2 * ∑ a ∈ Icc 1 (N / g), (moebius a : ℝ) ^ 2 *
            ((M : ℝ) / ((g : ℝ) * a) * (K * rankinProduct a * rankinProduct g / L3 + 1 / S)) :=
          mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)) (sq_nonneg _)
      _ ≤ (moebius g : ℝ) ^ 2 * ∑ a ∈ Icc 1 N, (moebius a : ℝ) ^ 2 *
            ((M : ℝ) / ((g : ℝ) * a) * (K * rankinProduct a * rankinProduct g / L3 + 1 / S)) :=
          mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg
            (Icc_subset_Icc le_rfl (Nat.div_le_self N g)) fun a ha _ => hnn a ha) (sq_nonneg _)
      _ ≤ ∑ a ∈ Icc 1 N, M * (K * ((moebius g : ℝ) ^ 2 * rankinProduct g / g) *
            ((moebius a : ℝ) ^ 2 * rankinProduct a / a / L3) + ((g : ℝ))⁻¹ * (((a : ℝ))⁻¹ / S)) := by
          rw [mul_sum]; exact sum_le_sum hterm
      _ = M * (K * ((moebius g : ℝ) ^ 2 * rankinProduct g / g) *
            ∑ a ∈ Icc 1 N, (moebius a : ℝ) ^ 2 * rankinProduct a / a / L3 +
          ((g : ℝ))⁻¹ * ∑ a ∈ Icc 1 N, ((a : ℝ))⁻¹ / S) := by
          rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
  rw [sum_moebius_fract_lcm_eq]
  have hA : ∑ a ∈ Icc 1 N, (moebius a : ℝ) ^ 2 * rankinProduct a / a / L3 ≤
      (1 + Real.log N) * E / L3 := by
    rw [← sum_div]; exact div_le_div_of_nonneg_right hsumP hL30.le
  have hI : ∑ a ∈ Icc 1 N, ((a : ℝ))⁻¹ / S ≤ (1 + Real.log N) / S := by
    rw [← sum_div]; exact div_le_div_of_nonneg_right hsumI hS0.le
  have hA0 : 0 ≤ ∑ a ∈ Icc 1 N, (moebius a : ℝ) ^ 2 * rankinProduct a / a / L3 :=
    sum_nonneg fun a _ => by have := one_le_rankinProduct a; positivity
  have hI0 : 0 ≤ ∑ a ∈ Icc 1 N, ((a : ℝ))⁻¹ / S := sum_nonneg fun a _ => by positivity
  calc _ ≤ ∑ g ∈ Icc 1 N, M * (K * ((moebius g : ℝ) ^ 2 * rankinProduct g / g) *
          ∑ a ∈ Icc 1 N, (moebius a : ℝ) ^ 2 * rankinProduct a / a / L3 +
        ((g : ℝ))⁻¹ * ∑ a ∈ Icc 1 N, ((a : ℝ))⁻¹ / S) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hcellsum)
    _ = M * (K * (∑ g ∈ Icc 1 N, (moebius g : ℝ) ^ 2 * rankinProduct g / g) *
          ∑ a ∈ Icc 1 N, (moebius a : ℝ) ^ 2 * rankinProduct a / a / L3 +
        (∑ g ∈ Icc 1 N, ((g : ℝ))⁻¹) * ∑ a ∈ Icc 1 N, ((a : ℝ))⁻¹ / S) := by
        rw [← mul_sum, sum_add_distrib, ← sum_mul, ← sum_mul, ← mul_sum]
    _ ≤ M * (K * ((1 + Real.log N) * E) * ((1 + Real.log N) * E / L3) +
        (1 + Real.log N) * ((1 + Real.log N) / S)) := by
        apply mul_le_mul_of_nonneg_left _ hM0
        apply add_le_add
        · apply mul_le_mul (mul_le_mul_of_nonneg_left hsumP hK0) hA hA0
          exact mul_nonneg hK0 (mul_nonneg (hN1 N) (Real.exp_pos _).le)
        · exact mul_le_mul hsumI hI hI0 (hN1 N)
    _ = M * (K * E ^ 2 * (1 + Real.log N) ^ 2 / L3 + (1 + Real.log N) ^ 2 / S) := by ring

/-- **Large band ratio.** If `B = ⌊M/N⌋ ≥ 256` and `N ≤ B¹⁶`, then
`|E_N(M)/M − C(N)| ≤ 256 K E²/(1 + log B) + 256 (1 + log B)²/√B`. -/
theorem abs_sieveL2PrefixEnergy_div_sub_le_of_le_pow {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ f c M X t : ℕ, f ≠ 0 → 1 ≤ c → M / c = t → 256 ≤ t →
      |∑ b ∈ Icc 1 X, coprimeMoebiusWeight f b * Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| ≤
        K * rankinProduct f * t / (1 + Real.log t) ^ 3 + Real.sqrt t)
    {N M : ℕ} (hN : 1 ≤ N) (hB : 256 ≤ M / N) (hNB : N ≤ (M / N) ^ 16) :
    |sieveL2PrefixEnergy N M moebiusReal / M - moebiusPeriodMeanSquare N| ≤
      256 * K * Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) ^ 2 /
          (1 + Real.log (M / N : ℕ)) +
        256 * (1 + Real.log (M / N : ℕ)) ^ 2 / Real.sqrt (M / N : ℕ) := by
  set E := Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) with hE
  have hBR : (256 : ℝ) ≤ (M / N : ℕ) := by exact_mod_cast hB
  have hM1 : 1 ≤ M := by
    have := Nat.div_le_self M N; omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM1
  have hlB : 0 ≤ Real.log (M / N : ℕ) := Real.log_nonneg (by linarith)
  have hLB : 0 < 1 + Real.log (M / N : ℕ) := by linarith
  have hS0 : 0 < Real.sqrt (M / N : ℕ) := Real.sqrt_pos.mpr (by linarith)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  -- `1 + log N ≤ 16 (1 + log B)`
  have h16 : 1 + Real.log N ≤ 16 * (1 + Real.log (M / N : ℕ)) := by
    have hNR : (N : ℝ) ≤ ((M / N : ℕ) : ℝ) ^ 16 := by exact_mod_cast hNB
    have := Real.log_le_log (by exact_mod_cast hN) hNR
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have h16sq : (1 + Real.log N) ^ 2 ≤ 256 * (1 + Real.log (M / N : ℕ)) ^ 2 := by
    have := pow_le_pow_left₀ (by linarith) h16 2
    nlinarith
  have hsum := abs_sum_moebius_fract_lcm_le hK0 hK (N := N) hB
  rw [sieveL2PrefixEnergy_moebiusReal_eq, sub_div, mul_div_cancel_left₀ _ hMR.ne',
    sub_sub_cancel_left, abs_neg, abs_div, abs_of_pos hMR, div_le_iff₀ hMR]
  refine hsum.trans ?_
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right _ hMR.le
  apply add_le_add
  · rw [div_le_div_iff₀ (by positivity) hLB]
    have hKE : 0 ≤ K * E ^ 2 := mul_nonneg hK0 (sq_nonneg _)
    calc K * E ^ 2 * (1 + Real.log N) ^ 2 * (1 + Real.log (M / N : ℕ))
        ≤ K * E ^ 2 * (256 * (1 + Real.log (M / N : ℕ)) ^ 2) * (1 + Real.log (M / N : ℕ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h16sq hKE) hLB.le
      _ = 256 * K * E ^ 2 * (1 + Real.log (M / N : ℕ)) ^ 3 := by ring
  · exact div_le_div_of_nonneg_right h16sq hS0.le

end

end GaloisForLFunctions.BezoutValuationIncidence
