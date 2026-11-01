import GaloisForLFunctions.RenormalizedIntersectionTheory.TheRoughWirsingBoundIsUniform
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheWirsingConstantOfAFlipTwinIsPositive
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The rough mean at a fixed scale

Fix a roughness `T`. Peeling one prime at a time (`gaugeHarmonicSum_roughGauge_prime`:
`S_p(Y) = S_{p+1}(Y) + (ω(p)/p) S_p(Y/p)`) transports the Wirsing asymptotic of `ω` to the
`T`-rough sums: if `S(Y) = c (log Y)^β + O(1)` with `0 < β ≤ 1`, then
`S_T(Y) = c Π_{p<T}(1 − ω(p)/p) (log Y)^β + O_T(1)` (`exists_abs_roughSum_sub_le`), since
`(log Y)^β − (log Y/p)^β ≤ (log 2p)^β` by subadditivity of `t ↦ t^β`. With `ω = 1`, `β = 1` this is
`F_T(Y) = Π_{p<T}(1 − 1/p) log Y + O_T(1)`.

For a flip twin, `δ_T = Π_{p<T}(1 − 1/p)/(1 − ω(p)/p)` is the Euler density of the flipped primes
below `T`, and the `T`-rough mean `S_T(Y)/F_T(Y)` is `(c/δ_T)(log Y)^{−2κ} + o((log Y)^{−2κ})`. The
fibres `a · R(T, N/a)` with `a ≤ N^η` carry rough means within `O(η^{2κ}) c_N` of `c_N/δ_T`, and
Rankin's bound `Σ_{a > X, T-smooth} 1/a ≤ K_T X^{−1/2}` (`exists_sum_smoothSet_tail_le`) makes the
remaining fibres negligible. Hence the **fixed-scale defect**
`Σ_{a T-smooth} (S_T(N/a) − (c_N/δ_T) F_T(N/a))²/(a F_T(N/a)) = o(H_N c_N²)`
(`eventually_fixedScaleDefect_le`): projected to the `T`-smooth fibres, the twin is `c_N/δ_T` times
its finite flip below `T`, up to `o(c_N)`.
-/

open Finset Filter Topology
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (gaugeHarmonicSum)
open GaloisForLFunctions.ArithmeticCountingPositivity (primeSetFlip)
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (roughInterval roughHarmonic smoothSet
  mem_smoothSet IsSignGauge)
open GaloisForLFunctions.ArithmeticElectrostatics (filter_dvd_Icc_eq_image)

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

section Peeling

variable {ω : ℕ → ℝ}

theorem roughGauge_zero (ω : ℕ → ℝ) : roughGauge 0 ω = ω := by
  funext n; unfold roughGauge; simp

theorem roughGauge_succ_of_not_prime {Q : ℕ} (hQ : ¬ Q.Prime) (ω : ℕ → ℝ) :
    roughGauge (Q + 1) ω = roughGauge Q ω := by
  funext n
  unfold roughGauge
  by_cases h : ∀ p ∈ n.primeFactors, Q ≤ p
  · have h' : ∀ p ∈ n.primeFactors, Q + 1 ≤ p := fun p hp => by
      rcases (h p hp).lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd (heq ▸ Nat.prime_of_mem_primeFactors hp) hQ
    rw [if_pos h', if_pos h]
  · have h' : ¬ ∀ p ∈ n.primeFactors, Q + 1 ≤ p := fun h'' =>
      h fun p hp => (Nat.le_succ Q).trans (h'' p hp)
    rw [if_neg h', if_neg h]

/-- **Peeling one prime**: `S_p(Y) = S_{p+1}(Y) + (ω(p)/p) S_p(Y/p)`. -/
theorem gaugeHarmonicSum_roughGauge_prime
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b) {p : ℕ} (hp : p.Prime) (Y : ℕ) :
    gaugeHarmonicSum (roughGauge p ω) Y =
      gaugeHarmonicSum (roughGauge (p + 1) ω) Y +
        ω p / p * gaugeHarmonicSum (roughGauge p ω) (Y / p) := by
  unfold gaugeHarmonicSum
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 Y) (fun n => p ∣ n)
    (fun n => roughGauge p ω n / n)
  have hsplit' := sum_filter_add_sum_filter_not (Icc 1 Y) (fun n => p ∣ n)
    (fun n => roughGauge (p + 1) ω n / n)
  -- off the multiples of `p` the two gauges agree; on them the finer gauge vanishes
  have hoff : ∑ n ∈ Icc 1 Y with ¬ p ∣ n, roughGauge p ω n / n =
      ∑ n ∈ Icc 1 Y with ¬ p ∣ n, roughGauge (p + 1) ω n / n := by
    refine sum_congr rfl fun n hn => ?_
    have hnd := (mem_filter.mp hn).2
    congr 1
    unfold roughGauge
    have hiff : (∀ q ∈ n.primeFactors, p ≤ q) ↔ ∀ q ∈ n.primeFactors, p + 1 ≤ q := by
      constructor
      · intro h q hq
        rcases (h q hq).lt_or_eq with hlt | heq
        · exact hlt
        · exact absurd (heq ▸ Nat.dvd_of_mem_primeFactors hq) hnd
      · intro h q hq; exact (Nat.le_succ p).trans (h q hq)
    by_cases h : ∀ q ∈ n.primeFactors, p ≤ q
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  have hon0 : ∑ n ∈ Icc 1 Y with p ∣ n, roughGauge (p + 1) ω n / n = 0 := by
    refine sum_eq_zero fun n hn => ?_
    obtain ⟨hn1, hnd⟩ := mem_filter.mp hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn1).1; omega
    unfold roughGauge
    rw [if_neg fun h => by
      have := h p (Nat.mem_primeFactors.mpr ⟨hp, hnd, hn0⟩); omega]
    simp
  -- the multiples of `p` are `p · [1, Y/p]`
  have hon : ∑ n ∈ Icc 1 Y with p ∣ n, roughGauge p ω n / n =
      ω p / p * ∑ m ∈ Icc 1 (Y / p), roughGauge p ω m / m := by
    rw [filter_dvd_Icc_eq_image hp.pos,
      sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
    have hpp : roughGauge p ω p = ω p := by
      unfold roughGauge; rw [if_pos fun q hq => by rw [hp.primeFactors] at hq; simp at hq; omega]
    rw [roughGauge_mul hmul p p m hp.ne_zero hm0, hpp]
    push_cast
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hm0' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    field_simp
  rw [← hsplit, ← hsplit', hon, hon0, hoff]
  ring

/-- `(log Y)^β − (log ⌊Y/p⌋)^β ∈ [0, (log 2p)^β]` for `0 < β ≤ 1`. -/
theorem abs_log_rpow_sub_log_div_rpow_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {p : ℕ}
    (hp : 1 ≤ p) (Y : ℕ) :
    |Real.log Y ^ β - Real.log ((Y / p : ℕ) : ℝ) ^ β| ≤ Real.log (2 * p) ^ β := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hl2p : 0 ≤ Real.log (2 * p) := Real.log_nonneg (by linarith)
  rcases lt_or_ge Y p with hYp | hYp
  · rw [Nat.div_eq_of_lt hYp, Nat.cast_zero, Real.log_zero,
      Real.zero_rpow hβ0.ne', sub_zero, abs_of_nonneg (Real.rpow_nonneg
        (Real.log_natCast_nonneg Y) _)]
    rcases Nat.eq_zero_or_pos Y with rfl | hY0
    · simp [Real.zero_rpow hβ0.ne', Real.rpow_nonneg hl2p]
    refine Real.rpow_le_rpow (Real.log_natCast_nonneg Y)
      (Real.log_le_log (by exact_mod_cast hY0) ?_) hβ0.le
    have : (Y : ℝ) ≤ p := by exact_mod_cast hYp.le
    linarith
  have hq1 : 1 ≤ Y / p := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hq0 : (0 : ℝ) < ((Y / p : ℕ) : ℝ) := by exact_mod_cast hq1
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  -- `⌊Y/p⌋ ≤ Y` and `Y < 2p ⌊Y/p⌋`
  have hqY : ((Y / p : ℕ) : ℝ) ≤ Y := by exact_mod_cast Nat.div_le_self Y p
  have hY2 : (Y : ℝ) ≤ 2 * p * ((Y / p : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add (a := Y) (b := p) (by omega)
    have h' : Y ≤ 2 * p * (Y / p) := by nlinarith [Nat.div_mul_le_self Y p]
    exact_mod_cast h'
  have hlq : Real.log ((Y / p : ℕ) : ℝ) ≤ Real.log Y := Real.log_le_log hq0 hqY
  have hlq0 : 0 ≤ Real.log ((Y / p : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hdiff : Real.log Y - Real.log ((Y / p : ℕ) : ℝ) ≤ Real.log (2 * p) := by
    rw [← Real.log_div hY0.ne' hq0.ne']
    exact Real.log_le_log (div_pos hY0 hq0) (by rw [div_le_iff₀ hq0]; linarith)
  have hsub := Real.rpow_add_le_add_rpow (sub_nonneg.mpr hlq) hlq0 hβ0.le hβ1
  rw [sub_add_cancel] at hsub
  have hmono : Real.log ((Y / p : ℕ) : ℝ) ^ β ≤ Real.log Y ^ β :=
    Real.rpow_le_rpow hlq0 hlq hβ0.le
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
  have := Real.rpow_le_rpow (sub_nonneg.mpr hlq) hdiff hβ0.le
  linarith

/-- **The fixed-scale rough asymptotic.** If `|S(Y) − c (log Y)^β| ≤ G (1 + log Y)^α` for all `Y`,
`α ≥ 0`, then for every `T` there is `G_T` with
`|S_T(Y) − c Π_{p<T}(1 − ω(p)/p) (log Y)^β| ≤ G_T (1 + log Y)^α` for all `Y`. -/
theorem exists_abs_roughSum_sub_le
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b) (hbd : ∀ n, |ω n| ≤ 1)
    {β c G α : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hα : 0 ≤ α)
    (hS : ∀ Y : ℕ, |gaugeHarmonicSum ω Y - c * Real.log Y ^ β| ≤ G * (1 + Real.log Y) ^ α)
    (T : ℕ) :
    ∃ G' : ℝ, ∀ Y : ℕ, |gaugeHarmonicSum (roughGauge T ω) Y -
      c * (∏ p ∈ Nat.primesBelow T, (1 - ω p / p)) * Real.log Y ^ β| ≤
        G' * (1 + Real.log Y) ^ α := by
  induction T with
  | zero => exact ⟨G, fun Y => by simpa [roughGauge_zero] using hS Y⟩
  | succ T ih =>
    obtain ⟨G', hG'⟩ := ih
    have hG'0 : 0 ≤ G' := by simpa using (abs_nonneg _).trans (hG' 0)
    by_cases hT : T.Prime
    · set a := c * ∏ p ∈ Nat.primesBelow T, (1 - ω p / p)
      have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT.one_lt.le
      refine ⟨G' + G' + |a| * Real.log (2 * T) ^ β, fun Y => ?_⟩
      have hPY : 1 ≤ (1 + Real.log Y) ^ α :=
        Real.one_le_rpow (by linarith [Real.log_natCast_nonneg Y]) hα
      have hmono : (1 + Real.log ((Y / T : ℕ) : ℝ)) ^ α ≤ (1 + Real.log Y) ^ α := by
        refine Real.rpow_le_rpow (by linarith [Real.log_natCast_nonneg (Y / T)]) ?_ hα
        rcases Nat.eq_zero_or_pos (Y / T) with h0 | h0
        · rw [h0, Nat.cast_zero, Real.log_zero]; linarith [Real.log_natCast_nonneg Y]
        · have := Real.log_le_log (by exact_mod_cast h0)
            (show ((Y / T : ℕ) : ℝ) ≤ Y by exact_mod_cast Nat.div_le_self Y T)
          linarith
      have hprod : c * ∏ p ∈ Nat.primesBelow (T + 1), (1 - ω p / p) = a * (1 - ω T / T) := by
        rw [Nat.primesBelow_succ, if_pos hT, prod_insert (fun h =>
          (Nat.lt_irrefl T) (Nat.mem_primesBelow.mp h).1)]
        simp only [a]; ring
      rw [hprod]
      have hpeel := gaugeHarmonicSum_roughGauge_prime hmul hT Y
      have hωT : |ω T / T| ≤ 1 := by
        rw [abs_div, Nat.abs_cast, div_le_one (by linarith)]; exact (hbd T).trans hT1
      have h1 := hG' Y
      have h2 := (hG' (Y / T)).trans (mul_le_mul_of_nonneg_left hmono hG'0)
      have h3 := abs_log_rpow_sub_log_div_rpow_le hβ0 hβ1 hT.one_lt.le Y
      have e : gaugeHarmonicSum (roughGauge (T + 1) ω) Y - a * (1 - ω T / T) * Real.log Y ^ β =
          (gaugeHarmonicSum (roughGauge T ω) Y - a * Real.log Y ^ β) -
            ω T / T * (gaugeHarmonicSum (roughGauge T ω) (Y / T) -
              a * Real.log ((Y / T : ℕ) : ℝ) ^ β) +
            ω T / T * a * (Real.log Y ^ β - Real.log ((Y / T : ℕ) : ℝ) ^ β) := by
        rw [hpeel]; ring
      rw [e]
      have hb2 : |ω T / T * (gaugeHarmonicSum (roughGauge T ω) (Y / T) -
          a * Real.log ((Y / T : ℕ) : ℝ) ^ β)| ≤ G' * (1 + Real.log Y) ^ α := by
        rw [abs_mul]; nlinarith [abs_nonneg (gaugeHarmonicSum (roughGauge T ω) (Y / T) -
          a * Real.log ((Y / T : ℕ) : ℝ) ^ β), abs_nonneg (ω T / T)]
      have hb3 : |ω T / T * a * (Real.log Y ^ β - Real.log ((Y / T : ℕ) : ℝ) ^ β)| ≤
          |a| * Real.log (2 * T) ^ β := by
        rw [abs_mul, abs_mul]
        have := mul_le_mul hωT h3 (abs_nonneg _) zero_le_one
        nlinarith [abs_nonneg a, abs_nonneg (ω T / T), abs_nonneg (Real.log Y ^ β -
          Real.log ((Y / T : ℕ) : ℝ) ^ β)]
      have hb3' : |a| * Real.log (2 * T) ^ β ≤ |a| * Real.log (2 * T) ^ β * (1 + Real.log Y) ^ α :=
        le_mul_of_one_le_right (mul_nonneg (abs_nonneg a)
          (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)) hPY
      calc _ ≤ |gaugeHarmonicSum (roughGauge T ω) Y - a * Real.log Y ^ β| +
            |ω T / T * (gaugeHarmonicSum (roughGauge T ω) (Y / T) -
              a * Real.log ((Y / T : ℕ) : ℝ) ^ β)| +
            |ω T / T * a * (Real.log Y ^ β - Real.log ((Y / T : ℕ) : ℝ) ^ β)| :=
            (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        _ ≤ G' * (1 + Real.log Y) ^ α + G' * (1 + Real.log Y) ^ α +
            |a| * Real.log (2 * T) ^ β * (1 + Real.log Y) ^ α :=
            add_le_add (add_le_add h1 hb2) (hb3.trans hb3')
        _ = (G' + G' + |a| * Real.log (2 * T) ^ β) * (1 + Real.log Y) ^ α := by ring
    · refine ⟨G', fun Y => ?_⟩
      rw [roughGauge_succ_of_not_prime hT, Nat.primesBelow_succ, if_neg hT]
      exact hG' Y

/-- The rough harmonic mass is the rough sum of the constant gauge. -/
theorem gaugeHarmonicSum_roughGauge_one (Q Y : ℕ) :
    gaugeHarmonicSum (roughGauge Q (fun _ => 1)) Y = roughHarmonic Q Y := by
  unfold gaugeHarmonicSum roughHarmonic roughInterval roughGauge
  rw [sum_filter]
  refine sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

/-- `|H_Y − log Y| ≤ 1`. -/
theorem abs_harmonic_sub_log_le (Y : ℕ) :
    |gaugeHarmonicSum (fun _ => (1 : ℝ)) Y - Real.log Y| ≤ 1 := by
  have h1 : gaugeHarmonicSum (fun _ => (1 : ℝ)) Y = hsum Y := by
    unfold gaugeHarmonicSum hsum; simp [one_div]
  rw [h1, abs_le]
  have hle := hsum_le Y
  have hge : Real.log Y ≤ hsum Y := by
    have h := log_add_one_le_harmonic Y
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    unfold hsum
    rcases Nat.eq_zero_or_pos Y with rfl | hY
    · simp
    · exact (Real.log_le_log (by exact_mod_cast hY) (by linarith)).trans h
  constructor <;> linarith

/-- **Fixed-scale rough mass**: `F_T(Y) = Π_{p<T}(1 − 1/p) log Y + O_T(1)`. -/
theorem exists_abs_roughHarmonic_sub_le (T : ℕ) :
    ∃ G : ℝ, ∀ Y : ℕ, |roughHarmonic T Y -
      (∏ p ∈ Nat.primesBelow T, (1 - 1 / (p : ℝ))) * Real.log Y| ≤ G := by
  have hS : ∀ Y : ℕ, |gaugeHarmonicSum (fun _ => (1 : ℝ)) Y - 1 * Real.log Y ^ (1 : ℝ)| ≤
      1 * (1 + Real.log Y) ^ (0 : ℝ) := by
    intro Y
    rw [Real.rpow_one, one_mul, Real.rpow_zero, one_mul]
    exact abs_harmonic_sub_log_le Y
  obtain ⟨G, hG⟩ := exists_abs_roughSum_sub_le (ω := fun _ => (1 : ℝ)) (fun _ _ _ _ => by ring)
    (fun _ => by simp) one_pos le_rfl le_rfl hS T
  refine ⟨G, fun Y => ?_⟩
  have h := hG Y
  rw [gaugeHarmonicSum_roughGauge_one, Real.rpow_one, one_mul, Real.rpow_zero, mul_one] at h
  simpa [one_div] using h

end Peeling

section Rankin

/-- `n ↦ n^{−1/2}` as a completely multiplicative function. -/
def invSqrtHom : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-(1 / 2 : ℝ))
  map_one' := by simp
  map_mul' m n := by
    push_cast
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Rankin's tail bound**: `Σ_{a ≤ N, T-smooth, a > X} 1/a ≤ K_T X^{−1/2}`. -/
theorem exists_sum_smoothSet_tail_le (T : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, ∀ X : ℝ, 0 < X →
      ∑ a ∈ (smoothSet T N).filter (fun a : ℕ => X < (a : ℝ)), (1 : ℝ) / a ≤ K / Real.sqrt X := by
  have hlt : ∀ {p : ℕ}, p.Prime → ‖invSqrtHom p‖ < 1 := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    change ‖(p : ℝ) ^ (-(1 / 2 : ℝ))‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  obtain ⟨hsum, hhas⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := invSqrtHom) hlt T
  set K := ∑' m : Nat.smoothNumbers T, invSqrtHom m
  have hK0 : 0 ≤ K := tsum_nonneg fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨K, hK0, fun N X hX => ?_⟩
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  -- `1/a ≤ a^{−1/2} X^{−1/2}` for `a > X`
  have hterm : ∀ a ∈ (smoothSet T N).filter (fun a : ℕ => X < (a : ℝ)),
      (1 : ℝ) / a ≤ invSqrtHom a / Real.sqrt X := by
    intro a ha
    have hXa := (mem_filter.mp ha).2
    have ha0 : (0 : ℝ) < a := hX.trans hXa
    change (1 : ℝ) / a ≤ (a : ℝ) ^ (-(1 / 2 : ℝ)) / Real.sqrt X
    rw [Real.rpow_neg ha0.le, ← Real.sqrt_eq_rpow, div_le_div_iff₀ ha0 hsX]
    have hsa : Real.sqrt X ≤ Real.sqrt a := Real.sqrt_le_sqrt hXa.le
    have hsa0 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
    rw [inv_mul_eq_div, le_div_iff₀ hsa0]
    have := Real.mul_self_sqrt ha0.le
    nlinarith
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_div]
  refine div_le_div_of_nonneg_right ?_ hsX.le
  -- the finite sum over smooth `a` is part of the Euler product
  have hinj : ∀ a ∈ (smoothSet T N).filter (fun a : ℕ => X < (a : ℝ)), a ∈ Nat.smoothNumbers T := by
    intro a ha
    obtain ⟨ha1, -, hap⟩ := mem_smoothSet.mp (mem_filter.mp ha).1
    exact Nat.mem_smoothNumbers'.mpr fun p hp hpa =>
      hap p (Nat.mem_primeFactors.mpr ⟨hp, hpa, by omega⟩)
  have hs : Summable (fun m : Nat.smoothNumbers T => invSqrtHom m) := hhas.summable
  calc ∑ a ∈ (smoothSet T N).filter (fun a : ℕ => X < (a : ℝ)), invSqrtHom a
      = ∑ m ∈ ((smoothSet T N).filter (fun a : ℕ => X < (a : ℝ))).subtype (· ∈ Nat.smoothNumbers T),
          invSqrtHom m := by
        rw [sum_subtype_of_mem (f := fun a => invSqrtHom a) hinj]
    _ ≤ K := hs.sum_le_tsum _ fun m _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

end Rankin

section Defect

/-- `L ℓ^β − ℓ L^β ≤ L^β L^β (L − ℓ)^{1−β}` for `0 ≤ ℓ ≤ L`, `0 < β ≤ 1`. -/
theorem mul_rpow_sub_le {β L ℓ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hℓ : 0 ≤ ℓ) (hℓL : ℓ ≤ L) :
    L * ℓ ^ β - ℓ * L ^ β ≤ L ^ β * L ^ β * (L - ℓ) ^ (1 - β) := by
  have hL : 0 ≤ L := hℓ.trans hℓL
  rcases hℓ.eq_or_lt with rfl | hℓ0
  · simp only [Real.zero_rpow hβ0.ne', mul_zero, zero_mul, sub_zero]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hL _) (Real.rpow_nonneg hL _))
      (Real.rpow_nonneg hL _)
  have hL0 : 0 < L := hℓ0.trans_le hℓL
  have eL : L = L ^ β * L ^ (1 - β) := by
    rw [← Real.rpow_add hL0]; simp
  have eℓ : ℓ = ℓ ^ β * ℓ ^ (1 - β) := by
    rw [← Real.rpow_add hℓ0]; simp
  have hsub := Real.rpow_add_le_add_rpow (sub_nonneg.mpr hℓL) hℓ (by linarith : (0 : ℝ) ≤ 1 - β)
    (by linarith)
  rw [sub_add_cancel] at hsub
  have hmono : ℓ ^ (1 - β) ≤ L ^ (1 - β) := Real.rpow_le_rpow hℓ hℓL (by linarith)
  have hmonoβ : ℓ ^ β ≤ L ^ β := Real.rpow_le_rpow hℓ hℓL hβ0.le
  have e1 : L * ℓ ^ β = ℓ ^ β * L ^ β * L ^ (1 - β) := by rw [mul_assoc, ← eL, mul_comm]
  have e2 : ℓ * L ^ β = ℓ ^ β * L ^ β * ℓ ^ (1 - β) := by
    rw [mul_comm (ℓ ^ β) (L ^ β), mul_assoc, ← eℓ, mul_comm]
  have e : L * ℓ ^ β - ℓ * L ^ β = ℓ ^ β * L ^ β * (L ^ (1 - β) - ℓ ^ (1 - β)) := by
    rw [e1, e2]; ring
  rw [e]
  have hd : 0 ≤ L ^ (1 - β) - ℓ ^ (1 - β) := sub_nonneg.mpr hmono
  have hd' : L ^ (1 - β) - ℓ ^ (1 - β) ≤ (L - ℓ) ^ (1 - β) := by linarith
  have hpos : 0 ≤ ℓ ^ β * L ^ β := mul_nonneg (Real.rpow_nonneg hℓ _) (Real.rpow_nonneg hL _)
  calc ℓ ^ β * L ^ β * (L ^ (1 - β) - ℓ ^ (1 - β)) ≤ ℓ ^ β * L ^ β * (L - ℓ) ^ (1 - β) :=
        mul_le_mul_of_nonneg_left hd' hpos
    _ ≤ L ^ β * L ^ β * (L - ℓ) ^ (1 - β) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmonoβ (Real.rpow_nonneg hL _))
          (Real.rpow_nonneg (sub_nonneg.mpr hℓL) _)

/-- **The pointwise defect.** With `S = Aℓ^β + O(G₁)`, `R = Bℓ + O(G₂)`, `S_N = cL^β + O(G₃)`,
`H = L + O(1)` and `Aδ = cB`:
`|δ H S − S_N R| ≤ cB (L ℓ^β − ℓ L^β) + (cB + 2G₁ + cG₂ + G₃B + G₃G₂) L`. -/
theorem abs_defect_le {A B c δ L ℓ β S R SN H G₁ G₂ G₃ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ L) (hL1 : 1 ≤ L) (hc : 0 ≤ c) (hB : 0 ≤ B) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hAδ : A * δ = c * B) (hS : |S - A * ℓ ^ β| ≤ G₁) (hR : |R - B * ℓ| ≤ G₂)
    (hSN : |SN - c * L ^ β| ≤ G₃) (hH : |H - L| ≤ 1) :
    |δ * H * S - SN * R| ≤ c * B * (L * ℓ ^ β - ℓ * L ^ β) +
      (c * B + 2 * G₁ + c * G₂ + G₃ * B + G₃ * G₂) * L := by
  have hG₁ : 0 ≤ G₁ := (abs_nonneg _).trans hS
  have hG₂ : 0 ≤ G₂ := (abs_nonneg _).trans hR
  have hG₃ : 0 ≤ G₃ := (abs_nonneg _).trans hSN
  set e₁ := S - A * ℓ ^ β
  set e₂ := R - B * ℓ
  set e₃ := SN - c * L ^ β
  set e₄ := H - L
  have hLβ : L ^ β ≤ L := by
    calc L ^ β ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 hβ1
      _ = L := Real.rpow_one L
  have hℓβ : ℓ ^ β ≤ L ^ β := Real.rpow_le_rpow hℓ0 hℓL hβ0.le
  have hℓβ0 : 0 ≤ ℓ ^ β := Real.rpow_nonneg hℓ0 _
  have hLβ0 : 0 ≤ L ^ β := Real.rpow_nonneg (by linarith) _
  have e : δ * H * S - SN * R = c * B * (L * ℓ ^ β - ℓ * L ^ β) + c * B * e₄ * ℓ ^ β +
      δ * (L + e₄) * e₁ - c * L ^ β * e₂ - e₃ * (B * ℓ + e₂) := by
    have hSdef : S = A * ℓ ^ β + e₁ := by simp only [e₁]; ring
    have hRdef : R = B * ℓ + e₂ := by simp only [e₂]; ring
    have hSNdef : SN = c * L ^ β + e₃ := by simp only [e₃]; ring
    have hHdef : H = L + e₄ := by simp only [e₄]; ring
    rw [hSdef, hRdef, hSNdef, hHdef]
    have : δ * (L + e₄) * (A * ℓ ^ β) = (A * δ) * (L + e₄) * ℓ ^ β := by ring
    rw [show δ * (L + e₄) * (A * ℓ ^ β + e₁) = (A * δ) * (L + e₄) * ℓ ^ β + δ * (L + e₄) * e₁ by
      ring, hAδ]
    ring
  rw [e]
  have h1 : |c * B * e₄ * ℓ ^ β| ≤ c * B * L := by
    rw [abs_mul, abs_mul, abs_of_nonneg (mul_nonneg hc hB), abs_of_nonneg hℓβ0]
    have := mul_le_mul hH (hℓβ.trans hLβ) hℓβ0 zero_le_one
    nlinarith [mul_nonneg hc hB]
  have h2 : |δ * (L + e₄) * e₁| ≤ 2 * G₁ * L := by
    rw [abs_mul, abs_mul, abs_of_nonneg hδ0]
    have hLe : |L + e₄| ≤ 2 * L := by
      have := abs_add_le L e₄; rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ L)] at this; linarith
    have := mul_le_mul hLe hS (abs_nonneg _) (by linarith)
    calc δ * |L + e₄| * |e₁| = δ * (|L + e₄| * |e₁|) := by ring
      _ ≤ 1 * (|L + e₄| * |e₁|) := mul_le_mul_of_nonneg_right hδ1 (by positivity)
      _ ≤ 2 * G₁ * L := by linarith
  have h3 : |c * L ^ β * e₂| ≤ c * G₂ * L := by
    rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hLβ0]
    have := mul_le_mul hLβ hR (abs_nonneg _) (by linarith)
    nlinarith
  have h4 : |e₃ * (B * ℓ + e₂)| ≤ (G₃ * B + G₃ * G₂) * L := by
    rw [abs_mul]
    have hBe : |B * ℓ + e₂| ≤ B * L + G₂ := by
      refine (abs_add_le _ _).trans (add_le_add ?_ hR)
      rw [abs_of_nonneg (mul_nonneg hB hℓ0)]; exact mul_le_mul_of_nonneg_left hℓL hB
    have := mul_le_mul hSN hBe (abs_nonneg _) hG₃
    nlinarith [mul_le_mul_of_nonneg_left hL1 (mul_nonneg hG₃ hG₂)]
  have hmain : 0 ≤ c * B * (L * ℓ ^ β - ℓ * L ^ β) := by
    refine mul_nonneg (mul_nonneg hc hB) ?_
    have := mul_rpow_sub_le hβ0 hβ1 hℓ0 hℓL
    -- `Lℓ^β ≥ ℓL^β` since `ℓ^{β−1} ≥ L^{β−1}`
    rcases hℓ0.eq_or_lt with rfl | hℓ
    · simp [Real.zero_rpow hβ0.ne']
    have hL0 : 0 < L := by linarith
    have eL : L ^ β = L * L ^ (β - 1) := by
      rw [show β = 1 + (β - 1) by ring, Real.rpow_add hL0, Real.rpow_one]; ring_nf
    have eℓ : ℓ ^ β = ℓ * ℓ ^ (β - 1) := by
      rw [show β = 1 + (β - 1) by ring, Real.rpow_add hℓ, Real.rpow_one]; ring_nf
    have hmono : L ^ (β - 1) ≤ ℓ ^ (β - 1) :=
      Real.rpow_le_rpow_of_nonpos hℓ hℓL (by linarith)
    rw [eL, eℓ]
    nlinarith [mul_le_mul_of_nonneg_left hmono (mul_nonneg hL0.le hℓ.le)]
  calc _ ≤ |c * B * (L * ℓ ^ β - ℓ * L ^ β)| + |c * B * e₄ * ℓ ^ β| + |δ * (L + e₄) * e₁| +
        |c * L ^ β * e₂| + |e₃ * (B * ℓ + e₂)| := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ c * B * (L * ℓ ^ β - ℓ * L ^ β) + c * B * L + 2 * G₁ * L + c * G₂ * L +
        (G₃ * B + G₃ * G₂) * L := by
        rw [abs_of_nonneg hmain]; linarith
    _ = _ := by ring

/-- The Euler density of the flipped primes below `T`, `δ_T = Π_{p<T}(1 − 1/p)/(1 − ω(p)/p)`. -/
def flipDensityBelow (ω : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesBelow T, (1 - 1 / (p : ℝ)) / (1 - ω p / p)

theorem flipDensityBelow_pos_le_one {ω : ℕ → ℝ} (hbd : ∀ n, |ω n| ≤ 1) (T : ℕ) :
    0 < flipDensityBelow ω T ∧ flipDensityBelow ω T ≤ 1 := by
  have hfac : ∀ p ∈ Nat.primesBelow T, 0 < (1 - 1 / (p : ℝ)) / (1 - ω p / p) ∧
      (1 - 1 / (p : ℝ)) / (1 - ω p / p) ≤ 1 := by
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hω := abs_le.mp (hbd p)
    have h1 : 0 < 1 - 1 / (p : ℝ) := by
      have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      linarith
    have h2 : 1 - 1 / (p : ℝ) ≤ 1 - ω p / p := by
      have : ω p / p ≤ 1 / p := div_le_div_of_nonneg_right hω.2 (by linarith)
      linarith
    exact ⟨div_pos h1 (h1.trans_le h2), (div_le_one (h1.trans_le h2)).mpr h2⟩
  exact ⟨prod_pos fun p hp => (hfac p hp).1,
    prod_le_one (fun p hp => (hfac p hp).1.le) fun p hp => (hfac p hp).2⟩

/-- `c Π(1 − ω(p)/p) · δ_T = c Π(1 − 1/p)`. -/
theorem mul_flipDensityBelow {ω : ℕ → ℝ} (hbd : ∀ n, |ω n| ≤ 1) (c : ℝ) (T : ℕ) :
    c * (∏ p ∈ Nat.primesBelow T, (1 - ω p / p)) * flipDensityBelow ω T =
      c * ∏ p ∈ Nat.primesBelow T, (1 - 1 / (p : ℝ)) := by
  unfold flipDensityBelow
  rw [mul_assoc, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun p hp => ?_
  have hpp := (Nat.mem_primesBelow.mp hp).2
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hpos : 0 < 1 - ω p / p := by
    have : ω p / p ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [(abs_le.mp (hbd p)).2]
    linarith
  rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hpos.ne', mul_one]

theorem log_le_harmonic (Y : ℕ) : Real.log Y ≤ gaugeHarmonicSum (fun _ => (1 : ℝ)) Y := by
  have h := log_add_one_le_harmonic Y
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  unfold gaugeHarmonicSum
  simp only [one_div] at h ⊢
  rcases Nat.eq_zero_or_pos Y with rfl | hY
  · simp
  · exact (Real.log_le_log (by exact_mod_cast hY) (by linarith)).trans h

theorem absHarmonic_le_harmonic {ω : ℕ → ℝ} (hbd : ∀ n, |ω n| ≤ 1) (N : ℕ) :
    absHarmonic ω N ≤ gaugeHarmonicSum (fun _ => (1 : ℝ)) N := by
  unfold absHarmonic gaugeHarmonicSum
  exact sum_le_sum fun m _ => div_le_div_of_nonneg_right (hbd m) (Nat.cast_nonneg m)

/-- **Low-fibre geometry.** If `log a ≤ ηL` with `L = log N`, `η ≤ 1/4`, `log 2 ≤ ηL`, then
`Y = ⌊N/a⌋` satisfies `1 ≤ Y ≤ N`, `L − log Y ≤ 2ηL` and `L/2 ≤ log Y`. -/
theorem lowFibre_log_bounds {N a : ℕ} (ha1 : 1 ≤ a) (hN : 1 ≤ N) {η : ℝ} (hη4 : η ≤ 1 / 4)
    (hLη : Real.log 2 ≤ η * Real.log N) (hla : Real.log a ≤ η * Real.log N) :
    1 ≤ N / a ∧ ((N / a : ℕ) : ℝ) ≤ N ∧
      Real.log N - Real.log ((N / a : ℕ) : ℝ) ≤ 2 * η * Real.log N ∧
      Real.log N / 2 ≤ Real.log ((N / a : ℕ) : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hηL : η * Real.log N ≤ Real.log N / 4 := by nlinarith
  -- `2a ≤ N`
  have haN2 : 2 * (a : ℝ) ≤ N := by
    have h := Real.exp_le_exp.mpr (show Real.log a ≤ Real.log N - Real.log 2 by linarith)
    rw [Real.exp_log ha0, Real.exp_sub, Real.exp_log hN0, Real.exp_log (by norm_num)] at h
    rw [le_div_iff₀ (by norm_num)] at h; linarith
  have haN : a ≤ N := by exact_mod_cast (show (a : ℝ) ≤ N by linarith)
  have hY1 : 1 ≤ N / a := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hY0 : (0 : ℝ) < ((N / a : ℕ) : ℝ) := by exact_mod_cast hY1
  have hYN : ((N / a : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N a
  have hYlow : (N : ℝ) / (2 * a) ≤ ((N / a : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add (a := N) (b := a) (by omega)
    have h' : (N : ℝ) < (((N / a : ℕ) : ℝ) + 1) * a := by
      have : N < (N / a + 1) * a := by rw [add_mul, one_mul]; simpa using h
      exact_mod_cast this
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h := Real.log_le_log (by positivity) hYlow
  rw [Real.log_div hN0.ne' (by positivity), Real.log_mul (by norm_num) ha0.ne'] at h
  refine ⟨hY1, hYN, by linarith, by linarith⟩

/-- **The low-fibre defect bound** (real form): with the asymptotics of `S, R, S_N, H` at
`ℓ ≤ L`, `L − ℓ ≤ 2ηL`, `cB(2η)^{2κ} ≤ θ/2` and `K₀ ≤ (θ/2)L^β`, `|δ H S − S_N R| ≤ θ L L^β`. -/
theorem abs_defect_le_low {A B c δ L ℓ β κ η θ S R SN H G₁ G₂ G₀ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (h1β : 1 - β = 2 * κ) (hκ0 : 0 < κ) (hη0 : 0 < η) (hℓ0 : 0 ≤ ℓ)
    (hℓL : ℓ ≤ L) (hL1 : 1 ≤ L) (hLℓ : L - ℓ ≤ 2 * η * L) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hAδ : A * δ = c * B) (hS : |S - A * ℓ ^ β| ≤ G₁)
    (hR : |R - B * ℓ| ≤ G₂) (hSN : |SN - c * L ^ β| ≤ G₀) (hH : |H - L| ≤ 1)
    (hcBη : c * B * (2 * η) ^ (2 * κ) ≤ θ / 2)
    (hK₀ : c * B + 2 * G₁ + c * G₂ + G₀ * B + G₀ * G₂ ≤ θ / 2 * L ^ β) :
    |δ * H * S - SN * R| ≤ θ * L * L ^ β := by
  have hD := abs_defect_le hβ0 hβ1 hℓ0 hℓL hL1 hc hB hδ0 hδ1 hAδ hS hR hSN hH
  have hcore := mul_rpow_sub_le hβ0 hβ1 hℓ0 hℓL
  have hLβ0 : 0 ≤ L ^ β := Real.rpow_nonneg (by linarith) _
  have hpow : (L - ℓ) ^ (1 - β) ≤ (2 * η) ^ (2 * κ) * L ^ (2 * κ) := by
    rw [h1β, ← Real.mul_rpow (by linarith) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) hLℓ (by linarith)
  have hLL : L ^ β * L ^ (2 * κ) = L := by
    rw [← Real.rpow_add (by linarith), show β + 2 * κ = 1 by linarith, Real.rpow_one]
  have h1 : c * B * (L * ℓ ^ β - ℓ * L ^ β) ≤ c * B * (2 * η) ^ (2 * κ) * (L * L ^ β) := by
    have := mul_le_mul_of_nonneg_left hpow (mul_nonneg hLβ0 hLβ0)
    have e : L ^ β * L ^ β * ((2 * η) ^ (2 * κ) * L ^ (2 * κ)) =
        (2 * η) ^ (2 * κ) * (L * L ^ β) :=
      calc L ^ β * L ^ β * ((2 * η) ^ (2 * κ) * L ^ (2 * κ)) =
            (2 * η) ^ (2 * κ) * ((L ^ β * L ^ (2 * κ)) * L ^ β) := by ring
        _ = (2 * η) ^ (2 * κ) * (L * L ^ β) := by rw [hLL]
    rw [e] at this
    have h := mul_le_mul_of_nonneg_left (hcore.trans this) (mul_nonneg hc hB)
    linarith
  have h2 : c * B * (2 * η) ^ (2 * κ) * (L * L ^ β) ≤ θ / 2 * (L * L ^ β) :=
    mul_le_mul_of_nonneg_right hcBη (mul_nonneg (by linarith) hLβ0)
  have h3 : (c * B + 2 * G₁ + c * G₂ + G₀ * B + G₀ * G₂) * L ≤ θ / 2 * (L * L ^ β) := by
    have := mul_le_mul_of_nonneg_right hK₀ (show 0 ≤ L by linarith)
    linarith
  linarith

/-- `c₀ L/(2 log T) ≤ R` from `R ≥ c₀ log(Y + 1)/log T` and `log(Y + 1) ≥ L/2`. -/
theorem half_mul_div_le {c₀ L ℓ' lT R : ℝ} (hc₀ : 0 < c₀) (hlT : 0 < lT) (hℓ : L / 2 ≤ ℓ')
    (hR : c₀ * ℓ' / lT ≤ R) : c₀ * L / (2 * lT) ≤ R :=
  calc c₀ * L / (2 * lT) = c₀ * (L / 2) / lT := by ring
    _ ≤ c₀ * ℓ' / lT := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ hc₀.le) hlT.le
    _ ≤ R := hR

/-- A pointwise bound on `D²/(aR)` from `|D| ≤ θ L L^β` and `R ≥ c₀ L/(2 log T)`. -/
theorem sq_div_le_of_abs_le {D R a θ L Lb c₀ lT : ℝ} (ha : 0 < a) (hc₀ : 0 < c₀) (hlT : 0 < lT)
    (hL : 0 < L) (hD : |D| ≤ θ * L * Lb) (hR : c₀ * L / (2 * lT) ≤ R) :
    D ^ 2 / (a * R) ≤ 1 / a * (2 * lT / c₀ * θ ^ 2 * L * Lb ^ 2) := by
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hD2 : D ^ 2 ≤ (θ * L * Lb) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hD 2
  rw [div_le_iff₀ (mul_pos ha hR0)]
  have e : 1 / a * (2 * lT / c₀ * θ ^ 2 * L * Lb ^ 2) * (a * (c₀ * L / (2 * lT))) =
      (θ * L * Lb) ^ 2 := by field_simp
  calc D ^ 2 ≤ (θ * L * Lb) ^ 2 := hD2
    _ = 1 / a * (2 * lT / c₀ * θ ^ 2 * L * Lb ^ 2) * (a * (c₀ * L / (2 * lT))) := e.symm
    _ ≤ 1 / a * (2 * lT / c₀ * θ ^ 2 * L * Lb ^ 2) * (a * R) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR ha.le) (by positivity)

/-- The high-fibre bound: `(δHS − S_N R)²/(aR) ≤ 64 L³/a` from `|S| ≤ R ≤ 4L`, `1 ≤ R`,
`0 ≤ S_N ≤ H ≤ 2L`, `0 ≤ δ ≤ 1`. -/
theorem defect_sq_div_le_high {δ H S SN R a L : ℝ} (ha : 0 < a) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hH0 : 0 ≤ H) (hH2 : H ≤ 2 * L) (hSN0 : 0 ≤ SN) (hSNH : SN ≤ H) (hS : |S| ≤ R)
    (hR1 : 1 ≤ R) (hR4 : R ≤ 4 * L) :
    (δ * H * S - SN * R) ^ 2 / (a * R) ≤ 1 / a * (64 * L ^ 3) := by
  have hR0 : 0 < R := by linarith
  have hDabs : |δ * H * S - SN * R| ≤ 2 * H * R := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hδ0, abs_of_nonneg hH0, abs_of_nonneg hSN0,
      abs_of_pos hR0]
    have h1 : δ * H * |S| ≤ H * R :=
      calc δ * H * |S| ≤ 1 * H * R :=
            mul_le_mul (mul_le_mul_of_nonneg_right hδ1 hH0) hS (abs_nonneg _) (by positivity)
        _ = H * R := by ring
    nlinarith
  have hD2 : (δ * H * S - SN * R) ^ 2 ≤ (2 * H * R) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hDabs 2
  have hpoly : 4 * H ^ 2 * R ≤ 64 * L ^ 3 := by
    have hL0 : 0 ≤ L := by linarith
    have hH2' : H ^ 2 ≤ 4 * L ^ 2 := by nlinarith
    calc 4 * H ^ 2 * R ≤ 4 * (4 * L ^ 2) * (4 * L) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hH2' (by norm_num)) hR4 hR0.le (by positivity)
      _ = 64 * L ^ 3 := by ring
  rw [div_le_iff₀ (mul_pos ha hR0)]
  calc (δ * H * S - SN * R) ^ 2 ≤ (2 * H * R) ^ 2 := hD2
    _ = 1 / a * (4 * H ^ 2 * R) * (a * R) := by field_simp; ring
    _ ≤ 1 / a * (64 * L ^ 3) * (a * R) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by positivity))
          (by positivity)

/-- The errors of the fixed-scale defect at horizon `L = log N`: with `K₀ = cB + 2G₁ + cG₂ + G₀B + G₀G₂`
and `4K₀/θ ≤ L^{β−α}`, the power-weighted errors satisfy
`cB + 2G₁(1 + L)^α + cG₂ + G₀(1 + L)^α B + G₀(1 + L)^α G₂ ≤ (θ/2) L^β`. -/
theorem defect_error_le {c B G₁ G₂ G₀ θ L β α : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) (hG₁ : 0 ≤ G₁)
    (hG₂ : 0 ≤ G₂) (hG₀ : 0 ≤ G₀) (hθ : 0 < θ) (hL1 : 1 ≤ L) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hbig : 4 * (c * B + 2 * G₁ + c * G₂ + G₀ * B + G₀ * G₂) / θ ≤ L ^ (β - α)) :
    c * B + 2 * (G₁ * (1 + L) ^ α) + c * G₂ + G₀ * (1 + L) ^ α * B + G₀ * (1 + L) ^ α * G₂ ≤
      θ / 2 * L ^ β := by
  set K₀ := c * B + 2 * G₁ + c * G₂ + G₀ * B + G₀ * G₂
  set P := (1 + L) ^ α
  have hP1 : 1 ≤ P := Real.one_le_rpow (by linarith) hα
  have hP2 : P ≤ 2 * L ^ α := by
    calc P ≤ (2 * L) ^ α := Real.rpow_le_rpow (by linarith) (by linarith) hα
      _ = 2 ^ α * L ^ α := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 2 * L ^ α := mul_le_mul_of_nonneg_right
          (by calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
                _ = 2 := Real.rpow_one 2) (Real.rpow_nonneg (by linarith) _)
  have hK₀0 : 0 ≤ K₀ := by positivity
  have h1 : c * B + 2 * (G₁ * P) + c * G₂ + G₀ * P * B + G₀ * P * G₂ ≤ K₀ * P := by
    have hcB : c * B ≤ c * B * P := le_mul_of_one_le_right (mul_nonneg hc hB) hP1
    have hcG : c * G₂ ≤ c * G₂ * P := le_mul_of_one_le_right (mul_nonneg hc hG₂) hP1
    have e : K₀ * P = c * B * P + 2 * (G₁ * P) + c * G₂ * P + G₀ * P * B + G₀ * P * G₂ := by
      simp only [K₀]; ring
    linarith
  have h2 : K₀ * P ≤ 2 * K₀ * L ^ α := by
    calc K₀ * P ≤ K₀ * (2 * L ^ α) := mul_le_mul_of_nonneg_left hP2 hK₀0
      _ = 2 * K₀ * L ^ α := by ring
  have hsplit : L ^ β = L ^ α * L ^ (β - α) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  have hLα0 : 0 ≤ L ^ α := Real.rpow_nonneg (by linarith) _
  rw [div_le_iff₀ hθ] at hbig
  have h4 : 2 * K₀ * L ^ α ≤ θ / 2 * L ^ β := by
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left hbig hLα0
    calc 2 * K₀ * L ^ α = (4 * K₀) * L ^ α / 2 := by ring
      _ ≤ (L ^ (β - α) * θ) * L ^ α / 2 := by
          have := mul_le_mul_of_nonneg_right hbig hLα0; linarith
      _ = θ / 2 * (L ^ α * L ^ (β - α)) := by ring
  linarith

/-- **The fixed-scale defect.** For a flip twin of relative log density `κ ∈ (0, 1/2)` and fixed
`T ≥ 3`, with `δ_T` the Euler density of the flipped primes below `T`,
`Σ_{a ≤ N, T-smooth} (δ_T H_N S_T(N/a) − S_N F_T(N/a))²/(a F_T(N/a)) ≤ ε δ_T² H_N S_N²` eventually.
Equivalently, the `T`-rough means `S_T/F_T` on the fibres equal `c_N/δ_T` up to `o(c_N)` in the
harmonic `L²` sense. -/
theorem eventually_fixedScaleDefect_le (P : Set ℕ) {κ C α : ℝ} (hκ0 : 0 < κ) (hα : 0 ≤ α)
    (hακ : α < 1 - 2 * κ)
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C * (1 + Real.log n) ^ α)
    {T : ℕ} (hT : 3 ≤ T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      ∑ a ∈ smoothSet T N, (flipDensityBelow (primeSetFlip P) T *
          gaugeHarmonicSum (fun _ => (1 : ℝ)) N *
            gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
          gaugeHarmonicSum (primeSetFlip P) N * roughHarmonic T (N / a)) ^ 2 /
        (a * roughHarmonic T (N / a)) ≤
      ε * flipDensityBelow (primeSetFlip P) T ^ 2 * gaugeHarmonicSum (fun _ => (1 : ℝ)) N *
        gaugeHarmonicSum (primeSetFlip P) N ^ 2 := by
  set ω := primeSetFlip P
  set β := 1 - 2 * κ with hβdef
  have hβ0 : 0 < β := by linarith
  have hβ1 : β ≤ 1 := by linarith
  have hαβ : α < β := hακ
  have hα1 : α ≤ 1 := by linarith
  have h1β : 1 - β = 2 * κ := by ring
  have hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b :=
    fun a b ha hb => (primeSetFlip_isSignGauge P).mul ha hb
  have hbd : ∀ n, |ω n| ≤ 1 := abs_primeSetFlip_le P
  have hlT : 1 ≤ Real.log T := one_le_log_of_three_le hT
  -- the global asymptotic with positive constant, extended to all `Y`
  obtain ⟨c, G₃, hc, hcG⟩ :=
    exists_pos_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le P hκ0.le hα hακ hP
  set G₀ := max |G₃| (2 + c)
  have hP1 : ∀ Y : ℕ, 1 ≤ (1 + Real.log Y) ^ α := fun Y =>
    Real.one_le_rpow (by linarith [Real.log_natCast_nonneg Y]) hα
  have hlog1 : ∀ Y : ℕ, Real.log Y ^ α ≤ (1 + Real.log Y) ^ α := fun Y =>
    Real.rpow_le_rpow (Real.log_natCast_nonneg Y) (by linarith) hα
  have hG₀0 : 0 ≤ G₀ := (abs_nonneg _).trans (le_max_left _ _)
  have hSall : ∀ Y : ℕ, |gaugeHarmonicSum ω Y - c * Real.log Y ^ β| ≤
      G₀ * (1 + Real.log Y) ^ α := by
    intro Y
    rcases lt_or_ge Y 3 with hY | hY
    · have hb := abs_gaugeHarmonicSum_le ω hbd Y
      have hlY : Real.log Y ≤ 1 := by
        rcases Nat.eq_zero_or_pos Y with rfl | hY0
        · simp
        · rw [Real.log_le_iff_le_exp (by exact_mod_cast hY0)]
          have : (Y : ℝ) ≤ 2 := by exact_mod_cast (show Y ≤ 2 by omega)
          linarith [Real.add_one_le_exp (1 : ℝ)]
      have hp0 : 0 ≤ Real.log Y ^ β := Real.rpow_nonneg (Real.log_natCast_nonneg Y) _
      have hp1 : Real.log Y ^ β ≤ 1 := Real.rpow_le_one (Real.log_natCast_nonneg Y) hlY hβ0.le
      have := le_max_right |G₃| (2 + c)
      have hGP := le_mul_of_one_le_right hG₀0 (hP1 Y)
      rw [abs_le] at hb ⊢
      constructor <;> nlinarith
    · refine (hcG Y hY).trans ?_
      exact mul_le_mul ((le_abs_self G₃).trans (le_max_left _ _)) (hlog1 Y)
        (Real.rpow_nonneg (Real.log_natCast_nonneg Y) _) hG₀0
  obtain ⟨G₁, hG₁⟩ := exists_abs_roughSum_sub_le hmul hbd hβ0 hβ1 hα hSall T
  obtain ⟨G₂, hG₂⟩ := exists_abs_roughHarmonic_sub_le T
  set A := c * ∏ p ∈ Nat.primesBelow T, (1 - ω p / p)
  set B := ∏ p ∈ Nat.primesBelow T, (1 - 1 / (p : ℝ))
  set δ := flipDensityBelow ω T
  obtain ⟨hδ0, hδ1⟩ := flipDensityBelow_pos_le_one hbd T
  have hAδ : A * δ = c * B := mul_flipDensityBelow hbd c T
  have hB0 : 0 ≤ B := prod_nonneg fun p hp => by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hG₀ : 0 ≤ G₀ := hG₀0
  have hG₁0 : 0 ≤ G₁ := by simpa using (abs_nonneg _).trans (hG₁ 0)
  have hG₂0 : 0 ≤ G₂ := (abs_nonneg _).trans (hG₂ 0)
  set K₀ := c * B + 2 * G₁ + c * G₂ + G₀ * B + G₀ * G₂
  obtain ⟨c₀, hc₀, hR⟩ := exists_roughHarmonic_ge
  obtain ⟨Ks, hKs, hsm⟩ := exists_sum_smoothSet_inv_le
  obtain ⟨KR, hKR, htail⟩ := exists_sum_smoothSet_tail_le T
  obtain ⟨c', hc', N₂, hN₂⟩ :=
    exists_pos_mul_rpow_le_gaugeHarmonicSum_primeSetFlip P hκ0.le hα hακ hP
  -- the low-fibre tolerance `θ` and the cutoff exponent `η`
  set θ := Real.sqrt (ε * δ ^ 2 * c' ^ 2 * c₀ / (4 * Ks * Real.log T ^ 2))
  have hθ0 : 0 < θ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ ^ 2 = ε * δ ^ 2 * c' ^ 2 * c₀ / (4 * Ks * Real.log T ^ 2) :=
    Real.sq_sqrt (by positivity)
  set t := θ / (2 * (c * B + 1))
  have ht0 : 0 < t := by positivity
  set η := min (1 / 4) (t ^ (1 / (2 * κ)) / 2)
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη4 : η ≤ 1 / 4 := min_le_left _ _
  have hηt : (2 * η) ^ (2 * κ) ≤ t := by
    have h2η : 2 * η ≤ t ^ (1 / (2 * κ)) := by
      have := min_le_right (1 / 4 : ℝ) (t ^ (1 / (2 * κ)) / 2); linarith
    calc (2 * η) ^ (2 * κ) ≤ (t ^ (1 / (2 * κ))) ^ (2 * κ) :=
          Real.rpow_le_rpow (by linarith) h2η (by linarith)
      _ = t := by
          rw [← Real.rpow_mul ht0.le, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
  have hcBη : c * B * (2 * η) ^ (2 * κ) ≤ θ / 2 := by
    have hcB : 0 ≤ c * B := mul_nonneg hc.le hB0
    have e : c * B * t = θ / 2 * (c * B / (c * B + 1)) := by simp only [t]; field_simp
    have hfrac : c * B / (c * B + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    calc c * B * (2 * η) ^ (2 * κ) ≤ c * B * t := mul_le_mul_of_nonneg_left hηt hcB
      _ = θ / 2 * (c * B / (c * B + 1)) := e
      _ ≤ θ / 2 * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = θ / 2 := mul_one _
  -- eventual size conditions on `L = log N`
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLβ : Tendsto (fun N : ℕ => Real.log N ^ (β - α)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hL
  have hexp : Tendsto (fun N : ℕ => Real.log N ^ 3 * Real.exp (-(η * Real.log N / 2))) atTop
      (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp
      ((tendsto_id.const_mul_atTop (show 0 < η / 2 by positivity)).comp hL)
    have h' := h.const_mul ((2 / η) ^ 3)
    rw [mul_zero] at h'
    refine h'.congr fun N => ?_
    simp only [Function.comp_apply, id]
    field_simp
  have hsmallT : 0 < ε * δ ^ 2 * c' ^ 2 / 2 / (64 * KR + 1) := by positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_ge_atTop (max 3 N₂)).and
    ((hL.eventually_ge_atTop (max (Real.log 2 / η) (max (2 * Real.log 2) 1))).and
      ((hLβ.eventually_ge_atTop (4 * K₀ / θ)).and
        (hexp.eventually (ge_mem_nhds hsmallT)))))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hN3, hLbig, hLβbig, hexpN⟩ := hN₀ N hN
  have hN3' : 3 ≤ N := (le_max_left _ _).trans hN3
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLbig)
  have hLη : Real.log 2 ≤ η * L := by
    have := (le_max_left _ _).trans hLbig
    rwa [div_le_iff₀ hη0, mul_comm] at this
  set Pα := (1 + L) ^ α
  have hK₀L := defect_error_le hc.le hB0 hG₁0 hG₂0 hG₀ hθ0 hL1 hα hα1 hLβbig
  set SN := gaugeHarmonicSum ω N
  set H := gaugeHarmonicSum (fun _ => (1 : ℝ)) N
  have hH := abs_harmonic_sub_log_le N
  have hHL : L ≤ H := log_le_harmonic N
  have hHu : H ≤ 1 + L := by have := (abs_le.mp hH).2; linarith
  have hSNlow : c' * L ^ β ≤ SN := hN₂ N ((le_max_right _ _).trans hN3)
  have hLβ0 : 0 ≤ L ^ β := Real.rpow_nonneg (by linarith) _
  have hSN0 : 0 ≤ SN := (mul_nonneg hc'.le hLβ0).trans hSNlow
  have hSNH : SN ≤ H :=
    (le_abs_self SN).trans ((abs_gaugeHarmonicSum_le_absHarmonic ω N).trans
      (absHarmonic_le_harmonic hbd N))
  have hSN' : |SN - c * L ^ β| ≤ G₀ * Pα :=
    (hcG N hN3').trans (mul_le_mul ((le_abs_self G₃).trans (le_max_left _ _)) (hlog1 N)
      (Real.rpow_nonneg (by linarith) _) hG₀0)
  -- the target is at least `ε δ² c'² L (L^β)²`
  have htarget : ε * δ ^ 2 * c' ^ 2 * L * (L ^ β) ^ 2 ≤ ε * δ ^ 2 * H * SN ^ 2 := by
    have h1 : c' ^ 2 * (L ^ β) ^ 2 ≤ SN ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (mul_nonneg hc'.le hLβ0) hSNlow 2
    have h2 : L * (c' ^ 2 * (L ^ β) ^ 2) ≤ H * SN ^ 2 :=
      mul_le_mul hHL h1 (by positivity) (by linarith)
    have hεδ : 0 ≤ ε * δ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left h2 hεδ
    linarith
  rw [← sum_filter_add_sum_filter_not (smoothSet T N) (fun a : ℕ => Real.log a ≤ η * L)]
  -- low fibres
  have hlow : ∀ a ∈ (smoothSet T N).filter (fun a : ℕ => Real.log a ≤ η * L),
      (δ * H * gaugeHarmonicSum (roughGauge T ω) (N / a) - SN * roughHarmonic T (N / a)) ^ 2 /
        (a * roughHarmonic T (N / a)) ≤
        1 / a * (2 * Real.log T / c₀ * θ ^ 2 * L * (L ^ β) ^ 2) := by
    intro a ha
    obtain ⟨ha1, -, -⟩ := mem_smoothSet.mp (mem_filter.mp ha).1
    obtain ⟨hY1, hYN, hLℓ, hℓhalf⟩ :=
      lowFibre_log_bounds ha1 (by omega) hη4 hLη (mem_filter.mp ha).2
    have hY0 : (0 : ℝ) < ((N / a : ℕ) : ℝ) := by exact_mod_cast hY1
    have hℓL : Real.log ((N / a : ℕ) : ℝ) ≤ L :=
      Real.log_le_log hY0 hYN
    have hG₁a : |gaugeHarmonicSum (roughGauge T ω) (N / a) - A * Real.log ((N / a : ℕ) : ℝ) ^ β| ≤
        G₁ * Pα := (hG₁ (N / a)).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith [Real.log_natCast_nonneg (N / a)]) (by linarith) hα) hG₁0)
    have hD := abs_defect_le_low hβ0 hβ1 h1β hκ0 hη0 (Real.log_natCast_nonneg _) hℓL hL1 hLℓ
      hc.le hB0 hδ0.le hδ1 hAδ hG₁a (hG₂ (N / a)) hSN' hH hcBη hK₀L
    have hlY : Real.log ((N / a : ℕ) : ℝ) ≤ Real.log (((N / a : ℕ) : ℝ) + 1) :=
      Real.log_le_log hY0 (lt_add_one _).le
    have hRY : c₀ * L / (2 * Real.log T) ≤ roughHarmonic T (N / a) :=
      half_mul_div_le hc₀ (lt_of_lt_of_le one_pos hlT) (hℓhalf.trans hlY) (hR T hT (N / a))
    exact sq_div_le_of_abs_le (by exact_mod_cast ha1) hc₀ (lt_of_lt_of_le one_pos hlT)
      (lt_of_lt_of_le one_pos hL1) hD hRY
  -- high fibres
  have hhigh : ∀ a ∈ (smoothSet T N).filter (fun a : ℕ => ¬ Real.log a ≤ η * L),
      (δ * H * gaugeHarmonicSum (roughGauge T ω) (N / a) - SN * roughHarmonic T (N / a)) ^ 2 /
        (a * roughHarmonic T (N / a)) ≤ 1 / a * (64 * L ^ 3) := by
    intro a ha
    obtain ⟨ha1, haN, -⟩ := mem_smoothSet.mp (mem_filter.mp ha).1
    have hY1 : 1 ≤ N / a := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hRN : roughHarmonic T (N / a) ≤ 4 * L := by
      have h := (RenormalizedArithmeticPotentialTheory.roughHarmonic_mono
        (Nat.div_le_self N a)).trans (roughHarmonic_le_one_add_div_log (Q := T) (by omega) N)
      have : (1 + 2 * L) / Real.log T ≤ 1 + 2 * L :=
        div_le_self (by linarith only [hL1]) hlT
      linarith only [h, this, hL1]
    exact defect_sq_div_le_high (by exact_mod_cast ha1) hδ0.le hδ1
      (zero_le_one.trans (hL1.trans hHL)) (by linarith only [hHu, hL1])
      hSN0 hSNH ((abs_gaugeHarmonicSum_le_absHarmonic _ _).trans (absHarmonic_roughGauge_le hbd T _))
      (RenormalizedArithmeticPotentialTheory.one_le_roughHarmonic T hY1) hRN
  -- sum the two fibre classes
  have hlowsum : ∑ a ∈ (smoothSet T N).filter (fun a : ℕ => Real.log a ≤ η * L),
      (δ * H * gaugeHarmonicSum (roughGauge T ω) (N / a) - SN * roughHarmonic T (N / a)) ^ 2 /
        (a * roughHarmonic T (N / a)) ≤ ε * δ ^ 2 * c' ^ 2 * L * (L ^ β) ^ 2 / 2 := by
    refine (sum_le_sum hlow).trans ?_
    rw [← sum_mul]
    have hS : ∑ a ∈ (smoothSet T N).filter (fun a : ℕ => Real.log a ≤ η * L), (1 : ℝ) / a ≤
        Ks * Real.log T :=
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity).trans
        (hsm T hT N)
    have e : Ks * Real.log T * (2 * Real.log T / c₀ * θ ^ 2 * L * (L ^ β) ^ 2) =
        ε * δ ^ 2 * c' ^ 2 * L * (L ^ β) ^ 2 / 2 := by
      have h1 : Ks ≠ 0 := hKs.ne'
      have h2 : c₀ ≠ 0 := hc₀.ne'
      have h3 : Real.log T ≠ 0 := (lt_of_lt_of_le one_pos hlT).ne'
      rw [hθsq]; field_simp; ring
    calc _ ≤ Ks * Real.log T * (2 * Real.log T / c₀ * θ ^ 2 * L * (L ^ β) ^ 2) :=
          mul_le_mul_of_nonneg_right hS (by positivity)
      _ = _ := e
  have hhighsum : ∑ a ∈ (smoothSet T N).filter (fun a : ℕ => ¬ Real.log a ≤ η * L),
      (δ * H * gaugeHarmonicSum (roughGauge T ω) (N / a) - SN * roughHarmonic T (N / a)) ^ 2 /
        (a * roughHarmonic T (N / a)) ≤ ε * δ ^ 2 * c' ^ 2 * L * (L ^ β) ^ 2 / 2 := by
    refine (sum_le_sum hhigh).trans ?_
    rw [← sum_mul]
    set X := Real.exp (η * L)
    have hX : 0 < X := Real.exp_pos _
    have hsub : (smoothSet T N).filter (fun a : ℕ => ¬ Real.log a ≤ η * L) ⊆
        (smoothSet T N).filter (fun a : ℕ => X < (a : ℝ)) := by
      intro a ha
      obtain ⟨ha', hla⟩ := mem_filter.mp ha
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_smoothSet.mp ha').1
      refine mem_filter.mpr ⟨ha', ?_⟩
      rw [not_le] at hla
      calc X = Real.exp (η * L) := rfl
        _ < Real.exp (Real.log a) := Real.exp_lt_exp.mpr hla
        _ = a := Real.exp_log ha0
    have hsqrt : Real.sqrt X = Real.exp (η * L / 2) := by
      have hX2 : X = Real.exp (η * L / 2) * Real.exp (η * L / 2) := by
        rw [← Real.exp_add, add_halves]
      rw [hX2, Real.sqrt_mul_self (Real.exp_pos _).le]
    have hS : ∑ a ∈ (smoothSet T N).filter (fun a : ℕ => ¬ Real.log a ≤ η * L), (1 : ℝ) / a ≤
        KR * Real.exp (-(η * L / 2)) := by
      refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
      refine (htail N X hX).trans (le_of_eq ?_)
      rw [hsqrt, Real.exp_neg, div_eq_mul_inv]
    have hLL : 1 ≤ L * (L ^ β) ^ 2 :=
      one_le_mul_of_one_le_of_one_le hL1 (one_le_pow₀ (Real.one_le_rpow hL1 hβ0.le))
    have h0 : 0 ≤ ε * δ ^ 2 * c' ^ 2 / 2 := by positivity
    calc _ ≤ KR * Real.exp (-(η * L / 2)) * (64 * L ^ 3) :=
          mul_le_mul_of_nonneg_right hS (by positivity)
      _ = 64 * KR * (L ^ 3 * Real.exp (-(η * L / 2))) := by ring
      _ ≤ (64 * KR + 1) * (ε * δ ^ 2 * c' ^ 2 / 2 / (64 * KR + 1)) :=
          mul_le_mul (le_add_of_nonneg_right zero_le_one) hexpN (by positivity) (by positivity)
      _ = ε * δ ^ 2 * c' ^ 2 / 2 * 1 := by field_simp
      _ ≤ ε * δ ^ 2 * c' ^ 2 / 2 * (L * (L ^ β) ^ 2) := mul_le_mul_of_nonneg_left hLL h0
      _ = ε * δ ^ 2 * c' ^ 2 * L * (L ^ β) ^ 2 / 2 := by ring
  linarith only [hlowsum, hhighsum, htarget]

end Defect

end GaloisForLFunctions.RenormalizedIntersectionTheory
