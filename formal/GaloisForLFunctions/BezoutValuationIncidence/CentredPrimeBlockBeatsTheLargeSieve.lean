import GaloisForLFunctions.BezoutValuationIncidence.MoebiusBlockBeatsTheTypeTwoBarrier
import GaloisForLFunctions.BezoutValuationIncidence.CentredPrimeRowPassesTheCoherentBlockObstruction
import GaloisForLFunctions.HTGeometry.FarBandPowerTail

/-!
# The centred prime block beats the large sieve

The short-window transfer law bounds the cross-scale remainder of a large-scale row by its
`H`-window average `x̄`, up to a loss `√(H/P)`. Every window average of a row bounded by `B` whose
windows inside the block `(Q, 2Q]` sum to at most `G` satisfies

`Σ_n x̄(n)² ≤ Q (G/H)² + 2H B²`,

the `2H` windows across the block ends taken trivially. For the centred prime block
`c'(n) = (Λ(n) - 1)·𝟙_{(Q, 2Q]}`, `x = c'/n²`, Huxley's prime number theorem in all windows of length
`H = ⌈(2Q)^α⌉`, `7/12 < α < 1`, gives `G = 2εH/Q²` (`abs_sum_block_le_of_window`), and `B = (log 2Q + 1)/Q²`,
so `Σ_n x̄(n)² ≤ ε²/Q³` for large `Q`. Hence, for every `ε > 0` and all large `Q`, every row `c` on
primes `p ≤ Q₀` with `8H (log 2Q + 1)² ≤ ε² p` satisfies

`|B + m R' + β H'| ≤ ε √(Σ c(p)² p²) √(Q + 2Q₀²) Q^{-3/2}
  + |Σ_{Q<n≤2Q} (Λ(n) - 1)/n²| Σ_p |c(p)|/(6p) + ¾ Σ_d |c(d)| d² Σ_n |c'(n)|/n³`.

The threshold is `p ≥ Q^{α+o(1)}`, so at `α < 3/5` this covers the whole balanced regime
`P ≤ Q < P^{5/3}`. Against the rank-two bound (`exists_abs_rowBilinear_centredPrimeRow_le`) the
gain is the large-sieve factor `(P/Q)^{1/2}` on top of `ε`; against the large-sieve size
`√(log Q) Q^{-3/2}` of the prime block the first term is `ε/√(log Q)` of it. The omitted residue
class of the prime row (`tendsto_mul_kernelStatistic_primeWindowRow`) sits inside these terms: its
dual-norm size `P/Q` is `o` of the large-sieve size `P^{5/2} Q^{-3/2}` once `P ≥ Q^{1/3+δ}`.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open ArithmeticFunction (vonMangoldt)
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Window averages from window bounds -/

/-- **Window averages from window bounds.** If `|x| ≤ B` and every window `(t, t + H]` with
`Q ≤ t`, `t + H < 2Q` sums to at most `G`, then `Σ_{Q<n≤2Q+H} x̄(n)² ≤ Q (G/H)² + 2H B²`. -/
theorem sum_sq_shortWindowAverage_le_of_window {Q H : ℕ} (hH : 1 ≤ H) (hHQ : H ≤ Q)
    {x : ℕ → ℝ} {B G : ℝ} (hB : ∀ m, |x m| ≤ B)
    (hG : ∀ t, Q ≤ t → t + H < 2 * Q → |∑ m ∈ Ioc t (t + H), x m| ≤ G) :
    ∑ n ∈ Icc (Q + 1) (Q + Q + H), shortWindowAverage H x n ^ 2 ≤
      Q * (G / H) ^ 2 + 2 * H * B ^ 2 := by
  classical
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  set good : ℕ → Prop := fun t => Q ≤ t ∧ t + H < 2 * Q
  set F : ℕ → ℝ := fun t => if good t then (G / H) ^ 2 else B ^ 2
  have hpt : ∀ n ∈ Icc (Q + 1) (Q + Q + H), shortWindowAverage H x n ^ 2 ≤ F (n - H) := by
    intro n hn
    have hn' := mem_Icc.mp hn
    have hwin : shortWindowAverage H x n = (∑ m ∈ Ioc (n - H) (n - H + H), x m) / H := by
      rw [shortWindowAverage, sum_range_sub_eq_sum_Ioc x (by omega), Nat.sub_add_cancel (by omega)]
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    rw [hwin, div_pow, div_le_iff₀ hH2, ← sq_abs]
    simp only [F]
    split_ifs with hg
    · have h := hG (n - H) hg.1 hg.2
      calc |∑ m ∈ Ioc (n - H) (n - H + H), x m| ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = (G / H) ^ 2 * (H : ℝ) ^ 2 := by field_simp
    · have h : |∑ m ∈ Ioc (n - H) (n - H + H), x m| ≤ H * B := by
        refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun m _ => hB m).trans (le_of_eq ?_))
        rw [sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left, nsmul_eq_mul]
      calc |∑ m ∈ Ioc (n - H) (n - H + H), x m| ^ 2 ≤ (H * B) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = B ^ 2 * (H : ℝ) ^ 2 := by ring
  have hshift : ∑ n ∈ Icc (Q + 1) (Q + Q + H), F (n - H) = ∑ t ∈ Icc (Q + 1 - H) (Q + Q), F t := by
    refine sum_nbij' (fun n => n - H) (fun t => t + H) (fun n hn => ?_) (fun t ht => ?_)
      (fun n hn => ?_) (fun t ht => ?_) (fun n _ => rfl)
    · simp only [mem_Icc] at hn ⊢; omega
    · simp only [mem_Icc] at ht ⊢; omega
    · simp only [mem_Icc] at hn; omega
    · simp only [mem_Icc] at ht; omega
  have hgood : (((Icc (Q + 1 - H) (Q + Q)).filter good).card : ℝ) ≤ Q := by
    have hsub : (Icc (Q + 1 - H) (Q + Q)).filter good ⊆ Ico Q (2 * Q) := by
      intro t ht
      obtain ⟨-, h1, h2⟩ := mem_filter.mp ht
      exact mem_Ico.mpr ⟨h1, by omega⟩
    have := card_le_card hsub
    rw [Nat.card_Ico, show 2 * Q - Q = Q by omega] at this
    exact_mod_cast this
  have hbad : (((Icc (Q + 1 - H) (Q + Q)).filter (fun t => ¬ good t)).card : ℝ) ≤ 2 * H := by
    have hsub : (Icc (Q + 1 - H) (Q + Q)).filter (fun t => ¬ good t) ⊆
        Ico (Q + 1 - H) Q ∪ Icc (2 * Q - H) (2 * Q) := by
      intro t ht
      obtain ⟨h1, h2⟩ := mem_filter.mp ht
      have h1' := mem_Icc.mp h1
      simp only [good, not_and_or, not_le, not_lt] at h2
      rcases h2 with h | h
      · exact mem_union_left _ (mem_Ico.mpr ⟨h1'.1, h⟩)
      · exact mem_union_right _ (mem_Icc.mpr ⟨by omega, by omega⟩)
    have hcard : ((Icc (Q + 1 - H) (Q + Q)).filter (fun t => ¬ good t)).card ≤ 2 * H := by
      refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
      rw [Nat.card_Ico, Nat.card_Icc]
      omega
    exact_mod_cast hcard
  calc _ ≤ ∑ n ∈ Icc (Q + 1) (Q + Q + H), F (n - H) := sum_le_sum hpt
    _ = ∑ t ∈ Icc (Q + 1 - H) (Q + Q), F t := hshift
    _ = (((Icc (Q + 1 - H) (Q + Q)).filter good).card : ℝ) * (G / H) ^ 2 +
        (((Icc (Q + 1 - H) (Q + Q)).filter (fun t => ¬ good t)).card : ℝ) * B ^ 2 := by
        simp only [F]; rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
    _ ≤ Q * (G / H) ^ 2 + 2 * H * B ^ 2 := by
        gcongr

/-! ## §2. The centred prime block -/

/-- The centred prime block `(Λ(n) - 1)·𝟙_{(Q, 2Q]}`. -/
def centredPrimeBlock (Q : ℕ) (n : ℕ) : ℝ :=
  if Q < n ∧ n ≤ 2 * Q then vonMangoldt n - 1 else 0

theorem centredPrimeBlock_supp {Q n : ℕ} (h : centredPrimeBlock Q n ≠ 0) :
    n ∈ Icc (Q + 1) (Q + Q) := by
  unfold centredPrimeBlock at h
  split_ifs at h with hn
  · exact mem_Icc.mpr ⟨hn.1, by omega⟩
  · exact absurd rfl h

theorem abs_centredPrimeBlock_le {Q : ℕ} (hQ : 1 ≤ Q) (m : ℕ) :
    |centredPrimeBlock Q m| ≤ Real.log (2 * Q) + 1 := by
  have hl : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith)
  unfold centredPrimeBlock
  split_ifs with h
  · have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := m)
    have hlog := ArithmeticFunction.vonMangoldt_le_log (n := m)
    have hm : Real.log m ≤ Real.log (2 * Q) := by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp; exact hl
      · exact Real.log_le_log (by exact_mod_cast hm0) (by exact_mod_cast h.2)
    rw [abs_le]; constructor <;> linarith
  · simp only [abs_zero]; linarith

theorem abs_centredPrimeBlock_div_le {Q : ℕ} (hQ : 1 ≤ Q) (m : ℕ) :
    |centredPrimeBlock Q m / (m : ℝ) ^ 2| ≤ (Real.log (2 * Q) + 1) / (Q : ℝ) ^ 2 := by
  have hb := abs_centredPrimeBlock_le hQ m
  by_cases h : centredPrimeBlock Q m = 0
  · rw [h, zero_div, abs_zero]
    exact div_nonneg ((abs_nonneg _).trans hb) (by positivity)
  · have hm := mem_Icc.mp (centredPrimeBlock_supp h)
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hmQ : (Q : ℝ) ≤ m := by exact_mod_cast (show Q ≤ m by omega)
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)]
    calc |centredPrimeBlock Q m| / (m : ℝ) ^ 2 ≤ (Real.log (2 * Q) + 1) / (m : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hb (by positivity)
      _ ≤ (Real.log (2 * Q) + 1) / (Q : ℝ) ^ 2 := by
          gcongr
          · exact (abs_nonneg _).trans hb

theorem sum_Icc_centredPrimeBlock_sq_div_le {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ n ∈ Icc (Q + 1) (Q + Q), centredPrimeBlock Q n ^ 2 / (n : ℝ) ^ 4 ≤
      (Real.log (2 * Q) + 1) ^ 2 / (Q : ℝ) ^ 3 := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  calc _ ≤ ∑ _n ∈ Icc (Q + 1) (Q + Q), ((Real.log (2 * Q) + 1) / (Q : ℝ) ^ 2) ^ 2 := by
        refine sum_le_sum fun n _ => ?_
        have h2 := pow_le_pow_left₀ (abs_nonneg _) (abs_centredPrimeBlock_div_le hQ n) 2
        rw [sq_abs] at h2
        calc centredPrimeBlock Q n ^ 2 / (n : ℝ) ^ 4 = (centredPrimeBlock Q n / (n : ℝ) ^ 2) ^ 2 := by
              ring
          _ ≤ _ := h2
    _ = (Real.log (2 * Q) + 1) ^ 2 / (Q : ℝ) ^ 3 := by
        rw [sum_const, Nat.card_Icc, show Q + Q + 1 - (Q + 1) = Q by omega, nsmul_eq_mul]
        field_simp

theorem sum_Icc_centredPrimeBlock_div_eq (Q : ℕ) :
    ∑ n ∈ Icc (Q + 1) (Q + Q), centredPrimeBlock Q n / (n : ℝ) ^ 2 =
      ∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2 := by
  rw [show Icc (Q + 1) (Q + Q) = Ioc Q (2 * Q) by ext n; simp only [mem_Icc, mem_Ioc]; omega]
  refine sum_congr rfl fun n hn => ?_
  rw [centredPrimeBlock, if_pos (mem_Ioc.mp hn)]

/-- `⌈(2Q)^α⌉ (log 2Q + 1)² ≤ 16 δ² Q` once `(1 + log Q)/Q^{(1-α)/2} ≤ δ`. -/
theorem natCeil_rpow_mul_log_sq_le {α δ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {Q : ℕ} (hQ : 1 ≤ Q)
    (hg : (1 + Real.log Q) / (Q : ℝ) ^ ((1 - α) / 2) ≤ δ) :
    (⌈(2 * (Q : ℝ)) ^ α⌉₊ : ℝ) * (Real.log (2 * Q) + 1) ^ 2 ≤ 16 * δ ^ 2 * Q := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQR
  have hQt : 0 < (Q : ℝ) ^ ((1 - α) / 2) := Real.rpow_pos_of_pos hQ0 _
  have h1 : 1 + Real.log Q ≤ δ * (Q : ℝ) ^ ((1 - α) / 2) := (div_le_iff₀ hQt).mp hg
  have hδ : 0 ≤ δ := le_trans (div_nonneg (by linarith) hQt.le) hg
  -- `H ≤ 4 Q^α`
  have h2α : (2 : ℝ) ^ α ≤ 2 := by
    calc (2 : ℝ) ^ α ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
      _ = 2 := Real.rpow_one 2
  have hQα : 1 ≤ (Q : ℝ) ^ α := Real.one_le_rpow hQR hα0
  have hH : (⌈(2 * (Q : ℝ)) ^ α⌉₊ : ℝ) ≤ 4 * (Q : ℝ) ^ α := by
    have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Q) α)
    have hm : (2 * (Q : ℝ)) ^ α = (2 : ℝ) ^ α * (Q : ℝ) ^ α := Real.mul_rpow (by norm_num) hQ0.le
    have h2 : (2 : ℝ) ^ α * (Q : ℝ) ^ α ≤ 2 * (Q : ℝ) ^ α :=
      mul_le_mul_of_nonneg_right h2α (by positivity)
    linarith
  -- `L² ≤ 4 δ² Q^{1-α}`
  have hL : Real.log (2 * Q) + 1 ≤ 2 * (1 + Real.log Q) := by
    rw [Real.log_mul (by norm_num) hQ0.ne']
    have := Real.log_two_lt_d9
    linarith
  have hL2 : (Real.log (2 * Q) + 1) ^ 2 ≤ 4 * δ ^ 2 * (Q : ℝ) ^ (1 - α) := by
    have hL0 : 0 ≤ Real.log (2 * Q) + 1 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * Q by linarith); linarith
    have hsq : ((Q : ℝ) ^ ((1 - α) / 2)) ^ 2 = (Q : ℝ) ^ (1 - α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
    calc (Real.log (2 * Q) + 1) ^ 2 ≤ (2 * (δ * (Q : ℝ) ^ ((1 - α) / 2))) ^ 2 :=
          pow_le_pow_left₀ hL0 (hL.trans (by linarith)) 2
      _ = 4 * δ ^ 2 * (Q : ℝ) ^ (1 - α) := by rw [mul_pow, mul_pow, hsq]; ring
  have hsum : (Q : ℝ) ^ α * (Q : ℝ) ^ (1 - α) = Q := by
    rw [← Real.rpow_add hQ0]; norm_num
  calc (⌈(2 * (Q : ℝ)) ^ α⌉₊ : ℝ) * (Real.log (2 * Q) + 1) ^ 2
      ≤ (4 * (Q : ℝ) ^ α) * (4 * δ ^ 2 * (Q : ℝ) ^ (1 - α)) :=
        mul_le_mul hH hL2 (sq_nonneg _) (by positivity)
    _ = 16 * δ ^ 2 * ((Q : ℝ) ^ α * (Q : ℝ) ^ (1 - α)) := by ring
    _ = 16 * δ ^ 2 * Q := by rw [hsum]

/-! ## §3. The cross-scale remainder of the centred prime block -/

theorem pi_sq_div_48_mul_sqrt_two_le : Real.pi ^ 2 / 48 * Real.sqrt 2 ≤ 1 / 2 := by
  have hpi := Real.pi_lt_d2
  have hs : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hpi2 : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_pos]
  nlinarith [Real.sqrt_nonneg 2]

/-- The smoothed-away factor: `√(2H) √(Σ c(p)² p) L ≤ (ε/2) √(Σ c(p)² p²)` when `8HL² ≤ ε² p` on `S`. -/
theorem sqrt_two_mul_window_le {H : ℕ} {L ε : ℝ} (hL : 1 ≤ L) (hε : 0 < ε) {S : Finset ℕ}
    {c : ℕ → ℝ} (hSP : ∀ p ∈ S, 8 * (H : ℝ) * L ^ 2 ≤ ε ^ 2 * p) :
    Real.sqrt (2 * H) * Real.sqrt (∑ p ∈ S, c p ^ 2 * p) * L ≤
      ε / 2 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) := by
  rw [show Real.sqrt (2 * H) * Real.sqrt (∑ p ∈ S, c p ^ 2 * p) * L =
      Real.sqrt (2 * H * L ^ 2 * ∑ p ∈ S, c p ^ 2 * p) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by linarith)]; ring,
    show ε / 2 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) =
      Real.sqrt ((ε / 2) ^ 2 * ∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]]
  refine Real.sqrt_le_sqrt ?_
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun p hp => ?_
  have h8p := hSP p hp
  have hc2 : 0 ≤ c p ^ 2 * p := by positivity
  nlinarith

/-- **The assembly at one scale.** If the averaged centred prime block has `Σ x̄² ≤ ε²/Q³` at a
length `1 ≤ H ≤ Q`, the cross-scale remainder is at most `ε` times the large-sieve size plus the mass
and cubic terms. -/
theorem abs_rowBilinear_centredPrimeBlock_le_of_average {N Q₀ Q H : ℕ} {S : Finset ℕ}
    {c : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) (hQ1 : 1 ≤ Q) (hH1 : 1 ≤ H) (hHQ : H ≤ Q)
    (hxbar : ∑ n ∈ Icc (Q + 1) (Q + Q + H),
      shortWindowAverage H (fun n => centredPrimeBlock Q n / (n : ℝ) ^ 2) n ^ 2 ≤
        ε ^ 2 / (Q : ℝ) ^ 3)
    (hQ₀ : 2 ≤ Q₀) (hN : Q + Q + H ≤ N + 1) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀)
    (hSP : ∀ p ∈ S, 8 * (H : ℝ) * (Real.log (2 * Q) + 1) ^ 2 ≤ ε ^ 2 * p)
    (hsupp : ∀ n, c n ≠ 0 → n ∈ S) :
    |rowBilinear N c (centredPrimeBlock Q) +
        rowMean N c * vonMangoldtReadout N (centredPrimeBlock Q) +
        rowBeta N c * finiteHarmonicSum N (centredPrimeBlock Q)| ≤
      ε * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) *
          Real.sqrt (1 / (Q : ℝ) ^ 3) +
        |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| / 6 * ∑ p ∈ S, |c p| / p +
        3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
          ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 := by
  have ht := abs_rowBilinear_add_mean_add_beta_le_shortWindow (A := Q) (L := Q) hQ₀ hS hsupp
    (fun n hn => centredPrimeBlock_supp hn) hH1 hN
  rw [sum_Icc_centredPrimeBlock_div_eq] at ht
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  set L := Real.log (2 * Q) + 1
  have hL1 : 1 ≤ L := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * Q by linarith); simp only [L]; linarith
  set S₂ := ∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2
  set V := Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2)
  set R := Real.sqrt (1 / (Q : ℝ) ^ 3)
  have hS₂ : 0 ≤ Real.sqrt S₂ := Real.sqrt_nonneg _
  have hV : 0 ≤ V := Real.sqrt_nonneg _
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hT1 : Real.pi ^ 2 / 48 * Real.sqrt S₂ * Real.sqrt ((Q : ℝ) + H + 2 * (Q₀ : ℝ) ^ 2) *
      Real.sqrt (∑ n ∈ Icc (Q + 1) (Q + Q + H),
        shortWindowAverage H (fun n => centredPrimeBlock Q n / (n : ℝ) ^ 2) n ^ 2) ≤
      ε / 2 * Real.sqrt S₂ * V * R := by
    have h1 : Real.sqrt ((Q : ℝ) + H + 2 * (Q₀ : ℝ) ^ 2) ≤ Real.sqrt 2 * V := by
      rw [← Real.sqrt_mul (by norm_num)]
      refine Real.sqrt_le_sqrt ?_
      have : (H : ℝ) ≤ Q := by exact_mod_cast hHQ
      nlinarith
    have h2 : Real.sqrt (∑ n ∈ Icc (Q + 1) (Q + Q + H),
        shortWindowAverage H (fun n => centredPrimeBlock Q n / (n : ℝ) ^ 2) n ^ 2) ≤ ε * R := by
      rw [show ε * R = Real.sqrt (ε ^ 2 / (Q : ℝ) ^ 3) by
        rw [div_eq_mul_one_div, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]]
      exact Real.sqrt_le_sqrt hxbar
    calc _ ≤ Real.pi ^ 2 / 48 * Real.sqrt S₂ * (Real.sqrt 2 * V) * (ε * R) := by gcongr
      _ = (Real.pi ^ 2 / 48 * Real.sqrt 2) * ε * (Real.sqrt S₂ * V * R) := by ring
      _ ≤ 1 / 2 * ε * (Real.sqrt S₂ * V * R) := by gcongr; exact pi_sq_div_48_mul_sqrt_two_le
      _ = ε / 2 * Real.sqrt S₂ * V * R := by ring
  have hT2 : Real.sqrt (2 * H) * Real.sqrt (∑ p ∈ S, c p ^ 2 * p) * V *
      Real.sqrt (∑ n ∈ Icc (Q + 1) (Q + Q), centredPrimeBlock Q n ^ 2 / (n : ℝ) ^ 4) ≤
      ε / 2 * Real.sqrt S₂ * V * R := by
    have h1 := sqrt_two_mul_window_le (S := S) (c := c) hL1 hε hSP
    have h2 : Real.sqrt (∑ n ∈ Icc (Q + 1) (Q + Q), centredPrimeBlock Q n ^ 2 / (n : ℝ) ^ 4) ≤
        L * R := by
      rw [show L * R = Real.sqrt (L ^ 2 / (Q : ℝ) ^ 3) by
        rw [div_eq_mul_one_div, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]]
      exact Real.sqrt_le_sqrt (sum_Icc_centredPrimeBlock_sq_div_le hQ1)
    have h0 : 0 ≤ Real.sqrt (2 * H) * Real.sqrt (∑ p ∈ S, c p ^ 2 * p) * V := by positivity
    calc _ ≤ Real.sqrt (2 * H) * Real.sqrt (∑ p ∈ S, c p ^ 2 * p) * V * (L * R) :=
          mul_le_mul_of_nonneg_left h2 h0
      _ = (Real.sqrt (2 * H) * Real.sqrt (∑ p ∈ S, c p ^ 2 * p) * L) * V * R := by ring
      _ ≤ ε / 2 * Real.sqrt S₂ * V * R := by gcongr
  linarith [ht, hT1, hT2]

/-- The averaged centred prime block at `H = ⌈(2Q)^α⌉` is eventually below `ε²/Q³` in `ℓ²`, and
`8H(log 2Q + 1)² ≤ 3ε²Q`. -/
theorem eventually_centredPrimeBlock_average_le {α : ℝ} (hα : 7 / 12 < α) (hα1 : α < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, 1 ≤ ⌈(2 * (Q : ℝ)) ^ α⌉₊ ∧ ⌈(2 * (Q : ℝ)) ^ α⌉₊ ≤ Q ∧
      ∑ n ∈ Icc (Q + 1) (Q + Q + ⌈(2 * (Q : ℝ)) ^ α⌉₊),
        shortWindowAverage ⌈(2 * (Q : ℝ)) ^ α⌉₊
          (fun n => centredPrimeBlock Q n / (n : ℝ) ^ 2) n ^ 2 ≤ ε ^ 2 / (Q : ℝ) ^ 3 := by
  have hα0 : 0 ≤ α := by linarith
  set ε₁ : ℝ := min (ε / 4) 1
  have hε₁ : 0 < ε₁ := lt_min (by linarith) one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁4 : ε₁ ≤ ε / 4 := min_le_left _ _
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (eventually_abs_psi_window_sub_le hα hα1 hε₁)
  set δ₀ : ℝ := min (ε / 7) (ε₁ / 20)
  have hδ₀ : 0 < δ₀ := lt_min (by linarith) (by linarith)
  have hg := (tendsto_one_add_log_div_rpow_atTop_zero (t := (1 - α) / 2) (by linarith)).eventually
    (eventually_le_nhds hδ₀)
  filter_upwards [hg, eventually_ge_atTop 100, eventually_ge_atTop ⌈X₀ + 1⌉₊] with Q hgQ hQ100 hQX
  set H := ⌈(2 * (Q : ℝ)) ^ α⌉₊
  set L := Real.log (2 * Q) + 1
  have hQ1 : 1 ≤ Q := by omega
  have hQR : (100 : ℝ) ≤ Q := by exact_mod_cast hQ100
  have hQXR : X₀ + 1 ≤ Q := (Nat.le_ceil _).trans (by exact_mod_cast hQX)
  have hL1 : 1 ≤ L := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * Q by linarith); simp only [L]; linarith
  have hHL : (H : ℝ) * L ^ 2 ≤ 16 * δ₀ ^ 2 * Q := natCeil_rpow_mul_log_sq_le hα0 hα1.le hQ1 hgQ
  have hHle : (2 * (Q : ℝ)) ^ α ≤ H := Nat.le_ceil _
  have hH1 : 1 ≤ H := by
    have : (1 : ℝ) ≤ (2 * (Q : ℝ)) ^ α := Real.one_le_rpow (by linarith) hα0
    exact_mod_cast this.trans hHle
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH1
  have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  have hHL' : (H : ℝ) ≤ H * L ^ 2 := by
    calc (H : ℝ) = H * 1 := by ring
      _ ≤ H * L ^ 2 := mul_le_mul_of_nonneg_left hL2 (by positivity)
  have h8 : 8 * (H : ℝ) * L ^ 2 ≤ 3 * ε ^ 2 * Q := by
    have : δ₀ ^ 2 ≤ (ε / 7) ^ 2 := pow_le_pow_left₀ hδ₀.le (min_le_left _ _) 2
    nlinarith
  have h25 : 25 * (H : ℝ) ≤ ε₁ * Q := by
    have : δ₀ ^ 2 ≤ (ε₁ / 20) ^ 2 := pow_le_pow_left₀ hδ₀.le (min_le_right _ _) 2
    have : ε₁ ^ 2 ≤ ε₁ := by nlinarith
    nlinarith
  have hHQ : H ≤ Q := by
    have : (H : ℝ) ≤ Q := by nlinarith
    exact_mod_cast this
  refine ⟨hH1, hHQ, ?_⟩
  have hwin : ∀ t, Q ≤ t → t + H < 2 * Q →
      |∑ m ∈ Ioc t (t + H), centredPrimeBlock Q m / (m : ℝ) ^ 2| ≤ 2 * ε₁ * H / (Q : ℝ) ^ 2 := by
    intro t ht1 ht2
    have hb := abs_sum_block_le_of_window hα0 hε₁ hε₁1 hX₀ (A := t + 1) (K := 1) (m := 0)
      (by omega) (by omega) hH1 hQR hQXR hHle h25 (by norm_num)
    simp only [zero_mul, add_zero] at hb
    rw [show ∑ m ∈ Ioc t (t + H), centredPrimeBlock Q m / (m : ℝ) ^ 2 =
        ∑ n ∈ Ico (t + 1) (t + 1 + H), (vonMangoldt n - 1) / (n : ℝ) ^ 2 by
      rw [show Ioc t (t + H) = Ico (t + 1) (t + 1 + H) by ext n; simp only [mem_Ioc, mem_Ico]; omega]
      refine sum_congr rfl fun n hn => ?_
      have := mem_Ico.mp hn
      rw [centredPrimeBlock, if_pos ⟨by omega, by omega⟩]]
    exact hb
  refine (sum_sq_shortWindowAverage_le_of_window hH1 hHQ
    (fun m => abs_centredPrimeBlock_div_le hQ1 m) hwin).trans ?_
  have hQ0 : (0 : ℝ) < Q := by linarith
  have e1 : (Q : ℝ) * (2 * ε₁ * H / (Q : ℝ) ^ 2 / H) ^ 2 = 4 * ε₁ ^ 2 / (Q : ℝ) ^ 3 := by
    field_simp; ring
  have e2 : 2 * (H : ℝ) * (L / (Q : ℝ) ^ 2) ^ 2 = 2 * (H * L ^ 2) / (Q : ℝ) ^ 4 := by
    field_simp
  rw [e1, e2]
  have hε4 : 4 * ε₁ ^ 2 ≤ ε ^ 2 / 4 := by
    have := pow_le_pow_left₀ hε₁.le hε₁4 2; nlinarith
  have hQ4 : 2 * (H * L ^ 2) / (Q : ℝ) ^ 4 ≤ 3 / 4 * ε ^ 2 / (Q : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 * (H * L ^ 2) ≤ 3 / 4 * ε ^ 2 * Q := by linarith
    have hQ3 : (0 : ℝ) ≤ (Q : ℝ) ^ 3 := by positivity
    calc 2 * (H * L ^ 2) * (Q : ℝ) ^ 3 ≤ 3 / 4 * ε ^ 2 * Q * (Q : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right this hQ3
      _ = 3 / 4 * ε ^ 2 * (Q : ℝ) ^ 4 := by ring
  have hQ3' : 4 * ε₁ ^ 2 / (Q : ℝ) ^ 3 ≤ ε ^ 2 / 4 / (Q : ℝ) ^ 3 :=
    div_le_div_of_nonneg_right hε4 (by positivity)
  calc _ ≤ ε ^ 2 / 4 / (Q : ℝ) ^ 3 + 3 / 4 * ε ^ 2 / (Q : ℝ) ^ 3 := add_le_add hQ3' hQ4
    _ = ε ^ 2 / (Q : ℝ) ^ 3 := by ring

/-- **The centred prime block beats the large sieve.** For `7/12 < α < 1`, `ε > 0` and all large `Q`,
with `H = ⌈(2Q)^α⌉`, every row `c` on primes `p ≤ Q₀` with `8H (log 2Q + 1)² ≤ ε² p` has, against
`c' = (Λ - 1)·𝟙_{(Q, 2Q]}`,
`|B + m R' + β H'| ≤ ε √(Σ c(p)² p²) √(Q + 2Q₀²) Q^{-3/2} + |Σ_{Q<n≤2Q} (Λ(n) - 1)/n²| Σ_p |c(p)|/(6p)
  + ¾ Σ_d |c(d)| d² Σ_n |c'(n)|/n³`. -/
theorem eventually_abs_rowBilinear_centredPrimeBlock_le {α : ℝ} (hα : 7 / 12 < α) (hα1 : α < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ {N Q₀ : ℕ} {S : Finset ℕ} {c : ℕ → ℝ}, 2 ≤ Q₀ →
      Q + Q + ⌈(2 * (Q : ℝ)) ^ α⌉₊ ≤ N + 1 → (∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) →
      (∀ p ∈ S, 8 * (⌈(2 * (Q : ℝ)) ^ α⌉₊ : ℝ) * (Real.log (2 * Q) + 1) ^ 2 ≤ ε ^ 2 * p) →
      (∀ n, c n ≠ 0 → n ∈ S) →
      |rowBilinear N c (centredPrimeBlock Q) +
          rowMean N c * vonMangoldtReadout N (centredPrimeBlock Q) +
          rowBeta N c * finiteHarmonicSum N (centredPrimeBlock Q)| ≤
        ε * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) *
            Real.sqrt (1 / (Q : ℝ) ^ 3) +
          |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| / 6 * ∑ p ∈ S, |c p| / p +
          3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
            ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 := by
  filter_upwards [eventually_centredPrimeBlock_average_le hα hα1 hε, eventually_ge_atTop 1] with
    Q hQ hQ1
  intro N Q₀ S c hQ₀ hN hS hSP hsupp
  exact abs_rowBilinear_centredPrimeBlock_le_of_average hε hQ1 hQ.1 hQ.2.1 hQ.2.2 hQ₀ hN hS hSP
    hsupp

end

end GaloisForLFunctions.BezoutValuationIncidence
