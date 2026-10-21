import GaloisForLFunctions.BezoutValuationIncidence.PronicBaezDuarteCriterion
import GaloisForLFunctions.BezoutValuationIncidence.LogHarmonicReadoutAndTheMobiusRowEnergyFloor
import GaloisForLFunctions.BezoutValuationIncidence.EnergyCenteredPronicGramPositivityAndVonMangoldtLowerBound
import GaloisForLFunctions.BezoutValuationIncidence.TruncatedPronicGramMatrixAndFiniteHorizonVonMangoldtApproximation
import GaloisForLFunctions.BezoutValuationIncidence.OscillatoryPronicTailSummationByPartsAndSecondOrderVonMangoldtError
import GaloisForLFunctions.BezoutValuationIncidence.ExactVasyuninReciprocityAsResidueDifferenceEnergy

/-!
# The summatory function controls the pronic Gram of a dyadic row

Let a row `c` be supported on one dyadic block of moduli `(N₀, 2N₀]` and let its summatory
function be bounded, `|Σ_{n ≤ m} c(n)| ≤ B` for all `m`. The energy-centered prefix
discrepancy is `V(M) = R₀ - Σ_n c(n) (M mod n)/n` with the von Mangoldt constant `R₀`, and

`Σ_n c(n) (M mod n)/n = M Σ_n c(n)/n - Σ_{j ≤ M} S(⌊M/j⌋)`,  `S(m) = Σ_{n ≤ m} c(n)`

(the hyperbola identity `Σ_n c(n) ⌊M/n⌋ = Σ_j S(⌊M/j⌋)`). Abel summation against the
decreasing weight `1/n` bounds the first term by `B M/(N₀+1)`; only the `⌊M/(N₀+1)⌋` layers
`j` with `⌊M/j⌋ > N₀` contribute to the second. Hence `|V(M) - R₀| ≤ 2 B M/(N₀+1)` below the
quadratic horizon `M ≤ (N₀+1)²`, the trivial bound `‖c‖₁` above it, and

`Σ_M V(M)²/(M(M+1)) ≤ 3 R₀² + 8 B² + 2 ‖c‖₁²/(N₀+1)²`.

Abel summation against `log n/n` gives `|R₀| ≤ B`, and `‖c‖₁²/(N₀+1)² ≤ 2 D(c)` by
Cauchy–Schwarz, where `D(c) = Σ c(n)²/n` is the diagonal of the row. Hence

`Σ_M V(M)²/(M(M+1)) ≤ 11 B² + 4 D(c)`.

For every row class whose dyadic summatory function is `O(√D)` — alternating signs on
consecutive moduli, a fixed character twist, any bounded-partial-sum pattern — the pronic Gram
is within a constant of its diagonal: dispersion at the receiver exponent `θ = 2`, at one
modulus, with no character or modulus average. Cauchy–Schwarz loses the number `N₀` of moduli.
Coherent blocks (`BrownianBridgeLawOfThePrimeBlockAndCodimensionNoGo`) show that the
summatory function is also necessary: the first-window energy is its mean square.
-/

open Finset ArithmeticFunction RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §2. The residue sum of a dyadic row -/

/-- The hyperbola identity: `Σ_n c(n) ⌊M/n⌋ = Σ_{j ≤ M} Σ_{n ≤ ⌊M/j⌋} c(n)`. -/
theorem sum_mul_div_eq_sum_partial (N M : ℕ) (c : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, c n * ((M / n : ℕ) : ℝ) =
      ∑ j ∈ Icc 1 M, ∑ n ∈ Icc 1 (min N (M / j)), c n := by
  have hcount : ∀ n ∈ Icc 1 N, ((M / n : ℕ) : ℝ) =
      ∑ j ∈ Icc 1 M, if n ≤ M / j then (1 : ℝ) else 0 := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    congr 1
    rw [show (Icc 1 M).filter (fun j => n ≤ M / j) = Icc 1 (M / n) by
      ext j
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hj1, _⟩, hj⟩
        refine ⟨hj1, ?_⟩
        rw [Nat.le_div_iff_mul_le (by omega)] at hj ⊢
        linarith
      · rintro ⟨hj1, hj⟩
        have hjM : j ≤ M := hj.trans (Nat.div_le_self _ _)
        refine ⟨⟨hj1, hjM⟩, ?_⟩
        rw [Nat.le_div_iff_mul_le (by omega)] at hj ⊢
        linarith, Nat.card_Icc, Nat.add_sub_cancel]
  rw [sum_congr rfl fun n hn => by rw [hcount n hn, mul_sum], sum_comm]
  refine sum_congr rfl fun j _ => ?_
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_Icc, le_min_iff]
  tauto

/-- Support on `(N₀, 2N₀]`: partial sums below `N₀` vanish. -/
theorem sum_Icc_eq_zero_of_le {c : ℕ → ℝ} {N₀ : ℕ} (hsupp : ∀ n, c n ≠ 0 → N₀ < n)
    {m : ℕ} (hm : m ≤ N₀) : ∑ n ∈ Icc 1 m, c n = 0 :=
  sum_eq_zero fun n hn => by
    by_contra h
    have := hsupp n h
    have := (mem_Icc.mp hn).2
    omega

/-- Abel summation on a dyadic row: against a weight that is nonnegative and decreasing on the
support, `|Σ_n c(n) w(n)| ≤ B w(N₀ + 1)`. -/
theorem abs_sum_mul_weight_le_of_partial (N N₀ : ℕ) (c w : ℕ → ℝ) {B : ℝ}
    (hsupp : ∀ n, c n ≠ 0 → N₀ < n ∧ n ≤ 2 * N₀) (h2N : 2 * N₀ ≤ N)
    (hB : ∀ m, |∑ n ∈ Icc 1 m, c n| ≤ B) (hw0 : ∀ i, 0 ≤ w (N₀ + 1 + i))
    (hanti : Antitone fun i => w (N₀ + 1 + i)) :
    |∑ n ∈ Icc 1 N, c n * w n| ≤ B * w (N₀ + 1) := by
  have hshift : ∀ (f : ℕ → ℝ), (∀ n, c n = 0 → f n = 0) → ∀ K, N₀ + K ≤ N →
      ∑ n ∈ Icc 1 (N₀ + K), f n = ∑ i ∈ range K, f (N₀ + 1 + i) := by
    intro f hf K
    induction K with
    | zero =>
      intro _
      simp only [add_zero, range_zero, sum_empty]
      exact sum_eq_zero fun n hn => hf n (by
        by_contra h
        have := (hsupp n h).1
        have := (mem_Icc.mp hn).2
        omega)
    | succ K ih =>
      intro hK
      rw [show N₀ + (K + 1) = (N₀ + K) + 1 by ring, sum_Icc_succ_top (by omega), ih (by omega),
        Finset.sum_range_succ]
      ring_nf
  have hzero : ∀ n, c n = 0 → c n * w n = 0 := fun n h => by rw [h, zero_mul]
  have hN : N₀ + N₀ ≤ N := by omega
  have htail : ∑ n ∈ Icc 1 N, c n * w n = ∑ n ∈ Icc 1 (N₀ + N₀), c n * w n := by
    rw [← Finset.sum_subset (Icc_subset_Icc_right hN) fun n hn hn' => by
      have hc : c n = 0 := by
        by_contra h
        have := (hsupp n h).2
        simp only [mem_Icc] at hn hn'
        omega
      rw [hc, zero_mul]]
  rw [htail, hshift _ hzero N₀ hN]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have h := abs_sum_range_mul_antitone_le (fun i => c (N₀ + 1 + i))
    (fun i => w (N₀ + 1 + i)) N₀ hB0 hw0 hanti
    (fun m hm => by
      rw [← hshift c (fun _ h => h) m (by omega)]
      exact hB _)
  simp only [add_zero] at h
  convert h using 2
  exact sum_congr rfl fun i _ => mul_comm _ _

/-- The harmonic coefficient of a dyadic row with bounded summatory function. -/
theorem abs_sum_div_le_of_partial (N N₀ : ℕ) (c : ℕ → ℝ) {B : ℝ}
    (hsupp : ∀ n, c n ≠ 0 → N₀ < n ∧ n ≤ 2 * N₀) (h2N : 2 * N₀ ≤ N)
    (hB : ∀ m, |∑ n ∈ Icc 1 m, c n| ≤ B) :
    |∑ n ∈ Icc 1 N, c n / n| ≤ B / ((N₀ : ℝ) + 1) := by
  have h := abs_sum_mul_weight_le_of_partial N N₀ c (fun n => 1 / (n : ℝ)) hsupp h2N hB
    (fun i => by positivity)
    (fun i j hij => one_div_le_one_div_of_le (by positivity) (by push_cast; exact_mod_cast
      (by omega : N₀ + 1 + i ≤ N₀ + 1 + j)))
  simp only [mul_one_div] at h
  convert h using 2
  push_cast
  ring

/-- **Residue sum of a dyadic row.** `|Σ_n c(n)(M mod n)/n| ≤ 2 B M/(N₀+1)`. -/
theorem abs_residueSum_le (N N₀ M : ℕ) (c : ℕ → ℝ) {B : ℝ}
    (hsupp : ∀ n, c n ≠ 0 → N₀ < n ∧ n ≤ 2 * N₀) (h2N : 2 * N₀ ≤ N)
    (hB : ∀ m, |∑ n ∈ Icc 1 m, c n| ≤ B) :
    |∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n| ≤ 2 * B * M / ((N₀ : ℝ) + 1) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hsplit : ∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n =
      (M : ℝ) * ∑ n ∈ Icc 1 N, c n / n - ∑ n ∈ Icc 1 N, c n * ((M / n : ℕ) : ℝ) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hmod : ((M % n : ℕ) : ℝ) = M - n * (M / n : ℕ) := by
      have := congrArg (Nat.cast (R := ℝ)) (Nat.mod_add_div M n)
      push_cast at this
      linarith
    rw [hmod]
    field_simp
  rw [hsplit, sum_mul_div_eq_sum_partial]
  -- the harmonic term
  have h1 : |(M : ℝ) * ∑ n ∈ Icc 1 N, c n / n| ≤ B * M / ((N₀ : ℝ) + 1) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg M)]
    calc (M : ℝ) * |∑ n ∈ Icc 1 N, c n / n| ≤ M * (B / ((N₀ : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (abs_sum_div_le_of_partial N N₀ c hsupp h2N hB)
            (Nat.cast_nonneg M)
      _ = B * M / ((N₀ : ℝ) + 1) := by ring
  -- the hyperbola layers: only `j ≤ M/(N₀+1)` survive
  have h2 : |∑ j ∈ Icc 1 M, ∑ n ∈ Icc 1 (min N (M / j)), c n| ≤ B * M / ((N₀ : ℝ) + 1) := by
    rw [← sum_filter_add_sum_filter_not (Icc 1 M) (fun j => N₀ < M / j)]
    have hzero : ∑ j ∈ (Icc 1 M).filter (fun j => ¬ N₀ < M / j),
        ∑ n ∈ Icc 1 (min N (M / j)), c n = 0 := sum_eq_zero fun j hj => by
      have := (mem_filter.mp hj).2
      exact sum_Icc_eq_zero_of_le (fun n h => (hsupp n h).1)
        ((min_le_right _ _).trans (not_lt.mp this))
    rw [hzero, add_zero]
    have hfilt : (Icc 1 M).filter (fun j => N₀ < M / j) = Icc 1 (M / (N₀ + 1)) := by
      ext j
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hj1, _⟩, hj⟩
        refine ⟨hj1, ?_⟩
        have h1 : (N₀ + 1) * j ≤ M := (Nat.le_div_iff_mul_le (by omega)).mp hj
        exact (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
      · rintro ⟨hj1, hj⟩
        have h1 : j * (N₀ + 1) ≤ M := (Nat.le_div_iff_mul_le (by omega)).mp hj
        refine ⟨⟨hj1, by nlinarith⟩, ?_⟩
        exact (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
    rw [hfilt]
    calc |∑ j ∈ Icc 1 (M / (N₀ + 1)), ∑ n ∈ Icc 1 (min N (M / j)), c n|
        ≤ ∑ j ∈ Icc 1 (M / (N₀ + 1)), |∑ n ∈ Icc 1 (min N (M / j)), c n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Icc 1 (M / (N₀ + 1)), B := sum_le_sum fun j _ => hB _
      _ = ((M / (N₀ + 1) : ℕ) : ℝ) * B := by rw [sum_const, Nat.card_Icc]; simp
      _ ≤ B * M / ((N₀ : ℝ) + 1) := by
        rw [mul_comm, mul_div_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hB0
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast Nat.div_mul_le_self M (N₀ + 1)
  calc _ ≤ |(M : ℝ) * ∑ n ∈ Icc 1 N, c n / n| +
        |∑ j ∈ Icc 1 M, ∑ n ∈ Icc 1 (min N (M / j)), c n| := abs_sub _ _
    _ ≤ B * M / ((N₀ : ℝ) + 1) + B * M / ((N₀ : ℝ) + 1) := add_le_add h1 h2
    _ = 2 * B * M / ((N₀ : ℝ) + 1) := by ring

/-- The trivial residue bound: `|Σ_n c(n)(M mod n)/n| ≤ ‖c‖₁`. -/
theorem abs_residueSum_le_l1 (N M : ℕ) (c : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n| ≤ ∑ n ∈ Icc 1 N, |c n| := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hlt : ((M % n : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Nat.mod_lt M (mem_Icc.mp hn).1).le
  rw [abs_div, abs_mul, abs_of_pos hn0, Nat.abs_cast]
  rw [div_le_iff₀ hn0]
  exact mul_le_mul_of_nonneg_left hlt (abs_nonneg _)

/-! ## §3. The pronic Gram bound -/

/-- **Summatory-function bound for the energy-centered pronic Gram of a dyadic row.** -/
theorem sieveEnergyCenteredPronicGramForm_le_summatory (N N₀ : ℕ) (c : ℕ → ℝ) {B : ℝ}
    (hsupp : ∀ n, c n ≠ 0 → N₀ < n ∧ n ≤ 2 * N₀) (h2N : 2 * N₀ ≤ N)
    (hB : ∀ m, |∑ n ∈ Icc 1 m, c n| ≤ B) :
    sieveEnergyCenteredPronicGramForm N c ≤
      3 * (∑ e ∈ Icc 2 N, vonMangoldt e * BiScaleUncertainty.selbergMultiplesCoord N c e) ^ 2 + 8 * B ^ 2 +
        2 * (∑ n ∈ Icc 1 N, |c n|) ^ 2 / ((N₀ : ℝ) + 1) ^ 2 := by
  set R₀ := ∑ e ∈ Icc 2 N, vonMangoldt e * BiScaleUncertainty.selbergMultiplesCoord N c e with hR₀
  set C₁ := ∑ n ∈ Icc 1 N, |c n|
  set V := fun M => sieveEnergyCenteredPrefixDiscrepancy N M c
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hC₁ : 0 ≤ C₁ := sum_nonneg fun _ _ => abs_nonneg _
  have hV : ∀ M, V M = R₀ - ∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n := fun M => by
    simp only [V]
    rw [sieveEnergyCenteredPrefixDiscrepancy_eq_add_vonMangoldt,
      sievePrefixDiscrepancy_eq_neg_residue]
    ring
  set U := (N₀ + 1) ^ 2
  have hN0 : (0 : ℝ) < (N₀ : ℝ) + 1 := by positivity
  -- the Gram form is the pronic series of `V²`, a bounded sequence
  have hGbd : ∀ M, |V M ^ 2| ≤ (|R₀| + C₁) ^ 2 := fun M => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [hV]
    exact (abs_sub _ _).trans (add_le_add le_rfl (abs_residueSum_le_l1 N M c))
  have hQ : sieveEnergyCenteredPronicGramForm N c = ∑' M : ℕ, V M ^ 2 / (pronicSeq M : ℝ) :=
    (hasSum_sieveEnergyCenteredPrefixDiscrepancy_sq_div_pronicSeq N c).tsum_eq.symm
  have htail := abs_tsum_div_pronicSeq_sub_sum_Icc_le hGbd U
  -- the head below the quadratic horizon
  have hhead : ∑ M ∈ Icc 1 U, V M ^ 2 / (pronicSeq M : ℝ) ≤ 2 * R₀ ^ 2 + 8 * B ^ 2 := by
    have hpt : ∀ M ∈ Icc 1 U, V M ^ 2 / (pronicSeq M : ℝ) ≤
        2 * R₀ ^ 2 * (1 / ((M : ℝ) * ((M : ℝ) + 1))) +
          8 * B ^ 2 / ((N₀ : ℝ) + 1) ^ 2 * 1 := by
      intro M hM
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (mem_Icc.mp hM).1
      have hres := abs_residueSum_le N N₀ M c hsupp h2N hB
      have hsq : V M ^ 2 ≤ 2 * R₀ ^ 2 + 2 * (2 * B * M / ((N₀ : ℝ) + 1)) ^ 2 := by
        rw [hV]
        have := abs_le.mp hres
        nlinarith [sq_nonneg (R₀ + ∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n)]
      rw [cast_pronicSeq_eq]
      have hden : (0 : ℝ) < (M : ℝ) * ((M : ℝ) + 1) := by positivity
      rw [div_le_iff₀ hden]
      have hfrac : (M : ℝ) ^ 2 ≤ (M : ℝ) * ((M : ℝ) + 1) := by nlinarith
      calc V M ^ 2 ≤ 2 * R₀ ^ 2 + 8 * B ^ 2 / ((N₀ : ℝ) + 1) ^ 2 * (M : ℝ) ^ 2 := by
            refine hsq.trans (le_of_eq ?_); field_simp; ring
        _ ≤ 2 * R₀ ^ 2 + 8 * B ^ 2 / ((N₀ : ℝ) + 1) ^ 2 * ((M : ℝ) * ((M : ℝ) + 1)) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hfrac (by positivity))
        _ = _ := by field_simp
    refine (sum_le_sum hpt).trans ?_
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      show Icc 1 U = Ico 1 (U + 1) by rfl, sum_Ico_pronic_mass (by norm_num) (by omega),
      nsmul_eq_mul, mul_one]
    have hU : ((U : ℕ) : ℝ) = ((N₀ : ℝ) + 1) ^ 2 := by simp [U]
    rw [hU]
    have : (1 : ℝ) / ((1 : ℕ) : ℝ) - 1 / ((U + 1 : ℕ) : ℝ) ≤ 1 := by
      have : (0 : ℝ) ≤ 1 / ((U + 1 : ℕ) : ℝ) := by positivity
      linarith
    calc 2 * R₀ ^ 2 * (1 / ((1 : ℕ) : ℝ) - 1 / ((U + 1 : ℕ) : ℝ)) +
          8 * B ^ 2 / ((N₀ : ℝ) + 1) ^ 2 * ((N₀ : ℝ) + 1) ^ 2
        ≤ 2 * R₀ ^ 2 * 1 + 8 * B ^ 2 / ((N₀ : ℝ) + 1) ^ 2 * ((N₀ : ℝ) + 1) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left this (by positivity)) le_rfl
      _ = 2 * R₀ ^ 2 + 8 * B ^ 2 := by field_simp
  -- the tail beyond the quadratic horizon
  have hUR : ((U : ℕ) : ℝ) + 1 = ((N₀ : ℝ) + 1) ^ 2 + 1 := by simp [U]
  have htail' : (|R₀| + C₁) ^ 2 / ((U : ℝ) + 1) ≤ R₀ ^ 2 + 2 * C₁ ^ 2 / ((N₀ : ℝ) + 1) ^ 2 := by
    rw [hUR]
    have h1 : (|R₀| + C₁) ^ 2 ≤ 2 * R₀ ^ 2 + 2 * C₁ ^ 2 := by
      nlinarith [sq_nonneg (|R₀| - C₁), sq_abs R₀]
    have h2 : (1 : ℝ) ≤ ((N₀ : ℝ) + 1) ^ 2 := by nlinarith
    calc (|R₀| + C₁) ^ 2 / (((N₀ : ℝ) + 1) ^ 2 + 1)
        ≤ (2 * R₀ ^ 2 + 2 * C₁ ^ 2) / (((N₀ : ℝ) + 1) ^ 2 + 1) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = 2 * R₀ ^ 2 / (((N₀ : ℝ) + 1) ^ 2 + 1) + 2 * C₁ ^ 2 / (((N₀ : ℝ) + 1) ^ 2 + 1) :=
          add_div _ _ _
      _ ≤ R₀ ^ 2 + 2 * C₁ ^ 2 / ((N₀ : ℝ) + 1) ^ 2 := by
          refine add_le_add ?_ (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (by linarith))
          rw [div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg R₀]
  rw [hQ]
  have := (abs_le.mp htail).2
  calc ∑' M : ℕ, V M ^ 2 / (pronicSeq M : ℝ)
      ≤ ∑ M ∈ Icc 1 U, V M ^ 2 / (pronicSeq M : ℝ) + (|R₀| + C₁) ^ 2 / ((U : ℝ) + 1) := by
        linarith
    _ ≤ (2 * R₀ ^ 2 + 8 * B ^ 2) + (R₀ ^ 2 + 2 * C₁ ^ 2 / ((N₀ : ℝ) + 1) ^ 2) :=
        add_le_add hhead htail'
    _ = 3 * R₀ ^ 2 + 8 * B ^ 2 + 2 * C₁ ^ 2 / ((N₀ : ℝ) + 1) ^ 2 := by ring

/-- The von Mangoldt readout of a dyadic row is at most `B`: Abel summation against the
decreasing weight `log n/n` on `n ≥ 3`. -/
theorem abs_vonMangoldtReadout_le_of_partial (N N₀ : ℕ) (c : ℕ → ℝ) {B : ℝ} (hN₀ : 2 ≤ N₀)
    (hsupp : ∀ n, c n ≠ 0 → N₀ < n ∧ n ≤ 2 * N₀) (h2N : 2 * N₀ ≤ N)
    (hB : ∀ m, |∑ n ∈ Icc 1 m, c n| ≤ B) :
    |vonMangoldtReadout N c| ≤ B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hge : ∀ i : ℕ, Real.exp 1 ≤ ((N₀ + 1 + i : ℕ) : ℝ) := fun i =>
    he.trans (by exact_mod_cast (by omega : 3 ≤ N₀ + 1 + i))
  have h := abs_sum_mul_weight_le_of_partial N N₀ c (fun n => Real.log n / n) hsupp h2N hB
    (fun i => div_nonneg (Real.log_nonneg (by
        have := hge i; linarith [Real.add_one_le_exp (1 : ℝ)])) (Nat.cast_nonneg _))
    (fun i j hij => Real.log_div_self_antitoneOn (hge i) (hge j)
      (by exact_mod_cast (by omega : N₀ + 1 + i ≤ N₀ + 1 + j)))
  rw [vonMangoldtReadout_eq_log_harmonic]
  have hlog : Real.log ((N₀ + 1 : ℕ) : ℝ) / ((N₀ + 1 : ℕ) : ℝ) ≤ 1 := by
    have hpos : (0 : ℝ) < ((N₀ + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_one hpos]
    linarith [Real.log_le_sub_one_of_pos hpos]
  calc |∑ d ∈ Icc 1 N, c d * Real.log d / d| = |∑ n ∈ Icc 1 N, c n * (Real.log n / n)| := by
        congr 1; exact sum_congr rfl fun _ _ => by ring
    _ ≤ B * (Real.log ((N₀ + 1 : ℕ) : ℝ) / ((N₀ + 1 : ℕ) : ℝ)) := h
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left hlog hB0
    _ = B := mul_one B

/-- **The pronic Gram of a dyadic row is at most `11 B² + 4 D(c)`**, with `B` the sup of the
summatory function and `D(c) = Σ c(n)²/n` the diagonal. -/
theorem sieveEnergyCenteredPronicGramForm_le_summatory_add_diag (N N₀ : ℕ) (c : ℕ → ℝ) {B : ℝ}
    (hN₀ : 2 ≤ N₀) (hsupp : ∀ n, c n ≠ 0 → N₀ < n ∧ n ≤ 2 * N₀) (h2N : 2 * N₀ ≤ N)
    (hB : ∀ m, |∑ n ∈ Icc 1 m, c n| ≤ B) :
    sieveEnergyCenteredPronicGramForm N c ≤ 11 * B ^ 2 + 4 * ∑ n ∈ Icc 1 N, c n ^ 2 / n := by
  have hmain := sieveEnergyCenteredPronicGramForm_le_summatory N N₀ c hsupp h2N hB
  have hR := abs_vonMangoldtReadout_le_of_partial N N₀ c hN₀ hsupp h2N hB
  have hR2 : (∑ e ∈ Icc 2 N, vonMangoldt e * BiScaleUncertainty.selbergMultiplesCoord N c e) ^ 2
      ≤ B ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hR 2
  -- `‖c‖₁² ≤ 2 N₀² D(c)` by Cauchy–Schwarz on the support
  set T := Ioc N₀ (2 * N₀)
  have hsub : T ⊆ Icc 1 N := fun n hn => by
    simp only [T, mem_Ioc, mem_Icc] at hn ⊢; omega
  have hout : ∀ n ∈ Icc 1 N, n ∉ T → c n = 0 := fun n _ hn => by
    by_contra h
    exact hn (by simp only [T, mem_Ioc]; exact hsupp n h)
  have hl1 : ∑ n ∈ Icc 1 N, |c n| = ∑ n ∈ T, |c n| :=
    (sum_subset hsub fun n hn hnT => by rw [hout n hn hnT, abs_zero]).symm
  have hD : ∑ n ∈ Icc 1 N, c n ^ 2 / n = ∑ n ∈ T, c n ^ 2 / n :=
    (sum_subset hsub fun n hn hnT => by rw [hout n hn hnT]; simp).symm
  have hcs : (∑ n ∈ T, |c n|) ^ 2 ≤ 2 * (N₀ : ℝ) ^ 2 * ∑ n ∈ T, c n ^ 2 / n := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := T) (f := fun n => |c n|)
    have hcardN : T.card = N₀ := by simp only [T, Nat.card_Ioc]; omega
    have hcard : (T.card : ℝ) = N₀ := by rw [hcardN]
    rw [hcard] at h1
    refine h1.trans ?_
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun n hn => ?_
    have hn := mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn2 : (n : ℝ) ≤ 2 * N₀ := by exact_mod_cast hn.2
    rw [sq_abs, mul_div_assoc', le_div_iff₀ hn0]
    nlinarith [mul_le_mul_of_nonneg_left hn2 (mul_nonneg (Nat.cast_nonneg (α := ℝ) N₀)
      (sq_nonneg (c n)))]
  have hdiv : 2 * (∑ n ∈ Icc 1 N, |c n|) ^ 2 / ((N₀ : ℝ) + 1) ^ 2 ≤
      4 * ∑ n ∈ Icc 1 N, c n ^ 2 / n := by
    rw [hl1, hD, div_le_iff₀ (by positivity)]
    have hDnn : 0 ≤ ∑ n ∈ T, c n ^ 2 / n := sum_nonneg fun n _ => by positivity
    nlinarith [sq_nonneg ((N₀ : ℝ) + 1), Nat.cast_nonneg (α := ℝ) N₀]
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
