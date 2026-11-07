import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHalfScaleOfTheRate
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheParityBalanceOfAProducer

/-!
# The one-fifth rate under the Riemann hypothesis

The entangled letters `G P` need not carry equal weights. If `r ≢ s` modulo a prime `P`, with `s = r mod G`, then `r mod G P ≥ s + G`, and only
the squarefree `b ≤ T` divisible by `P` can see the difference between `r` and `s`. There are at most `T/P` of them, each moving `F_T` by at most
`1`. So the weight `W_P = T/(P G)` pays exactly for what `P` can break, and for every `r`

`F_T(r) + Σ_P W_P (r mod G P) ≥ F_T(s) + Z s`, with `Z = (T/G) Σ_{P ≤ T} 1/P`.

The total weight drops from `π(T) T/G` to `(T/G) log log T`. A level `δ` at `T` then costs only `G ≍ T/δ` up to logarithms, and the alphabet is
`T²/δ`. A bound `|M(y)| ≤ C y^{1−σ}` gives the rate `K^{-a}` for every `a < σ/(2 + σ)`. Hence:

* a zero-free strip `Re s > Θ` gives every rate `K^{-a}`, `a < (1 − Θ)/(3 − Θ)`;
* the Riemann hypothesis gives every rate `K^{-a}`, `a < 1/5`.

Conversely, a rate `K^{-a}` forces `Re ρ ≤ 1 − a`. So under the Riemann hypothesis the exponent of the rate lies in `[1/5, 1/2]`.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

theorem mem_primesUpTo {T P : ℕ} : P ∈ primesUpTo T ↔ P.Prime ∧ P ≤ T := by
  simp only [primesUpTo, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.pos, h2⟩, h1⟩

/-- The squarefree `b ≤ T` divisible by a prime in `E` are all that separate `F_T(r)` from `F_T(s)`. -/
theorem abs_mobiusPart_sub_le {T r s : ℕ} (hsr : s ≤ r) :
    |mobiusPart T r - mobiusPart T s| ≤
      ∑ P ∈ (primesUpTo T).filter (fun P => ¬ P ∣ r - s), (T : ℝ) / P := by
  classical
  obtain ⟨E, hE⟩ : ∃ E, E = (primesUpTo T).filter (fun P => ¬ P ∣ r - s) := ⟨_, rfl⟩
  rw [← hE]
  have hterm : ∀ b ∈ Icc 1 T, |(-(ArithmeticFunction.moebius b : ℝ) / b) *
      (((r % b : ℕ) : ℝ) - ((s % b : ℕ) : ℝ))| ≤
        ∑ P ∈ E, if P ∣ b then (1 : ℝ) else 0 := by
    intro b hb
    obtain ⟨hb1, hbT⟩ := mem_Icc.mp hb
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb1
    have hsum0 : 0 ≤ ∑ P ∈ E, if P ∣ b then (1 : ℝ) else 0 :=
      sum_nonneg fun P _ => by split_ifs <;> norm_num
    by_cases hμ : ArithmeticFunction.moebius b = 0
    · simpa [hμ] using hsum0
    have hsq : Squarefree b := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hμ
    by_cases hex : ∃ P ∈ E, P ∣ b
    · obtain ⟨P, hP, hPb⟩ := hex
      have h1 : (1 : ℝ) ≤ ∑ P ∈ E, if P ∣ b then (1 : ℝ) else 0 := by
        have := single_le_sum (f := fun P => if P ∣ b then (1 : ℝ) else 0)
          (fun P _ => by split_ifs <;> norm_num) hP
        simpa [hPb] using this
      refine le_trans ?_ h1
      have hμ1 : |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.abs_moebius_le_one (n := b)
        exact_mod_cast this
      have hr0 : (0 : ℝ) ≤ ((r % b : ℕ) : ℝ) := Nat.cast_nonneg _
      have hs0 : (0 : ℝ) ≤ ((s % b : ℕ) : ℝ) := Nat.cast_nonneg _
      have hr1 : ((r % b : ℕ) : ℝ) ≤ b := by exact_mod_cast (Nat.mod_lt r hb1).le
      have hs1 : ((s % b : ℕ) : ℝ) ≤ b := by exact_mod_cast (Nat.mod_lt s hb1).le
      have hdiff : |((r % b : ℕ) : ℝ) - ((s % b : ℕ) : ℝ)| ≤ b := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul, abs_div, abs_neg, abs_of_pos hbR]
      calc |(ArithmeticFunction.moebius b : ℝ)| / b * |((r % b : ℕ) : ℝ) - ((s % b : ℕ) : ℝ)|
          ≤ 1 / b * b := by gcongr
        _ = 1 := by field_simp
    · push Not at hex
      have hdvd : b ∣ r - s := by
        rw [← Nat.prod_primeFactors_of_squarefree hsq]
        refine Finset.prod_primes_dvd (r - s)
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) fun p hp => ?_
        have hp1 := Nat.prime_of_mem_primeFactors hp
        have hpb := Nat.dvd_of_mem_primeFactors hp
        by_contra hnd
        refine hex p ?_ hpb
        rw [hE]
        exact mem_filter.mpr ⟨mem_primesUpTo.mpr ⟨hp1, (Nat.le_of_mem_primeFactors hp).trans hbT⟩, hnd⟩
      have hmod : s % b = r % b := (Nat.modEq_iff_dvd' hsr).mpr hdvd
      rw [hmod, sub_self, mul_zero, abs_zero]
      exact hsum0
  have hsplit : mobiusPart T r - mobiusPart T s = ∑ b ∈ Icc 1 T,
      (-(ArithmeticFunction.moebius b : ℝ) / b) * (((r % b : ℕ) : ℝ) - ((s % b : ℕ) : ℝ)) := by
    rw [mobiusPart, mobiusPart, ← sum_sub_distrib]
    exact sum_congr rfl fun b _ => by ring
  rw [hsplit]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_comm]
  refine sum_le_sum fun P hP => ?_
  have hP1 : 0 < P := by
    rw [hE] at hP
    exact (mem_primesUpTo.mp (mem_filter.mp hP).1).1.pos
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP1
  have hcount : ∑ b ∈ Icc 1 T, (if P ∣ b then (1 : ℝ) else 0) = ((T / P : ℕ) : ℝ) := by
    have hset : Icc 1 T = Ioc 0 T := by
      ext x
      simp only [mem_Icc, mem_Ioc]
      omega
    rw [hset, ← Nat.Ioc_filter_dvd_card_eq_div T P, card_eq_sum_ones, sum_filter]
    push_cast
    rfl
  rw [hcount]
  exact Nat.cast_div_le

/-- The residue at `G P` is at least `s`, and at least `s + G` when `P` does not divide `r − s`. -/
theorem mod_mul_ge {G P r : ℕ} (hG : 0 < G) (hP : 0 < P) :
    ((r % G : ℕ) : ℝ) + (if P ∣ r - r % G then 0 else (G : ℝ)) ≤ ((r % (G * P) : ℕ) : ℝ) := by
  have hmod : r % (G * P) % G = r % G := Nat.mod_mul_right_mod r G P
  have hdiv := Nat.div_add_mod (r % (G * P)) G
  rw [hmod] at hdiv
  by_cases hd : P ∣ r - r % G
  · rw [if_pos hd, add_zero]
    have : r % G ≤ r % (G * P) := by
      rw [← hdiv]
      exact Nat.le_add_left _ _
    exact_mod_cast this
  · rw [if_neg hd]
    have ht : r % (G * P) / G ≠ 0 := by
      intro h0
      rw [h0, mul_zero, zero_add] at hdiv
      apply hd
      have h1 : G * P ∣ r - r % (G * P) := Nat.dvd_sub_mod r
      rw [← hdiv] at h1
      exact (dvd_mul_left P G).trans h1
    have hG1 : G ≤ G * (r % (G * P) / G) := Nat.le_mul_of_pos_right G (Nat.pos_of_ne_zero ht)
    have : r % G + G ≤ r % (G * P) := by
      rw [← hdiv]
      omega
    exact_mod_cast this

/-- The entangled sum with harmonic weights `T/(P G)`. -/
def harmonicEntangled (T G r : ℕ) : ℝ :=
  ∑ P ∈ primesUpTo T, (T : ℝ) / ((G : ℝ) * P) * ((r % (G * P) : ℕ) : ℝ)

/-- The near coefficient `Z = (T/G) Σ_{P ≤ T} 1/P`. -/
def harmonicCoefficient (T G : ℕ) : ℝ := (T : ℝ) / G * primeHarmonic T

/-- **The harmonic inequality.** For every `r`, with `s = r mod G`,
`F_T(r) + Σ_P (T/(P G)) (r mod G P) ≥ F_T(s) + Z s`. -/
theorem mobiusPart_add_harmonicEntangled_ge (T r : ℕ) {G : ℕ} (hG : 0 < G) :
    mobiusPart T (r % G) + harmonicCoefficient T G * ((r % G : ℕ) : ℝ) ≤
      mobiusPart T r + harmonicEntangled T G r := by
  classical
  have hGR : (0 : ℝ) < G := by exact_mod_cast hG
  have hbad := abs_mobiusPart_sub_le (T := T) (r := r) (s := r % G) (Nat.mod_le r G)
  have hsum : harmonicCoefficient T G * ((r % G : ℕ) : ℝ) +
      ∑ P ∈ (primesUpTo T).filter (fun P => ¬ P ∣ r - r % G), (T : ℝ) / P ≤ harmonicEntangled T G r := by
    rw [sum_filter, harmonicCoefficient, primeHarmonic, mul_assoc, mul_comm (∑ P ∈ primesUpTo T, 1 / (P : ℝ)),
      ← mul_assoc, mul_sum, ← sum_add_distrib, harmonicEntangled]
    refine sum_le_sum fun P hP => ?_
    have hP1 := (mem_primesUpTo.mp hP).1.pos
    have hPR : (0 : ℝ) < P := by exact_mod_cast hP1
    have hW : (0 : ℝ) ≤ (T : ℝ) / ((G : ℝ) * P) := by positivity
    have hm := mul_le_mul_of_nonneg_left (mod_mul_ge (r := r) hG hP1) hW
    refine le_trans (le_of_eq ?_) hm
    by_cases hd : P ∣ r - r % G
    · simp only [hd, not_true_eq_false, if_false, add_zero, if_true]
      field_simp
    · simp only [hd, not_false_eq_true, if_true, if_false]
      field_simp
  have := (abs_le.mp hbad).1
  linarith

/-- The weights of the harmonic producer on the letters of the Möbius producer. -/
def harmonicWeights (T G k : ℕ) : ℚ :=
  if k ≤ T then -(ArithmeticFunction.moebius k : ℚ) / k else (T : ℚ) / ((G : ℚ) * ((k / G : ℕ) : ℚ))

/-- A sum over the letters splits into a Möbius sum and an entangled sum. -/
private lemma sum_harmonicLetters {T G : ℕ} (hG : T < G) (φ : ℕ → ℝ) (hφ : φ 1 = 0) :
    ∑ k ∈ moebiusLetters T G, (harmonicWeights T G k : ℝ) * φ k =
      ∑ b ∈ Icc 1 T, (-(ArithmeticFunction.moebius b : ℝ) / b) * φ b +
        ∑ P ∈ primesUpTo T, (T : ℝ) / ((G : ℝ) * P) * φ (G * P) := by
  classical
  have hG0 : 0 < G := by omega
  have hdisj : Disjoint ((Icc 2 T).filter (fun b => ArithmeticFunction.moebius b ≠ 0))
      ((primesUpTo T).image (G * ·)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hk'
    have hPpos := (mem_primesUpTo.mp hP).1.pos
    have h1 := (mem_Icc.mp (mem_filter.mp hk).1).2
    have h2 : G ≤ G * P := Nat.le_mul_of_pos_right G hPpos
    omega
  rw [moebiusLetters, sum_union hdisj, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hG0 h)]
  congr 1
  · rw [sum_filter]
    rcases Nat.eq_zero_or_pos T with hT0 | hT
    · subst hT0
      simp
    · have hsplit : Icc 1 T = insert 1 (Icc 2 T) := by
        ext b
        simp only [mem_insert, mem_Icc]
        omega
      have h1 : (1 : ℕ) ∉ Icc 2 T := by simp
      rw [hsplit, sum_insert h1, hφ, mul_zero, zero_add]
      refine sum_congr rfl fun b hb => ?_
      have hbT := (mem_Icc.mp hb).2
      by_cases hμ : ArithmeticFunction.moebius b = 0
      · rw [if_neg (not_not.mpr hμ)]
        simp [hμ]
      · rw [if_pos hμ, harmonicWeights, if_pos hbT]
        push_cast
        rfl
  · refine sum_congr rfl fun P hP => ?_
    have hPpos := (mem_primesUpTo.mp hP).1.pos
    have hle : T < G * P := lt_of_lt_of_le hG (Nat.le_mul_of_pos_right G hPpos)
    simp only [harmonicWeights]
    rw [if_neg (by omega), Nat.mul_div_cancel_left _ hG0]
    push_cast
    rfl

private lemma primeHarmonic_ge_half {T : ℕ} (hT : 2 ≤ T) : 1 / 2 ≤ primeHarmonic T := by
  have h2 : 2 ∈ primesUpTo T := mem_primesUpTo.mpr ⟨Nat.prime_two, hT⟩
  have := single_le_sum (f := fun P : ℕ => 1 / (P : ℝ)) (fun P _ => by positivity) h2
  simpa [primeHarmonic] using this

theorem primeHarmonic_le (T : ℕ) : primeHarmonic T ≤ 1 + Real.log T := by
  have hsub : primesUpTo T ⊆ Icc 1 T := filter_subset _ _
  have h1 : primeHarmonic T ≤ ∑ i ∈ Icc 1 T, ((i : ℝ))⁻¹ := by
    rw [primeHarmonic]
    simp only [one_div]
    exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hH := harmonic_le_one_add_log T
  rw [harmonic_eq_sum_Icc] at hH
  push_cast at hH
  linarith

/-- **The harmonic producer.** With `Q = |m(T)| + 2η(1 + log G) ≤ Z`, there is an integer producer with window `[1, G)` on the alphabet `[1, G T]`, of
rate at most `6 Z (1 + log (G T))`. -/
theorem exists_harmonic_producer {T G : ℕ} (hT : 2 ≤ T) (hG : T < G) {η : ℝ} (hη : 0 ≤ η)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y)
    (hZ : |mobiusHarmonic T| + 2 * η * (1 + Real.log G) ≤ harmonicCoefficient T G) :
    ∃ (c : ℕ →₀ ℤ) (m : ℕ), IsProducer c m G ∧ AlphabetLE c (G * T) ∧
      rate c m G ≤ 6 * harmonicCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ)) := by
  have hG0 : 0 < G := by omega
  have hG2 : 2 ≤ G := by omega
  have hGR : (0 : ℝ) < G := by exact_mod_cast hG0
  have hGT1 : 1 ≤ G * T := Nat.mul_pos hG0 (by omega)
  have hJ2 : ∀ k ∈ moebiusLetters T G, 2 ≤ k := by
    intro k hk
    rcases mem_union.mp hk with h | h
    · exact (mem_Icc.mp (mem_filter.mp h).1).1
    · obtain ⟨P, hP, rfl⟩ := mem_image.mp h
      exact hG2.trans (Nat.le_mul_of_pos_right G (mem_primesUpTo.mp hP).1.pos)
  have hJK : ∀ k ∈ moebiusLetters T G, k ≤ G * T := by
    intro k hk
    rcases mem_union.mp hk with h | h
    · have hkT := (mem_Icc.mp (mem_filter.mp h).1).2
      exact hkT.trans (hG.le.trans (Nat.le_mul_of_pos_right G (by omega)))
    · obtain ⟨P, hP, rfl⟩ := mem_image.mp h
      exact Nat.mul_le_mul_left G (mem_primesUpTo.mp hP).2
  have hsumMod : ∀ r, ∑ k ∈ moebiusLetters T G, (harmonicWeights T G k : ℝ) * ((r % k : ℕ) : ℝ) =
      mobiusPart T r + harmonicEntangled T G r := by
    intro r
    have h := sum_harmonicLetters hG (fun k => ((r % k : ℕ) : ℝ)) (by simp [Nat.mod_one])
    rw [h, mobiusPart, harmonicEntangled]
  have hpos : ∀ r, 0 ≤ mobiusPart T r + harmonicEntangled T G r ∧
      (1 ≤ r % G → 1 ≤ mobiusPart T r + harmonicEntangled T G r) := by
    intro r
    have hmain := mobiusPart_add_harmonicEntangled_ge T r hG0
    have hnear : 1 ≤ r % G → 1 ≤ mobiusPart T r + harmonicEntangled T G r := by
      intro hs1
      have hs0 : (0 : ℝ) < ((r % G : ℕ) : ℝ) := by exact_mod_cast hs1
      have hsG : ((r % G : ℕ) : ℝ) ≤ G := by exact_mod_cast (Nat.mod_lt r hG0).le
      have hlog : Real.log ((r % G : ℕ) : ℝ) ≤ Real.log G := Real.log_le_log hs0 hsG
      have hnearlaw := abs_mobiusPart_sub_one_le hs1 hη hM
      have hbound : |mobiusPart T (r % G) - 1| ≤ ((r % G : ℕ) : ℝ) * harmonicCoefficient T G := by
        refine hnearlaw.trans (mul_le_mul_of_nonneg_left (le_trans ?_ hZ) hs0.le)
        gcongr
      have := (abs_le.mp hbound).1
      linarith
    refine ⟨?_, hnear⟩
    by_cases hs : 1 ≤ r % G
    · have := hnear hs
      linarith
    · have hs0 : r % G = 0 := by omega
      rw [hs0] at hmain
      have hF : mobiusPart T 0 = 0 := by simp [mobiusPart]
      simpa [hF] using hmain
  obtain ⟨c, m, hP, hal, hslope⟩ := exists_producer_of_weights (J := moebiusLetters T G)
    (harmonicWeights T G) hJ2 hJK hGT1 hG2
    (fun r => by
      rw [hsumMod]
      exact (hpos r).1)
    (fun r hr => by
      rw [hsumMod]
      obtain ⟨hr1, hrG⟩ := mem_Ico.mp hr
      refine (hpos r).2 ?_
      rw [Nat.mod_eq_of_lt hrG]
      exact hr1)
  refine ⟨c, m, hP, hal, ?_⟩
  have hlogSum := sum_harmonicLetters hG (fun k => Real.log (k : ℝ)) (by simp)
  rw [← mobiusSlope] at hlogSum
  rw [hlogSum] at hslope
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ P ∈ primesUpTo T, (T : ℝ) / ((G : ℝ) * P) * Real.log ((G * P : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hS] at hslope
  have hm := hP.m_pos
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 1 - 1 / (G : ℝ) := ⟨_, rfl⟩
  have hG2R : (2 : ℝ) ≤ G := by exact_mod_cast hG2
  have hd1 : 1 / 2 ≤ d := by
    have : 1 / (G : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hG2R
    rw [hd]
    linarith
  have hd0 : 0 < d := by linarith
  have hrate : rate c m G = (mobiusSlope T + S - d) / d := by
    rw [rate, normSlope, hslope, ← hd, mul_div_mul_left _ _ hm.ne', div_sub_one hd0.ne']
  rw [hrate]
  -- The excess.
  have hH := primeHarmonic_ge_half hT
  have hT0 : (0 : ℝ) < T := by
    have : (2 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  have hZ0 : 0 ≤ harmonicCoefficient T G := by
    rw [harmonicCoefficient]
    positivity
  have hTG : (T : ℝ) / G ≤ 2 * harmonicCoefficient T G := by
    rw [harmonicCoefficient]
    have h0 : 0 ≤ (T : ℝ) / G := by positivity
    nlinarith
  have hGT0 : (1 : ℝ) ≤ ((G * T : ℕ) : ℝ) := by exact_mod_cast hGT1
  have hlogGT : 0 ≤ Real.log ((G * T : ℕ) : ℝ) := Real.log_nonneg hGT0
  have hlogG : Real.log (G : ℝ) ≤ Real.log ((G * T : ℕ) : ℝ) := by
    refine Real.log_le_log hGR ?_
    exact_mod_cast Nat.le_mul_of_pos_right G (by omega : 0 < T)
  have hlogG0 : 0 ≤ Real.log (G : ℝ) := Real.log_nonneg (by linarith)
  have hSle : S ≤ harmonicCoefficient T G * Real.log ((G * T : ℕ) : ℝ) := by
    have e : harmonicCoefficient T G * Real.log ((G * T : ℕ) : ℝ) =
        ∑ P ∈ primesUpTo T, (T : ℝ) / ((G : ℝ) * P) * Real.log ((G * T : ℕ) : ℝ) := by
      rw [harmonicCoefficient, primeHarmonic, mul_sum, sum_mul]
      refine sum_congr rfl fun P hP => ?_
      have hPR : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (mem_primesUpTo.mp hP).1.ne_zero
      field_simp
    rw [hS, e]
    refine sum_le_sum fun P hP => ?_
    obtain ⟨hPp, hPT⟩ := mem_primesUpTo.mp hP
    have hl : Real.log ((G * P : ℕ) : ℝ) ≤ Real.log ((G * T : ℕ) : ℝ) := by
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast Nat.mul_pos hG0 hPp.pos
      · exact_mod_cast Nat.mul_le_mul_left G hPT
    exact mul_le_mul_of_nonneg_left hl (by positivity)
  have hslT := mobiusSlope_le (T := T) hG2 hη hM
  rw [← hd] at hslT
  have hQ : (|mobiusHarmonic T| + 2 * η * (1 + Real.log G)) * (1 + Real.log G) ≤
      harmonicCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ)) :=
    mul_le_mul hZ (by linarith) (by linarith) hZ0
  have hL1 : 1 ≤ 1 + Real.log ((G * T : ℕ) : ℝ) := by linarith
  have hZL : harmonicCoefficient T G ≤ harmonicCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ)) :=
    le_mul_of_one_le_right hZ0 hL1
  have hnum : mobiusSlope T + S - d ≤ 3 * (harmonicCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ))) := by
    have e : harmonicCoefficient T G * Real.log ((G * T : ℕ) : ℝ) =
        harmonicCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ)) - harmonicCoefficient T G := by ring
    linarith
  have hZLpos : 0 ≤ harmonicCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ)) := by positivity
  rw [div_le_iff₀ hd0]
  calc mobiusSlope T + S - d ≤ 3 * (harmonicCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ))) := hnum
    _ = 6 * (harmonicCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ))) * (1 / 2) := by ring
    _ ≤ 6 * (harmonicCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ))) * d :=
        mul_le_mul_of_nonneg_left hd1 (by positivity)
    _ = _ := by ring

/-- The real arithmetic that places `G` for the harmonic producer. -/
private lemma harmonic_scale {T δ l H X : ℝ} (hT : 2 ≤ T) (hδ0 : 0 < δ) (hδT : 1 / T ≤ δ) (hl0 : 0 ≤ l)
    (hlT : 1 + l ≤ T) (hsm : 8 * (δ * (3 + 6 * l)) ≤ 1) (hH1 : 1 / 2 ≤ H) (hH2 : H ≤ 1 + l)
    (hX : X = T * H / (2 * (δ * (3 + 6 * l)))) :
    2 * T ≤ X ∧ 1 ≤ X ∧ 2 * X ≤ T ^ 2 * (1 + l) / δ ∧ 2 * X ≤ T ^ 3 := by
  have hT0 : 0 < T := by linarith
  have hA0 : 0 < δ * (3 + 6 * l) := by positivity
  have hA3 : 3 * δ ≤ δ * (3 + 6 * l) := by nlinarith
  have hX0 : X * (2 * (δ * (3 + 6 * l))) = T * H := by
    rw [hX]
    field_simp
  have hXpos : 0 ≤ X := by
    rw [hX]
    positivity
  have hlow : 2 * T ≤ X := by
    have h1 : 2 * T * (2 * (δ * (3 + 6 * l))) ≤ T * H := by nlinarith
    rw [← hX0] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hup : 2 * X * (3 * δ) ≤ T * (1 + l) := by
    have h1 : X * (3 * δ) ≤ X * (δ * (3 + 6 * l)) := mul_le_mul_of_nonneg_left hA3 hXpos
    have h2 : X * (δ * (3 + 6 * l)) * 2 = T * H := by
      rw [← hX0]
      ring
    have h3 : T * H ≤ T * (1 + l) := mul_le_mul_of_nonneg_left hH2 hT0.le
    nlinarith
  have hy : 1 / δ ≤ T := by
    rw [div_le_iff₀ hδ0]
    rw [div_le_iff₀ hT0] at hδT
    linarith
  have h2X : 2 * X ≤ T * (1 + l) / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith
  refine ⟨hlow, by linarith, ?_, ?_⟩
  · refine h2X.trans ?_
    have h1 : T * (1 + l) ≤ T ^ 2 * (1 + l) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      nlinarith
    exact div_le_div_of_nonneg_right h1 hδ0.le
  · calc 2 * X ≤ T * (1 + l) / δ := h2X
      _ = T * (1 + l) * (1 / δ) := by ring
      _ ≤ T * T * T := mul_le_mul (mul_le_mul_of_nonneg_left hlT hT0.le) hy (by positivity) (by positivity)
      _ = _ := by ring

/-- **The harmonic producer at a Mertens level.** On an alphabet in `[1, T² (1 + log T)/δ]`, of rate at most
`12 δ (3 + 6 log T)(1 + 4 log T)`. -/
theorem exists_harmonic_producer_of_level {T : ℕ} {δ : ℝ} (hT : 2 ≤ T) (hδ0 : 0 < δ)
    (hδT : 1 / (T : ℝ) ≤ δ) (hM : ∀ y, T ≤ y → |mertens y| ≤ δ * y) (hm : |mobiusHarmonic T| ≤ δ)
    (hsm : 8 * (δ * (3 + 6 * Real.log T)) ≤ 1) :
    ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧
      AlphabetLE c ⌊(T : ℝ) ^ 2 * (1 + Real.log T) / δ⌋₊ ∧
      rate c m B ≤ 12 * (δ * (3 + 6 * Real.log T)) * (1 + 4 * Real.log T) := by
  have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  obtain ⟨l, hldef⟩ : ∃ l, l = Real.log (T : ℝ) := ⟨_, rfl⟩
  rw [← hldef] at hsm ⊢
  have hl0 : 0 ≤ l := hldef ▸ Real.log_nonneg (by linarith)
  have hlT : 1 + l ≤ T := by
    have := Real.log_le_sub_one_of_pos hT0
    rw [hldef]
    linarith
  have hH1 := primeHarmonic_ge_half hT
  have hH2 : primeHarmonic T ≤ 1 + l := hldef ▸ primeHarmonic_le T
  obtain ⟨X, hXdef⟩ : ∃ X, X = (T : ℝ) * primeHarmonic T / (2 * (δ * (3 + 6 * l))) := ⟨_, rfl⟩
  obtain ⟨hX1, hX2, hX3, hX4⟩ := harmonic_scale hTR hδ0 hδT hl0 hlT hsm hH1 hH2 hXdef
  have hX0 : 0 ≤ X := by linarith
  obtain ⟨G, hGdef⟩ : ∃ G, G = ⌈X⌉₊ := ⟨_, rfl⟩
  have hGge : X ≤ G := hGdef ▸ Nat.le_ceil X
  have hGlt : (G : ℝ) < X + 1 := hGdef ▸ Nat.ceil_lt_add_one hX0
  have hG2X : (G : ℝ) ≤ 2 * X := by linarith
  have hGpos : (0 : ℝ) < G := by linarith
  have hTG : T < G := by
    have : (T : ℝ) < G := by linarith
    exact_mod_cast this
  obtain ⟨A, hAdef⟩ : ∃ A, A = δ * (3 + 6 * l) := ⟨_, rfl⟩
  rw [← hAdef] at hXdef
  have hA0 : 0 < A := by
    rw [hAdef]
    positivity
  have hXA : X * (2 * A) = (T : ℝ) * primeHarmonic T := by
    rw [hXdef]
    field_simp
  have hZup : harmonicCoefficient T G ≤ 2 * A := by
    have h : harmonicCoefficient T G = X * (2 * A) / G := by
      rw [harmonicCoefficient, hXA]
      ring
    rw [h, div_le_iff₀ hGpos, mul_comm (2 * A)]
    exact mul_le_mul_of_nonneg_right hGge (by positivity)
  have hZlow : A ≤ harmonicCoefficient T G := by
    have h : harmonicCoefficient T G = X * (2 * A) / G := by
      rw [harmonicCoefficient, hXA]
      ring
    rw [h, le_div_iff₀ hGpos]
    calc A * (G : ℝ) ≤ A * (2 * X) := mul_le_mul_of_nonneg_left hG2X hA0.le
      _ = _ := by ring
  have hGT3 : (G : ℝ) ≤ (T : ℝ) ^ 3 := hG2X.trans hX4
  have hlogG : Real.log (G : ℝ) ≤ 3 * l := by
    have h := Real.log_le_log hGpos hGT3
    rwa [Real.log_pow, ← hldef] at h
  have hZ : |mobiusHarmonic T| + 2 * δ * (1 + Real.log G) ≤ harmonicCoefficient T G := by
    refine le_trans ?_ hZlow
    rw [hAdef]
    have h := mul_le_mul_of_nonneg_left (by linarith : 1 + Real.log (G : ℝ) ≤ 1 + 3 * l)
      (by positivity : 0 ≤ 2 * δ)
    have e : δ * (3 + 6 * l) = δ + 2 * δ * (1 + 3 * l) := by ring
    rw [e]
    linarith
  obtain ⟨c, m, hP, hal, hr⟩ := exists_harmonic_producer hT hTG hδ0.le hM hZ
  have hGT : (((G * T : ℕ) : ℝ)) ≤ (T : ℝ) ^ 2 * (1 + l) / δ := by
    push_cast
    have h1 : (G : ℝ) ≤ 2 * X := hG2X
    have hδ1 : (T : ℝ) * (1 + l) / δ ≤ T ^ 2 * (1 + l) / δ := by
      apply div_le_div_of_nonneg_right _ hδ0.le
      have : (T : ℝ) ≤ T ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have hX5 : 2 * X * (T : ℝ) ≤ (T : ℝ) ^ 2 * (1 + l) / δ := by
      have hup : 2 * X ≤ (T : ℝ) * (1 + l) / δ := by
        have h2 : X * (2 * A) = (T : ℝ) * primeHarmonic T := hXA
        have hA3 : 3 * δ ≤ A := by
          rw [hAdef]
          nlinarith
        rw [le_div_iff₀ hδ0]
        have h3 : (T : ℝ) * primeHarmonic T ≤ (T : ℝ) * (1 + l) := mul_le_mul_of_nonneg_left hH2 hT0.le
        have h4 : X * (3 * δ) ≤ X * A := mul_le_mul_of_nonneg_left hA3 hX0
        nlinarith
      calc 2 * X * (T : ℝ) ≤ (T : ℝ) * (1 + l) / δ * T := mul_le_mul_of_nonneg_right hup hT0.le
        _ = _ := by ring
    calc (G : ℝ) * T ≤ 2 * X * T := mul_le_mul_of_nonneg_right h1 hT0.le
      _ ≤ _ := hX5
  refine ⟨c, m, G, hP, fun k hk => (hal k hk).trans (Nat.le_floor hGT), hr.trans ?_⟩
  have hGT4 : ((G * T : ℕ) : ℝ) ≤ (T : ℝ) ^ 4 := by
    push_cast
    calc (G : ℝ) * T ≤ (T : ℝ) ^ 3 * T := mul_le_mul_of_nonneg_right hGT3 hT0.le
      _ = _ := by ring
  have hGT1 : (1 : ℝ) ≤ ((G * T : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < G) (by omega : 0 < T)
  have hlogGT : Real.log ((G * T : ℕ) : ℝ) ≤ 4 * l := by
    have h2 := Real.log_le_log (by linarith) hGT4
    rwa [Real.log_pow, ← hldef] at h2
  have hlogGT0 := Real.log_nonneg hGT1
  have hZ0 : 0 ≤ harmonicCoefficient T G := by linarith
  calc 6 * harmonicCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ))
      ≤ 6 * (2 * A) * (1 + 4 * l) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hZup (by norm_num)) (by linarith) (by linarith) (by positivity)
    _ = _ := by
        rw [hAdef]
        ring

/-- A polylogarithm against a power. -/
private lemma tendsto_polylog_mul_rpow (A : ℝ) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun x : ℝ => A * ((3 + 6 * Real.log x) * (1 + 4 * Real.log x)) * x ^ (-η)) atTop (𝓝 0) := by
  have hbig : (fun x : ℝ => (3 + 6 * Real.log x) * (1 + 4 * Real.log x)) =o[atTop]
      fun x : ℝ => x ^ η := by
    have h1 : (fun x : ℝ => (3 : ℝ) + 6 * Real.log x) =o[atTop] fun x : ℝ => x ^ (η / 2) := by
      refine Asymptotics.IsLittleO.add ?_ ((isLittleO_log_rpow_atTop (by linarith)).const_mul_left 6)
      exact (Asymptotics.isLittleO_const_left.mpr (Or.inr
        (tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop (by linarith)))))
    have h2 : (fun x : ℝ => (1 : ℝ) + 4 * Real.log x) =o[atTop] fun x : ℝ => x ^ (η / 2) := by
      refine Asymptotics.IsLittleO.add ?_ ((isLittleO_log_rpow_atTop (by linarith)).const_mul_left 4)
      exact (Asymptotics.isLittleO_const_left.mpr (Or.inr
        (tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop (by linarith)))))
    refine (h1.mul h2).congr' (EventuallyEq.refl _ _) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have := hbig.tendsto_div_nhds_zero.const_mul A
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_neg hx.le]
  field_simp

/-- **A power bound on the Mertens function gives the polynomial rate.** With `|M(n)| ≤ C n^{1−σ}`, there are integer producers of rate `K^{-a}` for every
`a < σ/(2 + σ)`. -/
theorem hasRate_of_power_sharp {C σ a : ℝ} (hC : 0 ≤ C) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hM : ∀ n : ℕ, 1 ≤ n → |RHTower.Sieve.mertensM n| ≤ C * (n : ℝ) ^ (1 - σ)) (ha0 : 0 < a)
    (ha : a < σ / (2 + σ)) : HasRate fun K => (K : ℝ) ^ (-a) := by
  have hlevel := isMertensLevel_of_power hC hσ0 hσ1 hM
  obtain ⟨A, hAdef⟩ : ∃ A, A = (C + 1) * (1 + 1 / σ) := ⟨_, rfl⟩
  rw [← hAdef] at hlevel
  have hA1 : 1 ≤ A := by
    have h1 : 1 ≤ C + 1 := by linarith
    have h2 : 1 ≤ 1 + 1 / σ := by
      have : 0 ≤ 1 / σ := by positivity
      linarith
    rw [hAdef]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ _ := mul_le_mul h1 h2 zero_le_one (by linarith)
  have hA0 : 0 < A := by linarith
  -- A small power absorbs the logarithm in the alphabet.
  have hd₀ : 0 < 2 + σ := by linarith
  have ha' : a * (2 + σ) < σ := by rwa [lt_div_iff₀ hd₀] at ha
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = (σ - a * (2 + σ)) / (2 * a) := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκdef]
    apply div_pos <;> linarith
  have hκa : a * κ = (σ - a * (2 + σ)) / 2 := by
    rw [hκdef]
    field_simp
  obtain ⟨D, hDdef⟩ : ∃ D, D = 2 + σ + κ := ⟨_, rfl⟩
  have hD : 0 < D := by rw [hDdef]; linarith
  have hD1 : 1 ≤ D := by rw [hDdef]; linarith
  have haD : a * D < σ := by
    rw [hDdef]
    nlinarith
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 1 / D := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [hedef]; positivity
  have he1 : e ≤ 1 := by
    rw [hedef, div_le_one hD]
    exact hD1
  obtain ⟨b, hbdef⟩ : ∃ b, b = e * σ := ⟨_, rfl⟩
  have hab : a < b := by
    rw [hbdef, hedef]
    have : 1 / D * σ = σ / D := by ring
    rw [this, lt_div_iff₀ hD]
    exact haD
  obtain ⟨η, hηdef⟩ : ∃ η, η = b - a := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; linarith
  have hcut : Tendsto (fun K : ℕ => ⌊(K : ℝ) ^ e⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop he0).comp tendsto_natCast_atTop_atTop)
  have hpoly := (tendsto_polylog_mul_rpow (24 * A) hη).comp tendsto_natCast_atTop_atTop
  -- `8 δ (3 + 6 log T)` is eventually small, and `1 + log T ≤ T^κ`.
  have hsm : ∀ᶠ T : ℕ in atTop, 8 * (A * (T : ℝ) ^ (-σ) * (3 + 6 * Real.log T)) ≤ 1 := by
    have hlim := (tendsto_polylog_mul_rpow (8 * A) hσ0).comp tendsto_natCast_atTop_atTop
    filter_upwards [hlim.eventually (gt_mem_nhds zero_lt_one), eventually_ge_atTop 1] with T hT hT1
    simp only [Function.comp] at hT
    have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    have hl := Real.log_nonneg hTR
    have hTp : 0 < (T : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
    have h1 : 8 * (A * (T : ℝ) ^ (-σ) * (3 + 6 * Real.log T)) ≤
        8 * A * ((3 + 6 * Real.log (T : ℝ)) * (1 + 4 * Real.log (T : ℝ))) * (T : ℝ) ^ (-σ) := by
      have h2 : 3 + 6 * Real.log (T : ℝ) ≤ (3 + 6 * Real.log (T : ℝ)) * (1 + 4 * Real.log (T : ℝ)) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      calc 8 * (A * (T : ℝ) ^ (-σ) * (3 + 6 * Real.log T))
          = 8 * A * (T : ℝ) ^ (-σ) * (3 + 6 * Real.log T) := by ring
        _ ≤ 8 * A * (T : ℝ) ^ (-σ) * ((3 + 6 * Real.log (T : ℝ)) * (1 + 4 * Real.log (T : ℝ))) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    linarith
  have hlogκ : ∀ᶠ T : ℕ in atTop, 1 + Real.log (T : ℝ) ≤ (T : ℝ) ^ κ := by
    have h1 := (isLittleO_log_rpow_atTop hκ).bound (by norm_num : (0 : ℝ) < 1 / 2)
    have h2 := (tendsto_rpow_atTop hκ).eventually_ge_atTop (2 : ℝ)
    have h3 := tendsto_natCast_atTop_atTop.eventually (h1.and h2)
    filter_upwards [h3, eventually_ge_atTop 1] with T hT hT1
    obtain ⟨h4, h5⟩ := hT
    have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    have hl := Real.log_nonneg hTR
    have hp : 0 < (T : ℝ) ^ κ := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.norm_of_nonneg hl, Real.norm_of_nonneg hp.le] at h4
    linarith
  filter_upwards [hcut.eventually hlevel, hcut.eventually hsm, hcut.eventually hlogκ,
    hcut.eventually_ge_atTop 2, eventually_ge_atTop 1,
    hpoly.eventually (gt_mem_nhds zero_lt_one)] with K hL hS hLog hT2 hK1 hpol
  obtain ⟨T, hTdef⟩ : ∃ T, T = ⌊(K : ℝ) ^ e⌋₊ := ⟨_, rfl⟩
  rw [← hTdef] at hL hS hLog hT2
  obtain ⟨hδ0, _, hδT, hM', hm', _⟩ := hL
  simp only [Function.comp] at hpol
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT2
  have hT0 : (0 : ℝ) < T := by linarith
  have hKe : 0 ≤ (K : ℝ) ^ e := by positivity
  have hTle : (T : ℝ) ≤ (K : ℝ) ^ e := hTdef ▸ Nat.floor_le hKe
  have hTlt : (K : ℝ) ^ e < (T : ℝ) + 1 := hTdef ▸ Nat.lt_floor_add_one _
  obtain ⟨c, m, B, hP, hal, hr⟩ := exists_harmonic_producer_of_level hT2 hδ0 hδT hM' hm' hS
  refine ⟨c, m, B, hP, fun k hk => (hal k hk).trans (Nat.floor_le_of_le ?_), hr.trans ?_⟩
  · -- The alphabet: `T² (1 + log T)/δ ≤ T^{2+σ+κ}/A ≤ K`.
    have hTσ : (0 : ℝ) < (T : ℝ) ^ σ := Real.rpow_pos_of_pos hT0 _
    have hval : (T : ℝ) ^ 2 * (1 + Real.log T) / (A * (T : ℝ) ^ (-σ)) ≤ (T : ℝ) ^ D := by
      have hsplit : (T : ℝ) ^ D = (T : ℝ) ^ 2 * (T : ℝ) ^ κ * (T : ℝ) ^ σ := by
        rw [hDdef, Real.rpow_add hT0, Real.rpow_add hT0, Real.rpow_two]
        ring
      have hinv : (T : ℝ) ^ (-σ) * (T : ℝ) ^ σ = 1 := by
        rw [← Real.rpow_add hT0]
        simp
      rw [div_le_iff₀ (by positivity), hsplit]
      have hTκ : 0 < (T : ℝ) ^ κ := Real.rpow_pos_of_pos hT0 _
      calc (T : ℝ) ^ 2 * (1 + Real.log T) ≤ (T : ℝ) ^ 2 * (T : ℝ) ^ κ :=
            mul_le_mul_of_nonneg_left hLog (by positivity)
        _ = (T : ℝ) ^ 2 * (T : ℝ) ^ κ * ((T : ℝ) ^ (-σ) * (T : ℝ) ^ σ) := by rw [hinv, mul_one]
        _ ≤ (T : ℝ) ^ 2 * (T : ℝ) ^ κ * (A * ((T : ℝ) ^ (-σ) * (T : ℝ) ^ σ)) := by
            rw [hinv, mul_one]
            nlinarith [mul_pos (pow_pos hT0 2) hTκ]
        _ = _ := by ring
    have hpow : (T : ℝ) ^ D ≤ K := by
      calc (T : ℝ) ^ D ≤ ((K : ℝ) ^ e) ^ D := Real.rpow_le_rpow hT0.le hTle hD.le
        _ = (K : ℝ) := by
            rw [← Real.rpow_mul hK0.le, hedef, one_div, inv_mul_cancel₀ hD.ne', Real.rpow_one]
    exact hval.trans hpow
  · -- The rate.
    have hlogT0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by linarith)
    have hTK : (T : ℝ) ≤ K := by
      refine hTle.trans ?_
      calc (K : ℝ) ^ e ≤ (K : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hKR he1
        _ = K := Real.rpow_one _
    have hlogTK : Real.log (T : ℝ) ≤ Real.log (K : ℝ) := Real.log_le_log hT0 hTK
    have hT1 : (K : ℝ) ^ e / 2 ≤ T := by linarith
    have hpow : (T : ℝ) ^ (-σ) ≤ 2 * (K : ℝ) ^ (-b) := by
      calc (T : ℝ) ^ (-σ) ≤ ((K : ℝ) ^ e / 2) ^ (-σ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hT1 (by linarith)
        _ = (2 : ℝ) ^ σ * (K : ℝ) ^ (-b) := by
            rw [Real.div_rpow hKe (by norm_num), ← Real.rpow_mul hK0.le, Real.rpow_neg (by norm_num)]
            have hexp : e * -σ = -b := by rw [mul_neg, hbdef]
            rw [hexp]
            field_simp
        _ ≤ 2 * (K : ℝ) ^ (-b) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            calc (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
              _ = 2 := Real.rpow_one 2
    obtain ⟨u, hudef⟩ : ∃ u, u = Real.log (K : ℝ) := ⟨_, rfl⟩
    rw [← hudef] at hlogTK hpol
    have hsplitK : (K : ℝ) ^ (-b) = (K : ℝ) ^ (-η) * (K : ℝ) ^ (-a) := by
      rw [← Real.rpow_add hK0, hηdef]
      congr 1
      ring
    have hKa : 0 < (K : ℝ) ^ (-a) := Real.rpow_pos_of_pos hK0 _
    have h1 : (3 + 6 * Real.log (T : ℝ)) * (1 + 4 * Real.log (T : ℝ)) ≤ (3 + 6 * u) * (1 + 4 * u) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have hprod0 : 0 ≤ (3 + 6 * Real.log (T : ℝ)) * (1 + 4 * Real.log (T : ℝ)) := by positivity
    calc 12 * (A * (T : ℝ) ^ (-σ) * (3 + 6 * Real.log T)) * (1 + 4 * Real.log T)
        = 12 * A * ((3 + 6 * Real.log (T : ℝ)) * (1 + 4 * Real.log (T : ℝ))) * (T : ℝ) ^ (-σ) := by ring
      _ ≤ 12 * A * ((3 + 6 * Real.log (T : ℝ)) * (1 + 4 * Real.log (T : ℝ))) *
          (2 * ((K : ℝ) ^ (-η) * (K : ℝ) ^ (-a))) := by
          rw [← hsplitK]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ 12 * A * ((3 + 6 * u) * (1 + 4 * u)) * (2 * ((K : ℝ) ^ (-η) * (K : ℝ) ^ (-a))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (24 * A * ((3 + 6 * u) * (1 + 4 * u)) * (K : ℝ) ^ (-η)) * (K : ℝ) ^ (-a) := by ring
      _ ≤ 1 * (K : ℝ) ^ (-a) := mul_le_mul_of_nonneg_right hpol.le hKa.le
      _ = _ := one_mul _

/-- A zero-free strip gives a power bound on the Mertens function, for every exponent above the strip. -/
theorem exists_mertens_power_of_zeroFree {Θ σ : ℝ} (hΘh : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzf : ∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0) (hσ0 : 0 < σ) (hσ : σ < 1 - Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → |RHTower.Sieve.mertensM n| ≤ C * (n : ℝ) ^ (1 - σ) := by
  have hs : 0 < (1 - Θ) - σ := by linarith
  obtain ⟨C, hC, hbd⟩ := RHTower.mobiusMertens_subpower_of_zeroFree hΘh hΘ1.le hzf _ hs
  have hexp : Θ + ((1 - Θ) - σ) = 1 - σ := by ring
  refine ⟨C * 2, by positivity, fun n hn => ?_⟩
  have hb := hbd n
  rw [RHTower.mobiusMertensPartialSum_eq_sieveMertensM, Complex.norm_real, Real.norm_eq_abs,
    hexp] at hb
  refine hb.trans ?_
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) ≤ 1 - σ := by linarith
  have h1 : ((n : ℝ) + 1) ^ (1 - σ) ≤ (2 * (n : ℝ)) ^ (1 - σ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) h0
  have h2 : (2 * (n : ℝ)) ^ (1 - σ) = (2 : ℝ) ^ (1 - σ) * (n : ℝ) ^ (1 - σ) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have h3 : (2 : ℝ) ^ (1 - σ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 - σ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hnp : 0 ≤ (n : ℝ) ^ (1 - σ) := by positivity
  calc C * ((n : ℝ) + 1) ^ (1 - σ) ≤ C * ((2 : ℝ) ^ (1 - σ) * (n : ℝ) ^ (1 - σ)) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left h1 hC
    _ ≤ C * (2 * (n : ℝ) ^ (1 - σ)) := by gcongr
    _ = _ := by ring

/-- **The rate from a zero-free strip.** If `ζ ≠ 0` on `Re s > Θ`, `½ ≤ Θ < 1`, there are integer producers of rate `K^{-a}` for every
`a < (1 − Θ)/(3 − Θ)`. -/
theorem hasRate_of_zeroFree_sharp {Θ a : ℝ} (hΘh : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzf : ∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0) (ha0 : 0 < a) (ha : a < (1 - Θ) / (3 - Θ)) :
    HasRate fun K => (K : ℝ) ^ (-a) := by
  have hd : 0 < 3 - Θ := by linarith
  have ha' : a * (3 - Θ) < 1 - Θ := by rwa [lt_div_iff₀ hd] at ha
  have ha1 : a < 1 := by
    by_contra h
    push Not at h
    nlinarith
  have h1a : 0 < 1 - a := by linarith
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁, σ₁ = 2 * a / (1 - a) := ⟨_, rfl⟩
  have hσ₁lt : σ₁ < 1 - Θ := by
    rw [hσ₁, div_lt_iff₀ h1a]
    nlinarith
  have hσ₁0 : 0 < σ₁ := by rw [hσ₁]; positivity
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = (σ₁ + (1 - Θ)) / 2 := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hσ1 : σ ≤ 1 := by rw [hσ]; linarith
  have hσgt : σ₁ < σ := by rw [hσ]; linarith
  obtain ⟨C, hC, hM⟩ := exists_mertens_power_of_zeroFree hΘh hΘ1 hzf hσ0 (by rw [hσ]; linarith)
  refine hasRate_of_power_sharp hC hσ0 hσ1 hM ha0 ?_
  rw [lt_div_iff₀ (by linarith : 0 < 2 + σ)]
  have h3a : 2 * a < σ * (1 - a) := by
    have : σ₁ * (1 - a) = 2 * a := by
      rw [hσ₁]
      field_simp
    nlinarith
  linarith

/-- **The Riemann hypothesis gives every rate below `K^{-1/5}`.** -/
theorem hasRate_of_riemannHypothesis_sharp (h : RiemannHypothesis) {a : ℝ} (ha0 : 0 < a)
    (ha : a < 1 / 5) : HasRate fun K => (K : ℝ) ^ (-a) := by
  have hzf : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → riemannZeta s ≠ 0 := by
    intro s hs
    by_cases h1 : s.re < 1
    · exact (RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mp h) s hs h1
    · exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h1)
  refine hasRate_of_zeroFree_sharp (Θ := 1 / 2) le_rfl (by norm_num) hzf ha0 ?_
  norm_num
  linarith

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
