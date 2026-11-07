import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMoebiusProducer

/-!
# The Möbius producer has a rate

Assemble the Möbius part and the entangled letters into an integer producer. With `T ≥ 2`, `G > T`, and
a Mertens level `η`, the near condition gives a producer with window `[1, G)` on the alphabet `[1, G T]`, of
rate at most `4 Z (1 + log (G T))`, where `Z = π(T) T / G`.

Choosing `G` optimally: if `|M(y)| ≤ δ y` for `y ≥ T` and `|m(T)| ≤ δ`, there is a producer on an alphabet
in `[1, T³/δ]` of rate at most `8 δ (3 + 2 log (T²/δ)) (1 + log (T³/δ))`.

So the rate of an integer producer is the Mertens level, up to logarithms, at a polynomial alphabet.
-/

open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The letters of the Möbius producer. -/
def moebiusLetters (T G : ℕ) : Finset ℕ :=
  (Icc 2 T).filter (fun b => ArithmeticFunction.moebius b ≠ 0) ∪ (primesUpTo T).image (G * ·)

/-- The rational weights of the Möbius producer. -/
def moebiusWeights (T G k : ℕ) : ℚ :=
  if k ≤ T then -(ArithmeticFunction.moebius k : ℚ) / k else (T : ℚ) / G

/-- The coefficient form of a Möbius producer on the letters `moebiusLetters T G`. -/
structure IsMoebiusStencil (c : ℕ →₀ ℤ) (m T G : ℕ) : Prop where
  support : c.support ⊆ insert 1 (moebiusLetters T G)
  letter : ∀ k ∈ moebiusLetters T G, (c k : ℝ) = -(m : ℝ) * k * (moebiusWeights T G k : ℝ)

private lemma mem_primesUpTo' {T P : ℕ} : P ∈ primesUpTo T ↔ P.Prime ∧ P ≤ T := by
  simp only [primesUpTo, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.pos, h2⟩, h1⟩

/-- A sum over the letters splits into a Möbius sum and an entangled sum. -/
theorem sum_moebiusLetters {T G : ℕ} (hG : T < G) (φ : ℕ → ℝ) (hφ : φ 1 = 0) :
    ∑ k ∈ moebiusLetters T G, (moebiusWeights T G k : ℝ) * φ k =
      ∑ b ∈ Icc 1 T, (-(ArithmeticFunction.moebius b : ℝ) / b) * φ b +
        (T : ℝ) / G * ∑ P ∈ primesUpTo T, φ (G * P) := by
  classical
  have hG0 : 0 < G := by omega
  have hdisj : Disjoint ((Icc 2 T).filter (fun b => ArithmeticFunction.moebius b ≠ 0))
      ((primesUpTo T).image (G * ·)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hk'
    have hPpos := (mem_primesUpTo'.mp hP).1.pos
    have h1 := (mem_Icc.mp (mem_filter.mp hk).1).2
    have h2 : G ≤ G * P := Nat.le_mul_of_pos_right G hPpos
    omega
  rw [moebiusLetters, sum_union hdisj, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hG0 h)]
  congr 1
  · -- The Möbius sum: the letter `1` and the nonsquarefree `b` contribute nothing.
    have hsplit : Icc 1 T = insert 1 (Icc 2 T) ∨ T = 0 := by
      by_cases hT : 1 ≤ T
      · left
        ext b
        simp only [mem_insert, mem_Icc]
        omega
      · right
        omega
    rw [sum_filter]
    rcases hsplit with hsplit | hT0
    · have h1 : (1 : ℕ) ∉ Icc 2 T := by simp
      rw [hsplit, sum_insert h1, hφ, mul_zero, zero_add]
      refine sum_congr rfl fun b hb => ?_
      have hbT := (mem_Icc.mp hb).2
      by_cases hμ : ArithmeticFunction.moebius b = 0
      · rw [if_neg (not_not.mpr hμ)]
        simp [hμ]
      · rw [if_pos hμ, moebiusWeights, if_pos hbT]
        push_cast
        rfl
    · subst hT0
      simp
  · rw [mul_sum]
    refine sum_congr rfl fun P hP => ?_
    have hPpos := (mem_primesUpTo'.mp hP).1.pos
    have hle : T < G * P := lt_of_lt_of_le hG (Nat.le_mul_of_pos_right G hPpos)
    rw [moebiusWeights, if_neg (by omega)]
    push_cast
    rfl

/-- The weighted residue sum is the Möbius weight. -/
theorem sum_moebiusLetters_mod {T G : ℕ} (hG : T < G) (r : ℕ) :
    ∑ k ∈ moebiusLetters T G, (moebiusWeights T G k : ℝ) * ((r % k : ℕ) : ℝ) =
      moebiusWeight T G r := by
  have h := sum_moebiusLetters hG (fun k => ((r % k : ℕ) : ℝ)) (by simp [Nat.mod_one])
  rw [h, moebiusWeight, mobiusPart, entangled]

/-- The weighted logarithm sum is the slope. -/
theorem sum_moebiusLetters_log {T G : ℕ} (hG : T < G) :
    ∑ k ∈ moebiusLetters T G, (moebiusWeights T G k : ℝ) * Real.log k =
      mobiusSlope T + (T : ℝ) / G * ∑ P ∈ primesUpTo T, Real.log ((G * P : ℕ) : ℝ) := by
  have h := sum_moebiusLetters hG (fun k => Real.log (k : ℝ)) (by simp)
  rw [h, mobiusSlope]

/-- The excess of the slope of the Möbius producer over the main term. -/
private lemma slope_sub_le {T G : ℕ} (hT : 2 ≤ T) (hG : T < G) {η : ℝ} (hη : 0 ≤ η)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y)
    (hZ : |mobiusHarmonic T| + 2 * η * (1 + Real.log G) ≤ nearCoefficient T G) :
    mobiusSlope T + (T : ℝ) / G * ∑ P ∈ primesUpTo T, Real.log ((G * P : ℕ) : ℝ) -
      (1 - 1 / (G : ℝ)) ≤ 2 * nearCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ)) := by
  have hG2 : 2 ≤ G := by omega
  have hGR : (0 : ℝ) < G := by exact_mod_cast (by omega : 0 < G)
  have hTR : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hslope := mobiusSlope_le (T := T) hG2 hη hM
  have hcard : (1 : ℝ) ≤ ((primesUpTo T).card : ℝ) := by
    have h2 : 2 ∈ primesUpTo T := mem_primesUpTo'.mpr ⟨Nat.prime_two, hT⟩
    have : 0 < (primesUpTo T).card := card_pos.mpr ⟨2, h2⟩
    exact_mod_cast this
  have hZ0 : 0 ≤ nearCoefficient T G := by
    rw [nearCoefficient]
    positivity
  have hTG : (T : ℝ) / G ≤ nearCoefficient T G := by
    rw [nearCoefficient]
    have : 0 ≤ (T : ℝ) / G := by positivity
    nlinarith
  have hGT : (1 : ℝ) ≤ ((G * T : ℕ) : ℝ) := by
    have : 1 ≤ G * T := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hlogGT : 0 ≤ Real.log ((G * T : ℕ) : ℝ) := Real.log_nonneg hGT
  have hlogG : Real.log (G : ℝ) ≤ Real.log ((G * T : ℕ) : ℝ) := by
    refine Real.log_le_log hGR ?_
    have : G ≤ G * T := Nat.le_mul_of_pos_right G (by omega)
    exact_mod_cast this
  have hlogG0 : 0 ≤ Real.log (G : ℝ) := Real.log_natCast_nonneg G
  -- The entangled letters cost at most `Z log (G T)`.
  have hfix : (T : ℝ) / G * ∑ P ∈ primesUpTo T, Real.log ((G * P : ℕ) : ℝ) ≤
      nearCoefficient T G * Real.log ((G * T : ℕ) : ℝ) := by
    have hsum : ∑ P ∈ primesUpTo T, Real.log ((G * P : ℕ) : ℝ) ≤
        ((primesUpTo T).card : ℝ) * Real.log ((G * T : ℕ) : ℝ) := by
      rw [← nsmul_eq_mul]
      refine sum_le_card_nsmul _ _ _ fun P hP => ?_
      obtain ⟨hPp, hPT⟩ := mem_primesUpTo'.mp hP
      refine Real.log_le_log ?_ ?_
      · have : 0 < G * P := Nat.mul_pos (by omega) hPp.pos
        exact_mod_cast this
      · exact_mod_cast Nat.mul_le_mul_left G hPT
    calc _ ≤ (T : ℝ) / G * (((primesUpTo T).card : ℝ) * Real.log ((G * T : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by
          rw [nearCoefficient]
          ring
  -- The Möbius part costs at most `Z (1 + log G) + Z`.
  have hQ : (|mobiusHarmonic T| + 2 * η * (1 + Real.log G)) * (1 + Real.log G) ≤
      nearCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ)) := by
    refine mul_le_mul hZ (by linarith) (by linarith) hZ0
  have hprod : 0 ≤ nearCoefficient T G * Real.log ((G * T : ℕ) : ℝ) := mul_nonneg hZ0 hlogGT
  nlinarith

/-- **The Möbius producer.** For `T ≥ 2`, `G > T`, under the near condition
`|m(T)| + 2 η (1 + log G) ≤ Z`, there is an integer producer with window `[1, G)` on the alphabet
`[1, G T]`, with rate at most `4 Z (1 + log (G T))`. -/
theorem exists_moebius_producer_coeff {T G : ℕ} (hT : 2 ≤ T) (hG : T < G) {η : ℝ} (hη : 0 ≤ η)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y)
    (hZ : |mobiusHarmonic T| + 2 * η * (1 + Real.log G) ≤ nearCoefficient T G) :
    ∃ (c : ℕ →₀ ℤ) (m : ℕ), IsProducer c m G ∧ AlphabetLE c (G * T) ∧
      rate c m G ≤ 4 * nearCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ)) ∧
      IsMoebiusStencil c m T G := by
  have hG2 : 2 ≤ G := by omega
  have hGT1 : 1 ≤ G * T := Nat.mul_pos (by omega) (by omega)
  have hJ2 : ∀ k ∈ moebiusLetters T G, 2 ≤ k := by
    intro k hk
    rcases mem_union.mp hk with h | h
    · exact (mem_Icc.mp (mem_filter.mp h).1).1
    · obtain ⟨P, hP, rfl⟩ := mem_image.mp h
      exact hG2.trans (Nat.le_mul_of_pos_right G (mem_primesUpTo'.mp hP).1.pos)
  have hJK : ∀ k ∈ moebiusLetters T G, k ≤ G * T := by
    intro k hk
    rcases mem_union.mp hk with h | h
    · have hkT := (mem_Icc.mp (mem_filter.mp h).1).2
      exact hkT.trans (hG.le.trans (Nat.le_mul_of_pos_right G (by omega)))
    · obtain ⟨P, hP, rfl⟩ := mem_image.mp h
      exact Nat.mul_le_mul_left G (mem_primesUpTo'.mp hP).2
  obtain ⟨c, m, hP, hal, hslope, hsupp, hletter⟩ :=
    exists_producer_of_weights_coeff (J := moebiusLetters T G)
    (moebiusWeights T G) hJ2 hJK hGT1 hG2
    (fun r => by
      rw [sum_moebiusLetters_mod hG]
      exact (moebiusWeight_nonneg hG hη hM hZ r).1)
    (fun r hr => by
      rw [sum_moebiusLetters_mod hG]
      exact one_le_moebiusWeight hG hη hM hZ hr)
  refine ⟨c, m, hP, hal, ?_, ⟨hsupp, hletter⟩⟩
  rw [sum_moebiusLetters_log hG] at hslope
  have hm := hP.m_pos
  have h1 := hP.one_sub_pos
  have hexcess := slope_sub_le hT hG hη hM hZ
  set S : ℝ := mobiusSlope T + (T : ℝ) / G * ∑ P ∈ primesUpTo T, Real.log ((G * P : ℕ) : ℝ) with hS
  have hrate : rate c m G = (S - (1 - 1 / (G : ℝ))) / (1 - 1 / (G : ℝ)) := by
    rw [rate, normSlope, hslope, mul_div_mul_left _ _ hm.ne', div_sub_one h1.ne']
  have hhalf : (1 : ℝ) / 2 ≤ 1 - 1 / (G : ℝ) := by
    have hG2R : (2 : ℝ) ≤ G := by exact_mod_cast hG2
    have : 1 / (G : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hG2R
    linarith
  have hnum := hP.rate_pos
  rw [hrate] at hnum ⊢
  have hnum0 : 0 < S - (1 - 1 / (G : ℝ)) := by
    by_contra hneg
    push Not at hneg
    exact absurd hnum (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg hneg h1.le))
  calc (S - (1 - 1 / (G : ℝ))) / (1 - 1 / (G : ℝ))
      ≤ (S - (1 - 1 / (G : ℝ))) / (1 / 2) :=
        div_le_div_of_nonneg_left hnum0.le (by norm_num) hhalf
    _ = 2 * (S - (1 - 1 / (G : ℝ))) := by ring
    _ ≤ 2 * (2 * nearCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ))) := by linarith
    _ = _ := by ring

theorem exists_moebius_producer {T G : ℕ} (hT : 2 ≤ T) (hG : T < G) {η : ℝ} (hη : 0 ≤ η)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y)
    (hZ : |mobiusHarmonic T| + 2 * η * (1 + Real.log G) ≤ nearCoefficient T G) :
    ∃ (c : ℕ →₀ ℤ) (m : ℕ), IsProducer c m G ∧ AlphabetLE c (G * T) ∧
      rate c m G ≤ 4 * nearCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ)) := by
  obtain ⟨c, m, h1, h2, h3, _⟩ := exists_moebius_producer_coeff hT hG hη hM hZ
  exact ⟨c, m, h1, h2, h3⟩

/-- **The optimal choice of `G`.** If `|M(y)| ≤ δ y` on `y ≥ T`, `|m(T)| ≤ δ`, and
`δ (3 + 2 log (T²/δ)) ≤ ½`, there is an integer producer on an alphabet in `[1, T³/δ]` of rate at most
`8 δ (3 + 2 log (T²/δ)) (1 + log (T³/δ))`. -/
theorem exists_moebius_producer_of_level_coeff {T : ℕ} (hT : 2 ≤ T) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hM : ∀ y, T ≤ y → |mertens y| ≤ δ * y) (hm : |mobiusHarmonic T| ≤ δ)
    (hsmall : δ * (3 + 2 * Real.log ((T : ℝ) ^ 2 / δ)) ≤ 1 / 2) :
    ∃ (c : ℕ →₀ ℤ) (m G : ℕ), T < G ∧ IsProducer c m G ∧ AlphabetLE c ⌊(T : ℝ) ^ 3 / δ⌋₊ ∧
      rate c m G ≤ 8 * (δ * (3 + 2 * Real.log ((T : ℝ) ^ 2 / δ))) *
        (1 + Real.log ((T : ℝ) ^ 3 / δ)) ∧ IsMoebiusStencil c m T G := by
  have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log ((T : ℝ) ^ 2 / δ) := ⟨_, rfl⟩
  rw [← hL] at hsmall ⊢
  have hT2δ : 1 ≤ (T : ℝ) ^ 2 / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have hL0 : 0 ≤ L := hL ▸ Real.log_nonneg hT2δ
  obtain ⟨A, hA⟩ : ∃ A, A = δ * (3 + 2 * L) := ⟨_, rfl⟩
  rw [← hA] at hsmall ⊢
  have hA0 : 0 < A := by rw [hA]; positivity
  have hcardpos : (1 : ℝ) ≤ ((primesUpTo T).card : ℝ) := by
    have h2 : 2 ∈ primesUpTo T := mem_primesUpTo'.mpr ⟨Nat.prime_two, hT⟩
    have : 0 < (primesUpTo T).card := card_pos.mpr ⟨2, h2⟩
    exact_mod_cast this
  have hcardle : ((primesUpTo T).card : ℝ) ≤ T := by
    have h1 : (primesUpTo T).card ≤ (Icc 1 T).card := card_le_card (filter_subset _ _)
    rw [Nat.card_Icc] at h1
    exact_mod_cast (by omega : (primesUpTo T).card ≤ T)
  obtain ⟨X, hX⟩ : ∃ X, X = (T : ℝ) * ((primesUpTo T).card : ℝ) / A := ⟨_, rfl⟩
  have hX2T : 2 * (T : ℝ) ≤ X := by
    rw [hX, le_div_iff₀ hA0]
    nlinarith
  obtain ⟨G, hGdef⟩ : ∃ G, G = ⌊X⌋₊ := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by linarith
  have hGle : (G : ℝ) ≤ X := hGdef ▸ Nat.floor_le hX0
  have hGlt : X < (G : ℝ) + 1 := hGdef ▸ Nat.lt_floor_add_one X
  have hGT : T < G := by
    have h' : (T : ℝ) < G := by linarith
    exact_mod_cast h'
  have hGR : (0 : ℝ) < G := by linarith
  have hGhalf : X / 2 ≤ G := by linarith
  have hXG : (X : ℝ) * A = (T : ℝ) * ((primesUpTo T).card : ℝ) := by
    rw [hX]; field_simp
  -- The near coefficient is pinned between `A` and `2 A`.
  have hZ1 : A ≤ nearCoefficient T G := by
    rw [nearCoefficient, div_mul_eq_mul_div, le_div_iff₀ hGR, ← hXG]
    nlinarith
  have hZ2 : nearCoefficient T G ≤ 2 * A := by
    rw [nearCoefficient, div_mul_eq_mul_div, div_le_iff₀ hGR, ← hXG]
    nlinarith
  have hGupper : (G : ℝ) ≤ (T : ℝ) ^ 2 / δ := by
    refine hGle.trans ?_
    rw [hX, div_le_div_iff₀ hA0 hδ]
    have h3 : δ ≤ A := by
      rw [hA]
      nlinarith
    calc (T : ℝ) * ((primesUpTo T).card : ℝ) * δ ≤ (T : ℝ) * T * A :=
          mul_le_mul (mul_le_mul_of_nonneg_left hcardle hT0.le) h3 hδ.le (by positivity)
      _ = (T : ℝ) ^ 2 * A := by ring
  have hlogG : Real.log (G : ℝ) ≤ L := by
    rw [hL]
    exact Real.log_le_log hGR hGupper
  have hcond : |mobiusHarmonic T| + 2 * δ * (1 + Real.log G) ≤ nearCoefficient T G := by
    refine le_trans ?_ hZ1
    rw [hA]
    nlinarith
  obtain ⟨c, m, hP, hal, hr, hst⟩ := exists_moebius_producer_coeff hT hGT hδ.le hM hcond
  have hGTle : ((G * T : ℕ) : ℝ) ≤ (T : ℝ) ^ 3 / δ := by
    push_cast
    calc (G : ℝ) * T ≤ (T : ℝ) ^ 2 / δ * T := mul_le_mul_of_nonneg_right hGupper hT0.le
      _ = _ := by ring
  refine ⟨c, m, G, hGT, hP, fun k hk => ?_, ?_, hst⟩
  · refine (hal k hk).trans (Nat.le_floor hGTle)
  · have hGT1 : (1 : ℝ) ≤ ((G * T : ℕ) : ℝ) := by
      have : 1 ≤ G * T := Nat.mul_pos (by omega) (by omega)
      exact_mod_cast this
    have hlog : Real.log ((G * T : ℕ) : ℝ) ≤ Real.log ((T : ℝ) ^ 3 / δ) :=
      Real.log_le_log (by linarith) hGTle
    have hlog0 : 0 ≤ Real.log ((G * T : ℕ) : ℝ) := Real.log_nonneg hGT1
    refine hr.trans ?_
    calc 4 * nearCoefficient T G * (1 + Real.log ((G * T : ℕ) : ℝ))
        ≤ 4 * (2 * A) * (1 + Real.log ((T : ℝ) ^ 3 / δ)) := by
          have hZnn : 0 ≤ nearCoefficient T G := by linarith
          exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      _ = _ := by ring

/-- The optimal choice of `G`, without the coefficients. -/
theorem exists_moebius_producer_of_level {T : ℕ} (hT : 2 ≤ T) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ δ * y) (hm : |mobiusHarmonic T| ≤ δ)
    (hsmall : δ * (3 + 2 * Real.log ((T : ℝ) ^ 2 / δ)) ≤ 1 / 2) :
    ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧ AlphabetLE c ⌊(T : ℝ) ^ 3 / δ⌋₊ ∧
      rate c m B ≤ 8 * (δ * (3 + 2 * Real.log ((T : ℝ) ^ 2 / δ))) *
        (1 + Real.log ((T : ℝ) ^ 3 / δ)) := by
  obtain ⟨c, m, G, _, h1, h2, h3, _⟩ := exists_moebius_producer_of_level_coeff hT hδ hδ1 hM hm hsmall
  exact ⟨c, m, G, h1, h2, h3⟩

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
