import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheOneFifthRateUnderTheRiemannHypothesis
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheParityBalanceOfAProducer

/-!
# The parity neutral producer reaches the Mertens level

Dilating a stencil by `j` multiplies its slope by `1/j` and its parity balance by `λ(j)/j`, so a single Hecke factor
cannot change the ratio of the two by more than a constant. A **difference of adjacent dilates** can. If `λ(n) = −1` and
`λ(n + 1) = +1`, then `T_n − T_{n+1}` adds the two parity balances and subtracts the two slopes:

* parity balance `−(1/n + 1/(n + 1)) I`,
* slope `S / (n (n + 1))`.

The ratio of parity to slope is multiplied by about `2n`. On multiplicities, `F(⌊r/n⌋) − F(⌊r/(n+1)⌋)` is a spike at
`r = n` of height about `1`, and elsewhere it is an error of the size of the near law.

Take `f(r) = F_T(r) + W Σ_P (r mod G P) + a (F_T(⌊r/n⌋) − F_T(⌊r/(n+1)⌋))`, with `n (n + 1) ∣ G`, `a ≈ n/2` fixed by parity
balance `0`, and `W G ≥ (2 n + 3) T`. Entanglement still works: small residues give `r ≡ s` modulo `G P` for all `P ≤ T`, so
modulo `n b` and `(n + 1) b` for squarefree `b ≤ T`, and `f(r) = f(s)`. The spike costs slope about `1/n`.

So **parity neutrality costs nothing at the Mertens level**: from a level `δ(T)` there are parity neutral integer producers
of rate `≍ δ(T)` up to logarithms on an alphabet in `[1, T⁵]`. They reach every rate `exp(−(log K)^α)`, `α < 3/5`, and polynomial
parity neutral rates exist iff `ζ` has a zero-free strip. A pattern `(λ(n), λ(n + 1)) = (−1, +1)` exists in every interval
`[N, 4N]`, since `λ(P) = −1` and `λ(2P) = +1` at a prime `P`.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

local notation "lam" => ArithmeticFunction.liouville

private lemma mem_primesUpTo_iff' {T P : ℕ} : P ∈ primesUpTo T ↔ P.Prime ∧ P ≤ T := by
  simp only [primesUpTo, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.pos, h2⟩, h1⟩

private lemma lam_eq_or' {n : ℕ} (hn : n ≠ 0) : lam n = 1 ∨ lam n = -1 := by
  rw [ArithmeticFunction.liouville_apply hn]
  exact neg_one_pow_eq_or ℤ _

private lemma lam_prime' {p : ℕ} (hp : p.Prime) : lam p = -1 := by
  rw [ArithmeticFunction.liouville_apply hp.ne_zero, ArithmeticFunction.cardFactors_apply_prime hp,
    pow_one]

private lemma lam_two_mul {p : ℕ} (hp : p.Prime) : lam (2 * p) = 1 := by
  rw [ArithmeticFunction.liouville_apply (by have := hp.pos; omega),
    ArithmeticFunction.cardFactors_mul (by norm_num) hp.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp,
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_two]
  norm_num

/-- **The pattern `(−, +)` of the Liouville function occurs in every `[N, 4N]`.** -/
theorem exists_liouville_pattern {N : ℕ} (hN : 1 ≤ N) :
    ∃ n, N ≤ n ∧ n ≤ 4 * N ∧ lam n = -1 ∧ lam (n + 1) = 1 := by
  classical
  obtain ⟨P, hP, hNP, hPN⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  have hex : ∃ m, P < m ∧ lam m = 1 := ⟨2 * P, by have := hP.pos; omega, lam_two_mul hP⟩
  have hspec := Nat.find_spec hex
  have hmin := fun m => Nat.find_min hex (m := m)
  obtain ⟨hlt, hval⟩ := hspec
  obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [hn] at hlt hval
  have hle : Nat.find hex ≤ 2 * P := Nat.find_min' hex ⟨by have := hP.pos; omega, lam_two_mul hP⟩
  have hPn : P ≤ n := by omega
  have hnval : lam n = -1 := by
    rcases eq_or_lt_of_le hPn with h | h
    · rw [← h]
      exact lam_prime' hP
    · have hnot := hmin n (by omega)
      have hn0 : n ≠ 0 := by have := hP.pos; omega
      rcases lam_eq_or' hn0 with h1 | h1
      · exact absurd ⟨h, h1⟩ hnot
      · exact h1
  exact ⟨n, by omega, by omega, hnval, hval⟩

/-- The weight of the parity neutral producer. -/
def neutralWeight (T G n : ℕ) (W a : ℝ) (r : ℕ) : ℝ :=
  mobiusPart T r + W * entangled T G r + a * (mobiusPart T (r / n) - mobiusPart T (r / (n + 1)))

private lemma mobiusPart_zero (T : ℕ) : mobiusPart T 0 = 0 := by
  simp [mobiusPart]

private lemma mobiusPart_div_congr {T G d r s : ℕ} (hd : d ∣ G) (hd0 : 0 < d) (hsr : s ≤ r)
    (h : ∀ P ∈ primesUpTo T, G * P ∣ r - s) : mobiusPart T (r / d) = mobiusPart T (s / d) := by
  refine mobiusPart_congr (Nat.div_le_div_right hsr) fun P hP => ?_
  obtain ⟨g, rfl⟩ := hd
  obtain ⟨t, ht⟩ := h P hP
  have hsub : r - s = d * (g * P * t) := by
    rw [ht]
    ring
  have hr : r = s + d * (g * P * t) := by omega
  rw [hr, Nat.add_mul_div_left _ _ hd0, Nat.add_sub_cancel_left]
  exact ⟨g * t, by ring⟩

private lemma neutralWeight_of_small {T G n r : ℕ} {W a : ℝ} (hn0 : 0 < n) (hn : n ∣ G)
    (hn1 : n + 1 ∣ G) (h : ∀ P ∈ primesUpTo T, r % (G * P) < G) :
    neutralWeight T G n W a r = mobiusPart T (r % G) +
      W * ((primesUpTo T).card : ℝ) * ((r % G : ℕ) : ℝ) +
      a * (mobiusPart T ((r % G) / n) - mobiusPart T ((r % G) / (n + 1))) := by
  have hres : ∀ P ∈ primesUpTo T, r % (G * P) = r % G := by
    intro P hP
    have h1 := Nat.mod_mul_right_mod r G P
    rw [Nat.mod_eq_of_lt (h P hP)] at h1
    exact h1
  have hdvd : ∀ P ∈ primesUpTo T, G * P ∣ r - r % G := by
    intro P hP
    have hd : G * P ∣ r - r % (G * P) := Nat.dvd_sub_mod r
    rwa [hres P hP] at hd
  have hsr := Nat.mod_le r G
  have hcong : mobiusPart T r = mobiusPart T (r % G) :=
    mobiusPart_congr hsr fun P hP => (dvd_mul_left P G).trans (hdvd P hP)
  have hent : entangled T G r = ((primesUpTo T).card : ℝ) * ((r % G : ℕ) : ℝ) := by
    rw [entangled, sum_congr rfl fun P hP => by rw [hres P hP], sum_const, nsmul_eq_mul]
  rw [neutralWeight, hcong, hent, mobiusPart_div_congr hn hn0 hsr hdvd,
    mobiusPart_div_congr hn1 (Nat.succ_pos n) hsr hdvd]
  ring

/-- The near law up to `G`. -/
private lemma near_law {T G y : ℕ} {η Y : ℝ} (hη : 0 ≤ η) (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y)
    (hY : |mobiusHarmonic T| + 2 * η * (1 + Real.log G) ≤ Y) (hy1 : 1 ≤ y) (hyG : y ≤ G) :
    |mobiusPart T y - 1| ≤ (y : ℝ) * Y := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy1
  have hyR : (y : ℝ) ≤ G := by exact_mod_cast hyG
  have hlog : Real.log (y : ℝ) ≤ Real.log G := Real.log_le_log hy0 hyR
  refine (abs_mobiusPart_sub_one_le hy1 hη hM).trans (mul_le_mul_of_nonneg_left (le_trans ?_ hY) hy0.le)
  gcongr

/-- The spike is bounded below by the near law. -/
private lemma spike_ge {T G n s : ℕ} {η Y a : ℝ} (hn0 : 0 < n) (hη : 0 ≤ η)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y)
    (hY : |mobiusHarmonic T| + 2 * η * (1 + Real.log G) ≤ Y) (hY1 : Y ≤ 1) (hsG : s < G) (ha0 : 0 ≤ a)
    (ha1 : a ≤ (n : ℝ) + 1) (hY0 : 0 ≤ Y) :
    -(4 * (s : ℝ) * Y) ≤ a * (mobiusPart T (s / n) - mobiusPart T (s / (n + 1))) := by
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hneg : -(4 * (s : ℝ) * Y) ≤ 0 := by
    have : 0 ≤ 4 * (s : ℝ) * Y := by positivity
    linarith
  by_cases h2 : s / (n + 1) = 0
  · rw [h2, mobiusPart_zero, sub_zero]
    by_cases h1 : s / n = 0
    · rw [h1, mobiusPart_zero, mul_zero]
      exact hneg
    · have hsn : n ≤ s := by
        by_contra hlt
        exact h1 (Nat.div_eq_of_lt (by omega))
      have hsn1 : s < n + 1 := by
        rcases Nat.div_eq_zero_iff.mp h2 with h | h
        · omega
        · exact h
      have hseq : s = n := by omega
      rw [hseq, Nat.div_self hn0]
      have hlaw := near_law (y := 1) hη hM hY le_rfl (by omega)
      have hF := (abs_le.mp hlaw).1
      push_cast at hF
      have : 0 ≤ mobiusPart T 1 := by linarith
      have h5 := mul_nonneg ha0 this
      have h6 : 0 ≤ 4 * (n : ℝ) * Y := by positivity
      linarith
  · have hy2 : 1 ≤ s / (n + 1) := Nat.pos_of_ne_zero h2
    have hy12 : s / (n + 1) ≤ s / n := Nat.div_le_div_left (by omega) hn0
    have hy1 : 1 ≤ s / n := hy2.trans hy12
    have hyG : s / n ≤ G := (Nat.div_le_self s n).trans hsG.le
    have hyG2 : s / (n + 1) ≤ G := hy12.trans hyG
    have h1 := (abs_le.mp (near_law hη hM hY hy1 hyG)).1
    have h3 := (abs_le.mp (near_law hη hM hY hy2 hyG2)).2
    have hyR : ((s / (n + 1) : ℕ) : ℝ) ≤ ((s / n : ℕ) : ℝ) := by exact_mod_cast hy12
    have hdiff : -(2 * ((s / n : ℕ) : ℝ) * Y) ≤
        mobiusPart T (s / n) - mobiusPart T (s / (n + 1)) := by nlinarith
    have hnmul : (n : ℝ) * ((s / n : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.mul_div_le s n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hy0 : (0 : ℝ) ≤ ((s / n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hprod : a * ((s / n : ℕ) : ℝ) ≤ 2 * (s : ℝ) := by
      have ha2 : a ≤ 2 * (n : ℝ) := by linarith
      calc a * ((s / n : ℕ) : ℝ) ≤ (2 * (n : ℝ)) * ((s / n : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right ha2 hy0
        _ = 2 * ((n : ℝ) * ((s / n : ℕ) : ℝ)) := by ring
        _ ≤ _ := by linarith
    have hmul := mul_le_mul_of_nonneg_left hdiff ha0
    have hY2 : a * ((s / n : ℕ) : ℝ) * Y ≤ 2 * (s : ℝ) * Y := mul_le_mul_of_nonneg_right hprod hY0
    nlinarith

/-- **The positivity of the parity neutral weight.** -/
theorem neutralWeight_pos {T G n : ℕ} {W a η Y : ℝ} (hG : 0 < G) (hn0 : 0 < n) (hn : n ∣ G)
    (hn1 : n + 1 ∣ G) (hη : 0 ≤ η) (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y)
    (hY : |mobiusHarmonic T| + 2 * η * (1 + Real.log G) ≤ Y) (hY1 : Y ≤ 1) (ha0 : 0 ≤ a)
    (ha1 : a ≤ (n : ℝ) + 1) (hW : 0 ≤ W) (hZ : 5 * Y ≤ W * ((primesUpTo T).card : ℝ))
    (hpay : (T : ℝ) + 2 * a * T ≤ W * G) (r : ℕ) :
    0 ≤ neutralWeight T G n W a r ∧ (r ∈ Ico 1 G → 1 ≤ neutralWeight T G n W a r) := by
  have hY0 : 0 ≤ Y := le_trans (by positivity) hY
  -- The near range.
  have hnear : ∀ s : ℕ, 1 ≤ s → s < G → 1 ≤ mobiusPart T s +
      W * ((primesUpTo T).card : ℝ) * (s : ℝ) +
      a * (mobiusPart T (s / n) - mobiusPart T (s / (n + 1))) := by
    intro s hs1 hsG
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have h1 := (abs_le.mp (near_law hη hM hY hs1 hsG.le)).1
    have h2 := spike_ge hn0 hη hM hY hY1 hsG ha0 ha1 hY0
    have h3 : 5 * Y * (s : ℝ) ≤ W * ((primesUpTo T).card : ℝ) * (s : ℝ) :=
      mul_le_mul_of_nonneg_right hZ hs0
    nlinarith
  by_cases hsmall : ∀ P ∈ primesUpTo T, r % (G * P) < G
  · rw [neutralWeight_of_small hn0 hn hn1 hsmall]
    constructor
    · by_cases hs : 1 ≤ r % G
      · have := hnear _ hs (Nat.mod_lt r hG)
        linarith
      · have hs0 : r % G = 0 := by omega
        rw [hs0]
        simp [mobiusPart_zero]
    · intro hr
      obtain ⟨hr1, hrG⟩ := mem_Ico.mp hr
      have hmod : r % G = r := Nat.mod_eq_of_lt hrG
      rw [hmod]
      exact hnear r hr1 hrG
  · refine ⟨?_, fun hr => ?_⟩
    · push Not at hsmall
      obtain ⟨P, hP, hlarge⟩ := hsmall
      have hent : (G : ℝ) ≤ entangled T G r := by
        have h1 : ((r % (G * P) : ℕ) : ℝ) ≤ entangled T G r :=
          Finset.single_le_sum (f := fun Q => ((r % (G * Q) : ℕ) : ℝ))
            (fun _ _ => Nat.cast_nonneg _) hP
        have h2 : (G : ℝ) ≤ ((r % (G * P) : ℕ) : ℝ) := by exact_mod_cast hlarge
        linarith
      have h1 := mul_le_mul_of_nonneg_left hent hW
      have h2 := abs_le.mp (abs_mobiusPart_le T r)
      have h3 := abs_le.mp (abs_mobiusPart_le T (r / n))
      have h4 := abs_le.mp (abs_mobiusPart_le T (r / (n + 1)))
      have h5 : -(2 * a * T) ≤ a * (mobiusPart T (r / n) - mobiusPart T (r / (n + 1))) := by nlinarith
      rw [neutralWeight]
      linarith
    · exfalso
      obtain ⟨_, hrG⟩ := mem_Ico.mp hr
      refine hsmall fun P hP => ?_
      have hPpos : 0 < P := (mem_primesUpTo_iff'.mp hP).1.pos
      have hle : G ≤ G * P := Nat.le_mul_of_pos_right G hPpos
      rw [Nat.mod_eq_of_lt (by omega)]
      exact hrG

/-- The squarefree near letters. -/
private def nearLetters (T : ℕ) : Finset ℕ :=
  (Icc 2 T).filter fun b => ArithmeticFunction.moebius b ≠ 0

/-- The near weights `−μ(b)/b`. -/
private def nearWeights (b : ℕ) : ℚ := -(ArithmeticFunction.moebius b : ℚ) / b

/-- The entangled letters. -/
private def farLetters (T G : ℕ) : Finset ℕ := (primesUpTo T).image (G * ·)

private lemma sum_nearLetters_mod (T r : ℕ) :
    ∑ b ∈ nearLetters T, ((nearWeights b : ℚ) : ℝ) * ((r % b : ℕ) : ℝ) = mobiusPart T r := by
  have hsub : nearLetters T ⊆ Icc 1 T := fun b hb => by
    have := mem_Icc.mp (mem_filter.mp hb).1
    exact mem_Icc.mpr ⟨by omega, this.2⟩
  rw [mobiusPart, ← sum_subset hsub (fun b hb hb' => ?_)]
  · refine sum_congr rfl fun b _ => ?_
    simp only [nearWeights]
    push_cast
    rfl
  · obtain ⟨hb1, hbT⟩ := mem_Icc.mp hb
    by_cases h1 : b = 1
    · subst h1
      simp [Nat.mod_one]
    · have hμ : ArithmeticFunction.moebius b = 0 := by
        by_contra hμ
        exact hb' (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hbT⟩, hμ⟩)
      simp [hμ]

private lemma sum_nearLetters_log (T : ℕ) :
    ∑ b ∈ nearLetters T, ((nearWeights b : ℚ) : ℝ) * Real.log b = mobiusSlope T := by
  have hsub : nearLetters T ⊆ Icc 1 T := fun b hb => by
    have := mem_Icc.mp (mem_filter.mp hb).1
    exact mem_Icc.mpr ⟨by omega, this.2⟩
  rw [mobiusSlope, ← sum_subset hsub (fun b hb hb' => ?_)]
  · refine sum_congr rfl fun b _ => ?_
    simp only [nearWeights]
    push_cast
    rfl
  · obtain ⟨hb1, hbT⟩ := mem_Icc.mp hb
    by_cases h1 : b = 1
    · subst h1
      simp
    · have hμ : ArithmeticFunction.moebius b = 0 := by
        by_contra hμ
        exact hb' (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hbT⟩, hμ⟩)
      simp [hμ]

/-- The parity mass of the near letters. -/
private def nearParity (T : ℕ) : ℚ :=
  ∑ b ∈ nearLetters T, nearWeights b * (1 - (lam b : ℚ))

/-- The parity mass of the entangled letters, per unit of weight. -/
private def farParity (T G : ℕ) : ℚ := ∑ k ∈ farLetters T G, (1 - (lam k : ℚ))

private lemma near_term_nonneg {b : ℕ} (hb : b ∈ nearLetters T) :
    0 ≤ nearWeights b * (1 - (lam b : ℚ)) := by
  obtain ⟨hI, hμ⟩ := mem_filter.mp hb
  have hb2 := (mem_Icc.mp hI).1
  have hb0 : b ≠ 0 := by omega
  have hsq : Squarefree b := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hμ
  have heq : ArithmeticFunction.moebius b = lam b := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, ArithmeticFunction.liouville_apply hb0]
  have hbQ : (0 : ℚ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb0
  rw [nearWeights, heq]
  rcases lam_eq_or' hb0 with h | h <;> rw [h] <;> push_cast <;> norm_num <;> positivity

private lemma one_le_nearParity {T : ℕ} (hT : 2 ≤ T) : 1 ≤ nearParity T := by
  have h2 : 2 ∈ nearLetters T := by
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hT⟩, ?_⟩
    rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  have hle := single_le_sum (f := fun b => nearWeights b * (1 - (lam b : ℚ)))
    (fun b hb => near_term_nonneg hb) h2
  refine le_trans (le_of_eq ?_) hle
  simp only [nearWeights]
  rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two, lam_prime' Nat.prime_two]
  norm_num

private lemma far_card_le {T G : ℕ} : (farLetters T G).card ≤ (primesUpTo T).card := card_image_le

private lemma farParity_bounds (T G : ℕ) (hG : 0 < G) :
    0 ≤ farParity T G ∧ farParity T G ≤ 2 * ((primesUpTo T).card : ℚ) := by
  have hk0 : ∀ k ∈ farLetters T G, k ≠ 0 := by
    intro k hk
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hk
    exact Nat.mul_ne_zero hG.ne' (mem_primesUpTo_iff'.mp hP).1.ne_zero
  have hbound : ∀ k ∈ farLetters T G, 0 ≤ (1 - (lam k : ℚ)) ∧ (1 - (lam k : ℚ)) ≤ 2 := by
    intro k hk
    rcases lam_eq_or' (hk0 k hk) with h | h <;> rw [h] <;> norm_num
  refine ⟨sum_nonneg fun k hk => (hbound k hk).1, ?_⟩
  calc farParity T G ≤ ∑ _k ∈ farLetters T G, (2 : ℚ) := sum_le_sum fun k hk => (hbound k hk).2
    _ = ((farLetters T G).card : ℚ) * 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((primesUpTo T).card : ℚ) * 2 := by
        have : ((farLetters T G).card : ℚ) ≤ ((primesUpTo T).card : ℚ) := by
          exact_mod_cast far_card_le
        gcongr
    _ = _ := by ring

/-- The parity balance read from the weights. -/
theorem parityBalance_of_weights {c : ℕ →₀ ℤ} {D : ℕ} {J : Finset ℕ} {q : ℕ → ℚ} (hbal : IsBalanced c)
    (hJ2 : ∀ k ∈ J, 2 ≤ k) (hsupp : c.support ⊆ insert 1 J)
    (hletter : ∀ k ∈ J, (c k : ℝ) = -(D : ℝ) * k * (q k : ℝ)) :
    parityBalance c = (D : ℝ) * ∑ k ∈ J, (q k : ℝ) * (1 - (lam k : ℝ)) := by
  have h1 : 1 ∉ J := fun hmem => by
    have := hJ2 1 hmem
    omega
  rw [parityBalance_eq_weights hbal,
    sum_subset hsupp (fun k _ hk => by
      rw [Finsupp.notMem_support_iff.mp hk]
      simp),
    sum_insert h1, mul_sum]
  have hone : lam 1 = 1 := by
    rw [ArithmeticFunction.liouville_apply one_ne_zero]
    simp
  rw [hone]
  simp only [Int.cast_one, sub_self, mul_zero, zero_add]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : (k : ℝ) ≠ 0 := by
    have := hJ2 k hk
    exact Nat.cast_ne_zero.mpr (by omega)
  rw [hletter k hk]
  field_simp

private lemma exists_nat_ratio {x : ℚ} (hx : 0 ≤ x) : ∃ p q : ℕ, 0 < q ∧ ((x : ℚ) : ℝ) = (p : ℝ) / q := by
  refine ⟨x.num.toNat, x.den, x.pos, ?_⟩
  have hnum : ((x.num.toNat : ℕ) : ℤ) = x.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hx)
  have hcast : ((x.num.toNat : ℕ) : ℝ) = ((x.num : ℤ) : ℝ) := by exact_mod_cast hnum
  rw [hcast, Rat.cast_def]

private lemma stepWeight_neg (c : ℕ →₀ ℤ) (r : ℕ) : stepWeight (-c) r = -stepWeight c r := by
  have h := stepWeight_add c (-c) r
  rw [add_neg_cancel] at h
  have h0 : stepWeight (0 : ℕ →₀ ℤ) r = 0 := by simp [stepWeight]
  rw [h0] at h
  linarith

private lemma stencilSlope_neg (c : ℕ →₀ ℤ) : stencilSlope (-c) = -stencilSlope c := by
  have h := stencilSlope_add c (-c)
  rw [add_neg_cancel] at h
  have h0 : stencilSlope (0 : ℕ →₀ ℤ) = 0 := by simp [stencilSlope]
  rw [h0] at h
  linarith

private lemma parityBalance_neg (c : ℕ →₀ ℤ) : parityBalance (-c) = -parityBalance c := by
  have h := parityBalance_add c (-c)
  rw [add_neg_cancel] at h
  have h0 : parityBalance (0 : ℕ →₀ ℤ) = 0 := by simp [parityBalance]
  rw [h0] at h
  linarith

private lemma isBalanced_neg {c : ℕ →₀ ℤ} (h : IsBalanced c) : IsBalanced (-c) := by
  have hb : ∑ k ∈ c.support, (c k : ℝ) / k = 0 := h
  change ∑ k ∈ (-c).support, (((-c) k : ℤ) : ℝ) / k = 0
  rw [Finsupp.support_neg]
  have : ∑ k ∈ c.support, (((-c) k : ℤ) : ℝ) / k = -∑ k ∈ c.support, (c k : ℝ) / k := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp [neg_div]
  rw [this, hb, neg_zero]

private lemma alphabet_add {c d : ℕ →₀ ℤ} {K : ℕ} (hc : AlphabetLE c K) (hd : AlphabetLE d K) :
    AlphabetLE (c + d) K := fun k hk => by
  classical
  rcases mem_union.mp (Finsupp.support_add hk) with h | h
  · exact hc k h
  · exact hd k h

private lemma alphabet_nsmul {c : ℕ →₀ ℤ} {K : ℕ} (hc : AlphabetLE c K) (a : ℕ) :
    AlphabetLE (a • c) K := fun k hk => by
  refine hc k (Finsupp.mem_support_iff.mpr fun h0 => ?_)
  exact Finsupp.mem_support_iff.mp hk (by simp [h0])

private lemma alphabet_neg {c : ℕ →₀ ℤ} {K : ℕ} (hc : AlphabetLE c K) : AlphabetLE (-c) K := by
  intro k hk
  rw [Finsupp.support_neg] at hk
  exact hc k hk

private lemma alphabet_dilate {c : ℕ →₀ ℤ} {K j L : ℕ} (hc : AlphabetLE c K) (hL : j * K ≤ L) :
    AlphabetLE (dilate j c) L := fun k hk => by
  classical
  obtain ⟨b, hb, rfl⟩ := mem_image.mp (Finsupp.mapDomain_support hk)
  exact (Nat.mul_le_mul_left j (hc b hb)).trans hL

/-- The near coefficient `Z = π(T) T (2n + 3)/G` of the parity neutral producer. -/
def neutralCoefficient (T G n : ℕ) : ℝ := (T : ℝ) * (2 * (n : ℝ) + 3) / G * ((primesUpTo T).card : ℝ)

/-- The real arithmetic of the rate of the parity neutral producer. -/
private lemma neutral_rate_core {sT sf W a Z Y Q n TG d L : ℝ} (hn : 1 ≤ n) (ha0 : 0 ≤ a) (ha1 : a ≤ n + 1)
    (hZ0 : 0 ≤ Z) (hd1 : 1 / 2 ≤ d) (hd2 : d ≤ 1) (hL1 : 1 ≤ L) (hQ0 : 0 ≤ Q) (hQ : Q ≤ L)
    (hY : Y ≤ Z / 5) (hY0 : 0 ≤ Y) (hTG : TG ≤ Z) (hs : sT ≤ d + Y * Q + TG) (hsf : W * sf ≤ Z * (L - 1)) :
    (sT + W * sf + a * sT * (1 / n - 1 / (n + 1)) - d) / d ≤ 8 * Z * L + 2 / n := by
  have hn0 : 0 < n := by linarith
  have hkey : 1 / n - 1 / (n + 1) = 1 / (n * (n + 1)) := by
    field_simp
    ring
  have hκ : 0 < 1 / (n * (n + 1)) := by positivity
  have hYQ : Y * Q ≤ Z / 5 * L := mul_le_mul hY hQ hQ0 (by positivity)
  have hZL : Z ≤ Z * L := by nlinarith
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = 1 + Z / 5 * L + Z := ⟨_, rfl⟩
  have hsB : sT ≤ B₀ := by rw [hB₀]; linarith
  have hB0 : 0 ≤ B₀ := by rw [hB₀]; positivity
  have hspike : a * sT * (1 / n - 1 / (n + 1)) ≤ B₀ / n := by
    rw [hkey]
    have h1 : a * sT ≤ (n + 1) * B₀ := by
      calc a * sT ≤ a * B₀ := mul_le_mul_of_nonneg_left hsB ha0
        _ ≤ (n + 1) * B₀ := mul_le_mul_of_nonneg_right ha1 hB0
    calc a * sT * (1 / (n * (n + 1))) ≤ (n + 1) * B₀ * (1 / (n * (n + 1))) :=
          mul_le_mul_of_nonneg_right h1 hκ.le
      _ = B₀ / n := by field_simp
  have hBn : B₀ / n ≤ 1 / n + 6 / 5 * (Z * L) := by
    have h1 : (Z / 5 * L + Z) / n ≤ Z / 5 * L + Z := div_le_self (by positivity) hn
    have h2 : B₀ / n = 1 / n + (Z / 5 * L + Z) / n := by
      rw [hB₀]
      ring
    rw [h2]
    linarith
  have hnum : sT + W * sf + a * sT * (1 / n - 1 / (n + 1)) - d ≤ 12 / 5 * (Z * L) + 1 / n := by linarith
  have hd0 : 0 < d := by linarith
  have h1n : 0 < 1 / n := by positivity
  have hZLpos : 0 ≤ Z * L := by positivity
  rw [div_le_iff₀ hd0]
  have hgoal : 12 / 5 * (Z * L) + 1 / n ≤ (8 * Z * L + 2 / n) * d := by
    have h2n : 2 / n = 2 * (1 / n) := by ring
    rw [h2n]
    nlinarith
  linarith

/-- The near stencil, with multiplicity `D F_T`. -/
private lemma exists_near_stencil {T : ℕ} (hT : 1 ≤ T) :
    ∃ (cb : ℕ →₀ ℤ) (Db : ℕ), 0 < Db ∧ cb 0 = 0 ∧ IsBalanced cb ∧
      (∀ r, (stepWeight cb r : ℝ) = (Db : ℝ) * mobiusPart T r) ∧
      stencilSlope cb = (Db : ℝ) * mobiusSlope T ∧
      parityBalance cb = (Db : ℝ) * ((nearParity T : ℚ) : ℝ) ∧ AlphabetLE cb T := by
  have hJ : ∀ k ∈ nearLetters T, 2 ≤ k := fun k hk => (mem_Icc.mp (mem_filter.mp hk).1).1
  obtain ⟨cb, Db, hDb, hb0, hbbal, hbstep, hbslope, hbsupp, hbletter⟩ :=
    exists_stencil_of_weights nearWeights hJ
  refine ⟨cb, Db, hDb, hb0, hbbal, fun r => ?_, ?_, ?_, fun k hk => ?_⟩
  · rw [hbstep, sum_nearLetters_mod]
  · rw [hbslope, sum_nearLetters_log]
  · rw [parityBalance_of_weights hbbal hJ hbsupp hbletter, nearParity]
    push_cast
    rfl
  · rcases mem_insert.mp (hbsupp hk) with h | h
    · omega
    · exact (mem_Icc.mp (mem_filter.mp h).1).2

/-- The entangled stencil, with multiplicity `D Σ_P (r mod G P)`. -/
private lemma exists_far_stencil {T G : ℕ} (hG2 : 2 ≤ G) (hT : 1 ≤ T) :
    ∃ (cf : ℕ →₀ ℤ) (Df : ℕ), 0 < Df ∧ cf 0 = 0 ∧ IsBalanced cf ∧
      (∀ r, (stepWeight cf r : ℝ) = (Df : ℝ) * entangled T G r) ∧
      stencilSlope cf = (Df : ℝ) * ∑ P ∈ primesUpTo T, Real.log ((G * P : ℕ) : ℝ) ∧
      parityBalance cf = (Df : ℝ) * ((farParity T G : ℚ) : ℝ) ∧ AlphabetLE cf (G * T) := by
  classical
  have hG0 : 0 < G := by omega
  have hJ : ∀ k ∈ farLetters T G, 2 ≤ k := by
    intro k hk
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hk
    exact hG2.trans (Nat.le_mul_of_pos_right G (mem_primesUpTo_iff'.mp hP).1.pos)
  obtain ⟨cf, Df, hDf, hf0, hfbal, hfstep, hfslope, hfsupp, hfletter⟩ :=
    exists_stencil_of_weights (J := farLetters T G) (fun _ => 1) hJ
  have hinj : Set.InjOn (G * ·) (primesUpTo T : Set ℕ) := fun _ _ _ _ h =>
    Nat.eq_of_mul_eq_mul_left hG0 h
  refine ⟨cf, Df, hDf, hf0, hfbal, fun r => ?_, ?_, ?_, fun k hk => ?_⟩
  · rw [hfstep, farLetters, sum_image hinj, entangled]
    simp
  · rw [hfslope, farLetters, sum_image hinj]
    simp
  · rw [parityBalance_of_weights hfbal hJ hfsupp hfletter, farParity]
    push_cast
    simp
  · rcases mem_insert.mp (hfsupp hk) with h | h
    · have := Nat.mul_pos hG0 (by omega : 0 < T)
      omega
    · obtain ⟨P, hP', rfl⟩ := mem_image.mp h
      exact Nat.mul_le_mul_left G (mem_primesUpTo_iff'.mp hP').2

/-- Clearing the denominators of the two rational weights. -/
private lemma exists_clearing {Db Df : ℕ} (hDb : 0 < Db) (hDf : 0 < Df) {W a : ℚ} (hW0 : 0 ≤ W) (ha0 : 0 ≤ a) :
    ∃ E₁ E₂ E₃ m : ℕ, 0 < m ∧ (E₁ : ℝ) * Db = m ∧ (E₂ : ℝ) * Df = (m : ℝ) * (W : ℝ) ∧
      (E₃ : ℝ) * Db = (m : ℝ) * (a : ℝ) := by
  obtain ⟨w₁, w₂, hw₂, hwr⟩ := exists_nat_ratio hW0
  obtain ⟨a₁, a₂, ha₂, har⟩ := exists_nat_ratio ha0
  have hw₂R : (w₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hw₂.ne'
  have ha₂R : (a₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha₂.ne'
  refine ⟨Df * w₂ * a₂, Db * w₁ * a₂, Df * w₂ * a₁, Db * Df * w₂ * a₂, by positivity, ?_, ?_, ?_⟩
  · push_cast
    ring
  · rw [hwr]
    push_cast
    field_simp
  · rw [har]
    push_cast
    field_simp

/-- The combined stencil `E₁ c_b + E₂ c_f + E₃ (T_n c_b − T_{n+1} c_b)`. -/
private def combined (cb cf : ℕ →₀ ℤ) (E₁ E₂ E₃ n : ℕ) : ℕ →₀ ℤ :=
  E₁ • cb + E₂ • cf + E₃ • dilate n cb + -(E₃ • dilate (n + 1) cb)

private lemma stepWeight_combined (cb cf : ℕ →₀ ℤ) (E₁ E₂ E₃ n r : ℕ) :
    (stepWeight (combined cb cf E₁ E₂ E₃ n) r : ℝ) =
      (E₁ : ℝ) * (stepWeight cb r : ℝ) + (E₂ : ℝ) * (stepWeight cf r : ℝ) +
        (E₃ : ℝ) * (stepWeight cb (r / n) : ℝ) - (E₃ : ℝ) * (stepWeight cb (r / (n + 1)) : ℝ) := by
  simp only [combined, stepWeight_add, stepWeight_neg, stepWeight_nsmul, stepWeight_dilate]
  push_cast
  ring

private lemma isBalanced_combined {cb cf : ℕ →₀ ℤ} (hb : IsBalanced cb) (hf : IsBalanced cf)
    (E₁ E₂ E₃ : ℕ) {n : ℕ} (hn0 : 0 < n) : IsBalanced (combined cb cf E₁ E₂ E₃ n) :=
  isBalanced_add (isBalanced_add (isBalanced_add (isBalanced_nsmul hb _)
    (isBalanced_nsmul hf _)) (isBalanced_nsmul (isBalanced_dilate hn0 hb) _))
    (isBalanced_neg (isBalanced_nsmul (isBalanced_dilate (Nat.succ_pos n) hb) _))

private lemma parityBalance_combined {cb cf : ℕ →₀ ℤ} (hb0 : cb 0 = 0) (E₁ E₂ E₃ : ℕ) {n : ℕ} (hn0 : 0 < n)
    (hodd : lam n = -1) (heven : lam (n + 1) = 1) :
    parityBalance (combined cb cf E₁ E₂ E₃ n) =
      (E₁ : ℝ) * parityBalance cb + (E₂ : ℝ) * parityBalance cf -
        (E₃ : ℝ) * ((1 / (n : ℝ) + 1 / ((n : ℝ) + 1)) * parityBalance cb) := by
  simp only [combined, parityBalance_add, parityBalance_neg, parityBalance_nsmul,
    parityBalance_dilate hn0 hb0, parityBalance_dilate (Nat.succ_pos n) hb0, hodd, heven]
  push_cast
  ring

private lemma stencilSlope_combined {cb cf : ℕ →₀ ℤ} (hb0 : cb 0 = 0) (hb : IsBalanced cb) (E₁ E₂ E₃ : ℕ)
    {n : ℕ} (hn0 : 0 < n) :
    stencilSlope (combined cb cf E₁ E₂ E₃ n) =
      (E₁ : ℝ) * stencilSlope cb + (E₂ : ℝ) * stencilSlope cf +
        (E₃ : ℝ) * (stencilSlope cb * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by
  simp only [combined, stencilSlope_add, stencilSlope_neg, stencilSlope_nsmul,
    stencilSlope_dilate hn0 hb0 hb, stencilSlope_dilate (Nat.succ_pos n) hb0 hb]
  push_cast
  ring

/-- The rational weight `a` that makes the parity balance vanish. -/
private lemma exists_neutral_ratio {T G n : ℕ} (hT : 2 ≤ T) (hG0 : 0 < G) (hn0 : 0 < n) {W : ℚ} (hW0 : 0 ≤ W)
    (hZQ : 2 * (W * ((primesUpTo T).card : ℚ)) ≤ 1) :
    ∃ a : ℚ, 0 ≤ a ∧ a ≤ (n : ℚ) + 1 ∧
      a * ((1 / (n : ℚ) + 1 / ((n : ℚ) + 1)) * nearParity T) = nearParity T + W * farParity T G := by
  have hi1 := one_le_nearParity hT
  obtain ⟨hf0, hf2⟩ := farParity_bounds T G hG0
  have hi0 : 0 < nearParity T := by linarith
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn0
  have hWf : W * farParity T G ≤ nearParity T := by
    calc W * farParity T G ≤ W * (2 * ((primesUpTo T).card : ℚ)) := mul_le_mul_of_nonneg_left hf2 hW0
      _ = 2 * (W * ((primesUpTo T).card : ℚ)) := by ring
      _ ≤ 1 := hZQ
      _ ≤ _ := hi1
  have hν0 : 0 < 1 / (n : ℚ) + 1 / ((n : ℚ) + 1) := by positivity
  have hνi : 0 < (1 / (n : ℚ) + 1 / ((n : ℚ) + 1)) * nearParity T := mul_pos hν0 hi0
  refine ⟨(nearParity T + W * farParity T G) / ((1 / (n : ℚ) + 1 / ((n : ℚ) + 1)) * nearParity T),
    div_nonneg (by positivity) hνi.le, ?_, by field_simp⟩
  rw [div_le_iff₀ hνi]
  have hν2 : 2 ≤ ((n : ℚ) + 1) * (1 / (n : ℚ) + 1 / ((n : ℚ) + 1)) := by
    have hn00 : (0 : ℚ) < n := by linarith
    field_simp
    nlinarith
  nlinarith

/-- The rate of a stencil built with the slope of the neutral family. -/
private lemma neutral_rate_le {T G n : ℕ} {η Y : ℝ} {W a : ℝ} (hT : 2 ≤ T) (hTG : T < G) (hn0 : 0 < n)
    (hη : 0 ≤ η) (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y)
    (hY : |mobiusHarmonic T| + 2 * η * (1 + Real.log G) ≤ Y) (ha0 : 0 ≤ a) (ha1 : a ≤ (n : ℝ) + 1)
    (hW0 : 0 ≤ W) (hWR : W = (T : ℝ) * (2 * (n : ℝ) + 3) / G)
    (hZ : 5 * Y ≤ neutralCoefficient T G n) {c : ℕ →₀ ℤ} {m : ℕ} (hm : 0 < m)
    (hslope : stencilSlope c = (m : ℝ) * (mobiusSlope T + W * ∑ P ∈ primesUpTo T, Real.log ((G * P : ℕ) : ℝ) +
      a * mobiusSlope T * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))) :
    rate c m G ≤ 8 * neutralCoefficient T G n * (1 + Real.log ((G * T : ℕ) : ℝ)) + 2 / n := by
  have hG0 : 0 < G := by omega
  have hG2 : 2 ≤ G := by omega
  have hGR : (0 : ℝ) < G := by exact_mod_cast hG0
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hπ1 : (1 : ℝ) ≤ ((primesUpTo T).card : ℝ) := by
    have h2 : 2 ∈ primesUpTo T := mem_primesUpTo_iff'.mpr ⟨Nat.prime_two, hT⟩
    have : 0 < (primesUpTo T).card := card_pos.mpr ⟨2, h2⟩
    exact_mod_cast this
  have hZdef : neutralCoefficient T G n = W * ((primesUpTo T).card : ℝ) := by
    rw [neutralCoefficient, hWR]
  obtain ⟨sf, hsfdef⟩ : ∃ sf, sf = ∑ P ∈ primesUpTo T, Real.log ((G * P : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hsfdef] at hslope
  obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = 1 - 1 / (G : ℝ) := ⟨_, rfl⟩
  have hG2R : (2 : ℝ) ≤ G := by exact_mod_cast hG2
  have hd1 : 1 / 2 ≤ d := by
    have : 1 / (G : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hG2R
    rw [hddef]
    linarith
  have hd2 : d ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / (G : ℝ) := by positivity
    rw [hddef]
    linarith
  have hd0 : 0 < d := by linarith
  have hrate : rate c m G = (mobiusSlope T + W * sf +
      a * mobiusSlope T * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) - d) / d := by
    rw [rate, normSlope, hslope, ← hddef, mul_div_mul_left _ _ hmR.ne', div_sub_one hd0.ne']
  rw [hrate]
  have hGT1 : 1 ≤ G * T := Nat.mul_pos hG0 (by omega)
  have hGT0 : (1 : ℝ) ≤ ((G * T : ℕ) : ℝ) := by exact_mod_cast hGT1
  have hlogGT : 0 ≤ Real.log ((G * T : ℕ) : ℝ) := Real.log_nonneg hGT0
  have hlogG : Real.log (G : ℝ) ≤ Real.log ((G * T : ℕ) : ℝ) := by
    refine Real.log_le_log hGR ?_
    exact_mod_cast Nat.le_mul_of_pos_right G (by omega : 0 < T)
  have hlogG0 : 0 ≤ Real.log (G : ℝ) := Real.log_nonneg (by linarith)
  have hZ0 : 0 ≤ neutralCoefficient T G n := by rw [hZdef]; positivity
  have hY0 : 0 ≤ Y := le_trans (by positivity) hY
  have hslT := mobiusSlope_le (T := T) (G := G) hG2 hη hM
  have hs : mobiusSlope T ≤ d + Y * (1 + Real.log (G : ℝ)) + (T : ℝ) / G := by
    rw [hddef]
    have := mul_le_mul_of_nonneg_right hY (by positivity : 0 ≤ 1 + Real.log (G : ℝ))
    linarith
  have hTG' : (T : ℝ) / G ≤ neutralCoefficient T G n := by
    rw [hZdef, hWR]
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have h1 : (T : ℝ) / G ≤ (T : ℝ) * (2 * (n : ℝ) + 3) / G := by
      apply div_le_div_of_nonneg_right _ hGR.le
      nlinarith
    have h2 : (T : ℝ) * (2 * (n : ℝ) + 3) / G ≤
        (T : ℝ) * (2 * (n : ℝ) + 3) / G * ((primesUpTo T).card : ℝ) :=
      le_mul_of_one_le_right (by positivity) hπ1
    linarith
  have hsf : W * sf ≤ neutralCoefficient T G n * Real.log ((G * T : ℕ) : ℝ) := by
    rw [hZdef, hsfdef, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hW0
    calc ∑ P ∈ primesUpTo T, Real.log ((G * P : ℕ) : ℝ)
        ≤ ∑ _P ∈ primesUpTo T, Real.log ((G * T : ℕ) : ℝ) := by
          refine sum_le_sum fun P hP => ?_
          obtain ⟨hpr, hle⟩ := mem_primesUpTo_iff'.mp hP
          refine Real.log_le_log ?_ ?_
          · exact_mod_cast Nat.mul_pos hG0 hpr.pos
          · exact_mod_cast Nat.mul_le_mul_left G hle
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  exact neutral_rate_core (sT := mobiusSlope T) (sf := sf) (W := W) (a := a)
    (Z := neutralCoefficient T G n) (Y := Y) (Q := 1 + Real.log (G : ℝ)) (n := (n : ℝ))
    (TG := (T : ℝ) / G) (d := d) (L := 1 + Real.log ((G * T : ℕ) : ℝ)) hnR ha0 ha1 hZ0 hd1 hd2
    (by linarith) (by linarith) (by linarith) (by linarith) hY0 hTG' hs (by
      have : 1 + Real.log ((G * T : ℕ) : ℝ) - 1 = Real.log ((G * T : ℕ) : ℝ) := by ring
      rw [this]
      exact hsf)

/-- **The parity neutral Möbius producer.** With a Liouville pattern at `n`, `n (n + 1) ∣ G`, and the near condition `5 Q ≤ Z`,
there is an integer producer of parity balance `0` on the alphabet `[1, G T]` of rate at most `8 Z (1 + log (G T)) + 2/n`. -/
theorem exists_neutral_producer {T G n : ℕ} {η Y : ℝ} (hT : 2 ≤ T) (hTG : T < G) (hn0 : 0 < n) (hn : n ∣ G)
    (hn1 : n + 1 ∣ G) (hodd : lam n = -1) (heven : lam (n + 1) = 1) (hη : 0 ≤ η)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y)
    (hY : |mobiusHarmonic T| + 2 * η * (1 + Real.log G) ≤ Y) (hY1 : Y ≤ 1)
    (hZ : 5 * Y ≤ neutralCoefficient T G n) (hZ1 : 2 * neutralCoefficient T G n ≤ 1) :
    ∃ (c : ℕ →₀ ℤ) (m : ℕ), IsProducer c m G ∧ parityBalance c = 0 ∧ AlphabetLE c (G * T) ∧
      rate c m G ≤ 8 * neutralCoefficient T G n * (1 + Real.log ((G * T : ℕ) : ℝ)) + 2 / n := by
  have hG0 : 0 < G := by omega
  have hG2 : 2 ≤ G := by omega
  obtain ⟨W, hWdef⟩ : ∃ W : ℚ, W = (T : ℚ) * (2 * (n : ℚ) + 3) / G := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have hWR : (W : ℝ) = (T : ℝ) * (2 * (n : ℝ) + 3) / G := by rw [hWdef]; push_cast; rfl
  have hZdef : neutralCoefficient T G n = (W : ℝ) * ((primesUpTo T).card : ℝ) := by
    rw [neutralCoefficient, hWR]
  have hZQ : 2 * (W * ((primesUpTo T).card : ℚ)) ≤ 1 := by
    have : ((2 * (W * ((primesUpTo T).card : ℚ)) : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by
      push_cast
      rw [hZdef] at hZ1
      exact hZ1
    exact_mod_cast this
  obtain ⟨a, ha0, ha1, haeq⟩ := exists_neutral_ratio (G := G) hT hG0 hn0 hW0 hZQ
  have ha0R : (0 : ℝ) ≤ a := by exact_mod_cast ha0
  have ha1R : (a : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast ha1
  have hW0R : (0 : ℝ) ≤ W := by exact_mod_cast hW0
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hpay : (T : ℝ) + 2 * (a : ℝ) * T ≤ (W : ℝ) * G := by
    have hGR : (0 : ℝ) < G := by exact_mod_cast hG0
    have h1 : (W : ℝ) * G = (T : ℝ) * (2 * (n : ℝ) + 3) := by
      rw [hWR]
      field_simp
    rw [h1]
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    nlinarith
  have hpos := fun r => neutralWeight_pos (T := T) (G := G) (n := n) (W := W) (a := a) hG0 hn0 hn hn1 hη hM
    hY hY1 ha0R ha1R hW0R (by rw [← hZdef]; exact hZ) hpay r
  obtain ⟨cb, Db, hDb, hb0, hbbal, hbstep, hbslope, hbpar, hbal_T⟩ :=
    exists_near_stencil (T := T) (by omega)
  obtain ⟨cf, Df, hDf, hf0, hfbal, hfstep, hfslope, hfpar, hfal⟩ :=
    exists_far_stencil (T := T) hG2 (by omega)
  obtain ⟨E₁, E₂, E₃, m, hm0, hE₁m, hE₂m, hE₃m⟩ := exists_clearing hDb hDf hW0 ha0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hweight : ∀ r, (stepWeight (combined cb cf E₁ E₂ E₃ n) r : ℝ) =
      (m : ℝ) * neutralWeight T G n W a r := by
    intro r
    rw [stepWeight_combined, hbstep, hfstep, hbstep, hbstep, neutralWeight]
    calc _ = ((E₁ : ℝ) * Db) * mobiusPart T r + ((E₂ : ℝ) * Df) * entangled T G r +
          ((E₃ : ℝ) * Db) * (mobiusPart T (r / n) - mobiusPart T (r / (n + 1))) := by ring
      _ = _ := by
          rw [hE₁m, hE₂m, hE₃m]
          ring
  have hzero : combined cb cf E₁ E₂ E₃ n 0 = 0 := by
    simp [combined, hb0, hf0, dilate_zero hn0 hb0, dilate_zero (Nat.succ_pos n) hb0]
  have hP : IsProducer (combined cb cf E₁ E₂ E₃ n) m G := by
    refine ⟨hzero, isBalanced_combined hbbal hfbal _ _ _ hn0, fun r => ?_, hm0, hG2, fun r hr => ?_⟩
    · have hR : (0 : ℝ) ≤ (stepWeight (combined cb cf E₁ E₂ E₃ n) r : ℝ) := by
        rw [hweight]
        exact mul_nonneg hmR.le (hpos r).1
      exact_mod_cast hR
    · have hR : ((m : ℤ) : ℝ) ≤ (stepWeight (combined cb cf E₁ E₂ E₃ n) r : ℝ) := by
        rw [hweight]
        push_cast
        calc (m : ℝ) = (m : ℝ) * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left ((hpos r).2 hr) hmR.le
      exact_mod_cast hR
  have haeqR : (a : ℝ) * ((1 / (n : ℝ) + 1 / ((n : ℝ) + 1)) * ((nearParity T : ℚ) : ℝ)) =
      ((nearParity T : ℚ) : ℝ) + (W : ℝ) * ((farParity T G : ℚ) : ℝ) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) haeq
    simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at h
    exact h
  have hparity : parityBalance (combined cb cf E₁ E₂ E₃ n) = 0 := by
    rw [parityBalance_combined hb0 _ _ _ hn0 hodd heven, hbpar, hfpar]
    calc _ = ((E₁ : ℝ) * Db) * ((nearParity T : ℚ) : ℝ) + ((E₂ : ℝ) * Df) * ((farParity T G : ℚ) : ℝ) -
          ((E₃ : ℝ) * Db) * ((1 / (n : ℝ) + 1 / ((n : ℝ) + 1)) * ((nearParity T : ℚ) : ℝ)) := by ring
      _ = (m : ℝ) * (((nearParity T : ℚ) : ℝ) + (W : ℝ) * ((farParity T G : ℚ) : ℝ) -
          (a : ℝ) * ((1 / (n : ℝ) + 1 / ((n : ℝ) + 1)) * ((nearParity T : ℚ) : ℝ))) := by
          rw [hE₁m, hE₂m, hE₃m]
          ring
      _ = 0 := by
          rw [haeqR]
          ring
  have hal : AlphabetLE (combined cb cf E₁ E₂ E₃ n) (G * T) := by
    have hbal_GT : AlphabetLE cb (G * T) := fun k hk =>
      (hbal_T k hk).trans (Nat.le_mul_of_pos_left T hG0)
    refine alphabet_add (alphabet_add (alphabet_add (alphabet_nsmul hbal_GT _) (alphabet_nsmul hfal _))
      (alphabet_nsmul (alphabet_dilate hbal_T ?_) _))
      (alphabet_neg (alphabet_nsmul (alphabet_dilate hbal_T ?_) _))
    · exact Nat.mul_le_mul_right T (Nat.le_of_dvd hG0 hn)
    · exact Nat.mul_le_mul_right T (Nat.le_of_dvd hG0 hn1)
  have hslope : stencilSlope (combined cb cf E₁ E₂ E₃ n) = (m : ℝ) * (mobiusSlope T +
      (W : ℝ) * ∑ P ∈ primesUpTo T, Real.log ((G * P : ℕ) : ℝ) +
      (a : ℝ) * mobiusSlope T * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by
    rw [stencilSlope_combined hb0 hbbal _ _ _ hn0, hbslope, hfslope]
    calc _ = ((E₁ : ℝ) * Db) * mobiusSlope T +
          ((E₂ : ℝ) * Df) * ∑ P ∈ primesUpTo T, Real.log ((G * P : ℕ) : ℝ) +
          ((E₃ : ℝ) * Db) * (mobiusSlope T * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by ring
      _ = _ := by
          rw [hE₁m, hE₂m, hE₃m]
          ring
  exact ⟨_, m, hP, hparity, hal, neutral_rate_le hT hTG hn0 hη hM hY ha0R ha1R hW0R hWR hZ hm0 hslope⟩

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
