import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheParityNeutralProducerReachesTheMertensLevel

/-!
# The parity neutral rate

From a Mertens level `δ` at `T`, with the spike placed at `n ≍ 1/δ`, there is a parity neutral integer producer on the
alphabet `[1, T⁵]` of rate at most `4000 δ (1 + log T)²`. So:

* parity neutral producers reach every rate `exp(−(log K)^α)`, `α < 3/5`;
* a power bound `|M(n)| ≤ C n^{1−σ}` gives parity neutral rates `K^{-a}` for `a < σ/5`;
* parity neutral polynomial rates exist iff `ζ` has a zero-free strip.

At every proved scale a linear parity constraint changes the rate by at most a constant in the exponent. Parity is not read
by the coefficients of a stencil.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The pair `(X, G)`: a multiple `G` of `n₁` with `X ≤ G ≤ 2X`. -/
private lemma exists_multiple_between {X : ℝ} {n₁ : ℕ} (hn : 0 < n₁) (hX : (n₁ : ℝ) ≤ X) :
    ∃ t : ℕ, X ≤ ((n₁ * t : ℕ) : ℝ) ∧ ((n₁ * t : ℕ) : ℝ) ≤ 2 * X := by
  have hnR : (0 : ℝ) < n₁ := by exact_mod_cast hn
  have hX0 : 0 ≤ X / n₁ := div_nonneg (hnR.le.trans hX) hnR.le
  refine ⟨⌈X / n₁⌉₊, ?_, ?_⟩
  · have h := Nat.le_ceil (X / n₁)
    rw [div_le_iff₀ hnR] at h
    push_cast
    linarith
  · have h := Nat.ceil_lt_add_one hX0
    have h2 : (n₁ : ℝ) * (⌈X / n₁⌉₊ : ℝ) ≤ (n₁ : ℝ) * (X / n₁ + 1) :=
      mul_le_mul_of_nonneg_left h.le hnR.le
    have h3 : (n₁ : ℝ) * (X / n₁ + 1) = X + n₁ := by
      field_simp
    push_cast
    linarith

/-- The real arithmetic that places `G`. -/
private lemma neutral_scale {T δ A X n π l : ℝ} (hT : 2 ≤ T) (hδ0 : 0 < δ) (hδT : 1 / T ≤ δ)
    (hA : A = 10 * δ * (5 + 8 * l)) (hl : 0 ≤ l) (hA1 : A ≤ 1 / 10) (hn1 : 1 ≤ n) (hn8 : n ≤ 8 / δ) (hπ1 : 1 ≤ π)
    (hπT : π ≤ T) (hX : X = T * (2 * n + 3) * π / A) (hδ1 : δ ≤ 1) :
    n * (n + 1) ≤ X ∧ 20 * T ≤ X ∧ 2 * X ≤ T ^ 4 := by
  have hA50 : 50 * δ ≤ A := by
    rw [hA]
    nlinarith
  have hA0 : 0 < A := by linarith
  have hT0 : 0 < T := by linarith
  have hXA : X * A = T * (2 * n + 3) * π := by
    rw [hX]
    field_simp
  have hy : 1 / δ ≤ T := by
    rw [div_le_iff₀ hδ0]
    rw [div_le_iff₀ hT0] at hδT
    linarith
  have hy1 : 1 ≤ 1 / δ := by
    rw [le_div_iff₀ hδ0]
    linarith
  have hδy : δ * (1 / δ) = 1 := by field_simp
  obtain ⟨y, hydef⟩ : ∃ y, y = 1 / δ := ⟨_, rfl⟩
  rw [← hydef] at hy hy1 hδy
  have hn8' : n ≤ 8 * y := by
    rw [hydef]
    calc n ≤ 8 / δ := hn8
      _ = 8 * (1 / δ) := by ring
  have hX0 : 0 ≤ X := by
    rw [hX]
    positivity
  have hXlow : 20 * T * n ≤ X := by
    have h1 : T * (2 * n) * 1 ≤ T * (2 * n + 3) * π :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hT0.le) hπ1 zero_le_one (by positivity)
    have h2 : 20 * T * n * A ≤ T * (2 * n) * 1 := by
      have h3 : 0 < T * n := by positivity
      nlinarith
    have h3 : 20 * T * n * A ≤ X * A := by
      rw [hXA]
      linarith
    exact le_of_mul_le_mul_right h3 hA0
  refine ⟨?_, ?_, ?_⟩
  · have hn9 : n + 1 ≤ 9 * T := by nlinarith
    have hn0 : 0 ≤ n := by linarith
    calc n * (n + 1) ≤ n * (9 * T) := mul_le_mul_of_nonneg_left hn9 hn0
      _ ≤ 20 * T * n := by nlinarith
      _ ≤ X := hXlow
  · nlinarith
  · have h19 : 2 * n + 3 ≤ 19 * y := by linarith
    have hnum : T * (2 * n + 3) * π ≤ T * (19 * y) * T :=
      mul_le_mul (mul_le_mul_of_nonneg_left h19 hT0.le) hπT (by linarith) (by positivity)
    have h1 : X * (50 * δ) ≤ X * A := mul_le_mul_of_nonneg_left hA50 hX0
    have h2 : X * 50 * δ ≤ 19 * T ^ 2 * y := by
      calc X * 50 * δ = X * (50 * δ) := by ring
        _ ≤ T * (2 * n + 3) * π := by rw [← hXA]; exact h1
        _ ≤ T * (19 * y) * T := hnum
        _ = _ := by ring
    have h3 : X * 50 = X * 50 * (δ * y) := by rw [hδy, mul_one]
    have h4 : X * 50 ≤ 19 * T ^ 2 * y * y := by
      rw [h3]
      calc X * 50 * (δ * y) = (X * 50 * δ) * y := by ring
        _ ≤ (19 * T ^ 2 * y) * y := mul_le_mul_of_nonneg_right h2 (by linarith)
    have h5 : y * y ≤ T * T := mul_le_mul hy hy (by linarith) hT0.le
    have h6 : 19 * T ^ 2 * y * y ≤ 19 * T ^ 2 * (T * T) := by
      calc 19 * T ^ 2 * y * y = 19 * T ^ 2 * (y * y) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h5 (by positivity)
    have hT4 : 0 < T ^ 4 := by positivity
    nlinarith

/-- The real arithmetic of the rate at a Mertens level. -/
private lemma neutral_level_bound {δ l A Z L n : ℝ} (hδ0 : 0 < δ) (hl0 : 0 ≤ l)
    (hA : A = 10 * δ * (5 + 8 * l)) (hZ0 : 0 ≤ Z) (hZ : Z ≤ A) (hL0 : 0 ≤ L) (hL : L ≤ 5 * l) (hn : 0 < n)
    (h1n : 1 / n ≤ δ) : 8 * Z * (1 + L) + 2 / n ≤ 4000 * δ * (1 + l) ^ 2 := by
  have h2n : 2 / n ≤ 2 * δ := by
    have : 2 / n = 2 * (1 / n) := by ring
    rw [this]
    linarith
  have h1 : Z ≤ 10 * δ * (8 * (1 + l)) := by
    refine hZ.trans ?_
    rw [hA]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : 1 + L ≤ 5 * (1 + l) := by linarith
  have hfirst : 8 * Z * (1 + L) ≤ 8 * (10 * δ * (8 * (1 + l))) * (5 * (1 + l)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (by linarith) (by positivity)
  have hsq : 1 ≤ (1 + l) ^ 2 := one_le_pow₀ (by linarith)
  have hδsq : δ ≤ δ * (1 + l) ^ 2 := le_mul_of_one_le_right hδ0.le hsq
  have e1 : 8 * (10 * δ * (8 * (1 + l))) * (5 * (1 + l)) = 3200 * (δ * (1 + l) ^ 2) := by ring
  have e2 : 4000 * δ * (1 + l) ^ 2 = 4000 * (δ * (1 + l) ^ 2) := by ring
  rw [e2]
  rw [e1] at hfirst
  linarith

/-- **A Mertens level gives a parity neutral producer.** -/
theorem exists_neutral_producer_of_level {T : ℕ} {δ : ℝ} (hT : 2 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδT : 1 / (T : ℝ) ≤ δ) (hM : ∀ y, T ≤ y → |mertens y| ≤ δ * y) (hm : |mobiusHarmonic T| ≤ δ)
    (hsm : 100 * δ * (5 + 8 * Real.log T) ≤ 1) :
    ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧ parityBalance c = 0 ∧ AlphabetLE c (T ^ 5) ∧
      rate c m B ≤ 4000 * δ * (1 + Real.log T) ^ 2 := by
  have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  obtain ⟨l, hldef⟩ : ∃ l, l = Real.log (T : ℝ) := ⟨_, rfl⟩
  rw [← hldef] at hsm ⊢
  have hl0 : 0 ≤ l := hldef ▸ Real.log_nonneg (by linarith)
  have h1δ : 0 < 1 / δ := by positivity
  obtain ⟨N, hNdef⟩ : ∃ N, N = ⌈1 / δ⌉₊ := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := hNdef ▸ Nat.ceil_pos.mpr h1δ
  have hNle : 1 / δ ≤ (N : ℝ) := hNdef ▸ Nat.le_ceil _
  have hNlt : (N : ℝ) < 1 / δ + 1 := hNdef ▸ Nat.ceil_lt_add_one h1δ.le
  obtain ⟨n, hNn, hn4, hodd, heven⟩ := exists_liouville_pattern hN1
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hNnR : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hn4R : (n : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hn4
  have h1le : 1 ≤ 1 / δ := by
    rw [le_div_iff₀ hδ0]
    linarith
  have hn8 : (n : ℝ) ≤ 8 / δ := by
    have : 8 / δ = 8 * (1 / δ) := by ring
    rw [this]
    linarith
  have h1n : 1 / (n : ℝ) ≤ δ := by
    rw [div_le_iff₀ (by linarith)]
    have h2 : 1 / δ ≤ (n : ℝ) := hNle.trans hNnR
    rw [div_le_iff₀ hδ0] at h2
    linarith
  obtain ⟨A, hAdef⟩ : ∃ A, A = 10 * δ * (5 + 8 * l) := ⟨_, rfl⟩
  have hA1 : A ≤ 1 / 10 := by
    rw [hAdef]
    linarith
  have hA0 : 0 < A := by
    rw [hAdef]
    positivity
  have hπ1 : (1 : ℝ) ≤ ((primesUpTo T).card : ℝ) := by
    have h2 : 2 ∈ primesUpTo T := by
      simp only [primesUpTo, mem_filter, mem_Icc]
      exact ⟨⟨by norm_num, hT⟩, Nat.prime_two⟩
    have : 0 < (primesUpTo T).card := card_pos.mpr ⟨2, h2⟩
    exact_mod_cast this
  have hπT : ((primesUpTo T).card : ℝ) ≤ T := by
    have h1 : (primesUpTo T).card ≤ (Icc 1 T).card := card_le_card (filter_subset _ _)
    rw [Nat.card_Icc] at h1
    exact_mod_cast (by omega : (primesUpTo T).card ≤ T)
  obtain ⟨X, hXdef⟩ : ∃ X, X = (T : ℝ) * (2 * (n : ℝ) + 3) * ((primesUpTo T).card : ℝ) / A := ⟨_, rfl⟩
  obtain ⟨hX1, hX2, hX3⟩ := neutral_scale hTR hδ0 hδT hAdef hl0 hA1 hnR hn8 hπ1 hπT hXdef hδ1
  have hn1pos : 0 < n * (n + 1) := Nat.mul_pos hn0 (Nat.succ_pos n)
  have hcast : ((n * (n + 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) + 1) := by push_cast; ring
  obtain ⟨t, htX, htX2⟩ := exists_multiple_between (X := X) hn1pos (by rw [hcast]; exact hX1)
  obtain ⟨G, hGdef⟩ : ∃ G, G = n * (n + 1) * t := ⟨_, rfl⟩
  rw [← hGdef] at htX htX2
  have hGpos : (0 : ℝ) < G := by linarith
  have hTG : T < G := by
    have : (T : ℝ) < G := by linarith
    exact_mod_cast this
  have hn : n ∣ G := by
    rw [hGdef]
    exact ⟨(n + 1) * t, by ring⟩
  have hn1 : n + 1 ∣ G := by
    rw [hGdef]
    exact ⟨n * t, by ring⟩
  have hXA : X * A = (T : ℝ) * (2 * (n : ℝ) + 3) * ((primesUpTo T).card : ℝ) := by
    rw [hXdef]
    field_simp
  have hZeq : neutralCoefficient T G n = X * A / G := by
    rw [neutralCoefficient, hXA]
    ring
  have hZup : neutralCoefficient T G n ≤ A := by
    rw [hZeq, div_le_iff₀ hGpos, mul_comm A]
    exact mul_le_mul_of_nonneg_right htX hA0.le
  have hZlow : A / 2 ≤ neutralCoefficient T G n := by
    rw [hZeq, le_div_iff₀ hGpos]
    calc A / 2 * (G : ℝ) ≤ A / 2 * (2 * X) := mul_le_mul_of_nonneg_left htX2 (by positivity)
      _ = X * A := by ring
  have hGT4 : (G : ℝ) ≤ (T : ℝ) ^ 4 := htX2.trans hX3
  have hlogG : Real.log (G : ℝ) ≤ 4 * l := by
    have h := Real.log_le_log hGpos hGT4
    rwa [Real.log_pow, ← hldef] at h
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = δ * (3 + 8 * l) := ⟨_, rfl⟩
  have hY : |mobiusHarmonic T| + 2 * δ * (1 + Real.log G) ≤ Y := by
    rw [hYdef]
    have h := mul_le_mul_of_nonneg_left (by linarith : 1 + Real.log (G : ℝ) ≤ 1 + 4 * l)
      (by positivity : 0 ≤ 2 * δ)
    have e : δ * (3 + 8 * l) = δ + 2 * δ * (1 + 4 * l) := by ring
    rw [e]
    linarith
  have hYA : 5 * Y ≤ A / 2 := by
    rw [hYdef, hAdef]
    have e : 10 * δ * (5 + 8 * l) / 2 - 5 * (δ * (3 + 8 * l)) = 10 * δ := by ring
    linarith
  have hY1 : Y ≤ 1 := by linarith
  obtain ⟨c, m, hP, hpar, hal, hr⟩ := exists_neutral_producer hT hTG hn0 hn hn1 hodd heven hδ0.le hM hY hY1
    (by linarith) (by linarith)
  have hGT : G * T ≤ T ^ 5 := by
    have : (G : ℝ) * T ≤ (T : ℝ) ^ 5 := by
      calc (G : ℝ) * T ≤ (T : ℝ) ^ 4 * T := mul_le_mul_of_nonneg_right hGT4 hT0.le
        _ = _ := by ring
    exact_mod_cast this
  refine ⟨c, m, G, hP, hpar, fun k hk => (hal k hk).trans hGT, hr.trans ?_⟩
  have hGT1 : (1 : ℝ) ≤ ((G * T : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < G) (by omega : 0 < T)
  have hlogGT : Real.log ((G * T : ℕ) : ℝ) ≤ 5 * l := by
    have h : ((G * T : ℕ) : ℝ) ≤ (T : ℝ) ^ 5 := by exact_mod_cast hGT
    have h2 := Real.log_le_log (by linarith) h
    rwa [Real.log_pow, ← hldef] at h2
  have hlogGT0 := Real.log_nonneg hGT1
  have hZ0 : 0 ≤ neutralCoefficient T G n := by
    have : 0 < A / 2 := by linarith
    linarith
  exact neutral_level_bound hδ0 hl0 hAdef hZ0 hZup hlogGT0 hlogGT (by linarith) h1n

/-- A family of parity neutral producers of rate at most `f`. -/
def HasParityNeutralRate (f : ℕ → ℝ) : Prop :=
  ∀ᶠ K : ℕ in atTop, ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧ AlphabetLE c K ∧
    parityBalance c = 0 ∧ rate c m B ≤ f K

/-- Parity neutral producers are producers. -/
theorem HasParityNeutralRate.hasRate {f : ℕ → ℝ} (h : HasParityNeutralRate f) : HasRate f := by
  filter_upwards [h] with K hK
  obtain ⟨c, m, B, hP, ha, _, hr⟩ := hK
  exact ⟨c, m, B, hP, ha, hr⟩

/-- The cutoff at alphabet size `K`, with `T⁵ ≤ K`. -/
def neutralCutoff (K : ℕ) : ℕ := ⌊(K : ℝ) ^ (1 / 5 : ℝ)⌋₊

theorem tendsto_neutralCutoff : Tendsto neutralCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_natCast_atTop_atTop)

private lemma neutralCutoff_pow_le (K : ℕ) : neutralCutoff K ^ 5 ≤ K := by
  have h0 : (0 : ℝ) ≤ (K : ℝ) ^ (1 / 5 : ℝ) := by positivity
  have h1 : (neutralCutoff K : ℝ) ≤ (K : ℝ) ^ (1 / 5 : ℝ) := Nat.floor_le h0
  have h2 : ((neutralCutoff K : ℕ) : ℝ) ^ 5 ≤ (K : ℝ) := by
    calc ((neutralCutoff K : ℕ) : ℝ) ^ 5 ≤ ((K : ℝ) ^ (1 / 5 : ℝ)) ^ 5 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h1 5
      _ = (K : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg K)]
          norm_num
  exact_mod_cast h2

private lemma half_rpow_le_neutralCutoff {K : ℕ} (h1 : 1 ≤ neutralCutoff K) :
    (K : ℝ) ^ (1 / 5 : ℝ) / 2 ≤ neutralCutoff K := by
  have hlt : (K : ℝ) ^ (1 / 5 : ℝ) < (neutralCutoff K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hT : (1 : ℝ) ≤ neutralCutoff K := by exact_mod_cast h1
  linarith

/-- **A Mertens level gives parity neutral producers at every alphabet.** -/
theorem eventually_neutral_of_level {δ : ℕ → ℝ} (h : IsMertensLevel δ)
    (hsm : ∀ᶠ T : ℕ in atTop, 100 * δ T * (5 + 8 * Real.log T) ≤ 1) :
    ∀ᶠ K : ℕ in atTop, ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧ AlphabetLE c K ∧
      parityBalance c = 0 ∧
      rate c m B ≤ 4000 * δ (neutralCutoff K) * (1 + Real.log (neutralCutoff K)) ^ 2 := by
  filter_upwards [tendsto_neutralCutoff.eventually h, tendsto_neutralCutoff.eventually hsm,
    tendsto_neutralCutoff.eventually_ge_atTop 2] with K hK hS hT2
  obtain ⟨hδ0, hδ1, hδT, hM, hm, _⟩ := hK
  obtain ⟨c, m, B, hP, hpar, hal, hr⟩ := exists_neutral_producer_of_level hT2 hδ0 hδ1 hδT hM hm hS
  exact ⟨c, m, B, hP, fun k hk => (hal k hk).trans (neutralCutoff_pow_le K), hpar, hr⟩

/-- `(1 + log x) x^{-δ} → 0`. -/
private lemma tendsto_one_add_log_mul_rpow' {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => (1 + Real.log x) * x ^ (-δ)) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_neg_atTop hδ
  have h2 := (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_neg hx.le]
  field_simp

/-- **Parity neutral producers at the Vinogradov–Korobov rate.** For `0 < α < 3/5`, parity neutral integer producers have
rate `exp(−(log K)^α)`. -/
theorem hasParityNeutralRate_vk {α : ℝ} (hα0 : 0 < α) (hα : α < 3 / 5) :
    HasParityNeutralRate fun K => Real.exp (-(Real.log (K : ℝ) ^ α)) := by
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (α + 3 / 5) / 2 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβdef]; linarith
  have hβ : β < 3 / 5 := by rw [hβdef]; linarith
  have hαβ : α < β := by rw [hβdef]; linarith
  have hlogT : Tendsto (fun T : ℕ => Real.log (T : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsm : ∀ᶠ T : ℕ in atTop,
      100 * Real.exp (-(Real.log (T : ℝ) ^ β)) * (5 + 8 * Real.log T) ≤ 1 := by
    have h1 := hlogT.eventually (HTGeometry.eventually_mul_rpow_le_exp_rpow (1300 : ℝ)
      (c := 1) (δ := β) (p := 1) one_pos hβ0)
    filter_upwards [h1, hlogT.eventually_ge_atTop 1] with T hT hT1
    rw [Real.rpow_one, one_mul] at hT
    have hexp := Real.exp_pos (Real.log (T : ℝ) ^ β)
    have hneg : Real.exp (-(Real.log (T : ℝ) ^ β)) * Real.exp (Real.log (T : ℝ) ^ β) = 1 := by
      rw [← Real.exp_add]
      simp
    have hepos := Real.exp_pos (-(Real.log (T : ℝ) ^ β))
    have h5 : 100 * (5 + 8 * Real.log (T : ℝ)) ≤ Real.exp (Real.log (T : ℝ) ^ β) := by nlinarith
    calc _ = Real.exp (-(Real.log (T : ℝ) ^ β)) * (100 * (5 + 8 * Real.log (T : ℝ))) := by ring
      _ ≤ Real.exp (-(Real.log (T : ℝ) ^ β)) * Real.exp (Real.log (T : ℝ) ^ β) :=
          mul_le_mul_of_nonneg_left h5 hepos.le
      _ = 1 := hneg
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = (1 / 6 : ℝ) ^ β := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  have hlogK : Tendsto (fun K : ℕ => Real.log (K : ℝ)) atTop atTop := hlogT
  have hp1 := hlogK.eventually (HTGeometry.eventually_mul_rpow_le_exp_rpow (16000 : ℝ)
    (c := c₀ / 2) (δ := β) (p := 2) (by positivity) hβ0)
  have hp2 : ∀ᶠ K : ℕ in atTop, 2 / c₀ ≤ Real.log (K : ℝ) ^ (β - α) :=
    hlogK.eventually ((tendsto_rpow_atTop (by linarith : 0 < β - α)).eventually_ge_atTop (2 / c₀))
  filter_upwards [eventually_neutral_of_level (isMertensLevel_vk hβ0 hβ) hsm,
    tendsto_neutralCutoff.eventually_ge_atTop 1, hp1, hp2, hlogK.eventually_ge_atTop 30,
    eventually_ge_atTop 1] with K hK hT1 h1 h2 h3 hK1
  obtain ⟨c, m, B, hP, ha, hpar, hr⟩ := hK
  refine ⟨c, m, B, hP, ha, hpar, hr.trans ?_⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = neutralCutoff K := ⟨_, rfl⟩
  rw [← hTdef] at hT1 ⊢
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log (K : ℝ) := ⟨_, rfl⟩
  rw [← hudef] at h1 h2 h3 ⊢
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hT0 : (0 : ℝ) < T := by linarith
  have hu0 : 0 < u := by linarith
  have hlow : u / 6 ≤ Real.log (T : ℝ) := by
    have h4 := half_rpow_le_neutralCutoff (hTdef ▸ hT1 : 1 ≤ neutralCutoff K)
    rw [← hTdef] at h4
    have h5 : Real.log ((K : ℝ) ^ (1 / 5 : ℝ) / 2) ≤ Real.log (T : ℝ) :=
      Real.log_le_log (by positivity) h4
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hK0, ← hudef] at h5
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  have hup : Real.log (T : ℝ) ≤ u := by
    have h4 : (T : ℝ) ≤ K := by
      have h5 : T ^ 5 ≤ K := hTdef ▸ neutralCutoff_pow_le K
      have h6 : T ≤ T ^ 5 := Nat.le_self_pow (by norm_num) T
      exact_mod_cast h6.trans h5
    rw [hudef]
    exact Real.log_le_log hT0 h4
  have hlogT0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg hTR
  have hδ : Real.exp (-(Real.log (T : ℝ) ^ β)) ≤ Real.exp (-(c₀ * u ^ β)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have h4 : (u / 6) ^ β ≤ Real.log (T : ℝ) ^ β := Real.rpow_le_rpow (by positivity) hlow hβ0.le
    have h5 : (u / 6) ^ β = c₀ * u ^ β := by
      rw [hc₀, div_eq_mul_inv, mul_comm u, Real.mul_rpow (by norm_num) hu0.le]
      norm_num
    linarith
  have hsq : (1 + Real.log (T : ℝ)) ^ 2 ≤ 4 * u ^ 2 := by nlinarith
  have hup2 : u ^ (2 : ℝ) = u ^ 2 := by
    rw [← Real.rpow_natCast]
    norm_num
  rw [hup2] at h1
  have hexpc := Real.exp_pos (-(c₀ * u ^ β))
  have hsplit : Real.exp (c₀ / 2 * u ^ β) * Real.exp (-(c₀ * u ^ β)) = Real.exp (-(c₀ / 2 * u ^ β)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfin : Real.exp (-(c₀ / 2 * u ^ β)) ≤ Real.exp (-(u ^ α)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have huβ : u ^ β = u ^ α * u ^ (β - α) := by
      rw [← Real.rpow_add hu0]
      congr 1
      ring
    have hα0' : 0 < u ^ α := Real.rpow_pos_of_pos hu0 _
    have h3' : 1 ≤ c₀ / 2 * u ^ (β - α) := by
      have := (div_le_iff₀ hc₀0).mp h2
      linarith
    rw [huβ]
    nlinarith
  calc 4000 * Real.exp (-(Real.log (T : ℝ) ^ β)) * (1 + Real.log (T : ℝ)) ^ 2
      ≤ 4000 * Real.exp (-(c₀ * u ^ β)) * (4 * u ^ 2) :=
        mul_le_mul (by linarith) hsq (by positivity) (by positivity)
    _ = (16000 * u ^ 2) * Real.exp (-(c₀ * u ^ β)) := by ring
    _ ≤ Real.exp (c₀ / 2 * u ^ β) * Real.exp (-(c₀ * u ^ β)) :=
        mul_le_mul_of_nonneg_right h1 hexpc.le
    _ = Real.exp (-(c₀ / 2 * u ^ β)) := hsplit
    _ ≤ _ := hfin

/-- **A power bound on the Mertens function gives a polynomial parity neutral rate.** -/
theorem hasParityNeutralRate_of_power {C σ a : ℝ} (hC : 0 ≤ C) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hM : ∀ n : ℕ, 1 ≤ n → |RHTower.Sieve.mertensM n| ≤ C * (n : ℝ) ^ (1 - σ)) (ha : a < σ / 5) :
    HasParityNeutralRate fun K => (K : ℝ) ^ (-a) := by
  have hlevel := isMertensLevel_of_power hC hσ0 hσ1 hM
  obtain ⟨A, hAdef⟩ : ∃ A, A = (C + 1) * (1 + 1 / σ) := ⟨_, rfl⟩
  rw [← hAdef] at hlevel
  have hA0 : 0 < A := by rw [hAdef]; positivity
  have hsm : ∀ᶠ T : ℕ in atTop, 100 * (A * (T : ℝ) ^ (-σ)) * (5 + 8 * Real.log T) ≤ 1 := by
    have hlim := ((tendsto_one_add_log_mul_rpow' hσ0).comp tendsto_natCast_atTop_atTop).const_mul
      (800 * A)
    rw [mul_zero] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds zero_lt_one), eventually_ge_atTop 1] with T hT hT1
    simp only [Function.comp] at hT
    have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    have hl0 := Real.log_nonneg hTR
    have hTσ : 0 < (T : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
    have h8 : 5 + 8 * Real.log (T : ℝ) ≤ 8 * (1 + Real.log (T : ℝ)) := by linarith
    calc 100 * (A * (T : ℝ) ^ (-σ)) * (5 + 8 * Real.log T)
        ≤ 100 * (A * (T : ℝ) ^ (-σ)) * (8 * (1 + Real.log (T : ℝ))) :=
          mul_le_mul_of_nonneg_left h8 (by positivity)
      _ = 800 * A * ((1 + Real.log (T : ℝ)) * (T : ℝ) ^ (-σ)) := by ring
      _ ≤ 1 := hT.le
  obtain ⟨η, hηdef⟩ : ∃ η, η = σ / 5 - a := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; linarith
  have hpoly : Tendsto (fun K : ℕ => 8000 * A * ((1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-(η / 2))) ^ 2)
      atTop (𝓝 0) := by
    have h := (((tendsto_one_add_log_mul_rpow' (half_pos hη)).pow 2).const_mul (8000 * A)).comp
      tendsto_natCast_atTop_atTop
    have hz : 8000 * A * (0 : ℝ) ^ 2 = 0 := by simp
    rw [hz] at h
    exact h
  filter_upwards [eventually_neutral_of_level hlevel hsm, tendsto_neutralCutoff.eventually_ge_atTop 1,
    hpoly.eventually (gt_mem_nhds zero_lt_one), eventually_ge_atTop 1] with K hK hT1 hpol hK1
  obtain ⟨c, m, B, hP, hal, hpar, hr⟩ := hK
  refine ⟨c, m, B, hP, hal, hpar, hr.trans ?_⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = neutralCutoff K := ⟨_, rfl⟩
  rw [← hTdef] at hT1 ⊢
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hT0 : (0 : ℝ) < T := by linarith
  have hlow := half_rpow_le_neutralCutoff (hTdef ▸ hT1 : 1 ≤ neutralCutoff K)
  rw [← hTdef] at hlow
  have hTσ : (T : ℝ) ^ (-σ) ≤ 2 * (K : ℝ) ^ (-(σ / 5)) := by
    calc (T : ℝ) ^ (-σ) ≤ ((K : ℝ) ^ (1 / 5 : ℝ) / 2) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
      _ = (2 : ℝ) ^ σ * (K : ℝ) ^ (-(σ / 5)) := by
          rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hK0.le,
            Real.rpow_neg (by norm_num)]
          have hexp : (1 / 5 : ℝ) * -σ = -(σ / 5) := by ring
          rw [hexp]
          field_simp
      _ ≤ 2 * (K : ℝ) ^ (-(σ / 5)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
            _ = 2 := Real.rpow_one 2
  have hlT : Real.log (T : ℝ) ≤ Real.log (K : ℝ) := by
    have h4 : (T : ℝ) ≤ K := by
      have h5 : T ^ 5 ≤ K := hTdef ▸ neutralCutoff_pow_le K
      have h6 : T ≤ T ^ 5 := Nat.le_self_pow (by norm_num) T
      exact_mod_cast h6.trans h5
    exact Real.log_le_log hT0 h4
  have hl0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg hTR
  have hsplit : (K : ℝ) ^ (-(σ / 5)) = (K : ℝ) ^ (-η) * (K : ℝ) ^ (-a) := by
    rw [← Real.rpow_add hK0, hηdef]
    congr 1
    ring
  have hsq : ((1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-(η / 2))) ^ 2 =
      (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (-η) := by
    have h3 : ((K : ℝ) ^ (-(η / 2))) ^ 2 = (K : ℝ) ^ (-η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
      congr 1
      push_cast
      ring
    rw [mul_pow, h3]
  have hKa : 0 < (K : ℝ) ^ (-a) := Real.rpow_pos_of_pos hK0 _
  have hl1 : (1 + Real.log (T : ℝ)) ^ 2 ≤ (1 + Real.log (K : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  calc 4000 * (A * (T : ℝ) ^ (-σ)) * (1 + Real.log (T : ℝ)) ^ 2
      ≤ 4000 * (A * (2 * ((K : ℝ) ^ (-η) * (K : ℝ) ^ (-a)))) * (1 + Real.log (K : ℝ)) ^ 2 := by
        rw [← hsplit]
        exact mul_le_mul (by gcongr) hl1 (by positivity) (by positivity)
    _ = (8000 * A * ((1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (-η))) * (K : ℝ) ^ (-a) := by ring
    _ = (8000 * A * ((1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-(η / 2))) ^ 2) * (K : ℝ) ^ (-a) := by rw [hsq]
    _ ≤ 1 * (K : ℝ) ^ (-a) := mul_le_mul_of_nonneg_right hpol.le hKa.le
    _ = _ := one_mul _

/-- **Parity neutrality changes nothing at the polynomial scale.** Polynomial parity neutral rates exist iff `ζ` has a
zero-free strip. -/
theorem exists_hasParityNeutralRate_rpow_iff :
    (∃ a : ℝ, 0 < a ∧ HasParityNeutralRate fun K => (K : ℝ) ^ (-a)) ↔
      ∃ Θ : ℝ, Θ < 1 ∧ ∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0 := by
  constructor
  · rintro ⟨a, ha, h⟩
    exact exists_hasRate_rpow_iff.mp ⟨a, ha, h.hasRate⟩
  · rintro ⟨Θ, hΘ, hzf⟩
    obtain ⟨Θ', hΘ'⟩ : ∃ Θ', Θ' = max Θ (1 / 2) := ⟨_, rfl⟩
    have hΘ'1 : Θ' < 1 := by
      rw [hΘ']
      exact max_lt hΘ (by norm_num)
    have hΘ'h : 1 / 2 ≤ Θ' := hΘ' ▸ le_max_right _ _
    have hzf' : ∀ s : ℂ, Θ' < s.re → riemannZeta s ≠ 0 := fun s hs =>
      hzf s (lt_of_le_of_lt (hΘ' ▸ le_max_left _ _) hs)
    have hσ0 : 0 < (1 - Θ') / 2 := by linarith
    obtain ⟨C, hC, hM⟩ := exists_mertens_power_of_zeroFree hΘ'h hΘ'1 hzf' hσ0 (by linarith)
    exact ⟨(1 - Θ') / 2 / 6, by positivity, hasParityNeutralRate_of_power hC hσ0 (by linarith) hM (by linarith)⟩

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
