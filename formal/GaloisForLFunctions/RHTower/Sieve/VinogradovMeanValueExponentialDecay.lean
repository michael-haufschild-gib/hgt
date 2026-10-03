import GaloisForLFunctions.RHTower.Sieve.VinogradovCollisionPairRemoval
import GaloisForLFunctions.RHTower.Sieve.VinogradovMeanValueBound

/-!
# Vinogradov's mean value theorem with exponentially decaying defect

Let `J_s(N)` count the solutions of `x_1^j + ⋯ + x_s^j = y_1^j + ⋯ + y_s^j` (`1 ≤ j ≤ k`) with
`x_i, y_i < N`, and put `K = k(k+1)/2`, `θ = 1 - 1/k`.  For `k ≥ 3` and every `s`,

`J_s(N) ≤ C_{k,s} N^{2s - K + K θ^{s/k}}`

(`exists_vinogradov_mean_value_decay`).  The defect `K θ^{s/k}` falls below any fixed bound once
`s ≫ k² log k`.

The proof is a strong induction on `s` along `vinogradov_moment_bertrand_recurrence_pairRemoval`:

* injective leading blocks: a reservoir prime `p` with `N < p^k ≤ C N` and `J_{s-k}(⌈N/p⌉)` give
  the exponent `2s - K + K θ^{(s-k)/k} θ`, which is exactly `2s - K + K θ^{s/k}`;
* colliding blocks: `N² J_{s-2}(N)` fits because `K θ^{(s-2)/k}(1 - θ^{2/k}) ≤ 2`;
* `s ≤ k`: `J_s(N) ≤ s! N^s` fits because `K θ^{s/k} ≥ K - s`.

Since `θ^{s/k} ≤ e^{-s/k²}`, also `J_s(N) ≤ C N^{2s - K + K e^{-s/k²}}`
(`exists_vinogradov_mean_value_exp`).

The two inequalities come from `θ^x ≥ 1 - x/(k-1)` (`one_sub_div_le_rpow_one_sub_inv`).
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- The exponent `2s - k(k+1)/2 + (k(k+1)/2)(1 - 1/k)^{s/k}`. -/
def vinogradovDecayExponent (k s : ℕ) : ℝ :=
  2 * s - (k * (k + 1) / 2 : ℝ) + (k * (k + 1) / 2 : ℝ) * (1 - 1 / (k : ℝ)) ^ ((s : ℝ) / k)

/-- `(1 - 1/k)^x ≥ 1 - x/(k - 1)` for `x ≥ 0`. -/
theorem one_sub_div_le_rpow_one_sub_inv {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    1 - x / ((k : ℝ) - 1) ≤ (1 - 1 / (k : ℝ)) ^ x := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hθ : 0 < 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk2
    linarith
  have hlog : -(1 / ((k : ℝ) - 1)) ≤ Real.log (1 - 1 / (k : ℝ)) := by
    have h := Real.one_sub_inv_le_log_of_pos hθ
    have e : 1 - (1 - 1 / (k : ℝ))⁻¹ = -(1 / ((k : ℝ) - 1)) := by
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    rwa [e] at h
  rw [Real.rpow_def_of_pos hθ]
  have h1 := Real.add_one_le_exp (Real.log (1 - 1 / (k : ℝ)) * x)
  have h2 : -(1 / ((k : ℝ) - 1)) * x ≤ Real.log (1 - 1 / (k : ℝ)) * x :=
    mul_le_mul_of_nonneg_right hlog hx
  have e2 : 1 - x / ((k : ℝ) - 1) = -(1 / ((k : ℝ) - 1)) * x + 1 := by ring
  linarith

theorem rpow_one_sub_inv_pos {k : ℕ} (hk : 2 ≤ k) : 0 < 1 - 1 / (k : ℝ) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk2
  linarith

theorem rpow_one_sub_inv_le_one {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    (1 - 1 / (k : ℝ)) ^ x ≤ 1 :=
  Real.rpow_le_one (rpow_one_sub_inv_pos hk).le
    (by have : 0 ≤ 1 / (k : ℝ) := by positivity
        linarith) hx

/-- The exponent is at least `s`. -/
theorem le_vinogradovDecayExponent {k : ℕ} (hk : 3 ≤ k) (s : ℕ) :
    (s : ℝ) ≤ vinogradovDecayExponent k s := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : (0 : ℝ) ≤ (s : ℝ) / k := by positivity
  have h := one_sub_div_le_rpow_one_sub_inv (k := k) (by omega) hs
  have hK : (0 : ℝ) ≤ k * (k + 1) / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left h hK
  have hkey : (k * (k + 1) / 2 : ℝ) * (1 - (s : ℝ) / k / ((k : ℝ) - 1)) =
      (k * (k + 1) / 2 : ℝ) - (s : ℝ) * ((k + 1) / (2 * ((k : ℝ) - 1))) := by
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  have hfrac : ((k : ℝ) + 1) / (2 * ((k : ℝ) - 1)) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  unfold vinogradovDecayExponent
  nlinarith

/-- The exponent is at most `2s`. -/
theorem vinogradovDecayExponent_le {k : ℕ} (hk : 3 ≤ k) (s : ℕ) :
    vinogradovDecayExponent k s ≤ 2 * s := by
  have h := rpow_one_sub_inv_le_one (k := k) (by omega) (x := (s : ℝ) / k) (by positivity)
  have hK : (0 : ℝ) ≤ k * (k + 1) / 2 := by positivity
  have := mul_le_mul_of_nonneg_left h hK
  unfold vinogradovDecayExponent
  linarith

/-- The good-term exponent identity: `k + λ(b) + (k² - D(b))/k = λ(k + b)`. -/
theorem vinogradovDecayExponent_good {k : ℕ} (hk : 3 ≤ k) (b : ℕ) :
    (k : ℝ) + vinogradovDecayExponent k b +
        (2 * b + (k * (k - 1) / 2 : ℝ) - vinogradovDecayExponent k b) / k =
      vinogradovDecayExponent k (k + b) := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hθ := rpow_one_sub_inv_pos (k := k) (by omega)
  have hsplit : (1 - 1 / (k : ℝ)) ^ (((k + b : ℕ) : ℝ) / k) =
      (1 - 1 / (k : ℝ)) ^ ((b : ℝ) / k) * (1 - 1 / (k : ℝ)) := by
    have e : ((k + b : ℕ) : ℝ) / k = (b : ℝ) / k + 1 := by
      push_cast
      field_simp
      ring
    rw [e, Real.rpow_add hθ, Real.rpow_one]
  unfold vinogradovDecayExponent
  rw [hsplit]
  push_cast
  field_simp
  ring

/-- The collision exponent fits: `2 + λ(s - 2) ≤ λ(s)`. -/
theorem vinogradovDecayExponent_collision {k : ℕ} (hk : 3 ≤ k) {s : ℕ} (hs : 2 ≤ s) :
    2 + vinogradovDecayExponent k (s - 2) ≤ vinogradovDecayExponent k s := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hθ := rpow_one_sub_inv_pos (k := k) (by omega)
  set A := (1 - 1 / (k : ℝ)) ^ (((s - 2 : ℕ) : ℝ) / k) with hA
  set B := (1 - 1 / (k : ℝ)) ^ ((2 : ℝ) / k) with hB
  have hsplit : (1 - 1 / (k : ℝ)) ^ ((s : ℝ) / k) = A * B := by
    rw [hA, hB, ← Real.rpow_add hθ]
    congr 1
    rw [Nat.cast_sub hs]
    push_cast
    ring
  have hA1 : A ≤ 1 := rpow_one_sub_inv_le_one (by omega) (by positivity)
  have hA0 : 0 ≤ A := Real.rpow_nonneg hθ.le _
  have hBlow : 1 - (2 / (k : ℝ)) / ((k : ℝ) - 1) ≤ B :=
    one_sub_div_le_rpow_one_sub_inv (by omega) (by positivity)
  have hK : (k * (k + 1) / 2 : ℝ) * ((2 / (k : ℝ)) / ((k : ℝ) - 1)) ≤ 2 := by
    have e : (k * (k + 1) / 2 : ℝ) * ((2 / (k : ℝ)) / ((k : ℝ) - 1)) =
        ((k : ℝ) + 1) / ((k : ℝ) - 1) := by
      have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
      field_simp
    rw [e, div_le_iff₀ (by linarith)]
    linarith
  have hcast : ((s - 2 : ℕ) : ℝ) = (s : ℝ) - 2 := by rw [Nat.cast_sub hs]; norm_num
  unfold vinogradovDecayExponent
  rw [hsplit, ← hA, hcast]
  have hKpos : (0 : ℝ) ≤ k * (k + 1) / 2 := by positivity
  have h1 : (k * (k + 1) / 2 : ℝ) * A * (1 - B) ≤
      (k * (k + 1) / 2 : ℝ) * ((2 / (k : ℝ)) / ((k : ℝ) - 1)) := by
    have hB' : 1 - B ≤ (2 / (k : ℝ)) / ((k : ℝ) - 1) := by linarith
    have h1B : 0 ≤ 1 - B ∨ 1 - B < 0 := le_or_gt 0 (1 - B)
    rcases h1B with h | h
    · calc (k * (k + 1) / 2 : ℝ) * A * (1 - B) ≤ (k * (k + 1) / 2 : ℝ) * 1 * (1 - B) := by
            gcongr
        _ ≤ (k * (k + 1) / 2 : ℝ) * ((2 / (k : ℝ)) / ((k : ℝ) - 1)) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left hB' hKpos
    · have : (k * (k + 1) / 2 : ℝ) * A * (1 - B) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) h.le
      have h2 : (0 : ℝ) ≤ (k * (k + 1) / 2 : ℝ) * ((2 / (k : ℝ)) / ((k : ℝ) - 1)) := by
        have : (0 : ℝ) < (k : ℝ) - 1 := by linarith
        positivity
      linarith
  nlinarith

/-- **Vinogradov's mean value theorem with exponentially decaying defect.** -/
theorem exists_vinogradov_mean_value_decay {k : ℕ} (hk : 3 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, N ≠ 0 →
      (Fintype.card (VinogradovDiagonalSolution N s k) : ℝ) ≤
        C * (N : ℝ) ^ vinogradovDecayExponent k s := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  by_cases hsk : s ≤ k
  · refine ⟨s.factorial, by positivity, fun N hN => ?_⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
    have hJ : (Fintype.card (VinogradovDiagonalSolution N s k) : ℝ) ≤
        (s.factorial : ℝ) * (N : ℝ) ^ s := by
      exact_mod_cast card_vinogradovDiagonalSolution_le hsk
    refine hJ.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (le_vinogradovDecayExponent hk s)
  replace hsk := lt_of_not_ge hsk
  obtain ⟨b, rfl⟩ : ∃ b, s = k + b := ⟨s - k, by omega⟩
  have hb : b ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  obtain ⟨Cb, hCb, hJb⟩ := ih b (by omega)
  obtain ⟨Cc, hCc, hJc⟩ := ih (k - 2 + b) (by omega)
  set R : ℕ := vinogradovReservoirSize k with hR
  set CP : ℕ := vinogradovReservoirPrimePowerConstant k with hCP
  set Ts : ℕ := vinogradovReservoirSmallThreshold k with hTs
  set e : ℝ := 2 * b + (k * (k - 1) / 2 : ℝ) - vinogradovDecayExponent k b with he
  have he0 : 0 ≤ e := by
    have := vinogradovDecayExponent_le hk b
    have : (0 : ℝ) ≤ k * (k - 1) / 2 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
      positivity
    rw [he]; linarith
  have hCP1 : (1 : ℝ) ≤ CP := by
    rw [hCP, vinogradovReservoirPrimePowerConstant]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  set G : ℝ := (R : ℝ) * (R : ℝ) * (k.factorial : ℝ) * Cb *
      (2 : ℝ) ^ vinogradovDecayExponent k b * (CP : ℝ) ^ (e / k) with hG
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  set Cs : ℝ := (Ts : ℝ) ^ (2 * (k + b)) + 2 * (G + ((k * k - k : ℕ) : ℝ) ^ 2 * Cc) with hCs
  refine ⟨Cs, by rw [hCs]; positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hpow1 : (1 : ℝ) ≤ (N : ℝ) ^ vinogradovDecayExponent k (k + b) :=
    Real.one_le_rpow hN1 (le_trans (Nat.cast_nonneg _) (le_vinogradovDecayExponent hk _))
  by_cases hBN : vinogradovReservoirBound N k ≤ N
  · -- the recursion
    have hrec := vinogradov_moment_bertrand_recurrence_pairRemoval hk0 hb hN
    have hrecR : (Fintype.card (VinogradovDiagonalSolution N (k + b) k) : ℝ) ≤
        2 * ((R : ℝ) * ∑ i : Fin R,
            ((vinogradovReservoirPrime N k i : ℕ) : ℝ) ^ (2 * b) *
              ((N : ℝ) ^ k * ((k.factorial : ℝ) *
                ((vinogradovReservoirPrime N k i : ℕ) : ℝ) ^ (k * (k - 1) / 2) *
                (Fintype.card (VinogradovDiagonalSolution
                  (N ⌈/⌉ (vinogradovReservoirPrime N k i)) b k) : ℝ))) +
          ((k * k - k : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ 2 *
            (Fintype.card (VinogradovDiagonalSolution N (k - 2 + b) k) : ℝ)) := by
      exact_mod_cast hrec
    -- each good term
    have hterm : ∀ i : Fin R,
        ((vinogradovReservoirPrime N k i : ℕ) : ℝ) ^ (2 * b) *
            ((N : ℝ) ^ k * ((k.factorial : ℝ) *
              ((vinogradovReservoirPrime N k i : ℕ) : ℝ) ^ (k * (k - 1) / 2) *
              (Fintype.card (VinogradovDiagonalSolution
                (N ⌈/⌉ (vinogradovReservoirPrime N k i)) b k) : ℝ))) ≤
          (k.factorial : ℝ) * Cb * (2 : ℝ) ^ vinogradovDecayExponent k b *
            (CP : ℝ) ^ (e / k) * (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by
      intro i
      set p : ℕ := vinogradovReservoirPrime N k i with hp
      set M : ℕ := N ⌈/⌉ p with hM
      have hpprime : p.Prime := vinogradovReservoirPrime_prime i
      have hM0 : M ≠ 0 := ceilDiv_ne_zero_of_ne_zero hN hpprime.pos
      have hpM : p * M ≤ 2 * N := vinogradovReservoirPrime_mul_ceilDiv_le_two_mul hN i hBN
      have hpk : p ^ k ≤ CP * N := vinogradovReservoirPrime_pow_le_scale hk0 hN i
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_lt.le
      have hp0 : (0 : ℝ) < p := by linarith
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM0
      set lb := vinogradovDecayExponent k b with hlb
      have hlb0 : 0 ≤ lb := le_trans (Nat.cast_nonneg _) (le_vinogradovDecayExponent hk b)
      have hJ := hJb M hM0
      have hhalf : ((k * (k - 1) / 2 : ℕ) : ℝ) = (k * (k - 1) / 2 : ℝ) := by
        rw [Nat.cast_div (Nat.even_mul_pred_self k).two_dvd (by norm_num)]
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k)]
        norm_num
      -- `p^{2b + k(k-1)/2} M^{lb} ≤ p^e (2N)^{lb}`
      have hpowe : (p : ℝ) ^ (2 * b) * (p : ℝ) ^ (k * (k - 1) / 2) * (M : ℝ) ^ lb ≤
          (p : ℝ) ^ e * (2 * (N : ℝ)) ^ lb := by
        have h1 : (p : ℝ) ^ (2 * b) * (p : ℝ) ^ (k * (k - 1) / 2) =
            (p : ℝ) ^ e * (p : ℝ) ^ lb := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hp0, ← Real.rpow_add hp0,
            hhalf]
          congr 1
          rw [he]
          push_cast
          ring
        have h2 : (p : ℝ) ^ lb * (M : ℝ) ^ lb ≤ (2 * (N : ℝ)) ^ lb := by
          rw [← Real.mul_rpow hp0.le (by linarith)]
          apply Real.rpow_le_rpow (by positivity) _ hlb0
          exact_mod_cast hpM
        calc (p : ℝ) ^ (2 * b) * (p : ℝ) ^ (k * (k - 1) / 2) * (M : ℝ) ^ lb
            = (p : ℝ) ^ e * ((p : ℝ) ^ lb * (M : ℝ) ^ lb) := by rw [h1]; ring
          _ ≤ (p : ℝ) ^ e * (2 * (N : ℝ)) ^ lb :=
              mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hp0.le _)
      -- `p^e ≤ (CP N)^{e/k}`
      have hpe : (p : ℝ) ^ e ≤ ((CP : ℝ) * N) ^ (e / k) := by
        have hk0' : (k : ℝ) ≠ 0 := by positivity
        have e1 : (p : ℝ) ^ e = ((p : ℝ) ^ k) ^ (e / k) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
          congr 1
          field_simp
        rw [e1]
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        exact_mod_cast hpk
      have hexp := vinogradovDecayExponent_good hk b
      rw [← hlb, ← he] at hexp
      have hNpow : (N : ℝ) ^ k * (N : ℝ) ^ lb * (N : ℝ) ^ (e / k) =
          (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by
        rw [← hexp, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_natCast]
      have hsplitCN : ((CP : ℝ) * N) ^ (e / k) = (CP : ℝ) ^ (e / k) * (N : ℝ) ^ (e / k) :=
        Real.mul_rpow (by positivity) hN0.le
      have hsplit2N : (2 * (N : ℝ)) ^ lb = (2 : ℝ) ^ lb * (N : ℝ) ^ lb :=
        Real.mul_rpow (by norm_num) hN0.le
      calc (p : ℝ) ^ (2 * b) * ((N : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) *
            (Fintype.card (VinogradovDiagonalSolution M b k) : ℝ)))
          ≤ (p : ℝ) ^ (2 * b) * ((N : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) *
            (Cb * (M : ℝ) ^ lb))) := by gcongr
        _ = (k.factorial : ℝ) * Cb * (N : ℝ) ^ k *
            ((p : ℝ) ^ (2 * b) * (p : ℝ) ^ (k * (k - 1) / 2) * (M : ℝ) ^ lb) := by ring
        _ ≤ (k.factorial : ℝ) * Cb * (N : ℝ) ^ k * ((p : ℝ) ^ e * (2 * (N : ℝ)) ^ lb) :=
            mul_le_mul_of_nonneg_left hpowe (by positivity)
        _ ≤ (k.factorial : ℝ) * Cb * (N : ℝ) ^ k *
            (((CP : ℝ) * N) ^ (e / k) * (2 * (N : ℝ)) ^ lb) := by
            gcongr
        _ = (k.factorial : ℝ) * Cb * (2 : ℝ) ^ lb * (CP : ℝ) ^ (e / k) *
            ((N : ℝ) ^ k * (N : ℝ) ^ lb * (N : ℝ) ^ (e / k)) := by
            rw [hsplitCN, hsplit2N]; ring
        _ = (k.factorial : ℝ) * Cb * (2 : ℝ) ^ lb * (CP : ℝ) ^ (e / k) *
            (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by rw [hNpow]
    have hsum : (R : ℝ) * ∑ i : Fin R,
            ((vinogradovReservoirPrime N k i : ℕ) : ℝ) ^ (2 * b) *
              ((N : ℝ) ^ k * ((k.factorial : ℝ) *
                ((vinogradovReservoirPrime N k i : ℕ) : ℝ) ^ (k * (k - 1) / 2) *
                (Fintype.card (VinogradovDiagonalSolution
                  (N ⌈/⌉ (vinogradovReservoirPrime N k i)) b k) : ℝ))) ≤
          G * (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by
      have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin R))) => hterm i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
      calc _ ≤ (R : ℝ) * ((R : ℝ) * ((k.factorial : ℝ) * Cb *
            (2 : ℝ) ^ vinogradovDecayExponent k b * (CP : ℝ) ^ (e / k) *
            (N : ℝ) ^ vinogradovDecayExponent k (k + b))) :=
            mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
        _ = G * (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by rw [hG]; ring
    have hcoll : ((k * k - k : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ 2 *
          (Fintype.card (VinogradovDiagonalSolution N (k - 2 + b) k) : ℝ) ≤
        ((k * k - k : ℕ) : ℝ) ^ 2 * Cc * (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by
      have hJ := hJc N hN
      have hidx : k - 2 + b = (k + b) - 2 := by omega
      have hcol := vinogradovDecayExponent_collision hk (s := k + b) (by omega)
      rw [← hidx] at hcol
      have hN2 : (N : ℝ) ^ 2 * (N : ℝ) ^ vinogradovDecayExponent k (k - 2 + b) ≤
          (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
      calc ((k * k - k : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ 2 *
            (Fintype.card (VinogradovDiagonalSolution N (k - 2 + b) k) : ℝ)
          ≤ ((k * k - k : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ 2 *
            (Cc * (N : ℝ) ^ vinogradovDecayExponent k (k - 2 + b)) := by gcongr
        _ = ((k * k - k : ℕ) : ℝ) ^ 2 * Cc *
            ((N : ℝ) ^ 2 * (N : ℝ) ^ vinogradovDecayExponent k (k - 2 + b)) := by ring
        _ ≤ ((k * k - k : ℕ) : ℝ) ^ 2 * Cc * (N : ℝ) ^ vinogradovDecayExponent k (k + b) :=
            mul_le_mul_of_nonneg_left hN2 (by positivity)
    calc (Fintype.card (VinogradovDiagonalSolution N (k + b) k) : ℝ)
        ≤ 2 * (G * (N : ℝ) ^ vinogradovDecayExponent k (k + b) +
            ((k * k - k : ℕ) : ℝ) ^ 2 * Cc * (N : ℝ) ^ vinogradovDecayExponent k (k + b)) := by
          refine hrecR.trans ?_
          gcongr
      _ = 2 * (G + ((k * k - k : ℕ) : ℝ) ^ 2 * Cc) *
          (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by ring
      _ ≤ Cs * (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [hCs]
          have : (0 : ℝ) ≤ (Ts : ℝ) ^ (2 * (k + b)) := by positivity
          linarith
  · -- small `N`
    replace hBN := lt_of_not_ge hBN
    have hsmall : N ≤ Ts := vinogradovReservoirBound_failure_small (by omega) hN hBN
    have htriv : (Fintype.card (VinogradovDiagonalSolution N (k + b) k) : ℝ) ≤
        (N : ℝ) ^ (2 * (k + b)) := by
      exact_mod_cast card_vinogradovDiagonalSolution_le_trivial N (k + b) k
    have hNT : (N : ℝ) ^ (2 * (k + b)) ≤ (Ts : ℝ) ^ (2 * (k + b)) := by
      gcongr
    have hTs : (Ts : ℝ) ^ (2 * (k + b)) ≤ Cs := by
      rw [hCs]
      have : (0 : ℝ) ≤ 2 * (G + ((k * k - k : ℕ) : ℝ) ^ 2 * Cc) := by positivity
      linarith
    calc (Fintype.card (VinogradovDiagonalSolution N (k + b) k) : ℝ)
        ≤ Cs := htriv.trans (hNT.trans hTs)
      _ ≤ Cs * (N : ℝ) ^ vinogradovDecayExponent k (k + b) :=
          le_mul_of_one_le_right (by rw [hCs]; positivity) hpow1


/-- `(1 - 1/k)^{s/k} ≤ e^{-s/k²}`. -/
theorem rpow_one_sub_inv_le_exp {k : ℕ} (hk : 2 ≤ k) (s : ℕ) :
    (1 - 1 / (k : ℝ)) ^ ((s : ℝ) / k) ≤ Real.exp (-((s : ℝ) / (k : ℝ) ^ 2)) := by
  have hθ := rpow_one_sub_inv_pos (k := k) hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [Real.rpow_def_of_pos hθ, Real.exp_le_exp]
  have hlog : Real.log (1 - 1 / (k : ℝ)) ≤ -(1 / (k : ℝ)) := by
    have h := Real.log_le_sub_one_of_pos hθ
    linarith
  have hs : (0 : ℝ) ≤ (s : ℝ) / k := by positivity
  have e : -((s : ℝ) / (k : ℝ) ^ 2) = -(1 / (k : ℝ)) * ((s : ℝ) / k) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_right hlog hs

/-- **Vinogradov's mean value theorem, exponential form.**
`J_s(N) ≤ C N^{2s - K + K e^{-s/k²}}` with `K = k(k+1)/2`. -/
theorem exists_vinogradov_mean_value_exp {k : ℕ} (hk : 3 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, N ≠ 0 →
      (Fintype.card (VinogradovDiagonalSolution N s k) : ℝ) ≤
        C * (N : ℝ) ^ (2 * (s : ℝ) - (k * (k + 1) / 2 : ℝ) +
          (k * (k + 1) / 2 : ℝ) * Real.exp (-((s : ℝ) / (k : ℝ) ^ 2))) := by
  obtain ⟨C, hC, hJ⟩ := exists_vinogradov_mean_value_decay hk s
  refine ⟨C, hC, fun N hN => (hJ N hN).trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  apply Real.rpow_le_rpow_of_exponent_le hN1
  unfold vinogradovDecayExponent
  have h := rpow_one_sub_inv_le_exp (k := k) (by omega) s
  have hK : (0 : ℝ) ≤ k * (k + 1) / 2 := by positivity
  have := mul_le_mul_of_nonneg_left h hK
  linarith

end

end RHTower.Sieve
