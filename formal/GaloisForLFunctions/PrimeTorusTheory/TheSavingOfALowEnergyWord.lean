import GaloisForLFunctions.PrimeTorusTheory.TheEnergyOfASquaredWord
import GaloisForLFunctions.PrimeTorusTheory.TheSupBoundOfIntegerPowers

/-!
# The saving of a low energy word

At a placement in the band the phase of a squared word is at distance at least `1/(2R)` from the
integers. Grouping its letters by `a + b` and applying Cauchy–Schwarz gives
`1/(2R)² ≤ E · Σ_n ‖θ(x + hn)‖²` with `E = Σ_n r(n)²`, in place of the bound by the mass. For a fixed
step `h`, the placements `x ∈ [hu, hu + h)` meet each integer at most once, so no further loss occurs.

With a word of energy `≲ M²` this gives mean square distance `≳ 1/M³` instead of `1/M⁴`.

* `WordSetup.le_sum_sq_ap`: the mean square distance on every progression `r + qm`.
* `norm_sum_le_of_large_energy`, `norm_sum_ap_le_of_large_energy`:
  `‖Σ_{n<N} n^{it}‖ ≤ N(1 - 1/(10⁷ L⁶ ℓ³))` for `N ≥ 48 L² ℓ`, with `L = log|t|`, `ℓ = log L`.
* `le_sum_primes_sq_phaseDist`: `Σ_{p<N} ‖t log p/2π‖²/p ≥ 1/(10⁹ L⁶ ℓ⁴)`, by Cauchy–Schwarz on the
  prime factors of `n`.
* `le_sum_primes_critical_energy`: `Σ_{p<N} (1 - cos(t log p))/√p ≥ 8/(10⁹ L⁶ ℓ⁴)`.
-/

open Finset Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- **Energy replaces mass.** At a placement in the band, the square of the distance of the word's
phase is bounded by the energy of the word times the sum of the squares of the distances of its
letters. -/
theorem sq_le_energy_mul_sum {M : ℕ} {c : ℕ → ℤ} {R : ℝ} (hR : 1 ≤ R) (hm : binomMoment M c 0 = 0)
    {t x h : ℝ} (hx : 0 < x) (hh : 0 < h) (htpos : 0 < |t|)
    (h1 : π / |t| / R ≤ -wordForm M c (x / h)) (h2 : -wordForm M c (x / h) ≤ π / |t|) (φ : ℝ) :
    (1 / (2 * R)) ^ 2 ≤ wordEnergy M c *
      ∑ n ∈ range (2 * M + 1), dist01 (t * Real.log (x + h * (n : ℝ)) / (2 * π) - φ) ^ 2 := by
  have hR0 : 0 < R := by linarith
  set Θ : ℕ → ℝ := fun n => t * Real.log (x + h * (n : ℝ)) / (2 * π) - φ with hΘ
  set err : ℕ → ℝ := fun n => Θ n - round (Θ n) with herr
  have h0 := one_div_le_abs_sum_err hR hm hx hh htpos h1 h2 φ
  have e : ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a : ℝ) * (c b : ℝ) *
      (t * Real.log (x + h * ((a : ℝ) + b)) / (2 * π) - φ -
        round (t * Real.log (x + h * ((a : ℝ) + b)) / (2 * π) - φ)) =
      ∑ n ∈ range (2 * M + 1), conv M c n * err n := by
    have := sum_sum_eq_sum_conv (A := ℝ) M c err
    simp only [smul_eq_mul] at this
    rw [← this]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    simp only [herr, hΘ, Nat.cast_add]
  rw [e] at h0
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range (2 * M + 1)) (conv M c) err
  have hd : ∑ n ∈ range (2 * M + 1), err n ^ 2 = ∑ n ∈ range (2 * M + 1), dist01 (Θ n) ^ 2 :=
    sum_congr rfl fun n _ => by simp only [herr, dist01, sq_abs]
  rw [hd] at hcs
  calc (1 / (2 * R)) ^ 2 ≤ |∑ n ∈ range (2 * M + 1), conv M c n * err n| ^ 2 :=
        pow_le_pow_left₀ (by positivity) h0 2
    _ = (∑ n ∈ range (2 * M + 1), conv M c n * err n) ^ 2 := sq_abs _
    _ ≤ _ := hcs

/-- For fixed `h`, the integers `A + i + hm`, `i < h`, are distinct. -/
theorem sum_blocks_le {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) {h n A N : ℕ} (hN : A + h * n ≤ N) :
    ∑ i ∈ range h, ∑ m ∈ range n, g (A + i + h * m) ≤ ∑ m ∈ range N, g m := by
  rw [Finset.sum_comm]
  have e : ∑ m ∈ range n, ∑ i ∈ range h, g (A + i + h * m) =
      ∑ ρ ∈ range (h * n), g (A + ρ) := by
    rw [sum_range_mul_eq (fun ρ => g (A + ρ)) h n]
    refine sum_congr rfl fun m _ => sum_congr rfl fun i _ => ?_
    congr 1
    ring
  rw [e]
  exact sum_shift_le hg hN

namespace WordSetup

variable {H R : ℝ} {M k N₁ : ℕ} {c : ℕ → ℤ} {t : ℝ}

/-- The square distance over a multiple of `6M + 6` terms of the progression `r + qm`. -/
theorem le_energy_mul_sum_sq_ap_mul (S : WordSetup H R M k N₁ c t) (φ : ℝ) {q r B : ℕ} (hq : 1 ≤ q)
    (hr : r ≤ q) (hB : 1 ≤ B) :
    (B : ℝ) * (1 / (2 * R)) ^ 2 ≤
      wordEnergy M c * ∑ m ∈ range (B * (6 * M + 6)), rotDist t φ (r + q * m) ^ 2 := by
  have hm0 := S.moments 0 (Nat.zero_le k)
  obtain ⟨u₁, hu1, hu2, hband⟩ := S.exists_band
  have htpos := S.abs_pos
  have hN0 : (1 : ℝ) ≤ N₁ := by exact_mod_cast S.one_le_N
  have hu0 : 2 ≤ u₁ := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hrq : (r : ℝ) / q ≤ 1 := by
    rw [div_le_one hq0]
    exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ (r : ℝ) / q := by positivity
  set g : ℕ → ℝ := fun m => rotDist t φ (r + q * m) ^ 2 with hg
  have hgnn : ∀ m, 0 ≤ g m := fun m => sq_nonneg _
  have hE := wordEnergy_nonneg M c
  have hh0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hh1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hhu : 2 ≤ (B : ℝ) * u₁ := by nlinarith
  set A := ⌈(B : ℝ) * u₁ - (r : ℝ) / q⌉₊ with hA
  have hAlow : (B : ℝ) * u₁ - (r : ℝ) / q ≤ A := Nat.le_ceil _
  have hAup : (A : ℝ) < (B : ℝ) * u₁ - (r : ℝ) / q + 1 := Nat.ceil_lt_add_one (by linarith)
  have hApos : 1 ≤ A := by
    have : (1 : ℝ) ≤ A := by linarith
    exact_mod_cast this
  have hAnat : A ≤ B * (4 * (M + 1)) := by
    have h1 : (B : ℝ) * u₁ ≤ (B : ℝ) * (4 * ((M : ℝ) + 1)) := mul_le_mul_of_nonneg_left hu2 hh0.le
    have h2 : (A : ℝ) < ((B * (4 * (M + 1)) : ℕ) : ℝ) + 1 := by
      push_cast
      linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast h2)
  have hupper := sum_blocks_le hgnn (h := B) (n := 2 * M + 1) (A := A) (N := B * (6 * M + 6)) (by
    have h7 : B * (4 * (M + 1)) + B * (2 * M + 1) ≤ B * (6 * M + 6) := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left _ (by omega)
    omega)
  have hlower : ∀ i ∈ range B, (1 / (2 * R)) ^ 2 ≤ wordEnergy M c *
      ∑ n ∈ range (2 * M + 1), g (A + i + B * n) := by
    intro i hi
    have hih : (i : ℝ) + 1 ≤ (B : ℝ) := by exact_mod_cast mem_range.mp hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hApos
    have hx : (0 : ℝ) < ((r + q * (A + i) : ℕ) : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have h3 : 0 < (q : ℝ) * ((A : ℝ) + i) := by positivity
      linarith
    have hh'0 : (0 : ℝ) < ((q * B : ℕ) : ℝ) := by
      push_cast
      positivity
    have ee : ((r + q * (A + i) : ℕ) : ℝ) / ((q * B : ℕ) : ℝ) = ((r : ℝ) / q + A + i) / B := by
      push_cast
      field_simp
      ring
    have hmem : ((r + q * (A + i) : ℕ) : ℝ) / ((q * B : ℕ) : ℝ) ∈ Set.Icc u₁ (u₁ + 1) := by
      rw [ee]
      constructor
      · rw [le_div_iff₀ hh0]
        linarith
      · rw [div_le_iff₀ hh0]
        nlinarith
    have hb := hband _ hmem
    have h5 := sq_le_energy_mul_sum S.one_le_R hm0 hx hh'0 htpos hb.1 hb.2 φ
    refine h5.trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl fun n _ => ?_
    have hne : r + q * (A + i + B * n) ≠ 0 := by
      have : 0 < q * (A + i + B * n) := Nat.mul_pos (by omega) (by omega)
      omega
    have e : ((r + q * (A + i) : ℕ) : ℝ) + ((q * B : ℕ) : ℝ) * (n : ℝ) =
        ((r + q * (A + i + B * n) : ℕ) : ℝ) := by
      push_cast
      ring
    simp only [hg]
    unfold rotDist
    rw [if_neg hne, e]
  calc (B : ℝ) * (1 / (2 * R)) ^ 2 = ∑ _i ∈ range B, (1 / (2 * R)) ^ 2 := by
        rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ ∑ i ∈ range B, wordEnergy M c * ∑ n ∈ range (2 * M + 1), g (A + i + B * n) :=
        sum_le_sum hlower
    _ = wordEnergy M c * ∑ i ∈ range B, ∑ n ∈ range (2 * M + 1), g (A + i + B * n) := by
        rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hupper hE

/-- **The mean square distance on progressions.** For every `K ≥ 6(M + 1)`, uniformly in `q ≥ r`. -/
theorem le_energy_mul_sum_sq_ap (S : WordSetup H R M k N₁ c t) (φ : ℝ) {q r K : ℕ} (hq : 1 ≤ q)
    (hr : r ≤ q) (hK : 6 * M + 6 ≤ K) :
    (K : ℝ) / (48 * R ^ 2 * ((M : ℝ) + 1)) ≤
      wordEnergy M c * ∑ m ∈ range K, rotDist t φ (r + q * m) ^ 2 := by
  set Q := 6 * M + 6 with hQ
  have hQ0 : 0 < Q := by omega
  set B := K / Q with hB
  have hB1 : 1 ≤ B := (Nat.one_le_div_iff hQ0).mpr hK
  have hBle : B * Q ≤ K := Nat.div_mul_le_self K Q
  have hNlt : K < (B + 1) * Q := by
    have := Nat.lt_succ_iff.mpr (le_refl (K / Q))
    exact Nat.lt_mul_of_div_lt this hQ0
  have hmain := S.le_energy_mul_sum_sq_ap_mul φ hq hr hB1
  have hsub : ∑ m ∈ range (B * Q), rotDist t φ (r + q * m) ^ 2 ≤
      ∑ m ∈ range K, rotDist t φ (r + q * m) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hBle) fun n _ _ => sq_nonneg _
  have hE := wordEnergy_nonneg M c
  refine le_trans ?_ (hmain.trans (mul_le_mul_of_nonneg_left hsub hE))
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hR0 : 0 < R := by linarith [S.one_le_R]
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hNr : (K : ℝ) ≤ ((B : ℝ) + 1) * (6 * ((M : ℝ) + 1)) := by
    have : (K : ℝ) ≤ (((B + 1) * Q : ℕ) : ℝ) := by exact_mod_cast hNlt.le
    rw [hQ] at this
    push_cast at this
    linarith
  have hNr2 : (K : ℝ) ≤ 2 * (B : ℝ) * (6 * ((M : ℝ) + 1)) := by nlinarith
  have e : (B : ℝ) * (1 / (2 * R)) ^ 2 = (B : ℝ) * (12 * ((M : ℝ) + 1)) /
      (48 * R ^ 2 * ((M : ℝ) + 1)) := by
    field_simp
    ring
  rw [e]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  linarith

/-- The mean square distance for a word of energy at most `12 (M+1)²`. -/
theorem le_sum_sq_ap (S : WordSetup H R M k N₁ c t) (hE : wordEnergy M c ≤ 12 * ((M : ℝ) + 1) ^ 2)
    (φ : ℝ) {q r K : ℕ} (hq : 1 ≤ q) (hr : r ≤ q) (hK : 6 * M + 6 ≤ K) :
    (K : ℝ) * (1 / (576 * R ^ 2 * ((M : ℝ) + 1) ^ 3)) ≤ ∑ m ∈ range K, rotDist t φ (r + q * m) ^ 2 := by
  have h := S.le_energy_mul_sum_sq_ap φ hq hr hK
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hR0 : 0 < R := by linarith [S.one_le_R]
  set X := ∑ m ∈ range K, rotDist t φ (r + q * m) ^ 2 with hX
  have hX0 : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have h2 : (K : ℝ) / (48 * R ^ 2 * ((M : ℝ) + 1)) ≤ 12 * ((M : ℝ) + 1) ^ 2 * X :=
    h.trans (mul_le_mul_of_nonneg_right hE hX0)
  have e : (K : ℝ) * (1 / (576 * R ^ 2 * ((M : ℝ) + 1) ^ 3)) =
      (K : ℝ) / (48 * R ^ 2 * ((M : ℝ) + 1)) / (12 * ((M : ℝ) + 1) ^ 2) := by
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  linarith

/-- **The sup bound on progressions** for a word of low energy. -/
theorem norm_sum_ap_le_of_energy (S : WordSetup H R M k N₁ c t)
    (hE : wordEnergy M c ≤ 12 * ((M : ℝ) + 1) ^ 2) {q r K : ℕ} (hq : 1 ≤ q) (hr1 : 1 ≤ r) (hr : r ≤ q)
    (hK : 6 * M + 6 ≤ K) :
    ‖∑ m ∈ range K, Complex.exp (Complex.I * (t * Real.log ((r + q * m : ℕ) : ℝ)))‖ ≤
      (K : ℝ) * (1 - 1 / (72 * R ^ 2 * ((M : ℝ) + 1) ^ 3)) := by
  obtain ⟨φ, hφ⟩ := exists_phase_norm_sum_le (range K) (fun m => r + q * m) (fun m _ => by omega) t
  have h := S.le_sum_sq_ap hE φ hq hr hK
  rw [card_range] at hφ
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hR0 : 0 < R := by linarith [S.one_le_R]
  have e : (K : ℝ) * (1 - 1 / (72 * R ^ 2 * ((M : ℝ) + 1) ^ 3)) =
      (K : ℝ) - 8 * ((K : ℝ) * (1 / (576 * R ^ 2 * ((M : ℝ) + 1) ^ 3))) := by
    field_simp
    ring
  rw [e]
  linarith

/-- **The sup bound on the integers** for a word of low energy. -/
theorem norm_sum_le_of_energy (S : WordSetup H R M k N₁ c t)
    (hE : wordEnergy M c ≤ 12 * ((M : ℝ) + 1) ^ 2) {N : ℕ} (hN : 6 * M + 6 ≤ N) :
    ‖∑ n ∈ Finset.Ico 1 N, Complex.exp (Complex.I * (t * Real.log n))‖ ≤
      (N : ℝ) * (1 - 1 / (72 * R ^ 2 * ((M : ℝ) + 1) ^ 3)) := by
  have hN0 : 0 < N := by omega
  obtain ⟨φ, hφ⟩ := exists_phase_norm_sum_le (Finset.Ico 1 N) (fun n => n)
    (fun n hn => by have := (Finset.mem_Ico.mp hn).1; omega) t
  have h := S.le_sum_sq_ap hE φ (q := 1) (r := 0) le_rfl (Nat.zero_le 1) hN
  have hsum : ∑ m ∈ range N, rotDist t φ (0 + 1 * m) ^ 2 =
      ∑ n ∈ Finset.Ico 1 N, rotDist t φ n ^ 2 := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN0]
    simp [rotDist]
  rw [hsum] at h
  have hcard : ((Finset.Ico 1 N).card : ℝ) ≤ N := by
    rw [Nat.card_Ico]
    exact_mod_cast Nat.sub_le _ _
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hR0 : 0 < R := by linarith [S.one_le_R]
  have e : (N : ℝ) * (1 - 1 / (72 * R ^ 2 * ((M : ℝ) + 1) ^ 3)) =
      (N : ℝ) - 8 * ((N : ℝ) * (1 / (576 * R ^ 2 * ((M : ℝ) + 1) ^ 3))) := by
    field_simp
    ring
  rw [e]
  linarith

end WordSetup

/-! ### At large height -/

/-- The moment map has room for a low energy word: compared with `prod_choose_lt_of_log`, half of
all sign patterns suffice. -/
theorem prod_choose_lt_two_pow_of_log {M k : ℕ} (hM : 1 ≤ M)
    (h : ((k : ℝ) + 2) ^ 2 * Real.log ((M : ℝ) + 2) ≤ (M : ℝ)) :
    ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) < 2 ^ M := by
  have hterm : ∀ j ∈ range (k + 1), (M + 1).choose (j + 1) + 1 ≤ (M + 2) ^ (j + 1) := by
    intro j _
    have h1 : (M + 1).choose (j + 1) ≤ (M + 1) ^ (j + 1) := Nat.choose_le_pow _ _
    have hlt : (M + 1) ^ (j + 1) < (M + 1 + 1) ^ (j + 1) :=
      Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by omega)
    change (M + 1).choose (j + 1) + 1 ≤ (M + 1 + 1) ^ (j + 1)
    omega
  have hprod : ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) ≤
      ∏ j ∈ range (k + 1), (M + 2) ^ (j + 1) := Finset.prod_le_prod' hterm
  have hsum : ∏ j ∈ range (k + 1), (M + 2) ^ (j + 1) = (M + 2) ^ (∑ j ∈ range (k + 1), (j + 1)) :=
    Finset.prod_pow_eq_pow_sum _ _ _
  refine lt_of_le_of_lt hprod ?_
  rw [hsum]
  have hsumle : 2 * (∑ j ∈ range (k + 1), (j + 1)) = (k + 1) * (k + 2) := two_mul_sum_range_succ k
  have hM0 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogpos : 0 < Real.log ((M : ℝ) + 2) := Real.log_pos (by linarith)
  set N := ∑ j ∈ range (k + 1), (j + 1) with hN
  have hNR : 2 * (N : ℝ) = ((k : ℝ) + 1) * ((k : ℝ) + 2) := by exact_mod_cast hsumle
  have hNle : 2 * (N : ℝ) ≤ ((k : ℝ) + 2) ^ 2 := by
    rw [hNR]
    nlinarith [(by positivity : (0 : ℝ) ≤ (k : ℝ))]
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hreal : ((M + 2 : ℕ) : ℝ) ^ N < (2 : ℝ) ^ M := by
    rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    have hkey : 2 * (N : ℝ) * Real.log ((M : ℝ) + 2) ≤ (M : ℝ) :=
      (mul_le_mul_of_nonneg_right hNle hlogpos.le).trans h
    nlinarith
  exact_mod_cast hreal

theorem HeightSize.word_half {L ℓ : ℝ} (h : HeightSize L ℓ) {M k : ℕ} (hM1 : 6 * L ^ 2 * ℓ ≤ M)
    (hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1) (hk : (k : ℝ) ≤ L + 1) :
    ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) < 2 ^ M := by
  have hL := h.hundred_le
  have hℓ := h.one_le
  have hM : 1 ≤ M := by
    have h1 : (1 : ℝ) ≤ 6 * L ^ 2 * ℓ := by nlinarith [sq_nonneg L]
    have : (1 : ℝ) ≤ M := h1.trans hM1
    exact_mod_cast this
  refine prod_choose_lt_two_pow_of_log hM ?_
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlog : Real.log ((M : ℝ) + 2) ≤ 3 * ℓ := by
    have h1 := Real.log_le_log (by positivity) (h.M_add_two_le hM2)
    rw [Real.log_pow] at h1
    rw [h.log_eq]
    exact_mod_cast h1
  have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith)
  have hsq : ((k : ℝ) + 2) ^ 2 ≤ 2 * L ^ 2 := by nlinarith
  calc ((k : ℝ) + 2) ^ 2 * Real.log ((M : ℝ) + 2) ≤ 2 * L ^ 2 * (3 * ℓ) :=
        mul_le_mul hsq hlog hlog0 (by positivity)
    _ = 6 * L ^ 2 * ℓ := by ring
    _ ≤ M := hM1

/-- The word of height `1` and low energy at height `exp L`, for any length `K ≥ 48 L² ℓ`. -/
theorem HeightSize.exists_data_energy {L ℓ t : ℝ} (h : HeightSize L ℓ) (hexp : Real.exp L = |t|)
    {K : ℕ} (hK : 48 * L ^ 2 * ℓ ≤ K) :
    ∃ (M k N : ℕ) (c : ℕ → ℤ), WordSetup 1 16 M k N c t ∧ 6 * M + 6 ≤ K ∧
      (M : ℝ) + 1 ≤ 8 * (L ^ 2 * ℓ) ∧ wordEnergy M c ≤ 12 * ((M : ℝ) + 1) ^ 2 := by
  have hL := h.hundred_le
  have hℓ := h.one_le
  set M := ⌈6 * L ^ 2 * ℓ⌉₊ with hM
  set k := ⌈L⌉₊ with hk
  set N := ⌊L / 2⌋₊ with hN
  have hM1 : 6 * L ^ 2 * ℓ ≤ M := Nat.le_ceil _
  have hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : L ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hN1 : (N : ℝ) ≤ L / 2 := Nat.floor_le (by linarith)
  have hN2 : L / 2 - 1 ≤ (N : ℝ) := by
    have := Nat.lt_floor_add_one (L / 2)
    linarith
  have hN3 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hone : (1 : ℝ) ≤ L ^ 2 * ℓ := by nlinarith
  obtain ⟨c, hc, hm, h0, hE⟩ := exists_lowEnergy_word (h.word_half hM1 hM2 hk2)
  refine ⟨M, k, N, c, ⟨le_rfl, by norm_num, fun a => ?_, hm, h0, hN3, ?_, ?_, ?_⟩, ?_, by nlinarith, hE⟩
  · exact_mod_cast hc.bound a
  · rw [← hexp]
    have := h.low hN1
    simpa using this
  · rw [← hexp]
    have := h.step hM2 hN2
    simpa using this
  · rw [← hexp]
    have := h.up hM2 hk1
    simpa using this
  · have : ((6 * M + 6 : ℕ) : ℝ) ≤ K := by
      push_cast
      nlinarith
    exact_mod_cast this

/-- The constant of the sup bound. -/
theorem constant_le {L ℓ : ℝ} {M : ℕ} (hL : 0 < L) (hℓ : 0 < ℓ) (hM : (M : ℝ) + 1 ≤ 8 * (L ^ 2 * ℓ)) :
    1 - 1 / (72 * (16 : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 3) ≤ 1 - 1 / (10 ^ 7 * L ^ 6 * ℓ ^ 3) := by
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have h3 : ((M : ℝ) + 1) ^ 3 ≤ (8 * (L ^ 2 * ℓ)) ^ 3 := pow_le_pow_left₀ hM1.le hM 3
  have hpos : 0 < L ^ 6 * ℓ ^ 3 := by positivity
  have h4 : (72 * (16 : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 3) ≤ 10 ^ 7 * L ^ 6 * ℓ ^ 3 := by
    have e : (8 * (L ^ 2 * ℓ)) ^ 3 = 512 * (L ^ 6 * ℓ ^ 3) := by ring
    rw [e] at h3
    nlinarith
  have := one_div_le_one_div_of_le (by positivity) h4
  linarith

/-- **The sup bound with the saving `L⁻⁶`.** -/
theorem norm_sum_le_of_large_energy :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ,
      48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ N →
      ‖∑ n ∈ Finset.Ico 1 N, Complex.exp (Complex.I * (t * Real.log n))‖ ≤
        (N : ℝ) * (1 - 1 / (10 ^ 7 * Real.log |t| ^ 6 * Real.log (Real.log |t|) ^ 3)) := by
  obtain ⟨T₀, hT₀, hsize⟩ := eventually_heightSize
  refine ⟨T₀, hT₀, fun t ht N hN => ?_⟩
  have h := hsize t ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₀ ht
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp hN ⊢
  generalize Real.log L = ℓ at h hN ⊢
  obtain ⟨M, k, N₁, c, hS, hNnat, hM, hE⟩ := h.exists_data_energy hexp hN
  refine (hS.norm_sum_le_of_energy hE hNnat).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N))
  exact constant_le (by linarith [h.hundred_le]) (by linarith [h.one_le]) hM

/-- **The sup bound on progressions with the saving `L⁻⁶`, uniformly in the modulus.** -/
theorem norm_sum_ap_le_of_large_energy :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ K q r : ℕ, 1 ≤ r → r ≤ q →
      48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ K →
      ‖∑ m ∈ range K, Complex.exp (Complex.I * (t * Real.log ((r + q * m : ℕ) : ℝ)))‖ ≤
        (K : ℝ) * (1 - 1 / (10 ^ 7 * Real.log |t| ^ 6 * Real.log (Real.log |t|) ^ 3)) := by
  obtain ⟨T₀, hT₀, hsize⟩ := eventually_heightSize
  refine ⟨T₀, hT₀, fun t ht K q r hr1 hr hK => ?_⟩
  have h := hsize t ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₀ ht
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp hK ⊢
  generalize Real.log L = ℓ at h hK ⊢
  obtain ⟨M, k, N₁, c, hS, hNnat, hM, hE⟩ := h.exists_data_energy hexp hK
  refine (hS.norm_sum_ap_le_of_energy hE (by omega) hr1 hr hNnat).trans
    (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg K))
  exact constant_le (by linarith [h.hundred_le]) (by linarith [h.one_le]) hM

/-! ### The primes -/

/-- The number of prime factors of `n`, with multiplicity, is at most `log n / log 2`. -/
theorem sum_factorization_le_log (n : ℕ) :
    ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) ≤ Real.log n / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization,
    Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact Real.log_le_log (by norm_num) (by exact_mod_cast hp'.two_le)

/-- Cauchy–Schwarz on the prime factors of `n`. -/
theorem sq_phaseDist_le_factorization (t : ℝ) (n : ℕ) :
    phaseDist t n ^ 2 ≤ Real.log n / Real.log 2 *
      ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * phaseDist t p ^ 2 := by
  have h1 := phaseDist_le_factorization t n
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq n.primeFactors
    (fun p => √(n.factorization p : ℝ)) (fun p => √(n.factorization p : ℝ) * phaseDist t p)
  have e1 : ∀ p ∈ n.primeFactors, √(n.factorization p : ℝ) *
      (√(n.factorization p : ℝ) * phaseDist t p) = (n.factorization p : ℝ) * phaseDist t p := by
    intro p _
    rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have e2 : ∀ p ∈ n.primeFactors, √(n.factorization p : ℝ) ^ 2 = (n.factorization p : ℝ) := by
    intro p _
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have e3 : ∀ p ∈ n.primeFactors, (√(n.factorization p : ℝ) * phaseDist t p) ^ 2 =
      (n.factorization p : ℝ) * phaseDist t p ^ 2 := by
    intro p _
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3] at hcs
  have hnn : 0 ≤ ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * phaseDist t p ^ 2 :=
    sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  calc phaseDist t n ^ 2 ≤ (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * phaseDist t p) ^ 2 :=
        pow_le_pow_left₀ (phaseDist_nonneg t n) h1 2
    _ ≤ _ := hcs
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_factorization_le_log n) hnn

/-- **From the integers to the primes in mean square.** -/
theorem sum_sq_phaseDist_le_primes (t : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ range N, phaseDist t n ^ 2 ≤
      3 * Real.log N * (N : ℝ) * ∑ p ∈ N.primesBelow, phaseDist t p ^ 2 / p := by
  classical
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog2' : 0 < Real.log 2 := by linarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hratio : Real.log N / Real.log 2 ≤ 3 / 2 * Real.log N := by
    rw [div_le_iff₀ hlog2']
    nlinarith
  have hzero : phaseDist t 0 = 0 := by
    simp [phaseDist, dist01]
  have hstep : ∀ n ∈ range N, phaseDist t n ^ 2 ≤ 3 / 2 * Real.log N *
      ∑ p ∈ N.primesBelow, (n.factorization p : ℝ) * phaseDist t p ^ 2 := by
    intro n hn
    have hnN := mem_range.mp hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [hzero]
      simp
    have h1 := sq_phaseDist_le_factorization t n
    have hsub : ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * phaseDist t p ^ 2 =
        ∑ p ∈ N.primesBelow, (n.factorization p : ℝ) * phaseDist t p ^ 2 := by
      refine Finset.sum_subset (fun p hp => ?_) fun p _ hp => ?_
      · rw [Nat.mem_primesBelow]
        have hp' := Nat.mem_primeFactors.mp hp
        exact ⟨lt_of_le_of_lt (Nat.le_of_dvd hpos hp'.2.1) hnN, hp'.1⟩
      · have : n.factorization p = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
          exact hp
        rw [this]
        simp
    rw [hsub] at h1
    have hnn : 0 ≤ ∑ p ∈ N.primesBelow, (n.factorization p : ℝ) * phaseDist t p ^ 2 :=
      sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hn1 : (n : ℝ) ≤ N := by exact_mod_cast hnN.le
    have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    have hlogn : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hn1
    have hr : Real.log n / Real.log 2 ≤ Real.log N / Real.log 2 :=
      div_le_div_of_nonneg_right hlogn hlog2'.le
    exact h1.trans (mul_le_mul_of_nonneg_right (hr.trans hratio) hnn)
  calc ∑ n ∈ range N, phaseDist t n ^ 2
      ≤ ∑ n ∈ range N, 3 / 2 * Real.log N *
          ∑ p ∈ N.primesBelow, (n.factorization p : ℝ) * phaseDist t p ^ 2 := sum_le_sum hstep
    _ = 3 / 2 * Real.log N * ∑ p ∈ N.primesBelow,
          (∑ n ∈ range N, (n.factorization p : ℝ)) * phaseDist t p ^ 2 := by
        rw [← mul_sum, Finset.sum_comm]
        congr 1
        refine sum_congr rfl fun p _ => ?_
        rw [sum_mul]
    _ ≤ 3 / 2 * Real.log N * ∑ p ∈ N.primesBelow, (2 * (N : ℝ) / p) * phaseDist t p ^ 2 := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun p hp => ?_) (by positivity)
        exact mul_le_mul_of_nonneg_right
          (sum_factorization_le (Nat.mem_primesBelow.mp hp).2 N) (sq_nonneg _)
    _ = _ := by
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun p _ => ?_
        ring

/-- **The mean square mass of misaligned primes.** For every `N ≥ 48 L² ℓ`,
`Σ_{p<N} ‖t log p/2π‖²/p ≥ 1/(10⁹ L⁶ ℓ⁴)`. -/
theorem le_sum_primes_sq_phaseDist :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ,
      48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ N →
      1 / (10 ^ 9 * Real.log |t| ^ 6 * Real.log (Real.log |t|) ^ 4) ≤
        ∑ p ∈ N.primesBelow, phaseDist t p ^ 2 / p := by
  obtain ⟨T₀, hT₀, hsize⟩ := eventually_heightSize
  refine ⟨T₀, hT₀, fun t ht N hN => ?_⟩
  have h := hsize t ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₀ ht
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp hN ⊢
  generalize hℓdef : Real.log L = ℓ at h hN ⊢
  have hL := h.hundred_le
  have hℓ := h.one_le
  have hlogle := h.log_le
  have hLpos : 0 < L := by linarith
  have hℓpos : 0 < ℓ := by linarith
  set K := ⌈48 * L ^ 2 * ℓ⌉₊ with hKdef
  have hK1 : 48 * L ^ 2 * ℓ ≤ K := Nat.le_ceil _
  have hK2 : (K : ℝ) ≤ 48 * L ^ 2 * ℓ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hKN : K ≤ N := Nat.ceil_le.mpr hN
  obtain ⟨M, k, N₁, c, hS, hNnat, hM, hE⟩ := h.exists_data_energy hexp hK1
  have hK0 : 1 ≤ K := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hmain := hS.le_sum_sq_ap hE 0 (q := 1) (r := 0) le_rfl (Nat.zero_le 1) hNnat
  have hsum : ∑ m ∈ range K, rotDist t 0 (0 + 1 * m) ^ 2 = ∑ n ∈ range K, phaseDist t n ^ 2 := by
    refine sum_congr rfl fun n _ => ?_
    rw [zero_add, one_mul, rotDist_zero]
  rw [hsum] at hmain
  have htr := sum_sq_phaseDist_le_primes t hK0
  have hlogK : Real.log K ≤ 4 * ℓ := by
    have hbound : (K : ℝ) ≤ L ^ 4 := by
      have hsq : 0 < L ^ 2 := by positivity
      have h1 : 48 * L ^ 2 * ℓ + 1 ≤ 49 * L ^ 2 * ℓ := by nlinarith
      have h2 : 49 * L ^ 2 * ℓ ≤ L ^ 2 * (49 / 100 * L) := by nlinarith
      have h3 : L ^ 2 * (49 / 100 * L) ≤ L ^ 2 * L ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hsq.le
        nlinarith
      have e : L ^ 4 = L ^ 2 * L ^ 2 := by ring
      linarith
    have h1 := Real.log_le_log hKpos hbound
    rw [Real.log_pow, hℓdef] at h1
    exact_mod_cast h1
  have hP0 : 0 ≤ ∑ p ∈ K.primesBelow, phaseDist t p ^ 2 / p :=
    sum_nonneg fun p _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hmono : ∑ p ∈ K.primesBelow, phaseDist t p ^ 2 / p ≤
      ∑ p ∈ N.primesBelow, phaseDist t p ^ 2 / p := by
    refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ =>
      div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 hKN, hp.2⟩
  refine le_trans ?_ hmono
  set P := ∑ p ∈ K.primesBelow, phaseDist t p ^ 2 / p with hP
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have h3 : ((M : ℝ) + 1) ^ 3 ≤ 512 * (L ^ 6 * ℓ ^ 3) := by
    have := pow_le_pow_left₀ hM1.le hM 3
    calc ((M : ℝ) + 1) ^ 3 ≤ (8 * (L ^ 2 * ℓ)) ^ 3 := this
      _ = _ := by ring
  have hchain : (K : ℝ) * (1 / (576 * (16 : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 3)) ≤
      3 * (4 * ℓ) * (K : ℝ) * P := by
    refine hmain.trans (htr.trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ hP0
    exact mul_le_mul_of_nonneg_right (by linarith) hKpos.le
  have hcancel : 1 / (576 * (16 : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 3) ≤ 12 * ℓ * P := by
    have e : 3 * (4 * ℓ) * (K : ℝ) * P = (K : ℝ) * (12 * ℓ * P) := by ring
    rw [e] at hchain
    exact le_of_mul_le_mul_left hchain hKpos
  have hdenom : 1 / (576 * (16 : ℝ) ^ 2 * (512 * (L ^ 6 * ℓ ^ 3))) ≤
      1 / (576 * (16 : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 3) :=
    one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left h3 (by norm_num))
  have hfinal : 1 / (576 * (16 : ℝ) ^ 2 * (512 * (L ^ 6 * ℓ ^ 3))) ≤ 12 * ℓ * P :=
    hdenom.trans hcancel
  have hpos6 : 0 < L ^ 6 * ℓ ^ 3 := by positivity
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at hfinal
  have e : (12 * ℓ * P) * (576 * (16 : ℝ) ^ 2 * (512 * (L ^ 6 * ℓ ^ 3))) =
      905969664 * (P * (L ^ 6 * ℓ ^ 4)) := by ring
  have hX : 0 ≤ P * (L ^ 6 * ℓ ^ 4) := by positivity
  have e2 : P * (10 ^ 9 * L ^ 6 * ℓ ^ 4) = 10 ^ 9 * (P * (L ^ 6 * ℓ ^ 4)) := by ring
  rw [e2]
  rw [e] at hfinal
  linarith

/-- **The critical column.** For every `N ≥ 48 L² ℓ`,
`Σ_{p<N} (1 − cos(t log p))/√p ≥ 8/(10⁹ L⁶ ℓ⁴)`. -/
theorem le_sum_primes_critical_energy :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ,
      48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ N →
      8 / (10 ^ 9 * Real.log |t| ^ 6 * Real.log (Real.log |t|) ^ 4) ≤
        ∑ p ∈ N.primesBelow, (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
  obtain ⟨T₀, hT₀, hmass⟩ := le_sum_primes_sq_phaseDist
  refine ⟨T₀, hT₀, fun t ht N hN => ?_⟩
  have hm := hmass t ht N hN
  have hstep : 8 * ∑ p ∈ N.primesBelow, phaseDist t p ^ 2 / p ≤
      ∑ p ∈ N.primesBelow, (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
    rw [mul_sum]
    refine sum_le_sum fun p hp => ?_
    have hp' := (Nat.mem_primesBelow.mp hp).2
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_le
    have h1 := eight_mul_sq_le_one_sub_cos (t * Real.log p / (2 * π))
    have e : 2 * π * (t * Real.log p / (2 * π)) = t * Real.log p := by
      field_simp
    rw [e] at h1
    have hd : phaseDist t p = dist01 (t * Real.log p / (2 * π)) := rfl
    have hsq : √(p : ℝ) ≤ p := by
      have := Real.sqrt_le_sqrt hp1
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have hsqpos : 0 < √(p : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hnum : 0 ≤ 1 - Real.cos (t * Real.log p) := by linarith [Real.cos_le_one (t * Real.log p)]
    calc 8 * (phaseDist t p ^ 2 / p) = 8 * phaseDist t p ^ 2 / p := by ring
      _ ≤ (1 - Real.cos (t * Real.log p)) / p :=
          div_le_div_of_nonneg_right (by rw [hd]; exact h1) (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_left hnum hsqpos hsq
  refine le_trans ?_ hstep
  have e : 8 / (10 ^ 9 * Real.log |t| ^ 6 * Real.log (Real.log |t|) ^ 4) =
      8 * (1 / (10 ^ 9 * Real.log |t| ^ 6 * Real.log (Real.log |t|) ^ 4)) := by ring
  rw [e]
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
