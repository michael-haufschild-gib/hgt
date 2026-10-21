import GaloisForLFunctions.RHTower.Sieve.GuthMaynardTheoremOneOneKeyPropPieces
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLargeValuesStatement

/-!
# Guth–Maynard Theorem 1.1 from Proposition 3.1

`guthMaynard_largeValues_of_keyProp`: if Proposition 3.1 holds for a smooth bump `w`
(`KeyPropBound w`), then for every `ε > 0` there is `C` with

`|W| ≤ C T^ε (N²/V² + N^{18/5}/V⁴ + T N^{12/5}/V⁴)`

for every `1`-separated set `W ⊂ [T₀, T₀ + T]` on which `|Σ_{N<n≤2N} b_n n^{it}| ≥ V`, `|b_n| ≤ 1`,
`T ≥ 2` — exactly `GuthMaynardLargeValuesBound`.  This is the paper's §3 reduction.  The cases:

* `T ≤ N`: the log-free mean value count gives `|W| ≤ 1254 N²/V²`;
* `N ≤ 18438¹⁰`: `|W| ≤ T + 1` and `V ≤ N` give `|W| ≤ 2·18438²⁰ T N^{12/5}/V⁴`;
* `V < 4N^{7/10}`: the mean value count gives `|W| ≤ 20064 T N^{12/5}/V⁴`
  (`TNV⁻² ≤ 16 TN^{12/5}V⁻⁴`);
* `V ≥ N^{4/5}`, `N ≥ 18438¹⁰`: the Huxley count applies (`V² ≥ N^{8/5} ≥ 18438 N^{3/2}`) and
  `TN⁴V⁻⁶ ≤ TN^{12/5}V⁻⁴`;
* `4N^{7/10} ≤ V ≤ N^{4/5}`, `N < T`: split `(N, 2N]` into two plateau pieces; on one of them the
  partial sum is at least `V/2`; that piece is a smoothed polynomial of length `N_i ∈ [5N/6, 2N]`
  with `V/2 ∈ [N_i^{7/10}, N_i^{4/5}]`, and Proposition 3.1 on windows of length `N_i^{6/5}` bounds
  it by `C T^ε (T + N_i^{6/5}) N_i^{12/5} (V/2)⁻⁴` (`card_le_of_keyPropBound`).
-/

set_option autoImplicit false

open Finset Complex

namespace RHTower.GuthMaynard

open RHTower.Sieve

noncomputable section

/-! ### Elementary rpow facts -/

theorem two_rpow_le_two_pow {x : ℝ} {k : ℕ} (hx : x ≤ k) : (2 : ℝ) ^ x ≤ 2 ^ k := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hx

/-- `(cN)^x ≤ c^k N^x` for `c ≥ 1`, `N ≥ 0`, `x ≤ k`. -/
theorem mul_rpow_le {c N x : ℝ} {k : ℕ} (hc : 1 ≤ c) (hN : 0 ≤ N) (hx : x ≤ k) :
    (c * N) ^ x ≤ c ^ k * N ^ x := by
  rw [Real.mul_rpow (by linarith) hN]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hN _)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hc hx

theorem rpow_six_fifths_mul_rpow_twelve_fifths {N : ℝ} (hN : 0 < N) :
    N ^ (6 / 5 : ℝ) * N ^ (12 / 5 : ℝ) = N ^ (18 / 5 : ℝ) := by
  rw [← Real.rpow_add hN]; norm_num

/-- `N⁴ = N^{12/5} N^{8/5}`. -/
theorem pow_four_eq_rpow {N : ℝ} (hN : 0 < N) :
    N ^ 4 = N ^ (12 / 5 : ℝ) * N ^ (8 / 5 : ℝ) := by
  rw [← Real.rpow_add hN]; norm_num

/-! ### The five cases -/

/-- **Case `T ≤ N`.** -/
theorem card_le_of_length_ge {N : ℕ} (hN : 1 ≤ N) {T T₀ V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1) {W : Finset ℝ} (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T)
    (hsep : IsSeparated 1 W) (hbig : ∀ t ∈ W, V ≤ ‖dyadicPoly N b t‖) (hTN : T ≤ N) :
    (W.card : ℝ) ≤ 1254 * ((N : ℝ) ^ 2 / V ^ 2) := by
  have h := card_mul_sq_le_meanValue hN hT hV.le hb hW hsep hbig
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
  nlinarith

/-- **Case `V < 4 N^{7/10}`, `N ≤ T`.** -/
theorem card_le_of_level_lt {N : ℕ} (hN : 1 ≤ N) {T T₀ V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1) {W : Finset ℝ} (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T)
    (hsep : IsSeparated 1 W) (hbig : ∀ t ∈ W, V ≤ ‖dyadicPoly N b t‖) (hNT : (N : ℝ) ≤ T)
    (hlev : V < 4 * (N : ℝ) ^ (7 / 10 : ℝ)) :
    (W.card : ℝ) ≤ 20064 * (T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
  have h := card_mul_sq_le_meanValue hN hT hV.le hb hW hsep hbig
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  -- `N V² ≤ 16 N^{12/5}`
  have hV2 : V ^ 2 ≤ 16 * (N : ℝ) ^ (7 / 5 : ℝ) := by
    have h1 : V ^ 2 ≤ (4 * (N : ℝ) ^ (7 / 10 : ℝ)) ^ 2 := pow_le_pow_left₀ hV.le hlev.le 2
    have h2 : ((N : ℝ) ^ (7 / 10 : ℝ)) ^ 2 = (N : ℝ) ^ (7 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    nlinarith
  have hNV : (N : ℝ) * V ^ 2 ≤ 16 * (N : ℝ) ^ (12 / 5 : ℝ) := by
    have e : (N : ℝ) ^ (12 / 5 : ℝ) = N * (N : ℝ) ^ (7 / 5 : ℝ) := by
      rw [show (12 / 5 : ℝ) = 1 + 7 / 5 by norm_num, Real.rpow_add hN0, Real.rpow_one]
    rw [e]; nlinarith
  have hcard : (W.card : ℝ) * V ^ 2 ≤ 1254 * T * N := by nlinarith
  rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
  have hc0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  calc (W.card : ℝ) * V ^ 4 = (W.card * V ^ 2) * V ^ 2 := by ring
    _ ≤ (1254 * T * N) * V ^ 2 := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1254 * T * (N * V ^ 2) := by ring
    _ ≤ 1254 * T * (16 * (N : ℝ) ^ (12 / 5 : ℝ)) := by gcongr
    _ = 20064 * (T * (N : ℝ) ^ (12 / 5 : ℝ)) := by ring

/-- **Case `V ≥ N^{4/5}`, `N ≥ 18438¹⁰`** (the Huxley range). -/
theorem card_le_of_level_ge {N : ℕ} (hN : 1 ≤ N) {T T₀ V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1) {W : Finset ℝ} (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T)
    (hsep : IsSeparated 1 W) (hbig : ∀ t ∈ W, V ≤ ‖dyadicPoly N b t‖)
    (hN0 : (18438 : ℝ) ^ 10 ≤ N) (hlev : (N : ℝ) ^ (4 / 5 : ℝ) ≤ V) :
    (W.card : ℝ) ≤ 2110279680 * (1 + Real.log (T + 1)) *
      ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  -- `V² ≥ N^{8/5}`
  have hV2 : (N : ℝ) ^ (8 / 5 : ℝ) ≤ V ^ 2 := by
    have h1 := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hlev 2
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hNp.le, show (4 / 5 : ℝ) * ((2 : ℕ) : ℝ) = 8 / 5 by
      norm_num] at h1
  -- the Huxley threshold `18438 N √N ≤ N^{8/5}`
  have hroot : (18438 : ℝ) ≤ (N : ℝ) ^ ((10 : ℕ) : ℝ)⁻¹ := by
    have h := Real.rpow_le_rpow (by positivity) hN0 (by positivity : (0 : ℝ) ≤ ((10 : ℕ) : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)] at h
  have hthr : 18438 * (N : ℝ) * Real.sqrt N ≤ V ^ 2 := by
    have e : (N : ℝ) ^ (8 / 5 : ℝ) = (N : ℝ) ^ ((10 : ℕ) : ℝ)⁻¹ * ((N : ℝ) * Real.sqrt N) := by
      rw [Real.sqrt_eq_rpow, show (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ (1 + 1 / 2 : ℝ) by
        rw [Real.rpow_add hNp, Real.rpow_one], ← Real.rpow_add hNp]
      norm_num
    have hNs : 0 ≤ (N : ℝ) * Real.sqrt N := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hroot hNs]
  have h := card_mul_sq_le_huxley hN hT hV hb hW hsep hbig hthr
  -- `T N⁴/V⁴ ≤ T N^{12/5}/V²`
  have hV0 : 0 < V ^ 2 := by positivity
  have hq : T * (N : ℝ) ^ 4 / V ^ 4 ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hV0, pow_four_eq_rpow hNp]
    have : (N : ℝ) ^ (12 / 5 : ℝ) * (N : ℝ) ^ (8 / 5 : ℝ) * V ^ 2 ≤
        (N : ℝ) ^ (12 / 5 : ℝ) * V ^ 2 * V ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV2 (by positivity)) hV0.le
    calc T * ((N : ℝ) ^ (12 / 5 : ℝ) * (N : ℝ) ^ (8 / 5 : ℝ)) * V ^ 2
        = T * ((N : ℝ) ^ (12 / 5 : ℝ) * (N : ℝ) ^ (8 / 5 : ℝ) * V ^ 2) := by ring
      _ ≤ T * ((N : ℝ) ^ (12 / 5 : ℝ) * V ^ 2 * V ^ 2) := mul_le_mul_of_nonneg_left this hT
      _ = T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ 4 := by ring
  have hlog : 0 ≤ 1 + Real.log (T + 1) := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 1)]
  have hstep : (W.card : ℝ) * V ^ 2 ≤ 2110279680 * (1 + Real.log (T + 1)) *
      ((N : ℝ) ^ 2 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 2) := by
    refine h.trans ?_
    have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
    have : 6594624 * T * (N : ℝ) ^ 4 / V ^ 4 + (N : ℝ) ^ 2 ≤
        6594624 * ((N : ℝ) ^ 2 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 2) := by
      have e : 6594624 * T * (N : ℝ) ^ 4 / V ^ 4 = 6594624 * (T * (N : ℝ) ^ 4 / V ^ 4) := by ring
      rw [e]; nlinarith
    calc 320 * (1 + Real.log (T + 1)) * (6594624 * T * (N : ℝ) ^ 4 / V ^ 4 + (N : ℝ) ^ 2)
        ≤ 320 * (1 + Real.log (T + 1)) *
            (6594624 * ((N : ℝ) ^ 2 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have e : (N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4 =
      ((N : ℝ) ^ 2 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 2) / V ^ 2 := by
    field_simp
  rw [e, ← mul_div_assoc, le_div_iff₀ hV0]
  exact hstep

/-- **Case `N ≤ 18438¹⁰`.** -/
theorem card_le_of_length_le {N : ℕ} (hN : 1 ≤ N) {T T₀ V : ℝ} (hT : 1 ≤ T) (hV : 0 < V)
    {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1) {W : Finset ℝ} (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T)
    (hsep : IsSeparated 1 W) (hbig : ∀ t ∈ W, V ≤ ‖dyadicPoly N b t‖)
    (hN0 : (N : ℝ) ≤ 18438 ^ 10) :
    (W.card : ℝ) ≤ 2 * ((18438 : ℝ) ^ 10) ^ 2 * (T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
  rcases W.eq_empty_or_nonempty with he | ⟨t₀, ht₀⟩
  · rw [he, card_empty, Nat.cast_zero]; positivity
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcard : (W.card : ℝ) ≤ 2 * T := by
    have := card_le_of_separated (u := id) one_pos (by linarith) hsep hW
    simp only [div_one] at this
    linarith
  have hVN : V ≤ N := (hbig t₀ ht₀).trans (norm_dyadicPoly_le hb t₀)
  -- `V⁴ ≤ N⁴ ≤ 18438²⁰ N^{12/5}`
  have h4 : V ^ 4 ≤ ((18438 : ℝ) ^ 10) ^ 2 * (N : ℝ) ^ (12 / 5 : ℝ) := by
    have h85 : (N : ℝ) ^ (8 / 5 : ℝ) ≤ ((18438 : ℝ) ^ 10) ^ 2 := by
      have : (N : ℝ) ^ (8 / 5 : ℝ) ≤ (N : ℝ) ^ ((2 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      rw [Real.rpow_natCast] at this
      exact this.trans (pow_le_pow_left₀ hNp.le hN0 2)
    calc V ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ hV.le hVN 4
      _ = (N : ℝ) ^ (12 / 5 : ℝ) * (N : ℝ) ^ (8 / 5 : ℝ) := pow_four_eq_rpow hNp
      _ ≤ (N : ℝ) ^ (12 / 5 : ℝ) * ((18438 : ℝ) ^ 10) ^ 2 :=
          mul_le_mul_of_nonneg_left h85 (by positivity)
      _ = _ := by ring
  have hT' : T ≤ ((18438 : ℝ) ^ 10) ^ 2 * (T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Case `4N^{7/10} ≤ V ≤ N^{4/5}`, `6 ≤ N < T`**, through Proposition 3.1. -/
theorem card_le_of_keyProp_middle {w : CGLSmoothBump} (hkey : KeyPropBound w) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T T₀ V : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      6 ≤ N → (N : ℝ) < T → (∀ n, ‖b n‖ ≤ 1) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
      IsSeparated 1 W → 4 * (N : ℝ) ^ (7 / 10 : ℝ) ≤ V → V ≤ (N : ℝ) ^ (4 / 5 : ℝ) →
      (∀ t ∈ W, V ≤ ‖dyadicPoly N b t‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
  classical
  obtain ⟨K, hK0, hK⟩ := card_le_of_keyPropBound hkey hε
  refine ⟨1024 * K, by positivity, ?_⟩
  intro N T T₀ V b W hN hNT hb hW hsep hlo hhi hbig
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hT : 0 < T := hNp.trans hNT
  have hV : 0 < V := lt_of_lt_of_le (by positivity) hlo
  obtain ⟨N₁, N₂, P₁, P₂, hU, hD, hP₁, hP₂, h1, h2, h3, h4, -, -⟩ := exists_two_plateau_pieces hN
  -- one piece: the points where its partial sum is at least `V/2`
  have piece : ∀ (M : ℕ) (P : Finset ℕ),
      (∀ n ∈ P, M < n ∧ n ≤ 2 * M ∧ 6 * M ≤ 5 * n ∧ 5 * n ≤ 9 * M) → 5 * N ≤ 6 * M → M ≤ 2 * N →
      (((W.filter fun t : ℝ => V / 2 ≤
          ‖∑ n ∈ P, b n * Complex.exp (Complex.I * t * Real.log n)‖).card
        : ℕ) : ℝ) ≤ 512 * K * T ^ ε *
          ((N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
    intro M P hP hM1 hM2
    have hM1' : (5 : ℝ) * N ≤ 6 * M := by exact_mod_cast hM1
    have hM2' : (M : ℝ) ≤ 2 * N := by exact_mod_cast hM2
    have hMp : (0 : ℝ) < M := by linarith
    have hlo' : (M : ℝ) ^ (7 / 10 : ℝ) ≤ V / 2 := by
      calc (M : ℝ) ^ (7 / 10 : ℝ) ≤ (2 * N : ℝ) ^ (7 / 10 : ℝ) :=
            Real.rpow_le_rpow hMp.le hM2' (by norm_num)
        _ ≤ 2 ^ 1 * (N : ℝ) ^ (7 / 10 : ℝ) := mul_rpow_le (by norm_num) hNp.le (by norm_num)
        _ ≤ V / 2 := by linarith
    have hhi' : V / 2 ≤ (M : ℝ) ^ (4 / 5 : ℝ) := by
      have h2r : (2 : ℝ) ^ (4 / 5 : ℝ) ≤ 2 ^ 1 := two_rpow_le_two_pow (by norm_num)
      calc V / 2 ≤ (N : ℝ) ^ (4 / 5 : ℝ) / 2 ^ (4 / 5 : ℝ) := by
            rw [pow_one] at h2r
            calc V / 2 ≤ (N : ℝ) ^ (4 / 5 : ℝ) / 2 := by linarith
              _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) h2r
        _ = ((N : ℝ) / 2) ^ (4 / 5 : ℝ) := (Real.div_rpow hNp.le (by norm_num) _).symm
        _ ≤ (M : ℝ) ^ (4 / 5 : ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hb' : ∀ n, ‖(fun n => if n ∈ P then b n else 0) n‖ ≤ 1 := fun n => by
      dsimp only; split_ifs
      · exact hb n
      · simp
    have hbound := hK M T T₀ (V / 2) (fun n => if n ∈ P then b n else 0)
      (W.filter fun t : ℝ => V / 2 ≤ ‖∑ n ∈ P, b n * Complex.exp (Complex.I * t * Real.log n)‖)
      (by omega) (by linarith) hb' (fun t ht => hW t (Finset.mem_filter.mp ht).1)
      (fun x hx y hy hxy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
      hlo' hhi' (fun t ht => by
        rw [smoothedDyadicPoly_indicator w hP]; exact (Finset.mem_filter.mp ht).2)
    refine hbound.trans ?_
    -- `(T + M^{6/5}) M^{12/5} (V/2)⁻⁴ ≤ 512 (N^{18/5} + T N^{12/5}) V⁻⁴`
    have h65 : (M : ℝ) ^ (6 / 5 : ℝ) ≤ 2 ^ 2 * (N : ℝ) ^ (6 / 5 : ℝ) :=
      (Real.rpow_le_rpow hMp.le hM2' (by norm_num)).trans
        (mul_rpow_le (by norm_num) hNp.le (by norm_num))
    have h125 : (M : ℝ) ^ (12 / 5 : ℝ) ≤ 2 ^ 3 * (N : ℝ) ^ (12 / 5 : ℝ) :=
      (Real.rpow_le_rpow hMp.le hM2' (by norm_num)).trans
        (mul_rpow_le (by norm_num) hNp.le (by norm_num))
    have hprod : (T + (M : ℝ) ^ (6 / 5 : ℝ)) * (M : ℝ) ^ (12 / 5 : ℝ) ≤
        32 * ((N : ℝ) ^ (18 / 5 : ℝ) + T * (N : ℝ) ^ (12 / 5 : ℝ)) := by
      have e := rpow_six_fifths_mul_rpow_twelve_fifths hNp
      calc (T + (M : ℝ) ^ (6 / 5 : ℝ)) * (M : ℝ) ^ (12 / 5 : ℝ)
          ≤ (T + 2 ^ 2 * (N : ℝ) ^ (6 / 5 : ℝ)) * (2 ^ 3 * (N : ℝ) ^ (12 / 5 : ℝ)) := by
            gcongr
        _ = 8 * (T * (N : ℝ) ^ (12 / 5 : ℝ)) +
              32 * ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ (12 / 5 : ℝ)) := by ring
        _ ≤ 32 * ((N : ℝ) ^ (18 / 5 : ℝ) + T * (N : ℝ) ^ (12 / 5 : ℝ)) := by
            rw [e]; nlinarith [mul_nonneg hT.le (Real.rpow_nonneg hNp.le (12 / 5 : ℝ))]
    have hKT : 0 ≤ K * T ^ ε := by positivity
    calc K * T ^ ε * ((T + (M : ℝ) ^ (6 / 5 : ℝ)) * (M : ℝ) ^ (12 / 5 : ℝ) / (V / 2) ^ 4)
        = K * T ^ ε * (16 * ((T + (M : ℝ) ^ (6 / 5 : ℝ)) * (M : ℝ) ^ (12 / 5 : ℝ)) / V ^ 4) := by
          congr 1; field_simp; ring
      _ ≤ K * T ^ ε * (16 * (32 * ((N : ℝ) ^ (18 / 5 : ℝ) + T * (N : ℝ) ^ (12 / 5 : ℝ))) / V ^ 4) := by
          gcongr
      _ = 512 * K * T ^ ε *
            ((N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by ring
  -- every point of `W` lies in one of the two filters
  have hcover : W ⊆
      (W.filter fun t : ℝ => V / 2 ≤ ‖∑ n ∈ P₁, b n * Complex.exp (Complex.I * t * Real.log n)‖) ∪
      (W.filter fun t : ℝ => V / 2 ≤ ‖∑ n ∈ P₂, b n * Complex.exp (Complex.I * t * Real.log n)‖) := by
    intro t ht
    have hsplit : dyadicPoly N b t = ∑ n ∈ P₁, b n * Complex.exp (Complex.I * t * Real.log n) +
        ∑ n ∈ P₂, b n * Complex.exp (Complex.I * t * Real.log n) := by
      unfold dyadicPoly; rw [hU, sum_union hD]
    have h : V ≤ ‖∑ n ∈ P₁, b n * Complex.exp (Complex.I * t * Real.log n)‖ +
        ‖∑ n ∈ P₂, b n * Complex.exp (Complex.I * t * Real.log n)‖ :=
      (hbig t ht).trans (hsplit ▸ norm_add_le _ _)
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_or_gt (V / 2) ‖∑ n ∈ P₁, b n * Complex.exp (Complex.I * t * Real.log n)‖ with h1 | h1
    · exact Or.inl ⟨ht, h1⟩
    · exact Or.inr ⟨ht, by linarith⟩
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hc' := (Nat.cast_le (α := ℝ)).mpr hc
  rw [Nat.cast_add] at hc'
  have e1 := piece N₁ P₁ hP₁ h1 h2
  have e2 := piece N₂ P₂ hP₂ h3 h4
  linarith

/-! ### Theorem 1.1 -/

/-- `1 + log(T + 1) ≤ (1 + 2^ε/ε) T^ε` for `T ≥ 1`. -/
theorem one_add_log_le_rpow {T ε : ℝ} (hT : 1 ≤ T) (hε : 0 < ε) :
    1 + Real.log (T + 1) ≤ (1 + 2 ^ ε / ε) * T ^ ε := by
  have h1 : Real.log (T + 1) ≤ (T + 1) ^ ε / ε := Real.log_le_rpow_div (by linarith) hε
  have h2 : (T + 1) ^ ε ≤ 2 ^ ε * T ^ ε := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hε.le
  have h3 : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have h4 : (T + 1) ^ ε / ε ≤ 2 ^ ε / ε * T ^ ε := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε]; exact h2
  nlinarith

/-- A case bound `x ≤ k P u` with `k ≤ C`, `P ≥ 1`, `0 ≤ u ≤ S` gives `x ≤ C P S`. -/
theorem le_mul_of_case {x k C P u S : ℝ} (hk : 0 ≤ k) (hkC : k ≤ C) (hP : 1 ≤ P) (hu : 0 ≤ u)
    (huS : u ≤ S) (hx : x ≤ k * P * u) : x ≤ C * P * S :=
  hx.trans (mul_le_mul (mul_le_mul_of_nonneg_right hkC (by linarith)) huS hu
    (mul_nonneg (hk.trans hkC) (by linarith)))

/-- **Guth–Maynard, Theorem 1.1, from Proposition 3.1.**  If Proposition 3.1 holds for a smooth
bump `w` (support `[1,2]`, `w = 1` on `[6/5, 9/5]`), then for every `ε > 0` there is `C` such that
every `1`-separated `W ⊂ [T₀, T₀ + T]` (`T ≥ 2`) with `|Σ_{N<n≤2N} b_n n^{it}| ≥ V > 0` on `W`
and `|b_n| ≤ 1` has `|W| ≤ C T^ε (N²/V² + N^{18/5}/V⁴ + T N^{12/5}/V⁴)`. -/
theorem guthMaynard_largeValues_of_keyProp {w : CGLSmoothBump} (hkey : KeyPropBound w) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T T₀ V : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      1 ≤ N → 2 ≤ T → 0 < V → (∀ n, ‖b n‖ ≤ 1) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
      (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
      (∀ t ∈ W, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((N : ℝ) ^ 2 / V ^ 2 + (N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4
        + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
  obtain ⟨Cm, hCm0, hmid⟩ := card_le_of_keyProp_middle hkey hε
  have hKl : 0 ≤ 1 + 2 ^ ε / ε := by positivity
  refine ⟨1254 + 20064 + 2 * ((18438 : ℝ) ^ 10) ^ 2 + 2110279680 * (1 + 2 ^ ε / ε) + Cm,
    by positivity, ?_⟩
  intro N T T₀ V b W hN hT hV hb hW hsep hbig
  have hbig' : ∀ t ∈ W, V ≤ ‖dyadicPoly N b t‖ := hbig
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hP : 1 ≤ T ^ ε := Real.one_le_rpow (by linarith) hε.le
  -- the three terms
  have hA : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 := by positivity
  have hB : 0 ≤ (N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 := by positivity
  have hC : 0 ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4 := by
    have : 0 ≤ T := by linarith
    positivity
  set S := (N : ℝ) ^ 2 / V ^ 2 + (N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4
    with hS
  have hk1 : (0 : ℝ) ≤ 1254 := by norm_num
  have hk2 : (0 : ℝ) ≤ 20064 := by norm_num
  have hk3 : (0 : ℝ) ≤ 2 * ((18438 : ℝ) ^ 10) ^ 2 := by positivity
  have hk4 : 0 ≤ 2110279680 * (1 + 2 ^ ε / ε) := by positivity
  rcases le_or_gt T N with hTN | hNT
  · -- `T ≤ N`
    refine le_mul_of_case hk1 (by linarith) hP hA (by linarith) ?_
    have h := card_le_of_length_ge hN (by linarith) hV hb hW hsep hbig' hTN
    nlinarith
  rcases le_total (N : ℝ) (18438 ^ 10) with hsmall | hlarge
  · -- small `N`
    refine le_mul_of_case hk3 (by linarith) hP hC (by linarith) ?_
    have h := card_le_of_length_le hN (by linarith) hV hb hW hsep hbig' hsmall
    have : 2 * ((18438 : ℝ) ^ 10) ^ 2 * (T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) ≤
        2 * ((18438 : ℝ) ^ 10) ^ 2 * T ^ ε * (T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
      have := mul_le_mul_of_nonneg_left hP (mul_nonneg hk3 hC)
      nlinarith
    linarith
  have hN6 : 6 ≤ N := by
    have : (6 : ℝ) ≤ N := le_trans (by norm_num) hlarge
    exact_mod_cast this
  rcases lt_or_ge V (4 * (N : ℝ) ^ (7 / 10 : ℝ)) with hlow | hlow
  · -- low level: mean value
    refine le_mul_of_case hk2 (by linarith) hP hC (by linarith) ?_
    have h := card_le_of_level_lt hN (by linarith) hV hb hW hsep hbig' hNT.le hlow
    have := mul_le_mul_of_nonneg_left hP (mul_nonneg hk2 hC)
    nlinarith
  rcases le_or_gt ((N : ℝ) ^ (4 / 5 : ℝ)) V with hhigh | hhigh
  · -- high level: Huxley
    refine le_mul_of_case hk4 (by linarith) hP (add_nonneg hA hC) (by linarith) ?_
    have h := card_le_of_level_ge hN (by linarith) hV hb hW hsep hbig' hlarge hhigh
    have hl := one_add_log_le_rpow (by linarith : (1 : ℝ) ≤ T) hε
    have hAC : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4 := add_nonneg hA hC
    calc (W.card : ℝ) ≤ 2110279680 * (1 + Real.log (T + 1)) *
          ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := h
      _ ≤ 2110279680 * ((1 + 2 ^ ε / ε) * T ^ ε) *
          ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by gcongr
      _ = _ := by ring
  · -- middle range: Proposition 3.1
    refine le_mul_of_case hCm0 (by linarith) hP (add_nonneg hB hC) (by linarith) ?_
    exact hmid N T T₀ V b W hN6 hNT hb hW hsep hlow hhigh.le hbig'

/-- `GuthMaynardLargeValuesBound` (Theorem 1.1) from Proposition 3.1. -/
theorem guthMaynardLargeValuesBound_of_keyProp {w : CGLSmoothBump} (hkey : KeyPropBound w) :
    GuthMaynardLargeValuesBound :=
  fun hε => guthMaynard_largeValues_of_keyProp hkey hε

/-- **Theorem 1.1 for coefficients bounded by `B`**, from Proposition 3.1:
`|W| ≤ C T^ε (B²N²/V² + B⁴N^{18/5}/V⁴ + T B⁴ N^{12/5}/V⁴)`. -/
theorem guthMaynard_largeValues_of_norm_le_of_keyProp {w : CGLSmoothBump} (hkey : KeyPropBound w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T T₀ V B : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      1 ≤ N → 2 ≤ T → 0 < V → 0 < B → (∀ n, ‖b n‖ ≤ B) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
      (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
      (∀ t ∈ W, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
      (W.card : ℝ) ≤ C * T ^ ε * (B ^ 2 * (N : ℝ) ^ 2 / V ^ 2
        + B ^ 4 * (N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 + T * B ^ 4 * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) :=
  GuthMaynardLargeValuesBound.scaled (guthMaynardLargeValuesBound_of_keyProp hkey) hε

end

end RHTower.GuthMaynard
