import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropTwelveOne

/-!
# The explicit form of Guth–Maynard Proposition 12.1

For `σ ∈ [7/10, 39/50]` and `N = T^n`, `n ∈ [5/6, 1)`, the paper chooses the integer `k` of
Proposition 6.1 so that both `k`-dependent terms of (12.1) are at most the target
`T^{(30σ−21)/5} N^{(46−60σ)/5} = T^E`, `E = (30σ−21)/5 + n(46−60σ)/5`.

In exponent form (`exists_nat_explicit_exponent`): with `a = 2(13−15σ)(1−n)/5 > 0` and
`c = −3(10σ−7)(1−n)/5 ≤ 0`, the first term is at most `T^E` iff `k a ≤ E`, the second iff
`4kc ≤ 3E − 2`.  The integer `k = ⌊E/a⌋` works: `E ≥ a`, and the identity
`(3E − 2) a − 4c(E − a) = (2/5)(6n−5)(1−n)(−41 + 123σ − 90σ²)` (`explicit_interval_identity`)
is nonnegative on `[7/10, 39/50]`.  This is the paper's interval-length computation; the upper
end `39/50` is where `−41 + 123σ − 90σ²` stays nonnegative.

`propTwelveOne_explicit_of_fullBound` assembles the explicit form from (12.1) for all `k`, for
`T^{5/6} ≤ N ≤ T^{1−δ}`: there `k ≤ E/a ≤ 3/δ`, so finitely many `k` occur and their constants
combine.  (As `N → T` the chosen `k` is unbounded; the paper's `⪅` with a `k`-dependent constant
covers `N ≤ T^{1−δ}` for each `δ > 0`.)
-/

set_option autoImplicit false

open Finset

namespace RHTower.GuthMaynard

noncomputable section

/-! ### The exponent algebra -/

/-- `(3E − 2)a − 4c(E − a) = (2/5)(6n − 5)(1 − n)(−41 + 123σ − 90σ²)`. -/
theorem explicit_interval_identity (n σ : ℝ) :
    (3 * ((30 * σ - 21) / 5 + n * (46 - 60 * σ) / 5) - 2) * (2 * (13 - 15 * σ) * (1 - n) / 5) -
      4 * (-(3 * (10 * σ - 7) * (1 - n) / 5)) *
        ((30 * σ - 21) / 5 + n * (46 - 60 * σ) / 5 - 2 * (13 - 15 * σ) * (1 - n) / 5) =
      2 / 5 * (6 * n - 5) * (1 - n) * (-41 + 123 * σ - 90 * σ ^ 2) := by
  ring

/-- **The choice of `k`.**  For `n ∈ [5/6, 1)` and `σ ∈ [7/10, 39/50]` there is an integer
`1 ≤ k ≤ E/a` with `(k/(k+1))(1 + n(4−6σ)) ≤ E` and `n(5−6σ)·4k/(4k+3) + 2/(4k+3) ≤ E`. -/
theorem exists_nat_explicit_exponent {n σ : ℝ} (hn : 5 / 6 ≤ n) (hn1 : n < 1)
    (hσ : 7 / 10 ≤ σ) (hσ' : σ ≤ 39 / 50) :
    ∃ k : ℕ, 1 ≤ k ∧
      (k : ℝ) ≤ ((30 * σ - 21) / 5 + n * (46 - 60 * σ) / 5) / (2 * (13 - 15 * σ) * (1 - n) / 5) ∧
      (k : ℝ) / (k + 1) * (1 + n * (4 - 6 * σ)) ≤ (30 * σ - 21) / 5 + n * (46 - 60 * σ) / 5 ∧
      n * (5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3)) + 2 / (4 * (k : ℝ) + 3) ≤
        (30 * σ - 21) / 5 + n * (46 - 60 * σ) / 5 := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (30 * σ - 21) / 5 + n * (46 - 60 * σ) / 5 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * (13 - 15 * σ) * (1 - n) / 5 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -(3 * (10 * σ - 7) * (1 - n) / 5) := ⟨_, rfl⟩
  rw [← hE, ← ha]
  have ha0 : 0 < a := by rw [ha]; apply div_pos _ (by norm_num); apply mul_pos <;> nlinarith
  have hc0 : c ≤ 0 := by
    rw [hc, neg_nonpos]; apply div_nonneg _ (by norm_num); apply mul_nonneg <;> nlinarith
  have hEa : a ≤ E := by
    rw [hE, ha]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 39 / 50 - σ) (by linarith : (0 : ℝ) ≤ 90 * n - 60)]
  have hQ : 0 ≤ -41 + 123 * σ - 90 * σ ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ σ - 7 / 10) (by linarith : (0 : ℝ) ≤ 39 / 50 - σ)]
  have hid := explicit_interval_identity n σ
  rw [← hE, ← ha, ← hc] at hid
  have hpos : 0 ≤ (3 * E - 2) * a - 4 * c * (E - a) := by
    rw [hid]
    apply mul_nonneg _ hQ
    apply mul_nonneg _ (by linarith)
    apply mul_nonneg (by norm_num) (by linarith)
  have hU1 : 1 ≤ E / a := by rw [le_div_iff₀ ha0]; linarith
  refine ⟨⌊E / a⌋₊, Nat.one_le_floor_iff _ |>.mpr hU1, Nat.floor_le (by linarith), ?_, ?_⟩
  · -- `k a ≤ E`
    have hk := Nat.floor_le (by linarith : (0 : ℝ) ≤ E / a)
    have hka : (⌊E / a⌋₊ : ℝ) * a ≤ E := by rwa [le_div_iff₀ ha0] at hk
    have hk0 : (0 : ℝ) < ⌊E / a⌋₊ + 1 := by positivity
    have hrel : 1 + n * (4 - 6 * σ) = E + a := by rw [hE, ha]; ring
    rw [hrel, div_mul_eq_mul_div, div_le_iff₀ hk0]
    nlinarith
  · -- `4 k c ≤ 3E − 2`
    have hk := Nat.lt_floor_add_one (E / a)
    obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = (⌊E / a⌋₊ : ℝ) := ⟨_, rfl⟩
    rw [← hkdef] at hk ⊢
    have hk0 : 0 ≤ k := hkdef ▸ Nat.cast_nonneg _
    have hU : E / a - 1 ≤ k := by linarith
    have hrel : n * (5 - 6 * σ) = E + c := by rw [hE, hc]; ring
    have hD : (0 : ℝ) < 4 * k + 3 := by linarith
    rw [hrel, mul_div_assoc', ← add_div, div_le_iff₀ hD]
    -- `4kc ≤ 4(E/a − 1)c ≤ 3E − 2`
    have h1 : 4 * k * c ≤ 4 * (E / a - 1) * c := by nlinarith
    have h2 : 4 * (E / a - 1) * c ≤ 3 * E - 2 := by
      have e : 4 * (E / a - 1) * c = 4 * c * (E - a) / a := by field_simp
      rw [e, div_le_iff₀ ha0]
      linarith
    nlinarith

/-! ### From exponents to powers -/

/-- `T^a N^b ≤ T^E` when `N = T^n`, `T ≥ 1` and `a + n b ≤ E`. -/
theorem rpow_mul_rpow_le_of_logb {T N n a b E : ℝ} (hT : 1 ≤ T) (hN : N = T ^ n)
    (h : a + n * b ≤ E) : T ^ a * N ^ b ≤ T ^ E := by
  have hT0 : 0 < T := by linarith
  rw [hN, ← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]
  exact Real.rpow_le_rpow_of_exponent_le hT h

/-- **The `k`-terms against the explicit target.**  For `T > 1`, `T^{5/6} ≤ N ≤ T^{1−δ}` and
`σ ∈ [7/10, 39/50]` there is `1 ≤ k ≤ 3/δ` with
`T^{k/(k+1)}N^{(4−6σ)k/(k+1)} + N^{(5−6σ)4k/(4k+3)}T^{2/(4k+3)} ≤ 2 T^{(30σ−21)/5}N^{(46−60σ)/5}`. -/
theorem exists_nat_kTerms_le_explicit {N T σ δ : ℝ} (hT : 1 < T) (hδ : 0 < δ)
    (hN : T ^ (5 / 6 : ℝ) ≤ N) (hN' : N ≤ T ^ (1 - δ)) (hσ : 7 / 10 ≤ σ) (hσ' : σ ≤ 39 / 50) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 3 / δ ∧
      T ^ ((k : ℝ) / (k + 1)) * N ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
        N ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)) ≤
      2 * (T ^ ((30 * σ - 21) / 5) * N ^ ((46 - 60 * σ) / 5)) := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := lt_of_lt_of_le (Real.rpow_pos_of_pos hT0 _) hN
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = Real.logb T N := ⟨_, rfl⟩
  have hNn : N = T ^ n := by rw [hn, Real.rpow_logb hT0 hT.ne' hN0]
  have hn56 : 5 / 6 ≤ n := by
    rw [hNn] at hN; exact (Real.rpow_le_rpow_left_iff hT).mp hN
  have hn1 : n ≤ 1 - δ := by
    rw [hNn] at hN'; exact (Real.rpow_le_rpow_left_iff hT).mp hN'
  obtain ⟨k, hk1, hkU, hk3, hk4⟩ :=
    exists_nat_explicit_exponent hn56 (by linarith) hσ hσ'
  refine ⟨k, hk1, ?_, ?_⟩
  · -- `E/a ≤ 3/δ`
    refine hkU.trans ?_
    have hE : (30 * σ - 21) / 5 + n * (46 - 60 * σ) / 5 ≤ 32 / 25 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - n) (by linarith : (0 : ℝ) ≤ σ - 7 / 10)]
    have ha : 13 / 25 * δ ≤ 2 * (13 - 15 * σ) * (1 - n) / 5 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 39 / 50 - σ) (by linarith : (0 : ℝ) ≤ 1 - n)]
    have ha0 : 0 < 13 / 25 * δ := by positivity
    rw [div_le_div_iff₀ (by linarith) hδ]
    nlinarith
  · have htarget : T ^ ((30 * σ - 21) / 5) * N ^ ((46 - 60 * σ) / 5) =
        T ^ ((30 * σ - 21) / 5 + n * (46 - 60 * σ) / 5) := by
      rw [hNn, ← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]; congr 1; ring
    rw [htarget]
    have h3 := rpow_mul_rpow_le_of_logb hT.le hNn (a := (k : ℝ) / (k + 1))
      (b := (4 - 6 * σ) * ((k : ℝ) / (k + 1))) (E := (30 * σ - 21) / 5 + n * (46 - 60 * σ) / 5)
      (by nlinarith)
    have h4 := rpow_mul_rpow_le_of_logb hT.le hNn (a := 2 / (4 * (k : ℝ) + 3))
      (b := (5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3)))
      (E := (30 * σ - 21) / 5 + n * (46 - 60 * σ) / 5) (by nlinarith)
    rw [mul_comm (N ^ _)]
    linarith

/-! ### The explicit form -/

/-- **Guth–Maynard, Proposition 12.1, explicit form**, for `σ ∈ [7/10, 39/50]` and
`T^{5/6} ≤ N ≤ T^{1−δ}`, from (12.1) for every `k ≥ 1`:
`|W| ≤ C T^ε (N^{2−2σ} + T^{1/2}N^{3−4σ} + T^{(30σ−21)/5}N^{(46−60σ)/5})`. -/
theorem propTwelveOne_explicit_of_fullBound {w : CGLSmoothBump}
    (hFB : ∀ k : ℕ, 1 ≤ k → FullBoundStatement w k k) {δ : ℝ} (hδ : 0 < δ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T T₀ σ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → T ^ (5 / 6 : ℝ) ≤ N → (N : ℝ) ≤ T ^ (1 - δ) → 7 / 10 ≤ σ → σ ≤ 39 / 50 →
      (∀ n, ‖b n‖ ≤ 1) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
      (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5)) := by
  have hall := fun i : ℕ => propTwelveOne_of_fullBound (hFB (i + 1) (by omega)) hε
  choose Cf hCf0 hCf using hall
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌊3 / δ⌋₊ := ⟨_, rfl⟩
  refine ⟨2 * ∑ i ∈ range (K + 1), Cf i, by
    have := Finset.sum_nonneg fun i (_ : i ∈ range (K + 1)) => hCf0 i; positivity, ?_⟩
  intro N T T₀ σ b W hT hTN hNT hσ hσ' hb hW hsep hbig
  have hT1 : 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hNT' : (N : ℝ) ≤ T := hNT.trans
    (Real.rpow_le_rpow_of_exponent_le hT1.le (by linarith) |>.trans_eq (Real.rpow_one T))
  obtain ⟨k, hk1, hk3, hkle⟩ := exists_nat_kTerms_le_explicit hT1 hδ hTN hNT hσ hσ'
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  have hiK : i ∈ range (K + 1) := by
    rw [Finset.mem_range, hK]
    have : (i : ℝ) + 1 ≤ 3 / δ := by exact_mod_cast hk3
    have := Nat.le_floor (show ((i + 1 : ℕ) : ℝ) ≤ 3 / δ by exact_mod_cast hk3)
    omega
  have hbound := hCf i N T T₀ σ b W hT hTN hNT' hσ hb hW hsep hbig
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_rpow hT1.le (by norm_num)).trans hTN
  have hN0 : (0 : ℝ) < N := by linarith
  have hCi : Cf i ≤ ∑ j ∈ range (K + 1), Cf j :=
    Finset.single_le_sum (f := Cf) (fun j _ => hCf0 j) hiK
  have hTε : 0 ≤ T ^ ε := by positivity
  have ht1 : 0 ≤ (N : ℝ) ^ (2 - 2 * σ) := by positivity
  have ht6 : 0 ≤ T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) := by positivity
  have htg : 0 ≤ T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5) := by positivity
  push_cast at hbound hkle
  refine hbound.trans ?_
  calc Cf i * T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T ^ (((i : ℝ) + 1) / ((i : ℝ) + 1 + 1)) *
          (N : ℝ) ^ ((4 - 6 * σ) * (((i : ℝ) + 1) / ((i : ℝ) + 1 + 1))) +
        (N : ℝ) ^ ((5 - 6 * σ) * (4 * ((i : ℝ) + 1) / (4 * ((i : ℝ) + 1) + 3))) *
          T ^ (2 / (4 * ((i : ℝ) + 1) + 3)))
      ≤ Cf i * T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
          2 * (T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5))) := by
        have := mul_nonneg (hCf0 i) hTε
        nlinarith
    _ ≤ 2 * (∑ j ∈ range (K + 1), Cf j) * T ^ ε *
          ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
            T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5)) := by
        have hs : 0 ≤ ∑ j ∈ range (K + 1), Cf j :=
          Finset.sum_nonneg fun j _ => hCf0 j
        have hA : (N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
            2 * (T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5)) ≤
            2 * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
              T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5)) := by linarith
        calc Cf i * T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
              2 * (T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5)))
            ≤ (∑ j ∈ range (K + 1), Cf j) * T ^ ε *
                (2 * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
                  T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5))) := by
              gcongr
          _ = _ := by ring

/-- **Proposition 12.1, explicit form, from Propositions 6.1 (all `k`) and 11.2.** -/
theorem propTwelveOne_explicit_of_S_bounds (w : CGLUnitRealSmoothBump)
    (hS2 : ∀ k : ℕ, 1 ≤ k → PropSixOneBound w.toCGLRealSmoothBump k k)
    (hS3 : PropElevenTwoBound w.toCGLRealSmoothBump) {δ : ℝ} (hδ : 0 < δ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T T₀ σ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → T ^ (5 / 6 : ℝ) ≤ N → (N : ℝ) ≤ T ^ (1 - δ) → 7 / 10 ≤ σ → σ ≤ 39 / 50 →
      (∀ n, ‖b n‖ ≤ 1) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
      (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5)) :=
  propTwelveOne_explicit_of_fullBound
    (fun k hk => fullBoundStatement_of_S_bounds w hk hk (hS2 k hk) hS3) hδ hε

end

end RHTower.GuthMaynard
