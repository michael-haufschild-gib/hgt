import GaloisForLFunctions.SignedSuccessorArithmetic.TheFloorIsAttainedAtConductorThree

/-!
# The two-scale deficit is quantized

The signed two-scale identity `C(2N+1) − σ(1) + C(N) = 4E_N − N` says that the **two-scale
deficit** `D_N = C(2N+1) − σ(1) + C(N) + N` is four times a count. It is therefore quantized:
`D_N < 4` forces `D_N = 0` and the absence of doubled agreements up to `N`
(`twoScaleDeficit_lt_four_iff`). This is the quantization principle in its simplest form: a signed
correlation pinned to an integer lattice does not need to be estimated below the first quantum.

A completely multiplicative sign has **zero doubling defect** when no `n` has
`f(n) = f(n+1)` and `f(2n) = f(2n+1)`. Zero defect is equivalent to equality in the signed
two-scale floor at every scale (`zeroDefect_iff`), it holds for the conductor-three twins, and it
forces the logarithmic agreement density to be exactly `1/3`
(`logAgree_le_of_zeroDefect`): zero-defect signs are extremal for the one-third floor.

The zero-defect signs with `f(2) = 1` are not twins of `χ₃`: the defect condition at the first
steps forces `f(3) = f(5) = f(7) = −1` and `f(11) = f(13) = 1`
(`zeroDefect_of_two_eq_one`), a pattern no character of conductor `3` has.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Finset

/-- The two-scale deficit `D_N = C(2N+1) − σ(1) + C(N) + N`. -/
def twoScaleDeficit (f : ℕ → ℤˣ) (N : ℕ) : ℤ :=
  succCorr f (2 * N + 1) - ((succSign f 1 : ℤˣ) : ℤ) + succCorr f N + N

theorem twoScaleDeficit_eq (f : CMSign) (N : ℕ) :
    twoScaleDeficit f N = 4 * (doubleAgreeCount f N : ℤ) := by
  have := signed_two_scale_identity f N
  rw [twoScaleDeficit]; linarith

/-- **Quantization.** The deficit is a nonnegative multiple of `4`; below `4` it vanishes, and
then no doubled agreement occurs up to `N`. -/
theorem twoScaleDeficit_lt_four_iff (f : CMSign) (N : ℕ) :
    twoScaleDeficit f N < 4 ↔ doubleAgreeCount f N = 0 := by
  rw [twoScaleDeficit_eq]
  constructor
  · intro h
    have : (doubleAgreeCount f N : ℤ) < 1 := by linarith
    omega
  · intro h; rw [h]; norm_num

/-- Zero doubling defect. -/
def ZeroDefect (f : ℕ → ℤˣ) : Prop := ∀ n, 0 < n → agree f n * agree f (2 * n) = 0

theorem doubleAgreeCount_eq_zero_iff (f : ℕ → ℤˣ) :
    (∀ N, doubleAgreeCount f N = 0) ↔ ZeroDefect f := by
  constructor
  · intro h n hn
    have h1 := h n
    rw [doubleAgreeCount, sum_eq_zero_iff] at h1
    exact h1 n (by simp; omega)
  · intro h N
    exact sum_eq_zero fun n hn => h n (by simp at hn; omega)

/-- **Zero defect is equality in the signed floor at every scale.** -/
theorem zeroDefect_iff (f : CMSign) :
    ZeroDefect f ↔ ∀ N, succCorr f (2 * N + 1) - ((succSign f 1 : ℤˣ) : ℤ) + succCorr f N = -N := by
  rw [← doubleAgreeCount_eq_zero_iff]
  refine forall_congr' fun N => ?_
  have := signed_two_scale_identity f N
  constructor
  · intro h; rw [h] at this; push_cast at this; linarith
  · intro h
    have : (4 : ℤ) * doubleAgreeCount f N = 0 := by linarith
    exact_mod_cast (mul_eq_zero.mp this).resolve_left (by norm_num)

theorem zeroDefect_chi3Twin (ε : ℤˣ) : ZeroDefect (chi3Twin ε) :=
  fun _ hn => agree_mul_agree_two_mul_chi3Twin ε hn

/-- **Zero defect forces the floor density.** A zero-defect sign has logarithmic agreement mass at
most `(1/3) log M + 2`. -/
theorem logAgree_le_of_zeroDefect (f : CMSign) (hf : ZeroDefect f) {M : ℕ} (hM : 0 < M) :
    logAgree f M ≤ Real.log M / 3 + 2 := by
  -- the per-step identity with zero defect: `a(2n) + a(2n+1) = 1 − a(n)`
  have hstep : ∀ n, 0 < n → (agree f (2 * n) : ℝ) + agree f (2 * n + 1) = 1 - agree f n := by
    intro n hn
    have h := agree_doubling f hn
    rw [hf n hn, mul_zero, add_zero] at h
    have : ((agree f (2 * n) + agree f (2 * n + 1) + agree f n : ℕ) : ℝ) = (1 : ℕ) := by rw [h]
    push_cast at this; linarith
  -- `L(2N+1) ≤ 1 + (H_N − L(N))/2`
  have hpair : ∀ N, logAgree f (2 * N + 1) ≤ 1 + ((harmonic N : ℝ) - logAgree f N) / 2 := by
    intro N
    rw [logAgree, sum_Icc_two_mul_add_one (fun k => (agree f k : ℝ) / k)]
    have ha1 : (agree f 1 : ℝ) ≤ 1 := by exact_mod_cast agree_le_one f 1
    have hle : ∑ n ∈ Icc 1 N, ((agree f (2 * n) : ℝ) / ((2 * n : ℕ) : ℝ) +
        (agree f (2 * n + 1) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) ≤
        ∑ n ∈ Icc 1 N, (1 - (agree f n : ℝ)) / (2 * n) := by
      refine sum_le_sum fun n hn => ?_
      have hn1 : 0 < n := by simp at hn; omega
      have hb : (0 : ℝ) ≤ agree f (2 * n + 1) := Nat.cast_nonneg _
      push_cast
      have : (agree f (2 * n + 1) : ℝ) / (2 * n + 1) ≤ (agree f (2 * n + 1) : ℝ) / (2 * n) :=
        div_le_div_of_nonneg_left hb (by positivity) (by linarith)
      rw [← hstep n hn1, add_div]
      linarith
    have heq : ∑ n ∈ Icc 1 N, (1 - (agree f n : ℝ)) / (2 * n) =
        ((harmonic N : ℝ) - logAgree f N) / 2 := by
      rw [harmonic_eq_sum, logAgree, ← sum_sub_distrib, sum_div]
      exact sum_congr rfl fun n _ => by ring
    simp only [Nat.cast_one, div_one]
    linarith
  -- `L(N) ≥ L(2N+1) − 1`
  have hinc : ∀ N, logAgree f (2 * N + 1) - 1 ≤ logAgree f N := by
    intro N
    have key : ∀ k : ℕ, logAgree f (N + k) ≤ logAgree f N + k / (N + 1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [← add_assoc, logAgree, sum_Icc_succ_top (by omega), ← logAgree]
        have ha : (agree f (N + k + 1) : ℝ) ≤ 1 := by exact_mod_cast agree_le_one f _
        have h1 : (agree f (N + k + 1) : ℝ) / ((N + k + 1 : ℕ) : ℝ) ≤ 1 / ((N : ℝ) + 1) := by
          calc (agree f (N + k + 1) : ℝ) / ((N + k + 1 : ℕ) : ℝ) ≤ 1 / ((N + k + 1 : ℕ) : ℝ) :=
                div_le_div_of_nonneg_right ha (Nat.cast_nonneg _)
            _ ≤ 1 / ((N : ℝ) + 1) := div_le_div_of_nonneg_left zero_le_one (by positivity)
                (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])
        push_cast at ih h1 ⊢
        have : ((k : ℝ) + 1) / ((N : ℝ) + 1) = k / (N + 1) + 1 / (N + 1) := by ring
        linarith
    have := key (N + 1)
    rw [show N + (N + 1) = 2 * N + 1 by ring] at this
    have hk : ((N + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) = 1 := by push_cast; field_simp
    rw [hk] at this
    linarith
  obtain ⟨N, hN⟩ : ∃ N, M = 2 * N + 1 ∨ M = 2 * N + 2 := ⟨(M - 1) / 2, by omega⟩
  have h1 := hpair N
  have h2 := hinc N
  have hH : (harmonic N : ℝ) ≤ 1 + Real.log M := by
    rcases Nat.eq_zero_or_pos N with h0 | hN0
    · rw [h0]; simp only [harmonic_zero, Rat.cast_zero]
      have : (0 : ℝ) ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
      linarith
    · have := harmonic_le_one_add_log N
      have : Real.log N ≤ Real.log M :=
        Real.log_le_log (by exact_mod_cast hN0) (by exact_mod_cast (show N ≤ M by omega))
      linarith
  have hbase : logAgree f (2 * N + 1) ≤ Real.log M / 3 + 4 / 3 := by linarith
  rcases hN with rfl | rfl
  · linarith
  · have : logAgree f (2 * N + 2) ≤ logAgree f (2 * N + 1) + 1 / 2 := by
      rw [show 2 * N + 2 = 2 * N + 1 + 1 by ring, logAgree, sum_Icc_succ_top (by omega), ← logAgree]
      have ha : (agree f (2 * N + 1 + 1) : ℝ) ≤ 1 := by exact_mod_cast agree_le_one f _
      have : (agree f (2 * N + 1 + 1) : ℝ) / ((2 * N + 1 + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        push_cast; linarith [Nat.cast_nonneg (α := ℝ) N]
      linarith
    linarith

/-- **The `f(2) = 1` branch of zero defect.** Zero defect with `f(2) = 1` forces
`f(3) = f(5) = f(7) = −1` and `f(11) = f(13) = 1`. -/
theorem zeroDefect_of_two_eq_one (f : CMSign) (hf : ZeroDefect f) (h2 : f 2 = 1) :
    f 3 = -1 ∧ f 5 = -1 ∧ f 7 = -1 ∧ f 11 = 1 ∧ f 13 = 1 := by
  -- `σ(n) = 1 ⇒ σ(2n) = σ(2n+1) = −1`
  have hz : ∀ n, 0 < n → succSign f n = 1 →
      succSign f (2 * n) = -1 ∧ succSign f (2 * n + 1) = -1 := by
    intro n hn hσ
    have h := hf n hn
    have hne : succSign f (2 * n) ≠ 1 := by
      intro h'; simp [agree, hσ, h'] at h
    have h2n : succSign f (2 * n) = -1 := (Int.units_eq_one_or _).resolve_left hne
    refine ⟨h2n, ?_⟩
    have hc := succSign_two_mul_mul f hn
    rw [h2n, hσ] at hc
    rcases Int.units_eq_one_or (succSign f (2 * n + 1)) with h'' | h''
    · rw [h''] at hc; simp at hc
    · exact h''
  have m : ∀ a b : ℕ, 0 < a → 0 < b → f (a * b) = f a * f b := fun a b ha hb => f.map_mul ha hb
  have f1 : f 1 = 1 := f.map_one
  have f4 : f 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, m 2 2 (by norm_num) (by norm_num), h2,
    mul_one]
  have f8 : f 8 = 1 := by rw [show (8 : ℕ) = 2 * 4 from rfl, m 2 4 (by norm_num) (by norm_num), h2,
    f4, mul_one]
  have f16 : f 16 = 1 := by rw [show (16 : ℕ) = 2 * 8 from rfl, m 2 8 (by norm_num) (by norm_num),
    h2, f8, mul_one]
  -- `σ(1) = 1`, so `σ(2) = −1`: `f(3) = −1`
  have s1 : succSign f 1 = 1 := by simp [succSign, f1, h2]
  have f3 : f 3 = -1 := by
    have := (hz 1 one_pos s1).1
    simp only [succSign, mul_one, h2, one_mul] at this
    exact this
  have f6 : f 6 = -1 := by rw [show (6 : ℕ) = 2 * 3 from rfl, m 2 3 (by norm_num) (by norm_num), h2,
    f3, one_mul]
  have f9 : f 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, m 3 3 (by norm_num) (by norm_num), f3]; simp
  -- `f(5) = 1` would give `σ(4) = 1`, hence `σ(8) = −1`, but `f(8) = f(9) = 1`
  have f5 : f 5 = -1 := by
    rcases Int.units_eq_one_or (f 5) with h5 | h5
    · exfalso
      have s4 : succSign f 4 = 1 := by simp [succSign, f4, h5]
      have := (hz 4 (by norm_num) s4).1
      simp [succSign, f8, f9] at this
    · exact h5
  have f10 : f 10 = -1 := by rw [show (10 : ℕ) = 2 * 5 from rfl, m 2 5 (by norm_num) (by norm_num),
    h2, f5, one_mul]
  have f15 : f 15 = 1 := by
    rw [show (15 : ℕ) = 3 * 5 from rfl, m 3 5 (by norm_num) (by norm_num), f3, f5]
    simp
  -- `f(7) = 1` would give `σ(7) = 1`, hence `σ(14) = −1`, but `f(14) = f(15) = 1`
  have f7 : f 7 = -1 := by
    rcases Int.units_eq_one_or (f 7) with h7 | h7
    · exfalso
      have s7 : succSign f 7 = 1 := by simp [succSign, h7, f8]
      have f14 : f 14 = 1 := by rw [show (14 : ℕ) = 2 * 7 from rfl,
        m 2 7 (by norm_num) (by norm_num), h2, h7, one_mul]
      have := (hz 7 (by norm_num) s7).1
      simp [succSign, f14, f15] at this
    · exact h7
  -- `σ(5) = f(5) f(6) = 1`, so `σ(10) = −1`: `f(11) = 1`
  have s5 : succSign f 5 = 1 := by simp [succSign, f5, f6]
  have f11 : f 11 = 1 := by
    have := (hz 5 (by norm_num) s5).1
    simp only [succSign, show 2 * 5 = 10 from rfl, show 10 + 1 = 11 from rfl, f10] at this
    rcases Int.units_eq_one_or (f 11) with h | h
    · exact h
    · rw [h] at this; simp at this
  -- `σ(6) = f(6) f(7) = 1`, so `σ(12) = −1`: `f(13) = 1`
  have s6 : succSign f 6 = 1 := by simp [succSign, f6, f7]
  have f12 : f 12 = -1 := by rw [show (12 : ℕ) = 4 * 3 from rfl, m 4 3 (by norm_num) (by norm_num),
    f4, f3, one_mul]
  have f13 : f 13 = 1 := by
    have := (hz 6 (by norm_num) s6).1
    simp only [succSign, show 2 * 6 = 12 from rfl, show 12 + 1 = 13 from rfl, f12] at this
    rcases Int.units_eq_one_or (f 13) with h | h
    · exact h
    · rw [h] at this; simp at this
  exact ⟨f3, f5, f7, f11, f13⟩

end GaloisForLFunctions.SignedSuccessorArithmetic
