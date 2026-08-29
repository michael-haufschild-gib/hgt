import GaloisForLFunctions.RHTower.Sieve.KubalalikaRSum
import GaloisForLFunctions.RHTower.Sieve.ParityGeneralSet

/-!
# The large-scale regime of the Kubalalika localization

Every scalar hypothesis of the mixed hybrid block estimate at the parameters `U ≍ T^{1/2}`,
`V ≍ T^{1/8}` follows from three explicit inequalities in `T`: an absolute threshold, and two
statements that a power of `1 + log T` is below a power of `T`.  All three hold eventually.
-/

namespace RHTower.Sieve

open Filter Finset RHTower

noncomputable section

/-- A fixed multiple of a fixed power of `1 + log x` is eventually below every positive power. -/
theorem eventually_const_mul_one_add_log_pow_le_rpow {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (k : ℕ) : ∀ᶠ x : ℝ in atTop, c * (1 + Real.log x) ^ k ≤ x ^ δ := by
  have hbase : (0 : ℝ) < c * 2 ^ k := by positivity
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hδ).bound
    (c := 1 / (c * 2 ^ k)) (by positivity)
  filter_upwards [h, eventually_ge_atTop (Real.exp 1)] with x hx hx1
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hx1
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hx1
    rwa [Real.log_exp] at this
  have hlog0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hx
  have hcast : Real.log x ^ (k : ℝ) = Real.log x ^ k := Real.rpow_natCast _ k
  rw [hcast] at hx
  have hstep : (1 + Real.log x) ^ k ≤ 2 ^ k * Real.log x ^ k := by
    have h1 : 1 + Real.log x ≤ 2 * Real.log x := by linarith
    calc (1 + Real.log x) ^ k ≤ (2 * Real.log x) ^ k :=
          pow_le_pow_left₀ (by linarith) h1 k
      _ = 2 ^ k * Real.log x ^ k := by rw [mul_pow]
  calc c * (1 + Real.log x) ^ k ≤ c * (2 ^ k * Real.log x ^ k) :=
        mul_le_mul_of_nonneg_left hstep hc.le
    _ = (c * 2 ^ k) * Real.log x ^ k := by ring
    _ ≤ (c * 2 ^ k) * (1 / (c * 2 ^ k) * x ^ δ) :=
        mul_le_mul_of_nonneg_left hx hbase.le
    _ = x ^ δ := by field_simp

/-- The large-scale regime: an absolute threshold and two subpower comparisons. -/
def KubalalikaLarge (T : ℝ) : Prop :=
  (10 : ℝ) ^ 112 ≤ T ∧ 32 * (1 + Real.log T) ^ 2 ≤ T ^ (1 / 4 : ℝ)
    ∧ 100 * (1 + Real.log T) ^ 8 ≤ T ^ (3 / 8 : ℝ)

theorem eventually_kubalalikaLarge : ∀ᶠ T : ℝ in atTop, KubalalikaLarge T := by
  filter_upwards [eventually_ge_atTop ((10 : ℝ) ^ 112),
    eventually_const_mul_one_add_log_pow_le_rpow (δ := 1 / 4) (c := 32)
      (by norm_num) (by norm_num) 2,
    eventually_const_mul_one_add_log_pow_le_rpow (δ := 3 / 8) (c := 100)
      (by norm_num) (by norm_num) 8] with T h1 h2 h3
  exact ⟨h1, h2, h3⟩

variable {T : ℝ}

theorem KubalalikaLarge.one_le (h : KubalalikaLarge T) : (1 : ℝ) ≤ T := by
  have h1 := h.1
  have : (1 : ℝ) ≤ (10 : ℝ) ^ 112 := one_le_pow₀ (by norm_num)
  linarith

theorem KubalalikaLarge.pos (h : KubalalikaLarge T) : (0 : ℝ) < T :=
  lt_of_lt_of_le zero_lt_one h.one_le

theorem KubalalikaLarge.log_nonneg (h : KubalalikaLarge T) : (0 : ℝ) ≤ Real.log T :=
  Real.log_nonneg h.one_le

/-- The localization width is the reciprocal fourth root. -/
theorem kubalalikaEps_eq_rpow (hT : 0 ≤ T) : kubalalikaEps T = T ^ (-(1 / 4) : ℝ) := by
  rcases eq_or_lt_of_le hT with h | h
  · rw [kubalalikaEps, ← h]
    simp
  · rw [kubalalikaEps, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul h.le,
      Real.rpow_neg h.le]
    norm_num

theorem KubalalikaLarge.eps_le_one (h : KubalalikaLarge T) : kubalalikaEps T ≤ 1 := by
  rw [kubalalikaEps_eq_rpow h.pos.le]
  rw [Real.rpow_neg h.pos.le]
  refine inv_le_one_of_one_le₀ ?_
  exact Real.one_le_rpow h.one_le (by norm_num)

theorem KubalalikaLarge.eps_pos (h : KubalalikaLarge T) : 0 < kubalalikaEps T := by
  rw [kubalalikaEps_eq_rpow h.pos.le]
  exact Real.rpow_pos_of_pos h.pos _

theorem sqrt_sqrt_eq_rpow (hT : 0 ≤ T) : Real.sqrt (Real.sqrt T) = T ^ (1 / 4 : ℝ) := by
  rcases eq_or_lt_of_le hT with h | h
  · rw [← h]
    simp
  · rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul h.le]
    norm_num

theorem KubalalikaLarge.one_le_log (h : KubalalikaLarge T) : (1 : ℝ) ≤ Real.log T := by
  have he : Real.exp 1 ≤ T := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : (2.7182818286 : ℝ) ≤ (10 : ℝ) ^ 112 := by
      have : (1 : ℝ) ≤ (10 : ℝ) ^ 111 := one_le_pow₀ (by norm_num)
      nlinarith only [this]
    linarith [h.1]
  have := Real.log_le_log (Real.exp_pos 1) he
  rwa [Real.log_exp] at this

theorem KubalalikaLarge.rpow_le_rpow_exp (h : KubalalikaLarge T) {a b : ℝ} (hab : a ≤ b) :
    T ^ a ≤ T ^ b := Real.rpow_le_rpow_of_exponent_le h.one_le hab

/-- The upper end of the localization window. -/
theorem KubalalikaLarge.mHi_le (h : KubalalikaLarge T) :
    ((⌊T * (1 + kubalalikaEps T)⌋₊ : ℕ) : ℝ) ≤ 2 * T := by
  have h1 : ((⌊T * (1 + kubalalikaEps T)⌋₊ : ℕ) : ℝ) ≤ T * (1 + kubalalikaEps T) := by
    refine Nat.floor_le ?_
    have h0 := h.eps_pos
    have hp := h.pos
    positivity
  have h2 : T * (1 + kubalalikaEps T) ≤ 2 * T := by
    have := h.eps_le_one
    nlinarith only [this, h.pos]
  linarith

theorem KubalalikaLarge.one_le_mHi (h : KubalalikaLarge T) :
    1 ≤ ⌊T * (1 + kubalalikaEps T)⌋₊ := by
  refine Nat.le_floor ?_
  have := h.eps_pos
  have := h.one_le
  push_cast
  nlinarith only [h.eps_pos, h.one_le]

/-- The lower end of the localization window. -/
theorem KubalalikaLarge.mLo_ge (h : KubalalikaLarge T) :
    T / (2 * (1 + Real.log T) ^ 2)
      ≤ ((⌈T / ((1 + kubalalikaEps T) * (Real.log T) ^ 2)⌉₊ : ℕ) : ℝ) := by
  have hlog := h.one_le_log
  have hden : (0 : ℝ) < (1 + kubalalikaEps T) * (Real.log T) ^ 2 := by
    have := h.eps_pos
    positivity
  have hcmp : (1 + kubalalikaEps T) * (Real.log T) ^ 2 ≤ 2 * (1 + Real.log T) ^ 2 := by
    have h1 := h.eps_le_one
    nlinarith only [h1, hlog]
  have hstep : T / (2 * (1 + Real.log T) ^ 2)
      ≤ T / ((1 + kubalalikaEps T) * (Real.log T) ^ 2) :=
    div_le_div_of_nonneg_left h.pos.le hden hcmp
  exact le_trans hstep (Nat.le_ceil _)

theorem KubalalikaLarge.one_le_mLo (h : KubalalikaLarge T) :
    1 ≤ ⌈T / ((1 + kubalalikaEps T) * (Real.log T) ^ 2)⌉₊ := by
  have hlog := h.one_le_log
  have hpos : (0 : ℝ) < T / ((1 + kubalalikaEps T) * (Real.log T) ^ 2) := by
    have := h.eps_pos
    have := h.pos
    positivity
  exact Nat.one_le_iff_ne_zero.2 (fun hc => absurd (Nat.ceil_eq_zero.1 hc) (not_le.2 hpos))

/-- The lower end of the shift range. -/
theorem KubalalikaLarge.rLo_ge (h : KubalalikaLarge T) :
    T ^ (1 / 4 : ℝ) ≤ ((⌈Real.sqrt (Real.sqrt T)⌉₊ : ℕ) : ℝ) := by
  rw [← sqrt_sqrt_eq_rpow h.pos.le]
  exact Nat.le_ceil _

theorem KubalalikaLarge.one_le_rLo (h : KubalalikaLarge T) :
    1 ≤ ⌈Real.sqrt (Real.sqrt T)⌉₊ := by
  have h1 : (1 : ℝ) ≤ T ^ (1 / 4 : ℝ) := Real.one_le_rpow h.one_le (by norm_num)
  have h2 := h.rLo_ge
  have : (1 : ℝ) ≤ ((⌈Real.sqrt (Real.sqrt T)⌉₊ : ℕ) : ℝ) := le_trans h1 h2
  exact_mod_cast this

/-- The upper end of the shift range. -/
theorem KubalalikaLarge.rHi_le (h : KubalalikaLarge T) {mHi : ℕ}
    (hmHi : (mHi : ℝ) ≤ 2 * T) :
    ((⌊(mHi : ℝ) * kubalalikaEps T⌋₊ : ℕ) : ℝ) ≤ 2 * T ^ (3 / 4 : ℝ) := by
  have heps := h.eps_pos
  have h1 : ((⌊(mHi : ℝ) * kubalalikaEps T⌋₊ : ℕ) : ℝ) ≤ (mHi : ℝ) * kubalalikaEps T :=
    Nat.floor_le (by positivity)
  have h2 : (mHi : ℝ) * kubalalikaEps T ≤ 2 * T * kubalalikaEps T :=
    mul_le_mul_of_nonneg_right hmHi heps.le
  have h3 : T * kubalalikaEps T = T ^ (3 / 4 : ℝ) := by
    rw [kubalalikaEps_eq_rpow h.pos.le]
    nth_rewrite 1 [show T = T ^ (1 : ℝ) from (Real.rpow_one T).symm]
    rw [← Real.rpow_add h.pos]
    norm_num
  calc ((⌊(mHi : ℝ) * kubalalikaEps T⌋₊ : ℕ) : ℝ) ≤ 2 * T * kubalalikaEps T := le_trans h1 h2
    _ = 2 * (T * kubalalikaEps T) := by ring
    _ = 2 * T ^ (3 / 4 : ℝ) := by rw [h3]

/-- The two Vaughan parameters. -/
theorem KubalalikaLarge.ceil_bounds (h : KubalalikaLarge T) (e : ℝ) (he : 0 ≤ e) :
    T ^ e ≤ ((⌈T ^ e⌉₊ : ℕ) : ℝ) ∧ ((⌈T ^ e⌉₊ : ℕ) : ℝ) ≤ 2 * T ^ e ∧ 1 ≤ ⌈T ^ e⌉₊ := by
  have h1 : (1 : ℝ) ≤ T ^ e := Real.one_le_rpow h.one_le he
  refine ⟨Nat.le_ceil _, ?_, ?_⟩
  · have := Nat.ceil_lt_add_one (le_trans zero_le_one h1)
    linarith
  · have : (1 : ℝ) ≤ ((⌈T ^ e⌉₊ : ℕ) : ℝ) := le_trans h1 (Nat.le_ceil _)
    exact_mod_cast this

/-- **Every scalar hypothesis of the mixed hybrid block estimate.** -/
theorem KubalalikaLarge.block_conditions (h : KubalalikaLarge T) {r : ℝ} {A B U V : ℕ}
    (hr1 : T ^ (1 / 4 : ℝ) ≤ r) (hr2 : r ≤ 2 * T ^ (3 / 4 : ℝ)) (hAB : A ≤ B)
    (hAlow : T / (2 * (1 + Real.log T) ^ 2) ≤ (A : ℝ)) (hB3 : (B : ℝ) ≤ 3 * T)
    (hU2 : (U : ℝ) ≤ 2 * T ^ (1 / 2 : ℝ)) (hV2 : (V : ℝ) ≤ 2 * T ^ (1 / 8 : ℝ)) :
    U < A ∧ U * V ≤ A ∧ 8 * r ≤ (A : ℝ) ∧
      T * r * ((U * V : ℕ) : ℝ) ^ 3 ≤ 72 * Real.pi * (A : ℝ) ^ 4 ∧
      (10 : ℝ) ^ 27 * (A : ℝ) ≤ T * r := by
  have hT0 := h.pos
  have hlog := h.one_le_log
  set s : ℝ := 1 + Real.log T with hsdef
  have hs : (1 : ℝ) ≤ s := by rw [hsdef]; linarith
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have hden : (0 : ℝ) < 2 * s ^ 2 := by positivity
  have hT34 : (0 : ℝ) < T ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hkey : 32 * s ^ 2 * T ^ (3 / 4 : ℝ) ≤ T := by
    have h1 : 32 * s ^ 2 ≤ T ^ (1 / 4 : ℝ) := h.2.1
    have h2 : T ^ (1 / 4 : ℝ) * T ^ (3 / 4 : ℝ) = T := by
      rw [← Real.rpow_add hT0]
      norm_num
    calc 32 * s ^ 2 * T ^ (3 / 4 : ℝ) ≤ T ^ (1 / 4 : ℝ) * T ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right h1 hT34.le
      _ = T := h2
  have hdiv : ∀ x : ℝ, 0 ≤ x → 2 * s ^ 2 * x ≤ T → x ≤ (A : ℝ) := by
    intro x hx hxT
    have hstep : x ≤ T / (2 * s ^ 2) := by
      rw [le_div_iff₀ hden]
      linarith
    exact le_trans hstep hAlow
  -- the two Vaughan parameters fit inside the block
  have hUlt : (U : ℝ) < (A : ℝ) := by
    have hT12 : T ^ (1 / 2 : ℝ) ≤ T ^ (3 / 4 : ℝ) := h.rpow_le_rpow_exp (by norm_num)
    have hT120 : (0 : ℝ) < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT0 _
    have hlt : 2 * T ^ (1 / 2 : ℝ) < T / (2 * s ^ 2) := by
      rw [lt_div_iff₀ hden]
      have h1 : 2 * s ^ 2 * (2 * T ^ (1 / 2 : ℝ)) ≤ 4 * s ^ 2 * T ^ (3 / 4 : ℝ) := by
        nlinarith only [hT12, hs0, hT120, sq_nonneg s]
      have h2 : 4 * s ^ 2 * T ^ (3 / 4 : ℝ) < 32 * s ^ 2 * T ^ (3 / 4 : ℝ) := by
        have hpos : (0 : ℝ) < s ^ 2 * T ^ (3 / 4 : ℝ) := mul_pos (pow_pos hs0 2) hT34
        nlinarith only [hpos]
      linarith [hkey]
    calc (U : ℝ) ≤ 2 * T ^ (1 / 2 : ℝ) := hU2
      _ < T / (2 * s ^ 2) := hlt
      _ ≤ (A : ℝ) := hAlow
  have hUVle : ((U * V : ℕ) : ℝ) ≤ (A : ℝ) := by
    have hcast : ((U * V : ℕ) : ℝ) = (U : ℝ) * (V : ℝ) := by push_cast; ring
    have hU0 : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg _
    have hV0 : (0 : ℝ) ≤ (V : ℝ) := Nat.cast_nonneg _
    have hprod : (U : ℝ) * (V : ℝ) ≤ 4 * T ^ (5 / 8 : ℝ) := by
      have hmul : (U : ℝ) * (V : ℝ) ≤ (2 * T ^ (1 / 2 : ℝ)) * (2 * T ^ (1 / 8 : ℝ)) :=
        mul_le_mul hU2 hV2 hV0 (by positivity)
      have hval : (2 * T ^ (1 / 2 : ℝ)) * (2 * T ^ (1 / 8 : ℝ)) = 4 * T ^ (5 / 8 : ℝ) := by
        rw [show (5 / 8 : ℝ) = 1 / 2 + 1 / 8 by norm_num, Real.rpow_add hT0]
        ring
      linarith [hval ▸ hmul]
    have hT58 : T ^ (5 / 8 : ℝ) ≤ T ^ (3 / 4 : ℝ) := h.rpow_le_rpow_exp (by norm_num)
    have hT580 : (0 : ℝ) ≤ T ^ (5 / 8 : ℝ) := (Real.rpow_pos_of_pos hT0 _).le
    have hbnd : 2 * s ^ 2 * (4 * T ^ (5 / 8 : ℝ)) ≤ T := by
      have h1 : 2 * s ^ 2 * (4 * T ^ (5 / 8 : ℝ)) ≤ 8 * s ^ 2 * T ^ (3 / 4 : ℝ) := by
        nlinarith only [hT58, hs0, hT580, sq_nonneg s]
      have h2 : 8 * s ^ 2 * T ^ (3 / 4 : ℝ) ≤ 32 * s ^ 2 * T ^ (3 / 4 : ℝ) := by
        have hpos : (0 : ℝ) < s ^ 2 * T ^ (3 / 4 : ℝ) := mul_pos (pow_pos hs0 2) hT34
        nlinarith only [hpos]
      linarith [hkey]
    have := hdiv (4 * T ^ (5 / 8 : ℝ)) (by positivity) hbnd
    rw [hcast]
    linarith [hprod]
  have h8r : 8 * r ≤ (A : ℝ) := by
    have hbnd : 2 * s ^ 2 * (16 * T ^ (3 / 4 : ℝ)) ≤ T := by
      have : 2 * s ^ 2 * (16 * T ^ (3 / 4 : ℝ)) = 32 * s ^ 2 * T ^ (3 / 4 : ℝ) := by ring
      linarith [hkey, this]
    have := hdiv (16 * T ^ (3 / 4 : ℝ)) (by positivity) hbnd
    linarith [hr2]
  -- the reciprocal scale dominates the block scale
  have hAX : (10 : ℝ) ^ 27 * (A : ℝ) ≤ T * r := by
    have hAB' : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
    have hA3 : (A : ℝ) ≤ 3 * T := le_trans hAB' hB3
    have hten : (3 : ℝ) * 10 ^ 27 ≤ T ^ (1 / 4 : ℝ) := by
      have hbase : (((10 : ℝ) ^ 112)) ^ (1 / 4 : ℝ) ≤ T ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) h.1 (by norm_num)
      have hval : (((10 : ℝ) ^ 112)) ^ (1 / 4 : ℝ) = (10 : ℝ) ^ 28 := by
        rw [show ((10 : ℝ) ^ 112) = ((10 : ℝ) ^ 28) ^ (4 : ℕ) by norm_num,
          ← Real.rpow_natCast ((10 : ℝ) ^ 28) 4, ← Real.rpow_mul (by positivity)]
        norm_num
      have h3 : (3 : ℝ) * 10 ^ 27 ≤ (10 : ℝ) ^ 28 := by norm_num
      linarith [hval ▸ hbase]
    have hTr : T * T ^ (1 / 4 : ℝ) ≤ T * r := mul_le_mul_of_nonneg_left hr1 hT0.le
    have hstep : (10 : ℝ) ^ 27 * (A : ℝ) ≤ T * T ^ (1 / 4 : ℝ) := by
      have h1 : (10 : ℝ) ^ 27 * (A : ℝ) ≤ 10 ^ 27 * (3 * T) := by
        have : (0 : ℝ) ≤ (10 : ℝ) ^ 27 := by positivity
        nlinarith only [hA3, this]
      have h2 : (10 : ℝ) ^ 27 * (3 * T) ≤ T * T ^ (1 / 4 : ℝ) := by
        nlinarith only [hten, hT0]
      linarith
    linarith
  -- the curvature condition
  have hcurv : T * r * ((U * V : ℕ) : ℝ) ^ 3 ≤ 72 * Real.pi * (A : ℝ) ^ 4 := by
    have hcast : ((U * V : ℕ) : ℝ) = (U : ℝ) * (V : ℝ) := by push_cast; ring
    have hU0 : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg _
    have hV0 : (0 : ℝ) ≤ (V : ℝ) := Nat.cast_nonneg _
    have hprod : (U : ℝ) * (V : ℝ) ≤ 4 * T ^ (5 / 8 : ℝ) := by
      have hmul : (U : ℝ) * (V : ℝ) ≤ (2 * T ^ (1 / 2 : ℝ)) * (2 * T ^ (1 / 8 : ℝ)) :=
        mul_le_mul hU2 hV2 hV0 (by positivity)
      have hval : (2 * T ^ (1 / 2 : ℝ)) * (2 * T ^ (1 / 8 : ℝ)) = 4 * T ^ (5 / 8 : ℝ) := by
        rw [show (5 / 8 : ℝ) = 1 / 2 + 1 / 8 by norm_num, Real.rpow_add hT0]
        ring
      linarith [hval ▸ hmul]
    have hcube : ((U * V : ℕ) : ℝ) ^ 3 ≤ 64 * T ^ (15 / 8 : ℝ) := by
      have hc : (T ^ (5 / 8 : ℝ)) ^ 3 = T ^ (15 / 8 : ℝ) := by
        rw [← Real.rpow_natCast (T ^ (5 / 8 : ℝ)) 3, ← Real.rpow_mul hT0.le]
        norm_num
      calc ((U * V : ℕ) : ℝ) ^ 3 ≤ (4 * T ^ (5 / 8 : ℝ)) ^ 3 := by
            rw [hcast]
            exact pow_le_pow_left₀ (by positivity) hprod 3
        _ = 64 * (T ^ (5 / 8 : ℝ)) ^ 3 := by ring
        _ = 64 * T ^ (15 / 8 : ℝ) := by rw [hc]
    have hLHS : T * r * ((U * V : ℕ) : ℝ) ^ 3 ≤ 128 * T ^ (29 / 8 : ℝ) := by
      have hcomb : T * (2 * T ^ (3 / 4 : ℝ)) * (64 * T ^ (15 / 8 : ℝ))
          = 128 * T ^ (29 / 8 : ℝ) := by
        have h1 : T ^ (1 : ℝ) * T ^ (3 / 4 : ℝ) * T ^ (15 / 8 : ℝ) = T ^ (29 / 8 : ℝ) := by
          rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
          norm_num
        calc T * (2 * T ^ (3 / 4 : ℝ)) * (64 * T ^ (15 / 8 : ℝ))
            = 128 * (T ^ (1 : ℝ) * T ^ (3 / 4 : ℝ) * T ^ (15 / 8 : ℝ)) := by
              rw [Real.rpow_one]; ring
          _ = 128 * T ^ (29 / 8 : ℝ) := by rw [h1]
      calc T * r * ((U * V : ℕ) : ℝ) ^ 3
          ≤ T * (2 * T ^ (3 / 4 : ℝ)) * (64 * T ^ (15 / 8 : ℝ)) := by
            refine mul3_le hT0.le (le_trans (Real.rpow_pos_of_pos hT0 _).le hr1)
              (by positivity) le_rfl hr2 hcube
        _ = 128 * T ^ (29 / 8 : ℝ) := hcomb
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
    have hlow0 : (0 : ℝ) ≤ T / (2 * s ^ 2) := by positivity
    have hA4 : (T / (2 * s ^ 2)) ^ 4 ≤ (A : ℝ) ^ 4 := pow_le_pow_left₀ hlow0 hAlow 4
    have hsplit : T ^ (4 : ℕ) = T ^ (29 / 8 : ℝ) * T ^ (3 / 8 : ℝ) := by
      rw [← Real.rpow_add hT0, ← Real.rpow_natCast T 4]
      norm_num
    have hT290 : (0 : ℝ) < T ^ (29 / 8 : ℝ) := Real.rpow_pos_of_pos hT0 _
    have hT8 : 100 * s ^ 8 ≤ T ^ (3 / 8 : ℝ) := h.2.2
    have hlowval : (T / (2 * s ^ 2)) ^ 4 = T ^ (4 : ℕ) / (16 * s ^ 8) := by
      rw [div_pow]
      ring_nf
    have hs8 : (0 : ℝ) < 16 * s ^ 8 := by
      have := pow_pos hs0 8
      linarith
    have hRHS : 128 * T ^ (29 / 8 : ℝ) ≤ 216 * (T / (2 * s ^ 2)) ^ 4 := by
      have hval : 216 * (T ^ (29 / 8 : ℝ) * T ^ (3 / 8 : ℝ) / (16 * s ^ 8))
          = (216 * (T ^ (29 / 8 : ℝ) * T ^ (3 / 8 : ℝ))) / (16 * s ^ 8) := by ring
      rw [hlowval, hsplit, hval, le_div_iff₀ hs8]
      have h1 : 2048 * s ^ 8 ≤ 216 * T ^ (3 / 8 : ℝ) := by
        nlinarith only [hT8, hs0, pow_nonneg hs0.le 8]
      nlinarith only [h1, hT290]
    have hfinal : 216 * (T / (2 * s ^ 2)) ^ 4 ≤ 72 * Real.pi * (A : ℝ) ^ 4 := by
      have h1 : 216 * (T / (2 * s ^ 2)) ^ 4 ≤ 216 * (A : ℝ) ^ 4 := by linarith
      have h2 : 216 * (A : ℝ) ^ 4 ≤ 72 * Real.pi * (A : ℝ) ^ 4 := by
        have : (0 : ℝ) ≤ (A : ℝ) ^ 4 := by positivity
        nlinarith only [hpi, this]
      linarith
    linarith
  have hUV : U * V ≤ A := by exact_mod_cast hUVle
  have hU : U < A := by exact_mod_cast hUlt
  exact ⟨hU, hUV, h8r, hcurv, hAX⟩

end

end RHTower.Sieve
