import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBoxHighMoments

/-!
# Typical `ζ'/ζ` box bound at one scale, with a scale-dependent explicit-formula length

At scale `R` with `κ = R log T`, put `s = √κ`, take the explicit-formula length `x = T^{1/s}` and
the moment order `m = ⌊s/4⌋` of the prime part. Then `N_x^m ≤ 2^m T^{1/2}`, and:

* the Lorentzian and far-majorant terms decay like `e^{−(R/4) log x} = e^{−s/4}`
  (`lorentz_term_sqrt_le`, `far_term_sqrt_le`);
* the window term decays like `e^{−κ/9600} ≤ e^{−s/4}` (`window_term_sqrt_le`);
* the prime moment is `m!(1280/(ε²κ²))^m ≤ (320/(ε²s³))^m ≤ 3e^{−s/4}`
  (`factorial_mul_pow_le_exp_sqrt`).

Hence the heights `t ∈ [T, 2T]` without log-derivative scale data at level `ε log T` have measure
`≤ C T e^{−√κ/4} + C T^{1/2}` for `κ ≥ max(9·10⁸, 1000/ε²)`
(`exists_volume_not_zetaLogDerivScaleData_le_sqrt`).
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- The Lorentzian term at length `log x = L/s`, `κ = s²`. -/
theorem lorentz_term_sqrt_le {T L R ε C₀ x s : ℝ} (hT : 0 < T) (hL0 : 0 < L) (hR : 0 < R)
    (hε : 0 < ε) (hC₀ : 0 < C₀) (hs : 1 ≤ s) (hκ : R * L = s ^ 2) (hlx : Real.log x = L / s)
    (hΦ : C₀ * (4 * T + 4) * Real.log (4 * T + 5) ≤ 10 * C₀ * T * L) :
    4 * Real.pi / R * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) /
      (ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153)) ≤
      368960 * Real.pi * C₀ * T * (Real.exp (-(s / 4)) / ε) := by
  have hs0 : 0 < s := by linarith
  rw [hlx]
  set E := Real.exp (-(s / 4)) with hE
  have hexp : -(R / 4) * (L / s) = -(s / 4) := by
    have e1 : -(R / 4) * (L / s) = -(R * L) / (4 * s) := by field_simp
    rw [e1, hκ]; field_simp
  rw [hexp, ← hE]
  have hE0 : 0 < E := Real.exp_pos _
  set Φ := C₀ * (4 * T + 4) * Real.log (4 * T + 5) with hΦdef
  calc 4 * Real.pi / R * Φ / (ε * L / 4 / (2 * E / (L / s) * 1153))
      = 36896 * Real.pi * s * E / (ε * R * L ^ 2) * Φ := by field_simp; ring
    _ ≤ 36896 * Real.pi * s * E / (ε * R * L ^ 2) * (10 * C₀ * T * L) :=
        mul_le_mul_of_nonneg_left hΦ (by positivity)
    _ = 368960 * Real.pi * C₀ * T * (E / ε) * (s / (R * L)) := by field_simp; norm_num
    _ = 368960 * Real.pi * C₀ * T * (E / ε) / s := by rw [hκ]; field_simp
    _ ≤ 368960 * Real.pi * C₀ * T * (E / ε) := div_le_self (by positivity) hs

/-- The far-majorant term at length `log x = L/s`, `κ = s²`. -/
theorem far_term_sqrt_le {T L R ε C₀ x s : ℝ} (hT : 0 < T) (hL0 : 0 < L) (hR : 0 < R)
    (hε : 0 < ε) (hC₀ : 0 < C₀) (hs : 1 ≤ s) (hκ : R * L = s ^ 2) (hlx : Real.log x = L / s)
    (hΦ : C₀ * (4 * T + 4) * Real.log (4 * T + 5) ≤ 10 * C₀ * T * L)
    (hΦ0 : 0 ≤ Real.log (4 * T + 5)) :
    4 * Real.pi / (3 * R * Real.log x) * Real.exp (-(R / 2 * Real.log x)) *
      (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / (ε * L / 4) ≤
      54 * Real.pi * C₀ * T * (Real.exp (-(s / 4)) / ε) := by
  have hs0 : 0 < s := by linarith
  rw [hlx]
  have hexp : -(R / 2 * (L / s)) = -(s / 2) := by
    have e1 : -(R / 2 * (L / s)) = -(R * L) / (2 * s) := by field_simp
    rw [e1, hκ]; field_simp
  rw [hexp]
  set E := Real.exp (-(s / 4)) with hE
  have hE2 : Real.exp (-(s / 2)) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr; linarith
  set Φ := C₀ * (4 * T + 4) * Real.log (4 * T + 5) with hΦdef
  have hΦ0' : 0 ≤ Φ := by positivity
  calc 4 * Real.pi / (3 * R * (L / s)) * Real.exp (-(s / 2)) * Φ / (ε * L / 4)
      = 16 * Real.pi * s / (3 * ε * R * L ^ 2) * (Real.exp (-(s / 2)) * Φ) := by
        field_simp; ring
    _ ≤ 16 * Real.pi * s / (3 * ε * R * L ^ 2) * (E * (10 * C₀ * T * L)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hE2 hΦ hΦ0' (Real.exp_pos _).le
    _ = 160 / 3 * Real.pi * C₀ * T * (E / ε) * (s / (R * L)) := by field_simp; ring
    _ = 160 / 3 * Real.pi * C₀ * T * (E / ε) / s := by rw [hκ]; field_simp
    _ ≤ 160 / 3 * Real.pi * C₀ * T * (E / ε) := div_le_self (by positivity) hs
    _ ≤ 54 * Real.pi * C₀ * T * (E / ε) := by
        have : 0 ≤ Real.pi * C₀ * T * (E / ε) := by positivity
        nlinarith

/-- The window term at length `log x = L/s`, `κ = s²`, `s ≥ 30000`. -/
theorem window_term_sqrt_le {T L R ε A Kw x S s : ℝ} (hT : 0 < T) (hL : Real.log T = L)
    (hL0 : 0 < L) (hs : 30000 ≤ s) (hκ : R * L = s ^ 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 0 < A) (hKw : 0 ≤ Kw)
    (hlx : Real.log x = L / s)
    (hE5 : 144 * Kw / Real.pi * (L + 3) ^ 2 ≤ Real.exp ((1 / 2 - 1 / 10000) * L))
    (hS : S ≤ 168 * T * A / Real.pi * (1 + 9600 / (R * L)) * Real.exp (-(R * L / 9600)) +
      144 * (L + 3) ^ 2 * Kw * Real.exp (3 * Real.log x) / Real.pi) :
    S ≤ 336 * A / Real.pi * T * (Real.exp (-(s / 4)) / ε) + T ^ ((1 : ℝ) / 2) := by
  have hs0 : 0 < s := by linarith
  rw [hκ] at hS
  set E := Real.exp (-(s / 4)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEε : E ≤ E / ε := le_div_self hE0.le hε hε1
  have ha1 : 168 * T * A / Real.pi * (1 + 9600 / s ^ 2) * Real.exp (-(s ^ 2 / 9600)) ≤
      336 * A / Real.pi * T * (E / ε) := by
    have h1 : 1 + 9600 / s ^ 2 ≤ 2 := by
      have : 9600 / s ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
      linarith
    have h2 : Real.exp (-(s ^ 2 / 9600)) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.mpr
      have : s / 4 ≤ s ^ 2 / 9600 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
      linarith
    have hc : 0 ≤ 168 * T * A / Real.pi := by positivity
    calc 168 * T * A / Real.pi * (1 + 9600 / s ^ 2) * Real.exp (-(s ^ 2 / 9600))
        ≤ 168 * T * A / Real.pi * 2 * E :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (Real.exp_pos _).le (by positivity)
      _ = 336 * A / Real.pi * T * E := by ring
      _ ≤ 336 * A / Real.pi * T * (E / ε) :=
          mul_le_mul_of_nonneg_left hEε (by positivity)
  have ha2 : 144 * (L + 3) ^ 2 * Kw * Real.exp (3 * Real.log x) / Real.pi ≤
      T ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hT, hL, hlx]
    have h3 : Real.exp (3 * (L / s)) ≤ Real.exp (L / 10000) := by
      apply Real.exp_le_exp.mpr
      rw [show 3 * (L / s) = L * (3 / s) by ring, show L / 10000 = L * (1 / 10000) by ring]
      apply mul_le_mul_of_nonneg_left _ hL0.le
      rw [div_le_div_iff₀ hs0 (by norm_num)]; linarith
    have e : 144 * (L + 3) ^ 2 * Kw * Real.exp (L / 10000) / Real.pi =
        144 * Kw / Real.pi * (L + 3) ^ 2 * Real.exp (L / 10000) := by ring
    have hmono : 144 * (L + 3) ^ 2 * Kw * Real.exp (3 * (L / s)) / Real.pi ≤
        144 * (L + 3) ^ 2 * Kw * Real.exp (L / 10000) / Real.pi := by
      apply div_le_div_of_nonneg_right _ Real.pi_pos.le
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    refine hmono.trans ?_
    rw [e]
    have e2 : Real.exp (L * (1 / 2)) = Real.exp ((1 / 2 - 1 / 10000) * L) * Real.exp (L / 10000) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e2]
    exact mul_le_mul_of_nonneg_right hE5 (Real.exp_pos _).le
  linarith

/-- The length term at length `log x = L/s` and moment order `m ≤ s/4`. -/
theorem polyLength_pow_term_sqrt_le {T s : ℝ} {m : ℕ} (hT : 1 < T) (hs : 2 ≤ s)
    (hm : 4 * (m : ℝ) ≤ s)
    (h : 8 * 2 ^ m * (1 + (m : ℝ)) * (Real.log T + 3) ≤ Real.exp (1 / 2 * Real.log T)) :
    8 * ((selbergPolyLength (Real.exp (Real.log T / s)) ^ m : ℕ) : ℝ) *
      (1 + Real.log ((selbergPolyLength (Real.exp (Real.log T / s)) ^ m : ℕ) : ℝ)) ≤ T := by
  set L := Real.log T with hL
  have hL0 : 0 < L := Real.log_pos hT
  have hs0 : 0 < s := by linarith
  set x := Real.exp (L / s) with hx
  set N := selbergPolyLength x with hN
  have hx2 : x ^ 2 = Real.exp (2 * L / s) := by
    rw [hx, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hx21 : 1 ≤ x ^ 2 := by rw [hx2]; exact Real.one_le_exp (by positivity)
  have hNle : (N : ℝ) ≤ 2 * Real.exp (2 * L / s) := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ x ^ 2 by positivity)
    rw [hN, selbergPolyLength, ← hx2]
    linarith
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hN, selbergPolyLength]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      rw [Nat.ceil_eq_zero] at h0
      linarith)
  have h2Ls : 2 * L / s ≤ L := by
    rw [div_le_iff₀ hs0]; nlinarith
  have hlogN : Real.log N ≤ 1 + L := by
    have h1 : Real.log N ≤ Real.log (2 * Real.exp (2 * L / s)) :=
      Real.log_le_log (by linarith) hNle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp] at h1
    have := Real.log_two_lt_d9
    linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [Nat.cast_pow, Real.log_pow]
  have hNm : (N : ℝ) ^ m ≤ 2 ^ m * Real.exp (1 / 2 * L) := by
    calc (N : ℝ) ^ m ≤ (2 * Real.exp (2 * L / s)) ^ m :=
          pow_le_pow_left₀ (by linarith) hNle m
      _ = 2 ^ m * Real.exp (m * (2 * L / s)) := by rw [mul_pow, ← Real.exp_nat_mul]
      _ ≤ 2 ^ m * Real.exp (1 / 2 * L) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          have e : (m : ℝ) * (2 * L / s) = 2 * m / s * L := by ring
          rw [e]
          have h1 : 2 * (m : ℝ) / s ≤ 1 / 2 := by
            rw [div_le_iff₀ hs0]; linarith
          exact mul_le_mul_of_nonneg_right h1 hL0.le
  have hlog : 1 + (m : ℝ) * Real.log N ≤ (1 + m) * (L + 3) := by
    have : (m : ℝ) * Real.log N ≤ m * (1 + L) := mul_le_mul_of_nonneg_left hlogN hm0
    nlinarith
  have hT' : T = Real.exp (1 / 2 * L) * Real.exp (1 / 2 * L) := by
    rw [← Real.exp_add, show 1 / 2 * L + 1 / 2 * L = L by ring, hL, Real.exp_log (by linarith)]
  calc 8 * (N : ℝ) ^ m * (1 + (m : ℝ) * Real.log N)
      ≤ 8 * (2 ^ m * Real.exp (1 / 2 * L)) * ((1 + m) * (L + 3)) :=
        mul_le_mul (by linarith) hlog (by positivity) (by positivity)
    _ = 8 * 2 ^ m * (1 + (m : ℝ)) * (L + 3) * Real.exp (1 / 2 * L) := by ring
    _ ≤ Real.exp (1 / 2 * L) * Real.exp (1 / 2 * L) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = T := hT'.symm

/-- **The prime moment at order `m = ⌊s/4⌋`:** `m!(1280/(ε²κ²))^m ≤ 3e^{−s/4}` for `κ = s²`,
`s³ ≥ 1000/ε²`. -/
theorem factorial_mul_pow_le_exp_sqrt {ε s : ℝ} (hε : 0 < ε) (hs : 4 ≤ s)
    (hs3 : 1000 / ε ^ 2 ≤ s ^ 3) :
    ((⌊s / 4⌋₊).factorial : ℝ) * (1280 / (ε ^ 2 * (s ^ 2) ^ 2)) ^ ⌊s / 4⌋₊ ≤
      3 * Real.exp (-(s / 4)) := by
  set m := ⌊s / 4⌋₊ with hm
  have hs0 : 0 < s := by linarith
  set q : ℝ := 1280 / (ε ^ 2 * (s ^ 2) ^ 2) with hq
  have hq0 : 0 ≤ q := by positivity
  have hmle : (m : ℝ) ≤ s / 4 := Nat.floor_le (by positivity)
  have hmgt : s / 4 < m + 1 := Nat.lt_floor_add_one _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  have hmq : (m : ℝ) * q ≤ Real.exp (-1) := by
    have h1 : (m : ℝ) * q ≤ s / 4 * q := mul_le_mul_of_nonneg_right hmle hq0
    have h2 : s / 4 * q = 320 / (ε ^ 2 * s ^ 3) := by rw [hq]; field_simp; ring
    have h3 : 320 / (ε ^ 2 * s ^ 3) ≤ 32 / 100 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).mp hs3
      nlinarith
    have h4 : (32 / 100 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
      have := Real.exp_one_lt_d9
      norm_num at this ⊢
      linarith
    linarith
  have hmq0 : 0 ≤ (m : ℝ) * q := by positivity
  calc (m.factorial : ℝ) * q ^ m ≤ (m : ℝ) ^ m * q ^ m :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = ((m : ℝ) * q) ^ m := (mul_pow _ _ _).symm
    _ ≤ Real.exp (-1) ^ m := pow_le_pow_left₀ hmq0 hmq m
    _ = Real.exp (m * (-1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (1 + -(s / 4)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp 1 * Real.exp (-(s / 4)) := Real.exp_add _ _
    _ ≤ 3 * Real.exp (-(s / 4)) := by
        have := Real.exp_one_lt_d9
        have h0 := Real.exp_pos (-(s / 4))
        nlinarith

/-- `(log T + 3)⁴⁰ ≤ e^{4√(log T)}` for all large `T`. -/
theorem eventually_log_add_pow_le_exp_sqrt :
    ∀ᶠ T in atTop, (Real.log T + 3) ^ 40 ≤ Real.exp (4 * Real.sqrt (Real.log T)) := by
  have ho := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)).bound
    (show (0 : ℝ) < 1 / 20 by norm_num)
  have hL : Tendsto (fun T : ℝ => Real.log T + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ 3 Real.tendsto_log_atTop
  filter_upwards [hL.eventually ho, Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hT hT1
  set L := Real.log T with hLdef
  have hu : 0 < L + 3 := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
    abs_of_nonneg (Real.rpow_nonneg hu.le _), ← Real.sqrt_eq_rpow] at hT
  have hsq : Real.sqrt (L + 3) ≤ 2 * Real.sqrt L := by
    have h4 : Real.sqrt (4 * L) = 2 * Real.sqrt L := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← h4]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [← Real.exp_log (pow_pos hu 40), Real.log_pow]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith

/-- The scale parameters: `s = √κ` with `κ = R log T`. -/
theorem sqrt_scale_facts {L R ε : ℝ} (hL16 : 16 ≤ L) (hR16 : R ≤ 1 / 16)
    (hκ : max (9 * 10 ^ 8) (1000 / ε ^ 2) ≤ R * L) :
    30000 ≤ Real.sqrt (R * L) ∧ Real.sqrt (R * L) ^ 2 = R * L ∧
      4 * Real.sqrt (R * L) ≤ Real.sqrt L ∧ 1000 / ε ^ 2 ≤ Real.sqrt (R * L) ^ 3 := by
  have hκ9 : 9 * 10 ^ 8 ≤ R * L := le_trans (le_max_left _ _) hκ
  have hκε : 1000 / ε ^ 2 ≤ R * L := le_trans (le_max_right _ _) hκ
  have hs2 : Real.sqrt (R * L) ^ 2 = R * L := Real.sq_sqrt (by linarith)
  have hs30 : 30000 ≤ Real.sqrt (R * L) :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  refine ⟨hs30, hs2, ?_, ?_⟩
  · refine (Real.le_sqrt (by positivity) (by linarith)).mpr ?_
    rw [mul_pow, hs2]
    have hR0 : 0 ≤ R := by
      by_contra h
      push Not at h
      have : R * L < 0 := mul_neg_of_neg_of_pos h (by linarith)
      linarith
    nlinarith
  · calc 1000 / ε ^ 2 ≤ R * L := hκε
      _ = Real.sqrt (R * L) ^ 2 := hs2.symm
      _ ≤ Real.sqrt (R * L) ^ 3 := by
          rw [pow_succ]
          exact le_mul_of_one_le_right (by positivity) (by linarith)

/-- The growth condition of the length term: `8·2^m(1+m)(L+3) ≤ e^{L/2}` for `16m ≤ √L`. -/
theorem eight_two_pow_le_exp {L : ℝ} {m : ℕ} (hL16 : 16 ≤ L) (hm : 16 * (m : ℝ) ≤ Real.sqrt L)
    (hE7 : 8 * (L + 3) ^ 2 ≤ Real.exp (1 / 4 * L)) :
    8 * 2 ^ m * (1 + (m : ℝ)) * (L + 3) ≤ Real.exp (1 / 2 * L) := by
  have hsq : Real.sqrt L ≤ L := (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
  have hmL : (m : ℝ) ≤ L / 4 := by linarith
  have h2 : (2 : ℝ) ^ m ≤ Real.exp (L / 4) := by
    calc (2 : ℝ) ^ m ≤ Real.exp 1 ^ m := by
          refine pow_le_pow_left₀ (by norm_num) ?_ m
          have := Real.add_one_le_exp 1; linarith
      _ = Real.exp (m * 1) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (L / 4) := Real.exp_le_exp.mpr (by linarith)
  have h3 : 1 + (m : ℝ) ≤ L + 3 := by linarith
  have hsplit : Real.exp (1 / 2 * L) = Real.exp (L / 4) * Real.exp (1 / 4 * L) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  have hm0 : (0 : ℝ) ≤ 1 + m := by positivity
  have h4 := mul_le_mul h2 h3 hm0 (Real.exp_pos _).le
  calc 8 * 2 ^ m * (1 + (m : ℝ)) * (L + 3) = 8 * (2 ^ m * (1 + (m : ℝ))) * (L + 3) := by ring
    _ ≤ 8 * (Real.exp (L / 4) * (L + 3)) * (L + 3) := by gcongr
    _ = Real.exp (L / 4) * (8 * (L + 3) ^ 2) := by ring
    _ ≤ Real.exp (L / 4) * Real.exp (1 / 4 * L) :=
        mul_le_mul_of_nonneg_left hE7 (Real.exp_pos _).le

/-- The explicit-formula length `x = e^{L/s}`: the hypotheses of the explicit formula and of the
window sum. -/
theorem sqrt_length_facts {L R s : ℝ} (hL0 : 0 < L) (hs : 30000 ≤ s) (hs2 : s ^ 2 = R * L)
    (hsL : 4 * s ≤ Real.sqrt L) (hE40 : (L + 3) ^ 40 ≤ Real.exp (4 * Real.sqrt L)) :
    1 ≤ 36 * R * (L / s) ∧ (L + 3) ^ 40 ≤ Real.exp (L / s) ∧ L / s ≤ L / 8 ∧
      6 * (L / s) / L ≤ 1 / 4800 := by
  have hs0 : 0 < s := by linarith
  have hsqL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : 36 * R * (L / s) = 36 * s := by
      rw [show 36 * R * (L / s) = 36 * (R * L) / s by ring, ← hs2]; field_simp
    rw [e]; linarith
  · refine hE40.trans (Real.exp_le_exp.mpr ?_)
    rw [le_div_iff₀ hs0]
    have hsq0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
    nlinarith
  · exact div_le_div_of_nonneg_left hL0.le (by norm_num) (by linarith)
  · rw [show 6 * (L / s) / L = 6 / s by field_simp, div_le_div_iff₀ hs0 (by norm_num)]
    linarith

/-- The Dirichlet-polynomial level `εL/4` exceeds `96/R` once `κ ≥ 1000/ε²`, `ε ≤ 1`. -/
theorem ninetySix_div_le {L R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hκε : 1000 / ε ^ 2 ≤ R * L) : 96 / R ≤ ε * L / 4 := by
  rw [div_le_iff₀ hR]
  have h1 : 384 / ε ≤ 1000 / ε ^ 2 := by
    rw [div_le_div_iff₀ hε (by positivity)]; nlinarith
  have h2 := (div_le_iff₀ hε).mp (h1.trans hκε)
  nlinarith

/-- Combination of the four terms at the stretched rate. -/
theorem sqrt_terms_combine {Sw b c d A C₀ T E ε Ts : ℝ} (hA : 0 < A) (hC₀ : 0 < C₀)
    (hT : 0 ≤ T) (hE : 0 ≤ E) (hε : 0 < ε) (hTs : 0 ≤ Ts)
    (ha : Sw ≤ 336 * A / Real.pi * T * (E / ε) + Ts)
    (hb : b ≤ 368960 * Real.pi * C₀ * T * (E / ε)) (hc : c ≤ 54 * Real.pi * C₀ * T * (E / ε))
    (hd : d ≤ 12420 / Real.pi * T * E) :
    Sw + b + c + d ≤
      ((336 * A / Real.pi + 368960 * Real.pi * C₀ + 54 * Real.pi * C₀) / ε + 12420 / Real.pi + 1) *
          T * E +
        ((336 * A / Real.pi + 368960 * Real.pi * C₀ + 54 * Real.pi * C₀) / ε +
          12420 / Real.pi + 1) * Ts := by
  set K := (336 * A / Real.pi + 368960 * Real.pi * C₀ + 54 * Real.pi * C₀) / ε +
    12420 / Real.pi with hK
  have hK0 : 0 ≤ K := by positivity
  have hTE : 0 ≤ T * E := by positivity
  have e : 336 * A / Real.pi * T * (E / ε) + 368960 * Real.pi * C₀ * T * (E / ε) +
      54 * Real.pi * C₀ * T * (E / ε) + 12420 / Real.pi * T * E = K * (T * E) := by
    rw [hK]; field_simp
  have k1 : K * (T * E) ≤ (K + 1) * (T * E) := by nlinarith
  have k2 : Ts ≤ (K + 1) * Ts := by nlinarith
  have e2 : (K + 1) * T * E = (K + 1) * (T * E) := by ring
  rw [e2]
  linarith

/-- **Typical `ζ'/ζ` box bound at one scale, with a stretched-exponential rate.** For `0 < ε ≤ 1`
there is `C` such that for all large `T` and every scale `0 < R ≤ 1/16` with
`κ = R log T ≥ max(9·10⁸, 1000/ε²)`, the heights `t ∈ [T, 2T]` without log-derivative scale data at
level `ε log T` have measure `≤ C T e^{−√κ/4} + C T^{1/2}`. -/
theorem exists_volume_not_zetaLogDerivScaleData_le_sqrt {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T in atTop, ∀ R : ℝ, 0 < R → R ≤ 1 / 16 →
      max (9 * 10 ^ 8) (1000 / ε ^ 2) ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R (ε * Real.log T)} ≤
        ENNReal.ofReal (C * T * Real.exp (-(Real.sqrt (R * Real.log T) / 4)) +
          C * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨KE, hKE, hEFall⟩ := exists_selberg_explicit_formula_at_height
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (eventually_selbergHeightError_le_one hKE)
  obtain ⟨A, Kw, hA, hKw, hwin⟩ := exists_sum_selbergRightWindow_le
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_sum_mult_selbergMidZeros_le
  refine ⟨(336 * A / Real.pi + 368960 * Real.pi * C₀ + 54 * Real.pi * C₀) / ε +
    12420 / Real.pi + 1, by positivity, ?_⟩
  have hE3 := Real.tendsto_log_atTop.eventually_ge_atTop (4 / ε)
  have hE5 := eventually_mul_log_add_pow_le_exp 2 (144 * Kw / Real.pi)
    (show (0 : ℝ) < 1 / 2 - 1 / 10000 by norm_num)
  have hE7 := eventually_mul_log_add_pow_le_exp 2 8 (show (0 : ℝ) < 1 / 4 by norm_num)
  have hE16 := Real.tendsto_log_atTop.eventually_ge_atTop 16
  filter_upwards [hwin, eventually_ge_atTop (max t₀ 64), eventually_log_add_pow_le_exp_sqrt, hE3,
    hE5, hE7, hE16] with T hTwin hTt hE40 hE3 hE5 hE7 hE16
  intro R hR hR16 hκ
  have hT64 : 64 ≤ T := le_of_max_le_right hTt
  have hT0 : 0 < T := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log T := ⟨_, rfl⟩
  rw [← hLdef] at hκ hE40 hE3 hE5 hE7 hE16 hTwin ⊢
  have hL0 : 0 < L := by linarith
  obtain ⟨hs30, hs2, hsL, hs3⟩ := sqrt_scale_facts hE16 hR16 hκ
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (R * L) := ⟨_, rfl⟩
  rw [← hsdef] at hs30 hs2 hsL hs3 ⊢
  have hκε : 1000 / ε ^ 2 ≤ R * L := le_trans (le_max_right _ _) hκ
  clear hκ
  obtain ⟨hRx', hx40', hx8', hwin6⟩ := sqrt_length_facts hL0 hs30 hs2 hsL hE40
  obtain ⟨x, hxdef⟩ : ∃ x, x = Real.exp (L / s) := ⟨_, rfl⟩
  have hlx : Real.log x = L / s := by rw [hxdef, Real.log_exp]
  have hx : 1 < x := by rw [hxdef]; exact Real.one_lt_exp_iff.mpr (by positivity)
  have hEF := selberg_explicit_formula_block hEFall ht₀ hT64 (le_of_max_le_left hTt) hx
    (by rw [← hLdef, hxdef]; exact hx40') (by rw [hlx, ← hLdef]; exact hx8')
  clear hEFall ht₀
  obtain ⟨m, hmdef⟩ : ∃ m, m = ⌊s / 4⌋₊ := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by rw [hmdef]; exact Nat.le_floor (by push_cast; linarith)
  have hm4 : 4 * (m : ℝ) ≤ s := by
    have := Nat.floor_le (show (0 : ℝ) ≤ s / 4 by positivity)
    rw [← hmdef] at this; linarith
  have hEm := eight_two_pow_le_exp (m := m) hE16 (by linarith) hE7
  have hcL0 : 0 < 2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 := by
    have := Real.log_pos hx; positivity
  have hεL : 0 < ε * L / 4 := by positivity
  have hε4 : 4 ≤ ε * L := by
    have := (div_le_iff₀ hε).mp hE3
    linarith
  have hbox := volume_not_zetaLogDerivScaleData_le_of_largeNearBox (B := ε * L) (C₀ := C₀)
    (M_D := ε * L / 4) (M_L := ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) /
      Real.log x * 1153)) (M_F := ε * L / 4) hT64 hx hR hR16 (by rw [hlx]; exact hRx') hEF
    (hC₀ T (by linarith)) (div_pos hεL hcL0) hεL (by rw [mul_div_cancel₀ _ hcL0.ne']; linarith)
  have hD := (measure_mono (largeNearBox_selbergVonMangoldtPoly_subset_prime (T := T) hx hR hR16
    (ninetySix_div_le hR hε hε1 hκε))).trans (volume_largeNearBox_selbergPrimePoly_le hT0 hx hR
      hR16 (by positivity : 0 < ε * L / 4 / 2) hm1)
  have hΦ0 : 0 ≤ Real.log (4 * T + 5) := Real.log_nonneg (by linarith)
  have hΦ : C₀ * (4 * T + 4) * Real.log (4 * T + 5) ≤ 10 * C₀ * T * L := by
    have h1 : Real.log (4 * T + 5) ≤ 2 * L := by
      have : Real.log (4 * T + 5) ≤ Real.log (T ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith only [hT64])
      rw [Real.log_pow, ← hLdef] at this
      push_cast at this
      linarith
    have h3 : C₀ * (4 * T + 4) * Real.log (4 * T + 5) ≤ C₀ * (5 * T) * (2 * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC₀pos.le) h1 hΦ0 (by positivity)
    linarith
  have hRL4 : 4 ≤ R * L := by rw [← hs2]; nlinarith only [hs30]
  have hSa := hTwin x R hx hR (by linarith only [hR16]) hRL4 (by rw [hlx]; exact hwin6)
  have ha := window_term_sqrt_le hT0 hLdef.symm hL0 hs30 hs2.symm hε hε1 hA hKw hlx hE5 hSa
  have hb := lorentz_term_sqrt_le hT0 hL0 hR hε hC₀pos (by linarith) hs2.symm hlx hΦ
  have hc := far_term_sqrt_le hT0 hL0 hR hε hC₀pos (by linarith) hs2.symm hlx hΦ hΦ0
  have hN := polyLength_pow_term_sqrt_le (by linarith : 1 < T) (by linarith : 2 ≤ s) hm4
    (by rw [← hLdef]; exact hEm)
  rw [← hLdef, ← hxdef] at hN
  have hd0 := primePoly_term_le (m := m) hT64 hL0 hR hR16 hε hN
  rw [← hs2] at hd0
  have hfac := factorial_mul_pow_le_exp_sqrt hε (by linarith : 4 ≤ s) hs3
  rw [← hmdef] at hfac
  have hd := hd0.trans (by
    have := mul_le_mul_of_nonneg_left hfac (show 0 ≤ 4140 / Real.pi * T by positivity)
    exact this.trans_eq (by ring) : 4140 / Real.pi * T * (m.factorial *
      (1280 / (ε ^ 2 * (s ^ 2) ^ 2)) ^ m) ≤ 12420 / Real.pi * T * Real.exp (-(s / 4)))
  have hSw0 : 0 ≤ ∑ w ∈ (selbergMidZeros T).filter (fun w => 1 / 2 + R / 2 < w.re),
      2 * selbergRightWindow x R w := Finset.sum_nonneg fun w _ => by
    have := selbergRightWindow_pos (x := x) hR w; positivity
  have hnb : 0 ≤ 4 * Real.pi / R * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) /
      (ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153)) := by positivity
  have hnc : 0 ≤ 4 * Real.pi / (3 * R * Real.log x) * Real.exp (-(R / 2 * Real.log x)) *
      (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / (ε * L / 4) := by
    have := Real.log_pos hx; positivity
  have hsum := sqrt_terms_combine hA hC₀pos hT0.le (Real.exp_pos _).le hε
    (Real.rpow_nonneg hT0.le _) ha hb hc hd
  refine hbox.trans ?_
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal hsum)
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) hnc, ENNReal.ofReal_add hSw0 hnb]
  gcongr

end RHTower
