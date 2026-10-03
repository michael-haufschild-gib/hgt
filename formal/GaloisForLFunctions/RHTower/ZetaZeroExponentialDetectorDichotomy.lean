import GaloisForLFunctions.RHTower.ZetaZeroExponentialDetectorBounds

/-!
# The Type I / Type II dichotomy for zeros

At height `T` put `X = ⌊T^{1/30}⌋`, `Y = T^{3/5}` and `Z = ⌊T^{3/5} (log T)²⌋`.  There are
constants `K₀, c₀ > 0` such that for all large `T` every zero `ρ = β + iγ` of `ζ` with
`7/12 ≤ β < 1` and `T ≤ γ ≤ 2T` satisfies

* (Type I) `|Σ_{n ≤ Z} D(n) n^{-ρ} e^{-n/Y}| ≥ 1/8`, or
* (Type II) `∫_{|y| ≤ K₀ log T} |ζ(1/2 + i(γ + y))| dy ≥ c₀ Y^{β - 1/2} / X`.

Mechanism: the detector identity `tsum_moebiusZetaDefect_exp_eq` on `Re w = 1/2 - β` writes
`1 = S - r - J/2π`; the tail of `S` beyond `Z` is `≤ 4Y² e^{-Z/2Y} ≤ 4e^{1/2} T^{-9/5}`, the residue
`r` is `≤ T^{N+2} e^{-πT/2}`, and `J` is bounded by `exists_norm_integral_expDetIntegrand_le` with
`L = K₀ log T`, whose tail term is `≤ T^{1/30 - 2}`.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set

/-- The mollifier length `⌊T^{1/30}⌋`. -/
def expDetMoll (T : ℝ) : ℕ := ⌊T ^ (1 / 30 : ℝ)⌋₊

/-- The smoothing length `T^{3/5}`. -/
def expDetSmooth (T : ℝ) : ℝ := T ^ (3 / 5 : ℝ)

/-- The cutoff `⌊T^{3/5} (log T)²⌋`. -/
def expDetCut (T : ℝ) : ℕ := ⌊T ^ (3 / 5 : ℝ) * Real.log T ^ 2⌋₊

theorem one_le_expDetMoll {T : ℝ} (hT : 1 ≤ T) : 1 ≤ expDetMoll T := by
  unfold expDetMoll
  exact Nat.le_floor (by simpa using Real.one_le_rpow hT (by norm_num : (0 : ℝ) ≤ 1 / 30))

theorem expDetMoll_le {T : ℝ} (hT : 1 ≤ T) : (expDetMoll T : ℝ) ≤ T ^ (1 / 30 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg (by linarith) _)

theorem one_le_expDetSmooth {T : ℝ} (hT : 1 ≤ T) : 1 ≤ expDetSmooth T :=
  Real.one_le_rpow hT (by norm_num)

/-- The tail bound at the detector parameters: `4Y² e^{-Z/(2Y)} ≤ 1/8` once `log T ≥ 6`. -/
theorem expDet_tail_small {T : ℝ} (hT1 : 1 ≤ T) (hT : 6 ≤ Real.log T) :
    4 * expDetSmooth T ^ 2 * Real.exp (-((expDetCut T : ℝ) / (2 * expDetSmooth T))) ≤ 1 / 8 := by
  have hT0 : 0 < T := by linarith
  have hZ' : T ^ (3 / 5 : ℝ) * Real.log T ^ 2 - 1 ≤ (expDetCut T : ℝ) := by
    have := Nat.lt_floor_add_one (T ^ (3 / 5 : ℝ) * Real.log T ^ 2)
    unfold expDetCut
    linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = expDetSmooth T := ⟨_, rfl⟩
  rw [← hY]
  have hYT : Y = T ^ (3 / 5 : ℝ) := hY
  have hY1 : 1 ≤ Y := hY ▸ one_le_expDetSmooth hT1
  have hY0 : 0 < Y := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log T := ⟨_, rfl⟩
  rw [← hℓ] at hT hZ'
  rw [← hYT] at hZ'
  have hZ : Y * ℓ ^ 2 - 1 ≤ (expDetCut T : ℝ) := hZ'
  have hratio : ℓ ^ 2 / 2 - 1 / 2 ≤ (expDetCut T : ℝ) / (2 * Y) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hexp : Real.exp (-((expDetCut T : ℝ) / (2 * Y))) ≤ Real.exp (1 / 2) * T ^ (-(3 : ℝ)) := by
    rw [Real.rpow_def_of_pos hT0, ← Real.exp_add, ← hℓ]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hY2 : Y ^ 2 = T ^ (6 / 5 : ℝ) := by
    rw [hYT, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    norm_num
  have hTpow : T ^ (6 / 5 : ℝ) * T ^ (-(3 : ℝ)) = T ^ (-(9 / 5 : ℝ)) := by
    rw [← Real.rpow_add hT0]
    norm_num
  have he : Real.exp (1 / 2) ≤ 2 := by
    have := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hTbig : 403 ≤ T := by
    have h6 := Real.add_one_le_exp 6
    have : Real.exp 6 ≤ T := by rw [← Real.exp_log hT0, ← hℓ]; exact Real.exp_le_exp.mpr hT
    have he6 : (403 : ℝ) ≤ Real.exp 6 := by
      have h1 := Real.exp_one_gt_d9
      have : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) h1.le 6]
    linarith
  have hTneg : T ^ (-(9 / 5 : ℝ)) ≤ 1 / 64 := by
    have h1 : (64 : ℝ) ≤ T ^ (9 / 5 : ℝ) := by
      calc (64 : ℝ) ≤ 403 := by norm_num
        _ ≤ T := hTbig
        _ = T ^ (1 : ℝ) := (Real.rpow_one T).symm
        _ ≤ T ^ (9 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
    rw [Real.rpow_neg hT0.le, inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1
  calc 4 * Y ^ 2 * Real.exp (-((expDetCut T : ℝ) / (2 * Y)))
      ≤ 4 * Y ^ 2 * (Real.exp (1 / 2) * T ^ (-(3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 4 * Real.exp (1 / 2) * (T ^ (6 / 5 : ℝ) * T ^ (-(3 : ℝ))) := by rw [hY2]; ring
    _ = 4 * Real.exp (1 / 2) * T ^ (-(9 / 5 : ℝ)) := by rw [hTpow]
    _ ≤ 4 * 2 * (1 / 64) := by
        gcongr
    _ = 1 / 8 := by norm_num

/-- `T^a → 0` for `a < 0`, times a constant, is eventually below `1`. -/
theorem eventually_const_mul_rpow_neg_le_one (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ T : ℝ in atTop, C * T ^ (-a) ≤ 1 := by
  have h := (tendsto_rpow_neg_atTop ha).const_mul C
  rw [mul_zero] at h
  exact h.eventually (ge_mem_nhds (by norm_num))

/-- **The Type I / Type II dichotomy.** -/
theorem exists_expDetector_dichotomy :
    ∃ (K₀ c₀ T₀ : ℝ), 0 < c₀ ∧ 0 ≤ K₀ ∧ 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ ρ : ℂ,
      riemannZeta ρ = 0 → 7 / 12 ≤ ρ.re → ρ.re < 1 → T ≤ ρ.im → ρ.im ≤ 2 * T →
      1 / 8 ≤ ‖∑ n ∈ Finset.range (expDetCut T + 1),
          expDetTerm (expDetMoll T) ρ (expDetSmooth T) n‖ ∨
      c₀ * expDetSmooth T ^ (ρ.re - 1 / 2) / expDetMoll T ≤
        ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ.im + y : ℝ) : ℂ) * I)‖ := by
  obtain ⟨A, B, N, hA, hB, hJ⟩ := exists_norm_integral_expDetIntegrand_le
  obtain ⟨Cr, Nr, hCr, hr⟩ := exists_norm_expDetZetaResidue_le
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = 2 * ((N : ℝ) + 2) := ⟨_, rfl⟩
  have ev1 : ∀ᶠ T : ℝ in atTop, 6 ≤ Real.log T := Real.tendsto_log_atTop.eventually_ge_atTop 6
  have ev2 : ∀ᶠ T : ℝ in atTop,
      Cr * 2 ^ Nr * T ^ (Nr + 2) * Real.exp (-(Real.pi * T / 2)) ≤ 1 / 8 :=
    (tendsto_const_mul_pow_mul_exp_neg_pi (Cr * 2 ^ Nr) (Nr + 2)).eventually
      (ge_mem_nhds (by norm_num))
  have ev3 := eventually_const_mul_rpow_neg_le_one A (show (0 : ℝ) < 1 / 20 by norm_num)
  have ev4 := eventually_const_mul_rpow_neg_le_one (B * 3 ^ N)
    (show (0 : ℝ) < 59 / 30 by norm_num)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (ev1.and (ev2.and (ev3.and (ev4.and (eventually_ge_atTop (1 : ℝ))))))
  refine ⟨K₀, 1 / (A + 1), T₀, by positivity, by rw [hK₀]; positivity,
    (hT₀ T₀ le_rfl).2.2.2.2, fun T hT ρ hρ hβ1 hβ2 hγ1 hγ2 => ?_⟩
  obtain ⟨hlog, hres_small, hA_small, hB_small, hT1⟩ := hT₀ T hT
  have hT0 : 0 < T := by linarith
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ, X = expDetMoll T := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = expDetSmooth T := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = K₀ * Real.log T := ⟨_, rfl⟩
  rw [← hXdef, ← hYdef, ← hLdef]
  have hX1 : 1 ≤ X := hXdef ▸ one_le_expDetMoll hT1
  have hXle : (X : ℝ) ≤ T ^ (1 / 30 : ℝ) := hXdef ▸ expDetMoll_le hT1
  have hY1 : 1 ≤ Y := hYdef ▸ one_le_expDetSmooth hT1
  have hY0 : 0 < Y := by linarith
  have hYT : Y = T ^ (3 / 5 : ℝ) := hYdef
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hL0 : 0 ≤ L := by rw [hLdef, hK₀]; positivity
  set γ := ρ.im with hγ
  have hγ0 : 0 < γ := by linarith
  set c : ℝ := 1 / 2 - ρ.re with hc
  -- the detector identity and its three error terms
  have hid := tsum_moebiusZetaDefect_exp_eq X hX1 hρ (by linarith) hβ2 hY1 (c := c)
    (by rw [hc]; linarith) (by rw [hc]; linarith)
  have htail := (summable_expDetTerm_and_tail_le hX1 (by linarith) hY0 (expDetCut T)).2
  have htail' : ‖(∑' n, expDetTerm X ρ Y n) -
      ∑ n ∈ Finset.range (expDetCut T + 1), expDetTerm X ρ Y n‖ ≤ 1 / 8 := by
    refine le_trans htail ?_
    rw [hYdef]
    exact expDet_tail_small hT1 hlog
  have hres : ‖expDetZetaResidue X ρ Y‖ ≤ 1 / 8 := by
    have h := hr X ρ Y (by linarith) hβ2 (by rw [← hγ, abs_of_pos hγ0]; linarith) hY1
    rw [← hγ, abs_of_pos hγ0] at h
    refine le_trans h (le_trans ?_ hres_small)
    have hXT : (X : ℝ) ≤ T := le_trans hXle (by
      calc T ^ (1 / 30 : ℝ) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
        _ = T := Real.rpow_one T)
    have hYT' : Y ≤ T := by
      rw [hYT]
      calc T ^ (3 / 5 : ℝ) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
        _ = T := Real.rpow_one T
    have hγpow : γ ^ Nr ≤ (2 * T) ^ Nr := pow_le_pow_left₀ hγ0.le hγ2 Nr
    have hexp : Real.exp (-(Real.pi * γ / 2)) ≤ Real.exp (-(Real.pi * T / 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    calc (X : ℝ) * Y * (Cr * γ ^ Nr * Real.exp (-(Real.pi * γ / 2)))
        ≤ T * T * (Cr * (2 * T) ^ Nr * Real.exp (-(Real.pi * T / 2))) := by
          gcongr
      _ = Cr * 2 ^ Nr * T ^ (Nr + 2) * Real.exp (-(Real.pi * T / 2)) := by ring
  -- the line integral
  have hJb := hJ X ρ Y L hβ1 hβ2.le hY1 hL0
  rw [← hc] at hJb
  set Ig : ℝ := ∫ y in (-L)..L, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((γ + y : ℝ) : ℂ) * I)‖
    with hIg
  have hIg0 : 0 ≤ Ig := intervalIntegral.integral_nonneg (by linarith) fun y _ => norm_nonneg _
  have hYc : Y ^ c ≤ T ^ (-(1 / 20 : ℝ)) := by
    rw [hYT, ← Real.rpow_mul hT0.le]
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by rw [hc]; linarith)
  have hYc0 : 0 ≤ Y ^ c := Real.rpow_nonneg hY0.le _
  have hYc1 : Y ^ c ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY1 (by rw [hc]; linarith)
  have hJA : Y ^ c * A ≤ 1 := by
    calc Y ^ c * A ≤ T ^ (-(1 / 20 : ℝ)) * A := mul_le_mul_of_nonneg_right hYc hA
      _ = A * T ^ (-(1 / 20 : ℝ)) := by ring
      _ ≤ 1 := hA_small
  have hJB : Y ^ c * (X * B * (1 + |γ|) ^ N * Real.exp (-(L / 2))) ≤ 1 := by
    have hexpL : Real.exp (-(L / 2)) = T ^ (-((N : ℝ) + 2)) := by
      rw [Real.rpow_def_of_pos hT0, hLdef, hK₀]
      congr 1
      ring
    have hγ3 : (1 + |γ|) ^ N ≤ (3 * T) ^ N := by
      apply pow_le_pow_left₀ (by positivity)
      rw [abs_of_pos hγ0]
      linarith
    have hpow : T ^ (1 / 30 : ℝ) * (3 * T) ^ N * T ^ (-((N : ℝ) + 2)) =
        3 ^ N * T ^ (-(59 / 30 : ℝ)) := by
      rw [mul_pow, ← Real.rpow_natCast T N]
      have e : T ^ (1 / 30 : ℝ) * (3 ^ N * T ^ (N : ℝ)) * T ^ (-((N : ℝ) + 2)) =
          3 ^ N * (T ^ (1 / 30 : ℝ) * T ^ (N : ℝ) * T ^ (-((N : ℝ) + 2))) := by ring
      rw [e, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
      congr 2
      ring
    calc Y ^ c * (X * B * (1 + |γ|) ^ N * Real.exp (-(L / 2)))
        ≤ 1 * (T ^ (1 / 30 : ℝ) * B * (3 * T) ^ N * T ^ (-((N : ℝ) + 2))) := by
          rw [hexpL]
          gcongr
      _ = B * 3 ^ N * T ^ (-(59 / 30 : ℝ)) := by
          rw [one_mul]
          have := hpow
          calc T ^ (1 / 30 : ℝ) * B * (3 * T) ^ N * T ^ (-((N : ℝ) + 2))
              = B * (T ^ (1 / 30 : ℝ) * (3 * T) ^ N * T ^ (-((N : ℝ) + 2))) := by ring
            _ = B * (3 ^ N * T ^ (-(59 / 30 : ℝ))) := by rw [hpow]
            _ = B * 3 ^ N * T ^ (-(59 / 30 : ℝ)) := by ring
      _ ≤ 1 := hB_small
  -- the dichotomy
  by_cases hP : 1 / 8 ≤ ‖∑ n ∈ Finset.range (expDetCut T + 1), expDetTerm X ρ Y n‖
  · exact Or.inl hP
  right
  push Not at hP
  obtain ⟨J, hJdef⟩ : ∃ J : ℂ,
      J = ∫ y : ℝ, expDetIntegrand X ρ Y ((c : ℂ) + (y : ℂ) * I) := ⟨_, rfl⟩
  rw [← hJdef] at hid hJb
  obtain ⟨P, hPdef⟩ : ∃ P : ℂ,
      P = ∑ n ∈ Finset.range (expDetCut T + 1), expDetTerm X ρ Y n := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℂ, S = ∑' n, expDetTerm X ρ Y n := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℂ, R = expDetZetaResidue X ρ Y := ⟨_, rfl⟩
  rw [← hPdef] at hP htail'
  rw [← hSdef] at htail'
  rw [← hRdef] at hres
  have hS : S = 1 + R + ((1 / (2 * Real.pi) : ℝ) : ℂ) * J := by
    rw [hSdef, hRdef]
    simpa only [expDetTerm] using hid
  have hone : (1 : ℂ) = P + (S - P) - R - ((1 / (2 * Real.pi) : ℝ) : ℂ) * J := by
    rw [hS]; ring
  have hkey : ‖P + (S - P) - R - ((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖ ≤
      ‖P‖ + ‖S - P‖ + ‖R‖ + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖ := by
    calc ‖P + (S - P) - R - ((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖
        ≤ ‖P + (S - P) - R‖ + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖ := norm_sub_le _ _
      _ ≤ (‖P + (S - P)‖ + ‖R‖) + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ((‖P‖ + ‖S - P‖) + ‖R‖) + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖ := by
          gcongr; exact norm_add_le _ _
  have hJn : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖ = (1 / (2 * Real.pi)) * ‖J‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hnorm1 : (1 : ℝ) ≤ ‖P‖ + 1 / 8 + 1 / 8 + (1 / (2 * Real.pi)) * ‖J‖ := by
    have h := congrArg norm hone
    rw [norm_one] at h
    refine le_trans h.le (le_trans hkey ?_)
    rw [hJn]
    linarith only [htail', hres]
  have hJbig : 3 ≤ ‖J‖ := by
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have h1 : 5 / 8 ≤ (1 / (2 * Real.pi)) * ‖J‖ := by linarith only [hnorm1, hP]
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h1
    linarith only [h1, Real.pi_gt_three]
  -- extract the critical-line integral
  have hmain : 1 ≤ Y ^ c * (X * A * Ig) := by
    have h := le_trans hJbig hJb
    have e : Y ^ c * (A + X * A * Ig + X * B * (1 + |γ|) ^ N * Real.exp (-(L / 2))) =
        Y ^ c * A + Y ^ c * (X * A * Ig) +
          Y ^ c * (X * B * (1 + |γ|) ^ N * Real.exp (-(L / 2))) := by ring
    rw [e] at h
    linarith only [h, hJA, hJB]
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  have hYneg : Y ^ (ρ.re - 1 / 2) * Y ^ c = 1 := by
    rw [← Real.rpow_add hY0, hc]
    simp
  rw [div_le_iff₀ hX0]
  have hYpos : 0 < Y ^ (ρ.re - 1 / 2) := Real.rpow_pos_of_pos hY0 _
  calc 1 / (A + 1) * Y ^ (ρ.re - 1 / 2) = 1 / (A + 1) * Y ^ (ρ.re - 1 / 2) * 1 := by ring
    _ ≤ 1 / (A + 1) * Y ^ (ρ.re - 1 / 2) * (Y ^ c * (X * (A + 1) * Ig)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : Y ^ c * (X * A * Ig) ≤ Y ^ c * (X * (A + 1) * Ig) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith only) hX0.le) hIg0) hYc0
        exact le_trans hmain this
    _ = (Y ^ (ρ.re - 1 / 2) * Y ^ c) * (Ig * X) := by field_simp
    _ = Ig * X := by rw [hYneg, one_mul]

end RHTower
