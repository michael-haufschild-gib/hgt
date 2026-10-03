import GaloisForLFunctions.RHTower.ZetaZeroExponentialDetectorDichotomy

/-!
# The Type I / Type II dichotomy for general mollifier and smoothing lengths

At height `T` put `X = ⌊T^δ⌋`, `Y = T^y` and `Z = ⌊T^y (log T)²⌋` with `0 < δ ≤ 1`,
`0 < y ≤ 1`.  For every `σ₁ ≥ 7/12` there are constants `K₀, c₀ > 0` such that for all large `T`
every zero `ρ = β + iγ` of `ζ` with `σ₁ ≤ β < 1` and `T ≤ γ ≤ 2T` satisfies

* (Type I) `|Σ_{n ≤ Z} D(n) n^{-ρ} e^{-n/Y}| ≥ 1/8`, or
* (Type II) `∫_{|t| ≤ K₀ log T} |ζ(1/2 + i(γ + t))| dt ≥ c₀ Y^{β - 1/2} / X`.

The proof is that of `exists_expDetector_dichotomy`: the detector identity on `Re w = 1/2 - β`,
the tail beyond `Z` (`≤ 4Y² e^{-Z/2Y} ≤ 8 T^{-1}`), the residue (`≤ T^{N+2} e^{-πT/2}`) and the
line integral, whose error terms are `≤ A T^{-y(σ₁ - 1/2)}` and `≤ B 3^N T^{δ - 2}`.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set

/-- The mollifier length `⌊T^δ⌋`. -/
def pDetMoll (δ T : ℝ) : ℕ := ⌊T ^ δ⌋₊

/-- The smoothing length `T^y`. -/
def pDetSmooth (y T : ℝ) : ℝ := T ^ y

/-- The cutoff `⌊T^y (log T)²⌋`. -/
def pDetCut (y T : ℝ) : ℕ := ⌊T ^ y * Real.log T ^ 2⌋₊

theorem one_le_pDetMoll {δ T : ℝ} (hδ : 0 ≤ δ) (hT : 1 ≤ T) : 1 ≤ pDetMoll δ T := by
  unfold pDetMoll
  exact Nat.le_floor (by simpa using Real.one_le_rpow hT hδ)

theorem pDetMoll_le {δ T : ℝ} (hT : 1 ≤ T) : (pDetMoll δ T : ℝ) ≤ T ^ δ :=
  Nat.floor_le (Real.rpow_nonneg (by linarith) _)

theorem one_le_pDetSmooth {y T : ℝ} (hy : 0 ≤ y) (hT : 1 ≤ T) : 1 ≤ pDetSmooth y T :=
  Real.one_le_rpow hT hy

/-- The tail bound: `4Y² e^{-Z/(2Y)} ≤ 1/8` for `y ≤ 1` once `log T ≥ 6`. -/
theorem pDet_tail_small {y T : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hT1 : 1 ≤ T)
    (hT : 6 ≤ Real.log T) :
    4 * pDetSmooth y T ^ 2 * Real.exp (-((pDetCut y T : ℝ) / (2 * pDetSmooth y T))) ≤ 1 / 8 := by
  have hT0 : 0 < T := by linarith
  have hZ' : T ^ y * Real.log T ^ 2 - 1 ≤ (pDetCut y T : ℝ) := by
    have := Nat.lt_floor_add_one (T ^ y * Real.log T ^ 2)
    unfold pDetCut
    linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = pDetSmooth y T := ⟨_, rfl⟩
  rw [← hY]
  have hYT : Y = T ^ y := hY
  have hY1 : 1 ≤ Y := hY ▸ one_le_pDetSmooth hy0 hT1
  have hY0 : 0 < Y := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log T := ⟨_, rfl⟩
  rw [← hℓ] at hT hZ'
  rw [← hYT] at hZ'
  have hratio : ℓ ^ 2 / 2 - 1 / 2 ≤ (pDetCut y T : ℝ) / (2 * Y) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hexp : Real.exp (-((pDetCut y T : ℝ) / (2 * Y))) ≤ Real.exp (1 / 2) * T ^ (-(3 : ℝ)) := by
    rw [Real.rpow_def_of_pos hT0, ← Real.exp_add, ← hℓ]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hYle : Y ≤ T := by
    rw [hYT]
    calc T ^ y ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 hy1
      _ = T := Real.rpow_one T
  have hY2 : Y ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hY0.le hYle 2
  have hTpow : T ^ 2 * T ^ (-(3 : ℝ)) = T ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hT0]
    norm_num
  have he : Real.exp (1 / 2) ≤ 2 := by
    have := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hTbig : 403 ≤ T := by
    have : Real.exp 6 ≤ T := by rw [← Real.exp_log hT0, ← hℓ]; exact Real.exp_le_exp.mpr hT
    have he6 : (403 : ℝ) ≤ Real.exp 6 := by
      have h1 := Real.exp_one_gt_d9
      have : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) h1.le 6]
    linarith
  have hTneg : T ^ (-(1 : ℝ)) ≤ 1 / 64 := by
    rw [Real.rpow_neg hT0.le, Real.rpow_one, inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  calc 4 * Y ^ 2 * Real.exp (-((pDetCut y T : ℝ) / (2 * Y)))
      ≤ 4 * T ^ 2 * (Real.exp (1 / 2) * T ^ (-(3 : ℝ))) := by
        gcongr
    _ = 4 * Real.exp (1 / 2) * (T ^ 2 * T ^ (-(3 : ℝ))) := by ring
    _ = 4 * Real.exp (1 / 2) * T ^ (-(1 : ℝ)) := by rw [hTpow]
    _ ≤ 4 * 2 * (1 / 64) := by gcongr
    _ = 1 / 8 := by norm_num

/-- **The Type I / Type II dichotomy for general lengths.** -/
theorem exists_pDetector_dichotomy {δ y σ₁ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hy0 : 0 < y)
    (hy1 : y ≤ 1) (hσ₁ : 7 / 12 ≤ σ₁) :
    ∃ (K₀ c₀ T₀ : ℝ), 0 < c₀ ∧ 0 ≤ K₀ ∧ 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ ρ : ℂ,
      riemannZeta ρ = 0 → σ₁ ≤ ρ.re → ρ.re < 1 → T ≤ ρ.im → ρ.im ≤ 2 * T →
      1 / 8 ≤ ‖∑ n ∈ Finset.range (pDetCut y T + 1),
          expDetTerm (pDetMoll δ T) ρ (pDetSmooth y T) n‖ ∨
      c₀ * pDetSmooth y T ^ (ρ.re - 1 / 2) / pDetMoll δ T ≤
        ∫ t in (-(K₀ * Real.log T))..(K₀ * Real.log T),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)‖ := by
  obtain ⟨A, B, N, hA, hB, hJ⟩ := exists_norm_integral_expDetIntegrand_le
  obtain ⟨Cr, Nr, hCr, hr⟩ := exists_norm_expDetZetaResidue_le
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = 2 * ((N : ℝ) + 2) := ⟨_, rfl⟩
  set e : ℝ := y * (σ₁ - 1 / 2) with he
  have he0 : 0 < e := by rw [he]; exact mul_pos hy0 (by linarith)
  have ev1 : ∀ᶠ T : ℝ in atTop, 6 ≤ Real.log T := Real.tendsto_log_atTop.eventually_ge_atTop 6
  have ev2 : ∀ᶠ T : ℝ in atTop,
      Cr * 2 ^ Nr * T ^ (Nr + 2) * Real.exp (-(Real.pi * T / 2)) ≤ 1 / 8 :=
    (tendsto_const_mul_pow_mul_exp_neg_pi (Cr * 2 ^ Nr) (Nr + 2)).eventually
      (ge_mem_nhds (by norm_num))
  have ev3 := eventually_const_mul_rpow_neg_le_one A he0
  have ev4 := eventually_const_mul_rpow_neg_le_one (B * 3 ^ N) (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (ev1.and (ev2.and (ev3.and (ev4.and (eventually_ge_atTop (1 : ℝ))))))
  refine ⟨K₀, 1 / (A + 1), T₀, by positivity, by rw [hK₀]; positivity,
    (hT₀ T₀ le_rfl).2.2.2.2, fun T hT ρ hρ hβ1 hβ2 hγ1 hγ2 => ?_⟩
  obtain ⟨hlog, hres_small, hA_small, hB_small, hT1⟩ := hT₀ T hT
  have hT0 : 0 < T := by linarith
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ, X = pDetMoll δ T := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = pDetSmooth y T := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = K₀ * Real.log T := ⟨_, rfl⟩
  rw [← hXdef, ← hYdef, ← hLdef]
  have hX1 : 1 ≤ X := hXdef ▸ one_le_pDetMoll hδ0.le hT1
  have hXle : (X : ℝ) ≤ T ^ δ := hXdef ▸ pDetMoll_le hT1
  have hY1 : 1 ≤ Y := hYdef ▸ one_le_pDetSmooth hy0.le hT1
  have hY0 : 0 < Y := by linarith
  have hYT : Y = T ^ y := hYdef
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hL0 : 0 ≤ L := by rw [hLdef, hK₀]; positivity
  set γ := ρ.im with hγ
  have hγ0 : 0 < γ := by linarith
  set c : ℝ := 1 / 2 - ρ.re with hc
  have hid := tsum_moebiusZetaDefect_exp_eq X hX1 hρ (by linarith) hβ2 hY1 (c := c)
    (by rw [hc]; linarith) (by rw [hc]; linarith)
  have htail := (summable_expDetTerm_and_tail_le hX1 (by linarith) hY0 (pDetCut y T)).2
  have htail' : ‖(∑' n, expDetTerm X ρ Y n) -
      ∑ n ∈ Finset.range (pDetCut y T + 1), expDetTerm X ρ Y n‖ ≤ 1 / 8 := by
    refine le_trans htail ?_
    rw [hYdef]
    exact pDet_tail_small hy0.le hy1 hT1 hlog
  have hXT : (X : ℝ) ≤ T := le_trans hXle (by
    calc T ^ δ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 hδ1
      _ = T := Real.rpow_one T)
  have hYT' : Y ≤ T := by
    rw [hYT]
    calc T ^ y ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 hy1
      _ = T := Real.rpow_one T
  have hres : ‖expDetZetaResidue X ρ Y‖ ≤ 1 / 8 := by
    have h := hr X ρ Y (by linarith) hβ2 (by rw [← hγ, abs_of_pos hγ0]; linarith) hY1
    rw [← hγ, abs_of_pos hγ0] at h
    refine le_trans h (le_trans ?_ hres_small)
    have hγpow : γ ^ Nr ≤ (2 * T) ^ Nr := pow_le_pow_left₀ hγ0.le hγ2 Nr
    have hexp : Real.exp (-(Real.pi * γ / 2)) ≤ Real.exp (-(Real.pi * T / 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    calc (X : ℝ) * Y * (Cr * γ ^ Nr * Real.exp (-(Real.pi * γ / 2)))
        ≤ T * T * (Cr * (2 * T) ^ Nr * Real.exp (-(Real.pi * T / 2))) := by
          gcongr
      _ = Cr * 2 ^ Nr * T ^ (Nr + 2) * Real.exp (-(Real.pi * T / 2)) := by ring
  have hJb := hJ X ρ Y L (le_trans hσ₁ hβ1) hβ2.le hY1 hL0
  rw [← hc] at hJb
  set Ig : ℝ := ∫ t in (-L)..L, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((γ + t : ℝ) : ℂ) * I)‖
    with hIg
  have hIg0 : 0 ≤ Ig := intervalIntegral.integral_nonneg (by linarith) fun t _ => norm_nonneg _
  have hYc : Y ^ c ≤ T ^ (-e) := by
    rw [hYT, ← Real.rpow_mul hT0.le]
    apply Real.rpow_le_rpow_of_exponent_le hT1
    rw [he, hc]
    nlinarith
  have hYc0 : 0 ≤ Y ^ c := Real.rpow_nonneg hY0.le _
  have hJA : Y ^ c * A ≤ 1 := by
    calc Y ^ c * A ≤ T ^ (-e) * A := mul_le_mul_of_nonneg_right hYc hA
      _ = A * T ^ (-e) := by ring
      _ ≤ 1 := hA_small
  have hYc1 : Y ^ c ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY1 (by rw [hc]; linarith)
  have hJB : Y ^ c * (X * B * (1 + |γ|) ^ N * Real.exp (-(L / 2))) ≤ 1 := by
    have hexpL : Real.exp (-(L / 2)) = T ^ (-((N : ℝ) + 2)) := by
      rw [Real.rpow_def_of_pos hT0, hLdef, hK₀]
      congr 1
      ring
    have hγ3 : (1 + |γ|) ^ N ≤ (3 * T) ^ N := by
      apply pow_le_pow_left₀ (by positivity)
      rw [abs_of_pos hγ0]
      linarith
    have hpow : T * (3 * T) ^ N * T ^ (-((N : ℝ) + 2)) = 3 ^ N * T ^ (-(1 : ℝ)) := by
      rw [mul_pow, ← Real.rpow_natCast T N]
      have e' : T * (3 ^ N * T ^ (N : ℝ)) * T ^ (-((N : ℝ) + 2)) =
          3 ^ N * (T ^ (1 : ℝ) * T ^ (N : ℝ) * T ^ (-((N : ℝ) + 2))) := by
        rw [Real.rpow_one]; ring
      rw [e', ← Real.rpow_add hT0, ← Real.rpow_add hT0]
      congr 2
      ring
    calc Y ^ c * (X * B * (1 + |γ|) ^ N * Real.exp (-(L / 2)))
        ≤ 1 * (T * B * (3 * T) ^ N * T ^ (-((N : ℝ) + 2))) := by
          rw [hexpL]
          gcongr
      _ = B * 3 ^ N * T ^ (-(1 : ℝ)) := by
          rw [one_mul]
          calc T * B * (3 * T) ^ N * T ^ (-((N : ℝ) + 2))
              = B * (T * (3 * T) ^ N * T ^ (-((N : ℝ) + 2))) := by ring
            _ = B * (3 ^ N * T ^ (-(1 : ℝ))) := by rw [hpow]
            _ = B * 3 ^ N * T ^ (-(1 : ℝ)) := by ring
      _ ≤ 1 := hB_small
  -- the dichotomy
  by_cases hP : 1 / 8 ≤ ‖∑ n ∈ Finset.range (pDetCut y T + 1), expDetTerm X ρ Y n‖
  · exact Or.inl hP
  right
  push Not at hP
  obtain ⟨J, hJdef⟩ : ∃ J : ℂ,
      J = ∫ y : ℝ, expDetIntegrand X ρ Y ((c : ℂ) + (y : ℂ) * I) := ⟨_, rfl⟩
  rw [← hJdef] at hid hJb
  obtain ⟨P, hPdef⟩ : ∃ P : ℂ,
      P = ∑ n ∈ Finset.range (pDetCut y T + 1), expDetTerm X ρ Y n := ⟨_, rfl⟩
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
