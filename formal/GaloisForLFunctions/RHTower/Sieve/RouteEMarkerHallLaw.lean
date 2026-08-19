import GaloisForLFunctions.RHTower.Sieve.FreeScaleCover
import GaloisForLFunctions.RHTower.Sieve.CardLengthGap
import GaloisForLFunctions.RHTower.Sieve.ConstQuotientLimit
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowBrunTitchmarsh

/-!
# The reciprocal-marker Möbius Hall law

For every exponent `9/10 < β < 1`, every sign `σ ∈ {±1}` and every constant `C`, the window
`(Z, Z + H]` with `H = ⌈√Z·exp((log Z)^β)⌉` contains at least `C·H/log Z` integers with `μ = σ`,
for all sufficiently large `Z`.  The tile length of the marker construction is
`≍ √(Z log Z)·exp((log Z)^{β₀})` for an auxiliary `β₀ < β`, hence far below `H`; the window is
covered by such tiles and the counts add.
-/

namespace RHTower.Sieve

open Finset Filter ArithmeticFunction

noncomputable section

/-- The net harmonic mass of the marker family is unbounded in the number of blocks. -/
theorem exists_multiHarmConst_ge (B : ℝ) : ∃ K₀ : ℕ, B ≤ multiHarmConst K₀ := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := 2 * (2 * mertensFirstConst + 1 / 2) with hc
  refine ⟨⌈2 * (B + c) / Real.log 2⌉₊, ?_⟩
  have hceil : 2 * (B + c) / Real.log 2 ≤ (⌈2 * (B + c) / Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
  have hstep : 2 * (B + c) ≤ (⌈2 * (B + c) / Real.log 2⌉₊ : ℝ) * Real.log 2 := by
    rw [div_le_iff₀ hlog2] at hceil
    exact hceil
  rw [multiHarmConst, ← hc]
  nlinarith [hstep, hlog2]

/-- **The tile length against the physical scale.** -/
theorem tileLen_le_bound {β : ℝ} {K₀ u Z : ℕ} (hβ : 0 < β) (hpos : 0 < tileBase K₀ u)
    (hZ : tileBase K₀ u ≤ Z) :
    ((tileLen β K₀ u : ℕ) : ℝ)
      ≤ (2 * cardLength β (Z : ℝ) + (2 : ℝ) ^ (K₀ + 1))
          * (2 * Real.sqrt ((Z : ℝ) * Real.log (Z : ℝ))) + 1 := by
  set m : ℕ := tileM K₀ u with hm
  set T : ℕ := tileLog K₀ u with hT
  have hPeq : tileBase K₀ u = m * m * T := by rw [tileBase, ← hm, ← hT]
  have hm0 : 0 < m := by
    by_contra hcon
    have : m = 0 := by omega
    rw [hPeq, this] at hpos
    simp at hpos
  have hT0 : 0 < T := by
    by_contra hcon
    have : T = 0 := by omega
    rw [hPeq, this] at hpos
    simp at hpos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
  have hTR : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT0
  -- the physical scale dominates the modulus and its square
  have hmsq : m * m ≤ Z := le_trans (by nlinarith [hT0, hm0]) (hPeq ▸ hZ)
  have hmZ : m ≤ Z := le_trans (by nlinarith [hm0]) hmsq
  have hZ1 : 1 ≤ Z := le_trans hm0 hmZ
  have hZR : (1 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ1
  have hZR0 : (0 : ℝ) < (Z : ℝ) := by linarith
  have hmsqR : ((m : ℝ)) * (m : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hmsq
  have hlogZ0 : (0 : ℝ) ≤ Real.log (Z : ℝ) := Real.log_nonneg hZR
  -- the window of the tile is below the window of the scale
  have hCle : tileC β K₀ u ≤ cardLength β (Z : ℝ) := by
    rw [tileC, freeScale_zero, ← hm]
    refine cardLength_mono hβ ?_ ?_
    · nlinarith [hm1R]
    · nlinarith [hmsqR]
  -- the integer logarithm is below the logarithm of the scale
  have hTlog : (T : ℝ) ≤ Real.log (Z : ℝ) := by
    have h1 : (T : ℝ) ≤ Real.log ((m : ℕ) : ℝ) := by rw [hT, hm]; exact tileLog_le (by
      by_contra hcon
      have : u = 0 := by omega
      rw [hm, tileM, this] at hm0
      simp at hm0)
    have h2 : Real.log ((m : ℕ) : ℝ) ≤ Real.log (Z : ℝ) :=
      Real.log_le_log hmR (by exact_mod_cast hmZ)
    linarith
  -- the product `m·T` is below `√(Z log Z)`
  have hmT : (m : ℝ) * (T : ℝ) ≤ Real.sqrt ((Z : ℝ) * Real.log (Z : ℝ)) := by
    have hsq : ((m : ℝ) * (T : ℝ)) ^ 2 ≤ (Z : ℝ) * Real.log (Z : ℝ) := by
      have hPR : ((m : ℝ) * (m : ℝ)) * (T : ℝ) ≤ (Z : ℝ) := by
        have : ((tileBase K₀ u : ℕ) : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ
        rw [hPeq] at this
        push_cast at this
        linarith
      nlinarith [hPR, hTlog, hTR, hmR, hlogZ0]
    have hnn : (0 : ℝ) ≤ (m : ℝ) * (T : ℝ) := by positivity
    calc (m : ℝ) * (T : ℝ) = Real.sqrt (((m : ℝ) * (T : ℝ)) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((Z : ℝ) * Real.log (Z : ℝ)) := Real.sqrt_le_sqrt hsq
  -- the ceiling
  have hCpos : (0 : ℝ) < tileC β K₀ u := tileC_pos β K₀ u
  have hcoef : (0 : ℝ) < 2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1) := by positivity
  have hval : (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1))
        * (2 * ((tileBase K₀ u : ℕ) : ℝ)) / ((tileM K₀ u : ℕ) : ℝ)
      = (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1)) * (2 * ((m : ℝ) * (T : ℝ))) := by
    rw [hPeq, ← hm]
    push_cast
    field_simp
    try ring
  have hceil : ((tileLen β K₀ u : ℕ) : ℝ)
      ≤ (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1)) * (2 * ((m : ℝ) * (T : ℝ))) + 1 := by
    rw [tileLen, hval]
    have hmT0 : (0 : ℝ) ≤ 2 * ((m : ℝ) * (T : ℝ)) := by positivity
    have hnn : (0 : ℝ) ≤ (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1)) * (2 * ((m : ℝ) * (T : ℝ))) :=
      mul_nonneg hcoef.le hmT0
    linarith [Nat.ceil_lt_add_one hnn]
  refine hceil.trans ?_
  have hsq0 : (0 : ℝ) ≤ Real.sqrt ((Z : ℝ) * Real.log (Z : ℝ)) := Real.sqrt_nonneg _
  have hmono : (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1)) * (2 * ((m : ℝ) * (T : ℝ)))
      ≤ (2 * cardLength β (Z : ℝ) + (2 : ℝ) ^ (K₀ + 1))
        * (2 * Real.sqrt ((Z : ℝ) * Real.log (Z : ℝ))) := by
    have h1 : (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1))
        ≤ 2 * cardLength β (Z : ℝ) + (2 : ℝ) ^ (K₀ + 1) := by linarith [hCle]
    have h2 : (2 : ℝ) * ((m : ℝ) * (T : ℝ)) ≤ 2 * Real.sqrt ((Z : ℝ) * Real.log (Z : ℝ)) := by
      linarith [hmT]
    have h3 : (0 : ℝ) ≤ 2 * ((m : ℝ) * (T : ℝ)) := by positivity
    exact mul_le_mul h1 h2 h3 (by linarith [hCle, hCpos])
  linarith

theorem one_le_cardLength {β y : ℝ} (hy : 1 ≤ y) : 1 ≤ cardLength β y := by
  rw [cardLength]
  exact Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg hy) _)

/-- **Twice the tile length fits inside the prescribed window.** -/
theorem eventually_two_tileLen_le {β β' : ℝ} (hβ0 : 1 / 2 < β) (hββ' : β < β') (K₀ : ℕ) :
    ∀ᶠ Z : ℕ in atTop, ∀ u : ℕ, 0 < tileBase K₀ u → tileBase K₀ u ≤ Z →
      2 * ((tileLen β K₀ u : ℕ) : ℝ)
        ≤ ((⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ : ℕ) : ℝ) := by
  have hβpos : (0 : ℝ) < β := by linarith
  have hgap := eventually_cardLength_gap (β := β) (β' := β')
    (a := 8 + (2 : ℝ) ^ (K₀ + 3)) (b := 2) hβ0 hββ' (by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hgap,
    eventually_ge_atTop 1] with Z hZgap hZ1
  intro u hpos hZ
  have hZR : (1 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ1
  have hZR0 : (0 : ℝ) < (Z : ℝ) := by linarith
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (Z : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hZR
  have hlogZ0 : (0 : ℝ) ≤ Real.log (Z : ℝ) := Real.log_nonneg hZR
  have hCZ : (1 : ℝ) ≤ cardLength β (Z : ℝ) := one_le_cardLength hZR
  have hsplit : Real.sqrt ((Z : ℝ) * Real.log (Z : ℝ))
      = Real.sqrt (Z : ℝ) * Real.sqrt (Real.log (Z : ℝ)) := Real.sqrt_mul hZR0.le _
  have hbound := tileLen_le_bound (β := β) (K₀ := K₀) (u := u) (Z := Z) hβpos hpos hZ
  have hceilge : Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)
      ≤ ((⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  refine le_trans ?_ hceilge
  -- expand the doubled bound
  have hstep1 : 2 * ((tileLen β K₀ u : ℕ) : ℝ)
      ≤ (8 * cardLength β (Z : ℝ) + (2 : ℝ) ^ (K₀ + 3))
          * (Real.sqrt (Z : ℝ) * Real.sqrt (Real.log (Z : ℝ))) + 2 := by
    have hpow : (2 : ℝ) ^ (K₀ + 3) = 4 * (2 : ℝ) ^ (K₀ + 1) := by
      rw [show K₀ + 3 = (K₀ + 1) + 2 by ring, pow_add]; ring
    rw [hsplit] at hbound
    rw [hpow]
    nlinarith [hbound]
  refine hstep1.trans ?_
  -- absorb the constant into the window
  have habs : 8 * cardLength β (Z : ℝ) + (2 : ℝ) ^ (K₀ + 3)
      ≤ (8 + (2 : ℝ) ^ (K₀ + 3)) * cardLength β (Z : ℝ) := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ (K₀ + 3) := by positivity
    nlinarith [hCZ, hp]
  have hsqlog0 : (0 : ℝ) ≤ Real.sqrt (Real.log (Z : ℝ)) := Real.sqrt_nonneg _
  have hstep2 : (8 * cardLength β (Z : ℝ) + (2 : ℝ) ^ (K₀ + 3))
        * (Real.sqrt (Z : ℝ) * Real.sqrt (Real.log (Z : ℝ))) + 2
      ≤ Real.sqrt (Z : ℝ)
        * ((8 + (2 : ℝ) ^ (K₀ + 3)) * cardLength β (Z : ℝ) * Real.sqrt (Real.log (Z : ℝ)) + 2) := by
    have hmul : (8 * cardLength β (Z : ℝ) + (2 : ℝ) ^ (K₀ + 3))
          * (Real.sqrt (Z : ℝ) * Real.sqrt (Real.log (Z : ℝ)))
        ≤ ((8 + (2 : ℝ) ^ (K₀ + 3)) * cardLength β (Z : ℝ))
          * (Real.sqrt (Z : ℝ) * Real.sqrt (Real.log (Z : ℝ))) := by
      refine mul_le_mul_of_nonneg_right habs ?_
      positivity
    nlinarith [hmul, hsq1]
  refine hstep2.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith [hsq1])
  exact hZgap

/-- **The prescribed window is a small fraction of the scale.** -/
theorem eventually_three_mul_ceil_le {β' : ℝ} (hβ'0 : 0 < β') (hβ'1 : β' < 1) :
    ∀ᶠ Z : ℕ in atTop, 3 * ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ ≤ Z := by
  have hlim := tendsto_cardLength_div_sqrt (β := β') hβ'0 hβ'1
  have hev : ∀ᶠ y : ℝ in atTop, cardLength β' y ≤ Real.sqrt y / 6 := by
    filter_upwards [hlim.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 6 by norm_num)),
      eventually_ge_atTop (1 : ℝ)] with y hy hy1
    have hy0 : (0 : ℝ) < y := by linarith
    have hs0 : (0 : ℝ) < Real.sqrt y := Real.sqrt_pos.2 hy0
    rw [div_le_iff₀ hs0] at hy
    linarith [hy]
  have hev36 : ∀ᶠ y : ℝ in atTop, (36 : ℝ) ≤ y := eventually_ge_atTop _
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hev,
    tendsto_natCast_atTop_atTop.eventually hev36] with Z hZ hZ36
  have hZR0 : (0 : ℝ) < (Z : ℝ) := by linarith
  have hsq6 : (6 : ℝ) ≤ Real.sqrt (Z : ℝ) := by
    rw [show (6 : ℝ) = Real.sqrt 36 by
      rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hZ36
  have hsqsq : Real.sqrt (Z : ℝ) * Real.sqrt (Z : ℝ) = (Z : ℝ) :=
    Real.mul_self_sqrt hZR0.le
  have hnn : (0 : ℝ) ≤ Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ) := by
    have := cardLength_pos β' (Z : ℝ)
    positivity
  have hceil : ((⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ : ℕ) : ℝ)
      ≤ Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ) + 1 := by
    linarith [Nat.ceil_lt_add_one hnn]
  have hfin : (3 : ℝ) * ((⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ : ℕ) : ℝ) ≤ (Z : ℝ) := by
    have hmul : Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)
        ≤ Real.sqrt (Z : ℝ) * (Real.sqrt (Z : ℝ) / 6) :=
      mul_le_mul_of_nonneg_left hZ (by linarith [hsq6])
    have hval : Real.sqrt (Z : ℝ) * (Real.sqrt (Z : ℝ) / 6) = (Z : ℝ) / 6 := by
      rw [mul_div_assoc'] at *
      rw [hsqsq]
    rw [hval] at hmul
    have hZ36R : (36 : ℝ) ≤ (Z : ℝ) := hZ36
    linarith [hceil, hmul]
  exact_mod_cast hfin

set_option maxHeartbeats 1600000 in
/-- **The Route E reciprocal-marker Möbius Hall law.**  For every `9/10 < β < 1`, every sign
`σ ∈ {±1}` and every constant `C`, the interval `(Z, Z + H(Z)]` with
`H(Z) = ⌈√Z·exp((log Z)^β)⌉` contains at least `C·H(Z)/log Z` integers `n` with `μ(n) = σ`, for all
sufficiently large `Z`. -/
theorem route_e_marker_hall_law {β' : ℝ} (hβ'0 : 9 / 10 < β') (hβ'1 : β' < 1) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (C : ℝ) :
    ∀ᶠ Z : ℕ in atTop,
      C * (((⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ : ℕ) : ℝ) / Real.log ((Z : ℕ) : ℝ))
        ≤ ((((Finset.Ioc Z (Z + ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊)).filter
            (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  -- the auxiliary exponent, strictly between `9/10` and `β'`
  set β : ℝ := (9 / 10 + β') / 2 with hβdef
  have hβ0 : 9 / 10 < β := by rw [hβdef]; linarith
  have hββ' : β < β' := by rw [hβdef]; linarith
  have hβ1 : β < 1 := by linarith
  have hβhalf : 1 / 2 < β := by linarith
  -- enough blocks to beat the prescribed constant
  obtain ⟨K₀, hK₀⟩ := exists_multiHarmConst_ge (max (4096 * C / squarefreeDensity) 1)
  have hharm : 0 < multiHarmConst K₀ :=
    lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hK₀)
  have hCle : C ≤ tileConst K₀ / 4 := by
    have h1 : 4096 * C / squarefreeDensity ≤ multiHarmConst K₀ :=
      le_trans (le_max_left _ _) hK₀
    rw [div_le_iff₀ hD] at h1
    rw [tileConst]
    linarith [h1]
  filter_upwards [tiled_count hβ0 hβ1 hσ K₀ hharm,
    eventually_two_tileLen_le hβhalf hββ' K₀,
    eventually_three_mul_ceil_le (show (0 : ℝ) < β' by linarith) hβ'1,
    eventually_ge_atTop 2] with Z hcount htile h3 hZ2
  obtain ⟨u, hPu, hcov, hmain⟩ := hcount
  set H : ℕ := ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ with hH
  have hPpos : 0 < tileBase K₀ u := by omega
  have h2t : 2 * tileLen β K₀ u ≤ H := by
    have hR := htile u hPpos hPu
    exact_mod_cast hR
  refine le_trans ?_ (hmain H h3 h2t)
  have hZR : (2 : ℝ) ≤ ((Z : ℕ) : ℝ) := by exact_mod_cast hZ2
  have hlogZ : (0 : ℝ) < Real.log ((Z : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  have hnn : (0 : ℝ) ≤ (H : ℝ) / Real.log ((Z : ℕ) : ℝ) := div_nonneg hHnn hlogZ.le
  exact mul_le_mul_of_nonneg_right hCle hnn

/-! ## The prime supply of the same window -/

theorem eventually_log_pow_le_rpow (c : ℝ) :
    ∀ᶠ y : ℝ in atTop, c * (Real.log y) ^ 4 ≤ y ^ ((3 : ℝ) / 8) := by
  have hlo : (fun y : ℝ => Real.log y ^ (4 : ℝ)) =o[atTop] fun y : ℝ => y ^ ((3 : ℝ) / 8) :=
    isLittleO_log_rpow_rpow_atTop 4 (by norm_num)
  have hc : (0 : ℝ) < 1 / (|c| + 1) := by positivity
  filter_upwards [hlo.def hc, eventually_ge_atTop (1 : ℝ)] with y hy hy1
  have hy0 : (0 : ℝ) < y := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy1
  have hpow : Real.log y ^ (4 : ℝ) = (Real.log y) ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _)] at hy
  have habs : c ≤ |c| + 1 := by linarith [le_abs_self c]
  have hkey : (|c| + 1) * (Real.log y) ^ 4 ≤ y ^ ((3 : ℝ) / 8) := by
    have hpos : (0 : ℝ) < |c| + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hy hpos.le
    rw [show (|c| + 1) * (1 / (|c| + 1) * y ^ ((3 : ℝ) / 8)) = y ^ ((3 : ℝ) / 8) by
      field_simp] at hmul
    exact hmul
  nlinarith [hkey, habs, pow_nonneg hlog0 4]

set_option maxHeartbeats 1600000 in
/-- **The prime count of the prescribed window.**  Brun–Titchmarsh at the eighth root. -/
theorem eventually_card_primes_le_window (β' : ℝ) :
    ∀ᶠ Z : ℕ in atTop,
      ((#{p ∈ Finset.Ioc Z (Z + ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊) | p.Prime} : ℕ) : ℝ)
        ≤ 17 * (((⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ : ℕ) : ℝ)
            / Real.log ((Z : ℕ) : ℝ)) := by
  have hev : ∀ᶠ y : ℝ in atTop, (49 : ℝ) * (Real.log y) ^ 4 ≤ y ^ ((3 : ℝ) / 8) :=
    eventually_log_pow_le_rpow 49
  have hlogev : ∀ᶠ y : ℝ in atTop, (1 : ℝ) ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hev,
    tendsto_natCast_atTop_atTop.eventually hlogev, eventually_ge_atTop 3] with Z hZpow hZlog hZ3
  set H : ℕ := ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ with hH
  have hZR : (3 : ℝ) ≤ ((Z : ℕ) : ℝ) := by exact_mod_cast hZ3
  have hZR0 : (0 : ℝ) < ((Z : ℕ) : ℝ) := by linarith
  have hlogZ : (1 : ℝ) ≤ Real.log ((Z : ℕ) : ℝ) := hZlog
  have hlogZ0 : (0 : ℝ) < Real.log ((Z : ℕ) : ℝ) := by linarith
  -- the sieve parameter
  set z : ℝ := ((Z : ℕ) : ℝ) ^ ((1 : ℝ) / 8) with hz
  have hlogz : Real.log z = Real.log ((Z : ℕ) : ℝ) / 8 := by
    rw [hz, Real.log_rpow hZR0]; ring
  have hz1 : (1 : ℝ) < z := by
    rw [← Real.exp_log (show (0:ℝ) < z from Real.rpow_pos_of_pos hZR0 _), hlogz]
    have : (0 : ℝ) < Real.log ((Z : ℕ) : ℝ) / 8 := by linarith
    calc (1 : ℝ) = Real.exp 0 := by simp
      _ < Real.exp (Real.log ((Z : ℕ) : ℝ) / 8) := Real.exp_lt_exp.2 this
  have hz0 : (0 : ℝ) < z := by linarith
  have hbt := card_prime_Ioc_le_bt (A := Z) (B := Z + H) (by omega) hz1
  have hdiff : (((Z + H : ℕ) : ℝ) - ((Z : ℕ) : ℝ)) = (H : ℝ) := by push_cast; ring
  rw [hdiff, hlogz] at hbt
  refine hbt.trans ?_
  -- the main term
  have hmain : 2 * (H : ℝ) / (Real.log ((Z : ℕ) : ℝ) / 8)
      = 16 * ((H : ℝ) / Real.log ((Z : ℕ) : ℝ)) := by
    field_simp
    ring
  rw [hmain]
  -- the error term is below one unit of the main term
  have hHge : Real.sqrt ((Z : ℕ) : ℝ) ≤ (H : ℝ) := by
    have h1 : (1 : ℝ) ≤ cardLength β' ((Z : ℕ) : ℝ) := one_le_cardLength (by linarith)
    have h2 : Real.sqrt ((Z : ℕ) : ℝ) * 1 ≤ Real.sqrt ((Z : ℕ) : ℝ) * cardLength β' ((Z : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    have h3 : Real.sqrt ((Z : ℕ) : ℝ) * cardLength β' ((Z : ℕ) : ℝ) ≤ (H : ℝ) := Nat.le_ceil _
    linarith
  have hsqrt : Real.sqrt ((Z : ℕ) : ℝ) = z * ((Z : ℕ) : ℝ) ^ ((3 : ℝ) / 8) := by
    rw [hz, ← Real.rpow_add hZR0, Real.sqrt_eq_rpow]
    norm_num
  have herr : 6 * z * (1 + Real.log ((Z : ℕ) : ℝ) / 8) ^ 3 + 1
      ≤ (H : ℝ) / Real.log ((Z : ℕ) : ℝ) := by
    rw [le_div_iff₀ hlogZ0]
    have hz1' : (1 : ℝ) ≤ z := by linarith
    have hcube : (1 + Real.log ((Z : ℕ) : ℝ) / 8) ^ 3 ≤ (2 * Real.log ((Z : ℕ) : ℝ)) ^ 3 := by
      refine pow_le_pow_left₀ (by linarith) (by linarith) 3
    have hstep : (6 * z * (1 + Real.log ((Z : ℕ) : ℝ) / 8) ^ 3 + 1) * Real.log ((Z : ℕ) : ℝ)
        ≤ 49 * z * (Real.log ((Z : ℕ) : ℝ)) ^ 4 := by
      have hlog4 : Real.log ((Z : ℕ) : ℝ) ≤ (Real.log ((Z : ℕ) : ℝ)) ^ 4 := by
        have h1 : (Real.log ((Z : ℕ) : ℝ)) ^ 1 ≤ (Real.log ((Z : ℕ) : ℝ)) ^ 4 :=
          pow_le_pow_right₀ hlogZ (by norm_num)
        simpa using h1
      have hcube8 : (2 * Real.log ((Z : ℕ) : ℝ)) ^ 3 = 8 * (Real.log ((Z : ℕ) : ℝ)) ^ 3 := by
        ring
      have hA : 6 * z * (1 + Real.log ((Z : ℕ) : ℝ) / 8) ^ 3
          ≤ 48 * z * (Real.log ((Z : ℕ) : ℝ)) ^ 3 := by
        have h6z : (0 : ℝ) ≤ 6 * z := by linarith
        have hmm := mul_le_mul_of_nonneg_left hcube h6z
        rw [hcube8] at hmm
        linarith [hmm]
      have hLnn : (0 : ℝ) ≤ Real.log ((Z : ℕ) : ℝ) := hlogZ0.le
      have hB := mul_le_mul_of_nonneg_right hA hLnn
      have hD : Real.log ((Z : ℕ) : ℝ) ≤ z * (Real.log ((Z : ℕ) : ℝ)) ^ 4 := by
        nlinarith [hlog4, hz1', pow_nonneg hLnn 4]
      nlinarith [hB, hD]
    refine hstep.trans ?_
    have hmul : 49 * (Real.log ((Z : ℕ) : ℝ)) ^ 4 ≤ ((Z : ℕ) : ℝ) ^ ((3 : ℝ) / 8) := hZpow
    calc 49 * z * (Real.log ((Z : ℕ) : ℝ)) ^ 4 = z * (49 * (Real.log ((Z : ℕ) : ℝ)) ^ 4) := by ring
      _ ≤ z * ((Z : ℕ) : ℝ) ^ ((3 : ℝ) / 8) := mul_le_mul_of_nonneg_left hmul hz0.le
      _ = Real.sqrt ((Z : ℕ) : ℝ) := hsqrt.symm
      _ ≤ (H : ℝ) := hHge
  linarith [herr]

/-- **The window carries at least as many positive-Möbius integers as primes.**  This is the
card's consequence `(5)`: the Hall injection from the source primes of a dyadic shell to
positive-Möbius integers at displacement at most `H(X) = X^{1/2+o(1)}`. -/
theorem route_e_marker_hall_injection {β' : ℝ} (hβ'0 : 9 / 10 < β') (hβ'1 : β' < 1) :
    ∀ᶠ Z : ℕ in atTop,
      #{p ∈ Finset.Ioc Z (Z + ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊) | p.Prime}
        ≤ #{n ∈ Finset.Ioc Z (Z + ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊) |
              moebius n = 1} := by
  filter_upwards [route_e_marker_hall_law hβ'0 hβ'1 (Or.inl rfl) 17,
    eventually_card_primes_le_window β'] with Z hmark hprime
  have hR : ((#{p ∈ Finset.Ioc Z (Z + ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊) |
        p.Prime} : ℕ) : ℝ)
      ≤ ((#{n ∈ Finset.Ioc Z (Z + ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊) |
        moebius n = 1} : ℕ) : ℝ) := le_trans hprime hmark
  exact_mod_cast hR

end

end RHTower.Sieve
