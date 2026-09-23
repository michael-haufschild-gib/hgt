import GaloisForLFunctions.RHTower.HardyZDyadicMean
import GaloisForLFunctions.RHTower.HardyFourthMomentSignChange
import GaloisForLFunctions.RHTower.ZetaLineFirstMoment
import GaloisForLFunctions.RHTower.HorizontalSingletonFiberCharging

/-!
# Hardy's theorem

`\zeta` has infinitely many zeros on the critical line, with a logarithmic lower bound for the
census.  The three moment estimates over a dyadic window `[T, 2T]` —

* `T/4 \le \int Z^(2 : ℕ)` (first-moment route),
* `\int Z^(4 : ℕ) = O(T(1+\log T)^(4 : ℕ))` (Ingham),
* `\int Z = O(T^{3/4})` (van der Corput on the smooth approximate functional equation),

feed the interpolation inequality `(\int f^(2 : ℕ))^(3 : ℕ) \le (\int f)^(2 : ℕ) (\int f^(4 : ℕ))`: a `Z` of constant
sign on the window would satisfy `\int |Z| = |\int Z|`, which the three estimates contradict once
`64\,C_E^(2 : ℕ) C_F(1+\log T)^(4 : ℕ) < \sqrt T`.  Hence `Z` changes sign on every dyadic window beyond an
explicit height, and its zero is a critical-line zero of `\zeta`.

Chaining the windows `4^k M` gives `N_0(T) \ge c\log T`, where `N_0` is the census
`xiPosCriticalZeroCount` of critical-line `xi` zeros with ordinate in `(0, T]`, counted with
multiplicity.  Everything is unconditional.
-/

open Set MeasureTheory Complex


namespace RHTower

noncomputable section

/-- `(1 + log N)^(4 : ℕ)` is dominated by the fourth root of `N`, with an explicit constant. -/
theorem one_add_log_pow_four_le {N : ℝ} (hN : 1 ≤ N) :
    (1 + Real.log N) ^ 4 ≤ 83521 * Real.sqrt (Real.sqrt N) := by
  have hN0 : (0 : ℝ) < N := by linarith
  set a := Real.sqrt N with ha
  set b := Real.sqrt a with hb
  set c := Real.sqrt b with hc
  set u := Real.sqrt c with hu
  have ha1 : 1 ≤ a := by
    rw [ha, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hN
  have hb1 : 1 ≤ b := by
    rw [hb, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ha1
  have hc1 : 1 ≤ c := by
    rw [hc, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hb1
  have hu1 : 1 ≤ u := by
    rw [hu, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hc1
  have ha2 : a ^ 2 = N := Real.sq_sqrt hN0.le
  have hb2 : b ^ 2 = a := Real.sq_sqrt (by linarith)
  have hc2 : c ^ 2 = b := Real.sq_sqrt (by linarith)
  have hu2 : u ^ 2 = c := Real.sq_sqrt (by linarith)
  have hpow : u ^ 16 = N := by
    have : u ^ 16 = (((u ^ 2) ^ 2) ^ 2) ^ 2 := by ring
    rw [this, hu2, hc2, hb2, ha2]
  have hu0 : (0 : ℝ) < u := by linarith
  have hlog : Real.log N = 16 * Real.log u := by
    rw [← hpow, Real.log_pow]
    push_cast
    ring
  have hlogu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu0
  have hkey : 1 + Real.log N ≤ 17 * u := by
    rw [hlog]
    linarith
  have hnn : (0 : ℝ) ≤ 1 + Real.log N := by
    have : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN
    linarith
  have hb4 : u ^ 4 = b := by
    have : u ^ 4 = (u ^ 2) ^ 2 := by ring
    rw [this, hu2, hc2]
  calc (1 + Real.log N) ^ 4 ≤ (17 * u) ^ 4 := by
        exact pow_le_pow_left₀ hnn hkey 4
    _ = 83521 * u ^ 4 := by ring
    _ = 83521 * Real.sqrt (Real.sqrt N) := by rw [hb4]

/-- **Lemma F on real windows.**  The dyadic fourth moment bound extends from integer to real
heights by covering `[T, 2T]` with the two integer windows above `⌊T⌋`. -/
theorem exists_integral_hardyZ_pow_four_dyadic_real_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : ℝ}, 8 ≤ T →
      (∫ t in T..(2 * T), (hardyZ t) ^ 4) ≤ C * T * (1 + Real.log T) ^ 4 := by
  obtain ⟨C, hC, hF⟩ := exists_integral_hardyZ_pow_four_dyadic_le_polylog
  refine ⟨33 * C, by positivity, fun {T} hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  set N : ℕ := ⌊T⌋₊ with hNdef
  have hNle : (N : ℝ) ≤ T := Nat.floor_le hT0.le
  have hNlt : T < (N : ℝ) + 1 := Nat.lt_floor_add_one T
  have hN8 : 8 ≤ N := by
    have : (8 : ℕ) ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
    exact this
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_trans (by norm_num) hN8)
  have hcover : 2 * T ≤ 4 * (N : ℝ) := by linarith
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioc ((N : ℝ)) (4 * (N : ℝ)))]
      fun t => (hardyZ t) ^ 4 :=
    Filter.Eventually.of_forall fun t => by
      show (0 : ℝ) ≤ (hardyZ t) ^ 4
      positivity
  have hint : IntervalIntegrable (fun t => (hardyZ t) ^ 4) volume ((N : ℝ)) (4 * (N : ℝ)) :=
    (continuous_hardyZ.pow 4).intervalIntegrable _ _
  have hstep := intervalIntegral.integral_mono_interval (f := fun t => (hardyZ t) ^ 4)
    hNle (by linarith) hcover hnn hint
  -- split the big window
  have hsplit : (∫ t in ((N : ℝ))..(4 * (N : ℝ)), (hardyZ t) ^ 4)
      = (∫ t in ((N : ℝ))..(2 * (N : ℝ)), (hardyZ t) ^ 4)
        + ∫ t in (2 * (N : ℝ))..(4 * (N : ℝ)), (hardyZ t) ^ 4 :=
    (intervalIntegral.integral_add_adjacent_intervals
      ((continuous_hardyZ.pow 4).intervalIntegrable _ _)
      ((continuous_hardyZ.pow 4).intervalIntegrable _ _)).symm
  have hb1 := hF (show 4 ≤ N by omega)
  have hb2 := hF (show 4 ≤ 2 * N by omega)
  have hc1 : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  rw [hc1, show (2 : ℝ) * (2 * (N : ℝ)) = 4 * (N : ℝ) by ring] at hb2
  -- compare the logarithms
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogN : Real.log (N : ℝ) ≤ Real.log T := Real.log_le_log (by linarith) hNle
  have hlogN0 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlog2N : Real.log (2 * (N : ℝ)) ≤ 1 + Real.log T := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have hl2 : Real.log 2 ≤ 1 := by
      have : Real.log 2 ≤ Real.log (Real.exp 1) :=
        Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
      rwa [Real.log_exp] at this
    linarith
  have hp1 : C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 ≤ C * T * (1 + Real.log T) ^ 4 := by
    have h1 : (1 + Real.log (N : ℝ)) ^ 4 ≤ (1 + Real.log T) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 4
    have h2 : (0 : ℝ) ≤ (1 + Real.log T) ^ 4 := by positivity
    have hCN : (0 : ℝ) ≤ C * (N : ℝ) := by nlinarith
    calc C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4
        ≤ C * (N : ℝ) * (1 + Real.log T) ^ 4 := mul_le_mul_of_nonneg_left h1 hCN
      _ ≤ C * T * (1 + Real.log T) ^ 4 := by
          refine mul_le_mul_of_nonneg_right ?_ h2
          nlinarith
  have hp2 : C * (2 * (N : ℝ)) * (1 + Real.log (2 * (N : ℝ))) ^ 4
      ≤ 32 * C * T * (1 + Real.log T) ^ 4 := by
    have hlog2Nnn : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_nonneg (by linarith)
    have h1 : (1 + Real.log (2 * (N : ℝ))) ^ 4 ≤ (2 * (1 + Real.log T)) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 4
    have h1' : (2 * (1 + Real.log T)) ^ 4 = 16 * (1 + Real.log T) ^ 4 := by ring
    rw [h1'] at h1
    have h2 : (0 : ℝ) ≤ (1 + Real.log T) ^ 4 := by positivity
    have hCN : (0 : ℝ) ≤ C * (2 * (N : ℝ)) := by nlinarith
    calc C * (2 * (N : ℝ)) * (1 + Real.log (2 * (N : ℝ))) ^ 4
        ≤ C * (2 * (N : ℝ)) * (16 * (1 + Real.log T) ^ 4) :=
          mul_le_mul_of_nonneg_left h1 hCN
      _ ≤ 32 * C * T * (1 + Real.log T) ^ 4 := by
          have hstep2 : C * (2 * (N : ℝ)) * 16 ≤ 32 * C * T := by nlinarith
          nlinarith [h2, hstep2]
  calc (∫ t in T..(2 * T), (hardyZ t) ^ 4)
      ≤ ∫ t in ((N : ℝ))..(4 * (N : ℝ)), (hardyZ t) ^ 4 := hstep
    _ = (∫ t in ((N : ℝ))..(2 * (N : ℝ)), (hardyZ t) ^ 4)
          + ∫ t in (2 * (N : ℝ))..(4 * (N : ℝ)), (hardyZ t) ^ 4 := hsplit
    _ ≤ C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4
          + C * (2 * (N : ℝ)) * (1 + Real.log (2 * (N : ℝ))) ^ 4 := by linarith
    _ ≤ C * T * (1 + Real.log T) ^ 4 + 32 * C * T * (1 + Real.log T) ^ 4 := by linarith
    _ = 33 * C * T * (1 + Real.log T) ^ 4 := by ring

/-- **Hardy's theorem, dyadic form.**  Beyond an explicit height every dyadic window `[T, 2T]`
carries a zero of `ζ` on the critical line.  Unconditional. -/
theorem exists_riemannZeta_line_zero_dyadic :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∃ τ ∈ Set.Icc T (2 * T), riemannZeta (linePt τ) = 0 := by
  obtain ⟨TC, hTC, hC⟩ := exists_le_integral_hardyZ_sq
  obtain ⟨CF, hCF, hF⟩ := exists_integral_hardyZ_pow_four_dyadic_real_le
  obtain ⟨CE, hCE, hE⟩ := exists_abs_integral_hardyZ_dyadic_le
  set A : ℝ := 64 * CE ^ 2 * CF + 1 with hAdef
  have hA0 : (0 : ℝ) < A := by positivity
  set B : ℝ := (83521 * A) ^ 4 with hBdef
  refine ⟨max (max TC (B + 1)) 16, ?_, fun T hT => ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hn16 : (16 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hn0 : (0 : ℝ) < T := by linarith
  have hnTC : TC ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hnB : B < T := by
    have h1 : B + 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
    linarith
  have hnn : T ≤ 2 * T := by linarith
  have h2 := hC T hnTC
  have h4 := hF (show (8 : ℝ) ≤ T by linarith)
  have hEbd := hE hn16
  set r : ℝ := Real.sqrt (Real.sqrt T) with hrdef
  have hr0 : (0 : ℝ) ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = Real.sqrt T := Real.sq_sqrt (Real.sqrt_nonneg T)
  have hr4 : r ^ 4 = T := by
    have hrr : r ^ 4 = (r ^ 2) ^ 2 := by ring
    rw [hrr, hr2, Real.sq_sqrt hn0.le]
  have hrbig : 83521 * A < r := by
    by_contra hcon
    rw [not_lt] at hcon
    have hle := pow_le_pow_left₀ hr0 hcon 4
    rw [hr4] at hle
    exact absurd hle (not_le.mpr hnB)
  set F : ℝ := CF * T * (1 + Real.log T) ^ 4 with hFdef
  have hlognn : (0 : ℝ) ≤ 1 + Real.log T := by
    have : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
    linarith
  have hFnn : (0 : ℝ) ≤ F := by
    have h4nn : (0 : ℝ) ≤ (1 + Real.log T) ^ 4 := by positivity
    rw [hFdef]
    positivity
  have hFle : F ≤ 83521 * CF * r ^ 5 := by
    have hlogbd := one_add_log_pow_four_le (N := T) (by linarith)
    rw [← hrdef] at hlogbd
    have hstep : CF * T * (1 + Real.log T) ^ 4 ≤ CF * T * (83521 * r) :=
      mul_le_mul_of_nonneg_left hlogbd (by positivity)
    calc F ≤ CF * T * (83521 * r) := hstep
      _ = 83521 * CF * (r ^ 4 * r) := by rw [hr4]; ring
      _ = 83521 * CF * r ^ 5 := by ring
  have hIsq : (∫ u in T..(2 * T), hardyZ u) ^ 2 ≤ CE ^ 2 * r ^ 6 := by
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hEbd 2
    rw [sq_abs] at hsq
    refine le_trans hsq (le_of_eq ?_)
    rw [← hr2]
    ring
  have hgap : (∫ u in T..(2 * T), hardyZ u) ^ 2 * F < (T / 4) ^ 3 := by
    have hprod : (∫ u in T..(2 * T), hardyZ u) ^ 2 * F
        ≤ (CE ^ 2 * r ^ 6) * (83521 * CF * r ^ 5) :=
      mul_le_mul hIsq hFle hFnn (by positivity)
    have hcube : (T / 4) ^ 3 = r ^ 12 / 64 := by rw [← hr4]; ring
    rw [hcube]
    refine lt_of_le_of_lt hprod ?_
    rw [show (CE ^ 2 * r ^ 6) * (83521 * CF * r ^ 5)
        = (83521 * (CE ^ 2 * CF)) * r ^ 11 by ring]
    have hrpos : (0 : ℝ) < r := lt_of_le_of_lt (by positivity) hrbig
    have hr11 : (0 : ℝ) < r ^ 11 := by positivity
    have hcoef : 64 * (83521 * (CE ^ 2 * CF)) < r := by
      have hle : 64 * (83521 * (CE ^ 2 * CF)) ≤ 83521 * A := by
        rw [hAdef]; nlinarith [hCE, hCF, sq_nonneg CE]
      linarith
    rw [show r ^ 12 = r ^ 11 * r by ring, lt_div_iff₀ (by norm_num : (0:ℝ) < 64)]
    nlinarith [hr11, hcoef]
  have hS : (0 : ℝ) < T / 4 := by linarith
  exact exists_riemannZeta_line_zero_of_hardyZ_fourth_moment_gap
    (α := T) (β := 2 * T) (S := T / 4) (F := F) hnn hS h2 (by rw [hFdef]; exact h4) hgap

/-! ## The critical-line census grows -/

theorem stripFinsetPos_subset {T T' : ℝ} (h : T ≤ T') :
    stripFinsetPos T ⊆ stripFinsetPos T' := by
  intro z hz
  rw [mem_stripFinsetPos] at hz ⊢
  exact ⟨hz.1, hz.2.1, hz.2.2.1, le_trans hz.2.2.2.1 h, hz.2.2.2.2⟩

theorem monotone_xiPosCriticalZeroCount : Monotone xiPosCriticalZeroCount := by
  intro T T' h
  exact Finset.sum_le_sum_of_subset
    (Finset.filter_subset_filter _ (stripFinsetPos_subset h))

/-- **The critical-line census strictly increases across each quadruple window.** -/
theorem xiPosCriticalZeroCount_lt_of_dyadic_zero {T₀ : ℝ}
    (hzero : ∀ T : ℝ, T₀ ≤ T → ∃ τ ∈ Set.Icc T (2 * T), riemannZeta (linePt τ) = 0)
    {T : ℝ} (hT : T₀ ≤ T) (hT0 : 0 < T) :
    xiPosCriticalZeroCount T < xiPosCriticalZeroCount (4 * T) := by
  obtain ⟨τ, hτ, hz⟩ := hzero (2 * T) (by linarith)
  have hτlow : 2 * T ≤ τ := hτ.1
  have hτhigh : τ ≤ 4 * T := by linarith [hτ.2]
  have hτpos : (0 : ℝ) < τ := by linarith
  have hxi : xi (linePt τ) = 0 := by
    rw [xi_line_eq_zero_iff_hardyZ]
    have hnorm := norm_riemannZeta_line_eq_abs_hardyZ τ
    rw [hz, norm_zero] at hnorm
    exact abs_eq_zero.mp hnorm.symm
  set z₀ : ℂ := linePt τ with hz₀
  set A : Finset ℂ := (stripFinsetPos T).filter (fun z => z.re = 1 / 2) with hA
  set B : Finset ℂ := (stripFinsetPos (4 * T)).filter (fun z => z.re = 1 / 2) with hB
  have hz₀B : z₀ ∈ B := by
    rw [hB, Finset.mem_filter, mem_stripFinsetPos]
    refine ⟨⟨linePt_re_pos τ, linePt_re_lt_one τ, ?_, ?_, hxi⟩, linePt_re τ⟩
    · rw [linePt_im]; exact hτpos
    · rw [linePt_im]; exact hτhigh
  have hz₀A : z₀ ∉ A := by
    rw [hA, Finset.mem_filter, mem_stripFinsetPos]
    rintro ⟨⟨_, _, _, him, _⟩, _⟩
    rw [linePt_im] at him
    linarith
  have hsub : insert z₀ A ⊆ B := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hwA
    · exact hz₀B
    · rw [hA, Finset.mem_filter, mem_stripFinsetPos] at hwA
      rw [hB, Finset.mem_filter, mem_stripFinsetPos]
      obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ := hwA
      exact ⟨⟨h1, h2, h3, by linarith, h5⟩, h6⟩
  have hord : 1 ≤ (analyticOrderAt xi z₀).toNat :=
    Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hxi)
  have hins : ∑ z ∈ insert z₀ A, (analyticOrderAt xi z).toNat
      = (analyticOrderAt xi z₀).toNat + ∑ z ∈ A, (analyticOrderAt xi z).toNat :=
    Finset.sum_insert hz₀A
  have hmono : ∑ z ∈ insert z₀ A, (analyticOrderAt xi z).toNat
      ≤ ∑ z ∈ B, (analyticOrderAt xi z).toNat :=
    Finset.sum_le_sum_of_subset hsub
  rw [xiPosCriticalZeroCount, xiPosCriticalZeroCount, ← hA, ← hB]
  omega

/-- The census exceeds every `k` at height `4^k` times an absolute constant. -/
theorem exists_pow_le_xiPosCriticalZeroCount :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ k : ℕ, k ≤ xiPosCriticalZeroCount ((4 : ℝ) ^ k * M) := by
  obtain ⟨T₀, hT₀, hzero⟩ := exists_riemannZeta_line_zero_dyadic
  refine ⟨max T₀ 1, le_max_right _ _, fun k => ?_⟩
  have hM1 : (1 : ℝ) ≤ max T₀ 1 := le_max_right _ _
  induction k with
  | zero => simp
  | succ k ih =>
      have hpow : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hge : max T₀ 1 ≤ (4 : ℝ) ^ k * max T₀ 1 := by nlinarith
      have hT₀le : T₀ ≤ (4 : ℝ) ^ k * max T₀ 1 := le_trans (le_max_left _ _) hge
      have hpos : (0 : ℝ) < (4 : ℝ) ^ k * max T₀ 1 := by nlinarith
      have hstep := xiPosCriticalZeroCount_lt_of_dyadic_zero hzero hT₀le hpos
      rw [show (4 : ℝ) * ((4 : ℝ) ^ k * max T₀ 1) = (4 : ℝ) ^ (k + 1) * max T₀ 1 by
        ring] at hstep
      omega

/-- **Hardy's theorem with a logarithmic census bound.**  The number of critical-line zeros of
`xi` with ordinate in `(0, T]`, counted with multiplicity, is at least a positive constant times
`log T` for all large `T`.  Unconditional. -/
theorem exists_log_le_xiPosCriticalZeroCount :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T →
      c * Real.log T ≤ (xiPosCriticalZeroCount T : ℝ) := by
  obtain ⟨M, hM1, hpow⟩ := exists_pow_le_xiPosCriticalZeroCount
  have hM0 : (0 : ℝ) < M := by linarith
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨1 / (2 * Real.log 4), by positivity, 16 * M ^ 2, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by nlinarith
  have hTM : (1 : ℝ) ≤ T / M := by
    rw [le_div_iff₀ hM0]
    nlinarith
  set y : ℝ := Real.log (T / M) / Real.log 4 with hy
  have hy0 : (0 : ℝ) ≤ y := by
    have : (0 : ℝ) ≤ Real.log (T / M) := Real.log_nonneg hTM
    positivity
  set k : ℕ := ⌊y⌋₊ with hk
  have hky : (k : ℝ) ≤ y := Nat.floor_le hy0
  have hyk : y < (k : ℝ) + 1 := Nat.lt_floor_add_one y
  have hpowle : (4 : ℝ) ^ k * M ≤ T := by
    have hrpow : (4 : ℝ) ^ (y : ℝ) = T / M := by
      rw [hy, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 4)]
      rw [show Real.log 4 * (Real.log (T / M) / Real.log 4) = Real.log (T / M) by
        field_simp]
      exact Real.exp_log (by positivity)
    have hmono : (4 : ℝ) ^ (k : ℝ) ≤ (4 : ℝ) ^ (y : ℝ) :=
      Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 4) |>.mpr hky
    rw [Real.rpow_natCast, hrpow] at hmono
    rw [← le_div_iff₀ hM0]
    exact hmono
  have hcensus : (k : ℝ) ≤ (xiPosCriticalZeroCount T : ℝ) := by
    have h1 : k ≤ xiPosCriticalZeroCount ((4 : ℝ) ^ k * M) := hpow k
    have h2 : xiPosCriticalZeroCount ((4 : ℝ) ^ k * M) ≤ xiPosCriticalZeroCount T :=
      monotone_xiPosCriticalZeroCount hpowle
    exact_mod_cast le_trans h1 h2
  have hlogdiv : Real.log (T / M) = Real.log T - Real.log M := Real.log_div hT0.ne' hM0.ne'
  have hlogM : (0 : ℝ) ≤ Real.log M := Real.log_nonneg hM1
  have hbig : 2 * Real.log M + 2 * Real.log 4 ≤ Real.log T := by
    have hle : Real.log (16 * M ^ 2) ≤ Real.log T := Real.log_le_log (by positivity) hT
    have heq : Real.log (16 * M ^ 2) = 2 * Real.log 4 + 2 * Real.log M := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
        show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have hfinal : 1 / (2 * Real.log 4) * Real.log T ≤ (k : ℝ) := by
    have hstep : y - 1 ≤ (k : ℝ) := by linarith
    refine le_trans ?_ hstep
    have hyval : y * Real.log 4 = Real.log T - Real.log M := by
      rw [hy, hlogdiv]; field_simp
    rw [div_mul_eq_mul_div, one_mul,
      div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log 4)]
    nlinarith [hyval, hbig, hlog4]
  linarith

end

end RHTower
