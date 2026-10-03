import GaloisForLFunctions.RHTower.ZetaLocalWindowTailUpper
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity
import GaloisForLFunctions.RHTower.XiZeroCountLocalCeiling

/-!
# The off-line moment in every dyadic window with the two-thirds proportion

The window tail law of `ZetaLocalWindowTailUpper` charges every zero right of the critical line at
the displacement `R/log T`, using only that at most half of the zeros of a window lie right of the
line.  On a dyadic window `(T, 2T]` the Alpöge–Furman theorem (pinned `Zeta23`, dyadic form
`thmB₀_mult`) gives at least `(2/3 − ε) N(T, 2T)` simple critical zeros.  By reflection, the zeros
right of the line then carry multiplicity at most `(1/3 + ε) N(T, 2T)/2`
(`two_mul_sum_right_add_simple_le`), and the window consumer improves to

  `4π Σ_{T+1 < Im ρ ≤ 2T−1} m_ρ (Re ρ − ½)⁺ ≤ (log c_R − (5/3) R + η) T`

(`eventually_dyadicWindowTail_le_selberg_upper`), the constant of the cumulative off-line moment,
now on every dyadic window.  At `R = 3/2`:
`Σ_{T+1 < Im ρ ≤ 2T−1} m_ρ (Re ρ − ½)⁺ ≤ (67/1000) T` for all large `T`
(`eventually_dyadicWindowTail_le_sixtySeven_thousandths`), against `(134/1000) T` from the
cumulative bound.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval ComplexOrder

namespace RHTower

noncomputable section

/-! ## The two-thirds theorem on dyadic windows -/

/-- Zeta23's zero window `(T₁, T₂]` is the native completed-Xi window, for `0 ≤ T₁`. -/
theorem zeta23_zerosIn_toFinset_eq_window {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) :
    (Zeta23.zerosIn_finite T₁ T₂).toFinset = stripFinsetPos T₂ \ stripFinsetPos T₁ := by
  classical
  ext z
  rw [Set.Finite.mem_toFinset, Finset.mem_sdiff, mem_stripFinsetPos, mem_stripFinsetPos]
  simp only [Zeta23.zerosIn, Zeta23.IsNontrivialZero, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hzeta, hre0, hre1⟩, him0, himT⟩
    have hxi := (xi_zero_iff_zeta_zero_of_mem_strip hre0 hre1).2 hzeta
    refine ⟨⟨hre0, hre1, by linarith, himT, hxi⟩, fun h => ?_⟩
    linarith [h.2.2.2.1]
  · rintro ⟨⟨hre0, hre1, him0, himT, hxi⟩, hnot⟩
    have hT1 : T₁ < z.im := by
      by_contra hle
      exact hnot ⟨hre0, hre1, him0, le_of_not_gt hle, hxi⟩
    exact ⟨⟨(xi_zero_iff_zeta_zero_of_mem_strip hre0 hre1).1 hxi, hre0, hre1⟩, hT1, himT⟩

theorem zeta23_Ncount_window_eq {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) :
    (Zeta23.Ncount T₁ T₂ : ℝ) =
      ∑ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁, ((analyticOrderAt xi z).toNat : ℝ) := by
  classical
  have h : Zeta23.Ncount T₁ T₂ =
      ∑ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁, (analyticOrderAt xi z).toNat := by
    calc Zeta23.Ncount T₁ T₂
        = ∑ z ∈ (Zeta23.zerosIn_finite T₁ T₂).toFinset, Zeta23.zeroMult z := by
          rw [Zeta23.Ncount, ← finsum_mem_coe_finset, Set.Finite.coe_toFinset]
      _ = ∑ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁, (analyticOrderAt xi z).toNat := by
          rw [zeta23_zerosIn_toFinset_eq_window hT₁]
          apply Finset.sum_congr rfl
          intro z hz
          have hz' := (Finset.mem_sdiff.mp hz).1
          unfold Zeta23.zeroMult
          rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
            ⟨(mem_stripFinsetPos.mp hz').1, (mem_stripFinsetPos.mp hz').2.1⟩]
  rw [h]
  push_cast
  rfl

theorem zeta23_N0simple_window_eq {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) :
    Zeta23.N0simple T₁ T₂ = ((stripFinsetPos T₂ \ stripFinsetPos T₁).filter
      (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)).card := by
  classical
  unfold Zeta23.N0simple
  rw [← Set.ncard_coe_finset]
  congr 1
  ext z
  have hw := congrArg (fun s : Finset ℂ => z ∈ s) (zeta23_zerosIn_toFinset_eq_window
    (T₂ := T₂) hT₁)
  simp only [Set.Finite.mem_toFinset, eq_iff_iff] at hw
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hz, hline⟩, hmult⟩
    have hz' := hw.mp hz
    have hstrip := (Finset.mem_sdiff.mp hz').1
    have horder := xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
      ⟨(mem_stripFinsetPos.mp hstrip).1, (mem_stripFinsetPos.mp hstrip).2.1⟩
    refine ⟨hz', hline, ?_⟩
    unfold Zeta23.zeroMult at hmult
    rwa [horder]
  · rintro ⟨hz', hline, hmult⟩
    have hstrip := (Finset.mem_sdiff.mp hz').1
    have horder := xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
      ⟨(mem_stripFinsetPos.mp hstrip).1, (mem_stripFinsetPos.mp hstrip).2.1⟩
    refine ⟨⟨hw.mpr hz', hline⟩, ?_⟩
    unfold Zeta23.zeroMult
    rwa [← horder]

/-- **Alpöge–Furman on dyadic windows**, in the completed-Xi census. -/
theorem two_thirds_simpleCritical_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T ≥ T₀,
      (2 / 3 - ε) * ∑ z ∈ stripFinsetPos (2 * T) \ stripFinsetPos T,
          ((analyticOrderAt xi z).toNat : ℝ)
        ≤ (((stripFinsetPos (2 * T) \ stripFinsetPos T).filter
            (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)).card : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.thmB₀_mult ε hε
  refine ⟨max T₀ 0, le_max_right _ _, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := le_trans (le_max_right _ _) hT
  have h := hT₀ T (le_trans (le_max_left _ _) hT)
  rw [zeta23_Ncount_window_eq hT0, zeta23_N0simple_window_eq hT0] at h
  exact h

/-- **Reflection with the simple critical zeros.**  Right of the line the zeros of a window carry
multiplicity `R`, left of it the same `R`, and on it at least the simple critical count `S`:
`2R + S ≤ N`. -/
theorem two_mul_sum_right_add_simple_le {T₁ T₂ : ℝ} :
    2 * ∑ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁,
        ((analyticOrderAt xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)
      + (((stripFinsetPos T₂ \ stripFinsetPos T₁).filter
          (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)).card : ℝ)
      ≤ ∑ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁, ((analyticOrderAt xi z).toNat : ℝ) := by
  classical
  set S := stripFinsetPos T₂ \ stripFinsetPos T₁ with hS
  set m : ℂ → ℝ := fun z => ((analyticOrderAt xi z).toNat : ℝ) with hm
  have hmr : ∀ z, m (lineReflect z) = m z := fun z => by simp only [hm, xi_orderAt_lineReflect]
  have hrefl := sum_lineReflect_eq (fun z hz => lineReflect_mem_window hz)
    (t := S) (fun z => m z * (if 1 / 2 < z.re then 1 else 0))
  simp only [hmr, lineReflect_re] at hrefl
  have hcard : (((S.filter (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)).card : ℕ)
      : ℝ) = ∑ z ∈ S, (if z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1 then 1 else 0) := by
    rw [Finset.sum_boole]
  rw [hcard, two_mul]
  nth_rewrite 1 [← hrefl]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  have hm0 : 0 ≤ m z := Nat.cast_nonneg _
  rcases lt_trichotomy z.re (1 / 2) with hlt | heq | hgt
  · have h1 : 1 / 2 < 1 - z.re := by linarith
    have h2 : ¬ (1 / 2 < z.re) := by linarith
    have h3 : ¬ (z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1) := fun h => by linarith [h.1]
    rw [if_pos h1, if_neg h2, if_neg h3]
    linarith
  · have h1 : ¬ (1 / 2 < 1 - z.re) := by linarith
    have h2 : ¬ (1 / 2 < z.re) := by linarith
    rw [if_neg h1, if_neg h2, mul_zero, zero_add, zero_add]
    split_ifs with h3
    · have : m z = 1 := by simp only [hm, h3.2, Nat.cast_one]
      linarith
    · exact hm0
  · have h1 : ¬ (1 / 2 < 1 - z.re) := by linarith
    have h3 : ¬ (z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1) := fun h => by linarith [h.1]
    rw [if_neg h1, if_pos hgt, if_neg h3]
    linarith

/-- `Σ m (Re ρ − ½)⁺ ≤ Σ m (Re ρ − ½ − d)⁺ + d Σ_{Re ρ > ½} m` over a window. -/
theorem windowTail_zero_le_right {d T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    windowTail 0 T₁ T₂ ≤ windowTail d T₁ T₂ + d * ∑ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁,
      ((analyticOrderAt xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0) := by
  rw [windowTail_eq_sum hT, windowTail_eq_sum hT, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  have hm0 : (0 : ℝ) ≤ ((analyticOrderAt xi z).toNat : ℝ) := Nat.cast_nonneg _
  have key : max (z.re - 1 / 2 - 0) 0 ≤ max (z.re - 1 / 2 - d) 0
      + d * (if 1 / 2 < z.re then 1 else 0) := by
    split_ifs with h
    · rw [max_eq_left (by linarith), mul_one]
      have := le_max_left (z.re - 1 / 2 - d) 0
      linarith
    · rw [max_eq_right (by linarith), mul_zero, add_zero]
      exact le_max_right _ _
  have := mul_le_mul_of_nonneg_left key hm0
  nlinarith [this]

/-- The assembly of the window moment with a proportion `p` of the zeros on the line. -/
theorem window_moment_combine_dyadic {S tl W0 dN Δ H L E logc R η p X : ℝ}
    (hΔ : 0 ≤ Δ) (hΔH : Δ ≤ H) (hlogc : 2 * R ≤ logc) (hR : 0 ≤ R) (hη : 0 < η)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hlit : 2 * Real.pi * S ≤ Δ / 2 * (logc + η / 4) + L)
    (hbridge : dN / (2 * Real.pi) + tl ≤ S)
    (hlow : Δ * (R - η / 16) - E ≤ dN)
    (hW0 : W0 ≤ tl + (1 - p) / 2 * (dN / (2 * Real.pi)) + X)
    (hadd : 2 * L + 3 * E + 4 * Real.pi * X ≤ η / 8 * Δ) (hE : 0 ≤ E) :
    4 * Real.pi * W0 ≤ (logc - (1 + p) * R + η) * H := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hb : dN + 2 * Real.pi * tl ≤ 2 * Real.pi * S := by
    have := mul_le_mul_of_nonneg_left hbridge (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    have e1 : 2 * Real.pi * (dN / (2 * Real.pi) + tl) = dN + 2 * Real.pi * tl := by
      field_simp
    linarith only [this, e1]
  have hW : 4 * Real.pi * W0 ≤ 4 * Real.pi * tl + (1 - p) * dN + 4 * Real.pi * X := by
    have h1 := mul_le_mul_of_nonneg_left hW0 (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    have e2 : 4 * Real.pi * (tl + (1 - p) / 2 * (dN / (2 * Real.pi)) + X)
        = 4 * Real.pi * tl + (1 - p) * dN + 4 * Real.pi * X := by field_simp; ring
    linarith only [h1, e2]
  have hlow' : (1 + p) * (Δ * (R - η / 16) - E) ≤ (1 + p) * dN :=
    mul_le_mul_of_nonneg_left hlow (by linarith)
  have e1 : (1 + p) * (Δ * (R - η / 16) - E)
      = (1 + p) * R * Δ - (1 + p) * (Δ * η) / 16 - (1 + p) * E := by ring
  have e2 : (1 + p) * dN = dN + p * dN := by ring
  have e3 : (1 - p) * dN = dN - p * dN := by ring
  have hpE : (1 + p) * E ≤ 2 * E := by nlinarith
  have hΔη : 0 ≤ Δ * η := mul_nonneg hΔ hη.le
  have hpΔη : (1 + p) * (Δ * η) / 16 ≤ Δ * η / 8 := by nlinarith
  have e4 : Δ / 2 * (logc + η / 4) = Δ * logc / 2 + Δ * η / 8 := by ring
  have e5 : (logc - (1 + p) * R + η / 2) * Δ
      = Δ * logc - (1 + p) * R * Δ + Δ * η / 2 := by ring
  have e6 : η / 8 * Δ = Δ * η / 8 := by ring
  have hmain : 4 * Real.pi * W0 ≤ (logc - (1 + p) * R + η / 2) * Δ := by
    rw [e5]
    rw [e1, e2] at hlow'
    rw [e3] at hW
    rw [e4] at hlit
    rw [e6] at hadd
    linarith only [hW, hb, hlit, hlow', hadd, hpE, hpΔη, hE]
  have h1 : 0 ≤ logc - (1 + p) * R + η / 2 := by nlinarith only [hlogc, hη, hR, hp1]
  have := mul_le_mul_of_nonneg_left hΔH h1
  nlinarith only [hmain, this, hη, hΔ, hΔH]

theorem window_moment_of_littlewood_dyadic {R η c C K CR T H T₁ T₂ L₀ A p Ec : ℝ} {N : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hR : 0 < R) (hη : 0 < η) (hc0 : 0 < c) (hlogc : 2 * R ≤ Real.log c) (hK : 0 < K)
    (hCR : 0 < CR) (hC : 0 < C) (hbb1 : 1 ≤ routeKRVMBase)
    (hL₀a : 8 * R ≤ L₀) (hL₀b : 16 * R * (Real.log 2 + Real.log routeKRVMBase) / η ≤ L₀)
    (hA : A = 12 * Real.pi * R * CR + 2 * C + 14 * K * Real.log 2)
    (hT0 : 0 < T) (hlogTL : L₀ ≤ Real.log T)
    (hratio : 8 * T ^ (-((1 : ℝ) / 100)) ≤ η / 8)
    (hA' : A ≤ η / 64 * T ^ ((24 : ℝ) / 25))
    (hK' : 8 * K * Real.log T ≤ η / 64 * T ^ ((24 : ℝ) / 25))
    (hX : 4 * Real.pi * (R / Real.log T₂ * Ec) ≤ η / 64 * T ^ ((24 : ℝ) / 25))
    (hT2425 : (4 : ℝ) ≤ T ^ ((24 : ℝ) / 25))
    (hH1 : T ^ ((24 : ℝ) / 25) ≤ H) (hH2 : H ≤ T)
    (hT₁lo : T < T₁) (hT₁hi : T₁ < T + 1) (hT₂lo : T + H - 1 < T₂) (hT₂hi : T₂ < T + H)
    (hN1 : 1 ≤ N) (hNle : (N : ℝ) ≤ (T + H) ^ ((21 : ℝ) / 50))
    (hlit₀ : 2 * Real.pi * (R / Real.log T₂ * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)
          + windowTail (R / Real.log T₂) T₁ T₂)
        ≤ (T₂ - T₁) / 2 * Real.log ((c + c * (η / 8))
            * (T₂ - T₁ + 2 * T₁ ^ ((19 : ℝ) / 20)) / (T₂ - T₁))
          + C + K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ))))
    (hNlo : (T₂ - T₁) * (Real.log (T₁ / routeKRVMBase) + 1) / (2 * Real.pi)
          - CR * (Real.log T₁ + Real.log T₂)
        ≤ (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)
    (hright : ∑ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁,
        ((analyticOrderAt xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)
      ≤ (1 - p) / 2 * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) + Ec) :
    4 * Real.pi * windowTail 0 (T + 1) (T + H - 1) ≤ (Real.log c - (1 + p) * R + η) * H := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hH4 : 4 ≤ H := le_trans hT2425 hH1
  have hT₁0 : 0 < T₁ := by linarith only [hT0, hT₁lo]
  have hT₂0 : 0 < T₂ := by linarith only [hT0, hT₁lo, hT₁hi, hT₂lo, hH4]
  have hT12 : T₁ < T₂ := by linarith only [hT₁hi, hT₂lo, hH4]
  have hT₂2 : T₂ ≤ 2 * T₁ := by linarith only [hT₂hi, hH2, hT₁lo]
  have hlogT₂L : L₀ ≤ Real.log T₂ :=
    le_trans hlogTL (Real.log_le_log hT0 (by linarith only [hT₁lo, hT12]))
  have hlogT₂pos : 0 < Real.log T₂ := by
    have : 0 < 8 * R := by positivity
    linarith only [this, hL₀a, hlogT₂L]
  obtain ⟨d, hdR⟩ : ∃ d : ℝ, d = R / Real.log T₂ := ⟨_, rfl⟩
  rw [← hdR] at hlit₀
  have hd0 : 0 < d := by rw [hdR]; positivity
  have hdlog : d * Real.log T₂ = R := by rw [hdR]; field_simp
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = T₂ - T₁ := ⟨_, rfl⟩
  rw [← hΔdef] at hlit₀ hNlo
  have hΔ0 : 0 < Δ := by rw [hΔdef]; linarith only [hT12]
  have hΔH : Δ ≤ H := by rw [hΔdef]; linarith only [hT₁lo, hT₂hi]
  have hΔlow : T ^ ((24 : ℝ) / 25) / 2 ≤ Δ := by
    rw [hΔdef]; linarith only [hT₁hi, hT₂lo, hH1, hT2425]
  -- the mean square per unit length
  have hτ0 : 0 ≤ 2 * T₁ ^ ((19 : ℝ) / 20) := by positivity
  have htaper := two_mul_rpow_taper_le hT0 hη hT₁0.le (by linarith only [hT₁hi, hT₂hi, hH2, hT12])
    hΔlow hratio
  have hlogMsq : Real.log ((c + c * (η / 8)) * (Δ + 2 * T₁ ^ ((19 : ℝ) / 20)) / Δ)
      ≤ Real.log c + η / 4 := by
    rw [show c + c * (η / 8) = c * (1 + η / 8) by ring]
    exact log_meanSquare_div_le hc0 hη hΔ0 hτ0 htaper
  -- Riemann–von Mangoldt on the window
  have hlogT₁ : Real.log T₂ - Real.log 2 ≤ Real.log T₁ := by
    have := Real.log_le_log hT₂0 hT₂2
    rw [Real.log_mul (by norm_num) hT₁0.ne'] at this
    linarith only [this]
  have hlogT₁T₂ : Real.log T₁ ≤ Real.log T₂ := Real.log_le_log hT₁0 hT12.le
  have hdsmall : d * (Real.log 2 + Real.log routeKRVMBase) ≤ η / 16 := by
    rw [hdR, div_mul_eq_mul_div, div_le_iff₀ hlogT₂pos]
    have h1 := hL₀b.trans hlogT₂L
    rw [div_le_iff₀ hη] at h1
    linarith only [h1]
  have hlow := two_pi_mul_count_window_ge hd0.le hCR.le hΔ0.le hdlog hlogT₁ hlogT₁T₂
    (Real.log_div hT₁0.ne' (by linarith only [hbb1])) hdsmall hNlo
  -- the additive terms
  have hlogN : Real.log ((N : ℝ) ^ (5 : ℕ)) ≤ 3 * (Real.log 2 + Real.log T₂) := by
    rw [Real.log_pow]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hTH0 : 0 < T + H := by linarith only [hT0, hH4]
    have h1 : Real.log (N : ℝ) ≤ Real.log ((T + H) ^ ((21 : ℝ) / 50)) :=
      Real.log_le_log hN0 hNle
    rw [Real.log_rpow hTH0] at h1
    have h2 : Real.log (T + H) ≤ Real.log 2 + Real.log T₂ := by
      have := Real.log_le_log hTH0 (show T + H ≤ 2 * T₂ by linarith only [hT₂lo, hT0, hH4])
      rwa [Real.log_mul (by norm_num) hT₂0.ne'] at this
    have h3 : 0 ≤ Real.log (T + H) := Real.log_nonneg (by linarith only [hT0, hH4])
    push_cast
    linarith only [h1, h2, h3, hlog2]
  have hlogT₂T : Real.log T₂ ≤ Real.log 2 + Real.log T := by
    have := Real.log_le_log hT₂0 (show T₂ ≤ 2 * T by linarith only [hT₂hi, hH2])
    rwa [Real.log_mul (by norm_num) hT0.ne'] at this
  have hlogMb0 : 0 ≤ Real.log ((N : ℝ) ^ (5 : ℕ)) :=
    Real.log_nonneg (one_le_pow₀ (by exact_mod_cast hN1))
  have hL0 : 0 ≤ C + K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ))) := by
    have : 0 ≤ Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)) := by
      linarith only [hlogT₂pos, hlogMb0]
    positivity
  have hE0 : 0 ≤ 4 * Real.pi * CR * R := by positivity
  have hadd : 2 * (C + K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ))))
      + 3 * (4 * Real.pi * CR * R) + 4 * Real.pi * (d * Ec) ≤ η / 8 * Δ := by
    have h3 : K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)))
        ≤ 7 * K * Real.log 2 + 4 * K * Real.log T := by
      have : Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)) ≤ 7 * Real.log 2 + 4 * Real.log T := by
        linarith only [hlogN, hlogT₂T]
      have := mul_le_mul_of_nonneg_left this hK.le
      linarith only [this]
    have h4 := mul_le_mul_of_nonneg_left hΔlow (show (0 : ℝ) ≤ η / 8 by positivity)
    have hX' : 4 * Real.pi * (d * Ec) ≤ η / 64 * T ^ ((24 : ℝ) / 25) := by rw [hdR]; exact hX
    have hηT : 0 ≤ η / 64 * T ^ ((24 : ℝ) / 25) := by positivity
    linarith only [h3, h4, hA, hA', hK', hX', hηT]
  -- assembly
  have hlit : 2 * Real.pi * (d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)
      + windowTail d T₁ T₂)
      ≤ Δ / 2 * (Real.log c + η / 4) + (C + K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)))) := by
    have := mul_le_mul_of_nonneg_left hlogMsq (by positivity : (0 : ℝ) ≤ Δ / 2)
    linarith only [this, hlit₀]
  have hbridge' : 2 * Real.pi * d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) / (2 * Real.pi)
      + windowTail d T₁ T₂
      ≤ d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) + windowTail d T₁ T₂ := by
    rw [show 2 * Real.pi * d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) / (2 * Real.pi)
        = d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) by field_simp]
  have hW0 : windowTail 0 T₁ T₂ ≤ windowTail d T₁ T₂
      + (1 - p) / 2 * (2 * Real.pi * d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)
        / (2 * Real.pi)) + d * Ec := by
    have h := windowTail_zero_le_right (d := d) hT12.le
    have h2 := mul_le_mul_of_nonneg_left hright hd0.le
    rw [show 2 * Real.pi * d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) / (2 * Real.pi)
        = d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) by field_simp]
    have e : d * ((1 - p) / 2 * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) + Ec)
        = (1 - p) / 2 * (d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)) + d * Ec := by ring
    linarith only [h, h2, e]
  have hlit' : 2 * Real.pi * (d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)
      + windowTail d T₁ T₂)
      ≤ Δ / 2 * (Real.log c + η / 4)
        + (C + K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)))) :=
    hlit
  have hmom := window_moment_combine_dyadic hΔ0.le hΔH hlogc hR.le hη hp0 hp1 hlit' hbridge'
    hlow hW0 hadd hE0
  -- monotonicity to the stated window
  have hmono0 : windowTail 0 (T + 1) (T + H - 1) ≤ windowTail 0 T₁ T₂ :=
    windowTail_mono hT₁hi.le hT₂lo.le
  have := mul_le_mul_of_nonneg_left hmono0 (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
  linarith only [this, hmom]


/-- The multiplicity sum over a window is the difference of the counts. -/
theorem window_mult_sum_eq {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    ∑ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁, ((analyticOrderAt xi z).toNat : ℝ)
      = (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁ := by
  unfold xiPosZeroCount
  have h := Finset.sum_sdiff (f := fun z => ((analyticOrderAt xi z).toNat : ℝ))
    (stripFinsetPos_mono hT)
  push_cast
  linarith [h]

/-- **The off-line moment on dyadic windows.**  For every `η > 0` and all large `T`,
`4π Σ_{T+1 < Im ρ ≤ 2T−1} m_ρ (Re ρ − ½)⁺ ≤ (log c_R − (5/3) R + η) T`. -/
theorem eventually_dyadicWindowTail_le_selberg_upper {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ T in atTop,
      4 * Real.pi * windowTail 0 (T + 1) (2 * T - 1)
        ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) - 5 / 3 * R + η) * T := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ZetaGateProductAFE.selbergBlockConstUpper R := ⟨_, rfl⟩
  rw [← hcdef]
  have hc1 : 1 ≤ c := hcdef ▸ ZetaGateProductAFE.one_le_selbergBlockConstUpper hR
  have hc0 : 0 < c := by linarith
  have hlogc : 2 * R ≤ Real.log c := hcdef ▸ two_mul_le_log_selbergBlockConstUpper hR
  obtain ⟨η', hη'⟩ : ∃ η' : ℝ, η' = η / 2 := ⟨_, rfl⟩
  have hη'0 : 0 < η' := by rw [hη']; positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (η / (4 * R)) (1 / 3) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; exact lt_min (by positivity) (by norm_num)
  have hε13 : ε ≤ 1 / 3 := by rw [hεdef]; exact min_le_right _ _
  have hεR : ε * R ≤ η / 4 := by
    have h1 : ε ≤ η / (4 * R) := by rw [hεdef]; exact min_le_left _ _
    calc ε * R ≤ η / (4 * R) * R := mul_le_mul_of_nonneg_right h1 hR.le
      _ = η / 4 := by field_simp
  obtain ⟨TZ, hTZ0, hZ⟩ := two_thirds_simpleCritical_dyadic ε hε0
  obtain ⟨Cc, hCc, Tc, hTc, hceil⟩ := exists_xiZeroCount_window_le
  obtain ⟨C, K, hC, hK, hwide⟩ := exists_zetaWideMoment_le_of_mollified_meanSquare
  obtain ⟨CR, hCR, TR, hTR, hrvm⟩ := exists_xiPosZeroCount_window_bounds
  have hεc : 0 < c * (η' / 8) := mul_pos hc0 (div_pos hη'0 (by norm_num))
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.mp
    (ZetaGateProductAFE.eventually_window_meanSquare_selberg_upper hR hεc)
  rw [← hcdef] at hU₀
  have hbb1 : 1 ≤ routeKRVMBase := by
    rw [routeKRVMBase]
    have h1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith
  have hlogbb : 0 ≤ Real.log routeKRVMBase := Real.log_nonneg hbb1
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ,
      L₀ = 8 * R + 16 * R * (Real.log 2 + Real.log routeKRVMBase) / η' := ⟨_, rfl⟩
  have hp1 : 0 ≤ 16 * R * (Real.log 2 + Real.log routeKRVMBase) / η' := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_nonneg (by positivity) hη'0.le
  have hL₀a : 8 * R ≤ L₀ := by linarith
  have hL₀b : 16 * R * (Real.log 2 + Real.log routeKRVMBase) / η' ≤ L₀ := by linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 12 * Real.pi * R * CR + 2 * C + 14 * K * Real.log 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 4 * Real.pi * R * (8 * (1 / (2 * Real.pi) + 2 * Cc)) := ⟨_, rfl⟩
  have hη64 : 0 < η' / 64 := div_pos hη'0 (by norm_num)
  filter_upwards [eventually_ge_atTop (max (max U₀ (TR + 1)) (max ((2 : ℝ) ^ 50) (Real.exp L₀))),
    eventually_ge_atTop (max (TZ + 1) (Tc + 1)),
    eventually_const_mul_rpow_neg_le 8 ((1 : ℝ) / 100) (by norm_num)
      (show 0 < η' / 8 from div_pos hη'0 (by norm_num)),
    eventually_const_mul_rpow_neg_mul_log_pow_le A ((24 : ℝ) / 25) (by norm_num) 0 hη64,
    eventually_const_mul_rpow_neg_mul_log_pow_le (8 * K) ((24 : ℝ) / 25) (by norm_num) 1 hη64,
    eventually_const_mul_rpow_neg_mul_log_pow_le B ((24 : ℝ) / 25) (by norm_num) 0 hη64]
    with T hTbig hTbig2 hratio hadd1 hadd2 hadd3
  have hTU₀ : U₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTbig
  have hTTR : TR + 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTbig
  have hT50 : (2 : ℝ) ^ 50 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTbig
  have hTL : Real.exp L₀ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTbig
  have hTZ : TZ ≤ T := by linarith [le_max_left (TZ + 1) (Tc + 1)]
  have hTc' : Tc ≤ T := by linarith [le_max_right (TZ + 1) (Tc + 1)]
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT50
  have hT2 : 2 ≤ T := le_trans (by norm_num) hT50
  have hlogTL : L₀ ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos L₀) hTL
    rwa [Real.log_exp] at this
  have hT2425 : (4 : ℝ) ≤ T ^ ((24 : ℝ) / 25) :=
    four_le_rpow_twentyfour_div_twentyfive (le_trans (by norm_num) hT50)
  have hH1 : T ^ ((24 : ℝ) / 25) ≤ T := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ T)
      (show (24 : ℝ) / 25 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have hH4 : 4 ≤ T := le_trans hT2425 hH1
  have hpos2425 : 0 < T ^ ((24 : ℝ) / 25) := Real.rpow_pos_of_pos hT0 _
  have hA' : A ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd1
    rw [pow_zero, mul_one, Real.rpow_neg hT0.le, ← div_eq_mul_inv, div_le_iff₀ hpos2425] at h
    exact h
  have hK' : 8 * K * Real.log T ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd2
    rw [pow_one, Real.rpow_neg hT0.le, ← mul_assoc, mul_comm (8 * K), mul_assoc,
      ← div_eq_inv_mul, div_le_iff₀ hpos2425] at h
    linarith only [h]
  have hB' : B ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd3
    rw [pow_zero, mul_one, Real.rpow_neg hT0.le, ← div_eq_mul_inv, div_le_iff₀ hpos2425] at h
    exact h
  have hms := hU₀ (T + T) (by linarith)
  obtain ⟨T₁, T₂, hT₁lo, hT₁hi, hT₂lo, hT₂hi, hlit₀⟩ :=
    exists_window_littlewood_upper hR hwide hT50 hH4 le_rfl (le_trans hL₀a hlogTL) hms
  obtain ⟨hNlo, -⟩ := hrvm T₁ T₂ (by linarith) (by linarith)
  have hN2 := ZetaGateProductAFE.two_le_mollUpper (show (2 : ℝ) ^ 50 ≤ T + T by linarith)
  -- the right mass of the window against the dyadic two-thirds theorem
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = 2 / 3 - ε := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hpdef]; linarith only [hε13]
  have hp1 : p ≤ 1 := by rw [hpdef]; linarith only [hε0]
  have hT₁₂ : T₁ ≤ T₂ := by linarith
  have hsub :
      stripFinsetPos T₂ \ stripFinsetPos T₁ ⊆ stripFinsetPos (2 * T) \ stripFinsetPos T := by
    intro z hz
    rw [Finset.mem_sdiff] at hz ⊢
    exact ⟨stripFinsetPos_mono (by linarith) hz.1,
      fun h => hz.2 (stripFinsetPos_mono hT₁lo.le h)⟩
  have hRmono : ∑ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁,
        ((analyticOrderAt xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)
      ≤ ∑ z ∈ stripFinsetPos (2 * T) \ stripFinsetPos T,
        ((analyticOrderAt xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (by split_ifs <;> norm_num)
  have hrefl := two_mul_sum_right_add_simple_le (T₁ := T) (T₂ := 2 * T)
  have hZT := hZ T hTZ
  have hNdy := window_mult_sum_eq (T₁ := T) (T₂ := 2 * T) (by linarith)
  rw [hNdy] at hrefl hZT
  -- the edge counts
  have hcast : ∀ t : ℝ, 0 ≤ t → ((xiPosZeroCount t : ℕ) : ℝ) = ((xiZeroCount t : ℤ) : ℝ) := by
    intro t ht
    have := xiPosZeroCount_eq_xiZeroCount ht
    exact_mod_cast this
  have hE₁ : (xiPosZeroCount T₁ : ℝ) - xiPosZeroCount T
      ≤ 1 / (2 * Real.pi) * Real.log (T + 1) + 2 * Cc * Real.log (T + 1) := by
    have h := hceil T hTc' 1 (by norm_num)
    rw [← hcast (T + 1) (by linarith), ← hcast T hT0.le] at h
    have hmono : (xiPosZeroCount T₁ : ℝ) ≤ xiPosZeroCount (T + 1) := by
      exact_mod_cast Finset.sum_le_sum_of_subset (stripFinsetPos_mono hT₁hi.le)
    have e : (1 : ℝ) / (2 * Real.pi) * Real.log (T + 1) = 1 / (2 * Real.pi) * Real.log (T + 1) :=
      rfl
    linarith
  have hE₂ : (xiPosZeroCount (2 * T) : ℝ) - xiPosZeroCount T₂
      ≤ 1 / (2 * Real.pi) * Real.log (2 * T) + 2 * Cc * Real.log (2 * T) := by
    have h := hceil (2 * T - 1) (by linarith) 1 (by norm_num)
    rw [show 2 * T - 1 + 1 = 2 * T by ring, ← hcast (2 * T) (by linarith),
      ← hcast (2 * T - 1) (by linarith)] at h
    have hmono : (xiPosZeroCount (2 * T - 1) : ℝ) ≤ xiPosZeroCount T₂ := by
      exact_mod_cast Finset.sum_le_sum_of_subset (stripFinsetPos_mono (by linarith))
    linarith
  have hlog1 : Real.log (T + 1) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
  have hlog2T : Real.log (2 * T) ≤ 2 * Real.log T := by
    have h2T : 2 * T ≤ T ^ 2 := by
      have := mul_le_mul_of_nonneg_left hT2 hT0.le
      nlinarith only [this]
    have := Real.log_le_log (by linarith) h2T
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  obtain ⟨Ec, hEc⟩ : ∃ Ec : ℝ, Ec = (1 / (2 * Real.pi) + 2 * Cc) * (2 * Real.log (2 * T)) :=
    ⟨_, rfl⟩
  have hright : ∑ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁,
        ((analyticOrderAt xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)
      ≤ (1 - p) / 2 * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) + Ec := by
    have hNw : (xiPosZeroCount (2 * T) : ℝ) - xiPosZeroCount T
        ≤ ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) + Ec := by
      rw [hEc]
      have hc4 : 0 ≤ 1 / (2 * Real.pi) + 2 * Cc := by positivity
      have h1 := mul_le_mul_of_nonneg_left hlog1 hc4
      have e1 : 1 / (2 * Real.pi) * Real.log (T + 1) + 2 * Cc * Real.log (T + 1)
          = (1 / (2 * Real.pi) + 2 * Cc) * Real.log (T + 1) := by ring
      have e2 : 1 / (2 * Real.pi) * Real.log (2 * T) + 2 * Cc * Real.log (2 * T)
          = (1 / (2 * Real.pi) + 2 * Cc) * Real.log (2 * T) := by ring
      have e3 : (1 / (2 * Real.pi) + 2 * Cc) * (2 * Real.log (2 * T))
          = 2 * ((1 / (2 * Real.pi) + 2 * Cc) * Real.log (2 * T)) := by ring
      linarith only [hE₁, hE₂, h1, e1, e2, e3]
    have hq : 0 ≤ (1 - p) / 2 := by linarith only [hp1]
    have hq1 : (1 - p) / 2 ≤ 1 := by linarith only [hp0]
    have hRdy : ∑ z ∈ stripFinsetPos (2 * T) \ stripFinsetPos T,
          ((analyticOrderAt xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)
        ≤ (1 - p) / 2 * ((xiPosZeroCount (2 * T) : ℝ) - xiPosZeroCount T) := by
      rw [hpdef]
      linarith only [hrefl, hZT]
    have h3 := mul_le_mul_of_nonneg_left hNw hq
    have hEc0 : 0 ≤ Ec := by
      rw [hEc]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith only [hT2])
      positivity
    have h4 : (1 - p) / 2 * Ec ≤ Ec := by
      have := mul_le_mul_of_nonneg_right hq1 hEc0
      linarith only [this]
    have e5 : (1 - p) / 2 * (((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) + Ec)
        = (1 - p) / 2 * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) + (1 - p) / 2 * Ec := by
      ring
    linarith only [hRmono, hRdy, h3, h4, e5]
  have hX : 4 * Real.pi * (R / Real.log T₂ * Ec) ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := by
    have hlogT₂ : Real.log T ≤ Real.log T₂ :=
      Real.log_le_log hT0 (by linarith only [hT₁lo, hT₁₂])
    have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith only [hT2])
    have h1 : R / Real.log T₂ * Ec ≤ R * (8 * (1 / (2 * Real.pi) + 2 * Cc)) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith only [hlogT₂, hlogTpos])]
      rw [hEc]
      have hc4 : 0 ≤ 1 / (2 * Real.pi) + 2 * Cc := by positivity
      have hl : 2 * Real.log (2 * T) ≤ 8 * Real.log T₂ := by
        linarith only [hlog2T, hlogT₂, hlogTpos]
      have h5 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl hc4) hR.le
      calc R * ((1 / (2 * Real.pi) + 2 * Cc) * (2 * Real.log (2 * T)))
          ≤ R * ((1 / (2 * Real.pi) + 2 * Cc) * (8 * Real.log T₂)) := h5
        _ = R * (8 * (1 / (2 * Real.pi) + 2 * Cc)) * Real.log T₂ := by ring
    calc 4 * Real.pi * (R / Real.log T₂ * Ec) ≤ 4 * Real.pi * (R * (8 * (1 / (2 * Real.pi) +
          2 * Cc))) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = B := by rw [hB]; ring
      _ ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := hB'
  have h := window_moment_of_littlewood_dyadic hp0 hp1 hR hη'0 hc0 hlogc hK hCR hC hbb1
    hL₀a hL₀b hA hT0 hlogTL hratio hA' hK' hX hT2425 hH1 le_rfl hT₁lo hT₁hi hT₂lo hT₂hi
    (by omega) (ZetaGateProductAFE.mollUpper_le (by linarith only [hT0])) hlit₀ hNlo hright
  rw [show T + T - 1 = 2 * T - 1 by ring] at h
  refine h.trans ?_
  have : Real.log c - (1 + p) * R + η' ≤ Real.log c - 5 / 3 * R + η := by
    rw [hpdef, hη']
    have e : (1 + (2 / 3 - ε)) * R = 5 / 3 * R - ε * R := by ring
    linarith only [e, hεR, hη]
  exact mul_le_mul_of_nonneg_right this hT0.le

/-- **The off-line moment of every dyadic window is at most `67/1000` of its length.** -/
theorem eventually_dyadicWindowTail_le_sixtySeven_thousandths :
    ∀ᶠ T in atTop, windowTail 0 (T + 1) (2 * T - 1) ≤ 67 / 1000 * T := by
  filter_upwards [eventually_dyadicWindowTail_le_selberg_upper (R := 3 / 2) (η := 1 / 1000)
    (by norm_num) (by norm_num), eventually_ge_atTop (0 : ℝ)] with T hT hT0
  have hc := ZetaGateProductAFE.log_selbergBlockConstUpper_three_halves_le
  have hπ : 0 < 4 * Real.pi := by positivity
  have h1 : 4 * Real.pi * windowTail 0 (T + 1) (2 * T - 1) ≤ 4 * Real.pi * (67 / 1000) * T :=
    hT.trans (mul_le_mul_of_nonneg_right hc hT0)
  have h2 : 4 * Real.pi * (67 / 1000) * T = 4 * Real.pi * (67 / 1000 * T) := by ring
  rw [h2] at h1
  exact le_of_mul_le_mul_left h1 hπ

end

end RHTower
