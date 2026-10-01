import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergNinth
import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailFromGate
import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder

/-!
# The off-line tail law in every window `[T, T + T^{24/25}]`

The high-block bound in window form (`exists_highBlock_bound_of_mainTerm_deep_window`) loses only
the taper `2a^{19/20}`, so Selberg's twisted mollifier of length `U^{1/9}` has mean square
`c_R = e^{2R}/(1 − e^{−2R/9})` per unit length on every window of length `≫ a^{19/20}`
(`eventually_window_meanSquare_selberg_ninth`).  Littlewood's lemma on the wide rectangle
`[½ − R/log T₂, 15/2] × [T₁, T₂]`, the reflection count identity and the Riemann–von Mangoldt
formula with remainder `O(log T)` then localize the tail law of `ZetaCriticalScaleTailFromGate`:
for every `η > 0`, all large `T` and every `T^{24/25} ≤ H ≤ T`,

* `4π Σ_{T+1 < Im ρ ≤ T+H−1} m_ρ (Re ρ − ½ − R/log(T+H−1))⁺ ≤ (log c_R − 2R + η) H`,
* `4π Σ_{T+1 < Im ρ ≤ T+H−1} m_ρ (Re ρ − ½)⁺ ≤ (log c_R − R + η) H`

(`eventually_windowTail_le_selberg_ninth`).  The second bound uses only that at most half of the
zeros in a window lie right of the line (reflection), not the two-thirds proportion of simple
critical zeros, which is a global statement.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-! ## Window sums of the off-line tail -/

/-- `Σ_{T₁ < Im ρ ≤ T₂} m_ρ (Re ρ − ½ − d)⁺` over the zeros of `ξ` in the strip. -/
def windowTail (d T₁ T₂ : ℝ) : ℝ := offLineTail d T₂ - offLineTail d T₁

theorem windowTail_eq_sum {d T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    windowTail d T₁ T₂ = ∑ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁,
      ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2 - d) 0 := by
  unfold windowTail offLineTail
  have h := Finset.sum_sdiff (f := fun z => ((analyticOrderAt xi z).toNat : ℝ) *
    max (z.re - 1 / 2 - d) 0) (stripFinsetPos_mono hT)
  linarith [h]

theorem windowTail_mono {d T₁ T₂ T₁' T₂' : ℝ} (h₁ : T₁' ≤ T₁) (h₂ : T₂ ≤ T₂') :
    windowTail d T₁ T₂ ≤ windowTail d T₁' T₂' := by
  unfold windowTail
  linarith [offLineTail_mono (d := d) h₁, offLineTail_mono (d := d) h₂]

theorem windowTail_anti {d d' T₁ T₂ : ℝ} (hd : d ≤ d') (hT : T₁ ≤ T₂) :
    windowTail d' T₁ T₂ ≤ windowTail d T₁ T₂ := by
  rw [windowTail_eq_sum hT, windowTail_eq_sum hT]
  exact Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left
    (max_le_max (by linarith) le_rfl) (Nat.cast_nonneg _)

/-- At most half of the zero copies in a window lie strictly right of the critical line. -/
theorem two_mul_sum_right_le_count {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    2 * ∑ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁,
        ((analyticOrderAt xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)
      ≤ (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁ := by
  classical
  set S := stripFinsetPos T₂ \ stripFinsetPos T₁ with hS
  set m : ℂ → ℝ := fun z => ((analyticOrderAt xi z).toNat : ℝ) with hm
  have hN : (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁ = ∑ z ∈ S, m z := by
    unfold xiPosZeroCount
    have h := Finset.sum_sdiff (f := fun z => ((analyticOrderAt xi z).toNat : ℝ))
      (stripFinsetPos_mono hT)
    push_cast
    linarith [h]
  have hmr : ∀ z, m (lineReflect z) = m z := fun z => by simp only [hm, xi_orderAt_lineReflect]
  have hrefl := sum_lineReflect_eq (fun z hz => lineReflect_mem_window hz)
    (t := S) (fun z => m z * (if 1 / 2 < z.re then 1 else 0))
  simp only [hmr, lineReflect_re] at hrefl
  rw [hN, two_mul]
  nth_rewrite 1 [← hrefl]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  have hm0 : 0 ≤ m z := Nat.cast_nonneg _
  split_ifs with h1 h2 h2
  · linarith
  · linarith
  · linarith
  · linarith

/-- `Σ m (Re ρ − ½)⁺ ≤ Σ m (Re ρ − ½ − d)⁺ + (d/2)(N(T₂) − N(T₁))` over a window. -/
theorem windowTail_zero_le {d T₁ T₂ : ℝ} (hd : 0 ≤ d) (hT : T₁ ≤ T₂) :
    windowTail 0 T₁ T₂
      ≤ windowTail d T₁ T₂ + d / 2 * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) := by
  have hhalf := two_mul_sum_right_le_count hT
  rw [windowTail_eq_sum hT, windowTail_eq_sum hT]
  have hpt : ∀ z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁,
      ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2 - 0) 0
        ≤ ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2 - d) 0
          + d * (((analyticOrderAt xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)) := by
    intro z _
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
    linarith [this]
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hd2 := mul_le_mul_of_nonneg_left hhalf hd
  nlinarith [hsum, hd2]

/-! ## Riemann–von Mangoldt on windows -/

/-- `T₂ log(T₂/b) − T₁ log(T₁/b)` lies between `(T₂ − T₁)(log(T₁/b) + 1)` and
`(T₂ − T₁)(log(T₂/b) + 1)` (convexity of `T log T`). -/
theorem mul_log_div_sub_bounds {b T₁ T₂ : ℝ} (hb : 0 < b) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂) :
    (T₂ - T₁) * (Real.log (T₁ / b) + 1) ≤ T₂ * Real.log (T₂ / b) - T₁ * Real.log (T₁ / b) ∧
    T₂ * Real.log (T₂ / b) - T₁ * Real.log (T₁ / b) ≤ (T₂ - T₁) * (Real.log (T₂ / b) + 1) := by
  have hT₂ : 0 < T₂ := lt_of_lt_of_le hT₁ hT
  have hl₁ : Real.log (T₁ / b) = Real.log T₁ - Real.log b := Real.log_div hT₁.ne' hb.ne'
  have hl₂ : Real.log (T₂ / b) = Real.log T₂ - Real.log b := Real.log_div hT₂.ne' hb.ne'
  have hq : Real.log (T₂ / T₁) = Real.log T₂ - Real.log T₁ := Real.log_div hT₂.ne' hT₁.ne'
  have hlow : 1 - T₁ / T₂ ≤ Real.log (T₂ / T₁) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hT₂ hT₁)
    rwa [inv_div] at h
  have hup : Real.log (T₂ / T₁) ≤ T₂ / T₁ - 1 := Real.log_le_sub_one_of_pos (div_pos hT₂ hT₁)
  rw [hl₁, hl₂]
  constructor
  · have h1 : T₂ * (1 - T₁ / T₂) ≤ T₂ * Real.log (T₂ / T₁) := mul_le_mul_of_nonneg_left hlow hT₂.le
    have e : T₂ * (1 - T₁ / T₂) = T₂ - T₁ := by field_simp
    rw [e, hq] at h1
    nlinarith [h1]
  · have h1 : T₁ * Real.log (T₂ / T₁) ≤ T₁ * (T₂ / T₁ - 1) := mul_le_mul_of_nonneg_left hup hT₁.le
    have e : T₁ * (T₂ / T₁ - 1) = T₂ - T₁ := by field_simp
    rw [e, hq] at h1
    nlinarith [h1]

/-- **Riemann–von Mangoldt on windows.**  For `T₀ ≤ T₁ ≤ T₂`,
`(T₂ − T₁)(log(T₁/2πe) + 1)/2π − C(log T₁ + log T₂) ≤ N(T₂) − N(T₁)
  ≤ (T₂ − T₁)(log(T₂/2πe) + 1)/2π + C(log T₁ + log T₂)`. -/
theorem exists_xiPosZeroCount_window_bounds :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ T₁ T₂ : ℝ, T₀ ≤ T₁ → T₁ ≤ T₂ →
      (T₂ - T₁) * (Real.log (T₁ / routeKRVMBase) + 1) / (2 * Real.pi)
          - C * (Real.log T₁ + Real.log T₂)
        ≤ (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁ ∧
      (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁
        ≤ (T₂ - T₁) * (Real.log (T₂ / routeKRVMBase) + 1) / (2 * Real.pi)
          + C * (Real.log T₁ + Real.log T₂) := by
  obtain ⟨C, hC, T₀, hT₀, hrvm⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  refine ⟨C, hC, T₀, hT₀, fun T₁ T₂ hT₁ hT => ?_⟩
  have hT₁0 : 0 < T₁ := by linarith
  have hcast : ∀ T : ℝ, 0 ≤ T → ((xiZeroCount T : ℤ) : ℝ) = (xiPosZeroCount T : ℝ) := by
    intro T hT
    rw [← xiPosZeroCount_eq_xiZeroCount hT]
    simp
  have h₁ := hrvm T₁ hT₁
  have h₂ := hrvm T₂ (le_trans hT₁ hT)
  rw [hcast T₁ hT₁0.le] at h₁
  rw [hcast T₂ (by linarith)] at h₂
  obtain ⟨hlow, hup⟩ := mul_log_div_sub_bounds routeKRVMBase_pos hT₁0 hT
  have hπ : 0 < 2 * Real.pi := by positivity
  have hdiff : routeKSmoothRVMCount T₂ - routeKSmoothRVMCount T₁
      = (T₂ * Real.log (T₂ / routeKRVMBase) - T₁ * Real.log (T₁ / routeKRVMBase))
        / (2 * Real.pi) := by
    unfold routeKSmoothRVMCount
    field_simp
    ring
  have hlo : (T₂ - T₁) * (Real.log (T₁ / routeKRVMBase) + 1) / (2 * Real.pi)
      ≤ routeKSmoothRVMCount T₂ - routeKSmoothRVMCount T₁ := by
    rw [hdiff]
    exact div_le_div_of_nonneg_right hlow hπ.le
  have hhi : routeKSmoothRVMCount T₂ - routeKSmoothRVMCount T₁
      ≤ (T₂ - T₁) * (Real.log (T₂ / routeKRVMBase) + 1) / (2 * Real.pi) := by
    rw [hdiff]
    exact div_le_div_of_nonneg_right hup hπ.le
  have a₁ := abs_le.mp h₁
  have a₂ := abs_le.mp h₂
  constructor
  · linarith [a₁.2, a₂.1]
  · linarith [a₁.1, a₂.2]

/-! ## The mean square on short windows -/

namespace ZetaGateProductAFE

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- **The mollified mean square on windows.**  With Selberg's twisted coefficients of length
`U^{1/9}`, for `U` large, every displacement `d` with `R ≤ d log U`, `d log(U − 1) ≤ R` and every
window `U^{7/8} ≤ a ≤ v ≤ 2a`, `v ≤ U`:
`∫_a^v ‖ζΨ(½ − d + iτ)‖² dτ ≤ (c_R + ε)(v − a + 2a^{19/20})`. -/
theorem eventually_window_meanSquare_selberg_ninth {R : ℝ} (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((7 : ℝ) / 8) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((selbergRealNinth R U n : ℝ) : ℂ)) (Finset.Icc 1 (mollNinth U))
                (displacedLinePt d τ)‖ ^ 2)
          ≤ (selbergBlockConstNinth R + ε) * (v - a + 2 * a ^ ((19 : ℝ) / 20)) := by
  have hN : ∀ᶠ U in atTop, (mollNinth U : ℝ) ≤ U ^ ((1 : ℝ) / 9) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with U hU
    exact mollNinth_le hU
  have hw : ∀ U, ∀ n ∈ Finset.Icc 1 (mollNinth U), |selbergRealNinth R U n| ≤ 1 := fun U n hn =>
    Sieve.abs_twistedWeight_le _ _ (Finset.mem_Icc.mp hn).1
  have hmain : ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U →
      d * Real.log (U - 1) ≤ R → ∀ a v η : ℝ, 0 < η → 4 ≤ a - η → a ≤ v → v ≤ U → η ≤ a →
      a / 2 ≤ a - η → U ^ ((1 : ℝ) / 8) ≤ a →
      gcdSum₂ d (mollNinth U) (selbergRealNinth R U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
        ≤ (v - a + 2 * η) * selbergBlockFactorNinth R U := by
    filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 9)] with U hU
    intro d hd hd8 hRd hdU1 a v η hη h4 hav hvU hηa haη haU
    have hU3 : (3 : ℝ) ≤ U := le_trans (by norm_num) hU
    exact selberg_mainTerm_le_ninth hR hd hd8 hRd hdU1 hU3 (two_le_mollNinth hU) hη h4 hav hvU hηa
      haη haU
  exact exists_highBlock_bound_of_mainTerm_deep_window hR (tendsto_selbergBlockFactorNinth hR)
    mollNinth (selbergRealNinth R) hN hw hmain ε hε

end ZetaGateProductAFE

/-! ## The tail law on windows -/

theorem one_le_selbergBlockConstNinth {R : ℝ} (hR : 0 < R) :
    1 ≤ ZetaGateProductAFE.selbergBlockConstNinth R := by
  unfold ZetaGateProductAFE.selbergBlockConstNinth
  have h1 : 0 < Real.exp (-(2 * R / 9)) := Real.exp_pos _
  have h2 := ZetaGateProductAFE.exp_neg_lt_one (show 0 < 2 * R / 9 by positivity)
  rw [le_div_iff₀ (by linarith)]
  have h3 : 1 ≤ Real.exp (2 * R) := Real.one_le_exp (by positivity)
  linarith

/-- `log c_R ≥ 2R`, since `c_R ≥ e^{2R}`. -/
theorem two_mul_le_log_selbergBlockConstNinth {R : ℝ} (hR : 0 < R) :
    2 * R ≤ Real.log (ZetaGateProductAFE.selbergBlockConstNinth R) := by
  unfold ZetaGateProductAFE.selbergBlockConstNinth
  have h1 : 0 < Real.exp (-(2 * R / 9)) := Real.exp_pos _
  have h2 := ZetaGateProductAFE.exp_neg_lt_one (show 0 < 2 * R / 9 by positivity)
  rw [Real.log_div (Real.exp_pos _).ne' (by linarith), Real.log_exp]
  have : Real.log (1 - Real.exp (-(2 * R / 9))) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  linarith

/-! ### Scalar steps of the window tail law -/

/-- `U^{7/8} ≤ T` when `U ≤ 2T` and `T ≥ 2⁹`. -/
theorem rpow_seven_eighths_le_of_le_two_mul {T U : ℝ} (hT9 : (2 : ℝ) ^ 9 ≤ T) (hU0 : 0 ≤ U)
    (hU : U ≤ 2 * T) : U ^ ((7 : ℝ) / 8) ≤ T := by
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT9
  have h1 : U ^ ((7 : ℝ) / 8) ≤ (2 * T) ^ ((7 : ℝ) / 8) :=
    Real.rpow_le_rpow hU0 hU (by norm_num)
  have h2 : (2 * T) ^ ((7 : ℝ) / 8) = (2 : ℝ) ^ ((7 : ℝ) / 8) * T ^ ((7 : ℝ) / 8) :=
    Real.mul_rpow (by norm_num) hT0.le
  have h3 : (2 : ℝ) ^ ((7 : ℝ) / 8) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (7 : ℝ) / 8 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have h4 : 2 ≤ T ^ ((1 : ℝ) / 8) := by
    have e : ((2 : ℝ) ^ 9) ^ ((1 : ℝ) / 8) = (2 : ℝ) ^ ((9 : ℝ) / 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have h5 : (2 : ℝ) ^ ((9 : ℝ) / 8) ≤ T ^ ((1 : ℝ) / 8) := by
      rw [← e]; exact Real.rpow_le_rpow (by positivity) hT9 (by norm_num)
    have h6 : (2 : ℝ) ≤ (2 : ℝ) ^ ((9 : ℝ) / 8) := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (1 : ℝ) ≤ 9 / 8 by norm_num)
      rwa [Real.rpow_one] at this
    linarith
  have hsplit : T = T ^ ((7 : ℝ) / 8) * T ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_add hT0]; norm_num
  have h7 : 0 ≤ T ^ ((7 : ℝ) / 8) := Real.rpow_nonneg hT0.le _
  have h8 : 2 * T ^ ((7 : ℝ) / 8) ≤ T := by
    calc 2 * T ^ ((7 : ℝ) / 8) ≤ T ^ ((1 : ℝ) / 8) * T ^ ((7 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_right h4 h7
      _ = T := by rw [mul_comm]; exact hsplit.symm
  have h9 : (2 : ℝ) ^ ((7 : ℝ) / 8) * T ^ ((7 : ℝ) / 8) ≤ 2 * T ^ ((7 : ℝ) / 8) :=
    mul_le_mul_of_nonneg_right h3 h7
  linarith

/-- The taper is negligible: `2 T₁^{19/20} ≤ (η/8) Δ` once `T₁ ≤ 2T`, `Δ ≥ T^{24/25}/2` and
`8 T^{−1/100} ≤ η/8`. -/
theorem two_mul_rpow_taper_le {T T₁ Δ η : ℝ} (hT0 : 0 < T) (hη : 0 < η) (hT₁0 : 0 ≤ T₁)
    (hT₁ : T₁ ≤ 2 * T) (hΔ : T ^ ((24 : ℝ) / 25) / 2 ≤ Δ)
    (hratio : 8 * T ^ (-((1 : ℝ) / 100)) ≤ η / 8) :
    2 * T₁ ^ ((19 : ℝ) / 20) ≤ η / 8 * Δ := by
  have hT1920 : T ^ ((19 : ℝ) / 20) = T ^ (-((1 : ℝ) / 100)) * T ^ ((24 : ℝ) / 25) := by
    rw [← Real.rpow_add hT0]; norm_num
  have h1 : T₁ ^ ((19 : ℝ) / 20) ≤ (2 * T) ^ ((19 : ℝ) / 20) :=
    Real.rpow_le_rpow hT₁0 hT₁ (by norm_num)
  have h2 : (2 * T) ^ ((19 : ℝ) / 20) = (2 : ℝ) ^ ((19 : ℝ) / 20) * T ^ ((19 : ℝ) / 20) :=
    Real.mul_rpow (by norm_num) hT0.le
  have h3 : (2 : ℝ) ^ ((19 : ℝ) / 20) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (19 : ℝ) / 20 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have h4 : 0 ≤ T ^ ((19 : ℝ) / 20) := Real.rpow_nonneg hT0.le _
  have h5 : T₁ ^ ((19 : ℝ) / 20) ≤ 2 * T ^ ((19 : ℝ) / 20) := by
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h3 h4)
  have h7 : 0 ≤ T ^ ((24 : ℝ) / 25) := Real.rpow_nonneg hT0.le _
  have h8 : 4 * T ^ ((19 : ℝ) / 20) ≤ η / 16 * T ^ ((24 : ℝ) / 25) := by
    rw [hT1920]
    have h6 : 4 * T ^ (-((1 : ℝ) / 100)) ≤ η / 16 := by linarith only [hratio]
    have := mul_le_mul_of_nonneg_right h6 h7
    linarith only [this]
  have h9 := mul_le_mul_of_nonneg_left hΔ (by positivity : (0 : ℝ) ≤ η / 8)
  linarith only [h5, h8, h9]

/-- `log(Msq/Δ) ≤ log c + η/4` for `Msq = c(1 + η/8)(Δ + 2T₁^{19/20})` with a negligible taper. -/
theorem log_meanSquare_div_le {c η Δ τ : ℝ} (hc : 0 < c) (hη : 0 < η) (hΔ : 0 < Δ)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ η / 8 * Δ) :
    Real.log (c * (1 + η / 8) * (Δ + τ) / Δ) ≤ Real.log c + η / 4 := by
  have h1 : c * (1 + η / 8) * (Δ + τ) / Δ ≤ c * (1 + η / 8) ^ 2 := by
    rw [div_le_iff₀ hΔ]
    have : Δ + τ ≤ (1 + η / 8) * Δ := by linarith only [hτ]
    have h := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ c * (1 + η / 8))
    nlinarith [h]
  have hpos : 0 < c * (1 + η / 8) * (Δ + τ) / Δ := by positivity
  have h2 := Real.log_le_log hpos h1
  have h3 : Real.log (c * (1 + η / 8) ^ 2) = Real.log c + 2 * Real.log (1 + η / 8) := by
    rw [Real.log_mul hc.ne' (by positivity), Real.log_pow]; push_cast; ring
  have h4 : Real.log (1 + η / 8) ≤ η / 8 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + η / 8 by positivity)
    linarith only [this]
  linarith only [h2, h3, h4]

/-- Riemann–von Mangoldt scaled by `2πd`, `d = R/log T₂`: the lower bound
`Δ(R − η/16) − 4πC R ≤ 2πd·(N(T₂) − N(T₁))`. -/
theorem two_pi_mul_count_window_ge {R η d CR Δ ΔN T₁ T₂ bb : ℝ} (hd0 : 0 ≤ d) (hCR : 0 ≤ CR)
    (hΔ : 0 ≤ Δ) (hdlog : d * Real.log T₂ = R) (hlogT₁ : Real.log T₂ - Real.log 2 ≤ Real.log T₁)
    (hlogT₁T₂ : Real.log T₁ ≤ Real.log T₂) (hlogdiv : Real.log (T₁ / bb) = Real.log T₁ - Real.log bb)
    (hdsmall : d * (Real.log 2 + Real.log bb) ≤ η / 16)
    (hN : Δ * (Real.log (T₁ / bb) + 1) / (2 * Real.pi) - CR * (Real.log T₁ + Real.log T₂) ≤ ΔN) :
    Δ * (R - η / 16) - 4 * Real.pi * CR * R ≤ 2 * Real.pi * d * ΔN := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h1 : R - η / 16 ≤ d * (Real.log (T₁ / bb) + 1) := by
    rw [hlogdiv]
    have : d * (Real.log T₂ - Real.log 2 - Real.log bb) ≤ d * (Real.log T₁ - Real.log bb + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlogT₁]) hd0
    have e : d * (Real.log T₂ - Real.log 2 - Real.log bb)
        = d * Real.log T₂ - d * (Real.log 2 + Real.log bb) := by ring
    linarith only [this, e, hdlog, hdsmall]
  have h2 : 2 * Real.pi * d * (CR * (Real.log T₁ + Real.log T₂)) ≤ 4 * Real.pi * CR * R := by
    have : CR * (Real.log T₁ + Real.log T₂) ≤ CR * (2 * Real.log T₂) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlogT₁T₂]) hCR
    have h3 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * Real.pi * d)
    have e : 2 * Real.pi * d * (CR * (2 * Real.log T₂)) = 4 * Real.pi * CR * (d * Real.log T₂) := by
      ring
    rw [e, hdlog] at h3
    exact h3
  have h3 := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ 2 * Real.pi * d)
  have e : 2 * Real.pi * d * (Δ * (Real.log (T₁ / bb) + 1) / (2 * Real.pi)
      - CR * (Real.log T₁ + Real.log T₂))
      = Δ * (d * (Real.log (T₁ / bb) + 1))
        - 2 * Real.pi * d * (CR * (Real.log T₁ + Real.log T₂)) := by
    field_simp
  rw [e] at h3
  have h4 := mul_le_mul_of_nonneg_left h1 hΔ
  linarith only [h2, h3, h4]

/-- The assembly of the window tail law: Littlewood, the reflection bridge and the two
Riemann–von Mangoldt bounds give both window bounds. -/
theorem window_tail_moment_combine {S tl W0 dN Δ H L E logc R η : ℝ}
    (hΔ : 0 ≤ Δ) (hΔH : Δ ≤ H) (hlogc : 2 * R ≤ logc) (hR : 0 ≤ R) (hη : 0 < η)
    (hlit : 2 * Real.pi * S ≤ Δ / 2 * (logc + η / 4) + L)
    (hbridge : dN / (2 * Real.pi) + tl ≤ S)
    (hlow : Δ * (R - η / 16) - E ≤ dN)
    (hW0 : W0 ≤ tl + dN / (4 * Real.pi))
    (hadd : 2 * L + 3 * E ≤ η / 8 * Δ) (hL : 0 ≤ L) (hE : 0 ≤ E) :
    4 * Real.pi * tl ≤ (logc - 2 * R + η) * H ∧ 4 * Real.pi * W0 ≤ (logc - R + η) * H := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hb : 2 * Real.pi * (dN / (2 * Real.pi)) + 2 * Real.pi * tl ≤ 2 * Real.pi * S := by
    have := mul_le_mul_of_nonneg_left hbridge (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    linarith only [this]
  have e1 : 2 * Real.pi * (dN / (2 * Real.pi)) = dN := by field_simp
  rw [e1] at hb
  have htl : 4 * Real.pi * tl ≤ (logc - 2 * R + η / 2) * Δ := by
    linarith only [hb, hlit, hlow, hadd, hL, hE, hη, hΔ]
  have hW : 4 * Real.pi * W0 ≤ (logc - R + η / 2 + η / 8) * Δ := by
    have h1 := mul_le_mul_of_nonneg_left hW0 (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    have e2 : 4 * Real.pi * (tl + dN / (4 * Real.pi)) = 4 * Real.pi * tl + dN := by field_simp
    rw [e2] at h1
    linarith only [h1, hb, hlit, hlow, hadd, hL, hE, hη, hΔ]
  constructor
  · have h1 : 0 ≤ logc - 2 * R + η / 2 := by linarith only [hlogc, hη]
    have := mul_le_mul_of_nonneg_left hΔH h1
    nlinarith only [htl, this, hη, hΔ, hΔH]
  · have h1 : 0 ≤ logc - R + η / 2 + η / 8 := by linarith only [hlogc, hη, hR]
    have := mul_le_mul_of_nonneg_left hΔH h1
    nlinarith only [hW, this, hη, hΔ, hΔH]

/-- **Littlewood's lemma on an admissible window.**  For `2⁹ ≤ T`, `4 ≤ H ≤ T` and
`log T ≥ 8R`, given the window mean square of Selberg's coefficients at `U = T + H` with
constant `c` and the wide-rectangle Littlewood bound, there are admissible heights
`T < T₁ < T + 1`, `T + H − 1 < T₂ < T + H` with, for `d = R/log T₂`,
`2π(d(N(T₂) − N(T₁)) + Σ_{T₁<Im ρ≤T₂} m_ρ(Re ρ − ½ − d)⁺)
  ≤ ((T₂−T₁)/2) log(c(T₂ − T₁ + 2T₁^{19/20})/(T₂ − T₁)) + C + K(log T₂ + log N⁵)`. -/
theorem exists_window_littlewood {R c C K T H : ℝ} (hR : 0 < R)
    (hwide : ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc σ₀ (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb))
    (hT9 : (2 : ℝ) ^ 9 ≤ T) (hH4 : 4 ≤ H) (hHT : H ≤ T) (hlogT : 8 * R ≤ Real.log T)
    (hms : ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log (T + H) →
      d * Real.log (T + H - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → (T + H) ^ ((7 : ℝ) / 8) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ T + H →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((ZetaGateProductAFE.selbergRealNinth R (T + H) n : ℝ) : ℂ))
                (Finset.Icc 1 (ZetaGateProductAFE.mollNinth (T + H))) (displacedLinePt d τ)‖ ^ 2)
          ≤ c * (v - a + 2 * a ^ ((19 : ℝ) / 20))) :
    ∃ T₁ T₂ : ℝ, T < T₁ ∧ T₁ < T + 1 ∧ T + H - 1 < T₂ ∧ T₂ < T + H ∧
      2 * Real.pi * (R / Real.log T₂ * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)
          + windowTail (R / Real.log T₂) T₁ T₂)
        ≤ (T₂ - T₁) / 2 * Real.log (c * (T₂ - T₁ + 2 * T₁ ^ ((19 : ℝ) / 20)) / (T₂ - T₁))
          + C + K * (Real.log T₂
            + Real.log ((ZetaGateProductAFE.mollNinth (T + H) : ℝ) ^ (5 : ℕ))) := by
  classical
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = T + H := ⟨_, rfl⟩
  rw [← hUdef] at hms ⊢
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT9
  have hU2T : U ≤ 2 * T := by linarith
  have hU9 : (2 : ℝ) ^ 9 ≤ U := by linarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ZetaGateProductAFE.mollNinth U := ⟨_, rfl⟩
  rw [← hNdef] at hms ⊢
  obtain ⟨b, hbdef⟩ : ∃ b : ℕ → ℂ,
      b = fun n => ((ZetaGateProductAFE.selbergRealNinth R U n : ℝ) : ℂ) := ⟨_, rfl⟩
  rw [← hbdef] at hms
  have hN2 : 2 ≤ N := hNdef ▸ ZetaGateProductAFE.two_le_mollNinth hU9
  have hN1 : 1 ≤ N := by omega
  have hw : ∀ n ∈ Finset.Icc 1 N, |ZetaGateProductAFE.selbergRealNinth R U n| ≤ 1 :=
    fun n hn => Sieve.abs_twistedWeight_le _ _ (Finset.mem_Icc.mp hn).1
  have hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1 := by
    rw [hbdef]; exact ZetaGateProductAFE.norm_ofReal_coeff_le hw
  have hb1 : b 1 = 1 := by
    rw [hbdef]
    simp only [ZetaGateProductAFE.selbergRealNinth, Sieve.twistedWeight_one, Complex.ofReal_one]
  have hbreal : ∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n := fun n _ => by
    rw [hbdef]; exact Complex.conj_ofReal _
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1mem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN1⟩
  have hΨan : AnalyticOnNhd ℂ (edPoly b (Finset.Icc 1 N)) Set.univ := analyticOnNhd_edPoly b hs
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ,
      F = fun z => levinsonGEntire (((0 : ℝ) : ℝ) : ℂ) z * edPoly b (Finset.Icc 1 N) z :=
    ⟨_, rfl⟩
  have hFan : AnalyticOnNhd ℂ F Set.univ := by
    rw [hFdef]
    exact fun z hz => ((analyticOnNhd_levinsonGEntire _) z hz).mul (hΨan z hz)
  have hlamC : ‖(((0 : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by simp
  have hΨright : edPoly b (Finset.Icc 1 N) (((15 / 2 : ℝ) : ℂ)) ≠ 0 := by
    intro h0
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs h1mem hb1 hbn
      (z := ((15 / 2 : ℝ) : ℂ)) (by simp; norm_num)
    rw [h0] at h
    norm_num at h
  have hFne : ∃ z : ℂ, F z ≠ 0 := by
    refine ⟨((15 / 2 : ℝ) : ℂ), ?_⟩
    rw [hFdef]
    exact mul_ne_zero (levinsonGEntire_ne_zero_of_four_le hlamC (by simp; norm_num)) hΨright
  obtain ⟨T₁, hT₁, T₂, hT₂, hF1, hF2⟩ :=
    exists_horizontal_slices_avoiding_entire_zeros hFan hFne (c := (1 / 4 : ℝ)) (d := 15 / 2)
      (by norm_num) (by linarith : T < T + 1) (by linarith : T + 1 < U - 1)
      (by linarith : U - 1 < U)
  obtain ⟨hT₁lo, hT₁hi⟩ := hT₁
  obtain ⟨hT₂lo, hT₂hi⟩ := hT₂
  have hT12 : T₁ < T₂ := by linarith
  have hT₁0 : 0 < T₁ := by linarith
  have hT₂0 : 0 < T₂ := by linarith
  have h20 : 20 ≤ T₁ := by linarith [show (20 : ℝ) ≤ 2 ^ 9 by norm_num]
  have hlogT₂ : Real.log T ≤ Real.log T₂ := Real.log_le_log hT0 (by linarith)
  have hlogT₂pos : 0 < Real.log T₂ := by
    have : 0 < Real.log T := Real.log_pos (by linarith [show (1 : ℝ) < 2 ^ 9 by norm_num])
    linarith
  -- the abscissa
  obtain ⟨d, hdR⟩ : ∃ d : ℝ, d = R / Real.log T₂ := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hdR]; positivity
  have hdlog : d * Real.log T₂ = R := by rw [hdR]; field_simp
  have hd8 : d ≤ 1 / 8 := by
    rw [hdR, div_le_iff₀ hlogT₂pos]
    linarith
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ℝ, σ₀ = 1 / 2 - d := ⟨_, rfl⟩
  have hσ₀a : 1 / 4 ≤ σ₀ := by linarith
  have hσ₀b : σ₀ < 1 / 2 := by linarith
  have hlogT₂U : Real.log T₂ ≤ Real.log U := Real.log_le_log hT₂0 hT₂hi.le
  have hlogU1T₂ : Real.log (U - 1) ≤ Real.log T₂ := Real.log_le_log (by linarith) hT₂lo.le
  have hRd : R ≤ d * Real.log U := by
    have := mul_le_mul_of_nonneg_left hlogT₂U hd0.le
    linarith
  have hdU1 : d * Real.log (U - 1) ≤ R := by
    have := mul_le_mul_of_nonneg_left hlogU1T₂ hd0.le
    linarith
  have hU78 : U ^ ((7 : ℝ) / 8) ≤ T₁ :=
    (rpow_seven_eighths_le_of_le_two_mul hT9 (by linarith) hU2T).trans hT₁lo.le
  have hT₂2 : T₂ ≤ 2 * T₁ := by linarith
  -- edges
  have hedge : ∀ Tz : ℝ, 20 ≤ Tz →
      (∀ x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2), F ((x : ℂ) + (Tz : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (Tz : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), edPoly b (Finset.Icc 1 N) ((x : ℂ) + (Tz : ℂ) * I) ≠ 0) := by
    intro Tz hTz hF
    have hmem : ∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2) := by
      intro x hx
      rw [uIcc_of_le (by norm_num)]
      exact ⟨le_trans hσ₀a hx.1, hx.2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · intro h0
      apply hF x (hmem x hx)
      have hne1 : ((x : ℂ) + (Tz : ℂ) * I) ≠ 1 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        linarith
      rw [hFdef]
      show levinsonGEntire _ _ * _ = 0
      rw [levinsonGEntire_eq _ hne1]
      simp [levinsonG, h0]
    · intro h0
      apply hF x (hmem x hx)
      rw [hFdef]
      show _ * edPoly b (Finset.Icc 1 N) _ = 0
      rw [h0, mul_zero]
  obtain ⟨hG1, hP1⟩ := hedge T₁ h20 hF1
  obtain ⟨hG2, hP2⟩ := hedge T₂ (by linarith) hF2
  -- the mean square
  have hms' := hms d hd0 hd8 hRd hdU1 T₁ T₂ h20 hU78 hT12.le hT₂2 hT₂hi.le
  have hfun : (fun τ : ℝ => ‖riemannZeta (displacedLinePt d τ)
        * edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2)
      = fun t : ℝ => ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I)
        * edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    funext t
    have hpt : displacedLinePt d t = (σ₀ : ℂ) + (t : ℂ) * I := by
      have := displacedLinePt_half_sub σ₀ t
      rw [hσ₀, show (1 / 2 : ℝ) - (1 / 2 - d) = d by ring] at this
      rw [this, hσ₀]
    rw [hpt]
  rw [hfun] at hms'
  have hMb1 : (1 : ℝ) ≤ (N : ℝ) ^ (5 : ℕ) := one_le_pow₀ (by exact_mod_cast hN1)
  obtain ⟨Z, hZ⟩ := exists_zetaWideRectangleZeros_finset (σ₀ := σ₀) h20 hT12
  have hc := hwide b N hN1 hb1 hbn hbreal ((N : ℝ) ^ (5 : ℕ)) hMb1
    (ZetaGateProductAFE.sum_norm_mul_rpow_four_le hbn) σ₀ T₁ T₂ _ hσ₀a hσ₀b h20 hT12
    hG1 hG2 hP1 hP2 hms' Z hZ
  have hZ' : ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc (1 / 2 - d) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 := by
    rw [← hσ₀]; exact hZ
  have hbridge := window_count_add_tail_le_zetaWideSum hd0.le hT12.le Z hZ'
  rw [← hσ₀] at hbridge
  refine ⟨T₁, T₂, hT₁lo, hT₁hi, hT₂lo, hT₂hi, ?_⟩
  rw [← hdR]
  have hb2 := mul_le_mul_of_nonneg_left hbridge (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  unfold windowTail
  linarith only [hb2, hc]

/-- **The window analysis.**  The Littlewood bound on an admissible window `[T₁, T₂]`, the
Riemann–von Mangoldt lower bound and the size conditions give the two window bounds. -/
theorem window_bounds_of_littlewood {R η c C K CR T H T₁ T₂ L₀ A : ℝ} {N : ℕ}
    (hR : 0 < R) (hη : 0 < η) (hc0 : 0 < c) (hlogc : 2 * R ≤ Real.log c) (hK : 0 < K)
    (hCR : 0 < CR) (hC : 0 < C) (hbb1 : 1 ≤ routeKRVMBase)
    (hL₀a : 8 * R ≤ L₀) (hL₀b : 16 * R * (Real.log 2 + Real.log routeKRVMBase) / η ≤ L₀)
    (hA : A = 12 * Real.pi * R * CR + 2 * C + 6 * K * Real.log 2)
    (hT0 : 0 < T) (hlogTL : L₀ ≤ Real.log T)
    (hratio : 8 * T ^ (-((1 : ℝ) / 100)) ≤ η / 8)
    (hA' : A ≤ η / 32 * T ^ ((24 : ℝ) / 25))
    (hK' : 4 * K * Real.log T ≤ η / 32 * T ^ ((24 : ℝ) / 25))
    (hT2425 : (4 : ℝ) ≤ T ^ ((24 : ℝ) / 25))
    (hH1 : T ^ ((24 : ℝ) / 25) ≤ H) (hH2 : H ≤ T)
    (hT₁lo : T < T₁) (hT₁hi : T₁ < T + 1) (hT₂lo : T + H - 1 < T₂) (hT₂hi : T₂ < T + H)
    (hN1 : 1 ≤ N) (hNle : (N : ℝ) ≤ (T + H) ^ ((1 : ℝ) / 9))
    (hlit₀ : 2 * Real.pi * (R / Real.log T₂ * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)
          + windowTail (R / Real.log T₂) T₁ T₂)
        ≤ (T₂ - T₁) / 2 * Real.log ((c + c * (η / 8))
            * (T₂ - T₁ + 2 * T₁ ^ ((19 : ℝ) / 20)) / (T₂ - T₁))
          + C + K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ))))
    (hNlo : (T₂ - T₁) * (Real.log (T₁ / routeKRVMBase) + 1) / (2 * Real.pi)
          - CR * (Real.log T₁ + Real.log T₂)
        ≤ (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) :
    4 * Real.pi * windowTail (R / Real.log (T + H - 1)) (T + 1) (T + H - 1)
        ≤ (Real.log c - 2 * R + η) * H ∧
      4 * Real.pi * windowTail 0 (T + 1) (T + H - 1) ≤ (Real.log c - R + η) * H := by
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
  have hlogN : Real.log ((N : ℝ) ^ (5 : ℕ)) ≤ Real.log 2 + Real.log T₂ := by
    rw [Real.log_pow]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hTH0 : 0 < T + H := by linarith only [hT0, hH4]
    have h1 : Real.log (N : ℝ) ≤ Real.log ((T + H) ^ ((1 : ℝ) / 9)) := Real.log_le_log hN0 hNle
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
      + 3 * (4 * Real.pi * CR * R) ≤ η / 8 * Δ := by
    have h3 : K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)))
        ≤ 3 * K * Real.log 2 + 2 * K * Real.log T := by
      have : Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)) ≤ 3 * Real.log 2 + 2 * Real.log T := by
        linarith only [hlogN, hlogT₂T]
      have := mul_le_mul_of_nonneg_left this hK.le
      linarith only [this]
    have h4 := mul_le_mul_of_nonneg_left hΔlow (show (0 : ℝ) ≤ η / 8 by positivity)
    linarith only [h3, h4, hA, hA', hK']
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
      + 2 * Real.pi * d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) / (4 * Real.pi) := by
    have h := windowTail_zero_le hd0.le hT12.le
    rw [show 2 * Real.pi * d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) / (4 * Real.pi)
        = d / 2 * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) by field_simp; ring]
    exact h
  have hlit' : 2 * Real.pi * (d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)
      + windowTail d T₁ T₂)
      ≤ Δ / 2 * (Real.log c + η / 4) + (C + K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)))) :=
    hlit
  obtain ⟨htail, hmom⟩ := window_tail_moment_combine hΔ0.le hΔH hlogc hR.le hη hlit' hbridge'
    hlow hW0 hadd hL0 hE0
  -- monotonicity to the stated window
  have hlogU1pos : 0 < Real.log (T + H - 1) := Real.log_pos (by linarith only [hT0, hH4, hH2])
  have hdd : d ≤ R / Real.log (T + H - 1) := by
    rw [hdR]
    exact div_le_div_of_nonneg_left hR.le hlogU1pos
      (Real.log_le_log (by linarith only [hT0, hH4]) hT₂lo.le)
  have hwin : T + 1 ≤ T + H - 1 := by linarith only [hH4]
  have hmono1 : windowTail (R / Real.log (T + H - 1)) (T + 1) (T + H - 1) ≤ windowTail d T₁ T₂ :=
    (windowTail_anti hdd hwin).trans (windowTail_mono hT₁hi.le hT₂lo.le)
  have hmono0 : windowTail 0 (T + 1) (T + H - 1) ≤ windowTail 0 T₁ T₂ :=
    windowTail_mono hT₁hi.le hT₂lo.le
  constructor
  · have := mul_le_mul_of_nonneg_left hmono1 (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    linarith only [this, htail]
  · have := mul_le_mul_of_nonneg_left hmono0 (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    linarith only [this, hmom]

/-- **The off-line tail law in every window `[T, T + H]`, `T^{24/25} ≤ H ≤ T`.**  With
`c_R = e^{2R}/(1 − e^{−2R/9})`, for every `η > 0` and all large `T`,
`4π Σ_{T+1 < Im ρ ≤ T+H−1} m_ρ (Re ρ − ½ − R/log(T+H−1))⁺ ≤ (log c_R − 2R + η) H` and
`4π Σ_{T+1 < Im ρ ≤ T+H−1} m_ρ (Re ρ − ½)⁺ ≤ (log c_R − R + η) H`. -/
theorem eventually_windowTail_le_selberg_ninth {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      4 * Real.pi * windowTail (R / Real.log (T + H - 1)) (T + 1) (T + H - 1)
          ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstNinth R) - 2 * R + η) * H ∧
      4 * Real.pi * windowTail 0 (T + 1) (T + H - 1)
          ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstNinth R) - R + η) * H := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ZetaGateProductAFE.selbergBlockConstNinth R := ⟨_, rfl⟩
  rw [← hcdef]
  have hc1 : 1 ≤ c := hcdef ▸ one_le_selbergBlockConstNinth hR
  have hc0 : 0 < c := by linarith
  have hlogc : 2 * R ≤ Real.log c := hcdef ▸ two_mul_le_log_selbergBlockConstNinth hR
  obtain ⟨C, K, hC, hK, hwide⟩ := exists_zetaWideMoment_le_of_mollified_meanSquare
  obtain ⟨CR, hCR, TR, hTR, hrvm⟩ := exists_xiPosZeroCount_window_bounds
  have hε : 0 < c * (η / 8) := by positivity
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.mp
    (ZetaGateProductAFE.eventually_window_meanSquare_selberg_ninth hR hε)
  rw [← hcdef] at hU₀
  have hbb1 : 1 ≤ routeKRVMBase := by
    rw [routeKRVMBase]
    have h1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith
  have hlogbb : 0 ≤ Real.log routeKRVMBase := Real.log_nonneg hbb1
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ,
      L₀ = 8 * R + 16 * R * (Real.log 2 + Real.log routeKRVMBase) / η := ⟨_, rfl⟩
  have hp1 : 0 ≤ 16 * R * (Real.log 2 + Real.log routeKRVMBase) / η := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hL₀a : 8 * R ≤ L₀ := by linarith
  have hL₀b : 16 * R * (Real.log 2 + Real.log routeKRVMBase) / η ≤ L₀ := by linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 12 * Real.pi * R * CR + 2 * C + 6 * K * Real.log 2 := ⟨_, rfl⟩
  have hη32 : 0 < η / 32 := by positivity
  filter_upwards [eventually_ge_atTop (max (max U₀ (TR + 1)) (max ((2 : ℝ) ^ 9) (Real.exp L₀))),
    eventually_const_mul_rpow_neg_le 8 ((1 : ℝ) / 100) (by norm_num) (show 0 < η / 8 by positivity),
    eventually_const_mul_rpow_neg_mul_log_pow_le A ((24 : ℝ) / 25) (by norm_num) 0 hη32,
    eventually_const_mul_rpow_neg_mul_log_pow_le (4 * K) ((24 : ℝ) / 25) (by norm_num) 1 hη32]
    with T hTbig hratio hadd1 hadd2
  intro H hH1 hH2
  have hTU₀ : U₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTbig
  have hTTR : TR + 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTbig
  have hT9 : (2 : ℝ) ^ 9 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTbig
  have hTL : Real.exp L₀ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTbig
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT9
  have hlogTL : L₀ ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos L₀) hTL
    rwa [Real.log_exp] at this
  have hT2425 : (4 : ℝ) ≤ T ^ ((24 : ℝ) / 25) := by
    have h1 : ((2 : ℝ) ^ 9) ^ ((24 : ℝ) / 25) ≤ T ^ ((24 : ℝ) / 25) :=
      Real.rpow_le_rpow (by positivity) hT9 (by norm_num)
    have h2 : (4 : ℝ) ≤ ((2 : ℝ) ^ 9) ^ ((24 : ℝ) / 25) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [this]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    linarith
  have hH4 : 4 ≤ H := le_trans hT2425 hH1
  have hpos2425 : 0 < T ^ ((24 : ℝ) / 25) := Real.rpow_pos_of_pos hT0 _
  have hA' : A ≤ η / 32 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd1
    rw [pow_zero, mul_one, Real.rpow_neg hT0.le, ← div_eq_mul_inv, div_le_iff₀ hpos2425] at h
    exact h
  have hK' : 4 * K * Real.log T ≤ η / 32 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd2
    rw [pow_one, Real.rpow_neg hT0.le, ← mul_assoc, mul_comm (4 * K), mul_assoc,
      ← div_eq_inv_mul, div_le_iff₀ hpos2425] at h
    linarith only [h]
  have hms := hU₀ (T + H) (by linarith)
  obtain ⟨T₁, T₂, hT₁lo, hT₁hi, hT₂lo, hT₂hi, hlit₀⟩ := exists_window_littlewood hR hwide hT9 hH4
    hH2 (le_trans hL₀a hlogTL) hms
  obtain ⟨hNlo, -⟩ := hrvm T₁ T₂ (by linarith) (by linarith)
  have hN2 := ZetaGateProductAFE.two_le_mollNinth (show (2 : ℝ) ^ 9 ≤ T + H by linarith)
  exact window_bounds_of_littlewood hR hη hc0 hlogc hK hCR hC hbb1 hL₀a hL₀b hA hT0
    hlogTL hratio hA' hK' hT2425 hH1 hH2 hT₁lo hT₁hi hT₂lo hT₂hi (by omega)
    (ZetaGateProductAFE.mollNinth_le (by linarith)) hlit₀ hNlo

end

end RHTower
