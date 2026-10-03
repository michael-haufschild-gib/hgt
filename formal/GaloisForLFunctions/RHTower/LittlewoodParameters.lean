import GaloisForLFunctions.RHTower.LittlewoodZeroSide
import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder
import GaloisForLFunctions.HTGeometry.DirichletSimultaneousApproximation

/-!
# The parameters of Littlewood's argument

With `y → ∞`, `h = 1/y`, `T = y²`, `Q = ⌈y²⌉`:

* `N(y) ≥ (y/4π) log y` (Riemann–von Mangoldt), so at least that many copies have `|γ| ≤ y`;
* the copies with `|γ| ≤ T` number at most `8(1 + T²)(C₀ + log 4)`;
* Dirichlet's theorem puts some `u = kU`, `1 ≤ k ≤ Q^{N_T}`, in phase with all of them, with
  `ε₁ = 2π²/Q²`, `ε₂ = 2π/Q`;
* at such `u`, the aligned lag differences are at least `(1/(5π³)) h log y` in size, with
  opposite signs on the two windows (`eventually_littlewood_zero_side`).
-/

open Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **Riemann–von Mangoldt from below.** -/
theorem eventually_xiZeroCount_ge :
    ∀ᶠ Y : ℝ in atTop, Y * Real.log Y / (4 * Real.pi) ≤ (xiZeroCount Y : ℝ) := by
  obtain ⟨C, hC, T₀, hT₀, hrvm⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  have hb := one_lt_routeKRVMBase
  have hlb : 0 < Real.log routeKRVMBase := Real.log_pos hb
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log routeKRVMBase + 4 * Real.pi * C + 1)]
    with Y hY hY1 hlog
  have hR := (abs_le.mp (hrvm Y hY)).1
  unfold routeKSmoothRVMCount at hR
  have hY0 : 0 < Y := by linarith
  have hlogdiv : Real.log (Y / routeKRVMBase) = Real.log Y - Real.log routeKRVMBase :=
    Real.log_div hY0.ne' (by linarith)
  rw [hlogdiv] at hR
  have hlogY : Real.log Y ≤ Y := by have := Real.log_le_sub_one_of_pos hY0; linarith
  have hπ := Real.pi_pos
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg hY1
  -- C log Y ≤ C Y / ... : bound `4πC log Y ≤ 4πC·Y`
  have h1 : 4 * Real.pi * C * Real.log Y ≤ 4 * Real.pi * C * Y :=
    mul_le_mul_of_nonneg_left hlogY (by positivity)
  have hkey : Y * Real.log Y / (4 * Real.pi)
      ≤ Y / (2 * Real.pi) * (Real.log Y - Real.log routeKRVMBase) + 7 / 8 - C * Real.log Y := by
    rw [div_le_iff₀ (by positivity)]
    have : Y / (2 * Real.pi) * (Real.log Y - Real.log routeKRVMBase) * (4 * Real.pi)
        = 2 * Y * (Real.log Y - Real.log routeKRVMBase) := by field_simp; ring
    nlinarith
  linarith

/-- The copies with `|γ| ≤ T` number at most `8(1 + T²)(C₀ + log 4)`. -/
theorem card_xiCopiesBelow_le (T : ℝ) :
    ((xiCopiesBelow T).card : ℝ) ≤ 8 * (1 + T ^ 2) * (xiLineTwoLogDerivConstant + Real.log 4) := by
  have h := ncard_xiOrdinateWindow_le_log T 0
  rw [Set.ncard_eq_toFinset_card _ (finite_xiOrdinateWindow T 0)] at h
  simpa [xiCopiesBelow] using h

/-- The positive copies up to `Y` lie among those with `|γ| ≤ T`, `Y ≤ T`. -/
theorem xiZeroCount_le_card_filter {Y T : ℝ} (hY : 0 ≤ Y) (hYT : Y ≤ T) :
    (xiZeroCount Y : ℝ)
      ≤ (((xiCopiesBelow T).filter (fun q => |zeroOrdinate q| ≤ Y)).card : ℝ) := by
  classical
  have hsub : xiCopiesPos Y ⊆ (xiCopiesBelow T).filter (fun q => |zeroOrdinate q| ≤ Y) := by
    intro q hq
    rw [mem_xiCopiesPos] at hq
    rw [Finset.mem_filter, mem_xiCopiesBelow]
    exact ⟨le_trans hq.1 hYT, hq.1⟩
  have hcard := Finset.card_le_card hsub
  have heq := intCast_card_xiCopiesPos hY
  have : ((xiCopiesPos Y).card : ℝ) = (xiZeroCount Y : ℝ) := by exact_mod_cast heq
  rw [← this]
  exact_mod_cast hcard

/-- **Simultaneous alignment of the low zeros.** -/
theorem exists_aligned_multiple (T U : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ Q ^ (xiCopiesBelow T).card ∧ ∀ q ∈ xiCopiesBelow T,
      1 - 2 * Real.pi ^ 2 / (Q : ℝ) ^ 2 ≤ Real.cos (zeroOrdinate q * (k * U))
        ∧ |Real.sin (zeroOrdinate q * (k * U))| ≤ 2 * Real.pi / Q := by
  classical
  obtain ⟨k, hk1, hkQ, hk⟩ := exists_dirichlet_phase
    (fun i : ↥(xiCopiesBelow T) => zeroOrdinate i.1) U Q hQ
  refine ⟨k, hk1, by simpa using hkQ, fun q hq => hk ⟨q, hq⟩⟩


/-- The constant of Littlewood's argument, `1/(5π³)`. -/
def littlewoodConst : ℝ := 1 / (5 * Real.pi ^ 3)

theorem littlewoodConst_pos : 0 < littlewoodConst := by unfold littlewoodConst; positivity

/-- The tail is negligible: `2τ(y²) ≤ 1/y` for large `y`. -/
theorem eventually_two_lagTailBound_le : ∀ᶠ y : ℝ in atTop, 2 * lagTailBound (y ^ 2) ≤ 1 / y := by
  have hC0 := xiLineTwoLogDerivConstant_nonneg
  have hlo := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 640 by norm_num)
  filter_upwards [hlo, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (160 * (xiLineTwoLogDerivConstant + 2) + 1)] with y hlog hy2 hyC
  have hy0 : 0 < y := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hy0] at hlog
  have hlogy : Real.log y ≤ y / 640 := by have := le_abs_self (Real.log y); linarith
  have hlog4 : Real.log (y ^ 2 + 4) ≤ 1 + 2 * Real.log y := by
    have h1 : y ^ 2 + 4 ≤ 2 * y ^ 2 := by nlinarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
    have h3 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    push_cast at h2
    linarith
  unfold lagTailBound
  have hnum : 80 * (xiLineTwoLogDerivConstant + 1 + Real.log (y ^ 2 + 4)) ≤ y := by
    nlinarith
  calc 2 * (40 * (xiLineTwoLogDerivConstant + 1 + Real.log (y ^ 2 + 4)) / y ^ 2)
      = 80 * (xiLineTwoLogDerivConstant + 1 + Real.log (y ^ 2 + 4)) / y ^ 2 := by ring
    _ ≤ y / y ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg y)
    _ = 1 / y := by field_simp

/-- **The aligned lag differences, lower window.**  Under RH, for large `y`, every `u` aligned at
resolution `⌈y²⌉` on the copies with `|γ| ≤ y²` has `Δ_{1/y}(u) ≤ -(1/(5π³)) log y / y`. -/
theorem eventually_littlewood_zero_side_lower (hRH : RiemannHypothesis) :
    ∀ᶠ y : ℝ in atTop, ∀ u : ℝ,
      (∀ q ∈ xiCopiesBelow (y ^ 2),
        1 - 2 * Real.pi ^ 2 / ((⌈y ^ 2⌉₊ : ℕ) : ℝ) ^ 2 ≤ Real.cos (zeroOrdinate q * u)
          ∧ |Real.sin (zeroOrdinate q * u)| ≤ 2 * Real.pi / ((⌈y ^ 2⌉₊ : ℕ) : ℝ)) →
      weilLagFunctionReal (u + 1 / y) * Real.exp (-(1 / y / 2)) - weilLagFunctionReal u
        ≤ -(littlewoodConst * (Real.log y / y)) := by
  have hw := summable_cosWeight hRH
  have hW0 : 0 ≤ ∑' q, cosWeight q := tsum_nonneg (fun q => by unfold cosWeight; positivity)
  set W := ∑' q, cosWeight q with hWdef
  filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_xiZeroCount_ge,
    Real.tendsto_log_atTop.eventually_ge_atTop (10 * Real.pi ^ 3 * (4.5 * W + 1)),
    eventually_two_lagTailBound_le] with y hy4 hN hlog htail u halign
  have hy0 : 0 < y := by linarith
  have hπ := Real.pi_pos
  have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
  set Q : ℕ := ⌈y ^ 2⌉₊ with hQ
  have hQy : y ^ 2 ≤ (Q : ℝ) := Nat.le_ceil _
  have hQ1 : 1 ≤ Q := by
    have : (1 : ℝ) ≤ Q := by nlinarith
    exact_mod_cast this
  have hQpos : (0 : ℝ) < Q := by nlinarith
  set ε₁ := 2 * Real.pi ^ 2 / (Q : ℝ) ^ 2 with hε₁
  set ε₂ := 2 * Real.pi / (Q : ℝ) with hε₂
  have hε₁0 : 0 ≤ ε₁ := by positivity
  have hε₂0 : 0 ≤ ε₂ := by positivity
  have hε₁y : ε₁ ≤ 1 / y := by
    rw [hε₁, div_le_div_iff₀ (by positivity) hy0]
    have h1 : y ^ 4 ≤ (Q : ℝ) ^ 2 := by nlinarith
    have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith
    have hy3 : 64 ≤ y ^ 3 := by nlinarith
    calc 2 * Real.pi ^ 2 * y ≤ 32 * y := by nlinarith
      _ ≤ y ^ 3 * y := by nlinarith
      _ = y ^ 4 := by ring
      _ ≤ 1 * (Q : ℝ) ^ 2 := by linarith
  have hε₂y : ε₂ ≤ 2 / y := by
    rw [hε₂, div_le_div_iff₀ hQpos hy0]
    nlinarith
  have hT : (4 : ℝ) ≤ y ^ 2 := by nlinarith
  have hh : (0 : ℝ) < 1 / y := by positivity
  have hL := lagDifference_le_of_aligned hRH (T := y ^ 2) (h := 1 / y) (u := u) hT hh hε₁0 hε₂0
    halign
  rw [one_div_one_div] at hL
  have hM := xiZeroCount_le_card_filter (T := y ^ 2) hy0.le (by nlinarith)
  set M := (((xiCopiesBelow (y ^ 2)).filter (fun q => |zeroOrdinate q| ≤ y)).card : ℝ) with hMdef
  have hδ : 1 - Real.exp (-(1 / y / 2)) ≤ 1 / (2 * y) := by
    have := Real.add_one_le_exp (-(1 / y / 2))
    have : 1 / y / 2 = 1 / (2 * y) := by ring
    linarith
  have hcoef : (1 - Real.exp (-(1 / y / 2))) + 2 * ε₁ + ε₂ ≤ 4.5 / y := by
    have : 1 / (2 * y) + 2 * (1 / y) + 2 / y = 4.5 / y := by field_simp; norm_num
    linarith
  have herr : ((1 - Real.exp (-(1 / y / 2))) + 2 * ε₁ + ε₂) * W ≤ 4.5 / y * W :=
    mul_le_mul_of_nonneg_right hcoef hW0
  have hmain : 8 / (5 * Real.pi ^ 2) * (1 / y) ^ 2 * (y * Real.log y / (4 * Real.pi))
      = 2 / (5 * Real.pi ^ 3) * (Real.log y / y) := by
    field_simp; ring
  have hmainle : 8 / (5 * Real.pi ^ 2) * (1 / y) ^ 2 * (y * Real.log y / (4 * Real.pi))
      ≤ 8 / (5 * Real.pi ^ 2) * (1 / y) ^ 2 * M :=
    mul_le_mul_of_nonneg_left (le_trans hN hM) (by positivity)
  have hlog' : (4.5 * W + 1) * (1 / y) ≤ 1 / (10 * Real.pi ^ 3) * (Real.log y / y) := by
    have h1 : (4.5 * W + 1) ≤ 1 / (10 * Real.pi ^ 3) * Real.log y := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]; linarith
    calc (4.5 * W + 1) * (1 / y) ≤ 1 / (10 * Real.pi ^ 3) * Real.log y * (1 / y) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 / (10 * Real.pi ^ 3) * (Real.log y / y) := by ring
  have hconst : littlewoodConst
      = 2 / (5 * Real.pi ^ 3) - 1 / (10 * Real.pi ^ 3) - 1 / (10 * Real.pi ^ 3) := by
    unfold littlewoodConst; field_simp; ring
  have hlogy0 : 0 ≤ Real.log y / y := div_nonneg (Real.log_nonneg (by linarith)) hy0.le
  have hextra : 0 ≤ 1 / (10 * Real.pi ^ 3) * (Real.log y / y) := by positivity
  have h45 : 4.5 / y * W + 1 / y = (4.5 * W + 1) * (1 / y) := by ring
  rw [hconst]
  nlinarith [hL, hmainle, hmain, herr, htail, hlog', h45]


/-- The arithmetic of the upper window. -/
theorem littlewood_upper_arith {y W M ε₁ ε₂ e τ Δ : ℝ} (hy4 : 4 ≤ y) (hW0 : 0 ≤ W)
    (hM : y * Real.log y / (4 * Real.pi) ≤ M) (hε₁y : ε₁ ≤ 1 / y) (hε₂y : ε₂ ≤ 2 / y)
    (hδ : 1 - e ≤ 1 / (2 * y)) (htail : 2 * τ ≤ 1 / y)
    (hlog : 10 * Real.pi ^ 3 * (4.5 * W + 1) ≤ Real.log y)
    (hU : (1 - ε₁) * (8 / (5 * Real.pi ^ 2)) * (1 / y) ^ 2 * M - ((1 - e) + ε₂) * W - 2 * τ ≤ Δ) :
    littlewoodConst * (Real.log y / y) ≤ Δ := by
  have hy0 : 0 < y := by linarith
  have hπ := Real.pi_pos
  have hcoef : (1 - e) + ε₂ ≤ 4.5 / y := by
    have : 1 / (2 * y) + 2 / y = 2.5 / y := by field_simp; norm_num
    have h45 : 2.5 / y ≤ 4.5 / y := div_le_div_of_nonneg_right (by norm_num) hy0.le
    linarith
  have herr : ((1 - e) + ε₂) * W ≤ 4.5 / y * W := mul_le_mul_of_nonneg_right hcoef hW0
  have hmain : 8 / (5 * Real.pi ^ 2) * (1 / y) ^ 2 * (y * Real.log y / (4 * Real.pi))
      = 2 / (5 * Real.pi ^ 3) * (Real.log y / y) := by
    field_simp; ring
  have hmainle : 8 / (5 * Real.pi ^ 2) * (1 / y) ^ 2 * (y * Real.log y / (4 * Real.pi))
      ≤ 8 / (5 * Real.pi ^ 2) * (1 / y) ^ 2 * M :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have hy14 : 1 / y ≤ 1 / 4 := by rw [div_le_div_iff₀ hy0 (by norm_num)]; linarith
  have h34 : (3 : ℝ) / 4 ≤ 1 - ε₁ := by linarith
  have hnn : 0 ≤ 8 / (5 * Real.pi ^ 2) * (1 / y) ^ 2 * (y * Real.log y / (4 * Real.pi)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ y by linarith)
    positivity
  have hthree : (3 / 4) * (2 / (5 * Real.pi ^ 3) * (Real.log y / y))
      ≤ (1 - ε₁) * (8 / (5 * Real.pi ^ 2) * (1 / y) ^ 2 * M) := by
    rw [← hmain]
    exact mul_le_mul h34 hmainle hnn (by linarith)
  have hlog' : (4.5 * W + 1) * (1 / y) ≤ 1 / (10 * Real.pi ^ 3) * (Real.log y / y) := by
    have h1 : (4.5 * W + 1) ≤ 1 / (10 * Real.pi ^ 3) * Real.log y := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]; linarith
    calc (4.5 * W + 1) * (1 / y) ≤ 1 / (10 * Real.pi ^ 3) * Real.log y * (1 / y) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 / (10 * Real.pi ^ 3) * (Real.log y / y) := by ring
  have hconst : littlewoodConst
      = (3 / 4) * (2 / (5 * Real.pi ^ 3)) - 1 / (10 * Real.pi ^ 3) := by
    unfold littlewoodConst; field_simp; ring
  have h45 : 4.5 / y * W + 1 / y = (4.5 * W + 1) * (1 / y) := by ring
  have hassoc : (1 - ε₁) * (8 / (5 * Real.pi ^ 2)) * (1 / y) ^ 2 * M
      = (1 - ε₁) * (8 / (5 * Real.pi ^ 2) * (1 / y) ^ 2 * M) := by ring
  rw [hassoc] at hU
  rw [hconst]
  have hfin : (3 / 4) * (2 / (5 * Real.pi ^ 3) * (Real.log y / y))
      - 1 / (10 * Real.pi ^ 3) * (Real.log y / y) ≤ Δ := by linarith
  have hre : (3 / 4 * (2 / (5 * Real.pi ^ 3)) - 1 / (10 * Real.pi ^ 3)) * (Real.log y / y)
      = (3 / 4) * (2 / (5 * Real.pi ^ 3) * (Real.log y / y))
        - 1 / (10 * Real.pi ^ 3) * (Real.log y / y) := by ring
  rw [hre]; exact hfin

/-- **The aligned lag differences, upper window.**  Under RH, for large `y`, every aligned `u` has
`Φ(u)e^{-1/(2y)} - Φ(u - 1/y) ≥ (1/(5π³)) log y / y`. -/
theorem eventually_littlewood_zero_side_upper (hRH : RiemannHypothesis) :
    ∀ᶠ y : ℝ in atTop, ∀ u : ℝ,
      (∀ q ∈ xiCopiesBelow (y ^ 2),
        1 - 2 * Real.pi ^ 2 / ((⌈y ^ 2⌉₊ : ℕ) : ℝ) ^ 2 ≤ Real.cos (zeroOrdinate q * u)
          ∧ |Real.sin (zeroOrdinate q * u)| ≤ 2 * Real.pi / ((⌈y ^ 2⌉₊ : ℕ) : ℝ)) →
      littlewoodConst * (Real.log y / y)
        ≤ weilLagFunctionReal u * Real.exp (-(1 / y / 2)) - weilLagFunctionReal (u - 1 / y) := by
  have hW0 : 0 ≤ ∑' q, cosWeight q := tsum_nonneg (fun q => by unfold cosWeight; positivity)
  filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_xiZeroCount_ge,
    Real.tendsto_log_atTop.eventually_ge_atTop (10 * Real.pi ^ 3 * (4.5 * ∑' q, cosWeight q + 1)),
    eventually_two_lagTailBound_le] with y hy4 hN hlog htail u halign
  have hy0 : 0 < y := by linarith
  have hπ := Real.pi_pos
  have hQy : y ^ 2 ≤ ((⌈y ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hQpos : (0 : ℝ) < ((⌈y ^ 2⌉₊ : ℕ) : ℝ) := by nlinarith
  have hε₁y : 2 * Real.pi ^ 2 / ((⌈y ^ 2⌉₊ : ℕ) : ℝ) ^ 2 ≤ 1 / y := by
    rw [div_le_div_iff₀ (by positivity) hy0]
    have h1 : y ^ 4 ≤ ((⌈y ^ 2⌉₊ : ℕ) : ℝ) ^ 2 := by nlinarith
    have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four]
    have hy3 : 64 ≤ y ^ 3 := by nlinarith
    calc 2 * Real.pi ^ 2 * y ≤ 32 * y := by nlinarith
      _ ≤ y ^ 3 * y := by nlinarith
      _ = y ^ 4 := by ring
      _ ≤ 1 * ((⌈y ^ 2⌉₊ : ℕ) : ℝ) ^ 2 := by linarith
  have hε₂y : 2 * Real.pi / ((⌈y ^ 2⌉₊ : ℕ) : ℝ) ≤ 2 / y := by
    rw [div_le_div_iff₀ hQpos hy0]
    nlinarith [Real.pi_le_four]
  have hy14 : 1 / y ≤ 1 / 4 := by rw [div_le_div_iff₀ hy0 (by norm_num)]; linarith
  have hT : (4 : ℝ) ≤ y ^ 2 := by nlinarith
  have hU := lagDifference_ge_of_aligned hRH (T := y ^ 2) (h := 1 / y) (u := u) hT
    (by positivity) (by linarith) (by positivity) halign
  rw [one_div_one_div] at hU
  have hM := xiZeroCount_le_card_filter (T := y ^ 2) hy0.le (by nlinarith)
  have hδ : 1 - Real.exp (-(1 / y / 2)) ≤ 1 / (2 * y) := by
    have := Real.add_one_le_exp (-(1 / y / 2))
    have : 1 / y / 2 = 1 / (2 * y) := by ring
    linarith
  exact littlewood_upper_arith hy4 hW0 (le_trans hN hM) hε₁y hε₂y hδ htail hlog hU

end

end RHTower
