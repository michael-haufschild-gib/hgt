import GaloisForLFunctions.VerifiedHeightRungs.SeparatedZerosInEveryLongWindow
import GaloisForLFunctions.VerifiedHeightRungs.SpreadNodesControlTheTransform
import GaloisForLFunctions.VerifiedHeightRungs.WindowEntries

/-!
# Window positivity from local sampling

**Theorem** (`re_W_nonneg_of_rhVerifiedThrough_spread`). RH verified through `spreadHeight a` makes the Weil form of `ζ`
nonnegative on every `C²` test supported in `[−a, a]`, `a ≥ 1`.

`WindowEntries` samples `h_f` on `|τ| ≤ T₁ ≈ exp(68e^{a+2})` with one Lagrange polynomial through nodes above the gap
height, so the degree `n`, and the exponent of the constant `48^{2n}`, are of order `T₁`. Here every `τ` is sampled
locally: next to `τ` lies a window of length `L = 10(m + 1)σ ≥ 2e^{2Y}` above the floor `t_*`, whose `4(m + 1)` separated
verified zeros (`exists_spread_zeros_in_window`) lie within `12(m + 1)σ` of `τ`; the modulated Taylor–Lagrange bound
(`norm_sq_paperFT_le_of_spread_nodes`) then gives `|h_f(τ)|² ≤ K Σ_{|γ| ≤ R} |h_f(γ)|² + 2(‖f‖₁ 48^{−2n})²`. The
degree only has to beat `e^{2Y}/σ`, `t_*/σ` and `log T₁`. The rest is the argument of `WindowEntries`.

Sizes: `Y = κ a^{4/3}` pays a `σ/4`-gap (`spreadY_cube`), `t_* = exp(C Y)` pays the tails and the prime variance.
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower Zeta23 GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-! ### The size of the tail term of the gap test -/

/-- The profile `w` of the gap test. -/
def gapProfile (u : ℝ) : ℂ := ((sinhTestWeight 1 u : ℝ) : ℂ)

theorem gapTestC_eq_profile (Y : ℝ) : gapTestC Y = fun u => gapProfile (Y⁻¹ * u) := by
  funext u
  simp only [gapTestC, gapTest, gapProfile, div_eq_inv_mul]

/-- The tail constant `16 (‖w‖₁ + ‖w''‖₁)²`. -/
def spreadTailC : ℝ := 16 * ((∫ u, ‖gapProfile u‖) + ∫ u, ‖deriv (deriv gapProfile) u‖) ^ 2

theorem spreadTailC_nonneg : 0 ≤ spreadTailC := by unfold spreadTailC; positivity

/-- **The tail term grows like `Y²`.** The test of width `Y` has `‖g‖₁ = Y ‖w‖₁` and `‖g''‖₁ = ‖w''‖₁ / Y`. -/
theorem gapTail_le {Y : ℝ} (hY : 1 ≤ Y) : gapTail Y ≤ spreadTailC * Y ^ 2 := by
  have hY0 : 0 < Y := by linarith only [hY]
  have hd1 : deriv (gapTestC Y) = fun u => (Y⁻¹ : ℂ) * deriv gapProfile (Y⁻¹ * u) := by
    rw [gapTestC_eq_profile]
    funext u
    rw [deriv_comp_mul_left, Complex.real_smul]
    push_cast
    ring
  have hd2 : deriv (deriv (gapTestC Y)) =
      fun u => (Y⁻¹ : ℂ) * ((Y⁻¹ : ℂ) * deriv (deriv gapProfile) (Y⁻¹ * u)) := by
    rw [hd1, deriv_const_mul_field']
    funext u
    rw [deriv_comp_mul_left, Complex.real_smul]
    push_cast
    ring
  have hI1 : ∫ u, ‖gapTestC Y u‖ = Y * ∫ u, ‖gapProfile u‖ := by
    rw [gapTestC_eq_profile]
    have h := Measure.integral_comp_mul_left (fun v => ‖gapProfile v‖) Y⁻¹
    simp only at h
    rw [h, inv_inv, abs_of_pos hY0, smul_eq_mul]
  have hI2 : ∫ u, ‖deriv (deriv (gapTestC Y)) u‖ = Y⁻¹ * ∫ u, ‖deriv (deriv gapProfile) u‖ := by
    rw [hd2]
    have hn : ∀ u, ‖(Y⁻¹ : ℂ) * ((Y⁻¹ : ℂ) * deriv (deriv gapProfile) (Y⁻¹ * u))‖ =
        Y⁻¹ ^ 2 * ‖deriv (deriv gapProfile) (Y⁻¹ * u)‖ := fun u => by
      rw [norm_mul, norm_mul, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hY0)]
      ring
    simp only [hn]
    rw [integral_const_mul]
    have h := Measure.integral_comp_mul_left (fun v => ‖deriv (deriv gapProfile) v‖) Y⁻¹
    simp only at h
    rw [h, inv_inv, abs_of_pos hY0, smul_eq_mul]
    field_simp
  have hw1 : 0 ≤ ∫ u, ‖gapProfile u‖ := integral_nonneg fun _ => norm_nonneg _
  have hw2 : 0 ≤ ∫ u, ‖deriv (deriv gapProfile) u‖ := integral_nonneg fun _ => norm_nonneg _
  have hYi : Y⁻¹ ≤ Y := (inv_le_one_of_one_le₀ hY).trans hY
  have hle : (∫ u, ‖gapTestC Y u‖) + ∫ u, ‖deriv (deriv (gapTestC Y)) u‖ ≤
      Y * ((∫ u, ‖gapProfile u‖) + ∫ u, ‖deriv (deriv gapProfile) u‖) := by
    rw [hI1, hI2]
    nlinarith only [mul_le_mul_of_nonneg_right hYi hw2]
  have h0 : 0 ≤ (∫ u, ‖gapTestC Y u‖) + ∫ u, ‖deriv (deriv (gapTestC Y)) u‖ :=
    add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  unfold gapTail spreadTailC
  have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 * ((∫ u, ‖gapTestC Y u‖) +
    ∫ u, ‖deriv (deriv (gapTestC Y)) u‖)) (mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 4)) 2
  calc _ ≤ (4 * (Y * ((∫ u, ‖gapProfile u‖) + ∫ u, ‖deriv (deriv gapProfile) u‖))) ^ 2 := this
    _ = _ := by ring

/-! ### The width and the floor -/

/-- `κ³` pays a gap of `nodeStep a / 4` at the width `κ a^{4/3}`. -/
def spreadKappa : ℝ :=
  (32 * (400 * gapMass) ^ 2 * 5760 * (36 * 48 ^ 4) ^ 4 / gapEnergy) ^ ((1 : ℝ) / 3) + 1

/-- The width of the gap test, `Y = κ a^{4/3}`. -/
def spreadY (a : ℝ) : ℝ := spreadKappa * a ^ ((4 : ℝ) / 3)

theorem one_le_spreadKappa : 1 ≤ spreadKappa := by
  unfold spreadKappa
  have := Real.rpow_nonneg (by have := gapMass_pos; have := gapEnergy_pos; positivity :
    (0 : ℝ) ≤ 32 * (400 * gapMass) ^ 2 * 5760 * (36 * 48 ^ 4) ^ 4 / gapEnergy) ((1 : ℝ) / 3)
  linarith only [this]

theorem one_le_spreadY {a : ℝ} (ha : 1 ≤ a) : 1 ≤ spreadY a := by
  unfold spreadY
  have h1 : 1 ≤ a ^ ((4 : ℝ) / 3) := Real.one_le_rpow ha (by norm_num)
  nlinarith only [h1, one_le_spreadKappa]

theorem spreadY_cube {a : ℝ} (ha : 0 < a) :
    32 * (400 * gapMass) ^ 2 * 5760 / ((nodeStep a / 4) ^ 4 * gapEnergy) ≤ spreadY a ^ 3 := by
  have hm := gapMass_pos
  have hE := gapEnergy_pos
  obtain ⟨B, hB⟩ : ∃ B, B = 32 * (400 * gapMass) ^ 2 * 5760 * (36 * 48 ^ 4) ^ 4 / gapEnergy := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hκ : B ≤ spreadKappa ^ 3 := by
    have h1 : B ^ ((1 : ℝ) / 3) ≤ spreadKappa := by
      unfold spreadKappa
      rw [← hB]
      linarith only
    have h2 := pow_le_pow_left₀ (Real.rpow_nonneg hB0 _) h1 3
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hB0, show ((1 : ℝ) / 3 * ((3 : ℕ) : ℝ)) = 1 by norm_num,
      Real.rpow_one] at h2
  have ha4 : (a ^ ((4 : ℝ) / 3)) ^ 3 = a ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le, show ((4 : ℝ) / 3 * ((3 : ℕ) : ℝ)) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hlhs : 32 * (400 * gapMass) ^ 2 * 5760 / ((nodeStep a / 4) ^ 4 * gapEnergy) = B * a ^ 4 := by
    rw [hB, nodeStep]
    field_simp
    ring
  rw [hlhs, spreadY, mul_pow, ha4]
  exact mul_le_mul_of_nonneg_right hκ (by positivity)

/-- The constant of the variance law of the prime polynomial. -/
def spreadVarC : ℝ := Classical.choose exists_primeVariance_le

theorem spreadVarC_nonneg : 0 ≤ spreadVarC := (Classical.choose_spec exists_primeVariance_le).1

/-- The exponent of the floor. -/
def spreadFloorC : ℝ :=
  32 + 4 * spreadTailC / gapEnergy + Real.sqrt (20480 * π * gapEnergy * (2 + spreadVarC) / (3 * gapMass ^ 2))

/-- **The floor** `t_* = exp(C Y)`. -/
def spreadFloor (a : ℝ) : ℝ := Real.exp (spreadFloorC * spreadY a)

theorem exp_thirty_le_spreadFloor {a : ℝ} (ha : 1 ≤ a) : Real.exp 30 ≤ spreadFloor a := by
  unfold spreadFloor
  have hY := one_le_spreadY ha
  have h1 : 0 ≤ 4 * spreadTailC / gapEnergy := by have := gapEnergy_pos; have := spreadTailC_nonneg; positivity
  have h2 := Real.sqrt_nonneg (20480 * π * gapEnergy * (2 + spreadVarC) / (3 * gapMass ^ 2))
  refine Real.exp_le_exp.2 ?_
  unfold spreadFloorC
  nlinarith only [h1, h2, hY]

theorem tail_le_spreadFloor {a : ℝ} (ha : 1 ≤ a) :
    4 * Real.exp (spreadY a) * gapTail (spreadY a) / (spreadY a * gapEnergy) ≤ spreadFloor a := by
  have hE := gapEnergy_pos
  have hY := one_le_spreadY ha
  have hY0 : 0 < spreadY a := by linarith only [hY]
  set Y := spreadY a with hYdef
  obtain ⟨x, hx⟩ : ∃ x, x = 4 * spreadTailC / gapEnergy := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; have := spreadTailC_nonneg; positivity
  have h1 : 4 * Real.exp Y * gapTail Y / (Y * gapEnergy) ≤ Real.exp Y * (x * Y) := by
    rw [div_le_iff₀ (by positivity), hx]
    have := gapTail_le hY
    have e : Real.exp Y * (4 * spreadTailC / gapEnergy * Y) * (Y * gapEnergy) =
        4 * Real.exp Y * (spreadTailC * Y ^ 2) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h2 : x * Y ≤ Real.exp (x * Y) := by
    have := Real.add_one_le_exp (x * Y)
    linarith only [this]
  have h3 : Real.exp Y * Real.exp (x * Y) ≤ spreadFloor a := by
    rw [← Real.exp_add, spreadFloor, ← hYdef]
    refine Real.exp_le_exp.2 ?_
    have h4 := Real.sqrt_nonneg (20480 * π * gapEnergy * (2 + spreadVarC) / (3 * gapMass ^ 2))
    unfold spreadFloorC
    rw [← hx]
    nlinarith only [h4, hY, hx0]
  calc _ ≤ Real.exp Y * (x * Y) := h1
    _ ≤ Real.exp Y * Real.exp (x * Y) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ ≤ _ := h3

theorem var_le_spreadFloor {a : ℝ} (ha : 1 ≤ a) :
    320 * π * gapEnergy * primeVariance (gapTestC (spreadY a)) ⌊Real.exp (2 * spreadY a)⌋₊ ≤
      3 * gapMass ^ 2 * (spreadY a * gapEnergy * Real.log (spreadFloor a + 3) / 4) ^ 2 := by
  have hπ := Real.pi_pos
  have hm := gapMass_pos
  have hE := gapEnergy_pos
  have hY := one_le_spreadY ha
  have hY0 : 0 < spreadY a := by linarith only [hY]
  set Y := spreadY a with hYdef
  have hC0 := spreadVarC_nonneg
  have hV := (Classical.choose_spec exists_primeVariance_le).2 Y hY0.le (gapTestC Y)
    (gapTestC_contDiff Y).continuous (hasCompactSupport_of_tsupport_subset_Icc (tsupport_gapTestC hY0))
  rw [integral_gapTestC_sq hY0] at hV
  change _ ≤ 2 * (Y * gapEnergy) ^ 2 * (2 * Y * (2 * Y + spreadVarC)) at hV
  -- `log(t_* + 3) ≥ s Y`, `s² = 20480 π m₂ (2 + C₀)/(3 m₁²)`.
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (20480 * π * gapEnergy * (2 + spreadVarC) / (3 * gapMass ^ 2)) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 20480 * π * gapEnergy * (2 + spreadVarC) / (3 * gapMass ^ 2) := by
    rw [hs, Real.sq_sqrt (by positivity)]
  have hlog : s * Y ≤ Real.log (spreadFloor a + 3) := by
    have h1 : Real.log (spreadFloor a) ≤ Real.log (spreadFloor a + 3) :=
      Real.log_le_log (Real.exp_pos _) (by linarith only)
    rw [spreadFloor, Real.log_exp] at h1
    refine le_trans ?_ h1
    unfold spreadFloorC
    rw [← hYdef, ← hs]
    have : 0 ≤ 4 * spreadTailC / gapEnergy := by have := spreadTailC_nonneg; positivity
    nlinarith only [this, hY0]
  have hlog2 : s ^ 2 * Y ^ 2 ≤ Real.log (spreadFloor a + 3) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlog 2
  -- `2Y + C₀ ≤ (2 + C₀) Y`.
  have hlin : 2 * Y + spreadVarC ≤ (2 + spreadVarC) * Y := by nlinarith only [hY, hC0]
  have hVle : primeVariance (gapTestC Y) ⌊Real.exp (2 * Y)⌋₊ ≤ 4 * gapEnergy ^ 2 * (2 + spreadVarC) * Y ^ 4 := by
    refine hV.trans ?_
    have : 0 ≤ 2 * (Y * gapEnergy) ^ 2 * (2 * Y) := by positivity
    calc 2 * (Y * gapEnergy) ^ 2 * (2 * Y * (2 * Y + spreadVarC))
        = 2 * (Y * gapEnergy) ^ 2 * (2 * Y) * (2 * Y + spreadVarC) := by ring
      _ ≤ 2 * (Y * gapEnergy) ^ 2 * (2 * Y) * ((2 + spreadVarC) * Y) := mul_le_mul_of_nonneg_left hlin this
      _ = _ := by ring
  have hR : 3 * gapMass ^ 2 * (Y * gapEnergy) ^ 2 / 16 * (s ^ 2 * Y ^ 2) ≤
      3 * gapMass ^ 2 * (Y * gapEnergy * Real.log (spreadFloor a + 3) / 4) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ 3 * gapMass ^ 2 * (Y * gapEnergy) ^ 2 / 16)
    refine this.trans (le_of_eq ?_)
    ring
  have hL : 320 * π * gapEnergy * (4 * gapEnergy ^ 2 * (2 + spreadVarC) * Y ^ 4) =
      3 * gapMass ^ 2 * (Y * gapEnergy) ^ 2 / 16 * (s ^ 2 * Y ^ 2) := by
    rw [hs2]
    field_simp
    ring
  calc 320 * π * gapEnergy * primeVariance (gapTestC Y) ⌊Real.exp (2 * Y)⌋₊
      ≤ 320 * π * gapEnergy * (4 * gapEnergy ^ 2 * (2 + spreadVarC) * Y ^ 4) :=
        mul_le_mul_of_nonneg_left hVle (by positivity)
    _ = _ := hL
    _ ≤ _ := hR

/-! ### The number of nodes and the height -/

/-- `m`: the windows have `4(m + 1)` nodes, length `10(m + 1)σ`. -/
def spreadM (a : ℝ) : ℕ :=
  ⌈(spreadFloor a + Real.exp (2 * spreadY a)) / nodeStep a + Real.log (8000 * a * winT₁ a * winD₀ a)⌉₊

/-- The degree `n = 4m + 3`. -/
def spreadN (a : ℝ) : ℕ := 4 * spreadM a + 3

/-- The Lagrange constant `2(n + 1) 48^{2n}`. -/
def spreadK (a : ℝ) : ℝ := 2 * ((spreadN a : ℝ) + 1) * ((48 : ℝ) ^ spreadN a) ^ 2

/-- The window length `10(m + 1)σ`. -/
def spreadL (a : ℝ) : ℝ := 10 * ((spreadM a : ℝ) + 1) * nodeStep a

/-- The radius of the sampled zeros. -/
def spreadR (a : ℝ) : ℝ := winT₁ a + spreadFloor a + spreadL a

/-- The smoothing width. -/
def spreadB (a : ℝ) : ℝ := 1 / (8 * winT₁ a * winD₀ a * spreadK a + 2 * spreadR a + 1)

/-- **The verified height of local sampling.** -/
def spreadHeight (a : ℝ) : ℝ := max (spreadR a + Real.exp (spreadY a) + 1) (winC a / spreadB a ^ 8)

theorem one_le_winT₁ (a : ℝ) : 1 ≤ winT₁ a := by
  unfold winT₁
  have h1 : 0 ≤ winE a + 2 * π := by
    have := horizonExponent_pos (Real.exp (2 * (a + 2)))
    unfold winE
    positivity
  have := Real.one_le_exp h1
  linarith only [this]

theorem one_le_winD₀ (a : ℝ) : 1 ≤ winD₀ a := by
  unfold winD₀
  have := horizonExponent_pos (Real.exp (2 * (a + 2)))
  have : 0 ≤ (1 + winT₁ a ^ 2) * (winE a / (2 * π)) := by unfold winE; positivity
  linarith only [this]

theorem spreadM_bounds {a : ℝ} (ha : 1 ≤ a) :
    spreadFloor a + Real.exp (2 * spreadY a) ≤ (spreadM a : ℝ) * nodeStep a ∧
      Real.log (8000 * a * winT₁ a * winD₀ a) ≤ spreadM a := by
  have ha0 : 0 < a := by linarith only [ha]
  have hσ := nodeStep_pos ha0
  have hlog : 0 ≤ Real.log (8000 * a * winT₁ a * winD₀ a) := by
    refine Real.log_nonneg ?_
    have h1 := one_le_winT₁ a
    have h2 := one_le_winD₀ a
    have h3 : 1 ≤ a * winT₁ a := one_le_mul_of_one_le_of_one_le ha h1
    have h4 : 1 ≤ a * winT₁ a * winD₀ a := one_le_mul_of_one_le_of_one_le h3 h2
    nlinarith only [h4]
  have hpos : 0 ≤ (spreadFloor a + Real.exp (2 * spreadY a)) / nodeStep a := by
    have := Real.exp_pos (spreadFloorC * spreadY a)
    unfold spreadFloor
    positivity
  have hM := Nat.le_ceil ((spreadFloor a + Real.exp (2 * spreadY a)) / nodeStep a +
    Real.log (8000 * a * winT₁ a * winD₀ a))
  rw [← spreadM] at hM
  constructor
  · have h := (div_le_iff₀ hσ).1 (show (spreadFloor a + Real.exp (2 * spreadY a)) / nodeStep a ≤ spreadM a by
      linarith only [hM, hlog])
    exact h
  · linarith only [hM, hpos]

/-! ### Local sampling -/

/-- **Local sampling on the low band.** -/
theorem norm_sq_paperFT_le_of_verified_spread {a T : ℝ} (ha : 1 ≤ a)
    (hT : spreadR a + Real.exp (spreadY a) ≤ T) (hRH : RHVerifiedThrough T) {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfs : ∀ u, f u ≠ 0 → |u| ≤ a) (S : Finset zetaZeroConfig.carrier)
    (hS : ∀ ρ : zetaZeroConfig.carrier, |(ρ : ℂ).im| ≤ spreadR a → ρ ∈ S) {τ : ℝ} (hτ : |τ| ≤ winT₁ a) :
    ‖paperFT f τ‖ ^ 2 ≤ spreadK a * ∑ ρ ∈ S, ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 +
      2 * ((∫ u, ‖f u‖) * ((48 : ℝ) ^ (2 * spreadN a))⁻¹) ^ 2 := by
  classical
  have ha0 : 0 < a := by linarith only [ha]
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = nodeStep a := ⟨_, rfl⟩
  have hσ : 0 < σ := by rw [hσdef]; exact nodeStep_pos ha0
  have hσ1 : σ ≤ 1 := by
    rw [hσdef, nodeStep, div_le_one (by positivity)]
    nlinarith only [ha]
  have hY1 := one_le_spreadY ha
  have hY0 : 0 < spreadY a := by linarith only [hY1]
  obtain ⟨hmσ, -⟩ := spreadM_bounds ha
  rw [← hσdef] at hmσ
  set m := spreadM a with hmdef
  set tₛ := spreadFloor a with htₛ
  set L := 10 * ((m : ℝ) + 1) * σ with hL
  have hLdef : spreadL a = L := by rw [spreadL, ← hσdef]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs0 : 0 < tₛ := Real.exp_pos _
  have he2 : 0 < Real.exp (2 * spreadY a) := Real.exp_pos _
  have hsm : tₛ ≤ ((m : ℝ) + 1) * σ := by nlinarith only [hmσ, he2, hσ]
  have hLY : 2 * Real.exp (2 * spreadY a) ≤ L := by rw [hL]; nlinarith only [hmσ, hs0, hσ]
  have hT₁0 : 0 ≤ winT₁ a := (one_le_winT₁ a).trans' zero_le_one
  have hRdef : spreadR a = winT₁ a + tₛ + L := by rw [spreadR, hLdef]
  have hn : (spreadN a : ℝ) + 1 = 4 * ((m : ℝ) + 1) := by rw [spreadN]; push_cast; ring
  -- A window next to `τ`.
  obtain ⟨c, hc1, hc2⟩ : ∃ c, (∀ t ∈ Icc c (c + L), tₛ ≤ |t| ∧ |t| ≤ spreadR a) ∧
      ∀ t ∈ Icc c (c + L), |t - τ| ≤ 3 * ((spreadN a : ℝ) + 1) * σ := by
    have hL0 : 0 ≤ L := by positivity
    obtain ⟨hτ1, hτ2⟩ := abs_le.1 hτ
    rcases le_or_gt tₛ τ with h | h
    · refine ⟨τ, fun t ht => ?_, fun t ht => ?_⟩
      · obtain ⟨h1, h2⟩ := ht
        rw [abs_of_nonneg (by linarith only [h, h1, hs0]), hRdef]
        exact ⟨by linarith only [h, h1], by linarith only [h2, hτ2, hs0]⟩
      · obtain ⟨h1, h2⟩ := ht
        rw [hn, abs_of_nonneg (by linarith only [h1])]
        nlinarith only [h2, hσ, hm0]
    rcases le_or_gt τ (-tₛ) with h' | h'
    · refine ⟨τ - L, fun t ht => ?_, fun t ht => ?_⟩
      · obtain ⟨h1, h2⟩ := ht
        rw [abs_of_neg (by linarith only [h', h2, hs0]), hRdef]
        exact ⟨by linarith only [h', h2], by linarith only [h1, hτ1, hs0]⟩
      · obtain ⟨h1, h2⟩ := ht
        rw [hn, abs_of_nonpos (by linarith only [h2])]
        nlinarith only [h1, hσ, hm0]
    · refine ⟨tₛ, fun t ht => ?_, fun t ht => ?_⟩
      · obtain ⟨h1, h2⟩ := ht
        rw [abs_of_nonneg (by linarith only [h1, hs0]), hRdef]
        exact ⟨h1, by linarith only [h2, hT₁0]⟩
      · obtain ⟨h1, h2⟩ := ht
        rw [hn]
        have : |t - τ| ≤ (tₛ + L) + tₛ := by
          rw [abs_le]
          constructor <;> linarith only [h1, h2, h, h']
        nlinarith only [this, hsm, hσ, hm0]
  -- The zeros of the window.
  have hY3 := spreadY_cube ha0
  rw [← hσdef] at hY3
  obtain ⟨node, hnode, hsep⟩ := exists_spread_zeros_in_window (c := c) (m := m) (T := T) hσ hσ1 hY0 hY3
    (exp_thirty_le_spreadFloor ha) (tail_le_spreadFloor ha) (var_le_spreadFloor ha) hLY
    (fun t ht => (hc1 t ht).1) (fun t ht => by linarith only [(hc1 t ht).2, hT]) hRH
  have hNm : spreadN a = 4 * m + 3 := rfl
  set v : ℕ → ℝ := fun j => ((node j : ℂ)).im with hv
  have hsep' : ∀ i ∈ range (spreadN a + 1), ∀ j ∈ range (spreadN a + 1),
      nodeStep a * |(i : ℝ) - j| ≤ |v i - v j| := by
    rw [hNm, ← hσdef]
    exact hsep
  have hnear : ∀ j ∈ range (spreadN a + 1), |v j - τ| ≤ 3 * ((spreadN a : ℝ) + 1) * nodeStep a := by
    intro j hj
    rw [← hσdef]
    rw [hNm] at hj
    exact hc2 _ (hnode j hj)
  have h := norm_sq_paperFT_le_of_spread_nodes ha0 hf hfc hfs v hsep' hnear
  -- The nodes are distinct zeros of radius at most `R`.
  have hinj : Set.InjOn node (range (spreadN a + 1) : Finset ℕ) := by
    intro i hi j hj hij
    by_contra hne
    have h1 := hsep' i hi j hj
    have hvij : v i = v j := by simp only [hv]; rw [hij]
    rw [hvij, sub_self, abs_zero] at h1
    have h2 : 0 < |(i : ℝ) - j| := abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast hne))
    have := nodeStep_pos ha0
    nlinarith only [h1, h2, this]
  have hsub : (range (spreadN a + 1)).image node ⊆ S := by
    intro ρ hρ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hρ
    refine hS _ ?_
    rw [hNm] at hj
    exact (hc1 _ (hnode j hj)).2
  have hsum : ∑ j ∈ range (spreadN a + 1), ‖paperFT f (v j)‖ ^ 2 ≤
      ∑ ρ ∈ S, ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 := by
    have e : ∑ j ∈ range (spreadN a + 1), ‖paperFT f (v j)‖ ^ 2 =
        ∑ ρ ∈ (range (spreadN a + 1)).image node, ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 := by
      rw [Finset.sum_image hinj]
    rw [e]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  have hK0 : 0 ≤ 2 * ((spreadN a : ℝ) + 1) * ((48 : ℝ) ^ spreadN a) ^ 2 := by positivity
  calc ‖paperFT f τ‖ ^ 2 ≤ 2 * ((spreadN a : ℝ) + 1) * ((48 : ℝ) ^ spreadN a) ^ 2 *
        ∑ j ∈ range (spreadN a + 1), ‖paperFT f (v j)‖ ^ 2 +
        2 * ((∫ u, ‖f u‖) * ((48 : ℝ) ^ (2 * spreadN a))⁻¹) ^ 2 := h
    _ ≤ _ := by
      rw [spreadK]
      exact add_le_add (mul_le_mul_of_nonneg_left hsum hK0) le_rfl

/-! ### Window positivity -/

/-- The verified zeros of height at most `R` form a finite set. -/
theorem finite_carrier_im_le (R : ℝ) :
    {ρ : zetaZeroConfig.carrier | |(ρ : ℂ).im| ≤ R}.Finite := by
  have h := zetaZeroConfig.finite_window (-R - 1) R
  refine (h.preimage Subtype.val_injective.injOn).subset fun ρ hρ => ?_
  simp only [Set.mem_setOf_eq] at hρ
  obtain ⟨h1, h2⟩ := abs_le.1 hρ
  exact ⟨ρ.2, by linarith only [h1], h2⟩

/-- **Window positivity from local sampling, for `a ≥ 1`.** -/
theorem re_W_nonneg_of_rhVerifiedThrough_spread {a T : ℝ} (ha : 1 ≤ a) (hT : spreadHeight a ≤ T)
    (hRH : RHVerifiedThrough T) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Set.Icc (-a) a) :
    0 ≤ (zetaZeroConfig.W f f).re := by
  classical
  have ha0 : 0 < a := by linarith only [ha]
  have hπ := Real.pi_pos
  obtain ⟨n, hndef⟩ : ∃ n, n = spreadN a := ⟨_, rfl⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hE0 : 0 < winE a := horizonExponent_pos _
  have hT₁1 := one_le_winT₁ a
  have hT₁0 : 0 < winT₁ a := by linarith only [hT₁1]
  have hD₀1 := one_le_winD₀ a
  have hD₀0 : 0 < winD₀ a := by linarith only [hD₀1]
  have hR0 : 0 ≤ spreadR a := by
    unfold spreadR spreadL spreadFloor
    have := nodeStep_pos ha0
    positivity
  -- The width.
  obtain ⟨b, hbdef⟩ : ∃ b, b = spreadB a := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = spreadK a := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; unfold spreadK; positivity
  have hdenpos : 0 < 8 * winT₁ a * winD₀ a * K + 2 * spreadR a + 1 := by positivity
  have hbval : b = 1 / (8 * winT₁ a * winD₀ a * K + 2 * spreadR a + 1) := by rw [hbdef, spreadB, ← hKdef]
  have hb : 0 < b := by rw [hbval]; positivity
  have hb1 : b ≤ 1 := by
    rw [hbval, div_le_one hdenpos]
    have : 0 ≤ 8 * winT₁ a * winD₀ a * K + 2 * spreadR a := by positivity
    linarith only [this]
  have hbK : b * (8 * winT₁ a * winD₀ a * K) ≤ 1 := by
    rw [hbval, one_div, inv_mul_le_iff₀ hdenpos]
    linarith only [hR0]
  have hbR : b * (2 * spreadR a) ≤ 1 := by
    rw [hbval, one_div, inv_mul_le_iff₀ hdenpos]
    have : 0 ≤ 8 * winT₁ a * winD₀ a * K := by positivity
    linarith only [this]
  -- The height.
  have hT1 : spreadR a + Real.exp (spreadY a) + 1 ≤ T := (le_max_left _ _).trans hT
  have hT2 : winC a / b ^ 8 ≤ T := by rw [hbdef]; exact (le_max_right _ _).trans hT
  have hT0 : 0 ≤ T := by
    have := Real.exp_pos (spreadY a)
    linarith only [hT1, hR0, this]
  -- The sampled zeros.
  set S : Finset zetaZeroConfig.carrier := (finite_carrier_im_le (spreadR a)).toFinset with hSdef
  have hSmem : ∀ ρ : zetaZeroConfig.carrier, |(ρ : ℂ).im| ≤ spreadR a → ρ ∈ S := fun ρ hρ => by
    rw [hSdef, Set.Finite.mem_toFinset]
    exact hρ
  have hS : ∀ ρ ∈ S, |(ρ : ℂ).im| ≤ T ∧ 2 * (b * (ρ : ℂ).im) ^ 2 ≤ 1 := by
    intro ρ hρ
    rw [hSdef, Set.Finite.mem_toFinset] at hρ
    simp only [Set.mem_setOf_eq] at hρ
    have he := Real.exp_pos (spreadY a)
    refine ⟨by linarith only [hρ, hT1, he], ?_⟩
    have h1 : |b * (ρ : ℂ).im| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hb]
      have := mul_le_mul_of_nonneg_left hρ hb.le
      linarith only [this, hbR]
    have h2 : (b * (ρ : ℂ).im) ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]
      have h0 := abs_nonneg (b * (ρ : ℂ).im)
      nlinarith only [h1, h0]
    linarith only [h2]
  -- The pieces.
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hfs' : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => abs_le.mpr (hfs (subset_tsupport f hu))
  obtain ⟨Sn, hSn⟩ : ∃ Sn, Sn = ∑ ρ ∈ S, ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 := ⟨_, rfl⟩
  have hSn0 : 0 ≤ Sn := by
    rw [hSn]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨F, hF⟩ : ∃ F, F = ∫ u, ‖f u‖ ^ 2 := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by
    rw [hF]
    exact integral_nonneg fun _ => sq_nonneg _
  have hN : (∫ u, ‖f u‖) ^ 2 ≤ 2 * a * F := by
    rw [hF]
    exact sq_integral_norm_le_of_abs_support hf.continuous ha0 fun x hx => by
      by_contra h
      exact absurd (hfs' x h) (not_le.mpr hx)
  obtain ⟨r₀, hr1, hr2, hrlow, hrup⟩ := kernelQ_half hb hb1
  have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
  have hb2' : 0 < b ^ 2 := by positivity
  have hr01 : 1 ≤ r₀ := by linarith only [hrlow, hb2']
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = r₀ ^ 2 := ⟨_, rfl⟩
  have hκ1 : 1 + b ^ 2 / 1280 ≤ κ := by rw [hκ]; nlinarith only [hrlow, hb2']
  have hκ2 : κ ≤ 1 + b ^ 2 := by
    rw [hκ]
    nlinarith only [hrup, hb2, hb2', hr01]
  have hκ0 : 0 < κ := by linarith only [hκ1, hb2']
  have hκle2 : κ ≤ 2 := by linarith only [hκ2, hb2]
  have hκi1 : 1 / 2 ≤ κ⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hκ0 hκle2
  have hκi2 : κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith only [hκ1, hb2'])
  obtain ⟨ϖ, hϖdef⟩ : ∃ ϖ, ϖ = 1 - κ⁻¹ := ⟨_, rfl⟩
  have hϖeq : ϖ = (κ - 1) * κ⁻¹ := by
    rw [hϖdef]
    field_simp
  have hϖlow : b ^ 2 / 2560 ≤ ϖ := by
    rw [hϖeq]
    have h1 : b ^ 2 / 1280 ≤ κ - 1 := by linarith only [hκ1]
    have := mul_le_mul h1 hκi1 (by norm_num) (by linarith only [h1, hb2'])
    refine le_trans (le_of_eq ?_) this
    ring
  have hϖup : ϖ ≤ b ^ 2 := by
    rw [hϖeq]
    have h1 : κ - 1 ≤ b ^ 2 := by linarith only [hκ2]
    have h0 : 0 ≤ κ - 1 := by linarith only [hκ1, hb2']
    calc
      (κ - 1) * κ⁻¹ ≤ (κ - 1) * 1 := mul_le_mul_of_nonneg_left hκi2 h0
      _ ≤ _ := by linarith only [h1]
  -- The low band, sampled locally.
  obtain ⟨R, hRdef⟩ : ∃ R, R = 2 * ((∫ u, ‖f u‖) * ((48 : ℝ) ^ (2 * n))⁻¹) ^ 2 := ⟨_, rfl⟩
  have hMb : ∀ τ : ℝ, |τ| ≤ winT₁ a → ‖paperFT f τ‖ ^ 2 ≤ K * Sn + R := by
    intro τ hτ
    have h := norm_sq_paperFT_le_of_verified_spread ha (by linarith only [hT1]) hRH hf.continuous hfc hfs' S
      hSmem hτ
    rw [hKdef, hSn, hRdef, hndef]
    exact h
  have hself := re_W_self_ge ha0.le hb hb1 hf hfs hr1 hr2 hr01 (T₁ := winT₁ a) (M := K * Sn + R) le_rfl hMb
  rw [← hκ, ← hϖdef, ← hF] at hself
  have hzero := re_W_smoothed_ge_of_verified ha0.le hb hb1 hf hfs hT0 hRH S hS
  rw [← hSn] at hzero
  -- The bounds of `window_numeric`.
  have hEdef : horizonExponent (Real.exp (2 * (a + 2))) = winE a := rfl
  rw [hEdef] at hself
  obtain ⟨E', hE'⟩ : ∃ E', E' = winE a / (2 * π) := ⟨_, rfl⟩
  have hE'0 : 0 ≤ E' := by rw [hE']; positivity
  rw [← hE'] at hself
  have hD₀eq : winD₀ a = 1 + (1 + winT₁ a ^ 2) * E' := by rw [winD₀, hE']
  have hDle : ϖ + (ϖ + (b * winT₁ a) ^ 2) * E' ≤ b ^ 2 * winD₀ a := by
    rw [hD₀eq]
    have h1 : (ϖ + (b * winT₁ a) ^ 2) * E' ≤ (b ^ 2 + b ^ 2 * winT₁ a ^ 2) * E' :=
      mul_le_mul_of_nonneg_right (by rw [mul_pow]; linarith only [hϖup]) hE'0
    nlinarith only [h1, hϖup]
  have hR0' : 0 ≤ R := by rw [hRdef]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = (((48 : ℝ) ^ (2 * n))⁻¹) ^ 2 := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hRle : R ≤ 4 * a * F * q := by
    rw [hRdef, mul_pow, ← hq]
    have := mul_le_mul_of_nonneg_right hN hq0
    nlinarith only [this]
  have h1 : 8 * winT₁ a * winD₀ a * K * b ^ 2 ≤ 1 := by
    have h0 : 0 ≤ 8 * winT₁ a * winD₀ a * K := by positivity
    have : b ^ 2 ≤ b := by nlinarith only [hb, hb1]
    calc
      8 * winT₁ a * winD₀ a * K * b ^ 2 ≤ 8 * winT₁ a * winD₀ a * K * b := mul_le_mul_of_nonneg_left this h0
      _ = b * (8 * winT₁ a * winD₀ a * K) := by ring
      _ ≤ 1 := hbK
  have h2 : 8 * a * winT₁ a * winD₀ a * q ≤ π / 2560 := by
    -- `48^{2n} ≥ e^n ≥ 8000 a T₁ D₀`.
    obtain ⟨-, hlog⟩ := spreadM_bounds ha
    have hpos : 0 < 8000 * a * winT₁ a * winD₀ a := by positivity
    have hnm : (spreadM a : ℝ) ≤ n := by
      rw [hndef, spreadN]
      push_cast
      linarith only [Nat.cast_nonneg (α := ℝ) (spreadM a)]
    have hexp : 8000 * a * winT₁ a * winD₀ a ≤ Real.exp n := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.2 (hlog.trans hnm)
    have hpow : Real.exp n ≤ (48 : ℝ) ^ (2 * n) := by
      rw [← Real.exp_one_pow, pow_mul]
      refine pow_le_pow_left₀ (Real.exp_pos 1).le ?_ n
      have := Real.exp_one_lt_d9
      norm_num
      linarith only [this]
    have hge1 : (1 : ℝ) ≤ 48 ^ (2 * n) := one_le_pow₀ (by norm_num)
    have hq1 : q ≤ ((48 : ℝ) ^ (2 * n))⁻¹ := by
      rw [hq, sq]
      have h0 : 0 ≤ ((48 : ℝ) ^ (2 * n))⁻¹ := by positivity
      have h3 : ((48 : ℝ) ^ (2 * n))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hge1
      nlinarith only [h0, h3]
    have hval : 8 * a * winT₁ a * winD₀ a * q ≤ 1 / 1000 := by
      have h3 : 8000 * a * winT₁ a * winD₀ a * q ≤ 1 := by
        calc 8000 * a * winT₁ a * winD₀ a * q ≤ 8000 * a * winT₁ a * winD₀ a * ((48 : ℝ) ^ (2 * n))⁻¹ :=
              mul_le_mul_of_nonneg_left hq1 hpos.le
          _ ≤ (48 : ℝ) ^ (2 * n) * ((48 : ℝ) ^ (2 * n))⁻¹ :=
              mul_le_mul_of_nonneg_right (hexp.trans hpow) (by positivity)
          _ = 1 := mul_inv_cancel₀ (by positivity)
      linarith only [h3]
    have := Real.pi_gt_three
    linarith only [hval, this]
  -- The tail.
  obtain ⟨Tail, hTaildef⟩ : ∃ Tail, Tail = Real.exp a * (∫ u, ‖f u‖) ^ 2 * (Real.exp 1 * 400 ^ 2 / b ^ 6) *
      (24 * 240 * Real.log 3 / (1 + T)) := ⟨_, rfl⟩
  rw [← hTaildef] at hzero
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hTail0 : 0 ≤ Tail := by
    rw [hTaildef]
    positivity
  have hTail : Tail ≤ π * b ^ 2 / 2560 * F := by
    have hT3 : winC a / b ^ 8 ≤ 1 + T := by linarith only [hT2]
    have hb8 : 0 < b ^ 8 := by positivity
    have hC0 : 0 ≤ winC a := by unfold winC; positivity
    rw [div_le_iff₀ hb8] at hT3
    have hTp : 0 < 1 + T := by linarith only [hT0]
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = Real.exp a * (Real.exp 1 * 400 ^ 2) * (24 * 240 * Real.log 3) := ⟨_, rfl⟩
    have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
    have hC : winC a = 2 * a * Z * 1000 := by rw [winC, hZ]; ring
    have e : Tail = (∫ u, ‖f u‖) ^ 2 * Z / (b ^ 6 * (1 + T)) := by
      rw [hTaildef, hZ]
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h3 : (∫ u, ‖f u‖) ^ 2 * Z ≤ 2 * a * F * Z := mul_le_mul_of_nonneg_right hN hZ0
    have h4 : π / 2560 ≥ 1 / 1000 := by
      have := Real.pi_gt_three
      linarith only [this]
    have h5 : 2 * a * Z * 1000 * F ≤ (1 + T) * b ^ 8 * F := by
      rw [hC] at hT3
      exact mul_le_mul_of_nonneg_right hT3 hF0
    have h6 : 0 ≤ (1 + T) * b ^ 8 * F := by positivity
    have e2 : π * b ^ 2 / 2560 * F * (b ^ 6 * (1 + T)) = π / 2560 * ((1 + T) * b ^ 8 * F) := by ring
    rw [e2]
    have h7 : 1 / 1000 * ((1 + T) * b ^ 8 * F) ≤ π / 2560 * ((1 + T) * b ^ 8 * F) :=
      mul_le_mul_of_nonneg_right h4 h6
    nlinarith only [h3, h5, h7]
  exact window_numeric (κi := κ⁻¹) (ϖ := ϖ) (b := b) (D₀ := winD₀ a) (T₁ := winT₁ a) (K := K) (Sn := Sn) (F := F)
    (Tail := Tail) (Wg := (zetaZeroConfig.W f (smoothedTest b f)).re) (Wf := (zetaZeroConfig.W f f).re)
    (M := K * Sn + R) (R := R) (D := ϖ + (ϖ + (b * winT₁ a) ^ 2) * E') (a := a) (q := q)
    hκi1 hκi2 hϖlow hzero hself hDle hD₀0.le rfl hR0' hRle h1 h2 hTail0 hTail hSn0 hF0 hT₁0.le hK0

end

end GaloisForLFunctions.VerifiedHeightRungs
