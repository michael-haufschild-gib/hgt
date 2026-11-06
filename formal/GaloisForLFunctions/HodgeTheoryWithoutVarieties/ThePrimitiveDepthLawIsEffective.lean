import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheDepthLawIsEffective
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSpectralGapOfThePrimeFormIsTwoLogTwo
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTensorizationConstantIsExplicit

/-!
# The primitive depth law with an explicit horizon

For `0 < ε ≤ 1` the horizon `primitiveDepthHorizon ε` is a closed expression:

* `Q = ⌈exp(8 C)⌉ + 2` with `C` the explicit tensorization constant, so rough fibres cost `C / log Q ≤ 1/8`;
* `X = ⌈exp(gapScale ε)⌉ + 2`, the grid where the `Q`-smooth valuation chain has gap `2 log 2 − ε/2`;
* `X (⌈exp(G/m)⌉ + 1)`, where the rough mass `F_Q(N/X) ≥ m log(N/X)` beats the two-scale coefficients.

Above it:

* **Spectral gap** (`mul_harmonicVar_le_poleDefect_of_horizon`): `(2 log 2 − ε) Var ≤ D_N`;
* **Prime form below its pole** (`atomicWeilForm_le_two_log_two_of_horizon`):
  `P_N(x) ≤ (log N − γ − 2 log 2 + ε)|x|²` on pole-orthogonal `x`;
* **Primitive depth law** (`renormalizedPrimeForm_starRestrict_ge_primitive_of_horizon`):
  `R_N ≥ (log d + 2 log 2 − ε)|x|²` on the star of `d` with pole-orthogonal pullback, once
  `⌊N/d⌋ ≥ primitiveDepthHorizon ε`.
-/

noncomputable section

open Finset ArithmeticFunction
open GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

local notation "γ" => Real.eulerMascheroniConstant

/-! ### The deficit of the sharp counterterm -/

/-- The logarithmic horizon of the deficit inequality at precision `ε`. -/
def deficitLogHorizon (ε : ℝ) : ℝ :=
  Real.log ((mertensCutoff ε + 1 : ℕ) : ℝ) + ((mertensCutoff ε + 1 : ℕ) : ℝ) *
    (Real.log ((mertensCutoff ε + 1 : ℕ) : ℝ) + 2) * (4 * (Real.log 4 + 4) + 2) / ε

/-- **The deficit of the prime form is the pole defect, with an explicit horizon.** -/
theorem atomicWeilForm_add_poleDefect_le_of_horizon {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {N : ℕ}
    (hN1 : 1 ≤ N) (hN : deficitLogHorizon ε ≤ Real.log N) (x : ℕ → ℝ) :
    atomicWeilForm N x + (1 - ε) * poleDefect N x ≤
      (Real.log N - γ + ε) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  set B : ℝ := Real.log 4 + 4 with hB
  have hB0 : 0 < B := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  set th : ℝ := ε / (4 * B + 2) with hth
  have hth0 : 0 < th := by positivity
  have hthε : 2 * th ≤ ε := by
    rw [hth, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hthB : 2 * th * B ≤ ε / 2 := by
    rw [hth]; field_simp; nlinarith
  have hγ0 : 0 < γ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant
  obtain ⟨Q₀, hQ₀def⟩ : ∃ Q₀, Q₀ = mertensCutoff ε := ⟨_, rfl⟩
  have hQ₀ : ∀ b : ℕ, Q₀ ≤ b → mertensSum b - Real.log b < -γ + ε / 2 := fun b hb =>
    mertensSum_sub_log_lt hε hε1 (hQ₀def ▸ hb)
  set Q : ℕ := Q₀ + 1 with hQ
  have hQ0 : (0 : ℝ) < Q := by positivity
  set C : ℝ := mertensSum Q + γ with hC
  have hAQ : 0 ≤ mertensSum Q := sum_nonneg fun t _ => div_nonneg vonMangoldt_nonneg (by positivity)
  have hC0 : 0 < C := by linarith
  have hlogN : Real.log Q + Q * C / th ≤ Real.log N := by
    refine le_trans ?_ hN
    have hCle : C ≤ Real.log Q + 2 := by
      have := hQ₀ Q (by omega)
      linarith only [this, hε1]
    have hcoef : Q * C / th = (Q : ℝ) * C * (4 * B + 2) / ε := by
      rw [hth]; field_simp
    have hmono : (Q : ℝ) * C * (4 * B + 2) / ε ≤ (Q : ℝ) * (Real.log Q + 2) * (4 * B + 2) / ε := by
      have h1 := mul_le_mul_of_nonneg_left hCle hQ0.le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) hε.le
    rw [hcoef]
    have hQe : Q = mertensCutoff ε + 1 := by rw [hQ, hQ₀def]
    unfold deficitLogHorizon
    rw [← hQe]
    linarith only [hmono]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  -- every row is at most `log N − γ + ε/2 + th (n/N) log n`
  have hrowbd : ∀ n ∈ Icc 1 N, mertensSum (N / n) + Real.log n ≤
      Real.log N - γ + ε / 2 + th * ((n : ℝ) / N * Real.log n) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlogn : Real.log n ≤ Real.log N :=
      Real.log_le_log hn0 (by exact_mod_cast hnN)
    by_cases hbulk : Q₀ ≤ N / n
    · have hM := hQ₀ (N / n) hbulk
      have hq0 : (0 : ℝ) < ((N / n : ℕ) : ℝ) := by
        exact_mod_cast Nat.div_pos hnN hn1
      have hprod : ((N / n : ℕ) : ℝ) * n ≤ N := by exact_mod_cast Nat.div_mul_le_self N n
      have hlogs : Real.log ((N / n : ℕ) : ℝ) + Real.log n ≤ Real.log N := by
        rw [← Real.log_mul hq0.ne' hn0.ne']
        exact Real.log_le_log (mul_pos hq0 hn0) hprod
      have htop : 0 ≤ th * ((n : ℝ) / N * Real.log n) :=
        mul_nonneg hth0.le (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hn1)))
      linarith
    · have hlt : N / n < Q := by omega
      have hNQ : (N : ℝ) < Q * n := by
        exact_mod_cast (Nat.div_lt_iff_lt_mul hn1).mp hlt
      have hmono : mertensSum (N / n) ≤ mertensSum Q :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hlt.le)
          fun t _ _ => div_nonneg vonMangoldt_nonneg (by positivity)
      have hratio : 1 / (Q : ℝ) ≤ (n : ℝ) / N := by
        rw [div_le_div_iff₀ hQ0 hN0]; linarith
      have hNQ0 : (0 : ℝ) < N / Q := by positivity
      have hlogQ : Real.log (N / Q) ≤ Real.log n := by
        refine Real.log_le_log hNQ0 ?_
        rw [div_le_iff₀ hQ0]; linarith
      have hlogNQ : Q * C / th ≤ Real.log (N / Q) := by
        rw [Real.log_div hN0.ne' hQ0.ne']; linarith
      have hlogNQ0 : 0 ≤ Real.log (N / Q) := le_trans (by positivity) hlogNQ
      have hCle : C ≤ th * ((n : ℝ) / N * Real.log n) := by
        have h1 : C ≤ th * (1 / (Q : ℝ) * Real.log (N / Q)) := by
          have h2 : (Q : ℝ) * C ≤ th * Real.log (N / Q) := by
            have := (div_le_iff₀ hth0).mp hlogNQ; linarith
          rw [show th * (1 / (Q : ℝ) * Real.log (N / Q)) = th * Real.log (N / Q) / Q by
            field_simp, le_div_iff₀ hQ0]
          linarith
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ hth0.le)
        exact mul_le_mul hratio hlogQ hlogNQ0 (by positivity)
      linarith
  have htopsum := sum_top_le_poleDefect N x
  have hD := poleDefect_nonneg N x
  have hid := atomicWeilForm_add_poleDefect N x
  have hrows : ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 ≤
      (Real.log N - γ + ε / 2) * ∑ n ∈ Icc 1 N, x n ^ 2 +
        th * ∑ n ∈ Icc 1 N, (n : ℝ) / N * Real.log n * x n ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun n hn => by
      nlinarith [mul_le_mul_of_nonneg_right (hrowbd n hn) (sq_nonneg (x n))]
  have hX := sum_nonneg fun n (_ : n ∈ Icc 1 N) => sq_nonneg (x n)
  nlinarith [mul_le_mul_of_nonneg_left htopsum hth0.le, mul_le_mul_of_nonneg_right hthε hD,
    mul_le_mul_of_nonneg_right hthB hX]

/-! ### The smooth valuation chain -/

/-- The finite-prime chain has gap `2 log 2 − ε` on the explicit scale conditions. -/
theorem smoothVar_le_smoothEnergy_of_scale {Q X : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hl1 : 1 ≤ Real.log X)
    (hl2 : 64 * (2 * Real.log 2) * logSum Q / ε ≤ Real.log X)
    (hl3 : 128 * logSum Q * ladderConstant Q / ε ≤ Real.log X)
    (hs : 32 * logSum Q / ε + 1 ≤ Real.sqrt (Real.sqrt X))
    (hp : (1 / 2 : ℝ) ^ X ≤ ε / (4 * (2 * Real.log 2))) (hX2 : 2 ≤ X) (h : ℕ → ℝ) :
    (2 * Real.log 2 - ε) * smoothVar Q X h ≤ smoothEnergy Q X h := by
  set A := 2 * Real.log 2
  set L := logSum Q
  set M := ladderConstant Q
  have hA : 0 < A := by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
  have hL := logSum_nonneg Q
  have hM := ladderConstant_nonneg Q
  have hlX : 0 < Real.log X := by linarith
  have hT : 0 < Real.sqrt (Real.sqrt X) := by linarith [show 0 ≤ 32 * L / ε by positivity]
  have hpow' : (1 / 2 : ℝ) ^ (X + 1) ≤ ε / (4 * A) :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ X)).trans hp
  have hmain := smoothVar_mul_le (Q := Q) hX2 h
  have hV : 0 ≤ smoothVar Q X h := wVar_nonneg fun _ _ => by positivity
  have ht : A * (16 * L / Real.log X) ≤ ε / 4 := by
    rw [div_le_iff₀ hε] at hl2
    rw [mul_div_assoc', div_le_iff₀ hlX]; nlinarith
  have hs1 : 4 * L / Real.sqrt (Real.sqrt X) ≤ ε / 8 := by
    rw [div_le_iff₀ hT]
    have : 32 * L / ε ≤ Real.sqrt (Real.sqrt X) := by linarith
    rw [div_le_iff₀ hε] at this; nlinarith
  have hs2 : 16 * L * M / Real.log X ≤ ε / 8 := by
    rw [div_le_iff₀ hε] at hl3
    rw [div_le_iff₀ hlX]; nlinarith
  have hg : A - ε / 4 ≤ boxGap X := by
    rw [boxGap]
    have := mul_le_mul_of_nonneg_left hpow' hA.le
    rw [mul_div_assoc', mul_comm A ε, mul_div_mul_right _ _ hA.ne'] at this
    nlinarith
  have hcoef : (A - ε) * (1 + 16 * L / Real.log X) ≤
      boxGap X - 4 * L / Real.sqrt (Real.sqrt X) - 16 * L * M / Real.log X := by
    have h16 : 0 ≤ 16 * L / Real.log X := by positivity
    nlinarith
  have h1t : 0 < 1 + 16 * L / Real.log X := by positivity
  have := mul_le_mul_of_nonneg_right hcoef hV
  have h2 : (A - ε) * smoothVar Q X h * (1 + 16 * L / Real.log X) ≤
      smoothEnergy Q X h * (1 + 16 * L / Real.log X) := by nlinarith
  exact le_of_mul_le_mul_right h2 h1t

/-! ### The explicit horizon -/

/-- The prime cutoff where the rough fibres cost at most `1/8`. -/
def gapCutoff : ℕ := ⌈Real.exp (8 * tensorizationConstant)⌉₊ + 2

/-- The two-scale tolerance of precision `ε`. -/
def gapRate (ε : ℝ) : ℝ := min (1 / 2 : ℝ) (ε / 24)

/-- The logarithmic scale of the smooth grid at precision `ε`. -/
def gapScale (ε : ℝ) : ℝ :=
  1 + 64 * (2 * Real.log 2) * logSum gapCutoff / (ε / 2) +
    128 * logSum gapCutoff * ladderConstant gapCutoff / (ε / 2) +
    2 * (ladderConstant gapCutoff + 1) / gapRate ε +
    4 * Real.log (32 * logSum gapCutoff / (ε / 2) + 1) + 4 * (2 * Real.log 2) / (ε / 2)

/-- The smooth grid at precision `ε`. -/
def gapGrid (ε : ℝ) : ℕ := ⌈Real.exp (gapScale ε)⌉₊ + 2

/-- The rough mass needed above the grid. -/
def gapMass (ε : ℝ) : ℝ :=
  (1 + Real.log (gapGrid ε)) / gapRate ε +
    16 * (1 + 1 / gapRate ε) * logSum gapCutoff / (2 * Real.log 2 - ε / 2)

/-- **The explicit horizon of the spectral gap at precision `ε`.** -/
def gapHorizon (ε : ℝ) : ℕ :=
  gapGrid ε * (⌈Real.exp (gapMass ε / RHTower.mertensPrimeProduct (gapCutoff - 1))⌉₊ + 1)

private theorem tensorization_cost_le :
    tensorizationConstant / Real.log gapCutoff ≤ 1 / 8 := by
  have hQ : Real.exp (8 * tensorizationConstant) ≤ (gapCutoff : ℝ) := by
    have := Nat.le_ceil (Real.exp (8 * tensorizationConstant))
    unfold gapCutoff
    push_cast
    linarith
  have hlQ0 : 0 < Real.log (gapCutoff : ℝ) := by
    refine Real.log_pos ?_
    have : 1 < gapCutoff := by unfold gapCutoff; omega
    exact_mod_cast this
  have h3 : 8 * tensorizationConstant ≤ Real.log (gapCutoff : ℝ) := by
    calc 8 * tensorizationConstant = Real.log (Real.exp (8 * tensorizationConstant)) :=
          (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) hQ
  rw [div_le_iff₀ hlQ0]
  linarith only [h3]

/-- **The multiplicative walk has Poincaré constant `2 log 2`, with an explicit horizon.** -/
theorem mul_harmonicVar_le_poleDefect_of_horizon {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {N : ℕ}
    (hN : gapHorizon ε ≤ N) (x : ℕ → ℝ) :
    (2 * Real.log 2 - ε) * harmonicVar 0 N (poleGauge x) ≤ poleDefect N x := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hεl : ε < 2 * Real.log 2 := by linarith only [hε1, hl2]
  have hg₁ : 0 < 2 * Real.log 2 - ε / 2 := by linarith only [hεl, hε]
  have hτ0 : 0 < gapRate ε := lt_min (by norm_num) (by linarith only [hε])
  obtain ⟨hK, hKt⟩ := tensorizationConstant_spec
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = gapCutoff := ⟨_, rfl⟩
  have hQ2 : 2 ≤ Q := by rw [hQd]; unfold gapCutoff; omega
  have hκ : tensorizationConstant / Real.log Q ≤ 1 / 8 := hQd ▸ tensorization_cost_le
  have hL0 := logSum_nonneg Q
  have hM0 := ladderConstant_nonneg Q
  obtain ⟨X, hXd⟩ : ∃ X, X = gapGrid ε := ⟨_, rfl⟩
  have hX2 : 2 ≤ X := by rw [hXd]; unfold gapGrid; omega
  have hε' : 0 < ε / 2 := by linarith only [hε]
  -- the scale inequalities on the grid
  have hscaleX : gapScale ε ≤ Real.log X := by
    have h1 : Real.exp (gapScale ε) ≤ (X : ℝ) := by
      have hc := Nat.le_ceil (Real.exp (gapScale ε))
      rw [hXd]
      unfold gapGrid
      push_cast
      linarith only [hc]
    calc gapScale ε = Real.log (Real.exp (gapScale ε)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) h1
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hpart (h₁ h₂ h₃ h₄ h₅ h₆ : ℝ) (e : gapScale ε = 1 + h₁ + h₂ + h₃ + h₄ + h₅)
      (h1 : 0 ≤ h₁) (h2 : 0 ≤ h₂) (h3 : 0 ≤ h₃) (h4 : 0 ≤ h₄) (h5 : 0 ≤ h₅) (_ : h₆ = 0) :
      1 ≤ Real.log X ∧ h₁ ≤ Real.log X ∧ h₂ ≤ Real.log X ∧ h₃ ≤ Real.log X ∧ h₄ ≤ Real.log X ∧
        h₅ ≤ Real.log X := by
    rw [e] at hscaleX
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hscaleX, h1, h2, h3, h4, h5]
  have hlogb : 0 ≤ Real.log (32 * logSum Q / (ε / 2) + 1) := by
    refine Real.log_nonneg ?_
    have : 0 ≤ 32 * logSum Q / (ε / 2) := by positivity
    linarith only [this]
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨hl1, hl2a, hl3, h2M, h4b, h4A⟩ := hpart
    (64 * (2 * Real.log 2) * logSum Q / (ε / 2))
    (128 * logSum Q * ladderConstant Q / (ε / 2))
    (2 * (ladderConstant Q + 1) / gapRate ε)
    (4 * Real.log (32 * logSum Q / (ε / 2) + 1))
    (4 * (2 * Real.log 2) / (ε / 2)) 0
    (by rw [hQd]; rfl) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) rfl
  have hlX : 0 < Real.log X := by linarith only [hl1]
  -- the root condition
  have hroot : 32 * logSum Q / (ε / 2) + 1 ≤ Real.sqrt (Real.sqrt X) := by
    obtain ⟨b, hb⟩ : ∃ b, b = 32 * logSum Q / (ε / 2) + 1 := ⟨_, rfl⟩
    have hb1 : 1 ≤ b := by
      have : 0 ≤ 32 * logSum Q / (ε / 2) := by positivity
      rw [hb]; linarith only [this]
    have hb0 : 0 < b := by linarith only [hb1]
    rw [← hb] at h4b ⊢
    have hle : Real.log (b ^ 4) ≤ Real.log X := by
      rw [Real.log_pow]
      exact_mod_cast h4b
    have hb4 : b ^ 4 ≤ (X : ℝ) := (Real.log_le_log_iff (by positivity) hX0).mp hle
    refine Real.le_sqrt_of_sq_le (Real.le_sqrt_of_sq_le ?_)
    calc ((b ^ 2) ^ 2 : ℝ) = b ^ 4 := by ring
      _ ≤ (X : ℝ) := hb4
  -- the dyadic condition
  have hdyadic : (1 / 2 : ℝ) ^ X ≤ (ε / 2) / (4 * (2 * Real.log 2)) := by
    have h2X : (X : ℝ) ≤ (2 : ℝ) ^ X := by exact_mod_cast (Nat.lt_two_pow_self (n := X)).le
    have hXbig : 4 * (2 * Real.log 2) / (ε / 2) ≤ X := by
      have hle := Real.log_le_self hX0.le
      linarith only [h4A, hle]
    rw [one_div, inv_pow]
    have h1 : ((2 : ℝ) ^ X)⁻¹ ≤ (X : ℝ)⁻¹ := inv_anti₀ hX0 h2X
    refine h1.trans ?_
    have hc : 0 < 4 * (2 * Real.log 2) / (ε / 2) := by positivity
    have h3 := inv_anti₀ hc hXbig
    refine h3.trans_eq ?_
    rw [inv_div]
  have hX₀ : ∀ h : ℕ → ℝ, (2 * Real.log 2 - ε / 2) * smoothVar Q X h ≤ smoothEnergy Q X h :=
    fun h => smoothVar_le_smoothEnergy_of_scale hε' hl1 hl2a hl3 hroot hdyadic hX2 h
  have hML : 2 * ladderConstant Q / Real.log X ≤ gapRate ε := by
    rw [div_le_iff₀ hlX]
    have := (div_le_iff₀ hτ0).mp h2M
    nlinarith only [this, hτ0]
  have h2L : 2 / Real.log X ≤ gapRate ε := by
    rw [div_le_iff₀ hlX]
    have := (div_le_iff₀ hτ0).mp h2M
    nlinarith only [this, hτ0, hM0]
  -- the rough mass beyond the grid
  obtain ⟨m, hmd⟩ : ∃ m, m = RHTower.mertensPrimeProduct (Q - 1) := ⟨_, rfl⟩
  have hm : 0 < m := hmd ▸ mertensPrimeProduct_pos _
  obtain ⟨T, hTd⟩ : ∃ T, T = ⌈Real.exp (gapMass ε / m)⌉₊ := ⟨_, rfl⟩
  have hNge : X * (T + 1) ≤ N := by
    rw [hXd, hTd, hmd, hQd]
    exact hN
  have hXN : X ≤ N := (Nat.le_mul_of_pos_right X (by omega)).trans hNge
  have hG : gapMass ε ≤ roughHarmonic Q (N / X) := by
    have hNX : T + 1 ≤ N / X := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hNge)
    have h1 := mertensPrimeProduct_mul_log_le_roughHarmonic (Q - 1) (N / X)
    rw [show Q - 1 + 1 = Q by omega, ← hmd] at h1
    have h2 : Real.exp (gapMass ε / m) ≤ ((N / X : ℕ) : ℝ) + 1 := by
      have hc := Nat.le_ceil (Real.exp (gapMass ε / m))
      have h3 : ((T + 1 : ℕ) : ℝ) ≤ ((N / X : ℕ) : ℝ) := by exact_mod_cast hNX
      rw [← hTd] at hc
      push_cast at h3
      linarith only [hc, h3]
    have h4 : gapMass ε / m ≤ Real.log (((N / X : ℕ) : ℝ) + 1) := by
      calc gapMass ε / m = Real.log (Real.exp (gapMass ε / m)) := (Real.log_exp _).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos _) h2
    rw [div_le_iff₀ hm] at h4
    linarith only [h4, h1]
  -- the two-scale inequality
  have hGX : (1 + Real.log X) / gapRate ε + 16 * (1 + 1 / gapRate ε) * logSum Q /
      (2 * Real.log 2 - ε / 2) ≤ roughHarmonic Q (N / X) := by
    rw [hQd, hXd]
    rw [hQd, hXd] at hG
    exact hG
  obtain ⟨hρ, hc⟩ := ratio_bounds (F := roughHarmonic Q N) (G := roughHarmonic Q (N / X)) hτ0 hg₁
    (logSum_nonneg Q) hlX.le
    (by have := roughHarmonic_sub_div_le Q N (show 1 ≤ X by omega); linarith) hGX
    (min_le_left _ _)
  have hcore := two_scale_le hX2 hXN hg₁ hτ0 (poleGauge x) (hX₀ _)
  have hU := sum_fibreVar_le hK.le hKt hQ2 N (poleGauge x)
  have hVW : harmonicVar 0 N (poleGauge x) ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (poleGauge x n -
      wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N (poleGauge x))) ^ 2 := by
    rw [harmonicVar, roughInterval_zero]
    exact wVar_le (fun n _ => by positivity) _
  rw [← walkEnergy_small_add_large Q N x]
  have hW := gap_of_two_scale hε hεl rfl hτ0 (min_le_left _ _) (min_le_right _ _) hML h2L
    (sum_nonneg fun n _ => by positivity)
    (sum_nonneg fun a _ => mul_nonneg (by positivity) (harmonicVar_nonneg _ _ _))
    (walkEnergy_nonneg _ _ _) (walkEnergy_nonneg _ _ _) hρ hc hκ hU hcore
  exact (mul_le_mul_of_nonneg_left hVW (by linarith only [hεl])).trans hW

/-- **The explicit horizon of the primitive depth law at precision `ε`.** -/
def primitiveDepthHorizon (ε : ℝ) : ℕ :=
  max (⌈Real.exp (deficitLogHorizon (min (1 / 2 : ℝ) (ε / 6)))⌉₊ + 1) (gapHorizon (ε / 2))

/-- **The prime form lies `2 log 2` below its pole, with an explicit horizon.** -/
theorem atomicWeilForm_le_two_log_two_of_horizon {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {N : ℕ}
    (hN : primitiveDepthHorizon ε ≤ N) (x : ℕ → ℝ)
    (hx : ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0) :
    atomicWeilForm N x ≤ (Real.log N - γ - 2 * Real.log 2 + ε) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  set ε₁ := min (1 / 2 : ℝ) (ε / 6)
  have hε₁ : 0 < ε₁ := lt_min (by norm_num) (by linarith)
  have hε₁2 : ε₁ ≤ 1 / 2 := min_le_left _ _
  have hε₁6 : ε₁ ≤ ε / 6 := min_le_right _ _
  have hN₁ : ⌈Real.exp (deficitLogHorizon ε₁)⌉₊ + 1 ≤ N := (le_max_left _ _).trans hN
  have hN₂ : gapHorizon (ε / 2) ≤ N := (le_max_right _ _).trans hN
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlog : deficitLogHorizon ε₁ ≤ Real.log N := by
    have hc := Nat.le_ceil (Real.exp (deficitLogHorizon ε₁))
    have hc2 : ((⌈Real.exp (deficitLogHorizon ε₁)⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN₁
    push_cast at hc2
    have hexp : Real.exp (deficitLogHorizon ε₁) ≤ N := by linarith only [hc, hc2]
    calc deficitLogHorizon ε₁ = Real.log (Real.exp (deficitLogHorizon ε₁)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) hexp
  have h1 := atomicWeilForm_add_poleDefect_le_of_horizon hε₁ (by linarith only [hε₁2]) hN1 hlog x
  have h2 := mul_harmonicVar_le_poleDefect_of_horizon (show 0 < ε / 2 by linarith)
    (by linarith only [hε1]) hN₂ x
  rw [harmonicVar_poleGauge_eq hx] at h2
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - ε₁ by linarith)
  have h4 : ε₁ * (1 + 2 * Real.log 2) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤
      ε / 2 * ∑ n ∈ Icc 1 N, x n ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) hS
  have h5 : 0 ≤ ε₁ * (ε / 2) * ∑ n ∈ Icc 1 N, x n ^ 2 := by positivity
  nlinarith

/-- **The primitive depth law with an explicit horizon.** On the star of `d`, with pole-orthogonal
pullback and `⌊N/d⌋ ≥ primitiveDepthHorizon ε`, the renormalized prime form is at least
`(log d + 2 log 2 − ε)` times the mass. -/
theorem renormalizedPrimeForm_starRestrict_ge_primitive_of_horizon {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {d N : ℕ} (hd : 0 < d) (hdN : d ≤ N) (hM : primitiveDepthHorizon ε ≤ N / d)
    (x : ℕ → ℝ) (hprim : ∑ a ∈ Icc 1 (N / d), starPullback d x a / Real.sqrt a = 0) :
    (Real.log d + 2 * Real.log 2 - ε) * ∑ n ∈ Icc 1 N, starRestrict d x n ^ 2 ≤
      renormalizedPrimeForm N (starRestrict d x) := by
  rw [renormalizedPrimeForm_starRestrict hd, sum_sq_starRestrict hd, renormalizedPrimeForm]
  have h1 := atomicWeilForm_le_two_log_two_of_horizon hε hε1 hM (starPullback d x) hprim
  have h2 := log_le_log_sub_log_div hd hdN
  have hmass : 0 ≤ ∑ a ∈ Icc 1 (N / d), starPullback d x a ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  nlinarith only [h1, h2, hmass]

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
