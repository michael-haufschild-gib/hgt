import GaloisForLFunctions.WindowTowerOfSpecZ.TheTransferAcrossAStage
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover
import GaloisForLFunctions.RHTower.SeparatedBumpPrimeBlindPositivity

/-!
# The exit charge pays every new fold

At the stage `N + 1` a window of length `A` has the new fold `T_{N+1}` acting between its two
**collars** of width `ε = A − log(N+1)`: the left collar `[−A, −A + ε]` and the right collar `[−ε, 0]`;
they are exactly the ends of the fold (`inWindowCount_eq_collar`).

* **Collar exit charge** (`levyJump_ge_collar`): every archimedean jump longer than `ε` carries the
  collars out of the window, so for a window test
  `Ω(ε)·∫_{collars} H² ≤ J_∞(H)`, `Ω(ε) = ∫_ε^∞ ω` (RHTower `archLevyAntideriv`).
* **Uniform margin along the tower** (`primeJumpWeight_le_archLevyAntideriv`): on every stage the
  collar width is `< log((N+2)/(N+1)) ≤ log(3/2)`, so `Ω(ε) ≥ Ω(log(3/2)) ≥ log 3`
  (`log_three_le_archLevyAntideriv`), while every fold weight satisfies `Λ(n)/√n ≤ 2/e < log 3`
  (`primeJumpWeight_le`). The exit charge of the collars exceeds the weight of the new fold at every
  stage of the tower.
* **The exit charge pays every new fold** (`weilQuad_ge_reducedStageForm`): on a window of level
  `N + 1` past the entrance, `Q(H) ≥ Q_N(H) − Ω(ε)∫_{collars}H²`, while the reduced archimedean energy
  `J_∞(H) − Ω(ε)∫_{collars}H²` stays nonnegative. Crossing a stage costs the previous stage datum only a
  loan of its own collar exit charge.

New folds are never the obstruction at their entrance: the positivity problem of the tower is the
accumulated canonical class in the bulk of the window, not the creation of folds.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole
open RHTower.WeilLevyPoleGauss
open _root_.RHTower (archLevyDensity)

variable {A ε : ℝ} {H : ℝ → ℝ}

/-! ### Collars -/

/-- The collar weight `1_{[−ε,0]} + 1_{[−A,−A+ε]}`. -/
def collarWeight (A ε u : ℝ) : ℝ :=
  (Icc (-ε) 0).indicator 1 u + (Icc (-A) (-A + ε)).indicator 1 u

theorem collarWeight_nonneg (A ε u : ℝ) : 0 ≤ collarWeight A ε u :=
  add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
    (indicator_nonneg (fun _ _ => zero_le_one) _)

theorem collarWeight_mul (A ε u : ℝ) (f : ℝ → ℝ) :
    collarWeight A ε u * f u = (Icc (-ε) 0).indicator f u + (Icc (-A) (-A + ε)).indicator f u := by
  unfold collarWeight
  by_cases h1 : u ∈ Icc (-ε) 0 <;> by_cases h2 : u ∈ Icc (-A) (-A + ε) <;> simp [h1, h2, add_mul]

/-- The ends of the fold by `ℓ` are the collars of width `A − ℓ`. -/
theorem inWindowCount_eq_collar (A ℓ u : ℝ) : inWindowCount A ℓ u = collarWeight A (A - ℓ) u := by
  unfold inWindowCount collarWeight
  rw [show -(A - ℓ) = ℓ - A by ring, show -A + (A - ℓ) = -ℓ by ring, add_comm]

theorem archLevyDensity_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ archLevyDensity x := by
  unfold archLevyDensity
  have : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact div_nonneg (Real.exp_pos _).le (by linarith)

/-! ### The collar exit charge -/

/-- For a jump `y > ε` the collars leave the window: `∫_{collars} H² ≤ ∫(H − H(·+y))²`. -/
theorem collar_le_jump (hH : IsWindowTest A H) (hεA : ε ≤ A) {y : ℝ} (hy : ε < y) :
    ∫ u, collarWeight A ε u * H u ^ 2 ≤ ∫ u, (H u - H (u + y)) ^ 2 := by
  have hc := hH.continuous
  have iH := integrable_sq hc hH.hasCompactSupport
  have iHs : Integrable fun u => H (u + y) ^ 2 :=
    integrable_sq (hc.comp (continuous_add_const y)) (hasCompactSupport_comp_add
      hH.hasCompactSupport y)
  have iJ : Integrable fun u => (H u - H (u + y)) ^ 2 :=
    integrable_sq (hc.sub (hc.comp (continuous_add_const y)))
      (hH.hasCompactSupport.sub (hasCompactSupport_comp_add hH.hasCompactSupport y))
  -- the right collar jumps out of the window, the left collar is jumped into from outside
  have hpt : ∀ u, (Icc (-ε) 0).indicator (fun u => H u ^ 2) u +
      (Icc (-A - y) (-A - y + ε)).indicator (fun u => H (u + y) ^ 2) u ≤ (H u - H (u + y)) ^ 2 := by
    intro u
    by_cases h1 : u ∈ Icc (-ε) 0
    · have h2 : u ∉ Icc (-A - y) (-A - y + ε) := fun h => by linarith [h.2, h1.1]
      rw [indicator_of_mem h1, indicator_of_notMem h2, add_zero,
        hH.vanish (u + y) fun hm => by linarith [hm.2, h1.1], sub_zero]
    · rw [indicator_of_notMem h1, zero_add]
      by_cases h2 : u ∈ Icc (-A - y) (-A - y + ε)
      · rw [indicator_of_mem h2, hH.vanish u fun hm => by linarith [hm.1, h2.2], zero_sub, neg_sq]
      · rw [indicator_of_notMem h2]; exact sq_nonneg _
  have hleft : ∫ u, (Icc (-A - y) (-A - y + ε)).indicator (fun u => H (u + y) ^ 2) u =
      ∫ u, (Icc (-A) (-A + ε)).indicator (fun u => H u ^ 2) u := by
    rw [← integral_add_right_eq_self (fun u => (Icc (-A) (-A + ε)).indicator (fun u => H u ^ 2) u)
      y]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have hiff : u ∈ Icc (-A - y) (-A - y + ε) ↔ u + y ∈ Icc (-A) (-A + ε) := by
      simp only [mem_Icc]; constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith
    by_cases hu : u ∈ Icc (-A - y) (-A - y + ε)
    · simp only [indicator_of_mem hu, indicator_of_mem (hiff.mp hu)]
    · simp only [indicator_of_notMem hu, indicator_of_notMem (fun h => hu (hiff.mpr h))]
  have mI := measurableSet_Icc (a := -ε) (b := (0 : ℝ))
  have mJ := measurableSet_Icc (a := -A - y) (b := -A - y + ε)
  have mK := measurableSet_Icc (a := -A) (b := -A + ε)
  calc ∫ u, collarWeight A ε u * H u ^ 2
      = (∫ u, (Icc (-ε) 0).indicator (fun u => H u ^ 2) u) +
          ∫ u, (Icc (-A) (-A + ε)).indicator (fun u => H u ^ 2) u := by
        rw [← integral_add (iH.indicator mI) (iH.indicator mK)]
        exact integral_congr_ae (Eventually.of_forall fun u =>
          collarWeight_mul A ε u fun u => H u ^ 2)
    _ = ∫ u, ((Icc (-ε) 0).indicator (fun u => H u ^ 2) u +
          (Icc (-A - y) (-A - y + ε)).indicator (fun u => H (u + y) ^ 2) u) := by
        rw [integral_add (iH.indicator mI) (iHs.indicator mJ), hleft]
    _ ≤ ∫ u, (H u - H (u + y)) ^ 2 :=
        integral_mono ((iH.indicator mI).add (iHs.indicator mJ)) iJ hpt

/-- **Collar exit charge**: `Ω(ε)·∫_{collars}H² ≤ J_∞(H)` for a window test and `0 < ε ≤ A`. -/
theorem levyJump_ge_collar (hH : IsWindowTest A H) (hε : 0 < ε) (hεA : ε ≤ A) :
    archLevyAntideriv ε * ∫ u, collarWeight A ε u * H u ^ 2 ≤ levyJump H := by
  set C := ∫ u, collarWeight A ε u * H u ^ 2 with hCdef
  have hC : 0 ≤ C := integral_nonneg fun u => mul_nonneg (collarWeight_nonneg A ε u) (sq_nonneg _)
  have hΩ0 : 0 ≤ archLevyAntideriv ε := (archLevyAntideriv_pos hε).le
  have hfin := RHTower.SeparatedBump.lintegral_levy_ne_top hH.contDiff hH.hasCompactSupport
  rw [levyJump, ← ENNReal.ofReal_le_iff_le_toReal hfin]
  have hΩ : ENNReal.ofReal (archLevyAntideriv ε) =
      ∫⁻ x in Ioi ε, ENNReal.ofReal (archLevyDensity x) := by
    rw [← RHTower.WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hε]
    exact ofReal_integral_eq_lintegral_ofReal
      (RHTower.WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hε)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx =>
        archLevyDensity_nonneg (hε.trans hx)))
  calc ENNReal.ofReal (archLevyAntideriv ε * C)
      = (∫⁻ x in Ioi ε, ENNReal.ofReal (archLevyDensity x)) * ENNReal.ofReal C := by
        rw [ENNReal.ofReal_mul hΩ0, hΩ]
    _ = ∫⁻ x in Ioi ε, ENNReal.ofReal (archLevyDensity x * C) := by
        rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        rw [ENNReal.ofReal_mul (archLevyDensity_nonneg (hε.trans hx))]
    _ ≤ ∫⁻ x in Ioi ε, ENNReal.ofReal (archLevyDensity x * ∫ u, (H u - H (u + x)) ^ 2) :=
        setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (collar_le_jump hH hεA hx)
            (archLevyDensity_nonneg (hε.trans hx)))
    _ ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal (archLevyDensity x * ∫ u, (H u - H (u + x)) ^ 2) :=
        lintegral_mono_set (Ioi_subset_Ioi hε.le)

/-! ### The uniform margin -/

/-- `log y ≤ y/e` for `y > 0`. -/
theorem log_le_div_exp_one {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 1))
  rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

/-- **Every fold weight is at most `2/e`**: `Λ(n)/√n ≤ 2/e`. -/
theorem primeJumpWeight_le (n : ℕ) : primeJumpWeight n ≤ 2 / Real.exp 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeJumpWeight]; positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hlog : Real.log n ≤ 2 / Real.exp 1 * Real.sqrt n := by
    have h := log_le_div_exp_one hs
    have e : Real.log n = 2 * Real.log (Real.sqrt n) := by
      rw [Real.log_sqrt hn0.le]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * Real.log (Real.sqrt n) ≤ 2 * (Real.sqrt n / Real.exp 1) := this
      _ = 2 / Real.exp 1 * Real.sqrt n := by ring
  rw [primeJumpWeight, div_le_iff₀ hs]
  exact ArithmeticFunction.vonMangoldt_le_log.trans hlog

theorem two_div_exp_one_lt_log_three : 2 / Real.exp 1 < Real.log 3 := by
  have he : 2 < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h1 : 2 / Real.exp 1 < 1 := (div_lt_one (by positivity)).mpr he
  have h3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  linarith

/-- **`Ω(log(3/2)) ≥ log 3`**: the exit tail of the Gamma factor at the longest stage collar. -/
theorem log_three_le_archLevyAntideriv : Real.log 3 ≤ archLevyAntideriv (Real.log (3 / 2)) := by
  have hy : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  rw [archLevyAntideriv_eq_log_div hy]
  set t := Real.exp (-Real.log (3 / 2) / 2) with htdef
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  -- `t ≥ 4/5` since `(4/5)²·(3/2) = 24/25 ≤ 1`
  have ht45 : 4 / 5 ≤ t := by
    rw [htdef, ← Real.exp_log (by norm_num : (0 : ℝ) < 4 / 5), Real.exp_le_exp]
    have h : Real.log (4 / 5) + Real.log (4 / 5) + Real.log (3 / 2) ≤ 0 := by
      rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
      exact Real.log_nonpos (by norm_num) (by norm_num)
    linarith
  have h9 : (9 : ℝ) ≤ (1 + t) / (1 - t) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hlog9 : Real.log 9 ≤ Real.log ((1 + t) / (1 - t)) := Real.log_le_log (by norm_num) h9
  have h93 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have harc : 0 ≤ Real.arctan t := (Real.arctan_pos.mpr (Real.exp_pos _)).le
  linarith

/-- On every stage past its entrance the collar width lies in `(0, log(3/2))`. -/
theorem collarWidth_mem {N : ℕ} (hN : 1 ≤ N) (hA : windowLevel A = N + 1)
    (hpast : Real.log (N + 1 : ℕ) < A) :
    0 < A - Real.log (N + 1 : ℕ) ∧ A - Real.log (N + 1 : ℕ) ≤ Real.log (3 / 2) := by
  refine ⟨by linarith, ?_⟩
  have hlt : A < Real.log (N + 1 + 1 : ℕ) := by
    rw [windowLevel, Nat.floor_eq_iff (Real.exp_pos A).le] at hA
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact_mod_cast hA.2
  have hN1 : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hq : Real.log (N + 1 + 1 : ℕ) - Real.log (N + 1 : ℕ) ≤ Real.log (3 / 2) := by
    rw [← Real.log_div (by positivity) hN1.ne']
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ hN1]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    push_cast
    linarith
  linarith

/-- **Uniform margin**: on every stage past its entrance the collar exit tail exceeds the weight of
the new fold, `Λ(N+1)/√(N+1) ≤ Ω(A − log(N+1))`. -/
theorem primeJumpWeight_le_archLevyAntideriv {N : ℕ} (hN : 1 ≤ N) (hA : windowLevel A = N + 1)
    (hpast : Real.log (N + 1 : ℕ) < A) :
    primeJumpWeight (N + 1) ≤ archLevyAntideriv (A - Real.log (N + 1 : ℕ)) := by
  obtain ⟨h0, h1⟩ := collarWidth_mem hN hA hpast
  have hmono := antitoneOn_archLevyAntideriv (show A - Real.log (N + 1 : ℕ) ∈ Ioi 0 from h0)
    (show Real.log (3 / 2) ∈ Ioi 0 from Real.log_pos (by norm_num)) h1
  linarith [primeJumpWeight_le (N + 1), two_div_exp_one_lt_log_three,
    log_three_le_archLevyAntideriv]

/-! ### The exit charge pays every new fold -/

/-- **The exit charge pays every new fold**: on a window of level `N + 1` past the entrance, with
collar width `ε = A − log(N+1)`, `Q(H) ≥ Q_N(H) − Ω(ε)∫_{collars}H²` and
`J_∞(H) − Ω(ε)∫_{collars}H² ≥ 0`. -/
theorem weilQuad_ge_reducedStageForm (hH : IsWindowTest A H) {N : ℕ} (hN : 1 ≤ N)
    (hA : windowLevel A = N + 1) (hpast : Real.log (N + 1 : ℕ) < A) :
    stageForm N H - archLevyAntideriv (A - Real.log (N + 1 : ℕ)) *
        ∫ u, collarWeight A (A - Real.log (N + 1 : ℕ)) u * H u ^ 2 ≤ weilQuad H ∧
      0 ≤ levyJump H - archLevyAntideriv (A - Real.log (N + 1 : ℕ)) *
        ∫ u, collarWeight A (A - Real.log (N + 1 : ℕ)) u * H u ^ 2 := by
  obtain ⟨h0, _⟩ := collarWidth_mem hN hA hpast
  have hM : 0 ≤ ∫ u, collarWeight A (A - Real.log (N + 1 : ℕ)) u * H u ^ 2 :=
    integral_nonneg fun u => mul_nonneg (collarWeight_nonneg _ _ u) (sq_nonneg _)
  have hw := primeJumpWeight_le_archLevyAntideriv hN hA hpast
  have htr := weilQuad_ge_stageForm_sub_endMass hH hN hA
  simp_rw [inWindowCount_eq_collar] at htr
  refine ⟨?_, ?_⟩
  · nlinarith
  · have := levyJump_ge_collar hH h0 (by linarith [(Real.log_pos (show (1 : ℝ) < (N + 1 : ℕ) by
      exact_mod_cast (by omega : 1 < N + 1)))])
    linarith

end GaloisForLFunctions.WindowTowerOfSpecZ
