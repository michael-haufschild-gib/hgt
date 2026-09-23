import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantileOddWindowMismatchMass
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount
import GaloisForLFunctions.RHTower.MassBesselRadiationDivergence

namespace RHTower

private theorem prime_supply_weight_ge
    {K a x P : ℝ} {B : ℕ}
    (hK : 0 < K) (ha : 0 < a) (hx : 1 < x)
    (hB : 0 < B) (hBx : (B : ℝ) ≤ K * x)
    (hP : a * (x / Real.log x) ≤ P) :
    (a * Real.log 2 / Real.sqrt K) *
        (Real.sqrt x / Real.log x) ≤
      P * (Real.log 2 / Real.sqrt B) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hsB : 0 < Real.sqrt (B : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hB)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsble : Real.sqrt (B : ℝ) ≤ Real.sqrt (K * x) :=
    Real.sqrt_le_sqrt hBx
  have hweight : Real.log 2 / Real.sqrt (K * x) ≤
      Real.log 2 / Real.sqrt B :=
    div_le_div_of_nonneg_left hlog2.le hsB hsble
  have hcoeff : 0 ≤ a * (x / Real.log x) := by positivity
  have hprod : a * (x / Real.log x) *
        (Real.log 2 / Real.sqrt (K * x)) ≤
      a * (x / Real.log x) * (Real.log 2 / Real.sqrt B) :=
    mul_le_mul_of_nonneg_left hweight hcoeff
  have hprodP : a * (x / Real.log x) *
        (Real.log 2 / Real.sqrt B) ≤
      P * (Real.log 2 / Real.sqrt B) :=
    mul_le_mul_of_nonneg_right hP (by positivity)
  have hsplit : Real.sqrt (K * x) = Real.sqrt K * Real.sqrt x :=
    Real.sqrt_mul hK.le x
  have hroot : (Real.sqrt x) ^ (2 : ℕ) = x := Real.sq_sqrt (by linarith)
  calc
    (a * Real.log 2 / Real.sqrt K) * (Real.sqrt x / Real.log x) =
        a * (x / Real.log x) *
          (Real.log 2 / Real.sqrt (K * x)) := by
            rw [hsplit]
            field_simp [ne_of_gt hlx, ne_of_gt hsx, ne_of_gt hsK]
            nlinarith [hroot]
    _ ≤ _ := hprod
    _ ≤ _ := hprodP

private theorem prime_window_log_debit_le
    {K x : ℝ} {B : ℕ}
    (hK : 0 < K) (hx : 0 < x) (hB : 1 ≤ B)
    (hBx : (B : ℝ) ≤ K * x) :
    2 * Real.log B + Real.log 2 / Real.sqrt B ≤
      2 * (Real.log K + Real.log x) + Real.log 2 := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlogB : Real.log (B : ℝ) ≤ Real.log K + Real.log x := by
    calc
      Real.log (B : ℝ) ≤ Real.log (K * x) :=
        Real.log_le_log hBpos hBx
      _ = Real.log K + Real.log x :=
        Real.log_mul (ne_of_gt hK) (ne_of_gt hx)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt B := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ B by exact_mod_cast hB)
    simpa using h
  have hlog2 : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num))
  have hcost : Real.log 2 / Real.sqrt B ≤ Real.log 2 := by
    simpa using div_le_div_of_nonneg_left hlog2 (by norm_num : (0:ℝ)<1) hsqrt1
  linarith

/-- Critical-Mellin PNT main scale dominates every logarithmic separator
debit on fixed multiplicative windows. -/
theorem tendsto_odd_window_main_minus_log_atTop
    {a K : ℝ} (ha : 0 < a) :
    Filter.Tendsto
      (fun x : ℝ => a * Real.sqrt x / Real.log x -
        2 * (Real.log K + Real.log x) - Real.log 2)
      Filter.atTop Filter.atTop := by
  have hratio : Filter.Tendsto
      (fun x : ℝ => a * (Real.sqrt x / Real.log x ^ (2 : ℕ)))
      Filter.atTop Filter.atTop :=
    (tendsto_sqrt_div_log_pow_atTop 2).const_mul_atTop ha
  have hfactor : Filter.Tendsto
      (fun x : ℝ => a * (Real.sqrt x / Real.log x ^ (2 : ℕ)) - 2)
      Filter.atTop Filter.atTop :=
    hratio.atTop_add (tendsto_const_nhds (x := (-2 : ℝ)))
  have hlog : Filter.Tendsto Real.log Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop
  have hprod : Filter.Tendsto
      (fun x : ℝ => Real.log x *
        (a * (Real.sqrt x / Real.log x ^ (2 : ℕ)) - 2))
      Filter.atTop Filter.atTop :=
    hlog.atTop_mul_atTop₀ hfactor
  have hrest : Filter.Tendsto
      (fun _x : ℝ => -2 * Real.log K - Real.log 2)
      Filter.atTop (nhds (-2 * Real.log K - Real.log 2)) :=
    tendsto_const_nhds
  have hsum := hprod.atTop_add hrest
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  have hlogne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  change Real.log x *
      (a * (Real.sqrt x / Real.log x ^ (2 : ℕ)) - 2) +
        (-2 * Real.log K - Real.log 2) =
      a * Real.sqrt x / Real.log x -
        2 * (Real.log K + Real.log x) - Real.log 2
  field_simp [hlogne]
  ring

/-- PNT prime supply on the same literal canonical odd-log windows as the
completed-source mismatch law. -/
theorem eventually_ccmOddLogWindow_primeCount_ge_pnt :
    ∀ᶠ t : ℕ in Filter.atTop,
      (Real.exp (1 / 4 : ℝ) - 1) / 2 *
          (Real.exp ((2 * t + 1 : ℕ) : ℝ) /
            Real.log (Real.exp ((2 * t + 1 : ℕ) : ℝ))) ≤
        (((Finset.Icc (ccmOddLogWindowLower t)
          (ccmOddLogWindowUpper t)).filter Nat.Prime).card : ℝ) := by
  let K : ℝ := Real.exp (1 / 4 : ℝ)
  have hK : 1 < K := by
    dsimp [K]
    exact Real.one_lt_exp_iff.mpr (by norm_num)
  have hlin : Filter.Tendsto
      (fun t : ℕ => ((2 * t + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_mono
      (fun t : ℕ => by exact_mod_cast (show t ≤ 2 * t + 1 by omega))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hxTop : Filter.Tendsto
      (fun t : ℕ => Real.exp ((2 * t + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_exp_atTop.comp hlin
  have hpnt := hxTop.eventually
    (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge hK)
  filter_upwards [hpnt, hxTop.eventually_ge_atTop (1 / (K - 1))]
    with t hpnt hlarge
  let x : ℝ := Real.exp ((2 * t + 1 : ℕ) : ℝ)
  let A : ℕ := ccmOddLogWindowLower t
  let B : ℕ := ccmOddLogWindowUpper t
  have hx0 : 0 < x := Real.exp_pos _
  have hAreal : (A : ℝ) ≤ x + 1 := by
    have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    change ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ x + 1
    push_cast
    linarith
  have hgap : x + 1 ≤ K * x := by
    have hKdiff : 0 < K - 1 := by linarith
    have hlarge' : 1 / (K - 1) ≤ x := hlarge
    have hh : (1 : ℝ) ≤ x * (K - 1) :=
      (div_le_iff₀ hKdiff).mp hlarge'
    nlinarith
  have hAB : A ≤ B := by
    dsimp only [B, ccmOddLogWindowUpper]
    apply Nat.le_floor
    rw [Real.exp_add]
    simpa only [x, K, mul_comm] using hAreal.trans hgap
  have hBfloor : B = ⌊K * x⌋₊ := by
    change ⌊Real.exp (((2 * t + 1 : ℕ) : ℝ) + 1 / 4)⌋₊ =
      ⌊Real.exp (1 / 4 : ℝ) * Real.exp ((2 * t + 1 : ℕ) : ℝ)⌋₊
    rw [Real.exp_add, mul_comm]
  have hcard :
      ((Finset.Icc A B).filter Nat.Prime).card =
        (GaloisForLFunctions.HTGeometry.primesInIoc ⌊x⌋₊ B).card := by
    change ((Finset.Icc (⌊x⌋₊ + 1) B).filter Nat.Prime).card =
      ((Finset.Ioc ⌊x⌋₊ B).filter Nat.Prime).card
    rw [Finset.Icc_add_one_left_eq_Ioc]
  have hfloorB : ⌊x⌋₊ ≤ B := by
    change ⌊x⌋₊ + 1 ≤ B at hAB
    omega
  have hcount := GaloisForLFunctions.HTGeometry.card_primesInIoc hfloorB
  change (K - 1) / 2 * (x / Real.log x) ≤ _
  rw [hcard, hcount, hBfloor]
  exact hpnt

/-- The actual completed-source mismatch mass diverges on canonical
odd-centered prime-power windows. This is unconditional and uses PNT,
the active-path resonance exclusion, and the exact proper-power defect. -/
theorem tendsto_ccmOddLogWindowMismatchMass_atTop :
    Filter.Tendsto
      (fun t : ℕ => ∑ n ∈ ccmOddLogWindowMismatchSet
        (ccmOddLogWindowLower t) (ccmOddLogWindowUpper t),
        criticalMellinAtomWeight n)
      Filter.atTop Filter.atTop := by
  let K : ℝ := Real.exp (1 / 4 : ℝ)
  let α : ℝ := (K - 1) / 2
  let a : ℝ := α * Real.log 2 / Real.sqrt K
  have hK : 1 < K := by
    dsimp [K]
    exact Real.one_lt_exp_iff.mpr (by norm_num)
  have hKpos : 0 < K := by linarith
  have hα : 0 < α := by dsimp [α]; linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hlin : Filter.Tendsto
      (fun t : ℕ => ((2 * t + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_mono
      (fun t : ℕ => by exact_mod_cast (show t ≤ 2 * t + 1 by omega))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hxTop : Filter.Tendsto
      (fun t : ℕ => Real.exp ((2 * t + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_exp_atTop.comp hlin
  have hgrowth :=
    (tendsto_odd_window_main_minus_log_atTop (K := K) ha).comp hxTop
  refine Filter.tendsto_atTop.2 ?_
  intro C
  filter_upwards
    [eventually_ccmOddLogWindow_primeCount_ge_pnt,
      eventually_odd_window_prime_count_weight_le_two_mismatch_mass_add_log,
      hxTop.eventually_ge_atTop (max 2 K),
      hgrowth.eventually_ge_atTop (2 * C)]
    with t hpnt hsource hxlarge hgrowthC
  let x : ℝ := Real.exp ((2 * t + 1 : ℕ) : ℝ)
  let B : ℕ := ccmOddLogWindowUpper t
  let P : ℝ := (((Finset.Icc (ccmOddLogWindowLower t) B).filter Nat.Prime).card : ℝ)
  let M : ℝ := ∑ n ∈ ccmOddLogWindowMismatchSet
    (ccmOddLogWindowLower t) B, criticalMellinAtomWeight n
  have hx1 : 1 < x := by
    have hx2 : (2 : ℝ) ≤ x := (le_max_left _ _).trans hxlarge
    linarith
  have hB1 : 1 ≤ B := by
    change 1 ≤ ⌊Real.exp (((2 * t + 1 : ℕ) : ℝ) + 1 / 4)⌋₊
    apply Nat.le_floor
    have harg : (0 : ℝ) ≤ ((2 * t + 1 : ℕ) : ℝ) + 1 / 4 := by positivity
    simpa using Real.one_le_exp harg
  have hBpos : 0 < B := by omega
  have hBx : (B : ℝ) ≤ K * x := by
    change (⌊Real.exp (((2 * t + 1 : ℕ) : ℝ) + 1 / 4)⌋₊ : ℝ) ≤
      Real.exp (1 / 4 : ℝ) * Real.exp ((2 * t + 1 : ℕ) : ℝ)
    calc
      _ ≤ Real.exp (((2 * t + 1 : ℕ) : ℝ) + 1 / 4) :=
        Nat.floor_le (Real.exp_nonneg _)
      _ = Real.exp (1 / 4 : ℝ) * Real.exp ((2 * t + 1 : ℕ) : ℝ) := by
        rw [Real.exp_add]
        ring
  have hpnt' : α * (x / Real.log x) ≤ P := by
    simpa only [α, K, x, P, B] using hpnt
  have hsource' : P * (Real.log 2 / Real.sqrt B) ≤
      2 * M + 2 * Real.log (B : ℝ) + Real.log 2 / Real.sqrt B := by
    simpa only [P, M, B] using hsource
  have hweight := prime_supply_weight_ge hKpos hα hx1 hBpos hBx hpnt'
  have hdebit := prime_window_log_debit_le hKpos (by linarith : 0 < x) hB1 hBx
  have hmain : a * (Real.sqrt x / Real.log x) -
      2 * (Real.log K + Real.log x) - Real.log 2 ≤ 2 * M := by
    dsimp only [a]
    linarith
  change C ≤ M
  have hgrowthC' : 2 * C ≤
      a * Real.sqrt x / Real.log x -
        2 * (Real.log K + Real.log x) - Real.log 2 := hgrowthC
  have heq : a * (Real.sqrt x / Real.log x) =
      a * Real.sqrt x / Real.log x := by ring
  rw [heq] at hmain
  linarith

end RHTower
