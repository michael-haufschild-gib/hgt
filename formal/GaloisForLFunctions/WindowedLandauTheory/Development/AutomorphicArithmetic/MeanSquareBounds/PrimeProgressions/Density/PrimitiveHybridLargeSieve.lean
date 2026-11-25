import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.ShortIntervalLargeSieve
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimeGallagher

/-! Gallagher's logarithmic windows give the hybrid large sieve for primitive characters. -/

open Complex Finset MeasureTheory RHTower.Sieve

namespace QH.PrimeProgressions

open Classical in
private theorem primitive_log_window_le {Q : ℕ} (hQ : 2 ≤ Q) {S : Finset ℕ}
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) {T : ℝ} (hT : 1 ≤ T) (u : ℝ) :
    ∑ r ∈ range Q, ∑ χ ∈ univ.filter (DirichletCharacter.IsPrimitive (R := ℂ) (n := r + 1)),
      ‖logWindowSum (fun n => a n * χ (n : ZMod (r + 1))) S (1 / T) u‖ ^ 2 ≤
    ∑ n ∈ S, Set.indicator (logWindow (1 / T) n)
      (fun _ => 2 * ((Q : ℝ) ^ 2 + n / T) * ‖a n‖ ^ 2) u := by
  classical
  let δ : ℝ := 1 / T
  let W := S.filter (fun n => u ∈ logWindow δ n)
  let x := Real.exp u
  let y := Real.exp (u + δ)
  let L := ⌊y⌋₊ - ⌊x⌋₊
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hδ : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := (div_le_one hT0).2 hT
  have hx : 0 < x := Real.exp_pos _
  have hxy : x ≤ y := Real.exp_le_exp.mpr (le_add_of_nonneg_right hδ)
  have hmem {n : ℕ} (hn : n ∈ W) : x < n ∧ (n : ℝ) ≤ y := by
    obtain ⟨hSn, hw⟩ := mem_filter.mp hn
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast hS n hSn
    change Real.log (n : ℝ) - δ ≤ u ∧ u < Real.log (n : ℝ) at hw
    exact ⟨(Real.lt_log_iff_exp_lt hn₀).mp hw.2,
      (Real.log_le_iff_le_exp hn₀).mp ((sub_le_iff_le_add).mp hw.1)⟩
  have hW : W ⊆ Ico (⌊x⌋₊ + 1) (⌊x⌋₊ + 1 + L) := by
    intro n hn
    obtain ⟨hg, hl⟩ := hmem hn
    have h₁ := (Nat.floor_lt hx.le).2 hg
    have h₂ := Nat.le_floor hl
    have he := Nat.add_sub_cancel' (Nat.floor_mono hxy)
    change ⌊x⌋₊ + (⌊y⌋₊ - ⌊x⌋₊) = ⌊y⌋₊ at he
    exact mem_Ico.2 ⟨by omega, by change n < ⌊x⌋₊ + 1 + (⌊y⌋₊ - ⌊x⌋₊); omega⟩
  have hwidth : (L : ℝ) ≤ 2 * x / T + 1 := by
    have he : y - x = x * (Real.exp δ - 1) := by dsimp [x, y]; rw [Real.exp_add]; ring
    have hexp : Real.exp δ - 1 ≤ 2 * δ := by
      have h := Real.abs_exp_sub_one_le (x := δ) (by simpa [abs_of_nonneg hδ] using hδ1)
      rw [abs_of_nonneg hδ] at h
      exact (le_abs_self _).trans h
    have hl := mul_le_mul_of_nonneg_left hexp hx.le
    have h₁ := Nat.floor_le (hx.le.trans hxy)
    have h₂ := Nat.sub_one_lt_floor x
    dsimp only [L]
    rw [Nat.cast_sub (Nat.floor_mono hxy)]
    have hh : y - x ≤ 2 * x / T := by
      rw [he]
      calc
        x * (Real.exp δ - 1) ≤ x * (2 * δ) := hl
        _ = 2 * x / T := by dsimp [δ]; ring
    linarith only [hh, h₁, h₂]
  have hsum (r : ℕ) (χ : DirichletCharacter ℂ (r + 1)) :
      logWindowSum (fun n => a n * χ (n : ZMod (r + 1))) S δ u =
      ∑ n ∈ W, a n * χ (n : ZMod (r + 1)) := by
    dsimp only [W]
    rw [logWindowSum, sum_filter]
    exact sum_congr rfl fun n _ => by
      by_cases hn : u ∈ logWindow δ n <;> simp [hn]
  change (∑ r ∈ range Q, ∑ χ ∈ univ.filter (DirichletCharacter.IsPrimitive (R := ℂ) (n := r + 1)),
      ‖logWindowSum (fun n => a n * χ (n : ZMod (r + 1))) S δ u‖ ^ 2) ≤ _
  simp_rw [hsum]
  refine (primitive_short_interval_large_sieve hQ hW a).trans ?_
  rw [mul_sum]
  calc
    _ ≤ ∑ n ∈ W, 2 * ((Q : ℝ) ^ 2 + n / T) * ‖a n‖ ^ 2 := by
      refine sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hle : 2 * x / T ≤ 2 * ((n : ℝ) / T) := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hmem hn).1.le (by norm_num)) hT0.le
      linarith only [hle, hwidth]
    _ = _ := by
      dsimp only [W]
      rw [sum_filter]
      exact sum_congr rfl fun n _ => by
        let b := 2 * ((Q : ℝ) ^ 2 + n / T) * ‖a n‖ ^ 2
        change (if u ∈ logWindow δ n then b else 0) = (logWindow δ n).indicator (fun _ => b) u
        by_cases hn : u ∈ logWindow δ n
        · rw [if_pos hn, Set.indicator_of_mem hn]
        · rw [if_neg hn, Set.indicator_of_notMem hn]

open Classical in
/-- Mean square over moduli up to Q and heights in the interval [-T,T]. -/
theorem primitive_hybrid_large_sieve {Q : ℕ} (hQ : 2 ≤ Q) {S : Finset ℕ}
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) {T : ℝ} (hT : 1 ≤ T) :
    ∑ r ∈ range Q, ∑ χ ∈ univ.filter (DirichletCharacter.IsPrimitive (R := ℂ) (n := r + 1)),
      (∫ t in (-T)..T, ‖∑ n ∈ S, a n * χ (n : ZMod (r + 1)) * (n : ℂ) ^ (-(t * I))‖ ^ 2) ≤
    8 * Real.pi * ∑ n ∈ S, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  classical
  let δ : ℝ := 1 / T
  let F (r : ℕ) (χ : DirichletCharacter ℂ (r + 1)) (u : ℝ) :=
    ‖logWindowSum (fun n => a n * χ (n : ZMod (r + 1))) S δ u‖ ^ 2
  let χs (r : ℕ) := univ.filter (DirichletCharacter.IsPrimitive (R := ℂ) (n := r + 1))
  let w (n : ℕ) := 2 * ((Q : ℝ) ^ 2 + n / T) * ‖a n‖ ^ 2
  let K (n : ℕ) := Set.indicator (logWindow δ n) (fun _ => w n)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hδ : 0 ≤ δ := by positivity
  have hF (r : ℕ) (χ : DirichletCharacter ℂ (r + 1)) : Integrable (F r χ) :=
    integrable_normSq_logWindowSum _ S δ
  have hK (n : ℕ) : Integrable (K n) :=
    (integrableOn_const (volume_logWindow_ne_top δ n) (by simp)).integrable_indicator
      (measurableSet_logWindow δ n)
  have hmass (n : ℕ) : ∫ u : ℝ, K n u = δ * w n := by
    dsimp only [K]
    rw [integral_indicator_const _ (measurableSet_logWindow δ n), smul_eq_mul,
      logWindow, measureReal_def, Real.volume_Ico, sub_sub_cancel, ENNReal.toReal_ofReal hδ]
  calc
    _ ≤ 4 * Real.pi * T ^ 2 * ∑ r ∈ range Q, ∑ χ ∈ χs r, ∫ u : ℝ, F r χ u := by
      rw [mul_sum]
      refine sum_le_sum fun r _ => ?_
      rw [mul_sum]
      exact sum_le_sum fun χ _ => prime_gallagher_mean _ S hS hT0
    _ = 4 * Real.pi * T ^ 2 * (∫ u : ℝ, ∑ r ∈ range Q, ∑ χ ∈ χs r, F r χ u) := by
      rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ fun χ _ => hF r χ)]
      exact congrArg (fun x : ℝ => 4 * Real.pi * T ^ 2 * x) (sum_congr rfl fun r _ =>
        (integral_finsetSum _ (fun χ _ => hF r χ)).symm)
    _ ≤ 4 * Real.pi * T ^ 2 * (∫ u : ℝ, ∑ n ∈ S, K n u) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact integral_mono
        (integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun χ _ => hF r χ)
        (integrable_finsetSum _ fun n _ => hK n) (primitive_log_window_le hQ hS a hT)
    _ = _ := by
      rw [integral_finsetSum _ (fun n _ => hK n), mul_sum, mul_sum]
      refine sum_congr rfl fun n _ => ?_
      rw [hmass]
      dsimp [δ, w]
      field_simp
      ring

end QH.PrimeProgressions
