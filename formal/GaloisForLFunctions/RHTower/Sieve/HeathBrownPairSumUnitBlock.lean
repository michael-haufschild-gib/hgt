import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumDilation
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenReflectionArithmetic
import GaloisForLFunctions.HTGeometry.SeparatedPointCount

/-!
# Heath-Brown's pair sums and the reflected unit block

The corpus reflects the unit block `U_N(t) = Σ_{N<n≤2N} n^{−1−it}` (`mtWattUnitBlock N (2N)`)
by van der Corput's B-process into dual unit blocks `U_B`, `B ≍ t/N`, averaged against the
Perron weight `du/|1+iu|` (the Perron masses `P_B(t) = ∫_{−U}^{U} |U_B(u − t)| du/|1+iu|`).
This file connects that machinery with Heath-Brown's pair sums.

* `U_N(t) = Σ_{N<n≤2N} n^{−1} n^{−it}`, so `Σ_{t₁,t₂∈W} |U_N(t₁−t₂)|² = 𝒜₁((N, 2N])`.
* Weights: `𝒜_{1/2}((N,2N]) ≤ 2N 𝒜₁((N,2N])`, `𝒜₁((B,2B]) ≤ 𝒜_{1/2}((B,2B])/B`, and the
  unweighted pair sum with `|a_n| ≤ 1` is at most `2N 𝒜_{1/2}((N,2N])` (majorant principle).
* A `1`-separated set meets `[t − L, t + L]` in at most `2L + 1` points.
* **Perron masses over pairs.**  Cauchy–Schwarz against the Perron weight, whose mass on
  `[−U, U]` is at most `4 log(1+U)`, and the shift-invariance of the majorised pair sum give
  `Σ_{t₁,t₂∈W} P_B(|t₁−t₂|)² ≤ 2 (4 log(1+U))² 𝒜₁((B, 2B])`.
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset Complex

noncomputable section

/-- `n^{−1−it} = n^{−1} · n^{i(−t)}` for `n ≥ 1`. -/
theorem natCast_cpow_neg_one_sub_eq {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (-(1 : ℂ) - Complex.I * (t : ℂ)) =
      ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ) * hbPhase n (-t) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), hbPhase,
    ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le, Real.rpow_def_of_pos hn0,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The unit block is a Heath-Brown polynomial:** `U_{N,M}(t) = Σ_{N<n≤M} n^{−1} n^{i(−t)}`. -/
theorem mtWattUnitBlock_eq_hbPoly (N M : ℕ) (t : ℝ) :
    mtWattUnitBlock N M t =
      hbPoly (Finset.Ioc N M) (fun n => ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)) (-t) := by
  rw [mtWattUnitBlock_eq_sum_Ico, show Finset.Ico (N + 1) (M + 1) = Finset.Ioc N M by
    ext n; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega, hbPoly]
  refine Finset.sum_congr rfl fun n hn => ?_
  exact natCast_cpow_neg_one_sub_eq (by have := (Finset.mem_Ioc.mp hn).1; omega) t

/-- **Pair sums of the unit block** are the weight-`1` Heath-Brown pair sums. -/
theorem sum_normSq_mtWattUnitBlock_eq_hbAmp (W : Finset ℝ) (N M : ℕ) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖mtWattUnitBlock N M (t₁ - t₂)‖ ^ 2 =
      hbAmp W 1 (Finset.Ioc N M) := by
  rw [hbAmp, hbPairSum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t₂ _ => Finset.sum_congr rfl fun t₁ _ => ?_
  rw [mtWattUnitBlock_eq_hbPoly, neg_sub]

/-- `𝒜_{1/2}((N,2N]) ≤ 2N 𝒜₁((N,2N])`. -/
theorem hbAmp_half_le_two_mul_hbAmp_one (W : Finset ℝ) (N : ℕ) :
    hbAmp W (1 / 2) (Finset.Ioc N (2 * N)) ≤ 2 * N * hbAmp W 1 (Finset.Ioc N (2 * N)) := by
  have hmaj := hbPairSum_le_of_norm_le W (S := Finset.Ioc N (2 * N))
    (a := fun n => ((((n : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ))
    (b := fun n => Real.sqrt (2 * N) * (n : ℝ) ^ (-(1 : ℝ))) fun n hn => by
      obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn0.le _)]
      have hsq : Real.sqrt n ≤ Real.sqrt (2 * N) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hn2)
      have e1 : (n : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt n * (n : ℝ) ^ (-(1 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
        norm_num
      rw [e1]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hn0.le _)
  refine hmaj.trans (le_of_eq ?_)
  have e : (fun n : ℕ => ((Real.sqrt (2 * N) * (n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)) =
      fun n : ℕ => ((Real.sqrt (2 * N) : ℝ) : ℂ) * ((((n : ℝ) ^ (-(1 : ℝ))) : ℝ) : ℂ) := by
    funext n; push_cast; ring
  rw [e, hbPairSum_const_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity), hbAmp]

/-- `𝒜₁((B,2B]) ≤ 𝒜_{1/2}((B,2B])/B` for `B ≥ 1`. -/
theorem hbAmp_one_le_hbAmp_half_div (W : Finset ℝ) {B : ℕ} (hB : 0 < B) :
    hbAmp W 1 (Finset.Ioc B (2 * B)) ≤ hbAmp W (1 / 2) (Finset.Ioc B (2 * B)) / B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hmaj := hbPairSum_le_of_norm_le W (S := Finset.Ioc B (2 * B))
    (a := fun n => ((((n : ℝ) ^ (-(1 : ℝ))) : ℝ) : ℂ))
    (b := fun n => (Real.sqrt B)⁻¹ * (n : ℝ) ^ (-(1 / 2 : ℝ))) fun n hn => by
      obtain ⟨hn1, -⟩ := Finset.mem_Ioc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn0.le _)]
      have hsq : (Real.sqrt n)⁻¹ ≤ (Real.sqrt B)⁻¹ :=
        inv_anti₀ (Real.sqrt_pos.mpr hB0) (Real.sqrt_le_sqrt (by exact_mod_cast hn1.le))
      have e1 : (n : ℝ) ^ (-(1 : ℝ)) = (Real.sqrt n)⁻¹ * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]
        norm_num
      rw [e1]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hn0.le _)
  refine hmaj.trans (le_of_eq ?_)
  have e : (fun n : ℕ => (((Real.sqrt B)⁻¹ * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
      fun n : ℕ => (((Real.sqrt B)⁻¹ : ℝ) : ℂ) * ((((n : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) := by
    funext n; push_cast; ring
  rw [e, hbPairSum_const_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt hB0.le, hbAmp]
  ring

/-- The unweighted pair sum with `|a_n| ≤ 1` is at most `2N 𝒜_{1/2}((N,2N])`. -/
theorem hbPairSum_le_two_mul_hbAmp_half (W : Finset ℝ) {N : ℕ} {a : ℕ → ℂ}
    (ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc N (2 * N)) a ≤ 2 * N * hbAmp W (1 / 2) (Finset.Ioc N (2 * N)) := by
  have hmaj := hbPairSum_le_of_norm_le W (S := Finset.Ioc N (2 * N)) (a := a)
    (b := fun n => Real.sqrt (2 * N) * (n : ℝ) ^ (-(1 / 2 : ℝ))) fun n hn => by
      obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have h1 : (1 : ℝ) = Real.sqrt n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
        norm_num
      calc ‖a n‖ ≤ 1 := ha n hn
        _ = Real.sqrt n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast hn2))
            (Real.rpow_nonneg hn0.le _)
  refine hmaj.trans (le_of_eq ?_)
  have e : (fun n : ℕ => ((Real.sqrt (2 * N) * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
      fun n : ℕ => ((Real.sqrt (2 * N) : ℝ) : ℂ) * ((((n : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) := by
    funext n; push_cast; ring
  rw [e, hbPairSum_const_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity), hbAmp]

/-- A `1`-separated set meets `[t − L, t + L]` in at most `2L + 1` points. -/
theorem card_filter_abs_sub_le {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W) (t : ℝ)
    {L : ℝ} (hL : 0 ≤ L) : ((W.filter fun t' => |t - t'| ≤ L).card : ℝ) ≤ 2 * L + 1 := by
  have h := card_le_of_separated_of_subset_Icc (L := 1) (a := t - L) (b := t + L) one_pos
    (by linarith) (W.filter fun t' => |t - t'| ≤ L)
    (fun x hx y hy hxy => hW x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
    fun x hx => by
      have := (Finset.mem_filter.mp hx).2
      rw [abs_le] at this
      exact ⟨by linarith, by linarith⟩
  linarith

/-- **Perron masses over pairs.**
`Σ_{t₁,t₂∈W} P_B(|t₁−t₂|)² ≤ 2 (4 log(1+U))² 𝒜₁((B, 2B])` for `U ≥ 0`. -/
theorem sum_sq_ubPerronMass_abs_le (W : Finset ℝ) (B : ℕ) {U : ℝ} (hU : 0 ≤ U) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ubPerronMass B U |t₁ - t₂| ^ 2 ≤
      2 * (4 * Real.log (1 + U)) ^ 2 * hbAmp W 1 (Finset.Ioc B (2 * B)) := by
  obtain ⟨w, hw⟩ : ∃ w : ℝ → ℝ, w = fun u : ℝ => 1 / ‖(1 : ℂ) + (u : ℂ) * Complex.I‖ := ⟨_, rfl⟩
  have hwc : Continuous w := hw ▸ continuous_inv_norm_one_add
  have hw0 : ∀ u, 0 ≤ w u := fun u => hw ▸ inv_norm_one_add_nonneg u
  have hwmass : ∫ u in (-U)..U, w u ≤ 4 * Real.log (1 + U) := hw ▸ integral_inv_norm_one_add_le hU
  have hUU : -U ≤ U := by linarith
  have hwint0 : 0 ≤ ∫ u in (-U)..U, w u := intervalIntegral.integral_nonneg hUU fun u _ => hw0 u
  have hlog0 : 0 ≤ 4 * Real.log (1 + U) := le_trans hwint0 hwmass
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ → ℝ, F = fun s u => ‖mtWattUnitBlock B (2 * B) (u - s)‖ :=
    ⟨_, rfl⟩
  have hFc : ∀ s, Continuous (F s) := fun s => hF ▸
    ((continuous_mtWattUnitBlock B (2 * B)).comp (continuous_id.sub continuous_const)).norm
  -- Cauchy–Schwarz against the Perron weight
  have hcs : ∀ s, ubPerronMass B U s ^ 2 ≤
      4 * Real.log (1 + U) * ∫ u in (-U)..U, F s u ^ 2 * w u := by
    intro s
    have hs : Continuous fun u => Real.sqrt (w u) := Real.continuous_sqrt.comp hwc
    have h := GaloisForLFunctions.HTGeometry.sq_intervalIntegral_mul_le
      (g := fun u => F s u * Real.sqrt (w u)) (h := fun u => Real.sqrt (w u)) hUU
      ((hFc s).mul hs) hs
    beta_reduce at h
    have e1 : (∫ u in (-U)..U, F s u * Real.sqrt (w u) * Real.sqrt (w u)) = ubPerronMass B U s := by
      rw [ubPerronMass]
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [hF]
      rw [mul_assoc, Real.mul_self_sqrt (hw0 u), hw, mul_one_div]
    have e2 : (∫ u in (-U)..U, (F s u * Real.sqrt (w u)) ^ 2) = ∫ u in (-U)..U, F s u ^ 2 * w u :=
      intervalIntegral.integral_congr fun u _ => by rw [mul_pow, Real.sq_sqrt (hw0 u)]
    have e3 : (∫ u in (-U)..U, Real.sqrt (w u) ^ 2) = ∫ u in (-U)..U, w u :=
      intervalIntegral.integral_congr fun u _ => Real.sq_sqrt (hw0 u)
    rw [e1, e2, e3] at h
    have hint : 0 ≤ ∫ u in (-U)..U, F s u ^ 2 * w u :=
      intervalIntegral.integral_nonneg hUU fun u _ => mul_nonneg (sq_nonneg _) (hw0 u)
    calc ubPerronMass B U s ^ 2 ≤ (∫ u in (-U)..U, F s u ^ 2 * w u) * ∫ u in (-U)..U, w u := h
      _ ≤ (∫ u in (-U)..U, F s u ^ 2 * w u) * (4 * Real.log (1 + U)) :=
          mul_le_mul_of_nonneg_left hwmass hint
      _ = _ := by ring
  -- for each shift `u`, the pair sum of `U_B` at `u − |t₁ − t₂|` is at most `2 𝒜₁((B,2B])`
  have hpt : ∀ u, ∑ t₁ ∈ W, ∑ t₂ ∈ W, F |t₁ - t₂| u ^ 2 ≤
      2 * hbAmp W 1 (Finset.Ioc B (2 * B)) := by
    intro u
    have hshift : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖mtWattUnitBlock B (2 * B) (u - (t₁ - t₂))‖ ^ 2 ≤
        hbAmp W 1 (Finset.Ioc B (2 * B)) := by
      have h := sum_normSq_hbPoly_shift_le W (S := Finset.Ioc B (2 * B))
        (a := fun n => ((((n : ℝ) ^ (-(1 : ℝ))) : ℝ) : ℂ))
        (b := fun n => (n : ℝ) ^ (-(1 : ℝ))) (fun n _ => by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]) (-u)
      refine le_of_eq_of_le (Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl
        fun t₂ _ => ?_) h
      rw [mtWattUnitBlock_eq_hbPoly]
      congr 3
      ring
    have hsym : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖mtWattUnitBlock B (2 * B) (u + (t₁ - t₂))‖ ^ 2 =
        ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖mtWattUnitBlock B (2 * B) (u - (t₁ - t₂))‖ ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ => by
        rw [show u + (t₂ - t₁) = u - (t₁ - t₂) by ring]
    have hterm : ∀ t₁ t₂ : ℝ, F |t₁ - t₂| u ^ 2 ≤
        ‖mtWattUnitBlock B (2 * B) (u - (t₁ - t₂))‖ ^ 2 +
          ‖mtWattUnitBlock B (2 * B) (u + (t₁ - t₂))‖ ^ 2 := by
      intro t₁ t₂
      simp only [hF]
      rcases abs_choice (t₁ - t₂) with h | h <;> rw [h]
      · exact le_add_of_nonneg_right (sq_nonneg _)
      · rw [sub_neg_eq_add]
        exact le_add_of_nonneg_left (sq_nonneg _)
    calc ∑ t₁ ∈ W, ∑ t₂ ∈ W, F |t₁ - t₂| u ^ 2
        ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, (‖mtWattUnitBlock B (2 * B) (u - (t₁ - t₂))‖ ^ 2 +
            ‖mtWattUnitBlock B (2 * B) (u + (t₁ - t₂))‖ ^ 2) :=
          Finset.sum_le_sum fun t₁ _ => Finset.sum_le_sum fun t₂ _ => hterm t₁ t₂
      _ = 2 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖mtWattUnitBlock B (2 * B) (u - (t₁ - t₂))‖ ^ 2 := by
          simp only [Finset.sum_add_distrib]
          rw [hsym]
          ring
      _ ≤ 2 * hbAmp W 1 (Finset.Ioc B (2 * B)) := by linarith
  -- sum the Cauchy–Schwarz bound over pairs and integrate
  have hint : ∀ t₁ t₂ : ℝ, IntervalIntegrable (fun u => F |t₁ - t₂| u ^ 2 * w u)
      MeasureTheory.volume (-U) U := fun t₁ t₂ =>
    (((hFc _).pow 2).mul hwc).intervalIntegrable _ _
  have hA0 := hbAmp_nonneg W 1 (Finset.Ioc B (2 * B))
  calc ∑ t₁ ∈ W, ∑ t₂ ∈ W, ubPerronMass B U |t₁ - t₂| ^ 2
      ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, 4 * Real.log (1 + U) * ∫ u in (-U)..U, F |t₁ - t₂| u ^ 2 * w u :=
        Finset.sum_le_sum fun t₁ _ => Finset.sum_le_sum fun t₂ _ => hcs _
    _ = 4 * Real.log (1 + U) * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∫ u in (-U)..U, F |t₁ - t₂| u ^ 2 * w u := by
        simp only [Finset.mul_sum]
    _ = 4 * Real.log (1 + U) *
          ∫ u in (-U)..U, (∑ t₁ ∈ W, ∑ t₂ ∈ W, F |t₁ - t₂| u ^ 2) * w u := by
        congr 1
        have hinner : ∀ t₁ : ℝ, ∑ t₂ ∈ W, ∫ u in (-U)..U, F |t₁ - t₂| u ^ 2 * w u =
            ∫ u in (-U)..U, ∑ t₂ ∈ W, F |t₁ - t₂| u ^ 2 * w u := fun t₁ =>
          (intervalIntegral.integral_finsetSum fun t₂ _ => hint t₁ t₂).symm
        simp only [hinner]
        rw [← intervalIntegral.integral_finsetSum (fun t₁ _ => ?_)]
        · refine intervalIntegral.integral_congr fun u _ => ?_
          simp only [Finset.sum_mul]
        · exact (continuous_finsetSum _ fun t₂ _ =>
            ((hFc |t₁ - t₂|).pow 2).mul hwc).intervalIntegrable _ _
    _ ≤ 4 * Real.log (1 + U) * ∫ u in (-U)..U, 2 * hbAmp W 1 (Finset.Ioc B (2 * B)) * w u := by
        refine mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on hUU ?_ ?_
          fun u _ => mul_le_mul_of_nonneg_right (hpt u) (hw0 u)) hlog0
        · exact (Continuous.mul (continuous_finsetSum _ fun t₁ _ => continuous_finsetSum _
            fun t₂ _ => (hFc _).pow 2) hwc).intervalIntegrable _ _
        · exact (continuous_const.mul hwc).intervalIntegrable _ _
    _ = 4 * Real.log (1 + U) * (2 * hbAmp W 1 (Finset.Ioc B (2 * B)) *
          ∫ u in (-U)..U, w u) := by rw [intervalIntegral.integral_const_mul]
    _ ≤ 4 * Real.log (1 + U) * (2 * hbAmp W 1 (Finset.Ioc B (2 * B)) *
          (4 * Real.log (1 + U))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwmass (by positivity)) hlog0
    _ = 2 * (4 * Real.log (1 + U)) ^ 2 * hbAmp W 1 (Finset.Ioc B (2 * B)) := by ring

end

end RHTower.Sieve
