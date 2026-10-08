import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Square-root mass on good notch scales

Finite partial summation prevents a nonnegative sequence with sublogarithmic
harmonic mass from having a positive square-root mass floor on every late scale.
-/

noncomputable section
open Finset Filter Topology

namespace RHTower.WeilSingularArithmetic

private theorem log_step_le_sqrt_step {x : ℝ} (hx : 1 ≤ x) :
    (Real.log (x + 1) - Real.log x) / 4 ≤
      Real.sqrt x * ((Real.sqrt x)⁻¹ - (Real.sqrt (x + 1))⁻¹) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < x + 1 := by linarith
  have ha := Real.sqrt_pos.mpr hx0
  have hb := Real.sqrt_pos.mpr hy0
  have hab : Real.sqrt x ≤ Real.sqrt (x + 1) := Real.sqrt_le_sqrt (by linarith)
  have hsa := Real.sq_sqrt hx0.le
  have hsb := Real.sq_sqrt hy0.le
  have hlog : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h
    have he : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    rwa [he] at h
  have hlog' : Real.log (x + 1) - Real.log x ≤ 2 / (x + 1) :=
    hlog.trans ((div_le_div_iff₀ hx0 hy0).mpr (by linarith))
  have hprod : (Real.sqrt (x + 1) - Real.sqrt x) *
      (Real.sqrt (x + 1) + Real.sqrt x) = 1 := by nlinarith
  have hone : 1 ≤ 2 * Real.sqrt (x + 1) * (Real.sqrt (x + 1) - Real.sqrt x) := by
    have h := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hab)
    nlinarith
  have hbnd : Real.sqrt (x + 1) ≤
      (Real.sqrt (x + 1) - Real.sqrt x) * (2 * (x + 1)) := by
    calc
      Real.sqrt (x + 1) = 1 * Real.sqrt (x + 1) := by ring
      _ ≤ (2 * Real.sqrt (x + 1) * (Real.sqrt (x + 1) - Real.sqrt x)) *
          Real.sqrt (x + 1) := mul_le_mul_of_nonneg_right hone hb.le
      _ = (Real.sqrt (x + 1) - Real.sqrt x) * (2 * (x + 1)) := by
        calc
          _ = (Real.sqrt (x + 1) - Real.sqrt x) * (2 * Real.sqrt (x + 1) ^ 2) := by ring
          _ = _ := by rw [hsb]
  have he : Real.sqrt x * ((Real.sqrt x)⁻¹ - (Real.sqrt (x + 1))⁻¹) =
      (Real.sqrt (x + 1) - Real.sqrt x) / Real.sqrt (x + 1) := by
    field_simp [ha.ne', hb.ne']
  rw [he]
  calc
    (Real.log (x + 1) - Real.log x) / 4 ≤ (2 / (x + 1)) / 4 :=
      div_le_div_of_nonneg_right hlog' (by norm_num)
    _ = 1 / (2 * (x + 1)) := by field_simp; ring
    _ ≤ (Real.sqrt (x + 1) - Real.sqrt x) / Real.sqrt (x + 1) :=
      (div_le_div_iff₀ (by positivity) hb).mpr (by simpa only [one_mul] using hbnd)

private theorem sqrt_weighted_partial_sum_lower {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) {ε D : ℝ} (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hfloor : ∀ k : ℕ, ε * Real.sqrt (k + 1) - D ≤ ∑ n ∈ range (k + 1), w n)
    (N : ℕ) :
    ε / 4 * Real.log (N + 1) ≤
      (∑ n ∈ range (N + 1), (Real.sqrt (n + 1))⁻¹ * w n) + D := by
  let f (k : ℕ) := (Real.sqrt ((k : ℝ) + 1))⁻¹
  let B (k : ℕ) := ∑ n ∈ range (k + 1), w n
  have hf (k : ℕ) : 0 ≤ f k := by dsimp [f]; positivity
  have hd (k : ℕ) : 0 ≤ f k - f (k + 1) := by
    apply sub_nonneg.mpr
    dsimp [f]
    simpa only [one_div] using one_div_le_one_div_of_le
      (Real.sqrt_pos.mpr (show 0 < (k : ℝ) + 1 by positivity))
      (Real.sqrt_le_sqrt (by push_cast; linarith))
  have hstep (k : ℕ) :
      ε / 4 * (Real.log ((k + 1 : ℕ) + 1) - Real.log (k + 1)) ≤
        (f k - f (k + 1)) * B k + D * (f k - f (k + 1)) := by
    have hs := mul_le_mul_of_nonneg_left
      (log_step_le_sqrt_step (show 1 ≤ (k : ℝ) + 1 by
        have hk : 0 ≤ (k : ℝ) := by positivity
        linarith)) hε
    have ht := mul_le_mul_of_nonneg_left (hfloor k) (hd k)
    dsimp [f, B] at *
    push_cast at *
    nlinarith
  have hsum := Finset.sum_le_sum (s := range N) fun k _ => hstep k
  have hlog : (∑ k ∈ range N,
      (Real.log ((k + 1 : ℕ) + 1) - Real.log (k + 1))) = Real.log (N + 1) := by
    simpa using Finset.sum_range_sub (fun k : ℕ => Real.log ((k : ℝ) + 1)) N
  have htel : (∑ k ∈ range N, (f k - f (k + 1))) = 1 - f N := by
    simpa [f] using Finset.sum_range_sub' f N
  rw [← Finset.mul_sum, hlog, Finset.sum_add_distrib, ← Finset.mul_sum, htel] at hsum
  have hparts := Finset.sum_range_by_parts f w (N + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at hparts
  change (∑ n ∈ range (N + 1), f n * w n) =
    f N * B N - ∑ k ∈ range N, (f (k + 1) - f k) * B k at hparts
  have hneg : (∑ k ∈ range N, (f (k + 1) - f k) * B k) =
      -(∑ k ∈ range N, (f k - f (k + 1)) * B k) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hneg] at hparts
  have hBN : 0 ≤ B N := Finset.sum_nonneg fun n _ => hw n
  have he := mul_nonneg (hf N) hBN
  have hDf := mul_nonneg hD (hf N)
  change ε / 4 * Real.log (N + 1) ≤ (∑ n ∈ range (N + 1), f n * w n) + D
  linarith

/-- Sublogarithmic harmonic mass forces arbitrarily late small square-root
mass scales. The envelope formulation includes every finite initial segment. -/
theorem exists_small_sqrt_mass_of_sublog_envelope {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
      (∑ n ∈ range (N + 1), (Real.sqrt (n + 1))⁻¹ * w n) ≤
        A + η * Real.log (N + 1))
    {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ N : ℕ, K ≤ N ∧ (∑ n ∈ range (N + 1), w n) < ε * Real.sqrt (N + 1) := by
  by_contra h
  push Not at h
  let D := ε * Real.sqrt ((K : ℝ) + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hfloor (k : ℕ) :
      ε * Real.sqrt (k + 1) - D ≤ ∑ n ∈ range (k + 1), w n := by
    by_cases hk : K ≤ k
    · exact (sub_le_self _ hD).trans (h k hk)
    · have hkk : (k : ℝ) ≤ K := by exact_mod_cast (Nat.lt_of_not_ge hk).le
      have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith :
        (k : ℝ) + 1 ≤ (K : ℝ) + 1)) hε.le
      exact (sub_nonpos.mpr hs).trans (Finset.sum_nonneg fun n _ => hw n)
  obtain ⟨A, hA, hbound⟩ := hsmall (ε / 8) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (8 * (A + D + 1) / ε))
  have hexp : 0 < Real.exp (8 * (A + D + 1) / ε) := Real.exp_pos _
  have hlog := Real.log_le_log hexp (show
    Real.exp (8 * (A + D + 1) / ε) ≤ (N : ℝ) + 1 by linarith)
  rw [Real.log_exp] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hε.le
  have hcancel : ε * (8 * (A + D + 1) / ε) = 8 * (A + D + 1) := by field_simp
  rw [hcancel] at hm
  have hlo := sqrt_weighted_partial_sum_lower hw hε.le hD hfloor N
  have hhi := hbound N
  linarith

/-- The ordinary absolute harmonic envelope supplies the shifted envelope
needed by finite partial summation. -/
theorem exists_small_abs_sqrt_mass_of_harmonic_envelope (d : ℕ → ℝ)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
      (∑ n ∈ range (N + 1), |d n| / n) ≤ A + η * Real.log (N + 1))
    {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ N : ℕ, K ≤ N ∧
      (∑ n ∈ range (N + 1), |d n| / Real.sqrt n) < ε * Real.sqrt (N + 1) := by
  apply exists_small_sqrt_mass_of_sublog_envelope
    (fun n => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) ?_ hε K
  intro η hη
  obtain ⟨A, hA, hb⟩ := hsmall η hη
  refine ⟨A, hA, fun N => le_trans (Finset.sum_le_sum fun n _ => ?_) (hb N)⟩
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs := Real.sqrt_pos.mpr hn0
  have hi : (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ (Real.sqrt n)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hs
      (Real.sqrt_le_sqrt (by linarith : (n : ℝ) ≤ (n : ℝ) + 1))
  calc
    (Real.sqrt ((n : ℝ) + 1))⁻¹ * (|d n| / Real.sqrt n) ≤
        (Real.sqrt n)⁻¹ * (|d n| / Real.sqrt n) :=
      mul_le_mul_of_nonneg_right hi (by positivity)
    _ = |d n| / n := by
      field_simp [hn0.ne', hs.ne']
      rw [Real.sq_sqrt hn0.le]
      ring

/-- The full square-root mass is bounded by the harmonic mass at its cutoff. -/
theorem sum_abs_div_sqrt_le_sqrt_mul_harmonic (d : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range (N + 1), |d n| / Real.sqrt n) ≤
      Real.sqrt N * ∑ n ∈ range (N + 1), |d n| / n := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hs := Real.sqrt_pos.mpr hnpos
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  calc
    |d n| / Real.sqrt n = Real.sqrt n * (|d n| / n) := by
      field_simp [hnpos.ne', hs.ne']
      rw [Real.sq_sqrt hnpos.le]
    _ ≤ Real.sqrt N * (|d n| / n) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hnN) (by positivity)

/-- One arbitrarily late real scale controls the local mass for every finite
cutoff. This is the input required by Gaussian localization. -/
theorem exists_large_local_mass_scale_of_harmonic_envelope (d : ℕ → ℝ)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
      (∑ n ∈ range (N + 1), |d n| / n) ≤ A + η * Real.log (N + 1))
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (L₀ : ℝ) :
    ∃ L : ℝ, max 1 L₀ ≤ L ∧ ∀ F : Finset ℕ,
      (∑ n ∈ F, |d n| / Real.sqrt n * (if (n : ℝ) ≤ c * L then 1 else 0)) ≤
        ε * Real.sqrt L := by
  classical
  have hs : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨J, hJ, hmass⟩ := exists_small_abs_sqrt_mass_of_harmonic_envelope d hsmall
    (div_pos hε hs) (max 1 ⌈c * max 1 L₀⌉₊)
  have hJ1 : 1 ≤ J := (le_max_left _ _).trans hJ
  have hJ1r : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have hceil : c * max 1 L₀ ≤ (J : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hJ))
  let L := (J : ℝ) / c
  have hL : max 1 L₀ ≤ L := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hceil)
  have hL0 : 0 ≤ L := (show (0 : ℝ) ≤ 1 by norm_num).trans ((le_max_left _ _).trans hL)
  have hcL : c * L = J := by dsimp [L]; field_simp
  have hroot : Real.sqrt ((J : ℝ) + 1) ≤ Real.sqrt (2 * c) * Real.sqrt L := by
    have harg : (J : ℝ) + 1 ≤ (2 * c) * L := by rw [mul_assoc, hcL]; linarith
    have h := Real.sqrt_le_sqrt harg
    rwa [Real.sqrt_mul (by positivity : 0 ≤ 2 * c)] at h
  have hbound : (∑ n ∈ range (J + 1), |d n| / Real.sqrt n) ≤ ε * Real.sqrt L := by
    apply hmass.le.trans
    calc
      (ε / Real.sqrt (2 * c)) * Real.sqrt ((J : ℝ) + 1) ≤
          (ε / Real.sqrt (2 * c)) * (Real.sqrt (2 * c) * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = ε * Real.sqrt L := by field_simp
  refine ⟨L, hL, fun F => le_trans ?_ hbound⟩
  have he : (∑ n ∈ F, |d n| / Real.sqrt n * (if (n : ℝ) ≤ c * L then 1 else 0)) =
      ∑ n ∈ F.filter (fun n : ℕ => (n : ℝ) ≤ c * L), |d n| / Real.sqrt n := by
    simp only [Finset.sum_filter, mul_ite, mul_one, mul_zero]
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hnc := (Finset.mem_filter.mp hn).2
    rw [hcL] at hnc
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.cast_le.mp hnc))
  · intro n _ _
    positivity

end RHTower.WeilSingularArithmetic
