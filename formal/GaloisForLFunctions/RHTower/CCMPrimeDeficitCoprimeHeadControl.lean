import GaloisForLFunctions.RHTower.CCMPrimeDeficitCoprimeRows

/-!
# A decaying bound for complete rows of signed cross work

The first index ranges from two to the square-root cutoff; the second
index ranges through every coprime partner up to the full cutoff. Since
no such row has a coprime diagonal, this controls an actual block of
signed cross interactions. The endpoint row and larger first indices
remain outside this estimate.
-/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace RHTower

def ccmPrimeDeficitCoprimeHeadCross (T : ℝ) : ℝ :=
  Real.exp (-T) * ∑ a ∈ Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊,
    ccmPrimeDeficitMobiusCenteredWork (T - Real.log a) * ccmPrimeDeficitCoprimeRow a T

theorem abs_ccmPrimeDeficitMobiusCenteredWork_le_exp (T : ℝ) :
    |ccmPrimeDeficitMobiusCenteredWork T| ≤ (7 / 2) * Real.exp T := by
  unfold ccmPrimeDeficitMobiusCenteredWork
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊) :
      |moebiusCoeff n * ccmPrimeDeficitDilationRemainder (T - Real.log n)| ≤ 7 / 2 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnT : (n : ℝ) ≤ Real.exp T :=
      (Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hn).2
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (abs_moebiusCoeff_le_one n)
      (abs_ccmPrimeDeficitDilationRemainder_le_uniform
        (sub_nonneg.mpr ((Real.log_le_iff_le_exp hnpos).mpr hnT))) (abs_nonneg _) zero_le_one
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        |moebiusCoeff n * ccmPrimeDeficitDilationRemainder (T - Real.log n)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (7 / 2 : ℝ) := Finset.sum_le_sum hterm
    _ = (7 / 2) * (⌊Real.exp T⌋₊ : ℝ) := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.floor_le (Real.exp_pos T).le) (by positivity)

private theorem weighted_row_bound {T : ℝ} {a : ℕ}
    (hT : 0 ≤ T) (ha : a ∈ Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊) :
    |ccmPrimeDeficitMobiusCenteredWork (T - Real.log a) * ccmPrimeDeficitCoprimeRow a T| ≤
      (7 / 8) * (T + 14) * (1 + T / 2) := by
  have hapos : 0 < a := by have := (Finset.mem_Icc.mp ha).1; omega
  have haposR : (0 : ℝ) < a := by exact_mod_cast hapos
  have haT : (a : ℝ) ≤ Real.exp (T / 2) :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp ha).2
  have hlog : Real.log a ≤ T / 2 := (Real.log_le_iff_le_exp haposR).mpr haT
  have haFull : a ∈ Finset.Icc 1 ⌊Real.exp T⌋₊ := Finset.mem_Icc.mpr ⟨hapos,
    (Finset.mem_Icc.mp ha).2.trans
      (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith only [hT])))⟩
  have hq := abs_ccmPrimeDeficitMobiusCenteredWork_le_exp (T - Real.log a)
  rw [Real.exp_sub, Real.exp_log haposR] at hq
  have hr := abs_ccmPrimeDeficitCoprimeRow_le_logMass hT haFull
    (by have := (Finset.mem_Icc.mp ha).1; omega)
  have he : Real.exp T * Real.exp (-T) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [abs_mul]
  calc
    _ ≤ ((7 / 2) * (Real.exp T / a)) *
        (Real.exp (-T) * (T + 14) / 4 * ((a : ℝ) * (1 + Real.log a))) :=
      mul_le_mul hq hr (abs_nonneg _) (by positivity)
    _ = (7 / 8) * (T + 14) * (1 + Real.log a) := by
      calc
        _ = (Real.exp T * Real.exp (-T)) * ((7 / 8) * (T + 14) * (1 + Real.log a)) := by
          field_simp
          ring
        _ = _ := by rw [he, one_mul]
    _ ≤ _ := by gcongr

/-- The entire indicated block of signed cross interactions is negligible
at critical normalization, with no estimate on the unknown deficit as a premise. -/
theorem abs_ccmPrimeDeficitCoprimeHeadCross_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitCoprimeHeadCross T| ≤
      (7 / 8) * Real.exp (-(T / 2)) * (T + 14) * (1 + T / 2) := by
  let B : ℝ := (7 / 8) * (T + 14) * (1 + T / 2)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hcard : (((Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊).card : ℕ) : ℝ) ≤ Real.exp (T / 2) := by
    refine le_trans ?_ (Nat.floor_le (Real.exp_pos _).le)
    exact_mod_cast (show (Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊).card ≤ ⌊Real.exp (T / 2)⌋₊ by
      rw [Nat.card_Icc]; omega)
  have hs : |∑ a ∈ Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊,
      ccmPrimeDeficitMobiusCenteredWork (T - Real.log a) * ccmPrimeDeficitCoprimeRow a T| ≤
        Real.exp (T / 2) * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _a ∈ Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊, B :=
        Finset.sum_le_sum (fun a ha => weighted_row_bound hT ha)
      _ = ((Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hB
  have he : Real.exp (-T) * Real.exp (T / 2) = Real.exp (-(T / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [ccmPrimeDeficitCoprimeHeadCross, abs_mul, abs_of_pos (Real.exp_pos (-T))]
  calc
    _ ≤ Real.exp (-T) * (Real.exp (T / 2) * B) :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos (-T)).le
    _ = _ := by rw [← mul_assoc, he]; dsimp only [B]; ring

theorem tendsto_ccmPrimeDeficitCoprimeHeadCross :
    Tendsto ccmPrimeDeficitCoprimeHeadCross atTop (𝓝 0) := by
  have hh : Tendsto (fun T : ℝ => T / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have hp (n : ℕ) := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp hh
  have h := (((hp 2).const_mul (7 / 4)).add ((hp 1).const_mul 14)).add
    ((hp 0).const_mul (49 / 4))
  have hb : Tendsto
      (fun T : ℝ => (7 / 8) * Real.exp (-(T / 2)) * (T + 14) * (1 + T / 2))
      atTop (𝓝 0) := by
    convert h using 1 <;> (try simp only [Function.comp_apply, pow_zero, pow_one]) <;> ring
  apply squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  simpa only [Real.norm_eq_abs] using abs_ccmPrimeDeficitCoprimeHeadCross_le hT

end RHTower
