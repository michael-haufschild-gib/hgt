import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheBoundStatesOfAWindowAreAtMostTheSinksOfAPositiveTrialVector
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheGroundVectorOfTheBlockMatrixOfANarrowWindowHasOneSignAndIsCharged
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# On a narrow window the potential is shallow and the count of bound states is one

Let `Δ(n) = (n + 1) log(n + 1) − n log n` (`xLogXStep`). On a window `(R, R + J]` with `J ≤ R`
no block is the image of another under a floor map, the jets telescope, and the potential of
the block `R + j` has the closed form

  `V_j = Δ(R + j) − γ − log 2π − ½ (Δ(2R + j + J) − Δ(2R + j)) − ½ (Δ(j) + Δ(J − 1 − j))`

(`blockPotential_eq_of_window`): the density, the jets to the sums, and the jets to the
differences on the two sides of the block.

* Every pair of blocks of the window is coupled by at least `1/(2J)`
  (`inv_two_mul_le_blockWeight`): the jet at a distance `n` is at least `1/(n + 1)`.
* With `log(n + 1) + 1 − 1/(n + 1) ≤ Δ(n) ≤ log(n + 1) + 1`, the potential is at least
  `log((R + 1)/J) − γ − log 2π − …`. If `16 J ≤ R` it is at least `−½`
  (`blockPotential_add_half_nonneg_of_narrow`).

So for `16 J ≤ R` the count of the bound states from the potential and the couplings is one
(`hermNegIndex_neutralWindow_le_one_of_narrow_count`): the constant trial vector, shifted by the
constant charge, has no sink. The sign is known on wider windows from the positivity of Weil's
form on a short aperture; here it follows from the graph of the window alone.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The first difference of `n log n` -/

/-- `Δ(n) = (n + 1) log(n + 1) − n log n`. -/
def xLogXStep (n : ℕ) : ℝ := xLogX (n + 1) - xLogX n

theorem xLogXStep_zero : xLogXStep 0 = 0 := by
  simp [xLogXStep, xLogX]

/-- The jet at `n` is the difference of two steps. -/
theorem xLogXDiff_eq_step {n : ℕ} (hn : 1 ≤ n) :
    xLogXDiff n = xLogXStep n - xLogXStep (n - 1) := by
  rw [xLogXDiff, xLogXStep, xLogXStep, Nat.sub_add_cancel hn]
  ring

/-- The jets at the distances `0, …, k` add up to `Δ(k)`. -/
theorem sum_range_succ_xLogXDiff (k : ℕ) : ∑ d ∈ range (k + 1), xLogXDiff d = xLogXStep k := by
  induction k with
  | zero => rw [Finset.sum_range_one, xLogXDiff_zero, xLogXStep_zero]
  | succ k ih =>
    have hD : xLogXDiff (k + 1) = xLogXStep (k + 1) - xLogXStep k := by
      have h := xLogXDiff_eq_step (n := k + 1) (by omega)
      rwa [Nat.add_sub_cancel] at h
    rw [Finset.sum_range_succ, ih, hD]
    ring

/-- The jets at `m + 1, …, m + K` add up to `Δ(m + K) − Δ(m)`. -/
theorem sum_range_xLogXDiff_add (m K : ℕ) :
    ∑ i ∈ range K, xLogXDiff (m + i + 1) = xLogXStep (m + K) - xLogXStep m := by
  induction K with
  | zero => rw [Finset.sum_range_zero, add_zero, sub_self]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, xLogXDiff_eq_step (by omega), Nat.add_sub_cancel, ← add_assoc]
    ring

/-- `Δ(n) = log(n + 1) + n log(1 + 1/n)`. -/
theorem xLogXStep_eq (n : ℕ) :
    xLogXStep n = Real.log ((n : ℝ) + 1) + n * blockDegree n := by
  rw [xLogXStep, xLogX, xLogX, blockDegree]
  push_cast
  ring

theorem xLogXStep_le (n : ℕ) : xLogXStep n ≤ Real.log ((n : ℝ) + 1) + 1 := by
  rw [xLogXStep_eq]
  have h : (n : ℝ) * blockDegree n ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      calc (n : ℝ) * blockDegree n ≤ n * (1 / n) :=
            mul_le_mul_of_nonneg_left (blockDegree_le_inv hn) hn0.le
        _ = 1 := by field_simp
  linarith

theorem le_xLogXStep {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) + 1 - 1 / ((n : ℝ) + 1) ≤ xLogXStep n := by
  rw [xLogXStep_eq]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_left (inv_succ_le_blockDegree hn) hn0.le
  have e : (n : ℝ) * (1 / ((n : ℝ) + 1)) = 1 - 1 / ((n : ℝ) + 1) := by
    field_simp
    ring
  linarith

/-! ### The potential of a window without contacts -/

/-- A block below twice another is not its image under a floor map. -/
theorem floorContact_eq_zero_of_lt_two_mul {Q a b : ℕ} (hb : b < 2 * a) :
    floorContact Q a b = 0 := by
  refine Finset.sum_eq_zero fun k hk => if_neg ?_
  have h1 : b / k ≤ b / 2 := Nat.div_le_div_left (Finset.mem_Icc.mp hk).1 (by norm_num)
  omega

/-- The neutral part between two blocks without contact: the density on the diagonal, minus
the jets to the sum and to the difference. -/
theorem neutralBlock_eq_of_lt_two_mul {Q a b : ℕ} (hab : max a b < 2 * min a b) :
    neutralBlock Q a b = (if a = b then blockDensity a else 0) -
      (xLogXDiff (a + b + 1) + xLogXDiff (max a b - min a b)) / 2 := by
  rw [neutralBlock, blockMatrix, blockJet, floorContact_eq_zero_of_lt_two_mul hab, min_add_max]
  ring

/-- **The potential of a block of a window `(R, R + J]` with `J ≤ R`, in closed form.** -/
theorem blockPotential_eq_of_window {Q R J j : ℕ} (hJ : J ≤ R) (hj : j < J) :
    blockPotential Q R J j = blockDensity (R + j) -
      (xLogXStep (R + j + R + J) - xLogXStep (R + j + R)) / 2 -
        (xLogXStep j + xLogXStep (J - 1 - j)) / 2 := by
  have hterm : ∀ l ∈ range J, neutralBlock Q (R + j) (R + l) =
      (if j = l then blockDensity (R + j) else 0) - xLogXDiff (R + j + R + l + 1) / 2 -
        xLogXDiff (max j l - min j l) / 2 := by
    intro l hl
    have hl' := Finset.mem_range.mp hl
    have e2 : max (R + j) (R + l) - min (R + j) (R + l) = max j l - min j l := by omega
    have e3 : R + j + (R + l) + 1 = R + j + R + l + 1 := by omega
    rw [neutralBlock_eq_of_lt_two_mul (by omega), e2, e3]
    by_cases h : j = l
    · rw [if_pos h, if_pos (by rw [h])]
      ring
    · rw [if_neg h, if_neg (by omega)]
      ring
  -- the jets to the sums telescope
  have h1 : ∑ l ∈ range J, xLogXDiff (R + j + R + l + 1) =
      xLogXStep (R + j + R + J) - xLogXStep (R + j + R) := sum_range_xLogXDiff_add (R + j + R) J
  -- the jets to the differences, on the two sides of the block
  have h2 : ∑ l ∈ range J, xLogXDiff (max j l - min j l) =
      xLogXStep j + xLogXStep (J - 1 - j) := by
    obtain ⟨K, rfl⟩ : ∃ K, J = j + 1 + K := ⟨J - 1 - j, by omega⟩
    have ha : ∑ l ∈ range (j + 1), xLogXDiff (max j l - min j l) = xLogXStep j := by
      rw [← sum_range_succ_xLogXDiff j, ← Finset.sum_range_reflect (fun d => xLogXDiff d) (j + 1)]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' := Finset.mem_range.mp hl
      show xLogXDiff (max j l - min j l) = xLogXDiff (j + 1 - 1 - l)
      congr 1
      omega
    have hb : ∑ i ∈ range K, xLogXDiff (max j (j + 1 + i) - min j (j + 1 + i)) =
        xLogXStep K := by
      rw [← sum_range_succ_xLogXDiff K, Finset.sum_range_succ', xLogXDiff_zero, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      omega
    rw [Finset.sum_range_add, ha, hb]
    congr 2
    omega
  rw [blockPotential, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hj), ← Finset.sum_div, ← Finset.sum_div, h1,
    h2]

/-- **Every pair of blocks of a window `(R, R + J]` with `J ≤ R` is coupled by at least
`1/(2J)`.** -/
theorem inv_two_mul_le_blockWeight {Q R J : ℕ} (hJ : J ≤ R) {j l : ℕ} (hj : j < J)
    (hl : l < J) (hjl : j ≠ l) : 1 / (2 * (J : ℝ)) ≤ blockWeight Q (R + j) (R + l) := by
  have h1 : 0 < xLogXDiff (R + j + (R + l) + 1) := xLogXDiff_pos (by omega)
  obtain ⟨n, hn, hn1, hnJ⟩ : ∃ n, n = max (R + j) (R + l) - min (R + j) (R + l) ∧ 1 ≤ n ∧
      n + 1 ≤ J := ⟨_, rfl, by omega, by omega⟩
  have h2 : 1 / ((n : ℝ) + 1) ≤ xLogXDiff n :=
    (inv_succ_le_blockDegree hn1).trans (blockDegree_le_xLogXDiff hn1)
  have h3 : 1 / (J : ℝ) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hnJ)
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have e : 1 / (2 * (J : ℝ)) = 1 / (J : ℝ) / 2 := by field_simp
  rw [blockWeight, neutralBlock_eq_of_lt_two_mul (by omega), if_neg (by omega), ← hn, e]
  linarith

/-! ### The potential of a narrow window -/

/-- `log 2π < 2`. -/
theorem log_two_pi_lt_two : Real.log (2 * Real.pi) < 2 := by
  have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : (2.7 : ℝ) * 2.7 < Real.exp 1 * Real.exp 1 :=
    mul_lt_mul'' h1 h1 (by norm_num) (by norm_num)
  rw [Real.log_lt_iff_lt_exp (by positivity), he]
  linarith [Real.pi_lt_d2]

/-- The bound behind the potential of a narrow window, in the steps of `n log n`. -/
theorem potential_step_bound {J j a m : ℕ} (hJ : 1 ≤ J) (hj : j < J) (ha : 16 * J ≤ a)
    (hm : 32 * J ≤ m) :
    0 ≤ xLogXStep a - (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) -
      (xLogXStep (m + J) - xLogXStep m) / 2 - (xLogXStep j + xLogXStep (J - 1 - j)) / 2 +
        1 / 2 := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hb1 := le_xLogXStep (show 1 ≤ a by omega)
  have hb2 := xLogXStep_le (m + J)
  have hb3 := le_xLogXStep (show 1 ≤ m by omega)
  have hb4 := xLogXStep_le j
  have hb5 := xLogXStep_le (J - 1 - j)
  -- `a + 1 ≥ 16 J`, so `log(a + 1) ≥ 4 log 2 + log J`
  have haR : (16 : ℝ) * J ≤ (a : ℝ) := by
    have h : ((16 * J : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    push_cast at h
    exact h
  have haJ : (16 : ℝ) * J ≤ (a : ℝ) + 1 := by linarith
  have hlogA : Real.log 16 + Real.log J ≤ Real.log ((a : ℝ) + 1) := by
    rw [← Real.log_mul (by norm_num) hJr.ne']
    exact Real.log_le_log (by positivity) haJ
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  -- the two sides of the block are at most `J` long
  have hlj : Real.log ((j : ℝ) + 1) ≤ Real.log J :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : j + 1 ≤ J))
  have hlJj : Real.log (((J - 1 - j : ℕ) : ℝ) + 1) ≤ Real.log J :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : J - 1 - j + 1 ≤ J))
  -- the jets to the sums are small: `m + 1 ≥ 32 J`
  have hmR : (32 : ℝ) * J ≤ (m : ℝ) := by
    have h : ((32 * J : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    push_cast at h
    exact h
  have hmJ : (32 : ℝ) * J ≤ (m : ℝ) + 1 := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlogM : Real.log (((m + J : ℕ) : ℝ) + 1) - Real.log ((m : ℝ) + 1) ≤ 1 / 32 := by
    have hpos : (0 : ℝ) < ((m + J : ℕ) : ℝ) + 1 := by positivity
    rw [← Real.log_div hpos.ne' hmpos.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hpos hmpos)
    have h2 : (((m + J : ℕ) : ℝ) + 1) / ((m : ℝ) + 1) - 1 ≤ 1 / 32 := by
      rw [div_sub_one hmpos.ne', div_le_div_iff₀ hmpos (by norm_num)]
      push_cast
      linarith
    linarith
  have h1a : 1 / ((a : ℝ) + 1) ≤ 1 / 17 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h1m : 1 / ((m : ℝ) + 1) ≤ 1 / 33 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hπ := log_two_pi_lt_two
  have hlog2 := Real.log_two_gt_d9
  linarith

/-- **On a window with `16 J ≤ R` the potential is at least `−½` at every block.** -/
theorem blockPotential_add_half_nonneg_of_narrow {Q R J j : ℕ} (hJ : 16 * J ≤ R) (hj : j < J) :
    0 ≤ blockPotential Q R J j + 1 / 2 := by
  have hρ : blockDensity (R + j) =
      xLogXStep (R + j) - (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) := rfl
  rw [blockPotential_eq_of_window (by omega) hj, hρ]
  exact potential_step_bound (by omega) hj (by omega) (by omega)

/-- **The count of the bound states of a narrow window is one.** If `16 J ≤ R`, the neutral
part of the window `(R, R + J]` has at most one negative square, by the count from the potential
and the couplings: the potential is at least `−½` and the couplings are at least `1/(2J)`. -/
theorem hermNegIndex_neutralWindow_le_one_of_narrow_count {Q R J : ℕ} (hJ : 16 * J ≤ R) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos J with rfl | hJpos
  · exact hermNegIndex_neutralWindow_le_one_of_shallow Q R 0 0 (fun j => j.elim0)
      fun j => j.elim0
  · have hJr : (0 : ℝ) < J := by exact_mod_cast hJpos
    refine hermNegIndex_neutralWindow_le_one_of_shallow Q R J (1 / (2 * (J : ℝ)))
      (fun j l hjl => inv_two_mul_le_blockWeight (by omega) j.2 l.2
        fun h => hjl (Fin.ext h)) fun j => ?_
    have e : 1 / (2 * (J : ℝ)) * J = 1 / 2 := by field_simp
    rw [e]
    exact blockPotential_add_half_nonneg_of_narrow hJ j.2

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
