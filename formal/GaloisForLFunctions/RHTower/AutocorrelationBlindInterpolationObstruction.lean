import GaloisForLFunctions.RHTower.EvenSectorLevyKreinRigidity
import GaloisForLFunctions.RHTower.CCM.CCMRectangularAutocorrelation

/-!
# No positive universal interior deficit from one blind shift

A train of `N+1` disjoint equal rectangular pulses, spaced by `4 log 2 / 5`,
is blind at `log 2`. Translation by one pulse spacing loses exactly one pulse:
`k(0) = (N+1) d`, `k(4 log 2 / 5) = N d`, where `d = log 2 / 10`.
Thus even among real compactly supported L² sources the normalized deficit at
this fixed interior point has infimum zero. The dyadic and complementary-shift
bounds in `EvenSectorLevyKreinRigidity` remain valid.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower.AutocorrelationKrein

open ArchimedeanAnomaly

def pulseSpacing : ℝ := 4 * Real.log 2 / 5
def pulseWidth : ℝ := Real.log 2 / 10

theorem pulseWidth_pos : 0 < pulseWidth := by
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem pulseSpacing_interior : pulseSpacing ∈ Ioo (0 : ℝ) (Real.log 2) := by
  have h := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  dsimp [pulseSpacing]
  constructor <;> linarith

def pulse (i : ℕ) : ℝ → ℝ := rectangularIntervalIndicator (i * pulseSpacing) pulseWidth

def pulseTrain (N : ℕ) (u : ℝ) : ℝ := ∑ i ∈ Finset.range (N + 1), pulse i u

theorem memLp_pulse (i : ℕ) : MemLp (pulse i) 2 volume :=
  memLp_indicator_const 2 measurableSet_Ioc 1 (Or.inr (ne_of_lt measure_Ioc_lt_top))

theorem memLp_pulseTrain (N : ℕ) : MemLp (pulseTrain N) 2 volume := by
  unfold pulseTrain
  exact memLp_finsetSum _ (fun i _ => memLp_pulse i)

theorem pulse_overlap (i j : ℕ) (x : ℝ) :
    (∫ u, pulse i (u + x) * pulse j u) =
      max 0 (pulseWidth - |x - (i * pulseSpacing - j * pulseSpacing)|) :=
  rectangularIntervalCrossCorrelation_eq_tent _ _ _ _

theorem pulse_overlap_zero (i j : ℕ) :
    (∫ u, pulse i u * pulse j u) = if i = j then pulseWidth else 0 := by
  have h := pulse_overlap i j 0
  simp only [add_zero] at h
  rw [h]
  have hd := pulseWidth_pos
  have hs : pulseWidth ≤ pulseSpacing := by
    dsimp [pulseWidth, pulseSpacing] at *
    linarith
  split_ifs with hij
  · subst j
    simp only [sub_self, abs_zero, sub_zero, max_eq_right hd.le]
  · apply max_eq_left
    rcases lt_or_gt_of_ne hij with hij | hij
    · have hn : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_iff.mpr hij)
      have hgap : pulseSpacing ≤ j * pulseSpacing - i * pulseSpacing := by
        nlinarith [pulseSpacing_interior.1]
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hn : (j : ℝ) + 1 ≤ i := by exact_mod_cast (Nat.succ_le_iff.mpr hij)
      have hgap : pulseSpacing ≤ i * pulseSpacing - j * pulseSpacing := by
        nlinarith [pulseSpacing_interior.1]
      rw [abs_of_nonpos (by linarith)]
      linarith

theorem pulse_overlap_spacing (i j : ℕ) :
    (∫ u, pulse i (u + pulseSpacing) * pulse j u) =
      if i = j + 1 then pulseWidth else 0 := by
  rw [pulse_overlap]
  have hd := pulseWidth_pos
  have hs : pulseWidth ≤ pulseSpacing := by
    dsimp [pulseWidth, pulseSpacing] at *
    linarith
  split_ifs with hij
  · subst i
    rw [Nat.cast_add, Nat.cast_one]
    ring_nf
    simp [max_eq_right hd.le]
  · apply max_eq_left
    rcases lt_or_gt_of_ne hij with hij | hij
    · have hn : (i : ℝ) ≤ j := by exact_mod_cast (show i ≤ j by omega)
      have hgap : pulseSpacing ≤ pulseSpacing - (i * pulseSpacing - j * pulseSpacing) := by
        nlinarith [pulseSpacing_interior.1]
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hn : (j : ℝ) + 2 ≤ i := by exact_mod_cast (show j + 2 ≤ i by omega)
      have hgap : pulseSpacing ≤ i * pulseSpacing - j * pulseSpacing - pulseSpacing := by
        nlinarith [pulseSpacing_interior.1]
      rw [abs_of_nonpos (by linarith)]
      linarith

theorem pulse_overlap_blind (i j : ℕ) :
    (∫ u, pulse i (u + Real.log 2) * pulse j u) = 0 := by
  rw [pulse_overlap]
  apply max_eq_left
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hij : i ≤ j + 1
  · have hn : (i : ℝ) ≤ j + 1 := by exact_mod_cast hij
    have hgap : pulseWidth ≤ Real.log 2 - (i * pulseSpacing - j * pulseSpacing) := by
      have h := mul_le_mul_of_nonneg_right hn pulseSpacing_interior.1.le
      dsimp [pulseWidth, pulseSpacing] at *
      nlinarith
    rw [abs_of_nonneg (pulseWidth_pos.le.trans hgap)]
    linarith
  · have hn : (j : ℝ) + 2 ≤ i := by exact_mod_cast (show j + 2 ≤ i by omega)
    have hgap : pulseWidth ≤ (i * pulseSpacing - j * pulseSpacing) - Real.log 2 := by
      have h := mul_le_mul_of_nonneg_right hn pulseSpacing_interior.1.le
      dsimp [pulseWidth, pulseSpacing] at *
      nlinarith
    rw [abs_of_nonpos (by linarith [pulseWidth_pos])]
    linarith

theorem pulseTrain_autocorr (N : ℕ) (x : ℝ) :
    autocorr (pulseTrain N) x =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ∫ u, pulse i (u + x) * pulse j u := by
  have hi (i j : ℕ) : Integrable (fun u => pulse i (u + x) * pulse j u) :=
    integrable_rectangularIntervalCrossCorrelation _ _ _ _
  unfold autocorr pulseTrain
  have he : (fun u => (∑ i ∈ Finset.range (N + 1), pulse i u) *
      (∑ i ∈ Finset.range (N + 1), pulse i (u + x))) =
      fun u => ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        pulse i (u + x) * pulse j u := by
    funext u
    rw [mul_comm]
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum _ (fun j _ => hi i j)

theorem pulseTrain_autocorr_zero (N : ℕ) :
    autocorr (pulseTrain N) 0 = (N + 1) * pulseWidth := by
  rw [pulseTrain_autocorr]
  simp only [add_zero, pulse_overlap_zero, Finset.sum_ite_eq, Finset.mem_range]
  rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))]
  simp

theorem pulseTrain_autocorr_spacing (N : ℕ) :
    autocorr (pulseTrain N) pulseSpacing = N * pulseWidth := by
  rw [pulseTrain_autocorr, Finset.sum_comm]
  simp_rw [pulse_overlap_spacing]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.add_lt_add_iff_right]
  rw [Finset.sum_range_succ]
  simp only [lt_self_iff_false, ↓reduceIte, add_zero]
  rw [Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj))]
  simp

theorem pulseTrain_autocorr_blind (N : ℕ) :
    autocorr (pulseTrain N) (Real.log 2) = 0 := by
  simp [pulseTrain_autocorr, pulse_overlap_blind]

/-- No positive lower bound at the fixed interior shift can follow from L²
autocorrelation and prime-2 blindness alone. -/
theorem exists_blind_small_interior_deficit (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, MemLp f 2 volume ∧ 0 < autocorr f 0 ∧
      autocorr f (Real.log 2) = 0 ∧
      autocorr f 0 - autocorr f pulseSpacing < ε * autocorr f 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨pulseTrain N, memLp_pulseTrain N, ?_, pulseTrain_autocorr_blind N, ?_⟩
  · rw [pulseTrain_autocorr_zero]
    exact mul_pos (by positivity) pulseWidth_pos
  · rw [pulseTrain_autocorr_zero, pulseTrain_autocorr_spacing]
    have hN' : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
    have h := mul_lt_mul_of_pos_right (show 1 < ε * (N + 1) by nlinarith) pulseWidth_pos
    nlinarith

end RHTower.AutocorrelationKrein
