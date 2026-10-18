import GaloisForLFunctions.BiScaleUncertainty.EndpointCycleDeterminant
import GaloisForLFunctions.BiScaleUncertainty.SharpCycleDetectionOrder
import GaloisForLFunctions.BiScaleUncertainty.SeparatedCopyCyclePolarAmbiguity

/-!
# A first-order detecting Gram configuration

Equally spaced samples of the literal separated source form a chordless
cycle at the first detecting order. Its closing edge carries the copy sign,
and the exact determinant difference has no cancellation.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.SharpCycle
open SeparatedCycle (gramDet)
set_option autoImplicit false

/-- Number of vertices beyond the initial triangle. -/
def cycleExcess (T : Ioi (2 : ℝ)) : ℕ := ⌊(T : ℝ)⌋₊ - 2

theorem cycleExcess_size (T : Ioi (2 : ℝ)) : cycleExcess T + 3 = firstOrder T := by
  have hT : (2 : ℝ) < T := T.property
  have hT0 : 0 ≤ (T : ℝ) := by linarith only [hT]
  have hf : 2 ≤ ⌊(T : ℝ)⌋₊ := by
    by_contra h
    have hx : (T : ℝ) < 2 := (Nat.floor_lt hT0).mp (show ⌊(T : ℝ)⌋₊ < 2 by omega)
    linarith only [hT, hx]
  simp only [cycleExcess, firstOrder]
  omega

def cycleStep (T : Ioi (2 : ℝ)) : ℝ := (T : ℝ) / (cycleExcess T + 3 : ℕ)

theorem cycleStep_bounds (T : Ioi (2 : ℝ)) :
    0 < cycleStep T ∧ cycleStep T < 1 ∧ 1 < 2 * cycleStep T := by
  have hT : (2 : ℝ) < T := T.property
  have hT0 : 0 ≤ (T : ℝ) := by linarith only [hT]
  have hq : (0 : ℝ) < (cycleExcess T + 3 : ℕ) := by positivity
  have hqeq : ((cycleExcess T + 3 : ℕ) : ℝ) = (⌊(T : ℝ)⌋₊ : ℝ) + 1 := by
    rw [cycleExcess_size]
    simp only [firstOrder, Nat.cast_add, Nat.cast_one]
  have hlt : (T : ℝ) < (cycleExcess T + 3 : ℕ) := by
    rw [hqeq]
    exact Nat.lt_floor_add_one (T : ℝ)
  have hle : ((cycleExcess T + 3 : ℕ) : ℝ) ≤ (T : ℝ) + 1 := by
    rw [hqeq]
    linarith only [Nat.floor_le hT0]
  have htwo : 1 < 2 * ((T : ℝ) / (cycleExcess T + 3 : ℕ)) := by
    rw [show 2 * ((T : ℝ) / (cycleExcess T + 3 : ℕ)) =
      (2 * (T : ℝ)) / (cycleExcess T + 3 : ℕ) by ring]
    apply (lt_div_iff₀ hq).mpr
    linarith only [hle, hT]
  exact ⟨div_pos (by linarith only [hT]) hq,
    (div_lt_iff₀ hq).mpr (by simpa only [one_mul] using hlt), htwo⟩

theorem gap_eq_cycleStep (T : Ioi (2 : ℝ)) :
    (T : ℝ) = ((cycleExcess T : ℝ) + 3) * cycleStep T := by
  have hn : (cycleExcess T : ℝ) + 3 ≠ 0 := by positivity
  simp only [cycleStep, Nat.cast_add, Nat.cast_ofNat]
  field_simp [hn]

def cycleSamples (T : Ioi (2 : ℝ)) (i : Fin (cycleExcess T + 3)) : ℝ :=
  (i.val : ℝ) * cycleStep T

private theorem lattice_correlation (T : Ioi (2 : ℝ)) (a : ℝ)
    (m : Fin (cycleExcess T + 3)) :
    autocorr (source T a) ((m.val : ℝ) * cycleStep T) =
      if m.val = 0 then (1 + a ^ 2) * autocorr seed 0
      else if m.val = 1 then (1 + a ^ 2) * autocorr seed (cycleStep T)
      else if m.val = cycleExcess T + 2 then -a * autocorr seed (cycleStep T)
      else 0 := by
  obtain ⟨hs0, hs1, hs2⟩ := cycleStep_bounds T
  have hT : (2 : ℝ) < T := T.property
  by_cases h0 : m.val = 0
  · simpa only [h0, if_true, Nat.cast_zero, zero_mul] using source_mass T a
  by_cases h1 : m.val = 1
  · rw [if_neg h0, if_pos h1, h1, Nat.cast_one, one_mul]
    exact source_central T a ⟨cycleStep T, by constructor <;> linarith only [hs0, hs1]⟩
  by_cases hlast : m.val = cycleExcess T + 2
  · rw [if_neg h0, if_neg h1, if_pos hlast, hlast]
    have hlag : ((cycleExcess T + 2 : ℕ) : ℝ) * cycleStep T =
        (T : ℝ) + -cycleStep T := by
      have hg := gap_eq_cycleStep T
      simp only [Nat.cast_add, Nat.cast_ofNat]
      nlinarith only [hg]
    rw [hlag]
    simpa only [autocorr_neg] using source_right T a
      ⟨-cycleStep T, by constructor <;> linarith only [hs0, hs1]⟩
  rw [if_neg h0, if_neg h1, if_neg hlast]
  have hm := m.isLt
  have hlo : (2 : ℝ) ≤ m.val := by exact_mod_cast (show 2 ≤ m.val by omega)
  have hhi : (m.val : ℝ) ≤ (cycleExcess T : ℝ) + 1 := by
    exact_mod_cast (show m.val ≤ cycleExcess T + 1 by omega)
  have hlom := mul_le_mul_of_nonneg_right hlo hs0.le
  have hhim := mul_le_mul_of_nonneg_right hhi hs0.le
  have hg := gap_eq_cycleStep T
  have hx : 1 ≤ (m.val : ℝ) * cycleStep T := by linarith only [hlom, hs2]
  have hl : 1 ≤ -((m.val : ℝ) * cycleStep T - T) := by nlinarith only [hhim, hg, hs2]
  have hr : 1 ≤ (m.val : ℝ) * cycleStep T + T := by linarith only [hx, hT]
  rw [source_correlation,
    (seed_correlation_eq_zero_iff _).mpr (hx.trans (le_abs_self _)),
    (seed_correlation_eq_zero_iff _).mpr (hl.trans (neg_le_abs _)),
    (seed_correlation_eq_zero_iff _).mpr (hr.trans (le_abs_self _))]
  ring

/-- The actual sampled correlation matrix is a cycle with one sign-sensitive edge. -/
theorem gram_cycle_matrix (T : Ioi (2 : ℝ)) (a : ℝ) :
    (fun i j : Fin (cycleExcess T + 3) =>
      autocorr (source T a) (cycleSamples T i - cycleSamples T j)) =
      CycleMatrix.cycle (cycleExcess T) ((1 + a ^ 2) * autocorr seed 0)
        ((1 + a ^ 2) * autocorr seed (cycleStep T)) (-a * autocorr seed (cycleStep T)) := by
  have hp (i j : Fin (cycleExcess T + 3)) (hij : j.val ≤ i.val) :
      autocorr (source T a) (cycleSamples T i - cycleSamples T j) =
        CycleMatrix.cycle (cycleExcess T) ((1 + a ^ 2) * autocorr seed 0)
          ((1 + a ^ 2) * autocorr seed (cycleStep T)) (-a * autocorr seed (cycleStep T)) i j := by
    have hi := i.isLt
    have hj := j.isLt
    let m : Fin (cycleExcess T + 3) := ⟨i.val - j.val, by omega⟩
    have hlag : cycleSamples T i - cycleSamples T j = (m.val : ℝ) * cycleStep T := by
      dsimp only [cycleSamples, m]
      rw [Nat.cast_sub hij]
      ring
    rw [hlag, lattice_correlation]
    dsimp only [m]
    simp only [CycleMatrix.cycle, CycleMatrix.path]
    split_ifs <;> first | rfl | omega
  ext i j
  by_cases hij : j.val ≤ i.val
  · exact hp i j hij
  · calc
      _ = autocorr (source T a) (cycleSamples T j - cycleSamples T i) := by
        rw [show cycleSamples T i - cycleSamples T j =
          -(cycleSamples T j - cycleSamples T i) by ring, autocorr_neg]
      _ = _ := hp j i (by omega)
      _ = _ := (CycleMatrix.cycle_symm _ _ _ _).apply i j

/-- Exact determinant separation at the minimal closed-product order. -/
theorem gram_cycle_difference (T : Ioi (2 : ℝ)) (a : ℝ) :
    gramDet (source T (-a)) (cycleExcess T + 3) (cycleSamples T) -
      gramDet (source T a) (cycleExcess T + 3) (cycleSamples T) =
      4 * a * autocorr seed (cycleStep T) * (-1 : ℝ) ^ (cycleExcess T + 2) *
        ((1 + a ^ 2) * autocorr seed (cycleStep T)) ^ (cycleExcess T + 2) := by
  dsimp only [gramDet]
  rw [gram_cycle_matrix, gram_cycle_matrix]
  simp only [neg_sq, neg_neg]
  calc
    _ = -4 * (-a * autocorr seed (cycleStep T)) * (-1 : ℝ) ^ (cycleExcess T + 2) *
        ((1 + a ^ 2) * autocorr seed (cycleStep T)) ^ (cycleExcess T + 2) := by
      simpa only [neg_mul, neg_neg] using CycleMatrix.det_neg_sub_det (cycleExcess T)
        ((1 + a ^ 2) * autocorr seed 0) ((1 + a ^ 2) * autocorr seed (cycleStep T))
        (-a * autocorr seed (cycleStep T))
    _ = _ := by ring

theorem gram_cycle_distinct_iff (T : Ioi (2 : ℝ)) (a : ℝ) :
    gramDet (source T (-a)) (cycleExcess T + 3) (cycleSamples T) ≠
      gramDet (source T a) (cycleExcess T + 3) (cycleSamples T) ↔ a ≠ 0 := by
  constructor
  · intro h ha
    subst a
    exact h (by rw [neg_zero])
  · intro ha he
    have hH : 0 < autocorr seed (cycleStep T) :=
      (seed_correlation_pos_iff _).mpr
        (by rw [abs_of_pos (cycleStep_bounds T).1]; exact (cycleStep_bounds T).2.1)
    have hc : 0 < (1 + a ^ 2) * autocorr seed (cycleStep T) := mul_pos (by positivity) hH
    have hn : 4 * a * autocorr seed (cycleStep T) * (-1 : ℝ) ^ (cycleExcess T + 2) *
        ((1 + a ^ 2) * autocorr seed (cycleStep T)) ^ (cycleExcess T + 2) ≠ 0 :=
      mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hH.ne')
          (pow_ne_zero _ (by norm_num))) (pow_ne_zero _ hc.ne')
    have hz : gramDet (source T (-a)) (cycleExcess T + 3) (cycleSamples T) -
        gramDet (source T a) (cycleExcess T + 3) (cycleSamples T) = 0 := by rw [he, sub_self]
    rw [gram_cycle_difference] at hz
    exact hn hz

end GaloisForLFunctions.BiScaleUncertainty.SharpCycle
