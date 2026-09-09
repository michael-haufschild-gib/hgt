import GaloisForLFunctions.HTGeometry.FiniteKMSWightman
import GaloisForLFunctions.HTGeometry.SelectionSynthesisDivergence

/-!
# Record time for arbitrary finite Gibbs histories

The record-based parameter of arXiv:2605.03958, equation (52), is an
accumulation of directed relative entropy. Actual normalized Gibbs states
supply every positivity and normalization fact. A record clock is monotone
for every history, including histories whose thermodynamic parameter reverses.
-/
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Directed relative entropy between consecutive finite Gibbs states. -/
def gibbsRecordIncrement {n : ℕ} (oldEnergy newEnergy : Fin (n + 1) → ℝ) : ℝ :=
  relEntropy (_root_.HTGeometry.finiteGibbsStateWeight 1 newEnergy)
    (_root_.HTGeometry.finiteGibbsStateWeight 1 oldEnergy)

/-- Accumulated distinguishability along an arbitrary history of finite spectra. -/
def gibbsRecordClock {n : ℕ} (energy : ℕ → Fin (n + 1) → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, gibbsRecordIncrement (energy k) (energy (k + 1))

theorem gibbsRecordIncrement_nonneg {n : ℕ}
    (oldEnergy newEnergy : Fin (n + 1) → ℝ) : 0 ≤ gibbsRecordIncrement oldEnergy newEnergy := by
  apply relEntropy_nonneg
  · intro i
    exact (_root_.HTGeometry.finiteGibbsStateWeight_pos 1 newEnergy i).le
  · exact _root_.HTGeometry.finiteGibbsStateWeight_pos 1 oldEnergy
  · simpa only [_root_.HTGeometry.sum_finiteGibbsStateWeight_eq_one] using
      hasSum_fintype (_root_.HTGeometry.finiteGibbsStateWeight 1 newEnergy)
  · simpa only [_root_.HTGeometry.sum_finiteGibbsStateWeight_eq_one] using
      hasSum_fintype (_root_.HTGeometry.finiteGibbsStateWeight 1 oldEnergy)
  · exact (hasSum_fintype _).summable

theorem gibbsRecordIncrement_self {n : ℕ} (energy : Fin (n + 1) → ℝ) :
    gibbsRecordIncrement energy energy = 0 :=
  relEntropy_self_eq_zero (_root_.HTGeometry.finiteGibbsStateWeight_pos 1 energy)

theorem gibbsRecordClock_succ {n : ℕ} (energy : ℕ → Fin (n + 1) → ℝ) (N : ℕ) :
    gibbsRecordClock energy (N + 1) = gibbsRecordClock energy N +
      gibbsRecordIncrement (energy N) (energy (N + 1)) := by
  exact Finset.sum_range_succ _ _

theorem gibbsRecordClock_nonneg {n : ℕ} (energy : ℕ → Fin (n + 1) → ℝ) (N : ℕ) :
    0 ≤ gibbsRecordClock energy N := by
  exact Finset.sum_nonneg fun k _ => gibbsRecordIncrement_nonneg _ _

/-- The accumulated record parameter is monotone even for nonmonotone energy histories. -/
theorem gibbsRecordClock_monotone {n : ℕ} (energy : ℕ → Fin (n + 1) → ℝ) :
    Monotone (gibbsRecordClock energy) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [gibbsRecordClock_succ]
  exact le_add_of_nonneg_right (gibbsRecordIncrement_nonneg _ _)

/-- A step advances record time precisely when its directed information cost is positive. -/
theorem gibbsRecordClock_advances_iff {n : ℕ} (energy : ℕ → Fin (n + 1) → ℝ) (N : ℕ) :
    gibbsRecordClock energy N < gibbsRecordClock energy (N + 1) ↔
      0 < gibbsRecordIncrement (energy N) (energy (N + 1)) := by
  rw [gibbsRecordClock_succ, lt_add_iff_pos_right]

/-- Constant physical states leave the record clock stationary at every resolution. -/
theorem gibbsRecordClock_constant {n : ℕ} (energy : Fin (n + 1) → ℝ) (N : ℕ) :
    gibbsRecordClock (fun _ => energy) N = 0 := by
  simp [gibbsRecordClock, gibbsRecordIncrement_self]

/-- Vanishing accumulated records force every individual increment to vanish. -/
theorem gibbsRecordClock_zero_iff {n : ℕ} (energy : ℕ → Fin (n + 1) → ℝ) (N : ℕ) :
    gibbsRecordClock energy N = 0 ↔
      ∀ k < N, gibbsRecordIncrement (energy k) (energy (k + 1)) = 0 := by
  rw [gibbsRecordClock, Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => gibbsRecordIncrement_nonneg (energy k) (energy (k + 1)))]
  simp only [Finset.mem_range]

/-- Spectral energy-origin shifts are invisible to every Gibbs record. -/
theorem gibbsRecord_weight_shift {n : ℕ} (energy : Fin (n + 1) → ℝ) (c : ℝ) :
    _root_.HTGeometry.finiteGibbsStateWeight 1 (fun i => energy i + c) =
      _root_.HTGeometry.finiteGibbsStateWeight 1 energy := by
  funext i
  unfold _root_.HTGeometry.finiteGibbsStateWeight _root_.HTGeometry.finiteGibbsPartition
  simp only [neg_mul, one_mul, neg_add_rev, Real.exp_add]
  rw [← Finset.mul_sum]
  field_simp

/-- Arbitrary time-dependent energy-origin shifts cannot create accumulated records. -/
theorem gibbsRecordClock_shift {n : ℕ} (energy : ℕ → Fin (n + 1) → ℝ)
    (shift : ℕ → ℝ) (N : ℕ) :
    gibbsRecordClock (fun k i => energy k i + shift k) N = gibbsRecordClock energy N := by
  unfold gibbsRecordClock gibbsRecordIncrement
  simp only [gibbsRecord_weight_shift]

end GaloisForLFunctions.HTGeometry
