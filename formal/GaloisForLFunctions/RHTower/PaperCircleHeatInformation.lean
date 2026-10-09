import GaloisForLFunctions.RHTower.PaperCircleEnergyHeatKernel
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Compress.Low
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Compress.Observe

/-! # Entropy and exact observations of native circle-energy heat increments

The actual heat laws add by convolution. Their entropy grows subadditively, and the
source block-observation theorem identifies exactly how much one increment is hidden
by observing only an accumulated sum.
-/

open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Shannon entropy of the actual finite heat law. -/
def paperCircleHeatEntropy (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (t : ℝ≥0) : ℝ :=
  (paperCircleGridHeat a M t).entropy

/-- Independent native heat increments sum to the law at the sum of their times. -/
theorem paperCircleGridHeat_send_add (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (s t : ℝ≥0) :
    ((paperCircleGridHeat a M s).tensorP (paperCircleGridHeat a M t)).send
      (fun x => x.1 + x.2) = paperCircleGridHeat a M (s + t) := by
  apply Law.ext_of_Ex
  intro f
  rw [Law.Ex_send, Law.Ex_tensorP]
  unfold Law.Ex
  simp_rw [paperCircleGridHeat_convolution, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  symm
  apply Fintype.sum_equiv (Equiv.addLeft x)
  intro y
  change paperCircleGridHeat a M s x * (paperCircleGridHeat a M t y * f (x + y)) =
    (paperCircleGridHeat a M s x * paperCircleGridHeat a M t (x + y - x)) * f (x + y)
  rw [add_sub_cancel_left]
  ring

/-- Exact uncertainty about the first increment after observing the combined increment. -/
theorem paperCircleGridHeat_condEntropy_sum (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (s t : ℝ≥0) :
    ((paperCircleGridHeat a M s).tensorP (paperCircleGridHeat a M t)).Hcond
      Prod.fst (fun x => x.1 + x.2) =
        paperCircleHeatEntropy a M s + paperCircleHeatEntropy a M t -
          paperCircleHeatEntropy a M (s + t) := by
  let P := (paperCircleGridHeat a M s).tensorP (paperCircleGridHeat a M t)
  have H : P.H (fun x => (x.1, x.1 + x.2)) = P.entropy := by
    rw [← Law.H_self P]
    apply Law.H_partition
    rintro ⟨x,y⟩ ⟨z,w⟩
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl,h⟩
      exact ⟨rfl,add_left_cancel h⟩
    · rintro ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩
  change P.H _ - P.H _ = _
  rw [H]
  change ((paperCircleGridHeat a M s).tensorP (paperCircleGridHeat a M t)).entropy - _ = _
  rw [Law.entropy_tensorP]
  change _ - (((paperCircleGridHeat a M s).tensorP (paperCircleGridHeat a M t)).send
    (fun x => x.1 + x.2)).entropy = _
  rw [paperCircleGridHeat_send_add]
  rfl

theorem paperCircleHeatEntropy_zero (a : ι → CCMCircleBoundedSymbol) (M : ℕ) :
    paperCircleHeatEntropy a M 0 = 0 := by
  rw [paperCircleHeatEntropy, paperCircleGridHeat_zero, Law.entropy_point]

theorem paperCircleHeatEntropy_nonneg (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (t : ℝ≥0) :
    0 ≤ paperCircleHeatEntropy a M t := Law.entropy_nonneg _

theorem paperCircleHeatEntropy_le_log_card (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (t : ℝ≥0) :
    paperCircleHeatEntropy a M t ≤ Real.log (Fintype.card (Grid M)) := Law.entropy_le_log_card _

/-- Entropy at a combined time is at most the sum of the two entropies. -/
theorem paperCircleHeatEntropy_add_le (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (s t : ℝ≥0) :
    paperCircleHeatEntropy a M (s + t) ≤ paperCircleHeatEntropy a M s + paperCircleHeatEntropy a M t := by
  have H := Law.Hcond_nonneg ((paperCircleGridHeat a M s).tensorP (paperCircleGridHeat a M t))
    Prod.fst (fun x => x.1 + x.2)
  rw [paperCircleGridHeat_condEntropy_sum] at H
  linarith

private theorem entropy_le_add_right (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (s t : ℝ≥0) :
    paperCircleHeatEntropy a M t ≤ paperCircleHeatEntropy a M (s + t) := by
  have H := Law.Hcond_le_H ((paperCircleGridHeat a M s).tensorP (paperCircleGridHeat a M t))
    Prod.fst (fun x => x.1 + x.2)
  rw [paperCircleGridHeat_condEntropy_sum, Law.H, Law.send_fst_tensorP] at H
  change _ ≤ paperCircleHeatEntropy a M s at H
  linarith

/-- Additional independent heat cannot lower entropy. -/
theorem paperCircleHeatEntropy_le_add (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (s t : ℝ≥0) :
    paperCircleHeatEntropy a M s ≤ paperCircleHeatEntropy a M (s + t) := by
  simpa only [add_comm] using entropy_le_add_right a M t s

theorem monotone_paperCircleHeatEntropy (a : ι → CCMCircleBoundedSymbol) (M : ℕ) :
    Monotone (paperCircleHeatEntropy a M) := by
  intro s t h
  obtain ⟨r,rfl⟩ := exists_add_of_le h
  exact paperCircleHeatEntropy_le_add a M s r

/-- Every independent finite block is exactly the native heat law at its total time. -/
theorem paperCircleGridHeat_iid_sum (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (t : ℝ≥0) (n : ℕ) :
    (Compress.iid (paperCircleGridHeat a M t) n).send (Compress.tot id) =
      paperCircleGridHeat a M (n • t) := by
  induction n with
  | zero =>
    apply Law.ext_of_Ex
    intro f
    rw [Law.Ex_send, zero_nsmul, paperCircleGridHeat_zero, Law.Ex_point]
    simp [Compress.tot, Law.Ex_const]
  | succ n ih =>
    rw [Compress.iid_succ, Law.send_send]
    have H := Law.send_tensorP (paperCircleGridHeat a M t)
      (Compress.iid (paperCircleGridHeat a M t) n) (fun x => x) (Compress.tot id)
    rw [Law.send_id, ih] at H
    calc
      _ = ((paperCircleGridHeat a M t).tensorP (paperCircleGridHeat a M (n • t))).send
          (fun x => x.1 + x.2) := by
        rw [← H, Law.send_send]
        congr 1
        funext x
        unfold Compress.tot Compress.appendOne
        rw [Fin.sum_univ_succ]
        rfl
      _ = paperCircleGridHeat a M (t + n • t) := paperCircleGridHeat_send_add a M t (n • t)
      _ = _ := by rw [add_smul, one_smul, add_comm]

/-- The source contextual sum-entropy is the actual heat entropy. -/
theorem fundG_initial_paperCircleGridHeat (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (t : ℝ≥0) (n : ℕ) :
    Compress.fundG id (Compress.initial (paperCircleGridHeat a M t)) n =
      paperCircleHeatEntropy a M (n • t) := by
  rw [Compress.G_initial, Law.H, paperCircleGridHeat_iid_sum]
  rfl

/-- Source observation model: one native heat increment together with the accumulated sum. -/
def paperCircleHeatObserved (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (t : ℝ≥0) (n : ℕ) :
    Compress.Labelled (Grid M) :=
  Compress.observe id (Compress.initial (paperCircleGridHeat a M t)) n

/-- Exact source observation identity with every cost replaced by native heat entropy. -/
theorem paperCircleHeatObserved_condEntropy (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (t : ℝ≥0) (n : ℕ) :
    (paperCircleHeatObserved a M t n).law.Hcond Prod.fst Prod.snd =
      paperCircleHeatEntropy a M t + paperCircleHeatEntropy a M (n • t) -
        paperCircleHeatEntropy a M ((n + 1) • t) := by
  have H := Compress.observe_cost (id : Grid M → Grid M) Function.injective_id
    (Compress.initial (paperCircleGridHeat a M t)) n
  rw [fundG_initial_paperCircleGridHeat, fundG_initial_paperCircleGridHeat,
    fundG_initial_paperCircleGridHeat, one_smul] at H
  rw [Compress.fundG_one id Function.injective_id] at H
  change paperCircleHeatEntropy a M t -
    (paperCircleHeatObserved a M t n).law.Hcond Prod.fst Prod.snd = _ at H
  linarith

/-- The exact information gained about one increment is the heat-entropy increment. -/
theorem paperCircleHeatObserved_information (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (t : ℝ≥0) (n : ℕ) :
    paperCircleHeatEntropy a M t - (paperCircleHeatObserved a M t n).law.Hcond Prod.fst Prod.snd =
      paperCircleHeatEntropy a M ((n + 1) • t) - paperCircleHeatEntropy a M (n • t) := by
  rw [paperCircleHeatObserved_condEntropy]
  ring

/-- Observation information always lies between zero and the one-step entropy. -/
theorem paperCircleHeatObserved_information_bounds (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (t : ℝ≥0) (n : ℕ) :
    0 ≤ paperCircleHeatEntropy a M ((n + 1) • t) - paperCircleHeatEntropy a M (n • t) ∧
      paperCircleHeatEntropy a M ((n + 1) • t) - paperCircleHeatEntropy a M (n • t) ≤
        paperCircleHeatEntropy a M t := by
  rw [add_smul, one_smul]
  constructor
  · exact sub_nonneg.mpr (paperCircleHeatEntropy_le_add a M (n • t) t)
  · linarith [paperCircleHeatEntropy_add_le a M (n • t) t]

end
end RHTower
