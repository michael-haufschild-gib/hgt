import GaloisForLFunctions.HTGeometry.AffineDynamics.ExitTimesOfLegendreMeanFlows
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exact initial reserves for finite and repeating schedules

Singh and Vaughan's scalar barrier comparison becomes a backwards recursion
on a switched Legendre mean flow. For a periodic schedule the admissible
initial half-line is nonempty precisely when the attracting cycle clears
the same reserve. A cycle below threshold gives an exact failure time.
-/

noncomputable section
open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.AffineDynamics

/-- Minimum starting slack required by a terminal bound c on one segment. -/
def preimageSlack (b t c : ℝ) : ℝ := Real.exp t*c-(Real.exp t-1)*b

theorem preimageSlack_le (a b t c : ℝ) :
    preimageSlack b t c ≤ a ↔ c ≤ slack a b t := by
  calc
    preimageSlack b t c ≤ a ↔ Real.exp t*c ≤ a + (Real.exp t-1)*b := sub_le_iff_le_add
    _ ↔ Real.exp t*c ≤ Real.exp t*slack a b t := by rw [scaled_slack]
    _ ↔ c ≤ slack a b t := mul_le_mul_iff_right₀ (Real.exp_pos t)

/-- Reserve guaranteeing safety at all intermediate times and a prescribed
terminal slack. At the empty schedule both constraints apply at time zero. -/
def reserve : List Segment → ℝ → ℝ
  | [], c => max 0 c
  | (t,b)::L, c => max 0 (preimageSlack b t (reserve L c))

theorem reserve_nonneg (L : List Segment) (c : ℝ) : 0 ≤ reserve L c := by
  cases L with
  | nil => exact le_max_left _ _
  | cons p L => exact le_max_left _ _

/-- The recursion is sharp simultaneously for safety and terminal payoff. -/
theorem reserve_iff (L : List Segment) (a c : ℝ) :
    reserve L c ≤ a ↔ safeAlong a L ∧ c ≤ endpoint a L := by
  induction L generalizing a with
  | nil => exact max_le_iff
  | cons p L ih =>
    rcases p with ⟨t,b⟩
    rw [reserve,max_le_iff,preimageSlack_le,ih]
    change _ ↔ (((∀ s ∈ Icc 0 (t : ℝ), 0 ≤ slack a b s) ∧ safeAlong (slack a b t) L) ∧ _)
    rw [window_safe_iff a b 0 t t.property]
    have hend (s : ℝ) (h : safeAlong s L) : 0 ≤ s :=
      (switched_safe_iff s L).1 h [] L rfl
    have h₀ : slack a b 0=a := by simp [slack]
    rw [h₀]
    exact ⟨fun ⟨ha,hs,hc⟩ => ⟨⟨⟨ha,hend _ hs⟩,hs⟩,hc⟩,
      fun ⟨⟨⟨ha,_⟩,hs⟩,hc⟩ => ⟨ha,hs,hc⟩⟩

/-- Reserves compose backwards exactly under concatenation. -/
theorem reserve_append (P Q : List Segment) (c : ℝ) :
    reserve (P++Q) c = reserve P (reserve Q c) := by
  induction P with
  | nil => exact (max_eq_right (reserve_nonneg Q c)).symm
  | cons p P ih => simp only [List.cons_append,reserve,ih]

/-- Every safe schedule ends with nonnegative slack, so terminal bound zero
imposes exactly the continuous-time safety condition. -/
theorem safe_reserve (L : List Segment) (a : ℝ) :
    safeAlong a L ↔ reserve L 0 ≤ a := by
  rw [reserve_iff]
  exact ⟨fun hs => ⟨hs,(switched_safe_iff a L).1 hs L [] (List.append_nil _).symm⟩,And.left⟩

/-- Total duration of a single passage through the schedule. -/
abbrev scheduleDuration (L : List Segment) := (L.map fun p => (p.1 : ℝ)).sum

/-- Repeated cycle endpoints converge to the attracting periodic initial slack. -/
theorem cycle_limit (a : ℝ) (L : List Segment) (hL : 0 < scheduleDuration L) :
    Tendsto (fun k : ℕ => (fun x => endpoint x L)^[k] a) atTop (𝓝 (periodicSlack L)) := by
  have hrat := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hL)
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hrat).mul_const
    (a-periodicSlack L)).add_const (periodicSlack L)
  simp only [zero_mul,zero_add] at h
  exact h.congr fun k => (eq_add_of_sub_eq (after_cycles a L k hL)).symm

/-- Infinite repetition is viable iff both the actual start and the periodic
start clear the one-cycle reserve. -/
theorem repeated_safe_iff (a : ℝ) (L : List Segment) (hL : 0 < scheduleDuration L) :
    (∀ k : ℕ, safeAlong ((fun x => endpoint x L)^[k] a) L) ↔
      reserve L 0 ≤ a ∧ reserve L 0 ≤ periodicSlack L := by
  simp_rw [safe_reserve]
  constructor
  · intro h
    exact ⟨h 0,le_of_tendsto_of_tendsto tendsto_const_nhds (cycle_limit a L hL)
      (Eventually.of_forall h)⟩
  · rintro ⟨ha,hp⟩ k
    let r := Real.exp (-(scheduleDuration L))
    have h₀ : 0 ≤ r^k := pow_nonneg (Real.exp_pos _).le _
    have h₁ : r^k ≤ 1 := pow_le_one₀ (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hL.le))
    have h := after_cycles a L k hL
    change _ - periodicSlack L = r^k*(a-periodicSlack L) at h
    have hA := mul_le_mul_of_nonneg_left ha h₀
    have hP := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr h₁)
    linarith only [h,hA,hP]

/-- When the periodic orbit fails, the last safe cycle is specified by one
logarithmic inequality. The boundary cycle is included. -/
theorem last_safe_cycle (a : ℝ) (L : List Segment) (hL : 0 < scheduleDuration L)
    (hP : periodicSlack L < reserve L 0) (ha : reserve L 0 ≤ a) (k : ℕ) :
    safeAlong ((fun x => endpoint x L)^[k] a) L ↔
      (k : ℝ)*scheduleDuration L ≤ Real.log ((a-periodicSlack L)/(reserve L 0-periodicSlack L)) := by
  have hd := sub_pos.mpr hP
  have hn := sub_pos.mpr (hP.trans_le ha)
  have h := after_cycles a L k hL
  have hpow : Real.exp (-(scheduleDuration L))^k = (Real.exp ((k : ℝ)*scheduleDuration L))⁻¹ := by
    rw [← Real.exp_nat_mul,← Real.exp_neg]
    congr 1
    ring
  change _ - periodicSlack L = Real.exp (-(scheduleDuration L))^k*(a-periodicSlack L) at h
  rw [hpow,inv_mul_eq_div,eq_div_iff (Real.exp_pos _).ne'] at h
  rw [safe_reserve,← Real.exp_le_exp (x := (k : ℝ)*scheduleDuration L) (y := Real.log _),Real.exp_log (div_pos hn hd),le_div_iff₀ hd,← h]
  have he := Real.exp_pos ((k : ℝ)*scheduleDuration L)
  rw [mul_comm (Real.exp _) _,mul_le_mul_iff_left₀ he]
  constructor <;> intro H <;> linarith only [H]

end GaloisForLFunctions.HTGeometry.AffineDynamics

#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.preimageSlack_le
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.reserve_nonneg
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.reserve_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.reserve_append
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.safe_reserve
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.cycle_limit
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.repeated_safe_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.last_safe_cycle
