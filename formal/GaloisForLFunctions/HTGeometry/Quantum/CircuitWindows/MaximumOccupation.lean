import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TranslatedWindowPacking
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion
import GaloisForLFunctions.HTGeometry.Quantum.FirstCircuitSaturationBoundary

/-! # Occupation below a fraction of a robust orbit maximum -/
open Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem continuous_budget_distance (H : selfAdjoint (Reg n)) (s : ℕ) :
    Continuous (orbitCircuitDistance H s) := by
  have hL : LipschitzWith ⟨‖H.val‖,norm_nonneg _⟩ (unitaryEvolution H.val) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,Real.dist_eq]
    exact norm_unitaryEvolution_time_sub_le H.2 x y
  exact (Metric.continuous_infDist_pt _).comp hL.continuous

private theorem affordable_iff_distance (H : selfAdjoint (Reg n)) (s : ℕ) (t ε : ℝ) :
    HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val t) ↔ orbitCircuitDistance H s t ≤ ε :=
  hasProjectiveCircuitApproximation_iff_infDist _ _ _

/-- Concatenating projective approximations adds their circuit budgets and errors. -/
private theorem affordable_add_time {n i j : ℕ} (H : selfAdjoint (Reg n)) {x y e f : ℝ}
    (hx : HasProjectiveCircuitApproximation n e i (unitaryEvolution H.val x))
    (hy : HasProjectiveCircuitApproximation n f j (unitaryEvolution H.val y)) :
    HasProjectiveCircuitApproximation n (e+f) (i+j) (unitaryEvolution H.val (x+y)) := by
  by_contra hno
  have hfar : ProjectiveCircuitSeparated n (e+f) (i+j) (unitaryEvolution H.val (x+y)) :=
    fun z hz C hC => lt_of_not_ge fun h => hno ⟨z,hz,C,hC,h⟩
  have h := projectiveCircuitSeparated_unitaryEvolution_backward_cone H (by omega : j ≤ i+j) hfar hy
    (le_rfl : e+f ≤ e+f)
  rw [add_sub_cancel_right,Nat.add_sub_cancel] at h
  obtain ⟨z,hz,C,hC,herr⟩ := hx
  exact (not_lt_of_ge herr) (h z hz C hC)

private theorem affordable_enlarge_budget {n i j : ℕ} {X : Reg n} {ε : ℝ} (hij : i ≤ j)
    (h : HasProjectiveCircuitApproximation n ε i X) : HasProjectiveCircuitApproximation n ε j X := by
  obtain ⟨z,hz,C,hC,herr⟩ := h
  exact ⟨z,hz,C,hC.trans hij,herr⟩

/-- A hard orbit point at error 2qε yields q+1 disjoint translates of the
s-gate hit set at error ε. Interpolation to successive gate budgets gives
physical times for all the translates between zero and the hard point. -/
theorem affordable_occupation_of_hard_lag {n s q : ℕ} (H : selfAdjoint (Reg n)) (hq : 0 < q)
    {ε : ℝ} (hε : 0 ≤ ε) (B : ℝ) (hB : 0 ≤ B)
    (hh : ProjectiveCircuitSeparated n (2*(q:ℝ)*ε) (2*s*q) (unitaryEvolution H.val B))
    (a T : ℝ) (hT : 0 ≤ T) :
    ((q:ℝ)+1)*volume.real ({t | HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val t)}
      ∩ Icc a (a+T)) ≤ T+B := by
  let U := unitaryEvolution H.val
  let A := {t | HasProjectiveCircuitApproximation n ε s (U t)}
  let d := orbitCircuitDistance H (2*s*q) B
  have hd : 2*(q:ℝ)*ε < d := by
    by_contra! h
    obtain ⟨z,hz,C,hC,he⟩ := (affordable_iff_distance H _ _ _).mpr h
    exact (not_lt_of_ge he) (hh z hz C hC)
  let r := d/(q:ℝ)
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hr : 2*ε < r := (lt_div_iff₀ hqr).mpr (by linarith only [hd])
  have hrpos : 0 ≤ r := le_trans (by positivity) hr.le
  have hrd : (q:ℝ)*r = d := by dsimp [r]; field_simp [hqr.ne']
  have level (i : Fin (q+1)) : ∃ t ∈ Icc 0 B, orbitCircuitDistance H (2*s*i.val) t = (i.val:ℝ)*r := by
    let b := 2*s*i.val
    have h0 : orbitCircuitDistance H b 0 ≤ 0 := by
      apply (affordable_iff_distance H b 0 0).mp
      refine ⟨1,by simp,TwoQubitCircuit.one n,Nat.zero_le _,?_⟩
      simp [TwoQubitCircuit.one_eval,unitaryEvolution]
    have hiq : i.val ≤ q := Nat.lt_succ_iff.mp i.isLt
    have hf := (affordable_iff_distance H b B _).mpr (le_rfl : orbitCircuitDistance H b B ≤ _)
    have hbig := (affordable_iff_distance H (2*s*q) B _).mp
      (affordable_enlarge_budget (Nat.mul_le_mul_left (2*s) hiq) hf)
    have hc : (i.val:ℝ)*r ≤ d := by
      rw [← hrd]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hiq) hrpos
    exact intermediate_value_Icc hB (continuous_budget_distance H b).continuousOn
      ⟨h0.trans (by positivity),hc.trans hbig⟩
  choose u hu heq using level
  have hforbid {i j : Fin (q+1)} (hij : i < j) (x : ℝ) (hi : x-u i ∈ A) (hj : x-u j ∈ A) : False := by
    have hstart := (affordable_iff_distance H (2*s*i.val) (u i) _).mpr (heq i).le
    have hj' : HasProjectiveCircuitApproximation n ε s (U (x-u j)) := hj
    have hinc := affordable_add_time H hi (hj'.neg_time H)
    have hend := affordable_add_time H hstart hinc
    rw [show u i+((x-u i)+ -(x-u j))=u j by ring] at hend
    have hbudget : 2*s*i.val+(s+s) ≤ 2*s*j.val := by
      have hstep := Nat.mul_le_mul_left (2*s) (show i.val+1 ≤ j.val from hij)
      simpa only [Nat.mul_add,Nat.mul_one,two_mul] using hstep
    have hdist := (affordable_iff_distance H (2*s*j.val) (u j) _).mp (affordable_enlarge_budget hbudget hend)
    rw [heq] at hdist
    have hstep : (i.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast (show i.val+1 ≤ j.val from hij)
    linarith only [hdist,hr,mul_le_mul_of_nonneg_right hstep hrpos]
  have hm : MeasurableSet A := by
    change MeasurableSet {t | HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val t)}
    simp only [affordable_iff_distance H]
    exact (isClosed_le (continuous_budget_distance H s) continuous_const).measurableSet
  have hsep (i j : Fin (q+1)) (hne : i ≠ j) (x : ℝ) (hi : x-u i ∈ A) (hj : x-u j ∈ A) : False :=
    (lt_or_gt_of_ne hne).elim (fun h => hforbid h x hi hj) (fun h => hforbid h x hj hi)
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
    occupation_mul_card_le_of_disjoint_shifts hm u hB hu hsep a T hT

/-- Two translates give the half-occupation bound at half the error. -/
theorem affordable_time_le_half_of_hard_lag {n s : ℕ} (H : selfAdjoint (Reg n))
    (u : ℝ) (hu : 0 ≤ u) (hh : ProjectiveCircuitSeparated n (1/10:ℝ) (2*s)
      (unitaryEvolution H.val u)) (a T : ℝ) (hT : 0 ≤ T) :
    2*volume.real ({t | HasProjectiveCircuitApproximation n (1/20:ℝ) s
      (unitaryEvolution H.val t)} ∩ Icc a (a+T)) ≤ T+u := by
  simpa using affordable_occupation_of_hard_lag H (q := 1) (s := s) (by decide)
    (by norm_num : (0:ℝ) ≤ 1/20) u hu (by norm_num; exact hh) a T hT

#print axioms affordable_occupation_of_hard_lag
end
end GaloisForLFunctions.HTGeometry
