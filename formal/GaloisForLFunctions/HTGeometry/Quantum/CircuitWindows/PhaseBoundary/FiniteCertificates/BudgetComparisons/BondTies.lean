import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.DistanceGap
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.BoundaryValues
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.BondMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.PathIncrement

/-! # Finitely many errors shared by budgets one bond sweep apart on each compact interval -/

open Set MeasureTheory
open scoped ENNReal NNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.BudgetComparisons
noncomputable section

abbrev generator {n : ℕ} (x : PathShell n) : selfAdjoint (Square (Bits (n+2))) :=
  ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian _⟩

private theorem signed_bond_step {n : ℕ} (x : PathShell n) (t : ℝ) :
    HasProjectiveCircuitApproximation (n+2) ((84*‖x‖^2)*|t|^2)
      (n+1) (unitaryEvolution (generator x).val t) := by
  obtain ⟨z,hz,C,hC,he⟩ := BondProducts.bond_sweep_error x |t| (abs_nonneg t) 1 one_pos
  have h : HasProjectiveCircuitApproximation (n+2) ((84*‖x‖^2)*|t|^2)
      (n+1) (unitaryEvolution (generator x).val |t|) := by
    refine ⟨z,hz,C,by simpa only [one_mul] using hC.le,?_⟩
    simpa only [Nat.cast_one,div_one,mul_comm (|t|^2)] using he
  rcases le_or_gt 0 t with ht|ht
  · simpa only [abs_of_nonneg ht] using h
  · simpa only [abs_of_neg ht,neg_neg] using h.neg_time (generator x)

theorem bond_increment {n : ℕ} (x : PathShell n) (s : ℕ) (t u : ℝ) :
    orbitCircuitDistance (generator x) (s+(n+1)) t ≤
      orbitCircuitDistance (generator x) s u + (84*‖x‖^2)*|t-u|^2 := by
  let H := generator x
  have hu := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val u) s
    (orbitCircuitDistance H s u)).mpr le_rfl
  have h := affordable_add_time H hu (signed_bond_step x (t-u))
  rw [show u+(t-u)=t by ring] at h
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp h

/-- Common approximation errors at dates where one extra bond sweep
gives precisely the same minimum projective error. -/
def tiedLevels {n : ℕ} (x : PathShell n) (s : ℕ) (a b : ℝ) : Set ℝ :=
  orbitCircuitDistance (generator x) s '' (Icc a b ∩
    {t | orbitCircuitDistance (generator x) s t=orbitCircuitDistance (generator x) (s+(n+1)) t})

/-- Avoiding the common values makes every smaller-budget fit a strict
interior fit with one extra sweep at the same error. -/
theorem bond_clearance {n : ℕ} (x : PathShell n) (s : ℕ) {a b e t : ℝ} (ht : t∈Icc a b)
    (hmiss : e∉tiedLevels x s a b) (hd : orbitCircuitDistance (generator x) s t≤e) :
    orbitCircuitDistance (generator x) (s+(n+1)) t<e := by
  have hle : orbitCircuitDistance (generator x) (s+(n+1)) t≤orbitCircuitDistance (generator x) s t := by
    simpa only [sub_self,abs_zero,zero_pow (by decide : 2≠0),mul_zero,add_zero] using bond_increment x s t t
  apply (hle.trans hd).lt_of_ne
  intro heq
  have he' := le_antisymm hd (heq.ge.trans hle)
  exact hmiss ⟨t,⟨ht,he'.trans heq.symm⟩,he'⟩

/-- On every finite chain, only finitely many such common values occur
in a compact window, even if the budgets tie throughout a time interval. -/
theorem finite_bond_ties {n : ℕ} (x : PathShell n) (s : ℕ) (a b : ℝ) :
    (tiedLevels x s a b).Finite := by
  let f := orbitCircuitDistance (generator x) s
  let g := orbitCircuitDistance (generator x) (s+(n+1))
  let K : ℝ≥0 := ⟨84*‖x‖^2,by positivity⟩
  have hd := ReturnLevels.shared_levels_dimension f g K 2 (by decide) (bond_increment x s)
  have hn := hausdorffMeasure_of_dimH_lt (hd.trans_lt (by norm_num : (1/(2:ℝ≥0∞))<((1:ℝ≥0):ℝ≥0∞)))
  have hz : volume (f '' {t | f t=g t})=0 := by
    simpa only [MeasureTheory.hausdorffMeasure_real,NNReal.coe_one] using hn
  exact finite_image_of_finite_frontier (isClosed_eq (orbitCircuitDistance_lipschitz _ _).continuous
    (orbitCircuitDistance_lipschitz _ _).continuous) (orbitCircuitDistance_lipschitz _ _).continuous hz a b
    (finite_distance_tie_frontier (generator x) (generator x) s (s+(n+1)) a b)

#print axioms finite_bond_ties
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.BudgetComparisons
