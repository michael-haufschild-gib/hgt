import GaloisForLFunctions.RepresentationLifting.Permutation.HistogramDynamics
import GaloisForLFunctions.RepresentationLifting.Permutation.OccupationReadout

/-!
# Replication invariance and exact occupation dynamics

Uniformly repeating a finite encoded history does not change the shared
attention readout at any depth. For the corpus's occupation tokens, the
histogram recurrence has exactly two states, weighted by the occupied and
vacant counts. This gives an explicit realization of the occupation-number
factorization and identifies an absolute-length ambiguity of pooled readout.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.RepresentationLifting.SharedAttention
open HTGeometry

variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Repeating every encoded token the same positive number of times leaves the prediction unchanged. -/
theorem readout_replicate (k : ℕ) (score : V → V → ℝ) (value post : V → V)
    (poolScore : V → ℝ) (output : V → W) (depth : ℕ) (initial : V) (input : ι → V) :
    readout score value post poolScore output depth initial
        (fun p : ι × Fin (k + 1) => input p.1) =
      readout score value post poolScore output depth initial input := by
  classical
  have hrep : historyMultiplicity (Prod.fst : ι × Fin (k + 1) → ι) = fun _ => k + 1 := by
    funext i
    unfold historyMultiplicity
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ j : ι, if j = i then k + 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i <;> simp [hj]
      _ = _ := by simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hid : historyMultiplicity (id : ι → ι) = fun _ => 1 := by
    funext i
    change (∑ j : ι, if j = i then 1 else 0) = 1
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hbase := readout_eq_countReadout (id : ι → ι) score value post
    poolScore output depth initial input
  simp only [Function.comp_id, hid] at hbase
  calc
    _ = countReadout (fun _ : ι => k + 1) score value post poolScore output depth initial input := by
      simpa only [hrep, Function.comp_def] using
        readout_eq_countReadout (Prod.fst : ι × Fin (k + 1) → ι)
          score value post poolScore output depth initial input
    _ = countReadout (fun _ : ι => 1) score value post poolScore output depth initial input := by
      simpa only [mul_one] using countReadout_scale k (fun _ : ι => 1)
        score value post poolScore output depth initial input
    _ = _ := hbase.symm

/-- Multiplicities of the occupied and vacant symbols. -/
def occupationCount (n m : ℕ) (b : Bool) : ℕ := if b then m else n - m

/-- The two feature values associated with occupancy. -/
def occupationValues (occupied vacant : V) (b : Bool) : V := if b then occupied else vacant

omit [AddCommGroup V] [Module ℝ V] in
private theorem occupationTokens_eq_values_comp (n : ℕ) (occupied vacant : V)
    (S : Finset (Fin n)) :
    occupationTokens n occupied vacant S = occupationValues occupied vacant ∘ sampleIndicator S := by
  funext i
  rfl

private theorem historyMultiplicity_sampleIndicator (n : ℕ) (S : Finset (Fin n)) :
    historyMultiplicity (sampleIndicator S) = occupationCount n S.card := by
  have hc (b : Bool) : historyMultiplicity (sampleIndicator S) b =
      Fintype.card {i // sampleIndicator S i = b} := by
    simp [historyMultiplicity, Fintype.card_subtype]
  funext b
  cases b
  · rw [hc, card_sampleIndicator_false]
    simp [occupationCount]
  · rw [hc, card_sampleIndicator_true]
    rfl

/-- Every occupation-token state is one of two explicitly evolving states. -/
theorem occupation_refine_eq_countRefine (n : ℕ) (score : V → V → ℝ)
    (value post : V → V) (depth : ℕ) (initial occupied vacant : V) (S : Finset (Fin n)) :
    refine score value post (occupationTokens n occupied vacant S) depth (fun _ => initial) =
      countRefine (occupationCount n S.card) score value post
        (occupationValues occupied vacant) depth (fun _ => initial) ∘ sampleIndicator S := by
  rw [occupationTokens_eq_values_comp,
    show (fun _ : Fin n => initial) = (fun _ : Bool => initial) ∘ sampleIndicator S from rfl,
    refine_eq_countRefine, historyMultiplicity_sampleIndicator]

/-- The occupation readout has an explicit two-state formula at every depth. -/
theorem occupation_readout_eq_countReadout (n : ℕ) (score : V → V → ℝ)
    (value post : V → V) (poolScore : V → ℝ) (output : V → W)
    (depth : ℕ) (initial occupied vacant : V) (S : Finset (Fin n)) :
    readout score value post poolScore output depth initial (occupationTokens n occupied vacant S) =
      countReadout (occupationCount n S.card) score value post poolScore output depth initial
        (occupationValues occupied vacant) := by
  rw [occupationTokens_eq_values_comp, readout_eq_countReadout, historyMultiplicity_sampleIndicator]

omit [AddCommGroup V] [Module ℝ V] in
/-- The two-state softmax includes the exact vacant and occupied multiplicities. -/
theorem countPool_occupation (n m : ℕ) (score : V → ℝ) (value : V → W) (x : Bool → V) :
    countPool (occupationCount n m) score value x =
      ((m : ℝ) * Real.exp (score (x true)) + (n - m : ℕ) * Real.exp (score (x false)))⁻¹ •
        (((m : ℝ) * Real.exp (score (x true))) • value (x true) +
          ((n - m : ℕ) * Real.exp (score (x false))) • value (x false)) := by
  simp [countPool, occupationCount]

#print axioms readout_replicate
#print axioms occupation_refine_eq_countRefine
#print axioms occupation_readout_eq_countReadout
#print axioms countPool_occupation

end GaloisForLFunctions.RepresentationLifting.SharedAttention
