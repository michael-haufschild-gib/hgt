import GaloisForLFunctions.HTGeometry.SortedSpectrumContinuity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Outgoing

/-! # The two rays of sorted centered log probabilities in a prime gas -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold.Noise

open Finset Real GaloisForLFunctions.HTGeometry _root_.HTGeometry

variable {n : ℕ} {X : Type*} [Fintype X]

def coordinates (f : X → ℝ) (i : Fin (Fintype.card X)) := f ((Fintype.equivFin X).symm i)

def centered (v : Fin n → ℝ) (i : Fin n) := v i - (∑ j, v j)/n

def rankedLog (P : X → ℝ) := sortedTuple (centered (coordinates (fun x => -log (P x))))

def lowVector (E : X → ℝ) := sortedTuple (centered (coordinates E))

def highVector (E : X → ℝ) (i : Fin (Fintype.card X)) := -lowVector E i.rev

private theorem sorted_perm (v : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : sortedTuple (v ∘ σ) = sortedTuple v :=
  Tuple.unique_monotone (f := v) (σ := (Tuple.sort (v ∘ σ)).trans σ) (τ := Tuple.sort v)
    (monotone_sortedTuple (v ∘ σ)) (monotone_sortedTuple v)

private theorem centered_perm (v : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    centered (v ∘ σ) = (centered v) ∘ σ := by
  funext i
  simp only [centered,Function.comp_apply,Equiv.sum_comp σ v]

/-- Permuting the measured states leaves the entire ranked observation unchanged, including ties. -/
theorem rankedLog_perm (P : X → ℝ) (R : Equiv.Perm X) : rankedLog (P ∘ R) = rankedLog P := by
  let a := Fintype.equivFin X
  let σ := (a.symm.trans R).trans a
  have hc : coordinates (fun x => -log ((P ∘ R) x)) = coordinates (fun x => -log (P x)) ∘ σ := by
    funext i
    simp only [coordinates,σ,a,Equiv.trans_apply,Equiv.symm_apply_apply,Function.comp_apply]
  rw [rankedLog,rankedLog,hc,centered_perm,sorted_perm]

private theorem centered_affine (v : Fin n → ℝ) (t d : ℝ) :
    centered (fun i => t*v i+d) = fun i => t*centered v i := by
  funext i
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  simp only [centered,sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]
  field_simp
  ring

private theorem log_weight (E : X → ℝ) (t : ℝ) (x : X) :
    -log (finiteGibbsStateWeight t E x) = t*E x+log (finiteGibbsPartition t E) := by
  letI : Nonempty X := ⟨x⟩
  rw [finiteGibbsStateWeight,log_div (exp_pos _).ne' (finiteGibbsPartition_pos _ _).ne',log_exp]
  ring

private theorem input_gibbs (E : X → ℝ) (t : ℝ) :
    centered (coordinates (fun x => -log (finiteGibbsStateWeight t E x))) =
      fun i => t*centered (coordinates E) i := by
  simp_rw [log_weight]
  exact centered_affine _ _ _

/-- Positive damping preserves the energy ranks. -/
theorem ranked_positive (E : X → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    rankedLog (finiteGibbsStateWeight t E) = fun i => t*lowVector E i := by
  rw [rankedLog,input_gibbs]
  let v := centered (coordinates E)
  exact Tuple.unique_monotone (f := fun i => t*v i) (τ := Tuple.sort v) (monotone_sortedTuple _)
    (fun i j hij => mul_le_mul_of_nonneg_left (monotone_sortedTuple v hij) ht)

/-- Negative damping reverses the energy ranks while preserving multiplicity. -/
theorem ranked_negative (E : X → ℝ) {t : ℝ} (ht : t ≤ 0) :
    rankedLog (finiteGibbsStateWeight t E) = fun i => (-t)*highVector E i := by
  rw [rankedLog,input_gibbs]
  let v := centered (coordinates E)
  let τ := Fin.revPerm.trans (Tuple.sort v)
  have h : sortedTuple (fun i => t*v i) = (fun i => t*v i) ∘ τ :=
    Tuple.unique_monotone (f := fun i => t*v i) (τ := τ) (monotone_sortedTuple _)
      (fun i j hij => mul_le_mul_of_nonpos_left (monotone_sortedTuple v (Fin.rev_le_rev.mpr hij)) ht)
  rw [h]
  funext i
  change t*lowVector E i.rev = (-t)*(-lowVector E i.rev)
  ring

#print axioms rankedLog_perm
#print axioms ranked_positive
#print axioms ranked_negative

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold.Noise
