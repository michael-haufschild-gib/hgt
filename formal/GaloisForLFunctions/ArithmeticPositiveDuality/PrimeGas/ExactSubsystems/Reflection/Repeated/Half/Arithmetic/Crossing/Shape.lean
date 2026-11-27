import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Sharp.Threshold
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Flow

/-! # An open set of spectra with a sign-changing thermal comparison -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing

open Finset Real Set
open _root_.HTGeometry (finiteGibbsPartition)

variable {I : Type*} [Fintype I]

def crossingSet (I : Type*) [Fintype I] : Set (I → ℝ) :=
  {E | oddTrace (centered E) 1*oddTrace (centered E) 2<0}

theorem crossing_open : IsOpen (crossingSet I) := by
  have coord (i : I) : Continuous (fun E : I → ℝ => centered E i) := by
    unfold centered meanEnergy
    fun_prop
  have read (t : ℝ) : Continuous (fun E : I → ℝ => oddTrace (centered E) t) := by
    apply continuous_finsetSum
    intro i _
    exact (Real.continuous_exp.comp (continuous_const.mul (coord i))).sub
      (Real.continuous_exp.comp (continuous_const.mul (coord i)))
  exact isOpen_lt ((read 1).mul (read 2)) continuous_const

theorem crossing_nonempty (n : ℕ) (hn : 5≤n) : (crossingSet (Fin n)).Nonempty := by
  obtain ⟨E,hs,first,second⟩ := failure_at_order n 2 (by omega) (by unfold cutoff; omega)
  have one : oddTrace E 1=0 := by
    rw [oddTrace_eq,sub_eq_zero]
    simpa only [Nat.cast_one] using (first 1 le_rfl (by omega)).symm
  have two : oddTrace E 2≠0 := by
    rw [oddTrace_eq,sub_ne_zero]
    exact fun eq => second (by simpa only [Nat.cast_ofNat] using eq.symm)
  obtain ⟨u,zero,opposite⟩ := opens_crossing E hs one two
  exact ⟨move E 1 u,by simpa only [crossingSet,mem_setOf_eq,centered_eq_of_sum_zero zero] using opposite⟩

/-- Open sign changes force a zero strictly between the two probes. -/
theorem crossing_between {E : I → ℝ} (h : E ∈ crossingSet I) :
    ∃ b ∈ Ioo (1 : ℝ) 2, oddTrace (centered E) b=0 := by
  let f := fun t => oddTrace (centered E) t
  have cont : Continuous f := by
    unfold f oddTrace oddTerm
    fun_prop
  change f 1*f 2<0 at h
  have image : (0 : ℝ) ∈ f '' Icc 1 2 := by
    rcases mul_neg_iff.mp h with ⟨a,b⟩ | ⟨a,b⟩
    · exact intermediate_value_Icc' one_le_two cont.continuousOn ⟨b.le,a.le⟩
    · exact intermediate_value_Icc one_le_two cont.continuousOn ⟨a.le,b.le⟩
  obtain ⟨b,hb,zero⟩ := image
  have left : b≠1 := by rintro rfl; rw [zero,zero_mul] at h; exact lt_irrefl _ h
  have right : b≠2 := by rintro rfl; rw [zero,mul_zero] at h; exact lt_irrefl _ h
  exact ⟨b,⟨lt_of_le_of_ne hb.1 left.symm,lt_of_le_of_ne hb.2 right⟩,zero⟩

#print axioms crossing_nonempty
#print axioms crossing_between

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing
