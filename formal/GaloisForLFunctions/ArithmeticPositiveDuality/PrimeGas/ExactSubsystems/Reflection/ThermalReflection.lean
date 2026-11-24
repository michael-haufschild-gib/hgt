import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.LabelReflection

/-! # Reflection of finite complex partitions and exchange of positive and negative temperature -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing

variable {ι κ : Type*} [Fintype ι]

/-- The thermal trace of a finite spectrum, evaluated at any complex temperature parameter. -/
def finiteHeatTrace (a : ι → ℕ+) (s : ℂ) := ∑ i, heat s (a i)

private theorem heat_cancel (s : ℂ) (n : ℕ+) : heat s n*heat (-s) n = 1 := by
  rw [← heat_add,add_neg_cancel]
  simp [heat]

/-- Factoring out the top energy exchanges a finite partition with the same partition at -s. -/
theorem finite_partition_reflection {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :
    ∃ m : ι, (∀ i, a i ∣ a m) ∧ ∀ s : ℂ,
      finiteHeatTrace a s = heat s (a m)*finiteHeatTrace a (-s) := by
  obtain ⟨m,R,hr,_⟩ := finite_label_reflection h
  refine ⟨m,fun i => ⟨a (R i),(hr i).symm⟩,fun s => ?_⟩
  calc
    _ = ∑ i, heat s (a (R i)) := (Equiv.sum_comp R (fun i => heat s (a i))).symm
    _ = _ := by
      rw [finiteHeatTrace,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = heat s (a (R i)) * (heat s (a i)*heat (-s) (a i)) := by rw [heat_cancel,mul_one]
        _ = _ := by rw [← hr i,heat_mul]; ring

/-- Every zero of any finite exact subsystem trace, with arbitrarily many prime species, lies on Re(s)=0. -/
theorem finite_partition_zeros_on_axis {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b)
    {s : ℂ} (hz : finiteHeatTrace a s = 0) : s.re = 0 := by
  have hn : ¬ 0 < s.re := fun hp => finiteSubsystem_zero_free h hp hz
  apply le_antisymm (le_of_not_gt hn)
  by_contra! hneg
  obtain ⟨m,_,hm⟩ := finite_partition_reflection h
  rw [hm s] at hz
  have hleft := (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)
  exact finiteSubsystem_zero_free h (s := -s) (by simpa only [Complex.neg_re,neg_pos] using hneg) hleft

#print axioms finite_partition_reflection
#print axioms finite_partition_zeros_on_axis

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
