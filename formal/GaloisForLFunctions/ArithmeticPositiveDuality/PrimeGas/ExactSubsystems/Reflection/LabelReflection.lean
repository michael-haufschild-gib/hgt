import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Fugacity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.ReciprocalPolynomial
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Marginal

/-! # Reflection of arbitrary finite exact subsystem spectra -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing

variable {ι κ : Type*}

private theorem label_injective {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) : Function.Injective a := by
  obtain ⟨v,_⟩ := h.2 1
  intro i j he
  exact congrArg Prod.fst (h.1 (a₁ := (i,v.2)) (a₂ := (j,v.2)) (congrArg (· * b v.2) he))

variable [Fintype ι]

/-- The finite subsystem has a top label M and a state involution pairing labels with product M. -/
theorem finite_label_reflection {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :
    ∃ m : ι, ∃ R : Equiv.Perm ι, (∀ i, a i * a (R i) = a m) ∧ Function.Involutive R := by
  classical
  let A := Finset.univ.image a
  let K := A ∪ (A ×ˢ A).image (fun v => v.1*v.2)
  have hA (i : ι) : a i ∈ A := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hK (i : ι) : a i ∈ K := Finset.mem_union_left _ (hA i)
  have hprod (i j : ι) : a i*a j ∈ K := Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨(a i,a j),Finset.mem_product.mpr ⟨hA i,hA j⟩,rfl⟩)
  obtain ⟨t,ht⟩ := exists_separating_grade K
  let g := fun i => grade t.val (a i).val
  have hg : Function.Injective g := fun i j he => label_injective h (ht (hK i) (hK j) he)
  let S := Finset.univ.image g
  have hS (i : ι) : g i ∈ S := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have h₀ : 0 ∈ S := by
    refine Finset.mem_image.mpr ⟨factorVacuum h,Finset.mem_univ _,?_⟩
    change grade t.val (a (factorVacuum h)).val = 0
    rw [factorVacuum_label h]
    exact grade_one _
  have hf (z : ℂ) (hz : ‖z‖ < 1) : (gradePolynomial S).eval z ≠ 0 := by
    have he : (gradePolynomial S).eval z = ∑ i, z^(g i) := by
      simp only [gradePolynomial,Polynomial.eval_finsetSum,Polynomial.eval_pow,Polynomial.eval_X]
      exact Finset.sum_image (fun i _ j _ he => hg he)
    rw [he]
    exact graded_partition_ne_zero h t hz
  let D := S.max' ⟨0,h₀⟩
  obtain ⟨m,_,hm⟩ := Finset.mem_image.mp (show D ∈ Finset.univ.image g from S.max'_mem _)
  have hall (i : ι) : ∃ j, a i*a j = a m := by
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (grade_reflected_mem S h₀ hf (hS i))
    refine ⟨j,ht (hprod i j) (hK m) ?_⟩
    change grade t.val ((a i).val*(a j).val) = g m
    rw [grade_mul _ (a i).ne_zero (a j).ne_zero]
    change g i+g j = g m
    rw [hj,Nat.add_sub_of_le (S.le_max' _ (hS i)),hm]
  choose r hr using hall
  have hr₂ : Function.Involutive r := fun i => label_injective h (mul_left_cancel
    ((hr (r i)).trans ((mul_comm (a (r i)) (a i)).trans (hr i)).symm))
  let R : Equiv.Perm ι := ⟨r,r,hr₂,hr₂⟩
  exact ⟨m,R,hr,hr₂⟩

/-- The reflecting state is the unique greatest label for divisibility. -/
theorem unique_divisibility_top {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :
    ∃! m : ι, ∀ i, a i ∣ a m := by
  obtain ⟨m,R,hr,_⟩ := finite_label_reflection h
  have hm (i : ι) : a i ∣ a m := ⟨a (R i),(hr i).symm⟩
  exact ⟨m,hm,fun j hj => label_injective h (le_antisymm (PNat.le_of_dvd (hm j)) (PNat.le_of_dvd (hj m)))⟩

/-- Particle-hole reflection takes every energy to the top energy minus that energy. -/
theorem finite_energy_reflection {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :
    ∃ m : ι, ∃ R : Equiv.Perm ι, Function.Involutive R ∧
      ∀ i, energy (a (R i)) = energy (a m)-energy (a i) := by
  obtain ⟨m,R,hr,hi⟩ := finite_label_reflection h
  refine ⟨m,R,hi,fun i => ?_⟩
  rw [← hr i,energy_mul,add_sub_cancel_left]

#print axioms finite_label_reflection
#print axioms unique_divisibility_top
#print axioms finite_energy_reflection

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
