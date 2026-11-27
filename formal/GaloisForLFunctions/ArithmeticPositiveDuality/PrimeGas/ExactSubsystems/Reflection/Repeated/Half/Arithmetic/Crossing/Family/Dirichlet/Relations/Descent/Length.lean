import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Descent.CoefficientLift

/-! # The shortest algebraic-integer relation on distinct shells -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Real Finset Set MvPolynomial

/-- A relation of exactly k distinct shell terms, all with nonzero algebraic-integer coefficients. -/
def shellRelationLength (s : ℝ) (k : ℕ) : Prop :=
  ∃ (a : Fin k → ℕ+) (c : Fin k → ShellIntegers), 0<k ∧ Function.Injective a ∧
    (∀ i, c i ≠ 0) ∧ (∑ i, (c i : ℂ)*(shellPower s (a i) : ℂ))=0

noncomputable def shortest (s : ℝ) : ℕ := sInf {k : ℕ | shellRelationLength s k}

theorem shortest_le {s : ℝ} {k : ℕ} (h : shellRelationLength s k) : shortest s ≤ k := Nat.sInf_le h

theorem shortest_attained {s : ℝ} (h : ∃ k, shellRelationLength s k) :
    shellRelationLength s (shortest s) := Nat.sInf_mem h

theorem relation_of_finite {ι : Type} [Fintype ι] [Nonempty ι] (a : ι → ℕ+) (c : ι → ShellIntegers)
    {s : ℝ} (inj : Function.Injective a) (nz : ∀ i, c i ≠ 0)
    (zero : (∑ i, (c i : ℂ)*(shellPower s (a i) : ℂ))=0) : shellRelationLength s (Fintype.card ι) := by
  let e := (Fintype.equivFin ι).symm
  exact ⟨a ∘ e,c ∘ e,Fintype.card_pos,inj.comp e.injective,fun i => nz (e i),
    (Equiv.sum_comp e (fun i => (c i : ℂ)*(shellPower s (a i) : ℂ))).trans zero⟩

theorem resonance_has_length {s : ℝ} (res : Resonant s) : ∃ k, shellRelationLength s k := by
  classical
  obtain ⟨P,ne,root⟩ := (resonant_iff_polynomial s).mp res
  let S := P.support
  obtain ⟨i,hi⟩ := support_nonempty.mpr ne
  letI : Nonempty S := ⟨⟨i,hi⟩⟩
  let c (i : S) : ShellIntegers := (coeff i.val P : ℤ)
  refine ⟨_,relation_of_finite (fun i : S => label i.val) c (label.injective.comp Subtype.val_injective)
    (fun i => Int.cast_ne_zero.mpr (mem_support_iff.mp i.property)) ?_⟩
  have eq := (value_sum P s).symm.trans root
  have cast := congrArg ((↑) : ℝ → ℂ) eq
  change (∑ i : S, (((coeff i.val P : ℤ) : ℂ))*((shellPower s (label i.val) : ℝ) : ℂ))=0
  rw [sum_coe_sort S (fun v => ((coeff v P : ℤ) : ℂ)*(shellPower s (label v) : ℂ))]
  simpa only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_intCast,Complex.ofReal_zero] using cast

/-- Complementing each label inside their common product reverses the sign
of the temperature and keeps exactly the same number of shell terms. -/
theorem reflected_length {s : ℝ} {k : ℕ} (h : shellRelationLength s k) : shellRelationLength (-s) k := by
  classical
  obtain ⟨a,c,hk,inj,live,zero⟩ := h
  let D := ∏ i, a i
  let b (i : Fin k) := ∏ j ∈ (univ.erase i), a j
  have constant (i : Fin k) : b i*a i=D := prod_erase_mul univ a (mem_univ i)
  have oneToOne : Function.Injective b := by
    intro i j eq
    apply inj
    have prod := (constant i).trans (constant j).symm
    rw [eq] at prod
    exact mul_left_cancel prod
  have e (i : Fin k) : energy D=energy (b i)+energy (a i) := by rw [← constant i,energy_mul]
  have law (i : Fin k) : shellPower (-s) (b i)=exp (-s*energy D)*shellPower s (a i) := by
    rw [shellPower_exp,shellPower_exp,← exp_add,e]
    congr 1
    ring
  refine ⟨b,c,hk,oneToOne,live,?_⟩
  simp only [law,Complex.ofReal_mul]
  calc (∑ i, (c i : ℂ)*((exp (-s*energy D) : ℂ)*(shellPower s (a i) : ℂ))) =
        (exp (-s*energy D) : ℂ)*(∑ i, (c i : ℂ)*(shellPower s (a i) : ℂ)) := by
          rw [mul_sum]; exact sum_congr rfl fun i _ => mul_left_comm _ _ _
       _ = 0 := by rw [zero,mul_zero]

/-- Removing zero coefficients from a nonzero relation strictly decreases
its length as soon as one shell has been eliminated. -/
theorem shorter_of_zero_coefficient {s : ℝ} {k : ℕ} (a : Fin k → ℕ+) (inj : Function.Injective a)
    (c : Fin k → ShellIntegers) (live : ∃ i, c i ≠ 0) (dead : ∃ i, c i=0)
    (zero : (∑ i, (c i : ℂ)*(shellPower s (a i) : ℂ))=0) :
    ∃ l, l<k ∧ shellRelationLength s l := by
  classical
  let S := univ.filter (fun i => c i ≠ 0)
  obtain ⟨i,hi⟩ := live
  letI : Nonempty S := ⟨⟨i,mem_filter.mpr ⟨mem_univ i,hi⟩⟩⟩
  obtain ⟨j,hj⟩ := dead
  have missing : j ∉ S := fun hit => (mem_filter.mp hit).2 hj
  have sub : S ⊂ univ := Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,fun eq => missing (by rw [eq]; exact mem_univ j)⟩
  refine ⟨Fintype.card S,by simpa only [Fintype.card_coe,card_univ,Fintype.card_fin] using Finset.card_lt_card sub,
    relation_of_finite (fun i : S => a i.val) (fun i : S => c i.val) (inj.comp Subtype.val_injective)
      (fun i => (mem_filter.mp i.property).2) ?_⟩
  rw [sum_coe_sort S (fun i => (c i : ℂ)*(shellPower s (a i) : ℂ))]
  apply Eq.trans _ zero
  apply sum_subset (subset_univ _)
  intro i _ miss
  have gone : c i=0 := by by_contra nz; exact miss (mem_filter.mpr ⟨mem_univ i,nz⟩)
  rw [gone,Subalgebra.coe_zero,zero_mul]

#print axioms resonance_has_length
#print axioms reflected_length
#print axioms shorter_of_zero_coefficient

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
