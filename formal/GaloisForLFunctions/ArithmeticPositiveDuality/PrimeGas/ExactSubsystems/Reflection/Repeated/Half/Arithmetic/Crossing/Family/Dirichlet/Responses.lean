import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Gibbs
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Prescribe

/-! # Realization of centered thermal responses on integer shells -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Finset Real

/-- The additive group of logarithms of positive rational numbers. -/
def gaps : AddSubgroup ℝ where
  carrier := {x | ∃ a b : ℕ+, x=energy a-energy b}
  zero_mem' := ⟨1,1,(sub_self _).symm⟩
  add_mem' := by
    rintro _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    exact ⟨a*c,b*d,by rw [energy_mul,energy_mul]; ring⟩
  neg_mem' := by
    rintro _ ⟨a,b,rfl⟩
    exact ⟨b,a,neg_sub _ _⟩

theorem gap_mem (a b : ℕ+) : energy a-energy b ∈ gaps := ⟨a,b,rfl⟩

private theorem energy_mem (a : ℕ+) : energy a ∈ gaps :=
  ⟨a,1,by simp [energy]⟩

/-- Every state is an actual occurrence, so all realized multiplicities are positive integers. -/
def Realized (f : ℝ → ℝ) := ∃ (n : ℕ) (E : Fin n → ℝ),
  (∀ i, E i ∈ gaps) ∧ (∑ i, E i)=0 ∧ ∀ t, oddTrace E t=f t

private theorem pack {I : Type*} [Fintype I] {E : I → ℝ} {f : ℝ → ℝ}
    (hg : ∀ i, E i ∈ gaps) (hz : ∑ i, E i=0) (he : ∀ t, oddTrace E t=f t) : Realized f := by
  let e := (Fintype.equivFin I).symm
  exact ⟨_,E ∘ e,fun i => hg (e i),(Equiv.sum_comp e E).trans hz,
    fun t => (Equiv.sum_comp e (fun i => oddTerm t (E i))).trans (he t)⟩

/-- Direct sum adds responses. Reflecting a centered spectrum changes its response sign. -/
def responses : AddSubgroup (ℝ → ℝ) where
  carrier := {f | Realized f}
  zero_mem' := ⟨0,Fin.elim0,(fun i => i.elim0),by simp,fun _ => by simp [oddTrace]⟩
  add_mem' := by
    rintro _ _ ⟨_,a,ha,za,ea⟩ ⟨_,b,hb,zb,eb⟩
    refine pack (E := Sum.elim a b) (fun i => by cases i with | inl i => exact ha i | inr i => exact hb i) ?_ (fun t => ?_)
    · simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,za,zb,add_zero]
    · simpa only [oddTrace,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.add_apply] using
        congrArg₂ (·+·) (ea t) (eb t)
  neg_mem' := by
    rintro _ ⟨_,a,ha,za,ea⟩
    refine pack (E := fun i => -a i) (fun i => gaps.neg_mem (ha i))
      (by rw [sum_neg_distrib,za,neg_zero]) (fun t => ?_)
    have neg (x : ℝ) : oddTerm t (-x) = -oddTerm t x := by
      simp only [oddTerm,mul_neg,neg_mul,neg_neg,neg_sub]
    simpa only [oddTrace,neg,sum_neg_distrib,Pi.neg_apply] using congrArg Neg.neg (ea t)

def originTrace (t : ℝ) := Lattice.base (t * energy 2)

theorem origin_pos {t : ℝ} (ht : 0<t) : 0<originTrace t :=
  Lattice.base_pos (mul_pos ht (log_pos (by norm_num : (1 : ℝ)<2)))

theorem origin_mem : originTrace ∈ responses := by
  let x := energy 2
  have hx : x ∈ gaps := energy_mem 2
  let E : Fin 3 → ℝ := ![x+x,-x,-x]
  refine pack (E := E) ?_ ?_ (fun t => ?_)
  · intro i
    fin_cases i
    · exact gaps.add_mem hx hx
    · exact gaps.neg_mem hx
    · exact gaps.neg_mem hx
  · rw [Fin.sum_univ_three]
    change x+x+-x+-x=0
    ring
  · rw [oddTrace,Fin.sum_univ_three]
    change oddTerm t (x+x)+oddTerm t (-x)+oddTerm t (-x)=Lattice.base (t*x)
    simp only [oddTerm,Lattice.base,Lattice.coordinate,mul_add,mul_neg,neg_mul,neg_neg,exp_add]
    ring

/-- Tensoring by the two levels at ±x preserves centering and multiplies the
odd trace by the even two-state partition function. -/
theorem pair_mem {f : ℝ → ℝ} (hf : f ∈ responses) {x : ℝ} (hx : x ∈ gaps) :
    (fun t => (exp (t*x)+exp (-t*x))*f t) ∈ responses := by
  obtain ⟨n,E,hm,hz,he⟩ := hf
  let F : Fin n ⊕ Fin n → ℝ := Sum.elim (fun i => E i+x) (fun i => E i-x)
  refine pack (E := F) ?_ ?_ (fun t => ?_)
  · intro i
    cases i with
    | inl i => exact gaps.add_mem (hm i) hx
    | inr i => exact gaps.sub_mem (hm i) hx
  · simp only [F,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_add_distrib,sum_sub_distrib,hz,
      zero_add,zero_sub,add_neg_cancel]
  · have step (y : ℝ) : oddTerm t (y+x)+oddTerm t (y-x) =
        (exp (t*x)+exp (-t*x))*oddTerm t y := by
      simp only [oddTerm,sub_eq_add_neg,mul_add,mul_neg,neg_mul,neg_neg,exp_add]
      ring
    rw [← he t]
    simp only [F,oddTrace,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      mul_sum,← sum_add_distrib,step]

/-- A common denominator translates every rational log level to an integer
shell. Centering removes that translation even when levels coincide. -/
theorem integer_shells {f : ℝ → ℝ} (hf : f ∈ responses) :
    ∃ (n : ℕ) (a : Fin n → ℕ+), ∀ t, oddTrace (centered (energy ∘ a)) t=f t := by
  classical
  obtain ⟨n,E,hm,hz,he⟩ := hf
  choose a b hab using hm
  let other (i : Fin n) := ∏ j ∈ univ.erase i, b j
  let D := ∏ j, b j
  have translated : energy ∘ (fun i => a i * other i) = fun i => 1*E i+energy D := by
    funext i
    have de : energy D=energy (other i)+energy (b i) := by
      rw [← energy_mul]
      exact congrArg energy (prod_erase_mul univ b (mem_univ i)).symm
    simp only [Function.comp_apply,energy_mul,one_mul,hab i,de]
    ring
  refine ⟨n,fun i => a i*other i,fun t => ?_⟩
  rw [translated,centered_affine,centered_eq_of_sum_zero hz]
  simpa only [one_mul] using he t

#print axioms origin_mem
#print axioms pair_mem
#print axioms integer_shells

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
