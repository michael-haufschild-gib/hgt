import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Schedule.Kernel
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Flow

/-! # Prescribing the signs of finitely many centered thermal readings -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Schedule

open Finset Real Set Filter Topology

variable {q p : ℕ}

private abbrev Carrier (q p : ℕ) := (Fin q ⊕ Fin q) ⊕ (Unit ⊕ Fin p)

private def base (x : Fin q → ℝ) : Carrier q p → ℝ
  | .inl (.inl i) => x i
  | .inl (.inr i) => -x i
  | .inr _ => 0

private def speed (v : Fin q → ℝ) : Carrier q p → ℝ
  | .inl (.inl i) | .inl (.inr i) => v i
  | .inr (.inl _) => -2*∑ i, v i
  | .inr (.inr _) => 0

private def levels (x v : Fin q → ℝ) (u : ℝ) (i : Carrier q p) := base x i+u*speed v i

private theorem centered_levels (x v : Fin q → ℝ) (u : ℝ) :
    (∑ i : Carrier q p, levels x v u i)=0 := by
  simp only [levels,base,speed,Fintype.sum_sum_type,Fintype.sum_unique,sum_add_distrib,
    sum_neg_distrib,← mul_sum,add_zero,sum_const_zero]
  ring

private theorem odd_initial (x v : Fin q → ℝ) (t : ℝ) :
    oddTrace (levels (p := p) x v 0) t=0 := by
  simp [oddTrace,oddTerm,levels,base,Fintype.sum_sum_type,sum_sub_distrib,mul_neg,neg_mul]
  ring

private theorem slope (t x v : ℝ) :
    HasDerivAt (fun u : ℝ => oddTerm t (x+u*v)) (2*t*cosh (t*x)*v) 0 := by
  have step : HasDerivAt (fun u : ℝ => x+u*v) v 0 := by
    simpa only [Pi.add_def,id_eq,one_mul,zero_add] using (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).mul_const v)
  have h := ((step.const_mul t).exp).sub ((step.const_mul (-t)).exp)
  simp only [zero_mul,add_zero] at h
  apply h.congr_deriv
  rw [cosh_eq,neg_mul]
  ring

private theorem reading_deriv (x v : Fin q → ℝ) (t : ℝ) :
    HasDerivAt (fun u => oddTrace (levels (p := p) x v u) t)
      (4*t*∑ i, (cosh (t*x i)-1)*v i) 0 := by
  have h := HasDerivAt.fun_sum (u := univ) (fun (i : Carrier q p) _ => slope t (base x i) (speed v i))
  apply h.congr_deriv
  simp only [Fintype.sum_sum_type,base,speed,mul_neg,cosh_neg,mul_zero,cosh_zero,
    Fintype.sum_unique,sum_const_zero,add_zero,sub_mul,one_mul,sum_sub_distrib,mul_assoc,← mul_sum]
  ring

private theorem sign_near {f : ℝ → ℝ} {b : ℝ} (hf : HasDerivAt f b 0) (zero : f 0=0) (hb : b≠0) :
    ∀ᶠ u in 𝓝[>] (0 : ℝ), 0<b*f u := by
  have lim := hf.tendsto_slope_zero_right
  have h : Tendsto (fun u : ℝ => b*(u⁻¹*f u)) (𝓝[>] 0) (𝓝 (b*b)) := by
    simpa only [zero_add,zero,sub_zero,smul_eq_mul] using (tendsto_const_nhds (x := b)).mul lim
  filter_upwards [h.eventually (eventually_gt_nhds (mul_self_pos.mpr hb)),self_mem_nhdsWithin] with u hu pos
  have product : 0<(b*f u)*u⁻¹ := by simpa only [mul_left_comm,mul_assoc,mul_comm] using hu
  exact pos_of_mul_pos_left product (inv_nonneg.mpr (show 0<u from pos).le)

/-- On any positive ordered schedule, a centered real spectrum of size \(2q+1\)
or larger realizes every prescribed strict sign pattern. -/
theorem signs_on_real_spectrum {n : ℕ} (dim : 2*q+1≤n) (t : Fin q ↪o Ioi (0 : ℝ))
    (b : Fin q → ℝ) (nonzero : ∀ j, b j≠0) :
    ∃ E : Fin n → ℝ, (∑ i, E i)=0 ∧ ∀ j, 0<b j*oddTrace E (t j).val := by
  let x : Fin q ↪o Ioi (0 : ℝ) := OrderEmbedding.ofStrictMono
    (fun i : Fin q => (⟨(i.val : ℝ)+1,show (0 : ℝ) < _ by positivity⟩ : Ioi (0 : ℝ))) (by
      intro i j h
      change (i.val : ℝ)+1 < (j.val : ℝ)+1
      have hval : (i.val : ℝ)<(j.val : ℝ) := Nat.cast_lt.mpr (show i.val<j.val from h)
      linarith only [hval])
  obtain ⟨v,hv⟩ := choose_velocity t x b
  let p := n-(2*q+1)
  let E := levels (p := p) (fun i => (x i).val) v
  have near : ∀ᶠ u in 𝓝[>] (0 : ℝ), ∀ j, 0<b j*oddTrace (E u) (t j).val := by
    apply Filter.eventually_all.mpr
    intro j
    exact sign_near ((reading_deriv (p := p) _ v (t j).val).congr_deriv (hv j))
      (odd_initial _ v _) (nonzero j)
  obtain ⟨u,hu⟩ := near.exists
  have size : Fintype.card (Carrier q p)=n := by
    simp only [Carrier,Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]; unfold p; omega
  let e := Fintype.equivFinOfCardEq size
  refine ⟨fun i => E u (e.symm i),(Equiv.sum_comp e.symm (E u)).trans (centered_levels _ _ _),fun j => ?_⟩
  have eq := Equiv.sum_comp e.symm (fun i => oddTerm (t j).val (E u i))
  change 0 < b j * (∑ i, oddTerm (t j).val (E u (e.symm i)))
  rw [eq]
  exact hu j

#print axioms signs_on_real_spectrum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Schedule
