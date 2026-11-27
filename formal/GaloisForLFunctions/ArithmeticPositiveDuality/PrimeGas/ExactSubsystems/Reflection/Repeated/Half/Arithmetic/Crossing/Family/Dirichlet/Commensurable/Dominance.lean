import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Certificate

/-! # Uniform separation of a finite exponential relation from all complex phases -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Finset Real Filter Topology

/-- At large positive order the largest distinct energy dominates even when
each summand is given an independent complex phase. -/
theorem dominant_shell {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ)
    (inj : Function.Injective E) (c : ι → ℤ) (live : ∀ i, c i ≠ 0) :
    ∃ C : ℝ, ∀ r ≥ C, ∀ z : ι → ℂ, (∀ i, ‖z i‖=exp (r*E i)) →
      ∑ i, (c i : ℂ)*z i ≠ 0 := by
  classical
  obtain ⟨k,_,top⟩ := exists_max_image univ E univ_nonempty
  let S := univ.erase k
  let w (i : ι) := ‖(c i : ℂ)‖
  have wk : 0<w k := norm_pos_iff.mpr (by exact_mod_cast live k)
  have decay (i : ι) (hi : i ∈ S) : Tendsto
      (fun r : ℝ => w i*exp (r*(E i-E k))) atTop (𝓝 0) := by
    have lt := lt_of_le_of_ne (top i (mem_univ i)) (fun eq => (mem_erase.mp hi).1 (inj eq))
    have lim := tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (sub_neg.mpr lt))
    simpa only [mul_zero,Function.comp_apply,id_eq] using lim.const_mul (w i)
  have lim : Tendsto (fun r : ℝ => ∑ i ∈ S, w i*exp (r*(E i-E k))) atTop (𝓝 0) := by
    simpa only [sum_const_zero] using tendsto_finsetSum S decay
  obtain ⟨C,hC⟩ := eventually_atTop.mp (lim.eventually_lt_const wk)
  refine ⟨C,fun r hr z hz zero => ?_⟩
  let v (i : ι) := (c i : ℂ)*z i
  have whole : (∑ i ∈ S, v i)+v k=0 := (sum_erase_add univ v (mem_univ k)).trans zero
  have rem : v k= -(∑ i ∈ S, v i) := by linear_combination whole
  have normv (i : ι) : ‖v i‖=w i*exp (r*E i) := by simp only [v,w,norm_mul,hz]
  have triangle : w k*exp (r*E k) ≤ ∑ i ∈ S, w i*exp (r*E i) := by
    calc _ = ‖v k‖ := (normv k).symm
         _ = ‖∑ i ∈ S, v i‖ := by rw [rem,norm_neg]
         _ ≤ ∑ i ∈ S, ‖v i‖ := norm_sum_le _ _
         _ = _ := sum_congr rfl fun i _ => normv i
  have scale (i : ι) : w i*exp (r*E i)*exp (-(r*E k))=w i*exp (r*(E i-E k)) := by
    rw [mul_assoc,← exp_add,mul_sub,sub_eq_add_neg]
  have bound := mul_le_mul_of_nonneg_right triangle (exp_pos (-(r*E k))).le
  rw [sum_mul,scale k,sub_self,mul_zero,exp_zero,mul_one] at bound
  exact (hC r hr).not_ge (by simpa only [scale] using bound)

/-- A vanishing sum with the prescribed moduli lies in one bounded interval
of logarithmic radii, uniformly over both choices of direction and all phases. -/
theorem radial_bound {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ)
    (inj : Function.Injective E) (c : ι → ℤ) (live : ∀ i, c i ≠ 0) :
    ∃ C : ℝ, 0<C ∧ ∀ (r : ℝ) (z : ι → ℂ), (∀ i, ‖z i‖=exp (r*E i)) →
      (∑ i, (c i : ℂ)*z i)=0 → |r|<C := by
  obtain ⟨A,hi⟩ := dominant_shell E inj c live
  obtain ⟨B,lo⟩ := dominant_shell (fun i => -E i) (neg_injective.comp inj) c live
  refine ⟨max 1 (max A B),lt_of_lt_of_le zero_lt_one (le_max_left _ _),fun r z hz zero => ?_⟩
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr]
    exact lt_of_lt_of_le (lt_of_not_ge (fun h => hi r h z hz zero)) ((le_max_left A B).trans (le_max_right _ _))
  · rw [abs_of_nonpos hr]
    have neg (i : ι) : ‖z i‖=exp ((-r)*(-E i)) := by rw [neg_mul_neg]; exact hz i
    exact lt_of_lt_of_le (lt_of_not_ge (fun h => lo (-r) h z neg zero)) ((le_max_right A B).trans (le_max_right _ _))

#print axioms radial_bound
#print axioms dominant_shell

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
