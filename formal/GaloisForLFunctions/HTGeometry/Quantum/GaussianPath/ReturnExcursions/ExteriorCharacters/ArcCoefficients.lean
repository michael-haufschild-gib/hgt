import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Tactic

/-! # Coefficients of a polynomial with all roots in a right half-plane -/

open Polynomial Set
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
noncomputable section

private theorem root_halfPlane (P : ℂ[X]) (c : ℝ) (h : P.rootSet ℂ ⊆ {z | c≤z.re})
    (k : ℕ) : (derivative^[k] P).rootSet ℂ ⊆ {z | c≤z.re} := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    let Q := derivative^[k] P
    by_cases hQ : 0<Q.degree
    · exact (rootSet_derivative_subset_convexHull_rootSet hQ).trans
        (convexHull_min ih (convex_halfSpace_ge Complex.reCLM.toLinearMap.isLinear c))
    · have hd : Q.natDegree=0 := Nat.eq_zero_of_not_pos fun h => hQ (natDegree_pos_iff_degree_pos.mp h)
      change Q.derivative.rootSet ℂ ⊆ _
      rw [derivative_of_natDegree_zero hd]
      simp

private theorem roots_prod_floor {c : ℝ} (hc : 0≤c) (s : Multiset ℂ)
    (h : ∀ z∈s, c≤‖z‖) : c^s.card≤‖s.prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    rw [Multiset.card_cons,Multiset.prod_cons,norm_mul,pow_succ]
    rw [mul_comm (c^s.card)]
    exact mul_le_mul (h z (Multiset.mem_cons_self _ _))
      (ih fun w hw => h w (Multiset.mem_cons_of_mem hw)) (pow_nonneg hc _) (norm_nonneg _)

private theorem constant_floor (P : ℂ[X]) {c : ℝ} (hc : 0≤c)
    (h : P.rootSet ℂ ⊆ {z | c≤z.re}) :
    ‖P.leadingCoeff‖*c^P.natDegree≤‖P.coeff 0‖ := by
  by_cases hp : P=0
  · simp [hp]
  have hs := IsAlgClosed.splits P
  have hh : ∀ z∈P.roots, c≤‖z‖ := by
    intro z hz
    have hroot : z∈P.rootSet ℂ := mem_rootSet.mpr ⟨hp,by
      simpa only [coe_aeval_eq_eval] using ((mem_roots hp).mp hz).eq_zero⟩
    exact (h hroot).trans (Complex.re_le_norm _)
  rw [hs.coeff_zero_eq_leadingCoeff_mul_prod_roots,norm_mul,norm_mul,norm_pow,
    norm_neg,norm_one,one_pow,one_mul,hs.natDegree_eq_card_roots]
  exact mul_le_mul_of_nonneg_left (roots_prod_floor hc _ hh) (norm_nonneg _)

/-- All coefficient orders obey the same half-plane bound. Gauss–Lucas
applied to the normalized derivative bounds its constant coefficient by
the product of the real-part lower bounds for its roots. -/
theorem coefficient_floor (P : ℂ[X]) {c : ℝ} (hc : 0≤c)
    (h : P.rootSet ℂ ⊆ {z | c≤z.re}) (j : ℕ) (hj : j≤P.natDegree) :
    (P.natDegree.choose j:ℝ)*‖P.leadingCoeff‖*c^(P.natDegree-j)≤‖P.coeff j‖ := by
  let Q := hasseDeriv j P
  have hd : Q.natDegree=P.natDegree-j := natDegree_hasseDeriv P j
  have hscale : j.factorial • Q=derivative^[j] P := congrFun (factorial_smul_hasseDeriv (R:=ℂ) j) P
  have hQ : Q.rootSet ℂ ⊆ {z | c≤z.re} := by
    intro z hz
    apply root_halfPlane P c h j
    rw [←hscale,mem_rootSet]
    obtain ⟨hn,he⟩ := mem_rootSet.mp hz
    refine ⟨?_,by simp only [map_nsmul,he,nsmul_zero]⟩
    rw [nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) hn
  have hlc : Q.leadingCoeff=(P.natDegree.choose j:ℂ)*P.leadingCoeff := by
    rw [←coeff_natDegree,hd,show Q=hasseDeriv j P from rfl,hasseDeriv_coeff,Nat.sub_add_cancel hj,
      coeff_natDegree]
  have hzero : Q.coeff 0=P.coeff j := by simp [Q,hasseDeriv_coeff]
  have hh := constant_floor Q hc hQ
  rwa [hd,hlc,hzero,norm_mul,Complex.norm_natCast] at hh

#print axioms coefficient_floor
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
