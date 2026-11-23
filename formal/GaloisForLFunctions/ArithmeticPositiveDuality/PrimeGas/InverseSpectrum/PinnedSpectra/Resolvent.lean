import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Mixture

/-! # The Stieltjes transform of the physical prefix construction -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Polynomial Lagrange

private theorem cauchy_residue_sum {m : ℕ} (a : Fin (m+1) → ℝ) (ha : Function.Injective a) (b : Fin m → ℝ)
    (x : ℝ) (hx : ∀ i, x ≠ a i) :
    ∑ i, residueMass a b i/(x-a i) = (∏ j, (x-b j))/∏ i, (x-a i) := by
  let P := nodal univ b
  have hd : P.degree < ↑(univ : Finset (Fin (m+1))).card := by
    simp only [P,degree_nodal,card_univ,Fintype.card_fin]
    exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self m)
  have hi := eq_interpolate (s := univ) ha.injOn hd
  have he := eval_interpolate_not_at_node (s := univ) (v := a) (fun i => P.eval (a i)) (fun i _ => hx i)
  rw [← hi] at he
  have hterm (i : Fin (m+1)) : nodalWeight univ a i*(x-a i)⁻¹*P.eval (a i) = residueMass a b i/(x-a i) := by
    simp only [P,nodalWeight_eq_eval_nodal_erase_inv,eval_nodal,residueMass,div_eq_mul_inv]
    ring
  simp only [hterm,P,eval_nodal] at he
  apply (eq_div_iff (prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hx i)))).mpr
  exact (mul_comm _ _).trans he.symm

private theorem residue_reflect {m : ℕ} (a : Fin (m+1) → ℝ) (b : Fin m → ℝ) (i : Fin (m+1)) :
    residueMass (fun j => -a j) (fun j => -b j) i = residueMass a b i := by
  have hn (u v : ℝ) : -u- -v = (-1)*(u-v) := by ring
  simp only [residueMass,hn,prod_mul_distrib,prod_const,card_univ,card_erase_of_mem (mem_univ i),Fintype.card_fin,Nat.add_sub_cancel]
  exact mul_div_mul_left _ _ (pow_ne_zero m (by norm_num : (-1:ℝ) ≠ 0))

def prefixProduct {m : ℕ} (b : PrefixData m) (x : ℝ) := ∏ j, (x+(b j).val)/(x+occupationWeight j.val)

theorem prefixProduct_pos {m : ℕ} (b : PrefixData m) {x : ℝ} (hx : 0 < x) : 0 < prefixProduct b x :=
  prod_pos fun j _ => div_pos (add_pos hx ((occupationWeight_pos _).trans_le (b j).property.1)) (add_pos hx (occupationWeight_pos _))

/-- The whole finite prefix enters the transform only through its ratio of characteristic products. -/
theorem mixture_stieltjes {m : ℕ} (b : PrefixData m) {x : ℝ} (hx : 0 < x) :
    (∑' n, prefixProbability b n/(x+occupationWeight n)) =
      prefixProduct b x * ∑' k, tailLaw k/(x+occupationWeight (m+k)) := by
  let f (n : ℕ) := (x+occupationWeight n)⁻¹
  have hf (n : ℕ) : |f n| ≤ x⁻¹ := by
    change |(x+occupationWeight n)⁻¹| ≤ x⁻¹
    rw [abs_of_pos (inv_pos.mpr (add_pos hx (occupationWeight_pos n)))]
    exact inv_anti₀ hx (le_add_of_nonneg_right (occupationWeight_pos n).le)
  have he (k : ℕ) : (∑ i, nodeResidue b k i*f (nodeIndex m k i)) = prefixProduct b x/(x+occupationWeight (m+k)) := by
    let a := nativeNode m k
    have hne (i : Fin (m+1)) : x ≠ -a i := (neg_lt_zero.mpr (occupationWeight_pos (nodeIndex m k i))).trans hx |>.ne'
    have h := cauchy_residue_sum (fun i => -a i) (neg_injective.comp (nativeNode_anti m k).injective) (fun j => -(b j).val) x hne
    simp only [residue_reflect,sub_neg_eq_add] at h
    change (∑ i, residueMass a (fun j => (b j).val) i*(x+a i)⁻¹) = _
    simp_rw [← div_eq_mul_inv]
    rw [h,Fin.prod_univ_castSucc (fun i => x+a i),prefixProduct,prod_div_distrib,div_div]
    simp only [a,nativeNode,nodeIndex_head,nodeIndex_last]
  have h := mixture_reading b f x⁻¹ hf
  change (∑' n, prefixProbability b n*(x+occupationWeight n)⁻¹) = _ at h
  simp only [div_eq_mul_inv] at he ⊢
  rw [h,← tsum_mul_left]
  exact tsum_congr fun k => by rw [he k]; ring

#print axioms mixture_stieltjes

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
