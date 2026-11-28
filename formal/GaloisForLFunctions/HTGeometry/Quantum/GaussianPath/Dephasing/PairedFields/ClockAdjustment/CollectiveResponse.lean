import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.GaussianPair

/-! # Combining onsite field rotations coherently across the chain -/

open Finset
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
open SpectralEdge
noncomputable section

private abbrev Edge (n : ℕ) := Fin (n+1)

/-- Adjacent edges address distinct coefficients even at their shared site,
using axis zero on the left and axis one on the right. -/
private def probe {n : ℕ} : Edge n ⊕ Edge n → PathLabel n
  | .inl i => leftSite i 0
  | .inr i => rightSite i 1

private theorem probe_injective (n : ℕ) : Function.Injective (probe (n:=n)) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (Fin.castSucc_injective _ (congrArg Prod.fst (Sum.inl.inj h)))
    | inr j => exact False.elim ((by decide : (0:Fin 3)≠1) (congrArg Prod.snd (Sum.inl.inj h)))
  | inr i =>
    cases j with
    | inl j => exact False.elim ((by decide : (0:Fin 3)≠1) (congrArg Prod.snd (Sum.inl.inj h)).symm)
    | inr j => exact congrArg Sum.inr (Fin.succ_injective _ (congrArg Prod.fst (Sum.inl.inj h)))

private theorem retimed_test {n : ℕ} (h g : Coeff n) (hg : (∑ i, h i*g i)=0) (t φ : ℝ) :
    let E := (generator h).2.isHermitian.eigenvalues
    (∑ i, g i*squareTrace h i)^2 ≤ (∑ j, E j^4)*(∑ j, (localSlope h g j+t*E j+φ)^2) := by
  intro E
  have hret := optimal_retiming h g t φ
  dsimp only at hret
  simp only [hg,zero_div,zero_mul,sub_zero,add_zero] at hret
  have hres : (∑ j, localSlope h g j^2) ≤ ∑ j, (localSlope h g j+t*E j+φ)^2 := by
    rw [hret]
    exact le_add_of_nonneg_right (by positivity)
  have hm : (∑ j, E j^2*localSlope h g j)=∑ i, g i*squareTrace h i := by
    simp only [localSlope,squareTrace_eq_energy_sum,mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [←hm]
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun j => E j^2) (localSlope h g)
  simp_rw [show ∀ j, (E j^2)^2=E j^4 from fun j => by ring] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left hres (sum_nonneg fun j _ => by positivity))

/-- One physical tangent field, of squared norm at most the original coupling energy,
realizes the sum of absolute edge responses against the quadratic energy observable.
Every retiming and common phase retain its resulting mean-square lower bound. -/
theorem collective_field {n : ℕ} (h : Coeff n) :
    ∃ g : Coeff n, (∑ l, h l*g l)=0 ∧ (∑ l, g l^2) ≤ ∑ l, h l^2 ∧
      ∀ t φ : ℝ, let E := (generator h).2.isHermitian.eigenvalues
      (∑ e, |edgeResponse h e 0 1|)^2 ≤ (∑ j, E j^4)*(∑ j, (localSlope h g j+t*E j+φ)^2) := by
  classical
  let s (i : Edge n) : ℝ := if edgeResponse h i 0 1<0 then -1 else 1
  let c : Edge n ⊕ Edge n → ℝ := Sum.elim (fun i => -(s i*h (rightSite i 1))) (fun i => s i*h (leftSite i 0))
  let g (l : PathLabel n) := ∑ j, if probe j=l then c j else 0
  have hp := probe_injective n
  have hv (j : Edge n ⊕ Edge n) : g (probe j)=c j := by
    simp only [g,hp.eq_iff,sum_ite_eq',mem_univ,if_true]
  have hprod (f : Coeff n) : (∑ l, g l*f l)=∑ j, c j*f (probe j) := by
    simp only [g,sum_mul,ite_mul,zero_mul]
    rw [sum_comm]
    simp
  have hedge (f : Coeff n) : (∑ l, g l*f l) =
      ∑ i, s i*(h (leftSite i 0)*f (rightSite i 1)-h (rightSite i 1)*f (leftSite i 0)) := by
    rw [hprod,Fintype.sum_sum_type,←sum_add_distrib]
    exact sum_congr rfl fun i _ => by dsimp only [c,Sum.elim,probe]; ring
  have hperp : (∑ l, h l*g l)=0 := by
    simp_rw [mul_comm (h _) (g _)]
    rw [hedge]
    apply sum_eq_zero
    intro i _
    ring
  refine ⟨g,hperp,?_,?_⟩
  · have hs (i : Edge n) : s i^2=1 := by dsimp only [s]; split <;> norm_num
    have hnorm : (∑ l, g l^2)=∑ j : Edge n ⊕ Edge n, h (probe j)^2 := by
      calc
        _ = ∑ l, g l*g l := sum_congr rfl fun l _ => sq _
        _ = ∑ j, c j*g (probe j) := hprod g
        _ = ∑ j, c j^2 := sum_congr rfl fun j _ => by rw [hv,sq]
        _ = _ := by
          simp only [Fintype.sum_sum_type,c,Sum.elim_inl,Sum.elim_inr,probe,neg_sq,mul_pow,hs,one_mul]
          exact add_comm ..
    rw [hnorm,← sum_image (f:=fun l => h l^2) (s:=univ) (g:=probe (n:=n)) hp.injOn]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun l _ _ => sq_nonneg _
  · intro t φ
    have he (i : Edge n) : s i*edgeResponse h i 0 1=|edgeResponse h i 0 1| := by
      by_cases hh : edgeResponse h i 0 1<0
      · simp only [s,if_pos hh,abs_of_neg hh,neg_one_mul]
      · simp only [s,if_neg hh,abs_of_nonneg (le_of_not_gt hh),one_mul]
    have hm := hedge (squareTrace h)
    change (∑ l, g l*squareTrace h l)=∑ i, s i*edgeResponse h i 0 1 at hm
    simp only [he] at hm
    rw [←hm]
    exact retimed_test h g hperp t φ

#print axioms collective_field
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
