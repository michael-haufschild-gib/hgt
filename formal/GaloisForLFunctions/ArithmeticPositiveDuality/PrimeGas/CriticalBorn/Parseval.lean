import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Fourier
import GaloisForLFunctions.RHTower.Sieve.DirichletExpansion

/-! # Recovering the finite gas norm from elementary clock readings -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset Real
open scoped Topology

private def average (N : ℕ) : (ℕ → ℂ) →ₗ[ℂ] ℂ :=
  (mass N : ℂ)⁻¹ • ∑ p ∈ primes N, (weight p : ℂ) • LinearMap.proj p

private theorem average_apply (N : ℕ) (f : ℕ → ℂ) :
    average N f = (∑ p ∈ primes N, (weight p : ℂ)*f p)/(mass N : ℂ) := by
  simp only [average,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.proj_apply,
    smul_eq_mul,div_eq_inv_mul]

private def gap {M : ℕ} (m n : Fin M) := log ((m.val:ℝ)+1)-log ((n.val:ℝ)+1)

/-- Harmonic prime clocks separate every pair of different energy shells. -/
private theorem gap_limit {M : ℕ} (m n : Fin M) :
    Tendsto (fun N => average N (fun p => (phase (gap m n) p : ℂ))) atTop
      (𝓝 (if m=n then 1 else 0)) := by
  have hm (N : ℕ) : average N (fun p => (phase (gap m n) p : ℂ)) = coefficient (gap m n) (-1) N := by
    simp only [average_apply,coefficient,neg_neg,zpow_one]
  simp only [hm]
  split_ifs with eq
  · subst n
    simp only [gap,sub_self,zero_height_coefficient]
    exact tendsto_const_nhds
  · exact nonzero_mode _ (sub_ne_zero.mpr (_root_.RHTower.Sieve.log_succ_injective
      (fun he => eq (Fin.ext he)))) _ (by norm_num)

/-- Limit of the measured square of a coherent occupation preparation.
Coefficients indexed by Fin M correspond to the positive labels 1 through M. -/
theorem preparation_mean_square {M : ℕ} (a : Fin M → ℂ) :
    Tendsto (fun N => (∑ p ∈ primes N, weight p*
      ‖_root_.RHTower.Sieve.dirPoly M a (-log p)‖^2)/mass N) atTop (𝓝 (∑ n, ‖a n‖^2)) := by
  let z (m n : Fin M) := a m*(starRingEnd ℂ) (a n)
  have square : (fun p : ℕ => ((‖_root_.RHTower.Sieve.dirPoly M a (-log p)‖^2 : ℝ):ℂ)) =
      ∑ m, ∑ n, z m n • (fun p => (phase (gap m n) p : ℂ)) := by
    funext p
    simp only [_root_.RHTower.Sieve.normSq_dirPoly_eq,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      z,gap,phase,Circle.coe_exp,neg_mul,mul_comm (log p) (_-_)]
  have diag (m : Fin M) : (∑ n, z m n*(if m=n then (1:ℂ) else 0)) = ((‖a m‖^2 : ℝ):ℂ) := by
    simp only [mul_ite,mul_one,mul_zero,sum_ite_eq,mem_univ,if_true,z]
    rw [mul_comm,_root_.RHTower.Sieve.conj_mul_self]
  have hc := tendsto_finsetSum univ (fun (m : Fin M) _ => tendsto_finsetSum univ
    (fun (n : Fin M) _ => (gap_limit m n).const_mul (z m n)))
  simp only [diag] at hc
  have complexLimit : Tendsto (fun N => average N
      (fun p => ((‖_root_.RHTower.Sieve.dirPoly M a (-log p)‖^2 : ℝ):ℂ))) atTop
      (𝓝 (∑ n, ((‖a n‖^2 : ℝ):ℂ))) := by
    simp only [square,map_sum,map_smul,smul_eq_mul]
    exact hc
  have realLimit := Complex.continuous_re.continuousAt.tendsto.comp complexLimit
  simpa only [Function.comp_def,average_apply,Complex.div_ofReal_re,Complex.re_sum,
    ←Complex.ofReal_mul,Complex.ofReal_re] using realLimit

#print axioms preparation_mean_square

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
