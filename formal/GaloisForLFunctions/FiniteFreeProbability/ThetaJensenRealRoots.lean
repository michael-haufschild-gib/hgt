import GaloisForLFunctions.FiniteFreeProbability.GammaThetaSzegoFactorization
import GaloisForLFunctions.HTGeometry.LaguerreShiftRealRootCount

/-!
# Real roots of the theta factor of Xi's Jensen polynomials

Qi's positive-moment argument (arXiv:2611.11194, §4) applies to the raw theta
moments on the half-line. Binomial summation turns the Jensen factor into an
integral of a single power. Even powers have positive integral, including at
negative arguments. The derivative ladder then gives exactly one simple real
root in every odd degree. Pascal's identity orders those roots by moment shift.
-/

open Polynomial Finset MeasureTheory Filter
open GaloisForLFunctions.SignAlternation RHTower RHTower.DeBruijn

namespace FiniteFreeProbability

noncomputable section

local notation "Θ" => jensenPoly thetaCuspRawEvenMoment

private def kernelPower (n d : ℕ) (x t : ℝ) : ℝ :=
  t ^ (2 * n) * riemannKernelReal t * (x * t ^ 2 + 1) ^ d

private theorem kernelPower_expand (n d : ℕ) (x t : ℝ) :
    kernelPower n d x t = ∑ j ∈ range (d + 1),
      ((d.choose j : ℝ) * x ^ j) * (t ^ (2 * (n + j)) * riemannKernelReal t) := by
  rw [kernelPower, add_pow, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp only [one_pow, mul_one, mul_pow]; ring

private theorem kernelPower_integrable (n d : ℕ) (x : ℝ) :
    Integrable (kernelPower n d x) := by
  simp_rw [show kernelPower n d x = fun t => ∑ j ∈ range (d + 1),
      ((d.choose j : ℝ) * x ^ j) * (t ^ (2 * (n + j)) * riemannKernelReal t) from
    funext (kernelPower_expand n d x)]
  exact integrable_finsetSum _ fun j _ => (integrable_pow_mul_riemannKernel _).const_mul _

/-- Binomial resummation of the theta moment factor, valid at every real argument. -/
theorem thetaJensen_eval_integral (n d : ℕ) (x : ℝ) :
    (Θ d n).eval x = ∫ t, t ^ (2 * n) * riemannKernelReal t * (x * t ^ 2 + 1) ^ d := by
  change _ = ∫ t, kernelPower n d x t
  simp_rw [kernelPower_expand]
  rw [integral_finsetSum _ fun j _ => (integrable_pow_mul_riemannKernel _).const_mul _]
  simp only [jensenPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, integral_const_mul,
    ← thetaCuspRawEvenMoment_eq_integral]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Even-degree theta factors are strictly positive on the whole real axis. -/
theorem thetaJensen_even_pos (n k : ℕ) (x : ℝ) : 0 < (Θ (2*k) n).eval x := by
  let f := kernelPower n (2*k) x
  have hf : Continuous f := by
    exact ((continuous_pow _).mul riemannKernel_superExp.continuous).mul (by fun_prop)
  have h₀ : ∀ t, 0 ≤ f t := fun t => mul_nonneg
    (mul_nonneg ((even_two_mul n).pow_nonneg _) (riemannKernel_superExp.nonneg t))
    ((even_two_mul k).pow_nonneg _)
  obtain ⟨u, hu, hxu⟩ : ∃ u : ℝ, 0 < u ∧ x * u ^ 2 + 1 ≠ 0 := by
    by_cases h : x = -1
    · exact ⟨2, by norm_num, by norm_num [h]⟩
    · exact ⟨1, zero_lt_one, by simpa using (show x + 1 ≠ 0 by grind)⟩
  have hfu : 0 < f u := mul_pos (mul_pos (pow_pos hu _) (riemannKernelReal_pos u))
    (lt_of_le_of_ne ((even_two_mul k).pow_nonneg _) (pow_ne_zero _ hxu).symm)
  have hlocal : 0 < ∫ t in (u-1)..(u+1), f t :=
    intervalIntegral_pos_of_continuous_global_nonneg hf h₀
      ⟨u, by constructor <;> linarith, hfu⟩
  rw [intervalIntegral.integral_of_le (by linarith)] at hlocal
  rw [thetaJensen_eval_integral]
  exact hlocal.trans_le (setIntegral_le_integral (kernelPower_integrable n (2*k) x)
    (Eventually.of_forall h₀))

/-- The true degree survives moment averaging, even at shift zero. -/
theorem thetaJensen_natDegree (n d : ℕ) : (Θ d n).natDegree = d := by
  refine (natDegree_jensenPoly_le _ _ _).antisymm (le_natDegree_of_ne_zero ?_)
  rw [jensenPoly, coeff_sum_range_C_mul_X_pow _ le_rfl, Nat.choose_self]
  simpa using (thetaCuspRawEvenMoment_pos (n + d)).ne'

/-- The odd derivative is positive everywhere, including at the odd root. -/
theorem thetaJensen_odd_derivative_pos (n k : ℕ) (x : ℝ) :
    0 < ((Θ (2*k+1) n).derivative).eval x := by
  rw [derivative_jensenPoly, eval_mul, eval_C]
  exact mul_pos (by positivity) (thetaJensen_even_pos _ _ _)

theorem thetaJensen_odd_strictMono (n k : ℕ) : StrictMono (Θ (2*k+1) n).eval := by
  apply strictMono_of_deriv_pos
  intro x
  rw [Polynomial.deriv]
  exact thetaJensen_odd_derivative_pos n k x

/-- Exactly one real root survives in odd degree. -/
theorem thetaJensen_odd_existsUnique_root (n k : ℕ) : ∃! x : ℝ, (Θ (2*k+1) n).IsRoot x := by
  obtain ⟨u, hu⟩ := GaloisForLFunctions.HTGeometry.card_roots_add_two_mul_eq_natDegree
    (Θ (2*k+1) n)
  rw [thetaJensen_natDegree] at hu
  obtain ⟨r, hr'⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < (Θ (2*k+1) n).roots.card by omega)
  have hr := (Polynomial.isRoot_of_mem_roots hr')
  exact ⟨r, hr, fun _ h => (thetaJensen_odd_strictMono n k).injective (h.trans hr.symm)⟩

/-- The unique real zero in degree `2k+1` at moment shift `n`. -/
def thetaOddRoot (n k : ℕ) : ℝ := (thetaJensen_odd_existsUnique_root n k).exists.choose

theorem thetaOddRoot_spec (n k : ℕ) : (Θ (2*k+1) n).eval (thetaOddRoot n k) = 0 :=
  (thetaJensen_odd_existsUnique_root n k).exists.choose_spec

theorem thetaOddRoot_neg (n k : ℕ) : thetaOddRoot n k < 0 := by
  apply (thetaJensen_odd_strictMono n k).lt_iff_lt.mp
  rw [thetaOddRoot_spec, thetaJensen_eval_integral]
  simpa only [zero_mul, zero_add, one_pow, mul_one, ← thetaCuspRawEvenMoment_eq_integral] using
    (thetaCuspRawEvenMoment_pos n)

/-- Raising the degree couples two adjacent shifts through Pascal's identity. -/
theorem thetaJensen_eval_succ (n d : ℕ) (x : ℝ) :
    (Θ (d+1) n).eval x = (Θ d n).eval x + x * (Θ d (n+1)).eval x := by
  simp_rw [thetaJensen_eval_integral]
  change ∫ t, kernelPower n (d+1) x t = _
  rw [show (∫ t, kernelPower n (d+1) x t) =
    ∫ t, kernelPower n d x t + x * kernelPower (n+1) d x t by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by simp only [kernelPower, pow_succ]; ring]
  rw [integral_add (kernelPower_integrable n d x) ((kernelPower_integrable (n+1) d x).const_mul _),
    integral_const_mul]
  rfl

/-- Size bias moves the unique odd zero strictly towards the origin at every shift. -/
theorem thetaOddRoot_strictMono (k : ℕ) : StrictMono (fun n => thetaOddRoot n k) := by
  apply strictMono_nat_of_lt_succ
  intro n
  apply (thetaJensen_odd_strictMono (n+1) k).lt_iff_lt.mp
  rw [thetaOddRoot_spec]
  have h := thetaJensen_even_pos n (k+1) (thetaOddRoot n k)
  rw [show 2*(k+1) = 2*k+1+1 by omega, thetaJensen_eval_succ, thetaOddRoot_spec, zero_add] at h
  exact ((mul_pos_iff.mp h).resolve_left fun hp => (thetaOddRoot_neg n k).not_gt hp.1).2

/-- The odd real root has multiplicity one. -/
theorem thetaOddRoot_multiplicity (n k : ℕ) :
    (Θ (2*k+1) n).rootMultiplicity (thetaOddRoot n k) = 1 := by
  have hp : Θ (2*k+1) n ≠ 0 := by
    intro h
    have hd := thetaJensen_natDegree n (2*k+1)
    rw [h, natDegree_zero] at hd
    omega
  have hr : (Θ (2*k+1) n).IsRoot (thetaOddRoot n k) := thetaOddRoot_spec n k
  have hpos := (Polynomial.rootMultiplicity_pos hp).2 hr
  have hle : ¬ 1 < (Θ (2*k+1) n).rootMultiplicity (thetaOddRoot n k) := by
    intro h
    exact (thetaJensen_odd_derivative_pos n k _).ne'
      ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).1 h).2
  omega

/-- All real roots with multiplicity, in both parities. -/
theorem thetaJensen_real_roots (n d : ℕ) :
    (Θ d n).roots = if Even d then 0 else {thetaOddRoot n (d/2)} := by
  classical
  rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show d = 2*k by omega, if_pos (even_two_mul k)]
    exact Multiset.eq_zero_of_forall_notMem fun x hx =>
      (thetaJensen_even_pos n k x).ne' (Polynomial.isRoot_of_mem_roots hx)
  · rw [hk, if_neg (show Odd (2*k+1) from ⟨k, rfl⟩).not_even, show (2*k+1)/2 = k by omega]
    ext x
    by_cases hx : x = thetaOddRoot n k
    · subst x
      simp [count_roots, thetaOddRoot_multiplicity]
    · have hnot : x ∉ (Θ (2*k+1) n).roots := by
        intro hm
        exact hx ((thetaJensen_odd_strictMono n k).injective
          ((Polynomial.isRoot_of_mem_roots hm).trans (thetaOddRoot_spec n k).symm))
      simp [Multiset.count_eq_zero_of_notMem hnot, hx]

/-- Exactly half the degree rounded down lies in each open complex half-plane. -/
theorem thetaJensen_upper_root_count (n d : ℕ) :
    (RiemannGaussian.realPolynomialUpperRootMultiset (Θ d n)).card = d/2 := by
  have h := RiemannGaussian.realPolynomial_realRoot_card_add_two_mul_upperRoot_card (Θ d n)
  rw [GaloisForLFunctions.HTGeometry.realPolynomialRealRootMultiset_eq_map_roots,
    Multiset.card_map, thetaJensen_real_roots, thetaJensen_natDegree] at h
  split at h <;> simp only [Multiset.card_zero, Multiset.card_singleton] at h <;> omega

#print axioms thetaJensen_upper_root_count
#print axioms thetaOddRoot_strictMono

end

end FiniteFreeProbability
