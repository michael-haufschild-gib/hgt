import GaloisForLFunctions.HTGeometry.CauchyKernelResidue
import GaloisForLFunctions.HTGeometry.SimplePoleResidueValue
import GaloisForLFunctions.Hurwitz.ExpIndependence
import GaloisForLFunctions.RHTower.ResidueModeMultiplicityBlock

/-!
# Higher-pole exponential residue modes

This file extracts the order-one Laurent coefficient after multiplying an arbitrary finite
principal part by `exp(-i*s*u)`.  The result is the common exponential `exp(-i*rho*u)` times an
explicit polynomial of degree at most one less than pole order.  A nonzero leading Laurent
coefficient makes the top polynomial coefficient nonzero and forces exact full block rank.
-/

namespace RHTower

open Complex Filter Topology Polynomial
open scoped BigOperators

noncomputable section

/-- Residue of an analytic numerator divided by an arbitrary positive coordinate power. -/
theorem laurentCoeff_inv_pow_mul_analytic {A : ℂ → ℂ} {rho : ℂ}
    (hA : AnalyticAt ℂ A rho) {m : ℕ} (hm : 1 ≤ m) :
    GaloisForLFunctions.HTGeometry.laurentCoeff
      (fun s : ℂ => ((s - rho) ^ m)⁻¹ * A s) rho (-1) =
      GaloisForLFunctions.HTGeometry.taylorCoeffZero (fun t : ℂ => A (rho + t)) (m - 1) := by
  let F : ℂ → ℂ := fun s : ℂ => ((s - rho) ^ m)⁻¹ * A s
  have hshift : GaloisForLFunctions.HTGeometry.laurentShift F rho (m + 1) =
      fun t : ℂ => t * A (rho + t) := by
    funext t
    rw [GaloisForLFunctions.HTGeometry.laurentShift]
    simp only [F]
    have harg : rho + t - rho = t := by ring
    rw [harg]
    rcases eq_or_ne t 0 with rfl | ht
    · simp [zero_pow (by omega : m ≠ 0)]
    · rw [pow_succ]
      field_simp
  have hAsh : AnalyticAt ℂ (fun t : ℂ => A (rho + t)) 0 :=
    GaloisForLFunctions.HTGeometry.analyticAt_comp_const_add hA
  have hana : AnalyticAt ℂ
      (GaloisForLFunctions.HTGeometry.laurentShift F rho (m + 1)) 0 := by
    rw [hshift]
    exact analyticAt_id.mul hAsh
  have hell : (0 : ℤ) ≤ (-1 : ℤ) + (((m + 1 : ℕ) : ℤ)) := by
    have hmz : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
    push_cast
    omega
  change GaloisForLFunctions.HTGeometry.laurentCoeff F rho (-1) = _
  rw [GaloisForLFunctions.HTGeometry.laurentCoeff_eq_taylorCoeffZero hana hell, hshift]
  have hidx : ((-1 : ℤ) + (((m + 1 : ℕ) : ℤ))).toNat = m := by omega
  rw [hidx]
  have hpow := GaloisForLFunctions.HTGeometry.taylorCoeffZero_pow_mul hAsh 1 m
  simp only [pow_one] at hpow
  rw [hpow, if_pos hm]

theorem taylorCoeffZero_shifted_exponential (rho u : ℂ) (j : ℕ) :
    GaloisForLFunctions.HTGeometry.taylorCoeffZero
      (fun t : ℂ => Complex.exp (-Complex.I * (rho + t) * u)) j =
      Complex.exp (-Complex.I * rho * u) * (-Complex.I * u) ^ j / (j.factorial : ℂ) := by
  have hfun : (fun t : ℂ => Complex.exp (-Complex.I * (rho + t) * u)) =
      fun t : ℂ => Complex.exp (-Complex.I * rho * u) *
        Complex.exp ((-Complex.I * u) * t) := by
    funext t
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hfun, GaloisForLFunctions.HTGeometry.taylorCoeffZero,
    iteratedDeriv_const_mul_field, HurwitzExp.iteratedDeriv_expLin]
  simp

/-- Polynomial multiplying the common exponential in the residue of a finite principal part. -/
def higherPoleResiduePolynomial (H : ℂ → ℂ) (rho : ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range k,
    Polynomial.C
      (GaloisForLFunctions.HTGeometry.laurentCoeff H rho ((j : ℤ) - (k : ℤ)) *
        (-Complex.I : ℂ) ^ (k - 1 - j) /
          ((k - 1 - j).factorial : ℂ)) *
      Polynomial.X ^ (k - 1 - j)

/-- An order-`k` principal part against `exp(-i*s*u)` has an exponential-polynomial residue. -/
theorem laurentCoeff_principalPart_mul_exponential
    (H : ℂ → ℂ) (rho u : ℂ) (k : ℕ) :
    GaloisForLFunctions.HTGeometry.laurentCoeff
      (fun s : ℂ => GaloisForLFunctions.HTGeometry.principalPart H rho k s *
        Complex.exp (-Complex.I * s * u)) rho (-1) =
      Complex.exp (-Complex.I * rho * u) * (higherPoleResiduePolynomial H rho k).eval u := by
  let E : ℂ → ℂ := fun s : ℂ => Complex.exp (-Complex.I * s * u)
  have hE : AnalyticAt ℂ E rho := by
    dsimp only [E]
    fun_prop
  have hterm : ∀ j : ℕ, MeromorphicAt
      (fun s : ℂ => ((s - rho) ^ (k - j))⁻¹ * E s) rho := by
    intro j
    exact (MeromorphicAt.inv
      ((analyticAt_id.sub analyticAt_const).pow (k - j)).meromorphicAt).mul hE.meromorphicAt
  have hfun :
      (fun s : ℂ => GaloisForLFunctions.HTGeometry.principalPart H rho k s * E s) =
        fun s : ℂ => ∑ j ∈ Finset.range k,
          GaloisForLFunctions.HTGeometry.laurentCoeff H rho ((j : ℤ) - (k : ℤ)) *
            (((s - rho) ^ (k - j))⁻¹ * E s) := by
    funext s
    rw [GaloisForLFunctions.HTGeometry.principalPart, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  change GaloisForLFunctions.HTGeometry.laurentCoeff
      (fun s : ℂ => GaloisForLFunctions.HTGeometry.principalPart H rho k s * E s)
      rho (-1) = _
  rw [hfun]
  rw [GaloisForLFunctions.HTGeometry.laurentCoeff_sum (Finset.range k)
    (fun j => fun s : ℂ => ((s - rho) ^ (k - j))⁻¹ * E s)
    (fun j => GaloisForLFunctions.HTGeometry.laurentCoeff H rho
      ((j : ℤ) - (k : ℤ))) rho (-1) (fun j _ => hterm j)]
  rw [higherPoleResiduePolynomial, Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j < k := Finset.mem_range.mp hj
  have hm : 1 ≤ k - j := by omega
  rw [laurentCoeff_inv_pow_mul_analytic hE hm]
  simp only [E]
  rw [taylorCoeffZero_shifted_exponential]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hsub : k - j - 1 = k - 1 - j := by omega
  rw [hsub, mul_pow]
  ring

theorem higherPoleResiduePolynomial_coeff_top
    (H : ℂ → ℂ) (rho : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (higherPoleResiduePolynomial H rho k).coeff (k - 1) =
      GaloisForLFunctions.HTGeometry.laurentCoeff H rho (-(k : ℤ)) *
        (-Complex.I : ℂ) ^ (k - 1) / ((k - 1).factorial : ℂ) := by
  rw [higherPoleResiduePolynomial, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [if_neg]
    have hjk : j < k := Finset.mem_range.mp hj
    omega
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hk)).elim

theorem higherPoleResiduePolynomial_coeff_top_ne_zero
    (H : ℂ → ℂ) (rho : ℂ) {k : ℕ} (hk : 1 ≤ k)
    (hlead : GaloisForLFunctions.HTGeometry.laurentCoeff H rho (-(k : ℤ)) ≠ 0) :
    (higherPoleResiduePolynomial H rho k).coeff (k - 1) ≠ 0 := by
  rw [higherPoleResiduePolynomial_coeff_top H rho hk]
  exact div_ne_zero
    (mul_ne_zero hlead (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)))
    (by exact_mod_cast Nat.factorial_ne_zero (k - 1))

/-- A pole of order `m+1` has an exact `m+1`-dimensional residue-mode coefficient block. -/
theorem higherPoleResidueCoeffMatrix_rank
    (H : ℂ → ℂ) (rho : ℂ) (m : ℕ)
    (hlead : GaloisForLFunctions.HTGeometry.laurentCoeff H rho (-((m + 1 : ℕ) : ℤ)) ≠ 0) :
    (residueModeCoeffMatrix m (fun r : Fin (m + 1) =>
      (higherPoleResiduePolynomial H rho (m + 1)).coeff r.val)).rank = m + 1 := by
  apply residueModeCoeffMatrix_rank
  simpa using higherPoleResiduePolynomial_coeff_top_ne_zero H rho (k := m + 1)
    (by omega) hlead

end

end RHTower
