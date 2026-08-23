import GaloisForLFunctions.HTGeometry.MeromorphicPrincipalPart
import Mathlib.Topology.Algebra.Polynomial

/-!
# A finite sum of principal parts that decays is zero

Clearing the denominators of a finite sum of principal parts produces a genuine polynomial; if the
sum decays along the real axis faster than every power, that polynomial vanishes at infinity, hence
is the zero polynomial, hence the sum vanishes identically off its poles.

This is the mechanism behind Burnol's Propositions 6.2 and 6.6: the residue series of a vector
orthogonal to all but finitely many evaluators is a *rational* function, and a rational function
cannot decay exponentially unless it is zero.

## Main results

* `principalSum`, `principalDen`, `principalPoly`
* `eval_principalPoly` — the polynomial computes `principalSum · principalDen` off the poles.
* `polynomial_eq_zero_of_tendsto_zero`
* `principalSum_eq_zero_of_tendsto`
-/

open Complex Filter Topology Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The sum of the principal parts of `H` at the points of `R`. -/
def principalSum (H : ℂ → ℂ) (R : Finset ℂ) (k : ℕ) : ℂ → ℂ :=
  fun Z => ∑ ρ ∈ R, principalPart H ρ k Z

/-- The common denominator. -/
def principalDen (R : Finset ℂ) (k : ℕ) : ℂ → ℂ :=
  fun Z => ∏ ρ ∈ R, (Z - ρ) ^ k

/-- The polynomial obtained by clearing the denominators. -/
def principalPoly (H : ℂ → ℂ) (R : Finset ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ ρ ∈ R, (∑ j ∈ Finset.range k,
      Polynomial.C (laurentCoeff H ρ ((j : ℤ) - k)) * (Polynomial.X - Polynomial.C ρ) ^ j)
    * ∏ ρ' ∈ R.erase ρ, (Polynomial.X - Polynomial.C ρ') ^ k

theorem principalPart_mul_pow {H : ℂ → ℂ} {ρ Z : ℂ} (hZ : Z ≠ ρ) (k : ℕ) :
    principalPart H ρ k Z * (Z - ρ) ^ k
      = ∑ j ∈ Finset.range k, laurentCoeff H ρ ((j : ℤ) - k) * (Z - ρ) ^ j := by
  rw [principalPart, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hne : (Z - ρ) ≠ 0 := sub_ne_zero.2 hZ
  have hsplit : (Z - ρ) ^ k = (Z - ρ) ^ (k - j) * (Z - ρ) ^ j := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, mul_assoc, ← mul_assoc ((Z - ρ) ^ (k - j))⁻¹, inv_mul_cancel₀ (pow_ne_zero _ hne),
    one_mul]

theorem eval_principalPoly (H : ℂ → ℂ) (R : Finset ℂ) (k : ℕ) {Z : ℂ} (hZ : Z ∉ R) :
    (principalPoly H R k).eval Z = principalSum H R k Z * principalDen R k Z := by
  classical
  rw [principalPoly, principalSum, principalDen, Polynomial.eval_finset_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have hZρ : Z ≠ ρ := by
    intro h
    exact hZ (h ▸ hρ)
  have hden : (∏ ρ' ∈ R, (Z - ρ') ^ k)
      = (Z - ρ) ^ k * ∏ ρ' ∈ R.erase ρ, (Z - ρ') ^ k := (Finset.mul_prod_erase R _ hρ).symm
  rw [Polynomial.eval_mul, Polynomial.eval_finset_sum, Polynomial.eval_prod, hden]
  have hsum : (∑ j ∈ Finset.range k,
      (Polynomial.C (laurentCoeff H ρ ((j : ℤ) - k))
        * (Polynomial.X - Polynomial.C ρ) ^ j).eval Z)
      = principalPart H ρ k Z * (Z - ρ) ^ k := by
    rw [principalPart_mul_pow hZρ k]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [hsum]
  have hprod : (∏ ρ' ∈ R.erase ρ, ((Polynomial.X - Polynomial.C ρ') ^ k).eval Z)
      = ∏ ρ' ∈ R.erase ρ, (Z - ρ') ^ k := by
    refine Finset.prod_congr rfl fun ρ' _ => ?_
    simp
  rw [hprod]
  ring

/-! ## A decaying polynomial vanishes -/

theorem polynomial_eq_zero_of_tendsto_zero {p : Polynomial ℂ}
    (h : Tendsto (fun σ : ℝ => p.eval ((σ : ℝ) : ℂ)) atTop (𝓝 0)) : p = 0 := by
  by_cases hdeg : 0 < p.degree
  · exfalso
    have hnorm : Tendsto (fun σ : ℝ => ‖((σ : ℝ) : ℂ)‖) atTop atTop := by
      have : ∀ σ : ℝ, ‖((σ : ℝ) : ℂ)‖ = |σ| := fun σ => Complex.norm_real σ ▸ rfl
      refine Tendsto.congr (fun σ => (this σ).symm) ?_
      exact tendsto_abs_atTop_atTop
    have hbig := Polynomial.tendsto_norm_atTop p hdeg hnorm
    have hzero : Tendsto (fun σ : ℝ => ‖p.eval ((σ : ℝ) : ℂ)‖) atTop (𝓝 0) := by
      simpa using h.norm
    exact not_tendsto_nhds_of_tendsto_atTop hbig 0 hzero
  · have hle : p.degree ≤ 0 := not_lt.1 hdeg
    have hC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_degree_le_zero hle
    have hconst : Tendsto (fun _ : ℝ => p.coeff 0) atTop (𝓝 0) := by
      refine h.congr fun σ => ?_
      rw [hC]
      simp
    have := tendsto_nhds_unique tendsto_const_nhds hconst
    rw [hC, this, map_zero]

/-! ## The conclusion -/

theorem principalSum_eq_zero_of_tendsto {H : ℂ → ℂ} {R : Finset ℂ} {k : ℕ}
    (h : Tendsto (fun σ : ℝ => (principalPoly H R k).eval ((σ : ℝ) : ℂ)) atTop (𝓝 0))
    {Z : ℂ} (hZ : Z ∉ R) (hk : k ≠ 0) : principalSum H R k Z = 0 := by
  have hp : principalPoly H R k = 0 := polynomial_eq_zero_of_tendsto_zero h
  have hval : principalSum H R k Z * principalDen R k Z = 0 := by
    rw [← eval_principalPoly H R k hZ, hp, Polynomial.eval_zero]
  have hden : principalDen R k Z ≠ 0 := by
    rw [principalDen]
    refine Finset.prod_ne_zero_iff.2 fun ρ hρ => ?_
    refine pow_ne_zero _ (sub_ne_zero.2 ?_)
    intro hcon
    exact hZ (hcon ▸ hρ)
  exact (mul_eq_zero.1 hval).resolve_right hden

end

end GaloisForLFunctions.HTGeometry
