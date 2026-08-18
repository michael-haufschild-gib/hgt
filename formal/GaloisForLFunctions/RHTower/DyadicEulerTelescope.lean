import Mathlib
import GaloisForLFunctions.HTGeometry.EulerBinaryProduct

/-!
# The dyadic Euler telescope and the strict-right squarefree localization

`prime-valuation-dyadic-fermion-normal-cone-law`, equations `(23)`–`(27)`.

Euler's binary product `∏_{j ≥ 0} (1 + q^{2^j}) = (1-q)^{-1}` applied to `q = p^{-s}` splits the
local Euler factor into its binary digits.  Globally the `j`-th digit is the ratio
`ζ(2^j s) / ζ(2^{j+1} s)`, so the tower telescopes to `ζ(s)`.  Only the first digit has a divergent
first trace at `s = 1`, and only the first digit can carry a zero in the strict right half plane,
because there `ζ(2ρ)` is finite and nonzero.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

/-- Euler's binary product over an arbitrary normed field. -/
theorem tendsto_prod_one_add_cpow {q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (1 + q ^ 2 ^ j)) atTop (nhds ((1 - q)⁻¹)) := by
  have hq1 : (1 : ℂ) - q ≠ 0 := by
    intro h
    have : q = 1 := by linear_combination -h
    rw [this, norm_one] at hq
    linarith
  have hpart : ∀ J : ℕ, ∏ j ∈ Finset.range J, (1 + q ^ 2 ^ j) = (1 - q ^ 2 ^ J) / (1 - q) := by
    intro J
    rw [eq_div_iff hq1, mul_comm]
    exact GaloisForLFunctions.HTGeometry.one_sub_mul_prod_one_add_pow q J
  have hpow : Tendsto (fun J : ℕ => q ^ 2 ^ J) atTop (nhds 0) := by
    have h1 : Tendsto (fun J : ℕ => (2 : ℕ) ^ J) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
    exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp h1
  have hlim : Tendsto (fun J : ℕ => (1 - q ^ 2 ^ J) / (1 - q)) atTop (nhds ((1 - 0) / (1 - q))) :=
    (tendsto_const_nhds.sub hpow).div_const _
  rw [sub_zero, one_div] at hlim
  exact hlim.congr fun J => (hpart J).symm

theorem primeCpow_dyadic {s : ℂ} (p : Nat.Primes) (j : ℕ) :
    ((p : ℕ) : ℂ) ^ (-((2 ^ j : ℕ) * s)) = (((p : ℕ) : ℂ) ^ (-s)) ^ (2 ^ j) := by
  rw [show -(((2 ^ j : ℕ) : ℂ) * s) = ((2 ^ j : ℕ) : ℂ) * (-s) by ring,
    Complex.cpow_nat_mul]

theorem norm_primeCpow_lt_one {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos]
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
  have : ((p : ℕ) : ℝ) ^ (-s).re < ((p : ℕ) : ℝ) ^ (0 : ℝ) := by
    refine Real.rpow_lt_rpow_of_exponent_lt hp1 ?_
    simpa using hs
  simpa using this

/-- **`(23)`: the local Euler factor is the binary product of its dyadic digits.** -/
theorem tendsto_prod_one_add_primePow {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (1 + ((p : ℕ) : ℂ) ^ (-((2 ^ j : ℕ) * s))))
      atTop (nhds (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) := by
  have hkey := tendsto_prod_one_add_cpow (norm_primeCpow_lt_one hs p)
  refine hkey.congr fun J => ?_
  exact Finset.prod_congr rfl fun j _ => by rw [primeCpow_dyadic]

/-- The `j`-th dyadic digit of the Euler factor, globally. -/
theorem hasProd_one_add_primePow {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1 + ((p : ℕ) : ℂ) ^ (-s))
      (riemannZeta s / riemannZeta (2 * s)) := by
  have hs2 : 1 < (2 * s).re := by
    rw [Complex.mul_re]
    simp only [Complex.re_ofNat, Complex.im_ofNat]
    nlinarith [hs]
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs2
  have h1 := riemannZeta_eulerProduct_hasProd hs
  have h2 := riemannZeta_eulerProduct_hasProd hs2
  have h2' : HasProd (fun p : Nat.Primes => 1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))
      (riemannZeta (2 * s))⁻¹ := by
    have hcont : ContinuousAt (fun x : ℂ => x⁻¹) (riemannZeta (2 * s)) :=
      continuousAt_inv₀ hz2
    have hcomp := (hcont.tendsto.comp h2)
    refine hcomp.congr fun t => ?_
    rw [Function.comp_apply, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun p _ => inv_inv _
  have hmul := h1.mul h2'
  have hfac : ∀ p : Nat.Primes,
      (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))
        = 1 + ((p : ℕ) : ℂ) ^ (-s) := by
    intro p
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).2 p.2.ne_zero
    have hne : (1 : ℂ) - ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := by
      intro h
      have habs : ‖((p : ℕ) : ℂ) ^ (-s)‖ = 1 := by
        have : ((p : ℕ) : ℂ) ^ (-s) = 1 := by linear_combination -h
        rw [this, norm_one]
      rw [Complex.norm_natCast_cpow_of_pos p.2.pos] at habs
      have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
      have hlt : ((p : ℕ) : ℝ) ^ (-s).re < 1 := by
        have : ((p : ℕ) : ℝ) ^ (-s).re < ((p : ℕ) : ℝ) ^ (0 : ℝ) := by
          refine Real.rpow_lt_rpow_of_exponent_lt hp1 ?_
          simp only [Complex.neg_re]
          linarith
        simpa using this
      linarith [habs, hlt]
    have hsq : ((p : ℕ) : ℂ) ^ (-(2 * s)) = (((p : ℕ) : ℂ) ^ (-s)) ^ 2 := by
      have h := primeCpow_dyadic (s := s) p 1
      simpa using h
    rw [hsq]
    field_simp
    ring
  rw [show riemannZeta s / riemannZeta (2 * s) = riemannZeta s * (riemannZeta (2 * s))⁻¹ from
    div_eq_mul_inv _ _]
  have hfun : (fun p : Nat.Primes =>
      (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))))
      = fun p : Nat.Primes => 1 + ((p : ℕ) : ℂ) ^ (-s) := funext hfac
  rw [hfun] at hmul
  exact hmul

/-- **`(25)`: the singular first digit.** -/
theorem hasProd_one_add_primePow_first {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1 + ((p : ℕ) : ℂ) ^ (-s))
      (riemannZeta s / riemannZeta (2 * s)) :=
  hasProd_one_add_primePow hs

/-- **`(26)`, first half: the parity digit has a divergent first trace.** -/
theorem not_summable_primeReciprocal : ¬ Summable (fun p : Nat.Primes => (1 / p : ℝ)) :=
  Nat.Primes.not_summable_one_div

/-- **`(26)`, second half: every higher dyadic digit has a convergent first trace.** -/
theorem summable_primePow_dyadic {j : ℕ} (hj : 1 ≤ j) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 ^ j : ℝ))) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) := by
    have h : Summable (fun n : ℕ => (((n : ℝ)) ^ (2 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    refine h.congr fun n => ?_
    rw [← Real.rpow_neg (Nat.cast_nonneg n)]
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := fun a b h => Subtype.ext h
  refine (hbase.comp_injective hinj).of_nonneg_of_le (fun p => by positivity) ?_
  intro p
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_le
  refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ j := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hj
  linarith

/-- **`(27)`: every strict-right zero is already carried by the squarefree digit.** -/
theorem riemannZeta_eq_zero_iff_squarefree_eq_zero {ρ : ℂ} (hρ : 1 / 2 < ρ.re) :
    riemannZeta ρ = 0 ↔ riemannZeta ρ / riemannZeta (2 * ρ) = 0 := by
  have hρ2 : 1 < (2 * ρ).re := by
    rw [Complex.mul_re]
    simp only [Complex.re_ofNat, Complex.im_ofNat]
    nlinarith [hρ]
  have hz2 : riemannZeta (2 * ρ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hρ2
  constructor
  · intro h
    rw [h, zero_div]
  · intro h
    rcases div_eq_zero_iff.mp h with h1 | h1
    · exact h1
    · exact absurd h1 hz2

end RHTower
