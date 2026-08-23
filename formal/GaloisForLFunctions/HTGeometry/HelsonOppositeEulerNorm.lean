import GaloisForLFunctions.HTGeometry.HelsonCharacterLSeries
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Opposite-sheet norm law for signed Helson Euler products

A prime phase taking values in the square roots of unity has two opposite Euler sheets.  Their
product is exactly `ζ(2s)` on the half-plane of absolute convergence.  This is the infinite
Euler-product form of the cyclotomic identity `(1-u x)(1+u x)=1-x²`.
-/

noncomputable section

open Complex ArithmeticFunction LSeries

namespace GaloisForLFunctions.HTGeometry

/-- The constant positive prime phase extends to the constant-one coefficient on every positive
integer. -/
theorem phaseChar_one (n : ℕ) :
    phaseChar (fun _ => (1 : ℂ)) n = if n = 0 then 0 else 1 := by
  by_cases hn : n = 0
  · subst n
    rfl
  · rw [phaseChar_apply_of_ne_zero _ hn, if_neg hn]
    simp

/-- The Dirichlet series of the constant positive prime phase is the Riemann zeta function. -/
theorem LSeries_phaseChar_one_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => phaseChar (fun _ => (1 : ℂ)) n) s = riemannZeta s := by
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  apply LSeries_congr
  intro n hn
  simp [phaseChar_one, ArithmeticFunction.zeta_apply, hn]

/-- **Infinite cyclotomic norm law.**  For every square-one unimodular prime phase, the two
opposite Helson Euler sheets have product `ζ(2s)` on `Re s > 1`. -/
theorem LSeries_phaseChar_mul_opposite_eq_riemannZeta_two_mul
    {u : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1)
    (hsq : ∀ p : ℕ, Nat.Prime p → u p ^ 2 = 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => phaseChar u n) s *
        LSeries (fun n => phaseChar (fun p => -u p) n) s =
      riemannZeta (2 * s) := by
  have hneg : ∀ p : ℕ, Nat.Prime p → ‖-u p‖ = 1 := by
    intro p hp
    rw [norm_neg, hu p hp]
  have hleft := hasProd_phaseEuler hu hs
  have hright := hasProd_phaseEuler hneg hs
  have hprod := hleft.mul hright
  have hs2 : 1 < (2 * s).re := by
    rw [Complex.mul_re]
    norm_num
    linarith
  have hzeta := riemannZeta_eulerProduct_hasProd hs2
  have hfactor :
      (fun p : Nat.Primes =>
        (1 - u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ *
          (1 - (-u (p : ℕ)) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) =
      (fun p : Nat.Primes => (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹) := by
    funext p
    let x : ℂ := ((p : ℕ) : ℂ) ^ (-s)
    have hpne : ((p : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast p.2.ne_zero
    have hxx : x * x = ((p : ℕ) : ℂ) ^ (-(2 * s)) := by
      dsimp only [x]
      rw [← Complex.cpow_add _ _ hpne]
      congr 1
      ring
    have huu : u (p : ℕ) * u (p : ℕ) = 1 := by
      simpa only [pow_two] using hsq p.1 p.2
    have hux : (u (p : ℕ) * x) * (u (p : ℕ) * x) = x * x := by
      calc
        (u (p : ℕ) * x) * (u (p : ℕ) * x) =
            (u (p : ℕ) * u (p : ℕ)) * (x * x) := by ring
        _ = x * x := by rw [huu, one_mul]
    have hux' :
        (u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) *
            (u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) =
          ((p : ℕ) : ℂ) ^ (-s) * ((p : ℕ) : ℂ) ^ (-s) := by
      simpa only [x] using hux
    rw [← mul_inv_rev]
    congr 1
    rw [neg_mul]
    rw [show (1 - -(u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))) *
        (1 - u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) =
      1 - (u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) *
        (u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) by ring, hux']
    simpa only [x] using congrArg (fun z : ℂ => 1 - z) hxx
  have hprod' : HasProd
      (fun p : Nat.Primes => (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹)
      (LSeries (fun n => phaseChar u n) s *
        LSeries (fun n => phaseChar (fun p => -u p) n) s) := by
    rw [← hfactor]
    exact hprod
  exact HasProd.unique hprod' hzeta

/-- Canonical negative sheet: its Euler/Dirichlet value is `ζ(2s)/ζ(s)`. -/
theorem LSeries_phaseChar_neg_one_eq_riemannZeta_two_mul_div
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => phaseChar (fun _ => (-1 : ℂ)) n) s =
      riemannZeta (2 * s) / riemannZeta s := by
  have hnorm := LSeries_phaseChar_mul_opposite_eq_riemannZeta_two_mul
    (u := fun _ => (1 : ℂ))
    (fun _ _ => norm_one)
    (fun _ _ => by norm_num) hs
  rw [LSeries_phaseChar_one_eq_riemannZeta hs] at hnorm
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  exact (eq_div_iff hzeta).2 (by simpa [mul_comm] using hnorm)

end GaloisForLFunctions.HTGeometry
