import GaloisForLFunctions.HTGeometry.EvenPowerCanonicalProductDA
import GaloisForLFunctions.HTGeometry.RationalPowerNormDichotomy
import GaloisForLFunctions.HTGeometry.GammaWeierstrassCanonicalProduct

/-!
# The reflection norm of a power canonical product

Alongside the rotation norm `∏_{j<q} W_{p/q}(ω^j z) = W_p((-1)^{q+1} z^q)` the power canonical
products satisfy an exact *reflection* norm law:

`W_p(u) · W_p(-u) = W_{2p}(-u²)`,

valid for every positive integer exponent, including `p = 1` where the genus-one exponential factors
cancel in pairs.  Since the right-hand side has an even exponent, it is differentially algebraic;
hence the reflection norm of every integer-power canonical product is differentially algebraic, for
every `p`.

This isolates what the open odd-exponent case has to overcome.  The obstruction is not local: `W_p`
and `W_p(-·)` have the same kind of Laurent data at their zeros for every `p`, and their product is
always differentially algebraic.  What distinguishes even from odd is whether the `p` scales
`ω^j` occurring in `W_p(z^p) = ∏_{j<p} Γ(ω^j z + 1)⁻¹` are *themselves* closed under negation —
which is exactly the pairing that the reflection formula `Γ(1+x)Γ(1-x) = πx/sin(πx)` consumes.
-/

namespace HTGeometry

open GaloisForLFunctions

/-- The zero sequence at an integer exponent. -/
theorem powerZero_natCast (p n : ℕ) : powerZero ((p : ℕ) : ℝ) n = -(((n : ℂ) + 1) ^ p) := by
  have hreal : (((n : ℝ) + 1) ^ (((p : ℕ) : ℝ))) = ((n : ℝ) + 1) ^ (p : ℕ) :=
    Real.rpow_natCast _ _
  rw [powerZero, hreal]
  push_cast
  ring

theorem powerGenus_natCast_of_two_le {p : ℕ} (hp : 2 ≤ p) : powerGenus ((p : ℕ) : ℝ) = 0 := by
  rw [powerGenus_natCast]
  exact Nat.div_eq_of_lt (by omega)

/-- **Reflection norm law.**  The product of a power canonical product with its reflection is the
canonical product of twice the exponent, in the squared coordinate. -/
theorem powerCanonicalProduct_mul_neg {p : ℕ} (hp : 0 < p) (u : ℂ) :
    powerCanonicalProduct ((p : ℕ) : ℝ) u * powerCanonicalProduct ((p : ℕ) : ℝ) (-u)
      = powerCanonicalProduct ((2 * p : ℕ) : ℝ) (-(u ^ 2)) := by
  have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp
  have h2pR : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by
    have : 0 < 2 * p := by omega
    exact_mod_cast this
  have hgenus2p : powerGenus ((2 * p : ℕ) : ℝ) = 0 :=
    powerGenus_natCast_of_two_le (by omega)
  have hNne : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := by
    intro n
    have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h]
    exact_mod_cast Nat.succ_ne_zero n
  have hfac : ∀ n : ℕ,
      primaryFactor (powerGenus ((p : ℕ) : ℝ)) (u / powerZero ((p : ℕ) : ℝ) n)
          * primaryFactor (powerGenus ((p : ℕ) : ℝ)) ((-u) / powerZero ((p : ℕ) : ℝ) n)
        = primaryFactor (powerGenus ((2 * p : ℕ) : ℝ))
            ((-(u ^ 2)) / powerZero ((2 * p : ℕ) : ℝ) n) := by
    intro n
    have hN := hNne n
    have hpow : (((n : ℂ) + 1) ^ (2 * p)) = (((n : ℂ) + 1) ^ p) ^ 2 := by
      rw [← pow_mul, mul_comm]
    have hRHS : primaryFactor (powerGenus ((2 * p : ℕ) : ℝ))
        ((-(u ^ 2)) / powerZero ((2 * p : ℕ) : ℝ) n)
        = 1 - u ^ 2 / (((n : ℂ) + 1) ^ p) ^ 2 := by
      rw [hgenus2p, primaryFactor_zero_apply, powerZero_natCast, hpow, neg_div_neg_eq]
    rcases Nat.lt_or_ge p 2 with hp1 | hp2
    · -- genus one: the exponential factors cancel in pairs
      have hpe : p = 1 := by omega
      subst hpe
      have hg : powerGenus ((1 : ℕ) : ℝ) = 1 := by rw [powerGenus_natCast]
      rw [hg, hRHS, powerZero_natCast, primaryFactor_one_apply, primaryFactor_one_apply]
      simp only [pow_one]
      have hcancel : Complex.exp (u / -((n : ℂ) + 1))
          * Complex.exp ((-u) / -((n : ℂ) + 1)) = 1 := by
        rw [← Complex.exp_add]
        have hz : u / -((n : ℂ) + 1) + (-u) / -((n : ℂ) + 1) = 0 := by
          rw [← add_div]
          simp
        rw [hz, Complex.exp_zero]
      have hexpand : (1 - u / -((n : ℂ) + 1)) * Complex.exp (u / -((n : ℂ) + 1))
            * ((1 - (-u) / -((n : ℂ) + 1)) * Complex.exp ((-u) / -((n : ℂ) + 1)))
          = ((1 - u / -((n : ℂ) + 1)) * (1 - (-u) / -((n : ℂ) + 1)))
            * (Complex.exp (u / -((n : ℂ) + 1)) * Complex.exp ((-u) / -((n : ℂ) + 1))) := by
        ring
      rw [hexpand, hcancel, mul_one]
      field_simp
      ring
    · -- genus zero
      have hg : powerGenus ((p : ℕ) : ℝ) = 0 := powerGenus_natCast_of_two_le hp2
      rw [hg, hRHS, primaryFactor_zero_apply, primaryFactor_zero_apply, powerZero_natCast]
      have hNp : (((n : ℂ) + 1) ^ p) ≠ 0 := pow_ne_zero _ hN
      field_simp
      ring
  have h1 := hasProd_powerCanonicalProduct hpR u
  have h2 := hasProd_powerCanonicalProduct hpR (-u)
  have h3 := hasProd_powerCanonicalProduct h2pR (-(u ^ 2))
  have hmul := h1.mul h2
  rw [funext hfac] at hmul
  exact hmul.unique h3

/-- **The reflection norm is differentially algebraic**, for every integer exponent. -/
theorem differentiallyAlgebraic_powerCanonicalProduct_mul_neg {p : ℕ} (hp : 0 < p) :
    DifferentiallyAlgebraic
      (fun u : ℂ => powerCanonicalProduct ((p : ℕ) : ℝ) u
        * powerCanonicalProduct ((p : ℕ) : ℝ) (-u)) := by
  have h2pR : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by
    have : 0 < 2 * p := by omega
    exact_mod_cast this
  have hfun : (fun u : ℂ => powerCanonicalProduct ((p : ℕ) : ℝ) u
        * powerCanonicalProduct ((p : ℕ) : ℝ) (-u))
      = fun u : ℂ => powerCanonicalProduct ((2 * p : ℕ) : ℝ) ((-1 : ℂ) * u ^ 2) := by
    funext u
    rw [show ((-1 : ℂ) * u ^ 2) = -(u ^ 2) from by ring]
    exact powerCanonicalProduct_mul_neg hp u
  rw [hfun]
  exact differentiallyAlgebraic_comp_const_mul_pow
    (analyticOnNhd_powerCanonicalProduct h2pR) (by norm_num) (by norm_num)
    (differentiallyAlgebraic_powerCanonicalProduct_of_even (by omega) ⟨p, by ring⟩)

/-- **Reflection collapse of the ray product.**  The reciprocal-Gamma ray product times its
reflection is a product of Euler sine factors, for every `p` — even or odd.  This is the exact
statement of what the odd case has to overcome: the reflection pairing is always available *between*
`G` and `G(-·)`, but for odd `p` it is never available *inside* `G` itself, because the scales
`ω^j` are then not closed under negation. -/
theorem gammaRayProduct_mul_neg (p : ℕ) (ω z : ℂ) :
    (∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * z + 1))⁻¹)
        * ∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * (-z) + 1))⁻¹
      = ∏ j ∈ Finset.range p, sincProduct (ω ^ j * z) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [show (ω ^ j * (-z)) = (-(ω ^ j)) * z from by ring]
  exact reciprocalGamma_scale_pair (ω ^ j) z

end HTGeometry

