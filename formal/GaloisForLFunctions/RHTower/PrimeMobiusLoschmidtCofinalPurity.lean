import GaloisForLFunctions.RHTower.PrimeMobiusLoschmidtPurity
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization

/-!
# Cofinal prime Möbius Loschmidt purity

The finite signed prime transfer has a Loschmidt echo whose Cesàro limit is the collision
probability of its squarefree Bernoulli state.  This file identifies the cofinal-prime value in the
absolutely convergent half-plane.  Its local collision factor is a quotient of two copies of the
squarefree Euler factor, so the existing squarefree Möbius normalization gives

`∏ₚ (1 + p⁻²ˢ)/(1 + p⁻ˢ)² = ζ(2s)³/(ζ(4s) ζ(s)²)` for real `s > 1`.

Thus the finite-aperture quantum survival law remains nonzero after the prime aperture is removed.
The theorem is deliberately confined to `s > 1`; it makes no critical-strip continuation claim.
-/

open scoped BigOperators
open Filter

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

/-- The positive Schur weight is the real branch of the corresponding complex prime power. -/
theorem primeSchurWeight_eq_cpow (sigma : ℝ) (p : Nat.Primes) :
    (primeSchurWeight sigma p : ℂ) =
      ((p : ℕ) : ℂ) ^ (-(sigma : ℂ)) := by
  rw [show (-(sigma : ℂ)) = ((-sigma : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (by positivity)]
  congr 1
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  rw [primeSchurWeight, Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- Squarefree Euler factors are multipliable on the half-plane of absolute convergence. -/
theorem multipliable_primeSquarefreeEulerFactor {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun p : Nat.Primes =>
      1 + ((p : ℕ) : ℂ) ^ (-s)) := by
  apply Complex.multipliable_one_add_of_summable
  apply Summable.of_norm
  have h := (summable_norm_squarefreeCpow hs).subtype Nat.Prime
  refine h.congr ?_
  intro p
  simp only [Function.comp_apply, squarefreeCpow_apply,
    if_pos p.property.squarefree]

/-- The squarefree Euler factor at a prime. -/
def primeSquarefreeEulerFactor (s : ℂ) (p : Nat.Primes) : ℂ :=
  1 + ((p : ℕ) : ℂ) ^ (-s)

/-- The one-prime collision factor in the Möbius Loschmidt purity. -/
def primeSquarefreeLoschmidtPurityFactor (sigma : ℝ) (p : Nat.Primes) : ℂ :=
  primeSquarefreeEulerFactor (2 * (sigma : ℂ)) p /
    primeSquarefreeEulerFactor (sigma : ℂ) p ^ 2

/-- The cofinal-prime Möbius Loschmidt purity. -/
def infinitePrimeSquarefreeLoschmidtPurity (sigma : ℝ) : ℂ :=
  ∏' p : Nat.Primes, primeSquarefreeLoschmidtPurityFactor sigma p

/-- Doubling the inverse temperature squares the one-prime Schur weight. -/
theorem primeSchurWeight_two_mul (sigma : ℝ) (p : Nat.Primes) :
    primeSchurWeight (2 * sigma) p = primeSchurWeight sigma p ^ 2 := by
  rw [primeSchurWeight, primeSchurWeight, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The real finite-state collision factor is exactly the squarefree Euler-factor quotient. -/
theorem ofReal_primeSquarefreeLoschmidtPurityFactor
    (sigma : ℝ) (p : Nat.Primes) :
    (((1 + primeSchurWeight sigma p ^ 2) /
      (1 + primeSchurWeight sigma p) ^ 2 : ℝ) : ℂ) =
        primeSquarefreeLoschmidtPurityFactor sigma p := by
  rw [← primeSchurWeight_two_mul sigma p]
  push_cast
  rw [primeSchurWeight_eq_cpow, primeSchurWeight_eq_cpow]
  simp only [primeSquarefreeLoschmidtPurityFactor, primeSquarefreeEulerFactor]
  congr 3
  congr 1
  push_cast
  ring

/-- The local quotient product converges to the quotient of the two nonzero squarefree Euler
products.  This is proved at the level of finite-product nets because `ℂ` is a group with zero,
not a multiplicative group. -/
private theorem hasProd_primeSquarefreeLoschmidtPurityFactor
    {sigma : ℝ} (hsigma : 1 < sigma) :
    HasProd (primeSquarefreeLoschmidtPurityFactor sigma)
      ((riemannZeta (2 * (sigma : ℂ)) /
          riemannZeta (2 * (2 * (sigma : ℂ)))) /
        ((riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ))) *
          (riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ))))) := by
  have hs : 1 < ((sigma : ℂ)).re := by simpa using hsigma
  have htwo : 1 < (2 * (sigma : ℂ)).re := by
    rw [Complex.mul_re]
    norm_num
    linarith
  have hbase := multipliable_primeSquarefreeEulerFactor hs
  have htwoBase := multipliable_primeSquarefreeEulerFactor htwo
  have hbaseValue := squarefree_eulerProduct_tprod hs
  have htwoValue := squarefree_eulerProduct_tprod htwo
  have hbaseProd :
      HasProd (primeSquarefreeEulerFactor (sigma : ℂ))
        (riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ))) := by
    simpa only [primeSquarefreeEulerFactor, hbaseValue] using hbase.hasProd
  have htwoProd :
      HasProd (primeSquarefreeEulerFactor (2 * (sigma : ℂ)))
        (riemannZeta (2 * (sigma : ℂ)) /
          riemannZeta (2 * (2 * (sigma : ℂ)))) := by
    simpa only [primeSquarefreeEulerFactor, htwoValue] using htwoBase.hasProd
  have hdenProd := hbaseProd.mul hbaseProd
  have hbaseZeta : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have htwoZeta : riemannZeta (2 * (sigma : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re htwo
  have hden_ne :
      (riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ))) *
          (riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ))) ≠ 0 :=
    mul_ne_zero (div_ne_zero hbaseZeta htwoZeta)
      (div_ne_zero hbaseZeta htwoZeta)
  have hratio :
      HasProd (fun p : Nat.Primes =>
        primeSquarefreeEulerFactor (2 * (sigma : ℂ)) p /
          (primeSquarefreeEulerFactor (sigma : ℂ) p *
            primeSquarefreeEulerFactor (sigma : ℂ) p))
        ((riemannZeta (2 * (sigma : ℂ)) /
            riemannZeta (2 * (2 * (sigma : ℂ)))) /
          ((riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ))) *
            (riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ))))) := by
    unfold HasProd at htwoProd hdenProd ⊢
    convert htwoProd.div hdenProd hden_ne using 1
    funext S
    rw [Finset.prod_div_distrib]
    rfl
  change HasProd (fun p : Nat.Primes =>
    primeSquarefreeEulerFactor (2 * (sigma : ℂ)) p /
      primeSquarefreeEulerFactor (sigma : ℂ) p ^ 2) _
  simpa only [pow_two] using hratio

/-- The local Loschmidt collision factors have a convergent cofinal prime product for `sigma > 1`. -/
theorem multipliable_primeSquarefreeLoschmidtPurityFactor
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Multipliable (primeSquarefreeLoschmidtPurityFactor sigma) :=
  (hasProd_primeSquarefreeLoschmidtPurityFactor hsigma).multipliable

/-- Exact zeta value of the cofinal-prime Möbius Loschmidt purity. -/
theorem infinitePrimeSquarefreeLoschmidtPurity_eq_zetaRatio
    {sigma : ℝ} (hsigma : 1 < sigma) :
    infinitePrimeSquarefreeLoschmidtPurity sigma =
      riemannZeta (2 * (sigma : ℂ)) ^ 3 /
        (riemannZeta (4 * (sigma : ℂ)) * riemannZeta (sigma : ℂ) ^ 2) := by
  rw [infinitePrimeSquarefreeLoschmidtPurity,
    (hasProd_primeSquarefreeLoschmidtPurityFactor hsigma).tprod_eq]
  have hs : 1 < ((sigma : ℂ)).re := by simpa using hsigma
  have htwo : 1 < (2 * (sigma : ℂ)).re := by
    rw [Complex.mul_re]
    norm_num
    linarith
  have hfour : riemannZeta (4 * (sigma : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      rw [Complex.mul_re]
      norm_num
      linarith)
  have htwoZeta : riemannZeta (2 * (sigma : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re htwo
  have hbaseZeta : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs
  field_simp
  ring

/-- Cofinal finite-aperture purities converge to the infinite-prime purity. -/
theorem tendsto_finitePrimeSquarefreeLoschmidtPurity_cofinal
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Tendsto
      (fun S : Finset Nat.Primes =>
        (finitePrimeSquarefreeLoschmidtPurity S sigma : ℂ))
      atTop (nhds (infinitePrimeSquarefreeLoschmidtPurity sigma)) := by
  rw [infinitePrimeSquarefreeLoschmidtPurity]
  have hprod :=
    (multipliable_primeSquarefreeLoschmidtPurityFactor hsigma).hasProd
  have hfinite :
      (fun S : Finset Nat.Primes =>
        (finitePrimeSquarefreeLoschmidtPurity S sigma : ℂ)) =
        fun S => ∏ p ∈ S, primeSquarefreeLoschmidtPurityFactor sigma p := by
    funext S
    rw [finitePrimeSquarefreeLoschmidtPurity_eq_prod]
    push_cast
    apply Finset.prod_congr rfl
    intro p hp
    have h := ofReal_primeSquarefreeLoschmidtPurityFactor sigma p
    push_cast at h
    exact h
  rw [hfinite]
  exact hprod

/-- Cofinal finite-aperture purities converge to the explicit zeta ratio. -/
theorem tendsto_finitePrimeSquarefreeLoschmidtPurity_cofinal_zetaRatio
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Tendsto
      (fun S : Finset Nat.Primes =>
        (finitePrimeSquarefreeLoschmidtPurity S sigma : ℂ))
      atTop
      (nhds (riemannZeta (2 * (sigma : ℂ)) ^ 3 /
        (riemannZeta (4 * (sigma : ℂ)) * riemannZeta (sigma : ℂ) ^ 2))) := by
  simpa only [infinitePrimeSquarefreeLoschmidtPurity_eq_zetaRatio hsigma] using
    tendsto_finitePrimeSquarefreeLoschmidtPurity_cofinal hsigma

/-- The cofinal-prime Möbius Loschmidt purity cannot vanish in the absolute half-plane. -/
theorem infinitePrimeSquarefreeLoschmidtPurity_ne_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    infinitePrimeSquarefreeLoschmidtPurity sigma ≠ 0 := by
  rw [infinitePrimeSquarefreeLoschmidtPurity_eq_zetaRatio hsigma]
  apply div_ne_zero
  · exact pow_ne_zero 3 (riemannZeta_ne_zero_of_one_lt_re (by
      rw [Complex.mul_re]
      norm_num
      linarith))
  · apply mul_ne_zero
    · exact riemannZeta_ne_zero_of_one_lt_re (by
        rw [Complex.mul_re]
        norm_num
        linarith)
    · exact pow_ne_zero 2 (riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma))

/-- Removing the prime aperture does not drive the finite-state Loschmidt purity to zero. -/
theorem not_tendsto_finitePrimeSquarefreeLoschmidtPurity_cofinal_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ¬ Tendsto
      (fun S : Finset Nat.Primes =>
        (finitePrimeSquarefreeLoschmidtPurity S sigma : ℂ))
      atTop (nhds 0) := by
  intro hzero
  exact infinitePrimeSquarefreeLoschmidtPurity_ne_zero hsigma
    (tendsto_nhds_unique
      (tendsto_finitePrimeSquarefreeLoschmidtPurity_cofinal hsigma) hzero)

end RHTower
