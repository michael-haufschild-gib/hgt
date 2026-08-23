import GaloisForLFunctions.RHTower.ConnesPadicWeilEulerFactor
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.VonMangoldtEuler

/-!
# The prime side of the Weil explicit formula as a sum of local Weil terms

Appendix II of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes' geometric side is a sum over the places of `ℚ` of local principal-value integrals
`∫'_{ℚ_v^*} f(u)|1-u|^{-1} d^*u`.  At a finite place the multiplicative Haar measure is
normalized so that the units have mass `log p`, and for the geometric test function carried by
the shells inside the unit ball the local term is the Euler factor `(p^s - 1)^{-1}`.  Summing
`log p · (p^s-1)^{-1}` over the primes reproduces the von Mangoldt Dirichlet series, i.e. the
logarithmic derivative `-ζ'/ζ`.  This identifies the finite part of Connes' geometric side with
the prime side of the explicit formula.
-/

open MeasureTheory ArithmeticFunction

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Every element of the type of primes carries the primality fact. -/
instance connesNatPrimesFact (p : Nat.Primes) : Fact ((p : ℕ)).Prime := ⟨p.2⟩

/-- The local Weil term at the finite place `p` for the geometric test with ratio `p^{-s}`. -/
def connesLocalWeilTerm (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∫ a, connesPadicRadial (p : ℕ) (connesPadicGeomProfile ((((p : ℕ)) : ℂ) ^ (-s))) a *
      ((‖1 - (a : ℚ_[(p : ℕ)])‖⁻¹ : ℝ) : ℂ)
    ∂fieldOnePadicMultiplicativeHaar (p : ℕ)

/-- **The local Weil term is the local Euler factor.** -/
theorem connesLocalWeilTerm_eq (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    connesLocalWeilTerm p s = ((((p : ℕ)) : ℂ) ^ s - 1)⁻¹ :=
  connes_padic_weil_eulerFactor (p : ℕ) hs

/-- Every finite-place local Weil term is nonzero in the open right half-plane. -/
theorem connesLocalWeilTerm_ne_zero (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    connesLocalWeilTerm p s ≠ 0 := by
  rw [connesLocalWeilTerm_eq p hs]
  apply inv_ne_zero
  apply sub_ne_zero.mpr
  intro h
  have hpow : (((p : ℕ) : ℂ) ^ s) = 1 := h
  have hpowneg : (((p : ℕ) : ℂ) ^ (-s)) = 1 := by
    rw [Complex.cpow_neg, hpow, inv_one]
  have hnorm := connes_padic_norm_cpow_neg_lt_one (p : ℕ) hs
  rw [hpowneg, norm_one] at hnorm
  exact (lt_irrefl 1 hnorm)

/-- Real form of the local Euler factor. -/
theorem connesLocalWeilTerm_ofReal (p : Nat.Primes) {σ : ℝ} (hσ : 0 < σ) :
    connesLocalWeilTerm p (σ : ℂ) = ((((((p : ℕ) : ℝ)) ^ σ - 1)⁻¹ : ℝ) : ℂ) := by
  rw [connesLocalWeilTerm_eq p (by simpa using hσ)]
  rw [show ((((p : ℕ)) : ℂ) ^ ((σ : ℝ) : ℂ)) = (((((p : ℕ) : ℝ)) ^ σ : ℝ) : ℂ) by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    norm_cast]
  push_cast
  ring

/-- The local Euler factor is the geometric series over the shells inside the unit ball. -/
theorem connes_realEulerFactor_eq_tsum (p : Nat.Primes) {σ : ℝ} (hσ : 0 < σ) :
    ((((p : ℕ) : ℝ)) ^ σ - 1)⁻¹ = ∑' a : ℕ, (((p : ℕ) : ℝ)) ^ (-(((a : ℝ) + 1) * σ)) := by
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast (p.2).one_lt
  have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := by positivity
  set x : ℝ := ((p : ℕ) : ℝ) ^ (-σ) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos (by linarith) _
  have hxlt : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hterm : ∀ a : ℕ, (((p : ℕ) : ℝ)) ^ (-(((a : ℝ) + 1) * σ)) = x * x ^ a := by
    intro a
    have hexp : -(((a : ℝ) + 1) * σ) = (-σ) * (((a + 1 : ℕ) : ℝ)) := by push_cast; ring
    rw [hexp, Real.rpow_mul hp0, Real.rpow_natCast, ← hx, pow_succ]
    ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one hxpos.le hxlt]
  have hxinv : x = (((p : ℕ) : ℝ) ^ σ)⁻¹ := by rw [hx, Real.rpow_neg hp0]
  rw [hxinv, ← mul_inv]
  congr 1
  have hne : ((p : ℕ) : ℝ) ^ σ ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  field_simp

/-- **The finite part of Connes' geometric side is the prime side of the explicit formula.**
With the normalization `vol(ℤ_p^*) = log p`, the sum over the primes of the local Weil terms is
the von Mangoldt Dirichlet series, i.e. `-ζ'/ζ`. -/
theorem connes_weil_primeSide {σ : ℝ} (hσ : 1 < σ) :
    (∑' p : Nat.Primes, (Real.log (((p : ℕ) : ℝ)) : ℂ) * connesLocalWeilTerm p (σ : ℂ))
      = -deriv riemannZeta ((σ : ℝ) : ℂ) / riemannZeta ((σ : ℝ) : ℂ) := by
  have hterm : ∀ p : Nat.Primes,
      (Real.log (((p : ℕ) : ℝ)) : ℂ) * connesLocalWeilTerm p (σ : ℂ)
        = ((Real.log (((p : ℕ) : ℝ)) *
            ∑' a : ℕ, (((p : ℕ) : ℝ)) ^ (-(((a : ℝ) + 1) * σ)) : ℝ) : ℂ) := by
    intro p
    rw [connesLocalWeilTerm_ofReal p (by linarith),
      ← connes_realEulerFactor_eq_tsum p (by linarith)]
    push_cast
    ring
  rw [tsum_congr hterm, ← Complex.ofReal_tsum,
    ← GaloisForLFunctions.HTGeometry.tsum_vonMangoldt_eq_tsum_primes hσ,
    GaloisForLFunctions.HTGeometry.ofReal_tsum_vonMangoldt_eq hσ]

end

end GaloisForLFunctions.RHTower
