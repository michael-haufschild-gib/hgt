import GaloisForLFunctions.HTGeometry.ClockHomogeneousScaling
import GaloisForLFunctions.HTGeometry.ChargeUnique

/-!
# A clock eigenvector is weighted-homogeneous

The jet-scaling clock is diagonal on monomials, scaling the coefficient of a monomial `s` by
`λ^{weight s}`.  Hence an eigenvector — a polynomial `p` with `ρ_λ(p) = χ(λ)·p` for all nonzero `λ`
— has all its monomials of one weight, i.e. is weighted-homogeneous.  Combined with the homogeneous
eigenvalue law this identifies the eigenvalue `χ(λ) = λ^k`, giving the polynomial character of the
concrete clock and discharging the algebraicity input.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {C : Type*} [Field C]

/-- The clock acts diagonally on coefficients: the coefficient at `s` is scaled by `λ^{weight s}`. -/
theorem clockDilationAlgHom_coeff (lam : C) (p : DifferentialPolynomial Unit C)
    (s : (Unit × ℕ) →₀ ℕ) :
    (clockDilationAlgHom lam p).coeff s
      = lam ^ (Finsupp.weight (fun r : Unit × ℕ => r.2) s) * p.coeff s := by
  induction p using MvPolynomial.induction_on' with
  | monomial t c =>
      rw [clockDilationAlgHom_monomial, MvPolynomial.C_mul_monomial, MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial]
      split_ifs with h
      · rw [h]
      · rw [mul_zero]
  | add p q hp hq =>
      rw [map_add, MvPolynomial.coeff_add, hp, hq, ← mul_add, ← MvPolynomial.coeff_add]

/-- **A clock eigenvector is weighted-homogeneous.**  If `ρ_λ(p) = χ(λ)·p` for all nonzero `λ`, the
nonzero polynomial `p` is weighted-homogeneous (all monomials of a single jet-weight). -/
theorem isWeightedHomogeneous_of_clock_eigenvector [Infinite C]
    {p : DifferentialPolynomial Unit C} (hp0 : p ≠ 0) {χ : C → C}
    (heig : ∀ lam : C, lam ≠ 0 → clockDilationAlgHom lam p = MvPolynomial.C (χ lam) * p) :
    ∃ k : ℕ, MvPolynomial.IsWeightedHomogeneous (fun r : Unit × ℕ => r.2) p k := by
  obtain ⟨t₀, ht₀⟩ := MvPolynomial.support_nonempty.mpr hp0
  have hct : p.coeff t₀ ≠ 0 := MvPolynomial.mem_support_iff.mp ht₀
  refine ⟨Finsupp.weight (fun r : Unit × ℕ => r.2) t₀, fun s hs => ?_⟩
  apply HTGeometry.charge_unique (C := C)
  intro lam hlam
  have h1 : lam ^ (Finsupp.weight (fun r : Unit × ℕ => r.2) s) * p.coeff s = χ lam * p.coeff s := by
    have := congrArg (MvPolynomial.coeff s) (heig lam hlam)
    rwa [clockDilationAlgHom_coeff, MvPolynomial.coeff_C_mul] at this
  have h2 : lam ^ (Finsupp.weight (fun r : Unit × ℕ => r.2) t₀) * p.coeff t₀ = χ lam * p.coeff t₀ := by
    have := congrArg (MvPolynomial.coeff t₀) (heig lam hlam)
    rwa [clockDilationAlgHom_coeff, MvPolynomial.coeff_C_mul] at this
  rw [mul_right_cancel₀ hs h1, mul_right_cancel₀ hct h2]

end

end GaloisForLFunctions
