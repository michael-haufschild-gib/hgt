import GaloisForLFunctions.RHTower.Sieve.MoebiusLogRecursion
import GaloisForLFunctions.HTGeometry.GeneralisedVonMangoldt

/-!
# The generalised von Mangoldt weight is a logarithm

The weight `Λ_f = f⁻¹ * (f·log)` of an invertible arithmetic function turns Dirichlet convolution into
addition:

`Λ_1 = 0`,   `Λ_{f*g} = Λ_f + Λ_g`,

because pointwise multiplication by `log` is a derivation of the Dirichlet ring.  So `f ↦ Λ_f` is a
homomorphism from the units of the ring to the additive group of arithmetic functions, and the classical
weights are its values at the classical units: `Λ` at `ζ`, `−Λ` at `μ` — the latter *forced* by
`μ * ζ = 1` — and `f·Λ` at a completely multiplicative `f`.
-/

noncomputable section

namespace RHTower.Sieve

open ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- The weight of the convolution identity vanishes. -/
theorem vonMangoldtOf_one (hf : Invertible ((1 : ArithmeticFunction ℝ) 1)) :
    vonMangoldtOf (1 : ArithmeticFunction ℝ) hf = 0 :=
  (eq_vonMangoldtOf_of_mul_eq (1 : ArithmeticFunction ℝ) 0 hf
    (by rw [mul_zero, one_pmul_log])).symm

/-- **Additivity of the generalised von Mangoldt weight.**  `Λ_{f*g} = Λ_f + Λ_g`, from the logarithmic
derivation rule for Dirichlet convolution. -/
theorem vonMangoldtOf_mul (f g : ArithmeticFunction ℝ) (hf : Invertible (f 1))
    (hg : Invertible (g 1)) (hfg : Invertible ((f * g) 1)) :
    vonMangoldtOf (f * g) hfg = vonMangoldtOf f hf + vonMangoldtOf g hg := by
  have hL := RHTower.pmul_log_mul f g
  rw [pmul_log_eq_mul_vonMangoldtOf f hf, pmul_log_eq_mul_vonMangoldtOf g hg] at hL
  refine (eq_vonMangoldtOf_of_mul_eq (f * g) _ hfg ?_).symm
  rw [hL]
  ring

/-- The weight of the Möbius function is `−Λ`. -/
theorem vonMangoldtOf_moebius
    (hf : Invertible ((((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)) 1)) :
    vonMangoldtOf (((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)) hf
      = -vonMangoldt := by
  refine (eq_vonMangoldtOf_of_mul_eq _ (-vonMangoldt) hf ?_).symm
  rw [moebius_pmul_log]
  ring

end RHTower.Sieve

end
