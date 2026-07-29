import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The logarithmic derivation on real Dirichlet convolutions and Selberg's identity

Pointwise multiplication by `log` is a derivation for Dirichlet convolution:

`(f * g)·log = (f·log) * g + f * (g·log)`,

since `log` is additive on the divisor antidiagonal.  This is the
real-coefficient counterpart of `HTGeometry.logWeight_leibniz`
(`OperatorTailDirichletMatroid`), which states the same derivation property
for complex coefficient rings; the real form is needed for the von Mangoldt
development, whose `Λ` and `log` are real-valued.

Applied to `Λ * ζ = log` and inverted by Möbius, the derivation rule yields
**Selberg's identity**

`Λ·log + Λ * Λ = (log·log) * μ`,

the starting point of the elementary treatment of the prime number theorem
with error terms.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction

/-- **Logarithmic derivation rule** (real coefficients; complex counterpart:
`HTGeometry.logWeight_leibniz`): pointwise `log` acts as a derivation on
Dirichlet convolution. -/
theorem pmul_log_mul (f g : ArithmeticFunction ℝ) :
    (f * g).pmul ArithmeticFunction.log
      = (f.pmul ArithmeticFunction.log) * g
        + f * (g.pmul ArithmeticFunction.log) := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  simp only [pmul_apply, mul_apply, ArithmeticFunction.add_apply, log_apply]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.1 hx
  have hx1 : x.1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hxn
    omega
  have hx2 : x.2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hxn
    omega
  have hlog : Real.log n = Real.log x.1 + Real.log x.2 := by
    rw [← hxn]
    push_cast
    exact Real.log_mul (by exact_mod_cast hx1) (by exact_mod_cast hx2)
  rw [hlog]
  ring

/-- `ζ` carries the pointwise `log` weight to `log` itself. -/
theorem zeta_pmul_log :
    ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ).pmul
        ArithmeticFunction.log
      = ArithmeticFunction.log := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  simp [log_apply]

/-- **Selberg's identity**: `Λ·log + Λ*Λ = (log·log) * μ`. -/
theorem vonMangoldt_pmul_log_add_mul_self :
    vonMangoldt.pmul ArithmeticFunction.log + vonMangoldt * vonMangoldt
      = (ArithmeticFunction.log.pmul ArithmeticFunction.log)
        * ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) := by
  have hζμ : ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
      * ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) = 1 :=
    coe_zeta_mul_coe_moebius
  have hkey : ArithmeticFunction.log.pmul ArithmeticFunction.log
      = (vonMangoldt.pmul ArithmeticFunction.log + vonMangoldt * vonMangoldt)
        * ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) := by
    calc ArithmeticFunction.log.pmul ArithmeticFunction.log
        = (vonMangoldt * ((zeta : ArithmeticFunction ℕ) :
            ArithmeticFunction ℝ)).pmul ArithmeticFunction.log := by
          rw [vonMangoldt_mul_zeta]
      _ = (vonMangoldt.pmul ArithmeticFunction.log)
            * ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
          + vonMangoldt * (((zeta : ArithmeticFunction ℕ) :
            ArithmeticFunction ℝ).pmul ArithmeticFunction.log) :=
          pmul_log_mul _ _
      _ = (vonMangoldt.pmul ArithmeticFunction.log)
            * ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
          + vonMangoldt * (vonMangoldt * ((zeta : ArithmeticFunction ℕ) :
            ArithmeticFunction ℝ)) := by
          rw [zeta_pmul_log, vonMangoldt_mul_zeta]
      _ = (vonMangoldt.pmul ArithmeticFunction.log
            + vonMangoldt * vonMangoldt)
          * ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) := by
          ring
  calc vonMangoldt.pmul ArithmeticFunction.log + vonMangoldt * vonMangoldt
      = (vonMangoldt.pmul ArithmeticFunction.log
          + vonMangoldt * vonMangoldt)
        * (((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
          * ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)) := by
        rw [hζμ, mul_one]
    _ = (ArithmeticFunction.log.pmul ArithmeticFunction.log)
        * ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) := by
        rw [← mul_assoc, ← hkey]

end RHTower
