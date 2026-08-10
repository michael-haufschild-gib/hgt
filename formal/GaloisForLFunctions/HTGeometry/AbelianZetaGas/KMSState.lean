import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GasKMSUniqueness
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.Core

/-!
# The unique KMS functional of the abelian zeta gas

At every positive temperature the mode weights `p^{-jσ}` lie strictly inside the unit disc, so the
gas algebra carries exactly one normalised functional satisfying the KMS exchange identity: the
Gibbs functional.  Its diagonal values are the geometric occupation law of the gas.
-/

namespace GaloisForLFunctions.HTGeometry

open GasWord

/-- The mode weight of the gas, read in `ℂ`. -/
noncomputable def gasNome (θ : AbelianZetaParameters) (m : AbelianZetaMode) : ℂ :=
  ((θ.ratio m : ℝ) : ℂ)

theorem gasNome_ne_zero (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    gasNome θ m ≠ 0 := by
  rw [gasNome, ne_eq, Complex.ofReal_eq_zero]
  exact (θ.ratio_pos m).ne'

theorem norm_gasNome_lt_one (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    ‖gasNome θ m‖ < 1 := by
  rw [gasNome, Complex.norm_real, Real.norm_of_nonneg (θ.ratio_nonneg m)]
  exact θ.ratio_lt_one m

/-- The imaginary-time modular flow of the gas. -/
noncomputable def gasTwist (θ : AbelianZetaParameters) :
    GasAlgebra AbelianZetaMode →ₐ[ℂ] GasAlgebra AbelianZetaMode :=
  twist (gasNome θ) (gasNome_ne_zero θ)

/-- The Gibbs functional of the gas. -/
noncomputable def gasGibbs (θ : AbelianZetaParameters) :
    GasAlgebra AbelianZetaMode →ₗ[ℂ] ℂ :=
  gibbs (gasNome θ)

/-- **Theorem 4.1, existence.**  The Gibbs functional is normalised and satisfies the KMS exchange
identity at every positive temperature. -/
theorem gasGibbs_exchange (θ : AbelianZetaParameters) (a b : GasAlgebra AbelianZetaMode) :
    gasGibbs θ (a * b) = gasGibbs θ (b * gasTwist θ a) :=
  gibbs_exchange (gasNome θ) (gasNome_ne_zero θ) a b

@[simp] theorem gasGibbs_one (θ : AbelianZetaParameters) : gasGibbs θ 1 = 1 :=
  gibbs_one (gasNome θ)

/-- **Theorem 4.1, uniqueness.** -/
theorem gasGibbs_unique (θ : AbelianZetaParameters)
    (ψ : GasAlgebra AbelianZetaMode →ₗ[ℂ] ℂ)
    (hexch : ∀ a b : GasAlgebra AbelianZetaMode, ψ (a * b) = ψ (b * gasTwist θ a))
    (hone : ψ 1 = 1) :
    ψ = gasGibbs θ :=
  gas_kms_unique ψ (gasNome θ) (gasNome_ne_zero θ) (norm_gasNome_lt_one θ) hexch hone

/-- **Theorem 4.1.**  For every positive temperature the gas algebra carries exactly one normalised
KMS functional. -/
theorem gas_kms_existsUnique (θ : AbelianZetaParameters) :
    ∃! ψ : GasAlgebra AbelianZetaMode →ₗ[ℂ] ℂ,
      (∀ a b : GasAlgebra AbelianZetaMode, ψ (a * b) = ψ (b * gasTwist θ a)) ∧ ψ 1 = 1 := by
  refine ⟨gasGibbs θ, ⟨gasGibbs_exchange θ, gasGibbs_one θ⟩, ?_⟩
  rintro ψ ⟨hexch, hone⟩
  exact gasGibbs_unique θ ψ hexch hone

/-! ## The diagonal masa carries the occupation law -/

/-- **The range projection of a mode carries `qⁿ`.** -/
theorem gasGibbs_rangeProj (θ : AbelianZetaParameters) (i : AbelianZetaMode) (n : ℕ) :
    gasGibbs θ ((gasV i) ^ n * (gasW i) ^ n) = gasNome θ i ^ n :=
  kms_range_mass (gasGibbs θ) (gasTwist θ) (gasGibbs_exchange θ)
    (twist_gasV (gasNome θ) (gasNome_ne_zero θ) i) (gasW_mul_gasV i) (gasGibbs_one θ) n

/-- **Each occupation layer carries `(1 − q)qⁿ`.**  This is the geometric mode law of the gas,
read on the diagonal masa. -/
theorem gasGibbs_layer (θ : AbelianZetaParameters) (i : AbelianZetaMode) (n : ℕ) :
    gasGibbs θ ((gasV i) ^ n * (1 - gasV i * gasW i) * (gasW i) ^ n)
      = (1 - gasNome θ i) * gasNome θ i ^ n :=
  kms_layer_mass (gasGibbs θ) (gasTwist θ) (gasGibbs_exchange θ)
    (twist_gasV (gasNome θ) (gasNome_ne_zero θ) i) (gasW_mul_gasV i) (gasGibbs_one θ) n

end GaloisForLFunctions.HTGeometry
