import GaloisForLFunctions.HTGeometry.DifferentialPolynomial

/-!
# The jet-scaling clock dilation

On the differential polynomial ring `DifferentialPolynomial ι C` (jets `X_(i,n)` with the jet-shift
derivation `D X_(i,n) = X_(i,n+1)`), the clock dilation `ρ_λ` scales the `n`-th jet by `λ^n`:

`ρ_λ(X_(i,n)) = λ^n · X_(i,n)`.

It is the concrete cocharacter of the clock-character law.  This file constructs it as an algebra
homomorphism, proves the composition law `ρ_λ ∘ ρ_μ = ρ_{λμ}` (so it is an automorphism for `λ ≠ 0`,
inverse `ρ_{λ⁻¹}`), and proves the defining semilinearity

`ρ_λ(D w) = λ · D(ρ_λ w)`.                                (eq. 1)

The base field carries the zero derivation (`λ` is a differential constant), so no compatibility
hypothesis is needed.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

variable {ι C : Type*} [CommRing C]

/-- The jet-scaling clock dilation `X_(i,n) ↦ λ^n · X_(i,n)`. -/
def clockDilationAlgHom (lam : C) :
    DifferentialPolynomial ι C →ₐ[C] DifferentialPolynomial ι C :=
  MvPolynomial.aeval fun p : ι × ℕ => MvPolynomial.C (lam ^ p.2) * MvPolynomial.X p

@[simp]
theorem clockDilationAlgHom_X (lam : C) (i : ι) (n : ℕ) :
    clockDilationAlgHom lam (MvPolynomial.X (i, n) : DifferentialPolynomial ι C) =
      MvPolynomial.C (lam ^ n) * MvPolynomial.X (i, n) := by
  simp [clockDilationAlgHom]

@[simp]
theorem clockDilationAlgHom_C (lam c : C) :
    clockDilationAlgHom (ι := ι) lam (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [clockDilationAlgHom]

/-- Composition law of the clock: `ρ_λ ∘ ρ_μ = ρ_{λμ}`. -/
theorem clockDilationAlgHom_comp (lam mu : C) :
    (clockDilationAlgHom (ι := ι) lam).comp (clockDilationAlgHom mu) =
      clockDilationAlgHom (lam * mu) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, n⟩
  simp only [AlgHom.comp_apply, clockDilationAlgHom_X, map_mul, clockDilationAlgHom_C]
  rw [mul_pow, MvPolynomial.C_mul]
  ring

theorem clockDilationAlgHom_apply_apply (lam mu : C) (w : DifferentialPolynomial ι C) :
    clockDilationAlgHom lam (clockDilationAlgHom mu w) = clockDilationAlgHom (lam * mu) w := by
  have := clockDilationAlgHom_comp (ι := ι) lam mu
  exact AlgHom.congr_fun this w

@[simp]
theorem clockDilationAlgHom_one (w : DifferentialPolynomial ι C) :
    clockDilationAlgHom (1 : C) w = w := by
  have : clockDilationAlgHom (ι := ι) (1 : C) = AlgHom.id C (DifferentialPolynomial ι C) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, n⟩
    simp
  rw [this, AlgHom.id_apply]

/-- The clock is an automorphism for `λ ≠ 0`, with inverse `ρ_{λ⁻¹}`. -/
def clockDilationAlgEquiv {C : Type*} [Field C] (lam : C) (hlam : lam ≠ 0) :
    DifferentialPolynomial ι C ≃ₐ[C] DifferentialPolynomial ι C :=
  AlgEquiv.ofAlgHom (clockDilationAlgHom lam) (clockDilationAlgHom lam⁻¹)
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, n⟩
      rw [AlgHom.comp_apply, clockDilationAlgHom_apply_apply, mul_inv_cancel₀ hlam,
        clockDilationAlgHom_one, AlgHom.id_apply])
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, n⟩
      rw [AlgHom.comp_apply, clockDilationAlgHom_apply_apply, inv_mul_cancel₀ hlam,
        clockDilationAlgHom_one, AlgHom.id_apply])

@[simp]
theorem clockDilationAlgEquiv_apply {C : Type*} [Field C] (lam : C) (hlam : lam ≠ 0)
    (w : DifferentialPolynomial ι C) :
    clockDilationAlgEquiv (ι := ι) lam hlam w = clockDilationAlgHom lam w := rfl

/-- **Semilinearity (eq. 1).**  `ρ_λ(D w) = λ · D(ρ_λ w)`. -/
theorem clockDilation_semilinear (lam : C) (w : DifferentialPolynomial ι C) :
    clockDilationAlgHom lam (w′) = MvPolynomial.C lam * (clockDilationAlgHom lam w)′ := by
  induction w using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      rw [map_add, map_add, hP, hQ, map_add, map_add, mul_add]
  | mul_X P p hP =>
      rcases p with ⟨i, n⟩
      have hDPX : (P * MvPolynomial.X (i, n) : DifferentialPolynomial ι C)′
          = P′ * MvPolynomial.X (i, n) + P * MvPolynomial.X (i, n + 1) := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul, differentialPolynomial_deriv_X]
        ring
      have hDrhs : (clockDilationAlgHom lam P
              * (MvPolynomial.C (lam ^ n) * MvPolynomial.X (i, n)))′
          = (clockDilationAlgHom lam P)′ * (MvPolynomial.C (lam ^ n) * MvPolynomial.X (i, n))
            + clockDilationAlgHom lam P * (MvPolynomial.C (lam ^ n) * MvPolynomial.X (i, n + 1)) := by
        rw [Derivation.leibniz, Derivation.leibniz]
        simp only [smul_eq_mul, differentialPolynomial_deriv_X, differentialPolynomial_deriv_C]
        ring
      conv_lhs => rw [hDPX, map_add, map_mul, map_mul, hP, clockDilationAlgHom_X,
        clockDilationAlgHom_X]
      conv_rhs => rw [map_mul, clockDilationAlgHom_X, hDrhs]
      rw [pow_succ', MvPolynomial.C_mul]
      ring

end

end GaloisForLFunctions
