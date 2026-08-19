import GaloisForLFunctions.HTGeometry.QuasiAbelianPoincareSeries
import GaloisForLFunctions.HTGeometry.LatticePeriodization

/-!
# The flat multiplier attached to a normalized profile

`1 - (1 - Θ)^m` equals `1` wherever `Θ` does and differs from `1` to order `m` there, so multiplying
by it leaves every jet of order below `m` unchanged at such a point.  Invariance is inherited from
`Θ`, because the expression is a polynomial in it.

This is the device that turns a periodized Gaussian, which is invariant and small transversally but
not normalized, into a damping multiplier that is genuinely the identity on a finite jet packet.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The flat multiplier of a profile. -/
def flatMultiplier {d : ℕ} (Θ : MultivariateEntire d) (m : ℕ) : MultivariateEntire d :=
  mvPolynomialMultivariateEntire 1
    - multivariateEntirePow (mvPolynomialMultivariateEntire 1 - Θ) m

theorem flatMultiplier_apply {d : ℕ} (Θ : MultivariateEntire d) (m : ℕ) (x : Fin d → ℂ) :
    (flatMultiplier Θ m).1 x = 1 - (1 - Θ.1 x) ^ m := by
  rw [flatMultiplier]
  have hsub : ∀ (f g : MultivariateEntire d) (y : Fin d → ℂ), (f - g).1 y = f.1 y - g.1 y :=
    fun _ _ _ => rfl
  have hone : (mvPolynomialMultivariateEntire (1 : MvPolynomial (Fin d) ℂ)).1 x = 1 := by
    simp [mvPolynomialMultivariateEntire]
  rw [hsub, multivariateEntirePow_apply, hsub, hone]

/-- **An invariant profile gives an invariant multiplier.** -/
theorem flatMultiplier_invariant {d : ℕ} (Θ : MultivariateEntire d) (m : ℕ)
    {ΓH : AddSubgroup (Fin d → ℂ)}
    (hΘ : ∀ η ∈ ΓH, ∀ x, Θ.1 (x + η) = Θ.1 x) :
    ∀ η ∈ ΓH, ∀ x, (flatMultiplier Θ m).1 (x + η) = (flatMultiplier Θ m).1 x := by
  intro η hη x
  rw [flatMultiplier_apply, flatMultiplier_apply, hΘ η hη x]

/-- **The flat multiplier does not move the low jets at a normalization point.** -/
theorem multiIndexJetEvalCLM_flatMultiplier_mul {d m : ℕ} (Θ f : MultivariateEntire d)
    {p : Fin d → ℂ} (hΘ : Θ.1 p = 1) (a : Fin d →₀ ℕ) (ha : Finsupp.degree a < m) :
    multiIndexJetEvalCLM p a (multivariateEntireMul (flatMultiplier Θ m) f)
      = multiIndexJetEvalCLM p a f := by
  set h : MultivariateEntire d := mvPolynomialMultivariateEntire 1 - Θ with hh
  have hhp : h.1 p = 0 := by
    have hone : (mvPolynomialMultivariateEntire (1 : MvPolynomial (Fin d) ℂ)).1 p = 1 := by
      simp [mvPolynomialMultivariateEntire]
    show (mvPolynomialMultivariateEntire 1).1 p - Θ.1 p = 0
    rw [hone, hΘ, sub_self]
  have hsplit : multivariateEntireMul (flatMultiplier Θ m) f
      = f - multivariateEntireMul (multivariateEntirePow h m) f := by
    ext x
    rw [multivariateEntireMul_apply, flatMultiplier_apply]
    have hsub : ∀ (u v : MultivariateEntire d) (y : Fin d → ℂ), (u - v).1 y = u.1 y - v.1 y :=
      fun _ _ _ => rfl
    rw [hsub, multivariateEntireMul_apply, multivariateEntirePow_apply]
    have hhx : h.1 x = 1 - Θ.1 x := by
      have hone : (mvPolynomialMultivariateEntire (1 : MvPolynomial (Fin d) ℂ)).1 x = 1 := by
        simp [mvPolynomialMultivariateEntire]
      show (mvPolynomialMultivariateEntire 1).1 x - Θ.1 x = 1 - Θ.1 x
      rw [hone]
    rw [hhx]
    ring
  rw [hsplit, map_sub, multiIndexJetEvalCLM_mul_pow_eq_zero_of_degree_lt h f p hhp a ha, sub_zero]

end

end GaloisForLFunctions.HTGeometry
