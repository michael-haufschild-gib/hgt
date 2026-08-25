import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyThermalDealiasingEndpoint

/-!
# Forced angular leakage of tilted chiral Teukolsky sectors

For a vector `psi` in the domain of a symmetric horizon angular operator `A`,
and complex candidate eigenvalue `lambda`, symmetry gives the exact identity

`‖A psi - lambda psi‖² = ‖A psi - re(lambda) psi‖² + im(lambda)² ‖psi‖²`.

The doubled theta--Teukolsky cusp weight has Birmingham--Mokhtari Casimir
`Q_H(z)=1/4+z²`, with imaginary part `2 re(z) im(z)`. Consequently its
irreducible spectral residual is at least

`4 re(z)² im(z)² ‖psi‖²`.

At an Xi divisor `re(z)` is nonzero. Every nonzero tilted doubled source must
therefore leave its candidate one-sector eigenchannel. This is quantitative
forced sector mixing; no KMS, CCR, passivity, or positivity premise enters.
It does not assert nonvanishing of the reduced second-order chiral source.

APS spectral flow applies after a self-adjoint real family has been produced;
it cannot itself turn a complex tilted candidate into such a family. The
identity below is the pointwise obstruction that precedes any family index.

**[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]**
-/

open scoped InnerProductSpace

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Pythagorean spectral-residual identity at one vector of a symmetric
complex operator. No boundedness assumption is needed. -/
theorem complexSymmetric_residual_norm_sq
    (Aψ ψ : H) (lambda : ℂ)
    (hsa : ⟪ψ, Aψ⟫_ℂ = ⟪Aψ, ψ⟫_ℂ) :
    ‖Aψ - lambda • ψ‖ ^ 2 =
      ‖Aψ - (lambda.re : ℂ) • ψ‖ ^ 2 +
        lambda.im ^ 2 * ‖ψ‖ ^ 2 := by
  rw [show ‖Aψ - lambda • ψ‖ ^ 2 =
        (⟪Aψ - lambda • ψ, Aψ - lambda • ψ⟫_ℂ).re from
      norm_sq_eq_re_inner (𝕜 := ℂ) (Aψ - lambda • ψ),
    show ‖Aψ - (lambda.re : ℂ) • ψ‖ ^ 2 =
        (⟪Aψ - (lambda.re : ℂ) • ψ,
          Aψ - (lambda.re : ℂ) • ψ⟫_ℂ).re from
      norm_sq_eq_re_inner (𝕜 := ℂ) (Aψ - (lambda.re : ℂ) • ψ),
    show ‖ψ‖ ^ 2 = (⟪ψ, ψ⟫_ℂ).re from
      norm_sq_eq_re_inner (𝕜 := ℂ) ψ]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, hsa]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, sub_zero]
  ring

/-- Exact tilt-resolved residual energy for the doubled chiral
Birmingham--Mokhtari angular channel. -/
theorem d4ThetaTeukolskyAngularSourceResidual_norm_sq
    (A : H → H) (ψ : H) (z : ℂ)
    (hsa : ⟪ψ, A ψ⟫_ℂ = ⟪A ψ, ψ⟫_ℂ) :
    ‖A ψ - d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue z • ψ‖ ^ 2 =
      ‖A ψ -
          ((d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue z).re : ℂ) • ψ‖ ^ 2 +
        4 * z.re ^ 2 * z.im ^ 2 * ‖ψ‖ ^ 2 := by
  rw [complexSymmetric_residual_norm_sq (A ψ) ψ
      (d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue z) hsa,
    d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_im]
  ring

/-- Tilt supplies a source-independent lower bound on failure of one-sector
angular closure. -/
theorem d4ThetaTeukolskyAngularSourceResidual_sq_lowerBound
    (A : H → H) (ψ : H) (z : ℂ)
    (hsa : ⟪ψ, A ψ⟫_ℂ = ⟪A ψ, ψ⟫_ℂ) :
    4 * z.re ^ 2 * z.im ^ 2 * ‖ψ‖ ^ 2 ≤
      ‖A ψ - d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue z • ψ‖ ^ 2 := by
  rw [d4ThetaTeukolskyAngularSourceResidual_norm_sq A ψ z hsa]
  have hnonneg :
      0 ≤ ‖A ψ -
        ((d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue z).re : ℂ) • ψ‖ ^ 2 :=
    sq_nonneg _
  linarith

/-- Every nonzero tilted divisor source has nonzero angular residual against
any horizon operator symmetric at that source. -/
theorem d4ThetaTeukolsky_tiltedAngularSource_forces_leakage
    (A : H → H) (ψ : H) (q : XiZeroCopy)
    (hsa : ⟪ψ, A ψ⟫_ℂ = ⟪A ψ, ψ⟫_ℂ)
    (hψ : ψ ≠ 0) (htilt : (xiSpectralPoint q).im ≠ 0) :
    A ψ - d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue
        (xiSpectralPoint q) • ψ ≠ 0 := by
  intro hzero
  have hbound := d4ThetaTeukolskyAngularSourceResidual_sq_lowerBound
    A ψ (xiSpectralPoint q) hsa
  rw [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hbound
  have hnorm : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hreSq : 0 < (xiSpectralPoint q).re ^ 2 :=
    sq_pos_of_ne_zero (thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q)
  have himSq : 0 < (xiSpectralPoint q).im ^ 2 := sq_pos_of_ne_zero htilt
  have hpositive :
      0 < 4 * (xiSpectralPoint q).re ^ 2 *
        (xiSpectralPoint q).im ^ 2 * ‖ψ‖ ^ 2 := by
    positivity
  linarith

end

end RHTower
