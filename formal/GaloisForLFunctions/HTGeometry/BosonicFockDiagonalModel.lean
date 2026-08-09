import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaRealSpectrum
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaMomentForm

/-!
# The diagonal bosonic Fock model

A strict diagonal contraction with one-particle eigenvalues `p` has a multiplicative bosonic second
quantization whose eigenvalues, on the occupation basis, are the occupation monomials `p^ν`.  This
file works entirely inside that diagonal model: the second quantization is specified by its
eigenvalues, its Schatten membership at a real exponent is the summability of their moduli raised to
that exponent, its Schatten trace is the corresponding sum, and the order-`d` regularized Fredholm
determinant of `I - x Γ` is the product of the primary factors at the eigenvalues.  Nothing here
claims anything about non-diagonal or non-normal operators.

Within that model: multiplicative second quantization preserves the whole positive real Schatten
spectrum, the Schatten trace is the nome Euler product at the same exponent, the regularized
determinant of order `g+1` is the infinite-order genus-`g` multiple elliptic gamma product, and its
logarithm is the trace series.
-/

namespace HTGeometry

open scoped BigOperators ENNReal NNReal

/-- Eigenvalue of the multiplicative second quantization at an occupation. -/
noncomputable def bosonicEigenvalue {ι : Type*} (p : ι → ℂ) (ν : ι →₀ ℕ) : ℂ :=
  nomeMonomial p ν

/-- Singular value of the multiplicative second quantization at an occupation. -/
noncomputable def bosonicSingularValue {ι : Type*} (p : ι → ℂ) (ν : ι →₀ ℕ) : ℝ :=
  ‖nomeMonomial p ν‖

/-- Schatten `σ`-membership of the second quantization in the diagonal model. -/
def BosonicSchatten {ι : Type*} (p : ι → ℂ) (σ : ℝ) : Prop :=
  Summable (fun ν : ι →₀ ℕ => bosonicSingularValue p ν ^ σ)

/-- Schatten `σ`-membership of the one-particle contraction. -/
def OneParticleSchatten {ι : Type*} (p : ι → ℂ) (σ : ℝ) : Prop :=
  Summable (fun a => ‖p a‖ ^ σ)

/-- Schatten `σ`-trace of the second quantization in the diagonal model. -/
noncomputable def bosonicSchattenTrace {ι : Type*} (p : ι → ℂ) (σ : ℝ) : ℝ≥0∞ :=
  ∑' ν : ι →₀ ℕ, ((‖nomeMonomial p ν‖₊ ^ σ : NNReal) : ℝ≥0∞)

/-- **Second quantization preserves the whole Schatten spectrum.**  At every positive real exponent
the second quantization lies in the Schatten class exactly when the one-particle contraction
does. -/
theorem bosonicSchatten_iff_oneParticleSchatten {ι : Type*} (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) {σ : ℝ} (hσ : 0 < σ) :
    BosonicSchatten p σ ↔ OneParticleSchatten p σ :=
  summable_nomeMonomial_rpow_iff σ hσ p hp_lt

/-- **The Schatten trace is the nome Euler product.**  The trace of the `σ`-th power of the modulus
of the second quantization is the Euler product of the one-particle moduli at the same exponent. -/
theorem bosonicSchattenTrace_eq {ι : Type*} (p : ι → ℂ) (σ : ℝ) :
    bosonicSchattenTrace p σ
      = ⨆ S : Finset ι, ∏ a ∈ S, (1 - ((‖p a‖₊ ^ σ : NNReal) : ℝ≥0∞))⁻¹ :=
  nomeOccupationMass_rpow_eq_iSup_finset σ p

/-- The order-`g+1` regularized Fredholm determinant of `I - x Γ` in the diagonal model, defined by
its eigenvalue product. -/
noncomputable def regularizedFredholmDet {ι : Type*} (g : ℕ) (p : ι → ℂ) (x : ℂ) : ℂ :=
  ∏' ν : ι →₀ ℕ, primaryFactor g (x * bosonicEigenvalue p ν)

/-- **Genus is the regularized determinant order.**  The order-`g+1` regularized determinant of
`I - x Γ` is the infinite-order genus-`g` multiple elliptic gamma product. -/
theorem regularizedFredholmDet_eq {ι : Type*} (g : ℕ) (p : ι → ℂ) (x : ℂ) :
    regularizedFredholmDet g p x = infiniteMultipleEllipticGamma g p x := rfl

/-- **The trace expansion of the regularized determinant.**  Inside the unit disc the logarithm of
the order-`g+1` regularized determinant is the trace series, starting at the determinant order. -/
theorem regularizedFredholmDet_eq_exp_neg_traceSeries {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    {x : ℂ} (hx : ‖x‖ < 1) :
    regularizedFredholmDet g p x
      = Complex.exp (-∑' m : ℕ, x ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ) *
          ∑' ν : ι →₀ ℕ, bosonicEigenvalue p ν ^ (m + (g + 1))) := by
  rw [regularizedFredholmDet_eq,
    infiniteMultipleEllipticGamma_eq_exp_neg_moments g p hp_lt hsum hx]
  congr 2
  refine tsum_congr fun m => ?_
  congr 1
  exact (tsum_nomeMonomial_pow p hp_lt (by omega)
    (summable_norm_pow_of_le hp_lt (by omega : g + 1 ≤ m + (g + 1)) hsum)).symm

end HTGeometry
