import GaloisForLFunctions.CompactHyperbolicSurfaces.EntireSelbergZeta
import GaloisForLFunctions.RHTower.XiGlobalKummerSquareClasses
import GaloisForLFunctions.RHTower.XiHorizontalSlopeNearOne

/-!
# The compact Selberg zeta function is a spectral model of a finite off-line layer

For the compact surface with a small eigenvalue (`exists_selbergZeta_small_eigenvalue`) the Selberg
zeta function `Ẑ` is entire, an Euler product `Π_{p,k} (1 − e^{−(s+k)ℓ_p})` on `Re s > 1`, satisfies
an exact functional equation, and has a finite nonempty set of zeros off `Re s = ½` in the strip.
It is the model in which an Euler product and an exact functional equation coexist with a finite
off-line layer. Two properties separate it from `ζ`:

* **The layer is real** (`exists_selbergZeta_spectral_finiteLayer`): the off-line zeros are
  `½ ± √(¼ − λ_j)`, from eigenvalues `λ_j` of a self-adjoint Laplacian.
* **The Euler logarithm has the other sign**: `Ẑ'/Ẑ(σ)` is the length series, a nonnegative real
  number for real `σ > 1` (`logDeriv_eulerZeta_ofReal`); `log Ẑ` has nonpositive coefficients.

For `ζ` the Euler logarithm has nonnegative coefficients, `Re(−ζ'/ζ(σ)) ≥ 0`, and `ξ` is positive on
the real axis, so an off-line zero of `ζ` is never real (`riemannZeta_euler_sign_and_xi_real_pos`).
A proof that finitely many off-line zeros force none, if it uses only an Euler product and an exact
functional equation, is refuted by `Ẑ`; it must use the sign of the Euler logarithm, the Gamma
factor of `ζ`, or the non-reality of the layer.
-/

open Complex Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

namespace CompactQuotient

variable {X : CompactQuotient}

/-- **The Selberg Euler logarithm is nonpositive**: on the real axis right of `1` the logarithmic
derivative of the Euler product is the length series, a nonnegative real number. -/
theorem logDeriv_eulerZeta_ofReal (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|) {σ : ℝ} (hσ : 1 < σ) :
    logDeriv X.eulerZeta σ = ((∑' c : X.NClass, X.realWeight σ c : ℝ) : ℂ) ∧
      0 ≤ ∑' c : X.NClass, X.realWeight σ c := by
  refine ⟨?_, tsum_nonneg fun c => realWeight_nonneg hhyp σ c⟩
  rw [logDeriv_eulerZeta hhyp (by simpa using hσ), lengthSeries_ofReal]

end CompactQuotient

open CompactQuotient

/-- **A spectral finite layer.** Some compact surface has an entire Selberg zeta function that is an
Euler product on `Re s > 1`, satisfies the exact functional equation, has a finite nonempty set of
zeros off the critical line in the strip, all of them real, and has a nonnegative real logarithmic
derivative on the real axis right of `1`. -/
theorem exists_selbergZeta_spectral_finiteLayer :
    ∃ (X : CompactQuotient) (Z : ℂ → ℂ),
      Differentiable ℂ Z ∧
      (∀ s : ℂ, 1 < s.re → HasProd (fun x : X.PClass × ℕ =>
          1 - Complex.exp (-((s + x.2) * X.classLen x.1.1))) (Z s)) ∧
      (∀ s : ℂ, 0 < s.re → s.re < 1 → Z (1 - s) = Z s * Complex.exp (-(X.area *
          ∫ t in (0 : ℝ)..1, (s - 1 / 2) * (((t : ℂ) * (s - 1 / 2)) *
            Complex.tan (Real.pi * ((t : ℂ) * (s - 1 / 2))))))) ∧
      {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ Z s = 0}.Finite ∧
      {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ Z s = 0}.Nonempty ∧
      (∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ 1 / 2 → Z s = 0 → s.im = 0) ∧
      (∀ σ : ℝ, 1 < σ → ∃ r : ℝ, 0 ≤ r ∧ logDeriv Z σ = r) := by
  obtain ⟨-, X, Z, -, hhyp, hdiff, -, hprod, hFE, hfin, hne, hset⟩ :=
    exists_selbergZeta_small_eigenvalue
  refine ⟨X, Z, hdiff, hprod, hFE, hfin, hne, fun s h0 h1 hhalf hz => ?_, fun σ hσ => ?_⟩
  · -- the off-line zeros are `½ ± √(¼ − λ_j)`
    have hmem : s ∈ {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ Z s = 0} := ⟨h0, h1, hhalf, hz⟩
    rw [hset] at hmem
    obtain ⟨j, -, -, hs | hs⟩ := hmem <;> rw [hs] <;> exact Complex.ofReal_im _
  · -- `Z` is the Euler product near `σ`, so their logarithmic derivatives agree there
    have hσ' : (1 : ℝ) < (σ : ℂ).re := by simpa using hσ
    have hev : Z =ᶠ[𝓝 (σ : ℂ)] X.eulerZeta := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσ'] with s hs
      exact (hprod s hs).tprod_eq.symm
    obtain ⟨hlog, hnn⟩ := logDeriv_eulerZeta_ofReal hhyp hσ
    refine ⟨_, hnn, ?_⟩
    rw [← hlog, logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]

/-- **The contrast with `ζ`.** `−ζ'/ζ` has nonnegative real part on the real axis right of `1` (the
Euler logarithm of `ζ` has nonnegative coefficients), and `ξ` is positive on the real axis, so no
zero of `ζ` off the critical line is real. -/
theorem riemannZeta_euler_sign_and_xi_real_pos :
    (∀ σ : ℝ, 1 < σ → 0 ≤ (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re) ∧
      ∀ t : ℝ, 0 < (_root_.RHTower.xi (t : ℂ)).re := by
  refine ⟨fun σ hσ => ?_, _root_.RHTower.XiGlobalKummer.xi_real_pos⟩
  rw [_root_.RHTower.DeBruijn.re_neg_logDeriv_riemannZeta_real_eq_tsum hσ]
  exact tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

end GaloisForLFunctions.CompactHyperbolicSurfaces
