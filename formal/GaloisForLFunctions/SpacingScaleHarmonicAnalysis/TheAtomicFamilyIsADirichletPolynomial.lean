import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.UnboundedOverlapIsTheRiemannHypothesis
import GaloisForLFunctions.ArithmeticElectrostatics.TheStabilityLawAtAtomicResolution

/-!
# The atomic family is a Dirichlet polynomial

On the zero side Weil's form samples the transform `h_f(z) = ∫ f(u) e^{izu} du` at the spectral
points `γ_ρ = (ρ − ½)/i` of the zeros. For an atomic test the transform factors into the bump and a
Dirichlet polynomial: the atomic family of level `N` and width `w` is the space of Dirichlet
polynomials of length `N`, band-limited by the bump at frequencies `≲ 1/w`.

* **Factorization** (`paperFT_atomicTest`): `h_{f_x}(z) = h_g(z) D_x(z)` with
  `D_x(z) = Σ_{n ≤ N} x_n e^{iz log n}`; at a zero, `D_x(γ_ρ) = Σ x_n n^{ρ − 1/2}`
  (`dirichletPoly_gammaOf`).
* **The zero-side summand** (`Wsummand_atomicTest`): the term of a zero `ρ` in `W(f_x, f_x)` is
  `m_ρ · h_g(γ_ρ) conj h_g(γ̄_ρ) · D_x(γ_ρ) conj D_x(γ̄_ρ)`, a product of a bump factor and a
  Dirichlet-polynomial factor.
* **Zeros on the line are squares** (`Wsummand_atomicTest_onLine`): for `Re ρ = ½` the term is
  `m_ρ |h_g(γ_ρ)|² |D_x(γ_ρ)|² ≥ 0`.

This is the dictionary of the programme: below the spacing the zeros up to height `≍ 1/w` oversample
the Dirichlet polynomials of length `N` (Nyquist density `log N/2π` against the zero density
`log(T/2π)/2π`), at the spacing they sample them at the Nyquist rate, and beyond it they undersample.
-/

noncomputable section

open MeasureTheory Finset Zeta23
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

variable {g : ℝ → ℝ}

/-- The **Dirichlet polynomial** `D_x(z) = Σ_{n ≤ N} x_n e^{iz log n}` of the weights `x`. -/
def dirichletPoly (N : ℕ) (x : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (x n : ℂ) * Complex.exp (Complex.I * z * (Real.log n : ℂ))

/-- At the spectral point of a zero the Dirichlet polynomial is `Σ x_n n^{ρ − 1/2}`. -/
theorem dirichletPoly_gammaOf (N : ℕ) (x : ℕ → ℝ) (ρ : ℂ) :
    dirichletPoly N x (gammaOf ρ) =
      ∑ n ∈ Icc 1 N, (x n : ℂ) * Complex.exp ((ρ - 1 / 2) * (Real.log n : ℂ)) := by
  unfold dirichletPoly gammaOf
  refine sum_congr rfl fun n _ => ?_
  congr 2
  field_simp

/-- The complexified atomic test is a combination of translates of the bump. -/
theorem cx_atomicTest (N : ℕ) (x : ℕ → ℝ) (g : ℝ → ℝ) :
    cx (atomicTest N x g) = fun u =>
      ∑ n ∈ Icc 1 N, (x n : ℂ) * ArithmeticCastelnuovoSeveri.translate (Real.log n) (cx g) u := by
  funext u
  simp only [cx, atomicTest, ArithmeticCastelnuovoSeveri.translate]
  push_cast
  rfl

/-- **Factorization of the transform**: `h_{f_x}(z) = h_g(z) D_x(z)`. -/
theorem paperFT_atomicTest (hg : Continuous g) (hgc : HasCompactSupport g) (N : ℕ)
    (x : ℕ → ℝ) (z : ℂ) :
    paperFT (cx (atomicTest N x g)) z = paperFT (cx g) z * dirichletPoly N x z := by
  have hint : ∀ n ∈ Icc 1 N, Integrable fun u =>
      (x n : ℂ) * ArithmeticCastelnuovoSeveri.translate (Real.log n) (cx g) u *
        Complex.exp (Complex.I * z * (u : ℂ)) := by
    intro n _
    have hc : Continuous fun u =>
        (x n : ℂ) * ArithmeticCastelnuovoSeveri.translate (Real.log n) (cx g) u *
          Complex.exp (Complex.I * z * (u : ℂ)) := by
      simp only [ArithmeticCastelnuovoSeveri.translate, cx]
      fun_prop
    refine hc.integrable_of_hasCompactSupport ?_
    have hs : HasCompactSupport (ArithmeticCastelnuovoSeveri.translate (Real.log n) (cx g)) :=
      translate_hasCompactSupport (hgc.comp_left Complex.ofReal_zero) _
    exact (hs.mul_left (f := fun _ => (x n : ℂ))).mul_right
  rw [cx_atomicTest, paperFT]
  simp_rw [sum_mul]
  rw [integral_finsetSum _ hint, dirichletPoly, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  have h := paperFT_translate (Real.log n) (cx g) z
  rw [paperFT] at h
  rw [show (fun u : ℝ => (x n : ℂ) * ArithmeticCastelnuovoSeveri.translate (Real.log n) (cx g) u *
      Complex.exp (Complex.I * z * (u : ℂ))) = fun u => (x n : ℂ) *
      (ArithmeticCastelnuovoSeveri.translate (Real.log n) (cx g) u *
        Complex.exp (Complex.I * z * (u : ℂ))) by funext u; ring, integral_const_mul, h]
  ring

/-- **The zero-side summand of an atomic test**: a bump factor times a Dirichlet-polynomial
factor. -/
theorem Wsummand_atomicTest (Z : ZeroConfig) (hg : Continuous g) (hgc : HasCompactSupport g)
    (N : ℕ) (x : ℕ → ℝ) (ρ : ℂ) :
    Z.Wsummand (cx (atomicTest N x g)) (cx (atomicTest N x g)) ρ =
      (Z.mult ρ : ℂ) * (paperFT (cx g) (gammaOf ρ) * conj (paperFT (cx g) (conj (gammaOf ρ)))) *
        (dirichletPoly N x (gammaOf ρ) * conj (dirichletPoly N x (conj (gammaOf ρ)))) := by
  rw [ZeroConfig.Wsummand, paperFT_atomicTest hg hgc, paperFT_atomicTest hg hgc, map_mul]
  ring

/-- **Zeros on the line are squares**: for `Re ρ = ½` the summand is
`m_ρ |h_g(γ_ρ)|² |D_x(γ_ρ)|²`. -/
theorem Wsummand_atomicTest_onLine (Z : ZeroConfig) (hg : Continuous g)
    (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    Z.Wsummand (cx (atomicTest N x g)) (cx (atomicTest N x g)) ρ =
      (Z.mult ρ : ℂ) * ((‖paperFT (cx g) (gammaOf ρ)‖ ^ 2 : ℝ) : ℂ) *
        ((‖dirichletPoly N x (gammaOf ρ)‖ ^ 2 : ℝ) : ℂ) := by
  have hreal : conj (gammaOf ρ) = gammaOf ρ := by
    rw [Complex.conj_eq_iff_im]
    simp [gammaOf, Complex.div_I, hρ]
  rw [Wsummand_atomicTest Z hg hgc, hreal, Complex.mul_conj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
