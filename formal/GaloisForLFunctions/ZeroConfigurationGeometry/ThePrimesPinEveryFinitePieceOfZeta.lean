import GaloisForLFunctions.ZeroConfigurationGeometry.FiniteModificationsAreSeenAtEveryAperture
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares
import GaloisForLFunctions.SquareRootThreshold.OnLineShadowIndistinguishability

/-!
# The primes pin every finite piece of the zeros of `ζ`

The **arithmetic image** of a window `f` with arithmetic data `λ : ℕ → ℝ` is the full Weil
functional of `f ⋆ f̃` (`RHTower.weilFullFunctional`): the pole terms at `±i/2`, the prime sum
`Σ_n λ(n) n^{−1/2} (k(log n) + k(−log n))` and the archimedean integral. For `λ = Λ` it is the image
of the zeros of `ζ` (`zetaZeroConfig_W_eq_weilFullFunctional_bilinear`, unconditional).

* **The camera of aperture `r` reads only the primes below `e^{2r}`**
  (`arithmeticImage_congr_of_eq_below`). The kernel `f ⋆ f̃` vanishes at `±log n` once
  `log n ≥ 2r`, so two data agreeing on `n < e^{2r}` have the same arithmetic image on windows of
  aperture `r`.
* **The primes pin every finite piece** (`eq_zeta_of_arithmeticImage_of_finite`). A tempered
  configuration that differs from the zeros of `ζ` in finitely many points and whose image on the
  windows of one aperture `r > 0` is produced by any arithmetic data agreeing with `Λ` below
  `e^{2r}` is the configuration of `ζ`.

Together with `no_bounded_aperture_excludes_eulerColumns` this is the dichotomy of the field:
finite rearrangements of the zeros are fixed by finitely many primes at every aperture, while the
arithmetic fakes that hide (Euler columns, lattices) are infinite modifications.
-/

open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- The **arithmetic image** of the window `f` with arithmetic data `λ`. -/
def arithmeticImage (lam : ℕ → ℝ) (f : ℝ → ℂ) : ℂ :=
  _root_.RHTower.weilFullFunctional lam (EF.weilTest f f)

/-- The image of the zeros of `ζ` is the arithmetic image of `Λ`. -/
theorem zeta_W_eq_arithmeticImage {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    zetaZeroConfig.W f f = arithmeticImage (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f :=
  _root_.RHTower.zetaZeroConfig_W_eq_weilFullFunctional_bilinear hf hfc hf hfc

/-- **The camera of aperture `r` reads only the data below `e^{2r}`.** -/
theorem arithmeticImage_congr_of_eq_below {lam lam' : ℕ → ℝ} {r : ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → Real.log n < 2 * r → lam n = lam' n) {f : ℝ → ℂ}
    (hf : ApertureWindow r f) : arithmeticImage lam f = arithmeticImage lam' f := by
  simp only [arithmeticImage, _root_.RHTower.weilFullFunctional]
  congr 2
  refine tsum_congr fun n => ?_
  by_cases hn : 2 ≤ n
  · by_cases hlog : Real.log n < 2 * r
    · rw [h n hn hlog]
    · have hle : 2 * r ≤ Real.log n := not_lt.mp hlog
      have hpos : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      rw [weilTest_eq_zero_of_two_mul_le hf.1.continuous hf.2 (v := Real.log n)
          (by rw [abs_of_nonneg hpos]; exact hle),
        weilTest_eq_zero_of_two_mul_le hf.1.continuous hf.2 (v := -Real.log n)
          (by rw [abs_neg, abs_of_nonneg hpos]; exact hle)]
      simp
  · simp [hn]

/-- **The primes pin every finite piece of the zeros of `ζ`.** -/
theorem eq_zeta_of_arithmeticImage_of_finite {Z : ZeroConfig} (hZ : TemperedConfig Z)
    (hfin : {z | multDiff Z zetaZeroConfig z ≠ 0}.Finite) {r : ℝ} (hr : 0 < r)
    {lam : ℕ → ℝ}
    (hlam : ∀ n : ℕ, 2 ≤ n → Real.log n < 2 * r → lam n = ArithmeticFunction.vonMangoldt n)
    (hW : ∀ f, ApertureWindow r f → Z.W f f = arithmeticImage lam f) :
    Z.carrier = zetaZeroConfig.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = zetaZeroConfig.mult ρ := by
  refine zeta_finite_modification_seen hZ hfin hr fun f hf => ?_
  rw [hW f hf, arithmeticImage_congr_of_eq_below hlam hf,
    zeta_W_eq_arithmeticImage hf.1 hf.hasCompactSupport]

end GaloisForLFunctions.ZeroConfigurationGeometry
