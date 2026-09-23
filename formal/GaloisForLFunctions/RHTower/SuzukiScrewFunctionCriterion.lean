import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewHilbert
import GaloisForLFunctions.RHTower.SuzukiScrewPointwiseNonnegativityCriterion
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Suzuki's screw-function criterion

This module formalizes Theorem 1.2 of Suzuki, *Aspects of the screw function corresponding to
the Riemann zeta-function* (arXiv:2206.03682).  The definitions below are the literal ones from
equations (1.4), (1.5), and (1.8): `g = -Psi`,

```text
G_g(t,u) = g(t-u) - g(t) - g(-u) + g(0),
```

and a screw function on the real line is continuous, Hermitian, and has positive-semidefinite
kernel on every finite set.

On RH, the exact zero series realizes `G_g` as a complex Gram kernel.  Because `G_g` is real,
the usual complex screw embedding alone only exposes its real inner product.  The doubled feature
`(V(t), conj V(t))` converts that real part into a genuine complex Gram matrix, retaining the full
complex-coefficient positivity required by Suzuki's definition.  Conversely, one-point kernel
positivity gives `2 * Psi(t) >= 0`; the already formalized literal pointwise criterion then gives
RH.
-/

open Complex
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Suzuki's function `g = -Psi`, equation (1.8), regarded as complex-valued. -/
def suzukiScrewG (t : ℝ) : ℂ :=
  -(suzukiPsi t : ℂ)

/-- Suzuki's kernel `G_g`, equation (1.4). -/
def suzukiScrewKernel (t u : ℝ) : ℂ :=
  suzukiScrewG (t - u) - suzukiScrewG t - suzukiScrewG (-u) + suzukiScrewG 0

/-- Finite restriction of Suzuki's kernel in the source order `G_g(t_i,t_j)`. -/
def suzukiScrewKernelMatrix {n : ℕ} (point : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => suzukiScrewKernel (point i) (point j)

/-- Exact class-membership assertion `g in G_infinity`: continuity, Hermitian symmetry, and
positive semidefiniteness of every finite kernel restriction. -/
def SuzukiScrewFunctionOnReal : Prop :=
  Continuous suzukiScrewG ∧
    (∀ t : ℝ, suzukiScrewG (-t) = star (suzukiScrewG t)) ∧
    ∀ (n : ℕ) (point : Fin n → ℝ), (suzukiScrewKernelMatrix point).PosSemidef

@[simp] theorem suzukiPsi_zero : suzukiPsi 0 = 0 := by
  have h := ofReal_suzukiPsi_eq_xiScrewDivisor_all 0
  rw [xiScrewDivisor_zero] at h
  exact_mod_cast h

@[simp] theorem suzukiScrewG_zero : suzukiScrewG 0 = 0 := by
  simp [suzukiScrewG]

/-- The literal source function has the required Hermitian symmetry. -/
theorem suzukiScrewG_hermitian (t : ℝ) :
    suzukiScrewG (-t) = star (suzukiScrewG t) := by
  simp [suzukiScrewG]

/-- Diagonal of Suzuki's kernel is exactly `2 * Psi`. -/
theorem suzukiScrewKernel_self (t : ℝ) :
    suzukiScrewKernel t t = ((2 * suzukiPsi t : ℝ) : ℂ) := by
  simp [suzukiScrewKernel, suzukiScrewG]
  ring

/-- On RH the literal prime--Lerch source function is the real critical-zero screw series, on
the full even extension used in Suzuki's paper. -/
theorem suzukiPsi_eq_xiCriticalScrewSeries_of_rh
    (hRH : RiemannHypothesis) (t : ℝ) :
    suzukiPsi t = xiCriticalScrewSeries t := by
  calc
    suzukiPsi t = ((suzukiPsi t : ℂ)).re := by simp
    _ = (xiScrewDivisor t).re := by
      rw [ofReal_suzukiPsi_eq_xiScrewDivisor_all]
    _ = xiCriticalScrewSeries t :=
      xiScrewDivisor_re_eq_xiCriticalScrewSeries_of_rh hRH t

/-- RH-side Hilbert screw point carrying the critical Xi zero multiset. -/
def xiCriticalScrewHilbertPoint (hRH : RiemannHypothesis) (t : ℝ) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  screwEmbed xiCriticalScrewWeight_nonneg
    (summable_xiCriticalScrewWeight_of_rh hRH)
    (screwPhase xiRealSpectralPoint t)

@[simp] theorem xiCriticalScrewHilbertPoint_zero (hRH : RiemannHypothesis) :
    xiCriticalScrewHilbertPoint hRH 0 = 0 := by
  apply lp.ext
  funext q
  simp [xiCriticalScrewHilbertPoint, screwEmbed, screwEmbedFun, screwPhase]

/-- Squared Hilbert chord length is the exact critical-zero screw series. -/
theorem sq_norm_xiCriticalScrewHilbertPoint_sub
    (hRH : RiemannHypothesis) (t u : ℝ) :
    ‖xiCriticalScrewHilbertPoint hRH t - xiCriticalScrewHilbertPoint hRH u‖ ^ (2 : ℕ) =
      xiCriticalScrewSeries (t - u) := by
  exact sq_norm_screwEmbed_screwPhase_sub xiCriticalScrewWeight_nonneg
    (summable_xiCriticalScrewWeight_of_rh hRH) xiRealSpectralPoint t u

/-- Conjugating both vectors in this coordinatewise complex `l2` model conjugates the inner
product. -/
theorem inner_star_xiCriticalScrewLp
    (x y : lp (fun _ : XiZeroCopy => ℂ) 2) :
    inner ℂ (star x) (star y) = star (inner ℂ x y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, tsum_star]
  apply tsum_congr
  intro q
  simp [lp.star_apply]

private theorem complex_add_star_eq_two_re (z : ℂ) :
    z + star z = ((2 * z.re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
    ring
  · simp

/-- Doubled feature whose complex inner product is twice the real part of the original screw
inner product. -/
def xiCriticalScrewDoubledPoint (hRH : RiemannHypothesis) (t : ℝ) :
    WithLp 2
      (lp (fun _ : XiZeroCopy => ℂ) 2 × lp (fun _ : XiZeroCopy => ℂ) 2) :=
  WithLp.toLp 2
    (xiCriticalScrewHilbertPoint hRH t, star (xiCriticalScrewHilbertPoint hRH t))

theorem inner_xiCriticalScrewDoubledPoint
    (hRH : RiemannHypothesis) (t u : ℝ) :
    inner ℂ (xiCriticalScrewDoubledPoint hRH t)
        (xiCriticalScrewDoubledPoint hRH u) =
      ((2 * (inner ℂ (xiCriticalScrewHilbertPoint hRH t)
        (xiCriticalScrewHilbertPoint hRH u)).re : ℝ) : ℂ) := by
  rw [WithLp.prod_inner_apply]
  simp only [xiCriticalScrewDoubledPoint, WithLp.ofLp_toLp]
  rw [inner_star_xiCriticalScrewLp]
  exact complex_add_star_eq_two_re _

/-- Under RH, Suzuki's literal kernel is the doubled Hilbert screw inner product. -/
theorem suzukiScrewKernel_eq_inner_of_rh
    (hRH : RiemannHypothesis) (t u : ℝ) :
    suzukiScrewKernel t u =
      inner ℂ (xiCriticalScrewDoubledPoint hRH t)
        (xiCriticalScrewDoubledPoint hRH u) := by
  have htu := sq_norm_xiCriticalScrewHilbertPoint_sub hRH t u
  have ht0 := sq_norm_xiCriticalScrewHilbertPoint_sub hRH t 0
  have hu0 := sq_norm_xiCriticalScrewHilbertPoint_sub hRH u 0
  have ht : ‖xiCriticalScrewHilbertPoint hRH t‖ ^ (2 : ℕ) =
      xiCriticalScrewSeries t := by
    simpa using ht0
  have hu : ‖xiCriticalScrewHilbertPoint hRH u‖ ^ (2 : ℕ) =
      xiCriticalScrewSeries u := by
    simpa using hu0
  rw [inner_xiCriticalScrewDoubledPoint]
  have hkernel : suzukiScrewKernel t u =
      ((-suzukiPsi (t - u) + suzukiPsi t + suzukiPsi u : ℝ) : ℂ) := by
    simp [suzukiScrewKernel, suzukiScrewG]
  rw [hkernel]
  congr 1
  rw [suzukiPsi_eq_xiCriticalScrewSeries_of_rh hRH,
    suzukiPsi_eq_xiCriticalScrewSeries_of_rh hRH,
    suzukiPsi_eq_xiCriticalScrewSeries_of_rh hRH]
  rw [← htu, ← ht, ← hu, norm_sub_sq (𝕜 := ℂ)]
  have hre : RCLike.re (inner ℂ (xiCriticalScrewHilbertPoint hRH t)
      (xiCriticalScrewHilbertPoint hRH u)) =
      (inner ℂ (xiCriticalScrewHilbertPoint hRH t)
        (xiCriticalScrewHilbertPoint hRH u)).re := rfl
  rw [hre]
  ring

/-- Every finite Suzuki kernel restriction is the Gram matrix of the doubled Xi screw feature. -/
theorem suzukiScrewKernelMatrix_eq_gram_of_rh
    (hRH : RiemannHypothesis) {n : ℕ} (point : Fin n → ℝ) :
    suzukiScrewKernelMatrix point =
      Matrix.gram ℂ (fun i => xiCriticalScrewDoubledPoint hRH (point i)) := by
  ext i j
  rw [suzukiScrewKernelMatrix, Matrix.gram_apply,
    suzukiScrewKernel_eq_inner_of_rh]

theorem continuous_suzukiScrewG_of_rh (hRH : RiemannHypothesis) :
    Continuous suzukiScrewG := by
  have hpsi : Continuous suzukiPsi :=
    (xiCriticalScrewSeries_continuous_of_rh hRH).congr
      (fun t => (suzukiPsi_eq_xiCriticalScrewSeries_of_rh hRH t).symm)
  change Continuous (fun t : ℝ => -(suzukiPsi t : ℂ))
  exact (Complex.continuous_ofReal.comp hpsi).neg

/-- RH makes Suzuki's literal `g = -Psi` a screw function on the whole real line. -/
theorem suzukiScrewFunctionOnReal_of_riemannHypothesis
    (hRH : RiemannHypothesis) : SuzukiScrewFunctionOnReal := by
  refine ⟨continuous_suzukiScrewG_of_rh hRH, suzukiScrewG_hermitian, ?_⟩
  intro n point
  rw [suzukiScrewKernelMatrix_eq_gram_of_rh hRH]
  exact Matrix.posSemidef_gram ℂ _

/-- Finite kernel positivity, already at one point at a time, forces nonnegativity of Suzuki's
literal `Psi` and hence RH. -/
theorem riemannHypothesis_of_suzukiScrewFunctionOnReal
    (hsource : SuzukiScrewFunctionOnReal) : RiemannHypothesis := by
  apply riemannHypothesis_of_suzukiPsiPointwiseNonnegative
  intro t _ht
  have hpsd := hsource.2.2 1 (fun _ : Fin 1 => t)
  have hd := hpsd.diag_nonneg (i := (0 : Fin 1))
  rw [suzukiScrewKernelMatrix, suzukiScrewKernel_self,
    Complex.le_def, Complex.zero_re, Complex.zero_im] at hd
  norm_num at hd
  exact hd

/-- **Suzuki 2022, Theorem 1.2.**  The Riemann hypothesis is equivalent to the paper's literal
function `g = -Psi` being a screw function on the full real line. -/
theorem riemannHypothesis_iff_suzukiScrewFunctionOnReal :
    RiemannHypothesis ↔ SuzukiScrewFunctionOnReal :=
  ⟨suzukiScrewFunctionOnReal_of_riemannHypothesis,
    riemannHypothesis_of_suzukiScrewFunctionOnReal⟩

end

end RHTower
