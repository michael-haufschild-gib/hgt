import GaloisForLFunctions.RHTower.FinitePrimeBoundaryTransfer
import GaloisForLFunctions.RHTower.PrimeSuperspaceWickAnisotropy
import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# Hedenmalm prime-normal Wick boundary energy

The source-normal theta-interval multiplier at a prime `p` is, after removal of the harmless
common root coordinate,

`b_p(z) = 2 p⁻¹ᐟ² sin(z log(p) / 2)`.

This file formalizes its squared finite-row energy.  The central identity is exact: the complex
row decomposes into the already formalized vertical trigonometric prime-clock energy plus the
radial hyperbolic reflected energy.  Consequently, sub-`log²` growth forces zero imaginary part.

The final theorem is only a consumer.  Its hypothesis says that every `XiC` zero already lies in
this sub-`log²` source-normal boundary domain; constructing that closed source-domain descent is
the remaining analytic problem.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Squared finite-row energy of the source-normal Hedenmalm prime multipliers. -/
def hedenmalmPrimeNormalEnergy (N : ℕ) (z : ℂ) : ℝ :=
  ∑ p ∈ Nat.primesLE N,
    4 * ‖Complex.sin (z * (Real.log p / 2 : ℝ))‖ ^ 2 / p

/-- Complex sine separates exactly into trigonometric and hyperbolic squared components. -/
lemma norm_sq_complex_sin_eq (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sin_eq]
  simp only [Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
    Complex.sinh_ofReal_re, Complex.sinh_ofReal_im,
    Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, zero_mul, add_zero,
    Complex.add_im, Complex.mul_im, zero_add, mul_one]
  nlinarith [Real.sin_sq_add_cos_sq z.re, Real.cosh_sq_sub_sinh_sq z.im]

/-- **Exact cross-chart Wick decomposition.**  The source-normal Hedenmalm prime row is the sum
of the corpus vertical clock energy and radial reflected energy, term by term. -/
theorem hedenmalmPrimeNormalEnergy_eq_vertical_add_radial (N : ℕ) (z : ℂ) :
    hedenmalmPrimeNormalEnergy N z =
      primeClockVerticalEnergy N z.re + primeClockCutoffEnergy N (z.im / 2) := by
  rw [hedenmalmPrimeNormalEnergy, primeClockVerticalEnergy,
    primeClockCutoffEnergy_eq_sinh, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [norm_sq_complex_sin_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.mul_im]
  ring_nf

/-- Any radial displacement pays at least its Fisher-susceptibility cost in the prime-normal
energy. -/
theorem im_sq_mul_primeClockSusceptibility_le_hedenmalmPrimeNormalEnergy
    (N : ℕ) (z : ℂ) :
    z.im ^ 2 * primeClockSusceptibility N ≤ hedenmalmPrimeNormalEnergy N z := by
  rw [hedenmalmPrimeNormalEnergy_eq_vertical_add_radial]
  have hradial := primeClockCutoffEnergy_quadratic_lower N (z.im / 2)
  have hvertical := primeClockVerticalEnergy_nonneg N z.re
  nlinarith

/-- The `o(log² N)` finite-domain condition for one source-normal prime row. -/
def HedenmalmPrimeNormalSubLogSquare (z : ℂ) : Prop :=
  Tendsto (fun N : ℕ => hedenmalmPrimeNormalEnergy N z / Real.log N ^ 2)
    atTop (𝓝 0)

/-- Sub-`log²` source-normal energy forces a point onto the real centered axis. -/
theorem im_eq_zero_of_hedenmalmPrimeNormalSubLogSquare
    {z : ℂ} (h : HedenmalmPrimeNormalSubLogSquare z) :
    z.im = 0 := by
  have hradial : Tendsto
      (fun N : ℕ => primeClockCutoffEnergy N (z.im / 2) / Real.log N ^ 2)
      atTop (𝓝 0) := by
    have hnonneg : ∀ᶠ N : ℕ in atTop,
        0 ≤ primeClockCutoffEnergy N (z.im / 2) / Real.log N ^ 2 :=
      Eventually.of_forall fun N =>
        div_nonneg (primeClockCutoffEnergy_nonneg N (z.im / 2)) (sq_nonneg _)
    have hle : ∀ᶠ N : ℕ in atTop,
        primeClockCutoffEnergy N (z.im / 2) / Real.log N ^ 2 ≤
          hedenmalmPrimeNormalEnergy N z / Real.log N ^ 2 := by
      filter_upwards with N
      rw [hedenmalmPrimeNormalEnergy_eq_vertical_add_radial]
      exact div_le_div_of_nonneg_right
        (le_add_of_nonneg_left (primeClockVerticalEnergy_nonneg N z.re)) (sq_nonneg _)
    exact squeeze_zero' hnonneg hle h
  have hzero :=
    tendsto_horizontalDisplacement_zero_of_energy_div_log_sq_tendsto_zero
      (fun _ : ℕ => z.im / 2) hradial
  have heq : z.im / 2 = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
  linarith

/-- Zero-fibre consumer of the still-open source-domain strict-descent theorem: every centered Xi
root has sub-`log²` source-normal prime energy.  This proposition is not itself a construction of
that descent and is kept visibly zero-specialized to prevent circular interpretation. -/
def XiCZeroHedenmalmPrimeNormalSubLogSquare : Prop :=
  ∀ z : ℂ, XiC z = 0 → HedenmalmPrimeNormalSubLogSquare z

/-- **RH consumer.**  Sub-`log²` source-normal prime energy at every `XiC` zero implies the
Riemann hypothesis.  A genuine strict source-domain descent would prove this premise, but the
premise alone is only an explicit zero-fibre criterion. -/
theorem riemannHypothesis_of_xiCZeroHedenmalmPrimeNormalSubLogSquare
    (h : XiCZeroHedenmalmPrimeNormalSubLogSquare) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  let z : ℂ := (rho - 1 / 2) * (-Complex.I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * Complex.I = rho := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-Complex.I) * Complex.I = (1 : ℂ) := by
        rw [neg_mul, Complex.I_mul_I]
        ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have him : z.im = 0 :=
    im_eq_zero_of_hedenmalmPrimeNormalSubLogSquare (h z hXiC)
  have hzIm : z.im = 1 / 2 - rho.re := by simp [z]
  have hre : rho.re = 1 / 2 := by linarith
  exact (ne_of_gt (mem_rightHalf.mp hrho)) hre

end

end RHTower
