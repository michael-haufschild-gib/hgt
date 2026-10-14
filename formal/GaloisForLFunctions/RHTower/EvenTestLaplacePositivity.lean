import GaloisForLFunctions.RHTower.XiShiftedGammaFamily
import GaloisForLFunctions.RHTower.ThetaRelativeSourceRigidity
import GaloisForLFunctions.RHTower.WeilBlindPoleSignLaw

/-!
# Even tests are positive on the whole imaginary axis

For a test `f` write `𝓛_f(z) = f̂(z) · conj(f̂(z̄))`.  For a continuous compactly supported `f` this
is the Fourier transform of the autocorrelation `f ⋆ f̃` at `z` (`EF.paperFT_weilTest`); at
`z = ±i/2` it gives the pole term.

* `laplacePairing_I_mul_of_even`: for an even `f`, `𝓛_f(iy) = |f̂(iy)|² ≥ 0` for every real `y`.
  So every nonnegative combination of autocorrelations of even tests has a Fourier transform that
  is `≥ 0` on `ℝ ∪ iℝ`, not only on `ℝ`.
* `laplacePairing_xiShiftedGammaTest_neg`: for the shifted-Gamma tests `F_j` with
  `F̂_j = Ξ Q_j`, `Q_j(τ) = ∏_{k<j} (k + ¼ + iτ/2)`, every `j ≥ 1` and every `½ < y < ¾`,
  `𝓛_{F_j}(iy) = Ξ(iy)² ∏_{k<j} (k + ¼ − y/2)(k + ¼ + y/2) < 0`.  The factor `k = 0` is the only
  negative one.

So the positivity of even autocorrelations on `iℝ` is violated by every `F_j` with `j ≥ 1`.
Positivity restricted to even tests is the positivity of a cosine-type (hypergroup) spectral
problem, with spectrum on `ℝ ∪ iℝ`.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower.EvenSector

/-- The two exponential moments of an even test coincide at opposite points. -/
theorem paperFT_neg_of_even {f : ℝ → ℂ} (heven : ∀ x, f (-x) = f x) (z : ℂ) :
    paperFT f (-z) = paperFT f z := by
  rw [paperFT_def, paperFT_def, ← integral_neg_eq_self]
  congr 1; funext u
  rw [heven]; congr 1; push_cast; ring_nf

/-- **Even tests are positive on the imaginary axis.**  For an even `f` and real `y`,
`f̂(iy) · conj(f̂(conj(iy))) = |f̂(iy)|²`. -/
theorem laplacePairing_I_mul_of_even {f : ℝ → ℂ} (heven : ∀ x, f (-x) = f x) (y : ℝ) :
    paperFT f (I * y) * conj (paperFT f (conj (I * y))) =
      ((‖paperFT f (I * y)‖ ^ 2 : ℝ) : ℂ) := by
  have hc : conj (I * (y : ℂ)) = -(I * y) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [hc, paperFT_neg_of_even heven, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The autocorrelation of an even test has nonnegative Fourier transform on the imaginary
axis. -/
theorem paperFT_weilTest_I_mul_of_even {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (heven : ∀ x, f (-x) = f x) (y : ℝ) :
    paperFT (EF.weilTest f f) (I * y) = ((‖paperFT f (I * y)‖ ^ 2 : ℝ) : ℂ) := by
  rw [EF.paperFT_weilTest hf hf hfc hfc]
  exact laplacePairing_I_mul_of_even heven y

theorem shiftedGammaPoly_I_mul (j : ℕ) (y : ℝ) :
    WeilSpectral.shiftedGammaPoly j (I * y) =
      ((∏ k ∈ Finset.range j, ((k : ℝ) + 1 / 4 - y / 2) : ℝ) : ℂ) := by
  unfold WeilSpectral.shiftedGammaPoly
  push_cast
  refine Finset.prod_congr rfl fun k _ => ?_
  have : I * (I * (y : ℂ)) / 2 = -(y : ℂ) / 2 := by
    rw [← mul_assoc, Complex.I_mul_I]; ring
  rw [this]; ring

/-- **The shifted-Gamma tests are negative on the imaginary axis.**  For `j ≥ 1` and
`½ < y < ¾`, `F̂_j(iy) · conj(F̂_j(conj(iy))) < 0`. -/
theorem laplacePairing_xiShiftedGammaTest_neg {j : ℕ} (hj : 1 ≤ j) {y : ℝ} (hy1 : 1 / 2 < y)
    (hy2 : y < 3 / 4) :
    (paperFT (fun u => (WeilSpectral.xiShiftedGammaTest j u : ℂ)) (I * y) *
      conj (paperFT (fun u => (WeilSpectral.xiShiftedGammaTest j u : ℂ)) (conj (I * y)))).re <
        0 := by
  have hc : conj (I * (y : ℂ)) = I * ((-y : ℝ) : ℂ) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
  have him1 : |(I * (y : ℂ)).im| < 3 / 4 := by
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add]
    rw [abs_of_pos (by linarith)]; exact hy2
  have him2 : |(I * ((-y : ℝ) : ℂ)).im| < 3 / 4 := by
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add]
    rw [abs_neg, abs_of_pos (by linarith)]; exact hy2
  rw [hc, WeilSpectral.paperFT_xiShiftedGammaTest j him1,
    WeilSpectral.paperFT_xiShiftedGammaTest j him2]
  unfold WeilSpectral.xiShiftedGamma
  rw [XiC_I_mul, XiC_I_mul, shiftedGammaPoly_I_mul, shiftedGammaPoly_I_mul]
  simp only [← Complex.ofReal_mul, Complex.conj_ofReal, Complex.ofReal_re]
  -- the signs of the factors
  have hL1 := thetaSourceLaplace_pos y
  have hL2 := thetaSourceLaplace_pos (-y)
  have hneg : ∏ k ∈ Finset.range j, ((k : ℝ) + 1 / 4 - y / 2) < 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    rw [Finset.prod_range_succ']
    have hpos : 0 < ∏ k ∈ Finset.range m, (((k + 1 : ℕ) : ℝ) + 1 / 4 - y / 2) :=
      Finset.prod_pos fun k _ => by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h0 : ((0 : ℕ) : ℝ) + 1 / 4 - y / 2 < 0 := by push_cast; linarith
    exact mul_neg_of_pos_of_neg hpos h0
  have hpos' : 0 < ∏ k ∈ Finset.range j, ((k : ℝ) + 1 / 4 - -y / 2) :=
    Finset.prod_pos fun k _ => by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have := mul_pos hL1 hL2
  nlinarith [mul_pos this hpos']

end RHTower.EvenSector

end
