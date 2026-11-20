import GaloisForLFunctions.goldbach.LiLiu.ArithmeticKernel
import GaloisForLFunctions.goldbach.LiLiu.Arithmetic.EulerBounds

/-! # Hermitian symmetry of the arithmetic boundary kernel -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex
open scoped ComplexConjugate Classical
noncomputable section

theorem characterKernel_hermitian (N : ℕ) [NeZero N] (s z : ℂ) :
    conj (characterKernel N z s) = characterKernel N s z := by
  simp only [characterKernel, map_mul, map_div₀, map_ofNat, map_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  change conj (characterFeature χ z * conj (characterFeature χ s)) =
    characterFeature χ s * conj (characterFeature χ z)
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem diagonalSeries_conj (N : ℕ) (w : ℂ) : diagonalSeries N (conj w) = conj (diagonalSeries N w) := by
  simp only [diagonalSeries, LSeries, Complex.conj_tsum]
  apply tsum_congr
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hc : conj (diagonalCoefficient N n) = diagonalCoefficient N n := by
    unfold diagonalCoefficient
    split_ifs <;> simp
  rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', map_div₀, hc]
  congr 1
  rw [show 1 + conj w = conj (1 + w) by simp]
  simpa only [Complex.ofReal_natCast] using
    _root_.RHTower.GaussZeroSum.ofReal_cpow_conj (Nat.cast_pos.mpr hn) (1+w)

theorem signedBetaGammaFactor_conj (s : ℂ) : signedBetaGammaFactor (conj s) = conj (signedBetaGammaFactor s) := by
  unfold signedBetaGammaFactor
  rw [map_div₀, ← Complex.Gamma_conj, ← Complex.Gamma_conj]
  simp

theorem betaModel_comm (N : ℕ) (s z : ℂ) : betaModel N s z = betaModel N z s := by
  simp only [betaModel, add_comm z s]
  ring

theorem betaModel_conj {N : ℕ} (hN : 0 < N) {s z : ℂ} (hw : 0 < (s+z).re) :
    betaModel N (conj s) (conj z) = conj (betaModel N s z) := by
  have hp : 0 < Real.pi / N := div_pos Real.pi_pos (Nat.cast_pos.mpr hN)
  simp only [betaModel, ← map_add, map_mul, Complex.conj_ofReal, signedBetaGammaFactor_conj,
    densityEuler_conj N hw, _root_.RHTower.GaussZeroSum.ofReal_cpow_conj hp, ← riemannZeta_conj]
  rw [map_sub, map_one]

/-- The denominator in the Hardy action is conjugated in the input variable. -/
def boundaryKernel (N : ℕ) [NeZero N] (s z : ℂ) : ℂ :=
  residualKernel N s z / ((1+s) * (1+conj z))

theorem residualKernel_hermitian (N : ℕ) [NeZero N] {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    conj (residualKernel N z s) = residualKernel N s z := by
  change conj (characterKernel N z s - diagonalSeries N (z + conj s) - betaModel N z (conj s)) =
    characterKernel N s z - diagonalSeries N (s + conj z) - betaModel N s (conj z)
  have hw : 0 < (z + conj s).re := by simpa using add_pos hz hs
  rw [map_sub, map_sub, characterKernel_hermitian, ← diagonalSeries_conj,
    ← betaModel_conj (NeZero.pos N) hw, map_add, Complex.conj_conj, add_comm (conj z) s,
    betaModel_comm]

theorem boundaryKernel_hermitian (N : ℕ) [NeZero N] {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    conj (boundaryKernel N z s) = boundaryKernel N s z := by
  simp only [boundaryKernel, map_div₀, residualKernel_hermitian N hs hz, map_mul, map_add,
    map_one, Complex.conj_conj, mul_comm]

#print axioms boundaryKernel_hermitian
end
end GaloisForLFunctions.Goldbach.LiLiu
