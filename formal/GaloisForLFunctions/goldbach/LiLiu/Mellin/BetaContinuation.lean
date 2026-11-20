import GaloisForLFunctions.goldbach.LiLiu.ArithmeticKernel
import GaloisForLFunctions.goldbach.LiLiu.Mellin.BetaFactorization

/-! # Agreement of the continued arithmetic model with the three Beta integrals -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex
noncomputable section

/-- Multiplying by the Mellin dilation recovers the density series times the signed Beta factor. -/
theorem scaled_betaModel {N : ℕ} (hN : 0 < N) {s z : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1/2) (hz : 0 < z.re) (hz' : z.re < 1/2) :
    (N:ℂ)^(s+z) * betaModel N s z =
      ((singularSeries N : ℂ) * riemannZeta (s+z) * densityEuler N (s+z)) * signedBeta s z := by
  let w := s+z
  have hw : 0 < w.re := add_pos hs hz
  have hw' : w.re < 1 := by change s.re+z.re < 1; linarith only [hs',hz']
  have hζ := riemannZeta_one_sub (s := w) (fun k h => by
    rw [h, neg_re, natCast_re] at hw
    linarith only [hw,Nat.cast_nonneg (α := ℝ) k]) (fun h => by simp [h] at hw')
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hp : (Real.pi:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hscale : (N:ℂ)^w * ((Real.pi / N : ℝ):ℂ)^w = (Real.pi:ℂ)^w := by
    have h := Complex.mul_cpow_ofReal_nonneg hn.le (div_nonneg Real.pi_pos.le hn.le) w
    rw [← Complex.ofReal_mul, show (N:ℝ)*(Real.pi/N) = Real.pi by field_simp,
      Complex.ofReal_natCast] at h
    exact h.symm
  have hpi : (2*(Real.pi:ℂ))^(-w) = (2:ℂ)^(-w) * (Real.pi:ℂ)^(-w) := by
    simpa only [Complex.ofReal_ofNat] using Complex.mul_cpow_ofReal_nonneg
      (by norm_num : (0:ℝ) ≤ 2) Real.pi_pos.le (-w)
  have htwo : (2:ℂ)^(1-w) = 2 * (2:ℂ)^(-w) := by
    rw [sub_eq_add_neg, cpow_add _ _ (by norm_num), cpow_one]
  have hcancel : (Real.pi:ℂ)^w * (Real.pi:ℂ)^(-w) = 1 := by
    rw [← cpow_add _ _ hp, add_neg_cancel, cpow_zero]
  rw [signedBeta_factorization hs hs' hz hz', betaModel]
  change (N:ℂ)^w * (_ * ((Real.pi/N:ℝ):ℂ)^w * _ * riemannZeta (1-w) * _ * _) =
    _ * ((2:ℂ)^(1-w) * _ * _ * _ * _)
  rw [hζ, hpi, htwo]
  calc
    _ = ((N:ℂ)^w * ((Real.pi/N:ℝ):ℂ)^w) * (Real.pi:ℂ)^(-w) *
        ((singularSeries N : ℂ) * riemannZeta w * densityEuler N w *
          (2*(2:ℂ)^(-w) * Gamma w * cos (Real.pi*w/2) * signedBetaGammaFactor s *
            signedBetaGammaFactor z)) := by ring
    _ = _ := by rw [hscale,hcancel,one_mul]

#print axioms scaled_betaModel
end
end GaloisForLFunctions.Goldbach.LiLiu
