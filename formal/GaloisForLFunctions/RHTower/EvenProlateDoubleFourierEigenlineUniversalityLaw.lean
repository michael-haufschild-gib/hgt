import GaloisForLFunctions.RHTower.ProlateDiagonalization
import GaloisForLFunctions.RHTower.SlepianKernelFubini

/-!
# Even prolate double-Fourier eigenline universality law

The Slepian kernel was identified as a composed finite-band Fourier integral on even carriers,
while the prolate commutation route independently showed that the sinc band transform is scalar on
every nonvanishing compact segment of a prolate eigenfunction.  Combining the exact operators—not
only their shared kernel vocabulary—shows that the original double Fourier aperture operator is
itself scalar on every even prolate eigenline.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- **Even prolate double-Fourier eigenline universality law.**  An even `C²` prolate
eigenfunction for bandwidth `2π` is an eigenfunction of the composed unit-aperture band-Fourier
operator on every compact interior interval on which it does not vanish.  One real scalar works at
every point of that interval. -/
theorem evenProlateEigenfunction_doubleBandFourier_smul_on
    {chi : ℝ} {psi : ℝ → ℝ}
    (hpsi1 : Differentiable ℝ psi)
    (hpsi2 : Differentiable ℝ (deriv psi))
    (hpsi2c : Continuous (deriv (deriv psi)))
    (heig : ∀ y, prolateSLAction (2 * Real.pi) psi y = chi * psi y)
    (heven : ∀ t, psi (-t) = psi t)
    {a b : ℝ} (hsub : Set.Icc a b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hne : ∀ y ∈ Set.Icc a b, psi y ≠ 0) :
    ∃ mu : ℝ, ∀ x ∈ Set.Icc a b,
      (∫ y in Set.Icc (-1 : ℝ) 1,
          Complex.exp (-((2 : ℂ) * (Real.pi : ℂ) * (x : ℂ) * (y : ℂ) * Complex.I)) *
            ∫ t in Set.Icc (-1 : ℝ) 1,
              Complex.exp (-((2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * (t : ℂ) * Complex.I)) *
                (psi t : ℂ)) =
        ((mu * psi x : ℝ) : ℂ) := by
  obtain ⟨mu, hmu⟩ := bandTransform_eigen_smul_on
    hpsi1 hpsi2 hpsi2c heig hsub hne
  refine ⟨mu, fun x hx => ?_⟩
  have hg : IntegrableOn (fun t : ℝ => (psi t : ℂ))
      (Set.Icc (-1 : ℝ) 1) volume :=
    (Complex.continuous_ofReal.comp hpsi1.continuous).integrableOn_Icc
  have hdbl := double_integral_fourierChar_eq_sincKernel
    1 x (by norm_num) hg (Filter.Eventually.of_forall fun t => by
      exact_mod_cast heven t)
  norm_num at hdbl
  rw [hdbl]
  have hkernel :
      (∫ t in Set.Icc (-1 : ℝ) 1,
          ((sincKernelSmooth (2 * Real.pi) x t : ℝ) : ℂ) * (psi t : ℂ)) =
        (bandTransform (2 * Real.pi) psi x : ℂ) := by
    rw [bandTransform, intervalIntegral.integral_of_le (by norm_num),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← integral_complex_ofReal]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    norm_num
  rw [hkernel, hmu x hx]

end

end RHTower
