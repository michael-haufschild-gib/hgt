import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.Discriminant

/-! # Gaussian lower tails for polynomials with Gaussian-integer coefficients -/
open MvPolynomial MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- A nonzero integral coefficient has modulus at least one. A total-degree upper
bound therefore controls the small-value probability without a coefficient factor. -/
theorem gaussianInt_sublevel_of_degree_le {n : ℕ} (g : MvPolynomial (Fin n) GaussianInt) (B : ℕ)
    (hg : g.totalDegree ≤ B) (hnz : map GaussianInt.toComplex g ≠ 0)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      {x | ‖eval₂Hom GaussianInt.toComplex (fun i => (x i : ℂ)) g‖ < r^B} ≤
        ENNReal.ofReal (2*(B:ℝ)*r) := by
  let f := map GaussianInt.toComplex g
  have hd : f.totalDegree ≤ B := (show f.totalDegree ≤ g.totalDegree from
    Finset.sup_mono (support_map_subset GaussianInt.toComplex g)).trans hg
  have hev (x : Fin n → ℝ) : eval₂Hom GaussianInt.toComplex (fun i => (x i : ℂ)) g =
      eval (fun i => (x i : ℂ)) f := (eval_map ..).symm
  obtain ⟨a,ha⟩ := lexHeadCoefficient_is_coeff f
  have hc : GaussianInt.toComplex (g.coeff a) = lexHeadCoefficient f := by rw [← ha,show f = map GaussianInt.toComplex g from rfl,coeff_map]
  have hnorm := one_le_gaussianInt_norm (g.coeff a) (by rw [hc]; exact lexHeadCoefficient_ne_zero f hnz)
  change 1 ≤ ‖GaussianInt.toComplex (g.coeff a)‖ at hnorm
  rw [hc] at hnorm
  have hsmall := gaussian_mvPolynomial_sublevel f hnz hr hr'
  apply (measure_mono ?_).trans (hsmall.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro x hx
    change ‖eval (fun i => (x i : ℂ)) f‖ < _
    rw [← hev]
    exact hx.trans_le ((pow_le_pow_of_le_one hr.le hr' hd).trans
      (le_mul_of_one_le_left (pow_nonneg hr.le _) hnorm))
  · gcongr

end
end GaloisForLFunctions.HTGeometry.SpectralJets
