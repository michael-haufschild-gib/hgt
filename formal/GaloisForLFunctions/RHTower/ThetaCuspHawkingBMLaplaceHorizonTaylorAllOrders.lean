import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceHorizonTaylorBound

/-!
Uniform finite-order horizon Taylor tails for the literal Gauss factor.

The source-pole action lies in `-4 < Re w < -2`; its endpoint continuation needs
the order-three, rather than order-one, horizon subtraction.  This leaf exposes the
arbitrary finite order already carried by the literal hypergeometric series.
-/

namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- On one nonreal-frequency neighbourhood, deleting any fixed finite number of
literal horizon Gauss coefficients gains exactly that number of endpoint powers. -/
theorem horizonGauss_uniform_taylor_bound (w chi : ℂ) (hw : w.im ≠ 0)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (k : ℕ) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧
      ∀ u ∈ ball w R, ∀ z ∈ Icc (0 : ℝ) b,
        ‖gaussFactor u chi false (z : ℂ) -
          ∑ n ∈ Finset.range k,
            ordinaryHypergeometricCoefficient (gaussA u chi) (gaussB u chi) (gaussC u) n *
              (z : ℂ) ^ n‖ ≤ C * z ^ k := by
  obtain ⟨R, B, δ, hR, _, hB, hδ, hp⟩ := horizonGauss_parameter_neighborhood w chi hw
  obtain ⟨N, hN⟩ := exists_nat_ge (B + 1)
  have hsep (u : ℂ) (hu : u ∈ ball w R) (j : ℕ) : δ ≤ ‖gaussC u + j‖ := by
    have hh := Complex.abs_im_le_norm (gaussC u + j)
    simp only [gaussC, Complex.add_im, Complex.one_im, Complex.natCast_im, zero_add, add_zero] at hh
    exact (hp u hu).2.2.2.trans hh
  have hcoef (u : ℂ) (hu : u ∈ ball w R) := gaussParameterMajorant_bound hB hδ
    (hp u hu).1 (hp u hu).2.1 (hp u hu).2.2.1 (hsep u hu) N hN
  have hnonneg (n : ℕ) : 0 ≤ gaussParameterMajorant B δ N n :=
    (norm_nonneg _).trans (hcoef w (mem_ball_self hR) n)
  let C := ∑' n, gaussParameterMajorant B δ N (n + k) * b ^ n
  have hC : 0 ≤ C := tsum_nonneg (fun n => mul_nonneg (hnonneg _) (pow_nonneg hb.le _))
  refine ⟨R, C, hR, hC, ?_⟩
  intro u hu z hz
  have hn : ‖(z : ℂ)‖ ≤ b := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz.1] using hz.2
  have hh := hypergeometric_taylor_remainder_bound hB hδ hb hb1
    (hp u hu).1 (hp u hu).2.1 (hp u hu).2.2.1 (hsep u hu) N hN hn k
  simpa only [ordinaryHypergeometric, gaussFactor, radialSeries, Bool.false_eq_true, ↓reduceIte,
    horizonSeries, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz.1] using hh

/-- The literal source-pole counterterm obtains the required cubic Gauss tail. -/
theorem horizonGauss_uniform_cubic_bound (w chi : ℂ) (hw : w.im ≠ 0)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧
      ∀ u ∈ ball w R, ∀ z ∈ Icc (0 : ℝ) b,
        ‖gaussFactor u chi false (z : ℂ) -
          ∑ n ∈ Finset.range 3,
            ordinaryHypergeometricCoefficient (gaussA u chi) (gaussB u chi) (gaussC u) n *
              (z : ℂ) ^ n‖ ≤ C * z ^ 3 :=
  horizonGauss_uniform_taylor_bound w chi hw hb hb1 3

end
end RHTower.D4BMLaplaceRadial
