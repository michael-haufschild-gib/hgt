import GaloisForLFunctions.HTGeometry.Probability.ComplexSphereMonomialNorm

/-!
# Radial weights on complex-coordinate powers

Polar integration separates a homogeneous observable from an arbitrary radial profile.
For powers of a complex coordinate, the angular factor is the spherical Mellin moment.
The identity applies to annular cutoffs as well as Gaussian profiles.
-/

open MeasureTheory Set Metric

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Logarithmic radius carries `dr/r` to Lebesgue measure on the line. -/
theorem integral_logRadius_weight (F : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), r ^ (-1 : ℝ) * F (Real.log r)) = ∫ t : ℝ, F t := by
  rw [← Real.range_exp, ← Set.image_univ]
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun r => r ^ (-1 : ℝ) * F (Real.log r))
  rw [h]
  simp only [Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards with t
  rw [abs_of_pos (Real.exp_pos t), smul_eq_mul, Real.log_exp,
    Real.rpow_neg (Real.exp_pos t).le, Real.rpow_one]
  field_simp

/-- A real-homogeneous observable separates from an arbitrary radial profile. -/
theorem integral_real_homogeneous_mul_radial
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (g : E → ℝ) (a : ℝ) (φ : ℝ → ℝ)
    (hg : ∀ (r : ℝ), 0 < r → ∀ x : E, g (r • x) = r ^ a * g x) :
    (∫ x, g x * φ ‖x‖) =
      (∫ ω : sphere (0 : E) 1, g ω.1 ∂volume.toSphere) *
        ∫ r in Ioi (0 : ℝ), r ^ ((Module.finrank ℝ E : ℝ) - 1 + a) * φ r := by
  rw [integral_polar_sphere_radius]
  have he : (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
      g (p.2.1 • p.1.1) * φ ‖p.2.1 • p.1.1‖) =
      fun p => g p.1.1 * (p.2.1 ^ a * φ p.2.1) := by
    funext p
    have hnorm : ‖(p.1.1 : E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
    have hr : (0 : ℝ) < p.2.1 := p.2.2
    simp only [hg _ hr, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hnorm, mul_one]
    ring
  rw [he, integral_prod_mul (fun ω : sphere (0 : E) 1 => g ω.1)
    (fun r : Ioi (0 : ℝ) => r.1 ^ a * φ r.1),
    integral_volumeIoiPow_comp_subtype (Module.finrank ℝ E - 1)
      (fun r : ℝ => r ^ a * φ r)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hd : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  have hcast : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) = (Module.finrank ℝ E : ℝ) - 1 := by
    rw [Nat.cast_sub hd, Nat.cast_one]
  dsimp only
  rw [Real.rpow_add hr, ← hcast, Real.rpow_natCast]
  simp only [smul_eq_mul, mul_assoc]

section ComplexBlock

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Separation of every radial profile against a real power of a complex coordinate. -/
theorem integral_complexBlock_rpow_radial (s : ℝ) (φ : ℝ → ℝ) :
    (∫ x : BlockSpace ℂ V, ‖x.fst‖ ^ (2 * s) * φ ‖x‖) =
      ((volume.toSphere : Measure (sphere (0 : BlockSpace ℂ V) 1)).real univ *
        complexBlockSphereMellin V s) *
          ∫ r in Ioi (0 : ℝ),
            r ^ ((Module.finrank ℝ (BlockSpace ℂ V) : ℝ) - 1 + 2 * s) * φ r := by
  rw [integral_real_homogeneous_mul_radial
    (fun x : BlockSpace ℂ V => ‖x.fst‖ ^ (2 * s)) (2 * s) φ (by
      intro r hr x
      simp only [WithLp.smul_fst, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        Real.mul_rpow hr.le (norm_nonneg _)])]
  congr 1
  unfold complexBlockSphereMellin
  field_simp [(complexBlock_sphere_mass_pos V).ne']

/-- A complex-coordinate monomial multiplied by a profile in logarithmic radius. -/
def radialComplexMonomial (m : ℕ) (χ : ℝ → ℝ) (x : BlockSpace ℂ V) : ℂ :=
  x.fst ^ m * (χ (Real.log ‖x‖) : ℂ)

/-- The monomial phase disappears from its absolute value. -/
theorem norm_radialComplexMonomial (m : ℕ) (χ : ℝ → ℝ) (x : BlockSpace ℂ V) :
    ‖radialComplexMonomial V m χ x‖ = ‖x.fst‖ ^ m * |χ (Real.log ‖x‖)| := by
  simp only [radialComplexMonomial, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- The weighted power of a radial monomial separates pointwise into angular and radial powers. -/
theorem weighted_norm_radialComplexMonomial_rpow (m : ℕ) (χ : ℝ → ℝ)
    (τ p : ℝ) (x : BlockSpace ℂ V) :
    (‖x‖ ^ (-τ) * ‖radialComplexMonomial V m χ x‖) ^ p =
      ‖x.fst‖ ^ ((m : ℝ) * p) *
        (‖x‖ ^ (-τ * p) * |χ (Real.log ‖x‖)| ^ p) := by
  rw [norm_radialComplexMonomial,
    Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _) (by positivity),
    Real.mul_rpow (pow_nonneg (norm_nonneg _) _) (abs_nonneg _),
    ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast ‖x.fst‖ m,
    ← Real.rpow_mul (norm_nonneg _)]
  ring

/-- Exact separation of the weighted `Lᵖ` integral of a radial coordinate monomial. -/
theorem integral_weighted_radialComplexMonomial (m : ℕ) (χ : ℝ → ℝ) (τ p : ℝ) :
    (∫ x : BlockSpace ℂ V, (‖x‖ ^ (-τ) * ‖radialComplexMonomial V m χ x‖) ^ p) =
      ((volume.toSphere : Measure (sphere (0 : BlockSpace ℂ V) 1)).real univ *
        complexBlockSphereMellin V ((m : ℝ) * p / 2)) *
          ∫ r in Ioi (0 : ℝ),
            r ^ ((Module.finrank ℝ (BlockSpace ℂ V) : ℝ) - 1 + ((m : ℝ) - τ) * p) *
              |χ (Real.log r)| ^ p := by
  simp_rw [weighted_norm_radialComplexMonomial_rpow]
  have h := integral_complexBlock_rpow_radial V ((m : ℝ) * p / 2)
    (fun r => r ^ (-τ * p) * |χ (Real.log r)| ^ p)
  have he : 2 * ((m : ℝ) * p / 2) = (m : ℝ) * p := by ring
  simp only [he] at h
  rw [h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [← mul_assoc, ← Real.rpow_add hr]
  congr 2
  ring

/-- At the dimension-balanced weight, the radial integral is independent of monomial degree. -/
theorem integral_critical_weighted_radialComplexMonomial (m : ℕ) (χ : ℝ → ℝ)
    {p : ℝ} (hp : p ≠ 0) :
    (∫ x : BlockSpace ℂ V,
      (‖x‖ ^ (-((m : ℝ) + (Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / p)) *
        ‖radialComplexMonomial V m χ x‖) ^ p) =
      ((volume.toSphere : Measure (sphere (0 : BlockSpace ℂ V) 1)).real univ *
        complexBlockSphereMellin V ((m : ℝ) * p / 2)) * ∫ t : ℝ, |χ t| ^ p := by
  rw [integral_weighted_radialComplexMonomial]
  have he : (Module.finrank ℝ (BlockSpace ℂ V) : ℝ) - 1 +
      ((m : ℝ) - ((m : ℝ) + (Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / p)) * p = -1 := by
    field_simp
    ring
  rw [he, integral_logRadius_weight]

end ComplexBlock

/-- The critical upper exponent exactly cancels the radial Jacobian. -/
theorem integral_carlemanQ_radialComplexMonomial (n m : ℕ) (χ : ℝ → ℝ) :
    (∫ x : BlockSpace ℂ (EuclideanSpace ℝ (Fin (2 * n))),
      (‖x‖ ^ (-((m : ℝ) + n + 1 / 2)) *
        ‖radialComplexMonomial (EuclideanSpace ℝ (Fin (2 * n))) m χ x‖) ^
          complexSphereCarlemanQ n) =
      ((volume.toSphere : Measure
        (sphere (0 : BlockSpace ℂ (EuclideanSpace ℝ (Fin (2 * n)))) 1)).real univ *
        complexSphereMellin n ((m : ℝ) * complexSphereCarlemanQ n / 2)) *
          ∫ t : ℝ, |χ t| ^ complexSphereCarlemanQ n := by
  have hq := (complexSphereCarlemanP_pos n).trans (complexSphereCarlemanP_lt_Q n)
  have h := integral_critical_weighted_radialComplexMonomial
    (EuclideanSpace ℝ (Fin (2 * n))) m χ hq.ne'
  have hd : Module.finrank ℝ (BlockSpace ℂ (EuclideanSpace ℝ (Fin (2 * n)))) =
      2 + 2 * n := by
    rw [(WithLp.linearEquiv 2 ℝ (ℂ × EuclideanSpace ℝ (Fin (2 * n)))).finrank_eq,
      Module.finrank_prod, Complex.finrank_real_complex]
    simp
  have he : (m : ℝ) + ((2 + 2 * n : ℕ) : ℝ) / complexSphereCarlemanQ n =
      (m : ℝ) + n + 1 / 2 := by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    unfold complexSphereCarlemanQ
    push_cast
    field_simp
    ring
  rw [hd, he] at h
  exact h

end GaloisForLFunctions.HTGeometry
