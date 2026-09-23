import GaloisForLFunctions.HTGeometry.ProductChartDalembertian
import GaloisForLFunctions.HTGeometry.ClockTwoDimensionalProbe
import GaloisForLFunctions.HTGeometry.HillRegularProbes

/-!
# Clock probes on a chart whose principal part varies in space

Every clock chart built so far carries a principal part that varies at most in time. The product
construction removes that restriction without any variable-coefficient hyperbolic theory.

In two dimensions the inverse step is already closed unconditionally: an arbitrary continuously
differentiable potential carries a probe near every event, and the probe is regular — the Goursat
solution is twice continuously differentiable and the null frame is linear. Crossing the surface
with a flat factor and pulling the probe back along the projection gives a probe of the product,
because the d'Alembertian of the product on a transversally constant field is the d'Alembertian of
the factor. Rescaling the product conformally by an arbitrary smooth function of **all** the
coordinates then produces a chart whose inverse metric varies in every coordinate, and the corpus's
conformal transfer carries the probes there.

Consequently the potential of such a chart is determined by its probes, and two clock species of
different mass sharing one two-dimensional potential reconstruct the conformal factor pointwise.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

/-! ## Probes of the two-dimensional factor, with their regularity -/

/-- **A two-dimensional clock spacetime carries regular probes at every event.** -/
theorem regularOpenProbes_two_dimensional {V : (Fin (1 + 1) → ℝ) → ℝ} (hV : ContDiff ℝ 1 V) :
    RegularOpenProbes
      (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert V := by
  intro x
  obtain ⟨W, hWopen, hxW, U, hUon, hUne, _, hUreg⟩ := exists_clockProbe_on_two_dimensional hV x
  exact ⟨W, hWopen, hxW, U, hUreg, hUon, hUne⟩

namespace SmoothMetricChart

/-! ## Probes transport to the product -/

variable {n : ℕ} (M : SmoothMetricChart n) (k : ℕ)

/-- **Regular probes transport to the product with a flat factor**, for a potential which does not
depend on the transverse coordinates. -/
theorem regularOpenProbes_prodFlat {V : (Fin n → ℝ) → ℝ}
    (h : RegularOpenProbes M.dalembert V) :
    RegularOpenProbes (M.prodFlat k).dalembert (fun y => V (frontMap n k y)) := by
  intro x
  obtain ⟨W, hWopen, hxW, u, hureg, hu, hune⟩ := h (frontMap n k x)
  refine ⟨frontMap n k ⁻¹' W, hWopen.preimage (continuous_frontMap n k), hxW,
    fun z => u (frontMap n k z), differentiablePartialsOn_comp_frontMap k hWopen hureg,
    fun z hz => ?_, fun z hz => hune _ hz⟩
  show (M.prodFlat k).dalembert (fun w => u (frontMap n k w)) z
      + V (frontMap n k z) * u (frontMap n k z) = 0
  rw [M.prodFlat_dalembert_comp_front k hWopen hureg hz]
  exact hu _ hz

end SmoothMetricChart

/-! ## A two-dimensional factor times a flat factor -/

section TwoDimensional

variable (k : ℕ)

/-- The product of a two-dimensional clock spacetime with a flat factor. -/
noncomputable def flatProductChart : SmoothMetricChart (1 + 1 + k) :=
  (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.prodFlat k

/-- **The product of a two-dimensional clock spacetime with a flat factor carries regular probes**,
for an arbitrary continuously differentiable potential of the two-dimensional factor. -/
theorem regularOpenProbes_flatProductChart {V : (Fin (1 + 1) → ℝ) → ℝ} (hV : ContDiff ℝ 1 V) :
    RegularOpenProbes (flatProductChart k).dalembert (fun y => V (frontMap (1 + 1) k y)) :=
  SmoothMetricChart.regularOpenProbes_prodFlat _ k (regularOpenProbes_two_dimensional hV)

/-- **Every conformal rescaling of that product carries regular probes too.**

The conformal factor is an arbitrary smooth function of all `2 + k` coordinates, so the inverse
metric of the rescaled chart varies in every coordinate: the principal part is no longer independent
of the point, in space or in time. -/
theorem regularOpenProbes_conformalRescale_flatProductChart {V : (Fin (1 + 1) → ℝ) → ℝ}
    (hV : ContDiff ℝ 1 V) {sigma : (Fin (1 + 1 + k) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma) :
    RegularOpenProbes ((flatProductChart k).conformalRescale sigma hsigma).dalembert
      ((flatProductChart k).conformalTransferPotential sigma
        (fun y => V (frontMap (1 + 1) k y))) :=
  regularOpenProbes_conformalRescale (flatProductChart k) hsigma
    (regularOpenProbes_flatProductChart k hV)

/-- The product of a conformally rescaled two-dimensional clock spacetime with a flat factor: a
warped product in which the two-dimensional block carries a conformal factor of its own coordinates
and the transverse block does not. -/
noncomputable def warpedProductChart {sigma₂ : (Fin (1 + 1) → ℝ) → ℝ}
    (hsigma₂ : ContDiff ℝ ∞ sigma₂) : SmoothMetricChart (1 + 1 + k) :=
  ((SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.conformalRescale
    sigma₂ hsigma₂).prodFlat k

/-- **The warped product carries regular probes.** The two blocks of the metric scale differently,
so this is not a conformal rescaling of the flat product. -/
theorem regularOpenProbes_warpedProductChart {sigma₂ : (Fin (1 + 1) → ℝ) → ℝ}
    (hsigma₂ : ContDiff ℝ ∞ sigma₂) {V : (Fin (1 + 1) → ℝ) → ℝ} (hV : ContDiff ℝ 1 V) :
    RegularOpenProbes (warpedProductChart k hsigma₂).dalembert
      (fun y => SmoothMetricChart.conformalTransferPotential
        (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart sigma₂ V
        (frontMap (1 + 1) k y)) :=
  SmoothMetricChart.regularOpenProbes_prodFlat _ k
    (regularOpenProbes_conformalRescale _ hsigma₂ (regularOpenProbes_two_dimensional hV))

/-- **Every conformal rescaling of the warped product carries regular probes.**

This is the widest chart class the construction reaches: the two-dimensional block carries an
arbitrary conformal factor of its own coordinates, the whole product carries a second arbitrary
conformal factor of all `2 + k` coordinates, and the potential of the two-dimensional factor is an
arbitrary continuously differentiable function. Every entry of the inverse metric varies with every
coordinate. -/
theorem regularOpenProbes_conformalRescale_warpedProductChart {sigma₂ : (Fin (1 + 1) → ℝ) → ℝ}
    (hsigma₂ : ContDiff ℝ ∞ sigma₂) {V : (Fin (1 + 1) → ℝ) → ℝ} (hV : ContDiff ℝ 1 V)
    {sigma : (Fin (1 + 1 + k) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma) :
    RegularOpenProbes ((warpedProductChart k hsigma₂).conformalRescale sigma hsigma).dalembert
      ((warpedProductChart k hsigma₂).conformalTransferPotential sigma
        (fun y => SmoothMetricChart.conformalTransferPotential
          (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart sigma₂ V
          (frontMap (1 + 1) k y))) :=
  regularOpenProbes_conformalRescale (warpedProductChart k hsigma₂) hsigma
    (regularOpenProbes_warpedProductChart k hsigma₂ hV)

/-- **The probes determine the potential of the product chart.** -/
theorem potential_eq_of_probes_flatProductChart {V : (Fin (1 + 1) → ℝ) → ℝ} (hV : ContDiff ℝ 1 V)
    {other : (Fin (1 + 1 + k) → ℝ) → ℝ}
    (h : ∀ (u : (Fin (1 + 1 + k) → ℝ) → ℝ) (W : Set (Fin (1 + 1 + k) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn (flatProductChart k).dalembert
          (fun y => V (frontMap (1 + 1) k y)) u W →
        SolvesPotentialWaveOn (flatProductChart k).dalembert other u W) :
    other = fun y => V (frontMap (1 + 1) k y) :=
  potential_eq_of_openProbes (regularOpenProbes_flatProductChart k hV).openProbes h

/-- **The probes determine the potential of every conformal rescaling of the product chart.** -/
theorem potential_eq_of_probes_conformalRescale_flatProductChart {V : (Fin (1 + 1) → ℝ) → ℝ}
    (hV : ContDiff ℝ 1 V) {sigma : (Fin (1 + 1 + k) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {other : (Fin (1 + 1 + k) → ℝ) → ℝ}
    (h : ∀ (u : (Fin (1 + 1 + k) → ℝ) → ℝ) (W : Set (Fin (1 + 1 + k) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn ((flatProductChart k).conformalRescale sigma hsigma).dalembert
          ((flatProductChart k).conformalTransferPotential sigma
            (fun y => V (frontMap (1 + 1) k y))) u W →
        SolvesPotentialWaveOn ((flatProductChart k).conformalRescale sigma hsigma).dalembert
          other u W) :
    other = (flatProductChart k).conformalTransferPotential sigma
      (fun y => V (frontMap (1 + 1) k y)) :=
  potential_eq_of_openProbes
    (regularOpenProbes_conformalRescale_flatProductChart k hV hsigma).openProbes h

/-- **The two-species conformal clock scale law on a chart whose principal part varies in space.**

Two clock species of different mass, feeling the same continuously differentiable potential of the
two-dimensional factor and propagating on the same conformally rescaled product chart, reconstruct
the conformal factor pointwise: the shared potential cancels in the difference of the two
transferred potentials, the mass difference does not. -/
theorem twoSpecies_scale_law_flatProductChart {P : (Fin (1 + 1) → ℝ) → ℝ} (hP : ContDiff ℝ 1 P)
    {m₁ m₂ : ℝ} (hmass : m₂ ^ (2 : ℕ) - m₁ ^ (2 : ℕ) ≠ 0)
    {sigma : (Fin (1 + 1 + k) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {other₁ other₂ : (Fin (1 + 1 + k) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (1 + 1 + k) → ℝ) → ℝ) (W : Set (Fin (1 + 1 + k) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn ((flatProductChart k).conformalRescale sigma hsigma).dalembert
          ((flatProductChart k).conformalTransferPotential sigma
            (fun y => (fun z => P z - m₁ ^ (2 : ℕ)) (frontMap (1 + 1) k y))) u W →
        SolvesPotentialWaveOn ((flatProductChart k).conformalRescale sigma hsigma).dalembert
          other₁ u W)
    (h₂ : ∀ (u : (Fin (1 + 1 + k) → ℝ) → ℝ) (W : Set (Fin (1 + 1 + k) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn ((flatProductChart k).conformalRescale sigma hsigma).dalembert
          ((flatProductChart k).conformalTransferPotential sigma
            (fun y => (fun z => P z - m₂ ^ (2 : ℕ)) (frontMap (1 + 1) k y))) u W →
        SolvesPotentialWaveOn ((flatProductChart k).conformalRescale sigma hsigma).dalembert
          other₂ u W)
    (x : Fin (1 + 1 + k) → ℝ) :
    (other₁ x - other₂ x) / (m₂ ^ (2 : ℕ) - m₁ ^ (2 : ℕ)) = Real.exp (-2 * sigma x) := by
  have hP₁ : ContDiff ℝ 1 fun z : Fin (1 + 1) → ℝ => P z - m₁ ^ (2 : ℕ) := hP.sub contDiff_const
  have hP₂ : ContDiff ℝ 1 fun z : Fin (1 + 1) → ℝ => P z - m₂ ^ (2 : ℕ) := hP.sub contDiff_const
  have e₁ := potential_eq_of_probes_conformalRescale_flatProductChart k hP₁ hsigma h₁
  have e₂ := potential_eq_of_probes_conformalRescale_flatProductChart k hP₂ hsigma h₂
  rw [e₁, e₂, conformalTransferPotential_sub]
  show Real.exp (-2 * sigma x) *
      ((P (frontMap (1 + 1) k x) - m₁ ^ (2 : ℕ)) - (P (frontMap (1 + 1) k x) - m₂ ^ (2 : ℕ))) /
        (m₂ ^ (2 : ℕ) - m₁ ^ (2 : ℕ)) = Real.exp (-2 * sigma x)
  have hfac : (P (frontMap (1 + 1) k x) - m₁ ^ (2 : ℕ)) - (P (frontMap (1 + 1) k x) - m₂ ^ (2 : ℕ))
      = m₂ ^ (2 : ℕ) - m₁ ^ (2 : ℕ) := by ring
  rw [hfac, mul_div_assoc, div_self hmass, mul_one]

/-- **The two-species conformal clock scale law on the warped product.**

Two clock species of different mass reconstruct the *total* conformal factor of the warped product:
the factor of the two-dimensional block and the factor of the whole chart multiply, and the shared
potential cancels. -/
theorem twoSpecies_scale_law_warpedProductChart {sigma₂ : (Fin (1 + 1) → ℝ) → ℝ}
    (hsigma₂ : ContDiff ℝ ∞ sigma₂) {P : (Fin (1 + 1) → ℝ) → ℝ} (hP : ContDiff ℝ 1 P)
    {m₁ m₂ : ℝ} (hmass : m₂ ^ (2 : ℕ) - m₁ ^ (2 : ℕ) ≠ 0)
    {sigma : (Fin (1 + 1 + k) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {other₁ other₂ : (Fin (1 + 1 + k) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (1 + 1 + k) → ℝ) → ℝ) (W : Set (Fin (1 + 1 + k) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn ((warpedProductChart k hsigma₂).conformalRescale sigma hsigma).dalembert
          ((warpedProductChart k hsigma₂).conformalTransferPotential sigma
            (fun y => SmoothMetricChart.conformalTransferPotential
              (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart sigma₂
              (fun z => P z - m₁ ^ (2 : ℕ)) (frontMap (1 + 1) k y))) u W →
        SolvesPotentialWaveOn
          ((warpedProductChart k hsigma₂).conformalRescale sigma hsigma).dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (1 + 1 + k) → ℝ) → ℝ) (W : Set (Fin (1 + 1 + k) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn ((warpedProductChart k hsigma₂).conformalRescale sigma hsigma).dalembert
          ((warpedProductChart k hsigma₂).conformalTransferPotential sigma
            (fun y => SmoothMetricChart.conformalTransferPotential
              (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart sigma₂
              (fun z => P z - m₂ ^ (2 : ℕ)) (frontMap (1 + 1) k y))) u W →
        SolvesPotentialWaveOn
          ((warpedProductChart k hsigma₂).conformalRescale sigma hsigma).dalembert other₂ u W)
    (x : Fin (1 + 1 + k) → ℝ) :
    (other₁ x - other₂ x) / (m₂ ^ (2 : ℕ) - m₁ ^ (2 : ℕ))
      = Real.exp (-2 * sigma x) * Real.exp (-2 * sigma₂ (frontMap (1 + 1) k x)) := by
  have hP₁ : ContDiff ℝ 1 fun z : Fin (1 + 1) → ℝ => P z - m₁ ^ (2 : ℕ) := hP.sub contDiff_const
  have hP₂ : ContDiff ℝ 1 fun z : Fin (1 + 1) → ℝ => P z - m₂ ^ (2 : ℕ) := hP.sub contDiff_const
  have e₁ := potential_eq_of_openProbes
    (regularOpenProbes_conformalRescale_warpedProductChart k hsigma₂ hP₁ hsigma).openProbes h₁
  have e₂ := potential_eq_of_openProbes
    (regularOpenProbes_conformalRescale_warpedProductChart k hsigma₂ hP₂ hsigma).openProbes h₂
  rw [e₁, e₂, conformalTransferPotential_sub]
  have hinner : SmoothMetricChart.conformalTransferPotential
        (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart sigma₂
        (fun z => P z - m₁ ^ (2 : ℕ)) (frontMap (1 + 1) k x)
      - SmoothMetricChart.conformalTransferPotential
        (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart sigma₂
        (fun z => P z - m₂ ^ (2 : ℕ)) (frontMap (1 + 1) k x)
      = Real.exp (-2 * sigma₂ (frontMap (1 + 1) k x)) * (m₂ ^ (2 : ℕ) - m₁ ^ (2 : ℕ)) := by
    rw [conformalTransferPotential_sub]
    have hfac : (P (frontMap (1 + 1) k x) - m₁ ^ (2 : ℕ)) - (P (frontMap (1 + 1) k x) - m₂ ^ (2 : ℕ))
        = m₂ ^ (2 : ℕ) - m₁ ^ (2 : ℕ) := by ring
    rw [hfac]
  rw [hinner]
  rw [mul_comm (Real.exp (-2 * sigma₂ (frontMap (1 + 1) k x))) (m₂ ^ (2 : ℕ) - m₁ ^ (2 : ℕ)),
    ← mul_assoc, mul_comm (Real.exp (-2 * sigma x)) (m₂ ^ (2 : ℕ) - m₁ ^ (2 : ℕ)), mul_assoc,
    mul_comm (m₂ ^ (2 : ℕ) - m₁ ^ (2 : ℕ))
      (Real.exp (-2 * sigma x) * Real.exp (-2 * sigma₂ (frontMap (1 + 1) k x))),
    mul_div_assoc, div_self hmass, mul_one]

end TwoDimensional

end GaloisForLFunctions.HTGeometry
