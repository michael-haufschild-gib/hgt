import GaloisForLFunctions.HTGeometry.FokasLenellsEigenfunctions
import GaloisForLFunctions.HTGeometry.FokasLenellsPlaneWaves
import GaloisForLFunctions.HTGeometry.IntegralGronwall
import GaloisForLFunctions.HTGeometry.IntegrableDerivLimit

/-!
# Integrable transport in the Fokas–Lenells scattering frame

Section 2 of Yan–Zhang–Zhu, arXiv:2607.19649v1, uses an oscillating
frame to separate free propagation from the potential. For every Schwartz
potential and every positive real spectral parameter, this file transports
the corpus's constructed eigenfunctions into that frame. The derivative is
bounded by an explicit integrable density involving `q′` and its reflection.

The corpus's variable-coefficient Grönwall theorem gives a uniform bound on
the positive ray. Its integrable-derivative limit theorem then constructs a
right asymptotic state. No smallness or assumed asymptotic hypothesis occurs.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The unitary diagonal frame removing the free spatial oscillation. -/
def rotatingFrame (z x : ℝ) (v : SpectralVector) : SpectralVector :=
  (FDNLS.staggerPhase z x*v.1, FDNLS.staggerPhase (-z) x*v.2)

theorem rotatingFrame_norm (z x : ℝ) (v : SpectralVector) :
    ‖rotatingFrame z x v‖ = ‖v‖ := by
  simp [rotatingFrame, Prod.norm_def, FDNLS.norm_staggerPhase]

theorem rotatingFrame_neg_inverse (z x : ℝ) (v : SpectralVector) :
    rotatingFrame (-z) x (rotatingFrame z x v) = v := by
  apply Prod.ext <;> simp [rotatingFrame, FDNLS.staggerPhase, ← Complex.exp_add, ← mul_assoc]

/-- Integrable coefficient mass in the interaction frame. -/
def scatteringDensity (q : SchwartzMap ℝ ℂ) (κ x : ℝ) : ℝ :=
  Real.exp κ*(‖SchwartzMap.derivCLM ℂ ℂ q x‖ + ‖reflectedDerivative q x‖)

theorem scatteringDensity_nonneg (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    0 ≤ scatteringDensity q κ x := by unfold scatteringDensity; positivity

theorem scatteringDensity_continuous (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    Continuous (scatteringDensity q κ) := by
  unfold scatteringDensity
  fun_prop

theorem scatteringDensity_integrable (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    Integrable (scatteringDensity q κ) :=
  ((SchwartzMap.derivCLM ℂ ℂ q).integrable.norm.add
    (reflectedDerivative q).integrable.norm).const_mul (Real.exp κ)

def interactionRate (q : SchwartzMap ℝ ℂ) (κ x : ℝ) (v : SpectralVector) : SpectralVector :=
  rotatingFrame ((Real.exp κ)^2) x
    (pairOperator 0 (I*(Real.exp κ:ℂ)*reflectedDerivative q x)
      (I*(Real.exp κ:ℂ)*deriv q x) 0
      (rotatingFrame (-((Real.exp κ)^2)) x v))

theorem interactionRate_bound (q : SchwartzMap ℝ ℂ) (κ x : ℝ) (v : SpectralVector) :
    ‖interactionRate q κ x v‖ ≤ scatteringDensity q κ x*‖v‖ := by
  unfold interactionRate
  rw [rotatingFrame_norm]
  refine ((pairOperator _ _ _ _).le_opNorm _).trans ?_
  rw [rotatingFrame_norm]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  refine (pairOperator_bound _ _ _ _).trans_eq ?_
  simp [scatteringDensity, SchwartzMap.derivCLM_apply]
  ring

theorem interactionRate_continuous (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    Continuous (fun p : ℝ × SpectralVector => interactionRate q κ p.1 p.2) := by
  unfold interactionRate rotatingFrame pairOperator
  change Continuous fun p : ℝ × SpectralVector =>
    (FDNLS.staggerPhase ((Real.exp κ)^2) p.1 *
      (0*(FDNLS.staggerPhase (-((Real.exp κ)^2)) p.1*p.2.1) +
        (I*(Real.exp κ:ℂ)*reflectedDerivative q p.1)*
          (FDNLS.staggerPhase (-(-((Real.exp κ)^2))) p.1*p.2.2)),
     FDNLS.staggerPhase (-((Real.exp κ)^2)) p.1 *
      ((I*(Real.exp κ:ℂ)*SchwartzMap.derivCLM ℂ ℂ q p.1)*
        (FDNLS.staggerPhase (-((Real.exp κ)^2)) p.1*p.2.1) +
        0*(FDNLS.staggerPhase (-(-((Real.exp κ)^2))) p.1*p.2.2)))
  unfold FDNLS.staggerPhase
  fun_prop

/-- The constructed spatial eigenfunction viewed in its oscillating frame. -/
def interactionSolution (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector) (x : ℝ) :
    SpectralVector := rotatingFrame ((Real.exp κ)^2) x (spatialEigenfunction q (κ:ℂ) v x)

/-- The diagonal terms cancel exactly in the rotating frame. -/
theorem interactionSolution_hasDerivAt (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) (x : ℝ) :
    HasDerivAt (interactionSolution q κ v)
      (interactionRate q κ x (interactionSolution q κ v x)) x := by
  have h1 := (FDNLS.hasDerivAt_staggerPhase ((Real.exp κ)^2) x).mul
    (spatialEigenfunction_first_hasDerivAt q (κ:ℂ) v x)
  have h2 := (FDNLS.hasDerivAt_staggerPhase (-((Real.exp κ)^2)) x).mul
    (spatialEigenfunction_second_hasDerivAt q (κ:ℂ) v x)
  refine (h1.prodMk h2).congr_deriv ?_
  change _ = rotatingFrame ((Real.exp κ)^2) x
    (pairOperator 0 (I*(Real.exp κ:ℂ)*reflectedDerivative q x)
      (I*(Real.exp κ:ℂ)*deriv q x) 0
      (rotatingFrame (-((Real.exp κ)^2)) x
        (rotatingFrame ((Real.exp κ)^2) x (spatialEigenfunction q (κ:ℂ) v x))))
  rw [rotatingFrame_neg_inverse]
  apply Prod.ext <;>
    simp [rotatingFrame, pairOperator, reflectedDerivative_apply, ← Complex.ofReal_exp] <;> ring

theorem interactionSolution_initial (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector) :
    interactionSolution q κ v 0 = v := by
  simp [interactionSolution, spatialEigenfunction_initial, rotatingFrame, FDNLS.staggerPhase]

theorem interactionSolution_continuous (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector) :
    Continuous (interactionSolution q κ v) :=
  (show Differentiable ℝ (interactionSolution q κ v) from
    fun x => (interactionSolution_hasDerivAt q κ v x).differentiableAt).continuous

/-- Total L¹ interaction mass. -/
def scatteringMass (q : SchwartzMap ℝ ℂ) (κ : ℝ) : ℝ :=
  ∫ x : ℝ, scatteringDensity q κ x

theorem scatteringMass_nonneg (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    0 ≤ scatteringMass q κ := integral_nonneg (scatteringDensity_nonneg q κ)

def interactionDerivative (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector) (x : ℝ) :
    SpectralVector := interactionRate q κ x (interactionSolution q κ v x)

theorem interactionDerivative_continuous (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) : Continuous (interactionDerivative q κ v) :=
  (interactionRate_continuous q κ).comp
    (f := fun x : ℝ => (x, interactionSolution q κ v x))
    (continuous_id.prodMk (interactionSolution_continuous q κ v))

theorem interactionSolution_integral (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) (x : ℝ) :
    interactionSolution q κ v x = v + ∫ s in (0:ℝ)..x, interactionDerivative q κ v s := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => interactionSolution_hasDerivAt q κ v y)
    ((interactionDerivative_continuous q κ v).intervalIntegrable 0 x)
  rw [interactionSolution_initial] at h
  simpa only [add_comm, interactionDerivative] using (sub_eq_iff_eq_add.mp h.symm)

/-- The integrable coefficient gives a bound uniform along the positive ray,
not the exponential-in-position bound of the initial Picard construction. -/
theorem interactionSolution_positive_bound (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) (x : ℝ) :
    ‖interactionSolution q κ v |x|‖ ≤ ‖v‖*Real.exp (scatteringMass q κ) := by
  have hS := (interactionSolution_continuous q κ v).norm
  have hk := scatteringDensity_continuous q κ
  have hD := (interactionDerivative_continuous q κ v).norm
  apply le_mul_exp_of_le_add_integral_of_mass_le (A := 0) (B := |x|)
    (S := fun y => ‖interactionSolution q κ v y‖) (k := scatteringDensity q κ)
    (abs_nonneg x) hS.continuousOn hk.continuousOn
    (fun y _ => scatteringDensity_nonneg q κ y) (norm_nonneg v)
  · intro y hy
    calc
      ‖interactionSolution q κ v y‖ =
          ‖v + ∫ s in (0:ℝ)..y, interactionDerivative q κ v s‖ := by
        rw [interactionSolution_integral]
      _ ≤ ‖v‖ + ‖∫ s in (0:ℝ)..y, interactionDerivative q κ v s‖ := norm_add_le _ _
      _ ≤ ‖v‖ + ∫ s in (0:ℝ)..y, ‖interactionDerivative q κ v s‖ :=
        add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hy.1)
      _ ≤ ‖v‖ + ∫ s in (0:ℝ)..y, scatteringDensity q κ s*‖interactionSolution q κ v s‖ := by
        apply add_le_add le_rfl
        exact intervalIntegral.integral_mono_on hy.1 (hD.intervalIntegrable 0 y)
          ((hk.mul hS).intervalIntegrable 0 y)
          (fun s _ => interactionRate_bound q κ s (interactionSolution q κ v s))
  · intro y hy
    rw [intervalIntegral.integral_of_le hy.1]
    exact setIntegral_le_integral (scatteringDensity_integrable q κ)
      (Filter.Eventually.of_forall (scatteringDensity_nonneg q κ))
  · exact ⟨abs_nonneg x, le_rfl⟩

/-- The rotated derivative is genuinely integrable, supplying an asymptotic state. -/
theorem interactionDerivative_integrableOn_Ioi (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) : IntegrableOn (interactionDerivative q κ v) (Set.Ioi 0) := by
  have hmajor := ((scatteringDensity_integrable q κ).const_mul
    (‖v‖*Real.exp (scatteringMass q κ))).integrableOn (s := Set.Ioi 0)
  apply hmajor.mono' (interactionDerivative_continuous q κ v).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hb := interactionSolution_positive_bound q κ v x
  rw [abs_of_pos hx] at hb
  calc
    ‖interactionDerivative q κ v x‖ ≤
        scatteringDensity q κ x*‖interactionSolution q κ v x‖ := interactionRate_bound _ _ _ _
    _ ≤ scatteringDensity q κ x*(‖v‖*Real.exp (scatteringMass q κ)) :=
      mul_le_mul_of_nonneg_left hb (scatteringDensity_nonneg q κ x)
    _ = _ := mul_comm _ _

/-- The asymptotic state is the initial vector plus total integrable transport. -/
def rightAsymptoticVector (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector) :
    SpectralVector := v + ∫ x in Set.Ioi (0:ℝ), interactionDerivative q κ v x

theorem interactionSolution_tendsto_right (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) :
    Tendsto (interactionSolution q κ v) atTop (𝓝 (rightAsymptoticVector q κ v)) := by
  have h := tendsto_of_hasDerivAt_of_integrableOn_Ioi
    (a := 0) (fun x _ => interactionSolution_hasDerivAt q κ v x)
    (interactionDerivative_integrableOn_Ioi q κ v)
  simpa only [interactionSolution_initial, rightAsymptoticVector, interactionDerivative] using h

end
end GaloisForLFunctions.HTGeometry.FokasLenells
