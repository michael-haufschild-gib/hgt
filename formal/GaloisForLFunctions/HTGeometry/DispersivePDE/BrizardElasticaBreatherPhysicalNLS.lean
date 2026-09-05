import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaMaNLS
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaBreatherPhysicalScaling
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaScalingClosure
import Mathlib.Tactic

/-!
# Physical-variable NLS certificates for the breather formulas

The paper's substitutions use amplitude `2α`, spatial scale `α`, and temporal scale `Dα²`.
This module packages that nonstandard normalization as a map from certified focusing-NLS solutions
to certified solutions of Brizard's dimensional NLS, then identifies both physical breather fields.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def physicalizeFocusingJet (D α : ℝ) (J : ComplexEvolutionJet2) :
    ComplexEvolutionJet2 where
  u := fun t x => ((2 * α : ℝ) : ℂ) * J.u (D * α ^ 2 * t) (α * x)
  ut := fun t x => ((2 * α : ℝ) : ℂ) * (((D * α ^ 2 : ℝ) : ℂ) *
    J.ut (D * α ^ 2 * t) (α * x))
  ux := fun t x => ((2 * α : ℝ) : ℂ) * ((α : ℂ) *
    J.ux (D * α ^ 2 * t) (α * x))
  uxx := fun t x => ((2 * α : ℝ) : ℂ) * (((α ^ 2 : ℝ) : ℂ) *
    J.uxx (D * α ^ 2 * t) (α * x))
  hasDerivAt_time := by
    intro t x
    have hinner : HasDerivAt (fun r : ℝ => D * α ^ 2 * r) (D * α ^ 2) t := by
      simpa using (hasDerivAt_id t).const_mul (D * α ^ 2)
    have h := (J.hasDerivAt_time (D * α ^ 2 * t) (α * x)).scomp t hinner
      |>.const_mul (((2 * α : ℝ) : ℂ))
    apply h.congr_deriv
    simp only [Complex.real_smul]
  hasDerivAt_space := by
    intro t x
    have hinner : HasDerivAt (fun y : ℝ => α * y) α x := by
      simpa using (hasDerivAt_id x).const_mul α
    have h := (J.hasDerivAt_space (D * α ^ 2 * t) (α * x)).scomp x hinner
      |>.const_mul (((2 * α : ℝ) : ℂ))
    apply h.congr_deriv
    simp only [Complex.real_smul]
  hasDerivAt_space_one := by
    intro t x
    have hinner : HasDerivAt (fun y : ℝ => α * y) α x := by
      simpa using (hasDerivAt_id x).const_mul α
    have h := (J.hasDerivAt_space_one (D * α ^ 2 * t) (α * x)).scomp x hinner
    have hscaled := h.const_mul (((2 * α : ℝ) : ℂ) * (α : ℂ))
    apply (hscaled.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards with y
      simp only [Function.comp_apply]
      ring
    · simp only [Complex.real_smul]
      push_cast
      ring_nf

theorem norm_physicalizeFocusingJet_sq (D α : ℝ) (J : ComplexEvolutionJet2) (t x : ℝ) :
    ‖(physicalizeFocusingJet D α J).u t x‖ ^ 2 =
      (2 * α) ^ 2 * ‖J.u (D * α ^ 2 * t) (α * x)‖ ^ 2 := by
  simp only [physicalizeFocusingJet, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]

/-- The exact dimensionalization used before paper equation (35). -/
noncomputable def physicalizeFocusingSolution (D α : ℝ) (S : FocusingSolutionJet) :
    BrizardSolutionJet D :=
  ⟨physicalizeFocusingJet D α S.val, by
    intro t x
    have h := S.property (D * α ^ 2 * t) (α * x)
    rw [norm_physicalizeFocusingJet_sq]
    simp only [physicalizeFocusingJet]
    push_cast at h ⊢
    calc
      _ = ((2 : ℂ) * (D : ℂ) * (α : ℂ) ^ 3) *
          (Complex.I * S.val.ut (D * α ^ 2 * t) (α * x) +
            S.val.uxx (D * α ^ 2 * t) (α * x) +
            (2 : ℂ) * (‖S.val.u (D * α ^ 2 * t) (α * x)‖ : ℂ) ^ 2 *
              S.val.u (D * α ^ 2 * t) (α * x)) := by ring
      _ = 0 := by
        apply mul_eq_zero_of_right
        exact h⟩

theorem physicalizeFocusingSolution_solves (D α : ℝ) (S : FocusingSolutionJet) :
    SolvesNLS D (physicalizeFocusingSolution D α S).val :=
  (physicalizeFocusingSolution D α S).property

noncomputable def akhmedievFocusingSolution (φ : BreatherAngle) : FocusingSolutionJet :=
  ⟨akhmedievBreatherJet φ, akhmedievBreather_solves φ⟩

noncomputable def maFocusingSolution (φ : MaAngle) : FocusingSolutionJet :=
  ⟨maBreatherJet φ, maBreather_solves φ⟩

noncomputable def physicalAkhmedievSolution
    (P : BreatherPhysicalScales) (φ : BreatherAngle) :
    BrizardSolutionJet (P.circulation : ℝ) :=
  physicalizeFocusingSolution (P.circulation : ℝ)
    ((P.waveNumber : ℝ) / akhmedievWaveNumber φ) (akhmedievFocusingSolution φ)

noncomputable def physicalMaSolution (P : BreatherPhysicalScales) (φ : MaAngle) :
    BrizardSolutionJet (P.circulation : ℝ) :=
  physicalizeFocusingSolution (P.circulation : ℝ)
    ((P.waveNumber : ℝ) / maWaveNumber φ) (maFocusingSolution φ)

theorem physicalAkhmedievSolution_field
    (P : BreatherPhysicalScales) (φ : BreatherAngle) (t s : ℝ) :
    (physicalAkhmedievSolution P φ).val.u t s = physicalAkhmedievBreather P φ s t := by
  simp only [physicalAkhmedievSolution, physicalizeFocusingSolution,
    physicalizeFocusingJet, akhmedievFocusingSolution, akhmedievBreatherJet]
  rw [physicalAkhmedievBreather, physicalAkhmedievAmplitude,
    physicalAkhmedievXi, physicalAkhmedievTau, physicalAkhmedievFrequency]
  have hp : akhmedievWaveNumber φ ≠ 0 := ne_of_gt (akhmedievWaveNumber_pos φ)
  have hOmega : akhmedievOmega φ ≠ 0 := by
    rw [akhmedievOmega]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [φ.property.1]) (by linarith [φ.property.2, Real.pi_pos]))
  congr 1
  · push_cast
    ring
  · congr 1
    · field_simp [hp, hOmega]
    · field_simp [hp]

theorem physicalMaSolution_field
    (P : BreatherPhysicalScales) (φ : MaAngle) (t s : ℝ) :
    (physicalMaSolution P φ).val.u t s = physicalMaBreather P φ s t := by
  simp only [physicalMaSolution, physicalizeFocusingSolution,
    physicalizeFocusingJet, maFocusingSolution, maBreatherJet]
  rw [physicalMaBreather, physicalMaAmplitude, physicalMaXi, physicalMaTau,
    physicalMaFrequency]
  have hp : maWaveNumber φ ≠ 0 := ne_of_gt (maWaveNumber_pos φ)
  have hOmega : maOmega φ ≠ 0 := ne_of_gt (maOmega_pos φ)
  congr 1
  · push_cast
    ring
  · congr 1
    · field_simp [hp, hOmega]
    · field_simp [hp]

theorem physicalAkhmedievSolution_solves
    (P : BreatherPhysicalScales) (φ : BreatherAngle) :
    SolvesNLS (P.circulation : ℝ) (physicalAkhmedievSolution P φ).val :=
  (physicalAkhmedievSolution P φ).property

theorem physicalMaSolution_solves (P : BreatherPhysicalScales) (φ : MaAngle) :
    SolvesNLS (P.circulation : ℝ) (physicalMaSolution P φ).val :=
  (physicalMaSolution P φ).property

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
