import GaloisForLFunctions.HTGeometry.GomesQuarticTensorDensity

/-!
# Quartic charge measures and their exact ground-state boundary

The same integer tensor charge simultaneously controls an actual density measure and the
corpus's factorized quartic Hamiltonian. Finiteness is equivalent to existence of a nonzero
Schwartz zero mode. Positive charges reuse the existing quartic ground state after logarithmic
reparameterization; no ground-state or integrability premise is supplied.
-/

noncomputable section
open MeasureTheory
open scoped SchwartzMap NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- The raw quartic measure of every signed integer charge, allowing infinite mass. -/
def gomesQuarticChargeMeasure (b : ℝ) (n : ℤ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (gomesQuarticTensorDensity b n x))

/-- Exact measure-finiteness classification. -/
theorem gomesQuarticChargeMeasure_finite_iff (b : ℝ) (n : ℤ) :
    IsFiniteMeasure (gomesQuarticChargeMeasure b n) ↔ 0 < (n : ℝ) * b := by
  have h : Integrable (fun _ : ℝ => (1 : ℝ)) (gomesQuarticChargeMeasure b n) ↔
      Integrable (gomesQuarticTensorDensity b n) := by
    change Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.withDensity (fun x => ENNReal.ofReal (gomesQuarticTensorDensity b n x))) ↔ _
    rw [integrable_withDensity_iff_integrable_smul'
      (gomesQuarticTensorDensity_continuous b n).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (gomesQuarticTensorDensity_pos b n _).le,
      smul_eq_mul, mul_one]
  exact (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).symm.trans
    (h.trans (gomesQuarticTensorDensity_integrable_iff b n))

/-- The complementary closed half-lattice gives infinite total mass. -/
theorem gomesQuarticChargeMeasure_infinite_iff (b : ℝ) (n : ℤ) :
    gomesQuarticChargeMeasure b n Set.univ = ∞ ↔ (n : ℝ) * b ≤ 0 := by
  rw [← not_isFiniteMeasure_iff, gomesQuarticChargeMeasure_finite_iff]
  exact not_lt

/-- The neutral tensor charge is unrestricted Lebesgue volume. -/
theorem gomesQuarticChargeMeasure_zero (b : ℝ) :
    gomesQuarticChargeMeasure b 0 = volume := by
  have h : (fun x => ENNReal.ofReal (gomesQuarticTensorDensity b 0 x)) = 1 := by
    funext x
    simp [gomesQuarticTensorDensity_formula]
  rw [gomesQuarticChargeMeasure, h, withDensity_one]

/-- Density reweighting implements integer tensor addition on the actual quartic measures. -/
theorem gomesQuarticChargeMeasure_tensor (b : ℝ) (m n : ℤ) :
    (gomesQuarticChargeMeasure b m).withDensity
      (fun x => ENNReal.ofReal (gomesQuarticTensorDensity b n x)) =
        gomesQuarticChargeMeasure b (m + n) := by
  rw [gomesQuarticChargeMeasure, ← withDensity_mul _
    (gomesQuarticTensorDensity_continuous b m).measurable.ennreal_ofReal
    (gomesQuarticTensorDensity_continuous b n).measurable.ennreal_ofReal]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [Pi.mul_apply, gomesQuarticTensorDensity_add,
      ENNReal.ofReal_mul (gomesQuarticTensorDensity_pos b m x).le]

/-- Dual cancellation always returns infinite uniform volume. -/
theorem gomesQuarticChargeMeasure_dual_cancel (b : ℝ) (n : ℤ) :
    (gomesQuarticChargeMeasure b n).withDensity
      (fun x => ENNReal.ofReal (gomesQuarticTensorDensity b (-n) x)) = volume := by
  rw [gomesQuarticChargeMeasure_tensor, add_neg_cancel, gomesQuarticChargeMeasure_zero]

/-- The positive charge is exactly the corpus's original logarithmic coupling. -/
theorem gomesQuarticLogWeight_log (a : Set.Ioi (0 : ℝ)) :
    quarticDilatonLogWeight (Real.log a.val) = gomesQuarticLogWeight a.val := by
  rw [← gomesQuarticLogWeight_exp, Real.exp_log a.property]

/-- The already constructed quartic ground state at the charge's logarithmic coupling. -/
def gomesQuarticChargeGroundState (a : Set.Ioi (0 : ℝ)) : 𝓢(ℝ, ℂ) :=
  quarticDilatonGroundState (Real.log a.val)

/-- Explicit square-root density profile of the positive charge ground state. -/
theorem gomesQuarticChargeGroundState_apply (a : Set.Ioi (0 : ℝ)) (x : ℝ) :
    gomesQuarticChargeGroundState a x = (Real.exp (-a.val * x ^ 4 / 2) : ℂ) := by
  rw [gomesQuarticChargeGroundState, quarticDilatonGroundState_apply, Real.exp_log a.property]

/-- The transported ground state is nonzero on the actual Schwartz domain. -/
theorem gomesQuarticChargeGroundState_ne_zero (a : Set.Ioi (0 : ℝ)) :
    gomesQuarticChargeGroundState a ≠ 0 := quarticDilatonGroundState_ne_zero _

/-- Positive effective charge has the exact zero-energy state supplied by the corpus. -/
theorem gomesQuarticChargeGroundState_kernel (a : Set.Ioi (0 : ℝ)) :
    dilatonHamiltonianCLM (gomesQuarticLogWeight a.val) (gomesQuarticChargeGroundState a) = 0 := by
  rw [← gomesQuarticLogWeight_log, gomesQuarticChargeGroundState]
  exact quarticDilatonGroundState_eigenfunction _

/-- The positive-charge kernel is precisely one scalar line. -/
theorem gomesQuarticChargeGroundState_span (a : Set.Ioi (0 : ℝ)) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (gomesQuarticLogWeight a.val) ψ = 0 ↔
      ∃ c : ℂ, ψ = c • gomesQuarticChargeGroundState a := by
  constructor
  · intro h
    refine ⟨ψ 0, ?_⟩
    rw [← gomesQuarticLogWeight_log] at h
    exact (quarticDilaton_kernel_span _ ψ).mp h
  · rintro ⟨c, rfl⟩
    rw [map_smul, gomesQuarticChargeGroundState_kernel, smul_zero]

/-- The complete zero-mode existence boundary is positive effective charge. -/
theorem gomesQuarticHamiltonian_nonzero_kernel_iff (a : ℝ) :
    (∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧ dilatonHamiltonianCLM (gomesQuarticLogWeight a) ψ = 0) ↔
      0 < a := by
  constructor
  · rintro ⟨ψ, hψ, hk⟩
    have hc := (dilatonHamiltonian_kernel_classification _ _).mp hk
    let c := dilatonUndressed (gomesQuarticLogWeight a) ψ 0
    have hcn : c ≠ 0 := by
      intro hz
      apply hψ
      ext x
      have hx : dilatonGauge (gomesQuarticLogWeight a) x * ψ x = c := hc x
      rw [hz] at hx
      exact (mul_eq_zero.mp hx).resolve_left (dilatonGauge_ne_zero _ x)
    have hint := dilatonUndressed_weighted_integrable (gomesQuarticLogWeight a) ψ
    have heq : (fun x => dilatonWeight (gomesQuarticLogWeight a) x *
        ‖dilatonUndressed (gomesQuarticLogWeight a) ψ x‖ ^ 2) =
        (fun x => dilatonWeight (gomesQuarticLogWeight a) x * ‖c‖ ^ 2) := by
      funext x
      rw [hc x]
    rw [heq] at hint
    have hw := (integrable_mul_const_iff
      (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hcn)))
      (dilatonWeight (gomesQuarticLogWeight a))).mp hint
    have hden : gomesQuarticTensorDensity a 1 = dilatonWeight (gomesQuarticLogWeight a) := by
      simp only [gomesQuarticTensorDensity, gomesQuarticTensorLogWeight, Int.cast_one, one_mul]
    have ha := (gomesQuarticTensorDensity_integrable_iff a 1).mp (hden.symm ▸ hw)
    simpa using ha
  · intro ha
    exact ⟨gomesQuarticChargeGroundState ⟨a, ha⟩,
      gomesQuarticChargeGroundState_ne_zero ⟨a, ha⟩, gomesQuarticChargeGroundState_kernel ⟨a, ha⟩⟩

/-- Measure finiteness and existence of a nonzero charged Schwartz ground state coincide exactly. -/
theorem gomesQuarticChargeMeasure_ground_state_iff (b : ℝ) (n : ℤ) :
    IsFiniteMeasure (gomesQuarticChargeMeasure b n) ↔
      ∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧
        dilatonHamiltonianCLM (gomesQuarticTensorLogWeight b n) ψ = 0 := by
  rw [gomesQuarticChargeMeasure_finite_iff]
  exact (gomesQuarticHamiltonian_nonzero_kernel_iff ((n : ℝ) * b)).symm

/-- The finite constructor retains the exact original charged density measure. -/
def gomesQuarticChargeSource (b : ℝ) (n : GomesQuarticFiniteCharge b) : FiniteMeasure ℝ :=
  ⟨gomesQuarticChargeMeasure b n.val, (gomesQuarticChargeMeasure_finite_iff b n.val).mpr n.property⟩

/-- No normalization or truncation separates the finite source from its raw measure. -/
theorem gomesQuarticChargeSource_measure (b : ℝ) (n : GomesQuarticFiniteCharge b) :
    (gomesQuarticChargeSource b n : Measure ℝ) = gomesQuarticChargeMeasure b n.val := rfl

end GaloisForLFunctions.HTGeometry
