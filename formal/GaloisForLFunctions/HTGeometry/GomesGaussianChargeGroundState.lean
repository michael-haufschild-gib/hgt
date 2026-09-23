import GaloisForLFunctions.HTGeometry.GomesGaussianChargeMeasure
import GaloisForLFunctions.HTGeometry.DilatonGroundStates
import GaloisForLFunctions.HTGeometry.RiemannGaussian.GaussianSchwartz

/-!
# Finite tensor-charge measures are exactly the charges with a Schwartz ground state

The integer-charge experiment of arXiv:2509.25276v7 section 5.2 meets the corpus's
factorized dilaton Hamiltonian. The Gaussian measure cutoff is exactly the existence
boundary for a nonzero zero-energy Schwartz state. Inside that sector the kernel is
one-dimensional. The Gaussian constructor and the general kernel theorem are reused;
no decay, integrability, or spectral assumption is supplied to the final classifications.
-/

noncomputable section
open MeasureTheory
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- The existing positive-width Gaussian, embedded into the complex Schwartz domain. -/
def gomesGaussianChargeGroundState (a : Set.Ioi (0 : ℝ)) : 𝓢(ℝ, ℂ) :=
  (RiemannGaussian.centeredGaussianSchwartz
    ⟨Real.pi * a.val, mul_pos Real.pi_pos a.property⟩).postcompCLM Complex.ofRealCLM

/-- The ground state is the square root of the Gaussian density. -/
theorem gomesGaussianChargeGroundState_apply (a : Set.Ioi (0 : ℝ)) (x : ℝ) :
    gomesGaussianChargeGroundState a x = (Real.exp (-Real.pi * a.val * x ^ (2 : ℕ)) : ℂ) := by
  change (RiemannGaussian.centeredGaussianSchwartz
    ⟨Real.pi * a.val, mul_pos Real.pi_pos a.property⟩ x : ℂ) = _
  rw [RiemannGaussian.centeredGaussianSchwartz_apply]
  congr 2
  ring

/-- Evaluation at the origin fixes the normalization. -/
theorem gomesGaussianChargeGroundState_zero (a : Set.Ioi (0 : ℝ)) :
    gomesGaussianChargeGroundState a 0 = 1 := by
  simp [gomesGaussianChargeGroundState_apply]

/-- The constructed Schwartz state is nonzero. -/
theorem gomesGaussianChargeGroundState_ne_zero (a : Set.Ioi (0 : ℝ)) :
    gomesGaussianChargeGroundState a ≠ 0 := by
  intro h
  have hx := congrArg (fun f : 𝓢(ℝ, ℂ) => f 0) h
  exact one_ne_zero (by simpa only [gomesGaussianChargeGroundState_zero, zero_apply] using hx)

/-- Removing the Gaussian gauge leaves the constant unit profile. -/
theorem gomesGaussianChargeGroundState_undressed (a : Set.Ioi (0 : ℝ)) (x : ℝ) :
    dilatonUndressed (gomesGaussianLogWeight a.val) (gomesGaussianChargeGroundState a) x = 1 := by
  rw [dilatonUndressed, gomesGaussianChargeGroundState_apply]
  simp only [dilatonGauge, gomesGaussianLogWeight_eval]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  rw [show -(-2 * Real.pi * a.val * x ^ (2 : ℕ)) / 2 + -Real.pi * a.val * x ^ (2 : ℕ) = 0 by ring,
    Real.exp_zero, Complex.ofReal_one]

/-- The positive-charge Gaussian is annihilated by the actual Schwartz Hamiltonian. -/
theorem gomesGaussianChargeGroundState_kernel (a : Set.Ioi (0 : ℝ)) :
    dilatonHamiltonianCLM (gomesGaussianLogWeight a.val) (gomesGaussianChargeGroundState a) = 0 := by
  apply (dilatonHamiltonian_kernel_classification _ _).mpr
  intro x
  rw [gomesGaussianChargeGroundState_undressed, gomesGaussianChargeGroundState_undressed]

/-- Every positive-charge zero mode is a scalar multiple of the explicit Gaussian. -/
theorem gomesGaussianChargeGroundState_span (a : Set.Ioi (0 : ℝ)) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (gomesGaussianLogWeight a.val) ψ = 0 ↔
      ∃ c : ℂ, ψ = c • gomesGaussianChargeGroundState a := by
  constructor
  · intro h
    have hk := (dilatonHamiltonian_kernel_classification _ _).mp h
    let c := dilatonUndressed (gomesGaussianLogWeight a.val) ψ 0
    refine ⟨c, ?_⟩
    ext x
    apply mul_left_cancel₀ (dilatonGauge_ne_zero (gomesGaussianLogWeight a.val) x)
    change dilatonGauge (gomesGaussianLogWeight a.val) x * ψ x =
      dilatonGauge (gomesGaussianLogWeight a.val) x * (c * gomesGaussianChargeGroundState a x)
    have hx : dilatonGauge (gomesGaussianLogWeight a.val) x * ψ x = c := hk x
    have hg : dilatonGauge (gomesGaussianLogWeight a.val) x *
        gomesGaussianChargeGroundState a x = 1 := gomesGaussianChargeGroundState_undressed a x
    rw [hx]
    calc
      c = c * 1 := (mul_one c).symm
      _ = c * (dilatonGauge (gomesGaussianLogWeight a.val) x *
          gomesGaussianChargeGroundState a x) := by rw [hg]
      _ = _ := by ring
  · rintro ⟨c, rfl⟩
    rw [map_smul, gomesGaussianChargeGroundState_kernel, smul_zero]

/-- A nonzero Schwartz zero mode exists exactly for positive Gaussian effective charge. -/
theorem gomesGaussianHamiltonian_nonzero_kernel_iff (a : ℝ) :
    (∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧ dilatonHamiltonianCLM (gomesGaussianLogWeight a) ψ = 0) ↔
      0 < a := by
  constructor
  · rintro ⟨ψ, hψ, hk⟩
    have hc := (dilatonHamiltonian_kernel_classification _ _).mp hk
    let c := dilatonUndressed (gomesGaussianLogWeight a) ψ 0
    have hcn : c ≠ 0 := by
      intro hz
      apply hψ
      ext x
      have hx : dilatonGauge (gomesGaussianLogWeight a) x * ψ x = c := hc x
      rw [hz] at hx
      exact (mul_eq_zero.mp hx).resolve_left (dilatonGauge_ne_zero _ x)
    have hint := dilatonUndressed_weighted_integrable (gomesGaussianLogWeight a) ψ
    have heq : (fun x => dilatonWeight (gomesGaussianLogWeight a) x *
        ‖dilatonUndressed (gomesGaussianLogWeight a) ψ x‖ ^ (2 : ℕ)) =
        (fun x => dilatonWeight (gomesGaussianLogWeight a) x * ‖c‖ ^ (2 : ℕ)) := by
      funext x
      rw [hc x]
    rw [heq] at hint
    have hw := (integrable_mul_const_iff
      (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hcn)))
      (dilatonWeight (gomesGaussianLogWeight a))).mp hint
    have hden : gomesGaussianTensorDensity a 1 = dilatonWeight (gomesGaussianLogWeight a) := by
      simp only [gomesGaussianTensorDensity, gomesGaussianTensorLogWeight, Int.cast_one, one_mul]
    have ha := (gomesGaussianTensorDensity_integrable_iff a 1).mp (hden.symm ▸ hw)
    simpa using ha
  · intro ha
    exact ⟨gomesGaussianChargeGroundState ⟨a, ha⟩,
      gomesGaussianChargeGroundState_ne_zero ⟨a, ha⟩, gomesGaussianChargeGroundState_kernel ⟨a, ha⟩⟩

/-- The complete nonpositive sector has trivial Schwartz kernel, including neutral charge. -/
theorem gomesGaussianHamiltonian_trivial_kernel_iff (a : ℝ) :
    (∀ ψ : 𝓢(ℝ, ℂ), dilatonHamiltonianCLM (gomesGaussianLogWeight a) ψ = 0 ↔ ψ = 0) ↔
      a ≤ 0 := by
  rw [← not_lt, ← gomesGaussianHamiltonian_nonzero_kernel_iff]
  constructor
  · rintro h ⟨ψ, hψ, hk⟩
    exact hψ ((h ψ).mp hk)
  · intro h ψ
    constructor
    · intro hk
      by_contra hn
      exact h ⟨ψ, hn, hk⟩
    · rintro rfl
      exact map_zero _

/-- Measure finiteness is exactly the existence of a nonzero charged Schwartz ground state. -/
theorem gomesGaussianChargeMeasure_ground_state_iff (b : ℝ) (n : ℤ) :
    IsFiniteMeasure (gomesGaussianChargeMeasure b n) ↔
      ∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧
        dilatonHamiltonianCLM (gomesGaussianTensorLogWeight b n) ψ = 0 := by
  rw [gomesGaussianChargeMeasure_finite_iff]
  exact (gomesGaussianHamiltonian_nonzero_kernel_iff ((n : ℝ) * b)).symm

/-- A charge and its dual can never both carry a nonzero Schwartz zero mode. -/
theorem gomesGaussianCharge_no_dual_ground_pair (b : ℝ) (n : ℤ) :
    ¬ ((∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧
        dilatonHamiltonianCLM (gomesGaussianTensorLogWeight b n) ψ = 0) ∧
      (∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧
        dilatonHamiltonianCLM (gomesGaussianTensorLogWeight b (-n)) ψ = 0)) := by
  rw [← gomesGaussianChargeMeasure_ground_state_iff, ← gomesGaussianChargeMeasure_ground_state_iff]
  exact gomesGaussianChargeMeasure_no_finite_dual b n

end GaloisForLFunctions.HTGeometry
