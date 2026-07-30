import GaloisForLFunctions.RHTower.SuzukiGlobalPhaseConjugacy
import GaloisForLFunctions.RHTower.SuzukiDonoghueSpectralMeasure
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Suzuki's compactified inverse-phase lattice profile

For a proper normalized Suzuki phase `φ : ℝ ≃o ℝ`, define its centered inverse and Cayley
compactification by

`X(y) = φ⁻¹(π + y)`,  `U(y) = arctan(X(y))`.

On paper the common Livšic anchor `Θ(i)=0` factors one Cayley Blaschke factor.  The remaining inner
factor has nonnegative boundary phase speed, giving the sharp floor

`2 ≤ φ'(x) * (1 + x²)`.

This module formalizes the dependency-closed consequence.  The compactified inverse speed is

`U'(y) = 1 / (φ'(X(y)) * (1 + X(y)²))`,

so it lies in `(0, 1/2]` and `U` is globally `1/2`-Lipschitz.  At every fixed even Clark phase
level, twice this derivative is exactly the normalized Donoghue probability mass.  Thus values and
first derivatives on one fixed phase lattice reconstruct both moving support and atom weights.

No RH assumption and no numerical computation occur.
-/

open Real

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## Compactified inverse phase -/

/-- Centered inverse of a proper normalized Suzuki phase. -/
def suzukiCenteredInversePhase (φ : ℝ ≃o ℝ) (y : ℝ) : ℝ :=
  φ.symm (Real.pi + y)

/-- Cayley compactification of the centered inverse phase. -/
def suzukiCompactifiedInversePhase (φ : ℝ ≃o ℝ) (y : ℝ) : ℝ :=
  Real.arctan (suzukiCenteredInversePhase φ y)

/-- Fixed centered phase level of the `k`-th even Clark atom. -/
def suzukiEvenPhaseLattice (k : ℤ) : ℝ :=
  (2 * (k : ℝ) - 1) * Real.pi

/-- The centered inverse has exactly the prescribed lifted phase. -/
@[simp] theorem suzukiCenteredInversePhase_phase (φ : ℝ ≃o ℝ) (y : ℝ) :
    φ (suzukiCenteredInversePhase φ y) = Real.pi + y := by
  simp [suzukiCenteredInversePhase]

/-- Compactification loses no finite pole position. -/
@[simp] theorem tan_suzukiCompactifiedInversePhase (φ : ℝ ≃o ℝ) (y : ℝ) :
    Real.tan (suzukiCompactifiedInversePhase φ y) =
      suzukiCenteredInversePhase φ y := by
  simp [suzukiCompactifiedInversePhase]

/-- Every compactified inverse-phase value lies strictly inside the projective interval. -/
theorem suzukiCompactifiedInversePhase_mem_Ioo (φ : ℝ ≃o ℝ) (y : ℝ) :
    suzukiCompactifiedInversePhase φ y ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
  Real.arctan_mem_Ioo _

/-- Both inverse phase and its compactification are strictly increasing. -/
theorem suzukiCenteredInversePhase_strictMono (φ : ℝ ≃o ℝ) :
    StrictMono (suzukiCenteredInversePhase φ) := by
  intro y z hyz
  exact φ.symm.strictMono (by linarith)

theorem suzukiCompactifiedInversePhase_strictMono (φ : ℝ ≃o ℝ) :
    StrictMono (suzukiCompactifiedInversePhase φ) :=
  Real.arctan_strictMono.comp (suzukiCenteredInversePhase_strictMono φ)

/-- The standard phase normalization `φ(0)=π` centers the compactified profile at zero. -/
@[simp] theorem suzukiCenteredInversePhase_zero
    {φ : ℝ ≃o ℝ} (hφzero : φ 0 = Real.pi) :
    suzukiCenteredInversePhase φ 0 = 0 := by
  rw [suzukiCenteredInversePhase, add_zero, ← hφzero, φ.symm_apply_apply]

@[simp] theorem suzukiCompactifiedInversePhase_zero
    {φ : ℝ ≃o ℝ} (hφzero : φ 0 = Real.pi) :
    suzukiCompactifiedInversePhase φ 0 = 0 := by
  rw [suzukiCompactifiedInversePhase, suzukiCenteredInversePhase_zero hφzero,
    Real.arctan_zero]

/-- Odd Donoghue symmetry makes the centered inverse phase odd. -/
theorem suzukiCenteredInversePhase_neg
    {φ : ℝ ≃o ℝ}
    (hreflection : ∀ x, φ (-x) = 2 * Real.pi - φ x) (y : ℝ) :
    suzukiCenteredInversePhase φ (-y) = -suzukiCenteredInversePhase φ y := by
  apply φ.injective
  rw [suzukiCenteredInversePhase_phase, hreflection, suzukiCenteredInversePhase_phase]
  ring

/-- Hence the compactified inverse phase is odd as well. -/
theorem suzukiCompactifiedInversePhase_neg
    {φ : ℝ ≃o ℝ}
    (hreflection : ∀ x, φ (-x) = 2 * Real.pi - φ x) (y : ℝ) :
    suzukiCompactifiedInversePhase φ (-y) =
      -suzukiCompactifiedInversePhase φ y := by
  rw [suzukiCompactifiedInversePhase, suzukiCenteredInversePhase_neg hreflection,
    Real.arctan_neg, suzukiCompactifiedInversePhase]

/-! ## Anchored phase floor and inverse derivatives -/

/-- One Cayley Blaschke factor contributes `2/(1+x²)` to phase speed; every residual inner phase
has nonnegative speed. -/
theorem suzukiAnchoredPhaseSpeed_floor
    {x phaseSpeed residualSpeed : ℝ}
    (hphaseSpeed : phaseSpeed = 2 / (1 + x ^ 2) + residualSpeed)
    (hresidualSpeed : 0 ≤ residualSpeed) :
    2 ≤ phaseSpeed * (1 + x ^ 2) := by
  have hxpos : 0 < 1 + x ^ 2 := by positivity
  rw [hphaseSpeed]
  have hmul : 0 ≤ residualSpeed * (1 + x ^ 2) :=
    mul_nonneg hresidualSpeed hxpos.le
  field_simp
  linarith

/-- The derivative of the centered global inverse phase is reciprocal phase speed. -/
theorem hasDerivAt_suzukiCenteredInversePhase
    {φ : ℝ ≃o ℝ} {y phaseSpeed : ℝ}
    (hphase : HasDerivAt φ phaseSpeed (suzukiCenteredInversePhase φ y))
    (hphaseSpeed : phaseSpeed ≠ 0) :
    HasDerivAt (suzukiCenteredInversePhase φ) phaseSpeed⁻¹ y := by
  have hinv : HasDerivAt (φ.symm : ℝ → ℝ) phaseSpeed⁻¹ (Real.pi + y) :=
    hphase.of_local_left_inverse φ.symm.continuous.continuousAt hphaseSpeed
      (Filter.Eventually.of_forall (fun z => φ.apply_symm_apply z))
  have hadd : HasDerivAt (fun z : ℝ => Real.pi + z) 1 y := by
    simpa only [Pi.add_apply, id_eq, zero_add] using!
      (hasDerivAt_const y Real.pi).add (hasDerivAt_id y)
  simpa [suzukiCenteredInversePhase] using! hinv.comp y hadd

/-- Exact compactified inverse-phase derivative. -/
theorem hasDerivAt_suzukiCompactifiedInversePhase
    {φ : ℝ ≃o ℝ} {y phaseSpeed : ℝ}
    (hphase : HasDerivAt φ phaseSpeed (suzukiCenteredInversePhase φ y))
    (hphaseSpeed : phaseSpeed ≠ 0) :
    HasDerivAt (suzukiCompactifiedInversePhase φ)
      (1 / (phaseSpeed * (1 + suzukiCenteredInversePhase φ y ^ 2))) y := by
  have hinv := hasDerivAt_suzukiCenteredInversePhase hphase hphaseSpeed
  simpa [suzukiCompactifiedInversePhase, one_div, mul_comm, mul_left_comm, mul_assoc]
    using! hinv.arctan

/-- The sharp anchored floor confines compactified inverse speed to `(0,1/2]`. -/
theorem suzukiCompactifiedInversePhase_speed_mem
    {φ : ℝ ≃o ℝ} {y phaseSpeed : ℝ}
    (hfloor : 2 ≤ phaseSpeed * (1 + suzukiCenteredInversePhase φ y ^ 2)) :
    0 < 1 / (phaseSpeed * (1 + suzukiCenteredInversePhase φ y ^ 2)) ∧
      1 / (phaseSpeed * (1 + suzukiCenteredInversePhase φ y ^ 2)) ≤ 1 / 2 := by
  have hdpos : 0 < phaseSpeed * (1 + suzukiCenteredInversePhase φ y ^ 2) :=
    lt_of_lt_of_le (by norm_num) hfloor
  constructor
  · exact one_div_pos.mpr hdpos
  · exact (div_le_div_iff₀ hdpos (by norm_num : (0 : ℝ) < 2)).2 (by linarith)

/-- Derivative form of the sharp compactified speed bound. -/
theorem deriv_suzukiCompactifiedInversePhase_mem
    {φ : ℝ ≃o ℝ} {y phaseSpeed : ℝ}
    (hphase : HasDerivAt φ phaseSpeed (suzukiCenteredInversePhase φ y))
    (hphaseSpeed : phaseSpeed ≠ 0)
    (hfloor : 2 ≤ phaseSpeed * (1 + suzukiCenteredInversePhase φ y ^ 2)) :
    0 < deriv (suzukiCompactifiedInversePhase φ) y ∧
      deriv (suzukiCompactifiedInversePhase φ) y ≤ 1 / 2 := by
  rw [(hasDerivAt_suzukiCompactifiedInversePhase hphase hphaseSpeed).deriv]
  exact suzukiCompactifiedInversePhase_speed_mem hfloor

/-! ## Fixed-lattice Donoghue probability holography -/

/-- A normalized Donoghue atom is exactly twice the compactified inverse-phase derivative at its
fixed lifted phase label. -/
theorem suzukiPhaseProbabilityMass_eq_two_mul_compactifiedDeriv
    {φ : ℝ ≃o ℝ} {y phaseSpeed probabilityMass : ℝ}
    (hphase : HasDerivAt φ phaseSpeed (suzukiCenteredInversePhase φ y))
    (hphaseSpeed : phaseSpeed ≠ 0)
    (hprobabilityMass : probabilityMass =
      2 / (phaseSpeed * (1 + suzukiCenteredInversePhase φ y ^ 2))) :
    probabilityMass = 2 * deriv (suzukiCompactifiedInversePhase φ) y := by
  rw [(hasDerivAt_suzukiCompactifiedInversePhase hphase hphaseSpeed).deriv,
    hprobabilityMass]
  ring

/-- The fixed odd-`π` lattice is precisely the centered even-extension phase lattice. -/
theorem pi_add_suzukiEvenPhaseLattice (k : ℤ) :
    Real.pi + suzukiEvenPhaseLattice k = 2 * (k : ℝ) * Real.pi := by
  rw [suzukiEvenPhaseLattice]
  ring

/-- Its physical point is the corresponding globally phase-labeled pole. -/
theorem suzukiCenteredInversePhase_evenLattice (φ : ℝ ≃o ℝ) (k : ℤ) :
    suzukiCenteredInversePhase φ (suzukiEvenPhaseLattice k) =
      suzukiPhasePole φ (2 * (k : ℝ) * Real.pi) := by
  rw [suzukiCenteredInversePhase, suzukiPhasePole,
    pi_add_suzukiEvenPhaseLattice]

/-- If the atom probabilities sum to one, their compactified derivative samples do too. -/
theorem hasSum_two_mul_suzukiCompactifiedDeriv_one
    {φ : ℝ ≃o ℝ} {probabilityMass : ℤ → ℝ}
    (hmass : ∀ k, probabilityMass k =
      2 * deriv (suzukiCompactifiedInversePhase φ) (suzukiEvenPhaseLattice k))
    (hprobability : HasSum probabilityMass 1) :
    HasSum (fun k : ℤ =>
      2 * deriv (suzukiCompactifiedInversePhase φ) (suzukiEvenPhaseLattice k)) 1 := by
  have hfun : probabilityMass = fun k : ℤ =>
      2 * deriv (suzukiCompactifiedInversePhase φ) (suzukiEvenPhaseLattice k) :=
    funext hmass
  rw [← hfun]
  exact hprobability

/-! ## Projective endpoint mass -/

/-- At positive projective infinity, the Donoghue probability kernel becomes the linear
Nevanlinna kernel.  Thus probability escaping through this end contributes linear mass. -/
theorem tendsto_suzukiDonoghueKernel_atTop (z : ℂ) :
    Filter.Tendsto (fun t : ℝ => suzukiDonoghueKernel t z)
      Filter.atTop (nhds z) := by
  have hden : Filter.Tendsto (fun t : ℝ => (t : ℂ) - z) Filter.atTop
      (Bornology.cobounded ℂ) :=
    (tendsto_sub_const_cobounded z).comp (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
  have hinv : Filter.Tendsto (fun t : ℝ => ((t : ℂ) - z)⁻¹) Filter.atTop (nhds 0) :=
    Filter.tendsto_inv₀_cobounded.comp hden
  simpa only [suzukiDonoghueKernel, div_eq_mul_inv, mul_zero, add_zero] using
    (tendsto_const_nhds (x := z)).add
      ((tendsto_const_nhds (x := z ^ 2 + 1)).mul hinv)

/-- Negative projective infinity has the same Donoghue kernel value.  The Herglotz transform sees
the sum of the two endpoint masses; Suzuki evenness separates them equally. -/
theorem tendsto_suzukiDonoghueKernel_atBot (z : ℂ) :
    Filter.Tendsto (fun t : ℝ => suzukiDonoghueKernel t z)
      Filter.atBot (nhds z) := by
  have hden : Filter.Tendsto (fun t : ℝ => (t : ℂ) - z) Filter.atBot
      (Bornology.cobounded ℂ) :=
    (tendsto_sub_const_cobounded z).comp (RCLike.tendsto_ofReal_atBot_cobounded ℂ)
  have hinv : Filter.Tendsto (fun t : ℝ => ((t : ℂ) - z)⁻¹) Filter.atBot (nhds 0) :=
    Filter.tendsto_inv₀_cobounded.comp hden
  simpa only [suzukiDonoghueKernel, div_eq_mul_inv, mul_zero, add_zero] using
    (tendsto_const_nhds (x := z)).add
      ((tendsto_const_nhds (x := z ^ 2 + 1)).mul hinv)

/-! ## Global equi-Lipschitz compactness input -/

/-- The sharp anchored phase floor makes every compactified inverse phase globally
`1/2`-Lipschitz.  This is the exact Arzelà--Ascoli input used by the paper theorem. -/
theorem suzukiCompactifiedInversePhase_lipschitz
    (φ : ℝ ≃o ℝ) (phaseSpeed : ℝ → ℝ)
    (hphase : ∀ y, HasDerivAt φ (phaseSpeed y) (suzukiCenteredInversePhase φ y))
    (hphaseSpeed : ∀ y, phaseSpeed y ≠ 0)
    (hfloor : ∀ y, 2 ≤ phaseSpeed y * (1 + suzukiCenteredInversePhase φ y ^ 2)) :
    LipschitzWith (2 : NNReal)⁻¹ (suzukiCompactifiedInversePhase φ) := by
  have hderiv : ∀ y, deriv (suzukiCompactifiedInversePhase φ) y =
      1 / (phaseSpeed y * (1 + suzukiCenteredInversePhase φ y ^ 2)) := by
    intro y
    exact (hasDerivAt_suzukiCompactifiedInversePhase (hphase y) (hphaseSpeed y)).deriv
  have hdiff : Differentiable ℝ (suzukiCompactifiedInversePhase φ) := by
    intro y
    exact (hasDerivAt_suzukiCompactifiedInversePhase
      (hphase y) (hphaseSpeed y)).differentiableAt
  apply lipschitzWith_of_nnnorm_deriv_le hdiff
  intro y
  apply NNReal.coe_le_coe.1
  simp only [coe_nnnorm, NNReal.coe_inv, NNReal.coe_ofNat]
  rw [hderiv]
  have hbound := suzukiCompactifiedInversePhase_speed_mem (hfloor y)
  rw [Real.norm_eq_abs, abs_of_pos hbound.1]
  simpa only [one_div] using hbound.2

end GaloisForLFunctions.RHTower
