import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Continuum chronometric rigidity for metric gravity

On a coordinate-trivialized continuum region, a metric field is an indexed family of symmetric
bilinear forms. Its signed squared-interval data are the diagonal values `g x v v`. Polarization
recovers every off-diagonal metric component, so squared-interval data are injective.

For an arbitrary source operator `law : Geometry → Source`, its branch-safe chronometric graph is
the range of `geometry ↦ (law geometry, encode geometry)`. If the observation encoding is
injective, equality of chronometric graphs is equivalent to equality of the complete operators.
This needs neither linearity of the operator nor uniqueness of a source-to-solution map.

These are unconditional continuum-indexed algebraic theorems. A physical application must still
identify the index and vector fibers with a Lorentzian tangent bundle, construct the clock/radar
protocol yielding the signed diagonal field, and quotient by diffeomorphism and gauge.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

open scoped Matrix

/-- A coordinate-trivialized continuum metric field: every event carries a symmetric real
bilinear form on the model tangent fiber. Lorentz signature is not needed for polarization. -/
structure ChronometricMetricField (Event : Type u) (Tangent : Type v)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  form : Event → LinearMap.BilinForm ℝ Tangent
  symmetric : ∀ event u v, form event u v = form event v u

namespace ChronometricMetricField

variable {Event : Type u} {Tangent : Type v}
  [AddCommGroup Tangent] [Module ℝ Tangent]

/-- Two chronometric metric fields with identical bilinear forms are identical. -/
@[ext]
theorem ext {g h : ChronometricMetricField Event Tangent}
    (hform : g.form = h.form) : g = h := by
  cases g
  cases h
  simp_all

/-- Signed infinitesimal squared-clock data of a metric field. For Lorentz signature, negative
values are squared proper-time rates, zero values are null, and positive values are spacelike. -/
def squaredInterval (g : ChronometricMetricField Event Tangent) :
    Event → Tangent → ℝ :=
  fun event v => g.form event v v

/-- Polarization formula recovering one metric component from three squared intervals. -/
theorem form_eq_half_squaredInterval_polarization
    (g : ChronometricMetricField Event Tangent)
    (event : Event) (u v : Tangent) :
    g.form event u v =
      (squaredInterval g event (u + v) -
        squaredInterval g event u - squaredInterval g event v) / 2 := by
  simp only [squaredInterval, map_add, LinearMap.add_apply]
  rw [g.symmetric event v u]
  ring

/-- **Squared clock intervals determine the complete continuum metric field.** -/
theorem squaredInterval_injective :
    Function.Injective
      (squaredInterval :
        ChronometricMetricField Event Tangent → Event → Tangent → ℝ) := by
  intro g h heq
  apply ext
  funext event
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  rw [form_eq_half_squaredInterval_polarization,
    form_eq_half_squaredInterval_polarization, heq]

end ChronometricMetricField

/-- Branch-safe solution graph of a law after encoding each geometry by its complete observation
data. Multiple geometries with the same source remain separate graph points when `encode` is
injective. -/
def chronometricSolutionGraph
    {Geometry : Type u} {Source : Type v} {Observation : Type w}
    (encode : Geometry → Observation) (law : Geometry → Source) :
    Set (Source × Observation) :=
  Set.range fun geometry => (law geometry, encode geometry)

/-- **Abstract chronometric operator rigidity.** An injective observation encoding turns equality
of branch-safe solution graphs into equality of arbitrary nonlinear laws. -/
theorem chronometricSolutionGraph_eq_iff_of_injective
    {Geometry : Type u} {Source : Type v} {Observation : Type w}
    {encode : Geometry → Observation} (hencode : Function.Injective encode)
    (law₁ law₂ : Geometry → Source) :
    chronometricSolutionGraph encode law₁ =
        chronometricSolutionGraph encode law₂ ↔
      law₁ = law₂ := by
  constructor
  · intro hgraph
    funext geometry
    have hmem :
        (law₁ geometry, encode geometry) ∈
          chronometricSolutionGraph encode law₂ := by
      rw [← hgraph]
      exact ⟨geometry, rfl⟩
    rcases hmem with ⟨other, hother⟩
    have hsource : law₂ other = law₁ geometry :=
      congrArg Prod.fst hother
    have hobservation : encode other = encode geometry :=
      congrArg Prod.snd hother
    have hgeometry : other = geometry := hencode hobservation
    subst other
    exact hsource.symm
  · intro hlaw
    subst law₂
    rfl

/-- **Continuum chronometric gravity law.** Two source operators on coordinate-trivialized
continuum metric fields have identical complete squared-clock solution graphs exactly when the
operators themselves are identical. No perturbative, analytic, or unique-solution hypothesis is
used. -/
theorem continuumChronometricOperatorRigidity
    {Event : Type u} {Tangent : Type v}
    [AddCommGroup Tangent] [Module ℝ Tangent]
    {Source : Type w}
    (law₁ law₂ : ChronometricMetricField Event Tangent → Source) :
    chronometricSolutionGraph ChronometricMetricField.squaredInterval law₁ =
        chronometricSolutionGraph ChronometricMetricField.squaredInterval law₂ ↔
      law₁ = law₂ :=
  chronometricSolutionGraph_eq_iff_of_injective
    ChronometricMetricField.squaredInterval_injective law₁ law₂

/-! ## Exact two-quadrature clock phase recovery -/

/-- Reduced two-level clock state after a controlled unitary whose system expectation is `z`.
The off-diagonal coherence carries both quadratures of `z`. -/
noncomputable def chronometricRamseyClockState (z : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ) / 2, star z / 2;
     z / 2, (1 : ℂ) / 2]

/-- Pauli-X readout of the two-level clock. -/
def chronometricRamseyPauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1;
     1, 0]

/-- Pauli-Y readout of the two-level clock. -/
def chronometricRamseyPauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I;
     Complex.I, 0]

/-- The X quadrature of the controlled clock is exactly the real part of the system-unitary
expectation. -/
theorem trace_chronometricRamseyClockState_mul_pauliX (z : ℂ) :
    Matrix.trace
        (chronometricRamseyClockState z * chronometricRamseyPauliX) =
      z.re := by
  apply Complex.ext
  · simp [chronometricRamseyClockState, chronometricRamseyPauliX,
      Matrix.trace, Fin.sum_univ_two]
  · simp [chronometricRamseyClockState, chronometricRamseyPauliX,
      Matrix.trace, Fin.sum_univ_two]
    ring

/-- The Y quadrature of the controlled clock is exactly the imaginary part of the system-unitary
expectation. -/
theorem trace_chronometricRamseyClockState_mul_pauliY (z : ℂ) :
    Matrix.trace
        (chronometricRamseyClockState z * chronometricRamseyPauliY) =
      z.im := by
  apply Complex.ext
  · simp [chronometricRamseyClockState, chronometricRamseyPauliY,
      Matrix.trace, Fin.sum_univ_two]
    ring
  · simp [chronometricRamseyClockState, chronometricRamseyPauliY,
      Matrix.trace, Fin.sum_univ_two]

/-- Complete pair of equatorial clock readouts for one controlled expectation. -/
noncomputable def chronometricRamseyQuadratures (z : ℂ) : ℂ × ℂ :=
  (Matrix.trace
      (chronometricRamseyClockState z * chronometricRamseyPauliX),
    Matrix.trace
      (chronometricRamseyClockState z * chronometricRamseyPauliY))

/-- **Two clock quadratures recover the complete complex expectation.** This closes the phase-loss
obstruction of a probability-only detector readout. -/
theorem chronometricRamseyQuadratures_injective :
    Function.Injective chronometricRamseyQuadratures := by
  intro z w h
  apply Complex.ext
  · simpa [chronometricRamseyQuadratures,
      trace_chronometricRamseyClockState_mul_pauliX] using
      congrArg Prod.fst h
  · simpa [chronometricRamseyQuadratures,
      trace_chronometricRamseyClockState_mul_pauliY] using
      congrArg Prod.snd h

/-! ## Exact order-controlled causal phase -/

/-- Ramsey quadrature data for two opposite operator orderings. -/
noncomputable def chronometricRamseyOrderQuadratures
    (ordered reverseOrdered : ℂ) :
    (ℂ × ℂ) × (ℂ × ℂ) :=
  (chronometricRamseyQuadratures ordered,
    chronometricRamseyQuadratures reverseOrdered)

/-- Both complex ordered expectations are recovered by the four Ramsey quadratures. -/
theorem chronometricRamseyOrderQuadratures_injective :
    Function.Injective
      (fun data : ℂ × ℂ =>
        chronometricRamseyOrderQuadratures data.1 data.2) := by
  rintro ⟨ordered₁, reverse₁⟩ ⟨ordered₂, reverse₂⟩ hdata
  apply Prod.ext
  · apply chronometricRamseyQuadratures_injective
    exact congrArg Prod.fst hdata
  · apply chronometricRamseyQuadratures_injective
    exact congrArg Prod.snd hdata

/-- A central order phase passes exactly to every complex-linear state functional. -/
theorem orderedExpectation_eq_phase_mul_reverse
    {A : Type*} [Ring A] [Algebra ℂ A]
    (state : A →ₗ[ℂ] ℂ) (ordered reverseOrdered : A) (phase : ℂ)
    (hphase : ordered = phase • reverseOrdered) :
    state ordered = phase * state reverseOrdered := by
  rw [hphase, map_smul]
  rfl

/-- If the reverse-order expectation is nonzero, the quotient of the two Ramsey-recoverable
complex expectations is exactly the central order phase. -/
theorem orderedExpectation_ratio_eq_phase
    {A : Type*} [Ring A] [Algebra ℂ A]
    (state : A →ₗ[ℂ] ℂ) (ordered reverseOrdered : A) (phase : ℂ)
    (hphase : ordered = phase • reverseOrdered)
    (hreverse : state reverseOrdered ≠ 0) :
    state ordered / state reverseOrdered = phase := by
  rw [orderedExpectation_eq_phase_mul_reverse
    state ordered reverseOrdered phase hphase]
  exact mul_div_cancel_right₀ phase hreverse

/-- **State-independent order-commutator phase.** If opposite orderings differ by a central scalar
phase and explicit right inverses are supplied, their group commutator is that phase times the
identity. This is the algebraic Weyl causal-phase law. -/
theorem centralOrderPhase_groupCommutator
    {A : Type*} [Ring A] [Algebra ℂ A]
    (first second firstInv secondInv : A) (phase : ℂ)
    (hphase : first * second = phase • (second * first))
    (hfirst : first * firstInv = 1)
    (hsecond : second * secondInv = 1) :
    first * second * firstInv * secondInv = phase • (1 : A) := by
  rw [hphase]
  simp only [smul_mul_assoc, mul_assoc, hfirst, mul_one, hsecond]

/-- Exact Weyl system for a real symplectic test-function space. -/
structure CausalWeylSystem
    (V : Type*) (A : Type*)
    [AddCommGroup V] [Module ℝ V] [Ring A] [Algebra ℂ A] where
  operator : V → A
  causalPairing : LinearMap.BilinForm ℝ V
  causalPairing_self : ∀ f, causalPairing f f = 0
  operator_zero : operator 0 = 1
  operator_mul : ∀ f h,
    operator f * operator h =
      Complex.exp (-(Complex.I * (causalPairing f h : ℂ)) / 2) •
        operator (f + h)

namespace CausalWeylSystem

variable {V : Type*} {A : Type*}
  [AddCommGroup V] [Module ℝ V] [Ring A] [Algebra ℂ A]

theorem causalPairing_skew (S : CausalWeylSystem V A) (f h : V) :
    S.causalPairing h f = -S.causalPairing f h := by
  have hzero := S.causalPairing_self (f + h)
  simp only [map_add, LinearMap.add_apply] at hzero
  rw [S.causalPairing_self f, S.causalPairing_self h] at hzero
  linarith

/-- Weyl relation with order swapped: exact causal phase, derived from the half-phase law. -/
theorem operator_mul_swap (S : CausalWeylSystem V A) (f h : V) :
    S.operator f * S.operator h =
      Complex.exp (-(Complex.I * (S.causalPairing f h : ℂ))) •
        (S.operator h * S.operator f) := by
  rw [S.operator_mul f h, S.operator_mul h f, add_comm,
    S.causalPairing_skew h f, Complex.ofReal_neg]
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  ring

/-- Coupling-scaled form of the Weyl causal phase. -/
theorem operator_smul_mul_swap
    (S : CausalWeylSystem V A) (lambda eta : ℝ) (f h : V) :
    S.operator (lambda • f) * S.operator (eta • h) =
      Complex.exp
          (-(Complex.I * ((lambda * eta * S.causalPairing f h : ℝ) : ℂ))) •
        (S.operator (eta • h) * S.operator (lambda • f)) := by
  rw [S.operator_mul_swap]
  congr 2
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [show eta * (lambda * S.causalPairing f h) =
      lambda * eta * S.causalPairing f h by ring]

theorem operator_mul_neg (S : CausalWeylSystem V A) (f : V) :
    S.operator f * S.operator (-f) = 1 := by
  rw [S.operator_mul]
  simp [S.causalPairing_self, S.operator_zero]

theorem operator_neg_mul (S : CausalWeylSystem V A) (f : V) :
    S.operator (-f) * S.operator f = 1 := by
  rw [S.operator_mul]
  simp [S.causalPairing_self, S.operator_zero]

/-- Exact order commutator, with the inverse Weyl operators identified as opposite smearings. -/
theorem operator_smul_groupCommutator
    (S : CausalWeylSystem V A) (lambda eta : ℝ) (f h : V) :
    S.operator (lambda • f) * S.operator (eta • h) *
          S.operator (-(lambda • f)) * S.operator (-(eta • h)) =
      Complex.exp
          (-(Complex.I * ((lambda * eta * S.causalPairing f h : ℝ) : ℂ))) •
        (1 : A) := by
  exact centralOrderPhase_groupCommutator
    (S.operator (lambda • f)) (S.operator (eta • h))
    (S.operator (-(lambda • f))) (S.operator (-(eta • h))) _
    (S.operator_smul_mul_swap lambda eta f h)
    (S.operator_mul_neg (lambda • f)) (S.operator_mul_neg (eta • h))

end CausalWeylSystem

/-- Continuity and unit normalization make Ramsey expectations nonzero near zero coupling. -/
theorem eventually_ne_zero_of_continuousAt_eq_one
    {F : ℝ × ℝ → ℂ}
    (hF : ContinuousAt F (0, 0)) (hF0 : F (0, 0) = 1) :
    ∀ᶠ p in nhds (0, 0), F p ≠ 0 := by
  exact hF.eventually_ne (by simp [hF0])

/-- Continuous order phase associated with a complexified causal pairing. Real causal pairings are
included through the canonical embedding into `ℂ`. -/
noncomputable def causalOrderPhase (causal t : ℂ) : ℂ :=
  Complex.exp (t * (-Complex.I * causal))

/-- The causal pairing is the infinitesimal generator of the continuously calibrated order phase.
This removes the fixed-phase `2π` branch ambiguity at zero coupling. -/
theorem hasDerivAt_causalOrderPhase_zero (causal : ℂ) :
    HasDerivAt (causalOrderPhase causal) (-Complex.I * causal) 0 := by
  have hlinear :
      HasDerivAt
        (fun t : ℂ => t * (-Complex.I * causal))
        (-Complex.I * causal) 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℂ) 0).mul_const (-Complex.I * causal)
  change
    HasDerivAt
      (fun t : ℂ => Complex.exp (t * (-Complex.I * causal)))
      (-Complex.I * causal) 0
  simpa using hlinear.cexp

/-- **Branch-free causal recovery from the phase germ.** -/
theorem causalPairing_eq_I_mul_deriv_orderPhase_zero (causal : ℂ) :
    causal =
      Complex.I * deriv (causalOrderPhase causal) 0 := by
  rw [(hasDerivAt_causalOrderPhase_zero causal).deriv]
  rw [show Complex.I * (-Complex.I * causal) =
      -(Complex.I ^ (2 : ℕ) * causal) by ring, Complex.I_sq]
  ring

/-! ## Nine null-order probes and one tick determine a four-metric -/

/-- Squared interval of a four-vector in a candidate metric matrix. -/
def clockSquaredInterval4
    (g : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) : ℝ :=
  dotProduct v (g *ᵥ v)

/-- Timelike unit reference channel. -/
def clockTime4 : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- Six axis light-clock channels. -/
def clockXPlus4 : Fin 4 → ℝ := ![1, 1, 0, 0]
def clockXMinus4 : Fin 4 → ℝ := ![1, -1, 0, 0]
def clockYPlus4 : Fin 4 → ℝ := ![1, 0, 1, 0]
def clockYMinus4 : Fin 4 → ℝ := ![1, 0, -1, 0]
def clockZPlus4 : Fin 4 → ℝ := ![1, 0, 0, 1]
def clockZMinus4 : Fin 4 → ℝ := ![1, 0, 0, -1]

/-- Three Pythagorean mixed light-clock channels. The integer coefficients avoid square roots:
`5² = 3² + 4²`. -/
def clockXYNull4 : Fin 4 → ℝ := ![5, 3, 4, 0]
def clockXZNull4 : Fin 4 → ℝ := ![5, 3, 0, 4]
def clockYZNull4 : Fin 4 → ℝ := ![5, 0, 3, 4]

/-- Standard four-dimensional Minkowski metric in the selected clock frame. -/
def minkowskiMetric4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 0, 0;
      0, 1, 0, 0;
      0, 0, 1, 0;
      0, 0, 0, 1]

/-- **Nine before/after boundary probes plus one clock tick determine a four-metric.**

Any symmetric real `4 × 4` candidate for which the nine declared directions are null and the
reference timelike direction has squared interval `-1` is exactly the Minkowski metric in that
frame. No signature or nondegeneracy assumption is needed: the ten clock constraints force both.
-/
theorem nineNullClockComparisons_oneTick_metricRigidity
    (g : Matrix (Fin 4) (Fin 4) ℝ) (hsymm : g.IsSymm)
    (htick : clockSquaredInterval4 g clockTime4 = -1)
    (hxplus : clockSquaredInterval4 g clockXPlus4 = 0)
    (hxminus : clockSquaredInterval4 g clockXMinus4 = 0)
    (hyplus : clockSquaredInterval4 g clockYPlus4 = 0)
    (hyminus : clockSquaredInterval4 g clockYMinus4 = 0)
    (hzplus : clockSquaredInterval4 g clockZPlus4 = 0)
    (hzminus : clockSquaredInterval4 g clockZMinus4 = 0)
    (hxy : clockSquaredInterval4 g clockXYNull4 = 0)
    (hxz : clockSquaredInterval4 g clockXZNull4 = 0)
    (hyz : clockSquaredInterval4 g clockYZNull4 = 0) :
    g = minkowskiMetric4 := by
  have h01 := congrFun (congrFun hsymm.eq (0 : Fin 4)) (1 : Fin 4)
  have h02 := congrFun (congrFun hsymm.eq (0 : Fin 4)) (2 : Fin 4)
  have h03 := congrFun (congrFun hsymm.eq (0 : Fin 4)) (3 : Fin 4)
  have h12 := congrFun (congrFun hsymm.eq (1 : Fin 4)) (2 : Fin 4)
  have h13 := congrFun (congrFun hsymm.eq (1 : Fin 4)) (3 : Fin 4)
  have h23 := congrFun (congrFun hsymm.eq (2 : Fin 4)) (3 : Fin 4)
  simp only [Matrix.transpose_apply] at h01 h02 h03 h12 h13 h23
  simp [clockSquaredInterval4, dotProduct, Matrix.mulVec,
    Fin.sum_univ_succ, clockTime4, clockXPlus4, clockXMinus4,
    clockYPlus4, clockYMinus4, clockZPlus4, clockZMinus4,
    clockXYNull4, clockXZNull4, clockYZNull4]
    at htick hxplus hxminus hyplus hyminus hzplus hzminus hxy hxz hyz
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [minkowskiMetric4] <;>
    linarith

/-! ## Two-species conformal-scale separation -/

/-- Algebraic form of a conformally conjugated clock-species potential: `massSq * scale` minus a
geometric defect shared by every minimally coupled scalar species. The differential-geometric
derivation of this form is deliberately not encoded here. -/
def twoSpeciesConformalPotential
    (massSq scale sharedGeometricDefect : ℝ) : ℝ :=
  massSq * scale - sharedGeometricDefect

/-- The difference of two clock-species potentials cancels the shared geometric defect exactly. -/
theorem twoSpeciesConformalPotential_difference
    (massSq₁ massSq₂ scale sharedGeometricDefect : ℝ) :
    twoSpeciesConformalPotential massSq₁ scale sharedGeometricDefect -
        twoSpeciesConformalPotential massSq₂ scale sharedGeometricDefect =
      (massSq₁ - massSq₂) * scale := by
  simp only [twoSpeciesConformalPotential]
  ring

/-- Distinct calibrated squared masses reconstruct the conformal scale from the two effective
potentials. -/
theorem twoSpeciesConformalScale_reconstruction
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    (scale sharedGeometricDefect : ℝ) :
    (twoSpeciesConformalPotential massSq₁ scale sharedGeometricDefect -
        twoSpeciesConformalPotential massSq₂ scale sharedGeometricDefect) /
        (massSq₁ - massSq₂) =
      scale := by
  rw [twoSpeciesConformalPotential_difference]
  exact mul_div_cancel_left₀ scale (sub_ne_zero.mpr hmass)

/-- Two distinct clock species jointly identify both conformal scale and the shared geometric
defect. -/
theorem twoSpeciesConformalPotentialPair_injective
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂) :
    Function.Injective
      (fun data : ℝ × ℝ =>
        (twoSpeciesConformalPotential massSq₁ data.1 data.2,
          twoSpeciesConformalPotential massSq₂ data.1 data.2)) := by
  rintro ⟨scale₁, defect₁⟩ ⟨scale₂, defect₂⟩ hdata
  have hfirst := congrArg Prod.fst hdata
  have hsecond := congrArg Prod.snd hdata
  dsimp at hfirst hsecond
  have hscale : scale₁ = scale₂ := by
    have hmassSub : massSq₁ - massSq₂ ≠ 0 := sub_ne_zero.mpr hmass
    apply mul_left_cancel₀ hmassSub
    calc
      (massSq₁ - massSq₂) * scale₁ =
          twoSpeciesConformalPotential massSq₁ scale₁ defect₁ -
            twoSpeciesConformalPotential massSq₂ scale₁ defect₁ := by
              rw [twoSpeciesConformalPotential_difference]
      _ = twoSpeciesConformalPotential massSq₁ scale₂ defect₂ -
            twoSpeciesConformalPotential massSq₂ scale₂ defect₂ := by
              rw [hfirst, hsecond]
      _ = (massSq₁ - massSq₂) * scale₂ :=
        twoSpeciesConformalPotential_difference _ _ _ _
  apply Prod.ext
  · exact hscale
  · dsimp
    have hdefect :
        massSq₁ * scale₁ - defect₁ =
          massSq₁ * scale₂ - defect₂ := hfirst
    rw [hscale] at hdefect
    linarith

end GaloisForLFunctions.HTGeometry
