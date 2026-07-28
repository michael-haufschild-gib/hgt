import GaloisForLFunctions.HTGeometry.ClockCompassNoncommutativeTomography

/-!
# Exact causal-response fracture and clock-intervention reconstruction

For two Green-hyperbolic operator presentations `P₀,E₀` and `P₁,E₁`, the exact second
resolvent identity is

`E₁ - E₀ = E₀ * (P₀ - P₁) * E₁`.

With two-sided inverse laws, the change of operator is recovered exactly from the change of
propagator:

`P₀ * (E₁ - E₀) * P₁ = P₀ - P₁`.

The second part lifts complete clock-compass tomography from one background to arbitrary finite
source packets.  In particular, every finite difference or finite source-jet stencil of the
curvature reporters is reconstructed from the identical stencil of clock reporters.

These are unconditional algebraic statements.  A physical application must separately construct
retarded/advanced Green operators in the relevant support class, derive the clock reporter matrix,
and prove that the allowed stress interventions supply the required source family.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R A Curv Clock Source : Type*}

/-- **Exact causal fracture identity.**  The difference of two Green elements factorizes once
through the difference of their operators.  Only the inverse sides used by the factorization are
required. -/
theorem greenElement_fracture
    [Ring A] (P₀ P₁ E₀ E₁ : A)
    (hE₀P₀ : E₀ * P₀ = 1) (hP₁E₁ : P₁ * E₁ = 1) :
    E₁ - E₀ = E₀ * (P₀ - P₁) * E₁ := by
  calc
    E₁ - E₀ = (E₀ * P₀) * E₁ - E₀ * (P₁ * E₁) := by
      rw [hE₀P₀, hP₁E₁, one_mul, mul_one]
    _ = E₀ * (P₀ - P₁) * E₁ := by noncomm_ring

/-- **Exact operator recovery from causal fracture.**  With the opposite inverse sides, the
operator change is reconstructed from the Green-element change. -/
theorem operatorChange_reconstruction_from_greenElement_fracture
    [Ring A] (P₀ P₁ E₀ E₁ : A)
    (hP₀E₀ : P₀ * E₀ = 1) (hE₁P₁ : E₁ * P₁ = 1) :
    P₀ * (E₁ - E₀) * P₁ = P₀ - P₁ := by
  calc
    P₀ * (E₁ - E₀) * P₁ =
        P₀ * (E₁ * P₁) - (P₀ * E₀) * P₁ := by noncomm_ring
    _ = P₀ - P₁ := by rw [hP₀E₀, hE₁P₁, mul_one, one_mul]

/-- The fracture and recovery identities together give an exact equivalence between operator
change and Green-element change whenever both presentations are two-sided inverses. -/
theorem greenElement_fracture_and_operatorChange_reconstruction
    [Ring A] (P₀ P₁ E₀ E₁ : A)
    (hE₀P₀ : E₀ * P₀ = 1) (hP₀E₀ : P₀ * E₀ = 1)
    (hE₁P₁ : E₁ * P₁ = 1) (hP₁E₁ : P₁ * E₁ = 1) :
    E₁ - E₀ = E₀ * (P₀ - P₁) * E₁ ∧
      P₀ * (E₁ - E₀) * P₁ = P₀ - P₁ :=
  ⟨greenElement_fracture P₀ P₁ E₀ E₁ hE₀P₀ hP₁E₁,
    operatorChange_reconstruction_from_greenElement_fracture
      P₀ P₁ E₀ E₁ hP₀E₀ hE₁P₁⟩

/-- Clock response between two controlled source settings. -/
def clockReporterDifference
    [CommRing R] [Ring A] [Algebra R A] [Fintype Curv]
    (C : Clock → Curv → R) (curvature : Source → Curv → A)
    (source₀ source₁ : Source) (i : Clock) : A :=
  clockReporter C (curvature source₁) i -
    clockReporter C (curvature source₀) i

/-- **Clock causal-susceptibility reconstruction.**  A complete reporter left inverse reconstructs
the exact curvature response between any two source settings. -/
theorem curvatureDifference_reconstruction
    [CommRing R] [Ring A] [Algebra R A]
    [Fintype Curv] [DecidableEq Curv] [Fintype Clock]
    (C : Clock → Curv → R) (D : Curv → Clock → R)
    (curvature : Source → Curv → A)
    (hDC : ∀ a b, ∑ i, D a i * C i b = if a = b then 1 else 0)
    (source₀ source₁ : Source) (a : Curv) :
    ∑ i, D a i •
        clockReporterDifference C curvature source₀ source₁ i =
      curvature source₁ a - curvature source₀ a := by
  simp only [clockReporterDifference, smul_sub, Finset.sum_sub_distrib]
  rw [curvature_reconstruction C D (curvature source₁) hDC a,
    curvature_reconstruction C D (curvature source₀) hDC a]

/-- Finite source packet, encompassing finite differences and arbitrary finite source-jet
stencils. -/
def curvatureSourcePacket
    [CommSemiring R] [Semiring A] [Algebra R A] [Fintype Source]
    (weight : Source → R) (curvature : Source → Curv → A) (a : Curv) : A :=
  ∑ source, weight source • curvature source a

/-- Apply the same finite source packet to every clock reporter. -/
def clockReporterSourcePacket
    [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype Curv] [Fintype Source]
    (C : Clock → Curv → R) (weight : Source → R)
    (curvature : Source → Curv → A) (i : Clock) : A :=
  ∑ source, weight source • clockReporter C (curvature source) i

/-- Reporter formation commutes exactly with every finite source packet. -/
theorem clockReporter_curvatureSourcePacket
    [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype Curv] [Fintype Source]
    (C : Clock → Curv → R) (weight : Source → R)
    (curvature : Source → Curv → A) (i : Clock) :
    clockReporter C (curvatureSourcePacket weight curvature) i =
      clockReporterSourcePacket C weight curvature i := by
  classical
  simp only [clockReporter, curvatureSourcePacket, clockReporterSourcePacket,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm]

/-- **All finite intervention stencils are observable.**  Complete clock reporters reconstruct
every finite source packet of every curvature generator. -/
theorem curvatureSourcePacket_reconstruction
    [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype Curv] [DecidableEq Curv] [Fintype Clock] [Fintype Source]
    (C : Clock → Curv → R) (D : Curv → Clock → R)
    (weight : Source → R) (curvature : Source → Curv → A)
    (hDC : ∀ a b, ∑ i, D a i * C i b = if a = b then 1 else 0)
    (a : Curv) :
    ∑ i, D a i • clockReporterSourcePacket C weight curvature i =
      curvatureSourcePacket weight curvature a := by
  simp_rw [← clockReporter_curvatureSourcePacket C weight curvature]
  exact curvature_reconstruction C D
    (curvatureSourcePacket weight curvature) hDC a

/-- Equality of complete clock intervention data at every source forces equality of the complete
ordered curvature-word data at every source. -/
theorem states_agree_on_curvature_intervention_words
    [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype Curv] [DecidableEq Curv] [Fintype Clock]
    {S : Type*}
    (C : Clock → Curv → R) (D : Curv → Clock → R)
    (curvature : Source → Curv → A)
    (hDC : ∀ a b, ∑ i, D a i * C i b = if a = b then 1 else 0)
    (state₁ state₂ : A → S)
    (hstate : ∀ source : Source, ∀ q : FreeAlgebra R Clock,
      state₁ (clockWordEval C (curvature source) q) =
        state₂ (clockWordEval C (curvature source) q)) :
    ∀ source : Source, ∀ p : FreeAlgebra R Curv,
      state₁ (curvatureWordEval (curvature source) p) =
        state₂ (curvatureWordEval (curvature source) p) := by
  intro source
  exact states_agree_on_curvature_words_of_agree_on_clock_words
    C D (curvature source) hDC state₁ state₂ (hstate source)

/-! ## Clock coframes and the conservation budget -/

/-- Adaptive clock coefficients that cancel a prescribed conservation defect. -/
def conservationBalancedClockSource
    [Ring R] [AddCommGroup Curv] [Module R Curv]
    [AddCommGroup Clock] [Module R Clock]
    (clockCoframe : Clock ≃ₗ[R] Curv) (defect : Curv) : Clock :=
  clockCoframe.symm (-defect)

/-- **Clock-coframe conservation law.** A complete clock coframe cancels every covector-valued
conservation defect exactly. -/
theorem clockCoframe_conservation
    [Ring R] [AddCommGroup Curv] [Module R Curv]
    [AddCommGroup Clock] [Module R Clock]
    (clockCoframe : Clock ≃ₗ[R] Curv) (defect : Curv) :
    defect + clockCoframe
      (conservationBalancedClockSource clockCoframe defect) = 0 := by
  simp [conservationBalancedClockSource]

/-- Adaptive conservation source together with an independently prescribed signal channel. -/
def conservationBalancedClockSourceWithSignal
    [Ring R] [AddCommGroup Curv] [Module R Curv]
    [AddCommGroup Clock] [Module R Clock]
    (clockCoframe : Clock ≃ₗ[R] Curv)
    {Signal : Type*} (defect : Curv) (signal : Signal) : Clock × Signal :=
  (conservationBalancedClockSource clockCoframe defect, signal)

/-- Adding a separate signal channel does not change exact conservation cancellation. -/
theorem clockCoframe_conservation_withSignal
    [Ring R] [AddCommGroup Curv] [Module R Curv]
    [AddCommGroup Clock] [Module R Clock]
    (clockCoframe : Clock ≃ₗ[R] Curv)
    {Signal : Type*} (defect : Curv) (signal : Signal) :
    defect + clockCoframe
      (conservationBalancedClockSourceWithSignal
        clockCoframe defect signal).1 = 0 := by
  exact clockCoframe_conservation clockCoframe defect

/-- The independent signal survives the conservation-balancing construction unchanged. -/
theorem clockCoframe_signal_reconstruction
    [Ring R] [AddCommGroup Curv] [Module R Curv]
    [AddCommGroup Clock] [Module R Clock]
    (clockCoframe : Clock ≃ₗ[R] Curv)
    {Signal : Type*} (defect : Curv) (signal : Signal) :
    (conservationBalancedClockSourceWithSignal
      clockCoframe defect signal).2 = signal :=
  rfl

/-- Conservation balancing plus a free signal is jointly injective in defect and signal. -/
theorem conservationBalancedClockSourceWithSignal_injective
    [Ring R] [AddCommGroup Curv] [Module R Curv]
    [AddCommGroup Clock] [Module R Clock]
    (clockCoframe : Clock ≃ₗ[R] Curv)
    {Signal : Type*} :
    Function.Injective
      (fun data : Curv × Signal =>
        conservationBalancedClockSourceWithSignal
          clockCoframe data.1 data.2) := by
  intro data₁ data₂ hdata
  apply Prod.ext
  · have hfirst :=
      congrArg (fun value : Clock × Signal => value.1) hdata
    simp only [conservationBalancedClockSourceWithSignal,
      conservationBalancedClockSource] at hfirst
    exact neg_injective (clockCoframe.symm.injective hfirst)
  · exact congrArg (fun value : Clock × Signal => value.2) hdata

end

end GaloisForLFunctions.HTGeometry
