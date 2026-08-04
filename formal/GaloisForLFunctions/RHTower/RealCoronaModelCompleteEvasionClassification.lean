import GaloisForLFunctions.RHTower.RealCoronaLocalDetectabilityFracture

/-!
# Model-complete Real-corona evasion classification

This module classifies, by exact equivalences, both ways in which changing a model can make a
Real-corona projector locally admissible.  On an invariant operator domain, admissibility is
equivalent to boundedness of the orientation-odd part of the operator.  In an arbitrary unital
complex function subalgebra, admissibility is equivalent to independent patching of the two
sectors.  Thus model changes do not invalidate the obstruction: they pay one of two precisely
classified prices.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

section OperatorClassification

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The commutator with the projector `(1 + m) / 2` is half the commutator with its orientation
`m`, on the exact invariant domain of the partially defined operator. -/
theorem linearPMapExchangeCommutator_eq_half_orientationCommutator
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) (x : D.domain) :
    linearPMapExchangeCommutator D m hdomm x =
      (2 : ℂ)⁻¹ • linearPMapOrientationCommutator D m hdomm x := by
  let mx : D.domain := ⟨m x, hdomm x⟩
  let ex : D.domain :=
    ⟨cliffordExchangeProjector m x,
      linearPMapExchangeProjector_mem D m hdomm x⟩
  have hex : ex = (2 : ℂ)⁻¹ • (mx + x) := by
    apply Subtype.ext
    simp [ex, mx, cliffordExchangeProjector]
  rw [linearPMapExchangeCommutator_apply,
    linearPMapOrientationCommutator_apply,
    show (⟨cliffordExchangeProjector m x,
      linearPMapExchangeProjector_mem D m hdomm x⟩ : D.domain) = ex from rfl,
    hex, D.map_smul, D.map_add]
  change (2 : ℂ)⁻¹ • (D mx + D x) -
      (2 : ℂ)⁻¹ • (m (D x) + D x) =
        (2 : ℂ)⁻¹ • (D mx - m (D x))
  module

/-- Exact model-complete norm law: the projector commutator sees precisely the odd parity
component, with no loss in the norm constant. -/
theorem norm_linearPMapExchangeCommutator_eq_orientationOdd
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hm : m * m = 1) (hiso : ∀ y : V, ‖m y‖ = ‖y‖) (x : D.domain) :
    ‖linearPMapExchangeCommutator D m hdomm x‖ =
      ‖linearPMapOrientationOdd D m hdomm x‖ := by
  rw [linearPMapExchangeCommutator_eq_half_orientationCommutator D m hdomm x,
    norm_smul, norm_inv, Complex.norm_ofNat,
    norm_linearPMapOrientationCommutator_eq_two_odd D m hdomm hm hiso x]
  nlinarith [norm_nonneg (linearPMapOrientationOdd D m hdomm x)]

/-- Across every invariant-domain operator model, the Real-corona projector is Lipschitz exactly
when the orientation-odd component of the operator is bounded. -/
theorem hasLinearPMapBoundOnDomain_exchangeCommutator_iff_orientationOdd
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hm : m * m = 1) (hiso : ∀ y : V, ‖m y‖ = ‖y‖) :
    HasLinearPMapBoundOnDomain (linearPMapExchangeCommutator D m hdomm) ↔
      HasLinearPMapBoundOnDomain (linearPMapOrientationOdd D m hdomm) := by
  constructor <;> rintro ⟨C, hC, hbound⟩
  · exact ⟨C, hC, fun x => by
      rw [← norm_linearPMapExchangeCommutator_eq_orientationOdd D m hdomm hm hiso x]
      exact hbound x⟩
  · exact ⟨C, hC, fun x => by
      rw [norm_linearPMapExchangeCommutator_eq_orientationOdd D m hdomm hm hiso x]
      exact hbound x⟩

/-- For a genuinely unbounded operator, every model in which the Real-corona projector is
Lipschitz has exactly one escape mechanism: the odd channel is bounded and all unboundedness is
carried by the commuting even channel. -/
theorem bounded_exchangeCommutator_iff_unbounded_even_and_bounded_odd
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hm : m * m = 1) (hiso : ∀ y : V, ‖m y‖ = ‖y‖)
    (hD : IsGenuinelyUnboundedLinearPMap D) :
    HasLinearPMapBoundOnDomain (linearPMapExchangeCommutator D m hdomm) ↔
      IsGenuinelyUnboundedLinearPMap (linearPMapOrientationEven D m hdomm) ∧
        HasLinearPMapBoundOnDomain (linearPMapOrientationOdd D m hdomm) := by
  rw [hasLinearPMapBoundOnDomain_exchangeCommutator_iff_orientationOdd
    D m hdomm hm hiso]
  constructor
  · intro hodd
    exact ⟨genuinelyUnbounded_even_of_bounded_orientationCommutator
        D m hdomm hm hiso hD
        ((hasLinearPMapBoundOnDomain_orientationCommutator_iff_odd
          D m hdomm hm hiso).mpr hodd), hodd⟩
  · exact And.right

end OperatorClassification

section CoefficientAlgebraClassification

variable {X : Type*}

/-- Characteristic idempotent of a Real sector in the algebra of all complex-valued functions. -/
def realCoronaSectorIdempotent (S : Set X) : X → ℂ :=
  S.indicator fun _ => 1

/-- A function algebra can choose its values independently on the two sides of a Real sector. -/
def HasIndependentRealCoronaSectorPatching
    (A : Subalgebra ℂ (X → ℂ)) (S : Set X) : Prop :=
  ∀ f g : A, ∃ h : A,
    (∀ x ∈ S, (h : X → ℂ) x = (f : X → ℂ) x) ∧
      (∀ x ∉ S, (h : X → ℂ) x = (g : X → ℂ) x)

/-- Across every unital complex function subalgebra, the Real-sector projector belongs to the
algebra exactly when arbitrary algebra elements can be patched independently across the sector. -/
theorem realCoronaSectorIdempotent_mem_iff_independentSectorPatching
    (A : Subalgebra ℂ (X → ℂ)) (S : Set X) :
    realCoronaSectorIdempotent S ∈ A ↔
      HasIndependentRealCoronaSectorPatching A S := by
  classical
  constructor
  · intro he f g
    let e : A := ⟨realCoronaSectorIdempotent S, he⟩
    let h : A := e * f + (1 - e) * g
    refine ⟨h, ?_, ?_⟩
    · intro x hx
      simp [h, e, realCoronaSectorIdempotent, Set.indicator_of_mem hx]
    · intro x hx
      simp [h, e, realCoronaSectorIdempotent, Set.indicator_of_notMem hx]
  · intro hpatch
    obtain ⟨h, hS, hSc⟩ := hpatch 1 0
    have hh : (h : X → ℂ) = realCoronaSectorIdempotent S := by
      funext x
      by_cases hx : x ∈ S
      · simpa [realCoronaSectorIdempotent, Set.indicator_of_mem hx] using hS x hx
      · simpa [realCoronaSectorIdempotent, Set.indicator_of_notMem hx] using hSc x hx
    rw [← hh]
    exact h.property

/-- The universal sector function is an idempotent independently of the chosen function algebra. -/
theorem realCoronaSectorIdempotent_isIdempotent (S : Set X) :
    IsIdempotentElem (realCoronaSectorIdempotent S) := by
  classical
  ext x
  by_cases hx : x ∈ S <;>
    simp [realCoronaSectorIdempotent, Set.indicator_of_mem, Set.indicator_of_notMem, hx]

end CoefficientAlgebraClassification

end GaloisForLFunctions.RHTower
