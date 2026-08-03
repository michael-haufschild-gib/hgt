import GaloisForLFunctions.RHTower.RealCoronaUniversalTransgression

noncomputable section

namespace GaloisForLFunctions.RHTower

section LocalDetectabilityFracture

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Conjugation of a partially defined operator by a bounded domain-preserving orientation. -/
def linearPMapOrientationConjugate
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) : V →ₗ.[ℂ] V where
  domain := D.domain
  toFun := m.comp (D.toFun.comp (linearPMapOrientationDomainMap D m hdomm))

@[simp] theorem linearPMapOrientationConjugate_apply
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) (x : D.domain) :
    linearPMapOrientationConjugate D m hdomm x = m (D ⟨m x, hdomm x⟩) := by
  rfl

/-- Part of `D` even under orientation conjugation. -/
def linearPMapOrientationEven
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) : V →ₗ.[ℂ] V where
  domain := D.domain
  toFun := (2 : ℂ)⁻¹ •
    (D.toFun +
      m.comp (D.toFun.comp (linearPMapOrientationDomainMap D m hdomm)))

/-- Part of `D` odd under orientation conjugation. -/
def linearPMapOrientationOdd
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) : V →ₗ.[ℂ] V where
  domain := D.domain
  toFun := (2 : ℂ)⁻¹ •
    (D.toFun -
      m.comp (D.toFun.comp (linearPMapOrientationDomainMap D m hdomm)))

@[simp] theorem linearPMapOrientationEven_apply
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) (x : D.domain) :
    linearPMapOrientationEven D m hdomm x =
      (2 : ℂ)⁻¹ • (D x + m (D ⟨m x, hdomm x⟩)) := by
  rfl

@[simp] theorem linearPMapOrientationOdd_apply
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) (x : D.domain) :
    linearPMapOrientationOdd D m hdomm x =
      (2 : ℂ)⁻¹ • (D x - m (D ⟨m x, hdomm x⟩)) := by
  rfl

theorem linearPMapOrientation_even_add_odd
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) (x : D.domain) :
    linearPMapOrientationEven D m hdomm x +
        linearPMapOrientationOdd D m hdomm x = D x := by
  rw [linearPMapOrientationEven_apply, linearPMapOrientationOdd_apply]
  module

theorem linearPMapOrientationEven_commutes
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hm : m * m = 1) (x : D.domain) :
    linearPMapOrientationEven D m hdomm ⟨m x, hdomm x⟩ =
      m (linearPMapOrientationEven D m hdomm x) := by
  have hmm (y : V) : m (m y) = y := by
    exact LinearMap.congr_fun hm y
  have hsub :
      (⟨m (m x), hdomm ⟨m x, hdomm x⟩⟩ : D.domain) = x := by
    apply Subtype.ext
    exact hmm x
  rw [linearPMapOrientationEven_apply, linearPMapOrientationEven_apply, hsub,
    map_smul, map_add, hmm]
  exact congrArg (fun y : V => (2 : ℂ)⁻¹ • y)
    (add_comm (D ⟨m x, hdomm x⟩) (m (D x)))

theorem linearPMapOrientationOdd_anticommutes
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hm : m * m = 1) (x : D.domain) :
    linearPMapOrientationOdd D m hdomm ⟨m x, hdomm x⟩ =
      -m (linearPMapOrientationOdd D m hdomm x) := by
  have hmm (y : V) : m (m y) = y := by
    exact LinearMap.congr_fun hm y
  have hsub :
      (⟨m (m x), hdomm ⟨m x, hdomm x⟩⟩ : D.domain) = x := by
    apply Subtype.ext
    exact hmm x
  rw [linearPMapOrientationOdd_apply, linearPMapOrientationOdd_apply, hsub,
    map_smul, map_sub, hmm]
  rw [← smul_neg, neg_sub]
  rfl

/-- Exact local-detectability identity: the commutator is twice the odd component, transported by
the orientation. -/
theorem linearPMapOrientationCommutator_eq_two_odd
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hm : m * m = 1) (x : D.domain) :
    linearPMapOrientationCommutator D m hdomm x =
      (2 : ℂ) • linearPMapOrientationOdd D m hdomm ⟨m x, hdomm x⟩ := by
  have hmm (y : V) : m (m y) = y := LinearMap.congr_fun hm y
  have hsub :
      (⟨m (m x), hdomm ⟨m x, hdomm x⟩⟩ : D.domain) = x := by
    apply Subtype.ext
    exact hmm x
  rw [linearPMapOrientationCommutator_apply, linearPMapOrientationOdd_apply, hsub]
  rw [smul_smul]
  norm_num
  rfl

theorem norm_linearPMapOrientationCommutator_eq_two_odd
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hm : m * m = 1) (hiso : ∀ y : V, ‖m y‖ = ‖y‖) (x : D.domain) :
    ‖linearPMapOrientationCommutator D m hdomm x‖ =
      2 * ‖linearPMapOrientationOdd D m hdomm x‖ := by
  rw [linearPMapOrientationCommutator_eq_two_odd D m hdomm hm x,
    norm_smul, Complex.norm_ofNat,
    linearPMapOrientationOdd_anticommutes D m hdomm hm x,
    norm_neg, hiso]

/-- Bounded first commutator is equivalent to boundedness of the orientation-odd component. -/
theorem hasLinearPMapBoundOnDomain_orientationCommutator_iff_odd
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hm : m * m = 1) (hiso : ∀ y : V, ‖m y‖ = ‖y‖) :
    HasLinearPMapBoundOnDomain (linearPMapOrientationCommutator D m hdomm) ↔
      HasLinearPMapBoundOnDomain (linearPMapOrientationOdd D m hdomm) := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, fun x => ?_⟩
    have h := hbound x
    rw [norm_linearPMapOrientationCommutator_eq_two_odd D m hdomm hm hiso x] at h
    nlinarith [norm_nonneg (linearPMapOrientationOdd D m hdomm x),
      norm_nonneg (x : V)]
  · rintro ⟨C, hC, hbound⟩
    refine ⟨2 * C, mul_nonneg (by norm_num) hC, fun x => ?_⟩
    rw [norm_linearPMapOrientationCommutator_eq_two_odd D m hdomm hm hiso x]
    nlinarith [hbound x, norm_nonneg (x : V)]

/-- If an unbounded operator has bounded commutator with its orientation, all unboundedness lies in
the commuting even component; the detecting odd component is only bounded. -/
theorem genuinelyUnbounded_even_of_bounded_orientationCommutator
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hm : m * m = 1) (hiso : ∀ y : V, ‖m y‖ = ‖y‖)
    (hD : IsGenuinelyUnboundedLinearPMap D)
    (hcomm : HasLinearPMapBoundOnDomain
      (linearPMapOrientationCommutator D m hdomm)) :
    IsGenuinelyUnboundedLinearPMap (linearPMapOrientationEven D m hdomm) := by
  have hodd :=
    (hasLinearPMapBoundOnDomain_orientationCommutator_iff_odd D m hdomm hm hiso).mp hcomm
  rintro ⟨Ce, hCe, heven⟩
  rcases hodd with ⟨Co, hCo, hodd⟩
  apply hD
  refine ⟨Ce + Co, add_nonneg hCe hCo, fun x => ?_⟩
  rw [← linearPMapOrientation_even_add_odd D m hdomm x]
  calc
    ‖linearPMapOrientationEven D m hdomm x +
        linearPMapOrientationOdd D m hdomm x‖
        ≤ ‖linearPMapOrientationEven D m hdomm x‖ +
          ‖linearPMapOrientationOdd D m hdomm x‖ := norm_add_le _ _
    _ ≤ Ce * ‖(x : V)‖ + Co * ‖(x : V)‖ := add_le_add (heven x) (hodd x)
    _ = (Ce + Co) * ‖(x : V)‖ := by ring

/-- Universal local-detectability fracture: Lipschitz regularity and an unbounded detecting odd
component are mutually exclusive. -/
theorem not_boundedCommutator_and_genuinelyUnbounded_odd
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hm : m * m = 1) (hiso : ∀ y : V, ‖m y‖ = ‖y‖) :
    ¬(HasLinearPMapBoundOnDomain (linearPMapOrientationCommutator D m hdomm) ∧
      IsGenuinelyUnboundedLinearPMap (linearPMapOrientationOdd D m hdomm)) := by
  rintro ⟨hcomm, hodd⟩
  exact hodd
    ((hasLinearPMapBoundOnDomain_orientationCommutator_iff_odd D m hdomm hm hiso).mp hcomm)

end LocalDetectabilityFracture

end GaloisForLFunctions.RHTower

