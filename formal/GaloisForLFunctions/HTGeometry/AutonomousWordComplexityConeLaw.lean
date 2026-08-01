import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Robust autonomous word-complexity cone

Repeated powering of an approximate endpoint loses resolution linearly in the
power.  Autonomous time addition has a stronger one-step consequence: a hard
late endpoint and one circuit for the intervening evolution force an earlier
endpoint to remain hard, with only one additive error loss.

The result is abstract in the gate alphabet and multiplication-compatible
metric.  It applies to operator-norm unitary circuit models and does not assume
randomness, locality, spectral independence, or finite dimension.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Value of a finite gate word, in list order. -/
def circuitWordValue {gate G : Type*} [Monoid G]
    (generator : gate → G) (w : List gate) : G :=
  (w.map generator).prod

/-- An endpoint has a gate-word approximation of length at most `s` and
metric error at most `ε`. -/
def HasCircuitWordApproximation
    {gate G : Type*} [Monoid G] [PseudoMetricSpace G]
    (generator : gate → G) (ε : ℝ) (s : ℕ) (x : G) : Prop :=
  ∃ w : List gate,
    w.length ≤ s ∧ dist (circuitWordValue generator w) x ≤ ε

/-- Every gate word of length at most `s` misses the endpoint by more than
`ε`.  This is the lower-bound form of robust circuit complexity. -/
def CircuitWordSeparated
    {gate G : Type*} [Monoid G] [PseudoMetricSpace G]
    (generator : gate → G) (ε : ℝ) (s : ℕ) (x : G) : Prop :=
  ∀ w : List gate,
    w.length ≤ s → ε < dist (circuitWordValue generator w) x

theorem circuitWordValue_append
    {gate G : Type*} [Monoid G]
    (generator : gate → G) (u v : List gate) :
    circuitWordValue generator (u ++ v) =
      circuitWordValue generator u * circuitWordValue generator v := by
  simp [circuitWordValue]

/-- Hardness of a product transfers to its left factor after paying the word
length and approximation error of the right factor. -/
theorem circuitWordSeparated_left_of_product
    {gate G : Type*} [Group G] [PseudoMetricSpace G]
    (generator : gate → G) {x y : G} {εx εy εxy : ℝ}
    {sx sy : ℕ}
    (hmul : ∀ a₁ a₂ b₁ b₂ : G,
      dist (a₁ * a₂) (b₁ * b₂) ≤ dist a₁ b₁ + dist a₂ b₂)
    (hproduct : CircuitWordSeparated generator εxy (sx + sy) (x * y))
    (hy : HasCircuitWordApproximation generator εy sy y)
    (herror : εx + εy ≤ εxy) :
    CircuitWordSeparated generator εx sx x := by
  intro wx hwlen
  by_contra hnot
  have hw : dist (circuitWordValue generator wx) x ≤ εx :=
    le_of_not_gt hnot
  obtain ⟨wy, hwylen, hwy⟩ := hy
  have hlen : (wx ++ wy).length ≤ sx + sy := by
    simp only [List.length_append]
    omega
  have hsep := hproduct (wx ++ wy) hlen
  rw [circuitWordValue_append] at hsep
  have hdist :
      dist (circuitWordValue generator wx * circuitWordValue generator wy)
          (x * y) ≤ εx + εy :=
    (hmul _ _ _ _).trans (add_le_add hw hwy)
  linarith

/-- **Robust autonomous backward complexity cone.** If the endpoint at `T`
is separated from every word of length `P`, while the increment of duration
`τ` has an `r`-gate approximation, then the endpoint at `T-τ` is separated
from every word of length `P-r`.  The earlier and increment errors need only
sum to the late separation scale; there is no `1/N` resolution collapse. -/
theorem circuitWordSeparated_autonomous_backward_cone
    {gate G : Type*} [Group G] [PseudoMetricSpace G]
    (generator : gate → G) (flow : ℝ → G)
    (hmul : ∀ a₁ a₂ b₁ b₂ : G,
      dist (a₁ * a₂) (b₁ * b₂) ≤ dist a₁ b₁ + dist a₂ b₂)
    {T τ εearly εincrement εlate : ℝ} {P r : ℕ}
    (hr : r ≤ P)
    (hflow : flow (T - τ) * flow τ = flow T)
    (hlate : CircuitWordSeparated generator εlate P (flow T))
    (hincrement :
      HasCircuitWordApproximation generator εincrement r (flow τ))
    (herror : εearly + εincrement ≤ εlate) :
    CircuitWordSeparated generator εearly (P - r) (flow (T - τ)) := by
  apply circuitWordSeparated_left_of_product generator
      (x := flow (T - τ)) (y := flow τ)
      (sx := P - r) (sy := r) hmul
  · simpa [Nat.sub_add_cancel hr, hflow] using hlate
  · exact hincrement
  · exact herror

/-- **Syndetic cone propagation.** If `P`-hard autonomous endpoints occur in
every interval of one fixed length `L`, then for every lag `τ` the
corresponding `(P-r)` backward-cone section also occurs in every interval of
the same length.  The cone operation does not enlarge recurrence gaps. -/
theorem circuitWordSeparated_syndetic_backward_cones
    {gate G : Type*} [Group G] [PseudoMetricSpace G]
    (generator : gate → G) (flow : ℝ → G)
    (hmul : ∀ a₁ a₂ b₁ b₂ : G,
      dist (a₁ * a₂) (b₁ * b₂) ≤ dist a₁ b₁ + dist a₂ b₂)
    {L τ εearly εincrement εlate : ℝ} {P r : ℕ}
    (hr : r ≤ P)
    (hflow : ∀ T : ℝ, flow (T - τ) * flow τ = flow T)
    (hlate : ∀ a : ℝ, ∃ T ∈ Set.Icc a (a + L),
      CircuitWordSeparated generator εlate P (flow T))
    (hincrement :
      HasCircuitWordApproximation generator εincrement r (flow τ))
    (herror : εearly + εincrement ≤ εlate) :
    ∀ a : ℝ, ∃ t ∈ Set.Icc a (a + L),
      CircuitWordSeparated generator εearly (P - r) (flow t) := by
  intro a
  obtain ⟨T, hT, hhard⟩ := hlate (a + τ)
  obtain ⟨hTlower, hTupper⟩ := hT
  refine ⟨T - τ, ⟨by linarith, by linarith⟩, ?_⟩
  exact circuitWordSeparated_autonomous_backward_cone
    generator flow hmul hr (hflow T) hhard hincrement herror

/-! ## Operator-norm unitary specialization -/

/-- Multiplication of unitary operators is jointly one-Lipschitz in each
operator-norm argument.  This discharges the abstract multiplication premise
in the circuit cone for arbitrary unital C⋆-algebras, with no dimension or
matrix-representation assumption. -/
theorem unitary_dist_mul_mul_le
    {A : Type*} [CStarAlgebra A]
    (a₁ a₂ b₁ b₂ : unitary A) :
    dist (a₁ * a₂) (b₁ * b₂) ≤ dist a₁ b₁ + dist a₂ b₂ := by
  simp only [Subtype.dist_eq, dist_eq_norm]
  change ‖(a₁ : A) * (a₂ : A) - (b₁ : A) * (b₂ : A)‖ ≤
    ‖(a₁ : A) - (b₁ : A)‖ + ‖(a₂ : A) - (b₂ : A)‖
  calc
    ‖(a₁ : A) * (a₂ : A) - (b₁ : A) * (b₂ : A)‖ =
        ‖((a₁ : A) - (b₁ : A)) * (a₂ : A) +
          (b₁ : A) * ((a₂ : A) - (b₂ : A))‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖((a₁ : A) - (b₁ : A)) * (a₂ : A)‖ +
        ‖(b₁ : A) * ((a₂ : A) - (b₂ : A))‖ := norm_add_le _ _
    _ = ‖(a₁ : A) - (b₁ : A)‖ + ‖(a₂ : A) - (b₂ : A)‖ := by
      rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

/-- **Operator-norm autonomous backward complexity cone.** A hard unitary
endpoint at time `T` forces a hard endpoint at every earlier time `T-τ` after
subtracting only the circuit cost of the intervening evolution and adding its
single approximation error.  The theorem holds in every unital C⋆-algebra;
the multiplication-Lipschitz premise is no longer exposed. -/
theorem unitaryCircuitWordSeparated_autonomous_backward_cone
    {gate A : Type*} [CStarAlgebra A]
    (generator : gate → unitary A) (flow : ℝ → unitary A)
    {T τ εearly εincrement εlate : ℝ} {P r : ℕ}
    (hr : r ≤ P)
    (hflow : flow (T - τ) * flow τ = flow T)
    (hlate : CircuitWordSeparated generator εlate P (flow T))
    (hincrement :
      HasCircuitWordApproximation generator εincrement r (flow τ))
    (herror : εearly + εincrement ≤ εlate) :
    CircuitWordSeparated generator εearly (P - r) (flow (T - τ)) := by
  exact circuitWordSeparated_autonomous_backward_cone
    generator flow unitary_dist_mul_mul_le hr hflow hlate hincrement herror

/-- Operator-norm specialization of syndetic cone propagation in arbitrary
unital C⋆-algebras. -/
theorem unitaryCircuitWordSeparated_syndetic_backward_cones
    {gate A : Type*} [CStarAlgebra A]
    (generator : gate → unitary A) (flow : ℝ → unitary A)
    {L τ εearly εincrement εlate : ℝ} {P r : ℕ}
    (hr : r ≤ P)
    (hflow : ∀ T : ℝ, flow (T - τ) * flow τ = flow T)
    (hlate : ∀ a : ℝ, ∃ T ∈ Set.Icc a (a + L),
      CircuitWordSeparated generator εlate P (flow T))
    (hincrement :
      HasCircuitWordApproximation generator εincrement r (flow τ))
    (herror : εearly + εincrement ≤ εlate) :
    ∀ a : ℝ, ∃ t ∈ Set.Icc a (a + L),
      CircuitWordSeparated generator εearly (P - r) (flow t) := by
  exact circuitWordSeparated_syndetic_backward_cones
    generator flow unitary_dist_mul_mul_le hr hflow hlate hincrement herror

end GaloisForLFunctions.HTGeometry
