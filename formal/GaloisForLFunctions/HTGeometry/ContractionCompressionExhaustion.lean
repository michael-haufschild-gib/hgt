import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

/-!
# Compression exhaustion for a bounded relative contraction

For a bounded operator `K` on an inner product space and an increasing family of subspaces whose
union is dense, the contraction inequality `K ≤ I` on the whole space, the compression inequalities
`P_d K P_d ≤ P_d`, and the dense-domain quadratic form inequality are all equivalent.

The equivalence needs boundedness: the forward direction is restriction, and the backward direction
is continuity of the quadratic defect together with density.

Any fixed finite depth is blind: a rank-one operator supported on a unit vector orthogonal to the
first `D` subspaces has vanishing compressions there while failing the contraction inequality.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The quadratic defect of a bounded operator is continuous. -/
theorem continuous_contractionDefect (K : H →L[ℂ] H) :
    Continuous fun y : H => ‖y‖ ^ 2 - (inner ℂ (K y) y : ℂ).re := by
  have hnorm : Continuous fun y : H => ‖y‖ ^ 2 := (continuous_norm (E := H)).pow 2
  have hpair : Continuous fun y : H => ((K y : H), (y : H)) :=
    K.continuous.prodMk continuous_id
  have hinner : Continuous fun y : H => (inner ℂ (K y) y : ℂ) :=
    continuous_inner.comp hpair
  exact hnorm.sub (Complex.continuous_re.comp hinner)

/-- **Dense exhaustion.**  A bounded operator whose quadratic form is a contraction on a dense set
is a contraction everywhere. -/
theorem re_inner_le_norm_sq_of_dense (K : H →L[ℂ] H) {S : Set H} (hS : Dense S)
    (h : ∀ v ∈ S, (inner ℂ (K v) v : ℂ).re ≤ ‖v‖ ^ 2) (x : H) :
    (inner ℂ (K x) x : ℂ).re ≤ ‖x‖ ^ 2 := by
  set T : Set H := {y : H | 0 ≤ ‖y‖ ^ 2 - (inner ℂ (K y) y : ℂ).re} with hT
  have hclosed : IsClosed T := isClosed_le continuous_const (continuous_contractionDefect K)
  have hsub : S ⊆ T := by
    intro v hv
    have := h v hv
    simp only [hT, Set.mem_setOf_eq]
    linarith
  have huniv : (Set.univ : Set H) ⊆ T := by
    rw [← hS.closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  have hx : x ∈ T := huniv (Set.mem_univ x)
  simp only [hT, Set.mem_setOf_eq] at hx
  linarith

/-- **Compression exhaustion.**  For an increasing family of subspaces with dense union, the global
contraction inequality, the family of subspace inequalities, and the dense-domain inequality all
agree. -/
theorem contraction_iff_forall_subspace (K : H →L[ℂ] H) (E : ℕ → Submodule ℂ H)
    (hdense : Dense (⋃ d, (E d : Set H))) :
    ((∀ h : H, (inner ℂ (K h) h : ℂ).re ≤ ‖h‖ ^ 2) ↔
        ∀ d : ℕ, ∀ v ∈ E d, (inner ℂ (K v) v : ℂ).re ≤ ‖v‖ ^ 2) ∧
      ((∀ d : ℕ, ∀ v ∈ E d, (inner ℂ (K v) v : ℂ).re ≤ ‖v‖ ^ 2) ↔
        ∀ v ∈ ⋃ d, (E d : Set H), (inner ℂ (K v) v : ℂ).re ≤ ‖v‖ ^ 2) := by
  have hsecond : (∀ d : ℕ, ∀ v ∈ E d, (inner ℂ (K v) v : ℂ).re ≤ ‖v‖ ^ 2) ↔
      ∀ v ∈ ⋃ d, (E d : Set H), (inner ℂ (K v) v : ℂ).re ≤ ‖v‖ ^ 2 := by
    constructor
    · rintro h v hv
      obtain ⟨d, hvs⟩ := Set.mem_iUnion.mp hv
      exact h d v hvs
    · intro h d v hv
      exact h v (Set.mem_iUnion.mpr ⟨d, hv⟩)
  refine ⟨?_, hsecond⟩
  constructor
  · intro h d v _
    exact h v
  · intro h
    exact re_inner_le_norm_sq_of_dense K hdense (hsecond.mp h)

/-- The rank-one operator attached to a vector. -/
def rankOneOp (u : H) : H →L[ℂ] H := (innerSL ℂ u).smulRight u

theorem rankOneOp_apply (u v : H) : rankOneOp u v = (inner ℂ u v : ℂ) • u := by
  simp [rankOneOp, innerSL_apply_apply]

theorem re_inner_rankOneOp (c : ℝ) (u v : H) :
    (inner ℂ (((c : ℂ) • rankOneOp u) v) v : ℂ).re = c * ‖(inner ℂ u v : ℂ)‖ ^ 2 := by
  have hval : ((c : ℂ) • rankOneOp u) v = ((c : ℂ) * (inner ℂ u v : ℂ)) • u := by
    rw [smul_apply, rankOneOp_apply, smul_smul]
  rw [hval, inner_smul_left, map_mul, Complex.conj_ofReal]
  have hnorm : (starRingEnd ℂ) (inner ℂ u v : ℂ) * (inner ℂ u v : ℂ) =
      ((Complex.normSq (inner ℂ u v : ℂ) : ℝ) : ℂ) := (Complex.normSq_eq_conj_mul_self).symm
  rw [mul_assoc, hnorm, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.sq_norm]

/-- **Finite-depth blindness.**  A rank-one operator on a unit vector orthogonal to a subspace has
vanishing compression on that subspace while failing the contraction inequality. -/
theorem rankOneOp_finiteDepth_blind {u : H} (hu : ‖u‖ = 1) {c : ℝ} (hc : 1 < c)
    (F : Submodule ℂ H) (hperp : ∀ v ∈ F, (inner ℂ u v : ℂ) = 0) :
    (∀ v ∈ F, (inner ℂ (((c : ℂ) • rankOneOp u) v) v : ℂ).re ≤ ‖v‖ ^ 2) ∧
      ¬ (∀ h : H, (inner ℂ (((c : ℂ) • rankOneOp u) h) h : ℂ).re ≤ ‖h‖ ^ 2) := by
  constructor
  · intro v hv
    rw [re_inner_rankOneOp, hperp v hv]
    simp
  · intro hcon
    have hval := hcon u
    rw [re_inner_rankOneOp] at hval
    have hself : (inner ℂ u u : ℂ) = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [hself, hu] at hval
    norm_num at hval
    linarith

end GaloisForLFunctions.HTGeometry
