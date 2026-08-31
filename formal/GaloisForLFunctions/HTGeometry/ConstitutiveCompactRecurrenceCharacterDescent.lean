import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Compactness.Compact

/-!
# Compact recurrence character descent

A faithful compact recurrence formation embeds an additive history group injectively and densely
in a compact topological abelian group.  Exact recovery of a real additive character through that
formation is possible exactly for the zero character: every continuous additive map from a compact
group to the real line vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A compact observer completion that retains every algebraic formation history and has dense
history range. -/
structure FaithfulCompactRecurrenceFormation
    (L : Type*) [AddCommGroup L] where
  History : Type*
  [historyTopology : TopologicalSpace History]
  [historyAddCommGroup : AddCommGroup History]
  [historyCompact : CompactSpace History]
  historyMap : L →+ History
  historyMap_injective : Function.Injective historyMap
  historyMap_dense : DenseRange historyMap

/-- Exact information-neutral descent of a real character through a compact recurrence formation. -/
def CompactCharacterDescends
    {L : Type*} [AddCommGroup L]
    (F : FaithfulCompactRecurrenceFormation L)
    (chi : L →+ ℝ) : Prop :=
  letI := F.historyTopology
  letI := F.historyAddCommGroup
  ∃ chiBar : F.History →ₜ+ ℝ, ∀ x, chiBar (F.historyMap x) = chi x

/-- A compact topological abelian group has no nonzero continuous real additive character. -/
theorem continuousAddMonoidHom_eq_zero_of_compact
    {K : Type*} [TopologicalSpace K] [AddCommGroup K] [CompactSpace K]
    (phi : K →ₜ+ ℝ) : phi = 0 := by
  ext x
  by_contra hx
  have hcompact : IsCompact (Set.range phi) := isCompact_range phi.continuous
  obtain ⟨bound : ℝ, hbound⟩ :=
    (isBounded_iff_forall_norm_le (E := ℝ) (s := Set.range phi)).mp hcompact.isBounded
  have hphi : 0 < ‖phi x‖ := norm_pos_iff.mpr hx
  obtain ⟨n : ℕ, hn : bound / ‖phi x‖ < n⟩ :=
    exists_nat_gt (bound / ‖phi x‖)
  have hgrow : bound < (n : ℝ) * ‖phi x‖ :=
    (div_lt_iff₀ hphi).mp hn
  have hle : ‖phi (n • x)‖ ≤ bound := hbound _ ⟨n • x, rfl⟩
  rw [map_nsmul] at hle
  exact (not_lt_of_ge hle) (by simpa [nsmul_eq_mul] using hgrow)

/-- Compact recurrence plus exact recovery selects precisely the neutral real character. -/
theorem compactCharacterDescends_iff
    {L : Type*} [AddCommGroup L]
    (F : FaithfulCompactRecurrenceFormation L)
    (chi : L →+ ℝ) :
    CompactCharacterDescends F chi ↔ chi = 0 := by
  letI := F.historyTopology
  letI := F.historyAddCommGroup
  letI := F.historyCompact
  constructor
  · rintro ⟨chiBar, hrecover⟩
    have hz : chiBar = 0 := continuousAddMonoidHom_eq_zero_of_compact chiBar
    ext x
    rw [← hrecover x, hz]
    rfl
  · rintro rfl
    exact ⟨0, fun _ => rfl⟩

end GaloisForLFunctions.HTGeometry
