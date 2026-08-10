import Mathlib

/-!
# Conservative repair, viability--coercivity transmutation, and open history

A semantically dependent repair leaves the represented range unchanged while creating a new
kernel-history direction.  The canonical two-resource cell crosses from strict scalar progress to
a unique full-support nonnegative circulation.  Repetition of that circulation has stationary
semantic endpoint and unbounded positive execution size.

Paper source:
`docs/drafts/pipeline/2-fully-proven/universal-law-field/
conservative-repair-viability-coercivity-transmutation-and-open-history-law.md`.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## General conservative repair -/

section GeneralRepair

variable {W V : Type*} [AddCommGroup W] [Module ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- Adjoin a rule with semantic boundary `-B c`. -/
def conservativeRepairBoundary (B : W →ₗ[ℝ] V) (c : W) : W × ℝ →ₗ[ℝ] V where
  toFun z := B (z.1 - z.2 • c)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    rw [show x.1 + y.1 - (x.2 • c + y.2 • c) =
      (x.1 - x.2 • c) + (y.1 - y.2 • c) by abel]
    exact B.map_add _ _
  map_smul' a x := by
    simp [smul_sub, smul_smul]

/-- A dependent repair is semantically conservative: old and repaired ranges coincide. -/
theorem conservativeRepairBoundary_range (B : W →ₗ[ℝ] V) (c : W) :
    LinearMap.range (conservativeRepairBoundary B c) = LinearMap.range B := by
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.1 - z.2 • c, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(w, 0), by simp [conservativeRepairBoundary]⟩

/-- Exact history law: the repaired execution is closed precisely when its old component differs
from the repair coordinate by an old closed history. -/
theorem conservativeRepairBoundary_eq_zero_iff (B : W →ₗ[ℝ] V) (c : W)
    (x : W) (t : ℝ) :
    conservativeRepairBoundary B c (x, t) = 0 ↔ x - t • c ∈ LinearMap.ker B := by
  simp [conservativeRepairBoundary, LinearMap.mem_ker]

/-- Split history form: every repaired closed history is uniquely presented by an old closed
history and the new repair coordinate. -/
theorem conservativeRepairBoundary_kernel_split_iff (B : W →ₗ[ℝ] V) (c : W)
    (x : W) (t : ℝ) :
    conservativeRepairBoundary B c (x, t) = 0 ↔
      ∃ k : W, k ∈ LinearMap.ker B ∧ x = k + t • c := by
  rw [conservativeRepairBoundary_eq_zero_iff]
  constructor
  · intro h
    exact ⟨x - t • c, h, by abel⟩
  · rintro ⟨k, hk, rfl⟩
    simpa only [add_sub_cancel_right] using hk

/-- Every dependent repair creates a distinguished zero-boundary history with nonzero repair
coordinate. -/
theorem conservativeRepairBoundary_birth (B : W →ₗ[ℝ] V) (c : W) :
    conservativeRepairBoundary B c (c, 1) = 0 := by
  simp [conservativeRepairBoundary]

end GeneralRepair

/-! ## Canonical two-resource transmutation cell -/

/-- Old execution multiplicities. -/
abbrev ViabilityOldFlux := ℝ × ℝ

/-- Old multiplicities plus the dependent repair multiplicity. -/
abbrev ViabilityRepairFlux := ViabilityOldFlux × ℝ

/-- Old semantic boundary: two independent resource directions. -/
def viabilityOldBoundary : ViabilityOldFlux →ₗ[ℝ] ViabilityOldFlux := LinearMap.id

/-- Repaired semantic boundary for rule vectors `(1,0)`, `(0,1)`, and `(-1,-1)`. -/
def viabilityRepairBoundary : ViabilityRepairFlux →ₗ[ℝ] ViabilityOldFlux where
  toFun h := (h.1.1 - h.2, h.1.2 - h.2)
  map_add' x y := by ext <;> simp <;> ring
  map_smul' a x := by ext <;> simp <;> ring

theorem viabilityOldBoundary_surjective : Function.Surjective viabilityOldBoundary := by
  intro z
  exact ⟨z, rfl⟩

/-- The repair does not change the represented semantic state space. -/
theorem viabilityRepairBoundary_surjective : Function.Surjective viabilityRepairBoundary := by
  intro z
  exact ⟨(z, 0), by ext <;> simp [viabilityRepairBoundary]⟩

/-- Coordinate form of the born kernel relation. -/
theorem viabilityRepairBoundary_eq_zero_iff (h : ViabilityRepairFlux) :
    viabilityRepairBoundary h = 0 ↔ h.1.1 = h.2 ∧ h.1.2 = h.2 := by
  constructor
  · intro hh
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    simp [viabilityRepairBoundary] at h1 h2
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  · rintro ⟨h1, h2⟩
    ext <;> simp [viabilityRepairBoundary, h1, h2]

/-- The whole repaired kernel is one lineage ray before imposing positivity. -/
theorem viabilityRepairBoundary_kernel_ray (h : ViabilityRepairFlux) :
    viabilityRepairBoundary h = 0 ↔ ∃ t : ℝ, h = ((t, t), t) := by
  rw [viabilityRepairBoundary_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h.2, ?_⟩
    rcases h with ⟨⟨x, y⟩, t⟩
    simp only at h1 h2 ⊢
    subst x
    subst y
    rfl
  · rintro ⟨t, rfl⟩
    simp

/-- Nonnegative execution multiplicities. -/
def ViabilityRepairFeasible (h : ViabilityRepairFlux) : Prop :=
  0 ≤ h.1.1 ∧ 0 ≤ h.1.2 ∧ 0 ≤ h.2

/-- Exact positive viability chamber: every feasible closed history is a nonnegative multiple of
the full-support carrier. -/
theorem viabilityRepair_feasible_kernel_ray (h : ViabilityRepairFlux) :
    ViabilityRepairFeasible h ∧ viabilityRepairBoundary h = 0 ↔
      ∃ t : ℝ, 0 ≤ t ∧ h = ((t, t), t) := by
  constructor
  · rintro ⟨hfeas, hker⟩
    obtain ⟨t, rfl⟩ := viabilityRepairBoundary_kernel_ray h |>.mp hker
    exact ⟨t, hfeas.2.2, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨ht, ht, ht⟩, viabilityRepairBoundary_kernel_ray _ |>.mpr ⟨t, rfl⟩⟩

/-- Unit-mass normalization selects one and only one feasible circulation. -/
theorem viabilityRepair_normalized_feasible_unique (h : ViabilityRepairFlux)
    (_hfeas : ViabilityRepairFeasible h) (hker : viabilityRepairBoundary h = 0)
    (hnorm : h.1.1 + h.1.2 + h.2 = 1) :
    h = (((1 : ℝ) / 3, (1 : ℝ) / 3), (1 : ℝ) / 3) := by
  rw [viabilityRepairBoundary_eq_zero_iff] at hker
  rcases h with ⟨⟨x, y⟩, t⟩
  simp only at hker hnorm ⊢
  rcases hker with ⟨rfl, rfl⟩
  apply Prod.ext
  · apply Prod.ext <;> linarith
  · linarith

/-- Every rule is load-bearing: a closed history with any zero coordinate is the zero history. -/
theorem viabilityRepair_kernel_zero_coordinate_minimal (h : ViabilityRepairFlux)
    (hker : viabilityRepairBoundary h = 0)
    (hz : h.1.1 = 0 ∨ h.1.2 = 0 ∨ h.2 = 0) : h = 0 := by
  rw [viabilityRepairBoundary_eq_zero_iff] at hker
  rcases h with ⟨⟨x, y⟩, t⟩
  simp only at hker hz ⊢
  rcases hker with ⟨rfl, rfl⟩
  rcases hz with h | h | h <;> simp_all

/-! ## Strict-progress duality -/

/-- Strict scalar progress on the two old rule directions. -/
def viabilityOldPotential : ViabilityOldFlux →ₗ[ℝ] ℝ where
  toFun z := z.1 + z.2
  map_add' _ _ := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' _ _ := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring

theorem viabilityOldPotential_positive :
    0 < viabilityOldPotential (1, 0) ∧ 0 < viabilityOldPotential (0, 1) := by
  norm_num [viabilityOldPotential]

/-- Positive circulation birth destroys every scalar functional strictly positive on all three
directed rule vectors. -/
theorem viabilityRepair_no_strict_progress :
    ¬ ∃ ell : ViabilityOldFlux →ₗ[ℝ] ℝ,
      0 < ell (1, 0) ∧ 0 < ell (0, 1) ∧ 0 < ell (-1, -1) := by
  rintro ⟨ell, h1, h2, hr⟩
  have heq : ell (-1, -1) = -(ell (1, 0) + ell (0, 1)) := by
    calc
      ell (-1, -1) = ell (-((1, 0) + (0, 1))) := by norm_num
      _ = -(ell ((1, 0) + (0, 1))) := by rw [map_neg]
      _ = -(ell (1, 0) + ell (0, 1)) := by rw [map_add]
  linarith

/-! ## Repair-generated open history -/

/-- `n` traversals of the born positive circulation. -/
def viabilityCycleHistory (n : ℕ) : ViabilityRepairFlux :=
  (((n : ℝ), (n : ℝ)), (n : ℝ))

/-- Positive unit execution cost. -/
def viabilityExecutionSize (h : ViabilityRepairFlux) : ℝ := h.1.1 + h.1.2 + h.2

theorem viabilityCycleHistory_boundary_zero (n : ℕ) :
    viabilityRepairBoundary (viabilityCycleHistory n) = 0 := by
  ext <;> simp [viabilityRepairBoundary, viabilityCycleHistory]

theorem viabilityCycleHistory_size (n : ℕ) :
    viabilityExecutionSize (viabilityCycleHistory n) = 3 * n := by
  simp [viabilityExecutionSize, viabilityCycleHistory]
  ring

/-- Endpoint semantics is stationary while positive execution size is unbounded. -/
theorem viabilityCycleHistory_unbounded (N : ℕ) :
    (N : ℝ) < viabilityExecutionSize (viabilityCycleHistory (N + 1)) := by
  rw [viabilityCycleHistory_size]
  push_cast
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  linarith

/-- Positive cycle cost cannot be represented by any scalar potential of the semantic endpoint. -/
theorem viabilityUnitCost_not_endpoint_integrable :
    ∀ Phi : ViabilityOldFlux → ℝ,
      viabilityExecutionSize (viabilityCycleHistory 1) ≠
        Phi (viabilityRepairBoundary (viabilityCycleHistory 1)) - Phi 0 := by
  intro Phi h
  rw [viabilityCycleHistory_boundary_zero] at h
  simp only [sub_self] at h
  rw [viabilityCycleHistory_size] at h
  norm_num at h

/-- Closed unconditional package: stationary semantics, exact viability ray, minimal support,
coercivity loss, and open positive-cost history occur in one repair event. -/
theorem viabilityCoercivityTransmutationMechanism_unconditional :
    Function.Surjective viabilityOldBoundary ∧
    Function.Surjective viabilityRepairBoundary ∧
    (∀ h : ViabilityRepairFlux,
      viabilityRepairBoundary h = 0 ↔ ∃ t : ℝ, h = ((t, t), t)) ∧
    (∀ h : ViabilityRepairFlux,
      ViabilityRepairFeasible h → viabilityRepairBoundary h = 0 →
      h.1.1 + h.1.2 + h.2 = 1 →
      h = (((1 : ℝ) / 3, (1 : ℝ) / 3), (1 : ℝ) / 3)) ∧
    (∀ h : ViabilityRepairFlux,
      viabilityRepairBoundary h = 0 →
      (h.1.1 = 0 ∨ h.1.2 = 0 ∨ h.2 = 0) → h = 0) ∧
    (0 < viabilityOldPotential (1, 0) ∧ 0 < viabilityOldPotential (0, 1)) ∧
    (¬ ∃ ell : ViabilityOldFlux →ₗ[ℝ] ℝ,
      0 < ell (1, 0) ∧ 0 < ell (0, 1) ∧ 0 < ell (-1, -1)) ∧
    (∀ n : ℕ, viabilityRepairBoundary (viabilityCycleHistory n) = 0) ∧
    (∀ N : ℕ, (N : ℝ) < viabilityExecutionSize (viabilityCycleHistory (N + 1))) ∧
    (∀ Phi : ViabilityOldFlux → ℝ,
      viabilityExecutionSize (viabilityCycleHistory 1) ≠
        Phi (viabilityRepairBoundary (viabilityCycleHistory 1)) - Phi 0) := by
  exact ⟨viabilityOldBoundary_surjective, viabilityRepairBoundary_surjective,
    viabilityRepairBoundary_kernel_ray, viabilityRepair_normalized_feasible_unique,
    viabilityRepair_kernel_zero_coordinate_minimal, viabilityOldPotential_positive,
    viabilityRepair_no_strict_progress, viabilityCycleHistory_boundary_zero,
    viabilityCycleHistory_unbounded, viabilityUnitCost_not_endpoint_integrable⟩

end GaloisForLFunctions.HTGeometry
