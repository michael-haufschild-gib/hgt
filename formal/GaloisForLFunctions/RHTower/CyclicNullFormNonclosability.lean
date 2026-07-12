import GaloisForLFunctions.SchwartzSesquilinear
import GaloisForLFunctions.RHTower.CyclicRadicalCollapse

/-!
# Cyclic-null forms are forced to be nonclosable

A Hermitian sesquilinear form on Schwartz space whose radical family is
cyclic in an ambient normed space admits an ambient-null sequence with fixed
form energy and pairwise zero difference energy.  Any nonzero such form
therefore fails the standard sequential closability criterion.
-/

open Complex Function Filter Set
open scoped Topology SchwartzMap

noncomputable section

open RHTower

namespace SchwartzMap.ContinuousSchwartzSesquilinearForm

variable (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)

/-- The algebraic left radical of a Schwartz sesquilinear form. -/
def leftRadical : Submodule ℂ 𝓢(ℝ, ℂ) where
  carrier := {u | ∀ v, Q u v = 0}
  zero_mem' := by
    intro v
    have h := Q.map_smul_left 0 0 v
    simpa using h
  add_mem' hu hv w := by simp [hu w, hv w]
  smul_mem' c u hu w := by simp [hu w]

@[simp] theorem mem_leftRadical_iff (u : 𝓢(ℝ, ℂ)) :
    u ∈ Q.leftRadical ↔ ∀ v, Q u v = 0 :=
  Iff.rfl

/-- A sequence is Cauchy for the diagonal energy of the form. -/
def IsFormCauchy (u : ℕ → 𝓢(ℝ, ℂ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
    ‖Q (u m - u n) (u m - u n)‖ < ε

/-- Sequential closability through a linear map into an ambient normed space. -/
def IsSequentiallyClosableThrough
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (j : 𝓢(ℝ, ℂ) →ₗ[ℂ] H) : Prop :=
  ∀ u : ℕ → 𝓢(ℝ, ℂ),
    Tendsto (fun n ↦ j (u n)) atTop (𝓝 0) →
    Q.IsFormCauchy u →
    Tendsto (fun n ↦ Q (u n) (u n)) atTop (𝓝 0)

/-- A left-radical vector is also in the right radical of a Hermitian form. -/
theorem apply_eq_zero_of_mem_leftRadical_of_isHermitian
    (hHermitian : Q.IsHermitian) {r : 𝓢(ℝ, ℂ)}
    (hr : r ∈ Q.leftRadical) (u : 𝓢(ℝ, ℂ)) :
    Q u r = 0 := by
  rw [hHermitian r u]
  simp [hr u]

/-- Every vector in the span of a radical family remains radical. -/
theorem span_le_leftRadical { ι : Type*} {v : ι → 𝓢(ℝ, ℂ)}
    (hnull : ∀ i w, Q (v i) w = 0) :
    Submodule.span ℂ (Set.range v) ≤ Q.leftRadical := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hnull i

/-- A complex sesquilinear form whose diagonal vanishes identically is the zero form. -/
theorem eq_zero_of_diagonal_eq_zero
    (hdiag : ∀ w : 𝓢(ℝ, ℂ), Q w w = 0) :
    ∀ u v : 𝓢(ℝ, ℂ), Q u v = 0 := by
  intro u v
  have hplus := hdiag (u + v)
  have hI := hdiag (u + Complex.I • v)
  have huu := hdiag u
  have hvv := hdiag v
  simp only [Q.apply_add_left, Q.apply_add_right, Q.apply_smul_left,
    Q.apply_smul_right] at hplus hI
  rw [huu, hvv] at hplus hI
  have hsum : Q u v + Q v u = 0 := by simpa using hplus
  have hdiff : -Complex.I * Q u v + Complex.I * Q v u = 0 := by
    simpa using hI
  have hvu : Q v u = -Q u v := by linear_combination hsum
  rw [hvu] at hdiff
  have hmul : (-2 * Complex.I) * Q u v = 0 := by
    linear_combination hdiff
  exact (mul_eq_zero.mp hmul).resolve_left (by norm_num [Complex.I_ne_zero])

/-- Every nonzero complex sesquilinear form has a nonzero diagonal value. -/
theorem exists_diagonal_ne_zero_of_exists_apply_ne_zero
    (hne : ∃ u v : 𝓢(ℝ, ℂ), Q u v ≠ 0) :
    ∃ w : 𝓢(ℝ, ℂ), Q w w ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  obtain ⟨u, v, huv⟩ := hne
  exact huv (Q.eq_zero_of_diagonal_eq_zero h u v)

/-- Every vector in the image-orbit span has a preimage in the source-orbit span. -/
theorem exists_span_preimage
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (j : 𝓢(ℝ, ℂ) →ₗ[ℂ] H) {ι : Type*} (v : ι → 𝓢(ℝ, ℂ))
    {x : H} (hx : x ∈ Submodule.span ℂ (Set.range fun i ↦ j (v i))) :
    ∃ r : 𝓢(ℝ, ℂ), r ∈ Submodule.span ℂ (Set.range v) ∧ j r = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨v i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨rx, hrx, hjx⟩ := hx
      obtain ⟨ry, hry, hjy⟩ := hy
      exact ⟨rx + ry, Submodule.add_mem _ hrx hry, by simp [hjx, hjy]⟩
  | smul c x _ hx =>
      obtain ⟨r, hr, hj⟩ := hx
      exact ⟨c • r, Submodule.smul_mem _ c hr, by simp [hj]⟩

/-- **Cyclic-null singular-sequence theorem.** A Hermitian form whose radical family is cyclic
through the ambient embedding has, around every source vector, an ambient-null sequence with
constant form energy and pairwise zero difference energy. -/
theorem exists_ambientNull_constantEnergy_sequence_of_cyclic_null
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (j : 𝓢(ℝ, ℂ) →ₗ[ℂ] H) (v : ι → 𝓢(ℝ, ℂ))
    (hcyclic : IsCyclicFamily (𝕜 := ℂ) (fun i ↦ j (v i)))
    (hHermitian : Q.IsHermitian)
    (hnull : ∀ i w, Q (v i) w = 0)
    (u : 𝓢(ℝ, ℂ)) :
    ∃ z : ℕ → 𝓢(ℝ, ℂ),
      Tendsto (fun n ↦ j (z n)) atTop (𝓝 0) ∧
      (∀ m n, Q (z m - z n) (z m - z n) = 0) ∧
      (∀ n, Q (z n) (z n) = Q u u) := by
  have hju : j u ∈ closure
      (Submodule.span ℂ (Set.range fun i ↦ j (v i)) : Set H) := by
    rw [hcyclic.closure_eq]
    exact Set.mem_univ _
  obtain ⟨x, hxspan, hxtend⟩ := mem_closure_iff_seq_limit.mp hju
  have hlift (n : ℕ) :
      ∃ r : 𝓢(ℝ, ℂ), r ∈ Submodule.span ℂ (Set.range v) ∧ j r = x n :=
    exists_span_preimage j v (hxspan n)
  choose r hrspan hjr using hlift
  let z : ℕ → 𝓢(ℝ, ℂ) := fun n ↦ u - r n
  have hspanRad : Submodule.span ℂ (Set.range v) ≤ Q.leftRadical :=
    Q.span_le_leftRadical hnull
  have hrRad (n : ℕ) : r n ∈ Q.leftRadical := hspanRad (hrspan n)
  have hleft (n : ℕ) (w : 𝓢(ℝ, ℂ)) : Q (r n) w = 0 := (hrRad n) w
  have hright (n : ℕ) (w : 𝓢(ℝ, ℂ)) : Q w (r n) = 0 :=
    Q.apply_eq_zero_of_mem_leftRadical_of_isHermitian hHermitian (hrRad n) w
  refine ⟨z, ?_, ?_, ?_⟩
  · have hsub : Tendsto (fun n ↦ j u - x n) atTop (𝓝 (j u - j u)) :=
      tendsto_const_nhds.sub hxtend
    have heq : (fun n ↦ j (z n)) = fun n ↦ j u - x n := by
      funext n
      simp [z, hjr n]
    rw [heq]
    simpa using hsub
  · intro m n
    have hdiff : z m - z n = r n - r m := by
      dsimp [z]
      abel
    rw [hdiff]
    have hrad : r n - r m ∈ Q.leftRadical :=
      Submodule.sub_mem _ (hrRad n) (hrRad m)
    exact hrad _
  · intro n
    rw [show z n = u - r n by rfl, Q.apply_sub_left, Q.apply_sub_right]
    simp [hleft n, hright n]

/-- A cyclic radical and one nonzero diagonal force failure of sequential closability through the
ambient normed space. -/
theorem not_isSequentiallyClosableThrough_of_cyclic_null
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (j : 𝓢(ℝ, ℂ) →ₗ[ℂ] H) (v : ι → 𝓢(ℝ, ℂ))
    (hcyclic : IsCyclicFamily (𝕜 := ℂ) (fun i ↦ j (v i)))
    (hHermitian : Q.IsHermitian)
    (hnull : ∀ i w, Q (v i) w = 0)
    {u : 𝓢(ℝ, ℂ)} (hu : Q u u ≠ 0) :
    ¬ Q.IsSequentiallyClosableThrough j := by
  intro hclose
  obtain ⟨z, hz0, hzdiff, hzenergy⟩ :=
    Q.exists_ambientNull_constantEnergy_sequence_of_cyclic_null
      j v hcyclic hHermitian hnull u
  have hzcauchy : Q.IsFormCauchy z := by
    intro ε hε
    refine ⟨0, ?_⟩
    intro m _ n _
    rw [hzdiff]
    simpa using hε
  have htozero := hclose z hz0 hzcauchy
  have htoconst : Tendsto (fun n ↦ Q (z n) (z n)) atTop (𝓝 (Q u u)) := by
    simpa only [hzenergy] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ Q u u) atTop (𝓝 (Q u u)))
  exact hu (tendsto_nhds_unique htoconst htozero)

end SchwartzMap.ContinuousSchwartzSesquilinearForm

end
