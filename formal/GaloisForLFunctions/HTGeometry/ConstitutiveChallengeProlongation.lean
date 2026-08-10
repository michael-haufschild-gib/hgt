import Mathlib

/-!
# Constitutive challenge prolongation

A source promoter generates a lineage of legal challenges.  An intertwining observer maps the
source challenge space onto the observed challenge space, contracts its rank, and can create an
apparent recurrence only by erasing a definite source challenge combination.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {𝕜 : Type u} {V : Type v} {W : Type w}
variable [Field 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup W] [Module 𝕜 W]

def challengeProlongation (D : V →ₗ[𝕜] V) (v : V) : ℕ → V
  | 0 => v
  | n + 1 => D (challengeProlongation D v n)

@[simp] theorem challengeProlongation_zero (D : V →ₗ[𝕜] V) (v : V) :
    challengeProlongation D v 0 = v := rfl

@[simp] theorem challengeProlongation_succ (D : V →ₗ[𝕜] V) (v : V) (n : ℕ) :
    challengeProlongation D v (n + 1) = D (challengeProlongation D v n) := rfl

theorem map_challengeProlongation
    (D : V →ₗ[𝕜] V) (E : W →ₗ[𝕜] W) (q : V →ₗ[𝕜] W)
    (hintertwine : q.comp D = E.comp q) (v : V) (n : ℕ) :
    q (challengeProlongation D v n) = challengeProlongation E (q v) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [challengeProlongation_succ, challengeProlongation_succ]
      have hpoint := LinearMap.congr_fun hintertwine (challengeProlongation D v n)
      change q (D (challengeProlongation D v n)) =
        E (q (challengeProlongation D v n)) at hpoint
      rw [hpoint, ih]

def challengeCombination
    (D : V →ₗ[𝕜] V) (v : V) {n : ℕ} (a : Fin n → 𝕜) : V :=
  ∑ i, a i • challengeProlongation D v (i : ℕ)

theorem map_challengeCombination
    (D : V →ₗ[𝕜] V) (E : W →ₗ[𝕜] W) (q : V →ₗ[𝕜] W)
    (hintertwine : q.comp D = E.comp q) (v : V) {n : ℕ} (a : Fin n → 𝕜) :
    q (challengeCombination D v a) = challengeCombination E (q v) a := by
  simp only [challengeCombination, map_sum, LinearMap.map_smul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_challengeProlongation D E q hintertwine v i]

def challengeSpace (D : V →ₗ[𝕜] V) (v : V) (n : ℕ) : Submodule 𝕜 V :=
  Submodule.span 𝕜 (Set.range fun i : Fin n => challengeProlongation D v (i : ℕ))

theorem challengeCombination_mem_space
    (D : V →ₗ[𝕜] V) (v : V) {n : ℕ} (a : Fin n → 𝕜) :
    challengeCombination D v a ∈ challengeSpace D v n := by
  apply Submodule.sum_mem
  intro i _hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem map_challengeSpace
    (D : V →ₗ[𝕜] V) (E : W →ₗ[𝕜] W) (q : V →ₗ[𝕜] W)
    (hintertwine : q.comp D = E.comp q) (v : V) (n : ℕ) :
    Submodule.map q (challengeSpace D v n) = challengeSpace E (q v) n := by
  rw [challengeSpace, challengeSpace, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (map_challengeProlongation D E q hintertwine v i).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨challengeProlongation D v i, ⟨i, rfl⟩, ?_⟩
    exact map_challengeProlongation D E q hintertwine v i

theorem finrank_challengeSpace_observer_le
    (D : V →ₗ[𝕜] V) (E : W →ₗ[𝕜] W) (q : V →ₗ[𝕜] W)
    (hintertwine : q.comp D = E.comp q) (v : V) (n : ℕ) :
    Module.finrank 𝕜 (challengeSpace E (q v) n) ≤
      Module.finrank 𝕜 (challengeSpace D v n) := by
  letI : Module.Finite 𝕜 (challengeSpace D v n) :=
    Module.Finite.of_fg (Submodule.fg_span (Set.finite_range _))
  rw [← map_challengeSpace D E q hintertwine v n]
  exact Submodule.finrank_map_le q (challengeSpace D v n)

theorem observerRelation_iff_hiddenKernel
    (D : V →ₗ[𝕜] V) (E : W →ₗ[𝕜] W) (q : V →ₗ[𝕜] W)
    (hintertwine : q.comp D = E.comp q) (v : V) {n : ℕ} (a : Fin n → 𝕜) :
    challengeCombination E (q v) a = 0 ↔ challengeCombination D v a ∈ LinearMap.ker q := by
  rw [LinearMap.mem_ker, map_challengeCombination D E q hintertwine v a]

theorem observerRelation_reflects_of_injective
    (D : V →ₗ[𝕜] V) (E : W →ₗ[𝕜] W) (q : V →ₗ[𝕜] W)
    (hintertwine : q.comp D = E.comp q) (hq : Function.Injective q)
    (v : V) {n : ℕ} (a : Fin n → 𝕜)
    (hobserved : challengeCombination E (q v) a = 0) :
    challengeCombination D v a = 0 := by
  apply hq
  rw [map_challengeCombination D E q hintertwine v a, hobserved, map_zero]

theorem observerRelation_reflects_of_injectiveOnChallengeSpace
    (D : V →ₗ[𝕜] V) (E : W →ₗ[𝕜] W) (q : V →ₗ[𝕜] W)
    (hintertwine : q.comp D = E.comp q) (v : V) {n : ℕ} (a : Fin n → 𝕜)
    (hinjective : ∀ x ∈ challengeSpace D v n, q x = 0 → x = 0)
    (hobserved : challengeCombination E (q v) a = 0) :
    challengeCombination D v a = 0 := by
  apply hinjective _ (challengeCombination_mem_space D v a)
  rw [map_challengeCombination D E q hintertwine v a, hobserved]

theorem exists_hiddenChallenge_of_observerDependence
    (D : V →ₗ[𝕜] V) (E : W →ₗ[𝕜] W) (q : V →ₗ[𝕜] W)
    (hintertwine : q.comp D = E.comp q) (v : V) (n : ℕ)
    (hsource : LinearIndependent 𝕜
      (fun i : Fin n => challengeProlongation D v (i : ℕ)))
    (hobserved : ¬ LinearIndependent 𝕜
      (fun i : Fin n => challengeProlongation E (q v) (i : ℕ))) :
    ∃ a : Fin n → 𝕜,
      a ≠ 0 ∧
      challengeCombination D v a ≠ 0 ∧
      challengeCombination D v a ∈ LinearMap.ker q ∧
      challengeCombination E (q v) a = 0 := by
  rw [Fintype.linearIndependent_iff] at hsource hobserved
  push Not at hobserved
  obtain ⟨a, haObserved, i, hai⟩ := hobserved
  have ha : a ≠ 0 := by
    intro hzero
    apply hai
    exact congrFun hzero i
  have haSource : challengeCombination D v a ≠ 0 := by
    intro hzero
    exact hai (hsource a hzero i)
  have haKernel : challengeCombination D v a ∈ LinearMap.ker q :=
    (observerRelation_iff_hiddenKernel D E q hintertwine v a).mp haObserved
  exact ⟨a, ha, haSource, haKernel, haObserved⟩

theorem constitutiveChallengeProlongation_closed
    (D : V →ₗ[𝕜] V) (E : W →ₗ[𝕜] W) (q : V →ₗ[𝕜] W)
    (hintertwine : q.comp D = E.comp q) (v : V) :
    (∀ n, q (challengeProlongation D v n) = challengeProlongation E (q v) n) ∧
      (∀ (n : ℕ) (a : Fin n → 𝕜),
        q (challengeCombination D v a) = challengeCombination E (q v) a) ∧
      (∀ n, Submodule.map q (challengeSpace D v n) = challengeSpace E (q v) n) ∧
      (∀ (n : ℕ) (a : Fin n → 𝕜),
        challengeCombination E (q v) a = 0 ↔
          challengeCombination D v a ∈ LinearMap.ker q) := by
  exact ⟨map_challengeProlongation D E q hintertwine v,
    fun _ a => map_challengeCombination D E q hintertwine v a,
    map_challengeSpace D E q hintertwine v,
    fun _ a => observerRelation_iff_hiddenKernel D E q hintertwine v a⟩

end

end GaloisForLFunctions.HTGeometry
