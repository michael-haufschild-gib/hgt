import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.SourceOrientation

/-!
# Regular readers are blind to the incompatibility modules

A module `P` is *`t`-torsion free* when `t • p = 0` forces `p = 0`.  Any module annihilated by `t`
admits only the zero map into a `t`-torsion-free module.  Applied to `t = q - 1` this says that
every homomorphism from the physical incompatibility module `Q` — or from the source orientation
line `Q_src` — to a torsion-free reader vanishes.

* `linearMap_eq_zero_of_annihilator_torsionFree` — the general vanishing lemma;
* `hom_incompatModule_eq_zero` — `Hom_R(Q, P) = 0`;
* `hom_srcIncompatModule_eq_zero` — `Hom_R(Q_src, P) = 0`;
* the corresponding `Subsingleton` instances.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

universe u v w

section General

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {P : Type w} [AddCommGroup P] [Module R P]

/-- **Regular-reader exclusion.**  If `t` annihilates `M` and `P` is `t`-torsion free, then every
`R`-linear map `M → P` is zero. -/
theorem linearMap_eq_zero_of_annihilator_torsionFree {t : R}
    (hM : t ∈ Module.annihilator R M) (hP : ∀ p : P, t • p = 0 → p = 0)
    (f : M →ₗ[R] P) : f = 0 := by
  ext m
  refine hP (f m) ?_
  rw [← f.map_smul, Module.mem_annihilator.1 hM m, map_zero]

theorem subsingleton_hom_of_annihilator_torsionFree {t : R}
    (hM : t ∈ Module.annihilator R M) (hP : ∀ p : P, t • p = 0 → p = 0) :
    Subsingleton (M →ₗ[R] P) :=
  ⟨fun f g => by
    rw [linearMap_eq_zero_of_annihilator_torsionFree hM hP f,
      linearMap_eq_zero_of_annihilator_torsionFree hM hP g]⟩

end General

section Incompat

variable {R : Type u} [CommRing R] {P : Type w} [AddCommGroup P] [Module R P] {q c : R}

theorem wallEq_mem_annihilator_incompatModule (hc : IsUnit c) :
    (q - 1) ∈ Module.annihilator R (incompatModule q c) := by
  rw [annihilator_incompatModule q c hc]
  exact Ideal.mem_span_singleton_self _

/-- **Theorem 4.1, `Hom` half.**  Every map from the physical incompatibility module to a
`(q-1)`-torsion-free reader vanishes. -/
theorem hom_incompatModule_eq_zero (hc : IsUnit c)
    (hP : ∀ p : P, (q - 1) • p = 0 → p = 0) (f : incompatModule q c →ₗ[R] P) : f = 0 :=
  linearMap_eq_zero_of_annihilator_torsionFree (M := incompatModule q c) (t := q - 1)
    (wallEq_mem_annihilator_incompatModule hc) hP f

theorem subsingleton_hom_incompatModule (hc : IsUnit c)
    (hP : ∀ p : P, (q - 1) • p = 0 → p = 0) :
    Subsingleton (incompatModule q c →ₗ[R] P) :=
  subsingleton_hom_of_annihilator_torsionFree (M := incompatModule q c) (t := q - 1)
    (wallEq_mem_annihilator_incompatModule hc) hP

variable {S : Type v} [AddCommGroup S] [Module R S] {tauS : S →ₗ[R] S} {eps : S →ₗ[R] R}

theorem wallEq_mem_annihilator_srcIncompatModule (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hq : IsUnit q) (hc : IsUnit c) :
    (q - 1) ∈ Module.annihilator R (srcIncompatModule tauS eps q c) := by
  rw [annihilator_srcIncompatModule hinv heps hq hc]
  exact Ideal.mem_span_singleton_self _

/-- **Theorem 4A.1, `Hom` half.**  Every map from the source orientation line to a
`(q-1)`-torsion-free reader vanishes. -/
theorem hom_srcIncompatModule_eq_zero (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hq : IsUnit q) (hc : IsUnit c)
    (hP : ∀ p : P, (q - 1) • p = 0 → p = 0)
    (f : srcIncompatModule tauS eps q c →ₗ[R] P) : f = 0 :=
  linearMap_eq_zero_of_annihilator_torsionFree (M := srcIncompatModule tauS eps q c)
    (t := q - 1) (wallEq_mem_annihilator_srcIncompatModule hinv heps hq hc) hP f

theorem subsingleton_hom_srcIncompatModule (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hq : IsUnit q) (hc : IsUnit c)
    (hP : ∀ p : P, (q - 1) • p = 0 → p = 0) :
    Subsingleton (srcIncompatModule tauS eps q c →ₗ[R] P) :=
  subsingleton_hom_of_annihilator_torsionFree (M := srcIncompatModule tauS eps q c)
    (t := q - 1) (wallEq_mem_annihilator_srcIncompatModule hinv heps hq hc) hP

end Incompat

section TorsionFreeExamples

variable {R : Type u} [CommRing R] [IsDomain R] {q : R}

/-- A domain is torsion free over any nonzero element; in particular the ring itself is a regular
reader, so `Hom_R(Q, R) = 0`. -/
theorem domain_torsionFree (hq : q ≠ 1) : ∀ p : R, (q - 1) • p = 0 → p = 0 := by
  intro p hp
  rw [smul_eq_mul] at hp
  rcases mul_eq_zero.1 hp with h | h
  · exact absurd (by linear_combination h) hq
  · exact h

end TorsionFreeExamples

end GaloisForLFunctions.HTGeometry.DerivedSelection
