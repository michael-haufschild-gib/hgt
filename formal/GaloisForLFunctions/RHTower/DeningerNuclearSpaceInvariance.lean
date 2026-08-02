import GaloisForLFunctions.RHTower.DeningerSeminormQuotient

/-!
# Nuclearity does not depend on the defining seminorm family

Comparison maps of seminorms are determined by their effect on classes of vectors, so two
dominations with different constants give the same map, and a chain of dominations gives the
composite of the comparison maps.

Consequently nuclearity is an invariant of the topology, not of the chosen family of seminorms:
if two families dominate each other then one is nuclear exactly when the other is.  This is what
lets a nuclear space be tested on any convenient cofinal exhaustion.

* `deningerSeminormComparison_ext` : comparison maps are determined on classes.
* `deningerSeminormComparison_congr` : the constant does not matter.
* `deningerSeminormComparison_trans` : a chain of dominations composes.
* `deningerIsNuclearSpace_of_dominating` : nuclearity transfers between mutually dominating
  families.
* `deningerIsNuclearSpace_comp` : nuclearity may be tested on a cofinal subfamily.
-/

namespace RHTower

section Comparison

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **A map out of a seminorm quotient is determined on classes of vectors.** -/
theorem deningerSeminormComparison_ext {p q : Seminorm 𝕜 E}
    (f g : DeningerSeminormSpace q →L[𝕜] DeningerSeminormSpace p)
    (h : ∀ x : E, f (deningerSeminormMk q x) = g (deningerSeminormMk q x)) : f = g := by
  refine ContinuousLinearMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := deningerSeminormMk_surjective q z
  exact h x

/-- **The comparison map does not depend on the constant.** -/
theorem deningerSeminormComparison_congr {p q : Seminorm 𝕜 E} {C C' : ℝ}
    (h : ∀ x, p x ≤ C * q x) (h' : ∀ x, p x ≤ C' * q x) :
    deningerSeminormComparison h = deningerSeminormComparison h' :=
  deningerSeminormComparison_ext _ _ fun _ => rfl

/-- A domination holds with the absolute value of its constant. -/
theorem deningerSeminorm_le_abs {p q : Seminorm 𝕜 E} {C : ℝ} (h : ∀ x, p x ≤ C * q x) :
    ∀ x, p x ≤ |C| * q x := by
  intro x
  refine (h x).trans ?_
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (apply_nonneg q x)

/-- **A chain of dominations composes.** -/
theorem deningerSeminormComparison_trans {p q r : Seminorm 𝕜 E} {C C' D : ℝ}
    (h₁ : ∀ x, p x ≤ C * q x) (h₂ : ∀ x, q x ≤ C' * r x)
    (h₃ : ∀ x, p x ≤ D * r x) :
    deningerSeminormComparison h₃
      = (deningerSeminormComparison h₁).comp (deningerSeminormComparison h₂) :=
  deningerSeminormComparison_ext _ _ fun _ => rfl

theorem DeningerIsNuclear.of_eq {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y] {T S : X →L[𝕜] Y}
    (hT : DeningerIsNuclear T) (hEq : S = T) : DeningerIsNuclear S := hEq ▸ hT

end Comparison

section Invariance

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Nuclearity transfers between mutually dominating seminorm families.**  A comparison map of
the second family factors through a nuclear comparison map of the first, using the two dominations
to pass between the families. -/
theorem deningerIsNuclearSpace_of_dominating {ι κ : Type*} (P : SeminormFamily 𝕜 E ι)
    (Q : SeminormFamily 𝕜 E κ)
    (hPQ : ∀ k, ∃ (i : ι) (C : ℝ), ∀ x, Q k x ≤ C * P i x)
    (hQP : ∀ i, ∃ (k : κ) (C : ℝ), ∀ x, P i x ≤ C * Q k x)
    (hP : DeningerIsNuclearSpace P) : DeningerIsNuclearSpace Q := by
  intro k
  obtain ⟨i, C₁, h₁⟩ := hPQ k
  obtain ⟨i', C, h₂, hnuc⟩ := hP i
  obtain ⟨j, C₂, h₃⟩ := hQP i'
  have h₁' : ∀ x, Q k x ≤ |C₁| * P i x := deningerSeminorm_le_abs h₁
  have h₂' : ∀ x, P i x ≤ |C| * P i' x := deningerSeminorm_le_abs h₂
  have h₃' : ∀ x, P i' x ≤ |C₂| * Q j x := deningerSeminorm_le_abs h₃
  have hchain : ∀ x, Q k x ≤ (|C₁| * |C| * |C₂|) * Q j x := by
    intro x
    calc Q k x ≤ |C₁| * P i x := h₁' x
      _ ≤ |C₁| * (|C| * P i' x) :=
          mul_le_mul_of_nonneg_left (h₂' x) (abs_nonneg C₁)
      _ ≤ |C₁| * (|C| * (|C₂| * Q j x)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (h₃' x) (abs_nonneg C)) (abs_nonneg C₁)
      _ = (|C₁| * |C| * |C₂|) * Q j x := by ring
  refine ⟨j, |C₁| * |C| * |C₂|, hchain, ?_⟩
  have hcomp : DeningerIsNuclear
      ((deningerSeminormComparison h₁').comp
        ((deningerSeminormComparison h₂).comp (deningerSeminormComparison h₃'))) :=
    ((hnuc.compR (deningerSeminormComparison h₃')).compL (deningerSeminormComparison h₁'))
  refine hcomp.of_eq ?_
  refine deningerSeminormComparison_ext _ _ fun _ => rfl

/-- **Nuclearity may be tested on a cofinal subfamily.**  If every seminorm of a family is
dominated by one indexed through a reindexing map, the reindexed family is nuclear as soon as the
original is.  This is why the nuclear test topology may be computed on any cofinal exhaustion. -/
theorem deningerIsNuclearSpace_comp {ι κ : Type*} (P : SeminormFamily 𝕜 E ι) (f : κ → ι)
    (hcof : ∀ i, ∃ (k : κ) (C : ℝ), ∀ x, P i x ≤ C * P (f k) x)
    (hP : DeningerIsNuclearSpace P) : DeningerIsNuclearSpace (fun k => P (f k)) := by
  refine deningerIsNuclearSpace_of_dominating P (fun k => P (f k)) ?_ ?_ hP
  · intro k
    exact ⟨f k, 1, fun x => by rw [one_mul]⟩
  · intro i
    exact hcof i

end Invariance

end RHTower

