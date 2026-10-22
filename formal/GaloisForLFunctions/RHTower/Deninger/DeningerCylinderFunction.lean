import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Cylinder functions on a character space

A function of characters is cylinder at a point when near that point it is an analytic function of
finitely many evaluation coordinates.  The condition is local by construction, and it is stable
under the operations the coefficient sheaf needs: constants and evaluation coordinates are
cylinder, and sums and products of cylinder functions are cylinder, because two finite coordinate
tuples can be concatenated and the coordinate projections are continuous linear.

Permuting the character variable permutes the evaluation coordinates, so the condition is stable
under the Galois action; and a power of an evaluation coordinate is the evaluation coordinate of the
corresponding power, so it is stable under the power maps.

* `DeningerIsCylinderAt` : the cylinder condition.
* `deningerIsCylinderAt_add`, `_mul` : stability under the ring operations.
* `deningerIsCylinderAt_comp` : stability under a permutation of the character variable.
-/

namespace RHTower

open Filter Topology

section Cylinder

variable {V : Type*}

/-- A function of characters is **cylinder** at a point when near it it is an analytic function of
finitely many evaluation coordinates. -/
def DeningerIsCylinderAt (f : (V → ℂ) → ℂ) (P₀ : V → ℂ) : Prop :=
  ∃ (r : ℕ) (a : Fin r → V) (h : (Fin r → ℂ) → ℂ),
    AnalyticAt ℂ h (fun i => P₀ (a i)) ∧ ∀ᶠ P in 𝓝 P₀, f P = h fun i => P (a i)

/-- The evaluation tuple is continuous. -/
theorem deningerEvalTuple_continuous {r : ℕ} (a : Fin r → V) :
    Continuous fun P : V → ℂ => fun i => P (a i) :=
  continuous_pi fun i => continuous_apply (a i)

/-- **Constants are cylinder.** -/
theorem deningerIsCylinderAt_const (c : ℂ) (P₀ : V → ℂ) :
    DeningerIsCylinderAt (fun _ => c) P₀ :=
  ⟨0, Fin.elim0, fun _ => c, analyticAt_const, Eventually.of_forall fun _ => rfl⟩

/-- **Evaluation coordinates are cylinder.** -/
theorem deningerIsCylinderAt_eval (v : V) (P₀ : V → ℂ) :
    DeningerIsCylinderAt (fun P => P v) P₀ := by
  refine ⟨1, fun _ => v, fun x => x 0, ?_, Eventually.of_forall fun P => rfl⟩
  exact (show (Fin 1 → ℂ) →L[ℂ] ℂ from ContinuousLinearMap.proj (0 : Fin 1)).analyticAt _

/-- The left coordinate projection of a concatenation. -/
private theorem deningerAppendLeft {r s : ℕ} (a : Fin r → V) (b : Fin s → V) (P : V → ℂ) :
    (fun i => (fun k => P (Fin.append a b k)) (Fin.castAdd s i)) = fun i => P (a i) := by
  funext i
  simp [Fin.append_left]

/-- The right coordinate projection of a concatenation. -/
private theorem deningerAppendRight {r s : ℕ} (a : Fin r → V) (b : Fin s → V) (P : V → ℂ) :
    (fun j => (fun k => P (Fin.append a b k)) (Fin.natAdd r j)) = fun j => P (b j) := by
  funext j
  simp [Fin.append_right]

/-- Analyticity of a cylinder function in the concatenated coordinates. -/
private theorem deningerAnalyticLeft {r s : ℕ} {h : (Fin r → ℂ) → ℂ} {a : Fin r → V}
    {b : Fin s → V} {P₀ : V → ℂ} (hh : AnalyticAt ℂ h fun i => P₀ (a i)) :
    AnalyticAt ℂ (fun x : Fin (r + s) → ℂ => h fun i => x (Fin.castAdd s i))
      (fun k => P₀ (Fin.append a b k)) := by
  have hcomp : AnalyticAt ℂ (h ∘ fun x : Fin (r + s) → ℂ => fun i => x (Fin.castAdd s i))
      (fun k => P₀ (Fin.append a b k)) := by
    refine AnalyticAt.comp ?_ ?_
    · rw [deningerAppendLeft a b P₀]
      exact hh
    · exact (show (Fin (r + s) → ℂ) →L[ℂ] (Fin r → ℂ) from
        ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd s i)).analyticAt _
  exact hcomp

/-- Analyticity of a cylinder function in the concatenated coordinates, on the right. -/
private theorem deningerAnalyticRight {r s : ℕ} {h : (Fin s → ℂ) → ℂ} {a : Fin r → V}
    {b : Fin s → V} {P₀ : V → ℂ} (hh : AnalyticAt ℂ h fun j => P₀ (b j)) :
    AnalyticAt ℂ (fun x : Fin (r + s) → ℂ => h fun j => x (Fin.natAdd r j))
      (fun k => P₀ (Fin.append a b k)) := by
  have hcomp : AnalyticAt ℂ (h ∘ fun x : Fin (r + s) → ℂ => fun j => x (Fin.natAdd r j))
      (fun k => P₀ (Fin.append a b k)) := by
    refine AnalyticAt.comp ?_ ?_
    · rw [deningerAppendRight a b P₀]
      exact hh
    · exact (show (Fin (r + s) → ℂ) →L[ℂ] (Fin s → ℂ) from
        ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.natAdd r j)).analyticAt _
  exact hcomp

/-- **Sums of cylinder functions are cylinder.**  Concatenate the two coordinate tuples. -/
theorem deningerIsCylinderAt_add {f g : (V → ℂ) → ℂ} {P₀ : V → ℂ}
    (hf : DeningerIsCylinderAt f P₀) (hg : DeningerIsCylinderAt g P₀) :
    DeningerIsCylinderAt (fun P => f P + g P) P₀ := by
  obtain ⟨r, a, h₁, hh₁, hf'⟩ := hf
  obtain ⟨s, b, h₂, hh₂, hg'⟩ := hg
  refine ⟨r + s, Fin.append a b,
    fun x => h₁ (fun i => x (Fin.castAdd s i)) + h₂ fun j => x (Fin.natAdd r j), ?_, ?_⟩
  · exact (deningerAnalyticLeft (b := b) hh₁).add (deningerAnalyticRight (a := a) hh₂)
  · filter_upwards [hf', hg'] with P hP hQ
    rw [hP, hQ, deningerAppendLeft a b P, deningerAppendRight a b P]

/-- **Products of cylinder functions are cylinder.** -/
theorem deningerIsCylinderAt_mul {f g : (V → ℂ) → ℂ} {P₀ : V → ℂ}
    (hf : DeningerIsCylinderAt f P₀) (hg : DeningerIsCylinderAt g P₀) :
    DeningerIsCylinderAt (fun P => f P * g P) P₀ := by
  obtain ⟨r, a, h₁, hh₁, hf'⟩ := hf
  obtain ⟨s, b, h₂, hh₂, hg'⟩ := hg
  refine ⟨r + s, Fin.append a b,
    fun x => h₁ (fun i => x (Fin.castAdd s i)) * h₂ fun j => x (Fin.natAdd r j), ?_, ?_⟩
  · exact (deningerAnalyticLeft (b := b) hh₁).mul (deningerAnalyticRight (a := a) hh₂)
  · filter_upwards [hf', hg'] with P hP hQ
    rw [hP, hQ, deningerAppendLeft a b P, deningerAppendRight a b P]

/-- **The cylinder condition is stable under a permutation of the character variable.**  Galois
maps permute the evaluation coordinates. -/
theorem deningerIsCylinderAt_comp {f : (V → ℂ) → ℂ} {σ : V → V} {P₀ : V → ℂ}
    (hf : DeningerIsCylinderAt f (P₀ ∘ σ)) :
    DeningerIsCylinderAt (fun P => f (P ∘ σ)) P₀ := by
  obtain ⟨r, a, h, hh, hf'⟩ := hf
  refine ⟨r, σ ∘ a, h, hh, ?_⟩
  have hcont : Continuous fun P : V → ℂ => P ∘ σ := continuous_pi fun v => continuous_apply (σ v)
  have htend : Tendsto (fun P : V → ℂ => P ∘ σ) (𝓝 P₀) (𝓝 (P₀ ∘ σ)) := hcont.tendsto P₀
  exact htend.eventually hf'

/-- **A power of an evaluation coordinate is cylinder.** -/
theorem deningerIsCylinderAt_eval_pow (v : V) (P₀ : V → ℂ) (n : ℕ) :
    DeningerIsCylinderAt (fun P => (P v) ^ n) P₀ := by
  induction n with
  | zero =>
    simpa using deningerIsCylinderAt_const (V := V) 1 P₀
  | succ m ih =>
    have := deningerIsCylinderAt_mul ih (deningerIsCylinderAt_eval v P₀)
    simpa [pow_succ] using this

end Cylinder

end RHTower

namespace RHTower

section CylinderLocality

open Filter Topology

variable {V : Type*}

/-- **The cylinder condition is local**: a function agreeing near a point with a cylinder function
is cylinder there.  This is what makes the cylinder functions a sheaf: a function glued from
cylinder functions agreeing on overlaps is near each point one of them. -/
theorem deningerIsCylinderAt_congr {f g : (V → ℂ) → ℂ} {P₀ : V → ℂ} (h : f =ᶠ[𝓝 P₀] g)
    (hg : DeningerIsCylinderAt g P₀) : DeningerIsCylinderAt f P₀ := by
  obtain ⟨r, a, k, hk, hg'⟩ := hg
  refine ⟨r, a, k, hk, ?_⟩
  filter_upwards [h, hg'] with P hP hP'
  rw [hP, hP']

/-- **A glued family of cylinder functions is cylinder**: if a function agrees near a point with a
member of a family of cylinder functions, it is cylinder at that point. -/
theorem deningerIsCylinderAt_glue {ι : Type*} {f : (V → ℂ) → ℂ} {g : ι → (V → ℂ) → ℂ}
    {P₀ : V → ℂ} (i : ι) (h : f =ᶠ[𝓝 P₀] g i) (hg : ∀ j, DeningerIsCylinderAt (g j) P₀) :
    DeningerIsCylinderAt f P₀ :=
  deningerIsCylinderAt_congr h (hg i)

/-- The cylinder condition only depends on the germ. -/
theorem deningerIsCylinderAt_congr_iff {f g : (V → ℂ) → ℂ} {P₀ : V → ℂ} (h : f =ᶠ[𝓝 P₀] g) :
    DeningerIsCylinderAt f P₀ ↔ DeningerIsCylinderAt g P₀ :=
  ⟨fun hf => deningerIsCylinderAt_congr h.symm hf, fun hg => deningerIsCylinderAt_congr h hg⟩

end CylinderLocality

end RHTower
