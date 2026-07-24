import Mathlib

/-!
# Injectivity modulus and finite-resolution law escape

The finite-resolution law-escape theorem of `wigner-smith-finite-resolution-law-escape` rests on a
general functional-analysis fact: the **injectivity modulus** `γ(A) = ⨅_{‖v‖=1} ‖A v‖` (the smallest
singular value) is `1`-Lipschitz in operator norm.  Hence if a finite-resolution evaluation map `A_ε`
converges to an injective law-evaluation `A` (so `γ(A) > 0`), then `γ(A_ε) ≥ γ(A)/2` for all
sufficiently fine resolutions: every fine-enough finite-bandwidth trace still violates every nonzero
law in the window.  This file formalizes that stability mechanism abstractly and unconditionally.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Injectivity modulus (smallest singular value) of a continuous linear map:
`γ(A) = ⨅_{‖v‖=1} ‖A v‖`. -/
noncomputable def injMod (A : E →L[ℝ] F) : ℝ := ⨅ w : Metric.sphere (0 : E) 1, ‖A w‖

theorem bddBelow_injMod (A : E →L[ℝ] F) :
    BddBelow (Set.range fun w : Metric.sphere (0 : E) 1 => ‖A w‖) :=
  ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩

theorem injMod_le (A : E →L[ℝ] F) (w : Metric.sphere (0 : E) 1) : injMod A ≤ ‖A w‖ :=
  ciInf_le (bddBelow_injMod A) w

theorem injMod_nonneg [Nontrivial E] (A : E →L[ℝ] F) : 0 ≤ injMod A := by
  haveI : Nonempty (Metric.sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.mpr (by norm_num)).to_subtype
  exact le_ciInf (fun w => norm_nonneg _)

/-- **Perturbation stability of the injectivity modulus.**  `γ(A) - ‖A - B‖ ≤ γ(B)`; the injectivity
modulus is `1`-Lipschitz in operator norm. -/
theorem injMod_sub_opNorm_le [Nontrivial E] (A B : E →L[ℝ] F) :
    injMod A - ‖A - B‖ ≤ injMod B := by
  haveI : Nonempty (Metric.sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.mpr (by norm_num)).to_subtype
  refine le_ciInf (fun w => ?_)
  have hw : ‖(w : E)‖ = 1 := by rw [← mem_sphere_zero_iff_norm]; exact w.2
  have h1 : injMod A ≤ ‖A w‖ := injMod_le A w
  have h2 : ‖A (w : E) - B (w : E)‖ ≤ ‖A - B‖ := by
    have := (A - B).unit_le_opNorm (w : E) (by rw [hw])
    rwa [ContinuousLinearMap.sub_apply] at this
  have h3 : ‖A (w : E)‖ ≤ ‖A (w : E) - B (w : E)‖ + ‖B (w : E)‖ := by
    have ht := norm_add_le (A (w : E) - B (w : E)) (B (w : E))
    rwa [sub_add_cancel] at ht
  linarith

/-- **Finite-resolution law escape.**  If a perturbation is within half the injectivity modulus,
the modulus stays above half: `‖A - B‖ ≤ γ(A)/2 ⟹ γ(A)/2 ≤ γ(B)`. -/
theorem half_injMod_le [Nontrivial E] {A B : E →L[ℝ] F} (h : ‖A - B‖ ≤ injMod A / 2) :
    injMod A / 2 ≤ injMod B := by
  have := injMod_sub_opNorm_le A B
  linarith

/-- The injectivity modulus is `1`-Lipschitz: `|γ(A) - γ(B)| ≤ ‖A - B‖`. -/
theorem abs_injMod_sub_le [Nontrivial E] (A B : E →L[ℝ] F) :
    |injMod A - injMod B| ≤ ‖A - B‖ := by
  rw [abs_sub_le_iff]
  constructor
  · have := injMod_sub_opNorm_le A B; linarith
  · have := injMod_sub_opNorm_le B A
    rw [norm_sub_rev] at this; linarith

end GaloisForLFunctions.HTGeometry
