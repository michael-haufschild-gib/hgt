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

open Metric Filter Topology

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

/-- **Positive injectivity modulus** `(12)`.  An injective continuous linear map from a
finite-dimensional space has `γ(A) > 0`: `‖A·‖` is continuous and strictly positive on the compact
unit sphere, so it attains a positive minimum. -/
theorem injMod_pos_of_injective [FiniteDimensional ℝ E] [Nontrivial E]
    {A : E →L[ℝ] F} (hA : Function.Injective A) : 0 < injMod A := by
  have hne : (Metric.sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr (by norm_num)
  haveI : Nonempty (Metric.sphere (0 : E) 1) := hne.to_subtype
  have hcomp : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hcont : ContinuousOn (fun v : E => ‖A v‖) (Metric.sphere (0 : E) 1) :=
    (continuous_norm.comp A.continuous).continuousOn
  obtain ⟨w, hw, hmin⟩ := hcomp.exists_isMinOn hne hcont
  have hle2 : ‖A w‖ ≤ injMod A := by
    rw [injMod]
    exact le_ciInf (fun v => (isMinOn_iff.mp hmin) v.1 v.2)
  have hw0 : (w : E) ≠ 0 := by
    intro h
    rw [mem_sphere_zero_iff_norm, h, norm_zero] at hw
    norm_num at hw
  have hpos : 0 < ‖A w‖ := by
    rw [norm_pos_iff]
    exact fun hAw => hw0 (hA (by rw [hAw, map_zero]))
  exact lt_of_lt_of_le hpos hle2

/-- **Finite-resolution law escape** `(12)`+`(14)`.  Any map within half the injectivity modulus of an
injective finite-dimensional map still has positive modulus: `γ(B) > 0`.  Every sufficiently fine
finite-bandwidth trace still violates every nonzero law in the window. -/
theorem injMod_pos_of_close_to_injective [FiniteDimensional ℝ E] [Nontrivial E]
    {A B : E →L[ℝ] F} (hA : Function.Injective A) (h : ‖A - B‖ ≤ injMod A / 2) :
    0 < injMod B := by
  have hpos := injMod_pos_of_injective hA
  have hhalf := half_injMod_le h
  linarith

/-- **Quantitative injectivity (antilipschitz bound).**  `γ(A)·‖v‖ ≤ ‖A v‖` for every `v`:
the injectivity modulus is a uniform lower Lipschitz constant. -/
theorem injMod_mul_norm_le [Nontrivial E] (A : E →L[ℝ] F) (v : E) :
    injMod A * ‖v‖ ≤ ‖A v‖ := by
  rcases eq_or_ne v 0 with h | h
  · simp [h]
  · have hv : 0 < ‖v‖ := norm_pos_iff.mpr h
    have hunit : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv.ne']
    have hle := injMod_le A ⟨‖v‖⁻¹ • v, hunit⟩
    rw [map_smul, norm_smul, norm_inv, norm_norm] at hle
    have h2 := mul_le_mul_of_nonneg_right hle hv.le
    rwa [mul_right_comm, inv_mul_cancel₀ hv.ne', one_mul] at h2

/-- **Positivity characterization.**  On a finite-dimensional domain, `0 < γ(A) ↔ A injective`. -/
theorem injMod_pos_iff [FiniteDimensional ℝ E] [Nontrivial E] (A : E →L[ℝ] F) :
    0 < injMod A ↔ Function.Injective A := by
  constructor
  · intro hpos
    refine (injective_iff_map_eq_zero A).mpr (fun v hv => ?_)
    have hb := injMod_mul_norm_le A v
    rw [hv, norm_zero] at hb
    have hvz : ‖v‖ = 0 := by
      by_contra hne
      have : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      nlinarith [hpos]
    exact norm_eq_zero.mp hvz
  · exact injMod_pos_of_injective

/-- The injectivity modulus is `1`-Lipschitz in operator norm, hence continuous. -/
theorem lipschitzWith_injMod [Nontrivial E] :
    LipschitzWith 1 (injMod : (E →L[ℝ] F) → ℝ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro A B
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  exact abs_injMod_sub_le A B

theorem continuous_injMod [Nontrivial E] :
    Continuous (injMod : (E →L[ℝ] F) → ℝ) := lipschitzWith_injMod.continuous

/-- **Limit-form finite-resolution law escape** `(13)`+`(14)`.  If `A` is injective on a
finite-dimensional space and `B x → A` (operator norm) along a filter, then `γ(B x) > 0` eventually:
any net of evaluation maps converging to an injective (hypertranscendental) one is eventually
injective with positive margin. -/
theorem injMod_eventually_pos [FiniteDimensional ℝ E] [Nontrivial E] {A : E →L[ℝ] F}
    (hA : Function.Injective A) {ι : Type*} {l : Filter ι} {B : ι → (E →L[ℝ] F)}
    (hB : Tendsto B l (𝓝 A)) : ∀ᶠ x in l, 0 < injMod (B x) := by
  have hpos : 0 < injMod A := injMod_pos_of_injective hA
  have hcont : Tendsto (fun x => injMod (B x)) l (𝓝 (injMod A)) :=
    (continuous_injMod.tendsto A).comp hB
  exact hcont.eventually (eventually_gt_nhds hpos)

end GaloisForLFunctions.HTGeometry
