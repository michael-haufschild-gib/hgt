import GaloisForLFunctions.HTGeometry.ClosedRangeTransgression
import GaloisForLFunctions.HTGeometry.HilbertBlockOperator
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# A closed-range history whose transgression fails

Two closed subspaces of a Hilbert space can have a non-closed sum, and then the inclusion of the
first and the orthogonal projection onto the complement of the second are closed-range maps whose
composite is not of closed range.  This file makes that configuration explicit.

Inside the orthogonal double `E ⊕₂ E` the first summand `firstSummand` and the graph
`graphSubmodule T` of a bounded operator are both closed, and their sum is the preimage of
`range T` under the second-coordinate projection; the sum is therefore closed exactly when
`range T` is.  Taking for `T` the diagonal operator on `ℓ²(ℕ)` with entries `(i+1)⁻¹`, whose range
is dense and proper, produces closed subspaces with non-closed sum.

Composing the resulting non-closed-range map with the zero map restores closedness of the total
range, so terminal closedness of a finite history does not imply that every prefix is proper.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ENNReal

section OrthogonalDouble

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- First coordinate of the orthogonal double `E ⊕₂ E`. -/
noncomputable def doubleFst : WithLp 2 (E × E) →L[𝕜] E :=
  (ContinuousLinearMap.fst 𝕜 E E).comp
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 E E : WithLp 2 (E × E) ≃L[𝕜] E × E) :
      WithLp 2 (E × E) →L[𝕜] E × E)

/-- Second coordinate of the orthogonal double `E ⊕₂ E`. -/
noncomputable def doubleSnd : WithLp 2 (E × E) →L[𝕜] E :=
  (ContinuousLinearMap.snd 𝕜 E E).comp
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 E E : WithLp 2 (E × E) ≃L[𝕜] E × E) :
      WithLp 2 (E × E) →L[𝕜] E × E)

/-- The section of the second coordinate that lands in the second summand. -/
noncomputable def doubleInr : E →L[𝕜] WithLp 2 (E × E) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E E).symm : E × E →L[𝕜] WithLp 2 (E × E)).comp
    (ContinuousLinearMap.inr 𝕜 E E)

@[simp] theorem doubleFst_toLp (x y : E) : doubleFst 𝕜 E (WithLp.toLp 2 (x, y)) = x := rfl

@[simp] theorem doubleSnd_toLp (x y : E) : doubleSnd 𝕜 E (WithLp.toLp 2 (x, y)) = y := rfl

@[simp] theorem doubleFst_doubleInr (y : E) : doubleFst 𝕜 E (doubleInr 𝕜 E y) = 0 := rfl

@[simp] theorem doubleSnd_doubleInr (y : E) : doubleSnd 𝕜 E (doubleInr 𝕜 E y) = y := rfl

/-- The first summand of the orthogonal double, as the kernel of the second coordinate. -/
noncomputable def firstSummand : Submodule 𝕜 (WithLp 2 (E × E)) :=
  LinearMap.ker ((doubleSnd 𝕜 E : WithLp 2 (E × E) →L[𝕜] E) : WithLp 2 (E × E) →ₗ[𝕜] E)

theorem mem_firstSummand {v : WithLp 2 (E × E)} :
    v ∈ firstSummand 𝕜 E ↔ doubleSnd 𝕜 E v = 0 := Iff.rfl

theorem isClosed_firstSummand : IsClosed ((firstSummand 𝕜 E : Submodule 𝕜 (WithLp 2 (E × E)))
    : Set (WithLp 2 (E × E))) :=
  ContinuousLinearMap.isClosed_ker (doubleSnd 𝕜 E)

variable {𝕜 E}

/-- The graph of a bounded operator, as a subspace of the orthogonal double. -/
noncomputable def graphSubmodule (T : E →L[𝕜] E) : Submodule 𝕜 (WithLp 2 (E × E)) :=
  LinearMap.ker
    ((doubleSnd 𝕜 E - T.comp (doubleFst 𝕜 E) : WithLp 2 (E × E) →L[𝕜] E)
      : WithLp 2 (E × E) →ₗ[𝕜] E)

theorem mem_graphSubmodule {T : E →L[𝕜] E} {v : WithLp 2 (E × E)} :
    v ∈ graphSubmodule T ↔ doubleSnd 𝕜 E v = T (doubleFst 𝕜 E v) := by
  constructor
  · intro hv
    have : doubleSnd 𝕜 E v - T (doubleFst 𝕜 E v) = 0 := hv
    linear_combination (norm := module) this
  · intro hv
    show doubleSnd 𝕜 E v - T (doubleFst 𝕜 E v) = 0
    rw [hv, sub_self]

theorem isClosed_graphSubmodule (T : E →L[𝕜] E) :
    IsClosed ((graphSubmodule T : Submodule 𝕜 (WithLp 2 (E × E))) : Set (WithLp 2 (E × E))) :=
  ContinuousLinearMap.isClosed_ker _

/-- **The sum of the first summand and a graph is a preimage of the range.**  A point of the
double lies in `firstSummand + graph T` exactly when its second coordinate is in `range T`. -/
theorem firstSummand_sup_graphSubmodule (T : E →L[𝕜] E) :
    (firstSummand 𝕜 E ⊔ graphSubmodule T : Submodule 𝕜 (WithLp 2 (E × E)))
      = Submodule.comap ((doubleSnd 𝕜 E : WithLp 2 (E × E) →L[𝕜] E)
          : WithLp 2 (E × E) →ₗ[𝕜] E) (LinearMap.range (T : E →ₗ[𝕜] E)) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro v hv
      have hv0 : doubleSnd 𝕜 E v = 0 := hv
      exact ⟨0, by simp [hv0]⟩
    · intro v hv
      exact ⟨doubleFst 𝕜 E v, (mem_graphSubmodule.mp hv).symm⟩
  · intro v hv
    obtain ⟨b, hb⟩ : ∃ b, T b = doubleSnd 𝕜 E v := hv
    refine Submodule.mem_sup.mpr
      ⟨v - WithLp.toLp 2 (b, T b), ?_, WithLp.toLp 2 (b, T b), ?_, by abel⟩
    · have hsub : doubleSnd 𝕜 E (v - WithLp.toLp 2 (b, T b)) = doubleSnd 𝕜 E v - T b :=
        map_sub _ _ _
      rw [mem_firstSummand, hsub, hb, sub_self]
    · exact mem_graphSubmodule.mpr rfl

/-- **Non-closed range gives a non-closed sum of closed subspaces.** -/
theorem not_isClosed_firstSummand_sup_graphSubmodule {T : E →L[𝕜] E}
    (hT : ¬ IsClosed (Set.range T)) :
    ¬ IsClosed ((firstSummand 𝕜 E ⊔ graphSubmodule T : Submodule 𝕜 (WithLp 2 (E × E)))
      : Set (WithLp 2 (E × E))) := by
  intro hclosed
  refine hT ?_
  have hpre : Set.range T = (doubleInr 𝕜 E) ⁻¹'
      ((firstSummand 𝕜 E ⊔ graphSubmodule T : Submodule 𝕜 (WithLp 2 (E × E)))
        : Set (WithLp 2 (E × E))) := by
    ext y
    rw [Set.mem_preimage, SetLike.mem_coe, firstSummand_sup_graphSubmodule]
    simp [Submodule.mem_comap, LinearMap.mem_range, Set.mem_range]
  rw [hpre]
  exact hclosed.preimage (doubleInr 𝕜 E).continuous

end OrthogonalDouble

section DecayDiagonal

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The `i`-th block of the decaying diagonal: multiplication by `(i+1)⁻¹`. -/
noncomputable def decayBlock (i : ℕ) : 𝕜 →L[𝕜] 𝕜 :=
  (((i : 𝕜) + 1)⁻¹) • ContinuousLinearMap.id 𝕜 𝕜

theorem norm_decayBlock_coeff (i : ℕ) : ‖((i : 𝕜) + 1)‖ = (i : ℝ) + 1 := by
  have : ((i : 𝕜) + 1) = ((i + 1 : ℕ) : 𝕜) := by push_cast; ring
  rw [this, RCLike.norm_natCast]
  push_cast
  ring

theorem decayBlock_coeff_ne_zero (i : ℕ) : ((i : 𝕜) + 1) ≠ 0 := by
  intro h
  have := norm_decayBlock_coeff 𝕜 i
  rw [h, norm_zero] at this
  have : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  linarith [this]

@[simp] theorem decayBlock_apply (i : ℕ) (x : 𝕜) :
    decayBlock 𝕜 i x = ((i : 𝕜) + 1)⁻¹ * x := rfl

theorem norm_decayBlock_le (i : ℕ) : ‖decayBlock 𝕜 i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [decayBlock_apply, norm_mul, norm_inv, norm_decayBlock_coeff, one_mul]
  have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have h2 : ((i : ℝ) + 1)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    linarith [Nat.cast_nonneg (α := ℝ) i]
  nlinarith [norm_nonneg x]

theorem decayBlock_injective (i : ℕ) : Function.Injective (decayBlock 𝕜 i) := by
  intro x y hxy
  rw [decayBlock_apply, decayBlock_apply] at hxy
  exact mul_left_cancel₀ (inv_ne_zero (decayBlock_coeff_ne_zero 𝕜 i)) hxy

theorem decayBlock_surjective (i : ℕ) : Function.Surjective (decayBlock 𝕜 i) := by
  intro y
  refine ⟨((i : 𝕜) + 1) * y, ?_⟩
  rw [decayBlock_apply, ← mul_assoc, inv_mul_cancel₀ (decayBlock_coeff_ne_zero 𝕜 i), one_mul]

theorem decayBlock_null (ε : ℝ) (hε : 0 < ε) :
    ∃ (i : ℕ) (v : 𝕜), ‖v‖ = 1 ∧ ‖decayBlock 𝕜 i v‖ < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n, 1, norm_one, ?_⟩
  rw [decayBlock_apply, mul_one, norm_inv, norm_decayBlock_coeff]
  rw [one_div] at hn
  exact hn

/-- **The decaying diagonal on `ℓ²(ℕ; 𝕜)`.**  It is injective with dense range, but the range is
not closed. -/
noncomputable def decayOperator :
    lp (fun _ : ℕ => 𝕜) 2 →L[𝕜] lp (fun _ : ℕ => 𝕜) 2 :=
  blockOperator (decayBlock 𝕜) zero_le_one (norm_decayBlock_le 𝕜)

theorem not_isClosed_range_decayOperator : ¬ IsClosed (Set.range (decayOperator 𝕜)) :=
  not_isClosed_range_blockOperator (decayBlock 𝕜) zero_le_one (norm_decayBlock_le 𝕜)
    (decayBlock_injective 𝕜) (decayBlock_surjective 𝕜) (decayBlock_null 𝕜)

end DecayDiagonal

section Countermodel

set_option synthInstance.maxHeartbeats 1000000

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The countermodel Hilbert space: two orthogonal copies of `ℓ²(ℕ; 𝕜)`. -/
abbrev CounterSpace :=
  WithLp 2 (lp (fun _ : ℕ => 𝕜) 2 × lp (fun _ : ℕ => 𝕜) 2)

/-- The first summand of the countermodel. -/
noncomputable def counterFirst : Submodule 𝕜 (CounterSpace 𝕜) :=
  firstSummand 𝕜 (lp (fun _ : ℕ => 𝕜) 2)

/-- The graph of the decaying diagonal inside the countermodel. -/
noncomputable def counterGraph : Submodule 𝕜 (CounterSpace 𝕜) :=
  graphSubmodule (decayOperator 𝕜)

theorem isClosed_counterFirst :
    IsClosed ((counterFirst 𝕜 : Submodule 𝕜 (CounterSpace 𝕜)) : Set (CounterSpace 𝕜)) :=
  isClosed_firstSummand 𝕜 _

theorem isClosed_counterGraph :
    IsClosed ((counterGraph 𝕜 : Submodule 𝕜 (CounterSpace 𝕜)) : Set (CounterSpace 𝕜)) :=
  isClosed_graphSubmodule _

/-- **Two closed subspaces with non-closed sum.** -/
theorem not_isClosed_counterFirst_sup_counterGraph :
    ¬ IsClosed ((counterFirst 𝕜 ⊔ counterGraph 𝕜 : Submodule 𝕜 (CounterSpace 𝕜))
      : Set (CounterSpace 𝕜)) :=
  not_isClosed_firstSummand_sup_graphSubmodule (not_isClosed_range_decayOperator 𝕜)

/-- **Terminal closedness does not imply global formation properness.**  The inclusion of
`counterFirst` and the orthogonal projection onto the complement of `counterGraph` both have
closed range, yet their composite does not; appending the zero map makes the total range closed
while this middle prefix stays non-closed. -/
theorem counter_terminal_closedness_not_global_properness :
    ¬ IsClosed ((LinearMap.range
        (((((counterGraph 𝕜)ᗮ).starProjection : CounterSpace 𝕜 →L[𝕜] CounterSpace 𝕜).comp
          (counterFirst 𝕜).subtypeL) : counterFirst 𝕜 →ₗ[𝕜] CounterSpace 𝕜)
        : Submodule 𝕜 (CounterSpace 𝕜)) : Set (CounterSpace 𝕜))
      ∧ IsClosed ((LinearMap.range
        ((((0 : CounterSpace 𝕜 →L[𝕜] CounterSpace 𝕜)).comp
          ((((counterGraph 𝕜)ᗮ).starProjection : CounterSpace 𝕜 →L[𝕜] CounterSpace 𝕜).comp
            (counterFirst 𝕜).subtypeL)) : counterFirst 𝕜 →ₗ[𝕜] CounterSpace 𝕜)
        : Submodule 𝕜 (CounterSpace 𝕜)) : Set (CounterSpace 𝕜)) :=
  terminal_closedness_not_global_properness (isClosed_counterGraph 𝕜)
    (not_isClosed_counterFirst_sup_counterGraph 𝕜)

end Countermodel

end GaloisForLFunctions.HTGeometry
