import GaloisForLFunctions.RHTower.CompleteResolutionSourceEmbeddingReflectionLaw

/-!
# Label-blind observer rigidity for the complete Riemann source

The complete high-exponent resolution embeds the spectral right half-plane into the affine
mass-one hyperplane of a fixed `ℓ¹` source space.  This file classifies every bounded linear
consumer which does not distinguish the source labels.

Such a consumer factors uniquely through the norm-one source codiagonal.  It is therefore
constant on the entire spectral embedding and annihilates its zero-mass radical.  In particular,
off the critical line the canonical unsquared reflection displacement is nonzero but is invisible
to every bounded label-blind consumer.

This turns the need for retained source labels into an exact observer-classification theorem.
-/

open scoped ENNReal

namespace RHTower

noncomputable section

/-- A bounded consumer is label-blind when all unit source channels have the same image. -/
def SourceLabelBlind
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : CompleteResolutionSourceSpace →L[ℂ] F) : Prop :=
  ∀ i j : ℕ,
    T (lp.single (E := fun _ : ℕ => ℂ) 1 i 1) =
      T (lp.single (E := fun _ : ℕ => ℂ) 1 j 1)

private theorem span_sourceSingles_dense :
    (Submodule.span ℂ
      (Set.range fun i : ℕ =>
        lp.single (E := fun _ : ℕ => ℂ) 1 i (1 : ℂ))).topologicalClosure =
      ⊤ := by
  rw [Submodule.eq_top_iff']
  intro f
  set p : Submodule ℂ CompleteResolutionSourceSpace :=
    Submodule.span ℂ
      (Set.range fun i : ℕ =>
        lp.single (E := fun _ : ℕ => ℂ) 1 i (1 : ℂ)) with hp
  have hsum := lp.hasSum_single (E := fun _ : ℕ => ℂ) (p := 1)
    (by norm_num) f
  have hmem : ∀ s : Finset ℕ,
      (∑ i ∈ s,
        lp.single (E := fun _ : ℕ => ℂ) 1 i
          ((f : ∀ _ : ℕ, ℂ) i)) ∈ p := by
    intro s
    apply Submodule.sum_mem
    intro i _
    have hsingle :
        lp.single (E := fun _ : ℕ => ℂ) 1 i
            ((f : ∀ _ : ℕ, ℂ) i) =
          ((f : ∀ _ : ℕ, ℂ) i) •
            lp.single (E := fun _ : ℕ => ℂ) 1 i (1 : ℂ) := by
      rw [← lp.single_smul]
      congr 1
      simp
    rw [hsingle]
    exact Submodule.smul_mem _
      _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact mem_closure_of_tendsto hsum
    (Filter.Eventually.of_forall fun s => hmem s)

/-- The source codiagonal sends every unit channel to one. -/
@[simp] theorem sourceFusionCodiagonal_single_one (i : ℕ) :
    sourceFusionCodiagonal
        (lp.single (E := fun _ : ℕ => ℂ) 1 i 1) = 1 := by
  rw [sourceFusionCodiagonal, lp.tsumCLM_apply]
  simp

/-- **Bounded label-blind observer classification.**  Every bounded linear consumer which treats
all source labels equally factors through the norm-one codiagonal.  The factor is its value on
one unit channel. -/
theorem sourceLabelBlind_factorization
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : CompleteResolutionSourceSpace →L[ℂ] F)
    (hT : SourceLabelBlind T) :
    T =
      sourceFusionCodiagonal.smulRight
        (T (lp.single (E := fun _ : ℕ => ℂ) 1 0 1)) := by
  let c := T (lp.single (E := fun _ : ℕ => ℂ) 1 0 1)
  let D : CompleteResolutionSourceSpace →L[ℂ] F :=
    T - sourceFusionCodiagonal.smulRight c
  have hsingle :
      ∀ i : ℕ,
        lp.single (E := fun _ : ℕ => ℂ) 1 i 1 ∈ D.ker := by
    intro i
    change D (lp.single (E := fun _ : ℕ => ℂ) 1 i 1) = 0
    dsimp only [D]
    rw [sub_apply, ContinuousLinearMap.smulRight_apply,
      sourceFusionCodiagonal_single_one]
    change T (lp.single (E := fun _ : ℕ => ℂ) 1 i 1) - (1 : ℂ) • c = 0
    rw [hT i 0]
    simp [c]
  have hspan :
      Submodule.span ℂ
          (Set.range fun i : ℕ =>
            lp.single (E := fun _ : ℕ => ℂ) 1 i (1 : ℂ)) ≤
        D.ker :=
    Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact hsingle i)
  have hclosure :
      (Submodule.span ℂ
        (Set.range fun i : ℕ =>
          lp.single (E := fun _ : ℕ => ℂ) 1 i
            (1 : ℂ))).topologicalClosure ≤ D.ker :=
    Submodule.topologicalClosure_minimal
      _ hspan (ContinuousLinearMap.isClosed_ker D)
  have hD : D = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have hx : x ∈ D.ker := by
      have : x ∈
          (Submodule.span ℂ
            (Set.range fun i : ℕ =>
              lp.single (E := fun _ : ℕ => ℂ) 1 i
                (1 : ℂ))).topologicalClosure := by
        rw [span_sourceSingles_dense]
        trivial
      exact hclosure this
    exact hx
  change T = sourceFusionCodiagonal.smulRight c
  exact sub_eq_zero.mp hD

/-- Every bounded label-blind consumer annihilates the zero-mass radical. -/
theorem sourceLabelBlind_annihilates_radical
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : CompleteResolutionSourceSpace →L[ℂ] F)
    (hT : SourceLabelBlind T)
    (x : CompleteResolutionSourceSpace) :
    T (sourceFusionRadical x) = 0 := by
  rw [sourceLabelBlind_factorization T hT,
    ContinuousLinearMap.smulRight_apply,
    sourceFusionCodiagonal_radical, zero_smul]

/-- Label blindness is exactly annihilation of the zero-mass hyperplane. -/
theorem sourceLabelBlind_iff_annihilates_zeroMass
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : CompleteResolutionSourceSpace →L[ℂ] F) :
    SourceLabelBlind T ↔
      ∀ x : CompleteResolutionSourceSpace,
        sourceFusionCodiagonal x = 0 → T x = 0 := by
  constructor
  · intro hT x hx
    rw [sourceLabelBlind_factorization T hT,
      ContinuousLinearMap.smulRight_apply, hx, zero_smul]
  · intro hzero i j
    let ei : CompleteResolutionSourceSpace :=
      lp.single (E := fun _ : ℕ => ℂ) 1 i 1
    let ej : CompleteResolutionSourceSpace :=
      lp.single (E := fun _ : ℕ => ℂ) 1 j 1
    have hmass : sourceFusionCodiagonal (ei - ej) = 0 := by
      rw [map_sub]
      simp [ei, ej]
    have hdiff := hzero (ei - ej) hmass
    rw [map_sub, sub_eq_zero] at hdiff
    exact hdiff

/-- **Mass-fibre blindness law.**  Every bounded label-blind consumer is constant on every
affine fibre of the source codiagonal. -/
theorem sourceLabelBlind_eq_of_sameMass
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : CompleteResolutionSourceSpace →L[ℂ] F)
    (hT : SourceLabelBlind T)
    {x y : CompleteResolutionSourceSpace}
    (hmass : sourceFusionCodiagonal x = sourceFusionCodiagonal y) :
    T x = T y := by
  rw [sourceLabelBlind_factorization T hT,
    ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, hmass]

/-- Distinct points of one mass fibre have nonzero difference invisible to every bounded
label-blind consumer. -/
theorem sourceLabelBlind_nonzeroDifference_invisible
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : CompleteResolutionSourceSpace →L[ℂ] F)
    (hT : SourceLabelBlind T)
    {x y : CompleteResolutionSourceSpace}
    (hne : x ≠ y)
    (hmass : sourceFusionCodiagonal x = sourceFusionCodiagonal y) :
    x - y ≠ 0 ∧ T (x - y) = 0 := by
  refine ⟨sub_ne_zero.mpr hne, ?_⟩
  rw [map_sub, sourceLabelBlind_eq_of_sameMass T hT hmass, sub_self]

/-- A bounded label-blind consumer is constant on the complete spectral source embedding. -/
theorem sourceLabelBlind_constant_on_completeResolutionSourceEmbedding
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : CompleteResolutionSourceSpace →L[ℂ] F)
    (hT : SourceLabelBlind T)
    (K : ℕ) (s t : CompleteResolutionRightHalfPlane) :
    T (completeResolutionSourceEmbedding K s) =
      T (completeResolutionSourceEmbedding K t) := by
  rw [sourceLabelBlind_factorization T hT,
    ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply,
    sourceFusionCodiagonal_completeResolutionSourceEmbedding,
    sourceFusionCodiagonal_completeResolutionSourceEmbedding]

/-- **Complete-source blindness theorem.**  Off the critical line, the actual unsquared
reflection displacement is nonzero, but every bounded label-blind consumer sends it to zero. -/
theorem completeResolution_offlineReflectionDisplacement_labelBlind
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : CompleteResolutionSourceSpace →L[ℂ] F)
    (hT : SourceLabelBlind T)
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip)
    (hoff : s.1.re ≠ 1 / 2) :
    completeResolutionReflectionSourceDisplacement K s ≠ 0 ∧
      T (completeResolutionReflectionSourceDisplacement K s) = 0 := by
  refine ⟨(not_congr
      (completeResolutionReflectionSourceDisplacement_eq_zero_iff K s)).mpr
        hoff, ?_⟩
  rw [sourceLabelBlind_factorization T hT,
    ContinuousLinearMap.smulRight_apply,
    sourceFusionCodiagonal_completeResolutionReflectionSourceDisplacement,
    zero_smul]

end

end RHTower
