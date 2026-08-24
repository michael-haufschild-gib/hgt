import GaloisForLFunctions.HTGeometry.StokesEnhancedEpigraphConvolution

/-!
# Proper fiberwise addition on exponential epigraphs

Topological properness needed before constructing proper-support convolution of exponential
objects. This file proves only a support-level theorem; it does not construct sheaf tensor products,
derived direct images, enhanced sheaves, or irregular Riemann--Hilbert correspondence.
-/

namespace GaloisForLFunctions.IrregularStokes.ProperEpigraphAddition

open EnhancedEpigraph

variable {X : Type*} [TopologicalSpace X]

/-- Pairs of points over one base point in two exponential epigraphs. -/
def exponentialEpigraphPair (φ ψ : X → ℝ) : Set (X × (ℝ × ℝ)) :=
  {p | 0 ≤ p.2.1 + φ p.1 ∧ 0 ≤ p.2.2 + ψ p.1}

/-- Fiberwise addition restricted to a pair of exponential epigraphs. -/
def epigraphFiberwiseAddition (φ ψ : X → ℝ) :
    exponentialEpigraphPair φ ψ →
      exponentialEpigraph (fun x => φ x + ψ x) :=
  fun p => ⟨(p.1.1, p.1.2.1 + p.1.2.2), by
    change 0 ≤ (p.1.2.1 + p.1.2.2) + (φ p.1.1 + ψ p.1.1)
    rcases p.2 with ⟨hφ, hψ⟩
    linarith⟩

/-- Slack coordinates identify an exponential epigraph with a nonnegative half-line bundle. -/
noncomputable def exponentialEpigraphSlackHomeomorph (φ : X → ℝ) (hφ : Continuous φ) :
    exponentialEpigraph φ ≃ₜ X × NNReal where
  toFun p := (p.1.1, ⟨p.1.2 + φ p.1.1, p.2⟩)
  invFun p := ⟨(p.1, (p.2 : ℝ) - φ p.1), by simp⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      change (p.1.2 + φ p.1.1) - φ p.1.1 = p.1.2
      ring
  right_inv p := by
    apply Prod.ext
    · rfl
    · dsimp
      apply NNReal.eq
      change (p.2 : ℝ) - φ p.1 + φ p.1 = p.2
      ring
  continuous_toFun := by
    apply Continuous.prodMk continuous_subtype_val.fst
    exact Continuous.subtype_mk
      (continuous_subtype_val.snd.add (hφ.comp continuous_subtype_val.fst))
      (fun p => p.2)
  continuous_invFun := by
    exact Continuous.subtype_mk
      (Continuous.prodMk continuous_fst
        (NNReal.continuous_coe.comp continuous_snd |>.sub (hφ.comp continuous_fst)))
      (fun _ => by simp)

/-- Slack coordinates for a pair of exponential epigraphs over the same base. -/
noncomputable def exponentialEpigraphPairSlackHomeomorph (φ ψ : X → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    exponentialEpigraphPair φ ψ ≃ₜ X × (NNReal × NNReal) where
  toFun p :=
    (p.1.1,
      (⟨p.1.2.1 + φ p.1.1, p.2.1⟩,
       ⟨p.1.2.2 + ψ p.1.1, p.2.2⟩))
  invFun p :=
    ⟨(p.1, ((p.2.1 : ℝ) - φ p.1, (p.2.2 : ℝ) - ψ p.1)), by
      constructor <;> simp⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · dsimp
        change (p.1.2.1 + φ p.1.1) - φ p.1.1 = p.1.2.1
        ring
      · dsimp
        change (p.1.2.2 + ψ p.1.1) - ψ p.1.1 = p.1.2.2
        ring
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · dsimp
        apply NNReal.eq
        change (p.2.1 : ℝ) - φ p.1 + φ p.1 = p.2.1
        ring
      · dsimp
        apply NNReal.eq
        change (p.2.2 : ℝ) - ψ p.1 + ψ p.1 = p.2.2
        ring
  continuous_toFun := by
    apply Continuous.prodMk continuous_subtype_val.fst
    apply Continuous.prodMk
    · exact Continuous.subtype_mk
        (continuous_subtype_val.snd.fst.add
          (hφ.comp continuous_subtype_val.fst))
        (fun p => p.2.1)
    · exact Continuous.subtype_mk
        (continuous_subtype_val.snd.snd.add
          (hψ.comp continuous_subtype_val.fst))
        (fun p => p.2.2)
  continuous_invFun := by
    exact Continuous.subtype_mk
      (Continuous.prodMk continuous_fst
        (Continuous.prodMk
          ((NNReal.continuous_coe.comp continuous_snd.fst).sub
            (hφ.comp continuous_fst))
          ((NNReal.continuous_coe.comp continuous_snd.snd).sub
            (hψ.comp continuous_fst))))
      (fun _ => by constructor <;> simp)

/-- Addition of two nonnegative real numbers is proper. -/
theorem nnrealAdd_isProperMap :
    IsProperMap (fun p : NNReal × NNReal => p.1 + p.2) := by
  rw [isProperMap_iff_isCompact_preimage]
  constructor
  · fun_prop
  · intro K hK
    rw [Metric.isCompact_iff_isClosed_bounded]
    constructor
    · exact hK.isClosed.preimage (by fun_prop)
    · obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
      rw [Metric.isBounded_iff_subset_closedBall (0, 0)]
      refine ⟨r, ?_⟩
      intro p hp
      have hsum := hr hp
      change dist (p.1 + p.2) 0 ≤ r at hsum
      change max (dist p.1 0) (dist p.2 0) ≤ r
      simp only [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg,
        NNReal.coe_nonneg] at hsum ⊢
      exact max_le (le_trans (self_le_add_right p.1 p.2) hsum)
        (le_trans (self_le_add_left p.2 p.1) hsum)

/-- Fiberwise nonnegative addition over an arbitrary base. -/
def baseNNRealAddition : X × (NNReal × NNReal) → X × NNReal :=
  Prod.map id (fun p : NNReal × NNReal => p.1 + p.2)

/-- Fiberwise nonnegative addition over an arbitrary base is proper. -/
theorem baseNNRealAddition_isProperMap : IsProperMap (baseNNRealAddition (X := X)) :=
  isProperMap_id.prodMap nnrealAdd_isProperMap

/-- Under slack coordinates, epigraph addition is ordinary nonnegative addition. -/
theorem epigraphFiberwiseAddition_slack_commutes (φ ψ : X → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    exponentialEpigraphSlackHomeomorph (fun x => φ x + ψ x) (hφ.add hψ) ∘
        epigraphFiberwiseAddition φ ψ =
      (fun p : X × (NNReal × NNReal) => (p.1, p.2.1 + p.2.2)) ∘
        exponentialEpigraphPairSlackHomeomorph φ ψ hφ hψ := by
  funext p
  apply Prod.ext
  · rfl
  · apply NNReal.eq
    change (p.1.2.1 + p.1.2.2) + (φ p.1.1 + ψ p.1.1) =
      (p.1.2.1 + φ p.1.1) + (p.1.2.2 + ψ p.1.1)
    ring

/-- Fiberwise addition on closed exponential epigraphs is proper. -/
theorem epigraphFiberwiseAddition_isProperMap (φ ψ : X → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    IsProperMap (epigraphFiberwiseAddition φ ψ) := by
  let sourceHomeomorph := exponentialEpigraphPairSlackHomeomorph φ ψ hφ hψ
  let targetHomeomorph :=
    exponentialEpigraphSlackHomeomorph (fun x => φ x + ψ x) (hφ.add hψ)
  have hcomposed : IsProperMap (targetHomeomorph ∘ epigraphFiberwiseAddition φ ψ) := by
    rw [show targetHomeomorph ∘ epigraphFiberwiseAddition φ ψ =
      (fun p : X × (NNReal × NNReal) => (p.1, p.2.1 + p.2.2)) ∘
        sourceHomeomorph by
      simpa [sourceHomeomorph, targetHomeomorph] using
        epigraphFiberwiseAddition_slack_commutes φ ψ hφ hψ]
    exact baseNNRealAddition_isProperMap.comp sourceHomeomorph.isProperMap
  have hfactor : epigraphFiberwiseAddition φ ψ =
      targetHomeomorph.symm ∘ (targetHomeomorph ∘ epigraphFiberwiseAddition φ ψ) := by
    funext p
    simp
  rw [hfactor]
  exact targetHomeomorph.symm.isProperMap.comp hcomposed

omit [TopologicalSpace X] in
/-- Fiberwise addition on closed exponential epigraphs is surjective. -/
theorem epigraphFiberwiseAddition_surjective (φ ψ : X → ℝ) :
    Function.Surjective (epigraphFiberwiseAddition φ ψ) := by
  intro p
  refine ⟨⟨(p.1.1, (p.1.2 + ψ p.1.1, -ψ p.1.1)), ?_⟩, ?_⟩
  · constructor
    · change 0 ≤ (p.1.2 + ψ p.1.1) + φ p.1.1
      have hp := p.2
      change 0 ≤ p.1.2 + (φ p.1.1 + ψ p.1.1) at hp
      linarith
    · simp
  · apply Subtype.ext
    ext <;> simp [epigraphFiberwiseAddition]

end GaloisForLFunctions.IrregularStokes.ProperEpigraphAddition
