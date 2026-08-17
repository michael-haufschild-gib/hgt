import GaloisForLFunctions.HTGeometry.DivergenceCompactSupport

/-!
# The compactly supported divergence theorem in Euclidean coordinates

The Euclidean space of a finite index type is the coordinate space with a different norm, and the
identification is a continuous linear equivalence that preserves Lebesgue measure and carries the
coordinate basis to itself.  The compactly supported divergence theorem therefore transports
verbatim.

Stating it in the Euclidean space is what an argument on the unit sphere needs, since the sphere,
the radial variable and the polar decomposition all refer to the Euclidean norm.
-/

open MeasureTheory Metric Set WithLp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Euclidean

variable {n : ℕ}

/-- The divergence of a field on Euclidean space, in the coordinate basis. -/
def euclideanDivergence
    (V' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))))
    (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  ∑ i, V' x (EuclideanSpace.single i 1) i

/-- **The divergence theorem in Euclidean coordinates.**  A continuously differentiable field with
compact support has vanishing total divergence. -/
theorem integral_euclideanDivergence_eq_zero
    (V : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (V' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))))
    (hd : ∀ x, HasFDerivAt V (V' x) x)
    (hcont : Continuous (euclideanDivergence V'))
    (hsupp : HasCompactSupport V) :
    ∫ x, euclideanDivergence V' x = 0 := by
  classical
  set L : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
    EuclideanSpace.equiv (Fin (n + 1)) ℝ with hL
  -- the transported field and its derivative
  set W : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun y => L (V (L.symm y)) with hW
  set W' : (Fin (n + 1) → ℝ) → ((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) :=
    fun y => (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] (Fin (n + 1) → ℝ)).comp
      ((V' (L.symm y)).comp
        (L.symm : (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) with hW'
  have hdW : ∀ y, HasFDerivAt W (W' y) y := by
    intro y
    have h1 : HasFDerivAt (fun z : (Fin (n + 1) → ℝ) => L.symm z)
        (L.symm : (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) y :=
      (L.symm : (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).hasFDerivAt
    have h2 := (hd (L.symm y)).comp y h1
    have h3 := (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      (Fin (n + 1) → ℝ)).hasFDerivAt.comp y h2
    exact h3
  -- the divergences agree along the identification
  have hdiv : ∀ x : EuclideanSpace ℝ (Fin (n + 1)),
      divergence W' (L x) = euclideanDivergence V' x := by
    intro x
    rw [divergence, euclideanDivergence]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hsuppW : HasCompactSupport W := by
    refine HasCompactSupport.intro (hsupp.isCompact.image L.continuous) ?_
    intro y hy
    show L (V (L.symm y)) = 0
    have hx : V (L.symm y) = 0 := by
      refine image_eq_zero_of_notMem_tsupport ?_
      intro hmem
      exact hy ⟨L.symm y, hmem, by simp⟩
    rw [hx, map_zero]
  have hcontW : Continuous (divergence W') := by
    have : divergence W' = (euclideanDivergence V') ∘ L.symm := by
      funext y
      have := hdiv (L.symm y)
      rw [L.apply_symm_apply] at this
      exact this
    rw [this]
    exact hcont.comp L.symm.continuous
  have hflat := integral_divergence_eq_zero_of_hasCompactSupport W W' hdW hcontW hsuppW
  -- transfer the integral back
  have hmp : MeasurePreserving (⇑L) (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) volume :=
    PiLp.volume_preserving_ofLp (Fin (n + 1))
  have htrans : ∫ x : EuclideanSpace ℝ (Fin (n + 1)), euclideanDivergence V' x
      = ∫ y : Fin (n + 1) → ℝ, divergence W' y := by
    have hcomp := hmp.integral_comp L.toHomeomorph.measurableEmbedding (divergence W')
    rw [← hcomp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact (hdiv x).symm
  rw [htrans, hflat]

end Euclidean

end

end GaloisForLFunctions.HTGeometry
