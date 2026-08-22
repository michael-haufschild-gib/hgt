import GaloisForLFunctions.HTGeometry.ObserverJacobianActiveMinorGaussianLaw

/-!
# Full Gaussian observer tube law

This module transports the active-minor law back to the original rectangular Gaussian coefficient
space.  A canonical index equivalence splits all coefficients into the selected active block and
its inactive complement.  The split preserves product Gaussian measure exactly, and the original
observer becomes the sum of the active square map and an arbitrary inactive drift.

Consequently the Gram pseudodeterminant bound controls tubes for the original `N` independent
Gaussian coefficients, not merely an abstract conditioned coordinate model.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The ordered active row enumeration as an equivalence onto the selected row subtype. -/
def observerActiveIndexEquiv {N v : ℕ}
    (s : Set.powersetCard (Fin N) v) :
    Fin v ≃ {a : Fin N // a ∈ (s : Finset (Fin N))} := by
  let e := Set.powersetCard.ofFinEmbEquiv.symm s
  let er : Fin v ≃ Set.range e := Equiv.ofInjective e e.injective
  have hrange : Set.range e = (s : Set (Fin N)) := by
    ext a
    exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s a
  exact er.trans (Equiv.setCongr hrange)

theorem observerActiveIndexEquiv_apply {N v : ℕ}
    (s : Set.powersetCard (Fin N) v) (j : Fin v) :
    ((observerActiveIndexEquiv s j : {a : Fin N //
      a ∈ (s : Finset (Fin N))}) : Fin N) =
      Set.powersetCard.ofFinEmbEquiv.symm s j := by
  rfl

/-- Row indices outside the selected active block. -/
abbrev observerInactiveIndex {N v : ℕ}
    (s : Set.powersetCard (Fin N) v) :=
  {a : Fin N // a ∉ (s : Finset (Fin N))}

/-- Disjoint union of inactive and ordered active indices is the original row index type. -/
def observerSplitIndexEquiv {N v : ℕ}
    (s : Set.powersetCard (Fin N) v) :
    observerInactiveIndex s ⊕ Fin v ≃ Fin N :=
  (Equiv.sumComm (observerInactiveIndex s) (Fin v)).trans
    ((Equiv.sumCongr (observerActiveIndexEquiv s)
      (Equiv.refl (observerInactiveIndex s))).trans
        (Equiv.sumCompl (fun a : Fin N => a ∈ (s : Finset (Fin N)))))

/-- Measurable decomposition of the original coefficient vector into inactive and active blocks. -/
def observerCoefficientSplit {N v : ℕ}
    (s : Set.powersetCard (Fin N) v) :
    (Fin N → ℝ) ≃ᵐ
      ((observerInactiveIndex s → ℝ) × (Fin v → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ)
      (observerSplitIndexEquiv s)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : observerInactiveIndex s ⊕ Fin v => ℝ))

/-- Coefficient splitting preserves the full product standard Gaussian law exactly. -/
theorem observerCoefficientSplit_measurePreserving {N v : ℕ}
    (s : Set.powersetCard (Fin N) v) :
    MeasurePreserving (observerCoefficientSplit s)
      (Measure.pi fun _ : Fin N => gaussianReal 0 1)
      ((Measure.pi fun _ : observerInactiveIndex s => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin v => gaussianReal 0 1)) := by
  have hindexForward := MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : Fin N => gaussianReal 0 1) (observerSplitIndexEquiv s)
  have hindex := MeasureTheory.MeasurePreserving.symm
    (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ)
      (observerSplitIndexEquiv s)) hindexForward
  have hsum := MeasureTheory.measurePreserving_sumPiEquivProdPi
    (fun _ : observerInactiveIndex s ⊕ Fin v => gaussianReal 0 1)
  exact hsum.comp hindex

@[simp] theorem observerCoefficientSplit_inactive_apply {N v : ℕ}
    (s : Set.powersetCard (Fin N) v) (x : Fin N → ℝ)
    (a : observerInactiveIndex s) :
    (observerCoefficientSplit s x).1 a = x a := by
  rfl

@[simp] theorem observerCoefficientSplit_active_apply {N v : ℕ}
    (s : Set.powersetCard (Fin N) v) (x : Fin N → ℝ) (j : Fin v) :
    (observerCoefficientSplit s x).2 j =
      x (Set.powersetCard.ofFinEmbEquiv.symm s j) := by
  rfl

/-- Full rectangular observer on the original coefficient vector. -/
def observerLinearMap {N v : ℕ} (J : Fin N → Fin v → ℝ) :
    (Fin N → ℝ) →ₗ[ℝ] (Fin v → ℝ) :=
  Matrix.toLin' (Matrix.of fun i a => J a i)

/-- Contribution of coefficients outside one selected active block. -/
def observerInactiveMap {N v : ℕ} (J : Fin N → Fin v → ℝ)
    (s : Set.powersetCard (Fin N) v) :
    ((observerInactiveIndex s → ℝ) →ₗ[ℝ] (Fin v → ℝ)) :=
  Matrix.toLin' (Matrix.of fun i a => J a i)

/-- The original rectangular action splits exactly into inactive drift plus active square action. -/
theorem observerLinearMap_split {N v : ℕ} (J : Fin N → Fin v → ℝ)
    (s : Set.powersetCard (Fin N) v) (x : Fin N → ℝ) :
    observerInactiveMap J s (observerCoefficientSplit s x).1 +
        observerActiveMap J s (observerCoefficientSplit s x).2 =
      observerLinearMap J x := by
  ext i
  simp only [observerInactiveMap, observerActiveMap, observerActiveMatrix,
    observerLinearMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Pi.add_apply]
  simp_rw [observerCoefficientSplit_inactive_apply,
    observerCoefficientSplit_active_apply]
  change (∑ a : observerInactiveIndex s, J a i * x a) +
      (∑ j : Fin v,
        J (Set.powersetCard.ofFinEmbEquiv.symm s j) i *
          x (Set.powersetCard.ofFinEmbEquiv.symm s j)) =
    ∑ a : Fin N, J a i * x a
  simp_rw [← observerActiveIndexEquiv_apply s]
  rw [Equiv.sum_comp (observerActiveIndexEquiv s)
    (fun a : {a : Fin N // a ∈ (s : Finset (Fin N))} => J a i * x a)]
  rw [add_comm]
  let f : Fin N → ℝ := fun a => J a i * x a
  have hactive : (∑ a : {a : Fin N // a ∈ (s : Finset (Fin N))}, f a) =
      ∑ a ∈ (s : Finset (Fin N)), f a := by
    change ∑ a ∈ (s : Finset (Fin N)).attach, f a = _
    exact Finset.sum_attach _ _
  have hinactive : (∑ a : observerInactiveIndex s, f a) =
      ∑ a ∈ Finset.univ \ (s : Finset (Fin N)), f a := by
    exact (Finset.sum_subtype (Finset.univ \ (s : Finset (Fin N)))
      (fun a => by simp) f).symm
  rw [hactive, hinactive]
  rw [add_comm]
  rw [Finset.sum_sdiff (f := f) (Finset.subset_univ (s : Finset (Fin N)))]

/-- Pullback box tube for the original rectangular observer. -/
def gaussianObserverBoxTube {N v : ℕ} (J : Fin N → Fin v → ℝ)
    (center : Fin v → ℝ) (radius : ℝ) : Set (Fin N → ℝ) :=
  {x | observerLinearMap J x ∈ Set.univ.pi fun i =>
    Set.Icc (center i - radius) (center i + radius)}

theorem observerCoefficientSplit_preimage_conditionedTube {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (s : Set.powersetCard (Fin N) v)
    (center : Fin v → ℝ) (radius : ℝ) :
    observerCoefficientSplit s ⁻¹'
      gaussianConditionedLinearBoxTube (observerActiveMap J s)
        (observerInactiveMap J s) center radius =
      gaussianObserverBoxTube J center radius := by
  ext x
  simp only [mem_preimage, gaussianConditionedLinearBoxTube,
    gaussianObserverBoxTube, mem_setOf_eq]
  rw [add_comm, observerLinearMap_split]

/-- Every selected active block gives a valid full-coefficient box-tube budget. -/
theorem measure_gaussianObserverBoxTube_le_activeBudget {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (s : Set.powersetCard (Fin N) v)
    (center : Fin v → ℝ) (radius : ℝ) :
    (Measure.pi fun _ : Fin N => gaussianReal 0 1)
        (gaussianObserverBoxTube J center radius) ≤
      gaussianLinearBoxTubeBudget (observerActiveMap J s) radius := by
  have hmp := observerCoefficientSplit_measurePreserving s
  rw [← observerCoefficientSplit_preimage_conditionedTube J s center radius]
  rw [← MeasurableEquiv.map_apply (observerCoefficientSplit s), hmp.map_eq]
  exact measure_gaussianConditionedLinearBoxTube_le
    (observerActiveMap J s) (observerInactiveMap J s) center radius

/-- Approximate sup-norm tube for the original rectangular observer. -/
def gaussianObserverNormTube {N v : ℕ} (J : Fin N → Fin v → ℝ)
    (center : Fin v → ℝ) (radius : ℝ) : Set (Fin N → ℝ) :=
  {x | ‖observerLinearMap J x - center‖ ≤ radius}

theorem observerCoefficientSplit_preimage_conditionedNormTube {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (s : Set.powersetCard (Fin N) v)
    (center : Fin v → ℝ) (radius : ℝ) :
    observerCoefficientSplit s ⁻¹'
      gaussianConditionedObserverNormTube (observerActiveMap J s)
        (observerInactiveMap J s) center radius =
      gaussianObserverNormTube J center radius := by
  ext x
  simp only [mem_preimage, gaussianConditionedObserverNormTube,
    gaussianObserverNormTube, mem_setOf_eq]
  rw [add_comm, observerLinearMap_split]

/-- Every selected active block gives a valid full-coefficient approximate-tube budget. -/
theorem measure_gaussianObserverNormTube_le_activeBudget {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (s : Set.powersetCard (Fin N) v)
    (center : Fin v → ℝ) (radius : ℝ) :
    (Measure.pi fun _ : Fin N => gaussianReal 0 1)
        (gaussianObserverNormTube J center radius) ≤
      gaussianLinearBoxTubeBudget (observerActiveMap J s) radius := by
  have hmp := observerCoefficientSplit_measurePreserving s
  rw [← observerCoefficientSplit_preimage_conditionedNormTube J s center radius]
  rw [← MeasurableEquiv.map_apply (observerCoefficientSplit s), hmp.map_eq]
  exact measure_gaussianConditionedObserverNormTube_le
    (observerActiveMap J s) (observerInactiveMap J s) center radius

/-- **Full rectangular Gaussian observer law.**  For the original `N` independent Gaussian
coefficients, unconditionally either the observer Gram determinant vanishes, or one canonical
active block witnesses the sharp Cauchy--Binet lower bound and controls every translated box and
approximate sup-norm tube by the Gram pseudodeterminant budget. -/
theorem observerJacobianGram_fullGaussianTube_dichotomy {N v : ℕ}
    (J : Fin N → Fin v → ℝ) :
    (observerJacobianGram J).det = 0 ∨
      ∃ s : Set.powersetCard (Fin N) v,
        Real.sqrt ((observerJacobianGram J).det / (N.choose v : ℝ)) ≤
            |observerActiveMinor J s| ∧
        ∀ (center : Fin v → ℝ) (radius : ℝ),
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)
              (gaussianObserverBoxTube J center radius) ≤
                observerJacobianGramTubeBudget J radius ∧
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)
              (gaussianObserverNormTube J center radius) ≤
                observerJacobianGramTubeBudget J radius := by
  by_cases hdet : (observerJacobianGram J).det = 0
  · exact Or.inl hdet
  · right
    have hvN : v ≤ N := by
      by_contra h
      exact hdet (det_observerJacobianGram_zero_of_lt (by omega) J)
    obtain ⟨s, hs⟩ := exists_activeMinor_average_of_le hvN J
    have hcpos : (0 : ℝ) < N.choose v := by
      exact_mod_cast Nat.choose_pos hvN
    have hsqrt : Real.sqrt
        ((observerJacobianGram J).det / (N.choose v : ℝ)) ≤
        |observerActiveMinor J s| := by
      apply (Real.sqrt_le_iff).2
      refine ⟨abs_nonneg _, ?_⟩
      rw [sq_abs]
      exact (div_le_iff₀ hcpos).2 (by simpa [mul_comm] using hs)
    have hminor : observerActiveMinor J s ≠ 0 := by
      intro hm
      rw [hm] at hs
      norm_num at hs
      exact hdet (le_antisymm hs (det_observerJacobianGram_nonneg J))
    refine ⟨s, hsqrt, fun center radius => ?_⟩
    have hinv := inv_abs_activeMinor_le_sqrt_choose_div_det J hdet s hs
    have hbox := measure_gaussianObserverBoxTube_le_activeBudget
      J s center radius
    have hnorm := measure_gaussianObserverNormTube_le_activeBudget
      J s center radius
    rw [gaussianLinearBoxTubeBudget, activeObserverPseudodeterminant,
      if_neg (abs_ne_zero.mpr (by simpa [det_observerActiveMap] using hminor))]
      at hbox hnorm
    rw [observerJacobianGramTubeBudget, if_neg hdet]
    constructor
    · refine hbox.trans ?_
      gcongr
      rw [det_observerActiveMap]
      exact hinv
    · refine hnorm.trans ?_
      gcongr
      rw [det_observerActiveMap]
      exact hinv

end GaloisForLFunctions.HTGeometry
