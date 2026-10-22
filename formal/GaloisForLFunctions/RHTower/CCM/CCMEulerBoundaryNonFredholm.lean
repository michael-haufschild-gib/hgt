import GaloisForLFunctions.RHTower.CCM.CCMEulerBoundaryKernelShell
import GaloisForLFunctions.RHTower.SoninBurnolConductorConcrete
import GaloisForLFunctions.RHTower.SoninEulerTripleShellOverlap
import GaloisForLFunctions.RHTower.CCM.CCMArithmeticPrimeFredholmOrientation

/-!
# Infinite shell kernels obstruct Fredholm Euler transitions

Every active source-preserving transition loses an entire nondegenerate Fourier
shell, not a finite defect. The exact kernel-shell equivalence is the positive
survivor: it specifies the channel that any relative completion must retain.
-/

noncomputable section

open IsDedekindDomain

namespace RHTower

/-- Fourier reflection recovers the physical cutoff from the literal Fourier cutoff. -/
theorem evenFourierTransform_mul_cutoff_mul (a : ℝ) :
    evenFourierTransform * evenFourierCutoff a * evenFourierTransform =
      evenIndicatorCutoff a := by
  calc
    _ = (evenFourierTransform * evenFourierTransform) * evenIndicatorCutoff a *
        (evenFourierTransform * evenFourierTransform) := by
      rw [evenFourierCutoff_eq_reflectedCutoff]
      simp only [reflectedCutoff, mul_assoc]
    _ = _ := by rw [evenFourierTransform_mul_self, one_mul, mul_one]

/-- A nondegenerate Fourier shell is not compact, by the actual Fourier involution. -/
theorem not_isCompactOperator_evenFourierShellDiff (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    ¬ IsCompactOperator (evenFourierCutoff t - evenFourierCutoff s) := by
  intro h
  have hc : IsCompactOperator (evenFourierTransform *
      (evenFourierCutoff t - evenFourierCutoff s) * evenFourierTransform) :=
    (h.comp_clm evenFourierTransform).clm_comp evenFourierTransform
  rw [mul_sub, sub_mul, evenFourierTransform_mul_cutoff_mul,
    evenFourierTransform_mul_cutoff_mul] at hc
  exact not_isCompactOperator_evenIndicatorShellDiff s t hs hst hc

/-- Every nondegenerate actual Fourier shell is infinite dimensional. -/
theorem not_finiteDimensional_ccmEulerBoundaryAnnulus_empty
    (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    ¬ FiniteDimensional ℂ (ccmEulerBoundaryAnnulus ∅ s t) := by
  intro hfin
  letI := hfin
  let B := evenFourierCutoff t - evenFourierCutoff s
  have hmem : ∀ u : evenSubspace, B u ∈ ccmEulerBoundaryAnnulus ∅ s t := by
    intro u
    rw [ccmEulerBoundaryAnnulus_eq_range ∅ s t (by
      simpa only [ccmFiniteEulerCarrierScale, Finset.prod_empty, div_one] using hst.le)]
    simpa only [ccmFiniteEulerCarrierScale, Finset.prod_empty, div_one] using
      (show B u ∈ B.range from ⟨u, rfl⟩)
  have hc : IsCompactOperator (B.codRestrict (ccmEulerBoundaryAnnulus ∅ s t) hmem) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact not_isCompactOperator_evenFourierShellDiff s t hs hst
    (hc.clm_comp (ccmEulerBoundaryAnnulus ∅ s t).subtypeL)

/-- Prime insertion above the active edge has an infinite-dimensional actual boundary kernel. -/
theorem not_finiteDimensional_ccmEulerBoundaryTransition_ker
    (S T : Finset (HeightOneSpectrum ℤ)) (hST : S ⊆ T) (b : ℝ) (hb : 0 < b)
    (hactive : max b (ccmFiniteEulerCarrierScale S) < ccmFiniteEulerCarrierScale T) :
    ¬ FiniteDimensional ℂ (ccmEulerBoundaryTransition S T hST b hb).ker := by
  intro hfin
  exact not_finiteDimensional_ccmEulerBoundaryAnnulus_empty _ _
    (hb.trans_le (le_max_left _ _)) hactive
    (@LinearEquiv.finiteDimensional ℂ
      (ccmEulerBoundaryTransition S T hST b hb).ker inferInstance
      (ccmEulerBoundaryTransition S T hST b hb).ker.addCommGroup
      (ccmEulerBoundaryTransition S T hST b hb).ker.module
      (ccmEulerBoundaryAnnulus ∅ (max b (ccmFiniteEulerCarrierScale S))
        (ccmFiniteEulerCarrierScale T))
      (ccmEulerBoundaryAnnulus ∅ (max b (ccmFiniteEulerCarrierScale S))
        (ccmFiniteEulerCarrierScale T)).addCommGroup
      (ccmEulerBoundaryAnnulus ∅ (max b (ccmFiniteEulerCarrierScale S))
        (ccmFiniteEulerCarrierScale T)).module
      (ccmEulerBoundaryKernelShellEquiv S T hST b hb).toLinearEquiv hfin)

/-- The full-domain source-preserving transition is not Fredholm in the active chamber. -/
theorem not_isFredholm_ccmEulerBoundaryTransition
    (S T : Finset (HeightOneSpectrum ℤ)) (hST : S ⊆ T) (b : ℝ) (hb : 0 < b)
    (hactive : max b (ccmFiniteEulerCarrierScale S) < ccmFiniteEulerCarrierScale T) :
    ¬ ((ccmEulerBoundaryTransition S T hST b hb).toLinearMap.toPMap ⊤).IsFredholm := by
  intro h
  have hf := h.finiteDimensional_kernel
  rw [kernel_toPMap_top] at hf
  exact not_finiteDimensional_ccmEulerBoundaryTransition_ker S T hST b hb hactive hf

/-- Genuine finite prime products are cofinally unbounded above every starting stage. -/
theorem exists_ccmFiniteEulerCarrierScale_above (S : Finset (HeightOneSpectrum ℤ)) (r : ℝ) :
    ∃ T : Finset (HeightOneSpectrum ℤ), S ⊆ T ∧ r < ccmFiniteEulerCarrierScale T := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt r
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
  let v : HeightOneSpectrum ℤ := Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp⟩
  refine ⟨insert v S, Finset.subset_insert v S, ?_⟩
  calc
    r < (p : ℝ) := hn.trans_le (by exact_mod_cast hnp)
    _ = ccmFiniteEulerCarrierScale {v} := by
      simp only [ccmFiniteEulerCarrierScale, Finset.prod_singleton, v,
        Equiv.apply_symm_apply]
    _ ≤ ccmFiniteEulerCarrierScale (insert v S) :=
      ccmFiniteEulerCarrierScale_mono (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self v S))

/-- No finite starting stage removes the non-Fredholm obstruction from all later transitions. -/
theorem exists_nonFredholm_ccmEulerBoundaryTransition
    (S : Finset (HeightOneSpectrum ℤ)) (b : ℝ) (hb : 0 < b) :
    ∃ T : Finset (HeightOneSpectrum ℤ), ∃ hST : S ⊆ T,
      ¬ ((ccmEulerBoundaryTransition S T hST b hb).toLinearMap.toPMap ⊤).IsFredholm := by
  obtain ⟨T, hST, hactive⟩ :=
    exists_ccmFiniteEulerCarrierScale_above S (max b (ccmFiniteEulerCarrierScale S))
  exact ⟨T, hST, not_isFredholm_ccmEulerBoundaryTransition S T hST b hb hactive⟩

end RHTower
