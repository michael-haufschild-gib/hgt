import GaloisForLFunctions.RHTower.SoninBurnolFiniteRankWardTrace
import GaloisForLFunctions.RHTower.SoninProlateCommutatorEnergy

/-!
# Faithful finite-rank Ward detection on the Sonin boundary

The diagonal finite-packet Ward form is a faithful cutoff-commutation detector.  For an orthogonal
cutoff and an arbitrary finite packet it is the sum of the two directional Hilbert--Schmidt boundary
energies.  For a self-adjoint packet those energies agree, giving exactly twice the one-way crossing
energy.  Real diagonal packets discharge self-adjointness, and the concrete even Fourier involution
reflects the Fourier-side Ward value to the physical Sonin crossing energy.

This is an operator identity, not an identification of the abstract polynomial torsion-seam witness
with the actual semilocal Sonin source action.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- **Two-corner commutator energy law.**  For an orthogonal cutoff, every Hilbert--Schmidt source
splits into two Hilbert--Schmidt boundary crossings, and the full commutator energy is their exact
sum.  No self-adjointness of the source is needed. -/
theorem hsNormSq_commutator_eq_boundary_sum_of_hilbertSchmidt
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (hX : IsHilbertSchmidt X) :
    hsNormSq (ccmCommutator X e) =
      hsNormSq (crossBoundary e X) + hsNormSq (upperBoundary e X) := by
  let L : H →L[ℂ] H := crossBoundary e X
  let U : H →L[ℂ] H := upperBoundary e X
  have hL : IsHilbertSchmidt L := by
    simpa only [L, crossBoundary, mul_assoc] using
      (hX.comp_right e).comp_left (1 - e)
  have hU : IsHilbertSchmidt U := by
    simpa only [U, upperBoundary, mul_assoc] using
      (hX.comp_right (1 - e)).comp_left e
  have hAdjL : adjoint L = upperBoundary e (adjoint X) := by
    dsimp only [L]
    unfold crossBoundary upperBoundary
    change adjoint (((1 - e) * X) ∘L e) = _
    rw [adjoint_comp]
    change adjoint e ∘L adjoint ((1 - e) ∘L X) = _
    rw [adjoint_comp, adjoint_one_sub heAdj, heAdj]
    rfl
  have hzero : upperBoundary e (adjoint X) * U = 0 := by
    simpa only [U] using upperBoundary_mul_upperBoundary e (adjoint X) X he
  have horth : hsInner L U = 0 := by
    have htrace : opTrace (adjoint L ∘L U) = hsInner L U := by
      simpa using opTrace_comp_eq_hsInner (adjoint L) U
    calc
      hsInner L U = opTrace (adjoint L ∘L U) := htrace.symm
      _ = opTrace (upperBoundary e (adjoint X) ∘L U) := by rw [hAdjL]
      _ = opTrace 0 := congrArg opTrace (by
        change upperBoundary e (adjoint X) * U = 0
        exact hzero)
      _ = 0 := by simp [opTrace]
  have hcomm : ccmCommutator X e = L - U := by
    simpa only [L, U] using ccmCommutator_eq_crossBoundary_sub_upperBoundary e X
  rw [hcomm]
  exact hsNormSq_sub_eq_add_of_hsInner_eq_zero hL hU horth

/-- **General finite-rank boundary law.**  The diagonal Ward value of an arbitrary finite packet at
an orthogonal cutoff is the sum of its outgoing and incoming boundary energies. -/
theorem finiteRankCutoffWardForm_self_eq_boundary_energy_sum
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (c : ι → ℂ) (x y : ι → H) :
    finiteRankCutoffWardForm e c x y c x y =
      ((hsNormSq (crossBoundary e (finiteRankProbe c x y)) +
        hsNormSq (upperBoundary e (finiteRankProbe c x y)) : ℝ) : ℂ) := by
  have henergy := hsNormSq_commutator_eq_boundary_sum_of_hilbertSchmidt
    e (finiteRankProbe c x y) he heAdj (finiteRankProbe_isHilbertSchmidt c x y)
  rw [finiteRankCutoffWardForm_self_eq_hsNormSq]
  exact congrArg (fun r : ℝ ↦ (r : ℂ)) henergy

/-- The diagonal Ward value at an orthogonal cutoff vanishes exactly when both directional
boundary crossings vanish.  This is the two-corner proposition interface without a source
self-adjointness premise. -/
theorem finiteRankCutoffWardForm_self_eq_zero_iff_boundaries
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (c : ι → ℂ) (x y : ι → H) :
    finiteRankCutoffWardForm e c x y c x y = 0 ↔
      crossBoundary e (finiteRankProbe c x y) = 0 ∧
        upperBoundary e (finiteRankProbe c x y) = 0 := by
  have hP := finiteRankProbe_isHilbertSchmidt c x y
  have hL : IsHilbertSchmidt (crossBoundary e (finiteRankProbe c x y)) := by
    simpa only [crossBoundary, mul_assoc] using (hP.comp_right e).comp_left (1 - e)
  have hU : IsHilbertSchmidt (upperBoundary e (finiteRankProbe c x y)) := by
    simpa only [upperBoundary, mul_assoc] using (hP.comp_right (1 - e)).comp_left e
  rw [finiteRankCutoffWardForm_self_eq_boundary_energy_sum e he heAdj c x y,
    Complex.ofReal_eq_zero,
    add_eq_zero_iff_of_nonneg (hsNormSq_nonneg _) (hsNormSq_nonneg _),
    hsNormSq_eq_zero_iff hL, hsNormSq_eq_zero_iff hU]

/-- The actual even position cutoff discharges the projection interfaces in the general
two-direction boundary law for every complex finite packet. -/
theorem finiteRankCutoffWardForm_evenIndicator_self_eq_boundary_energy_sum
    (a : ℝ) (c : ι → ℂ) (x y : ι → evenSubspace) :
    finiteRankCutoffWardForm (evenIndicatorCutoff a) c x y c x y =
      ((hsNormSq
          (crossBoundary (evenIndicatorCutoff a) (finiteRankProbe c x y)) +
        hsNormSq
          (upperBoundary (evenIndicatorCutoff a) (finiteRankProbe c x y)) : ℝ) : ℂ) := by
  exact finiteRankCutoffWardForm_self_eq_boundary_energy_sum
    (evenIndicatorCutoff a) (evenIndicatorCutoff_idempotent a)
    (adjoint_evenIndicatorCutoff a) c x y

/-- On the actual even position cutoff, the Ward value of an arbitrary finite packet vanishes
exactly when both physical directional crossings vanish. -/
theorem finiteRankCutoffWardForm_evenIndicator_self_eq_zero_iff_boundaries
    (a : ℝ) (c : ι → ℂ) (x y : ι → evenSubspace) :
    finiteRankCutoffWardForm (evenIndicatorCutoff a) c x y c x y = 0 ↔
      crossBoundary (evenIndicatorCutoff a) (finiteRankProbe c x y) = 0 ∧
        upperBoundary (evenIndicatorCutoff a) (finiteRankProbe c x y) = 0 := by
  exact finiteRankCutoffWardForm_self_eq_zero_iff_boundaries
    (evenIndicatorCutoff a) (evenIndicatorCutoff_idempotent a)
    (adjoint_evenIndicatorCutoff a) c x y

/-- **General concrete Sonin value reflection.**  The Fourier-side diagonal Ward value of every
reflected complex finite packet is the sum of its two physical-side Sonin boundary energies. -/
theorem finiteRankCutoffWardForm_evenFourier_reflected_self_eq_physicalBoundaryEnergySum
    (a : ℝ) (c : ι → ℂ) (x y : ι → evenSubspace) :
    finiteRankCutoffWardForm (evenFourierCutoff a) c
        (fun i ↦ evenFourierTransform (x i))
        (fun i ↦ evenFourierTransform (y i)) c
        (fun i ↦ evenFourierTransform (x i))
        (fun i ↦ evenFourierTransform (y i)) =
      ((hsNormSq
          (crossBoundary (evenIndicatorCutoff a) (finiteRankProbe c x y)) +
        hsNormSq
          (upperBoundary (evenIndicatorCutoff a) (finiteRankProbe c x y)) : ℝ) : ℂ) := by
  rw [evenFourierCutoff_eq_reflectedCutoff, reflectedCutoff]
  rw [finiteRankCutoffWardForm_conjugate_involution
    evenFourierTransform (evenIndicatorCutoff a) c x y c x y
    evenFourierTransform_mul_self adjoint_evenFourierTransform]
  exact finiteRankCutoffWardForm_evenIndicator_self_eq_boundary_energy_sum a c x y

/-- The Fourier-reflected diagonal Ward value of an arbitrary finite packet vanishes exactly when
both original physical-side Sonin boundary crossings vanish. -/
theorem finiteRankCutoffWardForm_evenFourier_reflected_self_eq_zero_iff_physicalBoundaries
    (a : ℝ) (c : ι → ℂ) (x y : ι → evenSubspace) :
    finiteRankCutoffWardForm (evenFourierCutoff a) c
        (fun i ↦ evenFourierTransform (x i))
        (fun i ↦ evenFourierTransform (y i)) c
        (fun i ↦ evenFourierTransform (x i))
        (fun i ↦ evenFourierTransform (y i)) = 0 ↔
      crossBoundary (evenIndicatorCutoff a) (finiteRankProbe c x y) = 0 ∧
        upperBoundary (evenIndicatorCutoff a) (finiteRankProbe c x y) = 0 := by
  rw [evenFourierCutoff_eq_reflectedCutoff, reflectedCutoff]
  rw [finiteRankCutoffWardForm_conjugate_involution
    evenFourierTransform (evenIndicatorCutoff a) c x y c x y
    evenFourierTransform_mul_self adjoint_evenFourierTransform]
  exact finiteRankCutoffWardForm_evenIndicator_self_eq_zero_iff_boundaries a c x y

/-- **Finite-rank Ward seam-energy law.**  For an orthogonal cutoff and a self-adjoint finite
packet, the diagonal Ward value is exactly twice the Hilbert--Schmidt energy of its one-way lower
boundary crossing. -/
theorem finiteRankCutoffWardForm_self_eq_two_mul_crossBoundary
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (c : ι → ℂ) (x y : ι → H)
    (hPAdj : adjoint (finiteRankProbe c x y) = finiteRankProbe c x y) :
    finiteRankCutoffWardForm e c x y c x y =
      ((2 * hsNormSq (crossBoundary e (finiteRankProbe c x y)) : ℝ) : ℂ) := by
  let P := finiteRankProbe c x y
  have hP : IsHilbertSchmidt P := finiteRankProbe_isHilbertSchmidt c x y
  have hL : IsHilbertSchmidt (crossBoundary e P) := by
    simpa only [crossBoundary, mul_assoc] using (hP.comp_right e).comp_left (1 - e)
  have henergy := hsNormSq_commutator_eq_two_mul_crossBoundary_of_selfAdjoint
    e P he heAdj hPAdj hL
  rw [finiteRankCutoffWardForm_self_eq_hsNormSq]
  exact congrArg (fun r : ℝ ↦ (r : ℂ)) henergy

/-- The one-way boundary corner is a faithful proposition interface for the diagonal Ward value
when both source and cutoff are self-adjoint. -/
theorem finiteRankCutoffWardForm_self_eq_zero_iff_crossBoundary
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (c : ι → ℂ) (x y : ι → H)
    (hPAdj : adjoint (finiteRankProbe c x y) = finiteRankProbe c x y) :
    finiteRankCutoffWardForm e c x y c x y = 0 ↔
      crossBoundary e (finiteRankProbe c x y) = 0 := by
  rw [finiteRankCutoffWardForm_self_eq_two_mul_crossBoundary e he heAdj c x y hPAdj,
    Complex.ofReal_eq_zero, mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero, false_or]
  exact hsNormSq_eq_zero_iff (by
    have hP := finiteRankProbe_isHilbertSchmidt c x y
    simpa only [crossBoundary, mul_assoc] using (hP.comp_right e).comp_left (1 - e))

/-- Real diagonal packets on the actual even position cutoff satisfy the exact one-way Sonin
boundary-energy law with no remaining structural hypothesis. -/
theorem finiteRankCutoffWardForm_evenIndicator_ofReal_self_eq_two_mul_crossBoundary
    (a : ℝ) (r : ι → ℝ) (x : ι → evenSubspace) :
    finiteRankCutoffWardForm (evenIndicatorCutoff a)
        (fun i ↦ (r i : ℂ)) x x (fun i ↦ (r i : ℂ)) x x =
      ((2 * hsNormSq
        (crossBoundary (evenIndicatorCutoff a)
          (finiteRankProbe (fun i ↦ (r i : ℂ)) x x)) : ℝ) : ℂ) := by
  exact finiteRankCutoffWardForm_self_eq_two_mul_crossBoundary
    (evenIndicatorCutoff a) (evenIndicatorCutoff_idempotent a)
    (adjoint_evenIndicatorCutoff a) (fun i ↦ (r i : ℂ)) x x
    (adjoint_finiteRankProbe_ofReal_self r x)

/-- On the concrete even position cutoff, a real diagonal packet has zero Ward value exactly when
its physical one-way Sonin boundary crossing vanishes. -/
theorem finiteRankCutoffWardForm_evenIndicator_ofReal_self_eq_zero_iff
    (a : ℝ) (r : ι → ℝ) (x : ι → evenSubspace) :
    finiteRankCutoffWardForm (evenIndicatorCutoff a)
        (fun i ↦ (r i : ℂ)) x x (fun i ↦ (r i : ℂ)) x x = 0 ↔
      crossBoundary (evenIndicatorCutoff a)
        (finiteRankProbe (fun i ↦ (r i : ℂ)) x x) = 0 := by
  exact finiteRankCutoffWardForm_self_eq_zero_iff_crossBoundary
    (evenIndicatorCutoff a) (evenIndicatorCutoff_idempotent a)
    (adjoint_evenIndicatorCutoff a) (fun i ↦ (r i : ℂ)) x x
    (adjoint_finiteRankProbe_ofReal_self r x)

/-- **Concrete Sonin value reflection.**  The diagonal Ward value of the Fourier-reflected real
packet at the even Fourier cutoff is exactly twice the physical-side one-way crossing energy. -/
theorem finiteRankCutoffWardForm_evenFourier_reflected_ofReal_self_eq_two_mul_physicalCrossBoundary
    (a : ℝ) (r : ι → ℝ) (x : ι → evenSubspace) :
    finiteRankCutoffWardForm (evenFourierCutoff a)
        (fun i ↦ (r i : ℂ))
        (fun i ↦ evenFourierTransform (x i))
        (fun i ↦ evenFourierTransform (x i))
        (fun i ↦ (r i : ℂ))
        (fun i ↦ evenFourierTransform (x i))
        (fun i ↦ evenFourierTransform (x i)) =
      ((2 * hsNormSq
        (crossBoundary (evenIndicatorCutoff a)
          (finiteRankProbe (fun i ↦ (r i : ℂ)) x x)) : ℝ) : ℂ) := by
  rw [evenFourierCutoff_eq_reflectedCutoff, reflectedCutoff]
  rw [finiteRankCutoffWardForm_conjugate_involution
    evenFourierTransform (evenIndicatorCutoff a)
    (fun i ↦ (r i : ℂ)) x x (fun i ↦ (r i : ℂ)) x x
    evenFourierTransform_mul_self adjoint_evenFourierTransform]
  exact finiteRankCutoffWardForm_evenIndicator_ofReal_self_eq_two_mul_crossBoundary a r x

/-- The reflected Fourier-side Ward value vanishes exactly when the original physical-side packet
has no one-way Sonin boundary crossing. -/
theorem finiteRankCutoffWardForm_evenFourier_reflected_ofReal_self_eq_zero_iff
    (a : ℝ) (r : ι → ℝ) (x : ι → evenSubspace) :
    finiteRankCutoffWardForm (evenFourierCutoff a)
        (fun i ↦ (r i : ℂ))
        (fun i ↦ evenFourierTransform (x i))
        (fun i ↦ evenFourierTransform (x i))
        (fun i ↦ (r i : ℂ))
        (fun i ↦ evenFourierTransform (x i))
        (fun i ↦ evenFourierTransform (x i)) = 0 ↔
      crossBoundary (evenIndicatorCutoff a)
        (finiteRankProbe (fun i ↦ (r i : ℂ)) x x) = 0 := by
  rw [finiteRankCutoffWardForm_evenFourier_reflected_ofReal_self_eq_two_mul_physicalCrossBoundary,
    Complex.ofReal_eq_zero, mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero, false_or]
  exact hsNormSq_eq_zero_iff (by
    have hP := finiteRankProbe_isHilbertSchmidt (fun i ↦ (r i : ℂ)) x x
    simpa only [crossBoundary, mul_assoc] using
      (hP.comp_right (evenIndicatorCutoff a)).comp_left (1 - evenIndicatorCutoff a))

end RHTower
