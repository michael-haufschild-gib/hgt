/-
# Free-fermion number variance as Sonin commutator energy

For a Fermi projection `P` and a spatial projection `R`, the local particle-number variance is
the plunge-spectrum value `tr(T - T²)` of the compressed projection `T = RPR`.  The two
off-diagonal transition corners are adjoints, square-zero, and Hilbert--Schmidt orthogonal.
Consequently the Hilbert--Schmidt energy of the projection commutator is exactly twice that
variance.

This file specializes that quantum-fluctuation identity to the central physical/Fourier Sonin
cutoffs.  It joins three existing theorem surfaces without an analytic comparison constant:

* the cutoff commutator energy;
* the lower transition-corner energy;
* the trace of the prolate impurity `T - T²`.
-/
import GaloisForLFunctions.HTGeometry.QuantumMasterConstraintSpectrum
import GaloisForLFunctions.RHTower.SoninLudersPinching
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

noncomputable section

namespace RHTower

open ContinuousLinearMap

/-- The central physical-to-Fourier transition corner is Hilbert--Schmidt.  This is the
free-fermion subsystem leakage operator `(1-R)PR`, obtained directly from the concrete Sonin
time-band ideal. -/
theorem centralProlateTransition_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) :
    IsHilbertSchmidt
      (crossBoundary (centralFourierForbidden a).starProjection
        (centralPhysicalForbidden a).starProjection) := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : SoninL2 →L[ℂ] SoninL2 := A.starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := B.starProjection
  have hPR : IsSoninTimeBandIdeal (P * R) := by
    simpa [P, R, A, B, centralPhysicalForbidden, centralFourierForbidden,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using!
      IsSoninTimeBandIdeal.indicatorFourier a a ha ha
  have hPRhs : IsHilbertSchmidt (P * R) := hPR.isHilbertSchmidt
  simpa only [P, R, A, B, crossBoundary, mul_assoc] using!
    hPRhs.comp_left (1 - R)

/-- **Central Shannon-number value.**  The operator trace of the actual central prolate
compression is the exact time--frequency area `4 a²`.  This is the trace-coordinate form of the
existing overlap Hilbert--Schmidt law and avoids passing through a singular-value expansion. -/
theorem re_opTrace_centralProlateBlock_eq_four_mul_sq
    (a : ℝ) (ha : 0 < a) :
    Complex.re
        (opTrace
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a))) =
      4 * a ^ 2 := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : SoninL2 →L[ℂ] SoninL2 := B.starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := A.starProjection
  have hR : IsIdempotentElem R := A.isIdempotentElem_starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (isSelfAdjoint_starProjection B).star_eq
  have hRadj : ContinuousLinearMap.adjoint R = R :=
    (isSelfAdjoint_starProjection A).star_eq
  have hRP : IsHilbertSchmidt (R * P) := by
    simpa only [P, R, A, B, centralPhysicalForbidden, centralFourierForbidden,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using!
      isHilbertSchmidt_indicatorCutoff_fourierCutoff_central a a ha
  have hAdj : ContinuousLinearMap.adjoint (R * P) = P * R := by
    change ContinuousLinearMap.adjoint (R ∘L P) = P ∘L R
    rw [ContinuousLinearMap.adjoint_comp, hPadj, hRadj]
  have hNorm : hsNormSq (R * P) = hsNormSq (P * R) := by
    rw [← hAdj]
    exact hRP.hsNormSq_adjoint.symm
  calc
    Complex.re
        (opTrace
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a))) =
        hsNormSq (R * P) := by
      simpa only [P, R, A, B, soninAlternatingBlock,
        HTGeometry.twoProjectionInteriorCompression] using
        HTGeometry.re_opTrace_twoProjectionInteriorCompression_eq_hsNormSq_overlap
          P R hR hPadj hRadj hRP
    _ = hsNormSq (P * R) := hNorm
    _ = 4 * a ^ 2 := by
      simpa only [P, R, A, B] using
        hsNormSq_centralTimeBandOverlap_eq_four_mul_sq a ha

/-- **Quantum transition-rate identity.**  For a self-adjoint observable `X` and an orthogonal
cutoff `e`, the commutator has exactly twice the Hilbert--Schmidt energy of its lower transition
corner.  The factor two is exact: the lower and upper corners are adjoints with equal energy,
while their cross pairing vanishes because each same-direction corner is square-zero. -/
theorem hsNormSq_commutator_eq_two_mul_crossBoundary_of_selfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (heAdj : ContinuousLinearMap.adjoint e = e)
    (hXAdj : ContinuousLinearMap.adjoint X = X)
    (hL : IsHilbertSchmidt (crossBoundary e X)) :
    hsNormSq (ccmCommutator X e) = 2 * hsNormSq (crossBoundary e X) := by
  let L : H →L[ℂ] H := crossBoundary e X
  let U : H →L[ℂ] H := upperBoundary e X
  have hL' : IsHilbertSchmidt L := by
    simpa only [L] using hL
  have hAdjL : ContinuousLinearMap.adjoint L = U := by
    dsimp only [L, U]
    unfold crossBoundary upperBoundary
    change ContinuousLinearMap.adjoint (((1 - e) * X) ∘L e) = _
    rw [ContinuousLinearMap.adjoint_comp]
    change ContinuousLinearMap.adjoint e ∘L
      ContinuousLinearMap.adjoint ((1 - e) ∘L X) = _
    rw [ContinuousLinearMap.adjoint_comp, adjoint_one_sub heAdj, hXAdj, heAdj]
    rfl
  have hU : IsHilbertSchmidt U := by
    rw [← hAdjL]
    exact hL'.adjoint
  have hUU : U * U = 0 := by
    simpa only [U] using upperBoundary_mul_upperBoundary e X X he
  have horth : hsInner L U = 0 := by
    have htrace :
        opTrace (ContinuousLinearMap.adjoint L ∘L U) = hsInner L U := by
      simpa using opTrace_comp_eq_hsInner (ContinuousLinearMap.adjoint L) U
    calc
      hsInner L U = opTrace (ContinuousLinearMap.adjoint L ∘L U) := htrace.symm
      _ = opTrace (U ∘L U) := by rw [hAdjL]
      _ = opTrace 0 := congrArg opTrace (by
        change U * U = 0
        exact hUU)
      _ = 0 := by simp [opTrace]
  have hUnorm : hsNormSq U = hsNormSq L := by
    rw [← hAdjL]
    exact hL'.hsNormSq_adjoint
  have hcomm : ccmCommutator X e = L - U := by
    simpa only [L, U] using ccmCommutator_eq_crossBoundary_sub_upperBoundary e X
  change hsNormSq (ccmCommutator X e) = 2 * hsNormSq L
  rw [hcomm]
  calc
    hsNormSq (L - U) = hsNormSq L + hsNormSq U :=
      hsNormSq_sub_eq_add_of_hsInner_eq_zero hL' hU horth
    _ = 2 * hsNormSq L := by rw [hUnorm]; ring

/-- **Exact one-corner Lüders energy law.**  For a self-adjoint observable and orthogonal cutoff,
the full nonselective-measurement disturbance has exactly twice the Hilbert--Schmidt energy of
one transition corner.  The lone analytic premise is finiteness of that corner itself. -/
theorem hsNormSq_ludersDisturbance_eq_two_mul_crossBoundary_of_selfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (heAdj : ContinuousLinearMap.adjoint e = e)
    (hXAdj : ContinuousLinearMap.adjoint X = X)
    (hL : IsHilbertSchmidt (crossBoundary e X)) :
    hsNormSq (X - ludersPinching e X) =
      2 * hsNormSq (crossBoundary e X) := by
  rw [hsNormSq_ludersDisturbance_eq_cutoffCommutator e X he heAdj hXAdj]
  exact hsNormSq_commutator_eq_two_mul_crossBoundary_of_selfAdjoint
    e X he heAdj hXAdj hL

/-- Hilbert--Schmidt self-adjoint observables satisfy the transition-rate identity with no
separate corner hypothesis: the two-sided ideal property supplies it automatically. -/
theorem hsNormSq_commutator_eq_two_mul_crossBoundary_of_selfAdjoint_hilbertSchmidt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (heAdj : ContinuousLinearMap.adjoint e = e)
    (hXAdj : ContinuousLinearMap.adjoint X = X)
    (hX : IsHilbertSchmidt X) :
    hsNormSq (ccmCommutator X e) = 2 * hsNormSq (crossBoundary e X) := by
  have hL : IsHilbertSchmidt (crossBoundary e X) := by
    simpa only [crossBoundary, mul_assoc] using! (hX.comp_right e).comp_left (1 - e)
  exact hsNormSq_commutator_eq_two_mul_crossBoundary_of_selfAdjoint
    e X he heAdj hXAdj hL

/-- Projection specialization of the quantum transition-rate identity. -/
theorem hsNormSq_starProjection_commutator_eq_two_mul_transition
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (hL : IsHilbertSchmidt (crossBoundary B.starProjection A.starProjection)) :
    hsNormSq (ccmCommutator A.starProjection B.starProjection) =
      2 * hsNormSq (crossBoundary B.starProjection A.starProjection) :=
  hsNormSq_commutator_eq_two_mul_crossBoundary_of_selfAdjoint
    B.starProjection A.starProjection B.isIdempotentElem_starProjection
    (isSelfAdjoint_starProjection B).star_eq
    (isSelfAdjoint_starProjection A).star_eq hL

/-- Central physical/Fourier specialization of the exact free-fermion fluctuation law.  The
existing time-band ideal discharges the generic Hilbert--Schmidt premise. -/
theorem hsNormSq_centralCutoffCommutator_eq_two_mul_transition
    (a : ℝ) (ha : 0 < a) :
    hsNormSq
        (ccmCommutator (centralPhysicalForbidden a).starProjection
          (centralFourierForbidden a).starProjection) =
      2 * hsNormSq
        (crossBoundary (centralFourierForbidden a).starProjection
          (centralPhysicalForbidden a).starProjection) :=
  hsNormSq_starProjection_commutator_eq_two_mul_transition
    (centralPhysicalForbidden a) (centralFourierForbidden a)
    (centralProlateTransition_isHilbertSchmidt a ha)

/-- **Central measurement-decoherence value.**  The total Hilbert--Schmidt energy removed by
measuring the physical Sonin projection with the Fourier cutoff is exactly twice the one-way
transition energy.  Thus the Lüders disturbance, cutoff commutator, and free-fermion leakage
channels are interchangeable without a comparison constant. -/
theorem hsNormSq_centralLudersDisturbance_eq_two_mul_transition
    (a : ℝ) (ha : 0 < a) :
    hsNormSq
        ((centralPhysicalForbidden a).starProjection -
          ludersPinching (centralFourierForbidden a).starProjection
            (centralPhysicalForbidden a).starProjection) =
      2 * hsNormSq
        (crossBoundary (centralFourierForbidden a).starProjection
          (centralPhysicalForbidden a).starProjection) := by
  exact hsNormSq_ludersDisturbance_eq_two_mul_crossBoundary_of_selfAdjoint
    (centralFourierForbidden a).starProjection
    (centralPhysicalForbidden a).starProjection
    (centralFourierForbidden a).isIdempotentElem_starProjection
    (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq
    (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
    (centralProlateTransition_isHilbertSchmidt a ha)

/-- The trace of any Hilbert--Schmidt Sonin transition impurity is exactly the transition-corner
energy.  This turns the existing operator-valued `T-T²` law into the scalar value used by
free-fermion number fluctuations. -/
theorem re_opTrace_soninAlternatingBlock_impurity_eq_transition_hsNormSq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (hL : IsHilbertSchmidt (crossBoundary B.starProjection A.starProjection)) :
    Complex.re
        (opTrace
          (soninAlternatingBlock A B - soninAlternatingBlock A B *
            soninAlternatingBlock A B)) =
      hsNormSq (crossBoundary B.starProjection A.starProjection) := by
  rw [soninAlternatingBlock_sub_sq_eq_quantumMasterConstraint_transition]
  exact HTGeometry.re_opTrace_quantumMasterConstraint_eq_hsNormSq hL

/-- **Projection-commutator plunge-spectrum sum rule.**  The commutator energy is twice the sum
of all greedy spectral values of the prolate impurity `T-T²`.  This is the spectrum-level form
of the free-fermion number-variance identity and connects the cutoff calculus directly to the
existing compact master-constraint spectrum API. -/
theorem hsNormSq_starProjection_commutator_eq_two_mul_tsum_svVal_prolateImpurity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (hL : IsHilbertSchmidt (crossBoundary B.starProjection A.starProjection)) :
    hsNormSq (ccmCommutator A.starProjection B.starProjection) =
      2 * ∑' n, svVal
        (soninAlternatingBlock A B -
          soninAlternatingBlock A B * soninAlternatingBlock A B) n := by
  rw [hsNormSq_starProjection_commutator_eq_two_mul_transition A B hL,
    HTGeometry.hsNormSq_eq_tsum_svVal_quantumMasterConstraint hL,
    ← soninAlternatingBlock_sub_sq_eq_quantumMasterConstraint_transition A B]

/-- The trace of the central prolate impurity is exactly the transition-corner energy.  In
free-fermion language this is the local particle-number variance `tr(T(1-T))`; here `T` is the
actual alternating physical/Fourier compression already used by the Sonin resolvent. -/
theorem re_opTrace_centralProlateImpurity_eq_transition_hsNormSq
    (a : ℝ) (ha : 0 < a) :
    Complex.re
        (opTrace
          (soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a) -
            soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a) *
              soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a))) =
      hsNormSq
        (crossBoundary (centralFourierForbidden a).starProjection
          (centralPhysicalForbidden a).starProjection) :=
  re_opTrace_soninAlternatingBlock_impurity_eq_transition_hsNormSq
    (centralPhysicalForbidden a) (centralFourierForbidden a)
    (centralProlateTransition_isHilbertSchmidt a ha)

/-- The exterior compressed Hamiltonian has the same impurity trace, hence the same
free-fermion transition variance, as the prolate block.  This is the scalar Witten supertrace
cancellation in the concrete Sonin model. -/
theorem re_opTrace_centralExteriorCompressionImpurity_eq_transition_hsNormSq
    (a : ℝ) (ha : 0 < a) :
    Complex.re
        (opTrace
          (centralSoninExteriorCompression a -
            centralSoninExteriorCompression a * centralSoninExteriorCompression a)) =
      hsNormSq
        (crossBoundary (centralFourierForbidden a).starProjection
          (centralPhysicalForbidden a).starProjection) := by
  calc
    Complex.re
        (opTrace
          (centralSoninExteriorCompression a -
            centralSoninExteriorCompression a * centralSoninExteriorCompression a)) =
        Complex.re
          (opTrace
            (soninAlternatingBlock (centralPhysicalForbidden a)
                  (centralFourierForbidden a) -
              soninAlternatingBlock (centralPhysicalForbidden a)
                  (centralFourierForbidden a) *
                soninAlternatingBlock (centralPhysicalForbidden a)
                  (centralFourierForbidden a))) := by
      exact congrArg Complex.re
        (opTrace_centralProlateImpurity_eq_exteriorCompressionImpurity a ha).symm
    _ = hsNormSq
        (crossBoundary (centralFourierForbidden a).starProjection
          (centralPhysicalForbidden a).starProjection) :=
      re_opTrace_centralProlateImpurity_eq_transition_hsNormSq a ha

/-- **Witten/free-fermion scalar partition of the Sonin correction.**  The transition channel in
the zero-mode-subtracted supersymmetric partition is exactly the trace of the prolate impurity.
Thus the correction energy is two positive Hamiltonian energies plus twice the local
free-fermion number variance. -/
theorem hsNormSq_centralSoninProjectionCorrection_eq_compressions_add_two_mul_re_opTrace_prolateImpurity
    (a : ℝ) (ha : 0 < a) :
    hsNormSq (centralSoninProjectionCorrection a) =
      hsNormSq
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a)) +
        hsNormSq (centralSoninExteriorCompression a) +
          2 * Complex.re
            (opTrace
              (soninAlternatingBlock (centralPhysicalForbidden a)
                  (centralFourierForbidden a) -
                soninAlternatingBlock (centralPhysicalForbidden a)
                    (centralFourierForbidden a) *
                  soninAlternatingBlock (centralPhysicalForbidden a)
                    (centralFourierForbidden a))) := by
  rw [hsNormSq_centralSoninProjectionCorrection_eq_compressions_add_two_mul_transition a ha,
    re_opTrace_centralProlateImpurity_eq_transition_hsNormSq a ha]

/-- **Sonin number-variance identity.**  The Hilbert--Schmidt energy of the central
physical/Fourier incompatibility is exactly twice the trace of the prolate plunge-spectrum
impurity.  Thus a commutator-energy estimate, a transition estimate, or a `T-T²` trace estimate
can be substituted for either of the others with no loss and no extra hypothesis. -/
theorem hsNormSq_centralCutoffCommutator_eq_two_mul_re_opTrace_prolateImpurity
    (a : ℝ) (ha : 0 < a) :
    hsNormSq
        (ccmCommutator (centralPhysicalForbidden a).starProjection
          (centralFourierForbidden a).starProjection) =
      2 * Complex.re
        (opTrace
          (soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a) -
            soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a) *
              soninAlternatingBlock (centralPhysicalForbidden a)
                (centralFourierForbidden a))) := by
  rw [hsNormSq_centralCutoffCommutator_eq_two_mul_transition a ha,
    re_opTrace_centralProlateImpurity_eq_transition_hsNormSq a ha]

/-- **Lüders/free-fermion value identity.**  Central projective-measurement decoherence is twice
the prolate impurity trace `tr(T-T²)`, i.e. twice the local free-fermion number variance.  This
exposes the trace observable directly, without asking a consumer to pass through a commutator. -/
theorem hsNormSq_centralLudersDisturbance_eq_two_mul_re_opTrace_prolateImpurity
    (a : ℝ) (ha : 0 < a) :
    hsNormSq
        ((centralPhysicalForbidden a).starProjection -
          ludersPinching (centralFourierForbidden a).starProjection
            (centralPhysicalForbidden a).starProjection) =
      2 * Complex.re
        (opTrace
          (soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a) -
            soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a) *
              soninAlternatingBlock (centralPhysicalForbidden a)
                (centralFourierForbidden a))) := by
  rw [hsNormSq_centralLudersDisturbance_eq_two_mul_transition a ha,
    re_opTrace_centralProlateImpurity_eq_transition_hsNormSq a ha]

/-- **Finite-aperture fermionic occupation budget.**  The prolate compressed energy plus its
number-variance transition channel is exactly the Shannon time--frequency area `4 a²`. -/
theorem hsNormSq_centralProlateBlock_add_transition_eq_four_mul_sq
    (a : ℝ) (ha : 0 < a) :
    hsNormSq
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a)) +
        hsNormSq
          (crossBoundary (centralFourierForbidden a).starProjection
            (centralPhysicalForbidden a).starProjection) =
      4 * a ^ 2 := by
  have h := hsNormSq_centralTimeBandOverlap_eq_prolateBlock_add_transition a ha
  rw [hsNormSq_centralTimeBandOverlap_eq_four_mul_sq a ha] at h
  exact h.symm

/-- The same occupation budget written as prolate energy plus the free-fermion number variance
`tr(T-T²)`. -/
theorem hsNormSq_centralProlateBlock_add_re_opTrace_impurity_eq_four_mul_sq
    (a : ℝ) (ha : 0 < a) :
    hsNormSq
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a)) +
        Complex.re
          (opTrace
            (soninAlternatingBlock (centralPhysicalForbidden a)
                  (centralFourierForbidden a) -
              soninAlternatingBlock (centralPhysicalForbidden a)
                  (centralFourierForbidden a) *
                soninAlternatingBlock (centralPhysicalForbidden a)
                  (centralFourierForbidden a))) =
      4 * a ^ 2 := by
  rw [re_opTrace_centralProlateImpurity_eq_transition_hsNormSq a ha]
  exact hsNormSq_centralProlateBlock_add_transition_eq_four_mul_sq a ha

/-- Doubled occupation budget: twice the prolate energy plus the cutoff-commutator energy is the
complete corrected aperture energy `8 a²`. -/
theorem two_mul_hsNormSq_centralProlateBlock_add_commutator_eq_eight_mul_sq
    (a : ℝ) (ha : 0 < a) :
    2 * hsNormSq
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a)) +
        hsNormSq
          (ccmCommutator (centralPhysicalForbidden a).starProjection
            (centralFourierForbidden a).starProjection) =
      8 * a ^ 2 := by
  have hbudget := hsNormSq_centralProlateBlock_add_transition_eq_four_mul_sq a ha
  have hcomm := hsNormSq_centralCutoffCommutator_eq_two_mul_transition a ha
  nlinarith

/-- The corrected finite-aperture budget can be read entirely as retained prolate energy plus
measurement-decoherence energy; the cutoff commutator is no longer a required interface. -/
theorem two_mul_hsNormSq_centralProlateBlock_add_ludersDisturbance_eq_eight_mul_sq
    (a : ℝ) (ha : 0 < a) :
    2 * hsNormSq
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a)) +
        hsNormSq
          ((centralPhysicalForbidden a).starProjection -
            ludersPinching (centralFourierForbidden a).starProjection
              (centralPhysicalForbidden a).starProjection) =
      8 * a ^ 2 := by
  rw [hsNormSq_ludersDisturbance_eq_cutoffCommutator
    (centralFourierForbidden a).starProjection
    (centralPhysicalForbidden a).starProjection
    (centralFourierForbidden a).isIdempotentElem_starProjection
    (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq
    (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq]
  exact two_mul_hsNormSq_centralProlateBlock_add_commutator_eq_eight_mul_sq a ha

end RHTower
