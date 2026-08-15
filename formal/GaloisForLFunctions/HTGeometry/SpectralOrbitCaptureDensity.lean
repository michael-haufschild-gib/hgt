import GaloisForLFunctions.HTGeometry.CompletedTimeCaptureDensity
import GaloisForLFunctions.HTGeometry.DiagonalPhaseSectionMeasure

/-!
# Completed-time density of spectral capture for a maximally projective Hamiltonian

The spectral orbit of a state with complex eigencoefficients is the nonnegative-amplitude phase
orbit translated by the argument vector of the coefficients, so the Haar measure of its capture
event is unchanged.  The event is invariant under a common phase, hence determined by its anchored
slice on the torus of relative phases, on which a maximally projective spectrum has rationally
independent frequencies.  Kronecker–Weyl equidistribution therefore transfers the replica-moment
bound on the phase box into a bound on the physical-time density of capture.
-/

open MeasureTheory Complex UnitAddTorus Set Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {C : Type*} [Fintype C] [Nonempty C]

section Character

theorem fourier_one_add (x y : UnitAddCircle) :
    (fourier 1 (x + y) : ℂ) = (fourier 1 x : ℂ) * (fourier 1 y : ℂ) := by
  simp_rw [fourier_apply, one_zsmul, AddCircle.toCircle_add, Circle.coe_mul]

theorem norm_fourier_one (x : UnitAddCircle) : ‖(fourier 1 x : ℂ)‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

theorem finitePureStateFidelity_const_mul {α : Type*} [Fintype α] {w : ℂ} (hw : ‖w‖ = 1)
    (u v : α → ℂ) :
    finitePureStateFidelity (fun j => w * u j) v = finitePureStateFidelity u v := by
  have hinner : finiteComplexInner (fun j => w * u j) v =
      (starRingEnd ℂ) w * finiteComplexInner u v := by
    simp only [finiteComplexInner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  rw [finitePureStateFidelity, finitePureStateFidelity, hinner, norm_mul, Complex.norm_conj, hw,
    one_mul]

end Character

section AmplitudeOrbit

/-- The spectral phase orbit of a state with complex eigencoefficients. -/
def torusAmpOrbit (c : I → ℂ) (t : UnitAddTorus I) : I → ℂ :=
  fun j => c j * UnitAddTorus.mFourier (Pi.single j 1) t

/-- The argument vector of a family of complex eigencoefficients, read on the phase torus. -/
def ampPhase (c : I → ℂ) : UnitAddTorus I :=
  fun j => ((Complex.arg (c j) / (2 * Real.pi) : ℝ) : UnitAddCircle)

theorem fourier_one_ampPhase (c : I → ℂ) (j : I) :
    (fourier 1 (ampPhase c j) : ℂ) = Complex.exp (Complex.arg (c j) * Complex.I) := by
  rw [ampPhase, fourier_coe_apply]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **The complex-coefficient orbit is the nonnegative-amplitude orbit translated by the argument
vector.** -/
theorem torusAmpOrbit_eq_torusPhaseOrbit (c : I → ℂ) (t : UnitAddTorus I) :
    torusAmpOrbit c t = torusPhaseOrbit (fun j => ‖c j‖ ^ 2) (t + ampPhase c) := by
  funext j
  rw [torusAmpOrbit, torusPhaseOrbit, UnitAddTorus.mFourier_single, UnitAddTorus.mFourier_single,
    Real.sqrt_sq (norm_nonneg _)]
  have hadd : (t + ampPhase c) j = t j + ampPhase c j := rfl
  rw [hadd, fourier_one_add, fourier_one_ampPhase]
  have hc : ((‖c j‖ : ℝ) : ℂ) * Complex.exp (Complex.arg (c j) * Complex.I) = c j :=
    Complex.norm_mul_exp_arg_mul_I (c j)
  conv_lhs => rw [← hc]
  ring

theorem continuous_torusAmpOrbit_apply (c : I → ℂ) (j : I) :
    Continuous fun t : UnitAddTorus I => torusAmpOrbit c t j :=
  continuous_const.mul (UnitAddTorus.mFourier (Pi.single j 1)).continuous

theorem continuous_fidelity_torusAmpOrbit (c : I → ℂ) (v : I → ℂ) :
    Continuous fun t : UnitAddTorus I => finitePureStateFidelity (torusAmpOrbit c t) v := by
  refine (Continuous.norm ?_).pow 2
  refine continuous_finsetSum Finset.univ fun j _ => ?_
  exact (Complex.continuous_conj.comp (continuous_torusAmpOrbit_apply c j)).mul continuous_const

end AmplitudeOrbit

section CaptureTarget

/-- The complete-target capture event of a complex-coefficient spectral orbit. -/
def torusAmpCaptureTarget (c : I → ℂ) (a : ℝ) (z : C → (I → ℂ)) : Set (UnitAddTorus I) :=
  {t | ∃ κ, a ≤ finitePureStateFidelity (torusAmpOrbit c t) (z κ)}

theorem isClosed_torusAmpCaptureTarget (c : I → ℂ) (a : ℝ) (z : C → (I → ℂ)) :
    IsClosed (torusAmpCaptureTarget c a z) := by
  have hunion : torusAmpCaptureTarget c a z =
      ⋃ κ : C, {t : UnitAddTorus I | a ≤ finitePureStateFidelity (torusAmpOrbit c t) (z κ)} := by
    ext t
    simp [torusAmpCaptureTarget]
  rw [hunion]
  exact isClosed_iUnion_of_finite fun κ =>
    isClosed_le continuous_const (continuous_fidelity_torusAmpOrbit c (z κ))

theorem measurableSet_torusAmpCaptureTarget (c : I → ℂ) (a : ℝ) (z : C → (I → ℂ)) :
    MeasurableSet (torusAmpCaptureTarget c a z) :=
  (isClosed_torusAmpCaptureTarget c a z).measurableSet

/-- The complex-coefficient capture event is a translate of the nonnegative-amplitude one. -/
theorem torusAmpCaptureTarget_eq_preimage (c : I → ℂ) (a : ℝ) (z : C → (I → ℂ)) :
    torusAmpCaptureTarget c a z =
      (fun t => ampPhase c + t) ⁻¹' (torusCaptureTarget (fun j => ‖c j‖ ^ 2) a z) := by
  ext t
  simp only [torusAmpCaptureTarget, torusCaptureTarget, Set.mem_preimage, Set.mem_setOf_eq]
  have horb : torusAmpOrbit c t = torusPhaseOrbit (fun j => ‖c j‖ ^ 2) (ampPhase c + t) := by
    rw [torusAmpOrbit_eq_torusPhaseOrbit, add_comm]
  rw [horb]

/-- **The Haar measure of the complex-coefficient capture event.** -/
theorem measure_torusAmpCaptureTarget (c : I → ℂ) (a : ℝ) (z : C → (I → ℂ)) :
    (volume : Measure (UnitAddTorus I)) (torusAmpCaptureTarget c a z) =
      ((volume : Measure (I → ℝ)).restrict (torusBox I))
        {x : I → ℝ | ∃ κ,
          a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit (fun j => ‖c j‖ ^ 2) x) (z κ)} := by
  rw [torusAmpCaptureTarget_eq_preimage c a z, measure_preimage_add,
    measure_torusCaptureTarget]

theorem diagonalPhaseInvariant_torusAmpCaptureTarget (c : I → ℂ) (a : ℝ) (z : C → (I → ℂ)) :
    DiagonalPhaseInvariant (torusAmpCaptureTarget c a z) := by
  intro γ x
  have horb : torusAmpOrbit c (fun i => x i + γ) =
      fun j => (fourier 1 γ : ℂ) * torusAmpOrbit c x j := by
    funext j
    rw [torusAmpOrbit, torusAmpOrbit, UnitAddTorus.mFourier_single, UnitAddTorus.mFourier_single,
      fourier_one_add]
    ring
  have hfid : ∀ v : I → ℂ,
      finitePureStateFidelity (torusAmpOrbit c fun i => x i + γ) v =
        finitePureStateFidelity (torusAmpOrbit c x) v := by
    intro v
    rw [horb]
    exact finitePureStateFidelity_const_mul (norm_fourier_one γ) _ _
  constructor
  · rintro ⟨κ, hκ⟩
    exact ⟨κ, by rwa [hfid (z κ)] at hκ⟩
  · rintro ⟨κ, hκ⟩
    exact ⟨κ, by rw [hfid (z κ)]; exact hκ⟩

end CaptureTarget

section Projective

/-- The spectral orbit read on the torus of phases relative to an anchored reference level. -/
def projectiveSpectralOrbit (ref : I) (c : I → ℂ)
    (y : UnitAddTorus {i : I // i ≠ ref}) : I → ℂ :=
  torusAmpOrbit c (torusSection ref y)

/-- The complete-target capture event on the torus of relative phases. -/
def projectiveAmpCaptureTarget (ref : I) (c : I → ℂ) (a : ℝ) (z : C → (I → ℂ)) :
    Set (UnitAddTorus {i : I // i ≠ ref}) :=
  {y | ∃ κ, a ≤ finitePureStateFidelity (projectiveSpectralOrbit ref c y) (z κ)}

theorem projectiveAmpCaptureTarget_eq_preimage (ref : I) (c : I → ℂ) (a : ℝ) (z : C → (I → ℂ)) :
    projectiveAmpCaptureTarget ref c a z = torusSection ref ⁻¹' (torusAmpCaptureTarget c a z) := by
  ext y
  rfl

theorem isClosed_projectiveAmpCaptureTarget (ref : I) (c : I → ℂ) (a : ℝ) (z : C → (I → ℂ)) :
    IsClosed (projectiveAmpCaptureTarget ref c a z) := by
  rw [projectiveAmpCaptureTarget_eq_preimage]
  exact (isClosed_torusAmpCaptureTarget c a z).preimage (continuous_torusSection ref)

/-- **The relative-phase capture event has the Haar measure of the full-torus one.** -/
theorem measure_projectiveAmpCaptureTarget (ref : I) (c : I → ℂ) (a : ℝ) (z : C → (I → ℂ)) :
    (volume : Measure (UnitAddTorus {i : I // i ≠ ref}))
        (projectiveAmpCaptureTarget ref c a z) =
      (volume : Measure (UnitAddTorus I)) (torusAmpCaptureTarget c a z) := by
  rw [projectiveAmpCaptureTarget_eq_preimage]
  exact (measure_eq_measure_torusSection_preimage ref (measurableSet_torusAmpCaptureTarget c a z)
    (diagonalPhaseInvariant_torusAmpCaptureTarget c a z)).symm

end Projective

section Density

/-- **Completed-time density of spectral capture.**  For a Hamiltonian whose spectrum admits no
nonzero balanced integer resonance, the long-time density of the set of observation times at which
the spectral orbit of a subnormalized state reaches fidelity `a` with some member of a finite
target family is at most the replica-moment bound of the corresponding phase-box capture event. -/
theorem limsup_finiteTorusPhaseProbabilityMeasure_projectiveAmpCapture_le
    (lam : I → ℝ) (hmax : MaximallyProjectiveEnergy lam) (ref : I)
    (c : I → ℂ) (hcsum : ∑ j, ‖c j‖ ^ 2 ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (I → ℂ)) (hz : ∀ κ, finiteComplexInner (z κ) (z κ) = 1)
    (hznorm : ∀ κ, ∑ j, ‖z κ j‖ ^ 2 ≤ 1) (r : ℕ) :
    atTop.limsup (fun T => (finiteTorusPhaseProbabilityMeasure (projectiveFrequency lam ref) T :
        Measure (UnitAddTorus {i : I // i ≠ ref})) (projectiveAmpCaptureTarget ref c a z)) ≤
      ENNReal.ofReal ((Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * occupationCollision (fun j => ‖c j‖ ^ 2) / a ^ 2) ^ r) := by
  classical
  have hind : RationallyIndependentFrequency (projectiveFrequency lam ref) :=
    maximallyProjectiveEnergy_projectiveFrequency_independent lam hmax ref
  refine le_trans (rationallyIndependent_closedTarget_limsup_le_volume _ hind
    (isClosed_projectiveAmpCaptureTarget ref c a z)) ?_
  have hbox := measureReal_capture_le_return_add_replicaMoment
    (p := fun j => ‖c j‖ ^ 2) (fun j => sq_nonneg _) hcsum ha z hz hznorm
    (R := (∅ : Set (I → ℝ)))
    (Q := {x : I → ℝ | ∃ κ,
      a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit (fun j => ‖c j‖ ^ 2) x) (z κ)})
    MeasurableSet.empty (fun x hx => hx.1) r
  rw [measureReal_empty, zero_add] at hbox
  have hmeas := (measure_projectiveAmpCaptureTarget ref c a z).trans
    (measure_torusAmpCaptureTarget c a z)
  have hfin : (volume : Measure (UnitAddTorus {i : I // i ≠ ref}))
      (projectiveAmpCaptureTarget ref c a z) ≠ ⊤ := measure_ne_top _ _
  have hle : (volume : Measure (UnitAddTorus {i : I // i ≠ ref})).real
      (projectiveAmpCaptureTarget ref c a z) ≤
      (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * occupationCollision (fun j => ‖c j‖ ^ 2) / a ^ 2) ^ r := by
    rw [measureReal_def, hmeas, ← measureReal_def]
    exact hbox
  have hstep := ENNReal.ofReal_le_ofReal hle
  rwa [measureReal_def, ENNReal.ofReal_toReal hfin] at hstep

end Density

section PhysicalTime

/-- Absence of nonzero balanced integer resonances is invariant under reversing the energy sign. -/
theorem maximallyProjectiveEnergy_neg {lam : I → ℝ} (h : MaximallyProjectiveEnergy lam) :
    MaximallyProjectiveEnergy (fun i => -lam i) := by
  intro k hbal hsum
  refine h k hbal ?_
  have hkey : (∑ i, (k i : ℝ) * (-lam i)) = -(∑ i, (k i : ℝ) * lam i) := by
    simp [mul_neg]
  rw [hkey, neg_eq_zero] at hsum
  exact hsum

/-- **The sampled relative-phase point carries the Schrödinger orbit.**  At sampled observation
time `A(2u-1)` the anchored relative-phase orbit is the eigencoefficient vector of the evolved
state, up to the global phase of the anchored level. -/
theorem projectiveSpectralOrbit_finiteTorusPhasePoint (ref : I) (c : I → ℂ) (lam : I → ℝ)
    (A u : ℝ) (j : I) :
    projectiveSpectralOrbit ref c
        (finiteTorusPhasePoint (projectiveFrequency (fun i => -lam i) ref) A u) j =
      c j * Complex.exp (-(Complex.I * ((A * (2 * u - 1)) * (lam j - lam ref)))) := by
  rw [projectiveSpectralOrbit, torusAmpOrbit, UnitAddTorus.mFourier_single]
  by_cases hj : j ≠ ref
  · have hsec : torusSection ref
        (finiteTorusPhasePoint (projectiveFrequency (fun i => -lam i) ref) A u) j =
        ((A * (2 * u - 1) * (projectiveFrequency (fun i => -lam i) ref ⟨j, hj⟩) /
          (2 * Real.pi) : ℝ) : UnitAddCircle) := by
      rw [torusSection, dif_pos hj, finiteTorusPhasePoint]
    rw [hsec, fourier_coe_apply]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [projectiveFrequency]
    push_cast
    field_simp
    ring
  · have hjref : j = ref := by
      by_contra hcon
      exact hj hcon
    subst hjref
    have hsec : torusSection ref
        (finiteTorusPhasePoint (projectiveFrequency (fun i => -lam i) ref) A u) j = 0 := by
      rw [torusSection, dif_neg hj]
    rw [hsec]
    simp

/-- **Completed-time density of Schrödinger capture.**  Restatement of the capture-density bound
for the physical evolution sign convention. -/
theorem limsup_finiteTorusPhaseProbabilityMeasure_evolutionCapture_le
    (lam : I → ℝ) (hmax : MaximallyProjectiveEnergy lam) (ref : I)
    (c : I → ℂ) (hcsum : ∑ j, ‖c j‖ ^ 2 ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (I → ℂ)) (hz : ∀ κ, finiteComplexInner (z κ) (z κ) = 1)
    (hznorm : ∀ κ, ∑ j, ‖z κ j‖ ^ 2 ≤ 1) (r : ℕ) :
    atTop.limsup (fun T => (finiteTorusPhaseProbabilityMeasure
        (projectiveFrequency (fun i => -lam i) ref) T :
        Measure (UnitAddTorus {i : I // i ≠ ref})) (projectiveAmpCaptureTarget ref c a z)) ≤
      ENNReal.ofReal ((Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * occupationCollision (fun j => ‖c j‖ ^ 2) / a ^ 2) ^ r) :=
  limsup_finiteTorusPhaseProbabilityMeasure_projectiveAmpCapture_le _
    (maximallyProjectiveEnergy_neg hmax) ref c hcsum ha z hz hznorm r

end PhysicalTime

end GaloisForLFunctions.HTGeometry
