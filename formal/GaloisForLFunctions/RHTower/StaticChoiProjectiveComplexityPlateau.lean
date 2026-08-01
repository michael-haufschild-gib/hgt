import GaloisForLFunctions.RHTower.StaticChoiComplexityPlateau
import Mathlib.MeasureTheory.Group.Prod

/-!
# Projective static Choi complexity plateau

Physical pure-state density matrices erase one common spectral phase.  This
file removes that redundant coordinate exactly.  The full phase torus splits
measure-preservingly into one global phase and the zero-anchored projective
torus; equal-weight Choi densities are constant on the global factor.

Consequently the full-torus circuit-target entropy bound is exactly the
projective Haar bound.  Maximal projective spectral rank, rather than the
strictly stronger and physically inappropriate independence of all energies,
then gives the completed-time static Choi plateau.  In particular the theorem
applies to traceless Hamiltonians.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower

/-- Split a finite phase packet into its zeroth global phase and all phases
relative to that coordinate. -/
def zeroRelativePhaseEquiv (d : ℕ) :
    (Fin (d + 1) → UnitAddCircle) ≃+
      UnitAddCircle × (Fin d → UnitAddCircle) where
  toFun x := (x 0, fun j ↦ x j.succ - x 0)
  invFun y := Fin.cases y.1 (fun j ↦ y.2 j + y.1)
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simp
  right_inv y := by
    ext
    · simp
    · simp
  map_add' x y := by
    ext
    · simp
    · simp
      abel

theorem continuous_zeroRelativePhaseEquiv (d : ℕ) :
    Continuous (zeroRelativePhaseEquiv d :
      (Fin (d + 1) → UnitAddCircle) →
        UnitAddCircle × (Fin d → UnitAddCircle)) := by
  change Continuous (fun x : Fin (d + 1) → UnitAddCircle ↦
    (x 0, fun j : Fin d ↦ x j.succ - x 0))
  exact (continuous_apply 0).prodMk (by
    apply continuous_pi
    intro j
    exact (continuous_apply j.succ).sub (continuous_apply 0))

/-- Global-phase splitting preserves normalized Haar measure exactly. -/
theorem measurePreserving_zeroRelativePhaseEquiv (d : ℕ) :
    MeasurePreserving (zeroRelativePhaseEquiv d :
      (Fin (d + 1) → UnitAddCircle) →
        UnitAddCircle × (Fin d → UnitAddCircle))
      (volume : Measure (Fin (d + 1) → UnitAddCircle))
      ((volume : Measure UnitAddCircle).prod
        (volume : Measure (Fin d → UnitAddCircle))) := by
  letI : ((volume : Measure UnitAddCircle).prod
      (volume : Measure (Fin d → UnitAddCircle))).IsAddHaarMeasure :=
    MeasureTheory.Measure.prod.instIsAddHaarMeasure
      (volume : Measure UnitAddCircle)
      (volume : Measure (Fin d → UnitAddCircle))
  apply (zeroRelativePhaseEquiv d).toAddMonoidHom.measurePreserving
      (continuous_zeroRelativePhaseEquiv d)
      (zeroRelativePhaseEquiv d).surjective
  have hunivProd :
      (Set.univ : Set (UnitAddCircle × (Fin d → UnitAddCircle))) =
        Set.univ ×ˢ Set.univ := by
    ext
    simp
  have hfull :
      (volume : Measure (Fin (d + 1) → UnitAddCircle)) Set.univ = 1 := by
    change Measure.pi (fun _ : Fin (d + 1) ↦
      (volume : Measure UnitAddCircle)) Set.univ = 1
    rw [Measure.pi_univ]
    simp
  have hrelative :
      (volume : Measure (Fin d → UnitAddCircle)) Set.univ = 1 := by
    change Measure.pi (fun _ : Fin d ↦
      (volume : Measure UnitAddCircle)) Set.univ = 1
    rw [Measure.pi_univ]
    simp
  rw [hunivProd, Measure.prod_prod, hfull,
    UnitAddCircle.measure_univ, hrelative]
  norm_num

/-- Insert a zero global phase before the projective coordinates. -/
def zeroAnchoredPhase (d : ℕ)
    (x : Fin d → UnitAddCircle) : Fin (d + 1) → UnitAddCircle :=
  Fin.cases 0 x

theorem zeroRelativePhaseEquiv_symm_eq_anchored_add
    (d : ℕ) (y : UnitAddCircle × (Fin d → UnitAddCircle)) :
    (zeroRelativePhaseEquiv d).symm y =
      fun i ↦ zeroAnchoredPhase d y.2 i + y.1 := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [zeroRelativePhaseEquiv,
    zeroAnchoredPhase]

/-- A common spectral phase cancels exactly from a pure-state Choi density. -/
theorem uniformPhaseDensity_add_common
    (d : ℕ) (x : Fin d → UnitAddCircle) (a : UnitAddCircle) :
    uniformPhaseDensity d (fun i ↦ x i + a) =
      uniformPhaseDensity d x := by
  ext ij
  simp only [uniformPhaseDensity_apply]
  rw [fourier_one, fourier_one, fourier_one, fourier_one,
    AddCircle.toCircle_add, AddCircle.toCircle_add, Circle.coe_mul,
    Circle.coe_mul, map_mul]
  have ha : (AddCircle.toCircle a : ℂ) *
      starRingEnd ℂ (AddCircle.toCircle a : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp
  rw [show
      ((d : ℝ)⁻¹ : ℂ) *
          ((AddCircle.toCircle (x ij.1) : ℂ) *
            (AddCircle.toCircle a : ℂ)) *
          (starRingEnd ℂ (AddCircle.toCircle (x ij.2) : ℂ) *
            starRingEnd ℂ (AddCircle.toCircle a : ℂ)) =
        (((d : ℝ)⁻¹ : ℂ) * (AddCircle.toCircle (x ij.1) : ℂ) *
          starRingEnd ℂ (AddCircle.toCircle (x ij.2) : ℂ)) *
          ((AddCircle.toCircle a : ℂ) *
            starRingEnd ℂ (AddCircle.toCircle a : ℂ)) by ring]
  rw [ha, mul_one]

/-- Pullback of a Choi-density metric ball to the zero-anchored projective
phase torus. -/
def zeroAnchoredMetricBallTarget (d : ℕ)
    (c : EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1))) (δ : ℝ) :
    Set (Fin d → UnitAddCircle) :=
  {x | dist (uniformPhaseDensity (d + 1) (zeroAnchoredPhase d x)) c ≤ δ}

theorem measurableSet_zeroAnchoredMetricBallTarget (d : ℕ)
    (c : EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1))) (δ : ℝ) :
    MeasurableSet (zeroAnchoredMetricBallTarget d c δ) := by
  apply IsClosed.measurableSet
  rw [zeroAnchoredMetricBallTarget]
  apply isClosed_le
  · apply Continuous.dist
    · exact (continuous_uniformPhaseDensity (d + 1)).comp (by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact continuous_const
        · exact continuous_apply j)
    · exact continuous_const
  · exact continuous_const

/-- A single projective Choi target has exactly the Haar mass of its
global-phase-invariant full-torus lift. -/
theorem volume_zeroAnchoredMetricBallTarget_eq_full
    (d : ℕ)
    (c : EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1))) (δ : ℝ) :
    volume (zeroAnchoredMetricBallTarget d c δ) =
      volume (torusMetricBallTarget (uniformPhaseDensity (d + 1)) c δ) := by
  let B := zeroAnchoredMetricBallTarget d c δ
  let A := torusMetricBallTarget (uniformPhaseDensity (d + 1)) c δ
  have hB : MeasurableSet B := measurableSet_zeroAnchoredMetricBallTarget d c δ
  have hpre : (zeroRelativePhaseEquiv d :
      (Fin (d + 1) → UnitAddCircle) →
        UnitAddCircle × (Fin d → UnitAddCircle)) ⁻¹' (Set.univ ×ˢ B) = A := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    simp only [B, A, zeroAnchoredMetricBallTarget, torusMetricBallTarget,
      Set.mem_setOf_eq]
    have hdensity :
        uniformPhaseDensity (d + 1) x =
          uniformPhaseDensity (d + 1)
            (zeroAnchoredPhase d (zeroRelativePhaseEquiv d x).2) := by
      calc
        _ = uniformPhaseDensity (d + 1)
            ((zeroRelativePhaseEquiv d).symm
              (zeroRelativePhaseEquiv d x)) := by
              rw [(zeroRelativePhaseEquiv d).symm_apply_apply]
        _ = uniformPhaseDensity (d + 1)
            (fun i ↦ zeroAnchoredPhase d
              (zeroRelativePhaseEquiv d x).2 i +
                (zeroRelativePhaseEquiv d x).1) := by
              rw [zeroRelativePhaseEquiv_symm_eq_anchored_add]
        _ = _ := uniformPhaseDensity_add_common _ _ _
    rw [hdensity]
  have hmeasure := (measurePreserving_zeroRelativePhaseEquiv d).measure_preimage
    (MeasurableSet.univ.prod hB).nullMeasurableSet
  rw [hpre] at hmeasure
  change volume A =
    ((volume : Measure UnitAddCircle).prod
      (volume : Measure (Fin d → UnitAddCircle))) (Set.univ ×ˢ B)
      at hmeasure
  rw [Measure.prod_prod, UnitAddCircle.measure_univ, one_mul] at hmeasure
  exact hmeasure.symm

/-- Relative energy frequencies with the physical `exp (-i t H)` sign. -/
def zeroProjectiveFrequency {d : ℕ}
    (energy : Fin (d + 1) → ℝ) (i : Fin d) : ℝ :=
  energy 0 - energy i.succ

/-- Maximal projective spectral rank is exactly strong enough to make the
zero-anchored physical frequency packet rationally independent. -/
theorem maximallyProjectiveEnergy_zeroProjectiveFrequency_independent
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : GaloisForLFunctions.HTGeometry.MaximallyProjectiveEnergy energy) :
    GaloisForLFunctions.HTGeometry.RationallyIndependentFrequency
      (zeroProjectiveFrequency energy) := by
  intro n hdetuning
  let k : Fin (d + 1) → ℤ :=
    Fin.cases (∑ i, n i) (fun i ↦ -n i)
  have hbalanced :
      GaloisForLFunctions.HTGeometry.SpectralCharacterBalanced k := by
    unfold GaloisForLFunctions.HTGeometry.SpectralCharacterBalanced
    rw [Fin.sum_univ_succ]
    simp [k]
  have henergy :
      (∑ j, (k j : ℝ) * energy j) = 0 := by
    rw [Fin.sum_univ_succ]
    change (((∑ i, n i) : ℤ) : ℝ) * energy 0 +
      ∑ i, ((-n i : ℤ) : ℝ) * energy i.succ = 0
    push_cast
    rw [GaloisForLFunctions.HTGeometry.finiteTorusCharacterDetuning]
      at hdetuning
    change (∑ i, (n i : ℝ) *
      (energy 0 - energy i.succ)) = 0 at hdetuning
    simp_rw [mul_sub] at hdetuning
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hdetuning
    linarith
  have hk := hmax k hbalanced henergy
  funext i
  have hi := congrFun hk i.succ
  simpa [k] using congrArg Neg.neg hi

/-- Complete low-complexity target on the projective phase torus. -/
def zeroAnchoredPaddedCircuitTarget
    (d : ℕ) {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (δ : ℝ) : Set (Fin d → UnitAddCircle) :=
  ⋃ w, zeroAnchoredMetricBallTarget d (target w) δ

theorem isClosed_zeroAnchoredMetricBallTarget
    (d : ℕ)
    (c : EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1))) (δ : ℝ) :
    IsClosed (zeroAnchoredMetricBallTarget d c δ) := by
  rw [zeroAnchoredMetricBallTarget]
  apply isClosed_le
  · apply Continuous.dist
    · exact (continuous_uniformPhaseDensity (d + 1)).comp (by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact continuous_const
        · exact continuous_apply j)
    · exact continuous_const
  · exact continuous_const

theorem isClosed_zeroAnchoredPaddedCircuitTarget
    (d : ℕ) {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (δ : ℝ) :
    IsClosed (zeroAnchoredPaddedCircuitTarget d s target δ) := by
  rw [zeroAnchoredPaddedCircuitTarget]
  exact isClosed_iUnion_of_finite fun w ↦
    isClosed_zeroAnchoredMetricBallTarget d (target w) δ

/-- The entire finite circuit union has exactly the mass of its full-torus
lift; equality survives overlaps between circuit balls. -/
theorem volume_zeroAnchoredPaddedCircuitTarget_eq_full
    (d : ℕ) {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (δ : ℝ) :
    volume (zeroAnchoredPaddedCircuitTarget d s target δ) =
      volume (⋃ w, torusMetricBallTarget
        (uniformPhaseDensity (d + 1)) (target w) δ) := by
  let B := zeroAnchoredPaddedCircuitTarget d s target δ
  let A := ⋃ w, torusMetricBallTarget
    (uniformPhaseDensity (d + 1)) (target w) δ
  have hB : MeasurableSet B :=
    (isClosed_zeroAnchoredPaddedCircuitTarget d s target δ).measurableSet
  have hpre : (zeroRelativePhaseEquiv d :
      (Fin (d + 1) → UnitAddCircle) →
        UnitAddCircle × (Fin d → UnitAddCircle)) ⁻¹' (Set.univ ×ˢ B) = A := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    have hdensity :
        uniformPhaseDensity (d + 1) x =
          uniformPhaseDensity (d + 1)
            (zeroAnchoredPhase d (zeroRelativePhaseEquiv d x).2) := by
      calc
        _ = uniformPhaseDensity (d + 1)
            ((zeroRelativePhaseEquiv d).symm
              (zeroRelativePhaseEquiv d x)) := by
              rw [(zeroRelativePhaseEquiv d).symm_apply_apply]
        _ = uniformPhaseDensity (d + 1)
            (fun i ↦ zeroAnchoredPhase d
              (zeroRelativePhaseEquiv d x).2 i +
                (zeroRelativePhaseEquiv d x).1) := by
              rw [zeroRelativePhaseEquiv_symm_eq_anchored_add]
        _ = _ := uniformPhaseDensity_add_common _ _ _
    constructor
    · intro hx
      rw [B, zeroAnchoredPaddedCircuitTarget, Set.mem_iUnion] at hx
      obtain ⟨w, hw⟩ := hx
      rw [A, Set.mem_iUnion]
      refine ⟨w, ?_⟩
      change dist (uniformPhaseDensity (d + 1) x) (target w) ≤ δ
      rw [hdensity]
      exact hw
    · intro hx
      rw [A, Set.mem_iUnion] at hx
      obtain ⟨w, hw⟩ := hx
      rw [B, zeroAnchoredPaddedCircuitTarget, Set.mem_iUnion]
      refine ⟨w, ?_⟩
      change dist
        (uniformPhaseDensity (d + 1)
          (zeroAnchoredPhase d (zeroRelativePhaseEquiv d x).2))
        (target w) ≤ δ
      rw [← hdensity]
      exact hw
  have hmeasure := (measurePreserving_zeroRelativePhaseEquiv d).measure_preimage
    (MeasurableSet.univ.prod hB).nullMeasurableSet
  rw [hpre] at hmeasure
  change volume A =
    ((volume : Measure UnitAddCircle).prod
      (volume : Measure (Fin d → UnitAddCircle))) (Set.univ ×ˢ B)
      at hmeasure
  rw [Measure.prod_prod, UnitAddCircle.measure_univ, one_mul] at hmeasure
  exact hmeasure.symm

/-- Explicit circuit entropy bound on the physical projective phase torus. -/
theorem measureReal_zeroAnchoredPaddedCircuitTarget_le
    (d : ℕ) {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    {δ : ℝ} (hδ : 0 < δ) :
    volume.real (zeroAnchoredPaddedCircuitTarget d s target δ) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
          Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ ((d + 1 : ℕ) - 1)) := by
  rw [measureReal_def, volume_zeroAnchoredPaddedCircuitTarget_eq_full,
    ← measureReal_def]
  exact measureReal_iUnion_uniformPhaseDensity_paddedCircuitTargets_le
    (Nat.succ_pos d) s target hδ

/-- **Projective completed-time static Choi plateau law.** Every maximally
projective finite spectrum spends at most the explicitly bounded Haar fraction
of completed time inside any fixed finite-gate circuit dictionary.  No
independence of the common energy mode is assumed. -/
theorem completedTime_zeroAnchoredPaddedCircuitTargets
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : GaloisForLFunctions.HTGeometry.MaximallyProjectiveEnergy energy)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    {δ : ℝ} (hδ : 0 < δ) :
    let A := zeroAnchoredPaddedCircuitTarget d s target δ
    atTop.limsup (fun T ↦
        (GaloisForLFunctions.HTGeometry.finiteTorusPhaseProbabilityMeasure
          (zeroProjectiveFrequency energy) T :
            Measure (UnitAddTorus (Fin d))) A) ≤ volume A ∧
      volume.real A ≤
        (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^
              ((d + 1 : ℕ) - 1)) := by
  dsimp only
  constructor
  · apply GaloisForLFunctions.HTGeometry.rationallyIndependent_closedTarget_limsup_le_volume
      (zeroProjectiveFrequency energy)
      (maximallyProjectiveEnergy_zeroProjectiveFrequency_independent energy hmax)
    exact isClosed_zeroAnchoredPaddedCircuitTarget d s target δ
  · exact measureReal_zeroAnchoredPaddedCircuitTarget_le d s target hδ

end RHTower
