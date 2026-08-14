import GaloisForLFunctions.HTGeometry.FiniteGridCoherenceMoment
import GaloisForLFunctions.RHTower.AdaptiveCircuitShortcutActionLaw

/-!
# Finite-grid Choi caps for arbitrary normalized rays

Prime-torsion phase grids are embedded into the normalized diagonal Choi
manifold.  Any trace-distance cap about an arbitrary normalized state is
contained in one translated coherence cap as soon as it captures one grid
point.  Consequently an arbitrary finite circuit dictionary costs only its
cardinality in the grid union bound; target rays need not lie on the diagonal
manifold or on the phase grid.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Lift a finite cyclic phase to the unit additive circle. -/
def zmodUnitAddCirclePhase (M : ℕ) [NeZero M] (x : ZMod M) : UnitAddCircle :=
  (AddCircle.homeomorphCircle one_ne_zero).symm (ZMod.toCircle x)

/-- The lifted phase has the standard finite cyclic additive character. -/
theorem fourier_zmodUnitAddCirclePhase
    (M : ℕ) [NeZero M] (x : ZMod M) :
    fourier 1 (zmodUnitAddCirclePhase M x) = ZMod.stdAddChar x := by
  rw [fourier_apply, ZMod.stdAddChar_apply]
  simp only [one_smul]
  have hcircle :=
    (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply (ZMod.toCircle x)
  exact congrArg Subtype.val
    ((AddCircle.homeomorphCircle_apply one_ne_zero _).symm.trans hcircle)

/-- Uniform Born weight on the `d` diagonal Choi coordinates. -/
def finiteGridChoiWeight (d : ℕ) (_ : Fin d) : ℝ :=
  (d : ℝ)⁻¹

theorem finiteGridChoiWeight_nonneg (d : ℕ) (i : Fin d) :
    0 ≤ finiteGridChoiWeight d i := by
  simp only [finiteGridChoiWeight]
  positivity

theorem finiteGridChoiWeight_sq_sum
    {d : ℕ} (hd : 0 < d) :
    ∑ i : Fin d, finiteGridChoiWeight d i ^ 2 = (d : ℝ)⁻¹ := by
  simp only [finiteGridChoiWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

/-- Normalized diagonal Choi vector attached to a finite cyclic phase grid. -/
def finiteGridChoiVector
    (M d : ℕ) [NeZero M] (x : Fin d → ZMod M) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  fullUniformPhaseChoiVector d fun i => zmodUnitAddCirclePhase M (x i)

theorem finiteGridChoiVector_norm
    {M d : ℕ} [NeZero M] (hd : 0 < d) (x : Fin d → ZMod M) :
    ‖finiteGridChoiVector M d x‖ = 1 :=
  fullUniformPhaseChoiVector_norm hd _

private theorem stdAddChar_mul_conj
    {M : ℕ} [NeZero M] (x y : ZMod M) :
    ZMod.stdAddChar x * starRingEnd ℂ (ZMod.stdAddChar y) =
      ZMod.stdAddChar (x - y) := by
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, sub_eq_add_neg]

/-- Relative phase coherence is exactly the overlap of two finite-grid Choi
vectors. -/
theorem inner_finiteGridChoiVector_eq_uniformCoherence
    {M d : ℕ} [NeZero M] (hd : 0 < d)
    (center x : Fin d → ZMod M) :
    inner ℂ (finiteGridChoiVector M d center)
        (finiteGridChoiVector M d x) =
      ∑ i, (finiteGridChoiWeight d i : ℂ) *
        ZMod.stdAddChar (x i - center i) := by
  rw [EuclideanSpace.inner_toLp_toLp]
  change
    (∑ ij : Fin d × Fin d,
      (if ij.1 = ij.2 then
          ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
            fourier 1 (zmodUnitAddCirclePhase M (x ij.1))
        else 0) *
      starRingEnd ℂ
        (if ij.1 = ij.2 then
            ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
              fourier 1 (zmodUnitAddCirclePhase M (center ij.1))
          else 0)) =
      ∑ i, (finiteGridChoiWeight d i : ℂ) *
        ZMod.stdAddChar (x i - center i)
  rw [Fintype.sum_prod_type]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hdR)
  have hreal :
      (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
        (d : ℝ)⁻¹ := by
    field_simp [hsqrt]
    simpa [pow_two] using (Real.mul_self_sqrt hdR.le).symm
  have hcoef :
      (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ))) =
        (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [starRingEnd_apply, Complex.star_def, map_inv₀, Complex.conj_ofReal]
    exact_mod_cast hreal
  simp_rw [fourier_zmodUnitAddCirclePhase]
  simp_rw [apply_ite (starRingEnd ℂ)]
  simp only [map_zero, ite_mul, zero_mul]
  have hdiag (i j : Fin d) :
      (if i = j then
          ((Real.sqrt (d : ℝ))⁻¹ : ℂ) * ZMod.stdAddChar (x i) *
            if i = j then
              starRingEnd ℂ
                (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
                  ZMod.stdAddChar (center i))
            else 0
        else 0) =
        if i = j then
          (((Real.sqrt (d : ℝ))⁻¹ : ℂ) * ZMod.stdAddChar (x i)) *
            starRingEnd ℂ
              (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
                ZMod.stdAddChar (center i))
        else 0 := by
    by_cases hij : i = j <;> simp [hij]
  simp_rw [hdiag]
  simp only [Fintype.sum_ite_eq]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_mul]
  calc
    (((Real.sqrt (d : ℝ))⁻¹ : ℂ) * ZMod.stdAddChar (x i)) *
          (starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ)) *
            starRingEnd ℂ (ZMod.stdAddChar (center i))) =
        ((((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
            starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ))) *
          (ZMod.stdAddChar (x i) *
            starRingEnd ℂ (ZMod.stdAddChar (center i)))) := by ring
    _ = (((d : ℝ)⁻¹ : ℝ) : ℂ) *
          ZMod.stdAddChar (x i - center i) := by
        rw [hcoef, stdAddChar_mul_conj]
    _ = (finiteGridChoiWeight d i : ℂ) *
          ZMod.stdAddChar (x i - center i) := by
        rfl

/-- Grid points captured within trace distance `epsilon` by an arbitrary
normalized target ray. -/
def finiteGridChoiRayCaptureSet
    (M d : ℕ) [NeZero M]
    (target : EuclideanSpace ℂ (Fin d × Fin d)) (epsilon : ℝ) :
    Finset (Fin d → ZMod M) :=
  Finset.univ.filter fun x =>
    pureStateTraceDistance (finiteGridChoiVector M d x) target ≤ epsilon

/-- If an arbitrary ray cap captures `center`, every other captured grid
point lies in the translated coherence cap about `center`. -/
theorem finiteGridChoiRayCapture_subset_translatedCoherenceCap
    {M d : ℕ} [NeZero M] (hd : 0 < d)
    {target : EuclideanSpace ℂ (Fin d × Fin d)} (htarget : ‖target‖ = 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    {center : Fin d → ZMod M}
    (hcenter : center ∈ finiteGridChoiRayCaptureSet M d target epsilon) :
    finiteGridChoiRayCaptureSet M d target epsilon ⊆
      finiteGridTranslatedCoherenceCap M (finiteGridChoiWeight d)
        (Real.sqrt (1 - 4 * epsilon ^ 2)) center := by
  intro x hx
  have hx' : pureStateTraceDistance
      (finiteGridChoiVector M d x) target ≤ epsilon := by
    simpa [finiteGridChoiRayCaptureSet] using hx
  have hcenter' : pureStateTraceDistance
      (finiteGridChoiVector M d center) target ≤ epsilon := by
    simpa [finiteGridChoiRayCaptureSet] using hcenter
  have htargetCenter : pureStateTraceDistance target
      (finiteGridChoiVector M d center) ≤ epsilon := by
    rw [pureStateTraceDistance_comm]
    exact hcenter'
  have hbetween : pureStateTraceDistance
      (finiteGridChoiVector M d x)
      (finiteGridChoiVector M d center) ≤ 2 * epsilon := by
    calc
      _ ≤ pureStateTraceDistance (finiteGridChoiVector M d x) target +
          pureStateTraceDistance target (finiteGridChoiVector M d center) :=
        pureStateTraceDistance_triangle _ _ _
          (finiteGridChoiVector_norm hd x) htarget
          (finiteGridChoiVector_norm hd center)
      _ ≤ epsilon + epsilon := add_le_add hx' htargetCenter
      _ = 2 * epsilon := by ring
  have hcoherence :=
    norm_inner_ge_sqrt_one_sub_four_mul_sq_of_traceDistance_le
      (finiteGridChoiVector M d x) (finiteGridChoiVector M d center)
      (finiteGridChoiVector_norm hd x)
      (finiteGridChoiVector_norm hd center)
      hepsilon hepsilonHalf hbetween
  rw [norm_inner_symm,
    inner_finiteGridChoiVector_eq_uniformCoherence hd center x] at hcoherence
  rw [mem_finiteGridTranslatedCoherenceCap_iff]
  exact hcoherence

/-- An arbitrary normalized-ray cap contains no more phase-grid points than
one coherence cap. -/
theorem finiteGridChoiRayCaptureSet_card_le_coherenceCap
    {M d : ℕ} [NeZero M] (hd : 0 < d)
    {target : EuclideanSpace ℂ (Fin d × Fin d)} (htarget : ‖target‖ = 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    (finiteGridChoiRayCaptureSet M d target epsilon).card ≤
      (finiteGridCoherenceCap M (finiteGridChoiWeight d)
        (Real.sqrt (1 - 4 * epsilon ^ 2))).card := by
  by_cases hempty : finiteGridChoiRayCaptureSet M d target epsilon = ∅
  · simp [hempty]
  · obtain ⟨center, hcenter⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    calc
      _ ≤ (finiteGridTranslatedCoherenceCap M (finiteGridChoiWeight d)
          (Real.sqrt (1 - 4 * epsilon ^ 2)) center).card :=
        Finset.card_le_card
          (finiteGridChoiRayCapture_subset_translatedCoherenceCap hd htarget
            hepsilon hepsilonHalf hcenter)
      _ = _ := finiteGridTranslatedCoherenceCap_card M
        (finiteGridChoiWeight d) (Real.sqrt (1 - 4 * epsilon ^ 2)) center

/-- Union of arbitrary normalized-ray caps over a finite target dictionary. -/
def finiteGridChoiTargetCaptureSet
    {Y : Type*} [Fintype Y]
    (M d : ℕ) [NeZero M]
    (target : Y → EuclideanSpace ℂ (Fin d × Fin d)) (epsilon : ℝ) :
    Finset (Fin d → ZMod M) :=
  Finset.univ.biUnion fun y =>
    finiteGridChoiRayCaptureSet M d (target y) epsilon

/-- Complete arbitrary target union bound on the finite phase grid. -/
theorem finiteGridChoiTargetCaptureSet_card_le
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {M d : ℕ} [NeZero M] (hd : 0 < d)
    (target : Y → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ y, ‖target y‖ = 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    (finiteGridChoiTargetCaptureSet M d target epsilon).card ≤
      Fintype.card Y *
        (finiteGridCoherenceCap M (finiteGridChoiWeight d)
          (Real.sqrt (1 - 4 * epsilon ^ 2))).card := by
  unfold finiteGridChoiTargetCaptureSet
  calc
    _ ≤ ∑ y ∈ Finset.univ,
        (finiteGridChoiRayCaptureSet M d (target y) epsilon).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ Finset.univ,
        (finiteGridCoherenceCap M (finiteGridChoiWeight d)
          (Real.sqrt (1 - 4 * epsilon ^ 2))).card := by
      apply Finset.sum_le_sum
      intro y _hy
      exact finiteGridChoiRayCaptureSet_card_le_coherenceCap hd (htarget y)
        hepsilon hepsilonHalf
    _ = Fintype.card Y *
        (finiteGridCoherenceCap M (finiteGridChoiWeight d)
          (Real.sqrt (1 - 4 * epsilon ^ 2))).card := by simp

end RHTower
