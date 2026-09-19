import GaloisForLFunctions.RHTower.WeilInsertionAnyWeight

/-!
# The restricted Weil operator with finitely many prime weights changed

For finitely many scales `x i > 1` and real weights `w i`, the block
`∑ i, w i · x i^{-1/2} (τ_{log x i} + τ_{−log x i})` is added to the finite prime block of the
restricted Weil operator.  The resulting remainders form an aperture-compatible family, so the
ground-energy theory of `CCMRemainderFamily` applies.  The family's ground energy exceeds the
literal one by at most `∑ i, |w i| · 2/√(x i)`, hence it is unbounded below if the Riemann
hypothesis fails; and on the modulated wide bump its Rayleigh floor is the literal zero side minus
`∑ i, w i · x i^{-1/2} · 2 cos(ζ log x i) · overlap(L, log x i)`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilDeletion

/-- Finitely many changes of prime weights: scales `x i > 1` and real weights `w i`. -/
structure FinitePrimePerturbation (k : ℕ) where
  x : Fin k → ℝ
  w : Fin k → ℝ
  one_lt : ∀ i, 1 < x i

variable {k : ℕ}

/-- The sum of the inserted blocks. -/
def ccmFiniteBlock (a : SuzukiPositiveAperture) (P : FinitePrimePerturbation k) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ∑ i, ccmInsertedBlock a (P.x i) (P.w i)

theorem ccmFiniteBlock_isSelfAdjoint (a : SuzukiPositiveAperture) (P : FinitePrimePerturbation k) :
    IsSelfAdjoint (ccmFiniteBlock a P) := by
  unfold ccmFiniteBlock
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, ContinuousLinearMap.adjoint.map_add, ih]
    have := ccmInsertedBlock_isSelfAdjoint a (P.x j) (P.w j)
    rw [ContinuousLinearMap.isSelfAdjoint_iff'] at this
    rw [this]

/-- The bounded remainder with the finite block removed from the prime side. -/
def ccmFiniteRemainder (a : SuzukiPositiveAperture) (P : FinitePrimePerturbation k) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmRestrictedWeilBoundedRemainder a - ccmFiniteBlock a P

theorem ccmFiniteRemainder_isSelfAdjoint (a : SuzukiPositiveAperture)
    (P : FinitePrimePerturbation k) : IsSelfAdjoint (ccmFiniteRemainder a P) := by
  unfold ccmFiniteRemainder
  have h1 := ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a
  have h2 := ccmFiniteBlock_isSelfAdjoint a P
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at h1 h2 ⊢
  rw [ContinuousLinearMap.adjoint.map_sub, h1, h2]

theorem re_inner_ccmFiniteBlock (a : SuzukiPositiveAperture) (P : FinitePrimePerturbation k)
    (f : suzukiApertureHilbert a) :
    (inner ℂ (ccmFiniteBlock a P f) f).re =
      ∑ i, (inner ℂ (ccmInsertedBlock a (P.x i) (P.w i) f) f).re := by
  unfold ccmFiniteBlock
  rw [sum_apply, sum_inner, Complex.re_sum]

/-- The finitely perturbed remainders as an aperture-compatible family. -/
def finiteFamily (P : FinitePrimePerturbation k) : CCMRemainderFamily where
  B a := ccmFiniteRemainder a P
  selfAdjoint a := ccmFiniteRemainder_isSelfAdjoint a P
  compat := by
    intro a b hab u v hvu
    unfold ccmFiniteRemainder
    rw [sub_apply, sub_apply, inner_sub_left, inner_sub_left, Complex.sub_re, Complex.sub_re,
      literal_diagonal_eq_of_val_eq hab hvu, re_inner_ccmFiniteBlock, re_inner_ccmFiniteBlock]
    congr 1
    exact Finset.sum_congr rfl fun i _ => inserted_diagonal_eq_of_val_eq _ _ hab hvu

theorem finiteFamily_Q_eq (P : FinitePrimePerturbation k) (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (finiteFamily P).Q a u = ccmRestrictedWeilSourceQuadratic a u -
      ∑ i, (inner ℂ (ccmInsertedBlock a (P.x i) (P.w i) (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re := by
  rw [CCMRemainderFamily.Q_eq_form_re]
  show (inner ℂ u u + inner ℂ (ccmFiniteRemainder a P (ccmArchimedeanFormToAperture a u))
    (ccmArchimedeanFormToAperture a u)).re = _
  unfold ccmFiniteRemainder
  rw [sub_apply, inner_sub_left, ← add_sub_assoc, Complex.sub_re, re_inner_ccmFiniteBlock]
  congr 1
  exact ccmRestrictedWeilForm_self_re_eq_source a u

theorem literalFamily_Q_eq (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    literalFamily.Q a u = ccmRestrictedWeilSourceQuadratic a u := by
  rw [CCMRemainderFamily.Q_eq_form_re]
  exact ccmRestrictedWeilForm_self_re_eq_source a u

/-- The Rayleigh floor of the finite family. -/
theorem finiteFamily_energy_mul_le (P : FinitePrimePerturbation k) (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (finiteFamily P).energy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u -
        ∑ i, (inner ℂ (ccmInsertedBlock a (P.x i) (P.w i) (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re := by
  have := (finiteFamily P).energy_mul_formNorm_sq_le a u
  rwa [finiteFamily_Q_eq] at this

/-- The total operator-norm budget of the finite block. -/
def finiteBlockBudget (P : FinitePrimePerturbation k) : ℝ :=
  ∑ i, |P.w i| * (2 / Real.sqrt (P.x i))

theorem finiteBlockBudget_nonneg (P : FinitePrimePerturbation k) : 0 ≤ finiteBlockBudget P :=
  Finset.sum_nonneg fun i _ => by positivity

theorem finiteFamily_Q_le (P : FinitePrimePerturbation k) (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (finiteFamily P).Q a u ≤
      literalFamily.Q a u + finiteBlockBudget P * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  rw [finiteFamily_Q_eq, literalFamily_Q_eq]
  unfold finiteBlockBudget
  rw [Finset.sum_mul]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      -(inner ℂ (ccmInsertedBlock a (P.x i) (P.w i) (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re ≤
      |P.w i| * (2 / Real.sqrt (P.x i)) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    intro i _
    have hb := abs_re_inner_insertedBlock_le a (P.x i) (P.w i) (by linarith [P.one_lt i])
      (ccmArchimedeanFormToAperture a u)
    have := neg_abs_le (inner ℂ (ccmInsertedBlock a (P.x i) (P.w i)
      (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a u)).re
    linarith
  have hs := Finset.sum_le_sum hterm
  rw [Finset.sum_neg_distrib] at hs
  linarith

/-- The finite family's ground energy exceeds the literal one by at most the block budget. -/
theorem finiteFamily_energy_le (P : FinitePrimePerturbation k) (a : SuzukiPositiveAperture) :
    (finiteFamily P).energy a ≤ ccmRestrictedWeilGroundEnergy a + finiteBlockBudget P := by
  rw [← literalFamily_energy]
  exact CCMRemainderFamily.energy_le_energy_add_of_Q_le literalFamily (finiteFamily P) a
    (finiteFamily_Q_le P a)

/-- If the Riemann hypothesis fails, every finite perturbation has negative ground energy at some
aperture. -/
theorem exists_finiteFamily_energy_neg_of_not_riemannHypothesis (P : FinitePrimePerturbation k)
    (hRH : ¬ RiemannHypothesis) : ∃ a : SuzukiPositiveAperture, (finiteFamily P).energy a < 0 := by
  obtain ⟨a, ha⟩ := exists_ccmRestrictedWeilGroundEnergy_lt_of_not_riemannHypothesis hRH
    (finiteBlockBudget_nonneg P)
  exact ⟨a, by linarith [finiteFamily_energy_le P a]⟩

/-! ## The Rayleigh floor on the modulated wide bump -/

/-- The block pairing of a visible scale on the modulated bump. -/
theorem re_inner_insertedBlock_modulatedBump {L : ℝ} (hL : 1 ≤ L) (ζ : ℝ) {x : ℝ} (w : ℝ)
    (hvis : x ≤ Real.exp (2 * (wideBumpAperture L hL).1)) :
    (inner ℂ (ccmInsertedBlock (wideBumpAperture L hL) x w
      (ccmArchimedeanFormToAperture _ (modulatedBumpSource L hL ζ).toCCMFormVector))
      (ccmArchimedeanFormToAperture _ (modulatedBumpSource L hL ζ).toCCMFormVector)).re =
      w * (1 / Real.sqrt x) * (2 * Real.cos (ζ * Real.log x) * bumpOverlap L (Real.log x)) := by
  rw [re_inner_insertedBlock_eq _ x w _ hvis, re_inner_symmetric_modulatedBump _
    (modulatedBumpSource L hL ζ).toCCMFormVector_physical_coeFn]

/-- The Rayleigh floor of the finite family on the modulated wide bump, all scales visible. -/
theorem finiteFamily_energy_mul_le_modulatedBump (P : FinitePrimePerturbation k) {L : ℝ}
    (hL : 1 ≤ L) (ζ : ℝ) (hvis : ∀ i, P.x i ≤ Real.exp (2 * (wideBumpAperture L hL).1)) :
    (finiteFamily P).energy (wideBumpAperture L hL) *
      ‖ccmArchimedeanFormToAperture _ (modulatedBumpSource L hL ζ).toCCMFormVector‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic _ (modulatedBumpSource L hL ζ).toCCMFormVector -
        ∑ i, P.w i * (1 / Real.sqrt (P.x i)) *
          (2 * Real.cos (ζ * Real.log (P.x i)) * bumpOverlap L (Real.log (P.x i))) := by
  have h := finiteFamily_energy_mul_le P (wideBumpAperture L hL)
    (modulatedBumpSource L hL ζ).toCCMFormVector
  have hsum : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      (inner ℂ (ccmInsertedBlock (wideBumpAperture L hL) (P.x i) (P.w i)
        (ccmArchimedeanFormToAperture _ (modulatedBumpSource L hL ζ).toCCMFormVector))
        (ccmArchimedeanFormToAperture _ (modulatedBumpSource L hL ζ).toCCMFormVector)).re =
      P.w i * (1 / Real.sqrt (P.x i)) *
        (2 * Real.cos (ζ * Real.log (P.x i)) * bumpOverlap L (Real.log (P.x i))) :=
    fun i _ => re_inner_insertedBlock_modulatedBump hL ζ (P.w i) (hvis i)
  rw [Finset.sum_congr rfl hsum] at h
  exact h

end RHTower.WeilDeletion

end
