import GaloisForLFunctions.HilbertMetric.FifthRootCurvatureMixture
import GaloisForLFunctions.RHTower.ThetaCuspCompletedProductFiberCofinalDropRepair
import GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceFifthRootCurvature

/-!
# Cofinal total-variance decomposition of theta fifth-root curvature

The completed product-fibre expansion separates the reflected theta product
into its first fibre and a cofinal higher tail.  The corresponding accumulated
drop therefore splits exactly.  Combining that split with the fifth-root law
of total variance gives an unconditional peeling identity for the literal
theta `C₅` numerator.

The endpoint flux and curvature of the distinguished fibre are left as
algebraic jet coordinates `d,j`.  This makes the identity valid even at the
absolute-value seams; on a smooth chamber they may be instantiated with the
actual first-fibre jets.  The remaining sign is then an exact cofinal
curvature-absorption problem, including the nonnegative projective-flux
mismatch square.
-/

namespace RHTower

noncomputable section

/-- Accumulated drop of the first completed product fibre. -/
def thetaCuspCompletedProductFiberFirstDrop (u t : ℝ) : ℝ :=
  thetaCuspCompletedProductFiberAmplitude 1 u 0 -
    thetaCuspCompletedProductFiberAmplitude 1 u t

/-- Accumulated drop of the cofinal completed product-fibre tail. -/
def thetaCuspCompletedProductFiberHigherTailDrop (u t : ℝ) : ℝ :=
  thetaCuspCompletedProductFiberHigherTail u 0 -
    thetaCuspCompletedProductFiberHigherTail u t

/-- Algebraic decay-flux jet of the completed first product fibre. -/
def thetaCuspCompletedProductFiberFirstDecayFlux (u t : ℝ) : ℝ :=
  -iteratedDeriv 1 (thetaCuspCompletedProductFiberAmplitude 1 u) t

/-- Algebraic flux-curvature jet of the completed first product fibre. -/
def thetaCuspCompletedProductFiberFirstDecayFluxCurvature (u t : ℝ) : ℝ :=
  -iteratedDeriv 2 (thetaCuspCompletedProductFiberAmplitude 1 u) t

/-- Fifth-root numerator of the completed first product fibre. -/
def thetaCuspCompletedProductFiberFirstFifthRootCurvatureNumerator
    (u t : ℝ) : ℝ :=
  HilbertMetric.fifthRootCurvatureJetForm t
    (thetaCuspCompletedProductFiberFirstDrop u t)
    (thetaCuspCompletedProductFiberFirstDecayFlux u t)
    (thetaCuspCompletedProductFiberFirstDecayFluxCurvature u t)

/-- Algebraic fifth-root numerator of the residual cofinal jet after the
literal first product-fibre jet is removed from the source jet. -/
def thetaCuspCompletedProductFiberHigherTailResidualFifthRootCurvatureNumerator
    (u t : ℝ) : ℝ :=
  HilbertMetric.fifthRootCurvatureJetForm t
    (thetaCuspCompletedProductFiberHigherTailDrop u t)
    (thetaCuspReflectedSourceDecayFlux u t -
      thetaCuspCompletedProductFiberFirstDecayFlux u t)
    (thetaCuspReflectedSourceDecayFluxCurvature u t -
      thetaCuspCompletedProductFiberFirstDecayFluxCurvature u t)

/-- The exact cofinal budget which must absorb first-fibre fifth-root
curvature and projective-flux mismatch in the first-fibre-rise chamber. -/
def thetaCuspCompletedProductFiberCofinalCurvatureAbsorptionBudget
    (u t : ℝ) : ℝ :=
  thetaCuspCompletedProductFiberHigherTailDrop u t *
      thetaCuspReflectedSourceFirstDrop u t *
      thetaCuspCompletedProductFiberFirstFifthRootCurvatureNumerator u t +
    thetaCuspCompletedProductFiberFirstDrop u t *
      thetaCuspReflectedSourceFirstDrop u t *
      thetaCuspCompletedProductFiberHigherTailResidualFifthRootCurvatureNumerator u t +
    4 * t ^ 2 *
      (thetaCuspCompletedProductFiberFirstDrop u t *
          thetaCuspReflectedSourceDecayFlux u t -
        thetaCuspReflectedSourceFirstDrop u t *
          thetaCuspCompletedProductFiberFirstDecayFlux u t) ^ 2

/-- Exact drop decomposition induced by the completed product-fibre sum. -/
theorem thetaCuspReflectedSourceFirstDrop_eq_firstFiber_add_higherTail
    (u t : ℝ) :
    thetaCuspReflectedSourceFirstDrop u t =
      thetaCuspCompletedProductFiberFirstDrop u t +
        thetaCuspCompletedProductFiberHigherTailDrop u t := by
  have hzero :=
    thetaCuspCompletedProductFiberAmplitude_one_add_higherTail u 0
  have ht :=
    thetaCuspCompletedProductFiberAmplitude_one_add_higherTail u t
  unfold thetaCuspReflectedSourceFirstDrop
    thetaCuspCompletedProductFiberFirstDrop
    thetaCuspCompletedProductFiberHigherTailDrop
  linarith

/-- The literal theta fifth-root numerator is the universal algebraic jet
form in its accumulated drop, decay flux, and flux curvature. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_jetForm
    (u t : ℝ) :
    thetaCuspReflectedSourceFifthRootCurvatureNumerator u t =
      HilbertMetric.fifthRootCurvatureJetForm t
        (thetaCuspReflectedSourceFirstDrop u t)
        (thetaCuspReflectedSourceDecayFlux u t)
        (thetaCuspReflectedSourceDecayFluxCurvature u t) := by
  rfl

/-- The first-fibre algebraic numerator is the universal functional
fifth-root numerator of that literal fibre. -/
theorem thetaCuspCompletedProductFiberFirstFifthRootCurvatureNumerator_eq_functional
    (u t : ℝ) :
    thetaCuspCompletedProductFiberFirstFifthRootCurvatureNumerator u t =
      HilbertMetric.fifthRootDividedDropCurvatureNumerator
        (thetaCuspCompletedProductFiberAmplitude 1 u) t := by
  rw [HilbertMetric.fifthRootDividedDropCurvatureNumerator_eq_jetForm]
  rfl

/-- **Cofinal fifth-root total-variance law.**  Peel the completed first
product fibre from the literal theta source.  The residual accumulated drop
is exactly the cofinal higher-fibre drop.  For any proposed first-fibre jet
`(d,j)`, the only interaction term is the square of the projective flux
mismatch.

This theorem has no sign, smoothness, or convergence hypotheses: convergence
entered earlier through the exact completed product-fibre decomposition. -/
theorem thetaCuspReflectedSourceFifthRootCurvature_peel_firstFiber
    (u t d j : ℝ) :
    thetaCuspCompletedProductFiberFirstDrop u t *
          thetaCuspCompletedProductFiberHigherTailDrop u t *
          thetaCuspReflectedSourceFifthRootCurvatureNumerator u t =
      thetaCuspCompletedProductFiberHigherTailDrop u t *
          thetaCuspReflectedSourceFirstDrop u t *
          HilbertMetric.fifthRootCurvatureJetForm t
            (thetaCuspCompletedProductFiberFirstDrop u t) d j +
        thetaCuspCompletedProductFiberFirstDrop u t *
          thetaCuspReflectedSourceFirstDrop u t *
          HilbertMetric.fifthRootCurvatureJetForm t
            (thetaCuspCompletedProductFiberHigherTailDrop u t)
            (thetaCuspReflectedSourceDecayFlux u t - d)
            (thetaCuspReflectedSourceDecayFluxCurvature u t - j) +
        4 * t ^ 2 *
          (thetaCuspCompletedProductFiberFirstDrop u t *
              thetaCuspReflectedSourceDecayFlux u t -
            thetaCuspReflectedSourceFirstDrop u t * d) ^ 2 := by
  have hpeel := HilbertMetric.fifthRootCurvatureJetForm_peel_totalVariance
    t
    (thetaCuspReflectedSourceFirstDrop u t)
    (thetaCuspReflectedSourceDecayFlux u t)
    (thetaCuspReflectedSourceDecayFluxCurvature u t)
    (thetaCuspCompletedProductFiberFirstDrop u t) d j
  rw [thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_jetForm]
  rw [thetaCuspReflectedSourceFirstDrop_eq_firstFiber_add_higherTail] at hpeel ⊢
  ring_nf at hpeel ⊢
  exact hpeel

/-- Literal first-fibre specialization of the cofinal total-variance law. -/
theorem thetaCuspReflectedSourceFifthRootCurvature_mul_firstFiber_higherTail_eq_budget
    (u t : ℝ) :
    thetaCuspCompletedProductFiberFirstDrop u t *
          thetaCuspCompletedProductFiberHigherTailDrop u t *
          thetaCuspReflectedSourceFifthRootCurvatureNumerator u t =
      thetaCuspCompletedProductFiberCofinalCurvatureAbsorptionBudget u t := by
  simpa [thetaCuspCompletedProductFiberCofinalCurvatureAbsorptionBudget,
    thetaCuspCompletedProductFiberFirstFifthRootCurvatureNumerator,
    thetaCuspCompletedProductFiberHigherTailResidualFifthRootCurvatureNumerator] using
    thetaCuspReflectedSourceFifthRootCurvature_peel_firstFiber u t
      (thetaCuspCompletedProductFiberFirstDecayFlux u t)
      (thetaCuspCompletedProductFiberFirstDecayFluxCurvature u t)

/-- The first-fibre-rise chamber is nonempty, and the cofinal higher-tail drop
is then strictly positive. -/
theorem exists_thetaCuspCompletedProductFiber_firstDrop_neg_higherTailDrop_pos :
    ∃ t : ℝ, 0 < t ∧
      thetaCuspCompletedProductFiberFirstDrop 0 t < 0 ∧
      0 < thetaCuspCompletedProductFiberHigherTailDrop 0 t := by
  obtain ⟨t, ht, hrise⟩ :=
    exists_thetaCuspCompletedProductFiberAmplitude_one_rise
  have hsource := thetaCuspReflectedSourceFirstDrop_pos 0 ht
  have hsplit :=
    thetaCuspReflectedSourceFirstDrop_eq_firstFiber_add_higherTail 0 t
  refine ⟨t, ht, ?_, ?_⟩
  · unfold thetaCuspCompletedProductFiberFirstDrop
    linarith
  · linarith

/-- **Exact hard-core reduction in the first-fibre-rise chamber.**  Whenever
the completed first product fibre rises, the cofinal tail drop is positive.
The prefactor in the total-variance law is therefore negative, so literal
theta `C₅ ≥ 0` is equivalent to the cofinal absorption budget having the
opposite sign.

This equivalence isolates the precise statement a cofinal product-fibre proof
must establish; componentwise positivity cannot replace it. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_nonneg_iff_cofinalBudget_nonpos
    {u t : ℝ} (ht : 0 < t)
    (hrise :
      thetaCuspCompletedProductFiberAmplitude 1 u 0 <
        thetaCuspCompletedProductFiberAmplitude 1 u t) :
    0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator u t ↔
      thetaCuspCompletedProductFiberCofinalCurvatureAbsorptionBudget u t ≤ 0 := by
  have ha : thetaCuspCompletedProductFiberFirstDrop u t < 0 := by
    unfold thetaCuspCompletedProductFiberFirstDrop
    linarith
  have hsource := thetaCuspReflectedSourceFirstDrop_pos u ht
  have hsplit :=
    thetaCuspReflectedSourceFirstDrop_eq_firstFiber_add_higherTail u t
  have hb : 0 < thetaCuspCompletedProductFiberHigherTailDrop u t := by
    linarith
  have hab :
      thetaCuspCompletedProductFiberFirstDrop u t *
        thetaCuspCompletedProductFiberHigherTailDrop u t < 0 :=
    mul_neg_of_neg_of_pos ha hb
  have hbudget :=
    thetaCuspReflectedSourceFifthRootCurvature_mul_firstFiber_higherTail_eq_budget u t
  constructor
  · intro hC
    rw [← hbudget]
    exact mul_nonpos_of_nonpos_of_nonneg hab.le hC
  · intro hB
    by_contra hC
    have hCneg : thetaCuspReflectedSourceFifthRootCurvatureNumerator u t < 0 :=
      lt_of_not_ge hC
    have hprod : 0 <
        thetaCuspCompletedProductFiberFirstDrop u t *
          thetaCuspCompletedProductFiberHigherTailDrop u t *
          thetaCuspReflectedSourceFifthRootCurvatureNumerator u t :=
      mul_pos_of_neg_of_neg hab hCneg
    rw [hbudget] at hprod
    exact (not_lt_of_ge hB) hprod

end

end RHTower
