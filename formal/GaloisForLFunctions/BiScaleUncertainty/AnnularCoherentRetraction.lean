import GaloisForLFunctions.BiScaleUncertainty.CoherentMomentAttainment
import Mathlib.Algebra.Field.Periodic

/-!
# Fixed-annulus representatives of odd coherent classes

The entire folded sinh source has a canonical actual odd representative in a
fixed annulus. The construction is idempotent and preserves the signed moment,
exact coherent price and cell defect. These data price the original plastic
functional without replacing its other source-dependent terms.
-/

open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.AnnularCoherentRetraction
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
open CoherentSourceProjection LocalCoherentFilter FiniteFilterSchurResidual
open FoldedHyperbolicCellDefect CoherentMomentAttainment
noncomputable section

private abbrev d := Real.log 2
private theorem d_pos : 0 < d := Real.log_pos (by norm_num : (1 : ℝ) < 2)

/-- Canonical odd sources have an even folded sinh multiplier. -/
theorem cellFold_oddSource_even (f : C_c(ℝ, ℝ)) (x : ℝ) :
    cellFold (oddCompactSource f) (-x) = cellFold (oddCompactSource f) x := by
  rw [cellFold_apply, cellFold_apply]
  have he (k : ℤ) : d * (-x + k) = -(d * (x + (-k : ℤ))) := by push_cast; ring
  simp_rw [he, sinhCompact_oddSource_even]
  exact tsum_comp_neg (fun k : ℤ => sinhCompact (1 / 2) (oddCompactSource f) (d * (x + k)))

private theorem fold_add_int (f : C_c(ℝ, ℝ)) (x : ℝ) (k : ℤ) :
    cellFold f (x + k) = cellFold f x := by
  simpa only [mul_one] using (cellFold_periodic f).int_mul k x

private theorem attaining_fold_one (x : ℝ) : cellFold (attainingSource 1) x = 1 := by
  obtain ⟨y, hy, he⟩ := (cellFold_periodic (attainingSource 1)).exists_mem_Ico₀
    (by norm_num : (0 : ℝ) < 1) x
  rw [he]
  exact cellFold_attainingSource 1 y ⟨hy.1, hy.2.le⟩

/-- Canonical compact representative formed from the actual folded odd source. -/
def representative (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => attainingSource 1 u * cellFold (oddCompactSource f) (u / d),
    (attainingSource 1).continuous.mul
      ((cellFold (oddCompactSource f)).continuous.comp (continuous_id.div_const d))⟩,
    (attainingSource 1).hasCompactSupport.mul_right⟩

theorem representative_apply (f : C_c(ℝ, ℝ)) (u : ℝ) :
    representative f u = attainingSource 1 u * cellFold (oddCompactSource f) (u / Real.log 2) := rfl

/-- Every representative is supported in the same open annulus, regardless of the input radius. -/
theorem representative_support (f : C_c(ℝ, ℝ)) :
    Function.support (representative f : ℝ → ℝ) ⊆
      {u : ℝ | Real.log 2 < |u| ∧ |u| < 3 * Real.log 2} := by
  intro u hu
  change d < |u| ∧ |u| < 3 * d
  have hp : attainmentProfile u ≠ 0 := by
    intro hz
    apply hu
    simp [representative_apply, attainingSource_apply, hz]
  by_cases ha : GaloisForLFunctions.HTGeometry.tentReal 1 (u / d - 2) = 0
  · have hb : GaloisForLFunctions.HTGeometry.tentReal 1 (u / d + 2) ≠ 0 := by
      intro hb
      exact hp (by simp [attainmentProfile, ha, hb])
    have hh := abs_lt.mp (GaloisForLFunctions.HTGeometry.abs_lt_of_tentReal_ne_zero hb)
    have hlo : -3 * d < u := (lt_div_iff₀ d_pos).mp (by linarith only [hh.1])
    have hhi : u < -d := by
      have h := (div_lt_iff₀ d_pos).mp (show u / d < -1 by linarith only [hh.2])
      simpa only [neg_one_mul] using h
    rw [abs_of_neg (by linarith [d_pos] : u < 0)]
    constructor <;> linarith only [hlo, hhi]
  · have hh := abs_lt.mp (GaloisForLFunctions.HTGeometry.abs_lt_of_tentReal_ne_zero ha)
    have hlo : d < u := by
      have h := (lt_div_iff₀ d_pos).mp (show (1 : ℝ) < u / d by linarith only [hh.1])
      simpa only [one_mul] using h
    have hhi : u < 3 * d := (div_lt_iff₀ d_pos).mp (by linarith only [hh.2])
    rw [abs_of_pos (d_pos.trans hlo)]
    exact ⟨hlo, hhi⟩

theorem representative_odd (f : C_c(ℝ, ℝ)) (u : ℝ) :
    representative f (-u) = -representative f u := by
  simp only [representative_apply, attainingSource_odd, neg_div, cellFold_oddSource_even, neg_mul]

theorem oddCompactSource_representative (f : C_c(ℝ, ℝ)) :
    oddCompactSource (representative f) = representative f := by
  ext u
  change (representative f u - representative f (-u)) / 2 = representative f u
  rw [representative_odd]
  ring

theorem sinhCompact_representative (f : C_c(ℝ, ℝ)) (u : ℝ) :
    sinhCompact (1 / 2) (representative f) u =
      sinhCompact (1 / 2) (attainingSource 1) u * cellFold (oddCompactSource f) (u / Real.log 2) := by
  change Real.sinh ((1 / 2 : ℝ) * u) *
    (attainingSource 1 u * cellFold (oddCompactSource f) (u / d)) =
      (Real.sinh ((1 / 2 : ℝ) * u) * attainingSource 1 u) * cellFold (oddCompactSource f) (u / d)
  ring

/-- The complete folded multiplier is preserved on the whole real line. -/
theorem cellFold_representative (f : C_c(ℝ, ℝ)) :
    cellFold (representative f) = cellFold (oddCompactSource f) := by
  ext x
  rw [cellFold_apply]
  simp_rw [sinhCompact_representative, mul_div_cancel_left₀ _ d_pos.ne', fold_add_int]
  rw [tsum_mul_right, ← cellFold_apply, attaining_fold_one, one_mul]

/-- The actual source constructor is an idempotent retraction. -/
theorem representative_idempotent (f : C_c(ℝ, ℝ)) :
    representative (representative f) = representative f := by
  ext u
  simp only [representative_apply, oddCompactSource_representative, cellFold_representative]

/-- Representatives distinguish exactly the full folded coherent classes. -/
theorem representative_eq_iff_fold_eq (f g : C_c(ℝ, ℝ)) :
    representative f = representative g ↔ cellFold (oddCompactSource f) = cellFold (oddCompactSource g) := by
  constructor
  · intro h
    simpa only [cellFold_representative] using congrArg cellFold h
  · intro h
    ext u
    simp only [representative_apply, h]

theorem cellMean_representative (f : C_c(ℝ, ℝ)) :
    cellMean (representative f) = cellMean (oddCompactSource f) := by
  rw [← integral_cellFold, ← integral_cellFold, cellFold_representative]

theorem moment_representative (f : C_c(ℝ, ℝ)) :
    (∫ u, representative f u * Real.sinh (u / 2)) =
      ∫ u, oddCompactSource f u * Real.sinh (u / 2) := by
  have he := cellMean_representative f
  unfold cellMean at he
  field_simp [d_pos.ne'] at he
  exact he

theorem cellResidualEnergy_representative (f : C_c(ℝ, ℝ)) :
    cellResidualEnergy (representative f) = cellResidualEnergy (oddCompactSource f) := by
  unfold cellResidualEnergy
  rw [cellFold_representative, cellMean_representative]

/-- The entire signed coherent price is preserved, rather than merely bounded. -/
theorem exactBudget_representative (f : C_c(ℝ, ℝ)) :
    localBudget (representative f) - schurResidualGain (representative f) =
      localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f) := by
  have hR := integral_cellFold_sq (representative f)
  rw [oddCompactSource_representative, cellFold_representative] at hR
  have he := hR.symm.trans (integral_cellFold_sq f)
  field_simp [d_pos.ne'] at he
  exact he

/-- The fixed-annulus representative prices the original source's full plastic functional. -/
theorem odd_plastic_representative_bound (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
      2 * Real.log 2 * (localBudget (representative f) - schurResidualGain (representative f)) +
      2 * (Real.log 2) ^ 2 * cellResidualEnergy (representative f) ≤
        plasticCrossover (oddCompactSource f) := by
  have hp := odd_plasticCrossover_ge_optimized f N
  have he := cellResidualEnergy_identity (representative f)
  rw [oddCompactSource_representative, moment_representative] at he
  nlinarith only [hp, he]

end
end GaloisForLFunctions.BiScaleUncertainty.AnnularCoherentRetraction
