import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheWorkIntegralIsTheEnergyDrop
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheEscapeIsAnInteriorBump

/-!
# The free anchor at zero damping

Every transport in the continuation layer so far has started from half damping, where admission is
an analytic input: the corpus's bound on the receiver in the zero-free band.  The zero-damping end
needs no input at all.  The undamped source is exactly the constant one, so the critical energy
returns to the pronic mass there, and the pronic mass is below one *uniformly in the horizon*.

Running the work integral down to that end gives the anchored bound

`E_T(ε) ≤ Σ_{n ≤ T} 1/(n(n+1)) + B ≤ 1 + B`  whenever `∫_η^ε 2W_T ≤ B` for all `0 < η ≤ ε`
(`dampedMobiusEnergy_le_pronicMass_add`, `admits_of_work_integral_bound`),

and conversely admission bounds those integrals by the energy budget itself
(`work_integral_le_of_bddAbove`).  Hence

**RH ⟺ cofinally in the damping, the signed work integrals up to that damping are bounded uniformly
in the horizon** (`riemannHypothesis_iff_cofinal_work_integral_bound`),

a criterion with no endpoint hypothesis, no zero-free band and no unspecified constant: the only
quantity left is the total signed work accumulated from zero damping, and its admissible budget is
`1`.
-/

open Set Filter Topology Finset MeasureTheory RHTower

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The anchored bound -/

/-- **The zero-damping anchor.**  A uniform bound on the work integrals up to `ε` bounds the energy
at `ε` by the pronic mass plus that bound. -/
theorem dampedMobiusEnergy_le_pronicMass_add {ε B : ℝ} (hε : 0 < ε) (T : ℕ)
    (h : ∀ η : ℝ, 0 < η → η ≤ ε → (∫ x in η..ε, 2 * signedDampingWork x T) ≤ B) :
    dampedMobiusEnergy ε T ≤ (∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1))) + B := by
  have hge : ∀ η ∈ Ioo (0 : ℝ) ε,
      dampedMobiusEnergy ε T - B ≤ dampedMobiusEnergy η T := by
    intro η hη
    have hint := integral_signedDampingWork_eq hη.1 hη.2.le T
    have hb := h η hη.1 hη.2.le
    rw [hint] at hb
    linarith
  have hlim := tendsto_dampedMobiusEnergy_nhdsGT_zero T
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      dampedMobiusEnergy ε T - B ≤ dampedMobiusEnergy η T := by
    filter_upwards [Ioo_mem_nhdsGT hε] with η hη using hge η hη
  have hle := ge_of_tendsto hlim hev
  linarith

/-- **Admission from the free anchor.**  The budget is one plus the work bound. -/
theorem admits_of_work_integral_bound {ε B : ℝ} (hε : 0 < ε)
    (h : ∀ (T : ℕ) (η : ℝ), 0 < η → η ≤ ε →
      (∫ x in η..ε, 2 * signedDampingWork x T) ≤ B) :
    Admits dampedMobiusEnergy ε :=
  ⟨1 + B, fun T => by
    have h1 := dampedMobiusEnergy_le_pronicMass_add hε T (fun η hη hηε => h T η hη hηε)
    have h2 := pronicMass_le_one T
    linarith⟩

/-- The converse: an energy budget bounds the work integrals. -/
theorem work_integral_le_of_bddAbove {ε B : ℝ} (hB : ∀ T : ℕ, dampedMobiusEnergy ε T ≤ B)
    (T : ℕ) {η : ℝ} (hη : 0 < η) (hηε : η ≤ ε) :
    (∫ x in η..ε, 2 * signedDampingWork x T) ≤ B := by
  rw [integral_signedDampingWork_eq hη hηε T]
  linarith [dampedMobiusEnergy_nonneg η T, hB T]

/-! ## §2. The criterion without an endpoint -/

/-- **RH is a uniform bound on the signed work accumulated from zero damping.**  No endpoint
admission, no zero-free band: the pronic mass pays the anchor. -/
theorem riemannHypothesis_iff_cofinal_work_integral_bound :
    RiemannHypothesis ↔
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ B : ℝ, ∀ (T : ℕ) (η : ℝ), 0 < η → η ≤ ε →
        (∫ x in η..ε, 2 * signedDampingWork x T) ≤ B := by
  rw [riemannHypothesis_iff_cofinallyAdmits]
  constructor
  · intro h δ hδ
    obtain ⟨ε, hε, hεδ, B, hB⟩ := h δ hδ
    exact ⟨ε, hε, hεδ, B, fun T η hη hηε => work_integral_le_of_bddAbove hB T hη hηε⟩
  · intro h δ hδ
    obtain ⟨ε, hε, hεδ, B, hB⟩ := h δ hδ
    exact ⟨ε, hε, hεδ, admits_of_work_integral_bound hε hB⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
