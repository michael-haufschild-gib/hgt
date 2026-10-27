import GaloisForLFunctions.ArithmeticCorrespondencePositivity.EveryOffLineZeroHasALocalOutwardFieldWitness
import GaloisForLFunctions.RHTower.ZeroNetworkConductance
import GaloisForLFunctions.RHTower.TransverseEquilibrium

/-!
# The field law has a threshold

RH says that no zero of `ξ` feels a transverse field: `Re E(ρ) = 0` at every zero. The exact
equality is not what has to be proved. Every off-line zero has, within `C log γ`, a locally
rightmost terminal `p` of depth `δ ∈ (0, ½)` whose transverse field is at least
`1/(2δ) + c δ log(|γ_p| + 4)` (`exists_local_outward_field_witness`): the reflection partner pushes
with `1/(2δ) > 1`, and the logarithmic band of the other zeros adds `c δ log γ`. Minimizing over the
unknown depth gives the floor `√(2c log γ)`.

* **Threshold one** (`riemannHypothesis_iff_forall_transverseField_le_one`): RH holds iff every zero
  right of the line feels a transverse field at most `1`.
* **Threshold `√log`** (`exists_riemannHypothesis_iff_transverseField_lt_sqrt_log`): for an explicit
  `c > 0`, RH holds iff every zero right of the line feels a transverse field below
  `√(2c log(|γ| + 4))`.

So the field law that would exclude off-line zeros is an upper bound of size `max(1, √(2c log γ))`
at right zeros — far above the value `0` that RH predicts. Detection supplies the lower bound; the
missing arithmetic input is an upper bound of this size, not an exact equilibrium.
-/

open RHTower GaloisForLFunctions.ArithmeticCorrespondencePositivity

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- Under RH every zero copy is critical. -/
theorem re_eq_half_of_riemannHypothesis (h : RiemannHypothesis) (p : XiZeroCopy) :
    (p.1 : ℂ).re = 1 / 2 :=
  (supportPartner_eq_self_iff p.1).mp (riemannHypothesis_iff_supportPartner_eq_id.mp h p.1)

/-- Without RH some zero copy is off the line. -/
theorem exists_offLine_copy_of_not_riemannHypothesis (h : ¬RiemannHypothesis) :
    ∃ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 := by
  by_contra hc
  push Not at hc
  exact h (riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ => by
    simpa using hc (supportToCopy ρ))

/-- A zero right of the line has depth in `(0, ½)`. -/
theorem xiZeroDepth_mem_of_right {p : XiZeroCopy} (hp : 1 / 2 < (p.1 : ℂ).re) :
    0 < xiZeroDepth p ∧ xiZeroDepth p < 1 / 2 := by
  have h1 := (xiDivisorSupport_re_mem p.1).2
  rw [xiZeroDepth, abs_of_pos (by linarith)]
  constructor <;> linarith

/-- The terminal lower bound of the witness, in the form used below: some right zero `p` of
depth `δ` has transverse field at least `1/(2δ) + c δ log(|γ_p| + 4)`. -/
theorem exists_right_zero_field_ge {c : ℝ}
    (hw : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 → ∃ p : XiZeroCopy,
      1 / 2 < (p.1 : ℂ).re ∧ 0 < (xiZeroCopyFiber p.1).card ∧
      ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p) +
        c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤ xiTransverseField p)
    (h : ¬RiemannHypothesis) :
    ∃ p : XiZeroCopy, 1 / 2 < (p.1 : ℂ).re ∧
      1 / (2 * xiZeroDepth p) + c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤
        xiTransverseField p := by
  obtain ⟨q, hq⟩ := exists_offLine_copy_of_not_riemannHypothesis h
  obtain ⟨p, hp, hcard, hfield⟩ := hw q hq
  refine ⟨p, hp, le_trans ?_ hfield⟩
  have hδ := (xiZeroDepth_mem_of_right hp).1
  have hc1 : (1 : ℝ) ≤ (xiZeroCopyFiber p.1).card := by exact_mod_cast hcard
  gcongr

/-- The witness, reduced to the field bound at a right zero. -/
theorem exists_field_witness_constant : ∃ c : ℝ, 0 < c ∧
    ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 → ∃ p : XiZeroCopy,
      1 / 2 < (p.1 : ℂ).re ∧ 0 < (xiZeroCopyFiber p.1).card ∧
      ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p) +
        c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤ xiTransverseField p := by
  obtain ⟨C, c, -, hc, hw⟩ := exists_local_outward_field_witness
  refine ⟨c, hc, fun q hq => ?_⟩
  obtain ⟨p, -, hp, -, -, hcard, -, -, hfield, -⟩ := hw q hq
  exact ⟨p, hp, hcard, hfield⟩

/-- **Threshold one**: RH holds iff every zero right of the line feels a transverse field at most
`1`. -/
theorem riemannHypothesis_iff_forall_transverseField_le_one :
    RiemannHypothesis ↔ ∀ p : XiZeroCopy, 1 / 2 < (p.1 : ℂ).re → xiTransverseField p ≤ 1 := by
  constructor
  · intro h p hp
    exact absurd (re_eq_half_of_riemannHypothesis h p) (ne_of_gt hp)
  · intro hle
    by_contra hRH
    obtain ⟨c, hc, hw⟩ := exists_field_witness_constant
    obtain ⟨p, hp, hfield⟩ := exists_right_zero_field_ge hw hRH
    obtain ⟨hδ0, hδ1⟩ := xiZeroDepth_mem_of_right hp
    have hL : 0 ≤ Real.log (|xiZeroHeight p| + 4) :=
      Real.log_nonneg (by linarith [abs_nonneg (xiZeroHeight p)])
    have h1 : 1 < 1 / (2 * xiZeroDepth p) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    have h2 : 0 ≤ c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) := by positivity
    linarith [hle p hp]

/-- **Threshold `√log`**: for an explicit `c > 0`, RH holds iff every zero right of the line feels a
transverse field below `√(2c log(|γ| + 4))`. -/
theorem exists_riemannHypothesis_iff_transverseField_lt_sqrt_log :
    ∃ c : ℝ, 0 < c ∧ (RiemannHypothesis ↔ ∀ p : XiZeroCopy, 1 / 2 < (p.1 : ℂ).re →
      xiTransverseField p < Real.sqrt (2 * c * Real.log (|(p.1 : ℂ).im| + 4))) := by
  obtain ⟨c, hc, hw⟩ := exists_field_witness_constant
  refine ⟨c, hc, fun h p hp => absurd (re_eq_half_of_riemannHypothesis h p) (ne_of_gt hp),
    fun hlt => ?_⟩
  by_contra hRH
  obtain ⟨p, hp, hfield⟩ := exists_right_zero_field_ge hw hRH
  obtain ⟨hδ0, -⟩ := xiZeroDepth_mem_of_right hp
  set δ := xiZeroDepth p
  set L := Real.log (|(p.1 : ℂ).im| + 4)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [abs_nonneg (p.1 : ℂ).im])
  -- AM–GM: `1/(2δ) + cδL ≥ √(2cL)`
  have hamgm : Real.sqrt (2 * c * L) ≤ 1 / (2 * δ) + c * δ * L := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hprod : 1 / (2 * δ) * (c * δ * L) = c * L / 2 := by field_simp
    nlinarith [sq_nonneg (1 / (2 * δ) - c * δ * L)]
  have := hlt p hp
  have hfield' : 1 / (2 * δ) + c * δ * L ≤ xiTransverseField p := hfield
  linarith

end

end GaloisForLFunctions.ArithmeticElectrostatics
