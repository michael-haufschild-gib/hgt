import GaloisForLFunctions.RHTower.SoninPhysicalTailVanishing
import GaloisForLFunctions.RHTower.SoninPacketCompactVanishing
import GaloisForLFunctions.RHTower.SoninCouplingBranchEstimate

/-!
# Compact corrections die on the dilated wavepacket

Escaping support gives weak nullity, and weak nullity plus a uniform bound gives norm nullity under
any compact operator.  Applied to the inverse-dilated wavepacket, whose support sits beyond radius
`r b`, this removes every exact Sonin projection correction from the flag computation.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology InnerProductSpace

/-- **Compact operators annihilate families whose support escapes.** -/
theorem tendsto_norm_compactOperator_apply_of_evenIndicatorCutoff_apply_eq_zero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (K : evenSubspace →L[ℂ] F) (hK : IsCompactOperator K)
    (v : ℕ → evenSubspace) (M : ℝ) (hM : ∀ n, ‖v n‖ ≤ M)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hzero : ∀ n, evenIndicatorCutoff (R n) (v n) = 0) :
    Tendsto (fun n : ℕ => ‖K (v n)‖) atTop (𝓝 0) := by
  refine IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null K hK v M hM
    (fun ℓ => ?_)
  have hw := tendsto_inner_of_evenIndicatorCutoff_apply_eq_zero
    ((InnerProductSpace.toDual ℂ evenSubspace).symm ℓ) v M hM R hR hzero
  refine hw.congr fun n => ?_
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := evenSubspace)
    (x := v n) (y := ℓ)

/-- The inverse-dilated wavepacket, as a family indexed by the clock. -/
def soninDilatedPacket (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (κ r : ℝ) (hr : 0 < r) : evenSubspace :=
  evenDilationCLM r⁻¹ (inv_pos.mpr hr) (soninPacketEven b c hb hbc κ)

theorem norm_soninDilatedPacket (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (κ r : ℝ) (hr : 0 < r) :
    ‖soninDilatedPacket b c hb hbc κ r hr‖ = ‖soninPacketEven b c hb hbc κ‖ :=
  norm_evenDilationCLM_apply r⁻¹ (inv_pos.mpr hr) (soninPacketEven b c hb hbc κ)

theorem norm_soninDilatedPacket_le (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (κ r : ℝ) (hr : 0 < r) :
    ‖soninDilatedPacket b c hb hbc κ r hr‖ ≤ 2 * ‖soninBumpL2 b c hb hbc‖ := by
  rw [norm_soninDilatedPacket b c hb hbc κ r hr]
  exact norm_soninPacketL2_le b c hb hbc κ

theorem evenIndicatorCutoff_soninDilatedPacket_eq_zero (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (κ r : ℝ) (hr : 0 < r) :
    evenIndicatorCutoff (r * b) (soninDilatedPacket b c hb hbc κ r hr) = 0 :=
  evenIndicatorCutoff_evenDilationCLM_inv_soninPacketEven_eq_zero b c hb hbc κ r hr (r * b)
    le_rfl

/-- **`(15)`.**  Every compact operator dies on the dilated wavepacket family. -/
theorem tendsto_norm_compactOperator_apply_soninDilatedPacket
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (K : evenSubspace →L[ℂ] F) (hK : IsCompactOperator K)
    (κ : ℕ → ℝ) (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ => ‖K (soninDilatedPacket b c hb hbc (κ n) (r n) (hrpos n))‖)
      atTop (𝓝 0) := by
  refine tendsto_norm_compactOperator_apply_of_evenIndicatorCutoff_apply_eq_zero K hK
    (fun n => soninDilatedPacket b c hb hbc (κ n) (r n) (hrpos n))
    (2 * ‖soninBumpL2 b c hb hbc‖)
    (fun n => norm_soninDilatedPacket_le b c hb hbc (κ n) (r n) (hrpos n))
    (fun n => r n * b) ?_ (fun n => evenIndicatorCutoff_soninDilatedPacket_eq_zero b c hb hbc
      (κ n) (r n) (hrpos n))
  exact Filter.Tendsto.atTop_mul_const hb hr

/-- The exact Sonin projection correction dies on the dilated wavepacket. -/
theorem tendsto_norm_evenSoninProjectionCorrection_apply_soninDilatedPacket
    (b c t : ℝ) (hb : 0 < b) (hbc : b < c) (ht : 0 < t)
    (κ : ℕ → ℝ) (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninProjectionCorrection t
          (soninDilatedPacket b c hb hbc (κ n) (r n) (hrpos n))‖) atTop (𝓝 0) :=
  tendsto_norm_compactOperator_apply_soninDilatedPacket b c hb hbc
    (evenSoninProjectionCorrection t)
    (IsSoninPrincipalRelativeIdeal.isCompactOperator
      (IsSoninPrincipalRelativeIdeal.projectionCorrection t ht)) κ r hrpos hr

end RHTower
