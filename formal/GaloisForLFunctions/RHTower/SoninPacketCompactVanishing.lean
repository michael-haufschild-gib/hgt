import GaloisForLFunctions.RHTower.SoninPacketL2
import GaloisForLFunctions.RHTower.SoninEulerQuadraticCorner
import GaloisForLFunctions.RHTower.SoninPrincipalRelativeIdeal

/-!
# Every fixed compact correction dies on the wavepacket family

The wavepacket family is bounded in norm and escapes weakly, so any compact operator sends it to a
norm-null sequence.  In particular the exact Sonin projection correction — the only place where the
aperture projections differ from their formal physical/Fourier complement — vanishes along the
family, which is what lets the coupling be computed from cutoffs alone at high frequency.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology InnerProductSpace

/-- **Compact operators annihilate the wavepacket family.** -/
theorem tendsto_norm_compactOperator_apply_soninPacketEven
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (K : evenSubspace →L[ℂ] F) (hK : IsCompactOperator K)
    (κ : ℕ → ℝ) (hκ : Tendsto κ atTop atTop) :
    Tendsto (fun n : ℕ => ‖K (soninPacketEven b c hb hbc (κ n))‖) atTop (𝓝 0) := by
  refine IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null K hK
    (fun n => soninPacketEven b c hb hbc (κ n))
    (2 * ‖soninBumpL2 b c hb hbc‖) (fun n => ?_) (fun ℓ => ?_)
  · exact norm_soninPacketL2_le b c hb hbc (κ n)
  · have hv := tendsto_inner_soninPacketL2_atTop b c hb hbc
      (((InnerProductSpace.toDual ℂ evenSubspace).symm ℓ : evenSubspace) : SoninL2)
    refine (hv.comp hκ).congr fun n => ?_
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := evenSubspace)
      (x := soninPacketEven b c hb hbc (κ n)) (y := ℓ)

/-- **`(8)`.**  The exact Sonin projection correction vanishes along the wavepacket family. -/
theorem tendsto_norm_evenSoninProjectionCorrection_apply_soninPacketEven
    (b c t : ℝ) (hb : 0 < b) (hbc : b < c) (ht : 0 < t)
    (κ : ℕ → ℝ) (hκ : Tendsto κ atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninProjectionCorrection t (soninPacketEven b c hb hbc (κ n))‖) atTop (𝓝 0) :=
  tendsto_norm_compactOperator_apply_soninPacketEven b c hb hbc
    (evenSoninProjectionCorrection t)
    (IsSoninPrincipalRelativeIdeal.isCompactOperator
      (IsSoninPrincipalRelativeIdeal.projectionCorrection t ht)) κ hκ

/-- Any element of the relative ideal vanishes along the family, not only the correction. -/
theorem tendsto_norm_isSoninPrincipalRelativeIdeal_apply_soninPacketEven
    (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    {T : evenSubspace →L[ℂ] evenSubspace} (hT : IsSoninPrincipalRelativeIdeal T)
    (κ : ℕ → ℝ) (hκ : Tendsto κ atTop atTop) :
    Tendsto (fun n : ℕ => ‖T (soninPacketEven b c hb hbc (κ n))‖) atTop (𝓝 0) :=
  tendsto_norm_compactOperator_apply_soninPacketEven b c hb hbc T
    (IsSoninPrincipalRelativeIdeal.isCompactOperator hT) κ hκ

end RHTower
