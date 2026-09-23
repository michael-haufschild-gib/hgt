import GaloisForLFunctions.RHTower.SoninScaledPacketScaling
import GaloisForLFunctions.RHTower.SoninEvenCarrier
import GaloisForLFunctions.RHTower.GaussianEvenCarrier

/-!
# The rescaled packet as a vector of the even Sonin space

The rescaled packet is continuous with compact support, so it defines an element of `L²(ℝ)`, and it
is even, so that element lies in the even subspace.  Its squared norm is the integral of its square,
which by the scaling law is the half-width times the reference energy at the rescaled frequency.

So the whole family of narrowing annuli with proportionally rising carriers is carried by one
reference vector, up to an explicit factor.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology InnerProduct InnerProductSpace

/-- The complexified rescaled packet is square integrable. -/
theorem memLp_soninScaledPacket (m δ κ : ℝ) (hδ : 0 < δ) :
    MemLp (fun x : ℝ => (soninScaledPacket m δ κ x : ℂ)) 2 (volume : Measure ℝ) := by
  refine Continuous.memLp_of_hasCompactSupport
    (Complex.continuous_ofReal.comp (continuous_soninScaledPacket m δ κ hδ)) ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_soninScaledPacket m δ κ hδ) ?_
  intro x hx
  refine subset_tsupport _ ?_
  intro h0
  exact hx (by simp [h0])

/-- The rescaled packet as an element of `L²(ℝ)`. -/
def soninScaledPacketL2 (m δ κ : ℝ) (hδ : 0 < δ) : SoninL2 :=
  (memLp_soninScaledPacket m δ κ hδ).toLp _

theorem soninScaledPacketL2_coeFn (m δ κ : ℝ) (hδ : 0 < δ) :
    (soninScaledPacketL2 m δ κ hδ : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => (soninScaledPacket m δ κ x : ℂ) :=
  MemLp.coeFn_toLp (memLp_soninScaledPacket m δ κ hδ)

/-- The rescaled packet is even, so its `L²` class lies in the even subspace. -/
theorem soninScaledPacketL2_mem_evenSubspace (m δ κ : ℝ) (hδ : 0 < δ) :
    soninScaledPacketL2 m δ κ hδ ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  apply Lp.ext
  have hrefl := l2Reflection_ae (soninScaledPacketL2 m δ κ hδ)
  have hcoe := soninScaledPacketL2_coeFn m δ κ hδ
  have hcoeNeg := hcoe.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hrefl, hcoe, hcoeNeg] with x hx hval hvalNeg
  rw [hx]
  have hvalNeg' : (soninScaledPacketL2 m δ κ hδ : ℝ → ℂ) (-x) =
      (soninScaledPacket m δ κ (-x) : ℂ) := by
    simpa [Function.comp_apply] using hvalNeg
  rw [hvalNeg', hval, soninScaledPacket_even m δ κ x]

/-- The rescaled packet as a vector of the even Sonin carrier. -/
def soninScaledPacketEven (m δ κ : ℝ) (hδ : 0 < δ) : evenSubspace :=
  ⟨soninScaledPacketL2 m δ κ hδ, soninScaledPacketL2_mem_evenSubspace m δ κ hδ⟩

@[simp] theorem coe_soninScaledPacketEven (m δ κ : ℝ) (hδ : 0 < δ) :
    ((soninScaledPacketEven m δ κ hδ : evenSubspace) : SoninL2) =
      soninScaledPacketL2 m δ κ hδ := rfl

/-- The squared norm is the integral of the square. -/
theorem norm_sq_soninScaledPacketEven (m δ κ : ℝ) (hδ : 0 < δ) :
    ‖soninScaledPacketEven m δ κ hδ‖ ^ (2 : ℕ) = ∫ x : ℝ, soninScaledPacket m δ κ x ^ (2 : ℕ) := by
  rw [show ‖soninScaledPacketEven m δ κ hδ‖ = ‖soninScaledPacketL2 m δ κ hδ‖ from rfl,
    norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [soninScaledPacketL2_coeFn m δ κ hδ] with x hx
  rw [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Energy of the family.**  The squared norm is the half-width times the reference energy at the
rescaled frequency. -/
theorem norm_sq_soninScaledPacketEven_scaling (m δ κ : ℝ) (hδ : 0 < δ) :
    ‖soninScaledPacketEven m δ κ hδ‖ ^ (2 : ℕ) =
      δ * ‖soninScaledPacketEven (m / δ) 1 (δ * κ) one_pos‖ ^ (2 : ℕ) := by
  rw [norm_sq_soninScaledPacketEven m δ κ hδ,
    norm_sq_soninScaledPacketEven (m / δ) 1 (δ * κ) one_pos,
    integral_soninScaledPacket_sq_scaling m δ κ hδ]

end RHTower
