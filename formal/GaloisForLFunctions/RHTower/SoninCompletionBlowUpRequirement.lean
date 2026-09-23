import GaloisForLFunctions.RHTower.SoninChannelAnnulusBound

/-!
# A completion must blow up on the packets themselves

Whatever operators a completion is built from, its contribution at one scale is at most the norm of
the operator applied to that scale's packet, times the packet norm — and the packet norms are
bounded uniformly.  The coupling energy diverges, so a completion that restores the floor must send
the packets to vectors of unbounded norm.

It is not enough for the operators to be large somewhere: they have to be large exactly where the
source packets live.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- The packet family read along the crossing clock. -/
def soninClockPacket (a b c : ℝ) (hb : 0 < b) (hbc : b < c) (q : ℝ) (i : ℕ) : evenSubspace :=
  soninPacketEven b c hb hbc (2 * Real.pi * (soninCrossingClock a c i * q))

/-- The diagonal pairing of the packets against a family of operators. -/
def soninChannelFamilyContribution (a b c : ℝ) (hb : 0 < b) (hbc : b < c) (q : ℝ)
    (T : ℕ → (evenSubspace →L[ℂ] evenSubspace)) (i : ℕ) : ℝ :=
  (⟪soninClockPacket a b c hb hbc q i,
    T i (soninClockPacket a b c hb hbc q i)⟫_ℂ).re

/-- The packet norms are bounded below the uniform bump bound, which is therefore positive. -/
theorem norm_soninBumpL2_pos (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    0 < 2 * ‖soninBumpL2 b c hb hbc‖ := by
  have hLpos := sqrt_half_energy_pos b c hb hbc
  have hlim := tendsto_norm_soninPacketEven b c hb hbc (fun n : ℕ => (n : ℝ))
    tendsto_natCast_atTop_atTop
  have hhalf : Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ (2 : ℕ)) / 2 <
      Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ (2 : ℕ)) := by linarith
  obtain ⟨i, hi⟩ := (hlim.eventually_const_lt hhalf).exists
  have hbound : ‖soninPacketEven b c hb hbc (i : ℝ)‖ ≤ 2 * ‖soninBumpL2 b c hb hbc‖ :=
    norm_soninPacketL2_le b c hb hbc _
  have hpos : 0 < ‖soninPacketEven b c hb hbc (i : ℝ)‖ := lt_trans (half_pos hLpos) hi
  linarith

/-- **A completion with a floor blows up on the packets.**  If a family of operators restores the
lower floor, then the norms of its values on the source packets tend to infinity. -/
theorem tendsto_norm_apply_soninClockPacket_atTop_of_bddBelow
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) (T : ℕ → (evenSubspace →L[ℂ] evenSubspace))
    (hfloor : ∃ M : ℝ, ∀ s : Finset ℕ,
      M ≤ soninCompletedPacketValueVar s a b c (soninCrossingClock a c)
        (one_lt_soninCrossingClock a c) (soninChannelFamilyContribution a b c hb hbc q T)) :
    Tendsto (fun i => ‖T i (soninClockPacket a b c hb hbc q i)‖) atTop atTop := by
  have henergy := tendsto_hsNormSq_soninApertureCoupling_atTop a b c ha hb hab hbc q haq hqb
    (soninCrossingClock a c) (soninCrossingClock_pos a c) (one_lt_soninCrossingClock a c)
    (fun n => lt_soninCrossingClock_mul a c ha n) (tendsto_soninCrossingClock a c)
  have hκ := tendsto_atTop_of_bddBelow_soninCompletedPacketValueVar ha hab hbc
    (soninCrossingClock a c) (one_lt_soninCrossingClock a c)
    (fun i => lt_soninCrossingClock_mul a c ha i)
    (soninChannelFamilyContribution a b c hb hbc q T) henergy hfloor
  have hpos := norm_soninBumpL2_pos b c hb hbc
  have hle : ∀ i : ℕ, soninChannelFamilyContribution a b c hb hbc q T i ≤
      2 * ‖soninBumpL2 b c hb hbc‖ * ‖T i (soninClockPacket a b c hb hbc q i)‖ := by
    intro i
    set w : evenSubspace := soninClockPacket a b c hb hbc q i with hw
    have hbound : ‖w‖ ≤ 2 * ‖soninBumpL2 b c hb hbc‖ :=
      norm_soninPacketL2_le b c hb hbc _
    have hre : (⟪w, T i w⟫_ℂ).re ≤ ‖(⟪w, T i w⟫_ℂ)‖ := Complex.re_le_norm _
    have hinner : ‖(⟪w, T i w⟫_ℂ)‖ ≤ ‖w‖ * ‖T i w‖ := norm_inner_le_norm _ _
    have hmul : ‖w‖ * ‖T i w‖ ≤ 2 * ‖soninBumpL2 b c hb hbc‖ * ‖T i w‖ :=
      mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    calc soninChannelFamilyContribution a b c hb hbc q T i = (⟪w, T i w⟫_ℂ).re := rfl
      _ ≤ ‖(⟪w, T i w⟫_ℂ)‖ := hre
      _ ≤ ‖w‖ * ‖T i w‖ := hinner
      _ ≤ 2 * ‖soninBumpL2 b c hb hbc‖ * ‖T i w‖ := hmul
  have hprod : Tendsto (fun i => 2 * ‖soninBumpL2 b c hb hbc‖ *
      ‖T i (soninClockPacket a b c hb hbc q i)‖) atTop atTop :=
    tendsto_atTop_mono hle hκ
  exact hprod.atTop_of_const_mul₀ hpos

end RHTower
