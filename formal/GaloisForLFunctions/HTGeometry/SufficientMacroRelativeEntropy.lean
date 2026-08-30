import GaloisForLFunctions.HTGeometry.FinitePacketMeasure

/-!
# Relative entropy of the sufficient macropacket

The relative-entropy and Jeffreys halves of Theorem 6.1 of the formation-resource card
`ULF-FRM-2`.  The sum statistic and the common recovery kernel are Markov maps in opposite
directions between the independent packet and its macro law, so randomized data processing
applied twice turns the capital inequality into an exact identity, and independence of the packet
turns it into `d` times the one-packet cost.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace SufficientMacro

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
  [MeasurableSingletonClass X] (b T : X → ℝ)

instance instNonemptyMacroAlphabet (d : ℕ) : Nonempty (MacroAlphabet T d) :=
  ⟨⟨sumStat T d (fun _ => Classical.arbitrary X), sumStat_mem T d _⟩⟩

omit [DecidableEq X] in
/-- The macro law and the independent packet are related by Markov maps in both directions. -/
theorem comp_statKernel (hb : ∀ x, 0 < b x) (d : ℕ) (θ : ℝ) :
    (finiteKernel (statKernel T d)) ∘ₘ (packetMeasure (tensorPower d (packet b T θ)))
      = packetMeasure (macroPacket b T d θ) := by
  rw [finiteKernel_comp _ (tensorPower_nonneg d (packet_nonneg b T hb θ)),
    statKernel_applyReal b T hb θ d]

omit [DecidableEq X] in
theorem comp_recoveryKernel (hb : ∀ x, 0 < b x) (d : ℕ) (θ : ℝ) :
    (finiteKernel (recoveryKernel b T hb d)) ∘ₘ (packetMeasure (macroPacket b T d θ))
      = packetMeasure (tensorPower d (packet b T θ)) := by
  rw [finiteKernel_comp _ (macroPacket_nonneg b T hb d θ),
    recoveryKernel_applyReal b T hb θ d]

/-- Exact sufficiency for relative entropy: the macro law costs exactly what the packet costs. -/
theorem klDiv_macroPacket_eq (hb : ∀ x, 0 < b x) (d : ℕ) (θ φ : ℝ) :
    klDiv (packetMeasure (macroPacket b T d θ)) (packetMeasure (macroPacket b T d φ))
      = klDiv (packetMeasure (tensorPower d (packet b T θ)))
        (packetMeasure (tensorPower d (packet b T φ))) := by
  haveI : IsProbabilityMeasure (packetMeasure (tensorPower d (packet b T θ))) :=
    isProbabilityMeasure_packetMeasure (tensorPower_nonneg d (packet_nonneg b T hb θ))
      (by rw [sum_tensorPower, packet_sum b T hb θ, one_pow])
  haveI : IsProbabilityMeasure (packetMeasure (tensorPower d (packet b T φ))) :=
    isProbabilityMeasure_packetMeasure (tensorPower_nonneg d (packet_nonneg b T hb φ))
      (by rw [sum_tensorPower, packet_sum b T hb φ, one_pow])
  haveI : IsProbabilityMeasure (packetMeasure (macroPacket b T d θ)) :=
    isProbabilityMeasure_packetMeasure (macroPacket_nonneg b T hb d θ)
      (macroPacket_sum b T hb d θ)
  haveI : IsProbabilityMeasure (packetMeasure (macroPacket b T d φ)) :=
    isProbabilityMeasure_packetMeasure (macroPacket_nonneg b T hb d φ)
      (macroPacket_sum b T hb d φ)
  refine le_antisymm ?_ ?_
  · rw [← comp_statKernel b T hb d θ, ← comp_statKernel b T hb d φ]
    exact klDiv_comp_le _ _ _
  · rw [← comp_recoveryKernel b T hb d θ, ← comp_recoveryKernel b T hb d φ]
    exact klDiv_comp_le _ _ _

/-- **Theorem 6.1, `(FCAP.34)`.**  The macro law carries exactly `d` times the one-packet
relative entropy. -/
theorem klDiv_macroPacket (hb : ∀ x, 0 < b x) (d : ℕ) (θ φ : ℝ) :
    klDiv (packetMeasure (macroPacket b T d θ)) (packetMeasure (macroPacket b T d φ))
      = d * klDiv (packetMeasure (packet b T θ)) (packetMeasure (packet b T φ)) := by
  haveI : IsProbabilityMeasure (packetMeasure (packet b T θ)) :=
    isProbabilityMeasure_packetMeasure (packet_nonneg b T hb θ) (packet_sum b T hb θ)
  haveI : IsProbabilityMeasure (packetMeasure (packet b T φ)) :=
    isProbabilityMeasure_packetMeasure (packet_nonneg b T hb φ) (packet_sum b T hb φ)
  rw [klDiv_macroPacket_eq b T hb d θ φ,
    packetMeasure_tensorPower d (packet_nonneg b T hb θ) (packet_sum b T hb θ),
    packetMeasure_tensorPower d (packet_nonneg b T hb φ) (packet_sum b T hb φ),
    klDiv_pi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Theorem 6.1, `(FCAP.34)` Jeffreys form.** -/
theorem formationJeffreys_macroPacket (hb : ∀ x, 0 < b x) (d : ℕ) (θ φ : ℝ) :
    formationJeffreys (packetMeasure (macroPacket b T d θ)) (packetMeasure (macroPacket b T d φ))
      = d * formationJeffreys (packetMeasure (packet b T θ)) (packetMeasure (packet b T φ)) := by
  rw [formationJeffreys, formationJeffreys, klDiv_macroPacket b T hb d θ φ,
    klDiv_macroPacket b T hb d φ θ, mul_add]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- **`(FCAP.35a)`.**  The whole Rényi capital spectrum of the macro pair is exactly `d` times
the one-packet spectrum. -/
theorem renyiCapital_macroPacket {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (hb : ∀ x, 0 < b x)
    (d : ℕ) (θ φ : ℝ) :
    renyiCapital α (macroPacket b T d θ) (macroPacket b T d φ)
      = d * renyiCapital α (packet b T θ) (packet b T φ) := by
  have hov := renyiOverlap_macroPacket b T h0 h1 hb d θ φ
  have hcnn : 0 ≤ renyiOverlap α (packet b T θ) (packet b T φ) :=
    renyiOverlap_nonneg (packet_nonneg b T hb θ) (packet_nonneg b T hb φ)
  rw [renyiCapital, renyiCapital, hov]
  rcases eq_or_lt_of_le hcnn with hz | hpos
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [if_neg (by rw [← hz]; simp [zero_pow hd.ne']), if_neg (by rw [← hz]; simp),
        ENNReal.mul_top (by exact_mod_cast hd.ne')]
  · rw [if_pos (pow_pos hpos d), if_pos hpos, Real.log_pow, neg_mul_eq_mul_neg,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

end SufficientMacro

end

end GaloisForLFunctions.HTGeometry
