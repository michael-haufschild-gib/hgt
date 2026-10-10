import GaloisForLFunctions.HTGeometry.PaperRestrictionPacketDefect
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Finite.Comparison
import GaloisForLFunctions.RHTower.JointAncestryPrimeSupportUnitaryObstruction

/-!
# RFHM survival information and its coherent complement

The proven finite-law entropy and Pinsker inequalities apply to the actual retained and discarded
squared norms of a native RFHM state. These two masses form a probability law for every unit state.
The complex defect retains precisely the coefficients involving the inserted prime; together with
the compressed output it recovers the entire input. In contrast, the two energy probabilities are
independent of the insertion's arithmetic log grade. Their entropy therefore measures support loss
but does not supply RFHM's missing phase/depth/compound-sensitive wall law.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open RestrictionPacket FourierLLogL
open scoped Classical

/-- Unit vectors in the actual support-and-log-grade Hilbert carrier. -/
abbrev PaperRFHMUnitState := {v : JASPacketHilbert // ‖v‖ = 1}

/-- Actual Born masses of the retained and discarded complex branches. -/
def paperRFHMSurvivalLaw (s : JASRestrictionPacket) (v : PaperRFHMUnitState) : Law Bool :=
  ⟨(fun b => if b then ‖packetOperator s v.val‖ ^ 2 else ‖paperPacketDefect s v.val‖ ^ 2),
    (fun b => by dsimp; split_ifs <;> positivity), by
      simpa [Fintype.sum_bool, v.property] using paperPacketDefect_energy s v.val⟩

theorem paperRFHMSurvivalLaw_true (s : JASRestrictionPacket) (v : PaperRFHMUnitState) :
    paperRFHMSurvivalLaw s v true = ‖packetOperator s v.val‖ ^ 2 := rfl

theorem paperRFHMSurvivalLaw_false (s : JASRestrictionPacket) (v : PaperRFHMUnitState) :
    paperRFHMSurvivalLaw s v false = ‖paperPacketDefect s v.val‖ ^ 2 := rfl

/-- Uniform-reference KL is exactly the entropy missing from one binary observation. -/
theorem paperRFHMSurvivalLaw_kl_uniform (s : JASRestrictionPacket) (v : PaperRFHMUnitState) :
    (paperRFHMSurvivalLaw s v).kl (Law.uniform Bool) =
      Real.log 2 - (paperRFHMSurvivalLaw s v).entropy := by
  unfold Law.kl Law.crossE
  simp only [Law.uniform_apply, Fintype.card_bool, Nat.cast_ofNat, Real.log_inv, neg_neg,
    Law.Ex_const]

/-- The branch entropy always lies between zero and one natural-log bit. -/
theorem paperRFHMSurvivalLaw_entropy_bounds (s : JASRestrictionPacket)
    (v : PaperRFHMUnitState) :
    0 ≤ (paperRFHMSurvivalLaw s v).entropy ∧
      (paperRFHMSurvivalLaw s v).entropy ≤ Real.log 2 := by
  refine ⟨Law.entropy_nonneg _, ?_⟩
  simpa using Law.entropy_le_log_card (paperRFHMSurvivalLaw s v)

private theorem survival_tv_uniform (s : JASRestrictionPacket) (v : PaperRFHMUnitState) :
    (paperRFHMSurvivalLaw s v).tv (Law.uniform Bool) =
      |‖packetOperator s v.val‖ ^ 2 - 1 / 2| := by
  have h := paperPacketDefect_energy s v.val
  rw [v.property, one_pow] at h
  have hd : ‖paperPacketDefect s v.val‖ ^ 2 - (2 : ℝ)⁻¹ =
      -(‖packetOperator s v.val‖ ^ 2 - (2 : ℝ)⁻¹) := by linarith
  simp only [Law.tv, Fintype.sum_bool, paperRFHMSurvivalLaw_true,
    paperRFHMSurvivalLaw_false, Law.uniform_apply, Fintype.card_bool, Nat.cast_ofNat]
  rw [hd, abs_neg]
  simp only [one_div]
  ring

/-- Paper Pinsker bounds the actual squared survival-energy imbalance by its entropy deficit. -/
theorem paperRFHMSurvivalLaw_energy_imbalance (s : JASRestrictionPacket)
    (v : PaperRFHMUnitState) :
    (‖packetOperator s v.val‖ ^ 2 - 1 / 2) ^ 2 ≤
      Real.log 2 - (paperRFHMSurvivalLaw s v).entropy := by
  have hdom : (paperRFHMSurvivalLaw s v).dominated (Law.uniform Bool) := by
    intro b _
    rw [Law.uniform_apply]
    positivity
  have h := Law.tv_sq_le_kl hdom
  rw [survival_tv_uniform, paperRFHMSurvivalLaw_kl_uniform, sq_abs] at h
  exact h

/-- The same source theorem gives the unsquared physical energy imbalance. -/
theorem paperRFHMSurvivalLaw_energy_imbalance_sqrt (s : JASRestrictionPacket)
    (v : PaperRFHMUnitState) :
    |‖packetOperator s v.val‖ ^ 2 - 1 / 2| ≤
      Real.sqrt (Real.log 2 - (paperRFHMSurvivalLaw s v).entropy) := by
  have hdom : (paperRFHMSurvivalLaw s v).dominated (Law.uniform Bool) := by
    intro b _
    rw [Law.uniform_apply]
    positivity
  simpa only [survival_tv_uniform, paperRFHMSurvivalLaw_kl_uniform] using
    Law.tv_le_sqrt_kl hdom

/-- Exact native input support of a Gamma insertion; logarithmic history does not alter it. -/
theorem paperRFHMInsertion_sourceSupport (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes) :
    sourceSupport (jasGammaInsertionPacket x p P) = jasFiniteSupportComplement {p} := rfl

/-- The complementary record keeps every complex coefficient involving the inserted prime,
at its original grade. It is not replaced by its absolute value or energy. -/
theorem paperRFHMInsertion_defect_apply (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes)
    (v : JASPacketHilbert) (i : JASPrimeSupport × JASLogGrade) :
    (paperPacketDefect (jasGammaInsertionPacket x p P) v :
      (JASPrimeSupport × JASLogGrade) → ℂ) i = if p ∈ i.1 then v i else 0 := by
  classical
  rw [paperPacketDefect_apply]
  change v i - (supportProjection (sourceSupport (jasGammaInsertionPacket x p P)) v :
    (JASPrimeSupport × JASLogGrade) → ℂ) i = _
  rw [paperRFHMInsertion_sourceSupport, supportProjection_apply]
  by_cases hp : p ∈ i.1
  · have hn : ¬ i.1 ⊆ jasFiniteSupportComplement {p} := by
      intro h
      have hh := h hp
      simp [jasFiniteSupportComplement] at hh
    simp [hp, hn]
  · have hs : i.1 ⊆ jasFiniteSupportComplement {p} := by
      intro q hq
      change q ∉ ({p} : Finset Nat.Primes)
      simpa only [Finset.mem_singleton] using
        (show q ≠ p from fun h => hp (h ▸ hq))
    simp [hp, hs]

/-- The native coherent recovery formula includes every grade and support sector. -/
theorem paperRFHMInsertion_reconstruction (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes)
    (v : JASPacketHilbert) :
    (packetOperator (jasGammaInsertionPacket x p P)).adjoint
        (packetOperator (jasGammaInsertionPacket x p P) v) +
      paperPacketDefect (jasGammaInsertionPacket x p P) v = v :=
  paperPacketDefect_reconstruction _ _

/-- Exact boundary of energy-only information: changing the arithmetic gain leaves both Born
probabilities unchanged. The coherent retained branch still carries the grade translation. -/
theorem paperRFHMInsertion_survivalLaw_independent_gain
    (x y : ℝ) (p : Nat.Primes) (P Q : Finset Nat.Primes) (v : PaperRFHMUnitState) :
    paperRFHMSurvivalLaw (jasGammaInsertionPacket x p P) v =
      paperRFHMSurvivalLaw (jasGammaInsertionPacket y p Q) v := by
  apply Law.ext
  intro b
  cases b
  · simp only [paperRFHMSurvivalLaw_false, paperPacketDefect_apply,
      paperRFHMInsertion_sourceSupport]
  · simp only [paperRFHMSurvivalLaw_true, paperPacket_norm_sq,
      paperRFHMInsertion_sourceSupport]

/-- Consequently the finite-law entropy of this native compression cannot recover its gain. -/
theorem paperRFHMInsertion_entropy_independent_gain
    (x y : ℝ) (p : Nat.Primes) (P Q : Finset Nat.Primes) (v : PaperRFHMUnitState) :
    (paperRFHMSurvivalLaw (jasGammaInsertionPacket x p P) v).entropy =
      (paperRFHMSurvivalLaw (jasGammaInsertionPacket y p Q) v).entropy := by
  rw [paperRFHMInsertion_survivalLaw_independent_gain x y p P Q v]

private theorem binaryLaw_ext_true {P Q : Law Bool} (h : P true = Q true) : P = Q := by
  have hp := P.total
  have hq := Q.total
  simp only [Fintype.sum_bool] at hp hq
  apply Law.ext
  intro b
  cases b
  · linarith
  · exact h

/-- Sharp positive classification: maximal branch entropy means exactly equal retained and
discarded energy, without a conclusion about the logarithmic grade or any Xi zero. -/
theorem paperRFHMSurvivalLaw_entropy_max_iff (s : JASRestrictionPacket)
    (v : PaperRFHMUnitState) :
    (paperRFHMSurvivalLaw s v).entropy = Real.log 2 ↔
      ‖packetOperator s v.val‖ ^ 2 = 1 / 2 := by
  constructor
  · intro h
    have hb := paperRFHMSurvivalLaw_energy_imbalance s v
    rw [h, sub_self] at hb
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hb (sq_nonneg _)))
  · intro h
    have heq : paperRFHMSurvivalLaw s v = Law.uniform Bool := by
      apply binaryLaw_ext_true
      simpa only [paperRFHMSurvivalLaw_true, Law.uniform_apply, Fintype.card_bool,
        Nat.cast_ofNat, one_div] using h
    rw [heq, Law.entropy_uniform]
    norm_num

/-- A literal support-and-grade basis state, already normalized by the native Hilbert theory. -/
def paperRFHMBasisState (i : JASPrimeSupport × JASLogGrade) : PaperRFHMUnitState :=
  ⟨packetBasis i, norm_packetBasis i⟩

/-- On every native basis state, the binary law records precisely whether the inserted prime was
present. All reversible grades have the same deterministic outcome for a fixed support. -/
theorem paperRFHMInsertion_basis_law (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes)
    (i : JASPrimeSupport × JASLogGrade) :
    paperRFHMSurvivalLaw (jasGammaInsertionPacket x p P) (paperRFHMBasisState i) =
      if p ∈ i.1 then Law.point false else Law.point true := by
  have hs : i.1 ⊆ jasFiniteSupportComplement {p} ↔ p ∉ i.1 := by
    constructor
    · intro h hp
      have hh := h hp
      simp [jasFiniteSupportComplement] at hh
    · intro hp q hq
      change q ∉ ({p} : Finset Nat.Primes)
      simpa only [Finset.mem_singleton] using
        (show q ≠ p from fun h => hp (h ▸ hq))
  apply binaryLaw_ext_true
  rw [paperRFHMSurvivalLaw_true]
  change ‖packetOperator (jasGammaInsertionPacket x p P) (packetBasis i)‖ ^ 2 = _
  rw [packetOperator_basis]
  by_cases hp : p ∈ i.1 <;>
    simp [jasGammaInsertionPacket, hs, hp, Law.point_apply]

/-- Every single basis state has zero branch entropy, irrespective of its reversible grade. -/
theorem paperRFHMInsertion_basis_entropy (x : ℝ) (p : Nat.Primes)
    (P : Finset Nat.Primes) (i : JASPrimeSupport × JASLogGrade) :
    (paperRFHMSurvivalLaw (jasGammaInsertionPacket x p P) (paperRFHMBasisState i)).entropy = 0 := by
  rw [paperRFHMInsertion_basis_law]
  split_ifs <;> exact Law.entropy_point _

end

end RHTower
