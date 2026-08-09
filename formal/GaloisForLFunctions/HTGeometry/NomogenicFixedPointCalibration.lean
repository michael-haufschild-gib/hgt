import GaloisForLFunctions.HTGeometry.ConstitutiveExtensionCarry

/-!
# Nomogenic fixed-point calibration

One periodic source word and its fixed phase quotient couple recurrent observation, nonclosed
lifted state, nonzero carry, endpoint-decoder failure, and unbounded finite-prefix history.  This is
the smallest exact calibration of the least/rational/greatest fixed-point interpretation proposed
for nomogenic fixed-point dynamics.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The length-`n` well-founded approximation to the periodic `ZMod 4` source history. -/
def nomogenicSourcePrefix (n : ℕ) : List ConstitutiveCarryMiddle :=
  List.ofFn (fun i : Fin n => constitutiveCarryHistory i)

/-- The length-`n` observed approximation after quotienting the source history modulo two. -/
def nomogenicObserverPrefix (n : ℕ) : List ConstitutiveBit :=
  List.ofFn (fun i : Fin n => constitutiveBaseHistory i)

@[simp] theorem nomogenicSourcePrefix_length (n : ℕ) :
    (nomogenicSourcePrefix n).length = n := by
  simp [nomogenicSourcePrefix]

@[simp] theorem nomogenicObserverPrefix_length (n : ℕ) :
    (nomogenicObserverPrefix n).length = n := by
  simp [nomogenicObserverPrefix]

/-- The observer history is the exact quotient of the source history at every time. -/
theorem nomogenicHistory_quotient (n : ℕ) :
    constitutiveCarryQuotient (constitutiveCarryHistory n) = constitutiveBaseHistory n := by
  exact constitutiveCarryQuotient_natCast n

/-- One observed period never closes the nonsplit source history. -/
theorem nomogenicSourceHistory_not_period_two (n : ℕ) :
    constitutiveCarryHistory (n + 2) ≠ constitutiveCarryHistory n := by
  rw [constitutiveCarryHistory_period_increment]
  intro h
  have h' : constitutiveCarryHistory n + constitutiveCarryInclusion 1 =
      constitutiveCarryHistory n + 0 := by simpa using h
  exact constitutiveCarryHistory_increment_ne_zero (add_left_cancel h')

/-- No pointwise decoder of the observed state reconstructs the full source trajectory. -/
theorem nomogenicHistory_no_decoder :
    ¬ ∃ d : ConstitutiveBit → ConstitutiveCarryMiddle,
      ∀ n : ℕ, d (constitutiveBaseHistory n) = constitutiveCarryHistory n := by
  rintro ⟨d, hd⟩
  have hbase := constitutiveBaseHistory_period_two 0
  have hsource : constitutiveCarryHistory (0 + 2) = constitutiveCarryHistory 0 := by
    rw [← hd (0 + 2), ← hd 0, hbase]
  exact nomogenicSourceHistory_not_period_two 0 hsource

/-- Prefix depth is unbounded even though the observed endpoint has period two. -/
theorem nomogenicSourcePrefix_unbounded (bound : ℕ) :
    ∃ n : ℕ, bound < (nomogenicSourcePrefix n).length := by
  refine ⟨bound + 1, ?_⟩
  simp

/-- **Periodic producer/phase quotient/open-prefix law.**  A single source history and one declared
quotient simultaneously produce closed observer recurrence, nonzero lifted holonomy, binary carry,
failure of endpoint reconstruction, and unbounded well-founded prefix depth. -/
theorem nomogenicPeriodicProducer_phaseQuotient_recurrence_openPrefix :
    (∀ n : ℕ,
      constitutiveCarryQuotient (constitutiveCarryHistory n) = constitutiveBaseHistory n) ∧
    (∀ n : ℕ, constitutiveBaseHistory (n + 2) = constitutiveBaseHistory n) ∧
    (∀ n : ℕ, constitutiveCarryHistory (n + 2) =
      constitutiveCarryHistory n + constitutiveCarryInclusion 1) ∧
    constitutiveCarryInclusion 1 ≠ 0 ∧
    (∀ n : ℕ, constitutiveCarryHistory (n + 2) ≠ constitutiveCarryHistory n) ∧
    (∀ n : ℕ, constitutiveCarryHistory (n + 4) = constitutiveCarryHistory n) ∧
    (¬ ∃ d : ConstitutiveBit → ConstitutiveCarryMiddle,
      ∀ n : ℕ, d (constitutiveBaseHistory n) = constitutiveCarryHistory n) ∧
    (∀ n : ℕ, (nomogenicSourcePrefix n).length = n) ∧
    (∀ bound : ℕ, ∃ n : ℕ, bound < (nomogenicSourcePrefix n).length) ∧
    (constitutiveCarrySection 1 + constitutiveCarrySection 1 -
      constitutiveCarrySection (1 + 1) = constitutiveCarryInclusion 1) := by
  exact ⟨nomogenicHistory_quotient,
    constitutiveBaseHistory_period_two,
    constitutiveCarryHistory_period_increment,
    constitutiveCarryHistory_increment_ne_zero,
    nomogenicSourceHistory_not_period_two,
    constitutiveCarryHistory_period_four,
    nomogenicHistory_no_decoder,
    nomogenicSourcePrefix_length,
    nomogenicSourcePrefix_unbounded,
    constitutiveCarry_one_one⟩

end GaloisForLFunctions.HTGeometry
