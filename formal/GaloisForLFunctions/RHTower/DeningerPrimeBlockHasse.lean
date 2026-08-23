import GaloisForLFunctions.RHTower.DeningerPrimeBlockRestrictionAssembly

/-!
# Hasse quotient for full prime-block restrictions

The quotient of a global source by vectors invisible at every prime is exactly the space of
simultaneous prime profiles actually realized in the Hilbert direct sum.  The assembled Green
energy descends faithfully to this quotient: it vanishes exactly on the zero class and is strictly
positive exactly on nonzero classes.
-/

namespace RHTower

open Filter Topology
open scoped ENNReal BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Kp : Nat.Primes → Type*}
  [∀ p, NormedAddCommGroup (Kp p)] [∀ p, InnerProductSpace ℝ (Kp p)]

/-- Global vectors modulo simultaneous prime invisibility are exactly the realized square-summable
family of prime-packet restrictions. -/
noncomputable def deningerPrimeBlockHasseQuotientEquivRealizedProfiles
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ)) :
    (E ⧸ LinearMap.ker (deningerPrimeRestrictionLinearMap restriction hsummable)) ≃ₗ[ℝ]
      LinearMap.range (deningerPrimeRestrictionLinearMap restriction hsummable) :=
  LinearMap.quotKerEquivRange _

@[simp] theorem deningerPrimeBlockHasseQuotientEquivRealizedProfiles_mk
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    (x : E) :
    deningerPrimeBlockHasseQuotientEquivRealizedProfiles restriction hsummable
        (Submodule.Quotient.mk x) =
      ⟨deningerPrimeRestrictionLinearMap restriction hsummable x,
        ⟨x, rfl⟩⟩ := by
  rfl

/-- The kernel of simultaneous prime restriction consists exactly of vectors vanishing at every
prime packet. -/
theorem deningerPrimeBlockHasse_mem_ker_iff
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    (x : E) :
    x ∈ LinearMap.ker (deningerPrimeRestrictionLinearMap restriction hsummable) ↔
      ∀ p, restriction p x = 0 := by
  change deningerPrimeRestrictionLinearMap restriction hsummable x = 0 ↔ _
  constructor
  · intro h p
    exact congrArg (fun z : DeningerHilbertSum Kp => z p) h
  · intro h
    ext p
    exact h p

/-- Two global vectors represent the same Hasse quotient class exactly when all prime-packet
restrictions agree. -/
theorem deningerPrimeBlock_congr_hasse_iff
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    (x y : E) :
    x - y ∈ LinearMap.ker (deningerPrimeRestrictionLinearMap restriction hsummable) ↔
      ∀ p, restriction p x = restriction p y := by
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
  constructor
  · intro h p
    exact congrArg (fun z : DeningerHilbertSum Kp => z p) h
  · intro h
    ext p
    exact h p

variable [∀ p, CompleteSpace (Kp p)]

/-- The assembled all-prime Green energy vanishes exactly on the zero simultaneous-local quotient
class. -/
theorem deningerPrimeBlockHasse_zeroClass_iff_energy_zero
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    Submodule.Quotient.mk x =
        (0 : E ⧸ LinearMap.ker
          (deningerPrimeRestrictionLinearMap restriction hsummable)) ↔
      deningerPrimeRestrictionSummedGreenForm
        restriction hsummable hC hBessel x x = 0 := by
  rw [Submodule.Quotient.mk_eq_zero,
    deningerPrimeBlockHasse_mem_ker_iff restriction hsummable,
    deningerPrimeRestrictionSummedGreenForm_self_eq_zero_iff]

/-- The assembled all-prime Green energy is strictly positive exactly on nonzero
simultaneous-local quotient classes. -/
theorem deningerPrimeBlockHasse_energy_pos_iff_class_ne_zero
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    0 < deningerPrimeRestrictionSummedGreenForm
        restriction hsummable hC hBessel x x ↔
      Submodule.Quotient.mk x ≠
        (0 : E ⧸ LinearMap.ker
          (deningerPrimeRestrictionLinearMap restriction hsummable)) := by
  constructor
  · intro hpos hzero
    have henergy :=
      (deningerPrimeBlockHasse_zeroClass_iff_energy_zero
        restriction hsummable hC hBessel x).1 hzero
    exact (ne_of_gt hpos) henergy
  · intro hne
    have henergy :
        deningerPrimeRestrictionSummedGreenForm
          restriction hsummable hC hBessel x x ≠ 0 := by
      intro hzero
      exact hne ((deningerPrimeBlockHasse_zeroClass_iff_energy_zero
        restriction hsummable hC hBessel x).2 hzero)
    exact lt_of_le_of_ne
      (deningerPrimeRestrictionSummedGreenForm_nonneg
        restriction hsummable hC hBessel x) (Ne.symm henergy)

end

end RHTower
