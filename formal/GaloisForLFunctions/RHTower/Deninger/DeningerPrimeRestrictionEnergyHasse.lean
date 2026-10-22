import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeBlockRestrictionAssembly

/-!
# Hasse detection by all-prime Deninger Green energy

The assembled Green energy is turned into a local-global separation interface.  Equality of all
prime-packet restrictions is exactly zero energy of the global difference.  A nonzero global
energy therefore has a concrete prime witness.  Finally, definiteness of this energy is equivalent
to joint injectivity of the entire local restriction family.
-/

namespace RHTower

open Filter Topology
open scoped ENNReal BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Kp : Nat.Primes → Type*}
  [∀ p, NormedAddCommGroup (Kp p)] [∀ p, InnerProductSpace ℝ (Kp p)]
  [∀ p, CompleteSpace (Kp p)]

/-- Two source vectors have equal data at every prime-place exactly when their difference has zero
assembled Green energy. -/
theorem deningerPrimeRestrictionEnergy_sub_eq_zero_hasse_iff
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x y : E) :
    deningerPrimeRestrictionSummedGreenForm restriction hsummable hC hBessel
        (x - y) (x - y) = 0 ↔
      ∀ p, restriction p x = restriction p y := by
  rw [deningerPrimeRestrictionSummedGreenForm_self_eq_zero_iff]
  simp only [map_sub, sub_eq_zero]

/-- Nonzero global Green energy is witnessed by a nonzero restriction at one prime-place. -/
theorem deningerPrimeRestrictionEnergy_ne_zero_iff_exists_localWitness
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    deningerPrimeRestrictionSummedGreenForm restriction hsummable hC hBessel x x ≠ 0 ↔
      ∃ p, restriction p x ≠ 0 := by
  classical
  constructor
  · intro henergy
    by_contra hno
    apply henergy
    apply (deningerPrimeRestrictionSummedGreenForm_self_eq_zero_iff
      restriction hsummable hC hBessel x).mpr
    intro p
    by_contra hp
    exact hno ⟨p, hp⟩
  · rintro ⟨p, hp⟩ henergy
    exact hp ((deningerPrimeRestrictionSummedGreenForm_self_eq_zero_iff
      restriction hsummable hC hBessel x).mp henergy p)

/-- The assembled all-prime Green energy separates source vectors exactly when the prime-packet
restrictions are jointly injective. -/
theorem deningerPrimeRestrictionEnergy_separates_iff_jointly_injective
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ)) :
    (∀ x y : E,
      deningerPrimeRestrictionSummedGreenForm restriction hsummable hC hBessel
          (x - y) (x - y) = 0 ↔ x = y) ↔
      ∀ x : E, (∀ p, restriction p x = 0) → x = 0 := by
  constructor
  · intro hseparates x hx
    apply (hseparates x 0).mp
    apply (deningerPrimeRestrictionEnergy_sub_eq_zero_hasse_iff
      restriction hsummable hC hBessel x 0).mpr
    simpa using hx
  · intro hinjective x y
    rw [deningerPrimeRestrictionEnergy_sub_eq_zero_hasse_iff]
    constructor
    · intro hlocal
      apply sub_eq_zero.mp
      apply hinjective
      intro p
      simp only [map_sub, sub_eq_zero]
      exact hlocal p
    · rintro rfl p
      rfl

/-! ## Premise-free specialization to the actual full prime-block carrier -/

variable {Kp' : Nat.Primes → Type*}
  [∀ p, NormedAddCommGroup (Kp' p)] [∀ p, InnerProductSpace ℝ (Kp' p)]
  [∀ p, CompleteSpace (Kp' p)]

/-- On the actual full prime-block Hilbert carrier, zero energy of a difference is exactly
coordinatewise equality at every prime. -/
theorem deningerPrimeBlockEnergy_sub_eq_zero_hasse_iff
    (x y : DeningerHilbertSum Kp') :
    deningerPrimeBlockSummedGreenForm (x - y) (x - y) = 0 ↔
      ∀ p, x p = y p := by
  rw [deningerPrimeBlockSummedGreenForm_self_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro rfl p
    rfl
  · intro h
    apply lp.ext
    funext p
    exact h p

/-- Every nonzero actual full-block Green energy has a prime coordinate witnessing it. -/
theorem deningerPrimeBlockEnergy_ne_zero_iff_exists_primeWitness
    (x : DeningerHilbertSum Kp') :
    deningerPrimeBlockSummedGreenForm x x ≠ 0 ↔ ∃ p, x p ≠ 0 := by
  classical
  constructor
  · intro henergy
    by_contra hno
    apply henergy
    apply (deningerPrimeBlockSummedGreenForm_self_eq_zero_iff x).mpr
    apply lp.ext
    funext p
    by_contra hp
    exact hno ⟨p, hp⟩
  · rintro ⟨p, hp⟩ henergy
    have hx := (deningerPrimeBlockSummedGreenForm_self_eq_zero_iff x).mp henergy
    exact hp (congrArg (fun z : DeningerHilbertSum Kp' => z p) hx)

/-- The actual all-prime full-block Green form is strictly positive on every nonzero vector. -/
theorem deningerPrimeBlockEnergy_pos_iff_ne_zero
    (x : DeningerHilbertSum Kp') :
    0 < deningerPrimeBlockSummedGreenForm x x ↔ x ≠ 0 := by
  constructor
  · intro hpos hx
    subst x
    exact (lt_irrefl (0 : ℝ)) (by simpa only [map_zero] using hpos)
  · intro hx
    have henergy : deningerPrimeBlockSummedGreenForm x x ≠ 0 := fun hzero =>
      hx ((deningerPrimeBlockSummedGreenForm_self_eq_zero_iff x).mp hzero)
    exact lt_of_le_of_ne (deningerPrimeBlockSummedGreenForm_nonneg x) (Ne.symm henergy)

end

end RHTower
