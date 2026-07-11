import GaloisForLFunctions.RHTower.PrimeClockShaleDiagonal

/-!
# Continuous prime-clock sector witnesses vanish

The reflected prime-clock displacement is square-summable only on the critical line.  Since the
complement of that line is dense, a continuous family whose nonzero values require square
summability must vanish everywhere.

This is the topological obstruction to obtaining a nonzero normal clock-change intertwiner as an
ordinary continuous or holomorphic operator family.  Any viable source construction must be
singular, distributional, or derived at the critical seam.
-/

noncomputable section

namespace RHTower

/-- The complement of the critical line is dense in the spectral plane. -/
theorem dense_offCriticalLine :
    Dense {s : ℂ | s.re ≠ 1 / 2} := by
  have hreal : Dense ({(1 / 2 : ℝ)}ᶜ) := dense_compl_singleton (1 / 2 : ℝ)
  have hpull : Dense (Complex.re ⁻¹' ({(1 / 2 : ℝ)}ᶜ)) :=
    hreal.preimage Complex.isOpenMap_re
  simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hpull

/-- A continuous family supported only on the critical line vanishes identically. -/
theorem continuous_eq_zero_of_eq_zero_offCriticalLine
    {E : Type*} [TopologicalSpace E] [T2Space E] [Zero E]
    (U : ℂ → E) (hU : Continuous U)
    (hoff : ∀ s : ℂ, s.re ≠ 1 / 2 → U s = 0) :
    U = 0 := by
  apply Continuous.ext_on dense_offCriticalLine hU continuous_const
  intro s hs
  exact hoff s hs

/-- Pointwise form of `continuous_eq_zero_of_eq_zero_offCriticalLine`. -/
theorem continuous_apply_eq_zero_of_eq_zero_offCriticalLine
    {E : Type*} [TopologicalSpace E] [T2Space E] [Zero E]
    (U : ℂ → E) (hU : Continuous U)
    (hoff : ∀ s : ℂ, s.re ≠ 1 / 2 → U s = 0)
    (s : ℂ) :
    U s = 0 := by
  rw [continuous_eq_zero_of_eq_zero_offCriticalLine U hU hoff]
  rfl

/--
A continuous witness family vanishes if every nonzero value requires the reflected prime-clock
displacement to be square-summable.

For a family of normal CCR intertwiners, the last hypothesis is supplied by the coherent-sector
implementability criterion.  The theorem therefore isolates the singularity requirement without
formalizing operator-algebra representation theory.
-/
theorem continuous_eq_zero_of_nonzero_imp_primeClockSummable
    {E : Type*} [TopologicalSpace E] [T2Space E] [Zero E]
    (U : ℂ → E) (hU : Continuous U)
    (hsector : ∀ s : ℂ, U s ≠ 0 → Summable (primeClockReflectionEnergy s.re)) :
    U = 0 := by
  apply continuous_eq_zero_of_eq_zero_offCriticalLine U hU
  intro s hs
  by_contra hne
  exact hs ((summable_primeClockReflectionEnergy_iff s.re).1 (hsector s hne))

/--
Consequently, a continuous sector-witness family that is required to be nonzero at every `xi` zero
would imply that `xi` has no zeros at all.  This is a no-go statement for the proposed interface,
not a zero-free theorem: its hypotheses cannot hold for the completed zeta source.
-/
theorem xi_ne_zero_of_continuous_primeClockSectorWitness
    {E : Type*} [TopologicalSpace E] [T2Space E] [Zero E]
    (U : ℂ → E) (hU : Continuous U)
    (hsector : ∀ s : ℂ, U s ≠ 0 → Summable (primeClockReflectionEnergy s.re))
    (hzeroWitness : ∀ rho : ℂ, xi rho = 0 → U rho ≠ 0) :
    ∀ rho : ℂ, xi rho ≠ 0 := by
  have hvanish := continuous_eq_zero_of_nonzero_imp_primeClockSummable U hU hsector
  intro rho hzero
  exact hzeroWitness rho hzero (by
    simpa only [Pi.zero_apply] using congrFun hvanish rho)

end RHTower
