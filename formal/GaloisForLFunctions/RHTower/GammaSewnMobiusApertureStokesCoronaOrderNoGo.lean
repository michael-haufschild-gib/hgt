import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesDeningerTimeCorona

/-!
# No finite positive unitization of the zero-parameter Gamma-sewn Euler current

The completed local Deninger trace from P-G67 is positive on compact probes, but this positivity
cannot be extended to a finite coefficientwise-positive corona unit.  The indicator of the first
`N` powers of prime two is a rapid Kummer vector with every coordinate in the real interval
`[0,1]`.  Its zero-parameter Euler current is exactly `N log 2`, hence unbounded on that order
interval.

Thus the singular completion needed by Route P cannot be an ordinary positive unital extension of
the local prime distribution.  Any successful passivity mechanism must use a parameter-dependent
resolvent/reflection order or a genuinely renormalized signed channel.  This is stronger than mere
seminorm escape: it is an order-unit obstruction.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators Distributions FourierTransform

noncomputable section

namespace RHTower

/-- Prime two as the fixed corona ray. -/
def gammaSewnMobiusApertureStokesCoronaPrime : Nat.Primes :=
  ⟨2, Nat.prime_two⟩

/-- First `N` prime-power labels on the prime-two ray. -/
def gammaSewnMobiusApertureStokesCoronaPrimePowerFinset
    (N : ℕ) : Finset (Nat.Primes × ℕ) :=
  (Finset.range N).image
    (fun e => (gammaSewnMobiusApertureStokesCoronaPrime, e))

@[simp]
theorem mem_gammaSewnMobiusApertureStokesCoronaPrimePowerFinset
    (N e : ℕ) :
    (gammaSewnMobiusApertureStokesCoronaPrime, e) ∈
        gammaSewnMobiusApertureStokesCoronaPrimePowerFinset N ↔
      e < N := by
  simp [gammaSewnMobiusApertureStokesCoronaPrimePowerFinset]

theorem card_gammaSewnMobiusApertureStokesCoronaPrimePowerFinset
    (N : ℕ) :
    (gammaSewnMobiusApertureStokesCoronaPrimePowerFinset N).card = N := by
  rw [gammaSewnMobiusApertureStokesCoronaPrimePowerFinset,
    Finset.card_image_of_injective]
  · simp
  · intro e f h
    exact congrArg Prod.snd h

/-- Finite constant-one indicator on the first `N` prime-two Kummer axes. -/
def gammaSewnMobiusApertureStokesCoronaIndicator
    (N : ℕ) : DeningerHeightKothe :=
  ∑ pk ∈ gammaSewnMobiusApertureStokesCoronaPrimePowerFinset N,
    deningerKotheDelta deningerHeightKotheData
      (gammaSewnMobiusApertureStokesPrimePowerAxis pk)

/-- Every coefficient of the finite corona indicator is exactly zero or one. -/
theorem gammaSewnMobiusApertureStokesCoronaIndicator_coord
    (N : ℕ) (m : DeningerPrimeLattice) :
    ((gammaSewnMobiusApertureStokesCoronaIndicator N :
        DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m =
      if m ∈
          (gammaSewnMobiusApertureStokesCoronaPrimePowerFinset N).image
            gammaSewnMobiusApertureStokesPrimePowerAxis
      then 1 else 0 := by
  classical
  rw [gammaSewnMobiusApertureStokesCoronaIndicator,
    Submodule.coe_sum, Finset.sum_apply]
  by_cases hm : m ∈
      (gammaSewnMobiusApertureStokesCoronaPrimePowerFinset N).image
        gammaSewnMobiusApertureStokesPrimePowerAxis
  · rw [if_pos hm]
    rcases Finset.mem_image.mp hm with ⟨pk, hpk, rfl⟩
    rw [Finset.sum_eq_single pk]
    · simp
    · intro q hq hne
      have haxis :
          gammaSewnMobiusApertureStokesPrimePowerAxis pk ≠
            gammaSewnMobiusApertureStokesPrimePowerAxis q := by
        exact gammaSewnMobiusApertureStokesPrimePowerAxis_injective.ne
          hne.symm
      change
        (Pi.single
          (gammaSewnMobiusApertureStokesPrimePowerAxis q) (1 : ℂ) :
            DeningerPrimeLattice → ℂ)
            (gammaSewnMobiusApertureStokesPrimePowerAxis pk) = 0
      rw [Pi.single_eq_of_ne haxis]
    · exact fun h => (h hpk).elim
  · rw [if_neg hm, Finset.sum_eq_zero]
    intro pk hpk
    have hne :
        m ≠ gammaSewnMobiusApertureStokesPrimePowerAxis pk := by
      intro h
      apply hm
      exact Finset.mem_image.mpr ⟨pk, hpk, h.symm⟩
    change
      (Pi.single
        (gammaSewnMobiusApertureStokesPrimePowerAxis pk) (1 : ℂ) :
          DeningerPrimeLattice → ℂ) m = 0
    rw [Pi.single_eq_of_ne hne]

theorem gammaSewnMobiusApertureStokesCoronaIndicator_primePowerAxis_of_mem
    (N : ℕ) (pk : Nat.Primes × ℕ)
    (hpk : pk ∈ gammaSewnMobiusApertureStokesCoronaPrimePowerFinset N) :
    ((gammaSewnMobiusApertureStokesCoronaIndicator N :
        DeningerHeightKothe) : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis pk) = 1 := by
  rw [gammaSewnMobiusApertureStokesCoronaIndicator_coord, if_pos]
  exact Finset.mem_image.mpr ⟨pk, hpk, rfl⟩

theorem gammaSewnMobiusApertureStokesCoronaIndicator_primePowerAxis_of_not_mem
    (N : ℕ) (pk : Nat.Primes × ℕ)
    (hpk : pk ∉ gammaSewnMobiusApertureStokesCoronaPrimePowerFinset N) :
    ((gammaSewnMobiusApertureStokesCoronaIndicator N :
        DeningerHeightKothe) : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis pk) = 0 := by
  rw [gammaSewnMobiusApertureStokesCoronaIndicator_coord, if_neg]
  intro hm
  rcases Finset.mem_image.mp hm with ⟨q, hq, heq⟩
  exact hpk
    (gammaSewnMobiusApertureStokesPrimePowerAxis_injective heq.symm ▸ hq)

theorem primePowerFluxTerm_zero (pk : Nat.Primes × ℕ) :
    primePowerFluxTerm 0 pk = (Real.log (pk.1 : ℕ) : ℂ) := by
  simp [primePowerFluxTerm]

/-- The zero-parameter current of the `N`-axis indicator is exactly `N log 2`. -/
theorem gammaSewnMobiusApertureStokesCoronaIndicator_current_zero
    (N : ℕ) :
    gammaSewnMobiusApertureStokesComplexEulerDualPairing 0
        (gammaSewnMobiusApertureStokesCoronaIndicator N) =
      (N : ℂ) * (Real.log 2 : ℂ) := by
  rw [gammaSewnMobiusApertureStokesComplexEulerDualPairing]
  rw [tsum_eq_sum
    (s := gammaSewnMobiusApertureStokesCoronaPrimePowerFinset N)]
  · rw [Finset.sum_congr rfl (fun pk hpk => by
      rw [
        gammaSewnMobiusApertureStokesCoronaIndicator_primePowerAxis_of_mem
          N pk hpk,
        mul_one, primePowerFluxTerm_zero])]
    rw [show
      (∑ pk ∈ gammaSewnMobiusApertureStokesCoronaPrimePowerFinset N,
          (Real.log (pk.1 : ℕ) : ℂ)) =
        ∑ pk ∈ gammaSewnMobiusApertureStokesCoronaPrimePowerFinset N,
          (Real.log 2 : ℂ) by
      apply Finset.sum_congr rfl
      intro pk hpk
      rcases Finset.mem_image.mp hpk with ⟨e, he, rfl⟩
      rfl]
    simp [card_gammaSewnMobiusApertureStokesCoronaPrimePowerFinset]
  · intro pk hpk
    rw [
      gammaSewnMobiusApertureStokesCoronaIndicator_primePowerAxis_of_not_mem
        N pk hpk,
      mul_zero]

/-- Coordinatewise real order interval cut out by the proposed corona unit. -/
def GammaSewnMobiusApertureStokesCoronaRealUnitOrderInterval
    (a : DeningerHeightKothe) : Prop :=
  ∀ m : DeningerPrimeLattice,
    ((a : DeningerPrimeLattice → ℂ) m).im = 0 ∧
    0 ≤ ((a : DeningerPrimeLattice → ℂ) m).re ∧
    ((a : DeningerPrimeLattice → ℂ) m).re ≤ 1

theorem gammaSewnMobiusApertureStokesCoronaIndicator_mem_realUnitOrderInterval
    (N : ℕ) :
    GammaSewnMobiusApertureStokesCoronaRealUnitOrderInterval
      (gammaSewnMobiusApertureStokesCoronaIndicator N) := by
  intro m
  rw [gammaSewnMobiusApertureStokesCoronaIndicator_coord]
  split_ifs <;> norm_num

/-- **Order-unit obstruction.**  Zero-parameter Euler current is unbounded on the coefficientwise
unit interval.  Consequently it admits no finite positive order-unit extension whose unit
dominates all rapid tests in this interval. -/
theorem gammaSewnMobiusApertureStokesComplexEulerDualPairing_zero_not_orderBounded :
    ¬ ∃ M : ℝ, ∀ a : DeningerHeightKothe,
      GammaSewnMobiusApertureStokesCoronaRealUnitOrderInterval a →
        (gammaSewnMobiusApertureStokesComplexEulerDualPairing 0 a).re ≤ M := by
  rintro ⟨M, hM⟩
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (M / Real.log 2)
  have hbound := hM
    (gammaSewnMobiusApertureStokesCoronaIndicator N)
    (gammaSewnMobiusApertureStokesCoronaIndicator_mem_realUnitOrderInterval N)
  rw [gammaSewnMobiusApertureStokesCoronaIndicator_current_zero] at hbound
  simp [Complex.mul_re] at hbound
  have hlogre : (Complex.log (2 : ℂ)).re = Real.log 2 := by
    change
      (Complex.log (((2 : ℕ) : ℂ))).re =
        Real.log ((2 : ℕ) : ℝ)
    rw [← Complex.natCast_log]
    rfl
  rw [hlogre] at hbound
  have hstrict : M < (N : ℝ) * Real.log 2 := by
    rw [div_lt_iff₀ hlog] at hN
    exact hN
  linarith

end RHTower
