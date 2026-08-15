import GaloisForLFunctions.RHTower.MertensSecondTheorem
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The degree-one Dirichlet-character case of Selberg C1

For a complex Dirichlet character, every unit value has norm one and every nonunit value is zero.
Thus its prime reciprocal energy is the ordinary prime reciprocal sum minus exactly the finitely
many primes dividing its level.  For the associated primitive character, that level is its
conductor, so the same identity gives the literal conductor-prime correction.

The distinction is necessary: an imprimitive character may vanish at primes dividing its chosen
level but not its conductor.  This module makes no false conductor-level identification for such
a character.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Prime reciprocal energy of the coefficient system of a complex Dirichlet character. -/
def dirichletCharacterPrimeRecipEnergy {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 N,
    if n.Prime then ‖χ (n : ZMod q)‖ ^ 2 / (n : ℝ) else 0

/-- Contribution of the primes dividing the selected level. -/
def dirichletCharacterLevelPrimeCorrection (q N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 N,
    if n.Prime ∧ n ∣ q then ((n : ℝ)⁻¹) else 0

/-- Full finite level-prime correction, once the cutoff contains the positive level. -/
def dirichletCharacterLevelPrimeCorrectionTotal (q : ℕ) : ℝ :=
  dirichletCharacterLevelPrimeCorrection q q

/-- Full prime correction attached to the conductor of a Dirichlet character. -/
def dirichletCharacterConductorPrimeCorrection {q : ℕ} (χ : DirichletCharacter ℂ q) : ℝ :=
  dirichletCharacterLevelPrimeCorrectionTotal χ.conductor

private theorem norm_sq_dirichletCharacter_apply_eq_indicator {q n : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ‖χ (n : ZMod q)‖ ^ 2 = if n.Coprime q then 1 else 0 := by
  classical
  by_cases hcop : n.Coprime q
  · rw [if_pos hcop]
    have hunit : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hcop
    calc
      ‖χ (n : ZMod q)‖ ^ 2 = ‖χ (hunit.unit : ZMod q)‖ ^ 2 := by
        rw [hunit.unit_spec]
      _ = 1 := by rw [DirichletCharacter.unit_norm_eq_one χ hunit.unit]; norm_num
  · rw [if_neg hcop]
    have hunit : ¬ IsUnit (n : ZMod q) := by
      rwa [ZMod.isUnit_iff_coprime]
    rw [χ.map_nonunit hunit, norm_zero]
    norm_num

/-- Exact finite-cutoff C1 identity for any complex Dirichlet character.  The correction is by
the selected level, not generally by the conductor. -/
theorem dirichletCharacterPrimeRecipEnergy_eq {q N : ℕ}
    (χ : DirichletCharacter ℂ q) :
    dirichletCharacterPrimeRecipEnergy χ N =
      primeRecipSum N - dirichletCharacterLevelPrimeCorrection q N := by
  classical
  rw [dirichletCharacterPrimeRecipEnergy, primeRecipSum,
    dirichletCharacterLevelPrimeCorrection, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hp : n.Prime
  · rw [if_pos hp, primeRecipWeight, if_pos hp,
      norm_sq_dirichletCharacter_apply_eq_indicator]
    by_cases hd : n ∣ q
    · have hncop : ¬ n.Coprime q := fun hcop => (hp.coprime_iff_not_dvd.mp hcop) hd
      rw [if_neg hncop]
      simp [hp, hd]
    · have hcop : n.Coprime q := hp.coprime_iff_not_dvd.mpr hd
      rw [if_pos hcop]
      simp [hp, hd]
  · simp [hp, primeRecipWeight]

/-- Once a positive level lies below cutoff, its correction has stabilized to the finite total. -/
theorem dirichletCharacterLevelPrimeCorrection_eq_total_of_le {q N : ℕ}
    (hq0 : 0 < q) (hN : q ≤ N) :
    dirichletCharacterLevelPrimeCorrection q N =
      dirichletCharacterLevelPrimeCorrectionTotal q := by
  unfold dirichletCharacterLevelPrimeCorrectionTotal dirichletCharacterLevelPrimeCorrection
  symm
  refine Finset.sum_subset ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hN⟩
  · intro n hnN hnq
    have hndvd : ¬ n ∣ q := by
      intro hdvd
      apply hnq
      simp only [Finset.mem_Icc]
      exact ⟨Nat.zero_le _, Nat.le_of_dvd hq0 hdvd⟩
    simp [hndvd]

/-- Mertens' second theorem for a positive-level Dirichlet character's coefficient energy. -/
theorem tendsto_dirichletCharacterPrimeRecipEnergy_sub_logLog {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    Tendsto
      (fun N : ℕ => dirichletCharacterPrimeRecipEnergy χ N - Real.log (Real.log N)) atTop
      (nhds (mertensSecondConstant - dirichletCharacterLevelPrimeCorrectionTotal q)) := by
  have hbase := tendsto_primeRecipSum_sub_logLog.sub_const
    (dirichletCharacterLevelPrimeCorrectionTotal q)
  refine hbase.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop q] with N hN
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [dirichletCharacterPrimeRecipEnergy_eq,
    dirichletCharacterLevelPrimeCorrection_eq_total_of_le hq0 hN]
  ring

/-- The primitive coefficient system loses exactly the conductor primes. -/
theorem primitiveDirichletCharacterPrimeRecipEnergy_eq {q N : ℕ}
    (χ : DirichletCharacter ℂ q) :
    dirichletCharacterPrimeRecipEnergy χ.primitiveCharacter N =
      primeRecipSum N - dirichletCharacterLevelPrimeCorrection χ.conductor N :=
  dirichletCharacterPrimeRecipEnergy_eq χ.primitiveCharacter

/-- Mertens' second theorem for the primitive coefficient system, with its finite
conductor-prime correction. -/
theorem tendsto_primitiveDirichletCharacterPrimeRecipEnergy_sub_logLog {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    Tendsto
      (fun N : ℕ => dirichletCharacterPrimeRecipEnergy χ.primitiveCharacter N -
        Real.log (Real.log N)) atTop
      (nhds (mertensSecondConstant - dirichletCharacterConductorPrimeCorrection χ)) := by
  letI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  simpa only [dirichletCharacterConductorPrimeCorrection] using
    (tendsto_dirichletCharacterPrimeRecipEnergy_sub_logLog χ.primitiveCharacter)

end

end RHTower
