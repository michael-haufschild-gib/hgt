import GaloisForLFunctions.RHTower.JointAncestryGammaBooleanClosedCreation
import Mathlib.Analysis.PSeries

/-!
# Uniform arithmetic ceilings for literal Gamma support weights

The state-dependent insertion gain is bounded by its vacuum value, and the vacuum value by
`1/(p+1)`. Thus every synchronized compound is bounded by the corresponding prime reciprocal
product. These are source estimates, uniform over the complete Boolean support lattice.
-/

namespace RHTower

noncomputable section

open scoped BigOperators

theorem gammaSewnSynchronizedLcmWeight_singleton_le
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnSynchronizedLcmWeight x {p} ≤ ((p : ℝ) + 1)⁻¹ := by
  rw [gammaSewnSynchronizedLcmWeight_singleton hx p,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have heq : (p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹) = ((p : ℝ) + 1)⁻¹ := by
    field_simp
  rw [heq]
  exact mul_le_of_le_one_left (by positivity)
    (gammaSewnMobiusValuationContractionMultiplier_lt_one hx p).le

/-- Synchronizing with an existing support never increases the vacuum insertion coefficient. -/
theorem gammaSewnSynchronizedLcmInsertionGain_le_singleton
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes)
    {P : Finset Nat.Primes} (hP : P.Nonempty) :
    gammaSewnSynchronizedLcmInsertionGain x p P ≤
      gammaSewnSynchronizedLcmWeight x {p} := by
  let q := xiMobiusContinuousApertureDiskNode x p
  let R := gammaSewnSynchronizedLcmNode x P
  have hq0 : 0 ≤ q := (xiMobiusContinuousApertureDiskNode_pos x p).le
  have hq1 : q < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hR := gammaSewnSynchronizedLcmNode_nonneg_lt_one hx hP
  have hR0 : 0 ≤ R := hR.1
  have hR1 : R < 1 := hR.2
  have hqR : q * R ≤ R := mul_le_of_le_one_left hR0 hq1.le
  have hden : 0 < 1 - q * R := by linarith
  have hnum : (1 - q) * (1 - R) ≤ 1 - q * R := by
    have hfirst : (1 - q) * (1 - R) ≤ 1 - R :=
      mul_le_of_le_one_left (by linarith) (by linarith)
    linarith
  have hratio : (1 - q) * (1 - R) / (1 - q * R) ≤ 1 :=
    (div_le_one hden).mpr hnum
  rw [gammaSewnSynchronizedLcmWeight_singleton hx p]
  let A := gammaSewnMobiusValuationContractionMultiplier x p *
    (xiTransversePrimeApertureDiskNode 1 p / (1 + xiTransversePrimeApertureDiskNode 1 p))
  have hA : 0 ≤ A := by
    have hnode := (xiTransversePrimeApertureDiskNode_pos 1 p).le
    have hmult := (gammaSewnMobiusValuationContractionMultiplier_pos x p).le
    dsimp [A]
    positivity
  change gammaSewnSynchronizedLcmInsertionGain x p P ≤ A
  calc
    gammaSewnSynchronizedLcmInsertionGain x p P =
        A * ((1 - q) * (1 - R) / (1 - q * R)) := by
      dsimp [gammaSewnSynchronizedLcmInsertionGain, A, q, R]
      ring
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left hratio hA
    _ = A := mul_one A

/-- The complete synchronized coefficient has a multiplicative arithmetic majorant, including
the exceptional Boolean vacuum. -/
theorem gammaSewnSynchronizedLcmWeight_le_reciprocalProduct
    {x : ℝ} (hx : 0 < x) (P : Finset Nat.Primes) :
    gammaSewnSynchronizedLcmWeight x P ≤ ∏ p ∈ P, ((p : ℝ) + 1)⁻¹ := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [gammaSewnSynchronizedLcmWeight]
  | @insert p P hp ih =>
    by_cases hP : P = ∅
    · subst P
      simpa using gammaSewnSynchronizedLcmWeight_singleton_le hx p
    · have hPne := Finset.nonempty_iff_ne_empty.mpr hP
      rw [gammaSewnSynchronizedLcmWeight_insert hx hPne hp, Finset.prod_insert hp]
      exact mul_le_mul
        ((gammaSewnSynchronizedLcmInsertionGain_le_singleton hx p hPne).trans
          (gammaSewnSynchronizedLcmWeight_singleton_le hx p)) ih
        (jasGammaSynchronizedLcmWeight_pos hx P).le (by positivity)

theorem gammaSewnSynchronizedLcmWeight_le_primeReciprocalProduct
    {x : ℝ} (hx : 0 < x) (P : Finset Nat.Primes) :
    gammaSewnSynchronizedLcmWeight x P ≤ ∏ p ∈ P, (p : ℝ)⁻¹ := by
  apply (gammaSewnSynchronizedLcmWeight_le_reciprocalProduct hx P).trans
  apply Finset.prod_le_prod
  · intro p _; positivity
  · intro p _
    have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
    exact (inv_le_inv₀ (by linarith : 0 < (p : ℝ) + 1) hp).mpr (by linarith)

theorem summable_primeReciprocal_sq :
    Summable (fun p : Nat.Primes => ((p : ℝ)⁻¹) ^ 2) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) :=
    hnat.comp_injective Subtype.val_injective
  simpa only [inv_pow] using hprime

/-- The native Boolean creator is uniformly bounded in its support coordinate. The actual
theta multiplier remains unbounded and is handled by the completed source's next grade. -/
theorem jasGammaBooleanCreationEnergy_bounds
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) (P : Finset Nat.Primes) :
    0 ≤ jasGammaBooleanCreationEnergy x p P ∧
      jasGammaBooleanCreationEnergy x p P ≤ ((p : ℝ) + 1)⁻¹ := by
  classical
  by_cases hp : p ∈ P
  · simp only [jasGammaBooleanCreationEnergy, if_pos hp]
    exact ⟨le_rfl, by positivity⟩
  rw [jasGammaBooleanCreationEnergy, if_neg hp]
  refine ⟨(jasGammaBooleanInsertionGain_pos hx p P).le, ?_⟩
  by_cases hP : P = ∅
  · subst P
    simpa [jasGammaBooleanInsertionGain, gammaSewnSynchronizedLcmWeight] using
      gammaSewnSynchronizedLcmWeight_singleton_le hx p
  · have hPne := Finset.nonempty_iff_ne_empty.mpr hP
    rw [jasGammaBooleanInsertionGain_eq_gamma hx hPne hp]
    exact (gammaSewnSynchronizedLcmInsertionGain_le_singleton hx p hPne).trans
      (gammaSewnSynchronizedLcmWeight_singleton_le hx p)

end

end RHTower
