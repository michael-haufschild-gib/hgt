import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.JointLaw
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.VacuumBlend

/-! # Exact marginal ambiguity for simultaneous prime clocks -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open MeasureTheory Filter Topology
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Equal mixture of two exterior occupation laws. -/
def observationMixture (v w : MissingWave) : MissingWave :=
  lawOmission (midpointExterior (exteriorLaw v) (occupationProbability w) (occupationLaw_nonneg w) (occupationLaw_hasSum w))

private theorem mixture_probability (v w : MissingWave) (n : ℕ+) :
    occupationProbability (observationMixture v w) n = (occupationProbability v n + occupationProbability w n)/2 :=
  congrFun (lawOmission_probability _) n

private theorem selected_mixture (v w : MissingWave) (P : ℕ+ → Prop) :
    selectedMass (occupationProbability (observationMixture v w)) P =
      (selectedMass (occupationProbability v) P + selectedMass (occupationProbability w) P)/2 := by
  have hv := (selected_summable (occupationLaw_hasSum v).summable P).hasSum
  have hw := (selected_summable (occupationLaw_hasSum w).summable P).hasSum
  apply HasSum.tsum_eq
  apply ((hv.add hw).div_const 2).congr_fun
  intro n
  by_cases h : P n <;> simp [h,mixture_probability]

theorem selected_insertion (a : ℕ+) (v : MissingWave) (P : ℕ+ → Prop) :
    selectedMass (occupationProbability (insertedWave a v)) P =
      selectedMass (occupationProbability v) (fun n => P (a*n)) := by
  rw [insertedWave_probability]
  apply HasSum.tsum_eq
  apply (inserted_hasSum_iff a _ (fun n x => if P n then x else 0) (fun n => by simp) _).mpr
  exact (selected_summable (occupationLaw_hasSum v).summable _).hasSum

theorem whole_block_invisible (p : Nat.Primes) (D n : ℕ+) :
    occupationPhase (primeClockTime p D) (primeRayLabel p D.val*n) = occupationPhase (primeClockTime p D) n := by
  have hn : n ≤ primeRayLabel p D.val*n := by
    change n.val ≤ (primeRayLabel p D.val).val*n.val
    exact Nat.le_mul_of_pos_left _ (primeRayLabel p D.val).pos
  apply Eq.symm
  apply (primeClock_alias_iff p D _ _ hn).mpr
  exact ⟨1,by rw [Nat.mul_one,mul_comm]⟩

private theorem rectangle_marginal {X : Type*} [MeasurableSpace X] (Z : ℕ+ → X) (v : MissingWave) (a b : ℕ+)
    (hinv : (∀ n, Z (a*n) = Z n) ∨ (∀ n, Z (b*n) = Z n)) :
    labelReportLaw (observationMixture v (insertedWave (a*b) v)) Z =
      labelReportLaw (observationMixture (insertedWave a v) (insertedWave b v)) Z := by
  apply labelReportLaw_ext
  intro s _
  rw [selected_mixture,selected_mixture]
  simp only [selected_insertion]
  rcases hinv with ha | hb
  · simp only [mul_assoc,ha]
  · simp only [show a*b = b*a from mul_comm _ _,mul_assoc,hb,add_comm]

/-- Two separate laws at arbitrary prescribed prime denominators lose their joint correlation. -/
theorem primeClock_marginals_ambiguous (p q : Nat.Primes) (hpq : p ≠ q) (D E : ℕ+) :
    ∃ v w : MissingWave,
      occupationPhaseLaw v (primeClockTime p D) = occupationPhaseLaw w (primeClockTime p D) ∧
      occupationPhaseLaw v (primeClockTime q E) = occupationPhaseLaw w (primeClockTime q E) ∧
      0 < occupationProbability v 1 ∧ occupationProbability w 1 = 0 ∧
      jointClockLaw v p q D E ≠ jointClockLaw w p q D E := by
  let u := vacuumBlend (lacunaryOmission p)
  let a := primeRayLabel p D.val
  let b := primeRayLabel q E.val
  let v := observationMixture u (insertedWave (a*b) u)
  let w := observationMixture (insertedWave a u) (insertedWave b u)
  have hu : 0 < occupationProbability u 1 := by
    dsimp only [u]
    rw [vacuumBlend_probability,show vacuumMass 1 = 1 by simp [vacuumMass]]
    exact div_pos (add_pos_of_nonneg_of_pos (occupationLaw_nonneg _ 1) zero_lt_one) (by norm_num)
  have hv : 0 < occupationProbability v 1 := by
    change 0 < occupationProbability (observationMixture u (insertedWave (a*b) u)) 1
    rw [mixture_probability]
    exact div_pos (add_pos_of_pos_of_nonneg hu (occupationLaw_nonneg (insertedWave (a*b) u) 1)) (by norm_num)
  have ha : 1 < a.val := Nat.lt_of_lt_of_le p.property.one_lt (Nat.le_self_pow D.ne_zero _)
  have hb : 1 < b.val := Nat.lt_of_lt_of_le q.property.one_lt (Nat.le_self_pow E.ne_zero _)
  have hw : occupationProbability w 1 = 0 := by
    dsimp only [w]
    rw [mixture_probability,insertedWave_probability,insertedWave_probability,
      insertedMass_below a 1 _ ha,insertedMass_below b 1 _ hb]
    simp
  refine ⟨v,w,rectangle_marginal _ u a b (.inl (whole_block_invisible p D)),
    rectangle_marginal _ u a b (.inr (whole_block_invisible q E)),hv,hw,?_⟩
  intro he
  have h := congrFun ((jointClockLaw_identifies_occupations p q hpq D E v w).mp he) 1
  exact hv.ne' (h.trans hw)

/-- Inserting a whole clock block preserves the full phase law while every fixed occupation escapes. -/
theorem moving_clock_alias (p : Nat.Primes) (v : MissingWave) :
    ∃ w : ℕ → MissingWave,
      (∀ j : ℕ, occupationPhaseLaw (w j) (primeClockTime p j.succPNat) =
        occupationPhaseLaw v (primeClockTime p j.succPNat)) ∧
      ∀ n, ∀ᶠ j in atTop, occupationProbability (w j) n = 0 := by
  refine ⟨fun j => insertedWave (resonantBlock p j) v,?_,?_⟩
  · intro j
    simp only [phaseLaw_as_labelReport]
    apply labelReportLaw_ext
    intro s _
    rw [selected_insertion]
    exact selectedMass_congr _ (fun n => by rw [show resonantBlock p j = primeRayLabel p j.succPNat.val from rfl,
      whole_block_invisible])
  · intro n
    filter_upwards [resonantBlock_escapes p n] with j hj
    rw [insertedWave_probability,insertedMass_below _ _ _ hj]

#print axioms selected_insertion
#print axioms whole_block_invisible
#print axioms primeClock_marginals_ambiguous
#print axioms moving_clock_alias

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
