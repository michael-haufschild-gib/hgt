import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.ClockAliases
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Selections

/-! # Occupation tomography and the finite clock cutoff -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology MeasureTheory
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Measured mass of the phase containing the target label. -/
def clockAtom (v : MissingWave) (p : Nat.Primes) (D a : ℕ+) : ℝ :=
  ((occupationPhaseLaw v (primeClockTime p D) : Measure Circle) {occupationPhase (primeClockTime p D) a}).toReal

theorem clockAtom_eq (v : MissingWave) (p : Nat.Primes) (D a : ℕ+) :
    clockAtom v p D a = selectedMass (occupationProbability v) (fun n =>
      occupationPhase (primeClockTime p D) n = occupationPhase (primeClockTime p D) a) := by
  rw [clockAtom,phaseLaw_as_labelReport,labelReportLaw_atom]

theorem selectedMass_single {ι : Type*} (w : ι → ℝ) (a : ι) :
    selectedMass w (fun n => n = a) = w a := tsum_ite_eq a w

private theorem selectedMass_mono {ι : Type*} {w : ι → ℝ} (hw : ∀ e, 0 ≤ w e) (hs : Summable w)
    {P Q : ι → Prop} (h : ∀ n, P n → Q n) : selectedMass w P ≤ selectedMass w Q := by
  apply (selected_summable hs P).tsum_le_tsum _ (selected_summable hs Q)
  intro n
  by_cases hp : P n
  · simp only [hp,h n hp,if_true,le_refl]
  · by_cases hq : Q n <;> simp [hp,hq,hw]

/-- The whole alias error below the cutoff is bounded by the probability at and above it. -/
theorem clockAtom_error (v : MissingWave) (p : Nat.Primes) (D a : ℕ+) (ha : a.val < p.val^D.val) :
    0 ≤ clockAtom v p D a - occupationProbability v a ∧
    clockAtom v p D a - occupationProbability v a ≤
      selectedMass (occupationProbability v) (fun n => p.val^D.val ≤ n.val) := by
  let w := occupationProbability v
  let F (n : ℕ+) := occupationPhase (primeClockTime p D) n = occupationPhase (primeClockTime p D) a
  let T (n : ℕ+) := p.val^D.val ≤ n.val
  have hw := occupationLaw_nonneg v
  have hs := (occupationLaw_hasSum v).summable
  rw [clockAtom_eq]
  change 0 ≤ selectedMass w F - w a ∧ selectedMass w F - w a ≤ selectedMass w T
  constructor
  · apply sub_nonneg.mpr
    rw [← selectedMass_single w a]
    exact selectedMass_mono hw hs (fun n (h : n = a) => by subst n; rfl)
  · apply sub_le_iff_le_add'.mpr
    rw [← selectedMass_single w a]
    unfold selectedMass
    rw [← (selected_summable hs _).tsum_add (selected_summable hs _)]
    apply (selected_summable hs F).tsum_le_tsum _
      ((selected_summable hs _).add (selected_summable hs _))
    intro n
    by_cases hn : n = a
    · subst n
      simp [F,T,ha.not_ge]
    · by_cases ht : T n
      · by_cases hf : F n <;> simp [hf,ht,hn,hw]
      · have hf : ¬ F n := fun he => hn ((primeClock_separates_below p D n a (lt_of_not_ge ht) ha).mp he)
        simp [hn,ht,hf]

/-- Phase fibers recover every coordinate of any finite nonnegative occupation law. -/
theorem primeClock_fiber_limit {w : ℕ+ → ℝ} (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (p : Nat.Primes) (a : ℕ+) :
    Tendsto (fun j : ℕ => selectedMass w (fun n => occupationPhase (primeClockTime p j.succPNat) n =
      occupationPhase (primeClockTime p j.succPNat) a)) atTop (𝓝 (w a)) := by
  apply selectedMass_limit_singleton hw hs
  intro n
  filter_upwards [resonantBlock_escapes p n,resonantBlock_escapes p a] with j hn ha
  exact primeClock_separates_below p j.succPNat n a hn ha

/-- Any fixed Born probability is the limit of single moving phase atoms at one prime. -/
theorem clockAtom_limit (v : MissingWave) (p : Nat.Primes) (a : ℕ+) :
    Tendsto (fun j : ℕ => clockAtom v p j.succPNat a) atTop (𝓝 (occupationProbability v a)) := by
  simp_rw [clockAtom_eq]
  exact primeClock_fiber_limit (occupationLaw_nonneg v) (occupationLaw_hasSum v).summable p a

/-- Vanishing probability above the clock cutoff suffices for accurate readings even when the
preparation and the target vary together. -/
theorem moving_clock_error_limit (p : Nat.Primes) (v : ℕ → MissingWave) (a : ℕ → ℕ+)
    (ha : ∀ᶠ j : ℕ in atTop, (a j).val < p.val^(j+1))
    (ht : Tendsto (fun j => selectedMass (occupationProbability (v j)) (fun n => p.val^(j+1) ≤ n.val))
      atTop (𝓝 0)) :
    Tendsto (fun j : ℕ => clockAtom (v j) p j.succPNat (a j) - occupationProbability (v j) (a j)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · filter_upwards [ha] with j hj
    exact (clockAtom_error (v j) p j.succPNat (a j) hj).1
  · filter_upwards [ha] with j hj
    exact (clockAtom_error (v j) p j.succPNat (a j) hj).2

theorem labelReportLaw_ext {X : Type*} [MeasurableSpace X] {v w : MissingWave} (Z : ℕ+ → X)
    (he : ∀ s : Set X, MeasurableSet s → selectedMass (occupationProbability v) (fun n => Z n ∈ s) =
      selectedMass (occupationProbability w) (fun n => Z n ∈ s)) : labelReportLaw v Z = labelReportLaw w Z := by
  apply Subtype.ext
  change (labelReportLaw v Z : Measure X) = (labelReportLaw w Z : Measure X)
  apply Measure.ext
  intro s hs
  exact (labelReportLaw_apply v Z hs).trans ((congrArg ENNReal.ofReal (he s hs)).trans (labelReportLaw_apply w Z hs).symm)

theorem labelReportLaw_congr {X : Type*} [MeasurableSpace X] {v w : MissingWave}
    (h : occupationProbability v = occupationProbability w) (Z : ℕ+ → X) :
    labelReportLaw v Z = labelReportLaw w Z := by
  apply labelReportLaw_ext
  intro s _
  rw [h]

theorem primeClock_identifies_occupations (p : Nat.Primes) (v w : MissingWave) :
    (∀ D, occupationPhaseLaw v (primeClockTime p D) = occupationPhaseLaw w (primeClockTime p D)) ↔
      occupationProbability v = occupationProbability w := by
  constructor
  · intro h
    funext a
    have he : ∀ j : ℕ, clockAtom v p j.succPNat a = clockAtom w p j.succPNat a := fun j => by
      rw [clockAtom,clockAtom,h]
    exact tendsto_nhds_unique ((funext he) ▸ clockAtom_limit v p a) (clockAtom_limit w p a)
  · intro h D
    exact labelReportLaw_congr h _

#print axioms clockAtom_eq
#print axioms selectedMass_single
#print axioms clockAtom_error
#print axioms primeClock_fiber_limit
#print axioms clockAtom_limit
#print axioms moving_clock_error_limit
#print axioms labelReportLaw_ext
#print axioms labelReportLaw_congr
#print axioms primeClock_identifies_occupations

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
