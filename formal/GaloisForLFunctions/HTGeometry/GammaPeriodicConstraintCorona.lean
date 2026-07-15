import GaloisForLFunctions.RHTower.PinnedAffinePrimeJetRigidity
import GaloisForLFunctions.Hurwitz.ExpIndependence
import GaloisForLFunctions.HTGeometry.FormalUnitInverseFreeness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Gamma shift source has a finite-invisible periodic conormal

The homogeneous tangent of the affine digamma shift equation is the space of period-one
functions.  Finite Fourier packets in that tangent realize every prescribed finite jet by a
Vandermonde isomorphism.  Nevertheless, the infinite factorial-tail Taylor functional annihilates
every such packet because translation by one is the identity.

This is the first concrete source model of the finite-observable conormal corona: every finite
clock window is free, while one nonzero infinite-support source constraint survives.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The frequency of the `m`-th period-one Fourier mode. -/
def gammaPeriodicFrequency (m : ℕ) : ℂ :=
  (m : ℂ) * (2 * (Real.pi : ℂ) * I)

/-- The `m`-th entire period-one Fourier mode. -/
def gammaPeriodicMode (m : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (gammaPeriodicFrequency m * z)

@[simp] theorem gammaPeriodicFrequency_exp (m : ℕ) :
    Complex.exp (gammaPeriodicFrequency m) = 1 := by
  simp [gammaPeriodicFrequency]

@[simp] theorem gammaPeriodicMode_add_one (m : ℕ) (z : ℂ) :
    gammaPeriodicMode m (z + 1) = gammaPeriodicMode m z := by
  rw [gammaPeriodicMode, mul_add, mul_one, Complex.exp_add,
    gammaPeriodicFrequency_exp, mul_one]
  rfl

theorem gammaPeriodicMode_periodic (m : ℕ) :
    Function.Periodic (gammaPeriodicMode m) 1 :=
  gammaPeriodicMode_add_one m

theorem iteratedDeriv_gammaPeriodicMode (m n : ℕ) :
    iteratedDeriv n (gammaPeriodicMode m) =
      fun z ↦ gammaPeriodicFrequency m ^ n * gammaPeriodicMode m z := by
  exact HurwitzExp.iteratedDeriv_expLin (gammaPeriodicFrequency m) n

@[simp] theorem iteratedDeriv_gammaPeriodicMode_zero (m n : ℕ) :
    iteratedDeriv n (gammaPeriodicMode m) 0 = gammaPeriodicFrequency m ^ n := by
  rw [iteratedDeriv_gammaPeriodicMode]
  simp [gammaPeriodicMode]

theorem gammaPeriodicFrequency_fin_injective {k : ℕ} :
    Function.Injective (fun i : Fin k ↦ gammaPeriodicFrequency i) := by
  intro i j hij
  apply Fin.ext
  have hcast : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) := by
    apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
    simpa [gammaPeriodicFrequency] using hij
  exact_mod_cast hcast

/-- The first `k` derivatives at zero of a finite period-one Fourier packet. -/
def gammaPeriodicFourierJet {k : ℕ} (a : Fin k → ℂ) (n : Fin k) : ℂ :=
  ∑ m : Fin k, a m * gammaPeriodicFrequency m ^ (n : ℕ)

/-- **Finite-window freedom.**  Every finite clock packet is realized uniquely by a square packet
of periodic Fourier modes. -/
theorem existsUnique_gammaPeriodicFourierJet {k : ℕ} (c : Fin k → ℂ) :
    ∃! a : Fin k → ℂ, ∀ n : Fin k, gammaPeriodicFourierJet a n = c n := by
  simpa [gammaPeriodicFourierJet] using
    RHTower.existsUnique_weightedFiniteMoments
      (fun i : Fin k ↦ gammaPeriodicFrequency i) (fun _ ↦ 1)
      gammaPeriodicFrequency_fin_injective (fun _ ↦ one_ne_zero) c

/-- A finite period-one Fourier polynomial. -/
def gammaPeriodicFourierPolynomial {k : ℕ} (a : Fin k → ℂ) (z : ℂ) : ℂ :=
  ∑ m : Fin k, a m * gammaPeriodicMode m z

theorem gammaPeriodicFourierPolynomial_periodic {k : ℕ} (a : Fin k → ℂ) :
    Function.Periodic (gammaPeriodicFourierPolynomial a) 1 := by
  intro z
  simp [gammaPeriodicFourierPolynomial]

theorem iteratedDeriv_gammaPeriodicFourierPolynomial_zero
    {k : ℕ} (a : Fin k → ℂ) (n : Fin k) :
    iteratedDeriv (n : ℕ) (gammaPeriodicFourierPolynomial a) 0 =
      gammaPeriodicFourierJet a n := by
  change iteratedDeriv (n : ℕ)
    (fun z : ℂ ↦ ∑ m : Fin k, a m * gammaPeriodicMode m z) 0 = _
  rw [HurwitzExp.iteratedDeriv_finset_sum Finset.univ (n : ℕ)]
  · simp [gammaPeriodicFourierJet, iteratedDeriv_const_mul_field,
      iteratedDeriv_gammaPeriodicMode_zero]
  · intro m hm
    exact contDiff_const.mul (HurwitzExp.contDiff_expLin (gammaPeriodicFrequency m))

/-- Every prescribed finite jet is carried by an actual entire period-one Fourier polynomial. -/
theorem existsUnique_gammaPeriodicFourierPolynomial_jet
    {k : ℕ} (c : Fin k → ℂ) :
    ∃! a : Fin k → ℂ,
      Function.Periodic (gammaPeriodicFourierPolynomial a) 1 ∧
        ∀ n : Fin k,
          iteratedDeriv (n : ℕ) (gammaPeriodicFourierPolynomial a) 0 = c n := by
  obtain ⟨a, ha, hua⟩ := existsUnique_gammaPeriodicFourierJet c
  refine ⟨a, ⟨gammaPeriodicFourierPolynomial_periodic a, fun n ↦ ?_⟩, ?_⟩
  · rw [iteratedDeriv_gammaPeriodicFourierPolynomial_zero, ha n]
  · intro b hb
    apply hua
    intro n
    rw [← iteratedDeriv_gammaPeriodicFourierPolynomial_zero]
    exact hb.2 n

/-- The factorial-tail conormal of one period-one Fourier mode has sum zero.  It is the Taylor
form of `e_m(1) - e_m(0) = 0`. -/
theorem gammaPeriodicMode_taylorConormal_hasSum (m : ℕ) :
    HasSum (fun n : ℕ ↦
      gammaPeriodicFrequency m ^ (n + 1) / (n + 1).factorial) 0 := by
  have hexp : NormedSpace.exp (gammaPeriodicFrequency m) = 1 := by
    simpa only [← Complex.exp_eq_exp_ℂ] using gammaPeriodicFrequency_exp m
  simpa [hexp] using (hasSum_nat_add_iff' 1).mpr
    (NormedSpace.expSeries_div_hasSum_exp (gammaPeriodicFrequency m))

/-- **Concrete infinite conormal.**  The same nonzero infinite-support Taylor functional
annihilates every finite periodic Fourier packet, even though those packets realize arbitrary
finite jet data. -/
theorem gammaPeriodicFourier_taylorConormal_hasSum
    {k : ℕ} (a : Fin k → ℂ) :
    HasSum (fun n : ℕ ↦
      ∑ m : Fin k,
        a m * (gammaPeriodicFrequency m ^ (n + 1) / (n + 1).factorial)) 0 := by
  classical
  have hsum : ∀ s : Finset (Fin k),
      HasSum (fun n : ℕ ↦
        ∑ m ∈ s,
          a m * (gammaPeriodicFrequency m ^ (n + 1) / (n + 1).factorial)) 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert m s hm ih =>
        have hmSum := (gammaPeriodicMode_taylorConormal_hasSum m).mul_left (a m)
        simpa [Finset.sum_insert hm] using hmSum.add ih
  simpa using hsum Finset.univ

/-! ### Formal-unit/global-nonunit specialization -/

/-- Positive-degree coefficients of the formal shift cofactor
`(exp D - 1) / D = 1 + D/2! + D^2/3! + ...`. -/
def gammaShiftCofactorCoefficients (n : ℕ) : ℂ :=
  1 / ((n + 2).factorial : ℂ)

/-- The shift cofactor as a formal unit. -/
def gammaShiftCofactorFormal : PowerSeries ℂ :=
  GaloisForLFunctions.unitPowerSeriesOfCoefficients gammaShiftCofactorCoefficients

/-- Its canonical formal inverse. -/
def gammaShiftCofactorFormalInverse : PowerSeries ℂ :=
  GaloisForLFunctions.unitInversePowerSeriesOfCoefficients gammaShiftCofactorCoefficients

@[simp] theorem gammaShiftCofactorFormal_constantCoeff :
    gammaShiftCofactorFormal.constantCoeff = 1 := by
  simp [gammaShiftCofactorFormal]

theorem gammaShiftCofactorFormal_mul_inverse :
    gammaShiftCofactorFormal * gammaShiftCofactorFormalInverse = 1 := by
  exact GaloisForLFunctions.unitPowerSeries_mul_unitInverse gammaShiftCofactorCoefficients

theorem gammaShiftCofactorFormal_inverse_mul :
    gammaShiftCofactorFormalInverse * gammaShiftCofactorFormal = 1 := by
  exact GaloisForLFunctions.unitInverse_mul_unitPowerSeries gammaShiftCofactorCoefficients

/-- The global analytic symbol of the shift cofactor away from its removable origin. -/
def gammaShiftCofactorSymbol (z : ℂ) : ℂ :=
  (Complex.exp z - 1) / z

@[simp] theorem gammaShiftCofactorSymbol_periodicFrequency (m : ℕ) :
    gammaShiftCofactorSymbol (gammaPeriodicFrequency m) = 0 := by
  simp [gammaShiftCofactorSymbol]

theorem gammaPeriodicFrequency_ne_zero {m : ℕ} (hm : m ≠ 0) :
    gammaPeriodicFrequency m ≠ 0 := by
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hm) Complex.two_pi_I_ne_zero

/-- Reflection preserves the global nonunit divisor up to the nowhere-zero exponential unit. -/
theorem gammaShiftCofactorSymbol_neg {z : ℂ} (hz : z ≠ 0) :
    gammaShiftCofactorSymbol (-z) =
      Complex.exp (-z) * gammaShiftCofactorSymbol z := by
  rw [gammaShiftCofactorSymbol, gammaShiftCofactorSymbol]
  rw [Complex.exp_neg]
  field_simp [hz, Complex.exp_ne_zero]
  ring

end


end GaloisForLFunctions.HTGeometry
