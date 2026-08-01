import GaloisForLFunctions.RHTower.MobiusAdditiveCircleBoundary
import GaloisForLFunctions.RHTower.Mollifier

/-!
# Exact finite diagonalization of the Möbius dilation family

Expanding a finite linear combination of the damped Möbius dilates at additive-circle
frequencies produces a divisor--Möbius incidence coefficient at every frequency.  Parseval then
diagonalizes the full quadratic form exactly.  This is the finite, unconditional algebraic core
of the all-scale identity `(G32b)` on the Route E research card.

The constant incidence vector is sent to the first pure tone by Möbius inversion.  Thus the
positive Gram geometry has no unaccounted boundary mode; any further point-evaluation estimate
must control the signed incidence coefficients themselves.
-/

open Complex
open scoped BigOperators Polynomial

namespace RHTower

noncomputable section

private theorem sum_filter_identity_eq_dilation
    {α R : Type*} [DecidableEq α] [AddCommMonoid R]
    (s : Finset α) (w : α → R) {a : α} (ha : a ∈ s) :
    ∑ i ∈ s.filter (fun i => i = a), w i = w a := by
  have hfilter : s.filter (fun i => i = a) = {a} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun hi => hi.2
    · intro hi
      subst i
      exact ⟨ha, rfl⟩
  rw [hfilter]
  simp

/-- Divisor--Möbius incidence coefficient created by a dilation coefficient vector `c`.
At frequency `m`, the divisor `d` represents the Möbius frequency inside dilation `m / d`. -/
def mobiusDilationIncidenceCoefficient (c : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ d ∈ m.divisors,
    c (m / d) * ((ArithmeticFunction.moebius d : ℤ) : ℂ)

/-- Möbius inversion sends the constant dilation vector to the unit frequency. -/
theorem mobiusDilationIncidenceCoefficient_one (m : ℕ) :
    mobiusDilationIncidenceCoefficient (fun _ => (1 : ℂ)) m =
      if m = 1 then 1 else 0 := by
  rw [mobiusDilationIncidenceCoefficient]
  simp only [one_mul]
  exact_mod_cast sum_moebius_divisors m

/-- Exponentially damped incidence coefficient at additive frequency `m`. -/
def dampedMobiusDilationIncidenceCoefficient
    (x : ℝ) (c : ℕ → ℂ) (m : ℕ) : ℂ :=
  mobiusDilationIncidenceCoefficient c m *
    Complex.exp (-((m : ℝ) * x : ℝ))

/-- Finite additive-circle polynomial carrying every Möbius dilation resonance through
frequency `M`. -/
def finiteMobiusDilationIncidencePolynomial
    (M : ℕ) (x : ℝ) (c : ℕ → ℂ) : ℂ[X] :=
  finiteFrequencyPolynomial (Finset.Icc 1 M) id
    (dampedMobiusDilationIncidenceCoefficient x c)

/-- Exact finite Parseval diagonalization of the full divisor--Möbius incidence form. -/
theorem circleAverage_finiteMobiusDilationIncidencePolynomial_norm_sq
    (M : ℕ) (x : ℝ) (c : ℕ → ℂ) :
    Real.circleAverage
        (fun z => ‖(finiteMobiusDilationIncidencePolynomial M x c).eval z‖ ^ (2 : ℕ))
        0 1 =
      ∑ m ∈ Finset.Icc 1 M,
        ‖dampedMobiusDilationIncidenceCoefficient x c m‖ ^ (2 : ℕ) := by
  classical
  rw [finiteMobiusDilationIncidencePolynomial]
  have hparse := circleAverage_finiteFrequencyPolynomial_norm_sq
    (Finset.Icc 1 M) id (dampedMobiusDilationIncidenceCoefficient x c)
  rw [Finset.image_id] at hparse
  rw [hparse]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [id_eq]
  rw [sum_filter_identity_eq_dilation (Finset.Icc 1 M)
    (dampedMobiusDilationIncidenceCoefficient x c) hm]

/-- For the constant dilation vector, every finite frequency window containing `1` collapses
coefficientwise to the damped first pure tone. -/
theorem dampedMobiusDilationIncidenceCoefficient_one
    (x : ℝ) (m : ℕ) :
    dampedMobiusDilationIncidenceCoefficient x (fun _ => (1 : ℂ)) m =
      if m = 1 then Complex.exp (-x) else 0 := by
  rw [dampedMobiusDilationIncidenceCoefficient,
    mobiusDilationIncidenceCoefficient_one]
  split_ifs with hm
  · subst m
    simp
  · simp

end

end RHTower
