import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Occupations
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Thermal

/-! # Lifting paired prime-energy inequalities to peak probabilities at fixed particle number -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak

open Finset Real
open scoped ComplexConjugate

theorem read_neg_fun {I : Type*} [Fintype I] {m : ℕ} (e : I → ℝ) :
    (read (fun j => -e j) : Boson I m → ℝ) = fun x => -read e x := by
  funext x
  simp [read]

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem boson_peak_above {m : ℕ} (hm : 0 < m) (e : I → ℝ) (l u : I)
    (hl : ∀ i, e l ≤ e i) (hu : ∀ i, e i ≤ e u) (R : Equiv.Perm I)
    (hall : ∀ i, e l + e u ≤ e i + e (R i)) (hstrict : ∃ i, e l + e u < e i + e (R i))
    {t : ℝ} (ht : 0 < t) :
    largest (read e : Boson I m → ℝ) (-t) < largest (read e : Boson I m → ℝ) t := by
  refine strict_peak_above ht (pure m l) (pure m u) ?_ ?_ (move m R) ?_ ?_
  · intro x
    rw [read_pure, ← read_const x]
    exact read_mono x hl
  · intro x
    rw [read_pure, ← read_const x]
    exact read_mono x hu
  · intro x
    rw [read_pure, read_pure, ← mul_add, ← read_const x, read_move, ← read_add]
    exact read_mono x hall
  · obtain ⟨i, hi⟩ := hstrict
    refine ⟨pure m i, ?_⟩
    simp only [read_move, read_pure, ← mul_add]
    exact mul_lt_mul_of_pos_left hi (Nat.cast_pos.mpr hm)

theorem boson_peak_below {m : ℕ} (hm : 0 < m) (e : I → ℝ) (l u : I)
    (hl : ∀ i, e l ≤ e i) (hu : ∀ i, e i ≤ e u) (R : Equiv.Perm I)
    (hall : ∀ i, e i + e (R i) ≤ e l + e u) (hstrict : ∃ i, e i + e (R i) < e l + e u)
    {t : ℝ} (ht : 0 < t) :
    largest (read e : Boson I m → ℝ) t < largest (read e : Boson I m → ℝ) (-t) := by
  obtain ⟨i, hi⟩ := hstrict
  have hh := boson_peak_above hm (fun j => -e j) u l (fun j => neg_le_neg (hu j))
    (fun j => neg_le_neg (hl j)) R (fun j => by linarith only [hall j]) ⟨i, by linarith only [hi]⟩ ht
  rw [read_neg_fun] at hh
  simpa only [largest_neg_energy, neg_neg] using hh

/-- Largest conserved-label probability measured after splitting the equal-amplitude input. -/
def measured (S : Finset Nat.Primes) (m : ℕ) (s : ℂ) :=
  sSup (Set.range (fun x : Boson S m => outgoingShare s x))

theorem measured_eq (S : Finset Nat.Primes) (m : ℕ) (s : ℂ) :
    measured S m s = largest (read primeEnergy : Boson S m → ℝ) (2*s.re-1) := by
  apply congrArg (fun f : Boson S m → ℝ => sSup (Set.range f))
  funext x
  rw [outgoing_gibbs]
  simp_rw [energy_eq_read]

theorem measured_reflection_iff {S : Finset Nat.Primes} {m : ℕ}
    (hne : ∀ t : ℝ, 0 < t →
      largest (read primeEnergy : Boson S m → ℝ) t ≠ largest (read primeEnergy : Boson S m → ℝ) (-t))
    (s : ℂ) : measured S m s = measured S m (1-conj s) ↔ s.re = 1/2 := by
  rw [measured_eq, measured_eq]
  have flip : 2*(1-conj s).re-1 = -(2*s.re-1) := by rw [Complex.sub_re, Complex.one_re, Complex.conj_re]; ring
  rw [flip]
  constructor
  · intro he
    rcases lt_trichotomy (2*s.re-1) 0 with h | h | h
    · have ne := hne _ (neg_pos.mpr h)
      rw [neg_neg] at ne
      exact (ne he.symm).elim
    · linarith only [h]
    · exact (hne _ h he).elim
  · intro h
    rw [show 2*s.re-1 = 0 by linarith only [h], neg_zero]

#print axioms boson_peak_above
#print axioms boson_peak_below
#print axioms measured_eq

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak
