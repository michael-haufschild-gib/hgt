import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Splitting along a coprime monic pair

If `A` is monic and coprime to `B`, every polynomial is uniquely `dA * B + A * dB` with
`deg dA < deg A`; and if its degree is below `deg A + deg B`, then also `deg dB < deg B`.  This is
the polynomial partial-fraction decomposition, and it holds over an arbitrary commutative ring — no
field, no dimension count, no flatness.

For the critical fibre of a horizon this is the exact solvability of one linearised step: the
displacement `(dA, dB)` producing a prescribed inversion error over the horizon exists and is unique.
Because the statement is ring-level it survives base change to any deformation of the coefficients,
which is what lifting a fibre point along a deformation of the observation needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R : Type*} [CommRing R]

/-- **A multiple of a monic polynomial of smaller degree vanishes.** -/
theorem eq_zero_of_monic_dvd_of_natDegree_lt {A P : R[X]} (hA : A.Monic)
    (hdvd : A ∣ P) (hdeg : P.natDegree < A.natDegree) : P = 0 := by
  obtain ⟨h, rfl⟩ := hdvd
  rcases eq_or_ne h 0 with rfl | hh
  · rw [mul_zero]
  · exfalso
    have hlead : h.leadingCoeff * A.leadingCoeff ≠ 0 := by
      rw [hA.leadingCoeff, mul_one]
      exact Polynomial.leadingCoeff_ne_zero.2 hh
    have hmul : (h * A).natDegree = h.natDegree + A.natDegree :=
      Polynomial.natDegree_mul' hlead
    rw [mul_comm, hmul] at hdeg
    omega

/-- **Existence of the split.**  Divide by the monic factor after clearing a Bézout identity. -/
theorem exists_coprimeSplit [Nontrivial R] {A B : R[X]} (hA : A.Monic) (hcop : IsCoprime A B)
    (E : R[X]) :
    ∃ dA dB : R[X], dA.degree < A.degree ∧ dA * B + A * dB = E := by
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨r, q, hrdeg, hrq⟩ : ∃ r q : R[X], r.degree < A.degree ∧ r + A * q = E * v :=
    ⟨(E * v) %ₘ A, (E * v) /ₘ A, degree_modByMonic_lt _ hA, modByMonic_add_div (E * v) A⟩
  refine ⟨r, E * u + q * B, hrdeg, ?_⟩
  calc r * B + A * (E * u + q * B) = (r + A * q) * B + A * (E * u) := by ring
    _ = (E * v) * B + A * (E * u) := by rw [hrq]
    _ = E * (u * A + v * B) := by ring
    _ = E := by rw [huv, mul_one]

/-- The split in the degree bookkeeping used below the horizon. -/
theorem exists_coprimeSplit_natDegree [Nontrivial R] {m : ℕ} {A B : R[X]} (hA : A.Monic)
    (hAdeg : A.natDegree = m) (hm : 0 < m) (hcop : IsCoprime A B) (E : R[X]) :
    ∃ dA dB : R[X], dA.natDegree < m ∧ dA * B + A * dB = E := by
  obtain ⟨dA, dB, hdeg, heq⟩ := exists_coprimeSplit hA hcop E
  refine ⟨dA, dB, ?_, heq⟩
  rcases eq_or_ne dA 0 with rfl | h0
  · rw [Polynomial.natDegree_zero]
    omega
  · rw [← hAdeg]
    exact Polynomial.natDegree_lt_natDegree h0 hdeg

/-- **The second component of a split is small too**, once the target is below the total degree. -/
theorem natDegree_snd_lt_of_coprimeSplit {m n : ℕ} {A B dA dB E : R[X]} (hA : A.Monic)
    (hAdeg : A.natDegree = m) (hBdeg : B.natDegree ≤ n) (hn : 0 < n)
    (hdA : dA.natDegree < m) (hE : E.natDegree < m + n)
    (heq : dA * B + A * dB = E) : dB.natDegree < n := by
  rcases eq_or_ne dB 0 with rfl | hdB
  · rw [Polynomial.natDegree_zero]
    omega
  have hlead : dB.leadingCoeff * A.leadingCoeff ≠ 0 := by
    rw [hA.leadingCoeff, mul_one]
    exact Polynomial.leadingCoeff_ne_zero.2 hdB
  have hprod : (A * dB).natDegree = dB.natDegree + m := by
    rw [mul_comm, Polynomial.natDegree_mul' hlead, hAdeg]
  have hsub : A * dB = E - dA * B := by linear_combination heq
  have hle1 : (dA * B).natDegree < m + n :=
    lt_of_le_of_lt (Polynomial.natDegree_mul_le) (by omega)
  have hlt : (A * dB).natDegree < m + n := by
    rw [hsub]
    exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hE hle1)
  omega

/-- **Uniqueness of the split.** -/
theorem coprimeSplit_unique {A B dA dB dA' dB' : R[X]} (hA : A.Monic) (hcop : IsCoprime A B)
    (h1 : dA.natDegree < A.natDegree) (h2 : dA'.natDegree < A.natDegree)
    (heq : dA * B + A * dB = dA' * B + A * dB') : dA = dA' ∧ dB = dB' := by
  have hdiff : (dA - dA') * B = A * (dB' - dB) := by linear_combination heq
  have hAdA : A ∣ (dA - dA') := hcop.dvd_of_dvd_mul_right ⟨dB' - dB, hdiff⟩
  have hzero : dA - dA' = 0 :=
    eq_zero_of_monic_dvd_of_natDegree_lt hA hAdA
      (lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt h1 h2))
  refine ⟨sub_eq_zero.1 hzero, ?_⟩
  rw [hzero, zero_mul] at hdiff
  exact (sub_eq_zero.1 (hA.mul_right_eq_zero_iff.1 hdiff.symm)).symm

/-- **The linearised fibre step has a unique solution, over any ring.**  For a monic `A` of degree
`m` coprime to `B` of degree at most `n`, every inversion error of degree below `m + n` is the image
of exactly one displacement pair with degrees below `m` and `n`. -/
theorem existsUnique_coprimeSplit [Nontrivial R] {m n : ℕ} {A B : R[X]} (hA : A.Monic)
    (hAdeg : A.natDegree = m) (hBdeg : B.natDegree ≤ n) (hm : 0 < m) (hn : 0 < n)
    (hcop : IsCoprime A B) {E : R[X]} (hE : E.natDegree < m + n) :
    ∃! p : R[X] × R[X], p.1.natDegree < m ∧ p.2.natDegree < n ∧ p.1 * B + A * p.2 = E := by
  obtain ⟨dA, dB, hdA, heq⟩ := exists_coprimeSplit_natDegree hA hAdeg hm hcop E
  refine ⟨⟨dA, dB⟩, ⟨hdA, natDegree_snd_lt_of_coprimeSplit hA hAdeg hBdeg hn hdA hE heq, heq⟩, ?_⟩
  rintro ⟨dA', dB'⟩ ⟨hdA', _, heq'⟩
  obtain ⟨e1, e2⟩ := coprimeSplit_unique hA hcop (by rw [hAdeg]; exact hdA')
    (by rw [hAdeg]; exact hdA) (heq'.trans heq.symm)
  exact Prod.ext e1 e2

end GaloisForLFunctions.HTGeometry
