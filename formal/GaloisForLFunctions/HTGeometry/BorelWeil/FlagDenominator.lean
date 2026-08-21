import GaloisForLFunctions.HTGeometry.BorelWeil.CellCoprime
import GaloisForLFunctions.HTGeometry.BorelWeil.CellSections
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Denominators of sections regular on every Bruhat cell

An element of the localization that is regular on every Bruhat cell has, after clearing
denominators, a denominator all of whose prime factors divide the determinant: this is the previous
file's statement that a prime missing `det` misses some cell equation, combined with the fact that
the polynomial ring is a unique factorization domain, so that the set of admissible denominators of
a fixed element is an ideal from which primes can be stripped one at a time.

Consequently a power of the determinant already clears the denominator, which is the algebraic form
of the statement that the Bruhat cells cover `GL`.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.denomIdeal` — the admissible denominators of an element.

## Main results

* `mem_denomIdeal_of_prime_mul` — a prime missing one admissible denominator can be stripped.
* `exists_detPow_mem_denomIdeal` — a power of `det` clears the denominator of any element regular on
  every cell.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

instance instIsDomainFlagLoc : IsDomain (FlagLoc N k) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (totalDenom N k)) _
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero totalDenom_ne_zero))

/-- The admissible denominators of an element of the localization: the polynomials that clear it. -/
noncomputable def denomIdeal (x : FlagLoc N k) : Ideal (MvPolynomial (Fin N × Fin N) k) where
  carrier := {r | ∃ q : MvPolynomial (Fin N × Fin N) k,
    x * algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) r = algebraMap _ _ q}
  add_mem' := by
    rintro r s ⟨q, hq⟩ ⟨q', hq'⟩
    exact ⟨q + q', by rw [map_add, mul_add, hq, hq', map_add]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c r ⟨q, hq⟩
    refine ⟨c * q, ?_⟩
    rw [smul_eq_mul, map_mul, ← mul_assoc, mul_comm x, mul_assoc, hq, map_mul]

theorem mem_denomIdeal_iff {x : FlagLoc N k} {r : MvPolynomial (Fin N × Fin N) k} :
    r ∈ denomIdeal x ↔ ∃ q : MvPolynomial (Fin N × Fin N) k,
      x * algebraMap _ (FlagLoc N k) r = algebraMap _ _ q := Iff.rfl

theorem algebraMap_flagLoc_inj :
    Function.Injective (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)) := by
  refine IsLocalization.injective (M := Submonoid.powers (totalDenom N k)) (FlagLoc N k) ?_
  intro y hy
  obtain ⟨n, rfl⟩ := hy
  exact pow_mem (mem_nonZeroDivisors_of_ne_zero totalDenom_ne_zero) n

/-- **Stripping a prime from a denominator.**  If `π * c` clears `x` and some `d` prime to `π`
clears `x`, then `c` already clears `x`. -/
theorem mem_denomIdeal_of_prime_mul {x : FlagLoc N k} {π c d : MvPolynomial (Fin N × Fin N) k}
    (hπ : Prime π) (hc : π * c ∈ denomIdeal x) (hd : d ∈ denomIdeal x) (hnd : ¬ π ∣ d) :
    c ∈ denomIdeal x := by
  obtain ⟨a, ha⟩ := hc
  obtain ⟨p, hp⟩ := hd
  have hmul : algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (a * d)
      = algebraMap _ _ (π * (c * p)) := by
    have h1 : algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (a * d)
        = algebraMap _ _ (π * c) * (x * algebraMap _ _ d) := by
      rw [map_mul, ← ha]; ring
    rw [h1, hp, map_mul, map_mul, map_mul]
    ring
  have hdvd : π ∣ a * d := ⟨c * p, algebraMap_flagLoc_inj hmul⟩
  obtain ⟨a', rfl⟩ : π ∣ a := (hπ.dvd_or_dvd hdvd).resolve_right hnd
  refine ⟨a', ?_⟩
  have hπ0 : algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) π ≠ 0 := by
    intro h
    exact hπ.ne_zero (algebraMap_flagLoc_inj (by rw [h, map_zero]))
  refine mul_left_cancel₀ hπ0 ?_
  rw [← map_mul]
  calc algebraMap _ (FlagLoc N k) π * (x * algebraMap _ _ c)
      = x * algebraMap _ _ (π * c) := by rw [map_mul]; ring
    _ = algebraMap _ _ (π * a') := ha

/-- A denominator can be replaced by one whose prime factors all divide the determinant. -/
theorem exists_mem_denomIdeal_primes_dvd {x : FlagLoc N k}
    (hcell : ∀ σ : Equiv.Perm (Fin N), ∃ m : ℕ, cellDenomPoly N k σ ^ m ∈ denomIdeal x)
    {c : MvPolynomial (Fin N × Fin N) k} (hc0 : c ≠ 0) (hc : c ∈ denomIdeal x) :
    ∃ c' : MvPolynomial (Fin N × Fin N) k, c' ≠ 0 ∧ c' ∈ denomIdeal x ∧
      ∀ π, Prime π → π ∣ c' → π ∣ detPoly N k := by
  classical
  have key : ∀ b : MvPolynomial (Fin N × Fin N) k, ∀ e : MvPolynomial (Fin N × Fin N) k,
      b * e ≠ 0 → b * e ∈ denomIdeal x → (∀ π, Prime π → π ∣ e → π ∣ detPoly N k) →
      ∃ c' : MvPolynomial (Fin N × Fin N) k, c' ≠ 0 ∧ c' ∈ denomIdeal x ∧
        ∀ π, Prime π → π ∣ c' → π ∣ detPoly N k := by
    intro b
    refine UniqueFactorizationMonoid.induction_on_prime
      (P := fun b : MvPolynomial (Fin N × Fin N) k => ∀ e : MvPolynomial (Fin N × Fin N) k,
        b * e ≠ 0 → b * e ∈ denomIdeal x → (∀ π, Prime π → π ∣ e → π ∣ detPoly N k) →
        ∃ c' : MvPolynomial (Fin N × Fin N) k, c' ≠ 0 ∧ c' ∈ denomIdeal x ∧
          ∀ π, Prime π → π ∣ c' → π ∣ detPoly N k) b ?_ ?_ ?_
    · intro e h0 _ _
      exact absurd (zero_mul e) h0
    · intro u hu e h0 hmem hprim
      refine ⟨u * e, h0, hmem, fun π hπ hdvd => ?_⟩
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      refine hprim π hπ ?_
      have he : e = u * e * v := by rw [mul_comm u e, mul_assoc, hv, mul_one]
      rw [he]
      exact hdvd.mul_right v
    · intro a π ha hπ IH e h0 hmem hprim
      by_cases hd : π ∣ detPoly N k
      · refine IH (π * e) ?_ ?_ ?_
        · intro h; exact h0 (by rw [← h]; ring)
        · have : a * (π * e) = π * a * e := by ring
          rw [this]; exact hmem
        · intro q hq hqdvd
          rcases hq.dvd_or_dvd hqdvd with h | h
          · exact h.trans hd
          · exact hprim q hq h
      · obtain ⟨σ, hσ⟩ := exists_cellDenom_not_dvd hπ hd
        obtain ⟨m, hm⟩ := hcell σ
        have hnd : ¬ π ∣ cellDenomPoly N k σ ^ m := fun h => hσ (hπ.dvd_of_dvd_pow h)
        have hmem' : π * (a * e) ∈ denomIdeal x := by
          have : π * (a * e) = π * a * e := by ring
          rw [this]; exact hmem
        refine IH e ?_ (mem_denomIdeal_of_prime_mul hπ hmem' hm hnd) hprim
        intro h; exact h0 (by rw [mul_assoc, h, mul_zero])
  refine key c 1 ?_ ?_ ?_
  · rwa [mul_one]
  · rwa [mul_one]
  · intro π hπ h1
    exact absurd (isUnit_of_dvd_one h1) hπ.not_unit

/-- An element all of whose prime factors divide `d` divides a power of `d`. -/
theorem dvd_pow_of_primes_dvd {c d : MvPolynomial (Fin N × Fin N) k} (hc0 : c ≠ 0)
    (h : ∀ π, Prime π → π ∣ c → π ∣ d) : ∃ M : ℕ, c ∣ d ^ M := by
  classical
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun c : MvPolynomial (Fin N × Fin N) k => c ≠ 0 →
      (∀ π, Prime π → π ∣ c → π ∣ d) → ∃ M : ℕ, c ∣ d ^ M) c ?_ ?_ ?_ hc0 h
  · intro h0; exact absurd rfl h0
  · intro u hu _ _
    exact ⟨0, by rw [pow_zero]; exact hu.dvd⟩
  · intro a π ha hπ IH _ hprim
    obtain ⟨M, hM⟩ := IH ha fun q hq hqa => hprim q hq (hqa.mul_left π)
    refine ⟨M + 1, ?_⟩
    rw [pow_succ, mul_comm (d ^ M) d]
    exact mul_dvd_mul (hprim π hπ ⟨a, rfl⟩) hM

/-- **A power of the determinant clears the denominator of anything regular on every cell.** -/
theorem exists_detPow_mem_denomIdeal {x : FlagLoc N k}
    (hcell : ∀ σ : Equiv.Perm (Fin N), ∃ m : ℕ, cellDenomPoly N k σ ^ m ∈ denomIdeal x) :
    ∃ M : ℕ, detPoly N k ^ M ∈ denomIdeal x := by
  classical
  obtain ⟨m, hm⟩ := hcell 1
  obtain ⟨c', hc'0, hc'mem, hc'prim⟩ :=
    exists_mem_denomIdeal_primes_dvd hcell (pow_ne_zero m (cellDenomPoly_ne_zero 1)) hm
  obtain ⟨M, t, ht⟩ := dvd_pow_of_primes_dvd hc'0 hc'prim
  exact ⟨M, by rw [ht]; exact Ideal.mul_mem_right _ _ hc'mem⟩

end GaloisForLFunctions.HTGeometry.BorelWeil
