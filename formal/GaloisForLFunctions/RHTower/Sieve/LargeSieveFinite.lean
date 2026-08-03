import GaloisForLFunctions.RHTower.Sieve.LargeSieveGallagher

/-!
# The sharp large sieve for finitely many points

`largeSieve_gallagher` asks for a sequence whose *every* consecutive gap is at least `δ`, but an
application supplies only finitely many points.  Continuing the sequence arithmetically past the
last point preserves the gap hypothesis and changes nothing below it, so the finite statement
follows:

`∑_{r ≤ R} |S(λ_r)|² ≤ (δ^{-1} + 4πN) ∑_{n < N} |c_n|²`

now requires the gap only between consecutive points that are actually used.
-/

namespace RHTower.Sieve

open Finset

/-- A finite family of points, continued arithmetically past the last one. -/
noncomputable def extendSeq (lam : ℕ → ℝ) (R : ℕ) (δ : ℝ) : ℕ → ℝ :=
  fun i => if i ≤ R then lam i else lam R + ((i - R : ℕ) : ℝ) * δ

theorem extendSeq_of_le {lam : ℕ → ℝ} {R : ℕ} {δ : ℝ} {i : ℕ} (hi : i ≤ R) :
    extendSeq lam R δ i = lam i := by
  rw [extendSeq, if_pos hi]

/-- The continuation keeps the gap at every step. -/
theorem gap_extendSeq {lam : ℕ → ℝ} {δ : ℝ} {R : ℕ}
    (hgap : ∀ i, i < R → lam i + δ ≤ lam (i + 1)) :
    ∀ i, extendSeq lam R δ i + δ ≤ extendSeq lam R δ (i + 1) := by
  intro i
  rcases le_or_gt (i + 1) R with hle | hgt
  · rw [extendSeq_of_le (by omega), extendSeq_of_le hle]
    exact hgap i (by omega)
  · rcases le_or_gt i R with hiR | hiR
    · have hiEq : i = R := by omega
      subst hiEq
      rw [extendSeq_of_le le_rfl, extendSeq, if_neg (by omega)]
      have hone : ((i + 1 - i : ℕ) : ℝ) = 1 := by
        have : (i + 1 - i : ℕ) = 1 := by omega
        rw [this]
        norm_num
      rw [hone]
      linarith
    · rw [extendSeq, if_neg (by omega), extendSeq, if_neg (by omega)]
      have hstep : ((i + 1 - R : ℕ) : ℝ) = ((i - R : ℕ) : ℝ) + 1 := by
        have hnat : (i + 1 - R : ℕ) = (i - R) + 1 := by omega
        rw [hnat]
        push_cast
        ring
      rw [hstep]
      ring_nf
      linarith

/-- **The sharp large sieve for finitely many separated points.** -/
theorem largeSieve_gallagher_finite (N : ℕ) (hN : 0 < N) (c : Fin N → ℂ) {lam : ℕ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (R : ℕ) (hgap : ∀ i, i < R → lam i + δ ≤ lam (i + 1))
    (hlow : δ / 2 ≤ lam 0) (hhigh : lam R + δ / 2 ≤ 1) :
    ∑ r ∈ Finset.range (R + 1), ‖expSum N c (lam r)‖ ^ 2
      ≤ (1 / δ + 4 * Real.pi * (N : ℝ)) * ∑ n : Fin N, ‖c n‖ ^ 2 := by
  have hlow' : δ / 2 ≤ extendSeq lam R δ 0 := by
    rw [extendSeq_of_le (Nat.zero_le R)]
    exact hlow
  have hhigh' : extendSeq lam R δ R + δ / 2 ≤ 1 := by
    rw [extendSeq_of_le le_rfl]
    exact hhigh
  have hbase := largeSieve_gallagher N hN c hδ (gap_extendSeq hgap) hlow' R hhigh'
  have hsum : ∑ r ∈ Finset.range (R + 1), ‖expSum N c (extendSeq lam R δ r)‖ ^ 2
      = ∑ r ∈ Finset.range (R + 1), ‖expSum N c (lam r)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrR : r ≤ R := by
      have := Finset.mem_range.mp hr
      omega
    rw [extendSeq_of_le hrR]
  rw [hsum] at hbase
  exact hbase

end RHTower.Sieve
