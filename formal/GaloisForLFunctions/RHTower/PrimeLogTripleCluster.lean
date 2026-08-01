import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.PrimeCounting

/-!
# Cofinal three-prime logarithmic clusters from Euler divergence

Euler's divergence of the reciprocal-prime series forces arbitrarily far triples of consecutive
primes with both adjacent logarithmic gaps arbitrarily small.  If every sufficiently late
two-gap block contained a gap at least `δ`, the primes at even block endpoints would grow at least
geometrically with ratio `exp δ`.  Both parity subsequences of their reciprocals would then be
summable, contradicting Euler divergence.

This elementary consequence avoids invoking the prime number theorem when a source kernel is known
to be nonzero on a neighborhood of zero and one needs cofinal three-prime cycle coordinates.
-/

open scoped BigOperators Nat.Prime

namespace RHTower

noncomputable section

/-- `n`th prime as a member of the marked-prime subtype. -/
def nthPrimeSubtype (n : ℕ) : Nat.Primes :=
  ⟨Nat.nth Nat.Prime n, Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n⟩

/-- Increasing enumeration identifies natural indices with marked primes. -/
def nthPrimeEquiv : ℕ ≃ Nat.Primes where
  toFun := nthPrimeSubtype
  invFun := fun p => Nat.primeCounting' p
  left_inv n := by
    simp [nthPrimeSubtype]
  right_inv p := by
    apply Subtype.ext
    simp [nthPrimeSubtype, Nat.primeCounting', Nat.nth_count p.prop]

theorem not_summable_nthPrime_reciprocal :
    ¬ Summable (fun n : ℕ => (1 / (nthPrimeSubtype n : ℝ))) := by
  intro h
  apply Nat.Primes.not_summable_one_div
  apply nthPrimeEquiv.summable_iff.mp
  simpa [Function.comp_def, nthPrimeEquiv] using h

theorem nthPrimeSubtype_strictMono :
    StrictMono (fun n : ℕ => (nthPrimeSubtype n : ℕ)) := by
  exact Nat.nth_strictMono Nat.infinite_setOf_prime

theorem nthPrimeSubtype_injective :
    Function.Injective nthPrimeSubtype := by
  intro m n h
  apply nthPrimeSubtype_strictMono.injective
  exact congrArg Subtype.val h

theorem nthPrimeSubtype_pos (n : ℕ) :
    0 < (nthPrimeSubtype n : ℝ) := by
  exact_mod_cast (nthPrimeSubtype n).prop.pos

theorem nthPrimeSubtype_log_strictMono :
    StrictMono (fun n : ℕ => Real.log (nthPrimeSubtype n : ℝ)) := by
  intro m n hmn
  apply Real.strictMonoOn_log
    (nthPrimeSubtype_pos m) (nthPrimeSubtype_pos n)
  exact_mod_cast nthPrimeSubtype_strictMono hmn

theorem summable_rpow_nat_div_two {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => r ^ (n / 2)) := by
  have hprod : Summable (fun x : ℕ × Fin 2 => r ^ x.1) := by
    apply (summable_prod_of_nonneg (fun x => by positivity)).2
    constructor
    · intro n
      apply summable_of_ne_finset_zero (s := Finset.univ)
      simp
    · have hgeom : Summable (fun n : ℕ => r ^ n) :=
        summable_geometric_of_lt_one hr0 hr1
      simpa [tsum_fintype] using hgeom.mul_left 2
  have htrans := (Nat.divModEquiv 2).summable_iff.mpr hprod
  simpa [Function.comp_def, Nat.divModEquiv_apply] using htrans

/-- **Cofinal logarithmic triple clustering.** For every positive gap threshold and every starting
index, three consecutive primes occur later with both adjacent logarithmic gaps below the
threshold. -/
theorem exists_two_consecutive_nthPrime_log_gaps_lt
    {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      Real.log (nthPrimeSubtype (n + 1) : ℝ) -
          Real.log (nthPrimeSubtype n : ℝ) < δ ∧
      Real.log (nthPrimeSubtype (n + 2) : ℝ) -
          Real.log (nthPrimeSubtype (n + 1) : ℝ) < δ := by
  by_contra hcluster
  push Not at hcluster
  have hgap_nonneg (n : ℕ) :
      0 ≤ Real.log (nthPrimeSubtype (n + 1) : ℝ) -
        Real.log (nthPrimeSubtype n : ℝ) := by
    linarith [nthPrimeSubtype_log_strictMono n.lt_succ_self]
  have hblock (n : ℕ) (hn : N ≤ n) :
      δ ≤
        (Real.log (nthPrimeSubtype (n + 1) : ℝ) -
          Real.log (nthPrimeSubtype n : ℝ)) +
        (Real.log (nthPrimeSubtype (n + 2) : ℝ) -
          Real.log (nthPrimeSubtype (n + 1) : ℝ)) := by
    by_cases hfirst :
        Real.log (nthPrimeSubtype (n + 1) : ℝ) -
            Real.log (nthPrimeSubtype n : ℝ) < δ
    · have hsecond :
          δ ≤ Real.log (nthPrimeSubtype (n + 2) : ℝ) -
            Real.log (nthPrimeSubtype (n + 1) : ℝ) :=
        hcluster n hn hfirst
      linarith [hgap_nonneg n]
    · have hfirst' :
          δ ≤ Real.log (nthPrimeSubtype (n + 1) : ℝ) -
            Real.log (nthPrimeSubtype n : ℝ) := not_lt.mp hfirst
      linarith [hgap_nonneg (n + 1)]
  have hlog_lower (k : ℕ) :
      Real.log (nthPrimeSubtype N : ℝ) + (k : ℝ) * δ ≤
        Real.log (nthPrimeSubtype (N + 2 * k) : ℝ) := by
    induction k with
    | zero =>
        simp
    | succ k ih =>
        have hb := hblock (N + 2 * k) (by omega)
        have hindex :
            N + 2 * (k + 1) = (N + 2 * k) + 2 := by omega
        rw [hindex]
        calc
          Real.log (nthPrimeSubtype N : ℝ) +
                ((k + 1 : ℕ) : ℝ) * δ
              = (Real.log (nthPrimeSubtype N : ℝ) +
                  (k : ℝ) * δ) + δ := by
                    push_cast
                    ring
          _ ≤ Real.log (nthPrimeSubtype (N + 2 * k) : ℝ) + δ := by
            linarith
          _ ≤ Real.log (nthPrimeSubtype (N + 2 * k) : ℝ) +
              ((Real.log (nthPrimeSubtype (N + 2 * k + 1) : ℝ) -
                Real.log (nthPrimeSubtype (N + 2 * k) : ℝ)) +
              (Real.log (nthPrimeSubtype (N + 2 * k + 2) : ℝ) -
                Real.log (nthPrimeSubtype (N + 2 * k + 1) : ℝ))) := by
            linarith
          _ = Real.log (nthPrimeSubtype (N + 2 * k + 2) : ℝ) := by
            ring
  let C : ℝ := (nthPrimeSubtype N : ℝ)⁻¹
  let r : ℝ := Real.exp (-δ)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hmajor (m : ℕ) :
      1 / (nthPrimeSubtype (N + m) : ℝ) ≤
        C * r ^ (m / 2) := by
    let k := m / 2
    have htwok : 2 * k ≤ m := by
      dsimp [k]
      exact Nat.mul_div_le m 2
    have hprime_le :
        (nthPrimeSubtype (N + 2 * k) : ℝ) ≤
          (nthPrimeSubtype (N + m) : ℝ) := by
      exact_mod_cast nthPrimeSubtype_strictMono.monotone
        (Nat.add_le_add_left htwok N)
    have hrecip_le :
        1 / (nthPrimeSubtype (N + m) : ℝ) ≤
          1 / (nthPrimeSubtype (N + 2 * k) : ℝ) :=
      one_div_le_one_div_of_le
        (nthPrimeSubtype_pos (N + 2 * k)) hprime_le
    have hlog := hlog_lower k
    have hexp :
        Real.exp (-Real.log (nthPrimeSubtype (N + 2 * k) : ℝ)) ≤
          Real.exp (-Real.log (nthPrimeSubtype N : ℝ) -
            (k : ℝ) * δ) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hrewrite_left :
        Real.exp (-Real.log (nthPrimeSubtype (N + 2 * k) : ℝ)) =
          1 / (nthPrimeSubtype (N + 2 * k) : ℝ) := by
      rw [Real.exp_neg,
        Real.exp_log (nthPrimeSubtype_pos (N + 2 * k))]
      simp only [one_div]
    have hrewrite_right :
        Real.exp (-Real.log (nthPrimeSubtype N : ℝ) -
            (k : ℝ) * δ) = C * r ^ k := by
      rw [show -Real.log (nthPrimeSubtype N : ℝ) -
          (k : ℝ) * δ =
          -Real.log (nthPrimeSubtype N : ℝ) +
            (k : ℝ) * (-δ) by ring,
        Real.exp_add, Real.exp_neg,
        Real.exp_log (nthPrimeSubtype_pos N),
        Real.exp_nat_mul]
    calc
      1 / (nthPrimeSubtype (N + m) : ℝ) ≤
          1 / (nthPrimeSubtype (N + 2 * k) : ℝ) := hrecip_le
      _ = Real.exp (-Real.log
          (nthPrimeSubtype (N + 2 * k) : ℝ)) := hrewrite_left.symm
      _ ≤ Real.exp (-Real.log (nthPrimeSubtype N : ℝ) -
          (k : ℝ) * δ) := hexp
      _ = C * r ^ k := hrewrite_right
      _ = C * r ^ (m / 2) := rfl
  have hgeom : Summable (fun m : ℕ => C * r ^ (m / 2)) :=
    (summable_rpow_nat_div_two hr0 hr1).mul_left C
  have htail : Summable (fun m : ℕ =>
      1 / (nthPrimeSubtype (N + m) : ℝ)) :=
    Summable.of_nonneg_of_le
      (fun m => by positivity) hmajor hgeom
  apply not_summable_nthPrime_reciprocal
  apply (summable_nat_add_iff N).mp
  simpa [Nat.add_comm] using htail

end

end RHTower
