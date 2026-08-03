import GaloisForLFunctions.RHTower.Sieve.LargeSieveDual
import GaloisForLFunctions.RHTower.Sieve.ConcreteRoot

/-!
# An exponential sum over a set depends only on residues

The exponential `e(na/q)` is unchanged when `n` is replaced by `n mod q`, because the two arguments
differ by the integer `(n / q)·a`.  Grouping a finite set `A` by residue therefore collapses its
exponential sum to a sum of length `q` weighted by the residue counts:

`∑_{n ∈ A} e(na/q) = ∑_{h < q} #{n ∈ A : n ≡ h} · e(ha/q)`.

This is the step that turns a sieve hypothesis about residue classes into a statement about
exponential sums, and hence the entry point for the large sieve of this folder.
-/

namespace RHTower.Sieve

open Finset

/-- The number of elements of `A` in a residue class. -/
def residueCount (q : ℕ) (A : Finset ℕ) (h : ℕ) : ℕ :=
  (A.filter (fun n => n % q = h)).card

/-- The circle frequency is invariant under integer translation. -/
theorem circleFreq_add_int (x : ℝ) (k : ℤ) : circleFreq (x + (k : ℝ)) = circleFreq x := by
  rw [circleFreq, circleFreq]
  have hsplit : ((2 * Real.pi * (x + (k : ℝ)) : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The circle frequency at a fraction is a power of the standard root of unity. -/
theorem circleFreq_div_eq_rootOfUnity_pow (q m : ℕ) :
    circleFreq ((m : ℝ) / (q : ℝ)) = (rootOfUnity q) ^ m := by
  have hval : (2 * Real.pi * ((m : ℝ) / (q : ℝ)) : ℝ)
      = ((m : ℝ) * (2 * Real.pi / (q : ℝ)) : ℝ) := by ring
  rw [circleFreq, rootOfUnity_pow, hval]

/-- **Reduction modulo the denominator.** -/
theorem circleFreq_mod {q : ℕ} (hq : 0 < q) (n a : ℕ) :
    circleFreq (((n * a : ℕ) : ℝ) / (q : ℝ)) = circleFreq (((n % q * a : ℕ) : ℝ) / (q : ℝ)) := by
  have hqR : ((q : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact ne_of_gt this
  have hnat : n * a = q * (n / q * a) + n % q * a := by
    conv_lhs => rw [← Nat.div_add_mod n q]
    ring
  have hcastnat : ((n * a : ℕ) : ℝ)
      = (q : ℝ) * ((n / q * a : ℕ) : ℝ) + ((n % q * a : ℕ) : ℝ) := by
    rw [hnat]
    push_cast
    ring
  have hz : (((n / q * a : ℕ) : ℤ) : ℝ) = ((n / q * a : ℕ) : ℝ) := Int.cast_natCast _
  have hkey : ((n * a : ℕ) : ℝ) / (q : ℝ)
      = ((n % q * a : ℕ) : ℝ) / (q : ℝ) + (((n / q * a : ℕ) : ℤ) : ℝ) := by
    rw [hcastnat, hz]
    field_simp
    ring
  rw [hkey, circleFreq_add_int]

/-- **An exponential sum over a set is a sum over residues.** -/
theorem sum_circleFreq_eq_residue {q : ℕ} (hq : 0 < q) (a : ℕ) (A : Finset ℕ) :
    ∑ n ∈ A, circleFreq (((n * a : ℕ) : ℝ) / (q : ℝ))
      = ∑ h ∈ Finset.range q,
          ((residueCount q A h : ℕ) : ℂ) * circleFreq (((h * a : ℕ) : ℝ) / (q : ℝ)) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % q) (t := Finset.range q)
      (fun n _ => Finset.mem_range.mpr (Nat.mod_lt _ hq))]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hconst : ∀ n ∈ A.filter (fun n => n % q = h),
      circleFreq (((n * a : ℕ) : ℝ) / (q : ℝ)) = circleFreq (((h * a : ℕ) : ℝ) / (q : ℝ)) := by
    intro n hn
    have hmod := (Finset.mem_filter.mp hn).2
    rw [circleFreq_mod hq n a, hmod]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, residueCount]

end RHTower.Sieve
