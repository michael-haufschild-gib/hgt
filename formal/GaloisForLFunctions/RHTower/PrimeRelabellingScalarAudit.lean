import Mathlib.Data.PNat.Factors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
# Scalar prime relabelling and its exact finite cutoff defect

Permuting prime factors gives an actual multiplicative bijection of the positive integers.
The resulting scalar Dirichlet sum is norm-summable and exactly zeta on `Re(s)>1` for every
prime permutation. Comparing any two such scalars is therefore zero without any zero input.

Finite cutoffs need not be fixed by the bijection. Their exact defect is supported on the
entering and exiting integers, and its composition law retains the transported cutoff.
These are classical reindexing identities audited as a failed scalar RH candidate. No
claim about a new zero-specific arithmetic relation or novelty is made.
-/

open scoped BigOperators

namespace RHTower.PrimeRelabellingScalarAudit

noncomputable section

def primeMultisetRelabel (e : Equiv.Perm Nat.Primes) : PrimeMultiset ≃ PrimeMultiset where
  toFun v := (v : Multiset Nat.Primes).map e
  invFun v := (v : Multiset Nat.Primes).map e.symm
  left_inv v := by
    change Multiset.map e.symm (Multiset.map e v) = v
    rw [Multiset.map_map]
    simp
  right_inv v := by
    change Multiset.map e (Multiset.map e.symm v) = v
    rw [Multiset.map_map]
    simp

/-- Relabel prime factors and multiply them as actual positive integers. -/
def relabel (e : Equiv.Perm Nat.Primes) : Equiv.Perm ℕ+ :=
  PNat.factorMultisetEquiv.trans ((primeMultisetRelabel e).trans PNat.factorMultisetEquiv.symm)

theorem relabel_mul (e : Equiv.Perm Nat.Primes) (m n : ℕ+) :
    relabel e (m * n) = relabel e m * relabel e n := by
  change PrimeMultiset.prod (Multiset.map e (m * n).factorMultiset) =
    PrimeMultiset.prod (Multiset.map e m.factorMultiset) *
      PrimeMultiset.prod (Multiset.map e n.factorMultiset)
  rw [PNat.factorMultiset_mul]
  calc
    _ = PrimeMultiset.prod ((Multiset.map e m.factorMultiset : PrimeMultiset) +
        (Multiset.map e n.factorMultiset : PrimeMultiset)) := by
      congr 1
      exact Multiset.map_add _ _ _
    _ = _ := PrimeMultiset.prod_add _ _

theorem relabel_prime (e : Equiv.Perm Nat.Primes) (p : Nat.Primes) :
    relabel e (p : ℕ+) = (e p : ℕ+) := by
  change PrimeMultiset.prod (Multiset.map e (p : ℕ+).factorMultiset) = _
  rw [PNat.factorMultiset_ofPrime]
  change PrimeMultiset.prod (PrimeMultiset.ofPrime (e p)) = _
  exact PrimeMultiset.prod_ofPrime (e p)

def scalar (e : Equiv.Perm Nat.Primes) (s : ℂ) : ℂ :=
  ∑' n : ℕ+, (((relabel e n : ℕ+) : ℕ) : ℂ) ^ (-s)

theorem scalar_norm_summable (e : Equiv.Perm Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ+ => ‖(((relabel e n : ℕ+) : ℕ) : ℂ) ^ (-s)‖) := by
  have hz : Summable (fun n : ℕ => ‖(n : ℂ) ^ (-s)‖) :=
    summable_riemannZetaSummand hs
  have h : Summable (fun n : ℕ+ => ‖((n : ℕ) : ℂ) ^ (-s)‖) :=
    summable_pnat_iff_summable_nat.mpr hz
  exact ((relabel e).summable_iff (f := fun n : ℕ+ => ‖((n : ℕ) : ℂ) ^ (-s)‖)).mpr h

/-- The relabelled scalar is the original zeta function throughout absolute convergence. -/
theorem scalar_eq_zeta (e : Equiv.Perm Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    scalar e s = riemannZeta s := by
  rw [scalar, (relabel e).tsum_eq (fun n : ℕ+ => ((n : ℕ) : ℂ) ^ (-s))]
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (n : ℂ) ^ (-s)),
    zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  apply tsum_congr
  intro n
  simp [Complex.cpow_neg, one_div]

def cutoffDefect (e : Equiv.Perm ℕ+) (F : Finset ℕ+) (f : ℕ+ → ℂ) : ℂ :=
  (∑ n ∈ F, f (e n)) - ∑ n ∈ F, f n

/-- Exact finite boundary: the relabelled cutoff must also be transported. -/
theorem cutoffDefect_eq_image (e : Equiv.Perm ℕ+) (F : Finset ℕ+) (f : ℕ+ → ℂ) :
    cutoffDefect e F f = (∑ n ∈ F.image e, f n) - ∑ n ∈ F, f n := by
  rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
  rfl

/-- The common part cancels exactly; only the entering and exiting integer sets remain. -/
theorem cutoffDefect_eq_boundary (e : Equiv.Perm ℕ+) (F : Finset ℕ+) (f : ℕ+ → ℂ) :
    cutoffDefect e F f =
      (∑ n ∈ F.image e \ F, f n) - ∑ n ∈ F \ F.image e, f n := by
  rw [cutoffDefect_eq_image, Finset.sum_sdiff_sub_sum_sdiff]

/-- Composition retains the transported cutoff; this is an unconditional finite identity. -/
theorem cutoffDefect_trans (e d : Equiv.Perm ℕ+) (F : Finset ℕ+) (f : ℕ+ → ℂ) :
    cutoffDefect (d.trans e) F f =
      cutoffDefect e (F.image d) f + cutoffDefect d F f := by
  unfold cutoffDefect
  rw [Finset.sum_image (fun _ _ _ _ h => d.injective h),
    Finset.sum_image (fun _ _ _ _ h => d.injective h)]
  simp only [Equiv.trans_apply]
  abel

/-- The scalar comparison is zero at every point of absolute convergence, without a zero input. -/
theorem scalar_comparison_closed :
    (∀ (e : Equiv.Perm Nat.Primes) (m n : ℕ+),
      relabel e (m * n) = relabel e m * relabel e n) ∧
    (∀ (e : Equiv.Perm Nat.Primes) (p : Nat.Primes), relabel e (p : ℕ+) = (e p : ℕ+)) ∧
    (∀ (e d : Equiv.Perm Nat.Primes) (s : ℂ), 1 < s.re →
      Summable (fun n : ℕ+ => ‖(((relabel e n : ℕ+) : ℕ) : ℂ) ^ (-s)‖) ∧
      scalar e s = riemannZeta s ∧ scalar e s - scalar d s = 0) := by
  refine ⟨relabel_mul, relabel_prime, ?_⟩
  intro e d s hs
  exact ⟨scalar_norm_summable e hs, scalar_eq_zeta e hs,
    by rw [scalar_eq_zeta e hs, scalar_eq_zeta d hs, sub_self]⟩

end

end RHTower.PrimeRelabellingScalarAudit
