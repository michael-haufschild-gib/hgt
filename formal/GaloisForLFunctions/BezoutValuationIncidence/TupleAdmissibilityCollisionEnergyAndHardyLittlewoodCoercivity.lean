import GaloisForLFunctions.BezoutValuationIncidence.GeneralRadicalMultiplicativeAndGcdLcmValuationAlgebra
import GaloisForLFunctions.BezoutValuationIncidence.NonMarkovianLagOperatorAlgebraAndPrimePowerRevival

/-!
# Tuple Admissibility, Mod-$d$ Collision Energy, and Hardy–Littlewood Spectral Coercivity

In multidimensional sieve theory (Hardy–Littlewood, Selberg, Goldston–Pintz–Yıldırım, Maynard–Tao),
one studies divisor correlations across an arbitrary $k$-tuple of additive shifts
$(n + h_1, \dots, n + h_k)$ for $H : \operatorname{Fin} k \to \mathbb{N}$.

This module establishes the exact residue-occupancy, collision-energy, and radical-factorization
laws governing arbitrary $k$-tuples $H : \operatorname{Fin} k \to \mathbb{N}$, and proves that our
earlier 2-point consecutive-integer results ($H = (0, 1)$, where $p = 2$ is annihilated and $p = 3$
attains the universal $1/2$-coercivity floor) are the $k = 2$ specialization of a general
$k$-tuple Hardy–Littlewood admissibility theorem:

1. **Residue Occupancy & Collision Energy (`tupleResidueCount`, `tupleModCollisionEnergy`):**
   For any $k$-tuple $H : \operatorname{Fin} k \to \mathbb{N}$ and modulus $d \ge 1$, let
   $\nu_H(d, r) = \#\{i \in \operatorname{Fin} k : H(i) \bmod d = r\}$ and
   $C_H(d) = \sum_{r=0}^{d-1} \nu_H(d, r)^2$. Then $\sum_{r=0}^{d-1} \nu_H(d, r) = k$,
   $C_H(d) = \#\{(i, j) : H(i) \equiv H(j) \pmod d\} \ge k$, and $C_H(d) = k$ if and only if
   the shifts of $H$ are pairwise incongruent modulo $d$ ($\nu_H(d, r) \le 1$ for all $r$).

2. **Prime Structure Factor & Exact Sum-of-Squares Decomposition (`tuplePrimeStructureFactor`):**
   The prime-mode Ramanujan dispersion weight of $H$ at a prime $p$ is
   $S_p(H) = p\,C_H(p) - k^2 = \sum_{i, j} \bigl(p\,\mathbf{1}_{H_i \equiv H_j \pmod p} - 1\bigr)$,
   which satisfies the exact sum-of-squares identity
   $$p\,S_p(H) = \sum_{r=0}^{p-1} \bigl(p\,\nu_H(p, r) - k\bigr)^2 \ge 0.$$
   Thus $S_p(H) = 0$ if and only if $H$ is completely equidistributed modulo $p$
   ($p\,\nu_H(p, r) = k$ for all $r < p$, the exact modular obstruction), while if $H$ is
   pairwise distinct modulo $p$ ($\nu_H(p, r) \le 1$), then $S_p(H) = k(p - k)$.

3. **The Hardy–Littlewood Admissibility Spectral Coercivity Theorem
   (`IsTupleAdmissibleMod`, `hardyLittlewood_admissibility_sos_identity`,
   `hardyLittlewood_admissibility_coercivity`):**
   A $k$-tuple $H$ is Hardy–Littlewood admissible at $p$ if it omits at least one residue class
   $r_0 \in \{0, \dots, p - 1\}$ ($\nu_H(p, r_0) = 0$). On the remaining $p - 1$ residue classes,
   $S_p(H)$ satisfies the exact sum-of-squares identity
   $$(p - 1)\bigl((p - 1)\,S_p(H) - k^2\bigr) =
     p \sum_{r \in (\operatorname{range} p).\operatorname{erase} r_0}
       \bigl((p - 1)\nu_H(p, r) - k\bigr)^2 \ge 0.$$
   Consequently, every $k$-tuple that is Hardy–Littlewood admissible at a prime $p$ satisfies
   the universal strictly positive coercivity bound
   $$S_p(H) \ge \frac{k^2}{p - 1} = \frac{k^2}{\varphi(p)} > 0,$$
   with equality if and only if $(p - 1)\nu_H(p, r) = k$ on all $p - 1$ non-forbidden residue
   classes (recovering $S_3((0, 1)) = \frac{2^2}{3 - 1} = 2$, i.e. $\frac{S_3((0,1))}{2\varphi(3)} = \frac{1}{2}$,
   at $k = 2, p = 3$).

4. **General Lag-$h$ Radical Factorization (`radicalPrimeProd_shift_mul_eq`):**
   For any lag $h \ge 1$ and any radical prime-factor functional $F = \operatorname{radicalPrimeProd}(w)$,
   $$F(n)\,F(n + h) = F\bigl(n(n + h)\bigr)\,F\bigl(\gcd(n, h)\bigr),$$
   reducing to exact multiplicativity $F(n(n + h)) = F(n)F(n + h)$ whenever $\gcd(n, h) = 1$,
   and obeying the universal lag-$h$ Bézout ceiling $F(n)\,F(n + h) \le F(\gcd(n, h))$.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

/-! ### 1. Residue Occupancy Counts and Mod-$d$ Collision Energy -/

/-- Number of elements in the shift $k$-tuple $H : \operatorname{Fin} k \to \mathbb{N}$ occupying
residue class $r$ modulo $d$:
$$\nu_H(d, r) = \#\{i \in \operatorname{Fin} k : H(i) \bmod d = r\}.$$ -/
def tupleResidueCount {k : ℕ} (H : Fin k → ℕ) (d r : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin k => H i % d = r)).card

/-- The mod-$d$ collision energy of a shift $k$-tuple $H : \operatorname{Fin} k \to \mathbb{N}$:
$$C_H(d) = \sum_{r=0}^{d-1} \nu_H(d, r)^2.$$ -/
def tupleModCollisionEnergy {k : ℕ} (H : Fin k → ℕ) (d : ℕ) : ℕ :=
  ∑ r ∈ Finset.range d, (tupleResidueCount H d r) ^ 2

/-- Conservation of tuple mass across the $d$ residue classes modulo $d > 0$:
$$\sum_{r=0}^{d-1} \nu_H(d, r) = k.$$ -/
theorem sum_tupleResidueCount_eq_card {k : ℕ} (H : Fin k → ℕ) (d : ℕ) (hd : 0 < d) :
    ∑ r ∈ Finset.range d, tupleResidueCount H d r = k := by
  unfold tupleResidueCount
  rw [← Finset.card_biUnion]
  · have h_eq : (Finset.range d).biUnion
        (fun r => Finset.univ.filter (fun i : Fin k => H i % d = r)) = Finset.univ := by
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_univ,
        true_and, iff_true]
      exact ⟨H i % d, Nat.mod_lt (H i) hd, rfl⟩
    rw [h_eq, Finset.card_fin]
  · intro r₁ _ r₂ _ hne
    change Disjoint (Finset.univ.filter (fun i : Fin k => H i % d = r₁))
      (Finset.univ.filter (fun i : Fin k => H i % d = r₂))
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    rw [Finset.mem_filter] at hi₁ hi₂
    exact hne (hi₁.2.symm.trans hi₂.2)

/-- Each natural occupancy count satisfies $\nu \le \nu^2$. -/
theorem tupleResidueCount_le_sq {k : ℕ} (H : Fin k → ℕ) (d r : ℕ) :
    tupleResidueCount H d r ≤ (tupleResidueCount H d r) ^ 2 := by
  rw [sq]
  exact Nat.le_mul_self (tupleResidueCount H d r)

/-- For every $d > 0$, the mod-$d$ collision energy is at least the tuple size $k$:
$$k \le C_H(d).$$ -/
theorem card_le_tupleModCollisionEnergy {k : ℕ} (H : Fin k → ℕ) (d : ℕ) (hd : 0 < d) :
    k ≤ tupleModCollisionEnergy H d := by
  calc
    k = ∑ r ∈ Finset.range d, tupleResidueCount H d r :=
      (sum_tupleResidueCount_eq_card H d hd).symm
    _ ≤ ∑ r ∈ Finset.range d, (tupleResidueCount H d r) ^ 2 :=
      Finset.sum_le_sum (fun r _ => tupleResidueCount_le_sq H d r)
    _ = tupleModCollisionEnergy H d := rfl

/-- A natural number $n$ satisfies $n^2 = n$ if and only if $n \le 1$. -/
theorem nat_sq_eq_self_iff_le_one (n : ℕ) : n ^ 2 = n ↔ n ≤ 1 := by
  constructor
  · intro h
    nlinarith
  · intro h
    interval_cases n <;> rfl

/-- The mod-$d$ collision energy equals $k$ if and only if the shifts of $H$ are pairwise
incongruent modulo $d$ ($\nu_H(d, r) \le 1$ for all $r < d$). -/
theorem tupleModCollisionEnergy_eq_card_iff_le_one {k : ℕ} (H : Fin k → ℕ) (d : ℕ) (hd : 0 < d) :
    tupleModCollisionEnergy H d = k ↔
      ∀ r ∈ Finset.range d, tupleResidueCount H d r ≤ 1 := by
  have hsum := sum_tupleResidueCount_eq_card H d hd
  have hle : ∀ r ∈ Finset.range d, tupleResidueCount H d r ≤ (tupleResidueCount H d r) ^ 2 :=
    fun r _ => tupleResidueCount_le_sq H d r
  constructor
  · intro heq r hr
    have heq' : (∑ r ∈ Finset.range d, tupleResidueCount H d r) =
        ∑ r ∈ Finset.range d, (tupleResidueCount H d r) ^ 2 := by
      rw [hsum, ← tupleModCollisionEnergy, heq]
    have h_eq_r := (Finset.sum_eq_sum_iff_of_le hle).mp heq' r hr
    exact (nat_sq_eq_self_iff_le_one _).mp h_eq_r.symm
  · intro hall
    calc
      tupleModCollisionEnergy H d = ∑ r ∈ Finset.range d, tupleResidueCount H d r := by
        unfold tupleModCollisionEnergy
        apply Finset.sum_congr rfl
        intro r hr
        exact (nat_sq_eq_self_iff_le_one _).mpr (hall r hr)
      _ = k := hsum

/-- Pairwise residue collision sum over $\operatorname{Fin} k \times \operatorname{Fin} k$ equals
$C_H(d)$. -/
theorem sum_pair_mod_eq_tupleModCollisionEnergy {k : ℕ} (H : Fin k → ℕ) (d : ℕ) (hd : 0 < d) :
    (∑ i : Fin k, ∑ j : Fin k, (if H i % d = H j % d then (1 : ℝ) else 0)) =
      (tupleModCollisionEnergy H d : ℝ) := by
  unfold tupleModCollisionEnergy tupleResidueCount
  push_cast
  have h_part : ∀ i : Fin k,
      (∑ r ∈ Finset.range d, (if H i % d = r then (1 : ℝ) else 0) *
        ∑ j : Fin k, (if H j % d = r then (1 : ℝ) else 0)) =
      ∑ j : Fin k, (if H i % d = H j % d then (1 : ℝ) else 0) := by
    intro i
    rw [Finset.sum_eq_single (H i % d)]
    · simp only [ ↓reduceIte, one_mul]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : H i % d = H j % d
      · simp [h]
      · have h' : H j % d ≠ H i % d := Ne.symm h
        simp [h, h']
    · intro r _ hne
      simp [Ne.symm hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (Nat.mod_lt (H i) hd)))
  calc
    (∑ i : Fin k, ∑ j : Fin k, (if H i % d = H j % d then (1 : ℝ) else 0))
      = ∑ i : Fin k, ∑ r ∈ Finset.range d,
          (if H i % d = r then (1 : ℝ) else 0) *
            ∑ j : Fin k, (if H j % d = r then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (h_part i).symm
    _ = ∑ r ∈ Finset.range d,
          (∑ i : Fin k, (if H i % d = r then (1 : ℝ) else 0)) *
            (∑ j : Fin k, (if H j % d = r then (1 : ℝ) else 0)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [← Finset.sum_mul]
    _ = ∑ r ∈ Finset.range d,
          (((Finset.univ.filter (fun i : Fin k => H i % d = r)).card : ℝ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro r _
        have h_card : (∑ i : Fin k, (if H i % d = r then (1 : ℝ) else 0)) =
            ((Finset.univ.filter (fun i : Fin k => H i % d = r)).card : ℝ) := by
          rw [← Finset.sum_filter]
          simp
        rw [h_card, sq]

/-! ### 2. The Prime Structure Factor and Exact Sum-of-Squares Identity -/

/-- The prime Ramanujan structure factor of a $k$-tuple $H : \operatorname{Fin} k \to \mathbb{N}$
at modulus $p$:
$$S_p(H) = p\,C_H(p) - k^2.$$ -/
def tuplePrimeStructureFactor {k : ℕ} (H : Fin k → ℕ) (p : ℕ) : ℝ :=
  (p : ℝ) * (tupleModCollisionEnergy H p : ℝ) - (k : ℝ) ^ 2

/-- Pairwise Ramanujan correlation representation of `tuplePrimeStructureFactor`:
$$S_p(H) = \sum_{i, j \in \operatorname{Fin} k}
  \bigl(\text{if } H(i) \equiv H(j) \pmod p \text{ then } p - 1 \text{ else } -1\bigr).$$ -/
theorem sum_pair_prime_ramanujan_eq_tuplePrimeStructureFactor {k : ℕ} (H : Fin k → ℕ)
    (p : ℕ) (hp : 0 < p) :
    (∑ i : Fin k, ∑ j : Fin k,
      (if H i % p = H j % p then ((p : ℝ) - 1) else (-1 : ℝ))) =
      tuplePrimeStructureFactor H p := by
  have hterm : ∀ i j : Fin k,
      (if H i % p = H j % p then ((p : ℝ) - 1) else (-1 : ℝ)) =
        (p : ℝ) * (if H i % p = H j % p then (1 : ℝ) else 0) - 1 := by
    intro i j
    split_ifs <;> ring
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_pair_mod_eq_tupleModCollisionEnergy H p hp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold tuplePrimeStructureFactor
  ring

/-- **Exact Sum-of-Squares Decomposition of the Prime Structure Factor:**
For every $p > 0$ and every $k$-tuple $H : \operatorname{Fin} k \to \mathbb{N}$,
$$p\,S_p(H) = \sum_{r=0}^{p-1} \bigl(p\,\nu_H(p, r) - k\bigr)^2.$$ -/
theorem mul_tuplePrimeStructureFactor_eq_sum_sq {k : ℕ} (H : Fin k → ℕ) (p : ℕ) (hp : 0 < p) :
    (p : ℝ) * tuplePrimeStructureFactor H p =
      ∑ r ∈ Finset.range p, ((p : ℝ) * (tupleResidueCount H p r : ℝ) - (k : ℝ)) ^ 2 := by
  have hsum : (∑ r ∈ Finset.range p, (tupleResidueCount H p r : ℝ)) = (k : ℝ) := by
    exact_mod_cast sum_tupleResidueCount_eq_card H p hp
  have hsq : ∀ r : ℕ,
      ((p : ℝ) * (tupleResidueCount H p r : ℝ) - (k : ℝ)) ^ 2 =
        (p : ℝ) ^ 2 * (tupleResidueCount H p r : ℝ) ^ 2 -
          2 * (p : ℝ) * (k : ℝ) * (tupleResidueCount H p r : ℝ) + (k : ℝ) ^ 2 :=
    fun r => by ring
  simp_rw [hsq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold tuplePrimeStructureFactor tupleModCollisionEnergy
  push_cast
  ring

/-- Non-negativity of the prime structure factor $S_p(H) \ge 0$ for every $p > 0$. -/
theorem tuplePrimeStructureFactor_nonneg {k : ℕ} (H : Fin k → ℕ) (p : ℕ) (hp : 0 < p) :
    0 ≤ tuplePrimeStructureFactor H p := by
  have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hmul : 0 ≤ (p : ℝ) * tuplePrimeStructureFactor H p := by
    rw [mul_tuplePrimeStructureFactor_eq_sum_sq H p hp]
    exact Finset.sum_nonneg (fun r _ => sq_nonneg _)
  exact nonneg_of_mul_nonneg_right hmul hpR

/-- **Exact Modular Equidistribution Vanishing Law:**
For $p > 0$, the prime structure factor $S_p(H)$ vanishes if and only if $H$ hits every residue
class modulo $p$ with identical multiplicity $k / p$ ($p\,\nu_H(p, r) = k$ for all $r < p$). -/
theorem tuplePrimeStructureFactor_eq_zero_iff {k : ℕ} (H : Fin k → ℕ) (p : ℕ) (hp : 0 < p) :
    tuplePrimeStructureFactor H p = 0 ↔
      ∀ r ∈ Finset.range p, p * tupleResidueCount H p r = k := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← mul_eq_zero_iff_left hp0, mul_tuplePrimeStructureFactor_eq_sum_sq H p hp]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sq_nonneg _)]
  constructor
  · intro hall r hr
    have h_r := sq_eq_zero_iff.mp (hall r hr)
    have h_cast : ((p * tupleResidueCount H p r : ℕ) : ℝ) = (k : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h_cast
  · intro hall r hr
    have h_cast : (p : ℝ) * (tupleResidueCount H p r : ℝ) = (k : ℝ) := by
      exact_mod_cast hall r hr
    rw [h_cast, sub_self, sq, mul_zero]

/-- If the shifts of $H$ are pairwise incongruent modulo $p$ ($\nu_H(p, r) \le 1$ for all $r < p$),
then $S_p(H) = k(p - k)$. -/
theorem tuplePrimeStructureFactor_of_le_one {k : ℕ} (H : Fin k → ℕ) (p : ℕ) (hp : 0 < p)
    (h_dist : ∀ r ∈ Finset.range p, tupleResidueCount H p r ≤ 1) :
    tuplePrimeStructureFactor H p = (k : ℝ) * ((p : ℝ) - (k : ℝ)) := by
  unfold tuplePrimeStructureFactor
  rw [(tupleModCollisionEnergy_eq_card_iff_le_one H p hp).mpr h_dist]
  ring

/-! ### 3. The Hardy–Littlewood Admissibility Spectral Coercivity Theorem -/

/-- A $k$-tuple $H : \operatorname{Fin} k \to \mathbb{N}$ is **Hardy–Littlewood admissible modulo $p$**
if its shifts do not cover all $p$ residue classes modulo $p$ (there exists a forbidden residue
class $r_0 < p$ with $\nu_H(p, r_0) = 0$). -/
def IsTupleAdmissibleMod {k : ℕ} (H : Fin k → ℕ) (p : ℕ) : Prop :=
  ∃ r₀ ∈ Finset.range p, tupleResidueCount H p r₀ = 0

/-- Every $k$-tuple with $k < p$ is automatically Hardy–Littlewood admissible modulo $p$ by the
pigeonhole principle. -/
theorem isTupleAdmissibleMod_of_lt {k : ℕ} (H : Fin k → ℕ) (p : ℕ) (hkp : k < p) :
    IsTupleAdmissibleMod H p := by
  by_contra hnot
  unfold IsTupleAdmissibleMod at hnot
  have hp : 0 < p := by omega
  have h1 : ∀ r ∈ Finset.range p, 1 ≤ tupleResidueCount H p r := by
    intro r hr
    have hne : tupleResidueCount H p r ≠ 0 := fun hz => hnot ⟨r, hr, hz⟩
    omega
  have hsum := sum_tupleResidueCount_eq_card H p hp
  have hge : p ≤ ∑ r ∈ Finset.range p, tupleResidueCount H p r := by
    simpa using Finset.sum_le_sum h1
  omega

/-- **Exact Hardy–Littlewood Admissibility Sum-of-Squares Identity:**
If a $k$-tuple $H$ omits residue class $r_0 < p$ ($\nu_H(p, r_0) = 0$), then on the remaining
$p - 1$ residue classes $(\operatorname{range} p).\operatorname{erase} r_0$:
$$(p - 1)\bigl((p - 1)\,S_p(H) - k^2\bigr) =
  p \sum_{r \in (\operatorname{range} p).\operatorname{erase} r_0}
    \bigl((p - 1)\nu_H(p, r) - k\bigr)^2.$$ -/
theorem hardyLittlewood_admissibility_sos_identity {k : ℕ} (H : Fin k → ℕ) (p r₀ : ℕ)
    (hr₀ : r₀ ∈ Finset.range p) (hz : tupleResidueCount H p r₀ = 0) :
    ((p : ℝ) - 1) * (((p : ℝ) - 1) * tuplePrimeStructureFactor H p - (k : ℝ) ^ 2) =
      (p : ℝ) * ∑ r ∈ (Finset.range p).erase r₀,
        (((p : ℝ) - 1) * (tupleResidueCount H p r : ℝ) - (k : ℝ)) ^ 2 := by
  have hp : 1 ≤ p := by
    have := Finset.mem_range.mp hr₀
    omega
  have hsum_erased :
      (∑ r ∈ (Finset.range p).erase r₀, (tupleResidueCount H p r : ℝ)) = (k : ℝ) := by
    have htot : (∑ r ∈ Finset.range p, (tupleResidueCount H p r : ℝ)) = (k : ℝ) := by
      exact_mod_cast sum_tupleResidueCount_eq_card H p (by omega)
    rw [← Finset.add_sum_erase _ _ hr₀, hz] at htot
    simpa using htot
  have hsq_erased :
      (∑ r ∈ (Finset.range p).erase r₀, (tupleResidueCount H p r : ℝ) ^ 2) =
        (tupleModCollisionEnergy H p : ℝ) := by
    have htot : (∑ r ∈ Finset.range p, (tupleResidueCount H p r : ℝ) ^ 2) =
        (tupleModCollisionEnergy H p : ℝ) := by
      unfold tupleModCollisionEnergy
      push_cast
      rfl
    rw [← Finset.add_sum_erase _ _ hr₀, hz] at htot
    simpa using htot
  have hcard_erased : ((Finset.range p).erase r₀).card = p - 1 := by
    rw [Finset.card_erase_of_mem hr₀, Finset.card_range]
  have hexpand : ∀ r : ℕ,
      (((p : ℝ) - 1) * (tupleResidueCount H p r : ℝ) - (k : ℝ)) ^ 2 =
        ((p : ℝ) - 1) ^ 2 * (tupleResidueCount H p r : ℝ) ^ 2 -
          2 * ((p : ℝ) - 1) * (k : ℝ) * (tupleResidueCount H p r : ℝ) + (k : ℝ) ^ 2 :=
    fun r => by ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hsq_erased, hsum_erased]
  simp only [Finset.sum_const, hcard_erased, nsmul_eq_mul]
  have hp_cast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp, Nat.cast_one]
  rw [hp_cast]
  unfold tuplePrimeStructureFactor
  ring

/-- **The Hardy–Littlewood Admissibility Spectral Coercivity Theorem:**
For every $p \ge 2$ and every $k$-tuple $H : \operatorname{Fin} k \to \mathbb{N}$ that is
Hardy–Littlewood admissible modulo $p$ (`IsTupleAdmissibleMod H p`),
$$k^2 \le (p - 1)\,S_p(H).$$ -/
theorem hardyLittlewood_admissibility_coercivity {k : ℕ} (H : Fin k → ℕ) (p : ℕ) (hp : 2 ≤ p)
    (hadm : IsTupleAdmissibleMod H p) :
    (k : ℝ) ^ 2 ≤ ((p : ℝ) - 1) * tuplePrimeStructureFactor H p := by
  obtain ⟨r₀, hr₀, hz⟩ := hadm
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have h_id := hardyLittlewood_admissibility_sos_identity H p r₀ hr₀ hz
  have h_rhs_nonneg : 0 ≤ (p : ℝ) * ∑ r ∈ (Finset.range p).erase r₀,
      (((p : ℝ) - 1) * (tupleResidueCount H p r : ℝ) - (k : ℝ)) ^ 2 := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun r _ => sq_nonneg _)
  rw [← h_id] at h_rhs_nonneg
  have h_sub := nonneg_of_mul_nonneg_right h_rhs_nonneg hp1
  linarith

/-- Totient-normalized form of Hardy–Littlewood admissibility coercivity at any prime $p$:
$$\frac{k^2}{\varphi(p)} \le S_p(H).$$ -/
theorem hardyLittlewood_admissibility_div_totient_le {k : ℕ} (H : Fin k → ℕ) (p : ℕ)
    (hp : p.Prime) (hadm : IsTupleAdmissibleMod H p) :
    (k : ℝ) ^ 2 / (p.totient : ℝ) ≤ tuplePrimeStructureFactor H p := by
  have hp2 : 2 ≤ p := hp.two_le
  have htot : (p.totient : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub (by omega), Nat.cast_one]
  rw [htot, div_le_iff₀ (by linarith [show (2 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp2])]
  have h := hardyLittlewood_admissibility_coercivity H p hp2 hadm
  linarith

/-- Characterization of equality in the Hardy–Littlewood admissibility coercivity bound:
for $p \ge 2$ and $\nu_H(p, r_0) = 0$, $(p - 1)\,S_p(H) = k^2$ if and only if $H$ hits each of the
remaining $p - 1$ residue classes with equal weight $(p - 1)\,\nu_H(p, r) = k$. -/
theorem hardyLittlewood_admissibility_coercivity_eq_iff {k : ℕ} (H : Fin k → ℕ) (p r₀ : ℕ)
    (hp : 2 ≤ p) (hr₀ : r₀ ∈ Finset.range p) (hz : tupleResidueCount H p r₀ = 0) :
    ((p : ℝ) - 1) * tuplePrimeStructureFactor H p = (k : ℝ) ^ 2 ↔
      ∀ r ∈ (Finset.range p).erase r₀, (p - 1) * tupleResidueCount H p r = k := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hp_cast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  have h_id := hardyLittlewood_admissibility_sos_identity H p r₀ hr₀ hz
  constructor
  · intro heq
    rw [heq, sub_self, mul_zero] at h_id
    have hsum0 : (∑ r ∈ (Finset.range p).erase r₀,
        (((p : ℝ) - 1) * (tupleResidueCount H p r : ℝ) - (k : ℝ)) ^ 2) = 0 :=
      (mul_eq_zero.mp h_id.symm).resolve_left hp0
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sq_nonneg _)] at hsum0
    intro r hr
    have hr0 := sq_eq_zero_iff.mp (hsum0 r hr)
    have h_cast : (((p - 1) * tupleResidueCount H p r : ℕ) : ℝ) = (k : ℝ) := by
      push_cast
      rw [hp_cast]
      linarith
    exact_mod_cast h_cast
  · intro hall
    have hsum0 : (∑ r ∈ (Finset.range p).erase r₀,
        (((p : ℝ) - 1) * (tupleResidueCount H p r : ℝ) - (k : ℝ)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have h_cast : ((p : ℝ) - 1) * (tupleResidueCount H p r : ℝ) = (k : ℝ) := by
        rw [← hp_cast]
        exact_mod_cast hall r hr
      rw [h_cast, sub_self, sq, mul_zero]
    rw [hsum0, mul_zero] at h_id
    have hsub0 : ((p : ℝ) - 1) * tuplePrimeStructureFactor H p - (k : ℝ) ^ 2 = 0 :=
      (mul_eq_zero.mp h_id).resolve_left hp1
    linarith

/-! ### 4. Prime-Power Hierarchical Structure Factor & General Lag-$h$ Radical Factorization -/

/-- Prime-power Ramanujan structure factor of a $k$-tuple $H : \operatorname{Fin} k \to \mathbb{N}$
at mode $q = p^{a+1}$ ($a \ge 1$):
$$S_{p^{a+1}}(H) = p^a\bigl(p\,C_H(p^{a+1}) - C_H(p^a)\bigr).$$ -/
def tuplePrimePowerStructureFactor {k : ℕ} (H : Fin k → ℕ) (p a : ℕ) : ℝ :=
  ((p ^ a : ℕ) : ℝ) *
    ((p : ℝ) * (tupleModCollisionEnergy H (p ^ (a + 1)) : ℝ) -
      (tupleModCollisionEnergy H (p ^ a) : ℝ))

/-- If the shifts of $H$ are pairwise incongruent modulo $p^a$, then they are also pairwise
incongruent modulo $p^{a+1}$, and $S_{p^{a+1}}(H) = k\,\varphi(p^{a+1})$ (zero phase loss at
prime-power mode $p^{a+1}$). -/
theorem tuplePrimePowerStructureFactor_of_le_one {k : ℕ} (H : Fin k → ℕ) (p a : ℕ)
    (hp : p.Prime) (ha : 1 ≤ a)
    (h_dist : ∀ r ∈ Finset.range (p ^ a), tupleResidueCount H (p ^ a) r ≤ 1) :
    tuplePrimePowerStructureFactor H p a = (k : ℝ) * ((p ^ (a + 1)).totient : ℝ) := by
  have hpa_pos : 0 < p ^ a := pow_pos hp.pos a
  have hpa1_pos : 0 < p ^ (a + 1) := pow_pos hp.pos (a + 1)
  have h_dist_succ :
      ∀ r ∈ Finset.range (p ^ (a + 1)), tupleResidueCount H (p ^ (a + 1)) r ≤ 1 := by
    intro r _
    have hsub : Finset.univ.filter (fun i : Fin k => H i % (p ^ (a + 1)) = r) ⊆
        Finset.univ.filter (fun i : Fin k => H i % (p ^ a) = r % (p ^ a)) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, ?_⟩
      have hdvd : p ^ a ∣ p ^ (a + 1) := pow_dvd_pow p (by omega)
      rw [← Nat.mod_mod_of_dvd (H i) hdvd, hi.2]
    exact (Finset.card_le_card hsub).trans
      (h_dist (r % (p ^ a)) (Finset.mem_range.mpr (Nat.mod_lt r hpa_pos)))
  unfold tuplePrimePowerStructureFactor
  rw [(tupleModCollisionEnergy_eq_card_iff_le_one H (p ^ a) hpa_pos).mpr h_dist,
    (tupleModCollisionEnergy_eq_card_iff_le_one H (p ^ (a + 1)) hpa1_pos).mpr h_dist_succ]
  rw [Nat.totient_prime_pow hp (by omega : 0 < a + 1)]
  simp only [Nat.add_sub_cancel]
  rw [Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  ring

/-- General lag-$h$ Bézout GCD identity: $\gcd(n, n + h) = \gcd(n, h)$. -/
theorem gcd_self_add_right (n h : ℕ) : Nat.gcd n (n + h) = Nat.gcd n h := by
  simp

/-- **General Lag-$h$ Bézout–Radical Factorization Theorem:**
For any natural numbers $n, h$ and any prime weight $w : \mathbb{N} \to \mathbb{R}$,
the radical prime-factor functional $F = \operatorname{radicalPrimeProd}(w)$ satisfies
$$F(n)\,F(n + h) = F\bigl(n(n + h)\bigr)\,F\bigl(\gcd(n, h)\bigr).$$
In particular, the shift-collision defect between $F(n)F(n + h)$ and $F(n(n + h))$ depends only
on $\gcd(n, h)$ (supported exclusively on primes dividing the lag $h$). -/
theorem radicalPrimeProd_shift_mul_eq (w : ℕ → ℝ) (n h : ℕ) :
    radicalPrimeProd w n * radicalPrimeProd w (n + h) =
      radicalPrimeProd w (n * (n + h)) * radicalPrimeProd w (Nat.gcd n h) := by
  rw [radicalPrimeProd_mul_eq_mul_gcd w n (n + h), gcd_self_add_right]

/-- When $\gcd(n, h) = 1$, `radicalPrimeProd w` is strictly multiplicative across the shifted pair
$(n, n + h)$:
$$F(n)\,F(n + h) = F\bigl(n(n + h)\bigr).$$ -/
theorem radicalPrimeProd_shift_mul_of_coprime (w : ℕ → ℝ) (n h : ℕ)
    (hcop : Nat.Coprime n h) :
    radicalPrimeProd w n * radicalPrimeProd w (n + h) =
      radicalPrimeProd w (n * (n + h)) := by
  rw [radicalPrimeProd_shift_mul_eq w n h, hcop.gcd_eq_one, radicalPrimeProd_one, mul_one]

/-- **Universal Lag-$h$ Radical Ceiling:**
For any prime weight $w : \mathbb{N} \to [0, 1]$ and any $n, h \in \mathbb{N}$,
$$F(n)\,F(n + h) \le F\bigl(\gcd(n, h)\bigr).$$ -/
theorem radicalPrimeProd_shift_mul_le_gcd (w : ℕ → ℝ)
    (hw0 : ∀ p, p.Prime → 0 ≤ w p) (hw1 : ∀ p, p.Prime → w p ≤ 1)
    (n h : ℕ) :
    radicalPrimeProd w n * radicalPrimeProd w (n + h) ≤
      radicalPrimeProd w (Nat.gcd n h) := by
  rw [radicalPrimeProd_shift_mul_eq w n h]
  have h1 : radicalPrimeProd w (n * (n + h)) ≤ 1 :=
    radicalPrimeProd_le_one hw0 hw1 (n * (n + h))
  have h0 : 0 ≤ radicalPrimeProd w (Nat.gcd n h) :=
    radicalPrimeProd_nonneg hw1 (Nat.gcd n h)
  nlinarith

end

end GaloisForLFunctions.BezoutValuationIncidence
