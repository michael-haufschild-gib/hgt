import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Antidiagonal

/-!
# The multiplicative prime Koszul complex stays acyclic in the `∏_p` limit

The `e–h` reciprocity `Σ_{i+j=k} (−1)^i e_i h_j = 0` is proved for **finitely many** variables in
`GaloisForLFunctions.RHTower.EHKoszulDuality`.  The G15 card poses exactly one open question: *does
that acyclicity survive the limit* `∏_{p ≤ P} → ∏_p`?  This file answers it **YES, unconditionally**,
by proving the reciprocity directly in the limit ring itself — no finiteness of the variable set is
used anywhere.

The limit ring `Λ` of the tower of finite-variable symmetric-function rings sits inside the ring
`MvPowerSeries ι R` of formal power series in the **arbitrary** (in particular infinite) variable
family `ι`.  There the elementary and complete homogeneous symmetric functions are the elements

* `esymLimit ι R k` — coefficient `1` on every *squarefree* exponent vector of degree `k`;
* `hsymLimit ι R k` — coefficient `1` on *every* exponent vector of degree `k`,

honest elements of `MvPowerSeries ι R` for infinite `ι` even though they are no longer polynomials.
The reciprocity then reduces, coefficient by coefficient, to the alternating subset sum
`Σ_{T ⊆ supp d} (−1)^{|T|}`, which vanishes precisely because `d ≠ 0`.

## Main results

* `eh_koszul_duality_limit` — `Σ_{i+j=k} (−1)^i e_i h_j = 0` in `MvPowerSeries ι R` for every `k ≥ 1`
  and **every** index type `ι` (in particular the infinite set of all primes): the `∞`-prime
  multiplicative Koszul complex is acyclic;
* `esymGen_mul_hsymGen` — the generating-series form `E(t)·H(t) = 1` in the limit ring;
* `isUnit_hsymGen`, `isUnit_esymGen` — the acyclicity restated: both generating series are units.

Nothing here is conditional on RH: it is the `λ`-ring reciprocity, valid always.
-/

noncomputable section

namespace GaloisForLFunctions

open Finsupp Finset

variable {ι : Type*} {R : Type*} [CommRing R]

/-! ### Squarefree exponent vectors -/

/-- The exponent vector supported on `T` with every exponent equal to `1`. -/
def sqfreeExp (T : Finset ι) : ι →₀ ℕ := ∑ j ∈ T, Finsupp.single j 1

theorem sqfreeExp_apply_of_mem {T : Finset ι} {i : ι} (hi : i ∈ T) : sqfreeExp T i = 1 := by
  classical
  rw [sqfreeExp, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd hi h

theorem sqfreeExp_apply_of_notMem {T : Finset ι} {i : ι} (hi : i ∉ T) : sqfreeExp T i = 0 := by
  classical
  rw [sqfreeExp, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero (fun b hb => ?_)
  have hne : b ≠ i := fun h => hi (h ▸ hb)
  simp [hne]

theorem sqfreeExp_le_one (T : Finset ι) (i : ι) : sqfreeExp T i ≤ 1 := by
  classical
  by_cases h : i ∈ T
  · simp [sqfreeExp_apply_of_mem h]
  · simp [sqfreeExp_apply_of_notMem h]

@[simp] theorem support_sqfreeExp (T : Finset ι) : (sqfreeExp T).support = T := by
  ext i
  simp only [Finsupp.mem_support_iff]
  constructor
  · intro h
    by_contra hi
    exact h (sqfreeExp_apply_of_notMem hi)
  · intro h
    rw [sqfreeExp_apply_of_mem h]
    exact one_ne_zero

@[simp] theorem degree_sqfreeExp (T : Finset ι) : (sqfreeExp T).degree = T.card := by
  rw [sqfreeExp, map_sum]
  simp

/-- A squarefree exponent vector is the indicator of its own support. -/
theorem sqfreeExp_support_eq_self {d : ι →₀ ℕ} (hd : ∀ i, d i ≤ 1) : sqfreeExp d.support = d := by
  ext i
  by_cases h : i ∈ d.support
  · rw [sqfreeExp_apply_of_mem h]
    have h1 := Finsupp.mem_support_iff.mp h
    have h2 := hd i
    omega
  · rw [sqfreeExp_apply_of_notMem h, Finsupp.notMem_support_iff.mp h]

/-- **Squarefreeness is the equality case of `card supp ≤ degree`.**  This is the decidable form of
"every variable occurs at most once" used below to define the elementary symmetric functions. -/
theorem card_support_eq_degree_iff (d : ι →₀ ℕ) :
    d.support.card = d.degree ↔ ∀ i, d i ≤ 1 := by
  have hle : ∀ j ∈ d.support, 1 ≤ d j := fun j hj =>
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have hdeg : d.degree = ∑ j ∈ d.support, d j := Finsupp.degree_apply d
  have hcard : d.support.card = ∑ _j ∈ d.support, 1 := by simp
  constructor
  · intro h i
    by_contra hi
    push Not at hi
    have hmem : i ∈ d.support := Finsupp.mem_support_iff.mpr (by omega)
    have hlt : (∑ _j ∈ d.support, 1) < ∑ j ∈ d.support, d j :=
      Finset.sum_lt_sum hle ⟨i, hmem, hi⟩
    omega
  · intro h
    rw [hdeg, hcard]
    exact Finset.sum_congr rfl (fun j hj => by have := hle j hj; have := h j; omega)

/-! ### The symmetric functions of the limit ring -/

/-- The `k`-th **elementary** symmetric function of the infinite variable family `ι`, as an element
of the limit ring: coefficient `1` on every squarefree exponent vector of degree `k`. -/
def esymLimit (ι : Type*) (R : Type*) [CommRing R] (k : ℕ) : MvPowerSeries ι R :=
  fun d => if d.support.card = k ∧ d.degree = k then (1 : R) else 0

/-- The `k`-th **complete homogeneous** symmetric function of the infinite variable family `ι`:
coefficient `1` on every exponent vector of degree `k`. -/
def hsymLimit (ι : Type*) (R : Type*) [CommRing R] (k : ℕ) : MvPowerSeries ι R :=
  fun d => if d.degree = k then (1 : R) else 0

@[simp] theorem coeff_esymLimit (k : ℕ) (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d (esymLimit ι R k)
      = if d.support.card = k ∧ d.degree = k then (1 : R) else 0 := rfl

@[simp] theorem coeff_hsymLimit (k : ℕ) (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d (hsymLimit ι R k) = if d.degree = k then (1 : R) else 0 := rfl

@[simp] theorem esymLimit_zero : esymLimit ι R 0 = 1 := by
  classical
  ext d
  rw [coeff_esymLimit, MvPowerSeries.coeff_one]
  by_cases h : d = 0
  · simp [h]
  · rw [if_neg h, if_neg]
    rintro ⟨-, h2⟩
    exact h ((Finsupp.degree_eq_zero_iff d).mp h2)

@[simp] theorem hsymLimit_zero : hsymLimit ι R 0 = 1 := by
  classical
  ext d
  rw [coeff_hsymLimit, MvPowerSeries.coeff_one]
  by_cases h : d = 0
  · simp [h]
  · rw [if_neg h, if_neg]
    intro h2
    exact h ((Finsupp.degree_eq_zero_iff d).mp h2)

/-- Both families are homogeneous: a nonzero coefficient forces the exponent vector to have the
prescribed degree. -/
theorem degree_eq_of_coeff_hsymLimit_ne_zero {k : ℕ} {d : ι →₀ ℕ}
    (h : MvPowerSeries.coeff d (hsymLimit ι R k) ≠ 0) : d.degree = k := by
  by_contra hd
  exact h (by rw [coeff_hsymLimit, if_neg hd])

theorem degree_eq_of_coeff_esymLimit_ne_zero {k : ℕ} {d : ι →₀ ℕ}
    (h : MvPowerSeries.coeff d (esymLimit ι R k) ≠ 0) : d.degree = k := by
  by_contra hd
  refine h ?_
  rw [coeff_esymLimit, if_neg]
  rintro ⟨-, h2⟩
  exact hd h2

/-! ### The alternating subset sum -/

section DecEq

variable [DecidableEq ι]

/-- **The combinatorial heart.**  Splitting a nonzero exponent vector `n` as `a + b` with `a`
squarefree, weighted by `(−1)^{deg a}`, gives zero: such `a` are exactly the indicators of subsets
of `supp n`, and `Σ_{T ⊆ S} (−1)^{|T|} = 0` for `S ≠ ∅`. -/
theorem sum_antidiagonal_sqfree_sign {n : ι →₀ ℕ} (hn : n ≠ 0) :
    ∑ q ∈ Finset.antidiagonal n,
      (if q.1.support.card = q.1.degree then (-1 : R) ^ q.1.degree else 0) = 0 := by
  classical
  rw [← Finset.sum_filter]
  have key : ∑ T ∈ n.support.powerset, (-1 : R) ^ T.card
      = ∑ q ∈ (Finset.antidiagonal n).filter (fun q => q.1.support.card = q.1.degree),
          ((-1 : R) ^ q.1.degree) := by
    refine Finset.sum_nbij' (fun T => (sqfreeExp T, n - sqfreeExp T)) (fun q => q.1.support)
      ?_ ?_ ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_powerset] at hT
      have hle : ∀ i, sqfreeExp T i ≤ n i := by
        intro i
        by_cases hi : i ∈ T
        · rw [sqfreeExp_apply_of_mem hi]
          exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (hT hi))
        · rw [sqfreeExp_apply_of_notMem hi]
          exact Nat.zero_le _
      refine Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr ?_, ?_⟩
      · dsimp only
        ext i
        rw [Finsupp.add_apply, Finsupp.tsub_apply]
        have := hle i
        omega
      · simp
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_antidiagonal] at hq
      rw [Finset.mem_powerset]
      intro i hi
      rw [Finsupp.mem_support_iff] at hi ⊢
      have hsum : q.1 i + q.2 i = n i := by
        have := congrArg (fun f => f i) hq.1
        simpa using this
      omega
    · intro T _
      simp
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_antidiagonal] at hq
      have hsq : ∀ i, q.1 i ≤ 1 := (card_support_eq_degree_iff q.1).mp hq.2
      have h1 : sqfreeExp q.1.support = q.1 := sqfreeExp_support_eq_self hsq
      refine Prod.ext h1 ?_
      simp only
      rw [h1]
      ext i
      rw [Finsupp.tsub_apply]
      have hsum : q.1 i + q.2 i = n i := by
        have := congrArg (fun f => f i) hq.1
        simpa using this
      omega
    · intro T _
      rw [degree_sqfreeExp]
  rw [← key]
  have hne : n.support.Nonempty := Finsupp.support_nonempty_iff.mpr hn
  have hz : ∑ T ∈ n.support.powerset, (-1 : ℤ) ^ T.card = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hne
  calc ∑ T ∈ n.support.powerset, (-1 : R) ^ T.card
      = ((∑ T ∈ n.support.powerset, (-1 : ℤ) ^ T.card : ℤ) : R) := by push_cast; ring
    _ = 0 := by rw [hz]; simp

/-- The coefficientwise form of the alternating `e–h` sum. -/
theorem coeff_ehAlternating (k : ℕ) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n
        (∑ p ∈ Finset.antidiagonal k, (-1 : R) ^ p.1 • (esymLimit ι R p.1 * hsymLimit ι R p.2))
      = if n.degree = k then
          (∑ q ∈ Finset.antidiagonal n,
            (if q.1.support.card = q.1.degree then (-1 : R) ^ q.1.degree else 0))
        else 0 := by
  classical
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, MvPowerSeries.coeff_mul, coeff_esymLimit, coeff_hsymLimit,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  by_cases hdeg : n.degree = k
  · rw [if_pos hdeg]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [Finset.mem_antidiagonal] at hq
    have hqd : q.1.degree + q.2.degree = k := by
      rw [← hdeg, ← hq]
      exact (map_add Finsupp.degree q.1 q.2).symm
    rw [Finset.sum_eq_single (q.1.degree, q.2.degree)]
    · by_cases hs : q.1.support.card = q.1.degree
      · rw [if_pos hs, if_pos ⟨hs, rfl⟩, if_pos rfl]
        ring
      · rw [if_neg hs, if_neg (fun h => hs h.1), if_pos rfl]
        ring
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      by_cases hA : q.1.support.card = p.1 ∧ q.1.degree = p.1
      · by_cases hB : q.2.degree = p.2
        · exact absurd (Prod.ext hA.2.symm hB.symm) hne
        · rw [if_neg hB]; ring
      · rw [if_neg hA]; ring
    · intro h
      exact absurd (Finset.mem_antidiagonal.mpr hqd) h
  · rw [if_neg hdeg]
    refine Finset.sum_eq_zero (fun q hq => ?_)
    rw [Finset.mem_antidiagonal] at hq
    refine Finset.sum_eq_zero (fun p hp => ?_)
    rw [Finset.mem_antidiagonal] at hp
    by_cases hA : q.1.support.card = p.1 ∧ q.1.degree = p.1
    · by_cases hB : q.2.degree = p.2
      · exact absurd (by rw [← hq, map_add, hA.2, hB, hp]) hdeg
      · rw [if_neg hB]; ring
    · rw [if_neg hA]; ring

end DecEq

/-- **The `e–h` Koszul reciprocity in the `∏_p` limit — unconditional.**  For every `k ≥ 1` and
every index type `ι` (in particular the *infinite* set of all primes),
`Σ_{i+j=k} (−1)^i e_i h_j = 0` holds in the limit ring.  So the finite acyclicity of the
multiplicative Koszul complex survives the limit `∏_{p ≤ P} → ∏_p`: no homology condenses. -/
theorem eh_koszul_duality_limit (k : ℕ) (hk : 1 ≤ k) :
    (∑ p ∈ Finset.antidiagonal k, (-1 : R) ^ p.1 • (esymLimit ι R p.1 * hsymLimit ι R p.2))
      = 0 := by
  classical
  ext n
  rw [coeff_ehAlternating, MvPowerSeries.coeff_zero]
  split_ifs with h
  · refine sum_antidiagonal_sqfree_sign (fun hn0 => ?_)
    rw [hn0, map_zero] at h
    omega
  · rfl

/-! ### The generating-series form -/

/-- `E(t) = Σ_k (−1)^k e_k t^k` over the infinite variable family. -/
def esymGen (ι : Type*) (R : Type*) [CommRing R] : PowerSeries (MvPowerSeries ι R) :=
  PowerSeries.mk fun k => (-1 : R) ^ k • esymLimit ι R k

/-- `H(t) = Σ_k h_k t^k` over the infinite variable family. -/
def hsymGen (ι : Type*) (R : Type*) [CommRing R] : PowerSeries (MvPowerSeries ι R) :=
  PowerSeries.mk fun k => hsymLimit ι R k

/-- **`E(t)·H(t) = 1` in the limit ring.**  This is the card's `H(t)E(−t) = 1` in `Λ`, proved
directly for an arbitrary — in particular infinite — prime family. -/
theorem esymGen_mul_hsymGen : esymGen ι R * hsymGen ι R = 1 := by
  refine PowerSeries.ext fun k => ?_
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one]
  simp only [esymGen, hsymGen, PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [if_pos rfl]
    have h0 : Finset.antidiagonal (0 : ℕ) = {((0 : ℕ), (0 : ℕ))} := rfl
    rw [h0]
    simp
  · rw [if_neg (by omega)]
    rw [← eh_koszul_duality_limit (ι := ι) (R := R) k hk]
    exact Finset.sum_congr rfl (fun p _ => smul_mul_assoc _ _ _)

/-- **Acyclicity, restated.**  `H(t)` is a unit in the power-series ring over the limit ring. -/
theorem isUnit_hsymGen : IsUnit (hsymGen ι R) :=
  ⟨⟨hsymGen ι R, esymGen ι R, by rw [mul_comm]; exact esymGen_mul_hsymGen,
    esymGen_mul_hsymGen⟩, rfl⟩

/-- `E(t)` is a unit as well. -/
theorem isUnit_esymGen : IsUnit (esymGen ι R) :=
  ⟨⟨esymGen ι R, hsymGen ι R, esymGen_mul_hsymGen, by rw [mul_comm]; exact esymGen_mul_hsymGen⟩,
    rfl⟩

end GaloisForLFunctions
