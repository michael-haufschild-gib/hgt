import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# The primitive-ratio decomposition of an off-diagonal double sum

Every kernel arising from the mean square of a Dirichlet polynomial depends on the pair `(m, n)` only
through the ratio `m/n` — the oscillatory factor of `DirichletDiagonal.integral_normSq_dirPoly_sub_diag`
is `∫_0^T e^{it(log m − log n)}dt`, a function of `log m − log n` alone.  Grouping the off-diagonal pairs
by their primitive ratio therefore turns the off-diagonal into a sum over *coprime* pairs `(m', n')`,
weighted by the multiplicative correlation `∑_d a_{dm'} conj(a_{dn'})` of the coefficients along that
ratio.

This file supplies the index bijection that reduction needs, for an arbitrary summand: writing
`d = gcd(m,n)`, the map `(m, n) ↦ (d, m/d, n/d)` is a bijection from the off-diagonal pairs of `[1,N]²`
onto the triples `(d, m', n')` with `m'`, `n'` coprime and distinct and `dm', dn' ≤ N`, with inverse
`(d, m', n') ↦ (dm', dn')`.

The point of isolating it is that it identifies exactly what a route must estimate.  After the
decomposition the coefficients enter only through their correlations along primitive ratios, so an
estimate of those correlations is the whole remaining content — and by the triage of
`coefficient-free-cap-law.md`, that estimate is where the sign of the coefficients has to be used, since
a majorisation of the correlations through `‖a_n‖` returns to a capped family.
-/

namespace RHTower.Sieve
open Finset

/-- The off-diagonal pairs of `[1,N]²`. -/
def offDiagPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  Finset.filter (fun p => p.1 ≠ p.2) (Finset.Icc 1 N ×ˢ Finset.Icc 1 N)

/-- The primitive triples: a scale `d` and a coprime distinct pair, both multiples inside `[1,N]`. -/
def primitiveTriples (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.filter
    (fun t => Nat.Coprime t.2.1 t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ t.1 * t.2.1 ≤ N ∧ t.1 * t.2.2 ≤ N)
    (Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N)

/-- **The primitive-ratio decomposition.**  Grouping the off-diagonal pairs by `gcd` and primitive
ratio, for an arbitrary summand. -/
theorem sum_offDiagPairs_eq_sum_primitiveTriples {M : Type*} [AddCommMonoid M] (N : ℕ)
    (f : ℕ → ℕ → M) :
    ∑ p ∈ offDiagPairs N, f p.1 p.2
      = ∑ t ∈ primitiveTriples N, f (t.1 * t.2.1) (t.1 * t.2.2) := by
  classical
  refine Finset.sum_nbij' (i := fun p : ℕ × ℕ => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2,
      p.2 / Nat.gcd p.1 p.2))
    (j := fun t : ℕ × ℕ × ℕ => (t.1 * t.2.1, t.1 * t.2.2)) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro p hp
    rw [offDiagPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hm1, hmN⟩, hn1, hnN⟩, hne⟩ := hp
    have hg0 : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ hm1
    have hgm : Nat.gcd p.1 p.2 ∣ p.1 := Nat.gcd_dvd_left _ _
    have hgn : Nat.gcd p.1 p.2 ∣ p.2 := Nat.gcd_dvd_right _ _
    have hmul : Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) = p.1 := Nat.mul_div_cancel' hgm
    have hmul' : Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) = p.2 := Nat.mul_div_cancel' hgn
    have hq1 : 1 ≤ p.1 / Nat.gcd p.1 p.2 := Nat.one_le_div_iff hg0 |>.2 (Nat.le_of_dvd hm1 hgm)
    have hq1' : 1 ≤ p.2 / Nat.gcd p.1 p.2 := Nat.one_le_div_iff hg0 |>.2 (Nat.le_of_dvd hn1 hgn)
    rw [primitiveTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hg0, le_trans (Nat.le_of_dvd hm1 hgm) hmN⟩, ⟨hq1, ?_⟩, hq1', ?_⟩,
      Nat.coprime_div_gcd_div_gcd hg0, ?_, ?_, ?_⟩
    · exact le_trans (Nat.div_le_self _ _) hmN
    · exact le_trans (Nat.div_le_self _ _) hnN
    · intro heq
      have heq' : p.1 / Nat.gcd p.1 p.2 = p.2 / Nat.gcd p.1 p.2 := heq
      apply hne
      calc p.1 = Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) := hmul.symm
        _ = Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) := by rw [heq']
        _ = p.2 := hmul'
    · rw [hmul]; exact hmN
    · rw [hmul']; exact hnN
  · -- backward membership
    intro t ht
    rw [primitiveTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc] at ht
    obtain ⟨⟨⟨hd1, _⟩, ⟨hm1, _⟩, hn1, _⟩, _, hne, hmN, hnN⟩ := ht
    rw [offDiagPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨?_, hmN⟩, ?_, hnN⟩, ?_⟩
    · calc 1 = 1 * 1 := (one_mul 1).symm
        _ ≤ t.1 * t.2.1 := Nat.mul_le_mul hd1 hm1
    · calc 1 = 1 * 1 := (one_mul 1).symm
        _ ≤ t.1 * t.2.2 := Nat.mul_le_mul hd1 hn1
    · intro heq
      exact hne (Nat.eq_of_mul_eq_mul_left hd1 heq)
  · -- left inverse
    intro p hp
    rw [offDiagPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hm1, _⟩, _, _⟩, _⟩ := hp
    have hg0 : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ hm1
    have hmul : Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) = p.1 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hmul' : Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) = p.2 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    exact Prod.ext hmul hmul'
  · -- right inverse
    intro t ht
    rw [primitiveTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc] at ht
    obtain ⟨⟨⟨hd1, _⟩, _, _⟩, hcop, _, _, _⟩ := ht
    have hgcd : Nat.gcd (t.1 * t.2.1) (t.1 * t.2.2) = t.1 := by
      rw [Nat.gcd_mul_left, hcop, mul_one]
    have h1 : t.1 * t.2.1 / t.1 = t.2.1 := Nat.mul_div_cancel_left _ hd1
    have h2 : t.1 * t.2.2 / t.1 = t.2.2 := Nat.mul_div_cancel_left _ hd1
    simp only [hgcd, h1, h2]
  · -- the summand matches
    intro p hp
    rw [offDiagPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hm1, _⟩, _, _⟩, _⟩ := hp
    have hg0 : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ hm1
    have hmul : Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) = p.1 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hmul' : Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) = p.2 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    rw [hmul, hmul']


/-! ### From a `Fin N` off-diagonal double sum to the pairs -/

/-- The off-diagonal of a `Fin N` double sum, as a sum over the product. -/
theorem sum_fin_erase_eq_sum_filter {M : Type*} [AddCommMonoid M] (N : ℕ) (g : Fin N → Fin N → M) :
    ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m, g m n
      = ∑ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 ≠ p.2) Finset.univ, g p.1 p.2 := by
  classical
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n
  simp [Finset.mem_erase, ne_comm]

/-- Shifting the `Fin N` index to `[1, N]`. -/
theorem sum_fin_offDiag_eq_sum_offDiagPairs {M : Type*} [AddCommMonoid M] (N : ℕ)
    (f : ℕ → ℕ → M) :
    ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m, f ((m : ℕ) + 1) ((n : ℕ) + 1)
      = ∑ p ∈ offDiagPairs N, f p.1 p.2 := by
  classical
  rw [sum_fin_erase_eq_sum_filter]
  refine Finset.sum_nbij (fun p : Fin N × Fin N => (((p.1 : ℕ) + 1), ((p.2 : ℕ) + 1)))
    ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [offDiagPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨Nat.le_add_left 1 _, ?_⟩, Nat.le_add_left 1 _, ?_⟩, ?_⟩
    · exact Nat.succ_le_of_lt p.1.isLt
    · exact Nat.succ_le_of_lt p.2.isLt
    · intro heq
      exact hp.2 (Fin.ext (by omega))
  · intro p _ q _ h
    have h1 : (p.1 : ℕ) = (q.1 : ℕ) := by
      have := congrArg Prod.fst h; simp at this; omega
    have h2 : (p.2 : ℕ) = (q.2 : ℕ) := by
      have := congrArg (fun z => (Prod.snd z)) h; simp at this; omega
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · intro q hq
    rw [Finset.mem_coe, offDiagPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_Icc] at hq
    obtain ⟨⟨⟨hm1, hmN⟩, hn1, hnN⟩, hne⟩ := hq
    refine ⟨(⟨q.1 - 1, by omega⟩, ⟨q.2 - 1, by omega⟩), ?_, ?_⟩
    · refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      intro h
      exact hne (by have := congrArg (fun z : Fin N => (z : ℕ)) h; simp at this; omega)
    · exact Prod.ext (by simp; omega) (by simp; omega)
  · intro p _
    rfl

/-! ### Grouping by the primitive ratio -/

/-- Coprime distinct pairs inside `[1, N]²` — the primitive ratios. -/
def primitiveRatioPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  Finset.filter (fun q => Nat.Coprime q.1 q.2 ∧ q.1 ≠ q.2) (Finset.Icc 1 N ×ˢ Finset.Icc 1 N)

/-- The scales available to a given primitive ratio: `d` with `dm, dn ≤ N`. -/
def ratioScales (N m n : ℕ) : Finset ℕ :=
  Finset.filter (fun d => d * m ≤ N ∧ d * n ≤ N) (Finset.Icc 1 N)

/-- The primitive triples, with the pair first. -/
def primitivePairScales (N : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  Finset.filter
    (fun t => Nat.Coprime t.1.1 t.1.2 ∧ t.1.1 ≠ t.1.2 ∧ t.2 * t.1.1 ≤ N ∧ t.2 * t.1.2 ≤ N)
    ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N) ×ˢ Finset.Icc 1 N)

theorem mem_primitivePairScales_iff (N : ℕ) (t : (ℕ × ℕ) × ℕ) :
    t ∈ primitivePairScales N ↔
      t.1 ∈ primitiveRatioPairs N ∧ t.2 ∈ ratioScales N t.1.1 t.1.2 := by
  classical
  rw [primitivePairScales, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
    primitiveRatioPairs, Finset.mem_filter, Finset.mem_product, ratioScales, Finset.mem_filter]
  constructor
  · exact fun ⟨⟨hp, hd⟩, hcop, hne, h1, h2⟩ => ⟨⟨hp, hcop, hne⟩, hd, h1, h2⟩
  · exact fun ⟨⟨hp, hcop, hne⟩, hd, h1, h2⟩ => ⟨⟨hp, hd⟩, hcop, hne, h1, h2⟩

theorem sum_primitiveTriples_eq_sum_primitivePairScales {M : Type*} [AddCommMonoid M] (N : ℕ)
    (F : ℕ → ℕ → ℕ → M) :
    ∑ t ∈ primitiveTriples N, F t.1 t.2.1 t.2.2
      = ∑ t ∈ primitivePairScales N, F t.2 t.1.1 t.1.2 := by
  classical
  refine Finset.sum_nbij (fun t : ℕ × ℕ × ℕ => ((t.2.1, t.2.2), t.1)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro t ht
    rw [primitiveTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at ht
    rw [primitivePairScales, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    exact ⟨⟨⟨ht.1.2.1, ht.1.2.2⟩, ht.1.1⟩, ht.2⟩
  · intro s _ t _ h
    have h1 := congrArg (fun z => (Prod.snd z)) h
    have h2 := congrArg (fun z => (Prod.fst (Prod.fst z))) h
    have h3 := congrArg (fun z => (Prod.snd (Prod.fst z))) h
    simp only at h1 h2 h3
    exact Prod.ext h1 (Prod.ext h2 h3)
  · intro t ht
    rw [Finset.mem_coe, primitivePairScales, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at ht
    refine ⟨(t.2, t.1.1, t.1.2), ?_, rfl⟩
    rw [Finset.mem_coe, primitiveTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product]
    exact ⟨⟨ht.1.2, ht.1.1.1, ht.1.1.2⟩, ht.2⟩

/-- **The off-diagonal in primitive-ratio form.**  A `Fin N`-indexed off-diagonal double sum equals a
sum over primitive ratios of a sum over the available scales. -/
theorem sum_fin_offDiag_eq_sum_ratio {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → ℕ → M) :
    ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m, f ((m : ℕ) + 1) ((n : ℕ) + 1)
      = ∑ q ∈ primitiveRatioPairs N, ∑ d ∈ ratioScales N q.1 q.2, f (d * q.1) (d * q.2) := by
  classical
  rw [sum_fin_offDiag_eq_sum_offDiagPairs, sum_offDiagPairs_eq_sum_primitiveTriples,
    sum_primitiveTriples_eq_sum_primitivePairScales (F := fun d m n => f (d * m) (d * n))]
  exact Finset.sum_finset_product' (primitivePairScales N) (primitiveRatioPairs N)
    (fun q => ratioScales N q.1 q.2) (mem_primitivePairScales_iff N)
    (f := fun (q : ℕ × ℕ) (d : ℕ) => f (d * q.1) (d * q.2))

end RHTower.Sieve
