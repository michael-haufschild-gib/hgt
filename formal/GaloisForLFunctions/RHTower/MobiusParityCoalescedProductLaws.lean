import GaloisForLFunctions.RHTower.MobiusParityCoalescedFullMassCube
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The product laws of the parity-coalesced full-mass cube

Every quantitative statement of the coalesced relation is a product over the groups of one
per-group square-root law.  Because square roots multiply, the group products collapse:

* the mixed Gibbs cost of the cube is `a·∏(q_G - U_G) ≤ √(a n T)·Λ^g`, since
  `∏U_G = n/a` and `∏t_G = T`;
* the row supply is `∏N_G ≥ √(n/(aT))/∏c_G`, the half-density row degree;
* the physical co-degree is `∏(√(q_G t_G)Λ + 1) ≤ (2Λ)^g √(vT/a)`, the matching half-density
  column bound.

All three come from the single identity `∏√(f_G g_G) = √(∏f_G · ∏g_G)`: the source products
associate exactly and the reservoir product enters only through `√T`.
-/

namespace RHTower

open Finset

/-- **Square roots multiply over the groups.** -/
theorem prod_sqrt_mul {ι : Type*} (G : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ G, 0 ≤ f i) (hg : ∀ i ∈ G, 0 ≤ g i) :
    ∏ i ∈ G, Real.sqrt (f i * g i) = Real.sqrt ((∏ i ∈ G, f i) * ∏ i ∈ G, g i) := by
  have hprod : ∀ i ∈ G, (0 : ℝ) ≤ f i * g i := fun i hi => mul_nonneg (hf i hi) (hg i hi)
  rw [← Real.sqrt_prod G hprod, Finset.prod_mul_distrib]

/-- **(30) The mixed Gibbs cost of the coalesced cube.**  Per-group square-root gaps multiply into
one square-root cost in which the reservoir product enters only through `√T`. -/
theorem mixed_gibbs_cost_le {ι : Type*} (G : Finset ι) (U t q : ι → ℝ) (Λ a n T : ℝ)
    (hU : ∀ i ∈ G, 0 ≤ U i) (ht : ∀ i ∈ G, 0 ≤ t i) (ha : 0 < a)
    (hgap : ∀ i ∈ G, 0 ≤ q i - U i)
    (hgap' : ∀ i ∈ G, q i - U i ≤ Real.sqrt (U i * t i) * Λ)
    (hprodU : ∏ i ∈ G, U i = n / a) (hprodT : ∏ i ∈ G, t i = T) :
    a * ∏ i ∈ G, (q i - U i) ≤ Real.sqrt (a * n * T) * Λ ^ G.card := by
  have hstep : ∏ i ∈ G, (q i - U i) ≤ ∏ i ∈ G, Real.sqrt (U i * t i) * Λ :=
    Finset.prod_le_prod hgap hgap'
  have hexp : ∏ i ∈ G, Real.sqrt (U i * t i) * Λ
      = Real.sqrt (n / a * T) * Λ ^ G.card := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, prod_sqrt_mul G U t hU ht, hprodU, hprodT]
  rw [hexp] at hstep
  have hnT : Real.sqrt (n / a * T) = Real.sqrt (a * n * T) / a := by
    have hval : n / a * T = a * n * T / a ^ 2 := by
      field_simp
    rw [hval, Real.sqrt_div' (a * n * T) (by positivity), Real.sqrt_sq ha.le]
  rw [hnT] at hstep
  have hmul := mul_le_mul_of_nonneg_left hstep ha.le
  refine le_trans hmul (le_of_eq ?_)
  field_simp

/-- **(32) The full-mass row supply.**  Per-group square-root token counts multiply into the
half-density row degree `√(n/(aT))`. -/
theorem row_supply_ge {ι : Type*} (G : Finset ι) (N y c : ι → ℝ) (n a T : ℝ)
    (hy : ∀ i ∈ G, 0 ≤ y i) (hc : ∀ i ∈ G, 0 < c i)
    (hN : ∀ i ∈ G, Real.sqrt (y i) / c i ≤ N i)
    (hprod : ∏ i ∈ G, y i = n / (a * T)) :
    Real.sqrt (n / (a * T)) / ∏ i ∈ G, c i ≤ ∏ i ∈ G, N i := by
  have hnn : ∀ i ∈ G, (0 : ℝ) ≤ Real.sqrt (y i) / c i := fun i hi =>
    div_nonneg (Real.sqrt_nonneg _) (hc i hi).le
  have hstep : ∏ i ∈ G, Real.sqrt (y i) / c i ≤ ∏ i ∈ G, N i :=
    Finset.prod_le_prod hnn hN
  refine le_trans (le_of_eq ?_) hstep
  rw [Finset.prod_div_distrib, ← Real.sqrt_prod G hy, hprod]

/-- **(37) The physical co-degree.**  Per-group inverse-interval counts multiply into the matching
half-density column bound `(2Λ)^g √(vT/a)`. -/
theorem codegree_le {ι : Type*} (G : Finset ι) (q t : ι → ℝ) (Λ v a T : ℝ)
    (hq : ∀ i ∈ G, 0 ≤ q i) (ht : ∀ i ∈ G, 0 ≤ t i)
    (hbig : ∀ i ∈ G, 1 ≤ Real.sqrt (q i * t i) * Λ)
    (hprodq : ∏ i ∈ G, q i = v / a) (hprodT : ∏ i ∈ G, t i = T) :
    ∏ i ∈ G, (Real.sqrt (q i * t i) * Λ + 1)
      ≤ (2 * Λ) ^ G.card * Real.sqrt (v * T / a) := by
  have hnn : ∀ i ∈ G, (0 : ℝ) ≤ Real.sqrt (q i * t i) * Λ + 1 := fun i hi => by
    have := hbig i hi
    linarith
  have hle : ∀ i ∈ G, Real.sqrt (q i * t i) * Λ + 1 ≤ 2 * (Real.sqrt (q i * t i) * Λ) :=
    fun i hi => by linarith [hbig i hi]
  have hstep : ∏ i ∈ G, (Real.sqrt (q i * t i) * Λ + 1)
      ≤ ∏ i ∈ G, 2 * (Real.sqrt (q i * t i) * Λ) := Finset.prod_le_prod hnn hle
  refine le_trans hstep (le_of_eq ?_)
  have hexp : ∏ i ∈ G, 2 * (Real.sqrt (q i * t i) * Λ)
      = 2 ^ G.card * (Real.sqrt (v / a * T) * Λ ^ G.card) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_mul_distrib, Finset.prod_const,
      prod_sqrt_mul G q t hq ht, hprodq, hprodT]
  rw [hexp]
  have hval : Real.sqrt (v / a * T) = Real.sqrt (v * T / a) := by
    congr 1
    ring
  rw [hval, mul_pow]
  ring

/-! ## The robust token range -/

/-- **(15)/(17) The robust token range.**  A group whose source lower bound exceeds its reservoir
bound by a factor `M` has `y_G = U_G/t_G ≥ M`.  The three cases of the card are the instances
`M = Y` (singleton, shift `+1`), `M = YZ²` (singleton, shift `-1`), and `M = Y²` (coalesced group,
shift `-1`), each with `E = Z^{b_G}`. -/
theorem token_range_ge {M U t E : ℝ} (hM : 0 ≤ M) (hU : M * E ≤ U) (ht : 0 < t) (htle : t ≤ E) :
    M ≤ U / t := by
  rw [le_div_iff₀ ht]
  calc M * t ≤ M * E := mul_le_mul_of_nonneg_left htle hM
    _ ≤ U := hU

/-! ## The seam at the full terminal -/

/-- The number of prime factors above the seam. -/
noncomputable def seamCount (z : ℝ) (m : ℕ) : ℕ := by
  classical
  exact (m.primeFactors.filter fun p : ℕ => z < (p : ℝ)).card

theorem seamCount_eq_zero_iff {z : ℝ} {m : ℕ} :
    seamCount z m = 0 ↔ ∀ p ∈ m.primeFactors, (p : ℝ) ≤ z := by
  classical
  rw [seamCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h p hp
    exact not_lt.1 (h hp)
  · intro h p hp
    exact not_lt.2 (h p hp)

theorem seamCount_mul_eq_zero {z : ℝ} {b c : ℕ} (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : seamCount z b = 0) (h2 : seamCount z c = 0) : seamCount z (b * c) = 0 := by
  classical
  rw [seamCount_eq_zero_iff] at h1 h2 ⊢
  intro p hp
  rw [Nat.primeFactors_mul hb hc, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact h1 p hp
  · exact h2 p hp

theorem seamCount_prod_eq_zero {z : ℝ} {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hne : ∀ i ∈ s, f i ≠ 0) (h : ∀ i ∈ s, seamCount z (f i) = 0) :
    seamCount z (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, seamCount_eq_zero_iff]
      intro p hp
      simp at hp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      have hfi : f i ≠ 0 := hne i (Finset.mem_insert_self i s)
      have hprod : (∏ j ∈ s, f j) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j hj => hne j (Finset.mem_insert_of_mem hj)
      refine seamCount_mul_eq_zero hfi hprod (h i (Finset.mem_insert_self i s)) ?_
      exact ih (fun j hj => hne j (Finset.mem_insert_of_mem hj))
        (fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- **(40) The seam is automatic at the full terminal.**  Every replacement coordinate and the
inactive product have all their prime factors below the seam, so the full terminal carries no
prime above it. -/
theorem seamCount_fullTerminal_eq_zero {z : ℝ} {ι : Type*} (s : Finset ι) (q : ι → ℕ) (a : ℕ)
    (ha : a ≠ 0) (hane : seamCount z a = 0)
    (hne : ∀ i ∈ s, q i ≠ 0) (h : ∀ i ∈ s, seamCount z (q i) = 0) :
    seamCount z (a * ∏ i ∈ s, q i) = 0 := by
  classical
  have hprod : (∏ i ∈ s, q i) ≠ 0 := Finset.prod_ne_zero_iff.2 hne
  exact seamCount_mul_eq_zero ha hprod hane (seamCount_prod_eq_zero s q hne h)

/-- **Coprime additivity of the seam count.** -/
theorem seamCount_mul_of_coprime {z : ℝ} {b c : ℕ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hcop : Nat.Coprime b c) : seamCount z (b * c) = seamCount z b + seamCount z c := by
  classical
  have hdisj : Disjoint b.primeFactors c.primeFactors := Nat.Coprime.disjoint_primeFactors hcop
  have hunion : (b * c).primeFactors = b.primeFactors ∪ c.primeFactors :=
    Nat.primeFactors_mul hb hc
  simp only [seamCount, hunion]
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter hdisj

/-- **(53) The sector law.**  A corner that replaces the distinguished coordinate carries no prime
above the seam; a corner that keeps it carries exactly the seam count of that coordinate. -/
theorem seamCount_corner {z : ℝ} {b c : ℕ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hcop : Nat.Coprime b c) (hbz : seamCount z b = 0) :
    seamCount z (b * c) = seamCount z c := by
  rw [seamCount_mul_of_coprime hb hc hcop, hbz, zero_add]

/-! ## Parity of a unit breadth shift -/

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius


/-- **A unit breadth shift reverses the Möbius sign.**  A squarefree replacement whose number of
prime factors exceeds the source's by one has the opposite sign. -/
theorem moebius_eq_neg_of_cardFactors_succ {u q : ℕ} (hu : Squarefree u) (hq : Squarefree q)
    (h : cardFactors q = cardFactors u + 1) : (μ q : ℤ) = -(μ u : ℤ) := by
  rw [moebius_apply_of_squarefree hu, moebius_apply_of_squarefree hq, h, pow_succ]
  ring

/-- The same statement with the roles reversed: a replacement one shorter also reverses sign. -/
theorem moebius_eq_neg_of_cardFactors_pred {u q : ℕ} (hu : Squarefree u) (hq : Squarefree q)
    (h : cardFactors u = cardFactors q + 1) : (μ q : ℤ) = -(μ u : ℤ) := by
  rw [moebius_apply_of_squarefree hu, moebius_apply_of_squarefree hq, h, pow_succ]
  ring

end RHTower
