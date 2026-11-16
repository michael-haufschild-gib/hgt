import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Trace and norm fibers in a quadratic finite-field extension

A trace-and-norm fiber is a Frobenius conjugate pair. For each prescribed
sum and product, the ordered pairs in the base field and the trace-and-norm
fiber in the quadratic field have total cardinality two. A uniform upper
bound and the total cardinality prove this identity without choosing roots
of every quadratic polynomial.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Finset
open scoped Classical
variable {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]
variable (hdegree : Module.finrank K L = 2)

include hdegree in
omit [Fintype K] in
/-- In a quadratic finite-field extension, the embedded trace is the sum with the Frobenius conjugate. -/
theorem finiteField_quadratic_trace (x : L) :
    algebraMap K L (Algebra.trace K L x) = x + x ^ Nat.card K := by
  simpa only [hdegree, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    pow_zero, pow_one, zero_add] using FiniteField.algebraMap_trace_eq_sum_pow K L x

include hdegree in
omit [Fintype K] in
/-- In a quadratic finite-field extension, the embedded norm is the product with the Frobenius conjugate. -/
theorem finiteField_quadratic_norm (x : L) :
    algebraMap K L (Algebra.norm K x) = x * x ^ Nat.card K := by
  simpa only [hdegree, Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty,
    pow_zero, pow_one, one_mul] using FiniteField.algebraMap_norm_eq_prod_pow K L x

include hdegree in
private theorem quadratic_frobenius_sq (x : L) :
    (x ^ Nat.card K) ^ Nat.card K = x := by
  have hcard : Fintype.card L = (Nat.card K) ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := K), hdegree, Nat.card_eq_fintype_card]
  have hx := FiniteField.pow_card x
  rw [hcard] at hx
  rw [← pow_mul]
  simpa only [pow_two] using hx

include hdegree in
private theorem quadratic_trace_base (a : K) :
    Algebra.trace K L (algebraMap K L a) = a + a := by
  have ha : a ^ Nat.card K = a := by
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card a
  apply (algebraMap K L).injective
  rw [finiteField_quadratic_trace hdegree, ← map_pow, ha, map_add]

private theorem first_eq_or_of_sum_prod_eq {F : Type*} [Field F]
    (a b x y : F) (hs : x + y = a + b) (hp : x * y = a * b) : x = a ∨ x = b := by
  have hz : (x - a) * (x - b) = 0 := by
    calc
      (x - a) * (x - b) = x * x - (a + b) * x + a * b := by ring
      _ = 0 := by rw [← hs, ← hp]; ring
  exact (mul_eq_zero.mp hz).imp sub_eq_zero.mp sub_eq_zero.mp

include hdegree in
/-- Equal trace and norm characterize the two Frobenius conjugates in every quadratic finite-field extension. -/
theorem finiteField_quadratic_trace_norm_iff (x y : L) :
    (Algebra.trace K L y = Algebra.trace K L x ∧ Algebra.norm K y = Algebra.norm K x) ↔
      y = x ∨ y = x ^ Nat.card K := by
  constructor
  · rintro ⟨ht, hn⟩
    have hs : y + y ^ Nat.card K = x + x ^ Nat.card K :=
      (finiteField_quadratic_trace hdegree y).symm.trans
        ((congrArg (algebraMap K L) ht).trans (finiteField_quadratic_trace hdegree x))
    have hp : y * y ^ Nat.card K = x * x ^ Nat.card K :=
      (finiteField_quadratic_norm hdegree y).symm.trans
        ((congrArg (algebraMap K L) hn).trans (finiteField_quadratic_norm hdegree x))
    exact first_eq_or_of_sum_prod_eq x (x ^ Nat.card K) y (y ^ Nat.card K) hs hp
  · rintro (rfl | rfl)
    · exact ⟨rfl, rfl⟩
    · constructor
      · apply (algebraMap K L).injective
        rw [finiteField_quadratic_trace hdegree, finiteField_quadratic_trace hdegree, quadratic_frobenius_sq hdegree,
          add_comm]
      · apply (algebraMap K L).injective
        rw [finiteField_quadratic_norm hdegree, finiteField_quadratic_norm hdegree, quadratic_frobenius_sq hdegree,
          mul_comm]

omit [Fintype K] in
private theorem pair_fiber_pair (a b : K) (x : K × K)
    (h : (x.1 + x.2, x.1 * x.2) = (a + b, a * b)) :
    x = (a, b) ∨ x = (b, a) := by
  have hs : x.1 + x.2 = a + b := congrArg Prod.fst h
  have hp : x.1 * x.2 = a * b := congrArg Prod.snd h
  rcases first_eq_or_of_sum_prod_eq a b x.1 x.2 hs hp with hx | hx
  · left
    apply Prod.ext hx
    rw [hx] at hs
    exact add_left_cancel hs
  · right
    apply Prod.ext hx
    rw [hx, add_comm a b] at hs
    exact add_left_cancel hs

include hdegree in
omit [Fintype K] in
private theorem quadratic_fiber_base_root (a b : K) (x : L)
    (ht : Algebra.trace K L x = a + b) (hn : Algebra.norm K x = a * b) :
    x = algebraMap K L a ∨ x = algebraMap K L b := by
  have hs : x + x ^ Nat.card K = algebraMap K L a + algebraMap K L b := by
    rw [← finiteField_quadratic_trace hdegree, ht, map_add]
  have hp : x * x ^ Nat.card K = algebraMap K L a * algebraMap K L b := by
    rw [← finiteField_quadratic_norm hdegree, hn, map_mul]
  exact first_eq_or_of_sum_prod_eq _ _ x (x ^ Nat.card K) hs hp

include hdegree in
private theorem quadratic_fiber_card_le_two (v : K × K) :
    (Finset.univ.filter (fun x : L => (Algebra.trace K L x, Algebra.norm K x) = v)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun x : L => (Algebra.trace K L x, Algebra.norm K x) = v)
  change S.card ≤ 2
  by_contra h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hsub : S ⊆ {x, x ^ Nat.card K} := by
    intro y hy
    have he : (Algebra.trace K L y, Algebra.norm K y) =
        (Algebra.trace K L x, Algebra.norm K x) :=
      (Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp hx).2.symm
    have hyx := (finiteField_quadratic_trace_norm_iff hdegree x y).mp
      ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    rcases hyx with rfl | rfl <;> simp
  have hpair : ({x, x ^ Nat.card K} : Finset L).card ≤ 2 := Finset.card_le_two
  have hb := (Finset.card_le_card hsub).trans hpair
  omega

include hdegree in
private theorem quadratic_combined_fiber_bound (v : K × K) :
    (Finset.univ.filter (fun x : K × K => (x.1 + x.2, x.1 * x.2) = v)).card +
      (Finset.univ.filter (fun x : L => (Algebra.trace K L x, Algebra.norm K x) = v)).card ≤ 2 := by
  classical
  by_cases hex : ∃ x : K × K, (x.1 + x.2, x.1 * x.2) = v
  · obtain ⟨⟨a, b⟩, rfl⟩ := hex
    let S := Finset.univ.filter (fun x : K × K => (x.1 + x.2, x.1 * x.2) = (a + b, a * b))
    let T := Finset.univ.filter (fun x : L => (Algebra.trace K L x, Algebra.norm K x) = (a + b, a * b))
    change S.card + T.card ≤ 2
    by_cases hab : a = b
    · subst b
      have hs : S ⊆ {(a, a)} := by
        intro x hx
        have he := pair_fiber_pair a a x (Finset.mem_filter.mp hx).2
        exact Finset.mem_singleton.mpr (he.elim id id)
      have ht : T ⊆ {algebraMap K L a} := by
        intro x hx
        have he := (Finset.mem_filter.mp hx).2
        have hr := quadratic_fiber_base_root hdegree a a x (congrArg Prod.fst he) (congrArg Prod.snd he)
        exact Finset.mem_singleton.mpr (hr.elim id id)
      have hs' : S.card ≤ 1 := by simpa only [Finset.card_singleton] using Finset.card_le_card hs
      have ht' : T.card ≤ 1 := by simpa only [Finset.card_singleton] using Finset.card_le_card ht
      omega
    · have hs : S ⊆ {(a, b), (b, a)} := by
        intro x hx
        rcases pair_fiber_pair a b x (Finset.mem_filter.mp hx).2 with rfl | rfl <;> simp
      have hp : (a, b) ≠ (b, a) := fun h => hab (congrArg Prod.fst h)
      have hs' : S.card ≤ 2 := by simpa only [Finset.card_pair hp] using Finset.card_le_card hs
      have ht : T = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        have he := (Finset.mem_filter.mp hx).2
        have htr : Algebra.trace K L x = a + b := congrArg Prod.fst he
        rcases quadratic_fiber_base_root hdegree a b x htr (congrArg Prod.snd he) with hxa | hxb
        · rw [hxa, quadratic_trace_base hdegree] at htr
          exact hab (add_left_cancel htr)
        · rw [hxb, quadratic_trace_base hdegree] at htr
          exact hab (add_right_cancel htr).symm
      rw [ht, Finset.card_empty, add_zero]
      exact hs'
  · have hs : (Finset.univ.filter (fun x : K × K => (x.1 + x.2, x.1 * x.2) = v)) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      exact hex ⟨x, (Finset.mem_filter.mp hx).2⟩
    rw [hs, Finset.card_empty, zero_add]
    exact quadratic_fiber_card_le_two hdegree v

include hdegree in
/-- For every prescribed sum and product, base-field ordered pairs and quadratic trace-and-norm solutions have total cardinality two. -/
theorem finiteField_quadratic_trace_norm_fiber_card (t n : K) :
    (Finset.univ.filter (fun x : K × K => x.1 + x.2 = t ∧ x.1 * x.2 = n)).card +
      (Finset.univ.filter (fun x : L => Algebra.trace K L x = t ∧ Algebra.norm K x = n)).card = 2 := by
  classical
  let f : K × K → K × K := fun x => (x.1 + x.2, x.1 * x.2)
  let g : L → K × K := fun x => (Algebra.trace K L x, Algebra.norm K x)
  have hf : (∑ v : K × K, (Finset.univ.filter (fun x : K × K => f x = v)).card) =
      Fintype.card (K × K) := by
    simpa only [Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
        (fun x _ => Finset.mem_univ (f x))).symm
  have hg : (∑ v : K × K, (Finset.univ.filter (fun x : L => g x = v)).card) =
      Fintype.card L := by
    simpa only [Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise (f := g) (s := Finset.univ) (t := Finset.univ)
        (fun x _ => Finset.mem_univ (g x))).symm
  have htotal : (∑ v : K × K,
      ((Finset.univ.filter (fun x : K × K => f x = v)).card +
        (Finset.univ.filter (fun x : L => g x = v)).card)) = ∑ _ : K × K, 2 := by
    rw [Finset.sum_add_distrib, hf, hg,
      Module.card_eq_pow_finrank (K := K) (V := L), hdegree]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
      pow_two, Nat.cast_id]
    omega
  have hpoint := (Finset.sum_eq_sum_iff_of_le
    (fun v (_ : v ∈ (Finset.univ : Finset (K × K))) => quadratic_combined_fiber_bound hdegree v)).mp htotal
  simpa only [f, g, Prod.mk.injEq] using hpoint (t, n) (Finset.mem_univ _)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
