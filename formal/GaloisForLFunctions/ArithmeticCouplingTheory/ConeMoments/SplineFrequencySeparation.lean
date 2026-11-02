import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.QuantitativeConeCutoffs
import GaloisForLFunctions.HTGeometry.TranscendentalExpOne
import GaloisForLFunctions.HTGeometry.RittMonomialScaling

/-!
# Integer shifts of positive prime-logarithm frequencies

Two distinct prime logarithms and the integer frequency have no nontrivial
integer relation: exponentiation and transcendence of `e` remove a nonzero
integer shift, while prime-logarithm separation removes the homogeneous case.

The shifts from `-8` to `8` in the cubic-spline numerator consequently stay
uniformly away from zero on the whole positive cone. Only a fixed finite
window of cone frequencies can approach these shifts.
-/

open GaloisForLFunctions.ArithmeticOfSquareRootPrecision
open Finset

noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

private lemma real_exp_integer_mul (r : ℤ) (x : ℝ) :
    Real.exp ((r : ℝ)*x)=(Real.exp x)^r := by
  cases r with
  | ofNat k => rw [Int.ofNat_eq_natCast, Int.cast_natCast, zpow_natCast, Real.exp_nat_mul]
  | negSucc k =>
    rw [Int.cast_negSucc, zpow_negSucc, neg_mul, Real.exp_neg]
    congr 1
    simpa only [Nat.cast_add, Nat.cast_one] using
      (show Real.exp (((k+1 : ℕ) : ℝ)*x)=(Real.exp x)^(k+1) by rw [Real.exp_nat_mul])

/-- Integer shifts cannot create a relation between two prime logarithms. -/
theorem prime_log_integer_relation {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (m n r : ℤ)
    (h : (m : ℝ)*Real.log p+(n : ℝ)*Real.log q+(r : ℝ)=0) :
    m=0 ∧ n=0 ∧ r=0 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hr : r=0 := by
    by_contra hr
    have he : (Real.exp 1)^(-r)=algebraMap ℚ ℝ ((p : ℚ)^m*(q : ℚ)^n) := by
      rw [← real_exp_integer_mul, mul_one]
      have hh : ((-r : ℤ) : ℝ)=(m : ℝ)*Real.log p+(n : ℝ)*Real.log q := by
        push_cast
        linarith only [h]
      rw [hh, Real.exp_add, real_exp_integer_mul, real_exp_integer_mul,
        Real.exp_log hpR, Real.exp_log hqR]
      push_cast
      rfl
    exact HTGeometry.zpow_notMem_of_transcendental HTGeometry.transcendental_exp_one
      (neg_ne_zero.mpr hr) he
  subst r
  simp only [Int.cast_zero, add_zero] at h
  have hmn : m=0 ∧ n=0 := by
    by_contra hnot
    have hne : n ≠ 0 ∨ -m ≠ 0 := by omega
    obtain ⟨c, C, hc, hC, hb⟩ := exists_baker_separation hp hq hpq
    have hb' := hb n (-m) hne
    have he : (n : ℝ)*Real.log q-((-m : ℤ) : ℝ)*Real.log p=0 := by
      push_cast
      linarith only [h]
    rw [he, abs_zero] at hb'
    have hpw : 0 < c*(2+(|(n : ℝ)|+|((-m : ℤ) : ℝ)|))^(-C) := by positivity
    exact (not_le_of_gt hpw) hb'
  exact ⟨hmn.1, hmn.2, rfl⟩

lemma positiveCone_add_int_ne_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (t : PositiveCone (Real.log p) (Real.log q)) (r : ℤ) :
    t.val+(r : ℝ) ≠ 0 := by
  intro h
  obtain ⟨⟨m,n⟩, he⟩ := t.property.2
  have hrel := prime_log_integer_relation hp hq hpq (m : ℤ) (n : ℤ) r (by
    rw [← he] at h
    simpa only [coneFrequency, Int.cast_natCast] using h)
  have hm : m=0 := by exact_mod_cast hrel.1
  have hn : n=0 := by exact_mod_cast hrel.2.1
  have ht0 : t.val=0 := by simpa only [coneFrequency, hm, hn, Nat.cast_zero, zero_mul, zero_add] using he.symm
  exact (ne_of_gt t.property.1) ht0

/-- The finitely many shifts in the spline numerator stay uniformly away from zero
on the whole positive cone. Only bounded cone times can approach a fixed shift. -/
theorem exists_cone_spline_shift_gap {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : PositiveCone (Real.log p) (Real.log q),
      ∀ r : ℤ, |(r : ℝ)| ≤ 8 → η ≤ |t.val+(r : ℝ)| := by
  classical
  have ha : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  obtain ⟨N, hN⟩ := exists_nat_gt (9/Real.log p)
  obtain ⟨M, hM⟩ := exists_nat_gt (9/Real.log q)
  let S := coneSquare (Real.log p) (Real.log q) (max N M)
  have hsmall : ∀ t : PositiveCone (Real.log p) (Real.log q), t.val ≤ 9 → t.val ∈ S := by
    intro t ht
    obtain ⟨⟨m,n⟩, he⟩ := t.property.2
    have hma : (m : ℝ)*Real.log p ≤ t.val := by
      rw [← he]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hb.le)
    have hnb : (n : ℝ)*Real.log q ≤ t.val := by
      rw [← he]
      exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg m) ha.le)
    have hmR : (m : ℝ) ≤ N := ((le_div_iff₀ ha).mpr (hma.trans ht)).trans hN.le
    have hnR : (n : ℝ) ≤ M := ((le_div_iff₀ hb).mpr (hnb.trans ht)).trans hM.le
    have hm : m ≤ N := by exact_mod_cast hmR
    have hn : n ≤ M := by exact_mod_cast hnR
    exact (mem_coneSquare_iff _ _ _ _).mpr
      ⟨ne_of_gt t.property.1, m, n, hm.trans (le_max_left _ _), hn.trans (le_max_right _ _), he⟩
  let T : Finset ℝ := insert 1 ((S ×ˢ Icc (-8 : ℤ) 8).image fun v => |v.1+(v.2 : ℝ)|)
  have hTne : T.Nonempty := ⟨1, mem_insert_self _ _⟩
  have hTpos : ∀ u ∈ T, 0 < u := by
    intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · norm_num
    obtain ⟨⟨t,r⟩, htr, rfl⟩ := mem_image.mp hu
    have ht := (mem_product.mp htr).1
    obtain ⟨_, m, n, _, _, he⟩ := (mem_coneSquare_iff _ _ _ _).mp ht
    let t' : PositiveCone (Real.log p) (Real.log q) :=
      ⟨t, coneSquare_positive ha hb ht, ⟨(m,n), he⟩⟩
    exact abs_pos.mpr (positiveCone_add_int_ne_zero hp hq hpq t' r)
  refine ⟨T.min' hTne, hTpos _ (min'_mem _ _), ?_⟩
  intro t r hr
  rcases le_or_gt t.val 9 with ht | ht
  · apply min'_le
    apply mem_insert_of_mem
    apply mem_image.mpr
    refine ⟨(t.val,r), mem_product.mpr ⟨hsmall t ht, ?_⟩, rfl⟩
    have hrZ : |r| ≤ (8 : ℤ) := by exact_mod_cast hr
    exact mem_Icc.mpr (abs_le.mp hrZ)
  · have h1 : T.min' hTne ≤ 1 := min'_le _ _ (mem_insert_self _ _)
    have hrlo := (abs_le.mp hr).1
    exact h1.trans ((show (1 : ℝ) ≤ t.val+(r : ℝ) by linarith only [ht, hrlo]).trans (le_abs_self _))

#print axioms prime_log_integer_relation
#print axioms exists_cone_spline_shift_gap
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
