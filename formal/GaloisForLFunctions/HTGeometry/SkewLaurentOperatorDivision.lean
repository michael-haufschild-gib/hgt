import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# A concrete skew Laurent division ring

For a field `K` and automorphism `σ`, realize `K((u;σ))` inside ordinary Hahn
series with additive-endomorphism coefficients. A degree-`n` coefficient is
the operator `x ↦ a * σ^n(x)`. Composition gives the skew product exactly.

Formal geometric inversion is proved for noncommutative coefficients, and
coefficientwise closure keeps every constructed inverse in the skew subring.
Thus the division-ring instance is constructed, rather than assumed.

An additive translation coordinate gives an explicit unit commutator. Every
cyclic trace then kills the unit. This identifies why a normalized rotation
trace cannot extend across a full meromorphic additive-coordinate field.

This is algebraic infrastructure for IRK trace integrality. It supplies no Xi
projective class, canonical C*-trace, or Riemann-hypothesis proof.
-/

open HahnSeries
open scoped Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Geometric

variable {R : Type*} [Ring R]

private theorem power_support_lower_bound (x : HahnSeries ℤ R)
    (hx : 0 < x.orderTop) (n : ℕ) {i : ℤ} (hi : (x ^ n).coeff i ≠ 0) :
    (n : ℤ) ≤ i := by
  induction n generalizing i with
  | zero =>
    have : i = 0 := by simpa using (show i = 0 ∧ (1 : R) ≠ 0 from by simpa using hi).1
    simp [this]
  | succ n ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := HahnSeries.support_mul_subset hi
    have ha' := ih ha
    have hb' : 0 < b := by
      have := HahnSeries.orderTop_le_of_coeff_ne_zero hb
      exact_mod_cast lt_of_lt_of_le hx this
    change ((n + 1 : ℕ) : ℤ) ≤ a + b
    omega

/-- Formal geometric powers for noncommutative Laurent coefficients. -/
def noncommLaurentPowers (x : HahnSeries ℤ R) (hx : 0 < x.orderTop) :
    HahnSeries.SummableFamily ℤ R ℕ where
  toFun n := x ^ n
  isPWO_iUnion_support' :=
    HahnSeries.SummableFamily.isPWO_iUnion_support_powers
      (HahnSeries.zero_le_orderTop_iff.mp hx.le)
  finite_co_support' i := by
    apply (Set.finite_Iic i.toNat).subset
    intro n hn
    have hn' := power_support_lower_bound x hx n hn
    exact Int.ofNat_le.mp (hn'.trans (Int.self_le_toNat i))

@[simp] theorem noncommLaurentPowers_apply (x : HahnSeries ℤ R)
    (hx : 0 < x.orderTop) (n : ℕ) : noncommLaurentPowers x hx n = x ^ n := rfl

private theorem noncommLaurentPowers_shift (x : HahnSeries ℤ R)
    (hx : 0 < x.orderTop) :
    (x • noncommLaurentPowers x hx).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      noncommLaurentPowers x hx -
        HahnSeries.SummableFamily.ofFinsupp (Finsupp.single 0 1) := by
  apply HahnSeries.SummableFamily.ext
  rintro (_ | n)
  · simp
  · simp [HahnSeries.SummableFamily.embDomain_apply,
      HahnSeries.of_symm_smul_of_eq_mul, pow_succ', -smul_eq_mul]

/-- The geometric series is a right inverse without commutative coefficients. -/
theorem one_sub_mul_noncommLaurentPowers (x : HahnSeries ℤ R)
    (hx : 0 < x.orderTop) :
    (1 - x) * (noncommLaurentPowers x hx).hsum = 1 := by
  rw [← HahnSeries.SummableFamily.hsum_smul, sub_smul 1 x (noncommLaurentPowers x hx), one_smul,
    HahnSeries.SummableFamily.hsum_sub,
    ← HahnSeries.SummableFamily.hsum_embDomain (x • noncommLaurentPowers x hx)
      ⟨Nat.succ, Nat.succ_injective⟩,
    noncommLaurentPowers_shift]
  simp

end Geometric

section Skew

variable {K : Type*} [Field K]

/-- Degree-n coefficient operator a sigma^n in the skew Laurent representation. -/
def skewLaurentCoefficient (σ : K ≃+* K) (n : ℤ) : K →+ AddMonoid.End K where
  toFun a :=
    { toFun := fun x => a * (σ ^ n) x
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add] }
  map_zero' := by ext x; exact zero_mul _
  map_add' a b := by ext x; exact add_mul a b _

@[simp] theorem skewLaurentCoefficient_apply (σ : K ≃+* K) (n : ℤ) (a x : K) :
    skewLaurentCoefficient σ n a x = a * (σ ^ n) x := rfl

@[simp] theorem skewLaurentCoefficient_apply_one (σ : K ≃+* K) (n : ℤ) (a : K) :
    skewLaurentCoefficient σ n a 1 = a := by simp

theorem skewLaurentCoefficient_injective (σ : K ≃+* K) (n : ℤ) :
    Function.Injective (skewLaurentCoefficient σ n) := by
  intro a b h
  simpa using DFunLike.congr_fun h 1

theorem skewLaurentCoefficient_mul (σ : K ≃+* K) (m n : ℤ) (a b : K) :
    skewLaurentCoefficient σ m a * skewLaurentCoefficient σ n b =
      skewLaurentCoefficient σ (m + n) (a * (σ ^ m) b) := by
  ext x
  change a * (σ ^ m) (b * (σ ^ n) x) =
    (a * (σ ^ m) b) * (σ ^ (m + n)) x
  simp [map_mul, zpow_add, mul_assoc]

@[simp] theorem skewLaurentCoefficient_zero_one (σ : K ≃+* K) :
    skewLaurentCoefficient σ 0 1 = 1 := by ext x; simp

/-- Concrete skew Laurent series as a graded coefficient subring of operator Hahn series. -/
def skewLaurentOperatorRing (σ : K ≃+* K) :
    Subring (HahnSeries ℤ (AddMonoid.End K)) where
  carrier := {f | ∀ n, f.coeff n ∈ (skewLaurentCoefficient σ n).range}
  zero_mem' n := by simp
  one_mem' n := by
    by_cases hn : n = 0
    · subst n
      exact ⟨1, by simp⟩
    · simp [HahnSeries.coeff_one, hn]
  add_mem' hf hg n := by
    simpa only [HahnSeries.coeff_add] using
      (skewLaurentCoefficient σ n).range.add_mem (hf n) (hg n)
  neg_mem' hf n := by
    simpa only [HahnSeries.coeff_neg] using
      (skewLaurentCoefficient σ n).range.neg_mem (hf n)
  mul_mem' hf hg n := by
    rw [HahnSeries.coeff_mul]
    apply AddSubmonoid.sum_mem
    intro ij hij
    obtain ⟨a, ha⟩ := hf ij.1
    obtain ⟨b, hb⟩ := hg ij.2
    rw [← ha, ← hb, skewLaurentCoefficient_mul,
      (Finset.mem_antidiagonal.mp hij).2.2]
    exact ⟨_, rfl⟩

theorem skewLaurentOperatorRing_single (σ : K ≃+* K) (n : ℤ) (a : K) :
    HahnSeries.single n (skewLaurentCoefficient σ n a) ∈ skewLaurentOperatorRing σ := by
  intro m
  by_cases hm : m = n
  · subst m
    exact ⟨a, by simp⟩
  · simp [hm]

/-- A summable family stays in the skew ring coefficientwise. -/
theorem skewLaurentOperatorRing_hsum (σ : K ≃+* K) {ι : Type*}
    (f : HahnSeries.SummableFamily ℤ (AddMonoid.End K) ι)
    (hf : ∀ i, f i ∈ skewLaurentOperatorRing σ) :
    f.hsum ∈ skewLaurentOperatorRing σ := by
  intro n
  rw [HahnSeries.SummableFamily.coeff_hsum_eq_sum]
  exact AddSubmonoid.sum_mem _ (fun i _ => hf i n)

/-- A monomial in the concrete skew Laurent ring. -/
def skewLaurentMonomial (σ : K ≃+* K) (n : ℤ) (a : K) :
    skewLaurentOperatorRing σ :=
  ⟨HahnSeries.single n (skewLaurentCoefficient σ n a),
    skewLaurentOperatorRing_single σ n a⟩

theorem skewLaurentMonomial_mul (σ : K ≃+* K) (m n : ℤ) (a b : K) :
    skewLaurentMonomial σ m a * skewLaurentMonomial σ n b =
      skewLaurentMonomial σ (m + n) (a * (σ ^ m) b) := by
  apply Subtype.ext
  exact (HahnSeries.single_mul_single).trans
    (congrArg (HahnSeries.single (m + n)) (skewLaurentCoefficient_mul σ m n a b))

@[simp] theorem skewLaurentMonomial_zero_one (σ : K ≃+* K) :
    skewLaurentMonomial σ 0 1 = 1 := by
  apply Subtype.ext
  simp [skewLaurentMonomial]

/-- Every nonzero skew monomial is explicitly invertible. -/
def skewLaurentMonomialUnit (σ : K ≃+* K) (n : ℤ) (a : K) (ha : a ≠ 0) :
    (skewLaurentOperatorRing σ)ˣ where
  val := skewLaurentMonomial σ n a
  inv := skewLaurentMonomial σ (-n) ((σ ^ (-n)) a⁻¹)
  val_inv := by
    rw [skewLaurentMonomial_mul]
    simp [ha]
  inv_val := by
    rw [skewLaurentMonomial_mul]
    simp [ha]

theorem isUnit_skewLaurentCoefficient (σ : K ≃+* K) (n : ℤ) {a : K} (ha : a ≠ 0) :
    IsUnit (skewLaurentCoefficient σ n a) := by
  refine ⟨⟨skewLaurentCoefficient σ n a,
    skewLaurentCoefficient σ (-n) ((σ ^ (-n)) a⁻¹), ?_, ?_⟩, rfl⟩
  · rw [skewLaurentCoefficient_mul]
    simp [ha]
  · rw [skewLaurentCoefficient_mul]
    simp [ha]

theorem isUnit_skewLaurent_leadingCoeff (σ : K ≃+* K)
    (f : skewLaurentOperatorRing σ) (hf : f ≠ 0) :
    IsUnit (f.val.leadingCoeff) := by
  obtain ⟨a, ha⟩ := f.property f.val.order
  rw [HahnSeries.leadingCoeff_eq, ← ha]
  apply isUnit_skewLaurentCoefficient
  intro h
  have hzero : f.val.leadingCoeff = 0 := by
    rw [HahnSeries.leadingCoeff_eq, ← ha, h, map_zero]
  exact hf (Subtype.ext (HahnSeries.leadingCoeff_eq_zero.mp hzero))

instance skewLaurentOperatorRing_noZeroDivisors (σ : K ≃+* K) :
    NoZeroDivisors (skewLaurentOperatorRing σ) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} hfg := by
    by_cases hf : f = 0
    · exact Or.inl hf
    right
    have hfg' : f.val * g.val = 0 := congrArg Subtype.val hfg
    have hcoeff : f.val.leadingCoeff * g.val.leadingCoeff = 0 := by
      rw [← HahnSeries.coeff_mul_order_add_order, hfg', HahnSeries.coeff_zero]
    have hg := (isUnit_skewLaurent_leadingCoeff σ f hf).mul_right_eq_zero.mp hcoeff
    exact Subtype.ext (HahnSeries.leadingCoeff_eq_zero.mp hg)

/-- The normalized remainder has strictly positive outer order. -/
private theorem skewLaurent_normalized_remainder_positive
    (σ : K ≃+* K) (f : skewLaurentOperatorRing σ)
    (a : K) (ha : skewLaurentCoefficient σ f.val.order a = f.val.leadingCoeff)
    (ha0 : a ≠ 0) :
    0 < (1 -
      (skewLaurentMonomialUnit σ f.val.order a ha0).inv.val * f.val).orderTop := by
  apply lt_of_lt_of_le (show (0 : WithTop ℤ) < 1 by norm_num)
  apply HahnSeries.le_orderTop_iff_forall.mpr
  intro j hj
  have hj' : j < 1 := by exact_mod_cast hj
  change (1 - HahnSeries.single (-f.val.order)
    (skewLaurentCoefficient σ (-f.val.order) ((σ ^ (-f.val.order)) a⁻¹)) * f.val).coeff j = 0
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_mul]
  by_cases hj0 : j = 0
  · subst j
    simp only [HahnSeries.coeff_one, zero_sub, neg_neg]
    rw [← HahnSeries.leadingCoeff_eq, ← ha, skewLaurentCoefficient_mul]
    simp [ha0]
  · have hjneg : j < 0 := by omega
    rw [HahnSeries.coeff_eq_zero_of_lt_order (x := f.val) (by omega), mul_zero]
    simp [HahnSeries.coeff_one, hj0]

instance skewLaurentOperatorRing_nontrivial (σ : K ≃+* K) :
    Nontrivial (skewLaurentOperatorRing σ) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hh := congrArg (fun f : skewLaurentOperatorRing σ => f.val.coeff 0 1) h
  simp at hh

instance skewLaurentOperatorRing_isDomain (σ : K ≃+* K) :
    IsDomain (skewLaurentOperatorRing σ) := NoZeroDivisors.to_isDomain _

instance skewLaurentOperatorRing_dedekindFinite (σ : K ≃+* K) :
    IsDedekindFiniteMonoid (skewLaurentOperatorRing σ) where
  mul_eq_one_symm {a b} hab := by
    have ha := left_ne_zero_of_mul_eq_one hab
    have hz : a * (b * a - 1) = 0 := by
      rw [mul_sub a (b * a) 1, ← mul_assoc, hab, one_mul, mul_one a, sub_self]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hz with h | h
    · exact (ha h).elim
    · exact sub_eq_zero.mp h

theorem isUnit_one_sub_skewLaurentOperator (σ : K ≃+* K)
    (h : skewLaurentOperatorRing σ) (hh : 0 < h.val.orderTop) : IsUnit (1 - h) := by
  let g : skewLaurentOperatorRing σ :=
    ⟨(noncommLaurentPowers h.val hh).hsum,
      skewLaurentOperatorRing_hsum σ _ (fun n =>
        by
          rw [noncommLaurentPowers_apply]
          exact (skewLaurentOperatorRing σ).pow_mem (x := h.val) h.property n)⟩
  have hright : (1 - h) * g = 1 := by
    apply Subtype.ext
    exact one_sub_mul_noncommLaurentPowers h.val hh
  exact IsUnit.of_mul_eq_one g hright

/-- Every nonzero concrete skew Laurent series has an inverse in the same ring. -/
theorem isUnit_skewLaurentOperator (σ : K ≃+* K)
    (f : skewLaurentOperatorRing σ) (hf : f ≠ 0) : IsUnit f := by
  obtain ⟨a, ha⟩ := f.property f.val.order
  have ha' : skewLaurentCoefficient σ f.val.order a = f.val.leadingCoeff :=
    ha.trans HahnSeries.leadingCoeff_eq.symm
  have ha0 : a ≠ 0 := by
    intro h
    have hzero : f.val.leadingCoeff = 0 := by rw [← ha', h, map_zero]
    exact hf (Subtype.ext (HahnSeries.leadingCoeff_eq_zero.mp hzero))
  let u := skewLaurentMonomialUnit σ f.val.order a ha0
  let h : skewLaurentOperatorRing σ := 1 - u.inv * f
  have hh : 0 < h.val.orderTop :=
    skewLaurent_normalized_remainder_positive σ f a ha' ha0
  have hunit : IsUnit (u.inv * f) := by
    have hi := isUnit_one_sub_skewLaurentOperator σ h hh
    change IsUnit (1 - (1 - u.inv * f)) at hi
    rw [sub_sub_self (1 : skewLaurentOperatorRing σ) (u.inv * f)] at hi
    exact hi
  exact isUnit_of_mul_isUnit_right hunit

/-- Division structure obtained from the explicit formal inverses, without an existence axiom. -/
instance skewLaurentOperatorRing_divisionRing (σ : K ≃+* K) :
    DivisionRing (skewLaurentOperatorRing σ) :=
  DivisionRing.ofIsUnitOrEqZero fun f => by
    by_cases hf : f = 0
    · exact Or.inr hf
    · exact Or.inl (isUnit_skewLaurentOperator σ f hf)

/-- The coefficient field sits in outer degree zero. -/
def skewLaurentConstant (σ : K ≃+* K) : K →+* skewLaurentOperatorRing σ where
  toFun a := skewLaurentMonomial σ 0 a
  map_zero' := by apply Subtype.ext; simp [skewLaurentMonomial]
  map_one' := skewLaurentMonomial_zero_one σ
  map_add' a b := by
    apply Subtype.ext
    simp [skewLaurentMonomial, map_add, HahnSeries.single_add]
  map_mul' a b := by
    rw [skewLaurentMonomial_mul]
    simp

/-- The additive sigma-coboundary is an actual commutator in the skew division ring. -/
theorem skewLaurent_clock_commutator (σ : K ≃+* K) (x : K) :
    skewLaurentMonomial σ 1 1 * skewLaurentMonomial σ (-1) x -
      skewLaurentMonomial σ (-1) x * skewLaurentMonomial σ 1 1 =
        skewLaurentConstant σ (σ x - x) := by
  rw [skewLaurentMonomial_mul, skewLaurentMonomial_mul,
    (skewLaurentConstant σ).map_sub]
  simp [skewLaurentConstant]

/-- An additive translation coordinate forces every cyclic trace to kill the unit. -/
theorem skewLaurent_cyclicTrace_one_eq_zero_of_translation
    (σ : K ≃+* K) {A : Type*} [AddCommGroup A]
    (T : skewLaurentOperatorRing σ →+ A)
    (hT : ∀ a b, T (a * b) = T (b * a))
    {x : K} (hx : σ x = x + 1) : T 1 = 0 := by
  have h := congrArg T (skewLaurent_clock_commutator σ x)
  rw [map_sub, hT, sub_self, hx, add_sub_cancel_left, map_one] at h
  exact h.symm

end Skew

end
end GaloisForLFunctions.HTGeometry
