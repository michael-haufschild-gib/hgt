import GaloisForLFunctions.RHTower.RouteETerminalSourceReporterFirewall
import GaloisForLFunctions.RHTower.RouteEPrimitiveConeParentNoGo
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Fixed-order test of the Route E largest-prime cofactor mechanism.
For 1 < r ≤ 2, every coefficient-bounded single numerator channel with
numerator at most q is absolutely summable over denominator primes q.
This is a boundary/receiver quantifier no-go, not a full-covariance bound. -/

open Set Finset
namespace RHTower
noncomputable section

def routeEFixedOrderDifference (r a b : ℝ) : ℝ :=
  (a + b) ^ (-r) - (2 * a + b) ^ (-r)

theorem routeEFixedOrderDifference_one_eq_cone
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    routeEFixedOrderDifference 1 a b = routeEPrimitiveConeWeight a b := by
  rw [routeEPrimitiveConeWeight_eq_diff ha hb]
  simp only [routeEFixedOrderDifference, Real.rpow_neg_one, inv_eq_one_div]

theorem routeEFixedOrderDifference_le
    {r a b : ℝ} (hr : 1 < r) (hr2 : r ≤ 2)
    (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ routeEFixedOrderDifference r a b ∧
      routeEFixedOrderDifference r a b ≤ 3 * a * b ^ (-(r + 1)) := by
  have ht : 0 < a + b := by linarith
  have hu : 0 ≤ a / (a + b) := div_nonneg ha ht.le
  have hfactor : (a + b) * (1 + a / (a + b)) = 2 * a + b := by
    field_simp
    ring
  have hformula : routeEFixedOrderDifference r a b =
      (a + b) ^ (-r) * (1 - (1 + a / (a + b)) ^ (-r)) := by
    unfold routeEFixedOrderDifference
    rw [← hfactor, Real.mul_rpow ht.le (by positivity)]
    ring
  have hcore := one_sub_one_add_rpow_neg_le_three_mul hu (by linarith : 0 < r) hr2
  rw [hformula]
  constructor
  · exact mul_nonneg (Real.rpow_nonneg ht.le _) hcore.1
  · have hmul :
        (a + b) ^ (-r) * (1 - (1 + a / (a + b)) ^ (-r)) ≤
        (a + b) ^ (-r) * (3 * (a / (a + b))) :=
      mul_le_mul_of_nonneg_left hcore.2 (Real.rpow_nonneg ht.le _)
    have hpower : (a + b) ^ (-r) * (3 * (a / (a + b))) =
        3 * a * (a + b) ^ (-(r + 1)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one,
        show -(r + 1) = -r + (-1 : ℝ) by ring, Real.rpow_add ht]
      ring
    have hcompare : (a + b) ^ (-(r + 1)) ≤ b ^ (-(r + 1)) :=
      Real.rpow_le_rpow_of_nonpos hb (by linarith : b ≤ a + b) (by linarith)
    calc
      (a + b) ^ (-r) * (1 - (1 + a / (a + b)) ^ (-r)) ≤
          (a + b) ^ (-r) * (3 * (a / (a + b))) := hmul
      _ = 3 * a * (a + b) ^ (-(r + 1)) := hpower
      _ ≤ 3 * a * b ^ (-(r + 1)) :=
        mul_le_mul_of_nonneg_left hcompare (by positivity)

def routeEFixedOrderCofactorFibre (r a : ℝ) (q : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioo 0 q,
    c d * routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ))

theorem abs_routeEFixedOrderCofactorFibre_le
    {r a : ℝ} (hr : 1 < r) (hr2 : r ≤ 2) (ha : 0 ≤ a)
    {q : ℕ} (hq : 0 < q) (c : ℕ → ℝ) (hc : ∀ d, |c d| ≤ 1) :
    |routeEFixedOrderCofactorFibre r a q c| ≤
      6 * a * (q : ℝ) ^ (-(r + 1)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlocal (d : ℕ) (hd : d ∈ Finset.Ioo 0 q) :
      |c d * routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ))| ≤
        (3 * a * (q : ℝ) ^ (-(r + 1))) * (1 / (d : ℝ) ^ (2 : ℕ)) := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Ioo.mp hd).1
    have hd1 : (1 : ℝ) ≤ d := by
      have hdn : 1 ≤ d := by
        have hdpos := (Finset.mem_Ioo.mp hd).1
        omega
      exact_mod_cast hdn
    have hk := routeEFixedOrderDifference_le hr hr2 ha (mul_pos hq0 hd0)
    have hdm : (d : ℝ) ^ (-(r + 1)) ≤ (d : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
    have heq : ((q : ℝ) * (d : ℝ)) ^ (-(r + 1)) =
        (q : ℝ) ^ (-(r + 1)) * (d : ℝ) ^ (-(r + 1)) :=
      Real.mul_rpow hq0.le hd0.le
    rw [abs_mul, abs_of_nonneg hk.1]
    have hcoeff : |c d| * routeEFixedOrderDifference r a ((q : ℝ) * d) ≤
        3 * a * ((q : ℝ) * d) ^ (-(r + 1)) := by
      calc
        _ ≤ 1 * routeEFixedOrderDifference r a ((q : ℝ) * d) :=
          mul_le_mul_of_nonneg_right (hc d) hk.1
        _ ≤ 3 * a * ((q : ℝ) * d) ^ (-(r + 1)) := by simpa using hk.2
    calc
      _ ≤ 3 * a * ((q : ℝ) * d) ^ (-(r + 1)) := hcoeff
      _ = (3 * a * (q : ℝ) ^ (-(r + 1))) * (d : ℝ) ^ (-(r + 1)) := by
        rw [heq]; ring
      _ ≤ (3 * a * (q : ℝ) ^ (-(r + 1))) * (d : ℝ) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_left hdm (by positivity)
      _ = (3 * a * (q : ℝ) ^ (-(r + 1))) * (1 / (d : ℝ) ^ (2 : ℕ)) := by
        rw [Real.rpow_neg hd0.le, Real.rpow_ofNat]
        ring
  have hsum : (∑ d ∈ Finset.Ioo 0 q, 1 / (d : ℝ) ^ (2 : ℕ)) ≤ 2 := by
    have h := sum_Ioo_inv_sq_le (α := ℝ) 0 q
    norm_num at h ⊢
    simpa only [one_div] using h
  calc
    |routeEFixedOrderCofactorFibre r a q c| ≤
        ∑ d ∈ Finset.Ioo 0 q,
          |c d * routeEFixedOrderDifference r a ((q : ℝ) * d)| := by
            exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioo 0 q,
          (3 * a * (q : ℝ) ^ (-(r + 1))) * (1 / (d : ℝ) ^ (2 : ℕ)) := by
            apply Finset.sum_le_sum
            intro d hd
            exact hlocal d hd
    _ = (3 * a * (q : ℝ) ^ (-(r + 1))) *
          (∑ d ∈ Finset.Ioo 0 q, 1 / (d : ℝ) ^ (2 : ℕ)) := by
            rw [Finset.mul_sum]
    _ ≤ (3 * a * (q : ℝ) ^ (-(r + 1))) * 2 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 6 * a * (q : ℝ) ^ (-(r + 1)) := by ring

theorem summable_routeEFixedOrderCofactorFibre
    {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2)
    (a : Nat.Primes → ℝ) (ha0 : ∀ q, 0 ≤ a q)
    (haq : ∀ q, a q ≤ ((q : ℕ) : ℝ))
    (c : Nat.Primes → ℕ → ℝ) (hc : ∀ q d, |c q d| ≤ 1) :
    Summable (fun q : Nat.Primes =>
      routeEFixedOrderCofactorFibre r (a q) (q : ℕ) (c q)) := by
  have hnat : Summable fun n : ℕ => (n : ℝ) ^ (-r) := by
    rw [Real.summable_nat_rpow]
    linarith
  have hprime : Summable fun q : Nat.Primes => ((q : ℕ) : ℝ) ^ (-r) :=
    hnat.subtype _
  refine Summable.of_norm_bounded
    (g := fun q : Nat.Primes => 6 * (((q : ℕ) : ℝ) ^ (-r)))
    (hprime.mul_left 6) ?_
  intro q
  have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.property.pos
  have hb := abs_routeEFixedOrderCofactorFibre_le hr hr2 (ha0 q)
    q.property.pos (c q) (hc q)
  have hpow : ((q : ℕ) : ℝ) * ((q : ℕ) : ℝ) ^ (-(r + 1)) =
      ((q : ℕ) : ℝ) ^ (-r) := by
    calc
      _ = ((q : ℕ) : ℝ) ^ (1 : ℝ) * ((q : ℕ) : ℝ) ^ (-(r + 1)) := by
        rw [Real.rpow_one]
      _ = ((q : ℕ) : ℝ) ^ ((1 : ℝ) + (-(r + 1))) :=
        (Real.rpow_add hq0 1 (-(r + 1))).symm
      _ = ((q : ℕ) : ℝ) ^ (-r) := by congr 1; ring
  rw [Real.norm_eq_abs]
  calc
    |routeEFixedOrderCofactorFibre r (a q) (q : ℕ) (c q)| ≤
        6 * a q * ((q : ℕ) : ℝ) ^ (-(r + 1)) := hb
    _ = a q * (6 * ((q : ℕ) : ℝ) ^ (-(r + 1))) := by ring
    _ ≤ ((q : ℕ) : ℝ) * (6 * ((q : ℕ) : ℝ) ^ (-(r + 1))) :=
      mul_le_mul_of_nonneg_right (haq q) (by positivity)
    _ = 6 * ((q : ℕ) : ℝ) ^ (-r) := by
      calc
        _ = 6 * (((q : ℕ) : ℝ) * ((q : ℕ) : ℝ) ^ (-(r + 1))) := by ring
        _ = _ := by rw [hpow]

def routeEFixedOrderPrimeFibre (r : ℝ) (p q : Nat.Primes) : ℝ :=
  routeEFixedOrderCofactorFibre r (p : ℝ) (q : ℕ) (fun d =>
    if Nat.Coprime (p : ℕ) d then
      (ArithmeticFunction.moebius (p : ℕ) : ℝ) *
        (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ)
    else 0)

theorem routeEFixedOrderPrimeFibre_coeff_bound (p q : Nat.Primes) (d : ℕ) :
    |if Nat.Coprime (p : ℕ) d then
      (ArithmeticFunction.moebius (p : ℕ) : ℝ) *
        (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ)
    else 0| ≤ 1 := by
  split_ifs with h
  · rw [abs_mul]
    have hp : |(ArithmeticFunction.moebius (p : ℕ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (p : ℕ))
    have hqd : |(ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (q : ℕ) * d)
    nlinarith [abs_nonneg (ArithmeticFunction.moebius (p : ℕ) : ℝ),
      abs_nonneg (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ)]
  · norm_num

theorem summable_routeEFixedOrderPrimeFibre
    {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2)
    (p : Nat.Primes → Nat.Primes)
    (hp : ∀ q, ((p q : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ)) :
    Summable (fun q : Nat.Primes => routeEFixedOrderPrimeFibre r (p q) q) := by
  exact summable_routeEFixedOrderCofactorFibre hr hr2
    (fun q => ((p q : ℕ) : ℝ))
    (fun q => by positivity) hp
    (fun q d => if Nat.Coprime (p q : ℕ) d then
      (ArithmeticFunction.moebius (p q : ℕ) : ℝ) *
        (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ)
      else 0)
    (fun q d => routeEFixedOrderPrimeFibre_coeff_bound (p q) q d)

theorem routeERealOrderedSecantRpow {r x y z w : ℝ}
    (hr : 1 ≤ r) (hx : 0 ≤ x) (hxy : x < y) (hyz : y ≤ z) (hzw : z < w) :
    (y ^ r - x ^ r) / (y - x) ≤ (w ^ r - z ^ r) / (w - z) := by
  have hconv := convexOn_rpow hr
  have hxmem : x ∈ Ici (0 : ℝ) := hx
  have hymem : y ∈ Ici (0 : ℝ) := by simp; linarith
  have hzmem : z ∈ Ici (0 : ℝ) := by simp; linarith
  have hwmem : w ∈ Ici (0 : ℝ) := by simp; linarith
  have h1 := hconv.secant_mono hxmem hymem hwmem (ne_of_gt hxy)
    (ne_of_gt (lt_of_lt_of_le hxy (hyz.trans hzw.le))) (by linarith : y ≤ w)
  have h2 := hconv.secant_mono hwmem hxmem hzmem (by linarith : x ≠ w)
    (by linarith : z ≠ w) (by linarith : x ≤ z)
  have h2' : (w ^ r - x ^ r) / (w - x) ≤ (w ^ r - z ^ r) / (w - z) := by
    calc
      (w ^ r - x ^ r) / (w - x) = (x ^ r - w ^ r) / (x - w) := by
        rw [show x ^ r - w ^ r = -(w ^ r - x ^ r) by ring,
          show x - w = -(w - x) by ring, neg_div_neg_eq]
      _ ≤ (z ^ r - w ^ r) / (z - w) := h2
      _ = (w ^ r - z ^ r) / (w - z) := by
        rw [show z ^ r - w ^ r = -(w ^ r - z ^ r) by ring,
          show z - w = -(w - z) by ring, neg_div_neg_eq]
  exact h1.trans h2'

theorem routeEReciprocalRpow {u r : ℝ} (hu : 0 < u) :
    (1 / u) ^ r = u ^ (-r) := by
  rw [one_div, Real.inv_rpow hu.le, Real.rpow_neg hu.le]

theorem routeEFixedOrderDifference_cross
    {r a b c : ℝ} (hr : 1 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (hbc : b + a ≤ c) :
    routeEFixedOrderDifference r a c * routeEFixedOrderDifference 1 a b ≤
      routeEFixedOrderDifference 1 a c * routeEFixedOrderDifference r a b := by
  let x : ℝ := 1 / (2 * a + c)
  let y : ℝ := 1 / (a + c)
  let z : ℝ := 1 / (2 * a + b)
  let w : ℝ := 1 / (a + b)
  have hc : 0 < c := by linarith
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxy : x < y := by
    dsimp [x, y]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hyz : y ≤ z := by
    dsimp [y, z]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hzw : z < w := by
    dsimp [z, w]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hslope := routeERealOrderedSecantRpow hr hx hxy hyz hzw
  have hcross := (div_le_div_iff₀ (by linarith : 0 < y - x)
    (by linarith : 0 < w - z)).mp hslope
  have hkrc : y ^ r - x ^ r = routeEFixedOrderDifference r a c := by
    dsimp [x, y, routeEFixedOrderDifference]
    rw [routeEReciprocalRpow (by positivity : 0 < a + c),
      routeEReciprocalRpow (by positivity : 0 < 2 * a + c)]
  have hkrb : w ^ r - z ^ r = routeEFixedOrderDifference r a b := by
    dsimp [w, z, routeEFixedOrderDifference]
    rw [routeEReciprocalRpow (by positivity : 0 < a + b),
      routeEReciprocalRpow (by positivity : 0 < 2 * a + b)]
  have hk1c : y - x = routeEFixedOrderDifference 1 a c := by
    dsimp [x, y, routeEFixedOrderDifference]
    simp only [Real.rpow_neg_one, inv_eq_one_div]
  have hk1b : w - z = routeEFixedOrderDifference 1 a b := by
    dsimp [w, z, routeEFixedOrderDifference]
    simp only [Real.rpow_neg_one, inv_eq_one_div]
  rw [hkrc, hkrb, hk1c, hk1b] at hcross
  simpa only [mul_comm] using hcross

theorem routeEInvSqTail_le (q : ℕ) (hq : 3 ≤ q) :
    (∑ d ∈ Finset.Ioo 1 q, 1 / (d : ℝ) ^ (2 : ℕ)) ≤ 11 / 12 := by
  have hset : Finset.Ioo 1 q = insert 2 (Finset.Ioo 2 q) := by
    ext d
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  have h := sum_Ioo_inv_sq_le (α := ℝ) 2 q
  norm_num at h ⊢
  have h' : (∑ d ∈ Finset.Ioo 2 q, 1 / (d : ℝ) ^ (2 : ℕ)) ≤ 2 / 3 := by
    simpa only [one_div] using h
  linarith

theorem routeEBaseMain_gt
    {a : ℝ} (ha : 0 < a) {q : ℕ} (hq128 : 128 * a ≤ (q : ℝ)) :
    (11 / 12 : ℝ) * a / (q : ℝ) ^ (2 : ℕ) <
      routeEFixedOrderDifference 1 a (q : ℝ) := by
  have hq : (0 : ℝ) < q := by linarith
  have haBound : a ≤ (q : ℝ) / 128 := by linarith
  have hsqa : a * a ≤ a * (q : ℝ) / 128 := by
    nlinarith [mul_le_mul_of_nonneg_left haBound ha.le]
  have haq : a * (q : ℝ) ≤ (q : ℝ) ^ (2 : ℕ) / 128 := by
    nlinarith [mul_le_mul_of_nonneg_right haBound hq.le]
  have hden : (a + (q : ℝ)) * (2 * a + (q : ℝ)) <
      (12 / 11 : ℝ) * (q : ℝ) ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hq]
  rw [routeEFixedOrderDifference_one_eq_cone ha hq]
  unfold routeEPrimitiveConeWeight
  have hdenpos : 0 < (a + (q : ℝ)) * (2 * a + (q : ℝ)) := by positivity
  have hq2pos : 0 < (q : ℝ) ^ (2 : ℕ) := by positivity
  rw [div_lt_div_iff₀ hq2pos hdenpos]
  have hscaled := mul_lt_mul_of_pos_left hden ha
  nlinarith

theorem routeEBaseKernel_le_invSq
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    routeEFixedOrderDifference 1 a b ≤ a / b ^ (2 : ℕ) := by
  rcases eq_or_lt_of_le ha with rfl | ha0
  · simp [routeEFixedOrderDifference]
  rw [routeEFixedOrderDifference_one_eq_cone ha0 hb]
  unfold routeEPrimitiveConeWeight
  have hden : b ^ (2 : ℕ) ≤ (a + b) * (2 * a + b) := by
    nlinarith [sq_nonneg a]
  have hdenpos : 0 < (a + b) * (2 * a + b) := by positivity
  have hb2pos : 0 < b ^ (2 : ℕ) := by positivity
  rw [div_le_div_iff₀ hdenpos hb2pos]
  nlinarith [mul_le_mul_of_nonneg_left hden ha]

theorem routeEBaseTail_le
    {a : ℝ} (ha : 0 ≤ a) {q : ℕ} (hq : 3 ≤ q) :
    (∑ d ∈ Finset.Ioo 1 q,
      routeEFixedOrderDifference 1 a ((q : ℝ) * (d : ℝ))) ≤
      (11 / 12 : ℝ) * a / (q : ℝ) ^ (2 : ℕ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpoint (d : ℕ) (hd : d ∈ Finset.Ioo 1 q) :
      routeEFixedOrderDifference 1 a ((q : ℝ) * (d : ℝ)) ≤
        (a / (q : ℝ) ^ (2 : ℕ)) * (1 / (d : ℝ) ^ (2 : ℕ)) := by
    have hd0 : (0 : ℝ) < d := by
      exact_mod_cast (show 0 < d by have := (Finset.mem_Ioo.mp hd).1; omega)
    have hk := routeEBaseKernel_le_invSq ha (mul_pos hq0 hd0)
    calc
      _ ≤ a / ((q : ℝ) * (d : ℝ)) ^ (2 : ℕ) := hk
      _ = (a / (q : ℝ) ^ (2 : ℕ)) * (1 / (d : ℝ) ^ (2 : ℕ)) := by
        rw [mul_pow]
        ring
  calc
    (∑ d ∈ Finset.Ioo 1 q,
      routeEFixedOrderDifference 1 a ((q : ℝ) * (d : ℝ))) ≤
      ∑ d ∈ Finset.Ioo 1 q,
        (a / (q : ℝ) ^ (2 : ℕ)) * (1 / (d : ℝ) ^ (2 : ℕ)) := by
          exact Finset.sum_le_sum hpoint
    _ = (a / (q : ℝ) ^ (2 : ℕ)) *
          (∑ d ∈ Finset.Ioo 1 q, 1 / (d : ℝ) ^ (2 : ℕ)) := by
            rw [Finset.mul_sum]
    _ ≤ (a / (q : ℝ) ^ (2 : ℕ)) * (11 / 12) :=
      mul_le_mul_of_nonneg_left (routeEInvSqTail_le q hq) (by positivity)
    _ = (11 / 12 : ℝ) * a / (q : ℝ) ^ (2 : ℕ) := by ring

theorem routeEFixedOrderDifference_pos
    {r a b : ℝ} (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) :
    0 < routeEFixedOrderDifference r a b := by
  unfold routeEFixedOrderDifference
  exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg (by positivity)
    (by linarith : a + b < 2 * a + b) (by linarith : -r < 0))

/-- Universal first-cofactor dominance: any bounded coefficient sequence whose
first coefficient is one has positive completed fibre in the far cone. -/
theorem routeEFixedOrderCofactorFibre_pos
    {r a : ℝ} (hr : 1 ≤ r) (ha : 0 < a)
    {q : ℕ} (hq : 3 ≤ q) (hq128 : 128 * a ≤ (q : ℝ))
    (c : ℕ → ℝ) (hc : ∀ d, |c d| ≤ 1) (hc1 : c 1 = 1) :
    0 < routeEFixedOrderCofactorFibre r a q c := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmain1 := routeEBaseMain_gt ha hq128
  have htail1 := routeEBaseTail_le ha.le hq
  have hgap1 :
      (∑ d ∈ Finset.Ioo 1 q,
        routeEFixedOrderDifference 1 a ((q : ℝ) * (d : ℝ))) <
      routeEFixedOrderDifference 1 a (q : ℝ) := lt_of_le_of_lt htail1 hmain1
  have hmain1pos : 0 < routeEFixedOrderDifference 1 a (q : ℝ) :=
    routeEFixedOrderDifference_pos (by norm_num) ha hq0
  have hmainrpos : 0 < routeEFixedOrderDifference r a (q : ℝ) :=
    routeEFixedOrderDifference_pos (by linarith) ha hq0
  have hcross :
      (∑ d ∈ Finset.Ioo 1 q,
        routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ))) *
        routeEFixedOrderDifference 1 a (q : ℝ) ≤
      (∑ d ∈ Finset.Ioo 1 q,
        routeEFixedOrderDifference 1 a ((q : ℝ) * (d : ℝ))) *
        routeEFixedOrderDifference r a (q : ℝ) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d hd
    apply routeEFixedOrderDifference_cross hr ha hq0
    have hd2 : 2 ≤ d := by have := (Finset.mem_Ioo.mp hd).1; omega
    have hd2R : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have haq : a ≤ (q : ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hd2R hq0.le]
  have htailr :
      (∑ d ∈ Finset.Ioo 1 q,
        routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ))) <
      routeEFixedOrderDifference r a (q : ℝ) := by
    have hchain :
        (∑ d ∈ Finset.Ioo 1 q,
          routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ))) *
          routeEFixedOrderDifference 1 a (q : ℝ) <
        routeEFixedOrderDifference r a (q : ℝ) *
          routeEFixedOrderDifference 1 a (q : ℝ) := by
      calc
        _ ≤ (∑ d ∈ Finset.Ioo 1 q,
              routeEFixedOrderDifference 1 a ((q : ℝ) * (d : ℝ))) *
              routeEFixedOrderDifference r a (q : ℝ) := hcross
        _ < routeEFixedOrderDifference 1 a (q : ℝ) *
              routeEFixedOrderDifference r a (q : ℝ) :=
          mul_lt_mul_of_pos_right hgap1 hmainrpos
        _ = routeEFixedOrderDifference r a (q : ℝ) *
              routeEFixedOrderDifference 1 a (q : ℝ) := by ring
    by_contra hnot
    have hle : routeEFixedOrderDifference r a (q : ℝ) ≤
        ∑ d ∈ Finset.Ioo 1 q,
          routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ)) := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_right hle hmain1pos.le
    linarith
  have hset : Finset.Ioo 0 q = insert 1 (Finset.Ioo 1 q) := by
    ext d
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  have htailCoeff :
      -(∑ d ∈ Finset.Ioo 1 q,
          routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ))) ≤
      ∑ d ∈ Finset.Ioo 1 q,
        c d * routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro d hd
    have hd0 : (0 : ℝ) < d := by
      exact_mod_cast (show 0 < d by have := (Finset.mem_Ioo.mp hd).1; omega)
    have hk := routeEFixedOrderDifference_pos (by linarith : 0 < r) ha
      (mul_pos hq0 hd0)
    have hcminus := (abs_le.mp (hc d)).1
    nlinarith
  unfold routeEFixedOrderCofactorFibre
  rw [hset, Finset.sum_insert (by simp), hc1, one_mul]
  simp only [Nat.cast_one, mul_one]
  linarith

theorem routeEFixedOrderPrimeFibre_pos
    {r : ℝ} (hr : 1 ≤ r) (p q : Nat.Primes) (hq128 :
      128 * (p : ℝ) ≤ (q : ℝ)) :
    0 < routeEFixedOrderPrimeFibre r p q := by
  have hq3 : 3 ≤ (q : ℕ) := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    have hq2 : (256 : ℝ) ≤ (q : ℝ) := by nlinarith
    exact_mod_cast (show (3 : ℝ) ≤ (q : ℝ) by linarith)
  have hc1 :
      (if Nat.Coprime (p : ℕ) 1 then
        (ArithmeticFunction.moebius (p : ℕ) : ℝ) *
          (ArithmeticFunction.moebius ((q : ℕ) * 1) : ℝ)
      else 0) = 1 := by
    simp [ArithmeticFunction.moebius_apply_prime p.property,
      ArithmeticFunction.moebius_apply_prime q.property]
  exact routeEFixedOrderCofactorFibre_pos hr (by exact_mod_cast p.property.pos)
    hq3 hq128 _ (routeEFixedOrderPrimeFibre_coeff_bound p q) hc1

theorem routeEFixedOrderCofactorFibre_neg
    {r a : ℝ} (hr : 1 ≤ r) (ha : 0 < a)
    {q : ℕ} (hq : 3 ≤ q) (hq128 : 128 * a ≤ (q : ℝ))
    (c : ℕ → ℝ) (hc : ∀ d, |c d| ≤ 1) (hc1 : c 1 = -1) :
    routeEFixedOrderCofactorFibre r a q c < 0 := by
  have hpos := routeEFixedOrderCofactorFibre_pos hr ha hq hq128
    (fun d => -c d) (fun d => by simpa using hc d) (by simp [hc1])
  have heq : routeEFixedOrderCofactorFibre r a q (fun d => -c d) =
      -routeEFixedOrderCofactorFibre r a q c := by
    unfold routeEFixedOrderCofactorFibre
    simp only [neg_mul, Finset.sum_neg_distrib]
  rw [heq] at hpos
  linarith

def routeEFixedOrderIntegerNumeratorFibre
    (r : ℝ) (a : ℕ) (q : Nat.Primes) : ℝ :=
  routeEFixedOrderCofactorFibre r (a : ℝ) (q : ℕ) (fun d =>
    if Nat.Coprime a d then
      (ArithmeticFunction.moebius a : ℝ) *
        (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ)
    else 0)

/-- All squarefree numerator grades retain their Möbius parity after every
physical denominator cofactor below q, at every order r ≥ 1. -/
theorem routeEFixedOrderIntegerNumeratorFibre_parity
    {r : ℝ} (hr : 1 ≤ r) {a : ℕ} (ha : 0 < a) (haSq : Squarefree a)
    (q : Nat.Primes) (hq128 : 128 * (a : ℝ) ≤ (q : ℝ)) :
    0 < -(ArithmeticFunction.moebius a : ℝ) *
      routeEFixedOrderIntegerNumeratorFibre r a q := by
  let mu : ℝ := (ArithmeticFunction.moebius a : ℝ)
  let coeff : ℕ → ℝ := fun d => if Nat.Coprime a d then
    mu * (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ) else 0
  have hmuSq : mu ^ (2 : ℕ) = 1 := by
    change (ArithmeticFunction.moebius a : ℝ) ^ (2 : ℕ) = 1
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree haSq
  have hmuAbs : |mu| = 1 := by
    change |(ArithmeticFunction.moebius a : ℝ)| = 1
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree haSq
  have hcoeff (d : ℕ) : |coeff d| ≤ 1 := by
    dsimp [coeff]
    split_ifs with h
    · rw [abs_mul, hmuAbs, one_mul]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (q : ℕ) * d)
    · norm_num
  have hnewcoeff (d : ℕ) : |-mu * coeff d| ≤ 1 := by
    rw [abs_mul, abs_neg, hmuAbs, one_mul]
    exact hcoeff d
  have hcoeffOne : (-mu * coeff 1) = 1 := by
    simp [coeff, ArithmeticFunction.moebius_apply_prime q.property]
    nlinarith
  have hq3 : 3 ≤ (q : ℕ) := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hqBig : (128 : ℝ) ≤ (q : ℝ) := by nlinarith
    exact_mod_cast (show (3 : ℝ) ≤ (q : ℝ) by linarith)
  have hpos := routeEFixedOrderCofactorFibre_pos hr
    (by exact_mod_cast ha : (0 : ℝ) < a) hq3 hq128
    (fun d => -mu * coeff d) hnewcoeff hcoeffOne
  have hlinear : routeEFixedOrderCofactorFibre r (a : ℝ) (q : ℕ)
      (fun d => -mu * coeff d) =
      -mu * routeEFixedOrderCofactorFibre r (a : ℝ) (q : ℕ) coeff := by
    unfold routeEFixedOrderCofactorFibre
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  change 0 < -mu * routeEFixedOrderCofactorFibre r (a : ℝ) (q : ℕ) coeff
  rw [← hlinear]
  exact hpos

theorem routeEBaseMain_gt_fifteen_sixteenths
    {a : ℝ} (ha : 0 < a) {q : ℕ} (hq128 : 128 * a ≤ (q : ℝ)) :
    (15 / 16 : ℝ) * a / (q : ℝ) ^ (2 : ℕ) <
      routeEFixedOrderDifference 1 a (q : ℝ) := by
  have hq : (0 : ℝ) < q := by linarith
  have haBound : a ≤ (q : ℝ) / 128 := by linarith
  have hsqa : a * a ≤ a * (q : ℝ) / 128 := by
    nlinarith [mul_le_mul_of_nonneg_left haBound ha.le]
  have haq : a * (q : ℝ) ≤ (q : ℝ) ^ (2 : ℕ) / 128 := by
    nlinarith [mul_le_mul_of_nonneg_right haBound hq.le]
  have hden : (a + (q : ℝ)) * (2 * a + (q : ℝ)) <
      (16 / 15 : ℝ) * (q : ℝ) ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hq]
  rw [routeEFixedOrderDifference_one_eq_cone ha hq]
  unfold routeEPrimitiveConeWeight
  have hdenpos : 0 < (a + (q : ℝ)) * (2 * a + (q : ℝ)) := by positivity
  have hq2pos : 0 < (q : ℝ) ^ (2 : ℕ) := by positivity
  rw [div_lt_div_iff₀ hq2pos hdenpos]
  have hscaled := mul_lt_mul_of_pos_left hden ha
  nlinarith

/-- Uniform quantitative first-cofactor dominance, relative to the principal
fixed-order edge, valid for all r ≥ 1. -/
theorem routeEFixedOrderCofactorFibre_gt_fraction
    {r a : ℝ} (hr : 1 ≤ r) (ha : 0 < a)
    {q : ℕ} (hq : 3 ≤ q) (hq128 : 128 * a ≤ (q : ℝ))
    (c : ℕ → ℝ) (hc : ∀ d, |c d| ≤ 1) (hc1 : c 1 = 1) :
    (1 / 48 : ℝ) * routeEFixedOrderDifference r a (q : ℝ) <
      routeEFixedOrderCofactorFibre r a q c := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmain1 := routeEBaseMain_gt_fifteen_sixteenths ha hq128
  have htail1 := routeEBaseTail_le ha.le hq
  have hmain1max := routeEBaseKernel_le_invSq ha.le hq0
  have hmain1pos : 0 < routeEFixedOrderDifference 1 a (q : ℝ) :=
    routeEFixedOrderDifference_pos (by norm_num) ha hq0
  have hmainrpos : 0 < routeEFixedOrderDifference r a (q : ℝ) :=
    routeEFixedOrderDifference_pos (by linarith) ha hq0
  have htail1strong :
      (∑ d ∈ Finset.Ioo 1 q,
        routeEFixedOrderDifference 1 a ((q : ℝ) * (d : ℝ))) <
      (47 / 48 : ℝ) * routeEFixedOrderDifference 1 a (q : ℝ) := by
    have hratio : 0 < a / (q : ℝ) ^ (2 : ℕ) := by positivity
    have hmain1' : (15 / 16 : ℝ) * (a / (q : ℝ) ^ (2 : ℕ)) <
        routeEFixedOrderDifference 1 a (q : ℝ) := by
      convert hmain1 using 1; ring
    have htail1' :
        (∑ d ∈ Finset.Ioo 1 q,
          routeEFixedOrderDifference 1 a ((q : ℝ) * (d : ℝ))) ≤
        (11 / 12 : ℝ) * (a / (q : ℝ) ^ (2 : ℕ)) := by
      convert htail1 using 1; ring
    linarith
  have hcross :
      (∑ d ∈ Finset.Ioo 1 q,
        routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ))) *
        routeEFixedOrderDifference 1 a (q : ℝ) ≤
      (∑ d ∈ Finset.Ioo 1 q,
        routeEFixedOrderDifference 1 a ((q : ℝ) * (d : ℝ))) *
        routeEFixedOrderDifference r a (q : ℝ) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d hd
    apply routeEFixedOrderDifference_cross hr ha hq0
    have hd2 : 2 ≤ d := by have := (Finset.mem_Ioo.mp hd).1; omega
    have hd2R : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have haq : a ≤ (q : ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hd2R hq0.le]
  have htailr :
      (∑ d ∈ Finset.Ioo 1 q,
        routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ))) <
      (47 / 48 : ℝ) * routeEFixedOrderDifference r a (q : ℝ) := by
    have hchain :
        (∑ d ∈ Finset.Ioo 1 q,
          routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ))) *
          routeEFixedOrderDifference 1 a (q : ℝ) <
        ((47 / 48 : ℝ) * routeEFixedOrderDifference r a (q : ℝ)) *
          routeEFixedOrderDifference 1 a (q : ℝ) := by
      calc
        _ ≤ (∑ d ∈ Finset.Ioo 1 q,
              routeEFixedOrderDifference 1 a ((q : ℝ) * (d : ℝ))) *
              routeEFixedOrderDifference r a (q : ℝ) := hcross
        _ < ((47 / 48 : ℝ) * routeEFixedOrderDifference 1 a (q : ℝ)) *
              routeEFixedOrderDifference r a (q : ℝ) :=
          mul_lt_mul_of_pos_right htail1strong hmainrpos
        _ = ((47 / 48 : ℝ) * routeEFixedOrderDifference r a (q : ℝ)) *
              routeEFixedOrderDifference 1 a (q : ℝ) := by ring
    by_contra hnot
    have hle : (47 / 48 : ℝ) * routeEFixedOrderDifference r a (q : ℝ) ≤
        ∑ d ∈ Finset.Ioo 1 q,
          routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ)) := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_right hle hmain1pos.le
    linarith
  have hset : Finset.Ioo 0 q = insert 1 (Finset.Ioo 1 q) := by
    ext d
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  have htailCoeff :
      -(∑ d ∈ Finset.Ioo 1 q,
          routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ))) ≤
      ∑ d ∈ Finset.Ioo 1 q,
        c d * routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro d hd
    have hd0 : (0 : ℝ) < d := by
      exact_mod_cast (show 0 < d by have := (Finset.mem_Ioo.mp hd).1; omega)
    have hk := routeEFixedOrderDifference_pos (by linarith : 0 < r) ha
      (mul_pos hq0 hd0)
    have hcminus := (abs_le.mp (hc d)).1
    nlinarith
  unfold routeEFixedOrderCofactorFibre
  rw [hset, Finset.sum_insert (by simp), hc1, one_mul]
  simp only [Nat.cast_one, mul_one]
  linarith

/-- Quantitative all-grade law: completing every smaller denominator cofactor
retains at least a forty-eighth of the principal edge, with Möbius parity. -/
theorem routeEFixedOrderIntegerNumeratorFibre_margin
    {r : ℝ} (hr : 1 ≤ r) {a : ℕ} (ha : 0 < a) (haSq : Squarefree a)
    (q : Nat.Primes) (hq128 : 128 * (a : ℝ) ≤ (q : ℝ)) :
    (1 / 48 : ℝ) * routeEFixedOrderDifference r (a : ℝ) (q : ℝ) <
      -(ArithmeticFunction.moebius a : ℝ) *
        routeEFixedOrderIntegerNumeratorFibre r a q := by
  let mu : ℝ := (ArithmeticFunction.moebius a : ℝ)
  let coeff : ℕ → ℝ := fun d => if Nat.Coprime a d then
    mu * (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ) else 0
  have hmuSq : mu ^ (2 : ℕ) = 1 := by
    change (ArithmeticFunction.moebius a : ℝ) ^ (2 : ℕ) = 1
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree haSq
  have hmuAbs : |mu| = 1 := by
    change |(ArithmeticFunction.moebius a : ℝ)| = 1
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree haSq
  have hcoeff (d : ℕ) : |coeff d| ≤ 1 := by
    dsimp [coeff]
    split_ifs with h
    · rw [abs_mul, hmuAbs, one_mul]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (q : ℕ) * d)
    · norm_num
  have hnewcoeff (d : ℕ) : |-mu * coeff d| ≤ 1 := by
    rw [abs_mul, abs_neg, hmuAbs, one_mul]
    exact hcoeff d
  have hcoeffOne : (-mu * coeff 1) = 1 := by
    simp [coeff, ArithmeticFunction.moebius_apply_prime q.property]
    nlinarith
  have hq3 : 3 ≤ (q : ℕ) := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hqBig : (128 : ℝ) ≤ (q : ℝ) := by nlinarith
    exact_mod_cast (show (3 : ℝ) ≤ (q : ℝ) by linarith)
  have hpos := routeEFixedOrderCofactorFibre_gt_fraction hr
    (by exact_mod_cast ha : (0 : ℝ) < a) hq3 hq128
    (fun d => -mu * coeff d) hnewcoeff hcoeffOne
  have hlinear : routeEFixedOrderCofactorFibre r (a : ℝ) (q : ℕ)
      (fun d => -mu * coeff d) =
      -mu * routeEFixedOrderCofactorFibre r (a : ℝ) (q : ℕ) coeff := by
    unfold routeEFixedOrderCofactorFibre
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  change (1 / 48 : ℝ) * routeEFixedOrderDifference r (a : ℝ) (q : ℝ) <
    -mu * routeEFixedOrderCofactorFibre r (a : ℝ) (q : ℕ) coeff
  rw [← hlinear]
  exact hpos

theorem routeEFixedOrderDifference_scale
    {r a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q) :
    routeEFixedOrderDifference r a q =
      q ^ (-r) * routeEFixedOrderDifference r (a / q) 1 := by
  have h1 : a + q = q * (a / q + 1) := by
    field_simp
  have h2 : 2 * a + q = q * (2 * (a / q) + 1) := by
    field_simp
  unfold routeEFixedOrderDifference
  rw [h1, h2, Real.mul_rpow hq.le (by positivity),
    Real.mul_rpow hq.le (by positivity)]
  ring

theorem routeEFixedOrderDifference_continuousOn_ratio
    (r α β : ℝ) (hα : 0 < α) :
    ContinuousOn (fun t : ℝ => routeEFixedOrderDifference r t 1) (Icc α β) := by
  have hc1 : ContinuousOn (fun t : ℝ => t + 1) (Icc α β) := by fun_prop
  have hc2 : ContinuousOn (fun t : ℝ => 2 * t + 1) (Icc α β) := by fun_prop
  have hp1 : ContinuousOn (fun t : ℝ => (t + 1) ^ (-r)) (Icc α β) :=
    hc1.rpow_const (fun t ht => Or.inl (ne_of_gt (by linarith [ht.1] : 0 < t + 1)))
  have hp2 : ContinuousOn (fun t : ℝ => (2 * t + 1) ^ (-r)) (Icc α β) :=
    hc2.rpow_const (fun t ht => Or.inl (ne_of_gt (by linarith [ht.1] : 0 < 2 * t + 1)))
  convert hp1.sub hp2 using 1
  funext t
  rfl

/-- Positive compact ratio floor for the source edge at a fixed exponent. -/
theorem exists_routeEFixedOrderRatioFloor
    {r α β : ℝ} (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Icc α β,
      m ≤ routeEFixedOrderDifference r t 1 := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨α, ⟨le_rfl, hαβ⟩⟩
    (routeEFixedOrderDifference_continuousOn_ratio r α β hα)
  refine ⟨routeEFixedOrderDifference r t₀ 1,
    routeEFixedOrderDifference_pos hr (lt_of_lt_of_le hα ht₀.1) (by norm_num), ?_⟩
  intro t ht
  exact hmin ht

/-- On a compact proportional prime-pair band, the literal full-cofactor
source retains a fixed positive fraction of its homogeneous main edge. -/
theorem exists_routeEPrimeBandFloor
    {r : ℝ} (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : Nat.Primes,
      (1 / 1024 : ℝ) ≤ ((p : ℝ) / (q : ℝ)) →
      ((p : ℝ) / (q : ℝ)) ≤ (1 / 256 : ℝ) →
      C * (q : ℝ) ^ (-r) ≤ routeEFixedOrderPrimeFibre r p q := by
  obtain ⟨m, hm, hmin⟩ := exists_routeEFixedOrderRatioFloor
    (r := r) (α := (1 / 1024 : ℝ)) (β := (1 / 256 : ℝ))
    (by linarith) (by norm_num) (by norm_num)
  refine ⟨m / 48, by positivity, ?_⟩
  intro p q hlo hhi
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property.pos
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hp_le : (p : ℝ) ≤ (1 / 256 : ℝ) * (q : ℝ) :=
    (div_le_iff₀ hq0).mp hhi
  have hq128 : 128 * (p : ℝ) ≤ (q : ℝ) := by linarith
  have hq3 : 3 ≤ (q : ℕ) := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    exact_mod_cast (show (3 : ℝ) ≤ (q : ℝ) by linarith)
  have hc1 :
      (if Nat.Coprime (p : ℕ) 1 then
        (ArithmeticFunction.moebius (p : ℕ) : ℝ) *
          (ArithmeticFunction.moebius ((q : ℕ) * 1) : ℝ)
      else 0) = 1 := by
    simp [ArithmeticFunction.moebius_apply_prime p.property,
      ArithmeticFunction.moebius_apply_prime q.property]
  have hrel : (1 / 48 : ℝ) * routeEFixedOrderDifference r (p : ℝ) (q : ℝ) <
      routeEFixedOrderPrimeFibre r p q := by
    exact routeEFixedOrderCofactorFibre_gt_fraction hr hp0 hq3 hq128 _
      (routeEFixedOrderPrimeFibre_coeff_bound p q) hc1
  have hmFloor : m ≤ routeEFixedOrderDifference r ((p : ℝ) / (q : ℝ)) 1 :=
    hmin _ ⟨hlo, hhi⟩
  have hscale := routeEFixedOrderDifference_scale
    (r := r) (a := (p : ℝ)) (q := (q : ℝ)) hp0.le hq0
  calc
    (m / 48) * (q : ℝ) ^ (-r) =
        (1 / 48 : ℝ) * ((q : ℝ) ^ (-r) * m) := by ring
    _ ≤ (1 / 48 : ℝ) * ((q : ℝ) ^ (-r) *
          routeEFixedOrderDifference r ((p : ℝ) / (q : ℝ)) 1) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmFloor (by positivity)) (by norm_num)
    _ = (1 / 48 : ℝ) * routeEFixedOrderDifference r (p : ℝ) (q : ℝ) := by
      rw [hscale]
    _ ≤ routeEFixedOrderPrimeFibre r p q := hrel.le

/-- The adjacent composite grade has a uniform negative source floor on the
same proportional band; this is a distinct literal numerator channel. -/
theorem exists_routeECompositeBandFloor
    {r : ℝ} (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : Nat.Primes,
      3 ≤ (p : ℕ) →
      (1 / 1024 : ℝ) ≤ ((p : ℝ) / (q : ℝ)) →
      ((p : ℝ) / (q : ℝ)) ≤ (1 / 256 : ℝ) →
      routeEFixedOrderIntegerNumeratorFibre r (2 * (p : ℕ)) q ≤
        -C * (q : ℝ) ^ (-r) := by
  obtain ⟨m, hm, hmin⟩ := exists_routeEFixedOrderRatioFloor
    (r := r) (α := (1 / 512 : ℝ)) (β := (1 / 128 : ℝ))
    (by linarith) (by norm_num) (by norm_num)
  refine ⟨m / 48, by positivity, ?_⟩
  intro p q hp3 hlo hhi
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property.pos
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hp_le : (p : ℝ) ≤ (1 / 256 : ℝ) * (q : ℝ) :=
    (div_le_iff₀ hq0).mp hhi
  have hq128 : 128 * ((2 * (p : ℕ) : ℕ) : ℝ) ≤ (q : ℝ) := by
    push_cast
    linarith
  have hpodd : Odd (p : ℕ) := p.property.odd_of_ne_two (by omega)
  have hcop : Nat.Coprime 2 (p : ℕ) := hpodd.coprime_two_left
  have hsq : Squarefree (2 * (p : ℕ)) :=
    Nat.squarefree_mul_iff.mpr ⟨hcop, Nat.prime_two.squarefree, p.property.squarefree⟩
  have hmu : (ArithmeticFunction.moebius (2 * (p : ℕ)) : ℝ) = 1 := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime p.property]
    norm_num
  have hmargin := routeEFixedOrderIntegerNumeratorFibre_margin hr
    (by omega : 0 < 2 * (p : ℕ)) hsq q hq128
  rw [hmu] at hmargin
  have hmFloor : m ≤ routeEFixedOrderDifference r
      (((2 * (p : ℕ) : ℕ) : ℝ) / (q : ℝ)) 1 := by
    apply hmin
    have hratio : (((2 * (p : ℕ) : ℕ) : ℝ) / (q : ℝ)) =
        2 * ((p : ℝ) / (q : ℝ)) := by push_cast; ring
    rw [hratio]
    constructor <;> linarith
  have hscale := routeEFixedOrderDifference_scale
    (r := r) (a := ((2 * (p : ℕ) : ℕ) : ℝ)) (q := (q : ℝ))
    (by positivity) hq0
  have hbound : (m / 48) * (q : ℝ) ^ (-r) ≤
      (1 / 48 : ℝ) * routeEFixedOrderDifference r
        ((2 * (p : ℕ) : ℕ) : ℝ) (q : ℝ) := by
    calc
      _ = (1 / 48 : ℝ) * ((q : ℝ) ^ (-r) * m) := by ring
      _ ≤ (1 / 48 : ℝ) * ((q : ℝ) ^ (-r) *
          routeEFixedOrderDifference r
            (((2 * (p : ℕ) : ℕ) : ℝ) / (q : ℝ)) 1) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmFloor (by positivity)) (by norm_num)
      _ = (1 / 48 : ℝ) * routeEFixedOrderDifference r
          ((2 * (p : ℕ) : ℕ) : ℝ) (q : ℝ) := by rw [hscale]
  linarith

end
end RHTower
