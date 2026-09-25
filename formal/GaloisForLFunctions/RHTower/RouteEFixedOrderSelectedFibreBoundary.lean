import GaloisForLFunctions.RHTower.RouteETerminalSourceReporterFirewall
import GaloisForLFunctions.RHTower.RouteEPrimitiveConeParentNoGo

/-! Fixed-order test of the Route E largest-prime cofactor mechanism.
For 1 < r ≤ 2, every coefficient-bounded single numerator channel with
numerator at most q is absolutely summable over denominator primes q.
This is a boundary/receiver quantifier no-go, not a full-covariance bound. -/

open Finset
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

end
end RHTower
