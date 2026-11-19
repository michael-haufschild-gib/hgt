import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheLogarithmicDivisorRowsAtThePrimeMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SmoothPrimeTriplesBelowTheMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMidpointInTwoAdjacentGcdHorizons
import GaloisForLFunctions.RHTower.MobiusDivisorSectionSignLaw

/-!
# Completion of the short divisor rows at the cubic prime midpoint

The same divisor cutoff applies to all three product endpoints. Transposing
the truncated convolution exposes the ordinary and divisor-counting log rows
at their exact integer quotients.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def divisorLogPrefix (T d : ℕ) : ℝ :=
  ∑ r ∈ Icc 1 (T/d), Real.log (d*r:ℕ)*(r.divisors.card:ℝ)

private theorem scaled_log_prefix {d : ℕ} (hd : 0 < d) (T : ℕ) :
    (∑ r ∈ Icc 1 (T/d),Real.log (d*r:ℕ))=progressionLogFactorial d T := by
  have hl (r : ℕ) (hr : r ∈ Icc 1 (T/d)) : Real.log (d*r:ℕ)=Real.log d+Real.log r := by
    rw [Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr hd.ne')
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mem_Icc.mp hr).1))]
  rw [sum_congr rfl hl,sum_add_distrib,sum_const,nsmul_eq_mul,Nat.card_Icc,
    Nat.add_one_sub_one,_root_.RHTower.Sieve.sum_Icc_log_eq_log_factorial,progressionLogFactorial]

private theorem zeta_squared_value (r : ℕ) :
    ((zeta:ArithmeticFunction ℝ)^2 : ArithmeticFunction ℝ) r=r.divisors.card := by
  rw [pow_two,coe_mul_zeta_apply]
  calc _ = ∑ _ ∈ r.divisors,(1:ℝ) := by
             apply sum_congr rfl
             intro j hj
             rw [natCoe_apply,zeta_apply_ne (Nat.pos_of_mem_divisors hj).ne',Nat.cast_one]
       _ = _ := by simp

/-- Twice the log price of the short divisors through a single product endpoint. -/
def cubicShortDivisorPrefix (Y D T : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 T,twiceLowDivisorWeight Y D k*Real.log k

private theorem short_divisor_prefix (Y : ℕ) {D T : ℕ} (hD : D ≤ T) :
    cubicShortDivisorPrefix Y D T =
      ∑ d ∈ Icc 1 D,(4*cubicSmoothMoebius Y d*progressionLogFactorial d T-
        (cubicSmoothMoebius Y^2 : ArithmeticFunction ℝ) d*divisorLogPrefix T d) := by
  let A := cubicSmoothMoebius Y
  let f (d k : ℕ) := if d ≤ D then
    (4*A d-(A^2 : ArithmeticFunction ℝ) d*((k/d).divisors.card:ℝ))*Real.log k else 0
  let G (d : ℕ) := ∑ r ∈ Icc 1 (T/d),f d (d*r)
  have hleft (k : ℕ) : (∑ d ∈ k.divisors,f d k)=twiceLowDivisorWeight Y D k*Real.log k := by
    simp only [twiceLowDivisorWeight,zeta_squared_value,sum_mul,sum_filter,f,A,ite_mul,zero_mul]
  have he := _root_.RHTower.sum_Icc_sum_Icc_div_eq_sum_divisors T f
  simp_rw [hleft] at he
  have he' : (∑ d ∈ Icc 1 D,G d)=∑ d ∈ Icc 1 T,G d := by
    apply sum_subset (Icc_subset_Icc_right hD)
    intro d hd hnot
    have h : ¬d ≤ D := fun hh => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,hh⟩)
    simp only [G,f,if_neg h,sum_const_zero]
  change (∑ d ∈ Icc 1 T,G d)=cubicShortDivisorPrefix Y D T at he
  rw [←he,←he']
  apply sum_congr rfl
  intro d hd
  obtain ⟨hd1,hdD⟩ := mem_Icc.mp hd
  simp only [G,f,if_pos hdD,Nat.mul_div_cancel_left _ hd1,sub_mul,sum_sub_distrib,
    divisorLogPrefix,←scaled_log_prefix hd1 T,mul_sum,A]
  congr 1
  apply sum_congr rfl
  intro r _
  ring

private theorem row_as_prefix_difference (n d i : ℕ) :
    midpointDivisorRow n d i=divisorLogPrefix ((i+1)*n) d-divisorLogPrefix (i*n) d := by
  have hfloor (j : ℕ) : ⌊((n:ℝ)/d)*j⌋₊=j*n/d := by
    rw [show (n:ℝ)/d*j=((j*n:ℕ):ℝ)/d by push_cast; ring,
      Nat.floor_div_natCast,Nat.floor_natCast]
  have hset (t : ℕ) : Icc 1 t=Ioc 0 t := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  simp only [midpointDivisorRow,divisorLogPrefix,←Nat.cast_succ,hfloor,hset]
  exact eq_sub_of_add_eq' (sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.div_le_div_right
    (Nat.mul_le_mul_right n (Nat.le_succ i))))

/-- Signed integral center of both completed divisor rows. -/
def cubicShortDivisorIntegral (n : ℕ) : ℝ :=
  let Y := cubicMidpointCut n
  ∑ d ∈ Icc 1 (4*n/(Y+1)),(2*cubicSmoothMoebius Y d*((n:ℝ)/d)*midpointLogMoment 1-
    (cubicSmoothMoebius Y^2 : ArithmeticFunction ℝ) d/2*((n:ℝ)/d)*
      (midpointLogMoment 2+midpointLogMoment 1*(2*Real.log n+2*Real.eulerMascheroniConstant-Real.log d)))

/-- At every admissible integer midpoint, the actual short-divisor log
price differs from its two signed integral moments by O(n^(5/6+ε)). -/
theorem sharp_cubic_short_divisor_center {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ {n : ℕ}, 3 ≤ cubicMidpointCut n →
      let Y := cubicMidpointCut n
      let S := cubicShortDivisorPrefix Y (4*n/(Y+1))
      |(S (4*n)-2*S (3*n)+S (2*n))/2-cubicShortDivisorIntegral n| ≤ C*(n:ℝ)^(5/6+ε) := by
  obtain ⟨C,hC⟩ := cubic_complete_row_replacement hε
  refine ⟨C,?_⟩
  intro n hY
  let Y := cubicMidpointCut n
  let D := 4*n/(Y+1)
  let S := cubicShortDivisorPrefix Y D
  have hDn : D ≤ n := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos Y)).mpr
    exact (show 4*n<(n+1)*4 by omega).trans_le
      (Nat.mul_le_mul_left (n+1) (show 4 ≤ Y+1 by omega))
  have he : (S (4*n)-2*S (3*n)+S (2*n))/2-cubicShortDivisorIntegral n =
      ∑ d ∈ Icc 1 D,(2*cubicSmoothMoebius Y d*ordinaryMidpointRowRemainder n d-
        (cubicSmoothMoebius Y^2 : ArithmeticFunction ℝ) d*midpointDivisorRemainder n d/2) := by
    dsimp only [S,cubicShortDivisorIntegral]
    rw [short_divisor_prefix Y (show D ≤ 4*n by omega),short_divisor_prefix Y (show D ≤ 3*n by omega),
      short_divisor_prefix Y (show D ≤ 2*n by omega)]
    change ((∑ d ∈ Icc 1 D, _)-2*(∑ d ∈ Icc 1 D, _)+(∑ d ∈ Icc 1 D, _))/2-
      (∑ d ∈ Icc 1 D, _)=_
    rw [mul_sum,←sum_sub_distrib,←sum_add_distrib,sum_div,←sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    simp only [ordinaryMidpointRowRemainder,midpointDivisorRemainder,row_as_prefix_difference]
    norm_num only [show (3:ℕ)+1=4 by decide,show (2:ℕ)+1=3 by decide]
    ring
  change |(S (4*n)-2*S (3*n)+S (2*n))/2-cubicShortDivisorIntegral n| ≤ _
  rw [he]
  exact hC hY

/-- Remaining log price of a product, combining its long-divisor term and
the ordered triples of rough ordinary primes at the same endpoint. -/
def cubicUncompletedProductPrice (n k : ℕ) : ℝ :=
  let Y := cubicMidpointCut n
  (twiceHighDivisorWeight Y (4*n/(Y+1)) k/2+
    (cubicPrimeIndicator Y^3 : ArithmeticFunction ℝ) k/3)*Real.log k

private theorem low_price_interval {n a b : ℕ} (hY : 3 ≤ cubicMidpointCut n)
    (hab : a ≤ b) (hcap : b ≤ 4*n) :
    let Y := cubicMidpointCut n
    let S := cubicShortDivisorPrefix Y (4*n/(Y+1))
    (∑ k ∈ Ioc a b,(cubicRoughMangoldt Y k-cubicUncompletedProductPrice n k)) =
      (S b-S a)/2 := by
  let Y := cubicMidpointCut n
  let D := 4*n/(Y+1)
  let f := fun k : ℕ => twiceLowDivisorWeight Y D k*Real.log k
  have h (k : ℕ) (hk : k ∈ Ioc a b) :
      cubicRoughMangoldt Y k-cubicUncompletedProductPrice n k=f k/2 := by
    have he := cubic_divisor_and_triple_decomposition hY ((mem_Ioc.mp hk).2.trans hcap)
    change 2*cubicRoughMangoldt Y k=(twiceLowDivisorWeight Y D k+twiceHighDivisorWeight Y D k)*Real.log k+
      (2/3:ℝ)*(cubicPrimeIndicator Y^3 : ArithmeticFunction ℝ) k*Real.log k at he
    change cubicRoughMangoldt Y k-(twiceHighDivisorWeight Y D k/2+
      (cubicPrimeIndicator Y^3 : ArithmeticFunction ℝ) k/3)*Real.log k=_
    dsimp only [f]
    linarith only [he]
  have hset (t : ℕ) : Icc 1 t=Ioc 0 t := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  dsimp only
  rw [sum_congr rfl h,←sum_div]
  simp only [cubicShortDivisorPrefix,hset]
  exact congrArg (· / (2:ℝ)) (eq_sub_of_add_eq' (sum_Ioc_consecutive f (Nat.zero_le a) hab))

private theorem rough_midpoint_proper_power_cost {n : ℕ} (hY : 3 ≤ cubicMidpointCut n) :
    let Y := cubicMidpointCut n
    |primeMidpointPrice n+((∑ k ∈ Ioc (3*n) (4*n),cubicRoughMangoldt Y k)-
      ∑ k ∈ Ioc (2*n) (3*n),cubicRoughMangoldt Y k)| ≤ Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ) := by
  let Y := cubicMidpointCut n
  let E := fun k : ℕ => cubicRoughMangoldt Y k-(if k.Prime then Real.log k else 0)
  have hcube : Y^3 ≤ 3*n := (cubic_midpoint_thresholds n hY).1
  have h3 : 3*Y^2 ≤ Y^3 := by rw [pow_succ Y 2,Nat.mul_comm (Y^2)]; exact Nat.mul_le_mul_right _ hY
  have hy2 : Y ≤ Y^2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right Y (by omega)
  have hcut : Y ≤ 2*n := by omega
  have point {k : ℕ} (hk : Y < k) :
      0 ≤ E k ∧ E k ≤ (if ¬k.Prime then vonMangoldt k else 0) := by
    change 0 ≤ (if (primorial Y).Coprime k then vonMangoldt k else 0)-
      (if k.Prime then Real.log k else 0) ∧ _ ≤ _
    by_cases hp : k.Prime
    · have hc := (hp.coprime_iff_not_dvd.mpr (fun h => hk.not_ge (hp.dvd_primorial_iff.mp h))).symm
      dsimp only [E,cubicRoughMangoldt]
      change 0 ≤ (if (primorial Y).Coprime k then vonMangoldt k else 0)-_ ∧
        (if (primorial Y).Coprime k then vonMangoldt k else 0)-_ ≤ _
      simp only [hc,if_true,hp,not_true_eq_false,if_false,vonMangoldt_apply_prime hp,sub_self,le_refl,and_self]
    · change 0 ≤ (if (primorial Y).Coprime k then vonMangoldt k else 0)-_ ∧
        (if (primorial Y).Coprime k then vonMangoldt k else 0)-_ ≤ _
      simp only [if_neg hp,if_pos hp,sub_zero]
      split_ifs <;> simp [vonMangoldt_nonneg]
  have cost (a b : ℕ) (ha : Y ≤ a) (hb : b ≤ 4*n) :
      0 ≤ ∑ k ∈ Ioc a b,E k ∧ (∑ k ∈ Ioc a b,E k) ≤
        Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ) := by
    refine ⟨sum_nonneg fun k hk => (point (ha.trans_lt (mem_Ioc.mp hk).1)).1,?_⟩
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,sum_filter]
    apply (sum_le_sum fun k hk => (point (ha.trans_lt (mem_Ioc.mp hk).1)).2).trans
    apply sum_le_sum_of_subset_of_nonneg
    · exact fun k hk => mem_Ioc.mpr ⟨(Nat.zero_le a).trans_lt (mem_Ioc.mp hk).1,(mem_Ioc.mp hk).2.trans hb⟩
    · intro k _ _
      split_ifs <;> simp [vonMangoldt_nonneg]
  have hl := cost (2*n) (3*n) hcut (by omega)
  have hr := cost (3*n) (4*n) (by omega) le_rfl
  simp only [E,sum_sub_distrib] at hl hr
  simp only [primeMidpointPrice,sum_filter,abs_le]
  constructor <;> linarith only [hr.1,hr.2,hl.1,hl.2]

/-- The ordinary-prime midpoint is minus its explicit divisor center and
minus the signed price of the surviving products, to five-sixths-plus precision. -/
theorem ordinary_prime_midpoint_cubic_center {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ {n : ℕ}, 3 ≤ cubicMidpointCut n →
      |primeMidpointPrice n+cubicShortDivisorIntegral n+
        ((∑ k ∈ Ioc (3*n) (4*n),cubicUncompletedProductPrice n k)-
         ∑ k ∈ Ioc (2*n) (3*n),cubicUncompletedProductPrice n k)| ≤ C*(n:ℝ)^(5/6+ε) := by
  obtain ⟨C,hC⟩ := sharp_cubic_short_divisor_center hε
  obtain ⟨A,hA⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨C+2*|A|,?_⟩
  intro n hY
  have hn : 0 < n := by
    by_contra! hz
    obtain rfl : n=0 := by omega
    norm_num [cubicMidpointCut,Real.zero_rpow] at hY
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  let Y := cubicMidpointCut n
  let S := cubicShortDivisorPrefix Y (4*n/(Y+1))
  let P := (n:ℝ)^(5/6+ε)
  have ha := (rough_midpoint_proper_power_cost hY).trans (hA ((4*n:ℕ):ℝ))
  have hs : Real.sqrt ((4*n:ℕ):ℝ) ≤ 2*P := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num,Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])) (by norm_num)
  have hb := ha.trans (mul_le_mul (le_abs_self A) hs (Real.sqrt_nonneg _) (abs_nonneg _))
  have hr := low_price_interval (n:=n) (a:=3*n) (b:=4*n) hY (by omega) le_rfl
  have hl := low_price_interval (n:=n) (a:=2*n) (b:=3*n) hY (by omega) (by omega)
  have hc := hC hY
  dsimp only at hr hl hc hb
  simp only [sum_sub_distrib] at hr hl
  change |(S (4*n)-2*S (3*n)+S (2*n))/2-cubicShortDivisorIntegral n| ≤ C*P at hc
  change (∑ k ∈ Ioc (3*n) (4*n),cubicRoughMangoldt Y k)-
    (∑ k ∈ Ioc (3*n) (4*n),cubicUncompletedProductPrice n k)=(S (4*n)-S (3*n))/2 at hr
  change (∑ k ∈ Ioc (2*n) (3*n),cubicRoughMangoldt Y k)-
    (∑ k ∈ Ioc (2*n) (3*n),cubicUncompletedProductPrice n k)=(S (3*n)-S (2*n))/2 at hl
  change |primeMidpointPrice n+((∑ k ∈ Ioc (3*n) (4*n),cubicRoughMangoldt Y k)-
    ∑ k ∈ Ioc (2*n) (3*n),cubicRoughMangoldt Y k)| ≤ |A|*(2*P) at hb
  change |_ | ≤ (C+2*|A|)*P
  rw [abs_le]
  constructor <;> linarith only [hr,hl,(abs_le.mp hb).1,(abs_le.mp hb).2,(abs_le.mp hc).1,(abs_le.mp hc).2]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
