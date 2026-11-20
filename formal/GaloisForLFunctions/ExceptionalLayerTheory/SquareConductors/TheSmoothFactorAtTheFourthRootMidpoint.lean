import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheTotientTermInTheReflectedCompositePrice
import GaloisForLFunctions.RHTower.Sieve.SmoothRough
import GaloisForLFunctions.RHTower.TruncatedMoebiusResidual

/-!
# The smooth factor at a fourth-root midpoint cutoff

The logarithms removed from the complementary cofactor occur on rows
indexed by one small Möbius divisor and one prime power. Their least
common multiple is the actual period in the two adjacent intervals.
-/

noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open _root_.RHTower.Sieve (smoothPart roughPart)
open _root_.RHTower (truncMoebiusDivisorSum)
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Every divisor through the cutoff divides the smooth part. -/
theorem truncated_weight_on_smooth_factor {k : ℕ} (hk : 0 < k) (Y : ℕ) :
    truncMoebiusDivisorSum Y k=truncMoebiusDivisorSum Y (smoothPart Y k) := by
  unfold _root_.RHTower.truncMoebiusDivisorSum
  congr 1
  apply filter_congr
  intro e he
  obtain ⟨he0,heY⟩ := mem_Icc.mp he
  have hc : e.Coprime (roughPart Y k) := by
    unfold _root_.RHTower.Sieve.roughPart
    apply Nat.Coprime.prod_right
    intro p hp
    obtain ⟨hp0,hpY⟩ := mem_filter.mp hp
    exact ((Nat.prime_of_mem_primeFactors hp0).coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt he0 (heY.trans_lt (lt_of_not_ge hpY)))).symm.pow_right _
  nth_rw 1 [←_root_.RHTower.Sieve.smoothPart_mul_roughPart hk.ne' Y]
  exact hc.dvd_mul_right

/-- A nonunit whose squarefree radical is within the sieve level has
zero divisor weight, regardless of the multiplicities of its primes. -/
theorem truncated_weight_below_radical {k Y : ℕ} (hk : 1<k)
    (hY : (∏ p ∈ k.primeFactors,p) ≤ Y) : truncMoebiusDivisorSum Y k=0 := by
  have hk0 := zero_lt_one.trans hk
  let S := (Icc 1 Y).filter (· ∣ k)
  have hsub : S ⊆ k.divisors := fun _ he => Nat.mem_divisors.mpr ⟨(mem_filter.mp he).2,hk0.ne'⟩
  have he : (∑ e ∈ S,(μ e:ℝ))=∑ e ∈ k.divisors,(μ e:ℝ) := by
    apply sum_subset hsub
    intro d hd hn
    have hdiv := Nat.dvd_of_mem_divisors hd
    have hcut : ¬d ≤ Y := fun h => hn (mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,h⟩,hdiv⟩)
    have hns : ¬Squarefree d := by
      intro hsq
      have hs : d.primeFactors ⊆ k.primeFactors := fun p hp => Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hp,(Nat.dvd_of_mem_primeFactors hp).trans hdiv,hk0.ne'⟩
      have hdvd := prod_dvd_prod_of_subset d.primeFactors k.primeFactors id hs
      change (∏ p ∈ d.primeFactors,p) ∣ (∏ p ∈ k.primeFactors,p) at hdvd
      rw [Nat.prod_primeFactors_of_squarefree hsq] at hdvd
      exact hcut ((Nat.le_of_dvd (prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos) hdvd).trans hY)
    rw [moebius_eq_zero_of_not_squarefree hns,Int.cast_zero]
  change (∑ e ∈ S,(μ e:ℝ))=0
  rw [he,←Int.cast_sum,_root_.RHTower.sum_moebius_divisors,if_neg hk.ne',Int.cast_zero]

/-- At most three rough prime factors occur below the fourth power.
A surviving mixed product has at most two, and its smooth radical exceeds the cut. -/
theorem fourth_root_surviving_factors {k Y : ℕ} (hk : 0<k) (hY : 1 ≤ Y) (hcap : k ≤ Y^4) :
    let s := smoothPart Y k
    let r := roughPart Y k
    r.primeFactorsList.length ≤ 3 ∧
      (1<s → truncMoebiusDivisorSum Y k ≠ 0 →
        Y < (∏ p ∈ s.primeFactors,p) ∧ r.primeFactorsList.length ≤ 2) := by
  intro s r
  have hr := _root_.RHTower.Sieve.roughPart_pos Y k
  have hs := _root_.RHTower.Sieve.smoothPart_pos Y k
  have prod : s*r=k := _root_.RHTower.Sieve.smoothPart_mul_roughPart hk.ne' Y
  have lower (p : ℕ) (hp : p ∈ r.primeFactorsList) : Y+1 ≤ p := by
    have h := Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactorsList hp,Nat.dvd_of_mem_primeFactorsList hp,hr.ne'⟩
    change p ∈ (roughPart Y k).primeFactors at h
    rw [_root_.RHTower.Sieve.primeFactors_roughPart hk.ne'] at h
    exact lt_of_not_ge (mem_filter.mp h).2
  have bound (l : List ℕ) : (∀ p ∈ l,Y+1 ≤ p) → (Y+1)^l.length ≤ l.prod := by
    induction l with
    | nil => simp
    | cons p l ih =>
      intro h
      rw [List.length_cons,List.prod_cons,pow_succ,Nat.mul_comm ((Y+1)^l.length)]
      exact Nat.mul_le_mul (h _ (List.mem_cons_self ..)) (ih fun q hq => h q (List.mem_cons_of_mem _ hq))
  have base := bound r.primeFactorsList lower
  rw [Nat.prod_primeFactorsList hr.ne'] at base
  have h4 : Y^4 < (Y+1)^4 := Nat.pow_lt_pow_left (Nat.lt_succ_self Y) (by decide)
  constructor
  · by_contra! h
    have hlarge := (Nat.pow_le_pow_right (Nat.succ_pos Y) h).trans base
    have hrk : r ≤ k := Nat.le_of_dvd hk (_root_.RHTower.Sieve.roughPart_dvd Y k)
    exact h4.not_ge (hlarge.trans (hrk.trans hcap))
  · intro hmix hw
    have hcut : Y < ∏ p ∈ s.primeFactors,p := by
      by_contra! hz
      exact hw ((truncated_weight_on_smooth_factor hk Y).trans (truncated_weight_below_radical hmix hz))
    refine ⟨hcut,?_⟩
    by_contra! h
    have hlarge := (Nat.pow_le_pow_right (Nat.succ_pos Y) h).trans base
    have hsy := hcut.trans_le (Nat.le_of_dvd hs (Nat.prod_primeFactors_dvd s))
    have hprod := Nat.mul_le_mul hlarge hsy
    rw [←pow_succ,Nat.mul_comm r s,prod] at hprod
    exact h4.not_ge (hprod.trans hcap)

private theorem small_factor_log_sum {k X : ℕ} (hk : 0 < k) (hX : k ≤ X) (Y : ℕ) :
    Real.log (smoothPart Y k)=∑ p ∈ Nat.primesLE Y,∑ j ∈ Icc 1 (Nat.log p X),
      if p^j ∣ k then Real.log p else 0 := by
  let S := k.primeFactors.filter (· ≤ Y)
  have hsub : S ⊆ Nat.primesLE Y := fun p hp => Nat.mem_primesLE.mpr
    ⟨(mem_filter.mp hp).2,Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1⟩
  have hex : (∑ p ∈ S,(k.factorization p:ℝ)*Real.log p)=
      ∑ p ∈ Nat.primesLE Y,(k.factorization p:ℝ)*Real.log p := by
    apply sum_subset hsub
    intro p hp hnot
    have hnd : ¬p ∣ k := fun hd => hnot (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primesLE hp,hd,hk.ne'⟩,(Nat.mem_primesLE.mp hp).1⟩)
    rw [Nat.factorization_eq_zero_of_not_dvd hnd,Nat.cast_zero,zero_mul]
  have hlog : Real.log (smoothPart Y k)=∑ p ∈ S,(k.factorization p:ℝ)*Real.log p := by
    rw [_root_.RHTower.Sieve.smoothPart,Nat.cast_prod,Real.log_prod]
    · exact sum_congr rfl fun p _ => by rw [Nat.cast_pow,Real.log_pow]
    · intro p hp
      exact Nat.cast_ne_zero.mpr (pow_pos (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos _).ne'
  rw [hlog,hex]
  apply sum_congr rfl
  intro p hp
  have hpr := Nat.prime_of_mem_primesLE hp
  have hpow := Nat.le_of_dvd hk ((hpr.pow_dvd_iff_le_factorization hk.ne').mpr (le_refl (k.factorization p)))
  have hbound : k.factorization p ≤ Nat.log p X := Nat.le_log_of_pow_le hpr.one_lt (hpow.trans hX)
  have hs : (Icc 1 (Nat.log p X)).filter (fun j => p^j ∣ k)=Icc 1 (k.factorization p) := by
    ext j
    simp only [mem_filter,mem_Icc,hpr.pow_dvd_iff_le_factorization hk.ne']
    omega
  rw [←sum_filter,hs,sum_const,Nat.card_Icc,Nat.add_one_sub_one,nsmul_eq_mul]

private def primitiveMultiple (n u k : ℕ) : ℝ := if n.Coprime k ∧ u ∣ k then 1 else 0

private theorem primitive_multiple_second_difference {u : ℕ} (hu : 0<u) (n : ℕ) :
    (∑ k ∈ Ioc (3*n) (4*n),primitiveMultiple n u k)-
      (∑ k ∈ Ioc (2*n) (3*n),primitiveMultiple n u k)=coprimeMidpointMultipleCount n u := by
  let F (T : ℕ) := ∑ k ∈ Icc 1 T,primitiveMultiple n u k
  let C (T : ℕ) := (((Icc 1 (T/u)).filter (n.Coprime ·)).card:ℝ)
  have pref (T : ℕ) : F T=if n.Coprime u then C T else 0 := by
    change (∑ k ∈ Icc 1 T,(if n.Coprime k ∧ u ∣ k then (1:ℝ) else 0))=_
    have term (k : ℕ) : (if n.Coprime k ∧ u ∣ k then (1:ℝ) else 0)=
        if u ∣ k then (if n.Coprime k then 1 else 0) else 0 := by split_ifs <;> simp_all
    simp_rw [term]
    rw [←sum_filter,_root_.RHTower.Sieve.sum_filter_dvd_eq_sum_scaled hu]
    simp only [Nat.coprime_mul_iff_right]
    by_cases hc : n.Coprime u
    · simp only [and_iff_right hc,if_pos hc]
      rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
    · have off (j : ℕ) : ¬(n.Coprime u ∧ n.Coprime j) := fun h => hc h.1
      simp only [if_neg hc,if_neg (off _),sum_const_zero]
  have inter (a b : ℕ) (hab : a ≤ b) :
      (∑ k ∈ Ioc a b,primitiveMultiple n u k)=F b-F a := by
    have he (t : ℕ) : Icc 1 t=Ioc 0 t := by ext j; simp only [mem_Icc,mem_Ioc]; omega
    simp only [F,he]
    exact eq_sub_of_add_eq' (sum_Ioc_consecutive _ (Nat.zero_le a) hab)
  rw [inter _ _ (by omega),inter _ _ (by omega),pref,pref,pref]
  change _=if n.Coprime u then C (4*n)-2*C (3*n)+C (2*n) else 0
  split_ifs <;> ring

private def weightedSmoothLog (n Y k : ℕ) : ℝ :=
  if n.Coprime k then truncMoebiusDivisorSum Y k*Real.log (smoothPart Y k) else 0

private theorem weighted_smooth_log_rows {k X : ℕ} (hk : 0 < k) (hX : k ≤ X) (n Y : ℕ) :
    weightedSmoothLog n Y k =
    ∑ e ∈ Icc 1 Y,∑ p ∈ Nat.primesLE Y,∑ j ∈ Icc 1 (Nat.log p X),
      (μ e:ℝ)*Real.log p*primitiveMultiple n (e.lcm (p^j)) k := by
  rw [weightedSmoothLog,small_factor_log_sum hk hX,_root_.RHTower.truncMoebiusDivisorSum,sum_filter]
  by_cases hc : n.Coprime k
  · rw [if_pos hc,sum_mul]
    simp only [mul_sum]
    apply sum_congr rfl
    intro e _
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro j _
    by_cases he : e ∣ k <;> by_cases hj : p^j ∣ k <;>
      simp [primitiveMultiple,Nat.lcm_dvd_iff,he,hj,if_pos hc]
  · simp [hc,primitiveMultiple]

/-- The signed log price removed by replacing each integer with its
rough factor costs at most one endpoint per Möbius divisor and prime power. -/
theorem quarter_smooth_logarithm_cost {n : ℕ} (hn : 0<n) (Y : ℕ) :
    |(∑ k ∈ Ioc (3*n) (4*n),weightedSmoothLog n Y k)-
      (∑ k ∈ Ioc (2*n) (3*n),weightedSmoothLog n Y k)| ≤
      squarefreeDivisorMass n*(Y:ℝ)^2*Real.log (4*n:ℕ) := by
  let M := squarefreeDivisorMass n
  let X := 4*n
  have hX : 0 < X := Nat.mul_pos (by decide) hn
  have hM : 0 ≤ M := sum_nonneg fun _ _ => abs_nonneg _
  let F (a b e p j : ℕ) := ∑ k ∈ Ioc a b,(μ e:ℝ)*Real.log p*primitiveMultiple n (e.lcm (p^j)) k
  have inter (a b : ℕ) (hb : b ≤ X) : (∑ k ∈ Ioc a b,weightedSmoothLog n Y k)=
      ∑ e ∈ Icc 1 Y,∑ p ∈ Nat.primesLE Y,∑ j ∈ Icc 1 (Nat.log p X),F a b e p j := by
    rw [sum_congr rfl fun k hk => weighted_smooth_log_rows ((Nat.zero_le a).trans_lt (mem_Ioc.mp hk).1)
      ((mem_Ioc.mp hk).2.trans hb) n Y,sum_comm]
    apply sum_congr rfl
    intro e _
    rw [sum_comm]
    exact sum_congr rfl fun p _ => sum_comm
  rw [inter _ _ le_rfl,inter _ _ (by dsimp [X]; omega),←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  have hterm (e : ℕ) (he : e ∈ Icc 1 Y) (p : ℕ) (hp : p ∈ Nat.primesLE Y) (j : ℕ) :
      |F (3*n) (4*n) e p j-F (2*n) (3*n) e p j| ≤ M*Real.log p := by
    have hpr := Nat.prime_of_mem_primesLE hp
    have hu := Nat.lcm_pos (mem_Icc.mp he).1 (pow_pos hpr.pos j)
    dsimp only [F]
    rw [←mul_sum,←mul_sum,←mul_sub,primitive_multiple_second_difference hu,abs_mul,abs_mul,
      abs_of_nonneg (Real.log_natCast_nonneg p)]
    have hm : |(μ e:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=e)
    exact (mul_le_mul (mul_le_of_le_one_left (Real.log_natCast_nonneg p) hm)
      (abs_coprime_midpoint_multiple_count hn hu) (abs_nonneg _) (Real.log_natCast_nonneg p)).trans_eq (mul_comm ..)
  have primecost (e : ℕ) (he : e ∈ Icc 1 Y) (p : ℕ) (hp : p ∈ Nat.primesLE Y) :
      |(∑ j ∈ Icc 1 (Nat.log p X),F (3*n) (4*n) e p j)-
        (∑ j ∈ Icc 1 (Nat.log p X),F (2*n) (3*n) e p j)| ≤ M*Real.log X := by
    rw [←sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun j _ => hterm e he p hp j)).trans ?_)
    rw [sum_const,Nat.card_Icc,Nat.add_one_sub_one,nsmul_eq_mul]
    have h := Real.log_le_log (Nat.cast_pos.mpr (pow_pos (Nat.prime_of_mem_primesLE hp).pos (Nat.log p X)))
      (Nat.cast_le.mpr (Nat.pow_log_le_self p hX.ne'))
    rw [Nat.cast_pow,Real.log_pow] at h
    exact (show ((Nat.log p X:ℕ):ℝ)*(M*Real.log p)=M*((Nat.log p X:ℕ)*Real.log p) by ring).le.trans
      (mul_le_mul_of_nonneg_left h hM)
  have hcard : (Nat.primesLE Y).card ≤ Y := by
    have hs : Nat.primesLE Y ⊆ Icc 1 Y := fun p hp => mem_Icc.mpr
      ⟨(Nat.prime_of_mem_primesLE hp).pos,(Nat.mem_primesLE.mp hp).1⟩
    simpa only [Nat.card_Icc,Nat.add_one_sub_one] using card_le_card hs
  calc _ ≤ ∑ _ ∈ Icc 1 Y,(Y:ℝ)*(M*Real.log X) := by
             apply sum_le_sum
             intro e he
             rw [←sum_sub_distrib]
             apply (abs_sum_le_sum_abs ..).trans ((sum_le_sum (primecost e he)).trans ?_)
             rw [sum_const,nsmul_eq_mul]
             exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (mul_nonneg hM (Real.log_natCast_nonneg _))
       _ = _ := by simp only [sum_const,Nat.card_Icc,Nat.add_one_sub_one,nsmul_eq_mul]; dsimp only [M,X]; ring

/-- Full coprime log reading with the fixed small-divisor weight. -/
private def completeQuarterLog (n Y k : ℕ) : ℝ :=
  if n.Coprime k then truncMoebiusDivisorSum Y k*Real.log k else 0

/-- The actual rough cofactor of a composite receives its full logarithm. -/
private def compositeQuarterLog (n Y k : ℕ) : ℝ :=
  if n.Coprime k ∧ ¬k.Prime then truncMoebiusDivisorSum Y (smoothPart Y k)*Real.log (roughPart Y k) else 0

private theorem quarter_log_difference {n Y k : ℕ} (hn : 0 < n) (hY : 1 ≤ Y) (hk : n < k) (hy : Y < k) :
    completeQuarterLog n Y k-compositeQuarterLog n Y k=
      weightedSmoothLog n Y k+(if k.Prime then Real.log k else 0) := by
  have hk0 := hn.trans hk
  have hlog := congrArg (fun x : ℕ => Real.log (x:ℝ)) (_root_.RHTower.Sieve.smoothPart_mul_roughPart hk0.ne' Y)
  simp only [Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr (_root_.RHTower.Sieve.smoothPart_pos Y k).ne')
    (Nat.cast_ne_zero.mpr (_root_.RHTower.Sieve.roughPart_pos Y k).ne')] at hlog
  by_cases hp : k.Prime
  · have hs : smoothPart Y k=1 := by simp [_root_.RHTower.Sieve.smoothPart,hp.primeFactors,not_le.mpr hy]
    have hweight := truncated_weight_on_smooth_factor hk0 Y
    rw [hs,_root_.RHTower.truncMoebiusDivisorSum_of_le le_rfl hY,if_pos rfl] at hweight
    have hc := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hn hk)).symm
    simp [completeQuarterLog,compositeQuarterLog,weightedSmoothLog,hp,hc,hweight,hs]
  · by_cases hc : n.Coprime k
    · rw [completeQuarterLog,if_pos hc,compositeQuarterLog,if_pos ⟨hc,hp⟩,weightedSmoothLog,
        if_pos hc,if_neg hp,add_zero,←truncated_weight_on_smooth_factor hk0 Y,←hlog]
      ring
    · simp [completeQuarterLog,compositeQuarterLog,weightedSmoothLog,hc,hp]

private def ordinaryMidpointDifference (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Ioc (3*n) (4*n),f k)-(∑ k ∈ Ioc (2*n) (3*n),f k)

/-- Signed proper-composite rough-factor price less the complete
weighted coprime logarithm on the same sharp intervals. -/
def roughFactorMidpointReading (n Y : ℕ) : ℝ :=
  ordinaryMidpointDifference n (compositeQuarterLog n Y)-ordinaryMidpointDifference n (completeQuarterLog n Y)

theorem rough_factor_midpoint_error {n Y : ℕ} (hn : 0 < n) (hY : 1 ≤ Y) (hy : Y ≤ 2*n) :
    |primeMidpointPrice n-roughFactorMidpointReading n Y| ≤
      squarefreeDivisorMass n*(Y:ℝ)^2*Real.log (4*n:ℕ) := by
  let p (k : ℕ) := if k.Prime then Real.log k else 0
  have inter (a b : ℕ) (ha : 2*n ≤ a) :
      (∑ k ∈ Ioc a b,completeQuarterLog n Y k)-(∑ k ∈ Ioc a b,compositeQuarterLog n Y k)=
      (∑ k ∈ Ioc a b,weightedSmoothLog n Y k)+(∑ k ∈ Ioc a b,p k) := by
    rw [←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    have h := ha.trans_lt (mem_Ioc.mp hk).1
    exact quarter_log_difference hn hY (by omega) (hy.trans_lt h)
  have hr := inter (3*n) (4*n) (by omega)
  have hl := inter (2*n) (3*n) le_rfl
  have he : primeMidpointPrice n-roughFactorMidpointReading n Y=
      ordinaryMidpointDifference n (weightedSmoothLog n Y) := by
    simp only [primeMidpointPrice,sum_filter,roughFactorMidpointReading,ordinaryMidpointDifference]
    dsimp only [p] at hr hl
    linarith only [hr,hl]
  rw [he]
  exact quarter_smooth_logarithm_cost hn Y

/-- Taking the fourth-root cutoff makes the full smooth-factor omission
a half-power-plus error, uniformly at every positive integer center. -/
theorem fourth_root_cofactor_midpoint_error {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ {n : ℕ}, 1 ≤ n →
      |primeMidpointPrice n-roughFactorMidpointReading n ⌈((4*n:ℕ):ℝ)^(1/4:ℝ)⌉₊| ≤ C*(n:ℝ)^(1/2+ε) := by
  let η := ε/2
  have hη : 0 < η := half_pos hε
  let A := |_root_.RHTower.Sieve.divisorBoundConst η|
  refine ⟨4*A*(4:ℝ)^(1/2+η)/η,?_⟩
  intro n hn
  let X : ℝ := (4*n:ℕ)
  let R := X^(1/4:ℝ)
  let Y := ⌈R⌉₊
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have hn0 := zero_lt_one.trans_le hn1
  have hx1 : 1 ≤ X := (Nat.one_le_cast (α:=ℝ)).mpr (by omega)
  have hx0 := zero_lt_one.trans_le hx1
  have hr : 1 ≤ R := Real.one_le_rpow hx1 (by norm_num)
  have hY : 1 ≤ Y := Nat.one_le_ceil_iff.mpr (zero_lt_one.trans_le hr)
  have hy : (Y:ℝ) ≤ 2*R := (Nat.ceil_lt_add_one (zero_le_one.trans hr)).le.trans (by linarith only [hr])
  have hhalf : R^2=X^(1/2:ℝ) := by
    dsimp only [R]; rw [←Real.rpow_natCast,←Real.rpow_mul hx0.le]; norm_num
  have hcut : Y ≤ 2*n := by
    apply Nat.ceil_le.mpr
    have hb : R ≤ Real.sqrt X := by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    apply hb.trans
    rw [Nat.cast_mul,Nat.cast_ofNat]
    apply (Real.sqrt_le_iff).mpr ⟨by positivity,?_⟩
    dsimp only [X]
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hn1 hn0.le]
  have hm : squarefreeDivisorMass n ≤ A*(n:ℝ)^η := by
    have h := sum_le_sum (s:=n.divisors) fun d _ =>
      (show |(μ d:ℝ)| ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d))
    simp only [sum_const,nsmul_eq_mul,mul_one] at h
    exact (h.trans (_root_.RHTower.Sieve.card_divisors_le_rpow hη (Nat.ne_of_gt hn))).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hn0.le _))
  have hy2 := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) Y) hy 2
  rw [mul_pow,hhalf] at hy2
  have hl := Real.log_le_rpow_div hx0.le hη
  have ha := mul_le_mul (mul_le_mul hm hy2 (sq_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hn0.le _))) hl
    (Real.log_nonneg hx1) (by dsimp only [A]; positivity)
  apply (rough_factor_midpoint_error hn hY hcut).trans (ha.trans_eq ?_)
  have hprod : X^(1/2:ℝ)*X^η=(4:ℝ)^(1/2+η)*(n:ℝ)^(1/2+η) := by
    rw [←Real.rpow_add hx0]
    dsimp only [X]
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num) hn0.le]
  have hnprod : (n:ℝ)^η*(n:ℝ)^(1/2+η)=(n:ℝ)^(1/2+ε) := by
    rw [←Real.rpow_add hn0,show η+(1/2+η)=1/2+ε by dsimp only [η]; ring]
  calc _ = 4*A/η*((n:ℝ)^η*(X^(1/2:ℝ)*X^η)) := by ring
       _ = _ := by rw [hprod,←hnprod]; ring

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
