import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCenteredReadingBelowTheHyperbola
import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments
import GaloisForLFunctions.BezoutValuationIncidence.TheVaughanEmptyLegReadsTheZeroAbscissa
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# Prime readings beyond the hyperbola

The ordinary prime weights determine how far the signed head can be
moved. All changes on proper prime powers have uniformly bounded mass
at each exponent above one half. The full Mangoldt head is a signed
logarithmic Möbius prefix at the smaller endpoint.
-/

noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev H (y T : ℕ) (a : ArithmeticFunction ℝ) := quotientReading (roughFloorCoefficient y a) T

private theorem perturbation_price {s C : ℝ} (sp : 0<s) (hC : 0 ≤ C)
    (full : ∀ n,|coprimeMoebiusSum 1 n| ≤ C*(n:ℝ)^s) (y T : ℕ) (a b : ArithmeticFunction ℝ) :
    |H y T a-H y T b| ≤ 2*C*deletionPrice s y*(T:ℝ)^s*
      ∑ q ∈ Icc 1 T,|a q-b q| * (q:ℝ)^(-s) := by
  rw [coefficient_head_as_quotient_sum,coefficient_head_as_quotient_sum,←sum_sub_distrib,mul_sum]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro q hq
  let D := 2*C*deletionPrice s y
  have d0 : 0 ≤ D := mul_nonneg (by positivity) (zero_le_one.trans (deletionPrice_one_le sp _))
  have qp := (Nat.cast_pos (α := ℝ)).mpr (mem_Icc.mp hq).1
  have bound : ((T/q:ℕ):ℝ) ≤ (T:ℝ)/q := (le_div_iff₀ qp).mpr (by exact_mod_cast Nat.div_mul_le_self T q)
  have price := (all_frozen_rows_from_full_prefix sp hC full (T/q) y).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) bound sp.le) d0)
  rw [Real.div_rpow (Nat.cast_nonneg _) qp.le] at price
  rw [←sub_mul,abs_mul]
  exact (mul_le_mul_of_nonneg_left price (abs_nonneg _)).trans_eq (by
    rw [Real.rpow_neg qp.le]; ring)

/-- At arbitrary observation walls and heights the cumulative price of
proper-power edits is bounded by their atomwise variation. The number
of observations and the order of the edits are unrestricted. -/
theorem signed_price_of_all_proper_power_edits {s : ℝ} (strip : RHTower.zetaZeroAbscissa<s)
    (upper : s ≤ 1) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ N Y T : ℕ,∀ y h : ℕ → ℕ,
      (∀ i,i<N → y i ≤ Y) → (∀ i,i<N → h i ≤ T) →
      ∀ a b : ℕ → ArithmeticFunction ℝ,∀ B : ℝ,0 ≤ B →
      (∀ i p,i<N → p.Prime → b i p=a i p) →
      (∀ q,(∑ i ∈ range N,|b i q-a i q|) ≤ B*vonMangoldt q) →
      (∑ i ∈ range N,|H (y i) (h i) (b i)-H (y i) (h i) (a i)|) ≤
        K*B*deletionPrice s Y*(T:ℝ)^s := by
  have hs := RHTower.half_le_zetaZeroAbscissa.trans_lt strip
  have sp := (by norm_num : (0:ℝ)<1/2).trans hs
  obtain ⟨C,c0,full⟩ := exists_moebius_power_bound_of_abscissa_lt strip
  have allN (n : ℕ) : |coprimeMoebiusSum 1 n| ≤ C*(n:ℝ)^s := by
    rcases Nat.eq_zero_or_pos n with rfl | np
    · simp [coprimeMoebiusSum,Real.zero_rpow sp.ne']
    simpa [coprimeMoebiusSum,coprimeMoebiusIndicator,moebiusReal] using full n np
  let P := 36/(s-1/2)
  have p0 : 0 ≤ P := div_nonneg (by norm_num) (sub_nonneg.mpr hs.le)
  refine ⟨2*C*P,by positivity,fun N Y T y h walls heights a b B bp fixed changes => ?_⟩
  let D := 2*C*deletionPrice s Y*(T:ℝ)^s
  let mass := fun i q : ℕ => |b i q-a i q| * (q:ℝ)^(-s)
  have d0 : 0 ≤ D := mul_nonneg (mul_nonneg (by positivity) (zero_le_one.trans (deletionPrice_one_le sp _)))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have m0 (i q : ℕ) : 0 ≤ mass i q := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have step (i : ℕ) (hi : i ∈ range N) :
      |H (y i) (h i) (b i)-H (y i) (h i) (a i)| ≤ D*∑ q ∈ Icc 1 T,mass i q := by
    have ti := heights i (mem_range.mp hi)
    have cut := perturbation_price sp c0 allN (y i) (h i) (b i) (a i)
    have prod := mul_le_mul (mul_le_mul_of_nonneg_left (deletionPrice_mono sp (walls i (mem_range.mp hi)))
      (by positivity : 0 ≤ 2*C)) (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr ti) sp.le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (by positivity) (zero_le_one.trans (deletionPrice_one_le sp Y)))
    exact cut.trans (mul_le_mul prod (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right ti) (fun q _ _ => m0 i q))
      (sum_nonneg (fun q _ => m0 i q)) d0)
  have cost (q : ℕ) : (∑ i ∈ range N,mass i q) ≤
      B*(if ¬q.Prime then vonMangoldt q*(q:ℝ)^(-s) else 0) := by
    by_cases prime : q.Prime
    · have zero := sum_eq_zero (s := range N) (f := fun i => mass i q)
        (fun i hi => by simp [mass,fixed i q (mem_range.mp hi) prime])
      simp [zero,prime]
    · simp only [mass,←sum_mul,prime,not_false_eq_true,if_true]
      exact (mul_le_mul_of_nonneg_right (changes q) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq (mul_assoc ..)
  have sumcap := RHTower.sum_nonprime_vonMangoldt_rpow_le (sub_pos.mpr hs) (by linarith only [upper] : s-1/2 ≤ 1) T
  rw [show (1:ℝ)/2+(s-1/2)=s by ring,sum_filter] at sumcap
  have sumcost := sum_le_sum (s := Icc 1 T) (fun q _ => cost q)
  rw [←mul_sum] at sumcost
  have combined := sumcost.trans (mul_le_mul_of_nonneg_left sumcap bp)
  have across := sum_le_sum step
  rw [←mul_sum,sum_comm] at across
  exact across.trans ((mul_le_mul_of_nonneg_left combined d0).trans_eq (by dsimp only [D,P]; ring))

/-- Uniform head price when the ordinary primes have their original weights
and the contribution at every proper prime power is chosen independently.
Only a weaker strip estimate is used at the head's own height. -/
theorem structured_prime_head_above_the_strip {s : ℝ} (strip : RHTower.zetaZeroAbscissa<s) (upper : s ≤ 1) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ y T : ℕ,0<y → ∀ a : ArithmeticFunction ℝ,
      (∀ q,|a q| ≤ vonMangoldt q) → (∀ p,p.Prime → a p=roughMangoldtWeight y p) →
      |quotientReading (roughFloorCoefficient y a) T| ≤ K*deletionPrice s y*(T:ℝ)^s*(1+Real.log T) := by
  have hs : (1:ℝ)/2<s := RHTower.half_le_zetaZeroAbscissa.trans_lt strip
  have sp : 0<s := (by norm_num : (0:ℝ)<1/2).trans hs
  obtain ⟨C,hC,h⟩ := exists_moebius_power_bound_of_abscissa_lt strip
  have full (n : ℕ) : |coprimeMoebiusSum 1 n| ≤ C*(n:ℝ)^s := by
    rcases Nat.eq_zero_or_pos n with rfl | pos
    · simp [coprimeMoebiusSum,Real.zero_rpow sp.ne']
    simpa [coprimeMoebiusSum,coprimeMoebiusIndicator,moebiusReal] using h n pos
  let B := 36/(s-1/2)
  have b0 : 0 ≤ B := div_nonneg (by norm_num) (sub_nonneg.mpr hs.le)
  refine ⟨4*C*(1+B),by positivity,fun y T yp a dom same => ?_⟩
  let b := roughMangoldtWeight y
  let D := deletionPrice s y*(T:ℝ)^s
  have d0 : 0 ≤ D := mul_nonneg (zero_le_one.trans (deletionPrice_one_le sp _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have mono : Monotone (fun k : ℕ => Real.log k) := by
    intro k l order
    rcases Nat.eq_zero_or_pos k with rfl | pos
    · simpa only [Nat.cast_zero,Real.log_zero] using Real.log_natCast_nonneg l
    exact Real.log_le_log (Nat.cast_pos.mpr pos) (Nat.cast_le.mpr order)
  have main := weighted_reading_from_full_prefix _ mono (by simp) sp hC full y T
  have ident : H y T b= -weightedFrozenPrefix (fun k => Real.log k) y T := by
    rw [show H y T b=roughCofactorReading y T (quotientReading b) from
      (rough_action_as_a_coefficient_prefix y T b).symm,full_rough_reading yp]
    unfold roughLogarithmicHead weightedFrozenPrefix
    congr 1
    exact sum_congr rfl (fun n hn => congrArg (fun z : ℝ => z*Real.log n)
      (primorial_indicator_eq_deleted_mobius y n (mem_Icc.mp hn).1).symm)
  have m : |H y T b| ≤ 4*C*D*Real.log T := by
    rw [ident,abs_neg]; exact main.trans_eq (by dsimp only [D]; ring)
  have sumcap := RHTower.sum_nonprime_vonMangoldt_rpow_le (sub_pos.mpr hs)
    (by linarith only [upper] : s-1/2 ≤ 1) T
  rw [show (1:ℝ)/2+(s-1/2)=s by ring] at sumcap
  have pert : (∑ q ∈ Icc 1 T,|a q-b q| * (q:ℝ)^(-s)) ≤ 2*B := by
    apply le_trans _ (mul_le_mul_of_nonneg_left sumcap (by norm_num : (0:ℝ) ≤ 2))
    rw [mul_sum,sum_filter]
    apply sum_le_sum
    intro q _
    by_cases prime : q.Prime
    · simp [b,same q prime,prime]
    · have bd : |b q| ≤ vonMangoldt q := by
        rw [show b=roughRestriction y vonMangoldt from rfl,roughRestriction_apply]
        split
        · exact (abs_of_nonneg vonMangoldt_nonneg).le
        · rw [abs_zero]; exact vonMangoldt_nonneg
      simp only [prime,not_false_eq_true,if_true]
      exact (mul_le_mul_of_nonneg_right ((abs_sub ..).trans ((add_le_add (dom q) bd).trans_eq
        (two_mul _).symm)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq (by ring)
  have diff := (perturbation_price sp hC full y T a b).trans (mul_le_mul_of_nonneg_left pert
    (mul_nonneg (mul_nonneg (by positivity) (zero_le_one.trans (deletionPrice_one_le sp y)))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  have tri := abs_add_le (H y T a-H y T b) (H y T b)
  rw [sub_add_cancel] at tri
  apply tri.trans ((add_le_add diff m).trans ?_)
  change 2*C*deletionPrice s y*(T:ℝ)^s*(2*B)+4*C*D*Real.log T ≤ _
  have extra := mul_nonneg (mul_nonneg (mul_nonneg hC d0) b0) (Real.log_natCast_nonneg T)
  dsimp only [D] at *
  linarith only [extra,mul_nonneg hC d0]


/-- At the log-square sieve, the same price applies to the complete
prime-power reading, ordinary primes alone and all intermediate signed
prime-power selections. A head of height at most X^α costs every
exponent strictly larger than α times the strip boundary. -/
theorem shrinking_the_cofactor_range_for_prime_readings {α u : ℝ} (ap : 0<α)
    (gain : α*RHTower.zetaZeroAbscissa<u) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ᶠ X : ℕ in atTop,∀ T : ℕ,(T:ℝ) ≤ (X:ℝ)^α →
      ∀ a : ArithmeticFunction ℝ,(∀ q,|a q| ≤ vonMangoldt q) →
      (∀ p,p.Prime → a p=roughMangoldtWeight (logSquareCutoff X) p) →
      |roughCofactorReading (logSquareCutoff X) X (quotientReading a)-
        roughInteriorReading a (logSquareCutoff X) X T| ≤ K*(X:ℝ)^u := by
  let β := RHTower.zetaZeroAbscissa
  have lower : (1:ℝ)/2 ≤ β := RHTower.half_le_zetaZeroAbscissa
  have upper : β<1 := ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths.trans_lt (by norm_num)
  have room : β < u/α := (lt_div_iff₀ ap).mpr (by unfold β; rwa [mul_comm])
  let s := (β+min 1 (u/α))/2
  have width : β < min 1 (u/α) := lt_min upper room
  have strip : β<s := by dsimp only [s]; linarith only [width]
  have sl : s < min 1 (u/α) := by dsimp only [s]; linarith only [width]
  have sp : 0<s := ((by norm_num : (0:ℝ)<1/2).trans_le lower).trans strip
  have sg := (lt_div_iff₀ ap).mp (sl.trans_le (min_le_right ..))
  let η := (u-α*s)/2
  have ep : 0<η := by dsimp only [η]; linarith only [sg]
  obtain ⟨K,hK,cap⟩ := structured_prime_head_above_the_strip strip (sl.le.trans (min_le_left ..))
  refine ⟨K*(1+1/η),by positivity,?_⟩
  filter_upwards [log_square_deletion_cost (lower.trans_lt strip) ep,
    logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)] with X price yp xp
  intro T height a dom same
  let y := logSquareCutoff X
  let n := min X T
  let E := deletionPrice s y
  have ex : 1 ≤ E := deletionPrice_one_le sp _
  have cheap : E ≤ (X:ℝ)^η := by
    have sq : E ≤ E^2 := by nlinarith only [ex,sq_nonneg (E-1)]
    exact sq.trans ((le_mul_of_one_le_left (sq_nonneg E) (by
      have := Nat.cast_nonneg (α := ℝ) (logSquareCutoff X); linarith)).trans price)
  have positive : 0<(X:ℝ) := Nat.cast_pos.mpr xp
  have npow : (n:ℝ)^s ≤ (X:ℝ)^(α*s) := by
    rw [Real.rpow_mul positive.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) ((Nat.cast_le.mpr (min_le_right X T)).trans height) sp.le
  have lg : Real.log n ≤ Real.log X := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h,Nat.cast_zero,Real.log_zero]; exact Real.log_natCast_nonneg _
    exact Real.log_le_log (Nat.cast_pos.mpr h) (Nat.cast_le.mpr (min_le_left ..))
  have xpow := Real.one_le_rpow (Nat.one_le_cast.mpr xp) ep.le
  have logcap : 1+Real.log n ≤ (1+1/η)*(X:ℝ)^η := by
    have log := lg.trans (Real.log_le_rpow_div positive.le ep)
    linarith only [xpow,log]
  rw [rough_head_and_interior,add_sub_cancel_left]
  have main := cap y n yp a dom same
  have bounded := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left cheap hK) npow
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg hK (Real.rpow_nonneg positive.le _))) logcap
    (by linarith only [Real.log_natCast_nonneg n] : 0 ≤ 1+Real.log n)
    (mul_nonneg (mul_nonneg hK (Real.rpow_nonneg positive.le _)) (Real.rpow_nonneg positive.le _))
  apply main.trans (bounded.trans_eq ?_)
  have scale : u=η+α*s+η := by dsimp only [η]; ring
  rw [scale,Real.rpow_add positive,Real.rpow_add positive]; ring

private theorem ordinary_agrees_at_prime (y : ℕ) {p : ℕ} (hp : p.Prime) :
    roughOrdinaryPrimeWeight y p=roughMangoldtWeight y p := by
  have free : IsFree (RoughReading.banned y) p ↔ y<p := by
    simpa only [RoughReading.banned,Set.mem_setOf_eq,not_le] using isFree_prime (RoughReading.banned y) hp
  rw [roughMangoldtWeight,roughRestriction_apply,vonMangoldt_apply_prime hp]
  change (if p.Prime ∧ y<p then Real.log p else 0)=_
  simp only [hp,true_and,free]

/-- At the head X^(4/7), only cofactors up to X^(3/7) remain.
For both ordinary primes and all prime powers the signed price has
an exponent strictly below one half. -/
theorem ordinary_and_prime_power_transfer_to_three_sevenths :
    ∃ K : ℝ,0 ≤ K ∧ ∀ᶠ X : ℕ in atTop,
      let y := logSquareCutoff X
      let T := ⌊(X:ℝ)^(4/7:ℝ)⌋₊
      ((X/(T+1):ℕ):ℝ) ≤ (X:ℝ)^(3/7:ℝ) ∧
      ∀ a ∈ ({roughOrdinaryPrimeWeight y,roughMangoldtWeight y} : Finset (ArithmeticFunction ℝ)),
        |roughCofactorReading y X (quotientReading a)-roughInteriorReading a y X T| ≤
          K*(X:ℝ)^(1/2-1/84000:ℝ) := by
  obtain ⟨K,hK,good⟩ := shrinking_the_cofactor_range_for_prime_readings
    (by norm_num : (0:ℝ)<4/7) ((mul_le_mul_of_nonneg_left ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths (by norm_num : (0:ℝ) ≤ 4/7)).trans_lt (by norm_num))
  refine ⟨K,hK,?_⟩
  filter_upwards [good,eventually_ge_atTop (1:ℕ)] with X bound xp
  let T := ⌊(X:ℝ)^(4/7:ℝ)⌋₊
  let y := logSquareCutoff X
  have x0 : 0<(X:ℝ) := Nat.cast_pos.mpr xp
  have size : (T:ℝ) ≤ (X:ℝ)^(4/7:ℝ) := Nat.floor_le (Real.rpow_nonneg x0.le _)
  have rem : (X:ℝ)^(4/7:ℝ) ≤ ((T+1:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one ((X:ℝ)^(4/7:ℝ))).le
  constructor
  · have fac := (mul_le_mul_of_nonneg_left rem (Nat.cast_nonneg (α := ℝ) (X/(T+1)))).trans
      (show ((X/(T+1):ℕ):ℝ)*((T+1:ℕ):ℝ) ≤ X by exact_mod_cast Nat.div_mul_le_self X (T+1))
    apply le_of_mul_le_mul_right _ (Real.rpow_pos_of_pos x0 (4/7:ℝ))
    rwa [←Real.rpow_add x0,show (3/7:ℝ)+4/7=1 by norm_num,Real.rpow_one]
  · intro a ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact bound T size _ (ordinary_dominated y) (fun _ hp => ordinary_agrees_at_prime y hp)
    · exact bound T size _ (mangoldt_dominated y) (fun _ _ => rfl)

/-- The corrected prime-power reading on cofactors through X/(1+floor(X^α)). -/
def primePowerInteriorAtExponent (α : ℝ) (X : ℕ) :=
  roughInteriorReading (roughMangoldtWeight (logSquareCutoff X)) (logSquareCutoff X) X ⌊(X:ℝ)^α⌋₊

/-- The smaller-cofactor prime-power reading retains the complete
Mertens criterion through the reciprocal of twice the zero abscissa,
including the endpoint. The square-root estimate on the interior is the only
input still required for the full prefix. -/
theorem mertens_criterion_on_the_shrunken_cofactor_range {α : ℝ} (ap : 0<α)
    (width : α*RHTower.zetaZeroAbscissa ≤ 1/2) :
    (∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (primePowerInteriorAtExponent α)) ↔
      ∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (coprimeMoebiusSum 1) := by
  let c := fun X => centeredPrimePowerRemainder (logSquareCutoff X) X
  let f := primePowerInteriorAtExponent α
  have eq {ε : ℝ} (ep : 0<ε) : PrefixPower (1/2+ε) f ↔ PrefixPower (1/2+ε) c := by
    let u := (1:ℝ)/2+ε
    have up : 0<u := by dsimp only [u]; linarith only [ep]
    obtain ⟨K,hK,budget⟩ := shrinking_the_cofactor_range_for_prime_readings ap (width.trans_lt (lt_add_of_pos_right _ ep))
    have small : ∀ᶠ X : ℕ in atTop,|c X-f X| ≤ (K+1)*(X:ℝ)^u := by
      filter_upwards [budget,smooth_main_term_paid_at_the_log_square_cutoff ep,
        logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1] with X cost smooth yp
      let y := logSquareCutoff X
      let a := roughMangoldtWeight y
      let T := ⌊(X:ℝ)^α⌋₊
      let A := roughCofactorReading y X (quotientReading a)
      have delta : |A-f X| ≤ K*(X:ℝ)^u :=
        cost T (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) a (mangoldt_dominated y) (fun _ _ => rfl)
      have center : c X=A-smoothQuotientCenter y X := centered_eq_rough_reading_sub_smooth yp X
      rw [center,show A-smoothQuotientCenter y X-f X=(A-f X)-smoothQuotientCenter y X by ring]
      have nonneg : 0 ≤ smoothQuotientCenter y X := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      apply (abs_sub ..).trans
      rw [abs_of_nonneg nonneg]
      have sm : smoothQuotientCenter y X ≤ (X:ℝ)^u := smooth y le_rfl
      linarith only [delta,sm]
    have c0 : c 0=0 := by simp [c,centeredPrimePowerRemainder,RoughReading.freeSet]
    have f0 : f 0=0 := by simp [f,primePowerInteriorAtExponent,roughInteriorReading]
    constructor <;> rintro ⟨D,_,bound⟩
    · apply prefixPower_of_eventual (C := D+K+1) c0 up
      filter_upwards [small] with X cost
      have tri := abs_add_le (c X-f X) (f X)
      rw [sub_add_cancel] at tri
      linarith only [tri,cost,bound X]
    · apply prefixPower_of_eventual (C := D+K+1) f0 up
      filter_upwards [small] with X cost
      have tri := abs_sub (c X) (c X-f X)
      rw [sub_sub_cancel] at tri
      linarith only [tri,cost,bound X]
  rw [←square_root_iff_one_centered_prime_power_reading]
  exact ⟨fun h ε ep => (eq ep).mp (h ε ep),fun h ε ep => (eq ep).mpr (h ε ep)⟩

#print axioms mertens_criterion_on_the_shrunken_cofactor_range
#print axioms ordinary_and_prime_power_transfer_to_three_sevenths
#print axioms signed_price_of_all_proper_power_edits
#print axioms structured_prime_head_above_the_strip
#print axioms shrinking_the_cofactor_range_for_prime_readings

end GaloisForLFunctions.RestrictedFactorizationCalculus
