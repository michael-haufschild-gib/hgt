import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFineVariationOfTheCenteredPrimeCut
import GaloisForLFunctions.RHTower.PrimeWindowSupply
import GaloisForLFunctions.RHTower.PsiWindowUpperBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Prime jumps and the critical fine-variation order

The upper half of the prime cutoff carries a positive proportion of
its prime log mass. On that half the signed unit jump has magnitude
comparable to the cutoff times the prime logarithm. The q-th power sum
retains exactly q−1 powers of the logarithm. At the seventeen-ninths
cut, the fine variation admits a cubic bound precisely for q>17/10.
-/

noncomputable section
open Finset Filter
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Variation power on the full integer mesh of the original conductor tail. -/
def fineCutPower (N K : ℕ) (q : ℝ) : ℝ :=
  ∑ k ∈ range K, ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖^q

private theorem price_mesh {N K : ℕ} {q : ℝ} (hq : 0<q) (hN : 0<N)
    (hk : (K:ℝ)≤Real.exp (-8)*(N:ℝ)^2) :
    fineCutPower N K q=∑ n ∈ range (K+1), |innerCutIncrement n|^q := by
  rw [sum_range_succ',show |innerCutIncrement 0|^q=0 by simp [innerCutIncrement,Real.zero_rpow hq.ne'],add_zero]
  apply sum_congr rfl
  intro k h
  have hi := Nat.succ_le_of_lt (mem_range.mp h)
  rw [centered_fixed_cut_step hN ((Nat.cast_le.mpr hi).trans hk),Complex.norm_real,Real.norm_eq_abs]

private theorem upper_half_mass :
    ∀ᶠ K : ℕ in atTop, (K:ℝ)/4≤∑ n ∈ (Ioc (K/2) K).filter Nat.Prime, Real.log n := by
  obtain ⟨U,hu⟩ := _root_.RHTower.chebyshevTheta_remainder_eventually_le (by norm_num : (0:ℝ)<1/8)
  filter_upwards [eventually_ge_atTop (2*U)] with K hK
  rw [←_root_.RHTower.theta_window_eq (Nat.div_le_self K 2)]
  have lo := (abs_le.mp (hu K (by omega))).1
  have hi := (abs_le.mp (hu (K/2) (by omega))).2
  have half : (↑(K/2):ℝ)*2≤K := by exact_mod_cast Nat.div_mul_le_self K 2
  linarith only [lo,hi,half,Nat.cast_nonneg (α:=ℝ) K]

private theorem prime_jump {n K : ℕ} {q : ℝ} (hq : 1≤q) (lg : 4≤Real.log K)
    (hn : n∈(Ioc (K/2) K).filter Nat.Prime) :
    (innerPrimeSlope*K/4)^q*(Real.log K/2)^(q-1)*Real.log n≤|innerCutIncrement n|^q := by
  obtain ⟨inrow,prime⟩ := mem_filter.mp hn
  obtain ⟨lo,hi⟩ := mem_Ioc.mp inrow
  have np : 0<(n:ℝ) := Nat.cast_pos.mpr prime.pos
  have il := innerPrimeSlope_pos
  have kp : 0<(K:ℝ) := Nat.cast_pos.mpr (prime.pos.trans_le hi)
  have two : (K:ℝ)≤2*n := by exact_mod_cast (show K≤2*n by omega)
  have logs := Real.log_le_log kp two
  rw [Real.log_mul (by norm_num) np.ne'] at logs
  have log2 : Real.log 2≤1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have half : Real.log K/2≤Real.log n := by linarith only [logs,log2,lg]
  have ln : 2≤Real.log n := by linarith only [half,lg]
  have size : innerPrimeSlope*K/4*Real.log n≤|innerCutIncrement n| := by
    unfold innerCutIncrement
    rw [if_pos prime,abs_mul,abs_of_nonneg (mul_nonneg innerPrimeSlope_pos.le np.le),
      abs_of_nonpos (show 1-Real.log n≤0 by linarith only [ln])]
    have prod := mul_le_mul_of_nonneg_left two (mul_nonneg innerPrimeSlope_pos.le (Real.log_natCast_nonneg n))
    have paid := mul_le_mul_of_nonneg_left ln (mul_nonneg innerPrimeSlope_pos.le np.le)
    linarith only [prod,paid]
  have term := Real.rpow_le_rpow (mul_nonneg (by positivity : 0 ≤ innerPrimeSlope*K/4) (Real.log_natCast_nonneg n))
    size (zero_le_one.trans hq)
  rw [Real.mul_rpow (by positivity : 0 ≤ innerPrimeSlope*K/4) (Real.log_natCast_nonneg n)] at term
  have split : (Real.log n)^(q-1)*Real.log n=(Real.log n)^q := by
    simpa only [Real.rpow_one,sub_add_cancel] using (Real.rpow_add (by linarith only [ln] : 0<Real.log n) (q-1) 1).symm
  have comp := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (by linarith only [lg] : 0≤Real.log K/2) half (sub_nonneg.mpr hq))
    (Real.log_natCast_nonneg n)
  rw [split] at comp
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left comp (Real.rpow_nonneg (by positivity) _)).trans term

/-- The two explicit estimates have the same order K^(q+1) log(K)^(q−1)
for every fixed q≥1. The lower estimate uses primes only on (K/2,K]. -/
theorem fine_cut_power_bounds {q : ℝ} (hq : 1≤q) :
    ∀ᶠ K : ℕ in atTop, ∀ N : ℕ, 0<N → (K:ℝ)≤Real.exp (-8)*(N:ℝ)^2 →
      (innerPrimeSlope*K/4)^q*(Real.log K/2)^(q-1)*(K/4:ℝ)≤fineCutPower N K q ∧
      fineCutPower N K q≤(innerPrimeSlope*K*(1+Real.log K))^(q-1)*(innerPrimeSlope*(1+Real.log 4)*(K:ℝ)^2) := by
  have loggrow : Tendsto (fun K : ℕ => Real.log K) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [upper_half_mass,loggrow.eventually_ge_atTop 4] with K mass lg
  intro N hN hk
  refine ⟨?_,centered_fixed_cut_fine_power hq hN hk⟩
  let S := (Ioc (K/2) K).filter Nat.Prime
  let C := (innerPrimeSlope*K/4)^q*(Real.log K/2)^(q-1)
  have il := innerPrimeSlope_pos
  have cpos : 0≤C := mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (by linarith only [lg]) _)
  have term : (∑ n ∈ S,C*Real.log n)≤∑ n ∈ S, |innerCutIncrement n|^q :=
    sum_le_sum (fun n hn => prime_jump hq lg hn)
  have inc : S⊆range (K+1) := fun n hn => mem_range.mpr (Nat.lt_succ_of_le (mem_Ioc.mp (mem_filter.mp hn).1).2)
  have whole := sum_le_sum_of_subset_of_nonneg inc (fun n _ _ => Real.rpow_nonneg (abs_nonneg (innerCutIncrement n)) q)
  rw [←mul_sum] at term
  rw [price_mesh (zero_lt_one.trans_le hq) hN hk]
  exact ((mul_le_mul_of_nonneg_left mass cpos).trans term).trans whole

private theorem power_order {q : ℝ} (hq : 1≤q) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ᶠ K : ℕ in atTop, ∀ N : ℕ, 0<N → (K:ℝ)≤Real.exp (-8)*(N:ℝ)^2 →
      c*(K:ℝ)^(q+1)*(Real.log K)^(q-1)≤fineCutPower N K q ∧
      fineCutPower N K q≤C*(K:ℝ)^(q+1)*(Real.log K)^(q-1) := by
  let l := innerPrimeSlope
  have lp : 0<l := innerPrimeSlope_pos
  let c := (l/4)^q*(1/2:ℝ)^(q-1)/4
  let C := (2*l)^(q-1)*(l*(1+Real.log 4))
  have l4 : 0<1+Real.log 4 := by linarith only [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]
  refine ⟨c,C,by dsimp [c]; positivity,by dsimp [C]; positivity,?_⟩
  have grow : Tendsto (fun K : ℕ => Real.log K) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [fine_cut_power_bounds hq,grow.eventually_ge_atTop 1,eventually_ge_atTop 1] with K raw log1 K1
  intro N hN hk
  obtain ⟨low,high⟩ := raw N hN hk
  let x := (K:ℝ)
  let v := Real.log x
  change 1≤v at log1
  have xp : 0<x := Nat.cast_pos.mpr K1
  have vp : 0<v := zero_lt_one.trans_le log1
  have add : x^(q+1)=x^q*x := by rw [Real.rpow_add xp,Real.rpow_one]
  have sub : x^(q-1)*x^2=x^(q+1) := by
    rw [←Real.rpow_two,←Real.rpow_add xp,show q-1+2=q+1 by ring]
  constructor
  · apply le_trans _ low
    change c*x^(q+1)*v^(q-1)≤(l*x/4)^q*(v/2)^(q-1)*(x/4)
    rw [show l*x/4=(l/4)*x by ring,show v/2=(1/2:ℝ)*v by ring,Real.mul_rpow (div_nonneg lp.le (by norm_num)) xp.le,
      Real.mul_rpow (by norm_num : (0:ℝ)≤1/2) vp.le,add]
    dsimp only [c]
    exact le_of_eq (by ring)
  · apply high.trans
    change (l*x*(1+v))^(q-1)*(l*(1+Real.log 4)*x^2)≤C*x^(q+1)*v^(q-1)
    have base : l*x*(1+v)≤(2*l*x)*v := by linarith only [mul_le_mul_of_nonneg_left log1 (mul_nonneg lp.le xp.le)]
    have power := Real.rpow_le_rpow (mul_nonneg (mul_nonneg lp.le xp.le) (add_nonneg zero_le_one vp.le)) base (sub_nonneg.mpr hq)
    apply (mul_le_mul_of_nonneg_right power (by positivity)).trans
    rw [Real.mul_rpow (by positivity : 0≤2*l*x) vp.le,Real.mul_rpow (by positivity : 0≤2*l) xp.le,←sub]
    dsimp only [C]
    exact le_of_eq (by ring)

/-- At the seventeen-ninths cutoff the exact power-log order is
N^((17/9)(q+1)) (log N)^(q−1), also at the critical value of q. -/
theorem fine_cut_power_at_seventeen_ninths {q : ℝ} (hq : 1≤q) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ᶠ N : ℕ in atTop,
      let E := fineCutPower N ⌊(N:ℝ)^(17/9:ℝ)⌋₊ q
      let S := (N:ℝ)^((17/9)*(q+1))*(Real.log N)^(q-1)
      c*S≤E ∧ E≤C*S := by
  obtain ⟨c,C,hc,hC,cost⟩ := power_order hq
  obtain ⟨U,hU⟩ := eventually_atTop.mp cost
  refine ⟨c*(1/2:ℝ)^(q+1),C*(17/9:ℝ)^(q-1),by positivity,by positivity,?_⟩
  filter_upwards [seventeen_ninths_inside_first_knot,eventually_ge_atTop (max U 2)] with N geo hN
  let x := (N:ℝ)
  let Y := x^(17/9:ℝ)
  let K := ⌊Y⌋₊
  have n2 : 2≤N := (le_max_right U 2).trans hN
  have xp : 0<x := Nat.cast_pos.mpr (by omega)
  have nk : N≤K := geo.1
  have kp : 0<(K:ℝ) := Nat.cast_pos.mpr (by omega)
  have k1 : 1≤(K:ℝ) := Nat.one_le_cast.mpr (by omega)
  have yp : 0<Y := Real.rpow_pos_of_pos xp _
  have ky : (K:ℝ)≤Y := Nat.floor_le yp.le
  have yk : (1/2:ℝ)*Y≤K := by
    have h : Y<(K:ℝ)+1 := Nat.lt_floor_add_one _
    linarith only [h,k1]
  have qr : 0≤q+1 := by linarith only [hq]
  have xpow : Y^(q+1)=x^((17/9)*(q+1)) := (Real.rpow_mul xp.le _ _).symm
  have lp := Real.rpow_le_rpow (mul_nonneg (by norm_num) yp.le) yk qr
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤1/2) yp.le,xpow] at lp
  have up := (Real.rpow_le_rpow kp.le ky qr).trans_eq xpow
  have llog := Real.log_le_log xp (Nat.cast_le.mpr nk)
  have ulog := Real.log_le_log kp ky
  change Real.log (K:ℝ)≤Real.log (x^(17/9:ℝ)) at ulog
  rw [Real.log_rpow xp] at ulog
  have rp := sub_nonneg.mpr hq
  have nx : 0≤Real.log x := Real.log_natCast_nonneg N
  have lowerLog := Real.rpow_le_rpow nx llog rp
  have upperLog := Real.rpow_le_rpow (Real.log_natCast_nonneg K) ulog rp
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤17/9) nx] at upperLog
  obtain ⟨low,high⟩ := hU K (((le_max_left U 2).trans hN).trans nk) N (by omega) geo.2
  have lower := mul_le_mul (mul_le_mul_of_nonneg_left lp hc.le) lowerLog (Real.rpow_nonneg nx _) (mul_nonneg hc.le (Real.rpow_nonneg kp.le _))
  have upper := mul_le_mul (mul_le_mul_of_nonneg_left up hC.le) upperLog (Real.rpow_nonneg (Real.log_natCast_nonneg K) _)
    (mul_nonneg hC.le (Real.rpow_nonneg xp.le _))
  constructor
  · apply le_trans _ (lower.trans low)
    exact le_of_eq (by ring)
  · apply (high.trans upper).trans
    exact le_of_eq (by ring)

/-- At and below order 17/10 the q-th power sum exceeds every cubic
q-th power budget eventually. At equality the excess comes solely
from the prime logarithm. -/
theorem fine_cut_exceeds_cubic_budget {q : ℝ} (hq : 1≤q) (hcrit : q≤17/10) (M : ℝ) :
    ∀ᶠ N : ℕ in atTop, M*(N:ℝ)^(3*q)<fineCutPower N ⌊(N:ℝ)^(17/9:ℝ)⌋₊ q := by
  obtain ⟨c,_,hc,_,bounds⟩ := fine_cut_power_at_seventeen_ninths hq
  let a := (17/9:ℝ)*(q+1)
  have loggrow : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  rcases lt_or_eq_of_le hcrit with below|atcrit
  · have diff : 0<a-3*q := by dsimp [a]; linarith only [below]
    have grow : Tendsto (fun n : ℕ => c*(n:ℝ)^(a-3*q)) atTop atTop :=
      ((tendsto_rpow_atTop diff).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
    filter_upwards [bounds,grow.eventually_gt_atTop M,loggrow.eventually_ge_atTop 1,eventually_ge_atTop 1] with n floor big log1 n1
    have xp : 0<(n:ℝ) := Nat.cast_pos.mpr n1
    have paid := mul_lt_mul_of_pos_right big (Real.rpow_pos_of_pos xp (3*q))
    change M*(n:ℝ)^(3*q)<(c*(n:ℝ)^(a-3*q))*(n:ℝ)^(3*q) at paid
    rw [mul_assoc,←Real.rpow_add xp,sub_add_cancel] at paid
    have lpow := Real.one_le_rpow log1 (sub_nonneg.mpr hq)
    have z := mul_le_mul_of_nonneg_left lpow (mul_pos hc (Real.rpow_pos_of_pos xp a)).le
    rw [mul_one,mul_assoc] at z
    exact (paid.trans_le z).trans_le floor.1
  · have pq : 0<q-1 := by linarith only [atcrit]
    have power : a=3*q := by dsimp [a]; linarith only [atcrit]
    have grow : Tendsto (fun n : ℕ => c*(Real.log n)^(q-1)) atTop atTop :=
      ((tendsto_rpow_atTop pq).comp loggrow).const_mul_atTop hc
    filter_upwards [bounds,grow.eventually_gt_atTop M,eventually_ge_atTop 1] with n floor big n1
    have xp : 0<(n:ℝ) := Nat.cast_pos.mpr n1
    have h := mul_lt_mul_of_pos_right big (Real.rpow_pos_of_pos xp (3*q))
    have low := floor.1
    change c*((n:ℝ)^a*(Real.log n)^(q-1))≤_ at low
    rw [power] at low
    exact (by linarith only [h] : M*(n:ℝ)^(3*q)<c*((n:ℝ)^(3*q)*(Real.log n)^(q-1))).trans_le low

/-- The unit-mesh variation at the actual conductor cutoff admits a
cubic bound precisely for orders q>17/10. -/
theorem cubic_fine_cut_variation_iff {q : ℝ} (hq : 1≤q) :
    (∃ M : ℝ, 0≤M ∧ ∀ᶠ N : ℕ in atTop, fineCutPower N ⌊(N:ℝ)^(17/9:ℝ)⌋₊ q≤M*(N:ℝ)^(3*q)) ↔
      17/10<q := by
  constructor
  · rintro ⟨M,_,cap⟩
    by_contra! small
    obtain ⟨n,big,paid⟩ := ((fine_cut_exceeds_cubic_budget hq small M).and cap).exists
    exact big.not_ge paid
  · intro above
    obtain ⟨_,C,_,hC,bounds⟩ := fine_cut_power_at_seventeen_ninths hq
    let a := (17/9:ℝ)*(q+1)
    have diff : 0<3*q-a := by dsimp [a]; linarith only [above]
    have little := (isLittleO_log_rpow_rpow_atTop (q-1) diff).comp_tendsto
      (tendsto_natCast_atTop_atTop (R:=ℝ))
    refine ⟨C,hC.le,?_⟩
    filter_upwards [bounds,little.bound zero_lt_one,eventually_ge_atTop 1] with n cap logcap n1
    have xp : 0<(n:ℝ) := Nat.cast_pos.mpr n1
    change ‖(Real.log n)^(q-1)‖≤1*‖(n:ℝ)^(3*q-a)‖ at logcap
    simp only [one_mul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg n) _),
      abs_of_nonneg (Real.rpow_nonneg xp.le _)] at logcap
    have p := mul_le_mul_of_nonneg_left logcap (Real.rpow_pos_of_pos xp a).le
    rw [←Real.rpow_add xp,show a+(3*q-a)=3*q by ring] at p
    exact cap.2.trans (mul_le_mul_of_nonneg_left p hC.le)

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
