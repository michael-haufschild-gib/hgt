import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeReadingsBeyondTheHyperbola
import GaloisForLFunctions.RHTower.MertensThirdTheorem
import GaloisForLFunctions.RHTower.Sieve.MertensIntervalShell
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# Tilting the Euler deletion price at exponent one

A displacement of size O(1/log y) changes the inverse Euler product by
a bounded factor. The local cost is proportional to log(p)/p, so the
first Mertens estimate pays for all primes at once. The dependence on
the tilt is explicit before taking an observation limit.
-/
noncomputable section
open Finset Filter
open scoped Topology Classical
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev C₁ := _root_.RHTower.Sieve.mertensIntervalConst
private abbrev gap := 1-((1/2:ℝ)^(1/2:ℝ))
private theorem gap_pos : 0 < gap := sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num))

private theorem exponential_increment {u λ : ℝ} (hu : 0 ≤ u) (hλ : u ≤ λ) :
    Real.exp u-1 ≤ Real.exp λ*u := by
  have h := Real.add_one_le_exp (-u)
  rw [Real.exp_neg] at h
  have h' := (le_div_iff₀ (Real.exp_pos u)).mp (by simpa only [one_div] using h :
    -u+1 ≤ 1/Real.exp u)
  have h'' := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hλ) hu
  linarith only [h',h'']

private theorem tilted_factor {p : ℕ} (hp : p.Prime) {δ λ : ℝ}
    (hδ : 0 ≤ δ) (hh : δ ≤ 1/2) (hz : δ*Real.log p ≤ λ) :
    (1-(1/(p:ℝ))^(1-δ))⁻¹ ≤ (1-(1/(p:ℝ)))⁻¹*
      Real.exp ((Real.exp λ/gap*δ)*(Real.log p/(p:ℝ))) := by
  let a := 1/(p:ℝ)
  let w := a^(1-δ)
  let E := ((Real.exp λ/gap)*δ)*(Real.log p/(p:ℝ))
  have pp := (Nat.cast_pos (α:=ℝ)).mpr hp.pos
  have p2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have ap : 0 < a := one_div_pos.mpr pp
  have ha : a ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) p2
  have wa : w=Real.exp (δ*Real.log p)*a := by
    rw [show 1-δ=(-δ)+1 by ring,Real.rpow_add ap,Real.rpow_one,Real.rpow_def_of_pos ap]
    dsimp only [a]
    rw [one_div,Real.log_inv,neg_mul_neg,mul_comm (Real.log (p:ℝ)) δ]
  have wmax : w ≤ (1/2:ℝ)^(1/2:ℝ) := by
    apply (Real.rpow_le_rpow_of_exponent_ge ap (ha.trans (by norm_num)) (by linarith : 1/2 ≤ 1-δ)).trans
    exact Real.rpow_le_rpow ap.le ha (by norm_num)
  have gw : gap ≤ 1-w := sub_le_sub_left wmax _
  have gpos := gap_pos.trans_le gw
  have aa : 0 < 1-a := by linarith only [ha]
  have inc := exponential_increment (mul_nonneg hδ (Real.log_natCast_nonneg p)) hz
  have hdiff : w-a ≤ (Real.exp λ*δ)*(Real.log p/(p:ℝ)) := by
    have hl := mul_le_mul_of_nonneg_right inc ap.le
    rw [wa]
    dsimp only [a] at hl ⊢
    linarith only [hl]
  have e0 : 0 ≤ E := mul_nonneg (mul_nonneg (div_nonneg (Real.exp_pos _).le gap_pos.le) hδ)
    (div_nonneg (Real.log_natCast_nonneg p) pp.le)
  have hbound : 1-a ≤ (1-w)*(1+E) := by
    have add := mul_le_mul_of_nonneg_right gw e0
    have eq : gap*E=(Real.exp λ*δ)*(Real.log p/(p:ℝ)) := by
      dsimp only [E];field_simp [gap_pos.ne']
    rw [eq] at add
    linarith only [hdiff,add]
  have strong := hbound.trans (mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp E) gpos.le)
  change (1-w)⁻¹ ≤ (1-a)⁻¹*Real.exp E
  rw [inv_mul_eq_div]
  rw [←one_div,div_le_div_iff₀ gpos aa]
  linarith only [strong]

/-- The inverse prime Euler product is stable under a finite critical
tilt. Its price relative to the untilted product depends only on the
displacement times the logarithmic width and on the first Mertens constant. -/
theorem price_of_a_critical_euler_tilt {y : ℕ} (hy : 1 ≤ y) {δ λ : ℝ}
    (hd : 0 ≤ δ) (hh : δ ≤ 1/2) (hz : δ*Real.log y ≤ λ) :
    deletionPrice (1-δ) y ≤ deletionPrice 1 y*
      Real.exp ((Real.exp λ/gap)*(λ+δ*C₁)) := by
  let P := Nat.primesLE y
  let A := Real.exp λ/gap*δ
  have big (p : ℕ) (hp : p ∈ P) : δ*Real.log p ≤ λ := by
    obtain ⟨hl,pr⟩ := Nat.mem_primesLE.mp hp
    exact (mul_le_mul_of_nonneg_left (Real.log_le_log (Nat.cast_pos.mpr pr.pos) (Nat.cast_le.mpr hl)) hd).trans hz
  have factor := prod_le_prod (s:=P)
    (f:=fun p : ℕ => (1-(1/(p:ℝ))^(1-δ))⁻¹)
    (g:=fun p : ℕ => (1-1/(p:ℝ))⁻¹*Real.exp (A*(Real.log p/(p:ℝ))))
    (fun p hp => inv_nonneg.mpr (sub_nonneg.mpr (deletion_weight_lt_one (by linarith : 0 < 1-δ) (Nat.mem_primesLE.mp hp).2).le))
    (fun p hp => tilted_factor (Nat.mem_primesLE.mp hp).2 hd hh (big p hp))
  have hsub : P ⊆ Nat.primesLE y \ Nat.primesLE 1 := by
    intro p hp
    apply mem_sdiff.mpr
    exact ⟨hp,fun h => by have h₁ := (Nat.mem_primesLE.mp h).1;have h₂ := (Nat.mem_primesLE.mp h).2.two_le;omega⟩
  have first := _root_.RHTower.Sieve.sum_log_div_prime_interval_le (a:=1) le_rfl hy hsub
  rw [Nat.cast_one,Real.log_one,sub_zero] at first
  have apos := div_nonneg (Real.exp_pos λ).le gap_pos.le
  have main := mul_le_mul_of_nonneg_left first (mul_nonneg apos hd)
  have endprice := mul_le_mul_of_nonneg_left (add_le_add_right hz (δ*C₁)) apos
  have hlog : A*(∑ p∈P,Real.log p/(p:ℝ)) ≤ (Real.exp λ/gap)*(λ+δ*C₁) := by
    dsimp only [A]
    linarith only [main,endprice]
  rw [prod_mul_distrib,←Real.exp_sum,←mul_sum] at factor
  have pos := deletionPrice_one_le (by norm_num : (0:ℝ) < 1) y
  have id : (∏ p∈P,(1-1/(p:ℝ))⁻¹)=deletionPrice 1 y := by simp only [P,deletionPrice,Real.rpow_one]
  rw [id] at factor
  exact factor.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlog) (zero_le_one.trans pos))

private theorem untilted {y : ℕ} : deletionPrice 1 y=(_root_.RHTower.mertensPrimeProduct y)⁻¹ := by
  rw [deletionPrice,_root_.RHTower.mertensPrimeProduct,←prod_inv_distrib]
  simp only [Real.rpow_one]
  congr 1
  change (∏ p∈(range (y+1)).filter Nat.Prime,(1-1/(p:ℝ)))=_
  rw [prod_filter,Nat.range_succ_eq_Icc_zero]
  simp only [one_div]

private theorem ordinary_price : ∃ C : ℝ,0 < C ∧ ∀ y : ℕ, deletionPrice 1 y ≤ C*(1+Real.log y) := by
  let b := Real.exp (-Real.eulerMascheroniConstant)/2
  have hb : 0 < b := half_pos (Real.exp_pos _)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (_root_.RHTower.tendsto_mertensPrimeProduct_mul_log.eventually_const_lt
    (show b < Real.exp (-Real.eulerMascheroniConstant) from half_lt_self (Real.exp_pos _)))
  let C := max (deletionPrice 1 J) (1/b)
  have cp : 0 < C := (one_div_pos.mpr hb).trans_le (le_max_right ..)
  refine ⟨C,cp,fun y => ?_⟩
  rcases le_total y J with h|h
  · exact ((deletionPrice_mono (by norm_num : (0:ℝ) < 1) h).trans (le_max_left ..)).trans
      (le_mul_of_one_le_right cp.le (by have := Real.log_natCast_nonneg y;linarith))
  · have hy := hJ y h
    have hp := _root_.RHTower.mertensPrimeProduct_pos y
    rw [untilted,←one_div]
    have hdiv : 1/(_root_.RHTower.mertensPrimeProduct y) ≤ (1/b)*Real.log y := by
      apply (div_le_iff₀ hp).mpr
      rw [one_div_mul_eq_div,div_mul_eq_mul_div,le_div_iff₀ hb,one_mul]
      simpa only [mul_comm] using hy.le
    exact hdiv.trans (mul_le_mul (le_max_right ..) (by linarith : Real.log y ≤ 1+Real.log y)
      (Real.log_natCast_nonneg _) cp.le)

/-- Exponential decay in the ratio of the endpoint logarithm to the
logarithmic prime cutoff. The constant and the shift in the denominator
can depend on the chosen decay rate but are uniform in both endpoints. -/
theorem exponential_rough_prefix_at_every_prime_wall {λ : ℝ} (hλ : 0 < λ) :
    ∃ C : ℝ,0 < C ∧ ∀ X y t : ℕ, 1 ≤ X → 1 ≤ y → t ≤ X →
      |coprimeMoebiusSum (primorial y) t| ≤
        C*(1+Real.log y)*(X:ℝ)*Real.exp (-(λ*Real.log X/(16*(1+λ)+Real.log y))) := by
  have strip : _root_.RHTower.zetaZeroAbscissa < 7/8 := by
    linarith only [GaloisForLFunctions.ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths]
  obtain ⟨B,hB,hbase⟩ := exists_moebius_power_bound_of_abscissa_lt strip
  obtain ⟨P,hP,price⟩ := ordinary_price
  let E := Real.exp ((Real.exp λ/gap)*(λ+C₁))
  have hE : 0 < E := Real.exp_pos _
  refine ⟨2*(B+1)*P*E,by positivity,fun X y t hX hy ht => ?_⟩
  let L := 16*(1+λ)+Real.log y
  let δ := λ/L
  have logy := Real.log_natCast_nonneg y
  have hl : 0 < L := by dsimp only [L];linarith only [hλ,logy]
  have hd : 0 ≤ δ := div_nonneg hλ.le hl.le
  have hd16 : δ ≤ 1/16 := (div_le_iff₀ hl).mpr (by dsimp only [L];linarith only [logy])
  have hsmall : δ*Real.log y ≤ λ := by
    have hr : Real.log y ≤ L := by dsimp only [L];linarith only [hλ]
    exact (mul_le_mul_of_nonneg_left hr hd).trans_eq (div_mul_cancel₀ _ hl.ne')
  have hpos : 0 < 1-δ := by linarith only [hd16]
  have base (n : ℕ) : |coprimeMoebiusSum 1 n| ≤ (B+1)*(n:ℝ)^(1-δ) := by
    rcases Nat.eq_zero_or_pos n with rfl|hn
    · simp [coprimeMoebiusSum,Real.zero_rpow hpos.ne']
    · have h := hbase n hn
      have up := Real.rpow_le_rpow_of_exponent_le ((Nat.one_le_cast (α:=ℝ)).mpr hn)
        (show (7/8:ℝ) ≤ 1-δ by linarith only [hd16])
      apply le_trans _ (mul_le_mul (by linarith : B ≤ B+1) up (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity))
      simpa [coprimeMoebiusSum,coprimeMoebiusIndicator,moebiusReal] using h
  have cost := price_of_a_critical_euler_tilt hy hd (by linarith only [hd16]) hsmall
  have hcost : deletionPrice (1-δ) y ≤ P*(1+Real.log y)*E := by
    have hb : λ+δ*C₁ ≤ λ+C₁ := by
      apply add_le_add_left
      exact mul_le_of_le_one_left _root_.RHTower.Sieve.mertensIntervalConst_nonneg (by linarith only [hd16])
    apply cost.trans
    exact mul_le_mul (price y) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb
      (div_nonneg (Real.exp_pos _).le gap_pos.le))) (Real.exp_pos _).le (mul_nonneg hP.le (by linarith))
  have estimate := all_frozen_rows_from_full_prefix hpos (show 0 ≤ B+1 by positivity) base t y
  have x0 := (Nat.cast_pos (α:=ℝ)).mpr hX
  have form : (X:ℝ)^(1-δ)=(X:ℝ)*Real.exp (-(λ*Real.log X/L)) := by
    rw [sub_eq_add_neg,Real.rpow_add x0,Real.rpow_one,Real.rpow_def_of_pos x0]
    congr 2
    dsimp only [δ];ring
  apply estimate.trans
  have coeff := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 2*(B+1) by positivity)
  have pwr := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr ht) hpos.le
  apply (mul_le_mul coeff pwr (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (by have := Real.log_natCast_nonneg y;positivity)).trans_eq
  rw [form]
  dsimp only [L]
  ring

/-- A common, subpolynomial prime cutoff far above every fixed power of
log X still admits every inverse-logarithmic gain in its signed prefixes. -/
theorem logarithmic_savings_through_subpower_prime_walls (p : ℕ) {K : ℝ} (hk : 0 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ y t : ℕ, 1 ≤ y → t ≤ X →
      Real.log y*Real.log (Real.log X) ≤ K*Real.log X →
      |coprimeMoebiusSum (primorial y) t| * Real.log X^p ≤ C*(X:ℝ) := by
  let m := (p:ℝ)+2
  let λ := 2*(K+1)*m
  have hm : 0 < m := by dsimp only [m];positivity
  have hλ : 0 < λ := by dsimp only [λ];positivity
  obtain ⟨C,hC,estimate⟩ := exponential_rough_prefix_at_every_prime_wall hλ
  refine ⟨2*C,by positivity,?_⟩
  have grow := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have loglog := Real.tendsto_log_atTop.comp grow
  have little := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp grow)
  filter_upwards [grow.eventually_ge_atTop 1,loglog.eventually_ge_atTop (K+1),eventually_ge_atTop 1,
    little.eventually_lt_const (show 0 < 1/(16*(1+λ)) by positivity)]
    with X hL hLL xp hsmall
  intro y t hy ht hwall
  let L := Real.log (X:ℝ)
  let w := Real.log (y:ℝ)
  let D := 16*(1+λ)+w
  have w0 : 0 ≤ w := Real.log_natCast_nonneg _
  have L1 : 1 ≤ L := hL
  have lp := zero_lt_one.trans_le L1
  change K+1 ≤ Real.log L at hLL
  change Real.log L/L < 1/(16*(1+λ)) at hsmall
  change w*Real.log L ≤ K*L at hwall
  have d0 : 0 < D := by dsimp only [D];linarith only [hλ,w0]
  have tiny := (div_lt_div_iff₀ lp (show 0 < 16*(1+λ) by positivity)).mp hsmall
  have wL : w ≤ L := by
    have hmul := mul_le_mul_of_nonneg_left (show K ≤ Real.log L by linarith only [hLL]) w0
    by_cases hzero : K=0
    · rw [hzero,zero_mul] at hwall
      have hpos : 0 < Real.log L := by linarith only [hLL,hzero]
      have := (mul_nonpos_iff_of_pos_right hpos).mp hwall
      linarith only [this,L1]
    · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne hk (Ne.symm hzero))).mp
        (hmul.trans (by simpa only [mul_comm K L] using hwall))
  have rate : m*Real.log L ≤ λ*L/D := by
    apply (le_div_iff₀ d0).mpr
    have hbd : Real.log L*D ≤ (K+1)*L := by
      dsimp only [D];linarith only [tiny,hwall]
    have h := mul_le_mul_of_nonneg_left hbd hm.le
    have hpos := mul_nonneg (mul_nonneg hm.le (by linarith : 0 ≤ K+1)) lp.le
    dsimp only [λ];nlinarith only [h,hpos]
  have save : Real.exp (-(λ*L/D)) ≤ 1/L^(p+2) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg rate)).trans_eq
    rw [Real.exp_neg,one_div,←Real.rpow_natCast L (p+2),Real.rpow_def_of_pos lp]
    congr 2
    dsimp only [m];push_cast;ring
  have hprefix := estimate X y t xp hy ht
  have wprice : 1+w ≤ 2*L := by linarith only [wL,L1]
  have hx := Nat.cast_nonneg (α:=ℝ) X
  have factor := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left wprice hC.le) hx)
    save (Real.exp_pos _).le (by positivity)
  have fin := mul_le_mul_of_nonneg_right (hprefix.trans factor) (pow_nonneg lp.le p)
  apply fin.trans
  change C*(2*L)*(X:ℝ)*(1/L^(p+2))*L^p ≤ 2*C*(X:ℝ)
  have eq : C*(2*L)*(X:ℝ)*(1/L^(p+2))*L^p=(2*C*(X:ℝ))/L := by
    rw [pow_add];field_simp [lp.ne'];ring
  rw [eq]
  exact div_le_self (by positivity) L1

end GaloisForLFunctions.RestrictedFactorizationCalculus
