import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositePrimeExcursionsOnOneFixedBand
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.FiniteWeakMomentComparison
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Rectangular levels in the opposite prime excursions

A layer decomposition in the two signed amplitudes retains their joint
numerators. Each coordinate is measured in units of the square root of
that numerator. The sharp product moment is bounded by a single weighted
rectangle, losing only the square of the number of dyadic amplitude levels.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

private def levelCount (b M : ℝ) := ⌊Real.logb 2 (M/b)⌋₊+1
private def heightAt (b : ℝ) (j : ℕ) := b*2^j

private theorem level_for {b M x : ℝ} (hb : 0<b) (hx : b≤x) (hxM : x≤M) :
    ∃ i ∈ range (levelCount b M), heightAt b i ≤ x ∧ x ≤ 2*heightAt b i := by
  let t := Real.logb 2 (x/b)
  let i := ⌊t⌋₊
  have hxb := div_pos (hb.trans_le hx) hb
  have ht : 0≤t := Real.logb_nonneg (by norm_num) ((one_le_div hb).mpr hx)
  have hlo := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hxb).mp (Nat.floor_le ht)
  have hhi := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hxb).mp (Nat.lt_floor_add_one t)
  have hmon : i ≤ ⌊Real.logb 2 (M/b)⌋₊ := Nat.floor_mono (Real.logb_le_logb_of_le
    (by norm_num : (1:ℝ)<2) hxb (div_le_div_of_nonneg_right hxM hb.le))
  refine ⟨i,mem_range.mpr (Nat.lt_succ_of_le hmon),?_,?_⟩
  · rw [Real.rpow_natCast] at hlo
    simpa only [heightAt,mul_comm b] using (le_div_iff₀ hb).mp hlo
  · rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one,Real.rpow_natCast] at hhi
    exact ((div_lt_iff₀ hb).mp hhi).le.trans_eq (by dsimp only [heightAt,i]; ring)

/-- Weighted simultaneous upper tail for two independent amplitude thresholds. -/
def jointRectangle {ι : Type*} (S : Finset ι) (f g μ : ι → ℝ) (u v : ℝ) : ℝ :=
  u*v*∑ j ∈ S, if u≤f j ∧ v≤g j then μ j else 0

/-- Two dyadic levels suffice to see at least a 1/(4R²) share of a
weighted product moment, where R is the logarithmic amplitude span. -/
theorem joint_rectangle_capture {ι : Type*} (S : Finset ι) (f g μ : ι → ℝ) {b M : ℝ}
    (hb : 0<b) (hw : ∀ j ∈ S, 0≤μ j)
    (hf : ∀ j ∈ S, f j ∈ Set.Icc b M) (hg : ∀ j ∈ S, g j ∈ Set.Icc b M) :
    let R := ⌊Real.logb 2 (M/b)⌋₊+1
    ∃ i<R, ∃ k<R, let u := b*2^i; let v := b*2^k
      (∑ j ∈ S,μ j*f j*g j) ≤ 4*(R:ℝ)^2*jointRectangle S f g μ u v ∧
        jointRectangle S f g μ u v ≤ ∑ j ∈ S,μ j*f j*g j := by
  classical
  intro R
  let D := (range R) ×ˢ (range R)
  let term (j : ι) (p : ℕ × ℕ) : ℝ :=
    if heightAt b p.1≤f j ∧ heightAt b p.2≤g j then heightAt b p.1*heightAt b p.2*μ j else 0
  have hnon (j) (hj : j∈S) (p) : 0≤term j p := by
    dsimp only [term]
    split_ifs
    · exact mul_nonneg (by dsimp only [heightAt]; positivity) (hw j hj)
    · exact le_rfl
  have hmajor (j) (hj : j∈S) : μ j*f j*g j ≤ 4*∑ p ∈ D,term j p := by
    obtain ⟨i,hi,hai,hfi⟩ := level_for hb (hf j hj).1 (hf j hj).2
    obtain ⟨k,hk,hak,hgk⟩ := level_for hb (hg j hj).1 (hg j hj).2
    have hp : (i,k)∈D := mem_product.mpr ⟨hi,hk⟩
    have hs := single_le_sum (fun p _ => hnon j hj p) hp
    rw [show term j (i,k)=heightAt b i*heightAt b k*μ j from if_pos ⟨hai,hak⟩] at hs
    have hu : 0≤2*heightAt b i := by dsimp [heightAt]; positivity
    have hfg := mul_le_mul hfi hgk (hb.le.trans (hg j hj).1) hu
    have h := mul_le_mul_of_nonneg_left hfg (hw j hj)
    linarith only [h,hs]
  let price (p : ℕ × ℕ) := jointRectangle S f g μ (heightAt b p.1) (heightAt b p.2)
  have hpEq (p : ℕ × ℕ) : ∑ j ∈ S,term j p=price p := by
    simp only [price,jointRectangle,mul_sum]
    exact sum_congr rfl fun j _ => by dsimp only [term]; split_ifs <;> simp
  have hR : 0<R := Nat.zero_lt_succ _
  have hD : D.Nonempty := ⟨(0,0),mem_product.mpr ⟨mem_range.mpr hR,mem_range.mpr hR⟩⟩
  obtain ⟨p,hp,hmax⟩ := D.exists_max_image price hD
  have hsum := sum_le_sum hmajor
  rw [←mul_sum,sum_comm] at hsum
  simp_rw [hpEq] at hsum
  have hmaxsum := sum_le_sum (s:=D) (fun a ha => hmax a ha)
  have hc : D.card=R*R := by simp [D]
  rw [sum_const,hc,nsmul_eq_mul,Nat.cast_mul] at hmaxsum
  obtain ⟨hi,hk⟩ := mem_product.mp hp
  refine ⟨p.1,mem_range.mp hi,p.2,mem_range.mp hk,?_,?_⟩
  · change _ ≤ 4*(R:ℝ)^2*price p
    linarith only [hsum,hmaxsum]
  · change price p ≤ _
    rw [←hpEq]
    apply sum_le_sum
    intro j hj
    dsimp only [term]
    split_ifs with hh
    · have h₁ : 0≤heightAt b p.2 := by dsimp [heightAt]; positivity
      have h := mul_le_mul hh.1 hh.2 h₁ (hb.le.trans (hf j hj).1)
      simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_right h (hw j hj)
    · exact mul_nonneg (mul_nonneg (hw j hj) (hb.le.trans (hf j hj).1)) (hb.le.trans (hg j hj).1)

open MeasureTheory

private theorem one_layer_price {ι : Type*} (S : Finset ι) (f μ : ι → ℝ)
    {b M : ℝ} (hb : 0<b) (hM : b≤M) (hf : ∀ i ∈ S, f i ∈ Set.Icc b M) :
    ∃ u ∈ Set.Icc b M, (∑ i ∈ S, μ i*f i) ≤
      (1+Real.log (M/b))*(u*∑ i ∈ S,if u≤f i then μ i else 0) := by
  classical
  let χ (i : ι) (u : ℝ) := if u≤f i then μ i else 0
  let W (u : ℝ) := ∑ i ∈ S,χ i u
  let D := 1+Real.log (M/b)
  let A := (∑ i ∈ S,μ i*f i)/D
  have hD : 0<D := by
    have hlog := Real.log_nonneg ((one_le_div hb).mpr hM)
    dsimp only [D]; linarith only [hlog]
  have rep (i : ι) : χ i=(Set.Iic (f i)).indicator (fun _ => μ i) := by
    funext u
    simp only [χ,Set.indicator_apply,Set.mem_Iic]
  have hi (i : ι) : IntervalIntegrable (χ i) volume b M := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hM,rep]
    exact (integrableOn_const (C := μ i) measure_Ioc_lt_top.ne).indicator measurableSet_Iic
  have hread (i : ι) (h : i∈S) : (∫ u in b..M,χ i u)=(f i-b)*μ i := by
    rw [intervalIntegral.integral_of_le hM,rep,setIntegral_indicator measurableSet_Iic,
      Set.Ioc_inter_Iic,inf_eq_right.mpr (hf i h).2,setIntegral_const,Real.volume_real_Ioc_of_le (hf i h).1,
      smul_eq_mul]
  have hlow : W b=∑ i ∈ S,μ i := by
    exact sum_congr rfl fun i h => if_pos (hf i h).1
  have htotal : b*W b+(∫ u in b..M,W u)=∑ i ∈ S,μ i*f i := by
    rw [hlow]
    change b*(∑ i ∈ S,μ i)+(∫ u in b..M,∑ i ∈ S,χ i u)=_
    rw [intervalIntegral.integral_finsetSum (fun i _ => hi i),mul_sum,←sum_add_distrib]
    exact sum_congr rfl fun i h => by rw [hread i h]; ring
  by_contra! hbad
  have hprice (u : ℝ) (hu : u∈Set.Icc b M) : u*W u<A := by
    apply (lt_div_iff₀ hD).mpr
    simpa only [W,χ,D,mul_comm (u*W u)] using hbad u hu
  have hinv : ContinuousOn (fun u : ℝ => A*u⁻¹) (Set.uIcc b M) := by
    apply continuousOn_const.mul
    exact continuousOn_id.inv₀ fun u hu => (hb.trans_le ((Set.uIcc_of_le hM ▸ hu).1)).ne'
  have hWI : IntervalIntegrable W volume b M := by
    have h := IntervalIntegrable.sum S (fun i _ => hi i)
    have hfun : (∑ i ∈ S,χ i) = W := by funext u; simp only [W,Finset.sum_apply]
    rwa [hfun] at h
  have hmon := intervalIntegral.integral_mono_on hM hWI
    hinv.intervalIntegrable (fun u hu => (by
      rw [←div_eq_mul_inv,le_div_iff₀ (hb.trans_le hu.1),mul_comm]
      exact (hprice u hu).le : W u≤A*u⁻¹))
  change (∫ u in b..M,W u) ≤ ∫ u in b..M,A*u⁻¹ at hmon
  rw [intervalIntegral.integral_const_mul,integral_inv_of_pos hb (hb.trans_le hM)] at hmon
  have hA : A*D = ∑ i ∈ S,μ i*f i := div_mul_cancel₀ _ hD.ne'
  dsimp only [D] at hA
  linarith only [hA,hprice b ⟨le_rfl,hM⟩,htotal,hmon]

/-- With freely chosen levels, log-uniform averaging replaces bin
rounding. The loss is the product of the two logarithmic amplitude spans,
which need not be equal. -/
theorem logarithmic_rectangle_capture {ι : Type*} (S : Finset ι) (f g μ : ι → ℝ)
    {b M c N : ℝ} (hb : 0<b) (hM : b≤M) (hc : 0<c) (hN : c≤N)
    (hf : ∀ i ∈ S, f i ∈ Set.Icc b M) (hg : ∀ i ∈ S, g i ∈ Set.Icc c N) :
    ∃ u ∈ Set.Icc b M, ∃ v ∈ Set.Icc c N, (∑ i ∈ S,μ i*f i*g i) ≤
      (1+Real.log (M/b))*(1+Real.log (N/c))*jointRectangle S f g μ u v := by
  classical
  obtain ⟨u,hu,h₁⟩ := one_layer_price S f (fun i => μ i*g i) hb hM hf
  obtain ⟨v,hv,h₂⟩ := one_layer_price S g (fun i => if u≤f i then μ i else 0) hc hN hg
  refine ⟨u,hu,v,hv,?_⟩
  have hlow : 0≤(1+Real.log (M/b))*u := mul_nonneg
    (add_nonneg zero_le_one (Real.log_nonneg ((one_le_div hb).mpr hM))) (hb.le.trans hu.1)
  have hsum : (∑ i ∈ S,(if u≤f i then μ i else 0)*g i) =
      ∑ i ∈ S,if u≤f i then μ i*g i else 0 := sum_congr rfl fun i _ => by split_ifs <;> simp
  have he : (∑ i ∈ S,if v≤g i then (if u≤f i then μ i else 0) else 0) =
      ∑ i ∈ S,if u≤f i ∧ v≤g i then μ i else 0 := sum_congr rfl fun i _ => by split_ifs <;> simp_all
  rw [hsum,he] at h₂
  have hupper := mul_le_mul_of_nonneg_left h₂ hlow
  rw [← mul_assoc] at h₁
  rw [show (∑ i ∈ S,μ i*f i*g i) = ∑ i ∈ S,μ i*g i*f i from sum_congr rfl fun i _ => by ring]
  exact (h₁.trans hupper).trans_eq (by unfold jointRectangle; ring)


private theorem reciprocal_tail_price (n : ℕ) {u : ℝ} (hu : 0≤u) :
    u*(((Icc 1 n).filter fun j : ℕ => u≤(j:ℝ)⁻¹).card:ℝ) ≤ 1 := by
  let V := (Icc 1 n).filter (fun j : ℕ => u≤(j:ℝ)⁻¹)
  change u*(V.card:ℝ)≤1
  rcases V.eq_empty_or_nonempty with hv|hv
  · simp [hv]
  let k := V.max' hv
  have hk := mem_filter.mp (V.max'_mem hv)
  have hk₀ : 0<(k:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hk.1).1
  have hs : V ⊆ Icc 1 k := fun j hj => mem_Icc.mpr
    ⟨(mem_Icc.mp (mem_filter.mp hj).1).1,V.le_max' j hj⟩
  have hc : V.card ≤ k := (card_le_card hs).trans_eq (by simp)
  calc u*(V.card:ℝ) ≤ u*k := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hc) hu
       _ ≤ (k:ℝ)⁻¹*k := mul_le_mul_of_nonneg_right hk.2 hk₀.le
       _ = 1 := inv_mul_cancel₀ hk₀.ne'

/-- On the reciprocal-rank grid, every positive rectangle costs at
most one, while the full product moment is the square of the harmonic
number. Each coordinate spans only a factor n. -/
theorem reciprocal_grid_rectangle_loss (n : ℕ) :
    let S := Icc 1 n ×ˢ Icc 1 n
    let f := fun j : ℕ × ℕ => (j.1:ℝ)⁻¹
    let g := fun j : ℕ × ℕ => (j.2:ℝ)⁻¹
    (∑ j ∈ S,f j*g j)=(harmonic n:ℝ)^2 ∧
      ∀ u v : ℝ, 0≤u → 0≤v → jointRectangle S f g (fun _ => 1) u v ≤ 1 := by
  intro S f g
  have hm := (FiniteWeakMoment.sharp_reciprocal_sample n).1
  constructor
  · change (∑ j ∈ (Icc 1 n ×ˢ Icc 1 n),(j.1:ℝ)⁻¹*(j.2:ℝ)⁻¹)=_
    rw [sum_product]
    simp_rw [←mul_sum]
    rw [←sum_mul,hm,sq]
  · intro u v hu hv
    let A := (Icc 1 n).filter (fun j : ℕ => u≤(j:ℝ)⁻¹)
    let B := (Icc 1 n).filter (fun j : ℕ => v≤(j:ℝ)⁻¹)
    have hset : S.filter (fun j => u≤f j ∧ v≤g j)=A ×ˢ B := by
      ext j
      simp only [S,A,B,f,g,mem_filter,mem_product]
      tauto
    rw [jointRectangle,sum_boole,hset,card_product,Nat.cast_mul]
    calc u*v*((A.card:ℝ)*B.card) = (u*A.card)*(v*B.card) := by ring
         _ ≤ 1*1 := mul_le_mul (reciprocal_tail_price n hu) (reciprocal_tail_price n hv)
           (mul_nonneg hv (Nat.cast_nonneg _)) zero_le_one
         _ = _ := one_mul _


private def signedAmplitude (s : ℝ) (S : Finset ℕ) (H : ℕ) :=
  max 0 (s*oddQuotientPrimeExcess S H)/Real.sqrt H

/-- Every nontrivial quotient has denominator between 1 and H, regardless
of the original support. Chebyshev's estimate bounds its total amplitude. -/
private theorem odd_cut_bound (S : Finset ℕ) (H : ℕ) :
    |oddQuotientPrimeExcess S H|≤(1+Real.log 4)*H := by
  let U := S.filter (fun n => n∈Ioc 0 H)
  have he : oddQuotientPrimeExcess U H=oddQuotientPrimeExcess S H := by
    unfold oddQuotientPrimeExcess
    apply sum_subset (filter_subset _ _)
    intro n hn hnU
    have hcut : n∉Ioc 0 H := fun h => hnU (mem_filter.mpr ⟨hn,h⟩)
    rcases Nat.eq_zero_or_pos n with rfl|hpos
    · simp
    · have hgt : H<n := lt_of_not_ge (fun h => hcut (mem_Ioc.mpr ⟨hpos,h⟩))
      simp [Nat.div_eq_of_lt hgt]
  rw [←he]
  exact oddQuotientPrimeExcess_le U H H (fun _ hn => (mem_filter.mp hn).2)

private theorem amplitude_bound {H L : ℕ} (hHL : H<L^2) (hH : 0<H)
    {s : ℝ} (hs : |s|=1) (S : Finset ℕ) :
    signedAmplitude s S H≤(1+Real.log 4)*L := by
  have hp := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hH : (0:ℝ)<H)
  have hL : Real.sqrt H≤L := (Real.sqrt_le_iff).mpr ⟨Nat.cast_nonneg _,by exact_mod_cast hHL.le⟩
  have hmax := max_le (abs_nonneg (s*oddQuotientPrimeExcess S H)) (le_abs_self _)
  rw [abs_mul,hs,one_mul] at hmax
  have hC : 0≤1+Real.log 4 := by positivity
  apply (div_le_iff₀ hp).mpr
  calc max 0 (s*oddQuotientPrimeExcess S H) ≤ _ := hmax.trans (odd_cut_bound S H)
       _ = (1+Real.log 4)*Real.sqrt H*Real.sqrt H := by
         rw [mul_assoc,Real.mul_self_sqrt (Nat.cast_nonneg H)]
       _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hC) hp.le

/-- Joint rectangular price on the actual prime numerators. Levels u,v
compare the independently signed flanks with u√H and v√H at the same H. -/
def primeRectangle (left : Bool) (s a g d T : ℝ) (k L : ℕ) (u v : ℝ) :=
  jointRectangle (largeOppositePrimeNumerators left s a g d T k L)
    (fun H => signedAmplitude s (Ioc k L) H)
    (fun H => signedAmplitude (-s) (middleTestFlank left k L H) H) (fun H => 1/(H:ℝ)) u v

/-- The original mixed prime moment is equivalent up to an explicit
squared logarithmic loss to the largest dyadic rectangular count. -/
theorem opposite_prime_rectangle (left : Bool) {s a : ℝ} (hs : s=1 ∨ s= -1)
    (ha : 0<a) (g d T : ℝ) (k L : ℕ) :
    let b := a*Real.exp (g*T)
    let R := ⌊Real.logb 2 ((1+Real.log 4)*L/b)⌋₊+1
    let mass := (L:ℝ)*∑ H ∈ largeOppositePrimeNumerators left s a g d T k L,oppositePrimeProduct left s k L H
    ∃ i<R, ∃ j<R, let price := (L:ℝ)*primeRectangle left s a g d T k L (b*2^i) (b*2^j)
      mass≤4*(R:ℝ)^2*price ∧ price≤ mass := by
  intro b R mass
  let S := largeOppositePrimeNumerators left s a g d T k L
  let f := fun H => signedAmplitude s (Ioc k L) H
  let e := fun H => signedAmplitude (-s) (middleTestFlank left k L H) H
  have hsign : |s|=1 := by rcases hs with rfl|rfl <;> norm_num
  have hb : 0<b := mul_pos ha (Real.exp_pos _)
  have hH {H : ℕ} (h : H∈S) : 0<H ∧ H<L^2 := by
    obtain ⟨he,_⟩ := mem_filter.mp h
    obtain ⟨he,hx,_⟩ := mem_filter.mp he
    exact ⟨Nat.cast_pos.mp ((Real.exp_pos _).trans_le hx),mem_range.mp he⟩
  have hlower {y : ℝ} {H : ℕ} (h : H∈S) (hy : b*Real.sqrt H<y) :
      b≤ max 0 y/Real.sqrt H := (le_div_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hH h).1))).mpr
        (hy.le.trans (le_max_right _ _))
  have hf (H : ℕ) (h : H∈S) : f H ∈ Set.Icc b ((1+Real.log 4)*L) :=
    ⟨hlower h (mem_filter.mp h).2.1,amplitude_bound (hH h).2 (hH h).1 hsign _⟩
  have he (H : ℕ) (h : H∈S) : e H ∈ Set.Icc b ((1+Real.log 4)*L) :=
    ⟨hlower h (mem_filter.mp h).2.2,amplitude_bound (hH h).2 (hH h).1 (by simpa only [abs_neg] using hsign) _⟩
  have hm : mass=(L:ℝ)*∑ H ∈ S,(1/(H:ℝ))*f H*e H := by
    apply congrArg ((L:ℝ)*·)
    apply sum_congr rfl
    intro H h
    have hp : (H:ℝ)≠0 := Nat.cast_ne_zero.mpr (hH h).1.ne'
    have hsqrt : Real.sqrt H≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hH h).1)).ne'
    dsimp only [oppositePrimeProduct,f,e,signedAmplitude]
    field_simp [hp,hsqrt]
    rw [Real.sq_sqrt (Nat.cast_nonneg H)] <;> ring
  obtain ⟨i,hi,j,hj,hh₁,hh₂⟩ := joint_rectangle_capture S f e (fun H => 1/(H:ℝ)) hb
    (fun H _ => by positivity) hf he
  refine ⟨i,hi,j,hj,?_,?_⟩
  · rw [hm]
    exact (mul_le_mul_of_nonneg_left hh₁ (Nat.cast_nonneg L)).trans_eq (by unfold primeRectangle; ring)
  · rw [hm]
    exact mul_le_mul_of_nonneg_left hh₂ (Nat.cast_nonneg L)

/-- Failure of RH forces a weighted joint count above two separate
amplitude levels on every sufficiently narrow band. The two thresholds
and the flank may vary with the scale, while both comparisons refer to
the same numerator. -/
theorem rh_or_large_prime_rectangle : RiemannHypothesis ∨
    ∃ a c g d r : ℝ, 0<a ∧ 0<c ∧ 0<g ∧ 0<d ∧ d≤1/4 ∧ 0<r ∧
      ∀ η : ℝ, 0<η → η≤r → ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ n, T n/(1+η)≤Real.log (k n) ∧ Real.log (k n)≤T n) ∧
        let L := fun n => ⌈Real.exp ((1+η)*T n)⌉₊
        let b := fun n => a*Real.exp (g*T n)
        let R := fun n => ⌊Real.logb 2 ((1+Real.log 4)*L n/b n)⌋₊+1
        ∀ᶠ n in atTop, ∃ (s : ℝ) (left : Bool), (s=1 ∨ s= -1) ∧
          ∃ i<R n, ∃ j<R n, c*a^2*Real.exp ((1/2+3*g)*T n) <
            4*(R n:ℝ)^2*(L n*primeRectangle left s a g d (T n) (k n) (L n) (b n*2^i) (b n*2^j)) := by
  obtain hr | ⟨_,_,_,a,c,g,d,r,_,_,_,_,_,ha,hc,hg,hd,hd₁,hr,hseq⟩ :=
    riemannHypothesis_or_fixed_band_opposite_prime_moment
  · exact Or.inl hr
  refine Or.inr ⟨a,c,g,d,r,ha,hc,hg,hd,hd₁,hr,fun η hη hηr => ?_⟩
  obtain ⟨T,k,hT,hk,_,hs⟩ := hseq η hη hηr
  let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
  refine ⟨T,k,hT,hk,?_⟩
  filter_upwards [hs] with n hn
  obtain ⟨_,_,s,left,_,_,hsign,_,_,_,_,_,hp⟩ := hn
  obtain ⟨i,hi,j,hj,hprice,_⟩ := opposite_prime_rectangle left hsign ha g d (T n) (k n) (L n)
  exact ⟨s,left,hsign,i,hi,j,hj,hp.trans_le hprice⟩


end GaloisForLFunctions.ExclusionOfTheCriticalState
