import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheHybridHeightBoundForSharpMoebiusSections
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheOrderOfAbsoluteMertensMass
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.PowerMassOfAnExceptionalSet
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The population of large critical prefixes at a drifting height

Inverse Abel summation compares the absolute Mertens mass with the
reciprocal-square-root mass of the translated critical prefixes. Sorting
the cutoff sites by size then converts a bound on the number of large
prefixes into a bound at that same length. The height may vary with length.
-/
noncomputable section
open Complex Finset Filter
open scoped Topology
open _root_.RHTower (mobCoeff mobiusMertensPartialSum mobiusComplexCoefficient edPoly zetaZeroAbscissa)
open GaloisForLFunctions.MultiscaleMollifiedZetaField
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg zetaZeroWidth_eq_zetaZeroAbscissa_sub_half)
open GaloisForLFunctions.ArithmeticPowerMass (packed_power)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private abbrev sectionAt (u : ℝ) (k : ℕ) := moebiusPoly k (linePoint u)
private abbrev untwist (u : ℝ) (k : ℕ) := (k:ℂ)^(linePoint u)

private theorem section_succ (u : ℝ) (k : ℕ) :
    sectionAt u (k+1)=sectionAt u k+mobCoeff (k+1)*((k+1:ℕ):ℂ)^(-linePoint u) := by
  unfold sectionAt moebiusPoly edPoly
  rw [sum_Icc_succ_top (by omega)]

private theorem mertens_succ (k : ℕ) :
    mobiusMertensPartialSum (k+1)=mobiusMertensPartialSum k+mobCoeff (k+1) := by
  rw [mobiusMertensPartialSum,sum_range_succ]
  rfl

private theorem inverse_abel (u : ℝ) (k : ℕ) :
    mobiusMertensPartialSum k = untwist u k*sectionAt u k+
      ∑ j ∈ range k, sectionAt u j*(untwist u j-untwist u (j+1)) := by
  induction k with
  | zero => simp [mobiusMertensPartialSum,mobiusComplexCoefficient,sectionAt,moebiusPoly,edPoly]
  | succ k ih =>
    have hn : ((k+1:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have hcancel : untwist u (k+1)*((k+1:ℕ):ℂ)^(-linePoint u) = 1 := by
      rw [untwist,←Complex.cpow_add _ _ hn,add_neg_cancel,Complex.cpow_zero]
    rw [mertens_succ,ih,section_succ,sum_range_succ]
    linear_combination -(mobCoeff (k+1))*hcancel

private theorem untwist_step (u : ℝ) {j : ℕ} (hj : 0 < j) :
    ‖untwist u j-untwist u (j+1)‖ ≤ ‖linePoint u‖*(j:ℝ)^(-(1/2:ℝ)) := by
  let s := linePoint u
  let x : ℝ := j
  have hx : 0 < x := Nat.cast_pos.mpr hj
  have hxr : x ≤ x+1 := by linarith
  have hs : s ≠ 0 := fun he => by
    have h := congrArg Complex.re he
    change (linePoint u).re=(0:ℂ).re at h
    norm_num [linePoint_re] at h
  let I := Set.Icc x (x+1)
  have hder : ∀ t∈I, HasDerivWithinAt (fun y : ℝ => (y:ℂ)^s) (s*(t:ℂ)^(s-1)) I t :=
    fun t ht => (hasDerivAt_ofReal_cpow_const (hx.trans_le ht.1).ne' hs).hasDerivWithinAt
  have hbd (t : ℝ) (ht : t∈I) : ‖s*(t:ℂ)^(s-1)‖ ≤ ‖s‖*x^(-(1/2:ℝ)) := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans_le ht.1),Complex.sub_re,Complex.one_re,
      show s.re-1= -(1/2:ℝ) by rw [show s.re=1/2 from linePoint_re u]; ring]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx ht.1 (by norm_num)) (norm_nonneg _)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_Icc _ _)
    (Set.left_mem_Icc.mpr hxr) (Set.right_mem_Icc.mpr hxr)
  rw [show x+1-x=1 by ring,norm_one,mul_one] at h
  rw [norm_sub_rev]
  simpa only [untwist,x,s,Nat.cast_add,Nat.cast_one,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast] using h

/-- Positive weighted mass of the critical-line prefixes through N. -/
def verticalPrefixMass (u : ℝ) (N : ℕ) :=
  ∑ j ∈ Icc 1 N, ‖sectionAt u j‖*(j:ℝ)^(-(1/2:ℝ))

private theorem weighted_range_le (u : ℝ) {k N : ℕ} (hk : k ≤ N) :
    (∑ j ∈ range k, ‖sectionAt u j‖*(j:ℝ)^(-(1/2:ℝ))) ≤ verticalPrefixMass u N := by
  let w := fun j : ℕ => ‖sectionAt u j‖*(j:ℝ)^(-(1/2:ℝ))
  have hz : w 0=0 := by simp [w,sectionAt,moebiusPoly,edPoly]
  have hlarge : (∑ j ∈ range (N+1), w j)=verticalPrefixMass u N := by
    rw [sum_range_succ',hz,add_zero,verticalPrefixMass,_root_.RHTower.sum_Icc_eq_sum_range_shift]
  exact (sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (hk.trans (Nat.le_succ N)))
    (fun j _ _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))).trans_eq hlarge

private theorem mertens_via_prefix_mass (u : ℝ) {k N : ℕ} (hk : k∈Icc 1 N) :
    ‖mobiusMertensPartialSum k‖ ≤ (k:ℝ)^(1/2:ℝ)*‖sectionAt u k‖+‖linePoint u‖*verticalPrefixMass u N := by
  have hpos := (mem_Icc.mp hk).1
  have he := inverse_abel u k
  rw [he]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul,untwist,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hpos),linePoint_re]
  · refine (norm_sum_le _ _).trans ?_
    have hs := sum_le_sum (s:=range k) (fun j _ => show
      ‖sectionAt u j*(untwist u j-untwist u (j+1))‖ ≤ ‖linePoint u‖*(‖sectionAt u j‖*(j:ℝ)^(-(1/2:ℝ))) by
      rcases Nat.eq_zero_or_pos j with rfl|hj
      · simp [sectionAt,moebiusPoly,edPoly]
      rw [norm_mul,mul_left_comm]
      exact mul_le_mul_of_nonneg_left (untwist_step u hj) (norm_nonneg _))
    rw [←mul_sum] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left (weighted_range_le u (mem_Icc.mp hk).2) (norm_nonneg _))

/-- A single arbitrary vertical translate controls the full unweighted
Mertens mass. The cost is linear in the height and logarithmic in the cutoff. -/
theorem mertens_mass_from_vertical_prefixes (u : ℝ) (N : ℕ) :
    mertensAbelMass N ≤ (1+‖linePoint u‖*(1+Real.log N))*verticalPrefixMass u N := by
  have hh : (∑ k ∈ Icc 1 N, (k:ℝ)⁻¹) ≤ 1+Real.log N := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log N
  have hm : 0 ≤ verticalPrefixMass u N := sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hrow (k : ℕ) (hk : k∈Icc 1 N) : ‖mobiusMertensPartialSum k‖/(k:ℝ) ≤
      ‖sectionAt u k‖*(k:ℝ)^(-(1/2:ℝ)) + (‖linePoint u‖*verticalPrefixMass u N)*(k:ℝ)⁻¹ := by
    have hp : 0 < (k:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hk).1
    refine (div_le_div_of_nonneg_right (mertens_via_prefix_mass u hk) hp.le).trans_eq ?_
    have hx : (k:ℝ)^(1/2:ℝ)*(k:ℝ)⁻¹=(k:ℝ)^(-(1/2:ℝ)) := by
      rw [← Real.rpow_neg_one,←Real.rpow_add hp]; norm_num
    rw [add_div,div_eq_mul_inv,div_eq_mul_inv,show ∀ a b c : ℝ, a*b*c=b*(a*c) by intros; ring,hx]
  have hs := sum_le_sum hrow
  rw [←mertens_abel_mass_eq,sum_add_distrib,←mul_sum] at hs
  change mertensAbelMass N ≤ verticalPrefixMass u N+_ at hs
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg _) hm)
  linarith only [hs,hh']

/-- Indices with critical-prefix amplitude above a common threshold. -/
def largeVerticalPrefixes (u H : ℝ) (N : ℕ) :=
  (Icc 1 N).filter (fun j => H < ‖sectionAt u j‖)

private theorem mass_on_subset (u H : ℝ) (S : Finset ℕ) (hs : ∀ j∈S, 1 ≤ j)
    (hH : 0 ≤ H) (hb : ∀ j∈S, ‖sectionAt u j‖ ≤ H) :
    (∑ j∈S, ‖sectionAt u j‖*(j:ℝ)^(-(1/2:ℝ))) ≤ 3*H*((S.card:ℝ)+1)^(1/2:ℝ) := by
  have h := packed_power (by norm_num : (0:ℝ) < 1/2) (by norm_num) S hs
  norm_num at h
  have hn := sum_le_sum (s:=S) (fun j hj => mul_le_mul_of_nonneg_right (hb j hj)
    (Real.rpow_nonneg (Nat.cast_nonneg j) (-(1/2:ℝ))))
  rw [←mul_sum] at hn
  refine hn.trans ((mul_le_mul_of_nonneg_left ?_ hH).trans_eq (by ring))
  convert h using 1 <;> norm_num

/-- Finite two-population inequality: arbitrary heights, arbitrary cutoffs,
and the number of large sections at the very same height and cutoff. -/
theorem vertical_prefix_two_population (u : ℝ) {H U : ℝ} (hH : 0 ≤ H) (hU : 0 ≤ U)
    (N : ℕ) (hb : ∀ j∈Icc 1 N, ‖sectionAt u j‖ ≤ U) :
    verticalPrefixMass u N ≤ 3*H*((N:ℝ)+1)^(1/2:ℝ)+
      3*U*(((largeVerticalPrefixes u H N).card:ℝ)+1)^(1/2:ℝ) := by
  let S := Icc 1 N
  let E := largeVerticalPrefixes u H N
  have hsub : E ⊆ S := filter_subset _ _
  have hc := card_le_card (sdiff_subset (s:=S) (t:=E))
  have hc' : (((S \ E).card:ℝ)+1) ≤ (N:ℝ)+1 := by
    have he : S.card=N := by simp [S,Nat.card_Icc]
    exact add_le_add_right (Nat.cast_le.mpr (hc.trans_eq he)) _
  have h₁ := mass_on_subset u H (S \ E) (fun _ hj => (mem_Icc.mp (mem_sdiff.mp hj).1).1) hH
    (fun j hj => le_of_not_gt (fun h => (mem_sdiff.mp hj).2 (mem_filter.mpr ⟨(mem_sdiff.mp hj).1,h⟩)))
  have h₂ := mass_on_subset u U E (fun _ hj => (mem_Icc.mp (hsub hj)).1) hU (fun j hj => hb j (hsub hj))
  have hsize := Real.rpow_le_rpow (by positivity) hc' (by norm_num : 0 ≤ (1/2:ℝ))
  have hs := add_le_add (h₁.trans (mul_le_mul_of_nonneg_left hsize (by positivity))) h₂
  rw [sum_sdiff hsub] at hs
  exact hs

private theorem line_norm_le (u : ℝ) : ‖linePoint u‖ ≤ 1+|u| := by
  unfold linePoint
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  norm_num

private theorem small_height_cost {e : ℝ} (he : 0 < e) (N : ℕ) {u : ℝ}
    (hu : |u| ≤ ((N:ℝ)+1)^e) :
    1+‖linePoint u‖*(1+Real.log N) ≤ (1+2*(1+1/e))*((N:ℝ)+1)^(2*e) := by
  let X := (N:ℝ)+1
  have hx : 1 ≤ X := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have hp := zero_lt_one.trans_le hx
  have hpow := Real.one_le_rpow hx he.le
  have hlog : Real.log N ≤ Real.log X := by
    rcases Nat.eq_zero_or_pos N with rfl|hN
    · simp [X]
    exact Real.log_le_log (Nat.cast_pos.mpr hN) (le_add_of_nonneg_right zero_le_one)
  have hex := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hp e)
  rw [Real.log_rpow hp] at hex
  have hfrac : Real.log X ≤ X^e/e := (le_div_iff₀ he).mpr (by linarith only [hex])
  have hs : ‖linePoint u‖ ≤ 2*X^e := (line_norm_le u).trans (by linarith only [hu,hpow])
  have hL : 1+Real.log N ≤ (1+1/e)*X^e := by linarith only [hlog,hfrac,hpow]
  have hb := mul_le_mul hs hL (add_nonneg zero_le_one (Real.log_natCast_nonneg N)) (by positivity)
  have hsq : X^e*X^e = X^(2*e) := by rw [←Real.rpow_add hp,two_mul]
  have hh : 1 ≤ X^(2*e) := Real.one_le_rpow hx (by positivity)
  change _ ≤ (1+2*(1+1/e))*X^(2*e)
  calc _ ≤ 1+(2*X^e)*((1+1/e)*X^e) := add_le_add_left hb 1
       _ = 1+2*(1+1/e)*X^(2*e) := by rw [←hsq];ring
       _ ≤ _ := by linarith only [hh]

/-- At every sufficiently large cutoff the population has logarithmic
counting exponent one. The conclusion holds simultaneously on a positive
power height band depending only on the distance to each threshold. -/
theorem many_critical_prefixes_on_a_height_band {b d : ℝ} (hb : b < zetaZeroWidth) (hd : d < 1) :
    ∃ e : ℝ, 0 < e ∧ ∀ᶠ N : ℕ in atTop, ∀ u : ℝ, |u| ≤ ((N:ℝ)+1)^e →
      ((N:ℝ)+1)^d < ((largeVerticalPrefixes u (((N:ℝ)+1)^b) N).card:ℝ) := by
  let v := max 0 d
  have hv : v < 1 := max_lt (by norm_num) hd
  have hv₀ : 0 ≤ v := le_max_left _ _
  let e := min (1/8:ℝ) (min ((zetaZeroWidth-b)/8) ((1-v)/16))
  have he : 0 < e := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have he1 : e ≤ 1/8 := min_le_left _ _
  have heb : e ≤ (zetaZeroWidth-b)/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hed : e ≤ (1-v)/16 := (min_le_right _ _).trans (min_le_right _ _)
  let a := e/2
  have ha : 0 < a := div_pos he (by norm_num)
  obtain ⟨K,hK,hpoint⟩ := hybrid_moebius_section_bound ha
  let U := K*3^a
  have hU : 0 ≤ U := mul_nonneg hK (Real.rpow_nonneg (by norm_num) _)
  let L := 1+2*(1+1/e)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  let q := zetaZeroAbscissa-e
  have hq : 0 ≤ q := by dsimp only [q]; linarith only [he1,_root_.RHTower.half_le_zetaZeroAbscissa]
  have hq' : q < zetaZeroAbscissa := sub_lt_self _ he
  have hw : 1/2+zetaZeroWidth=zetaZeroAbscissa := by rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]; ring
  have hbase : b+1/2+2*e ≤ q := by dsimp only [q]; linarith only [heb,he.le,hw]
  have htail : zetaZeroWidth+e+v/2+2*e ≤ q := by dsimp only [q]; linarith only [hed,he.le,hw]
  refine ⟨e,he,?_⟩
  filter_upwards [eventually_large_mertens_abel_mass hq hq' (L*(3+6*U))] with N hlarge u hu
  let X := (N:ℝ)+1
  have hx : 1 ≤ X := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have hp := zero_lt_one.trans_le hx
  let H := X^b
  let M := U*X^(zetaZeroWidth+e)
  have hM : 0 ≤ M := mul_nonneg hU (Real.rpow_nonneg hp.le _)
  have hbnd (k : ℕ) (hk : k∈Icc 1 N) : ‖sectionAt u k‖ ≤ M := by
    have hku := hpoint k u
    have hkX : (k:ℝ)+1 ≤ X := add_le_add_right (Nat.cast_le.mpr (mem_Icc.mp hk).2) _
    have hlen := Real.rpow_le_rpow (by positivity) hkX (add_nonneg zetaZeroWidth_nonneg ha.le)
    have hxe := Real.rpow_le_rpow_of_exponent_le hx (by linarith only [he1] : e ≤ 1)
    rw [Real.rpow_one] at hxe
    have hy : 2+|u| ≤ 3*X := by linarith only [hu,hxe,hx]
    have hr := Real.rpow_le_rpow (by positivity) hy ha.le
    rw [Real.mul_rpow (by norm_num) hp.le] at hr
    refine hku.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hlen hK) hr (by positivity) (by positivity)).trans_eq ?_)
    dsimp only [M,U]
    rw [show zetaZeroWidth+e=(zetaZeroWidth+a)+a by dsimp only [a];ring,Real.rpow_add hp]
    ring
  by_contra! hsmall
  let S := largeVerticalPrefixes u H N
  have hc : (S.card:ℝ)+1 ≤ 2*X^v :=
    by linarith only [hsmall,Real.rpow_le_rpow_of_exponent_le hx (le_max_right 0 d), Real.one_le_rpow hx hv₀]
  have hhalf := Real.rpow_le_rpow (by positivity) hc (by norm_num : 0 ≤ (1/2:ℝ))
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hp.le _),←Real.rpow_mul hp.le] at hhalf
  have htwo : (2:ℝ)^(1/2:ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (1/2:ℝ) ≤ 1)
  have hpop := vertical_prefix_two_population u (Real.rpow_nonneg hp.le b) hM N hbnd
  have hroot : ((S.card:ℝ)+1)^(1/2:ℝ) ≤ 2*X^(v/2) := by
    rw [show v/2 = v*(1/2) by ring]
    exact hhalf.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hp.le _))
  have hcost := small_height_cost he N hu
  have hmain := mertens_mass_from_vertical_prefixes u N
  have hmass : 0 ≤ verticalPrefixMass u N := sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hfirst : 3*H*X^(1/2:ℝ)*X^(2*e) ≤ 3*X^q := by
    dsimp only [H]
    rw [mul_assoc 3,←Real.rpow_add hp,mul_assoc 3,←Real.rpow_add hp]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hbase) (by norm_num)
  have hsecond : (3*M)*(((S.card:ℝ)+1)^(1/2:ℝ))*X^(2*e) ≤ 6*U*X^q := by
    have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity : (0:ℝ) ≤ 3*M))
      (Real.rpow_nonneg hp.le (2*e))
    refine h₁.trans ?_
    calc (3*M)*(2*X^(v/2))*X^(2*e) = 6*U*(X^(zetaZeroWidth+e)*X^(v/2)*X^(2*e)) := by dsimp only [M]; ring
         _ ≤ _ := by
           rw [←Real.rpow_add hp,←Real.rpow_add hp]
           exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx htail) (by positivity)
  have hsum := mul_le_mul_of_nonneg_right hpop (Real.rpow_nonneg hp.le (2*e))
  have hpop' : verticalPrefixMass u N*X^(2*e) ≤ (3+6*U)*X^q := by
    change _ ≤ (3*H*X^(1/2:ℝ)+3*M*(((S.card:ℝ)+1)^(1/2:ℝ)))*X^(2*e) at hsum
    linarith only [hsum,hfirst,hsecond]
  have hlim := hmain.trans (mul_le_mul_of_nonneg_right hcost hmass)
  have hx' := mul_le_mul_of_nonneg_left hpop' hL
  change L*(3+6*U)*X^q < _ at hlarge
  change mertensAbelMass N ≤ L*X^(2*e)*verticalPrefixMass u N at hlim
  linarith only [hlarge,hlim,hx']

/-- Unnormalized pth moment across all integer cutoffs at one height. -/
def cutoffMoment (p u : ℝ) (N : ℕ) := ∑ j ∈ Icc 1 N, ‖sectionAt u j‖^p

/-- Every positive moment across cutoffs has exponent 1+p times the zero
width in the sense 1+p(Θ−1/2). The power squeeze holds throughout a
height band whose width grows as a positive power of the cutoff. -/
theorem cutoff_moment_power_squeeze {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) :
    ∃ v : ℝ, 0 < v ∧ ∀ᶠ N : ℕ in atTop, ∀ u : ℝ, |u| ≤ ((N:ℝ)+1)^v →
      ((N:ℝ)+1)^(1+p*zetaZeroWidth-ε) < cutoffMoment p u N ∧
        cutoffMoment p u N ≤ ((N:ℝ)+1)^(1+p*zetaZeroWidth+ε) := by
  let b := zetaZeroWidth-ε/(2*p)
  let d := 1-ε/2
  have hbw : b < zetaZeroWidth := sub_lt_self _ (by positivity)
  have hd : d < 1 := sub_lt_self _ (by positivity)
  obtain ⟨v,hv,hcount⟩ := many_critical_prefixes_on_a_height_band hbw hd
  let a := ε/(4*p)
  have ha : 0 < a := div_pos hε (by positivity)
  obtain ⟨C,hC,hsec⟩ := hybrid_moebius_section_bound ha
  let B := C*3^a
  have hB : 0 ≤ B := mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  have hbig := (tendsto_rpow_atTop (show 0 < ε/2 by positivity)).comp
    (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  refine ⟨min v 1,lt_min hv zero_lt_one,?_⟩
  filter_upwards [hcount,hbig.eventually_ge_atTop (B^p)] with N ht hc u hu
  let X := (N:ℝ)+1
  have hX : 1 ≤ X := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have hXpos := zero_lt_one.trans_le hX
  have hsmall := Real.rpow_le_rpow_of_exponent_le hX (min_le_left v 1)
  have hstep := ht u (hu.trans hsmall)
  let S := largeVerticalPrefixes u (X^b) N
  have ht₁ : X^d*(X^b)^p < (S.card:ℝ)*(X^b)^p :=
    mul_lt_mul_of_pos_right hstep (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hXpos _) _)
  have ht₂ : (S.card:ℝ)*(X^b)^p ≤ cutoffMoment p u N := by
    rw [←nsmul_eq_mul,←sum_const]
    refine (sum_le_sum (s:=S) (fun j hj => Real.rpow_le_rpow (Real.rpow_nonneg hXpos.le _)
      (mem_filter.mp hj).2.le hp.le)).trans ?_
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ => Real.rpow_nonneg (norm_nonneg _) _
  constructor
  · have h := ht₁.trans_le ht₂
    rw [←Real.rpow_mul hXpos.le,←Real.rpow_add hXpos] at h
    exact (show (d+b*p)=1+p*zetaZeroWidth-ε by dsimp only [b,d]; field_simp [hp.ne'];ring) ▸ h
  · have hyt := Real.rpow_le_rpow_of_exponent_le hX (min_le_right v 1)
    rw [Real.rpow_one] at hyt
    have hh : 2+|u| ≤ 3*X := by linarith only [hu,hyt,hX]
    have hy := Real.rpow_le_rpow (by positivity) hh ha.le
    rw [Real.mul_rpow (by norm_num) hXpos.le] at hy
    have hU : ∀ k∈Icc 1 N, ‖sectionAt u k‖ ≤ B*X^(zetaZeroWidth+2*a) := by
      intro k hk
      have hh : (k:ℝ)+1 ≤ X := add_le_add_right (Nat.cast_le.mpr (mem_Icc.mp hk).2) _
      have hs := Real.rpow_le_rpow (by positivity) hh (add_nonneg zetaZeroWidth_nonneg ha.le)
      refine (hsec k u).trans ((mul_le_mul (mul_le_mul_of_nonneg_left hs hC) hy (by positivity) (by positivity)).trans_eq ?_)
      rw [show zetaZeroWidth+2*a=(zetaZeroWidth+a)+a by ring,Real.rpow_add hXpos]
      dsimp only [B]; ring
    have sm := sum_le_sum (s:=Icc 1 N) (fun j hj => Real.rpow_le_rpow (norm_nonneg _)
      (hU j hj) hp.le)
    rw [sum_const,nsmul_eq_mul,Nat.card_Icc] at sm
    simp only [Nat.add_sub_cancel] at sm
    have hn : (N:ℝ) ≤ X := le_add_of_nonneg_right zero_le_one
    have hupp := sm.trans (mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg (by positivity) _))
    rw [Real.mul_rpow hB (Real.rpow_nonneg hXpos.le _),←Real.rpow_mul hXpos.le,
      show (zetaZeroWidth+2*a)*p=p*zetaZeroWidth+ε/2 by dsimp only [a]; field_simp [hp.ne']; ring] at hupp
    refine hupp.trans ?_
    change B^p ≤ X^(ε/2) at hc
    have hk := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hXpos.le (p*zetaZeroWidth+ε/2))
    calc X*(B^p*X^(p*zetaZeroWidth+ε/2)) ≤ X*(X^(ε/2)*X^(p*zetaZeroWidth+ε/2)) :=
           mul_le_mul_of_nonneg_left hk hXpos.le
         _ = X^(1+p*zetaZeroWidth+ε) := by
           rw [←Real.rpow_add hXpos,←Real.rpow_one X,←Real.rpow_add hXpos]
           congr 1;ring

/-- Along every subpolynomially drifting height the ordinary logarithmic
growth order exists for every positive moment across the prefixes. -/
theorem drifting_height_cutoff_moment_order {p : ℝ} (hp : 0 < p) (u : ℕ → ℝ)
    (hu : ∀ v : ℝ, 0 < v → ∀ᶠ N : ℕ in atTop, |u N| ≤ ((N:ℝ)+1)^v) :
    Tendsto (fun N : ℕ => Real.log (cutoffMoment p (u N) N)/Real.log ((N:ℝ)+1))
      atTop (𝓝 (1+p*zetaZeroWidth)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨v,hv,h⟩ := cutoff_moment_power_squeeze hp (show 0 < ε/2 by positivity)
  filter_upwards [h,hu v hv,eventually_ge_atTop (1:ℕ)] with N hh hvN hn
  let X := (N:ℝ)+1
  have hx : 1 < X := by dsimp only [X]; exact lt_add_of_pos_left _ (Nat.cast_pos.mpr hn)
  have hlog := Real.log_pos hx
  have hpos := zero_lt_one.trans hx
  have hbounds := hh (u N) hvN
  have hlo := Real.log_lt_log (Real.rpow_pos_of_pos hpos _) hbounds.1
  have hhi := Real.log_le_log ((Real.rpow_pos_of_pos hpos _).trans hbounds.1) hbounds.2
  rw [Real.log_rpow hpos] at hlo hhi
  rw [Real.dist_eq,abs_lt]
  constructor
  · have hl := (lt_div_iff₀ hlog).mpr hlo
    linarith only [hl,hε]
  · have hr := (div_le_iff₀ hlog).mpr hhi
    linarith only [hr,hε]

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
