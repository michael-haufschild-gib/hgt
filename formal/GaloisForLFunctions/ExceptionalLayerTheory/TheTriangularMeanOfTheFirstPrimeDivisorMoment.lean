import GaloisForLFunctions.ExceptionalLayerTheory.TheSquareRootErrorInTheFirstPrimeDivisorMoment
import GaloisForLFunctions.ExceptionalLayerTheory.ThePowerModesOfTheOddQuotientMean
import GaloisForLFunctions.ExceptionalLayerTheory.TheQuarterExponentOfTheOddQuotientPrimeCount
import GaloisForLFunctions.ExceptionalLayerTheory.APowerSavingForTheUnaveragedOddQuotientPrimeCount
import GaloisForLFunctions.RHTower.CarlsonHalfPlaneProducerFloor

/-!
# The triangular first prime-divisor moment

The linear centering disappears on taking a dyadic difference. A sublinear
term is determined by that difference at all larger dyadic cutoffs. This
recovers the raw mean from the finite parity count and the two unrestricted
power rows.
-/

noncomputable section
open Finset Filter Complex Topology
open _root_.RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem double_quotient_sum (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ range (2*N), f (j/2)) = 2*∑ j ∈ range N, f j := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,show 2*n+2=2*n+1+1 by omega,sum_range_succ,sum_range_succ,ih,
      sum_range_succ f,show (2*n+1)/2=n by omega,show 2*n/2=n by omega]
    ring

private theorem sharp_moment_deficit (j N : ℕ) (hj : j ≤ N) :
    distinctPrimeLogMoment j - Real.log (j.factorial:ℕ) =
      -(∑ d ∈ Icc 1 N, primePowerPart d*((j/d:ℕ):ℝ)) := by
  have hp : (∑ p ∈ Nat.primesLE j, Real.log p*((j/p:ℕ):ℝ)) =
      ∑ p ∈ Nat.primesLE N, Real.log p*((j/p:ℕ):ℝ) := by
    apply sum_subset (Nat.primesLE_mono hj)
    intro p hp hnot
    have hlt : j<p := lt_of_not_ge fun h => hnot (Nat.mem_primesLE.mpr ⟨h,(Nat.mem_primesLE.mp hp).2⟩)
    simp [Nat.div_eq_of_lt hlt]
  have hm : (∑ d ∈ Icc 1 j, ArithmeticFunction.vonMangoldt d*((j/d:ℕ):ℝ)) =
      ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d*((j/d:ℕ):ℝ) := by
    apply sum_subset (Icc_subset_Icc_right hj)
    intro d hd hnot
    have hlt : j<d := lt_of_not_ge fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,h⟩)
    simp [Nat.div_eq_of_lt hlt]
  have hi : Icc 1 j = Ioc 0 j := by ext n; simp only [mem_Icc,mem_Ioc]; omega
  rw [hi,ArithmeticOfSquareRootPrecision.chebyshevTransform_vonMangoldt] at hm
  rw [distinctPrimeLogMoment,hp,hm,Nat.primesLE_eq_filter_Icc_one,sum_filter,← sum_sub_distrib,←sum_neg_distrib]
  exact sum_congr rfl fun d _ => by
    by_cases hd : d.Prime <;> simp [primePowerPart,hd,ArithmeticFunction.vonMangoldt_apply_prime]

/-- Doubling the integer cutoff reads exactly the normalized parity count
of the actual proper-prime-power weights. -/
theorem triangularDistinctPrimeLogMoment_dyadic {N : ℕ} (hN : 0 < N) :
    triangularDistinctPrimeLogMoment (2*N)-2*triangularDistinctPrimeLogMoment N =
      -(∑ d ∈ Icc 1 (2*N), primePowerPart d*
        discreteQuotientMean (fun n => ((n%2:ℕ):ℝ)) d (2*N))/(2*(N:ℝ)) := by
  let F (j : ℕ) := distinctPrimeLogMoment j-Real.log (j.factorial:ℕ)
  have hfloor (j d : ℕ) : ((j/d:ℕ):ℝ)-2*(((j/2)/d:ℕ):ℝ)=((j/d%2:ℕ):ℝ) := by
    have hdiv : (j/2)/d=(j/d)/2 := by
      rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,mul_comm 2 d]
    rw [hdiv]
    have h := congrArg (Nat.cast (R := ℝ)) (Nat.mod_add_div (j/d) 2)
    push_cast at h; linarith only [h]
  have hrow (j : ℕ) (hj : j ∈ range (2*N)) :
      F j-2*F (j/2)= -(∑ d ∈ Icc 1 (2*N), primePowerPart d*((j/d%2:ℕ):ℝ)) := by
    dsimp only [F]
    rw [sharp_moment_deficit _ _ (mem_range.mp hj).le,
      sharp_moment_deficit _ _ ((Nat.div_le_self j 2).trans (mem_range.mp hj).le),mul_neg,
      neg_sub_neg,← neg_sub,neg_inj,mul_sum,← sum_sub_distrib]
    exact sum_congr rfl fun d _ => by rw [← hfloor]; ring
  have he := Finset.sum_congr (s₁ := range (2*N)) rfl hrow
  rw [sum_sub_distrib,←mul_sum,double_quotient_sum,sum_neg_distrib] at he
  simp only [discreteQuotientMean,mul_sum]
  rw [sum_comm]
  change (∑ j ∈ range (2*N), F j)/((2*N:ℕ):ℝ)+repeatedPrimeLogDensity*(2*N:ℕ)/2-
    2*((∑ j ∈ range N, F j)/(N:ℝ)+repeatedPrimeLogDensity*N/2)=_
  push_cast
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp
  linear_combination he

/-- A sublinear sequence with a power bound on its dyadic difference has
the same power bound. The geometric constant is explicit. -/
private theorem sublinear_dyadic_inverse (f : ℕ → ℝ) {b K : ℝ} (hb : b<1) (hK : 0≤K)
    (hlim : Tendsto (fun n : ℕ => f n/(n:ℝ)) atTop (𝓝 0))
    (hrec : ∀ n : ℕ, 1 ≤ n → |f (2*n)-2*f n| ≤ K*((2*n:ℕ):ℝ)^b)
    {n : ℕ} (hn : 1 ≤ n) :
    |f n| ≤ K*(2:ℝ)^b/(2-(2:ℝ)^b)*(n:ℝ)^b := by
  let B := K*(2:ℝ)^b/(2-(2:ℝ)^b)
  have h2 : (2:ℝ)^b < 2 := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hb
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hK (by positivity)) (sub_pos.mpr h2).le
  have hid : B*(2-(2:ℝ)^b)=K*(2:ℝ)^b := div_mul_cancel₀ _ (sub_pos.mpr h2).ne'
  have hstep (m : ℕ) (hm : 1 ≤ m) :
      2*(|f m|-B*(m:ℝ)^b) ≤ |f (2*m)|-B*((2*m:ℕ):ℝ)^b := by
    have he := abs_sub (f (2*m)) (f (2*m)-2*f m)
    rw [sub_sub_cancel,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at he
    have h := hrec m hm
    push_cast at h ⊢
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg _)] at h ⊢
    have hh := congrArg (· * (m:ℝ)^b) hid
    linarith only [h,he,hh]
  have hiter (k : ℕ) : (2:ℝ)^k*(|f n|-B*(n:ℝ)^b) ≤
      |f (2^k*n)|-B*((2^k*n:ℕ):ℝ)^b := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := hstep (2^k*n) (Nat.mul_pos (by positivity) hn)
      rw [pow_succ',mul_assoc,pow_succ',mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℝ)≤2)).trans hh
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht : Tendsto (fun k : ℕ => (2:ℕ)^k*n) atTop atTop := by
    apply tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_right (2^k) hn)
    exact tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have hlim' : Tendsto (fun k : ℕ => |f (2^k*n)|/(2:ℝ)^k) atTop (𝓝 0) := by
    have h := ((hlim.comp ht).abs.mul_const (n:ℝ))
    simp only [abs_zero,zero_mul] at h
    apply h.congr (fun k => ?_)
    change |f (2^k*n)/((2^k*n:ℕ):ℝ)|*n=_
    rw [abs_div,abs_of_nonneg (Nat.cast_nonneg _)]
    push_cast; field_simp
  have hend : |f n|-B*(n:ℝ)^b ≤ 0 := by
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlim'
    intro k
    apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^k)).mpr
    rw [mul_comm]
    exact (hiter k).trans (sub_le_self _ (mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  exact sub_nonpos.mp hend

/-- The raw triangular mode before the dyadic difference. -/
def primeMomentZetaMode (ρ s : ℂ) (N : ℕ) : ℝ :=
  (((N:ℂ)^s*riemannZeta s/(s+1))/ρ).re

private theorem mode_difference (ρ s : ℂ) (N : ℕ) :
    primeMomentZetaMode ρ s (2*N)-2*primeMomentZetaMode ρ s N = oddQuotientEtaMode ρ s (2*N) := by
  unfold primeMomentZetaMode oddQuotientEtaMode
  rw [← Complex.re_ofReal_mul,← Complex.sub_re]
  apply congrArg re
  have he : ((2*N:ℕ):ℂ)^s=(2:ℂ)^s*(N:ℂ)^s := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,ofReal_mul,ofReal_ofNat,ofReal_natCast] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg N) s
  have h₂ : (2:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  rw [he,alternatingDivisorFactor,Complex.cpow_neg]
  push_cast
  field_simp
  <;> ring

private theorem mode_abs (ρ : ℂ) {s : ℂ} (hs : s.re ≤ 1/2) {N : ℕ} (hN : 1 ≤ N) :
    |primeMomentZetaMode ρ s N| ≤ ‖riemannZeta s/(s+1)/ρ‖*Real.sqrt N := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hpos := zero_lt_one.trans_le hn
  unfold primeMomentZetaMode
  apply (Complex.abs_re_le_norm _).trans
  rw [show (N:ℂ)^s*riemannZeta s/(s+1)/ρ = (N:ℂ)^s*(riemannZeta s/(s+1)/ρ) by ring,
    norm_mul,mul_comm,← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hpos,Real.sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn hs) (norm_nonneg _)

/-- Subtracting the real square and cube main terms from the centered first mean. -/
def primeMomentRealRemainder (N : ℕ) :=
  triangularDistinctPrimeLogMoment N + primeMomentZetaMode 1 (1/2) N + primeMomentZetaMode 1 (1/3) N

private theorem real_remainder_sqrt :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → |primeMomentRealRemainder N| ≤ K*Real.sqrt N := by
  let L := 15*(Real.log 4+4)
  let A := ‖riemannZeta (1/2)/(1/2+1)/1‖
  let B := ‖riemannZeta (1/3)/(1/3+1)/1‖
  let c := |repeatedPrimeLogDensity|/2
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  refine ⟨c+L+A+B,by dsimp only [L,A,B]; positivity,fun N hn => ?_⟩
  have h₁ : (1:ℝ) ≤ N := by exact_mod_cast hn
  have hroot : 1 ≤ Real.sqrt (N:ℝ) := by simpa using Real.sqrt_le_sqrt h₁
  have hh := mul_le_mul_of_nonneg_left hroot hc
  have h0 := triangularDistinctPrimeLogMoment_abs hn
  have h2 := mode_abs 1 (s := 1/2) (by norm_num) hn
  have h3 := mode_abs 1 (s := 1/3) (by norm_num) hn
  unfold primeMomentRealRemainder
  apply (abs_add_le _ _).trans
  apply (add_le_add (abs_add_le _ _) le_rfl).trans
  change _ ≤ (c+15*(Real.log 4+4)+_+_)*_
  dsimp only [L,c,A,B] at *
  linarith only [hh,h0,h2,h3]

private theorem sublinear_of_sqrt {f : ℕ → ℝ} {K : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → |f n| ≤ K*Real.sqrt n) :
    Tendsto (fun n : ℕ => f n/(n:ℝ)) atTop (𝓝 0) := by
  have he := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul K
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (g := fun n : ℕ => K*(n:ℝ)^(-(1/2:ℝ))) _
    (by simpa only [mul_zero,Function.comp_apply] using he)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos : (0:ℝ)<n := by exact_mod_cast hn
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hpos,show -(1/2:ℝ)=1/2-1 by norm_num,
    Real.rpow_sub_one hpos.ne',← mul_div_assoc,← Real.sqrt_eq_rpow]
  exact div_le_div_of_nonneg_right (h n hn) hpos.le

private theorem dyadic_real_remainder {b : ℝ} (hb : 1/4<b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |primeMomentRealRemainder (2*N)-2*primeMomentRealRemainder N+
        oddQuotientPowerTotal (2*N)/(2*(N:ℝ))| ≤ C*((2*N:ℕ):ℝ)^b := by
  obtain ⟨C,hC,h⟩ := oddQuotientPowerTotal_lattice_modes
  let δ := (b-1/4)/2
  have hd : 0<δ := by dsimp only [δ]; linarith only [hb]
  refine ⟨C*(1+1/δ)^2,by positivity,fun N hn => ?_⟩
  have h2N : 1 ≤ 2*N := by omega
  have hx : (1:ℝ) ≤ (2*N:ℕ) := by exact_mod_cast h2N
  have hpos := zero_lt_one.trans_le hx
  have hlog := CarlsonFloor.one_add_log_sq_le hd hx
  have hl := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hpos.le (1/4))
  have hp : ((2*N:ℕ):ℝ)^(1/4:ℝ)*((2*N:ℕ):ℝ)^(2*δ)=((2*N:ℕ):ℝ)^b := by
    rw [← Real.rpow_add hpos]; dsimp only [δ]; congr 1; ring
  have he := h (2*N) h2N
  let W := (∑ d ∈ Icc 1 (2*N), primePowerPart d*
    discreteQuotientMean (fun n => ((n%2:ℕ):ℝ)) d (2*N))/(2*(N:ℝ))
  have hdiff : primeMomentRealRemainder (2*N)-2*primeMomentRealRemainder N =
      -W+oddQuotientEtaMode 1 (1/2) (2*N)+oddQuotientEtaMode 1 (1/3) (2*N) := by
    have hraw := triangularDistinctPrimeLogMoment_dyadic hn
    unfold primeMomentRealRemainder
    dsimp only [W]
    linear_combination hraw+mode_difference 1 (1/2) N+mode_difference 1 (1/3) N
  rw [hdiff]
  have hc := mul_le_mul_of_nonneg_left hl hC
  have hz : C*(((2*N:ℕ):ℝ)^(1/4:ℝ)*((1+1/δ)^2*((2*N:ℕ):ℝ)^(2*δ))) =
      C*(1+1/δ)^2*((2*N:ℕ):ℝ)^b := by rw [← hp]; ring
  apply le_trans _ (hc.trans_eq hz)
  rw [← abs_neg]
  convert he using 2
  dsimp only [W]; push_cast; ring

/-- Under RH only the two real prime-power modes remain above the quarter exponent. -/
theorem primeMomentRealRemainder_quarter_of_rh (hRH : RiemannHypothesis) {b : ℝ}
    (hb : 1/4 < b) (hb' : b < 1/2) :
    ∃ K : ℝ, 0≤K ∧ ∀ N : ℕ, 1≤N → |primeMomentRealRemainder N| ≤ K*(N:ℝ)^b := by
  obtain ⟨C,hC,h⟩ := dyadic_real_remainder hb
  obtain ⟨D,hD,hM⟩ := oddQuotientPowerTotal_quarter_of_rh hRH hb hb'
  obtain ⟨L,_,hL⟩ := real_remainder_sqrt
  have hs := sublinear_of_sqrt hL
  have hrec (N : ℕ) (hN : 1 ≤ N) : |primeMomentRealRemainder (2*N)-2*primeMomentRealRemainder N| ≤
      (C+D)*((2*N:ℕ):ℝ)^b := by
    have hn : 1≤2*N := by omega
    have hp : (0:ℝ)<(2*N:ℕ) := by exact_mod_cast hn
    have he := hM (2*N) hn
    rw [Real.rpow_add_one hp.ne'] at he
    have hdiv : |oddQuotientPowerTotal (2*N)/(2*(N:ℝ))| ≤ D*((2*N:ℕ):ℝ)^b := by
      rw [show 2*(N:ℝ)=((2*N:ℕ):ℝ) by push_cast; rfl,abs_div,abs_of_pos hp,div_le_iff₀ hp]
      exact he.trans_eq (by ring)
    obtain ⟨ll,lu⟩ := abs_le.mp (h N hN)
    obtain ⟨ml,mu⟩ := abs_le.mp hdiv
    rw [abs_le]
    constructor <;> linarith only [ll,lu,ml,mu]
  have hbl : b<1 := by linarith only [hb']
  have htwo : (2:ℝ)^b < 2 := by simpa only [Real.rpow_one] using
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hbl
  exact ⟨_,div_nonneg (mul_nonneg (add_nonneg hC hD) (by positivity)) (sub_pos.mpr htwo).le,
    fun _ hn => sublinear_dyadic_inverse _ hbl (add_nonneg hC hD) hs hrec hn⟩

private theorem odd_total_succ (n : ℕ) :
    oddQuotientPowerTotal (n+1)=oddQuotientPowerTotal n+oddQuotientPowerCount n := by
  let c : ArithmeticFunction ℝ := properPowerLatticeWeight*alternatingDivisorCoeff
  have he (N : ℕ) : oddQuotientPowerTotal N=∑ k ∈ range N, ∑ j ∈ Icc 1 k, c j :=
    (oddQuotientPowerTotal_eq_triangular N).trans (triangularPrimeProfile_sample c N)
  rw [he (n+1),he n,sum_range_succ]
  congr 1
  rw [oddQuotientPowerCount,show (∑ j ∈ Icc 1 n, c j)=_ from
    _root_.RHTower.sum_Icc_mul_apply properPowerLatticeWeight alternatingDivisorCoeff n]
  simp only [prefix_alternatingDivisorCoeff]

private theorem odd_total_of_even_bound {b K : ℝ} (hb : 0<b) (hK : 0 ≤ K)
    (h : ∀ n : ℕ, 1 ≤ n → |oddQuotientPowerTotal (2*n)| ≤ K*((2*n:ℕ):ℝ)^(b+1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1≤n → |oddQuotientPowerTotal n| ≤ C*(n:ℝ)^(b+1) := by
  obtain ⟨J,hJ,hS⟩ := oddQuotientPowerCount_eight_seventeenths
  refine ⟨K*(2:ℝ)^(b+1)+J,by positivity,fun n hn => ?_⟩
  let j := (n+1)/2
  have hj : 1 ≤ j := by dsimp only [j]; omega
  have hm : 2*j=n ∨ 2*j=n+1 := by dsimp only [j]; omega
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hp : 0 ≤ (n:ℝ)^(b+1) := by positivity
  have hS' := (hS n hn).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hn' (by linarith only [hb] : (8/17:ℝ) ≤ b+1)) hJ)
  have hs : ((2*j:ℕ):ℝ)^(b+1) ≤ 2^(b+1)*(n:ℝ)^(b+1) := by
    rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg n)]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show 2*j ≤ 2*n by omega)) (by linarith only [hb])
  have hm' := (h j hj).trans (mul_le_mul_of_nonneg_left hs hK)
  rcases hm with he | he
  · rw [he] at hm'
    linarith only [hm',mul_nonneg hJ hp]
  · rw [he,odd_total_succ] at hm'
    have hh := abs_sub (oddQuotientPowerTotal n+oddQuotientPowerCount n) (oddQuotientPowerCount n)
    rw [add_sub_cancel_right] at hh
    linarith only [hh,hm',hS']

/-- The ordinary-prime triangular mean determines RH after removing its
explicit real square and cube terms, already at integer cutoffs. -/
theorem riemannHypothesis_iff_triangularDistinctPrimeLogMoment :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/4 < b → b < 1/2 →
      ∃ K : ℝ, 0≤K ∧ ∀ N : ℕ, 1≤N → |primeMomentRealRemainder N| ≤ K*(N:ℝ)^b := by
  constructor
  · exact fun h _ hb hb' => primeMomentRealRemainder_quarter_of_rh h hb hb'
  · intro h
    apply riemannHypothesis_iff_oddQuotientPowerTotal_quarter.mpr
    intro b hb hb'
    obtain ⟨C,hC,hc⟩ := dyadic_real_remainder hb
    obtain ⟨K,hK,hk⟩ := h b hb hb'
    have hb0 : 0<b := by linarith only [hb]
    apply odd_total_of_even_bound hb0 (K := C+3*K) (by positivity)
    intro n hn
    have h2n : 1≤2*n := by omega
    have hp : (0:ℝ)<(2*n:ℕ) := by exact_mod_cast h2n
    have he := hc n hn
    have hlow := (hk n hn).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (Nat.cast_nonneg n) (by exact_mod_cast (show n ≤ 2*n by omega)) hb0.le) hK)
    obtain ⟨hl,hu⟩ := abs_le.mp he
    obtain ⟨ll,lu⟩ := abs_le.mp hlow
    obtain ⟨rl,ru⟩ := abs_le.mp (hk (2*n) h2n)
    have hm : |oddQuotientPowerTotal (2*n)/(2*(n:ℝ))| ≤ (C+3*K)*((2*n:ℕ):ℝ)^b := by
      rw [abs_le]
      constructor <;> linarith only [hl,hu,ll,lu,rl,ru]
    have hd : 2*(n:ℝ)=((2*n:ℕ):ℝ) := by push_cast; rfl
    rw [hd,abs_div,abs_of_pos hp,div_le_iff₀ hp] at hm
    rw [Real.rpow_add_one hp.ne']
    exact hm.trans_eq (by ring)

/-- Both nonreal modes of the raw first mean, after its two real terms
have been subtracted. The square mode has coefficient
2m ζ(ρ/2)/(ρ(1+ρ/2)), and the cube mode has the same formula at ρ/3. -/
theorem triangularDistinctPrimeLogMoment_singleQuartet {ρ : ℂ} (hq : ExclusionOfTheCriticalState.HasSingleOffLineQuartet ρ)
    {b : ℝ} (hb : 1/4 < b) (hb' : b < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      |primeMomentRealRemainder n - 2*(ExclusionOfTheCriticalState.quartetCopyMult ρ:ℝ)*
        (primeMomentZetaMode ρ (ρ/2) n+primeMomentZetaMode ρ (ρ/3) n)| ≤ K*(n:ℝ)^b := by
  let m := 2*(ExclusionOfTheCriticalState.quartetCopyMult ρ:ℝ)
  let f (n : ℕ) := primeMomentRealRemainder n - m*
    (primeMomentZetaMode ρ (ρ/2) n+primeMomentZetaMode ρ (ρ/3) n)
  have hm : 0 ≤ m := by dsimp only [m]; positivity
  have hr₂ : (ρ/2).re ≤ 1/2 := by rw [Complex.div_ofNat_re]; linarith only [hq.re_lt_one]
  have hr₃ : (ρ/3).re ≤ 1/2 := by rw [Complex.div_ofNat_re]; linarith only [hq.re_lt_one]
  obtain ⟨L,hL,hR⟩ := real_remainder_sqrt
  have hs : Tendsto (fun n : ℕ => f n/(n:ℝ)) atTop (𝓝 0) := by
    apply sublinear_of_sqrt (K := L+m*(‖riemannZeta (ρ/2)/(ρ/2+1)/ρ‖+‖riemannZeta (ρ/3)/(ρ/3+1)/ρ‖))
    intro n hn
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg hm]
    have hW := (abs_add_le _ _).trans (add_le_add (mode_abs ρ hr₂ hn) (mode_abs ρ hr₃ hn))
    have hh := add_le_add (hR n hn) (mul_le_mul_of_nonneg_left hW hm)
    exact hh.trans_eq (by ring)
  obtain ⟨C,hC,hc⟩ := dyadic_real_remainder hb
  obtain ⟨D,hD,hd⟩ := oddQuotientPowerTotal_singleQuartet_modes hq
  let δ := (b-1/4)/2
  have hδ : 0<δ := by dsimp only [δ]; linarith only [hb]
  let B := C+D*(1+1/δ)^2
  have hB : 0≤B := by dsimp only [B]; positivity
  have hrec (n : ℕ) (hn : 1≤n) : |f (2*n)-2*f n| ≤ B*((2*n:ℕ):ℝ)^b := by
    have h2n : 1≤2*n := by omega
    have hx : (1:ℝ)≤(2*n:ℕ) := by exact_mod_cast h2n
    have hxpos := zero_lt_one.trans_le hx
    have hlog := CarlsonFloor.one_add_log_sq_le hδ hx
    have hh := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hxpos.le (1/4))
    have he : ((2*n:ℕ):ℝ)^(1/4:ℝ)*((1+1/δ)^2*((2*n:ℕ):ℝ)^(2*δ)) =
        (1+1/δ)^2*((2*n:ℕ):ℝ)^b := by
      rw [mul_left_comm,← Real.rpow_add hxpos,show 1/4+2*δ=b by dsimp only [δ]; ring]
    have hmode := (hd (2*n) h2n).trans (mul_le_mul_of_nonneg_left (hh.trans_eq he) hD)
    have hbase := hc n hn
    have hform : f (2*n)-2*f n = (primeMomentRealRemainder (2*n)-2*primeMomentRealRemainder n+
        oddQuotientPowerTotal (2*n)/(2*(n:ℝ)))-(oddQuotientPowerTotal (2*n)/(2*(n:ℝ))+
        m*(oddQuotientEtaMode ρ (ρ/2) (2*n)+oddQuotientEtaMode ρ (ρ/3) (2*n))) := by
      dsimp only [f]
      rw [← mode_difference,← mode_difference]; ring
    rw [hform]
    apply (abs_sub _ _).trans
    push_cast at hmode hbase ⊢
    exact (add_le_add hbase hmode).trans_eq (by dsimp only [B]; ring)
  have htwo : (2:ℝ)^b < 2 := by simpa only [Real.rpow_one] using
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hb'
  exact ⟨_,div_nonneg (mul_nonneg hB (by positivity)) (sub_pos.mpr htwo).le,
    fun _ hn => sublinear_dyadic_inverse f hb' hB hs hrec hn⟩

end GaloisForLFunctions.ExceptionalLayerTheory
