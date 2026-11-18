import GaloisForLFunctions.ExceptionalLayerTheory.TheFirstPrimeDivisorMomentAtHalfARightZero
import GaloisForLFunctions.ExceptionalLayerTheory.ThreeProperPrimePowerCountsRecoverThePrimeError
import GaloisForLFunctions.ExceptionalLayerTheory.AdjacentDenominatorsInDiscreteQuotientMeans
import GaloisForLFunctions.ExceptionalLayerTheory.TheAlternatingDivisorCountHasSquareRootError
import GaloisForLFunctions.RHTower.AdjacentDilationZetaBase
import GaloisForLFunctions.RHTower.WeilPositivityPrimePowersForced
import GaloisForLFunctions.RHTower.MobiusHilbertLogarithmicMertensBound
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.WherePrecisionIsLost

/-!
# A finite mean of proper prime powers and two unrestricted power counts

The proper prime powers carry the logarithm of their underlying prime.
Each positive square and cube subtracts one, including both contributions
at a sixth power. The dyadic difference of the multiple counts selects
the odd floor quotients. Their first mean has the same upper power bounds
as the centered coefficient prefix at each positive exponent below one.
-/

noncomputable section
open Finset ArithmeticFunction
open _root_.RHTower _root_.RHTower.AdjacentDilation
namespace GaloisForLFunctions.ExceptionalLayerTheory

private def powerAtom (r : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => (perfectPowerArith r d).re,by simp⟩

private theorem root_cut {r : ℕ} (hr : 0 < r) (a N : ℕ) :
    a^r ≤ N ↔ a ≤ ⌊(N:ℝ)^((r:ℝ)⁻¹)⌋₊ := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast hr
  rw [Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  have he : ((N:ℝ)^((r:ℝ)⁻¹))^(r:ℝ)=N := by
    rw [← Real.rpow_mul (Nat.cast_nonneg N),inv_mul_cancel₀ hr0.ne',Real.rpow_one]
  rw [← Real.rpow_le_rpow_iff (Nat.cast_nonneg a) (Real.rpow_nonneg (Nat.cast_nonneg N) _) hr0,
    he,Real.rpow_natCast]
  exact_mod_cast Iff.rfl

private theorem powerAtom_sum {r : ℕ} (hr : 0<r) (N : ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, powerAtom r n * F n)=∑ a ∈ Icc 1 ⌊(N:ℝ)^((r:ℝ)⁻¹)⌋₊, F (a^r) := by
  classical
  let M := ⌊(N:ℝ)^((r:ℝ)⁻¹)⌋₊
  let T := (Icc 1 N).filter (fun n => ∃ a : ℕ, n=a^r)
  have he : T=(Icc 1 M).image (fun a : ℕ => a^r) := by
    ext n
    constructor
    · rintro hn
      obtain ⟨hn,⟨a,rfl⟩⟩ := mem_filter.mp hn
      obtain ⟨hn,hN⟩ := mem_Icc.mp hn
      have ha : a≠0 := by rintro rfl; simpa [zero_pow hr.ne'] using hn
      exact mem_image.mpr ⟨a,mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr ha,(root_cut hr a N).mp hN⟩,rfl⟩
    · intro hn
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hn
      obtain ⟨ha,hM⟩ := mem_Icc.mp ha
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨pow_pos ha _,(root_cut hr a N).mpr hM⟩,a,rfl⟩
  calc
    _ = ∑ d ∈ T, F d := by
      rw [show T=(Icc 1 N).filter _ from rfl,sum_filter]
      refine sum_congr rfl fun d hd => ?_
      change (perfectPowerArith r d).re*F d=_
      rw [perfectPowerArith_apply (Nat.ne_of_gt (mem_Icc.mp hd).1)]
      split <;> simp_all only [if_true,if_false,Complex.one_re,Complex.zero_re,one_mul,zero_mul]
    _ = _ := by rw [he]; exact sum_image (fun _ _ _ _ h => Nat.pow_left_injective hr.ne' h)

private theorem powerAtom_prefix {r : ℕ} (hr : 0<r) (N : ℕ) :
    (∑ n ∈ Icc 1 N, powerAtom r n)=(⌊(N:ℝ)^((r:ℝ)⁻¹)⌋₊ : ℝ) := by
  simpa using powerAtom_sum hr N (fun _ => 1)

/-- Signed weight of the proper prime powers relative to the positive squares and cubes. -/
def properPowerLatticeWeight : ArithmeticFunction ℝ :=
  (⟨primePowerPart,by simp [primePowerPart]⟩ : ArithmeticFunction ℝ)-powerAtom 2-powerAtom 3

/-- The integer lattice changes the smooth square and cube main terms by less than two. -/
theorem properPowerLatticeWeight_prefix (N : ℕ) :
    0 ≤ (∑ d ∈ Icc 1 N, properPowerLatticeWeight d)-properPowerDiscrepancy N ∧
    (∑ d ∈ Icc 1 N, properPowerLatticeWeight d)-properPowerDiscrepancy N ≤ 2 := by
  have hW : (∑ d ∈ Icc 1 N, primePowerPart d)=Chebyshev.psi N-Chebyshev.theta N := by
    have hi : Icc 1 N=Ioc 0 N := by ext n; simp only [mem_Icc,mem_Ioc]; omega
    rw [hi,Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,sum_filter]
    exact sum_congr rfl fun d _ => by by_cases h : d.Prime <;> simp [primePowerPart,h]
  simp only [properPowerLatticeWeight,ArithmeticFunction.sub_apply,ArithmeticFunction.coe_mk,
    sum_sub_distrib,powerAtom_prefix (by norm_num : 0<2),powerAtom_prefix (by norm_num : 0<3),
    hW,properPowerDiscrepancy,Nat.cast_ofNat,← one_div]
  have h₂ := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (1/2:ℝ))
  have h₃ := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (1/3:ℝ))
  have hg := Nat.lt_floor_add_one ((N:ℝ)^(1/2:ℝ))
  have hh := Nat.lt_floor_add_one ((N:ℝ)^(1/3:ℝ))
  constructor <;> linarith only [h₂,h₃,hg,hh]

/-- Total over cutoffs below N of the odd-quotient weighted prime-power discrepancy. -/
def oddQuotientPowerTotal (N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, properPowerLatticeWeight d * discreteQuotientMean (fun n => ((n%2:ℕ):ℝ)) d N

/-- Number of base cutoffs below N at which d has an odd quotient. -/
def oddQuotientMultiplicity (N d : ℕ) : ℝ := discreteQuotientMean (fun n => ((n%2:ℕ):ℝ)) d N

private theorem weighted_floor_factorial {j N : ℕ} (hj : j≤N) :
    (∑ d ∈ Icc 1 N, vonMangoldt d*((j/d:ℕ):ℝ))=Real.log (j.factorial:ℕ) := by
  have hsub := Icc_subset_Icc_right (a := 1) hj
  have he : (∑ d ∈ Icc 1 j, vonMangoldt d*((j/d:ℕ):ℝ))=
      ∑ d ∈ Icc 1 N, vonMangoldt d*((j/d:ℕ):ℝ) := by
    apply sum_subset hsub
    intro d hd hd'
    have hlt : j<d := lt_of_not_ge fun h => hd' (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,h⟩)
    simp [Nat.div_eq_of_lt hlt]
  have hi : Icc 1 j=Ioc 0 j := by ext n; simp only [mem_Icc,mem_Ioc]; omega
  rw [← he,hi]
  exact ArithmeticOfSquareRootPrecision.chebyshevTransform_vonMangoldt j

private theorem odd_log_factorial (N : ℕ) :
    (∑ d ∈ Icc 1 N, vonMangoldt d*oddQuotientMultiplicity N d)=
      ∑ j ∈ range N, (Real.log (j.factorial:ℕ)-2*Real.log ((j/2).factorial:ℕ)) := by
  simp only [oddQuotientMultiplicity,discreteQuotientMean,mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have hdiv (d : ℕ) : (j/d)/2=(j/2)/d := by
    rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,mul_comm d 2]
  have hval (d : ℕ) : ((j/d%2:ℕ):ℝ)=((j/d:ℕ):ℝ)-2*(((j/2)/d:ℕ):ℝ) := by
    have e : ((j/d%2:ℕ):ℝ)+2*(((j/d)/2:ℕ):ℝ)=((j/d:ℕ):ℝ) := by exact_mod_cast Nat.mod_add_div (j/d) 2
    rw [hdiv] at e
    linarith only [e]
  rw [← weighted_floor_factorial (mem_range.mp hj).le,← weighted_floor_factorial ((Nat.div_le_self j 2).trans (mem_range.mp hj).le),
    mul_sum,← sum_sub_distrib]
  exact sum_congr rfl fun d _ => by rw [hval]; ring

/-- One ordinary-prime sum, two unrestricted lattice counts and elementary factorials
give the entire mean at every integer cutoff. -/
theorem oddQuotientPowerTotal_finite_formula (N : ℕ) :
    oddQuotientPowerTotal N=
      (∑ j ∈ range N, (Real.log (j.factorial:ℕ)-2*Real.log ((j/2).factorial:ℕ)))-
      (∑ p ∈ Nat.primesLE N, Real.log p*oddQuotientMultiplicity N p)-
      (∑ a ∈ Icc 1 ⌊(N:ℝ)^(1/2:ℝ)⌋₊, oddQuotientMultiplicity N (a^2))-
      (∑ a ∈ Icc 1 ⌊(N:ℝ)^(1/3:ℝ)⌋₊, oddQuotientMultiplicity N (a^3)) := by
  have hsplit (d : ℕ) : primePowerPart d=vonMangoldt d-(if d.Prime then Real.log d else 0) := by
    by_cases hd : d.Prime <;> simp [primePowerPart,hd,vonMangoldt_apply_prime]
  have hp (r : ℕ) (hr : 0<r) := powerAtom_sum hr N (oddQuotientMultiplicity N)
  change (∑ d ∈ Icc 1 N, properPowerLatticeWeight d*oddQuotientMultiplicity N d)=_
  simp only [properPowerLatticeWeight,ArithmeticFunction.sub_apply,ArithmeticFunction.coe_mk,hsplit,
    sub_mul,sum_sub_distrib,odd_log_factorial,hp 2 (by decide),hp 3 (by decide),Nat.cast_ofNat,← one_div]
  rw [Nat.primesLE_eq_filter_Icc_one,sum_filter]
  simp only [ite_mul,zero_mul]

/-- The total is the integer triangular mean of a single Dirichlet convolution. -/
theorem oddQuotientPowerTotal_eq_triangular (N : ℕ) :
    oddQuotientPowerTotal N=N*triangularPrimeProfile (properPowerLatticeWeight*alternatingDivisorCoeff)
      (N:ℝ)⁻¹ := by
  rw [triangularPrimeProfile_sample,oddQuotientPowerTotal]
  simp_rw [RHTower.sum_Icc_mul_apply,prefix_alternatingDivisorCoeff,discreteQuotientMean,mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun n hn => (sum_subset (Icc_subset_Icc_right (mem_range.mp hn).le) ?_).symm
  intro d hd hd'
  have hlt : n<d := lt_of_not_ge fun h => hd' (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,h⟩)
  simp [Nat.div_eq_of_lt hlt]

/-- Discrete Abel summation transfers the prefix bound with the same
exponent. Integration of the power costs the explicit factor 1/b. -/
theorem oddQuotientPowerTotal_bound {b K : ℝ} (hb : 0 < b) (hb1 : b < 1) (hK : 0≤K)
    (h : ∀ x : ℝ, 1≤x → |properPowerDiscrepancy x|≤K*x^b) {N : ℕ} (hn : 1≤N) :
    |oddQuotientPowerTotal N| ≤ ((K+2)/b)*(N:ℝ)^(b+1) := by
  have hdisp (n : ℕ) (hn' : 1≤n) :
      |∑ d ∈ Icc 1 n, properPowerLatticeWeight d| ≤ (K+2)*(n:ℝ)^b := by
    have h1 : (1:ℝ)≤n := by exact_mod_cast hn'
    have ht := h n h1
    have hfl := properPowerLatticeWeight_prefix n
    have hp := Real.one_le_rpow h1 hb.le
    rw [abs_le] at ht ⊢
    constructor <;> linarith only [hfl.1,hfl.2,ht.1,ht.2,hp]
  have hvar := abs_discreteQuotientMean_weighted properPowerLatticeWeight (fun n => ((n%2:ℕ):ℝ))
    (by norm_num) (fun n => ⟨Nat.cast_nonneg _,by exact_mod_cast (show n%2≤1 by omega)⟩) N
  apply hvar.trans
  have hterm (n : ℕ) (hm : n∈Icc 1 N) : |∑ d ∈ Icc 1 n, properPowerLatticeWeight d|/((n:ℝ)+1) ≤
      (K+2)*(n:ℝ)^(b-1) := by
    have hpos : (0:ℝ)<n := by exact_mod_cast (mem_Icc.mp hm).1
    rw [Real.rpow_sub_one hpos.ne',← mul_div_assoc]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) hpos (by linarith only : (n:ℝ)≤n+1)).trans
      (div_le_div_of_nonneg_right (hdisp n (mem_Icc.mp hm).1) hpos.le)
  have H := sum_le_sum hterm
  rw [← mul_sum] at H
  have hsum : (∑ n ∈ Icc 1 N, (n:ℝ)^(b-1)) ≤ (N:ℝ)^b/b := by
    rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
    have hr := _root_.RHTower.sum_range_rpow_neg_le (1-b) (by linarith only [hb1]) (by linarith only [hb]) N
    simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,add_comm (1:ℝ),
      show -(1-b)=b-1 by ring,show 1-(1-b)=b by ring] using hr
  have hx : (0:ℝ)<N := by exact_mod_cast hn
  rw [Real.rpow_add_one hx.ne']
  exact (mul_le_mul_of_nonneg_left (H.trans (mul_le_mul_of_nonneg_left hsum (by positivity))) hx.le).trans_eq (by ring)

/-- Independent power bound for the finite prime-power and lattice count. -/
theorem oddQuotientPowerTotal_sub_seven_sixteenths {b : ℝ} (hb : 20999/48000 < b) (hb1 : b < 1) :
    ∃ K : ℝ, 0≤K ∧ ∀ N : ℕ, 1≤N → |oddQuotientPowerTotal N| ≤ K*(N:ℝ)^(b+1) := by
  obtain ⟨K,hK,h⟩ := properPowerDiscrepancy_from_zero_free_strip hb
  have hp : 0 < b := by linarith only [hb]
  exact ⟨(K+2)/b,by positivity,fun _ hn => oddQuotientPowerTotal_bound hp hb1 hK h hn⟩

/-- Under RH the normalized finite count takes every exponent above one quarter. -/
theorem oddQuotientPowerTotal_quarter_of_rh (hRH : RiemannHypothesis) {b : ℝ} (hb : 1/4 < b) (hb' : b < 1/2) :
    ∃ K : ℝ, 0≤K ∧ ∀ N : ℕ, 1≤N → |oddQuotientPowerTotal N| ≤ K*(N:ℝ)^(b+1) := by
  obtain ⟨K,hK,h⟩ := riemannHypothesis_iff_properPowerDiscrepancy_quarter.mp hRH b hb hb'
  have hp : 0 < b := by linarith only [hb]
  exact ⟨(K+2)/b,by positivity,fun _ hn => oddQuotientPowerTotal_bound hp (by linarith only [hb']) hK h hn⟩

private abbrev cxCoeff (f : ArithmeticFunction ℝ) := fun n : ℕ => (f n : ℂ)

private theorem proper_euler {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (primePowerPart n:ℂ)) s ∧
      LSeries (fun n : ℕ => (primePowerPart n:ℂ)) s=xiPrimeLogHigherValuation s := by
  classical
  let P : Set ℕ := {n | n.Prime}
  let v := LSeries.term (fun n => (vonMangoldt n:ℂ)) s
  have hv : Summable v := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have he : LSeries.term (fun n => (primePowerPart n:ℂ)) s=Pᶜ.indicator v := by
    funext n
    by_cases h : n.Prime
    · have hnot : n∉Pᶜ := fun k => k h
      simp [Set.indicator_of_notMem hnot,LSeries.term,primePowerPart,h]
    · have hmem : n∈Pᶜ := h
      simp only [Set.indicator_of_mem hmem,v,LSeries.term,primePowerPart,if_neg h]
  refine ⟨by rw [LSeriesSummable,he]; exact hv.indicator _,?_⟩
  rw [LSeries,he,← _root_.tsum_subtype]
  have hp : (∑' n : P, v n)=xiPrimeLogDirichlet s :=
    tsum_congr (vonMangoldtLSeries_prime_term_eq_xiPrimeLogDirichlet_term s)
  have htot := hv.tsum_subtype_add_tsum_subtype_compl P
  rw [hp,show (∑' n, v n)=xiPrimeLogDirichlet s+xiPrimeLogHigherValuation s from
    tsum_vonMangoldtLSeriesTerm_eq_primeLog_add_higherValuation hs] at htot
  exact add_left_cancel htot

private theorem powerAtom_complex (r : ℕ) : cxCoeff (powerAtom r)=fun n => perfectPowerArith r n := by
  classical
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cxCoeff]
  change ((perfectPowerArith r n).re:ℂ)=_
  rw [perfectPowerArith_apply hn.ne']
  split <;> simp

/-- The regular part to subtract from the first-prime moment before the dyadic difference. -/
def properPowerLatticeMain (s : ℂ) : ℂ :=
  -deriv riemannZeta s-riemannZeta s*(riemannZeta (2*s)+riemannZeta (3*s))

open scoped LSeries.notation in
/-- The genuine triangular count has the dyadic zeta factor multiplying the
proper-prime-power series minus the two unrestricted-power series. -/
theorem oddQuotientPowerTotal_series {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (cxCoeff (properPowerLatticeWeight*alternatingDivisorCoeff)) s ∧
      LSeries (cxCoeff (properPowerLatticeWeight*alternatingDivisorCoeff)) s=
        alternatingDivisorFactor s*(properPowerLatticeMain s-firstPrimeDivisorMoment s) := by
  have h₂ : 1<((2:ℂ)*s).re := by simp; linarith only [hs]
  have h₃ : 1<((3:ℂ)*s).re := by simp; linarith only [hs]
  have h2 := lseriesSummable_perfectPowerArith (s := s) (k := 2) (by decide) (by simpa using h₂)
  have h3 := lseriesSummable_perfectPowerArith (s := s) (k := 3) (by decide) (by simpa using h₃)
  obtain ⟨hw,hw'⟩ := proper_euler hs
  have he : cxCoeff properPowerLatticeWeight=(fun n : ℕ => (primePowerPart n:ℂ))-
      (fun n => perfectPowerArith 2 n)-(fun n => perfectPowerArith 3 n) := by
    rw [← powerAtom_complex 2,← powerAtom_complex 3]
    funext n
    simp [cxCoeff,properPowerLatticeWeight,Complex.ofReal_sub]
  have hsum : LSeriesSummable (cxCoeff properPowerLatticeWeight) s := by
    rw [he]; exact (hw.sub h2).sub h3
  have ha := (alternatingDivisor_series_on_euler hs).1
  have hm : cxCoeff (properPowerLatticeWeight*alternatingDivisorCoeff)=
      cxCoeff properPowerLatticeWeight ⍟ cxCoeff alternatingDivisorCoeff := by
    funext n; rw [LSeries.convolution_def]; exact coe_mul_apply _ _ _
  rw [hm]
  refine ⟨hsum.convolution ha.1,?_⟩
  rw [LSeries_convolution' hsum ha.1,ha.2,he,LSeries_sub (hw.sub h2) h3,LSeries_sub hw h2,hw',
    lseries_perfectPowerArith (s := s) (k := 2) (by decide) (by simpa using h₂),
    lseries_perfectPowerArith (s := s) (k := 3) (by decide) (by simpa using h₃),
    firstPrimeDivisorMoment_euler hs,properPowerLatticeMain]
  have hζ : riemannZeta s*(xiPrimeLogDirichlet s+xiPrimeLogHigherValuation s)= -deriv riemannZeta s := by
    rw [← infinitePrimeFlux_eq_primeLog_add_higherValuation hs,infinitePrimeFlux,logDeriv_apply]
    field_simp [riemannZeta_ne_zero_of_one_le_re hs.le]
  push_cast
  rw [← hζ]
  ring

#print axioms oddQuotientPowerTotal_finite_formula
#print axioms oddQuotientPowerTotal_series
#print axioms oddQuotientPowerTotal_sub_seven_sixteenths
#print axioms oddQuotientPowerTotal_quarter_of_rh
#print axioms oddQuotientPowerTotal_eq_triangular
#print axioms oddQuotientPowerTotal_bound
end GaloisForLFunctions.ExceptionalLayerTheory
