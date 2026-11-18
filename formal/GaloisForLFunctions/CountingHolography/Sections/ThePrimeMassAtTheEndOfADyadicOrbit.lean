import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic
import GaloisForLFunctions.CountingHolography.Sections.SquareGeneratorPrefix
import GaloisForLFunctions.HTGeometry.AlternatingHarmonicPair
import GaloisForLFunctions.CountingHolography.Sections.FinitePlaceCostOfTheStirlingRemainder
import GaloisForLFunctions.CountingHolography.Sections.TheLogarithmicMomentOfTheSquarePrimeProfile

/-! # The escaping prime mass on a dyadic orbit of square conductors

The logarithmic valuations are a difference of two positive prime profiles
at successive squares, up to a quadratically bounded absolute error.
In the dyadic sum with weights eight to the minus depth this error is
absolutely summable in both indices. The end profile has a nonzero
limiting mass although it vanishes eventually at every fixed prime.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology MeasureTheory ArithmeticCastelnuovoSeveri ArithmeticFunction
open ArithmeticWeightTheory _root_.RHTower _root_.RHTower.WeilDeletion BiScaleUncertainty.ChebyshevGauge

private def weight (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
private def S (n : ℕ) := ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1))
private def q (n : ℕ) := ordinaryPrimeGenerator (n • successorSquareTriple n)
private def price (n k : ℕ) := (deningerRatExp (q n) k:ℝ)*weight k

/-- Positive moving endpoint, with the logarithmic prime weight included. -/
def squarePrimeEndpoint (n k : ℕ) : ℝ :=
  (4*(n:ℝ)^2/Real.sqrt k)*splineAutoCorr (Real.log k-Real.log ((n:ℝ)^2))*weight k

private def err (n k : ℕ) := price n k-(squarePrimeEndpoint n k-squarePrimeEndpoint (2*n) k/8)

private theorem endpoint_zero {n k : ℕ} (hn : 0 < n) (hk : k ∉ S n) :
    price n k=0 ∧ squarePrimeEndpoint n k=0 ∧ squarePrimeEndpoint (2*n) k=0 := by
  by_cases hp : k.Prime
  · have hcut : 3*windowEnd ((2*n+1)^2+1) < k :=
      lt_of_not_ge fun h => hk (mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le,h⟩,hp⟩)
    have hkL : (windowEnd ((2*n+1)^2+1):ℝ) < k := by
      exact_mod_cast (by omega : windowEnd ((2*n+1)^2+1) < k)
    have hb := (successorSquareWindowScale_bounds n).2.2.trans_lt hkL
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
    have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr hp.pos
    have hhigh : 0 < ((2*n:ℕ):ℝ) := by positivity
    have hsq : (((2*n:ℕ):ℝ))^2 ≤ (((2*n+1:ℕ):ℝ))^2 :=
      pow_le_pow_left₀ hhigh.le (by exact_mod_cast Nat.le_succ (2*n)) 2
    have hlow : (n:ℝ)^2 ≤ (((2*n+1:ℕ):ℝ))^2 :=
      pow_le_pow_left₀ hn'.le (by exact_mod_cast (by omega : n ≤ 2*n+1)) 2
    have hz {x : ℝ} (hx : 0 < x) (h : x^2 ≤ (((2*n+1:ℕ):ℝ))^2) : splineAutoCorr (Real.log k-Real.log (x^2))=0 := by
      apply splineAutoCorr_zero_outside
      apply lt_of_lt_of_le _ (le_abs_self _)
      rw [← Real.log_div hk'.ne' (sq_pos_of_pos hx).ne',Real.lt_log_iff_exp_lt (div_pos hk' (sq_pos_of_pos hx)),lt_div_iff₀ (sq_pos_of_pos hx)]
      have he := (mul_le_mul_of_nonneg_left h (Real.exp_pos 8).le)
      exact he.trans_lt hb
    have he := ordinaryPrimeGenerator_exponent (n • successorSquareTriple n) k
    change deningerRatExp (q n) k=if k ∈ S n then _ else 0 at he
    simp only [price,he,if_neg hk,Int.cast_zero,zero_mul,squarePrimeEndpoint,hz hn' hlow,hz hhigh hsq,mul_zero,and_self]
  · simp [price,squarePrimeEndpoint,weight,hp]

private theorem error_row {n k : ℕ} (hn : 0 < n) :
    err n k=((deningerRatExp (q n) k:ℝ)-diagonalPrimeProfile n k)*weight k := by
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have he : Real.log (((2*n:ℕ):ℝ)^2)=Real.log ((n:ℝ)^2)+Real.log 4 := by
    push_cast
    rw [mul_pow,Real.log_mul (by norm_num) (sq_pos_of_pos hn').ne']
    norm_num
    ring
  simp only [err,price,squarePrimeEndpoint,diagonalPrimeProfile,squareLogProfile,he,
    show Real.log k-(Real.log ((n:ℝ)^2)+Real.log 4)=Real.log k-Real.log ((n:ℝ)^2)-Real.log 4 by ring,
    Nat.cast_mul,Nat.cast_ofNat]
  ring

private theorem error_summable {n : ℕ} (hn : 0 < n) : Summable (fun k => |err n k|) :=
  summable_of_ne_finset_zero (s := S n) fun k hk => by
    obtain ⟨h₁,h₂,h₃⟩ := endpoint_zero hn hk
    simp [err,h₁,h₂,h₃]

private theorem error_budget : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n → (∑' k, |err n k|) ≤ C*(n:ℝ)^2 := by
  obtain ⟨C,hC,hE⟩ := diagonal_prime_exponent_profile_error
  refine ⟨C,hC,fun {n} hn => ?_⟩
  rw [tsum_eq_sum (s := S n) (fun k hk => by
    obtain ⟨h₁,h₂,h₃⟩ := endpoint_zero hn hk
    simp [err,h₁,h₂,h₃])]
  apply le_trans (le_of_eq (sum_congr rfl fun k hk => ?_)) (hE hn)
  have hp := (mem_filter.mp hk).2
  rw [error_row hn,abs_mul,weight,if_pos hp,abs_of_nonneg (Real.log_natCast_nonneg _),vonMangoldt_apply_prime hp]
  rfl

private theorem price_sum (n : ℕ) (hn : 0 < n) : (∑' k, price n k)=Real.log (q n:ℝ) := by
  rw [tsum_eq_sum (s := S n) (fun _ hk => (endpoint_zero hn hk).1),q,log_ordinaryPrimeGenerator]
  refine sum_congr rfl fun k hk => ?_
  have hp := (mem_filter.mp hk).2
  have he := ordinaryPrimeGenerator_exponent (n • successorSquareTriple n) k
  change deningerRatExp (q n) k=if k ∈ S n then _ else 0 at he
  rw [price,he,if_pos hk,weight,if_pos hp,vonMangoldt_apply_prime hp]

private theorem endpoint_summable {n : ℕ} (hn : 0 < n) : Summable (squarePrimeEndpoint n) :=
  summable_of_ne_finset_zero (s := S n) fun _ hk => (endpoint_zero hn hk).2.1

/-- The positive endpoint has cubic mass with an explicit leading coefficient. -/
theorem tendsto_squarePrimeEndpoint_mass :
    Tendsto (fun n : ℕ => (∑' k, squarePrimeEndpoint n k)/(n:ℝ)^3) atTop (𝓝 (4*squareAutocorrelationMass)) := by
  have hK : HasCompactSupport splineAutoCorr := by
    rw [show splineAutoCorr=upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
    exact hasCompactSupport_upow 1 7
  have h := ((tendsto_ordinary_prime_log_test continuous_splineAutoCorr hK).comp
    ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)).const_mul 4
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hsub : (∑' p : Nat.Primes, squarePrimeEndpoint n p.val)=∑' k, squarePrimeEndpoint n k :=
    tsum_subtype_eq_of_support_subset fun k hk hp => hk (by simp [squarePrimeEndpoint,weight,hp])
  rw [← hsub]
  let L := fun p : Nat.Primes => Real.log (p:ℕ)*(splineAutoCorr (Real.log ((p:ℕ)/(n:ℝ)^2))/Real.sqrt ((p:ℕ)/(n:ℝ)^2))
  have he (p : Nat.Primes) : squarePrimeEndpoint n p.val = (4*(n:ℝ))*L p := by
    have hp : 0 < ((p:ℕ):ℝ) := Nat.cast_pos.mpr p.property.pos
    simp only [squarePrimeEndpoint,weight,if_pos p.property,L,Real.log_div hp.ne' (sq_pos_of_pos hn').ne',
      Real.sqrt_div hp.le,Real.sqrt_sq hn'.le]
    field_simp [hn'.ne',(Real.sqrt_pos.mpr hp).ne'] <;> ring
  simp_rw [he]
  rw [tsum_mul_left]
  change 4*((∑' p, L p)/(n:ℝ)^2)=_
  field_simp

private theorem harmonic_block :
    Tendsto (fun N : ℕ => ∑ j ∈ Ioc N (2*N), 1/(j:ℝ)) atTop (𝓝 (Real.log 2)) := by
  have hsum (N : ℕ) : (∑ j ∈ Ioc 0 N, 1/(j:ℝ)) = (harmonic N:ℝ) := by
    induction N with
    | zero => simp
    | succ N ih => rw [sum_Ioc_succ_top (Nat.zero_le _),ih,harmonic_succ]; push_cast; ring
  apply HTGeometry.tendsto_harmonic_two_mul_sub_harmonic.congr
  intro N
  have hs := sum_Ioc_consecutive (fun j : ℕ => 1/(j:ℝ)) (Nat.zero_le N) (show N ≤ 2*N by omega)
  rw [hsum,hsum] at hs
  linarith only [hs]

private theorem moving_harmonic_block {f : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (n:ℝ)*f n) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => ∑ j ∈ Ioc N (2*N), f j) atTop (𝓝 (L*Real.log 2)) := by
  have herr : Tendsto (fun N : ℕ => ∑ j ∈ Ioc N (2*N), (f j-L/j)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp h (ε/2) (half_pos hε)
    refine ⟨max 1 N,fun n hn => ?_⟩
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr ((le_max_left 1 N).trans hn)
    have row (j : ℕ) (hj : j ∈ Ioc n (2*n)) : |f j-L/j| ≤ (ε/2)/n := by
      have hjn := (mem_Ioc.mp hj).1
      have hj' : 0 < (j:ℝ) := hn'.trans (Nat.cast_lt.mpr hjn)
      have he := hN j ((le_max_right 1 N).trans (hn.trans hjn.le))
      rw [Real.dist_eq] at he
      rw [show f j-L/j=((j:ℝ)*f j-L)/j by field_simp,abs_div,abs_of_pos hj']
      exact (div_le_div_of_nonneg_right he.le hj'.le).trans
        (div_le_div_of_nonneg_left (half_nonneg hε.le) hn' (Nat.cast_le.mpr hjn.le))
    rw [Real.dist_eq,sub_zero]
    refine ((abs_sum_le_sum_abs _ _).trans ((sum_le_sum row).trans_eq ?_)).trans_lt (half_lt_self hε)
    rw [sum_const,nsmul_eq_mul,Nat.card_Ioc,show 2*n-n=n by omega]
    field_simp [hn'.ne']
  have ht := herr.add (harmonic_block.const_mul L)
  rw [zero_add] at ht
  refine ht.congr fun N => ?_
  rw [sum_sub_distrib,mul_sum]
  simp only [div_eq_mul_inv,one_mul,sub_add_cancel]

/-- At fourth-power conductor weights the moving endpoint on N < m ≤ 2N
retains total logarithmic prime mass 4 M log 2. -/
theorem squarePrimeEndpoint_mass_on_doubled_interval :
    Tendsto (fun N : ℕ => ∑ m ∈ Ioc N (2*N),
      (∑' k, squarePrimeEndpoint m k)/(m:ℝ)^4) atTop
      (𝓝 (4*squareAutocorrelationMass*Real.log 2)) := by
  apply moving_harmonic_block
  refine tendsto_squarePrimeEndpoint_mass.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  field_simp [Nat.cast_ne_zero.mpr hn.ne' : (n:ℝ)≠0]

/-- Endpoint after weighting an individual conductor by its inverse fourth power. -/
def fourthPowerPrimeEndpoint (n k : ℕ) := squarePrimeEndpoint n k/(n:ℝ)^4

private theorem fourthPower_row {n : ℕ} (hn : 0 < n) (k : ℕ) :
    price n k/(n:ℝ)^4 =
      fourthPowerPrimeEndpoint n k-2*fourthPowerPrimeEndpoint (2*n) k+err n k/(n:ℝ)^4 := by
  simp only [fourthPowerPrimeEndpoint,err,Nat.cast_mul,Nat.cast_ofNat]
  field_simp [Nat.cast_ne_zero.mpr hn.ne' : (n:ℝ) ≠ 0] <;> ring

/-- The total absolute error of the fourth-power decomposition is summable. -/
theorem summable_fourthPower_prime_error :
    Summable (fun i : ℕ × ℕ => |err i.1 i.2/(i.1:ℝ)^4|) := by
  obtain ⟨C,hC,h⟩ := error_budget
  apply (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
  constructor
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp only [abs_div,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg n) 4)]
      exact (error_summable hn).div_const _
  · have hs := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left C
    apply Summable.of_nonneg_of_le (fun n => tsum_nonneg fun k => abs_nonneg _) _ hs
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp only [abs_div,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg n) 4),tsum_div_const]
      refine (div_le_div_of_nonneg_right (h hn) (pow_nonneg (Nat.cast_nonneg n) 4)).trans_eq ?_
      field_simp [Nat.cast_ne_zero.mpr hn.ne' : (n:ℝ) ≠ 0] <;> ring

private theorem scaled_spline_step {K H : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hb : ∀ x, |splineAutoCorr x| ≤ H)
    (hl : ∀ x y, |splineAutoCorr x-splineAutoCorr y| ≤ K*|x-y|)
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    |splineAutoCorr (t-Real.log (x^2))/x^2 -
      splineAutoCorr (t-Real.log ((x+1)^2))/(x+1)^2| ≤ (2*K+2*H)/x^3 := by
  let a := splineAutoCorr (t-Real.log (x^2))
  let b := splineAutoCorr (t-Real.log ((x+1)^2))
  have hx1 : 0 < x+1 := by linarith only [hx]
  have hlx : Real.log (x+1)-Real.log x ≤ 1/x := by
    rw [← Real.log_div hx1.ne' hx.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hx1 hx)).trans_eq ?_
    field_simp
  have hab : |a-b| ≤ 2*K/x := by
    have h := hl (t-Real.log (x^2)) (t-Real.log ((x+1)^2))
    rw [show (t-Real.log (x^2))-(t-Real.log ((x+1)^2))=Real.log ((x+1)^2)-Real.log (x^2) by ring,
      Real.log_pow,Real.log_pow] at h
    rw [abs_of_nonneg (by nlinarith only [Real.log_le_log hx (show x ≤ x+1 by linarith)] :
      0 ≤ (2:ℝ)*Real.log (x+1)-2*Real.log x)] at h
    calc _ ≤ K*(2*Real.log (x+1)-2*Real.log x) := h
      _ = K*(2*(Real.log (x+1)-Real.log x)) := by ring
      _ ≤ K*(2*(1/x)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlx (by norm_num)) hK
      _ = _ := by ring
  have hinv : 0 ≤ 1/x^2-1/(x+1)^2 := sub_nonneg.mpr
    (div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hx) (by nlinarith only [hx]))
  have hstep : 1/x^2-1/(x+1)^2 ≤ 2/x^3 := by
    field_simp [hx.ne',hx1.ne']
    nlinarith only [hx,sq_nonneg x]
  change |a/x^2-b/(x+1)^2| ≤ _
  rw [show a/x^2-b/(x+1)^2=(a-b)/x^2+b*(1/x^2-1/(x+1)^2) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div,abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_nonneg hinv]
  exact (add_le_add (div_le_div_of_nonneg_right hab (sq_nonneg _))
    (mul_le_mul (hb _) hstep hinv hH)).trans_eq (by ring)

/-- The total prime mass of a consecutive endpoint difference is O(n⁻²). -/
theorem fourthPowerPrimeEndpoint_variation : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    (∑' k, |fourthPowerPrimeEndpoint n k-fourthPowerPrimeEndpoint (n+1) k|) ≤ C/(n:ℝ)^2 := by
  have hc : ContDiff ℝ 6 (upow 1 7) := contDiff_upow one_pos 6
  have hs := hasCompactSupport_upow 1 7
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hc (by norm_num)
  obtain ⟨H,hH⟩ := hs.exists_bound_of_continuous hc.continuous
  have hH₀ := (norm_nonneg _).trans (hH 0)
  have hb (x : ℝ) : |splineAutoCorr x| ≤ H := by
    simpa only [splineAutoCorr_eq_eight_boxes,Real.norm_eq_abs] using hH x
  have hl (x y : ℝ) : |splineAutoCorr x-splineAutoCorr y| ≤ (K:ℝ)*|x-y| := by
    simpa only [splineAutoCorr_eq_eight_boxes,Real.dist_eq] using hK.dist_le_mul x y
  obtain ⟨A,hA,hwindow⟩ := successorSquare_window_bound
  let D : ℝ := 4*(2*(K:ℝ)+2*H)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA₀ := zero_le_one.trans hA
  refine ⟨68*A*D,by positivity,fun {n} hn => ?_⟩
  let L := fun m : ℕ => 3*windowEnd ((2*m+1)^2+1)
  let M := max (L n) (L (n+1))
  let B := fourthPowerPrimeEndpoint
  have hout {k : ℕ} (hk : k ∉ ordinaryPrimeLags M) (m : ℕ) (hm : 0 < m) (hd : L m ≤ M) :
      B m k=0 := by
    have hkm : k ∉ S m := fun hh => hk (mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hh).1).1,
      ((mem_Icc.mp (mem_filter.mp hh).1).2).trans hd⟩,(mem_filter.mp hh).2⟩)
    simp only [B,fourthPowerPrimeEndpoint,(endpoint_zero hm hkm).2.1,zero_div]
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hr {m : ℕ} (hm : 0 < m) : Real.sqrt (L m) ≤ A*m := by
    simpa only [Real.sqrt_sq (mul_nonneg hA₀ (Nat.cast_nonneg m))] using Real.sqrt_le_sqrt (hwindow hm)
  have hM : Real.sqrt M ≤ A*((n:ℝ)+1) := by
    rcases le_total (L n) (L (n+1)) with h | h
    · simpa only [M,max_eq_right h,Nat.cast_add,Nat.cast_one] using hr (Nat.succ_pos n)
    · rw [show M=L n from max_eq_left h]
      exact (hr hn).trans (mul_le_mul_of_nonneg_left (by linarith) hA₀)
  change (∑' k, |B n k-B (n+1) k|) ≤ _
  rw [tsum_eq_sum (s := ordinaryPrimeLags M) (fun k hk => by
    simp only [hout hk n hn (le_max_left _ _),hout hk (n+1) (Nat.succ_pos _) (le_max_right _ _),sub_self,abs_zero])]
  have hrow (k : ℕ) (hk : k ∈ ordinaryPrimeLags M) :
      |B n k-B (n+1) k| ≤ D/(n:ℝ)^3*(vonMangoldt k/Real.sqrt k) := by
    have hp := (mem_filter.mp hk).2
    have hlog := Real.log_natCast_nonneg k
    have hp' := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.pos : (0:ℝ)<k)).ne'
    have form (m : ℕ) (hm : 0 < m) : B m k =
        (4*Real.log k/Real.sqrt k)*(splineAutoCorr (Real.log k-Real.log ((m:ℝ)^2))/(m:ℝ)^2) := by
      simp only [B,fourthPowerPrimeEndpoint,squarePrimeEndpoint,weight,if_pos hp]
      field_simp [Nat.cast_ne_zero.mpr hm.ne' : (m:ℝ)≠0,hp'] <;> ring
    rw [form n hn,form (n+1) (Nat.succ_pos _),Nat.cast_add,Nat.cast_one,← mul_sub,abs_mul,
      abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hlog) (Real.sqrt_nonneg _)),vonMangoldt_apply_prime hp]
    exact (mul_le_mul_of_nonneg_left (scaled_spline_step K.coe_nonneg hH₀ hb hl hn' _)
      (by positivity)).trans_eq (by dsimp only [D]; ring)
  refine (sum_le_sum hrow).trans ?_
  rw [← mul_sum]
  have he := ((ordinaryPrimeLagSums M).2.trans (mul_le_mul_of_nonneg_left hM (by norm_num)))
  have hn1 : (n:ℝ)+1 ≤ 2*n := by
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine (mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hn1 hA₀) (by norm_num))) (div_nonneg hD (pow_nonneg hn'.le _))).trans_eq ?_
  field_simp [hn'.ne'] <;> ring

private theorem range_eq_zero_add_interval (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ range (N+1), f j)=f 0+∑ j ∈ Ioc 0 N, f j := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih,sum_Ioc_succ_top (Nat.zero_le N),add_assoc]

private theorem alternating_block (f : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Ioc 0 N, (f j-2*f (2*j)) =
      (∑ i ∈ range N, (f (2*i+1)-f (2*i+2)))-∑ m ∈ Ioc N (2*N), f m := by
  have hpair (n : ℕ) : (∑ m ∈ Ioc 0 (2*n), f m) - 2*∑ j ∈ Ioc 0 n, f (2*j) =
      ∑ i ∈ range n, (f (2*i+1)-f (2*i+2)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,← ih,show 2*(n+1)=2*n+1+1 by omega]
      simp only [sum_Ioc_succ_top (Nat.zero_le _)]
      ring
  rw [sum_sub_distrib,← mul_sum,← hpair]
  have h := sum_Ioc_consecutive f (Nat.zero_le N) (show N ≤ 2*N by omega)
  linarith only [h]

private def pairedEndpoint (i : ℕ × ℕ) :=
  fourthPowerPrimeEndpoint (2*i.1+1) i.2-fourthPowerPrimeEndpoint (2*i.1+2) i.2

private theorem summable_pairedEndpoint : Summable pairedEndpoint := by
  obtain ⟨C,hC,h⟩ := fourthPowerPrimeEndpoint_variation
  apply Summable.of_abs
  apply (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
  constructor
  · intro j
    let n := 2*j+1
    have hb (m : ℕ) (hm : 0 < m) : Summable (fourthPowerPrimeEndpoint m) :=
      (endpoint_summable hm).div_const _
    exact ((hb n (Nat.succ_pos _)).sub (hb (n+1) (Nat.succ_pos _))).abs
  · have hi : Function.Injective (fun j : ℕ => 2*j+1) := fun a b he => by dsimp at he; omega
    have hs := ((Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left C).comp_injective hi
    exact Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => abs_nonneg _))
      (fun j => (h (Nat.succ_pos (2*j))).trans_eq (by ring)) hs

private theorem fourthPower_endpoint_column (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, fourthPowerPrimeEndpoint n k=0 := by
  have ht := Real.tendsto_log_atTop.comp ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually_gt_atTop (Real.log k+8)] with n hn
  change Real.log k+8 < Real.log ((n:ℝ)^2) at hn
  have hz := splineAutoCorr_zero_outside (x := Real.log k-Real.log ((n:ℝ)^2))
    (by linarith only [hn,neg_abs_le (Real.log k-Real.log ((n:ℝ)^2))])
  simp [fourthPowerPrimeEndpoint,squarePrimeEndpoint,hz]

private def fourthPowerError (i : ℕ × ℕ) := err i.1 i.2/(i.1:ℝ)^4

/-- In prime order the normalized fourth-power series exceeds the conductor-order
limit by exactly 4 M log 2. Paired first differences and the row errors are summable
over the product of the two index sets. -/
theorem fourthPower_square_prime_mass_escape :
    Tendsto (fun N : ℕ => (∑' k : ℕ, ∑' n : ℕ, price n k/(n:ℝ)^4) -
      ∑ n ∈ Ioc 0 N, Real.log (q n:ℝ)/(n:ℝ)^4) atTop (𝓝 (4*squareAutocorrelationMass*Real.log 2)) := by
  let B := fourthPowerPrimeEndpoint
  let E := fourthPowerError
  have hE : Summable E := Summable.of_abs summable_fourthPower_prime_error
  have hP := summable_pairedEndpoint
  have hzero (k : ℕ) : E (0,k)=0 := by simp [E,fourthPowerError]
  have hB (n : ℕ) (hn : 0 < n) : Summable (B n) := (endpoint_summable hn).div_const _
  have hcol (k : ℕ) : (∑' n : ℕ, price n k/(n:ℝ)^4) =
      (∑' j : ℕ, pairedEndpoint (j,k)) + ∑' n : ℕ, E (n,k) := by
    obtain ⟨J,hJ⟩ := eventually_atTop.mp (fourthPower_endpoint_column k)
    have hf (d : ℕ) (hd : 0 < d) : Summable (fun n : ℕ => B (d*n) k) := by
      apply summable_of_ne_finset_zero (s := range J)
      intro n hn
      exact hJ _ ((le_of_not_gt (fun hl => hn (mem_range.mpr hl))).trans (Nat.le_mul_of_pos_left _ hd))
    have hs : Summable (fun n : ℕ => B n k) := by simpa only [one_mul] using hf 1 Nat.one_pos
    have he (n : ℕ) : price n k/(n:ℝ)^4=B n k-2*B (2*n) k+E (n,k) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [B,fourthPowerPrimeEndpoint,hzero]
      · exact fourthPower_row hn k
    simp_rw [he]
    rw [(hs.sub ((hf 2 (by decide)).mul_left 2)).tsum_add (hE.prod_symm.prod_factor k)]
    apply congrArg (· + ∑' n : ℕ, E (n,k))
    have hlim := (hs.sub ((hf 2 (by decide)).mul_left 2)).hasSum.tendsto_sum_nat
    have pairlim := (hP.prod_symm.prod_factor k).hasSum.tendsto_sum_nat
    refine tendsto_nhds_unique hlim (pairlim.congr' ?_)
    filter_upwards [eventually_ge_atTop (J+1)] with N hN
    have htail : (∑ j ∈ Ioc N (2*N), B j k)=0 :=
      sum_eq_zero fun j hj => hJ _ (by have := (mem_Ioc.mp hj).1; omega)
    have ha := alternating_block (fun j => B j k) N
    have bf : B 0 k=0 := by simp [B,fourthPowerPrimeEndpoint]
    have bn : B N k=0 := hJ _ (by omega)
    have bd : B (2*N) k=0 := hJ _ (by omega)
    have hh := range_eq_zero_add_interval (fun j => B j k-2*B (2*j) k) N
    rw [Finset.sum_range_succ] at hh
    simpa only [Function.comp_apply,pairedEndpoint,B,htail,sub_zero] using
      (show (∑ i ∈ range N, (B (2*i+1) k-B (2*i+2) k)) =
          ∑ i ∈ range N, (B i k-2*B (2*i) k) by
        rw [htail,sub_zero] at ha
        simp only [mul_zero,bf,bn,bd,sub_self,mul_zero,zero_sub,sub_zero,zero_add,add_zero] at hh
        exact ha.symm.trans hh.symm)
  have hcols : (∑' k : ℕ, ∑' n : ℕ, price n k/(n:ℝ)^4) =
      (∑' j : ℕ, ∑' k : ℕ, pairedEndpoint (j,k)) + ∑' n : ℕ, ∑' k : ℕ, E (n,k) := by
    simp_rw [hcol]
    rw [hP.prod_symm.prod.tsum_add hE.prod_symm.prod,hP.tsum_comm,hE.tsum_comm]
  let mass := fun n : ℕ => ∑' k : ℕ, B n k
  have hrow (n : ℕ) (hn : 0 < n) : Real.log (q n:ℝ)/(n:ℝ)^4 =
      mass n-2*mass (2*n)+∑' k, E (n,k) := by
    rw [← price_sum n hn,← tsum_div_const]
    simp_rw [fourthPower_row hn]
    rw [((hB n hn).sub ((hB (2*n) (by omega)).mul_left _)).tsum_add (hE.prod_factor n),
      (hB n hn).tsum_sub ((hB (2*n) (by omega)).mul_left _),tsum_mul_left]
  have hpair (j : ℕ) : mass (2*j+1)-mass (2*j+2) = ∑' k, pairedEndpoint (j,k) :=
    ((hB _ (by omega)).tsum_sub (hB _ (by omega))).symm
  have he : Tendsto (fun N : ℕ => ∑ n ∈ Ioc 0 N, ∑' k : ℕ, E (n,k)) atTop (𝓝 (∑' n, ∑' k, E (n,k))) := by
    have hz : (∑' k, E (0,k))=0 := by simp only [hzero,tsum_zero]
    have hi := hE.prod.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    apply hi.congr
    intro N
    change (∑ n ∈ range (N+1), ∑' k, E (n,k))=_
    rw [range_eq_zero_add_interval,hz,zero_add]
  have hp := hP.prod.hasSum.tendsto_sum_nat
  have ht := ((tendsto_const_nhds.sub hp).add (tendsto_const_nhds.sub he)).add squarePrimeEndpoint_mass_on_doubled_interval
  rw [sub_self,sub_self,zero_add,zero_add] at ht
  refine ht.congr fun N => ?_
  rw [hcols,sum_congr rfl (fun n hn => hrow n (mem_Ioc.mp hn).1),sum_add_distrib,
    alternating_block mass N]
  simp_rw [hpair]
  simp only [mass,B,fourthPowerPrimeEndpoint,tsum_div_const]
  ring

private def fourthMass (n : ℕ) := ∑' k : ℕ, fourthPowerPrimeEndpoint n k
private def fourthErrorMass (n : ℕ) := ∑' k : ℕ, fourthPowerError (n,k)
private def pairMass (j : ℕ) := ∑' k : ℕ, pairedEndpoint (j,k)

private theorem pairMass_eq (j : ℕ) : pairMass j=fourthMass (2*j+1)-fourthMass (2*j+2) := by
  have hb (m : ℕ) (hm : 0 < m) : Summable (fourthPowerPrimeEndpoint m) := (endpoint_summable hm).div_const _
  exact (hb _ (by omega)).tsum_sub (hb _ (by omega))

private theorem fourthMass_limit :
    Tendsto (fun n : ℕ => (n:ℝ)*fourthMass n) atTop (𝓝 (4*squareAutocorrelationMass)) := by
  refine tendsto_squarePrimeEndpoint_mass.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [fourthMass,fourthPowerPrimeEndpoint,tsum_div_const]
  field_simp [Nat.cast_ne_zero.mpr hn.ne' : (n:ℝ)≠0]

private theorem fourthErrorMass_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    |fourthErrorMass n| ≤ C/(n:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := error_budget
  refine ⟨C,hC,fun {n} hn => ?_⟩
  change |∑' k, err n k/(n:ℝ)^4| ≤ _
  rw [tsum_div_const,abs_div,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) 4)]
  have he := (norm_tsum_le_tsum_norm ((error_summable hn).congr (fun k => (Real.norm_eq_abs _).symm)))
  simp only [Real.norm_eq_abs] at he
  exact (div_le_div_of_nonneg_right (he.trans (h hn)) (pow_nonneg (Nat.cast_nonneg _) 4)).trans_eq
    (by field_simp [Nat.cast_ne_zero.mpr hn.ne' : (n:ℝ)≠0] <;> ring)

private theorem pairMass_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, |pairMass j| ≤ C/((j:ℝ)+1)^2 := by
  obtain ⟨C,hC,h⟩ := fourthPowerPrimeEndpoint_variation
  refine ⟨C,hC,fun j => ?_⟩
  have ht := summable_pairedEndpoint.abs.prod_factor j
  have he := norm_tsum_le_tsum_norm (ht.congr fun k => (Real.norm_eq_abs _).symm)
  simp only [Real.norm_eq_abs] at he
  refine (he.trans (h (Nat.succ_pos (2*j)))).trans (div_le_div_of_nonneg_left hC (by positivity) ?_)
  apply pow_le_pow_left₀ (by positivity)
  push_cast
  linarith only [Nat.cast_nonneg (α := ℝ) j]

private theorem fourthPower_sum_row {n : ℕ} (hn : 0 < n) : Real.log (q n:ℝ)/(n:ℝ)^4 =
    fourthMass n-2*fourthMass (2*n)+fourthErrorMass n := by
  have hb (m : ℕ) (hm : 0 < m) : Summable (fourthPowerPrimeEndpoint m) := (endpoint_summable hm).div_const _
  have hE : Summable fourthPowerError := Summable.of_abs summable_fourthPower_prime_error
  rw [← price_sum n hn,← tsum_div_const]
  simp_rw [fourthPower_row hn]
  rw [((hb n hn).sub ((hb _ (by omega)).mul_left _)).tsum_add (hE.prod_factor n),
    (hb n hn).tsum_sub ((hb _ (by omega)).mul_left _),tsum_mul_left]
  rfl

private theorem interval_tail_estimate {f : ℕ → ℝ} {C : ℝ}
    (hc : 0 ≤ C) (hb : ∀ n : ℕ, 0 < n → |f n| ≤ C/(n:ℝ)^2)
    {N M : ℕ} (hn : 0 < N) : |∑ j ∈ Ioc N M, f j| ≤ C/N := by
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (fun j hj => hb j (hn.trans (mem_Ioc.mp hj).1))).trans ?_)
  simp_rw [show ∀ j : ℕ, C/(j:ℝ)^2=C*(1/(j:ℝ)^2) from fun j => by ring]
  rw [← mul_sum,show Ioc N M=Icc (N+1) M by ext j; simp only [mem_Ioc,mem_Icc]; omega]
  exact (mul_le_mul_of_nonneg_left (sum_inv_sq_tail_le hn M) hc).trans_eq (by ring)

private theorem pair_tail {N M : ℕ} (hn : 0 < N) {C : ℝ} (hc : 0 ≤ C)
    (h : ∀ j : ℕ, |pairMass j| ≤ C/((j:ℝ)+1)^2) :
    |∑ i ∈ Ico N M, pairMass i| ≤ C/N := by
  have he : (∑ i ∈ Ico N M, pairMass i)=∑ j ∈ Ioc N M, pairMass (j-1) := by
    apply sum_nbij' (fun i => i+1) (fun j => j-1)
    · intro i hi; exact mem_Ioc.mpr ⟨by have := (mem_Ico.mp hi).1; omega,by have := (mem_Ico.mp hi).2; omega⟩
    · intro j hj; exact mem_Ico.mpr ⟨by have := (mem_Ioc.mp hj).1; omega,by have := (mem_Ioc.mp hj).2; omega⟩
    · intro i _; omega
    · intro j hj; have := (mem_Ioc.mp hj).1; omega
    · intro i _; simp
  rw [he]
  apply interval_tail_estimate hc _ hn
  intro j hj
  simpa only [Nat.cast_sub (show 1 ≤ j from hj),Nat.cast_one,sub_add_cancel] using h (j-1)

/-- Twice the mass of the even endpoints in the moving interval. -/
def squareEvenBoundary (N : ℕ) := 2*∑ j ∈ Ioc (N/2) N, fourthMass (2*j)

private def fourthPartial (N : ℕ) := ∑ n ∈ Ioc 0 N, Real.log (q n:ℝ)/(n:ℝ)^4

private theorem fourth_even_sum (N : ℕ) :
    fourthPartial N+squareEvenBoundary N =
      (∑ j ∈ range (N/2), pairMass j) + (if N%2=0 then 0 else fourthMass N) +
      ∑ n ∈ Ioc 0 N, fourthErrorMass n := by
  have hp (j : ℕ) :
      (∑ m ∈ Ioc 0 (2*j), fourthMass m)-2*∑ m ∈ Ioc 0 j, fourthMass (2*m) = ∑ i ∈ range j, pairMass i := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ,← ih,pairMass_eq,show 2*(j+1)=2*j+1+1 by omega]
      simp only [sum_Ioc_succ_top (Nat.zero_le _)]
      ring
  have he := sum_Ioc_consecutive (fun j => fourthMass (2*j)) (Nat.zero_le (N/2)) (Nat.div_le_self N 2)
  rw [fourthPartial,squareEvenBoundary,sum_congr rfl (fun n h => fourthPower_sum_row (mem_Ioc.mp h).1),
    sum_add_distrib,sum_sub_distrib,← mul_sum,← hp]
  by_cases h : N%2=0
  · rw [if_pos h,show 2*(N/2)=N by omega]; linarith only [he]
  · have hs := sum_Ioc_succ_top (a := 0) (b := 2*(N/2)) (by omega) fourthMass
    rw [show 2*(N/2)+1=N by omega] at hs
    rw [if_neg h]; linarith only [he,hs]

private theorem squareEvenBoundary_limit : Tendsto squareEvenBoundary atTop (𝓝 (4*squareAutocorrelationMass*Real.log 2)) := by
  let f := fun j : ℕ => 2*fourthMass (2*j)
  have hd : Tendsto (fun j : ℕ => 2*j) atTop atTop := tendsto_atTop_mono (f := id) (fun j => by dsimp; omega) tendsto_id
  have hl : Tendsto (fun j : ℕ => (j:ℝ)*f j) atTop (𝓝 (4*squareAutocorrelationMass)) := by
    refine (fourthMass_limit.comp hd).congr fun j => ?_
    change ((2*j:ℕ):ℝ)*fourthMass (2*j)=(j:ℝ)*(2*fourthMass (2*j))
    push_cast; ring
  have hhalf : Tendsto (fun n : ℕ => n/2) atTop atTop := tendsto_atTop.mpr (fun m => ⟨2*m,fun n hn => by omega⟩)
  have hf₀ : Tendsto f atTop (𝓝 0) := by
    refine (hl.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne' : (n:ℝ)≠0)
  have hterm : Tendsto (fun n : ℕ => if n%2=0 then 0 else f n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by split_ifs <;> simp) (tendsto_zero_iff_norm_tendsto_zero.mp hf₀)
  have h := ((moving_harmonic_block hl).comp hhalf).add hterm
  rw [add_zero] at h
  refine h.congr fun n => ?_
  change (∑ j ∈ Ioc (n/2) (2*(n/2)), f j)+(if n%2=0 then 0 else f n)=_
  rw [squareEvenBoundary,mul_sum]
  by_cases he : n%2=0
  · rw [if_pos he,show 2*(n/2)=n by omega,add_zero]
  · rw [if_neg he]
    have h := sum_Ioc_succ_top (a := n/2) (b := 2*(n/2)) (by omega) f
    rw [show 2*(n/2)+1=n by omega] at h
    exact h.symm

/-- The limit in conductor order with its moving positive boundary restored. -/
def fourthPowerAdjustedLimit := (∑' j, pairMass j) + ∑' n, fourthErrorMass n

private theorem adjusted_fourthPower_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |fourthPowerAdjustedLimit-(fourthPartial N+squareEvenBoundary N)| ≤ C/N := by
  obtain ⟨P,hP,hp⟩ := pairMass_bound
  obtain ⟨E,hE,he⟩ := fourthErrorMass_bound
  have hq := (summable_pairedEndpoint.prod : Summable pairMass)
  have hr := ((Summable.of_abs summable_fourthPower_prime_error : Summable fourthPowerError).prod : Summable fourthErrorMass)
  have hM := (Metric.tendsto_atTop.mp fourthMass_limit 1 one_pos)
  obtain ⟨J,hJ⟩ := hM
  let K := 1+|4*squareAutocorrelationMass|
  have hK : 0 ≤ K := by unfold K; positivity
  refine ⟨3*P+E+K,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max J 2)] with n hn
  have hn₂ : 2 ≤ n := (le_max_right _ _).trans hn
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hk' : 0 < (↑(n/2):ℝ) := by exact_mod_cast (by omega : 0 < n/2)
  have hb : |fourthMass n| ≤ K/n := by
    apply (le_div_iff₀ hn').mpr
    rw [mul_comm,← abs_of_pos hn',← abs_mul]
    have h := hJ n ((le_max_left _ _).trans hn)
    rw [Real.dist_eq] at h
    have hu := abs_sub_abs_le_abs_sub ((n:ℝ)*fourthMass n) (4*squareAutocorrelationMass)
    dsimp only [K]
    linarith only [hu,h]
  have hb' : |if n%2=0 then 0 else fourthMass n| ≤ K/n := by split_ifs <;> simp [hb,div_nonneg hK hn'.le]
  have hpt : |(∑' j, pairMass j)-∑ j ∈ range (n/2), pairMass j| ≤ 3*P/n := by
    have ht := hq.hasSum.tendsto_sum_nat.sub_const (∑ j ∈ range (n/2), pairMass j)
    refine le_of_tendsto ht.abs ?_
    filter_upwards [eventually_ge_atTop (n/2)] with m hm
    rw [← sum_Ico_eq_sub _ hm]
    refine (pair_tail (by omega) hP hp).trans ?_
    apply (div_le_div_iff₀ hk' hn').mpr
    have hn₃ : (n:ℝ) ≤ 3*(↑(n/2):ℝ) := by exact_mod_cast (by omega : n ≤ 3*(n/2))
    linarith only [mul_le_mul_of_nonneg_left hn₃ hP]
  have het : |(∑' j, fourthErrorMass j)-∑ j ∈ Ioc 0 n, fourthErrorMass j| ≤ E/n := by
    have ht := (hr.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).sub_const (∑ j ∈ Ioc 0 n, fourthErrorMass j)
    refine le_of_tendsto ht.abs ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    change |(∑ j ∈ range (m+1), fourthErrorMass j)-_| ≤ _
    rw [range_eq_zero_add_interval,show fourthErrorMass 0=0 by simp [fourthErrorMass,fourthPowerError],zero_add,
      ← sum_Ioc_consecutive fourthErrorMass (Nat.zero_le n) hm,add_sub_cancel_left]
    exact interval_tail_estimate hE he (by omega)
  rw [fourth_even_sum,fourthPowerAdjustedLimit]
  generalize (∑' j, pairMass j)=p at *
  generalize (∑ j ∈ range (n/2), pairMass j)=q at *
  generalize (∑' j, fourthErrorMass j)=r at *
  generalize (∑ j ∈ Ioc 0 n, fourthErrorMass j)=e at *
  generalize (if n%2=0 then (0:ℝ) else fourthMass n)=v at *
  rw [show p+r-(q+v+e)=(p-q)+(r-e)+(-v) by ring]
  refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) (le_refl |-v|)).trans ?_)
  rw [abs_neg]
  exact (add_le_add (add_le_add hpt het) hb').trans_eq (by ring)

/-- The signed tail equals the moving even endpoint minus its limiting
mass with an O(1/N) error. -/
theorem fourthPower_square_price_tail :
    let L := fourthPowerAdjustedLimit-4*squareAutocorrelationMass*Real.log 2
    Tendsto fourthPartial atTop (𝓝 L) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |(L-fourthPartial N)-(squareEvenBoundary N-4*squareAutocorrelationMass*Real.log 2)| ≤ C/N := by
  obtain ⟨C,hC,h⟩ := adjusted_fourthPower_sum
  have hc := (tendsto_const_nhds (x := C)).div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have h₀ : Tendsto (fun N => fourthPowerAdjustedLimit-(fourthPartial N+squareEvenBoundary N)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) h hc)
  have ht := ((tendsto_const_nhds (x := fourthPowerAdjustedLimit)).sub h₀).sub squareEvenBoundary_limit
  rw [sub_zero] at ht
  refine ⟨ht.congr (fun _ => by ring),C,hC,?_⟩
  exact h.mono fun n hn => by simpa only [show ∀ x y z a : ℝ, (x-a-y)-(z-a)=x-(y+z) by intros; ring] using hn

/-- Partial summation turns a reciprocal-size fluctuation of the positive
even boundary into the cubic estimate for the actual rational prefix. -/
theorem squareGeneratorPrefix_cubic_of_even_boundary
    (hb : ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ n : ℕ in atTop,
      |squareEvenBoundary n-4*squareAutocorrelationMass*Real.log 2| ≤ E/n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 0 < N →
      |Real.log (squareGeneratorPrefix N:ℝ)| ≤ C*(N:ℝ)^3 := by
  let L := fourthPowerAdjustedLimit-4*squareAutocorrelationMass*Real.log 2
  let T := fun n => L-fourthPartial n
  obtain ⟨D,hD,hd⟩ := fourthPower_square_price_tail.2
  obtain ⟨E,hE,he⟩ := hb
  have ht : ∀ᶠ n in atTop, |T n| ≤ (D+E)/(n:ℝ) := by
    filter_upwards [hd,he] with n ha hb
    let B := squareEvenBoundary n-4*squareAutocorrelationMass*Real.log 2
    change |T n-B| ≤ _ at ha
    rw [← sub_add_cancel (T n) B]
    exact (abs_add_le _ _).trans ((add_le_add ha hb).trans_eq (add_div _ _ _).symm)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp ht
  let H := ∑ j ∈ range J, (j:ℝ)*|T j|
  let K := D+E+H
  have hH : 0 ≤ H := sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hK : 0 ≤ K := add_nonneg (add_nonneg hD hE) hH
  have hT {j : ℕ} (hj : 0 < j) : |T j| ≤ K/(j:ℝ) := by
    by_cases h : J ≤ j
    · exact (hJ j h).trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right hH) (Nat.cast_nonneg _))
    · apply (le_div_iff₀ (Nat.cast_pos.mpr hj)).mpr
      rw [mul_comm]
      exact (single_le_sum (fun k _ => mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (T k)))
        (mem_range.mpr (lt_of_not_ge h))).trans (le_add_of_nonneg_left (add_nonneg hD hE))
  have hstep (n : ℕ) : Real.log (q (n+1):ℝ) = (((n+1:ℕ):ℝ))^4*(T n-T (n+1)) := by
    dsimp only [T,fourthPartial]
    rw [sum_Ioc_succ_top (Nat.zero_le n)]
    field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) : ((n+1:ℕ):ℝ)≠0] <;> ring
  let delta := fun j : ℕ => (((j+1:ℕ):ℝ))^4-(j:ℝ)^4
  have hsum (N : ℕ) : (∑ n ∈ Ioc 0 N, Real.log (q n:ℝ))+(N:ℝ)^4*T N =
      ∑ j ∈ range N, delta j*T j := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [sum_Ioc_succ_top (Nat.zero_le _),hstep,Finset.sum_range_succ,← ih]
      dsimp only [delta]; ring
  have hdj {j : ℕ} (hj : 0 < j) : |delta j*T j| ≤ 15*K*(j:ℝ)^2 := by
    have hj' : 0 < (j:ℝ) := Nat.cast_pos.mpr hj
    have hj₁ : (1:ℝ) ≤ j := by exact_mod_cast hj
    have h₁ := mul_le_mul_of_nonneg_right hj₁ (Nat.cast_nonneg (α := ℝ) j)
    have h₂ := mul_le_mul_of_nonneg_right hj₁ (sq_nonneg (j:ℝ))
    have hδ : 0 ≤ delta j := sub_nonneg.mpr (pow_le_pow_left₀ hj'.le (Nat.cast_le.mpr (Nat.le_succ _)) 4)
    have hup : delta j ≤ 15*(j:ℝ)^3 := by
      dsimp only [delta]; push_cast; linarith only [hj₁,h₁,h₂]
    rw [abs_mul,abs_of_nonneg hδ]
    exact (mul_le_mul hup (hT hj) (abs_nonneg _) (by positivity)).trans_eq (by field_simp [hj'.ne'] <;> ring)
  refine ⟨|T 0|+16*K,by positivity,fun {N} hn => ?_⟩
  have hN : (1:ℝ) ≤ N := by exact_mod_cast hn
  have hz (j : ℕ) (hj : j ∈ range N) : |delta j*T j| ≤ (if j=0 then |T 0| else 0)+15*K*(N:ℝ)^2 := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · simp only [delta,Nat.zero_add,Nat.cast_one,one_pow,Nat.cast_zero,zero_pow (by decide : 4≠0),sub_zero,one_mul,if_true]
      exact le_add_of_nonneg_right (by positivity)
    · rw [if_neg h.ne',zero_add]
      exact (hdj h).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg j)
        (Nat.cast_le.mpr (mem_range.mp hj).le) 2) (by positivity))
  have hbound := (abs_sum_le_sum_abs (fun j => delta j*T j) (range N)).trans (sum_le_sum hz)
  rw [sum_add_distrib] at hbound
  simp only [sum_const,card_range,nsmul_eq_mul,Finset.sum_ite_eq',mem_range,if_pos hn] at hbound
  have hend := mul_le_mul_of_nonneg_left (hT hn) (pow_nonneg (Nat.cast_nonneg N) 4)
  have hN' : 0 < (N:ℝ) := Nat.cast_pos.mpr hn
  rw [show (N:ℝ)^4*(K/N)=K*(N:ℝ)^3 by field_simp [hN'.ne'] <;> ring] at hend
  have hlog : Real.log (squareGeneratorPrefix N:ℝ)=∑ n ∈ Ioc 0 N, Real.log (q n:ℝ) := by
    unfold squareGeneratorPrefix
    push_cast
    exact Real.log_prod (fun n _ => (show 0 < (q n:ℝ) by exact_mod_cast
      (show 0 < q n from prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _)).ne')
  rw [hlog,show (∑ n ∈ Ioc 0 N, Real.log (q n:ℝ))=(∑ j ∈ range N, delta j*T j)-(N:ℝ)^4*T N
    from eq_sub_of_add_eq (hsum N)]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg N) 4)]
  have hx := mul_le_mul_of_nonneg_left (one_le_pow₀ hN (n := 3)) (abs_nonneg (T 0))
  linarith only [hend,hbound,hx]

private def orbit (n j : ℕ) := 2^j*n
private def factor (j : ℕ) : ℝ := (1/8)^j
private def row (n j k : ℕ) := factor j*price (orbit n j) k
private def tail (n j k : ℕ) := factor j*squarePrimeEndpoint (orbit n j) k
private def remainder (n : ℕ) (i : ℕ × ℕ) := factor i.1*err (orbit n i.1) i.2

private theorem orbit_pos {n : ℕ} (hn : 0 < n) (j : ℕ) : 0 < orbit n j :=
  Nat.mul_pos (pow_pos (by decide : 0 < 2) j) hn

private theorem orbit_infty {n : ℕ} (hn : 0 < n) : Tendsto (orbit n) atTop atTop := by
  refine tendsto_atTop_mono (f := fun j : ℕ => 2^j) (fun j => ?_) (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2:ℕ)))
  exact Nat.le_mul_of_pos_right _ hn

private theorem row_split (n j k : ℕ) :
    row n j k=tail n j k-tail n (j+1) k+remainder n (j,k) := by
  simp only [row,tail,remainder,factor,orbit,err,pow_succ]
  rw [show (2:ℕ)^j*2*n=2*(2^j*n) by ring]
  ring

private def geometricError (n : ℕ) (r : ℝ) (i : ℕ × ℕ) := r^i.1*err (orbit n i.1) i.2

private theorem summable_geometricError {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) (hr₄ : r*4 < 1) :
    Summable (geometricError n r) := by
  obtain ⟨C,hC,hE⟩ := error_budget
  have hf (j : ℕ) : 0 ≤ r^j := pow_nonneg hr _
  have habs (j k : ℕ) : |geometricError n r (j,k)|=r^j*|err (orbit n j) k| := by
    rw [geometricError,abs_mul,abs_of_nonneg (hf j)]
  apply Summable.of_norm
  simp only [Real.norm_eq_abs]
  apply (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
  constructor
  · intro j
    simp_rw [habs]
    exact (error_summable (orbit_pos hn j)).mul_left _
  · let D := C*(n:ℝ)^2
    have hgeo := (summable_geometric_of_lt_one (mul_nonneg hr (by norm_num : (0:ℝ) ≤ 4)) hr₄).mul_right D
    apply Summable.of_nonneg_of_le (fun j => tsum_nonneg fun k => abs_nonneg _) _ hgeo
    intro j
    simp_rw [habs]
    rw [tsum_mul_left]
    refine (mul_le_mul_of_nonneg_left (hE (orbit_pos hn j)) (hf j)).trans_eq ?_
    dsimp only [orbit,D]
    push_cast
    rw [mul_pow,← pow_mul,Nat.mul_comm j 2,pow_mul]
    calc _ = (r^j*((2:ℝ)^2)^j)*(C*(n:ℝ)^2) := by ring
      _ = _ := by rw [← mul_pow]; norm_num

private theorem summable_remainder {n : ℕ} (hn : 0 < n) : Summable (remainder n) :=
  summable_geometricError hn (by norm_num : (0:ℝ) ≤ 1/8) (by norm_num)

private theorem tail_eventually_zero {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ∀ᶠ j : ℕ in atTop, tail n j k=0 := by
  have ht := Real.tendsto_log_atTop.comp ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp
    (tendsto_natCast_atTop_atTop.comp (orbit_infty hn)))
  filter_upwards [ht.eventually_gt_atTop (Real.log k+8)] with j hj
  change Real.log k+8 < Real.log ((orbit n j:ℝ)^2) at hj
  have hz := splineAutoCorr_zero_outside (x := Real.log k-Real.log ((orbit n j:ℝ)^2))
    (by linarith only [hj,neg_abs_le (Real.log k-Real.log ((orbit n j:ℝ)^2))])
  simp [tail,squarePrimeEndpoint,hz]

private theorem orbit_column_sum {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (∑' j, row n j k)=squarePrimeEndpoint n k+∑' j, remainder n (j,k) := by
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (tail_eventually_zero hn k)
  have ht : Summable (fun j => tail n j k) := summable_of_ne_finset_zero (s := range J)
    fun j hj => hJ j (le_of_not_gt (fun hh => hj (mem_range.mpr hh)))
  have ht' : Summable (fun j => tail n (j+1) k) := summable_of_ne_finset_zero (s := range J)
    fun j hj => hJ _ (by have := not_lt.mp (mt mem_range.mpr hj); omega)
  have hR := (summable_remainder hn).prod_symm.prod_factor k
  simp_rw [row_split]
  rw [(ht.sub ht').tsum_add hR,ht.tsum_sub ht']
  have hs := ht.tsum_eq_zero_add
  change (∑' j, tail n j k)=tail n 0 k+∑' j, tail n (j+1) k at hs
  rw [hs]
  simp [tail,factor,orbit]

private theorem tail_mass_limit {n : ℕ} (hn : 0 < n) :
    Tendsto (fun j => ∑' k, tail n j k) atTop (𝓝 (4*(n:ℝ)^3*squareAutocorrelationMass)) := by
  have h := (tendsto_squarePrimeEndpoint_mass.comp (orbit_infty hn)).const_mul ((n:ℝ)^3)
  rw [show (n:ℝ)^3*(4*squareAutocorrelationMass)=4*(n:ℝ)^3*squareAutocorrelationMass by ring] at h
  apply h.congr fun j => ?_
  simp only [tail,tsum_mul_left]
  change (n:ℝ)^3*((∑' k, squarePrimeEndpoint (orbit n j) k)/(orbit n j:ℝ)^3)=_
  have he : (orbit n j:ℝ)^3=(8:ℝ)^j*(n:ℝ)^3 := by
    simp only [orbit,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_pow,← pow_mul]
    rw [Nat.mul_comm j 3,pow_mul]
    norm_num
  have hn' : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [he]
  dsimp only [factor]
  rw [one_div,inv_pow]
  field_simp

/-- Summing first along each fixed prime and then over the primes exceeds
the limit in conductor order by exactly four times the positive cubic mass. -/
theorem dyadic_square_prime_mass_escape {n : ℕ} (hn : 0 < n) :
    Tendsto (fun K : ℕ =>
      (∑' p : ℕ, ∑' j : ℕ, (1/8:ℝ)^j*
        (deningerRatExp (ordinaryPrimeGenerator ((2^j*n) • successorSquareTriple (2^j*n))) p:ℝ)*
        (if p.Prime then Real.log p else 0)) -
      ∑ j ∈ range K, (1/8:ℝ)^j*Real.log
        (ordinaryPrimeGenerator ((2^j*n) • successorSquareTriple (2^j*n)):ℝ))
      atTop (𝓝 (4*(n:ℝ)^3*squareAutocorrelationMass)) := by
  have hR := summable_remainder hn
  have hcols : (∑' p, ∑' j, row n j p)=(∑' p, squarePrimeEndpoint n p)+∑' j, ∑' p, remainder n (j,p) := by
    simp_rw [orbit_column_sum hn]
    rw [(endpoint_summable hn).tsum_add hR.prod_symm.prod,hR.tsum_comm]
  have hsum (j : ℕ) : factor j*Real.log (q (orbit n j):ℝ)=
      (∑' p, tail n j p)-(∑' p, tail n (j+1) p)+∑' p, remainder n (j,p) := by
    rw [← price_sum _ (orbit_pos hn _),← tsum_mul_left]
    change (∑' p, row n j p)=_
    have ht (i : ℕ) : Summable (tail n i) := (endpoint_summable (orbit_pos hn i)).mul_left _
    simp_rw [row_split]
    rw [((ht j).sub (ht (j+1))).tsum_add (hR.prod_factor j),(ht j).tsum_sub (ht (j+1))]
  have hRlim := hR.prod.hasSum.tendsto_sum_nat
  have h := (tail_mass_limit hn).add ((tendsto_const_nhds
    (x := ∑' j, ∑' p, remainder n (j,p))).sub hRlim)
  rw [sub_self,add_zero] at h
  apply h.congr fun K => ?_
  simp only [mul_assoc]
  change _ = (∑' p, ∑' j, row n j p)-∑ j ∈ range K, factor j*Real.log (q (orbit n j):ℝ)
  simp_rw [hsum]
  rw [hcols,sum_add_distrib,sum_range_sub']
  simp only [tail,factor,orbit,pow_zero,one_mul]
  ring

/-- The two-index family of actual logarithmic valuations cannot be
summed unconditionally. Its failure at weight one eighth occurs on every
positive dyadic orbit, including orbits with bounded signed prices. -/
theorem not_summable_dyadic_square_log_valuations {n : ℕ} (hn : 0 < n) :
    ¬ Summable (fun i : ℕ × ℕ => (1/8:ℝ)^i.1 *
      ((deningerRatExp (ordinaryPrimeGenerator ((2^i.1*n) • successorSquareTriple (2^i.1*n))) i.2:ℝ)*
        (if i.2.Prime then Real.log i.2 else 0))) := by
  intro h
  change Summable (Function.uncurry (row n)) at h
  have hprice (j : ℕ) : (∑' p, row n j p)=factor j*Real.log (q (orbit n j):ℝ) := by
    simp only [row,tsum_mul_left,price_sum _ (orbit_pos hn j)]
  have hzero := ((tendsto_const_nhds (x := ∑' j, ∑' p, row n j p)).sub h.prod.hasSum.tendsto_sum_nat)
  rw [sub_self] at hzero
  have he := dyadic_square_prime_mass_escape hn
  simp only [mul_assoc] at he
  change Tendsto (fun K => (∑' p, ∑' j, row n j p)-
    ∑ j ∈ range K, factor j*Real.log (q (orbit n j):ℝ)) atTop _ at he
  simp_rw [← hprice] at he
  rw [h.tsum_comm] at he
  have hp : 0 < 4*(n:ℝ)^3*squareAutocorrelationMass :=
    mul_pos (mul_pos (by norm_num) (pow_pos (Nat.cast_pos.mpr hn) 3)) squareAutocorrelationMass_pos
  exact hp.ne' (tendsto_nhds_unique he hzero)

private theorem abs_row_sum {n : ℕ} (hn : 0 < n) :
    (∑' k, |price n k|)=Real.log (q n).num.natAbs+Real.log (q n).den := by
  rw [tsum_eq_sum (s := S n) (fun k hk => by rw [(endpoint_zero hn hk).1,abs_zero]),
    ← ordinary_absolute_prime_mass (n • successorSquareTriple n)]
  refine sum_congr rfl fun k hk => ?_
  have hp := (mem_filter.mp hk).2
  rw [price,abs_mul,weight,if_pos hp,abs_of_nonneg (Real.log_natCast_nonneg k),vonMangoldt_apply_prime hp]

/-- One eighth is exactly the radius of absolute convergence of the
prime-by-prime dyadic series, on every positive starting conductor. -/
theorem summable_dyadic_square_log_valuations_iff {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun i : ℕ × ℕ => r^i.1*((deningerRatExp (q (orbit n i.1)) i.2:ℝ)*weight i.2)) ↔ r < 1/8 := by
  change Summable (fun i : ℕ × ℕ => r^i.1*price (orbit n i.1) i.2) ↔ _
  constructor
  · intro h
    by_contra he
    apply not_summable_dyadic_square_log_valuations hn
    apply Summable.of_abs
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun i => ?_) h.abs
    change |(1/8:ℝ)^i.1*price (orbit n i.1) i.2| ≤ |r^i.1*price (orbit n i.1) i.2|
    rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/8) _),abs_of_nonneg (pow_nonneg hr _)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (le_of_not_gt he) _) (abs_nonneg _)
  · intro hsmall
    obtain ⟨B,hB,hsize⟩ := successorSquare_products_upper
    have hgeo := (summable_geometric_of_lt_one (mul_nonneg hr (by norm_num : (0:ℝ) ≤ 8))
      (show r*8 < 1 by linarith only [hsmall])).mul_right (3*B*(n:ℝ)^3)
    apply Summable.of_abs
    simp only [abs_mul,abs_of_nonneg (pow_nonneg hr _)]
    apply (summable_prod_of_nonneg (fun i => mul_nonneg (pow_nonneg hr i.1) (abs_nonneg _))).mpr
    constructor
    · intro j
      exact (summable_of_ne_finset_zero (s := S (orbit n j)) (fun k hk => by
        rw [(endpoint_zero (orbit_pos hn j) hk).1,abs_zero])).mul_left _
    · refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun k => mul_nonneg (pow_nonneg hr j) (abs_nonneg _))
        (fun j => ?_) hgeo
      let m := orbit n j
      have hm : 0 < m := orbit_pos hn j
      have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
      obtain ⟨hu,hv⟩ := hsize (m := m) hm
      have hsub := mul_le_mul_of_nonneg_right hm' (sq_nonneg (m:ℝ))
      have htot : Real.log (q m).num.natAbs+Real.log (q m).den ≤ 3*B*(m:ℝ)^3 := by
        change Real.log (q m).num.natAbs ≤ B*m*(m:ℝ)^2 at hu
        change Real.log (q m).den ≤ B*((m:ℝ)*(m:ℝ)^2+m^2) at hv
        linarith only [hu,hv,mul_le_mul_of_nonneg_left hsub hB]
      rw [tsum_mul_left,abs_row_sum (orbit_pos hn j)]
      refine (mul_le_mul_of_nonneg_left htot (pow_nonneg hr j)).trans_eq ?_
      dsimp only [m,orbit]
      push_cast
      rw [mul_pow (2:ℝ)^j,← pow_mul,Nat.mul_comm j 3,pow_mul]
      change r^j*(3*B*(8^j*(n:ℝ)^3))=_
      rw [mul_pow r 8 j]; ring

private theorem endpoint_nonneg (n k : ℕ) : 0 ≤ squarePrimeEndpoint n k := by
  have hw : 0 ≤ weight k := by
    unfold weight; split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl
  exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.sqrt_nonneg _))
    (splineAutoCorr_nonneg _)) hw

/-- Product of the first K prices on a doubling orbit with integer powers
eight to the remaining depth. -/
def dyadicSquareProduct (n : ℕ) : ℕ → ℚ
  | 0 => 1
  | K+1 => dyadicSquareProduct n K ^ 8 * q (2^K*n)

private theorem orbit_price_pos (n : ℕ) : 0 < q n := by
  unfold q ordinaryPrimeGenerator
  exact prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k) : (0:ℚ) < _) _

private theorem dyadic_product_pos (n K : ℕ) : 0 < dyadicSquareProduct n K := by
  induction K with
  | zero => exact zero_lt_one
  | succ K ih => exact mul_pos (pow_pos ih 8) (orbit_price_pos _)

private theorem dyadic_product_row (n K k : ℕ) :
    8*factor K*(deningerRatExp (dyadicSquareProduct n K) k:ℝ)*weight k =
      ∑ j ∈ range K, row n j k := by
  induction K with
  | zero => simp [dyadicSquareProduct]
  | succ K ih =>
    rw [Finset.sum_range_succ,← ih,dyadicSquareProduct,deningerRatExp_mul
      (pow_ne_zero 8 (dyadic_product_pos _ _).ne') (orbit_price_pos _).ne',deningerRatExp_pow (dyadic_product_pos _ _).ne']
    simp only [Finsupp.add_apply,Finsupp.smul_apply,nsmul_eq_mul,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
    dsimp only [factor,row,price,orbit]
    rw [pow_succ]; ring

private theorem finite_dyadic_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    ∀ (P : Finset ℕ) (K : ℕ), (∑ k ∈ P, |∑ j ∈ range K, remainder n (j,k)|) ≤ 2*C*(n:ℝ)^2 := by
  obtain ⟨C,hC,hE⟩ := error_budget
  refine ⟨C,hC,fun {n} hn P K => ?_⟩
  let D := C*(n:ℝ)^2
  have hd : 0 ≤ D := mul_nonneg hC (sq_nonneg _)
  have hgeo := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)).mul_right D
  calc _ ≤ ∑ k ∈ P, ∑ j ∈ range K, |remainder n (j,k)| :=
            sum_le_sum fun k _ => abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ range K, ∑ k ∈ P, |remainder n (j,k)| := sum_comm
    _ ≤ ∑ j ∈ range K, (1/2:ℝ)^j*D := sum_le_sum fun j _ => by
      have hfac : 0 ≤ factor j := pow_nonneg (by norm_num) _
      simp only [remainder,abs_mul,abs_of_nonneg hfac,← mul_sum]
      have hsum := (error_summable (orbit_pos hn j)).sum_le_tsum P (fun _ _ => abs_nonneg _)
      refine (mul_le_mul_of_nonneg_left (hsum.trans (hE (orbit_pos hn j))) hfac).trans_eq ?_
      dsimp only [orbit,factor,D]
      push_cast
      rw [mul_pow,← pow_mul,Nat.mul_comm j 2,pow_mul]
      calc _ = ((1/8:ℝ)^j*(2^2:ℝ)^j)*(C*(n:ℝ)^2) := by ring
        _ = _ := by rw [← mul_pow]; norm_num
    _ ≤ _ := (hgeo.summable.sum_le_tsum _ (fun j _ => mul_nonneg (pow_nonneg (by norm_num) _) hd)).trans_eq
      (by rw [hgeo.tsum_eq]; dsimp only [D]; ring)

/-- The limiting log price on a dyadic orbit differs from its centered
positive prime mass by a uniform quadratic allowance. -/
theorem dyadic_square_log_centered_endpoint : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    ∃ L : ℝ, Tendsto (fun K => ∑ j ∈ range K, (1/8:ℝ)^j*Real.log (q (2^j*n):ℝ)) atTop (𝓝 L) ∧
      |L-((∑' k, squarePrimeEndpoint n k)-4*(n:ℝ)^3*squareAutocorrelationMass)| ≤ 2*C*(n:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := finite_dyadic_error
  refine ⟨C,hC,fun {n} hn => ?_⟩
  let R := fun k : ℕ => ∑' j, remainder n (j,k)
  let A := ∑' k, squarePrimeEndpoint n k
  let D := 4*(n:ℝ)^3*squareAutocorrelationMass
  have hR := (summable_remainder hn).prod_symm
  have hbound (P : Finset ℕ) : |∑ k ∈ P, R k| ≤ 2*C*(n:ℝ)^2 := by
    have ht := tendsto_finset_sum P (fun k _ => (hR.prod_factor k).hasSum.tendsto_sum_nat)
    exact le_of_tendsto' ht.abs (fun K => (abs_sum_le_sum_abs _ _).trans (h hn P K))
  have hb : |∑' k, R k| ≤ 2*C*(n:ℝ)^2 := le_of_tendsto' hR.prod.hasSum.abs hbound
  have hcols : (∑' k, ∑' j, row n j k) = A + ∑' k, R k := by
    simp_rw [orbit_column_sum hn]
    exact (endpoint_summable hn).tsum_add hR.prod
  have ht := dyadic_square_prime_mass_escape hn
  change Tendsto (fun K => (∑' k, ∑' j, row n j k) -
    ∑ j ∈ range K, (1/8:ℝ)^j*Real.log (q (2^j*n):ℝ)) atTop (𝓝 D) at ht
  rw [hcols] at ht
  refine ⟨(A+∑' k, R k)-D,?_,?_⟩
  · exact ((tendsto_const_nhds (x := A+∑' k, R k)).sub ht).congr (fun _ => by ring)
  · change |(A+∑' k, R k)-D-(A-D)| ≤ _
    rwa [show (A+∑' k, R k)-D-(A-D) = ∑' k, R k by ring]

/-- The two endpoint profiles recover the normalized integer product up
to a uniform quadratic error in total absolute logarithmic weight. -/
theorem dyadic_square_product_endpoints : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    ∀ (P : Finset ℕ) (K : ℕ),
      ∑ k ∈ P, |8*(1/8:ℝ)^K*(deningerRatExp (dyadicSquareProduct n K) k:ℝ)*weight k -
        (squarePrimeEndpoint n k - (1/8:ℝ)^K*squarePrimeEndpoint (2^K*n) k)| ≤ 2*C*(n:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := finite_dyadic_error
  refine ⟨C,hC,fun {n} hn P K => ?_⟩
  refine le_trans (le_of_eq (sum_congr rfl fun k _ => ?_)) (h hn P K)
  rw [← show factor K=(1/8:ℝ)^K from rfl,dyadic_product_row]
  simp_rw [row_split]
  rw [sum_add_distrib,sum_range_sub']
  simp [tail,factor,orbit]

/-- Once the two support intervals are disjoint, the positive and negative
parts of the product recover the two endpoint masses separately. -/
theorem dyadic_square_product_separated_endpoints : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    ∀ (P : Finset ℕ) (K : ℕ), 16 < 2*K*Real.log 2 →
    let v := fun k => 8*(1/8:ℝ)^K*(deningerRatExp (dyadicSquareProduct n K) k:ℝ)*weight k
    (∑ k ∈ P, |max (v k) 0 - squarePrimeEndpoint n k|) ≤ 2*C*(n:ℝ)^2 ∧
    (∑ k ∈ P, |max (-v k) 0 - (1/8:ℝ)^K*squarePrimeEndpoint (2^K*n) k|) ≤ 2*C*(n:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := dyadic_square_product_endpoints
  refine ⟨C,hC,fun {n} hn P K hK => ?_⟩
  let x := squarePrimeEndpoint n
  let y := fun k => (1/8:ℝ)^K*squarePrimeEndpoint (2^K*n) k
  have hzero (k : ℕ) : x k = 0 ∨ y k = 0 := by
    let t := Real.log k-Real.log ((n:ℝ)^2)
    by_cases ht : 8 < |t|
    · left; change 4*(n:ℝ)^2/Real.sqrt k*splineAutoCorr t*weight k=0
      rw [splineAutoCorr_zero_outside ht,mul_zero,zero_mul]
    · right
      have hl : Real.log (((2^K*n:ℕ):ℝ)^2) = 2*K*Real.log 2 + Real.log ((n:ℝ)^2) := by
        rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_pow,Real.log_mul
          (by positivity) (sq_pos_of_pos (Nat.cast_pos.mpr hn)).ne',Real.log_pow,Real.log_pow]
        push_cast; ring
      have hz : 8 < |Real.log k-Real.log (((2^K*n:ℕ):ℝ)^2)| := by
        rw [hl]
        have ht' := (le_abs_self t).trans (le_of_not_gt ht)
        dsimp only [t] at ht'
        linarith only [ht',hK,neg_abs_le (Real.log k-(2*K*Real.log 2+Real.log ((n:ℝ)^2)))]
      simp [y,squarePrimeEndpoint,splineAutoCorr_zero_outside hz]
  have hj (k : ℕ) : max (x k-y k) 0 = x k ∧ max (-(x k-y k)) 0 = y k := by
    have hx : 0 ≤ x k := endpoint_nonneg _ _
    have hy : 0 ≤ y k := mul_nonneg (pow_nonneg (by norm_num) _) (endpoint_nonneg _ _)
    rcases hzero k with hz | hz <;> simp [hz,max_eq_left hx,max_eq_left hy,
      max_eq_right (neg_nonpos.mpr hx),max_eq_right (neg_nonpos.mpr hy)]
  constructor
  · refine (sum_le_sum fun k _ => ?_).trans (h hn P K)
    rw [← (hj k).1]
    exact abs_max_sub_max_le_abs _ _ _
  · refine (sum_le_sum fun k _ => ?_).trans (h hn P K)
    rw [← (hj k).2]
    exact (abs_max_sub_max_le_abs _ _ _).trans_eq (by rw [neg_sub_neg,abs_sub_comm])

private theorem endpoint_column_finite {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ∀ᶠ j : ℕ in atTop, squarePrimeEndpoint (orbit n j) k = 0 := by
  filter_upwards [tail_eventually_zero hn k] with j hj
  exact (mul_eq_zero.mp hj).resolve_left (pow_ne_zero j (by norm_num : (1/8:ℝ) ≠ 0))

/-- Above one eighth, the actual sum in prime order tends to positive
infinity as long as the accumulated quadratic row error is summable. -/
theorem dyadic_square_supercritical_prime_order {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 1/8 < r) (hr₄ : r*4 < 1) :
    Tendsto (fun K : ℕ => ∑ k ∈ range K, ∑' j : ℕ, r^j *
      ((deningerRatExp (q (2^j*n)) k : ℝ)*weight k)) atTop atTop := by
  have hr₀ : 0 ≤ r := le_trans (by norm_num) hr.le
  let B := fun j k => squarePrimeEndpoint (orbit n j) k
  let Q := fun i : ℕ × ℕ => r^i.1 * B (i.1+1) i.2
  let E := geometricError n r
  have hE : Summable E := summable_geometricError hn hr₀ hr₄
  have hQ₀ (i : ℕ × ℕ) : 0 ≤ Q i := mul_nonneg (pow_nonneg hr₀ _) (endpoint_nonneg _ _)
  have hBsum (k d : ℕ) : Summable (fun j : ℕ => r^j * B (j+d) k) := by
    obtain ⟨J,hJ⟩ := eventually_atTop.mp (endpoint_column_finite hn k)
    exact summable_of_ne_finset_zero (s := range J) fun j hj => by
      have h : J ≤ j := not_lt.mp (mt mem_range.mpr hj)
      rw [show B (j+d) k=0 from hJ _ (by omega),mul_zero]
  have hcolumn (k : ℕ) : (∑' j : ℕ, r^j * price (orbit n j) k) =
      (r-1/8)*(∑' j : ℕ, Q (j,k)) + (squarePrimeEndpoint n k + ∑' j : ℕ, E (j,k)) := by
    let A := fun j : ℕ => r^j * B j k
    have hA : Summable A := by simpa only [Nat.add_zero] using hBsum k 0
    have hQ : Summable (fun j => Q (j,k)) := hBsum k 1
    have he (j : ℕ) : r^j*price (orbit n j) k = A j-(1/8)*Q (j,k)+E (j,k) := by
      dsimp only [A,Q,E,B,geometricError,err,orbit]
      rw [show 2^(j+1)*n=2*(2^j*n) by ring]
      ring
    simp_rw [he]
    rw [(hA.sub (hQ.mul_left _)).tsum_add (hE.prod_symm.prod_factor k),hA.tsum_sub (hQ.mul_left _),
      tsum_mul_left,hA.tsum_eq_zero_add]
    have htail : ∀ j, A (j+1)=r*Q (j,k) := fun j => by dsimp only [A,Q]; rw [pow_succ]; ring
    simp_rw [htail]
    rw [tsum_mul_left]
    simp only [A,B,orbit,pow_zero,one_mul]
    ring
  have hbad : ¬Summable (fun k : ℕ => ∑' j : ℕ, Q (j,k)) := by
    intro ha
    have hdouble : Summable (fun i : ℕ × ℕ => Q (i.2,i.1)) :=
      (summable_prod_of_nonneg (fun i => hQ₀ (i.2,i.1))).mpr ⟨fun k => hBsum k 1,ha⟩
    have hrows : Tendsto (fun j : ℕ => ∑' k, Q (j,k)) atTop (𝓝 0) := hdouble.prod_symm.prod.tendsto_atTop_zero
    have htail : Tendsto (fun j : ℕ => ∑' k, tail n (j+1) k) atTop (𝓝 0) := by
      refine squeeze_zero (fun j => tsum_nonneg fun k => mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/8) _) (endpoint_nonneg _ _)) (fun j => ?_) hrows
      simp only [tail,factor,Q,B,tsum_mul_left]
      have he : (1/8:ℝ)^(j+1) ≤ r^j  := calc
        (1/8:ℝ)^(j+1) = (1/8:ℝ)^j*(1/8) := pow_succ _ _
        _ ≤ (1/8:ℝ)^j := mul_le_of_le_one_right (by positivity) (by norm_num)
        _ ≤ r^j := pow_le_pow_left₀ (by norm_num) hr.le _
      exact mul_le_mul_of_nonneg_right he (tsum_nonneg fun k => endpoint_nonneg _ k)
    have hlim := (tail_mass_limit hn).comp (tendsto_add_atTop_nat 1)
    have hpos : 0 < 4*(n:ℝ)^3*squareAutocorrelationMass := by
      exact mul_pos (mul_pos (by norm_num) (pow_pos (Nat.cast_pos.mpr hn) _)) squareAutocorrelationMass_pos
    exact hpos.ne (tendsto_nhds_unique htail hlim)
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k => tsum_nonneg fun j => hQ₀ (j,k))).mp hbad
  have hrest := ((endpoint_summable hn).add hE.prod_symm.prod).hasSum.tendsto_sum_nat
  have hmain := hdiv.const_mul_atTop (sub_pos.mpr hr)
  have h := hmain.atTop_add hrest
  refine h.congr fun K => ?_
  change (r-1/8)*(∑ k ∈ range K, ∑' j, Q (j,k))+
    (∑ k ∈ range K, (squarePrimeEndpoint n k + ∑' j, E (j,k)))=_
  rw [mul_sum,← sum_add_distrib]
  exact sum_congr rfl fun k _ => (hcolumn k).symm

/-- In conductor order the signed price is absolutely summable below
the threshold determined by the zero width. -/
theorem dyadic_square_conductor_order {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r)
    (hwidth : r*2^(2+2*SquareRootThreshold.zetaZeroWidth:ℝ) < 1) :
    Summable (fun j : ℕ => r^j*Real.log (q (2^j*n):ℝ)) := by
  obtain ⟨C,hC,h⟩ := successorSquare_diagonal_log_at_width
  let b := 2*SquareRootThreshold.zetaZeroWidth
  have hb : 0 ≤ b := mul_nonneg two_pos.le SquareRootThreshold.zetaZeroWidth_nonneg
  let A := C*(n:ℝ)^2*(2*(n:ℝ))^b
  have hgeo := (summable_geometric_of_lt_one (mul_nonneg hr (Real.rpow_nonneg (by norm_num) _)) hwidth).mul_right A
  apply Summable.of_norm_bounded hgeo
  intro j
  let m := orbit n j
  have hm := orbit_pos hn j
  have hm₁ : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (m:ℝ)+1) (by linarith only [hm₁] : (m:ℝ)+1 ≤ 2*m) hb
  have hbound := (h m hm).trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hC (sq_nonneg _)))
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hr _)]
  refine (mul_le_mul_of_nonneg_left hbound (pow_nonneg hr j)).trans_eq ?_
  dsimp only [m,orbit,A]
  push_cast
  rw [show 2*((2:ℝ)^j*n)=2^j*(2*n) by ring,Real.mul_rpow (by positivity) (by positivity),
    mul_pow (2:ℝ)^j,← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    show (j:ℝ)*b=b*j by ring,Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,
    Real.rpow_add (by norm_num : (0:ℝ) < 2),Real.rpow_two,mul_pow r,mul_pow (2^2:ℝ)]
  ring

end GaloisForLFunctions.CountingHolography.Sections
