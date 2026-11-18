import GaloisForLFunctions.ExceptionalLayerTheory.DiscreteFirstMeansContinueTheirDirichletSeries
import GaloisForLFunctions.ExceptionalLayerTheory.TheIntegerDensityOfTheLastQuotientClass
import GaloisForLFunctions.ExceptionalLayerTheory.RightZerosObstructPowerBoundsForBinomialGcds
import GaloisForLFunctions.HTGeometry.RpowPartialSumBound

/-!
# First means of the dyadic binomial gcds and the zeta zeros

Triangular averaging preserves the pole at each detected zero. Integer
sampling changes its cumulative sum by at most a constant times the
three-halves power, and the integer reference has an explicit density.
-/

noncomputable section

open Finset Filter Topology Complex ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

private def primeTotal (q : ℕ) (A : ℝ) (X : ℕ) : ℝ :=
  ∑ k ∈ range X, (lastClassPrimeMass q k-A*k)

/-- Cumulative deviation of the logarithms of the dyadic binomial gcds. -/
def binomialGcdFirstTotal (j : ℕ) (A : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (Real.log (dyadicBinomialGcd j n)-A*(2^(j+1)*n:ℕ))

private theorem triangular_count_identity (c : ℕ → ℝ) (N : ℕ) :
    (N:ℝ)*triangularPrimeProfile c (N:ℝ)⁻¹ = ∑ k ∈ range N, ∑ d ∈ Icc 1 k, c d := by
  rcases Nat.eq_zero_or_pos N with rfl | hn
  · simp
  have hp : 0<(N:ℝ) := by exact_mod_cast hn
  have hcut : 1 ≤ ((N:ℝ)+1)*(N:ℝ)⁻¹ := by
    rw [add_mul,mul_inv_cancel₀ hp.ne',one_mul]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hp.le)
  rw [triangularPrimeProfile_eq_sum c (inv_nonneg.mpr hp.le) N hcut,mul_sum,
    ← triangular_weighted_sum_eq_sum_prefix,← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine sum_congr rfl fun n hn' => ?_
  have hle : (n:ℝ)+1 ≤ N := by exact_mod_cast mem_range.mp hn'
  have hh := mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hp.le)
  rw [mul_inv_cancel₀ hp.ne'] at hh
  rw [max_eq_left (sub_nonneg.mpr hh),add_comm 1 n,Nat.cast_add,Nat.cast_one]
  field_simp

private theorem zero_of_primeTotal_bound (q : ℕ) [NeZero q] (hq : 2≤q)
    {b A C : ℝ} (hb : 0≤b) (hb1 : b<1) (hC : 0≤C)
    (h : ∀ N : ℕ, 1≤N → |primeTotal q A N| ≤ C*(N:ℝ)^(b+1))
    {ρ : ℂ} (hρ : b<ρ.re) (hz : riemannZeta ρ=0) : lastQuotientClassSymbol q ρ=0 := by
  let c := fun n : ℕ => lastClassPrimeCoeff q n-A
  have hprofile (N : ℕ) (hn : 1≤N) :
      |triangularPrimeProfile c (N:ℝ)⁻¹| ≤ C*(N:ℝ)^b := by
    have hp : 0<(N:ℝ) := by exact_mod_cast hn
    have he : (N:ℝ)*triangularPrimeProfile c (N:ℝ)⁻¹ = primeTotal q A N := by
      rw [triangular_count_identity,primeTotal]
      refine sum_congr rfl fun k _ => ?_
      simp only [c,sum_sub_distrib,← lastClassPrimeMass_eq_prefix q hq,sum_const,nsmul_eq_mul,
        Nat.card_Icc,Nat.add_sub_cancel,mul_comm A]
    have hh := h N hn
    rw [← he,abs_mul,abs_of_pos hp,Real.rpow_add_one hp.ne'] at hh
    exact le_of_mul_le_mul_left (hh.trans_eq (by ring)) hp
  apply lastQuotientClassSymbol_vanishes_of_continuation q (A := A) hb1 (triangularDirichletContinuation c)
    (fun _ hs => (differentiableAt_triangularDirichletContinuation c hC hb hprofile hs).differentiableWithinAt) _ hρ hz
  intro s hs
  have hs1 : 1<s.re := by linarith only [hs]
  have hcoeff (n : ℕ) : |c (n+1)| ≤ (1 + |A|)*((n:ℝ)+1)^(1:ℝ) := by
    have hlog := (abs_lastClassPrimeCoeff_le q (n+1)).trans (Real.log_le_self (by positivity))
    have hn : 1≤(n:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have ha := le_mul_of_one_le_right (abs_nonneg A) hn
    rw [Real.rpow_one]
    change |lastClassPrimeCoeff q (n+1)-A| ≤ _
    apply (abs_sub _ _).trans
    push_cast at hlog
    linarith only [ha,hlog]
  rw [triangularDirichletContinuation_eq_series c hcoeff (by linarith only [hs]) (by linarith only [hs])]
  obtain ⟨hf,he⟩ := lastClassPrimeCoeff_series q hs1
  let f := fun n : ℕ => (lastClassPrimeCoeff q n : ℂ)
  have hterm (n : ℕ) : LSeries.term (f-(A:ℂ) • (1:ℕ→ℂ)) s (n+1) =
      (c (n+1):ℂ)*((n:ℂ)+1)^(-s) := by
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),Complex.cpow_neg,div_eq_mul_inv]
    simp [c,f]
  have ha := (LSeriesSummable_one_iff.mpr hs1).smul (A:ℂ)
  calc
    _ = LSeries (f-(A:ℂ) • (1:ℕ→ℂ)) s := by
      rw [LSeries_sub hf ha,LSeries_smul,LSeries_one_eq_riemannZeta hs1,← he]
    _ = _ := by
      have hsum := (hf.sub ha).hasSum
      have hs' := (hasSum_nat_add_iff' 1).mpr hsum
      simp only [sum_range_one,LSeries.term_zero,sub_zero] at hs'
      exact hs'.tsum_eq.symm.trans (tsum_congr hterm)


private theorem repeated_sample_sum (f : ℕ → ℝ) {q : ℕ} (hq : 0<q) (N : ℕ) :
    ∑ k ∈ range (q*N), f (k/q) = q*∑ n ∈ range N, f n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ,sum_range_add,ih,Finset.sum_range_succ f N,mul_add]
    apply congrArg (fun x : ℝ => (q:ℝ)*(∑ n ∈ range N, f n)+x)
    calc
      _ = ∑ _r ∈ range q, f N := by
        refine sum_congr rfl fun r hr => ?_
        rw [Nat.mul_add_div hq,Nat.div_eq_of_lt (mem_range.mp hr),add_zero]
      _ = _ := by simp

private theorem abs_primeMass_le_linear (q k : ℕ) :
    |lastClassPrimeMass q k| ≤ (Real.log 4+4)*k := by
  have h₁ : 0≤lastClassPrimeMass q k := by
    apply sum_nonneg
    intro m _
    change 0≤vonMangoldt m*(if q∣k/m+1 then (1:ℝ) else 0)
    split <;> positivity
  rw [abs_of_nonneg h₁]
  apply le_trans _ (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg k))
  rw [Chebyshev.psi,Nat.floor_natCast]
  change (∑ m ∈ Icc 1 k, vonMangoldt m*(if q∣k/m+1 then (1:ℝ) else 0)) ≤ ∑ m ∈ Icc 1 k, vonMangoldt m
  refine sum_le_sum fun m _ => ?_
  split <;> simp [vonMangoldt_nonneg]

private theorem sampled_total_comparison (j : ℕ) (A : ℝ) :
    ∃ K : ℝ, 0≤K ∧ ∀ X : ℕ, 1≤X →
      let q := 2^(j+1)
      |primeTotal q A X - q*binomialGcdFirstTotal j A (X/q)| ≤ K*(X:ℝ)*Real.sqrt X := by
  let q := 2^(j+1)
  have hq : 2≤q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
  have hq0 : 0<q := by omega
  obtain ⟨C,hC⟩ := exists_uniform_dyadicBinomialGcd_log_error
  let J := 2*(q:ℝ) + |C| + |A| * q
  let H := Real.log 4+4 + |A|
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hJ : 0≤J := by dsimp only [J]; positivity
  have hH : 0≤H := by dsimp only [H]; positivity
  refine ⟨J+q*H,by positivity,fun X hX => ?_⟩
  let Y := q*(X/q)
  let f := fun k : ℕ => lastClassPrimeMass q k-A*k
  let g := fun n : ℕ => Real.log (dyadicBinomialGcd j n)-A*(q*n:ℕ)
  have hXY : Y≤X := Nat.mul_div_le X q
  have gap (k : ℕ) : k-q*(k/q) ≤ q := by
    have := Nat.mod_add_div k q; have := Nat.mod_lt k hq0; omega
  have hx : 1≤(X:ℝ) := by exact_mod_cast hX
  have hroot : 1≤Real.sqrt X := Real.one_le_sqrt.mpr hx
  have hlogX : Real.log ((X:ℝ)+1) ≤ 2*Real.sqrt X := calc
    _ ≤ Real.sqrt ((X:ℝ)+1) := _root_.RHTower.log_le_sqrt (by positivity)
    _ ≤ Real.sqrt (4*(X:ℝ)) := Real.sqrt_le_sqrt (by linarith only [hx])
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
  have hcell (k : ℕ) (hk : k≤X) : |f k-g (k/q)| ≤ J*Real.sqrt X := by
    let z := q*(k/q)
    have hz : z≤k := Nat.mul_div_le k q
    have hθ := lastClassPrimeMass_cutoff_gap hq hz
    have hd : |lastClassPrimeMass q k-lastClassPrimeMass q z| ≤ (q:ℝ)*(2*Real.sqrt X) := by
      apply hθ.trans
      exact mul_le_mul (by exact_mod_cast gap k)
        ((Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)).trans hlogX)
        (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg k))) (Nat.cast_nonneg q)
    have hg : |lastClassPrimeMass q z-Real.log (dyadicBinomialGcd j (k/q))| ≤ |C| * Real.sqrt X := by
      change |lastClassPrimeMass (2^(j+1)) (2^(j+1)*(k/q)) - _| ≤ _
      rw [abs_sub_comm,lastClassPrimeMass_at_dyadic]
      exact (hC j (k/q)).trans (mul_le_mul (le_abs_self _) (Real.sqrt_le_sqrt
        (by exact_mod_cast hz.trans hk : (z:ℝ)≤X)) (Real.sqrt_nonneg _) (abs_nonneg _))
    have hlin : |A*((k:ℝ)-z)| ≤ (|A| * q)*Real.sqrt X := by
      rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hz))]
      have he : (k:ℝ)-z ≤ q := by
        rw [← Nat.cast_sub hz]
        exact_mod_cast gap k
      exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans
        (le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) hroot)
    have he : f k-g (k/q) = (lastClassPrimeMass q k-lastClassPrimeMass q z)+
        (lastClassPrimeMass q z-Real.log (dyadicBinomialGcd j (k/q)))-A*((k:ℝ)-z) := by
      dsimp only [f,g,z]; ring
    rw [he]
    refine (abs_sub _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hd hg)) hlin).trans_eq ?_)
    dsimp only [J]; ring
  have hhead : |(∑ k ∈ range Y, f k) - q*∑ n ∈ range (X/q), g n| ≤ (X:ℝ)*(J*Real.sqrt X) := by
    rw [← repeated_sample_sum g hq0,← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _k ∈ range Y, J*Real.sqrt X := sum_le_sum fun k hk =>
        hcell k ((mem_range.mp hk).le.trans hXY)
      _ ≤ _ := by
        rw [sum_const,card_range,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hXY) (mul_nonneg hJ (Real.sqrt_nonneg _))
  have htail : |∑ k ∈ Ico Y X, f k| ≤ (q:ℝ)*(H*X) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _k ∈ Ico Y X, H*X := by
        apply sum_le_sum
        intro k hk
        have hkR : (k:ℝ)≤X := by exact_mod_cast (mem_Ico.mp hk).2.le
        have hh := abs_primeMass_le_linear q k
        have h₁ := mul_le_mul_of_nonneg_left hkR (by linarith only [hlog] : 0≤Real.log 4+4)
        have h₂ := mul_le_mul_of_nonneg_left hkR (abs_nonneg A)
        apply (abs_sub _ _).trans
        change |lastClassPrimeMass q k| + |A*(k:ℝ)| ≤ H*X
        rw [abs_mul A (k:ℝ),show |(k:ℝ)|=(k:ℝ) from abs_of_nonneg (Nat.cast_nonneg k)]
        dsimp only [H]; linarith only [hh,h₁,h₂]
      _ ≤ _ := by
        rw [sum_const,nsmul_eq_mul,Nat.card_Ico]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast gap X) (mul_nonneg hH (Nat.cast_nonneg X))
  change |(∑ k ∈ range X, f k)-q*∑ n ∈ range (X/q), g n| ≤ _
  rw [← sum_range_add_sum_Ico f hXY,add_sub_right_comm]
  apply (abs_add_le _ _).trans
  have he := le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg q) (mul_nonneg hH (Nat.cast_nonneg X))) hroot
  exact (add_le_add hhead (htail.trans he)).trans_eq (by ring)

private theorem sampling_power_iff (j : ℕ) (A : ℝ) {b : ℝ} (hb : 1/2 ≤ b) :
    (∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, |binomialGcdFirstTotal j A N| ≤ C*(N:ℝ)^(b+1)) ↔
      ∃ C : ℝ, 0≤C ∧ ∀ X : ℕ, 1≤X → |primeTotal (2^(j+1)) A X| ≤ C*(X:ℝ)^(b+1) := by
  let q := 2^(j+1)
  have hq1 : 1≤q := Nat.one_le_two_pow
  have hqR : 1≤(q:ℝ) := by exact_mod_cast hq1
  have hpow : 0≤b+1 := by linarith only [hb]
  obtain ⟨L,hL,hcmp⟩ := sampled_total_comparison j A
  have hclose (X : ℕ) (hx : 1≤X) :
      |primeTotal q A X-q*binomialGcdFirstTotal j A (X/q)| ≤ L*(X:ℝ)^(b+1) := by
    have hxR : 1≤(X:ℝ) := by exact_mod_cast hx
    have hr : Real.sqrt X ≤ (X:ℝ)^b := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hxR hb
    apply (hcmp X hx).trans
    rw [Real.rpow_add_one (by positivity : (X:ℝ) ≠ 0)]
    exact (mul_le_mul_of_nonneg_left hr (mul_nonneg hL (Nat.cast_nonneg X))).trans_eq (by ring)
  constructor
  · rintro ⟨C,hC,h⟩
    refine ⟨L+q*C,by positivity,fun X hx => ?_⟩
    have hB : |(q:ℝ)*binomialGcdFirstTotal j A (X/q)| ≤ (q*C)*(X:ℝ)^(b+1) := by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg q),mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
      exact (h _).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.div_le_self X q) hpow) hC)
    have ht := abs_sub_le (primeTotal q A X) ((q:ℝ)*binomialGcdFirstTotal j A (X/q)) 0
    simp only [sub_zero] at ht
    exact (ht.trans (add_le_add (hclose X hx) hB)).trans_eq (add_mul ..).symm
  · rintro ⟨C,hC,h⟩
    refine ⟨(L+C)*(q:ℝ)^(b+1),by positivity,fun N => ?_⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [binomialGcdFirstTotal,Real.zero_rpow (show b+1≠0 by linarith only [hb])]
    have hx := Nat.mul_pos hq1 hN
    have hd := hclose (q*N) hx
    rw [Nat.mul_div_cancel_left N hq1,abs_sub_comm] at hd
    have ht := abs_sub_le ((q:ℝ)*binomialGcdFirstTotal j A N) (primeTotal q A (q*N)) 0
    simp only [sub_zero] at ht
    have htot := ht.trans (add_le_add hd (h (q*N) hx))
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg q),← add_mul,Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg N),← mul_assoc] at htot
    exact (le_mul_of_one_le_left (abs_nonneg _) hqR).trans htot

private theorem primeTotal_above_abscissa {b : ℝ} (hb : _root_.RHTower.zeroReSup < b) (hb1 : b<1) :
    ∃ C : ℝ, 0≤C ∧ ∀ q X : ℕ, 2≤q → 1≤X →
      |primeTotal q (lastClassIntegerDensity q) X| ≤ C*(X:ℝ)^(b+1) := by
  have hh := _root_.RHTower.half_le_zeroReSup.trans_lt hb
  have hb0 : 0<b := by linarith only [hh]
  obtain ⟨K,hK,hψ⟩ := _root_.RHTower.exists_abs_chebyshevPsi_sub_le_rpow hb
  refine ⟨K/b+18,by positivity,fun q X hq hx => ?_⟩
  have hxR : 1≤(X:ℝ) := by exact_mod_cast hx
  have hx0 := zero_lt_one.trans_le hxR
  have hsum : |lastClassFirstMeanExcess q X| ≤ (K/b)*(X:ℝ)^b := by
    apply (abs_lastClassFirstMeanExcess_le q X hq).trans
    calc
      _ ≤ ∑ n ∈ Icc 1 X, K*(n:ℝ)^(b-1) := by
        apply sum_le_sum
        intro n hn
        have h1 : 1≤(n:ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
        have hp := zero_lt_one.trans_le h1
        rw [Real.rpow_sub_one hp.ne',← mul_div_assoc]
        exact (div_le_div_of_nonneg_left (abs_nonneg _) hp (by linarith : (n:ℝ)≤n+1)).trans
          (div_le_div_of_nonneg_right (hψ n h1) hp.le)
      _ ≤ _ := by
        rw [← mul_sum,← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,add_comm (1:ℝ)]
        exact (mul_le_mul_of_nonneg_left (_root_.HTGeometry.sum_rpow_sub_one_le hb0 hb1 X) hK).trans_eq (by ring)
  have hint : |∑ k ∈ range X, (lastClassIntegerCount q k-(k:ℝ)*lastClassIntegerDensity q)| ≤
      (X:ℝ)*(18*(X:ℝ)^b) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _k ∈ range X, 18*(X:ℝ)^b := by
        refine sum_le_sum fun k hk => (lastClassIntegerCount_density_error q k hq).trans ?_
        have hr := Real.sqrt_le_sqrt (show (k:ℝ)≤X by exact_mod_cast (mem_range.mp hk).le)
        have hp : Real.sqrt X ≤ (X:ℝ)^b := by
          rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hxR hh.le
        exact mul_le_mul_of_nonneg_left (hr.trans hp) (by norm_num)
      _ = _ := by simp
  have he : primeTotal q (lastClassIntegerDensity q) X =
      (X:ℝ)*lastClassFirstMeanExcess q X+
        ∑ k ∈ range X, (lastClassIntegerCount q k-(k:ℝ)*lastClassIntegerDensity q) := by
    rw [lastClassFirstMeanExcess_eq_sum q X hq,← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_pos hx0,Real.rpow_add_one hx0.ne']
  exact (add_le_add (mul_le_mul_of_nonneg_left hsum hx0.le) hint).trans_eq (by ring)

/-- RH is equivalent to power bounds for the first means of the actual binomial gcds
at cofinally many fixed depths. The slope may be chosen independently at each depth. -/
theorem riemannHypothesis_iff_binomialGcd_first_means :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/2<b → b<1 → ∃ᶠ j : ℕ in atTop,
      ∃ A C : ℝ, 0≤C ∧ ∀ N : ℕ, |binomialGcdFirstTotal j A N| ≤ C*(N:ℝ)^(b+1) := by
  constructor
  · intro hRH b hb hb1
    have hsup := _root_.RHTower.zeroReSup_le_of_forall_re_le fun z =>
      (_root_.RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hRH z).le
    obtain ⟨K,hK,h⟩ := primeTotal_above_abscissa (hsup.trans_lt hb) hb1
    apply Eventually.frequently
    exact Filter.Eventually.of_forall fun j => by
      let q := 2^(j+1)
      have hq : 2≤q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
      exact ⟨lastClassIntegerDensity q,(sampling_power_iff j _ hb.le).mpr
        ⟨K,hK,fun X hx => h q X hq hx⟩⟩
  · intro h
    apply _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro ρ hhalf hone hz
    obtain ⟨b,hb,hbρ⟩ := exists_between hhalf
    obtain ⟨j,⟨A,C,hC,hN⟩,hD⟩ := ((h b hb (hbρ.trans hone)).and_eventually
      (eventually_dyadicQuotientSymbol_ne_zero (by linarith only [hhalf] : 0<ρ.re))).exists
    obtain ⟨K,hK,hP⟩ := (sampling_power_iff j A hb.le).mp ⟨C,hC,hN⟩
    have hq : 2≤2^(j+1) := by have := Nat.lt_two_pow_self (n := j+1); omega
    exact hD (zero_of_primeTotal_bound _ hq (by linarith only [hb]) (hbρ.trans hone) hK hP hbρ hz)

#print axioms riemannHypothesis_iff_binomialGcd_first_means

end GaloisForLFunctions.ExceptionalLayerTheory
