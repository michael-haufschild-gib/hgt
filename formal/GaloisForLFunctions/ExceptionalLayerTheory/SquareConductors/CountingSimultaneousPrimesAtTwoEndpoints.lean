import GaloisForLFunctions.RHTower.Sieve.AffinePairSieve
import GaloisForLFunctions.RHTower.Sieve.GenericMarkerAnalytic

/-!
# Simultaneous prime crossings at two moving endpoints

For two fixed affine forms with distinct rational roots, the number of
simultaneous prime values up to M is O(M / log² M). Discarding primes up
to the slopes and determinant leaves exactly the ordinary two-root
Selberg denominator. The discarded primes affect only the constant.
-/

noncomputable section
open Finset Filter RHTower.Sieve
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem no_large_divisor {L h q : ℕ} (hq : 0 < q) (hqL : q ≤ L) :
    ∀ p ∈ rangePrimes L h, ¬ p ∣ q := by
  intro p hp hd
  have hlo := (mem_Icc.mp (mem_filter.mp hp).1).1
  have h := Nat.le_of_dvd hq hd
  omega

private theorem upper_affine_primorial {L h a b : ℕ} (hab : 0 < a*b) (hL : a*b ≤ L) :
    affinePairPrimorial L h a b = rangePrimorial L h := by
  have he : affinePairSiftingPrimes L h a b = rangePrimes L h := by
    exact filter_true_of_mem (no_large_divisor hab hL)
  unfold affinePairPrimorial rangePrimorial
  rw [he]

private theorem affine_bounding_above_slopes {L a b : ℕ} (hL : 2 ≤ L)
    (hab : 0 < a*b) (habL : a*b ≤ L) (h c d : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    affinePairBoundingSum L h a b c d z =
      SelbergSieve.selbergBoundingSum (roughPairSieve 0 hL h (affinePairDiscriminant a b c d).natAbs hz) := by
  rw [affinePairBoundingSum,upper_affine_primorial hab habL]
  apply sum_congr rfl
  intro e he
  have hd := (Nat.mem_divisors.mp he).1
  have hn := ((rangePrimorial_squarefree L h).squarefree_of_dvd hd).ne_zero
  change (if (e : ℝ)^2 ≤ z then _ else 0) = (if (e : ℝ)^2 ≤ z then _ else 0)
  split_ifs
  · exact (selbergTerms_roughPairSieve 0 hL h _ hz hd hn).symm
  · rfl

/-- Mertens' lower bound gives a denominator proportional to the square
of the sifting logarithm once the lower cutoff exceeds the exceptional primes. -/
private theorem affine_endpoint_denominator {a b L : ℕ} (hL : 2 ≤ L)
    (hab : 0 < a*b) (habL : a*b ≤ L) (c d : ℕ)
    (hD : 0 < (affinePairDiscriminant a b c d).natAbs)
    (hDL : (affinePairDiscriminant a b c d).natAbs ≤ L) {h : ℕ} (hh : L ≤ h)
    {z : ℝ} (hz : 1 ≤ z) (hlev : (h:ℝ)^(18:ℝ) ≤ Real.sqrt z)
    (hlog : 20*mertensFirstConst ≤ Real.log h) :
    (Real.log h * Real.exp (-(mertensSecondLowerConst + mertensS L)))^2 / 2 ≤
      affinePairBoundingSum L h a b c d z := by
  let D := (affinePairDiscriminant a b c d).natAbs
  have he : (rangePrimes L h).filter (fun p => p ∣ D) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro p hp
    exact no_large_divisor hD hDL p hp
  have hh₂ := hL.trans hh
  have hs := selbergBoundingSum_ge_mertens_sharp 0 hL D hz hh₂ hh hlev hlog
  rw [he,prod_empty,mul_one] at hs
  rw [affine_bounding_above_slopes hL hab habL h c d hz]
  have hm := le_mertensS hh₂
  have ht : Real.log (Real.log h) + -(mertensSecondLowerConst + mertensS L) ≤
      mertensS h - mertensS L := by
    change Real.log (Real.log h) - mertensSecondLowerConst ≤ mertensS h at hm
    linarith only [hm]
  have hl := log_pos_of_two_le hh₂
  have hExp := Real.exp_le_exp.mpr ht
  rw [Real.exp_add,Real.exp_log hl] at hExp
  have hsq := pow_le_pow_left₀ (mul_nonneg hl.le (Real.exp_pos _).le) hExp 2
  linarith only [hs,hsq]

private theorem affine_endpoint_remainder {L h a b : ℕ} (hL : 2 ≤ L)
    (hab : 0 < a*b) (habL : a*b ≤ L) {z : ℝ} (hz : 1 ≤ z) :
    (∑ e ∈ (affinePairPrimorial L h a b).divisors,
      if (e:ℝ) ≤ z then (6:ℝ)^e.primeFactors.card else 0) ≤ 2*z^3 := by
  rw [upper_affine_primorial hab habL]
  refine le_trans (sum_le_sum fun e _ => ?_) (sieve_remainder_le (h:=h) hL hz)
  split_ifs
  · linarith only [show 0 ≤ (6:ℝ)^e.primeFactors.card by positivity]
  · exact le_rfl

private theorem prime_pairs_with_small_values {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (c d M h : ℕ) :
    ((Icc 1 M).filter (fun n => (a*n+c).Prime ∧ (b*n+d).Prime)).card ≤
      h + ((Icc 1 M).filter (fun n => (a*n+c).Prime ∧ (b*n+d).Prime ∧ h<a*n+c ∧ h<b*n+d)).card := by
  let S := (Icc 1 M).filter (fun n => (a*n+c).Prime ∧ (b*n+d).Prime ∧ h<a*n+c ∧ h<b*n+d)
  have hsub : ((Icc 1 M).filter (fun n => (a*n+c).Prime ∧ (b*n+d).Prime)) ⊆ Icc 1 h ∪ S := by
    intro n hn
    obtain ⟨hn,hp,hq⟩ := mem_filter.mp hn
    by_cases hnh : n ≤ h
    · exact mem_union_left _ (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,hnh⟩)
    · have hu := Nat.le_mul_of_pos_left n ha
      have hv := Nat.le_mul_of_pos_left n hb
      exact mem_union_right _ (mem_filter.mpr ⟨hn,hp,hq,by omega,by omega⟩)
  simpa only [Nat.card_Icc,Nat.add_sub_cancel] using (card_le_card hsub).trans (card_union_le _ _)

private theorem secondary_power_times_log_sq {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 * x ^ (3/4:ℝ) ≤ 64*x := by
  have hx₀ := zero_lt_one.trans_le hx
  have h := Real.log_le_rpow_div hx₀.le (by norm_num : (0:ℝ)<1/8)
  have hu : Real.log x ≤ 8 * x^(1/8:ℝ) := by linarith only [h]
  have hsq := pow_le_pow_left₀ (Real.log_nonneg hx) hu 2
  apply (mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hx₀.le _)).trans_eq
  rw [mul_pow,←Real.rpow_natCast (x^(1/8:ℝ)) 2,←Real.rpow_mul hx₀.le,mul_assoc,
    ←Real.rpow_add hx₀]
  norm_num

/-- For fixed positive slopes and distinct affine roots, the number of
simultaneous prime values has the full two-logarithm upper bound. -/
theorem two_affine_prime_endpoints_log_squared {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (c d : ℕ) (hne : a*d ≠ b*c) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      Real.log M ^ 2 * (((Icc 1 M).filter (fun n => (a*n+c).Prime ∧ (b*n+d).Prime)).card:ℝ)
        ≤ C*M := by
  let D := (affinePairDiscriminant a b c d).natAbs
  let L := max 2 (max (a*b) D)
  have hL : 2 ≤ L := le_max_left _ _
  have hab := Nat.mul_pos ha hb
  have habL : a*b ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hDL : D ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hD : 0 < D := by
    apply Int.natAbs_pos.mpr
    unfold affinePairDiscriminant
    exact sub_ne_zero.mpr (by exact_mod_cast hne)
  let A := Real.exp (-(mertensSecondLowerConst + mertensS L))/288
  have hA : 0 < A := div_pos (Real.exp_pos _) (by norm_num)
  refine ⟨2/A^2+192,by positivity,?_⟩
  have hcast := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hlogs := Real.tendsto_log_atTop.comp hcast
  have hpow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/144)).comp hcast
  filter_upwards [eventually_ge_atTop 2,hpow.eventually_ge_atTop (L:ℝ),
    hlogs.eventually_ge_atTop (288*Real.log 2),hlogs.eventually_ge_atTop (288*(20*mertensFirstConst))] with M hM hp hl₂ hl₀
  let h := sieveSift M
  have hh : L ≤ h := Nat.le_floor hp
  have hh₂ := hL.trans hh
  have hg := log_sieveSift_ge hM hl₂ hh₂
  have hM₁ : 1 ≤ M := by omega
  have hMR := (Nat.one_le_cast (α:=ℝ)).mpr hM₁
  have hlogM := log_pos_of_two_le hM
  have hlog : 20*mertensFirstConst ≤ Real.log h := by
    change 288*(20*mertensFirstConst) ≤ Real.log M at hl₀
    linarith only [hl₀,hg]
  have hz := one_le_sieveLevel hM₁
  let B := affinePairBoundingSum L h a b c d (sieveLevel M)
  have hsmall : A * Real.log M ≤ Real.log h * Real.exp (-(mertensSecondLowerConst + mertensS L)) := by
    have hu := mul_le_mul_of_nonneg_right hg (Real.exp_pos (-(mertensSecondLowerConst + mertensS L))).le
    dsimp only [A]
    linarith only [hu]
  have hd := affine_endpoint_denominator hL hab habL c d hD hDL hh hz (sieveSift_pow_le hM₁) hlog
  have hB : (A*Real.log M)^2/2 ≤ B :=
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (mul_pos hA hlogM).le hsmall 2) (by norm_num)).trans hd
  have hscale : Real.log M ^ 2 * ((M:ℝ)/B) ≤ (2/A^2)*M := by
    have hpos : 0 < (A*Real.log M)^2/2 := by positivity
    have hu := div_le_div_of_nonneg_left (Nat.cast_nonneg M) hpos hB
    apply (mul_le_mul_of_nonneg_left hu (sq_nonneg _)).trans_eq
    field_simp [hA.ne',hlogM.ne']
    <;> ring
  have hc := card_primeAffinePair_le M hL h ha hb c d hz
  have hr := affine_endpoint_remainder (h:=h) hL hab habL hz
  have hlev : sieveLevel M ^ 3 = (M:ℝ)^(3/4:ℝ) := by
    rw [←Real.rpow_natCast (sieveLevel M) 3,sieveLevel,←Real.rpow_mul (Nat.cast_nonneg M)]
    norm_num
  rw [hlev] at hr
  have hcut : (h:ℝ) ≤ (M:ℝ)^(3/4:ℝ) :=
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg M) (1/144:ℝ))).trans
      (Real.rpow_le_rpow_of_exponent_le hMR (by norm_num))
  have hfull := (Nat.cast_le (α:=ℝ)).mpr (prime_pairs_with_small_values ha hb c d M h)
  rw [Nat.cast_add] at hfull
  have htotal : (((Icc 1 M).filter (fun n => (a*n+c).Prime ∧ (b*n+d).Prime)).card:ℝ)
      ≤ (M:ℝ)/B + 3*(M:ℝ)^(3/4:ℝ) := by
    dsimp only [B]
    linarith only [hfull,hcut,hc,hr]
  have hu := mul_le_mul_of_nonneg_left htotal (sq_nonneg (Real.log M))
  have hv := secondary_power_times_log_sq hMR
  linarith only [hu,hv,hscale]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
