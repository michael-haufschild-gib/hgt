import GaloisForLFunctions.ExceptionalLayerTheory.PairedCofactorBoundsForOrdinaryPrimeCounts
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrimeAbelCutoff
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion
import GaloisForLFunctions.PNTPlus.Consequences
import GaloisForLFunctions.RHTower.MertensSecondTheorem

/-!
# Prime multiples recover each finite cofactor

At a product of a fixed cofactor and a prime larger than the entire cofactor
support, the centred prime convolution is affine in the logarithm of that
prime. Its slope is the selected cofactor coefficient. The prime number
theorem recovers this coefficient by a signed average on the same products.
-/

noncomputable section

open Finset ArithmeticFunction Filter Topology
open scoped Pointwise
open RHTower.Sieve

namespace GaloisForLFunctions.ExceptionalLayerTheory

local notation "primeExcess" => (vonMangoldt - (zeta : ArithmeticFunction ℝ))

private theorem sum_divisors_large_prime (u : ℕ → ℝ) {d p : ℕ} (hp : p.Prime)
    (hd : 0 < d) (hlt : d < p) :
    (∑ e ∈ (p*d).divisors, u e) = (∑ e ∈ d.divisors, u e) + ∑ e ∈ d.divisors, u (p*e) := by
  rw [Nat.divisors_mul, Finset.mul_def, sum_image]
  · rw [sum_product]
    simp [hp.divisors, hp.ne_one.symm]
  · intro x hx y hy hxy
    exact (hp.coprime_iff_not_dvd.mpr (fun h => hlt.not_ge (Nat.le_of_dvd hd h))).mul_injOn_divisors hx hy hxy

private theorem prime_weight_mul_smaller {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hlt : k < p) :
    vonMangoldt (p*k) = if k = 1 then Real.log p else 0 := by
  split_ifs with h
  · rw [h, mul_one, vonMangoldt_apply_prime hp]
  · by_contra hn
    obtain ⟨q, _, hu⟩ := isPrimePow_iff_unique_prime_dvd.mp (vonMangoldt_ne_zero_iff.mp hn)
    have hpq := hu p ⟨hp, dvd_mul_right p k⟩
    have hkq := hu k.minFac ⟨Nat.minFac_prime h, dvd_mul_of_dvd_right (Nat.minFac_dvd k) p⟩
    have hpk : p ∣ k := by rw [hpq.trans hkq.symm]; exact Nat.minFac_dvd k
    exact hlt.not_ge (Nat.le_of_dvd hk hpk)

/-- On ordinary prime multiples of a fixed index, the slope in `log p` is
exactly the coefficient at that index, and the intercept is its divisor sum. -/
theorem centered_cofactor_at_prime_mul (f : ArithmeticFunction ℝ) {W d p : ℕ}
    (hd : 0 < d) (hdW : d ≤ W) (hp : p.Prime) (hWp : W < p) :
    (primeExcess * truncAF f W) (p*d) =
      f d * Real.log p - ∑ e ∈ d.divisors, f e := by
  rw [mul_comm, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun e k => truncAF f W e * primeExcess k), sum_divisors_large_prime _ hp hd (hdW.trans_lt hWp)]
  have hlarge : (∑ e ∈ d.divisors, truncAF f W (p * e) * primeExcess (p*d/(p*e))) = 0 := by
    apply sum_eq_zero
    intro e he
    have he0 := Nat.pos_of_mem_divisors he
    rw [truncAF_apply_of_gt (hWp.trans_le (Nat.le_mul_of_pos_right p he0)), zero_mul]
  have hsingle : (∑ e ∈ d.divisors, if e = d then f e * Real.log p else 0) = f d * Real.log p := by
    rw [sum_ite_eq', if_pos (Nat.mem_divisors.mpr ⟨dvd_refl d, hd.ne'⟩)]
  rw [hlarge, add_zero, ← hsingle, ← sum_sub_distrib]
  refine sum_congr rfl fun e he => ?_
  have hed := (Nat.mem_divisors.mp he).1
  have he0 := Nat.pos_of_mem_divisors he
  have heD := Nat.le_of_dvd hd hed
  have hk : 0 < d/e := (Nat.one_le_div_iff he0).mpr heD
  have hqe : d/e = 1 ↔ e = d := by
    constructor
    · intro h
      simpa [h] using Nat.div_mul_cancel hed
    · rintro rfl
      exact Nat.div_self hd
  have hpos := Nat.mul_pos hp.pos hk
  rw [truncAF_apply, if_pos (heD.trans hdW), Nat.mul_div_assoc p hed]
  change f e * (vonMangoldt (p * (d/e)) - (zeta : ArithmeticFunction ℝ) (p * (d/e))) = _
  rw [RHTower.Sieve.zeta_real_apply_of_ne_zero hpos.ne',
    prime_weight_mul_smaller hp hk ((Nat.div_le_self d e).trans_lt (hdW.trans_lt hWp))]
  simp only [hqe]
  by_cases h : e = d <;> simp [h]
  ring

/-- Signed sum on multiples of one fixed index by primes between `W` and `X`. -/
def primeMultipleSum (f : ArithmeticFunction ℝ) (W d X : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE X \ Nat.primesLE W), (primeExcess * truncAF f W) (p*d)

private theorem primeMultipleSum_eq (f : ArithmeticFunction ℝ) {W d X : ℕ}
    (hd : 0 < d) (hdW : d ≤ W) (hWX : W ≤ X) :
    primeMultipleSum f W d X =
      f d * (Chebyshev.theta X - Chebyshev.theta W) -
      ((Nat.primeCounting X : ℝ) - Nat.primeCounting W) * ∑ e ∈ d.divisors, f e := by
  classical
  let B := ∑ e ∈ d.divisors, f e
  have hs := Nat.primesLE_mono hWX
  have he (p : ℕ) (hp : p ∈ Nat.primesLE X \ Nat.primesLE W) :
      (primeExcess * truncAF f W) (p*d) = f d * Real.log p - B := by
    obtain ⟨hX, hW⟩ := mem_sdiff.mp hp
    obtain ⟨hX', hprime⟩ := Nat.mem_primesLE.mp hX
    exact centered_cofactor_at_prime_mul f hd hdW hprime
      (lt_of_not_ge fun h => hW (Nat.mem_primesLE.mpr ⟨h, hprime⟩))
  rw [primeMultipleSum, sum_congr rfl he, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul,
    card_sdiff_of_subset hs, Nat.cast_sub (card_le_card hs), Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting, sum_sdiff_eq_sub hs,
    Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]

/-- Normalizing by the prime cutoff recovers each signed coefficient. -/
theorem tendsto_primeMultipleSum_div (f : ArithmeticFunction ℝ) {W d : ℕ}
    (hd : 0 < d) (hdW : d ≤ W) :
    Tendsto (fun X : ℕ => primeMultipleSum f W d X / (X : ℝ)) atTop (𝓝 (f d)) := by
  have hθ : Tendsto (fun X : ℕ => Chebyshev.theta X / (X : ℝ)) atTop (𝓝 1) :=
    ((Asymptotics.isEquivalent_iff_tendsto_one
      ((eventually_gt_atTop (0 : ℝ)).mono fun _ hx => hx.ne')).mp chebyshev_asymptotic).comp
      tendsto_natCast_atTop_atTop
  have hconst (c : ℝ) : Tendsto (fun X : ℕ => c / (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hπ := ArithmeticWeightTheory.GaugeDeformations.tendsto_primeCounting_div_nat_zero
  have h := ((hθ.sub (hconst (Chebyshev.theta W))).const_mul (f d)).sub
    ((hπ.sub (hconst (Nat.primeCounting W))).mul_const (∑ e ∈ d.divisors, f e))
  simp only [sub_zero, mul_one, sub_self, zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop W] with X hX
  rw [primeMultipleSum_eq f hd hdW hX]
  ring

/-- In the product coordinate the signed density of this prime slice is
`f d / d`. The underlying set of products itself has natural density zero. -/
theorem tendsto_primeMultipleSum_div_product (f : ArithmeticFunction ℝ) {W d : ℕ}
    (hd : 0 < d) (hdW : d ≤ W) :
    Tendsto (fun N : ℕ => primeMultipleSum f W d (N/d) / (N : ℝ)) atTop (𝓝 (f d / d)) := by
  have h := ((tendsto_primeMultipleSum_div f hd hdW).comp (HTGeometry.tendsto_natDiv_atTop hd)).mul
    (HTGeometry.tendsto_natDiv_div_self hd)
  rw [mul_one_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop d] with N hN
  have hq : 0 < N/d := (Nat.one_le_div_iff hd).mpr hN
  have hqr : ((N/d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  change (_ / ((N/d : ℕ) : ℝ)) * (((N/d : ℕ) : ℝ) / N) = _
  field_simp

/-- Products from different large-prime slices are disjoint. -/
private theorem prime_slice_subset {W : ℕ} (S : Finset ℕ) (hS : S ⊆ Icc 1 W) (N : ℕ) :
    ∃ A ⊆ Icc 1 N, ∀ u : ℕ → ℝ,
      (∑ d ∈ S, ∑ p ∈ Nat.primesLE (N/d) \ Nat.primesLE W, u (p*d)) = ∑ n ∈ A, u n := by
  classical
  let P := fun d => Nat.primesLE (N/d) \ Nat.primesLE W
  let T := S.sigma P
  let prod := fun x : (d : ℕ) × ℕ => x.2*x.1
  have hmem {d p : ℕ} (h : (⟨d,p⟩ : (i : ℕ) × ℕ) ∈ T) :
      (1 ≤ d ∧ d ≤ W) ∧ (p ≤ N/d ∧ p.Prime) ∧ W < p := by
    obtain ⟨hd, hp⟩ := mem_sigma.mp h
    obtain ⟨hpN, hpW⟩ := mem_sdiff.mp hp
    have hp' := Nat.mem_primesLE.mp hpN
    exact ⟨mem_Icc.mp (hS hd), hp', lt_of_not_ge fun hle =>
      hpW (Nat.mem_primesLE.mpr ⟨hle, hp'.2⟩)⟩
  have hinj : Set.InjOn prod (T : Set ((d : ℕ) × ℕ)) := by
    rintro ⟨d,p⟩ hx ⟨e,q⟩ hy heq
    obtain ⟨_, ⟨_,hp⟩, hWp⟩ := hmem hx
    obtain ⟨⟨he0, heW⟩, ⟨_,hq⟩, _⟩ := hmem hy
    change p*d = q*e at heq
    have hdiv : p ∣ q*e := heq ▸ dvd_mul_right p d
    have hpq := (Nat.prime_dvd_prime_iff_eq hp hq).mp ((hp.dvd_mul.mp hdiv).resolve_right
      (fun h => hWp.not_ge ((Nat.le_of_dvd he0 h).trans heW)))
    subst q
    obtain rfl := Nat.eq_of_mul_eq_mul_left hp.pos heq
    rfl
  refine ⟨T.image prod, ?_, fun u => ?_⟩
  · intro n hn
    obtain ⟨⟨d,p⟩, hx, rfl⟩ := mem_image.mp hn
    obtain ⟨⟨hd,_⟩, ⟨hpN,hp⟩, _⟩ := hmem hx
    exact mem_Icc.mpr ⟨Nat.mul_pos hp.pos hd, (Nat.le_div_iff_mul_le hd).mp hpN⟩
  · simp only [sum_image hinj, T, sum_sigma, P, prod]

private theorem prime_slice_abs_sum_le {W : ℕ} (S : Finset ℕ) (hS : S ⊆ Icc 1 W)
    (g : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ S, |∑ p ∈ Nat.primesLE (N/d) \ Nat.primesLE W, g (p*d)|) ≤ ∑ n ∈ Icc 1 N, |g n| := by
  obtain ⟨A, hA, he⟩ := prime_slice_subset S hS N
  have htri (d : ℕ) := abs_sum_le_sum_abs (fun p : ℕ => g (p*d)) (Nat.primesLE (N/d) \ Nat.primesLE W)
  have hsum := sum_le_sum (s := S) (fun d _ => htri d)
  have htotal := sum_le_sum_of_subset_of_nonneg (f := fun n => |g n|) hA (fun n _ _ => abs_nonneg (g n))
  exact hsum.trans ((he (fun n => |g n|)).le.trans htotal)

/-- Every finite subfamily forces its full absolute harmonic mass as a
linear lower bound on the variation of the centred convolution. -/
theorem eventually_cofactor_variation_gt (f : ArithmeticFunction ℝ) {W : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Icc 1 W) {c : ℝ} (hc : c < ∑ d ∈ S, |f d| / d) :
    ∀ᶠ N : ℕ in atTop, c * N < ∑ n ∈ Icc 1 N, |(primeExcess * truncAF f W) n| := by
  have h := tendsto_finsetSum S fun d hd =>
    (tendsto_primeMultipleSum_div_product f (mem_Icc.mp (hS hd)).1 (mem_Icc.mp (hS hd)).2).abs
  simp only [abs_div, Nat.abs_cast, ← sum_div] at h
  filter_upwards [Filter.Tendsto.eventually_const_lt hc h, eventually_gt_atTop (0 : ℕ)] with N hN hpos
  have hr : (0 : ℝ) < N := by exact_mod_cast hpos
  exact ((lt_div_iff₀ hr).mp hN).trans_le
    (prime_slice_abs_sum_le S hS (fun n => (primeExcess * truncAF f W) n) N)

private theorem short_prime {V p : ℕ} (hV : 1 ≤ V) (hp : p.Prime) (hlt : V < p) :
    typeIIShort V p = -1 := by
  change (1 : ArithmeticFunction ℝ) p -
    ((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) V) p = _
  rw [ArithmeticFunction.coe_zeta_mul_apply, hp.divisors]
  simp [hp.ne_one, hp.ne_one.symm, truncAF_apply, hV, not_le.mpr hlt]

private theorem primeRecipSum_eq (X : ℕ) :
    RHTower.primeRecipSum X = ∑ p ∈ Nat.primesLE X, 1 / (p : ℝ) := by
  simp only [RHTower.primeRecipSum, RHTower.primeRecipWeight, ← sum_filter, one_div,
    Nat.primesLE_eq_filter_Icc_zero]

private theorem primeBand_mass :
    Tendsto (fun V : ℕ => ∑ p ∈ Nat.primesLE (V^2) \ Nat.primesLE V, 1 / (p : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  have h := ((RHTower.tendsto_primeRecipSum_sub_logLog.comp
    (tendsto_pow_atTop (by decide : 2 ≠ 0))).sub RHTower.tendsto_primeRecipSum_sub_logLog).add_const
    (Real.log 2)
  rw [sub_self, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with V hV
  have hsq : V ≤ V^2 := by simpa only [sq] using Nat.le_mul_of_pos_left V (by omega)
  have hlog : 0 < Real.log V := Real.log_pos (by exact_mod_cast hV)
  rw [sum_sdiff_eq_sub (Nat.primesLE_mono hsq), ← primeRecipSum_eq, ← primeRecipSum_eq]
  simp only [Function.comp_apply, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlog.ne']
  ring

private theorem cofactorCountError_div_tendsto_zero (V W : ℕ) :
    Tendsto (fun N : ℕ => cofactorCountError V W N / (N : ℝ)) atTop (𝓝 0) := by
  have hterm (d : ℕ) (hd : d ∈ Icc 1 W) :
      Tendsto (fun N : ℕ => typeIIShort V d *
        ((Chebyshev.psi (N/d : ℕ) - (N/d : ℕ)) / (N : ℝ))) atTop (𝓝 0) := by
    have hd0 := (mem_Icc.mp hd).1
    have h := (((RHTower.tendsto_psi_natCast_div.comp (HTGeometry.tendsto_natDiv_atTop hd0)).sub_const 1).mul
      (HTGeometry.tendsto_natDiv_div_self hd0)).const_mul (typeIIShort V d)
    simp only [sub_self, zero_mul, mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop d] with N hN
    have hq' : 0 < N/d := (Nat.one_le_div_iff hd0).mpr hN
    have hq : ((N/d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
    simp only [Function.comp_apply]
    field_simp
  have h := tendsto_finsetSum (Icc 1 W) hterm
  simp only [sum_const_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop W] with N hN
  rw [cofactorCountError_eq, min_eq_right hN, sum_div]
  exact sum_congr rfl fun d _ => (mul_div_assoc _ _ _).symm

/-- The prime cofactors in `(V,V²]` force negative mass, and their
complement carries the opposite mass by the prime number theorem. Thus
the full variation per integer exceeds every constant below `2 log 2`
at all sufficiently large paired cutoffs. -/
theorem vaughan_cofactor_linear_variation {c : ℝ} (hc : c < 2 * Real.log 2) :
    ∀ᶠ V : ℕ in atTop, ∀ W ≥ V^2, ∀ᶠ N : ℕ in atTop,
      c * N < ∑ n ∈ Icc 1 N, |cofactorCountCoeff V W n| := by
  have hc' : c/2 < Real.log 2 := by linarith only [hc]
  filter_upwards [Filter.Tendsto.eventually_const_lt hc' primeBand_mass, eventually_ge_atTop (1 : ℕ)] with V hm hV
  intro W hW
  let S := Nat.primesLE (V^2) \ Nat.primesLE V
  have hmem {p : ℕ} (hp : p ∈ S) : p.Prime ∧ V < p ∧ p ≤ V^2 := by
    obtain ⟨hhi, hlo⟩ := mem_sdiff.mp hp
    obtain ⟨hh, hprime⟩ := Nat.mem_primesLE.mp hhi
    exact ⟨hprime, lt_of_not_ge (fun h => hlo (Nat.mem_primesLE.mpr ⟨h,hprime⟩)), hh⟩
  have hS : S ⊆ Icc 1 W := fun _ hp => mem_Icc.mpr ⟨(hmem hp).1.pos, (hmem hp).2.2.trans hW⟩
  have hlim := tendsto_finsetSum S fun p hp =>
    tendsto_primeMultipleSum_div_product (typeIIShort V) (hmem hp).1.pos ((hmem hp).2.2.trans hW)
  have hcoeff : (∑ p ∈ S, typeIIShort V p / p) = -(∑ p ∈ S, 1 / (p : ℝ)) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun p hp => by rw [short_prime hV (hmem hp).1 (hmem hp).2.1, neg_div]
  rw [hcoeff] at hlim
  have h := (cofactorCountError_div_tendsto_zero V W).sub (hlim.const_mul 2)
  have hm' : c < 0 - 2 * (-(∑ p ∈ S, 1 / (p : ℝ))) := by
    change c/2 < (∑ p ∈ S, 1 / (p : ℝ)) at hm
    linarith only [hm]
  filter_upwards [Filter.Tendsto.eventually_const_lt hm' h, eventually_gt_atTop (0 : ℕ)] with N hN hpos
  have hr : (0 : ℝ) < N := by exact_mod_cast hpos
  change c < cofactorCountError V W N / N - 2 * ∑ p ∈ S, primeMultipleSum (typeIIShort V) W p (N/p) / N at hN
  rw [← sum_div, ← mul_div_assoc, ← sub_div, lt_div_iff₀ hr] at hN
  obtain ⟨A,hA,he⟩ := prime_slice_subset S hS N
  change c * N < (∑ n ∈ Icc 1 N, cofactorCountCoeff V W n) -
    2 * (∑ p ∈ S, ∑ q ∈ Nat.primesLE (N/p) \ Nat.primesLE W, cofactorCountCoeff V W (q*p)) at hN
  rw [he] at hN
  have ha := sum_le_sum (s := A) (fun n _ => neg_abs_le (cofactorCountCoeff V W n))
  have hb := sum_le_sum (s := Icc 1 N \ A) (fun n _ => le_abs_self (cofactorCountCoeff V W n))
  rw [sum_neg_distrib] at ha
  rw [sum_sdiff_eq_sub hA, sum_sdiff_eq_sub hA] at hb
  linarith only [ha, hb, hN]

#print axioms centered_cofactor_at_prime_mul
#print axioms tendsto_primeMultipleSum_div
#print axioms vaughan_cofactor_linear_variation

end GaloisForLFunctions.ExceptionalLayerTheory
