import GaloisForLFunctions.RHTower.Sieve.PrimeDilationFullSieve
import GaloisForLFunctions.RHTower.Sieve.GenericMarkerAnalytic
import GaloisForLFunctions.RHTower.RouteEForbiddenSupportStability
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicMain
import GaloisForLFunctions.RHTower.Sieve.TwistedOffDiagonalSum
import GaloisForLFunctions.RHTower.BourgainGaussianFourier
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Critical-height Gaussian prime-pair cancellation

For the complete Gaussian prime band at scale `N = K^2`, the normalized
Gaussian height average of its squared modulus against `(A/B)^(it)` is
`o(1/log N)`, uniformly in the height centre and all distinct positive coprime
`A, B ≤ K`.

After subtracting the entire diagonal Gaussian packet, the same conclusion
holds uniformly for every real twist `β ∈ [1/2, 2]`, including the near-identity
region. Dirichlet approximation and translated blocks of width `b*K` reduce
all off-diagonal pairs to affine progressions of length at most `K`. The full
shifted determinant kernel has mass `O(b)`, cancelling the block count `O(K/b)`.

A logarithmic lower sieve cutoff bounds the singular product away from zero.
Every prime pair, original Gaussian coefficient, sieve anchor, finite sieve
remainder and Gaussian tail is retained. No prime-distribution or
zero-correlation hypothesis is assumed.
-/

noncomputable section
open Finset Filter MeasureTheory
open scoped Topology
namespace RHTower
namespace GaussianPrimeTwist
open Sieve

private theorem prod_one_sub_ge (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ p ∈ s, 0 ≤ f p ∧ f p ≤ 1) :
    1 - ∑ p ∈ s, f p ≤ ∏ p ∈ s, (1 - f p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (by simp)
    have hfs : ∀ p ∈ s, 0 ≤ f p ∧ f p ≤ 1 := fun p hp => hf p (by simp [hp])
    have hsum : 0 ≤ ∑ p ∈ s, f p := Finset.sum_nonneg fun p hp => (hfs p hp).1
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hm := mul_le_mul_of_nonneg_left (ih hfs) (sub_nonneg.mpr hfa.2)
    nlinarith [mul_nonneg hfa.1 hsum]

private theorem tail_singular_ge_half {d L h : ℕ} (hd : d ≠ 0) (hL : 2 ≤ L)
    (hlog : 2 * Real.log d ≤ (L : ℝ) * Real.log L) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ (rangePrimes L h).filter (fun p => p ∣ d),
      (((p : ℝ) - 1) / p) := by
  let S := (rangePrimes L h).filter (fun p => p ∣ d)
  have hmem (p : ℕ) (hp : p ∈ S) : p.Prime ∧ L < p ∧ p ∣ d := by
    obtain ⟨hr, hdv⟩ := Finset.mem_filter.mp hp
    exact ⟨rangePrimes_prime hr, by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
      omega, hdv⟩
  have hsub : S ⊆ d.primeFactors := fun p hp =>
    (hmem p hp).1.mem_primeFactors (hmem p hp).2.2 hd
  have hLR : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hsum := ForbiddenSupport.sum_inv_le_log hd hsub hLR (fun p hp =>
    by exact_mod_cast (hmem p hp).2.1.le)
  have hprod := prod_one_sub_ge S (fun p => (p : ℝ)⁻¹) (by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hmem p hp).1.one_lt.le
    exact ⟨inv_nonneg.mpr (by positivity), inv_le_one_of_one_le₀ hp1⟩)
  have hden : 0 < (L : ℝ) * Real.log L := mul_pos (by positivity) (Real.log_pos hLR)
  have hh : Real.log d / ((L : ℝ) * Real.log L) ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hbound : (1 / 2 : ℝ) ≤ ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by linarith
  apply hbound.trans_eq
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hmem p hp).1.ne_zero
  field_simp

private theorem mertens_saving (L h : ℕ) (hL : 2 ≤ L) (hh : 2 ≤ h) :
    (Real.log h / Real.log L) * Real.exp (-mertensGapConst) ≤
      Real.exp (mertensS h - mertensS L) := by
  have hlo := le_mertensS hh
  have hup := mertensS_le hL
  have hlogh : 0 < Real.log (h : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < h))
  have hlogL : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
  have hstep : Real.log (Real.log h) - Real.log (Real.log L) - mertensGapConst ≤
      mertensS h - mertensS L := by
    dsimp [logLog, mertensGapConst] at *
    linarith
  convert Real.exp_le_exp.mpr hstep using 1
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log hlogh, Real.exp_log hlogL, Real.exp_neg]
  ring

private theorem high_sieve_main {M L d : ℕ} (hL : 2 ≤ L)
    (hLh : L ≤ sieveSift M) (hd : d ≠ 0)
    (hlogd : 2*Real.log (d : ℝ) ≤ (L : ℝ)*Real.log L) (X : ℝ) (hX : 0 ≤ X) :
    X / ((1/2)*(Real.exp (mertensS (sieveSift M)-mertensS L)^2 *
      ∏ p ∈ (rangePrimes L (sieveSift M)).filter (fun p => p ∣ d), (((p : ℝ)-1)/p))) ≤
      4*X*(Real.log L/Real.log (sieveSift M))^2*Real.exp (2*mertensGapConst) := by
  have hh : 2 ≤ sieveSift M := hL.trans hLh
  have hsing := tail_singular_ge_half (h := sieveSift M) hd hL hlogd
  have hsav := mertens_saving L (sieveSift M) hL hh
  have hlogL : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
  have hlogH : 0 < Real.log (sieveSift M) := Real.log_pos (by exact_mod_cast (by omega : 1 < sieveSift M))
  have hsave0 : 0 < (Real.log (sieveSift M) / Real.log L) * Real.exp (-mertensGapConst) := by positivity
  have hsq := pow_le_pow_left₀ hsave0.le hsav 2
  have hden : (1 / 4 : ℝ) * ((Real.log (sieveSift M) / Real.log L) *
        Real.exp (-mertensGapConst)) ^ 2 ≤
      (1 / 2) * (Real.exp (mertensS (sieveSift M) - mertensS L)^2 *
        ∏ p ∈ (rangePrimes L (sieveSift M)).filter (fun p => p ∣ d),
          (((p : ℝ) - 1) / p)) := by
    have hm := mul_le_mul hsq hsing (by norm_num : (0 : ℝ) ≤ 1/2) (by positivity)
    nlinarith
  have hmain := div_le_div_of_nonneg_left hX (by positivity) hden
  have heq : (X / ((1 / 4) *
      ((Real.log (sieveSift M) / Real.log L) * Real.exp (-mertensGapConst)) ^ 2)) =
      4 * X * (Real.log L / Real.log (sieveSift M))^2 *
        Real.exp (2 * mertensGapConst) := by
    have hexp : Real.exp (-mertensGapConst)^2 = (Real.exp (2*mertensGapConst))⁻¹ := by
      rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-mertensGapConst) = -(2*mertensGapConst) by push_cast; ring,
        Real.exp_neg]
    rw [mul_pow, hexp]
    field_simp
  exact hmain.trans_eq heq

private theorem high_sieve_remainder {M L : ℕ} (hM : 1 ≤ M) (hL : 2 ≤ L) :
    (∑ e ∈ (rangePrimorial L (sieveSift M)).divisors,
      if (e : ℝ) ≤ sieveLevel M then (6 : ℝ)^e.primeFactors.card else 0) ≤
        2*(M : ℝ)^((3 : ℝ)/4) := by
  have hrem := sieve_remainder_le (P₁ := L) (h := sieveSift M) hL (one_le_sieveLevel hM)
  have hrem' : (∑ e ∈ (rangePrimorial L (sieveSift M)).divisors,
        if (e : ℝ) ≤ sieveLevel M then (6 : ℝ)^e.primeFactors.card else 0) ≤
      2 * (M : ℝ)^((3 : ℝ)/4) := by
    have hle : (∑ e ∈ (rangePrimorial L (sieveSift M)).divisors,
        if (e : ℝ) ≤ sieveLevel M then (6 : ℝ)^e.primeFactors.card else 0) ≤
        ∑ e ∈ (rangePrimorial L (sieveSift M)).divisors,
          if (e : ℝ) ≤ sieveLevel M then 2*(6 : ℝ)^e.primeFactors.card else 0 := by
      apply Finset.sum_le_sum
      intro e he
      split_ifs <;> nlinarith [pow_nonneg (show (0 : ℝ) ≤ 6 by norm_num) e.primeFactors.card]
    have hlev : sieveLevel M^3 = (M : ℝ)^((3 : ℝ)/4) := by
      rw [← Real.rpow_natCast (sieveLevel M) 3, sieveLevel, ← Real.rpow_mul (Nat.cast_nonneg M)]
      norm_num
    exact (hle.trans hrem).trans_eq (by rw [hlev])
  exact hrem'

private theorem critical_fibre_bound {P Q M L A B : ℕ} (hM : 1 ≤ M)
    (hL : 2 ≤ L) (hLh : L ≤ sieveSift M)
    (hlogh : 20 * mertensFirstConst ≤ Real.log (sieveSift M))
    (hA : 0 < A) (hB : 0 < B) (hcop : A.Coprime B)
    (v : ℤ) (hv : v ≠ 0)
    (hd : 2 * Real.log (v.natAbs * A * B) ≤ (L : ℝ) * Real.log L) :
    ((primeDilationPairs P Q A B (sieveSift M) v).card : ℝ) ≤
      1 + 4 * ((P / B : ℕ) : ℝ) * (Real.log L / Real.log (sieveSift M)) ^ 2 *
        Real.exp (2 * mertensGapConst) + 2 * (M : ℝ) ^ ((3 : ℝ) / 4) := by
  have hh : 2 ≤ sieveSift M := hL.trans hLh
  have hd0 : v.natAbs*A*B ≠ 0 := by
    exact Nat.ne_of_gt (mul_pos (mul_pos (Int.natAbs_pos.mpr hv) hA) hB)
  have hmain := high_sieve_main hL hLh hd0 (by simpa only [Nat.cast_mul] using hd)
    (((P/B : ℕ) : ℝ)) (Nat.cast_nonneg _)
  have hfull := card_primeDilationPairs_full_mertens_le P Q hL hA hB hcop v
    (one_le_sieveLevel hM) hh hLh (sieveSift_pow_le hM) hlogh
  exact hfull.trans (add_le_add (add_le_add le_rfl hmain) (high_sieve_remainder hM hL))

private theorem local_anchor (S : Finset (ℕ × ℕ)) {J M a b h : ℕ} {v : ℤ}
    (hb : 0 < b) (hab : a.Coprime b)
    (hS : ∀ x ∈ S, x.1.Prime ∧ x.2.Prime ∧ h < x.1 ∧ h < x.2 ∧
      J ≤ x.2 ∧ x.2 ≤ J+b*M ∧ (b : ℤ)*x.1-(a : ℤ)*x.2 = v)
    (hne : S.Nonempty) :
    ∃ x₀ ∈ S, (S.card : ℝ) ≤ 1 + (((Finset.Icc 1 M).filter (fun n =>
      (a*n+x₀.1).Prime ∧ (b*n+x₀.2).Prime ∧
        h < a*n+x₀.1 ∧ h < b*n+x₀.2)).card : ℝ) := by
  classical
  obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image S Prod.snd hne
  have hparam (x : ℕ × ℕ) (hx : x ∈ S) :
      ∃ n : ℕ, x.1 = x₀.1+a*n ∧ x.2 = x₀.2+b*n := by
    have heq : a*x.2+b*x₀.1 = a*x₀.2+b*x.1 := by
      have hxv := (hS x hx).2.2.2.2.2.2
      have h0v := (hS x₀ hx₀).2.2.2.2.2.2
      exact_mod_cast (show (a : ℤ)*x.2+b*x₀.1 = a*x₀.2+b*x.1 by linarith only [hxv, h0v])
    obtain ⟨n, hnq, hnp⟩ := exists_primeDilation_parameter hb hab (hmin x hx) heq
    exact ⟨n, hnp, hnq⟩
  let φ : ℕ × ℕ → ℕ := fun x => if hx : x ∈ S then Classical.choose (hparam x hx) else 0
  have hφ (x : ℕ × ℕ) (hx : x ∈ S) :
      x.1 = x₀.1+a*φ x ∧ x.2 = x₀.2+b*φ x := by
    dsimp only [φ]
    rw [dif_pos hx]
    exact Classical.choose_spec (hparam x hx)
  let F := (Finset.Icc 1 M).filter (fun n => (a*n+x₀.1).Prime ∧
    (b*n+x₀.2).Prime ∧ h < a*n+x₀.1 ∧ h < b*n+x₀.2)
  have hmaps (x : ℕ × ℕ) (hx : x ∈ S) : φ x ∈ insert 0 F := by
    by_cases hn : φ x = 0
    · simp only [hn, Finset.mem_insert, true_or]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      have hnM : φ x ≤ M := by
        have hxq := (hS x hx).2.2.2.2.2.1
        have h0q := (hS x₀ hx₀).2.2.2.2.1
        have hxφ := (hφ x hx).2
        nlinarith only [hxq, h0q, hxφ, hb]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, hnM⟩, ?_⟩
      have he1 : a*φ x+x₀.1 = x.1 := by rw [Nat.add_comm, ← (hφ x hx).1]
      have he2 : b*φ x+x₀.2 = x.2 := by rw [Nat.add_comm, ← (hφ x hx).2]
      rw [he1, he2]
      exact ⟨(hS x hx).1, (hS x hx).2.1, (hS x hx).2.2.1, (hS x hx).2.2.2.1⟩
  have hinj : Set.InjOn φ (S : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    apply Prod.ext
    · rw [(hφ x hx).1, (hφ y hy).1, hxy]
    · rw [(hφ x hx).2, (hφ y hy).2, hxy]
  have hcard := Finset.card_le_card_of_injOn φ hmaps hinj
  refine ⟨x₀, hx₀, ?_⟩
  have hc : S.card ≤ F.card+1 := hcard.trans (Finset.card_insert_le _ _)
  exact_mod_cast (by omega : S.card ≤ 1+F.card)

private theorem local_fibre_bound (S : Finset (ℕ × ℕ)) {J M L a b : ℕ} {v : ℤ}
    (hM : 1 ≤ M) (hL : 2 ≤ L) (hLh : L ≤ sieveSift M)
    (hlogh : 20*mertensFirstConst ≤ Real.log (sieveSift M))
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (hv : v ≠ 0)
    (hd : 2*Real.log (v.natAbs*a*b) ≤ (L : ℝ)*Real.log L)
    (hS : ∀ x ∈ S, x.1.Prime ∧ x.2.Prime ∧ sieveSift M < x.1 ∧ sieveSift M < x.2 ∧
      J ≤ x.2 ∧ x.2 ≤ J+b*M ∧ (b : ℤ)*x.1-(a : ℤ)*x.2 = v) :
    (S.card : ℝ) ≤ 1+4*(M : ℝ)*(Real.log L/Real.log (sieveSift M))^2*
      Real.exp (2*mertensGapConst)+2*(M : ℝ)^((3 : ℝ)/4) := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨x₀, hx₀, hc⟩ := local_anchor S hb hab hS hne
    have hx := hS x₀ hx₀
    have hdisc : affinePairDiscriminant a b x₀.1 x₀.2 = -v := by
      unfold affinePairDiscriminant
      linarith only [hx.2.2.2.2.2.2]
    have hf := card_primeAffinePair_full_mertens_le M hL ha hb hab hx.1 hx.2.1
      hx.2.2.1 hx.2.2.2.1 (one_le_sieveLevel hM) (hL.trans hLh) hLh
      (sieveSift_pow_le hM) hlogh
    rw [hdisc, Int.natAbs_neg] at hf
    have hd0 : v.natAbs*a*b ≠ 0 := Nat.ne_of_gt (mul_pos (mul_pos (Int.natAbs_pos.mpr hv) ha) hb)
    have hm := high_sieve_main hL hLh hd0 (by simpa only [Nat.cast_mul] using hd)
      (M : ℝ) (Nat.cast_nonneg _)
    have hr := high_sieve_remainder hM hL
    linarith only [hc, hf, hm, hr]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

private theorem gaussian_nat_data {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c*(n : ℝ)^2)) ∧
    (∑' n : ℕ, Real.exp (-c*(n : ℝ)^2)) ≤ 1 + Real.sqrt (Real.pi/c)/2 ∧
    (∑' n : ℕ, Real.exp (-c*((n : ℝ)+1)^2)) ≤ Real.sqrt (Real.pi/c)/2 := by
  have ha : AntitoneOn (fun x : ℝ => Real.exp (-c*x^2)) (Set.Ici 0) := by
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    have hsquare : x^2 ≤ y^2 := (sq_le_sq₀ hx hy).mpr hxy
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left hsquare hc.le)
  have hi := (integrable_exp_neg_mul_sq hc).integrableOn (s := Set.Ioi 0)
  have hn : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ Real.exp (-c*x^2) := fun _ _ => (Real.exp_pos _).le
  refine ⟨ha.summable_of_integrableOn_Ioi_zero hi hn, ?_, ?_⟩
  · have hb := ha.tsum_le_integral hi hn
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, Real.exp_zero,
      integral_gaussian_Ioi] using hb
  · have hb := ha.tsum_add_one_le_integral hi hn
    simpa only [Nat.cast_add, Nat.cast_one, integral_gaussian_Ioi] using hb

private theorem gaussian_integer_sum {c : ℝ} (hc : 0 < c) (s : Finset ℤ) :
    ∑ v ∈ s, Real.exp (-c * (v : ℝ)^2) ≤ 1 + Real.sqrt (Real.pi / c) := by
  obtain ⟨hs, hb0, hb1⟩ := gaussian_nat_data hc
  have hs1 : Summable (fun n : ℕ => Real.exp (-c*((n : ℝ)+1)^2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  have hneg (n : ℕ) : Real.exp (-c * ((-(n+1) : ℤ) : ℝ)^2) =
      Real.exp (-c*((n : ℝ)+1)^2) := by
    congr 1
    push_cast
    ring
  have hsneg : Summable (fun n : ℕ => Real.exp (-c * ((-(n+1) : ℤ) : ℝ)^2)) := by
    simpa only [hneg] using hs1
  have hsnat : Summable (fun n : ℕ => Real.exp (-c * ((n : ℤ) : ℝ)^2)) := by
    simpa only [Int.cast_natCast] using hs
  have hsi : Summable (fun v : ℤ => Real.exp (-c * (v : ℝ)^2)) :=
    Summable.of_nat_of_neg_add_one (f := fun v : ℤ => Real.exp (-c*(v : ℝ)^2)) hsnat hsneg
  have hsum := hsi.sum_le_tsum s (fun _ _ => (Real.exp_pos _).le)
  have ht := tsum_of_nat_of_neg_add_one (f := fun v : ℤ => Real.exp (-c*(v : ℝ)^2)) hsnat hsneg
  simp only [hneg, Int.cast_natCast] at ht
  rw [ht] at hsum
  linarith only [hsum, hb0, hb1]

private theorem gaussian_integer_scaled {B : ℝ} (hB : 1 ≤ B) (s : Finset ℤ) :
    ∑ v ∈ s, Real.exp (-((v : ℝ)^2 / (16*B^2))) ≤ (1+4*Real.sqrt Real.pi)*B := by
  have hB0 : 0 < B := by linarith
  have hc : 0 < 1/(16*B^2) := by positivity
  have hh := gaussian_integer_sum hc s
  have hsqrt : Real.sqrt (Real.pi / (1/(16*B^2))) = 4*Real.sqrt Real.pi*B := by
    rw [div_div_eq_mul_div, div_one, show Real.pi*(16*B^2) = Real.pi*(4*B)^2 by ring,
      Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq (by positivity)]
    ring
  rw [hsqrt] at hh
  have heq : (fun v : ℤ => Real.exp (-(1/(16*B^2))*(v : ℝ)^2)) =
      (fun v : ℤ => Real.exp (-((v : ℝ)^2/(16*B^2)))) := by
    ext v
    congr 1
    ring
  rw [heq] at hh
  nlinarith only [hh, hB]

private theorem gaussian_fibre_sum {s : Finset (ℕ × ℕ)} (f : ℕ × ℕ → ℤ)
    {D B : ℝ} (hD : 0 ≤ D) (hB : 1 ≤ B)
    (hf : ∀ v ∈ s.image f, ((s.filter (fun x => f x = v)).card : ℝ) ≤ D) :
    ∑ x ∈ s, Real.exp (-((f x : ℝ)^2/(16*B^2))) ≤ D*(1+4*Real.sqrt Real.pi)*B := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image f) (g := f) (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    (fun x => Real.exp (-((f x : ℝ)^2/(16*B^2))))]
  calc
    _ ≤ ∑ v ∈ s.image f, D*Real.exp (-((v : ℝ)^2/(16*B^2))) := by
      apply Finset.sum_le_sum
      intro v hv
      have heq : (∑ x ∈ s.filter (fun x => f x=v), Real.exp (-((f x : ℝ)^2/(16*B^2)))) =
          ((s.filter (fun x => f x=v)).card : ℝ)*Real.exp (-((v : ℝ)^2/(16*B^2))) := by
        calc
          _ = ∑ _x ∈ s.filter (fun x => f x=v), Real.exp (-((v : ℝ)^2/(16*B^2))) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [(Finset.mem_filter.mp hx).2]
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [heq]
      exact mul_le_mul_of_nonneg_right (hf v hv) (Real.exp_pos _).le
    _ = D * ∑ v ∈ s.image f, Real.exp (-((v : ℝ)^2/(16*B^2))) := (Finset.mul_sum _ _ _).symm
    _ ≤ D * ((1+4*Real.sqrt Real.pi)*B) := mul_le_mul_of_nonneg_left (gaussian_integer_scaled hB _) hD
    _ = _ := by ring

private theorem band_determinant {N A B p q : ℕ}
    (_hN : 1 ≤ N) (hA : 0 < A) (hAB : A ≤ B) (hBN : B ≤ N)
    (hcop : A.Coprime B) (hne : A ≠ B)
    (hp : p ∈ primeProfileBand (N : ℝ)) (hq : q ∈ primeProfileBand (N : ℝ)) :
    (A : ℤ)*p-(B : ℤ)*q ≠ 0 ∧ ((A : ℤ)*p-(B : ℤ)*q).natAbs ≤ 4*N*B := by
  obtain ⟨hpp,hpN,hp2⟩ := primeProfileBand_mem (Nat.cast_nonneg N) hp
  obtain ⟨_,hqN,hq2⟩ := primeProfileBand_mem (Nat.cast_nonneg N) hq
  have hpN' : N < p := by exact_mod_cast hpN
  have hp2' : p ≤ 2*N := by exact_mod_cast hp2
  have hq2' : q ≤ 2*N := by exact_mod_cast hq2
  have hAp : A*p ≤ 2*N*B := by nlinarith only [Nat.mul_le_mul_right p hAB, Nat.mul_le_mul_left B hp2']
  have hBq : B*q ≤ 2*N*B := by nlinarith only [Nat.mul_le_mul_left B hq2']
  constructor
  · intro hv
    have heq : A*p = B*q := by exact_mod_cast sub_eq_zero.mp hv
    have hd : B ∣ p := hcop.symm.dvd_of_dvd_mul_left (heq ▸ dvd_mul_right B q)
    obtain hb | hb := hpp.eq_one_or_self_of_dvd B hd
    · exact hne (by omega)
    · omega
  · have hh := Int.natAbs_sub_le ((A : ℤ)*p) ((B : ℤ)*q)
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at hh
    nlinarith only [hh, hAp, hBq]

private def fibreBound (N M L B : ℕ) : ℝ :=
  1 + 4 * (((2*N)/B : ℕ) : ℝ) * (Real.log L / Real.log (sieveSift M))^2 *
    Real.exp (2*mertensGapConst) + 2*(M : ℝ)^((3 : ℝ)/4)

private theorem fibreBound_nonneg (N M L B : ℕ) : 0 ≤ fibreBound N M L B := by
  unfold fibreBound
  positivity

private theorem full_band_fibre_bound {N M L A B : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hMN : sieveSift M ≤ N)
    (hL : 2 ≤ L) (hLh : L ≤ sieveSift M)
    (hlogh : 20*mertensFirstConst ≤ Real.log (sieveSift M))
    (hA : 0 < A) (hAB : A ≤ B) (hBN : B ≤ N)
    (hcop : A.Coprime B) (hne : A ≠ B)
    (hd : 2*Real.log ((4*N*B^3 : ℕ) : ℝ) ≤ (L : ℝ)*Real.log L)
    (v : ℤ) (hv : v ∈ ((primeProfileBand (N : ℝ)).product
      (primeProfileBand (N : ℝ))).image (fun x => (A : ℤ)*x.1-(B : ℤ)*x.2)) :
    ((((primeProfileBand (N : ℝ)).product (primeProfileBand (N : ℝ))).filter
      (fun x => (A : ℤ)*x.1-(B : ℤ)*x.2 = v)).card : ℝ) ≤ fibreBound N M L B := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hx
  obtain ⟨hv0,hvbound⟩ := band_determinant hN hA hAB hBN hcop hne hp hq
  have hB : 0 < B := hA.trans_le hAB
  have hdpos : 0 < ((A : ℤ)*x.1-(B : ℤ)*x.2).natAbs*A*B :=
    mul_pos (mul_pos (Int.natAbs_pos.mpr hv0) hA) hB
  have hdbound : ((A : ℤ)*x.1-(B : ℤ)*x.2).natAbs*A*B ≤ 4*N*B^3 := by
    calc
      _ ≤ (4*N*B)*B*B := Nat.mul_le_mul_right B (Nat.mul_le_mul hvbound hAB)
      _ = _ := by ring
  have hdlog : 2*Real.log ((((A : ℤ)*x.1-(B : ℤ)*x.2).natAbs : ℝ)*A*B) ≤
      (L : ℝ)*Real.log L := by
    have hh := Real.log_le_log (y := ((4*N*B^3 : ℕ) : ℝ)) (by exact_mod_cast hdpos : (0 : ℝ) <
      (((A : ℤ)*x.1-(B : ℤ)*x.2).natAbs*A*B : ℕ)) (by exact_mod_cast hdbound)
    push_cast at hh
    push_cast at hd
    linarith only [hh,hd]
  have hc := critical_fibre_bound (P := 2*N) (Q := 2*N) hM hL hLh hlogh hA hB
    hcop ((A : ℤ)*x.1-(B : ℤ)*x.2) hv0 hdlog
  apply le_trans ?_ hc
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro y hy
  obtain ⟨hym,hyv⟩ := Finset.mem_filter.mp hy
  obtain ⟨hy1,hy2⟩ := Finset.mem_product.mp hym
  obtain ⟨hyp,hyN,hyU⟩ := primeProfileBand_mem (Nat.cast_nonneg N) hy1
  obtain ⟨hyq,hyN',hyU'⟩ := primeProfileBand_mem (Nat.cast_nonneg N) hy2
  have hyl : N < y.1 := by exact_mod_cast hyN
  have hyu : y.1 ≤ 2*N := by exact_mod_cast hyU
  have hyl' : N < y.2 := by exact_mod_cast hyN'
  have hyu' : y.2 ≤ 2*N := by exact_mod_cast hyU'
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega,hyu⟩,Finset.mem_Icc.mpr ⟨by omega,hyu'⟩⟩,
      hyp,hyq,by omega,by omega,hyv⟩

private theorem full_band_determinant_gaussian {N M L A B : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hMN : sieveSift M ≤ N)
    (hL : 2 ≤ L) (hLh : L ≤ sieveSift M)
    (hlogh : 20*mertensFirstConst ≤ Real.log (sieveSift M))
    (hA : 0 < A) (hAB : A ≤ B) (hBN : B ≤ N)
    (hcop : A.Coprime B) (hne : A ≠ B)
    (hd : 2*Real.log ((4*N*B^3 : ℕ) : ℝ) ≤ (L : ℝ)*Real.log L) :
    ∑ x ∈ (primeProfileBand (N : ℝ)).product (primeProfileBand (N : ℝ)),
      Real.exp (-((((A : ℤ)*x.1-(B : ℤ)*x.2 : ℤ) : ℝ)^2/(16*(B : ℝ)^2))) ≤
        fibreBound N M L B * (1+4*Real.sqrt Real.pi) * B := by
  apply gaussian_fibre_sum _ (fibreBound_nonneg N M L B)
    (by exact_mod_cast (by omega : 1 ≤ B))
  intro v hv
  exact full_band_fibre_bound hN hM hMN hL hLh hlogh hA hAB hBN hcop hne hd v hv

private def pairFreq (A B p q : ℕ) : ℝ := Real.log ((A : ℝ)*p)-Real.log ((B : ℝ)*q)

private theorem log_gaussian_le_determinant {N A B p q : ℕ}
    (hN : 1 ≤ N) (hA : 0 < A) (hAB : A ≤ B)
    (hp : p ∈ primeProfileBand (N : ℝ)) (hq : q ∈ primeProfileBand (N : ℝ)) :
    Real.exp (-Real.pi*((N : ℝ)*pairFreq A B p q)^2) ≤
      Real.exp (-((((A : ℤ)*p-(B : ℤ)*q : ℤ) : ℝ)^2/(16*(B : ℝ)^2))) := by
  obtain ⟨_,hpN,hp2⟩ := primeProfileBand_mem (Nat.cast_nonneg N) hp
  obtain ⟨_,hqN,hq2⟩ := primeProfileBand_mem (Nat.cast_nonneg N) hq
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hABR : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hBR : (0 : ℝ) < B := hAR.trans_le hABR
  have hp0 : (0 : ℝ) < p := hN0.trans hpN
  have hq0 : (0 : ℝ) < q := hN0.trans hqN
  have hmax : max ((A : ℝ)*p) ((B : ℝ)*q) ≤ 2*N*B := by
    apply max_le
    · nlinarith only [mul_le_mul_of_nonneg_right hABR hp0.le,
        mul_le_mul_of_nonneg_left hp2 hBR.le]
    · nlinarith only [mul_le_mul_of_nonneg_left hq2 hBR.le]
  have hg := abs_sub_div_max_le_abs_log_sub_log (mul_pos hAR hp0) (mul_pos hBR hq0)
  have hm0 : 0 < max ((A : ℝ)*p) ((B : ℝ)*q) := (mul_pos hAR hp0).trans_le (le_max_left _ _)
  have hgap := (div_le_iff₀ hm0).mp hg
  have hgap' := hgap.trans (mul_le_mul_of_nonneg_left hmax (abs_nonneg _))
  have hh : |(((A : ℤ)*p-(B : ℤ)*q : ℤ) : ℝ)| ≤ 2*(B : ℝ)*|(N : ℝ)*pairFreq A B p q| := by
    push_cast
    dsimp [pairFreq]
    rw [abs_mul,abs_of_pos hN0]
    nlinarith only [hgap']
  have hsquare := pow_le_pow_left₀ (abs_nonneg _) hh 2
  simp only [mul_pow, sq_abs] at hsquare
  have hqbound : ((((A : ℤ)*p-(B : ℤ)*q : ℤ) : ℝ)^2/(16*(B : ℝ)^2)) ≤
      ((N : ℝ)*pairFreq A B p q)^2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16*(B : ℝ)^2)).mpr
    nlinarith only [hsquare, mul_nonneg (sq_nonneg (B : ℝ)) (sq_nonneg ((N : ℝ)*pairFreq A B p q))]
  have hpi := mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
    (sq_nonneg ((N : ℝ)*pairFreq A B p q))
  apply Real.exp_le_exp.mpr
  linarith only [hqbound,hpi]

private def bandCoeff (N : ℝ) (p : ℕ) : ℂ := smoothAFECutoff ((p : ℝ)/N)/(Real.sqrt p : ℂ)

private theorem bandCoeff_norm {N : ℝ} (hN : 0 < N) {p : ℕ} (hp : p ∈ primeProfileBand N) :
    ‖bandCoeff N p‖ ≤ 1/Real.sqrt N := by
  have hpN := (primeProfileBand_mem hN.le hp).2.1
  have hp0 : (0 : ℝ) < p := hN.trans hpN
  have hs0 := Real.sqrt_pos.mpr hp0
  unfold bandCoeff
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  exact (div_le_div_of_nonneg_right (norm_smoothAFECutoff_le_one (div_pos hp0 hN)) hs0.le).trans
    (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hN) (Real.sqrt_le_sqrt hpN.le))

private def spectralPair (N : ℝ) (A B : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
    bandCoeff N p * (starRingEnd ℂ) (bandCoeff N q) *
      Complex.exp (((pairFreq A B p q*t : ℝ) : ℂ)*Complex.I) *
      (Real.exp (-Real.pi*(N*pairFreq A B p q)^2) : ℂ)

private theorem spectral_pair_bound {N M L A B : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hMN : sieveSift M ≤ N)
    (hL : 2 ≤ L) (hLh : L ≤ sieveSift M)
    (hlogh : 20*mertensFirstConst ≤ Real.log (sieveSift M))
    (hA : 0 < A) (hAB : A ≤ B) (hBN : B ≤ N)
    (hcop : A.Coprime B) (hne : A ≠ B)
    (hd : 2*Real.log ((4*N*B^3 : ℕ) : ℝ) ≤ (L : ℝ)*Real.log L) (t : ℝ) :
    ‖spectralPair (N : ℝ) A B t‖ ≤ fibreBound N M L B*(1+4*Real.sqrt Real.pi)*B/N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcoef (p q : ℕ) (hp : p ∈ primeProfileBand (N : ℝ))
      (hq : q ∈ primeProfileBand (N : ℝ)) :
      ‖bandCoeff N p * (starRingEnd ℂ) (bandCoeff N q)‖ ≤ 1/(N : ℝ) := by
    rw [norm_mul, RCLike.norm_conj]
    have hb := mul_le_mul (bandCoeff_norm hN0 hp) (bandCoeff_norm hN0 hq) (norm_nonneg _) (by positivity)
    apply hb.trans_eq
    rw [one_div_mul_one_div,← pow_two,Real.sq_sqrt hN0.le]
  have hterm (p q : ℕ) (hp : p ∈ primeProfileBand (N : ℝ))
      (hq : q ∈ primeProfileBand (N : ℝ)) :
      ‖bandCoeff N p * (starRingEnd ℂ) (bandCoeff N q) *
        Complex.exp (((pairFreq A B p q*t : ℝ) : ℂ)*Complex.I) *
        (Real.exp (-Real.pi*((N : ℝ)*pairFreq A B p q)^2) : ℂ)‖ ≤
        (1/(N : ℝ))*Real.exp (-((((A : ℤ)*p-(B : ℤ)*q : ℤ) : ℝ)^2/(16*(B : ℝ)^2))) := by
    rw [norm_mul,norm_mul,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,Complex.ofReal_im,
      Complex.I_im,sub_self,Real.exp_zero,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hcoef p q hp hq) (log_gaussian_le_determinant hN hA hAB hp hq)
      (Real.exp_pos _).le (by positivity)
  have hsum : ‖spectralPair (N : ℝ) A B t‖ ≤
      (1/(N : ℝ)) * ∑ x ∈ (primeProfileBand (N : ℝ)).product (primeProfileBand (N : ℝ)),
        Real.exp (-((((A : ℤ)*x.1-(B : ℤ)*x.2 : ℤ) : ℝ)^2/(16*(B : ℝ)^2))) := by
    unfold spectralPair
    apply (norm_sum_le _ _).trans
    rw [Finset.product_eq_sprod,Finset.sum_product,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun q hq => hterm p q hp hq)
  have hb := mul_le_mul_of_nonneg_left
    (full_band_determinant_gaussian hN hM hMN hL hLh hlogh hA hAB hBN hcop hne hd) (by positivity : 0 ≤ 1/(N : ℝ))
  exact hsum.trans (by simpa only [one_div_mul_eq_div] using hb)

private def lowerCutoff (K : ℕ) : ℕ := ⌈16*Real.log (K : ℝ)⌉₊

private theorem cutoff_conditions :
    ∀ᶠ K : ℕ in atTop,
      2 ≤ K ∧ 2 ≤ lowerCutoff K ∧ lowerCutoff K ≤ sieveSift K ∧
      20*mertensFirstConst ≤ Real.log (sieveSift K) ∧
      Real.log (K : ℝ)/288 ≤ Real.log (sieveSift K) ∧
      2*Real.log ((4*K^5 : ℕ) : ℝ) ≤ (lowerCutoff K : ℝ)*Real.log (lowerCutoff K) ∧
      Real.log (lowerCutoff K) ≤ Real.log 17 + Real.log (Real.log K) ∧
      1 ≤ Real.log (K : ℝ) := by
  have hlog : Tendsto (fun K : ℕ => Real.log (K : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun K : ℕ => (16*Real.log (K : ℝ)+2)/(K : ℝ)^((1 : ℝ)/144)) atTop (𝓝 0) := by
    have hl := ((isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)/144) 1 (by norm_num)).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
    have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/144)).comp tendsto_natCast_atTop_atTop
    have hc := hp.const_div_atTop (2 : ℝ)
    have hs := (hl.const_mul (16 : ℝ)).add hc
    simp only [Real.rpow_one,mul_zero,add_zero,Function.comp_def] at hs
    apply hs.congr'
    filter_upwards [] with K
    ring
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually_ge_atTop 1,
    hlog.eventually_ge_atTop (Real.exp 1), hlog.eventually_ge_atTop (Real.log 4),
    hlog.eventually_ge_atTop (288*Real.log 2),
    hlog.eventually_ge_atTop (5760*mertensFirstConst),
    hratio.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with K hK hlog1 hloge hlog4 hlog2 hlogC hsmall
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hLlo : 16*Real.log (K : ℝ) ≤ (lowerCutoff K : ℝ) := Nat.le_ceil _
  have hLup : (lowerCutoff K : ℝ) < 16*Real.log (K : ℝ)+1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hL2 : 2 ≤ lowerCutoff K := by
    have hh : (2 : ℝ) ≤ lowerCutoff K := by linarith only [hLlo,hlog1]
    exact_mod_cast hh
  have hL0 : (0 : ℝ) < lowerCutoff K := by exact_mod_cast (by omega : 0 < lowerCutoff K)
  have hLh : lowerCutoff K ≤ sieveSift K := by
    have hh := (div_lt_one (Real.rpow_pos_of_pos hK0 _)).mp hsmall
    have hf := Nat.lt_floor_add_one ((K : ℝ)^((1 : ℝ)/144))
    change (K : ℝ)^((1 : ℝ)/144) < (sieveSift K : ℝ)+1 at hf
    have hle : (lowerCutoff K : ℝ) ≤ sieveSift K := by linarith only [hh,hf,hLup]
    exact_mod_cast hle
  have hs2 : 2 ≤ sieveSift K := hL2.trans hLh
  have hslog := log_sieveSift_ge hK hlog2 hs2
  have hlogL1 : 1 ≤ Real.log (lowerCutoff K) := by
    apply (Real.le_log_iff_exp_le hL0).mpr
    linarith only [hLlo,hloge,Real.exp_pos (1 : ℝ)]
  have hdisc : 2*Real.log ((4*K^5 : ℕ) : ℝ) ≤ (lowerCutoff K : ℝ)*Real.log (lowerCutoff K) := by
    have hh := mul_le_mul_of_nonneg_left hlogL1 hL0.le
    push_cast
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero _ hK0.ne'),Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hh,hLlo,hlog4]
  have hlogLup : Real.log (lowerCutoff K) ≤ Real.log 17 + Real.log (Real.log K) := by
    have hle : (lowerCutoff K : ℝ) ≤ 17*Real.log (K : ℝ) := by linarith only [hLup,hlog1]
    have hh := Real.log_le_log hL0 hle
    rwa [Real.log_mul (by norm_num : (17 : ℝ) ≠ 0) (by linarith : Real.log (K : ℝ) ≠ 0)] at hh
  exact ⟨hK,hL2,hLh,by linarith only [hslog,hlogC],hslog,hdisc,hlogLup,hlog1⟩

private theorem cutoff_ratio_limit :
    Tendsto (fun K : ℕ => Real.log (K : ℝ) *
      (Real.log (lowerCutoff K)/Real.log (sieveSift K))^2) atTop (𝓝 0) := by
  have hlog : Tendsto (fun K : ℕ => Real.log (K : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hl2 : Tendsto (fun K : ℕ => (Real.log (Real.log (K : ℝ)))^2 / Real.log K) atTop (𝓝 0) := by
    have hh := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) 2 (by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_two,Real.rpow_one,Function.comp_def] using hh.comp hlog
  have hc : Tendsto (fun K : ℕ => (Real.log (17 : ℝ))^2 / Real.log K) atTop (𝓝 0) :=
    hlog.const_div_atTop _
  have hmajor := (hc.add hl2).const_mul (2*288^2 : ℝ)
  simp only [add_zero,mul_zero] at hmajor
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [cutoff_conditions] with K hK
    obtain ⟨_,_,_,_,_,_,_,hl⟩ := hK
    exact mul_nonneg (by linarith only [hl]) (sq_nonneg _)
  · filter_upwards [cutoff_conditions] with K hK
    obtain ⟨_,hL,hLh,_,hs,_,hu,hlog1⟩ := hK
    have hlog0 : 0 < Real.log (K : ℝ) := by linarith
    have hs0 : 0 < Real.log (sieveSift K) := by linarith
    have hLl0 : 0 ≤ Real.log (lowerCutoff K) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ lowerCutoff K))
    have hu0 : 0 ≤ Real.log 17 + Real.log (Real.log K) := hLl0.trans hu
    have hdiv : Real.log (lowerCutoff K)/Real.log (sieveSift K) ≤
        288*(Real.log 17+Real.log (Real.log K))/Real.log K := by
      calc
        _ ≤ Real.log (lowerCutoff K)/(Real.log (K : ℝ)/288) :=
          div_le_div_of_nonneg_left hLl0 (by positivity) hs
        _ ≤ (Real.log 17+Real.log (Real.log K))/(Real.log (K : ℝ)/288) :=
          div_le_div_of_nonneg_right hu (by positivity)
        _ = _ := by ring
    have hsq := pow_le_pow_left₀ (div_nonneg hLl0 hs0.le) hdiv 2
    have hm := mul_le_mul_of_nonneg_left hsq hlog0.le
    have hquad : (Real.log 17+Real.log (Real.log (K : ℝ)))^2 ≤
        2*((Real.log 17)^2+(Real.log (Real.log (K : ℝ)))^2) := by
      nlinarith only [sq_nonneg (Real.log 17-Real.log (Real.log (K : ℝ)))]
    apply hm.trans
    calc
      _ = 288^2*(Real.log 17+Real.log (Real.log (K : ℝ)))^2/Real.log K := by field_simp
      _ ≤ 288^2*(2*((Real.log 17)^2+(Real.log (Real.log (K : ℝ)))^2))/Real.log K :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hquad (by positivity)) hlog0.le
      _ = _ := by ring

/-- Gaussian height average of the full prime band against a rational logarithmic twist. -/
def average (N : ℝ) (A B : ℕ) (t : ℝ) : ℂ :=
  ∫ u : ℝ, (Real.exp (-Real.pi*u^2) : ℂ) *
    Complex.exp ((((Real.log A-Real.log B)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
    primeGaussianChiField 1 N (t+2*Real.pi*N*u) *
    (starRingEnd ℂ) (primeGaussianChiField 1 N (t+2*Real.pi*N*u))

private theorem pair_phase (N t u : ℝ) {A B p q : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hp : 0 < p) (hq : 0 < q) :
    (Real.exp (-Real.pi*u^2) : ℂ) *
      Complex.exp ((((Real.log A-Real.log B)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
      (bandCoeff N p * Complex.exp (((Real.log p*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I)) *
      (starRingEnd ℂ) (bandCoeff N q * Complex.exp (((Real.log q*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I)) =
    (bandCoeff N p*(starRingEnd ℂ) (bandCoeff N q)*Complex.exp (((pairFreq A B p q*t : ℝ) : ℂ)*Complex.I)) *
      bourgainGaussianFourierIntegrand (N*pairFreq A B p q) u := by
  have hf : pairFreq A B p q = Real.log A+Real.log p-Real.log B-Real.log q := by
    unfold pairFreq
    rw [Real.log_mul (by exact_mod_cast hA.ne') (by exact_mod_cast hp.ne'),
      Real.log_mul (by exact_mod_cast hB.ne') (by exact_mod_cast hq.ne')]
    ring
  have hpj : (starRingEnd ℂ) (Complex.exp (((Real.log q*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I)) =
      Complex.exp (-(((Real.log q*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I)) := by
    rw [← Complex.exp_conj]
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg]
  have hphase :
      Complex.exp ((((Real.log A-Real.log B)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
      Complex.exp (((Real.log p*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
      Complex.exp (-(((Real.log q*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I)) =
      Complex.exp (((pairFreq A B p q*t : ℝ) : ℂ)*Complex.I) *
      Complex.exp (2*(Real.pi : ℂ)*Complex.I*((N*pairFreq A B p q : ℝ) : ℂ)*(u : ℂ)) := by
    rw [← Complex.exp_add,← Complex.exp_add,← Complex.exp_add]
    congr 1
    rw [hf]
    push_cast
    ring
  have hg : (Real.exp (-Real.pi*u^2) : ℂ) = Complex.exp (-((Real.pi : ℂ)*(u : ℂ)^2)) := by
    rw [Complex.ofReal_exp]
    push_cast
    congr 1
    ring
  rw [map_mul,hpj,hg]
  unfold bourgainGaussianFourierIntegrand
  calc
    _ = (bandCoeff N p*(starRingEnd ℂ) (bandCoeff N q)) *
        Complex.exp (-((Real.pi : ℂ)*(u : ℂ)^2)) *
        (Complex.exp ((((Real.log A-Real.log B)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
        Complex.exp (((Real.log p*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
        Complex.exp (-(((Real.log q*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I))) := by ring
    _ = _ := by rw [hphase]; ring

private theorem pairAverage_eq_spectral {N : ℝ} (hN : 0 < N) {A B : ℕ}
    (hA : 0 < A) (hB : 0 < B) (t : ℝ) : average N A B t = spectralPair N A B t := by
  have hpoint (u : ℝ) :
      (Real.exp (-Real.pi*u^2) : ℂ) *
        Complex.exp ((((Real.log A-Real.log B)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
        primeGaussianChiField 1 N (t+2*Real.pi*N*u) *
        (starRingEnd ℂ) (primeGaussianChiField 1 N (t+2*Real.pi*N*u)) =
      ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
        (bandCoeff N p*(starRingEnd ℂ) (bandCoeff N q)*Complex.exp (((pairFreq A B p q*t : ℝ) : ℂ)*Complex.I)) *
          bourgainGaussianFourierIntegrand (N*pairFreq A B p q) u := by
    simp only [primeGaussianChiField,one_mul,map_sum,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    have hp0 : 0 < p := by exact_mod_cast hN.trans (primeProfileBand_mem hN.le hp).2.1
    have hq0 : 0 < q := by exact_mod_cast hN.trans (primeProfileBand_mem hN.le hq).2.1
    exact pair_phase N t u hA hB hp0 hq0
  have hi (p q : ℕ) : MeasureTheory.Integrable (fun u : ℝ =>
      (bandCoeff N p*(starRingEnd ℂ) (bandCoeff N q)*Complex.exp (((pairFreq A B p q*t : ℝ) : ℂ)*Complex.I)) *
        bourgainGaussianFourierIntegrand (N*pairFreq A B p q) u) :=
    (integrable_bourgainGaussianFourierIntegrand _).const_mul _
  unfold average
  simp_rw [hpoint]
  rw [MeasureTheory.integral_finsetSum _ (fun p _ => MeasureTheory.integrable_finsetSum _ (fun q _ => hi p q))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [MeasureTheory.integral_finsetSum _ (fun q _ => hi p q)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [MeasureTheory.integral_const_mul,integral_bourgainGaussianFourierIntegrand]

private def growthError (K : ℕ) : ℝ :=
  (Real.log (lowerCutoff K)/Real.log (sieveSift K))^2+(K : ℝ)^(-(1 : ℝ)/4)

private theorem growthError_log_limit :
    Tendsto (fun K : ℕ => Real.log (K : ℝ)*growthError K) atTop (𝓝 0) := by
  have hh := ((isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)/4) 1 (by norm_num)).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  have htail : Tendsto (fun K : ℕ => Real.log (K : ℝ)*(K : ℝ)^(-(1 : ℝ)/4)) atTop (𝓝 0) := by
    simp only [Real.rpow_one,Function.comp_def] at hh
    apply hh.congr'
    filter_upwards [] with K
    rw [show -(1 : ℝ)/4 = -((1 : ℝ)/4) by ring,Real.rpow_neg (Nat.cast_nonneg K)]
    ring
  simpa only [growthError,mul_add,add_zero] using cutoff_ratio_limit.add htail

private theorem spectral_pair_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ K : ℕ in atTop, ∀ A B : ℕ, 0 < A → A < B → B ≤ K →
      A.Coprime B → ∀ t : ℝ, ‖spectralPair ((K : ℝ)^2) A B t‖ ≤ C*growthError K := by
  let E := Real.exp (2*mertensGapConst)
  let G := 1+4*Real.sqrt Real.pi
  have hE : 0 < E := Real.exp_pos _
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨G*(8*E+3),by positivity,?_⟩
  filter_upwards [cutoff_conditions] with K hK
  obtain ⟨hK,hL,hLh,hlogh,hslog,hdisc,hLup,hlog1⟩ := hK
  intro A B hA hAB hBK hcop t
  have hK1 : 1 ≤ K := by omega
  have hK2 : K ≤ K^2 := by nlinarith only [hK]
  have hN : 1 ≤ K^2 := hK1.trans hK2
  have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hB : 0 < B := by omega
  have hK0 : 0 < K := by omega
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hBKR : (B : ℝ) ≤ K := by exact_mod_cast hBK
  have hd : 2*Real.log ((4*(K^2)*B^3 : ℕ) : ℝ) ≤ (lowerCutoff K : ℝ)*Real.log (lowerCutoff K) := by
    have hh : 4*(K^2)*B^3 ≤ 4*K^5 := by
      calc
        _ ≤ 4*(K^2)*K^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hBK _)
        _ = _ := by ring
    have hl := Real.log_le_log (y := ((4*K^5 : ℕ) : ℝ)) (by positivity : (0 : ℝ) < ((4*(K^2)*B^3 : ℕ) : ℝ))
      (by exact_mod_cast hh)
    linarith only [hl,hdisc]
  have hb := spectral_pair_bound hN hK1 ((sieveSift_le hK1).trans hK2) hL hLh hlogh
    hA hAB.le (hBK.trans hK2) hcop (Nat.ne_of_lt hAB) hd t
  push_cast at hb
  apply hb.trans
  have hf : ((((2*K^2)/B : ℕ) : ℝ)) ≤ 2*(K : ℝ)^2/B := by
    have hh : (((2*K^2/B : ℕ) : ℝ)) ≤ ((2*K^2 : ℕ) : ℝ)/(B : ℝ) := Nat.cast_div_le
    push_cast at hh
    exact hh
  let R := (Real.log (lowerCutoff K)/Real.log (sieveSift K))^2
  have hR : 0 ≤ R := sq_nonneg _
  have hfb : fibreBound (K^2) K (lowerCutoff K) B ≤
      1+8*(K : ℝ)^2/(B : ℝ)*R*E+2*(K : ℝ)^((3 : ℝ)/4) := by
    unfold fibreBound
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 4)) hR) hE.le
    change 1+4*(((2*K^2/B : ℕ) : ℝ))*R*E+2*(K : ℝ)^((3 : ℝ)/4) ≤ _
    rw [show 4*(2*(K : ℝ)^2/(B : ℝ))*R*E = 8*(K : ℝ)^2/(B : ℝ)*R*E by ring] at hm
    linarith only [hm]
  have hfirst : fibreBound (K^2) K (lowerCutoff K) B*G*B/(K : ℝ)^2 ≤
      G*((1+2*(K : ℝ)^((3 : ℝ)/4))/(K : ℝ)+8*R*E) := by
    have hmul := mul_le_mul_of_nonneg_right hfb (by positivity : 0 ≤ G*(B : ℝ)/(K : ℝ)^2)
    have hsmall := mul_le_mul_of_nonneg_left hBKR (by positivity : 0 ≤ 1+2*(K : ℝ)^((3 : ℝ)/4))
    have hdiv := div_le_div_of_nonneg_right hsmall (by positivity : 0 ≤ (K : ℝ)^2)
    have hineq := mul_le_mul_of_nonneg_left hdiv hG.le
    calc
      _ ≤ (1+8*(K : ℝ)^2/(B : ℝ)*R*E+2*(K : ℝ)^((3 : ℝ)/4))*(G*(B : ℝ)/(K : ℝ)^2) := by simpa only [mul_div_assoc,mul_assoc] using hmul
      _ = G*((1+2*(K : ℝ)^((3 : ℝ)/4))*(B : ℝ)/(K : ℝ)^2+8*R*E) := by field_simp; ring
      _ ≤ G*((1+2*(K : ℝ)^((3 : ℝ)/4))*(K : ℝ)/(K : ℝ)^2+8*R*E) := by nlinarith only [hineq]
      _ = _ := by field_simp
  have hpow : (K : ℝ)^((3 : ℝ)/4)/(K : ℝ) = (K : ℝ)^(-(1 : ℝ)/4) := by
    rw [← Real.rpow_sub_one hKR.ne']
    norm_num
  have hinv : 1/(K : ℝ) ≤ (K : ℝ)^(-(1 : ℝ)/4) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hK1 : (1 : ℝ) ≤ K)
      (by norm_num : (-1 : ℝ) ≤ -(1 : ℝ)/4)
    simpa only [Real.rpow_neg_one,one_div] using hh
  have htail : (1+2*(K : ℝ)^((3 : ℝ)/4))/(K : ℝ) ≤ 3*(K : ℝ)^(-(1 : ℝ)/4) := by
    rw [add_div,mul_div_assoc,hpow]
    linarith only [hinv]
  change fibreBound (K^2) K (lowerCutoff K) B*G*B/(K : ℝ)^2 ≤ _
  apply hfirst.trans
  dsimp [growthError]
  change G*(_+8*R*E) ≤ G*(8*E+3)*(R+_)
  have hh := mul_le_mul_of_nonneg_left htail hG.le
  nlinarith only [hh,mul_nonneg hG.le hR,mul_nonneg (mul_nonneg hG.le hE.le) (Real.rpow_nonneg (Nat.cast_nonneg K) (-(1 : ℝ)/4))]

private theorem spectral_pair_swap (N : ℝ) (A B : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (spectralPair N A B t) = spectralPair N B A t := by
  unfold spectralPair
  simp only [map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have hf : pairFreq A B q p = -pairFreq B A p q := by unfold pairFreq; ring
  rw [hf]
  simp only [map_mul,map_neg,Complex.conj_conj,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I,
    Complex.ofReal_neg,neg_mul,mul_neg,neg_neg,neg_sq]
  ring

/-- The literal full Gaussian prime field has negligible critical-height pair
correlation under every nontrivial reduced rational twist with numerator and
denominator at most the square root of the band scale. The height centre is
unrestricted. The vanishing envelope is source-constructed, with no assumed
prime distribution or zero-pair estimate. -/
theorem exists_negligible_error :
    ∃ error : ℕ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ K : ℕ in atTop, ∀ A B : ℕ, 0 < A → 0 < B → A ≤ K → B ≤ K →
        A.Coprime B → A ≠ B → ∀ t : ℝ,
          Real.log ((K : ℝ)^2)*‖average ((K : ℝ)^2) A B t‖ ≤ error K := by
  obtain ⟨C,hC,hbound⟩ := spectral_pair_uniform
  refine ⟨fun K => (2*C)*(Real.log (K : ℝ)*growthError K),?_,?_⟩
  · simpa only [mul_zero] using growthError_log_limit.const_mul (2*C)
  · filter_upwards [hbound,eventually_ge_atTop (2 : ℕ)] with K hK hK2
    intro A B hA hB hAK hBK hcop hne t
    have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    have hlog : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ K))
    have hs : ‖spectralPair ((K : ℝ)^2) A B t‖ ≤ C*growthError K := by
      rcases lt_or_gt_of_ne hne with hab | hba
      · exact hK A B hA hab hBK hcop t
      · have hh := hK B A hB hba hAK hcop.symm t
        have heq := congrArg norm (spectral_pair_swap ((K : ℝ)^2) A B t)
        simpa only [RCLike.norm_conj] using heq.le.trans hh
    rw [pairAverage_eq_spectral (by positivity) hA hB,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*Real.log (K : ℝ))
    nlinarith only [hh]

private theorem connected_determinant {N a b p q : ℕ}
    (_ha : 0 < a) (_hb : 0 < b) (haN : a ≤ N) (hbN : b ≤ N)
    (hab : a.Coprime b) (hne : p ≠ q)
    (hp : p ∈ primeProfileBand (N : ℝ)) (hq : q ∈ primeProfileBand (N : ℝ)) :
    (b : ℤ)*p-(a : ℤ)*q ≠ 0 := by
  obtain ⟨hpp,hpN,_⟩ := primeProfileBand_mem (Nat.cast_nonneg N) hp
  obtain ⟨hqp,hqN,_⟩ := primeProfileBand_mem (Nat.cast_nonneg N) hq
  have hpN' : N < p := by exact_mod_cast hpN
  have hqN' : N < q := by exact_mod_cast hqN
  intro hv
  have heq : b*p = a*q := by exact_mod_cast sub_eq_zero.mp hv
  have hap : a ∣ p := hab.dvd_of_dvd_mul_left (heq ▸ dvd_mul_right a q)
  have hbq : b ∣ q := hab.symm.dvd_of_dvd_mul_left (heq.symm ▸ dvd_mul_right b p)
  have ha1 : a = 1 := (hpp.eq_one_or_self_of_dvd a hap).resolve_right (by omega)
  have hb1 : b = 1 := (hqp.eq_one_or_self_of_dvd b hbq).resolve_right (by omega)
  simp only [ha1,hb1,one_mul] at heq
  exact hne heq

private theorem real_log_gaussian {N p q : ℕ} {β : ℝ}
    (hN : 1 ≤ N) (hβ : 0 < β) (hβ2 : β ≤ 2)
    (hp : p ∈ primeProfileBand (N : ℝ)) (hq : q ∈ primeProfileBand (N : ℝ)) :
    Real.exp (-Real.pi*((N : ℝ)*(Real.log p-Real.log q-Real.log β))^2) ≤
      Real.exp (-((p : ℝ)-β*q)^2/16) := by
  obtain ⟨_,hpN,hp2⟩ := primeProfileBand_mem (Nat.cast_nonneg N) hp
  obtain ⟨_,hqN,hq2⟩ := primeProfileBand_mem (Nat.cast_nonneg N) hq
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp0 := hN0.trans hpN
  have hq0 := hN0.trans hqN
  have hm0 : 0 < max (p : ℝ) (β*q) := hp0.trans_le (le_max_left _ _)
  have hmax : max (p : ℝ) (β*q) ≤ 4*N := by
    apply max_le
    · linarith only [hp2,hN0]
    · nlinarith only [mul_le_mul_of_nonneg_right hβ2 hq0.le,hq2]
  have hg := (div_le_iff₀ hm0).mp (abs_sub_div_max_le_abs_log_sub_log hp0 (mul_pos hβ hq0))
  have hg' := hg.trans (mul_le_mul_of_nonneg_left hmax (abs_nonneg _))
  have heq : Real.log p-Real.log (β*q) = Real.log p-Real.log q-Real.log β := by
    rw [Real.log_mul hβ.ne' hq0.ne']
    ring
  rw [heq] at hg'
  have hgap : |(p : ℝ)-β*q| ≤ 4*|(N : ℝ)*(Real.log p-Real.log q-Real.log β)| := by
    rw [abs_mul,abs_of_pos hN0]
    nlinarith only [hg']
  have hs := pow_le_pow_left₀ (abs_nonneg _) hgap 2
  simp only [mul_pow,sq_abs] at hs
  have hpi := mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
    (sq_nonneg ((N : ℝ)*(Real.log p-Real.log q-Real.log β)))
  apply Real.exp_le_exp.mpr
  nlinarith only [hs,hpi]

private theorem local_kernel {p q J a b : ℕ} {β : ℝ}
    (hb : 0 < b) (_hJ : (J : ℝ) ≤ q)
    (hshift : |((b : ℝ)*β-a)*((q : ℝ)-J)| ≤ b) :
    Real.exp (-((p : ℝ)-β*q)^2/16) ≤ Real.exp 1 *
      Real.exp (-((((b : ℤ)*p-(a : ℤ)*q-⌊((b : ℝ)*β-a)*J⌋ : ℤ) : ℝ)^2 /
        (16*(2*(b : ℝ))^2))) := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  let c : ℝ := ((b : ℝ)*β-a)*J
  have hfloor : |c-(⌊c⌋ : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le c))]
    linarith only [Int.lt_floor_add_one c]
  have hid : (((b : ℤ)*p-(a : ℤ)*q-⌊c⌋ : ℤ) : ℝ) =
      (b : ℝ)*((p : ℝ)-β*q)+((b : ℝ)*β-a)*((q : ℝ)-J)+(c-(⌊c⌋ : ℝ)) := by
    simp only [Int.cast_sub,Int.cast_mul,Int.cast_natCast]
    dsimp only [c]
    ring
  have habs : |(((b : ℤ)*p-(a : ℤ)*q-⌊c⌋ : ℤ) : ℝ)| ≤
      (b : ℝ)*|(p : ℝ)-β*q|+|((b : ℝ)*β-a)*((q : ℝ)-J)|+|c-(⌊c⌋ : ℝ)| := by
    rw [hid]
    apply (abs_add_le _ _).trans
    have ht := add_le_add (abs_add_le ((b : ℝ)*((p : ℝ)-β*q))
      (((b : ℝ)*β-a)*((q : ℝ)-J))) (le_refl |c-(⌊c⌋ : ℝ)|)
    simpa only [abs_mul (b : ℝ),abs_of_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b)] using ht
  have hbound : |(((b : ℤ)*p-(a : ℤ)*q-⌊c⌋ : ℤ) : ℝ)| ≤
      (b : ℝ)*|(p : ℝ)-β*q|+2*b := by linarith only [habs,hshift,hfloor,hb1]
  have hs := pow_le_pow_left₀ (abs_nonneg _) hbound 2
  rw [sq_abs] at hs
  have hquad : (((b : ℤ)*p-(a : ℤ)*q-⌊c⌋ : ℤ) : ℝ)^2 ≤
      2*(b : ℝ)^2*((p : ℝ)-β*q)^2+8*(b : ℝ)^2 := by
    nlinarith only [hs,sq_abs ((p : ℝ)-β*q),sq_nonneg ((b : ℝ)*|(p : ℝ)-β*q|-2*b)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hdiv : (((b : ℤ)*p-(a : ℤ)*q-⌊c⌋ : ℤ) : ℝ)^2/(16*(2*(b : ℝ))^2) ≤
      1+((p : ℝ)-β*q)^2/16 := by
    apply (div_le_iff₀ (by positivity : 0 < 16*(2*(b : ℝ))^2)).mpr
    nlinarith only [hquad,mul_nonneg (sq_nonneg (b : ℝ)) (sq_nonneg ((p : ℝ)-β*q)),sq_nonneg (b : ℝ)]
  linarith only [hdiv]

private theorem real_approximation {K : ℕ} (hK : 4 ≤ K) {β : ℝ}
    (hβ : 1/2 ≤ β) (hβ2 : β ≤ 2) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ b ≤ K ∧ a ≤ 3*b ∧ a.Coprime b ∧
      |(b : ℝ)*β-a| ≤ 1/(K : ℝ) := by
  obtain ⟨r,hr,hrK⟩ := Real.exists_rat_abs_sub_le_and_den_le β (by omega : 0 < K)
  have hb : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hb1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  have hK4 : (4 : ℝ) ≤ K := by exact_mod_cast hK
  have herr : |β-(r : ℝ)| ≤ 1/5 := by
    apply hr.trans
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5)
    nlinarith only [hb1,hK4]
  have hrpos : (0 : ℝ) < r := by linarith only [(abs_le.mp herr).2,hβ]
  have hr3 : (r : ℝ) ≤ 3 := by linarith only [(abs_le.mp herr).1,hβ2]
  have hnum : 0 < r.num := Rat.num_pos.mpr (by exact_mod_cast hrpos)
  have hnumcast : ((r.num.natAbs : ℕ) : ℝ) = (r.num : ℝ) := by
    rw [Nat.cast_natAbs,abs_of_pos hnum]
  have hrat : (r : ℝ) = (r.num.natAbs : ℝ)/r.den := by rw [Rat.cast_def,hnumcast]
  refine ⟨r.num.natAbs,r.den,Int.natAbs_pos.mpr hnum.ne',r.den_pos,hrK,?_,r.reduced,?_⟩
  · have hbound := (div_le_iff₀ hb).mp (hrat ▸ hr3)
    exact_mod_cast hbound
  · have hm := mul_le_mul_of_nonneg_left hr hb.le
    have habs : (r.den : ℝ)*|β-(r : ℝ)| = |(r.den : ℝ)*(β-(r : ℝ))| := by
      rw [abs_mul,abs_of_pos hb]
    rw [habs,hrat] at hm
    have heq : (r.den : ℝ)*(β-(r.num.natAbs : ℝ)/r.den) = (r.den : ℝ)*β-r.num.natAbs := by field_simp
    rw [heq] at hm
    have heq' : (r.den : ℝ)*(1/(((K : ℝ)+1)*r.den)) = 1/((K : ℝ)+1) := by field_simp
    rw [heq'] at hm
    exact hm.trans (one_div_le_one_div_of_le hK0 (by linarith))

private theorem connected_cutoff :
    ∀ᶠ K : ℕ in atTop, 4 ≤ K ∧
      2*Real.log ((24*K^5 : ℕ) : ℝ) ≤ (lowerCutoff K : ℝ)*Real.log (lowerCutoff K) := by
  have hlog : Tendsto (fun K : ℕ => Real.log (K : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [cutoff_conditions,eventually_ge_atTop (4 : ℕ),
    hlog.eventually_ge_atTop (Real.log 24),hlog.eventually_ge_atTop (Real.exp 1)] with K hc hK h24 he
  refine ⟨hK,?_⟩
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hLlo : 16*Real.log (K : ℝ) ≤ (lowerCutoff K : ℝ) := Nat.le_ceil _
  have hL0 : (0 : ℝ) < lowerCutoff K := by exact_mod_cast (by have := hc.2.1; omega : 0 < lowerCutoff K)
  have hlogL1 : 1 ≤ Real.log (lowerCutoff K) := by
    apply (Real.le_log_iff_exp_le hL0).mpr
    linarith only [hLlo,he,Real.exp_pos (1 : ℝ)]
  have hh := mul_le_mul_of_nonneg_left hlogL1 hL0.le
  push_cast
  rw [Real.log_mul (by norm_num : (24 : ℝ) ≠ 0) (pow_ne_zero _ hK0.ne'),Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [hh,hLlo,h24]

private def localBound (K L : ℕ) : ℝ :=
  1+4*(K : ℝ)*(Real.log L/Real.log (sieveSift K))^2*
    Real.exp (2*mertensGapConst)+2*(K : ℝ)^((3 : ℝ)/4)

private theorem localBound_nonneg (K L : ℕ) : 0 ≤ localBound K L := by
  unfold localBound
  positivity

private theorem local_gaussian_sum (S : Finset (ℕ × ℕ)) {K L J a b : ℕ} {β : ℝ}
    (hK : 4 ≤ K) (hL : 2 ≤ L) (hLh : L ≤ sieveSift K)
    (hlogh : 20*mertensFirstConst ≤ Real.log (sieveSift K))
    (hdisc : 2*Real.log ((24*K^5 : ℕ) : ℝ) ≤ (L : ℝ)*Real.log L)
    (ha : 0 < a) (hb : 0 < b) (hbK : b ≤ K) (ha3 : a ≤ 3*b) (hab : a.Coprime b)
    (hβ : 0 < β) (hβ2 : β ≤ 2) (happrox : |(b : ℝ)*β-a| ≤ 1/(K : ℝ))
    (hS : ∀ x ∈ S, x.1 ∈ primeProfileBand ((K^2 : ℕ) : ℝ) ∧
      x.2 ∈ primeProfileBand ((K^2 : ℕ) : ℝ) ∧ x.1 ≠ x.2 ∧
      J ≤ x.2 ∧ x.2 ≤ J+b*K) :
    ∑ x ∈ S, Real.exp (-Real.pi*(((K^2 : ℕ) : ℝ)*
      (Real.log x.1-Real.log x.2-Real.log β))^2) ≤
        Real.exp 1*localBound K L*(1+4*Real.sqrt Real.pi)*(2*b) := by
  classical
  let z : ℤ := ⌊((b : ℝ)*β-a)*J⌋
  let f : ℕ × ℕ → ℤ := fun x => (b : ℤ)*x.1-(a : ℤ)*x.2-z
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hKN : K ≤ K^2 := by nlinarith only [hK]
  have haN : a ≤ K^2 := by nlinarith only [ha3,hbK,hK]
  have hbN : b ≤ K^2 := hbK.trans hKN
  have hfib (v : ℤ) (hv : v ∈ S.image f) :
      ((S.filter (fun x => f x=v)).card : ℝ) ≤ localBound K L := by
    obtain ⟨x,hx,hxv⟩ := Finset.mem_image.mp hv
    have hxdata := hS x hx
    have hv0 := connected_determinant ha hb haN hbN hab hxdata.2.2.1 hxdata.1 hxdata.2.1
    have hvz : v+z = (b : ℤ)*x.1-(a : ℤ)*x.2 := by dsimp [f] at hxv; omega
    have hp := primeProfileBand_mem (Nat.cast_nonneg (K^2)) hxdata.1
    have hq := primeProfileBand_mem (Nat.cast_nonneg (K^2)) hxdata.2.1
    have hp2 : x.1 ≤ 2*K^2 := by exact_mod_cast hp.2.2
    have hq2 : x.2 ≤ 2*K^2 := by exact_mod_cast hq.2.2
    have hvabs : ((b : ℤ)*x.1-(a : ℤ)*x.2).natAbs ≤ 8*K^3 := by
      have hh := Int.natAbs_sub_le ((b : ℤ)*x.1) ((a : ℤ)*x.2)
      simp only [Int.natAbs_mul,Int.natAbs_natCast] at hh
      have hbp := Nat.mul_le_mul hbK hp2
      have haq := Nat.mul_le_mul (ha3.trans (Nat.mul_le_mul_left 3 hbK)) hq2
      nlinarith only [hh,hbp,haq]
    have hdbound : (v+z).natAbs*a*b ≤ 24*K^5 := by
      rw [hvz]
      calc
        _ ≤ (8*K^3)*(3*K)*K := Nat.mul_le_mul (Nat.mul_le_mul hvabs
          (ha3.trans (Nat.mul_le_mul_left 3 hbK))) hbK
        _ = _ := by ring
    have hd0 : 0 < (v+z).natAbs*a*b := by
      rw [hvz]
      exact mul_pos (mul_pos (Int.natAbs_pos.mpr hv0) ha) hb
    have hdlog : 2*Real.log ((v+z).natAbs*a*b) ≤ (L : ℝ)*Real.log L := by
      have hl := Real.log_le_log (y := ((24*K^5 : ℕ) : ℝ))
        (by exact_mod_cast hd0 : (0 : ℝ) < (((v+z).natAbs*a*b : ℕ) : ℝ))
        (by exact_mod_cast hdbound)
      push_cast at hl
      push_cast at hdisc
      linarith only [hl,hdisc]
    apply local_fibre_bound _ hK1 hL hLh hlogh ha hb hab (by rwa [hvz]) hdlog
    intro y hy
    obtain ⟨hym,hyv⟩ := Finset.mem_filter.mp hy
    have hydata := hS y hym
    have hyp := primeProfileBand_mem (Nat.cast_nonneg (K^2)) hydata.1
    have hyq := primeProfileBand_mem (Nat.cast_nonneg (K^2)) hydata.2.1
    have hpN : K^2 < y.1 := by exact_mod_cast hyp.2.1
    have hqN : K^2 < y.2 := by exact_mod_cast hyq.2.1
    have hsN := (sieveSift_le hK1).trans hKN
    refine ⟨hyp.1,hyq.1,by omega,by omega,hydata.2.2.2.1,hydata.2.2.2.2,?_⟩
    dsimp [f] at hyv
    omega
  have hB : (1 : ℝ) ≤ 2*(b : ℝ) := by
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    linarith only [hb1]
  have hg := gaussian_fibre_sum (s := S) f (localBound_nonneg K L) hB hfib
  calc
    _ ≤ ∑ x ∈ S, Real.exp 1*Real.exp (-((f x : ℝ)^2/(16*(2*(b : ℝ))^2))) := by
      apply Finset.sum_le_sum
      intro x hx
      have hd := hS x hx
      have hJ : (J : ℝ) ≤ x.2 := by exact_mod_cast hd.2.2.2.1
      have hJu : (x.2 : ℝ) ≤ J+(b : ℝ)*K := by exact_mod_cast hd.2.2.2.2
      have hshift : |((b : ℝ)*β-a)*((x.2 : ℝ)-J)| ≤ b := by
        rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hJ)]
        have hm := mul_le_mul happrox (show (x.2 : ℝ)-J ≤ (b : ℝ)*K by linarith)
          (sub_nonneg.mpr hJ) (by positivity : (0 : ℝ) ≤ 1/(K : ℝ))
        apply hm.trans_eq
        field_simp
      exact (real_log_gaussian (by nlinarith only [hK] : 1 ≤ K^2) hβ hβ2 hd.1 hd.2.1).trans
        (local_kernel hb hJ hshift)
    _ = Real.exp 1*∑ x ∈ S, Real.exp (-((f x : ℝ)^2/(16*(2*(b : ℝ))^2))) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hg (Real.exp_pos 1).le
      simpa only [mul_assoc] using hm

private def connectedBand (N : ℝ) : Finset (ℕ × ℕ) :=
  ((primeProfileBand N).product (primeProfileBand N)).filter (fun x => x.1 ≠ x.2)

private theorem full_connected_gaussian {K L : ℕ} {β : ℝ}
    (hK : 4 ≤ K) (hL : 2 ≤ L) (hLh : L ≤ sieveSift K)
    (hlogh : 20*mertensFirstConst ≤ Real.log (sieveSift K))
    (hdisc : 2*Real.log ((24*K^5 : ℕ) : ℝ) ≤ (L : ℝ)*Real.log L)
    (hβ : 1/2 ≤ β) (hβ2 : β ≤ 2) :
    ∑ x ∈ connectedBand ((K^2 : ℕ) : ℝ), Real.exp (-Real.pi*(((K^2 : ℕ) : ℝ)*
      (Real.log x.1-Real.log x.2-Real.log β))^2) ≤
        6*Real.exp 1*(1+4*Real.sqrt Real.pi)*(K : ℝ)*localBound K L := by
  classical
  obtain ⟨a,b,ha,hb,hbK,ha3,hab,happrox⟩ := real_approximation hK hβ hβ2
  let S := connectedBand ((K^2 : ℕ) : ℝ)
  let T := Finset.range (2*K^2/(b*K)+1)
  let g : ℕ × ℕ → ℕ := fun x => x.2/(b*K)
  have hS (x : ℕ × ℕ) (hx : x ∈ S) :
      x.1 ∈ primeProfileBand ((K^2 : ℕ) : ℝ) ∧
      x.2 ∈ primeProfileBand ((K^2 : ℕ) : ℝ) ∧ x.1 ≠ x.2 := by
    obtain ⟨hm,hne⟩ := Finset.mem_filter.mp hx
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hm
    exact ⟨hp,hq,hne⟩
  have hmaps (x : ℕ × ℕ) (hx : x ∈ S) : g x ∈ T := by
    have hq2 : x.2 ≤ 2*K^2 := by
      exact_mod_cast (primeProfileBand_mem (Nat.cast_nonneg (K^2)) (hS x hx).2.1).2.2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hq2))
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := g) hmaps]
  have hlocal (j : ℕ) (_hj : j ∈ T) :
      ∑ x ∈ S.filter (fun x => g x=j), Real.exp (-Real.pi*(((K^2 : ℕ) : ℝ)*
        (Real.log x.1-Real.log x.2-Real.log β))^2) ≤
          Real.exp 1*localBound K L*(1+4*Real.sqrt Real.pi)*(2*b) := by
    apply local_gaussian_sum _ hK hL hLh hlogh hdisc ha hb hbK ha3 hab
      (by linarith : 0 < β) hβ2 happrox (J := j*(b*K))
    intro x hx
    obtain ⟨hxm,hxj⟩ := Finset.mem_filter.mp hx
    obtain ⟨hp,hq,hne⟩ := hS x hxm
    refine ⟨hp,hq,hne,?_,?_⟩
    · simpa only [← hxj,g] using Nat.div_mul_le_self x.2 (b*K)
    · have hm := Nat.mod_lt x.2 (mul_pos hb (by omega : 0 < K))
      have he := Nat.div_add_mod x.2 (b*K)
      dsimp [g] at hxj
      rw [hxj] at he
      nlinarith only [hm,he]
  have hsum := Finset.sum_le_sum hlocal
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  have hcard : (T.card : ℝ)*(b : ℝ) ≤ 3*K := by
    have hdiv := Nat.div_mul_le_self (2*K^2) (b*K)
    have hbn : (2*K^2/(b*K)+1)*b ≤ 3*K := by
      nlinarith only [hdiv,hbK,hK]
    simpa only [T,Finset.card_range,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using
      (show (((2*K^2/(b*K)+1)*b : ℕ) : ℝ) ≤ ((3*K : ℕ) : ℝ) by exact_mod_cast hbn)
  apply hsum.trans
  have hD := localBound_nonneg K L
  have hm := mul_le_mul_of_nonneg_right hcard
    (by positivity : 0 ≤ 2*Real.exp 1*localBound K L*(1+4*Real.sqrt Real.pi))
  nlinarith only [hm]

private def realFreq (β : ℝ) (p q : ℕ) : ℝ := Real.log p-Real.log q-Real.log β

private def connectedSpectral (N β t : ℝ) : ℂ :=
  ∑ x ∈ connectedBand N, bandCoeff N x.1*(starRingEnd ℂ) (bandCoeff N x.2)*
    Complex.exp (((realFreq β x.1 x.2*t : ℝ) : ℂ)*Complex.I)*
    (Real.exp (-Real.pi*(N*realFreq β x.1 x.2)^2) : ℂ)

private theorem connected_spectral_bound {K L : ℕ} {β : ℝ}
    (hK : 4 ≤ K) (hL : 2 ≤ L) (hLh : L ≤ sieveSift K)
    (hlogh : 20*mertensFirstConst ≤ Real.log (sieveSift K))
    (hdisc : 2*Real.log ((24*K^5 : ℕ) : ℝ) ≤ (L : ℝ)*Real.log L)
    (hβ : 1/2 ≤ β) (hβ2 : β ≤ 2) (t : ℝ) :
    ‖connectedSpectral ((K^2 : ℕ) : ℝ) β t‖ ≤
      6*Real.exp 1*(1+4*Real.sqrt Real.pi)*localBound K L/(K : ℝ) := by
  have hN : (0 : ℝ) < ((K^2 : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (by omega : 0 < K) 2
  have hterm (x : ℕ × ℕ) (hx : x ∈ connectedBand ((K^2 : ℕ) : ℝ)) :
      ‖bandCoeff ((K^2 : ℕ) : ℝ) x.1*(starRingEnd ℂ) (bandCoeff ((K^2 : ℕ) : ℝ) x.2)*
        Complex.exp (((realFreq β x.1 x.2*t : ℝ) : ℂ)*Complex.I)*
        (Real.exp (-Real.pi*(((K^2 : ℕ) : ℝ)*realFreq β x.1 x.2)^2) : ℂ)‖ ≤
      (1/((K^2 : ℕ) : ℝ))*Real.exp (-Real.pi*(((K^2 : ℕ) : ℝ)*realFreq β x.1 x.2)^2) := by
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
    have hc : ‖bandCoeff ((K^2 : ℕ) : ℝ) x.1*(starRingEnd ℂ) (bandCoeff ((K^2 : ℕ) : ℝ) x.2)‖ ≤
        1/((K^2 : ℕ) : ℝ) := by
      rw [norm_mul,RCLike.norm_conj]
      have hm := mul_le_mul (bandCoeff_norm hN hp) (bandCoeff_norm hN hq) (norm_nonneg _) (by positivity)
      apply hm.trans_eq
      rw [one_div_mul_one_div,← pow_two,Real.sq_sqrt hN.le]
    rw [norm_mul,norm_mul,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,Complex.ofReal_im,
      Complex.I_im,sub_self,Real.exp_zero,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [← Finset.mul_sum] at hsum
  have hg := mul_le_mul_of_nonneg_left (full_connected_gaussian hK hL hLh hlogh hdisc hβ hβ2)
    (by positivity : (0 : ℝ) ≤ 1/((K^2 : ℕ) : ℝ))
  apply hsum.trans (hg.trans_eq ?_)
  push_cast
  field_simp

/-- Gaussian height average of the literal prime field at an arbitrary real twist. -/
def realAverage (N β t : ℝ) : ℂ :=
  ∫ u : ℝ, (Real.exp (-Real.pi*u^2) : ℂ) *
    Complex.exp ((((-Real.log β)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
    primeGaussianChiField 1 N (t+2*Real.pi*N*u) *
    (starRingEnd ℂ) (primeGaussianChiField 1 N (t+2*Real.pi*N*u))

/-- Entire diagonal Gaussian packet, including twists arbitrarily close to one. -/
def diagonalPacket (N β t : ℝ) : ℂ :=
  primeGaussianBandEnergy N*Complex.exp (((-Real.log β*t : ℝ) : ℂ)*Complex.I)*
    (Real.exp (-Real.pi*(N*Real.log β)^2) : ℂ)

private def fullRealSpectral (N β t : ℝ) : ℂ :=
  ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
    bandCoeff N p*(starRingEnd ℂ) (bandCoeff N q)*
      Complex.exp (((realFreq β p q*t : ℝ) : ℂ)*Complex.I)*
      (Real.exp (-Real.pi*(N*realFreq β p q)^2) : ℂ)

private theorem real_pair_phase (N β t u : ℝ) (p q : ℕ) :
    (Real.exp (-Real.pi*u^2) : ℂ) *
      Complex.exp ((((-Real.log β)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
      (bandCoeff N p * Complex.exp (((Real.log p*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I)) *
      (starRingEnd ℂ) (bandCoeff N q * Complex.exp (((Real.log q*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I)) =
    (bandCoeff N p*(starRingEnd ℂ) (bandCoeff N q)*Complex.exp (((realFreq β p q*t : ℝ) : ℂ)*Complex.I)) *
      bourgainGaussianFourierIntegrand (N*realFreq β p q) u := by
  have hpj : (starRingEnd ℂ) (Complex.exp (((Real.log q*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I)) =
      Complex.exp (-(((Real.log q*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I)) := by
    rw [← Complex.exp_conj]
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg]
  have hphase :
      Complex.exp ((((-Real.log β)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
      Complex.exp (((Real.log p*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
      Complex.exp (-(((Real.log q*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I)) =
      Complex.exp (((realFreq β p q*t : ℝ) : ℂ)*Complex.I) *
      Complex.exp (2*(Real.pi : ℂ)*Complex.I*((N*realFreq β p q : ℝ) : ℂ)*(u : ℂ)) := by
    rw [← Complex.exp_add,← Complex.exp_add,← Complex.exp_add]
    congr 1
    unfold realFreq
    push_cast
    ring
  have hg : (Real.exp (-Real.pi*u^2) : ℂ) = Complex.exp (-((Real.pi : ℂ)*(u : ℂ)^2)) := by
    rw [Complex.ofReal_exp]
    push_cast
    congr 1
    ring
  rw [map_mul,hpj,hg]
  unfold bourgainGaussianFourierIntegrand
  calc
    _ = (bandCoeff N p*(starRingEnd ℂ) (bandCoeff N q)) *
        Complex.exp (-((Real.pi : ℂ)*(u : ℂ)^2)) *
        (Complex.exp ((((-Real.log β)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
        Complex.exp (((Real.log p*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
        Complex.exp (-(((Real.log q*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I))) := by ring
    _ = _ := by rw [hphase]; ring

private theorem realAverage_eq_spectral (N β t : ℝ) :
    realAverage N β t = fullRealSpectral N β t := by
  have hpoint (u : ℝ) :
      (Real.exp (-Real.pi*u^2) : ℂ) *
        Complex.exp ((((-Real.log β)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
        primeGaussianChiField 1 N (t+2*Real.pi*N*u) *
        (starRingEnd ℂ) (primeGaussianChiField 1 N (t+2*Real.pi*N*u)) =
      ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
        (bandCoeff N p*(starRingEnd ℂ) (bandCoeff N q)*Complex.exp (((realFreq β p q*t : ℝ) : ℂ)*Complex.I)) *
          bourgainGaussianFourierIntegrand (N*realFreq β p q) u := by
    simp only [primeGaussianChiField,one_mul,map_sum,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    exact real_pair_phase N β t u p q
  have hi (p q : ℕ) : MeasureTheory.Integrable (fun u : ℝ =>
      (bandCoeff N p*(starRingEnd ℂ) (bandCoeff N q)*Complex.exp (((realFreq β p q*t : ℝ) : ℂ)*Complex.I)) *
        bourgainGaussianFourierIntegrand (N*realFreq β p q) u) :=
    (integrable_bourgainGaussianFourierIntegrand _).const_mul _
  unfold realAverage
  simp_rw [hpoint]
  rw [MeasureTheory.integral_finsetSum _ (fun p _ => MeasureTheory.integrable_finsetSum _ (fun q _ => hi p q))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [MeasureTheory.integral_finsetSum _ (fun q _ => hi p q)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [MeasureTheory.integral_const_mul,integral_bourgainGaussianFourierIntegrand]


private theorem bandCoeff_diagonal (N : ℝ) (p : ℕ) :
    bandCoeff N p*(starRingEnd ℂ) (bandCoeff N p) =
      smoothAFECutoff ((p : ℝ)/N)*(starRingEnd ℂ) (smoothAFECutoff ((p : ℝ)/N))/(p : ℂ) := by
  have hs : (Real.sqrt p : ℂ)*(Real.sqrt p : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul,← pow_two,Real.sq_sqrt (Nat.cast_nonneg p)]
    rfl
  simp only [bandCoeff,map_div₀,Complex.conj_ofReal,div_mul_div_comm,hs]

/-- Exact connected decomposition; the diagonal packet is removed at every real twist. -/
private theorem realAverage_sub_diagonalPacket (N β t : ℝ) :
    realAverage N β t-diagonalPacket N β t = connectedSpectral N β t := by
  classical
  rw [realAverage_eq_spectral]
  let F : ℕ → ℕ → ℂ := fun p q => bandCoeff N p*(starRingEnd ℂ) (bandCoeff N q)*
    Complex.exp (((realFreq β p q*t : ℝ) : ℂ)*Complex.I)*
    (Real.exp (-Real.pi*(N*realFreq β p q)^2) : ℂ)
  have hd (p : ℕ) : F p p =
      (smoothAFECutoff ((p : ℝ)/N)*(starRingEnd ℂ) (smoothAFECutoff ((p : ℝ)/N))/(p : ℂ))*
        Complex.exp (((-Real.log β*t : ℝ) : ℂ)*Complex.I)*
        (Real.exp (-Real.pi*(N*Real.log β)^2) : ℂ) := by
    dsimp only [F]
    rw [bandCoeff_diagonal]
    simp only [realFreq,sub_self,zero_sub,mul_neg,neg_sq]
  have he (p q : ℕ) : F p q = (if p ≠ q then F p q else 0)+(if p = q then F p q else 0) := by
    by_cases h : p=q <;> simp [h]
  have hsplit : fullRealSpectral N β t = connectedSpectral N β t+∑ p ∈ primeProfileBand N, F p p := by
    change (∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N, F p q) = _
    conv_lhs => arg 2; ext p; arg 2; ext q; rw [he p q]
    simp only [Finset.sum_add_distrib]
    congr 1
    · unfold connectedSpectral connectedBand
      rw [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
    · apply Finset.sum_congr rfl
      intro p hp
      simp [hp]
  rw [hsplit]
  have hdiag : (∑ p ∈ primeProfileBand N, F p p) = diagonalPacket N β t := by
    simp_rw [hd]
    rw [← Finset.sum_mul,← Finset.sum_mul]
    rfl
  rw [hdiag]
  abel

private theorem connected_uniform {K : ℕ} {β : ℝ}
    (hK : 4 ≤ K) (hL : 2 ≤ lowerCutoff K) (hLh : lowerCutoff K ≤ sieveSift K)
    (hlogh : 20*mertensFirstConst ≤ Real.log (sieveSift K))
    (hdisc : 2*Real.log ((24*K^5 : ℕ) : ℝ) ≤ (lowerCutoff K : ℝ)*Real.log (lowerCutoff K))
    (hβ : 1/2 ≤ β) (hβ2 : β ≤ 2) (t : ℝ) :
    ‖connectedSpectral ((K^2 : ℕ) : ℝ) β t‖ ≤
      (6*Real.exp 1*(1+4*Real.sqrt Real.pi)*(4*Real.exp (2*mertensGapConst)+3))*growthError K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hpow : (K : ℝ)^((3 : ℝ)/4)/(K : ℝ) = (K : ℝ)^(-(1 : ℝ)/4) := by
    rw [← Real.rpow_sub_one hKR.ne']
    norm_num
  have hinv : 1/(K : ℝ) ≤ (K : ℝ)^(-(1 : ℝ)/4) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ K) : (1 : ℝ) ≤ K)
      (by norm_num : (-1 : ℝ) ≤ -(1 : ℝ)/4)
    simpa only [Real.rpow_neg_one,one_div] using hh
  have hD : localBound K (lowerCutoff K)/(K : ℝ) ≤
      (4*Real.exp (2*mertensGapConst)+3)*growthError K := by
    unfold localBound growthError
    rw [add_div,add_div,show 2*(K : ℝ)^((3 : ℝ)/4)/(K : ℝ) = 2*((K : ℝ)^((3 : ℝ)/4)/(K : ℝ)) by ring,hpow]
    have heq : 4*(K : ℝ)*(Real.log (lowerCutoff K)/Real.log (sieveSift K))^2*
        Real.exp (2*mertensGapConst)/(K : ℝ) =
        4*(Real.log (lowerCutoff K)/Real.log (sieveSift K))^2*Real.exp (2*mertensGapConst) := by field_simp
    rw [heq]
    nlinarith only [hinv,sq_nonneg (Real.log (lowerCutoff K)/Real.log (sieveSift K)),
      mul_nonneg (Real.exp_pos (2*mertensGapConst)).le
        (Real.rpow_nonneg (Nat.cast_nonneg K) (-(1 : ℝ)/4))]
  apply (connected_spectral_bound hK hL hLh hlogh hdisc hβ hβ2 t).trans
  have hm := mul_le_mul_of_nonneg_left hD
    (by positivity : 0 ≤ 6*Real.exp 1*(1+4*Real.sqrt Real.pi))
  simpa only [mul_div_assoc,mul_assoc] using hm

/-- Uniform critical-height cancellation of the full connected prime-pair average
for every real twist in the band ratio range, with arbitrary height centre.
The error tends to zero after multiplication by the logarithm of the band scale. -/
theorem exists_connected_negligible_error :
    ∃ error : ℕ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ K : ℕ in atTop, ∀ β ∈ Set.Icc (1/2 : ℝ) 2, ∀ t : ℝ,
        Real.log ((K^2 : ℕ) : ℝ)*
          ‖realAverage ((K^2 : ℕ) : ℝ) β t-diagonalPacket ((K^2 : ℕ) : ℝ) β t‖ ≤ error K := by
  let C : ℝ := 6*Real.exp 1*(1+4*Real.sqrt Real.pi)*(4*Real.exp (2*mertensGapConst)+3)
  refine ⟨fun K => (2*C)*(Real.log (K : ℝ)*growthError K),?_,?_⟩
  · simpa only [mul_zero] using growthError_log_limit.const_mul (2*C)
  · filter_upwards [cutoff_conditions,connected_cutoff] with K hc hu
    intro β hβ t
    obtain ⟨_,hL,hLh,hlogh,_,_,_,hlog1⟩ := hc
    rw [realAverage_sub_diagonalPacket]
    have hb := connected_uniform hu.1 hL hLh hlogh hu.2 hβ.1 hβ.2 t
    have hl : Real.log ((K^2 : ℕ) : ℝ) = 2*Real.log (K : ℝ) := by rw [Nat.cast_pow,Real.log_pow]; norm_num
    rw [hl]
    have hm := mul_le_mul_of_nonneg_left hb (by linarith only [hlog1] : 0 ≤ 2*Real.log (K : ℝ))
    exact hm.trans_eq (by ring)

end GaussianPrimeTwist
end RHTower
