import GaloisForLFunctions.RHTower.Sieve.MertensSecond
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.PSeries
import GaloisForLFunctions.RHTower.WeilPrimitiveSetMeanSquare

/-!
# Arithmetic envelope for weighted polar recovery

Primitive sets grouped by total prime-factor count control the absolute
harmonic coefficient mass. For every 1 < z < 2 the squared harmonic mass
is bounded by a constant times the primitive square budget and
(1 + log N)^z. The harmonic exponential moment is proved from the finite
Euler product and the corpus elementary Mertens upper bound.

This is the arithmetic component of the paper proof of exact weighted
fibre recovery for 0 < beta < 1/2. It does not itself derive a primitive
budget from a spectral separator, prove weighted recovery, or control
Gamma energy. No RH, numerical estimate or new axiom is used.
Paper: docs/reports/weil-work/results/02-exposing-ray/SUBHALF-LOG-FIBRE-PROOF.md.
-/

open Finset
noncomputable section
namespace RHTower.ExposingRayTransfer

private def omegaWeight (z : ℝ) (n : ℕ) : ℝ :=
  z ^ ArithmeticFunction.cardFactors n / n

private theorem omegaWeight_nonneg {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ omegaWeight z n := by unfold omegaWeight; positivity

private theorem omegaWeight_mul (z : ℝ) (m n : ℕ) :
    omegaWeight z (m*n) = omegaWeight z m * omegaWeight z n := by
  by_cases hm : m=0
  · simp [hm, omegaWeight]
  by_cases hn : n=0
  · simp [hn, omegaWeight]
  simp only [omegaWeight, ArithmeticFunction.cardFactors_mul hm hn, pow_add, Nat.cast_mul]
  ring

private theorem omegaWeight_prime_pow (z : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    omegaWeight z (p^k) = (z / p)^k := by
  simp [omegaWeight, ArithmeticFunction.cardFactors_apply_prime_pow hp, div_pow]

private theorem omegaWeight_sum_le_product {z : ℝ} (hz : 0 ≤ z) (hz2 : z < 2)
    (N : ℕ) :
    (∑ n ∈ Icc 1 N, omegaWeight z n) ≤
      ∏ p ∈ N.primesLE, (1-z/p)⁻¹ := by
  have hratio {p : ℕ} (hp : p.Prime) : z / p < 1 := by
    apply (div_lt_one (by exact_mod_cast hp.pos : (0:ℝ)<p)).2
    exact hz2.trans_le (by exact_mod_cast hp.two_le)
  have hseries {p : ℕ} (hp : p.Prime) :
      HasSum (fun k => omegaWeight z (p^k)) (1-z/p)⁻¹ := by
    simpa only [omegaWeight_prime_pow z hp] using
      hasSum_geometric_of_lt_one (div_nonneg hz (Nat.cast_nonneg p)) (hratio hp)
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := omegaWeight z) (by simp [omegaWeight])
    (fun {m n} _ => omegaWeight_mul z m n)
    (fun {p} hp => (hseries hp).summable.norm) N.primesLE
  have hprod : (∏ p ∈ N.primesLE with p.Prime, ∑' k, omegaWeight z (p^k)) =
      ∏ p ∈ N.primesLE, (1-z/p)⁻¹ := by
    have he : N.primesLE.filter Nat.Prime = N.primesLE :=
      filter_eq_self.mpr fun p hp => (Nat.mem_primesLE.mp hp).2
    rw [he]
    exact prod_congr rfl fun p hp => (hseries (Nat.mem_primesLE.mp hp).2).tsum_eq
  rw [hprod] at hs
  let e : (Icc 1 N : Finset ℕ) → Nat.factoredNumbers N.primesLE := fun n =>
    ⟨n, Nat.mem_factoredNumbers_of_primeFactors_subset
      (by have h := (mem_Icc.mp n.2).1; omega) (by
        intro p hp
        obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
        exact Nat.mem_primesLE.mpr
          ⟨(Nat.le_of_dvd (by have h := (mem_Icc.mp n.2).1; omega) hpn).trans
            (mem_Icc.mp n.2).2, hpp⟩)⟩
  have hinj : Function.Injective e := by
    intro m n h
    apply Subtype.ext
    exact congrArg (fun x : Nat.factoredNumbers N.primesLE => (x : ℕ)) h
  have h := Summable.tsum_le_tsum_of_inj e hinj
    (fun n _ => omegaWeight_nonneg hz n) (fun _ => le_rfl)
    (hasSum_fintype _).summable hs.2.summable
  rw [hs.2.tsum_eq, tsum_fintype] at h
  simpa only [e, Finset.sum_coe_sort] using h

private theorem log_geometric_le {z p : ℝ} (hz : 0 ≤ z) (hz2 : z < 2) (hp : 2 ≤ p) :
    Real.log (1-z/p)⁻¹ ≤ z/p + (z^2/(1-z/2)) * (1/p^2) := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < 1-z/p := by rw [sub_pos, div_lt_one hp0]; linarith
  have hd2 : 0 < 1-z/2 := by linarith
  have hdiv : z/p ≤ z/2 := div_le_div_of_nonneg_left hz (by norm_num) hp
  have hden : 1-z/2 ≤ 1-z/p := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
  have hid : (1-z/p)⁻¹-1 = z/p + (z/p)^2/(1-z/p) := by
    have hpz : p-z ≠ 0 := ne_of_gt (by linarith : 0 < p-z)
    field_simp [hp0.ne', hd.ne', hpz]
    ring
  have hle := div_le_div_of_nonneg_left (sq_nonneg (z/p)) hd2 hden
  rw [hid] at hlog
  calc
    _ ≤ z/p + (z/p)^2/(1-z/p) := hlog
    _ ≤ z/p + (z/p)^2/(1-z/2) := add_le_add_right hle _
    _ = _ := by ring

/-- Prime-factor count has every harmonic exponential moment with base below two. -/
theorem exists_omega_harmonic_bound {z : ℝ} (hz : 1 < z) (hz2 : z < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (∑ n ∈ Icc 1 N, z ^ ArithmeticFunction.cardFactors n / (n:ℝ)) ≤
        C * (1+Real.log N)^z := by
  let Z : ℝ := ∑' n : ℕ, (1:ℝ)/(n:ℝ)^2
  let K : ℝ := 1+2*(Sieve.mertensFirstConst/Real.log 2)-Sieve.logLog 2
  let D : ℝ := z^2/(1-z/2)
  have hz0 : 0 ≤ z := by linarith
  have hd2 : 0 < 1-z/2 := by linarith
  have hD : 0 ≤ D := div_nonneg (sq_nonneg z) hd2.le
  have hZs : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine ⟨Real.exp (z*K+D*Z), Real.exp_pos _, fun N hN => ?_⟩
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1<N))
  have hsum := hZs.sum_le_tsum N.primesLE (fun _ _ => by positivity)
  have hM : (∑ p ∈ N.primesLE, (1:ℝ)/p) ≤ Real.log (Real.log N)+K :=
    Sieve.mertensSecond_upper hN
  have hlogs : (∑ p ∈ N.primesLE, Real.log (1-z/(p:ℝ))⁻¹) ≤
      z*Real.log (Real.log N)+(z*K+D*Z) := by
    have hpoint := sum_le_sum (s := N.primesLE) fun p hp =>
      log_geometric_le (p := (p:ℝ)) hz0 hz2 (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le)
    have hM' := mul_le_mul_of_nonneg_left hM hz0
    have hZ' := mul_le_mul_of_nonneg_left hsum hD
    rw [sum_add_distrib, ← mul_sum] at hpoint
    have he : (∑ p ∈ N.primesLE, z/(p:ℝ)) = z*(∑ p ∈ N.primesLE, (1:ℝ)/p) := by
      rw [mul_sum]; apply sum_congr rfl; intro p _; ring
    rw [he] at hpoint
    dsimp only [D] at hZ'
    dsimp only [D, Z]
    nlinarith only [hpoint, hM', hZ']
  have hprod : (∏ p ∈ N.primesLE, (1-z/(p:ℝ))⁻¹) =
      Real.exp (∑ p ∈ N.primesLE, Real.log (1-z/(p:ℝ))⁻¹) := by
    rw [Real.exp_sum]
    apply prod_congr rfl
    intro p hp
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
    symm
    apply Real.exp_log
    apply inv_pos.mpr
    rw [sub_pos, div_lt_one hp0]
    exact hz2.trans_le (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le)
  calc
    _ ≤ ∏ p ∈ N.primesLE, (1-z/(p:ℝ))⁻¹ := omegaWeight_sum_le_product hz0 hz2 N
    _ ≤ Real.exp (z*Real.log (Real.log N)+(z*K+D*Z)) := by
      rw [hprod]; exact Real.exp_le_exp.mpr hlogs
    _ = Real.exp (z*K+D*Z)*(Real.log N)^z := by
      rw [Real.exp_add, Real.rpow_def_of_pos hlogN, mul_comm z (Real.log (Real.log N))]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hlogN.le (by linarith) hz0) (Real.exp_pos _).le

/-- Integers of a fixed total prime-factor count form a primitive set. -/
theorem omega_layer_primitive (N k : ℕ) :
    WeilMeanSquare.IsPrimitiveSet ((Icc 2 N).filter
      (fun n => ArithmeticFunction.cardFactors n = k)) := by
  intro n hn m hm d hd hnm
  obtain ⟨hn, hnk⟩ := mem_filter.mp hn
  obtain ⟨hm, hmk⟩ := mem_filter.mp hm
  have hd0 : d ≠ 0 := by omega
  have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
  have hdp : 0 < ArithmeticFunction.cardFactors d :=
    ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega)
  rw [hnm, ArithmeticFunction.cardFactors_mul hd0 hm0, hmk] at hnk
  omega

/-- A primitive-set square bound controls an absolute harmonic moment.
The constant depends only on the exponent, not the coefficients or cutoff. -/
theorem exists_primitive_harmonic_square_bound {z : ℝ} (hz : 1 < z) (hz2 : z < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℕ → ℝ) (B : ℝ) (N : ℕ), 2 ≤ N →
      (∀ S : Finset ℕ, S ⊆ Icc 2 N → WeilMeanSquare.IsPrimitiveSet S →
        (∑ n ∈ S, b n ^ 2) ≤ B^2) →
      (∑ n ∈ Icc 2 N, |b n| / Real.sqrt n)^2 ≤ C*B^2*(1+Real.log N)^z := by
  obtain ⟨C0, hC0, hmoment⟩ := exists_omega_harmonic_bound hz hz2
  have hz0 : 0 < z := by linarith
  have hi0 : 0 ≤ z⁻¹ := (inv_pos.mpr hz0).le
  have hi1 : z⁻¹ < 1 := by
    rw [inv_eq_one_div, div_lt_one hz0]
    exact hz
  let G : ℝ := (1-z⁻¹)⁻¹
  have hG : 0 < G := inv_pos.mpr (sub_pos.mpr hi1)
  refine ⟨G*C0, mul_pos hG hC0, fun b B N hN hprim => ?_⟩
  let S := Icc 2 N
  let K := S.image ArithmeticFunction.cardFactors
  have hlayer (k : ℕ) :
      (∑ n ∈ S with ArithmeticFunction.cardFactors n = k, b n^2) ≤ B^2 :=
    hprim _ (filter_subset _ _) (omega_layer_primitive N k)
  have hgeom := (hasSum_geometric_of_lt_one hi0 hi1).summable.sum_le_tsum K
    (fun _ _ => pow_nonneg hi0 _)
  rw [(hasSum_geometric_of_lt_one hi0 hi1).tsum_eq] at hgeom
  have hweighted : (∑ n ∈ S, b n^2 / z^ArithmeticFunction.cardFactors n) ≤ B^2*G := by
    have hsplit := sum_fiberwise_of_maps_to
      (s := S) (t := K) (fun n hn => mem_image_of_mem _ hn)
      (fun n => b n^2 / z^ArithmeticFunction.cardFactors n)
    rw [← hsplit]
    calc
      _ = ∑ k ∈ K, (∑ n ∈ S with ArithmeticFunction.cardFactors n=k, b n^2) / z^k := by
        apply sum_congr rfl
        intro k _
        rw [sum_div]
        apply sum_congr rfl
        intro n hn
        rw [(mem_filter.mp hn).2]
      _ ≤ ∑ k ∈ K, B^2/z^k := sum_le_sum fun k _ =>
        div_le_div_of_nonneg_right (hlayer k) (pow_nonneg hz0.le k)
      _ = B^2*(∑ k ∈ K, (z⁻¹)^k) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k _
        rw [inv_pow, div_eq_mul_inv]
      _ ≤ B^2*G := mul_le_mul_of_nonneg_left hgeom (sq_nonneg B)
  have hCS := sum_mul_sq_le_sq_mul_sq S
    (fun n => |b n|/Real.sqrt (z^ArithmeticFunction.cardFactors n))
    (fun n => Real.sqrt (z^ArithmeticFunction.cardFactors n)/Real.sqrt n)
  have hleft : (∑ n ∈ S, |b n|/Real.sqrt (z^ArithmeticFunction.cardFactors n) *
      (Real.sqrt (z^ArithmeticFunction.cardFactors n)/Real.sqrt n)) =
      ∑ n ∈ S, |b n|/Real.sqrt n := by
    apply sum_congr rfl
    intro n _
    have hp : Real.sqrt (z^ArithmeticFunction.cardFactors n) ≠ 0 := by positivity
    field_simp
  have hfirst : (∑ n ∈ S, (|b n|/Real.sqrt (z^ArithmeticFunction.cardFactors n))^2) =
      ∑ n ∈ S, b n^2/z^ArithmeticFunction.cardFactors n := by
    apply sum_congr rfl
    intro n _
    rw [div_pow, sq_abs, Real.sq_sqrt (pow_nonneg hz0.le _)]
  have hsecond : (∑ n ∈ S, (Real.sqrt (z^ArithmeticFunction.cardFactors n)/Real.sqrt n)^2) =
      ∑ n ∈ S, z^ArithmeticFunction.cardFactors n/(n:ℝ) := by
    apply sum_congr rfl
    intro n _
    rw [div_pow, Real.sq_sqrt (pow_nonneg hz0.le _), Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hleft, hfirst, hsecond] at hCS
  have hmom : (∑ n ∈ S, z^ArithmeticFunction.cardFactors n/(n:ℝ)) ≤
      C0*(1+Real.log N)^z := by
    apply le_trans _ (hmoment N hN)
    apply sum_le_sum_of_subset_of_nonneg
      (fun n hn => mem_Icc.mpr ⟨by have := (mem_Icc.mp hn).1; omega, (mem_Icc.mp hn).2⟩)
    intro n _ _
    positivity
  calc
    _ ≤ (∑ n ∈ S, b n^2/z^ArithmeticFunction.cardFactors n) *
        ∑ n ∈ S, z^ArithmeticFunction.cardFactors n/(n:ℝ) := hCS
    _ ≤ (B^2*G)*(C0*(1+Real.log N)^z) := mul_le_mul hweighted hmom
      (sum_nonneg fun n _ => by positivity) (mul_nonneg (sq_nonneg B) hG.le)
    _ = _ := by ring

end RHTower.ExposingRayTransfer
