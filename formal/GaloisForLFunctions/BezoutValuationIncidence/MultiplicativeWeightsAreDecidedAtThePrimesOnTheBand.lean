import GaloisForLFunctions.BezoutValuationIncidence.ParityPairSeparatedOnTheVinogradovKorobovBand
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ReceiverOfMultiplicativeWeightsIsDecidedAtThePrimes

/-!
# Multiplicative weights are decided at the primes on the Vinogradov–Korobov band

Let `f` be multiplicative with `|f| ≤ 1` and consider the damped weight `f(d) d^{-ε}`.

* **`f(p) = −1` at every prime** (Möbius, Liouville, …). Then `f = g ⋆ μ` with `g = f ⋆ 1` vanishing
  at the primes, so `g(d) d^{-ε}` lies in the critical Wiener algebra with mass
  `G_ε = Σ_q |g(q)| q^{-1/2-ε} ≤ G_{1/4}` for `ε ≥ 1/4`. The finite-horizon convolution law
  `‖A_{g⋆c}‖ ≤ G ‖A_c‖ + (√2+1) G |m_c|` transports the Möbius receiver bound on the band:
  `E_T(f d^{-ε}) ≤ E_f` uniformly for every `T` and every `ε` on the band
  `1/4 ≤ ε ≤ 1/2`, `ε ≥ 1/2 − κσ(T)/(480 log T)`.
* **`f(p) = +1` at every prime and `f ≥ 0`.** Then `f ≥ μ²`, the squarefree moduli beyond the prefix
  leave the drift `n Σ_{n<d≤2n} f(d) d^{-1-ε} ≥ n (2n)^{-ε}/16`, and
  `E_T(f d^{-ε}) ≥ (log(T+1) − log 100)/1024` for every `T` and every `0 < ε ≤ 1/2`.

So on the band, as at half damping, the receiver of a multiplicative weight is decided by its sign at
the primes, i.e. by the dilations `k ↦ pk`; the values on higher prime powers are invisible.
-/

open Finset Filter Topology RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- `0 < ρ_ε ≤ 1`: every Euler factor `1 - p^{-1-ε}` lies in `[0, 1]`. -/
theorem dampedDensity_le_one {ε : ℝ} (hε : 0 < ε) : dampedDensity ε ≤ 1 := by
  refine le_of_tendsto' (RHTower.pmPowerDampedDivisorDensity_hasProd_real hε) fun s =>
    prod_le_one (fun p _ => ?_) fun p _ => ?_
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_le
    have hp0 : (0 : ℝ) < p := by linarith
    have ht : (p : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
    exact sub_nonneg.mpr ((div_le_one hp0).mpr (by linarith))
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
    have : 0 ≤ (p : ℝ) ^ (-ε) / p := div_nonneg (Real.rpow_nonneg hp0.le _) hp0.le
    linarith

/-- The critical Wiener mass of `(f ⋆ 1)(q) q^{-ε}` decreases in `ε`. -/
theorem criticalMass_le_quarter {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hfp : ∀ p : ℕ, p.Prime → f p = -1) (hbd : ∀ n, |f n| ≤ 1) {ε : ℝ} (hε4 : 1 / 4 ≤ ε) :
    ∑' q : ℕ, |dampedSignWeight ⇑(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ε q| *
        (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      ∑' q : ℕ, |dampedSignWeight ⇑(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (1 / 4) q| *
        (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hε : 0 < ε := by linarith
  have h4 := criticalWiener_mul_zeta hf hfp hbd (by norm_num : (0 : ℝ) < 1 / 4)
  refine (criticalWiener_mul_zeta hf hfp hbd hε).tsum_le_tsum (fun q => ?_) h4
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  unfold dampedSignWeight
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [Real.zero_rpow (show -ε ≠ 0 by linarith)]
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq) (by linarith)

/-- **Weights `−1` at the primes on the band.** For multiplicative `f` with `|f| ≤ 1` and `f(p) = −1`
there is `E` with `E_T(f d^{-ε}) ≤ E` for every `T` and every `ε` on the Vinogradov–Korobov band. -/
theorem exists_receiver_le_on_vinogradovKorobovBand_of_primes_neg_one {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hfp : ∀ p : ℕ, p.Prime → f p = -1) (hbd : ∀ n, |f n| ≤ 1) :
    ∃ E : ℝ, ∀ (T : ℕ) (ε : ℝ), 1 / 4 ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ ε →
        weightPronicEnergy (dampedSignWeight ⇑f ε) (∑' d : ℕ, dampedSignWeight ⇑f ε d / d) T ≤ E := by
  obtain ⟨E, hE⟩ := exists_receiver_le_on_vinogradovKorobovBand
  set Gq := ∑' q : ℕ,
    |dampedSignWeight ⇑(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (1 / 4) q| *
      (q : ℝ) ^ (-(1 / 2 : ℝ)) with hGdef
  have hG0 : 0 ≤ Gq := tsum_nonneg fun q =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  refine ⟨(Gq * Real.sqrt (max E 0) + (Real.sqrt 2 + 1) * Gq) ^ 2,
    fun T ε hε4 hε2 hband => ?_⟩
  have hε : 0 < ε := by linarith
  set g := dampedSignWeight ⇑(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ε
  set c := pmPowerDampedRealWeight ε
  have hg := criticalWiener_mul_zeta hf hfp hbd hε
  have hc := summable_abs_pmPowerDamped_div hε
  have hconv : dampedSignWeight ⇑f ε = RHTower.dirichletConv g c :=
    funext (dampedMultiplicative_eq_dirichletConv f ε)
  have hmc : ∑' d : ℕ, c d / d = dampedDensity ε := (hasSum_pmPowerDampedRealWeight_div hε).tsum_eq
  have hmean : ∑' d : ℕ, dampedSignWeight ⇑f ε d / d = (∑' q : ℕ, g q / q) * dampedDensity ε := by
    rw [hconv, ← hmc]
    exact (hasSum_dirichletConv_div hg.summable_abs_div.of_abs.hasSum hc.of_abs.hasSum
      hg.summable_abs_div hc).tsum_eq
  have hGε := criticalMass_le_quarter hf hfp hbd hε4
  have hρ0 : 0 < dampedDensity ε := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  have hρ1 := dampedDensity_le_one hε
  -- the Möbius receiver on the band
  have hEc : pronicNorm (weightCenteredPrefix c (dampedDensity ε)) T ≤ Real.sqrt (max E 0) := by
    rw [← Real.sqrt_sq (pronicNorm_nonneg _ T), ← weightPronicEnergy_eq_sq_pronicNorm]
    refine Real.sqrt_le_sqrt ((?_ : _ ≤ E).trans (le_max_left _ _))
    rw [weightPronicEnergy_pmPowerDamped]
    exact hE T ε hε4 hε2 hband
  have hlaw := pronicNorm_dirichletConv_le (c := c) hg (dampedDensity ε) T
  rw [hmean, weightPronicEnergy_eq_sq_pronicNorm, hconv]
  refine pow_le_pow_left₀ (pronicNorm_nonneg _ T) (hlaw.trans ?_) 2
  have hGε0 : 0 ≤ ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) := tsum_nonneg fun q =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  rw [abs_of_pos hρ0]
  have hs2 : 0 ≤ Real.sqrt 2 + 1 := by positivity
  calc (∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) *
        pronicNorm (weightCenteredPrefix c (dampedDensity ε)) T +
        dampedDensity ε * ((Real.sqrt 2 + 1) * ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)))
      ≤ Gq * Real.sqrt (max E 0) + 1 * ((Real.sqrt 2 + 1) * Gq) := by
        refine add_le_add (mul_le_mul hGε hEc (pronicNorm_nonneg _ T) hG0) ?_
        exact mul_le_mul hρ1 (mul_le_mul_of_nonneg_left hGε hs2) (by positivity) zero_le_one
    _ = Gq * Real.sqrt (max E 0) + (Real.sqrt 2 + 1) * Gq := by ring

/-- The squarefree drift of a weight `≥ μ²`: `n (2n)^{-ε}/16 ≤ n Σ_{n<d≤2n} f(d) d^{-ε}/d`. -/
theorem drift_ge_of_ge_moebius_sq {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hsq : ∀ n, Squarefree n → f n = 1) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 100 ≤ n) :
    1 / 16 * (n : ℝ) * (2 * (n : ℝ)) ^ (-ε) ≤
      (n : ℝ) * ∑ d ∈ Ioc n (2 * n), dampedSignWeight f ε d / d := by
  set c := dampedSignWeight f ε
  have hc0 : ∀ d, 0 ≤ c d := fun d => mul_nonneg (hf0 d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have hcount := squarefree_count_dyadic_ge hn
  rw [show n + n = 2 * n by ring] at hcount
  have hterm : ∀ d ∈ Ioc n (2 * n), ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ (2 : ℕ) *
      ((2 * (n : ℝ)) ^ (-ε) / (2 * n)) ≤ c d / d := fun d hd => by
    have hd := mem_Ioc.mp hd
    have hd0 : (0 : ℝ) < d := by
      have : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd.1
      exact_mod_cast this
    have hdle : (d : ℝ) ≤ 2 * n := by exact_mod_cast hd.2
    have hpow : (2 * (n : ℝ)) ^ (-ε) / (2 * n) ≤ (d : ℝ) ^ (-ε) / d := by
      rw [← Real.rpow_sub_one h2n.ne', ← Real.rpow_sub_one hd0.ne']
      exact Real.rpow_le_rpow_of_nonpos hd0 hdle (by linarith)
    by_cases hsf : Squarefree d
    · rw [show ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ (2 : ℕ) = 1 by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf, one_mul]
      simp only [c, dampedSignWeight, hsq d hsf, one_mul]
      exact hpow
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact div_nonneg (hc0 d) hd0.le
  have hsum := sum_le_sum hterm
  rw [← sum_mul] at hsum
  have hP : 0 ≤ (2 * (n : ℝ)) ^ (-ε) / (2 * n) := by positivity
  have h1 : (n : ℝ) / 8 * ((2 * (n : ℝ)) ^ (-ε) / (2 * n)) ≤ ∑ d ∈ Ioc n (2 * n), c d / d :=
    (mul_le_mul_of_nonneg_right hcount hP).trans hsum
  have h2 : 1 / 16 * (n : ℝ) * (2 * (n : ℝ)) ^ (-ε) =
      (n : ℝ) * ((n : ℝ) / 8 * ((2 * (n : ℝ)) ^ (-ε) / (2 * n))) := by
    field_simp; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 hn0.le

/-- **Weights `+1` at the primes grow logarithmically**, uniformly in `0 < ε ≤ 1/2`:
`E_T(f d^{-ε}) ≥ (log(T+1) − log 100)/1024` for multiplicative `0 ≤ f ≤ 1` with `f(p) = 1`. -/
theorem receiver_ge_log_of_primes_one {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hfp : ∀ p : ℕ, p.Prime → f p = 1) (hf0 : ∀ n, 0 ≤ f n) (hbd : ∀ n, |f n| ≤ 1) {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (T : ℕ) :
    (Real.log ((T : ℝ) + 1) - Real.log 100) / 1024 ≤
      weightPronicEnergy (dampedSignWeight ⇑f ε) (∑' d : ℕ, dampedSignWeight ⇑f ε d / d) T := by
  have hsq : ∀ n : ℕ, Squarefree n → f n = 1 := fun n hn => by
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp hk =>
      have hk1 : k = 1 := by
        by_contra h
        exact absurd hn (by rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; omega)
      rw [hk1, pow_one, hfp p hp]
    | zero => exact absurd hn _root_.not_squarefree_zero
    | one => exact hf.map_one
    | coprime a b ha hb hab iha ihb =>
      rw [hf.map_mul_of_coprime hab, iha (Squarefree.of_mul_left hn),
        ihb (Squarefree.of_mul_right hn), mul_one]
  set c := dampedSignWeight ⇑f ε
  have hc0 : ∀ d, 0 ≤ c d := fun d => mul_nonneg (hf0 d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hs := (summable_abs_dampedSign_div_of_abs_le hbd hε).of_abs
  have hcell : ∀ n : ℕ, 100 ≤ n → 1 / 1024 * (1 / (n : ℝ)) ≤
      weightCenteredPrefix c (∑' d : ℕ, c d / d) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n hn
    have h := weightCell_ge_of_drift hc0 hs.hasSum (K := 1 / 16) (by norm_num) hε2 (by omega)
      (drift_ge_of_ge_moebius_sq hf0 hsq hε hn)
    calc 1 / 1024 * (1 / (n : ℝ)) = (1 / 16 : ℝ) ^ 2 / 4 / n := by ring
      _ ≤ _ := h
  rw [weightPronicEnergy]
  rcases lt_or_ge T 99 with hT | hT
  · have hlog : Real.log ((T : ℝ) + 1) ≤ Real.log 100 :=
      Real.log_le_log (by positivity)
        (by have : (T : ℝ) ≤ 98 := by exact_mod_cast (by omega : T ≤ 98)
            linarith)
    have hnn : 0 ≤ ∑ n ∈ Icc 1 T, weightCenteredPrefix c (∑' d : ℕ, c d / d) n ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) := sum_nonneg fun n _ => by positivity
    have : (Real.log ((T : ℝ) + 1) - Real.log 100) / 1024 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg <;> linarith
    linarith
  · have hsub : Icc 100 T ⊆ Icc 1 T := Icc_subset_Icc (by norm_num) le_rfl
    have hlog := log_sub_log_le_sum_Icc_inv (a := 100) (by norm_num) (T := T) (by omega)
    push_cast at hlog
    calc (Real.log ((T : ℝ) + 1) - Real.log 100) / 1024
        = 1 / 1024 * (Real.log ((T : ℝ) + 1) - Real.log 100) := by ring
      _ ≤ 1 / 1024 * ∑ n ∈ Icc 100 T, (1 : ℝ) / n := mul_le_mul_of_nonneg_left hlog (by norm_num)
      _ = ∑ n ∈ Icc 100 T, 1 / 1024 * (1 / (n : ℝ)) := by rw [mul_sum]
      _ ≤ ∑ n ∈ Icc 100 T, weightCenteredPrefix c (∑' d : ℕ, c d / d) n ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1)) := sum_le_sum fun n hn => hcell n (mem_Icc.mp hn).1
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity

end

end GaloisForLFunctions.BezoutValuationIncidence
