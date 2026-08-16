import GaloisForLFunctions.RHTower.ParabolicDegreeTimeWedge

/-!
# The complete fixed-degree prime jet is invisible before the first-prime horizon

A fixed-degree Gaussian jet has Fourier transform bounded by a polynomial factor times
`e^{-ξ²/(4t)}`.  Splitting that Gaussian in half and using `log n ≥ log 2` for one half and `t ≤ 1`
for the other leaves the uniform superexponential factor `e^{-(log 2)²/(8t)}` in front of a prime
series that converges absolutely and does not depend on the time.  With `Λ(n) ≤ log n` this bounds
the whole prime modulation of the jet, not merely each atom separately, and no prime number theorem
or zero count is used.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## The time-free prime majorant -/

/-- The time-free prime majorant of a fixed-degree jet. -/
def primeJetMajorant (m : ℕ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
    * (1 + (Real.log n) ^ m) * Real.exp (-((Real.log n) ^ 2 / 8))

theorem primeJetMajorant_nonneg (m n : ℕ) : 0 ≤ primeJetMajorant m n := by
  rw [primeJetMajorant]
  have hvm : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  positivity

/-- **The prime majorant converges.** -/
theorem summable_primeJetMajorant (m : ℕ) : Summable (primeJetMajorant m) := by
  have hmaj : Summable (fun n : ℕ => (4 * (1 + 4 ^ m)) * ((n : ℝ) ^ ((13 : ℝ) / 4))⁻¹) :=
    (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hmaj ?_
  filter_upwards [Filter.eventually_ge_atTop (max 1 (Nat.ceil (Real.exp (8 * (m + 3)))))]
    with n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hceil : Nat.ceil (Real.exp (8 * (m + 3))) ≤ n := le_trans (le_max_right _ _) hn
  have hexpn : Real.exp (8 * ((m : ℝ) + 3)) ≤ (n : ℝ) := by
    have h := Nat.le_ceil (Real.exp (8 * ((m : ℝ) + 3)))
    exact le_trans h (by exact_mod_cast hceil)
  have hlog : 8 * ((m : ℝ) + 3) ≤ Real.log n := by
    have h := Real.log_le_log (Real.exp_pos _) hexpn
    rwa [Real.log_exp] at h
  have hlognn : 0 ≤ Real.log n := by
    have : (0 : ℝ) ≤ 8 * ((m : ℝ) + 3) := by positivity
    linarith
  -- the Gaussian beats the required power
  have hgauss : Real.exp (-((Real.log n) ^ 2 / 8)) ≤ ((n : ℝ) ^ ((m : ℝ) + 3))⁻¹ := by
    have hstep : ((m : ℝ) + 3) * Real.log n ≤ (Real.log n) ^ 2 / 8 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 8)]
      nlinarith
    have hexp : Real.exp (-((Real.log n) ^ 2 / 8)) ≤ Real.exp (-(((m : ℝ) + 3) * Real.log n)) :=
      Real.exp_le_exp.2 (by linarith)
    have hval : Real.exp (-(((m : ℝ) + 3) * Real.log n)) = ((n : ℝ) ^ ((m : ℝ) + 3))⁻¹ := by
      rw [Real.rpow_def_of_pos hnpos, ← Real.exp_neg]
      congr 1
      ring
    rwa [hval] at hexp
  -- the von Mangoldt and logarithm factors are small powers
  have hvm : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
    ArithmeticFunction.vonMangoldt_le_log
  have hvm0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hlogle : Real.log n ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := log_le_four_rpow hnpos
  have hpow : (1 : ℝ) + (Real.log n) ^ m ≤ (1 + 4 ^ m) * (n : ℝ) ^ ((m : ℝ) / 4) := by
    have hbase : (Real.log n) ^ m ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) ^ m :=
      pow_le_pow_left₀ hlognn hlogle m
    have hexpand : (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) ^ m = 4 ^ m * (n : ℝ) ^ ((m : ℝ) / 4) := by
      rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 4)) m, ← Real.rpow_mul hnpos.le]
      congr 2
      ring
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ ((m : ℝ) / 4) := by
      refine Real.one_le_rpow ?_ (by positivity)
      exact_mod_cast hn1
    rw [hexpand] at hbase
    nlinarith [hone, hbase, pow_nonneg (by norm_num : (0:ℝ) ≤ 4) m]
  have hinvhalf : (0 : ℝ) < ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by positivity
  have hchain : primeJetMajorant m n
      ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
          * ((1 + 4 ^ m) * (n : ℝ) ^ ((m : ℝ) / 4)) * ((n : ℝ) ^ ((m : ℝ) + 3))⁻¹ := by
    rw [primeJetMajorant]
    have h1 : ArithmeticFunction.vonMangoldt n ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) :=
      le_trans hvm hlogle
    have hA : (0 : ℝ) ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
      positivity
    have hB : (0 : ℝ) ≤ (1 + (Real.log n) ^ m) := by positivity
    have hC : (0 : ℝ) ≤ Real.exp (-((Real.log n) ^ 2 / 8)) := (Real.exp_pos _).le
    have hstep1 : ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
        ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ :=
      mul_le_mul_of_nonneg_right h1 hinvhalf.le
    have hstep2 : ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
          * (1 + (Real.log n) ^ m)
        ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
          * ((1 + 4 ^ m) * (n : ℝ) ^ ((m : ℝ) / 4)) := by
      refine mul_le_mul hstep1 hpow hB hA
    exact mul_le_mul hstep2 hgauss hC (by positivity)
  have hcollapse : (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
        * ((1 + 4 ^ m) * (n : ℝ) ^ ((m : ℝ) / 4)) * ((n : ℝ) ^ ((m : ℝ) + 3))⁻¹
      ≤ (4 * (1 + 4 ^ m)) * ((n : ℝ) ^ ((13 : ℝ) / 4))⁻¹ := by
    have hone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hcomb : (n : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
        * (n : ℝ) ^ ((m : ℝ) / 4) * ((n : ℝ) ^ ((m : ℝ) + 3))⁻¹
        = (n : ℝ) ^ (-((13 : ℝ) / 4) - 3 * (m : ℝ) / 4) := by
      rw [← Real.rpow_neg hnpos.le, ← Real.rpow_neg hnpos.le]
      rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
      congr 1
      ring
    have hmono : (n : ℝ) ^ (-((13 : ℝ) / 4) - 3 * (m : ℝ) / 4) ≤ (n : ℝ) ^ (-((13 : ℝ) / 4)) := by
      refine Real.rpow_le_rpow_of_exponent_le hone ?_
      have : (0 : ℝ) ≤ 3 * (m : ℝ) / 4 := by positivity
      linarith
    have hval : (n : ℝ) ^ (-((13 : ℝ) / 4)) = ((n : ℝ) ^ ((13 : ℝ) / 4))⁻¹ :=
      Real.rpow_neg hnpos.le _
    calc (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
          * ((1 + 4 ^ m) * (n : ℝ) ^ ((m : ℝ) / 4)) * ((n : ℝ) ^ ((m : ℝ) + 3))⁻¹
        = (4 * (1 + 4 ^ m)) * ((n : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
            * (n : ℝ) ^ ((m : ℝ) / 4) * ((n : ℝ) ^ ((m : ℝ) + 3))⁻¹) := by ring
      _ = (4 * (1 + 4 ^ m)) * (n : ℝ) ^ (-((13 : ℝ) / 4) - 3 * (m : ℝ) / 4) := by rw [hcomb]
      _ ≤ (4 * (1 + 4 ^ m)) * (n : ℝ) ^ (-((13 : ℝ) / 4)) := by
          refine mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (4 * (1 + 4 ^ m)) * ((n : ℝ) ^ ((13 : ℝ) / 4))⁻¹ := by rw [hval]
  rw [Real.norm_eq_abs, abs_of_nonneg (primeJetMajorant_nonneg m n)]
  linarith

/-! ## The horizon estimate -/

/-- **(24.130) The first-prime heat horizon.**  Under the fixed-degree jet bound the whole prime
modulation carries the uniform superexponential factor `e^{-(log 2)²/(8t)}`. -/
theorem sum_primeJet_le {m : ℕ} {K : ℝ} {G : ℕ → ℝ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hK : 0 ≤ K)
    (hG : ∀ n : ℕ, 2 ≤ n → |G n| ≤ K * (1 + (Real.log n) ^ m)
      * Real.exp (-((Real.log n) ^ 2 / (4 * t)))) (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N,
        (ArithmeticFunction.vonMangoldt n) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * |G n|
      ≤ (K * Real.exp (-((Real.log 2) ^ 2 / (8 * t)))) * ∑' n : ℕ, primeJetMajorant m n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ n ∈ Finset.Icc 2 N,
      (ArithmeticFunction.vonMangoldt n) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * |G n|
        ≤ (K * Real.exp (-((Real.log 2) ^ 2 / (8 * t)))) * primeJetMajorant m n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn2 : 2 ≤ n := hn.1
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this
    have hlogn : Real.log 2 ≤ Real.log n := by
      refine Real.log_le_log (by norm_num) ?_
      exact_mod_cast hn2
    have hsplit : Real.exp (-((Real.log n) ^ 2 / (4 * t)))
        ≤ Real.exp (-((Real.log 2) ^ 2 / (8 * t))) * Real.exp (-((Real.log n) ^ 2 / 8)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hsq : (Real.log 2) ^ 2 ≤ (Real.log n) ^ 2 := by nlinarith
      have hA : (Real.log 2) ^ 2 / (8 * t) ≤ (Real.log n) ^ 2 / (8 * t) := by
        refine div_le_div_of_nonneg_right hsq (by positivity)
      have hB : (Real.log n) ^ 2 / 8 ≤ (Real.log n) ^ 2 / (8 * t) := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        nlinarith
      have hhalf : (Real.log n) ^ 2 / (4 * t)
          = (Real.log n) ^ 2 / (8 * t) + (Real.log n) ^ 2 / (8 * t) := by
        field_simp
        ring
      linarith
    have hvm0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hinv : (0 : ℝ) < ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by positivity
    have hpoly : (0 : ℝ) ≤ 1 + (Real.log n) ^ m := by
      have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      positivity
    have hGn : |G n| ≤ K * (1 + (Real.log n) ^ m)
        * (Real.exp (-((Real.log 2) ^ 2 / (8 * t))) * Real.exp (-((Real.log n) ^ 2 / 8))) := by
      refine le_trans (hG n hn2) ?_
      exact mul_le_mul_of_nonneg_left hsplit (by positivity)
    have hfront : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ :=
      mul_nonneg hvm0 hinv.le
    calc ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * |G n|
        ≤ ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
            * (K * (1 + (Real.log n) ^ m)
              * (Real.exp (-((Real.log 2) ^ 2 / (8 * t)))
                * Real.exp (-((Real.log n) ^ 2 / 8)))) :=
          mul_le_mul_of_nonneg_left hGn hfront
      _ = (K * Real.exp (-((Real.log 2) ^ 2 / (8 * t)))) * primeJetMajorant m n := by
          rw [primeJetMajorant]
          ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Summable.sum_le_tsum _ (fun i _ => primeJetMajorant_nonneg m i)
    (summable_primeJetMajorant m)

end

end RHTower
