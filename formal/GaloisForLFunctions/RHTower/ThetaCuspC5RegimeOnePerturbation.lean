import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5HyperbolicGaussianTailCore
import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5ExactFirstAtomTailCore
import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5LikelihoodHomotopyCurvatureReduction
import GaloisForLFunctions.RHTower.ThetaCuspC5RegimeOneCurvatureSigns

/-!
# The completed C5 gate in regime I by perturbation from the single-atom gate

For `A(u − t) ≥ 6` and `t ≥ 1/4` the completed margin `M(1)` is compared with the single-atom
margin `M(0)` (a corpus theorem, `c5SingleAtomCompensationMargin_pos_of_sameHalfLine`) through
the affine likelihood homotopy: every completed jet is a single-atom jet plus a likelihood
correction (`a + da`, …), and in regime I the corrections are bounded by the moment majorants
of `ThetaCuspC5RegimeOneCurvatureSigns`.  The single-atom margin is bounded below through the
corpus factorisation `base = (2A + λ/r)(4A + d/r)·shape(t) + correction`, with the hyperbolic
Gaussian shape bounded below by a partial sum of its positive series.

## §1 The certificate series (public versions of the corpus lemmas)
-/

open Set

namespace RHTower

theorem hasSum_c5HyperbolicShiftedSinhTerm' (x : ℝ) :
    HasSum (c5HyperbolicShiftedSinhTerm x) (5 * x ^ 2 * Real.sinh x) := by
  have htail : HasSum (fun n => c5HyperbolicShiftedSinhTerm x (n + 1))
      (5 * x ^ 2 * Real.sinh x) := by
    have h := HasSum.const_smul (5 * x ^ 2) (Real.hasSum_sinh x)
    convert h using 1 <;> simp [c5HyperbolicShiftedSinhTerm, smul_eq_mul]
  have hfull := (hasSum_nat_add_iff (f := c5HyperbolicShiftedSinhTerm x) 1).1 htail
  simpa only [Finset.sum_range_one, c5HyperbolicShiftedSinhTerm, add_zero] using hfull

theorem hasSum_c5HyperbolicCertificateSeriesTerm' (x : ℝ) :
    HasSum (c5HyperbolicCertificateSeriesTerm x) (c5HyperbolicCertificate x) := by
  have h3 := HasSum.const_smul (18 : ℝ) (Real.hasSum_sinh (3 * x))
  have h2 := HasSum.const_smul (-119 / 2 : ℝ) (Real.hasSum_sinh (2 * x))
  have h1 := HasSum.const_smul (65 : ℝ) (Real.hasSum_sinh x)
  have hs := hasSum_c5HyperbolicShiftedSinhTerm' x
  have hc2 := HasSum.const_smul (-41 * x) (Real.hasSum_cosh (2 * x))
  have hc1 := HasSum.const_smul (129 * x) (Real.hasSum_cosh x)
  have hlin := hasSum_ite_eq (0 : ℕ) (-88 * x)
  have h := (((((h3.add h2).add h1).add hs).add hc2).add hc1).add hlin
  have hraw : HasSum (c5HyperbolicCertificateSeriesTerm x)
      (18 * Real.sinh (3 * x) - 119 / 2 * Real.sinh (2 * x) +
          65 * Real.sinh x + 5 * x ^ 2 * Real.sinh x -
        41 * x * Real.cosh (2 * x) + 129 * x * Real.cosh x + -88 * x) := by
    convert h using 1
    · funext n
      unfold c5HyperbolicCertificateSeriesTerm
      ring
    · ring
  have hvalue : c5HyperbolicCertificate x =
      18 * Real.sinh (3 * x) - 119 / 2 * Real.sinh (2 * x) +
          65 * Real.sinh x + 5 * x ^ 2 * Real.sinh x -
        41 * x * Real.cosh (2 * x) + 129 * x * Real.cosh x + -88 * x := by
    unfold c5HyperbolicCertificate
    rw [Real.sinh_three_mul, Real.sinh_two_mul, Real.cosh_two_mul]
    rw [Real.cosh_sq]
    ring
  rw [hvalue]
  exact hraw

theorem c5Hyperbolic_exponential_core_pos' {n : ℕ} (hn : 3 ≤ n) :
    (160 + 82 * (n : ℝ)) * (4 : ℝ) ^ n < 54 * (9 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ, pow_succ]
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hcoeff : 4 * (160 + 82 * ((n : ℝ) + 1)) <
          9 * (160 + 82 * (n : ℝ)) := by nlinarith
      have hpow : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _
      calc
        (160 + 82 * ((n + 1 : ℕ) : ℝ)) * 4 ^ (n + 1) =
            (4 * (160 + 82 * ((n : ℝ) + 1))) * 4 ^ n := by
              norm_num
              ring
        _ < (9 * (160 + 82 * (n : ℝ))) * 4 ^ n :=
          mul_lt_mul_of_pos_right hcoeff hpow
        _ < 9 * (54 * 9 ^ n) := by nlinarith
        _ = 54 * 9 ^ (n + 1) := by ring

/-- Closed form of the series term for `n ≥ 1`. -/
theorem c5HyperbolicCertificateSeriesTerm_succ_eq (x : ℝ) (k : ℕ) :
    c5HyperbolicCertificateSeriesTerm x (k + 1) =
      (54 * (9 : ℝ) ^ (k + 1) - (160 + 82 * ((k + 1 : ℕ) : ℝ)) * (4 : ℝ) ^ (k + 1) +
          (20 * ((k + 1 : ℕ) : ℝ) ^ 2 + 268 * ((k + 1 : ℕ) : ℝ) + 194)) *
        x ^ (2 * (k + 1) + 1) / (Nat.factorial (2 * (k + 1) + 1) : ℝ) := by
  simp only [c5HyperbolicCertificateSeriesTerm, c5HyperbolicShiftedSinhTerm]
  have hodd : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
  have heven : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  have hfacOdd : (Nat.factorial (2 * (k + 1) + 1) : ℝ) =
      ((2 * k + 3 : ℕ) : ℝ) * ((2 * k + 2 : ℕ) : ℝ) *
        (Nat.factorial (2 * k + 1) : ℝ) := by
    rw [hodd, show 2 * k + 1 + 2 = Nat.succ (Nat.succ (2 * k + 1)) by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hfacEven : (Nat.factorial (2 * (k + 1)) : ℝ) =
      ((2 * k + 2 : ℕ) : ℝ) * (Nat.factorial (2 * k + 1) : ℝ) := by
    rw [heven, show 2 * k + 1 + 1 = Nat.succ (2 * k + 1) by omega,
      Nat.factorial_succ]
    push_cast
    ring
  have hxpow : x ^ (2 * (k + 1) + 1) = x ^ 2 * x ^ (2 * k + 1) := by
    rw [hodd, pow_add]; ring
  have hxeven : x ^ (2 * (k + 1)) = x ^ 2 * x ^ (2 * k) := by
    rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add]
  have htwoOdd : (2 : ℝ) ^ (2 * (k + 1) + 1) = 2 * 4 ^ (k + 1) := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  have hthreeOdd : (3 : ℝ) ^ (2 * (k + 1) + 1) = 3 * 9 ^ (k + 1) := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  have htwoEven : (2 : ℝ) ^ (2 * (k + 1)) = 4 ^ (k + 1) := by
    rw [pow_mul]
    norm_num
  rw [hfacOdd, hfacEven]
  simp only [mul_pow]
  rw [hxpow, hxeven]
  rw [htwoOdd, hthreeOdd, htwoEven]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  push_cast
  field_simp [show (Nat.factorial (2 * k + 1) : ℝ) ≠ 0 by positivity]
  ring

theorem c5HyperbolicCertificateSeriesTerm_nonneg' {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ c5HyperbolicCertificateSeriesTerm x n := by
  rcases lt_trichotomy n 3 with hn | hn | hn
  · interval_cases n <;>
      simp [c5HyperbolicCertificateSeriesTerm, c5HyperbolicShiftedSinhTerm] <;>
      ring_nf <;> rfl
  · subst n
    simp [c5HyperbolicCertificateSeriesTerm, c5HyperbolicShiftedSinhTerm]
    ring_nf
    positivity
  · have hcore := c5Hyperbolic_exponential_core_pos' (show 3 ≤ n by omega)
    have hcoeff : 0 <
        54 * (9 : ℝ) ^ n - (160 + 82 * (n : ℝ)) * (4 : ℝ) ^ n +
          (20 * (n : ℝ) ^ 2 + 268 * (n : ℝ) + 194) := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [sq_nonneg (n : ℝ)]
    have hfac : 0 < (Nat.factorial (2 * n + 1) : ℝ) := by positivity
    have hpow : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx _
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [c5HyperbolicCertificateSeriesTerm_succ_eq]
    exact div_nonneg (mul_nonneg hcoeff.le hpow) hfac.le

/-- Partial sums bound the certificate from below. -/
theorem sum_range_le_c5HyperbolicCertificate {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    ∑ n ∈ Finset.range N, c5HyperbolicCertificateSeriesTerm x n ≤ c5HyperbolicCertificate x :=
  sum_le_hasSum (Finset.range N) (fun n _ => c5HyperbolicCertificateSeriesTerm_nonneg' hx n)
    (hasSum_c5HyperbolicCertificateSeriesTerm' x)

/-- The shape is twice the certificate at `2t`. -/
theorem c5HyperbolicGaussianBaseShape_eq (t : ℝ) :
    c5HyperbolicGaussianBaseShape t = 2 * c5HyperbolicCertificate (2 * t) := by
  unfold c5HyperbolicGaussianBaseShape thetaCuspSingleAtomReflectionDefect
  dsimp only
  unfold c5HyperbolicCertificate
  ring

/-- **Explicit lower bound for the shape:** the terms `n = 3, 4, 5` of the series. -/
theorem c5HyperbolicGaussianBaseShape_ge {t : ℝ} (ht : 0 ≤ t) :
    6656 / 9 * t ^ 7 + 615872 / 945 * t ^ 9 + 50560 / 189 * t ^ 11 ≤
      c5HyperbolicGaussianBaseShape t := by
  rw [c5HyperbolicGaussianBaseShape_eq]
  have h := sum_range_le_c5HyperbolicCertificate (x := 2 * t) (by linarith) 6
  have h0 : c5HyperbolicCertificateSeriesTerm (2 * t) 0 = 0 := by
    simp [c5HyperbolicCertificateSeriesTerm, c5HyperbolicShiftedSinhTerm]
    ring
  have h1 : c5HyperbolicCertificateSeriesTerm (2 * t) 1 = 0 := by
    rw [c5HyperbolicCertificateSeriesTerm_succ_eq]
    norm_num [Nat.factorial]
  have h2 : c5HyperbolicCertificateSeriesTerm (2 * t) 2 = 0 := by
    rw [c5HyperbolicCertificateSeriesTerm_succ_eq]
    norm_num [Nat.factorial]
  have h3 : c5HyperbolicCertificateSeriesTerm (2 * t) 3 = 3328 / 9 * t ^ 7 := by
    rw [c5HyperbolicCertificateSeriesTerm_succ_eq]
    norm_num [Nat.factorial]
    ring
  have h4 : c5HyperbolicCertificateSeriesTerm (2 * t) 4 = 307936 / 945 * t ^ 9 := by
    rw [c5HyperbolicCertificateSeriesTerm_succ_eq]
    norm_num [Nat.factorial]
    ring
  have h5 : c5HyperbolicCertificateSeriesTerm (2 * t) 5 = 25280 / 189 * t ^ 11 := by
    rw [c5HyperbolicCertificateSeriesTerm_succ_eq]
    norm_num [Nat.factorial]
    ring
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2, h3, h4, h5] at h
  linarith

/-! ## §2 Likelihood corrections in regime I -/

/-- `|J₁(x)| ≤ 6 A ε` and `0 ≤ LP(x) ≤ ε` in regime I. -/
theorem regimeOne_jetOne_logPartition_bounds {x : ℝ}
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodSourceLogPartitionJetOne x| ≤
      6 * thetaCuspSingleAtomReflectionScale 1 x * regimeOneLikelihoodScale x ∧
    0 ≤ thetaCuspLikelihoodSourceLogPartition x ∧
    thetaCuspLikelihoodSourceLogPartition x ≤ regimeOneLikelihoodScale x := by
  obtain ⟨hμ0, hμ, -, -, -, -⟩ := regimeOne_cumulant_bounds hA
  have hx : 0 ≤ x := (regimeOne_pos_of_six_le hA).le
  have hB := thetaCuspLikelihoodCoordinate_pos hx
  refine ⟨?_, ?_, ?_⟩
  · unfold thetaCuspLikelihoodSourceLogPartitionJetOne
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_nonneg (by linarith : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x), abs_of_nonneg hμ0]
    have := mul_le_mul_of_nonneg_left hμ
      (show 0 ≤ 2 * thetaCuspSingleAtomReflectionScale 1 x by linarith)
    linarith
  · unfold thetaCuspLikelihoodSourceLogPartition
    exact Real.log_nonneg (one_le_thetaCuspLikelihoodPartition hB)
  · unfold thetaCuspLikelihoodSourceLogPartition
    have hZ1 := one_le_thetaCuspLikelihoodPartition hB
    -- `Z − 1 = M₀ ≤ ε`
    have hr : thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) - 1 ≤
        regimeOneLikelihoodScale x := by
      unfold thetaCuspLikelihoodPartition
      rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
      have hB₀ : 0 < thetaCuspLikelihoodCoordinate 0 := thetaCuspLikelihoodCoordinate_pos le_rfl
      have hδ : ((0 : ℕ) : ℝ) / 3 ≤ thetaCuspLikelihoodCoordinate x - thetaCuspLikelihoodCoordinate 0 := by
        rw [thetaCuspLikelihoodCoordinate_sub_zero]
        have := Real.pi_lt_four
        simp only [Nat.cast_zero, zero_div]
        linarith
      have hcmp := thetaCuspHigherLikelihoodSpectralMoment_le_three_pow_mul_exp_support_comparison
        0 hB₀ hδ
      rw [thetaCuspLikelihoodCoordinate_sub_zero] at hcmp
      have hcal := thetaCuspHigherLikelihoodSpectralMoment_zero_coordinate_zero_lt
      simp only [pow_zero, one_mul] at hcmp
      unfold regimeOneLikelihoodScale
      have hE := (Real.exp_pos (-(3 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi)))).le
      calc 1 + thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 0 - 1
          = thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 0 := by ring
        _ ≤ Real.exp (-(3 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) *
            thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate 0) 0 := hcmp
        _ ≤ Real.exp (-(3 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) * (1 / 399) :=
            mul_le_mul_of_nonneg_left hcal.le hE
        _ = Real.exp (-(3 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399 := by ring
    calc Real.log (thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x))
        ≤ thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) - 1 :=
          Real.log_le_sub_one_of_pos (by linarith)
      _ ≤ regimeOneLikelihoodScale x := hr

/-- Monotone transport of `A^k ε` from the left endpoint. -/
theorem regimeOne_pow_scale_le_left {x y : ℝ} {k : ℕ} (hk : (k : ℝ) ≤ 18)
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) (hxy : x ≤ y) :
    thetaCuspSingleAtomReflectionScale 1 y ^ k * regimeOneLikelihoodScale y ≤
      thetaCuspSingleAtomReflectionScale 1 x ^ k * regimeOneLikelihoodScale x := by
  have hAxy : thetaCuspSingleAtomReflectionScale 1 x ≤ thetaCuspSingleAtomReflectionScale 1 y := by
    unfold thetaCuspSingleAtomReflectionScale
    have := Real.exp_le_exp.mpr (show 2 * x ≤ 2 * y by linarith)
    simp only [Nat.cast_one, one_pow, mul_one]
    exact mul_le_mul_of_nonneg_left this Real.pi_pos.le
  have h := pow_mul_regimeOneLikelihoodScale_le (k := k)
    (A₁ := thetaCuspSingleAtomReflectionScale 1 x) (x := y) (by linarith)
    (by rw [div_le_iff₀ (by linarith)]; linarith) hAxy
  rw [regimeOneLikelihoodScale_eq (x := x)]
  exact h

/-- The seven likelihood-correction jets of the homotopy in regime I, bounded by the left
endpoint scale `ε₋ = ε(u − t)` and `Am = A(u − t)`. -/
theorem regimeOne_homotopy_correction_bounds {u t : ℝ} (ht : 0 ≤ t)
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    let Am := thetaCuspSingleAtomReflectionScale 1 (u - t)
    let ε := regimeOneLikelihoodScale (u - t)
    |thetaCuspReflectedLikelihoodCumulantJetOne u t| ≤ 12 * Am * ε ∧
    |thetaCuspReflectedLikelihoodCumulantJetTwo u t| ≤ 76 * Am ^ 2 * ε ∧
    |thetaCuspReflectedLikelihoodCumulantJetThree u t| ≤ 522 * Am ^ 3 * ε ∧
    |c5LikelihoodScaleActionJetOne u t| ≤ 24 * Am * ε ∧
    |c5LikelihoodScaleMixedJetOne u t| ≤ 76 * Am ^ 2 * ε ∧
    |c5LikelihoodScaleMixedJetTwo u t| ≤ 522 * Am ^ 3 * ε ∧
    |thetaCuspReflectedLikelihoodCumulantAction u t| ≤ 4 * ε := by
  intro Am ε
  have hmono : ∀ x : ℝ, u - t ≤ x → 6 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    intro x hx
    refine le_trans hA ?_
    unfold thetaCuspSingleAtomReflectionScale
    have := Real.exp_le_exp.mpr (show 2 * (u - t) ≤ 2 * x by linarith)
    simp only [Nat.cast_one, one_pow, mul_one]
    exact mul_le_mul_of_nonneg_left this Real.pi_pos.le
  -- pointwise bounds transported to the left endpoint
  have hJ1 : ∀ x : ℝ, u - t ≤ x → |thetaCuspLikelihoodSourceLogPartitionJetOne x| ≤ 6 * Am * ε := by
    intro x hx
    have h := (regimeOne_jetOne_logPartition_bounds (hmono x hx)).1
    have hm := regimeOne_pow_scale_le_left (k := 1) (by norm_num) hA hx
    simp only [pow_one] at hm
    calc _ ≤ 6 * thetaCuspSingleAtomReflectionScale 1 x * regimeOneLikelihoodScale x := h
      _ = 6 * (thetaCuspSingleAtomReflectionScale 1 x * regimeOneLikelihoodScale x) := by ring
      _ ≤ 6 * (Am * ε) := by gcongr
      _ = 6 * Am * ε := by ring
  have hJ2 : ∀ x : ℝ, u - t ≤ x → |thetaCuspLikelihoodSourceLogPartitionJetTwo x| ≤ 38 * Am ^ 2 * ε := by
    intro x hx
    have h := regimeOne_jetTwo_bound (hmono x hx)
    have hm := regimeOne_pow_scale_le_left (k := 2) (by norm_num) hA hx
    calc _ ≤ 38 * thetaCuspSingleAtomReflectionScale 1 x ^ 2 * regimeOneLikelihoodScale x := h
      _ = 38 * (thetaCuspSingleAtomReflectionScale 1 x ^ 2 * regimeOneLikelihoodScale x) := by ring
      _ ≤ 38 * (Am ^ 2 * ε) := by gcongr
      _ = 38 * Am ^ 2 * ε := by ring
  have hJ3 : ∀ x : ℝ, u - t ≤ x → |thetaCuspLikelihoodSourceLogPartitionJetThree x| ≤
      261 * Am ^ 3 * ε := by
    intro x hx
    have h := regimeOne_jetThree_bound (hmono x hx)
    have hm := regimeOne_pow_scale_le_left (k := 3) (by norm_num) hA hx
    calc _ ≤ 261 * thetaCuspSingleAtomReflectionScale 1 x ^ 3 * regimeOneLikelihoodScale x := h
      _ = 261 * (thetaCuspSingleAtomReflectionScale 1 x ^ 3 * regimeOneLikelihoodScale x) := by ring
      _ ≤ 261 * (Am ^ 3 * ε) := by gcongr
      _ = 261 * Am ^ 3 * ε := by ring
  have hLP : ∀ x : ℝ, u - t ≤ x → |thetaCuspLikelihoodSourceLogPartition x| ≤ ε := by
    intro x hx
    have h := regimeOne_jetOne_logPartition_bounds (hmono x hx)
    have hm := regimeOne_pow_scale_le_left (k := 0) (by norm_num) hA hx
    simp only [pow_zero, one_mul] at hm
    rw [abs_of_nonneg h.2.1]
    exact h.2.2.trans hm
  have hl : u - t ≤ u - t := le_rfl
  have hc : u - t ≤ u := by linarith
  have hr : u - t ≤ u + t := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold thetaCuspReflectedLikelihoodCumulantJetOne
    have := abs_sub _ _ |>.trans (add_le_add (hJ1 _ hl) (hJ1 _ hr))
    linarith
  · unfold thetaCuspReflectedLikelihoodCumulantJetTwo
    have h1 := hJ2 _ hr
    have h2 := hJ2 _ hl
    calc |-thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t) -
          thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t)|
        ≤ |-thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t)| +
          |thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t)| := abs_sub _ _
      _ ≤ 38 * Am ^ 2 * ε + 38 * Am ^ 2 * ε := by rw [abs_neg]; exact add_le_add h1 h2
      _ = 76 * Am ^ 2 * ε := by ring
  · unfold thetaCuspReflectedLikelihoodCumulantJetThree
    have := abs_sub _ _ |>.trans (add_le_add (hJ3 _ hl) (hJ3 _ hr))
    linarith
  · unfold c5LikelihoodScaleActionJetOne
    have h1 := hJ1 _ hc
    have h2 := hJ1 _ hr
    have h3 := hJ1 _ hl
    calc |2 * thetaCuspLikelihoodSourceLogPartitionJetOne u -
          thetaCuspLikelihoodSourceLogPartitionJetOne (u + t) -
          thetaCuspLikelihoodSourceLogPartitionJetOne (u - t)|
        ≤ |2 * thetaCuspLikelihoodSourceLogPartitionJetOne u -
            thetaCuspLikelihoodSourceLogPartitionJetOne (u + t)| +
          |thetaCuspLikelihoodSourceLogPartitionJetOne (u - t)| := abs_sub _ _
      _ ≤ (|2 * thetaCuspLikelihoodSourceLogPartitionJetOne u| +
            |thetaCuspLikelihoodSourceLogPartitionJetOne (u + t)|) +
          |thetaCuspLikelihoodSourceLogPartitionJetOne (u - t)| := by
            gcongr
            exact abs_sub _ _
      _ ≤ (2 * (6 * Am * ε) + 6 * Am * ε) + 6 * Am * ε := by
            rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
            gcongr
      _ = 24 * Am * ε := by ring
  · unfold c5LikelihoodScaleMixedJetOne
    have := abs_sub _ _ |>.trans (add_le_add (hJ2 _ hl) (hJ2 _ hr))
    linarith
  · unfold c5LikelihoodScaleMixedJetTwo
    have h1 := hJ3 _ hr
    have h2 := hJ3 _ hl
    calc |-thetaCuspLikelihoodSourceLogPartitionJetThree (u + t) -
          thetaCuspLikelihoodSourceLogPartitionJetThree (u - t)|
        ≤ |-thetaCuspLikelihoodSourceLogPartitionJetThree (u + t)| +
          |thetaCuspLikelihoodSourceLogPartitionJetThree (u - t)| := abs_sub _ _
      _ ≤ 522 * Am ^ 3 * ε := by rw [abs_neg]; linarith
  · unfold thetaCuspReflectedLikelihoodCumulantAction
    have h1 := hLP _ hc
    have h2 := hLP _ hr
    have h3 := hLP _ hl
    calc |2 * thetaCuspLikelihoodSourceLogPartition u - thetaCuspLikelihoodSourceLogPartition (u + t) -
          thetaCuspLikelihoodSourceLogPartition (u - t)|
        ≤ |2 * thetaCuspLikelihoodSourceLogPartition u - thetaCuspLikelihoodSourceLogPartition (u + t)| +
          |thetaCuspLikelihoodSourceLogPartition (u - t)| := abs_sub _ _
      _ ≤ (|2 * thetaCuspLikelihoodSourceLogPartition u| +
            |thetaCuspLikelihoodSourceLogPartition (u + t)|) +
          |thetaCuspLikelihoodSourceLogPartition (u - t)| := by
            gcongr
            exact abs_sub _ _
      _ ≤ (2 * ε + ε) + ε := by
            rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
            gcongr
      _ = 4 * ε := by ring

/-! ## §3 Single-atom jet sizes for `A ≥ 6` -/

theorem thetaCuspSingleAtomReflectionLambda_le {A : ℝ} (hA : 6 ≤ A) :
    thetaCuspSingleAtomReflectionLambda A ≤ 6 / A := by
  unfold thetaCuspSingleAtomReflectionLambda
  rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (by linarith)]
  nlinarith

theorem abs_c5SingleAtomScaleLambdaJetOne_le {A : ℝ} (hA : 6 ≤ A) :
    |c5SingleAtomScaleLambdaJetOne A| ≤ 18 / A := by
  unfold c5SingleAtomScaleLambdaJetOne
  have hden : 0 < (A - 3 / 2) ^ 3 := pow_pos (by linarith) 3
  rw [abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 6),
    abs_of_pos (by linarith : (0:ℝ) < A), abs_of_pos (by linarith : (0:ℝ) < A + 3 / 2)]
  rw [div_le_div_iff₀ hden (by linarith)]
  nlinarith [sq_nonneg (A - 6), sq_nonneg A]

/-- Sizes of the single-atom jets for `A ≥ 6`, `z ≥ 0`, `z' ≥ 0`, `1/2 < r ≤ 1`. -/
theorem singleAtom_jet_bounds {A z z' : ℝ} (hA : 6 ≤ A) (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (hr : 1 / 2 < thetaCuspSingleAtomReflectionFactor A z) :
    let l := thetaCuspSingleAtomReflectionLambda A
    let d := c5SingleAtomScaleLambdaJetOne A
    let r := thetaCuspSingleAtomReflectionFactor A z
    |thetaCuspSingleAtomReflectedActionJetOne A z z'| ≤ (2 * A + 12 / A) * z' ∧
    |thetaCuspSingleAtomReflectedActionJetTwo A z| ≤
      4 * (12 / A) ^ 2 * z * (z + 2) + 4 * (2 * A + 12 / A) * (z + 1) ∧
    |thetaCuspSingleAtomReflectedActionJetThree A z z'| ≤
      z' * (8 * (12 / A) ^ 3 * z * (z + 2) + 12 * (12 / A) ^ 2 * (z + 1) + 4 * (2 * A + 12 / A)) ∧
    |c5SingleAtomScaleActionJetOne A z| ≤ 4 * A * z + 36 / A * z ∧
    |c5SingleAtomScaleMixedJetOne A z z'| ≤ (4 * A + 72 / A) * z' ∧
    |c5SingleAtomScaleMixedJetTwo A z| ≤
      4 * (1728 / A ^ 2 * z * (z + 2) + (4 * A + 72 / A) * (z + 1)) ∧
    2 * A ≤ thetaCuspSingleAtomReflectionSlope A z ∧
    4 * A - 36 / A ≤ 4 * A + d / r := by
  intro l d r
  have hA0 : 0 < A := by linarith
  have hl := thetaCuspSingleAtomReflectionLambda_le hA
  have hl0 := thetaCuspSingleAtomReflectionLambda_pos (show (3:ℝ) < A by linarith)
  have hd := abs_c5SingleAtomScaleLambdaJetOne_le hA
  have hr0 : 0 < r := by linarith
  have hr1 : r ≤ 1 := by
    show thetaCuspSingleAtomReflectionFactor A z ≤ 1
    unfold thetaCuspSingleAtomReflectionFactor
    have : 0 ≤ thetaCuspSingleAtomReflectionLambda A * z := mul_nonneg hl0.le hz
    linarith
  have hlr : l / r ≤ 12 / A := by
    rw [div_le_iff₀ hr0]
    calc l ≤ 6 / A := hl
      _ = 12 / A * (1 / 2) := by ring
      _ ≤ 12 / A * r := by gcongr
  have hlr0 : 0 ≤ l / r := div_nonneg hl0.le hr0.le
  have hdr : |d| / r ≤ 36 / A := by
    rw [div_le_iff₀ hr0]
    calc |d| ≤ 18 / A := hd
      _ = 36 / A * (1 / 2) := by ring
      _ ≤ 36 / A * r := by gcongr
  have hdr2 : |d| / r ^ 2 ≤ 72 / A := by
    rw [div_le_iff₀ (by positivity)]
    calc |d| ≤ 18 / A := hd
      _ = 72 / A * (1 / 2) ^ 2 := by ring
      _ ≤ 72 / A * r ^ 2 := by gcongr
  have hdr3 : |d| / r ^ 3 ≤ 144 / A := by
    rw [div_le_iff₀ (by positivity)]
    calc |d| ≤ 18 / A := hd
      _ = 144 / A * (1 / 2) ^ 3 := by ring
      _ ≤ 144 / A * r ^ 3 := by gcongr
  have hslope : thetaCuspSingleAtomReflectionSlope A z = 2 * A + l / r := rfl
  have hslope_le : thetaCuspSingleAtomReflectionSlope A z ≤ 2 * A + 12 / A := by
    rw [hslope]; linarith
  have hslope_ge : 2 * A ≤ thetaCuspSingleAtomReflectionSlope A z := by
    rw [hslope]; linarith
  have hslope0 : 0 ≤ thetaCuspSingleAtomReflectionSlope A z := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hslope_ge, ?_⟩
  · unfold thetaCuspSingleAtomReflectedActionJetOne
    rw [abs_mul, abs_of_nonneg hslope0, abs_of_nonneg hz']
    exact mul_le_mul_of_nonneg_right hslope_le hz'
  · unfold thetaCuspSingleAtomReflectedActionJetTwo
    have h1 : 0 ≤ 4 * (l ^ 2 / r ^ 2) * z * (z + 2) := by positivity
    have h2 : 0 ≤ 4 * thetaCuspSingleAtomReflectionSlope A z * (z + 1) := by positivity
    rw [abs_of_nonneg (by positivity)]
    have hlr2 : l ^ 2 / r ^ 2 ≤ (12 / A) ^ 2 := by
      rw [← div_pow]; exact pow_le_pow_left₀ hlr0 hlr 2
    have e1 : 4 * (l ^ 2 / r ^ 2) * z * (z + 2) ≤ 4 * (12 / A) ^ 2 * z * (z + 2) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlr2 hz) (by linarith : 0 ≤ z + 2)
      linarith
    have e2 := mul_le_mul_of_nonneg_right hslope_le (by linarith : 0 ≤ z + 1)
    show 4 * (l ^ 2 / r ^ 2) * z * (z + 2) + 4 * thetaCuspSingleAtomReflectionSlope A z * (z + 1) ≤ _
    linarith
  · unfold thetaCuspSingleAtomReflectedActionJetThree
    rw [abs_mul, abs_of_nonneg hz']
    have hlr2 : l ^ 2 / r ^ 2 ≤ (12 / A) ^ 2 := by
      rw [← div_pow]; exact pow_le_pow_left₀ hlr0 hlr 2
    have hlr3 : l ^ 3 / r ^ 3 ≤ (12 / A) ^ 3 := by
      rw [← div_pow]; exact pow_le_pow_left₀ hlr0 hlr 3
    have hin : 0 ≤ 8 * (l ^ 3 / r ^ 3) * z * (z + 2) + 12 * (l ^ 2 / r ^ 2) * (z + 1) +
        4 * thetaCuspSingleAtomReflectionSlope A z := by positivity
    rw [abs_of_nonneg hin]
    apply mul_le_mul_of_nonneg_left _ hz'
    have e1 : 8 * (l ^ 3 / r ^ 3) * z * (z + 2) ≤ 8 * (12 / A) ^ 3 * z * (z + 2) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlr3 hz) (by linarith : 0 ≤ z + 2)
      linarith
    have e2 : 12 * (l ^ 2 / r ^ 2) * (z + 1) ≤ 12 * (12 / A) ^ 2 * (z + 1) := by
      have := mul_le_mul_of_nonneg_right hlr2 (by linarith : 0 ≤ z + 1)
      linarith
    linarith
  · unfold c5SingleAtomScaleActionJetOne
    have e : |d * z / r| ≤ 36 / A * z := by
      rw [abs_div, abs_mul, abs_of_nonneg hz, abs_of_pos hr0]
      calc |d| * z / r = (|d| / r) * z := by ring
        _ ≤ 36 / A * z := mul_le_mul_of_nonneg_right hdr hz
    calc |4 * A * z + d * z / r| ≤ |4 * A * z| + |d * z / r| := abs_add_le _ _
      _ ≤ 4 * A * z + 36 / A * z := by
          rw [abs_of_nonneg (by positivity)]
          linarith
  · unfold c5SingleAtomScaleMixedJetOne
    rw [abs_mul, abs_of_nonneg hz']
    apply mul_le_mul_of_nonneg_right _ hz'
    calc |4 * A + d / r ^ 2| ≤ |4 * A| + |d / r ^ 2| := abs_add_le _ _
      _ ≤ 4 * A + 72 / A := by
          rw [abs_of_pos (by linarith), abs_div, abs_of_pos (by positivity : 0 < r ^ 2)]
          linarith
  · unfold c5SingleAtomScaleMixedJetTwo
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have e1 : |2 * l * d / r ^ 3 * z * (z + 2)| ≤ 1728 / A ^ 2 * z * (z + 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hz, abs_of_nonneg (by linarith : (0:ℝ) ≤ z + 2)]
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      apply mul_le_mul_of_nonneg_right _ hz
      rw [abs_div, abs_of_pos (by positivity : 0 < r ^ 3), abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hl0]
      have hr3 : r ^ 3 = r * r ^ 2 := by ring
      calc 2 * l * |d| / r ^ 3 = 2 * (l / r) * (|d| / r ^ 2) := by
            rw [hr3]; field_simp
        _ ≤ 2 * (12 / A) * (72 / A) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hlr (by norm_num)) hdr2
              (div_nonneg (abs_nonneg _) (by positivity)) (by positivity)
        _ = 1728 / A ^ 2 := by ring
    have e2 : |(4 * A + d / r ^ 2) * (z + 1)| ≤ (4 * A + 72 / A) * (z + 1) := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ z + 1)]
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      calc |4 * A + d / r ^ 2| ≤ |4 * A| + |d / r ^ 2| := abs_add_le _ _
        _ ≤ 4 * A + 72 / A := by
            rw [abs_of_pos (by linarith), abs_div, abs_of_pos (by positivity : 0 < r ^ 2)]
            linarith
    calc |2 * l * d / r ^ 3 * z * (z + 2) + (4 * A + d / r ^ 2) * (z + 1)|
        ≤ |2 * l * d / r ^ 3 * z * (z + 2)| + |(4 * A + d / r ^ 2) * (z + 1)| := abs_add_le _ _
      _ ≤ _ := add_le_add e1 e2
  · have := (abs_le.mp (show |d / r| ≤ 36 / A by
      rw [abs_div, abs_of_pos hr0]; exact hdr)).1
    linarith

/-! ## §4 Differences along the affine homotopy -/

namespace C5LikelihoodAffineData

theorem velocitySlope_one_sub_zero (d : C5LikelihoodAffineData) :
    d.velocitySlope 1 - d.velocitySlope 0 = d.velocitySlopeOne 0 + d.velocitySlopeTwo / 2 := by
  unfold velocitySlope velocitySlopeOne velocitySlopeTwo jetOne jetTwo jetThree scaleAction
    scaleMixedOne scaleMixedTwo affine
  ring

theorem velocityCenter_one_sub_zero (d : C5LikelihoodAffineData) :
    d.velocityCenter 1 - d.velocityCenter 0 = d.velocityCenterOne 0 + d.velocityCenterTwo / 2 := by
  unfold velocityCenter velocityCenterOne velocityCenterTwo jetOne jetTwo scaleAction
    scaleMixedOne affine
  ring

theorem compensation_one_sub_zero (d : C5LikelihoodAffineData) :
    d.compensation 1 - d.compensation 0 =
      5 * (d.velocitySlope 1 - d.velocitySlope 0) -
        (d.boseCoefficient 1 - d.boseCoefficient 0) * d.velocityCenter 1 -
        d.boseCoefficient 0 * (d.velocityCenter 1 - d.velocityCenter 0) := by
  unfold compensation
  ring

/-- Bound expressions. -/
noncomputable def slopeDiffBound (t a' b' c' s' m' n' da' db' dc' ds' dm' dn' : ℝ) : ℝ :=
  da' * (t * m' + t ^ 2 * n') + a' * (t * dm' + t ^ 2 * dn') +
    (da' + 3 * t * db' + t ^ 2 * dc') * s' + (a' + 3 * t * b' + t ^ 2 * c') * ds' +
    (da' * (t * dm' + t ^ 2 * dn') + (da' + 3 * t * db' + t ^ 2 * dc') * ds')

noncomputable def centerDiffBound (t a' b' s' m' da' db' ds' dm' : ℝ) : ℝ :=
  da' * (t * m') + a' * (t * dm') + (da' + t * db') * s' + (a' + t * b') * ds' +
    (da' * (t * dm') + (da' + t * db') * ds')

noncomputable def centerZeroBound (t a' b' s' m' : ℝ) : ℝ := a' * (t * m') + (a' + t * b') * s'

noncomputable def boseZeroBound (t a' q : ℝ) : ℝ := 14 + 10 * t * a' + 16 * t * a' * Real.exp (-q)

noncomputable def boseDiffBound (t a' da' dq' q : ℝ) : ℝ :=
  10 * t * da' + 48 * t * da' * Real.exp (-q) + 192 * t * a' * dq' * Real.exp (-q)

noncomputable def compensationDiffBound (t a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' q : ℝ) : ℝ :=
  5 * slopeDiffBound t a' b' c' s' m' n' da' db' dc' ds' dm' dn' +
    boseDiffBound t a' da' dq' q *
      (centerZeroBound t a' b' s' m' + centerDiffBound t a' b' s' m' da' db' ds' dm') +
    boseZeroBound t a' q * centerDiffBound t a' b' s' m' da' db' ds' dm'

theorem abs_three_term_le {t x y z x' y' z' : ℝ} (ht : 0 ≤ t) (k : ℝ) (hk : 0 ≤ k)
    (hx : |x| ≤ x') (hy : |y| ≤ y') (hz : |z| ≤ z') :
    |x + k * t * y + t ^ 2 * z| ≤ x' + k * t * y' + t ^ 2 * z' := by
  have ht2 : 0 ≤ t ^ 2 := by positivity
  calc |x + k * t * y + t ^ 2 * z| ≤ |x + k * t * y| + |t ^ 2 * z| := abs_add_le _ _
    _ ≤ (|x| + |k * t * y|) + |t ^ 2 * z| := by gcongr; exact abs_add_le _ _
    _ = |x| + k * t * |y| + t ^ 2 * |z| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg ht2, abs_of_nonneg hk]
    _ ≤ x' + k * t * y' + t ^ 2 * z' := by gcongr

theorem abs_two_term_le {t x y x' y' : ℝ} (ht : 0 ≤ t) (hx : |x| ≤ x') (hy : |y| ≤ y') :
    |t * x + t ^ 2 * y| ≤ t * x' + t ^ 2 * y' := by
  have ht2 : 0 ≤ t ^ 2 := by positivity
  calc |t * x + t ^ 2 * y| ≤ |t * x| + |t ^ 2 * y| := abs_add_le _ _
    _ = t * |x| + t ^ 2 * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg ht2]
    _ ≤ t * x' + t ^ 2 * y' := by gcongr

theorem abs_mul_le_of_abs_le {x y x' y' : ℝ} (hx : |x| ≤ x') (hy : |y| ≤ y') : |x * y| ≤ x' * y' := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)

/-- Generic bound on the velocity-slope difference from bounds on the fields. -/
theorem abs_velocitySlope_diff_le (d : C5LikelihoodAffineData) {a' b' c' s' m' n' da' db' dc' ds' dm' dn' : ℝ}
    (ht : 0 ≤ d.t)
    (ha : |d.a| ≤ a') (hb : |d.b| ≤ b') (hc : |d.c| ≤ c') (hs : |d.s| ≤ s') (hm : |d.m| ≤ m')
    (hn : |d.n| ≤ n') (hda : |d.da| ≤ da') (hdb : |d.db| ≤ db') (hdc : |d.dc| ≤ dc')
    (hds : |d.ds| ≤ ds') (hdm : |d.dm| ≤ dm') (hdn : |d.dn| ≤ dn') :
    |d.velocitySlope 1 - d.velocitySlope 0| ≤
      slopeDiffBound d.t a' b' c' s' m' n' da' db' dc' ds' dm' dn' := by
  rw [velocitySlope_one_sub_zero]
  unfold velocitySlopeOne velocitySlopeTwo jetOne jetTwo jetThree scaleAction scaleMixedOne
    scaleMixedTwo affine slopeDiffBound
  simp only [zero_mul, add_zero]
  have h1 := abs_mul_le_of_abs_le hda (abs_two_term_le ht hm hn)
  have h2 := abs_mul_le_of_abs_le ha (abs_two_term_le ht hdm hdn)
  have hbr := abs_three_term_le ht 3 (by norm_num) hda hdb hdc
  have hbr' := abs_three_term_le ht 3 (by norm_num) ha hb hc
  have h3 := abs_mul_le_of_abs_le hbr hs
  have h4 := abs_mul_le_of_abs_le hbr' hds
  have h5 := abs_mul_le_of_abs_le hda (abs_two_term_le ht hdm hdn)
  have h6 := abs_mul_le_of_abs_le hbr hds
  have hsplit : d.da * (d.t * d.m + d.t ^ 2 * d.n) + d.a * (d.t * d.dm + d.t ^ 2 * d.dn) -
        (d.da + 3 * d.t * d.db + d.t ^ 2 * d.dc) * d.s -
        (d.a + 3 * d.t * d.b + d.t ^ 2 * d.c) * d.ds +
        2 * (d.da * (d.t * d.dm + d.t ^ 2 * d.dn) -
          (d.da + 3 * d.t * d.db + d.t ^ 2 * d.dc) * d.ds) / 2 =
      d.da * (d.t * d.m + d.t ^ 2 * d.n) + d.a * (d.t * d.dm + d.t ^ 2 * d.dn) -
        (d.da + 3 * d.t * d.db + d.t ^ 2 * d.dc) * d.s -
        (d.a + 3 * d.t * d.b + d.t ^ 2 * d.c) * d.ds +
        (d.da * (d.t * d.dm + d.t ^ 2 * d.dn) -
          (d.da + 3 * d.t * d.db + d.t ^ 2 * d.dc) * d.ds) := by ring
  rw [hsplit]
  have e1 := abs_le.mp h1
  have e2 := abs_le.mp h2
  have e3 := abs_le.mp h3
  have e4 := abs_le.mp h4
  have e5 := abs_le.mp h5
  have e6 := abs_le.mp h6
  rw [abs_le]
  constructor <;> linarith only [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2]

/-- Generic bound on the velocity-centre difference. -/
theorem abs_velocityCenter_diff_le (d : C5LikelihoodAffineData) {a' b' s' m' da' db' ds' dm' : ℝ}
    (ht : 0 ≤ d.t)
    (ha : |d.a| ≤ a') (hb : |d.b| ≤ b') (hs : |d.s| ≤ s') (hm : |d.m| ≤ m')
    (hda : |d.da| ≤ da') (hdb : |d.db| ≤ db') (hds : |d.ds| ≤ ds') (hdm : |d.dm| ≤ dm') :
    |d.velocityCenter 1 - d.velocityCenter 0| ≤ centerDiffBound d.t a' b' s' m' da' db' ds' dm' := by
  rw [velocityCenter_one_sub_zero]
  unfold velocityCenterOne velocityCenterTwo jetOne jetTwo scaleAction scaleMixedOne affine
    centerDiffBound
  simp only [zero_mul, add_zero]
  have htm : |d.t * d.m| ≤ d.t * m' := by
    rw [abs_mul, abs_of_nonneg ht]; exact mul_le_mul_of_nonneg_left hm ht
  have htdm : |d.t * d.dm| ≤ d.t * dm' := by
    rw [abs_mul, abs_of_nonneg ht]; exact mul_le_mul_of_nonneg_left hdm ht
  have h1 := abs_mul_le_of_abs_le hda htm
  have h2 := abs_mul_le_of_abs_le ha htdm
  have hbr : |d.da + d.t * d.db| ≤ da' + d.t * db' := by
    calc |d.da + d.t * d.db| ≤ |d.da| + |d.t * d.db| := abs_add_le _ _
      _ = |d.da| + d.t * |d.db| := by rw [abs_mul, abs_of_nonneg ht]
      _ ≤ da' + d.t * db' := by gcongr
  have hbr' : |d.a + d.t * d.b| ≤ a' + d.t * b' := by
    calc |d.a + d.t * d.b| ≤ |d.a| + |d.t * d.b| := abs_add_le _ _
      _ = |d.a| + d.t * |d.b| := by rw [abs_mul, abs_of_nonneg ht]
      _ ≤ a' + d.t * b' := by gcongr
  have h3 := abs_mul_le_of_abs_le hbr hs
  have h4 := abs_mul_le_of_abs_le hbr' hds
  have h5 := abs_mul_le_of_abs_le hda htdm
  have h6 := abs_mul_le_of_abs_le hbr hds
  have hsplit : d.da * (d.t * d.m) + d.a * (d.t * d.dm) - (d.da + d.t * d.db) * d.s -
        (d.a + d.t * d.b) * d.ds + 2 * (d.da * (d.t * d.dm) - (d.da + d.t * d.db) * d.ds) / 2 =
      d.da * (d.t * d.m) + d.a * (d.t * d.dm) - (d.da + d.t * d.db) * d.s -
        (d.a + d.t * d.b) * d.ds + (d.da * (d.t * d.dm) - (d.da + d.t * d.db) * d.ds) := by ring
  rw [hsplit]
  have e1 := abs_le.mp h1
  have e2 := abs_le.mp h2
  have e3 := abs_le.mp h3
  have e4 := abs_le.mp h4
  have e5 := abs_le.mp h5
  have e6 := abs_le.mp h6
  rw [abs_le]
  constructor <;> linarith only [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2]

/-- The velocity centre at `l = 0` in raw size. -/
theorem abs_velocityCenter_zero_le (d : C5LikelihoodAffineData) {a' b' s' m' : ℝ} (ht : 0 ≤ d.t)
    (ha : |d.a| ≤ a') (hb : |d.b| ≤ b') (hs : |d.s| ≤ s') (hm : |d.m| ≤ m') :
    |d.velocityCenter 0| ≤ centerZeroBound d.t a' b' s' m' := by
  unfold velocityCenter jetOne jetTwo scaleAction scaleMixedOne affine centerZeroBound
  simp only [zero_mul, add_zero]
  have htm : |d.t * d.m| ≤ d.t * m' := by
    rw [abs_mul, abs_of_nonneg ht]; exact mul_le_mul_of_nonneg_left hm ht
  have h1 := abs_mul_le_of_abs_le ha htm
  have hbr' : |d.a + d.t * d.b| ≤ a' + d.t * b' := by
    calc |d.a + d.t * d.b| ≤ |d.a| + |d.t * d.b| := abs_add_le _ _
      _ = |d.a| + d.t * |d.b| := by rw [abs_mul, abs_of_nonneg ht]
      _ ≤ a' + d.t * b' := by gcongr
  have h2 := abs_mul_le_of_abs_le hbr' hs
  calc |d.a * (d.t * d.m) - (d.a + d.t * d.b) * d.s|
      ≤ |d.a * (d.t * d.m)| + |(d.a + d.t * d.b) * d.s| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

/-- Bose reciprocal bounds: for `2 ≤ q` and `|dq| ≤ 1`, `ρ(0) ≤ 2e^{-q}`, `ρ(1) ≤ 6e^{-q}` and
`|ρ(1) − ρ(0)| ≤ 24 |dq| e^{-q}`. -/
theorem boseReciprocal_bounds (d : C5LikelihoodAffineData) (hq : 2 ≤ d.q) (hdq : |d.dq| ≤ 1) :
    0 ≤ d.boseReciprocal 0 ∧ d.boseReciprocal 0 ≤ 2 * Real.exp (-d.q) ∧
    0 ≤ d.boseReciprocal 1 ∧ d.boseReciprocal 1 ≤ 6 * Real.exp (-d.q) ∧
    |d.boseReciprocal 1 - d.boseReciprocal 0| ≤ 24 * |d.dq| * Real.exp (-d.q) := by
  have hact0 : d.action 0 = d.q := by simp [action, affine]
  have hact1 : d.action 1 = d.q + d.dq := by simp [action, affine]
  have hdq' := abs_le.mp hdq
  have hE : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9; linarith
  have hE' : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he0 : 0 < Real.exp d.q := Real.exp_pos _
  have hexp2 : (7 : ℝ) < Real.exp 2 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have := mul_lt_mul'' hE' hE' (by norm_num) (by norm_num)
    linarith
  have hq4 : 7 ≤ Real.exp d.q := le_trans hexp2.le (Real.exp_le_exp.mpr hq)
  have hden0 : Real.exp d.q / 2 ≤ Real.exp d.q - 1 := by linarith
  have hden0pos : 0 < Real.exp d.q - 1 := by linarith
  have hqdq : Real.exp (d.q - 1) ≤ Real.exp (d.q + d.dq) := Real.exp_le_exp.mpr (by linarith)
  have hqm1 : Real.exp (d.q - 1) = Real.exp d.q / Real.exp 1 := by rw [Real.exp_sub]
  have hden1 : Real.exp d.q / 6 ≤ Real.exp (d.q + d.dq) - 1 := by
    have h1 : Real.exp d.q / 3 ≤ Real.exp (d.q - 1) := by
      rw [hqm1]; exact div_le_div_of_nonneg_left he0.le (by linarith) hE.le
    have h2 : Real.exp d.q / 6 ≤ Real.exp d.q / 3 - 1 := by linarith
    linarith
  have hden1pos : 0 < Real.exp (d.q + d.dq) - 1 := by linarith
  have hρ0 : d.boseReciprocal 0 = 1 / (Real.exp d.q - 1) := by
    unfold boseReciprocal; rw [hact0]
  have hρ1 : d.boseReciprocal 1 = 1 / (Real.exp (d.q + d.dq) - 1) := by
    unfold boseReciprocal; rw [hact1]
  have hexpneg : Real.exp (-d.q) = 1 / Real.exp d.q := by rw [Real.exp_neg]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hρ0]; positivity
  · rw [hρ0, hexpneg, div_le_iff₀ hden0pos]
    rw [show 2 * (1 / Real.exp d.q) * (Real.exp d.q - 1) = 2 * (Real.exp d.q - 1) / Real.exp d.q by ring,
      le_div_iff₀ he0]
    linarith
  · rw [hρ1]; positivity
  · rw [hρ1, hexpneg, div_le_iff₀ hden1pos]
    rw [show 6 * (1 / Real.exp d.q) * (Real.exp (d.q + d.dq) - 1) =
      6 * (Real.exp (d.q + d.dq) - 1) / Real.exp d.q by ring, le_div_iff₀ he0]
    linarith
  · rw [hρ1, hρ0]
    have hdiff : 1 / (Real.exp (d.q + d.dq) - 1) - 1 / (Real.exp d.q - 1) =
        (Real.exp d.q - Real.exp (d.q + d.dq)) /
          ((Real.exp (d.q + d.dq) - 1) * (Real.exp d.q - 1)) := by
      field_simp
      ring
    rw [hdiff, abs_div, abs_of_pos (mul_pos hden1pos hden0pos)]
    have hnum : |Real.exp d.q - Real.exp (d.q + d.dq)| ≤ 2 * |d.dq| * Real.exp d.q := by
      rw [Real.exp_add, show Real.exp d.q - Real.exp d.q * Real.exp d.dq =
        -(Real.exp d.q * (Real.exp d.dq - 1)) by ring, abs_neg, abs_mul, abs_of_pos he0]
      have := Real.abs_exp_sub_one_le hdq
      calc Real.exp d.q * |Real.exp d.dq - 1| ≤ Real.exp d.q * (2 * |d.dq|) :=
            mul_le_mul_of_nonneg_left this he0.le
        _ = 2 * |d.dq| * Real.exp d.q := by ring
    rw [div_le_iff₀ (mul_pos hden1pos hden0pos)]
    have hprod : Real.exp d.q / 6 * (Real.exp d.q / 2) ≤
        (Real.exp (d.q + d.dq) - 1) * (Real.exp d.q - 1) :=
      mul_le_mul hden1 hden0 (by positivity) hden1pos.le
    rw [hexpneg]
    have hdq0 := abs_nonneg d.dq
    calc |Real.exp d.q - Real.exp (d.q + d.dq)| ≤ 2 * |d.dq| * Real.exp d.q := hnum
      _ = 24 * |d.dq| * (1 / Real.exp d.q) * (Real.exp d.q / 6 * (Real.exp d.q / 2)) := by
          field_simp; ring
      _ ≤ 24 * |d.dq| * (1 / Real.exp d.q) * ((Real.exp (d.q + d.dq) - 1) * (Real.exp d.q - 1)) := by
          gcongr

/-- The Bose coefficient at `l = 0` and its difference. -/
theorem boseCoefficient_bounds (d : C5LikelihoodAffineData) {a' da' dq' : ℝ} (ht : 0 ≤ d.t)
    (hq : 2 ≤ d.q) (hdq : |d.dq| ≤ 1) (hdq' : |d.dq| ≤ dq') (ha : |d.a| ≤ a') (hda : |d.da| ≤ da') :
    |d.boseCoefficient 0| ≤ boseZeroBound d.t a' d.q ∧
    |d.boseCoefficient 1 - d.boseCoefficient 0| ≤ boseDiffBound d.t a' da' dq' d.q := by
  obtain ⟨hρ00, hρ0, hρ10, hρ1, hΔρ⟩ := d.boseReciprocal_bounds hq hdq
  have hj0 : d.jetOne 0 = d.a := by simp [jetOne, affine]
  have hj1 : d.jetOne 1 = d.a + d.da := by simp [jetOne, affine]
  have ha0 := le_trans (abs_nonneg _) ha
  have hda0 := le_trans (abs_nonneg _) hda
  have hE := (Real.exp_pos (-d.q)).le
  have hta : |d.t * d.a| ≤ d.t * a' := by
    rw [abs_mul, abs_of_nonneg ht]; exact mul_le_mul_of_nonneg_left ha ht
  have htda : |d.t * d.da| ≤ d.t * da' := by
    rw [abs_mul, abs_of_nonneg ht]; exact mul_le_mul_of_nonneg_left hda ht
  have hρ0' : |d.boseReciprocal 0| ≤ 2 * Real.exp (-d.q) := by rw [abs_of_nonneg hρ00]; exact hρ0
  have hρ1' : |d.boseReciprocal 1| ≤ 6 * Real.exp (-d.q) := by rw [abs_of_nonneg hρ10]; exact hρ1
  constructor
  · unfold boseCoefficient boseZeroBound
    rw [hj0]
    have h1 := abs_mul_le_of_abs_le hta hρ0'
    have e0 := abs_le.mp hta
    have e1 := abs_le.mp h1
    rw [abs_le]
    constructor <;> nlinarith [e0.1, e0.2, e1.1, e1.2, hE, ha0, ht]
  · unfold boseCoefficient boseDiffBound
    rw [hj0, hj1]
    have hsplit : 14 + 10 * (d.t * (d.a + d.da)) + 8 * (d.t * (d.a + d.da)) * d.boseReciprocal 1 -
        (14 + 10 * (d.t * d.a) + 8 * (d.t * d.a) * d.boseReciprocal 0) =
        10 * (d.t * d.da) + 8 * ((d.t * d.da) * d.boseReciprocal 1) +
          8 * ((d.t * d.a) * (d.boseReciprocal 1 - d.boseReciprocal 0)) := by ring
    rw [hsplit]
    have h1 := abs_mul_le_of_abs_le htda hρ1'
    have hΔρ' : |d.boseReciprocal 1 - d.boseReciprocal 0| ≤ 24 * dq' * Real.exp (-d.q) := by
      refine hΔρ.trans ?_
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdq' (by norm_num : (0:ℝ) ≤ 24)) hE
      linarith
    have h2 := abs_mul_le_of_abs_le hta hΔρ'
    have e0 := abs_le.mp htda
    have e1 := abs_le.mp h1
    have e2 := abs_le.mp h2
    rw [abs_le]
    constructor <;> nlinarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2]

/-- **Generic perturbation bound for the compensation margin.** -/
theorem abs_compensation_diff_le (d : C5LikelihoodAffineData)
    {a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' : ℝ}
    (ht : 0 ≤ d.t) (hq : 2 ≤ d.q) (hdq : |d.dq| ≤ 1) (hdq' : |d.dq| ≤ dq')
    (ha : |d.a| ≤ a') (hb : |d.b| ≤ b') (hc : |d.c| ≤ c') (hs : |d.s| ≤ s') (hm : |d.m| ≤ m')
    (hn : |d.n| ≤ n') (hda : |d.da| ≤ da') (hdb : |d.db| ≤ db') (hdc : |d.dc| ≤ dc')
    (hds : |d.ds| ≤ ds') (hdm : |d.dm| ≤ dm') (hdn : |d.dn| ≤ dn') :
    |d.compensation 1 - d.compensation 0| ≤
      compensationDiffBound d.t a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' d.q := by
  rw [compensation_one_sub_zero]
  unfold compensationDiffBound
  have hS := d.abs_velocitySlope_diff_le ht ha hb hc hs hm hn hda hdb hdc hds hdm hdn
  have hC := d.abs_velocityCenter_diff_le ht ha hb hs hm hda hdb hds hdm
  have hC0 := d.abs_velocityCenter_zero_le ht ha hb hs hm
  obtain ⟨hW0, hΔW⟩ := d.boseCoefficient_bounds ht hq hdq hdq' ha hda
  have hC1 : |d.velocityCenter 1| ≤ centerZeroBound d.t a' b' s' m' +
      centerDiffBound d.t a' b' s' m' da' db' ds' dm' := by
    calc |d.velocityCenter 1| = |d.velocityCenter 0 + (d.velocityCenter 1 - d.velocityCenter 0)| := by
          ring_nf
      _ ≤ |d.velocityCenter 0| + |d.velocityCenter 1 - d.velocityCenter 0| := abs_add_le _ _
      _ ≤ _ := add_le_add hC0 hC
  have t1 : |5 * (d.velocitySlope 1 - d.velocitySlope 0)| ≤
      5 * slopeDiffBound d.t a' b' c' s' m' n' da' db' dc' ds' dm' dn' := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5)]
    exact mul_le_mul_of_nonneg_left hS (by norm_num)
  have t2 := abs_mul_le_of_abs_le hΔW hC1
  have t3 := abs_mul_le_of_abs_le hW0 hC
  calc |5 * (d.velocitySlope 1 - d.velocitySlope 0) -
        (d.boseCoefficient 1 - d.boseCoefficient 0) * d.velocityCenter 1 -
        d.boseCoefficient 0 * (d.velocityCenter 1 - d.velocityCenter 0)|
      ≤ |5 * (d.velocitySlope 1 - d.velocitySlope 0) -
          (d.boseCoefficient 1 - d.boseCoefficient 0) * d.velocityCenter 1| +
        |d.boseCoefficient 0 * (d.velocityCenter 1 - d.velocityCenter 0)| := abs_sub _ _
    _ ≤ (|5 * (d.velocitySlope 1 - d.velocitySlope 0)| +
          |(d.boseCoefficient 1 - d.boseCoefficient 0) * d.velocityCenter 1|) +
        |d.boseCoefficient 0 * (d.velocityCenter 1 - d.velocityCenter 0)| := by
          gcongr; exact abs_sub _ _
    _ ≤ _ := add_le_add (add_le_add t1 t2) t3

end C5LikelihoodAffineData

/-! ## §5 Quantitative single-atom margin -/

/-- `M(0) ≥ 2A (4A − 36/A) · (series lower bound of the shape)` for `A(u) ≥ 6`, `0 < t ≤ u`. -/
theorem c5SingleAtomCompensationMargin_ge {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    2 * thetaCuspSingleAtomReflectionScale 1 u *
        (4 * thetaCuspSingleAtomReflectionScale 1 u - 36 / thetaCuspSingleAtomReflectionScale 1 u) *
      (6656 / 9 * t ^ 7 + 615872 / 945 * t ^ 9 + 50560 / 189 * t ^ 11) ≤
    c5SingleAtomCompensationMargin (thetaCuspSingleAtomReflectionScale 1 u) t := by
  set A := thetaCuspSingleAtomReflectionScale 1 u with hAdef
  set z := thetaCuspSingleAtomReflectionDefect t with hzdef
  have hz : 0 ≤ z := by
    show 0 ≤ Real.cosh (2 * t) - 1
    linarith [Real.one_le_cosh (2 * t)]
  have hr : 1 / 2 < thetaCuspSingleAtomReflectionFactor A z := by
    simpa only [A, z] using one_half_lt_thetaCuspSingleAtomReflectionFactor_of_sameHalfLine ht.le htu
  obtain ⟨-, -, -, -, -, -, hslope, hL⟩ := singleAtom_jet_bounds (z' := 0) hscale hz le_rfl hr
  have hA3 : (3 : ℝ) < A := by linarith
  have hr0 : 0 < thetaCuspSingleAtomReflectionFactor A z := by linarith
  have hH : c5SingleAtomVelocityCenterNumerator A t < 0 :=
    c5SingleAtomVelocityCenterNumerator_neg_of_sameHalfLine ht htu hscale
  have hfull := c5SingleAtomBaseCompensationMargin_lt_full hA3 ht hr0 hH
  have hp : 0 < 2 * A + thetaCuspSingleAtomReflectionLambda A /
      thetaCuspSingleAtomReflectionFactor A z := by
    have := hslope
    unfold thetaCuspSingleAtomReflectionSlope at this
    linarith
  have hLpos : 0 < 4 * A + c5SingleAtomScaleLambdaJetOne A / thetaCuspSingleAtomReflectionFactor A z := by
    have h36 : 36 / A ≤ 6 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hfac := c5SingleAtomBaseCompensationMargin_eq_gaussian_add_correction
    (show 3 / 2 < A by linarith) hr0.ne' hp.ne' hLpos.ne'
  have hcorr := c5SingleAtomBaseRationalCorrection_pos_of_sameHalfLine ht htu hscale
  have hshape := c5HyperbolicGaussianBaseShape_ge ht.le
  have hshape0 : 0 ≤ 6656 / 9 * t ^ 7 + 615872 / 945 * t ^ 9 + 50560 / 189 * t ^ 11 := by positivity
  have hpL : 2 * A * (4 * A - 36 / A) ≤
      (2 * A + thetaCuspSingleAtomReflectionLambda A / thetaCuspSingleAtomReflectionFactor A z) *
        (4 * A + c5SingleAtomScaleLambdaJetOne A / thetaCuspSingleAtomReflectionFactor A z) := by
    have h2A : 2 * A ≤ 2 * A + thetaCuspSingleAtomReflectionLambda A /
        thetaCuspSingleAtomReflectionFactor A z := by
      have := hslope; unfold thetaCuspSingleAtomReflectionSlope at this; exact this
    have h36 : 0 ≤ 4 * A - 36 / A := by
      have : 36 / A ≤ 6 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    exact mul_le_mul h2A hL h36 hp.le
  calc 2 * A * (4 * A - 36 / A) * (6656 / 9 * t ^ 7 + 615872 / 945 * t ^ 9 + 50560 / 189 * t ^ 11)
      ≤ (2 * A + thetaCuspSingleAtomReflectionLambda A / thetaCuspSingleAtomReflectionFactor A z) *
          (4 * A + c5SingleAtomScaleLambdaJetOne A / thetaCuspSingleAtomReflectionFactor A z) *
          c5HyperbolicGaussianBaseShape t :=
        mul_le_mul hpL hshape hshape0 (by positivity)
    _ ≤ c5SingleAtomBaseCompensationMargin A t := by
        rw [hfac]; linarith
    _ ≤ c5SingleAtomCompensationMargin A t := hfull.le

/-! ## §6 Assembly: regime I for `t ≥ 1/4` -/

theorem one_add_sq_div_two_le_cosh' (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := Real.hasSum_cosh x
  have hle := sum_le_hasSum (Finset.range 2)
    (fun n _ => div_nonneg ((even_two_mul n).pow_nonneg x) (by positivity)) h
  simp [Finset.sum_range_succ, Nat.factorial] at hle
  linarith

/-- The homotopy data fields. -/
theorem thetaCuspC5LikelihoodHomotopyData_fields (u t : ℝ) :
    let d := thetaCuspC5LikelihoodHomotopyData u t
    let A := thetaCuspSingleAtomReflectionScale 1 u
    let z := thetaCuspSingleAtomReflectionDefect t
    let z' := 2 * Real.sinh (2 * t)
    d.t = t ∧ d.q = thetaCuspSingleAtomReflectedAction A t ∧
    d.dq = thetaCuspReflectedLikelihoodCumulantAction u t ∧
    d.a = thetaCuspSingleAtomReflectedActionJetOne A z z' ∧
    d.da = thetaCuspReflectedLikelihoodCumulantJetOne u t ∧
    d.b = thetaCuspSingleAtomReflectedActionJetTwo A z ∧
    d.db = thetaCuspReflectedLikelihoodCumulantJetTwo u t ∧
    d.c = thetaCuspSingleAtomReflectedActionJetThree A z z' ∧
    d.dc = thetaCuspReflectedLikelihoodCumulantJetThree u t ∧
    d.s = c5SingleAtomScaleActionJetOne A z ∧
    d.ds = c5LikelihoodScaleActionJetOne u t ∧
    d.m = c5SingleAtomScaleMixedJetOne A z z' ∧
    d.dm = c5LikelihoodScaleMixedJetOne u t ∧
    d.n = c5SingleAtomScaleMixedJetTwo A z ∧
    d.dn = c5LikelihoodScaleMixedJetTwo u t := by
  intro d A z z'
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Regime-I gate from the key inequality.**  For `1/4 ≤ t ≤ u` and `A(u−t) ≥ 6`, if the
explicit perturbation bound is below the single-atom lower bound, the completed margin is
positive. -/
theorem c5CompletedCompensationMargin_pos_of_regimeOne_key {u t : ℝ}
    (ht : 1 / 4 ≤ t) (htu : t ≤ u)
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t))
    (hkey :
      let A := thetaCuspSingleAtomReflectionScale 1 u
      let Am := thetaCuspSingleAtomReflectionScale 1 (u - t)
      let ε := regimeOneLikelihoodScale (u - t)
      let z := thetaCuspSingleAtomReflectionDefect t
      let z' := 2 * Real.sinh (2 * t)
      C5LikelihoodAffineData.compensationDiffBound t
        ((2 * A + 12 / A) * z')
        (4 * (12 / A) ^ 2 * z * (z + 2) + 4 * (2 * A + 12 / A) * (z + 1))
        (z' * (8 * (12 / A) ^ 3 * z * (z + 2) + 12 * (12 / A) ^ 2 * (z + 1) + 4 * (2 * A + 12 / A)))
        (4 * A * z + 36 / A * z) ((4 * A + 72 / A) * z')
        (4 * (1728 / A ^ 2 * z * (z + 2) + (4 * A + 72 / A) * (z + 1)))
        (12 * Am * ε) (76 * Am ^ 2 * ε) (522 * Am ^ 3 * ε) (24 * Am * ε) (76 * Am ^ 2 * ε)
        (522 * Am ^ 3 * ε) (4 * ε) (thetaCuspSingleAtomReflectedAction A t) <
      2 * A * (4 * A - 36 / A) *
        (6656 / 9 * t ^ 7 + 615872 / 945 * t ^ 9 + 50560 / 189 * t ^ 11)) :
    0 < c5CompletedCompensationMargin u t := by
  have ht0 : 0 < t := by linarith
  have hu : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u := by
    refine le_trans hA ?_
    unfold thetaCuspSingleAtomReflectionScale
    have := Real.exp_le_exp.mpr (show 2 * (u - t) ≤ 2 * u by linarith)
    simp only [Nat.cast_one, one_pow, mul_one]
    exact mul_le_mul_of_nonneg_left this Real.pi_pos.le
  -- the homotopy data and its fields
  set d := thetaCuspC5LikelihoodHomotopyData u t with hddef
  obtain ⟨hdt, hdq, hddq, hda, hdda, hdb, hddb, hdc, hddc, hds, hdds, hdm, hddm, hdn, hddn⟩ :=
    thetaCuspC5LikelihoodHomotopyData_fields u t
  set A := thetaCuspSingleAtomReflectionScale 1 u with hAdef
  set Am := thetaCuspSingleAtomReflectionScale 1 (u - t) with hAmdef
  set ε := regimeOneLikelihoodScale (u - t) with hεdef
  set z := thetaCuspSingleAtomReflectionDefect t with hzdef
  set z' := 2 * Real.sinh (2 * t) with hz'def
  have hz0 : 0 ≤ z := by
    show 0 ≤ Real.cosh (2 * t) - 1
    linarith [Real.one_le_cosh (2 * t)]
  have hz'0 : 0 ≤ z' := by
    show 0 ≤ 2 * Real.sinh (2 * t)
    have := Real.sinh_nonneg_iff.mpr (by linarith : (0:ℝ) ≤ 2 * t)
    linarith
  have hr : 1 / 2 < thetaCuspSingleAtomReflectionFactor A z := by
    simpa only [A, z] using one_half_lt_thetaCuspSingleAtomReflectionFactor_of_sameHalfLine ht0.le htu
  obtain ⟨ha, hb, hc, hs, hm, hn, -, -⟩ := singleAtom_jet_bounds hu hz0 hz'0 hr
  obtain ⟨hda', hdb', hdc', hds', hdm', hdn', hdq'⟩ := regimeOne_homotopy_correction_bounds ht0.le hA
  -- `q ≥ 2`
  have hq2 : 2 ≤ thetaCuspSingleAtomReflectedAction A t := by
    unfold thetaCuspSingleAtomReflectedAction
    rw [← hzdef]
    have hr1 : thetaCuspSingleAtomReflectionFactor A z ≤ 1 := by
      unfold thetaCuspSingleAtomReflectionFactor
      have := mul_nonneg (thetaCuspSingleAtomReflectionLambda_pos (show (3:ℝ) < A by linarith)).le hz0
      linarith
    have hlog : Real.log (thetaCuspSingleAtomReflectionFactor A z) ≤ 0 :=
      Real.log_nonpos (by linarith) hr1
    have hzt : 2 * t ^ 2 ≤ z := by
      have := one_add_sq_div_two_le_cosh' (2 * t)
      show 2 * t ^ 2 ≤ Real.cosh (2 * t) - 1
      linarith only [this]
    have hAe : 6 * Real.exp (2 * t) ≤ A := by
      have : A = Am * Real.exp (2 * t) := by
        simp only [A, Am, thetaCuspSingleAtomReflectionScale]
        rw [show (2 : ℝ) * u = 2 * (u - t) + 2 * t by ring, Real.exp_add]
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    have hexp : (1 : ℝ) < Real.exp (2 * t) := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
    have hAz : 1 ≤ A * z := by
      have h1 : 9 ≤ A := by
        have := Real.add_one_le_exp (2 * t)
        linarith only [hAe, this, ht]
      have ht2 : (1 / 4 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num) ht 2
      have h2 : 1 / 8 ≤ z := by linarith only [hzt, ht2]
      have := mul_le_mul h1 h2 (by norm_num) (by linarith)
      linarith only [this]
    linarith only [hlog, hAz]
  have hdq1 : |d.dq| ≤ 1 := by
    rw [hddq]
    have hε := regimeOneLikelihoodScale_le_of_six_le hA
    linarith [hdq']
  -- compare `M(1)` with `M(0)`
  have hdiff := d.abs_compensation_diff_le (a' := (2 * A + 12 / A) * z')
    (b' := 4 * (12 / A) ^ 2 * z * (z + 2) + 4 * (2 * A + 12 / A) * (z + 1))
    (c' := z' * (8 * (12 / A) ^ 3 * z * (z + 2) + 12 * (12 / A) ^ 2 * (z + 1) + 4 * (2 * A + 12 / A)))
    (s' := 4 * A * z + 36 / A * z) (m' := (4 * A + 72 / A) * z')
    (n' := 4 * (1728 / A ^ 2 * z * (z + 2) + (4 * A + 72 / A) * (z + 1)))
    (da' := 12 * Am * ε) (db' := 76 * Am ^ 2 * ε) (dc' := 522 * Am ^ 3 * ε) (ds' := 24 * Am * ε)
    (dm' := 76 * Am ^ 2 * ε) (dn' := 522 * Am ^ 3 * ε) (dq' := 4 * ε)
    (by rw [hdt]; exact ht0.le) (by rw [hdq]; exact hq2) hdq1 (by rw [hddq]; exact hdq')
    (by rw [hda]; exact ha) (by rw [hdb]; exact hb) (by rw [hdc]; exact hc) (by rw [hds]; exact hs)
    (by rw [hdm]; exact hm) (by rw [hdn]; exact hn) (by rw [hdda]; exact hda')
    (by rw [hddb]; exact hdb') (by rw [hddc]; exact hdc') (by rw [hdds]; exact hds')
    (by rw [hddm]; exact hdm') (by rw [hddn]; exact hdn')
  rw [hdt, hdq] at hdiff
  have hM0 := c5SingleAtomCompensationMargin_ge ht0 htu hu
  have h1 : d.compensation 1 = c5CompletedCompensationMargin u t :=
    thetaCuspC5LikelihoodHomotopyCompensation_one u t
  have h0 : d.compensation 0 = c5SingleAtomCompensationMargin A t :=
    thetaCuspC5LikelihoodHomotopyCompensation_zero u t
  rw [h1, h0] at hdiff
  have hlow := (abs_le.mp hdiff).1
  simp only at hkey
  generalize hBd : C5LikelihoodAffineData.compensationDiffBound t ((2 * A + 12 / A) * z')
    (4 * (12 / A) ^ 2 * z * (z + 2) + 4 * (2 * A + 12 / A) * (z + 1))
    (z' * (8 * (12 / A) ^ 3 * z * (z + 2) + 12 * (12 / A) ^ 2 * (z + 1) + 4 * (2 * A + 12 / A)))
    (4 * A * z + 36 / A * z) ((4 * A + 72 / A) * z')
    (4 * (1728 / A ^ 2 * z * (z + 2) + (4 * A + 72 / A) * (z + 1)))
    (12 * Am * ε) (76 * Am ^ 2 * ε) (522 * Am ^ 3 * ε) (24 * Am * ε) (76 * Am ^ 2 * ε)
    (522 * Am ^ 3 * ε) (4 * ε) (thetaCuspSingleAtomReflectedAction A t) = Bd at hlow hkey
  generalize hMl : 2 * A * (4 * A - 36 / A) *
    (6656 / 9 * t ^ 7 + 615872 / 945 * t ^ 9 + 50560 / 189 * t ^ 11) = Ml at hM0 hkey
  generalize hM1 : c5CompletedCompensationMargin u t = M1 at hlow ⊢
  generalize hM0' : c5SingleAtomCompensationMargin A t = M0 at hlow hM0
  linarith only [hlow, hkey, hM0]

end RHTower
