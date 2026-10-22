import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5SharpTailJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5FrozenJetGateSharp
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5RegimeOneKey

/-!
# Window bounds for the frozen-jet gate in regime I

Uniform error constants for the sharp jets (`A ≥ 6`), the decomposition
`c⁽⁴⁾ = BW₆ − J₆`, `c⁽⁵⁾ = BW₇ − J₇`, explicit majorants of `sup |c⁽⁴⁾|`, `sup |c⁽⁵⁾|` on a window,
two-sided chamber bounds for `c, c', c'', c'''` at the centre, and the reduction of the sharp key
inequality to its value at the right end of a `t`-chamber.
-/

namespace RHTower

open Set

/-! ## Uniform error constants -/

theorem exp_twentyTwo_gt : (3500000000 : ℝ) < Real.exp 22 := by
  have h1 := exp_twentyOne_gt
  have h2 := Real.exp_one_gt_d9
  have : Real.exp 22 = Real.exp 21 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith

/-- `A^k e^{-8(A-π)} ≤ 6^k / 3.5·10⁹` for `A ≥ 6`, `k ≤ 7`. -/
theorem pow_mul_exp_neg_eight_gap_le {A : ℝ} (hA : 6 ≤ A) (k : ℕ) (hk : k ≤ 7) :
    A ^ k * Real.exp (-(8 * (A - Real.pi))) ≤ 6 ^ k * (1 / 3500000000) := by
  have hk' : (k : ℝ) ≤ 7 := by exact_mod_cast hk
  have h1 := pow_mul_exp_neg_le_of_le (m := k) (δ := 8) (a := 6) (t := A) (by norm_num)
    (by rw [div_le_iff₀ (by norm_num)]; linarith) hA
  have hsplit : Real.exp (-(8 * (A - Real.pi))) = Real.exp (8 * Real.pi) * Real.exp (-(8 * A)) := by
    rw [← Real.exp_add]; ring_nf
  have hpi := Real.pi_lt_d2
  have h22 : Real.exp (8 * Real.pi) * Real.exp (-(8 * 6)) ≤ 1 / 3500000000 := by
    rw [← Real.exp_add]
    have : 8 * Real.pi + -(8 * 6) ≤ -22 := by norm_num at hpi ⊢; linarith
    have h3 := Real.exp_le_exp.mpr this
    have h4 : Real.exp (-22) = 1 / Real.exp 22 := by rw [Real.exp_neg]; ring
    rw [h4] at h3
    have h5 := exp_twentyTwo_gt
    calc Real.exp (8 * Real.pi + -(8 * 6)) ≤ 1 / Real.exp 22 := h3
      _ ≤ 1 / 3500000000 := one_div_le_one_div_of_le (by norm_num) h5.le
  rw [hsplit]
  have hE := Real.exp_pos (8 * Real.pi)
  calc A ^ k * (Real.exp (8 * Real.pi) * Real.exp (-(8 * A)))
      = Real.exp (8 * Real.pi) * (A ^ k * Real.exp (-(8 * A))) := by ring
    _ ≤ Real.exp (8 * Real.pi) * (6 ^ k * Real.exp (-(8 * 6))) :=
        mul_le_mul_of_nonneg_left h1 hE.le
    _ = 6 ^ k * (Real.exp (8 * Real.pi) * Real.exp (-(8 * 6))) := by ring
    _ ≤ 6 ^ k * (1 / 3500000000) := mul_le_mul_of_nonneg_left h22 (by positivity)

/-- Uniform bounds for the sharp jet errors: `|J_k − h_k(A)| ≤ ê_k` for `A ≥ 6`. -/
theorem sharpJet_uniform_bounds {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodSourceLogPartitionJetTwo x -
        sharpJetMain2 (thetaCuspSingleAtomReflectionScale 1 x)| ≤ 1 / 100000000 ∧
    |thetaCuspLikelihoodSourceLogPartitionJetThree x -
        sharpJetMain3 (thetaCuspSingleAtomReflectionScale 1 x)| ≤ 1 / 1000000 ∧
    |thetaCuspLikelihoodSourceLogPartitionJetFour x -
        sharpJetMain4 (thetaCuspSingleAtomReflectionScale 1 x)| ≤ 1 / 10000 ∧
    |thetaCuspLikelihoodSourceLogPartitionJetFive x -
        sharpJetMain5 (thetaCuspSingleAtomReflectionScale 1 x)| ≤ 1 / 100 ∧
    |thetaCuspLikelihoodSourceLogPartitionJetSix x -
        sharpJetMain6 (thetaCuspSingleAtomReflectionScale 1 x)| ≤ 1 ∧
    |thetaCuspLikelihoodSourceLogPartitionJetSeven x -
        sharpJetMain7 (thetaCuspSingleAtomReflectionScale 1 x)| ≤ 100 := by
  have hε := regimeOneLikelihoodScale_le_of_six_le hA
  have hε0 := (regimeOneLikelihoodScale_pos x).le
  have hA0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hE0 : 0 ≤ Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399 := by
    positivity
  -- generic step
  have step : ∀ (k : ℕ), k ≤ 7 → ∀ (K L b : ℝ), 0 ≤ K → 0 ≤ L →
      K * 6 ^ k * (49 / 100000000) * (5 / 10000000) + L * 6 ^ k * (1 / 3500000000) / 399 ≤ b →
      K * thetaCuspSingleAtomReflectionScale 1 x ^ k * regimeOneLikelihoodScale x ^ (2 : ℕ) +
        L * thetaCuspSingleAtomReflectionScale 1 x ^ k *
          (Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399) ≤ b := by
    intro k hk K L b hK hL hb
    have h1 := regimeOne_scale_pow_le (k := k) (by exact_mod_cast (show k ≤ 18 by omega)) hA
    have h2 := pow_mul_exp_neg_eight_gap_le hA k hk
    have hp : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x ^ k * regimeOneLikelihoodScale x := by positivity
    have e1 : K * thetaCuspSingleAtomReflectionScale 1 x ^ k * regimeOneLikelihoodScale x ^ (2 : ℕ) =
        K * ((thetaCuspSingleAtomReflectionScale 1 x ^ k * regimeOneLikelihoodScale x) *
          regimeOneLikelihoodScale x) := by ring
    have e2 : L * thetaCuspSingleAtomReflectionScale 1 x ^ k *
        (Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399) =
        L * (thetaCuspSingleAtomReflectionScale 1 x ^ k *
          Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi)))) / 399 := by ring
    rw [e1, e2]
    have t1 : (thetaCuspSingleAtomReflectionScale 1 x ^ k * regimeOneLikelihoodScale x) *
        regimeOneLikelihoodScale x ≤ (6 ^ k * (49 / 100000000)) * (5 / 10000000) :=
      mul_le_mul h1 hε hε0 (by positivity)
    have t2 := mul_le_mul_of_nonneg_left t1 hK
    have t3 := mul_le_mul_of_nonneg_left h2 hL
    have t4 : L * (thetaCuspSingleAtomReflectionScale 1 x ^ k *
        Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi)))) / 399 ≤
        L * (6 ^ k * (1 / 3500000000)) / 399 := by
      apply div_le_div_of_nonneg_right t3 (by norm_num)
    calc _ ≤ K * ((6 ^ k * (49 / 100000000)) * (5 / 10000000)) + L * (6 ^ k * (1 / 3500000000)) / 399 := by
          linarith
      _ = K * 6 ^ k * (49 / 100000000) * (5 / 10000000) + L * 6 ^ k * (1 / 3500000000) / 399 := by ring
      _ ≤ b := hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (sharpJet_bound_2 hA).trans (step 2 (by norm_num) _ _ _ (by norm_num) (by norm_num) (by norm_num))
  · exact (sharpJet_bound_3 hA).trans (step 3 (by norm_num) _ _ _ (by norm_num) (by norm_num) (by norm_num))
  · exact (sharpJet_bound_4 hA).trans (step 4 (by norm_num) _ _ _ (by norm_num) (by norm_num) (by norm_num))
  · exact (sharpJet_bound_5 hA).trans (step 5 (by norm_num) _ _ _ (by norm_num) (by norm_num) (by norm_num))
  · exact (sharpJet_bound_6 hA).trans (step 6 (by norm_num) _ _ _ (by norm_num) (by norm_num) (by norm_num))
  · exact (sharpJet_bound_7 hA).trans (step 7 (by norm_num) _ _ _ (by norm_num) (by norm_num) (by norm_num))

/-! ## The sixth and seventh curvature jets -/

theorem thetaCuspLogCurvatureJetFour_eq_bornWitten_sub_jet {x : ℝ} (hx : 0 < x) :
    thetaCuspLogCurvatureJetFour x =
      thetaCuspBornWittenLogSixthDerivative 1 x - thetaCuspLikelihoodSourceLogPartitionJetSix x := by
  unfold thetaCuspLogCurvatureJetFour
  rw [iteratedDeriv_six_thetaCuspLogSource_eq_full_jets hx]
  unfold thetaCuspFullLogJetSix
  ring

theorem thetaCuspLogCurvatureJetFive_eq_bornWitten_sub_jet {x : ℝ} (hx : 0 < x) :
    thetaCuspLogCurvatureJetFive x =
      thetaCuspBornWittenLogSeventhDerivative 1 x - thetaCuspLikelihoodSourceLogPartitionJetSeven x := by
  unfold thetaCuspLogCurvatureJetFive
  rw [iteratedDeriv_seven_thetaCuspLogSource_eq_full_jets hx]
  unfold thetaCuspFullLogJetSeven
  ring

/-! ## Born–Witten majorants on a `q`-interval -/

/-- Majorant of `|BW₆|` for `q ∈ [qlo, qhi]`. -/
noncomputable def bwSixAbs (qlo qhi : ℝ) : ℝ :=
  (2 * qhi + 3) * (32 + 48 / qlo ^ (2 : ℕ) + 2160 / qlo ^ (3 : ℕ) + 16200 / qlo ^ (4 : ℕ) + 38880 / qlo ^ (5 : ℕ) +
    29160 / qlo ^ (6 : ℕ))

/-- Majorant of `|BW₇|` for `q ∈ [qlo, qhi]`. -/
noncomputable def bwSevenAbs (qlo qhi : ℝ) : ℝ :=
  (2 * qhi + 3) * (64 + 96 / qlo ^ (2 : ℕ) + 8928 / qlo ^ (3 : ℕ) + 116640 / qlo ^ (4 : ℕ) + 505440 / qlo ^ (5 : ℕ) +
    874800 / qlo ^ (6 : ℕ) + 524880 / qlo ^ (7 : ℕ))

theorem inv_pow_le_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ) : 1 / b ^ k ≤ 1 / a ^ k :=
  one_div_le_one_div_of_le (pow_pos ha k) (pow_le_pow_left₀ ha.le hab k)

theorem abs_bornWittenSix_le {q qlo qhi : ℝ} (hlo : 0 < qlo) (h1 : qlo ≤ q) (h2 : q ≤ qhi) :
    |(2 * q + 3) * (32 + 48 / q ^ (2 : ℕ) + 2160 / q ^ (3 : ℕ) + 16200 / q ^ (4 : ℕ) + 38880 / q ^ (5 : ℕ) +
      29160 / q ^ (6 : ℕ))| ≤ bwSixAbs qlo qhi := by
  have hq : 0 < q := by linarith
  have j2 : 48 / q ^ (2 : ℕ) ≤ 48 / qlo ^ (2 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hlo 2) (pow_le_pow_left₀ hlo.le h1 2)
  have j3 : 2160 / q ^ (3 : ℕ) ≤ 2160 / qlo ^ (3 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hlo 3) (pow_le_pow_left₀ hlo.le h1 3)
  have j4 : 16200 / q ^ (4 : ℕ) ≤ 16200 / qlo ^ (4 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hlo 4) (pow_le_pow_left₀ hlo.le h1 4)
  have j5 : 38880 / q ^ (5 : ℕ) ≤ 38880 / qlo ^ (5 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hlo 5) (pow_le_pow_left₀ hlo.le h1 5)
  have j6 : 29160 / q ^ (6 : ℕ) ≤ 29160 / qlo ^ (6 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hlo 6) (pow_le_pow_left₀ hlo.le h1 6)
  have hg : 32 + 48 / q ^ (2 : ℕ) + 2160 / q ^ (3 : ℕ) + 16200 / q ^ (4 : ℕ) + 38880 / q ^ (5 : ℕ) + 29160 / q ^ (6 : ℕ) ≤
      32 + 48 / qlo ^ (2 : ℕ) + 2160 / qlo ^ (3 : ℕ) + 16200 / qlo ^ (4 : ℕ) + 38880 / qlo ^ (5 : ℕ) + 29160 / qlo ^ (6 : ℕ) := by
    linarith
  have hg0 : 0 ≤ 32 + 48 / q ^ (2 : ℕ) + 2160 / q ^ (3 : ℕ) + 16200 / q ^ (4 : ℕ) + 38880 / q ^ (5 : ℕ) + 29160 / q ^ (6 : ℕ) := by
    positivity
  rw [abs_of_nonneg (mul_nonneg (by linarith) hg0)]
  unfold bwSixAbs
  exact mul_le_mul (by linarith) hg hg0 (by linarith)

theorem abs_bornWittenSeven_le {q qlo qhi : ℝ} (hlo : 0 < qlo) (h1 : qlo ≤ q) (h2 : q ≤ qhi) :
    |(2 * q + 3) * (64 - 96 / q ^ (2 : ℕ) - 8928 / q ^ (3 : ℕ) - 116640 / q ^ (4 : ℕ) - 505440 / q ^ (5 : ℕ) -
      874800 / q ^ (6 : ℕ) - 524880 / q ^ (7 : ℕ))| ≤ bwSevenAbs qlo qhi := by
  have hq : 0 < q := by linarith
  have j2 : 96 / q ^ (2 : ℕ) ≤ 96 / qlo ^ (2 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hlo 2) (pow_le_pow_left₀ hlo.le h1 2)
  have j3 : 8928 / q ^ (3 : ℕ) ≤ 8928 / qlo ^ (3 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hlo 3) (pow_le_pow_left₀ hlo.le h1 3)
  have j4 : 116640 / q ^ (4 : ℕ) ≤ 116640 / qlo ^ (4 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hlo 4) (pow_le_pow_left₀ hlo.le h1 4)
  have j5 : 505440 / q ^ (5 : ℕ) ≤ 505440 / qlo ^ (5 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hlo 5) (pow_le_pow_left₀ hlo.le h1 5)
  have j6 : 874800 / q ^ (6 : ℕ) ≤ 874800 / qlo ^ (6 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hlo 6) (pow_le_pow_left₀ hlo.le h1 6)
  have j7 : 524880 / q ^ (7 : ℕ) ≤ 524880 / qlo ^ (7 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hlo 7) (pow_le_pow_left₀ hlo.le h1 7)
  have p2 : 0 ≤ 96 / q ^ (2 : ℕ) := by positivity
  have p3 : 0 ≤ 8928 / q ^ (3 : ℕ) := by positivity
  have p4 : 0 ≤ 116640 / q ^ (4 : ℕ) := by positivity
  have p5 : 0 ≤ 505440 / q ^ (5 : ℕ) := by positivity
  have p6 : 0 ≤ 874800 / q ^ (6 : ℕ) := by positivity
  have p7 : 0 ≤ 524880 / q ^ (7 : ℕ) := by positivity
  have hg : |64 - 96 / q ^ (2 : ℕ) - 8928 / q ^ (3 : ℕ) - 116640 / q ^ (4 : ℕ) - 505440 / q ^ (5 : ℕ) - 874800 / q ^ (6 : ℕ) -
      524880 / q ^ (7 : ℕ)| ≤ 64 + 96 / qlo ^ (2 : ℕ) + 8928 / qlo ^ (3 : ℕ) + 116640 / qlo ^ (4 : ℕ) + 505440 / qlo ^ (5 : ℕ) +
      874800 / qlo ^ (6 : ℕ) + 524880 / qlo ^ (7 : ℕ) := by
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * q + 3)]
  unfold bwSevenAbs
  exact mul_le_mul (by linarith) hg (abs_nonneg _) (by linarith)

/-! ## Window majorants for `c⁽⁴⁾` and `c⁽⁵⁾` -/

theorem thetaCuspSingleAtomReflectionScale_mono {x y : ℝ} (h : x ≤ y) :
    thetaCuspSingleAtomReflectionScale 1 x ≤ thetaCuspSingleAtomReflectionScale 1 y := by
  unfold thetaCuspSingleAtomReflectionScale
  have := Real.exp_le_exp.mpr (show 2 * x ≤ 2 * y by linarith)
  simp only [Nat.cast_one, one_pow, mul_one]
  exact mul_le_mul_of_nonneg_left this Real.pi_pos.le

/-- `sup |c⁽⁴⁾|` on the window. -/
theorem abs_jetFour_le_window {u t : ℝ}
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    ∀ x ∈ Icc (u - t) (u + t), |thetaCuspLogCurvatureJetFour x| ≤
      bwSixAbs (thetaCuspSingleAtomReflectionScale 1 (u - t) - 3 / 2)
          (thetaCuspSingleAtomReflectionScale 1 (u + t) - 3 / 2) +
        |sharpJetMain6 (thetaCuspSingleAtomReflectionScale 1 (u - t))| + 1 := by
  intro x hx
  have hAx : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x :=
    hA.trans (thetaCuspSingleAtomReflectionScale_mono hx.1)
  obtain ⟨hq, hq45, hx0, -, -, -, -, -⟩ := regimeOne_data hAx
  rw [thetaCuspLogCurvatureJetFour_eq_bornWitten_sub_jet hx0]
  have hJ := (sharpJet_uniform_bounds hAx).2.2.2.2.1
  have hmono := sharpJetMain6_abs_le_of_le hA (thetaCuspSingleAtomReflectionScale_mono hx.1)
  have hbw : |thetaCuspBornWittenLogSixthDerivative 1 x| ≤
      bwSixAbs (thetaCuspSingleAtomReflectionScale 1 (u - t) - 3 / 2)
        (thetaCuspSingleAtomReflectionScale 1 (u + t) - 3 / 2) := by
    simp only [thetaCuspBornWittenLogSixthDerivative]
    rw [hq]
    apply abs_bornWittenSix_le (by linarith)
    · linarith [thetaCuspSingleAtomReflectionScale_mono hx.1]
    · linarith [thetaCuspSingleAtomReflectionScale_mono hx.2]
  have h1 := abs_sub (thetaCuspBornWittenLogSixthDerivative 1 x)
    (thetaCuspLikelihoodSourceLogPartitionJetSix x)
  have h2 := abs_sub_abs_le_abs_sub (thetaCuspLikelihoodSourceLogPartitionJetSix x)
    (sharpJetMain6 (thetaCuspSingleAtomReflectionScale 1 x))
  linarith

/-- `sup |c⁽⁵⁾|` on the window. -/
theorem abs_jetFive_le_window {u t : ℝ}
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    ∀ x ∈ Icc (u - t) (u + t), |thetaCuspLogCurvatureJetFive x| ≤
      bwSevenAbs (thetaCuspSingleAtomReflectionScale 1 (u - t) - 3 / 2)
          (thetaCuspSingleAtomReflectionScale 1 (u + t) - 3 / 2) +
        |sharpJetMain7 (thetaCuspSingleAtomReflectionScale 1 (u - t))| + 100 := by
  intro x hx
  have hAx : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x :=
    hA.trans (thetaCuspSingleAtomReflectionScale_mono hx.1)
  obtain ⟨hq, hq45, hx0, -, -, -, -, -⟩ := regimeOne_data hAx
  rw [thetaCuspLogCurvatureJetFive_eq_bornWitten_sub_jet hx0]
  have hJ := (sharpJet_uniform_bounds hAx).2.2.2.2.2
  have hmono := sharpJetMain7_abs_le_of_le hA (thetaCuspSingleAtomReflectionScale_mono hx.1)
  have hbw : |thetaCuspBornWittenLogSeventhDerivative 1 x| ≤
      bwSevenAbs (thetaCuspSingleAtomReflectionScale 1 (u - t) - 3 / 2)
        (thetaCuspSingleAtomReflectionScale 1 (u + t) - 3 / 2) := by
    simp only [thetaCuspBornWittenLogSeventhDerivative]
    rw [hq]
    apply abs_bornWittenSeven_le (by linarith)
    · linarith [thetaCuspSingleAtomReflectionScale_mono hx.1]
    · linarith [thetaCuspSingleAtomReflectionScale_mono hx.2]
  have h1 := abs_sub (thetaCuspBornWittenLogSeventhDerivative 1 x)
    (thetaCuspLikelihoodSourceLogPartitionJetSeven x)
  have h2 := abs_sub_abs_le_abs_sub (thetaCuspLikelihoodSourceLogPartitionJetSeven x)
    (sharpJetMain7 (thetaCuspSingleAtomReflectionScale 1 x))
  linarith


/-! ## Chamber bounds for the centre jets -/

noncomputable def bwTwoLo (q₁ q₂ : ℝ) : ℝ := (2 * q₁ + 3) * (2 + 3 / q₂ ^ (2 : ℕ))
noncomputable def bwTwoHi (q₁ q₂ : ℝ) : ℝ := (2 * q₂ + 3) * (2 + 3 / q₁ ^ (2 : ℕ))
noncomputable def bwThreeLo (q₁ : ℝ) : ℝ := (2 * q₁ + 3) * (4 - 6 / q₁ ^ (2 : ℕ) - 18 / q₁ ^ (3 : ℕ))
noncomputable def bwThreeHi (q₂ : ℝ) : ℝ := (2 * q₂ + 3) * (4 - 6 / q₂ ^ (2 : ℕ) - 18 / q₂ ^ (3 : ℕ))
noncomputable def bwFourLo (q₁ q₂ : ℝ) : ℝ :=
  (2 * q₁ + 3) * (8 + 12 / q₂ ^ (2 : ℕ) + 108 / q₂ ^ (3 : ℕ) + 162 / q₂ ^ (4 : ℕ))
noncomputable def bwFourHi (q₁ q₂ : ℝ) : ℝ :=
  (2 * q₂ + 3) * (8 + 12 / q₁ ^ (2 : ℕ) + 108 / q₁ ^ (3 : ℕ) + 162 / q₁ ^ (4 : ℕ))
noncomputable def bwFiveLo (q₁ : ℝ) : ℝ :=
  (2 * q₁ + 3) * (16 - 24 / q₁ ^ (2 : ℕ) - 504 / q₁ ^ (3 : ℕ) - 1944 / q₁ ^ (4 : ℕ) - 1944 / q₁ ^ (5 : ℕ))
noncomputable def bwFiveHi (q₂ : ℝ) : ℝ :=
  (2 * q₂ + 3) * (16 - 24 / q₂ ^ (2 : ℕ) - 504 / q₂ ^ (3 : ℕ) - 1944 / q₂ ^ (4 : ℕ) - 1944 / q₂ ^ (5 : ℕ))

theorem div_pow_antitone {c q₁ q : ℝ} (hc : 0 ≤ c) (h1 : 0 < q₁) (hq : q₁ ≤ q) (k : ℕ) :
    c / q ^ k ≤ c / q₁ ^ k :=
  div_le_div_of_nonneg_left hc (pow_pos h1 k) (pow_le_pow_left₀ h1.le hq k)

theorem bornWitten_chamber_bounds {q q₁ q₂ : ℝ} (h1 : 9 / 2 ≤ q₁) (hq1 : q₁ ≤ q) (hq2 : q ≤ q₂) :
    bwTwoLo q₁ q₂ ≤ (2 * q + 3) * (2 + 3 / q ^ (2 : ℕ)) ∧
    (2 * q + 3) * (2 + 3 / q ^ (2 : ℕ)) ≤ bwTwoHi q₁ q₂ ∧
    bwThreeLo q₁ ≤ (2 * q + 3) * (4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ)) ∧
    (2 * q + 3) * (4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ)) ≤ bwThreeHi q₂ ∧
    bwFourLo q₁ q₂ ≤ (2 * q + 3) * (8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ)) ∧
    (2 * q + 3) * (8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ)) ≤ bwFourHi q₁ q₂ ∧
    bwFiveLo q₁ ≤ (2 * q + 3) * (16 - 24 / q ^ (2 : ℕ) - 504 / q ^ (3 : ℕ) - 1944 / q ^ (4 : ℕ) - 1944 / q ^ (5 : ℕ)) ∧
    (2 * q + 3) * (16 - 24 / q ^ (2 : ℕ) - 504 / q ^ (3 : ℕ) - 1944 / q ^ (4 : ℕ) - 1944 / q ^ (5 : ℕ)) ≤ bwFiveHi q₂ := by
  have h10 : 0 < q₁ := by linarith
  have hq0 : 0 < q := by linarith
  have hq20 : 0 < q₂ := by linarith
  -- termwise monotonicity of the negative powers
  have a2 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 3) h10 hq1 2
  have b2 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 3) hq0 hq2 2
  have a6 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 6) h10 hq1 2
  have b6 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 6) hq0 hq2 2
  have a18 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 18) h10 hq1 3
  have b18 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 18) hq0 hq2 3
  have a12 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 12) h10 hq1 2
  have b12 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 12) hq0 hq2 2
  have a108 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 108) h10 hq1 3
  have b108 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 108) hq0 hq2 3
  have a162 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 162) h10 hq1 4
  have b162 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 162) hq0 hq2 4
  have a24 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 24) h10 hq1 2
  have b24 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 24) hq0 hq2 2
  have a504 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 504) h10 hq1 3
  have b504 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 504) hq0 hq2 3
  have a1944 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 1944) h10 hq1 4
  have b1944 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 1944) hq0 hq2 4
  have a1944' := div_pow_antitone (by norm_num : (0:ℝ) ≤ 1944) h10 hq1 5
  have b1944' := div_pow_antitone (by norm_num : (0:ℝ) ≤ 1944) hq0 hq2 5
  -- positivity of the third and fifth profiles at `q₁ ≥ 9/2`
  have c6 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 6) (by norm_num : (0:ℝ) < 9 / 2) h1 2
  have c18 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 18) (by norm_num : (0:ℝ) < 9 / 2) h1 3
  have c24 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 24) (by norm_num : (0:ℝ) < 9 / 2) h1 2
  have c504 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 504) (by norm_num : (0:ℝ) < 9 / 2) h1 3
  have c1944 := div_pow_antitone (by norm_num : (0:ℝ) ≤ 1944) (by norm_num : (0:ℝ) < 9 / 2) h1 4
  have c1944' := div_pow_antitone (by norm_num : (0:ℝ) ≤ 1944) (by norm_num : (0:ℝ) < 9 / 2) h1 5
  norm_num at c6 c18 c24 c504 c1944 c1944'
  have g3pos : 0 ≤ 4 - 6 / q₁ ^ (2 : ℕ) - 18 / q₁ ^ (3 : ℕ) := by linarith
  have g5pos : 0 ≤ 16 - 24 / q₁ ^ (2 : ℕ) - 504 / q₁ ^ (3 : ℕ) - 1944 / q₁ ^ (4 : ℕ) - 1944 / q₁ ^ (5 : ℕ) := by linarith
  have hl : 0 ≤ 2 * q₁ + 3 := by linarith
  have hm : 2 * q₁ + 3 ≤ 2 * q + 3 := by linarith
  have hM : 2 * q + 3 ≤ 2 * q₂ + 3 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold bwTwoLo
    exact mul_le_mul hm (by linarith) (by positivity) (by linarith)
  · unfold bwTwoHi
    exact mul_le_mul hM (by linarith) (by positivity) (by linarith)
  · unfold bwThreeLo
    exact mul_le_mul hm (by linarith) g3pos (by linarith)
  · unfold bwThreeHi
    exact mul_le_mul hM (by linarith) (by linarith) (by linarith)
  · unfold bwFourLo
    exact mul_le_mul hm (by linarith) (by positivity) (by linarith)
  · unfold bwFourHi
    exact mul_le_mul hM (by linarith) (by positivity) (by linarith)
  · unfold bwFiveLo
    exact mul_le_mul hm (by linarith) g5pos (by linarith)
  · unfold bwFiveHi
    exact mul_le_mul hM (by linarith) (by linarith) (by linarith)

/-- **Two-sided chamber bounds for the centre jets** `c, c', c'', c'''` at `u` with
`6 ≤ A₁ ≤ A(u) ≤ A₂`. -/
theorem centreJets_chamber_bounds {u A₁ A₂ : ℝ} (h1 : 6 ≤ A₁)
    (hA1 : A₁ ≤ thetaCuspSingleAtomReflectionScale 1 u) (hA2 : thetaCuspSingleAtomReflectionScale 1 u ≤ A₂) :
    bwTwoLo (A₁ - 3 / 2) (A₂ - 3 / 2) - |sharpJetMain2 A₁| - 1 / 100000000 ≤ thetaCuspLogCurvature u ∧
    thetaCuspLogCurvature u ≤ bwTwoHi (A₁ - 3 / 2) (A₂ - 3 / 2) + |sharpJetMain2 A₁| + 1 / 100000000 ∧
    bwThreeLo (A₁ - 3 / 2) - |sharpJetMain3 A₁| - 1 / 1000000 ≤ thetaCuspLogCurvatureJet u ∧
    thetaCuspLogCurvatureJet u ≤ bwThreeHi (A₂ - 3 / 2) + |sharpJetMain3 A₁| + 1 / 1000000 ∧
    bwFourLo (A₁ - 3 / 2) (A₂ - 3 / 2) - |sharpJetMain4 A₁| - 1 / 10000 ≤ thetaCuspLogCurvatureJetTwo u ∧
    thetaCuspLogCurvatureJetTwo u ≤ bwFourHi (A₁ - 3 / 2) (A₂ - 3 / 2) + |sharpJetMain4 A₁| + 1 / 10000 ∧
    bwFiveLo (A₁ - 3 / 2) - |sharpJetMain5 A₁| - 1 / 100 ≤ thetaCuspLogCurvatureJetThree u ∧
    thetaCuspLogCurvatureJetThree u ≤ bwFiveHi (A₂ - 3 / 2) + |sharpJetMain5 A₁| + 1 / 100 := by
  have hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u := h1.trans hA1
  obtain ⟨hq, hq45, hu0, -, -, -, -, -⟩ := regimeOne_data hA
  obtain ⟨e2, e3, e4, e5, -, -⟩ := sharpJet_uniform_bounds hA
  have m2 := sharpJetMain2_abs_le_of_le h1 hA1
  have m3 := sharpJetMain3_abs_le_of_le h1 hA1
  have m4 := sharpJetMain4_abs_le_of_le h1 hA1
  have m5 := sharpJetMain5_abs_le_of_le h1 hA1
  obtain ⟨bw2, bw3, bw4, bw5⟩ := bornWitten_jets_eq u
  rw [hq] at bw2 bw3 bw4 bw5
  have hbw := bornWitten_chamber_bounds (q := thetaCuspSingleAtomReflectionScale 1 u - 3 / 2)
    (q₁ := A₁ - 3 / 2) (q₂ := A₂ - 3 / 2) (by linarith) (by linarith) (by linarith)
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5⟩ := hbw
  rw [← bw2] at l2 u2
  rw [← bw3] at l3 u3
  rw [← bw4] at l4 u4
  rw [← bw5] at l5 u5
  rw [thetaCuspLogCurvature_eq_bornWitten_sub_jet hu0, thetaCuspLogCurvatureJet_eq_bornWitten_sub_jet hu0,
    thetaCuspLogCurvatureJetTwo_eq_bornWitten_sub_jet hu0,
    thetaCuspLogCurvatureJetThree_eq_bornWitten_sub_jet hu0]
  have j2 := abs_sub_abs_le_abs_sub (thetaCuspLikelihoodSourceLogPartitionJetTwo u)
    (sharpJetMain2 (thetaCuspSingleAtomReflectionScale 1 u))
  have j3 := abs_sub_abs_le_abs_sub (thetaCuspLikelihoodSourceLogPartitionJetThree u)
    (sharpJetMain3 (thetaCuspSingleAtomReflectionScale 1 u))
  have j4 := abs_sub_abs_le_abs_sub (thetaCuspLikelihoodSourceLogPartitionJetFour u)
    (sharpJetMain4 (thetaCuspSingleAtomReflectionScale 1 u))
  have j5 := abs_sub_abs_le_abs_sub (thetaCuspLikelihoodSourceLogPartitionJetFive u)
    (sharpJetMain5 (thetaCuspSingleAtomReflectionScale 1 u))
  have a2 := abs_le.mp (le_refl |thetaCuspLikelihoodSourceLogPartitionJetTwo u|)
  have a3 := abs_le.mp (le_refl |thetaCuspLikelihoodSourceLogPartitionJetThree u|)
  have a4 := abs_le.mp (le_refl |thetaCuspLikelihoodSourceLogPartitionJetFour u|)
  have a5 := abs_le.mp (le_refl |thetaCuspLikelihoodSourceLogPartitionJetFive u|)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## Right-end reduction of the sharp key -/

/-- The sharp key inequality (with the positivity side conditions) follows from its explicit
right-end instance on a `t`-chamber `(0, tb]` with two-sided bounds on all inputs. -/
theorem sharpKey_of_bounds {c₀ c₁ c₂ c₃ S₄ S₅ t : ℝ}
    {c₀l c₀u c₁l c₁u c₂l c₂u c₃l c₃u S₄u S₅u tb : ℝ}
    (ht : 0 < t) (htb : t ≤ tb)
    (h0 : c₀l ≤ c₀ ∧ c₀ ≤ c₀u) (h1 : c₁l ≤ c₁ ∧ c₁ ≤ c₁u) (h2 : c₂l ≤ c₂ ∧ c₂ ≤ c₂u)
    (h3 : c₃l ≤ c₃ ∧ c₃ ≤ c₃u) (hS4 : 0 ≤ S₄ ∧ S₄ ≤ S₄u) (hS5 : 0 ≤ S₅ ∧ S₅ ≤ S₅u)
    (hc0l : 0 ≤ c₀l) (hc1l : 0 ≤ c₁l) (hc2l : 0 ≤ c₂l) (hc3l : 0 ≤ c₃l)
    (hΦb : 0 ≤ c₀l - S₄u * tb ^ (4 : ℕ) / 360) (hEb : 0 ≤ c₀l - S₄u * tb ^ (4 : ℕ) / 120)
    (hOb : 0 ≤ c₁l / 2 - S₅u * tb ^ (4 : ℕ) / 720) (hYb : 0 ≤ c₂l / 3 - S₄u * tb ^ (2 : ℕ) / 30)
    (hnum : 5 * ((c₀u + c₂u * tb ^ (2 : ℕ) / 6 + S₄u * tb ^ (4 : ℕ) / 120) * (S₅u / 90) +
        (c₁u / 2 + c₃u * tb ^ (2 : ℕ) / 24 + S₅u * tb ^ (4 : ℕ) / 720) * (S₄u / 15)) <
      12 * (c₀l - S₄u * tb ^ (4 : ℕ) / 360) *
        ((c₁l / 2 - S₅u * tb ^ (4 : ℕ) / 720) * (c₂l / 3 - S₄u * tb ^ (2 : ℕ) / 30) -
          (c₀u + c₂u * tb ^ (2 : ℕ) / 6 + S₄u * tb ^ (4 : ℕ) / 120) * (c₃u / 12 + S₅u * tb ^ (2 : ℕ) / 180))) :
    (0 ≤ c₀ * t + c₂ * t ^ (3 : ℕ) / 6 - S₄ * t ^ (5 : ℕ) / 120) ∧
    (0 ≤ c₁ * t ^ (2 : ℕ) / 2 + c₃ * t ^ (4 : ℕ) / 24 - S₅ * t ^ (6 : ℕ) / 720) ∧
    (0 ≤ c₂ * t ^ (3 : ℕ) / 3 - S₄ * t ^ (5 : ℕ) / 30) ∧
    (0 ≤ c₃ * t ^ (4 : ℕ) / 12 + S₅ * t ^ (6 : ℕ) / 180) ∧
    (0 ≤ c₀ * t ^ (2 : ℕ) + c₂ * t ^ (4 : ℕ) / 12 - S₄ * t ^ (6 : ℕ) / 360) ∧
    5 * ((c₀ * t + |c₂| * t ^ (3 : ℕ) / 6 + S₄ * t ^ (5 : ℕ) / 120) * (S₅ * t ^ (6 : ℕ) / 90) +
        (c₁ * t ^ (2 : ℕ) / 2 + |c₃| * t ^ (4 : ℕ) / 24 + S₅ * t ^ (6 : ℕ) / 720) * (S₄ * t ^ (5 : ℕ) / 15)) <
      12 * (c₀ * t ^ (2 : ℕ) + c₂ * t ^ (4 : ℕ) / 12 - S₄ * t ^ (6 : ℕ) / 360) *
        ((c₁ * t ^ (2 : ℕ) / 2 + c₃ * t ^ (4 : ℕ) / 24 - S₅ * t ^ (6 : ℕ) / 720) * (c₂ * t ^ (3 : ℕ) / 3 - S₄ * t ^ (5 : ℕ) / 30) -
        (c₀ * t + |c₂| * t ^ (3 : ℕ) / 6 + S₄ * t ^ (5 : ℕ) / 120) * (c₃ * t ^ (4 : ℕ) / 12 + S₅ * t ^ (6 : ℕ) / 180)) := by
  obtain ⟨h0l, h0u⟩ := h0
  obtain ⟨h1l, h1u⟩ := h1
  obtain ⟨h2l, h2u⟩ := h2
  obtain ⟨h3l, h3u⟩ := h3
  obtain ⟨hS40, hS4u⟩ := hS4
  obtain ⟨hS50, hS5u⟩ := hS5
  have hc2 : 0 ≤ c₂ := le_trans hc2l h2l
  have hc3 : 0 ≤ c₃ := le_trans hc3l h3l
  have hc0 : 0 ≤ c₀ := le_trans hc0l h0l
  have hc1 : 0 ≤ c₁ := le_trans hc1l h1l
  rw [abs_of_nonneg hc2, abs_of_nonneg hc3]
  have ht0 : 0 ≤ t := ht.le
  have htb0 : 0 ≤ tb := le_trans ht0 htb
  have ht2 : t ^ (2 : ℕ) ≤ tb ^ (2 : ℕ) := pow_le_pow_left₀ ht0 htb 2
  have ht4 : t ^ (4 : ℕ) ≤ tb ^ (4 : ℕ) := pow_le_pow_left₀ ht0 htb 4
  have ht20 : 0 ≤ t ^ (2 : ℕ) := by positivity
  have ht40 : 0 ≤ t ^ (4 : ℕ) := by positivity
  have ht7 : 0 < t ^ (7 : ℕ) := by positivity
  -- the six reduced quantities at `t`
  have p44 : S₄ * t ^ (4 : ℕ) ≤ S₄u * tb ^ (4 : ℕ) := mul_le_mul hS4u ht4 ht40 (by linarith)
  have p42 : S₄ * t ^ (2 : ℕ) ≤ S₄u * tb ^ (2 : ℕ) := mul_le_mul hS4u ht2 ht20 (by linarith)
  have p54 : S₅ * t ^ (4 : ℕ) ≤ S₅u * tb ^ (4 : ℕ) := mul_le_mul hS5u ht4 ht40 (by linarith)
  have p52 : S₅ * t ^ (2 : ℕ) ≤ S₅u * tb ^ (2 : ℕ) := mul_le_mul hS5u ht2 ht20 (by linarith)
  have p22 : c₂ * t ^ (2 : ℕ) ≤ c₂u * tb ^ (2 : ℕ) := mul_le_mul h2u ht2 ht20 (by linarith)
  have p32 : c₃ * t ^ (2 : ℕ) ≤ c₃u * tb ^ (2 : ℕ) := mul_le_mul h3u ht2 ht20 (by linarith)
  have n22 : 0 ≤ c₂ * t ^ (2 : ℕ) := mul_nonneg hc2 ht20
  have n32 : 0 ≤ c₃ * t ^ (2 : ℕ) := mul_nonneg hc3 ht20
  have hΦ : c₀l - S₄u * tb ^ (4 : ℕ) / 360 ≤ c₀ + c₂ * t ^ (2 : ℕ) / 12 - S₄ * t ^ (4 : ℕ) / 360 := by linarith
  have hO : c₁l / 2 - S₅u * tb ^ (4 : ℕ) / 720 ≤ c₁ / 2 + c₃ * t ^ (2 : ℕ) / 24 - S₅ * t ^ (4 : ℕ) / 720 := by linarith
  have hY : c₂l / 3 - S₄u * tb ^ (2 : ℕ) / 30 ≤ c₂ / 3 - S₄ * t ^ (2 : ℕ) / 30 := by linarith
  have hE : c₀ + c₂ * t ^ (2 : ℕ) / 6 + S₄ * t ^ (4 : ℕ) / 120 ≤ c₀u + c₂u * tb ^ (2 : ℕ) / 6 + S₄u * tb ^ (4 : ℕ) / 120 := by
    linarith
  have hΛ : c₃ / 12 + S₅ * t ^ (2 : ℕ) / 180 ≤ c₃u / 12 + S₅u * tb ^ (2 : ℕ) / 180 := by linarith
  have hOu : c₁ / 2 + c₃ * t ^ (2 : ℕ) / 24 + S₅ * t ^ (4 : ℕ) / 720 ≤
      c₁u / 2 + c₃u * tb ^ (2 : ℕ) / 24 + S₅u * tb ^ (4 : ℕ) / 720 := by linarith
  have hE0 : 0 ≤ c₀ + c₂ * t ^ (2 : ℕ) / 6 + S₄ * t ^ (4 : ℕ) / 120 := by positivity
  have hΛ0 : 0 ≤ c₃ / 12 + S₅ * t ^ (2 : ℕ) / 180 := by positivity
  have hOu0 : 0 ≤ c₁ / 2 + c₃ * t ^ (2 : ℕ) / 24 + S₅ * t ^ (4 : ℕ) / 720 := by positivity
  -- generalize the reduced quantities
  generalize hΦt : c₀ + c₂ * t ^ (2 : ℕ) / 12 - S₄ * t ^ (4 : ℕ) / 360 = Φt at hΦ
  generalize hOt : c₁ / 2 + c₃ * t ^ (2 : ℕ) / 24 - S₅ * t ^ (4 : ℕ) / 720 = Ot at hO
  generalize hYt : c₂ / 3 - S₄ * t ^ (2 : ℕ) / 30 = Yt at hY
  generalize hEt : c₀ + c₂ * t ^ (2 : ℕ) / 6 + S₄ * t ^ (4 : ℕ) / 120 = Et at hE hE0
  generalize hΛt : c₃ / 12 + S₅ * t ^ (2 : ℕ) / 180 = Λt at hΛ hΛ0
  generalize hOut : c₁ / 2 + c₃ * t ^ (2 : ℕ) / 24 + S₅ * t ^ (4 : ℕ) / 720 = Out at hOu hOu0
  generalize hΦb' : c₀l - S₄u * tb ^ (4 : ℕ) / 360 = Φb at hΦ hΦb hnum
  generalize hOb' : c₁l / 2 - S₅u * tb ^ (4 : ℕ) / 720 = Ob at hO hOb hnum
  generalize hYb' : c₂l / 3 - S₄u * tb ^ (2 : ℕ) / 30 = Yb at hY hYb hnum
  generalize hEb' : c₀u + c₂u * tb ^ (2 : ℕ) / 6 + S₄u * tb ^ (4 : ℕ) / 120 = Eb at hE hnum
  generalize hΛb' : c₃u / 12 + S₅u * tb ^ (2 : ℕ) / 180 = Λb at hΛ hnum
  generalize hOub' : c₁u / 2 + c₃u * tb ^ (2 : ℕ) / 24 + S₅u * tb ^ (4 : ℕ) / 720 = Oub at hOu hnum
  have hΦt0 : 0 ≤ Φt := le_trans hΦb hΦ
  have hOt0 : 0 ≤ Ot := le_trans hOb hO
  have hYt0 : 0 ≤ Yt := le_trans hYb hY
  have hEb0 : 0 ≤ Eb := le_trans hE0 hE
  have hΛb0 : 0 ≤ Λb := le_trans hΛ0 hΛ
  have hOub0 : 0 ≤ Oub := le_trans hOu0 hOu
  -- the bracket at `tb` is positive
  have hLb0 : 0 ≤ 5 * (Eb * (S₅u / 90) + Oub * (S₄u / 15)) := by
    have : 0 ≤ S₄u := le_trans hS40 hS4u
    have : 0 ≤ S₅u := le_trans hS50 hS5u
    positivity
  have hbr : 0 < Ob * Yb - Eb * Λb := by
    by_contra hcon
    have hcon' : Ob * Yb - Eb * Λb ≤ 0 := not_lt.mp hcon
    have : 12 * Φb * (Ob * Yb - Eb * Λb) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon'
    linarith
  -- comparisons of the brackets
  have hOY : Ob * Yb ≤ Ot * Yt := mul_le_mul hO hY hYb hOt0
  have hEL : Et * Λt ≤ Eb * Λb := mul_le_mul hE hΛ hΛ0 hEb0
  have hbrt : Ob * Yb - Eb * Λb ≤ Ot * Yt - Et * Λt := by linarith
  have hR : 12 * Φb * (Ob * Yb - Eb * Λb) ≤ 12 * Φt * (Ot * Yt - Et * Λt) := by
    have := mul_le_mul hΦ hbrt hbr.le hΦt0
    linarith
  have hL : 5 * (Et * (S₅ / 90) + Out * (S₄ / 15)) ≤ 5 * (Eb * (S₅u / 90) + Oub * (S₄u / 15)) := by
    have := mul_le_mul hE (div_le_div_of_nonneg_right hS5u (by norm_num : (0:ℝ) ≤ 90)) (by positivity) hEb0
    have := mul_le_mul hOu (div_le_div_of_nonneg_right hS4u (by norm_num : (0:ℝ) ≤ 15)) (by positivity) hOub0
    linarith
  -- factor `t⁷`
  have eL : 5 * ((c₀ * t + c₂ * t ^ (3 : ℕ) / 6 + S₄ * t ^ (5 : ℕ) / 120) * (S₅ * t ^ (6 : ℕ) / 90) +
      (c₁ * t ^ (2 : ℕ) / 2 + c₃ * t ^ (4 : ℕ) / 24 + S₅ * t ^ (6 : ℕ) / 720) * (S₄ * t ^ (5 : ℕ) / 15)) =
      t ^ (7 : ℕ) * (5 * (Et * (S₅ / 90) + Out * (S₄ / 15))) := by
    rw [← hEt, ← hOut]; ring
  have eR : 12 * (c₀ * t ^ (2 : ℕ) + c₂ * t ^ (4 : ℕ) / 12 - S₄ * t ^ (6 : ℕ) / 360) *
      ((c₁ * t ^ (2 : ℕ) / 2 + c₃ * t ^ (4 : ℕ) / 24 - S₅ * t ^ (6 : ℕ) / 720) * (c₂ * t ^ (3 : ℕ) / 3 - S₄ * t ^ (5 : ℕ) / 30) -
      (c₀ * t + c₂ * t ^ (3 : ℕ) / 6 + S₄ * t ^ (5 : ℕ) / 120) * (c₃ * t ^ (4 : ℕ) / 12 + S₅ * t ^ (6 : ℕ) / 180)) =
      t ^ (7 : ℕ) * (12 * Φt * (Ot * Yt - Et * Λt)) := by
    rw [← hΦt, ← hOt, ← hYt, ← hEt, ← hΛt]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ t * (c₀ + c₂ * t ^ (2 : ℕ) / 6 - S₄ * t ^ (4 : ℕ) / 120) := by
      apply mul_nonneg ht0
      linarith
    linarith [this]
  · have : 0 ≤ t ^ (2 : ℕ) * Ot := mul_nonneg ht20 hOt0
    rw [← hOt] at this; linarith [this]
  · have : 0 ≤ t ^ (3 : ℕ) * Yt := mul_nonneg (by positivity) hYt0
    rw [← hYt] at this; linarith [this]
  · positivity
  · have : 0 ≤ t ^ (2 : ℕ) * Φt := mul_nonneg ht20 hΦt0
    rw [← hΦt] at this; linarith [this]
  · rw [eL, eR]
    apply mul_lt_mul_of_pos_left _ ht7
    linarith

end RHTower
