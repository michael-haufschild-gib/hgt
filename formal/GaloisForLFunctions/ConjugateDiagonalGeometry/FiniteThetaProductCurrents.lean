import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaReadingError

/-!
# Finite theta currents on compact pair tests

One scalar error constant controls every compact C² test through its Laplacian bound.
Positivity telescopes two scalar errors into a product-current estimate. Separate
Laplacians suffice. A source-defined prefix stage dominates both the support radius
and the differential norm, so its error vanishes for arbitrary smooth test sequences.
-/

open Complex MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Laplacian Topology
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
noncomputable section

private theorem compact_source_decay_bound {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    (Real.pi * ((n : ℝ) + 2) ^ 2 / 2 + 8 * C * ((n : ℝ) + 1) ^ 6) *
        Real.exp (-(((n : ℝ) + 1) ^ 4)) ≤
      (2 * Real.pi + 8 * C) * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
  have h := source_poly_exp_window_le hC 0 n 0 0
    (by simpa only [abs_zero] using Nat.cast_nonneg (α := ℝ) n)
    (by simp only [Nat.cast_zero, abs_zero, zero_mul];
        exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) n])))
  simp only [abs_zero, Nat.cast_zero, zero_mul, add_zero] at h
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  linarith only [sq_nonneg ((n : ℝ) + 3)]

/-- One constant controls all compact C² tests after their support fits inside the cutoff. -/
theorem exists_uniform_finiteTheta_compact_current_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → ∀ φ : ℂ → ℝ,
      ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ B : ℝ, 0 ≤ B →
      (fun z => sourceCutoff n z * φ z) = φ →
      (∀ z, |Δ φ z| ≤ B) →
      |finiteThetaSourceReading φ n - zetaSourceTrace φ| ≤
        K * B * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
  obtain ⟨C, hC, hlocal⟩ := exists_explicitSourceLocalError_bound
  let K := 2 * finiteThetaPotentialConstant + (2 * Real.pi)⁻¹ * (2 * Real.pi + 8 * C)
  have hK : 0 ≤ K := by
    have hF := finiteThetaPotentialConstant_nonneg
    dsimp only [K]
    positivity
  refine ⟨K, hK, fun n hn1 φ hp hc B hB hn hbound => ?_⟩
  have hb : ∀ z ∈ closedBall (0 : ℂ) |(n : ℝ) + 2|,
      |Δ (fun w => sourceCutoff n w * φ w) z| ≤ sourceCutoffControl n * B := by
    intro z _
    rw [hn]
    exact (hbound z).trans (by nlinarith only [one_le_sourceCutoffControl n, hB])
  have hf := abs_finiteThetaSourceReading_sub_explicit_le φ hp hn1 hB hb
  have hs := abs_explicitSourceReading_sub_current_le φ hp n hb
  rw [hn, xiCurrentPairing_eq_trace φ hp hc] at hs
  have hf' : |finiteThetaSourceReading φ n - explicitSourceReading φ n| ≤
      (2 * B * finiteThetaPotentialConstant) *
        Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
    have hF := finiteThetaPotentialConstant_nonneg
    have h := mul_le_mul_of_nonneg_left (compact_source_decay_bound (C := 0) (by norm_num) n)
      (show 0 ≤ B * finiteThetaPotentialConstant / Real.pi by positivity)
    simp only [mul_zero, zero_mul, add_zero] at h
    have heq : (2 * Real.pi)⁻¹ * B * finiteThetaPotentialConstant *
        Real.exp (-(((n : ℝ) + 1) ^ 4)) * (Real.pi * ((n : ℝ) + 2) ^ 2) =
      B * finiteThetaPotentialConstant / Real.pi *
        (Real.pi * ((n : ℝ) + 2) ^ 2 / 2 * Real.exp (-(((n : ℝ) + 1) ^ 4))) := by
      field_simp
    rw [heq] at hf
    exact hf.trans (h.trans_eq (by field_simp))
  have hs' : |explicitSourceReading φ n - zetaSourceTrace φ| ≤
      ((2 * Real.pi)⁻¹ * B * (2 * Real.pi + 8 * C)) *
        Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
    have h := (hlocal n hn1).trans (compact_source_decay_bound hC.le n)
    have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ (2 * Real.pi)⁻¹ * B by positivity)
    exact hs.trans (by nlinarith only [hm])
  have ht := dist_triangle (finiteThetaSourceReading φ n) (explicitSourceReading φ n)
    (zetaSourceTrace φ)
  simp only [Real.dist_eq] at ht
  exact (ht.trans (add_le_add hf' hs')).trans_eq (by dsimp only [K]; ring)

#print axioms exists_uniform_finiteTheta_compact_current_error

/-- The prefix stage dominates the support radius and the actual differential cost. -/
def thetaTestStage (R n : ℕ) (B : ℝ) : ℕ := n + R + 4 + Nat.ceil B

theorem le_thetaTestStage (R n : ℕ) (B : ℝ) : n ≤ thetaTestStage R n B := by
  unfold thetaTestStage
  omega

theorem differentialCost_le_thetaTestStage (R n : ℕ) (B : ℝ) :
    B ≤ (thetaTestStage R n B : ℝ) := by
  exact (Nat.le_ceil B).trans (by exact_mod_cast (show Nat.ceil B ≤ thetaTestStage R n B by
    unfold thetaTestStage
    omega))

private theorem thetaDecay_exponent_le_neg {x : ℝ} (hx : 8 ≤ x) :
    -x^4 + 56*x^2 + 62 ≤ -x := by
  have hsq : 64 ≤ x^2 := by nlinarith only [hx]
  have hfour : 64*x^2 ≤ x^4 := by
    nlinarith only [mul_le_mul_of_nonneg_right hsq (sq_nonneg x)]
  have hlinear : 8*x ≤ x^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hx (by linarith only [hx] : 0 ≤ x)]
  nlinarith only [hx, hlinear, hfour]

/-- Increasing the prefix with its differential norm handles any smooth compact test sequence. -/
theorem tendsto_thetaTestStage_error (R : ℕ) {B : ℕ → ℝ} (hB : ∀ n, 0 ≤ B n)
    {K : ℝ} (hK : 0 ≤ K) :
    Tendsto (fun n : ℕ => K * B n * Real.exp
      (-((thetaTestStage R n (B n) : ℝ)^4) +
        56*(thetaTestStage R n (B n) : ℝ)^2 + 62)) atTop (𝓝 0) := by
  let k : ℕ → ℝ := fun n => thetaTestStage R n (B n)
  have hk : Tendsto k atTop atTop :=
    tendsto_atTop_mono (fun n => by
      change (n : ℝ) ≤ (thetaTestStage R n (B n) : ℝ)
      exact_mod_cast le_thetaTestStage R n (B n))
      tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => K * (k n * Real.exp (-k n))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hk
    simpa only [pow_one, mul_zero, Function.comp_apply] using h.const_mul K
  apply squeeze_zero' (Eventually.of_forall fun n =>
    mul_nonneg (mul_nonneg hK (hB n)) (Real.exp_pos _).le) _ hlim
  filter_upwards [hk.eventually_ge_atTop 8] with n hn
  have hcost : B n ≤ k n := differentialCost_le_thetaTestStage R n (B n)
  have he : Real.exp (-(k n)^4 + 56*(k n)^2 + 62) ≤ Real.exp (-k n) :=
    Real.exp_le_exp.mpr (thetaDecay_exponent_le_neg hn)
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hcost hK) he
    (Real.exp_pos _).le (mul_nonneg hK (by dsimp only [k]; positivity))).trans_eq (by ring)

#print axioms tendsto_thetaTestStage_error



theorem continuous_finiteThetaSourceCurvature {η : ℝ} (hη : 0 < η) (N : ℕ) :
    Continuous (finiteThetaSourceCurvature η N) := by
  have he : finiteThetaSourceCurvature η N =
      (fun z => (1 / 2 : ℝ) * Δ (finiteThetaSourcePotential η N) z) := by
    funext z
    rw [laplacian_finiteThetaSourcePotential hη]
    ring
  rw [he]
  exact continuous_const.mul (continuous_test_laplacian (contDiff_finiteThetaSourcePotential hη N))

theorem integrable_finiteThetaSourceReading (n : ℕ) (φ : ℂ → ℝ) (hφ : Continuous φ) :
    Integrable (fun z => sourceCutoff n z * φ z *
      finiteThetaSourceCurvature (explicitSourceRegulator n) (explicitThetaIntegerCutoff n) z) :=
  (((sourceCutoff n).continuous.mul hφ).mul
    (continuous_finiteThetaSourceCurvature (explicitSourceRegulator_pos n) _)).integrable_of_hasCompactSupport
      (sourceCutoff n).hasCompactSupport.mul_right.mul_right

theorem finiteThetaSourceReading_nonneg {φ : ℂ → ℝ} (hφ : ∀ z, 0 ≤ φ z) (n : ℕ) :
    0 ≤ finiteThetaSourceReading φ n := by
  apply mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
  apply integral_nonneg
  intro z
  exact mul_nonneg (mul_nonneg (sourceCutoff n).nonneg (hφ z))
    (finiteThetaSourceCurvature_nonneg (explicitSourceRegulator_pos n).le _ z)

theorem finiteThetaSourceReading_mono (φ ψ : ℂ → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) (h : ∀ z, φ z ≤ ψ z) (n : ℕ) :
    finiteThetaSourceReading φ n ≤ finiteThetaSourceReading ψ n := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.pi_pos.le)
  apply integral_mono (integrable_finiteThetaSourceReading n φ hφ)
    (integrable_finiteThetaSourceReading n ψ hψ)
  intro z
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (h z) (sourceCutoff n).nonneg)
    (finiteThetaSourceCurvature_nonneg (explicitSourceRegulator_pos n).le _ z)

theorem finiteThetaSourceReading_const_mul (C : ℝ) (φ : ℂ → ℝ) (n : ℕ) :
    finiteThetaSourceReading (fun z => C * φ z) n = C * finiteThetaSourceReading φ n := by
  unfold finiteThetaSourceReading
  have he : (fun z => sourceCutoff n z * (C * φ z) *
      finiteThetaSourceCurvature (explicitSourceRegulator n) (explicitThetaIntegerCutoff n) z) =
      (fun z => C * (sourceCutoff n z * φ z *
      finiteThetaSourceCurvature (explicitSourceRegulator n) (explicitThetaIntegerCutoff n) z)) := by
    funext z
    ring
  rw [he, integral_const_mul]
  ring

theorem finiteThetaSourceReading_sub (φ ψ : ℂ → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) (n : ℕ) :
    finiteThetaSourceReading (fun z => φ z - ψ z) n =
      finiteThetaSourceReading φ n - finiteThetaSourceReading ψ n := by
  unfold finiteThetaSourceReading
  simp_rw [mul_sub, sub_mul]
  rw [integral_sub (integrable_finiteThetaSourceReading n φ hφ)
    (integrable_finiteThetaSourceReading n ψ hψ), mul_sub]

theorem finiteThetaSourceReading_finsetSum {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℝ)
    (hF : ∀ i ∈ S, Continuous (F i)) (n : ℕ) :
    finiteThetaSourceReading (fun z => ∑ i ∈ S, F i z) n =
      ∑ i ∈ S, finiteThetaSourceReading (F i) n := by
  unfold finiteThetaSourceReading
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i hi => integrable_finiteThetaSourceReading n (F i) (hF i hi)),
    Finset.mul_sum]

theorem abs_finiteThetaSourceReading_le (φ : ℂ → ℝ) (n : ℕ) :
    |finiteThetaSourceReading φ n| ≤ finiteThetaSourceReading (fun z => |φ z|) n := by
  unfold finiteThetaSourceReading
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr Real.pi_pos.le)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.pi_pos.le)
  have h := norm_integral_le_integral_norm (μ := volume)
    (fun z => sourceCutoff n z * φ z *
      finiteThetaSourceCurvature (explicitSourceRegulator n) (explicitThetaIntegerCutoff n) z)
  simpa only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sourceCutoff n).nonneg,
    abs_of_nonneg (finiteThetaSourceCurvature_nonneg (explicitSourceRegulator_pos n).le _ _)] using h

theorem continuous_finiteThetaSourceReading_family {F : ℂ → ℂ → ℝ}
    (hrow : ∀ z, Continuous (F z)) (hcol : ∀ w, Continuous (fun z => F z w))
    (hbound : ∀ z w, |F z w| ≤ 1) (n : ℕ) :
    Continuous (fun z => finiteThetaSourceReading (F z) n) := by
  let d := finiteThetaSourceCurvature (explicitSourceRegulator n) (explicitThetaIntegerCutoff n)
  have hd : Continuous d := continuous_finiteThetaSourceCurvature (explicitSourceRegulator_pos n) _
  have hdn (w : ℂ) : 0 ≤ d w :=
    finiteThetaSourceCurvature_nonneg (explicitSourceRegulator_pos n).le _ w
  have hi : Integrable (fun w => sourceCutoff n w * d w) := by
    simpa only [mul_one] using integrable_finiteThetaSourceReading n (fun _ => 1) continuous_const
  apply continuous_const.mul
  apply MeasureTheory.continuous_of_dominated
    (bound := fun w => sourceCutoff n w * d w)
  · intro z
    exact (((sourceCutoff n).continuous.mul (hrow z)).mul hd).aestronglyMeasurable
  · intro z
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (sourceCutoff n).nonneg, abs_of_nonneg (hdn w)]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left (hbound z w) (sourceCutoff n).nonneg).trans_eq (mul_one _))
      (hdn w)
  · exact hi
  · filter_upwards [] with w
    exact (continuous_const.mul (hcol w)).mul continuous_const

theorem abs_finiteThetaSourceReading_sub_le {φ ψ χ : ℂ → ℝ} {A : ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) (hχ : Continuous χ)
    (h : ∀ z, |φ z - ψ z| ≤ A * χ z) (n : ℕ) :
    |finiteThetaSourceReading φ n - finiteThetaSourceReading ψ n| ≤
      A * finiteThetaSourceReading χ n := by
  rw [← finiteThetaSourceReading_sub φ ψ hφ hψ]
  have hb := finiteThetaSourceReading_mono (fun z => |φ z - ψ z|) (fun z => A * χ z)
    (hφ.sub hψ).abs (continuous_const.mul hχ) h n
  rw [finiteThetaSourceReading_const_mul] at hb
  exact (abs_finiteThetaSourceReading_le _ n).trans hb

#print axioms continuous_finiteThetaSourceReading_family

/-- Positivity turns separate scalar current errors into a product-current error. -/
theorem abs_finiteThetaProductSourceReading_sub_finitePair_le
    {F : ℂ → ℂ → ℝ} (hrow : ∀ z, Continuous (F z))
    (hcol : ∀ w, Continuous (fun z => F z w)) (hbound : ∀ z w, |F z w| ≤ 1)
    (S : Finset ℂ) (m : ℂ → ℝ) (hm : ∀ z ∈ S, 0 ≤ m z)
    {χ : ℂ → ℝ} (hχ : Continuous χ) {A : ℝ} (n : ℕ)
    (hrowerr : ∀ z, |finiteThetaSourceReading (F z) n - ∑ w ∈ S, m w * F z w| ≤ A * χ z)
    (hcolerr : ∀ w, |finiteThetaSourceReading (fun z => F z w) n -
      ∑ z ∈ S, m z * F z w| ≤ A * χ w) :
    |finiteThetaSourceReading (fun z => finiteThetaSourceReading (F z) n) n -
      ∑ z ∈ S, m z * (∑ w ∈ S, m w * F z w)| ≤
        A * (finiteThetaSourceReading χ n + ∑ z ∈ S, m z * χ z) := by
  let g : ℂ → ℝ := fun z => ∑ w ∈ S, m w * F z w
  have hgc : Continuous g := continuous_finsetSum _ fun w _ =>
    continuous_const.mul (hcol w)
  have hqc := continuous_finiteThetaSourceReading_family hrow hcol hbound n
  have hfirst := abs_finiteThetaSourceReading_sub_le hqc hgc hχ hrowerr n
  have hQg : finiteThetaSourceReading g n =
      ∑ w ∈ S, m w * finiteThetaSourceReading (fun z => F z w) n := by
    rw [show g = (fun z => ∑ w ∈ S, m w * F z w) from rfl,
      finiteThetaSourceReading_finsetSum S (fun w z => m w * F z w)
        (fun w _ => continuous_const.mul (hcol w))]
    simp only [finiteThetaSourceReading_const_mul]
  have hswap : (∑ z ∈ S, m z * g z) =
      ∑ w ∈ S, m w * (∑ z ∈ S, m z * F z w) := by
    dsimp only [g]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro z _
    ring
  have hsecond : |finiteThetaSourceReading g n - ∑ z ∈ S, m z * g z| ≤
      A * (∑ w ∈ S, m w * χ w) := by
    rw [hQg, hswap, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ w ∈ S, |m w * finiteThetaSourceReading (fun z => F z w) n -
          m w * (∑ z ∈ S, m z * F z w)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ S, A * (m w * χ w) := by
        apply Finset.sum_le_sum
        intro w hw
        rw [← mul_sub, abs_mul, abs_of_nonneg (hm w hw)]
        exact (mul_le_mul_of_nonneg_left (hcolerr w) (hm w hw)).trans_eq (by ring)
      _ = _ := (Finset.mul_sum S (fun w => m w * χ w) A).symm
  calc
    _ = |(finiteThetaSourceReading (fun z => finiteThetaSourceReading (F z) n) n -
          finiteThetaSourceReading g n) +
        (finiteThetaSourceReading g n - ∑ z ∈ S, m z * g z)| := by
      congr 1
      dsimp only [g]
      ring
    _ ≤ |finiteThetaSourceReading (fun z => finiteThetaSourceReading (F z) n) n -
          finiteThetaSourceReading g n| +
        |finiteThetaSourceReading g n - ∑ z ∈ S, m z * g z| := abs_add_le _ _
    _ ≤ A * finiteThetaSourceReading χ n + A * (∑ z ∈ S, m z * χ z) :=
      add_le_add hfirst hsecond
    _ = _ := by ring

#print axioms abs_finiteThetaProductSourceReading_sub_finitePair_le

/-- Separate Laplacians vary continuously with both arguments of a smooth pair test. -/
theorem continuous_pairTest_row_laplacian {F : ℂ → ℂ → ℝ}
    (hF : ContDiff ℝ 2 (Function.uncurry F)) :
    Continuous (fun p : ℂ × ℂ => Δ (F p.1) p.2) := by
  have hspread : ContDiff ℝ 2 (fun p : (ℂ × ℂ) × ℂ => F p.1.1 p.2) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hfirst (v : ℂ) : ContDiff ℝ 1
      (fun p : ℂ × ℂ => fderiv ℝ (F p.1) p.2 v) :=
    hspread.fderiv_apply contDiff_snd contDiff_const (by norm_num)
  have hsecond (v : ℂ) : Continuous
      (fun p : ℂ × ℂ => Bottcher.dderiv (F p.1) v p.2) := by
    have hs : ContDiff ℝ 1 (fun p : (ℂ × ℂ) × ℂ =>
        fderiv ℝ (F p.1.1) p.2 v) :=
      (hfirst v).comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact (hs.fderiv_apply (n := 0) contDiff_snd contDiff_const (by norm_num)).continuous
  have he : (fun p : ℂ × ℂ => Δ (F p.1) p.2) =
      (fun p => Bottcher.dderiv (F p.1) 1 p.2 +
        Bottcher.dderiv (F p.1) Complex.I p.2) := by
    funext p
    exact Bottcher.laplacian_eq_dderiv _
      (hF.comp (contDiff_const.prodMk contDiff_id)) p.2
  rw [he]
  exact (hsecond 1).add (hsecond Complex.I)

#print axioms continuous_pairTest_row_laplacian

/-- A source-defined bound for the two separate Laplacians on a compact pair support. -/
def pairTestDifferentialBound (F : ℂ → ℂ → ℝ) (R : ℕ) : ℝ :=
  1 + |sSup ((fun p : ℂ × ℂ => |Δ (F p.1) p.2|) ''
    (closedBall (0 : ℂ) ((R : ℝ) + 2) ×ˢ closedBall (0 : ℂ) ((R : ℝ) + 2)))| +
    |sSup ((fun p : ℂ × ℂ => |Δ (fun z => F z p.1) p.2|) ''
    (closedBall (0 : ℂ) ((R : ℝ) + 2) ×ˢ closedBall (0 : ℂ) ((R : ℝ) + 2)))| +
    ‖sourceCutoffLaplacian (R + 1)‖

theorem one_le_pairTestDifferentialBound (F : ℂ → ℂ → ℝ) (R : ℕ) :
    1 ≤ pairTestDifferentialBound F R := by
  unfold pairTestDifferentialBound
  linarith only [abs_nonneg (sSup ((fun p : ℂ × ℂ => |Δ (F p.1) p.2|) ''
    (closedBall (0 : ℂ) ((R : ℝ) + 2) ×ˢ closedBall (0 : ℂ) ((R : ℝ) + 2)))),
    abs_nonneg (sSup ((fun p : ℂ × ℂ => |Δ (fun z => F z p.1) p.2|) ''
    (closedBall (0 : ℂ) ((R : ℝ) + 2) ×ˢ closedBall (0 : ℂ) ((R : ℝ) + 2)))),
    norm_nonneg (sourceCutoffLaplacian (R + 1))]

theorem pairTestDifferentialBound_row {F : ℂ → ℂ → ℝ}
    (hF : ContDiff ℝ 2 (Function.uncurry F)) (R : ℕ) {z w : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) ((R : ℝ) + 2))
    (hw : w ∈ closedBall (0 : ℂ) ((R : ℝ) + 2)) :
    |Δ (F z) w| ≤ pairTestDifferentialBound F R := by
  have hb := ((isCompact_closedBall (0 : ℂ) ((R : ℝ) + 2)).prod
    (isCompact_closedBall (0 : ℂ) ((R : ℝ) + 2))).bddAbove_image
      (continuous_pairTest_row_laplacian hF).abs.continuousOn
  have hs := le_csSup hb (mem_image_of_mem (fun p : ℂ × ℂ => |Δ (F p.1) p.2|)
    (show (z, w) ∈ closedBall (0 : ℂ) ((R : ℝ) + 2) ×ˢ
      closedBall (0 : ℂ) ((R : ℝ) + 2) from ⟨hz, hw⟩))
  exact hs.trans ((le_abs_self _).trans (by
    unfold pairTestDifferentialBound
    have h := abs_nonneg (sSup ((fun p : ℂ × ℂ => |Δ (fun z => F z p.1) p.2|) ''
      (closedBall (0 : ℂ) ((R : ℝ) + 2) ×ˢ closedBall (0 : ℂ) ((R : ℝ) + 2))))
    have hn := norm_nonneg (sourceCutoffLaplacian (R + 1))
    linarith only [h, hn]))

theorem pairTestDifferentialBound_swap (F : ℂ → ℂ → ℝ) (R : ℕ) :
    pairTestDifferentialBound (fun z w => F w z) R = pairTestDifferentialBound F R := by
  unfold pairTestDifferentialBound
  ring

#print axioms pairTestDifferentialBound_row

theorem pairTest_hasCompactSupport_row {F : ℂ → ℂ → ℝ} (R : ℕ)
    (hzero : ∀ z w, w ∉ closedBall (0 : ℂ) ((R : ℝ) + 2) → F z w = 0)
    (z : ℂ) : HasCompactSupport (F z) := by
  have hs : tsupport (F z) ⊆ closedBall (0 : ℂ) ((R : ℝ) + 2) := by
    apply closure_minimal _ isClosed_closedBall
    intro w hw
    by_contra hn
    exact hw (hzero z w hn)
  exact (isCompact_closedBall (0 : ℂ) ((R : ℝ) + 2)).of_isClosed_subset (isClosed_tsupport _) hs

/-- A larger fixed cutoff is a common majorant for all separate row errors. -/
theorem pairTestDifferentialBound_row_global {F : ℂ → ℂ → ℝ}
    (hF : ContDiff ℝ 2 (Function.uncurry F)) (R : ℕ)
    (hzero : ∀ z w, z ∉ closedBall (0 : ℂ) ((R : ℝ) + 2) ∨
      w ∉ closedBall (0 : ℂ) ((R : ℝ) + 2) → F z w = 0)
    (z w : ℂ) : |Δ (F z) w| ≤ pairTestDifferentialBound F R * sourceCutoff (R + 1) z := by
  have hB : 0 ≤ pairTestDifferentialBound F R :=
    zero_le_one.trans (one_le_pairTestDifferentialBound F R)
  have hp : ContDiff ℝ 2 (F z) := hF.comp (contDiff_const.prodMk contDiff_id)
  by_cases hz : z ∈ closedBall (0 : ℂ) ((R : ℝ) + 2)
  · have hχ : sourceCutoff (R + 1) z = 1 := by
      apply (sourceCutoff (R + 1)).one_of_mem_closedBall
      change z ∈ closedBall (0 : ℂ) (((R + 1 : ℕ) : ℝ) + 1)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hz
    rw [hχ, mul_one]
    by_cases hw : w ∈ closedBall (0 : ℂ) ((R : ℝ) + 2)
    · exact pairTestDifferentialBound_row hF R hz hw
    · have hts : tsupport (F z) ⊆ closedBall (0 : ℂ) ((R : ℝ) + 2) := by
        apply closure_minimal _ isClosed_closedBall
        intro u hu
        by_contra hn
        exact hu (hzero z u (Or.inr hn))
      have he : Δ (F z) w = 0 := by
        by_contra hn
        exact hw (hts (tsupport_test_laplacian_subset hp (subset_tsupport _ hn)))
      rw [he, abs_zero]
      exact hB
  · have he : F z = fun _ => 0 := funext fun u => hzero z u (Or.inl hz)
    rw [he]
    simp only [laplacian_const, Pi.zero_apply, abs_zero]
    exact mul_nonneg hB (sourceCutoff (R + 1)).nonneg

#print axioms pairTestDifferentialBound_row_global

/-- A compact source trace is the exact finite multiplicity sum in its support disc. -/
theorem zetaSourceTrace_eq_sum_on_ball (R : ℝ) (φ : ℂ → ℝ)
    (hsupp : ∀ z, z ∉ closedBall (0 : ℂ) R → φ z = 0) :
    zetaSourceTrace φ = ∑ z ∈ (RHTower.xi_zeros_closedBall_finite 0 R).toFinset,
      (GaloisForLFunctions.HTGeometry.zeroMult RHTower.xi z : ℝ) * φ z := by
  have hc : HasCompactSupport φ := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) hsupp
  unfold zetaSourceTrace
  rw [← xi_realDivisorPairing_eq_carrier φ hc]
  apply GaloisForLFunctions.HTGeometry.realDivisorPairing_eq_sum
  intro z hm hz
  rw [Set.Finite.mem_toFinset]
  refine ⟨?_, GaloisForLFunctions.HTGeometry.eq_zero_of_zeroMult_ne_zero hm⟩
  by_contra hn
  exact hz (hsupp z hn)

#print axioms zetaSourceTrace_eq_sum_on_ball

end
end GaloisForLFunctions.ConjugateDiagonalGeometry
