import GaloisForLFunctions.RHTower.ThetaCuspTiltedSchwartz
import GaloisForLFunctions.RHTower.MobiusThetaNativeCollarSourceTransport
import GaloisForLFunctions.RHTower.DeningerSecondaryCollarDefect
import GaloisForLFunctions.RHTower.DeningerMeyerTopology
import GaloisForLFunctions.RHTower.XiShiftedHardEdgePolynomialGaussianExponentialSchwartz

/-!
# All-exponential admission of the original native theta collar

A monomial upgrade of the existing polynomial Gaussian majorant bounds every
source derivative at every real exponential rate. Temperate multiplication,
the exact half-density tilt and native dilation retain this admission. Thus the
original internal jet at every positive depth lies in the existing Meyer source,
with no extra source-admission premise. Its full arithmetic reconstruction now
converges at all positive depths, including the unchanged finite prime prefix.

This does not identify the two fixed readers or assert a vanishing boundary.
-/

set_option autoImplicit false
open Real Polynomial MeasureTheory
open scoped SchwartzMap
noncomputable section
namespace RHTower

private theorem atom_monomial (P : ℝ[X]) (N n : ℕ) (x : ℝ) :
    thetaCuspPolynomialAtom (X ^ N * P) n x =
      ((n : ℝ) * Real.exp x) ^ N * thetaCuspPolynomialAtom P n x := by
  simp only [thetaCuspPolynomialAtom, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X]
  ring

/-- A monomial upgrade of the existing Gaussian bound admits any real exponential rate. -/
theorem exp_mul_abs_thetaCuspPolynomialAtom_le_at_rate
    (P : ℝ[X]) (N : ℕ) {A x : ℝ} (hA : A ≤ (N : ℝ) + 1)
    (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
    Real.exp (A * x) * |thetaCuspPolynomialAtom P n x| ≤
      thetaCuspGaussianConstant (X ^ N * P) *
        Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : Real.exp x ≤ (n : ℝ) * Real.exp x := by
    nlinarith [Real.exp_pos x]
  have hweight : Real.exp (A * x) ≤
      Real.exp x * ((n : ℝ) * Real.exp x) ^ N := by
    calc
      Real.exp (A * x) ≤ Real.exp (((N : ℝ) + 1) * x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA hx)
      _ = Real.exp x * (Real.exp x) ^ N := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp x * ((n : ℝ) * Real.exp x) ^ N := by
        gcongr
  have hatom := exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos (X ^ N * P) hx hn
  rw [atom_monomial, abs_mul, abs_of_nonneg
    (pow_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) N)] at hatom
  calc
    _ ≤ (Real.exp x * ((n : ℝ) * Real.exp x) ^ N) *
        |thetaCuspPolynomialAtom P n x| :=
      mul_le_mul_of_nonneg_right hweight (abs_nonneg _)
    _ ≤ _ := by simpa only [mul_assoc] using hatom

/-- Every theta derivative has a bound at every real exponential rate on the positive ray. -/
theorem thetaCuspFullSource_derivative_exp_bound_pos (A : ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x →
      Real.exp (A * x) * |iteratedDeriv k thetaCuspFullSource x| ≤ C := by
  obtain ⟨N, hN⟩ := exists_nat_gt A
  let P := thetaCuspLogDerivativePolynomial k
  refine ⟨thetaCuspGaussianConstant (X ^ N * P) *
    ∑' n : ℕ, Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2), ?_⟩
  intro x hx
  have ha : Summable (fun n : ℕ => thetaCuspPolynomialAtom P n x) := by
    have h := summable_iteratedDeriv_thetaCuspSourceTerm k x
    simpa only [P, iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom] using h
  have hn (n : ℕ) :
      Real.exp (A * x) * |thetaCuspPolynomialAtom P n x| ≤
        thetaCuspGaussianConstant (X ^ N * P) *
          Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [show thetaCuspPolynomialAtom P 0 x = 0 from
        thetaCuspPolynomialAtom_derivative_zero k x]
      simp only [abs_zero, mul_zero]
      exact mul_nonneg (thetaCuspGaussianConstant_nonneg _) (Real.exp_pos _).le
    · exact exp_mul_abs_thetaCuspPolynomialAtom_le_at_rate P N (by linarith) hx hn
  have ht := (ha.norm.mul_left (Real.exp (A * x))).tsum_le_tsum hn
    (summable_thetaCuspHalfGaussian.mul_left (thetaCuspGaussianConstant (X ^ N * P)))
  rw [tsum_mul_left, tsum_mul_left] at ht
  rw [iteratedDeriv_thetaCuspFullSource, thetaCuspFullDerivative]
  simp_rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom]
  exact le_trans
    (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm ha.norm) (Real.exp_pos _).le) ht

/-- The reflection law upgrades every derivative bound to the whole original source. -/
theorem thetaCuspFullSource_derivative_exp_bound (A : ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ,
      Real.exp (A * |x|) * |iteratedDeriv k thetaCuspFullSource x| ≤ C := by
  obtain ⟨C, hC⟩ := thetaCuspFullSource_derivative_exp_bound_pos A k
  refine ⟨C, fun x => ?_⟩
  rcases le_or_gt 0 x with hx | hx
  · simpa only [abs_of_nonneg hx] using hC x hx
  · have h := hC (-x) (by linarith)
    rw [abs_iteratedDeriv_thetaCuspFullSource_neg] at h
    simpa only [abs_of_neg hx] using h

/-- Strong Meyer admission of the original theta Schwartz source, including every derivative. -/
theorem thetaCuspSchwartz_mem_deningerExpSchwartz :
    thetaCuspSchwartz ∈ DeningerExpSchwartz := by
  intro A k
  obtain ⟨C, hC⟩ := thetaCuspFullSource_derivative_exp_bound A k
  refine ⟨C, fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change Real.exp (A * |x|) *
    ‖iteratedDeriv k (fun y : ℝ => (thetaCuspFullSource y : ℂ)) x‖ ≤ C
  rw [show (fun y : ℝ => (thetaCuspFullSource y : ℂ)) =
      (fun y : ℝ => thetaCuspFullSource y • (1 : ℂ)) by
        funext y
        simp]
  rw [iteratedDeriv_smul_const (contDiff_thetaCuspFullSource.contDiffAt.of_le
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))) (1 : ℂ)]
  simpa only [norm_smul, norm_one, mul_one, Real.norm_eq_abs] using hC x

/-- Polynomially bounded smooth multipliers preserve every exponential source weight. -/
theorem deningerExpSchwartz_smulLeftCLM_mem
    {f : SchwartzMap ℝ ℂ} (hf : f ∈ DeningerExpSchwartz)
    {u : ℝ → ℂ} (hu : u.HasTemperateGrowth) :
    SchwartzMap.smulLeftCLM ℂ u f ∈ DeningerExpSchwartz := by
  have heq : (SchwartzMap.smulLeftCLM ℂ u f : ℝ → ℂ) =
      fun x : ℝ => u x * f x := by
    funext x
    rw [SchwartzMap.smulLeftCLM_apply_apply hu]
    rfl
  intro A n
  rw [heq]
  obtain ⟨K, B, hB, huB⟩ := hu.norm_iteratedFDeriv_le_uniform n
  choose C hC using fun j : ℕ => hf (A + K) j
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B * max (C (n - i)) 0,
    fun x => ?_⟩
  have hw : Real.exp (A * |x|) * (1 + ‖x‖) ^ K ≤
      Real.exp ((A + K) * |x|) := by
    have hpow : (1 + ‖x‖) ^ K ≤ Real.exp ((K : ℝ) * |x|) := by
      rw [Real.exp_nat_mul]
      apply pow_le_pow_left₀ (by positivity)
      simpa only [Real.norm_eq_abs, add_comm] using Real.add_one_le_exp |x|
    calc
      _ ≤ Real.exp (A * |x|) * Real.exp ((K : ℝ) * |x|) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hl := norm_iteratedFDeriv_mul_le hu.1 f.smooth' x (n := n) ENat.LEInfty.out
  refine le_trans (mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le) ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hc : Real.exp ((A + K) * |x|) *
      ‖iteratedFDeriv ℝ (n - i) (f : ℝ → ℂ) x‖ ≤ max (C (n - i)) 0 :=
    (hC (n - i) x).trans (le_max_left _ _)
  have hmid : Real.exp (A * |x|) * (1 + ‖x‖) ^ K *
      ‖iteratedFDeriv ℝ (n - i) (f : ℝ → ℂ) x‖ ≤ max (C (n - i)) 0 :=
    (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans hc
  calc
    _ ≤ Real.exp (A * |x|) *
        ((n.choose i : ℝ) * (B * (1 + ‖x‖) ^ K) *
          ‖iteratedFDeriv ℝ (n - i) (f : ℝ → ℂ) x‖) := by
      gcongr
      · exact huB i hi' x
      · exact le_rfl
    _ = (n.choose i : ℝ) * B * (Real.exp (A * |x|) * (1 + ‖x‖) ^ K *
          ‖iteratedFDeriv ℝ (n - i) (f : ℝ → ℂ) x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmid (mul_nonneg (by positivity) hB)

/-- The exact half-density tilt used in the native collar has all-order Meyer admission. -/
theorem thetaCuspHalfTilt_mem_deningerExpSchwartz :
    thetaCuspTiltedSchwartz (1 / 2) (by norm_num) ∈ DeningerExpSchwartz := by
  have he : thetaCuspTiltedSchwartz (1 / 2) (by norm_num) =
      (deningerExpMul (1 / 2) ⟨thetaCuspSchwartz,
        thetaCuspSchwartz_mem_deningerExpSchwartz⟩ : SchwartzMap ℝ ℂ) := by
    ext x
    rw [thetaCuspTiltedSchwartz_apply, deningerExpMul_apply, thetaCuspSchwartz_apply]
    push_cast
    rfl
  rw [he]
  exact (deningerExpMul (1 / 2) ⟨thetaCuspSchwartz,
    thetaCuspSchwartz_mem_deningerExpSchwartz⟩).property

/-- Strong admission of the original native collar, retaining every internal jet and depth. -/
theorem mobiusThetaNativeCollarSource_mem_deningerExpSchwartz (k : ℕ) (m : ℕ+) :
    mobiusThetaNativeCollarSource k m ∈ DeningerExpSchwartz := by
  let f : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ
    (fun u : ℝ => (-Complex.I * (u : ℂ)) ^ k)
    (thetaCuspTiltedSchwartz (1 / 2) (by norm_num))
  have hf : f ∈ DeningerExpSchwartz :=
    deningerExpSchwartz_smulLeftCLM_mem thetaCuspHalfTilt_mem_deningerExpSchwartz (by fun_prop)
  have hm : -(m : ℝ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast m.ne_zero)
  have hd := schwartzDilate_mem_deningerExpSchwartz hf hm
  convert hd using 1
  ext t
  rfl

/-- The original source in the existing Meyer topology; no source-membership premise remains. -/
def mobiusThetaNativeMeyerSource (k : ℕ) (m : ℕ+) : DeningerMeyerSource :=
  DeningerMeyerSource.toSource.symm ⟨mobiusThetaNativeCollarSource k m,
    mobiusThetaNativeCollarSource_mem_deningerExpSchwartz k m⟩

@[simp] theorem mobiusThetaNativeMeyerSource_toSource (k : ℕ) (m : ℕ+) :
    (DeningerMeyerSource.toSource (mobiusThetaNativeMeyerSource k m) : SchwartzMap ℝ ℂ) =
      mobiusThetaNativeCollarSource k m := rfl

/-- The original arithmetic source converges absolutely at every positive native depth. -/
theorem summable_norm_mobiusThetaInternalJetRawHeadSource_all_depths
    (k p : ℕ) (m : ℕ+) (x : ℝ) :
    Summable (fun j : ℕ => ‖mobiusThetaInternalJetRawHeadSource k (p + j) m x‖) := by
  have hs := (deningerMobiusRay_summable
    (mobiusThetaNativeCollarSource_mem_deningerExpSchwartz k m)
    (Real.exp_pos (-x / (m : ℝ)))).norm
  simp_rw [mobiusThetaNativeCollarSource_mobiusTerm, norm_mul] at hs
  have he : ‖(Real.exp (x / 2) : ℂ)‖ ≠ 0 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_pos _).ne'
  have hr := (summable_mul_left_iff he).mp hs
  simpa only [Nat.add_comm] using (_root_.summable_nat_add_iff p).2 hr

/-- The finite prefix and complete tail reconstruct the same native source at every depth. -/
theorem mobiusThetaNativeCollarSource_preimage_at_anchor_all_depths
    (k p : ℕ) (m : ℕ+) (x : ℝ) :
    deningerMobiusPreimage (mobiusThetaNativeCollarSource k m)
        (Real.exp (-x / (m : ℝ))) =
      (Real.exp (x / 2) : ℂ) *
        ((∑ n ∈ Finset.range p, mobiusThetaInternalJetRawHeadSource k n m x) +
          mobiusThetaInternalJetRawResidualSource k p m x) := by
  have hs : Summable (fun n : ℕ => mobiusThetaInternalJetRawHeadSource k n m x) := by
    simpa only [Nat.zero_add] using
      (summable_norm_mobiusThetaInternalJetRawHeadSource_all_depths k 0 m x).of_norm
  rw [mobiusThetaNativeCollarSource_preimage]
  congr 1
  simpa only [mobiusThetaInternalJetRawResidualSource, Nat.zero_add, Nat.add_zero, Nat.add_comm]
    using (hs.sum_add_tsum_nat_add p).symm

end RHTower
