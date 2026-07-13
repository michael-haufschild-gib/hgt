import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.RHTower.L2MellinUnitary

open Complex MeasureTheory
open scoped BigOperators

noncomputable section
namespace RHTower

def squarefreeMobiusMass (sigma : ℝ) (n : ℕ) : ℝ :=
  if Squarefree n then (n : ℝ) ^ (-sigma) else 0

theorem squarefreeMobiusMass_nonneg (sigma : ℝ) (n : ℕ) :
    0 ≤ squarefreeMobiusMass sigma n := by
  simp only [squarefreeMobiusMass]
  split_ifs <;> positivity

theorem summable_squarefreeMobiusMass {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (squarefreeMobiusMass sigma) := by
  apply Summable.of_nonneg_of_le (squarefreeMobiusMass_nonneg sigma)
    (fun n => ?_) (Real.summable_nat_rpow.mpr (by linarith : -sigma < -1))
  rw [squarefreeMobiusMass]
  split_ifs
  · exact le_rfl
  · positivity

def squarefreeMobiusTotal (sigma : ℝ) : ℝ :=
  ∑' n : ℕ, squarefreeMobiusMass sigma n

theorem ofReal_squarefreeMobiusMass_eq (sigma : ℝ) (n : ℕ) :
    (squarefreeMobiusMass sigma n : ℂ) =
      if Squarefree n then 1 / (n : ℂ) ^ (sigma : ℂ) else 0 := by
  rw [squarefreeMobiusMass]
  split_ifs with hn
  · have hn0 : n ≠ 0 := by
      intro h
      subst n
      exact not_squarefree_zero hn
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    rw [show ((-sigma : ℝ) : ℂ) = -(sigma : ℂ) by norm_cast]
    rw [Complex.cpow_neg, one_div]
    congr 2
  · norm_num

theorem squarefreeMobiusTotal_eq_zetaRatio_re {sigma : ℝ} (hsigma : 1 < sigma) :
    squarefreeMobiusTotal sigma =
      (riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ))).re := by
  have hmap := Complex.ofRealCLM.map_tsum (summable_squarefreeMobiusMass hsigma)
  simp only [Complex.ofRealCLM_apply] at hmap
  have hkernel :
      (∑' n : ℕ, (squarefreeMobiusMass sigma n : ℂ)) =
        ∑' n : ℕ, (if Squarefree n then 1 / (n : ℂ) ^ (sigma : ℂ) else 0) := by
    apply tsum_congr
    exact ofReal_squarefreeMobiusMass_eq sigma
  have hzeta := tsum_squarefree_cpow
    (s := (sigma : ℂ)) (by simpa using hsigma)
  have hcomplex : (squarefreeMobiusTotal sigma : ℂ) =
      riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ)) := by
    calc
      (squarefreeMobiusTotal sigma : ℂ) =
          ∑' n : ℕ, (squarefreeMobiusMass sigma n : ℂ) := by
        rw [squarefreeMobiusTotal]
        exact hmap
      _ = ∑' n : ℕ,
          (if Squarefree n then 1 / (n : ℂ) ^ (sigma : ℂ) else 0) := hkernel
      _ = riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ)) := hzeta
  exact_mod_cast congrArg Complex.re hcomplex

theorem squarefreeMobiusTotal_pos {sigma : ℝ} (hsigma : 1 < sigma) :
    0 < squarefreeMobiusTotal sigma := by
  apply (summable_squarefreeMobiusMass hsigma).tsum_pos
    (squarefreeMobiusMass_nonneg sigma) 1
  simp [squarefreeMobiusMass]

def squarefreeMobiusProbability (sigma : ℝ) (n : ℕ) : ℝ :=
  squarefreeMobiusMass sigma n / squarefreeMobiusTotal sigma

theorem squarefreeMobiusProbability_nonneg {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    0 ≤ squarefreeMobiusProbability sigma n := by
  exact div_nonneg (squarefreeMobiusMass_nonneg sigma n)
    (squarefreeMobiusTotal_pos hsigma).le

theorem summable_squarefreeMobiusProbability {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (squarefreeMobiusProbability sigma) :=
  (summable_squarefreeMobiusMass hsigma).div_const _

theorem tsum_squarefreeMobiusProbability {sigma : ℝ} (hsigma : 1 < sigma) :
    ∑' n : ℕ, squarefreeMobiusProbability sigma n = 1 := by
  rw [show (∑' n : ℕ, squarefreeMobiusProbability sigma n) =
      (∑' n : ℕ, squarefreeMobiusMass sigma n) / squarefreeMobiusTotal sigma by
    exact tsum_div_const]
  rw [show (∑' n : ℕ, squarefreeMobiusMass sigma n) =
      squarefreeMobiusTotal sigma by rfl]
  exact div_self (ne_of_gt (squarefreeMobiusTotal_pos hsigma))

def infiniteMobiusSignedWeight (sigma : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
    Real.sqrt (squarefreeMobiusProbability sigma n)

theorem norm_infiniteMobiusSignedWeight_sq {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    ‖infiniteMobiusSignedWeight sigma n‖ ^ 2 =
      squarefreeMobiusProbability sigma n := by
  rw [infiniteMobiusSignedWeight, norm_mul, mul_pow]
  by_cases hn : Squarefree n
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hn]
    have hnorm : ‖((((-1 : ℤ) ^ ArithmeticFunction.cardFactors n : ℤ) : ℂ))‖ = 1 := by
      rw [Complex.norm_intCast]
      simp
    rw [hnorm, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
    exact squarefreeMobiusProbability_nonneg hsigma n
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
    norm_num [squarefreeMobiusProbability, squarefreeMobiusMass, hn]

theorem summable_norm_sq_infiniteMobiusSignedWeight {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n => ‖infiniteMobiusSignedWeight sigma n‖ ^ 2) := by
  simpa only [norm_infiniteMobiusSignedWeight_sq hsigma] using
    summable_squarefreeMobiusProbability hsigma

def infiniteMobiusSignedWeightLp (sigma : ℝ) (hsigma : 1 < sigma) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨infiniteMobiusSignedWeight sigma,
    HilbertSchmidt.memℓp_of_sq (summable_norm_sq_infiniteMobiusSignedWeight hsigma)⟩

theorem norm_infiniteMobiusSignedWeightLp_sq {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖infiniteMobiusSignedWeightLp sigma hsigma‖ ^ 2 = 1 := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  simpa only [infiniteMobiusSignedWeightLp,
    norm_infiniteMobiusSignedWeight_sq hsigma] using
    tsum_squarefreeMobiusProbability hsigma

theorem norm_infiniteMobiusSignedWeightLp {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖infiniteMobiusSignedWeightLp sigma hsigma‖ = 1 := by
  nlinarith [norm_infiniteMobiusSignedWeightLp_sq hsigma,
    norm_nonneg (infiniteMobiusSignedWeightLp sigma hsigma)]

def infiniteSignedChannelSynthesis {ι : Type*}
    (w : lp (fun _ : ι => ℂ) 2) : lp (fun _ : ι => ℂ) 2 →L[ℂ] ℂ :=
  innerSL ℂ w

def infiniteSignedChannelAnalysis {ι : Type*}
    (w : lp (fun _ : ι => ℂ) 2) : ℂ →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) w

def infiniteSignedChannelProjection {ι : Type*}
    (w : lp (fun _ : ι => ℂ) 2) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  (infiniteSignedChannelAnalysis w).comp (infiniteSignedChannelSynthesis w)

theorem infiniteSignedChannelSynthesis_analysis {ι : Type*}
    {w : lp (fun _ : ι => ℂ) 2} (hw : ‖w‖ = 1) (c : ℂ) :
    infiniteSignedChannelSynthesis w (infiniteSignedChannelAnalysis w c) = c := by
  rw [infiniteSignedChannelSynthesis, infiniteSignedChannelAnalysis,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hw]
  norm_num

theorem infiniteSignedChannelProjection_idempotent {ι : Type*}
    {w : lp (fun _ : ι => ℂ) 2} (hw : ‖w‖ = 1) :
    (infiniteSignedChannelProjection w).comp (infiniteSignedChannelProjection w) =
      infiniteSignedChannelProjection w := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [infiniteSignedChannelProjection, ContinuousLinearMap.comp_apply]
  rw [infiniteSignedChannelSynthesis_analysis hw]

theorem infiniteSignedChannelSynthesis_projection {ι : Type*}
    {w : lp (fun _ : ι => ℂ) 2} (hw : ‖w‖ = 1)
    (f : lp (fun _ : ι => ℂ) 2) :
    infiniteSignedChannelSynthesis w (infiniteSignedChannelProjection w f) =
      infiniteSignedChannelSynthesis w f := by
  simp only [infiniteSignedChannelProjection, ContinuousLinearMap.comp_apply]
  rw [infiniteSignedChannelSynthesis_analysis hw]

theorem infiniteSignedChannelProjection_analysis {ι : Type*}
    {w : lp (fun _ : ι => ℂ) 2} (hw : ‖w‖ = 1) (c : ℂ) :
    infiniteSignedChannelProjection w (infiniteSignedChannelAnalysis w c) =
      infiniteSignedChannelAnalysis w c := by
  simp only [infiniteSignedChannelProjection, ContinuousLinearMap.comp_apply]
  rw [infiniteSignedChannelSynthesis_analysis hw]

theorem norm_infiniteSignedChannelSynthesis_le {ι : Type*}
    {w : lp (fun _ : ι => ℂ) 2} (hw : ‖w‖ = 1)
    (f : lp (fun _ : ι => ℂ) 2) :
    ‖infiniteSignedChannelSynthesis w f‖ ≤ ‖f‖ := by
  rw [infiniteSignedChannelSynthesis, innerSL_apply_apply]
  calc
    ‖inner ℂ w f‖ ≤ ‖w‖ * ‖f‖ := norm_inner_le_norm _ _
    _ = ‖f‖ := by rw [hw, one_mul]

theorem norm_infiniteSignedChannelProjection_le {ι : Type*}
    {w : lp (fun _ : ι => ℂ) 2} (hw : ‖w‖ = 1)
    (f : lp (fun _ : ι => ℂ) 2) :
    ‖infiniteSignedChannelProjection w f‖ ≤ ‖f‖ := by
  rw [infiniteSignedChannelProjection, ContinuousLinearMap.comp_apply,
    infiniteSignedChannelAnalysis, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, norm_smul, hw, mul_one]
  exact norm_infiniteSignedChannelSynthesis_le hw f

theorem infiniteSignedChannel_incidence_factorization {ι : Type*}
    {w : lp (fun _ : ι => ℂ) 2} (hw : ‖w‖ = 1)
    (Z : ℂ) (f : lp (fun _ : ι => ℂ) 2) :
    Z * infiniteSignedChannelSynthesis w f =
      Z * infiniteSignedChannelSynthesis w (infiniteSignedChannelProjection w f) := by
  rw [infiniteSignedChannelSynthesis_projection hw]

theorem infiniteMobiusSignedChannel_coisometry {sigma : ℝ} (hsigma : 1 < sigma) (c : ℂ) :
    infiniteSignedChannelSynthesis (infiniteMobiusSignedWeightLp sigma hsigma)
        (infiniteSignedChannelAnalysis (infiniteMobiusSignedWeightLp sigma hsigma) c) = c :=
  infiniteSignedChannelSynthesis_analysis (norm_infiniteMobiusSignedWeightLp hsigma) c

def signedMobiusProbability (sigma : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) * squarefreeMobiusProbability sigma n

theorem norm_signedMobiusProbability {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    ‖signedMobiusProbability sigma n‖ = squarefreeMobiusProbability sigma n := by
  rw [signedMobiusProbability, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (squarefreeMobiusProbability_nonneg hsigma n)]
  by_cases hn : Squarefree n
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hn,
      Complex.norm_intCast]
    simp
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
    norm_num [squarefreeMobiusProbability, squarefreeMobiusMass, hn]

def infiniteMobiusShiftTerm (sigma : ℝ) (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  signedMobiusProbability sigma n •
    MellinL2.additiveTranslationUnitary (-Real.log n) f

theorem norm_infiniteMobiusShiftTerm {sigma : ℝ} (hsigma : 1 < sigma)
    (n : ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖infiniteMobiusShiftTerm sigma n f‖ =
      squarefreeMobiusProbability sigma n * ‖f‖ := by
  rw [infiniteMobiusShiftTerm, norm_smul,
    LinearIsometryEquiv.norm_map,
    norm_signedMobiusProbability hsigma]

theorem summable_infiniteMobiusShiftTerm {sigma : ℝ} (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Summable (fun n => infiniteMobiusShiftTerm sigma n f) := by
  apply Summable.of_norm
  simpa only [norm_infiniteMobiusShiftTerm hsigma] using
    (summable_squarefreeMobiusProbability hsigma).mul_right ‖f‖

/-- The all-prime signed right-shift average on logarithmic `L²`. -/
def infiniteMobiusShiftAverage (sigma : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ∑' n : ℕ, infiniteMobiusShiftTerm sigma n f

/-- The actual all-prime shift average is contractive on logarithmic `L²`. -/
theorem norm_infiniteMobiusShiftAverage_le {sigma : ℝ} (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖infiniteMobiusShiftAverage sigma f‖ ≤ ‖f‖ := by
  have hnorm : Summable (fun n => ‖infiniteMobiusShiftTerm sigma n f‖) := by
    simpa only [norm_infiniteMobiusShiftTerm hsigma] using
      (summable_squarefreeMobiusProbability hsigma).mul_right ‖f‖
  calc
    ‖infiniteMobiusShiftAverage sigma f‖ ≤
        ∑' n : ℕ, ‖infiniteMobiusShiftTerm sigma n f‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ∑' n : ℕ, squarefreeMobiusProbability sigma n * ‖f‖ := by
      apply tsum_congr
      intro n
      exact norm_infiniteMobiusShiftTerm hsigma n f
    _ = (∑' n : ℕ, squarefreeMobiusProbability sigma n) * ‖f‖ :=
      tsum_mul_right
    _ = ‖f‖ := by rw [tsum_squarefreeMobiusProbability hsigma, one_mul]

end RHTower
