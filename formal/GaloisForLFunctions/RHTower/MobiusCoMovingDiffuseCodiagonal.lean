import GaloisForLFunctions.RHTower.InfiniteMobiusShiftAnalysis
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardJuliaTransport
import GaloisForLFunctions.RHTower.MobiusChannelCriticalMassEscape
import GaloisForLFunctions.HTGeometry.HilbertSchmidt

open Complex MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section
namespace RHTower

def coMovingTensorLift
    (x : lp (fun _ : ℕ => ℂ) 2)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : InfiniteMobiusShiftChannel :=
  ⟨fun n => x n • MellinL2.additiveTranslationUnitary (-Real.log n) f,
    (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).2 (by
      have hx := (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_smul,
        LinearIsometryEquiv.norm_map, mul_pow] using
        hx.mul_right (‖f‖ ^ 2))⟩

@[simp] theorem coMovingTensorLift_apply
    (x : lp (fun _ : ℕ => ℂ) 2)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) :
    coMovingTensorLift x f n =
      x n • MellinL2.additiveTranslationUnitary (-Real.log n) f := rfl

theorem norm_coMovingTensorLift_sq
    (x : lp (fun _ : ℕ => ℂ) 2)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖coMovingTensorLift x f‖ ^ 2 = ‖x‖ ^ 2 * ‖f‖ ^ 2 := by
  have hnorm := lp.norm_rpow_eq_tsum
    (p := (2 : ENNReal)) (by norm_num : 0 < (2 : ENNReal).toReal)
    (coMovingTensorLift x f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hnorm
  rw [hnorm, HilbertSchmidt.lp_norm_sq_eq]
  simp only [coMovingTensorLift_apply, norm_smul,
    LinearIsometryEquiv.norm_map, mul_pow]
  rw [tsum_mul_right]

theorem norm_coMovingTensorLift
    (x : lp (fun _ : ℕ => ℂ) 2)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖coMovingTensorLift x f‖ = ‖x‖ * ‖f‖ := by
  rw [← (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))]
  simpa only [mul_pow] using norm_coMovingTensorLift_sq x f

theorem inner_coMovingTensorLift
    (x y : lp (fun _ : ℕ => ℂ) 2)
    (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ (coMovingTensorLift x f) (coMovingTensorLift y g) =
      inner ℂ x y * inner ℂ f g := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [coMovingTensorLift_apply, inner_smul_left, inner_smul_right,
    LinearIsometryEquiv.inner_map_map, RCLike.inner_apply, starRingEnd_apply]
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  ring

def coMovingAnalysisLinearMap
    (x : lp (fun _ : ℕ => ℂ) 2) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] InfiniteMobiusShiftChannel where
  toFun := coMovingTensorLift x
  map_add' f g := by
    apply lp.ext
    funext n
    change x n • MellinL2.additiveTranslationUnitary (-Real.log n) (f + g) =
      x n • MellinL2.additiveTranslationUnitary (-Real.log n) f +
        x n • MellinL2.additiveTranslationUnitary (-Real.log n) g
    simp
  map_smul' c f := by
    apply lp.ext
    funext n
    simp only [coMovingTensorLift_apply, map_smul, lp.coeFn_smul,
      Pi.smul_apply, RingHom.id_apply]
    rw [smul_smul, mul_comm, ← smul_smul]

def coMovingAnalysis
    (x : lp (fun _ : ℕ => ℂ) 2) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] InfiniteMobiusShiftChannel :=
  (coMovingAnalysisLinearMap x).mkContinuous ‖x‖
    (fun f => (norm_coMovingTensorLift x f).le)

theorem norm_coMovingAnalysis_le
    (x : lp (fun _ : ℕ => ℂ) 2) :
    ‖coMovingAnalysis x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
  intro f
  exact (norm_coMovingTensorLift x f).le

def coMovingSynthesis
    (x : lp (fun _ : ℕ => ℂ) 2) :
    InfiniteMobiusShiftChannel →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  ContinuousLinearMap.adjoint (coMovingAnalysis x)

theorem coMovingSynthesis_tensorLift
    (x y : lp (fun _ : ℕ => ℂ) 2)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    coMovingSynthesis x (coMovingTensorLift y f) =
      inner ℂ x y • f := by
  apply ext_inner_left ℂ
  intro g
  rw [coMovingSynthesis, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (coMovingTensorLift x g) (coMovingTensorLift y f) =
    inner ℂ g (inner ℂ x y • f)
  rw [inner_coMovingTensorLift, inner_smul_right]

theorem coMovingSynthesis_analysis
    {x : lp (fun _ : ℕ => ℂ) 2} (hx : ‖x‖ = 1)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    coMovingSynthesis x (coMovingAnalysis x f) = f := by
  have hnorm : ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      ‖coMovingAnalysis x f‖ = ‖f‖ := by
    intro f
    simpa [coMovingAnalysis, hx] using! norm_coMovingTensorLift x f
  let U : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] InfiniteMobiusShiftChannel :=
    { (coMovingAnalysis x).toLinearMap with norm_map' := hnorm }
  have hcomp := U.adjoint_comp_self
  have hcomp' :
      (ContinuousLinearMap.adjoint (coMovingAnalysis x)) ∘L
          coMovingAnalysis x = 1 := by
    simpa only [U] using! hcomp
  exact congrFun (congrArg DFunLike.coe hcomp') f

theorem norm_coMovingSynthesis_le
    {x : lp (fun _ : ℕ => ℂ) 2} (hx : ‖x‖ = 1)
    (y : InfiniteMobiusShiftChannel) :
    ‖coMovingSynthesis x y‖ ≤ ‖y‖ := by
  have hnorm : ‖coMovingSynthesis x‖ = ‖coMovingAnalysis x‖ :=
    (ContinuousLinearMap.adjoint : _ ≃ₗᵢ⋆[ℂ] _).norm_map _
  calc
    ‖coMovingSynthesis x y‖ ≤ ‖coMovingSynthesis x‖ * ‖y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖coMovingAnalysis x‖ * ‖y‖ := by rw [hnorm]
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right
      (by simpa [hx] using norm_coMovingAnalysis_le x) (norm_nonneg y)
    _ = ‖y‖ := one_mul _

def infiniteMobiusCriticalDampedFisherTangentWeight
    (sigma u : ℝ) (n : ℕ) : ℂ :=
  (Real.exp (-(u * (sigma - 1) * Real.log n)) : ℂ) *
    infiniteMobiusCriticalFisherTangentWeight sigma n

private theorem summable_norm_sq_infiniteMobiusCriticalDampedFisherTangentWeight
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalDampedFisherTangentWeight sigma u n‖ ^ 2) := by
  have hsum := (lp.memℓp
    (infiniteMobiusCriticalFisherTangentLp sigma hsigma)).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hsum
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_ hsum
  intro n
  rw [infiniteMobiusCriticalDampedFisherTangentWeight, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hexp : Real.exp (-(u * (sigma - 1) * Real.log n)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr
      (mul_nonneg (mul_nonneg hu (sub_nonneg.mpr hsigma.le)) hlog)
  have hsq : Real.exp (-(u * (sigma - 1) * Real.log n)) ^ 2 ≤ 1 := by
    nlinarith [Real.exp_pos (-(u * (sigma - 1) * Real.log n))]
  change Real.exp (-(u * (sigma - 1) * Real.log n)) ^ 2 *
      ‖infiniteMobiusCriticalFisherTangentWeight sigma n‖ ^ 2 ≤
    ‖infiniteMobiusCriticalFisherTangentWeight sigma n‖ ^ 2
  exact mul_le_of_le_one_left (sq_nonneg _) hsq

def infiniteMobiusCriticalDampedFisherTangentLp
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨infiniteMobiusCriticalDampedFisherTangentWeight sigma u,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_infiniteMobiusCriticalDampedFisherTangentWeight hsigma hu)⟩

theorem inner_signed_dampedFisher_eq_fisher_dampedSigned
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ (infiniteMobiusSignedWeightLp sigma hsigma)
        (infiniteMobiusCriticalDampedFisherTangentLp sigma u hsigma hu) =
      inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
        (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [infiniteMobiusSignedWeightLp,
    infiniteMobiusCriticalDampedFisherTangentLp,
    infiniteMobiusCriticalFisherTangentLp,
    infiniteMobiusCriticalDampedSignedWeightLp, RCLike.inner_apply]
  rw [infiniteMobiusCriticalDampedFisherTangentWeight,
    infiniteMobiusCriticalDampedSignedWeight,
    infiniteMobiusCriticalFisherTangentWeight]
  simp only [map_mul, conj_ofReal]
  ring

theorem mobiusCoMovingSynthesis_dampedFisher_eq_score_smul
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    coMovingSynthesis (infiniteMobiusSignedWeightLp sigma hsigma)
        (coMovingTensorLift
          (infiniteMobiusCriticalDampedFisherTangentLp sigma u hsigma hu) f) =
      GaloisForLFunctions.squarefreeFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) • f := by
  rw [coMovingSynthesis_tensorLift,
    inner_signed_dampedFisher_eq_fisher_dampedSigned hsigma hu,
    inner_fisherTangent_damped_eq_squarefreeFisherScore hsigma hu]

theorem mobiusCoMovingSynthesis_contracts
    {sigma : ℝ} (hsigma : 1 < sigma)
    (y : InfiniteMobiusShiftChannel) :
    ‖coMovingSynthesis (infiniteMobiusSignedWeightLp sigma hsigma) y‖ ≤ ‖y‖ :=
  norm_coMovingSynthesis_le (norm_infiniteMobiusSignedWeightLp hsigma) y

theorem squarefreeMobiusMass_le_one
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    squarefreeMobiusMass sigma n ≤ 1 := by
  rw [squarefreeMobiusMass]
  split_ifs with hn
  · have hn0 : n ≠ 0 := by
      intro h
      subst n
      exact not_squarefree_zero hn
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)
      (by linarith)
  · norm_num

theorem squarefreeMobiusProbability_le_invTotal
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    squarefreeMobiusProbability sigma n ≤
      (squarefreeMobiusTotal sigma)⁻¹ := by
  rw [squarefreeMobiusProbability, div_eq_mul_inv]
  exact mul_le_of_le_one_left
    (inv_nonneg.mpr (squarefreeMobiusTotal_pos hsigma).le)
    (squarefreeMobiusMass_le_one hsigma n)

def infiniteMobiusCollisionSourceWeight
    (sigma : ℝ) (n : ℕ) : ℂ :=
  (squarefreeMobiusProbability sigma n : ℂ) *
    infiniteMobiusSignedWeight sigma n

private theorem norm_infiniteMobiusCollisionSourceWeight_sq
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    ‖infiniteMobiusCollisionSourceWeight sigma n‖ ^ 2 =
      squarefreeMobiusProbability sigma n ^ 3 := by
  rw [infiniteMobiusCollisionSourceWeight, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (squarefreeMobiusProbability_nonneg hsigma n),
    norm_infiniteMobiusSignedWeight_sq hsigma]
  ring

private theorem summable_norm_sq_infiniteMobiusCollisionSourceWeight
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ =>
      ‖infiniteMobiusCollisionSourceWeight sigma n‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_
    (summable_squarefreeMobiusProbability hsigma)
  intro n
  rw [norm_infiniteMobiusCollisionSourceWeight_sq hsigma]
  have hp0 := squarefreeMobiusProbability_nonneg hsigma n
  have hp1 : squarefreeMobiusProbability sigma n ≤ 1 := by
    calc
      squarefreeMobiusProbability sigma n ≤
          (squarefreeMobiusTotal sigma)⁻¹ :=
        squarefreeMobiusProbability_le_invTotal hsigma n
      _ ≤ 1 := by
        rw [inv_le_one₀ (squarefreeMobiusTotal_pos hsigma)]
        have hterm : squarefreeMobiusMass sigma 1 = 1 := by
          simp [squarefreeMobiusMass]
        calc
          1 = squarefreeMobiusMass sigma 1 := hterm.symm
          _ ≤ ∑' n, squarefreeMobiusMass sigma n :=
            (summable_squarefreeMobiusMass hsigma).le_tsum 1
              (fun j _ => squarefreeMobiusMass_nonneg sigma j)
          _ = squarefreeMobiusTotal sigma := rfl
  have hp2 : squarefreeMobiusProbability sigma n ^ 2 ≤ 1 ^ 2 :=
    (sq_le_sq₀ hp0 zero_le_one).2 hp1
  calc
    squarefreeMobiusProbability sigma n ^ 3 =
        squarefreeMobiusProbability sigma n ^ 2 *
          squarefreeMobiusProbability sigma n := by ring
    _ ≤ 1 ^ 2 * squarefreeMobiusProbability sigma n :=
      mul_le_mul_of_nonneg_right hp2 hp0
    _ = squarefreeMobiusProbability sigma n := by ring

def infiniteMobiusCollisionSourceLp
    (sigma : ℝ) (hsigma : 1 < sigma) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨infiniteMobiusCollisionSourceWeight sigma,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_infiniteMobiusCollisionSourceWeight hsigma)⟩

theorem norm_infiniteMobiusCollisionSourceLp_le
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖infiniteMobiusCollisionSourceLp sigma hsigma‖ ≤
      (squarefreeMobiusTotal sigma)⁻¹ := by
  have hbound : ∀ n : ℕ,
      ‖infiniteMobiusCollisionSourceWeight sigma n‖ ^ 2 ≤
        (squarefreeMobiusTotal sigma)⁻¹ ^ 2 *
          squarefreeMobiusProbability sigma n := by
    intro n
    rw [norm_infiniteMobiusCollisionSourceWeight_sq hsigma]
    have hp0 := squarefreeMobiusProbability_nonneg hsigma n
    have hp := squarefreeMobiusProbability_le_invTotal hsigma n
    have hi0 : 0 ≤ (squarefreeMobiusTotal sigma)⁻¹ :=
      inv_nonneg.mpr (squarefreeMobiusTotal_pos hsigma).le
    have hp2 :
        squarefreeMobiusProbability sigma n ^ 2 ≤
          (squarefreeMobiusTotal sigma)⁻¹ ^ 2 :=
      (sq_le_sq₀ hp0 hi0).2 hp
    calc
      squarefreeMobiusProbability sigma n ^ 3 =
          squarefreeMobiusProbability sigma n ^ 2 *
            squarefreeMobiusProbability sigma n := by ring
      _ ≤ (squarefreeMobiusTotal sigma)⁻¹ ^ 2 *
          squarefreeMobiusProbability sigma n :=
        mul_le_mul_of_nonneg_right hp2 hp0
  have hsquare :
      ‖infiniteMobiusCollisionSourceLp sigma hsigma‖ ^ 2 ≤
        (squarefreeMobiusTotal sigma)⁻¹ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    calc
      (∑' n : ℕ, ‖infiniteMobiusCollisionSourceWeight sigma n‖ ^ 2) ≤
          ∑' n : ℕ, (squarefreeMobiusTotal sigma)⁻¹ ^ 2 *
            squarefreeMobiusProbability sigma n :=
        Summable.tsum_le_tsum hbound
          (summable_norm_sq_infiniteMobiusCollisionSourceWeight hsigma)
          ((summable_squarefreeMobiusProbability hsigma).mul_left _)
      _ = (squarefreeMobiusTotal sigma)⁻¹ ^ 2 := by
        rw [tsum_mul_left, tsum_squarefreeMobiusProbability hsigma, mul_one]
  exact (sq_le_sq₀ (norm_nonneg _)
    (inv_nonneg.mpr (squarefreeMobiusTotal_pos hsigma).le)).mp hsquare

def mobiusDiffuseCollisionResidual
    (sigma u : ℝ) : ℂ :=
  if hsigma : 1 < sigma then
    if hu : 0 ≤ u then
      inner ℂ (infiniteMobiusCollisionSourceLp sigma hsigma)
        (infiniteMobiusCriticalDampedFisherTangentLp sigma u hsigma hu)
    else 0
  else 0

theorem norm_infiniteMobiusCriticalDampedFisherTangentLp_le
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    ‖infiniteMobiusCriticalDampedFisherTangentLp sigma u hsigma hu‖ ≤
      ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ := by
  have hpoint : ∀ n : ℕ,
      ‖infiniteMobiusCriticalDampedFisherTangentWeight sigma u n‖ ^ 2 ≤
        ‖infiniteMobiusCriticalFisherTangentWeight sigma n‖ ^ 2 := by
    intro n
    rw [infiniteMobiusCriticalDampedFisherTangentWeight, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hexp : Real.exp (-(u * (sigma - 1) * Real.log n)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr
        (mul_nonneg (mul_nonneg hu (sub_nonneg.mpr hsigma.le)) hlog)
    have hsq : Real.exp (-(u * (sigma - 1) * Real.log n)) ^ 2 ≤ 1 := by
      nlinarith [Real.exp_pos (-(u * (sigma - 1) * Real.log n))]
    exact mul_le_of_le_one_left (sq_nonneg _) hsq
  have hright := (lp.memℓp
    (infiniteMobiusCriticalFisherTangentLp sigma hsigma)).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hright
  have hsquare :
      ‖infiniteMobiusCriticalDampedFisherTangentLp sigma u hsigma hu‖ ^ 2 ≤
        ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
    exact Summable.tsum_le_tsum hpoint
      (summable_norm_sq_infiniteMobiusCriticalDampedFisherTangentWeight hsigma hu)
      hright
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

theorem norm_mobiusDiffuseCollisionResidual_le
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    ‖mobiusDiffuseCollisionResidual sigma u‖ ≤
      (squarefreeMobiusTotal sigma)⁻¹ *
        ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ := by
  rw [mobiusDiffuseCollisionResidual, dif_pos hsigma, dif_pos hu]
  calc
    ‖inner ℂ (infiniteMobiusCollisionSourceLp sigma hsigma)
        (infiniteMobiusCriticalDampedFisherTangentLp sigma u hsigma hu)‖ ≤
      ‖infiniteMobiusCollisionSourceLp sigma hsigma‖ *
        ‖infiniteMobiusCriticalDampedFisherTangentLp sigma u hsigma hu‖ :=
      norm_inner_le_norm _ _
    _ ≤ (squarefreeMobiusTotal sigma)⁻¹ *
        ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ :=
      mul_le_mul
        (norm_infiniteMobiusCollisionSourceLp_le hsigma)
        (norm_infiniteMobiusCriticalDampedFisherTangentLp_le hsigma hu)
        (norm_nonneg _)
        (inv_nonneg.mpr (squarefreeMobiusTotal_pos hsigma).le)

def extendedMobiusCriticalFisherTangentNorm (sigma : ℝ) : ℝ :=
  if hsigma : 1 < sigma then
    ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖
  else 0

theorem tendsto_extendedMobiusCriticalFisherTangentNorm :
    Tendsto extendedMobiusCriticalFisherTangentNorm
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 2) := by
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp
    tendsto_norm_infiniteMobiusCriticalFisherTangentLp_sq
  have hfun :
      (fun sigma : ℝ =>
        Real.sqrt
          (if hsigma : 1 < sigma then
            ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2
          else 0)) =
        extendedMobiusCriticalFisherTangentNorm := by
    funext sigma
    rw [extendedMobiusCriticalFisherTangentNorm]
    split_ifs with hsigma
    · exact Real.sqrt_sq (norm_nonneg _)
    · simp
  have hsqrt' :
      Tendsto
        (fun sigma : ℝ =>
          Real.sqrt
            (if hsigma : 1 < sigma then
              ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2
            else 0))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.sqrt 4)) := by
    simpa only [Function.comp_apply] using! hsqrt
  rw [hfun] at hsqrt'
  norm_num at hsqrt'
  exact hsqrt'

theorem tendsto_norm_mobiusDiffuseCollisionResidual_zero
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ => ‖mobiusDiffuseCollisionResidual sigma u‖)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hupper :
      Tendsto
        (fun sigma : ℝ =>
          (squarefreeMobiusTotal sigma)⁻¹ *
            extendedMobiusCriticalFisherTangentNorm sigma)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    simpa using (tendsto_inv_squarefreeMobiusTotal_zero).mul
      tendsto_extendedMobiusCriticalFisherTangentNorm
  refine squeeze_zero'
    (f := fun sigma : ℝ => ‖mobiusDiffuseCollisionResidual sigma u‖)
    (g := fun sigma : ℝ =>
      (squarefreeMobiusTotal sigma)⁻¹ *
        extendedMobiusCriticalFisherTangentNorm sigma) ?_ ?_ hupper
  · exact Filter.Eventually.of_forall (fun sigma => norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    change 1 < sigma at hsigma
    simpa [extendedMobiusCriticalFisherTangentNorm, hsigma] using
      norm_mobiusDiffuseCollisionResidual_le hsigma hu

private theorem tsum_ite_eq_zero_of_eq_sub
    {f : ℕ → ℝ} (hf : Summable f) (n : ℕ) :
    (∑' m : ℕ, if m = n then 0 else f m) = (∑' m : ℕ, f m) - f n := by
  rw [show (fun m : ℕ => if m = n then 0 else f m) =
      fun m => f m - if m = n then f n else 0 by
    funext m
    split_ifs with h
    · subst m
      simp
    · simp]
  rw [Summable.tsum_sub hf (hasSum_ite_eq n (f n)).summable]
  rw [tsum_ite_eq]

/-- Source codiagonal of the joined rank-two Fisher kernel with its literal diagonal removed. -/
def diffuseFisherOffDiagonalCodiagonal
    (p a d : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, ∑' m : ℕ,
    if m = n then 0 else p n * p m * (a n + a m) * d n

/-- Atomic collision term missed by an off-diagonal Fisher codiagonal. -/
def diffuseFisherCollisionResidual
    (p a d : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, p n ^ 2 * a n * d n

/-- **Diffuse Fisher codiagonal law.** For any centered probability score, the complete
off-diagonal codiagonal of the joined rank-two Fisher kernel recovers the damped score up to
exactly twice the atomic collision residual. -/
theorem diffuseFisherOffDiagonalCodiagonal_eq_score_sub_collision
    {p a d : ℕ → ℝ}
    (hp : Summable p)
    (hpa : Summable (fun n => p n * a n))
    (hpad : Summable (fun n => p n * a n * d n))
    (hcollision : Summable (fun n => p n ^ 2 * a n * d n))
    (hp_one : ∑' n, p n = 1)
    (hpa_zero : ∑' n, p n * a n = 0) :
    diffuseFisherOffDiagonalCodiagonal p a d =
      (∑' n, p n * a n * d n) -
        2 * diffuseFisherCollisionResidual p a d := by
  have hinner (n : ℕ) :
      Summable (fun m : ℕ => p n * p m * (a n + a m) * d n) := by
    have h1 := hp.mul_left (p n * a n * d n)
    have h2 := hpa.mul_left (p n * d n)
    convert h1.add h2 using 1
    all_goals try rfl
    funext m
    ring
  have hinnerValue (n : ℕ) :
      (∑' m : ℕ, p n * p m * (a n + a m) * d n) =
        p n * a n * d n := by
    rw [show (fun m : ℕ => p n * p m * (a n + a m) * d n) =
        fun m => (p n * a n * d n) * p m +
          (p n * d n) * (p m * a m) by
      funext m
      ring]
    rw [Summable.tsum_add (hp.mul_left _) (hpa.mul_left _),
      tsum_mul_left, tsum_mul_left, hp_one, hpa_zero]
    ring
  rw [diffuseFisherOffDiagonalCodiagonal]
  simp_rw [tsum_ite_eq_zero_of_eq_sub (hinner _) _, hinnerValue]
  rw [show (fun n : ℕ =>
      p n * a n * d n - p n * p n * (a n + a n) * d n) =
      fun n => p n * a n * d n - 2 * (p n ^ 2 * a n * d n) by
    funext n
    ring]
  rw [Summable.tsum_sub hpad (hcollision.mul_left 2)]
  rw [tsum_mul_left, diffuseFisherCollisionResidual]

def mobiusCriticalFisherCoordinate (sigma : ℝ) (n : ℕ) : ℝ :=
  -2 * (sigma - 1) *
    (Real.log n - squarefreeMobiusLogMoment 1 sigma)

def mobiusCriticalDampingCoordinate (sigma u : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(u * (sigma - 1) * Real.log n))

theorem infiniteMobiusSignedWeight_mul_conj
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    infiniteMobiusSignedWeight sigma n *
        (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) =
      (squarefreeMobiusProbability sigma n : ℂ) := by
  calc
    _ = ((‖infiniteMobiusSignedWeight sigma n‖ : ℂ) ^ 2) :=
      RCLike.mul_conj (infiniteMobiusSignedWeight sigma n)
    _ = _ := by
      rw [← Complex.ofReal_pow,
        norm_infiniteMobiusSignedWeight_sq hsigma]

private theorem inner_signed_fisher_apply_eq
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    inner ℂ (infiniteMobiusSignedWeight sigma n)
        (infiniteMobiusCriticalFisherTangentWeight sigma n) =
      (squarefreeMobiusProbability sigma n *
        mobiusCriticalFisherCoordinate sigma n : ℝ) := by
  simp only [RCLike.inner_apply, infiniteMobiusCriticalFisherTangentWeight,
    mobiusCriticalFisherCoordinate]
  rw [mul_assoc, infiniteMobiusSignedWeight_mul_conj hsigma]
  push_cast
  ring

private theorem inner_signed_dampedFisher_apply_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    inner ℂ (infiniteMobiusSignedWeight sigma n)
        (infiniteMobiusCriticalDampedFisherTangentWeight sigma u n) =
      (squarefreeMobiusProbability sigma n *
        mobiusCriticalFisherCoordinate sigma n *
          mobiusCriticalDampingCoordinate sigma u n : ℝ) := by
  simp only [RCLike.inner_apply,
    infiniteMobiusCriticalDampedFisherTangentWeight,
    infiniteMobiusCriticalFisherTangentWeight,
    mobiusCriticalFisherCoordinate, mobiusCriticalDampingCoordinate]
  calc
    _ = (Real.exp (-(u * (sigma - 1) * Real.log n)) : ℂ) *
        ((-2 * (sigma - 1) *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ) *
        (infiniteMobiusSignedWeight sigma n *
          (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) := by ring
    _ = _ := by
      rw [infiniteMobiusSignedWeight_mul_conj hsigma]
      push_cast
      ring

private theorem inner_collision_dampedFisher_apply_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    inner ℂ (infiniteMobiusCollisionSourceWeight sigma n)
        (infiniteMobiusCriticalDampedFisherTangentWeight sigma u n) =
      (squarefreeMobiusProbability sigma n ^ 2 *
        mobiusCriticalFisherCoordinate sigma n *
          mobiusCriticalDampingCoordinate sigma u n : ℝ) := by
  simp only [RCLike.inner_apply, infiniteMobiusCollisionSourceWeight,
    infiniteMobiusCriticalDampedFisherTangentWeight,
    infiniteMobiusCriticalFisherTangentWeight,
    mobiusCriticalFisherCoordinate, mobiusCriticalDampingCoordinate,
    map_mul, conj_ofReal]
  calc
    _ = (squarefreeMobiusProbability sigma n : ℂ) *
        (Real.exp (-(u * (sigma - 1) * Real.log n)) : ℂ) *
        ((-2 * (sigma - 1) *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ) *
        (infiniteMobiusSignedWeight sigma n *
          (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) := by ring
    _ = _ := by
      rw [infiniteMobiusSignedWeight_mul_conj hsigma]
      push_cast
      ring

theorem summable_mobius_probability_mul_fisherCoordinate
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ =>
      squarefreeMobiusProbability sigma n *
        mobiusCriticalFisherCoordinate sigma n) := by
  apply Complex.summable_ofReal.mp
  exact (lp.summable_inner
    (infiniteMobiusSignedWeightLp sigma hsigma)
    (infiniteMobiusCriticalFisherTangentLp sigma hsigma)).congr
      (fun n => inner_signed_fisher_apply_eq hsigma n)

theorem summable_mobius_probability_mul_fisherCoordinate_mul_damping
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Summable (fun n : ℕ =>
      squarefreeMobiusProbability sigma n *
        mobiusCriticalFisherCoordinate sigma n *
          mobiusCriticalDampingCoordinate sigma u n) := by
  apply Complex.summable_ofReal.mp
  exact (lp.summable_inner
    (infiniteMobiusSignedWeightLp sigma hsigma)
    (infiniteMobiusCriticalDampedFisherTangentLp sigma u hsigma hu)).congr
      (fun n => inner_signed_dampedFisher_apply_eq hsigma n)

theorem summable_mobius_collision
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Summable (fun n : ℕ =>
      squarefreeMobiusProbability sigma n ^ 2 *
        mobiusCriticalFisherCoordinate sigma n *
          mobiusCriticalDampingCoordinate sigma u n) := by
  apply Complex.summable_ofReal.mp
  exact (lp.summable_inner
    (infiniteMobiusCollisionSourceLp sigma hsigma)
    (infiniteMobiusCriticalDampedFisherTangentLp sigma u hsigma hu)).congr
      (fun n => inner_collision_dampedFisher_apply_eq hsigma n)

theorem tsum_mobius_probability_mul_fisherCoordinate_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' n : ℕ, squarefreeMobiusProbability sigma n *
      mobiusCriticalFisherCoordinate sigma n) = 0 := by
  have hcomplex :
      (∑' n : ℕ,
        ((squarefreeMobiusProbability sigma n *
          mobiusCriticalFisherCoordinate sigma n : ℝ) : ℂ)) = 0 := by
    rw [show (fun n : ℕ =>
        ((squarefreeMobiusProbability sigma n *
          mobiusCriticalFisherCoordinate sigma n : ℝ) : ℂ)) =
        fun n => inner ℂ
          (infiniteMobiusSignedWeightLp sigma hsigma n)
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma n) by
      funext n
      exact (inner_signed_fisher_apply_eq hsigma n).symm]
    rw [← lp.inner_eq_tsum
      (infiniteMobiusSignedWeightLp sigma hsigma)
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma)]
    exact inner_infiniteMobiusSignedWeightLp_fisherTangent_eq_zero hsigma
  have hmap := Complex.ofRealCLM.map_tsum
    (summable_mobius_probability_mul_fisherCoordinate hsigma)
  simp only [Complex.ofRealCLM_apply] at hmap
  have hcast :
      (((∑' n : ℕ, squarefreeMobiusProbability sigma n *
        mobiusCriticalFisherCoordinate sigma n) : ℝ) : ℂ) = 0 := by
    rw [hmap]
    exact hcomplex
  exact_mod_cast hcast

def mobiusFisherOffDiagonalCodiagonal
    (sigma u : ℝ) : ℝ :=
  diffuseFisherOffDiagonalCodiagonal
    (squarefreeMobiusProbability sigma)
    (mobiusCriticalFisherCoordinate sigma)
    (mobiusCriticalDampingCoordinate sigma u)

theorem mobiusFisherOffDiagonalCodiagonal_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    mobiusFisherOffDiagonalCodiagonal sigma u =
      (∑' n : ℕ, squarefreeMobiusProbability sigma n *
        mobiusCriticalFisherCoordinate sigma n *
          mobiusCriticalDampingCoordinate sigma u n) -
        2 * diffuseFisherCollisionResidual
          (squarefreeMobiusProbability sigma)
          (mobiusCriticalFisherCoordinate sigma)
          (mobiusCriticalDampingCoordinate sigma u) := by
  exact diffuseFisherOffDiagonalCodiagonal_eq_score_sub_collision
    (summable_squarefreeMobiusProbability hsigma)
    (summable_mobius_probability_mul_fisherCoordinate hsigma)
    (summable_mobius_probability_mul_fisherCoordinate_mul_damping hsigma hu)
    (summable_mobius_collision hsigma hu)
    (tsum_squarefreeMobiusProbability hsigma)
    (tsum_mobius_probability_mul_fisherCoordinate_zero hsigma)

/-- The real Möbius Fisher score appearing in the diffuse codiagonal law is exactly the
complex critical Fisher/damped-source coefficient. -/
theorem ofReal_tsum_mobius_probability_mul_fisherCoordinate_mul_damping_eq_coefficient
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    (((∑' n : ℕ, squarefreeMobiusProbability sigma n *
      mobiusCriticalFisherCoordinate sigma n *
        mobiusCriticalDampingCoordinate sigma u n) : ℝ) : ℂ) =
      infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u := by
  have hmap := Complex.ofRealCLM.map_tsum
    (summable_mobius_probability_mul_fisherCoordinate_mul_damping hsigma hu)
  simp only [Complex.ofRealCLM_apply] at hmap
  calc
    (((∑' n : ℕ, squarefreeMobiusProbability sigma n *
      mobiusCriticalFisherCoordinate sigma n *
        mobiusCriticalDampingCoordinate sigma u n) : ℝ) : ℂ) =
        ∑' n : ℕ,
          ((squarefreeMobiusProbability sigma n *
            mobiusCriticalFisherCoordinate sigma n *
              mobiusCriticalDampingCoordinate sigma u n : ℝ) : ℂ) := hmap
    _ = inner ℂ (infiniteMobiusSignedWeightLp sigma hsigma)
        (infiniteMobiusCriticalDampedFisherTangentLp sigma u hsigma hu) := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro n
      exact (inner_signed_dampedFisher_apply_eq hsigma n).symm
    _ = inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
        (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu) :=
      inner_signed_dampedFisher_eq_fisher_dampedSigned hsigma hu
    _ = infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u :=
      inner_fisherTangent_damped_eq_coefficient hsigma hu

/-- The atomic collision term in the diffuse law is exactly the Hilbert-space collision
residual. -/
theorem ofReal_diffuseFisherCollisionResidual_eq_mobiusDiffuseCollisionResidual
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    ((diffuseFisherCollisionResidual
      (squarefreeMobiusProbability sigma)
      (mobiusCriticalFisherCoordinate sigma)
      (mobiusCriticalDampingCoordinate sigma u) : ℝ) : ℂ) =
        mobiusDiffuseCollisionResidual sigma u := by
  have hmap := Complex.ofRealCLM.map_tsum
    (summable_mobius_collision hsigma hu)
  simp only [Complex.ofRealCLM_apply] at hmap
  rw [diffuseFisherCollisionResidual]
  calc
    (((∑' n : ℕ, squarefreeMobiusProbability sigma n ^ 2 *
      mobiusCriticalFisherCoordinate sigma n *
        mobiusCriticalDampingCoordinate sigma u n) : ℝ) : ℂ) =
        ∑' n : ℕ,
          ((squarefreeMobiusProbability sigma n ^ 2 *
            mobiusCriticalFisherCoordinate sigma n *
              mobiusCriticalDampingCoordinate sigma u n : ℝ) : ℂ) := hmap
    _ = inner ℂ (infiniteMobiusCollisionSourceLp sigma hsigma)
        (infiniteMobiusCriticalDampedFisherTangentLp sigma u hsigma hu) := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro n
      exact (inner_collision_dampedFisher_apply_eq hsigma n).symm
    _ = mobiusDiffuseCollisionResidual sigma u := by
      rw [mobiusDiffuseCollisionResidual, dif_pos hsigma, dif_pos hu]

/-- **Critical diffuse codiagonal identity.** The complete off-diagonal Möbius Fisher
codiagonal is the desired critical source coefficient minus exactly twice the atomic
collision residual. This is an infinite source identity; no finite-rank truncation occurs. -/
theorem ofReal_mobiusFisherOffDiagonalCodiagonal_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    (mobiusFisherOffDiagonalCodiagonal sigma u : ℂ) =
      infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u -
        2 * mobiusDiffuseCollisionResidual sigma u := by
  calc
    (mobiusFisherOffDiagonalCodiagonal sigma u : ℂ) =
        (((∑' n : ℕ, squarefreeMobiusProbability sigma n *
          mobiusCriticalFisherCoordinate sigma n *
            mobiusCriticalDampingCoordinate sigma u n) -
          2 * diffuseFisherCollisionResidual
            (squarefreeMobiusProbability sigma)
            (mobiusCriticalFisherCoordinate sigma)
            (mobiusCriticalDampingCoordinate sigma u) : ℝ) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ))
        (mobiusFisherOffDiagonalCodiagonal_eq hsigma hu)
    _ = (((∑' n : ℕ, squarefreeMobiusProbability sigma n *
          mobiusCriticalFisherCoordinate sigma n *
            mobiusCriticalDampingCoordinate sigma u n) : ℝ) : ℂ) -
        2 * ((diffuseFisherCollisionResidual
          (squarefreeMobiusProbability sigma)
          (mobiusCriticalFisherCoordinate sigma)
          (mobiusCriticalDampingCoordinate sigma u) : ℝ) : ℂ) := by
      push_cast
      ring
    _ = infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u -
        2 * mobiusDiffuseCollisionResidual sigma u := by
      rw [
        ofReal_tsum_mobius_probability_mul_fisherCoordinate_mul_damping_eq_coefficient
          hsigma hu,
        ofReal_diffuseFisherCollisionResidual_eq_mobiusDiffuseCollisionResidual
          hsigma hu]

/-- **Critical diffuse codiagonal recovery law.** At the Möbius critical boundary,
off-diagonal source Fisher data recover the full universal score profile. Atomic diagonal
loss disappears because the probability law becomes diffuse. -/
theorem tendsto_ofReal_mobiusFisherOffDiagonalCodiagonal
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ =>
      (mobiusFisherOffDiagonalCodiagonal sigma u : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (((2 * u / (1 + u) ^ 2 : ℝ) : ℂ))) := by
  have hcollision :
      Tendsto (fun sigma : ℝ => mobiusDiffuseCollisionResidual sigma u)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (tendsto_norm_mobiusDiffuseCollisionResidual_zero hu)
  have hmain :=
    (tendsto_infiniteMobiusCriticalFisherTangentDampedCoefficient hu).sub
      (hcollision.const_mul 2)
  have heq :
      (fun sigma : ℝ =>
        infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u -
          2 * mobiusDiffuseCollisionResidual sigma u) =ᶠ[
            nhdsWithin 1 (Set.Ioi 1)]
        (fun sigma : ℝ =>
          (mobiusFisherOffDiagonalCodiagonal sigma u : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    change 1 < sigma at hsigma
    exact (ofReal_mobiusFisherOffDiagonalCodiagonal_eq hsigma hu).symm
  simpa using hmain.congr' heq

/-! ## One-corner order folding

The complete ordered codiagonal does not require both adjoint cutoff corners.  A single strict
lower corner contains one representative of every unordered pair.  Testing each lower entry
against the joined row/column damping `d n + d m` recovers both ordered terms. -/

/-- Codiagonal obtained from one strict lower corner by a joined row/column reporter. -/
def strictLowerOneCornerCodiagonal
    (F : ℕ × ℕ → ℝ) : ℝ :=
  ∑' q : ℕ × ℕ,
    if q.2 < q.1 then F q + F q.swap else 0

/-- Complete ordered off-diagonal codiagonal in product-index form. -/
def orderedOffDiagonalCodiagonal
    (F : ℕ × ℕ → ℝ) : ℝ :=
  ∑' q : ℕ × ℕ,
    if q.1 ≠ q.2 then F q else 0

private theorem summable_strictLower
    (F : ℕ × ℕ → ℝ) (hF : Summable F) :
    Summable (fun q : ℕ × ℕ =>
      if q.2 < q.1 then F q else 0) := by
  let A : Set (ℕ × ℕ) := {q | q.2 < q.1}
  exact (hF.indicator A).congr
    (fun q => by simp [A, Set.indicator])

private theorem summable_strictLower_swap
    (F : ℕ × ℕ → ℝ) (hF : Summable F) :
    Summable (fun q : ℕ × ℕ =>
      if q.2 < q.1 then F q.swap else 0) := by
  have hs : Summable (fun q : ℕ × ℕ => F q.swap) :=
    hF.prod_symm
  let A : Set (ℕ × ℕ) := {q | q.2 < q.1}
  exact (hs.indicator A).congr
    (fun q => by simp [A, Set.indicator])

private theorem summable_strictUpper
    (F : ℕ × ℕ → ℝ) (hF : Summable F) :
    Summable (fun q : ℕ × ℕ =>
      if q.1 < q.2 then F q else 0) := by
  let A : Set (ℕ × ℕ) := {q | q.1 < q.2}
  exact (hF.indicator A).congr
    (fun q => by simp [A, Set.indicator])

private theorem summable_orderedOffDiagonal
    (F : ℕ × ℕ → ℝ) (hF : Summable F) :
    Summable (fun q : ℕ × ℕ =>
      if q.1 ≠ q.2 then F q else 0) := by
  let A : Set (ℕ × ℕ) := {q | q.1 ≠ q.2}
  exact (hF.indicator A).congr
    (fun q => by simp [A, Set.indicator])

/-- **Infinite one-corner folding law.**  For every absolutely summable ordered kernel, one
strict lower corner with its joined row/column reporter equals the complete ordered
off-diagonal codiagonal.  This is countably infinite and has no finite-rank hypothesis. -/
theorem strictLowerOneCornerCodiagonal_eq_orderedOffDiagonal
    (F : ℕ × ℕ → ℝ) (hF : Summable F) :
    strictLowerOneCornerCodiagonal F =
      orderedOffDiagonalCodiagonal F := by
  have hL := summable_strictLower F hF
  have hLS := summable_strictLower_swap F hF
  have hU := summable_strictUpper F hF
  rw [strictLowerOneCornerCodiagonal,
    show (fun q : ℕ × ℕ =>
      if q.2 < q.1 then F q + F q.swap else 0) =
      (fun q =>
        (if q.2 < q.1 then F q else 0) +
          (if q.2 < q.1 then F q.swap else 0)) by
      funext q
      split_ifs <;> simp_all]
  rw [hL.tsum_add hLS]
  have hswap :
      (∑' q : ℕ × ℕ,
        if q.2 < q.1 then F q.swap else 0) =
      ∑' q : ℕ × ℕ,
        if q.1 < q.2 then F q else 0 := by
    simpa using (Equiv.prodComm ℕ ℕ).tsum_eq
      (fun q : ℕ × ℕ =>
        if q.1 < q.2 then F q else 0)
  rw [hswap, ← hL.tsum_add hU,
    orderedOffDiagonalCodiagonal]
  apply tsum_congr
  intro q
  rcases lt_trichotomy q.1 q.2 with h | h | h
  · have hn : ¬ q.2 < q.1 := not_lt_of_ge h.le
    simp [h, h.ne, hn]
  · simp [h]
  · have hn : ¬ q.1 < q.2 := not_lt_of_ge h.le
    simp [h, h.ne', hn]

/-- Ordered Fisher kernel before the one-corner fold. -/
def diffuseFisherOrderedKernel
    (p a d : ℕ → ℝ) (q : ℕ × ℕ) : ℝ :=
  p q.1 * p q.2 * (a q.1 + a q.2) * d q.1

/-- One strict lower Fisher corner, tested by the symmetric damping reporter. -/
def diffuseFisherOneCornerCodiagonal
    (p a d : ℕ → ℝ) : ℝ :=
  strictLowerOneCornerCodiagonal
    (diffuseFisherOrderedKernel p a d)

private theorem summable_diffuseFisherOrderedKernel
    {p a d : ℕ → ℝ}
    (hp : Summable p)
    (hpa : Summable (fun n => p n * a n))
    (hpd : Summable (fun n => p n * d n))
    (hpad : Summable (fun n => p n * a n * d n)) :
    Summable (diffuseFisherOrderedKernel p a d) := by
  have hleft :
      Summable (fun q : ℕ × ℕ =>
        (p q.1 * a q.1 * d q.1) * p q.2) :=
    summable_mul_of_summable_norm hpad.norm hp.norm
  have hright :
      Summable (fun q : ℕ × ℕ =>
        (p q.1 * d q.1) * (p q.2 * a q.2)) :=
    summable_mul_of_summable_norm hpd.norm hpa.norm
  convert hleft.add hright using 1
  funext q
  simp only [diffuseFisherOrderedKernel]
  ring

/-- Product-index and iterated presentations of the ordered Fisher codiagonal agree. -/
theorem orderedOffDiagonalCodiagonal_diffuseFisherOrderedKernel_eq
    {p a d : ℕ → ℝ}
    (hp : Summable p)
    (hpa : Summable (fun n => p n * a n))
    (hpd : Summable (fun n => p n * d n))
    (hpad : Summable (fun n => p n * a n * d n)) :
    orderedOffDiagonalCodiagonal
        (diffuseFisherOrderedKernel p a d) =
      diffuseFisherOffDiagonalCodiagonal p a d := by
  have hF :=
    summable_diffuseFisherOrderedKernel hp hpa hpd hpad
  have hO :=
    summable_orderedOffDiagonal
      (diffuseFisherOrderedKernel p a d) hF
  rw [orderedOffDiagonalCodiagonal, hO.tsum_prod,
    diffuseFisherOffDiagonalCodiagonal]
  apply tsum_congr
  intro n
  apply tsum_congr
  intro m
  by_cases hmn : m = n
  · subst m
    simp
  · have hnm : n ≠ m := Ne.symm hmn
    simp [hmn, hnm, diffuseFisherOrderedKernel]

/-- A single strict lower Fisher corner carries the complete ordered codiagonal. -/
theorem diffuseFisherOneCornerCodiagonal_eq_offDiagonal
    {p a d : ℕ → ℝ}
    (hp : Summable p)
    (hpa : Summable (fun n => p n * a n))
    (hpd : Summable (fun n => p n * d n))
    (hpad : Summable (fun n => p n * a n * d n)) :
    diffuseFisherOneCornerCodiagonal p a d =
      diffuseFisherOffDiagonalCodiagonal p a d := by
  rw [diffuseFisherOneCornerCodiagonal,
    strictLowerOneCornerCodiagonal_eq_orderedOffDiagonal
      (diffuseFisherOrderedKernel p a d)
      (summable_diffuseFisherOrderedKernel hp hpa hpd hpad)]
  exact orderedOffDiagonalCodiagonal_diffuseFisherOrderedKernel_eq
    hp hpa hpd hpad

theorem summable_mobius_probability_mul_damping
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Summable (fun n : ℕ =>
      squarefreeMobiusProbability sigma n *
        mobiusCriticalDampingCoordinate sigma u n) := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg
      (squarefreeMobiusProbability_nonneg hsigma n)
      (Real.exp_pos _).le)
    (fun n => ?_)
    (summable_squarefreeMobiusProbability hsigma)
  apply mul_le_of_le_one_right
    (squarefreeMobiusProbability_nonneg hsigma n)
  rw [mobiusCriticalDampingCoordinate, Real.exp_le_one_iff]
  exact neg_nonpos.mpr
    (mul_nonneg
      (mul_nonneg hu (sub_nonneg.mpr hsigma.le))
      (Real.log_natCast_nonneg n))

/-- The physical one-corner Möbius Fisher codiagonal.  Only pairs `m < n` occur; the joined
reporter retains both damping placements on that one lower entry. -/
def mobiusFisherOneCornerCodiagonal
    (sigma u : ℝ) : ℝ :=
  diffuseFisherOneCornerCodiagonal
    (squarefreeMobiusProbability sigma)
    (mobiusCriticalFisherCoordinate sigma)
    (mobiusCriticalDampingCoordinate sigma u)

/-- The Möbius one-corner reporter is exactly the complete off-diagonal reporter at every safe
Euler parameter. -/
theorem mobiusFisherOneCornerCodiagonal_eq_offDiagonal
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    mobiusFisherOneCornerCodiagonal sigma u =
      mobiusFisherOffDiagonalCodiagonal sigma u := by
  exact diffuseFisherOneCornerCodiagonal_eq_offDiagonal
    (summable_squarefreeMobiusProbability hsigma)
    (summable_mobius_probability_mul_fisherCoordinate hsigma)
    (summable_mobius_probability_mul_damping hsigma hu)
    (summable_mobius_probability_mul_fisherCoordinate_mul_damping
      hsigma hu)

/-- **One-corner critical diffuse identity.**  One physical lower Fisher corner recovers the
critical source coefficient up to exactly twice the vanishing collision residual. -/
theorem ofReal_mobiusFisherOneCornerCodiagonal_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    (mobiusFisherOneCornerCodiagonal sigma u : ℂ) =
      infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u -
        2 * mobiusDiffuseCollisionResidual sigma u := by
  rw [mobiusFisherOneCornerCodiagonal_eq_offDiagonal hsigma hu]
  exact ofReal_mobiusFisherOffDiagonalCodiagonal_eq hsigma hu

/-- **One-corner critical diffuse recovery law.**  A single non-diagonal lower Fisher corner
recovers the complete universal critical score profile; neither its adjoint upper corner nor a
finite-rank truncation is used. -/
theorem tendsto_ofReal_mobiusFisherOneCornerCodiagonal
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ =>
      (mobiusFisherOneCornerCodiagonal sigma u : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (((2 * u / (1 + u) ^ 2 : ℝ) : ℂ))) := by
  apply
    (tendsto_ofReal_mobiusFisherOffDiagonalCodiagonal hu).congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  exact_mod_cast
    (mobiusFisherOneCornerCodiagonal_eq_offDiagonal hsigma hu).symm

/-! ## Collision renormalization through the singular Gamma graph -/

/-- Euler parameter seen by the squared atomic probability in the collision residual. -/
def mobiusDiffuseCollisionParameter (sigma u : ℝ) : ℝ :=
  2 * sigma + u * (sigma - 1)

theorem mobiusDiffuseCollisionParameter_gt_one
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    1 < mobiusDiffuseCollisionParameter sigma u := by
  dsimp [mobiusDiffuseCollisionParameter]
  nlinarith

private theorem squarefreeMobiusMass_sq_mul_damping
    {sigma u : ℝ} (n : ℕ) :
    squarefreeMobiusMass sigma n ^ 2 *
        mobiusCriticalDampingCoordinate sigma u n =
      squarefreeMobiusMass
        (mobiusDiffuseCollisionParameter sigma u) n := by
  rw [squarefreeMobiusMass, squarefreeMobiusMass]
  split_ifs with hn
  · have hn0 : n ≠ 0 := by
      intro h
      subst n
      exact not_squarefree_zero hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn0
    have hdamp :
        Real.exp (-(u * (sigma - 1) * Real.log n)) =
          (n : ℝ) ^ (-(u * (sigma - 1))) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    rw [mobiusCriticalDampingCoordinate, hdamp,
      ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le,
      ← Real.rpow_add hnpos]
    congr 1
    dsimp [mobiusDiffuseCollisionParameter]
    ring
  · simp

private theorem tsum_squarefreeMobiusMass_mul_centeredLog
    {tau sigma : ℝ} (htau : 1 < tau) :
    (∑' n : ℕ, squarefreeMobiusMass tau n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma)) =
      squarefreeMobiusTotal tau *
        (squarefreeMobiusLogMoment 1 tau -
          squarefreeMobiusLogMoment 1 sigma) := by
  have hlog := summable_squarefreeMobiusLogMoment 1 htau
  have hmass := summable_squarefreeMobiusMass htau
  have hraw : Summable (fun n : ℕ =>
      squarefreeMobiusMass tau n * Real.log n) := by
    have hz := (squarefreeMobiusTotal_pos htau).ne'
    have hscaled := hlog.mul_left (squarefreeMobiusTotal tau)
    convert hscaled using 1
    all_goals try rfl
    funext n
    rw [squarefreeMobiusProbability]
    field_simp [hz]
  rw [show (fun n : ℕ => squarefreeMobiusMass tau n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma)) =
      fun n => squarefreeMobiusMass tau n * Real.log n -
        squarefreeMobiusLogMoment 1 sigma *
          squarefreeMobiusMass tau n by
    funext n
    ring]
  rw [Summable.tsum_sub hraw (hmass.mul_left _), tsum_mul_left]
  have hmoment :
      (∑' n : ℕ, squarefreeMobiusMass tau n * Real.log n) =
        squarefreeMobiusTotal tau *
          squarefreeMobiusLogMoment 1 tau := by
    have hz := (squarefreeMobiusTotal_pos htau).ne'
    rw [squarefreeMobiusLogMoment]
    rw [show (fun n : ℕ =>
        squarefreeMobiusProbability tau n * Real.log n ^ 1) =
        fun n => squarefreeMobiusMass tau n * Real.log n /
          squarefreeMobiusTotal tau by
      funext n
      rw [squarefreeMobiusProbability]
      simp only [pow_one]
      ring]
    rw [tsum_div_const]
    field_simp [hz]
  rw [hmoment, show (∑' n : ℕ, squarefreeMobiusMass tau n) =
    squarefreeMobiusTotal tau by rfl]
  ring

/-- **Exact collision law.**  Squaring the Möbius probability moves the Euler parameter from
`sigma` to `2 * sigma + u * (sigma - 1)`.  This extra Euler summability is what makes the
collision residual one full critical order smaller than the prior norm estimate detected. -/
theorem diffuseFisherCollisionResidual_mobius_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    diffuseFisherCollisionResidual
        (squarefreeMobiusProbability sigma)
        (mobiusCriticalFisherCoordinate sigma)
        (mobiusCriticalDampingCoordinate sigma u) =
      -2 * (sigma - 1) *
        (squarefreeMobiusTotal
            (mobiusDiffuseCollisionParameter sigma u) /
          squarefreeMobiusTotal sigma ^ 2) *
        (squarefreeMobiusLogMoment 1
            (mobiusDiffuseCollisionParameter sigma u) -
          squarefreeMobiusLogMoment 1 sigma) := by
  have htau := mobiusDiffuseCollisionParameter_gt_one hsigma hu
  have hz := (squarefreeMobiusTotal_pos hsigma).ne'
  rw [diffuseFisherCollisionResidual]
  have hpoint : (fun n : ℕ =>
      squarefreeMobiusProbability sigma n ^ 2 *
        mobiusCriticalFisherCoordinate sigma n *
          mobiusCriticalDampingCoordinate sigma u n) =
      fun n =>
        (-2 * (sigma - 1) / squarefreeMobiusTotal sigma ^ 2) *
          (squarefreeMobiusMass
              (mobiusDiffuseCollisionParameter sigma u) n *
            (Real.log n - squarefreeMobiusLogMoment 1 sigma)) := by
    funext n
    rw [squarefreeMobiusProbability, mobiusCriticalFisherCoordinate]
    calc
      (squarefreeMobiusMass sigma n /
              squarefreeMobiusTotal sigma) ^ 2 *
            (-2 * (sigma - 1) *
              (Real.log n - squarefreeMobiusLogMoment 1 sigma)) *
          mobiusCriticalDampingCoordinate sigma u n =
        (-2 * (sigma - 1) / squarefreeMobiusTotal sigma ^ 2) *
          (squarefreeMobiusMass sigma n ^ 2 *
            mobiusCriticalDampingCoordinate sigma u n) *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma) := by
        field_simp [hz]
      _ = (-2 * (sigma - 1) / squarefreeMobiusTotal sigma ^ 2) *
          (squarefreeMobiusMass
              (mobiusDiffuseCollisionParameter sigma u) n *
            (Real.log n - squarefreeMobiusLogMoment 1 sigma)) := by
        rw [squarefreeMobiusMass_sq_mul_damping]
        ring
  rw [hpoint, tsum_mul_left,
    tsum_squarefreeMobiusMass_mul_centeredLog htau]
  field_simp [hz]

/-- Exact critical scale of the reciprocal squarefree partition. -/
theorem tendsto_inv_squarefreeMobiusTotal_div_sub_one :
    Tendsto (fun sigma : ℝ =>
      (squarefreeMobiusTotal sigma)⁻¹ / (sigma - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ)).re) := by
  have hsigma : Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      inf_le_left
  have htwoArg : Tendsto (fun sigma : ℝ => 2 * (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hsigma :
      Tendsto (fun sigma : ℝ => (2 : ℂ) * (sigma : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 ((2 : ℂ) * 1)))
  have hnum : Tendsto
      (fun sigma : ℝ => riemannZeta (2 * (sigma : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) :=
    (differentiableAt_riemannZeta
      (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp htwoArg
  have hunit : Tendsto
      (fun sigma : ℝ => zetaResidueUnit (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using!
      zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hsigma
  have hquot : Tendsto
      (fun sigma : ℝ =>
        riemannZeta (2 * (sigma : ℂ)) /
          zetaResidueUnit (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) := by
    simpa using! hnum.div hunit (by norm_num : (1 : ℂ) ≠ 0)
  have heq :
      (fun sigma : ℝ =>
        (((squarefreeMobiusTotal sigma)⁻¹ /
          (sigma - 1) : ℝ) : ℂ)) =ᶠ[𝓝[>] (1 : ℝ)]
      fun sigma : ℝ =>
        riemannZeta (2 * (sigma : ℂ)) /
          zetaResidueUnit (sigma : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigmaGt
    change 1 < sigma at hsigmaGt
    have hsigmaOne : (sigma : ℂ) ≠ 1 := by
      exact_mod_cast ne_of_gt hsigmaGt
    have hzetaSigma : riemannZeta (sigma : ℂ) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re
        (by simpa using hsigmaGt)
    have hzetaTwo : riemannZeta (2 * (sigma : ℂ)) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
    rw [Complex.ofReal_div, Complex.ofReal_inv,
      ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigmaGt]
    rw [show zetaResidueUnit (sigma : ℂ) =
        ((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ) by
      simp only [zetaResidueUnit, Function.update_of_ne hsigmaOne]]
    push_cast
    field_simp [hzetaSigma, hzetaTwo, hsigmaOne,
      sub_ne_zero.mpr hsigmaOne]
  have hcast : Tendsto
      (fun sigma : ℝ =>
        (((squarefreeMobiusTotal sigma)⁻¹ /
          (sigma - 1) : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) :=
    hquot.congr' heq.symm
  have hre :=
    Complex.continuous_re.continuousAt.tendsto.comp hcast
  convert hre using 1 <;> rfl

theorem tendsto_mobiusDiffuseCollisionParameter
    (u : ℝ) :
    Tendsto (fun sigma : ℝ =>
      mobiusDiffuseCollisionParameter sigma u)
      (𝓝[>] (1 : ℝ)) (𝓝 2) := by
  have hs : Tendsto (fun sigma : ℝ => sigma)
      (𝓝[>] (1 : ℝ)) (𝓝 1) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  simpa [mobiusDiffuseCollisionParameter] using
    (tendsto_const_nhds.mul hs).add
      (tendsto_const_nhds.mul (hs.sub_const 1))

private theorem tendsto_squarefreeMobiusTotal_collisionParameter
    (u : ℝ) :
    Tendsto (fun sigma : ℝ =>
      squarefreeMobiusTotal
        (mobiusDiffuseCollisionParameter sigma u))
      (𝓝[>] (1 : ℝ))
      (𝓝 (GaloisForLFunctions.squarefreePartition (2 : ℂ)).re) := by
  have htauR := tendsto_mobiusDiffuseCollisionParameter u
  have htauC : Tendsto (fun sigma : ℝ =>
      ((mobiusDiffuseCollisionParameter sigma u : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp htauR
  have hpart :=
    (GaloisForLFunctions.differentiableAt_squarefreePartition
      (s := (2 : ℂ)) (by norm_num)).continuousAt.tendsto.comp htauC
  have heq :
      (fun sigma : ℝ =>
        (squarefreeMobiusTotal
          (mobiusDiffuseCollisionParameter sigma u) : ℂ)) =ᶠ[
            𝓝[>] (1 : ℝ)]
      fun sigma : ℝ =>
        GaloisForLFunctions.squarefreePartition
          (mobiusDiffuseCollisionParameter sigma u : ℂ) := by
    filter_upwards
      [htauR (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))]
      with sigma htau
    simpa [GaloisForLFunctions.squarefreePartition] using
      ofReal_squarefreeMobiusTotal_eq_zetaRatio htau
  have hcast := hpart.congr' heq.symm
  have hre :=
    Complex.continuous_re.continuousAt.tendsto.comp hcast
  simpa [Function.comp_def] using hre

private theorem tendsto_squarefreeMobiusLogMoment_collisionParameter
    (u : ℝ) :
    Tendsto (fun sigma : ℝ =>
      squarefreeMobiusLogMoment 1
        (mobiusDiffuseCollisionParameter sigma u))
      (𝓝[>] (1 : ℝ))
      (𝓝 (GaloisForLFunctions.squarefreeFixedCurrent (2 : ℂ)).re) := by
  have htauR := tendsto_mobiusDiffuseCollisionParameter u
  have htauC : Tendsto (fun sigma : ℝ =>
      ((mobiusDiffuseCollisionParameter sigma u : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp htauR
  have hflux2 :
      DifferentiableAt ℂ infinitePrimeFlux (2 : ℂ) := by
    simpa only [infinitePrimeFlux, logDeriv_apply, neg_div] using!
      (differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re
        (s := (2 : ℂ)) (by norm_num))
  have hflux4 :
      DifferentiableAt ℂ infinitePrimeFlux (4 : ℂ) := by
    simpa only [infinitePrimeFlux, logDeriv_apply, neg_div] using!
      (differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re
        (s := (4 : ℂ)) (by norm_num))
  have hcomp : DifferentiableAt ℂ
      (fun z : ℂ => infinitePrimeFlux (2 * z)) (2 : ℂ) := by
    have hflux4' :
        DifferentiableAt ℂ infinitePrimeFlux
          (2 * (2 : ℂ)) := by
      norm_num
      exact hflux4
    exact hflux4'.comp (2 : ℂ)
      (show DifferentiableAt ℂ
        (fun z : ℂ => 2 * z) (2 : ℂ) by fun_prop)
  have hfixed :
      ContinuousAt GaloisForLFunctions.squarefreeFixedCurrent
        (2 : ℂ) := by
    change ContinuousAt
      (fun z : ℂ => infinitePrimeFlux z -
        2 * infinitePrimeFlux (2 * z)) (2 : ℂ)
    exact hflux2.continuousAt.sub
      (hcomp.const_mul (2 : ℂ)).continuousAt
  have hcurrent := hfixed.tendsto.comp htauC
  have heq :
      (fun sigma : ℝ =>
        (squarefreeMobiusLogMoment 1
          (mobiusDiffuseCollisionParameter sigma u) : ℂ)) =ᶠ[
            𝓝[>] (1 : ℝ)]
      fun sigma : ℝ =>
        GaloisForLFunctions.squarefreeFixedCurrent
          (mobiusDiffuseCollisionParameter sigma u : ℂ) := by
    filter_upwards
      [htauR (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))]
      with sigma htau
    exact ofReal_squarefreeMobiusLogMoment_one_eq_fixedCurrent
      htau
  have hcast := hcurrent.congr' heq.symm
  have hre :=
    Complex.continuous_re.continuousAt.tendsto.comp hcast
  simpa [Function.comp_def] using hre

private theorem tendsto_squarefreeMobiusLogMoment_mul_invTotal :
    Tendsto (fun sigma : ℝ =>
      squarefreeMobiusLogMoment 1 sigma *
        (squarefreeMobiusTotal sigma)⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ)).re) := by
  have hprod :=
    tendsto_squarefreeMobiusLogMoment_one_critical.mul
      tendsto_inv_squarefreeMobiusTotal_div_sub_one
  have hprod' : Tendsto
      (fun sigma : ℝ =>
        (sigma - 1) * squarefreeMobiusLogMoment 1 sigma *
          ((squarefreeMobiusTotal sigma)⁻¹ / (sigma - 1)))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ)).re) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  have heps : sigma - 1 ≠ 0 :=
    sub_ne_zero.mpr hsigma.ne'
  field_simp [heps]

/-- **Renormalized collision disappearance.**  The collision residual remains negligible after
division by the critical factor `sigma - 1`; this is one order stronger than unscaled diffuse
convergence. -/
theorem tendsto_diffuseFisherCollisionResidual_div_sub_one_zero
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ =>
      diffuseFisherCollisionResidual
          (squarefreeMobiusProbability sigma)
          (mobiusCriticalFisherCoordinate sigma)
          (mobiusCriticalDampingCoordinate sigma u) /
        (sigma - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have htotal :=
    tendsto_squarefreeMobiusTotal_collisionParameter u
  have hinv := tendsto_inv_squarefreeMobiusTotal_zero
  have hbase :=
    tendsto_squarefreeMobiusLogMoment_mul_invTotal
  have hfar :=
    (tendsto_squarefreeMobiusLogMoment_collisionParameter u).mul
      hinv
  have hbracket := hbase.sub hfar
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ))
      (𝓝[>] (1 : ℝ)) (𝓝 2) := tendsto_const_nhds
  have hmain0 :=
    ((htwo.mul htotal).mul hinv).mul hbracket
  have hmain : Tendsto (fun sigma : ℝ =>
      2 * squarefreeMobiusTotal
          (mobiusDiffuseCollisionParameter sigma u) *
        (squarefreeMobiusTotal sigma)⁻¹ *
        (squarefreeMobiusLogMoment 1 sigma *
            (squarefreeMobiusTotal sigma)⁻¹ -
          squarefreeMobiusLogMoment 1
              (mobiusDiffuseCollisionParameter sigma u) *
            (squarefreeMobiusTotal sigma)⁻¹))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using hmain0
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  have heps : sigma - 1 ≠ 0 :=
    sub_ne_zero.mpr hsigma.ne'
  have hz := (squarefreeMobiusTotal_pos hsigma).ne'
  rw [diffuseFisherCollisionResidual_mobius_eq hsigma hu]
  field_simp [heps, hz]
  ring

/-- The collision error vanishes even after the exact overlap division in the singular
Möbius--Gamma graph. -/
theorem tendsto_mobiusDiffuseCollisionResidual_div_graphScale_zero
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ =>
      mobiusDiffuseCollisionResidual sigma u /
        (((sigma - 1 : ℝ) : ℂ) *
          squarefreeMobiusBoundaryLayerLaplace sigma u))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hreal :=
    tendsto_diffuseFisherCollisionResidual_div_sub_one_zero hu
  have hcast : Tendsto (fun sigma : ℝ =>
      ((diffuseFisherCollisionResidual
          (squarefreeMobiusProbability sigma)
          (mobiusCriticalFisherCoordinate sigma)
          (mobiusCriticalDampingCoordinate sigma u) /
        (sigma - 1) : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hoverlap :=
    tendsto_squarefreeMobiusBoundaryLayerLaplace hu
  have hlimitNe :
      ((((1 + u : ℝ) : ℂ))⁻¹) ≠ 0 := by
    exact inv_ne_zero
      (Complex.ofReal_ne_zero.mpr (by nlinarith))
  have hquot := hcast.div hoverlap hlimitNe
  have hquot' : Tendsto (fun sigma : ℝ =>
      ((diffuseFisherCollisionResidual
          (squarefreeMobiusProbability sigma)
          (mobiusCriticalFisherCoordinate sigma)
          (mobiusCriticalDampingCoordinate sigma u) /
        (sigma - 1) : ℝ) : ℂ) /
        squarefreeMobiusBoundaryLayerLaplace sigma u)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using! hquot
  apply hquot'.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [←
    ofReal_diffuseFisherCollisionResidual_eq_mobiusDiffuseCollisionResidual
      hsigma hu]
  push_cast
  rw [div_div]

/-! ## Off-diagonal one-corner Gamma--Xi transport -/

/-- The one-corner numerator plus its exact atomic correction is the division-free squarefree
Fisher numerator. -/
theorem ofReal_mobiusFisherOneCornerCodiagonal_add_collision_eq_score
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    (mobiusFisherOneCornerCodiagonal sigma u : ℂ) +
        2 * mobiusDiffuseCollisionResidual sigma u =
      GaloisForLFunctions.squarefreeFisherScore
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) := by
  have hcoefficient :
      infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u =
        GaloisForLFunctions.squarefreeFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) := by
    calc
      infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u =
          inner ℂ
            (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
            (infiniteMobiusCriticalDampedSignedWeightLp
              sigma u hsigma hu) :=
        (inner_fisherTangent_damped_eq_coefficient hsigma hu).symm
      _ = GaloisForLFunctions.squarefreeFisherScore
            (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) :=
        inner_fisherTangent_damped_eq_squarefreeFisherScore
          hsigma hu
  rw [ofReal_mobiusFisherOneCornerCodiagonal_eq hsigma hu,
    hcoefficient]
  ring

/-- Gamma current transport using only the strict lower one-corner codiagonal, with no diagonal
collision term inserted. -/
def squarefreeMobiusOneCornerGammaCurrentTransportV
    (sigma u : ℝ) : ℂ :=
  2 * GaloisForLFunctions.squarefreeFixedCurrent sigma -
    (mobiusFisherOneCornerCodiagonal sigma u : ℂ) /
      (((sigma - 1 : ℝ) : ℂ) *
        squarefreeMobiusBoundaryLayerLaplace sigma u) -
    2 * logDeriv archFactor
      (mobiusCriticalBoundaryParameter sigma u)

/-- Exact prelimit comparison: the off-diagonal one-corner Gamma transport differs from the
completed squarefree current by precisely the renormalized atomic collision. -/
theorem squarefreeMobiusOneCornerGammaCurrentTransportV_eq_completed_add_collision
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    squarefreeMobiusOneCornerGammaCurrentTransportV sigma u =
      GaloisForLFunctions.completedSquarefreeFixedCurrent
          (mobiusCriticalBoundaryParameter sigma u : ℂ) +
        2 * mobiusDiffuseCollisionResidual sigma u /
          (((sigma - 1 : ℝ) : ℂ) *
            squarefreeMobiusBoundaryLayerLaplace sigma u) := by
  have hfull :=
    squarefreeMobiusGammaCurrentTransportV_actualTangent
      hsigma hu
  have hoverlap :=
    squarefreeMobiusBoundaryLayerLaplace_eq_squarefreeBoundaryOverlap
      hsigma hu
  have hcoord :
      ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
    exact_mod_cast (show mobiusCriticalBoundaryParameter sigma u =
      sigma + u * (sigma - 1) by rfl)
  calc
    squarefreeMobiusOneCornerGammaCurrentTransportV sigma u =
        squarefreeMobiusGammaCurrentTransportV
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
          (fun v =>
            GaloisForLFunctions.squarefreeFisherScore
              (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v)
          (u : ℂ) +
        2 * mobiusDiffuseCollisionResidual sigma u /
          (((sigma - 1 : ℝ) : ℂ) *
            squarefreeMobiusBoundaryLayerLaplace sigma u) := by
      rw [squarefreeMobiusOneCornerGammaCurrentTransportV,
        squarefreeMobiusGammaCurrentTransportV, ← hoverlap,
        hcoord,
        ←
          ofReal_mobiusFisherOneCornerCodiagonal_add_collision_eq_score
            hsigma hu]
      ring
    _ = GaloisForLFunctions.completedSquarefreeFixedCurrent
          (mobiusCriticalBoundaryParameter sigma u : ℂ) +
        2 * mobiusDiffuseCollisionResidual sigma u /
          (((sigma - 1 : ℝ) : ℂ) *
            squarefreeMobiusBoundaryLayerLaplace sigma u) := by
      rw [hfull]

/-- **Singular-graph one-corner recovery.**  The strict lower one-corner Gamma transport and the
completed squarefree current have vanishing difference at the critical boundary.  Thus diagonal
collision loss stays negligible after the formerly fatal overlap division. -/
theorem tendsto_squarefreeMobiusOneCornerGammaCurrentTransportV_sub_completed_zero
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ =>
      squarefreeMobiusOneCornerGammaCurrentTransportV sigma u -
        GaloisForLFunctions.completedSquarefreeFixedCurrent
          (mobiusCriticalBoundaryParameter sigma u : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hcollision :=
    (tendsto_mobiusDiffuseCollisionResidual_div_graphScale_zero
      hu).const_mul 2
  norm_num at hcollision
  have hcollision' : Tendsto (fun sigma : ℝ =>
      2 * mobiusDiffuseCollisionResidual sigma u /
        (((sigma - 1 : ℝ) : ℂ) *
          squarefreeMobiusBoundaryLayerLaplace sigma u))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, mul_div_assoc] using
      hcollision
  apply hcollision'.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [
    squarefreeMobiusOneCornerGammaCurrentTransportV_eq_completed_add_collision
      hsigma hu]
  ring

/-- Continued Xi transport obtained from the off-diagonal one-corner Gamma current and the exact
source-framed doubled-prime correction. -/
def squarefreeMobiusOneCornerGammaXiWardTransportV
    (sigma u : ℝ) : ℂ :=
  let s : ℂ := (mobiusCriticalBoundaryParameter sigma u : ℂ)
  (-I / 2) *
    (squarefreeMobiusOneCornerGammaCurrentTransportV sigma u +
      4 * infinitePrimeFlux (2 * s))

/-- Exact error identity between the off-diagonal source transport and the continued Xi trace. -/
theorem squarefreeMobiusOneCornerGammaXiWardTransportV_sub_continuedSource
    (sigma u : ℝ) :
    squarefreeMobiusOneCornerGammaXiWardTransportV sigma u -
      continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate
          (mobiusCriticalBoundaryParameter sigma u : ℂ)) =
      (-I / 2) *
        (squarefreeMobiusOneCornerGammaCurrentTransportV sigma u -
          GaloisForLFunctions.completedSquarefreeFixedCurrent
            (mobiusCriticalBoundaryParameter sigma u : ℂ)) := by
  rw [squarefreeMobiusOneCornerGammaXiWardTransportV,
    continuedPrimeArchSourceRelativeTrace_eq_completedSquarefree_add_correction,
    xiWardCenteredCoordinate_source]
  ring

/-- **Off-diagonal Möbius--Gamma/Xi cofinal recovery.**  The source-defined strict lower
one-corner transport asymptotically reconstructs the continued Xi trace on every nonnegative
critical ray.  No target divisor, diagonal Fisher term, or finite-rank cutoff defines the
transport. -/
theorem tendsto_squarefreeMobiusOneCornerGammaXiWardTransportV_sub_continuedSource_zero
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ =>
      squarefreeMobiusOneCornerGammaXiWardTransportV sigma u -
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            (mobiusCriticalBoundaryParameter sigma u : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have h :=
    (tendsto_squarefreeMobiusOneCornerGammaCurrentTransportV_sub_completed_zero
      hu).const_mul (-I / 2)
  have h' : Tendsto (fun sigma : ℝ =>
      (-I / 2) *
        (squarefreeMobiusOneCornerGammaCurrentTransportV sigma u -
          GaloisForLFunctions.completedSquarefreeFixedCurrent
            (mobiusCriticalBoundaryParameter sigma u : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using h
  apply h'.congr'
  exact Filter.Eventually.of_forall
    (fun sigma =>
      (squarefreeMobiusOneCornerGammaXiWardTransportV_sub_continuedSource
        sigma u).symm)

end RHTower
