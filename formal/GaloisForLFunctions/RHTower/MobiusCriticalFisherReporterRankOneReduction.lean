import GaloisForLFunctions.RHTower.CountertransportCountableReporterSelectionCriterion

/-!
# Rank-one reduction of the countable common Hardy reporter

The countable one-corner reporter attached to a contraction `D` depends on
`D` only through the single source vector `D psi_sigma`.  Since the physical
Möbius source `psi_sigma` has norm one, the rank-one contraction

`|D psi_sigma><psi_sigma|`

has the same source value and produces exactly the same `L²` reporter.
Thus Route R's operator-valued selection problem has no extra operator
freedom: it is exactly a unit-ball source-vector selection problem.
-/

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open ContinuousLinearMap InnerProductSpace
open DeningerMeyerGaussianGreen
open GaloisForLFunctions.HTGeometry

/-- Canonical rank-one contraction carrying the normalized physical source
to a prescribed source vector. -/
def squarefreeMobiusCriticalFisherSourceRankOne
    (sigma : ℝ) (hsigma : 1 < sigma)
    (phi : lp (fun _ : ℕ => ℂ) 2) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  rankOne ℂ phi (infiniteMobiusSignedWeightLp sigma hsigma)

@[simp]
theorem squarefreeMobiusCriticalFisherSourceRankOne_apply_source
    (sigma : ℝ) (hsigma : 1 < sigma)
    (phi : lp (fun _ : ℕ => ℂ) 2) :
    squarefreeMobiusCriticalFisherSourceRankOne sigma hsigma phi
        (infiniteMobiusSignedWeightLp sigma hsigma) = phi := by
  rw [squarefreeMobiusCriticalFisherSourceRankOne, rankOne_apply,
    inner_self_eq_norm_sq_to_K, norm_infiniteMobiusSignedWeightLp hsigma]
  norm_num

@[simp]
theorem norm_squarefreeMobiusCriticalFisherSourceRankOne
    (sigma : ℝ) (hsigma : 1 < sigma)
    (phi : lp (fun _ : ℕ => ℂ) 2) :
    ‖squarefreeMobiusCriticalFisherSourceRankOne sigma hsigma phi‖ =
      ‖phi‖ := by
  rw [squarefreeMobiusCriticalFisherSourceRankOne,
    InnerProductSpace.norm_rankOne,
    norm_infiniteMobiusSignedWeightLp hsigma]
  exact mul_one _

theorem norm_squarefreeMobiusCriticalFisherSourceRankOne_le_one
    (sigma : ℝ) (hsigma : 1 < sigma)
    {phi : lp (fun _ : ℕ => ℂ) 2} (hphi : ‖phi‖ ≤ 1) :
    ‖squarefreeMobiusCriticalFisherSourceRankOne sigma hsigma phi‖ ≤ 1 := by
  simpa only [norm_squarefreeMobiusCriticalFisherSourceRankOne] using hphi

/-- Vector-parametrized form of the countable reporter. -/
def squarefreeMobiusCriticalFisherSourceVectorReporter
    (sigma : ℝ) (hsigma : 1 < sigma)
    (phi : lp (fun _ : ℕ => ℂ) 2) (hphi : ‖phi‖ ≤ 1) :
    Lp ℂ 2 halfLineLaplaceMeasure :=
  squarefreeMobiusCriticalFisherCountableCommonHardyReporter sigma hsigma
    (squarefreeMobiusCriticalFisherSourceRankOne sigma hsigma phi)
    (norm_squarefreeMobiusCriticalFisherSourceRankOne_le_one
      sigma hsigma hphi)

/-! ## Exact squarefree-support quotient -/

/-- Orthogonal projection onto the squarefree coordinates visible to both
the normalized Möbius source and its Fisher tangent. -/
def squarefreeMobiusCriticalFisherReporterProjection :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  lpCoordinateProjection {n : ℕ | Squarefree n}

@[simp]
theorem squarefreeMobiusCriticalFisherReporterProjection_apply
    (phi : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    squarefreeMobiusCriticalFisherReporterProjection phi n =
      if Squarefree n then phi n else 0 := by
  rw [squarefreeMobiusCriticalFisherReporterProjection,
    lpCoordinateProjection_apply]
  simp only [Set.indicator, Set.mem_setOf_eq]

theorem norm_squarefreeMobiusCriticalFisherReporterProjection_le
    (phi : lp (fun _ : ℕ => ℂ) 2) :
    ‖squarefreeMobiusCriticalFisherReporterProjection phi‖ ≤ ‖phi‖ := by
  exact lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) fun n => by
    rw [squarefreeMobiusCriticalFisherReporterProjection_apply]
    split_ifs
    · exact le_rfl
    · simp

theorem norm_squarefreeMobiusCriticalFisherReporterProjection_le_one
    {phi : lp (fun _ : ℕ => ℂ) 2} (hphi : ‖phi‖ ≤ 1) :
    ‖squarefreeMobiusCriticalFisherReporterProjection phi‖ ≤ 1 :=
  (norm_squarefreeMobiusCriticalFisherReporterProjection_le phi).trans hphi

/-- Every genuine valuation-depth coordinate `p^(e+2)` is deleted by the
reporter quotient.  The surviving prime cell is depth zero only. -/
@[simp]
theorem squarefreeMobiusCriticalFisherReporterProjection_apply_prime_pow_succ_succ
    (phi : lp (fun _ : ℕ => ℂ) 2) (p : ℕ) (hp : p.Prime) (e : ℕ) :
    squarefreeMobiusCriticalFisherReporterProjection phi (p ^ (e + 2)) = 0 := by
  rw [squarefreeMobiusCriticalFisherReporterProjection_apply, if_neg]
  intro hsquarefree
  have hpow :=
    (Nat.squarefree_pow_iff hp.ne_one (by omega : e + 2 ≠ 0)).mp hsquarefree
  omega

theorem infiniteMobiusSignedWeightLp_apply_eq_zero_of_not_squarefree
    {sigma : ℝ} (hsigma : 1 < sigma) {n : ℕ}
    (hn : ¬ Squarefree n) :
    infiniteMobiusSignedWeightLp sigma hsigma n = 0 := by
  change infiniteMobiusSignedWeight sigma n = 0
  simp [infiniteMobiusSignedWeight,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]

theorem infiniteMobiusCriticalFisherTangentLp_apply_eq_zero_of_not_squarefree
    {sigma : ℝ} (hsigma : 1 < sigma) {n : ℕ}
    (hn : ¬ Squarefree n) :
    infiniteMobiusCriticalFisherTangentLp sigma hsigma n = 0 := by
  change infiniteMobiusCriticalFisherTangentWeight sigma n = 0
  rw [infiniteMobiusCriticalFisherTangentWeight]
  simp [infiniteMobiusSignedWeight,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]

/-- Every ordered-pair coefficient is unchanged after deleting the selected
source vector's nonsquarefree coordinates.  This is the coefficient-level
loss of valuation depth, before the Hardy integral or any norm estimate. -/
theorem squarefreeMobiusCriticalFisherJoinedPairCoefficient_projection
    (sigma : ℝ) (hsigma : 1 < sigma)
    (phi : lp (fun _ : ℕ => ℂ) 2) (i j : ℕ) :
    squarefreeMobiusCriticalFisherJoinedPairCoefficient sigma hsigma
        (squarefreeMobiusCriticalFisherSourceRankOne sigma hsigma
          (squarefreeMobiusCriticalFisherReporterProjection phi)) i j =
      squarefreeMobiusCriticalFisherJoinedPairCoefficient sigma hsigma
        (squarefreeMobiusCriticalFisherSourceRankOne sigma hsigma phi) i j := by
  simp only [squarefreeMobiusCriticalFisherJoinedPairCoefficient,
    squarefreeMobiusCriticalFisherSourceRankOne_apply_source]
  by_cases hi : Squarefree i
  · by_cases hj : Squarefree j
    · simp [squarefreeMobiusCriticalFisherReporterProjection_apply, hi, hj]
    · rw [infiniteMobiusSignedWeightLp_apply_eq_zero_of_not_squarefree
          hsigma hj,
        infiniteMobiusCriticalFisherTangentLp_apply_eq_zero_of_not_squarefree
          hsigma hj]
      simp
  · rw [infiniteMobiusSignedWeightLp_apply_eq_zero_of_not_squarefree
        hsigma hi,
      infiniteMobiusCriticalFisherTangentLp_apply_eq_zero_of_not_squarefree
        hsigma hi]
    simp

/-- The complete countable cutoff field factors through squarefree
projection of the selected source vector. -/
theorem squarefreeMobiusCriticalFisherJoinedCodiagonal_projection
    (sigma : ℝ) (hsigma : 1 < sigma)
    (phi : lp (fun _ : ℕ => ℂ) 2) :
    squarefreeMobiusCriticalFisherJoinedCodiagonal sigma hsigma
        (squarefreeMobiusCriticalFisherSourceRankOne sigma hsigma
          (squarefreeMobiusCriticalFisherReporterProjection phi)) =
      squarefreeMobiusCriticalFisherJoinedCodiagonal sigma hsigma
        (squarefreeMobiusCriticalFisherSourceRankOne sigma hsigma phi) := by
  funext u
  rw [squarefreeMobiusCriticalFisherJoinedCodiagonal_eq_tsum,
    squarefreeMobiusCriticalFisherJoinedCodiagonal_eq_tsum]
  apply tsum_congr
  intro p
  rw [squarefreeMobiusCriticalFisherJoinedPairCoefficient_projection]

/-- **Squarefree reporter quotient.**  The actual `L²` common reporter is
literally unchanged after orthogonally deleting every nonsquarefree selected
coordinate.  Hence no contraction choice can transmit prime-power valuation
depth through this consumer. -/
theorem squarefreeMobiusCriticalFisherSourceVectorReporter_projection
    (sigma : ℝ) (hsigma : 1 < sigma)
    (phi : lp (fun _ : ℕ => ℂ) 2) (hphi : ‖phi‖ ≤ 1) :
    squarefreeMobiusCriticalFisherSourceVectorReporter sigma hsigma
        (squarefreeMobiusCriticalFisherReporterProjection phi)
        (norm_squarefreeMobiusCriticalFisherReporterProjection_le_one hphi) =
      squarefreeMobiusCriticalFisherSourceVectorReporter sigma hsigma
        phi hphi := by
  unfold squarefreeMobiusCriticalFisherSourceVectorReporter
    squarefreeMobiusCriticalFisherCountableCommonHardyReporter
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun u =>
    congrFun
      (squarefreeMobiusCriticalFisherJoinedCodiagonal_projection
        sigma hsigma phi) u

private theorem contraction_apply_source_norm_le_one
    {sigma : ℝ} (hsigma : 1 < sigma)
    (D : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (hD : ‖D‖ ≤ 1) :
    ‖D (infiniteMobiusSignedWeightLp sigma hsigma)‖ ≤ 1 := by
  calc
    ‖D (infiniteMobiusSignedWeightLp sigma hsigma)‖ ≤
        ‖D‖ * ‖infiniteMobiusSignedWeightLp sigma hsigma‖ :=
      ContinuousLinearMap.le_opNorm D _
    _ = ‖D‖ := by rw [norm_infiniteMobiusSignedWeightLp hsigma, mul_one]
    _ ≤ 1 := hD

/-- Pointwise reporter invariance under replacing a contraction by its
canonical rank-one representative. -/
theorem squarefreeMobiusCriticalFisherJoinedCodiagonal_rankOne
    (sigma : ℝ) (hsigma : 1 < sigma)
    (D : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) :
    squarefreeMobiusCriticalFisherJoinedCodiagonal sigma hsigma
        (squarefreeMobiusCriticalFisherSourceRankOne sigma hsigma
          (D (infiniteMobiusSignedWeightLp sigma hsigma))) =
      squarefreeMobiusCriticalFisherJoinedCodiagonal sigma hsigma D := by
  funext u
  unfold squarefreeMobiusCriticalFisherJoinedCodiagonal
    GaloisForLFunctions.HTGeometry.infiniteFisherOneCornerJoinedReporter
  rw [squarefreeMobiusCriticalFisherSourceRankOne_apply_source]

/-- **Exact rank-one reporter reduction.**  Every contraction-generated
countable common reporter is literally the reporter of its one unit-ball
source vector. -/
theorem squarefreeMobiusCriticalFisherSourceVectorReporter_apply_contraction
    (sigma : ℝ) (hsigma : 1 < sigma)
    (D : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (hD : ‖D‖ ≤ 1) :
    squarefreeMobiusCriticalFisherSourceVectorReporter sigma hsigma
        (D (infiniteMobiusSignedWeightLp sigma hsigma))
        (contraction_apply_source_norm_le_one hsigma D hD) =
      squarefreeMobiusCriticalFisherCountableCommonHardyReporter
        sigma hsigma D hD := by
  unfold squarefreeMobiusCriticalFisherSourceVectorReporter
    squarefreeMobiusCriticalFisherCountableCommonHardyReporter
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun u =>
    congrFun
      (squarefreeMobiusCriticalFisherJoinedCodiagonal_rankOne
        sigma hsigma D) u

/-- Vector-only form of the exact Route-R selection gate.  Operator-valued
contractions are unnecessary: domination by reporters from one unit-ball
source vector at each depth already forces RH. -/
theorem
    riemannHypothesis_of_countertransportXiField_sq_norm_le_sourceVectorReporter
    (sigma : ℝ) (hsigma : 1 < sigma)
    (phi : ℝ → lp (fun _ : ℕ => ℂ) 2)
    (hphi : ∀ c, ‖phi c‖ ≤ 1)
    (K : ℝ) (hK : 0 ≤ K)
    (hdom : ∀ c : ℝ,
      ‖deningerMeyerReflectedGaussianCountertransportXiField c‖ ^ 2 ≤
        K *
          ‖squarefreeMobiusCriticalFisherSourceVectorReporter
            sigma hsigma (phi c) (hphi c)‖ ^ 2) :
    RiemannHypothesis := by
  let D : ℝ →
      (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) :=
    fun c =>
      squarefreeMobiusCriticalFisherSourceRankOne sigma hsigma (phi c)
  have hD : ∀ c, ‖D c‖ ≤ 1 := fun c => by
    dsimp only [D]
    exact norm_squarefreeMobiusCriticalFisherSourceRankOne_le_one
      sigma hsigma (hphi c)
  apply
    riemannHypothesis_of_countertransportXiField_sq_norm_le_countableReporter
      sigma hsigma D hD K hK
  intro c
  simpa only [D, squarefreeMobiusCriticalFisherSourceVectorReporter]
    using hdom c

end

end RHTower
