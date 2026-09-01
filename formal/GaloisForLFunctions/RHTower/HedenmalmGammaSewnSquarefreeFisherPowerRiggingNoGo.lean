import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherPhysicalHilbertWall
import GaloisForLFunctions.RHTower.MobiusChannelCriticalMassEscape
import GaloisForLFunctions.RHTower.SoninCofinalMobiusGammaXiIncidence
import GaloisForLFunctions.RHTower.CompleteResolutionCofinalConditioningLaw

/-!
# Fixed-power riggings cannot close the physical MSC graph

At a fixed spectral point `rho`, Dirichlet power damping `n ↦ n⁻ʳ` shifts the physical source
coordinate by `r / (sigma - 1)`.  The resulting squarefree-Möbius column is in `ell²` exactly for

`sigma < 2 Re rho + 2r - 1`.

Consequently every fixed power has an exact dichotomy.  If `r ≤ 1 - Re rho`, it never admits the
physical column for `sigma > 1`.  If `r > 1 - Re rho`, it admits a cofinal sequence, but the
normalized source vectors converge to zero while the residue-subtracted MSC regular output
converges to `2`.  Every closed linear relation retaining these pairs therefore has `(0,2)` in its
vertical fibre and cannot be single-valued.

This kills the full fixed-power rigged-Hilbert continuation branch.  The positive survivor is the
universal vertical value `2` (energy `4`): an MSC continuation must retain it in a genuinely
multivalued or non-power distributional completion.
-/

open Complex Filter Set Topology
open scoped BigOperators Topology

noncomputable section

namespace RHTower.HedenmalmThetaSource

/-- Physical MSC coordinate after a fixed Dirichlet power rigging `n ↦ n⁻ʳ`. -/
def mscPowerRiggedPhysicalZeroCoordinate
    (rho : ℂ) (r sigma : ℝ) : ℂ :=
  (rho - (sigma : ℂ) + (r : ℂ)) / ((sigma - 1 : ℝ) : ℂ)

/-- Right endpoint of the Hilbert-admissible physical interval. -/
def mscPowerRiggingAdmissionThreshold (rho : ℂ) (r : ℝ) : ℝ :=
  2 * rho.re + 2 * r - 1

theorem mscPowerRiggedPhysicalZeroCoordinate_eq_shift
    (rho : ℂ) (r : ℝ) (sigma : ℝ) :
    mscPowerRiggedPhysicalZeroCoordinate rho r sigma =
      mscPhysicalZeroCoordinate rho sigma +
        (r : ℂ) / ((sigma - 1 : ℝ) : ℂ) := by
  unfold mscPowerRiggedPhysicalZeroCoordinate mscPhysicalZeroCoordinate
  ring

/-- The shifted coordinate is literally the fixed coefficient rigging `n ↦ n⁻ʳ`. -/
theorem infiniteMobiusCriticalComplexDampedSignedWeight_powerRigged
    (rho : ℂ) (r : ℝ) {sigma : ℝ} (hsigma : sigma ≠ 1) (n : ℕ) :
    infiniteMobiusCriticalComplexDampedSignedWeight sigma
        (mscPowerRiggedPhysicalZeroCoordinate rho r sigma) n =
      Complex.exp (-((r * Real.log n : ℝ) : ℂ)) *
        infiniteMobiusCriticalComplexDampedSignedWeight sigma
          (mscPhysicalZeroCoordinate rho sigma) n := by
  rw [infiniteMobiusCriticalComplexDampedSignedWeight_eq_exp,
    infiniteMobiusCriticalComplexDampedSignedWeight_eq_exp,
    ← mul_assoc, ← Complex.exp_add]
  congr 1
  rw [mscPowerRiggedPhysicalZeroCoordinate_eq_shift rho r sigma]
  have heps : (((sigma - 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hsigma
  congr 1
  calc
    -(mscPhysicalZeroCoordinate rho sigma +
          (r : ℂ) / ((sigma - 1 : ℝ) : ℂ)) *
          ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ) =
        -(mscPhysicalZeroCoordinate rho sigma * ((sigma - 1 : ℝ) : ℂ) +
          ((r : ℂ) / ((sigma - 1 : ℝ) : ℂ)) *
            ((sigma - 1 : ℝ) : ℂ)) * ((Real.log n : ℝ) : ℂ) := by ring
    _ = -(mscPhysicalZeroCoordinate rho sigma * ((sigma - 1 : ℝ) : ℂ) +
          (r : ℂ)) * ((Real.log n : ℝ) : ℂ) := by
      rw [div_mul_cancel₀ _ heps]
    _ = -((r * Real.log n : ℝ) : ℂ) +
          -mscPhysicalZeroCoordinate rho sigma * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log n : ℝ) : ℂ) := by
      push_cast
      ring

theorem mscPowerRiggedPhysicalZeroCoordinate_re
    (rho : ℂ) (r : ℝ) {sigma : ℝ} (hsigma : sigma ≠ 1) :
    (mscPowerRiggedPhysicalZeroCoordinate rho r sigma).re =
      (rho.re - sigma + r) / (sigma - 1) := by
  have hnum : (rho - (sigma : ℂ) + (r : ℂ)).re = rho.re - sigma + r := by
    simp
  rw [mscPowerRiggedPhysicalZeroCoordinate, Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, add_zero, Complex.normSq_apply, hnum]
  field_simp [sub_ne_zero.mpr hsigma]
  ring

theorem summable_norm_sq_mscPowerRiggedPhysicalZeroSource_iff
    (rho : ℂ) (r : ℝ) {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma
        (mscPowerRiggedPhysicalZeroCoordinate rho r sigma) n‖ ^ 2) ↔
      sigma < mscPowerRiggingAdmissionThreshold rho r := by
  rw [summable_norm_sq_infiniteMobiusCriticalComplexDampedSignedWeight_iff hsigma,
    mscPowerRiggedPhysicalZeroCoordinate_re rho r hsigma.ne']
  unfold mscPowerRiggingAdmissionThreshold
  have hden : 0 < sigma - 1 := sub_pos.mpr hsigma
  rw [lt_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith

theorem not_summable_mscPowerRiggedPhysicalZeroSource_of_le
    (rho : ℂ) {r : ℝ} (hr : r ≤ 1 - rho.re)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ¬ Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma
        (mscPowerRiggedPhysicalZeroCoordinate rho r sigma) n‖ ^ 2) := by
  rw [summable_norm_sq_mscPowerRiggedPhysicalZeroSource_iff rho r hsigma]
  unfold mscPowerRiggingAdmissionThreshold
  linarith

theorem one_lt_mscPowerRiggingAdmissionThreshold_iff
    (rho : ℂ) (r : ℝ) :
    1 < mscPowerRiggingAdmissionThreshold rho r ↔ 1 - rho.re < r := by
  unfold mscPowerRiggingAdmissionThreshold
  constructor <;> intro h <;> linarith

/-- Canonical admitted sequence for a strong fixed power rigging. -/
def mscPowerRiggedCofinalSigma (rho : ℂ) (r : ℝ) (N : ℕ) : ℝ :=
  fixedEulerCofinalSigma (mscPowerRiggingAdmissionThreshold rho r) (N + 1)

theorem mscPowerRiggedCofinalSigma_gt_one
    (rho : ℂ) {r : ℝ} (hr : 1 - rho.re < r) (N : ℕ) :
    1 < mscPowerRiggedCofinalSigma rho r N := by
  apply fixedEulerCofinalSigma_gt_one
  exact (one_lt_mscPowerRiggingAdmissionThreshold_iff rho r).2 hr

theorem mscPowerRiggedCofinalSigma_lt_threshold
    (rho : ℂ) {r : ℝ} (hr : 1 - rho.re < r) (N : ℕ) :
    mscPowerRiggedCofinalSigma rho r N <
      mscPowerRiggingAdmissionThreshold rho r := by
  let b := mscPowerRiggingAdmissionThreshold rho r
  have hb : 1 < b := (one_lt_mscPowerRiggingAdmissionThreshold_iff rho r).2 hr
  have hden : 1 < ((N + 1 : ℕ) : ℝ) + 1 := by
    have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
    linarith
  have hpos : 0 < b - 1 := sub_pos.mpr hb
  have hdiv : (b - 1) / (((N + 1 : ℕ) : ℝ) + 1) < b - 1 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) + 1)]
    nlinarith
  simpa [mscPowerRiggedCofinalSigma, fixedEulerCofinalSigma, b] using
    (show 1 + (b - 1) / (((N + 1 : ℕ) : ℝ) + 1) < b by linarith)

private theorem tendsto_nat_succ_atTop :
    Tendsto (fun N : ℕ => N + 1) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  omega

theorem tendsto_mscPowerRiggedCofinalSigma_nhdsGT
    (rho : ℂ) {r : ℝ} (hr : 1 - rho.re < r) :
    Tendsto (mscPowerRiggedCofinalSigma rho r) atTop (𝓝[>] (1 : ℝ)) := by
  change Tendsto
    (fun N : ℕ => fixedEulerCofinalSigma
      (mscPowerRiggingAdmissionThreshold rho r) (N + 1)) atTop (𝓝[>] (1 : ℝ))
  exact (tendsto_fixedEulerCofinalSigma_nhdsWithin
    ((one_lt_mscPowerRiggingAdmissionThreshold_iff rho r).2 hr)).comp
      tendsto_nat_succ_atTop

/-- Actual `ell²` physical source along the canonical admitted sequence. -/
def mscPowerRiggedCofinalSourceLp
    (rho : ℂ) (r : ℝ) (hr : 1 - rho.re < r) (N : ℕ) :
    lp (fun _ : ℕ => ℂ) 2 :=
  let sigma := mscPowerRiggedCofinalSigma rho r N
  ⟨infiniteMobiusCriticalComplexDampedSignedWeight sigma
      (mscPowerRiggedPhysicalZeroCoordinate rho r sigma),
    HilbertSchmidt.memℓp_of_sq
      ((summable_norm_sq_mscPowerRiggedPhysicalZeroSource_iff rho r
        (mscPowerRiggedCofinalSigma_gt_one rho hr N)).2
          (mscPowerRiggedCofinalSigma_lt_threshold rho hr N))⟩

theorem mobiusCriticalBoundaryParameter_mscPowerRiggedPhysicalZeroCoordinate
    (rho : ℂ) (r : ℝ) {sigma : ℝ} (hsigma : sigma ≠ 1) :
    mobiusCriticalBoundaryParameter sigma
        (2 * (mscPowerRiggedPhysicalZeroCoordinate rho r sigma).re) =
      mscPowerRiggingAdmissionThreshold rho r + 1 - sigma := by
  rw [mscPowerRiggedPhysicalZeroCoordinate_re rho r hsigma]
  unfold mobiusCriticalBoundaryParameter mscPowerRiggingAdmissionThreshold
  field_simp [sub_ne_zero.mpr hsigma]
  ring

theorem norm_sq_mscPowerRiggedCofinalSourceLp
    (rho : ℂ) (r : ℝ) (hr : 1 - rho.re < r) (N : ℕ) :
    ‖mscPowerRiggedCofinalSourceLp rho r hr N‖ ^ 2 =
      squarefreeMobiusTotal
          (mscPowerRiggingAdmissionThreshold rho r + 1 -
            mscPowerRiggedCofinalSigma rho r N) /
        squarefreeMobiusTotal (mscPowerRiggedCofinalSigma rho r N) := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  change (∑' n : ℕ,
    ‖infiniteMobiusCriticalComplexDampedSignedWeight
      (mscPowerRiggedCofinalSigma rho r N)
      (mscPowerRiggedPhysicalZeroCoordinate rho r
        (mscPowerRiggedCofinalSigma rho r N)) n‖ ^ 2) = _
  rw [show (fun n : ℕ =>
      ‖infiniteMobiusCriticalComplexDampedSignedWeight
        (mscPowerRiggedCofinalSigma rho r N)
        (mscPowerRiggedPhysicalZeroCoordinate rho r
          (mscPowerRiggedCofinalSigma rho r N)) n‖ ^ 2) =
      squarefreeMobiusBoundaryLayerTerm
        (mscPowerRiggedCofinalSigma rho r N)
        (2 * (mscPowerRiggedPhysicalZeroCoordinate rho r
          (mscPowerRiggedCofinalSigma rho r N)).re) by
    funext n
    rw [norm_infiniteMobiusCriticalComplexDampedSignedWeight]
    exact norm_sq_infiniteMobiusCriticalDampedSignedWeight_eq_boundaryLayer
      (mscPowerRiggedCofinalSigma_gt_one rho hr N) n,
    tsum_squarefreeMobiusBoundaryLayerTerm,
    mobiusCriticalBoundaryParameter_mscPowerRiggedPhysicalZeroCoordinate
      rho r (mscPowerRiggedCofinalSigma_gt_one rho hr N).ne']

theorem squarefreeMobiusMass_antitone_exponent
    {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    squarefreeMobiusMass b n ≤ squarefreeMobiusMass a n := by
  rw [squarefreeMobiusMass, squarefreeMobiusMass]
  split_ifs with hn
  · have hnbase : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
        (fun hn0 => by subst n; exact not_squarefree_zero hn))
    exact Real.rpow_le_rpow_of_exponent_le hnbase (neg_le_neg hab)
  · exact le_rfl

theorem squarefreeMobiusTotal_antitone_on_one
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    squarefreeMobiusTotal b ≤ squarefreeMobiusTotal a := by
  unfold squarefreeMobiusTotal
  exact Summable.tsum_le_tsum (squarefreeMobiusMass_antitone_exponent hab)
    (summable_squarefreeMobiusMass (lt_of_lt_of_le ha hab))
    (summable_squarefreeMobiusMass ha)

theorem half_threshold_le_mscPowerRiggedCofinalParameter
    (rho : ℂ) {r : ℝ} (hr : 1 - rho.re < r) (N : ℕ) :
    (mscPowerRiggingAdmissionThreshold rho r + 1) / 2 ≤
      mscPowerRiggingAdmissionThreshold rho r + 1 -
        mscPowerRiggedCofinalSigma rho r N := by
  let b := mscPowerRiggingAdmissionThreshold rho r
  let d : ℝ := (((N + 1 : ℕ) : ℝ) + 1)
  have hb : 1 < b := (one_lt_mscPowerRiggingAdmissionThreshold_iff rho r).2 hr
  have hd : 0 < d := by dsimp [d]; positivity
  have hd2 : 2 ≤ d := by
    dsimp [d]
    norm_num
    nlinarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N]
  have hpos : 0 ≤ b - 1 := (sub_pos.mpr hb).le
  have hfrac : (b - 1) / d ≤ (b - 1) / 2 := by
    rw [div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_nonneg hpos (sub_nonneg.mpr hd2)]
  change (b + 1) / 2 ≤ b + 1 - fixedEulerCofinalSigma b (N + 1)
  simp only [fixedEulerCofinalSigma]
  change (b + 1) / 2 ≤ b + 1 - (1 + (b - 1) / d)
  linarith

theorem norm_sq_mscPowerRiggedCofinalSourceLp_le
    (rho : ℂ) (r : ℝ) (hr : 1 - rho.re < r) (N : ℕ) :
    ‖mscPowerRiggedCofinalSourceLp rho r hr N‖ ^ 2 ≤
      squarefreeMobiusTotal
          ((mscPowerRiggingAdmissionThreshold rho r + 1) / 2) *
        (squarefreeMobiusTotal (mscPowerRiggedCofinalSigma rho r N))⁻¹ := by
  rw [norm_sq_mscPowerRiggedCofinalSourceLp, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right
  · apply squarefreeMobiusTotal_antitone_on_one
    · have hb := (one_lt_mscPowerRiggingAdmissionThreshold_iff rho r).2 hr
      linarith
    · exact half_threshold_le_mscPowerRiggedCofinalParameter rho hr N
  · exact inv_nonneg.mpr (squarefreeMobiusTotal_pos
      (mscPowerRiggedCofinalSigma_gt_one rho hr N)).le

theorem tendsto_norm_sq_mscPowerRiggedCofinalSourceLp_zero
    (rho : ℂ) (r : ℝ) (hr : 1 - rho.re < r) :
    Tendsto (fun N : ℕ => ‖mscPowerRiggedCofinalSourceLp rho r hr N‖ ^ 2)
      atTop (𝓝 0) := by
  have hinv : Tendsto
      (fun N : ℕ =>
        (squarefreeMobiusTotal (mscPowerRiggedCofinalSigma rho r N))⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_squarefreeMobiusTotal_zero.comp
      (tendsto_mscPowerRiggedCofinalSigma_nhdsGT rho hr)
  have hupper : Tendsto
      (fun N : ℕ =>
        squarefreeMobiusTotal
            ((mscPowerRiggingAdmissionThreshold rho r + 1) / 2) *
          (squarefreeMobiusTotal (mscPowerRiggedCofinalSigma rho r N))⁻¹)
      atTop (𝓝 0) := by
    simpa using hinv.const_mul
      (squarefreeMobiusTotal
        ((mscPowerRiggingAdmissionThreshold rho r + 1) / 2))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun N => sq_nonneg _)
    (Filter.Eventually.of_forall fun N =>
      norm_sq_mscPowerRiggedCofinalSourceLp_le rho r hr N)

theorem tendsto_mscPowerRiggedCofinalSourceLp_zero
    (rho : ℂ) (r : ℝ) (hr : 1 - rho.re < r) :
    Tendsto (mscPowerRiggedCofinalSourceLp rho r hr) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsquare := tendsto_norm_sq_mscPowerRiggedCofinalSourceLp_zero rho r hr
  rw [Metric.tendsto_atTop] at hsquare
  obtain ⟨N, hN⟩ := hsquare (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hsq := hN n hn
  have hsq' : ‖mscPowerRiggedCofinalSourceLp rho r hr n‖ ^ 2 < ε ^ 2 := by
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (sq_nonneg
        ‖mscPowerRiggedCofinalSourceLp rho r hr n‖)] at hsq
    exact hsq
  rw [dist_zero_right]
  nlinarith [norm_nonneg (mscPowerRiggedCofinalSourceLp rho r hr n)]

theorem tendsto_mscPhysicalRegularGerm_powerRiggedCofinal
    (rho : ℂ) (g : ℂ → ℂ) {r : ℝ} (hr : 1 - rho.re < r) :
    Tendsto
      (fun N : ℕ =>
        mscPhysicalRegularGerm rho g (mscPowerRiggedCofinalSigma rho r N)
          (mscPhysicalZeroCoordinate rho
            (mscPowerRiggedCofinalSigma rho r N)))
      atTop (𝓝 2) :=
  (tendsto_mscPhysicalRegularGerm_at_zeroCoordinate rho g).comp
    (tendsto_mscPowerRiggedCofinalSigma_nhdsGT rho hr)

/-- Every closed linear completion retaining the admitted power-rigged MSC graph has the universal
regular response `2` in its vertical fibre. -/
theorem mscPowerRigged_closedLinearRelation_vertical_two
    (rho : ℂ) (g : ℂ → ℂ) (r : ℝ) (hr : 1 - rho.re < r)
    (R : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2 × ℂ))
    (hclosed : IsClosed (R : Set (lp (fun _ : ℕ => ℂ) 2 × ℂ)))
    (hgraph : ∀ N : ℕ,
      (mscPowerRiggedCofinalSourceLp rho r hr N,
        mscPhysicalRegularGerm rho g (mscPowerRiggedCofinalSigma rho r N)
          (mscPhysicalZeroCoordinate rho
            (mscPowerRiggedCofinalSigma rho r N))) ∈ R) :
    (2 : ℂ) ∈ linearRelationVerticalFiber R := by
  exact closedLinearRelation_mem_vertical_of_graph_tendsto
    R hclosed
      (mscPowerRiggedCofinalSourceLp rho r hr)
      (fun N : ℕ =>
        mscPhysicalRegularGerm rho g (mscPowerRiggedCofinalSigma rho r N)
          (mscPhysicalZeroCoordinate rho
            (mscPowerRiggedCofinalSigma rho r N)))
      2
      (tendsto_mscPowerRiggedCofinalSourceLp_zero rho r hr)
      (tendsto_mscPhysicalRegularGerm_powerRiggedCofinal rho g hr)
      hgraph

/-- **Fixed-power MSC graph no-go.** No closed single-valued linear relation can retain the
cofinal physical regular-germ pairs for any power strong enough to admit them. -/
theorem not_exists_closed_singleValued_mscPowerRiggedGraph
    (rho : ℂ) (g : ℂ → ℂ) (r : ℝ) (hr : 1 - rho.re < r) :
    ¬ ∃ R : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2 × ℂ),
      IsClosed (R : Set (lp (fun _ : ℕ => ℂ) 2 × ℂ)) ∧
      (∀ y : ℂ, ((0 : lp (fun _ : ℕ => ℂ) 2), y) ∈ R → y = 0) ∧
      (∀ N : ℕ,
        (mscPowerRiggedCofinalSourceLp rho r hr N,
          mscPhysicalRegularGerm rho g (mscPowerRiggedCofinalSigma rho r N)
            (mscPhysicalZeroCoordinate rho
              (mscPowerRiggedCofinalSigma rho r N))) ∈ R) := by
  rintro ⟨R, hclosed, hsingle, hgraph⟩
  have htwo := mscPowerRigged_closedLinearRelation_vertical_two
    rho g r hr R hclosed hgraph
  have hzero : (2 : ℂ) = 0 := hsingle 2 htwo
  norm_num at hzero

/-- At an actual strict-right Xi zero, the residue-split MSC germ supplied by the arithmetic source
cannot be retained by any closed single-valued fixed-power Hilbert graph. -/
theorem strictRightXiZero_exists_mscPowerRiggedGraphNoGo
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1)
    (hzero : xi rho = 0) (r : ℝ) (hr : 1 - rho.re < r) :
    ∃ k : ℕ, analyticOrderAt xi rho = (k + 1 : ℕ) ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho ∧
        (∀ sigma : ℝ, 1 < sigma →
          AnalyticAt ℂ (mscPhysicalRegularGerm rho g sigma)
              (mscPhysicalZeroCoordinate rho sigma) ∧
            (fun v =>
              GaloisForLFunctions.squarefreeFisherScore
                  (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v /
                GaloisForLFunctions.squarefreeBoundaryOverlap
                  (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v) =ᶠ[
              𝓝[≠] (mscPhysicalZeroCoordinate rho sigma)]
                fun v => 2 * ((k + 1 : ℕ) : ℂ) /
                  (v - mscPhysicalZeroCoordinate rho sigma) +
                    mscPhysicalRegularGerm rho g sigma v) ∧
        ¬ ∃ R : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2 × ℂ),
          IsClosed (R : Set (lp (fun _ : ℕ => ℂ) 2 × ℂ)) ∧
          (∀ y : ℂ, ((0 : lp (fun _ : ℕ => ℂ) 2), y) ∈ R → y = 0) ∧
          (∀ N : ℕ,
            (mscPowerRiggedCofinalSourceLp rho r hr N,
              mscPhysicalRegularGerm rho g
                (mscPowerRiggedCofinalSigma rho r N)
                (mscPhysicalZeroCoordinate rho
                  (mscPowerRiggedCofinalSigma rho r N))) ∈ R) := by
  obtain ⟨k, hk, g, hg, hsplit, _⟩ :=
    exists_mscPhysicalRegularGerm_residueSplit_tendsto_four hhalf hone hzero
  exact ⟨k, hk, g, hg, hsplit,
    not_exists_closed_singleValued_mscPowerRiggedGraph rho g r hr⟩

end RHTower.HedenmalmThetaSource
