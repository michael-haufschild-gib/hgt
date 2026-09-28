import GaloisForLFunctions.RHTower.MertensPrimeCellClock
import GaloisForLFunctions.RHTower.WeylSpectrumCompactTransfer
import GaloisForLFunctions.RHTower.STCPoissonPrimePhysicalClockWall
import GaloisForLFunctions.HTGeometry.SechSquareConvolutionKernel
import GaloisForLFunctions.HTGeometry.WienerHopfPlaneWaveWeyl
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.RHTower.STCPrimeHeightCalkinGhost

/-!
# The Calkin model of the all-aperture prime Poisson kernel

The full-aperture prime Poisson kernel on `ℓ²(primes)` is

`K(p,q) = 4 log p log q / (√(pq) (log p + log q)²) = (pq)^{-1/2} h(x_p - x_q)`,

with `h(s) = sech²(s/2)` and the Mertens clock `x_p = log log p`.  Put the prime `p` on the cell
`I_p = [y_p, y_p + 1/p)`, `y_p = ∑_{q<p} 1/q`, of the half-line, and let `U δ_p = p^{1/2} 1_{I_p}`.
Then `U` is an isometry of `ℓ²(primes)` onto the step functions, and

`K = U* A U`,   `A` = the integral operator with the step kernel `h(φ(y) - φ(z))`,

where `φ = log log p + B` on `I_p` is the Mertens step clock.  Mertens' second theorem with decaying
error gives `|φ(y) - y| ≤ D e^{-y}`, so `A - W` is Hilbert–Schmidt, where `W` is the Wiener–Hopf
operator with kernel `h(y - z)`.  The same holds for the tilted profile `j(s) = s h(s)`, whose
compression is the matrix `(x_p - x_q) K(p,q)`.

Consequences proved here: `K` is bounded, positive and self-adjoint; `0 ≤ W ≤ 4`; the Weyl spectra of
`W` and of `K` are both `[0, 4]`; `‖K‖_ess = 4`, so `K` is not compact.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2
local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-! ### The half-line clock -/

/-- The decay constant `D` of `|φ(y) - y| ≤ D e^{-y}`. -/
def poissonClockConst : ℝ := Classical.choose exists_abs_mertensStepClock_sub_le

theorem poissonClockConst_nonneg : 0 ≤ poissonClockConst :=
  (Classical.choose_spec exists_abs_mertensStepClock_sub_le).1

/-- The Mertens step clock on `[0, ∞)`, continued by the identity to the left. -/
def poissonClock (y : ℝ) : ℝ := if 0 ≤ y then mertensStepClock y else y

theorem measurable_poissonClock : Measurable poissonClock :=
  Measurable.ite measurableSet_Ici measurable_mertensStepClock measurable_id

theorem abs_poissonClock_sub_le {y : ℝ} (hy : 0 ≤ y) :
    |poissonClock y - y| ≤ poissonClockConst * Real.exp (-y) := by
  rw [poissonClock, if_pos hy]
  exact (Classical.choose_spec exists_abs_mertensStepClock_sub_le).2 y hy

theorem abs_poissonClock_sub_le_const (y : ℝ) : |poissonClock y - y| ≤ poissonClockConst := by
  by_cases hy : 0 ≤ y
  · refine (abs_poissonClock_sub_le hy).trans ?_
    have : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [poissonClockConst_nonneg]
  · rw [poissonClock, if_neg hy, sub_self, abs_zero]
    exact poissonClockConst_nonneg

theorem poissonClock_of_mem {p : ℕ} (hp : p.Prime) {y : ℝ} (hy : y ∈ primeCell p) :
    poissonClock y = Real.log (Real.log p) + Sieve.meisselMertensConst := by
  rw [poissonClock, if_pos (show (0 : ℝ) ≤ y from primeCell_subset_Ici p hy),
    mertensStepClock_of_mem hp hy]

/-! ### The profile at prime clocks -/

theorem sechSqHalf_log_sub_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    sechSqHalf (Real.log a - Real.log b) = 4 * a * b / (a + b) ^ 2 := by
  rw [sechSqHalf, Real.exp_sub, Real.exp_log ha, Real.exp_log hb]
  field_simp
  ring

theorem stcClock_pos' (p : Nat.Primes) : 0 < stcClock p := by
  unfold stcClock
  exact Real.log_pos (by exact_mod_cast p.prop.one_lt)

/-- The Mertens clock `x_p = log log p`. -/
def mertensPrimeClock (p : Nat.Primes) : ℝ := Real.log (stcClock p)

/-- `K(p,q) = (pq)^{-1/2} h(x_p - x_q)`. -/
theorem stcPrimePoissonKernel_eq_sechSqHalf (p q : Nat.Primes) :
    stcPrimePoissonKernel p q =
      sechSqHalf (mertensPrimeClock p - mertensPrimeClock q) /
        (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) := by
  rw [mertensPrimeClock, mertensPrimeClock, sechSqHalf_log_sub_log (stcClock_pos' p)
    (stcClock_pos' q), stcPrimePoissonKernel]
  rw [div_div, mul_comm (Real.sqrt _ * Real.sqrt _)]

/-! ### Prime cells in `L²(0, ∞)` -/

theorem halfLineMeasure_primeCell (p : ℕ) :
    halfLineMeasure (primeCell p) = ENNReal.ofReal (1 / p) := by
  rw [halfLineMeasure, Measure.restrict_apply (measurableSet_primeCell p),
    Set.inter_eq_left.mpr (primeCell_subset_Ici p), volume_primeCell]

theorem halfLineMeasure_primeCell_ne_top (p : Nat.Primes) :
    halfLineMeasure (primeCell p) ≠ ∞ := by
  rw [halfLineMeasure_primeCell]; exact ENNReal.ofReal_ne_top

theorem halfLineMeasure_primeCell_ne_zero (p : Nat.Primes) :
    halfLineMeasure (primeCell p) ≠ 0 := by
  rw [halfLineMeasure_primeCell, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  positivity

theorem halfLineMeasure_real_primeCell (p : Nat.Primes) :
    halfLineMeasure.real (primeCell p) = 1 / (p : ℕ) := by
  rw [measureReal_def, halfLineMeasure_primeCell, ENNReal.toReal_ofReal (by positivity)]

/-- The normalized prime cell vector `p^{1/2} 1_{I_p}`. -/
def primeCellVec (p : Nat.Primes) : L²₊ :=
  SchurKernel.cellVec (fun p : Nat.Primes => primeCell p) (fun p => measurableSet_primeCell p)
    halfLineMeasure_primeCell_ne_top p

theorem orthonormal_primeCellVec : Orthonormal ℂ primeCellVec :=
  SchurKernel.orthonormal_cellVec (fun p : Nat.Primes => primeCell p)
    (fun p => measurableSet_primeCell p) halfLineMeasure_primeCell_ne_top
    halfLineMeasure_primeCell_ne_zero pairwise_disjoint_primeCell

theorem cellConst_primeCell (p : Nat.Primes) :
    SchurKernel.cellConst (μ := halfLineMeasure) (fun p : Nat.Primes => primeCell p) p =
      Real.sqrt (p : ℕ) := by
  rw [SchurKernel.cellConst, halfLineMeasure_primeCell, ENNReal.toReal_ofReal (by positivity),
    Real.sqrt_eq_rpow, one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  ring_nf

/-! ### The cell isometry -/

/-- The cell isometry `U δ_p = p^{1/2} 1_{I_p}`. -/
def primeCellIsometry : ℓ²P →ₗᵢ[ℂ] L²₊ :=
  orthonormal_primeCellVec.orthogonalFamily.linearIsometry

/-- The cell isometry as a bounded operator. -/
def primeCellOp : ℓ²P →L[ℂ] L²₊ := primeCellIsometry.toContinuousLinearMap

theorem primeCellOp_single (p : Nat.Primes) :
    primeCellOp (lp.single 2 p (1 : ℂ)) = primeCellVec p := by
  classical
  rw [primeCellOp, LinearIsometry.coe_toContinuousLinearMap, primeCellIsometry,
    OrthogonalFamily.linearIsometry_apply_single]
  simp

theorem primeCellOp_lpBasisVec (p : Nat.Primes) :
    primeCellOp (lpBasisVec p) = primeCellVec p := primeCellOp_single p

theorem norm_primeCellOp_apply (f : ℓ²P) : ‖primeCellOp f‖ = ‖f‖ :=
  primeCellIsometry.norm_map f

theorem adjoint_primeCellOp_comp : primeCellOp.adjoint ∘L primeCellOp = ContinuousLinearMap.id ℂ ℓ²P :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self primeCellOp).mp norm_primeCellOp_apply

theorem coord_eq_inner (f : ℓ²P) (p : Nat.Primes) :
    (f : Nat.Primes → ℂ) p = inner ℂ (lpBasisVec p) f := by
  classical
  rw [lpBasisVec, lp.inner_single_left]
  simp

theorem adjoint_primeCellOp_apply (g : L²₊) (p : Nat.Primes) :
    (primeCellOp.adjoint g : Nat.Primes → ℂ) p = inner ℂ (primeCellVec p) g := by
  rw [coord_eq_inner, ContinuousLinearMap.adjoint_inner_right, primeCellOp_lpBasisVec]

/-! ### The kernels -/

theorem lintegral_enorm_sechSqHalf_sub (y : ℝ) :
    ∫⁻ z, ‖((sechSqHalf (y - z) : ℝ) : ℂ)‖ₑ = 4 := by
  have hpt : ∀ z, ‖((sechSqHalf (y - z) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (sechSqHalf (y - z)) := by
    intro z
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sechSqHalf_pos _)]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sechSqHalf.comp_sub_left y)
    (Eventually.of_forall fun z => (sechSqHalf_pos _).le),
    integral_sub_left_eq_self sechSqHalf volume y, integral_sechSqHalf]
  simp

/-- The Wiener–Hopf kernel `h(y - z)` on the half-line; Schur bound `∫ h = 4`. -/
def wienerHopfSechKernel : SchurKernel halfLineMeasure where
  toFun y z := (sechSqHalf (y - z) : ℂ)
  measurable := Complex.measurable_ofReal.comp
    (measurable_sechSqHalf.comp (measurable_fst.sub measurable_snd))
  bound := 4
  row y := (setLIntegral_le_lintegral _ _).trans (by rw [lintegral_enorm_sechSqHalf_sub]; simp)
  col z := by
    refine (setLIntegral_le_lintegral _ _).trans ?_
    have h : ∀ y, ‖((sechSqHalf (y - z) : ℝ) : ℂ)‖ₑ = ‖((sechSqHalf (z - y) : ℝ) : ℂ)‖ₑ := by
      intro y; rw [← neg_sub, sechSqHalf_neg]
    simp_rw [h]
    rw [lintegral_enorm_sechSqHalf_sub]; simp

/-- The Schur bound of a clock kernel with profile `|g| ≤ M e^{-α|s|}`. -/
def clockKernelBound (M α : ℝ) : ℝ≥0 :=
  Real.toNNReal (M * Real.exp (α * (2 * poissonClockConst)) * (2 / α))

/-- The clock kernel `g(φ(y) - φ(z))` of an exponentially decaying profile. -/
def clockKernel (g : ℝ → ℝ) (hg : Measurable g) {M α : ℝ} (hM : 0 ≤ M) (hα : 0 < α)
    (hgb : ∀ s, |g s| ≤ M * Real.exp (-(α * |s|))) : SchurKernel halfLineMeasure where
  toFun y z := (g (poissonClock y - poissonClock z) : ℂ)
  measurable := Complex.measurable_ofReal.comp
    (hg.comp ((measurable_poissonClock.comp measurable_fst).sub
      (measurable_poissonClock.comp measurable_snd)))
  bound := clockKernelBound M α
  row y := (setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_clock_kernel_le hM hα hgb abs_poissonClock_sub_le_const y)
  col z := (setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_clock_kernel_le' hM hα hgb abs_poissonClock_sub_le_const z)

/-- The step kernel `h(φ(y) - φ(z))`. -/
def mertensStepSechKernel : SchurKernel halfLineMeasure :=
  clockKernel sechSqHalf measurable_sechSqHalf (by norm_num) one_pos abs_sechSqHalf_le

/-- The tilted Wiener–Hopf kernel `j(y - z)`, `j(s) = s h(s)`. -/
def wienerHopfTiltKernel : SchurKernel halfLineMeasure where
  toFun y z := (sechSqHalfTilt (y - z) : ℂ)
  measurable := Complex.measurable_ofReal.comp
    (continuous_sechSqHalfTilt.measurable.comp (measurable_fst.sub measurable_snd))
  bound := Real.toNNReal (8 * Real.exp ((1 / 2) * (2 * 0)) * (2 / (1 / 2)))
  row y := (setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_clock_kernel_le (φ := id) (by norm_num) (by norm_num) abs_sechSqHalfTilt_le
      (fun y => by simp) y)
  col z := (setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_clock_kernel_le' (φ := id) (by norm_num) (by norm_num) abs_sechSqHalfTilt_le
      (fun y => by simp) z)

/-- The tilted step kernel `j(φ(y) - φ(z))`. -/
def mertensStepTiltKernel : SchurKernel halfLineMeasure :=
  clockKernel sechSqHalfTilt continuous_sechSqHalfTilt.measurable (by norm_num) (by norm_num)
    abs_sechSqHalfTilt_le

/-- The Wiener–Hopf operator `W`. -/
def wienerHopfSechOp : L²₊ →L[ℂ] L²₊ := wienerHopfSechKernel.op

/-- The step operator `A`. -/
def mertensStepSechOp : L²₊ →L[ℂ] L²₊ := mertensStepSechKernel.op

/-- The tilted Wiener–Hopf operator `W_j`. -/
def wienerHopfTiltOp : L²₊ →L[ℂ] L²₊ := wienerHopfTiltKernel.op

/-- The tilted step operator `A_j`. -/
def mertensStepTiltOp : L²₊ →L[ℂ] L²₊ := mertensStepTiltKernel.op

/-! ### The compressed prime operators -/

/-- The all-aperture prime Poisson operator `K = U* A U`. -/
def poissonPrimeOp : ℓ²P →L[ℂ] ℓ²P := primeCellOp.adjoint ∘L mertensStepSechOp ∘L primeCellOp

/-- The compressed clock commutator `C = U* A_j U`. -/
def poissonPrimeCommOp : ℓ²P →L[ℂ] ℓ²P :=
  primeCellOp.adjoint ∘L mertensStepTiltOp ∘L primeCellOp

theorem mertensStepSechKernel_toFun_of_mem {p q : Nat.Primes} {y z : ℝ} (hy : y ∈ primeCell p)
    (hz : z ∈ primeCell q) :
    mertensStepSechKernel.toFun y z = (sechSqHalf (mertensPrimeClock p - mertensPrimeClock q) : ℂ) := by
  change ((sechSqHalf (poissonClock y - poissonClock z) : ℝ) : ℂ) = _
  rw [poissonClock_of_mem p.prop hy, poissonClock_of_mem q.prop hz, mertensPrimeClock,
    mertensPrimeClock, stcClock, stcClock]
  congr 2
  ring

theorem mertensStepTiltKernel_toFun_of_mem {p q : Nat.Primes} {y z : ℝ} (hy : y ∈ primeCell p)
    (hz : z ∈ primeCell q) :
    mertensStepTiltKernel.toFun y z =
      (sechSqHalfTilt (mertensPrimeClock p - mertensPrimeClock q) : ℂ) := by
  change ((sechSqHalfTilt (poissonClock y - poissonClock z) : ℝ) : ℂ) = _
  rw [poissonClock_of_mem p.prop hy, poissonClock_of_mem q.prop hz, mertensPrimeClock,
    mertensPrimeClock, stcClock, stcClock]
  congr 2
  ring

/-- Matrix elements of a kernel that is constant on the cell rectangle `I_p × I_q`. -/
theorem inner_primeCellVec_op_of_const (k : SchurKernel halfLineMeasure) {p q : Nat.Primes} {c : ℂ}
    (hk : ∀ y ∈ primeCell p, ∀ z ∈ primeCell q, k.toFun y z = c) :
    inner ℂ (primeCellVec p) (k.op (primeCellVec q)) =
      c / ((Real.sqrt (p : ℕ) * Real.sqrt (q : ℕ) : ℝ) : ℂ) := by
  rw [primeCellVec, primeCellVec, SchurKernel.inner_cellVec_op, cellConst_primeCell,
    cellConst_primeCell]
  have hin : ∀ y ∈ primeCell p, ∫ z in primeCell q, k.toFun y z ∂halfLineMeasure =
      ((1 / (q : ℕ) : ℝ) : ℂ) * c := by
    intro y hy
    rw [setIntegral_congr_fun (measurableSet_primeCell q) (fun z hz => hk y hy z hz),
      setIntegral_const, halfLineMeasure_real_primeCell, Complex.real_smul]
  rw [setIntegral_congr_fun (measurableSet_primeCell p) hin, setIntegral_const,
    halfLineMeasure_real_primeCell, Complex.real_smul]
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  have hq : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.prop.pos
  have hsp := Real.sq_sqrt hp.le
  have hsq := Real.sq_sqrt hq.le
  have hsp0 : Real.sqrt (p : ℕ) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hsq0 : Real.sqrt (q : ℕ) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have e1 : (1 / ((p : ℕ) : ℝ)) = 1 / Real.sqrt (p : ℕ) ^ 2 := by rw [hsp]
  have e2 : (1 / ((q : ℕ) : ℝ)) = 1 / Real.sqrt (q : ℕ) ^ 2 := by rw [hsq]
  rw [e1, e2]
  have hsp0' : ((Real.sqrt (p : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsp0
  have hsq0' : ((Real.sqrt (q : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq0
  push_cast
  field_simp

/-- **The matrix of `K`.**  `⟪δ_p, K δ_q⟫ = K(p,q)`. -/
theorem hasLpMatrix_poissonPrimeOp :
    HasLpMatrix poissonPrimeOp fun p q => (stcPrimePoissonKernel p q : ℂ) := by
  intro p q
  show _ = ((stcPrimePoissonKernel p q : ℝ) : ℂ)
  rw [coord_eq_inner, poissonPrimeOp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply, primeCellOp_lpBasisVec,
    primeCellOp_lpBasisVec, mertensStepSechOp,
    inner_primeCellVec_op_of_const _ fun y hy z hz => mertensStepSechKernel_toFun_of_mem hy hz,
    stcPrimePoissonKernel_eq_sechSqHalf]
  push_cast
  ring

/-- **The matrix of `C`.**  `⟪δ_p, C δ_q⟫ = (x_p - x_q) K(p,q)`. -/
theorem hasLpMatrix_poissonPrimeCommOp :
    HasLpMatrix poissonPrimeCommOp fun p q =>
      ((mertensPrimeClock p - mertensPrimeClock q) * stcPrimePoissonKernel p q : ℂ) := by
  intro p q
  show _ = ((mertensPrimeClock p : ℂ) - mertensPrimeClock q) * (stcPrimePoissonKernel p q : ℂ)
  rw [coord_eq_inner, poissonPrimeCommOp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply, primeCellOp_lpBasisVec,
    primeCellOp_lpBasisVec, mertensStepTiltOp,
    inner_primeCellVec_op_of_const _ fun y hy z hz => mertensStepTiltKernel_toFun_of_mem hy hz,
    stcPrimePoissonKernel_eq_sechSqHalf, sechSqHalfTilt]
  push_cast
  ring

/-! ### Symmetry and positivity -/

theorem isSelfAdjoint_wienerHopfSechOp : IsSelfAdjoint wienerHopfSechOp :=
  SchurKernel.isSelfAdjoint_op _ fun y z => by
    change (starRingEnd ℂ) ((sechSqHalf (z - y) : ℝ) : ℂ) = ((sechSqHalf (y - z) : ℝ) : ℂ)
    rw [Complex.conj_ofReal, ← neg_sub, sechSqHalf_neg]

theorem isSelfAdjoint_mertensStepSechOp : IsSelfAdjoint mertensStepSechOp :=
  SchurKernel.isSelfAdjoint_op _ fun y z => by
    change (starRingEnd ℂ) ((sechSqHalf (poissonClock z - poissonClock y) : ℝ) : ℂ) =
      ((sechSqHalf (poissonClock y - poissonClock z) : ℝ) : ℂ)
    rw [Complex.conj_ofReal, ← neg_sub, sechSqHalf_neg]

theorem adjoint_mertensStepTiltOp :
    ContinuousLinearMap.adjoint mertensStepTiltOp = -mertensStepTiltOp := by
  rw [mertensStepTiltOp, SchurKernel.adjoint_op]
  refine SchurKernel.op_eq_neg_of_toFun fun y z => ?_
  change (starRingEnd ℂ) ((sechSqHalfTilt (poissonClock z - poissonClock y) : ℝ) : ℂ) =
    -((sechSqHalfTilt (poissonClock y - poissonClock z) : ℝ) : ℂ)
  rw [Complex.conj_ofReal, ← neg_sub, sechSqHalfTilt_neg]
  push_cast; ring

theorem re_inner_wienerHopfSechOp_nonneg (f : L²₊) : 0 ≤ (inner ℂ f (wienerHopfSechOp f)).re :=
  SchurKernel.re_inner_op_nonneg_of_sechSqHalf _ measurable_id (fun _ _ => rfl) f

theorem re_inner_mertensStepSechOp_nonneg (f : L²₊) :
    0 ≤ (inner ℂ f (mertensStepSechOp f)).re :=
  SchurKernel.re_inner_op_nonneg_of_sechSqHalf _ measurable_poissonClock (fun _ _ => rfl) f

theorem norm_wienerHopfSechOp_le : ‖wienerHopfSechOp‖ ≤ 4 := by
  have h := SchurKernel.norm_op_le wienerHopfSechKernel
  have hb : (wienerHopfSechKernel.bound : ℝ) = 4 := by simp [wienerHopfSechKernel]
  rw [hb] at h
  exact h

theorem re_inner_wienerHopfSechOp_le (f : L²₊) :
    (inner ℂ f (wienerHopfSechOp f)).re ≤ 4 * ‖f‖ ^ 2 := by
  calc (inner ℂ f (wienerHopfSechOp f)).re ≤ ‖inner ℂ f (wienerHopfSechOp f)‖ :=
        Complex.re_le_norm _
    _ ≤ ‖f‖ * ‖wienerHopfSechOp f‖ := norm_inner_le_norm _ _
    _ ≤ ‖f‖ * (4 * ‖f‖) := by
        gcongr
        exact (wienerHopfSechOp.le_opNorm f).trans
          (mul_le_mul_of_nonneg_right norm_wienerHopfSechOp_le (norm_nonneg _))
    _ = 4 * ‖f‖ ^ 2 := by ring

theorem isPositive_of_re_inner_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) (hpos : ∀ f, 0 ≤ (inner ℂ f (T f)).re) :
    T.IsPositive := by
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨hT.isSymmetric, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_conj_symm, RCLike.conj_re]
  exact hpos x

/-- **`0 ≤ W ≤ 4`.** -/
theorem isPositive_wienerHopfSechOp : wienerHopfSechOp.IsPositive :=
  isPositive_of_re_inner_nonneg isSelfAdjoint_wienerHopfSechOp re_inner_wienerHopfSechOp_nonneg

theorem isSelfAdjoint_poissonPrimeOp : IsSelfAdjoint poissonPrimeOp :=
  isSelfAdjoint_mertensStepSechOp.adjoint_conj primeCellOp

theorem re_inner_poissonPrimeOp_nonneg (f : ℓ²P) : 0 ≤ (inner ℂ f (poissonPrimeOp f)).re := by
  rw [poissonPrimeOp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply]
  exact re_inner_mertensStepSechOp_nonneg _

/-- **`K` is a bounded positive self-adjoint operator.** -/
theorem isPositive_poissonPrimeOp : poissonPrimeOp.IsPositive :=
  isPositive_of_re_inner_nonneg isSelfAdjoint_poissonPrimeOp re_inner_poissonPrimeOp_nonneg

/-- **`C` is skew-adjoint.** -/
theorem adjoint_poissonPrimeCommOp :
    ContinuousLinearMap.adjoint poissonPrimeCommOp = -poissonPrimeCommOp := by
  rw [poissonPrimeCommOp, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, adjoint_mertensStepTiltOp]
  ext1 f
  simp

/-! ### The step operators live on the step functions -/

/-- `⟪p^{1/2} 1_{I_p}, g⟫ = p^{1/2} ∫_{I_p} g`. -/
theorem inner_primeCellVec_eq (p : Nat.Primes) (g : L²₊) :
    inner ℂ (primeCellVec p) g =
      ((Real.sqrt (p : ℕ) : ℝ) : ℂ) * ∫ z in primeCell p, (g : ℝ → ℂ) z ∂halfLineMeasure := by
  rw [primeCellVec, SchurKernel.cellVec, L2.inner_def, ← integral_const_mul]
  have hcoe := indicatorConstLp_coeFn (p := 2) (μ := halfLineMeasure)
    (hs := measurableSet_primeCell p) (hμs := halfLineMeasure_primeCell_ne_top p)
    (c := ((SchurKernel.cellConst (μ := halfLineMeasure) (fun p : Nat.Primes => primeCell p) p : ℝ) : ℂ))
  rw [← integral_indicator (measurableSet_primeCell p)]
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with z hz
  rw [hz, RCLike.inner_apply, cellConst_primeCell]
  by_cases hzp : z ∈ primeCell p
  · simp only [Set.indicator_of_mem hzp, Complex.conj_ofReal]
    ring
  · simp [Set.indicator_of_notMem hzp]

/-- A step kernel annihilates every vector orthogonal to all prime cells. -/
theorem clockKernel_op_eq_zero (g : ℝ → ℝ) (hg : Measurable g) {M α : ℝ} (hM : 0 ≤ M) (hα : 0 < α)
    (hgb : ∀ s, |g s| ≤ M * Real.exp (-(α * |s|))) {f : L²₊}
    (hf : ∀ p, inner ℂ (primeCellVec p) f = 0) : (clockKernel g hg hM hα hgb).op f = 0 := by
  set k := clockKernel g hg hM hα hgb
  have hcell : ∀ p : Nat.Primes, ∫ z in primeCell p, (f : ℝ → ℂ) z ∂halfLineMeasure = 0 := by
    intro p
    have h := hf p
    rw [inner_primeCellVec_eq] at h
    have hp : ((Real.sqrt (p : ℕ) : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
      exact_mod_cast (Real.sqrt_pos.mpr this).ne'
    exact (mul_eq_zero.mp h).resolve_left hp
  have hμ : halfLineMeasure.restrict (⋃ p : Nat.Primes, primeCell p) = halfLineMeasure := by
    rw [iUnion_primeCell, halfLineMeasure, Measure.restrict_restrict_of_subset le_rfl]
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [k.op_coeFn f, k.ae_integrable f] with y hy hint
  rw [hy, Pi.zero_apply, SchurKernel.apply]
  have hsplit := integral_iUnion (μ := halfLineMeasure) (f := fun z => k.toFun y z * (f : ℝ → ℂ) z)
    (fun p : Nat.Primes => measurableSet_primeCell p) pairwise_disjoint_primeCell
    (by rw [IntegrableOn, hμ]; exact hint)
  rw [hμ] at hsplit
  rw [hsplit]
  refine (tsum_congr fun p => ?_).trans tsum_zero
  have hconst : ∀ z ∈ primeCell (p : ℕ), k.toFun y z * (f : ℝ → ℂ) z =
      (g (poissonClock y - (Real.log (Real.log (p : ℕ)) + Sieve.meisselMertensConst)) : ℂ) *
        (f : ℝ → ℂ) z := by
    intro z hz
    change ((g (poissonClock y - poissonClock z) : ℝ) : ℂ) * _ = _
    rw [poissonClock_of_mem p.prop hz]
  rw [setIntegral_congr_fun (measurableSet_primeCell p) hconst, integral_const_mul, hcell p,
    mul_zero]

/-- The coordinates of `U* g` vanish exactly when `g` is orthogonal to all prime cells. -/
theorem adjoint_primeCellOp_eq_zero_iff (g : L²₊) :
    primeCellOp.adjoint g = 0 ↔ ∀ p, inner ℂ (primeCellVec p) g = 0 := by
  constructor
  · intro h p
    rw [← adjoint_primeCellOp_apply, h]; rfl
  · intro h
    ext p
    rw [adjoint_primeCellOp_apply, h p]; rfl

/-- **A step operator equals its compression by the range projection.** -/
theorem clockKernel_range_proj (g : ℝ → ℝ) (hg : Measurable g) {M α : ℝ} (hM : 0 ≤ M)
    (hα : 0 < α) (hgb : ∀ s, |g s| ≤ M * Real.exp (-(α * |s|)))
    (hsa : ContinuousLinearMap.adjoint (clockKernel g hg hM hα hgb).op = (clockKernel g hg hM hα hgb).op ∨
      ContinuousLinearMap.adjoint (clockKernel g hg hM hα hgb).op =
        -(clockKernel g hg hM hα hgb).op) :
    primeCellOp ∘L primeCellOp.adjoint ∘L (clockKernel g hg hM hα hgb).op =
      (clockKernel g hg hM hα hgb).op := by
  set T := (clockKernel g hg hM hα hgb).op
  ext1 f
  set v := T f - primeCellOp (primeCellOp.adjoint (T f)) with hv
  have hUv : primeCellOp.adjoint v = 0 := by
    rw [hv, map_sub, ← ContinuousLinearMap.comp_apply primeCellOp.adjoint primeCellOp,
      adjoint_primeCellOp_comp, ContinuousLinearMap.id_apply, sub_self]
  have hTv : T v = 0 :=
    clockKernel_op_eq_zero g hg hM hα hgb ((adjoint_primeCellOp_eq_zero_iff v).mp hUv)
  have hvv : inner ℂ v v = 0 := by
    have h1 : inner ℂ v (T f) = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left]
      rcases hsa with h | h
      · rw [h, hTv, inner_zero_left]
      · rw [h, _root_.neg_apply, hTv, neg_zero, inner_zero_left]
    have h2 : inner ℂ v (primeCellOp (primeCellOp.adjoint (T f))) = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hUv, inner_zero_left]
    rw [show inner ℂ v v = inner ℂ v (T f) - inner ℂ v (primeCellOp (primeCellOp.adjoint (T f))) by
      rw [← inner_sub_right]]
    rw [h1, h2, sub_self]
  have := inner_self_eq_zero.mp hvv
  rw [hv, sub_eq_zero] at this
  simp only [ContinuousLinearMap.comp_apply]
  exact this.symm

theorem mertensStepSechOp_range_proj :
    primeCellOp ∘L primeCellOp.adjoint ∘L mertensStepSechOp = mertensStepSechOp :=
  clockKernel_range_proj _ _ _ _ _ (Or.inl isSelfAdjoint_mertensStepSechOp)

theorem mertensStepTiltOp_range_proj :
    primeCellOp ∘L primeCellOp.adjoint ∘L mertensStepTiltOp = mertensStepTiltOp :=
  clockKernel_range_proj _ _ _ _ _ (Or.inr adjoint_mertensStepTiltOp)

theorem range_proj_adjoint :
    ContinuousLinearMap.adjoint (primeCellOp ∘L primeCellOp.adjoint) =
      primeCellOp ∘L primeCellOp.adjoint := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem mertensStepSechOp_proj_right :
    mertensStepSechOp ∘L primeCellOp ∘L primeCellOp.adjoint = mertensStepSechOp := by
  have h := congrArg ContinuousLinearMap.adjoint mertensStepSechOp_range_proj
  rw [← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.adjoint_comp, range_proj_adjoint,
    isSelfAdjoint_mertensStepSechOp.adjoint_eq] at h
  simpa [ContinuousLinearMap.comp_assoc] using h

theorem mertensStepTiltOp_proj_right :
    mertensStepTiltOp ∘L primeCellOp ∘L primeCellOp.adjoint = mertensStepTiltOp := by
  have h := congrArg ContinuousLinearMap.adjoint mertensStepTiltOp_range_proj
  rw [← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.adjoint_comp, range_proj_adjoint,
    adjoint_mertensStepTiltOp] at h
  have h' := congrArg Neg.neg h
  simpa [ContinuousLinearMap.comp_assoc] using h'

/-- **The embedded operator is the step operator:** `U K U* = A`. -/
theorem primeCellOp_conj_poissonPrimeOp :
    primeCellOp ∘L poissonPrimeOp ∘L primeCellOp.adjoint = mertensStepSechOp := by
  rw [poissonPrimeOp]
  calc primeCellOp ∘L (primeCellOp.adjoint ∘L mertensStepSechOp ∘L primeCellOp) ∘L
        primeCellOp.adjoint
      = (primeCellOp ∘L primeCellOp.adjoint ∘L mertensStepSechOp) ∘L
          (primeCellOp ∘L primeCellOp.adjoint) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = mertensStepSechOp := by
        rw [mertensStepSechOp_range_proj, mertensStepSechOp_proj_right]

/-- **The embedded commutator is the tilted step operator:** `U C U* = A_j`. -/
theorem primeCellOp_conj_poissonPrimeCommOp :
    primeCellOp ∘L poissonPrimeCommOp ∘L primeCellOp.adjoint = mertensStepTiltOp := by
  rw [poissonPrimeCommOp]
  calc primeCellOp ∘L (primeCellOp.adjoint ∘L mertensStepTiltOp ∘L primeCellOp) ∘L
        primeCellOp.adjoint
      = (primeCellOp ∘L primeCellOp.adjoint ∘L mertensStepTiltOp) ∘L
          (primeCellOp ∘L primeCellOp.adjoint) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = mertensStepTiltOp := by
        rw [mertensStepTiltOp_range_proj, mertensStepTiltOp_proj_right]

/-! ### Hilbert–Schmidt defects -/

theorem lintegral_iter_lt_top_of_prod {F : ℝ → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F))
    (h : ∫⁻ p, F p.1 p.2 ∂(halfLineMeasure.prod halfLineMeasure) < ∞) :
    ∫⁻ y, ∫⁻ z, F y z ∂halfLineMeasure ∂halfLineMeasure < ∞ := by
  have e := lintegral_prod (μ := halfLineMeasure) (ν := halfLineMeasure)
    (fun p : ℝ × ℝ => F p.1 p.2) hF.aemeasurable
  rw [e] at h
  exact h

/-- **(†) The step operator is a Hilbert–Schmidt perturbation of the Wiener–Hopf operator.** -/
theorem isHilbertSchmidt_mertensStepSechOp_sub :
    ContinuousLinearMap.IsHilbertSchmidt (mertensStepSechOp - wienerHopfSechOp) := by
  rw [mertensStepSechOp, wienerHopfSechOp, ← SchurKernel.sub_op]
  refine SchurKernel.isHilbertSchmidt_op _ (lintegral_iter_lt_top_of_prod
    (((SchurKernel.sub mertensStepSechKernel wienerHopfSechKernel).measurable_enorm.pow_const 2)) ?_)
  have h := lintegral_clock_sub_sq_lt_top hasDerivAt_sechSqHalf (by norm_num : (0 : ℝ) ≤ 4) one_pos
    abs_sechSqHalfDeriv_le_exp poissonClockConst_nonneg (fun y hy => abs_poissonClock_sub_le hy)
  refine lt_of_le_of_lt (le_of_eq ?_) h
  refine lintegral_congr fun p => ?_
  change ‖((sechSqHalf (poissonClock p.1 - poissonClock p.2) : ℝ) : ℂ) -
    ((sechSqHalf (p.1 - p.2) : ℝ) : ℂ)‖ₑ ^ 2 = _
  push_cast; rfl

/-- **The tilted step operator is a Hilbert–Schmidt perturbation of the tilted Wiener–Hopf
operator.** -/
theorem isHilbertSchmidt_mertensStepTiltOp_sub :
    ContinuousLinearMap.IsHilbertSchmidt (mertensStepTiltOp - wienerHopfTiltOp) := by
  rw [mertensStepTiltOp, wienerHopfTiltOp, ← SchurKernel.sub_op]
  refine SchurKernel.isHilbertSchmidt_op _ (lintegral_iter_lt_top_of_prod
    (((SchurKernel.sub mertensStepTiltKernel wienerHopfTiltKernel).measurable_enorm.pow_const 2)) ?_)
  have h := lintegral_clock_sub_sq_lt_top hasDerivAt_sechSqHalfTilt (by norm_num : (0 : ℝ) ≤ 8)
    (by norm_num : (0 : ℝ) < 1 / 2) abs_sechSqHalfTiltDeriv_le poissonClockConst_nonneg
    (fun y hy => abs_poissonClock_sub_le hy)
  refine lt_of_le_of_lt (le_of_eq ?_) h
  refine lintegral_congr fun p => ?_
  change ‖((sechSqHalfTilt (poissonClock p.1 - poissonClock p.2) : ℝ) : ℂ) -
    ((sechSqHalfTilt (p.1 - p.2) : ℝ) : ℂ)‖ₑ ^ 2 = _
  push_cast; rfl

/-- **`U K U* - W` is Hilbert–Schmidt.** -/
theorem isHilbertSchmidt_conj_poissonPrimeOp_sub :
    ContinuousLinearMap.IsHilbertSchmidt
      (primeCellOp ∘L poissonPrimeOp ∘L primeCellOp.adjoint - wienerHopfSechOp) := by
  rw [primeCellOp_conj_poissonPrimeOp]; exact isHilbertSchmidt_mertensStepSechOp_sub

/-- **`U C U* - W_j` is Hilbert–Schmidt.** -/
theorem isHilbertSchmidt_conj_poissonPrimeCommOp_sub :
    ContinuousLinearMap.IsHilbertSchmidt
      (primeCellOp ∘L poissonPrimeCommOp ∘L primeCellOp.adjoint - wienerHopfTiltOp) := by
  rw [primeCellOp_conj_poissonPrimeCommOp]; exact isHilbertSchmidt_mertensStepTiltOp_sub

theorem isCompactOperator_mertensStepSechOp_sub :
    IsCompactOperator (mertensStepSechOp - wienerHopfSechOp) :=
  isHilbertSchmidt_mertensStepSechOp_sub.isCompactOperator

theorem isCompactOperator_mertensStepTiltOp_sub :
    IsCompactOperator (mertensStepTiltOp - wienerHopfTiltOp) :=
  isHilbertSchmidt_mertensStepTiltOp_sub.isCompactOperator

/-! ### Weyl spectra -/

/-- The `n`-th prime. -/
def nthPrime (n : ℕ) : Nat.Primes := ⟨Nat.nth Nat.Prime n, Nat.prime_nth_prime n⟩

theorem nthPrime_injective : Function.Injective nthPrime := fun _ _ h =>
  Nat.nth_injective Nat.infinite_setOf_prime (congrArg Subtype.val h)

theorem tendsto_one_div_nthPrime :
    Tendsto (fun n => (1 : ℝ) / ((nthPrime n : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hle : ∀ n : ℕ, (n : ℝ) ≤ ((nthPrime n : ℕ) : ℝ) := fun n => by
    exact_mod_cast (Nat.nth_strictMono Nat.infinite_setOf_prime).id_le n
  have h : Tendsto (fun n => ((nthPrime n : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono hle tendsto_natCast_atTop_atTop
  simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h

/-- The Weyl interval `[0, 4] ⊂ ℂ`. -/
def weylIntervalZeroFour : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc 0 4

theorem mem_weylIntervalZeroFour_of {c : ℂ} (him : c.im = 0) (h0 : 0 ≤ c.re) (h4 : c.re ≤ 4) :
    c ∈ weylIntervalZeroFour :=
  ⟨c.re, ⟨h0, h4⟩, Complex.ext (by simp) (by simp [him])⟩

theorem norm_mertensStepSechKernel_le (y z : ℝ) : ‖mertensStepSechKernel.toFun y z‖ ≤ 1 := by
  change ‖((sechSqHalf (poissonClock y - poissonClock z) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sechSqHalf_pos _)]
  exact sechSqHalf_le_one _

theorem norm_wienerHopfSechKernel_le (y z : ℝ) : ‖wienerHopfSechKernel.toFun y z‖ ≤ 1 := by
  change ‖((sechSqHalf (y - z) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sechSqHalf_pos _)]
  exact sechSqHalf_le_one _

/-- A bounded kernel sends the shrinking prime cells to a null sequence. -/
theorem tendsto_norm_op_primeCellVec (k : SchurKernel halfLineMeasure)
    (hk : ∀ y z, ‖k.toFun y z‖ ≤ 1) :
    Tendsto (fun n => ‖k.op (primeCellVec (nthPrime n))‖) atTop (𝓝 0) := by
  have hb : ∀ n, ‖k.op (primeCellVec (nthPrime n))‖ ^ 2 ≤
      k.bound * (1 / ((nthPrime n : ℕ) : ℝ)) := by
    intro n
    have h := SchurKernel.norm_op_cellVec_sq_le k (fun p : Nat.Primes => primeCell p)
      (fun p => measurableSet_primeCell p) halfLineMeasure_primeCell_ne_top
      halfLineMeasure_primeCell_ne_zero zero_le_one hk (nthPrime n)
    rw [one_mul, halfLineMeasure_primeCell, ENNReal.toReal_ofReal (by positivity)] at h
    exact h
  have hlim : Tendsto (fun n => (k.bound : ℝ) * (1 / ((nthPrime n : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_nthPrime.const_mul (k.bound : ℝ)
  have h2 : Tendsto (fun n => ‖k.op (primeCellVec (nthPrime n))‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => by positivity) hb hlim
  have := h2.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

theorem zero_mem_weylEssentialSpectrum_wienerHopfSechOp :
    (0 : ℂ) ∈ weylEssentialSpectrum wienerHopfSechOp := by
  refine mem_weylEssentialSpectrum_of_orthonormal
    (orthonormal_primeCellVec.comp nthPrime nthPrime_injective) ?_
  simpa [wienerHopfSechOp] using
    tendsto_norm_op_primeCellVec wienerHopfSechKernel norm_wienerHopfSechKernel_le

theorem ofReal_mem_weylEssentialSpectrum_wienerHopfSechOp {c : ℝ} (hc0 : 0 < c) (hc4 : c ≤ 4) :
    (c : ℂ) ∈ weylEssentialSpectrum wienerHopfSechOp := by
  obtain ⟨ξ, hξ⟩ := exists_sechSqHalfSymbol_eq hc0 hc4
  have ht := tendsto_norm_op_planeWavePacketSeq_sub wienerHopfSechKernel measurable_sechSqHalf
    integrable_sechSqHalf integrable_abs_mul_sechSqHalf (fun _ _ => rfl) ξ
  have hsym : convSymbol sechSqHalf ξ = c := hξ
  rw [hsym] at ht
  exact mem_weylEssentialSpectrum_of_orthonormal (orthonormal_planeWavePacketSeq ξ) ht

/-- **The Weyl spectrum of the Wiener–Hopf operator is `[0, 4]`.** -/
theorem weylEssentialSpectrum_wienerHopfSechOp :
    weylEssentialSpectrum wienerHopfSechOp = weylIntervalZeroFour := by
  refine Set.Subset.antisymm (fun c hc => ?_) ?_
  · exact mem_weylIntervalZeroFour_of
      (im_eq_zero_of_mem_weylEssentialSpectrum isSelfAdjoint_wienerHopfSechOp hc)
      (re_nonneg_of_mem_weylEssentialSpectrum re_inner_wienerHopfSechOp_nonneg hc)
      (re_le_of_mem_weylEssentialSpectrum re_inner_wienerHopfSechOp_le hc)
  · rintro _ ⟨x, ⟨hx0, hx4⟩, rfl⟩
    rcases hx0.eq_or_lt with h | h
    · subst h; simpa using zero_mem_weylEssentialSpectrum_wienerHopfSechOp
    · exact ofReal_mem_weylEssentialSpectrum_wienerHopfSechOp h hx4

theorem weylEssentialSpectrum_mertensStepSechOp :
    weylEssentialSpectrum mertensStepSechOp = weylIntervalZeroFour := by
  rw [weylEssentialSpectrum_eq_of_isCompactOperator isCompactOperator_mertensStepSechOp_sub,
    weylEssentialSpectrum_wienerHopfSechOp]

theorem norm_adjoint_primeCellOp_apply_le (g : L²₊) : ‖primeCellOp.adjoint g‖ ≤ ‖g‖ := by
  refine (primeCellOp.adjoint.le_opNorm g).trans ?_
  have h1 : ‖primeCellOp.adjoint‖ = ‖primeCellOp‖ := ContinuousLinearMap.adjoint.norm_map _
  have h2 : ‖primeCellOp‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
  rw [h1]
  nlinarith [norm_nonneg g]

theorem zero_mem_weylEssentialSpectrum_poissonPrimeOp :
    (0 : ℂ) ∈ weylEssentialSpectrum poissonPrimeOp := by
  refine ⟨fun n => lpBasisVec (nthPrime n), (orthonormal_lpBasisVec_comp nthPrime_injective).1,
    Orthonormal.weakly_tendsto_zero (orthonormal_lpBasisVec_comp nthPrime_injective), ?_⟩
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (tendsto_norm_op_primeCellVec mertensStepSechKernel norm_mertensStepSechKernel_le)
  rw [zero_smul, sub_zero, poissonPrimeOp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, primeCellOp_lpBasisVec]
  exact norm_adjoint_primeCellOp_apply_le _

/-- **The Weyl spectrum of the prime Poisson operator is `[0, 4]`.** -/
theorem weylEssentialSpectrum_poissonPrimeOp :
    weylEssentialSpectrum poissonPrimeOp = weylIntervalZeroFour := by
  refine Set.Subset.antisymm (fun c hc => ?_) ?_
  · rw [← weylEssentialSpectrum_mertensStepSechOp]
    exact mem_weylEssentialSpectrum_of_compression adjoint_primeCellOp_comp
      mertensStepSechOp_range_proj hc
  · rintro _ ⟨x, ⟨hx0, hx4⟩, rfl⟩
    rcases hx0.eq_or_lt with h | h
    · subst h; simpa using zero_mem_weylEssentialSpectrum_poissonPrimeOp
    · have hA : (x : ℂ) ∈ weylEssentialSpectrum mertensStepSechOp := by
        rw [weylEssentialSpectrum_mertensStepSechOp]; exact ⟨x, ⟨hx0, hx4⟩, rfl⟩
      exact mem_weylEssentialSpectrum_compression adjoint_primeCellOp_comp
        mertensStepSechOp_range_proj mertensStepSechOp_proj_right
        (show (x : ℂ) ≠ 0 from by exact_mod_cast h.ne') hA

/-- **`‖K‖_ess = 4`.** -/
theorem essentialNorm_poissonPrimeOp : essentialNorm poissonPrimeOp = 4 := by
  apply le_antisymm
  · have hcomp : IsCompactOperator
        (primeCellOp.adjoint ∘L (mertensStepSechOp - wienerHopfSechOp) ∘L primeCellOp) :=
      (isCompactOperator_mertensStepSechOp_sub.comp_clm primeCellOp).clm_comp primeCellOp.adjoint
    refine (essentialNorm_le _ _ hcomp).trans ?_
    have hsplit : poissonPrimeOp -
        primeCellOp.adjoint ∘L (mertensStepSechOp - wienerHopfSechOp) ∘L primeCellOp =
        primeCellOp.adjoint ∘L wienerHopfSechOp ∘L primeCellOp := by
      rw [poissonPrimeOp, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
      abel
    rw [hsplit]
    have h1 : ‖primeCellOp.adjoint‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]; exact LinearIsometry.norm_toContinuousLinearMap_le _
    have h2 : ‖primeCellOp‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
    calc ‖primeCellOp.adjoint ∘L wienerHopfSechOp ∘L primeCellOp‖
        ≤ ‖primeCellOp.adjoint‖ * (‖wienerHopfSechOp‖ * ‖primeCellOp‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (4 * 1) := by
          gcongr
          exact norm_wienerHopfSechOp_le
      _ = 4 := by norm_num
  · have h4 : ((4 : ℝ) : ℂ) ∈ weylEssentialSpectrum poissonPrimeOp := by
      rw [weylEssentialSpectrum_poissonPrimeOp]; exact ⟨4, ⟨by norm_num, le_rfl⟩, rfl⟩
    have := norm_le_essentialNorm_of_mem_weylEssentialSpectrum h4
    simpa using this

/-- **`K` is not compact.** -/
theorem not_isCompactOperator_poissonPrimeOp : ¬ IsCompactOperator poissonPrimeOp := fun h => by
  have := essentialNorm_eq_zero_of_isCompactOperator h
  rw [essentialNorm_poissonPrimeOp] at this
  norm_num at this

end

end RHTower
