import GaloisForLFunctions.RHTower.MobiusThetaInternalJetSourceToXiLanding
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalSourceToXiLanding

/-!
# Physical prime-normal graph for internally promoted theta jets

Internal jet promotion is lifted here from the pointwise Fourier--Laplace source to the actual
physical `L²` source space.  The base vector is the polynomially weighted theta Schwartz source
whose Fourier transform is the corresponding Xi jet.  Prime-normal residuals and their adjacent
exponent cofaces are then constructed before any spectral parameter or divisor point is selected.

The full post-label tail converges strongly to zero by a vector-valued Tannery argument.  Hence
every internally promoted prime-normal residual converges to its retained oriented source, and the
complete exponent codiagonal telescopes strongly to that physical jet source.  The graph-norm
Hellinger--Hodge landing is a separate theorem and is not asserted here.
-/

open Complex Real MeasureTheory ArithmeticFunction Filter Topology
open scoped BigOperators Moebius FourierTransform SchwartzMap

noncomputable section
namespace RHTower

/-- Normalized physical theta source carrying the `k`-th internal spectral moment. -/
def xiThetaInternalJetSchwartzSource (k : ℕ) : 𝒮(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
      (fun x : ℝ => (-(((2 * Real.pi * x : ℝ) : ℂ)) * I) ^ k)
    xiThetaSchwartzSource

@[simp]
theorem xiThetaInternalJetSchwartzSource_apply (k : ℕ) (x : ℝ) :
    xiThetaInternalJetSchwartzSource k x =
      (-(((2 * Real.pi * x : ℝ) : ℂ)) * I) ^ k *
        xiThetaSchwartzSource x := by
  rw [xiThetaInternalJetSchwartzSource,
    SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  rfl

/-- `L²` realization of the internally promoted theta source. -/
def xiThetaInternalJetSourceL2 (k : ℕ) : MobiusThetaSourceL2 :=
  (xiThetaInternalJetSchwartzSource k).toLp 2 volume

/-- The zeroth internal source is the original physical theta source. -/
theorem xiThetaInternalJetSourceL2_zero :
    xiThetaInternalJetSourceL2 0 = xiThetaSourceL2 := by
  apply Lp.ext
  filter_upwards [
      (xiThetaInternalJetSchwartzSource 0).coeFn_toLp
        (p := 2) (mu := (volume : Measure ℝ)),
      xiThetaSchwartzSource.coeFn_toLp
        (p := 2) (mu := (volume : Measure ℝ))]
    with x hx hbase
  rw [xiThetaInternalJetSourceL2, xiThetaSourceL2, hx, hbase]
  simp

/-- Source-only `m = 3` envelope for the internally promoted post-`p` tail. -/
def mobiusThetaInternalJetPrimeNormalMajorant (k p j : ℕ) : ℝ :=
  ((p : ℝ) / (p + j + 1 : ℕ)) ^ (3 / 2 : ℝ) *
    ‖xiThetaInternalJetSourceL2 k‖

theorem summable_mobiusThetaInternalJetPrimeNormalMajorant
    (k p : ℕ) :
    Summable (mobiusThetaInternalJetPrimeNormalMajorant k p) := by
  have hs : Summable (fun j : ℕ => (j : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift : Summable
      (fun j : ℕ => ((j + (p + 1) : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (_root_.summable_nat_add_iff (p + 1)).2 hs
  have hmul := hshift.mul_left
    ((p : ℝ) ^ (3 / 2 : ℝ) * ‖xiThetaInternalJetSourceL2 k‖)
  refine hmul.congr fun j => ?_
  rw [mobiusThetaInternalJetPrimeNormalMajorant,
    Real.div_rpow (by positivity) (by positivity),
    Real.rpow_neg (by positivity :
      (0 : ℝ) ≤ ((j + (p + 1) : ℕ) : ℝ))]
  push_cast
  ring_nf

/-- One post-`p` physical channel with internal jet promotion performed before translation. -/
def mobiusThetaInternalJetPrimeNormalTailTerm
    (k p m j : ℕ) : MobiusThetaSourceL2 :=
  (mobiusThetaPrimeNormalWeight p m j : ℂ) •
    MellinL2.additiveTranslationUnitary
      (-((m : ℝ) * Real.log ((p + j + 1 : ℕ) / (p : ℝ))) *
        MellinL2.spectralNormalization)
      (xiThetaInternalJetSourceL2 k)

theorem norm_mobiusThetaInternalJetPrimeNormalTailTerm
    (k p m j : ℕ) :
    ‖mobiusThetaInternalJetPrimeNormalTailTerm k p m j‖ =
      |mobiusThetaPrimeNormalWeight p m j| *
        ‖xiThetaInternalJetSourceL2 k‖ := by
  rw [mobiusThetaInternalJetPrimeNormalTailTerm, norm_smul,
    LinearIsometryEquiv.norm_map, Complex.norm_real, Real.norm_eq_abs]

/-- Uniform source envelope, independent of the exponent once `m ≥ 3`. -/
theorem norm_mobiusThetaInternalJetPrimeNormalTailTerm_le_majorant
    (k : ℕ) {p m : ℕ} (hp : 1 ≤ p) (hm : 3 ≤ m) (j : ℕ) :
    ‖mobiusThetaInternalJetPrimeNormalTailTerm k p m j‖ ≤
      mobiusThetaInternalJetPrimeNormalMajorant k p j := by
  rw [norm_mobiusThetaInternalJetPrimeNormalTailTerm,
    mobiusThetaPrimeNormalWeight, abs_mul]
  have hmu : |(μ (p + j + 1) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p + j + 1)
  have hratioPos : 0 < (p : ℝ) / (p + j + 1 : ℕ) := by positivity
  have hratioLe : (p : ℝ) / (p + j + 1 : ℕ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast (by omega : p ≤ p + j + 1)
  have hexp : (3 / 2 : ℝ) ≤ (m : ℝ) / 2 := by
    exact_mod_cast hm
  rw [abs_of_nonneg (Real.rpow_nonneg hratioPos.le _)]
  unfold mobiusThetaInternalJetPrimeNormalMajorant
  calc
    |(μ (p + j + 1) : ℝ)| *
          ((p : ℝ) / (p + j + 1 : ℕ)) ^ ((m : ℝ) / 2) *
          ‖xiThetaInternalJetSourceL2 k‖ ≤
        1 * ((p : ℝ) / (p + j + 1 : ℕ)) ^ ((m : ℝ) / 2) *
          ‖xiThetaInternalJetSourceL2 k‖ := by
      gcongr
    _ ≤ ((p : ℝ) / (p + j + 1 : ℕ)) ^ (3 / 2 : ℝ) *
          ‖xiThetaInternalJetSourceL2 k‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hratioPos hratioLe hexp)
        (norm_nonneg _)

/-- Each fixed labelled tail vanishes strongly as exponent tends to infinity. -/
theorem tendsto_mobiusThetaInternalJetPrimeNormalTailTerm_zero
    (k : ℕ) {p : ℕ} (hp : 1 ≤ p) (j : ℕ) :
    Tendsto
      (fun m : ℕ => mobiusThetaInternalJetPrimeNormalTailTerm k p m j)
      atTop (nhds 0) := by
  have hratioPos : 0 < (p : ℝ) / (p + j + 1 : ℕ) := by positivity
  have hratioLt : (p : ℝ) / (p + j + 1 : ℕ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast (by omega : p < p + j + 1)
  have hpow : Tendsto
      (fun m : ℕ => ((p : ℝ) / (p + j + 1 : ℕ)) ^ ((m : ℝ) / 2))
      atTop (nhds 0) := by
    have hb := tendsto_rpow_atTop_of_base_lt_one
      ((p : ℝ) / (p + j + 1 : ℕ)) (by linarith) hratioLt
    exact hb.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert ((tendsto_const_nhds.mul hpow).mul tendsto_const_nhds) using 1
  funext m
  rw [norm_mobiusThetaInternalJetPrimeNormalTailTerm,
    mobiusThetaPrimeNormalWeight, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hratioPos.le _)]

/-- Full internally promoted post-`p` tail vanishes strongly. -/
theorem tendsto_tsum_mobiusThetaInternalJetPrimeNormalTailTerm_zero
    (k : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    Tendsto
      (fun m : ℕ =>
        ∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k p m j)
      atTop (nhds 0) := by
  rw [show (0 : MobiusThetaSourceL2) = ∑' _j : ℕ, 0 by simp]
  apply tendsto_tsum_of_dominated_convergence
    (summable_mobiusThetaInternalJetPrimeNormalMajorant k p)
  · exact tendsto_mobiusThetaInternalJetPrimeNormalTailTerm_zero k hp
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with m hm j
    exact norm_mobiusThetaInternalJetPrimeNormalTailTerm_le_majorant k hp hm j

/-- Singular internally promoted prime-normal source. -/
def mobiusThetaInternalJetPrimeNormalResidual
    (k p m : ℕ) : MobiusThetaSourceL2 :=
  ((μ p : ℝ) : ℂ) • xiThetaInternalJetSourceL2 k +
    ∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k p m j

/-- **Unconditional internally promoted prime-normal extraction in physical `L²`.** -/
theorem tendsto_mobiusThetaInternalJetPrimeNormalResidual
    (k : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    Tendsto (mobiusThetaInternalJetPrimeNormalResidual k p) atTop
      (nhds (((μ p : ℝ) : ℂ) • xiThetaInternalJetSourceL2 k)) := by
  unfold mobiusThetaInternalJetPrimeNormalResidual
  simpa using tendsto_const_nhds.add
    (tendsto_tsum_mobiusThetaInternalJetPrimeNormalTailTerm_zero k hp)

/-- Direct exponent rung is the `p = 1` internally promoted residual. -/
def mobiusThetaInternalJetDirectPhysicalRung
    (k m : ℕ) : MobiusThetaSourceL2 :=
  mobiusThetaInternalJetPrimeNormalResidual k 1 m

theorem tendsto_mobiusThetaInternalJetDirectPhysicalRung (k : ℕ) :
    Tendsto (mobiusThetaInternalJetDirectPhysicalRung k) atTop
      (nhds (xiThetaInternalJetSourceL2 k)) := by
  simpa [mobiusThetaInternalJetDirectPhysicalRung] using
    (tendsto_mobiusThetaInternalJetPrimeNormalResidual k
      (p := 1) (by omega : 1 ≤ 1))

/-- Complete internally promoted physical exponent channel. -/
def mobiusThetaInternalJetCompletePhysicalChannel
    (k K : ℕ) : ℕ → MobiusThetaSourceL2
  | 0 => mobiusThetaInternalJetDirectPhysicalRung k K
  | j + 1 =>
      mobiusThetaInternalJetDirectPhysicalRung k (K + j + 1) -
        mobiusThetaInternalJetDirectPhysicalRung k (K + j)

/-- Exact finite codiagonal before transform or divisor evaluation. -/
theorem sum_range_mobiusThetaInternalJetCompletePhysicalChannel
    (k K N : ℕ) :
    ∑ j ∈ Finset.range (N + 1),
        mobiusThetaInternalJetCompletePhysicalChannel k K j =
      mobiusThetaInternalJetDirectPhysicalRung k (K + N) := by
  induction N with
  | zero => simp [mobiusThetaInternalJetCompletePhysicalChannel]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp [mobiusThetaInternalJetCompletePhysicalChannel, add_assoc]

/-- **Strong complete-source landing for every internal jet order.** -/
theorem tendsto_sum_range_mobiusThetaInternalJetCompletePhysicalChannel
    (k K : ℕ) :
    Tendsto
      (fun N : ℕ => ∑ j ∈ Finset.range (N + 1),
        mobiusThetaInternalJetCompletePhysicalChannel k K j)
      atTop (nhds (xiThetaInternalJetSourceL2 k)) := by
  have h := (tendsto_mobiusThetaInternalJetDirectPhysicalRung k).comp
    (tendsto_add_atTop_nat K)
  have h' : Tendsto
      (fun N : ℕ => mobiusThetaInternalJetDirectPhysicalRung k (K + N))
      atTop (nhds (xiThetaInternalJetSourceL2 k)) := by
    simpa [Function.comp_def, Nat.add_comm] using h
  exact h'.congr' (Filter.Eventually.of_forall fun N =>
    (sum_range_mobiusThetaInternalJetCompletePhysicalChannel k K N).symm)

end RHTower
