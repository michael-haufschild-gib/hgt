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

open Complex Real MeasureTheory ArithmeticFunction LSeries Filter Topology
open scoped BigOperators LSeries.notation Moebius FourierTransform SchwartzMap

noncomputable section
namespace RHTower

/-- Normalized physical theta source carrying the `k`-th internal spectral moment. -/
def xiThetaInternalJetSchwartzSource (k : ℕ) : 𝓢(ℝ, ℂ) :=
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

/-- **Exact physical source-to-Xi landing.**  Fourier transformation of the `k`-th internally
promoted theta source is the `k`-th centered Xi jet on the whole real spectral axis.  Promotion
takes place in the physical Schwartz source before transformation. -/
theorem fourier_xiThetaInternalJetSchwartzSource (k : ℕ) (t : ℝ) :
    (𝓕 (xiThetaInternalJetSchwartzSource k)) t =
      iteratedDeriv k XiC (t : ℂ) := by
  change FourierTransform.fourier
    (fun x : ℝ => xiThetaInternalJetSchwartzSource k x) t = _
  rw [Real.fourier_real_eq_integral_exp_smul]
  let G : ℝ → ℂ := fun y => thetaCuspFourierLaplaceJetIntegrand k (t : ℂ) y
  have hfun : (fun x : ℝ =>
      Complex.exp (↑(-2 * Real.pi * x * t) * I) •
        xiThetaInternalJetSchwartzSource k x) =
      fun x => (2 * Real.pi : ℂ) * G ((2 * Real.pi) * x) := by
    funext x
    rw [xiThetaInternalJetSchwartzSource_apply, xiThetaSchwartzSource_apply]
    change Complex.exp (↑(-2 * Real.pi * x * t) * I) *
        (((-((2 * Real.pi * x : ℝ) : ℂ) * I) ^ k) *
          ((2 * Real.pi : ℂ) * thetaCuspFullSource ((2 * Real.pi) * x))) = _
    dsimp [G, thetaCuspFourierLaplaceJetIntegrand,
      thetaCuspFourierLaplaceIntegrand]
    have hphase : Complex.exp (↑(-2 * Real.pi * x * t) * I) =
        Complex.exp (-I * (t : ℂ) * (((2 * Real.pi) * x : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [hphase]
    push_cast
    ring
  rw [hfun, integral_const_mul]
  rw [MeasureTheory.Measure.integral_comp_mul_left G (2 * Real.pi)]
  have hscale : |((2 * Real.pi)⁻¹)| = (2 * Real.pi)⁻¹ := by
    rw [abs_of_pos]
    positivity
  rw [hscale]
  change (2 * Real.pi : ℂ) * (((2 * Real.pi)⁻¹ : ℝ) • (∫ y : ℝ, G y)) = _
  rw [real_smul]
  have hcancel : (2 * Real.pi : ℂ) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [← mul_assoc, hcancel, one_mul]
  rw [iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet k
    (by simp [thetaCuspFourierLaplaceStrip])]

/-- `L²` realization of the internally promoted theta source. -/
def xiThetaInternalJetSourceL2 (k : ℕ) : MobiusThetaSourceL2 :=
  (xiThetaInternalJetSchwartzSource k).toLp 2 volume

/-- Exact Fourier-side `L²` realization of the internally promoted source. -/
def xiThetaInternalJetFourierSourceL2 (k : ℕ) : MobiusThetaSourceL2 :=
  (𝓕 (xiThetaInternalJetSchwartzSource k)).toLp 2 volume

/-- The Fourier-side physical vector is almost everywhere the actual `k`-th Xi jet. -/
theorem xiThetaInternalJetFourierSourceL2_ae (k : ℕ) :
    xiThetaInternalJetFourierSourceL2 k =ᵐ[volume]
      fun t : ℝ => iteratedDeriv k XiC (t : ℂ) := by
  filter_upwards [(𝓕 (xiThetaInternalJetSchwartzSource k)).coeFn_toLp
    (p := 2) volume] with t ht
  rw [xiThetaInternalJetFourierSourceL2, ht,
    fourier_xiThetaInternalJetSchwartzSource]

/-- Plancherel transports the physical internal jet to its exact Xi-jet profile. -/
theorem fourier_xiThetaInternalJetSourceL2 (k : ℕ) :
    𝓕 (xiThetaInternalJetSourceL2 k) =
      xiThetaInternalJetFourierSourceL2 k := by
  rw [xiThetaInternalJetSourceL2, xiThetaInternalJetFourierSourceL2,
    SchwartzMap.toLp_fourier_eq]

/-- The zeroth internal source is the original physical theta source. -/
theorem xiThetaInternalJetSourceL2_zero :
    xiThetaInternalJetSourceL2 0 = xiThetaSourceL2 := by
  apply Lp.ext
  filter_upwards [
      (xiThetaInternalJetSchwartzSource 0).coeFn_toLp
        (p := 2) volume,
      xiThetaSchwartzSource.coeFn_toLp
        (p := 2) volume]
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

/-- Direct integer-labelled internal-jet term before the `mPart` power reindexing. -/
def mobiusThetaInternalJetDirectDirichletTerm
    (k m n : ℕ) : MobiusThetaSourceL2 :=
  LSeries.term (↗(μ : ArithmeticFunction ℤ)) ((m : ℂ) / 2) n •
    MellinL2.additiveTranslationUnitary
      (-((m : ℝ) * Real.log n) * MellinL2.spectralNormalization)
      (xiThetaInternalJetSourceL2 k)

theorem mobiusThetaInternalJetDirectDirichletTerm_zero (k m : ℕ) :
    mobiusThetaInternalJetDirectDirichletTerm k m 0 = 0 := by
  simp [mobiusThetaInternalJetDirectDirichletTerm]

theorem mobiusThetaInternalJetDirectDirichletTerm_one (k m : ℕ) :
    mobiusThetaInternalJetDirectDirichletTerm k m 1 =
      xiThetaInternalJetSourceL2 k := by
  simp only [mobiusThetaInternalJetDirectDirichletTerm,
    LSeries.term_of_ne_zero one_ne_zero,
    ArithmeticFunction.moebius_apply_one, Nat.cast_one, one_cpow, div_one,
    Real.log_one, mul_zero, neg_zero, zero_mul]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (xiThetaInternalJetSourceL2 k)
    (MellinL2.realTranslation_measurePreserving 0)] with x hx
  simpa [MellinL2.additiveTranslationUnitary,
    MellinL2.lpCompMeasurePreservingEquiv,
    MellinL2.realTranslationEquiv] using hx

/-- The complete integer-labelled tail term is exactly the corresponding direct source term. -/
theorem mobiusThetaInternalJetDirectDirichletTerm_add_two
    (k m j : ℕ) :
    mobiusThetaInternalJetDirectDirichletTerm k m (j + 2) =
      mobiusThetaInternalJetPrimeNormalTailTerm k 1 m j := by
  rw [mobiusThetaInternalJetDirectDirichletTerm,
    LSeries.term_of_ne_zero (by omega : j + 2 ≠ 0),
    mobiusThetaInternalJetPrimeNormalTailTerm, mobiusThetaPrimeNormalWeight]
  rw [show 1 + j + 1 = j + 2 by omega]
  congr 2
  · rw [Complex.ofReal_mul]
    norm_num only [Nat.cast_one]
    have hr := Complex.ofReal_cpow
      (x := (1 : ℝ) / (j + 2 : ℕ))
      (by positivity : 0 ≤ (1 : ℝ) / (j + 2 : ℕ)) ((m : ℝ) / 2)
    rw [hr]
    push_cast
    rw [one_div, Complex.inv_cpow _ _ (by
      rw [show (j : ℂ) + 2 = (((j : ℝ) + 2 : ℝ) : ℂ) by push_cast; rfl,
        Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_pos.ne'.symm)]
    ring
  · congr 2
    congr 1
    push_cast
    ring_nf

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
    have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
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
  have hscalar : Tendsto
      (fun m : ℕ => |(μ (p + j + 1) : ℝ)| *
        ((p : ℝ) / (p + j + 1 : ℕ)) ^ ((m : ℝ) / 2) *
          ‖xiThetaInternalJetSourceL2 k‖)
      atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds.mul hpow).mul tendsto_const_nhds)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert hscalar using 1
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
  change Tendsto (mobiusThetaInternalJetPrimeNormalResidual k 1) atTop
    (nhds (xiThetaInternalJetSourceL2 k))
  simpa using (tendsto_mobiusThetaInternalJetPrimeNormalResidual k
    (p := 1) (by omega : 1 ≤ 1))

theorem summable_mobiusThetaInternalJetDirectDirichletTerm
    (k : ℕ) {m : ℕ} (hm : 3 ≤ m) :
    Summable (mobiusThetaInternalJetDirectDirichletTerm k m) := by
  apply (_root_.summable_nat_add_iff 2).1
  have hnorm : Summable
      (fun j : ℕ => ‖mobiusThetaInternalJetPrimeNormalTailTerm k 1 m j‖) := by
    exact (summable_mobiusThetaInternalJetPrimeNormalMajorant k 1).of_norm_bounded
      (fun j => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact norm_mobiusThetaInternalJetPrimeNormalTailTerm_le_majorant
          k (by omega) hm j)
  have ht := Summable.of_norm hnorm
  exact ht.congr
    (fun j => (mobiusThetaInternalJetDirectDirichletTerm_add_two k m j).symm)

/-- The actual internally promoted prime-normal rung is the complete direct coefficient source. -/
theorem mobiusThetaInternalJetDirectPhysicalRung_eq_tsum
    (k : ℕ) {m : ℕ} (hm : 3 ≤ m) :
    mobiusThetaInternalJetDirectPhysicalRung k m =
      ∑' n : ℕ, mobiusThetaInternalJetDirectDirichletTerm k m n := by
  have hs :=
    (summable_mobiusThetaInternalJetDirectDirichletTerm k hm).sum_add_tsum_nat_add 2
  rw [mobiusThetaInternalJetDirectPhysicalRung,
    mobiusThetaInternalJetPrimeNormalResidual]
  rw [show (((μ 1 : ℝ) : ℂ) • xiThetaInternalJetSourceL2 k) =
      xiThetaInternalJetSourceL2 k by norm_num]
  calc
    xiThetaInternalJetSourceL2 k +
          ∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k 1 m j =
        ∑ i ∈ Finset.range 2,
            mobiusThetaInternalJetDirectDirichletTerm k m i +
          ∑' j : ℕ, mobiusThetaInternalJetDirectDirichletTerm k m (j + 2) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Finset.sum_range_zero, zero_add,
        mobiusThetaInternalJetDirectDirichletTerm_zero,
        mobiusThetaInternalJetDirectDirichletTerm_one,
        mobiusThetaInternalJetDirectDirichletTerm_add_two]
    _ = ∑' n : ℕ, mobiusThetaInternalJetDirectDirichletTerm k m n := hs

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

/-- **Unconditional physical source-to-Xi landing theorem.**  The complete prime-normal channel
converges strongly after Plancherel to the actual `k`-th Xi jet in `L²`, with its source order
retained and without choosing a divisor point. -/
theorem tendsto_fourier_sum_range_mobiusThetaInternalJetCompletePhysicalChannel
    (k K : ℕ) :
    Tendsto
      (fun N : ℕ => 𝓕 (∑ j ∈ Finset.range (N + 1),
        mobiusThetaInternalJetCompletePhysicalChannel k K j))
      atTop (nhds (xiThetaInternalJetFourierSourceL2 k)) := by
  have h := ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).continuous.tendsto
    (xiThetaInternalJetSourceL2 k)).comp
      (tendsto_sum_range_mobiusThetaInternalJetCompletePhysicalChannel k K)
  rw [← fourier_xiThetaInternalJetSourceL2]
  exact h

end RHTower
