import GaloisForLFunctions.RHTower.CommonRadialSubunitHarmonicCompletion
import GaloisForLFunctions.RHTower.JointAncestryHilbertMultiplicityHaarVacuumSuperselection
import GaloisForLFunctions.HTGeometry.FourierCircleTruncation
import GaloisForLFunctions.HTGeometry.ProjectivePhaseHaarStatistic
import GaloisForLFunctions.HTGeometry.HarmonicLogEquidistribution
import GaloisForLFunctions.HTGeometry.HilbertSchmidtLyapunovInverse
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.HTGeometry.L2OperatorFamilyIsometry
import GaloisForLFunctions.HTGeometry.RangeProjectionDeriv
import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert

/-!
# Phase-quotient stationary completion homotopy

This module formalizes the complete unconditional source-native phase field from `ULF-PQSCH-001`.
Contractive measurable common-radial fields produce positive Schatten-one covariance densities,
their one-sided Hardy compression gives an exact operator-valued Toeplitz history, and adding that
stationary history to the minimal prime completion preserves the same integral--nuclear defect.
The recurrent density is strictly below the primitive Euler budget, Haar phase closure retains
exactly the zero Fourier block, `L∞` field homotopies are operator-norm continuous, and constant
fields recover the earlier common-radial constant-block completion exactly.
-/

open Complex Matrix Set MeasureTheory Filter Topology
open scoped BigOperators InnerProductSpace ComplexOrder ENNReal

namespace RHTower

noncomputable section

open ContinuousLinearMap
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

theorem inner_lpUnitVectorEmbedding_cross
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure X) (e d : H) (he : ‖e‖ = 1) (hd : ‖d‖ = 1)
    (f g : Lp ℂ 2 μ) :
    inner ℂ (lpUnitVectorEmbedding μ e he f)
        (lpUnitVectorEmbedding μ d hd g) =
      inner ℂ f g * inner ℂ e d := by
  rw [L2.inner_def, L2.inner_def]
  have hef :=
    (scalarToUnitVectorIsometry e he).toContinuousLinearMap.coeFn_compLp f
  have hdg :=
    (scalarToUnitVectorIsometry d hd).toContinuousLinearMap.coeFn_compLp g
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [hef, hdg] with x hfx hgx
  change inner ℂ
      ((((scalarToUnitVectorIsometry e he).toContinuousLinearMap.compLp f :
        Lp H 2 μ) : X → H) x)
      ((((scalarToUnitVectorIsometry d hd).toContinuousLinearMap.compLp g :
        Lp H 2 μ) : X → H) x) = _
  rw [hfx, hgx]
  simp [scalarToUnitVectorIsometry, inner_smul_left, inner_smul_right,
    RCLike.inner_apply]
  ring

abbrev CommonRadialPhase := AddCircle (1 : ℝ)

abbrev CommonRadialPrimeSpace := lp (fun _ : Nat.Primes => ℂ) 2

abbrev CommonRadialPhaseBoundary :=
  Lp CommonRadialPrimeSpace 2 unitCircleHaar

theorem norm_commonRadialPrimeBasis (p : Nat.Primes) :
    ‖HilbertSchmidt.lpBasis Nat.Primes p‖ = 1 :=
  (HilbertSchmidt.lpBasis Nat.Primes).orthonormal.1 p

/-- Vector-valued nonnegative Fourier mode carrying one history grade and one prime. -/
def commonRadialHardyMode (np : PrimeHodgeHistoryIndex) :
    CommonRadialPhaseBoundary :=
  lpUnitVectorEmbedding unitCircleHaar
      (HilbertSchmidt.lpBasis Nat.Primes np.2)
      (norm_commonRadialPrimeBasis np.2)
      (fourierLp 2 (np.1 : ℤ))

theorem inner_commonRadialHardyMode (i j : PrimeHodgeHistoryIndex) :
    inner ℂ (commonRadialHardyMode i) (commonRadialHardyMode j) =
      if i = j then 1 else 0 := by
  rw [commonRadialHardyMode, commonRadialHardyMode,
    inner_lpUnitVectorEmbedding_cross,
    GaloisForLFunctions.inner_fourierLp_fourierLp]
  have hprime := (HilbertSchmidt.lpBasis Nat.Primes).orthonormal
  rw [(orthonormal_iff_ite.mp hprime) i.2 j.2]
  by_cases hn : i.1 = j.1 <;> by_cases hp : i.2 = j.2
  · have hij : i = j := Prod.ext hn hp
    simp [hn, hp, hij]
  · have hij : i ≠ j := fun h => hp (congrArg Prod.snd h)
    simp [hn, hp, hij]
  · have hij : i ≠ j := fun h => hn (congrArg Prod.fst h)
    simp [hn, hp, hij]
  · have hij : i ≠ j := fun h => hn (congrArg Prod.fst h)
    simp [hn, hp, hij]

theorem orthonormal_commonRadialHardyMode :
    Orthonormal ℂ commonRadialHardyMode := by
  rw [orthonormal_iff_ite]
  exact inner_commonRadialHardyMode

theorem summable_norm_inner_commonRadialHardyMode_sq
    (x : CommonRadialPhaseBoundary) :
    Summable fun i : PrimeHodgeHistoryIndex =>
      ‖inner ℂ (commonRadialHardyMode i) x‖ ^ (2 : ℝ) := by
  apply summable_of_sum_le (fun i => by positivity)
  intro s
  simpa [Real.rpow_two] using
    orthonormal_commonRadialHardyMode.sum_inner_products_le x (s := s)

theorem tsum_norm_inner_commonRadialHardyMode_sq_le
    (x : CommonRadialPhaseBoundary) :
    ∑' i : PrimeHodgeHistoryIndex,
        ‖inner ℂ (commonRadialHardyMode i) x‖ ^ (2 : ℝ) ≤
      (1 * ‖x‖) ^ (2 : ℝ) := by
  simpa [Real.rpow_two] using
    orthonormal_commonRadialHardyMode.tsum_inner_products_le x

/-- Isometric Hardy synthesis from prime history to vector-valued circle `L²`. -/
def commonRadialHardySynthesis :
    PrimeHodgeHistoryHilbert →L[ℂ] CommonRadialPhaseBoundary :=
  besselFamilySynthesisOperator commonRadialHardyMode
    summable_norm_inner_commonRadialHardyMode_sq (by norm_num)
    tsum_norm_inner_commonRadialHardyMode_sq_le

theorem commonRadialHardySynthesis_basis (i : PrimeHodgeHistoryIndex) :
    commonRadialHardySynthesis (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i) =
      commonRadialHardyMode i := by
  rw [commonRadialHardySynthesis]
  simpa [HilbertSchmidt.lpBasis_apply] using
    besselFamilySynthesisOperator_coordinateBasis commonRadialHardyMode
      summable_norm_inner_commonRadialHardyMode_sq (by norm_num)
      tsum_norm_inner_commonRadialHardyMode_sq_le i

theorem commonRadialHardyMode_coeFn
    (n : ℕ) (p : Nat.Primes) :
    ((commonRadialHardyMode (n, p) : CommonRadialPhaseBoundary) :
        CommonRadialPhase → CommonRadialPrimeSpace) =ᵐ[unitCircleHaar]
      fun z => fourier (n : ℤ) z • HilbertSchmidt.lpBasis Nat.Primes p := by
  have hcomp :=
    (scalarToUnitVectorIsometry
      (HilbertSchmidt.lpBasis Nat.Primes p)
      (norm_commonRadialPrimeBasis p)).toContinuousLinearMap.coeFn_compLp
        (fourierLp (T := (1 : ℝ)) 2 (n : ℤ))
  have hfourier := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) unitCircleHaar
    (fourier (T := (1 : ℝ)) (n : ℤ))
  filter_upwards [hcomp, hfourier] with z hcompz hfourierz
  change (((scalarToUnitVectorIsometry
      (HilbertSchmidt.lpBasis Nat.Primes p)
      (norm_commonRadialPrimeBasis p)).toContinuousLinearMap.compLp
        (fourierLp (T := (1 : ℝ)) 2 (n : ℤ)) : CommonRadialPhaseBoundary) :
          CommonRadialPhase → CommonRadialPrimeSpace) z = _
  rw [hcompz, hfourierz]
  rfl

theorem adjoint_comp_commonRadialHardySynthesis :
    ContinuousLinearMap.adjoint commonRadialHardySynthesis ∘L
        commonRadialHardySynthesis =
      ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert := by
  apply continuousLinearMap_eq_of_eq_on_hilbertBasis
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)
  intro i
  apply (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).repr.injective
  ext j
  rw [(HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).repr_apply_apply,
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).repr_apply_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [ContinuousLinearMap.adjoint_inner_right,
    commonRadialHardySynthesis_basis,
    commonRadialHardySynthesis_basis, inner_commonRadialHardyMode]
  have hb := (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).orthonormal
  rw [(orthonormal_iff_ite.mp hb) j i]

theorem norm_commonRadialHardySynthesis (x : PrimeHodgeHistoryHilbert) :
    ‖commonRadialHardySynthesis x‖ = ‖x‖ := by
  have hinner : inner ℂ (commonRadialHardySynthesis x)
      (commonRadialHardySynthesis x) = inner ℂ x x := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ x
      ((ContinuousLinearMap.adjoint commonRadialHardySynthesis ∘L
        commonRadialHardySynthesis) x) =
        inner ℂ x x
    rw [adjoint_comp_commonRadialHardySynthesis]
    rfl
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
  have hsq : ‖commonRadialHardySynthesis x‖ ^ (2 : ℕ) =
      ‖x‖ ^ (2 : ℕ) := by
    exact_mod_cast hinner
  nlinarith [norm_nonneg (commonRadialHardySynthesis x), norm_nonneg x]

def commonRadialHardyIsometry :
    PrimeHodgeHistoryHilbert →ₗᵢ[ℂ] CommonRadialPhaseBoundary :=
  LinearIsometry.mk commonRadialHardySynthesis norm_commonRadialHardySynthesis

/-! ## Bounded measurable operator-valued multiplication on `L²` -/

theorem eLpNorm_operatorFamily_apply_le_of_ae_bound
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {μ : Measure X} {A : X → H →L[ℂ] H} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C)
    (f : Lp H 2 μ) :
    eLpNorm (fun x => A x ((f : X → H) x)) 2 μ ≤
      ENNReal.ofReal C * eLpNorm (f : X → H) 2 μ := by
  have hmono :
      eLpNorm (fun x => A x ((f : X → H) x)) 2 μ ≤
        eLpNorm (((C : ℝ) : ℂ) • (f : X → H)) 2 μ := by
    apply eLpNorm_mono_ae
    filter_upwards [hC] with x hx
    rw [Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hC0]
    exact le_trans ((A x).le_opNorm _) (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  rw [eLpNorm_const_smul] at hmono
  have hnorm : ‖((C : ℝ) : ℂ)‖ₑ = ENNReal.ofReal C := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC0]
  rwa [hnorm] at hmono

theorem memLp_operatorFamily_apply_of_ae_bound
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {μ : Measure X} {A : X → H →L[ℂ] H}
    (hA : AEStronglyMeasurable A μ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C)
    (f : Lp H 2 μ) :
    MemLp (fun x => A x ((f : X → H) x)) 2 μ := by
  constructor
  · exact aeStronglyMeasurable_operatorFamily_apply hA f
  · refine lt_of_le_of_lt
      (eLpNorm_operatorFamily_apply_le_of_ae_bound hC0 hC f) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_ne_top f).lt_top

def lpBoundedOperatorFamilyLM
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {μ : Measure X} {A : X → H →L[ℂ] H}
    (hA : AEStronglyMeasurable A μ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) :
    Lp H 2 μ →ₗ[ℂ] Lp H 2 μ where
  toFun f := (memLp_operatorFamily_apply_of_ae_bound hA hC0 hC f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [
      MemLp.coeFn_toLp
        (memLp_operatorFamily_apply_of_ae_bound hA hC0 hC (f + g)),
      Lp.coeFn_add
        ((memLp_operatorFamily_apply_of_ae_bound hA hC0 hC f).toLp _)
        ((memLp_operatorFamily_apply_of_ae_bound hA hC0 hC g).toLp _),
      MemLp.coeFn_toLp
        (memLp_operatorFamily_apply_of_ae_bound hA hC0 hC f),
      MemLp.coeFn_toLp
        (memLp_operatorFamily_apply_of_ae_bound hA hC0 hC g),
      Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [
      MemLp.coeFn_toLp
        (memLp_operatorFamily_apply_of_ae_bound hA hC0 hC (c • f)),
      Lp.coeFn_smul c
        ((memLp_operatorFamily_apply_of_ae_bound hA hC0 hC f).toLp _),
      MemLp.coeFn_toLp
        (memLp_operatorFamily_apply_of_ae_bound hA hC0 hC f),
      Lp.coeFn_smul c f] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply, map_smul]

def lpBoundedOperatorFamilyCLM
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {μ : Measure X} {A : X → H →L[ℂ] H}
    (hA : AEStronglyMeasurable A μ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) :
    Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  LinearMap.mkContinuous (lpBoundedOperatorFamilyLM hA hC0 hC) C (by
    intro f
    change ‖(memLp_operatorFamily_apply_of_ae_bound hA hC0 hC f).toLp _‖ ≤ C * ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    have hle := eLpNorm_operatorFamily_apply_le_of_ae_bound hC0 hC f
    have hfin : eLpNorm ((f : X → H)) 2 μ ≠ ∞ := Lp.eLpNorm_ne_top f
    have htoReal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle
    refine htoReal.trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0])

theorem lpBoundedOperatorFamilyCLM_coeFn
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {μ : Measure X} {A : X → H →L[ℂ] H}
    (hA : AEStronglyMeasurable A μ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C)
    (f : Lp H 2 μ) :
    ((lpBoundedOperatorFamilyCLM hA hC0 hC f : Lp H 2 μ) : X → H) =ᵐ[μ]
      fun x => A x ((f : X → H) x) :=
  MemLp.coeFn_toLp (memLp_operatorFamily_apply_of_ae_bound hA hC0 hC f)

theorem norm_lpBoundedOperatorFamilyCLM_le
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {μ : Measure X} {A : X → H →L[ℂ] H}
    (hA : AEStronglyMeasurable A μ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) :
    ‖lpBoundedOperatorFamilyCLM hA hC0 hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC0 _

theorem integrable_inner_l2
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {μ : Measure X} (f g : Lp H 2 μ) :
    Integrable (fun x : X => inner ℂ ((f : X → H) x) ((g : X → H) x)) μ := by
  have hprod : Integrable
      ((fun x : X => ‖((f : X → H) x)‖) *
        (fun x : X => ‖((g : X → H) x)‖)) μ :=
    MemLp.integrable_mul (Lp.memLp f).norm (Lp.memLp g).norm
  exact Integrable.mono' hprod
    ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g))
    (Filter.Eventually.of_forall fun x => norm_inner_le_norm _ _)

/-- Pointwise positivity passes to bounded operator-valued multiplication on `L²`. -/
theorem lpBoundedOperatorFamilyCLM_isPositive
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {μ : Measure X} {A : X → H →L[ℂ] H}
    (hA : AEStronglyMeasurable A μ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C)
    (hpos : ∀ᵐ x ∂μ, (A x).IsPositive) :
    (lpBoundedOperatorFamilyCLM hA hC0 hC).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · intro f g
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [
      lpBoundedOperatorFamilyCLM_coeFn hA hC0 hC f,
      lpBoundedOperatorFamilyCLM_coeFn hA hC0 hC g,
      hpos] with x hfx hgx hx
    change inner ℂ
        ((((lpBoundedOperatorFamilyCLM hA hC0 hC) f : Lp H 2 μ) : X → H) x)
        ((g : X → H) x) =
      inner ℂ ((f : X → H) x)
        ((((lpBoundedOperatorFamilyCLM hA hC0 hC) g : Lp H 2 μ) : X → H) x)
    rw [hfx, hgx]
    exact hx.inner_left_eq_inner_right
      ((f : X → H) x) ((g : X → H) x)
  · intro f
    rw [L2.inner_def]
    let q : X → ℂ := fun x =>
      inner ℂ (A x ((f : X → H) x)) ((f : X → H) x)
    have hMf := lpBoundedOperatorFamilyCLM_coeFn hA hC0 hC f
    have hqint : Integrable q μ := by
      have hM : Integrable (fun x : X =>
          inner ℂ
            (((lpBoundedOperatorFamilyCLM hA hC0 hC f : Lp H 2 μ) : X → H) x)
            ((f : X → H) x)) μ :=
        integrable_inner_l2 (lpBoundedOperatorFamilyCLM hA hC0 hC f) f
      exact hM.congr (by
        filter_upwards [hMf] with x hx
        rw [hx])
    have hint :
        ∫ x : X,
            inner ℂ
              (((lpBoundedOperatorFamilyCLM hA hC0 hC f : Lp H 2 μ) : X → H) x)
              ((f : X → H) x) ∂μ =
          ∫ x : X, q x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hMf] with x hx
      rw [hx]
    rw [hint, Complex.nonneg_iff]
    constructor
    · have hre := Complex.reCLM.integral_comp_comm hqint
      change (∫ x : X, (q x).re ∂μ) = (∫ x : X, q x ∂μ).re at hre
      rw [← hre]
      apply integral_nonneg_of_ae
      filter_upwards [hpos] with x hx
      exact (Complex.nonneg_iff.mp
        (((ContinuousLinearMap.isPositive_iff (A x)).mp hx).2
          ((f : X → H) x))).1
    · have him := Complex.imCLM.integral_comp_comm hqint
      change (∫ x : X, (q x).im ∂μ) = (∫ x : X, q x ∂μ).im at him
      rw [← him]
      symm
      apply integral_eq_zero_of_ae
      filter_upwards [hpos] with x hx
      exact (Complex.nonneg_iff.mp
        (((ContinuousLinearMap.isPositive_iff (A x)).mp hx).2
          ((f : X → H) x))).2.symm

/-! ## Contractive radial phase fields and source densities -/

structure CommonRadialPhaseContractionField where
  toFun : CommonRadialPhase →
    CommonRadialSpace →L[ℂ] CommonRadialSpace
  aestronglyMeasurable_toFun :
    AEStronglyMeasurable toFun unitCircleHaar
  norm_le_one : ∀ᵐ z ∂unitCircleHaar, ‖toFun z‖ ≤ 1

instance : CoeFun CommonRadialPhaseContractionField
    (fun _ => CommonRadialPhase →
      CommonRadialSpace →L[ℂ] CommonRadialSpace) :=
  ⟨CommonRadialPhaseContractionField.toFun⟩

/-- One radial endomorphism inserted between fixed prime reachability and primitive source. -/
def commonRadialSourceSynthesisAt
    (a : {d : ℝ // 0 < d})
    (A : CommonRadialSpace →L[ℂ] CommonRadialSpace) :
    CommonRadialBurnolSourceSpace →L[ℂ] CommonRadialPrimeSpace :=
  commonRadialPrimeReachability a ∘L A ∘L
    routePPrimitiveBurnolBaseSynthesis

theorem commonRadialSourceSynthesisAt_isHilbertSchmidt
    (a : {d : ℝ // 0 < d})
    (A : CommonRadialSpace →L[ℂ] CommonRadialSpace) :
    (commonRadialSourceSynthesisAt a A).IsHilbertSchmidt := by
  exact (routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt.comp_left A).comp_left
    (commonRadialPrimeReachability a)

/-- Phase-resolved synthesis `W_d V(z) B_base`. -/
def commonRadialPhaseSourceSynthesis
    (a : {d : ℝ // 0 < d})
    (V : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    CommonRadialBurnolSourceSpace →L[ℂ] CommonRadialPrimeSpace :=
  commonRadialSourceSynthesisAt a (V z)

/-- Positive trace-class prime covariance density `W_d V(z) S_base V(z)† W_d†`. -/
def commonRadialPhaseSourceDensity
    (a : {d : ℝ // 0 < d})
    (V : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    CommonRadialPrimeSpace →L[ℂ] CommonRadialPrimeSpace :=
  rangeCovariance (commonRadialPhaseSourceSynthesis a V z)

theorem commonRadialPhaseSourceSynthesis_isHilbertSchmidt
    (a : {d : ℝ // 0 < d})
    (V : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    (commonRadialPhaseSourceSynthesis a V z).IsHilbertSchmidt := by
  exact commonRadialSourceSynthesisAt_isHilbertSchmidt a (V z)

theorem commonRadialPhaseSourceDensity_eq_sandwich
    (a : {d : ℝ // 0 < d})
    (V : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    commonRadialPhaseSourceDensity a V z =
      commonRadialPrimeReachability a ∘L V z ∘L
        routePPrimitiveBurnolBaseNuclearSource ∘L
          ContinuousLinearMap.adjoint (V z) ∘L commonRadialPrimeSynthesis a := by
  unfold commonRadialPhaseSourceDensity commonRadialPhaseSourceSynthesis
    commonRadialSourceSynthesisAt
    routePPrimitiveBurnolBaseNuclearSource rangeCovariance
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
  rw [show ContinuousLinearMap.adjoint (commonRadialPrimeReachability a) =
      commonRadialPrimeSynthesis a by
    rw [commonRadialPrimeReachability, ContinuousLinearMap.adjoint_adjoint]]
  ext x
  rfl

theorem commonRadialPhaseSourceDensity_isPositive
    (a : {d : ℝ // 0 < d})
    (V : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    (commonRadialPhaseSourceDensity a V z).IsPositive :=
  rangeCovariance_isPositive (commonRadialPhaseSourceSynthesis a V z)

theorem commonRadialPhaseSourceDensity_memSchattenClass_one
    (a : {d : ℝ // 0 < d})
    (V : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    MemSchattenClass 1 (commonRadialPhaseSourceDensity a V z) :=
  rangeCovariance_memSchattenClass_one_of_hilbertSchmidt
    (commonRadialPhaseSourceSynthesis_isHilbertSchmidt a V z)

theorem re_opTrace_commonRadialPhaseSourceDensity_eq_hsNormSq
    (a : {d : ℝ // 0 < d})
    (V : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    (ContinuousLinearMap.opTrace
      (commonRadialPhaseSourceDensity a V z)).re =
        ContinuousLinearMap.hsNormSq
          (commonRadialPhaseSourceSynthesis a V z) :=
  re_opTrace_rangeCovariance_eq_hsNormSq
    (commonRadialPhaseSourceSynthesis_isHilbertSchmidt a V z)

theorem hsNormSq_commonRadialPhaseSourceSynthesis_le
    (a : {d : ℝ // 0 < d})
    (V : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    ContinuousLinearMap.hsNormSq
        (commonRadialPhaseSourceSynthesis a V z) ≤
      ‖commonRadialPrimeReachability a‖ ^ 2 * ‖V z‖ ^ 2 *
        routePPrimitiveBaseCauchyCubicTraceBudget := by
  have hinner := ContinuousLinearMap.hsNormSq_comp_left_le
    routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt (V z)
  have houter := ContinuousLinearMap.hsNormSq_comp_left_le
    (routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt.comp_left (V z))
    (commonRadialPrimeReachability a)
  rw [hsNormSq_routePPrimitiveBurnolBaseSynthesis_eq_budget] at hinner
  calc
    ContinuousLinearMap.hsNormSq
        (commonRadialPhaseSourceSynthesis a V z) ≤
      ‖commonRadialPrimeReachability a‖ ^ 2 *
        ContinuousLinearMap.hsNormSq
          ((V z) ∘L routePPrimitiveBurnolBaseSynthesis) := by
      simpa [commonRadialPhaseSourceSynthesis,
        commonRadialSourceSynthesisAt] using houter
    _ ≤ ‖commonRadialPrimeReachability a‖ ^ 2 *
        (‖V z‖ ^ 2 * routePPrimitiveBaseCauchyCubicTraceBudget) := by
      exact mul_le_mul_of_nonneg_left hinner (sq_nonneg _)
    _ = ‖commonRadialPrimeReachability a‖ ^ 2 * ‖V z‖ ^ 2 *
        routePPrimitiveBaseCauchyCubicTraceBudget := by ring

theorem re_opTrace_commonRadialPhaseSourceDensity_le
    (a : {d : ℝ // 0 < d})
    (V : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    (ContinuousLinearMap.opTrace
      (commonRadialPhaseSourceDensity a V z)).re ≤
      ‖commonRadialPrimeReachability a‖ ^ 2 * ‖V z‖ ^ 2 *
        routePPrimitiveBaseCauchyCubicTraceBudget := by
  rw [re_opTrace_commonRadialPhaseSourceDensity_eq_hsNormSq]
  exact hsNormSq_commonRadialPhaseSourceSynthesis_le a V z

theorem ae_re_opTrace_commonRadialPhaseSourceDensity_le
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    ∀ᵐ z ∂unitCircleHaar,
      (ContinuousLinearMap.opTrace
        (commonRadialPhaseSourceDensity a V z)).re ≤
        ‖commonRadialPrimeReachability a‖ ^ 2 *
          routePPrimitiveBaseCauchyCubicTraceBudget := by
  filter_upwards [V.norm_le_one] with z hz
  calc
    (ContinuousLinearMap.opTrace
        (commonRadialPhaseSourceDensity a V z)).re ≤
      ‖commonRadialPrimeReachability a‖ ^ 2 * ‖V z‖ ^ 2 *
        routePPrimitiveBaseCauchyCubicTraceBudget :=
      re_opTrace_commonRadialPhaseSourceDensity_le a V z
    _ ≤ ‖commonRadialPrimeReachability a‖ ^ 2 *
        routePPrimitiveBaseCauchyCubicTraceBudget := by
      have hz2 : ‖V z‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg (V z)]
      have hb0 : 0 ≤ routePPrimitiveBaseCauchyCubicTraceBudget :=
        routePPrimitiveBaseCauchyCubicTraceBudget_pos.le
      calc
        ‖commonRadialPrimeReachability a‖ ^ 2 * ‖V z‖ ^ 2 *
            routePPrimitiveBaseCauchyCubicTraceBudget =
          ‖commonRadialPrimeReachability a‖ ^ 2 *
            (‖V z‖ ^ 2 * routePPrimitiveBaseCauchyCubicTraceBudget) := by ring
        _ ≤ ‖commonRadialPrimeReachability a‖ ^ 2 *
            (1 * routePPrimitiveBaseCauchyCubicTraceBudget) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hz2 hb0) (sq_nonneg _)
        _ = _ := by ring

theorem ae_norm_commonRadialPhaseSourceDensity_le
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    ∀ᵐ z ∂unitCircleHaar,
      ‖commonRadialPhaseSourceDensity a V z‖ ≤
        ‖commonRadialPrimeReachability a‖ ^ 2 *
          routePPrimitiveBaseCauchyCubicTraceBudget := by
  filter_upwards [ae_re_opTrace_commonRadialPhaseSourceDensity_le a V] with z hz
  exact le_trans
    (norm_le_traceNorm
      (commonRadialPhaseSourceDensity_memSchattenClass_one a V z).one_summable)
    (by
      rw [traceNorm_eq_re_opTrace_of_isPositive
        (commonRadialPhaseSourceDensity_memSchattenClass_one a V z)
        (commonRadialPhaseSourceDensity_isPositive a V z)]
      exact hz)

theorem aestronglyMeasurable_commonRadialPhaseSourceSynthesis
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    AEStronglyMeasurable
      (commonRadialPhaseSourceSynthesis a V) unitCircleHaar := by
  exact (show Continuous (fun T : CommonRadialSpace →L[ℂ] CommonRadialSpace =>
      commonRadialPrimeReachability a ∘L T ∘L
        routePPrimitiveBurnolBaseSynthesis) by fun_prop).comp_aestronglyMeasurable
    V.aestronglyMeasurable_toFun

/-- The source density bundled in the genuine trace-norm Banach carrier. -/
def commonRadialPhaseSourceDensitySchatten
    (a : {d : ℝ // 0 < d})
    (V : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    SchattenOneOperator CommonRadialPrimeSpace :=
  ⟨commonRadialPhaseSourceDensity a V z,
    commonRadialPhaseSourceDensity_memSchattenClass_one a V z⟩

theorem commonRadialPhaseSourceDensitySchatten_coe
    (a : {d : ℝ // 0 < d})
    (V : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    (commonRadialPhaseSourceDensitySchatten a V z :
      CommonRadialPrimeSpace →L[ℂ] CommonRadialPrimeSpace) =
        commonRadialPhaseSourceDensity a V z := rfl

theorem rangeCovariance_sub_decomposition
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (S T : E →L[ℂ] F) :
    rangeCovariance S - rangeCovariance T =
      (S - T) ∘L ContinuousLinearMap.adjoint S +
        T ∘L ContinuousLinearMap.adjoint (S - T) := by
  unfold rangeCovariance
  rw [show ContinuousLinearMap.adjoint (S - T) =
      ContinuousLinearMap.adjoint S - ContinuousLinearMap.adjoint T by
    exact map_sub ContinuousLinearMap.adjoint S T]
  ext x
  simp only [_root_.sub_apply, _root_.add_apply,
    ContinuousLinearMap.comp_apply]
  simp only [map_sub]
  abel

theorem hsNorm_adjoint_eq
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {S : E →L[ℂ] F} (hS : S.IsHilbertSchmidt) :
    ContinuousLinearMap.hsNorm (ContinuousLinearMap.adjoint S) =
      ContinuousLinearMap.hsNorm S := by
  rw [ContinuousLinearMap.hsNorm, ContinuousLinearMap.hsNorm,
    hS.hsNormSq_adjoint]

theorem norm_rangeCovarianceSchatten_sub_le
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {S T : E →L[ℂ] F} (hS : S.IsHilbertSchmidt)
    (hT : T.IsHilbertSchmidt) :
    ‖(⟨rangeCovariance S,
          rangeCovariance_memSchattenClass_one_of_hilbertSchmidt hS⟩ :
        SchattenOneOperator F) -
      (⟨rangeCovariance T,
          rangeCovariance_memSchattenClass_one_of_hilbertSchmidt hT⟩ :
        SchattenOneOperator F)‖ ≤
      ContinuousLinearMap.hsNorm (S - T) *
        (ContinuousLinearMap.hsNorm S + ContinuousLinearMap.hsNorm T) := by
  have hsub : (S - T).IsHilbertSchmidt := hS.sub hT
  have hfirst : MemSchattenClass 1
      ((S - T) ∘L ContinuousLinearMap.adjoint S) := by
    apply (memRectSchattenClass_iff_memSchattenClass 1 _).mp
    exact memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted
      hS.adjoint hsub
  have hsecond : MemSchattenClass 1
      (T ∘L ContinuousLinearMap.adjoint (S - T)) := by
    apply (memRectSchattenClass_iff_memSchattenClass 1 _).mp
    exact memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted
      hsub.adjoint hT
  let A : SchattenOneOperator F :=
    ⟨(S - T) ∘L ContinuousLinearMap.adjoint S, hfirst⟩
  let B : SchattenOneOperator F :=
    ⟨T ∘L ContinuousLinearMap.adjoint (S - T), hsecond⟩
  have hdecomp :
      (⟨rangeCovariance S,
          rangeCovariance_memSchattenClass_one_of_hilbertSchmidt hS⟩ :
        SchattenOneOperator F) -
      (⟨rangeCovariance T,
          rangeCovariance_memSchattenClass_one_of_hilbertSchmidt hT⟩ :
        SchattenOneOperator F) = A + B := by
    apply SchattenOneOperator.ext
    exact rangeCovariance_sub_decomposition S T
  rw [hdecomp]
  calc
    ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    _ ≤ ContinuousLinearMap.hsNorm S * ContinuousLinearMap.hsNorm (S - T) +
        ContinuousLinearMap.hsNorm (S - T) * ContinuousLinearMap.hsNorm T := by
      gcongr
      · change traceNorm F
          ((S - T) ∘L ContinuousLinearMap.adjoint S) ≤ _
        rw [← rectTraceNorm_eq_traceNorm]
        have hbound :=
          rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted
            hS.adjoint hsub
        rw [hsNorm_adjoint_eq hS] at hbound
        exact hbound
      · change traceNorm F
          (T ∘L ContinuousLinearMap.adjoint (S - T)) ≤ _
        rw [← rectTraceNorm_eq_traceNorm]
        have hbound :=
          rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted
            hsub.adjoint hT
        rw [hsNorm_adjoint_eq hsub] at hbound
        exact hbound
    _ = ContinuousLinearMap.hsNorm (S - T) *
        (ContinuousLinearMap.hsNorm S + ContinuousLinearMap.hsNorm T) := by ring

theorem commonRadialSourceSynthesisAt_sub
    (a : {d : ℝ // 0 < d})
    (A B : CommonRadialSpace →L[ℂ] CommonRadialSpace) :
    commonRadialSourceSynthesisAt a A -
        commonRadialSourceSynthesisAt a B =
      commonRadialPrimeReachability a ∘L (A - B) ∘L
        routePPrimitiveBurnolBaseSynthesis := by
  ext x
  simp [commonRadialSourceSynthesisAt]

theorem hsNorm_commonRadialSourceSynthesisAt_le
    (a : {d : ℝ // 0 < d})
    (A : CommonRadialSpace →L[ℂ] CommonRadialSpace) :
    ContinuousLinearMap.hsNorm (commonRadialSourceSynthesisAt a A) ≤
      ‖commonRadialPrimeReachability a‖ * ‖A‖ *
        ContinuousLinearMap.hsNorm routePPrimitiveBurnolBaseSynthesis := by
  have hinner := ContinuousLinearMap.hsNorm_comp_left_le
    (S := A) routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt
  have houter := ContinuousLinearMap.hsNorm_comp_left_le
    (S := commonRadialPrimeReachability a)
    (routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt.comp_left A)
  calc
    ContinuousLinearMap.hsNorm (commonRadialSourceSynthesisAt a A) ≤
        ‖commonRadialPrimeReachability a‖ *
          ContinuousLinearMap.hsNorm
            (A ∘L routePPrimitiveBurnolBaseSynthesis) := by
      simpa [commonRadialSourceSynthesisAt] using houter
    _ ≤ ‖commonRadialPrimeReachability a‖ *
        (‖A‖ * ContinuousLinearMap.hsNorm
          routePPrimitiveBurnolBaseSynthesis) := by
      exact mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    _ = _ := by ring

theorem hsNorm_commonRadialSourceSynthesisAt_sub_le
    (a : {d : ℝ // 0 < d})
    (A B : CommonRadialSpace →L[ℂ] CommonRadialSpace) :
    ContinuousLinearMap.hsNorm
        (commonRadialSourceSynthesisAt a A -
          commonRadialSourceSynthesisAt a B) ≤
      ‖commonRadialPrimeReachability a‖ * ‖A - B‖ *
        ContinuousLinearMap.hsNorm routePPrimitiveBurnolBaseSynthesis := by
  rw [commonRadialSourceSynthesisAt_sub]
  exact hsNorm_commonRadialSourceSynthesisAt_le a (A - B)

/-- Covariance map into trace class, defined on every bounded radial endomorphism. -/
def commonRadialSourceDensitySchattenAt
    (a : {d : ℝ // 0 < d})
    (A : CommonRadialSpace →L[ℂ] CommonRadialSpace) :
    SchattenOneOperator CommonRadialPrimeSpace :=
  ⟨rangeCovariance (commonRadialSourceSynthesisAt a A),
    rangeCovariance_memSchattenClass_one_of_hilbertSchmidt
      (commonRadialSourceSynthesisAt_isHilbertSchmidt a A)⟩

theorem norm_commonRadialSourceDensitySchattenAt_sub_le
    (a : {d : ℝ // 0 < d})
    (A B : CommonRadialSpace →L[ℂ] CommonRadialSpace) :
    ‖commonRadialSourceDensitySchattenAt a A -
        commonRadialSourceDensitySchattenAt a B‖ ≤
      (‖commonRadialPrimeReachability a‖ * ‖A - B‖ *
          ContinuousLinearMap.hsNorm routePPrimitiveBurnolBaseSynthesis) *
        (‖commonRadialPrimeReachability a‖ * ‖A‖ *
            ContinuousLinearMap.hsNorm routePPrimitiveBurnolBaseSynthesis +
          ‖commonRadialPrimeReachability a‖ * ‖B‖ *
            ContinuousLinearMap.hsNorm routePPrimitiveBurnolBaseSynthesis) := by
  let S := commonRadialSourceSynthesisAt a A
  let T := commonRadialSourceSynthesisAt a B
  calc
    ‖commonRadialSourceDensitySchattenAt a A -
        commonRadialSourceDensitySchattenAt a B‖ ≤
      ContinuousLinearMap.hsNorm (S - T) *
        (ContinuousLinearMap.hsNorm S + ContinuousLinearMap.hsNorm T) := by
      exact norm_rangeCovarianceSchatten_sub_le
        (commonRadialSourceSynthesisAt_isHilbertSchmidt a A)
        (commonRadialSourceSynthesisAt_isHilbertSchmidt a B)
    _ ≤ (‖commonRadialPrimeReachability a‖ * ‖A - B‖ *
          ContinuousLinearMap.hsNorm routePPrimitiveBurnolBaseSynthesis) *
        (‖commonRadialPrimeReachability a‖ * ‖A‖ *
            ContinuousLinearMap.hsNorm routePPrimitiveBurnolBaseSynthesis +
          ‖commonRadialPrimeReachability a‖ * ‖B‖ *
            ContinuousLinearMap.hsNorm routePPrimitiveBurnolBaseSynthesis) := by
      exact mul_le_mul
        (hsNorm_commonRadialSourceSynthesisAt_sub_le a A B)
        (add_le_add
          (hsNorm_commonRadialSourceSynthesisAt_le a A)
          (hsNorm_commonRadialSourceSynthesisAt_le a B))
        (add_nonneg (ContinuousLinearMap.hsNorm_nonneg S)
          (ContinuousLinearMap.hsNorm_nonneg T))
        (mul_nonneg
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (ContinuousLinearMap.hsNorm_nonneg
            routePPrimitiveBurnolBaseSynthesis))

theorem continuous_commonRadialSourceDensitySchattenAt
    (a : {d : ℝ // 0 < d}) :
    Continuous (commonRadialSourceDensitySchattenAt a) := by
  rw [continuous_iff_continuousAt]
  intro A
  change Tendsto (commonRadialSourceDensitySchattenAt a) (𝓝 A)
    (𝓝 (commonRadialSourceDensitySchattenAt a A))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun B => norm_nonneg _)
    (fun B => norm_commonRadialSourceDensitySchattenAt_sub_le a B A) ?_
  have hcont : ContinuousAt
      (fun B : CommonRadialSpace →L[ℂ] CommonRadialSpace =>
        (‖commonRadialPrimeReachability a‖ * ‖B - A‖ *
            ContinuousLinearMap.hsNorm routePPrimitiveBurnolBaseSynthesis) *
          (‖commonRadialPrimeReachability a‖ * ‖B‖ *
              ContinuousLinearMap.hsNorm routePPrimitiveBurnolBaseSynthesis +
            ‖commonRadialPrimeReachability a‖ * ‖A‖ *
              ContinuousLinearMap.hsNorm routePPrimitiveBurnolBaseSynthesis)) A := by
    fun_prop
  convert hcont.tendsto using 1 <;> simp

theorem commonRadialPhaseSourceDensitySchatten_eq_at
    (a : {d : ℝ // 0 < d})
    (V : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    commonRadialPhaseSourceDensitySchatten a V z =
      commonRadialSourceDensitySchattenAt a (V z) := by
  rfl

theorem aestronglyMeasurable_commonRadialPhaseSourceDensitySchatten
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    AEStronglyMeasurable
      (commonRadialPhaseSourceDensitySchatten a V) unitCircleHaar := by
  exact (continuous_commonRadialSourceDensitySchattenAt a).comp_aestronglyMeasurable
    V.aestronglyMeasurable_toFun

theorem aestronglyMeasurable_commonRadialPhaseSourceDensity
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    AEStronglyMeasurable
      (commonRadialPhaseSourceDensity a V) unitCircleHaar := by
  simpa [commonRadialPhaseSourceDensitySchatten_coe] using
    (schattenOneCoeCLM (H := CommonRadialPrimeSpace)).continuous.comp_aestronglyMeasurable
      (aestronglyMeasurable_commonRadialPhaseSourceDensitySchatten a V)

theorem ae_norm_commonRadialPhaseSourceDensitySchatten_le
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    ∀ᵐ z ∂unitCircleHaar,
      ‖commonRadialPhaseSourceDensitySchatten a V z‖ ≤
        ‖commonRadialPrimeReachability a‖ ^ 2 *
          routePPrimitiveBaseCauchyCubicTraceBudget := by
  filter_upwards [ae_re_opTrace_commonRadialPhaseSourceDensity_le a V] with z hz
  change traceNorm CommonRadialPrimeSpace
      (commonRadialPhaseSourceDensity a V z) ≤ _
  rw [traceNorm_eq_re_opTrace_of_isPositive
    (commonRadialPhaseSourceDensity_memSchattenClass_one a V z)
    (commonRadialPhaseSourceDensity_isPositive a V z)]
  exact hz

theorem integrable_commonRadialPhaseSourceDensitySchatten
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    Integrable (commonRadialPhaseSourceDensitySchatten a V) unitCircleHaar :=
  Integrable.of_bound
    (aestronglyMeasurable_commonRadialPhaseSourceDensitySchatten a V) _
    (ae_norm_commonRadialPhaseSourceDensitySchatten_le a V)

theorem integrable_fourier_smul_commonRadialPhaseSourceDensitySchatten
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (j : ℤ) :
    Integrable (fun z : CommonRadialPhase =>
      fourier j z • commonRadialPhaseSourceDensitySchatten a V z)
        unitCircleHaar := by
  have hmeas : AEStronglyMeasurable (fun z : CommonRadialPhase =>
      fourier j z • commonRadialPhaseSourceDensitySchatten a V z)
      unitCircleHaar :=
    (fourier j).continuous.aestronglyMeasurable.smul
      (aestronglyMeasurable_commonRadialPhaseSourceDensitySchatten a V)
  refine Integrable.of_bound hmeas
    (‖commonRadialPrimeReachability a‖ ^ 2 *
      routePPrimitiveBaseCauchyCubicTraceBudget) ?_
  filter_upwards [ae_norm_commonRadialPhaseSourceDensitySchatten_le a V]
    with z hz
  rw [norm_smul, GaloisForLFunctions.HTGeometry.norm_fourier_eq_one,
    one_mul]
  exact hz

/-- Schatten-one Fourier coefficient of the positive source density. -/
def commonRadialPhaseFourierCoefficientSchatten
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (j : ℤ) : SchattenOneOperator CommonRadialPrimeSpace :=
  ∫ z : CommonRadialPhase,
    fourier j z • commonRadialPhaseSourceDensitySchatten a V z ∂unitCircleHaar

/-- Underlying bounded operator of the Schatten-one Fourier coefficient. -/
def commonRadialPhaseFourierCoefficient
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (j : ℤ) : CommonRadialPrimeSpace →L[ℂ] CommonRadialPrimeSpace :=
  (commonRadialPhaseFourierCoefficientSchatten a V j :
    CommonRadialPrimeSpace →L[ℂ] CommonRadialPrimeSpace)

theorem commonRadialPhaseFourierCoefficient_memSchattenClass_one
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (j : ℤ) :
    MemSchattenClass 1 (commonRadialPhaseFourierCoefficient a V j) :=
  (commonRadialPhaseFourierCoefficientSchatten a V j).property

theorem commonRadialPhaseFourierCoefficient_eq_integral
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (j : ℤ) :
    commonRadialPhaseFourierCoefficient a V j =
      ∫ z : CommonRadialPhase,
        fourier j z • commonRadialPhaseSourceDensity a V z ∂unitCircleHaar := by
  rw [commonRadialPhaseFourierCoefficient,
    commonRadialPhaseFourierCoefficientSchatten]
  symm
  exact (schattenOneCoeCLM (H := CommonRadialPrimeSpace)).integral_comp_comm
    (integrable_fourier_smul_commonRadialPhaseSourceDensitySchatten a V j)

def commonRadialSchattenMatrixCoefficientCLM
    (p q : CommonRadialPrimeSpace) :
    SchattenOneOperator CommonRadialPrimeSpace →L[ℂ] ℂ :=
  (innerSL ℂ p) ∘L
    ((ContinuousLinearMap.apply ℂ CommonRadialPrimeSpace) q) ∘L
      schattenOneCoeCLM

theorem inner_commonRadialPhaseFourierCoefficient_eq_integral
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (j : ℤ) (p q : CommonRadialPrimeSpace) :
    inner ℂ p (commonRadialPhaseFourierCoefficient a V j q) =
      ∫ z : CommonRadialPhase, fourier j z *
        inner ℂ p (commonRadialPhaseSourceDensity a V z q)
          ∂unitCircleHaar := by
  let L := commonRadialSchattenMatrixCoefficientCLM p q
  have hcomm := L.integral_comp_comm
    (integrable_fourier_smul_commonRadialPhaseSourceDensitySchatten a V j)
  change (∫ z : CommonRadialPhase,
      L (fourier j z • commonRadialPhaseSourceDensitySchatten a V z)
        ∂unitCircleHaar) =
    L (∫ z : CommonRadialPhase,
      fourier j z • commonRadialPhaseSourceDensitySchatten a V z
        ∂unitCircleHaar) at hcomm
  change L (commonRadialPhaseFourierCoefficientSchatten a V j) = _
  rw [commonRadialPhaseFourierCoefficientSchatten]
  rw [← hcomm]
  apply integral_congr_ae
  filter_upwards [] with z
  simp [L, commonRadialSchattenMatrixCoefficientCLM,
    commonRadialPhaseFourierCoefficient,
    commonRadialPhaseFourierCoefficientSchatten,
    commonRadialPhaseSourceDensitySchatten_coe,
    inner_smul_right]

/-! ## Positive phase multiplication and Hardy Toeplitz lift -/

def commonRadialPhaseDensityBound (a : {d : ℝ // 0 < d}) : ℝ :=
  ‖commonRadialPrimeReachability a‖ ^ 2 *
    routePPrimitiveBaseCauchyCubicTraceBudget

theorem commonRadialPhaseDensityBound_nonneg (a : {d : ℝ // 0 < d}) :
    0 ≤ commonRadialPhaseDensityBound a :=
  mul_nonneg (sq_nonneg _) routePPrimitiveBaseCauchyCubicTraceBudget_pos.le

theorem commonRadialPhaseDensityBound_lt_budget (a : {d : ℝ // 0 < d}) :
    commonRadialPhaseDensityBound a <
      routePPrimitiveBaseCauchyCubicTraceBudget := by
  have hw := norm_commonRadialPrimeReachability_lt_one a
  have hw0 := norm_nonneg (commonRadialPrimeReachability a)
  have hw2 : ‖commonRadialPrimeReachability a‖ ^ 2 < 1 := by nlinarith
  simpa [commonRadialPhaseDensityBound] using
    (mul_lt_mul_of_pos_right hw2
      routePPrimitiveBaseCauchyCubicTraceBudget_pos)

theorem commonRadialPhaseDensityBound_lt_one (a : {d : ℝ // 0 < d}) :
    commonRadialPhaseDensityBound a < 1 :=
  (commonRadialPhaseDensityBound_lt_budget a).trans
    routePPrimitiveBaseCauchyCubicTraceBudget_lt_one

/-- Bounded multiplication by the positive prime covariance density on the circle boundary. -/
def commonRadialPhaseMultiplication
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    CommonRadialPhaseBoundary →L[ℂ] CommonRadialPhaseBoundary :=
  lpBoundedOperatorFamilyCLM
    (aestronglyMeasurable_commonRadialPhaseSourceDensity a V)
    (commonRadialPhaseDensityBound_nonneg a)
    (ae_norm_commonRadialPhaseSourceDensity_le a V)

theorem commonRadialPhaseMultiplication_coeFn
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (f : CommonRadialPhaseBoundary) :
    ((commonRadialPhaseMultiplication a V f : CommonRadialPhaseBoundary) :
        CommonRadialPhase → CommonRadialPrimeSpace) =ᵐ[unitCircleHaar]
      fun z => commonRadialPhaseSourceDensity a V z
        ((f : CommonRadialPhase → CommonRadialPrimeSpace) z) :=
  lpBoundedOperatorFamilyCLM_coeFn
    (aestronglyMeasurable_commonRadialPhaseSourceDensity a V)
    (commonRadialPhaseDensityBound_nonneg a)
    (ae_norm_commonRadialPhaseSourceDensity_le a V) f

theorem norm_commonRadialPhaseMultiplication_le
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    ‖commonRadialPhaseMultiplication a V‖ ≤ commonRadialPhaseDensityBound a :=
  norm_lpBoundedOperatorFamilyCLM_le
    (aestronglyMeasurable_commonRadialPhaseSourceDensity a V)
    (commonRadialPhaseDensityBound_nonneg a)
    (ae_norm_commonRadialPhaseSourceDensity_le a V)

theorem commonRadialPhaseMultiplication_isPositive
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    (commonRadialPhaseMultiplication a V).IsPositive :=
  lpBoundedOperatorFamilyCLM_isPositive
    (aestronglyMeasurable_commonRadialPhaseSourceDensity a V)
    (commonRadialPhaseDensityBound_nonneg a)
    (ae_norm_commonRadialPhaseSourceDensity_le a V)
    (Filter.Eventually.of_forall
      (commonRadialPhaseSourceDensity_isPositive a V))

theorem adjoint_comp_positive_comp_isPositive
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (S : E →L[ℂ] F) {A : F →L[ℂ] F} (hA : A.IsPositive) :
    (ContinuousLinearMap.adjoint S ∘L A ∘L S).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · intro x y
    change inner ℂ (ContinuousLinearMap.adjoint S (A (S x))) y =
      inner ℂ x (ContinuousLinearMap.adjoint S (A (S y)))
    rw [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
    exact hA.inner_left_eq_inner_right _ _
  · intro x
    change 0 ≤ inner ℂ (ContinuousLinearMap.adjoint S (A (S x))) x
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact ((ContinuousLinearMap.isPositive_iff A).mp hA).2 (S x)

/-- Positive operator-valued Toeplitz lift on one-sided prime history. -/
def commonRadialPhaseToeplitzLift
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  ContinuousLinearMap.adjoint commonRadialHardySynthesis ∘L
    commonRadialPhaseMultiplication a V ∘L commonRadialHardySynthesis

theorem commonRadialPhaseToeplitzLift_isPositive
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    (commonRadialPhaseToeplitzLift a V).IsPositive :=
  adjoint_comp_positive_comp_isPositive commonRadialHardySynthesis
    (commonRadialPhaseMultiplication_isPositive a V)

theorem inner_basis_commonRadialPhaseToeplitzLift_basis
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (n m : ℕ) (p q : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (commonRadialPhaseToeplitzLift a V
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (m, q))) =
      inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
        (commonRadialPhaseFourierCoefficient a V
          ((m : ℤ) - (n : ℤ))
          (HilbertSchmidt.lpBasis Nat.Primes q)) := by
  change inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
      (ContinuousLinearMap.adjoint commonRadialHardySynthesis
        (commonRadialPhaseMultiplication a V
          (commonRadialHardySynthesis
            (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (m, q))))) = _
  rw [ContinuousLinearMap.adjoint_inner_right,
    commonRadialHardySynthesis_basis, commonRadialHardySynthesis_basis,
    L2.inner_def,
    inner_commonRadialPhaseFourierCoefficient_eq_integral]
  apply integral_congr_ae
  filter_upwards [
    commonRadialHardyMode_coeFn n p,
    commonRadialHardyMode_coeFn m q,
    commonRadialPhaseMultiplication_coeFn a V
      (commonRadialHardyMode (m, q))] with z hn hm hM
  rw [hn, hM, hm, map_smul, inner_smul_left, inner_smul_right]
  rw [← fourier_neg]
  rw [show (m : ℤ) - (n : ℤ) = -(n : ℤ) + (m : ℤ) by ring,
    fourier_add]
  ring

/-- Cross-grade compression `E_n† R E_m`; diagonal compression is the case `n=m`. -/
def recurrentGradeBlock
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (n m : ℕ) :
    CommonRadialPrimeSpace →L[ℂ] CommonRadialPrimeSpace :=
  ContinuousLinearMap.adjoint (historyGradeEmbeddingCLM n) ∘L R ∘L
    historyGradeEmbeddingCLM m

theorem inner_basis_recurrentGradeBlock_basis
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (n m : ℕ) (p q : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
        (recurrentGradeBlock R n m
          (HilbertSchmidt.lpBasis Nat.Primes q)) =
      inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (R (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (m, q))) := by
  change inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
      (ContinuousLinearMap.adjoint (historyGradeEmbeddingCLM n)
        (R (historyGradeEmbeddingCLM m
          (HilbertSchmidt.lpBasis Nat.Primes q)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right,
    historyGradeEmbedding_basis, historyGradeEmbedding_basis]

/-- Exact operator-valued Toeplitz block law. -/
theorem recurrentGradeBlock_commonRadialPhaseToeplitzLift
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (n m : ℕ) :
    recurrentGradeBlock (commonRadialPhaseToeplitzLift a V) n m =
      commonRadialPhaseFourierCoefficient a V ((m : ℤ) - (n : ℤ)) := by
  apply continuousLinearMap_eq_of_eq_on_hilbertBasis
    (HilbertSchmidt.lpBasis Nat.Primes)
  intro q
  apply (HilbertSchmidt.lpBasis Nat.Primes).repr.injective
  ext p
  rw [(HilbertSchmidt.lpBasis Nat.Primes).repr_apply_apply,
    (HilbertSchmidt.lpBasis Nat.Primes).repr_apply_apply,
    inner_basis_recurrentGradeBlock_basis,
    inner_basis_commonRadialPhaseToeplitzLift_basis]

theorem historyShiftCLM_basis (n : ℕ) (p : Nat.Primes) :
    historyShiftCLM
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p)) =
      HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n + 1, p) := by
  calc
    historyShiftCLM
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p)) =
      (historyShiftCLM ∘L historyGradeEmbeddingCLM n)
        (HilbertSchmidt.lpBasis Nat.Primes p) := by
          rw [ContinuousLinearMap.comp_apply, historyGradeEmbedding_basis]
    _ = historyGradeEmbeddingCLM (n + 1)
        (HilbertSchmidt.lpBasis Nat.Primes p) := by
          rw [historyShift_gradeEmbedding]
    _ = _ := historyGradeEmbedding_basis (n + 1) p

/-- The Toeplitz lift is fixed by unilateral history-shift conjugation. -/
theorem recurrentHistoryConjugate_commonRadialPhaseToeplitzLift
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    recurrentHistoryConjugate (commonRadialPhaseToeplitzLift a V) =
      commonRadialPhaseToeplitzLift a V := by
  apply continuousLinearMap_eq_of_eq_on_hilbertBasis
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)
  rintro ⟨m, q⟩
  apply (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).repr.injective
  ext np
  rcases np with ⟨n, p⟩
  rw [(HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).repr_apply_apply,
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).repr_apply_apply]
  change inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
      (ContinuousLinearMap.adjoint historyShiftCLM
        (commonRadialPhaseToeplitzLift a V
          (historyShiftCLM
            (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (m, q))))) = _
  rw [ContinuousLinearMap.adjoint_inner_right,
    historyShiftCLM_basis, historyShiftCLM_basis,
    inner_basis_commonRadialPhaseToeplitzLift_basis,
    inner_basis_commonRadialPhaseToeplitzLift_basis]
  congr 2
  push_cast
  ring

theorem recurrentGradeCompression_eq_recurrentGradeBlock
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (n : ℕ) :
    recurrentGradeCompression R n = recurrentGradeBlock R n n := rfl

theorem recurrentGradeCompression_commonRadialPhaseToeplitzLift
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (n : ℕ) :
    recurrentGradeCompression (commonRadialPhaseToeplitzLift a V) n =
      commonRadialPhaseFourierCoefficient a V 0 := by
  rw [recurrentGradeCompression_eq_recurrentGradeBlock,
    recurrentGradeBlock_commonRadialPhaseToeplitzLift]
  norm_num

theorem commonRadialPhaseFourierCoefficient_zero_isPositive
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    (commonRadialPhaseFourierCoefficient a V 0).IsPositive := by
  rw [← recurrentGradeCompression_commonRadialPhaseToeplitzLift a V 0]
  exact recurrentGradeCompression_isPositive _
    (commonRadialPhaseToeplitzLift_isPositive a V) 0

theorem norm_commonRadialPhaseFourierCoefficientSchatten_zero_le
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    ‖commonRadialPhaseFourierCoefficientSchatten a V 0‖ ≤
      commonRadialPhaseDensityBound a := by
  rw [commonRadialPhaseFourierCoefficientSchatten]
  have hbound : ∀ᵐ z : CommonRadialPhase ∂unitCircleHaar,
      ‖fourier 0 z • commonRadialPhaseSourceDensitySchatten a V z‖ ≤
        commonRadialPhaseDensityBound a := by
    filter_upwards [ae_norm_commonRadialPhaseSourceDensitySchatten_le a V]
      with z hz
    rw [norm_smul, GaloisForLFunctions.HTGeometry.norm_fourier_eq_one,
      one_mul]
    exact hz
  have h := norm_integral_le_of_norm_le_const hbound
  simpa [commonRadialPhaseDensityBound] using h

theorem re_opTrace_commonRadialPhaseFourierCoefficient_zero_le
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    (ContinuousLinearMap.opTrace
      (commonRadialPhaseFourierCoefficient a V 0)).re ≤
        commonRadialPhaseDensityBound a := by
  rw [← traceNorm_eq_re_opTrace_of_isPositive
    (commonRadialPhaseFourierCoefficient_memSchattenClass_one a V 0)
    (commonRadialPhaseFourierCoefficient_zero_isPositive a V)]
  exact norm_commonRadialPhaseFourierCoefficientSchatten_zero_le a V

/-- Minimal recurrent solution plus positive operator-valued Toeplitz remainder. -/
def commonRadialPhaseHistoryCompletion
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    RecurrentPrimePositiveCompletion a where
  operator := recurrentPrimeMinimalCompletion a.property +
    commonRadialPhaseToeplitzLift a V
  positive := (recurrentPrimeMinimalCompletion_isPositive a.property).add
    (commonRadialPhaseToeplitzLift_isPositive a V)
  displacement := by
    rw [recurrentHistoryConjugate_add,
      recurrentHistoryConjugate_commonRadialPhaseToeplitzLift]
    have hG := recurrentPrimeMinimalCompletion_displacement a.property
    rw [← hG]
    abel

theorem commonRadialPhaseHistoryCompletion_remainder
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    (commonRadialPhaseHistoryCompletion a V).remainder =
      commonRadialPhaseToeplitzLift a V := by
  rw [RecurrentPrimePositiveCompletion.remainder]
  change recurrentPrimeMinimalCompletion a.property +
      commonRadialPhaseToeplitzLift a V -
        recurrentPrimeMinimalCompletion a.property = _
  abel

theorem commonRadialPhaseHistoryCompletion_gradeCompression
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (n : ℕ) :
    recurrentGradeCompression
        (commonRadialPhaseHistoryCompletion a V).remainder n =
      commonRadialPhaseFourierCoefficient a V 0 := by
  rw [commonRadialPhaseHistoryCompletion_remainder,
    recurrentGradeCompression_commonRadialPhaseToeplitzLift]

theorem commonRadialPhaseHistoryCompletion_totalBoundaryExcess
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    recurrentTotalBoundaryExcess a
        (commonRadialPhaseHistoryCompletion a V).operator =
      (ContinuousLinearMap.opTrace
        (commonRadialPhaseFourierCoefficient a V 0)).re := by
  let X := commonRadialPhaseHistoryCompletion a V
  have htrace : MemSchattenClass 1
      (recurrentGradeCompression X.remainder 0) := by
    change MemSchattenClass 1
      (recurrentGradeCompression
        (commonRadialPhaseHistoryCompletion a V).remainder 0)
    rw [commonRadialPhaseHistoryCompletion_gradeCompression]
    exact commonRadialPhaseFourierCoefficient_memSchattenClass_one a V 0
  rw [X.totalBoundaryExcess_eq_re_opTrace htrace]
  change (ContinuousLinearMap.opTrace
      (recurrentGradeCompression
        (commonRadialPhaseHistoryCompletion a V).remainder 0)).re = _
  rw [commonRadialPhaseHistoryCompletion_gradeCompression]

theorem commonRadialPhaseHistoryCompletion_totalBoundaryExcess_le
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    recurrentTotalBoundaryExcess a
        (commonRadialPhaseHistoryCompletion a V).operator ≤
      commonRadialPhaseDensityBound a := by
  rw [commonRadialPhaseHistoryCompletion_totalBoundaryExcess]
  exact re_opTrace_commonRadialPhaseFourierCoefficient_zero_le a V

theorem commonRadialPhaseHistoryCompletion_totalBoundaryExcess_lt_one
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    recurrentTotalBoundaryExcess a
        (commonRadialPhaseHistoryCompletion a V).operator < 1 :=
  (commonRadialPhaseHistoryCompletion_totalBoundaryExcess_le a V).trans_lt
    (commonRadialPhaseDensityBound_lt_one a)

theorem commonRadialPhaseHistoryCompletion_totalBoundaryExcess_lt_budget
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    recurrentTotalBoundaryExcess a
        (commonRadialPhaseHistoryCompletion a V).operator <
      routePPrimitiveBaseCauchyCubicTraceBudget :=
  (commonRadialPhaseHistoryCompletion_totalBoundaryExcess_le a V).trans_lt
    (commonRadialPhaseDensityBound_lt_budget a)

theorem commonRadialPhaseHistoryCompletion_normalizedFiniteCompressionTrace_eq
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (N : RecurrentPositiveCutoff) (F : Finset Nat.Primes) :
    (1 / (N : ℝ)) * recurrentFiniteCompressionTrace
        (commonRadialPhaseHistoryCompletion a V).remainder N F =
      recurrentFiniteBoundaryExcess a
        (commonRadialPhaseHistoryCompletion a V).operator F :=
  (commonRadialPhaseHistoryCompletion a V).normalizedFiniteCompressionTrace_eq N F

theorem commonRadialPhaseHistoryCompletion_finiteCompressionTrace_eq
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (N : ℕ) (F : Finset Nat.Primes) :
    recurrentFiniteCompressionTrace
        (commonRadialPhaseHistoryCompletion a V).remainder N F =
      N * ∑ p ∈ F,
        (inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
          (commonRadialPhaseFourierCoefficient a V 0
            (HilbertSchmidt.lpBasis Nat.Primes p))).re := by
  rw [recurrentFiniteCompressionTrace_eq _
    (commonRadialPhaseHistoryCompletion a V).remainder_fixed]
  simp only [recurrentFinitePrimeMass]
  rw [commonRadialPhaseHistoryCompletion_gradeCompression]

/-! ## Weak Haar phase quotient -/

def commonRadialHistoryGauge (z : CommonRadialPhase) :
    PrimeHodgeHistoryHilbert ≃ₗᵢ[ℂ] PrimeHodgeHistoryHilbert :=
  lpPhaseUnitary
    (fun np : PrimeHodgeHistoryIndex => fourier (np.1 : ℤ) z)
    (fun np => GaloisForLFunctions.HTGeometry.norm_fourier_eq_one np.1 z)

def commonRadialHistoryGaugeCLM (z : CommonRadialPhase) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  (commonRadialHistoryGauge z).toLinearIsometry.toContinuousLinearMap

theorem commonRadialHistoryGaugeCLM_basis
    (z : CommonRadialPhase) (n : ℕ) (p : Nat.Primes) :
    commonRadialHistoryGaugeCLM z
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p)) =
      fourier (n : ℤ) z •
        HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p) := by
  apply lp.ext
  funext i
  change commonRadialHistoryGauge z
      (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p)) i = _
  rw [commonRadialHistoryGauge, lpPhaseUnitary_apply]
  by_cases hi : i = (n, p)
  · subst i
    simp
  · simp [HilbertSchmidt.lpBasis_apply, lp.single_apply, hi]

def commonRadialHistoryGaugeConjugate
    (z : CommonRadialPhase)
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  ContinuousLinearMap.adjoint (commonRadialHistoryGaugeCLM z) ∘L R ∘L
    commonRadialHistoryGaugeCLM z

theorem inner_basis_commonRadialHistoryGaugeConjugate_basis
    (z : CommonRadialPhase)
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (n m : ℕ) (p q : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (commonRadialHistoryGaugeConjugate z R
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (m, q))) =
      fourier ((m : ℤ) - (n : ℤ)) z *
        inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
          (R (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (m, q))) := by
  change inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
      (ContinuousLinearMap.adjoint (commonRadialHistoryGaugeCLM z)
        (R (commonRadialHistoryGaugeCLM z
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (m, q))))) = _
  rw [ContinuousLinearMap.adjoint_inner_right,
    commonRadialHistoryGaugeCLM_basis,
    commonRadialHistoryGaugeCLM_basis, map_smul,
    inner_smul_left, inner_smul_right, ← fourier_neg]
  rw [show (m : ℤ) - (n : ℤ) = -(n : ℤ) + (m : ℤ) by ring,
    fourier_add]
  ring

theorem historyPrimeSlice_historyBasis
    (n m : ℕ) (q : Nat.Primes) :
    historyPrimeSlice
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (m, q)) n =
      if n = m then HilbertSchmidt.lpBasis Nat.Primes q else 0 := by
  ext p
  by_cases hnm : n = m
  · subst n
    by_cases hpq : p = q
    · subst p
      simp [HilbertSchmidt.lpBasis_apply, lp.single_apply]
    · have hpair₁ : (m, q) ≠ (m, p) := fun h =>
        hpq (congrArg Prod.snd h).symm
      have hpair₂ : (m, p) ≠ (m, q) := hpair₁.symm
      simp [historyPrimeSlice_apply, HilbertSchmidt.lpBasis_apply,
        lp.single_apply, hpq, hpair₁, hpair₂]
  · have hpair : (n, p) ≠ (m, q) := fun h => hnm (congrArg Prod.fst h)
    simp [historyPrimeSlice_apply, HilbertSchmidt.lpBasis_apply,
      lp.single_apply, hnm, hpair]

theorem inner_basis_recurrentConstantBlockLift_basis
    (C : CommonRadialPrimeSpace →L[ℂ] CommonRadialPrimeSpace)
    (n m : ℕ) (p q : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (recurrentConstantBlockLift C
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (m, q))) =
      if n = m then
        inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
          (C (HilbertSchmidt.lpBasis Nat.Primes q))
      else 0 := by
  rw [HilbertSchmidt.lpBasis_apply, lp.inner_single_left]
  rw [recurrentConstantBlockLift_apply_coordinate,
    historyPrimeSlice_historyBasis]
  by_cases hnm : n = m
  · subst n
    simp [HilbertSchmidt.lpBasis_apply, lp.inner_single_left]
  · simp [hnm]

theorem recurrentGradeBlock_recurrentConstantBlockLift
    (C : CommonRadialPrimeSpace →L[ℂ] CommonRadialPrimeSpace)
    (n m : ℕ) :
    recurrentGradeBlock (recurrentConstantBlockLift C) n m =
      if n = m then C else 0 := by
  apply continuousLinearMap_eq_of_eq_on_hilbertBasis
    (HilbertSchmidt.lpBasis Nat.Primes)
  intro q
  apply (HilbertSchmidt.lpBasis Nat.Primes).repr.injective
  ext p
  rw [(HilbertSchmidt.lpBasis Nat.Primes).repr_apply_apply,
    (HilbertSchmidt.lpBasis Nat.Primes).repr_apply_apply,
    inner_basis_recurrentGradeBlock_basis,
    inner_basis_recurrentConstantBlockLift_basis]
  by_cases hnm : n = m <;> simp [hnm]

/-- Closed phase observer: diagonal constant-block lift of the zero Fourier mode. -/
def commonRadialPhaseQuotient
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  recurrentConstantBlockLift (commonRadialPhaseFourierCoefficient a V 0)

theorem commonRadialPhaseQuotient_isPositive
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    (commonRadialPhaseQuotient a V).IsPositive :=
  recurrentConstantBlockLift_isPositive
    (commonRadialPhaseFourierCoefficient_zero_isPositive a V)

theorem recurrentHistoryConjugate_commonRadialPhaseQuotient
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    recurrentHistoryConjugate (commonRadialPhaseQuotient a V) =
      commonRadialPhaseQuotient a V :=
  recurrentHistoryConjugate_recurrentConstantBlockLift _

theorem recurrentGradeBlock_commonRadialPhaseQuotient
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (n m : ℕ) :
    recurrentGradeBlock (commonRadialPhaseQuotient a V) n m =
      if n = m then commonRadialPhaseFourierCoefficient a V 0 else 0 := by
  exact recurrentGradeBlock_recurrentConstantBlockLift _ n m

theorem recurrentGradeCompression_commonRadialPhaseQuotient
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (n : ℕ) :
    recurrentGradeCompression (commonRadialPhaseQuotient a V) n =
      commonRadialPhaseFourierCoefficient a V 0 := by
  rw [commonRadialPhaseQuotient,
    recurrentGradeCompression_recurrentConstantBlockLift]

/-- Haar weak average on every history-basis matrix coefficient equals the phase quotient. -/
theorem integral_inner_basis_commonRadialHistoryGaugeConjugate_eq_quotient
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (n m : ℕ) (p q : Nat.Primes) :
    (∫ z : CommonRadialPhase,
      inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (commonRadialHistoryGaugeConjugate z
          (commonRadialPhaseToeplitzLift a V)
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (m, q)))
        ∂unitCircleHaar) =
      inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (commonRadialPhaseQuotient a V
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (m, q))) := by
  simp_rw [inner_basis_commonRadialHistoryGaugeConjugate_basis,
    inner_basis_commonRadialPhaseToeplitzLift_basis]
  rw [integral_mul_const, integral_fourier_unitCircleHaar]
  rw [commonRadialPhaseQuotient,
    inner_basis_recurrentConstantBlockLift_basis]
  by_cases hnm : n = m
  · subst n
    simp
  · have hj : (m : ℤ) - (n : ℤ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hnm))
    simp [hnm, hj]

theorem commonRadialPhaseQuotient_totalBoundaryExcess_eq
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    recurrentHistoryMass (commonRadialPhaseQuotient a V) =
      (ContinuousLinearMap.opTrace
        (commonRadialPhaseFourierCoefficient a V 0)).re := by
  have h := recurrentHistoryMass_eq_re_opTrace
    (commonRadialPhaseQuotient a V)
    (commonRadialPhaseQuotient_isPositive a V)
    (by
      rw [recurrentGradeCompression_commonRadialPhaseQuotient]
      exact commonRadialPhaseFourierCoefficient_memSchattenClass_one a V 0)
  rw [h, recurrentGradeCompression_commonRadialPhaseQuotient]

/-! ## Essential-supremum homotopy control -/

theorem norm_comp_five_le
    {E₀ E₁ E₂ E₃ E₄ E₅ : Type*}
    [NormedAddCommGroup E₀] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
    [NormedAddCommGroup E₄] [NormedAddCommGroup E₅]
    [NormedSpace ℂ E₀] [NormedSpace ℂ E₁] [NormedSpace ℂ E₂]
    [NormedSpace ℂ E₃] [NormedSpace ℂ E₄] [NormedSpace ℂ E₅]
    (A : E₄ →L[ℂ] E₅) (B : E₃ →L[ℂ] E₄)
    (C : E₂ →L[ℂ] E₃) (D : E₁ →L[ℂ] E₂)
    (E : E₀ →L[ℂ] E₁) :
    ‖A ∘L B ∘L C ∘L D ∘L E‖ ≤
      ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ := by
  calc
    ‖A ∘L B ∘L C ∘L D ∘L E‖ ≤ ‖A‖ * ‖B ∘L C ∘L D ∘L E‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖ * (‖B‖ * ‖C ∘L D ∘L E‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖ * (‖B‖ * (‖C‖ * ‖D ∘L E‖)) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖ * (‖B‖ * (‖C‖ * (‖D‖ * ‖E‖))) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ := by ring

theorem norm_commonRadialPrimeSynthesis_eq_reachability
    (a : {d : ℝ // 0 < d}) :
    ‖commonRadialPrimeSynthesis a‖ = ‖commonRadialPrimeReachability a‖ := by
  rw [commonRadialPrimeReachability, norm_adjoint_eq_norm]

theorem commonRadialPhaseSourceDensity_sub_decomposition
    (a : {d : ℝ // 0 < d})
    (V Z : CommonRadialPhaseContractionField) (z : CommonRadialPhase) :
    commonRadialPhaseSourceDensity a V z -
        commonRadialPhaseSourceDensity a Z z =
      commonRadialPrimeReachability a ∘L (V z - Z z) ∘L
          routePPrimitiveBurnolBaseNuclearSource ∘L
            ContinuousLinearMap.adjoint (V z) ∘L commonRadialPrimeSynthesis a +
      commonRadialPrimeReachability a ∘L Z z ∘L
          routePPrimitiveBurnolBaseNuclearSource ∘L
            ContinuousLinearMap.adjoint (V z - Z z) ∘L
              commonRadialPrimeSynthesis a := by
  rw [commonRadialPhaseSourceDensity_eq_sandwich,
    commonRadialPhaseSourceDensity_eq_sandwich]
  rw [show ContinuousLinearMap.adjoint (V z - Z z) =
      ContinuousLinearMap.adjoint (V z) -
        ContinuousLinearMap.adjoint (Z z) by
    exact map_sub ContinuousLinearMap.adjoint (V z) (Z z)]
  ext x
  simp only [_root_.sub_apply, _root_.add_apply,
    ContinuousLinearMap.comp_apply, map_sub]
  abel

theorem ae_norm_commonRadialPhaseSourceDensity_sub_le
    (a : {d : ℝ // 0 < d})
    (V Z : CommonRadialPhaseContractionField) {ε : ℝ} (hε : 0 ≤ ε)
    (hVZ : ∀ᵐ z ∂unitCircleHaar, ‖V z - Z z‖ ≤ ε) :
    ∀ᵐ z ∂unitCircleHaar,
      ‖commonRadialPhaseSourceDensity a V z -
        commonRadialPhaseSourceDensity a Z z‖ ≤
      2 * ‖commonRadialPrimeReachability a‖ ^ 2 *
        ‖routePPrimitiveBurnolBaseNuclearSource‖ * ε := by
  filter_upwards [V.norm_le_one, Z.norm_le_one, hVZ] with z hV hZ hdiff
  rw [commonRadialPhaseSourceDensity_sub_decomposition]
  calc
    ‖commonRadialPrimeReachability a ∘L (V z - Z z) ∘L
          routePPrimitiveBurnolBaseNuclearSource ∘L
            ContinuousLinearMap.adjoint (V z) ∘L commonRadialPrimeSynthesis a +
       commonRadialPrimeReachability a ∘L Z z ∘L
          routePPrimitiveBurnolBaseNuclearSource ∘L
            ContinuousLinearMap.adjoint (V z - Z z) ∘L
              commonRadialPrimeSynthesis a‖ ≤
        ‖commonRadialPrimeReachability a ∘L (V z - Z z) ∘L
          routePPrimitiveBurnolBaseNuclearSource ∘L
            ContinuousLinearMap.adjoint (V z) ∘L commonRadialPrimeSynthesis a‖ +
        ‖commonRadialPrimeReachability a ∘L Z z ∘L
          routePPrimitiveBurnolBaseNuclearSource ∘L
            ContinuousLinearMap.adjoint (V z - Z z) ∘L
              commonRadialPrimeSynthesis a‖ := norm_add_le _ _
    _ ≤ (‖commonRadialPrimeReachability a‖ * ‖V z - Z z‖ *
          ‖routePPrimitiveBurnolBaseNuclearSource‖ *
            ‖ContinuousLinearMap.adjoint (V z)‖ *
              ‖commonRadialPrimeSynthesis a‖) +
        (‖commonRadialPrimeReachability a‖ * ‖Z z‖ *
          ‖routePPrimitiveBurnolBaseNuclearSource‖ *
            ‖ContinuousLinearMap.adjoint (V z - Z z)‖ *
              ‖commonRadialPrimeSynthesis a‖) := by
      exact add_le_add
        (norm_comp_five_le _ _ _ _ _)
        (norm_comp_five_le _ _ _ _ _)
    _ = ‖commonRadialPrimeReachability a‖ ^ 2 *
          ‖routePPrimitiveBurnolBaseNuclearSource‖ *
            (‖V z - Z z‖ * ‖V z‖ + ‖Z z‖ * ‖V z - Z z‖) := by
      rw [norm_adjoint_eq_norm, norm_adjoint_eq_norm,
        norm_commonRadialPrimeSynthesis_eq_reachability]
      ring
    _ ≤ ‖commonRadialPrimeReachability a‖ ^ 2 *
          ‖routePPrimitiveBurnolBaseNuclearSource‖ * (ε * 1 + 1 * ε) := by
      have h₁ : ‖V z - Z z‖ * ‖V z‖ ≤ ε * 1 :=
        mul_le_mul hdiff hV (norm_nonneg _) hε
      have h₂ : ‖Z z‖ * ‖V z - Z z‖ ≤ 1 * ε :=
        mul_le_mul hZ hdiff (norm_nonneg _) zero_le_one
      exact mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity)
    _ = 2 * ‖commonRadialPrimeReachability a‖ ^ 2 *
        ‖routePPrimitiveBurnolBaseNuclearSource‖ * ε := by ring

theorem lpBoundedOperatorFamilyCLM_sub_eq
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {μ : Measure X} {A B : X → H →L[ℂ] H}
    (hA : AEStronglyMeasurable A μ)
    (hB : AEStronglyMeasurable B μ)
    {CA CB D : ℝ} (hCA0 : 0 ≤ CA) (hCB0 : 0 ≤ CB) (hD0 : 0 ≤ D)
    (hCA : ∀ᵐ x ∂μ, ‖A x‖ ≤ CA)
    (hCB : ∀ᵐ x ∂μ, ‖B x‖ ≤ CB)
    (hD : ∀ᵐ x ∂μ, ‖A x - B x‖ ≤ D) :
    lpBoundedOperatorFamilyCLM hA hCA0 hCA -
        lpBoundedOperatorFamilyCLM hB hCB0 hCB =
      lpBoundedOperatorFamilyCLM (hA.sub hB) hD0 hD := by
  ext f
  filter_upwards [
    Lp.coeFn_sub
      (lpBoundedOperatorFamilyCLM hA hCA0 hCA f)
      (lpBoundedOperatorFamilyCLM hB hCB0 hCB f),
    lpBoundedOperatorFamilyCLM_coeFn hA hCA0 hCA f,
    lpBoundedOperatorFamilyCLM_coeFn hB hCB0 hCB f,
    lpBoundedOperatorFamilyCLM_coeFn (hA.sub hB) hD0 hD f] with
      x hsub hAf hBf hABf
  change
    ((((lpBoundedOperatorFamilyCLM hA hCA0 hCA -
        lpBoundedOperatorFamilyCLM hB hCB0 hCB) f : Lp H 2 μ) : X → H) x) =
      (((lpBoundedOperatorFamilyCLM (hA.sub hB) hD0 hD f :
        Lp H 2 μ) : X → H) x)
  rw [_root_.sub_apply, hsub, Pi.sub_apply, hAf, hBf, hABf]
  rfl

theorem norm_lpBoundedOperatorFamilyCLM_sub_le
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {μ : Measure X} {A B : X → H →L[ℂ] H}
    (hA : AEStronglyMeasurable A μ)
    (hB : AEStronglyMeasurable B μ)
    {CA CB D : ℝ} (hCA0 : 0 ≤ CA) (hCB0 : 0 ≤ CB) (hD0 : 0 ≤ D)
    (hCA : ∀ᵐ x ∂μ, ‖A x‖ ≤ CA)
    (hCB : ∀ᵐ x ∂μ, ‖B x‖ ≤ CB)
    (hD : ∀ᵐ x ∂μ, ‖A x - B x‖ ≤ D) :
    ‖lpBoundedOperatorFamilyCLM hA hCA0 hCA -
        lpBoundedOperatorFamilyCLM hB hCB0 hCB‖ ≤ D := by
  rw [lpBoundedOperatorFamilyCLM_sub_eq hA hB hCA0 hCB0 hD0 hCA hCB hD]
  exact norm_lpBoundedOperatorFamilyCLM_le (hA.sub hB) hD0 hD

theorem norm_commonRadialPhaseMultiplication_sub_le
    (a : {d : ℝ // 0 < d})
    (V Z : CommonRadialPhaseContractionField) {ε : ℝ} (hε : 0 ≤ ε)
    (hVZ : ∀ᵐ z ∂unitCircleHaar, ‖V z - Z z‖ ≤ ε) :
    ‖commonRadialPhaseMultiplication a V -
        commonRadialPhaseMultiplication a Z‖ ≤
      2 * ‖commonRadialPrimeReachability a‖ ^ 2 *
        ‖routePPrimitiveBurnolBaseNuclearSource‖ * ε := by
  exact norm_lpBoundedOperatorFamilyCLM_sub_le
    (aestronglyMeasurable_commonRadialPhaseSourceDensity a V)
    (aestronglyMeasurable_commonRadialPhaseSourceDensity a Z)
    (commonRadialPhaseDensityBound_nonneg a)
    (commonRadialPhaseDensityBound_nonneg a)
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (norm_nonneg _)) hε)
    (ae_norm_commonRadialPhaseSourceDensity_le a V)
    (ae_norm_commonRadialPhaseSourceDensity_le a Z)
    (ae_norm_commonRadialPhaseSourceDensity_sub_le a V Z hε hVZ)

theorem norm_commonRadialHardySynthesis_le_one :
    ‖commonRadialHardySynthesis‖ ≤ 1 := by
  apply commonRadialHardySynthesis.opNorm_le_bound zero_le_one
  intro x
  rw [norm_commonRadialHardySynthesis, one_mul]

theorem commonRadialPhaseToeplitzLift_sub_decomposition
    (a : {d : ℝ // 0 < d})
    (V Z : CommonRadialPhaseContractionField) :
    commonRadialPhaseToeplitzLift a V -
        commonRadialPhaseToeplitzLift a Z =
      ContinuousLinearMap.adjoint commonRadialHardySynthesis ∘L
        (commonRadialPhaseMultiplication a V -
          commonRadialPhaseMultiplication a Z) ∘L
            commonRadialHardySynthesis := by
  ext x
  simp [commonRadialPhaseToeplitzLift]

theorem norm_commonRadialPhaseToeplitzLift_sub_le
    (a : {d : ℝ // 0 < d})
    (V Z : CommonRadialPhaseContractionField) {ε : ℝ} (hε : 0 ≤ ε)
    (hVZ : ∀ᵐ z ∂unitCircleHaar, ‖V z - Z z‖ ≤ ε) :
    ‖commonRadialPhaseToeplitzLift a V -
        commonRadialPhaseToeplitzLift a Z‖ ≤
      2 * ‖commonRadialPrimeReachability a‖ ^ 2 *
        ‖routePPrimitiveBurnolBaseNuclearSource‖ * ε := by
  rw [commonRadialPhaseToeplitzLift_sub_decomposition]
  calc
    ‖ContinuousLinearMap.adjoint commonRadialHardySynthesis ∘L
        (commonRadialPhaseMultiplication a V -
          commonRadialPhaseMultiplication a Z) ∘L
            commonRadialHardySynthesis‖ ≤
      ‖ContinuousLinearMap.adjoint commonRadialHardySynthesis‖ *
        ‖commonRadialPhaseMultiplication a V -
          commonRadialPhaseMultiplication a Z‖ *
            ‖commonRadialHardySynthesis‖ := by
      calc
        _ ≤ ‖ContinuousLinearMap.adjoint commonRadialHardySynthesis ∘L
              (commonRadialPhaseMultiplication a V -
                commonRadialPhaseMultiplication a Z)‖ *
              ‖commonRadialHardySynthesis‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖ContinuousLinearMap.adjoint commonRadialHardySynthesis‖ *
              ‖commonRadialPhaseMultiplication a V -
                commonRadialPhaseMultiplication a Z‖) *
              ‖commonRadialHardySynthesis‖ := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 *
        (2 * ‖commonRadialPrimeReachability a‖ ^ 2 *
          ‖routePPrimitiveBurnolBaseNuclearSource‖ * ε) * 1 := by
      rw [norm_adjoint_eq_norm]
      gcongr
      · exact norm_commonRadialHardySynthesis_le_one
      · exact norm_commonRadialPhaseMultiplication_sub_le a V Z hε hVZ
      · exact norm_commonRadialHardySynthesis_le_one
    _ = _ := by ring

theorem commonRadialPhaseHistoryCompletion_operator_sub
    (a : {d : ℝ // 0 < d})
    (V Z : CommonRadialPhaseContractionField) :
    (commonRadialPhaseHistoryCompletion a V).operator -
        (commonRadialPhaseHistoryCompletion a Z).operator =
      commonRadialPhaseToeplitzLift a V -
        commonRadialPhaseToeplitzLift a Z := by
  change (recurrentPrimeMinimalCompletion a.property +
      commonRadialPhaseToeplitzLift a V) -
    (recurrentPrimeMinimalCompletion a.property +
      commonRadialPhaseToeplitzLift a Z) = _
  abel

theorem norm_commonRadialPhaseHistoryCompletion_operator_sub_le
    (a : {d : ℝ // 0 < d})
    (V Z : CommonRadialPhaseContractionField) {ε : ℝ} (hε : 0 ≤ ε)
    (hVZ : ∀ᵐ z ∂unitCircleHaar, ‖V z - Z z‖ ≤ ε) :
    ‖(commonRadialPhaseHistoryCompletion a V).operator -
        (commonRadialPhaseHistoryCompletion a Z).operator‖ ≤
      2 * ‖commonRadialPrimeReachability a‖ ^ 2 *
        ‖routePPrimitiveBurnolBaseNuclearSource‖ * ε := by
  rw [commonRadialPhaseHistoryCompletion_operator_sub]
  exact norm_commonRadialPhaseToeplitzLift_sub_le a V Z hε hVZ

/-- A contraction-field path continuous in the essential-supremum operator norm. -/
structure CommonRadialPhaseContractionHomotopy where
  toFun : ℝ → CommonRadialPhaseContractionField
  continuous_essSup : ∀ s : ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - s| < δ →
      ∀ᵐ z ∂unitCircleHaar, ‖toFun t z - toFun s z‖ ≤ ε

instance : CoeFun CommonRadialPhaseContractionHomotopy
    (fun _ => ℝ → CommonRadialPhaseContractionField) :=
  ⟨CommonRadialPhaseContractionHomotopy.toFun⟩

/-- Explicit epsilon-delta formulation of norm continuity for operator-valued paths. -/
def OperatorNormContinuousPath
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : ℝ → E →L[ℂ] F) : Prop :=
  ∀ s : ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - s| < δ → ‖T t - T s‖ < ε

/-- An `L∞`-continuous contraction-field homotopy gives an operator-norm continuous family of
recurrent positive completions, with the paper's explicit Lipschitz constant. -/
theorem operatorNormContinuous_commonRadialPhaseHistoryCompletion
    (a : {d : ℝ // 0 < d})
    (P : CommonRadialPhaseContractionHomotopy) :
    OperatorNormContinuousPath
      (fun s => (commonRadialPhaseHistoryCompletion a (P s)).operator) := by
  intro s ε hε
  let C : ℝ := 2 * ‖commonRadialPrimeReachability a‖ ^ 2 *
    ‖routePPrimitiveBurnolBaseNuclearSource‖
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hC1 : 0 < C + 1 := by linarith
  have hη : 0 < ε / (C + 1) := div_pos hε hC1
  obtain ⟨δ, hδ, hpath⟩ := P.continuous_essSup s (ε / (C + 1)) hη
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have hbound := norm_commonRadialPhaseHistoryCompletion_operator_sub_le
    a (P t) (P s) hη.le (hpath t ht)
  have hratio : C / (C + 1) < 1 := by
    exact (div_lt_one hC1).2 (by linarith)
  have hstrict : C * (ε / (C + 1)) < ε := by
    calc
      C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := mul_one ε
  exact hbound.trans_lt (by simpa [C] using hstrict)

/-- Full homotopy package: exact displacement, uniform density budget, and norm continuity. -/
theorem commonRadialPhaseHistoryCompletion_homotopy
    (a : {d : ℝ // 0 < d})
    (P : CommonRadialPhaseContractionHomotopy) :
    (∀ s : ℝ,
      (commonRadialPhaseHistoryCompletion a (P s)).operator -
          recurrentHistoryConjugate
            (commonRadialPhaseHistoryCompletion a (P s)).operator =
        primeHodgeHistoryDefectOperator a.property) ∧
    (∀ s : ℝ,
      recurrentTotalBoundaryExcess a
          (commonRadialPhaseHistoryCompletion a (P s)).operator <
        routePPrimitiveBaseCauchyCubicTraceBudget) ∧
    OperatorNormContinuousPath
      (fun s => (commonRadialPhaseHistoryCompletion a (P s)).operator) := by
  refine ⟨?_, ?_, operatorNormContinuous_commonRadialPhaseHistoryCompletion a P⟩
  · intro s
    exact (commonRadialPhaseHistoryCompletion a (P s)).displacement
  · intro s
    exact commonRadialPhaseHistoryCompletion_totalBoundaryExcess_lt_budget a (P s)

/-! ## Constant-field recovery -/

/-- Constant contraction field associated to one admissible common-radial contraction. -/
def commonRadialConstantPhaseField (V : CommonRadialContraction) :
    CommonRadialPhaseContractionField where
  toFun := fun _ => V.1
  aestronglyMeasurable_toFun :=
    Continuous.aestronglyMeasurable continuous_const
  norm_le_one := Filter.Eventually.of_forall fun _ => V.2

theorem commonRadialConstantPhaseField_apply
    (V : CommonRadialContraction) (z : CommonRadialPhase) :
    commonRadialConstantPhaseField V z = V.1 := rfl

/-- A constant phase field recovers the original common-radial contracted covariance exactly. -/
theorem commonRadialPhaseSourceDensity_constant
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction)
    (z : CommonRadialPhase) :
    commonRadialPhaseSourceDensity a (commonRadialConstantPhaseField V) z =
      commonRadialPrimeContractedSymbol a V := by
  rw [commonRadialPhaseSourceDensity_eq_sandwich,
    commonRadialPrimeContractedSymbol_eq_sandwich]
  rfl

/-- All Fourier blocks of a constant field vanish off frequency zero. -/
theorem commonRadialPhaseFourierCoefficient_constant
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) (j : ℤ) :
    commonRadialPhaseFourierCoefficient a (commonRadialConstantPhaseField V) j =
      if j = 0 then commonRadialPrimeContractedSymbol a V else 0 := by
  apply continuousLinearMap_eq_of_eq_on_hilbertBasis
    (HilbertSchmidt.lpBasis Nat.Primes)
  intro q
  apply (HilbertSchmidt.lpBasis Nat.Primes).repr.injective
  ext p
  rw [(HilbertSchmidt.lpBasis Nat.Primes).repr_apply_apply,
    (HilbertSchmidt.lpBasis Nat.Primes).repr_apply_apply,
    inner_commonRadialPhaseFourierCoefficient_eq_integral]
  simp_rw [commonRadialPhaseSourceDensity_constant]
  rw [integral_mul_const, integral_fourier_unitCircleHaar]
  by_cases hj : j = 0
  · simp [hj]
  · simp [hj]

/-- The phase Toeplitz construction specializes exactly to the earlier constant-block lift. -/
theorem commonRadialPhaseToeplitzLift_constant
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    commonRadialPhaseToeplitzLift a (commonRadialConstantPhaseField V) =
      recurrentConstantBlockLift (commonRadialPrimeContractedSymbol a V) := by
  apply continuousLinearMap_eq_of_eq_on_hilbertBasis
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)
  rintro ⟨m, q⟩
  apply (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).repr.injective
  ext ⟨n, p⟩
  rw [(HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).repr_apply_apply,
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).repr_apply_apply,
    inner_basis_commonRadialPhaseToeplitzLift_basis,
    commonRadialPhaseFourierCoefficient_constant,
    inner_basis_recurrentConstantBlockLift_basis]
  by_cases hnm : n = m
  · subst n
    simp
  · have hj : (m : ℤ) - (n : ℤ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hnm))
    simp [hnm, hj]

/-- Constant-field phase quotient is the original stationary constant-block history operator. -/
theorem commonRadialPhaseQuotient_constant
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    commonRadialPhaseQuotient a (commonRadialConstantPhaseField V) =
      recurrentConstantBlockLift (commonRadialPrimeContractedSymbol a V) := by
  rw [commonRadialPhaseQuotient,
    commonRadialPhaseFourierCoefficient_constant]
  simp

/-- The open Toeplitz history and its closed phase quotient carry exactly the same recurrent
grade-zero trace mass. -/
theorem commonRadialPhaseToeplitzLift_recurrentHistoryMass_eq
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    recurrentHistoryMass (commonRadialPhaseToeplitzLift a V) =
      (ContinuousLinearMap.opTrace
        (commonRadialPhaseFourierCoefficient a V 0)).re := by
  have h := recurrentHistoryMass_eq_re_opTrace
    (commonRadialPhaseToeplitzLift a V)
    (commonRadialPhaseToeplitzLift_isPositive a V)
    (by
      rw [recurrentGradeCompression_commonRadialPhaseToeplitzLift]
      exact commonRadialPhaseFourierCoefficient_memSchattenClass_one a V 0)
  rw [h, recurrentGradeCompression_commonRadialPhaseToeplitzLift]

theorem commonRadialPhaseToeplitzLift_recurrentHistoryMass_eq_quotient
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField) :
    recurrentHistoryMass (commonRadialPhaseToeplitzLift a V) =
      recurrentHistoryMass (commonRadialPhaseQuotient a V) := by
  rw [commonRadialPhaseToeplitzLift_recurrentHistoryMass_eq,
    commonRadialPhaseQuotient_totalBoundaryExcess_eq]

end

end RHTower
