import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleCharFun
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ModeExpectation
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.Response
import GaloisForLFunctions.HTGeometry.ConstitutiveGlobalFormationInformationProperness

/-!
# Parity mass of the abelian zeta gas

The total number of cyclic factors defines a native parity character on finite abelian group
classes.  Finite mode heads factor under the product gas.  Finite-support concentration then lets
the heads converge to the literal class parity, while the product limit is the quotient of the
doubled and original zero-occupation normalizers.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Total number of cyclic factors in a finite abelian group class. -/
def AbelianZetaGroupClass.cyclicFactorCount (A : AbelianZetaGroupClass) : ℕ :=
  A.sum fun _ n => n

/-- Native parity character `(-1)^Ω` of a finite abelian group class. -/
def AbelianZetaGroupClass.parity (A : AbelianZetaGroupClass) : ℂ :=
  (-1 : ℂ) ^ A.cyclicFactorCount

@[simp] theorem AbelianZetaGroupClass.norm_parity (A : AbelianZetaGroupClass) :
    ‖A.parity‖ = 1 := by
  simp [AbelianZetaGroupClass.parity]

/-- A fixed injective code used only to exhaust the countable prime-depth mode set. -/
private noncomputable def abelianZetaModeCode : AbelianZetaMode → ℕ :=
  Classical.choose (Countable.exists_injective_nat AbelianZetaMode)

private theorem abelianZetaModeCode_injective : Function.Injective abelianZetaModeCode :=
  Classical.choose_spec (Countable.exists_injective_nat AbelianZetaMode)

/-- Finite head containing exactly the modes whose code is below `N`. -/
private noncomputable def abelianZetaModeHead (N : ℕ) : Finset AbelianZetaMode :=
  (Finset.range N).preimage abelianZetaModeCode abelianZetaModeCode_injective.injOn

private theorem mem_abelianZetaModeHead_iff (N : ℕ) (m : AbelianZetaMode) :
    m ∈ abelianZetaModeHead N ↔ abelianZetaModeCode m < N := by
  rw [abelianZetaModeHead, Finset.mem_preimage]
  exact Finset.mem_range

private theorem tendsto_abelianZetaModeHead_atTop :
    Tendsto abelianZetaModeHead atTop atTop := by
  rw [tendsto_atTop]
  intro s
  let codes : Finset ℕ := s.image abelianZetaModeCode
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range codes
  filter_upwards [eventually_ge_atTop N] with M hM
  intro m hm
  rw [mem_abelianZetaModeHead_iff]
  have hcode : abelianZetaModeCode m ∈ codes := Finset.mem_image.mpr ⟨m, hm, rfl⟩
  exact lt_of_lt_of_le (Finset.mem_range.mp (hN hcode)) hM

/-- Parity phase on a finite mode head. -/
private def finiteModeParity (s : Finset AbelianZetaMode)
    (k : AbelianZetaMode → ℕ) : ℂ :=
  Complex.exp ((((∑ m ∈ s, Real.pi * k m : ℝ)) : ℂ) * Complex.I)

private theorem finiteModeParity_eq_negOnePow (s : Finset AbelianZetaMode)
    (k : AbelianZetaMode → ℕ) :
    finiteModeParity s k = (-1 : ℂ) ^ (∑ m ∈ s, k m) := by
  rw [finiteModeParity]
  have harg : (((∑ m ∈ s, Real.pi * k m : ℝ)) : ℂ) * Complex.I =
      ((∑ m ∈ s, k m : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [harg, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

private theorem finiteModeParity_eventually_eq_classParity
    (k : AbelianZetaMode → ℕ) (hk : (Function.support k).Finite) :
    ∀ᶠ N in atTop, finiteModeParity (abelianZetaModeHead N) k = (classOf k).parity := by
  let S : Finset AbelianZetaMode := hk.toFinset
  let codes : Finset ℕ := S.image abelianZetaModeCode
  obtain ⟨N₀, hN₀⟩ := Finset.exists_nat_subset_range codes
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hsupp : (classOf k).support ⊆ abelianZetaModeHead N := by
    intro m hm
    have hkm : k m ≠ 0 := by
      have hclass := congrFun (classOf_of_finite hk) m
      simpa [hclass] using hm
    rw [mem_abelianZetaModeHead_iff]
    have hmS : m ∈ S := Set.Finite.mem_toFinset hk |>.mpr hkm
    have hcode : abelianZetaModeCode m ∈ codes := Finset.mem_image.mpr ⟨m, hmS, rfl⟩
    exact lt_of_lt_of_le (Finset.mem_range.mp (hN₀ hcode)) hN
  rw [finiteModeParity_eq_negOnePow, AbelianZetaGroupClass.parity,
    AbelianZetaGroupClass.cyclicFactorCount]
  congr 1
  rw [Finsupp.sum_of_support_subset _ hsupp]
  · apply Finset.sum_congr rfl
    intro m hm
    exact (congrFun (classOf_of_finite hk) m).symm
  · simp

private theorem tendsto_integral_finiteModeParity
    (θ : AbelianZetaConvergentParameters) :
    Tendsto (fun N => ∫ k, finiteModeParity (abelianZetaModeHead N) k
        ∂θ.toAbelianZetaParameters.gasMeasure) atTop
      (𝓝 (∫ k, (classOf k).parity ∂θ.toAbelianZetaParameters.gasMeasure)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro N
    exact (by unfold finiteModeParity; fun_prop :
      Measurable (finiteModeParity (abelianZetaModeHead N))).aestronglyMeasurable
  · exact integrable_const 1
  · intro N
    filter_upwards [] with k
    rw [finiteModeParity, Complex.norm_exp]
    simp
  · filter_upwards [ae_finiteSupport θ] with k hk
    exact tendsto_const_nhds.congr'
      (Filter.EventuallyEq.symm (finiteModeParity_eventually_eq_classParity k hk))

private theorem integral_classLaw_parity_eq_gasMeasure
    (θ : AbelianZetaConvergentParameters) :
    (∫ A, A.parity ∂classLaw θ.toAbelianZetaParameters) =
      ∫ k, (classOf k).parity ∂θ.toAbelianZetaParameters.gasMeasure := by
  rw [classLaw_eq_map θ]
  exact integral_map measurable_classOf.aemeasurable
    (measurable_from_top.aestronglyMeasurable)

/-- Doubling a temperature parameter while remaining in the Euler chamber. -/
def EulerSigma.double (σ : EulerSigma) : EulerSigma where
  val := 2 * σ.val
  one_lt := by linarith [σ.one_lt]

@[simp] theorem EulerSigma.double_val (σ : EulerSigma) : σ.double.val = 2 * σ.val := rfl

/-- Simultaneous doubling of the order and socle exponents. -/
def AbelianZetaConvergentParameters.double (θ : AbelianZetaConvergentParameters) :
    AbelianZetaConvergentParameters where
  toAbelianZetaParameters :=
    { sigma := 2 * θ.sigma
      tau := 2 * θ.tau
      sigma_pos := by linarith [θ.sigma_pos]
      tau_nonneg := by linarith [θ.tau_nonneg] }
  firstDepth := by linarith [θ.firstDepth]

@[simp] theorem AbelianZetaConvergentParameters.double_sigma
    (θ : AbelianZetaConvergentParameters) : θ.double.sigma = 2 * θ.sigma := rfl

@[simp] theorem AbelianZetaConvergentParameters.double_tau
    (θ : AbelianZetaConvergentParameters) : θ.double.tau = 2 * θ.tau := rfl

private theorem ratio_parameters_double
    (θ : AbelianZetaConvergentParameters) (m : AbelianZetaMode) :
    θ.double.toAbelianZetaParameters.ratio m =
      (θ.toAbelianZetaParameters.ratio m) ^ 2 := by
  have hp : (0 : ℝ) < ((m.1 : ℕ) : ℝ) := by exact_mod_cast m.1.prop.pos
  rw [AbelianZetaParameters.ratio, AbelianZetaParameters.ratio,
    AbelianZetaParameters.exponent, AbelianZetaParameters.exponent]
  simp only [AbelianZetaConvergentParameters.double_sigma,
    AbelianZetaConvergentParameters.double_tau]
  rw [← Real.rpow_natCast
    (((m.1 : ℕ) : ℝ) ^
      (-(↑(AbelianZetaMode.depth m) * θ.sigma + θ.tau))) 2,
    ← Real.rpow_mul hp.le]
  congr 1
  push_cast
  ring

private def parityModeFactor
    (θ : AbelianZetaConvergentParameters) (m : AbelianZetaMode) : ℂ :=
  (1 - (θ.toAbelianZetaParameters.ratio m : ℂ)) /
    (1 + (θ.toAbelianZetaParameters.ratio m : ℂ))

private theorem parityModeFactor_eq_square_div_double
    (θ : AbelianZetaConvergentParameters) (m : AbelianZetaMode) :
    parityModeFactor θ m =
      (1 - (θ.toAbelianZetaParameters.ratio m : ℂ)) ^ 2 /
        (1 - (θ.double.toAbelianZetaParameters.ratio m : ℂ)) := by
  rw [parityModeFactor, ratio_parameters_double]
  push_cast
  have hq : (θ.toAbelianZetaParameters.ratio m : ℂ) ≠ 1 := by
    exact_mod_cast ne_of_lt (θ.toAbelianZetaParameters.ratio_lt_one m)
  have hsub :
      1 - (θ.toAbelianZetaParameters.ratio m : ℂ) ≠ 0 :=
    sub_ne_zero.mpr hq.symm
  have hadd :
      1 + (θ.toAbelianZetaParameters.ratio m : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (add_pos zero_lt_one (θ.toAbelianZetaParameters.ratio_pos m))
  have hsq :
      1 - (θ.toAbelianZetaParameters.ratio m : ℂ) ^ 2 ≠ 0 := by
    rw [show 1 - (θ.toAbelianZetaParameters.ratio m : ℂ) ^ 2 =
      (1 - (θ.toAbelianZetaParameters.ratio m : ℂ)) *
        (1 + (θ.toAbelianZetaParameters.ratio m : ℂ)) by ring]
    exact mul_ne_zero hsub hadd
  field_simp [hadd, hsq]
  ring

private theorem hasProd_parityModeFactor (θ : AbelianZetaConvergentParameters) :
    HasProd (parityModeFactor θ)
      (θ.complexNormalizer ^ 2 / θ.double.complexNormalizer) := by
  have hmσ : Multipliable (fun m : AbelianZetaMode =>
      1 - (θ.toAbelianZetaParameters.ratio m : ℂ)) := by
    simpa only [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable
      (((Complex.summable_ofReal).2 θ.summable_ratio).neg)
  have hσ : HasProd (fun m : AbelianZetaMode =>
      1 - (θ.toAbelianZetaParameters.ratio m : ℂ)) θ.complexNormalizer := by
    simpa only [AbelianZetaConvergentParameters.complexNormalizer] using hmσ.hasProd
  have hm2 : Multipliable (fun m : AbelianZetaMode =>
      1 - (θ.double.toAbelianZetaParameters.ratio m : ℂ)) := by
    simpa only [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable
      (((Complex.summable_ofReal).2 θ.double.summable_ratio).neg)
  have h2 : HasProd (fun m : AbelianZetaMode =>
      1 - (θ.double.toAbelianZetaParameters.ratio m : ℂ)) θ.double.complexNormalizer := by
    simpa only [AbelianZetaConvergentParameters.complexNormalizer] using hm2.hasProd
  have hnum := hσ.pow 2
  rw [HasProd] at hnum h2 ⊢
  have hquot := hnum.div h2 θ.double.complexNormalizer_ne_zero
  apply hquot.congr'
  filter_upwards [] with s
  change (∏ b ∈ s,
      (1 - (θ.toAbelianZetaParameters.ratio b : ℂ)) ^ 2) /
      (∏ b ∈ s,
        (1 - (θ.double.toAbelianZetaParameters.ratio b : ℂ))) =
        ∏ b ∈ s, parityModeFactor θ b
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro m hm
  exact (parityModeFactor_eq_square_div_double θ m).symm

private theorem integral_finiteModeParity_eq_prod
    (θ : AbelianZetaConvergentParameters) (N : ℕ) :
    (∫ k, finiteModeParity (abelianZetaModeHead N) k
        ∂θ.toAbelianZetaParameters.gasMeasure) =
      ∏ m ∈ abelianZetaModeHead N, parityModeFactor θ m := by
  change (∫ k, Complex.exp (((∑ m ∈ abelianZetaModeHead N,
      Real.pi * k m : ℝ) : ℂ) * Complex.I)
      ∂θ.toAbelianZetaParameters.gasMeasure) = _
  rw [AbelianZetaParameters.integral_gasMeasure_expo_finset]
  apply Finset.prod_congr rfl
  intro m hm
  rw [parityModeFactor, Complex.exp_pi_mul_I]
  ring

/-- General parity mass law on the full two-observable convergence chamber. -/
theorem integral_classLaw_parity_general (θ : AbelianZetaConvergentParameters) :
    (∫ A, A.parity ∂classLaw θ.toAbelianZetaParameters) =
      θ.double.zetaPartition / θ.zetaPartition ^ 2 := by
  have hint := tendsto_integral_finiteModeParity θ
  have hprod := (hasProd_parityModeFactor θ).comp tendsto_abelianZetaModeHead_atTop
  have hsame : Tendsto (fun N => ∫ k, finiteModeParity (abelianZetaModeHead N) k
      ∂θ.toAbelianZetaParameters.gasMeasure) atTop
      (𝓝 (θ.complexNormalizer ^ 2 / θ.double.complexNormalizer)) := by
    rw [show (fun N => ∫ k, finiteModeParity (abelianZetaModeHead N) k
        ∂θ.toAbelianZetaParameters.gasMeasure) =
      fun N => ∏ m ∈ abelianZetaModeHead N, parityModeFactor θ m from
        funext (integral_finiteModeParity_eq_prod θ)]
    exact hprod
  have heq := tendsto_nhds_unique hint hsame
  rw [← integral_classLaw_parity_eq_gasMeasure] at heq
  rw [θ.complexNormalizer_eq_zetaPartition_inv,
    θ.double.complexNormalizer_eq_zetaPartition_inv] at heq
  have hz := θ.complexNormalizer_ne_zero
  have hz2 := θ.double.complexNormalizer_ne_zero
  field_simp at heq ⊢
  exact heq

private theorem nnNormalizer_ne_zero
    (θ : AbelianZetaConvergentParameters) : θ.nnNormalizer ≠ 0 := by
  intro h
  apply θ.complexNormalizer_ne_zero
  rw [← θ.coe_nnNormalizer_eq_complexNormalizer, h]
  simp

private def realParityModeFactor
    (θ : AbelianZetaConvergentParameters) (m : AbelianZetaMode) : ℝ :=
  (1 - θ.toAbelianZetaParameters.ratio m) /
    (1 + θ.toAbelianZetaParameters.ratio m)

private theorem realParityModeFactor_pos
    (θ : AbelianZetaConvergentParameters) (m : AbelianZetaMode) :
    0 < realParityModeFactor θ m := by
  rw [realParityModeFactor]
  exact div_pos (sub_pos.mpr (θ.toAbelianZetaParameters.ratio_lt_one m))
    (add_pos zero_lt_one (θ.toAbelianZetaParameters.ratio_pos m))

private theorem realParityModeFactor_lt_one
    (θ : AbelianZetaConvergentParameters) (m : AbelianZetaMode) :
    realParityModeFactor θ m < 1 := by
  rw [realParityModeFactor]
  have hden : 0 < 1 + θ.toAbelianZetaParameters.ratio m := by
    linarith [θ.toAbelianZetaParameters.ratio_pos m]
  rw [div_lt_one hden]
  linarith [θ.toAbelianZetaParameters.ratio_pos m]

private theorem summable_realParityModeFactor_sub_one
    (θ : AbelianZetaConvergentParameters) :
    Summable fun m : AbelianZetaMode => realParityModeFactor θ m - 1 := by
  have hmaj : Summable fun m : AbelianZetaMode =>
      2 * θ.toAbelianZetaParameters.ratio m := θ.summable_ratio.mul_left 2
  refine Summable.of_norm_bounded hmaj fun m => ?_
  rw [realParityModeFactor]
  have hq0 := θ.toAbelianZetaParameters.ratio_nonneg m
  have hden : 0 < 1 + θ.toAbelianZetaParameters.ratio m := by linarith
  rw [show (1 - θ.toAbelianZetaParameters.ratio m) /
      (1 + θ.toAbelianZetaParameters.ratio m) - 1 =
      -(2 * θ.toAbelianZetaParameters.ratio m /
        (1 + θ.toAbelianZetaParameters.ratio m)) by
      field_simp
      ring]
  rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (div_nonneg (by positivity) hden.le)]
  rw [div_le_iff₀ hden]
  nlinarith

private theorem hasProd_realParityModeFactor
    (θ : AbelianZetaConvergentParameters) :
    HasProd (realParityModeFactor θ)
      (((θ.nnNormalizer : ℝ) ^ 2) / (θ.double.nnNormalizer : ℝ)) := by
  have hm : Multipliable (realParityModeFactor θ) := by
    have hs := summable_realParityModeFactor_sub_one θ
    convert Real.multipliable_one_add_of_summable hs using 1
    funext m
    ring
  let r : ℝ := ∏' m : AbelianZetaMode, realParityModeFactor θ m
  have hr : HasProd (realParityModeFactor θ) r := by
    simpa only [r] using hm.hasProd
  have hc := hr.map Complex.ofRealHom Complex.continuous_ofReal
  have hc' : HasProd (parityModeFactor θ) (r : ℂ) := by
    convert hc using 1
    · funext m
      unfold parityModeFactor realParityModeFactor
      simp only [Function.comp_apply]
      change (1 - (θ.toAbelianZetaParameters.ratio m : ℂ)) /
          (1 + (θ.toAbelianZetaParameters.ratio m : ℂ)) =
        ((((1 - θ.toAbelianZetaParameters.ratio m) /
          (1 + θ.toAbelianZetaParameters.ratio m) : ℝ)) : ℂ)
      push_cast
      rfl
    · rfl
  have heq := hc'.unique (hasProd_parityModeFactor θ)
  rw [← θ.coe_nnNormalizer_eq_complexNormalizer,
    ← θ.double.coe_nnNormalizer_eq_complexNormalizer] at heq
  have heqReal : r = (θ.nnNormalizer : ℝ) ^ 2 / (θ.double.nnNormalizer : ℝ) := by
    exact_mod_cast heq
  simpa only [heqReal] using hr

private theorem integral_classLaw_parity_general_eq_realProduct
    (θ : AbelianZetaConvergentParameters) :
    (∫ A, A.parity ∂classLaw θ.toAbelianZetaParameters) =
      ((((θ.nnNormalizer : ℝ) ^ 2) / (θ.double.nnNormalizer : ℝ) : ℝ) : ℂ) := by
  rw [integral_classLaw_parity_general,
    θ.zetaPartition_eq_complexNormalizer_inv,
    θ.double.zetaPartition_eq_complexNormalizer_inv,
    ← θ.coe_nnNormalizer_eq_complexNormalizer,
    ← θ.double.coe_nnNormalizer_eq_complexNormalizer]
  have hθ : (θ.nnNormalizer : ℂ) ≠ 0 := by
    exact_mod_cast nnNormalizer_ne_zero θ
  have hθ2 : (θ.double.nnNormalizer : ℂ) ≠ 0 := by
    exact_mod_cast nnNormalizer_ne_zero θ.double
  push_cast
  field_simp

/-- Strict range clause in `(GAS4.1)`: parity expectation lies in `(0,1)`. -/
theorem integral_classLaw_parity_re_mem_Ioo (σ : EulerSigma) :
    (∫ A, A.parity ∂classLaw (temperatureConv σ).toAbelianZetaParameters).re ∈
      Set.Ioo (0 : ℝ) 1 := by
  let θ := temperatureConv σ
  let r : ℝ := ((θ.nnNormalizer : ℝ) ^ 2) / (θ.double.nnNormalizer : ℝ)
  have hrprod : HasProd (realParityModeFactor θ) r := by
    simpa only [r] using hasProd_realParityModeFactor θ
  have hrpos : 0 < r := by
    have hn : 0 < (θ.nnNormalizer : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr (nnNormalizer_ne_zero θ))
    have hn2 : 0 < (θ.double.nnNormalizer : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr (nnNormalizer_ne_zero θ.double))
    dsimp only [r]
    positivity
  let m₀ : AbelianZetaMode := AbelianZetaParameters.modeEquivNat 0
  have hrle : r ≤ realParityModeFactor θ m₀ := by
    rw [HasProd] at hrprod
    apply le_of_tendsto hrprod
    filter_upwards [eventually_ge_atTop ({m₀} : Finset AbelianZetaMode)] with s hs
    have hm₀ : m₀ ∈ s := hs (by simp)
    rw [← Finset.mul_prod_erase s (realParityModeFactor θ) hm₀]
    have htail : ∏ m ∈ s.erase m₀, realParityModeFactor θ m ≤ 1 := by
      apply Finset.prod_le_one
      · intro m hm
        exact (realParityModeFactor_pos θ m).le
      · intro m hm
        exact (realParityModeFactor_lt_one θ m).le
    exact mul_le_of_le_one_right (realParityModeFactor_pos θ m₀).le htail
  have hrlt : r < 1 := lt_of_le_of_lt hrle (realParityModeFactor_lt_one θ m₀)
  rw [integral_classLaw_parity_general_eq_realProduct]
  exact ⟨hrpos, hrlt⟩

/-- **Parity mass law `(GAS4.1)`.**  Under the abelian zeta gas at `σ > 1`, the expected native
parity of the total cyclic-factor count is exactly `Z(2σ) / Z(σ)^2`. -/
theorem integral_classLaw_parity (σ : EulerSigma) :
    (∫ A, A.parity ∂classLaw (temperatureConv σ).toAbelianZetaParameters) =
      (temperatureConv σ.double).zetaPartition /
        (temperatureConv σ).zetaPartition ^ 2 := by
  simpa [AbelianZetaConvergentParameters.zetaPartition] using
    integral_classLaw_parity_general (temperatureConv σ)

/-- Nonnegative density carrying a base parameter point to a tilted parameter point. -/
def AbelianZetaConvergentParameters.gasTiltDensityNNReal
    (θ θ' : AbelianZetaConvergentParameters) (A : AbelianZetaGroupClass) : ℝ≥0 :=
  (θ'.nnNormalizer / θ.nnNormalizer) *
    Real.toNNReal (θ.gasTilt θ' A)

/-- General two-observable tilt as an exact density between class laws. -/
theorem classLaw_eq_withDensity_gasTilt
    (θ θ' : AbelianZetaConvergentParameters) :
    classLaw θ'.toAbelianZetaParameters =
      (classLaw θ.toAbelianZetaParameters).withDensity
        (fun A => (θ.gasTiltDensityNNReal θ' A : ℝ≥0∞)) := by
  refine Measure.ext_of_singleton fun A => ?_
  rw [classLaw_singleton, withDensity_singleton, classLaw_singleton,
    θ'.classMass_eq_ennNormalizer_mul_twoObservableWeight A,
    θ.classMass_eq_ennNormalizer_mul_twoObservableWeight A]
  have hw : 0 ≤ abelianZetaTwoObservableWeight θ.toAbelianZetaParameters A :=
    AbelianZetaConvergentParameters.twoObservableWeight_nonneg
      θ.toAbelianZetaParameters A
  have ht : 0 ≤ θ.gasTilt θ' A := θ.gasTilt_nonneg θ' A
  have hnn : θ.nnNormalizer ≠ 0 := nnNormalizer_ne_zero θ
  have hdensity : ((θ.gasTiltDensityNNReal θ' A : ℝ≥0) : ℝ≥0∞) =
      (θ'.ennNormalizer / θ.ennNormalizer) * ENNReal.ofReal (θ.gasTilt θ' A) := by
    rw [AbelianZetaConvergentParameters.gasTiltDensityNNReal, ENNReal.coe_mul,
      ENNReal.coe_div hnn, AbelianZetaConvergentParameters.ennNormalizer,
      AbelianZetaConvergentParameters.ennNormalizer]
    rw [Real.toNNReal_of_nonneg ht]
    rw [ENNReal.ofReal_eq_coe_nnreal ht]
  have hθ : θ.ennNormalizer ≠ 0 :=
    AbelianZetaConvergentParameters.ennNormalizer_ne_zero θ
  have htop : θ.ennNormalizer ≠ ⊤ := by
    rw [AbelianZetaConvergentParameters.ennNormalizer]
    exact ENNReal.coe_ne_top
  have hcancel : θ'.ennNormalizer / θ.ennNormalizer * θ.ennNormalizer =
      θ'.ennNormalizer :=
    ENNReal.div_mul_cancel hθ htop
  rw [hdensity]
  calc
    θ'.ennNormalizer *
        ENNReal.ofReal (abelianZetaTwoObservableWeight θ'.toAbelianZetaParameters A) =
      (θ'.ennNormalizer / θ.ennNormalizer * θ.ennNormalizer) *
        ENNReal.ofReal (abelianZetaTwoObservableWeight θ'.toAbelianZetaParameters A) := by
          rw [hcancel]
    _ = (θ'.ennNormalizer / θ.ennNormalizer * ENNReal.ofReal (θ.gasTilt θ' A)) *
        (θ.ennNormalizer *
          ENNReal.ofReal (abelianZetaTwoObservableWeight θ.toAbelianZetaParameters A)) := by
      have hof :
          ENNReal.ofReal (abelianZetaTwoObservableWeight θ.toAbelianZetaParameters A) *
              ENNReal.ofReal (θ.gasTilt θ' A) =
            ENNReal.ofReal (abelianZetaTwoObservableWeight θ'.toAbelianZetaParameters A) := by
        rw [← ENNReal.ofReal_mul hw, θ.twoObservableWeight_mul_gasTilt θ' A]
      rw [← hof]
      ring

private theorem gasTiltDensityNNReal_smul_parity
    (θ θ' : AbelianZetaConvergentParameters) (A : AbelianZetaGroupClass) :
    θ.gasTiltDensityNNReal θ' A • A.parity =
      ((θ'.nnNormalizer / θ.nnNormalizer : ℝ)) •
        ((θ.gasTilt θ' A : ℂ) * A.parity) := by
  rw [AbelianZetaConvergentParameters.gasTiltDensityNNReal]
  rw [NNReal.smul_def]
  simp only [NNReal.coe_mul, NNReal.coe_div]
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  rw [Real.coe_toNNReal (θ.gasTilt θ' A) (θ.gasTilt_nonneg θ' A)]
  ring

/-- **Signed grand response `(GAS4.2)`.**  For any two points in the exact convergence chamber,
the native parity twist imports the doubled target ladder:
`E_θ[(-1)^Omega · tilt(θ,θ')] = Z(2θ') / (Z(θ') Z(θ))`. -/
theorem integral_classLaw_parity_mul_gasTilt
    (θ θ' : AbelianZetaConvergentParameters) :
    (∫ A, A.parity * (θ.gasTilt θ' A : ℂ) ∂classLaw θ.toAbelianZetaParameters) =
      θ'.double.zetaPartition / (θ'.zetaPartition * θ.zetaPartition) := by
  have hmeas : Measurable (θ.gasTiltDensityNNReal θ') := measurable_from_top
  have hchange := integral_withDensity_eq_integral_smul
    (μ := classLaw θ.toAbelianZetaParameters) hmeas
    (fun A : AbelianZetaGroupClass => A.parity)
  rw [← classLaw_eq_withDensity_gasTilt θ θ'] at hchange
  have hfun :
      (fun A : AbelianZetaGroupClass => θ.gasTiltDensityNNReal θ' A • A.parity) =
        fun A => ((θ'.nnNormalizer / θ.nnNormalizer : ℝ)) •
          ((θ.gasTilt θ' A : ℂ) * A.parity) := by
    funext A
    exact gasTiltDensityNNReal_smul_parity θ θ' A
  rw [hfun, MeasureTheory.integral_smul] at hchange
  rw [integral_classLaw_parity_general] at hchange
  have hc :
      (((θ'.nnNormalizer / θ.nnNormalizer : ℝ) : ℂ)) =
        θ'.complexNormalizer / θ.complexNormalizer := by
    push_cast
    rw [θ'.coe_nnNormalizer_eq_complexNormalizer, θ.coe_nnNormalizer_eq_complexNormalizer]
  change θ'.double.zetaPartition / θ'.zetaPartition ^ 2 =
    (((θ'.nnNormalizer / θ.nnNormalizer : ℝ) : ℂ)) *
      (∫ A, (θ.gasTilt θ' A : ℂ) * A.parity
        ∂classLaw θ.toAbelianZetaParameters) at hchange
  rw [hc, θ'.complexNormalizer_eq_zetaPartition_inv,
    θ.complexNormalizer_eq_zetaPartition_inv] at hchange
  have hz := θ.zetaPartition_ne_zero
  have hz' := θ'.zetaPartition_ne_zero
  have hz2 := θ'.double.zetaPartition_ne_zero
  rw [show (fun A : AbelianZetaGroupClass =>
    A.parity * (θ.gasTilt θ' A : ℂ)) =
      fun A => (θ.gasTilt θ' A : ℂ) * A.parity by
        funext A
        ring]
  field_simp at hchange ⊢
  exact hchange.symm

end

end GaloisForLFunctions.HTGeometry
