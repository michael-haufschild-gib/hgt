import GaloisForLFunctions.HTGeometry.EllipticGammaAdditiveLogKernel
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Entire double products for the additive elliptic gamma function

The numerator and denominator double products converge locally uniformly on the whole additive
plane and are entire, nonzero functions. Their quotient is the actual elliptic gamma product.
On its regular locus its logarithmic derivative is exactly the normally convergent additive kernel,
so the analytic product and the previously formalized hierarchy equations are now the same object.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- One numerator factor of the additive elliptic-gamma double product. -/
def ellipticGammaForwardFactor (σ τ : ℂ) (jk : ℕ × ℕ) (z : ℂ) : ℂ :=
  1 - ellipticGammaForwardArgument (ellipticNome σ) (ellipticNome τ)
    (ellipticThetaCoordinate τ z) jk.1 jk.2

/-- The entire numerator double product. -/
def ellipticGammaForwardProduct (σ τ z : ℂ) : ℂ :=
  ∏' jk : ℕ × ℕ, ellipticGammaForwardFactor σ τ jk z

/-- One denominator factor of the additive elliptic-gamma double product. -/
def ellipticGammaBackwardFactor (σ τ : ℂ) (jk : ℕ × ℕ) (z : ℂ) : ℂ :=
  1 - ellipticGammaBackwardArgument (ellipticNome σ) (ellipticNome τ)
    (ellipticThetaCoordinate τ z) jk.1 jk.2

/-- The entire denominator double product. -/
def ellipticGammaBackwardProduct (σ τ z : ℂ) : ℂ :=
  ∏' jk : ℕ × ℕ, ellipticGammaBackwardFactor σ τ jk z

/-- The numerator double product converges locally uniformly on the whole additive plane. -/
theorem hasProdLocallyUniformlyOn_ellipticGammaForwardFactor
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    HasProdLocallyUniformlyOn (ellipticGammaForwardFactor σ τ)
      (ellipticGammaForwardProduct σ τ) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  have hInvCont : Continuous (fun z => (ellipticThetaCoordinate τ z)⁻¹) := by
    apply Continuous.inv₀
    · exact continuous_iff_continuousAt.mpr fun z =>
        (analyticAt_ellipticThetaCoordinate τ z).continuousAt
    · exact ellipticThetaCoordinate_ne_zero τ
  obtain ⟨C, hC⟩ := hK.bddAbove_image hInvCont.norm.continuousOn
  let D : ℝ := max C 0
  have hD0 : 0 ≤ D := le_max_right _ _
  have hD : ∀ z ∈ K, ‖(ellipticThetaCoordinate τ z)⁻¹‖ ≤ D := by
    intro z hz
    exact (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hp := norm_ellipticNome_lt_one hσ
  have hq := norm_ellipticNome_lt_one hτ
  have hweights : Summable (fun jk : ℕ × ℕ =>
      ‖ellipticNome σ‖ ^ (jk.1 + 1) * ‖ellipticNome τ‖ ^ (jk.2 + 1)) := by
    simpa [ellipticGammaForwardArgument] using
      (summable_norm_ellipticGammaForwardArgument
        (p := ellipticNome σ) (q := ellipticNome τ) (x := (1 : ℂ)) hp hq)
  have hu : Summable (fun jk : ℕ × ℕ =>
      D * (‖ellipticNome σ‖ ^ (jk.1 + 1) * ‖ellipticNome τ‖ ^ (jk.2 + 1))) :=
    hweights.mul_left D
  have hbound : ∀ᶠ jk : ℕ × ℕ in cofinite, ∀ z ∈ K,
      ‖-ellipticGammaForwardArgument (ellipticNome σ) (ellipticNome τ)
        (ellipticThetaCoordinate τ z) jk.1 jk.2‖ ≤
        D * (‖ellipticNome σ‖ ^ (jk.1 + 1) * ‖ellipticNome τ‖ ^ (jk.2 + 1)) := by
    filter_upwards with jk
    intro z hz
    have hInv := hD z hz
    have hw0 : 0 ≤ ‖ellipticNome σ‖ ^ (jk.1 + 1) *
        ‖ellipticNome τ‖ ^ (jk.2 + 1) :=
      mul_nonneg (pow_nonneg (norm_nonneg (ellipticNome σ)) (jk.1 + 1))
        (pow_nonneg (norm_nonneg (ellipticNome τ)) (jk.2 + 1))
    simp only [norm_neg, ellipticGammaForwardArgument, div_eq_mul_inv, norm_mul,
      norm_pow]
    nlinarith
  convert! Summable.hasProdUniformlyOn_one_add hK hu hbound (fun jk => by
    have hcont : Continuous (fun x : ℂ =>
        -(ellipticNome σ ^ (jk.1 + 1) * ellipticNome τ ^ (jk.2 + 1) *
          (ellipticThetaCoordinate τ x)⁻¹)) :=
      ((continuous_const.mul continuous_const).mul hInvCont).neg
    exact hcont.continuousOn) using 1

/-- The denominator double product converges locally uniformly on the whole additive plane. -/
theorem hasProdLocallyUniformlyOn_ellipticGammaBackwardFactor
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    HasProdLocallyUniformlyOn (ellipticGammaBackwardFactor σ τ)
      (ellipticGammaBackwardProduct σ τ) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  have hCoordCont : Continuous (ellipticThetaCoordinate τ) :=
    continuous_iff_continuousAt.mpr fun z =>
      (analyticAt_ellipticThetaCoordinate τ z).continuousAt
  obtain ⟨C, hC⟩ := hK.bddAbove_image hCoordCont.norm.continuousOn
  let D : ℝ := max C 0
  have hD : ∀ z ∈ K, ‖ellipticThetaCoordinate τ z‖ ≤ D := by
    intro z hz
    exact (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hp := norm_ellipticNome_lt_one hσ
  have hq := norm_ellipticNome_lt_one hτ
  have hweights : Summable (fun jk : ℕ × ℕ =>
      ‖ellipticNome σ‖ ^ jk.1 * ‖ellipticNome τ‖ ^ jk.2) := by
    simpa [ellipticGammaBackwardArgument] using
      (summable_norm_ellipticGammaBackwardArgument
        (p := ellipticNome σ) (q := ellipticNome τ) (x := (1 : ℂ)) hp hq)
  have hu : Summable (fun jk : ℕ × ℕ =>
      D * (‖ellipticNome σ‖ ^ jk.1 * ‖ellipticNome τ‖ ^ jk.2)) :=
    hweights.mul_left D
  have hbound : ∀ᶠ jk : ℕ × ℕ in cofinite, ∀ z ∈ K,
      ‖-ellipticGammaBackwardArgument (ellipticNome σ) (ellipticNome τ)
        (ellipticThetaCoordinate τ z) jk.1 jk.2‖ ≤
        D * (‖ellipticNome σ‖ ^ jk.1 * ‖ellipticNome τ‖ ^ jk.2) := by
    filter_upwards with jk
    intro z hz
    have hCoord := hD z hz
    have hw0 : 0 ≤ ‖ellipticNome σ‖ ^ jk.1 * ‖ellipticNome τ‖ ^ jk.2 :=
      mul_nonneg (pow_nonneg (norm_nonneg (ellipticNome σ)) jk.1)
        (pow_nonneg (norm_nonneg (ellipticNome τ)) jk.2)
    simp only [norm_neg, ellipticGammaBackwardArgument, norm_mul, norm_pow]
    nlinarith
  convert! Summable.hasProdUniformlyOn_one_add hK hu hbound (fun jk => by
    have hcont : Continuous (fun x : ℂ =>
        -(ellipticNome σ ^ jk.1 * ellipticNome τ ^ jk.2 *
          ellipticThetaCoordinate τ x)) :=
      ((continuous_const.mul continuous_const).mul hCoordCont).neg
    exact hcont.continuousOn) using 1

/-- Every numerator factor is entire. -/
theorem differentiable_ellipticGammaForwardFactor :
    Differentiable ℂ (ellipticGammaForwardFactor σ τ jk) := by
  intro z
  apply AnalyticAt.differentiableAt
  exact analyticAt_const.sub <|
    ((analyticAt_const.mul analyticAt_const).div
      (analyticAt_ellipticThetaCoordinate τ z)
        (ellipticThetaCoordinate_ne_zero τ z))

/-- Every denominator factor is entire. -/
theorem differentiable_ellipticGammaBackwardFactor :
    Differentiable ℂ (ellipticGammaBackwardFactor σ τ jk) := by
  intro z
  exact (analyticAt_const.sub
    ((analyticAt_const.mul analyticAt_const).mul
      (analyticAt_ellipticThetaCoordinate τ z))).differentiableAt

/-- The locally uniform numerator product is entire. -/
theorem differentiable_ellipticGammaForwardProduct
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    Differentiable ℂ (ellipticGammaForwardProduct σ τ) := by
  have hprod := hasProdLocallyUniformlyOn_ellipticGammaForwardFactor hσ hτ
  have ht := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod)
  have hd : ∀ᶠ S : Finset (ℕ × ℕ) in atTop,
      DifferentiableOn ℂ (fun z => ∏ jk ∈ S, ellipticGammaForwardFactor σ τ jk z) Set.univ := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun jk _ =>
      (differentiable_ellipticGammaForwardFactor (σ := σ) (τ := τ)
        (jk := jk)).differentiableOn
  intro z
  simpa only [differentiableWithinAt_univ] using
    ht.differentiableOn hd isOpen_univ z (Set.mem_univ z)

/-- The locally uniform denominator product is entire. -/
theorem differentiable_ellipticGammaBackwardProduct
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    Differentiable ℂ (ellipticGammaBackwardProduct σ τ) := by
  have hprod := hasProdLocallyUniformlyOn_ellipticGammaBackwardFactor hσ hτ
  have ht := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod)
  have hd : ∀ᶠ S : Finset (ℕ × ℕ) in atTop,
      DifferentiableOn ℂ (fun z => ∏ jk ∈ S, ellipticGammaBackwardFactor σ τ jk z) Set.univ := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun jk _ =>
      (differentiable_ellipticGammaBackwardFactor (σ := σ) (τ := τ)
        (jk := jk)).differentiableOn
  intro z
  simpa only [differentiableWithinAt_univ] using
    ht.differentiableOn hd isOpen_univ z (Set.mem_univ z)

/-- Every fiber of the exponential theta coordinate is countable. -/
theorem ellipticThetaCoordinate_fiber_countable (τ c : ℂ) :
    {z : ℂ | ellipticThetaCoordinate τ z = c}.Countable := by
  let a : ℂ := 2 * Real.pi * I
  let b : ℂ := -Complex.exp (Real.pi * I * τ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (mod_cast Real.pi_ne_zero)) I_ne_zero
  have hb : b ≠ 0 := by simp [b]
  have hexp : (Complex.exp ⁻¹' ({c / b} : Set ℂ)).Countable :=
    Set.Countable.preimage_cexp (Set.countable_singleton (c / b))
  have hlin : Function.Injective (fun z : ℂ => a * z) :=
    fun _ _ h => mul_left_cancel₀ ha h
  have hpre := hexp.preimage hlin
  apply hpre.mono
  intro z hz
  change ellipticThetaCoordinate τ z = c at hz
  change Complex.exp (a * z) ∈ ({c / b} : Set ℂ)
  rw [Set.mem_singleton_iff]
  rw [ellipticThetaCoordinate] at hz
  change b * Complex.exp (a * z) = c at hz
  exact (eq_div_iff hb).2 (by simpa [mul_comm] using hz)

/-- There is a common point at which both entire double products are nonzero; in particular neither
product is the zero function. -/
theorem exists_ellipticGammaProducts_ne_zero
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    ∃ z : ℂ, ellipticGammaForwardProduct σ τ z ≠ 0 ∧
      ellipticGammaBackwardProduct σ τ z ≠ 0 := by
  let Zf : Set ℂ := ⋃ jk : ℕ × ℕ,
    {z : ℂ | ellipticThetaCoordinate τ z =
      ellipticNome σ ^ (jk.1 + 1) * ellipticNome τ ^ (jk.2 + 1)}
  let Zb : Set ℂ := ⋃ jk : ℕ × ℕ,
    {z : ℂ | ellipticThetaCoordinate τ z =
      (ellipticNome σ ^ jk.1 * ellipticNome τ ^ jk.2)⁻¹}
  have hZf : Zf.Countable := Set.countable_iUnion fun jk =>
    ellipticThetaCoordinate_fiber_countable _ _
  have hZb : Zb.Countable := Set.countable_iUnion fun jk =>
    ellipticThetaCoordinate_fiber_countable _ _
  have hZ : (Zf ∪ Zb).Countable := hZf.union hZb
  letI : Uncountable ℂ := Complex.ofReal_injective.uncountable
  have hne : Zf ∪ Zb ≠ Set.univ := by
    intro h
    apply Set.not_countable_univ (α := ℂ)
    rw [← h]
    exact hZ
  obtain ⟨z, hz⟩ := Set.nonempty_compl.mpr hne
  have hz' : z ∉ Zf ∪ Zb := by simpa using hz
  have hzF : ∀ jk : ℕ × ℕ, ellipticGammaForwardFactor σ τ jk z ≠ 0 := by
    intro jk hzero
    apply hz'
    apply Set.mem_union_left Zb
    apply Set.mem_iUnion.mpr
    refine ⟨jk, ?_⟩
    change ellipticThetaCoordinate τ z =
      ellipticNome σ ^ (jk.1 + 1) * ellipticNome τ ^ (jk.2 + 1)
    rw [ellipticGammaForwardFactor, sub_eq_zero] at hzero
    have hx0 := ellipticThetaCoordinate_ne_zero τ z
    exact (div_eq_one_iff_eq hx0).mp hzero.symm |>.symm
  have hzB : ∀ jk : ℕ × ℕ, ellipticGammaBackwardFactor σ τ jk z ≠ 0 := by
    intro jk hzero
    apply hz'
    apply Set.mem_union_right Zf
    apply Set.mem_iUnion.mpr
    refine ⟨jk, ?_⟩
    change ellipticThetaCoordinate τ z =
      (ellipticNome σ ^ jk.1 * ellipticNome τ ^ jk.2)⁻¹
    rw [ellipticGammaBackwardFactor, sub_eq_zero] at hzero
    have hc0 : ellipticNome σ ^ jk.1 * ellipticNome τ ^ jk.2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (ellipticNome_ne_zero σ))
        (pow_ne_zero _ (ellipticNome_ne_zero τ))
    exact (mul_eq_one_iff_inv_eq₀ hc0).mp hzero.symm |>.symm
  have hsumF := summable_norm_ellipticGammaForwardArgument
    (p := ellipticNome σ) (q := ellipticNome τ)
      (x := ellipticThetaCoordinate τ z)
      (norm_ellipticNome_lt_one hσ) (norm_ellipticNome_lt_one hτ)
  have hsumB := summable_norm_ellipticGammaBackwardArgument
    (p := ellipticNome σ) (q := ellipticNome τ)
      (x := ellipticThetaCoordinate τ z)
      (norm_ellipticNome_lt_one hσ) (norm_ellipticNome_lt_one hτ)
  refine ⟨z, ?_, ?_⟩
  · have hprod := tprod_one_add_ne_zero_of_summable
      (f := fun jk : ℕ × ℕ =>
        -ellipticGammaForwardArgument (ellipticNome σ) (ellipticNome τ)
          (ellipticThetaCoordinate τ z) jk.1 jk.2)
      (fun jk => by simpa [ellipticGammaForwardFactor] using! hzF jk)
      (by simpa only [norm_neg] using hsumF)
    simpa [ellipticGammaForwardProduct, ellipticGammaForwardFactor] using! hprod
  · have hprod := tprod_one_add_ne_zero_of_summable
      (f := fun jk : ℕ × ℕ =>
        -ellipticGammaBackwardArgument (ellipticNome σ) (ellipticNome τ)
          (ellipticThetaCoordinate τ z) jk.1 jk.2)
      (fun jk => by simpa [ellipticGammaBackwardFactor] using! hzB jk)
      (by simpa only [norm_neg] using hsumB)
    simpa [ellipticGammaBackwardProduct, ellipticGammaBackwardFactor] using! hprod

/-- The logarithmic derivative of one numerator factor is the positive rational atom. -/
theorem logDeriv_ellipticGammaForwardFactor
    (σ τ : ℂ) (jk : ℕ × ℕ) (z : ℂ) :
    logDeriv (ellipticGammaForwardFactor σ τ jk) z =
      2 * Real.pi * I *
        ellipticGammaLogAtom
          (ellipticGammaForwardArgument (ellipticNome σ) (ellipticNome τ)
            (ellipticThetaCoordinate τ z) jk.1 jk.2) := by
  let c := ellipticNome σ ^ (jk.1 + 1) * ellipticNome τ ^ (jk.2 + 1)
  let X := ellipticThetaCoordinate τ
  have hX0 : X z ≠ 0 := ellipticThetaCoordinate_ne_zero τ z
  have hX := hasDerivAt_ellipticThetaCoordinate τ z
  have harg : HasDerivAt (fun w => c / X w)
      (-(2 * Real.pi * I) * (c / X z)) z := by
    convert! (hasDerivAt_const z c).div hX hX0 using 1
    simp only [X] at hX0 ⊢
    field_simp [hX0] <;> ring
  have hfac : HasDerivAt (ellipticGammaForwardFactor σ τ jk)
      (2 * Real.pi * I * (c / X z)) z := by
    convert! (hasDerivAt_const z 1).sub harg using 1 <;> ring
  rw [logDeriv_apply, hfac.deriv]
  rw [ellipticGammaForwardFactor, ellipticGammaForwardArgument,
    ellipticGammaLogAtom]
  dsimp [c, X] at hfac ⊢
  field_simp [hX0]

/-- The logarithmic derivative of one denominator factor is the negative rational atom. -/
theorem logDeriv_ellipticGammaBackwardFactor
    (σ τ : ℂ) (jk : ℕ × ℕ) (z : ℂ) :
    logDeriv (ellipticGammaBackwardFactor σ τ jk) z =
      -(2 * Real.pi * I) *
        ellipticGammaLogAtom
          (ellipticGammaBackwardArgument (ellipticNome σ) (ellipticNome τ)
            (ellipticThetaCoordinate τ z) jk.1 jk.2) := by
  let c := ellipticNome σ ^ jk.1 * ellipticNome τ ^ jk.2
  let X := ellipticThetaCoordinate τ
  have hX := hasDerivAt_ellipticThetaCoordinate τ z
  have harg : HasDerivAt (fun w => c * X w)
      (2 * Real.pi * I * (c * X z)) z := by
    convert! hX.const_mul c using 1 <;> ring
  have hfac : HasDerivAt (ellipticGammaBackwardFactor σ τ jk)
      (-(2 * Real.pi * I) * (c * X z)) z := by
    convert! (hasDerivAt_const z 1).sub harg using 1 <;> ring
  rw [logDeriv_apply, hfac.deriv]
  rw [ellipticGammaBackwardFactor, ellipticGammaBackwardArgument,
    ellipticGammaLogAtom]
  dsimp [c, X] at hfac ⊢
  field_simp

/-- The numerator product logarithmic derivative is the normally convergent forward atom sum. -/
theorem logDeriv_ellipticGammaForwardProduct
    {σ τ z : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hz : ellipticGammaForwardProduct σ τ z ≠ 0) :
    logDeriv (ellipticGammaForwardProduct σ τ) z =
      2 * Real.pi * I *
        ∑' jk : ℕ × ℕ,
          ellipticGammaLogAtom
            (ellipticGammaForwardArgument (ellipticNome σ) (ellipticNome τ)
              (ellipticThetaCoordinate τ z) jk.1 jk.2) := by
  have hfac : ∀ jk : ℕ × ℕ, ellipticGammaForwardFactor σ τ jk z ≠ 0 := by
    intro jk hjk
    apply hz
    rw [ellipticGammaForwardProduct]
    exact tprod_of_exists_eq_zero ⟨jk, hjk⟩
  have hsumArg := summable_norm_ellipticGammaForwardArgument
    (p := ellipticNome σ) (q := ellipticNome τ)
      (x := ellipticThetaCoordinate τ z)
      (norm_ellipticNome_lt_one hσ) (norm_ellipticNome_lt_one hτ)
  have hsumAtom := summable_ellipticGammaLogAtom_of_summable_norm hsumArg
  have hsumLD : Summable (fun jk : ℕ × ℕ =>
      logDeriv (ellipticGammaForwardFactor σ τ jk) z) := by
    simpa only [logDeriv_ellipticGammaForwardFactor] using!
      hsumAtom.mul_left (2 * Real.pi * I)
  have hprod : MultipliableLocallyUniformlyOn (ellipticGammaForwardFactor σ τ) Set.univ :=
    ⟨_, hasProdLocallyUniformlyOn_ellipticGammaForwardFactor hσ hτ⟩
  change logDeriv (fun x => ∏' jk : ℕ × ℕ,
    ellipticGammaForwardFactor σ τ jk x) z = _
  rw [logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z) hfac
    (fun jk => (differentiable_ellipticGammaForwardFactor (σ := σ) (τ := τ)
      (jk := jk)).differentiableOn) hsumLD hprod hz]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro jk
  exact logDeriv_ellipticGammaForwardFactor σ τ jk z

/-- The denominator product logarithmic derivative is the negative backward atom sum. -/
theorem logDeriv_ellipticGammaBackwardProduct
    {σ τ z : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hz : ellipticGammaBackwardProduct σ τ z ≠ 0) :
    logDeriv (ellipticGammaBackwardProduct σ τ) z =
      -(2 * Real.pi * I) *
        ∑' jk : ℕ × ℕ,
          ellipticGammaLogAtom
            (ellipticGammaBackwardArgument (ellipticNome σ) (ellipticNome τ)
              (ellipticThetaCoordinate τ z) jk.1 jk.2) := by
  have hfac : ∀ jk : ℕ × ℕ, ellipticGammaBackwardFactor σ τ jk z ≠ 0 := by
    intro jk hjk
    apply hz
    rw [ellipticGammaBackwardProduct]
    exact tprod_of_exists_eq_zero ⟨jk, hjk⟩
  have hsumArg := summable_norm_ellipticGammaBackwardArgument
    (p := ellipticNome σ) (q := ellipticNome τ)
      (x := ellipticThetaCoordinate τ z)
      (norm_ellipticNome_lt_one hσ) (norm_ellipticNome_lt_one hτ)
  have hsumAtom := summable_ellipticGammaLogAtom_of_summable_norm hsumArg
  have hsumLD : Summable (fun jk : ℕ × ℕ =>
      logDeriv (ellipticGammaBackwardFactor σ τ jk) z) := by
    simpa only [logDeriv_ellipticGammaBackwardFactor] using!
      hsumAtom.mul_left (-(2 * Real.pi * I))
  have hprod : MultipliableLocallyUniformlyOn (ellipticGammaBackwardFactor σ τ) Set.univ :=
    ⟨_, hasProdLocallyUniformlyOn_ellipticGammaBackwardFactor hσ hτ⟩
  change logDeriv (fun x => ∏' jk : ℕ × ℕ,
    ellipticGammaBackwardFactor σ τ jk x) z = _
  rw [logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z) hfac
    (fun jk => (differentiable_ellipticGammaBackwardFactor (σ := σ) (τ := τ)
      (jk := jk)).differentiableOn) hsumLD hprod hz]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro jk
  exact logDeriv_ellipticGammaBackwardFactor σ τ jk z

/-- The actual additive elliptic-gamma product: entire numerator divided by entire denominator. -/
def ellipticGammaProduct (σ τ z : ℂ) : ℂ :=
  ellipticGammaForwardProduct σ τ z / ellipticGammaBackwardProduct σ τ z

/-- On the regular locus, the logarithmic derivative of the actual elliptic-gamma product is
exactly the normally convergent additive double-sum kernel. -/
theorem logDeriv_ellipticGammaProduct_eq_additiveKernel
    {σ τ z : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hzF : ellipticGammaForwardProduct σ τ z ≠ 0)
    (hzB : ellipticGammaBackwardProduct σ τ z ≠ 0) :
    logDeriv (ellipticGammaProduct σ τ) z =
      ellipticGammaAdditiveLogKernel σ τ z := by
  change logDeriv (fun w => ellipticGammaForwardProduct σ τ w /
    ellipticGammaBackwardProduct σ τ w) z = _
  rw [logDeriv_div z hzF hzB
    (differentiable_ellipticGammaForwardProduct hσ hτ z)
    (differentiable_ellipticGammaBackwardProduct hσ hτ z)]
  rw [logDeriv_ellipticGammaForwardProduct hσ hτ hzF,
    logDeriv_ellipticGammaBackwardProduct hσ hτ hzB]
  rw [ellipticGammaAdditiveLogKernel, ellipticGammaLogKernel]
  have hsumF := summable_ellipticGammaLogAtom_of_summable_norm
    (summable_norm_ellipticGammaForwardArgument
      (p := ellipticNome σ) (q := ellipticNome τ)
        (x := ellipticThetaCoordinate τ z)
        (norm_ellipticNome_lt_one hσ) (norm_ellipticNome_lt_one hτ))
  have hsumB := summable_ellipticGammaLogAtom_of_summable_norm
    (summable_norm_ellipticGammaBackwardArgument
      (p := ellipticNome σ) (q := ellipticNome τ)
        (x := ellipticThetaCoordinate τ z)
        (norm_ellipticNome_lt_one hσ) (norm_ellipticNome_lt_one hτ))
  simp only [ellipticGammaLogSummand]
  rw [hsumF.tsum_add hsumB]
  ring

end

end GaloisForLFunctions
