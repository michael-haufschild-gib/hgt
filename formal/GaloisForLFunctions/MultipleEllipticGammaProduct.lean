import GaloisForLFunctions.MultipleEllipticGammaAdditiveHierarchy
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Entire products for all-order multiple elliptic gamma

The parity-independent forward and backward factors are assembled into locally uniformly
convergent entire products for every finite parameter set.  Subsequent results identify their
parity-dependent product or quotient with the multiple elliptic gamma function.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι]

theorem hasDerivAt_multipleEllipticGammaCoordinate (z : ℂ) :
    HasDerivAt multipleEllipticGammaCoordinate
      (2 * Real.pi * I * multipleEllipticGammaCoordinate z) z := by
  have hlin : HasDerivAt (fun w : ℂ => 2 * Real.pi * I * w)
      (2 * Real.pi * I) z := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id z).const_mul (2 * Real.pi * I)
  have hexp := (Complex.hasDerivAt_exp (2 * Real.pi * I * z)).comp z hlin
  convert hexp using 1
  all_goals (simp [multipleEllipticGammaCoordinate]; ring)

theorem analyticAt_multipleEllipticGammaCoordinate (z : ℂ) :
    AnalyticAt ℂ multipleEllipticGammaCoordinate z := by
  have hlin : AnalyticAt ℂ (fun w : ℂ => 2 * Real.pi * I * w) z :=
    analyticAt_const.mul analyticAt_id
  simpa [multipleEllipticGammaCoordinate, Function.comp_def] using
    analyticAt_cexp.comp hlin

/-- One forward entire factor of the multiple elliptic gamma product. -/
def multipleEllipticGammaForwardFactor (τ : ι → ℂ) (n : ι → ℕ) (z : ℂ) : ℂ :=
  1 - multipleEllipticGammaForwardArgument (fun i => ellipticNome (τ i))
    (multipleEllipticGammaCoordinate z) n

/-- One backward entire factor of the multiple elliptic gamma product. -/
def multipleEllipticGammaBackwardFactor (τ : ι → ℂ) (n : ι → ℕ) (z : ℂ) : ℂ :=
  1 - multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
    (multipleEllipticGammaCoordinate z) n

/-- The forward all-order entire product. -/
def multipleEllipticGammaForwardProduct (τ : ι → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ι → ℕ, multipleEllipticGammaForwardFactor τ n z

/-- The backward all-order entire product. -/
def multipleEllipticGammaBackwardProduct (τ : ι → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ι → ℕ, multipleEllipticGammaBackwardFactor τ n z

/-- The forward product converges locally uniformly on the additive plane. -/
theorem hasProdLocallyUniformlyOn_multipleEllipticGammaForwardFactor
    {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im) :
    HasProdLocallyUniformlyOn (multipleEllipticGammaForwardFactor τ)
      (multipleEllipticGammaForwardProduct τ) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  have hInvCont : Continuous (fun z => (multipleEllipticGammaCoordinate z)⁻¹) := by
    apply Continuous.inv₀
    · exact continuous_iff_continuousAt.mpr fun z =>
        (analyticAt_multipleEllipticGammaCoordinate z).continuousAt
    · exact multipleEllipticGammaCoordinate_ne_zero
  obtain ⟨C, hC⟩ := hK.bddAbove_image hInvCont.norm.continuousOn
  let D : ℝ := max C 0
  have hD : ∀ z ∈ K, ‖(multipleEllipticGammaCoordinate z)⁻¹‖ ≤ D := by
    intro z hz
    exact (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hweights : Summable (fun n : ι → ℕ =>
      ∏ i, ‖ellipticNome (τ i)‖ ^ (n i + 1)) := by
    simpa [multipleEllipticGammaForwardArgument] using
      (summable_norm_multipleEllipticGammaForwardArgument
        (p := fun i => ellipticNome (τ i)) (x := (1 : ℂ))
        (fun i => norm_ellipticNome_lt_one (hτ i)))
  have hu : Summable (fun n : ι → ℕ =>
      D * ∏ i, ‖ellipticNome (τ i)‖ ^ (n i + 1)) := hweights.mul_left D
  have hbound : ∀ᶠ n : ι → ℕ in cofinite, ∀ z ∈ K,
      ‖-multipleEllipticGammaForwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n‖ ≤
        D * ∏ i, ‖ellipticNome (τ i)‖ ^ (n i + 1) := by
    filter_upwards with n
    intro z hz
    have hInv := hD z hz
    have hw0 : 0 ≤ ∏ i, ‖ellipticNome (τ i)‖ ^ (n i + 1) :=
      Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _
    simp only [norm_neg, multipleEllipticGammaForwardArgument, div_eq_mul_inv,
      norm_mul, norm_pow, norm_prod]
    nlinarith
  convert Summable.hasProdUniformlyOn_one_add hK hu hbound (fun n => by
    have hcoord : Continuous (fun z => (multipleEllipticGammaCoordinate z)⁻¹) := hInvCont
    simpa [multipleEllipticGammaForwardArgument, div_eq_mul_inv] using
      (continuous_const.mul hcoord).neg.continuousOn) using 1

/-- The backward product converges locally uniformly on the additive plane. -/
theorem hasProdLocallyUniformlyOn_multipleEllipticGammaBackwardFactor
    {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im) :
    HasProdLocallyUniformlyOn (multipleEllipticGammaBackwardFactor τ)
      (multipleEllipticGammaBackwardProduct τ) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  have hCoordCont : Continuous multipleEllipticGammaCoordinate :=
    continuous_iff_continuousAt.mpr fun z =>
      (analyticAt_multipleEllipticGammaCoordinate z).continuousAt
  obtain ⟨C, hC⟩ := hK.bddAbove_image hCoordCont.norm.continuousOn
  let D : ℝ := max C 0
  have hD : ∀ z ∈ K, ‖multipleEllipticGammaCoordinate z‖ ≤ D := by
    intro z hz
    exact (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hweights : Summable (fun n : ι → ℕ =>
      ∏ i, ‖ellipticNome (τ i)‖ ^ n i) := by
    simpa [multipleEllipticGammaBackwardArgument] using
      (summable_norm_multipleEllipticGammaBackwardArgument
        (p := fun i => ellipticNome (τ i)) (x := (1 : ℂ))
        (fun i => norm_ellipticNome_lt_one (hτ i)))
  have hu : Summable (fun n : ι → ℕ =>
      D * ∏ i, ‖ellipticNome (τ i)‖ ^ n i) := hweights.mul_left D
  have hbound : ∀ᶠ n : ι → ℕ in cofinite, ∀ z ∈ K,
      ‖-multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n‖ ≤
        D * ∏ i, ‖ellipticNome (τ i)‖ ^ n i := by
    filter_upwards with n
    intro z hz
    have hCoord := hD z hz
    have hw0 : 0 ≤ ∏ i, ‖ellipticNome (τ i)‖ ^ n i :=
      Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _
    simp only [norm_neg, multipleEllipticGammaBackwardArgument, norm_mul,
      norm_pow, norm_prod]
    nlinarith
  convert Summable.hasProdUniformlyOn_one_add hK hu hbound (fun n => by
    simpa [multipleEllipticGammaBackwardArgument] using
      (continuous_const.mul hCoordCont).neg.continuousOn) using 1

theorem differentiable_multipleEllipticGammaForwardFactor
    (τ : ι → ℂ) (n : ι → ℕ) :
    Differentiable ℂ (multipleEllipticGammaForwardFactor τ n) := by
  intro z
  exact (analyticAt_const.sub <|
    analyticAt_const.div (analyticAt_multipleEllipticGammaCoordinate z)
      (multipleEllipticGammaCoordinate_ne_zero z)).differentiableAt

theorem differentiable_multipleEllipticGammaBackwardFactor
    (τ : ι → ℂ) (n : ι → ℕ) :
    Differentiable ℂ (multipleEllipticGammaBackwardFactor τ n) := by
  intro z
  exact (analyticAt_const.sub
    (analyticAt_const.mul (analyticAt_multipleEllipticGammaCoordinate z))).differentiableAt

theorem differentiable_multipleEllipticGammaForwardProduct
    {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im) :
    Differentiable ℂ (multipleEllipticGammaForwardProduct τ) := by
  have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    (hasProdLocallyUniformlyOn_multipleEllipticGammaForwardFactor hτ)
  have hd : ∀ᶠ S : Finset (ι → ℕ) in atTop,
      DifferentiableOn ℂ
        (fun z => ∏ n ∈ S, multipleEllipticGammaForwardFactor τ n z) Set.univ := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun n _ =>
      (differentiable_multipleEllipticGammaForwardFactor τ n).differentiableOn
  intro z
  simpa only [differentiableWithinAt_univ] using
    ht.differentiableOn hd isOpen_univ z (Set.mem_univ z)

theorem differentiable_multipleEllipticGammaBackwardProduct
    {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im) :
    Differentiable ℂ (multipleEllipticGammaBackwardProduct τ) := by
  have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    (hasProdLocallyUniformlyOn_multipleEllipticGammaBackwardFactor hτ)
  have hd : ∀ᶠ S : Finset (ι → ℕ) in atTop,
      DifferentiableOn ℂ
        (fun z => ∏ n ∈ S, multipleEllipticGammaBackwardFactor τ n z) Set.univ := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun n _ =>
      (differentiable_multipleEllipticGammaBackwardFactor τ n).differentiableOn
  intro z
  simpa only [differentiableWithinAt_univ] using
    ht.differentiableOn hd isOpen_univ z (Set.mem_univ z)

/-- Every fiber of the standard exponential coordinate is countable. -/
theorem multipleEllipticGammaCoordinate_fiber_countable (c : ℂ) :
    {z : ℂ | multipleEllipticGammaCoordinate z = c}.Countable := by
  let a : ℂ := 2 * Real.pi * I
  have ha : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (mod_cast Real.pi_ne_zero)) I_ne_zero
  have hexp : (Complex.exp ⁻¹' ({c} : Set ℂ)).Countable :=
    Set.Countable.preimage_cexp (Set.countable_singleton c)
  have hlin : Function.Injective (fun z : ℂ => a * z) :=
    fun _ _ h => mul_left_cancel₀ ha h
  have hpre := hexp.preimage hlin
  apply hpre.mono
  intro z hz
  change Complex.exp (a * z) ∈ ({c} : Set ℂ)
  simpa [a, multipleEllipticGammaCoordinate] using hz

/-- The two all-order entire products are both nonzero functions. -/
theorem exists_multipleEllipticGammaProducts_ne_zero
    {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im) :
    ∃ z : ℂ, multipleEllipticGammaForwardProduct τ z ≠ 0 ∧
      multipleEllipticGammaBackwardProduct τ z ≠ 0 := by
  let Zf : Set ℂ := ⋃ n : ι → ℕ,
    {z : ℂ | multipleEllipticGammaCoordinate z =
      ∏ i, ellipticNome (τ i) ^ (n i + 1)}
  let Zb : Set ℂ := ⋃ n : ι → ℕ,
    {z : ℂ | multipleEllipticGammaCoordinate z =
      (∏ i, ellipticNome (τ i) ^ n i)⁻¹}
  have hZf : Zf.Countable := Set.countable_iUnion fun n =>
    multipleEllipticGammaCoordinate_fiber_countable _
  have hZb : Zb.Countable := Set.countable_iUnion fun n =>
    multipleEllipticGammaCoordinate_fiber_countable _
  have hZ : (Zf ∪ Zb).Countable := hZf.union hZb
  letI : Uncountable ℂ := Complex.ofReal_injective.uncountable
  have hne : Zf ∪ Zb ≠ Set.univ := by
    intro h
    apply Set.not_countable_univ (α := ℂ)
    rw [← h]
    exact hZ
  obtain ⟨z, hz⟩ := Set.nonempty_compl.mpr hne
  have hz' : z ∉ Zf ∪ Zb := by simpa using hz
  have hzF : ∀ n : ι → ℕ, multipleEllipticGammaForwardFactor τ n z ≠ 0 := by
    intro n hzero
    apply hz'
    apply Set.mem_union_left Zb
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change multipleEllipticGammaCoordinate z =
      ∏ i, ellipticNome (τ i) ^ (n i + 1)
    rw [multipleEllipticGammaForwardFactor, sub_eq_zero] at hzero
    exact (div_eq_one_iff_eq (multipleEllipticGammaCoordinate_ne_zero z)).mp
      hzero.symm |>.symm
  have hzB : ∀ n : ι → ℕ, multipleEllipticGammaBackwardFactor τ n z ≠ 0 := by
    intro n hzero
    apply hz'
    apply Set.mem_union_right Zf
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change multipleEllipticGammaCoordinate z =
      (∏ i, ellipticNome (τ i) ^ n i)⁻¹
    rw [multipleEllipticGammaBackwardFactor, sub_eq_zero] at hzero
    have hc0 : (∏ i, ellipticNome (τ i) ^ n i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (ellipticNome_ne_zero (τ i))
    exact (mul_eq_one_iff_inv_eq₀ hc0).mp hzero.symm |>.symm
  have hsumF := summable_norm_multipleEllipticGammaForwardArgument
    (p := fun i => ellipticNome (τ i))
    (x := multipleEllipticGammaCoordinate z)
    (fun i => norm_ellipticNome_lt_one (hτ i))
  have hsumB := summable_norm_multipleEllipticGammaBackwardArgument
    (p := fun i => ellipticNome (τ i))
    (x := multipleEllipticGammaCoordinate z)
    (fun i => norm_ellipticNome_lt_one (hτ i))
  refine ⟨z, ?_, ?_⟩
  · have hprod := tprod_one_add_ne_zero_of_summable
      (f := fun n : ι → ℕ =>
        -multipleEllipticGammaForwardArgument (fun i => ellipticNome (τ i))
          (multipleEllipticGammaCoordinate z) n)
      (fun n => by simpa [multipleEllipticGammaForwardFactor] using hzF n)
      (by simpa only [norm_neg] using hsumF)
    simpa [multipleEllipticGammaForwardProduct,
      multipleEllipticGammaForwardFactor] using hprod
  · have hprod := tprod_one_add_ne_zero_of_summable
      (f := fun n : ι → ℕ =>
        -multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
          (multipleEllipticGammaCoordinate z) n)
      (fun n => by simpa [multipleEllipticGammaBackwardFactor] using hzB n)
      (by simpa only [norm_neg] using hsumB)
    simpa [multipleEllipticGammaBackwardProduct,
      multipleEllipticGammaBackwardFactor] using hprod

theorem multipleEllipticGammaForwardProduct_ne_zero
    {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaForwardProduct τ ≠ 0 := by
  obtain ⟨z, hz, _⟩ := exists_multipleEllipticGammaProducts_ne_zero hτ
  intro hzero
  exact hz (congrFun hzero z)

theorem multipleEllipticGammaBackwardProduct_ne_zero
    {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaBackwardProduct τ ≠ 0 := by
  obtain ⟨z, _, hz⟩ := exists_multipleEllipticGammaProducts_ne_zero hτ
  intro hzero
  exact hz (congrFun hzero z)

/-- The logarithmic derivative of one forward factor is the positive rational atom. -/
theorem logDeriv_multipleEllipticGammaForwardFactor
    (τ : ι → ℂ) (n : ι → ℕ) (z : ℂ) :
    logDeriv (multipleEllipticGammaForwardFactor τ n) z =
      2 * Real.pi * I *
        ellipticGammaLogAtom
          (multipleEllipticGammaForwardArgument (fun i => ellipticNome (τ i))
            (multipleEllipticGammaCoordinate z) n) := by
  let c : ℂ := ∏ i, ellipticNome (τ i) ^ (n i + 1)
  let X := multipleEllipticGammaCoordinate
  have hX0 : X z ≠ 0 := multipleEllipticGammaCoordinate_ne_zero z
  have hX := hasDerivAt_multipleEllipticGammaCoordinate z
  have harg : HasDerivAt (fun w => c / X w)
      (-(2 * Real.pi * I) * (c / X z)) z := by
    convert (hasDerivAt_const z c).div hX hX0 using 1
    dsimp [X]
    field_simp [hX0]
    ring
  have hfac : HasDerivAt (multipleEllipticGammaForwardFactor τ n)
      (2 * Real.pi * I * (c / X z)) z := by
    (convert (hasDerivAt_const z 1).sub harg using 1; ring)
  rw [logDeriv_apply, hfac.deriv]
  rw [multipleEllipticGammaForwardFactor,
    multipleEllipticGammaForwardArgument, ellipticGammaLogAtom]
  dsimp [c, X] at hfac ⊢
  field_simp [hX0]

/-- The logarithmic derivative of one backward factor is the negative rational atom. -/
theorem logDeriv_multipleEllipticGammaBackwardFactor
    (τ : ι → ℂ) (n : ι → ℕ) (z : ℂ) :
    logDeriv (multipleEllipticGammaBackwardFactor τ n) z =
      -(2 * Real.pi * I) *
        ellipticGammaLogAtom
          (multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
            (multipleEllipticGammaCoordinate z) n) := by
  let c : ℂ := ∏ i, ellipticNome (τ i) ^ n i
  let X := multipleEllipticGammaCoordinate
  have hX := hasDerivAt_multipleEllipticGammaCoordinate z
  have harg : HasDerivAt (fun w => c * X w)
      (2 * Real.pi * I * (c * X z)) z := by
    convert hX.const_mul c using 1
    ring
  have hfac : HasDerivAt (multipleEllipticGammaBackwardFactor τ n)
      (-(2 * Real.pi * I) * (c * X z)) z := by
    (convert (hasDerivAt_const z 1).sub harg using 1; ring)
  rw [logDeriv_apply, hfac.deriv]
  rw [multipleEllipticGammaBackwardFactor,
    multipleEllipticGammaBackwardArgument, ellipticGammaLogAtom]
  dsimp [c, X] at hfac ⊢
  field_simp

/-- The forward product logarithmic derivative is the convergent forward atom sum. -/
theorem logDeriv_multipleEllipticGammaForwardProduct
    {τ : ι → ℂ} {z : ℂ} (hτ : ∀ i, 0 < (τ i).im)
    (hz : multipleEllipticGammaForwardProduct τ z ≠ 0) :
    logDeriv (multipleEllipticGammaForwardProduct τ) z =
      2 * Real.pi * I *
        ∑' n : ι → ℕ, ellipticGammaLogAtom
          (multipleEllipticGammaForwardArgument (fun i => ellipticNome (τ i))
            (multipleEllipticGammaCoordinate z) n) := by
  have hfac : ∀ n : ι → ℕ, multipleEllipticGammaForwardFactor τ n z ≠ 0 := by
    intro n hn
    apply hz
    rw [multipleEllipticGammaForwardProduct]
    exact tprod_of_exists_eq_zero ⟨n, hn⟩
  have hsumArg := summable_norm_multipleEllipticGammaForwardArgument
    (p := fun i => ellipticNome (τ i))
    (x := multipleEllipticGammaCoordinate z)
    (fun i => norm_ellipticNome_lt_one (hτ i))
  have hsumAtom := summable_ellipticGammaLogAtom_of_summable_norm hsumArg
  have hsumLD : Summable (fun n : ι → ℕ =>
      logDeriv (multipleEllipticGammaForwardFactor τ n) z) := by
    convert hsumAtom.mul_left (2 * Real.pi * I) using 1
    ext n
    exact logDeriv_multipleEllipticGammaForwardFactor τ n z
  have hprod : MultipliableLocallyUniformlyOn
      (multipleEllipticGammaForwardFactor τ) Set.univ :=
    ⟨_, hasProdLocallyUniformlyOn_multipleEllipticGammaForwardFactor hτ⟩
  change logDeriv (fun x => ∏' n : ι → ℕ,
    multipleEllipticGammaForwardFactor τ n x) z = _
  rw [logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z) hfac
    (fun n => (differentiable_multipleEllipticGammaForwardFactor τ n).differentiableOn)
    hsumLD hprod hz]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  exact logDeriv_multipleEllipticGammaForwardFactor τ n z

/-- The backward product logarithmic derivative is the negative convergent backward atom sum. -/
theorem logDeriv_multipleEllipticGammaBackwardProduct
    {τ : ι → ℂ} {z : ℂ} (hτ : ∀ i, 0 < (τ i).im)
    (hz : multipleEllipticGammaBackwardProduct τ z ≠ 0) :
    logDeriv (multipleEllipticGammaBackwardProduct τ) z =
      -(2 * Real.pi * I) *
        ∑' n : ι → ℕ, ellipticGammaLogAtom
          (multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
            (multipleEllipticGammaCoordinate z) n) := by
  have hfac : ∀ n : ι → ℕ, multipleEllipticGammaBackwardFactor τ n z ≠ 0 := by
    intro n hn
    apply hz
    rw [multipleEllipticGammaBackwardProduct]
    exact tprod_of_exists_eq_zero ⟨n, hn⟩
  have hsumArg := summable_norm_multipleEllipticGammaBackwardArgument
    (p := fun i => ellipticNome (τ i))
    (x := multipleEllipticGammaCoordinate z)
    (fun i => norm_ellipticNome_lt_one (hτ i))
  have hsumAtom := summable_ellipticGammaLogAtom_of_summable_norm hsumArg
  have hsumLD : Summable (fun n : ι → ℕ =>
      logDeriv (multipleEllipticGammaBackwardFactor τ n) z) := by
    convert hsumAtom.mul_left (-(2 * Real.pi * I)) using 1
    ext n
    exact logDeriv_multipleEllipticGammaBackwardFactor τ n z
  have hprod : MultipliableLocallyUniformlyOn
      (multipleEllipticGammaBackwardFactor τ) Set.univ :=
    ⟨_, hasProdLocallyUniformlyOn_multipleEllipticGammaBackwardFactor hτ⟩
  change logDeriv (fun x => ∏' n : ι → ℕ,
    multipleEllipticGammaBackwardFactor τ n x) z = _
  rw [logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z) hfac
    (fun n => (differentiable_multipleEllipticGammaBackwardFactor τ n).differentiableOn)
    hsumLD hprod hz]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  exact logDeriv_multipleEllipticGammaBackwardFactor τ n z

/-- The genuine parity-dependent all-order multiple elliptic gamma product.  For even nome count
the backward product occurs in the denominator; for odd nome count it occurs in the numerator. -/
def multipleEllipticGammaProduct (τ : ι → ℂ) (z : ℂ) : ℂ :=
  if Even (Fintype.card ι) then
    multipleEllipticGammaForwardProduct τ z /
      multipleEllipticGammaBackwardProduct τ z
  else
    multipleEllipticGammaForwardProduct τ z *
      multipleEllipticGammaBackwardProduct τ z

theorem multipleEllipticGammaProduct_ne_zero
    {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaProduct τ ≠ 0 := by
  obtain ⟨z, hzF, hzB⟩ := exists_multipleEllipticGammaProducts_ne_zero hτ
  intro hzero
  have hz := congrFun hzero z
  by_cases hcard : Even (Fintype.card ι)
  · simp only [multipleEllipticGammaProduct, hcard, if_true] at hz
    exact (div_ne_zero hzF hzB) hz
  · simp only [multipleEllipticGammaProduct, hcard, if_false] at hz
    exact (mul_ne_zero hzF hzB) hz

/-- On its regular locus, the logarithmic derivative of the genuine parity-dependent product is
exactly the previously constructed all-order additive logarithmic kernel. -/
theorem logDeriv_multipleEllipticGammaProduct_eq_additiveKernel
    {τ : ι → ℂ} {z : ℂ} (hτ : ∀ i, 0 < (τ i).im)
    (hzF : multipleEllipticGammaForwardProduct τ z ≠ 0)
    (hzB : multipleEllipticGammaBackwardProduct τ z ≠ 0) :
    logDeriv (multipleEllipticGammaProduct τ) z =
      multipleEllipticGammaAdditiveLogKernel τ z := by
  have hsumF := summable_ellipticGammaLogAtom_of_summable_norm
    (summable_norm_multipleEllipticGammaForwardArgument
      (p := fun i => ellipticNome (τ i))
      (x := multipleEllipticGammaCoordinate z)
      (fun i => norm_ellipticNome_lt_one (hτ i)))
  have hsumB := summable_ellipticGammaLogAtom_of_summable_norm
    (summable_norm_multipleEllipticGammaBackwardArgument
      (p := fun i => ellipticNome (τ i))
      (x := multipleEllipticGammaCoordinate z)
      (fun i => norm_ellipticNome_lt_one (hτ i)))
  have hdF := (differentiable_multipleEllipticGammaForwardProduct hτ z)
  have hdB := (differentiable_multipleEllipticGammaBackwardProduct hτ z)
  rw [multipleEllipticGammaAdditiveLogKernel,
    multipleEllipticGammaLogKernel]
  simp_rw [multipleEllipticGammaLogSummand]
  rw [hsumF.tsum_add (hsumB.mul_left (multipleEllipticGammaLogSign ι)),
    tsum_mul_left]
  by_cases hcard : Even (Fintype.card ι)
  · change logDeriv (fun w => if Even (Fintype.card ι) then
        multipleEllipticGammaForwardProduct τ w /
          multipleEllipticGammaBackwardProduct τ w else
        multipleEllipticGammaForwardProduct τ w *
          multipleEllipticGammaBackwardProduct τ w) z = _
    simp only [hcard, if_true]
    rw [logDeriv_div z hzF hzB hdF hdB,
      logDeriv_multipleEllipticGammaForwardProduct hτ hzF,
      logDeriv_multipleEllipticGammaBackwardProduct hτ hzB]
    simp only [multipleEllipticGammaLogSign, neg_one_pow_eq_ite, hcard, if_true]
    ring
  · change logDeriv (fun w => if Even (Fintype.card ι) then
        multipleEllipticGammaForwardProduct τ w /
          multipleEllipticGammaBackwardProduct τ w else
        multipleEllipticGammaForwardProduct τ w *
          multipleEllipticGammaBackwardProduct τ w) z = _
    simp only [hcard, if_false]
    rw [logDeriv_mul z hzF hzB hdF hdB,
      logDeriv_multipleEllipticGammaForwardProduct hτ hzF,
      logDeriv_multipleEllipticGammaBackwardProduct hτ hzB]
    simp only [multipleEllipticGammaLogSign, neg_one_pow_eq_ite, hcard, if_false]
    ring

end

end GaloisForLFunctions
