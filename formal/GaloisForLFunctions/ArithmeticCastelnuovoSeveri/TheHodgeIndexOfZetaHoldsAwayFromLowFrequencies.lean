import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectOfZetaIsFiniteAtEveryDegree
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheDegreeFiltrationOfACurveIsItsWindowFiltration

/-!
# The Hodge index of `ζ` holds away from a finite low-frequency divisor

At every degree `a ≥ 0` there is an explicit finite set of frequencies — the pole `i/2` and the
grid `D_a = {j h(a) : |j| ≤ J(a)}` in `[−T(a), T(a)]` — such that Weil's form of `ζ` is nonnegative
on every `C²` test supported in `[−a, a]` whose transform vanishes on it
(`re_W_zeta_nonneg_of_lowGrid`). Unconditionally, the failure of the Hodge index at degree `a` is
confined to the low frequencies: a test that does not see `D_a` meets itself nonnegatively.

The mechanism.
* *Horizon.* A pole-free test with `Re W < 0` carries more than half its spectral mass below the
  archimedean horizon `T(a)` (`pi_mul_integral_lt_of_re_W_neg`).
* *Lipschitz sampling.* The transform of a test supported in `[−a, a]` is the inner product with a
  cut-off character, and `τ ↦` cut-off character is Lipschitz in `L²` with constant
  `√(2(a + 1)³)` (`norm_cutCharL2_sub_sq_le`). If the transform vanishes on a grid of step `h`, it
  is at most `√(2(a+1)³) h ‖f‖` on `[−T, T]`, so the low-frequency mass is at most
  `4T(a + 1)³h² ‖f‖²`, which the step `h(a) = 1/(2√(T(a)(a + 1)³) + 1)` makes `≤ ‖f‖² < π‖f‖²`.

Counting the conditions gives again a finite Hodge defect, `≤ #D_a + 1`
(`negIndex_zeroGram_zeta_le_lowGrid`). Over `𝔽_q` no finite divisor works: on the golden fake
curve beyond degree `log 5/2`, and on every off-line lattice beyond its Nyquist degree, every
finite set of frequencies is avoided by a test with `Re W < 0`
(`exists_neg_of_hodgeDefectAt_eq_top`, `goldenDatum_no_finite_divisor`). The archimedean place
turns the Hodge index of `ℤ` into a statement about finitely many low frequencies at each degree;
a curve has no such place, and its failure, when it fails, is spread over all frequencies.
-/

open Complex MeasureTheory Set Filter Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)
open scoped ComplexConjugate InnerProductSpace Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Lipschitz dependence of the cut-off character -/

theorem norm_cutChar_sub_sq_le (a τ τ' u : ℝ) :
    ‖cutChar a τ u - cutChar a τ' u‖ ^ 2 ≤
      (Icc (-(a + 1)) (a + 1)).indicator (fun _ => (τ - τ') ^ 2 * (a + 1) ^ 2) u := by
  by_cases hu : u ∈ Icc (-(a + 1)) (a + 1)
  · rw [indicator_of_mem hu]
    have hexpsplit : cexp (I * τ * u) =
        cexp (I * τ' * u) * cexp (I * (((τ - τ') * u : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hsplit : cutChar a τ u - cutChar a τ' u =
        (plateau a u : ℂ) * cexp (I * τ' * u) * (cexp (I * (((τ - τ') * u : ℝ) : ℂ)) - 1) := by
      simp only [cutChar]
      rw [hexpsplit]
      ring
    have hexp : ‖cexp (I * τ' * u)‖ = 1 := by
      rw [show I * (τ' : ℂ) * (u : ℂ) = ((τ' * u : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have hdiff := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (τ - τ') * u)
    have hpl := plateau_le_one a u
    have hpl0 := plateau_nonneg a u
    have hu' : |u| ≤ a + 1 := abs_le.mpr hu
    have hnorm : ‖cutChar a τ u - cutChar a τ' u‖ ≤ |τ - τ'| * (a + 1) := by
      rw [hsplit, norm_mul, norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hpl0]
      calc plateau a u * ‖cexp (I * (((τ - τ') * u : ℝ) : ℂ)) - 1‖
          ≤ 1 * ‖(τ - τ') * u‖ := mul_le_mul hpl hdiff (norm_nonneg _) zero_le_one
        _ = |τ - τ'| * |u| := by rw [one_mul, Real.norm_eq_abs, abs_mul]
        _ ≤ |τ - τ'| * (a + 1) := mul_le_mul_of_nonneg_left hu' (abs_nonneg _)
    calc ‖cutChar a τ u - cutChar a τ' u‖ ^ 2 ≤ (|τ - τ'| * (a + 1)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = (τ - τ') ^ 2 * (a + 1) ^ 2 := by rw [mul_pow, sq_abs]
  · rw [indicator_of_notMem hu]
    simp [cutChar, plateau_eq_zero hu]

/-- **The cut-off characters are Lipschitz in `L²`**:
`‖χ_τ − χ_{τ'}‖² ≤ 2(a + 1)³ (τ − τ')²`. -/
theorem norm_cutCharL2_sub_sq_le {a : ℝ} (ha : 0 ≤ a) (τ τ' : ℝ) :
    ‖cutCharL2 a τ - cutCharL2 a τ'‖ ^ 2 ≤ 2 * (a + 1) ^ 3 * (τ - τ') ^ 2 := by
  rw [cutCharL2, cutCharL2, ← MemLp.toLp_sub, norm_toLp_sq]
  have hint2 : Integrable ((Icc (-(a + 1)) (a + 1)).indicator
      fun _ => (τ - τ') ^ 2 * (a + 1) ^ 2) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp) enorm_ne_top)
  have hint1 : Integrable fun u => ‖(cutChar a τ - cutChar a τ') u‖ ^ 2 :=
    hint2.mono' (((continuous_cutChar a τ).sub (continuous_cutChar a τ')).norm.pow 2
      |>.aestronglyMeasurable)
      (Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (sq_nonneg _), Pi.sub_apply]
        exact norm_cutChar_sub_sq_le a τ τ' u)
  calc ∫ u, ‖(cutChar a τ - cutChar a τ') u‖ ^ 2
      ≤ ∫ u, (Icc (-(a + 1)) (a + 1)).indicator (fun _ => (τ - τ') ^ 2 * (a + 1) ^ 2) u :=
        integral_mono hint1 hint2 fun u => by
          rw [Pi.sub_apply]
          exact norm_cutChar_sub_sq_le a τ τ' u
    _ = 2 * (a + 1) ^ 3 * (τ - τ') ^ 2 := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
        Real.volume_real_Icc_of_le (by linarith)]
      ring

/-! ### The transform as an inner product, and Lipschitz sampling -/

theorem continuous_conj_comp {f : ℝ → ℂ} (hf : Continuous f) : Continuous fun u => conj (f u) :=
  continuous_conj.comp hf

theorem hasCompactSupport_conj_comp {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport fun u => conj (f u) :=
  hfc.comp_left (map_zero _)

/-- The `L²` class of `conj ∘ f`. -/
def testL2 {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_two (continuous_conj_comp hf) (hasCompactSupport_conj_comp hfc)).toLp fun u => conj (f u)

theorem norm_testL2_sq {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ‖testL2 hf hfc‖ ^ 2 = ∫ u, ‖f u‖ ^ 2 := by
  rw [testL2, norm_toLp_sq]
  simp only [Complex.norm_conj]

/-- For a test supported in `[−a, a]`, `h_f(τ) = ⟪conj f, χ_τ⟫`. -/
theorem paperFT_eq_inner_testL2 {a : ℝ} {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ Icc (-a) a) (τ : ℝ) :
    paperFT f τ = ⟪testL2 hf hfc, cutCharL2 a τ⟫_ℂ := by
  rw [testL2, cutCharL2, inner_toLp, paperFT]
  congr 1
  funext u
  rw [conj_conj, cutChar]
  by_cases hu : u ∈ Icc (-a) a
  · rw [plateau_eq_one hu]
    push_cast
    ring
  · rw [image_eq_zero_of_notMem_tsupport fun h => hu (hfs h)]
    ring

/-- **Lipschitz sampling**: `|h_f(τ) − h_f(τ')|² ≤ 2(a + 1)³(τ − τ')² ‖f‖²`. -/
theorem norm_paperFT_sub_sq_le {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Icc (-a) a) (τ τ' : ℝ) :
    ‖paperFT f τ - paperFT f τ'‖ ^ 2 ≤ 2 * (a + 1) ^ 3 * (τ - τ') ^ 2 * ∫ u, ‖f u‖ ^ 2 := by
  rw [paperFT_eq_inner_testL2 hf hfc hfs, paperFT_eq_inner_testL2 hf hfc hfs, ← inner_sub_right]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (testL2 hf hfc) (cutCharL2 a τ - cutCharL2 a τ')
  have h2 := norm_cutCharL2_sub_sq_le ha τ τ'
  have h3 := norm_testL2_sq hf hfc
  calc ‖⟪testL2 hf hfc, cutCharL2 a τ - cutCharL2 a τ'⟫_ℂ‖ ^ 2
      ≤ (‖testL2 hf hfc‖ * ‖cutCharL2 a τ - cutCharL2 a τ'‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ‖testL2 hf hfc‖ ^ 2 * ‖cutCharL2 a τ - cutCharL2 a τ'‖ ^ 2 := mul_pow _ _ _
    _ ≤ (∫ u, ‖f u‖ ^ 2) * (2 * (a + 1) ^ 3 * (τ - τ') ^ 2) := by
        rw [h3]
        exact mul_le_mul_of_nonneg_left h2 (integral_nonneg fun _ => sq_nonneg _)
    _ = 2 * (a + 1) ^ 3 * (τ - τ') ^ 2 * ∫ u, ‖f u‖ ^ 2 := by ring

/-! ### The low-frequency divisor -/

/-- The grid step `h = 1/(2√(T(a + 1)³) + 1)` for the band `[−T, T]` at aperture `a`. -/
def gridStepOf (T a : ℝ) : ℝ := 1 / (2 * Real.sqrt (T * (a + 1) ^ 3) + 1)

/-- The grid half-length `J = ⌈T/h⌉`. -/
def gridHalfOf (T a : ℝ) : ℕ := ⌈T / gridStepOf T a⌉₊

/-- The grid `{j : |j| ≤ J}`; its frequencies are `j h`. -/
def lowGridOf (T a : ℝ) : Finset ℤ := Finset.Icc (-(gridHalfOf T a : ℤ)) (gridHalfOf T a)

theorem gridStepOf_pos (T a : ℝ) : 0 < gridStepOf T a := by
  unfold gridStepOf
  positivity

theorem four_mul_gridStepOf_sq_le {T a : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a) :
    4 * T * (a + 1) ^ 3 * gridStepOf T a ^ 2 ≤ 1 := by
  set s := Real.sqrt (T * (a + 1) ^ 3) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = T * (a + 1) ^ 3 := Real.sq_sqrt (mul_nonneg hT (by positivity))
  have hpos : 0 < 2 * s + 1 := by linarith
  have hkey : 4 * T * (a + 1) ^ 3 * gridStepOf T a ^ 2 = (2 * s / (2 * s + 1)) ^ 2 := by
    rw [gridStepOf, ← hs, div_pow, div_pow]
    field_simp
    rw [hsq]
    ring
  rw [hkey]
  have h1 : 2 * s / (2 * s + 1) ≤ 1 := (div_le_one hpos).mpr (by linarith)
  have h0 : 0 ≤ 2 * s / (2 * s + 1) := div_nonneg (by linarith) hpos.le
  nlinarith

/-- Every frequency in `[−T, T]` lies within one step of a grid point. -/
theorem exists_lowGridOf_near {T a τ : ℝ} (hτ : τ ∈ Icc (-T) T) :
    ∃ j ∈ lowGridOf T a, |τ - j * gridStepOf T a| ≤ gridStepOf T a := by
  set h := gridStepOf T a
  have hh := gridStepOf_pos T a
  set j := ⌊τ / h⌋ with hj
  have hj1 : (j : ℝ) ≤ τ / h := Int.floor_le _
  have hj2 : τ / h < j + 1 := Int.lt_floor_add_one _
  have hJ : T / h ≤ (gridHalfOf T a : ℝ) := Nat.le_ceil _
  have hτh1 : τ / h ≤ T / h := div_le_div_of_nonneg_right hτ.2 hh.le
  have hτh2 : -T / h ≤ τ / h := div_le_div_of_nonneg_right hτ.1 hh.le
  refine ⟨j, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
  · have : (-(gridHalfOf T a : ℝ)) - 1 < j := by
      have : -T / h = -(T / h) := neg_div _ _
      linarith
    have h' : (-(gridHalfOf T a : ℤ) : ℝ) - 1 < (j : ℝ) := by push_cast; linarith
    have h'' : -(gridHalfOf T a : ℤ) - 1 < j := by exact_mod_cast h'
    omega
  · have h' : (j : ℝ) ≤ ((gridHalfOf T a : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h'
  · have e1 : (j : ℝ) * h ≤ τ := by
      have := mul_le_mul_of_nonneg_right hj1 hh.le
      rwa [div_mul_cancel₀ _ hh.ne'] at this
    have e2 : τ < (j : ℝ) * h + h := by
      have := mul_lt_mul_of_pos_right hj2 hh
      rwa [div_mul_cancel₀ _ hh.ne', add_mul, one_mul] at this
    rw [abs_le]
    constructor <;> linarith

/-- **A transform vanishing on the grid has small band mass**: if `f` is supported in `[−a, a]` and
`h_f(j h) = 0` for `|j| ≤ J`, then `∫_{−T}^{T} |h_f|² ≤ ‖f‖²`. -/
theorem integral_band_le_of_lowGridOf {T a : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hgrid : ∀ j ∈ lowGridOf T a, paperFT f (((j : ℝ) * gridStepOf T a : ℝ) : ℂ) = 0) :
    ∫ τ in (-T)..T, ‖paperFT f τ‖ ^ 2 ≤ ∫ u, ‖f u‖ ^ 2 := by
  set h := gridStepOf T a with hhdef
  set A := ∫ u, ‖f u‖ ^ 2 with hA
  have hA0 : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hbound : ∀ τ ∈ Icc (-T) T, ‖paperFT f τ‖ ^ 2 ≤ 2 * (a + 1) ^ 3 * h ^ 2 * A := by
    intro τ hτ
    obtain ⟨j, hj, hjτ⟩ := exists_lowGridOf_near (a := a) hτ
    have hlip := norm_paperFT_sub_sq_le ha hf hfc hfs τ ((j : ℝ) * h)
    rw [hgrid j hj, sub_zero] at hlip
    have hsq : (τ - j * h) ^ 2 ≤ h ^ 2 := by
      rw [← sq_abs (τ - j * h)]
      exact pow_le_pow_left₀ (abs_nonneg _) hjτ 2
    calc ‖paperFT f τ‖ ^ 2 ≤ 2 * (a + 1) ^ 3 * (τ - j * h) ^ 2 * A := hlip
      _ ≤ 2 * (a + 1) ^ 3 * h ^ 2 * A := by gcongr
  have hcont : Continuous fun τ : ℝ => ‖paperFT f τ‖ ^ 2 :=
    (RHTower.WeilOneSided.continuous_paperFT_real_arg
      (hf.integrable_of_hasCompactSupport hfc)).norm.pow 2
  have hint : ∫ τ in (-T)..T, ‖paperFT f τ‖ ^ 2 ≤ 2 * T * (2 * (a + 1) ^ 3 * h ^ 2 * A) := by
    calc ∫ τ in (-T)..T, ‖paperFT f τ‖ ^ 2 ≤ ∫ _τ in (-T)..T, 2 * (a + 1) ^ 3 * h ^ 2 * A :=
          intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _)
            intervalIntegrable_const hbound
      _ = 2 * T * (2 * (a + 1) ^ 3 * h ^ 2 * A) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hstep := four_mul_gridStepOf_sq_le hT ha
  rw [← hhdef] at hstep
  have h1 : 2 * T * (2 * (a + 1) ^ 3 * h ^ 2 * A) ≤ A := by
    have := mul_le_mul_of_nonneg_right hstep hA0
    linarith
  linarith

/-- The grid step at the archimedean horizon, `h(a) = gridStepOf T(a) a`. -/
def gridStep (a : ℝ) : ℝ := gridStepOf (horizonFreq a) a

/-- The low-frequency grid at the archimedean horizon; its frequencies are `j h(a)`. -/
def lowGrid (a : ℝ) : Finset ℤ := lowGridOf (horizonFreq a) a

/-- **The Hodge index of `ζ` holds away from the low-frequency divisor.** If `f ∈ C²` is supported
in `[−a, a]`, `a ≥ 0`, and its transform vanishes at the pole `i/2` and at the grid frequencies
`j h(a)`, `|j| ≤ J(a)`, then `Re W_ζ(f, f) ≥ 0`. -/
theorem re_W_zeta_nonneg_of_lowGrid {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hgrid : ∀ j ∈ lowGrid a, paperFT f (((j : ℝ) * gridStep a : ℝ) : ℂ) = 0) :
    0 ≤ (zetaZeroConfig.W f f).re := by
  by_contra hneg
  push Not at hneg
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hconc := pi_mul_integral_lt_of_re_W_neg hf hfs hp hneg
  have hband := integral_band_le_of_lowGridOf (horizonFreq_nonneg a) ha hf.continuous hfc hfs hgrid
  have hA0 : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hπ : 1 ≤ π := by linarith [Real.pi_gt_three]
  nlinarith

/-- **The count again.** The pole and the `2J(a) + 1` grid frequencies are linear conditions on
the weights, so the Hodge defect of `ζ` at degree `a` is at most `#D_a + 1 = 2J(a) + 2`. -/
theorem negIndex_zeroGram_zeta_le_lowGrid {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (f : Fin n → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i) ∧ tsupport (f i) ⊆ Icc (-a) a) :
    hermNegIndex (zeroGram zetaZeroConfig f) ≤ (lowGrid a).card + 1 := by
  have hfd : ∀ i, ContDiff ℝ 2 (f i) := fun i => (hf i).1
  have hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a := fun i => (hf i).2
  have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hfs i)
  have hfcont : ∀ i, Continuous (f i) := fun i => (hfd i).continuous
  let φ : Option (lowGrid a) → (Fin n → ℂ) →ₗ[ℂ] ℂ := fun k =>
    match k with
    | none => evalFunctional f (I / 2)
    | some j => evalFunctional f ((((j : ℤ) : ℝ) * gridStep a : ℝ) : ℂ)
  have hle := negIndex_le_card_of_nonneg_on_ker (zeroGram zetaZeroConfig f) φ fun x hx => by
    rw [hermQuad_zeroGram_of_tempered zetaZeroConfig
      GaloisForLFunctions.SquareRootThreshold.temperedConfig_zetaZeroConfig f hfd hfc x]
    have hzero : ∀ z : ℂ, evalFunctional f z x = 0 → paperFT (∑ i, conj (x i) • f i) z = 0 :=
      fun z hz => by
        rw [evalFunctional_eq f hfcont hfc z x] at hz
        exact (map_eq_zero (starRingEnd ℂ)).mp hz
    refine re_W_zeta_nonneg_of_lowGrid ha (contDiff_sum_smul f hfd _)
      (tsupport_sum_smul_subset f hfs _) (hzero _ (hx none)) fun j hj => ?_
    exact hzero _ (hx (some ⟨j, hj⟩))
  simpa [Fintype.card_option] using hle

/-! ### Over `𝔽_q` no finite divisor suffices -/

/-- If the Hodge defect is infinite at degree `a`, every finite set of frequencies is avoided by
an aperture-`a` test with `Re W < 0`: no finite divisor restores the Hodge index. -/
theorem exists_neg_of_hodgeDefectAt_eq_top (Z : ZeroConfig) (hZ : TemperedConfig Z) {a : ℝ}
    (htop : hodgeDefectAt Z a = ⊤) (S : Finset ℂ) :
    ∃ F : ℝ → ℂ, ContDiff ℝ 2 F ∧ tsupport F ⊆ Icc (-a) a ∧ (∀ z ∈ S, paperFT F z = 0) ∧
      (Z.W F F).re < 0 := by
  by_contra hno
  push Not at hno
  have hle : hodgeDefectAt Z a ≤ (S.card : ℕ∞) := by
    refine iSup₂_le fun n f => iSup_le fun hf => ?_
    have hfd : ∀ i, ContDiff ℝ 2 (f i) := fun i => (hf i).1
    have hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a := fun i => (hf i).2
    have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hfs i)
    have hfcont : ∀ i, Continuous (f i) := fun i => (hfd i).continuous
    have h := negIndex_le_card_of_nonneg_on_ker (zeroGram Z f)
      (fun z : S => evalFunctional f (z : ℂ)) fun x hx => by
        rw [hermQuad_zeroGram_of_tempered Z hZ f hfd hfc x]
        refine hno _ (contDiff_sum_smul f hfd _) (tsupport_sum_smul_subset f hfs _) fun z hz => ?_
        have h0 := hx ⟨z, hz⟩
        rw [evalFunctional_eq f hfcont hfc z x] at h0
        exact (map_eq_zero (starRingEnd ℂ)).mp h0
    rw [Fintype.card_coe] at h
    exact_mod_cast h
  rw [htop] at hle
  exact absurd hle (by simp)

/-- **The golden fake curve has no finite divisor.** Beyond degree `log 5/2`, every finite set of
frequencies is avoided by a test whose Weil form is negative. -/
theorem goldenDatum_no_finite_divisor {a : ℝ} (ha : Real.log 5 / 2 < a) (S : Finset ℂ) :
    ∃ F : ℝ → ℂ, ContDiff ℝ 2 F ∧ tsupport F ⊆ Icc (-a) a ∧ (∀ z ∈ S, paperFT F z = 0) ∧
      ((goldenDatum.curveConfig goldenDatum_strip).W F F).re < 0 := by
  refine exists_neg_of_hodgeDefectAt_eq_top _
    (goldenDatum.temperedConfig_curveConfig goldenDatum_strip) ?_ S
  rw [goldenDatum_hodgeDefectAt, if_neg (not_le.mpr ha)]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
