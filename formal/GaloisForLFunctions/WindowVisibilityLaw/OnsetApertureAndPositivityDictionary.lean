import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfAnIsolatedPair
import GaloisForLFunctions.SquareRootThreshold.TheContactApertureOfTheGroundEnergyPath
import GaloisForLFunctions.SquareRootThreshold.PositivityCertifiesIsolableTilts
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalThresholdOfAWindow
import GaloisForLFunctions.ArithmeticIncidencePositivity.AnExplicitLargerApertureRetainsAWeilFloor

/-!
# The Onset Aperture of Window Negativity and Its Route Dictionary

For any zero configuration `Z`, let `WindowPositiveAt Z a` assert that `0 ≤ Re W_Z(f, f)` for
every `C²` test `f : ℝ → ℂ` with `tsupport f ⊆ [−a, a]`, and define the **onset aperture**
`onsetAperture Z : EReal` as the supremum of all nonnegative half-widths `a` with
`WindowPositiveAt Z a`.

* **Closed-interval law (`windowPositiveAt_of_forall_lt`, `windowPositiveAt_iff_le_onsetAperture`,
  `exists_re_W_neg_iff_onsetAperture_lt`).** On any tempered configuration `Z`, dilating `f` by
  `r_n = 1 + 1/(n + 1)` shrinks its support strictly inside `(−a, a)` while bounding
  `‖h_{f_n}(z)‖ ≤ C / (1 + |Re z|)²` uniformly on `|Im z| ≤ ½`. Dominated convergence makes the set
  of positive apertures right-closed, so `WindowPositiveAt Z a ↔ (a : EReal) ≤ onsetAperture Z`
  (**seeing V1** and **hiding V2** are exact contrapositives on `[0, ∞)`), and simultaneously
  `hodgeDefectAt Z a = 0 ↔ (a : EReal) ≤ onsetAperture Z`.
* **Critical-line characterization (`onsetAperture_eq_top_iff_onLine`).** On any tempered
  configuration, `onsetAperture Z = ⊤` iff `∀ ρ ∈ Z.carrier, ρ.re = 1 / 2`.
* **Exact `ζ`, `P1`, and `AHD` dictionary (`riemannHypothesis_iff_onsetAperture_zeta_eq_top`,
  `onsetAperture_zeta_eq_contact_of_not_rh`, `zetaWindowPositive_contact_of_not_rh`,
  `windowThreshold_eq_top_iff_le_onsetAperture`, `enlargedWeilFloorAperture_le_onsetAperture_zeta`).**
  For `ζ`, `WindowPositiveAt zetaZeroConfig a ↔ ZetaWindowPositive a` (`a ≥ 0`); RH holds iff
  `onsetAperture zetaZeroConfig = ⊤`; off RH, `onsetAperture zetaZeroConfig = zetaContactAperture`
  and `ZetaWindowPositive zetaContactAperture` holds at the contact point itself; unconditionally
  `enlargedWeilFloorAperture ≤ onsetAperture zetaZeroConfig`; and for `A ≥ 0`,
  `AHD.windowThreshold A = ⊤ ↔ ((A / 2 : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.WindowVisibilityLaw

open Zeta23 _root_.RHTower
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

/-! ### 1. Window positivity and the canonical onset aperture -/

/-- Window positivity of `Z` at half-width `a`: `0 ≤ Re W_Z(f, f)` for every `C²` test supported in
`[−a, a]`. -/
def WindowPositiveAt (Z : ZeroConfig) (a : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re

/-- The nonnegative half-widths at which `Z` is window-positive, embedded in `EReal`. -/
def positiveApertureSet (Z : ZeroConfig) : Set EReal :=
  {x : EReal | ∃ a : ℝ, 0 ≤ a ∧ x = (a : EReal) ∧ WindowPositiveAt Z a}

/-- **The onset aperture `a*(Z)`**: the supremum in `[0, ∞]` of all half-widths at which `Z` is
window-positive. -/
def onsetAperture (Z : ZeroConfig) : EReal :=
  sSup (positiveApertureSet Z)

theorem windowPositiveAt_antitone {Z : ZeroConfig} {a b : ℝ} (hab : a ≤ b)
    (hb : WindowPositiveAt Z b) : WindowPositiveAt Z a :=
  fun f hf hfs => hb f hf (hfs.trans (Icc_subset_Icc (neg_le_neg hab) hab))

/-- At half-width `0`, every continuous test supported in `[0, 0]` vanishes everywhere since `{0}`
has empty interior. -/
theorem eq_zero_of_tsupport_subset_singleton_zero {f : ℝ → ℂ} (hf : Continuous f)
    (hfs : tsupport f ⊆ Icc (-0) 0) : f = 0 := by
  funext u
  by_cases hu : u = 0
  · subst hu
    have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hval : ∀ n : ℕ, f ((1 : ℝ) / ((n : ℝ) + 1)) = 0 := fun n =>
      image_eq_zero_of_notMem_tsupport fun hm => by
        have h := hfs hm
        rw [neg_zero, mem_Icc] at h
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hlim := (hf.tendsto 0).comp hseq
    simp only [Function.comp_def, hval, tendsto_const_nhds_iff] at hlim
    exact hlim.symm
  · exact image_eq_zero_of_notMem_tsupport fun hm => hu (by
      have h := hfs hm
      rw [neg_zero, mem_Icc] at h
      linarith)

theorem windowPositiveAt_zero (Z : ZeroConfig) : WindowPositiveAt Z 0 := by
  intro f hf hfs
  rw [eq_zero_of_tsupport_subset_singleton_zero hf.continuous hfs]
  have h0 : paperFT (0 : ℝ → ℂ) = 0 := by
    funext z; simp [paperFT_def]
  simp [ZeroConfig.W, ZeroConfig.Wsummand, h0]

theorem windowPositiveAt_of_neg (Z : ZeroConfig) {a : ℝ} (ha : a < 0) : WindowPositiveAt Z a := by
  intro f hf hfs
  have hempty : Icc (-a) a = ∅ := Icc_eq_empty (by linarith)
  have hf0 : f = 0 := by
    funext u
    exact image_eq_zero_of_notMem_tsupport fun hm => by
      have := hfs hm
      rw [hempty] at this
      exact this
  rw [hf0]
  have h0 : paperFT (0 : ℝ → ℂ) = 0 := by funext z; simp [paperFT_def]
  simp [ZeroConfig.W, ZeroConfig.Wsummand, h0]

theorem zero_mem_positiveApertureSet (Z : ZeroConfig) : (0 : EReal) ∈ positiveApertureSet Z :=
  ⟨0, le_rfl, EReal.coe_zero.symm, windowPositiveAt_zero Z⟩

theorem zero_le_onsetAperture (Z : ZeroConfig) : (0 : EReal) ≤ onsetAperture Z :=
  le_sSup (zero_mem_positiveApertureSet Z)

theorem le_onsetAperture_of_windowPositiveAt {Z : ZeroConfig} {a : ℝ} (ha : 0 ≤ a)
    (hpos : WindowPositiveAt Z a) : (a : EReal) ≤ onsetAperture Z :=
  le_sSup ⟨a, ha, rfl, hpos⟩

/-! ### 2. Dilation left-continuity and the closed-interval law -/

/-- Second derivative of a linear dilation `u ↦ f(r * u)`. -/
private theorem deriv_deriv_comp_mul_left {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (r u : ℝ) :
    deriv (deriv (fun x => f (r * x))) u = (r : ℂ) ^ 2 * deriv (deriv f) (r * u) := by
  have hd1 : ∀ x, HasDerivAt (fun y => f (r * y)) ((r : ℂ) * deriv f (r * x)) x := fun x => by
    have hfx : DifferentiableAt ℝ f (r * x) :=
      (hf.differentiable (by norm_num)).differentiableAt
    have hmul : HasDerivAt (fun y : ℝ => r * y) r x := by
      simpa using (hasDerivAt_id x).const_mul r
    simpa [real_smul, mul_comm] using hfx.hasDerivAt.scomp x hmul
  have heq1 : deriv (fun y => f (r * y)) = fun x => (r : ℂ) * deriv f (r * x) :=
    funext fun x => (hd1 x).deriv
  rw [heq1]
  have hdf : ContDiff ℝ 1 (deriv f) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num] at hf
    exact (contDiff_succ_iff_deriv.mp hf).2.2
  have hd2 : HasDerivAt (fun x => (r : ℂ) * deriv f (r * x))
      ((r : ℂ) * ((r : ℂ) * deriv (deriv f) (r * u))) u := by
    have hfx : DifferentiableAt ℝ (deriv f) (r * u) :=
      (hdf.differentiable le_rfl).differentiableAt
    have hmul : HasDerivAt (fun y : ℝ => r * y) r u := by
      simpa using (hasDerivAt_id u).const_mul r
    have hcomp : HasDerivAt (fun x => deriv f (r * x)) ((r : ℂ) * deriv (deriv f) (r * u)) u := by
      simpa [real_smul, mul_comm] using hfx.hasDerivAt.scomp u hmul
    exact hcomp.const_mul (r : ℂ)
  rw [hd2.deriv]
  ring

/-- Uniform strip decay of `paperFT (fun u => f (r * u))` for dilation factors `r ∈ [1, 2]`. -/
private theorem norm_paperFT_dilate_le_decay {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {a : ℝ} (ha : 0 ≤ a)
    (hfs : tsupport f ⊆ Icc (-a) a) {r : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (z : ℂ)
    (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (fun u => f (r * u)) z‖ ≤
      Real.exp a * (8 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) / (1 + |z.re|) ^ 2 := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  set g : ℝ → ℂ := fun u => f (r * u)
  have hg : ContDiff ℝ 2 g := hf.comp (contDiff_const.mul contDiff_id)
  have hsupp : ∀ u, g u ≠ 0 → |u| ≤ a := fun u hu => by
    have hmem : r * u ∈ Icc (-a) a := hfs (subset_tsupport f hu)
    rw [mem_Icc] at hmem
    rw [abs_le]
    constructor <;> nlinarith
  have hdec := RHTower.norm_paperFT_le_decay hg hsupp z
  have hexp : Real.exp (|z.im| * a) ≤ Real.exp a :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.im])
  have hint1 : ∫ u, ‖g u‖ ≤ ∫ u, ‖f u‖ := by
    have heq : (∫ u, ‖f (r * u)‖) = r⁻¹ * ∫ u, ‖f u‖ := by
      rw [Measure.integral_comp_mul_left (fun u => ‖f u‖) r, abs_of_pos (inv_pos.mpr hr0),
        smul_eq_mul]
    rw [heq]
    have hI0 : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun _ => norm_nonneg _
    have hinv : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
    nlinarith
  have hint2 : ∫ u, ‖deriv (deriv g) u‖ ≤ 2 * ∫ u, ‖deriv (deriv f) u‖ := by
    have hpt : (fun u => ‖deriv (deriv g) u‖) = fun u => r ^ 2 * ‖deriv (deriv f) (r * u)‖ := by
      funext u
      rw [deriv_deriv_comp_mul_left hf r u, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr0]
    rw [hpt, integral_const_mul, Measure.integral_comp_mul_left (fun u => ‖deriv (deriv f) u‖) r,
      abs_of_pos (inv_pos.mpr hr0), smul_eq_mul]
    have hI0 : 0 ≤ ∫ u, ‖deriv (deriv f) u‖ := integral_nonneg fun _ => norm_nonneg _
    have hrr : r ^ 2 * r⁻¹ = r := by field_simp [hr0.ne']
    nlinarith
  have hnorm_sum : 4 * ((∫ u, ‖g u‖) + ∫ u, ‖deriv (deriv g) u‖) ≤
      8 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) := by
    have hI1 : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun _ => norm_nonneg _
    have hI2 : 0 ≤ ∫ u, ‖deriv (deriv f) u‖ := integral_nonneg fun _ => norm_nonneg _
    linarith
  refine hdec.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  exact mul_le_mul hexp hnorm_sum (by positivity) (Real.exp_pos _).le

/-- Pointwise convergence of `paperFT` under dilation `r_n = 1 + 1/(n + 1) → 1`. -/
private theorem tendsto_paperFT_dilate {f : ℝ → ℂ} (hf : Continuous f) {a : ℝ} (ha : 0 ≤ a)
    (hfs : tsupport f ⊆ Icc (-a) a) (z : ℂ) :
    Tendsto (fun n : ℕ => paperFT (fun u => f ((1 + 1 / ((n : ℝ) + 1)) * u)) z)
      atTop (𝓝 (paperFT f z)) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ u, ‖f u‖ ≤ C := by
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := -a) (b := a)).bddAbove_image hf.norm.continuousOn
    refine ⟨max B 0, fun u => ?_⟩
    by_cases hu : u ∈ Icc (-a) a
    · exact (hB ⟨u, hu, rfl⟩).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport fun hm => hu (hfs hm), norm_zero]
      exact le_max_right _ _
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  set r : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  have hr1 : ∀ n, 1 ≤ r n := fun n => by dsimp [r]; positivity
  set bound : ℝ → ℝ := (Icc (-a) a).indicator fun _ => C * Real.exp (|z.im| * a)
  have hbound_int : Integrable bound :=
    (integrableOn_const (μ := volume) measure_Icc_lt_top.ne (by simp)).integrable_indicator
      measurableSet_Icc
  simp only [paperFT_def]
  refine tendsto_integral_of_dominated_convergence bound ?_ hbound_int ?_ ?_
  · intro n
    exact ((hf.comp (continuous_const.mul continuous_id)).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  · intro n
    refine Eventually.of_forall fun u => ?_
    by_cases hu : u ∈ Icc (-a) a
    · rw [Set.indicator_of_mem hu, norm_mul]
      have hua : |u| ≤ a := abs_le.mpr hu
      have hexp : ‖cexp (I * z * (u : ℂ))‖ ≤ Real.exp (|z.im| * a) := by
        rw [Complex.norm_exp]
        have him : (I * z * (u : ℂ)).re = -z.im * u := by
          simp [Complex.mul_re]
        rw [him]
        apply Real.exp_le_exp.mpr
        calc -z.im * u ≤ |-z.im * u| := le_abs_self _
          _ = |z.im| * |u| := by rw [abs_mul, abs_neg]
          _ ≤ |z.im| * a := mul_le_mul_of_nonneg_left hua (abs_nonneg _)
      exact mul_le_mul (hC _) hexp (norm_nonneg _) hC0
    · rw [Set.indicator_of_notMem hu]
      have hfu : f (r n * u) = 0 := image_eq_zero_of_notMem_tsupport fun hm => hu (by
        have h := hfs hm
        rw [mem_Icc] at h ⊢
        have := hr1 n
        rcases lt_or_ge u 0 with hneg | hpos
        · exact ⟨by nlinarith, by linarith⟩
        · exact ⟨by linarith, by nlinarith⟩)
      simp [hfu]
  · refine Eventually.of_forall fun u => ?_
    have hrt : Tendsto (fun n : ℕ => r n * u) atTop (𝓝 u) := by
      have h0 : Tendsto r atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at h0
      simpa using h0.mul_const u
    exact ((hf.tendsto u).comp hrt).mul_const _

/-- **Dilation left-continuity of window positivity.** On a tempered configuration `Z`, if
`WindowPositiveAt Z a'` holds for every `0 ≤ a' < a` (`0 < a`), then `WindowPositiveAt Z a` holds
at the endpoint `a` itself. -/
theorem windowPositiveAt_of_forall_lt {Z : ZeroConfig} (hZ : TemperedConfig Z) {a : ℝ}
    (ha : 0 < a) (h : ∀ a' : ℝ, 0 ≤ a' → a' < a → WindowPositiveAt Z a') :
    WindowPositiveAt Z a := by
  intro f hf hfs
  set r : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  set fn : ℕ → ℝ → ℂ := fun n u => f (r n * u)
  have hr1 : ∀ n, 1 < r n := fun n => by
    dsimp [r]; linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
  have hr2 : ∀ n, r n ≤ 2 := fun n => by
    dsimp [r]
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
      div_le_one_of_le₀ (by linarith [Nat.cast_nonneg n]) (by positivity)
    linarith
  have hfn_cd : ∀ n, ContDiff ℝ 2 (fn n) := fun n =>
    hf.comp (contDiff_const.mul contDiff_id)
  have hfn_supp : ∀ n, tsupport (fn n) ⊆ Icc (-(a / r n)) (a / r n) := fun n => by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    have hr0 : 0 < r n := zero_lt_one.trans (hr1 n)
    have hm : r n * u ∈ Icc (-a) a := hfs (subset_tsupport f (Function.mem_support.mp hu))
    rw [mem_Icc] at hm ⊢
    exact ⟨(neg_div a (r n)) ▸ (le_div_iff₀ hr0).mpr (by linarith [hm.1]),
      (div_le_iff₀ hr0).mpr (by linarith [hm.2])⟩
  have hpos_n : ∀ n, 0 ≤ (Z.W (fn n) (fn n)).re := fun n => by
    have hr0 : 0 < r n := zero_lt_one.trans (hr1 n)
    have hlt : a / r n < a := div_lt_self ha (hr1 n)
    exact h (a / r n) (div_nonneg ha.le hr0.le) hlt (fn n) (hfn_cd n) (hfn_supp n)
  set C := Real.exp a * (8 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num)
      (add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)))
  set maj : Z.carrier → ℝ := fun τ =>
    4 / 3 * C ^ 2 * ((Z.mult τ : ℝ) / (1 + Complex.normSq (gammaOf τ)))
  have hmaj_sum : Summable maj := hZ.mul_left (4 / 3 * C ^ 2)
  have hbound : ∀ n (τ : Z.carrier), ‖Z.Wsummand (fn n) (fn n) τ‖ ≤ maj τ := by
    intro n τ
    have him := abs_im_gammaOf_le Z τ
    have him_conj : |(conj (gammaOf τ)).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact him
    have hb1 := norm_paperFT_dilate_le_decay hf ha.le hfs (hr1 n).le (hr2 n) (gammaOf τ) him
    have hb2 := norm_paperFT_dilate_le_decay hf ha.le hfs (hr1 n).le (hr2 n) (conj (gammaOf τ)) him_conj
    have hb2' : ‖paperFT (fn n) (conj (gammaOf τ))‖ ≤ C :=
      hb2.trans (div_le_self hC0 (one_le_pow₀ (by linarith [abs_nonneg (conj (gammaOf τ)).re])))
    have hden : 1 / (1 + |(gammaOf τ).re|) ^ 2 ≤ (4 / 3) / (1 + Complex.normSq (gammaOf τ)) := by
      rw [Complex.normSq_apply, div_le_div_iff₀ (by positivity)
        (by nlinarith [mul_self_nonneg (gammaOf τ).re, mul_self_nonneg (gammaOf τ).im])]
      have h1 : (gammaOf τ).im * (gammaOf τ).im ≤ 1 / 4 := by nlinarith [abs_le.mp him]
      nlinarith [abs_nonneg (gammaOf τ).re, sq_abs (gammaOf τ).re]
    have hb1' : ‖paperFT (fn n) (gammaOf τ)‖ ≤ C * ((4 / 3) / (1 + Complex.normSq (gammaOf τ))) := by
      refine hb1.trans ?_
      rw [div_eq_mul_one_div C]
      exact mul_le_mul_of_nonneg_left hden hC0
    rw [ZeroConfig.Wsummand, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_conj]
    have hm0 : (0 : ℝ) ≤ Z.mult τ := Nat.cast_nonneg _
    have hN : 0 < 1 + Complex.normSq (gammaOf τ) := by
      linarith [Complex.normSq_nonneg (gammaOf τ)]
    calc (Z.mult τ : ℝ) * ‖paperFT (fn n) (gammaOf τ)‖ * ‖paperFT (fn n) (conj (gammaOf τ))‖
        ≤ (Z.mult τ : ℝ) * (C * ((4 / 3) / (1 + Complex.normSq (gammaOf τ)))) * C :=
          mul_le_mul (mul_le_mul_of_nonneg_left hb1' hm0) hb2' (norm_nonneg _)
            (mul_nonneg hm0 (mul_nonneg hC0 (div_nonneg (by norm_num) hN.le)))
      _ = maj τ := by dsimp [maj]; ring
  have hpt : ∀ τ : Z.carrier,
      Tendsto (fun n => Z.Wsummand (fn n) (fn n) τ) atTop (𝓝 (Z.Wsummand f f τ)) := by
    intro τ
    unfold ZeroConfig.Wsummand
    exact ((tendsto_paperFT_dilate hf.continuous ha.le hfs (gammaOf τ)).mul_const (Z.mult τ : ℂ) |>.congr
      fun n => mul_comm _ _).mul
      (Complex.continuous_conj.continuousAt.tendsto.comp
        (tendsto_paperFT_dilate hf.continuous ha.le hfs (conj (gammaOf τ))))
  have hW_lim : Tendsto (fun n => Z.W (fn n) (fn n)) atTop (𝓝 (Z.W f f)) :=
    tendsto_tsum_of_dominated_convergence hmaj_sum hpt (Eventually.of_forall hbound)
  exact ge_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp hW_lim) hpos_n

/-- **Exact closed-interval law (V1 seeing & V2 hiding).** For any tempered configuration `Z` and
`a ≥ 0`, `WindowPositiveAt Z a` holds iff `(a : EReal) ≤ onsetAperture Z`. -/
theorem windowPositiveAt_iff_le_onsetAperture {Z : ZeroConfig} (hZ : TemperedConfig Z) {a : ℝ}
    (ha : 0 ≤ a) : WindowPositiveAt Z a ↔ (a : EReal) ≤ onsetAperture Z := by
  constructor
  · exact le_onsetAperture_of_windowPositiveAt ha
  · intro hle
    rcases eq_or_lt_of_le ha with rfl | hapos
    · exact windowPositiveAt_zero Z
    · refine windowPositiveAt_of_forall_lt hZ hapos fun a' _ ha'lt => ?_
      have hlt : (a' : EReal) < onsetAperture Z :=
        (EReal.coe_lt_coe_iff.mpr ha'lt).trans_le hle
      obtain ⟨_, ⟨b, _, rfl, hbpos⟩, hab⟩ := lt_sSup_iff.mp hlt
      exact windowPositiveAt_antitone (EReal.coe_lt_coe_iff.mp hab).le hbpos

/-- **Strict visibility equivalence (V1 seeing).** On a tempered configuration `Z` at `a ≥ 0`, some
`C²` test supported in `[−a, a]` has `Re W_Z(f, f) < 0` iff `onsetAperture Z < (a : EReal)`. -/
theorem exists_re_W_neg_iff_onsetAperture_lt {Z : ZeroConfig} (hZ : TemperedConfig Z) {a : ℝ}
    (ha : 0 ≤ a) :
    (∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ (Z.W f f).re < 0) ↔
      onsetAperture Z < (a : EReal) := by
  rw [← not_le, ← windowPositiveAt_iff_le_onsetAperture hZ ha]
  unfold WindowPositiveAt
  push_neg
  rfl

/-- **Hodge-defect filtration dictionary.** On a tempered configuration `Z` at `a ≥ 0`,
`hodgeDefectAt Z a = 0` iff `(a : EReal) ≤ onsetAperture Z`. -/
theorem hodgeDefectAt_eq_zero_iff_le_onsetAperture {Z : ZeroConfig} (hZ : TemperedConfig Z) {a : ℝ}
    (ha : 0 ≤ a) : hodgeDefectAt Z a = 0 ↔ (a : EReal) ≤ onsetAperture Z :=
  (hodgeDefectAt_eq_zero_iff Z hZ a).trans (windowPositiveAt_iff_le_onsetAperture hZ ha)

/-! ### 3. Critical-line characterization -/

/-- **Infinite onset aperture is criticality.** On any tempered configuration `Z`,
`onsetAperture Z = ⊤` iff every zero of `Z` lies on `Re ρ = 1 / 2`. -/
theorem onsetAperture_eq_top_iff_onLine {Z : ZeroConfig} (hZ : TemperedConfig Z) :
    onsetAperture Z = ⊤ ↔ ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  constructor
  · intro htop ρ hρ
    have hall : ∀ a : ℝ, hodgeDefectAt Z a = 0 := fun a => by
      rcases lt_or_ge a 0 with ha | ha
      · exact (hodgeDefectAt_eq_zero_iff Z hZ a).mpr (windowPositiveAt_of_neg Z ha)
      · exact (hodgeDefectAt_eq_zero_iff_le_onsetAperture hZ ha).mpr (htop ▸ le_top)
    have hcard : (rightZeros Z).encard = 0 := by
      rw [← iSup_hodgeDefectAt Z hZ]
      simp [hall]
    have hempty : rightZeros Z = ∅ := Set.encard_eq_zero.mp hcard
    rcases lt_trichotomy ρ.re (1 / 2) with hlt | heq | hgt
    · exfalso
      have hrefl : reflect ρ ∈ rightZeros Z :=
        ⟨Z.reflect_mem ρ hρ, by simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith⟩
      rw [hempty] at hrefl
      exact hrefl
    · exact heq
    · exfalso
      have hmem : ρ ∈ rightZeros Z := ⟨hρ, hgt⟩
      rw [hempty] at hmem
      exact hmem
  · intro hon
    rw [eq_top_iff_forall_lt]
    intro b
    have hb0 : (max b 0 + 1 : ℝ) > b := by linarith [le_max_left b 0]
    have hpos : WindowPositiveAt Z (max b 0 + 1) :=
      fun f _ _ => SquareRootThreshold.re_W_nonneg_of_onLine Z hon f
    exact (EReal.coe_lt_coe_iff.mpr hb0).trans_le
      (le_onsetAperture_of_windowPositiveAt (by linarith [le_max_right b 0]) hpos)

/-! ### 4. Exact `ζ`, `P1`, and `AHD` dictionaries -/

/-- Complex window positivity of `zetaZeroConfig` equals real window positivity
`ZetaWindowPositive`. -/
theorem windowPositiveAt_zeta_iff (a : ℝ) :
    WindowPositiveAt zetaZeroConfig a ↔ ZetaWindowPositive a :=
  ⟨zetaWindowPositive_of_re_W_nonneg, fun h _ hf hfs => re_W_nonneg_of_zetaWindowPositive h hf hfs⟩

/-- **RH is infinite onset aperture of `ζ`.** -/
theorem riemannHypothesis_iff_onsetAperture_zeta_eq_top :
    RiemannHypothesis ↔ onsetAperture zetaZeroConfig = ⊤ := by
  rw [riemannHypothesis_iff_forall_zetaWindowPositive]
  constructor
  · intro hRH
    rw [eq_top_iff_forall_lt]
    intro b
    have hbpos : 0 < max b 0 + 1 := by linarith [le_max_right b 0]
    have hpos : WindowPositiveAt zetaZeroConfig (max b 0 + 1) :=
      (windowPositiveAt_zeta_iff _).mpr (hRH _ hbpos)
    exact (EReal.coe_lt_coe_iff.mpr (by linarith [le_max_left b 0])).trans_le
      (le_onsetAperture_of_windowPositiveAt hbpos.le hpos)
  · intro htop A hA
    exact (windowPositiveAt_zeta_iff A).mp
      ((windowPositiveAt_iff_le_onsetAperture temperedConfig_zetaZeroConfig hA.le).mpr
        (htop ▸ le_top))

/-- **Off RH, `ZetaWindowPositive` holds at `zetaContactAperture` itself**, closing the right
endpoint of `windowPositiveApertures`. -/
theorem zetaWindowPositive_contact_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ZetaWindowPositive zetaContactAperture := by
  rw [← windowPositiveAt_zeta_iff]
  refine windowPositiveAt_of_forall_lt temperedConfig_zetaZeroConfig (zetaContactAperture_pos hRH)
    fun a' ha'0 ha'lt => ?_
  rcases eq_or_lt_of_le ha'0 with rfl | ha'pos
  · exact windowPositiveAt_zero zetaZeroConfig
  · exact (windowPositiveAt_zeta_iff a').mpr (zetaWindowPositive_of_lt_contact ha'pos ha'lt)

/-- **Off RH, the onset aperture of `ζ` equals `zetaContactAperture`.** -/
theorem onsetAperture_zeta_eq_contact_of_not_rh (hRH : ¬ RiemannHypothesis) :
    onsetAperture zetaZeroConfig = (zetaContactAperture : EReal) := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨a, ha0, rfl, hpos⟩
    rw [EReal.coe_le_coe_iff]
    rcases eq_or_lt_of_le ha0 with rfl | hapos
    · exact (zetaContactAperture_pos hRH).le
    · rw [zetaContactAperture_eq_sSup_windowPositiveApertures hRH]
      exact le_csSup (bddAbove_windowPositiveApertures_of_not_riemannHypothesis hRH)
        ⟨hapos, (windowPositiveAt_zeta_iff a).mp hpos⟩
  · exact le_onsetAperture_of_windowPositiveAt (zetaContactAperture_pos hRH).le
      ((windowPositiveAt_zeta_iff _).mpr (zetaWindowPositive_contact_of_not_rh hRH))

/-- **Unconditional `P1` / `AIP` lower bound on `onsetAperture zetaZeroConfig`.** -/
theorem enlargedWeilFloorAperture_le_onsetAperture_zeta :
    ((enlargedWeilFloorAperture : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig := by
  have ha0 : 0 ≤ enlargedWeilFloorAperture := by
    linarith [enlargedWeilFloorAperture_bounds.1]
  refine le_onsetAperture_of_windowPositiveAt ha0 fun f hf hfs => ?_
  have hfloor := zetaZeroConfig_re_W_ge_of_aperture_le_enlargedWeilFloorAperture hf hfs
  have hint : 0 ≤ (1 / 8000 : ℝ) * ∫ u, ‖f u‖ ^ 2 :=
    mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)
  linarith

/-- **Midpoint translation dictionary between `[−A, 0]` (`IsWindowTest A`) and `[−A/2, A/2]`
(`ZetaWindowPositive (A / 2)`).** -/
theorem windowForm_nonneg_iff_zetaWindowPositive_half {A : ℝ} (hA : 0 ≤ A) :
    (∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ weilQuad H) ↔ ZetaWindowPositive (A / 2) := by
  constructor
  · intro h F hF hFc hv
    set H : ℝ → ℝ := fun u => F (u + A / 2)
    have hH : IsWindowTest A H :=
      { contDiff := hF.comp (contDiff_id.add contDiff_const)
        vanish := fun u hu => hv (u + A / 2) (by
          rw [mem_Icc, not_and_or, not_le, not_le] at hu
          rcases hu with hlt | hgt
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith) }
    rw [fullZeroForm_eq_weilQuad hF.continuous hFc, ← weilQuad_translate F (A / 2)]
    exact h H hH
  · intro h H hH
    set F : ℝ → ℝ := fun x => H (x - A / 2)
    have hF : ContDiff ℝ 2 F := hH.contDiff.comp (contDiff_id.sub contDiff_const)
    have hv : ∀ x, A / 2 < |x| → F x = 0 := fun x hx =>
      hH.vanish (x - A / 2) fun hm => by
        rw [mem_Icc] at hm
        have habs : |x| ≤ A / 2 := abs_le.mpr ⟨by linarith [hm.1], by linarith [hm.2]⟩
        linarith
    have hFc : HasCompactSupport F :=
      HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(A / 2)) (b := A / 2))
        fun x hx => abs_le.mp (le_of_not_gt fun hgt => hx (hv x hgt))
    have htr : H = fun u => F (u + A / 2) := by
      funext u; dsimp [F]; ring_nf
    rw [htr, weilQuad_translate F (A / 2), ← fullZeroForm_eq_weilQuad hF.continuous hFc]
    exact h F hF hFc hv

/-- **Exact zero meaning of `AHD.windowThreshold` (`R₁(A) = ⊤`).** For every `A ≥ 0`,
`windowThreshold A = ⊤` iff `((A / 2 : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig`. -/
theorem windowThreshold_eq_top_iff_le_onsetAperture {A : ℝ} (hA : 0 ≤ A) :
    windowThreshold A = ⊤ ↔ ((A / 2 : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig := by
  rw [windowThreshold_eq_top_iff, windowForm_nonneg_iff_zetaWindowPositive_half hA,
    ← windowPositiveAt_zeta_iff,
    windowPositiveAt_iff_le_onsetAperture temperedConfig_zetaZeroConfig (by linarith)]

/-- **Failure aperture of `AHD.windowThreshold`.** Off RH, `windowThreshold A < ⊤` (`A ≥ 0`) iff
`2 * zetaContactAperture < A`. -/
theorem windowThreshold_lt_top_iff_two_mul_contact_lt (hRH : ¬ RiemannHypothesis) {A : ℝ}
    (hA : 0 ≤ A) : windowThreshold A < ⊤ ↔ 2 * zetaContactAperture < A := by
  rw [lt_top_iff_ne_top, Ne, windowThreshold_eq_top_iff_le_onsetAperture hA,
    onsetAperture_zeta_eq_contact_of_not_rh hRH, not_le, EReal.coe_lt_coe_iff]
  constructor <;> intro h <;> linarith

end GaloisForLFunctions.WindowVisibilityLaw
