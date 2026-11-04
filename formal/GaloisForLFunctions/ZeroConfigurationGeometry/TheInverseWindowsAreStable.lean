import GaloisForLFunctions.ZeroConfigurationGeometry.DifferentialWindowsInvertTheCamera

/-!
# The inverse windows are stable: quantitative identification

The differential windows of `DifferentialWindowsInvertTheCamera` read each coefficient of a finite
modification exactly. Here their mass is controlled, which turns the exact inverse into a
stability estimate.

* **Mass of the inverse windows** (`exists_annihilating_window_bound`). With the derivative masses
  `M_k = ∫ |b^{(k)}|` of the base window, the window annihilating a finite set `T` has
  `∫ |f^{(k)}| ≤ Σ_{U ⊆ T} (∏_{z ∈ T∖U} |z|) M_{k+|U|}` (`annihilatorBound`). One operator
  `g' + izg` costs `∫ |g^{(k+1)}| + |z| ∫ |g^{(k)}|` (`derivMass_annihilate_le`).
* **Quantitative identification** (`norm_multDiff_mul_gaps_le`). If the images of `Z` and `Z'`
  agree to precision `ε` per unit window masses on the windows of aperture `r`, then
  `|c(z₀)| ∏_{z ≠ z₀} |γ_{z₀} − γ_z| ≤ ε · annihilatorBound(γ(S∖{z₀}), b, 0)`.
* **Precision that suffices** (`multDiff_eq_zero_of_precision`). Multiplicities are integers, so if
  `ε · annihilatorBound < ∏_{z ≠ z₀} |γ_{z₀} − γ_z|`, the configurations agree at `z₀`.

* **Uniformity in height** (`norm_multDiff_mul_gaps_le_at_height`). Modulating the inverse window to
  a height `T` replaces the frequencies `γ_z` by the offsets `γ_z − T`: the bound depends only on
  the local geometry of the cluster around `T`, not on `T`.

So the precision at which an image determines one point of a finite cluster is the product of the
gaps to the other points divided by the mass of the inverse window. Separated points need moderate
precision; near-collisions make the required precision fall like the gap.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- The derivative mass `∫ |g^{(k)}|`. -/
def derivMass (k : ℕ) (g : ℝ → ℂ) : ℝ := ∫ u, ‖iteratedDeriv k g u‖

/-- The mass bound `Σ_{U ⊆ T} (∏_{z ∈ T∖U} |z|) M_{k+|U|}` of the window annihilating `T`. -/
def annihilatorBound (T : Finset ℂ) (b : ℝ → ℂ) (k : ℕ) : ℝ :=
  ∑ U ∈ T.powerset, (∏ z ∈ T \ U, ‖z‖) * derivMass (k + U.card) b

theorem hasCompactSupport_iteratedDeriv {g : ℝ → ℂ} (hgc : HasCompactSupport g) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k g) := by
  induction k with
  | zero => simpa using hgc
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem integrable_norm_iteratedDeriv {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (k : ℕ) : Integrable fun u => ‖iteratedDeriv k g u‖ :=
  ((hg.continuous_iteratedDeriv k (by exact_mod_cast le_top)).norm).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv hgc k).norm

theorem iteratedDeriv_annihilate {z : ℂ} {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (k : ℕ)
    (u : ℝ) :
    iteratedDeriv k (annihilate z g) u =
      iteratedDeriv (k + 1) g u + (I * z) * iteratedDeriv k g u := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have he : annihilate z g = deriv g + fun v => (I * z) * g v := rfl
  rw [he, iteratedDeriv_add (hd.contDiffAt.of_le (by exact_mod_cast le_top))
      ((contDiff_const.mul hg).contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedDeriv_const_mul _ (hg.contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedDeriv_succ']

/-- **One operator costs one derivative and one factor `|z|`.** -/
theorem derivMass_annihilate_le {z : ℂ} {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (k : ℕ) :
    derivMass k (annihilate z g) ≤ derivMass (k + 1) g + ‖z‖ * derivMass k g := by
  simp only [derivMass]
  rw [← integral_const_mul, ← integral_add (integrable_norm_iteratedDeriv hg hgc (k + 1))
    ((integrable_norm_iteratedDeriv hg hgc k).const_mul _)]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    ((integrable_norm_iteratedDeriv hg hgc (k + 1)).add
      ((integrable_norm_iteratedDeriv hg hgc k).const_mul _)) (Filter.Eventually.of_forall fun u => ?_)
  show ‖iteratedDeriv k (annihilate z g) u‖ ≤
    ‖iteratedDeriv (k + 1) g u‖ + ‖z‖ * ‖iteratedDeriv k g u‖
  rw [iteratedDeriv_annihilate hg k u]
  calc ‖iteratedDeriv (k + 1) g u + I * z * iteratedDeriv k g u‖
      ≤ ‖iteratedDeriv (k + 1) g u‖ + ‖I * z * iteratedDeriv k g u‖ := norm_add_le _ _
    _ = ‖iteratedDeriv (k + 1) g u‖ + ‖z‖ * ‖iteratedDeriv k g u‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul]

/-- The recursion of the mass bound: adding a point `z ∉ T` applies `M_k ↦ M_{k+1} + |z| M_k`. -/
theorem annihilatorBound_insert {T : Finset ℂ} {z : ℂ} (hz : z ∉ T)
    (b : ℝ → ℂ) (k : ℕ) :
    annihilatorBound (insert z T) b k = annihilatorBound T b (k + 1) + ‖z‖ * annihilatorBound T b k := by
  simp only [annihilatorBound]
  rw [Finset.powerset_insert, Finset.sum_union]
  · rw [Finset.sum_image]
    · rw [add_comm, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun U hU => ?_
        have hzU : z ∉ U := fun h => hz (Finset.mem_powerset.mp hU h)
        rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hz,
          Finset.card_insert_of_notMem hzU]
        ring_nf
      · refine Finset.sum_congr rfl fun U hU => ?_
        have hzU : z ∉ U := fun h => hz (Finset.mem_powerset.mp hU h)
        rw [Finset.insert_sdiff_of_notMem _ hzU, Finset.prod_insert
          (fun h => hz (Finset.mem_sdiff.mp h).1)]
        ring
    · intro U hU V hV h
      have hzU : z ∉ U := fun h' => hz (Finset.mem_powerset.mp hU h')
      have hzV : z ∉ V := fun h' => hz (Finset.mem_powerset.mp hV h')
      have := congrArg (fun W => W.erase z) h
      simpa [Finset.erase_insert hzU, Finset.erase_insert hzV] using this
  · rw [Finset.disjoint_left]
    intro U hU hU'
    obtain ⟨V, -, rfl⟩ := Finset.mem_image.mp hU'
    exact hz (Finset.mem_powerset.mp hU (Finset.mem_insert_self z V))

/-- **Inverse windows with mass control.** -/
theorem exists_annihilating_window_bound (T : Finset ℂ) {b : ℝ → ℂ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ tsupport f ⊆ tsupport b ∧
      (∀ w, paperFT f w = (∏ z ∈ T, (-I * (w - z))) * paperFT b w) ∧
        ∀ k, derivMass k f ≤ annihilatorBound T b k := by
  induction T using Finset.induction_on with
  | empty => exact ⟨b, hb, subset_rfl, fun w => by simp, fun k => by simp [annihilatorBound]⟩
  | @insert z T hz ih =>
    obtain ⟨f, hf, hfs, hfw, hfm⟩ := ih
    have hfc : HasCompactSupport f := IsCompact.of_isClosed_subset hbc (isClosed_tsupport f) hfs
    refine ⟨annihilate z f, contDiff_annihilate hf, (tsupport_annihilate_subset z f).trans hfs,
      fun w => ?_, fun k => ?_⟩
    · rw [paperFT_annihilate hf hfc, hfw, Finset.prod_insert hz]; ring
    · rw [annihilatorBound_insert hz]
      exact (derivMass_annihilate_le hf hfc k).trans
        (add_le_add (hfm (k + 1)) (mul_le_mul_of_nonneg_left (hfm k) (norm_nonneg z)))

/-- A window of aperture `r` and mass at most `e^{|Im w₀| r}` whose transform equals `1` at `w₀`. -/
theorem exists_mass_window {r : ℝ} (hr : 0 < r) (w₀ : ℂ) :
    ∃ g : ℝ → ℂ, ApertureWindow r g ∧ (∫ u, ‖g u‖) ≤ Real.exp (|w₀.im| * r) ∧ paperFT g w₀ = 1 := by
  let B : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by linarith, by linarith⟩
  have hBs : tsupport (B.normed volume) ⊆ Icc (-r) r := by
    rw [B.tsupport_normed_eq]
    intro u hu
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, show B.rOut = r from rfl] at hu
    exact abs_le.mp hu
  have hBint : Integrable (B.normed volume) := B.integrable_normed
  refine ⟨fun u => (B.normed volume u : ℂ) * cexp (-(I * w₀ * u)), ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp B.contDiff_normed).mul
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg.cexp)
  · exact (tsupport_mul_subset_left).trans
      ((tsupport_comp_subset (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero _).trans hBs)
  · have hpt : ∀ u : ℝ, ‖(B.normed volume u : ℂ) * cexp (-(I * w₀ * u))‖ ≤
        Real.exp (|w₀.im| * r) * B.normed volume u := fun u => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (B.nonneg_normed u),
        Complex.norm_exp, mul_comm]
      by_cases hu : B.normed volume u = 0
      · rw [hu, mul_zero, mul_zero]
      · have hmem : u ∈ Function.support (B.normed volume) := hu
        rw [B.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero,
          show B.rOut = r from rfl] at hmem
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (B.nonneg_normed u)
        have hre : (-(I * w₀ * (u : ℂ))).re = w₀.im * u := by simp
        rw [hre]
        calc w₀.im * u ≤ |w₀.im * u| := le_abs_self _
          _ = |w₀.im| * |u| := abs_mul _ _
          _ ≤ |w₀.im| * r := mul_le_mul_of_nonneg_left hmem.le (abs_nonneg _)
    calc (∫ u, ‖(B.normed volume u : ℂ) * cexp (-(I * w₀ * u))‖)
        ≤ ∫ u, Real.exp (|w₀.im| * r) * B.normed volume u :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (hBint.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = Real.exp (|w₀.im| * r) := by rw [integral_const_mul, B.integral_normed, mul_one]
  · rw [paperFT_def]
    have : ∀ u : ℝ, (B.normed volume u : ℂ) * cexp (-(I * w₀ * u)) * cexp (I * w₀ * u) =
        (B.normed volume u : ℂ) := fun u => by
      rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    simp_rw [this]
    rw [integral_complex_ofReal, B.integral_normed, Complex.ofReal_one]

/-- The image difference on an annihilating window and a unit window at `conj γ_{z₀}`. -/
theorem W_sub_W_eq_of_annihilating {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {S : Finset ℂ} (hS : ∀ z ∉ S, multDiff Z Z' z = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ S) {r : ℝ} {b f g : ℝ → ℂ} (hb1 : paperFT b (gammaOf z₀) = 1)
    (hfw : ∀ w, paperFT f w = (∏ t ∈ (S.erase z₀).image gammaOf, (-I * (w - t))) * paperFT b w)
    (hf : ApertureWindow r f) (hg : ApertureWindow r g) (hg1 : paperFT g (conj (gammaOf z₀)) = 1) :
    Z.W f g - Z'.W f g = multDiff Z Z' z₀ * ∏ z ∈ S.erase z₀, (-I * (gammaOf z₀ - gammaOf z)) := by
  classical
  rw [W_sub_W_eq_sum hZ hZ' hS hf.1 hf.hasCompactSupport hg.1 hg.hasCompactSupport]
  rw [Finset.sum_eq_single z₀ (fun z hz hne => by
      rw [pointImage, hfw, Finset.prod_eq_zero
        (Finset.mem_image_of_mem gammaOf (Finset.mem_erase.mpr ⟨hne, hz⟩)) (by ring), zero_mul,
        zero_mul, mul_zero])
    (fun h => absurd hz₀ h)]
  rw [pointImage, hfw, hb1, hg1, map_one, mul_one, mul_one,
    Finset.prod_image fun z _ z' _ h => gammaOf_injective h]

/-- **Quantitative identification.** -/
theorem norm_multDiff_mul_gaps_le {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {S : Finset ℂ} (hS : ∀ z ∉ S, multDiff Z Z' z = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ S) {r : ℝ} (hr : 0 < r) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) (hbs : tsupport b ⊆ Icc (-r) r) (hb1 : paperFT b (gammaOf z₀) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ f g, ApertureWindow r f → ApertureWindow r g →
      ‖Z.W f g - Z'.W f g‖ ≤ ε * (∫ u, ‖f u‖) * ∫ u, ‖g u‖) :
    ‖multDiff Z Z' z₀‖ * ∏ z ∈ S.erase z₀, ‖gammaOf z₀ - gammaOf z‖ ≤
      ε * annihilatorBound ((S.erase z₀).image gammaOf) b 0 *
        Real.exp (|(gammaOf z₀).im| * r) := by
  obtain ⟨g, hg, hgm, hg1⟩ := exists_mass_window hr (conj (gammaOf z₀))
  rw [Complex.conj_im, abs_neg] at hgm
  obtain ⟨f, hf, hfs, hfw, hfm⟩ := exists_annihilating_window_bound
    ((S.erase z₀).image gammaOf) hb hbc
  have hfwin : ApertureWindow r f := ⟨hf.of_le (by norm_cast), hfs.trans hbs⟩
  have hid := W_sub_W_eq_of_annihilating hZ hZ' hS hz₀ hb1 hfw hfwin hg hg1
  have hnorm : ‖Z.W f g - Z'.W f g‖ =
      ‖multDiff Z Z' z₀‖ * ∏ z ∈ S.erase z₀, ‖gammaOf z₀ - gammaOf z‖ := by
    rw [hid, norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hf0 : (∫ u, ‖f u‖) ≤ annihilatorBound ((S.erase z₀).image gammaOf) b 0 := by
    have := hfm 0
    simpa [derivMass] using this
  rw [← hnorm]
  calc ‖Z.W f g - Z'.W f g‖ ≤ ε * (∫ u, ‖f u‖) * ∫ u, ‖g u‖ := hW f g hfwin hg
    _ ≤ ε * annihilatorBound ((S.erase z₀).image gammaOf) b 0 *
        Real.exp (|(gammaOf z₀).im| * r) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hf0 hε) hgm (integral_nonneg fun _ => norm_nonneg _)
        (mul_nonneg hε ((integral_nonneg fun _ => norm_nonneg _).trans hf0))

theorem exists_int_multDiff (Z Z' : ZeroConfig) (z : ℂ) : ∃ m : ℤ, multDiff Z Z' z = m := by
  classical
  refine ⟨(if z ∈ Z.carrier then (Z.mult z : ℤ) else 0) -
    (if z ∈ Z'.carrier then (Z'.mult z : ℤ) else 0), ?_⟩
  simp only [multDiff, Set.indicator_apply]
  split_ifs <;> push_cast <;> ring

/-- **Precision that suffices.** If the images agree to a precision `ε` with
`ε · annihilatorBound · e^{|Im γ_{z₀}| r} < ∏_{z ≠ z₀} |γ_{z₀} − γ_z|`, the configurations have the
same multiplicity at `z₀`. -/
theorem multDiff_eq_zero_of_precision {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {S : Finset ℂ} (hS : ∀ z ∉ S, multDiff Z Z' z = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ S) {r : ℝ} (hr : 0 < r) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) (hbs : tsupport b ⊆ Icc (-r) r) (hb1 : paperFT b (gammaOf z₀) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ f g, ApertureWindow r f → ApertureWindow r g →
      ‖Z.W f g - Z'.W f g‖ ≤ ε * (∫ u, ‖f u‖) * ∫ u, ‖g u‖)
    (hprec : ε * annihilatorBound ((S.erase z₀).image gammaOf) b 0 *
        Real.exp (|(gammaOf z₀).im| * r) < ∏ z ∈ S.erase z₀, ‖gammaOf z₀ - gammaOf z‖) :
    multDiff Z Z' z₀ = 0 := by
  by_contra hne
  have hle := norm_multDiff_mul_gaps_le hZ hZ' hS hz₀ hr hb hbc hbs hb1 hε hW
  obtain ⟨m, hm⟩ := exists_int_multDiff Z Z' z₀
  have hm0 : m ≠ 0 := fun h => hne (by rw [hm, h, Int.cast_zero])
  have h1 : (1 : ℝ) ≤ ‖multDiff Z Z' z₀‖ := by
    rw [hm, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hm0
  have hP : 0 ≤ ∏ z ∈ S.erase z₀, ‖gammaOf z₀ - gammaOf z‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  nlinarith

/-! ### Uniformity in height -/

/-- The window `f` modulated to height `T`: `f(u) e^{−iTu}`. -/
def modulate (T : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun u => f u * cexp (-(I * T * u))

theorem paperFT_modulate (T : ℝ) (f : ℝ → ℂ) (w : ℂ) :
    paperFT (modulate T f) w = paperFT f (w - T) := by
  rw [paperFT_def, paperFT_def]
  congr 1 with u
  rw [modulate, mul_assoc, ← Complex.exp_add]
  congr 2; ring

theorem norm_modulate (T : ℝ) (f : ℝ → ℂ) (u : ℝ) : ‖modulate T f u‖ = ‖f u‖ := by
  rw [modulate, norm_mul, show -(I * (T : ℂ) * (u : ℂ)) = ((-(T * u) : ℝ) : ℂ) * I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem contDiff_modulate {T : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (modulate T f) :=
  hf.mul ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg.cexp)

theorem tsupport_modulate_subset (T : ℝ) (f : ℝ → ℂ) : tsupport (modulate T f) ⊆ tsupport f :=
  tsupport_mul_subset_left

/-- **The inverse window at height `T`.** It has aperture `r`, mass at most the bound of the local
offsets `γ_z − T`, and transform `∏_{z ≠ z₀} (−i(w − γ_z)) · b̂(w − T)`. -/
theorem exists_inverse_window_at_height (S : Finset ℂ) (z₀ : ℂ) {r : ℝ} (T : ℝ) {b : ℝ → ℂ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b) (hbs : tsupport b ⊆ Icc (-r) r) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧
      (∫ u, ‖f u‖) ≤ annihilatorBound ((S.erase z₀).image fun z => gammaOf z - T) b 0 ∧
        ∀ w, paperFT f w =
          (∏ t ∈ (S.erase z₀).image gammaOf, (-I * (w - t))) * paperFT (modulate T b) w := by
  obtain ⟨f₀, hf₀, hf₀s, hf₀w, hf₀m⟩ := exists_annihilating_window_bound
    ((S.erase z₀).image fun z => gammaOf z - T) hb hbc
  have hinjT : Set.InjOn (fun z => gammaOf z - T) (S.erase z₀) := fun z _ z' _ h =>
    gammaOf_injective (sub_left_injective h)
  refine ⟨modulate T f₀, ⟨(contDiff_modulate hf₀).of_le (by norm_cast),
    (tsupport_modulate_subset T f₀).trans (hf₀s.trans hbs)⟩, ?_, fun w => ?_⟩
  · have := hf₀m 0
    simp only [derivMass, iteratedDeriv_zero] at this
    simpa only [norm_modulate] using this
  · rw [paperFT_modulate, hf₀w, paperFT_modulate, Finset.prod_image hinjT,
      Finset.prod_image fun z _ z' _ h => gammaOf_injective h]
    congr 1
    refine Finset.prod_congr rfl fun z _ => ?_
    ring

/-- **Quantitative identification at height `T`.** The precision bound depends only on the offsets
`γ_z − T` of the cluster from the height `T` and on a base window at the local frequency
`γ_{z₀} − T`; it is uniform in `T`. -/
theorem norm_multDiff_mul_gaps_le_at_height {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {S : Finset ℂ} (hS : ∀ z ∉ S, multDiff Z Z' z = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ S) {r : ℝ} (hr : 0 < r) (T : ℝ) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) (hbs : tsupport b ⊆ Icc (-r) r)
    (hb1 : paperFT b (gammaOf z₀ - T) = 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ f g, ApertureWindow r f → ApertureWindow r g →
      ‖Z.W f g - Z'.W f g‖ ≤ ε * (∫ u, ‖f u‖) * ∫ u, ‖g u‖) :
    ‖multDiff Z Z' z₀‖ * ∏ z ∈ S.erase z₀, ‖gammaOf z₀ - gammaOf z‖ ≤
      ε * annihilatorBound ((S.erase z₀).image fun z => gammaOf z - T) b 0 *
        Real.exp (|(gammaOf z₀).im| * r) := by
  obtain ⟨g, hg, hgm, hg1⟩ := exists_mass_window hr (conj (gammaOf z₀))
  rw [Complex.conj_im, abs_neg] at hgm
  obtain ⟨f, hfwin, hf0, hfw⟩ := exists_inverse_window_at_height S z₀ T hb hbc hbs
  have hb1' : paperFT (modulate T b) (gammaOf z₀) = 1 := by rw [paperFT_modulate, hb1]
  have hid := W_sub_W_eq_of_annihilating hZ hZ' hS hz₀ hb1' hfw hfwin hg hg1
  have hnorm : ‖Z.W f g - Z'.W f g‖ =
      ‖multDiff Z Z' z₀‖ * ∏ z ∈ S.erase z₀, ‖gammaOf z₀ - gammaOf z‖ := by
    rw [hid, norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  rw [← hnorm]
  calc ‖Z.W f g - Z'.W f g‖ ≤ ε * (∫ u, ‖f u‖) * ∫ u, ‖g u‖ := hW f g hfwin hg
    _ ≤ _ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hf0 hε) hgm (integral_nonneg fun _ => norm_nonneg _)
        (mul_nonneg hε ((integral_nonneg fun _ => norm_nonneg _).trans hf0))

end GaloisForLFunctions.ZeroConfigurationGeometry
