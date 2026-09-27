import GaloisForLFunctions.RHTower.IsolatedDeepZeroHodgeIndex

/-!
# Low-height Weil tests with prescribed transform zeros

For a real even `C²` weight `w` supported in `[-1, 1]`, iterated Zeta23 Weil convolutions of `w`
and `(I∂ - r̄)w` produce `C²` tests supported in `[-N, N]` whose transform is
`z ↦ F(z - γ₀)`, with

```text
F(x) = ŵ(x)^N · Π_{r ∈ L} (x - r)(x - r̄) ,     N = k + 2|L| + 1 .
```

Since `F(x̄) = conj F(x)`, the Weil summand of such a test at a zero `ρ` is `m_ρ F(γ_ρ - γ₀)²`.
This module collects the tools for using these tests:

* the transform formula (`lowHeightTest_props`);
* the square law (`Wsummand_lowHeightTest`);
* perturbation of products (`norm_list_prod_sub_prod_le`, `norm_lowHeightProfile_sub_le`);
* a Lipschitz bound for `ŵ` (`norm_paperFT_sub_le`);
* phase selection by the intermediate value theorem (`exists_phase_rotation`);
* pigeonhole over scales (`exists_gap_scale`);
* the pointwise size of the profile in the strip (`norm_lowHeightProfile_sq_le`).
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### Root-convolution tests -/

/-- For a real even weight, `conj ŵ(z̄) = ŵ(z)`. -/
theorem conj_paperFT_conj_of_even {w : ℝ → ℝ} (heven : ∀ u, w (-u) = w u) (z : ℂ) :
    conj (paperFT (fun u => (w u : ℂ)) (conj z)) = paperFT (fun u => (w u : ℂ)) z := by
  rw [paperFT_def, paperFT_def, ← integral_conj,
    ← integral_neg_eq_self (fun u : ℝ => (w u : ℂ) * cexp (I * z * u))]
  congr 1 with u
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, heven]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

/-- `(I∂ - r̄)w`, whose transform is `(z - r̄)ŵ(z)`. -/
def rootShiftFactor (w : ℝ → ℝ) (r : ℂ) : ℝ → ℂ :=
  fun u => I * ((deriv w u : ℝ) : ℂ) - conj r * (w u : ℂ)

theorem deriv_ofReal_comp_eq {w : ℝ → ℝ} (hw : Differentiable ℝ w) :
    deriv (fun u => (w u : ℂ)) = fun u => ((deriv w u : ℝ) : ℂ) :=
  funext fun u => ((hw u).hasDerivAt.ofReal_comp).deriv

theorem continuous_rootFactor {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (r : ℂ) :
    Continuous (rootShiftFactor w r) := by
  have h1 : Continuous (deriv w) := hw.continuous_deriv (by norm_num)
  unfold rootShiftFactor
  fun_prop

theorem rootFactor_supp {w : ℝ → ℝ} {b : ℝ} (hsupp : ∀ u, w u ≠ 0 → |u| ≤ b) (r : ℂ) :
    ∀ u, rootShiftFactor w r u ≠ 0 → |u| ≤ b := by
  intro u hu
  by_contra hlt
  apply hu
  have h0 : w u = 0 := by by_contra h; exact hlt (hsupp u h)
  have hts := tsupport_subset_of_support_subset_abs hsupp
  have h1 : deriv w u = 0 := by
    by_contra h
    have : u ∈ tsupport w := tsupport_deriv_subset (subset_tsupport _ h)
    exact hlt (abs_le.mpr (hts this))
  simp [rootShiftFactor, h0, h1]

theorem paperFT_rootFactor {w : ℝ → ℝ} {b : ℝ} (hw : ContDiff ℝ 2 w)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ b) (r z : ℂ) :
    paperFT (rootShiftFactor w r) z = (z - conj r) * paperFT (fun u => (w u : ℂ)) z := by
  have hW : ContDiff ℝ 2 (fun u => (w u : ℂ)) := Complex.ofRealCLM.contDiff.comp hw
  have hWs : HasCompactSupport (fun u => (w u : ℂ)) := hasCompactSupport_ofReal_of_abs hsupp
  have hd := paperFT_deriv (hW.of_le (by norm_num)) hWs z
  rw [deriv_ofReal_comp_eq (hw.differentiable (by norm_num))] at hd
  have hdc : Continuous (fun u => ((deriv w u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hw.continuous_deriv (by norm_num))
  have hds : HasCompactSupport (fun u => ((deriv w u : ℝ) : ℂ)) := by
    have := hWs.deriv
    rwa [deriv_ofReal_comp_eq (hw.differentiable (by norm_num))] at this
  have i1 : Integrable (fun u : ℝ => I * (((deriv w u : ℝ) : ℂ) * cexp (I * z * u))) :=
    (integrable_mul_cexp hdc hds z).const_mul I
  have i2 : Integrable (fun u : ℝ => conj r * ((w u : ℂ) * cexp (I * z * u))) :=
    (integrable_mul_cexp hW.continuous hWs z).const_mul (conj r)
  have h : (fun u => rootShiftFactor w r u * cexp (I * z * u)) =
      fun u => I * (((deriv w u : ℝ) : ℂ) * cexp (I * z * u)) -
        conj r * ((w u : ℂ) * cexp (I * z * u)) := by
    funext u; simp only [rootShiftFactor]; ring
  rw [paperFT_def, h, integral_sub i1 i2, integral_const_mul, integral_const_mul,
    ← paperFT_def, ← paperFT_def, hd]
  linear_combination (-(z * paperFT (fun u => (w u : ℂ)) z)) * Complex.I_mul_I

theorem weilTest_support_abs_le {f g : ℝ → ℂ} {A B : ℝ} (hf : ∀ u, f u ≠ 0 → |u| ≤ A)
    (hg : ∀ u, g u ≠ 0 → |u| ≤ B) : ∀ u, EF.weilTest f g u ≠ 0 → |u| ≤ A + B := by
  intro u hu
  have hmem : u ∈ Function.support (EF.weilTest f g) := hu
  unfold EF.weilTest at hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := support_convolution_subset (ContinuousLinearMap.mul ℝ ℂ) hmem
  have h1 := hf x hx
  have h2 : |y| ≤ B := by
    have hy' : g (-y) ≠ 0 := by
      intro h; apply hy; simp [EF.tilde, h]
    have := hg (-y) hy'
    rwa [abs_neg] at this
  rw [← hxy]
  calc |x + y| ≤ |x| + |y| := abs_add_le x y
    _ ≤ A + B := add_le_add h1 h2

/-- Iterated convolution `w ⋆ (I∂ - r̄₁)w̃ ⋆ …`, with transform `ŵ^{n+1} Π(z - rⱼ)`. -/
def rootConv (w : ℝ → ℝ) : List ℂ → ℝ → ℂ
  | [] => fun u => (w u : ℂ)
  | r :: rs => EF.weilTest (rootConv w rs) (rootShiftFactor w r)

theorem rootConv_props {w : ℝ → ℝ} {b : ℝ} (hw : ContDiff ℝ 2 w) (heven : ∀ u, w (-u) = w u)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ b) (rs : List ℂ) :
    ContDiff ℝ 2 (rootConv w rs) ∧
      (∀ u, rootConv w rs u ≠ 0 → |u| ≤ (rs.length + 1) * b) ∧
      ∀ z, paperFT (rootConv w rs) z =
        paperFT (fun u => (w u : ℂ)) z ^ (rs.length + 1) * (rs.map (fun r => z - r)).prod := by
  induction rs with
  | nil =>
    refine ⟨Complex.ofRealCLM.contDiff.comp hw, fun u hu => ?_, fun z => ?_⟩
    · simp only [List.length_nil, Nat.cast_zero, zero_add, one_mul]
      exact hsupp u (fun h => hu (by simp [rootConv, h]))
    · simp [rootConv]
  | cons r rs ih =>
    obtain ⟨ihc, ihs, ihf⟩ := ih
    have hcs : HasCompactSupport (rootConv w rs) := hasCompactSupport_of_support_subset_abs ihs
    have hFc := continuous_rootFactor hw r
    have hFs := rootFactor_supp hsupp r
    have hFcs : HasCompactSupport (rootShiftFactor w r) := hasCompactSupport_of_support_subset_abs hFs
    refine ⟨?_, ?_, ?_⟩
    · exact EF.weilTest_contDiff ihc hFc hcs
    · intro u hu
      have := weilTest_support_abs_le ihs hFs u hu
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith
    · intro z
      show paperFT (EF.weilTest (rootConv w rs) (rootShiftFactor w r)) z = _
      rw [EF.paperFT_weilTest ihc.continuous hFc hcs hFcs, ihf, paperFT_rootFactor hw hsupp,
        map_mul, conj_paperFT_conj_of_even heven, map_sub, Complex.conj_conj, Complex.conj_conj,
        List.map_cons, List.prod_cons, List.length_cons]
      ring

/-- Roots in conjugate pairs. -/
def pairRoots (L : List ℂ) : List ℂ := L.flatMap fun r => [r, conj r]

theorem pairRoots_length (L : List ℂ) : (pairRoots L).length = 2 * L.length := by
  induction L with
  | nil => simp [pairRoots]
  | cons r L ih =>
    simp only [pairRoots, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem prod_pairRoots (L : List ℂ) (z : ℂ) :
    ((pairRoots L).map (fun r => z - r)).prod = (L.map (fun r => (z - r) * (z - conj r))).prod := by
  induction L with
  | nil => simp [pairRoots]
  | cons r L ih =>
    simp only [pairRoots, List.flatMap_cons, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one] at ih ⊢
    rw [ih, mul_assoc]

theorem conj_prod_pairRoots_conj (L : List ℂ) (z : ℂ) :
    conj ((L.map (fun r => (conj z - r) * (conj z - conj r))).prod) =
      (L.map (fun r => (z - r) * (z - conj r))).prod := by
  induction L with
  | nil => simp
  | cons r L ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, map_sub, Complex.conj_conj, ih]
    ring

/-- `f ⋆ w ⋆ ⋯ ⋆ w` (`k` factors), with transform `f̂ ŵ^k`. -/
def plainConv (w : ℝ → ℝ) : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, f => f
  | k + 1, f => EF.weilTest (plainConv w k f) (fun u => (w u : ℂ))

theorem plainConv_props {w : ℝ → ℝ} {b : ℝ} (hw : ContDiff ℝ 2 w) (heven : ∀ u, w (-u) = w u)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ b) {f : ℝ → ℂ} {A : ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : ∀ u, f u ≠ 0 → |u| ≤ A) (k : ℕ) :
    ContDiff ℝ 2 (plainConv w k f) ∧ (∀ u, plainConv w k f u ≠ 0 → |u| ≤ A + k * b) ∧
      ∀ z, paperFT (plainConv w k f) z = paperFT f z * paperFT (fun u => (w u : ℂ)) z ^ k := by
  have hW : Continuous (fun u => (w u : ℂ)) := Complex.continuous_ofReal.comp hw.continuous
  have hWs : ∀ u, (fun u => (w u : ℂ)) u ≠ 0 → |u| ≤ b := fun u hu =>
    hsupp u (fun h => hu (by simp [h]))
  have hWcs : HasCompactSupport (fun u => (w u : ℂ)) := hasCompactSupport_of_support_subset_abs hWs
  induction k with
  | zero => exact ⟨hf, fun u hu => by simpa using hfs u hu, fun z => by simp [plainConv]⟩
  | succ k ih =>
    obtain ⟨ihc, ihs, ihf⟩ := ih
    have hcs : HasCompactSupport (plainConv w k f) := hasCompactSupport_of_support_subset_abs ihs
    refine ⟨EF.weilTest_contDiff ihc hW hcs, fun u hu => ?_, fun z => ?_⟩
    · have := weilTest_support_abs_le ihs hWs u hu
      push_cast
      linarith
    · show paperFT (EF.weilTest (plainConv w k f) (fun u => (w u : ℂ))) z = _
      rw [EF.paperFT_weilTest ihc.continuous hW hcs hWcs, ihf, conj_paperFT_conj_of_even heven]
      ring

/-- The low-height test `e^{-iγ₀u}·(w^{⋆k} ⋆ root convolution)(u)`, whose transform is
`z ↦ F(z - γ₀)` with `F(x) = ŵ(x)^{k + 2|L| + 1} Π_{r ∈ L}(x - r)(x - r̄)`. -/
def lowHeightTest (γ₀ : ℝ) (w : ℝ → ℝ) (k : ℕ) (L : List ℂ) : ℝ → ℂ :=
  fun u => cexp (-(I * γ₀ * u)) * plainConv w k (rootConv w (pairRoots L)) u

/-- The transform profile of the low-height test. -/
def lowHeightProfile (w : ℝ → ℝ) (k : ℕ) (L : List ℂ) (x : ℂ) : ℂ :=
  paperFT (fun u => (w u : ℂ)) x ^ (k + 2 * L.length + 1) *
    (L.map (fun r => (x - r) * (x - conj r))).prod

theorem lowHeightTest_props {w : ℝ → ℝ} {b : ℝ} (hw : ContDiff ℝ 2 w)
    (heven : ∀ u, w (-u) = w u) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ b) (γ₀ : ℝ) (k : ℕ)
    (L : List ℂ) :
    ContDiff ℝ 2 (lowHeightTest γ₀ w k L) ∧
      (∀ u, lowHeightTest γ₀ w k L u ≠ 0 → |u| ≤ (k + 2 * L.length + 1) * b) ∧
      ∀ z, paperFT (lowHeightTest γ₀ w k L) z = lowHeightProfile w k L (z - γ₀) := by
  obtain ⟨hrc, hrs, hrf⟩ := rootConv_props hw heven hsupp (pairRoots L)
  obtain ⟨hpc, hps, hpf⟩ := plainConv_props hw heven hsupp hrc hrs k
  refine ⟨?_, fun u hu => ?_, fun z => ?_⟩
  · unfold lowHeightTest
    have h1 : ContDiff ℝ 2 (fun u : ℝ => (u : ℂ)) := Complex.ofRealCLM.contDiff
    have h2 : ContDiff ℝ 2 (fun u : ℝ => -(I * (γ₀ : ℂ) * (u : ℂ))) := (contDiff_const.mul h1).neg
    exact (Complex.contDiff_exp.comp h2).mul hpc
  · have hne : plainConv w k (rootConv w (pairRoots L)) u ≠ 0 := by
      intro h; apply hu; simp [lowHeightTest, h]
    have := hps u hne
    rw [pairRoots_length] at this
    have e : ((2 * L.length : ℕ) : ℝ) + 1 = 2 * (L.length : ℝ) + 1 := by push_cast; ring
    calc |u| ≤ (((2 * L.length : ℕ) : ℝ) + 1) * b + k * b := this
      _ = (k + 2 * L.length + 1) * b := by push_cast; ring
  · unfold lowHeightTest
    rw [paperFT_modulate, hpf, hrf, prod_pairRoots, pairRoots_length, lowHeightProfile]
    ring

/-- Real structure: the Weil summand of the low-height test is `m F(x_ρ)²`. -/
theorem Wsummand_lowHeightTest {w : ℝ → ℝ} {b : ℝ} (hw : ContDiff ℝ 2 w)
    (heven : ∀ u, w (-u) = w u) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ b) (Z : ZeroConfig) (γ₀ : ℝ)
    (k : ℕ) (L : List ℂ) (ρ : ℂ) :
    Z.Wsummand (lowHeightTest γ₀ w k L) (lowHeightTest γ₀ w k L) ρ =
      (Z.mult ρ : ℂ) * lowHeightProfile w k L (gammaOf ρ - γ₀) ^ 2 := by
  obtain ⟨-, -, hf⟩ := lowHeightTest_props hw heven hsupp γ₀ k L
  rw [ZeroConfig.Wsummand, hf, hf]
  have hc : conj (gammaOf ρ) - (γ₀ : ℂ) = conj (gammaOf ρ - γ₀) := by
    rw [map_sub, Complex.conj_ofReal]
  rw [hc]
  have hreal : conj (lowHeightProfile w k L (conj (gammaOf ρ - γ₀))) =
      lowHeightProfile w k L (gammaOf ρ - γ₀) := by
    unfold lowHeightProfile
    rw [map_mul, map_pow, conj_paperFT_conj_of_even heven, conj_prod_pairRoots_conj]
  rw [hreal]
  ring

/-! ### Perturbation of products, Lipschitz transforms, phase selection -/

theorem norm_list_prod_sub_prod_le {ι : Type*} (l : List ι) (f g : ι → ℂ) (hg : ∀ i ∈ l, g i ≠ 0) :
    ‖(l.map f).prod - (l.map g).prod‖ ≤
      (Real.exp ((l.map fun i => ‖f i - g i‖ / ‖g i‖).sum) - 1) * ‖(l.map g).prod‖ := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hgi : g i ≠ 0 := hg i (List.mem_cons_self)
    have ih' := ih fun j hj => hg j (List.mem_cons_of_mem i hj)
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    set Pf := (l.map f).prod
    set Pg := (l.map g).prod
    set S := (l.map fun i => ‖f i - g i‖ / ‖g i‖).sum
    set e := ‖f i - g i‖ / ‖g i‖ with he
    have hgn : 0 < ‖g i‖ := norm_pos_iff.mpr hgi
    have he0 : 0 ≤ e := by positivity
    have hS0 : 0 ≤ Real.exp S - 1 := by
      have : 0 ≤ S := List.sum_nonneg (fun x hx => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx; positivity)
      linarith [Real.one_le_exp this]
    have hPf : ‖Pf‖ ≤ Real.exp S * ‖Pg‖ := by
      have := norm_le_insert' Pf Pg
      nlinarith [norm_sub_rev Pf Pg]
    have hfi : ‖f i - g i‖ = e * ‖g i‖ := by rw [he]; field_simp
    have key : f i * Pf - g i * Pg = g i * (Pf - Pg) + (f i - g i) * Pf := by ring
    rw [key]
    calc ‖g i * (Pf - Pg) + (f i - g i) * Pf‖
        ≤ ‖g i‖ * ‖Pf - Pg‖ + ‖f i - g i‖ * ‖Pf‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ ‖g i‖ * ((Real.exp S - 1) * ‖Pg‖) + e * ‖g i‖ * (Real.exp S * ‖Pg‖) := by
          rw [hfi]
          gcongr
      _ = ((1 + e) * Real.exp S - 1) * (‖g i‖ * ‖Pg‖) := by ring
      _ ≤ (Real.exp (e + S) - 1) * ‖g i * Pg‖ := by
          rw [norm_mul]
          gcongr
          rw [Real.exp_add]
          have := Real.add_one_le_exp e
          nlinarith [Real.exp_pos S]

/-- Lipschitz bound for the transform of a compactly supported test near a point. -/
theorem norm_paperFT_sub_le {w : ℝ → ℝ} {b : ℝ} (hw : Continuous w)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ b) {z₁ z₂ : ℂ} (hz : b * ‖z₁ - z₂‖ ≤ 1) :
    ‖paperFT (fun u => (w u : ℂ)) z₁ - paperFT (fun u => (w u : ℂ)) z₂‖ ≤
      2 * b * ‖z₁ - z₂‖ * Real.exp (|z₂.im| * b) * ∫ u, |w u| := by
  have hW : Continuous (fun u => (w u : ℂ)) := Complex.continuous_ofReal.comp hw
  have hWs : HasCompactSupport (fun u => (w u : ℂ)) := hasCompactSupport_ofReal_of_abs hsupp
  have i1 := integrable_mul_cexp hW hWs z₁
  have i2 := integrable_mul_cexp hW hWs z₂
  rw [paperFT_def, paperFT_def, ← integral_sub i1 i2]
  have hwi : Integrable (fun u => |w u|) :=
    (hw.abs.integrable_of_hasCompactSupport (hasCompactSupport_of_support_subset_abs hsupp).abs)
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hwi.const_mul _) (Eventually.of_forall fun u => ?_)
  by_cases hu : w u = 0
  · simp [hu]
  have hub := hsupp u hu
  have hfac : (w u : ℂ) * cexp (I * z₁ * u) - (w u : ℂ) * cexp (I * z₂ * u) =
      (w u : ℂ) * cexp (I * z₂ * u) * (cexp (I * (z₁ - z₂) * u) - 1) := by
    rw [show cexp (I * z₁ * u) = cexp (I * z₂ * u) * cexp (I * (z₁ - z₂) * u) by
      rw [← Complex.exp_add]; ring_nf]
    ring
  rw [hfac, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsmall : ‖I * (z₁ - z₂) * (u : ℂ)‖ ≤ 1 := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg (z₁ - z₂), abs_nonneg u]
  have h1 := Complex.norm_exp_sub_one_le hsmall
  have h2 : ‖cexp (I * z₂ * u)‖ ≤ Real.exp (|z₂.im| * b) := norm_cexp_I_mul_le hub
  have h3 : ‖I * (z₁ - z₂) * (u : ℂ)‖ ≤ ‖z₁ - z₂‖ * b := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hub (norm_nonneg _)
  calc |w u| * ‖cexp (I * z₂ * u)‖ * ‖cexp (I * (z₁ - z₂) * u) - 1‖
      ≤ |w u| * Real.exp (|z₂.im| * b) * (2 * (‖z₁ - z₂‖ * b)) := by
        gcongr
        exact h1.trans (by linarith)
    _ = 2 * b * ‖z₁ - z₂‖ * Real.exp (|z₂.im| * b) * |w u| := by ring

/-- Phase selection: some `c ∈ [-δ, δ]` makes `(c + iδ)² G` purely imaginary. -/
theorem exists_phase_rotation {δ : ℝ} (hδ : 0 < δ) (G : ℂ) :
    ∃ c ∈ Icc (-δ) δ, (((c : ℂ) + I * δ) ^ 2 * G).re = 0 := by
  set h : ℝ → ℝ := fun c => (((c : ℂ) + I * δ) ^ 2 * G).re with hh
  have hcont : Continuous h := by
    rw [hh]
    fun_prop
  have hI : I * I = -1 := Complex.I_mul_I
  have hp : h δ = -2 * δ ^ 2 * G.im := by
    simp only [hh]
    have : ((δ : ℂ) + I * δ) ^ 2 * G = ((2 * δ ^ 2 : ℝ) : ℂ) * (I * G) := by
      push_cast
      linear_combination ((δ : ℂ) ^ 2 * G) * hI
    rw [this, Complex.re_ofReal_mul]
    simp [Complex.mul_re]
  have hm : h (-δ) = 2 * δ ^ 2 * G.im := by
    simp only [hh]
    have : (((-δ : ℝ) : ℂ) + I * δ) ^ 2 * G = ((-2 * δ ^ 2 : ℝ) : ℂ) * (I * G) := by
      push_cast
      linear_combination ((δ : ℂ) ^ 2 * G) * hI
    rw [this, Complex.re_ofReal_mul]
    simp [Complex.mul_re]
  have hle : -δ ≤ δ := by linarith
  rcases le_or_gt 0 G.im with hG | hG
  · have hmem : (0 : ℝ) ∈ Icc (h δ) (h (-δ)) := by
      constructor
      · rw [hp]; nlinarith [sq_nonneg δ]
      · rw [hm]; positivity
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hle hcont.continuousOn hmem
    exact ⟨c, hc, hc0⟩
  · have hmem : (0 : ℝ) ∈ Icc (h (-δ)) (h δ) := by
      constructor
      · rw [hm]; nlinarith [sq_nonneg δ]
      · rw [hp]; nlinarith [sq_nonneg δ]
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hle hcont.continuousOn hmem
    exact ⟨c, hc, hc0⟩

theorem sq_eq_neg_normSq_of_re_eq_zero {F : ℂ} (h : F.re = 0) : F ^ 2 = -((‖F‖ ^ 2 : ℝ) : ℂ) := by
  have hF : F = (F.im : ℂ) * I := by apply Complex.ext <;> simp [h]
  have hn : ‖F‖ ^ 2 = F.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply, h]; ring
  rw [hn]
  conv_lhs => rw [hF]
  push_cast
  linear_combination ((F.im : ℂ)) ^ 2 * Complex.I_mul_I

/-! ### Scale selection and the cluster estimate -/

/-- Pigeonhole over `card s + 1` disjoint scales: some annulus `[ε₀/λ^{k+1}, ε₀/λ^k)` contains
none of the values `r i`. -/
theorem exists_gap_scale {ι : Type*} (s : Finset ι) (r : ι → ℝ) {ε₀ lam : ℝ} (hε₀ : 0 < ε₀)
    (hlam : 1 < lam) :
    ∃ k ≤ s.card, ∀ i ∈ s, r i < ε₀ / lam ^ (k + 1) ∨ ε₀ / lam ^ k ≤ r i := by
  classical
  by_contra h
  push Not at h
  have hbad : ∀ k ∈ Finset.range (s.card + 1), ∃ i ∈ s,
      ε₀ / lam ^ (k + 1) ≤ r i ∧ r i < ε₀ / lam ^ k := fun k hk =>
    h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  obtain ⟨i₀, -, -⟩ := hbad 0 (Finset.mem_range.mpr (Nat.succ_pos _))
  haveI : Nonempty ι := ⟨i₀⟩
  choose! g hgs hg using hbad
  have hinj : Set.InjOn g ((Finset.range (s.card + 1) : Finset ℕ) : Set ℕ) := by
    intro k hk k' hk' hkk'
    by_contra hne
    have h1 := hg k hk
    have h2 := hg k' hk'
    rw [hkk'] at h1
    have hlam0 : 0 < lam := by linarith
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : ε₀ / lam ^ k' ≤ ε₀ / lam ^ (k + 1) :=
        div_le_div_of_nonneg_left hε₀.le (by positivity)
          (pow_le_pow_right₀ hlam.le (by omega))
      linarith [h1.1, h2.2]
    · have : ε₀ / lam ^ k ≤ ε₀ / lam ^ (k' + 1) :=
        div_le_div_of_nonneg_left hε₀.le (by positivity)
          (pow_le_pow_right₀ hlam.le (by omega))
      linarith [h1.2, h2.1]
  have := Finset.card_le_card_of_injOn g (fun k hk => hgs k hk) hinj
  simp at this

/-- A small perturbation of a purely imaginary value keeps its square negative. -/
theorem re_sq_le_of_near {F₀ F₁ : ℂ} {θ : ℝ} (hθ : 0 ≤ θ) (h0 : F₀ ^ 2 = -((‖F₀‖ ^ 2 : ℝ) : ℂ))
    (h1 : ‖F₁ - F₀‖ ≤ θ * ‖F₀‖) : (F₁ ^ 2).re ≤ -(1 - 2 * θ - θ ^ 2) * ‖F₀‖ ^ 2 := by
  set E := F₁ - F₀ with hE
  have hF₁ : F₁ = F₀ + E := by rw [hE]; ring
  have hsq : F₁ ^ 2 = F₀ ^ 2 + (2 * F₀ * E + E ^ 2) := by rw [hF₁]; ring
  rw [hsq, Complex.add_re, h0, Complex.neg_re, Complex.ofReal_re]
  have h2 : (2 * F₀ * E + E ^ 2).re ≤ 2 * ‖F₀‖ * ‖E‖ + ‖E‖ ^ 2 := by
    refine (Complex.re_le_norm _).trans ((norm_add_le _ _).trans ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
  have hE0 : 0 ≤ ‖E‖ := norm_nonneg _
  have h3 : 2 * ‖F₀‖ * ‖E‖ + ‖E‖ ^ 2 ≤ (2 * θ + θ ^ 2) * ‖F₀‖ ^ 2 := by
    have := norm_nonneg F₀
    nlinarith [mul_le_mul h1 h1 hE0 (by positivity)]
  linarith

/-! ### The profile as a product of factors -/

theorem lowHeightProfile_conj {w : ℝ → ℝ} (heven : ∀ u, w (-u) = w u) (k : ℕ) (L : List ℂ)
    (z : ℂ) : lowHeightProfile w k L (conj z) = conj (lowHeightProfile w k L z) := by
  have hw' : conj (paperFT (fun u => (w u : ℂ)) z) = paperFT (fun u => (w u : ℂ)) (conj z) := by
    have := conj_paperFT_conj_of_even heven (conj z)
    rwa [Complex.conj_conj] at this
  have hp : conj ((L.map fun r => (z - r) * (z - conj r)).prod) =
      (L.map fun r => (conj z - r) * (conj z - conj r)).prod := by
    induction L with
    | nil => simp
    | cons r L ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, map_sub, Complex.conj_conj, ih]
      ring
  unfold lowHeightProfile
  rw [map_mul, map_pow, hw', hp]

/-- The factors of the profile: `ŵ` for `none`, `z - r` for `some r`. -/
def profileFactor (w : ℝ → ℝ) : Option ℂ → ℂ → ℂ
  | none, z => paperFT (fun u => (w u : ℂ)) z
  | some r, z => z - r

theorem lowHeightProfile_eq_prod (w : ℝ → ℝ) (k : ℕ) (L : List ℂ) (z : ℂ) :
    lowHeightProfile w k L z =
      ((List.replicate (k + 2 * L.length + 1) none ++ (pairRoots L).map some).map
        (fun o => profileFactor w o z)).prod := by
  rw [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate, List.map_map]
  unfold lowHeightProfile
  congr 1
  rw [← prod_pairRoots]
  rfl

/-- Perturbation of the profile. -/
theorem norm_lowHeightProfile_sub_le (w : ℝ → ℝ) (k : ℕ) (L : List ℂ) {z x₀ : ℂ}
    (hw0 : paperFT (fun u => (w u : ℂ)) x₀ ≠ 0) (hr : ∀ r ∈ pairRoots L, x₀ - r ≠ 0) :
    ‖lowHeightProfile w k L z - lowHeightProfile w k L x₀‖ ≤
      (Real.exp ((k + 2 * L.length + 1 : ℕ) *
          (‖paperFT (fun u => (w u : ℂ)) z - paperFT (fun u => (w u : ℂ)) x₀‖ /
            ‖paperFT (fun u => (w u : ℂ)) x₀‖) +
          ((pairRoots L).map fun r => ‖z - x₀‖ / ‖x₀ - r‖).sum) - 1) *
        ‖lowHeightProfile w k L x₀‖ := by
  rw [lowHeightProfile_eq_prod, lowHeightProfile_eq_prod]
  have hg : ∀ o ∈ List.replicate (k + 2 * L.length + 1) none ++ (pairRoots L).map some,
      profileFactor w o x₀ ≠ 0 := by
    intro o ho
    rcases List.mem_append.mp ho with h | h
    · rw [List.eq_of_mem_replicate h]; exact hw0
    · obtain ⟨r, hr', rfl⟩ := List.mem_map.mp h
      exact hr r hr'
  refine (norm_list_prod_sub_prod_le _ (fun o => profileFactor w o z)
    (fun o => profileFactor w o x₀) hg).trans (le_of_eq ?_)
  congr 2
  rw [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate, List.map_map,
    nsmul_eq_mul]
  congr 1
  simp only [Function.comp_def, profileFactor, sub_sub_sub_cancel_right]

/-! ### Size of the profile -/

theorem norm_list_prod_le_pow {l : List ℂ} {c : ℝ} (hc : 0 ≤ c) (f : ℂ → ℂ)
    (h : ∀ r ∈ l, ‖f r‖ ≤ c) : ‖(l.map f).prod‖ ≤ c ^ l.length := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    rw [norm_mul, mul_comm (c ^ l.length) c]
    exact mul_le_mul (h r List.mem_cons_self)
      (ih fun r' hr' => h r' (List.mem_cons_of_mem r hr')) (norm_nonneg _) hc

theorem le_norm_list_prod_pow {l : List ℂ} {c : ℝ} (hc : 0 ≤ c) (f : ℂ → ℂ)
    (h : ∀ r ∈ l, c ≤ ‖f r‖) : c ^ l.length ≤ ‖(l.map f).prod‖ := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    rw [norm_mul, mul_comm (c ^ l.length) c]
    exact mul_le_mul (h r List.mem_cons_self)
      (ih fun r' hr' => h r' (List.mem_cons_of_mem r hr')) (by positivity) (norm_nonneg _)

theorem lowHeightProfile_eq_pairRoots (w : ℝ → ℝ) (k : ℕ) (L : List ℂ) (x : ℂ) :
    lowHeightProfile w k L x = paperFT (fun u => (w u : ℂ)) x ^ (k + 2 * L.length + 1) *
      ((pairRoots L).map (fun r => x - r)).prod := by
  rw [lowHeightProfile, prod_pairRoots]

/-- Pointwise bound on the profile in the strip. -/
theorem norm_lowHeightProfile_sq_le {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) (k : ℕ) (L : List ℂ) {x : ℂ} (hxim : |x.im| ≤ 1 / 2)
    {M : ℝ} (hM : 0 ≤ M) (hr : ∀ r ∈ pairRoots L, ‖x - r‖ ≤ M * (1 + |x.re|)) :
    ‖lowHeightProfile w k L x‖ ^ 2 * ((1 + |x.re|) ^ 2) ^ (2 * (k + 2 * L.length + 1)) ≤
      (Real.exp (1 / 2) * (4 * testNorm w)) ^ (2 * (k + 2 * L.length + 1)) *
        (M * (1 + |x.re|)) ^ (2 * (pairRoots L).length) := by
  have hW : ContDiff ℝ 2 (fun u => (w u : ℂ)) := Complex.ofRealCLM.contDiff.comp hw
  have hWs : ∀ u, (fun u => (w u : ℂ)) u ≠ 0 → |u| ≤ 1 := fun u hu =>
    hsupp u (fun h => hu (by simp [h]))
  have hdec := norm_paperFT_le_decay hW hWs x
  change _ ≤ Real.exp _ * (4 * testNorm w) / _ at hdec
  have hN := testNorm_nonneg w
  have hD0 : 0 < 1 + |x.re| := by positivity
  have hwx : ‖paperFT (fun u => (w u : ℂ)) x‖ * (1 + |x.re|) ^ 2 ≤
      Real.exp (1 / 2) * (4 * testNorm w) := by
    rw [← le_div_iff₀ (by positivity)]
    refine hdec.trans ?_
    gcongr
    linarith
  have hprod := norm_list_prod_le_pow (by positivity : 0 ≤ M * (1 + |x.re|)) (fun r => x - r) hr
  rw [lowHeightProfile_eq_pairRoots, norm_mul, norm_pow]
  set N := k + 2 * L.length + 1
  set p := (pairRoots L).length
  have h1 : (‖paperFT (fun u => (w u : ℂ)) x‖ * (1 + |x.re|) ^ 2) ^ N ≤
      (Real.exp (1 / 2) * (4 * testNorm w)) ^ N :=
    pow_le_pow_left₀ (by positivity) hwx N
  have h2 := mul_le_mul h1 hprod (norm_nonneg _) (by positivity)
  have h3 := pow_le_pow_left₀ (by positivity) h2 2
  set D2 := (1 + |x.re|) ^ 2 with hD2
  calc (‖paperFT (fun u => (w u : ℂ)) x‖ ^ N * ‖((pairRoots L).map fun r => x - r).prod‖) ^ 2 *
        D2 ^ (2 * N)
      = ((‖paperFT (fun u => (w u : ℂ)) x‖ * D2) ^ N *
          ‖((pairRoots L).map fun r => x - r).prod‖) ^ 2 := by ring_nf
    _ ≤ ((Real.exp (1 / 2) * (4 * testNorm w)) ^ N * (M * (1 + |x.re|)) ^ p) ^ 2 := h3
    _ = _ := by ring

end RHTower
