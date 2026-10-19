import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw

/-!
# Windowed Weil forms: depth-blindness and the slice transfer law

For a test `f` and a window `η`, the *windowed Weil kernel* is the product `k_f · k_η` of the two
Weil kernels `k_f = f ⋆ f̃`, `k_η = η ⋆ η̃`. The *windowed Weil form* of a zero configuration is
`Σ_ρ m_ρ h_{k_f k_η}(γ_ρ)`. Fourier inversion identifies it with the average of the localized
forms `W(M_t f, M_t f)` over heights `t`, weighted by `|h_η(t)|²/2π`; see
`HeightWindowAverageRepresentation`. A window supported in `[-r, r]` therefore averages over height
windows of length about `1/r`.

* **Depth-blindness on lattices.** If the window is supported in `[-L/2, L/2]`, the windowed form
  of the off-line lattice pair `{½ ± δ + 2πik/L}` equals that of the doubled on-line lattice,
  `2L‖f‖²‖η‖²`, for **every** test `f`, whatever its aperture and whatever the depth `δ`.
* **Slice factorization.** With the slices `g_s(u) = f(u + s) η(u)`,
  `k_f(v) k_η(v) = ∫ k_{g_s}(v) ds`. Every slice is supported in the support of `η`.
* **Transfer law.** For every tempered configuration
  (`Σ_ρ m_ρ/(1 + |γ_ρ|²) < ∞`), the windowed form equals `∫ W(g_s, g_s) ds`. Hence Weil
  positivity at aperture `r` implies nonnegativity of every windowed form whose window is
  supported in `[-r, r]`, at every aperture of the test.

**Consequence (insensitivity of averaged information).** Height averages at resolution `r` see a
configuration only through its aperture-`r` Weil forms. Off-line lattice pairs of every depth, and
isolated pairs below their visibility threshold, have nonnegative windowed forms at every test
aperture. Window-averaged positivity can therefore never imply the Riemann hypothesis.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 RHTower

/-! ### Windows, slices and the windowed Weil form -/

/-- The part of `f` seen through the window `η` at offset `s`: `g_s(u) = f(u + s) η(u)`. -/
def windowSlice (f η : ℝ → ℂ) (s : ℝ) : ℝ → ℂ := fun u => f (u + s) * η u

/-- The windowed Weil kernel `k_f · k_η`. -/
def windowedKernel (f η : ℝ → ℂ) : ℝ → ℂ := fun v => EF.weilTest f f v * EF.weilTest η η v

/-- The windowed Weil form `Σ_ρ m_ρ h_{k_f k_η}(γ_ρ)`. -/
def windowedW (Z : ZeroConfig) (f η : ℝ → ℂ) : ℂ :=
  ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (windowedKernel f η) (gammaOf ρ)

/-- A zero configuration is *tempered* when `Σ_ρ m_ρ/(1 + |γ_ρ|²)` converges. -/
def TemperedConfig (Z : ZeroConfig) : Prop :=
  Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))

theorem windowSlice_contDiff {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hη : ContDiff ℝ 2 η)
    (s : ℝ) : ContDiff ℝ 2 (windowSlice f η s) :=
  (hf.comp (contDiff_id.add contDiff_const)).mul hη

theorem tsupport_windowSlice_subset (f η : ℝ → ℂ) (s : ℝ) :
    tsupport (windowSlice f η s) ⊆ tsupport η :=
  tsupport_mul_subset_right

theorem windowedKernel_contDiff {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) : ContDiff ℝ 2 (windowedKernel f η) :=
  (EF.weilTest_contDiff hf hf.continuous hfc).mul (EF.weilTest_contDiff hη hη.continuous hηc)

/-- At lag zero the windowed kernel is `‖f‖² ‖η‖²`. -/
theorem windowedKernel_zero (f η : ℝ → ℂ) :
    windowedKernel f η 0 = ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) * ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) := by
  simp only [windowedKernel, weilTest_apply, sub_zero, integral_mul_conj_self_eq]

/-! ### Radii -/

theorem exists_radius_of_hasCompactSupport {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    ∃ A, 0 ≤ A ∧ ∀ u, A < |u| → f u = 0 := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun u hu => ?_⟩
  by_contra hne
  have := hR (subset_tsupport _ (Function.mem_support.mpr hne))
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith [le_max_left R 0]

theorem eq_zero_of_lt_abs {η : ℝ → ℂ} {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r) {u : ℝ}
    (hu : r < |u|) : η u = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => by
    have := hηs h
    exact absurd (abs_le.mpr ⟨this.1, this.2⟩) (not_le.mpr hu)

theorem windowSlice_eq_zero_of_far {f η : ℝ → ℂ} {A r : ℝ} (hfA : ∀ u, A < |u| → f u = 0)
    (hηr : ∀ u, r < |u| → η u = 0) {s : ℝ} (hs : A + r < |s|) (u : ℝ) :
    windowSlice f η s u = 0 := by
  unfold windowSlice
  by_cases hu : r < |u|
  · rw [hηr u hu, mul_zero]
  · rw [not_lt] at hu
    have h := abs_add_le (u + s) (-u)
    rw [abs_neg, show u + s + -u = s by ring] at h
    rw [hfA (u + s) (by linarith), zero_mul]

/-- A windowed kernel vanishes beyond twice the window radius. -/
theorem windowedKernel_eq_zero_of_le {f η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r) {v : ℝ}
    (hv : 2 * r ≤ |v|) : windowedKernel f η v = 0 := by
  have hηs' : tsupport η ⊆ Icc (-(2 * r / 2)) (2 * r / 2) := by
    rwa [show 2 * r / 2 = r by ring]
  have hK := EF.tsupport_weilTest_subset hηs' hηs'
  have hKc : Continuous (EF.weilTest η η) :=
    (EF.weilTest_contDiff hη hη.continuous hηc).continuous
  simp only [windowedKernel, eq_zero_of_tsupport_subset_Icc hKc hK hv, mul_zero]


/-! ### Depth-blindness of windowed forms on lattices -/

/-- A `C²` kernel vanishing on `|u| ≥ L` has lattice Poisson sum `L·K(0)` on every vertical
lattice of spacing `2π/L`, at every depth. -/
theorem hasSum_paperFT_lattice_of_vanish {K : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hK : ContDiff ℝ 2 K)
    (hKz : ∀ u, L ≤ |u| → K u = 0) (δ : ℝ) :
    HasSum (fun k : ℤ => paperFT K ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * δ)) (L * K 0) := by
  have hKs : ∀ u, K u ≠ 0 → |u| ≤ L := fun u hu => by
    by_contra h
    exact hu (hKz u (le_of_lt (not_le.mp h)))
  have h := hasSum_paperFT_lattice_sub_I_mul hL hK hKs δ
  have ht : ∑' m : ℤ, K (m * L) * (Real.exp (δ * (m * L)) : ℂ) = K 0 := by
    rw [tsum_eq_single 0]
    · simp
    · intro m hm
      rw [hKz, zero_mul]
      rw [abs_mul, abs_of_pos hL]
      have : (1 : ℝ) ≤ |(m : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hm
      nlinarith
  rwa [ht] at h

/-- Windowed form of the doubled on-line lattice, for windows below the Nyquist aperture. -/
theorem windowedW_onLineLatticeConfig {L : ℝ} (hL : 0 < L) {f η : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-(L / 2)) (L / 2)) :
    windowedW (onLineLatticeConfig hL) f η = 2 * L * windowedKernel f η 0 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have hK := windowedKernel_contDiff hf hfc hη hηc
  have hKz : ∀ u, L ≤ |u| → windowedKernel f η u = 0 := fun u hu =>
    windowedKernel_eq_zero_of_le hη hηc hηs (by linarith)
  have h := (hasSum_paperFT_lattice_of_vanish hL hK hKz 0).mul_left 2
  set G : ℂ → ℂ := fun ρ => ((onLineLatticeConfig hL).mult ρ : ℂ) *
    paperFT (windowedKernel f η) (gammaOf ρ) with hG
  have hfun : G ∘ verticalLatticePoint L 0 =
      fun k : ℤ => 2 * paperFT (windowedKernel f η)
        ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * ((0 : ℝ) : ℂ)) := by
    funext k
    simp only [hG, Function.comp_apply, gammaOf_verticalLatticePoint]
    simp only [onLineLatticeConfig, Nat.cast_ofNat]
  have h' : HasSum (fun ρ : Set.range (verticalLatticePoint L 0) => G ρ)
      (2 * (L * windowedKernel f η 0)) := by
    rw [(verticalLatticePoint_injective hL 0).hasSum_range_iff, hfun]
    exact h
  rw [windowedW]
  exact h'.tsum_eq.trans (by ring)

/-- Windowed form of the off-line lattice pair, for windows below the Nyquist aperture. -/
theorem windowedW_offLineLatticeConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-(L / 2)) (L / 2)) :
    windowedW (offLineLatticeConfig hL hδ hδ') f η = 2 * L * windowedKernel f η 0 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have hK := windowedKernel_contDiff hf hfc hη hηc
  have hKz : ∀ u, L ≤ |u| → windowedKernel f η u = 0 := fun u hu =>
    windowedKernel_eq_zero_of_le hη hηc hηs (by linarith)
  set G : ℂ → ℂ := fun ρ => ((offLineLatticeConfig hL hδ hδ').mult ρ : ℂ) *
    paperFT (windowedKernel f η) (gammaOf ρ) with hG
  have hpart : ∀ ε : ℝ, HasSum (fun ρ : Set.range (verticalLatticePoint L ε) => G ρ)
      (L * windowedKernel f η 0) := by
    intro ε
    rw [(verticalLatticePoint_injective hL ε).hasSum_range_iff]
    have hfun : G ∘ verticalLatticePoint L ε = fun k : ℤ => paperFT (windowedKernel f η)
        ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * ε) := by
      funext k
      simp only [hG, Function.comp_apply, gammaOf_verticalLatticePoint, offLineLatticeConfig,
        Nat.cast_one, one_mul]
    rw [hfun]
    exact hasSum_paperFT_lattice_of_vanish hL hK hKz ε
  have hdisj : Disjoint (Set.range (verticalLatticePoint L δ))
      (Set.range (verticalLatticePoint L (-δ))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    have := congrArg Complex.re hk'
    simp only [verticalLatticePoint] at this
    linarith
  have hall := HasSum.add_disjoint (f := G) hdisj (hpart δ) (hpart (-δ))
  rw [windowedW]
  exact hall.tsum_eq.trans (by ring)

/-- **Depth-blindness of windowed forms.** For every window supported in `[-L/2, L/2]` and every
test of arbitrary aperture, the off-line lattice pair at any depth has the same windowed form as
the doubled on-line lattice. -/
theorem windowedW_offLineLattice_eq_onLine {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-(L / 2)) (L / 2)) :
    windowedW (offLineLatticeConfig hL hδ hδ') f η = windowedW (onLineLatticeConfig hL) f η := by
  rw [windowedW_offLineLatticeConfig hL hδ hδ' hf hfc hη hηs,
    windowedW_onLineLatticeConfig hL hf hfc hη hηs]

/-- The common value is `2L ‖f‖² ‖η‖² ≥ 0`. -/
theorem windowedW_offLineLatticeConfig_eq_norms {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-(L / 2)) (L / 2)) :
    windowedW (offLineLatticeConfig hL hδ hδ') f η =
      ((2 * L * ((∫ t, ‖f t‖ ^ 2) * ∫ t, ‖η t‖ ^ 2) : ℝ) : ℂ) := by
  rw [windowedW_offLineLatticeConfig hL hδ hδ' hf hfc hη hηs, windowedKernel_zero]
  push_cast
  ring

theorem re_windowedW_offLineLatticeConfig_nonneg {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-(L / 2)) (L / 2)) :
    0 ≤ (windowedW (offLineLatticeConfig hL hδ hδ') f η).re := by
  rw [windowedW_offLineLatticeConfig_eq_norms hL hδ hδ' hf hfc hη hηs, Complex.ofReal_re]
  have h1 : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h2 : 0 ≤ ∫ t, ‖η t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  positivity

/-! ### Slice factorization -/

/-- A continuous function on `ℝ × ℝ` vanishing outside a box is integrable. -/
theorem integrable_of_continuous_of_vanish_box {F : ℝ × ℝ → ℂ} (hF : Continuous F) {A B : ℝ}
    (hz : ∀ p : ℝ × ℝ, (A < |p.1| ∨ B < |p.2|) → F p = 0) :
    Integrable F (volume.prod volume) := by
  refine hF.integrable_of_hasCompactSupport (HasCompactSupport.intro
    ((isCompact_Icc (a := -A) (b := A)).prod (isCompact_Icc (a := -B) (b := B))) fun p hp => ?_)
  apply hz
  rw [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · left
    by_contra h'
    exact h (abs_le.mp (not_lt.mp h'))
  · right
    by_contra h'
    exact h (abs_le.mp (not_lt.mp h'))

theorem abs_lt_add_of_abs_le {s t A r : ℝ} (ht : |t| ≤ r) (hs : A + r < |s|) : A < |t + s| := by
  have h := abs_add_le (t + s) (-t)
  rw [abs_neg, show t + s + -t = s by ring] at h
  linarith

/-- **Slice factorization of the windowed kernel.** `k_f(v) k_η(v) = ∫ k_{g_s}(v) ds`. -/
theorem integral_weilTest_windowSlice {f η : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hη : Continuous η) (hηc : HasCompactSupport η) (v : ℝ) :
    ∫ s, EF.weilTest (windowSlice f η s) (windowSlice f η s) v = windowedKernel f η v := by
  obtain ⟨A, -, hfA⟩ := exists_radius_of_hasCompactSupport hfc
  obtain ⟨r, -, hηr⟩ := exists_radius_of_hasCompactSupport hηc
  simp only [weilTest_apply, windowSlice, windowedKernel]
  have hint : Integrable (Function.uncurry fun (s t : ℝ) =>
      f (t + s) * η t * conj (f (t - v + s) * η (t - v))) (volume.prod volume) := by
    refine integrable_of_continuous_of_vanish_box (A := A + r) (B := r) ?_ ?_
    · change Continuous fun p : ℝ × ℝ =>
        f (p.2 + p.1) * η p.2 * conj (f (p.2 - v + p.1) * η (p.2 - v))
      fun_prop
    · rintro ⟨s, t⟩ h
      simp only [Function.uncurry_apply_pair]
      rcases h with h | h
      · by_cases ht : r < |t|
        · rw [hηr t ht]; simp
        · rw [hfA (t + s) (abs_lt_add_of_abs_le (not_lt.mp ht) h)]; simp
      · rw [hηr t h]; simp
  rw [integral_integral_swap hint]
  have hinner : ∀ t, ∫ s, f (t + s) * η t * conj (f (t - v + s) * η (t - v)) =
      (η t * conj (η (t - v))) * ∫ x, f x * conj (f (x - v)) := by
    intro t
    rw [← integral_const_mul, ← integral_add_right_eq_self
      (fun x => (η t * conj (η (t - v))) * (f x * conj (f (x - v)))) t]
    congr 1 with s
    rw [map_mul, show s + t - v = t - v + s by ring, add_comm s t]
    ring
  rw [integral_congr_ae (Eventually.of_forall hinner), integral_mul_const]
  ring

/-- The slice kernels are jointly continuous in offset and lag. -/
theorem continuous_weilTest_windowSlice {f η : ℝ → ℂ} (hf : Continuous f) (hη : Continuous η)
    (hηc : HasCompactSupport η) :
    Continuous fun p : ℝ × ℝ => EF.weilTest (windowSlice f η p.1) (windowSlice f η p.1) p.2 := by
  obtain ⟨r, -, hηr⟩ := exists_radius_of_hasCompactSupport hηc
  have h : (fun p : ℝ × ℝ => EF.weilTest (windowSlice f η p.1) (windowSlice f η p.1) p.2) =
      fun p => ∫ t in Icc (-r) r, windowSlice f η p.1 t * conj (windowSlice f η p.1 (t - p.2)) := by
    funext p
    rw [weilTest_apply, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro t ht
    have hrt : r < |t| := by
      by_contra h'
      exact ht (abs_le.mp (not_lt.mp h'))
    simp [windowSlice, hηr t hrt]
  rw [h]
  refine continuous_parametric_integral_of_continuous ?_ isCompact_Icc
  change Continuous fun q : (ℝ × ℝ) × ℝ =>
    f (q.2 + q.1.1) * η q.2 * conj (f (q.2 - q.1.2 + q.1.1) * η (q.2 - q.1.2))
  fun_prop

/-- **Per-zero transfer.** The transform of the windowed kernel is the integral over offsets of
the transforms of the slice kernels. -/
theorem paperFT_windowedKernel_eq_integral {f η : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hη : Continuous η) (hηc : HasCompactSupport η) (z : ℂ) :
    paperFT (windowedKernel f η) z =
      ∫ s, paperFT (EF.weilTest (windowSlice f η s) (windowSlice f η s)) z := by
  obtain ⟨A, -, hfA⟩ := exists_radius_of_hasCompactSupport hfc
  obtain ⟨r, -, hηr⟩ := exists_radius_of_hasCompactSupport hηc
  have hG := continuous_weilTest_windowSlice hf hη hηc
  have hint : Integrable (Function.uncurry fun (s v : ℝ) =>
      EF.weilTest (windowSlice f η s) (windowSlice f η s) v * cexp (I * z * v))
      (volume.prod volume) := by
    refine integrable_of_continuous_of_vanish_box (A := A + r) (B := 2 * r) ?_ ?_
    · change Continuous fun p : ℝ × ℝ =>
        EF.weilTest (windowSlice f η p.1) (windowSlice f η p.1) p.2 * cexp (I * z * p.2)
      exact hG.mul (by fun_prop)
    · rintro ⟨s, v⟩ h
      simp only [Function.uncurry_apply_pair, weilTest_apply]
      have hzero : ∀ t, windowSlice f η s t * conj (windowSlice f η s (t - v)) = 0 := by
        intro t
        rcases h with h | h
        · rw [windowSlice_eq_zero_of_far hfA hηr h t, zero_mul]
        · by_cases ht : r < |t|
          · simp [windowSlice, hηr t ht]
          · have h2 : r < |t - v| := by
              have := abs_add_le (t - v) (-t)
              rw [abs_neg, show t - v + -t = -v by ring, abs_neg] at this
              linarith [not_lt.mp ht]
            simp [windowSlice, hηr (t - v) h2]
      simp [hzero]
  simp only [paperFT_def]
  rw [integral_integral_swap hint]
  congr 1 with v
  rw [integral_mul_const, integral_weilTest_windowSlice hf hfc hη hηc v]

/-! ### Uniform decay of the slices -/

/-- The slice transforms decay uniformly in the offset. -/
theorem exists_uniform_decay_windowSlice {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) {r : ℝ}
    (hηr : ∀ u, r < |u| → η u = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, ∀ z : ℂ,
      ‖paperFT (windowSlice f η s) z‖ ≤ Real.exp (|z.im| * r) * (4 * B) / (1 + |z.re|) ^ 2 := by
  set f1 := deriv f with hf1
  set f2 := deriv f1 with hf2
  set η1 := deriv η with hη1
  set η2 := deriv η1 with hη2
  have hf1c : ContDiff ℝ 1 f1 := hf.deriv'
  have hη1c : ContDiff ℝ 1 η1 := hη.deriv'
  have hf2cont : Continuous f2 := hf1c.continuous_deriv le_rfl
  have hη2cont : Continuous η2 := hη1c.continuous_deriv le_rfl
  obtain ⟨M₀, hM₀⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨M₁, hM₁⟩ := hf1c.continuous.bounded_above_of_compact_support hfc.deriv
  obtain ⟨M₂, hM₂⟩ := hf2cont.bounded_above_of_compact_support hfc.deriv.deriv
  have hηi : Integrable (fun u => ‖η u‖) :=
    hη.continuous.norm.integrable_of_hasCompactSupport hηc.norm
  have hη1i : Integrable (fun u => ‖η1 u‖) :=
    hη1c.continuous.norm.integrable_of_hasCompactSupport hηc.deriv.norm
  have hη2i : Integrable (fun u => ‖η2 u‖) :=
    hη2cont.norm.integrable_of_hasCompactSupport hηc.deriv.deriv.norm
  set N₀ := ∫ u, ‖η u‖
  set N₁ := ∫ u, ‖η1 u‖
  set N₂ := ∫ u, ‖η2 u‖
  have hN₀ : 0 ≤ N₀ := integral_nonneg fun _ => norm_nonneg _
  have hN₁ : 0 ≤ N₁ := integral_nonneg fun _ => norm_nonneg _
  have hN₂ : 0 ≤ N₂ := integral_nonneg fun _ => norm_nonneg _
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  refine ⟨M₀ * N₀ + (M₂ * N₀ + 2 * M₁ * N₁ + M₀ * N₂), by positivity, fun s z => ?_⟩
  have hfd : ∀ x, HasDerivAt f (f1 x) x := fun x =>
    (hf.differentiable (by norm_num) x).hasDerivAt
  have hf1d : ∀ x, HasDerivAt f1 (f2 x) x := fun x =>
    (hf1c.differentiable (by norm_num) x).hasDerivAt
  have hηd : ∀ x, HasDerivAt η (η1 x) x := fun x =>
    (hη.differentiable (by norm_num) x).hasDerivAt
  have hη1d : ∀ x, HasDerivAt η1 (η2 x) x := fun x =>
    (hη1c.differentiable (by norm_num) x).hasDerivAt
  have hd1 : deriv (windowSlice f η s) = fun u => f1 (u + s) * η u + f (u + s) * η1 u := by
    funext u
    exact (((hfd (u + s)).comp_add_const u s).mul (hηd u)).deriv
  have hd2 : deriv (deriv (windowSlice f η s)) = fun u =>
      (f2 (u + s) * η u + f1 (u + s) * η1 u) + (f1 (u + s) * η1 u + f (u + s) * η2 u) := by
    rw [hd1]
    funext u
    exact ((((hf1d (u + s)).comp_add_const u s).mul (hηd u)).add
      (((hfd (u + s)).comp_add_const u s).mul (hη1d u))).deriv
  have hsupp : ∀ u, windowSlice f η s u ≠ 0 → |u| ≤ r := fun u hu => by
    by_contra h
    exact hu (by simp [windowSlice, hηr u (not_le.mp h)])
  have hdecay := norm_paperFT_le_decay (windowSlice_contDiff hf hη s) hsupp z
  have hI0 : ∫ u, ‖windowSlice f η s u‖ ≤ M₀ * N₀ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (hηi.const_mul M₀) (Eventually.of_forall fun u => ?_)
    simp only [windowSlice, norm_mul]
    exact mul_le_mul_of_nonneg_right (hM₀ _) (norm_nonneg _)
  have hI2 : ∫ u, ‖deriv (deriv (windowSlice f η s)) u‖ ≤ M₂ * N₀ + 2 * M₁ * N₁ + M₀ * N₂ := by
    rw [hd2]
    have hbound : Integrable (fun u => M₂ * ‖η u‖ + 2 * M₁ * ‖η1 u‖ + M₀ * ‖η2 u‖) :=
      ((hηi.const_mul M₂).add (hη1i.const_mul (2 * M₁))).add (hη2i.const_mul M₀)
    calc ∫ u, ‖(f2 (u + s) * η u + f1 (u + s) * η1 u) + (f1 (u + s) * η1 u + f (u + s) * η2 u)‖
        ≤ ∫ u, (M₂ * ‖η u‖ + 2 * M₁ * ‖η1 u‖ + M₀ * ‖η2 u‖) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hbound
            (Eventually.of_forall fun u => ?_)
          have e1 := hM₂ (u + s)
          have e2 := hM₁ (u + s)
          have e3 := hM₀ (u + s)
          calc ‖(f2 (u + s) * η u + f1 (u + s) * η1 u) + (f1 (u + s) * η1 u + f (u + s) * η2 u)‖
              ≤ ‖f2 (u + s)‖ * ‖η u‖ + ‖f1 (u + s)‖ * ‖η1 u‖ +
                  (‖f1 (u + s)‖ * ‖η1 u‖ + ‖f (u + s)‖ * ‖η2 u‖) := by
                refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_)
                  ((norm_add_le _ _).trans ?_)) <;> rw [norm_mul, norm_mul]
            _ ≤ M₂ * ‖η u‖ + M₁ * ‖η1 u‖ + (M₁ * ‖η1 u‖ + M₀ * ‖η2 u‖) := by
                gcongr
            _ = M₂ * ‖η u‖ + 2 * M₁ * ‖η1 u‖ + M₀ * ‖η2 u‖ := by ring
      _ = M₂ * N₀ + 2 * M₁ * N₁ + M₀ * N₂ := by
          rw [integral_add (f := fun u => M₂ * ‖η u‖ + 2 * M₁ * ‖η1 u‖)
            (g := fun u => M₀ * ‖η2 u‖) ((hηi.const_mul M₂).add (hη1i.const_mul (2 * M₁)))
            (hη2i.const_mul M₀), integral_add (f := fun u => M₂ * ‖η u‖)
            (g := fun u => 2 * M₁ * ‖η1 u‖) (hηi.const_mul M₂) (hη1i.const_mul (2 * M₁)),
            integral_const_mul, integral_const_mul, integral_const_mul]
  refine hdecay.trans ?_
  gcongr

/-! ### The transfer law -/

theorem countable_carrier (Z : ZeroConfig) : Z.carrier.Countable := by
  have h : Z.carrier ⊆ ⋃ n : ℕ, Z.carrier ∩ {ρ | (-(n : ℝ)) < ρ.im ∧ ρ.im ≤ n} := by
    intro ρ hρ
    obtain ⟨n, hn⟩ := exists_nat_gt |ρ.im|
    exact Set.mem_iUnion.mpr ⟨n, hρ, by linarith [neg_abs_le ρ.im], by linarith [le_abs_self ρ.im]⟩
  exact (Set.countable_iUnion fun n => (Z.finite_window _ _).countable).mono h

/-- The transform of a slice is continuous in the offset. -/
theorem continuous_paperFT_windowSlice {f η : ℝ → ℂ} (hf : Continuous f) (hη : Continuous η)
    (hηc : HasCompactSupport η) (z : ℂ) :
    Continuous fun s => paperFT (windowSlice f η s) z := by
  obtain ⟨r, -, hηr⟩ := exists_radius_of_hasCompactSupport hηc
  have h : (fun s => paperFT (windowSlice f η s) z) =
      fun s => ∫ u in Icc (-r) r, windowSlice f η s u * cexp (I * z * u) := by
    funext s
    rw [paperFT_def, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    have hru : r < |u| := by
      by_contra h'
      exact hu (abs_le.mp (not_lt.mp h'))
    simp [windowSlice, hηr u hru]
  rw [h]
  refine continuous_parametric_integral_of_continuous ?_ isCompact_Icc
  change Continuous fun q : ℝ × ℝ => f (q.2 + q.1) * η q.2 * cexp (I * z * q.2)
  fun_prop

/-- **The slice transfer law.** For a tempered configuration, the windowed Weil form is the
integral over offsets of the Weil forms of the slices. -/
theorem windowedW_eq_integral_W (Z : ZeroConfig) (hZ : TemperedConfig Z) {f η : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) :
    windowedW Z f η = ∫ s, Z.W (windowSlice f η s) (windowSlice f η s) := by
  haveI : Countable Z.carrier := (countable_carrier Z).to_subtype
  obtain ⟨A, -, hfA⟩ := exists_radius_of_hasCompactSupport hfc
  obtain ⟨r, hr0, hηr⟩ := exists_radius_of_hasCompactSupport hηc
  obtain ⟨B, hB0, hB⟩ := exists_uniform_decay_windowSlice hf hfc hη hηc hηr
  set F : Z.carrier → ℝ → ℂ := fun ρ s =>
    Z.Wsummand (windowSlice f η s) (windowSlice f η s) ρ with hF
  have hslc : ∀ s, Continuous (windowSlice f η s) := fun s =>
    (windowSlice_contDiff hf hη s).continuous
  have hslcs : ∀ s, HasCompactSupport (windowSlice f η s) := fun s =>
    HasCompactSupport.intro (isCompact_Icc (a := -r) (b := r)) fun u hu => by
      have hru : r < |u| := by
        by_contra h'
        exact hu (abs_le.mp (not_lt.mp h'))
      simp [windowSlice, hηr u hru]
  have hFeq : ∀ ρ : Z.carrier, ∀ s, F ρ s = (Z.mult ρ : ℂ) *
      paperFT (EF.weilTest (windowSlice f η s) (windowSlice f η s)) (gammaOf ρ) := by
    intro ρ s
    simp only [hF]
    rw [ZeroConfig.Wsummand, EF.paperFT_weilTest (hslc s) (hslc s) (hslcs s) (hslcs s),
      mul_assoc]
  have hper : ∀ ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (windowedKernel f η) (gammaOf ρ) =
      ∫ s, F ρ s := by
    intro ρ
    rw [paperFT_windowedKernel_eq_integral hf.continuous hfc hη.continuous hηc,
      ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun s => (hFeq ρ s).symm)
  -- each `F ρ` is continuous and vanishes for large offsets
  have hFcont : ∀ ρ : Z.carrier, Continuous (F ρ) := by
    intro ρ
    have h1 := continuous_paperFT_windowSlice hf.continuous hη.continuous hηc (gammaOf ρ)
    have h2 := continuous_paperFT_windowSlice hf.continuous hη.continuous hηc
      (conj (gammaOf ρ))
    simp only [hF, ZeroConfig.Wsummand]
    exact (continuous_const.mul h1).mul (Complex.continuous_conj.comp h2)
  have hFzero : ∀ ρ : Z.carrier, ∀ s, A + r < |s| → F ρ s = 0 := by
    intro ρ s hs
    have h0 : windowSlice f η s = 0 := funext (windowSlice_eq_zero_of_far hfA hηr hs)
    simp [hF, ZeroConfig.Wsummand, h0, paperFT_def]
  have hFint : ∀ ρ : Z.carrier, Integrable (F ρ) := fun ρ =>
    (hFcont ρ).integrable_of_hasCompactSupport (HasCompactSupport.intro
      (isCompact_Icc (a := -(A + r)) (b := A + r)) fun s hs => hFzero ρ s (by
        by_contra h'
        exact hs (abs_le.mp (not_lt.mp h'))))
  -- the uniform zero-side bound
  set E : ℝ := Real.exp (r / 2) * (4 * B) with hE
  set V : ℝ := volume.real (Icc (-(A + r)) (A + r)) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  have hptw : ∀ ρ : Z.carrier, ∀ s, ‖F ρ s‖ ≤
      E ^ 2 * (5 / 4) * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ s
    have hstrip := Z.strip ρ ρ.2
    have him : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := WeilEF.abs_gammaOf_im_le hstrip
    have hb1 := hB s (gammaOf ρ)
    have hb2 := hB s (conj (gammaOf ρ))
    rw [Complex.conj_im, Complex.conj_re, abs_neg] at hb2
    have hexp : Real.exp (|(gammaOf (ρ : ℂ)).im| * r) ≤ Real.exp (r / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg (gammaOf (ρ : ℂ)).im])
    set x := (gammaOf (ρ : ℂ)).re
    have hden : 0 < (1 + |x|) ^ 2 := by positivity
    have hb1' : ‖paperFT (windowSlice f η s) (gammaOf ρ)‖ ≤ E / (1 + |x|) ^ 2 :=
      hb1.trans (by rw [hE]; gcongr)
    have hb2' : ‖paperFT (windowSlice f η s) (conj (gammaOf ρ))‖ ≤ E / (1 + |x|) ^ 2 :=
      hb2.trans (by rw [hE]; gcongr)
    have hnsq : Complex.normSq (gammaOf (ρ : ℂ)) ≤ x ^ 2 + 1 / 4 := by
      have him2 : (gammaOf (ρ : ℂ)).im * (gammaOf (ρ : ℂ)).im ≤ 1 / 4 := by
        rw [← abs_mul_abs_self]
        nlinarith [abs_nonneg (gammaOf (ρ : ℂ)).im]
      rw [Complex.normSq_apply, sq]
      linarith
    have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    have hE0 : 0 ≤ E := by rw [hE]; positivity
    simp only [hF]
    rw [ZeroConfig.Wsummand, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_natCast]
    have hq : (1 + Complex.normSq (gammaOf (ρ : ℂ))) ≤ 5 / 4 * (1 + |x|) ^ 2 * (1 + |x|) ^ 2 := by
      have h1 : 1 ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x]
      have h3 : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
      have h4 : (1 + |x|) ^ 2 ≤ (1 + |x|) ^ 2 * (1 + |x|) ^ 2 := by nlinarith
      nlinarith
    have hpos : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
      linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
    calc (Z.mult ρ : ℝ) * ‖paperFT (windowSlice f η s) (gammaOf ρ)‖ *
          ‖paperFT (windowSlice f η s) (conj (gammaOf ρ))‖
        ≤ (Z.mult ρ : ℝ) * (E / (1 + |x|) ^ 2) * (E / (1 + |x|) ^ 2) := by
          gcongr
      _ = ((Z.mult ρ : ℝ) * E ^ 2) / ((1 + |x|) ^ 2 * (1 + |x|) ^ 2) := by
          field_simp
      _ ≤ ((Z.mult ρ : ℝ) * E ^ 2) / ((1 + Complex.normSq (gammaOf (ρ : ℂ))) / (5 / 4)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by
            rw [div_le_iff₀ (by norm_num)]; linarith)
      _ = E ^ 2 * (5 / 4) * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
          field_simp
  have hFsum : Summable fun ρ : Z.carrier => ∫ s, ‖F ρ s‖ := by
    refine Summable.of_nonneg_of_le (fun ρ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) (hZ.mul_left (V * (E ^ 2 * (5 / 4))))
    have hset : ∫ s, ‖F ρ s‖ = ∫ s in Icc (-(A + r)) (A + r), ‖F ρ s‖ := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro s hs
      rw [hFzero ρ s (by
        by_contra h'
        exact hs (abs_le.mp (not_lt.mp h'))), norm_zero]
    rw [hset]
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-(A + r)) (A + r))
      (f := fun s => ‖F ρ s‖) measure_Icc_lt_top (fun s _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hptw ρ s)
    rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Icc
      fun _ _ => norm_nonneg _)] at hb
    calc ∫ s in Icc (-(A + r)) (A + r), ‖F ρ s‖
        ≤ E ^ 2 * (5 / 4) * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) * V := hb
      _ = V * (E ^ 2 * (5 / 4)) * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
          ring
  rw [windowedW, tsum_congr hper, integral_tsum_of_summable_integral_norm hFint hFsum]
  rfl

/-- **Positivity transfer.** If a tempered configuration is Weil-nonnegative at aperture `r`, then
every windowed form whose window is supported in `[-r, r]` is nonnegative, whatever the aperture
of the test. -/
theorem re_windowedW_nonneg_of_aperture_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {r : ℝ} (hpos : ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Icc (-r) r → 0 ≤ (Z.W g g).re)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-r) r) : 0 ≤ (windowedW Z f η).re := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  rw [windowedW_eq_integral_W Z hZ hf hfc hη hηc]
  by_cases hint : Integrable fun s => Z.W (windowSlice f η s) (windowSlice f η s)
  · have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    exact integral_nonneg fun s => hpos _ (windowSlice_contDiff hf hη s)
      ((tsupport_windowSlice_subset f η s).trans hηs)
  · rw [integral_undef hint, Complex.zero_re]

end GaloisForLFunctions.SquareRootThreshold
