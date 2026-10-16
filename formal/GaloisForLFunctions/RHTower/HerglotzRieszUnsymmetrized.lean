import GaloisForLFunctions.RHTower.HerglotzDirichletCarrierRigidity

/-!
# Unsymmetrised Herglotz–Riesz representation and Poisson support

Let `Φ` be holomorphic on `Re s > ½` with `Re Φ ≥ 0`.  No conjugation symmetry is assumed.

* `exists_hrKernel_representation`: there are a finite measure `ν` on angles and a real `c` with
  `Re Φ(s) = ∫ P(w, e^{iθ}) dν(θ)` and `Φ(s) = ∫ (e^{iθ} + w)/(e^{iθ} − w) dν(θ) + ic`,
  `w = discPt s`.  The kernel integral is holomorphic by dominated differentiation, its real part
  is the Poisson integral, so the difference with `Φ` is an imaginary constant.
* `measure_ordinate_open_eq_zero_of_poisson`: if `Re Φ(s) → 0` as `s → ½ + it` inside the
  half-plane for every `t` in an open set `U`, then `ν` gives no mass to the circle points `ζ ≠ 1`
  whose ordinate lies in `U`.  The Poisson kernel at `½ + ε + it` is at least `1/(2ε)` on the
  arc `|γ − t| ≤ ε`, so `ν` of that arc is at most `2ε Re Φ(½ + ε + it)`; uniform smallness on
  compact subintervals and a covering by `O((b − a)/ε)` arcs finish the argument.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal ComplexConjugate

noncomputable section

namespace RHTower.AtomDomination

open GaloisForLFunctions.HTGeometry

/-! ## The kernel in the disc variable -/

/-- The Herglotz–Riesz kernel `(ζ + w)/(ζ − w)` in the disc variable. -/
def hrDisk (w ζ : ℂ) : ℂ := (ζ + w) / (ζ - w)

/-- Its derivative in `w`. -/
def hrDiskDeriv (w ζ : ℂ) : ℂ := 2 * ζ / (ζ - w) ^ 2

theorem hrKernel_eq_hrDisk (s ζ : ℂ) : hrKernel s ζ = hrDisk (discPt s) ζ := rfl

theorem continuous_hrDisk_comp {X : Type*} [TopologicalSpace X] {w ζ : X → ℂ}
    (hw : Continuous w) (hζ : Continuous ζ) (hw1 : ∀ x, ‖w x‖ < 1) (hζ1 : ∀ x, ‖ζ x‖ = 1) :
    Continuous fun x => hrDisk (w x) (ζ x) := by
  have hne : ∀ x, ζ x - w x ≠ 0 := fun x => sub_ne_zero_of_norm (hζ1 x) (hw1 x)
  unfold hrDisk
  exact (hζ.add hw).div (hζ.sub hw) hne

theorem continuous_hrDiskDeriv_comp {X : Type*} [TopologicalSpace X] {w ζ : X → ℂ}
    (hw : Continuous w) (hζ : Continuous ζ) (hw1 : ∀ x, ‖w x‖ < 1) (hζ1 : ∀ x, ‖ζ x‖ = 1) :
    Continuous fun x => hrDiskDeriv (w x) (ζ x) := by
  have hne : ∀ x, ζ x - w x ≠ 0 := fun x => sub_ne_zero_of_norm (hζ1 x) (hw1 x)
  unfold hrDiskDeriv
  exact (continuous_const.mul hζ).div ((hζ.sub hw).pow 2) fun x => pow_ne_zero 2 (hne x)

theorem norm_hrDiskDeriv_le {w ζ : ℂ} {ε : ℝ} (hε : 0 < ε) (hζ : ‖ζ‖ = 1)
    (h1 : ε ≤ ‖ζ - w‖) : ‖hrDiskDeriv w ζ‖ ≤ 2 / ε ^ 2 := by
  unfold hrDiskDeriv
  rw [norm_div, norm_mul, norm_pow, hζ, Complex.norm_two, mul_one]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hε.le h1 2)

theorem hasDerivAt_hrDisk {w ζ : ℂ} (h : ζ - w ≠ 0) :
    HasDerivAt (fun x => hrDisk x ζ) (hrDiskDeriv w ζ) w :=
  hasDerivAt_hr h

theorem integrable_hrDisk {ν : Measure ℝ} [IsFiniteMeasure ν] {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (fun θ => hrDisk w (circleMap 0 1 θ)) ν :=
  (integrable_const (2 / (1 - ‖w‖))).mono'
    (continuous_hrDisk_comp continuous_const (continuous_circleMap 0 1) (fun _ => hw)
      norm_circleMap_one).aestronglyMeasurable
    (ae_of_all _ fun θ => norm_hr_le hw (norm_circleMap_one θ))

/-- `Re (ζ + w)/(ζ − w) = P(w, ζ)` for `|ζ| = 1`. -/
theorem re_hrDisk (w ζ : ℂ) : (hrDisk w ζ).re = poissonKernel 0 w ζ := by
  have h := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := w)) ζ
  rw [h, Function.comp_apply, herglotzRieszKernel_def]
  simp [hrDisk]

/-- The unsymmetrised Herglotz–Riesz integral `∫ (e^{iθ} + w)/(e^{iθ} − w) dν(θ)`. -/
def diskHr (ν : Measure ℝ) (w : ℂ) : ℂ := ∫ θ, hrDisk w (circleMap 0 1 θ) ∂ν

theorem differentiableAt_diskHr {ν : Measure ℝ} [IsFiniteMeasure ν] {w₀ : ℂ}
    (hw₀ : ‖w₀‖ < 1) : DifferentiableAt ℂ (diskHr ν) w₀ := by
  set ε : ℝ := (1 - ‖w₀‖) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hball : ∀ w ∈ Metric.ball w₀ ε, ‖w‖ < 1 ∧ ∀ θ : ℝ, ε ≤ ‖circleMap 0 1 θ - w‖ := by
    intro w hw
    have hd : ‖w - w₀‖ < ε := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have hnw : ‖w‖ < ‖w₀‖ + ε := by linarith [norm_sub_norm_le w w₀]
    refine ⟨by rw [hε] at hnw; linarith, fun θ => ?_⟩
    have := one_sub_norm_le_norm_sub (w := w) (norm_circleMap_one θ)
    rw [hε] at hnw ⊢
    linarith
  have hmem : Metric.ball w₀ ε ∈ 𝓝 w₀ := Metric.ball_mem_nhds w₀ hε0
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun w θ => hrDisk w (circleMap 0 1 θ))
    (F' := fun w θ => hrDiskDeriv w (circleMap 0 1 θ)) (bound := fun _ => 2 / ε ^ 2) hmem
    (Filter.eventually_of_mem hmem fun w hw => (integrable_hrDisk (hball w hw).1).1)
    (integrable_hrDisk hw₀)
    (continuous_hrDiskDeriv_comp continuous_const (continuous_circleMap 0 1) (fun _ => hw₀)
      norm_circleMap_one).aestronglyMeasurable
    (ae_of_all _ fun θ w hw => norm_hrDiskDeriv_le hε0 (norm_circleMap_one θ)
      ((hball w hw).2 θ))
    (integrable_const _)
    (ae_of_all _ fun θ w hw => hasDerivAt_hrDisk
      (norm_pos_iff.mp (lt_of_lt_of_le hε0 ((hball w hw).2 θ))))
  exact hderiv.differentiableAt

/-! ## The representation -/

/-- **Unsymmetrised Herglotz–Riesz representation.**  A holomorphic `Φ` with `Re Φ ≥ 0` on
`Re s > ½` is `∫ (e^{iθ} + w)/(e^{iθ} − w) dν(θ) + ic`, `w = discPt s`, for a finite measure `ν`
whose Poisson integral is `Re Φ`. -/
theorem exists_hrKernel_representation {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      (∀ s : ℂ, 1 / 2 < s.re →
        ∫ θ, poissonKernel 0 (discPt s) (circleMap 0 1 θ) ∂ν = (Φ s).re) ∧
      ∃ c : ℝ, ∀ s : ℂ, 1 / 2 < s.re →
        Φ s = (∫ θ, hrKernel s (circleMap 0 1 θ) ∂ν) + c * I := by
  obtain ⟨ν, hfin, hrep⟩ := exists_poissonRepresentation_halfPlane hΦd hΦre
  refine ⟨ν, hfin, hrep, ?_⟩
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsConnected U := (convex_halfSpace_re_gt (1 / 2)).isConnected
    ⟨1, show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num⟩
  set Ψ : ℂ → ℂ := fun s => diskHr ν (discPt s) with hΨ
  have hΨd : DifferentiableOn ℂ Ψ U := fun s hs =>
    ((differentiableAt_diskHr (norm_discPt_lt_one hs)).comp s
      (differentiableAt_discPt hs)).differentiableWithinAt
  have hreΨ : ∀ s ∈ U, (Ψ s).re = (Φ s).re := by
    intro s hs
    have hs' : 1 / 2 < s.re := hs
    have hw := norm_discPt_lt_one hs'
    simp only [hΨ, diskHr]
    have hre : (∫ θ, hrDisk (discPt s) (circleMap 0 1 θ) ∂ν).re =
        ∫ θ, (hrDisk (discPt s) (circleMap 0 1 θ)).re ∂ν :=
      (integral_re (integrable_hrDisk hw)).symm
    rw [hre]
    simp_rw [re_hrDisk]
    exact hrep s hs'
  have hre0 : ∀ s ∈ U, ((Φ - Ψ) s).re = 0 := fun s hs => by
    rw [Pi.sub_apply, Complex.sub_re, hreΨ s hs, sub_self]
  obtain ⟨c, hc⟩ := ((hΦd.sub hΨd).analyticOnNhd hUo).eq_re_add_const_mul_I_of_re_eq_const
    hre0 hUo hUc
  refine ⟨c, fun s hs => ?_⟩
  have h := hc s hs
  rw [Pi.sub_apply, Complex.ofReal_zero, zero_add, sub_eq_iff_eq_add] at h
  rw [h, add_comm]
  rfl

/-! ## Poisson support -/

/-- **The Poisson lower bound.**  `ν{ζ ≠ 1, |γ − t| ≤ ε} ≤ 4ε Re Φ(½ + ε + it)`. -/
theorem measure_ordinate_ball_le_of_poisson {Φ : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hrep : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ θ, poissonKernel 0 (discPt s) (circleMap 0 1 θ) ∂ν = (Φ s).re)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ν {θ | circleMap 0 1 θ ≠ 1 ∧ |angleOrd θ - t| ≤ ε} ≤
      ENNReal.ofReal (4 * ε * (Φ ((1 / 2 : ℂ) + ε + t * I)).re) := by
  set s : ℂ := (1 / 2 : ℂ) + ε + t * I with hsdef
  have hsre : s.re = 1 / 2 + ε := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hs : 1 / 2 < s.re := by rw [hsre]; linarith
  set A := {θ : ℝ | circleMap 0 1 θ ≠ 1 ∧ |angleOrd θ - t| ≤ ε} with hA
  have hAm : MeasurableSet A :=
    measurableSet_circleMap_eq_one.compl.inter
      (measurableSet_le (measurable_angleOrd.sub_const t).abs measurable_const)
  set g : ℝ → ℝ := fun θ => poissonKernel 0 (discPt s) (circleMap 0 1 θ) with hg
  have hw := norm_discPt_lt_one hs
  have hgi : Integrable g ν := integrable_poissonKernel_circleMap hw
  have hg0 : ∀ θ, 0 ≤ g θ := fun θ => poissonKernel_circleMap_one_nonneg hw θ
  have hre : (Φ s).re = ∫ θ, g θ ∂ν := (hrep s hs).symm
  have hlow : ∀ θ ∈ A, 1 / (2 * ε) ≤ g θ := by
    intro θ hθ
    have hζ := norm_circleMap_one θ
    have hb := eq_bdryPt_circleOrd hζ hθ.1
    simp only [hg]
    rw [hb, poissonKernel_discPt_bdryPt hs, hsre, hsim]
    set γ := circleOrd (circleMap 0 1 θ)
    have hγ : |γ - t| ≤ ε := hθ.2
    have hsq : (t - γ) ^ 2 ≤ ε ^ 2 := by
      rw [← sq_abs, abs_sub_comm]
      exact pow_le_pow_left₀ (abs_nonneg _) hγ 2
    have e : (1 / 2 + ε - 1 / 2 : ℝ) = ε := by ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg γ, mul_pos hε hε]
  have h1 : ∫ θ in A, g θ ∂ν ≤ ∫ θ, g θ ∂ν :=
    setIntegral_le_integral hgi (Eventually.of_forall hg0)
  have h2 : ν.real A • (1 / (2 * ε)) ≤ ∫ θ in A, g θ ∂ν :=
    setIntegral_ge_of_const_le hAm (measure_ne_top ν A) hlow hgi.integrableOn
  rw [smul_eq_mul] at h2
  have h3 : ν.real A ≤ 4 * ε * (Φ s).re := by
    rw [hre]
    have := h2.trans h1
    rw [mul_one_div, div_le_iff₀ (by positivity)] at this
    have hnn : 0 ≤ ∫ θ, g θ ∂ν := integral_nonneg hg0
    nlinarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν A)]
  exact ENNReal.ofReal_le_ofReal h3

/-- The ordinates of `ν` avoid every compact `[a, b] ⊆ U` on which `Re Φ` vanishes at the
boundary. -/
theorem measure_ordinate_Icc_eq_zero_of_poisson {Φ : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hrep : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ θ, poissonKernel 0 (discPt s) (circleMap 0 1 θ) ∂ν = (Φ s).re)
    {U : Set ℝ} (hlim : ∀ t ∈ U, Tendsto (fun s => (Φ s).re)
      (𝓝[{s : ℂ | 1 / 2 < s.re}] ((1 / 2 : ℂ) + t * I)) (𝓝 0))
    {a b : ℝ} (hab : Icc a b ⊆ U) :
    ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Icc a b} = 0 := by
  set S := {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Icc a b} with hSdef
  rcases lt_or_ge b a with hba | hab'
  · refine measure_mono_null (fun θ hθ => ?_) measure_empty
    exact absurd (hθ.2.1.trans hθ.2.2) (not_le.mpr hba)
  have hbound : ∀ η > 0, ν S ≤ ENNReal.ofReal ((2 * (b - a) + 8) * η) := by
    intro η hη
    obtain ⟨ε₀, hε₀, hunif⟩ := exists_uniform_re_le hab hlim hη
    set ε := min ε₀ 1 with hεdef
    have hε : 0 < ε := lt_min hε₀ one_pos
    have hε1 : ε ≤ 1 := min_le_right _ _
    set M : ℕ := ⌈(b - a) / (2 * ε)⌉₊ with hM
    set ctr : ℕ → ℝ := fun j => min (a + 2 * j * ε) b with hctr
    have hctr_mem : ∀ j, ctr j ∈ Icc a b := by
      intro j
      have h0 : (0 : ℝ) ≤ 2 * j * ε := by positivity
      exact ⟨le_min (by linarith) hab', min_le_right _ _⟩
    have hcover : S ⊆ ⋃ j ∈ Finset.range (M + 1),
        {θ | circleMap 0 1 θ ≠ 1 ∧ |angleOrd θ - ctr j| ≤ ε} := by
      intro θ hθ
      obtain ⟨h1, hγa, hγb⟩ := hθ
      set γ := angleOrd θ with hγ
      set x : ℝ := (γ - a) / (2 * ε) with hx
      have hx0 : 0 ≤ x := div_nonneg (by linarith) (by positivity)
      set j : ℕ := ⌊x + 1 / 2⌋₊ with hj
      have hj1 : (j : ℝ) ≤ x + 1 / 2 := Nat.floor_le (by linarith)
      have hj2 : x + 1 / 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
      have hxM : x ≤ M := by
        refine le_trans ?_ (Nat.le_ceil _)
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      have hjM : j < M + 1 := by
        have : (j : ℝ) < (M : ℝ) + 1 := by linarith
        exact_mod_cast this
      refine Set.mem_biUnion (Finset.mem_range.mpr hjM) ⟨h1, ?_⟩
      have hxe : x * (2 * ε) = γ - a := by rw [hx]; field_simp
      have hclose : |γ - (a + 2 * j * ε)| ≤ ε := by
        rw [abs_le]
        constructor <;> nlinarith
      show |γ - ctr j| ≤ ε
      by_cases hc : a + 2 * j * ε ≤ b
      · rw [hctr]
        simp only [min_eq_left hc]
        exact hclose
      · push Not at hc
        rw [hctr]
        simp only [min_eq_right hc.le]
        rw [abs_le] at hclose ⊢
        constructor <;> linarith [hclose.1]
    calc ν S ≤ ν (⋃ j ∈ Finset.range (M + 1),
          {θ | circleMap 0 1 θ ≠ 1 ∧ |angleOrd θ - ctr j| ≤ ε}) := measure_mono hcover
      _ ≤ ∑ j ∈ Finset.range (M + 1), ν {θ | circleMap 0 1 θ ≠ 1 ∧ |angleOrd θ - ctr j| ≤ ε} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range (M + 1), ENNReal.ofReal (4 * ε * η) := by
          refine Finset.sum_le_sum fun j _ =>
            (measure_ordinate_ball_le_of_poisson hrep (ctr j) hε).trans ?_
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (hunif (ctr j) (hctr_mem j) ε hε (min_le_left _ _)) (by positivity))
      _ = ENNReal.ofReal (((M : ℝ) + 1) * (4 * ε * η)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1)]
          congr 1
          rw [← ENNReal.ofReal_natCast, Nat.cast_add, Nat.cast_one]
      _ ≤ ENNReal.ofReal ((2 * (b - a) + 8) * η) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hM1 : (M : ℝ) ≤ (b - a) / (2 * ε) + 1 := (Nat.ceil_lt_add_one (by
            exact div_nonneg (by linarith) (by positivity))).le
          have hMe : (M : ℝ) * (2 * ε) ≤ (b - a) + 2 * ε := by
            have := mul_le_mul_of_nonneg_right hM1 (by positivity : (0 : ℝ) ≤ 2 * ε)
            rw [add_mul, div_mul_cancel₀ _ (by positivity)] at this
            linarith
          nlinarith
  have hfin : ν S ≠ ⊤ := measure_ne_top ν S
  have hle : ∀ η > 0, (ν S).toReal ≤ (2 * (b - a) + 8) * η := fun η hη =>
    (ENNReal.toReal_le_of_le_ofReal (by nlinarith) (hbound η hη))
  have h0 : (ν S).toReal ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hC : 0 < 2 * (b - a) + 8 := by linarith
    have := hle (δ / (2 * (b - a) + 8)) (div_pos hδ hC)
    rw [mul_div_cancel₀ _ hC.ne'] at this
    linarith
  have := ENNReal.toReal_nonneg (a := ν S)
  rw [← ENNReal.ofReal_toReal hfin, show (ν S).toReal = 0 by linarith, ENNReal.ofReal_zero]

/-- **Poisson support.**  The ordinates of `ν` avoid every open set on which `Re Φ` vanishes at
the boundary. -/
theorem measure_ordinate_open_eq_zero_of_poisson {Φ : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hrep : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ θ, poissonKernel 0 (discPt s) (circleMap 0 1 θ) ∂ν = (Φ s).re)
    {U : Set ℝ} (hU : IsOpen U) (hlim : ∀ t ∈ U, Tendsto (fun s => (Φ s).re)
      (𝓝[{s : ℂ | 1 / 2 < s.re}] ((1 / 2 : ℂ) + t * I)) (𝓝 0)) :
    ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ U} = 0 := by
  have hsub : {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ U} ⊆
      ⋃ p : ℚ × ℚ, {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Icc (p.1 : ℝ) p.2 ∧
        Icc (p.1 : ℝ) p.2 ⊆ U} := by
    intro θ hθ
    obtain ⟨h1, hγ⟩ := hθ
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU _ hγ
    obtain ⟨q1, hq1a, hq1b⟩ := exists_rat_btwn (show angleOrd θ - δ < angleOrd θ by linarith)
    obtain ⟨q2, hq2a, hq2b⟩ := exists_rat_btwn (show angleOrd θ < angleOrd θ + δ by linarith)
    refine Set.mem_iUnion.mpr ⟨(q1, q2), ?_⟩
    simp only [Set.mem_setOf_eq]
    refine ⟨h1, ⟨hq1b.le, hq2a.le⟩, fun r hr => hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  refine measure_mono_null hsub (measure_iUnion_null fun p => ?_)
  by_cases hp : Icc (p.1 : ℝ) p.2 ⊆ U
  · refine measure_mono_null (fun θ hθ => ?_)
      (measure_ordinate_Icc_eq_zero_of_poisson hrep hlim hp)
    exact ⟨hθ.1, hθ.2.1⟩
  · refine measure_mono_null (fun θ hθ => ?_) measure_empty
    exact hp hθ.2.2

end RHTower.AtomDomination
