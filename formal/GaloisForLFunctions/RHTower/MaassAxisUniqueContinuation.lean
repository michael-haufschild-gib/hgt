import Mathlib

/-!
# Unique continuation of quarter eigenfunctions from the imaginary axis

Write `∂ᵥF(z) = DF(z)v` for the real directional derivative of `F : ℂ → ℂ`, and call `F` a
*quarter eigenfunction* on the upper half-plane if

`∂₁∂₁F + ∂ᵢ∂ᵢF + F/(4y²) = 0`  (`quarterDefect F = 0`),

i.e. `−y²(∂ₓ² + ∂ᵧ²)F = F/4`: an eigenfunction of the hyperbolic Laplacian with eigenvalue `1/4`.

**Theorem** (`eq_zero_of_axis`).  Let `V` be smooth on the upper half-plane, a quarter
eigenfunction, even under the reflection `z ↦ −z̄`, vanishing on the imaginary axis, and real-analytic
along every horizontal line.  Then `V = 0`.

**Proof.**  The operator `∂₁` commutes with `∂ᵢ` (symmetry of second derivatives) and with
multiplication by functions of `y`, so every `Wⱼ = ∂₁ʲV` is again a smooth quarter eigenfunction
(`quarterDefect_dirD_one`).  If a smooth quarter eigenfunction `W` vanishes on the axis, so do its
derivatives along the axis, and the equation gives `∂₁∂₁W = −∂ᵢ∂ᵢW − W/(4y²) = 0` there
(`dirD_one_dirD_one_axis`).  `W₀ = V` and `W₁ = ∂₁V` (by evenness) vanish on the axis, hence all
`Wⱼ` do.  On the line `y = y₀` the `j`-th derivative of `x ↦ V(x + iy₀)` at `0` is `Wⱼ(iy₀) = 0`, so
this analytic function has infinite order at `0` and vanishes identically.
-/

open Complex Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RHTower.MaassAxisContinuation

/-- The open upper half-plane as a subset of `ℂ`. -/
def upper : Set ℂ := {z | 0 < z.im}

theorem isOpen_upper : IsOpen upper := isOpen_lt continuous_const continuous_im

/-- The real directional derivative `∂ᵥF(z) = DF(z) v`. -/
def dirD (v : ℂ) (F : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ F z v

/-- The weight `1/(4y²)`. -/
def quarterWeight (z : ℂ) : ℝ := (4 * z.im ^ 2)⁻¹

/-- The quarter defect `∂₁∂₁F + ∂ᵢ∂ᵢF + F/(4y²)`. -/
def quarterDefect (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  dirD 1 (dirD 1 F) z + dirD I (dirD I F) z + quarterWeight z • F z

variable {F : ℂ → ℂ}

theorem contDiffOn_dirD (hF : ContDiffOn ℝ ∞ F upper) (v : ℂ) :
    ContDiffOn ℝ ∞ (dirD v F) upper := by
  have h := hF.fderiv_of_isOpen isOpen_upper (m := ∞) (by simp)
  exact h.clm_apply contDiffOn_const

theorem differentiableAt_of_contDiffOn (hF : ContDiffOn ℝ ∞ F upper) {z : ℂ} (hz : z ∈ upper) :
    DifferentiableAt ℝ F z :=
  (hF.contDiffAt (isOpen_upper.mem_nhds hz)).differentiableAt (by simp)

/-- `∂ᵥ∂_wF = D²F(v, w)`. -/
theorem dirD_dirD {z : ℂ} (hF : DifferentiableAt ℝ (fderiv ℝ F) z) (v w : ℂ) :
    dirD v (dirD w F) z = fderiv ℝ (fderiv ℝ F) z v w := by
  unfold dirD
  rw [fderiv_clm_apply hF (differentiableAt_const w)]
  simp

/-- Symmetry of second derivatives. -/
theorem dirD_comm (hF : ContDiffOn ℝ ∞ F upper) {z : ℂ} (hz : z ∈ upper) (v w : ℂ) :
    dirD v (dirD w F) z = dirD w (dirD v F) z := by
  have hc : ContDiffAt ℝ ∞ F z := hF.contDiffAt (isOpen_upper.mem_nhds hz)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    ((hc.fderiv_right (m := 1) (by exact le_of_lt (by decide))).differentiableAt one_ne_zero)
  rw [dirD_dirD hd, dirD_dirD hd]
  exact (hc.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact le_of_lt (by decide))) v w

/-- Two functions that agree on the upper half-plane have the same directional derivatives there. -/
theorem dirD_congr {G : ℂ → ℂ} (h : EqOn F G upper) {z : ℂ} (hz : z ∈ upper) (v : ℂ) :
    dirD v F z = dirD v G z := by
  unfold dirD
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (isOpen_upper.mem_nhds hz) h)]

theorem differentiableAt_quarterWeight {z : ℂ} (hz : z ∈ upper) :
    DifferentiableAt ℝ quarterWeight z := by
  have hne : 4 * z.im ^ 2 ≠ 0 := by
    have : z.im ≠ 0 := ne_of_gt hz
    positivity
  have h1 : DifferentiableAt ℝ (fun w : ℂ => 4 * w.im ^ 2) z := by fun_prop
  exact h1.inv hne

/-- The weight is constant along horizontal lines: `∂₁(1/(4y²)) = 0`. -/
theorem fderiv_quarterWeight_one {z : ℂ} (hz : z ∈ upper) : fderiv ℝ quarterWeight z 1 = 0 := by
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add z
  have hz0 : z + ((0 : ℝ) : ℂ) = z := by simp
  have hd : DifferentiableAt ℝ quarterWeight (z + ((0 : ℝ) : ℂ)) := by
    rw [hz0]; exact differentiableAt_quarterWeight hz
  have h1 := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  rw [hz0] at h1
  have hconst : (quarterWeight ∘ fun t : ℝ => z + (t : ℂ)) = fun _ => quarterWeight z := by
    funext t
    simp [quarterWeight]
  rw [hconst] at h1
  exact h1.unique (hasDerivAt_const _ _)

/-- `∂₁ (F/(4y²)) = (∂₁F)/(4y²)`: the weight depends on `y` only. -/
theorem dirD_one_weight {z : ℂ} (hF : DifferentiableAt ℝ F z) (hz : z ∈ upper) :
    dirD 1 (fun w => quarterWeight w • F w) z = quarterWeight z • dirD 1 F z := by
  unfold dirD
  rw [show (fun w => quarterWeight w • F w) = quarterWeight • F from rfl,
    fderiv_smul (differentiableAt_quarterWeight hz) hF]
  simp [fderiv_quarterWeight_one hz]

/-- `∂₁` preserves the quarter defect: `D(∂₁F) = ∂₁(DF)` on the upper half-plane. -/
theorem quarterDefect_dirD_one (hF : ContDiffOn ℝ ∞ F upper) {z : ℂ} (hz : z ∈ upper) :
    quarterDefect (dirD 1 F) z = dirD 1 (quarterDefect F) z := by
  have h1 := contDiffOn_dirD hF 1
  have hI := contDiffOn_dirD hF I
  have h11 := contDiffOn_dirD h1 1
  have hII := contDiffOn_dirD hI I
  have hdiff : ∀ {G : ℂ → ℂ}, ContDiffOn ℝ ∞ G upper → DifferentiableAt ℝ G z :=
    fun hG => differentiableAt_of_contDiffOn hG hz
  -- `∂₁∂ᵢ∂ᵢF = ∂ᵢ∂ᵢ∂₁F`
  have hcomm1 : EqOn (dirD I (dirD 1 F)) (dirD 1 (dirD I F)) upper :=
    fun w hw => dirD_comm hF hw I 1
  have hcomm2 : dirD 1 (dirD I (dirD I F)) z = dirD I (dirD 1 (dirD I F)) z :=
    dirD_comm hI hz 1 I
  have hcomm3 : dirD I (dirD I (dirD 1 F)) z = dirD I (dirD 1 (dirD I F)) z :=
    dirD_congr hcomm1 hz I
  have hA := (hdiff h11).hasFDerivAt
  have hB := (hdiff hII).hasFDerivAt
  have hC := ((differentiableAt_quarterWeight hz).hasFDerivAt.smul (hdiff hF).hasFDerivAt)
  have hQ : HasFDerivAt (quarterDefect F) (fderiv ℝ (dirD 1 (dirD 1 F)) z +
      fderiv ℝ (dirD I (dirD I F)) z +
      (quarterWeight z • fderiv ℝ F z + (fderiv ℝ quarterWeight z).smulRight (F z))) z :=
    (hA.add hB).add hC
  have hsum : dirD 1 (quarterDefect F) z =
      dirD 1 (dirD 1 (dirD 1 F)) z + dirD 1 (dirD I (dirD I F)) z +
        quarterWeight z • dirD 1 F z := by
    unfold dirD
    rw [hQ.fderiv]
    simp [fderiv_quarterWeight_one hz]
    rfl
  rw [hsum, hcomm2, ← hcomm3]
  rfl

/-- Derivative along the imaginary axis: `d/dy F(iy) = ∂ᵢF(iy)`. -/
theorem hasDerivAt_axis {y : ℝ} (hF : DifferentiableAt ℝ F ((y : ℂ) * I)) :
    HasDerivAt (fun t : ℝ => F ((t : ℂ) * I)) (dirD I F ((y : ℂ) * I)) y := by
  have hl : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I y := by
    simpa using (hasDerivAt_id y).ofReal_comp.mul_const I
  exact hF.hasFDerivAt.comp_hasDerivAt y hl

theorem mem_upper_axis {y : ℝ} (hy : 0 < y) : (y : ℂ) * I ∈ upper := by
  simp [upper, hy]

/-- A smooth function vanishing on the imaginary axis has vanishing `∂ᵢ` there. -/
theorem dirD_I_axis (hF : ContDiffOn ℝ ∞ F upper) (hax : ∀ y : ℝ, 0 < y → F ((y : ℂ) * I) = 0)
    {y : ℝ} (hy : 0 < y) : dirD I F ((y : ℂ) * I) = 0 := by
  have hd := hasDerivAt_axis (differentiableAt_of_contDiffOn hF (mem_upper_axis hy))
  have hzero : (fun t : ℝ => F ((t : ℂ) * I)) =ᶠ[𝓝 y] fun _ => 0 :=
    Filter.eventually_of_mem (Ioi_mem_nhds hy) fun t ht => hax t ht
  rw [← hd.deriv, hzero.deriv_eq]
  simp

/-- **The axis step.**  A smooth quarter eigenfunction vanishing on the imaginary axis has
`∂₁∂₁W = 0` there. -/
theorem dirD_one_dirD_one_axis {W : ℂ → ℂ} (hW : ContDiffOn ℝ ∞ W upper)
    (hpde : ∀ z ∈ upper, quarterDefect W z = 0) (hax : ∀ y : ℝ, 0 < y → W ((y : ℂ) * I) = 0)
    {y : ℝ} (hy : 0 < y) : dirD 1 (dirD 1 W) ((y : ℂ) * I) = 0 := by
  have h1 : ∀ t : ℝ, 0 < t → dirD I W ((t : ℂ) * I) = 0 := fun t ht => dirD_I_axis hW hax ht
  have h2 := dirD_I_axis (contDiffOn_dirD hW I) h1 hy
  have h := hpde _ (mem_upper_axis hy)
  unfold quarterDefect at h
  rw [h2, hax y hy, smul_zero, add_zero, add_zero] at h
  exact h

/-- The iterated `x`-derivatives `Wⱼ = ∂₁ʲV`. -/
def xDeriv (V : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => V
  | j + 1 => dirD 1 (xDeriv V j)

theorem contDiffOn_xDeriv {V : ℂ → ℂ} (hV : ContDiffOn ℝ ∞ V upper) :
    ∀ j, ContDiffOn ℝ ∞ (xDeriv V j) upper
  | 0 => hV
  | j + 1 => contDiffOn_dirD (contDiffOn_xDeriv hV j) 1

theorem quarterDefect_xDeriv {V : ℂ → ℂ} (hV : ContDiffOn ℝ ∞ V upper)
    (hpde : ∀ z ∈ upper, quarterDefect V z = 0) : ∀ j, ∀ z ∈ upper, quarterDefect (xDeriv V j) z = 0
  | 0 => hpde
  | j + 1 => by
      intro z hz
      change quarterDefect (dirD 1 (xDeriv V j)) z = 0
      rw [quarterDefect_dirD_one (contDiffOn_xDeriv hV j) hz]
      have hzero : EqOn (quarterDefect (xDeriv V j)) (fun _ => 0) upper :=
        fun w hw => quarterDefect_xDeriv hV hpde j w hw
      rw [dirD_congr hzero hz]
      simp [dirD]

/-- `∂₁V` vanishes on the imaginary axis when `V(−z̄) = V(z)`. -/
theorem dirD_one_axis_of_even {V : ℂ → ℂ} (hV : ContDiffOn ℝ ∞ V upper)
    (heven : ∀ z ∈ upper, V (-(starRingEnd ℂ) z) = V z) {y : ℝ} (hy : 0 < y) :
    dirD 1 V ((y : ℂ) * I) = 0 := by
  set φ : ℝ → ℂ := fun x => V ((x : ℂ) + (y : ℂ) * I) with hφ
  have hφd : HasDerivAt φ (dirD 1 V ((y : ℂ) * I)) 0 := by
    have hl : HasDerivAt (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.add_const ((y : ℂ) * I)
    have hp : ((0 : ℝ) : ℂ) + (y : ℂ) * I = (y : ℂ) * I := by simp
    have hV0 : DifferentiableAt ℝ V (((0 : ℝ) : ℂ) + (y : ℂ) * I) := by
      rw [hp]; exact differentiableAt_of_contDiffOn hV (mem_upper_axis hy)
    have := hV0.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [hp] at this
    exact this
  have hφeven : φ ∘ Neg.neg = φ := by
    funext x
    simp only [Function.comp, hφ]
    have hz : ((x : ℂ) + (y : ℂ) * I) ∈ upper := by simp [upper, hy]
    rw [← heven _ hz]
    congr 1
    apply Complex.ext <;> simp
  have hneg : HasDerivAt (φ ∘ Neg.neg) (-(dirD 1 V ((y : ℂ) * I))) 0 := by
    have hφd' : HasDerivAt φ (dirD 1 V ((y : ℂ) * I)) (Neg.neg (0 : ℝ)) := by
      rw [neg_zero]; exact hφd
    have := hφd'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simpa using this
  rw [hφeven] at hneg
  have := hφd.unique hneg
  have h2 : (2 : ℂ) * dirD 1 V ((y : ℂ) * I) = 0 := by linear_combination this
  simpa using h2

/-- All iterated `x`-derivatives vanish on the imaginary axis. -/
theorem xDeriv_axis {V : ℂ → ℂ} (hV : ContDiffOn ℝ ∞ V upper)
    (hpde : ∀ z ∈ upper, quarterDefect V z = 0) (heven : ∀ z ∈ upper, V (-(starRingEnd ℂ) z) = V z)
    (hax : ∀ y : ℝ, 0 < y → V ((y : ℂ) * I) = 0) :
    ∀ (j : ℕ) (y : ℝ), 0 < y → xDeriv V j ((y : ℂ) * I) = 0
  | 0 => hax
  | 1 => fun _ hy => dirD_one_axis_of_even hV heven hy
  | j + 2 => fun _ hy =>
      dirD_one_dirD_one_axis (contDiffOn_xDeriv hV j) (quarterDefect_xDeriv hV hpde j)
        (xDeriv_axis hV hpde heven hax j) hy

/-- The `j`-th derivative of `x ↦ V(x + iy)` is `Wⱼ(x + iy)`. -/
theorem iteratedDeriv_horizontal {V : ℂ → ℂ} (hV : ContDiffOn ℝ ∞ V upper) {y : ℝ} (hy : 0 < y) :
    ∀ j, iteratedDeriv j (fun x : ℝ => V ((x : ℂ) + (y : ℂ) * I)) =
      fun x : ℝ => xDeriv V j ((x : ℂ) + (y : ℂ) * I)
  | 0 => by simp [xDeriv]
  | j + 1 => by
      rw [iteratedDeriv_succ, iteratedDeriv_horizontal hV hy j]
      funext x
      have hz : ((x : ℂ) + (y : ℂ) * I) ∈ upper := by simp [upper, hy]
      have hd := differentiableAt_of_contDiffOn (contDiffOn_xDeriv hV j) hz
      have hl : HasDerivAt (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) 1 x := by
        simpa using (hasDerivAt_id x).ofReal_comp.add_const ((y : ℂ) * I)
      have := hd.hasFDerivAt.comp_hasDerivAt x hl
      rw [show (fun x : ℝ => xDeriv V j ((x : ℂ) + (y : ℂ) * I)) =
        (xDeriv V j ∘ fun x : ℝ => (x : ℂ) + (y : ℂ) * I) from rfl, this.deriv]
      simp [xDeriv, dirD]

/-- **Unique continuation from the imaginary axis.** -/
theorem eq_zero_of_axis {V : ℂ → ℂ} (hV : ContDiffOn ℝ ∞ V upper)
    (hpde : ∀ z ∈ upper, quarterDefect V z = 0) (heven : ∀ z ∈ upper, V (-(starRingEnd ℂ) z) = V z)
    (hax : ∀ y : ℝ, 0 < y → V ((y : ℂ) * I) = 0)
    (hana : ∀ y : ℝ, 0 < y → AnalyticOnNhd ℝ (fun x : ℝ => V ((x : ℂ) + (y : ℂ) * I)) univ) :
    ∀ z ∈ upper, V z = 0 := by
  intro z hz
  have hy : 0 < z.im := hz
  set φ : ℝ → ℂ := fun x : ℝ => V ((x : ℂ) + (z.im : ℂ) * I) with hφ
  have hφa := hana z.im hy
  have hderivs : ∀ j, iteratedDeriv j φ 0 = 0 := by
    intro j
    rw [hφ, iteratedDeriv_horizontal hV hy j]
    simpa using xDeriv_axis hV hpde heven hax j z.im hy
  have htop : analyticOrderAt φ 0 = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hφa 0 (mem_univ _))).mpr
      fun i _ => hderivs i
  have hev : φ =ᶠ[𝓝 0] 0 := analyticOrderAt_eq_top.mp htop
  have hall := hφa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ 0) hev
  have := hall (mem_univ z.re)
  simp only [Pi.zero_apply] at this
  rwa [show ((z.re : ℂ) + (z.im : ℂ) * I) = z from Complex.re_add_im z] at this

end RHTower.MaassAxisContinuation
