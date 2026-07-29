/-
# Local collar interface for the disconnected Böttcher deck route

This file contains the small, already-formal bridge between the conjectural
local collar geometry and the existing explicit-branch / strip machinery.

The hard geometric input is still external: construct a local collar `A` near a
depth-`n` cylinder, contained in the other parameter's basin, on which the
iterate and the chosen logarithm sheet are injective and land in one horizontal
strip.  Once that input exists, the lemmas here turn it into the one-sheeted
`explicitBranch` chart consumed by the deck construction.
-/
import GaloisForLFunctions.Bottcher.ExplicitBranch
import GaloisForLFunctions.Bottcher.CylinderUnivalence
import GaloisForLFunctions.Bottcher.FarFieldUnivalence

open Complex Set Filter Topology

namespace Bottcher

/-- The logarithmic lift whose exponential is `explicitBranch c n`. -/
noncomputable def explicitBranchLift (c : ℂ) (n : ℕ) : ℂ → ℂ :=
  fun z => (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))

/-- `explicitBranch` is the exponential of its logarithmic lift. -/
theorem explicitBranch_eq_exp_lift (c : ℂ) (n : ℕ) (z : ℂ) :
    explicitBranch c n z = Complex.exp (explicitBranchLift c n z) := rfl

/-- If the iterate is injective on `A` and the selected Böttcher logarithm is injective on the
forward image, then the explicit-branch logarithmic lift is injective on `A`. -/
theorem explicitBranchLift_injOn_of_iterate_bottcherLog_injOn
    (c : ℂ) (n : ℕ) {A : Set ℂ}
    (hiter : Set.InjOn ((quadratic c)^[n]) A)
    (hlog : Set.InjOn (bottcherLog c) (((quadratic c)^[n]) '' A)) :
    Set.InjOn (explicitBranchLift c n) A := by
  intro z hz w hw hzw
  apply hiter hz hw
  apply hlog ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
  have hscale : (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) ≠ 0) := by
    exact_mod_cast inv_ne_zero (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))
  simpa [explicitBranchLift] using mul_left_cancel₀ hscale hzw

/-- Strip control for the logarithmic lift turns lift-injectivity into injectivity of the
single-valued explicit branch.  This is the formal endpoint of the local-collar construction. -/
theorem explicitBranch_injOn_of_lift_injOn_strip
    (c : ℂ) (n : ℕ) {A : Set ℂ} {y₀ : ℝ}
    (hlift : Set.InjOn (explicitBranchLift c n) A)
    (hstrip : ∀ z ∈ A, y₀ < (explicitBranchLift c n z).im ∧
      (explicitBranchLift c n z).im ≤ y₀ + 2 * Real.pi) :
    Set.InjOn (explicitBranch c n) A := by
  simpa [explicitBranch_eq_exp_lift] using!
    (exp_comp_injOn (g := explicitBranchLift c n) (D := A) (y₀ := y₀) hlift hstrip)

/-- A combined version: injectivity of the iterate, injectivity of the selected logarithm on the
forward image, and one-strip control imply that `explicitBranch c n` is one-sheeted on `A`. -/
theorem explicitBranch_injOn_of_iterate_bottcherLog_injOn_strip
    (c : ℂ) (n : ℕ) {A : Set ℂ} {y₀ : ℝ}
    (hiter : Set.InjOn ((quadratic c)^[n]) A)
    (hlog : Set.InjOn (bottcherLog c) (((quadratic c)^[n]) '' A))
    (hstrip : ∀ z ∈ A, y₀ < (explicitBranchLift c n z).im ∧
      (explicitBranchLift c n z).im ≤ y₀ + 2 * Real.pi) :
    Set.InjOn (explicitBranch c n) A :=
  explicitBranch_injOn_of_lift_injOn_strip c n
    (explicitBranchLift_injOn_of_iterate_bottcherLog_injOn c n hiter hlog) hstrip

/-- Injectivity of `φ_c = exp(bottcherLog c)` on a set implies injectivity of the chosen
Böttcher logarithm there. -/
theorem bottcherLog_injOn_of_bottcherCoord_injOn {c : ℂ} {E : Set ℂ}
    (hφ : Set.InjOn (bottcherCoord c) E) :
    Set.InjOn (bottcherLog c) E := by
  intro z hz w hw hlog
  apply hφ hz hw
  simp [bottcherCoord, hlog]

/-- Far-field Böttcher-coordinate univalence gives injectivity of the selected Böttcher logarithm
on every subset of the far field. -/
theorem bottcherLog_injOn_far_subset {c : ℂ} {R : ℝ} {E : Set ℂ}
    (hR1 : 2 * max 2 ‖c‖ < R) (hR2 : 16 * ‖c‖ < R ^ 2)
    (hEfar : E ⊆ {z | R < ‖z‖}) :
    Set.InjOn (bottcherLog c) E :=
  bottcherLog_injOn_of_bottcherCoord_injOn
    ((bottcherCoord_injOn_far hR1 hR2).mono hEfar)

/-- An unscaled imaginary interval for `bottcherLog` implies the scaled horizontal-strip condition
needed by `ForwardCollarData`.  This keeps the future analytic estimate in the natural coordinate
`bottcherLog`, then performs only the formal `2⁻ⁿ` rescaling here. -/
theorem scaled_strip_sector_of_bottcherLog_im_bounds
    {c : ℂ} {n : ℕ} {E : Set ℂ} {y₀ : ℝ}
    (hIm : ∀ w ∈ E, y₀ * (2 : ℝ) ^ n < (bottcherLog c w).im ∧
      (bottcherLog c w).im ≤ (y₀ + 2 * Real.pi) * (2 : ℝ) ^ n) :
    ∀ w ∈ E, y₀ < (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) *
        bottcherLog c w).im ∧
      (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c w).im ≤ y₀ + 2 * Real.pi := by
  intro w hw
  set q : ℝ := (2 : ℝ) ^ n with hqdef
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hqinvpos : 0 < q⁻¹ := inv_pos.mpr hqpos
  have him : (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c w).im =
      ((2 : ℝ) ^ n)⁻¹ * (bottcherLog c w).im := by
    simpa using Complex.im_ofReal_mul (((2 : ℝ) ^ n)⁻¹) (bottcherLog c w)
  have hImw := hIm w hw
  constructor
  · have hmul := mul_lt_mul_of_pos_left hImw.1 hqinvpos
    have hleft : q⁻¹ * (y₀ * q) = y₀ := by
      field_simp [hqne]
    rw [hleft] at hmul
    rw [him]
    simpa [hqdef, mul_comm] using hmul
  · have hmul := mul_le_mul_of_nonneg_left hImw.2 (le_of_lt hqinvpos)
    have hleft : q⁻¹ * ((y₀ + 2 * Real.pi) * q) = y₀ + 2 * Real.pi := by
      field_simp [hqne]
    rw [hleft] at hmul
    rw [him]
    simpa [hqdef, mul_comm] using hmul

/-- A principal-log imaginary interval with an error margin implies the corresponding
`bottcherLog` imaginary interval.  This is the formal bridge from geometric sector estimates for
`Complex.log` to strip control for the normalized Böttcher logarithm. -/
theorem bottcherLog_im_bounds_of_log_im_bounds_error
    {c : ℂ} {E : Set ℂ} {L U δ : ℝ}
    (herr : ∀ w ∈ E, ‖bottcherLog c w - Complex.log w‖ ≤ δ)
    (hlog : ∀ w ∈ E, L + δ < (Complex.log w).im ∧ (Complex.log w).im + δ ≤ U) :
    ∀ w ∈ E, L < (bottcherLog c w).im ∧ (bottcherLog c w).im ≤ U := by
  intro w hw
  have habs : |(bottcherLog c w - Complex.log w).im| ≤ δ :=
    le_trans (Complex.abs_im_le_norm _) (herr w hw)
  have hlo : -δ ≤ (bottcherLog c w - Complex.log w).im := (abs_le.mp habs).1
  have hhi : (bottcherLog c w - Complex.log w).im ≤ δ := (abs_le.mp habs).2
  have hdiff : (bottcherLog c w - Complex.log w).im =
      (bottcherLog c w).im - (Complex.log w).im := by
    simp [Complex.sub_im]
  have hlogw := hlog w hw
  rw [hdiff] at hlo hhi
  constructor <;> linarith

/-- The existing Böttcher normalization estimate gives a uniform log-error bound on every far-field
subset.  This is the analytic error term used by the principal-log sector route. -/
theorem bottcherLog_log_error_le_on_far
    {c : ℂ} {R : ℝ} {E : Set ℂ}
    (hRgt2 : 2 < R) (hcR : ‖c‖ ≤ R) (hEfar : E ⊆ {z | R < ‖z‖}) :
    ∀ w ∈ E, ‖bottcherLog c w - Complex.log w‖ ≤ 2 * ‖c‖ / R ^ 2 := by
  intro w hw
  have hRw : R < ‖w‖ := hEfar hw
  have hw2 : 2 < ‖w‖ := lt_trans hRgt2 hRw
  have hcw : ‖c‖ ≤ ‖w‖ := le_trans hcR (le_of_lt hRw)
  have hb := norm_bottcherLog_sub_log_le hcw hw2
  refine le_trans hb ?_
  have hRpos : 0 < R := lt_trans (by norm_num) hRgt2
  have hRsqpos : 0 < R ^ 2 := sq_pos_of_pos hRpos
  have hsq : R ^ 2 ≤ ‖w‖ ^ 2 := by
    nlinarith [hRw, hRpos, norm_nonneg w]
  exact div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * ‖c‖) hRsqpos hsq

/-- A point outside `filledJulia c` has a whole metric ball outside it. -/
theorem exists_ball_subset_compl_filledJulia_of_not_mem {c z₀ : ℂ}
    (hz₀ : z₀ ∈ (filledJulia c)ᶜ) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ (filledJulia c)ᶜ :=
  Metric.isOpen_iff.mp (isClosed_filledJulia c).isOpen_compl z₀ hz₀

/-- A point in a ball whose radius is smaller than the center's distance from `0` lies in the
open half-plane defined by multiplying by the inverse center. -/
theorem invCenter_halfplane_pos_of_norm_sub_lt_norm
    {b w : ℂ} (hb : b ≠ 0) (hw : ‖w - b‖ < ‖b‖) :
    0 < (b⁻¹ * w).re := by
  let u : ℂ := b⁻¹ * (w - b)
  have hdecomp : b⁻¹ * w = 1 + u := by
    calc
      b⁻¹ * w = b⁻¹ * (b + (w - b)) := by ring
      _ = b⁻¹ * b + b⁻¹ * (w - b) := by ring
      _ = 1 + u := by
        rw [inv_mul_cancel₀ hb]
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hu_norm : ‖u‖ < 1 := by
    have hmul : ‖u‖ = ‖b‖⁻¹ * ‖w - b‖ := by
      simp [u, norm_inv]
    rw [hmul]
    exact (inv_mul_lt_iff₀ hbpos).mpr (by simpa using hw)
  have hre_lower : -‖u‖ ≤ u.re := (abs_le.mp (Complex.abs_re_le_norm u)).1
  rw [hdecomp]
  simp only [Complex.add_re, Complex.one_re]
  linarith

/-- The formal data package a future local inverse-branch collar theorem should produce.

The conjectural geometry is not asserted here.  This structure records exactly the facts that
turn a basin-side collar `A` into the one-sheeted `explicitBranch` chart used by the deck route. -/
structure LocalCollarData (c₁ c₂ : ℂ) (n : ℕ) (A : Set ℂ) (y₀ : ℝ) : Prop where
  isOpen : IsOpen A
  isPreconnected : IsPreconnected A
  nonempty : A.Nonempty
  subset_explicitDomain : A ⊆ explicitDomain c₁ n
  offOther : A ⊆ (filledJulia c₂)ᶜ
  iterate_injOn : Set.InjOn ((quadratic c₁)^[n]) A
  bottcherLog_injOn : Set.InjOn (bottcherLog c₁) (((quadratic c₁)^[n]) '' A)
  strip : ∀ z ∈ A, y₀ < (explicitBranchLift c₁ n z).im ∧
    (explicitBranchLift c₁ n z).im ≤ y₀ + 2 * Real.pi

/-- A local collar data package immediately gives analyticity of the explicit branch on the collar. -/
theorem LocalCollarData.analyticOnNhd_explicitBranch
    {c₁ c₂ : ℂ} {n : ℕ} {A : Set ℂ} {y₀ : ℝ}
    (h : LocalCollarData c₁ c₂ n A y₀) :
    AnalyticOnNhd ℂ (explicitBranch c₁ n) A :=
  (Bottcher.analyticOnNhd_explicitBranch c₁ n).mono h.subset_explicitDomain

/-- A local collar data package immediately gives a one-sheeted explicit branch on the collar. -/
theorem LocalCollarData.explicitBranch_injOn
    {c₁ c₂ : ℂ} {n : ℕ} {A : Set ℂ} {y₀ : ℝ}
    (h : LocalCollarData c₁ c₂ n A y₀) :
    Set.InjOn (explicitBranch c₁ n) A :=
  explicitBranch_injOn_of_iterate_bottcherLog_injOn_strip c₁ n
    h.iterate_injOn h.bottcherLog_injOn h.strip

/-- A local collar carries the analytic radical `explicitBranch c₁ n`, whose `2^n`-th power is the
radicand `bottcherCoord c₁ ∘ f_c₁^[n]` at the germ level. -/
theorem LocalCollarData.exists_explicitBranch_radical
    {c₁ c₂ : ℂ} {n : ℕ} {A : Set ℂ} {y₀ : ℝ}
    (h : LocalCollarData c₁ c₂ n A y₀) :
    ∃ a : analyticSubring A,
      (a : Filter.Germ (𝓟 A) ℂ) =
        (↑(explicitBranch c₁ n) : Filter.Germ (𝓟 A) ℂ) ∧
      ((a ^ (2 ^ n) : analyticSubring A) : Filter.Germ (𝓟 A) ℂ) =
        (↑(fun z => bottcherCoord c₁ ((quadratic c₁)^[n] z)) :
          Filter.Germ (𝓟 A) ℂ) := by
  let a : analyticSubring A :=
    ⟨(↑(explicitBranch c₁ n) : Filter.Germ (𝓟 A) ℂ),
      explicitBranch c₁ n, h.analyticOnNhd_explicitBranch, rfl⟩
  refine ⟨a, rfl, ?_⟩
  rw [SubmonoidClass.coe_pow, ← Filter.Germ.coe_pow]
  refine Filter.Germ.coe_eq.mpr (Filter.eventually_principal.mpr ?_)
  intro z _hz
  exact explicitBranch_pow c₁ n z

/-- Forward-sector data for a local collar.

This is the next bridge after `LocalCollarData`: instead of asking directly for injectivity and strip
control on the pullback collar `A`, it lets a caller produce a forward sector `E` with
`f_c^[n](A) ⊆ E`.  Injectivity and strip control are then checked on `E` and transported back to `A`
by the explicit formula for `explicitBranchLift`. -/
structure ForwardCollarData (c₁ c₂ : ℂ) (n : ℕ) (A E : Set ℂ) (y₀ : ℝ) : Prop where
  isOpen : IsOpen A
  isPreconnected : IsPreconnected A
  nonempty : A.Nonempty
  forward_image_subset : ((quadratic c₁)^[n]) '' A ⊆ E
  sector_subset_explicitTarget : E ⊆ escapeOpen c₁ ∩ Complex.slitPlane
  offOther : A ⊆ (filledJulia c₂)ᶜ
  iterate_injOn : Set.InjOn ((quadratic c₁)^[n]) A
  bottcherLog_injOn_sector : Set.InjOn (bottcherLog c₁) E
  scaled_strip_sector : ∀ w ∈ E, y₀ < (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) *
      bottcherLog c₁ w).im ∧
    (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c₁ w).im ≤ y₀ + 2 * Real.pi

/-- Forward-sector data converts to the direct `LocalCollarData` interface. -/
theorem ForwardCollarData.toLocalCollarData
    {c₁ c₂ : ℂ} {n : ℕ} {A E : Set ℂ} {y₀ : ℝ}
    (h : ForwardCollarData c₁ c₂ n A E y₀) :
    LocalCollarData c₁ c₂ n A y₀ where
  isOpen := h.isOpen
  isPreconnected := h.isPreconnected
  nonempty := h.nonempty
  subset_explicitDomain := by
    intro z hz
    exact h.sector_subset_explicitTarget (h.forward_image_subset ⟨z, hz, rfl⟩)
  offOther := h.offOther
  iterate_injOn := h.iterate_injOn
  bottcherLog_injOn := h.bottcherLog_injOn_sector.mono h.forward_image_subset
  strip := by
    intro z hz
    simpa [explicitBranchLift] using
      h.scaled_strip_sector ((quadratic c₁)^[n] z) (h.forward_image_subset ⟨z, hz, rfl⟩)

/-- Forward-sector data immediately gives analyticity of the explicit branch on the pullback collar. -/
theorem ForwardCollarData.analyticOnNhd_explicitBranch
    {c₁ c₂ : ℂ} {n : ℕ} {A E : Set ℂ} {y₀ : ℝ}
    (h : ForwardCollarData c₁ c₂ n A E y₀) :
    AnalyticOnNhd ℂ (explicitBranch c₁ n) A :=
  h.toLocalCollarData.analyticOnNhd_explicitBranch

/-- Forward-sector data immediately gives a one-sheeted explicit branch on the pullback collar. -/
theorem ForwardCollarData.explicitBranch_injOn
    {c₁ c₂ : ℂ} {n : ℕ} {A E : Set ℂ} {y₀ : ℝ}
    (h : ForwardCollarData c₁ c₂ n A E y₀) :
    Set.InjOn (explicitBranch c₁ n) A :=
  h.toLocalCollarData.explicitBranch_injOn

/-- Build forward-sector data from stepwise injectivity of the quadratic map on the forward images.

This exposes the native cylinder obligation: for every `j < n`, the `j`-th forward image of `A`
must lie in a region where one quadratic step is injective. -/
theorem ForwardCollarData.of_stepwise_injOn
    {c₁ c₂ : ℂ} {n : ℕ} {A E : Set ℂ} {y₀ : ℝ}
    (hAo : IsOpen A) (hAc : IsPreconnected A) (hAne : A.Nonempty)
    (himage : ((quadratic c₁)^[n]) '' A ⊆ E)
    (hEtarget : E ⊆ escapeOpen c₁ ∩ Complex.slitPlane)
    (hoff : A ⊆ (filledJulia c₂)ᶜ)
    (hstep : ∀ j < n, Set.InjOn (quadratic c₁) (((quadratic c₁)^[j]) '' A))
    (hlog : Set.InjOn (bottcherLog c₁) E)
    (hstrip : ∀ w ∈ E, y₀ < (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) *
        bottcherLog c₁ w).im ∧
      (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c₁ w).im ≤ y₀ + 2 * Real.pi) :
    ForwardCollarData c₁ c₂ n A E y₀ where
  isOpen := hAo
  isPreconnected := hAc
  nonempty := hAne
  forward_image_subset := himage
  sector_subset_explicitTarget := hEtarget
  offOther := hoff
  iterate_injOn := quadratic_iterate_injOn n hstep
  bottcherLog_injOn_sector := hlog
  scaled_strip_sector := hstrip

/-- Build forward-sector data from antipodal-freeness of each forward image.  This is the lobe-shaped
form of the disconnected cylinder geometry: each `f^[j] '' A`, for `j < n`, should sit in one of the
two antipodal lobes. -/
theorem ForwardCollarData.of_stepwise_antipodalFree
    {c₁ c₂ : ℂ} {n : ℕ} {A E : Set ℂ} {y₀ : ℝ}
    (hAo : IsOpen A) (hAc : IsPreconnected A) (hAne : A.Nonempty)
    (himage : ((quadratic c₁)^[n]) '' A ⊆ E)
    (hEtarget : E ⊆ escapeOpen c₁ ∩ Complex.slitPlane)
    (hoff : A ⊆ (filledJulia c₂)ᶜ)
    (hanti : ∀ j < n, ∀ z₁ ∈ ((quadratic c₁)^[j]) '' A,
      ∀ z₂ ∈ ((quadratic c₁)^[j]) '' A, z₁ = -z₂ → z₁ = z₂)
    (hlog : Set.InjOn (bottcherLog c₁) E)
    (hstrip : ∀ w ∈ E, y₀ < (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) *
        bottcherLog c₁ w).im ∧
      (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c₁ w).im ≤ y₀ + 2 * Real.pi) :
    ForwardCollarData c₁ c₂ n A E y₀ :=
  ForwardCollarData.of_stepwise_injOn hAo hAc hAne himage hEtarget hoff
    (fun j hj => quadratic_injOn (hanti j hj)) hlog hstrip

/-- Far-field sector constructor for forward-collar data.  The caller supplies the sector as a subset
of the far field and the slit plane; `bottcherLog` injectivity is then discharged by far-field
univalence of `bottcherCoord`. -/
theorem ForwardCollarData.of_stepwise_antipodalFree_far
    {c₁ c₂ : ℂ} {n : ℕ} {A E : Set ℂ} {y₀ R : ℝ}
    (hR1 : 2 * max 2 ‖c₁‖ < R) (hR2 : 16 * ‖c₁‖ < R ^ 2)
    (hAo : IsOpen A) (hAc : IsPreconnected A) (hAne : A.Nonempty)
    (himage : ((quadratic c₁)^[n]) '' A ⊆ E)
    (hEfar : E ⊆ {z | R < ‖z‖})
    (hEslit : E ⊆ Complex.slitPlane)
    (hoff : A ⊆ (filledJulia c₂)ᶜ)
    (hanti : ∀ j < n, ∀ z₁ ∈ ((quadratic c₁)^[j]) '' A,
      ∀ z₂ ∈ ((quadratic c₁)^[j]) '' A, z₁ = -z₂ → z₁ = z₂)
    (hstrip : ∀ w ∈ E, y₀ < (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) *
        bottcherLog c₁ w).im ∧
      (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c₁ w).im ≤ y₀ + 2 * Real.pi) :
    ForwardCollarData c₁ c₂ n A E y₀ :=
  ForwardCollarData.of_stepwise_antipodalFree hAo hAc hAne himage
    (by
      intro w hw
      refine ⟨?_, hEslit hw⟩
      have hmaxR : max 2 ‖c₁‖ < R := by
        have hmaxpos : 0 < max 2 ‖c₁‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
        nlinarith
      exact lt_trans hmaxR (hEfar hw))
    hoff hanti (bottcherLog_injOn_far_subset hR1 hR2 hEfar) hstrip

/-- Far-field sector constructor using unscaled imaginary bounds for `bottcherLog`.  This is the
most convenient endpoint for future estimates based on
`bottcherLog c z = Complex.log z + ∑ k, bottcherLogTerm c z k`. -/
theorem ForwardCollarData.of_stepwise_antipodalFree_far_im_bounds
    {c₁ c₂ : ℂ} {n : ℕ} {A E : Set ℂ} {y₀ R : ℝ}
    (hR1 : 2 * max 2 ‖c₁‖ < R) (hR2 : 16 * ‖c₁‖ < R ^ 2)
    (hAo : IsOpen A) (hAc : IsPreconnected A) (hAne : A.Nonempty)
    (himage : ((quadratic c₁)^[n]) '' A ⊆ E)
    (hEfar : E ⊆ {z | R < ‖z‖})
    (hEslit : E ⊆ Complex.slitPlane)
    (hoff : A ⊆ (filledJulia c₂)ᶜ)
    (hanti : ∀ j < n, ∀ z₁ ∈ ((quadratic c₁)^[j]) '' A,
      ∀ z₂ ∈ ((quadratic c₁)^[j]) '' A, z₁ = -z₂ → z₁ = z₂)
    (hIm : ∀ w ∈ E, y₀ * (2 : ℝ) ^ n < (bottcherLog c₁ w).im ∧
      (bottcherLog c₁ w).im ≤ (y₀ + 2 * Real.pi) * (2 : ℝ) ^ n) :
    ForwardCollarData c₁ c₂ n A E y₀ :=
  ForwardCollarData.of_stepwise_antipodalFree_far hR1 hR2 hAo hAc hAne himage
    hEfar hEslit hoff hanti (scaled_strip_sector_of_bottcherLog_im_bounds hIm)

/-- Far-field sector constructor using principal-log imaginary bounds plus an explicit error
margin for `bottcherLog c₁ w - Complex.log w`.  This separates the future analytic estimate into
two independent obligations: place the principal argument in a wide sector, and bound the
Böttcher-log normalization error. -/
theorem ForwardCollarData.of_stepwise_antipodalFree_far_log_im_bounds_error
    {c₁ c₂ : ℂ} {n : ℕ} {A E : Set ℂ} {y₀ R δ : ℝ}
    (hR1 : 2 * max 2 ‖c₁‖ < R) (hR2 : 16 * ‖c₁‖ < R ^ 2)
    (hAo : IsOpen A) (hAc : IsPreconnected A) (hAne : A.Nonempty)
    (himage : ((quadratic c₁)^[n]) '' A ⊆ E)
    (hEfar : E ⊆ {z | R < ‖z‖})
    (hEslit : E ⊆ Complex.slitPlane)
    (hoff : A ⊆ (filledJulia c₂)ᶜ)
    (hanti : ∀ j < n, ∀ z₁ ∈ ((quadratic c₁)^[j]) '' A,
      ∀ z₂ ∈ ((quadratic c₁)^[j]) '' A, z₁ = -z₂ → z₁ = z₂)
    (herr : ∀ w ∈ E, ‖bottcherLog c₁ w - Complex.log w‖ ≤ δ)
    (hlog : ∀ w ∈ E, y₀ * (2 : ℝ) ^ n + δ < (Complex.log w).im ∧
      (Complex.log w).im + δ ≤ (y₀ + 2 * Real.pi) * (2 : ℝ) ^ n) :
    ForwardCollarData c₁ c₂ n A E y₀ :=
  ForwardCollarData.of_stepwise_antipodalFree_far_im_bounds hR1 hR2 hAo hAc hAne
    himage hEfar hEslit hoff hanti
    (bottcherLog_im_bounds_of_log_im_bounds_error herr hlog)

/-- Far-field/log-error constructor whose iterate-injectivity input is forward half-plane
containment.  This is the formal version of the angular-pruning mechanism: each intermediate
forward image only has to fit inside some open half-plane through `0`, which excludes antipodal
collisions and hence makes every quadratic step injective. -/
theorem ForwardCollarData.of_forward_halfplane_far_log_im_bounds_error
    {c₁ c₂ : ℂ} {n : ℕ} {A E : Set ℂ} {y₀ R δ : ℝ} (a : ℕ → ℂ)
    (hR1 : 2 * max 2 ‖c₁‖ < R) (hR2 : 16 * ‖c₁‖ < R ^ 2)
    (hAo : IsOpen A) (hAc : IsPreconnected A) (hAne : A.Nonempty)
    (himage : ((quadratic c₁)^[n]) '' A ⊆ E)
    (hEfar : E ⊆ {z | R < ‖z‖})
    (hEslit : E ⊆ Complex.slitPlane)
    (hoff : A ⊆ (filledJulia c₂)ᶜ)
    (hhalf : ∀ j < n, ∀ w ∈ ((quadratic c₁)^[j]) '' A, 0 < (a j * w).re)
    (herr : ∀ w ∈ E, ‖bottcherLog c₁ w - Complex.log w‖ ≤ δ)
    (hlog : ∀ w ∈ E, y₀ * (2 : ℝ) ^ n + δ < (Complex.log w).im ∧
      (Complex.log w).im + δ ≤ (y₀ + 2 * Real.pi) * (2 : ℝ) ^ n) :
    ForwardCollarData c₁ c₂ n A E y₀ :=
  ForwardCollarData.of_stepwise_antipodalFree_far_log_im_bounds_error
    hR1 hR2 hAo hAc hAne himage hEfar hEslit hoff
    (fun j hj => antipodalFree_of_halfplane (a := a j) (hhalf j hj))
    herr hlog

/-- Far-field/principal-log constructor with the Böttcher-log error discharged internally from the
normalization estimate.  The remaining geometric obligations are: construct the forward sector,
prove finite forward half-plane containment, and place the principal log in the widened strip. -/
theorem ForwardCollarData.of_forward_halfplane_far_log_im_bounds
    {c₁ c₂ : ℂ} {n : ℕ} {A E : Set ℂ} {y₀ R : ℝ} (a : ℕ → ℂ)
    (hR1 : 2 * max 2 ‖c₁‖ < R) (hR2 : 16 * ‖c₁‖ < R ^ 2)
    (hAo : IsOpen A) (hAc : IsPreconnected A) (hAne : A.Nonempty)
    (himage : ((quadratic c₁)^[n]) '' A ⊆ E)
    (hEfar : E ⊆ {z | R < ‖z‖})
    (hEslit : E ⊆ Complex.slitPlane)
    (hoff : A ⊆ (filledJulia c₂)ᶜ)
    (hhalf : ∀ j < n, ∀ w ∈ ((quadratic c₁)^[j]) '' A, 0 < (a j * w).re)
    (hlog : ∀ w ∈ E, y₀ * (2 : ℝ) ^ n + 2 * ‖c₁‖ / R ^ 2 < (Complex.log w).im ∧
      (Complex.log w).im + 2 * ‖c₁‖ / R ^ 2 ≤
        (y₀ + 2 * Real.pi) * (2 : ℝ) ^ n) :
    ForwardCollarData c₁ c₂ n A E y₀ := by
  have hRgt2 : 2 < R := by
    have hmax2 : (2 : ℝ) ≤ max 2 ‖c₁‖ := le_max_left _ _
    nlinarith
  have hcR : ‖c₁‖ ≤ R := by
    have hmaxc : ‖c₁‖ ≤ max 2 ‖c₁‖ := le_max_right _ _
    have hmax_nonneg : 0 ≤ max 2 ‖c₁‖ := le_trans (by norm_num) (le_max_left _ _)
    nlinarith
  exact ForwardCollarData.of_forward_halfplane_far_log_im_bounds_error
    (a := a) hR1 hR2 hAo hAc hAne himage hEfar hEslit hoff hhalf
    (bottcherLog_log_error_le_on_far hRgt2 hcR hEfar) hlog

/-- Ball-separated forward images are enough for the far-field/principal-log collar constructor.
This is the shrinking-cylinder form of the route: at each time `j < n`, the whole intermediate image
lies in a ball whose radius is smaller than the ball center's distance from `0`, hence in an open
half-plane through `0`. -/
theorem ForwardCollarData.of_forward_ball_separated_far_log_im_bounds
    {c₁ c₂ : ℂ} {n : ℕ} {A E : Set ℂ} {y₀ R : ℝ} (center : ℕ → ℂ)
    (hR1 : 2 * max 2 ‖c₁‖ < R) (hR2 : 16 * ‖c₁‖ < R ^ 2)
    (hAo : IsOpen A) (hAc : IsPreconnected A) (hAne : A.Nonempty)
    (himage : ((quadratic c₁)^[n]) '' A ⊆ E)
    (hEfar : E ⊆ {z | R < ‖z‖})
    (hEslit : E ⊆ Complex.slitPlane)
    (hoff : A ⊆ (filledJulia c₂)ᶜ)
    (hball : ∀ j < n, ∀ w ∈ ((quadratic c₁)^[j]) '' A,
      ‖w - center j‖ < ‖center j‖)
    (hlog : ∀ w ∈ E, y₀ * (2 : ℝ) ^ n + 2 * ‖c₁‖ / R ^ 2 < (Complex.log w).im ∧
      (Complex.log w).im + 2 * ‖c₁‖ / R ^ 2 ≤
        (y₀ + 2 * Real.pi) * (2 : ℝ) ^ n) :
    ForwardCollarData c₁ c₂ n A E y₀ :=
  ForwardCollarData.of_forward_halfplane_far_log_im_bounds (a := fun j => (center j)⁻¹)
    hR1 hR2 hAo hAc hAne himage hEfar hEslit hoff
    (fun j hj w hw => by
      have hlt := hball j hj w hw
      have hcenter_pos : 0 < ‖center j‖ :=
        lt_of_le_of_lt (norm_nonneg _) hlt
      exact invCenter_halfplane_pos_of_norm_sub_lt_norm
        (b := center j) (w := w) (norm_pos_iff.mp hcenter_pos) hlt)
    hlog

/-- Ball-separated forward images plus principal-argument bounds.  This is the sector form consumed
by external-ray or angular-pruning geometry. -/
theorem ForwardCollarData.of_forward_ball_separated_far_arg_bounds
    {c₁ c₂ : ℂ} {n : ℕ} {A E : Set ℂ} {y₀ R : ℝ} (center : ℕ → ℂ)
    (hR1 : 2 * max 2 ‖c₁‖ < R) (hR2 : 16 * ‖c₁‖ < R ^ 2)
    (hAo : IsOpen A) (hAc : IsPreconnected A) (hAne : A.Nonempty)
    (himage : ((quadratic c₁)^[n]) '' A ⊆ E)
    (hEfar : E ⊆ {z | R < ‖z‖})
    (hEslit : E ⊆ Complex.slitPlane)
    (hoff : A ⊆ (filledJulia c₂)ᶜ)
    (hball : ∀ j < n, ∀ w ∈ ((quadratic c₁)^[j]) '' A,
      ‖w - center j‖ < ‖center j‖)
    (harg : ∀ w ∈ E, y₀ * (2 : ℝ) ^ n + 2 * ‖c₁‖ / R ^ 2 < w.arg ∧
      w.arg + 2 * ‖c₁‖ / R ^ 2 ≤ (y₀ + 2 * Real.pi) * (2 : ℝ) ^ n) :
    ForwardCollarData c₁ c₂ n A E y₀ :=
  ForwardCollarData.of_forward_ball_separated_far_log_im_bounds center
    hR1 hR2 hAo hAc hAne himage hEfar hEslit hoff hball
    (by
      intro w hw
      simpa [Complex.log_im] using harg w hw)

end Bottcher
