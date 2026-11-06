import GaloisForLFunctions.WindowVisibilityLaw.ShallowClusterExclusionAndTaperedCrystalBarrier
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import GaloisForLFunctions.RHTower.SelbergSymbolCriticalStrip

/-!
# Sine localizers of a test

`sineLift τ g` is the finite difference whose transform is `sin(τz)` times that of `g`. Iterating
`N` times multiplies the transform by `sin(τz)^N` at the cost of `Nτ` of support. For `τT = π/2` the
factor is `cos(τ(z−T))^N`: close to one near height `T`, with a zero of order `N` at height zero.

On the real line the factor has modulus at most one, so it never increases an on-line term. The zero
at the origin makes low heights negligible by the maximum principle
(`norm_paperFT_sinePower_sq_le`), with no lower bound on the test's mass near height `T`.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.WindowVisibilityLaw

open Zeta23 _root_.RHTower

/-- The finite difference whose transform is `sin(τz)` times the transform of `g`. -/
def sineLift (τ : ℝ) (g : ℝ → ℂ) : ℝ → ℂ := fun u => (g (u - τ) - g (u + τ)) / (2 * I)

theorem contDiff_sineLift (τ : ℝ) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (sineLift τ g) := by
  unfold sineLift
  exact ((hg.comp (contDiff_id.sub contDiff_const)).sub
    (hg.comp (contDiff_id.add contDiff_const))).div_const _

theorem tsupport_sineLift_subset {τ A : ℝ} (hτ : 0 ≤ τ) {g : ℝ → ℂ}
    (hg : tsupport g ⊆ Icc (-A) A) :
    tsupport (sineLift τ g) ⊆ Icc (-(A + τ)) (A + τ) := by
  refine closure_minimal ?_ isClosed_Icc
  intro u hu
  by_contra hn
  apply hu
  have h0 : ∀ v, v ∉ Icc (-A) A → g v = 0 := fun v hv =>
    image_eq_zero_of_notMem_tsupport fun hm => hv (hg hm)
  have h1 : u - τ ∉ Icc (-A) A := fun h => hn ?_
  · have h2 : u + τ ∉ Icc (-A) A := fun h => hn ?_
    · simp [sineLift, h0 _ h1, h0 _ h2]
    · constructor <;> linarith [h.1, h.2]
  · constructor <;> linarith [h.1, h.2]

private theorem paperFT_shift_right (f : ℝ → ℂ) (c : ℝ) (z : ℂ) :
    paperFT (fun u => f (u + c)) z = cexp (-(I * z * c)) * paperFT f z := by
  simp only [paperFT]
  rw [← integral_const_mul]
  have h := integral_add_right_eq_self
    (fun u : ℝ => cexp (-(I * z * c)) * (f u * cexp (I * z * u))) c
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_left_comm, ← mul_assoc, mul_comm (cexp _) (f _), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem integrable_integrand {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (z : ℂ) : Integrable fun u : ℝ => g u * cexp (I * z * u) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right

theorem paperFT_sineLift (τ : ℝ) {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (z : ℂ) : paperFT (sineLift τ g) z = Complex.sin (τ * z) * paperFT g z := by
  have hgm : HasCompactSupport fun u => g (u - τ) := by
    simpa [sub_eq_add_neg] using hgc.comp_homeomorph (Homeomorph.addRight (-τ))
  have hgp : HasCompactSupport fun u => g (u + τ) :=
    hgc.comp_homeomorph (Homeomorph.addRight τ)
  have hm : paperFT (fun u => g (u - τ)) z = cexp (I * z * τ) * paperFT g z := by
    have h := paperFT_shift_right g (-τ) z
    simp only [sub_eq_add_neg]
    rw [h]
    congr 2
    push_cast
    ring
  have hp := paperFT_shift_right g τ z
  have hsplit : paperFT (sineLift τ g) z =
      (paperFT (fun u => g (u - τ)) z - paperFT (fun u => g (u + τ)) z) / (2 * I) := by
    simp only [paperFT, sineLift]
    rw [← integral_sub
      (integrable_integrand (hg.comp (by fun_prop)) hgm z)
      (integrable_integrand (hg.comp (by fun_prop)) hgp z), ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    ring
  rw [hsplit, hm, hp, Complex.sin]
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have e1 : -((τ : ℂ) * z) * I = -(I * z * τ) := by ring
  have e2 : ((τ : ℂ) * z) * I = I * z * τ := by ring
  rw [e1, e2]
  field_simp
  rw [Complex.I_sq]
  ring

/-- Multiplication of the transform by `sin(τz)^N`. -/
def sinePower (τ : ℝ) (N : ℕ) (g : ℝ → ℂ) : ℝ → ℂ := (sineLift τ)^[N] g

theorem contDiff_sinePower (τ : ℝ) (N : ℕ) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (sinePower τ N g) := by
  induction N with
  | zero => exact hg
  | succ N ih =>
    rw [sinePower, Function.iterate_succ_apply']
    exact contDiff_sineLift τ ih

theorem tsupport_sinePower_subset {τ A : ℝ} (hτ : 0 ≤ τ) (N : ℕ) {g : ℝ → ℂ}
    (hg : tsupport g ⊆ Icc (-A) A) :
    tsupport (sinePower τ N g) ⊆ Icc (-(A + N * τ)) (A + N * τ) := by
  induction N with
  | zero => simpa [sinePower] using hg
  | succ N ih =>
    rw [sinePower, Function.iterate_succ_apply']
    have h := tsupport_sineLift_subset hτ ih
    have e : A + ((N + 1 : ℕ) : ℝ) * τ = A + N * τ + τ := by push_cast; ring
    rw [e]
    exact h

theorem hasCompactSupport_sinePower {τ A : ℝ} (hτ : 0 ≤ τ) (N : ℕ) {g : ℝ → ℂ}
    (hg : tsupport g ⊆ Icc (-A) A) : HasCompactSupport (sinePower τ N g) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (tsupport_sinePower_subset hτ N hg)

theorem paperFT_sinePower {τ A : ℝ} (hτ : 0 ≤ τ) (N : ℕ) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Icc (-A) A) (z : ℂ) :
    paperFT (sinePower τ N g) z = Complex.sin (τ * z) ^ N * paperFT g z := by
  induction N with
  | zero => simp [sinePower]
  | succ N ih =>
    rw [sinePower, Function.iterate_succ_apply',
      paperFT_sineLift τ (contDiff_sinePower τ N hg).continuous
        (hasCompactSupport_sinePower hτ N hgs) z]
    change Complex.sin (τ * z) * paperFT (sinePower τ N g) z = _
    rw [ih, pow_succ]
    ring

/-- The localizer multiplies the transform of the autocorrelation by `sin(τz)^{2N}`. -/
theorem paperFT_weilTest_sinePower {τ A : ℝ} (hτ : 0 ≤ τ) (N : ℕ) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgs : tsupport g ⊆ Icc (-A) A) (z : ℂ) :
    paperFT (EF.weilTest (sinePower τ N g) (sinePower τ N g)) z =
      Complex.sin (τ * z) ^ (2 * N) * paperFT (EF.weilTest g g) z := by
  have hgc : HasCompactSupport g := IsCompact.of_isClosed_subset isCompact_Icc
    (isClosed_tsupport _) hgs
  have hc := (contDiff_sinePower τ N hg).continuous
  have hsc := hasCompactSupport_sinePower hτ N hgs
  rw [EF.paperFT_weilTest hc hc hsc hsc, EF.paperFT_weilTest hg.continuous hg.continuous hgc hgc,
    paperFT_sinePower hτ N hg hgs, paperFT_sinePower hτ N hg hgs, map_mul, map_pow,
    ← Complex.sin_conj, map_mul, Complex.conj_conj, Complex.conj_ofReal, two_mul, pow_add]
  ring

/-- Size of the transform of an autocorrelation at a complex point. -/
theorem norm_paperFT_weilTest_le {g : ℝ → ℂ} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A)
    (hgs : tsupport g ⊆ Icc (-A) A) (z : ℂ) :
    ‖paperFT (EF.weilTest g g) z‖ ≤
      4 * A * (∫ t, ‖g t‖ ^ 2) * Real.exp (2 * A * |z.im|) := by
  have hgc : HasCompactSupport g :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hgs
  have hKs : tsupport (EF.weilTest g g) ⊆ Icc (-(2 * A)) (2 * A) :=
    EF.tsupport_weilTest_subset (L := 2 * A) (by rwa [show 2 * A / 2 = A by ring])
      (by rwa [show 2 * A / 2 = A by ring])
  have hE0 : 0 ≤ ∫ t, ‖g t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  set F : ℝ → ℂ := fun u => EF.weilTest g g u * cexp (I * z * u) with hF
  have hFz : ∀ u, u ∉ Icc (-(2 * A)) (2 * A) → F u = 0 := fun u hu => by
    simp only [hF]
    rw [image_eq_zero_of_notMem_tsupport (fun h => hu (hKs h)), zero_mul]
  have hFn : ∀ u ∈ Icc (-(2 * A)) (2 * A),
      ‖F u‖ ≤ (∫ t, ‖g t‖ ^ 2) * Real.exp (2 * A * |z.im|) := by
    intro u hu
    have hu' : |u| ≤ 2 * A := abs_le.mpr ⟨hu.1, hu.2⟩
    simp only [hF]
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul (SquareRootThreshold.norm_weilTest_self_le hg hgc u)
      (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hE0
    have hre : (I * z * (u : ℂ)).re = -(z.im * u) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have h1 : -(z.im * u) ≤ |z.im * u| := neg_le_abs _
    rw [abs_mul] at h1
    have h2 : |z.im| * |u| ≤ |z.im| * (2 * A) := mul_le_mul_of_nonneg_left hu' (abs_nonneg _)
    linarith only [h1, h2]
  have hval : paperFT (EF.weilTest g g) z = ∫ u, F u := rfl
  rw [hval, ← setIntegral_eq_integral_of_forall_compl_eq_zero hFz]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-(2 * A)) (2 * A))
    (f := F) (by simp) hFn
  rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
    show 2 * A - -(2 * A) = 4 * A by ring] at this
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **The zero of the localizer pays low heights.** The transform of `sinePower τ N f` at a real
point `|x| ≤ r` is smaller by `(r/R)^{2N}` than the bound for the transform of its autocorrelation
on the circle of radius `R`. -/
theorem norm_paperFT_sinePower_sq_le {τ A a : ℝ} (hτ : 0 ≤ τ) (N : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hA : 0 ≤ A)
    (hgs : tsupport (sinePower τ N f) ⊆ Icc (-A) A) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {x : ℝ} (hx : |x| ≤ r) :
    ‖paperFT (sinePower τ N f) x‖ ^ 2 ≤
      (r / R) ^ (2 * N) *
        (4 * A * (∫ t, ‖sinePower τ N f t‖ ^ 2) * Real.exp (2 * A * R)) := by
  have hR : 0 < R := hr.trans_le hrR
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hfs
  set g := sinePower τ N f with hg
  have hgc : ContDiff ℝ 2 g := contDiff_sinePower τ N hf
  have hgcs : HasCompactSupport g :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hgs
  set C := 4 * A * (∫ t, ‖g t‖ ^ 2) * Real.exp (2 * A * R) with hCdef
  have hE0 : 0 ≤ ∫ t, ‖g t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  -- `sin(τz) = z s(z)` with `s` entire.
  let sn : ℂ → ℂ := fun z => Complex.sin (τ * z)
  have hsnD : Differentiable ℂ sn := by fun_prop
  let s : ℂ → ℂ := dslope sn 0
  have hsD : Differentiable ℂ s := by
    have := (Complex.differentiableOn_dslope (s := univ) (c := (0 : ℂ)) (f := sn)
      Filter.univ_mem).mpr hsnD.differentiableOn
    exact differentiableOn_univ.mp this
  have hsn : ∀ z, sn z = z * s z := fun z => by
    have h := sub_smul_dslope sn 0 z
    simp only [sub_zero, smul_eq_mul] at h
    have h0 : sn 0 = 0 := by simp [sn]
    rw [h0, sub_zero] at h
    exact h.symm
  have hPfD : Differentiable ℂ (paperFT (EF.weilTest f f)) :=
    EvenSector.differentiable_paperFT_of_compact
      (EF.weilTest_contDiff hf hf.continuous hfc).continuous
      (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
        (EF.tsupport_weilTest_subset (L := 2 * a) (by rwa [show 2 * a / 2 = a by ring])
          (by rwa [show 2 * a / 2 = a by ring])))
  let H : ℂ → ℂ := fun z => s z ^ (2 * N) * paperFT (EF.weilTest f f) z
  have hHD : Differentiable ℂ H := (hsD.pow _).mul hPfD
  have hG : ∀ z, paperFT (EF.weilTest g g) z = z ^ (2 * N) * H z := fun z => by
    rw [hg, paperFT_weilTest_sinePower hτ N hf hfs z]
    change sn z ^ (2 * N) * _ = _
    rw [hsn z, mul_pow]
    simp only [H]
    ring
  have hsphere : ∀ z ∈ frontier (ball (0 : ℂ) R), ‖H z‖ ≤ C / R ^ (2 * N) := by
    intro z hz
    rw [frontier_ball _ hR.ne', mem_sphere_zero_iff_norm] at hz
    have h1 := norm_paperFT_weilTest_le hgc.continuous hA hgs z
    have him : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hz.le
    have h2 : ‖paperFT (EF.weilTest g g) z‖ ≤ C := by
      refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
      exact mul_le_mul_of_nonneg_left him (by positivity)
    rw [hG, norm_mul, norm_pow, hz] at h2
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact h2
  have hxR : ((x : ℝ) : ℂ) ∈ closure (ball (0 : ℂ) R) := by
    rw [closure_ball _ hR.ne', mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact hx.trans hrR
  have hHx := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    hHD.diffContOnCl hsphere hxR
  rw [← Complex.ofReal_inj.mpr rfl]
  have hP := SelbergSymbolStrip.paperFT_weilTest_self_ofReal' hgc.continuous hgcs x
  sorry

end GaloisForLFunctions.WindowVisibilityLaw
