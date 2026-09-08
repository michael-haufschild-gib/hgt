import GaloisForLFunctions.RHTower.MaassCuspAutomorphicCorrespondence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# The actual period integral of a congruence Maass cusp eigenform

For every positive principal congruence level, the existing Maass definition gives
an actual horizontal period integral satisfying the Euler equation and tending to
zero at infinity. The proof derives periodicity from the congruence translation,
uses only the supplied real C² regularity, and justifies both differentiations
under the finite interval integral by local compact domination.

The integral is unnormalized (width times the constant Fourier coefficient).
Vanishing of this coefficient and the full Selberg bound are separate results.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassMean
noncomputable section

/-- Real coordinates in the complex chart. -/
def point (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
/-- The actual real Fréchet directional derivative. -/
def directional (v : ℂ) (F : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ F z v
/-- Unnormalized horizontal integral over one period. -/
def periodIntegral (w : ℝ) (F : ℂ → ℂ) (y : ℝ) : ℂ :=
  ∫ x in Ioc 0 w, F (point x y)

/-- Directional differentiation lowers real chart regularity by one. -/
theorem directional_contDiffOn {F : ℂ → ℂ} {n m : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n F {z : ℂ | 0 < z.im}) (hmn : m + 1 ≤ n) (v : ℂ) :
    ContDiffOn ℝ m (directional v F) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (((hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hz)).fderiv_right
    hmn).clm_apply contDiffAt_const).contDiffWithinAt

/-- The real height coordinate has vertical complex velocity. -/
theorem point_vertical (x y : ℝ) : HasDerivAt (point x) Complex.I y := by
  change HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) Complex.I y
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
    ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x : ℂ)

/-- The real horizontal coordinate has unit complex velocity. -/
theorem point_horizontal (x y : ℝ) :
    HasDerivAt (fun t => point t y) 1 x := by
  simpa [point] using
    (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)

/-- The chart directional derivative equals the actual height derivative. -/
theorem slice_vertical {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im}) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => F (point x t)) (directional Complex.I F (point x y)) y := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact ((hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt y (point_vertical x y)

/-- The chart directional derivative equals the actual horizontal derivative. -/
theorem slice_horizontal {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t => F (point t y)) (directional 1 F (point x y)) x := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact ((hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt x (point_horizontal x y)

/-- A continuous upper-half-plane chart function has continuous horizontal slices. -/
theorem slice_continuous {F : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => F (point x y)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact (hf.continuousAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).comp (f := fun t : ℝ => point t y)
    (point_horizontal x y).continuousAt

/-- C¹ regularity suffices to differentiate the actual horizontal integral. -/
theorem periodIntegral_hasDerivAt (w : ℝ) {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (periodIntegral w F) (periodIntegral w (directional Complex.I F) y) y := by
  have hd := directional_contDiffOn hf (m := 0) (by simp) Complex.I
  let K : Set (ℝ × ℝ) := Icc 0 w ×ˢ Icc (y / 2) (y + 1)
  have hcont : ContinuousOn (fun xy : ℝ × ℝ =>
      directional Complex.I F (point xy.1 xy.2)) K := by
    apply hd.continuousOn.comp (show Continuous (fun xy : ℝ × ℝ => point xy.1 xy.2) by
      unfold point; fun_prop).continuousOn
    intro xy hxy
    have hlow := hxy.2.1
    change 0 < (point xy.1 xy.2).im
    simp only [point, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.ofReal_re, zero_add]
    linarith
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  have hn : Ioo (y / 2) (y + 1) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ t ∈ Ioo (y / 2) (y + 1), 0 < t := by intro t ht; linarith [ht.1]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 w))
    (F := fun t x => F (point x t))
    (F' := fun t x => directional Complex.I F (point x t)) (bound := fun _ => C) hn
    (by filter_upwards [hn] with t ht
        exact (slice_continuous hf.continuousOn (hpos t ht)).aestronglyMeasurable.restrict)
    ((slice_continuous hf.continuousOn hy).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((slice_continuous hd.continuousOn hy).aestronglyMeasurable.restrict)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        intro t ht
        exact hC (x, t) ⟨⟨hx.1.le, hx.2⟩, ⟨ht.1.le, ht.2.le⟩⟩)
    (integrable_const C)
    (by filter_upwards with x
        intro t ht
        exact slice_vertical hf x (hpos t ht))).2

/-- C² regularity gives the second height derivative of the integral. -/
theorem periodIntegral_second_hasDerivAt (w : ℝ) {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (periodIntegral w F))
      (periodIntegral w (directional Complex.I (directional Complex.I F)) y) y := by
  have hd := directional_contDiffOn hf (m := 1) le_rfl Complex.I
  apply (periodIntegral_hasDerivAt w hd hy).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact (periodIntegral_hasDerivAt w (hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)) ht).deriv

/-- Horizontal differentiation preserves the actual slice periodicity. -/
theorem directional_periodic {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) (w : ℝ)
    (hp : ∀ x, F (point (x + w) y) = F (point x y)) (x : ℝ) :
    directional 1 F (point (x + w) y) = directional 1 F (point x y) := by
  have h1 := (slice_horizontal hf hy (x + w)).scomp x ((hasDerivAt_id x).add_const w)
  have h2 := slice_horizontal hf hy x
  have he : (fun t : ℝ => F (point (t + w) y)) = (fun t => F (point t y)) := funext hp
  have h1' : HasDerivAt (fun t : ℝ => F (point t y))
      (directional 1 F (point (x + w) y)) x := by
    simpa only [Function.comp_def, id_eq, one_smul, he] using h1
  exact h1'.unique h2

/-- Periodicity cancels the integral of the horizontal second derivative. -/
theorem periodIntegral_horizontal_second {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y)
    {w : ℝ} (hw : 0 ≤ w) (hp : ∀ x, F (point (x + w) y) = F (point x y)) :
    periodIntegral w (directional 1 (directional 1 F)) y = 0 := by
  have hd := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdd := directional_contDiffOn hd (m := 0) (by simp) (1 : ℂ)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := w)
    (fun x _ => slice_horizontal hd hy x)
    ((slice_continuous hdd.continuousOn hy).intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le hw] at h
  change periodIntegral w (directional 1 (directional 1 F)) y = _ at h
  rw [h]
  have hp' := directional_periodic (hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)) hy w hp 0
  exact sub_eq_zero.mpr (by simpa only [zero_add] using hp')

private theorem integral_action (g : SL2Z) (z : ℍ) : integralSL2ToReal g • z = g • z := by
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply]
  rfl

/-- The actual congruence translation gives period `N+1` at every positive height. -/
theorem maass_periodic (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (f.1.1 ∘ ofComplex) (point (x + (N + 1 : ℕ)) y) =
      (f.1.1 ∘ ofComplex) (point x y) := by
  let g : SL2Z := ModularGroup.T ^ ((N + 1 : ℕ) : ℤ)
  have hg : g ∈ CongruenceSubgroup.Gamma (N + 1) := by
    simpa only [Int.natAbs_natCast, g] using
      CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N + 1 : ℕ) (N + 1 : ℕ) (dvd_refl _)
  have hm : integralSL2ToReal g ∈ realImage (CongruenceSubgroup.Gamma (N + 1)) :=
    ⟨g, hg, rfl⟩
  have hp : 0 < (point x y).im := by simpa [point] using hy
  let z : ℍ := ⟨point x y, hp⟩
  have hi := f.1.property ⟨integralSL2ToReal g, hm⟩ z
  rw [integral_action, UpperHalfPlane.modular_T_zpow_smul] at hi
  have hz : ofComplex (point (x + (N + 1 : ℕ)) y) = (N + 1 : ℝ) +ᵥ z := by
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy)]
    simp [point, z, UpperHalfPlane.coe_vadd]
    ring
  change f.1.1 (ofComplex (point (x + (N + 1 : ℕ)) y)) = f.1.1 (ofComplex (point x y))
  rw [hz, ofComplex_apply_of_im_pos hp]
  simpa only [Int.cast_natCast, Int.cast_add, Int.cast_one, Nat.cast_add, Nat.cast_one] using hi

/-- The actual constant Fourier term multiplied by its positive cusp width. -/
def maassMean (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) : ℝ → ℂ :=
  periodIntegral (N + 1 : ℕ) (f.1.1 ∘ ofComplex)

/-- The Maass period integral is differentiable at every positive height. -/
theorem maassMean_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (maassMean N f) (deriv (maassMean N f) y) y :=
  (periodIntegral_hasDerivAt (N + 1 : ℕ)
    (f.2.2.1.1.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)) hy).differentiableAt.hasDerivAt

/-- Its first derivative is also differentiable at every positive height. -/
theorem maassMean_second_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (maassMean N f)) (deriv (deriv (maassMean N f)) y) y :=
  (periodIntegral_second_hasDerivAt (N + 1 : ℕ) f.2.2.1.1 hy).differentiableAt.hasDerivAt

/-- The original hyperbolic eigen-equation yields the exact Euler ODE. -/
theorem maassMean_euler (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 * deriv (deriv (maassMean N f)) y = (lam : ℂ) * maassMean N f y := by
  let F := f.1.1 ∘ ofComplex
  have hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := f.2.2.1.1
  have hd1 := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdI := directional_contDiffOn hf (m := 1) le_rfl Complex.I
  have hi1 : IntegrableOn (fun x => directional 1 (directional 1 F) (point x y))
      (Ioc 0 (N + 1 : ℕ)) :=
    (slice_continuous (directional_contDiffOn hd1 (m := 0) (by simp) 1).continuousOn hy
      ).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiI : IntegrableOn (fun x => directional Complex.I (directional Complex.I F) (point x y))
      (Ioc 0 (N + 1 : ℕ)) :=
    (slice_continuous (directional_contDiffOn hdI (m := 0) (by simp) Complex.I).continuousOn hy
      ).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have he : ∀ x : ℝ,
      -(y : ℂ) ^ 2 * (directional 1 (directional 1 F) (point x y) +
        directional Complex.I (directional Complex.I F) (point x y)) =
      (lam : ℂ) * F (point x y) := by
    intro x
    have hp : 0 < (point x y).im := by simpa [point] using hy
    have hh := f.2.2.1.2 ⟨point x y, hp⟩
    change -(y : ℂ) ^ 2 * (directional 1 (directional 1 F) (point x y) +
      directional Complex.I (directional Complex.I F) (point x y)) =
      (lam : ℂ) * f.1.1 (ofComplex (point x y))
    rw [ofComplex_apply_of_im_pos hp]
    convert hh using 1
    simp [positiveHyperbolicLaplacian, directional, F, UpperHalfPlane.im, point]
    exact Or.inl rfl
  have hint := integral_congr_ae (μ := volume.restrict (Ioc (0 : ℝ) (N + 1 : ℕ)))
    (Filter.Eventually.of_forall he)
  rw [integral_const_mul, integral_const_mul, integral_add hi1 hiI] at hint
  change -(y : ℂ) ^ 2 * (periodIntegral (N + 1 : ℕ) (directional 1 (directional 1 F)) y +
    periodIntegral (N + 1 : ℕ) (directional Complex.I (directional Complex.I F)) y) =
      (lam : ℂ) * periodIntegral (N + 1 : ℕ) F y at hint
  rw [periodIntegral_horizontal_second hf hy (by positivity) (fun x => maass_periodic N f x hy),
    zero_add, ← (periodIntegral_second_hasDerivAt (N + 1 : ℕ) hf hy).deriv] at hint
  exact hint

/-- The defining cusp filter forces the actual finite-width period integral to decay. -/
theorem maassMean_decay (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    Tendsto (maassMean N f) atTop (𝓝 0) := by
  have hc : IsZeroAtImInfty f.1.1 := by
    simpa only [map_one, one_smul] using f.2.2.2 (1 : SL2Z)
  rw [isZeroAtImInfty_iff] at hc
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  have hw : 0 < (N + 1 : ℕ) := Nat.succ_pos N
  have hwR : 0 < ((N + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hw
  obtain ⟨A, hA⟩ := hc (ε / (2 * (N + 1 : ℕ))) (div_pos hε (mul_pos (by linarith) hwR))
  refine ⟨max A 1, fun y hy => ?_⟩
  have hAy : A ≤ y := (le_max_left A 1).trans hy
  have hypos : 0 < y := lt_of_lt_of_le (by linarith : (0 : ℝ) < 1) ((le_max_right A 1).trans hy)
  have hb : ∀ x ∈ Ioc (0 : ℝ) (N + 1 : ℕ),
      ‖(f.1.1 ∘ ofComplex) (point x y)‖ ≤ ε / (2 * (N + 1 : ℕ)) := by
    intro x _
    have hp : 0 < (point x y).im := by simpa [point] using hypos
    simpa only [Function.comp_apply, ofComplex_apply_of_im_pos hp] using
      hA ⟨point x y, hp⟩ (by simpa [UpperHalfPlane.im, point] using hAy)
  have hb' := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top hb
  rw [Real.volume_real_Ioc_of_le hwR.le, sub_zero] at hb'
  have he : ε / (2 * ((N + 1 : ℕ) : ℝ)) * (N + 1 : ℕ) = ε / 2 := by
    field_simp
  rw [he] at hb'
  simpa only [dist_zero_right, maassMean, periodIntegral] using
    hb'.trans_lt (by linarith : ε / 2 < ε)

end
end GaloisForLFunctions.RHTower.SelbergMaassMean
