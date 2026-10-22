import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPositiveHeightOperator
import GaloisForLFunctions.RHTower.SelbergThetaCommonForcing
import GaloisForLFunctions.RHTower.SelbergNativeConstantMode
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Tannery
import GaloisForLFunctions.HTGeometry.SmoothWeight
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
/-!
The reflected theta source satisfies its common-forcing equation in the original
closed native operator. Two-ended compact height seeds converge in native graph
norm; all primitive rows and both cutoff derivative errors are retained. The
source is nonzero, and true constant-mode centering preserves graph admission
and gives exactly the centered full theta forcing. No normalized occurrence
or vanishing of that forcing is asserted.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry
set_option autoImplicit false
namespace RHTower.SelbergThetaCommonForcing
noncomputable section
private def radius (n : ℕ) : ℝ := n+3
private theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity
private theorem radius_inv_le (n : ℕ) : (radius n)⁻¹ ≤ radius n := by
  have hh : 1 ≤ radius n := by unfold radius; have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact (inv_le_one₀ (radius_pos n)).mpr hh |>.trans hh

def cutoff (n : ℕ) (y : ℝ) : ℝ :=
  smoothWeight (radius n) (radius n) y - smoothWeight (radius n)⁻¹ (radius n)⁻¹ y

theorem cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  (smoothWeight_contDiff _ _).sub (smoothWeight_contDiff _ _)

theorem cutoff_low (n : ℕ) (y : ℝ) (hy : y ≤ (radius n)⁻¹) : cutoff n y = 0 := by
  rw [cutoff,smoothWeight_eq_one (radius_pos n) (hy.trans (radius_inv_le n)),
    smoothWeight_eq_one (inv_pos.mpr (radius_pos n)) hy,sub_self]

theorem cutoff_high (n : ℕ) (y : ℝ) (hy : 2*radius n ≤ y) : cutoff n y = 0 := by
  rw [cutoff,smoothWeight_eq_zero (radius_pos n) (by linarith),
    smoothWeight_eq_zero (inv_pos.mpr (radius_pos n)) (by linarith [radius_inv_le n]),sub_self]

theorem cutoff_bound (n : ℕ) (y : ℝ) : |cutoff n y| ≤ 1 := by
  unfold cutoff
  exact abs_le.mpr ⟨by linarith [smoothWeight_nonneg (radius n) (radius n) y,
    smoothWeight_le_one (radius n)⁻¹ (radius n)⁻¹ y],
    by linarith [smoothWeight_le_one (radius n) (radius n) y,
      smoothWeight_nonneg (radius n)⁻¹ (radius n)⁻¹ y]⟩

private theorem cutoff_one_germ (n : ℕ) (y : ℝ)
    (hl : 2*(radius n)⁻¹ < y) (hr : y < radius n) :
    cutoff n =ᶠ[𝓝 y] (fun _ => (1:ℝ)) := by
  filter_upwards [Ioo_mem_nhds hl hr] with t ht
  rw [cutoff,smoothWeight_eq_one (radius_pos n) ht.2.le,
    smoothWeight_eq_zero (inv_pos.mpr (radius_pos n)) (by linarith [ht.1]),sub_zero]

theorem cutoff_eventually_one_germ (y : ℝ) (hy : 0 < y) :
    ∀ᶠ n : ℕ in atTop, cutoff n =ᶠ[𝓝 y] (fun _ => (1:ℝ)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max y (2/y))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnn : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hr : y < radius n := by unfold radius; linarith [le_max_left y (2/y)]
  have hl : 2*(radius n)⁻¹ < y := by
    have h : 2/y < radius n := by unfold radius; linarith [le_max_right y (2/y)]
    have hm : 2 < radius n*y := (div_lt_iff₀ hy).mp h
    rw [← div_eq_mul_inv,div_lt_iff₀ (radius_pos n)]
    nlinarith
  exact cutoff_one_germ n y hl hr

private theorem weight_iterated_high (j : ℕ) (a : ℝ) (ha : 0 < a) (y : ℝ)
    (hy : 2*a < y) : iteratedDeriv j (smoothWeight a a) y = 0 := by
  have he : smoothWeight a a =ᶠ[𝓝 y] (fun _ => (0:ℝ)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact smoothWeight_eq_zero ha (by have ht' : 2*a < t := ht; linarith)
  rw [he.iteratedDeriv_eq j,iteratedDeriv_const]
  simp

private theorem weight_euler_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → ∀ y : ℝ, 0 < y →
      |y^j*iteratedDeriv j (smoothWeight a a) y| ≤ C := by
  obtain ⟨C,hC,hb⟩ := exists_bound_iteratedDeriv_smoothWeight_uniform j
  refine ⟨2^j*C,by positivity,fun a ha y hy => ?_⟩
  by_cases hya : y ≤ 2*a
  · rw [abs_mul,abs_of_nonneg (pow_nonneg hy.le j)]
    calc
      _ ≤ (2*a)^j*(C/a^j) := mul_le_mul (pow_le_pow_left₀ hy.le hya j)
        (hb a a ha y) (abs_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow]; field_simp
  · rw [weight_iterated_high j a ha y (lt_of_not_ge hya),mul_zero,abs_zero]
    positivity

/-- Every Euler derivative of both ends has one uniform analytic bound. -/
theorem cutoff_euler_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ y : ℝ, 0 < y →
      |y^j*iteratedDeriv j (cutoff n) y| ≤ C := by
  obtain ⟨C,hC,hb⟩ := weight_euler_bound j
  refine ⟨2*C,by positivity,fun n y hy => ?_⟩
  have hcd (a : ℝ) : ContDiffAt ℝ (j:ℕ∞ω) (smoothWeight a a) y :=
    (smoothWeight_contDiff _ _ (n := (j:ℕ∞))).contDiffAt
  have he : iteratedDeriv j (cutoff n) y =
      iteratedDeriv j (smoothWeight (radius n) (radius n)) y-
        iteratedDeriv j (smoothWeight (radius n)⁻¹ (radius n)⁻¹) y :=
    iteratedDeriv_fun_sub (hcd _) (hcd _)
  rw [he,mul_sub]
  have htri := abs_sub_le (y^j*iteratedDeriv j (smoothWeight (radius n) (radius n)) y) 0
    (y^j*iteratedDeriv j (smoothWeight (radius n)⁻¹ (radius n)⁻¹) y)
  simp only [sub_zero,zero_sub,abs_neg] at htri
  have hb1 := hb (radius n) (radius_pos n) y hy
  have hb2 := hb ((radius n)⁻¹) (inv_pos.mpr (radius_pos n)) y hy
  exact htri.trans (by linarith)

def compactHeight (q : XiZeroCopy) (n : ℕ) (y : ℝ) : ℂ :=
  (cutoff n y:ℂ)*heightProfile q y

theorem compactHeight_smooth (q : XiZeroCopy) (n : ℕ) : ContDiff ℝ ∞ (compactHeight q n) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0 < y
  · exact (Complex.ofRealCLM.contDiff.comp (cutoff_smooth n)).contDiffAt.mul (height_contDiffAt q y hy)
  · have he : compactHeight q n =ᶠ[𝓝 y] (fun _ => (0:ℂ)) := by
      have hi : y < (radius n)⁻¹ := lt_of_le_of_lt (le_of_not_gt hy) (inv_pos.mpr (radius_pos n))
      filter_upwards [Iio_mem_nhds hi] with t ht
      simp only [compactHeight,cutoff_low n t ht.le,Complex.ofReal_zero,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem compactHeight_support (q : XiZeroCopy) (n : ℕ) :
    tsupport (compactHeight q n) ⊆ Icc (radius n)⁻¹ (2*radius n) := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  constructor
  · by_contra! h
    exact hy (by simp only [compactHeight,cutoff_low n y h.le,Complex.ofReal_zero,zero_mul])
  · by_contra! h
    exact hy (by simp only [compactHeight,cutoff_high n y h.le,Complex.ofReal_zero,zero_mul])

theorem compactHeight_compact (q : XiZeroCopy) (n : ℕ) : HasCompactSupport (compactHeight q n) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (compactHeight_support q n)

private theorem compactHeight_second (q : XiZeroCopy) (n : ℕ) (y : ℝ) (hy : 0 < y) :
    deriv (deriv (compactHeight q n)) y =
      ((deriv (deriv (cutoff n)) y:ℝ):ℂ)*heightProfile q y+
      2*((deriv (cutoff n) y:ℝ):ℂ)*deriv (heightProfile q) y+
      (cutoff n y:ℂ)*deriv (deriv (heightProfile q)) y := by
  have hc := (cutoff_smooth n).differentiable (by simp)
  have hdc := ((contDiff_infty_iff_deriv.mp (cutoff_smooth n)).2).differentiable (by simp)
  have hf : DifferentiableAt ℝ (heightProfile q) y := (height_hasDerivAt q y hy).differentiableAt
  have hdf : DifferentiableAt ℝ (deriv (heightProfile q)) y :=
    ((height_contDiffAt q y hy).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have he : deriv (compactHeight q n) =ᶠ[𝓝 y]
      (fun t => ((deriv (cutoff n) t:ℝ):ℂ)*heightProfile q t+
        (cutoff n t:ℂ)*deriv (heightProfile q) t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
    exact (((hc t).hasDerivAt.ofReal_comp).mul
      ((height_hasDerivAt q t ht).differentiableAt.hasDerivAt)).deriv
  rw [he.deriv_eq]
  have hd := (((hdc y).hasDerivAt.ofReal_comp).mul hf.hasDerivAt).add
    (((hc y).hasDerivAt.ofReal_comp).mul hdf.hasDerivAt)
  simp only [Pi.mul_def,Pi.add_def] at hd
  rw [hd.deriv]
  ring

def compactHeightImage (q : XiZeroCopy) (n : ℕ) (y : ℝ) : ℂ :=
  compactHeight q n y-(y:ℂ)^(2 : ℕ)*deriv (deriv (compactHeight q n)) y

/-- Literal operator image of the compact seed, with both cutoff errors retained. -/
theorem compactHeightImage_eq (q : XiZeroCopy) (n : ℕ) (y : ℝ) (hy : 0 < y) :
    compactHeightImage q n y = energy q*compactHeight q n y-
      (cutoff n y:ℂ)*(SelbergThetaNativeSource.positiveProfile y:ℂ)/4-
      2*((y*deriv (cutoff n) y:ℝ):ℂ)*((y:ℂ)*deriv (heightProfile q) y)-
      ((y^(2 : ℕ)*deriv (deriv (cutoff n)) y:ℝ):ℂ)*heightProfile q y := by
  unfold compactHeightImage
  rw [compactHeight_second q n y hy]
  unfold compactHeight
  have he := height_residual q y hy
  push_cast
  linear_combination (cutoff n y:ℂ)*he

/-- Both compact seed and operator image agree locally with the original at each positive height. -/
theorem compactHeight_eventually_eq (q : XiZeroCopy) (y : ℝ) (hy : 0 < y) :
    ∀ᶠ n : ℕ in atTop, compactHeight q n =ᶠ[𝓝 y] heightProfile q := by
  filter_upwards [cutoff_eventually_one_germ y hy] with n hn
  filter_upwards [hn] with t ht
  simp only [compactHeight,ht,Complex.ofReal_one,one_mul]

private theorem positiveProfile_pos (y : ℝ) : 0 < SelbergThetaNativeSource.positiveProfile y :=
  mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all _)

/-- Every compact source has the same original positive theta majorant. -/
theorem compactHeight_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 < C ∧ ∀ n y, ‖compactHeight q n y‖ ≤ C*SelbergThetaNativeSource.positiveProfile y := by
  obtain ⟨C,hC,hb⟩ := heightProfile_bound q
  refine ⟨C,hC,fun n y => ?_⟩
  rw [compactHeight,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (cutoff_bound n y) (norm_nonneg _)).trans (by simpa using hb y)

/-- The complete compact operator images have a single admitted theta majorant. -/
theorem compactHeightImage_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 < C ∧ ∀ n y, 0 < y →
      ‖compactHeightImage q n y‖ ≤ C*SelbergThetaNativeSource.positiveProfile y := by
  obtain ⟨C,hC,hb⟩ := compactHeight_bound q
  obtain ⟨D,hD,hd⟩ := height_euler_bound q
  obtain ⟨E,hE,he⟩ := heightProfile_bound q
  obtain ⟨a,ha,hab⟩ := cutoff_euler_bound 1
  obtain ⟨b,hb0,hbb⟩ := cutoff_euler_bound 2
  refine ⟨‖energy q‖*C+1/4+2*a*D+b*E,by positivity,fun n y hy => ?_⟩
  have hc1 : ‖((y*deriv (cutoff n) y:ℝ):ℂ)‖ ≤ a := by
    simpa only [pow_one,iteratedDeriv_one,Complex.norm_real,Real.norm_eq_abs] using hab n y hy
  have hc2 : ‖((y^(2 : ℕ)*deriv (deriv (cutoff n)) y:ℝ):ℂ)‖ ≤ b := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero,Complex.norm_real,Real.norm_eq_abs] using hbb n y hy
  have hc : ‖(cutoff n y:ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using cutoff_bound n y
  have hp : ‖(SelbergThetaNativeSource.positiveProfile y:ℂ)‖ = SelbergThetaNativeSource.positiveProfile y := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positiveProfile_pos y)]
  rw [compactHeightImage_eq q n y hy]
  calc
    _ ≤ ‖energy q*compactHeight q n y‖+
        ‖(cutoff n y:ℂ)*(SelbergThetaNativeSource.positiveProfile y:ℂ)/4‖+
        ‖2*((y*deriv (cutoff n) y:ℝ):ℂ)*((y:ℂ)*deriv (heightProfile q) y)‖+
        ‖((y^(2 : ℕ)*deriv (deriv (cutoff n)) y:ℝ):ℂ)*heightProfile q y‖ :=
      (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by
      simp only [norm_mul,norm_div,Complex.norm_ofNat,hp]
      have h0 := mul_le_mul_of_nonneg_left (hb n y) (norm_nonneg (energy q))
      have h1 := mul_le_mul_of_nonneg_right hc (positiveProfile_pos y).le
      have h2 := mul_le_mul hc1 (hd y hy) (norm_nonneg _) ha
      have h3 := mul_le_mul hc2 (he y) (norm_nonneg _) hb0
      rw [norm_mul] at h2
      nlinarith

open D4BMGlobalAngularResponse SelbergThetaNativeSource D4BMModularCore D4BMJointSource
private theorem native_dominated
    (f : ℕ → Lp ℂ 2 angularMeasure) (g : Lp ℂ 2 angularMeasure)
    (F : ℕ → UpperHalfPlane → ℂ) (G : UpperHalfPlane → ℂ)
    (hf : ∀ n, (f n : UpperHalfPlane → ℂ) =ᵐ[angularMeasure] F n)
    (hg : (g : UpperHalfPlane → ℂ) =ᵐ[angularMeasure] G)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n z, ‖F n z‖ ≤ C*positiveSource z)
    (ht : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (G z))) :
    Tendsto f atTop (𝓝 g) := by
  have hG (z : UpperHalfPlane) : ‖G z‖ ≤ C*positiveSource z :=
    le_of_tendsto (ht z).norm (Eventually.of_forall (fun n => hb n z))
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) angularMeasure :=
    (Lp.aestronglyMeasurable (f n)).congr (hf n)
  have hGm : AEStronglyMeasurable G angularMeasure :=
    (Lp.aestronglyMeasurable g).congr hg
  have hi : Integrable (fun z => (2*C)^(2 : ℕ)*positiveSource z^(2 : ℕ)) angularMeasure :=
    positiveSource_memLp.integrable_sq.const_mul _
  have hlim : Tendsto (fun n => ∫ z, ‖F n z-G z‖^(2 : ℕ) ∂angularMeasure) atTop (𝓝 0) := by
    have hl := tendsto_integral_of_dominated_convergence
      (μ := angularMeasure) (F := fun n z => ‖F n z-G z‖^(2 : ℕ)) (f := fun _ => (0:ℝ))
      (fun z => (2*C)^(2 : ℕ)*positiveSource z^(2 : ℕ))
      (fun n => ((hFm n).sub hGm).norm.pow 2) hi
      (fun n => Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        have hp : 0 ≤ C*positiveSource z := mul_nonneg hC (positiveSource_pos z).le
        have hs : ‖F n z-G z‖ ≤ 2*(C*positiveSource z) := by
          nlinarith [norm_sub_le (F n z) (G z),hb n z,hG z]
        calc
          _ ≤ (2*(C*positiveSource z))^(2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) hs 2
          _ = _ := by ring))
      (Eventually.of_forall (fun z => by
        have h := (((ht z).sub_const (G z)).norm).pow 2
        simpa using h))
    simpa only [integral_zero] using hl
  have he (n : ℕ) : ‖f n-g‖^(2 : ℕ) = ∫ z, ‖F n z-G z‖^(2 : ℕ) ∂angularMeasure := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (f n) g,hf n,hg] with z hs hfn hgn
    rw [hs,Pi.sub_apply,hfn,hgn]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun n => ‖f n-g‖^(2 : ℕ)) atTop (𝓝 0) := hlim.congr (fun n => (he n).symm)
  have h := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using h

def compactTest (q : XiZeroCopy) (n : ℕ) : PositiveHeightTest where
  field := compactHeight q n
  smooth := compactHeight_smooth q n
  compact := compactHeight_compact q n
  support := fun _ hy => lt_of_lt_of_le (inv_pos.mpr (radius_pos n)) ((compactHeight_support q n) hy).1

/-- Constructed compact approximants in the actual native graph domain. -/
def approximateDomain (q : XiZeroCopy) (n : ℕ) : energyOperator.domain :=
  (compactTest q n).operatorVector

private def rows (f : ℝ → ℂ) (z : UpperHalfPlane) : ℂ :=
  ∑' v : gammaSetHalf, f (gammaSetMatrix v.1 • z).im

private theorem positive_rows_summable (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => positiveProfile (gammaSetMatrix v.1 • z).im) := by
  obtain ⟨C,_,hb⟩ := positiveProfile_power_bound 2
  apply Summable.of_norm_bounded ((positiveCuspRows_summable 2 (by norm_num) z).mul_left C)
  intro v
  rw [Real.norm_eq_abs,abs_of_pos (positiveProfile_pos (gammaSetMatrix v.1 • z).im)]
  exact hb _ (gammaSetMatrix v.1 • z).im_pos

private theorem rows_summable (f : ℝ → ℂ) (C : ℝ)
    (hb : ∀ y : ℝ, 0 < y → ‖f y‖ ≤ C*positiveProfile y) (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => f (gammaSetMatrix v.1 • z).im) :=
  Summable.of_norm_bounded ((positive_rows_summable z).mul_left C)
    (fun v => hb _ (gammaSetMatrix v.1 • z).im_pos)

private theorem rows_bound (f : ℝ → ℂ) (C : ℝ)
    (hb : ∀ y : ℝ, 0 < y → ‖f y‖ ≤ C*positiveProfile y) (z : UpperHalfPlane) :
    ‖rows f z‖ ≤ C*positiveSource z := by
  have h := tsum_of_norm_bounded ((positive_rows_summable z).mul_left C).hasSum
    (fun v => hb _ (gammaSetMatrix v.1 • z).im_pos)
  simpa only [tsum_mul_left,rows,positiveSource] using h

private theorem approximateDomain_coe (q : XiZeroCopy) (n : ℕ) :
    ((approximateDomain q n : Space) : UpperHalfPlane → ℂ) =ᵐ[angularMeasure]
      rows (compactHeight q n) :=
  (compactTest q n).operatorVector_coe

private theorem approximateDomain_image_coe (q : XiZeroCopy) (n : ℕ) :
    (energyOperator (approximateDomain q n) : UpperHalfPlane → ℂ) =ᵐ[angularMeasure]
      rows (compactHeightImage q n) := by
  obtain ⟨C,_,hb⟩ := compactHeight_bound q
  have hs (z : UpperHalfPlane) := rows_summable (compactHeight q n) C (fun y _ => hb n y) z
  filter_upwards [(compactTest q n).energyOperator_coe] with z hz
  change (energyOperator (compactTest q n).operatorVector : UpperHalfPlane → ℂ) z = _
  rw [hz]
  exact ((hs z).tsum_sub ((compactTest q n).laplace_rows_summable z)).symm

/-- The original full source as an actual native Hilbert vector. -/
def nativeSource (q : XiZeroCopy) : Space := (source_memLp q).toLp (source q)

private theorem nativeSource_coe (q : XiZeroCopy) :
    (nativeSource q : UpperHalfPlane → ℂ) =ᵐ[angularMeasure] source q :=
  (source_memLp q).coeFn_toLp

/-- The fixed full theta forcing as an actual native vector. -/
def nativePositive : Space := positiveSource_memLp.ofReal.toLp (fun z => (positiveSource z:ℂ))

private theorem nativePositive_coe :
    (nativePositive : UpperHalfPlane → ℂ) =ᵐ[angularMeasure] (fun z => (positiveSource z:ℂ)) :=
  positiveSource_memLp.ofReal.coeFn_toLp

private def nativeImage (q : XiZeroCopy) : Space := energy q • nativeSource q-(1/4:ℂ) • nativePositive

private theorem nativeImage_coe (q : XiZeroCopy) :
    (nativeImage q : UpperHalfPlane → ℂ) =ᵐ[angularMeasure]
      (fun z => energy q*source q z-(positiveSource z:ℂ)/4) := by
  filter_upwards [Lp.coeFn_sub (energy q • nativeSource q) ((1/4:ℂ) • nativePositive),
    Lp.coeFn_smul (energy q) (nativeSource q),Lp.coeFn_smul (1/4:ℂ) nativePositive,
    nativeSource_coe q,nativePositive_coe] with z hs he hp hq hP
  change (energy q • nativeSource q-(1/4:ℂ) • nativePositive : Space) z = _
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hs he hp
  rw [hs,he,hp,hq,hP]
  ring

/-- The compact native values converge strongly to the literal reflected source. -/
theorem approximateDomain_tendsto (q : XiZeroCopy) :
    Tendsto (fun n => (approximateDomain q n : Space)) atTop (𝓝 (nativeSource q)) := by
  obtain ⟨C,hC,hb⟩ := compactHeight_bound q
  apply native_dominated _ _ (fun n => rows (compactHeight q n)) (source q)
    (approximateDomain_coe q) (nativeSource_coe q) C hC.le
    (fun n z => rows_bound _ C (fun y _ => hb n y) z)
  intro z
  rw [source_eq_rows]
  exact tendsto_tsum_of_dominated_convergence ((positive_rows_summable z).mul_left C)
    (fun v => tendsto_const_nhds.congr' ((compactHeight_eventually_eq q _ (gammaSetMatrix v.1 • z).im_pos).mono
      (fun n hn => hn.eq_of_nhds.symm)))
    (Eventually.of_forall (fun n v => hb n _))

private theorem compactHeightImage_eventually_eq (q : XiZeroCopy) (y : ℝ) (hy : 0 < y) :
    ∀ᶠ n : ℕ in atTop, compactHeightImage q n y =
      energy q*heightProfile q y-(positiveProfile y:ℂ)/4 := by
  filter_upwards [compactHeight_eventually_eq q y hy] with n hn
  rw [compactHeightImage,hn.eq_of_nhds,hn.deriv.deriv_eq]
  linear_combination height_residual q y hy

private theorem image_rows (q : XiZeroCopy) (z : UpperHalfPlane) :
    (∑' v : gammaSetHalf, (energy q*heightProfile q (gammaSetMatrix v.1 • z).im-
      (positiveProfile (gammaSetMatrix v.1 • z).im:ℂ)/4)) =
      energy q*source q z-(positiveSource z:ℂ)/4 := by
  have hp : Summable (fun v : gammaSetHalf => (positiveProfile (gammaSetMatrix v.1 • z).im:ℂ)) :=
    Complex.ofRealCLM.summable (positive_rows_summable z)
  rw [((height_rows_summable q z).mul_left (energy q)).tsum_sub (hp.div_const 4),
    tsum_mul_left,tsum_div_const,← Complex.ofReal_tsum,← source_eq_rows]
  rfl

/-- The full compact native operator images converge strongly, including both cutoff errors. -/
theorem approximateDomain_image_tendsto (q : XiZeroCopy) :
    Tendsto (fun n => energyOperator (approximateDomain q n)) atTop (𝓝 (nativeImage q)) := by
  obtain ⟨C,hC,hb⟩ := compactHeightImage_bound q
  apply native_dominated _ _ (fun n => rows (compactHeightImage q n))
    (fun z => energy q*source q z-(positiveSource z:ℂ)/4)
    (approximateDomain_image_coe q) (nativeImage_coe q) C hC.le
    (fun n z => rows_bound _ C (hb n) z)
  intro z
  rw [← image_rows q z]
  exact tendsto_tsum_of_dominated_convergence ((positive_rows_summable z).mul_left C)
    (fun v => tendsto_const_nhds.congr' ((compactHeightImage_eventually_eq q _
      (gammaSetMatrix v.1 • z).im_pos).mono (fun n hn => hn.symm)))
    (Eventually.of_forall (fun n v => hb n _ (gammaSetMatrix v.1 • z).im_pos))

open SelbergScatteringEntireOperator

/-- Actual bounded-inverse identity obtained from both native graph limits. -/
theorem nativeCovariance_image (q : XiZeroCopy) :
    nativeCovariance (nativeImage q) = nativeSource q := by
  have ht := (nativeCovariance.continuous.tendsto (nativeImage q)).comp
    (approximateDomain_image_tendsto q)
  have hb (n : ℕ) : nativeCovariance (energyOperator (approximateDomain q n)) =
      (approximateDomain q n : Space) :=
    closedDenseInverse_C_apply nativeCovariance nativeCovariance_injective (approximateDomain q n)
  exact tendsto_nhds_unique (ht.congr hb) (approximateDomain_tendsto q)

/-- The literal reflected theta source belongs to the original closed native operator domain. -/
theorem nativeSource_mem_domain (q : XiZeroCopy) : nativeSource q ∈ energyOperator.domain := by
  rw [← nativeCovariance_image q]
  exact (closedDenseInverse_apply_C nativeCovariance nativeCovariance_injective (nativeImage q)).1

/-- The original source with its proved native graph admission. -/
def nativeDomain (q : XiZeroCopy) : energyOperator.domain :=
  ⟨nativeSource q,nativeSource_mem_domain q⟩

/-- The actual graph image retains the complete common theta forcing. -/
theorem nativeDomain_image (q : XiZeroCopy) : energyOperator (nativeDomain q) = nativeImage q := by
  have h := closedDenseInverse_apply_C nativeCovariance nativeCovariance_injective (nativeImage q)
  have he : nativeDomain q = ⟨nativeCovariance (nativeImage q),h.1⟩ :=
    Subtype.ext (nativeCovariance_image q).symm
  rw [he]
  exact h.2

/-- Unconditional common-forcing equation in the unchanged native closed operator. -/
theorem nativeDomain_equation (q : XiZeroCopy) :
    energyOperator (nativeDomain q)-energy q • (nativeDomain q : Space) =
      -(1/4:ℂ) • nativePositive := by
  rw [nativeDomain_image]
  change (energy q • nativeSource q-(1/4:ℂ) • nativePositive)-energy q • nativeSource q = _
  rw [neg_smul]
  abel

/-- Exact native covariance transport of the same original forcing and full complex energy. -/
theorem nativeSource_resolvent_equation (q : XiZeroCopy) :
    nativeSource q-energy q • nativeCovariance (nativeSource q) =
      -(1/4:ℂ) • nativeCovariance nativePositive := by
  have h := nativeCovariance_image q
  rw [nativeImage,map_sub,map_smul,map_smul] at h
  rw [neg_smul]
  exact sub_eq_iff_eq_add.mpr (by simpa only [sub_eq_add_neg,add_comm] using h.symm)


/-- The constructed native source is nonzero; its exact source mean certifies survival. -/
theorem nativeSource_ne_zero (q : XiZeroCopy) : nativeSource q ≠ 0 := by
  intro hz
  have he : source q =ᵐ[angularMeasure] (fun _ => (0:ℂ)) := by
    have h := nativeSource_coe q
    rw [hz] at h
    exact h.symm.trans (Lp.coeFn_zero ℂ 2 angularMeasure)
  have hi : (∫ z, source q z ∂angularMeasure) = 0 := by
    rw [integral_congr_ae he,integral_zero]
  rw [source_integral] at hi
  exact (div_ne_zero (Complex.ofReal_ne_zero.mpr sourceMass_pos.ne')
    (mean_denominator_ne_zero q)) hi

open SelbergNativeConstantMode

private def sourceMeanCoefficient (q : XiZeroCopy) : ℂ :=
  inner ℂ constantVector (nativeSource q)/inner ℂ constantVector constantVector

private def positiveMeanCoefficient : ℂ :=
  inner ℂ constantVector nativePositive/inner ℂ constantVector constantVector

private theorem mean_forcing_balance (q : XiZeroCopy) :
    (energy q-1)*sourceMeanCoefficient q = (1/4:ℂ)*positiveMeanCoefficient := by
  have hs : inner ℂ constantVector (nativeSource q) = (sourceMass:ℂ)/(1+(xiSpectralPoint q)^(2 : ℕ)) := by
    rw [inner_constantVector,integral_congr_ae (nativeSource_coe q),source_integral]
  have hp : inner ℂ constantVector nativePositive = (sourceMass:ℂ) := by
    rw [inner_constantVector,integral_congr_ae nativePositive_coe]
    rw [integral_complex_ofReal,positiveSource_integral]
  unfold sourceMeanCoefficient positiveMeanCoefficient
  rw [hs,hp]
  have he : (energy q-1)*((sourceMass:ℂ)/(1+(xiSpectralPoint q)^(2 : ℕ))) = (sourceMass:ℂ)/4 := by
    unfold energy
    field_simp [mean_denominator_ne_zero q]
    ring
  calc
    _ = ((energy q-1)*((sourceMass:ℂ)/(1+(xiSpectralPoint q)^(2 : ℕ))))/
        inner ℂ constantVector constantVector := by ring
    _ = _ := by rw [he]; ring

/-- The literal source centered by the true native constant component, with graph admission retained. -/
def centeredDomain (q : XiZeroCopy) : energyOperator.domain :=
  nativeDomain q-sourceMeanCoefficient q • constantEnergyDomain

/-- The centered graph vector is exactly the original native orthogonal centering. -/
theorem centeredDomain_coe (q : XiZeroCopy) :
    (centeredDomain q : Space) = centered (nativeSource q) := rfl

/-- Exact zero native mean after subtracting the actual constant component. -/
theorem centeredDomain_mean (q : XiZeroCopy) :
    (∫ z, (centeredDomain q : Space) z ∂angularMeasure) = 0 := by
  rw [centeredDomain_coe]
  exact integral_centered _

/-- The centered common forcing equation, in the unchanged original native graph. -/
theorem centeredDomain_equation (q : XiZeroCopy) :
    energyOperator (centeredDomain q)-energy q • (centeredDomain q : Space) =
      -(1/4:ℂ) • centered nativePositive := by
  unfold centeredDomain
  rw [energyOperator.map_sub,energyOperator.map_smul,constantEnergyDomain_operator,nativeDomain_image]
  change (energy q • nativeSource q-(1/4:ℂ) • nativePositive)-
      sourceMeanCoefficient q • constantVector-
      energy q • (nativeSource q-sourceMeanCoefficient q • constantVector) = _
  calc
    _ = -(1/4:ℂ) • nativePositive+
        ((energy q-1)*sourceMeanCoefficient q) • constantVector := by module
    _ = -(1/4:ℂ) • nativePositive+
        ((1/4:ℂ)*positiveMeanCoefficient) • constantVector := by rw [mean_forcing_balance]
    _ = _ := by unfold centered constantComponent positiveMeanCoefficient; module

end
end RHTower.SelbergThetaCommonForcing
