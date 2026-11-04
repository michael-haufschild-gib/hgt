import GaloisForLFunctions.ZeroConfigurationGeometry.WindowsBlindToALattice
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Blind windows at the density aperture

Kernel design (question Q5) asks for windows whose transform vanishes on a given real
configuration and not at a given tilted point. `WindowsBlindToALattice` answers this for one
lattice. This module answers it for every configuration contained in the real zero set of an
exponential polynomial, at the width of that polynomial.

* **Exponential multipliers** (`apertureWindow_expPoly`). For a window `b` of aperture `r₀` and
  real frequencies `|ν_k| ≤ W`, the window `Σ_k c_k b(· + ν_k)` has aperture `r₀ + W` and
  transform `P(w) b̂(w)`, `P(w) = Σ_k c_k e^{−iwν_k}`.
* **Zero sets of exponential polynomials** (`exists_window_blind_to_expPoly_zeros`). For every
  aperture `r > W` and every `z` with `P(z) ≠ 0` there is a window of aperture `r` whose transform
  vanishes at every zero of `P` and not at `z`. This covers the real zero sets of real-rooted
  exponential polynomials, which include Fourier quasicrystals that are not lattices.
* **Sine multipliers** (`apertureWindow_sine`, `exists_window_prod_sine`). Shifting by `±c`
  multiplies the transform by `sin(c(w − τ))` at the cost `c` in aperture, and products compose.
* **Finite unions of lattices** (`exists_window_blind_to_lattices`). Let `Λ_j = τ_j + h_jℤ` be
  finitely many lattices with arbitrary, possibly incommensurable spacings, of total density
  `D = Σ_j 1/h_j`. For every aperture `r > πD` and every `z` off all `Λ_j` there is a window of
  aperture `r` whose transform vanishes on every `Λ_j` and not at `z`: the transform is
  `Π_j sin(π(w − τ_j)/h_j) b̂(w)` with `b̂(z) = 1`.

* **Zero sets of transforms of densities** (`densityTransform`,
  `exists_window_blind_to_densityTransform_zeros`). For an integrable density `φ` supported in
  `[−W, W]` and `Φ(w) = ∫ φ(t) e^{−iwt} dt`, every aperture `r > W` has a window blind to the zero
  set of `Φ` that sees any given `z` with `Φ(z) ≠ 0`: the convolution of a bump with `φ(−·)`, by
  Fubini. This reaches configurations in no exponential-polynomial zero set, for instance the
  zeros of `J₀(w) = (1/π) ∫_{−1}^{1} e^{−iwt} (1 − t²)^{−1/2} dt`, a perturbed lattice of spacing
  asymptotically `π`, blinded at every aperture `> 1 = πD`.
* **Sharpness for one lattice** (`tsum_add_int_eq_zero_of_fourier_eq_zero`,
  `eq_zero_of_blind_to_lattice`, `exists_window_blind_to_lattice_iff`). A window of aperture
  `r ≤ π/h` blind to `hℤ` vanishes: its periodization with period `2π/h` has Fourier coefficients
  `(h/2π) f̂(kh) = 0` (Poisson summation), and at this aperture the translates do not overlap. So a
  window blind to `hℤ` that sees some point exists exactly when `r > π/h`.

The aperture `πD` is the Jensen aperture of density `D`: an entire function of exponential type
`r` vanishing on a set of density `D` needs `r ≥ πD`. So against finite unions of lattices the
camera separates every off-configuration point at the least aperture that density allows. Such a
union need not be uniformly discrete (`ℤ ∪ √2ℤ` has points arbitrarily close), and no separation
enters.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real FourierTransform Convolution

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23

/-- **Exponential multipliers.** `Σ_k c_k b(· + ν_k)` has aperture `r₀ + W` and transform
`(Σ_k c_k e^{−iwν_k}) b̂(w)`. -/
theorem apertureWindow_expPoly {ι : Type*} (S : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) {r₀ W : ℝ}
    (hν : ∀ k ∈ S, |ν k| ≤ W) {b : ℝ → ℂ} (hb : ApertureWindow r₀ b) :
    ApertureWindow (r₀ + W) (fun u => ∑ k ∈ S, c k * b (u + ν k)) ∧
      ∀ w : ℂ, paperFT (fun u => ∑ k ∈ S, c k * b (u + ν k)) w =
        (∑ k ∈ S, c k * cexp (-(I * w * ν k))) * paperFT b w := by
  have hbc := hb.hasCompactSupport
  have hbcont := hb.1.continuous
  refine ⟨⟨?_, ?_⟩, fun w => ?_⟩
  · exact ContDiff.sum fun k _ => contDiff_const.mul (hb.1.comp (contDiff_id.add contDiff_const))
  · refine closure_minimal (fun u hu => ?_) isClosed_Icc
    obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
    have h1 : b (u + ν k) ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨l1, l2⟩ := hb.2 (subset_tsupport _ h1)
    have := abs_le.mp (hν k hk)
    exact ⟨by linarith [this.1, this.2], by linarith [this.1, this.2]⟩
  · have hint : ∀ k ∈ S, Integrable fun u : ℝ => c k * b (u + ν k) * cexp (I * w * u) :=
      fun k _ =>
        ((continuous_const.mul (hbcont.comp (continuous_id.add continuous_const))).mul
          (by fun_prop)).integrable_of_hasCompactSupport
          ((hbc.comp_homeomorph (Homeomorph.addRight (ν k))).mul_left.mul_right)
    rw [paperFT_def, show (fun u : ℝ => (∑ k ∈ S, c k * b (u + ν k)) * cexp (I * w * u)) =
      fun u => ∑ k ∈ S, c k * b (u + ν k) * cexp (I * w * u) by
        funext u; rw [Finset.sum_mul], integral_finsetSum S hint, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := paperFT_shift b (ν k) w
    rw [paperFT_def, paperFT_def] at h
    rw [show (fun u : ℝ => c k * b (u + ν k) * cexp (I * w * u)) =
      fun u => c k * (b (u + ν k) * cexp (I * w * u)) by funext u; ring, integral_const_mul, h,
      paperFT_def]
    ring

/-- **Windows blind to the zero set of an exponential polynomial.** -/
theorem exists_window_blind_to_expPoly_zeros {ι : Type*} (S : Finset ι) (c : ι → ℂ) (ν : ι → ℝ)
    {W r : ℝ} (hν : ∀ k ∈ S, |ν k| ≤ W) (hr : W < r) {z : ℂ}
    (hz : ∑ k ∈ S, c k * cexp (-(I * z * ν k)) ≠ 0) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧
      (∀ w : ℂ, ∑ k ∈ S, c k * cexp (-(I * w * ν k)) = 0 → paperFT f w = 0) ∧
      paperFT f z ≠ 0 := by
  obtain ⟨b, hb, hb1⟩ := exists_window_paperFT_eq_one (by linarith : 0 < r - W) z
  obtain ⟨hf, hft⟩ := apertureWindow_expPoly S c ν hν hb
  rw [sub_add_cancel] at hf
  refine ⟨_, hf, fun w hw => by rw [hft, hw, zero_mul], ?_⟩
  rw [hft, hb1, mul_one]
  exact hz

/-- **Sine multipliers.** Shifting by `±c` multiplies the transform by `sin(c(w − τ))`. -/
theorem apertureWindow_sine {r₀ c τ : ℝ} (hc : 0 ≤ c) {g : ℝ → ℂ} (hg : ApertureWindow r₀ g) :
    ∃ f : ℝ → ℂ, ApertureWindow (r₀ + c) f ∧
      ∀ w : ℂ, paperFT f w = Complex.sin (c * (w - τ)) * paperFT g w := by
  obtain ⟨hf, hft⟩ := apertureWindow_expPoly Finset.univ
    (fun k : Bool => if k then -cexp (I * c * τ) / (2 * I) else cexp (-(I * c * τ)) / (2 * I))
    (fun k : Bool => if k then c else -c) (W := c)
    (fun k _ => by cases k <;> simp [abs_of_nonneg hc]) hg
  refine ⟨_, hf, fun w => ?_⟩
  rw [hft, Fintype.sum_bool]
  congr 1
  simp only [if_true, Bool.false_eq_true, if_false, Complex.ofReal_neg]
  have e1 : cexp (I * c * τ) * cexp (-(I * w * c)) = cexp (-(c * (w - τ)) * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : cexp (-(I * c * τ)) * cexp (-(I * w * -c)) = cexp ((c * (w - τ)) * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [Complex.sin, div_mul_eq_mul_div, div_mul_eq_mul_div, neg_mul, e1, e2]
  have hI : I * I = -1 := Complex.I_mul_I
  field_simp
  linear_combination (cexp (c * (w - τ) * I) - cexp (-(c * (w - τ) * I))) * hI

/-- **Products of sine multipliers.** -/
theorem exists_window_prod_sine {ι : Type*} [DecidableEq ι] (S : Finset ι) (c τ : ι → ℝ)
    (hc : ∀ j ∈ S, 0 ≤ c j) {r₀ : ℝ} {b : ℝ → ℂ} (hb : ApertureWindow r₀ b) :
    ∃ f : ℝ → ℂ, ApertureWindow (r₀ + ∑ j ∈ S, c j) f ∧
      ∀ w : ℂ, paperFT f w = (∏ j ∈ S, Complex.sin (c j * (w - τ j))) * paperFT b w := by
  induction S using Finset.induction_on with
  | empty => exact ⟨b, by simpa using hb, fun w => by simp⟩
  | insert j S hj ih =>
    obtain ⟨g, hg, hgt⟩ := ih fun i hi => hc i (Finset.mem_insert_of_mem hi)
    obtain ⟨f, hf, hft⟩ := apertureWindow_sine (τ := τ j) (hc j (Finset.mem_insert_self j S)) hg
    refine ⟨f, ?_, fun w => ?_⟩
    · rw [Finset.sum_insert hj]
      convert hf using 1
      ring
    · rw [Finset.prod_insert hj, hft, hgt]
      ring

/-- **Windows blind to finitely many lattices at the density aperture.** For lattices
`τ_j + h_jℤ`, `j ∈ S`, of total density `D = Σ_j 1/h_j`, every aperture `r > πD` and every `z` off
all of them, some window of aperture `r` has transform vanishing on every lattice and not at
`z`. -/
theorem exists_window_blind_to_lattices {ι : Type*} [DecidableEq ι] (S : Finset ι) (τ h : ι → ℝ)
    (hh : ∀ j ∈ S, 0 < h j) {r : ℝ} (hr : π * ∑ j ∈ S, (h j)⁻¹ < r) {z : ℂ}
    (hz : ∀ j ∈ S, ∀ k : ℤ, z ≠ τ j + k * h j) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ j ∈ S, ∀ k : ℤ, paperFT f (τ j + k * h j) = 0) ∧
      paperFT f z ≠ 0 := by
  obtain ⟨b, hb, hb1⟩ := exists_window_paperFT_eq_one
    (by linarith : 0 < r - π * ∑ j ∈ S, (h j)⁻¹) z
  obtain ⟨f, hf, hft⟩ := exists_window_prod_sine S (fun j => π / h j) τ
    (fun j hj => (div_pos Real.pi_pos (hh j hj)).le) hb
  have hsum : r - π * ∑ j ∈ S, (h j)⁻¹ + ∑ j ∈ S, π / h j = r := by
    rw [Finset.mul_sum]
    simp only [div_eq_mul_inv]
    ring
  rw [hsum] at hf
  refine ⟨f, hf, fun j hj k => ?_, ?_⟩
  · rw [hft, Finset.prod_eq_zero hj, zero_mul]
    have hh' : (h j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hh j hj).ne'
    rw [show (((π / h j : ℝ)) : ℂ) * ((τ j : ℂ) + k * h j - τ j) = k * π by
      push_cast; field_simp; ring]
    exact Complex.sin_int_mul_pi k
  · rw [hft, hb1, mul_one, Finset.prod_ne_zero_iff]
    intro j hj h0
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h0
    apply hz j hj k
    have hh' : (h j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hh j hj).ne'
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast at hk
    field_simp at hk
    linear_combination hk

/-! ### Sharpness for one lattice -/

/-- **Poisson periodization of a Fourier-blind function.** A continuous compactly supported
function whose Fourier transform vanishes at every integer has vanishing `1`-periodization. -/
theorem tsum_add_int_eq_zero_of_fourier_eq_zero {ρ : ℝ → ℂ} (hc : Continuous ρ)
    (hcs : HasCompactSupport ρ) (h0 : ∀ n : ℤ, 𝓕 ρ n = 0) (x : ℝ) :
    ∑' k : ℤ, ρ (x + k) = 0 := by
  set ρc : C(ℝ, ℂ) := ⟨ρ, hc⟩ with hρc
  obtain ⟨B, hB⟩ : ∃ B, ∀ y, ρ y ≠ 0 → |y| ≤ B := by
    obtain ⟨B, hB⟩ := hcs.isCompact.isBounded.subset_closedBall 0
    refine ⟨B, fun y hy => ?_⟩
    have := hB (subset_tsupport _ hy)
    rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  have h_norm : ∀ K : TopologicalSpace.Compacts ℝ,
      Summable fun n : ℤ => ‖(ρc.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ := by
    intro K
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
    obtain ⟨N, hN⟩ := exists_int_gt (R + B)
    refine summable_of_ne_finset_zero (s := Finset.Icc (-N) N) fun n hn => ?_
    rw [norm_eq_zero]
    ext ⟨y, hy⟩
    have hyR : |y| ≤ R := by
      have := hR hy
      rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    have hn' : (N : ℝ) < |(n : ℝ)| := by
      rw [Finset.mem_Icc] at hn
      have : N < |n| := by rw [lt_abs]; omega
      exact_mod_cast this
    have hbig : B < |y + n| := by
      have h3 := abs_add_le (y + n) (-y)
      have e1 : y + n + -y = (n : ℝ) := by ring
      rw [e1, abs_neg] at h3
      linarith
    simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_addRight, ContinuousMap.zero_apply, hρc, ContinuousMap.coe_mk]
    by_contra hne
    linarith [hB _ hne]
  have hcoe : (ρc : ℝ → ℂ) = ρ := rfl
  have h_sum : Summable fun n : ℤ => 𝓕 (ρc : ℝ → ℂ) n := by
    rw [hcoe, show (fun n : ℤ => 𝓕 ρ n) = fun _ => 0 from funext fun n => h0 n]
    exact summable_zero
  have hP := Real.tsum_eq_tsum_fourier h_norm h_sum x
  rw [hcoe, show (fun n : ℤ => 𝓕 ρ n * fourier n (x : UnitAddCircle)) = fun _ => 0 from
    funext fun n => by rw [h0 n, zero_mul], tsum_zero] at hP
  exact hP

/-- **At most `π/h`, no window is blind to `hℤ`.** A continuous window supported in `[−r, r]` with
`r ≤ π/h` whose transform vanishes on `hℤ` is zero. Its rescaled periodization with period `2π/h`
has the Fourier coefficients `(h/2π) f̂(kh) = 0`, and at this aperture the translates do not
overlap. -/
theorem eq_zero_of_blind_to_lattice {h r : ℝ} (hh : 0 < h) (hr : r ≤ π / h) {f : ℝ → ℂ}
    (hf : Continuous f) (hfs : tsupport f ⊆ Icc (-r) r)
    (hblind : ∀ k : ℤ, paperFT f ((k : ℂ) * h) = 0) : f = 0 := by
  set T := 2 * π / h with hT
  have hT0 : 0 < T := by positivity
  have hTh : T * h = 2 * π := by rw [hT]; field_simp
  set ρ : ℝ → ℂ := fun x => f (-T * x) with hρ
  have hρc : Continuous ρ := hf.comp (continuous_const.mul continuous_id)
  have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  have hρcs : HasCompactSupport ρ :=
    hfc.comp_homeomorph (Homeomorph.mulLeft₀ (-T) (by linarith))
  -- the Fourier coefficients of `ρ` are multiples of `f̂(nh)`
  have hF : ∀ n : ℤ, 𝓕 ρ n = 0 := by
    intro n
    set g : ℝ → ℂ := fun u => cexp (↑(2 * π * u * n / T) * I) • f u with hg
    have hpt : ∀ v : ℝ, cexp (↑(-2 * π * v * n) * I) • ρ v = g (-T * v) := by
      intro v
      have e : (2 * π * (-T * v) * n / T : ℝ) = -2 * π * v * n := by field_simp
      simp only [hρ, hg, e]
    have hgf : ∫ u : ℝ, g u = paperFT f ((n : ℂ) * h) := by
      rw [paperFT_def]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      have e : ((2 * π * u * n / T : ℝ) : ℂ) * I = I * ((n : ℂ) * h) * u := by
        rw [show (2 * π * u * n / T : ℝ) = n * h * u by rw [hT]; field_simp]
        push_cast
        ring
      simp only [hg, smul_eq_mul, e]
      ring
    calc 𝓕 ρ n = ∫ v : ℝ, g (-T * v) := by
          rw [Real.fourier_real_eq_integral_exp_smul]
          exact integral_congr_ae (Eventually.of_forall hpt)
      _ = |(-T)⁻¹| • ∫ u : ℝ, g u := Measure.integral_comp_mul_left g (-T)
      _ = 0 := by rw [hgf, hblind n, smul_zero]
  have hP := tsum_add_int_eq_zero_of_fourier_eq_zero hρc hρcs hF
  -- the support of `ρ` lies in `[−½, ½]`
  have hsupp : ∀ y, ρ y ≠ 0 → |y| ≤ 1 / 2 := by
    intro y hy
    obtain ⟨h1, h2⟩ := hfs (subset_tsupport _ hy)
    have hTy : |T * y| ≤ T / 2 := by
      rw [abs_le]
      have hrT : r ≤ T / 2 := by rw [hT]; linarith [show π / h = 2 * π / h / 2 by ring]
      constructor <;> nlinarith
    rw [abs_mul, abs_of_pos hT0] at hTy
    nlinarith
  -- inside the period only the term `k = 0` survives
  have hzero : ∀ x : ℝ, |x| < 1 / 2 → ρ x = 0 := by
    intro x hx
    have h := hP x
    rwa [tsum_eq_single 0 (fun k hk => ?_), Int.cast_zero, add_zero] at h
    by_contra hne
    have h1 := hsupp _ hne
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have h2 := abs_sub_abs_le_abs_sub (k : ℝ) (-x)
    rw [abs_neg, sub_neg_eq_add, add_comm] at h2
    linarith
  -- and on the boundary by continuity
  have hall : ∀ x : ℝ, ρ x = 0 := by
    intro x
    rcases lt_trichotomy |x| (1 / 2) with hx | hx | hx
    · exact hzero x hx
    · have hlim : Tendsto (fun t : ℝ => ρ (t * x)) (𝓝[<] 1) (𝓝 (ρ x)) := by
        have h1 : Tendsto (fun t : ℝ => t * x) (𝓝 1) (𝓝 x) := by
          have := ((continuous_mul_const x).tendsto 1)
          rwa [one_mul] at this
        exact (hρc.tendsto x).comp (h1.mono_left nhdsWithin_le_nhds)
      have hev : (fun t : ℝ => ρ (t * x)) =ᶠ[𝓝[<] 1] fun _ => 0 := by
        filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
        refine hzero _ ?_
        rw [abs_mul, abs_of_pos ht.1, hx]
        nlinarith [ht.2]
      exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
    · by_contra hne
      linarith [hsupp x hne]
  funext u
  have := hall (-u / T)
  simp only [hρ] at this
  rwa [show -T * (-u / T) = u by field_simp] at this

/-- **The lattice threshold is sharp.** A window of aperture `r` blind to `hℤ` and seeing some
point exists exactly when `r > π/h`. -/
theorem exists_window_blind_to_lattice_iff {h r : ℝ} (hh : 0 < h) :
    (∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ k : ℤ, paperFT f ((k : ℂ) * h) = 0) ∧
      ∃ z, paperFT f z ≠ 0) ↔ π / h < r := by
  constructor
  · rintro ⟨f, hf, hblind, z, hz⟩
    by_contra hr
    push Not at hr
    have h0 := eq_zero_of_blind_to_lattice hh hr hf.1.continuous hf.2 hblind
    apply hz
    rw [h0, paperFT_def]
    simp
  · intro hr
    obtain ⟨f, hf, hblind, hz⟩ := exists_window_blind_to_lattice hh hr (z := I) fun k h0 => by
      have := congrArg Complex.im h0
      simp at this
    exact ⟨f, hf, hblind, I, hz⟩

/-! ### Zero sets of Fourier transforms of densities -/

/-- The transform `Φ(w) = ∫ φ(t) e^{−iwt} dt` of a density. -/
def densityTransform (φ : ℝ → ℂ) (w : ℂ) : ℂ := ∫ t, φ t * cexp (-(I * w * t))

/-- A density supported in `[−W, W]` times `e^{±iwt}` stays integrable. -/
theorem integrable_mul_cexp_of_support {φ : ℝ → ℂ} (hφ : Integrable φ) {W : ℝ}
    (hφs : ∀ t, φ t ≠ 0 → |t| ≤ W) (c : ℂ) :
    Integrable fun t : ℝ => φ t * cexp (c * t) := by
  refine Integrable.mono' (hφ.norm.const_mul (Real.exp (‖c‖ * W)))
    (hφ.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ => cexp (c * t)).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  by_cases ht : φ t = 0
  · simp [ht]
  · rw [norm_mul, mul_comm (Real.exp _)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hφs t ht) (norm_nonneg _)

/-- **Windows blind to the zero set of the transform of a density.** Let `φ` be integrable and
supported in `[−W, W]`, and `Φ(w) = ∫ φ(t) e^{−iwt} dt`. For every aperture `r > W` and every `z`
with `Φ(z) ≠ 0` there is a window of aperture `r` whose transform vanishes at every zero of `Φ`
and not at `z`. The window is the convolution of a bump with `φ(−·)`, with transform `Φ b̂`. -/
theorem exists_window_blind_to_densityTransform_zeros {φ : ℝ → ℂ} (hφ : Integrable φ) {W r : ℝ}
    (hφs : ∀ t, φ t ≠ 0 → |t| ≤ W) (hr : W < r) {z : ℂ} (hz : densityTransform φ z ≠ 0) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ w : ℂ, densityTransform φ w = 0 → paperFT f w = 0) ∧
      paperFT f z ≠ 0 := by
  obtain ⟨b, hb, hb1⟩ := exists_window_paperFT_eq_one (by linarith : 0 < r - W) z
  have hbc := hb.hasCompactSupport
  set ψ : ℝ → ℂ := fun s => φ (-s) with hψ
  have hψi : Integrable ψ := hφ.comp_neg
  set L := ContinuousLinearMap.mul ℝ ℂ with hL
  set f : ℝ → ℂ := b ⋆[L, volume] ψ with hf
  have hfapp : ∀ u, f u = ∫ t, b t * φ (t - u) := fun u => by
    rw [hf, convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [hL, hψ, neg_sub]
  -- smoothness and support
  have hfc : ContDiff ℝ 2 f := by
    have h := hbc.contDiff_convolution_left L (n := 2) hb.1 hψi.locallyIntegrable
    exact_mod_cast h
  have hsupp : ∀ u, f u ≠ 0 → u ∈ Icc (-r) r := by
    intro u hu
    by_contra hout
    apply hu
    rw [hfapp]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    simp only [Pi.zero_apply]
    by_cases hbt : b t = 0
    · rw [hbt, zero_mul]
    · by_cases hφt : φ (t - u) = 0
      · rw [hφt, mul_zero]
      · exfalso
        obtain ⟨h1, h2⟩ := hb.2 (subset_tsupport _ hbt)
        have h3 := abs_le.mp (hφs _ hφt)
        exact hout ⟨by linarith [h3.2], by linarith [h3.1]⟩
  have hfw : ApertureWindow r f := ⟨hfc, closure_minimal (fun u hu => hsupp u hu) isClosed_Icc⟩
  -- the transform is `Φ b̂`
  have hft : ∀ w : ℂ, paperFT f w = densityTransform φ w * paperFT b w := by
    intro w
    set B : ℝ → ℂ := fun t => b t * cexp (I * w * t) with hB
    set Ψ : ℝ → ℂ := fun s => φ (-s) * cexp (I * w * s) with hΨ
    have hBi : Integrable B := integrable_mul_cexp hb.1.continuous hbc w
    have hΨi : Integrable Ψ := by
      have h := integrable_mul_cexp_of_support hφ hφs (-(I * w))
      have := h.comp_neg
      refine this.congr (Eventually.of_forall fun s => ?_)
      simp only [hΨ]
      congr 1
      congr 1
      push_cast
      ring
    have hprod := hBi.convolution_integrand L hΨi (μ := volume) (ν := volume)
    have hpt : ∀ u : ℝ, f u * cexp (I * w * u) = ∫ t, L (B t) (Ψ (u - t)) := by
      intro u
      rw [hfapp, ← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hL, hB, hΨ, ContinuousLinearMap.mul_apply', neg_sub]
      rw [show cexp (I * w * u) = cexp (I * w * t) * cexp (I * w * ((u - t : ℝ) : ℂ)) by
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
      ring
    rw [paperFT_def, integral_congr_ae (Eventually.of_forall hpt)]
    rw [integral_integral_swap (f := fun u t => L (B t) (Ψ (u - t))) hprod]
    have hinner : ∀ t : ℝ, ∫ u, L (B t) (Ψ (u - t)) = B t * ∫ s, Ψ s := by
      intro t
      simp only [hL, ContinuousLinearMap.mul_apply']
      rw [integral_const_mul, integral_sub_right_eq_self (fun s => Ψ s) t]
    rw [integral_congr_ae (Eventually.of_forall hinner), integral_mul_const, paperFT_def,
      mul_comm]
    congr 1
    rw [densityTransform, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hΨ, neg_neg]
    congr 2
    push_cast
    ring
  refine ⟨f, hfw, fun w hw => by rw [hft, hw, zero_mul], ?_⟩
  rw [hft, hb1, mul_one]
  exact hz

end GaloisForLFunctions.ZeroConfigurationGeometry
