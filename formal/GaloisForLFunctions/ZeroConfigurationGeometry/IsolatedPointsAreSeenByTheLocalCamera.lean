import GaloisForLFunctions.ZeroConfigurationGeometry.ProductsOverPerturbedLatticesOnTheStrip
import GaloisForLFunctions.ZeroConfigurationGeometry.SparseClustersNeverCancel
import GaloisForLFunctions.ZeroConfigurationGeometry.FarZerosAreFaintInTheLocalCamera
import GaloisForLFunctions.HTGeometry.LinearExponentialSum

/-!
# Isolated points are seen by the local camera

The density criterion `eq_of_mimic_of_count_le` needs a count bound on the whole cluster. The zeros
of `ζ` have density `(1/2π) log(T/2π)`, unbounded in `T`, so for `ζ` the criterion must be
localized: at height `X` only the cluster near `X` may be counted, and the far cluster must be
faint in the camera.

**Uniform isolating windows** (`exists_uniform_isolating_window`). Fix a spacing `H`, an aperture
`r > π/H`, a matching distance `L`, an isolation radius `η` and a decay order `k`. There are
constants `c > 0`, `M` such that every set `P` of camera points of depth `≤ 1/2`, matched
injectively into `HℤH` at distance `≤ L`, and every target `w₀ ∈ i[−½, ½]` at distance `≥ η` from
`P` admit a window `f` of aperture `r` with

* `f̂ = 0` on `P`, `|f̂(w₀)| ≥ c`, and
* `|f̂(w)| (1 + |Re w|)^k ≤ M` on the strip `|Im w| ≤ 1/2`.

The constants do not depend on `P` or `w₀`. The window is the limit window over the perturbed lattice
`ν` that fills the unmatched sites at the half-shifted lattice points, convolved with an even bump
`b`. Its transform is `sin((π/H)(w − θH)) b̂(w)² Π_k r_k(w)`. The bounds are uniform because each
factor is: `|sin| ≥ 1/2` at `w₀` once the lattice shift `θ` lies in `(1/4, 3/4)`;
`b̂(iy) ≥ 1` (`exists_bump_one_le_norm_paperFT_I_mul`); the product floor
`norm_tprod_pertFactor_ge_strip` holds at points `η`-far from `ν`; and the strip growth
`norm_sin_mul_tprod_pertFactor_le_strip` is polynomial and absorbed by the decay of `b̂`.

**The local camera** (`one_add_pow_le_of_isolated_cancellation`). Let `Z, Z'` be tempered mimics at
aperture `a`, and let `z₀` be a point of their cluster at height `X`. Suppose that every other cluster
point with height in `[X − R, X + R]` is at distance `≥ η` from `z₀`, and that these points have
count bound `(D, C₀)` with `πD < 2a`. Then `(1 + R)^{2k−2} ≤ B (1 + |X|)² Σ_z |c(z)|/(1 + |γ_z|²)`,
with `B` depending only on `a, D, C₀, η, k`.

Proof. Translate the local cluster to height `0`, match it into `D⁻¹ℤ` and split it by parity, as
in `eq_of_mimic_of_count_le`. The uniform windows blind the two halves and see `z₀` with
`|f̂| |ĝ| ≥ c²`. Modulated to height `X`, they kill every near point except `z₀`. The far cluster
contributes at most `M² e^a (5/4)(1 + |X|)²/(1 + R)^{2k−2} Σ |c|/(1 + |γ|²)`
(`norm_tsum_far_le`). Mimicry makes the total zero, and `|c(z₀)| ≥ 1`.

So an isolated cancelling point at height `X` forces the cluster to reach density `2a/π` within
distance `R ≍ (1 + |X|)^{1/(k−1)}` of `X`, for every `k`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate Convolution

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-! ### An even bump seen on the imaginary axis -/

/-- **An even bump seen on the imaginary axis.** The normalized bump `b ≥ 0` of radius `ε` has
`b̂(iy) = ∫ b(u) e^{−yu} du ≥ ∫ b(u)(1 − yu) du = 1`, since `b` is even. -/
theorem exists_bump_one_le_norm_paperFT_I_mul {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) b ∧ tsupport b ⊆ Icc (-ε) ε ∧
      ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖ := by
  let B : ContDiffBump (0 : ℝ) := ⟨ε / 2, ε, by linarith, by linarith⟩
  set φ : ℝ → ℝ := B.normed volume with hφdef
  have hBs : tsupport φ ⊆ Icc (-ε) ε := by
    rw [hφdef, B.tsupport_normed_eq]
    intro u hu
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, show B.rOut = ε from rfl] at hu
    exact abs_le.mp hu
  have hφc : Continuous φ := B.continuous_normed
  have hφs : HasCompactSupport φ := B.hasCompactSupport_normed
  have hφ0 : ∀ u, 0 ≤ φ u := B.nonneg_normed
  have hφ1 : ∫ u, φ u = 1 := B.integral_normed
  have hφneg : ∀ u, φ (-u) = φ u := B.normed_neg
  refine ⟨fun u => (φ u : ℂ), Complex.ofRealCLM.contDiff.comp B.contDiff_normed,
    (tsupport_comp_subset (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero _).trans hBs,
    fun y => ?_⟩
  have hint : ∀ g : ℝ → ℝ, Continuous g → Integrable fun u => φ u * g u := fun g hg =>
    (hφc.mul hg).integrable_of_hasCompactSupport hφs.mul_right
  have hFT : paperFT (fun u => (φ u : ℂ)) ((y : ℂ) * I) =
      ((∫ u, φ u * Real.exp (-(y * u)) : ℝ) : ℂ) := by
    rw [paperFT_def, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have e : I * ((y : ℂ) * I) * (u : ℂ) = ((-(y * u) : ℝ) : ℂ) := by
      push_cast
      linear_combination (y : ℂ) * (u : ℂ) * Complex.I_sq
    simp only
    rw [e, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  have hodd : ∫ u, φ u * u = 0 := by
    have h := integral_neg_eq_self (fun u => φ u * u) volume
    simp only [hφneg, mul_neg, integral_neg] at h
    linarith
  have hlow : 1 ≤ ∫ u, φ u * Real.exp (-(y * u)) := by
    have hi1 : Integrable φ := hφc.integrable_of_hasCompactSupport hφs
    have hi2 : Integrable fun u => φ u * u := hint (fun u => u) continuous_id
    have hi3 : Integrable fun u => φ u * Real.exp (-(y * u)) :=
      hint (fun u => Real.exp (-(y * u))) (by fun_prop)
    have hmono : ∫ u, (φ u - y * (φ u * u)) ≤ ∫ u, φ u * Real.exp (-(y * u)) :=
      integral_mono (hi1.sub (hi2.const_mul y)) hi3 fun u => by
        have := Real.add_one_le_exp (-(y * u))
        have h0 := hφ0 u
        show φ u - y * (φ u * u) ≤ φ u * Real.exp (-(y * u))
        nlinarith
    rw [integral_sub hi1 (hi2.const_mul y), integral_const_mul, hodd, hφ1] at hmono
    linarith
  rw [hFT, Complex.norm_real, Real.norm_eq_abs]
  exact hlow.trans (le_abs_self _)

/-! ### The infinite product on the strip -/

/-- **The infinite product at an isolated point.** -/
theorem norm_tprod_pertFactor_ge_strip {h θ L η : ℝ} (hh : 0 < h) (hθ : |θ| ≤ 1) {ν : ℤ → ℂ}
    (hL : ∀ k, ‖ν k - latPt h θ k‖ ≤ L) (him : ∀ k, |(ν k).im| ≤ 1 / 2) {z : ℂ}
    (hzim : |z.im| ≤ 1 / 2) (hzlat : ∀ k, h / 4 ≤ |z.re - latPt h θ k|) (hη : 0 < η)
    (hzν : ∀ k, η ≤ ‖z - ν k‖) :
    isoConst L η * Real.exp (-(isoRate L η * nearFarConst h L)) *
        (1 + |z.re|) ^ (-(isoRate L η * (4 * (1 + L) / h))) ≤
      ‖∏' k, pertFactor h θ ν k z‖ := by
  have hz : ∀ k, z ≠ latPt h θ k := fun k e => by
    have := hzlat k
    rw [e, Complex.ofReal_re, sub_self, abs_zero] at this
    linarith
  have hlim : Tendsto (fun S : Finset ℤ => ‖∏ k ∈ S, pertFactor h θ ν k z‖) atTop
      (𝓝 ‖∏' k, pertFactor h θ ν k z‖) :=
    Filter.Tendsto.norm (multipliable_pertFactor hh hθ hL him hz).hasProd
  exact ge_of_tendsto hlim (Eventually.of_forall fun S =>
    norm_prod_pertFactor_ge_strip hh hθ hL him S hzim hzlat hη hzν)

/-- **The infinite product on the strip.** -/
theorem norm_sin_mul_tprod_pertFactor_le_strip {h θ L : ℝ} (hh : 0 < h) (hθ : |θ| ≤ 1)
    {ν : ℤ → ℂ} (hL : ∀ k, ‖ν k - latPt h θ k‖ ≤ L) (him : ∀ k, |(ν k).im| ≤ 1 / 2) {z : ℂ}
    (hzim : |z.im| ≤ 1 / 2) (hz : ∀ k, z ≠ latPt h θ k) :
    ‖Complex.sin (((π / h : ℝ) : ℂ) * (z - ((θ * h : ℝ) : ℂ))) * ∏' k, pertFactor h θ ν k z‖ ≤
      nearestConstStrip h L * Real.exp (3 * L * nearFarConst h L) *
        (1 + |z.re|) ^ (3 * L * (4 * (1 + L) / h)) := by
  have hlim : Tendsto (fun S : Finset ℤ => ‖Complex.sin (((π / h : ℝ) : ℂ) *
      (z - ((θ * h : ℝ) : ℂ))) * ∏ k ∈ S, pertFactor h θ ν k z‖) atTop
      (𝓝 ‖Complex.sin (((π / h : ℝ) : ℂ) * (z - ((θ * h : ℝ) : ℂ))) *
        ∏' k, pertFactor h θ ν k z‖) :=
    Filter.Tendsto.norm (((multipliable_pertFactor hh hθ hL him hz).hasProd).const_mul _)
  exact le_of_tendsto hlim (Eventually.of_forall fun S =>
    norm_sin_mul_prod_pertFactor_le_strip hh hθ hL him S hzim hz)

/-! ### Uniform isolating windows -/

theorem one_fourth_le_abs_int_add {θ : ℝ} (hθ0 : 1 / 4 < θ) (hθ1 : θ < 3 / 4) (j : ℤ) :
    1 / 4 ≤ |(j : ℝ) + θ| := by
  rcases le_or_gt 0 j with h | h
  · have : (0 : ℝ) ≤ j := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith
  · have : (j : ℝ) ≤ -1 := by exact_mod_cast (by omega : j ≤ -1)
    rw [abs_of_neg (by linarith)]; linarith

theorem half_le_abs_int_add_half (j : ℤ) : 1 / 2 ≤ |(j : ℝ) + 1 / 2| := by
  rcases le_or_gt 0 j with h | h
  · have : (0 : ℝ) ≤ j := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith
  · have : (j : ℝ) ≤ -1 := by exact_mod_cast (by omega : j ≤ -1)
    rw [abs_of_neg (by linarith)]; linarith

theorem half_le_norm_sin_shift {H θ : ℝ} (hH : 0 < H) (hθ0 : 1 / 4 < θ) (hθ1 : θ < 3 / 4)
    {w : ℂ} (hw : w.re = 0) :
    1 / 2 ≤ ‖Complex.sin (((π / H : ℝ) : ℂ) * (w - ((θ * H : ℝ) : ℂ)))‖ := by
  refine le_trans ?_ (HTGeometry.abs_sin_re_le_norm_sin _)
  have hre : (((π / H : ℝ) : ℂ) * (w - ((θ * H : ℝ) : ℂ))).re = -(π * θ) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.sub_im, hw, zero_mul, sub_zero]
    field_simp
    ring
  rw [hre, Real.sin_neg, abs_neg]
  have hd : 1 / 4 ≤ HTGeometry.distToInt θ := by
    unfold HTGeometry.distToInt
    rcases le_or_gt (round θ) 0 with h | h
    · have : ((round θ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
    · have : (1 : ℝ) ≤ ((round θ : ℤ) : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ round θ)
      rw [abs_of_neg (by linarith)]; linarith
  have := HTGeometry.two_mul_distToInt_le_abs_sin θ
  linarith

/-- The slack `L + 2H` of the lattice filled at the unmatched sites. -/
def windowSlack (H L : ℝ) : ℝ := L + 2 * H

/-- The growth exponent of the isolating product on the strip. -/
def windowExponent (H L : ℝ) : ℝ := 3 * windowSlack H L * (4 * (1 + windowSlack H L) / H)

/-- The growth constant of the isolating product on the strip. -/
def windowGrowth (H L : ℝ) : ℝ :=
  nearestConstStrip H (windowSlack H L) *
    Real.exp (3 * windowSlack H L * nearFarConst H (windowSlack H L))

/-- The floor of the isolating window at the target. -/
def windowFloor (H L η : ℝ) : ℝ :=
  1 / 2 * (isoConst (windowSlack H L) (min η (H / 2)) *
    Real.exp (-(isoRate (windowSlack H L) (min η (H / 2)) * nearFarConst H (windowSlack H L))))

theorem windowGrowth_nonneg {H L : ℝ} (hH : 0 < H) (hL : 0 ≤ L) : 0 ≤ windowGrowth H L := by
  have hS : 0 ≤ windowSlack H L := by rw [windowSlack]; linarith
  rw [windowGrowth, nearestConstStrip]
  refine mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (by linarith)) (by linarith)) zero_le_one) (Real.exp_pos _).le) (Real.exp_pos _).le

theorem windowFloor_pos {H L η : ℝ} (hH : 0 < H) (hL : 0 ≤ L) (hη : 0 < η) :
    0 < windowFloor H L η := by
  have hS : 0 ≤ windowSlack H L := by rw [windowSlack]; linarith
  rw [windowFloor]
  exact mul_pos (by norm_num) (mul_pos (isoConst_pos hS (lt_min hη (by linarith)))
    (Real.exp_pos _))

/-- **The isolating window and its structure.** The window of `isolating_window_of_bump`, with
the data of its construction: a lattice shift `θ ∈ (1/4, 3/4)`, the filled lattice `ν` (the points
`λ_i` at the matched sites, half-shifted lattice points elsewhere), and the transform
`F̂ = sin((π/H)(w − θH)) · b̂ · Π_k r_k · b̂` off the lattice. -/
theorem isolating_window_core {H L r η ε : ℝ} (hH : 0 < H) (hL : 0 ≤ L)
    (hε : 0 < ε) (hεr : π / H + 2 * ε ≤ r) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbs : tsupport b ⊆ Icc (-ε) ε)
    {ι : Type} (lam : ι → ℂ) (τ : ι → ℤ) (P : Set ι) (hτ : Set.InjOn τ P)
    (hPL : ∀ i ∈ P, ‖lam i - τ i * H‖ ≤ L) (hPim : ∀ i ∈ P, |(lam i).im| ≤ 1 / 2) {w₀ : ℂ}
    (hw₀re : w₀.re = 0) (hw₀P : ∀ i ∈ P, η ≤ ‖w₀ - lam i‖) :
    ∃ (θ : ℝ) (ν : ℤ → ℂ) (F : ℝ → ℂ), 1 / 4 < θ ∧ θ < 3 / 4 ∧
      (∀ j, ‖ν j - latPt H θ j‖ ≤ windowSlack H L) ∧ (∀ j, |(ν j).im| ≤ 1 / 2) ∧
      (∀ j, min η (H / 2) ≤ ‖w₀ - ν j‖) ∧
      ContDiff ℝ (⊤ : ℕ∞) F ∧ tsupport F ⊆ Icc (-r) r ∧ (∀ i ∈ P, paperFT F (lam i) = 0) ∧
      ∀ w : ℂ, (∀ j, w ≠ latPt H θ j) → paperFT F w =
        Complex.sin (((π / H : ℝ) : ℂ) * (w - ((θ * H : ℝ) : ℂ))) * paperFT b w *
          (∏' j, pertFactor H θ ν j w) * paperFT b w := by
  classical
  have hbc : HasCompactSupport b := isCompact_Icc.of_isClosed_subset (isClosed_tsupport b) hbs
  obtain ⟨L', hL'⟩ : ∃ L', L' = windowSlack H L := ⟨_, rfl⟩
  obtain ⟨η', hη'⟩ : ∃ η', η' = min η (H / 2) := ⟨_, rfl⟩
  -- fill the unmatched sites at the half-shifted lattice
  set ν : ℤ → ℂ := fun j => if hj : ∃ i ∈ P, τ i = j then lam hj.choose
    else (((j : ℝ) * H + H / 2 : ℝ) : ℂ) with hν
  have hνin : ∀ j (hj : ∃ i ∈ P, τ i = j), ν j = lam hj.choose := fun j hj => by
    simp only [hν, dif_pos hj]
  have hνout : ∀ j, (¬ ∃ i ∈ P, τ i = j) → ν j = (((j : ℝ) * H + H / 2 : ℝ) : ℂ) :=
    fun j hj => by simp only [hν, dif_neg hj]
  have hντ : ∀ i ∈ P, ν (τ i) = lam i := fun i hi => by
    have hj : ∃ v ∈ P, τ v = τ i := ⟨i, hi, rfl⟩
    rw [hνin _ hj, hτ hj.choose_spec.1 hi hj.choose_spec.2]
  have hνim : ∀ j, |(ν j).im| ≤ 1 / 2 := by
    intro j
    by_cases hj : ∃ i ∈ P, τ i = j
    · rw [hνin j hj]; exact hPim _ hj.choose_spec.1
    · rw [hνout j hj, Complex.ofReal_im, abs_zero]; norm_num
  have hνw₀ : ∀ j, η' ≤ ‖w₀ - ν j‖ := by
    intro j
    by_cases hj : ∃ i ∈ P, τ i = j
    · rw [hνin j hj, hη']
      exact (min_le_left _ _).trans (hw₀P _ hj.choose_spec.1)
    · rw [hνout j hj, hη']
      refine (min_le_right _ _).trans ((le_trans ?_ (Complex.abs_re_le_norm _)))
      rw [Complex.sub_re, hw₀re, Complex.ofReal_re, zero_sub, abs_neg,
        show (j : ℝ) * H + H / 2 = ((j : ℝ) + 1 / 2) * H by ring, abs_mul, abs_of_pos hH]
      nlinarith [half_le_abs_int_add_half j]
  -- a lattice shift in `(1/4, 3/4)` avoiding all coincidences
  obtain ⟨t, ⟨ht0, ht1⟩, htE⟩ := SquareRootThreshold.exists_mem_Ioo_notMem_of_countable
    (by norm_num : (0 : ℝ) < 1 / 2)
    (Set.countable_range fun q : ℤ × ℤ => (ν q.1).re / H - q.2 - 1 / 4)
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = t + 1 / 4 := ⟨_, rfl⟩
  have hθ0 : 1 / 4 < θ := by rw [hθdef]; linarith
  have hθ1 : θ < 3 / 4 := by rw [hθdef]; linarith
  have hθ : |θ| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hνlat : ∀ j m, ν j ≠ latPt H θ m := by
    intro j m e
    apply htE
    refine ⟨(j, m), ?_⟩
    simp only [e, Complex.ofReal_re, latPt]
    field_simp
    linarith
  have hlat : ∀ j : ℤ, ((latPt H θ j : ℝ) : ℂ) = (j : ℂ) * (H : ℂ) + ((θ * H : ℝ) : ℂ) :=
    fun j => by rw [latPt]; push_cast; ring
  have hνb : ∀ j, ‖ν j - latPt H θ j‖ ≤ L' := by
    intro j
    by_cases hj : ∃ i ∈ P, τ i = j
    · obtain ⟨v, hvP, hvl, hv⟩ : ∃ v ∈ P, hj.choose = v ∧ τ v = j :=
        ⟨_, hj.choose_spec.1, rfl, hj.choose_spec.2⟩
      rw [hνin j hj, hvl, hlat, ← hv,
        show lam v - ((τ v : ℂ) * H + ((θ * H : ℝ) : ℂ)) =
          (lam v - (τ v : ℂ) * H) - ((θ * H : ℝ) : ℂ) by ring]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by linarith) hH), hL',
        windowSlack]
      have := hPL v hvP
      nlinarith
    · rw [hνout j hj, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show (j : ℝ) * H + H / 2 - latPt H θ j = H * (1 / 2 - θ) by rw [latPt]; ring, abs_mul,
        abs_of_pos hH, hL', windowSlack]
      have : |1 / 2 - θ| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith
  -- the sine window and the limit window
  have hbw : ApertureWindow ε b := ⟨hb.of_le (by norm_cast), hbs⟩
  obtain ⟨hf₀w, hf₀t⟩ := sineShift_props (τ := θ * H) (by positivity : (0 : ℝ) ≤ π / H) hbw
  have hf₀ : ContDiff ℝ (⊤ : ℕ∞) (sineShift (π / H) (θ * H) b) := contDiff_sineShift _ _ hb
  obtain ⟨f, hfc, hfs, hfν, hfz⟩ := exists_blind_limit_window hH hθ (by positivity) hνb hνim hb
    hbc hf₀ hf₀w.2 hf₀t hνlat
  -- smoothing by the same bump
  have hfcs : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  set F := convolution f b (ContinuousLinearMap.mul ℝ ℂ) volume with hF
  have hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F :=
    hbc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hfc.locallyIntegrable hb
  have hFs : tsupport F ⊆ Icc (-r) r := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    by_contra hout
    apply hu
    refine convolution_eq_zero_of_lt hfs hbs ?_
    by_contra hle
    push Not at hle
    apply hout
    have := abs_le.mp hle
    constructor <;> linarith
  have hFcs : HasCompactSupport F := isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hFs
  have hFt : ∀ z, paperFT F z = paperFT f z * paperFT b z := fun z =>
    _root_.RHTower.WeilHerglotz.paperFT_convolution (hfc.integrable_of_hasCompactSupport hfcs)
      (hb.continuous.integrable_of_hasCompactSupport hbc) hfcs hbc z
  refine ⟨θ, ν, F, hθ0, hθ1, fun j => hL' ▸ hνb j, hνim, fun j => hη' ▸ hνw₀ j, hFsmooth, hFs,
    fun i hi => by rw [hFt, ← hντ i hi, hfν (τ i), zero_mul], fun w hw => ?_⟩
  rw [hFt, hfz w hw, hf₀t]

/-- **Floor and decay of the core window.** A window whose transform is
`sin((π/H)(w − θH)) · b̂ · Π_k r_k · b̂` off the lattice, with `θ ∈ (1/4, 3/4)` and `ν` within
`windowSlack H L` of the lattice and `min η (H/2)`-far from `w₀`, has `|F̂(w₀)| ≥ windowFloor H L η`
and `|F̂(w)| (1 + |Re w|)^k ≤ windowGrowth H L · C_m C_0 e^{ε}` on the strip. -/
theorem core_window_floor_decay {H L η ε : ℝ} (hH : 0 < H) (hL : 0 ≤ L) (hη : 0 < η)
    (hε : 0 < ε) {b : ℝ → ℂ} (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖) {k m : ℕ}
    (hm : windowExponent H L + k ≤ m) {Cm C0 : ℝ}
    (hCm : ∀ w : ℂ, (1 + ‖w‖) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|))
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|)) {w₀ : ℂ}
    (hw₀re : w₀.re = 0) (hw₀im : |w₀.im| ≤ 1 / 2) {θ : ℝ} (hθ0 : 1 / 4 < θ) (hθ1 : θ < 3 / 4)
    {ν : ℤ → ℂ} (hνb : ∀ j, ‖ν j - latPt H θ j‖ ≤ windowSlack H L)
    (hνim : ∀ j, |(ν j).im| ≤ 1 / 2) (hνw₀ : ∀ j, min η (H / 2) ≤ ‖w₀ - ν j‖) {F : ℝ → ℂ}
    (hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F) (hFcs : HasCompactSupport F)
    (hformula : ∀ w : ℂ, (∀ j, w ≠ latPt H θ j) → paperFT F w =
        Complex.sin (((π / H : ℝ) : ℂ) * (w - ((θ * H : ℝ) : ℂ))) * paperFT b w *
          (∏' j, pertFactor H θ ν j w) * paperFT b w) :
    windowFloor H L η ≤ ‖paperFT F w₀‖ ∧ ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT F w‖ * (1 + |w.re|) ^ k ≤ windowGrowth H L * Cm * C0 * Real.exp ε := by
  have hCm0 : 0 ≤ Cm := by
    have h1 := hCm 0
    rw [Complex.zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h1
    exact le_trans (by positivity) h1
  have hC00 : 0 ≤ C0 := by
    have h1 := hC0 0
    rw [Complex.zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h1
    exact le_trans (norm_nonneg _) h1
  obtain ⟨L', hL'⟩ : ∃ L', L' = windowSlack H L := ⟨_, rfl⟩
  have hL'0 : 0 ≤ L' := by rw [hL', windowSlack]; linarith
  obtain ⟨η', hη'⟩ : ∃ η', η' = min η (H / 2) := ⟨_, rfl⟩
  have hη'0 : 0 < η' := by rw [hη']; exact lt_min hη (by linarith)
  obtain ⟨K, hK⟩ : ∃ K, K = windowGrowth H L := ⟨_, rfl⟩
  have hK' : K = nearestConstStrip H L' * Real.exp (3 * L' * nearFarConst H L') := by
    rw [hK, windowGrowth, hL']
  have hK0 : 0 ≤ K := hK ▸ windowGrowth_nonneg hH hL
  obtain ⟨p, hp⟩ : ∃ p, p = windowExponent H L := ⟨_, rfl⟩
  have hp' : p = 3 * L' * (4 * (1 + L') / H) := by rw [hp, windowExponent, hL']
  rw [← hp] at hm
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = isoConst L' η' * Real.exp (-(isoRate L' η' * nearFarConst H L')) :=
    ⟨_, rfl⟩
  have hφ0 : 0 < φ := by rw [hφ]; exact mul_pos (isoConst_pos hL'0 hη'0) (Real.exp_pos _)
  have hfl : windowFloor H L η = 1 / 2 * φ := by rw [windowFloor, hφ, hL', hη']
  rw [hfl, ← hK]
  rw [← hL'] at hνb
  rw [← hη'] at hνw₀
  have hθ : |θ| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  refine ⟨?_, ?_⟩
  · -- the floor at the target
    have hw₀lat : ∀ j, w₀ ≠ latPt H θ j := fun j e => by
      have h1 := congrArg Complex.re e
      rw [hw₀re, Complex.ofReal_re, latPt] at h1
      have h2 : (j : ℝ) + θ = 0 :=
        (mul_eq_zero.mp h1.symm).resolve_right hH.ne'
      have h3 : j < 0 := by exact_mod_cast (show (j : ℝ) < 0 by linarith)
      have h4 : -1 < j := by exact_mod_cast (show (-1 : ℝ) < j by linarith)
      omega
    have hzlat : ∀ j : ℤ, H / 4 ≤ |w₀.re - latPt H θ j| := by
      intro j
      rw [hw₀re, zero_sub, abs_neg, latPt, abs_mul, abs_of_pos hH]
      nlinarith [one_fourth_le_abs_int_add hθ0 hθ1 j]
    have hfloor := norm_tprod_pertFactor_ge_strip hH hθ hνb hνim hw₀im hzlat hη'0 hνw₀
    rw [hw₀re, abs_zero, add_zero, Real.one_rpow, mul_one, ← hφ] at hfloor
    have hbw₀ : 1 ≤ ‖paperFT b w₀‖ := by
      have hw₀ : ((w₀.im : ℝ) : ℂ) * I = w₀ := by
        apply Complex.ext <;> simp [hw₀re]
      have := hb1 w₀.im
      rwa [hw₀] at this
    have hsin := half_le_norm_sin_shift hH hθ0 hθ1 hw₀re
    rw [hformula w₀ hw₀lat, norm_mul, norm_mul, norm_mul]
    calc 1 / 2 * φ = 1 / 2 * 1 * φ * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul (mul_le_mul hsin hbw₀ zero_le_one (by positivity)) hfloor
          hφ0.le (by positivity)) hbw₀ zero_le_one (by positivity)
  · -- the decay on the strip
    have hoff : ∀ w : ℂ, |w.im| ≤ 1 / 2 → (∀ j, w ≠ latPt H θ j) →
        ‖paperFT F w‖ * (1 + |w.re|) ^ k ≤ K * Cm * C0 * Real.exp ε := by
      intro w hw hwl
      have hsp := norm_sin_mul_tprod_pertFactor_le_strip hH hθ hνb hνim hw hwl
      rw [← hK', ← hp'] at hsp
      have h1 : (1 : ℝ) ≤ 1 + |w.re| := by linarith [abs_nonneg w.re]
      have hpn : (1 + |w.re|) ^ p * (1 + |w.re|) ^ k ≤ (1 + |w.re|) ^ m := by
        rw [← Real.rpow_natCast (1 + |w.re|) k, ← Real.rpow_add (by linarith),
          ← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le h1 hm
      have hre : (1 + |w.re|) ^ m ≤ (1 + ‖w‖) ^ m :=
        pow_le_pow_left₀ (by positivity) (by linarith [Complex.abs_re_le_norm w]) _
      have hexp : Real.exp (ε * |w.im|) * Real.exp (ε * |w.im|) ≤ Real.exp ε := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg w.im])
      have hB : (1 + |w.re|) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|) :=
        (mul_le_mul_of_nonneg_right hre (norm_nonneg _)).trans (hCm w)
      rw [hformula w hwl]
      calc ‖Complex.sin (((π / H : ℝ) : ℂ) * (w - ((θ * H : ℝ) : ℂ))) * paperFT b w *
            (∏' j, pertFactor H θ ν j w) * paperFT b w‖ * (1 + |w.re|) ^ k
          = ‖Complex.sin (((π / H : ℝ) : ℂ) * (w - ((θ * H : ℝ) : ℂ))) *
              ∏' j, pertFactor H θ ν j w‖ * ((1 + |w.re|) ^ k * ‖paperFT b w‖) *
                ‖paperFT b w‖ := by
            rw [norm_mul, norm_mul, norm_mul, norm_mul]; ring
        _ ≤ K * (1 + |w.re|) ^ p * ((1 + |w.re|) ^ k * ‖paperFT b w‖) * ‖paperFT b w‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsp (by positivity))
              (norm_nonneg _)
        _ = K * ((1 + |w.re|) ^ p * (1 + |w.re|) ^ k) * ‖paperFT b w‖ * ‖paperFT b w‖ := by
            ring
        _ ≤ K * (1 + |w.re|) ^ m * ‖paperFT b w‖ * ‖paperFT b w‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpn hK0) (norm_nonneg _)) (norm_nonneg _)
        _ = K * ((1 + |w.re|) ^ m * ‖paperFT b w‖) * ‖paperFT b w‖ := by ring
        _ ≤ K * (Cm * Real.exp (ε * |w.im|)) * (C0 * Real.exp (ε * |w.im|)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hB hK0) (hC0 w) (norm_nonneg _)
              (mul_nonneg hK0 (mul_nonneg hCm0 (Real.exp_pos _).le))
        _ = K * Cm * C0 * (Real.exp (ε * |w.im|) * Real.exp (ε * |w.im|)) := by ring
        _ ≤ K * Cm * C0 * Real.exp ε :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg (mul_nonneg hK0 hCm0) hC00)
    -- the lattice points by continuity
    have hΦ : Continuous fun w : ℂ => ‖paperFT F w‖ * (1 + |w.re|) ^ k :=
      ((_root_.RHTower.EvenSector.differentiable_paperFT_of_compact hFsmooth.continuous
        hFcs).continuous.norm).mul ((continuous_const.add Complex.continuous_re.abs).pow k)
    intro w hw
    by_cases hwl : ∀ j, w ≠ latPt H θ j
    · exact hoff w hw hwl
    · push Not at hwl
      obtain ⟨j, hj⟩ := hwl
      have hwim : w.im = 0 := by rw [hj, Complex.ofReal_im]
      have ht : Tendsto (fun s : ℝ => w + (s : ℂ) * I) (𝓝[>] 0) (𝓝 w) := by
        have h0 : Tendsto (fun s : ℝ => w + (s : ℂ) * I) (𝓝 0) (𝓝 (w + ((0 : ℝ) : ℂ) * I)) :=
          ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0)
        rw [Complex.ofReal_zero, zero_mul, add_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      refine le_of_tendsto ((hΦ.tendsto w).comp ht) ?_
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
      obtain ⟨hs0, hs1⟩ := hs
      have him' : (w + (s : ℂ) * I).im = s := by simp [hwim]
      refine hoff _ (by rw [him', abs_of_pos hs0]; linarith) fun j' e => ?_
      have := congrArg Complex.im e
      rw [him', Complex.ofReal_im] at this
      linarith


/-- **Isolating windows from a bump.** Let `b` be a smooth bump on `[−ε, ε]` with `|b̂(iy)| ≥ 1`
and decay `(1 + |w|)^m |b̂(w)| ≤ C_m e^{ε|Im w|}`, `|b̂(w)| ≤ C_0 e^{ε|Im w|}`, where
`m ≥ windowExponent H L + k`. Let `λ_i`, `i ∈ P`, of depth `≤ 1/2` be matched injectively to
`τ_i H` at distance `≤ L`, and `w₀ ∈ i[−½, ½]` at distance `≥ η` from them. Then some window of
aperture `π/H + 2ε` is blind to `P`, has `|f̂(w₀)| ≥ windowFloor H L η`, and has
`|f̂(w)| (1 + |Re w|)^k ≤ windowGrowth H L · C_m C_0 e^{ε}` on the strip `|Im w| ≤ 1/2`. -/
theorem isolating_window_of_bump {H L r η ε : ℝ} (hH : 0 < H) (hL : 0 ≤ L) (hη : 0 < η)
    (hε : 0 < ε) (hεr : π / H + 2 * ε ≤ r) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbs : tsupport b ⊆ Icc (-ε) ε) (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖) {k m : ℕ}
    (hm : windowExponent H L + k ≤ m) {Cm C0 : ℝ}
    (hCm : ∀ w : ℂ, (1 + ‖w‖) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|))
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|))
    {ι : Type} (lam : ι → ℂ) (τ : ι → ℤ) (P : Set ι) (hτ : Set.InjOn τ P)
    (hPL : ∀ i ∈ P, ‖lam i - τ i * H‖ ≤ L) (hPim : ∀ i ∈ P, |(lam i).im| ≤ 1 / 2) {w₀ : ℂ}
    (hw₀re : w₀.re = 0) (hw₀im : |w₀.im| ≤ 1 / 2) (hw₀P : ∀ i ∈ P, η ≤ ‖w₀ - lam i‖) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ ApertureWindow r f ∧ (∀ i ∈ P, paperFT f (lam i) = 0) ∧
      windowFloor H L η ≤ ‖paperFT f w₀‖ ∧
      ∀ w : ℂ, |w.im| ≤ 1 / 2 →
        ‖paperFT f w‖ * (1 + |w.re|) ^ k ≤ windowGrowth H L * Cm * C0 * Real.exp ε := by
  obtain ⟨θ, ν, F, hθ0, hθ1, hνb, hνim, hνw₀, hFsmooth, hFs, hblind, hformula⟩ :=
    isolating_window_core (η := η) hH hL hε hεr hb hbs lam τ P hτ hPL hPim hw₀re hw₀P
  exact ⟨F, hFsmooth, ⟨hFsmooth.of_le (by norm_cast), hFs⟩, hblind,
    core_window_floor_decay hH hL hη hε hb1 hm hCm hC0 hw₀re hw₀im hθ0 hθ1 hνb hνim hνw₀
      hFsmooth (isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hFs) hformula⟩

/-- **Uniform isolating windows.** For a spacing `H`, an aperture `r > π/H`, a matching distance
`L`, an isolation radius `η` and a decay order `k` there are `c > 0` and `M` such that: every family
`λ_i`, `i ∈ P`, of depth `≤ 1/2` matched injectively to `τ_i H` at distance `≤ L`, and every
`w₀ ∈ i[−½, ½]` at distance `≥ η` from it, admit a window of aperture `r` blind to `P` with
`|f̂(w₀)| ≥ c` and `|f̂(w)| (1 + |Re w|)^k ≤ M` on the strip `|Im w| ≤ 1/2`. -/
theorem exists_uniform_isolating_window {H L r η : ℝ} (hH : 0 < H) (hr : π / H < r)
    (hL : 0 ≤ L) (hη : 0 < η) (k : ℕ) :
    ∃ c M : ℝ, 0 < c ∧ 0 ≤ M ∧ ∀ {ι : Type} (lam : ι → ℂ) (τ : ι → ℤ) (P : Set ι),
      Set.InjOn τ P → (∀ i ∈ P, ‖lam i - τ i * H‖ ≤ L) → (∀ i ∈ P, |(lam i).im| ≤ 1 / 2) →
      ∀ w₀ : ℂ, w₀.re = 0 → |w₀.im| ≤ 1 / 2 → (∀ i ∈ P, η ≤ ‖w₀ - lam i‖) →
      ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ i ∈ P, paperFT f (lam i) = 0) ∧
        c ≤ ‖paperFT f w₀‖ ∧
        ∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖paperFT f w‖ * (1 + |w.re|) ^ k ≤ M := by
  obtain ⟨ε, hε⟩ : ∃ ε, ε = (r - π / H) / 3 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨b, hb, hbs, hb1⟩ := exists_bump_one_le_norm_paperFT_I_mul hε0
  obtain ⟨Cm, hCm0, hCm⟩ :=
    exists_pow_mul_norm_paperFT_le_exp hb hε0.le hbs (⌈windowExponent H L⌉₊ + k)
  obtain ⟨C0, hC00, hC0⟩ := exists_pow_mul_norm_paperFT_le_exp hb hε0.le hbs 0
  have hC0' : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|) := fun w => by
    have := hC0 w
    rwa [pow_zero, one_mul] at this
  have hm : windowExponent H L + k ≤ ((⌈windowExponent H L⌉₊ + k : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil (windowExponent H L)]
  refine ⟨windowFloor H L η, windowGrowth H L * Cm * C0 * Real.exp ε, windowFloor_pos hH hL hη,
    mul_nonneg (mul_nonneg (mul_nonneg (windowGrowth_nonneg hH hL) hCm0) hC00)
      (Real.exp_pos _).le, ?_⟩
  intro ι lam τ P hτ hPL hPim w₀ hw₀re hw₀im hw₀P
  obtain ⟨f, -, hf⟩ := isolating_window_of_bump (r := r) hH hL hη hε0 (by rw [hε]; linarith) hb
    hbs hb1 hm hCm hC0' lam τ P hτ hPL hPim hw₀re hw₀im hw₀P
  exact ⟨f, hf⟩

/-! ### The local camera -/

theorem apertureWindow_localWindow {r : ℝ} {b : ℝ → ℂ} (hb : ApertureWindow r b) (X : ℝ) :
    ApertureWindow r (localWindow X b) :=
  ⟨hb.1.mul (contDiff_const.mul Complex.ofRealCLM.contDiff).neg.cexp,
    tsupport_mul_subset_left.trans hb.2⟩

theorem norm_gammaOf_sub (z w : ℂ) : ‖gammaOf z - gammaOf w‖ = ‖z - w‖ := by
  simp only [gammaOf]
  rw [← sub_div, norm_div, Complex.norm_I, div_one]
  congr 1
  ring

theorem one_le_norm_multDiff {Z Z' : ZeroConfig} {z : ℂ} (hz : multDiff Z Z' z ≠ 0) :
    1 ≤ ‖multDiff Z Z' z‖ := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℤ, multDiff Z Z' z = m := by
    refine ⟨(if z ∈ Z.carrier then (Z.mult z : ℤ) else 0) -
      (if z ∈ Z'.carrier then (Z'.mult z : ℤ) else 0), ?_⟩
    simp only [multDiff, Set.indicator_apply]
    split_ifs <;> push_cast <;> ring
  rw [hm] at hz ⊢
  have hm0 : m ≠ 0 := fun e => hz (by rw [e, Int.cast_zero])
  rw [Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hm0

/-- The matching distance `(|C₀| + 1)/(2D) + 1/D + 1/2` of a cluster of count `(D, C₀)` in the
half lattice `2D⁻¹ℤ`. -/
def localSlack (D C₀ : ℝ) : ℝ := (|C₀| + 1) / 2 * D⁻¹ + D⁻¹ + 1 / 2

/-- The constant of the local camera: `M² e^a (5/4)/c²`, with `M` the strip decay and `c` the floor
of the isolating windows built from a bump of decay constants `C_m, C_0` and aperture `ε`. -/
def localCameraConst (a D C₀ η ε Cm C0 : ℝ) : ℝ :=
  (windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) ^ 2 * Real.exp a *
    (5 / 4) / windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2

/-- **Local window pairs from any window producer.** Let `Φ` be a property of a window and
a target. Suppose every family `λ_i`, `i ∈ P`, of depth `≤ 1/2`, matched injectively into
`(2/D)ℤ` at distance `≤ localSlack D C₀`, and every target `w₀ ∈ i[−½, ½]` at distance `≥ η`
from it, admit a window blind to `P` with property `Φ` at `w₀`. Then for a cluster near the
height `X` of `z₀` with count bound `(D, C₀)`, and every cluster point outside an excluded set
`Q` at distance `≥ η` from `z₀`, there are windows `F₁, G₁` with property `Φ` at the targets
`γ_{z₀} − X` and `conj γ_{z₀} − X`, such that at every such point `F̂₁(γ_z − X) = 0` or
`Ĝ₁(conj γ_z − X) = 0`. -/
theorem exists_local_pair_of_windows {D C₀ η : ℝ} (hD : 0 < D) (Φ : (ℝ → ℂ) → ℂ → Prop)
    (hwin : ∀ {ι : Type} (lam : ι → ℂ) (τ : ι → ℤ) (P : Set ι),
      Set.InjOn τ P → (∀ i ∈ P, ‖lam i - τ i * ((2 * D⁻¹ : ℝ) : ℂ)‖ ≤ localSlack D C₀) →
      (∀ i ∈ P, |(lam i).im| ≤ 1 / 2) →
      ∀ w₀ : ℂ, w₀.re = 0 → |w₀.im| ≤ 1 / 2 → (∀ i ∈ P, η ≤ ‖w₀ - lam i‖) →
      ∃ f : ℝ → ℂ, (∀ i ∈ P, paperFT f (lam i) = 0) ∧ Φ f w₀)
    (Z Z' : ZeroConfig) {z₀ : ℂ} (hz₀ : |z₀.re - 1 / 2| ≤ 1 / 2) {R : ℝ} (Q : ℂ → Prop)
    (hQ : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → ¬ Q z → η ≤ ‖z - z₀‖)
    (hcount : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ R ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀) :
    ∃ F₁ G₁ : ℝ → ℂ,
      (∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → ¬ Q z →
        paperFT F₁ (gammaOf z - z₀.im) = 0 ∨ paperFT G₁ (conj (gammaOf z) - z₀.im) = 0) ∧
      Φ F₁ (gammaOf z₀ - z₀.im) ∧ Φ G₁ (conj (gammaOf z₀) - z₀.im) := by
  classical
  obtain ⟨h, hh_def⟩ : ∃ h, h = D⁻¹ := ⟨_, rfl⟩
  have hh : 0 < h := by rw [hh_def]; exact inv_pos.mpr hD
  have hDh : D * h = 1 := by rw [hh_def]; field_simp
  obtain ⟨L, hLs⟩ : ∃ L, L = localSlack D C₀ := ⟨_, rfl⟩
  have hL : L = (|C₀| + 1) / 2 * h + h + 1 / 2 := by rw [hLs, localSlack, hh_def]
  rw [← hh_def, ← hLs] at hwin
  obtain ⟨X, hX⟩ : ∃ X, X = z₀.im := ⟨_, rfl⟩
  rw [← hX] at hQ hcount ⊢
  -- the local cluster, matched into `D⁻¹ℤ`
  set S : Set ℂ := {z | multDiff Z Z' z ≠ 0 ∧ |z.im - X| ≤ R} with hS
  have hcount' : ∀ (s : Finset S) (x y : ℝ), x ≤ y →
      (∀ i ∈ s, D * ((i : ℂ).im - X) ∈ Icc x y) → (s.card : ℝ) ≤ y - x + C₀ := by
    intro s x y hxy hs
    have hle := hcount (s.map (Function.Embedding.subtype _)) (x / D + X) (y / D + X)
      (by linarith [div_le_div_of_nonneg_right hxy hD.le]) fun z hz => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
        obtain ⟨h1, h2⟩ := hs i hi
        refine ⟨i.2.1, i.2.2, ?_, ?_⟩
        · simp only [Function.Embedding.subtype_apply]
          have : x / D ≤ (i : ℂ).im - X := (div_le_iff₀ hD).mpr (by linarith)
          linarith
        · simp only [Function.Embedding.subtype_apply]
          have : (i : ℂ).im - X ≤ y / D := (le_div_iff₀ hD).mpr (by linarith)
          linarith
    rw [Finset.card_map] at hle
    calc (s.card : ℝ) ≤ D * (y / D + X - (x / D + X)) + C₀ := hle
      _ = y - x + C₀ := by field_simp; ring
  obtain ⟨σ, hσ, hσd⟩ := exists_injective_near_int (fun i : S => D * ((i : ℂ).im - X)) hcount'
  have hhalf : ∀ i : S, |((i : ℂ).im - X) - ((σ i / 2 : ℤ) : ℝ) * (2 * h)| ≤ L - 1 / 2 := by
    intro i
    have hσi : |((i : ℂ).im - X) - (σ i : ℝ) * h| ≤ (|C₀| + 1) / 2 * h := by
      have e : ((i : ℂ).im - X) - (σ i : ℝ) * h = h * (D * ((i : ℂ).im - X) - σ i) := by
        rw [mul_sub, ← mul_assoc, mul_comm h D, hDh, one_mul, mul_comm]
      rw [e, abs_mul, abs_of_pos hh, mul_comm]
      refine mul_le_mul_of_nonneg_right ((hσd i).trans ?_) hh.le
      linarith [le_abs_self C₀]
    rw [hL]
    rcases Int.emod_two_eq_zero_or_one (σ i) with h0 | h1
    · have e : ((σ i / 2 : ℤ) : ℝ) * (2 * h) = (σ i : ℝ) * h := by
        have : (2 : ℤ) * (σ i / 2) = σ i := by omega
        have hc : (2 : ℝ) * ((σ i / 2 : ℤ) : ℝ) = (σ i : ℝ) := by exact_mod_cast this
        linear_combination h * hc
      rw [e]
      linarith
    · have e : ((σ i / 2 : ℤ) : ℝ) * (2 * h) = (σ i : ℝ) * h - h := by
        have : (2 : ℤ) * (σ i / 2) + 1 = σ i := by omega
        have hc : (2 : ℝ) * ((σ i / 2 : ℤ) : ℝ) + 1 = (σ i : ℝ) := by exact_mod_cast this
        linear_combination h * hc
      rw [e, show ((i : ℂ).im - X) - ((σ i : ℝ) * h - h) = (((i : ℂ).im - X) - (σ i : ℝ) * h) + h
        by ring]
      exact (abs_add_le _ _).trans (by rw [abs_of_pos hh]; linarith)
  -- the cluster lies in the strip
  have hstrip : ∀ z, multDiff Z Z' z ≠ 0 → |z.re - 1 / 2| ≤ 1 / 2 := by
    intro z hz
    rcases mem_carrier_of_multDiff_ne_zero hz with h' | h'
    · obtain ⟨h1, h2⟩ := Z.strip _ h'
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨h1, h2⟩ := Z'.strip _ h'
      rw [abs_le]; constructor <;> linarith
  -- the translated camera points
  have hnorm : ∀ (w : ℂ) (t : ℝ), ‖w - t‖ ≤ |w.re - t| + |w.im| := fun w t => by
    have h' := Complex.norm_le_abs_re_add_abs_im (w - t)
    simpa using h'
  set Γ : ℂ → ℂ := fun z => gammaOf z - X with hΓ
  set Γc : ℂ → ℂ := fun z => conj (gammaOf z) - X with hΓc
  have hΓre : ∀ z, (Γ z).re = z.im - X := fun z => by simp [hΓ, gammaOf_re]
  have hΓim : ∀ z, (Γ z).im = -(z.re - 1 / 2) := fun z => by simp [hΓ, gammaOf_im]
  have hΓcre : ∀ z, (Γc z).re = z.im - X := fun z => by simp [hΓc, gammaOf_re]
  have hΓcim : ∀ z, (Γc z).im = z.re - 1 / 2 := fun z => by simp [hΓc, gammaOf_im]
  have hcast : ∀ i : S, ((σ i / 2 : ℤ) : ℂ) * ((2 * h : ℝ) : ℂ) =
      ((((σ i / 2 : ℤ) : ℝ) * (2 * h) : ℝ) : ℂ) := fun i => by push_cast; ring
  have hΓb : ∀ i : S, ‖Γ i - ((σ i / 2 : ℤ) : ℂ) * ((2 * h : ℝ) : ℂ)‖ ≤ L := fun i => by
    rw [hcast]
    refine (hnorm _ _).trans ?_
    rw [hΓre, hΓim, abs_neg]
    linarith [hhalf i, hstrip _ i.2.1]
  have hΓcb : ∀ i : S, ‖Γc i - ((σ i / 2 : ℤ) : ℂ) * ((2 * h : ℝ) : ℂ)‖ ≤ L := fun i => by
    rw [hcast]
    refine (hnorm _ _).trans ?_
    rw [hΓcre, hΓcim]
    linarith [hhalf i, hstrip _ i.2.1]
  have hinj : ∀ P : Set S, (∀ i ∈ P, ∀ j ∈ P, σ i % 2 = σ j % 2) →
      Set.InjOn (fun i => σ i / 2) P := by
    intro P hP i hi j hj e
    apply hσ
    have := hP i hi j hj
    simp only at e
    omega
  -- the two windows at height `0`
  set PA : Set S := {i | σ i % 2 = 0 ∧ ¬ Q i} with hPA
  set PB : Set S := {i | σ i % 2 = 1 ∧ ¬ Q i} with hPB
  have hz₀re : (Γ z₀).re = 0 := by rw [hΓre, hX, sub_self]
  have hz₀cre : (Γc z₀).re = 0 := by rw [hΓcre, hX, sub_self]
  have hz₀im : |(Γ z₀).im| ≤ 1 / 2 := by rw [hΓim, abs_neg]; exact hz₀
  have hz₀cim : |(Γc z₀).im| ≤ 1 / 2 := by rw [hΓcim]; exact hz₀
  have hsep : ∀ i ∈ PA ∪ PB, η ≤ ‖z₀ - (i : ℂ)‖ := by
    intro i hi
    have hne : ¬ Q i := by rcases hi with hi | hi; exacts [hi.2, hi.2]
    rw [norm_sub_rev]
    exact hQ _ i.2.1 i.2.2 hne
  obtain ⟨F₁, hF₁A, hF₁Φ⟩ := hwin (fun i : S => Γ i) (fun i => σ i / 2) PA
    (hinj PA fun i hi j hj => by rw [hi.1, hj.1]) (fun i _ => hΓb i)
    (fun i _ => by rw [hΓim, abs_neg]; exact hstrip _ i.2.1) (Γ z₀) hz₀re hz₀im
    (fun i hi => by
      rw [show Γ z₀ - Γ i = gammaOf z₀ - gammaOf i by simp [hΓ], norm_gammaOf_sub]
      exact hsep i (Or.inl hi))
  obtain ⟨G₁, hG₁B, hG₁Φ⟩ := hwin (fun i : S => Γc i) (fun i => σ i / 2) PB
    (hinj PB fun i hi j hj => by rw [hi.1, hj.1]) (fun i _ => hΓcb i)
    (fun i _ => by rw [hΓcim]; exact hstrip _ i.2.1) (Γc z₀) hz₀cre hz₀cim
    (fun i hi => by
      rw [show Γc z₀ - Γc i = conj (gammaOf z₀ - gammaOf i) by simp [hΓc], Complex.norm_conj,
        norm_gammaOf_sub]
      exact hsep i (Or.inr hi))
  refine ⟨F₁, G₁, fun z hcz hzR hQz => ?_, hF₁Φ, hG₁Φ⟩
  set i : S := ⟨z, hcz, hzR⟩
  rcases Int.emod_two_eq_zero_or_one (σ i) with he | ho
  · exact Or.inl (hF₁A i ⟨he, hQz⟩)
  · exact Or.inr (hG₁B i ⟨ho, hQz⟩)

/-- **A pair of local isolating windows.** For a cluster near the height `X` of `z₀` with count
bound `(D, C₀)`, `πD/2 + 2ε ≤ a`, and every cluster point outside an excluded set `Q` at distance
`≥ η` from `z₀`, there are smooth windows `F₁, G₁` of aperture `a` at height `0` such that at every
such point `F̂₁(γ_z − X) = 0` or `Ĝ₁(conj γ_z − X) = 0`. Both see `z₀` with floor `windowFloor`, and
both decay on the strip with constant `windowGrowth · C_m C_0 e^ε`. -/
theorem exists_local_isolating_pair {a D C₀ η ε : ℝ} (hD : 0 < D) (hη : 0 < η) (hε : 0 < ε)
    (hεa : π * D / 2 + 2 * ε ≤ a) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbs : tsupport b ⊆ Icc (-ε) ε) (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖) {k m : ℕ}
    (hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + k ≤ m) {Cm C0 : ℝ}
    (hCm : ∀ w : ℂ, (1 + ‖w‖) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|))
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|))
    (Z Z' : ZeroConfig) {z₀ : ℂ} (hz₀ : |z₀.re - 1 / 2| ≤ 1 / 2) {R : ℝ} (Q : ℂ → Prop)
    (hQ : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → ¬ Q z → η ≤ ‖z - z₀‖)
    (hcount : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ R ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀) :
    ∃ F₁ G₁ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ContDiff ℝ (⊤ : ℕ∞) G₁ ∧
      ApertureWindow a F₁ ∧ ApertureWindow a G₁ ∧
      (∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → ¬ Q z →
        paperFT F₁ (gammaOf z - z₀.im) = 0 ∨ paperFT G₁ (conj (gammaOf z) - z₀.im) = 0) ∧
      windowFloor (2 * D⁻¹) (localSlack D C₀) η ≤ ‖paperFT F₁ (gammaOf z₀ - z₀.im)‖ ∧
      windowFloor (2 * D⁻¹) (localSlack D C₀) η ≤ ‖paperFT G₁ (conj (gammaOf z₀) - z₀.im)‖ ∧
      (∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖paperFT F₁ w‖ * (1 + |w.re|) ^ k ≤
        windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) ∧
      (∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖paperFT G₁ w‖ * (1 + |w.re|) ^ k ≤
        windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) := by
  have hh : (0 : ℝ) < 2 * D⁻¹ := by positivity
  have hL0 : 0 ≤ localSlack D C₀ := by unfold localSlack; positivity
  have hr : π / (2 * D⁻¹) + 2 * ε ≤ a := by
    rw [show π / (2 * D⁻¹) = π * D / 2 by field_simp]
    exact hεa
  obtain ⟨F₁, G₁, hblind, hF, hG⟩ := exists_local_pair_of_windows hD
    (fun f w₀ => ContDiff ℝ (⊤ : ℕ∞) f ∧ ApertureWindow a f ∧
      windowFloor (2 * D⁻¹) (localSlack D C₀) η ≤ ‖paperFT f w₀‖ ∧
      ∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖paperFT f w‖ * (1 + |w.re|) ^ k ≤
        windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε)
    (fun lam τ P hτ hPL hPim w₀ h1 h2 h3 => by
      obtain ⟨f, hfs, hfw, hfP, hf0, hfd⟩ := isolating_window_of_bump hh hL0 hη hε hr hb hbs hb1
        hm hCm hC0 lam τ P hτ hPL hPim h1 h2 h3
      exact ⟨f, hfP, hfs, hfw, hf0, hfd⟩) Z Z' hz₀ Q hQ hcount
  exact ⟨F₁, G₁, hF.1, hG.1, hF.2.1, hG.2.1, hblind, hF.2.2.1, hG.2.2.1, hF.2.2.2, hG.2.2.2⟩

/-- **The local camera, explicitly.** Let `b` be a bump on `[−ε, ε]` with `|b̂(iy)| ≥ 1` and decay
constants `C_m, C_0`, where `m ≥ windowExponent (2/D) (localSlack D C₀) + k` and
`πD/2 + 2ε ≤ a`. Let `Z, Z'` be tempered mimics at aperture `a` and `z₀` a point of their
cluster at height `X`. Suppose the other cluster points with height in `[X − R, X + R]` are
`η`-far from `z₀` and have count bound `(D, C₀)`. Then
`(1 + R)^{2k−2} ≤ localCameraConst a D C₀ η ε C_m C_0 · (1 + |X|)² Σ_z |c(z)|/(1 + |γ_z|²)`. -/
theorem one_add_pow_le_of_isolated_cancellation_of_bump {a D C₀ η ε : ℝ} (hD : 0 < D)
    (hη : 0 < η) (hε : 0 < ε) (hεa : π * D / 2 + 2 * ε ≤ a) {b : ℝ → ℂ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbs : tsupport b ⊆ Icc (-ε) ε)
    (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖) {k m : ℕ} (hk : 1 ≤ k)
    (hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + k ≤ m) {Cm C0 : ℝ}
    (hCm : ∀ w : ℂ, (1 + ‖w‖) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|))
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|))
    {Z Z' : ZeroConfig} (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) {z₀ : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : multDiff Z Z' z₀ ≠ 0)
    (hiso : ∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → η ≤ ‖z - z₀‖)
    (hcount : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ R ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀) :
    (1 + R) ^ (2 * k - 2) ≤ localCameraConst a D C₀ η ε Cm C0 * (1 + |z₀.im|) ^ 2 *
      ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) := by
  classical
  obtain ⟨h, hh_def⟩ : ∃ h, h = D⁻¹ := ⟨_, rfl⟩
  obtain ⟨L, hLs⟩ : ∃ L, L = localSlack D C₀ := ⟨_, rfl⟩
  have hh : 0 < h := by rw [hh_def]; exact inv_pos.mpr hD
  have hL0 : 0 ≤ L := by rw [hLs, localSlack]; positivity
  have ha : 0 ≤ a := by nlinarith [Real.pi_pos]
  have hCm0 : 0 ≤ Cm := by
    have h1 := hCm 0
    rw [Complex.zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h1
    exact le_trans (by positivity) h1
  have hC00 : 0 ≤ C0 := by
    have h1 := hC0 0
    rw [Complex.zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h1
    exact le_trans (norm_nonneg _) h1
  obtain ⟨c, hcdef⟩ : ∃ c, c = windowFloor (2 * h) L η := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = windowGrowth (2 * h) L * Cm * C0 * Real.exp ε := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; exact windowFloor_pos (by positivity) hL0 hη
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (windowGrowth_nonneg (by positivity) hL0) hCm0)
      hC00) (Real.exp_pos _).le
  have hBdef : localCameraConst a D C₀ η ε Cm C0 = M * M * Real.exp a * (5 / 4) / (c * c) := by
    rw [localCameraConst, ← hh_def, ← hLs, ← hcdef, ← hMdef]
    ring
  have hstrip : ∀ z, multDiff Z Z' z ≠ 0 → |z.re - 1 / 2| ≤ 1 / 2 := by
    intro z hz
    rcases mem_carrier_of_multDiff_ne_zero hz with h' | h'
    · obtain ⟨h1, h2⟩ := Z.strip _ h'
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨h1, h2⟩ := Z'.strip _ h'
      rw [abs_le]; constructor <;> linarith
  obtain ⟨F₁, G₁, -, -, hF₁, hG₁, hblind, hF₁0, hG₁0, hF₁d, hG₁d⟩ :=
    exists_local_isolating_pair hD hη hε hεa hb hbs hb1 hm hCm hC0 Z Z' (hstrip _ hc)
      (fun z => z = z₀) (fun z hcz hzR hne => hiso z hne hcz hzR) hcount
  rw [← hh_def, ← hLs, ← hcdef] at hF₁0 hG₁0
  rw [← hh_def, ← hLs, ← hMdef] at hF₁d hG₁d
  obtain ⟨X, hX⟩ : ∃ X, X = z₀.im := ⟨_, rfl⟩
  rw [← hX] at hiso hcount hblind hF₁0 hG₁0 ⊢
  -- modulated to height `X`
  set F := localWindow X F₁ with hF
  set G := localWindow X G₁ with hG
  have hFw : ApertureWindow a F := apertureWindow_localWindow hF₁ X
  have hGw : ApertureWindow a G := apertureWindow_localWindow hG₁ X
  have hFdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT F w‖ * (1 + |w.re - X|) ^ k ≤ M * Real.exp (a * |w.im|) := fun w hw => by
    rw [hF, paperFT_localWindow]
    have := hF₁d (w - X) (by simpa using hw)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    exact this.trans (le_mul_of_one_le_right hM0 (Real.one_le_exp (by positivity)))
  have hGdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT G w‖ * (1 + |w.re - X|) ^ k ≤ M * Real.exp (a * |w.im|) := fun w hw => by
    rw [hG, paperFT_localWindow]
    have := hG₁d (w - X) (by simpa using hw)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    exact this.trans (le_mul_of_one_le_right hM0 (Real.one_le_exp (by positivity)))
  -- the near cluster is invisible except at `z₀`
  have hnear : ∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - X| ≤ R → pointImage F G z = 0 := by
    intro z hz hcz hzR
    rw [pointImage, hF, hG, paperFT_localWindow, paperFT_localWindow]
    rcases hblind z hcz hzR hz with h0 | h0
    · rw [h0, zero_mul]
    · rw [h0, map_zero, mul_zero]
  have hsee : c * c ≤ ‖pointImage F G z₀‖ := by
    rw [pointImage, hF, hG, paperFT_localWindow, paperFT_localWindow, norm_mul, Complex.norm_conj]
    exact mul_le_mul hF₁0 hG₁0 hc0.le (hc0.le.trans hF₁0)
  -- mimicry: the image of the cluster vanishes
  have htot := summable_multDiff_pointImage hZ hZ' hFw.1 hFw.hasCompactSupport hGw.1
    hGw.hasCompactSupport
  have hzero : ∑' z, multDiff Z Z' z * pointImage F G z = 0 := by
    rw [← W_sub_W_eq_tsum hZ hZ' hFw.1 hFw.hasCompactSupport hGw.1 hGw.hasCompactSupport,
      W_eq_of_mimic hZ hZ' hW hFw hGw, sub_self]
  have hsplit : ∀ z, multDiff Z Z' z * pointImage F G z =
      (if z = z₀ then multDiff Z Z' z₀ * pointImage F G z₀ else 0) +
        (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0) := by
    intro z
    by_cases hz : z = z₀
    · subst hz
      have : ¬ R < |z.im - X| := by rw [hX, sub_self, abs_zero]; linarith
      rw [if_pos rfl, if_neg this, add_zero]
    · rw [if_neg hz, zero_add]
      split_ifs with hfar
      · rfl
      · by_cases hcz : multDiff Z Z' z = 0
        · rw [hcz, zero_mul]
        · rw [hnear z hz hcz (not_lt.mp hfar), mul_zero]
  have hsingle : Summable fun z => if z = z₀ then multDiff Z Z' z₀ * pointImage F G z₀ else 0 :=
    (hasSum_ite_eq z₀ _).summable
  have hfarS : Summable fun z => if R < |z.im - X| then multDiff Z Z' z * pointImage F G z
      else 0 :=
    (htot.sub hsingle).congr fun z => sub_eq_of_eq_add' (hsplit z)
  rw [tsum_congr hsplit, hsingle.tsum_add hfarS, tsum_ite_eq] at hzero
  -- the far tail
  obtain ⟨hfs, hfle⟩ := tsum_far_multDiff_le hZ hZ' hk ha hFdec hGdec hR
  have hfnorm : ∀ z, ‖(if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ =
      farTerm (multDiff Z Z') F G X R z := fun z => by
    unfold farTerm
    split_ifs
    · rw [norm_mul]
    · rw [norm_zero]
  have hfarle : ‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ ≤
      M * M * Real.exp a * (5 / 4 * (1 + |X|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
    (norm_tsum_le_tsum_norm (hfs.congr fun z => (hfnorm z).symm)).trans
      ((tsum_congr hfnorm).le.trans hfle)
  have hval : ‖multDiff Z Z' z₀ * pointImage F G z₀‖ =
      ‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ := by
    rw [eq_neg_of_add_eq_zero_left hzero, norm_neg]
  have hlow : c * c ≤ ‖multDiff Z Z' z₀ * pointImage F G z₀‖ := by
    rw [norm_mul]
    calc c * c = 1 * (c * c) := (one_mul _).symm
      _ ≤ _ := mul_le_mul (one_le_norm_multDiff hc) hsee (by positivity) (norm_nonneg _)
  obtain ⟨Sg, hSg⟩ : ∃ Sg, Sg = ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
    ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (1 + R) ^ (2 * k - 2) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  rw [← hSg, ← hQ] at hfarle
  rw [← hSg, ← hQ]
  have hmain : c * c * Q ≤ M * M * Real.exp a * (5 / 4) * (1 + |X|) ^ 2 * Sg := by
    have h1 : c * c ≤ (M * M * Real.exp a * (5 / 4) * (1 + |X|) ^ 2 * Sg) / Q := by
      have := (hlow.trans hval.le).trans hfarle
      calc c * c ≤ _ := this
        _ = _ := by ring
    rwa [le_div_iff₀ hQ0] at h1
  rw [hBdef, show M * M * Real.exp a * (5 / 4) / (c * c) * (1 + |X|) ^ 2 * Sg =
    (M * M * Real.exp a * (5 / 4) * (1 + |X|) ^ 2 * Sg) / (c * c) by ring,
    le_div_iff₀ (by positivity)]
  linarith


/-- **The local camera.** Let `Z, Z'` be tempered mimics at aperture `a` and `z₀` a point of their
cluster at height `X`. If every other cluster point with height in `[X − R, X + R]` is `η`-far
from `z₀`, and these points have count bound `(D, C₀)` with `πD < 2a`, then
`(1 + R)^{2k−2} ≤ B (1 + |X|)² Σ_z |c(z)|/(1 + |γ_z|²)`, with `B` depending only on
`a, D, C₀, η, k`. -/
theorem one_add_pow_le_of_isolated_cancellation {a D C₀ η : ℝ} (hD : 0 < D) (hDa : π * D < 2 * a)
    (hη : 0 < η) {k : ℕ} (hk : 1 ≤ k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (Z Z' : ZeroConfig), TemperedConfig Z → TemperedConfig Z' →
      (∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) →
      ∀ (z₀ : ℂ) (R : ℝ), 0 ≤ R → multDiff Z Z' z₀ ≠ 0 →
      (∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → η ≤ ‖z - z₀‖) →
      (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
        (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ R ∧ z.im ∈ Icc x y) →
          (s.card : ℝ) ≤ D * (y - x) + C₀) →
      (1 + R) ^ (2 * k - 2) ≤
        B * (1 + |z₀.im|) ^ 2 * ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) := by
  obtain ⟨ε, hε⟩ : ∃ ε, ε = (a - π * D / 2) / 3 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨b, hb, hbs, hb1⟩ := exists_bump_one_le_norm_paperFT_I_mul hε0
  obtain ⟨Cm, -, hCm⟩ := exists_pow_mul_norm_paperFT_le_exp hb hε0.le hbs
    (⌈windowExponent (2 * D⁻¹) (localSlack D C₀)⌉₊ + k)
  obtain ⟨C0, -, hC0⟩ := exists_pow_mul_norm_paperFT_le_exp hb hε0.le hbs 0
  have hC0' : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|) := fun w => by
    have := hC0 w
    rwa [pow_zero, one_mul] at this
  have hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + k ≤
      ((⌈windowExponent (2 * D⁻¹) (localSlack D C₀)⌉₊ + k : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil (windowExponent (2 * D⁻¹) (localSlack D C₀))]
  refine ⟨localCameraConst a D C₀ η ε Cm C0, by unfold localCameraConst; positivity,
    fun Z Z' hZ hZ' hW z₀ R hR hc hiso hcount => ?_⟩
  exact one_add_pow_le_of_isolated_cancellation_of_bump hD hη hε0 (by rw [hε]; linarith) hb hbs
    hb1 hk hm hCm hC0' hZ hZ' hW hR hc hiso hcount

end GaloisForLFunctions.ZeroConfigurationGeometry
