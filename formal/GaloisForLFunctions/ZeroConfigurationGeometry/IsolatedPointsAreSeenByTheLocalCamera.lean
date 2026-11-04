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
  classical
  -- the bump and the constants, fixed before the point set
  obtain ⟨ε, hε⟩ : ∃ ε, ε = (r - π / H) / 3 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨b, hb, hbs, hb1⟩ := exists_bump_one_le_norm_paperFT_I_mul hε0
  have hbc : HasCompactSupport b := isCompact_Icc.of_isClosed_subset (isClosed_tsupport b) hbs
  obtain ⟨L', hL'⟩ : ∃ L', L' = L + 2 * H := ⟨_, rfl⟩
  have hL'0 : 0 ≤ L' := by rw [hL']; linarith
  obtain ⟨η', hη'⟩ : ∃ η', η' = min η (H / 2) := ⟨_, rfl⟩
  have hη'0 : 0 < η' := by rw [hη']; exact lt_min hη (by linarith)
  obtain ⟨K, hK⟩ : ∃ K, K = nearestConstStrip H L' * Real.exp (3 * L' * nearFarConst H L') :=
    ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK, nearestConstStrip]
    refine mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (by linarith)) (by linarith)) zero_le_one) (Real.exp_pos _).le) (Real.exp_pos _).le
  obtain ⟨p, hp⟩ : ∃ p, p = 3 * L' * (4 * (1 + L') / H) := ⟨_, rfl⟩
  obtain ⟨Cb, hCb0, hCb⟩ := exists_pow_mul_norm_paperFT_le_exp hb hε0.le hbs (⌈p⌉₊ + k)
  obtain ⟨C0, hC00, hC0⟩ := exists_pow_mul_norm_paperFT_le_exp hb hε0.le hbs 0
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = isoConst L' η' * Real.exp (-(isoRate L' η' * nearFarConst H L')) :=
    ⟨_, rfl⟩
  have hφ0 : 0 < φ := by rw [hφ]; exact mul_pos (isoConst_pos hL'0 hη'0) (Real.exp_pos _)
  refine ⟨1 / 2 * φ, K * Cb * C0 * Real.exp ε, by positivity,
    mul_nonneg (mul_nonneg (mul_nonneg hK0 hCb0) hC00) (Real.exp_pos _).le, ?_⟩
  intro ι lam τ P hτ hPL hPim w₀ hw₀re hw₀im hw₀P
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
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by linarith) hH), hL']
      have := hPL v hvP
      nlinarith
    · rw [hνout j hj, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show (j : ℝ) * H + H / 2 - latPt H θ j = H * (1 / 2 - θ) by rw [latPt]; ring, abs_mul,
        abs_of_pos hH, hL']
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
  refine ⟨F, ⟨hFsmooth.of_le (by norm_cast), hFs⟩, fun i hi => by
    rw [hFt, ← hντ i hi, hfν (τ i), zero_mul], ?_, ?_⟩
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
    rw [hFt, hfz w₀ hw₀lat, hf₀t, norm_mul, norm_mul, norm_mul]
    calc 1 / 2 * φ = 1 / 2 * 1 * φ * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul (mul_le_mul hsin hbw₀ zero_le_one (by positivity)) hfloor
          hφ0.le (by positivity)) hbw₀ zero_le_one (by positivity)
  · -- the decay on the strip
    have hoff : ∀ w : ℂ, |w.im| ≤ 1 / 2 → (∀ j, w ≠ latPt H θ j) →
        ‖paperFT F w‖ * (1 + |w.re|) ^ k ≤ K * Cb * C0 * Real.exp ε := by
      intro w hw hwl
      have hsp := norm_sin_mul_tprod_pertFactor_le_strip hH hθ hνb hνim hw hwl
      rw [← hK, ← hp] at hsp
      have h1 : (1 : ℝ) ≤ 1 + |w.re| := by linarith [abs_nonneg w.re]
      have hpn : (1 + |w.re|) ^ p ≤ (1 + |w.re|) ^ ⌈p⌉₊ := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil p)
      have hb1' := hCb w
      have hb0' := hC0 w
      rw [pow_zero, one_mul] at hb0'
      have hre : (1 + |w.re|) ^ (⌈p⌉₊ + k) ≤ (1 + ‖w‖) ^ (⌈p⌉₊ + k) :=
        pow_le_pow_left₀ (by positivity) (by linarith [Complex.abs_re_le_norm w]) _
      have hexp : Real.exp (ε * |w.im|) * Real.exp (ε * |w.im|) ≤ Real.exp ε := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg w.im])
      have hA : ‖Complex.sin (((π / H : ℝ) : ℂ) * (w - ((θ * H : ℝ) : ℂ))) *
          ∏' j, pertFactor H θ ν j w‖ ≤ K * (1 + |w.re|) ^ ⌈p⌉₊ :=
        hsp.trans (mul_le_mul_of_nonneg_left hpn hK0)
      have hB : (1 + |w.re|) ^ (⌈p⌉₊ + k) * ‖paperFT b w‖ ≤ Cb * Real.exp (ε * |w.im|) :=
        (mul_le_mul_of_nonneg_right hre (norm_nonneg _)).trans hb1'
      rw [hFt, hfz w hwl, hf₀t]
      calc ‖Complex.sin (((π / H : ℝ) : ℂ) * (w - ((θ * H : ℝ) : ℂ))) * paperFT b w *
            (∏' j, pertFactor H θ ν j w) * paperFT b w‖ * (1 + |w.re|) ^ k
          = ‖Complex.sin (((π / H : ℝ) : ℂ) * (w - ((θ * H : ℝ) : ℂ))) *
              ∏' j, pertFactor H θ ν j w‖ * ((1 + |w.re|) ^ k * ‖paperFT b w‖) *
                ‖paperFT b w‖ := by
            rw [norm_mul, norm_mul, norm_mul, norm_mul]; ring
        _ ≤ K * (1 + |w.re|) ^ ⌈p⌉₊ * ((1 + |w.re|) ^ k * ‖paperFT b w‖) * ‖paperFT b w‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (by positivity))
              (norm_nonneg _)
        _ = K * ((1 + |w.re|) ^ (⌈p⌉₊ + k) * ‖paperFT b w‖) * ‖paperFT b w‖ := by
            rw [pow_add]; ring
        _ ≤ K * (Cb * Real.exp (ε * |w.im|)) * (C0 * Real.exp (ε * |w.im|)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hB hK0) hb0' (norm_nonneg _)
              (mul_nonneg hK0 (mul_nonneg hCb0 (Real.exp_pos _).le))
        _ = K * Cb * C0 * (Real.exp (ε * |w.im|) * Real.exp (ε * |w.im|)) := by ring
        _ ≤ K * Cb * C0 * Real.exp ε :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg (mul_nonneg hK0 hCb0) hC00)
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
  classical
  obtain ⟨h, hh_def⟩ : ∃ h, h = D⁻¹ := ⟨_, rfl⟩
  have hh : 0 < h := by rw [hh_def]; exact inv_pos.mpr hD
  have hDh : D * h = 1 := by rw [hh_def]; field_simp
  obtain ⟨L, hL⟩ : ∃ L, L = (|C₀| + 1) / 2 * h + h + 1 / 2 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hr : π / (2 * h) < a := by
    rw [div_lt_iff₀ (by positivity)]
    have : a * (2 * h) = 2 * a / D := by rw [hh_def]; field_simp
    rw [this, lt_div_iff₀ hD]
    linarith
  have ha : 0 ≤ a := by nlinarith [Real.pi_pos]
  obtain ⟨c, M, hc0, hM0, hwin⟩ := exists_uniform_isolating_window (by positivity : 0 < 2 * h)
    hr hL0 hη k
  refine ⟨M * M * Real.exp a * (5 / 4) / (c * c), by positivity, ?_⟩
  intro Z Z' hZ hZ' hW z₀ R hR hc hiso hcount
  obtain ⟨X, hX⟩ : ∃ X, X = z₀.im := ⟨_, rfl⟩
  rw [← hX] at hiso hcount ⊢
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
  set PA : Set S := {i | σ i % 2 = 0 ∧ (i : ℂ) ≠ z₀} with hPA
  set PB : Set S := {i | σ i % 2 = 1 ∧ (i : ℂ) ≠ z₀} with hPB
  have hz₀re : (Γ z₀).re = 0 := by rw [hΓre, hX, sub_self]
  have hz₀cre : (Γc z₀).re = 0 := by rw [hΓcre, hX, sub_self]
  have hz₀im : |(Γ z₀).im| ≤ 1 / 2 := by rw [hΓim, abs_neg]; exact hstrip _ hc
  have hz₀cim : |(Γc z₀).im| ≤ 1 / 2 := by rw [hΓcim]; exact hstrip _ hc
  have hsep : ∀ i ∈ PA ∪ PB, η ≤ ‖z₀ - (i : ℂ)‖ := by
    intro i hi
    have hne : (i : ℂ) ≠ z₀ := by rcases hi with hi | hi; exacts [hi.2, hi.2]
    rw [norm_sub_rev]
    exact hiso _ hne i.2.1 i.2.2
  obtain ⟨F₁, hF₁, hF₁A, hF₁0, hF₁d⟩ := hwin (fun i : S => Γ i) (fun i => σ i / 2) PA
    (hinj PA fun i hi j hj => by rw [hi.1, hj.1]) (fun i _ => hΓb i)
    (fun i _ => by rw [hΓim, abs_neg]; exact hstrip _ i.2.1) (Γ z₀) hz₀re hz₀im
    (fun i hi => by
      rw [show Γ z₀ - Γ i = gammaOf z₀ - gammaOf i by simp [hΓ], norm_gammaOf_sub]
      exact hsep i (Or.inl hi))
  obtain ⟨G₁, hG₁, hG₁B, hG₁0, hG₁d⟩ := hwin (fun i : S => Γc i) (fun i => σ i / 2) PB
    (hinj PB fun i hi j hj => by rw [hi.1, hj.1]) (fun i _ => hΓcb i)
    (fun i _ => by rw [hΓcim]; exact hstrip _ i.2.1) (Γc z₀) hz₀cre hz₀cim
    (fun i hi => by
      rw [show Γc z₀ - Γc i = conj (gammaOf z₀ - gammaOf i) by simp [hΓc], Complex.norm_conj,
        norm_gammaOf_sub]
      exact hsep i (Or.inr hi))
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
    set i : S := ⟨z, hcz, hzR⟩
    rw [pointImage, hF, hG, paperFT_localWindow, paperFT_localWindow]
    rcases Int.emod_two_eq_zero_or_one (σ i) with he | ho
    · rw [show gammaOf z - X = Γ i from rfl, hF₁A i ⟨he, hz⟩, zero_mul]
    · rw [show conj (gammaOf z) - X = Γc i from rfl, hG₁B i ⟨ho, hz⟩, map_zero, mul_zero]
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
  rw [show M * M * Real.exp a * (5 / 4) / (c * c) * (1 + |X|) ^ 2 * Sg =
    (M * M * Real.exp a * (5 / 4) * (1 + |X|) ^ 2 * Sg) / (c * c) by ring,
    le_div_iff₀ (by positivity)]
  linarith

end GaloisForLFunctions.ZeroConfigurationGeometry
