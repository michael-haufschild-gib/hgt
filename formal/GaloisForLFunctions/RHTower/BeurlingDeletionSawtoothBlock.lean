import GaloisForLFunctions.RHTower.BeurlingDeletionMobius
import GaloisForLFunctions.HTGeometry.SmoothedSawtoothFourier

/-!
# Dyadic sawtooth blocks of a deletion set

Let `S` be a deletion set (`DeletionData α`, `1/2 < α < 1`), `μ_S` its Möbius function and `λ_S`
the indicator of the `S`-numbers.  Assume RH, fix `0 < ε < 1/4` and put `σ₀ = α/2 + ε`.

* **The partition.**  `φ(u) = smoothTransition(2 − u)` (`cut`) equals `1` on `u ≤ 1`, `0` on
  `u ≥ 2` and is antitone; `F(u) = φ(u/2) − φ(u)` (`bump`) is a nonnegative test function on
  `[1, 4]`, and `φ(u/2^J M) − φ(u/M) = Σ_{j<J} F(u/2^j M)` (`cut_sub_cut_eq_sum_bump`).
* **Smooth sums** (`exists_norm_tsum_mobS_le`, `exists_norm_tsum_lamS_sub_le`).  For every test
  function `g`,
  `|Σ μ_S(n) g(n/M)| ≤ K M^{σ₀} ∫ (|t| + 1)^ε |𝓜g(σ₀ + it)| dt` and
  `|Σ λ_S(n) g(n/M) − H(α) 𝓜g(α) M^α| ≤ K M^{σ₀} ∫ (|t| + 1)^ε |𝓜g(σ₀ + it)| dt`,
  by Perron's formula shifted to `Re s = σ₀` (`HTGeometry.TestFunctionPerron`).
* **The block** (`exists_norm_block_le`).  For `1 ≤ M ≤ x` and `0 < Δ ≤ 1`,
  `|Σ_m μ_S(m) F(m/M) ψ(x/m)| ≤ K (M^{σ₀} (x/M)^{1/2+ε} Δ^{−1/2−2ε} + Δ^{1−ε} M^α)`.
  The sawtooth is split into a smooth trigonometric part and a positive majorant
  (`HTGeometry.SmoothedSawtooth.exists_saw_decomposition`); every frequency `h` gives the twisted
  sum `Σ b(m) F(m/M) e(hx/m)` of the test function `F(u) e(c/u)`, `c = hx/M`, whose Mellin transform
  has `L¹` mass `≪ (1 + |c|)^{1/2+ε}` and value at `α` of size `≪ 1/(1 + |c|)`.
-/

open Complex Finset Filter Topology Real
open GaloisForLFunctions.HTGeometry.TestFunctionPerron GaloisForLFunctions.HTGeometry.SmoothedSawtooth
open scoped ContDiff

noncomputable section

namespace RHTower.BeurlingDeletion

/-! ## The dyadic partition -/

/-- `φ(u) = 1` for `u ≤ 1`, `0` for `u ≥ 2`, smooth and antitone. -/
def cut (u : ℝ) : ℝ := Real.smoothTransition (2 - u)

theorem cut_antitone : Antitone cut := fun _ _ h =>
  Real.smoothTransition.monotone (by linarith)

theorem cut_eq_one {u : ℝ} (hu : u ≤ 1) : cut u = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cut_eq_zero {u : ℝ} (hu : 2 ≤ u) : cut u = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cut_nonneg (u : ℝ) : 0 ≤ cut u := Real.smoothTransition.nonneg _

theorem cut_le_one (u : ℝ) : cut u ≤ 1 := Real.smoothTransition.le_one _

theorem contDiff_cut : ContDiff ℝ ∞ cut :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

/-- `F(u) = φ(u/2) − φ(u)`, a bump on `[1, 4]`. -/
def bump (u : ℝ) : ℝ := cut (u / 2) - cut u

theorem bump_eq_zero_of_le {u : ℝ} (hu : u ≤ 1) : bump u = 0 := by
  unfold bump
  rw [cut_eq_one hu, cut_eq_one (by linarith)]; ring

theorem bump_eq_zero_of_ge {u : ℝ} (hu : 4 ≤ u) : bump u = 0 := by
  unfold bump
  rw [cut_eq_zero (by linarith), cut_eq_zero (by linarith)]; ring

theorem bump_nonneg (u : ℝ) : 0 ≤ bump u := by
  rcases le_or_gt u 1 with hu | hu
  · rw [bump_eq_zero_of_le hu]
  · unfold bump
    have := cut_antitone (show u / 2 ≤ u by linarith)
    linarith

theorem bump_le_one (u : ℝ) : bump u ≤ 1 := by
  unfold bump; linarith [cut_le_one (u / 2), cut_nonneg u]

/-- `F` with complex values. -/
def bumpC (u : ℝ) : ℂ := (bump u : ℂ)

theorem isTest_bumpC : IsTest bumpC 1 4 := by
  refine ⟨one_pos, by norm_num, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((contDiff_cut.comp (contDiff_id.div_const 2)).sub
      contDiff_cut)
  · intro u hu
    by_contra h
    apply hu
    simp only [bumpC]
    rcases le_or_gt u 1 with h1 | h1
    · rw [bump_eq_zero_of_le h1]; simp
    · rw [bump_eq_zero_of_ge (by simp only [Set.mem_Icc, not_and_or, not_le] at h; rcases h with h | h <;>
        linarith)]; simp

/-- `F(u)/u` with complex values. -/
def bumpDivC (u : ℝ) : ℂ := ((bump u / u : ℝ) : ℂ)

theorem isTest_bumpDivC : IsTest bumpDivC 1 4 := by
  refine ⟨one_pos, by norm_num, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro u
    rcases lt_or_ge u 1 with hu | hu
    · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hu] with v hv
      simp [bumpDivC, bump_eq_zero_of_le (le_of_lt hv)]
    · have hu0 : u ≠ 0 := by linarith
      have h1 : ContDiffAt ℝ ∞ bump u :=
        ((contDiff_cut.comp (contDiff_id.div_const 2)).sub contDiff_cut).contDiffAt
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp u (h1.div contDiffAt_id hu0)
  · intro u hu
    by_contra h
    apply hu
    simp only [bumpDivC]
    rcases le_or_gt u 1 with h1 | h1
    · rw [bump_eq_zero_of_le h1]; simp
    · rw [bump_eq_zero_of_ge (by simp only [Set.mem_Icc, not_and_or, not_le] at h; rcases h with h | h <;>
        linarith)]; simp

/-- Telescoping of the dyadic partition. -/
theorem cut_sub_cut_eq_sum_bump (u M : ℝ) (J : ℕ) :
    cut (u / (2 ^ J * M)) - cut (u / M) = ∑ j ∈ Finset.range J, bump (u / (2 ^ j * M)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold bump
    rw [show u / (2 ^ J * M) / 2 = u / (2 ^ (J + 1) * M) by rw [pow_succ]; ring]
    ring

/-! ## Frequency sums -/

/-- `(1 + (hΔ)²)^{−1} |h|^q ≤ Δ^{−(q+s)} |h|^{−s}` for `0 ≤ q + s ≤ 2`. -/
theorem inv_one_add_sq_mul_rpow_le {Δ : ℝ} (hΔ : 0 < Δ) {q s : ℝ} (h0 : 0 ≤ q + s)
    (h2 : q + s ≤ 2) {h : ℝ} (hh : h ≠ 0) :
    (1 + (h * Δ) ^ 2)⁻¹ * |h| ^ q ≤ Δ ^ (-(q + s)) * |h| ^ (-s) := by
  have hh' : 0 < |h| := abs_pos.mpr hh
  set z := |h| * Δ with hz
  have hz0 : 0 < z := by positivity
  have hzr : z ^ (q + s) ≤ 1 + (h * Δ) ^ 2 := by
    have hsq : (h * Δ) ^ 2 = z ^ (2 : ℝ) := by
      rw [hz, Real.rpow_two, mul_pow, mul_pow, sq_abs]
    rw [hsq]
    rcases le_or_gt z 1 with hz1 | hz1
    · have : z ^ (q + s) ≤ 1 := Real.rpow_le_one hz0.le hz1 h0
      have : 0 ≤ z ^ (2 : ℝ) := by positivity
      linarith
    · have : z ^ (q + s) ≤ z ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hz1.le h2
      linarith
  have hinv : (1 + (h * Δ) ^ 2)⁻¹ ≤ z ^ (-(q + s)) := by
    rw [Real.rpow_neg hz0.le]
    exact inv_anti₀ (by positivity) hzr
  calc (1 + (h * Δ) ^ 2)⁻¹ * |h| ^ q ≤ z ^ (-(q + s)) * |h| ^ q :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = Δ ^ (-(q + s)) * |h| ^ (-s) := by
        rw [hz, Real.mul_rpow hh'.le hΔ.le]
        rw [mul_comm (|h| ^ (-(q + s))), mul_assoc, ← Real.rpow_add hh']
        ring_nf

/-- `Σ_h |h|^{−s}` for `s > 1`. -/
def zetaAbs (s : ℝ) : ℝ := ∑' h : ℤ, |(h : ℝ)| ^ (-s)

theorem zetaAbs_nonneg (s : ℝ) : 0 ≤ zetaAbs s := tsum_nonneg fun _ => by positivity

/-! ## Smooth sums over a deletion set -/

namespace DeletionData

variable {α : ℝ} (D : DeletionData α)

/-- The line weight `∫ (|t| + 1)^κ |𝓜g(σ + it)| dt`. -/
def lineMass (g : ℝ → ℂ) (σ κ : ℝ) : ℝ := ∫ t : ℝ, (|t| + 1) ^ κ * ‖mellin g ((σ : ℂ) + t * I)‖

/-- **Smooth `μ_S` sums.** -/
theorem exists_norm_tsum_mobS_le (hRH : RiemannHypothesis) (hα0 : 0 < α) (hα : α < 1) {ε : ℝ}
    (hε : 0 < ε) (hεα : ε < α / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : ℝ → ℂ) (a b : ℝ), IsTest g a b → ∀ M : ℝ, 0 < M →
      ‖∑' n, D.mobS n * g (n / M)‖ ≤ K * M ^ (α / 2 + ε) * lineMass g (α / 2 + ε) ε := by
  set σ₀ : ℝ := α / 2 + ε with hσ₀
  obtain ⟨c, T, hc, hT1, hEQ⟩ := D.exists_norm_eFactor_mul_qFactor_le hRH hα0 hα
    (δ := ε) hε hεα (κ := ε / 2) (by linarith)
  rw [show 2 * (ε / 2) = ε by ring] at hEQ
  have hcont : ∀ s : ℂ, α / 2 < s.re →
      ContinuousAt (fun s => D.eFactor s * qFactor α s) s := fun s hs =>
    ((D.differentiableOn_eFactor_mul_qFactor hRH hα0 hα).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)).continuousAt
  obtain ⟨K, hK⟩ := exists_strip_bound (G := fun s => D.eFactor s * qFactor α s)
    (σ₀ := σ₀) (σ₁ := 3 / 2) (fun s h1 _ _ => hcont s (by linarith)) hε.le hEQ
  have hlinecont : Continuous fun t : ℝ =>
      ‖D.eFactor ((σ₀ : ℂ) + t * I) * qFactor α ((σ₀ : ℂ) + t * I)‖ :=
    (continuous_iff_continuousAt.mpr fun t => (hcont _ (by simp; linarith)).comp
      (by fun_prop)).norm
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_bound_line hlinecont hε.le (K := K) (T := 1) fun t ht => by
    have h := hK ((σ₀ : ℂ) + t * I) (by simp [hσ₀]) (by simp; linarith) (by simpa using ht)
    simpa using h
  refine ⟨K₀ / (2 * π), by positivity, fun g a b hg M hM => ?_⟩
  have h := norm_tsum_sub_residue_le hg D.mobS D.mobS_zero D.norm_mobS_le (A := 0) (ρ := 1)
    (G₀ := fun s => D.eFactor s * qFactor α s) (a₀ := α / 2) (σ₀ := σ₀) (by linarith)
    (by simp; linarith) (by norm_num)
    (D.differentiableOn_eFactor_mul_qFactor hRH hα0 hα)
    (fun s hs => by rw [zero_div, zero_add, D.LSeries_mobS_eq hα0 hα hs])
    hε.le (by linarith) (K := K) (fun s h1 h2 h3 => by rw [zero_div, zero_add]; exact hK s h1 h2 h3)
    (K₀ := K₀) (fun t => by rw [zero_div, zero_add]; exact hK₀ t) hM
  rw [zero_mul, zero_mul, sub_zero] at h
  calc _ ≤ _ := h
    _ = K₀ / (2 * π) * M ^ σ₀ * lineMass g σ₀ ε := by unfold lineMass; ring

/-- **Smooth `λ_S` sums.** -/
theorem exists_norm_tsum_lamS_sub_le (hRH : RiemannHypothesis) (hα0 : 0 < α) (hα : α < 1)
    {ε : ℝ} (hε : 0 < ε) (hεα : ε < α / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : ℝ → ℂ) (a b : ℝ), IsTest g a b → ∀ M : ℝ, 0 < M →
      ‖∑' n, D.lamS n * g (n / M) - D.lamNum α * mellin g (α : ℂ) * (M : ℂ) ^ (α : ℂ)‖ ≤
        K * M ^ (α / 2 + ε) * lineMass g (α / 2 + ε) ε := by
  set σ₀ : ℝ := α / 2 + ε with hσ₀
  obtain ⟨c, T, hc, hT1, hL⟩ := D.exists_norm_lamS_cont_le hRH hα0 hα (δ := ε) hε hεα
    (κ := ε / 2) (by linarith)
  rw [show 2 * (ε / 2) = ε by ring] at hL
  have hcont : ∀ s : ℂ, α / 2 < s.re → s ≠ (α : ℂ) →
      ContinuousAt (fun s => D.lamNum α / (s - α) + dslope D.lamNum (α : ℂ) s) s := by
    intro s hs hsα
    have h1 : ContinuousAt (fun s : ℂ => D.lamNum α / (s - α)) s :=
      continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hsα)
    exact h1.add ((D.differentiableOn_dslope_lamNum hα0 hα).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)).continuousAt
  have hne : ∀ s : ℂ, 1 ≤ |s.im| → s ≠ (α : ℂ) := fun s hs h => by
    rw [h] at hs; simp at hs; linarith
  obtain ⟨K, hK⟩ := exists_strip_bound
    (G := fun s => D.lamNum α / (s - α) + dslope D.lamNum (α : ℂ) s)
    (σ₀ := σ₀) (σ₁ := 3 / 2) (fun s h1 _ h3 => hcont s (by linarith) (hne s h3)) hε.le hL
  have hlinecont : Continuous fun t : ℝ =>
      ‖D.lamNum α / ((σ₀ : ℂ) + t * I - α) + dslope D.lamNum (α : ℂ) ((σ₀ : ℂ) + t * I)‖ := by
    refine (continuous_iff_continuousAt.mpr fun t => ?_).norm
    have hs : ((σ₀ : ℂ) + t * I) ≠ (α : ℂ) := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact (hcont _ (by simp; linarith) hs).comp (f := fun t : ℝ => (σ₀ : ℂ) + t * I)
      (by fun_prop)
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_bound_line hlinecont hε.le (K := K) (T := 1) fun t ht => by
    have h := hK ((σ₀ : ℂ) + t * I) (by simp [hσ₀]) (by simp; linarith) (by simpa using ht)
    simpa using h
  refine ⟨K₀ / (2 * π), by positivity, fun g a b hg M hM => ?_⟩
  have h := norm_tsum_sub_residue_le hg D.lamS D.lamS_zero D.norm_lamS_le (A := D.lamNum α)
    (ρ := (α : ℂ)) (G₀ := dslope D.lamNum (α : ℂ)) (a₀ := α / 2) (σ₀ := σ₀) (by linarith)
    (by simp; linarith) (by simp; linarith) (D.differentiableOn_dslope_lamNum hα0 hα)
    (fun s hs => D.LSeries_lamS_eq_residue hα0 hα hs) hε.le (by linarith) (K := K)
    (fun s h1 h2 h3 => hK s h1 h2 h3) (K₀ := K₀) hK₀ hM
  calc _ ≤ _ := h
    _ = K₀ / (2 * π) * M ^ σ₀ * lineMass g σ₀ ε := by unfold lineMass; ring

/-! ## The block -/

theorem bumpC_mul_fourier (M x : ℝ) (hM : 0 < M) (h : ℤ) {n : ℕ} (hn : 0 < n) :
    bumpC (n / M) * fourier h ((x / n : ℝ) : UnitAddCircle) = twist bumpC (h * x / M) (n / M) := by
  rw [twist, fourier_coe_apply]
  congr 1
  congr 1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  field_simp

theorem tsum_twist_eq_sum (c : ℕ → ℂ) (hc0 : c 0 = 0) (M : ℝ) (hM : 0 < M) (κ : ℝ) :
    ∑' n, c n * twist bumpC κ (n / M) =
      ∑ m ∈ Finset.Icc 1 ⌊4 * M⌋₊, c m * twist bumpC κ (m / M) := by
  refine tsum_eq_sum fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [hc0, zero_mul]
  · have hn4 : 4 < (n : ℝ) / M := by
      rw [lt_div_iff₀ hM]
      have : ¬ n ≤ ⌊4 * M⌋₊ := fun h => hn (Finset.mem_Icc.mpr ⟨hpos, h⟩)
      push Not at this
      exact (Nat.lt_of_floor_lt this)
    simp [twist, bumpC, bump_eq_zero_of_ge hn4.le]

/-- The frequency sums of a block are twisted smooth sums. -/
theorem sum_mul_fourier_eq_tsum (c : ℕ → ℂ) (hc0 : c 0 = 0) (M x : ℝ) (hM : 0 < M) (h : ℤ) :
    ∑ m ∈ Finset.Icc 1 ⌊4 * M⌋₊, c m * bumpC (m / M) * fourier h ((x / m : ℝ) : UnitAddCircle) =
      ∑' n, c n * twist bumpC (h * x / M) (n / M) := by
  rw [tsum_twist_eq_sum _ hc0 M hM]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_assoc, bumpC_mul_fourier M x hM h (Finset.mem_Icc.mp hm).1]

theorem two_rpow_bound {p y : ℝ} (hp : 0 ≤ p) (hy : 1 ≤ y) {h : ℤ} (hh : h ≠ 0) :
    (1 + |(h : ℝ)| * y) ^ p ≤ 2 ^ p * y ^ p * |(h : ℝ)| ^ p := by
  have hh1 : 1 ≤ |(h : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
  rw [← Real.mul_rpow (by norm_num) (by positivity), ← Real.mul_rpow (by positivity)
    (abs_nonneg _)]
  exact Real.rpow_le_rpow (by positivity) (by nlinarith) hp

/-- One frequency of the smooth part. -/
theorem smooth_term_le {A0 K CF ε Δ y Mσ a S : ℝ} (hA0 : 0 ≤ A0) (hK : 0 ≤ K) (hCF : 0 ≤ CF)
    (hΔ : 0 < Δ) (hy : 1 ≤ y) (hMσ : 0 ≤ Mσ) (hε : 0 < ε) (hε4 : ε < 1 / 4) {h : ℤ}
    (ha : a ≤ A0 * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹ / |(h : ℝ)|) (hS0 : 0 ≤ S)
    (hS : S ≤ K * Mσ * (CF * (1 + |(h : ℝ)| * y) ^ (1 / 2 + ε))) :
    a * S ≤ A0 * K * CF * 2 ^ (1 / 2 + ε) * Mσ * y ^ (1 / 2 + ε) * Δ ^ (-(1 / 2 + 2 * ε)) *
      |(h : ℝ)| ^ (-(1 + ε)) := by
  rcases eq_or_ne h 0 with rfl | hh
  · have : a ≤ 0 := by simpa using ha
    simp only [Int.cast_zero, abs_zero, Real.zero_rpow (show -(1 + ε) ≠ 0 by linarith), mul_zero]
    exact mul_nonpos_of_nonpos_of_nonneg this hS0
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  have habs : 0 < |(h : ℝ)| := abs_pos.mpr hh'
  have hq := inv_one_add_sq_mul_rpow_le hΔ (q := 1 / 2 + ε - 1) (s := 1 + ε) (by linarith)
    (by linarith) hh'
  rw [show -(1 / 2 + ε - 1 + (1 + ε)) = -(1 / 2 + 2 * ε) by ring] at hq
  have hS' : S ≤ K * Mσ * (CF * (2 ^ (1 / 2 + ε) * y ^ (1 / 2 + ε) * |(h : ℝ)| ^ (1 / 2 + ε))) := by
    refine hS.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCF) (by positivity))
    exact two_rpow_bound (by linarith) hy hh
  have hw : 0 ≤ A0 * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹ / |(h : ℝ)| := by positivity
  calc a * S ≤ (A0 * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹ / |(h : ℝ)|) *
        (K * Mσ * (CF * (2 ^ (1 / 2 + ε) * y ^ (1 / 2 + ε) * |(h : ℝ)| ^ (1 / 2 + ε)))) := by
        rcases le_or_gt 0 a with ha0 | ha0
        · exact mul_le_mul ha hS' hS0 hw
        · calc a * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0.le hS0
            _ ≤ _ := by positivity
    _ = A0 * K * CF * 2 ^ (1 / 2 + ε) * Mσ * y ^ (1 / 2 + ε) *
          ((1 + ((h : ℝ) * Δ) ^ 2)⁻¹ * |(h : ℝ)| ^ (1 / 2 + ε - 1)) := by
        rw [Real.rpow_sub habs, Real.rpow_one]
        field_simp
    _ ≤ A0 * K * CF * 2 ^ (1 / 2 + ε) * Mσ * y ^ (1 / 2 + ε) *
          (Δ ^ (-(1 / 2 + 2 * ε)) * |(h : ℝ)| ^ (-(1 + ε))) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring

/-- One frequency of the majorant. -/
theorem majorant_term_le {A0 L Cr K CF ε Δ y Mα Mσ k S : ℝ} (hA0 : 0 ≤ A0) (hL : 0 ≤ L)
    (hCr : 0 ≤ Cr) (hK : 0 ≤ K) (hCF : 0 ≤ CF) (hΔ : 0 < Δ) (hy : 1 ≤ y) (hMα : 0 ≤ Mα)
    (hMσ : 0 ≤ Mσ) (hε : 0 < ε) (hε4 : ε < 1 / 4) {h : ℤ}
    (hk : k ≤ A0 * Δ * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹) (hS0 : 0 ≤ S)
    (hS : S ≤ L * (Cr / (1 + |(h : ℝ)| * y)) * Mα +
      K * Mσ * (CF * (1 + |(h : ℝ)| * y) ^ (1 / 2 + ε))) :
    k * S ≤ (A0 * L * Cr * Mα * Δ ^ (1 - ε) +
      A0 * K * CF * 2 ^ (1 / 2 + ε) * Mσ * y ^ (1 / 2 + ε) * Δ ^ (-(1 / 2 + 2 * ε))) *
        |(h : ℝ)| ^ (-(1 + ε)) + (if h = 0 then A0 * Δ * (L * Cr * Mα + K * Mσ * CF) else 0) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp only [Int.cast_zero, abs_zero, Real.zero_rpow (show -(1 + ε) ≠ 0 by linarith),
      mul_zero, if_true, zero_add]
    simp only [Int.cast_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero, inv_one, mul_one, abs_zero, div_one, Real.one_rpow] at hk hS
    exact mul_le_mul hk hS hS0 (by positivity)
  simp only [hh, if_false, add_zero]
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  have habs : 0 < |(h : ℝ)| := abs_pos.mpr hh'
  have hh1 : 1 ≤ |(h : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
  have hq1 := inv_one_add_sq_mul_rpow_le hΔ (q := -1) (s := 1 + ε) (by linarith) (by linarith) hh'
  have hq2 := inv_one_add_sq_mul_rpow_le hΔ (q := 1 / 2 + ε) (s := 1 + ε) (by linarith)
    (by linarith) hh'
  rw [show -(-1 + (1 + ε)) = -ε by ring] at hq1
  have he2 : Δ * Δ ^ (-(1 / 2 + ε + (1 + ε))) = Δ ^ (-(1 / 2 + 2 * ε)) := by
    rw [← Real.rpow_one_add' hΔ.le (by linarith)]; ring_nf
  have he3 : Δ * Δ ^ (-ε) = Δ ^ (1 - ε) := by
    rw [← Real.rpow_one_add' hΔ.le (by linarith)]; ring_nf
  have hinvc : Cr / (1 + |(h : ℝ)| * y) ≤ Cr * |(h : ℝ)| ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ habs (by nlinarith)) hCr
  have hS' : S ≤ L * (Cr * |(h : ℝ)| ^ (-1 : ℝ)) * Mα +
      K * Mσ * (CF * (2 ^ (1 / 2 + ε) * y ^ (1 / 2 + ε) * |(h : ℝ)| ^ (1 / 2 + ε))) := by
    refine hS.trans (add_le_add (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinvc hL) hMα) (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ?_ hCF) (by positivity)))
    exact two_rpow_bound (by linarith) hy hh
  set w := (1 + ((h : ℝ) * Δ) ^ 2)⁻¹ with hw
  have hw0 : 0 ≤ w := by positivity
  calc k * S ≤ (A0 * Δ * w) * (L * (Cr * |(h : ℝ)| ^ (-1 : ℝ)) * Mα +
        K * Mσ * (CF * (2 ^ (1 / 2 + ε) * y ^ (1 / 2 + ε) * |(h : ℝ)| ^ (1 / 2 + ε)))) :=
        mul_le_mul hk hS' hS0 (by positivity)
    _ = A0 * L * Cr * Mα * Δ * (w * |(h : ℝ)| ^ (-1 : ℝ)) +
          A0 * K * CF * 2 ^ (1 / 2 + ε) * Mσ * y ^ (1 / 2 + ε) * Δ *
            (w * |(h : ℝ)| ^ (1 / 2 + ε)) := by ring
    _ ≤ A0 * L * Cr * Mα * Δ * (Δ ^ (-ε) * |(h : ℝ)| ^ (-(1 + ε))) +
          A0 * K * CF * 2 ^ (1 / 2 + ε) * Mσ * y ^ (1 / 2 + ε) * Δ *
            (Δ ^ (-(1 / 2 + ε + (1 + ε))) * |(h : ℝ)| ^ (-(1 + ε))) :=
        add_le_add (mul_le_mul_of_nonneg_left hq1 (by positivity))
          (mul_le_mul_of_nonneg_left hq2 (by positivity))
    _ = (A0 * L * Cr * Mα * (Δ * Δ ^ (-ε)) +
          A0 * K * CF * 2 ^ (1 / 2 + ε) * Mσ * y ^ (1 / 2 + ε) *
            (Δ * Δ ^ (-(1 / 2 + ε + (1 + ε))))) * |(h : ℝ)| ^ (-(1 + ε)) := by ring
    _ = _ := by rw [he2, he3]

/-- The twisted `μ_S` sum at frequency `h`. -/
theorem norm_tsum_mobS_twist_le {K₁ CF σ₀ ε : ℝ} (hK₁0 : 0 ≤ K₁)
    (hK₁ : ∀ (g : ℝ → ℂ) (a b : ℝ), IsTest g a b → ∀ M : ℝ, 0 < M →
      ‖∑' n, D.mobS n * g (n / M)‖ ≤ K₁ * M ^ σ₀ * lineMass g σ₀ ε)
    (hCF : ∀ c : ℝ, lineMass (twist bumpC c) σ₀ ε ≤ CF * (1 + |c|) ^ (ε + 1 / 2))
    {M x : ℝ} (hM : 0 < M) (hx : 0 ≤ x) (h : ℤ) :
    ‖∑' n, D.mobS n * twist bumpC (h * x / M) (n / M)‖ ≤
      K₁ * M ^ σ₀ * (CF * (1 + |(h : ℝ)| * (x / M)) ^ (1 / 2 + ε)) := by
  have hc : |(h : ℝ) * x / M| = |(h : ℝ)| * (x / M) := by
    rw [mul_div_assoc, abs_mul, abs_of_nonneg (div_nonneg hx hM.le)]
  refine (hK₁ _ 1 4 (isTest_bumpC.twist _) M hM).trans ?_
  have := hCF ((h : ℝ) * x / M)
  rw [hc, add_comm ε (1 / 2)] at this
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- The twisted `λ_S` sum at frequency `h`. -/
theorem norm_tsum_lamS_twist_le {K₂ CF Cr σ₀ ε : ℝ} (hK₂0 : 0 ≤ K₂)
    (hK₂ : ∀ (g : ℝ → ℂ) (a b : ℝ), IsTest g a b → ∀ M : ℝ, 0 < M →
      ‖∑' n, D.lamS n * g (n / M) - D.lamNum α * mellin g (α : ℂ) * (M : ℂ) ^ (α : ℂ)‖ ≤
        K₂ * M ^ σ₀ * lineMass g σ₀ ε)
    (hCF : ∀ c : ℝ, lineMass (twist bumpC c) σ₀ ε ≤ CF * (1 + |c|) ^ (ε + 1 / 2))
    (hCr : ∀ c : ℝ, ‖mellin (twist bumpC c) (α : ℂ)‖ ≤ Cr / (1 + |c|))
    {M x : ℝ} (hM : 0 < M) (hx : 0 ≤ x) (h : ℤ) :
    ‖∑' n, D.lamS n * twist bumpC (h * x / M) (n / M)‖ ≤
      ‖D.lamNum α‖ * (Cr / (1 + |(h : ℝ)| * (x / M))) * M ^ α +
        K₂ * M ^ σ₀ * (CF * (1 + |(h : ℝ)| * (x / M)) ^ (1 / 2 + ε)) := by
  have hc : |(h : ℝ) * x / M| = |(h : ℝ)| * (x / M) := by
    rw [mul_div_assoc, abs_mul, abs_of_nonneg (div_nonneg hx hM.le)]
  have h1 := hK₂ _ 1 4 (isTest_bumpC.twist ((h : ℝ) * x / M)) M hM
  have h2 := hCF ((h : ℝ) * x / M)
  rw [hc, add_comm ε (1 / 2)] at h2
  have h3 := hCr ((h : ℝ) * x / M)
  rw [hc] at h3
  have hres : ‖D.lamNum α * mellin (twist bumpC ((h : ℝ) * x / M)) (α : ℂ) * (M : ℂ) ^ (α : ℂ)‖ ≤
      ‖D.lamNum α‖ * (Cr / (1 + |(h : ℝ)| * (x / M))) * M ^ α := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hM, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
      (by positivity)
  calc _ ≤ ‖D.lamNum α * mellin (twist bumpC ((h : ℝ) * x / M)) (α : ℂ) * (M : ℂ) ^ (α : ℂ)‖ +
        ‖∑' n, D.lamS n * twist bumpC (h * x / M) (n / M) -
          D.lamNum α * mellin (twist bumpC ((h : ℝ) * x / M)) (α : ℂ) * (M : ℂ) ^ (α : ℂ)‖ :=
        norm_le_norm_add_norm_sub' _ _
    _ ≤ _ := add_le_add hres (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))

/-- **The block bound.** -/
theorem exists_norm_block_le (hRH : RiemannHypothesis) (hα1 : 1 / 2 < α) (hα : α < 1) {ε : ℝ}
    (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M x Δ : ℝ, 1 ≤ M → M ≤ x → 0 < Δ → Δ ≤ 1 →
      ‖∑ m ∈ Finset.Icc 1 ⌊4 * M⌋₊, D.mobS m * bumpC (m / M) * (saw (x / m) : ℂ)‖ ≤
        K * (M ^ (α / 2 + ε) * (x / M) ^ (1 / 2 + ε) * Δ ^ (-(1 / 2 + 2 * ε)) +
          Δ ^ (1 - ε) * M ^ α) := by
  have hα0 : 0 < α := by linarith
  have hεα : ε < α / 2 := by linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ := D.exists_norm_tsum_mobS_le hRH hα0 hα hε hεα
  obtain ⟨K₂, hK₂0, hK₂⟩ := D.exists_norm_tsum_lamS_sub_le hRH hα0 hα hε hεα
  obtain ⟨CF, hCF0, hCF⟩ := exists_integral_twist_le isTest_bumpC (σ := α / 2 + ε) (κ := ε)
    (by positivity) hε.le (by linarith)
  obtain ⟨Cr, hCr0, hCr⟩ := exists_norm_mellin_twist_le isTest_bumpC α
  obtain ⟨A0, hA0, hdec⟩ := exists_saw_decomposition
  have hZs : Summable fun h : ℤ => |(h : ℝ)| ^ (-(1 + ε)) := summable_abs_int_rpow (by linarith)
  set Z := zetaAbs (1 + ε) with hZ
  have hZ0 : 0 ≤ Z := zetaAbs_nonneg _
  set L := ‖D.lamNum α‖ with hL
  have hL0 : 0 ≤ L := norm_nonneg _
  set c₁ : ℝ := (A0 * K₁ * CF * 2 ^ (1 / 2 + ε) + A0 * K₂ * CF * 2 ^ (1 / 2 + ε)) * Z with hc₁
  set c₂ : ℝ := A0 * L * Cr * Z with hc₂
  set c₃ : ℝ := A0 * (L * Cr + K₂ * CF) with hc₃
  refine ⟨c₁ + c₂ + c₃, by positivity, ?_⟩
  intro M x Δ hM hMx hΔ hΔ1
  have hM0 : 0 < M := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hy1 : 1 ≤ x / M := by rw [le_div_iff₀ hM0]; linarith
  obtain ⟨a, k, haS, hkS, ha, hk, hmain⟩ := hdec Δ hΔ
  have hβ : ∀ m, ‖D.mobS m * bumpC (m / M)‖ ≤ D.lamR m * bump (m / M) := fun m => by
    rw [norm_mul, bumpC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bump_nonneg _)]
    exact mul_le_mul_of_nonneg_right (D.norm_mobS_le_lamR m) (bump_nonneg _)
  have key := hmain (Finset.Icc 1 ⌊4 * M⌋₊) (fun m : ℕ => x / m)
    (fun m => D.mobS m * bumpC (m / M)) (fun m => D.lamR m * bump (m / M)) hβ
  have hlamc : ∀ m : ℕ, ((D.lamR m * bump (m / M) : ℝ) : ℂ) = D.lamS m * bumpC (m / M) := by
    intro m; simp [lamS, bumpC]
  set X₁ : ℝ := M ^ (α / 2 + ε) * (x / M) ^ (1 / 2 + ε) * Δ ^ (-(1 / 2 + 2 * ε)) with hX₁
  set X₂ : ℝ := Δ ^ (1 - ε) * M ^ α with hX₂
  set G₀ : ℝ := A0 * Δ * (L * Cr * M ^ α + K₂ * M ^ (α / 2 + ε) * CF) with hG₀
  set B₁ : ℝ := A0 * K₁ * CF * 2 ^ (1 / 2 + ε) * X₁ with hB₁
  set B₂ : ℝ := A0 * L * Cr * M ^ α * Δ ^ (1 - ε) + A0 * K₂ * CF * 2 ^ (1 / 2 + ε) * X₁ with hB₂
  have hT1 : ∀ h : ℤ, ‖a h‖ * ‖∑ i ∈ Finset.Icc 1 ⌊4 * M⌋₊,
      (fun m => D.mobS m * bumpC (m / M)) i *
        fourier h (((fun m : ℕ => x / m) i : ℝ) : UnitAddCircle)‖ ≤ B₁ * |(h : ℝ)| ^ (-(1 + ε)) := by
    intro h
    have e : ∑ i ∈ Finset.Icc 1 ⌊4 * M⌋₊, (fun m => D.mobS m * bumpC (m / M)) i *
        fourier h (((fun m : ℕ => x / m) i : ℝ) : UnitAddCircle) =
        ∑' n, D.mobS n * twist bumpC (h * x / M) (n / M) :=
      sum_mul_fourier_eq_tsum _ D.mobS_zero M x hM0 h
    rw [e]
    refine (smooth_term_le hA0 hK₁0 hCF0 hΔ hy1 (by positivity) hε hε4 (ha h) (norm_nonneg _)
      (D.norm_tsum_mobS_twist_le hK₁0 hK₁ hCF hM0 hx0 h)).trans (le_of_eq ?_)
    rw [hB₁, hX₁]; ring
  have hT2 : ∀ h : ℤ, ‖k h‖ * ‖∑ i ∈ Finset.Icc 1 ⌊4 * M⌋₊,
      (((fun m => D.lamR m * bump (m / M)) i : ℝ) : ℂ) *
        fourier h (((fun m : ℕ => x / m) i : ℝ) : UnitAddCircle)‖ ≤
      B₂ * |(h : ℝ)| ^ (-(1 + ε)) + (if h = 0 then G₀ else 0) := by
    intro h
    have e : ∑ i ∈ Finset.Icc 1 ⌊4 * M⌋₊, (((fun m => D.lamR m * bump (m / M)) i : ℝ) : ℂ) *
        fourier h (((fun m : ℕ => x / m) i : ℝ) : UnitAddCircle) =
        ∑' n, D.lamS n * twist bumpC (h * x / M) (n / M) := by
      rw [← sum_mul_fourier_eq_tsum _ D.lamS_zero M x hM0 h]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [hlamc]
    rw [e]
    refine (majorant_term_le hA0 hL0 hCr0 hK₂0 hCF0 hΔ hy1 (by positivity) (by positivity) hε hε4
      (hk h) (norm_nonneg _) (D.norm_tsum_lamS_twist_le hK₂0 hK₂ hCF hCr hM0 hx0 h)).trans
      (le_of_eq ?_)
    rw [hB₂, hX₁, hG₀]; ring
  have hS1 := summable_mul_norm_sum (Finset.Icc 1 ⌊4 * M⌋₊)
    (fun m => D.mobS m * bumpC (m / M)) (fun m : ℕ => x / m) haS
  have hS2 := summable_mul_norm_sum (Finset.Icc 1 ⌊4 * M⌋₊)
    (fun m => ((D.lamR m * bump (m / M) : ℝ) : ℂ)) (fun m : ℕ => x / m) hkS
  have hfin : Summable fun h : ℤ => (if h = 0 then G₀ else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun b hb => by
      rw [Finset.mem_singleton] at hb; simp [hb]
  have hsum1 := hS1.tsum_le_tsum hT1 (hZs.mul_left B₁)
  rw [tsum_mul_left] at hsum1
  have hsum2 := hS2.tsum_le_tsum hT2 ((hZs.mul_left B₂).add hfin)
  rw [(hZs.mul_left _).tsum_add hfin, tsum_mul_left, tsum_ite_eq] at hsum2
  have hMσ : M ^ (α / 2 + ε) ≤ M ^ α := Real.rpow_le_rpow_of_exponent_le hM (by linarith)
  have hΔε : Δ ≤ Δ ^ (1 - ε) := by
    calc Δ = Δ ^ (1 : ℝ) := (Real.rpow_one Δ).symm
      _ ≤ Δ ^ (1 - ε) := Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1 (by linarith)
  have hG₀le : G₀ ≤ c₃ * X₂ := by
    have h1 : L * Cr * M ^ α + K₂ * M ^ (α / 2 + ε) * CF ≤ (L * Cr + K₂ * CF) * M ^ α := by
      have : K₂ * M ^ (α / 2 + ε) * CF ≤ K₂ * M ^ α * CF :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMσ hK₂0) hCF0
      nlinarith
    have h2 : 0 ≤ L * Cr * M ^ α + K₂ * M ^ (α / 2 + ε) * CF := by positivity
    calc G₀ = A0 * Δ * (L * Cr * M ^ α + K₂ * M ^ (α / 2 + ε) * CF) := rfl
      _ ≤ A0 * Δ ^ (1 - ε) * ((L * Cr + K₂ * CF) * M ^ α) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΔε hA0) h1 h2 (by positivity)
      _ = c₃ * X₂ := by rw [hc₃, hX₂]; ring
  have hX₁0 : 0 ≤ X₁ := by positivity
  have hX₂0 : 0 ≤ X₂ := by positivity
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hc₃0 : 0 ≤ c₃ := by positivity
  have hfinal : B₁ * Z + (B₂ * Z + G₀) ≤ (c₁ + c₂ + c₃) * (X₁ + X₂) := by
    have e1 : B₁ * Z + B₂ * Z = c₁ * X₁ + c₂ * X₂ := by rw [hB₁, hB₂, hc₁, hc₂, hX₂]; ring
    have e2 : (c₁ + c₂ + c₃) * (X₁ + X₂) = c₁ * X₁ + c₂ * X₂ + c₃ * X₂ +
        (c₁ * X₂ + c₂ * X₁ + c₃ * X₁) := by ring
    have h1 := mul_nonneg hc₁0 hX₂0
    have h2 := mul_nonneg hc₂0 hX₁0
    have h3 := mul_nonneg hc₃0 hX₁0
    linarith
  calc _ ≤ _ := key
    _ ≤ B₁ * Z + (B₂ * Z + G₀) := add_le_add hsum1 hsum2
    _ ≤ _ := hfinal

end DeletionData

end RHTower.BeurlingDeletion
