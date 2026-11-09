import GaloisForLFunctions.SurfaceOfSpecZ.PrimeWindowsDecideSeparatedConfigurations

/-!
# Only deep ordinates need separation

The window theorem for separated ordinates needs separation only among the exponents deeper than
the level tested. Let the exponents `z = ρ − ½` (zeros and conjugates) of depth `Re z > c ≥ 0` have
pairwise ordinate gaps `≥ δ` (`DeepSeparatedOrdinates`); the zeros of depth `≤ c`, on the line in
particular, are arbitrary. Then a lower bound `−K e^{su}`, `s ≥ c`, on windows of length `80/δ`
beyond every bound puts every zero in `Re ρ ≤ ½ + s`
(`re_le_of_bddBelow_exp_windows_of_deepSeparated`), and prime windows `[x, e^{80/δ + 1} x]` with a
bounded trace give `Re ρ ≤ ½ + c` (`re_le_of_bddBelow_prime_windows_of_deepSeparated`).

In Landau's inequality at the dominant exponent `z₀` (`norm_le_of_window_lower`), a deep exponent
leaks through the resolution of the window, `O(1/(δℓ)²)` in total
(`sum_term_deep_le`), while an exponent of depth `≤ c` leaks at most its weight
`|D_z| e^{cu₀} e^{ℓ}` (`sum_term_shallow_le`), negligible against the weight `≥ e^{(c+ε)u₀}` of `z₀`.

For `ζ`: if the zeros off the line have `δ`-separated ordinates, the Riemann hypothesis follows
from a bounded trace at the primes of windows `[x, e^{80/δ + 1} x]` along any sequence of scales
(`riemannHypothesis_of_prime_windows_of_offLine_separated`).
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **Separation of the deep ordinates.** Distinct exponents of depth `> c` have ordinates at
least `δ` apart. -/
def DeepSeparatedOrdinates (Z : ZeroConfig) (c δ : ℝ) : Prop :=
  ∀ z ∈ zeroExps Z, ∀ z' ∈ zeroExps Z, c < z.re → c < z'.re → z' ≠ z → δ ≤ |z.im - z'.im|

variable {Z : ZeroConfig}

/-- **Leakage of the deep exponents.** For `q` of depth `x₀` whose ordinate is `g` away from the
ordinates of the deep exponents of `S` other than `q`, which are `g`-separated, the deep exponents
other than `q` leak at most `B · 4/ℓ² · 8/g²` in the test at `q`. -/
theorem sum_term_deep_le {S : Finset ℂ} {c g : ℝ} (hg : 0 < g) {q : ℂ} {u₀ ℓ B : ℝ} (hℓ : 0 < ℓ)
    (hsep : ∀ z ∈ S, ∀ z' ∈ S, c < z.re → c < z'.re → z' ≠ z → g ≤ |z.im - z'.im|)
    (hq : ∀ z ∈ S, c < z.re → z ≠ q → g ≤ |z.im - q.im|)
    (hdrift : ∀ z, expWeight Z u₀ z * Real.exp (|z.re - q.re| * ℓ) ≤ B) :
    ∑ z ∈ (S.filter (fun z => c < z.re)).erase q,
        ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) * boxAvg ℓ (z - q) ^ 2‖ ≤
      B * (4 / ℓ ^ 2) * (8 / g ^ 2) := by
  classical
  have hB : 0 ≤ B :=
    le_trans (mul_nonneg (expWeight_nonneg _ _) (Real.exp_pos _).le) (hdrift 0)
  set Sd := (S.filter (fun z => c < z.re)).erase q with hSd
  have hmem : ∀ z ∈ Sd, z ∈ S ∧ c < z.re ∧ z ≠ q := fun z hz => by
    have h1 := Finset.mem_of_mem_erase hz
    exact ⟨(Finset.mem_filter.mp h1).1, (Finset.mem_filter.mp h1).2, Finset.ne_of_mem_erase hz⟩
  have hne : ∀ z ∈ Sd, z.im ≠ q.im := fun z hz h => by
    obtain ⟨h1, h2, h3⟩ := hmem z hz
    have := hq z h1 h2 h3
    rw [h, sub_self, abs_zero] at this
    linarith
  have hterm : ∀ z ∈ Sd, ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) * boxAvg ℓ (z - q) ^ 2‖ ≤
      B * (4 / ℓ ^ 2) * (1 / (z.im - q.im) ^ 2) := fun z hz => by
    have hw : (z - q).im ≠ 0 := by rw [Complex.sub_im]; exact sub_ne_zero.mpr (hne z hz)
    have h := norm_term_le (Z := Z) (w := z - q) (x₀ := q.re) hℓ hw (by simp) (hdrift z)
    rwa [Complex.sub_im] at h
  have hcount := sum_inv_sq_im_le (S := Sd) (t := q.im) hg
    (fun z hz z' hz' h1 _ => hsep z (hmem z hz).1 z' (hmem z' hz').1 (hmem z hz).2.1
      (hmem z' hz').2.1 h1)
    (fun z hz _ => hq z (hmem z hz).1 (hmem z hz).2.1 (hmem z hz).2.2)
  rw [Finset.filter_true_of_mem hne] at hcount
  calc _ ≤ ∑ z ∈ Sd, B * (4 / ℓ ^ 2) * (1 / (z.im - q.im) ^ 2) := Finset.sum_le_sum hterm
    _ = B * (4 / ℓ ^ 2) * ∑ z ∈ Sd, 1 / (z.im - q.im) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ B * (4 / ℓ ^ 2) * (8 / g ^ 2) := mul_le_mul_of_nonneg_left hcount (by positivity)

/-- **Leakage of the shallow exponents.** The exponents of depth `≤ c` contribute at most
`(Σ |D_z|) e^{ℓ} e^{cu₀}` to any test of depth `x₀`, `|x₀| ≤ ½`, at `u₀ ≥ 0`. -/
theorem sum_term_shallow_le (hZ : TemperedConfig Z) {S : Finset ℂ} (hS : ∀ z ∈ S, z ∈ zeroExps Z)
    {c u₀ ℓ : ℝ} (hu₀ : 0 ≤ u₀) (hℓ : 0 < ℓ) {q : ℂ} (hq : |q.re| ≤ 1 / 2) :
    ∑ z ∈ S.filter (fun z => ¬ c < z.re),
        ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) * boxAvg ℓ (z - q) ^ 2‖ ≤
      (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * Real.exp ℓ * Real.exp (c * u₀) := by
  have hs := summable_norm_evenCoeff_spline hZ
  have hterm : ∀ z ∈ S.filter (fun z => ¬ c < z.re),
      ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) * boxAvg ℓ (z - q) ^ 2‖ ≤
      ‖evenCoeff Z (boxSpline 1 3) z‖ * (Real.exp ℓ * Real.exp (c * u₀)) := fun z hz => by
    obtain ⟨hzS, hzc⟩ := Finset.mem_filter.mp hz
    push Not at hzc
    rw [norm_term_eq, norm_pow]
    have hσ := norm_boxAvg_sq_le_exp hℓ (z - q)
    have hre : |(z - q).re| ≤ 1 := by
      rw [Complex.sub_re]
      have h1 := abs_re_le_of_mem_zeroExps (hS z hzS)
      exact (abs_sub _ _).trans (by linarith)
    have h1 : ‖boxAvg ℓ (z - q)‖ ^ 2 ≤ Real.exp ℓ :=
      hσ.trans (Real.exp_le_exp.mpr (by nlinarith))
    have h2 : Real.exp (z.re * u₀) ≤ Real.exp (c * u₀) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzc hu₀)
    unfold expWeight
    calc ‖evenCoeff Z (boxSpline 1 3) z‖ * Real.exp (z.re * u₀) * ‖boxAvg ℓ (z - q)‖ ^ 2
        ≤ ‖evenCoeff Z (boxSpline 1 3) z‖ * Real.exp (c * u₀) * Real.exp ℓ :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) h1 (by positivity)
            (by positivity)
      _ = _ := by ring
  calc _ ≤ ∑ z ∈ S.filter (fun z => ¬ c < z.re),
        ‖evenCoeff Z (boxSpline 1 3) z‖ * (Real.exp ℓ * Real.exp (c * u₀)) :=
        Finset.sum_le_sum hterm
    _ = (∑ z ∈ S.filter (fun z => ¬ c < z.re), ‖evenCoeff Z (boxSpline 1 3) z‖) *
        (Real.exp ℓ * Real.exp (c * u₀)) := by rw [Finset.sum_mul]
    _ ≤ (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * (Real.exp ℓ * Real.exp (c * u₀)) :=
        mul_le_mul_of_nonneg_right (hs.sum_le_tsum _ fun _ _ => norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Deep and shallow leakage together, for the sum over `S` without `q`. -/
theorem sum_term_erase_deep_le (hZ : TemperedConfig Z) {S : Finset ℂ}
    (hS : ∀ z ∈ S, z ∈ zeroExps Z) {c g : ℝ} (hg : 0 < g) {q : ℂ} {u₀ ℓ B : ℝ} (hu₀ : 0 ≤ u₀)
    (hℓ : 0 < ℓ) (hqre : |q.re| ≤ 1 / 2)
    (hsep : ∀ z ∈ S, ∀ z' ∈ S, c < z.re → c < z'.re → z' ≠ z → g ≤ |z.im - z'.im|)
    (hq : ∀ z ∈ S, c < z.re → z ≠ q → g ≤ |z.im - q.im|)
    (hdrift : ∀ z, expWeight Z u₀ z * Real.exp (|z.re - q.re| * ℓ) ≤ B) :
    ∑ z ∈ S.erase q, ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) * boxAvg ℓ (z - q) ^ 2‖ ≤
      B * (4 / ℓ ^ 2) * (8 / g ^ 2) +
        (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * Real.exp ℓ * Real.exp (c * u₀) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (S.erase q) (fun z => c < z.re)]
  have e1 : (S.erase q).filter (fun z => c < z.re) = (S.filter (fun z => c < z.re)).erase q := by
    ext z; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  have h1 := sum_term_deep_le (Z := Z) hg hℓ hsep hq hdrift
  have h2 := sum_term_shallow_le hZ hS (c := c) hu₀ hℓ hqre
  have hsub : (S.erase q).filter (fun z => ¬ c < z.re) ⊆ S.filter (fun z => ¬ c < z.re) :=
    Finset.filter_subset_filter _ (Finset.erase_subset _ _)
  have h3 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun z =>
    ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) * boxAvg ℓ (z - q) ^ 2‖)
    fun _ _ _ => norm_nonneg _
  rw [e1]
  linarith

/-- **The dominant weight on a window, deep separation.** As `expWeight_le_of_window_lower`, with
separation only above depth `c`: `M₀ ≤ 3K' e^{ℓ/2} + 3 (Σ|D_z|) e^{ℓ} e^{cu₀}`. -/
theorem expWeight_le_of_window_lower_deep (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {c δ : ℝ} (hδ : 0 < δ)
    (hsep : DeepSeparatedOrdinates Z c δ) {S : Finset ℂ} (hSE : ∀ z ∈ S, z ∈ zeroExps Z) {z₀ : ℂ}
    (hz₀S : z₀ ∈ S) (hz₀'S : conj z₀ ∈ S) (hz₀c : c < z₀.re) {u₀ ℓ K' B : ℝ} (hu₀ : 0 ≤ u₀)
    (hℓ0 : 0 < ℓ) (hK'0 : 0 ≤ K') (hδℓ : 40 ≤ δ * ℓ)
    (hdrift : ∀ z, expWeight Z u₀ z * Real.exp (|z.re - z₀.re| * ℓ) ≤ B)
    (hBle : B ≤ 3 * expWeight Z u₀ z₀)
    (hlow : ∀ v ∈ Icc (-ℓ) ℓ, -K' ≤
      (∑ z ∈ S, evenCoeff Z (boxSpline 1 3) z * cexp (z * ((u₀ + v : ℝ) : ℂ))).re) :
    expWeight Z u₀ z₀ ≤ 3 * K' * Real.exp (ℓ / 2) +
      3 * ((∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * Real.exp ℓ * Real.exp (c * u₀)) := by
  classical
  set M₀ := expWeight Z u₀ z₀ with hM₀
  set Sh := (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * Real.exp ℓ * Real.exp (c * u₀) with hSh
  have hz₀E := hSE z₀ hz₀S
  have hz₀'E := hSE _ hz₀'S
  have hx₀ := abs_re_le_of_mem_zeroExps hz₀E
  have hL := norm_le_of_window_lower (D := evenCoeff Z (boxSpline 1 3)) hz₀S hz₀'S
    (evenCoeff_conj Z z₀) hℓ0 hK'0 hlow
  have hM : ‖evenCoeff Z (boxSpline 1 3) z₀ * cexp (z₀ * u₀)‖ = M₀ := by
    rw [norm_mul, norm_cexp_mul_ofReal]; rfl
  rw [hM] at hL
  have hsepS : ∀ g : ℝ, g ≤ δ → ∀ z ∈ S, ∀ z' ∈ S, c < z.re → c < z'.re → z' ≠ z →
      g ≤ |z.im - z'.im| := fun g hg z hz z' hz' h1 h2 h3 =>
    hg.trans (hsep z (hSE z hz) z' (hSE z' hz') h1 h2 h3)
  -- zero frequency: `q = x₀` real, at distance `δ/2` from every deep ordinate
  have hreal : ∀ z ∈ S, c < z.re → z ≠ ((z₀.re : ℝ) : ℂ) → δ / 2 ≤ |z.im - ((z₀.re : ℝ) : ℂ).im| :=
    fun z hz hzc _ => by
      rw [Complex.ofReal_im, sub_zero]
      have him := im_ne_zero_of_mem_zeroExps hnoreal (hSE z hz)
      have h := hsep z (hSE z hz) (conj z) (conj_mem_zeroExps (hSE z hz)) hzc
        (by rw [Complex.conj_re]; exact hzc)
        (fun h => him (by have := congrArg Complex.im h; simp at this; linarith))
      rw [Complex.conj_im, sub_neg_eq_add, ← two_mul, abs_mul, abs_two] at h
      linarith
  have hnot : ((z₀.re : ℝ) : ℂ) ∉ S := fun h =>
    im_ne_zero_of_mem_zeroExps hnoreal (hSE _ h) (Complex.ofReal_im _)
  have h0 := sum_term_erase_deep_le hZ hSE (c := c) (half_pos hδ) (q := ((z₀.re : ℝ) : ℂ)) hu₀ hℓ0
    (by rw [Complex.ofReal_re]; exact hx₀) (hsepS _ (by linarith)) hreal
    (by simpa only [Complex.ofReal_re] using hdrift)
  rw [Finset.erase_eq_of_notMem hnot] at h0
  -- the dominant ordinates
  have hm := sum_term_erase_deep_le hZ hSE (c := c) hδ (q := z₀) hu₀ hℓ0 hx₀ (hsepS _ le_rfl)
    (fun z hz hzc hne => by
      have := hsep z₀ hz₀E z (hSE z hz) hz₀c hzc hne; rwa [abs_sub_comm] at this) hdrift
  have hp := sum_term_erase_deep_le hZ hSE (c := c) hδ (q := conj z₀) hu₀ hℓ0
    (by rw [Complex.conj_re]; exact hx₀) (hsepS _ le_rfl)
    (fun z hz hzc hne => by
      have := hsep (conj z₀) hz₀'E z (hSE z hz) (by rw [Complex.conj_re]; exact hz₀c) hzc hne
      rwa [abs_sub_comm] at this)
    (by simpa only [Complex.conj_re] using hdrift)
  have hM0 : 0 ≤ M₀ := expWeight_nonneg _ _
  have hB0 : 0 ≤ B := le_trans (mul_nonneg (expWeight_nonneg _ _) (Real.exp_pos _).le) (hdrift 0)
  have h1600 : (1600 : ℝ) ≤ (δ * ℓ) ^ 2 :=
    calc (1600 : ℝ) = 40 * 40 := by norm_num
      _ ≤ (δ * ℓ) * (δ * ℓ) := mul_le_mul hδℓ hδℓ (by norm_num) (by linarith)
      _ = (δ * ℓ) ^ 2 := by ring
  have hq0 : 4 / ℓ ^ 2 * (8 / (δ / 2) ^ 2) ≤ 2 / 25 := by
    rw [show 4 / ℓ ^ 2 * (8 / (δ / 2) ^ 2) = 128 / (δ * ℓ) ^ 2 by field_simp; ring]
    calc 128 / (δ * ℓ) ^ 2 ≤ 128 / 1600 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1600
      _ = 2 / 25 := by norm_num
  have hq1 : 4 / ℓ ^ 2 * (8 / δ ^ 2) ≤ 1 / 50 := by
    rw [show 4 / ℓ ^ 2 * (8 / δ ^ 2) = 32 / (δ * ℓ) ^ 2 by field_simp; ring]
    calc 32 / (δ * ℓ) ^ 2 ≤ 32 / 1600 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1600
      _ = 1 / 50 := by norm_num
  have t0 : B * (4 / ℓ ^ 2) * (8 / (δ / 2) ^ 2) ≤ B * (2 / 25) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hq0 hB0
  have t1 : B * (4 / ℓ ^ 2) * (8 / δ ^ 2) ≤ B * (1 / 50) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hq1 hB0
  have hKexp : 2 * K' * Real.exp (|z₀.re| * ℓ) ≤ 2 * K' * Real.exp (ℓ / 2) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    calc |z₀.re| * ℓ ≤ 1 / 2 * ℓ := mul_le_mul_of_nonneg_right hx₀ hℓ0.le
      _ = ℓ / 2 := by ring
  have hKE : 0 ≤ K' * Real.exp (ℓ / 2) := by positivity
  linarith

/-- **The windowed width law under deep separation.** Let the exponents of depth `> c ≥ 0` of a
tempered configuration without real zeros have `δ`-separated ordinates, and let some zero have real
part `> ½ + s`, `s ≥ c`. For every `K` and `ℓ ≥ 40/δ`, far enough out every window
`[u₀ − ℓ, u₀ + ℓ]` contains a scale with `2 Re S(u) < −K e^{su}`. -/
theorem exists_lt_exp_in_window_of_deepSeparated (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hsep : DeepSeparatedOrdinates Z c δ) {s : ℝ} (hs : c ≤ s) {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ Z.carrier)
    (hρ₁re : 1 / 2 + s < ρ₁.re) {ℓ : ℝ} (hℓ : 40 / δ ≤ ℓ) (K : ℝ) :
    ∃ U : ℝ, ∀ u₀, U ≤ u₀ → ∃ u ∈ Icc (u₀ - ℓ) (u₀ + ℓ),
      2 * (lagStructure Z (boxSpline 1 3) u).re < -(K * Real.exp (s * u)) := by
  have hs0 : 0 ≤ s := hc.trans hs
  set zp : ℂ := ρ₁ - 1 / 2 with hzpdef
  have hzp : evenCoeff Z (boxSpline 1 3) zp ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z (contDiff_boxSpline (r := 1) one_pos 2).continuous
      (hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3))
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ₁
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  have hzpre : s < zp.re := by simp [zp]; linarith
  obtain ⟨b, hb, hbsup⟩ := exists_depth_sup hzp
  have hbz : zp.re ≤ b := hb zp hzp
  have hδℓ : 40 ≤ δ * ℓ := by rw [div_le_iff₀ hδ] at hℓ; linarith
  have hℓ0 : 0 < ℓ := by
    by_contra h; push Not at h; nlinarith
  set η := min ((zp.re - s) / 2) (1 / ℓ) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  have hηb : η ≤ (zp.re - s) / 2 := min_le_left _ _
  have hηℓ : η * ℓ ≤ 1 :=
    calc η * ℓ ≤ 1 / ℓ * ℓ := mul_le_mul_of_nonneg_right (min_le_right _ _) hℓ0.le
      _ = 1 := by field_simp
  obtain ⟨z₁, hz₁, hz₁b⟩ := hbsup (η / 2) (half_pos hη)
  obtain ⟨U₁, hdom⟩ := le_re_of_dominant hZ hη hz₁ hz₁b
  set A := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  set C : ℝ := 3 * (|K| + 1) * Real.exp (s * ℓ) * Real.exp (ℓ / 2) + 3 * (A * Real.exp ℓ)
    with hCdef
  have hgrow : Tendsto (fun u => expWeight Z u zp * Real.exp (-(s * u))) atTop atTop := by
    have e : (fun u => expWeight Z u zp * Real.exp (-(s * u))) =
        fun u => ‖evenCoeff Z (boxSpline 1 3) zp‖ * Real.exp ((zp.re - s) * u) := by
      funext u; unfold expWeight; rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [e]
    exact Tendsto.const_mul_atTop (norm_pos_iff.mpr hzp)
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith)))
  obtain ⟨U₃, hU₃⟩ := Filter.eventually_atTop.mp (hgrow.eventually_gt_atTop C)
  refine ⟨max (U₁ + ℓ) (max U₃ ℓ), fun u₀ hu₀ => ?_⟩
  have hu₁ : U₁ + ℓ ≤ u₀ := (le_max_left _ _).trans hu₀
  have hu₃ : U₃ ≤ u₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hu₀
  have hu₄ : ℓ ≤ u₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans hu₀
  have hu00 : 0 ≤ u₀ := hℓ0.le.trans hu₄
  by_contra hall
  push Not at hall
  set E := Real.exp (s * (u₀ + ℓ)) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg hs0 (by linarith))
  have hall' : ∀ u ∈ Icc (u₀ - ℓ) (u₀ + ℓ),
      -(|K| * E) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := fun u hu => by
    have hKe : K * Real.exp (s * u) ≤ |K| * E :=
      mul_le_mul (le_abs_self K) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hs0))
        (Real.exp_pos _).le (abs_nonneg K)
    linarith [hall u hu]
  obtain ⟨z₀, hz₀, h₀⟩ := exists_dominant hZ u₀ hzp
  obtain ⟨zA, hzA, hA'⟩ := exists_dominant hZ (u₀ + ℓ) hzp
  obtain ⟨zB, -, hB⟩ := exists_dominant hZ (u₀ + -ℓ) hzp
  have hz₀b : b - η ≤ z₀.re := hdom u₀ (by linarith) z₀ h₀
  have hzBb : b - η ≤ zB.re := hdom (u₀ + -ℓ) (by linarith) zB hB
  have hdrift := expWeight_drift_le hℓ0.le hb h₀ hz₀ hz₀b hA' hzA hB hzBb
  have hM0 : 0 ≤ expWeight Z u₀ z₀ := expWeight_nonneg _ _
  have hBle : Real.exp (η * ℓ) * expWeight Z u₀ z₀ ≤ 3 * expWeight Z u₀ z₀ :=
    mul_le_mul_of_nonneg_right ((Real.exp_le_exp.mpr hηℓ).trans
      (by linarith [Real.exp_one_lt_d9])) hM0
  have hz₀c : c < z₀.re := by linarith
  have hconj0 : evenCoeff Z (boxSpline 1 3) (conj z₀) ≠ 0 := by
    rw [evenCoeff_conj]; exact (map_ne_zero _).mpr hz₀
  classical
  obtain ⟨S, hTS, hSE, hlow⟩ := exists_finset_window_lower hZ u₀ ℓ hall' {z₀, conj z₀}
  have hz₀S : z₀ ∈ S := hTS z₀ (by simp) hz₀
  have hz₀'S : conj z₀ ∈ S := hTS _ (by simp) hconj0
  have hle := expWeight_le_of_window_lower_deep hZ hnoreal hδ hsep hSE hz₀S hz₀'S hz₀c hu00 hℓ0
    (by positivity : 0 ≤ |K| * E + 1) hδℓ hdrift hBle hlow
  have h1 := hU₃ u₀ hu₃
  have h2 : expWeight Z u₀ zp * Real.exp (-(s * u₀)) * Real.exp (s * u₀) =
      expWeight Z u₀ zp := by rw [mul_assoc, ← Real.exp_add]; simp
  have hEe : E = Real.exp (s * ℓ) * Real.exp (s * u₀) := by
    rw [hE, ← Real.exp_add]; ring_nf
  have hcs : Real.exp (c * u₀) ≤ Real.exp (s * u₀) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs hu00)
  have hsu1 : 1 ≤ Real.exp (s * u₀) := Real.one_le_exp (mul_nonneg hs0 hu00)
  have h3 : 3 * (|K| * E + 1) * Real.exp (ℓ / 2) + 3 * (A * Real.exp ℓ * Real.exp (c * u₀)) ≤
      C * Real.exp (s * u₀) := by
    have ha : 3 * (|K| * E + 1) * Real.exp (ℓ / 2) ≤
        3 * (|K| + 1) * Real.exp (s * ℓ) * Real.exp (ℓ / 2) * Real.exp (s * u₀) := by
      have hx : 0 ≤ Real.exp (ℓ / 2) := (Real.exp_pos _).le
      have hu1 : 1 ≤ Real.exp (s * ℓ) * Real.exp (s * u₀) := hEe ▸ hE1
      rw [hEe]
      nlinarith [abs_nonneg K]
    have hb' : 3 * (A * Real.exp ℓ * Real.exp (c * u₀)) ≤
        3 * (A * Real.exp ℓ) * Real.exp (s * u₀) := by
      have := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 3 * (A * Real.exp ℓ) by positivity)
      linarith
    rw [hCdef, add_mul]
    linarith
  have h4 : C * Real.exp (s * u₀) < expWeight Z u₀ z₀ :=
    calc C * Real.exp (s * u₀) < expWeight Z u₀ zp * Real.exp (-(s * u₀)) * Real.exp (s * u₀) :=
          mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
      _ = expWeight Z u₀ zp := h2
      _ ≤ expWeight Z u₀ z₀ := h₀ zp
  linarith

/-- **The width law on windows under deep separation.** -/
theorem re_le_of_bddBelow_exp_windows_of_deepSeparated (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hsep : DeepSeparatedOrdinates Z c δ) {s : ℝ} (hs : c ≤ s) {T : Set ℝ}
    (hT : ∀ U : ℝ, ∃ a, U ≤ a ∧ Icc a (a + 80 / δ) ⊆ T) {K : ℝ}
    (hK : ∀ u ∈ T, -(K * Real.exp (s * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + s := by
  intro ρ₁ hρ₁
  by_contra h
  push Not at h
  obtain ⟨U, hU⟩ := exists_lt_exp_in_window_of_deepSeparated hZ hnoreal hc hδ hsep hs hρ₁ h
    (le_refl (40 / δ)) K
  obtain ⟨a, ha, hsub⟩ := hT U
  have h40 : 0 < 40 / δ := by positivity
  have h80 : 80 / δ = 40 / δ + 40 / δ := by ring
  obtain ⟨u, hu, hlt⟩ := hU (a + 40 / δ) (by linarith)
  have hmem : u ∈ T := hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩
  linarith [hK u hmem]

/-- One bootstrap step at the primes: width `a` becomes width `α ≥ max(c, a − 1/3)`. -/
theorem re_le_of_prime_windows_step_deep (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hsep : DeepSeparatedOrdinates Z c δ) {a α K : ℝ} (ha : 0 ≤ a) (hα : c ≤ α)
    (haα : a - 1 / 3 ≤ α) (hwidth : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime → T ≤ Real.log p →
      Real.log p ≤ T + 80 / δ + 1 → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + α := by
  obtain ⟨M, hM⟩ := exists_bddBelow_exp_windows_of_prime_windows hZ ha (hc.trans hα) haα hwidth
    hprime
  refine re_le_of_bddBelow_exp_windows_of_deepSeparated hZ hnoreal hc hδ hsep hα
    (T := {u | -(M * Real.exp (α * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re})
    (fun U => ?_) (fun u hu => hu)
  obtain ⟨T, hTU, hT⟩ := hM U
  exact ⟨T + 1, by linarith, fun u hu => hT u ⟨hu.1, by linarith [hu.2]⟩⟩

/-- **Prime windows under deep separation.** If the exponents of depth `> c ≥ 0` have
`δ`-separated ordinates and `2 Re S(log p) ≥ −K` at the primes of windows `[T, T + 80/δ + 1]` (in
`log p`) beyond every bound, every zero has real part `≤ ½ + c`. -/
theorem re_le_of_bddBelow_prime_windows_of_deepSeparated (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hsep : DeepSeparatedOrdinates Z c δ) {K : ℝ}
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime → T ≤ Real.log p →
      Real.log p ≤ T + 80 / δ + 1 → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + c := by
  have hhalf : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + 1 / 2 := fun ρ hρ => by
    linarith [(Z.strip ρ hρ).2]
  have h1 := re_le_of_prime_windows_step_deep hZ hnoreal hc hδ hsep (a := 1 / 2)
    (α := max c (1 / 6)) (by norm_num) (le_max_left _ _)
    ((by norm_num : (1 : ℝ) / 2 - 1 / 3 ≤ 1 / 6).trans (le_max_right _ _)) hhalf hprime
  rcases le_total c (1 / 6) with h | h
  · rw [max_eq_right h] at h1
    exact re_le_of_prime_windows_step_deep hZ hnoreal hc hδ hsep (a := 1 / 6) (α := c)
      (by norm_num) le_rfl (by linarith) h1 hprime
  · rwa [max_eq_left h] at h1

/-- **For `ζ`: separated off-line ordinates and one sequence of prime windows.** If the zeros of
`ζ` off the critical line, with their conjugates, have `δ`-separated ordinates, then a bounded
trace `2 Re S(log p) ≥ −K` at the primes of windows `[x, e^{80/δ + 1} x]` along any sequence of
scales gives the Riemann hypothesis. -/
theorem riemannHypothesis_of_prime_windows_of_offLine_separated {δ : ℝ} (hδ : 0 < δ)
    (hsep : DeepSeparatedOrdinates zetaZeroConfig 0 δ) {K : ℝ}
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime → T ≤ Real.log p →
      Real.log p ≤ T + 80 / δ + 1 →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) :
    RiemannHypothesis :=
  riemannHypothesis_of_forall_re_le fun ρ hρ => by
    have := re_le_of_bddBelow_prime_windows_of_deepSeparated temperedConfig_zetaZeroConfig
      (fun _ hρ hzero => not_mem_carrier_of_im_eq_zero hρ hzero) le_rfl hδ hsep hprime ρ hρ
    linarith

end GaloisForLFunctions.SurfaceOfSpecZ
