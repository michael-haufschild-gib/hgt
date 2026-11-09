import GaloisForLFunctions.SurfaceOfSpecZ.SeparatedOrdinatesAreSeenInEveryWindow
import GaloisForLFunctions.SurfaceOfSpecZ.TheGapMethodIterates
import GaloisForLFunctions.SurfaceOfSpecZ.HasseWeilAtThePrimeDegreesBoundsTheWidth

/-!
# Prime windows of fixed ratio decide separated configurations

Let a tempered configuration without real zeros have `δ`-separated ordinates
(`SeparatedOrdinates`). If `2 Re S(log p) ≥ −K` for every prime `p` with
`log p ∈ [T, T + 80/δ + 1]`, for arbitrarily large `T`, every zero lies on the line
(`onLine_of_bddBelow_prime_windows_of_separatedOrdinates`). The windows `[x, e^{80/δ + 1} x]` have
fixed ratio and may sit at any sparse sequence of scales; no attainment is assumed.

* **Transfer** (`exists_bddBelow_exp_windows_of_prime_windows`). Primes have gaps `≤ y^{2/3}`
  (`powGaps_primes`), so every `u` in `[T + 1, T + 1 + 80/δ]` has a prime `p ≤ eᵘ` with
  `u − log p ≤ 2G e^{−u/3}`. At width `a` the trace is Lipschitz with constant `≍ e^{au}`
  (`abs_two_re_lagStructure_sub_le_of_width`), so the prime bound becomes `−M e^{αu}` on the real
  window, `α = max(0, a − 1/3)`.
* **Bootstrap.** The windowed width law (`re_le_of_bddBelow_exp_windows_of_separatedOrdinates`)
  turns `−M e^{αu}` on windows of length `80/δ` into width `α`. From the trivial width `½` two
  steps reach `1/6` and then `0`.

Contrapositive (`eventually_prime_window_lt_of_separatedOrdinates`): an impure separated
configuration falls below every `−K` at some prime of every window `[T, T + 80/δ + 1]` far out.
On prime windows of unbounded length a bounded-below impure configuration has no positive
separation (`not_separatedOrdinates_of_bddBelow_long_prime_windows`). This is review 0911's
scale-local sampling question (B139) for separated configurations, with fixed ratio.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

variable {Z : ZeroConfig}

/-- **Prime windows transfer to real windows.** At width `a ≥ 0`, a lower bound `−K` at the primes
of `[T, T + L + 1]` (in `log`) for arbitrarily large `T` gives `−M e^{αu}` on the real windows
`[T + 1, T + 1 + L]`, for every `α ≥ max(0, a − 1/3)`: prime gaps are `≤ y^{2/3}`. -/
theorem exists_bddBelow_exp_windows_of_prime_windows (hZ : TemperedConfig Z) {a α L K : ℝ}
    (ha : 0 ≤ a) (hα : 0 ≤ α) (haα : a - 1 / 3 ≤ α)
    (hwidth : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime → T ≤ Real.log p →
      Real.log p ≤ T + L + 1 → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∃ M : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u ∈ Icc (T + 1) (T + 1 + L),
      -(M * Real.exp (α * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  obtain ⟨G, U₀, hG, hU₀, hnear⟩ := exists_log_degree_near (θ := (2 : ℝ) / 3)
    (by norm_num) (powGaps_primes (by norm_num) (by norm_num))
  set Lc : ℝ := ∑' z : ℂ, ‖lagCoeff Z (boxSpline 1 3) z‖ * ‖z‖ with hLc
  have hLc0 : 0 ≤ Lc := tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hgaplim : Tendsto (fun u : ℝ => 2 * G * Real.exp (((2 : ℝ) / 3 - 1) * u)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (2 : ℝ) / 3 - 1 < 0))
    simpa only [Function.comp_def, id_eq, mul_zero] using he.const_mul (2 * G)
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.mp
    (hgaplim.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  refine ⟨|K| + 4 * Lc * G, fun U => ?_⟩
  obtain ⟨T, hTU, hbound⟩ := hprime (max U (max U₀ (max U₁ 0)))
  have hT₀ : U₀ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hTU
  have hT₁ : U₁ ≤ T := (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans hTU
  have hT0 : 0 ≤ T := (((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans hTU
  refine ⟨T, (le_max_left _ _).trans hTU, fun u hu => ?_⟩
  have hu0 : 0 ≤ u := by linarith [hu.1]
  obtain ⟨p, hp, -, hlog0, hlogu, hgap⟩ := hnear u (by linarith [hu.1])
  have hgap₁ : u - Real.log p ≤ 1 := hgap.trans (hU₁ u (by linarith [hu.1]))
  have hbase := hbound p hp (by linarith [hu.1]) (by linarith [hu.2])
  have hlip := abs_two_re_lagStructure_sub_le_of_width hZ ha hwidth hlog0 hlogu
  have hvar : |2 * (lagStructure Z (boxSpline 1 3) u).re -
      2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re| ≤
      4 * Lc * G * Real.exp (α * u) := by
    have h₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * Lc by positivity)) (Real.exp_pos (a * u)).le
    have he : Real.exp (((2 : ℝ) / 3 - 1) * u) * Real.exp (a * u) =
        Real.exp ((a - 1 / 3) * u) := by
      rw [← Real.exp_add]; congr 1; ring
    have h₂ : 2 * Lc * (2 * G * Real.exp (((2 : ℝ) / 3 - 1) * u)) * Real.exp (a * u) =
        4 * Lc * G * Real.exp ((a - 1 / 3) * u) := by
      calc _ = 4 * Lc * G * (Real.exp (((2 : ℝ) / 3 - 1) * u) * Real.exp (a * u)) := by ring
        _ = _ := by rw [he]
    have h₃ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right haα hu0))
      (show 0 ≤ 4 * Lc * G by positivity)
    exact hlip.trans (h₁.trans (h₂.le.trans h₃))
  have hK : K ≤ |K| * Real.exp (α * u) :=
    (le_abs_self K).trans (by
      have hh := mul_le_mul_of_nonneg_left (Real.one_le_exp (mul_nonneg hα hu0)) (abs_nonneg K)
      simpa only [mul_one] using hh)
  have hlow := (abs_le.mp hvar).1
  have e : (|K| + 4 * Lc * G) * Real.exp (α * u) =
      |K| * Real.exp (α * u) + 4 * Lc * G * Real.exp (α * u) := by ring
  rw [e]
  linarith

/-- One bootstrap step: at width `a`, prime windows of length `80/δ + 1` give width
`max(0, a − 1/3)`. -/
theorem re_le_of_prime_windows_step (hZ : TemperedConfig Z) (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hsep : SeparatedOrdinates Z δ) {a α K : ℝ} (ha : 0 ≤ a) (hα : 0 ≤ α)
    (haα : a - 1 / 3 ≤ α) (hwidth : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime → T ≤ Real.log p →
      Real.log p ≤ T + 80 / δ + 1 → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + α := by
  obtain ⟨M, hM⟩ := exists_bddBelow_exp_windows_of_prime_windows hZ ha hα haα hwidth hprime
  refine re_le_of_bddBelow_exp_windows_of_separatedOrdinates hZ hnoreal hδ hsep hα
    (T := {u | -(M * Real.exp (α * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re})
    (fun U => ?_) (fun u hu => hu)
  obtain ⟨T, hTU, hT⟩ := hM U
  exact ⟨T + 1, by linarith, fun u hu => hT u ⟨hu.1, by linarith [hu.2]⟩⟩

/-- **Prime windows of fixed ratio decide separated configurations.** If `2 Re S(log p) ≥ −K` for
every prime `p` with `log p ∈ [T, T + 80/δ + 1]`, for arbitrarily large `T`, every zero of a
tempered configuration without real zeros and with `δ`-separated ordinates lies on the line. -/
theorem onLine_of_bddBelow_prime_windows_of_separatedOrdinates (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hsep : SeparatedOrdinates Z δ)
    {K : ℝ}
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime → T ≤ Real.log p →
      Real.log p ≤ T + 80 / δ + 1 → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have hhalf : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + 1 / 2 := fun ρ hρ => by
    linarith [(Z.strip ρ hρ).2]
  have h1 := re_le_of_prime_windows_step hZ hnoreal hδ hsep (a := 1 / 2) (α := 1 / 6)
    (by norm_num) (by norm_num) (by norm_num) hhalf hprime
  have h2 := re_le_of_prime_windows_step hZ hnoreal hδ hsep (a := 1 / 6) (α := 0)
    (by norm_num) le_rfl (by norm_num) h1 hprime
  intro ρ hρ
  have hle := h2 ρ hρ
  have hle' := h2 _ (Z.reflect_mem ρ hρ)
  have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
  linarith

/-- **Every far prime window sees an impure separated configuration.** If some zero is off the
line, then for every `K`, every window `[T, T + 80/δ + 1]` (in `log p`) far enough out contains a
prime with `2 Re S(log p) < −K`. -/
theorem eventually_prime_window_lt_of_separatedOrdinates (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hsep : SeparatedOrdinates Z δ)
    (himpure : ∃ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2) (K : ℝ) :
    ∃ U : ℝ, ∀ T : ℝ, U ≤ T → ∃ p : ℕ, p.Prime ∧ T ≤ Real.log p ∧
      Real.log p ≤ T + 80 / δ + 1 ∧ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re < -K := by
  by_contra h
  push Not at h
  obtain ⟨ρ, hρ, hne⟩ := himpure
  exact hne (onLine_of_bddBelow_prime_windows_of_separatedOrdinates hZ hnoreal hδ hsep
    (K := K) (fun U => by
      obtain ⟨T, hTU, hT⟩ := h U
      exact ⟨T, hTU, fun p hp h1 h2 => hT p hp h1 h2⟩) ρ hρ)

/-- **Growing prime windows force near-coincident ordinates.** If an impure tempered configuration
without real zeros satisfies `2 Re S(log p) ≥ −K` at every prime of windows `[T, T + L]` (in
`log p`) of every length `L` beyond every bound, its ordinates have no positive separation: a
counterexample to scale-local sampling at the primes must carry near-coincident ordinates. -/
theorem not_separatedOrdinates_of_bddBelow_long_prime_windows (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ Z.carrier) (hre : ρ₁.re ≠ 1 / 2)
    {K : ℝ}
    (hprime : ∀ L U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime → T ≤ Real.log p →
      Real.log p ≤ T + L → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re)
    {δ : ℝ} (hδ : 0 < δ) : ¬ SeparatedOrdinates Z δ := fun hsep =>
  hre (onLine_of_bddBelow_prime_windows_of_separatedOrdinates hZ hnoreal hδ hsep (K := K)
    (fun U => by
      obtain ⟨T, hTU, hT⟩ := hprime (80 / δ + 1) U
      exact ⟨T, hTU, fun p hp h1 h2 => hT p hp h1 (by linarith)⟩) ρ₁ hρ₁)

end GaloisForLFunctions.SurfaceOfSpecZ
