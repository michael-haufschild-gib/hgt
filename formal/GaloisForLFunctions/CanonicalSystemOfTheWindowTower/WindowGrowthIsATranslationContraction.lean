import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheFrozenFormGluesTwoWindows
import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.HeckeSimilitudesOfAWindowAreScalars
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.WindowRealizations

/-!
# Window growth is a contraction of the shorter window

For `0 < ε < ℓ` the window `W_{ℓ+ε} = [−ℓ−ε, 0]` is the union of the two translates
`[−ℓ−ε, −ε]` and `[−ℓ, 0]` of `W_ℓ`; every test on it is `τ_ε u + v` with `u, v` tests on `W_ℓ`,
`τ_ε u(x) = u(x + ε)`.

* **Window growth law** (`window_nonneg_iff_contraction`): `Q ≥ 0` on `W_{ℓ+ε}` iff `Q ≥ 0` on `W_ℓ`
  and `W(τ_ε u, v)² ≤ Q(u)Q(v)` for all tests `u, v` on `W_ℓ`. The longer window is positive exactly
  when translation by `ε` is a contraction for the form of the shorter window — the continuous
  Schur–Krein step, with no inverse and no Schur complement.
* **The stage pairing** (`weilPair_stage_eq`): at a stage `ℓ = log(N+1)` the pairing is the frozen
  pairing (polarization of the stage datum `Q_N`) minus the new fold, which enters as the plain
  correlation at lag `ℓ − ε`:
  `W(τ_ε u, v) = W_N(τ_ε u, v) − w ∫ u(y) v(y + ℓ − ε) dy`.
* **The stage disk** (`stage_nonneg_iff_disk`): the stage window is positive iff the previous window
  is and `|W_N(τ_ε u, v) − w⟨u, τ_{ℓ−ε} v⟩| ≤ √(Q(u)Q(v))` for all `u, v` on it: the fold lies in
  the Carathéodory disk centred at the frozen pairing, of radius the geometric mean of the previous
  energies. In `ε` the centre moves by translation of one test against the other (a linear law);
  the arithmetic enters through the lag `ℓ − ε`, at which the new fold first meets the window, and
  through the earlier folds inside `W_N`.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower
open scoped Real

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open SpacingScaleHarmonicAnalysis CohomologyOfWindowsOfSpecZ RHTower.WeilMarkovPole
open ArithmeticCastelnuovoSeveri DimensionZeroGeometryOfSpecZ

/-! ### A smooth cutoff -/

/-- The cutoff equal to `1` left of `a` and `0` right of `b`. -/
def cutoff (a b x : ℝ) : ℝ := Real.smoothTransition ((b - x) / (b - a))

theorem contDiff_cutoff (a b : ℝ) : ContDiff ℝ 2 (cutoff a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

theorem cutoff_of_le {a b x : ℝ} (hab : a < b) (hx : x ≤ a) : cutoff a b x = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)

theorem cutoff_of_ge {a b x : ℝ} (hab : a < b) (hx : b ≤ x) : cutoff a b x = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

/-! ### Windows and their translates -/

theorem mem_realTests_of_windowTest {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    H ∈ realTests := ⟨hH.contDiff, hH.hasCompactSupport⟩

theorem isWindowTest_translate {ℓ ε : ℝ} {u : ℝ → ℝ} (hu : IsWindowTest ℓ u) (hε : 0 ≤ ε) :
    IsWindowTest (ℓ + ε) (fun x => u (x + ε)) := by
  refine ⟨hu.contDiff.comp (contDiff_id.add contDiff_const), fun y hy => hu.vanish _ fun hm => ?_⟩
  exact hy ⟨by linarith [hm.1], by linarith [hm.2]⟩

theorem weilQuad_translate (u : ℝ → ℝ) (ε : ℝ) : weilQuad (fun x => u (x + ε)) = weilQuad u := by
  have := weilQuad_comp_sub u (-ε)
  simpa only [sub_neg_eq_add] using this

/-- If a quadratic `a s² + 2 b s t + c t²` is nonnegative everywhere, then `b² ≤ a c`. -/
theorem sq_le_mul_of_forall_nonneg {a b c : ℝ} (ha : 0 ≤ a)
    (h : ∀ s : ℝ, 0 ≤ a * (s * s) + 2 * b * s + c) : b ^ 2 ≤ a * c := by
  have hc : 0 ≤ c := by simpa using h 0
  have := abs_le_sqrt_mul_sqrt_of_quadratic_nonneg ha h
  have h2 : |b| ^ 2 ≤ (Real.sqrt a * Real.sqrt c) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) this 2
  rwa [sq_abs, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hc] at h2

/-- **Window growth law**: the window of length `ℓ + ε` is positive iff the window of length `ℓ`
is and translation by `ε` is a contraction for its form. -/
theorem window_nonneg_iff_contraction {ℓ ε : ℝ} (hε : 0 < ε) (hεℓ : ε < ℓ) :
    (∀ H, IsWindowTest (ℓ + ε) H → 0 ≤ weilQuad H) ↔
      (∀ v, IsWindowTest ℓ v → 0 ≤ weilQuad v) ∧
        ∀ u v, IsWindowTest ℓ u → IsWindowTest ℓ v →
          weilPair (fun x => u (x + ε)) v ^ 2 ≤ weilQuad u * weilQuad v := by
  constructor
  · intro h
    refine ⟨fun v hv => h v (hv.mono (by linarith)), fun u v hu hv => ?_⟩
    have hu' := isWindowTest_translate hu hε.le
    have hv' : IsWindowTest (ℓ + ε) v := hv.mono (by linarith)
    refine sq_le_mul_of_forall_nonneg (h u (hu.mono (by linarith))) fun s => ?_
    have hH : IsWindowTest (ℓ + ε) (fun x => s * u (x + ε) + 1 * v x) :=
      ⟨(contDiff_const.mul hu'.contDiff).add (contDiff_const.mul hv.contDiff), fun y hy => by
        simp only [hu'.vanish y hy, hv'.vanish y hy, mul_zero, add_zero]⟩
    have := h _ hH
    rw [weilQuad_plane (mem_realTests_of_windowTest hu') (mem_realTests_of_windowTest hv') s 1, weilQuad_translate] at this
    nlinarith [this]
  · rintro ⟨hpos, hdisk⟩ H hH
    set χ := cutoff (-ℓ) (-ε) with hχ
    have hab : -ℓ < -ε := by linarith
    have hχc : ContDiff ℝ 2 χ := contDiff_cutoff _ _
    set u₀ : ℝ → ℝ := fun x => χ (x - ε) * H (x - ε) with hu₀def
    set v : ℝ → ℝ := fun x => (1 - χ x) * H x with hvdef
    have hu₀ : IsWindowTest ℓ u₀ := by
      refine ⟨(hχc.comp (contDiff_id.sub contDiff_const)).mul
        (hH.contDiff.comp (contDiff_id.sub contDiff_const)), fun y hy => ?_⟩
      have hy' : y < -ℓ ∨ 0 < y := by
        by_contra hc; push Not at hc; exact hy ⟨hc.1, hc.2⟩
      simp only [u₀]
      rcases hy' with hy' | hy'
      · rw [hH.vanish (y - ε) fun hm => by linarith [hm.1], mul_zero]
      · rw [hχ, cutoff_of_ge hab (by linarith), zero_mul]
    have hv : IsWindowTest ℓ v := by
      refine ⟨(contDiff_const.sub hχc).mul hH.contDiff, fun y hy => ?_⟩
      have hy' : y < -ℓ ∨ 0 < y := by
        by_contra hc; push Not at hc; exact hy ⟨hc.1, hc.2⟩
      simp only [v]
      rcases hy' with hy' | hy'
      · rw [hχ, cutoff_of_le hab hy'.le, sub_self, zero_mul]
      · rw [hH.vanish y fun hm => by linarith [hm.2], mul_zero]
    have hsplit : H = fun x => 1 * u₀ (x + ε) + 1 * v x := by
      funext x
      simp only [u₀, v, add_sub_cancel_right]
      ring
    have hu' := isWindowTest_translate hu₀ hε.le
    have hv' : IsWindowTest (ℓ + ε) v := hv.mono (by linarith)
    rw [hsplit, weilQuad_plane (mem_realTests_of_windowTest hu') (mem_realTests_of_windowTest hv') 1 1, weilQuad_translate]
    have ha := hpos u₀ hu₀
    have hc := hpos v hv
    have hb := hdisk u₀ v hu₀ hv
    nlinarith [sq_nonneg (weilQuad u₀ - weilQuad v), sq_nonneg (weilQuad u₀ + weilQuad v)]

/-! ### The stage pairing -/

/-- On a window of level `N + 1` the stage datum is Weil's form plus the new fold:
`Q_N(H) = Q(H) + 2w∫H(u)H(u + log(N+1))`. -/
theorem stageForm_eq_weilQuad_add_fold {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) {N : ℕ}
    (hN : 1 ≤ N) (hA : windowLevel A = N + 1) :
    WindowTowerOfSpecZ.stageForm N H =
      weilQuad H + 2 * primeJumpWeight (N + 1) * ∫ u, H u * H (u + Real.log (N + 1 : ℕ)) := by
  have hQ := weilQuad_eq_markovForm_windowLevel hH
  rw [hA, WindowTowerOfSpecZ.markovForm_succ hH.continuous hH.hasCompactSupport hN] at hQ
  rw [WindowTowerOfSpecZ.stageForm]
  linarith

/-- A test on a window of length `ℓ` does not meet its own translate by `ℓ`. -/
theorem mul_shift_length_eq_zero {ℓ : ℝ} {u : ℝ → ℝ} (hu : IsWindowTest ℓ u) (x : ℝ) :
    u x * u (x + ℓ) = 0 := by
  by_cases hx : x ≤ -ℓ
  · rw [eq_zero_of_vanish_off_Icc (u := x) hu.continuous hu.vanish (Or.inl hx), zero_mul]
  · push Not at hx
    rw [eq_zero_of_vanish_off_Icc (u := x + ℓ) hu.continuous hu.vanish (Or.inr (by linarith)),
      mul_zero]

/-- The **frozen pairing** of level `N`: the polarization of the stage datum `Q_N`. -/
def frozenPair (N : ℕ) (f g : ℝ → ℝ) : ℝ :=
  (WindowTowerOfSpecZ.stageForm N (fun x => f x + g x) - WindowTowerOfSpecZ.stageForm N f -
    WindowTowerOfSpecZ.stageForm N g) / 2

/-- **The stage pairing**: at the stage `ℓ = log(N+1)`, for tests `u, v` on `W_ℓ`,
`W(τ_ε u, v) = W_N(τ_ε u, v) − w ∫ u(y) v(y + ℓ − ε) dy`. -/
theorem weilPair_stage_eq {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε)
    (hεn : Real.log (N + 1 : ℕ) + ε < Real.log (N + 2 : ℕ)) {u v : ℝ → ℝ}
    (hu : IsWindowTest (Real.log (N + 1 : ℕ)) u) (hv : IsWindowTest (Real.log (N + 1 : ℕ)) v) :
    weilPair (fun x => u (x + ε)) v =
      frozenPair N (fun x => u (x + ε)) v -
        primeJumpWeight (N + 1) * crossCorr u v (Real.log (N + 1 : ℕ) - ε) := by
  set ℓ := Real.log (N + 1 : ℕ) with hℓ
  have hwl := windowLevel_stage hε.le hεn
  have hu' := isWindowTest_translate hu hε.le
  have hv' : IsWindowTest (ℓ + ε) v := hv.mono (by linarith)
  have hsum : IsWindowTest (ℓ + ε) (fun x => u (x + ε) + v x) :=
    ⟨hu'.contDiff.add hv'.contDiff, fun y hy => by
      simp only [hu'.vanish y hy, hv'.vanish y hy, add_zero]⟩
  have s1 := stageForm_eq_weilQuad_add_fold hsum hN hwl
  have s2 := stageForm_eq_weilQuad_add_fold hu' hN hwl
  have s3 := stageForm_eq_weilQuad_add_fold hv' hN hwl
  rw [← hℓ] at s1 s2 s3
  beta_reduce at s1 s2
  have p1 : ∀ x, (u (x + ε) + v x) * (u (x + ℓ + ε) + v (x + ℓ)) = u (x + ε) * v (x + ℓ) := by
    intro x
    have a1 := mul_shift_length_eq_zero hu (x + ε)
    have a2 := mul_shift_length_eq_zero hv x
    have a3 : v x * u (x + ℓ + ε) = 0 := by
      by_cases hx : x ≤ -ℓ
      · rw [eq_zero_of_vanish_off_Icc (u := x) hv.continuous hv.vanish (Or.inl hx), zero_mul]
      · push Not at hx
        rw [hu.vanish (x + ℓ + ε) fun hm => by linarith [hm.2], mul_zero]
    rw [show x + ε + ℓ = x + ℓ + ε by ring] at a1
    linear_combination a1 + a3 + a2
  have hc : ∫ x, u (x + ε) * v (x + ℓ) = crossCorr u v (ℓ - ε) := by
    unfold crossCorr
    rw [← integral_add_right_eq_self (fun y => u y * v (y + (ℓ - ε))) ε]
    congr 1; funext x; congr 2; ring
  have i1 : ∫ x, (u (x + ε) + v x) * (u (x + ℓ + ε) + v (x + ℓ)) = crossCorr u v (ℓ - ε) := by
    rw [show (fun x => (u (x + ε) + v x) * (u (x + ℓ + ε) + v (x + ℓ))) =
      fun x => u (x + ε) * v (x + ℓ) from funext p1, hc]
  have i2 : ∫ x, u (x + ε) * u (x + ℓ + ε) = 0 := by
    have h0 : ∀ x, u (x + ε) * u (x + ℓ + ε) = 0 := fun x => by
      have := mul_shift_length_eq_zero hu (x + ε)
      rwa [show x + ε + ℓ = x + ℓ + ε by ring] at this
    simp only [h0, integral_zero]
  have i3 : ∫ x, v x * v (x + ℓ) = 0 := by
    simp only [mul_shift_length_eq_zero hv, integral_zero]
  rw [i1] at s1
  rw [i2] at s2
  rw [i3] at s3
  have hplane := weilQuad_plane (mem_realTests_of_windowTest hu') (mem_realTests_of_windowTest hv') 1 1
  simp only [one_mul, one_pow, mul_one] at hplane
  unfold frozenPair
  beta_reduce
  rw [s1, s2, s3, hplane]
  ring

/-- **The stage disk**: the stage window is positive iff the previous window is and the new fold
lies in the Carathéodory disk centred at the frozen pairing. -/
theorem stage_nonneg_iff_disk {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε)
    (hεn : Real.log (N + 1 : ℕ) + ε < Real.log (N + 2 : ℕ)) :
    (∀ H, IsWindowTest (Real.log (N + 1 : ℕ) + ε) H → 0 ≤ weilQuad H) ↔
      (∀ v, IsWindowTest (Real.log (N + 1 : ℕ)) v → 0 ≤ weilQuad v) ∧
        ∀ u v, IsWindowTest (Real.log (N + 1 : ℕ)) u → IsWindowTest (Real.log (N + 1 : ℕ)) v →
          (frozenPair N (fun x => u (x + ε)) v -
              primeJumpWeight (N + 1) * crossCorr u v (Real.log (N + 1 : ℕ) - ε)) ^ 2 ≤
            weilQuad u * weilQuad v := by
  have hn : 2 ≤ N + 1 := by omega
  have hεn' : Real.log ((N + 1 : ℕ) : ℝ) + ε < Real.log (((N + 1 : ℕ) : ℝ) + 1) := by
    have : (((N + 1 : ℕ) : ℝ) + 1) = ((N + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [this]; exact hεn
  rw [window_nonneg_iff_contraction hε (stage_eps_lt_log hn hεn')]
  refine and_congr Iff.rfl (forall_congr' fun u => forall_congr' fun v => ?_)
  refine forall_congr' fun hu => forall_congr' fun hv => ?_
  rw [weilPair_stage_eq hN hε hεn hu hv]

/-- **RH is the contraction of every growth step**: Weil positivity on all windows holds iff for all
`0 < ε < ℓ` translation by `ε` is a contraction for Weil's form on `W_ℓ`. -/
theorem riemannHypothesis_iff_translation_contraction :
    RiemannHypothesis ↔ ∀ ℓ ε : ℝ, 0 < ε → ε < ℓ → ∀ u v,
      IsWindowTest ℓ u → IsWindowTest ℓ v →
        weilPair (fun x => u (x + ε)) v ^ 2 ≤ weilQuad u * weilQuad v := by
  rw [riemannHypothesis_iff_windowForm_nonneg]
  constructor
  · intro h ℓ ε hε hεℓ
    exact ((window_nonneg_iff_contraction hε hεℓ).mp fun H hH =>
      h _ (by linarith) H hH).2
  · intro hc
    -- windows of length `≤ (k+2)/2000` are positive, by induction on `k`
    have step : ∀ k : ℕ, ∀ A : ℝ, 0 ≤ A → A ≤ ((k : ℝ) + 2) / 2000 →
        ∀ H, IsWindowTest A H → 0 ≤ weilQuad H := by
      intro k
      induction k with
      | zero =>
        intro A hA0 hA H hH
        have h := weilQuad_ge_of_short (hH.mono (show A ≤ 1 / 1000 by norm_num at hA; linarith))
          (by norm_num) le_rfl
        exact le_trans (div_nonneg (integral_nonneg fun u => sq_nonneg _) (by norm_num)) h
      | succ k ih =>
        intro A hA0 hA H hH
        by_cases hsmall : A ≤ ((k : ℝ) + 2) / 2000
        · exact ih A hA0 hsmall H hH
        · push Not at hsmall
          have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          have hε : (0 : ℝ) < 1 / 2000 := by norm_num
          have hεℓ : (1 / 2000 : ℝ) < A - 1 / 2000 := by push_cast at hA hsmall ⊢; linarith
          have hgrow := (window_nonneg_iff_contraction hε hεℓ).mpr
            ⟨fun v hv => ih (A - 1 / 2000) (by linarith) (by push_cast at hA ⊢; linarith) v hv,
              hc (A - 1 / 2000) (1 / 2000) hε hεℓ⟩
          exact hgrow H (by rwa [sub_add_cancel])
    intro A hA0 H hH
    obtain ⟨k, hk⟩ := exists_nat_ge (2000 * A)
    exact step k A hA0 (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith) H hH

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
