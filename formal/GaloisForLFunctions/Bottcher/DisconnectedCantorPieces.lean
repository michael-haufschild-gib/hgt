/-
# Small pieces of a disconnected filled Julia set

For `c ∉ M` let `D = {G_c < s}` and `g_± = ±g` the two inverse branches of `f_c` over `D`
(`exists_inverse_branch`).  Both map `D` into the compact `{G_c ≤ s/2} ⊆ D`, so they strictly
contract the Carathéodory density of the bounded `D`; a composition `g_w` of `n` branches therefore
has `‖g_w'‖ = O((1+ε)^{-n})` on compact subsets of `D`.  Every `q ∈ K_c` equals `g_w(f_c^n q)` for
some word `w` of length `n`, and the depth-`n` piece `E = g_w({G_c < s'})` (`G_c(0) < s' < s`):

* is open and contains `q`, and has diameter `O((1+ε)^{-n})` by a finite chain of balls;
* has `E ∖ K_c = g_w({0 < G_c < s'})`, which is connected and nonempty;
* meets `K_c` in the compact set `g_w(K_c)`, which contains a second point `g_w(-f_c^n q)`.

Consequences: `K_c` has empty interior, no isolated points, is totally disconnected, and every
point of `K_c` has arbitrarily small open neighbourhoods `E` with `E ∖ K_c` connected.
-/
import GaloisForLFunctions.Bottcher.DisconnectedInverseBranch
import GaloisForLFunctions.Bottcher.CaratheodoryDensity

open Complex Set Filter Topology Metric

namespace Bottcher

variable {c : ℂ}

/-! ### Words of inverse branches -/

/-- The inverse branch `g` over `D = {G_c < s}`. -/
noncomputable def invBranch (hc : c ∉ mandelbrot) : ℂ → ℂ := (exists_inverse_branch hc).choose

theorem invBranch_spec (hc : c ∉ mandelbrot) :
    DifferentiableOn ℂ (invBranch hc) (branchDomain c) ∧
      (∀ y ∈ branchDomain c, quadratic c (invBranch hc y) = y) ∧
      ∀ z, quadratic c z ∈ branchDomain c →
        z = invBranch hc (quadratic c z) ∨ z = -invBranch hc (quadratic c z) :=
  (exists_inverse_branch hc).choose_spec

/-- The two inverse branches `g` and `-g`. -/
noncomputable def branchOf (hc : c ∉ mandelbrot) (b : Bool) : ℂ → ℂ :=
  if b then invBranch hc else fun y => -invBranch hc y

/-- The composition of inverse branches along a word. -/
noncomputable def branchComp (hc : c ∉ mandelbrot) : List Bool → ℂ → ℂ
  | [] => id
  | b :: w => branchOf hc b ∘ branchComp hc w

theorem branchOf_differentiableOn (hc : c ∉ mandelbrot) (b : Bool) :
    DifferentiableOn ℂ (branchOf hc b) (branchDomain c) := by
  cases b
  · exact (invBranch_spec hc).1.neg
  · exact (invBranch_spec hc).1

theorem quadratic_branchOf (hc : c ∉ mandelbrot) (b : Bool) {y : ℂ} (hy : y ∈ branchDomain c) :
    quadratic c (branchOf hc b y) = y := by
  have h := (invBranch_spec hc).2.1 y hy
  cases b
  · change (-invBranch hc y) ^ 2 + c = y
    have h' : invBranch hc y ^ 2 + c = y := h
    rw [neg_sq]; exact h'
  · exact h

theorem greenFunctionDyn_branchOf (hc : c ∉ mandelbrot) (b : Bool) {y : ℂ}
    (hy : y ∈ branchDomain c) :
    greenFunctionDyn c (branchOf hc b y) = greenFunctionDyn c y / 2 := by
  have h := greenFunctionDyn_quadratic c (branchOf hc b y)
  rw [quadratic_branchOf hc b hy] at h
  linarith

/-- The compact set `{G_c ≤ s/2}` receiving both branches. -/
def branchTarget (c : ℂ) : Set ℂ := {z | greenFunctionDyn c z ≤ branchLevel c / 2}

theorem branchLevel_pos (hc : c ∉ mandelbrot) : 0 < branchLevel c := by
  rw [branchLevel]; have := greenFunctionDyn_zero_pos hc; positivity

theorem branchTarget_subset (hc : c ∉ mandelbrot) : branchTarget c ⊆ branchDomain c :=
  fun z hz => by
    have h1 : greenFunctionDyn c z ≤ branchLevel c / 2 := hz
    have h2 := branchLevel_pos hc
    show greenFunctionDyn c z < branchLevel c
    linarith

theorem mapsTo_branchOf (hc : c ∉ mandelbrot) (b : Bool) :
    MapsTo (branchOf hc b) (branchDomain c) (branchTarget c) := by
  intro y hy
  change greenFunctionDyn c (branchOf hc b y) ≤ branchLevel c / 2
  rw [greenFunctionDyn_branchOf hc b hy]
  have : greenFunctionDyn c y < branchLevel c := hy
  linarith

theorem mapsTo_branchComp (hc : c ∉ mandelbrot) (w : List Bool) :
    MapsTo (branchComp hc w) (branchDomain c) (branchDomain c) := by
  induction w with
  | nil => exact mapsTo_id _
  | cons b w ih => exact ((mapsTo_branchOf hc b).mono_right (branchTarget_subset hc)).comp ih

theorem branchComp_differentiableOn (hc : c ∉ mandelbrot) (w : List Bool) :
    DifferentiableOn ℂ (branchComp hc w) (branchDomain c) := by
  induction w with
  | nil => exact differentiableOn_id
  | cons b w ih => exact (branchOf_differentiableOn hc b).comp ih (mapsTo_branchComp hc w)

theorem iterate_branchComp (hc : c ∉ mandelbrot) (w : List Bool) {y : ℂ}
    (hy : y ∈ branchDomain c) : (quadratic c)^[w.length] (branchComp hc w y) = y := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change (quadratic c)^[w.length + 1] (branchOf hc b (branchComp hc w y)) = y
    rw [Function.iterate_succ_apply, quadratic_branchOf hc b (mapsTo_branchComp hc w hy), ih]

theorem iterate_mem_filledJulia_iff (c z : ℂ) (n : ℕ) :
    (quadratic c)^[n] z ∈ filledJulia c ↔ z ∈ filledJulia c := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, quadratic_mem_filledJulia_iff]

theorem neg_mem_filledJulia_iff (c z : ℂ) : -z ∈ filledJulia c ↔ z ∈ filledJulia c := by
  rw [← quadratic_mem_filledJulia_iff c (-z), ← quadratic_mem_filledJulia_iff c z]
  simp [quadratic]

/-- **Addresses.**  Every point of `K_c` is `g_w(f_c^n q)` for a word `w` of length `n`. -/
theorem exists_address (hc : c ∉ mandelbrot) {q : ℂ} (hq : q ∈ filledJulia c) (n : ℕ) :
    ∃ w : List Bool, w.length = n ∧ branchComp hc w ((quadratic c)^[n] q) = q := by
  induction n generalizing q with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    have hfq : quadratic c q ∈ filledJulia c := (quadratic_mem_filledJulia_iff c q).mpr hq
    obtain ⟨w, hw, hwq⟩ := ih hfq
    have hD : quadratic c q ∈ branchDomain c := filledJulia_subset_branchDomain hc hfq
    obtain ⟨b, hb⟩ : ∃ b, branchOf hc b (quadratic c q) = q := by
      rcases (invBranch_spec hc).2.2 q hD with h | h
      · exact ⟨true, h.symm⟩
      · exact ⟨false, h.symm⟩
    refine ⟨b :: w, by simp [hw], ?_⟩
    change branchOf hc b (branchComp hc w ((quadratic c)^[n + 1] q)) = q
    rw [Function.iterate_succ_apply, hwq, hb]

/-! ### Contraction of the words -/

theorem exists_ball_branchDomain (c : ℂ) :
    ∃ B > 0, branchDomain c ⊆ ball 0 B := by
  obtain ⟨B, hB⟩ := (isCompact_green_sublevel c (branchLevel c)).isBounded.subset_ball 0
  refine ⟨max B 1, by positivity, fun z hz => ?_⟩
  exact ball_subset_ball (le_max_left _ _)
    (hB (show greenFunctionDyn c z ≤ branchLevel c from le_of_lt hz))

/-- **Exponential decay of the derivatives of words.** -/
theorem exists_branchComp_deriv_decay (hc : c ∉ mandelbrot) :
    ∃ ε > 0, ∃ B > 0, ∀ (w : List Bool) {y : ℂ} {r : ℝ}, 0 < r → ball y r ⊆ branchDomain c →
      ‖deriv (branchComp hc w) y‖ ≤ 2 * B / r / (1 + ε) ^ w.length := by
  obtain ⟨B, hB, hDB⟩ := exists_ball_branchDomain c
  have hDo := isOpen_branchDomain c
  have hLc : IsCompact (branchTarget c) := isCompact_green_sublevel c _
  obtain ⟨ε, hε, hstrict⟩ :=
    exists_strict_caraDensity_contraction hDo hB hDB hLc (branchTarget_subset hc)
  refine ⟨ε, hε, B, hB, ?_⟩
  -- the density inequality along words
  have hword : ∀ (w : List Bool), ∀ y ∈ branchDomain c,
      caraDensity (branchDomain c) (branchComp hc w y) *
        ((1 + ε) ^ w.length * ‖deriv (branchComp hc w) y‖) ≤
        caraDensity (branchDomain c) y := by
    intro w
    induction w with
    | nil =>
      intro y _
      simp [branchComp]
    | cons b w ih =>
      intro y hy
      set x := branchComp hc w y with hxdef
      have hx : x ∈ branchDomain c := mapsTo_branchComp hc w hy
      have hderiv : deriv (branchComp hc (b :: w)) y =
          deriv (branchOf hc b) x * deriv (branchComp hc w) y :=
        deriv_comp y ((branchOf_differentiableOn hc b).differentiableAt (hDo.mem_nhds hx))
          ((branchComp_differentiableOn hc w).differentiableAt (hDo.mem_nhds hy))
      have h1 := hstrict (branchOf hc b) (branchOf_differentiableOn hc b) (mapsTo_branchOf hc b)
        x hx
      have h2 := ih y hy
      change caraDensity (branchDomain c) (branchOf hc b x) *
        ((1 + ε) ^ (w.length + 1) * ‖deriv (branchComp hc (b :: w)) y‖) ≤ _
      rw [hderiv, norm_mul, pow_succ]
      calc caraDensity (branchDomain c) (branchOf hc b x) *
            ((1 + ε) ^ w.length * (1 + ε) * (‖deriv (branchOf hc b) x‖ *
              ‖deriv (branchComp hc w) y‖))
          = (caraDensity (branchDomain c) (branchOf hc b x) *
              ((1 + ε) * ‖deriv (branchOf hc b) x‖)) *
            ((1 + ε) ^ w.length * ‖deriv (branchComp hc w) y‖) := by ring
        _ ≤ caraDensity (branchDomain c) x *
            ((1 + ε) ^ w.length * ‖deriv (branchComp hc w) y‖) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ caraDensity (branchDomain c) y := h2
  intro w y r hr hrD
  have hy : y ∈ branchDomain c := hrD (mem_ball_self hr)
  have hlow := le_caraDensity hDo hB hDB (mapsTo_branchComp hc w hy)
  have hup := caraDensity_le hB hDB hr hrD
  have hw := hword w y hy
  have hpow : 0 < (1 + ε) ^ w.length := by positivity
  rw [le_div_iff₀ hpow]
  have h1 : 1 / (2 * B) * ((1 + ε) ^ w.length * ‖deriv (branchComp hc w) y‖) ≤ 1 / r :=
    le_trans (mul_le_mul_of_nonneg_right hlow (by positivity)) (hw.trans hup)
  have h2 : (1 + ε) ^ w.length * ‖deriv (branchComp hc w) y‖ ≤ 2 * B / r := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * B)
    rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
    calc (1 + ε) ^ w.length * ‖deriv (branchComp hc w) y‖ ≤ 2 * B * (1 / r) := this
      _ = 2 * B / r := by ring
  linarith [mul_comm ((1 + ε) ^ w.length) ‖deriv (branchComp hc w) y‖]

/-! ### Small pieces -/

/-- The level `s' = 5G_c(0)/4` of the pieces. -/
noncomputable def pieceLevel (c : ℂ) : ℝ := 5 / 4 * greenFunctionDyn c 0

/-- The base piece `{G_c < s'}`. -/
def pieceBase (c : ℂ) : Set ℂ := {z | greenFunctionDyn c z < pieceLevel c}

theorem pieceLevel_lt_branchLevel (hc : c ∉ mandelbrot) : pieceLevel c < branchLevel c := by
  unfold pieceLevel branchLevel; linarith [greenFunctionDyn_zero_pos hc]

theorem greenFunctionDyn_zero_lt_pieceLevel (hc : c ∉ mandelbrot) :
    greenFunctionDyn c 0 < pieceLevel c := by
  unfold pieceLevel; linarith [greenFunctionDyn_zero_pos hc]

theorem pieceLevel_pos (hc : c ∉ mandelbrot) : 0 < pieceLevel c :=
  lt_of_le_of_lt (greenFunctionDyn_nonneg c 0) (greenFunctionDyn_zero_lt_pieceLevel hc)

theorem pieceBase_subset (hc : c ∉ mandelbrot) : pieceBase c ⊆ branchDomain c := fun _ hz =>
  lt_trans hz (pieceLevel_lt_branchLevel hc)

theorem filledJulia_subset_pieceBase (hc : c ∉ mandelbrot) : filledJulia c ⊆ pieceBase c :=
  fun z hz => by
    change greenFunctionDyn c z < pieceLevel c
    rw [(greenFunctionDyn_eq_zero_iff c z).mpr hz]
    exact pieceLevel_pos hc

/-- **Small pieces.**  Every point `q` of `K_c` (`c ∉ M`) has arbitrarily small open neighbourhoods
`E = g_w({G_c < s'})` with `E ∖ K_c` connected and nonempty, `E ∩ K_c = g_w(K_c)`, and a second
point of `K_c` in `E`. -/
theorem exists_small_piece (hc : c ∉ mandelbrot) {q : ℂ} (hq : q ∈ filledJulia c) {r : ℝ}
    (hr : 0 < r) :
    ∃ E : Set ℂ, IsOpen E ∧ q ∈ E ∧ E ⊆ ball q r ∧ IsPreconnected (E \ filledJulia c) ∧
      (E \ filledJulia c).Nonempty ∧ IsCompact (E ∩ filledJulia c) ∧
      ∃ q' ∈ filledJulia c ∩ E, q' ≠ q := by
  classical
  have ht₀ := greenFunctionDyn_zero_pos hc
  have hDo := isOpen_branchDomain c
  obtain ⟨ε, hε, B, hB, hdecay⟩ := exists_branchComp_deriv_decay hc
  -- a margin around the closed base piece
  have hL'c : IsCompact {z : ℂ | greenFunctionDyn c z ≤ pieceLevel c} :=
    isCompact_green_sublevel c _
  have hL'D : {z : ℂ | greenFunctionDyn c z ≤ pieceLevel c} ⊆ branchDomain c := fun z hz =>
    lt_of_le_of_lt (show greenFunctionDyn c z ≤ pieceLevel c from hz)
      (pieceLevel_lt_branchLevel hc)
  obtain ⟨ρ, hρ, hρD⟩ := hL'c.exists_cthickening_subset_open hDo hL'D
  obtain ⟨t, htL, htfin, hcov⟩ := hL'c.finite_cover_balls (e := ρ / 2) (by positivity)
  set N : ℕ := htfin.toFinset.card with hNdef
  -- the variation of a word on one ball of the cover
  have hvar : ∀ (w : List Bool), ∀ x ∈ t, ∀ y ∈ ball x (ρ / 2), ∀ y' ∈ ball x (ρ / 2),
      dist (branchComp hc w y) (branchComp hc w y') ≤ 4 * B / (1 + ε) ^ w.length := by
    intro w x hx y hy y' hy'
    have hballD : ∀ u ∈ ball x (ρ / 2), ball u (ρ / 2) ⊆ branchDomain c := by
      intro u hu v hv
      apply hρD
      apply mem_cthickening_of_dist_le v x ρ _ (htL hx)
      have := dist_triangle v u x
      rw [mem_ball] at hu hv
      linarith
    have hder : ∀ u ∈ ball x (ρ / 2), ‖deriv (branchComp hc w) u‖ ≤
        2 * B / (ρ / 2) / (1 + ε) ^ w.length := fun u hu =>
      hdecay w (by positivity) (hballD u hu)
    have hdiff : ∀ u ∈ ball x (ρ / 2), DifferentiableAt ℂ (branchComp hc w) u := fun u hu =>
      (branchComp_differentiableOn hc w).differentiableAt
        (hDo.mem_nhds (hballD u hu (mem_ball_self (by positivity))))
    have hmv := (convex_ball x (ρ / 2)).norm_image_sub_le_of_norm_deriv_le hdiff hder hy' hy
    rw [dist_eq_norm]
    have hyy : ‖y - y'‖ ≤ ρ := by
      have := dist_triangle y x y'
      rw [mem_ball] at hy hy'
      rw [← dist_eq_norm]
      linarith [dist_comm x y']
    calc ‖branchComp hc w y - branchComp hc w y'‖
        ≤ 2 * B / (ρ / 2) / (1 + ε) ^ w.length * ‖y - y'‖ := hmv
      _ ≤ 2 * B / (ρ / 2) / (1 + ε) ^ w.length * ρ :=
          mul_le_mul_of_nonneg_left hyy (by positivity)
      _ = 4 * B / (1 + ε) ^ w.length := by field_simp; ring
  -- a depth with small pieces
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (N * (4 * B) / r) (by linarith : (1:ℝ) < 1 + ε)
  obtain ⟨w, hwlen, hwq⟩ := exists_address hc hq n
  set F := branchComp hc w with hFdef
  set x₀ := (quadratic c)^[n] q with hx₀def
  have hx₀K : x₀ ∈ filledJulia c := (iterate_mem_filledJulia_iff c q n).mpr hq
  have hFD : MapsTo F (branchDomain c) (branchDomain c) := mapsTo_branchComp hc w
  have hFit : ∀ y ∈ branchDomain c, (quadratic c)^[n] (F y) = y := fun y hy => by
    rw [← hwlen]; exact iterate_branchComp hc w hy
  have hFinj : InjOn F (branchDomain c) := fun y hy y' hy' h => by
    rw [← hFit y hy, ← hFit y' hy', h]
  -- the diameter bound on the base piece
  have hdiam : ∀ y ∈ pieceBase c, ∀ y' ∈ pieceBase c, dist (F y) (F y') < r := by
    intro y hy y' hy'
    have hZ : IsPreconnected (pieceBase c) :=
      (isConnected_green_sublevel c (greenFunctionDyn_zero_lt_pieceLevel hc)).isPreconnected
    have hcov' : pieceBase c ⊆ ⋃ x ∈ htfin.toFinset, ball x (ρ / 2) := by
      intro z hz
      have := hcov (show greenFunctionDyn c z ≤ pieceLevel c from le_of_lt hz)
      simpa using this
    have hchain := dist_le_card_mul_of_cover htfin.toFinset hZ (fun _ _ => isOpen_ball) hcov'
      (F := F) (δ := 4 * B / (1 + ε) ^ w.length)
      (fun x hx u hu v hv => hvar w x (htfin.mem_toFinset.mp hx) u hu.1 v hv.1) hy hy'
    rw [hwlen] at hchain
    have hpow : 0 < (1 + ε) ^ n := by positivity
    have : (N : ℝ) * (4 * B / (1 + ε) ^ n) < r := by
      rw [mul_div_assoc', div_lt_iff₀ hpow]
      rw [div_lt_iff₀ hr] at hn
      linarith
    exact lt_of_le_of_lt hchain this
  -- the piece
  set E := F '' pieceBase c with hEdef
  have hFan : AnalyticOnNhd ℂ F (branchDomain c) :=
    (branchComp_differentiableOn hc w).analyticOnNhd hDo
  have hEo : IsOpen E := by
    rcases hFan.is_constant_or_isOpen (isPreconnected_branchDomain hc) with ⟨v, hv⟩ | hopen
    · exfalso
      have hq0 : q ≠ 0 := fun h => hc (show (0:ℂ) ∈ filledJulia c from h ▸ hq)
      have hx₀D : x₀ ∈ branchDomain c := filledJulia_subset_branchDomain hc hx₀K
      have hnx₀D : -x₀ ∈ branchDomain c :=
        filledJulia_subset_branchDomain hc ((neg_mem_filledJulia_iff c x₀).mpr hx₀K)
      have hx₀0 : x₀ ≠ 0 := fun h => hc (show (0:ℂ) ∈ filledJulia c from h ▸ hx₀K)
      have := hFinj hx₀D hnx₀D (by rw [hv x₀ hx₀D, hv (-x₀) hnx₀D])
      exact hx₀0 (by linear_combination this / 2)
    · exact hopen _ (pieceBase_subset hc) (isOpen_lt (continuous_greenFunctionDyn c)
        continuous_const)
  have hx₀P : x₀ ∈ pieceBase c := filledJulia_subset_pieceBase hc hx₀K
  have hqE : q ∈ E := ⟨x₀, hx₀P, hwq⟩
  have hEK : E \ filledJulia c = F '' (pieceBase c \ filledJulia c) := by
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hzK⟩
      refine ⟨y, ⟨hy, fun hyK => hzK ?_⟩, rfl⟩
      rw [← iterate_mem_filledJulia_iff c _ n, hFit y (pieceBase_subset hc hy)]
      exact hyK
    · rintro ⟨y, ⟨hy, hyK⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, fun hzK => hyK ?_⟩
      rw [← hFit y (pieceBase_subset hc hy)]
      exact (iterate_mem_filledJulia_iff c _ n).mpr hzK
  have hEKc : E ∩ filledJulia c = F '' filledJulia c := by
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hzK⟩
      refine ⟨y, ?_, rfl⟩
      rw [← hFit y (pieceBase_subset hc hy)]
      exact (iterate_mem_filledJulia_iff c _ n).mpr hzK
    · rintro ⟨y, hyK, rfl⟩
      refine ⟨⟨y, filledJulia_subset_pieceBase hc hyK, rfl⟩, ?_⟩
      rw [← iterate_mem_filledJulia_iff c _ n, hFit y (filledJulia_subset_branchDomain hc hyK)]
      exact hyK
  have hband : IsPreconnected (pieceBase c \ filledJulia c) := by
    have h := isPreconnected_green_band c (greenFunctionDyn_zero_lt_pieceLevel hc)
    convert h using 1
    ext z
    simp only [pieceBase, Set.mem_sdiff, mem_setOf_eq]
    rw [← greenFunctionDyn_eq_zero_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (Ne.symm h2), h1⟩,
      fun ⟨h1, h2⟩ => ⟨h2, h1.ne'⟩⟩
  have hbandne : (pieceBase c \ filledJulia c).Nonempty := by
    obtain ⟨zf, hzf⟩ := exists_green_gt c (pieceLevel c)
    have hivt := isPreconnected_univ.intermediate_value (mem_univ q) (mem_univ zf)
      (continuous_greenFunctionDyn c).continuousOn
    have hmid : pieceLevel c / 2 ∈ Icc (greenFunctionDyn c q) (greenFunctionDyn c zf) := by
      rw [(greenFunctionDyn_eq_zero_iff c q).mpr hq]
      constructor
      · linarith [pieceLevel_pos hc]
      · linarith [pieceLevel_pos hc]
    obtain ⟨z, -, hz⟩ := hivt hmid
    refine ⟨z, ?_, ?_⟩
    · change greenFunctionDyn c z < pieceLevel c
      rw [hz]; linarith [pieceLevel_pos hc]
    · rw [← greenFunctionDyn_eq_zero_iff, hz]
      exact (half_pos (pieceLevel_pos hc)).ne'
  refine ⟨E, hEo, hqE, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_ball, ← hwq]
    exact hdiam y hy x₀ hx₀P
  · rw [hEK]
    exact hband.image _ ((branchComp_differentiableOn hc w).continuousOn.mono
      (fun z hz => pieceBase_subset hc hz.1))
  · rw [hEK]; exact hbandne.image _
  · rw [hEKc]
    exact (isCompact_filledJulia c).image_of_continuousOn
      ((branchComp_differentiableOn hc w).continuousOn.mono
        (filledJulia_subset_branchDomain hc))
  · have hnx₀K : -x₀ ∈ filledJulia c := (neg_mem_filledJulia_iff c x₀).mpr hx₀K
    refine ⟨F (-x₀), ⟨?_, ⟨-x₀, filledJulia_subset_pieceBase hc hnx₀K, rfl⟩⟩, ?_⟩
    · rw [← iterate_mem_filledJulia_iff c _ n,
        hFit _ (filledJulia_subset_branchDomain hc hnx₀K)]
      exact hnx₀K
    · intro h
      have hx₀0 : x₀ ≠ 0 := fun h0 => hc (show (0:ℂ) ∈ filledJulia c from h0 ▸ hx₀K)
      have h' := congrArg (quadratic c)^[n] h
      rw [hFit _ (filledJulia_subset_branchDomain hc hnx₀K), ← hwq,
        hFit _ (filledJulia_subset_branchDomain hc hx₀K)] at h'
      exact hx₀0 (by linear_combination -h' / 2)

/-! ### Consequences -/

/-- **A disconnected filled Julia set has empty interior.** -/
theorem interior_filledJulia_eq_empty_of_not_mem_mandelbrot (hc : c ∉ mandelbrot) :
    interior (filledJulia c) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  obtain ⟨E, -, -, hEr, -, ⟨y, hyE, hyK⟩, -⟩ := exists_small_piece hc (interior_subset hz) hr
  exact hyK (interior_subset (hrK (hEr hyE)))

/-- **A disconnected filled Julia set has no isolated points.** -/
theorem filledJulia_no_isolated_of_not_mem_mandelbrot (hc : c ∉ mandelbrot) :
    ∀ y ∈ filledJulia c, ∀ ε > 0, ∃ y' ∈ filledJulia c, y' ≠ y ∧ y' ∈ ball y ε := by
  intro y hy ε hε
  obtain ⟨E, -, -, hEr, -, -, -, q', ⟨hq'K, hq'E⟩, hq'ne⟩ := exists_small_piece hc hy hε
  exact ⟨q', hq'K, hq'ne, hEr hq'E⟩

/-- **Fatou's theorem: a disconnected filled Julia set is totally disconnected.** -/
theorem isTotallyDisconnected_filledJulia_of_not_mem_mandelbrot (hc : c ∉ mandelbrot) :
    IsTotallyDisconnected (filledJulia c) := by
  intro S hSK hS a ha b hb
  by_contra hab
  have hd : 0 < dist a b := dist_pos.mpr hab
  obtain ⟨E, hEo, haE, hEr, -, -, hEKc, -⟩ := exists_small_piece hc (hSK ha) hd
  -- `E ∩ K` is clopen in `K`, so the preconnected `S ⊆ K` stays in `E`
  have hSE : S ⊆ E := by
    have hsub : S ⊆ E ∪ (E ∩ filledJulia c)ᶜ := fun x hx => by
      by_cases h : x ∈ E
      · exact Or.inl h
      · exact Or.inr (fun h' => h h'.1)
    have hdisj : ∀ x ∈ S, x ∈ E → x ∈ (E ∩ filledJulia c)ᶜ → False :=
      fun x hx h1 h2 => h2 ⟨h1, hSK hx⟩
    by_contra hnot
    obtain ⟨x, hxS, hxE⟩ := not_subset.mp hnot
    obtain ⟨y, hyS, hy1, hy2⟩ := hS E (E ∩ filledJulia c)ᶜ hEo hEKc.isClosed.isOpen_compl hsub
      ⟨a, ha, haE⟩ ⟨x, hxS, fun h => hxE h.1⟩
    exact hdisj y hyS hy1 hy2
  have := hEr (hSE hb)
  rw [mem_ball, dist_comm] at this
  exact lt_irrefl _ this

end Bottcher
