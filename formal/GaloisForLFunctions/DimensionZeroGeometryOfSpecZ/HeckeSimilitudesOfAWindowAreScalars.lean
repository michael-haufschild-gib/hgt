import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheTateTwistIsTheShiftedPair
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowDatum

/-!
# Hecke similitudes of a window are scalars

Weil's argument over `𝔽_q` combines Rosati positivity with a Frobenius that is a *similitude* of the
intersection form (`F^†F = q`). On a window `W_A` the Hecke operators form the window algebra
`ρ_A(𝒜)` (the Dirichlet ring truncated at `⌊e^A⌋`, WTZ), and the reflection `σ_A` is its Rosati
involution. This module answers whether the window algebra contains a Frobenius.

**Theorem** (`windowRep_similitude`). Let `A > 0` and suppose `ρ_A(f)` is a similitude of Weil's form
with factor `λ` on window tests: `Q(ρ_A(f)H) = λQ(H)` whenever `H` and `ρ_A(f)H` are window tests.
Then `λ = f(1)²` and `f(n) = 0` for every `2 ≤ n < e^A`: the Hecke similitudes of a window are the
scalars. In particular the `Q`-isometries of the window algebra are `±1`
(`windowRep_isometry`).

*Proof.* Short bumps carry strictly positive Weil energy (`exists_short_bump`, from the coercivity of
`Q` on tests supported in `[−3/10, 3/10]`), and `Q` is translation invariant. A bump `B_r` at the
right end is killed by every shift, so `ρ_A(f)B_r = f(1)B_r` and `λ = f(1)²`. If `n₀` is the first
active index with `f(n₀) ≠ 0`, a bump `B_l` at distance `log n₀` from the right end is moved by
exactly one shift onto `B_r`: `ρ_A(f)(αB_l + βB_r) = f(1)αB_l + (f(1)β + cα)B_r`, `c = f(n₀)n₀^{−1/2}`
(`windowRepFun_plane`). The similitude identity on `B_l` and on `B_l + B_r` gives
`2f(1)c·Q(B_r) = 0` and then `c²Q(B_r) = 0`, so `c = 0`.

No positivity of `Q` beyond short bumps is used, and the statement holds for every Euler datum whose
Weil form is coercive on short tests: the obstruction is the triangular (Volterra) shape of the
window algebra, whose elements are `f(1)` plus a nilpotent that moves mass only toward the right end.
A Frobenius for windows must come from outside the window algebra — the reflection `σ_A`, which is a
`Q`-isometry (`weilQuad_windowReflection`), or operators changing the window (dilations, Adams lifts).
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open ArithmeticCastelnuovoSeveri CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis
open WindowTowerOfSpecZ

/-! ### Weil's form on a plane -/

theorem weilPair_smul_right (c : ℝ) (f g : ℝ → ℝ) : weilPair f (c • g) = c * weilPair f g := by
  rw [weilPair_comm, weilPair_smul_left, weilPair_comm]

/-- `Q(αh + βe) = α²Q(h) + 2αβW(h, e) + β²Q(e)`. -/
theorem weilQuad_plane {h e : ℝ → ℝ} (hh : h ∈ realTests) (he : e ∈ realTests) (α β : ℝ) :
    weilQuad (fun u => α * h u + β * e u) =
      α ^ 2 * weilQuad h + 2 * α * β * weilPair h e + β ^ 2 * weilQuad e := by
  have h1 : α • h ∈ realTests := realTests.smul_mem α hh
  have h2 : β • e ∈ realTests := realTests.smul_mem β he
  have h12 := realTests.add_mem h1 h2
  have hfun : (fun u => α * h u + β * e u) = α • h + β • e := by
    funext u; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  show weilPair (α • h + β • e) (α • h + β • e) =
    α ^ 2 * weilPair h h + 2 * α * β * weilPair h e + β ^ 2 * weilPair e e
  rw [weilPair_add_left h1 h2 h12, weilPair_comm (α • h), weilPair_comm (β • e),
    weilPair_add_left h1 h2 h1, weilPair_add_left h1 h2 h2]
  simp only [weilPair_smul_left, weilPair_smul_right]
  rw [weilPair_comm e h]
  ring

/-- `Q(cH) = c²Q(H)`. -/
theorem weilQuad_mul_left (c : ℝ) (H : ℝ → ℝ) : weilQuad (fun u => c * H u) = c ^ 2 * weilQuad H := by
  have h : (fun u => c * H u) = c • H := by funext u; simp [smul_eq_mul]
  rw [h]
  show weilPair (c • H) (c • H) = c ^ 2 * weilPair H H
  rw [weilPair_smul_left, weilPair_smul_right]
  ring

/-! ### Short bumps -/

/-- **A short bump has positive Weil energy**: a nonzero smooth bump supported in `[−ρ, ρ]`,
`ρ ≤ 3/10`, with `Q(b) > 0`. -/
theorem exists_short_bump {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 3 / 10) :
    ∃ b : ℝ → ℝ, b ∈ realTests ∧ (∀ u, ρ ≤ |u| → b u = 0) ∧ 0 < weilQuad b := by
  let φ : ContDiffBump (0 : ℝ) := ⟨ρ / 2, ρ, half_pos hρ, half_lt_self hρ⟩
  have hzero : ∀ u, ρ ≤ |u| → φ u = 0 := fun u hu => φ.zero_of_le_dist (by
    show ρ ≤ dist u 0
    rwa [Real.dist_eq, sub_zero])
  have hout : ∀ u, u ∉ Icc (-ρ) ρ → φ u = 0 := fun u hu => hzero u (by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith)
  have hcs : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hout
  have hmem : (φ : ℝ → ℝ) ∈ realTests := ⟨φ.contDiff, hcs⟩
  refine ⟨φ, hmem, hzero, ?_⟩
  have hsupp : tsupport φ ⊆ Icc (-(3 / 10)) (3 / 10) := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    by_contra h
    exact hu (hout u fun h' => h ⟨by linarith [h'.1], by linarith [h'.2]⟩)
  have hpos : 0 < ∫ u, (φ u) ^ 2 :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (hmem.1.continuous.pow 2)
      (HasCompactSupport.intro isCompact_Icc fun u hu => by
        show φ u ^ 2 = 0
        rw [hout u hu]; norm_num) (fun u => sq_nonneg _)
      (by
        show φ 0 ^ 2 ≠ 0
        rw [φ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_self]; exact (half_pos hρ).le)]
        norm_num)
  have h := LatticeSectionTheory.WindowJumpCounts.weilPair_ge_of_le_threeTenths hmem hsupp le_rfl
  show 0 < weilPair φ φ
  nlinarith

/-! ### Bumps on a window and their shifts -/

variable {b : ℝ → ℝ} {ρ : ℝ}

/-- The bump `b` moved to the centre `−(ρ + ℓ)`: supported in `[−2ρ − ℓ, −ℓ]`. -/
def bumpAt (b : ℝ → ℝ) (ρ ℓ : ℝ) : ℝ → ℝ := fun u => b (u - -(ρ + ℓ))

theorem bumpAt_eq_zero_of_ge (hb : ∀ u, ρ ≤ |u| → b u = 0) {ℓ u : ℝ} (hu : -ℓ ≤ u) :
    bumpAt b ρ ℓ u = 0 :=
  hb _ ((by linarith : ρ ≤ u - -(ρ + ℓ)).trans (le_abs_self _))

theorem bumpAt_eq_zero_of_le (hb : ∀ u, ρ ≤ |u| → b u = 0) {ℓ u : ℝ} (hu : u ≤ -2 * ρ - ℓ) :
    bumpAt b ρ ℓ u = 0 :=
  hb _ ((by linarith : ρ ≤ -(u - -(ρ + ℓ))).trans (neg_le_abs _))

/-- A shift by `t ≤ ℓ` moves the bump at `ℓ` to the bump at `ℓ − t`. -/
theorem windowShift_bumpAt (hb : ∀ u, ρ ≤ |u| → b u = 0) (ℓ t : ℝ) (htℓ : t ≤ ℓ) (u : ℝ) :
    windowShift t (bumpAt b ρ ℓ) u = bumpAt b ρ (ℓ - t) u := by
  rcases le_or_gt u 0 with hu | hu
  · rw [windowShift_apply_of_le _ hu]
    simp only [bumpAt]
    congr 1
    ring
  · rw [windowShift_apply_of_pos _ hu]
    exact (bumpAt_eq_zero_of_ge hb (by linarith)).symm

/-- A shift by `t ≥ ℓ + 2ρ` moves the bump at `ℓ` out of the window. -/
theorem windowShift_bumpAt_eq_zero (hb : ∀ u, ρ ≤ |u| → b u = 0) (ℓ t : ℝ)
    (ht : 2 * ρ ≤ t - ℓ) (u : ℝ) : windowShift t (bumpAt b ρ ℓ) u = 0 := by
  rcases le_or_gt u 0 with hu | hu
  · rw [windowShift_apply_of_le _ hu]
    exact hb _ ((by linarith : ρ ≤ -(u - t - -(ρ + ℓ))).trans (neg_le_abs _))
  · exact windowShift_apply_of_pos _ hu

theorem windowShift_plane (t : ℝ) (F G : ℝ → ℝ) (α β u : ℝ) :
    windowShift t (fun v => α * F v + β * G v) u = α * windowShift t F u + β * windowShift t G u := by
  rcases le_or_gt u 0 with hu | hu
  · simp only [windowShift_apply_of_le _ hu]
  · simp only [windowShift_apply_of_pos _ hu]; ring

theorem bumpAt_mem_realTests (hb : ∀ u, ρ ≤ |u| → b u = 0) (hbt : b ∈ realTests) (ℓ : ℝ) :
    bumpAt b ρ ℓ ∈ realTests :=
  ⟨hbt.1.comp (contDiff_id.sub contDiff_const),
    HasCompactSupport.intro (isCompact_Icc (a := -2 * ρ - ℓ) (b := -ℓ)) fun u hu => by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · exact bumpAt_eq_zero_of_le hb h.le
      · exact bumpAt_eq_zero_of_ge hb h.le⟩

theorem weilQuad_bumpAt (b : ℝ → ℝ) (ρ ℓ : ℝ) : weilQuad (bumpAt b ρ ℓ) = weilQuad b :=
  weilQuad_comp_sub b (-(ρ + ℓ))

/-- The bump at `ℓ ≥ 0` is a window test as soon as `2ρ + ℓ ≤ A`. -/
theorem isWindowTest_bumpAt {A : ℝ} (hb : ∀ u, ρ ≤ |u| → b u = 0) (hbt : b ∈ realTests)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hA : 2 * ρ + ℓ ≤ A) : IsWindowTest A (bumpAt b ρ ℓ) :=
  ⟨(bumpAt_mem_realTests hb hbt ℓ).1, fun y hy => by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with h | h
    · exact bumpAt_eq_zero_of_le hb (by linarith)
    · exact bumpAt_eq_zero_of_ge hb (by linarith)⟩

/-- Window tests form a vector space. -/
theorem isWindowTest_lin {A : ℝ} {F G : ℝ → ℝ} (hF : IsWindowTest A F) (hG : IsWindowTest A G)
    (α β : ℝ) : IsWindowTest A (fun u => α * F u + β * G u) :=
  ⟨(contDiff_const.mul hF.contDiff).add (contDiff_const.mul hG.contDiff), fun y hy => by
    rw [hF.vanish y hy, hG.vanish y hy]; ring⟩

theorem one_mem_Icc_windowLevel {A : ℝ} (hA : 0 ≤ A) : (1 : ℕ) ∈ Finset.Icc 1 (windowLevel A) :=
  Finset.mem_Icc.mpr ⟨le_rfl, by
    rw [windowLevel, Nat.le_floor_iff (Real.exp_pos A).le]
    simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr hA⟩

theorem log_two_le_log {n : ℕ} (hn : 2 ≤ n) : Real.log 2 ≤ Real.log n :=
  Real.log_le_log (by norm_num) (by exact_mod_cast hn)

/-- **A right-end bump is an eigenvector of every Hecke operator**: `ρ_A(f)B_r = f(1)B_r` when
`2ρ ≤ log 2`. -/
theorem windowRepFun_rightBump {A : ℝ} (hA : 0 ≤ A) (hρ2 : 2 * ρ ≤ Real.log 2)
    (hb : ∀ u, ρ ≤ |u| → b u = 0) (f : ArithmeticFunction ℝ) :
    windowRepFun A f (bumpAt b ρ 0) = fun u => f 1 * bumpAt b ρ 0 u := by
  funext u
  rw [windowRepFun, Finset.sum_eq_single_of_mem 1 (one_mem_Icc_windowLevel hA)]
  · simp only [Nat.cast_one, Real.sqrt_one, div_one, Real.log_one,
      windowShift_bumpAt hb 0 0 le_rfl, sub_zero]
  · intro n hn hn1
    have h2 : 2 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [windowShift_bumpAt_eq_zero hb 0 (Real.log n) (by linarith [log_two_le_log h2]),
      mul_zero]

/-- **The image of the plane.** If `f(n) = 0` for `2 ≤ n < m`, then on the plane spanned by the
bump at `log m` and the right-end bump, `ρ_A(f)(αB_l + βB_r) = f(1)αB_l + (f(1)β + cα)B_r`,
`c = f(m)m^{−1/2}`. -/
theorem windowRepFun_plane {A : ℝ} (hA : 0 ≤ A) (hb : ∀ u, ρ ≤ |u| → b u = 0)
    (f : ArithmeticFunction ℝ) {m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ windowLevel A)
    (hρ2 : 2 * ρ ≤ Real.log 2) (hρm : 2 * ρ ≤ Real.log (m + 1) - Real.log m)
    (hf : ∀ n, 2 ≤ n → n < m → f n = 0) (α β : ℝ) :
    windowRepFun A f (fun u => α * bumpAt b ρ (Real.log m) u + β * bumpAt b ρ 0 u) =
      fun u => f 1 * α * bumpAt b ρ (Real.log m) u +
        (f 1 * β + f m / Real.sqrt m * α) * bumpAt b ρ 0 u := by
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hm1 : m ∈ Finset.Icc 1 (windowLevel A) := Finset.mem_Icc.mpr ⟨by omega, hmN⟩
  funext u
  have hterm : ∀ n ∈ Finset.Icc 1 (windowLevel A), f n / Real.sqrt n *
      windowShift (Real.log n) (fun v => α * bumpAt b ρ (Real.log m) v + β * bumpAt b ρ 0 v) u =
      (if n = 1 then f 1 * (α * bumpAt b ρ (Real.log m) u + β * bumpAt b ρ 0 u) else 0) +
        (if n = m then f m / Real.sqrt m * α * bumpAt b ρ 0 u else 0) := by
    intro n hn
    rw [windowShift_plane]
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [if_pos rfl, if_neg (show (1 : ℕ) ≠ m by omega)]
      simp only [Nat.cast_one, Real.sqrt_one, div_one, Real.log_one,
        windowShift_bumpAt hb (Real.log m) 0 hlogm, windowShift_bumpAt hb 0 0 le_rfl, sub_zero,
        add_zero]
    have h2 : 2 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [if_neg hn1, zero_add]
    rcases lt_trichotomy n m with hlt | heq | hgt
    · rw [if_neg hlt.ne, hf n h2 hlt, zero_div, zero_mul]
    · rw [if_pos heq, heq, windowShift_bumpAt hb (Real.log m) (Real.log m) le_rfl, sub_self,
        windowShift_bumpAt_eq_zero hb 0 (Real.log m) (by linarith [log_two_le_log hm])]
      ring
    · have hmn : Real.log (m + 1) ≤ Real.log n :=
        Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_of_lt hgt)
      rw [if_neg hgt.ne', windowShift_bumpAt_eq_zero hb 0 (Real.log n)
          (by linarith [log_two_le_log h2]),
        windowShift_bumpAt_eq_zero hb (Real.log m) (Real.log n) (by linarith)]
      ring
  rw [windowRepFun, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_ite_eq' _ _ (fun _ => f 1 * (α * bumpAt b ρ (Real.log m) u + β * bumpAt b ρ 0 u)),
    Finset.sum_ite_eq' _ _ (fun _ => f m / Real.sqrt m * α * bumpAt b ρ 0 u),
    if_pos (one_mem_Icc_windowLevel hA), if_pos hm1]
  ring

/-! ### The theorem -/

/-- **Hecke similitudes of a window are scalars.** If `Q(ρ_A(f)H) = λQ(H)` for all window tests `H`
with `ρ_A(f)H` a window test, then `λ = f(1)²` and `f(n) = 0` for `2 ≤ n < e^A`. -/
theorem windowRep_similitude {A : ℝ} (hA : 0 < A) (f : ArithmeticFunction ℝ) {lam : ℝ}
    (hsim : ∀ H, IsWindowTest A H → IsWindowTest A (windowRepFun A f H) →
      weilQuad (windowRepFun A f H) = lam * weilQuad H) :
    lam = f 1 ^ 2 ∧ ∀ n : ℕ, 2 ≤ n → (n : ℝ) < Real.exp A → f n = 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the factor: a right-end bump is an eigenvector
  have hlam : lam = f 1 ^ 2 := by
    set ρ := min (min A (Real.log 2)) (3 / 5) / 4 with hρdef
    have hmin1 := min_le_left (min A (Real.log 2)) (3 / 5)
    have hmin2 := min_le_right (min A (Real.log 2)) (3 / 5)
    have hmin3 := min_le_left A (Real.log 2)
    have hmin4 := min_le_right A (Real.log 2)
    have hρ : 0 < ρ := by
      have : 0 < min (min A (Real.log 2)) (3 / 5) := lt_min (lt_min hA hlog2) (by norm_num)
      positivity
    obtain ⟨b, hbt, hb, hq⟩ := exists_short_bump hρ (by rw [hρdef]; linarith)
    have hρ2 : 2 * ρ ≤ Real.log 2 := by rw [hρdef]; linarith
    have hρA : 2 * ρ + 0 ≤ A := by rw [hρdef]; linarith
    have hBr := isWindowTest_bumpAt hb hbt le_rfl hρA
    have himg := windowRepFun_rightBump hA.le hρ2 hb f
    have hwin' : IsWindowTest A (windowRepFun A f (bumpAt b ρ 0)) := by
      rw [himg]
      exact ⟨contDiff_const.mul hBr.contDiff, fun y hy => by rw [hBr.vanish y hy, mul_zero]⟩
    have h := hsim _ hBr hwin'
    rw [himg, weilQuad_mul_left, weilQuad_bumpAt] at h
    have h' : (f 1 ^ 2 - lam) * weilQuad b = 0 := by rw [sub_mul]; linarith
    have := (mul_eq_zero.mp h').resolve_right hq.ne'
    linarith
  refine ⟨hlam, ?_⟩
  -- the coefficients: the first active one is forced to vanish
  by_contra hex
  push Not at hex
  classical
  have hP : ∃ n : ℕ, 2 ≤ n ∧ (n : ℝ) < Real.exp A ∧ f n ≠ 0 := hex
  set m := Nat.find hP with hmdef
  obtain ⟨hm2, hmA, hfm⟩ := Nat.find_spec hP
  have hmin : ∀ n, 2 ≤ n → n < m → f n = 0 := fun n h2 hlt => by
    by_contra hne
    exact Nat.find_min hP hlt ⟨h2, by
      have : (n : ℝ) < m := by exact_mod_cast hlt
      linarith, hne⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmN : m ≤ windowLevel A := Nat.le_floor hmA.le
  have hℓA : Real.log m < A := (Real.log_lt_iff_lt_exp hm0).mpr hmA
  have hℓ0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hgap : 0 < Real.log (m + 1) - Real.log m :=
    sub_pos.mpr (Real.log_lt_log hm0 (by linarith))
  set ρ := min (min (A - Real.log m) (Real.log (m + 1) - Real.log m))
    (min (Real.log 2) (3 / 5)) / 4 with hρdef
  have hρ : 0 < ρ := by
    have : 0 < min (min (A - Real.log m) (Real.log (m + 1) - Real.log m))
        (min (Real.log 2) (3 / 5)) :=
      lt_min (lt_min (by linarith) hgap) (lt_min hlog2 (by norm_num))
    positivity
  have hmins := min_le_left (min (A - Real.log m) (Real.log (m + 1) - Real.log m))
    (min (Real.log 2) (3 / 5))
  have hmins' := min_le_right (min (A - Real.log m) (Real.log (m + 1) - Real.log m))
    (min (Real.log 2) (3 / 5))
  have h1 := min_le_left (A - Real.log m) (Real.log (m + 1) - Real.log m)
  have h2 := min_le_right (A - Real.log m) (Real.log (m + 1) - Real.log m)
  have h3 := min_le_left (Real.log 2) (3 / 5)
  have h4 := min_le_right (Real.log 2) (3 / 5 : ℝ)
  have hρ3 : ρ ≤ 3 / 10 := by rw [hρdef]; linarith
  have hρ2 : 2 * ρ ≤ Real.log 2 := by rw [hρdef]; linarith
  have hρm : 2 * ρ ≤ Real.log (m + 1) - Real.log m := by rw [hρdef]; linarith
  have hρA : 2 * ρ + Real.log m ≤ A := by rw [hρdef]; linarith
  obtain ⟨b, hbt, hb, hq⟩ := exists_short_bump hρ hρ3
  have himg := windowRepFun_plane hA.le hb f hm2 hmN hρ2 hρm hmin
  have hBlw := isWindowTest_bumpAt hb hbt hℓ0 hρA
  have hBrw := isWindowTest_bumpAt hb hbt le_rfl (by linarith : 2 * ρ + 0 ≤ A)
  have hBl := bumpAt_mem_realTests hb hbt (Real.log m)
  have hBr := bumpAt_mem_realTests hb hbt 0
  set c := f m / Real.sqrt m with hc
  set p := weilPair (bumpAt b ρ (Real.log m)) (bumpAt b ρ 0) with hp
  have hQ : ∀ α β : ℝ, weilQuad (fun u => α * bumpAt b ρ (Real.log m) u + β * bumpAt b ρ 0 u) =
      (α ^ 2 + β ^ 2) * weilQuad b + 2 * α * β * p := fun α β => by
    rw [weilQuad_plane hBl hBr, weilQuad_bumpAt, weilQuad_bumpAt]; ring
  have hsimab : ∀ α β : ℝ, weilQuad (fun u => f 1 * α * bumpAt b ρ (Real.log m) u +
      (f 1 * β + c * α) * bumpAt b ρ 0 u) =
        lam * weilQuad (fun u => α * bumpAt b ρ (Real.log m) u + β * bumpAt b ρ 0 u) :=
    fun α β => by
      have h := hsim _ (isWindowTest_lin hBlw hBrw α β)
        (by rw [himg α β]; exact isWindowTest_lin hBlw hBrw _ _)
      rwa [himg α β] at h
  have E1 := hsimab 1 0
  have E2 := hsimab 1 1
  rw [hQ, hQ, hlam] at E1
  rw [hQ, hQ, hlam] at E2
  have hfc : f 1 * c * weilQuad b = 0 := by linear_combination (E2 - E1) / 2
  have hfc' : f 1 * c = 0 := (mul_eq_zero.mp hfc).resolve_right hq.ne'
  have hcc : c ^ 2 * weilQuad b = 0 := by linear_combination E1 - 2 * p * hfc'
  have hc0 : c = 0 := (pow_eq_zero_iff two_ne_zero).mp
    ((mul_eq_zero.mp hcc).resolve_right hq.ne')
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  rw [hc, div_eq_zero_iff] at hc0
  exact hfm (hc0.resolve_right hsq.ne')

/-- **The `Q`-isometries of the window algebra are `±1`.** -/
theorem windowRep_isometry {A : ℝ} (hA : 0 < A) (f : ArithmeticFunction ℝ)
    (hiso : ∀ H, IsWindowTest A H → IsWindowTest A (windowRepFun A f H) →
      weilQuad (windowRepFun A f H) = weilQuad H) :
    (f 1 = 1 ∨ f 1 = -1) ∧ ∀ n : ℕ, 2 ≤ n → (n : ℝ) < Real.exp A → f n = 0 := by
  obtain ⟨h1, h2⟩ := windowRep_similitude hA f (lam := 1) fun H hH hSH => by
    rw [one_mul]; exact hiso H hH hSH
  refine ⟨?_, h2⟩
  have : (f 1 - 1) * (f 1 + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- **The reflection is an isometry**: `Q(H(−A − ·)) = Q(H)`. The Rosati involution of the window
algebra lies outside it and preserves Weil's form. -/
theorem weilQuad_windowReflection (A : ℝ) (H : ℝ → ℝ) :
    weilQuad (fun u => H (-A - u)) = weilQuad H := by
  have h1 := weilQuad_comp_neg (fun u => H (u - A))
  rw [weilQuad_comp_sub H A] at h1
  rw [← h1]
  congr 1
  funext u
  ring_nf

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
