import GaloisForLFunctions.RHTower.PrimeBlindPoleWeightLevelWindow

/-!
# Prime-blind positivity at a finite level is a finite Farkas problem

Fix a level `L` and consider the tests supported in `[−L, L]` (`LevelTest L`).  Their
autocorrelations live on `[−2L, 2L]`, so only the nodes `log n < 2L` carry node values.  This
module proves the finite-level Farkas lemma: for every per-test functional `Φ : WeilTestFn → ℝ`,

  `Φ ≥ 0` on all nonnegative blind combinations of level-`L` tests
  ⟺ there are node weights `lam` with `Σ_n lam(n) ℓ_n(f) ≤ Φ(f)` for every level-`L` test `f`

(`levelBlindNonneg_iff_exists_weights`).  The weights may be taken supported on the finitely many
nodes `log n < 2L`.

**Producers.**  Each node `log n < 2L` is reached at level `L` with both signs by a two-bump test:
the narrow bump of node `n` placed at `±log n / 2` when that fits (`log n ≤ 2L − 2r_n`), and at the
two ends `±(L − r_n)` otherwise (`pairTestAt`, `levelPairTestFn`).  The node value of the two-bump
test with centres `a < b` is `σ (K(log n − d) + K(d − log n))/√n`, `d = b − a`, where `K` is the
autocorrelation of the bump, as soon as `|d − log n| < 2 r_n` (`logValue_pairTestAt`); the gap
`|log m − log n| ≥ 1/(n+1) = 4 r_n` between distinct nodes kills every other node value.

**Value function.**  `levelValue L Φ v = inf {Φ(c) : c ≥ 0, level L, node vector = π_L v}` with
`π_L` the projection onto the nodes `log n < 2L` is finite and sublinear once `Φ ≥ 0` on the blind
level-`L` combinations; a linear minorant exists (Hahn–Banach, `exists_extension_of_le_sublinear`)
and its values at the unit vectors are the weights.

**Instances.**
* `primeBlindPositiveAtLevel_iff_exists_weights`: blind positivity at level `L` with pole weight
  `β` ⟺ some node weights are Weil-positive at pole weight `β` on all level-`L` tests.
* `levelFloors_eq_levelMargins`: the uniform floors `m` with `A_β(c) ≥ m·mass(c)` on blind level-`L`
  combinations are exactly the margins `m` of level-`L` Weil forms `A_β − Σ lam ℓ ≥ m‖f‖²` (strong
  duality as an equality of sets).
* `riemannHypothesis_iff_forall_level_exists_weights`,
  `riemannHypothesis_iff_forall_level_exists_weights_one`: RH ⟺ at every level some node weights
  (and some pole weight, or the pole weight `1`) give a Weil-positive form on the level-`L` tests.
-/

open Complex MeasureTheory Set Finsupp Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-! ## The narrow bump: radius and autocorrelation -/

/-- The radius `1/(4(j+1))` of the narrow bump of node `j`. -/
def bumpRadius (j : ℕ) : ℝ := 1 / (4 * ((j : ℝ) + 1))

theorem bumpRadius_pos (j : ℕ) : 0 < bumpRadius j := by unfold bumpRadius; positivity

theorem bumpRadius_le (j : ℕ) : bumpRadius j ≤ 1 / 4 := by
  unfold bumpRadius
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

theorem two_bumpRadius_lt_log_two (j : ℕ) : 2 * bumpRadius j < Real.log 2 := by
  have := bumpRadius_le j
  linarith [WeilExcess.seventeen_div_twentyfive_lt_log_two]

theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  linarith [WeilExcess.seventeen_div_twentyfive_lt_log_two]

theorem four_mul_bumpRadius (j : ℕ) : 4 * bumpRadius j = 1 / ((j : ℝ) + 1) := by
  unfold bumpRadius; field_simp

theorem weilTest_narrowBumpC_eq_zero' (j : ℕ) {Y : ℝ} (hY : 2 * bumpRadius j < |Y|) :
    EF.weilTest (narrowBumpC j) (narrowBumpC j) Y = 0 :=
  weilTest_self_eq_zero (fun _ hu => narrowBumpC_eq_zero j hu) hY

/-- The autocorrelation `K(x) = ∫ h_j(t) h_j(t − x) dt` of the real narrow bump. -/
def bumpCorr (j : ℕ) (x : ℝ) : ℝ := ∫ t, narrowBump j t * narrowBump j (t - x)

theorem weilTest_narrowBumpC_eq (j : ℕ) (x : ℝ) :
    EF.weilTest (narrowBumpC j) (narrowBumpC j) x = ((bumpCorr j x : ℝ) : ℂ) := by
  simp only [EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply', EF.tilde, neg_sub,
    narrowBumpC, Complex.conj_ofReal]
  rw [bumpCorr, ← integral_complex_ofReal]
  congr 1
  funext t
  push_cast
  ring

/-- The bump autocorrelation is positive at lags below the diameter. -/
theorem bumpCorr_pos (j : ℕ) {x : ℝ} (hx : |x| < 2 * bumpRadius j) : 0 < bumpCorr j x := by
  have hr : (narrowBump j).rOut = bumpRadius j := rfl
  have hc : Continuous fun t => narrowBump j t * narrowBump j (t - x) :=
    (narrowBump j).continuous.mul
      ((narrowBump j).continuous.comp (continuous_id.sub continuous_const))
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (narrowBump j).hasCompactSupport.mul_right
    (fun t => mul_nonneg (narrowBump j).nonneg (narrowBump j).nonneg) (x := x / 2) ?_
  have h1 : 0 < narrowBump j (x / 2) := by
    apply (narrowBump j).pos_of_mem_ball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hr, abs_div, abs_two]
    linarith
  have h2 : 0 < narrowBump j (x / 2 - x) := by
    apply (narrowBump j).pos_of_mem_ball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hr,
      show x / 2 - x = -(x / 2) by ring, abs_neg, abs_div, abs_two]
    linarith
  exact (mul_pos h1 h2).ne'

/-! ## Two bumps with prescribed centres -/

/-- The two-bump test `h_j(u − a) + σ h_j(u − b)`. -/
def pairTestAt (j : ℕ) (σ a b : ℝ) (u : ℝ) : ℂ :=
  narrowBumpC j (u - a) + (σ : ℂ) * narrowBumpC j (u - b)

theorem pairTestAt_eq_sum (j : ℕ) (σ a b : ℝ) :
    pairTestAt j σ a b = fun u => ∑ m ∈ Finset.range 2,
      (if m = 0 then (1 : ℂ) else (σ : ℂ)) * narrowBumpC j (u - if m = 0 then a else b) := by
  funext u
  simp [pairTestAt, Finset.sum_range_succ]

theorem contDiff_pairTestAt (j : ℕ) (σ a b : ℝ) : ContDiff ℝ 2 (pairTestAt j σ a b) :=
  (((contDiff_narrowBumpC j).of_le (by norm_cast)).comp (contDiff_id.sub contDiff_const)).add
    (contDiff_const.mul (((contDiff_narrowBumpC j).of_le (by norm_cast)).comp
      (contDiff_id.sub contDiff_const)))

theorem hasCompactSupport_pairTestAt (j : ℕ) (σ a b : ℝ) :
    HasCompactSupport (pairTestAt j σ a b) :=
  ((hasCompactSupport_narrowBumpC j).comp_homeomorph (Homeomorph.subRight a)).add
    (((hasCompactSupport_narrowBumpC j).comp_homeomorph (Homeomorph.subRight b)).mul_left)

/-- The two-bump test as a Weil test. -/
def pairTestAtFn (j : ℕ) (σ a b : ℝ) : WeilTestFn :=
  ⟨pairTestAt j σ a b, contDiff_pairTestAt j σ a b, hasCompactSupport_pairTestAt j σ a b⟩

theorem pairTestAt_eq_zero (j : ℕ) (σ a b : ℝ) {u : ℝ} (ha : bumpRadius j < |u - a|)
    (hb : bumpRadius j < |u - b|) : pairTestAt j σ a b u = 0 := by
  simp [pairTestAt, narrowBumpC_eq_zero j ha, narrowBumpC_eq_zero j hb]

/-- The two-bump test has level `max(|a|, |b|) + r_j`. -/
theorem levelTest_pairTestAtFn {j : ℕ} {σ a b L : ℝ} (ha : |a| + bumpRadius j ≤ L)
    (hb : |b| + bumpRadius j ≤ L) : LevelTest L (pairTestAtFn j σ a b) := by
  intro u hu
  by_contra hL
  push Not at hL
  apply hu
  apply pairTestAt_eq_zero
  · have := abs_sub_abs_le_abs_sub u a; linarith
  · have := abs_sub_abs_le_abs_sub u b; linarith

/-- The autocorrelation of a two-bump test. -/
theorem weilTest_pairTestAt (j : ℕ) (σ a b : ℝ) (y : ℝ) :
    EF.weilTest (pairTestAt j σ a b) (pairTestAt j σ a b) y =
      (1 + σ ^ 2 : ℝ) * EF.weilTest (narrowBumpC j) (narrowBumpC j) y +
        (σ : ℂ) * (EF.weilTest (narrowBumpC j) (narrowBumpC j) (y - a + b) +
          EF.weilTest (narrowBumpC j) (narrowBumpC j) (y - b + a)) := by
  rw [pairTestAt_eq_sum, weilTest_sum_translates (contDiff_narrowBumpC j).continuous
    (hasCompactSupport_narrowBumpC j)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_true, one_ne_zero,
    if_false, Complex.conj_ofReal, map_one, mul_one, one_mul]
  rw [show y - a + a = y by ring, show y - b + b = y by ring]
  push_cast
  ring

/-- **Node values of a two-bump test.**  If the centre distance `d = b − a` is within `2 r_j` of
`log j`, the only node value is at `j`, and it is `σ (K(log j − d) + K(d − log j))/√j`. -/
theorem logValue_pairTestAt {j : ℕ} (hj : 2 ≤ j) (σ a b : ℝ)
    (hd : |b - a - Real.log j| < 2 * bumpRadius j) {m : ℕ} (hm : 2 ≤ m) :
    logValue (pairTestAt j σ a b) m =
      if m = j then
        σ * (bumpCorr j (Real.log j - (b - a)) + bumpCorr j (b - a - Real.log j)) / Real.sqrt j
      else 0 := by
  have hH := fun Y => weilTest_narrowBumpC_eq_zero' j (Y := Y)
  have hlog2 : ∀ n : ℕ, 2 ≤ n → Real.log 2 ≤ Real.log n := fun n hn =>
    Real.log_le_log two_pos (by exact_mod_cast hn)
  have hr := two_bumpRadius_lt_log_two j
  have hrpos := bumpRadius_pos j
  have hm2 := hlog2 m hm
  have hj2 := hlog2 j hj
  obtain ⟨hd1, hd2⟩ := abs_lt.mp hd
  have hdpos : 0 < b - a := by linarith
  have e1 := hH (Real.log m) (by rw [abs_of_pos (by linarith)]; linarith)
  have e2 := hH (-Real.log m) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have e3 := hH (Real.log m + (b - a)) (by rw [abs_of_pos (by linarith)]; linarith)
  have e4 := hH (-(Real.log m + (b - a))) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [logValue, weilTest_pairTestAt, weilTest_pairTestAt,
    show Real.log m - a + b = Real.log m + (b - a) by ring,
    show Real.log m - b + a = Real.log m - (b - a) by ring,
    show -Real.log m - a + b = -(Real.log m - (b - a)) by ring,
    show -Real.log m - b + a = -(Real.log m + (b - a)) by ring, e1, e2, e3, e4]
  split_ifs with hmj
  · subst hmj
    rw [weilTest_narrowBumpC_eq, weilTest_narrowBumpC_eq,
      show Real.log m - (b - a) = -(b - a - Real.log m) by ring, neg_neg]
    rw [show (1 + σ ^ 2 : ℝ) * (0 : ℂ) + (σ : ℂ) * (0 + ((bumpCorr m (-(b - a - Real.log m)) : ℝ) : ℂ)) +
        ((1 + σ ^ 2 : ℝ) * (0 : ℂ) + (σ : ℂ) * (((bumpCorr m (b - a - Real.log m) : ℝ) : ℂ) + 0)) =
        ((σ * (bumpCorr m (-(b - a - Real.log m)) + bumpCorr m (b - a - Real.log m)) : ℝ) : ℂ) by
          push_cast; ring, Complex.ofReal_re]
  · have hgap := WeilExcess.inv_succ_le_abs_log_sub (by omega) (by omega) hmj
    rw [← four_mul_bumpRadius] at hgap
    have hfar : 2 * bumpRadius j < |Real.log m - (b - a)| := by
      have h1 := abs_sub_abs_le_abs_sub (Real.log m - Real.log j) (b - a - Real.log j)
      rw [show Real.log m - Real.log j - (b - a - Real.log j) = Real.log m - (b - a) by ring] at h1
      linarith
    rw [hH _ hfar, hH _ (by rw [abs_neg]; exact hfar)]
    simp

/-! ## Reaching every node below `2L` at level `L` -/

/-- The level-`L` two-bump test at node `n`: centred at `±log n/2` when that fits inside the level,
pushed to the ends `±(L − r_n)` otherwise. -/
def levelPairTestFn (L : ℝ) (n : ℕ) (σ : ℝ) : WeilTestFn :=
  if Real.log n ≤ 2 * L - 2 * bumpRadius n then
    pairTestAtFn n σ (-(Real.log n / 2)) (Real.log n / 2)
  else pairTestAtFn n σ (-(L - bumpRadius n)) (L - bumpRadius n)

/-- The node weight of `levelPairTestFn L n 1`. -/
def levelWeight (L : ℝ) (n : ℕ) : ℝ :=
  if Real.log n ≤ 2 * L - 2 * bumpRadius n then 2 * bumpCorr n 0 / Real.sqrt n
  else (bumpCorr n (Real.log n - (2 * L - 2 * bumpRadius n)) +
    bumpCorr n (2 * L - 2 * bumpRadius n - Real.log n)) / Real.sqrt n

theorem levelTest_levelPairTestFn {L : ℝ} {n : ℕ} (hn : 2 ≤ n) (hL : Real.log n < 2 * L) (σ : ℝ) :
    LevelTest L (levelPairTestFn L n σ) := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlog2 : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have hr := bumpRadius_le n
  have hrpos := bumpRadius_pos n
  have hLr : bumpRadius n ≤ L := by linarith [half_lt_log_two]
  unfold levelPairTestFn
  split_ifs with h
  · apply levelTest_pairTestAtFn
    · rw [abs_neg, abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  · apply levelTest_pairTestAtFn
    · rw [abs_neg, abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith

theorem logVector_levelPairTestFn {L : ℝ} (n : LogIndex) (hL : Real.log n < 2 * L) (σ : ℝ) :
    logVector (levelPairTestFn L n σ) = Finsupp.single n (σ * levelWeight L n) := by
  have hrpos := bumpRadius_pos n
  ext m
  rw [logVector_apply, Finsupp.single_apply]
  unfold levelPairTestFn levelWeight
  split_ifs with h hmn hmn
  · change logValue (pairTestAt n σ _ _) m = _
    rw [logValue_pairTestAt n.2 σ _ _ (by
      rw [show Real.log ↑↑n / 2 - -(Real.log ↑↑n / 2) - Real.log ↑↑n = 0 by ring, abs_zero]
      linarith) m.2, if_pos (congrArg Subtype.val hmn.symm)]
    rw [show Real.log ↑↑n / 2 - -(Real.log ↑↑n / 2) = Real.log ↑↑n by ring, sub_self]
    rw [hmn]; ring
  · change logValue (pairTestAt n σ _ _) m = _
    rw [logValue_pairTestAt n.2 σ _ _ (by
      rw [show Real.log ↑↑n / 2 - -(Real.log ↑↑n / 2) - Real.log ↑↑n = 0 by ring, abs_zero]
      linarith) m.2, if_neg fun h' => hmn (Subtype.ext h'.symm)]
  · change logValue (pairTestAt n σ _ _) m = _
    push Not at h
    rw [logValue_pairTestAt n.2 σ _ _ (by
      rw [show L - bumpRadius ↑n - -(L - bumpRadius ↑n) - Real.log ↑↑n =
        2 * L - 2 * bumpRadius ↑n - Real.log ↑↑n by ring, abs_lt]
      constructor <;> linarith) m.2, if_pos (congrArg Subtype.val hmn.symm)]
    rw [show L - bumpRadius ↑n - -(L - bumpRadius ↑n) = 2 * L - 2 * bumpRadius ↑n by ring, hmn]
    ring
  · change logValue (pairTestAt n σ _ _) m = _
    push Not at h
    rw [logValue_pairTestAt n.2 σ _ _ (by
      rw [show L - bumpRadius ↑n - -(L - bumpRadius ↑n) - Real.log ↑↑n =
        2 * L - 2 * bumpRadius ↑n - Real.log ↑↑n by ring, abs_lt]
      constructor <;> linarith) m.2, if_neg fun h' => hmn (Subtype.ext h'.symm)]

theorem levelWeight_pos {L : ℝ} {n : ℕ} (hn : 2 ≤ n) (hL : Real.log n < 2 * L) :
    0 < levelWeight L n := by
  have hrpos := bumpRadius_pos n
  have hnpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  unfold levelWeight
  split_ifs with h
  · exact div_pos (mul_pos two_pos (bumpCorr_pos n (by rw [abs_zero]; linarith))) hnpos
  · push Not at h
    refine div_pos (add_pos (bumpCorr_pos n ?_) (bumpCorr_pos n ?_)) hnpos
    · rw [abs_lt]; constructor <;> linarith
    · rw [abs_lt]; constructor <;> linarith

/-! ## Node values of level-`L` tests vanish from `2L` on -/

/-- The autocorrelation of a level-`L` test vanishes at every lag of modulus `≥ 2L`. -/
theorem weilTest_eq_zero_of_levelTest {L : ℝ} {f : WeilTestFn} (hf : LevelTest L f) {Y : ℝ}
    (hY : 2 * L ≤ |Y|) : EF.weilTest f.1 f.1 Y = 0 := by
  simp only [EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply', EF.tilde, neg_sub]
  refine integral_eq_zero_of_ae ?_
  have hsub : {t : ℝ | f.1 t * (starRingEnd ℂ) (f.1 (t - Y)) ≠ 0} ⊆ {Y / 2} := by
    intro t ht
    have h1 : f.1 t ≠ 0 := fun h => ht (by simp [h])
    have h2 : f.1 (t - Y) ≠ 0 := fun h => ht (by simp [h])
    have ht1 := abs_le.mp (hf t h1)
    have ht2 := abs_le.mp (hf (t - Y) h2)
    rw [Set.mem_singleton_iff]
    rcases le_or_gt 0 Y with hY0 | hY0
    · rw [abs_of_nonneg hY0] at hY
      linarith
    · rw [abs_of_neg hY0] at hY
      linarith
  rw [Filter.EventuallyEq, ae_iff]
  exact measure_mono_null hsub (by simp)

theorem logVector_apply_eq_zero_of_levelTest {L : ℝ} {f : WeilTestFn} (hf : LevelTest L f)
    (n : LogIndex) (hn : 2 * L ≤ Real.log n) : logVector f n = 0 := by
  have hlog : 0 ≤ Real.log (n : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num) n.2 : 1 ≤ (n : ℕ)))
  rw [logVector_apply, logValue, weilTest_eq_zero_of_levelTest hf (by rwa [abs_of_nonneg hlog]),
    weilTest_eq_zero_of_levelTest hf (by rwa [abs_neg, abs_of_nonneg hlog])]
  simp

/-- The projection of a node vector onto the nodes `log n < 2L`. -/
def levelProj (L : ℝ) (v : LogIndex →₀ ℝ) : LogIndex →₀ ℝ :=
  v.filter fun n => Real.log n < 2 * L

theorem levelProj_add (L : ℝ) (v w : LogIndex →₀ ℝ) :
    levelProj L (v + w) = levelProj L v + levelProj L w := Finsupp.filter_add

theorem levelProj_smul (L : ℝ) (t : ℝ) (v : LogIndex →₀ ℝ) :
    levelProj L (t • v) = t • levelProj L v := Finsupp.filter_smul

theorem levelProj_zero (L : ℝ) : levelProj L 0 = 0 := Finsupp.filter_zero _

theorem levelProj_neg (L : ℝ) (v : LogIndex →₀ ℝ) : levelProj L (-v) = -levelProj L v := by
  rw [← neg_one_smul ℝ v, levelProj_smul, neg_one_smul]

theorem mem_support_levelProj {L : ℝ} {v : LogIndex →₀ ℝ} {n : LogIndex}
    (hn : n ∈ (levelProj L v).support) : Real.log n < 2 * L := by
  rw [levelProj, Finsupp.support_filter, Finset.mem_filter] at hn
  exact hn.2

/-- The node vector of a level-`L` combination is already supported below `2L`. -/
theorem levelProj_nodeVector {L : ℝ} {c : WeilTestFn →₀ ℝ} (hc : ∀ f ∈ c.support, LevelTest L f) :
    levelProj L (nodeVector c) = nodeVector c := by
  rw [levelProj, Finsupp.filter_eq_self_iff]
  intro n hn
  by_contra hL
  push Not at hL
  apply hn
  rw [nodeVector_eq, linearCombination_apply, Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_eq_zero fun f hf => ?_
  show (c f • logVector f) n = 0
  rw [Finsupp.smul_apply, logVector_apply_eq_zero_of_levelTest (hc f hf) n hL, smul_zero]

theorem levelProj_logVector {L : ℝ} {f : WeilTestFn} (hf : LevelTest L f) :
    levelProj L (logVector f) = logVector f := by
  classical
  have := levelProj_nodeVector (L := L) (c := Finsupp.single f 1) (fun g hg => by
    rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hg
    rw [hg]; exact hf)
  rwa [nodeVector_single_test] at this

/-! ## The level lift: every projected node vector is attained at level `L` -/

/-- Scaled level-`L` two-bump tests realising the node vector `π_L v`. -/
def levelLift (L : ℝ) (v : LogIndex →₀ ℝ) : WeilTestFn →₀ ℝ :=
  (levelProj L v).sum fun n t =>
    (|t| / levelWeight L n) • Finsupp.single (levelPairTestFn L n (if 0 ≤ t then 1 else -1)) 1

theorem levelLift_nonneg (L : ℝ) (v : LogIndex →₀ ℝ) (f : WeilTestFn) : 0 ≤ levelLift L v f := by
  classical
  rw [levelLift, Finsupp.sum_apply]
  refine Finsupp.sum_nonneg fun n hn => ?_
  have hw := levelWeight_pos n.2 (mem_support_levelProj hn)
  rw [Finsupp.smul_apply, smul_eq_mul]
  refine mul_nonneg (div_nonneg (abs_nonneg _) hw.le) ?_
  rw [Finsupp.single_apply]; split_ifs <;> norm_num

theorem levelTest_of_mem_support_levelLift {L : ℝ} {v : LogIndex →₀ ℝ} {f : WeilTestFn}
    (hf : f ∈ (levelLift L v).support) : LevelTest L f := by
  classical
  rw [levelLift] at hf
  have hsub := Finsupp.support_sum hf
  rw [Finset.mem_biUnion] at hsub
  obtain ⟨n, hn, hfn⟩ := hsub
  have hfn' := Finsupp.support_smul hfn
  rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hfn'
  rw [hfn']
  exact levelTest_levelPairTestFn n.2 (mem_support_levelProj hn) _

theorem nodeVector_levelLift (L : ℝ) (v : LogIndex →₀ ℝ) :
    nodeVector (levelLift L v) = levelProj L v := by
  classical
  rw [levelLift, nodeVector_eq, map_finsuppSum]
  conv_rhs => rw [← Finsupp.sum_single (levelProj L v)]
  refine Finsupp.sum_congr fun n hn => ?_
  have hL := mem_support_levelProj hn
  have hw := levelWeight_pos n.2 hL
  rw [map_smul, ← nodeVector_eq, nodeVector_single_test, logVector_levelPairTestFn n hL,
    Finsupp.smul_single, smul_eq_mul]
  congr 1
  split_ifs with h
  · rw [abs_of_nonneg h]; field_simp
  · push Not at h
    rw [abs_of_neg h]; field_simp

/-! ## The level value function and the finite-level Farkas lemma -/

variable (L : ℝ) (Φ : WeilTestFn → ℝ)

/-- `Φ` is nonnegative on every nonnegative blind combination of level-`L` tests. -/
def LevelBlindNonneg : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → (∀ f ∈ c.support, LevelTest L f) → nodeVector c = 0 →
    0 ≤ linearCombination ℝ Φ c

/-- The values of `Φ` on nonnegative level-`L` combinations with node vector `π_L v`. -/
def levelFibre (v : LogIndex →₀ ℝ) : Set ℝ :=
  {E | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ (∀ f ∈ c.support, LevelTest L f) ∧
    nodeVector c = levelProj L v ∧ linearCombination ℝ Φ c = E}

/-- The level value function. -/
def levelValue (v : LogIndex →₀ ℝ) : ℝ := sInf (levelFibre L Φ v)

theorem levelFibre_nonempty (v : LogIndex →₀ ℝ) : (levelFibre L Φ v).Nonempty :=
  ⟨_, levelLift L v, levelLift_nonneg L v, fun _ hf => levelTest_of_mem_support_levelLift hf,
    nodeVector_levelLift L v, rfl⟩

theorem zero_mem_levelFibre_zero : (0 : ℝ) ∈ levelFibre L Φ 0 :=
  ⟨0, fun _ => le_rfl, fun f hf => by simp at hf, by simp [nodeVector_eq, levelProj_zero],
    by simp⟩

theorem add_mem_levelFibre {v w : LogIndex →₀ ℝ} {E F : ℝ} (hE : E ∈ levelFibre L Φ v)
    (hF : F ∈ levelFibre L Φ w) : E + F ∈ levelFibre L Φ (v + w) := by
  classical
  obtain ⟨c, hc, hcL, hcv, rfl⟩ := hE
  obtain ⟨d, hd, hdL, hdw, rfl⟩ := hF
  refine ⟨c + d, fun f => by simpa using add_nonneg (hc f) (hd f), fun f hf => ?_, ?_, by
    rw [map_add]⟩
  · rcases Finset.mem_union.mp (Finsupp.support_add hf) with h | h
    · exact hcL f h
    · exact hdL f h
  · rw [nodeVector_add, hcv, hdw, levelProj_add]

theorem smul_mem_levelFibre {v : LogIndex →₀ ℝ} {E t : ℝ} (ht : 0 ≤ t)
    (hE : E ∈ levelFibre L Φ v) : t * E ∈ levelFibre L Φ (t • v) := by
  obtain ⟨c, hc, hcL, hcv, rfl⟩ := hE
  refine ⟨t • c, fun f => by rw [Finsupp.smul_apply, smul_eq_mul]; exact mul_nonneg ht (hc f),
    fun f hf => hcL f (Finsupp.support_smul hf), ?_, by rw [map_smul, smul_eq_mul]⟩
  rw [nodeVector_smul, hcv, levelProj_smul]

theorem levelFibre_smul {v : LogIndex →₀ ℝ} {t : ℝ} (ht : 0 < t) :
    levelFibre L Φ (t • v) = (fun E => t * E) '' levelFibre L Φ v := by
  ext E
  constructor
  · intro hE
    refine ⟨t⁻¹ * E, ?_, by show t * (t⁻¹ * E) = E; rw [mul_inv_cancel_left₀ ht.ne']⟩
    have := smul_mem_levelFibre L Φ (inv_nonneg.mpr ht.le) hE
    rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this
  · rintro ⟨F, hF, rfl⟩
    exact smul_mem_levelFibre L Φ ht.le hF

variable {L Φ}

theorem nonneg_of_mem_levelFibre_zero (h : LevelBlindNonneg L Φ) {E : ℝ}
    (hE : E ∈ levelFibre L Φ 0) : 0 ≤ E := by
  obtain ⟨c, hc, hcL, hcv, rfl⟩ := hE
  rw [levelProj_zero] at hcv
  exact h c hc hcL hcv

theorem bddBelow_levelFibre (h : LevelBlindNonneg L Φ) (v : LogIndex →₀ ℝ) :
    BddBelow (levelFibre L Φ v) := by
  obtain ⟨F, hF⟩ := levelFibre_nonempty L Φ (-v)
  refine ⟨-F, fun E hE => ?_⟩
  have := nonneg_of_mem_levelFibre_zero h (by
    have := add_mem_levelFibre L Φ hE hF
    rwa [add_neg_cancel] at this)
  linarith

theorem levelValue_le_of_mem (h : LevelBlindNonneg L Φ) {v : LogIndex →₀ ℝ} {E : ℝ}
    (hE : E ∈ levelFibre L Φ v) : levelValue L Φ v ≤ E :=
  csInf_le (bddBelow_levelFibre h v) hE

theorem levelValue_zero (h : LevelBlindNonneg L Φ) : levelValue L Φ 0 = 0 :=
  le_antisymm (levelValue_le_of_mem h (zero_mem_levelFibre_zero L Φ))
    (le_csInf (levelFibre_nonempty L Φ 0) fun _ hE => nonneg_of_mem_levelFibre_zero h hE)

theorem levelValue_add_le (h : LevelBlindNonneg L Φ) (v w : LogIndex →₀ ℝ) :
    levelValue L Φ (v + w) ≤ levelValue L Φ v + levelValue L Φ w := by
  have h1 : ∀ E ∈ levelFibre L Φ v, ∀ F ∈ levelFibre L Φ w, levelValue L Φ (v + w) ≤ E + F :=
    fun E hE F hF => levelValue_le_of_mem h (add_mem_levelFibre L Φ hE hF)
  have h2 : ∀ F ∈ levelFibre L Φ w, levelValue L Φ (v + w) - F ≤ levelValue L Φ v := fun F hF =>
    le_csInf (levelFibre_nonempty L Φ v) fun E hE => by linarith [h1 E hE F hF]
  have h3 : levelValue L Φ (v + w) - levelValue L Φ v ≤ levelValue L Φ w :=
    le_csInf (levelFibre_nonempty L Φ w) fun F hF => by linarith [h2 F hF]
  linarith

theorem levelValue_smul (h : LevelBlindNonneg L Φ) {t : ℝ} (ht : 0 < t) (v : LogIndex →₀ ℝ) :
    levelValue L Φ (t • v) = t * levelValue L Φ v := by
  rw [levelValue, levelValue, levelFibre_smul L Φ ht]
  have hne := levelFibre_nonempty L Φ v
  have hbdd := bddBelow_levelFibre h v
  have hbdd' : BddBelow ((fun E => t * E) '' levelFibre L Φ v) := by
    obtain ⟨b, hb⟩ := hbdd
    exact ⟨t * b, by rintro _ ⟨E, hE, rfl⟩; exact mul_le_mul_of_nonneg_left (hb hE) ht.le⟩
  refine le_antisymm ?_ ?_
  · have h1 : ∀ E ∈ levelFibre L Φ v, sInf ((fun E => t * E) '' levelFibre L Φ v) ≤ t * E :=
      fun E hE => csInf_le hbdd' ⟨E, hE, rfl⟩
    have h2 : t⁻¹ * sInf ((fun E => t * E) '' levelFibre L Φ v) ≤ sInf (levelFibre L Φ v) := by
      refine le_csInf hne fun E hE => ?_
      rw [inv_mul_le_iff₀ ht]
      exact h1 E hE
    have := mul_le_mul_of_nonneg_left h2 ht.le
    rwa [mul_inv_cancel_left₀ ht.ne'] at this
  · refine le_csInf (hne.image _) ?_
    rintro _ ⟨E, hE, rfl⟩
    exact mul_le_mul_of_nonneg_left (csInf_le hbdd hE) ht.le

/-- A linear minorant of the level value function (Hahn–Banach). -/
theorem exists_linearMap_le_levelValue (h : LevelBlindNonneg L Φ) :
    ∃ g : (LogIndex →₀ ℝ) →ₗ[ℝ] ℝ, ∀ v, g v ≤ levelValue L Φ v := by
  have H : ∀ c : ℝ, c • (0 : LogIndex →₀ ℝ) = 0 → (RingHom.id ℝ) c • (0 : ℝ) = 0 :=
    fun c _ => by simp
  have hdom : ∀ x : (LinearPMap.mkSpanSingleton' (0 : LogIndex →₀ ℝ) (0 : ℝ) H).domain,
      LinearPMap.mkSpanSingleton' (0 : LogIndex →₀ ℝ) (0 : ℝ) H x ≤ levelValue L Φ x := by
    intro x
    have hx : (x : LogIndex →₀ ℝ) ∈ Submodule.span ℝ {(0 : LogIndex →₀ ℝ)} := x.2
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    have hx' : x = ⟨a • 0, by rw [ha]; exact x.2⟩ := Subtype.ext ha.symm
    rw [hx', LinearPMap.mkSpanSingleton'_apply]
    simp only [RingHom.id_apply, smul_eq_mul, mul_zero, smul_zero]
    rw [levelValue_zero h]
  obtain ⟨g, -, hg⟩ := exists_extension_of_le_sublinear
    (LinearPMap.mkSpanSingleton' (0 : LogIndex →₀ ℝ) (0 : ℝ) H) (levelValue L Φ)
    (fun c hc x => levelValue_smul h hc x) (levelValue_add_le h) hdom
  exact ⟨g, hg⟩

theorem levelValue_le_apply (h : LevelBlindNonneg L Φ) {f : WeilTestFn} (hf : LevelTest L f) :
    levelValue L Φ (logVector f) ≤ Φ f := by
  classical
  refine levelValue_le_of_mem h ⟨Finsupp.single f 1, fun g => ?_, fun g hg => ?_, ?_, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hg
    rw [hg]; exact hf
  · rw [nodeVector_single_test, levelProj_logVector hf]
  · rw [linearCombination_single, one_smul]

theorem linearCombination_logVector_nodeVector (lam : LogIndex → ℝ) (c : WeilTestFn →₀ ℝ) :
    linearCombination ℝ lam (nodeVector c) =
      c.sum fun f t => t * linearCombination ℝ lam (logVector f) := by
  rw [nodeVector_eq, Finsupp.linearCombination_apply (R := ℝ) (v := logVector) c, map_finsuppSum]
  refine Finsupp.sum_congr fun f _ => ?_
  rw [map_smul, smul_eq_mul]

/-- **Finite-level Farkas lemma.**  `Φ` is nonnegative on the nonnegative blind combinations of
level-`L` tests iff some node weights `lam` satisfy `Σ_n lam(n) ℓ_n(f) ≤ Φ(f)` for every level-`L`
test `f`. -/
theorem levelBlindNonneg_iff_exists_weights :
    LevelBlindNonneg L Φ ↔
      ∃ lam : LogIndex → ℝ, ∀ f : WeilTestFn, LevelTest L f →
        linearCombination ℝ lam (logVector f) ≤ Φ f := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := exists_linearMap_le_levelValue h
    refine ⟨fun j => g (Finsupp.single j 1), fun f hf => ?_⟩
    rw [← linearMap_eq_linearCombination g]
    exact (hg _).trans (levelValue_le_apply h hf)
  · rintro ⟨lam, hlam⟩ c hc hcL hcv
    have h0 : (c.sum fun f t => t * linearCombination ℝ lam (logVector f)) = 0 := by
      rw [← linearCombination_logVector_nodeVector, hcv, map_zero]
    have hle : (c.sum fun f t => t * linearCombination ℝ lam (logVector f)) ≤
        c.sum fun f t => t * Φ f := by
      unfold Finsupp.sum
      exact Finset.sum_le_sum fun f hf =>
        mul_le_mul_of_nonneg_left (hlam f (hcL f hf)) (hc f)
    rw [linearCombination_apply]
    simp only [smul_eq_mul]
    linarith

/-- The weights produced by the Farkas lemma may be taken supported on the nodes `log n < 2L`. -/
theorem exists_weights_support_of_levelBlindNonneg (h : LevelBlindNonneg L Φ) :
    ∃ lam : LogIndex → ℝ, (∀ n : LogIndex, 2 * L ≤ Real.log n → lam n = 0) ∧
      ∀ f : WeilTestFn, LevelTest L f → linearCombination ℝ lam (logVector f) ≤ Φ f := by
  obtain ⟨g, hg⟩ := exists_linearMap_le_levelValue h
  refine ⟨fun j => g (Finsupp.single j 1), fun n hn => ?_, fun f hf => ?_⟩
  · have hproj : ∀ t : ℝ, levelProj L (t • Finsupp.single n (1 : ℝ)) = 0 := by
      intro t
      rw [levelProj_smul, levelProj,
        Finsupp.filter_single_of_neg (fun m : LogIndex => Real.log (m : ℕ) < 2 * L)
          (not_lt.mpr hn), smul_zero]
    have hval : ∀ t : ℝ, levelValue L Φ (t • Finsupp.single n (1 : ℝ)) = 0 := by
      intro t
      have : levelFibre L Φ (t • Finsupp.single n (1 : ℝ)) = levelFibre L Φ 0 := by
        unfold levelFibre; rw [hproj, levelProj_zero]
      rw [levelValue, this, ← levelValue, levelValue_zero h]
    have h1 := hg (Finsupp.single n 1)
    have h2 := hg (-Finsupp.single n 1)
    rw [← one_smul ℝ (Finsupp.single n (1 : ℝ)), hval] at h1
    rw [← neg_one_smul ℝ (Finsupp.single n (1 : ℝ)), hval, map_smul, smul_eq_mul] at h2
    simp only [one_smul] at h1
    linarith
  · rw [← linearMap_eq_linearCombination g]
    exact (hg _).trans (levelValue_le_apply h hf)

/-! ## Instances: pole weights, floors and margins, RH -/

theorem linearCombination_add_mul (Φ₁ Φ₂ : WeilTestFn → ℝ) (s : ℝ) (c : WeilTestFn →₀ ℝ) :
    linearCombination ℝ (fun f => Φ₁ f + s * Φ₂ f) c =
      linearCombination ℝ Φ₁ c + s * linearCombination ℝ Φ₂ c := by
  simp only [linearCombination_apply, Finsupp.sum, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun f _ => by ring

/-- The per-test functional `A_β(f) = weilArchRe(k_f) + (β − 1) Re P(k_f)`. -/
def poleWeightFunctional (β : ℝ) (f : WeilTestFn) : ℝ :=
  weilArchRe (EF.weilTest f.1 f.1) + (β - 1) * (weilPoleTerm (EF.weilTest f.1 f.1)).re

theorem linearCombination_poleWeightFunctional (β : ℝ) (c : WeilTestFn →₀ ℝ) :
    linearCombination ℝ (poleWeightFunctional β) c =
      nodeArchEnergy c + (β - 1) * nodePoleMass c := by
  unfold poleWeightFunctional
  rw [linearCombination_add_mul, nodeArchEnergy_eq]
  rfl

theorem primeBlindPositiveAtLevel_iff_levelBlindNonneg (L β : ℝ) :
    PrimeBlindPositiveAtLevel L β ↔ LevelBlindNonneg L (poleWeightFunctional β) := by
  unfold PrimeBlindPositiveAtLevel LevelBlindNonneg
  simp only [linearCombination_poleWeightFunctional]

/-- Node weights Weil-positive at pole weight `β` on all level-`L` tests. -/
def LevelWeilPositiveAt (L β : ℝ) (lam : LogIndex → ℝ) : Prop :=
  ∀ f : WeilTestFn, LevelTest L f →
    linearCombination ℝ lam (logVector f) ≤
      weilArchRe (EF.weilTest f.1 f.1) + (β - 1) * (weilPoleTerm (EF.weilTest f.1 f.1)).re

/-- **Finite-level Farkas for prime-blind positivity.**  Blind positivity at level `L` with pole
weight `β` holds iff some node weights are Weil-positive at pole weight `β` on the level-`L`
tests. -/
theorem primeBlindPositiveAtLevel_iff_exists_weights (L β : ℝ) :
    PrimeBlindPositiveAtLevel L β ↔ ∃ lam : LogIndex → ℝ, LevelWeilPositiveAt L β lam := by
  rw [primeBlindPositiveAtLevel_iff_levelBlindNonneg, levelBlindNonneg_iff_exists_weights]
  rfl

/-- The mass `∫‖f‖²` of a test. -/
def testMass (f : WeilTestFn) : ℝ := ∫ x, ‖f.1 x‖ ^ 2

/-- The uniform floors of the blind level-`L` functional: `m` with `A_β(c) ≥ m·mass(c)` on all
nonnegative blind level-`L` combinations. -/
def levelFloors (L β : ℝ) : Set ℝ :=
  {m | ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → (∀ f ∈ c.support, LevelTest L f) →
    nodeVector c = 0 → m * linearCombination ℝ testMass c ≤
      nodeArchEnergy c + (β - 1) * nodePoleMass c}

/-- The margins of level-`L` Weil forms: `m` such that for some node weights `lam`,
`Σ lam ℓ(f) + m ‖f‖² ≤ A_β(f)` for every level-`L` test. -/
def levelMargins (L β : ℝ) : Set ℝ :=
  {m | ∃ lam : LogIndex → ℝ, ∀ f : WeilTestFn, LevelTest L f →
    linearCombination ℝ lam (logVector f) + m * testMass f ≤ poleWeightFunctional β f}

/-- **Strong duality at a finite level.**  The uniform floors of the blind functional coincide with
the margins of the level-`L` Weil forms. -/
theorem levelFloors_eq_levelMargins (L β : ℝ) : levelFloors L β = levelMargins L β := by
  ext m
  have key := levelBlindNonneg_iff_exists_weights
    (L := L) (Φ := fun f => poleWeightFunctional β f + (-m) * testMass f)
  have hlc : ∀ c : WeilTestFn →₀ ℝ,
      linearCombination ℝ (fun f => poleWeightFunctional β f + (-m) * testMass f) c =
        nodeArchEnergy c + (β - 1) * nodePoleMass c - m * linearCombination ℝ testMass c := by
    intro c
    rw [linearCombination_add_mul, linearCombination_poleWeightFunctional]; ring
  constructor
  · intro hm
    have : LevelBlindNonneg L fun f => poleWeightFunctional β f + (-m) * testMass f := by
      intro c hc hcL hcv
      rw [hlc]
      linarith [hm c hc hcL hcv]
    obtain ⟨lam, hlam⟩ := key.mp this
    exact ⟨lam, fun f hf => by linarith [hlam f hf]⟩
  · rintro ⟨lam, hlam⟩ c hc hcL hcv
    have : LevelBlindNonneg L fun f => poleWeightFunctional β f + (-m) * testMass f :=
      key.mpr ⟨lam, fun f hf => by linarith [hlam f hf]⟩
    have := this c hc hcL hcv
    rw [hlc] at this
    linarith

/-- Blind positivity at level `L` and pole weight `β` is the statement `0 ∈ levelFloors L β`, hence
`0 ∈ levelMargins L β`. -/
theorem zero_mem_levelMargins_iff (L β : ℝ) :
    (0 : ℝ) ∈ levelMargins L β ↔ PrimeBlindPositiveAtLevel L β := by
  rw [← levelFloors_eq_levelMargins]
  unfold levelFloors PrimeBlindPositiveAtLevel
  simp only [Set.mem_setOf_eq, zero_mul]

/-- **RH is the solvability of a tower of finite Farkas problems.**  RH holds iff at every level
`L` some pole weight `β` and some node weights are Weil-positive on all tests supported in
`[−L, L]`. -/
theorem riemannHypothesis_iff_forall_level_exists_weights :
    RiemannHypothesis ↔ ∀ L : ℝ, ∃ β : ℝ, ∃ lam : LogIndex → ℝ, LevelWeilPositiveAt L β lam := by
  rw [riemannHypothesis_iff_forall_level_exists_mem_levelWindow]
  refine forall_congr' fun L => exists_congr fun β => ?_
  exact primeBlindPositiveAtLevel_iff_exists_weights L β

/-- RH holds iff at every level some node weights are Weil-positive at pole weight `1` on all
tests supported in `[−L, L]`. -/
theorem riemannHypothesis_iff_forall_level_exists_weights_one :
    RiemannHypothesis ↔ ∀ L : ℝ, ∃ lam : LogIndex → ℝ, LevelWeilPositiveAt L 1 lam := by
  rw [riemannHypothesis_iff_forall_one_mem_levelWindow]
  exact forall_congr' fun L => primeBlindPositiveAtLevel_iff_exists_weights L 1

/-- Under RH the von Mangoldt weights work at every level with pole weight `1`; in particular the
Farkas weights of each level exist. -/
theorem exists_levelWeilPositiveAt_one_of_riemannHypothesis (hRH : RiemannHypothesis) (L : ℝ) :
    ∃ lam : LogIndex → ℝ, LevelWeilPositiveAt L 1 lam :=
  riemannHypothesis_iff_forall_level_exists_weights_one.mp hRH L

end

end RHTower.WeilOneSided
