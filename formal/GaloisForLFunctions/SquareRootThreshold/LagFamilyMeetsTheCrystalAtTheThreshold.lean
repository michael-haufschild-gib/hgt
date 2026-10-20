import GaloisForLFunctions.SquareRootThreshold.ChainsHideFromLagGrids
import GaloisForLFunctions.SquareRootThreshold.HodgeIndexOnLagLatticeConfigurations

/-!
# The lag family meets the crystal at the threshold

The off-line lattice `{½ ± δ + 2πik/L}` hides from every test of aperture `≤ L/2` and from no
larger aperture (`RHTower.offLineLattice_weil_positive_iff`). The one-parameter family
`f_v = κ_w(t + v/2) − κ_w(t − v/2)`, of aperture `v/2 + w`, meets this threshold exactly. For
`L > 4w` its Weil form on the lattice is a comb in the lag:

* **Silence up to the threshold** (`re_W_offLineLattice_lag_nonneg_of_le`). For `0 ≤ v ≤ L − 2w`
  the aperture is at most `L/2`, and `Re W(f_v, f_v) ≥ 0`.
* **Teeth** (`W_offLineLattice_lag_nat_mul`). At every lag `v = nL`, `n ≥ 1`,
  `W(f_v, f_v) = 4L‖κ_w‖²(1 − cosh(nδL)) < 0`, for every depth `δ > 0`. The first negative lag
  lies in `(L − 2w, L]`, at aperture in `(L/2, L/2 + w]`.
* **Gaps** (`W_offLineLattice_lag_eq_of_gap`). For `v > 2w` off the teeth `|v − nL| ≤ 2w`,
  `W(f_v, f_v) = 4L‖κ_w‖² > 0`: between the teeth, tests of aperture far beyond `L/2` see nothing.

The mechanism is the lag formula `W(f, f) = L Σ_m k(mL) 2cosh(δmL)` (`W_offLineLatticeConfig_lag`)
and the kernel of the difference test, `k(x) = 2K(x) − K(x + v) − K(x − v)` with
`K = κ_w ⋆ κ̃_w` supported in `[−2w, 2w]` (`weilTest_twoBump_neg_one`). At `v = nL` the atoms
`m = ±n` carry `−K(0)` against `cosh(nδL)`. So the minimal receiver is threshold-exact on
crystals, and its negativity `4L‖κ_w‖²(cosh(nδL) − 1)` grows at the rate `e^{δv}` of the depth.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The kernel of the difference test -/

/-- **The kernel of the difference test.** For `b` continuous with compact support,
`(f_v ⋆ f̃_v)(x) = 2K(x) − K(x + v) − K(x − v)` with `K = b ⋆ b̃`. -/
theorem weilTest_twoBump_neg_one {b : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (v x : ℝ) :
    EF.weilTest (twoBump b v (-1)) (twoBump b v (-1)) x =
      2 * EF.weilTest b b x - EF.weilTest b b (x + v) - EF.weilTest b b (x - v) := by
  -- each cross term is a translate of `K`
  have hint : ∀ (f₁ g : ℝ → ℝ) (α β : ℝ), (∀ t, f₁ t = t + α) → (∀ t, g t = t + β) →
      Integrable fun t => b (f₁ t) * conj (b (g t)) := fun f₁ g α β hf hg => by
    have e : (fun t => b (f₁ t) * conj (b (g t))) = fun t => b (t + α) * conj (b (t + β)) :=
      funext fun t => by rw [hf, hg]
    rw [e]
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      ((hbc.comp_homeomorph (Homeomorph.addRight α)).mul_right)
  have key : ∀ (f₁ g : ℝ → ℝ) (α y : ℝ), (∀ t, f₁ t = t + α) → (∀ t, g t = t + α - y) →
      ∫ t, b (f₁ t) * conj (b (g t)) = EF.weilTest b b y := fun f₁ g α y hf hg => by
    have e : (fun t => b (f₁ t) * conj (b (g t))) = fun t => b (t + α) * conj (b (t + α - y)) :=
      funext fun t => by rw [hf, hg]
    rw [e, RHTower.weilTest_apply]
    exact integral_add_right_eq_self (fun s => b s * conj (b (s - y))) α
  have e : (fun t => twoBump b v (-1) t * conj (twoBump b v (-1) (t - x))) = fun t =>
      b (t + v / 2) * conj (b (t - x + v / 2)) - b (t + v / 2) * conj (b (t - x - v / 2)) -
        b (t - v / 2) * conj (b (t - x + v / 2)) + b (t - v / 2) * conj (b (t - x - v / 2)) := by
    funext t
    rw [twoBump_apply, twoBump_apply]
    simp only [map_add, map_mul, map_neg, map_one]
    ring
  have I1 := hint (fun t => t + v / 2) (fun t => t - x + v / 2) (v / 2) (-x + v / 2)
    (fun t => rfl) (fun t => by ring)
  have I2 := hint (fun t => t + v / 2) (fun t => t - x - v / 2) (v / 2) (-x - v / 2)
    (fun t => rfl) (fun t => by ring)
  have I3 := hint (fun t => t - v / 2) (fun t => t - x + v / 2) (-(v / 2)) (-x + v / 2)
    (fun t => by ring) (fun t => by ring)
  have I4 := hint (fun t => t - v / 2) (fun t => t - x - v / 2) (-(v / 2)) (-x - v / 2)
    (fun t => by ring) (fun t => by ring)
  have I12 : Integrable fun t => b (t + v / 2) * conj (b (t - x + v / 2)) -
      b (t + v / 2) * conj (b (t - x - v / 2)) := I1.sub I2
  have I123 : Integrable fun t => b (t + v / 2) * conj (b (t - x + v / 2)) -
      b (t + v / 2) * conj (b (t - x - v / 2)) - b (t - v / 2) * conj (b (t - x + v / 2)) :=
    I12.sub I3
  rw [RHTower.weilTest_apply, e, integral_add I123 I4, integral_sub I12 I3, integral_sub I1 I2,
    key (fun t => t + v / 2) (fun t => t - x + v / 2) (v / 2) x (fun t => rfl) (fun t => by ring),
    key (fun t => t + v / 2) (fun t => t - x - v / 2) (v / 2) (x + v) (fun t => rfl)
      (fun t => by ring),
    key (fun t => t - v / 2) (fun t => t - x + v / 2) (-(v / 2)) (x - v) (fun t => by ring)
      (fun t => by ring),
    key (fun t => t - v / 2) (fun t => t - x - v / 2) (-(v / 2)) x (fun t => by ring)
      (fun t => by ring)]
  ring

/-- The autocorrelation of a bump supported in `[−w, w]` vanishes beyond `2w`. -/
theorem weilTest_self_eq_zero_of_lt {b : ℝ → ℂ} {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {y : ℝ}
    (hy : 2 * w < |y|) : EF.weilTest b b y = 0 := by
  rw [RHTower.weilTest_apply]
  have hz : (fun t => b t * conj (b (t - y))) = fun _ => 0 := funext fun t => by
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
    have h3 := hbs t h1
    have h4 := hbs (t - y) fun h => h2 (by rw [h, map_zero])
    have : |y| ≤ 2 * w := by
      calc |y| = |t - (t - y)| := by ring_nf
        _ ≤ |t| + |t - y| := abs_sub _ _
        _ ≤ 2 * w := by linarith
    linarith
  rw [hz, integral_zero]

/-- `‖κ_w‖² > 0`. -/
theorem integral_norm_sq_modScaledBump_pos {w : ℝ} (hw : 0 < w) :
    0 < ∫ t, ‖modScaledBump w 0 t‖ ^ 2 := by
  have hbs := modScaledBump_support hw 0
  have hbc : HasCompactSupport (modScaledBump w 0) := hasCompactSupport_of_support_subset_abs hbs
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    ((contDiff_modScaledBump_two w 0).continuous.norm.pow 2)
    (hbc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)) (fun t => by positivity) ?_
  have h1 : weilBump 0 = 1 := weilBump.one_of_mem_closedBall
    (Metric.mem_closedBall_self weilBump.rIn_pos.le)
  simp [modScaledBump, scaledBump, weilBumpC, h1]

/-! ### The comb on the off-line lattice -/

/-- A nonzero integer multiple of `L > 2w` lies beyond `2w`. -/
theorem lt_abs_int_mul {w L : ℝ} (hw : 0 < w) (hL : 2 * w < L) {j : ℤ} (hj : j ≠ 0) :
    2 * w < |(j : ℝ) * L| := by
  have h1 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
  have hL0 : 0 < L := by linarith
  rw [abs_mul, abs_of_pos hL0]
  nlinarith [mul_le_mul_of_nonneg_right h1 hL0.le]

/-- **Teeth of the comb.** For `L > 4w` and `n ≥ 1`, the test `κ_w(t + nL/2) − κ_w(t − nL/2)` has
`W = 4L‖κ_w‖²(1 − cosh(nδL))` on the off-line lattice. -/
theorem W_offLineLattice_lag_nat_mul {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {w : ℝ} (hw : 0 < w) (hwL : 4 * w < L) {n : ℕ} (hn : 1 ≤ n) :
    (offLineLatticeConfig hL hδ hδ').W (twoBump (modScaledBump w 0) (n * L) (-1))
        (twoBump (modScaledBump w 0) (n * L) (-1)) =
      ((4 * L * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * (1 - Real.cosh (n * δ * L)) : ℝ) : ℂ) := by
  classical
  set b := modScaledBump w 0 with hbdef
  have hbs := modScaledBump_support hw 0
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  have h2w : 2 * w < L := by linarith
  set K := EF.weilTest b b with hK
  have hKz : ∀ y : ℝ, 2 * w < |y| → K y = 0 := fun y hy => weilTest_self_eq_zero_of_lt hbs hy
  have hKj : ∀ j : ℤ, j ≠ 0 → K (j * L) = 0 := fun j hj => hKz _ (lt_abs_int_mul hw h2w hj)
  set K₀ := ∫ t, ‖b t‖ ^ 2 with hK₀
  have hK0 : K 0 = (K₀ : ℂ) := weilTest_self_zero b
  have hk : ∀ x : ℝ, EF.weilTest (twoBump b (n * L) (-1)) (twoBump b (n * L) (-1)) x =
      2 * K x - K (x + n * L) - K (x - n * L) :=
    weilTest_twoBump_neg_one hb.continuous hbc (n * L)
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [W_offLineLatticeConfig_lag hL hδ hδ' (f := twoBump b (n * L) (-1))
    (contDiff_bumpTest hb (n * L) ![1, -1]) (hasCompactSupport_twoBump hbc (n * L) (-1))]
  -- only the atoms `m = 0, ±n` survive
  have hsum : ∑' m : ℤ, EF.weilTest (twoBump b (n * L) (-1)) (twoBump b (n * L) (-1)) (m * L) *
      (((2 * Real.cosh (δ * (m * L))) : ℝ) : ℂ) =
      ∑ m ∈ ({0, (n : ℤ), -(n : ℤ)} : Finset ℤ),
        EF.weilTest (twoBump b (n * L) (-1)) (twoBump b (n * L) (-1)) (m * L) *
          (((2 * Real.cosh (δ * (m * L))) : ℝ) : ℂ) := by
    refine tsum_eq_sum fun m hm => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨h0, h1, h2⟩ := hm
    rw [hk, hKj m h0, show (m : ℝ) * L + n * L = ((m + n : ℤ) : ℝ) * L by push_cast; ring,
      hKj _ (by omega), show (m : ℝ) * L - n * L = ((m - n : ℤ) : ℝ) * L by push_cast; ring,
      hKj _ (by omega)]
    simp
  rw [hsum, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_singleton]
  rw [hk, hk, hk]
  have e1 : ((0 : ℤ) : ℝ) * L + n * L = ((n : ℤ) : ℝ) * L := by push_cast; ring
  have e2 : ((0 : ℤ) : ℝ) * L - n * L = ((-(n : ℤ) : ℤ) : ℝ) * L := by push_cast; ring
  have e3 : ((n : ℤ) : ℝ) * L + n * L = ((2 * n : ℤ) : ℝ) * L := by push_cast; ring
  have e4 : ((n : ℤ) : ℝ) * L - n * L = 0 := by push_cast; ring
  have e5 : ((-(n : ℤ) : ℤ) : ℝ) * L + n * L = 0 := by push_cast; ring
  have e6 : ((-(n : ℤ) : ℤ) : ℝ) * L - n * L = ((-(2 * n) : ℤ) : ℝ) * L := by push_cast; ring
  rw [e1, e2, e3, e4, e5, e6, Int.cast_zero, zero_mul, hKj _ hn0, hKj _ (by omega),
    hKj _ (by omega), hKj _ (by omega), hK0]
  have c1 : δ * (((n : ℤ) : ℝ) * L) = n * δ * L := by push_cast; ring
  have c2 : δ * (((-(n : ℤ) : ℤ) : ℝ) * L) = -(n * δ * L) := by push_cast; ring
  rw [c1, c2, Real.cosh_neg, mul_zero, Real.cosh_zero]
  push_cast
  ring

theorem re_W_offLineLattice_lag_nat_mul_neg {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {w : ℝ} (hw : 0 < w) (hwL : 4 * w < L) {n : ℕ} (hn : 1 ≤ n) :
    ((offLineLatticeConfig hL hδ hδ').W (twoBump (modScaledBump w 0) (n * L) (-1))
        (twoBump (modScaledBump w 0) (n * L) (-1))).re < 0 := by
  rw [W_offLineLattice_lag_nat_mul hL hδ hδ' hw hwL hn, Complex.ofReal_re]
  have hK := integral_norm_sq_modScaledBump_pos hw
  have hc : 1 < Real.cosh (n * δ * L) := Real.one_lt_cosh.mpr (by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity)
  have : 0 < 4 * L * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 := by positivity
  nlinarith

/-- **Gaps of the comb.** For `L > 4w`, `v > 2w` and `|v − nL| > 2w` for every `n ≥ 1`, the test
`κ_w(t + v/2) − κ_w(t − v/2)` has `W = 4L‖κ_w‖²` on the off-line lattice. -/
theorem W_offLineLattice_lag_eq_of_gap {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {w : ℝ} (hw : 0 < w) (hwL : 4 * w < L) {v : ℝ} (hv : 2 * w < v)
    (hgap : ∀ n : ℕ, 1 ≤ n → 2 * w < |v - n * L|) :
    (offLineLatticeConfig hL hδ hδ').W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)) =
      ((4 * L * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 : ℝ) : ℂ) := by
  set b := modScaledBump w 0 with hbdef
  have hbs := modScaledBump_support hw 0
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  have h2w : 2 * w < L := by linarith
  set K := EF.weilTest b b with hK
  have hKz : ∀ y : ℝ, 2 * w < |y| → K y = 0 := fun y hy => weilTest_self_eq_zero_of_lt hbs hy
  have hk : ∀ x : ℝ, EF.weilTest (twoBump b v (-1)) (twoBump b v (-1)) x =
      2 * K x - K (x + v) - K (x - v) := weilTest_twoBump_neg_one hb.continuous hbc v
  rw [W_offLineLatticeConfig_lag hL hδ hδ' (f := twoBump b v (-1))
    (contDiff_bumpTest hb v ![1, -1]) (hasCompactSupport_twoBump hbc v (-1))]
  have hv0 : 0 < v := by linarith
  rw [tsum_eq_single 0 fun m hm => ?_]
  · rw [hk, Int.cast_zero, zero_mul, zero_add, zero_sub, hKz v (by rw [abs_of_pos hv0]; exact hv),
      hKz (-v) (by rw [abs_neg, abs_of_pos hv0]; exact hv), hK, weilTest_self_zero, mul_zero,
      Real.cosh_zero]
    push_cast
    ring
  · rw [hk, hKz _ (lt_abs_int_mul hw h2w hm)]
    rcases lt_or_gt_of_ne hm with hneg | hpos
    · -- `m = −n` with `n ≥ 1`
      obtain ⟨n, hn⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
      have hn1 : 1 ≤ n := by omega
      have hmR : (m : ℝ) = -(n : ℝ) := by rw [hn]; push_cast; ring
      rw [hKz (m * L + v) (by rw [hmR, show -(n : ℝ) * L + v = v - n * L by ring]; exact hgap n hn1),
        hKz (m * L - v) (by
          rw [hmR, abs_of_neg (by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
          nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
      simp
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, m = (n : ℤ) := ⟨m.natAbs, by omega⟩
      have hn1 : 1 ≤ n := by omega
      have hmR : (m : ℝ) = n := by rw [hn]; push_cast; ring
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      rw [hKz (m * L + v) (by
          rw [hmR, abs_of_pos (by nlinarith)]
          nlinarith),
        hKz (m * L - v) (by rw [hmR, abs_sub_comm]; exact hgap n hn1)]
      simp

/-- **Silence up to the threshold.** For `0 ≤ v ≤ L − 2w` the test `κ_w(t + v/2) − κ_w(t − v/2)`
has aperture at most `L/2`, and `Re W ≥ 0` on the off-line lattice. -/
theorem re_W_offLineLattice_lag_nonneg_of_le {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {w : ℝ} (hw : 0 < w) {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ L - 2 * w) :
    0 ≤ ((offLineLatticeConfig hL hδ hδ').W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re := by
  have hbs := modScaledBump_support hw 0
  have hsupp : tsupport (twoBump (modScaledBump w 0) v (-1)) ⊆ Icc (-(v / 2 + w)) (v / 2 + w) := by
    refine closure_minimal (fun t ht => ?_) isClosed_Icc
    have ht' : twoBump (modScaledBump w 0) v (-1) t ≠ 0 := ht
    rw [twoBump_apply] at ht'
    by_cases h1 : modScaledBump w 0 (t + v / 2) = 0
    · have h2 : modScaledBump w 0 (t - v / 2) ≠ 0 := fun h => ht' (by rw [h1, h]; ring)
      obtain ⟨h3, h4⟩ := abs_le.mp (hbs _ h2)
      exact ⟨by linarith, by linarith⟩
    · obtain ⟨h3, h4⟩ := abs_le.mp (hbs _ h1)
      exact ⟨by linarith, by linarith⟩
  exact ((offLineLattice_weil_positive_iff hL hδ hδ' (v / 2 + w)).mpr (by linarith)) _
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1]) hsupp

/-- **The lag family meets the crystal at the threshold.** For `L > 4w`, the one-parameter family
is Weil-nonnegative on the off-line lattice for every lag `0 ≤ v ≤ L − 2w` (aperture `≤ L/2`) and
negative at `v = L` (aperture `L/2 + w`), whatever the depth `δ > 0`. -/
theorem lag_family_meets_crystal_at_threshold {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {w : ℝ} (hw : 0 < w) (hwL : 4 * w < L) :
    (∀ v : ℝ, 0 ≤ v → v ≤ L - 2 * w → 0 ≤ ((offLineLatticeConfig hL hδ hδ').W
      (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re) ∧
    ((offLineLatticeConfig hL hδ hδ').W (twoBump (modScaledBump w 0) L (-1))
      (twoBump (modScaledBump w 0) L (-1))).re < 0 := by
  refine ⟨fun v hv0 hv => re_W_offLineLattice_lag_nonneg_of_le hL hδ hδ' hw hv0 hv, ?_⟩
  have h := re_W_offLineLattice_lag_nat_mul_neg hL hδ hδ' hw hwL (n := 1) le_rfl
  simpa using h

end GaloisForLFunctions.SquareRootThreshold
