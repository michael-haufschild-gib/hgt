import GaloisForLFunctions.WorldsOfTheZeroConfiguration.EveryFiniteLayerIsRealizedByATwoSidedEdit
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheBalanceLawOfTwoSidedEdits

/-!
# Every configuration that approaches the line is realized

A configuration that approaches the line is a sequence `ρ_j` of points whose real parts decrease
to `1/2` without reaching it: `1/2 < Re ρ_{j+1} ≤ Re ρ_j < 14/15` and `Re ρ_j → 1/2`.  The
heights are arbitrary and a point may occur several times.

The target switches the pair `ρ_j, ρ̄_j` on at `2^{j+1}`:

`m(k) = −Σ_{j < log₂ k} 2 Re k^{ρ_j − 1}` (`landingTarget`).

At `k` at most `log₂ k` pairs are on, so `m(k) = O(k^{b−1})` for every `b > Re ρ_0` and the greedy
edit of the primes against `m` has discrepancy `O(√n)`.

**Theorem** (`isLayerTwinOn_landing`).  For every `N`

`(s − 1) ζ_B(s) = (s − 1) ζ(s) · C_N · ∏_{j<N} (s − ρ_j)(s − ρ̄_j) · e^{H_N(s)}`,

with `H_N` holomorphic on `Re s > Re ρ_N`.  The target without its first `N` pairs
(`landingTail`) is `O(k^{x−1})` for every `x > Re ρ_N`: beyond `2^N` it is the sum of the pairs
`N ≤ j < log₂ k`, each of size `2 k^{Re ρ_N − 1}`.  Its Dirichlet series is holomorphic on
`Re s > Re ρ_N` and joins the regular part in the prescribed-factor theorem.

The continuations on the half-planes `Re s > Re ρ_N` agree and glue to one continuation of
`(s − 1) ζ_B(s)` to `Re s > 1/2` (`IsLandingTwin`).  Its zeros away from `1` and the zeros of `ζ`
are exactly the points `ρ_j`, `ρ̄_j`, with the multiplicities of the sequence
(`IsLandingTwin.hasFakeZeroSet`); the count is `A x + O(x^β)` for every `β > Re ρ_0`
(`exists_isEdit_landingTwin`).  If `ζ` does not vanish at one `ρ_j`, the system is an integer-norm
fake (`exists_isEdit_fake_with_landing`).

So infinitely many zeros off the line whose real parts approach the line are compatible with an
Euler product over the rational primes with multiplicities `0, 1, 2`, integer norms and a count
rate.
-/

open Complex Filter Topology Finset
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration

open PrimeEdits TwoSidedEdits

/-- The target of a configuration that approaches the line: the pair `ρ_j` is on from `2^(j+1)`. -/
def landingTarget (ρ : ℕ → ℂ) (k : ℕ) : ℝ := layerTarget (range (Nat.log 2 k)) ρ k

/-- The target without its first `N` pairs. -/
def landingTail (ρ : ℕ → ℂ) (N k : ℕ) : ℝ := landingTarget ρ k - layerTarget (range N) ρ k

/-- `B` is a **twin of `ζ` with the layer `ρ` on the half-plane `Re s > c`**. -/
def IsLayerTwinOn {ι : Type*} (c : ℝ) (B : BeurlingSystem) (J : Finset ι) (ρ : ι → ℂ) : Prop :=
  ∃ (C : ℂ) (H : ℂ → ℂ), C ≠ 0 ∧ DifferentiableOn ℂ H {s : ℂ | c < s.re} ∧
    ∀ s : ℂ, 1 < s.re → (s - 1) * B.zetaSeriesC s =
      zetaResidueUnit s * (C * layerFactor J ρ s * Complex.exp (H s))

/-- `B` is a **twin of `ζ` with the configuration `ρ`**: `(s − 1) ζ_B(s)` continues to
`Re s > 1/2`, and on every half-plane `Re s > Re ρ_N` it is `(s − 1) ζ(s)` times the factor of the
first `N` pairs times a zero-free factor. -/
def IsLandingTwin (B : BeurlingSystem) (ρ : ℕ → ℂ) : Prop :=
  ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
    (∀ s : ℂ, 1 < s.re → G s = (s - 1) * B.zetaSeriesC s) ∧
    ∀ N : ℕ, ∃ (C : ℂ) (H : ℂ → ℂ), C ≠ 0 ∧
      DifferentiableOn ℂ H {s : ℂ | (ρ N).re < s.re} ∧
      ∀ s : ℂ, (ρ N).re < s.re →
        G s = zetaResidueUnit s * (C * layerFactor (range N) ρ s * Complex.exp (H s))

/-! ## The size of the target -/

theorem landingTarget_zero (ρ : ℕ → ℂ) : landingTarget ρ 0 = 0 := by
  simp [landingTarget, layerTarget]

/-- At `k` at most `(2/ε) k^ε` pairs are on. -/
theorem natLog_two_le {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) :
    (Nat.log 2 k : ℝ) ≤ 2 / ε * (k : ℝ) ^ ε := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hpow : (2 : ℝ) ^ Nat.log 2 k ≤ k := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : k ≠ 0)
  have h1 : (Nat.log 2 k : ℝ) * Real.log 2 ≤ Real.log k := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have h2 : Real.log k ≤ (k : ℝ) ^ ε / ε := Real.log_le_rpow_div hk0.le hε
  have h3 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h4 : (Nat.log 2 k : ℝ) * (1 / 2) ≤ (Nat.log 2 k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
  have h5 : 2 / ε * (k : ℝ) ^ ε = 2 * ((k : ℝ) ^ ε / ε) := by ring
  rw [h5]
  linarith

theorem abs_landingTarget_le {ρ : ℕ → ℂ} (hanti : Antitone fun j => (ρ j).re) {b₀ ε : ℝ}
    (hb₀ : (ρ 0).re ≤ b₀) (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) :
    |landingTarget ρ k| ≤ 4 / ε * (k : ℝ) ^ (-(1 - (b₀ + ε))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := abs_layerTarget_le (range (Nat.log 2 k)) ρ (b := b₀)
    (fun j _ => le_trans (hanti (Nat.zero_le j)) hb₀) hk
  rw [Finset.card_range] at h1
  have h2 := natLog_two_le hε hk
  have h3 : 0 ≤ (k : ℝ) ^ (-(1 - b₀)) := Real.rpow_nonneg hk0.le _
  have h4 : (k : ℝ) ^ (-(1 - (b₀ + ε))) = (k : ℝ) ^ ε * (k : ℝ) ^ (-(1 - b₀)) := by
    rw [← Real.rpow_add hk0]
    congr 1
    ring
  calc |landingTarget ρ k| ≤ 2 * (Nat.log 2 k : ℝ) * (k : ℝ) ^ (-(1 - b₀)) := h1
    _ ≤ 2 * (2 / ε * (k : ℝ) ^ ε) * (k : ℝ) ^ (-(1 - b₀)) := by gcongr
    _ = 4 / ε * (k : ℝ) ^ (-(1 - (b₀ + ε))) := by rw [h4]; ring

/-- The mass of the target is `O(n^b)` for every `b > Re ρ_0`. -/
theorem exists_sum_abs_landingTarget_le {ρ : ℕ → ℂ} (hanti : Antitone fun j => (ρ j).re) {b : ℝ}
    (hb : (ρ 0).re < b) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Ioc 0 n, |landingTarget ρ k| ≤ K * (n : ℝ) ^ b := by
  have hε : 0 < b - (ρ 0).re := sub_pos.mpr hb
  refine ⟨4 / (b - (ρ 0).re) / b, by positivity, fun n _ => ?_⟩
  have hI : Ioc 0 n = Icc 1 n := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  calc ∑ k ∈ Ioc 0 n, |landingTarget ρ k|
      ≤ ∑ k ∈ Icc 1 n, 4 / (b - (ρ 0).re) * (k : ℝ) ^ (b - 1) := by
        rw [hI]
        refine Finset.sum_le_sum fun k hk => ?_
        have h := abs_landingTarget_le hanti (le_refl (ρ 0).re) hε (Finset.mem_Icc.mp hk).1
        rwa [show -(1 - ((ρ 0).re + (b - (ρ 0).re))) = b - 1 by ring] at h
    _ = 4 / (b - (ρ 0).re) * ∑ k ∈ Icc 1 n, (k : ℝ) ^ (b - 1) := by rw [Finset.mul_sum]
    _ ≤ 4 / (b - (ρ 0).re) * ((n : ℝ) ^ b / b) :=
        mul_le_mul_of_nonneg_left (DeletionData.sum_rpow_le hb0 hb1 n) (by positivity)
    _ = 4 / (b - (ρ 0).re) / b * (n : ℝ) ^ b := by ring

/-! ## The tail of the target -/

/-- The target without its first `N` pairs is `O(k^{x−1})` for every `x > Re ρ_N`. -/
theorem abs_landingTail_le {ρ : ℕ → ℂ} (hanti : Antitone fun j => (ρ j).re)
    (h0 : (ρ 0).re ≤ 1) (N : ℕ) {x : ℝ} (hx : (ρ N).re < x) (hx0 : 0 ≤ x) {k : ℕ}
    (hk : 1 ≤ k) :
    |landingTail ρ N k| ≤ (4 / (x - (ρ N).re) + 2 * N * 2 ^ N) * (k : ℝ) ^ (x - 1) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hε : 0 < x - (ρ N).re := sub_pos.mpr hx
  have hpw : 0 ≤ (k : ℝ) ^ (x - 1) := Real.rpow_nonneg hk0.le _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  rcases le_or_gt N (Nat.log 2 k) with hN | hN
  · -- beyond `2^N`: the pairs `N ≤ j < log₂ k`
    have hsplit : landingTail ρ N k = ∑ j ∈ Ico N (Nat.log 2 k), target (ρ j) k := by
      simp only [landingTail, landingTarget, layerTarget]
      rw [← Finset.sum_range_add_sum_Ico _ hN]
      ring
    have hterm : ∀ j ∈ Ico N (Nat.log 2 k),
        |target (ρ j) k| ≤ 2 * (k : ℝ) ^ ((ρ N).re - 1) := by
      intro j hj
      have hjN : (ρ j).re ≤ (ρ N).re := hanti (Finset.mem_Ico.mp hj).1
      have h1 : (k : ℝ) ^ ((ρ j).re - 1) ≤ (k : ℝ) ^ ((ρ N).re - 1) :=
        Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
      linarith [abs_target_le (ρ j) hk]
    have hcard : ((Ico N (Nat.log 2 k)).card : ℝ) ≤ 2 / (x - (ρ N).re) * (k : ℝ) ^ (x - (ρ N).re) := by
      refine le_trans ?_ (natLog_two_le hε hk)
      rw [Nat.card_Ico]
      exact_mod_cast Nat.sub_le _ _
    have hkk : (k : ℝ) ^ (x - (ρ N).re) * (k : ℝ) ^ ((ρ N).re - 1) = (k : ℝ) ^ (x - 1) := by
      rw [← Real.rpow_add hk0]
      congr 1
      ring
    have hq : 0 ≤ 2 * (k : ℝ) ^ ((ρ N).re - 1) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hk0.le _)
    calc |landingTail ρ N k| ≤ ∑ j ∈ Ico N (Nat.log 2 k), |target (ρ j) k| := by
          rw [hsplit]
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Ico N (Nat.log 2 k), 2 * (k : ℝ) ^ ((ρ N).re - 1) := Finset.sum_le_sum hterm
      _ = (Ico N (Nat.log 2 k)).card * (2 * (k : ℝ) ^ ((ρ N).re - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 / (x - (ρ N).re) * (k : ℝ) ^ (x - (ρ N).re) * (2 * (k : ℝ) ^ ((ρ N).re - 1)) :=
          mul_le_mul_of_nonneg_right hcard hq
      _ = 4 / (x - (ρ N).re) * (k : ℝ) ^ (x - 1) := by rw [← hkk]; ring
      _ ≤ (4 / (x - (ρ N).re) + 2 * N * 2 ^ N) * (k : ℝ) ^ (x - 1) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hpw
  · -- below `2^N`: at most `N` pairs, each of size at most `2`
    have hsplit : landingTail ρ N k = -∑ j ∈ Ico (Nat.log 2 k) N, target (ρ j) k := by
      simp only [landingTail, landingTarget, layerTarget]
      rw [← Finset.sum_range_add_sum_Ico _ hN.le]
      ring
    have hterm : ∀ j ∈ Ico (Nat.log 2 k) N, |target (ρ j) k| ≤ 2 := by
      intro j _
      have hj0 : (ρ j).re ≤ (ρ 0).re := hanti (Nat.zero_le j)
      have h1 : (k : ℝ) ^ ((ρ j).re - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hk1 (by linarith)
      linarith [abs_target_le (ρ j) hk]
    have hcard : ((Ico (Nat.log 2 k) N).card : ℝ) ≤ N := by
      rw [Nat.card_Ico]
      exact_mod_cast Nat.sub_le _ _
    have hk2 : k < 2 ^ N := Nat.lt_pow_of_log_lt (by norm_num) hN
    have hone : 1 ≤ (2 : ℝ) ^ N * (k : ℝ) ^ (x - 1) := by
      have h1 : (k : ℝ) ^ (-1 : ℝ) ≤ (k : ℝ) ^ (x - 1) :=
        Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
      have h3 : (k : ℝ) ≤ 2 ^ N := by exact_mod_cast hk2.le
      have h4 : 1 ≤ (2 : ℝ) ^ N * (k : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hk0]
        linarith
      exact h4.trans (mul_le_mul_of_nonneg_left h1 h2N.le)
    calc |landingTail ρ N k| ≤ ∑ j ∈ Ico (Nat.log 2 k) N, |target (ρ j) k| := by
          rw [hsplit, abs_neg]
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Ico (Nat.log 2 k) N, (2 : ℝ) := Finset.sum_le_sum hterm
      _ = (Ico (Nat.log 2 k) N).card * 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * 2 := mul_le_mul_of_nonneg_right hcard (by norm_num)
      _ ≤ 2 * N * (2 ^ N * (k : ℝ) ^ (x - 1)) := by nlinarith
      _ ≤ (4 / (x - (ρ N).re) + 2 * N * 2 ^ N) * (k : ℝ) ^ (x - 1) := by
          have h5 : 0 ≤ 4 / (x - (ρ N).re) * (k : ℝ) ^ (x - 1) := by positivity
          nlinarith

theorem exists_norm_landingTail_le {ρ : ℕ → ℂ} (hanti : Antitone fun j => (ρ j).re)
    (h0 : (ρ 0).re ≤ 1) (N : ℕ) {x : ℝ} (hx : (ρ N).re < x) (hx0 : 0 ≤ x) :
    ∃ C : ℝ, ∀ n : ℕ, n ≠ 0 → ‖((landingTail ρ N n : ℝ) : ℂ)‖ ≤ C * (n : ℝ) ^ (x - 1) :=
  ⟨_, fun n hn => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_landingTail_le hanti h0 N hx hx0 (Nat.one_le_iff_ne_zero.mpr hn)⟩

/-- The Dirichlet series of the tail of the target is holomorphic on `Re s > Re ρ_N`. -/
theorem differentiableOn_lseries_landingTail {ρ : ℕ → ℂ} (hanti : Antitone fun j => (ρ j).re)
    (h0 : (ρ 0).re ≤ 1) (hpos : ∀ j, 0 ≤ (ρ j).re) (N : ℕ) :
    DifferentiableOn ℂ (LSeries fun k : ℕ => ((landingTail ρ N k : ℝ) : ℂ))
      {s : ℂ | (ρ N).re < s.re} := by
  intro s hs
  have hs' : (ρ N).re < s.re := hs
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ((ρ N).re + s.re) / 2 := ⟨_, rfl⟩
  have hx1 : (ρ N).re < x := by rw [hx]; linarith
  have hx2 : x < s.re := by rw [hx]; linarith
  have habs : LSeries.abscissaOfAbsConv (fun k : ℕ => ((landingTail ρ N k : ℝ) : ℂ)) < s.re := by
    have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
      (exists_norm_landingTail_le hanti h0 N hx1 (by linarith [hpos N]))
    have hcast : (((x - 1 : ℝ) : EReal) + 1) = (x : EReal) := by
      rw [← EReal.coe_one, ← EReal.coe_add]
      congr 1
      ring
    rw [hcast] at h
    exact lt_of_le_of_lt h (by exact_mod_cast hx2)
  exact (LSeries_hasDerivAt habs).differentiableAt.differentiableWithinAt

/-! ## The edit of a configuration -/

/-- **The first `N` pairs split off on `Re s > Re ρ_N`.**  The greedy edit of the target of a
configuration that approaches the line is, on the half-plane right of `ρ_N`, a twin of `ζ` with
the layer of the first `N` pairs. -/
theorem isLayerTwinOn_landing {ρ : ℕ → ℂ} (hanti : Antitone fun j => (ρ j).re)
    (hhalf : ∀ j, 1 / 2 < (ρ j).re) (h0 : (ρ 0).re < 14 / 15) (N : ℕ) :
    IsLayerTwinOn (ρ N).re (editSystem (gedit (landingTarget ρ))) (range N) ρ := by
  have hσ1 : ∀ j, (ρ j).re < 1 := fun j =>
    lt_of_le_of_lt (hanti (Nat.zero_le j)) (by linarith)
  -- the size of the target
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ((ρ 0).re + 14 / 15) / 2 := ⟨_, rfl⟩
  have hb0 : (ρ 0).re < b := by rw [hb]; linarith
  have hb1 : b < 14 / 15 := by rw [hb]; linarith
  have hbhalf : 1 / 2 < b := lt_trans (hhalf 0) hb0
  have hmabs : ∀ k : ℕ, 1 ≤ k →
      |landingTarget ρ k| ≤ 4 / (b - (ρ 0).re) * (k : ℝ) ^ (-(1 - b)) := by
    intro k hk
    have h := abs_landingTarget_le hanti (le_refl (ρ 0).re) (sub_pos.mpr hb0) hk
    rwa [show (ρ 0).re + (b - (ρ 0).re) = b by ring] at h
  -- the discrepancy of the edit
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (17 / 30 + (3 / 2 - b)) / 2 := ⟨_, rfl⟩
  have hα0 : 17 / 30 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have hαc : α - (1 - b) ≤ (ρ N).re := by rw [hα]; linarith [hhalf N]
  obtain ⟨X, -, hwin⟩ := RHTower.exists_theta_window_lower_seventeenThirtieths hα0 hα1
  obtain ⟨K₀, hK₀, hdisc⟩ := exists_abs_gdisc_le_rpow_of_abs_le (m := landingTarget ρ)
    (A := 4 / (b - (ρ 0).re)) (η := 1 - b) (c := (ρ N).re)
    (div_nonneg (by norm_num) (sub_nonneg.mpr hb0.le)) (by linarith) (by linarith)
    hmabs hα1 (by linarith [hhalf N]) hαc hwin
  have hsumm : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun k => (landingTarget ρ k : ℂ)) s := by
    intro s hs
    refine LSeriesSummable_of_le_const_mul_rpow (x := b) (by linarith)
      ⟨4 / (b - (ρ 0).re), fun n hn => ?_⟩
    show ‖((landingTarget ρ n : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, show b - 1 = -(1 - b) by ring]
    exact hmabs n (Nat.one_le_iff_ne_zero.mpr hn)
  -- the target is the target of the first `N` pairs plus the tail
  have hmsplit : (fun k : ℕ => (landingTarget ρ k : ℂ)) =
      (fun k : ℕ => (layerTarget (range N) ρ k : ℂ)) +
        fun k : ℕ => ((landingTail ρ N k : ℝ) : ℂ) := by
    funext k
    simp only [Pi.add_apply, landingTail]
    push_cast
    ring
  have hΦ₀ : DifferentiableOn ℂ (fun s : ℂ =>
      ∑ j ∈ range N, (PrimeEdits.zetaRegular (s - (ρ j - 1)) +
        PrimeEdits.zetaRegular (s - ((starRingEnd ℂ) (ρ j) - 1))) -
      LSeries (fun k : ℕ => ((landingTail ρ N k : ℝ) : ℂ)) s) {s : ℂ | (ρ N).re < s.re} := by
    refine DifferentiableOn.sub (DifferentiableOn.fun_sum fun j _ => ?_)
      (differentiableOn_lseries_landingTail hanti (by linarith)
        (fun j => by linarith [hhalf j]) N)
    exact ((PrimeEdits.differentiable_zetaRegular.comp (differentiable_id.sub_const _)).add
      (PrimeEdits.differentiable_zetaRegular.comp
        (differentiable_id.sub_const _))).differentiableOn
  have hL : ∀ s : ℂ, 1 < s.re → layerFactor (range N) ρ s ≠ 0 ∧
      DifferentiableAt ℂ (layerFactor (range N) ρ) s ∧
      logDeriv (layerFactor (range N) ρ) s = -LSeries (fun k => (landingTarget ρ k : ℂ)) s -
        (∑ j ∈ range N, (PrimeEdits.zetaRegular (s - (ρ j - 1)) +
          PrimeEdits.zetaRegular (s - ((starRingEnd ℂ) (ρ j) - 1))) -
        LSeries (fun k : ℕ => ((landingTail ρ N k : ℝ) : ℂ)) s) := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := logDeriv_layerFactor_eq (range N) ρ (fun j _ => hσ1 j) hs
    refine ⟨h1, h2, ?_⟩
    have hsl : LSeriesSummable (fun k : ℕ => (layerTarget (range N) ρ k : ℂ)) s :=
      (lseriesHasSum_layerTarget (range N) ρ fun j _ => lt_trans (hσ1 j) hs).LSeriesSummable
    have hst : LSeriesSummable (fun k : ℕ => ((landingTail ρ N k : ℝ) : ℂ)) s :=
      LSeriesSummable_of_le_const_mul_rpow (x := 1) hs
        (exists_norm_landingTail_le hanti (by linarith) N (hσ1 N) (by norm_num))
    rw [h3, hmsplit, LSeries_add hsl hst]
    ring
  obtain ⟨C, K, hC, hK, hfac⟩ := exists_exp_geditSeries_eq (m := landingTarget ρ)
    (landingTarget_zero ρ) hK₀ (by linarith [hhalf N]) (hσ1 N).le hdisc hsumm
    (L := layerFactor (range N) ρ) hΦ₀ hL
  have he := isEdit_gedit (landingTarget ρ)
  have hRem : DifferentiableOn ℂ (editRem (gedit (landingTarget ρ)))
      {s : ℂ | (ρ N).re < s.re} :=
    (differentiableOn_editRem he).mono fun s (hs : (ρ N).re < s.re) =>
      show (1 : ℝ) / 2 < s.re from lt_trans (hhalf N) hs
  refine ⟨C, fun s => K s + editRem (gedit (landingTarget ρ)) s, hC, hK.add hRem,
    fun s hs => ?_⟩
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have hEK : Complex.exp (LSeries (fun k => (gedit (landingTarget ρ) k : ℂ)) s +
      editRem (gedit (landingTarget ρ)) s) =
      C * layerFactor (range N) ρ s *
        Complex.exp (K s + editRem (gedit (landingTarget ρ)) s) := by
    rw [Complex.exp_add, hfac s hs, Complex.exp_add]
    ring
  rw [editSystem_zetaSeriesC he hs, hEK, zetaResidueUnit_of_ne hs1]
  ring

/-! ## Gluing the half-planes -/

/-- Holomorphic functions on a decreasing family of half-planes that agree right of `1` glue to
one holomorphic function on the union of the half-planes. -/
theorem exists_glue {σ : ℕ → ℝ} (hσ : Antitone σ) (hlim : ∀ x : ℝ, 1 / 2 < x → ∃ N, σ N < x)
    {F : ℂ → ℂ} {G : ℕ → ℂ → ℂ} (hG : ∀ N, DifferentiableOn ℂ (G N) {s : ℂ | σ N < s.re})
    (hGF : ∀ N (s : ℂ), 1 < s.re → G N s = F s) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → H s = F s) ∧ ∀ N (s : ℂ), σ N < s.re → H s = G N s := by
  classical
  -- two members of the family agree where both are defined
  have hcons : ∀ M N, M ≤ N → ∀ s : ℂ, σ M < s.re → G M s = G N s := by
    intro M N hMN s hs
    have hsub : {s : ℂ | σ M < s.re} ⊆ {s : ℂ | σ N < s.re} :=
      fun z (hz : σ M < z.re) => show σ N < z.re from lt_of_le_of_lt (hσ hMN) hz
    exact BalanceLaw.eqOn_halfPlane (hG M) ((hG N).mono hsub)
      (fun z hz => (hGF M z hz).trans (hGF N z hz).symm)
      (show s ∈ {s : ℂ | σ M < s.re} from hs)
  have hcons' : ∀ M N (s : ℂ), σ M < s.re → σ N < s.re → G M s = G N s := by
    intro M N s hM hN
    rcases le_total M N with h | h
    · exact hcons M N h s hM
    · exact (hcons N M h s hN).symm
  have hHG : ∀ N (s : ℂ), σ N < s.re →
      (if h : ∃ N, σ N < s.re then G (Nat.find h) s else 0) = G N s := by
    intro N s hs
    have h : ∃ N, σ N < s.re := ⟨N, hs⟩
    rw [dif_pos h]
    exact hcons' _ _ s (Nat.find_spec h) hs
  refine ⟨fun s => if h : ∃ N, σ N < s.re then G (Nat.find h) s else 0,
    fun s hs => ?_, fun s hs => ?_, hHG⟩
  · obtain ⟨N, hN⟩ := hlim s.re hs
    have hopen : IsOpen {z : ℂ | σ N < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hd : DifferentiableAt ℂ (G N) s := (hG N).differentiableAt (hopen.mem_nhds hN)
    exact (hd.congr_of_eventuallyEq
      (Filter.eventually_of_mem (hopen.mem_nhds hN) fun z hz => hHG N z hz)).differentiableWithinAt
  · obtain ⟨N, hN⟩ := hlim s.re (by linarith)
    exact (hHG N s hN).trans (hGF N s hs)

/-- Twins on the half-planes right of the points of a configuration that approaches the line
glue to a twin with the configuration. -/
theorem isLandingTwin_of_isLayerTwinOn {B : BeurlingSystem} {ρ : ℕ → ℂ}
    (hanti : Antitone fun j => (ρ j).re) (hlim : ∀ x : ℝ, 1 / 2 < x → ∃ N, (ρ N).re < x)
    (h : ∀ N, IsLayerTwinOn (ρ N).re B (range N) ρ) : IsLandingTwin B ρ := by
  choose C H hC hH hfac using h
  have hG : ∀ N, DifferentiableOn ℂ (fun s => zetaResidueUnit s *
      (C N * layerFactor (range N) ρ s * Complex.exp (H N s))) {s : ℂ | (ρ N).re < s.re} :=
    fun N => differentiable_zetaResidueUnit.differentiableOn.mul
      (((differentiableOn_const (C N)).mul
        (differentiable_layerFactor (range N) ρ).differentiableOn).mul (hH N).cexp)
  obtain ⟨G, hGd, hGF, hGN⟩ := exists_glue (σ := fun N => (ρ N).re) hanti hlim
    (F := fun s => (s - 1) * B.zetaSeriesC s) hG (fun N s hs => (hfac N s hs).symm)
  exact ⟨G, hGd, hGF, fun N => ⟨C N, H N, hC N, hH N, fun s hs => hGN N s hs⟩⟩

/-- The fake zeros of a twin with a configuration that approaches the line are exactly the points
of the configuration and their conjugates. -/
theorem IsLandingTwin.hasFakeZeroSet {B : BeurlingSystem} {ρ : ℕ → ℂ}
    (hanti : Antitone fun j => (ρ j).re) (hlim : ∀ x : ℝ, 1 / 2 < x → ∃ N, (ρ N).re < x)
    (h : IsLandingTwin B ρ) :
    HasFakeZeroSet B {z : ℂ | ∃ j, z = ρ j ∨ z = (starRingEnd ℂ) (ρ j)} := by
  obtain ⟨G, hG, hGF, hfac⟩ := h
  refine ⟨G, hG, hGF, fun z hz hz1 hzζ => ?_⟩
  obtain ⟨N, hN⟩ := hlim z.re hz
  obtain ⟨C, H, hC, -, hGN⟩ := hfac N
  have hzu : zetaResidueUnit z ≠ 0 := by
    rw [zetaResidueUnit_of_ne hz1]
    exact mul_ne_zero (sub_ne_zero.mpr hz1) hzζ
  rw [hGN z hN]
  simp only [mul_eq_zero, hzu, hC, Complex.exp_ne_zero, false_or, or_false,
    layerFactor_eq_zero_iff, Set.mem_setOf_eq, Finset.mem_range]
  constructor
  · rintro ⟨j, -, hj⟩
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_, hj⟩
    by_contra hjN
    -- a point `ρ_j` with `j ≥ N` lies left of `Re ρ_N < Re z`
    have hle : (ρ j).re ≤ (ρ N).re := hanti (not_lt.mp hjN)
    have hre : z.re = (ρ j).re := by
      rcases hj with h | h
      · rw [h]
      · rw [h, Complex.conj_re]
    linarith

/-! ## Existence -/

/-- **Every configuration that approaches the line is realized.**  For points `ρ_j` with
`1/2 < Re ρ_{j+1} ≤ Re ρ_j < 14/15` and `Re ρ_j → 1/2`, and every `β ∈ (Re ρ_0, 1)`, there is a
two-sided edit of the rational primes with count `A x + O(x^β)` whose fake zeros right of the
line are exactly the points `ρ_j`, `ρ̄_j`, with the multiplicities of the sequence. -/
theorem exists_isEdit_landingTwin {ρ : ℕ → ℂ} (hanti : Antitone fun j => (ρ j).re)
    (hhalf : ∀ j, 1 / 2 < (ρ j).re) (h0 : (ρ 0).re < 14 / 15)
    (hlim : ∀ x : ℝ, 1 / 2 < x → ∃ N, (ρ N).re < x) {β : ℝ} (hβ : (ρ 0).re < β)
    (hβ1 : β < 1) :
    ∃ e : ℕ → ℤ, IsEdit e ∧
      (∃ A C : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) ∧
      IsLandingTwin (editSystem e) ρ ∧
      HasFakeZeroSet (editSystem e) {z : ℂ | ∃ j, z = ρ j ∨ z = (starRingEnd ℂ) (ρ j)} := by
  have htwin := isLandingTwin_of_isLayerTwinOn hanti hlim
    (isLayerTwinOn_landing hanti hhalf h0)
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ((ρ 0).re + β) / 2 := ⟨_, rfl⟩
  have hb0 : (ρ 0).re < b := by rw [hb]; linarith
  have hbβ : b < β := by rw [hb]; linarith
  have hbpos : 0 < b := by linarith [hhalf 0]
  obtain ⟨K, hK, hmass⟩ := exists_sum_abs_landingTarget_le hanti hb0 hbpos (by linarith)
  exact ⟨gedit (landingTarget ρ), isEdit_gedit _,
    editSystem_count (by linarith) hβ1
      (summable_abs_gedit_rpow (θ := b) hbpos.le hK hmass hbβ),
    htwin, htwin.hasFakeZeroSet hanti hlim⟩

/-- An edit whose continuation vanishes at a point right of the line where `ζ` does not vanish
edits a prime. -/
theorem exists_ne_zero_of_fake_zero {e : ℕ → ℤ} (he : IsEdit e) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) {z : ℂ}
    (hz : 1 / 2 < z.re) (hz1 : z ≠ 1) (hzζ : riemannZeta z ≠ 0) (hGz : G z = 0) :
    ∃ k, e k ≠ 0 := by
  by_contra hall
  push Not at hall
  have heq : ∀ s : ℂ, 1 < s.re → G s = zetaResidueUnit s := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    have hfun : (fun k => (e k : ℂ)) = 0 := by
      funext k
      simp [hall k]
    have hL0 : LSeries (fun k => (e k : ℂ)) s = 0 := by
      rw [hfun]; simp
    have hR0 : editRem e s = 0 := by simp [editRem, hall]
    rw [hGF s hs, editSystem_zetaSeriesC he hs, hL0, hR0, add_zero, Complex.exp_zero, mul_one,
      zetaResidueUnit_of_ne hs1]
  have h0 := BalanceLaw.eqOn_halfPlane hG differentiable_zetaResidueUnit.differentiableOn heq
    (show z ∈ {s : ℂ | 1 / 2 < s.re} from hz)
  rw [hGz, zetaResidueUnit_of_ne hz1] at h0
  exact mul_ne_zero (sub_ne_zero.mpr hz1) hzζ h0.symm

/-- **A fake with infinitely many fake zeros approaching the line.**  If `ζ` does not vanish at
one point of the configuration, the edit is an integer-norm fake at every `β ∈ (Re ρ_0, 1)` whose
fake zeros right of the line are exactly the points of the configuration and their conjugates. -/
theorem exists_isEdit_fake_with_landing {ρ : ℕ → ℂ} (hanti : Antitone fun j => (ρ j).re)
    (hhalf : ∀ j, 1 / 2 < (ρ j).re) (h0 : (ρ 0).re < 14 / 15)
    (hlim : ∀ x : ℝ, 1 / 2 < x → ∃ N, (ρ N).re < x) (hζ : ∃ j, riemannZeta (ρ j) ≠ 0)
    {β : ℝ} (hβ : (ρ 0).re < β) (hβ1 : β < 1) :
    ∃ e : ℕ → ℤ, IsEdit e ∧ IsIntegerNormFakeAt (editSystem e) β ∧
      IsLandingTwin (editSystem e) ρ ∧
      HasFakeZeroSet (editSystem e) {z : ℂ | ∃ j, z = ρ j ∨ z = (starRingEnd ℂ) (ρ j)} := by
  obtain ⟨j₀, hζ₀⟩ := hζ
  obtain ⟨e, he, hcount, htwin, hfake⟩ := exists_isEdit_landingTwin hanti hhalf h0 hlim hβ hβ1
  obtain ⟨G, hG, hGF, hzero⟩ := hfake
  have hρ₀ne : ρ j₀ ≠ 1 := fun h => by
    have h1 : (ρ j₀).re ≤ (ρ 0).re := hanti (Nat.zero_le j₀)
    rw [h, Complex.one_re] at h1
    linarith
  have hGz : G (ρ j₀) = 0 := (hzero (ρ j₀) (hhalf j₀) hρ₀ne hζ₀).mpr ⟨j₀, Or.inl rfl⟩
  obtain ⟨k, hk⟩ := exists_ne_zero_of_fake_zero he hG hGF (hhalf j₀) hρ₀ne hζ₀ hGz
  exact ⟨e, he, ⟨hasIntegerNorms_editSystem _, isDiscrete_editSystem _,
    notNormEquivPrimes_editSystem he hk, hcount, G, hG, hGF, ρ j₀, hhalf j₀, hρ₀ne, hGz, hζ₀⟩,
    htwin, ⟨G, hG, hGF, hzero⟩⟩

end GaloisForLFunctions.WorldsOfTheZeroConfiguration
