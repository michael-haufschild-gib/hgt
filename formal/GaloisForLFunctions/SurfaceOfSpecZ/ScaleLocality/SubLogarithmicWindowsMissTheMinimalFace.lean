import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.HighFrequencyBinomialPolynomials

/-!
# Resolution of the minimal face for class `𝒵`: sub-logarithmic windows do not decide `𝒵`

This module resolves both parts of the minimal-face scale-locality question for the class `𝒵` of
tempered reflection-symmetric zero configurations without real zeros, with lowest ordinate at least
`γ_min > 0` and local counts `N(t, t + 1) ≤ C log(|t| + 3)`:

1. **Unbounded sub-logarithmic windows (Question 2).** Not every unbounded radius `R(T) → ∞`
   decides `𝒵`. For every `γ_min > 0`, `C > 0`, and `0 < Θ ≤ 1/2`, there exist a configuration
   `Z ∈ 𝒵(γ_min, C)` of simple zeros (`mult ≡ 1`) with unattained accumulating top
   `sup_{ρ ∈ Z} Re ρ = 1/2 + Θ` (`Re ρ < 1/2 + Θ` for all `ρ ∈ Z`) and a monotone unbounded
   sub-logarithmic radius `R(T) → ∞` with `R(T) = o(log T)` such that `2 Re S_Z(u)` is bounded
   below beyond every bound on windows `[T_k − R(T_k), T_k + R(T_k)]` as `T_k → ∞`:
   `∀ K U : ℝ, ∃ T ≥ U, ∀ u ∈ [T − R(T), T + R(T)], 2 Re S_Z(u) ≥ K`.
2. **Bounded windows (Question 1).** Consequently, there is no window length `L = L(γ_min, C)`
   such that a floor `2 Re S_Z(u) ≥ −K` on windows `[u_k, u_k + L]` (`u_k → ∞`) forces every zero
   of a configuration in `𝒵` onto the critical line. In fact, a single universal configuration
   `Z ∈ 𝒵(γ_min, C)` simultaneously defeats every bounded window length `L > 0` and every floor `K`.
3. **Prime-power and prime-window corollaries.** Since `[T − R(T), T + R(T)]` contains all prime
   logarithms `log p` in that interval, the same configuration satisfies `2 Re S_Z(log p) ≥ K` for
   all primes `p` with `|log p − T| ≤ R(T)` (and on bounded prime windows `log p ∈ [u_k, u_k + L]`),
   including at the maximal strip boundary `Θ = 1/2` (`sup Re ρ = 1`).
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23 SplineTower

/-! ### Tower dominance with diverging window floors -/

/-- Variant of the Wolff-tower dominance lemma at the top active window `k + 1`: when `u` lies
below the right endpoint `U (k + 1)` of window `k + 1` and the `(k + 1)`-st term dominates the
earlier levels `0, …, k` with a surplus `M + 9` (`0 ≤ M`), the full series is at least `M`. -/
theorem tsum_ge_of_top_window {Θ : ℝ} (hΘ : 0 < Θ) {x w U a b : ℕ → ℝ}
    (hx0 : ∀ j, 0 ≤ x j) (hxΘ : ∀ j, x j ≤ Θ) (hxm : Monotone x) (hw : ∀ j, 0 ≤ w j)
    (hw0 : w 0 ≤ 1) (hwhi : ∀ j, w (j + 1) ≤ (1 / 2) ^ (j + 1) * Real.exp (-(Θ * U j)))
    (hUm : Monotone U) (hU0 : 0 ≤ U 0) (ha : ∀ j, |a j| ≤ w j) (hb : ∀ j, |b j| ≤ w j)
    {u M : ℝ} (hu0 : 0 ≤ u) (hM : 0 ≤ M) {k : ℕ} (hku : u ≤ U (k + 1))
    (hdom : M + 9 ≤ Real.exp ((x (k + 1) - x k) * u) * a (k + 1)) :
    M ≤ ∑' j, (Real.exp (x j * u) * a j + Real.exp (-(x j * u)) * b j) := by
  have hwg := weight_le_geom hw0 hwhi hΘ.le hUm hU0
  have hgeo : Summable fun j : ℕ => 2 * (1 / 2 : ℝ) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
  have hwsum : Summable w := Summable.of_nonneg_of_le hw hwg hgeo
  have hwtot : ∑' j, w j ≤ 4 := by
    calc ∑' j, w j ≤ ∑' j : ℕ, 2 * (1 / 2 : ℝ) ^ j := Summable.tsum_le_tsum hwg hwsum hgeo
      _ = 4 := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
  have hexpx : ∀ j, Real.exp (x j * u) ≤ Real.exp (Θ * u) := fun j =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hxΘ j) hu0)
  have hrefl1 : ∀ j, Real.exp (-(x j * u)) ≤ 1 := fun j =>
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (hx0 j) hu0))
  have hmain : Summable fun j => Real.exp (x j * u) * a j := by
    refine Summable.of_norm_bounded (hwsum.mul_left (Real.exp (Θ * u))) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hexpx j) (ha j) (abs_nonneg _) (Real.exp_pos _).le
  have hrefl : Summable fun j => Real.exp (-(x j * u)) * b j := by
    refine Summable.of_norm_bounded hwsum fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(x j * u)) * |b j| ≤ 1 * |b j| :=
          mul_le_mul_of_nonneg_right (hrefl1 j) (abs_nonneg _)
      _ ≤ w j := by rw [one_mul]; exact hb j
  rw [hmain.tsum_add hrefl]
  have hR : -4 ≤ ∑' j, Real.exp (-(x j * u)) * b j := by
    have h := Summable.tsum_le_tsum (fun j => neg_le_mul_of_abs_le (Real.exp_pos _).le
      (hrefl1 j) (hb j)) hwsum.neg hrefl
    rw [tsum_neg] at h
    linarith
  have htail := neg_one_le_tail hΘ.le hxΘ hwhi hUm ha hu0 hku hmain
  have hE_ge_one : 1 ≤ Real.exp (x k * u) :=
    Real.one_le_exp (mul_nonneg (hx0 k) hu0)
  have hE_pos : 0 < Real.exp (x k * u) := Real.exp_pos _
  have hhead : -(4 * Real.exp (x k * u)) ≤
      ∑ j ∈ Finset.range (k + 1), Real.exp (x j * u) * a j := by
    have h1 : ∀ j ∈ Finset.range (k + 1), -(Real.exp (x k * u) * w j) ≤
        Real.exp (x j * u) * a j := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hx : Real.exp (x j * u) ≤ Real.exp (x k * u) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hxm hjk) hu0)
      have h2 := neg_mul_le_mul_of_abs_le (Real.exp_pos (x j * u)).le (ha j)
      have h3 := mul_le_mul_of_nonneg_right hx (hw j)
      linarith
    have h2 := Finset.sum_le_sum h1
    have h3 : ∑ j ∈ Finset.range (k + 1), w j ≤ 4 :=
      (hwsum.sum_le_tsum _ (fun j _ => hw j)).trans hwtot
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at h2
    have h4 := mul_le_mul_of_nonneg_left h3 hE_pos.le
    linarith
  have hsplit_exp : Real.exp (x (k + 1) * u) * a (k + 1) =
      Real.exp (x k * u) * (Real.exp ((x (k + 1) - x k) * u) * a (k + 1)) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have htop : 4 * Real.exp (x k * u) + (M + 5) ≤ Real.exp (x (k + 1) * u) * a (k + 1) := by
    rw [hsplit_exp]
    have h1 : Real.exp (x k * u) * (M + 9) ≤
        Real.exp (x k * u) * (Real.exp ((x (k + 1) - x k) * u) * a (k + 1)) :=
      mul_le_mul_of_nonneg_left hdom hE_pos.le
    have h2 : M + 5 ≤ Real.exp (x k * u) * (M + 5) := by nlinarith
    linarith
  rw [← hmain.sum_add_tsum_nat_add (k + 2), Finset.sum_range_succ]
  linarith

/-! ### Mutual recursion for base ordinates `Γ_k` and window centers `T_k` -/

/-- Level-dependent multiplier ensuring weight ceilings, temperedness, lowest ordinate `≥ γ_min`,
and local count bound `N(t, t + 1) ≤ C log(|t| + 3)`. -/
def faceBaseConst (γ_min C : ℝ) (k : ℕ) : ℕ :=
  256 * 32 * (k + 1) * 2 ^ k + ⌈γ_min⌉₊ + ⌈Real.exp ((32 * (k : ℝ) + 40) / C)⌉₊ + 10

theorem ten_le_faceBaseConst (γ_min C : ℝ) (k : ℕ) : 10 ≤ faceBaseConst γ_min C k := by
  unfold faceBaseConst; omega

/-- Positivity floor `2 r₀(Γ, x) / 64^{m₀(Γ, k)}` of `levelMain` on `[T − R_k, T + R_k]`. -/
def faceFloorVal (Γ k : ℕ) (x : ℝ) : ℝ :=
  2 * (levelMinWeight Γ x / levelCoeffBound Γ k)

/-- Integer threshold for `T_k` above which the phase-split perturbation error is at most half the
ideal cosine polynomial floor. -/
def faceErrThresh (Γ k : ℕ) (x : ℝ) : ℕ :=
  ⌈((levelStart Γ k + 1 : ℕ) : ℝ) * (80 * (levelRadius k + 8)) *
    levelCoeffBound Γ k / levelMinWeight Γ x⌉₊

/-- Pair recursion `(T_k, Γ_k)` for parameters `(γ_min, C, Θ)`. At step `k + 1`, `Γ_{k+1}` is
chosen from the previous right window endpoint `U_k = T_k + k + 1`, and the new window center
`T_{k+1}` is then chosen from `Γ_{k+1}`. -/
def faceTowerPair (γ_min C Θ : ℝ) : ℕ → ℕ × ℕ
  | 0 =>
      let Γ₀ := faceBaseConst γ_min C 0
      let T₀ := max 105 (faceErrThresh Γ₀ 0 (SplineTower.depth Θ 0))
      (T₀, Γ₀)
  | k + 1 =>
      let prev := faceTowerPair γ_min C Θ k
      let T_k := prev.1
      let Γ_k := prev.2
      let U_k := T_k + k + 1
      let Γ_next :=
        max (2 * Γ_k + 4)
          (faceBaseConst γ_min C (k + 1) * ⌈Real.exp ((Θ / 7) * (U_k : ℝ))⌉₊)
      let x_next := SplineTower.depth Θ (k + 1)
      let L_next := faceFloorVal Γ_next (k + 1) x_next
      let Δ := x_next - SplineTower.depth Θ k
      let T_next :=
        max (max (U_k + k + 10) (104 * (k + 2) + 1))
          (max (faceErrThresh Γ_next (k + 1) x_next)
            (max ((k + 2) + ⌈Real.log (((k : ℝ) + 10) / L_next + 1) / Δ⌉₊)
              ⌈Real.exp (((k + 2 : ℕ) : ℝ) ^ 2)⌉₊))
      (T_next, Γ_next)

/-- Window center `T_k` at level `k`. -/
def winCenter (γ_min C Θ : ℝ) (k : ℕ) : ℕ := (faceTowerPair γ_min C Θ k).1

/-- Base ordinate `Γ_k` at level `k`. -/
def faceBaseFreq (γ_min C Θ : ℝ) (k : ℕ) : ℕ := (faceTowerPair γ_min C Θ k).2

/-- Right endpoint `U_k = T_k + k + 1` of the `k`-th window `[T_k − (k + 1), T_k + (k + 1)]`. -/
def winRight (γ_min C Θ : ℝ) (k : ℕ) : ℕ := winCenter γ_min C Θ k + k + 1

/-- Level weight bound `levelWeightBound Γ_k k`. -/
def faceLevelWeight (γ_min C Θ : ℝ) (k : ℕ) : ℝ :=
  levelWeightBound (faceBaseFreq γ_min C Θ k) k

@[simp] theorem faceBaseFreq_zero (γ_min C Θ : ℝ) :
    faceBaseFreq γ_min C Θ 0 = faceBaseConst γ_min C 0 := rfl

theorem faceBaseFreq_succ (γ_min C Θ : ℝ) (k : ℕ) :
    faceBaseFreq γ_min C Θ (k + 1) =
      max (2 * faceBaseFreq γ_min C Θ k + 4)
        (faceBaseConst γ_min C (k + 1) *
          ⌈Real.exp ((Θ / 7) * (winRight γ_min C Θ k : ℝ))⌉₊) := rfl

theorem winRight_cast (γ_min C Θ : ℝ) (k : ℕ) :
    (winRight γ_min C Θ k : ℝ) = (winCenter γ_min C Θ k : ℝ) + levelRadius k := by
  unfold winRight levelRadius
  push_cast
  ring

theorem winCenter_succ_ge_winRight (γ_min C Θ : ℝ) (k : ℕ) :
    winRight γ_min C Θ k + k + 10 ≤ winCenter γ_min C Θ (k + 1) := by
  dsimp only [winCenter, winRight, faceTowerPair]
  exact (le_max_left _ _).trans (le_max_left _ _)

theorem winCenter_add_four_le_succ (γ_min C Θ : ℝ) (k : ℕ) :
    winCenter γ_min C Θ k + 4 ≤ winCenter γ_min C Θ (k + 1) := by
  have := winCenter_succ_ge_winRight γ_min C Θ k
  unfold winRight at this
  omega

theorem strictMono_winCenter (γ_min C Θ : ℝ) : StrictMono (winCenter γ_min C Θ) :=
  strictMono_nat_of_lt_succ fun k => by have := winCenter_add_four_le_succ γ_min C Θ k; omega

theorem strictMono_winRight (γ_min C Θ : ℝ) : StrictMono (winRight γ_min C Θ) :=
  strictMono_nat_of_lt_succ fun k => by
    have := winCenter_succ_ge_winRight γ_min C Θ k
    unfold winRight at *
    omega

theorem monotone_winRight_cast (γ_min C Θ : ℝ) :
    Monotone (fun k => (winRight γ_min C Θ k : ℝ)) :=
  fun _ _ hab => Nat.cast_le.mpr ((strictMono_winRight γ_min C Θ).monotone hab)

theorem k_le_winCenter (γ_min C Θ : ℝ) (k : ℕ) : k ≤ winCenter γ_min C Θ k :=
  (strictMono_winCenter γ_min C Θ).id_le k

theorem step_bound_winCenter (γ_min C Θ : ℝ) (k : ℕ) :
    104 * (k + 1) + 1 ≤ winCenter γ_min C Θ k := by
  rcases k with _ | k
  · dsimp only [winCenter, faceTowerPair]
    exact le_max_left _ _
  · dsimp only [winCenter, faceTowerPair]
    exact (le_max_right _ _).trans (le_max_left _ _)

theorem winCenter_pos (γ_min C Θ : ℝ) (k : ℕ) : 0 < (winCenter γ_min C Θ k : ℝ) := by
  have := step_bound_winCenter γ_min C Θ k
  have h1 : 1 ≤ winCenter γ_min C Θ k := by omega
  exact_mod_cast h1

theorem two_six_div_winCenter_lt_levelStep (γ_min C Θ : ℝ) (k : ℕ) :
    26 / (winCenter γ_min C Θ k : ℝ) < levelStep k := by
  have hT := winCenter_pos γ_min C Θ k
  have hstep := step_bound_winCenter γ_min C Θ k
  have hTR : 104 * ((k : ℝ) + 1) + 1 ≤ (winCenter γ_min C Θ k : ℝ) := by exact_mod_cast hstep
  unfold levelStep levelRadius
  rw [div_lt_div_iff₀ hT (by positivity)]
  linarith

theorem two_six_div_winCenter_le_one (γ_min C Θ : ℝ) (k : ℕ) :
    26 / (winCenter γ_min C Θ k : ℝ) ≤ 1 := by
  refine (two_six_div_winCenter_lt_levelStep γ_min C Θ k).le.trans ?_
  unfold levelStep levelRadius
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem faceErrThresh_le_winCenter (γ_min C Θ : ℝ) (k : ℕ) :
    faceErrThresh (faceBaseFreq γ_min C Θ k) k (SplineTower.depth Θ k) ≤
      winCenter γ_min C Θ k := by
  rcases k with _ | k
  · dsimp only [winCenter, faceBaseFreq, faceTowerPair]
    exact le_max_right _ _
  · dsimp only [winCenter, faceBaseFreq, faceTowerPair]
    exact (le_max_left _ _).trans (le_max_right _ _)

theorem err_bound_winCenter (γ_min C Θ : ℝ) (k : ℕ) :
    ((levelStart (faceBaseFreq γ_min C Θ k) k + 1 : ℕ) : ℝ) * (80 * (levelRadius k + 8)) *
        levelCoeffBound (faceBaseFreq γ_min C Θ k) k /
        levelMinWeight (faceBaseFreq γ_min C Θ k) (SplineTower.depth Θ k) ≤
      (winCenter γ_min C Θ k : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast faceErrThresh_le_winCenter γ_min C Θ k)

theorem one_le_ceil_exp_face (γ_min C Θ : ℝ) (k : ℕ) :
    1 ≤ ⌈Real.exp ((Θ / 7) * (winRight γ_min C Θ k : ℝ))⌉₊ :=
  Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (Real.exp_pos _)).ne'

theorem faceBaseConst_le_faceBaseFreq (γ_min C Θ : ℝ) (k : ℕ) :
    faceBaseConst γ_min C k ≤ faceBaseFreq γ_min C Θ k := by
  rcases k with _ | k
  · exact le_rfl
  · rw [faceBaseFreq_succ]
    exact (Nat.le_mul_of_pos_right _ (one_le_ceil_exp_face γ_min C Θ k)).trans (le_max_right _ _)

theorem ten_le_faceBaseFreq (γ_min C Θ : ℝ) (k : ℕ) :
    10 ≤ faceBaseFreq γ_min C Θ k :=
  (ten_le_faceBaseConst γ_min C k).trans (faceBaseConst_le_faceBaseFreq γ_min C Θ k)

theorem four_le_faceBaseFreq (γ_min C Θ : ℝ) (k : ℕ) :
    4 ≤ faceBaseFreq γ_min C Θ k := by
  have := ten_le_faceBaseFreq γ_min C Θ k; omega

theorem one_le_faceBaseFreq (γ_min C Θ : ℝ) (k : ℕ) :
    1 ≤ faceBaseFreq γ_min C Θ k := by
  have := ten_le_faceBaseFreq γ_min C Θ k; omega

theorem k_le_faceBaseFreq (γ_min C Θ : ℝ) (k : ℕ) :
    k ≤ faceBaseFreq γ_min C Θ k := by
  have h1 : k ≤ faceBaseConst γ_min C k := by
    unfold faceBaseConst
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    nlinarith
  exact h1.trans (faceBaseConst_le_faceBaseFreq γ_min C Θ k)

theorem gamma_min_le_faceBaseFreq (γ_min C Θ : ℝ) (k : ℕ) :
    γ_min ≤ (faceBaseFreq γ_min C Θ k : ℝ) := by
  have h1 : ⌈γ_min⌉₊ ≤ faceBaseConst γ_min C k := by unfold faceBaseConst; omega
  exact (Nat.le_ceil _).trans (by exact_mod_cast h1.trans (faceBaseConst_le_faceBaseFreq γ_min C Θ k))

theorem exp_count_le_faceBaseFreq (γ_min C Θ : ℝ) (k : ℕ) :
    Real.exp ((32 * (k : ℝ) + 40) / C) ≤ (faceBaseFreq γ_min C Θ k : ℝ) := by
  have h1 : ⌈Real.exp ((32 * (k : ℝ) + 40) / C)⌉₊ ≤ faceBaseConst γ_min C k := by
    unfold faceBaseConst; omega
  exact (Nat.le_ceil _).trans (by exact_mod_cast h1.trans (faceBaseConst_le_faceBaseFreq γ_min C Θ k))

theorem two_mul_faceBaseFreq_add_four_le_succ (γ_min C Θ : ℝ) (k : ℕ) :
    2 * faceBaseFreq γ_min C Θ k + 4 ≤ faceBaseFreq γ_min C Θ (k + 1) := by
  rw [faceBaseFreq_succ]
  exact le_max_left _ _

theorem two_mul_faceBaseFreq_add_four_le_of_lt (γ_min C Θ : ℝ) {k₁ k₂ : ℕ} (h : k₁ < k₂) :
    2 * faceBaseFreq γ_min C Θ k₁ + 4 ≤ faceBaseFreq γ_min C Θ k₂ := by
  induction k₂ with
  | zero => omega
  | succ m ih =>
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ h) with rfl | hlt
    · exact two_mul_faceBaseFreq_add_four_le_succ γ_min C Θ k₁
    · have h1 := ih hlt
      have h2 := two_mul_faceBaseFreq_add_four_le_succ γ_min C Θ m
      omega

theorem levelWeightBound_le_div_pow_seven {Γ : ℕ} (hΓ : 1 ≤ Γ) (k : ℕ) :
    levelWeightBound Γ k ≤ (256 * 32 * ((k + 1 : ℕ) : ℝ)) / (Γ : ℝ) ^ 7 := by
  unfold levelWeightBound levelStart
  have hΓR : (1 : ℝ) ≤ (Γ : ℝ) := by exact_mod_cast hΓ
  have hΓpos : 0 < (Γ : ℝ) := by positivity
  have hm₀ : 1 ≤ 4 * (k + 1) * Γ := by nlinarith
  have hnum_nat : 4 * (4 * (k + 1) * Γ + 1) ≤ 32 * (k + 1) * Γ := by nlinarith
  have hnum : 4 * ((4 * (k + 1) * Γ + 1 : ℕ) : ℝ) ≤ 32 * ((k + 1 : ℕ) : ℝ) * (Γ : ℝ) := by
    exact_mod_cast hnum_nat
  calc 4 * ((4 * (k + 1) * Γ + 1 : ℕ) : ℝ) * (2 / (Γ : ℝ)) ^ 8
      ≤ (32 * ((k + 1 : ℕ) : ℝ) * (Γ : ℝ)) * (2 / (Γ : ℝ)) ^ 8 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = (256 * 32 * ((k + 1 : ℕ) : ℝ)) / (Γ : ℝ) ^ 7 := by
        rw [div_pow, show (2 : ℝ) ^ 8 = 256 by norm_num, show (8 : ℕ) = 7 + 1 by rfl, pow_succ]
        field_simp [hΓpos.ne']

theorem faceLevelWeight_nonneg (γ_min C Θ : ℝ) (k : ℕ) :
    0 ≤ faceLevelWeight γ_min C Θ k :=
  (levelWeightBound_pos (one_le_faceBaseFreq γ_min C Θ k) k).le

theorem faceLevelWeight_zero_le_one (γ_min C Θ : ℝ) :
    faceLevelWeight γ_min C Θ 0 ≤ 1 := by
  unfold faceLevelWeight
  have hΓ1 := one_le_faceBaseFreq γ_min C Θ 0
  refine (levelWeightBound_le_div_pow_seven hΓ1 0).trans ?_
  have hC : 256 * 32 ≤ faceBaseFreq γ_min C Θ 0 := by
    rw [faceBaseFreq_zero]
    unfold faceBaseConst
    omega
  have hCR : (256 * 32 : ℝ) ≤ (faceBaseFreq γ_min C Θ 0 : ℝ) := by exact_mod_cast hC
  have hΓR : (1 : ℝ) ≤ (faceBaseFreq γ_min C Θ 0 : ℝ) := by exact_mod_cast hΓ1
  have hpow : (faceBaseFreq γ_min C Θ 0 : ℝ) ≤ (faceBaseFreq γ_min C Θ 0 : ℝ) ^ 7 :=
    le_self_pow₀ hΓR (by omega)
  rw [div_le_one (by positivity)]
  push_cast
  linarith

theorem faceLevelWeight_succ_le (γ_min C Θ : ℝ) (j : ℕ) :
    faceLevelWeight γ_min C Θ (j + 1) ≤
      (1 / 2) ^ (j + 1) * Real.exp (-(Θ * (winRight γ_min C Θ j : ℝ))) := by
  unfold faceLevelWeight
  have hΓ1 := one_le_faceBaseFreq γ_min C Θ (j + 1)
  refine (levelWeightBound_le_div_pow_seven hΓ1 (j + 1)).trans ?_
  have hΓ_ge : faceBaseConst γ_min C (j + 1) *
      ⌈Real.exp ((Θ / 7) * (winRight γ_min C Θ j : ℝ))⌉₊ ≤
      faceBaseFreq γ_min C Θ (j + 1) := by
    rw [faceBaseFreq_succ]
    exact le_max_right _ _
  have hC_ge : 256 * 32 * (j + 1 + 1) * 2 ^ (j + 1) ≤ faceBaseConst γ_min C (j + 1) := by
    unfold faceBaseConst; omega
  have hC1 : (1 : ℝ) ≤ (faceBaseConst γ_min C (j + 1) : ℝ) := by
    exact_mod_cast (by have := ten_le_faceBaseConst γ_min C (j + 1); omega :
      1 ≤ faceBaseConst γ_min C (j + 1))
  have hCpow : (256 * 32 * ((j + 1 + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (j + 1) ≤
      (faceBaseConst γ_min C (j + 1) : ℝ) ^ 7 := by
    have hCR : (256 * 32 * ((j + 1 + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (j + 1) ≤
        (faceBaseConst γ_min C (j + 1) : ℝ) := by exact_mod_cast hC_ge
    exact hCR.trans (le_self_pow₀ hC1 (by omega))
  have hexp_le : Real.exp ((Θ / 7) * (winRight γ_min C Θ j : ℝ)) ≤
      (⌈Real.exp ((Θ / 7) * (winRight γ_min C Θ j : ℝ))⌉₊ : ℝ) := Nat.le_ceil _
  have hexp7 : Real.exp (Θ * (winRight γ_min C Θ j : ℝ)) ≤
      (⌈Real.exp ((Θ / 7) * (winRight γ_min C Θ j : ℝ))⌉₊ : ℝ) ^ 7 := by
    calc Real.exp (Θ * (winRight γ_min C Θ j : ℝ))
        = (Real.exp ((Θ / 7) * (winRight γ_min C Θ j : ℝ))) ^ 7 := by
            rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ (⌈Real.exp ((Θ / 7) * (winRight γ_min C Θ j : ℝ))⌉₊ : ℝ) ^ 7 :=
            pow_le_pow_left₀ (Real.exp_pos _).le hexp_le 7
  have hΓ_pow : (faceBaseConst γ_min C (j + 1) : ℝ) ^ 7 *
      (⌈Real.exp ((Θ / 7) * (winRight γ_min C Θ j : ℝ))⌉₊ : ℝ) ^ 7 ≤
      (faceBaseFreq γ_min C Θ (j + 1) : ℝ) ^ 7 := by
    rw [← mul_pow, ← Nat.cast_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hΓ_ge) 7
  have hden_pos : 0 < (faceBaseFreq γ_min C Θ (j + 1) : ℝ) ^ 7 := by
    have : (1 : ℝ) ≤ (faceBaseFreq γ_min C Θ (j + 1) : ℝ) := by exact_mod_cast hΓ1
    positivity
  rw [div_le_iff₀ hden_pos]
  have hprod : ((256 * 32 * ((j + 1 + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (j + 1)) *
      Real.exp (Θ * (winRight γ_min C Θ j : ℝ)) ≤
      (faceBaseFreq γ_min C Θ (j + 1) : ℝ) ^ 7 :=
    (mul_le_mul hCpow hexp7 (Real.exp_pos _).le (by positivity)).trans hΓ_pow
  have hmul := mul_le_mul_of_nonneg_left hprod
    (show (0 : ℝ) ≤ (1 / 2) ^ (j + 1) * Real.exp (-(Θ * (winRight γ_min C Θ j : ℝ))) by positivity)
  have hid : ((1 / 2 : ℝ) ^ (j + 1) * Real.exp (-(Θ * (winRight γ_min C Θ j : ℝ)))) *
      (((256 * 32 * ((j + 1 + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (j + 1)) *
        Real.exp (Θ * (winRight γ_min C Θ j : ℝ))) =
      256 * 32 * ((j + 1 + 1 : ℕ) : ℝ) := by
    have hpow2 : (1 / 2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (j + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hexp0 : Real.exp (-(Θ * (winRight γ_min C Θ j : ℝ))) *
        Real.exp (Θ * (winRight γ_min C Θ j : ℝ)) = 1 := by
      rw [← Real.exp_add]; simp
    calc ((1 / 2 : ℝ) ^ (j + 1) * Real.exp (-(Θ * (winRight γ_min C Θ j : ℝ)))) *
          (((256 * 32 * ((j + 1 + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (j + 1)) *
            Real.exp (Θ * (winRight γ_min C Θ j : ℝ)))
        = (256 * 32 * ((j + 1 + 1 : ℕ) : ℝ)) *
            ((1 / 2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (j + 1)) *
            (Real.exp (-(Θ * (winRight γ_min C Θ j : ℝ))) *
              Real.exp (Θ * (winRight γ_min C Θ j : ℝ))) := by ring
      _ = 256 * 32 * ((j + 1 + 1 : ℕ) : ℝ) := by rw [hpow2, hexp0]; ring
  linarith

theorem exp_mul_faceFloorVal_ge (γ_min C : ℝ) {Θ : ℝ} (hΘ : 0 < Θ) (k : ℕ) :
    (k : ℝ) + 10 ≤
      Real.exp ((SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k) *
          ((winCenter γ_min C Θ (k + 1) : ℝ) - levelRadius (k + 1))) *
        faceFloorVal (faceBaseFreq γ_min C Θ (k + 1)) (k + 1) (SplineTower.depth Θ (k + 1)) := by
  set Γ := faceBaseFreq γ_min C Θ (k + 1)
  set x := SplineTower.depth Θ (k + 1)
  set L := faceFloorVal Γ (k + 1) x
  set Δ := x - SplineTower.depth Θ k
  have hL_pos : 0 < L := by
    unfold L faceFloorVal levelMinWeight levelCoeffBound
    have hx_pos : 0 < x := SplineTower.depth_pos hΘ (k + 1)
    have hΓ_pos : (0 : ℝ) < (Γ : ℝ) := by exact_mod_cast one_le_faceBaseFreq γ_min C Θ (k + 1)
    positivity
  have hΔ_pos : 0 < Δ := sub_pos.mpr (SplineTower.strictMono_depth hΘ (Nat.lt_succ_self k))
  have hT_ge : (k + 2) + ⌈Real.log (((k : ℝ) + 10) / L + 1) / Δ⌉₊ ≤
      winCenter γ_min C Θ (k + 1) := by
    dsimp only [winCenter, faceTowerPair, Γ, x, L, Δ]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hTR : ((k + 2 : ℕ) : ℝ) + (⌈Real.log (((k : ℝ) + 10) / L + 1) / Δ⌉₊ : ℝ) ≤
      (winCenter γ_min C Θ (k + 1) : ℝ) := by exact_mod_cast hT_ge
  have hrad : ((k + 2 : ℕ) : ℝ) = levelRadius (k + 1) := by
    unfold levelRadius; push_cast; ring
  have hdiff : Real.log (((k : ℝ) + 10) / L + 1) / Δ ≤
      (winCenter γ_min C Θ (k + 1) : ℝ) - levelRadius (k + 1) := by
    have hc := Nat.le_ceil (Real.log (((k : ℝ) + 10) / L + 1) / Δ)
    linarith
  have hlog : Real.log (((k : ℝ) + 10) / L + 1) ≤
      Δ * ((winCenter γ_min C Θ (k + 1) : ℝ) - levelRadius (k + 1)) := by
    rw [div_le_iff₀ hΔ_pos] at hdiff
    linarith
  have hexp : ((k : ℝ) + 10) / L + 1 ≤
      Real.exp (Δ * ((winCenter γ_min C Θ (k + 1) : ℝ) - levelRadius (k + 1))) := by
    rw [← Real.exp_log (by positivity : 0 < ((k : ℝ) + 10) / L + 1)]
    exact Real.exp_le_exp.mpr hlog
  have hmul := mul_le_mul_of_nonneg_right hexp hL_pos.le
  rw [add_mul, div_mul_cancel₀ _ hL_pos.ne'] at hmul
  linarith

theorem exp_levelRadius_sq_le_winCenter (γ_min C Θ : ℝ) (k : ℕ) :
    Real.exp (levelRadius (k + 1) ^ 2) ≤ (winCenter γ_min C Θ (k + 1) : ℝ) := by
  have hT_ge : ⌈Real.exp (((k + 2 : ℕ) : ℝ) ^ 2)⌉₊ ≤ winCenter γ_min C Θ (k + 1) := by
    dsimp only [winCenter, faceTowerPair]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hrad : ((k + 2 : ℕ) : ℝ) = levelRadius (k + 1) := by
    unfold levelRadius; push_cast; ring
  rw [← hrad]
  exact (Nat.le_ceil _).trans (by exact_mod_cast hT_ge)

/-! ### The phase-split simple-zero configuration in `𝒵(γ_min, C)` -/

/-- Harmonic index finset `[m₀(Γ_k, k), 2 m₀(Γ_k, k)]` at level `k`. -/
def faceHarmonics (γ_min C Θ : ℝ) (k : ℕ) : Finset ℕ :=
  Finset.Icc (levelStart (faceBaseFreq γ_min C Θ k) k)
    (2 * levelStart (faceBaseFreq γ_min C Θ k) k)

/-- Index type for all zeros across levels `k`, harmonics `d`, pair members `b`, and reflection
sides `s`. -/
abbrev FaceIdx (γ_min C Θ : ℝ) : Type :=
  Σ k : ℕ, ↥(faceHarmonics γ_min C Θ k) × Bool × Bool

/-- Perturbed ordinate `γ_{k, d}^b` at level `k`. -/
def facePtFreq (γ_min C Θ : ℝ) (k : ℕ) (b : Bool) (d : ℕ) : ℝ :=
  levelFreq (faceBaseFreq γ_min C Θ k) k (SplineTower.depth Θ k)
    (winCenter γ_min C Θ k : ℝ) b d

/-- Zero location `½ ± x_k + i γ_{k, d}^b` associated with `⟨k, (d, b, s)⟩`. -/
def facePt (γ_min C Θ : ℝ) : FaceIdx γ_min C Θ → ℂ
  | ⟨k, (d, b, true)⟩ =>
      (1 / 2 : ℂ) + (SplineTower.depth Θ k : ℂ) + (facePtFreq γ_min C Θ k b d.1 : ℂ) * I
  | ⟨k, (d, b, false)⟩ =>
      (1 / 2 : ℂ) - (SplineTower.depth Θ k : ℂ) + (facePtFreq γ_min C Θ k b d.1 : ℂ) * I

theorem facePt_true_re (γ_min C Θ : ℝ) (k : ℕ) (d : ↥(faceHarmonics γ_min C Θ k)) (b : Bool) :
    (facePt γ_min C Θ ⟨k, (d, b, true)⟩).re = 1 / 2 + SplineTower.depth Θ k := by
  simp [facePt]

theorem facePt_false_re (γ_min C Θ : ℝ) (k : ℕ) (d : ↥(faceHarmonics γ_min C Θ k)) (b : Bool) :
    (facePt γ_min C Θ ⟨k, (d, b, false)⟩).re = 1 / 2 - SplineTower.depth Θ k := by
  simp [facePt]

theorem facePt_im (γ_min C Θ : ℝ) (idx : FaceIdx γ_min C Θ) :
    (facePt γ_min C Θ idx).im =
      facePtFreq γ_min C Θ idx.1 idx.2.2.1 idx.2.1.1 := by
  rcases idx with ⟨k, ⟨d, b, _ | _⟩⟩ <;> simp [facePt]

theorem facePt_im_bounds (γ_min C Θ : ℝ) (idx : FaceIdx γ_min C Θ) :
    (faceBaseFreq γ_min C Θ idx.1 : ℝ) < (facePt γ_min C Θ idx).im ∧
      (facePt γ_min C Θ idx).im ≤ 2 * (faceBaseFreq γ_min C Θ idx.1 : ℝ) + 1 := by
  rw [facePt_im]
  exact levelFreq_bounds (SplineTower.depth Θ idx.1) (winCenter_pos γ_min C Θ idx.1)
    (two_six_div_winCenter_le_one γ_min C Θ idx.1) idx.2.2.1 idx.2.1.2

theorem facePt_injective (γ_min C : ℝ) {Θ : ℝ} (hΘ : 0 < Θ) :
    Function.Injective (facePt γ_min C Θ) := by
  rintro ⟨k, ⟨d, b, s⟩⟩ ⟨k', ⟨d', b', s'⟩⟩ h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  have hd := (SplineTower.strictMono_depth hΘ).injective
  have h0 := SplineTower.depth_pos hΘ k
  have h0' := SplineTower.depth_pos hΘ k'
  have hk_eq : k = k' ∧ s = s' := by
    cases s <;> cases s'
    · rw [facePt_false_re, facePt_false_re] at hre
      exact ⟨hd (by linarith), rfl⟩
    · rw [facePt_false_re, facePt_true_re] at hre; linarith
    · rw [facePt_true_re, facePt_false_re] at hre; linarith
    · rw [facePt_true_re, facePt_true_re] at hre
      exact ⟨hd (by linarith), rfl⟩
  rcases hk_eq with ⟨rfl, rfl⟩
  rw [facePt_im, facePt_im] at him
  have hbd := levelFreq_injective (faceBaseFreq γ_min C Θ k) k (SplineTower.depth Θ k)
    (winCenter_pos γ_min C Θ k) (two_six_div_winCenter_lt_levelStep γ_min C Θ k) him
  rcases hbd with ⟨rfl, hd_eq⟩
  have hsub : d = d' := Subtype.ext hd_eq
  subst hsub
  rfl

theorem reflect_facePt (γ_min C Θ : ℝ) (k : ℕ) (d : ↥(faceHarmonics γ_min C Θ k))
    (b s : Bool) :
    reflect (facePt γ_min C Θ ⟨k, (d, b, s)⟩) = facePt γ_min C Θ ⟨k, (d, b, !s)⟩ := by
  apply Complex.ext <;> cases s <;> simp [reflect, facePt] <;> ring

/-- **The minimal-face counterexample configuration `Z ∈ 𝒵(γ_min, C)`.** All zeros have
multiplicity `1`, ordinates `≥ γ_min > 0`, local counts `N(t, t + 1) ≤ C log(|t| + 3)`, and
unattained accumulating top `sup Re ρ = 1/2 + Θ`. -/
def minimalFaceCounterConfig (γ_min C : ℝ) {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ZeroConfig where
  carrier := Set.range (facePt γ_min C Θ)
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro ρ ⟨⟨k, ⟨d, b, s⟩⟩, rfl⟩
    have h0 := SplineTower.depth_nonneg hΘ k
    have h1 := (SplineTower.depth_lt hΘ k).le
    cases s
    · rw [facePt_false_re]; constructor <;> linarith
    · rw [facePt_true_re]; constructor <;> linarith
  reflect_mem := by
    rintro ρ ⟨⟨k, ⟨d, b, s⟩⟩, rfl⟩
    exact ⟨⟨k, (d, b, !s)⟩, (reflect_facePt γ_min C Θ k d b s).symm⟩
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    let S : Set (FaceIdx γ_min C Θ) :=
      {idx : FaceIdx γ_min C Θ | idx.1 ≤ ⌊T₂⌋₊}
    have hSfin : S.Finite := by
      refine ((Set.finite_univ (α := ↥(Finset.Iic ⌊T₂⌋₊))).biUnion
        fun k _ => (Set.finite_univ (α := ↥(faceHarmonics γ_min C Θ k.1) × Bool × Bool)).image
          (fun dbs => (⟨k.1, dbs⟩ : FaceIdx γ_min C Θ))).subset ?_
      intro idx hidx
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and]
      exact ⟨⟨idx.1, Finset.mem_Iic.mpr hidx⟩, trivial, idx.2, rfl⟩
    refine (hSfin.image (facePt γ_min C Θ)).subset ?_
    rintro ρ ⟨⟨idx, rfl⟩, -, hT⟩
    refine ⟨idx, ?_, rfl⟩
    have him := (facePt_im_bounds γ_min C Θ idx).1
    have hk := k_le_faceBaseFreq γ_min C Θ idx.1
    have hkR : (idx.1 : ℝ) ≤ (faceBaseFreq γ_min C Θ idx.1 : ℝ) := by exact_mod_cast hk
    exact Nat.le_floor (by linarith)

theorem gammaOf_facePt_true (γ_min C Θ : ℝ) (k : ℕ) (d : ↥(faceHarmonics γ_min C Θ k))
    (b : Bool) :
    gammaOf (facePt γ_min C Θ ⟨k, (d, b, true)⟩) =
      generalSplinePoint (facePtFreq γ_min C Θ k b d.1) (SplineTower.depth Θ k) := by
  apply Complex.ext <;> simp [gammaOf, facePt, generalSplinePoint, Complex.div_I]

theorem gammaOf_facePt_false (γ_min C Θ : ℝ) (k : ℕ) (d : ↥(faceHarmonics γ_min C Θ k))
    (b : Bool) :
    gammaOf (facePt γ_min C Θ ⟨k, (d, b, false)⟩) =
      conj (generalSplinePoint (facePtFreq γ_min C Θ k b d.1) (SplineTower.depth Θ k)) := by
  apply Complex.ext <;> simp [gammaOf, facePt, generalSplinePoint, Complex.div_I]

theorem I_mul_generalSplinePoint (γ x u : ℝ) :
    I * generalSplinePoint γ x * (u : ℂ) =
      ((x * u : ℝ) : ℂ) + ((γ * u : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [generalSplinePoint]

theorem I_mul_conj_generalSplinePoint (γ x u : ℝ) :
    I * conj (generalSplinePoint γ x) * (u : ℂ) =
      ((-(x * u) : ℝ) : ℂ) + ((γ * u : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [generalSplinePoint]

theorem normSq_gammaOf_facePt_ge (γ_min C Θ : ℝ) (idx : FaceIdx γ_min C Θ) :
    (faceBaseFreq γ_min C Θ idx.1 : ℝ) ^ 2 ≤ Complex.normSq (gammaOf (facePt γ_min C Θ idx)) := by
  have hre : (gammaOf (facePt γ_min C Θ idx)).re = (facePt γ_min C Θ idx).im := by
    rcases idx with ⟨k, ⟨d, b, _ | _⟩⟩
    · rw [gammaOf_facePt_false, Complex.conj_re, generalSplinePoint_re, facePt_im]
    · rw [gammaOf_facePt_true, generalSplinePoint_re, facePt_im]
  rw [Complex.normSq_apply, hre]
  have him := (facePt_im_bounds γ_min C Θ idx).1.le
  have h0 : (0 : ℝ) ≤ (faceBaseFreq γ_min C Θ idx.1 : ℝ) := Nat.cast_nonneg _
  have h2 := mul_le_mul him him h0 (h0.trans him)
  nlinarith [mul_self_nonneg (gammaOf (facePt γ_min C Θ idx)).im]

/-- **The minimal-face counterexample configuration is tempered.** -/
theorem temperedConfig_minimalFaceCounterConfig (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    TemperedConfig (minimalFaceCounterConfig γ_min C hΘ hΘ2) := by
  unfold TemperedConfig
  set e := Equiv.ofInjective (facePt γ_min C Θ) (facePt_injective γ_min C hΘ)
  show Summable fun ρ : Set.range (facePt γ_min C Θ) =>
    ((1 : ℕ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
  refine (e.summable_iff).mp ?_
  set F : FaceIdx γ_min C Θ → ℝ := fun idx =>
    1 / (1 + Complex.normSq (gammaOf (facePt γ_min C Θ idx)))
  have hcomp : ((fun ρ : Set.range (facePt γ_min C Θ) =>
      ((1 : ℕ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))) ∘ e) = F := by
    ext idx
    simp [e, F]
  rw [hcomp]
  have hF0 : ∀ idx, 0 ≤ F idx := fun idx =>
    div_nonneg zero_le_one (by linarith [Complex.normSq_nonneg (gammaOf (facePt γ_min C Θ idx))])
  rw [summable_sigma_of_nonneg hF0]
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun _ => hF0 _) (fun k => ?_)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [tsum_fintype]
  set Γ := faceBaseFreq γ_min C Θ k
  have hΓ1 : 1 ≤ Γ := one_le_faceBaseFreq γ_min C Θ k
  have hΓR : (1 : ℝ) ≤ (Γ : ℝ) := by exact_mod_cast hΓ1
  have hterm : ∀ dbs : ↥(faceHarmonics γ_min C Θ k) × Bool × Bool,
      F ⟨k, dbs⟩ ≤ 1 / (Γ : ℝ) ^ 2 := by
    intro dbs
    dsimp only [F]
    have hns := normSq_gammaOf_facePt_ge γ_min C Θ ⟨k, dbs⟩
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
  have hcard : (Fintype.card (↥(faceHarmonics γ_min C Θ k) × Bool × Bool) : ℝ) ≤
      32 * ((k + 1 : ℕ) : ℝ) * (Γ : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, Fintype.card_bool]
    unfold faceHarmonics levelStart
    rw [Nat.card_Icc, show 2 * (4 * (k + 1) * Γ) + 1 - 4 * (k + 1) * Γ =
      4 * (k + 1) * Γ + 1 by omega]
    have hm₀ : 1 ≤ 4 * (k + 1) * Γ := by nlinarith
    have hnat : (4 * (k + 1) * Γ + 1) * (2 * 2) ≤ 32 * (k + 1) * Γ := by nlinarith
    exact_mod_cast hnat
  calc (∑ dbs : ↥(faceHarmonics γ_min C Θ k) × Bool × Bool, F ⟨k, dbs⟩)
      ≤ ∑ _dbs : ↥(faceHarmonics γ_min C Θ k) × Bool × Bool, (1 / (Γ : ℝ) ^ 2) :=
        Finset.sum_le_sum fun dbs _ => hterm dbs
    _ = (Fintype.card (↥(faceHarmonics γ_min C Θ k) × Bool × Bool) : ℝ) * (1 / (Γ : ℝ) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (32 * ((k + 1 : ℕ) : ℝ) * (Γ : ℝ)) * (1 / (Γ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 32 * ((k + 1 : ℕ) : ℝ) / (Γ : ℝ) := by
        rw [sq]; field_simp [(by positivity : (0 : ℝ) < (Γ : ℝ)).ne']
    _ ≤ (1 / 2 : ℝ) ^ k := by
        have hC_ge : 32 * (k + 1) * 2 ^ k ≤ Γ := by
          refine (?_ : 32 * (k + 1) * 2 ^ k ≤ faceBaseConst γ_min C k).trans
            (faceBaseConst_le_faceBaseFreq γ_min C Θ k)
          unfold faceBaseConst
          have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
          nlinarith
        have hCR : 32 * ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k ≤ (Γ : ℝ) := by exact_mod_cast hC_ge
        rw [div_le_iff₀ (by positivity)]
        have hpow2 : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
        have hmul := mul_le_mul_of_nonneg_left hCR (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k by positivity)
        have hid : (1 / 2 : ℝ) ^ k * (32 * ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k) =
            32 * ((k + 1 : ℕ) : ℝ) := by
          calc (1 / 2 : ℝ) ^ k * (32 * ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k)
              = 32 * ((k + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k) := by ring
            _ = 32 * ((k + 1 : ℕ) : ℝ) := by rw [hpow2, mul_one]
        linarith

/-- **Trace expansion of `minimalFaceCounterConfig`.** -/
theorem two_re_lagStructure_minimalFaceCounterConfig (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (u : ℝ) :
    2 * (lagStructure (minimalFaceCounterConfig γ_min C hΘ hΘ2) (boxSpline 1 3) u).re =
      ∑' k,
        (Real.exp (SplineTower.depth Θ k * u) *
            levelMain (faceBaseFreq γ_min C Θ k) k (SplineTower.depth Θ k)
              (winCenter γ_min C Θ k : ℝ) u +
          Real.exp (-(SplineTower.depth Θ k * u)) *
            levelRefl (faceBaseFreq γ_min C Θ k) k (SplineTower.depth Θ k)
              (winCenter γ_min C Θ k : ℝ) u) := by
  set Z := minimalFaceCounterConfig γ_min C hΘ hΘ2
  have hb3 := SplineTower.contDiff_two_boxSpline (o := 3) le_rfl
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hs := summable_lagStructure Z (temperedConfig_minimalFaceCounterConfig γ_min C hΘ hΘ2)
    hb3 hbs u
  set e := Equiv.ofInjective (facePt γ_min C Θ) (facePt_injective γ_min C hΘ)
  set F : FaceIdx γ_min C Θ → ℂ := fun idx =>
    paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf (facePt γ_min C Θ idx)) *
      cexp (I * gammaOf (facePt γ_min C Θ idx) * u) with hF
  have hcomp : ∀ idx,
      ((Z.mult (e idx) : ℂ) *
        paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf (e idx)) *
        cexp (I * gammaOf (e idx) * u)) = F idx := by
    intro idx
    simp [Z, minimalFaceCounterConfig, e, hF]
  have hS : HasSum F (lagStructure Z (boxSpline 1 3) u) := by
    have h1 := (e.hasSum_iff).mpr hs.hasSum
    simp only [Function.comp_def, hcomp] at h1
    exact h1
  set g : ℕ → ℂ := fun k =>
    ∑ d ∈ faceHarmonics γ_min C Θ k,
      ((sincC (generalSplinePoint (facePtFreq γ_min C Θ k false d) (SplineTower.depth Θ k)) ^ 8 *
          (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
          cexp (((facePtFreq γ_min C Θ k false d * u : ℝ) : ℂ) * I) +
        conj (sincC (generalSplinePoint (facePtFreq γ_min C Θ k false d) (SplineTower.depth Θ k)) ^ 8) *
          (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
          cexp (((facePtFreq γ_min C Θ k false d * u : ℝ) : ℂ) * I)) +
      (sincC (generalSplinePoint (facePtFreq γ_min C Θ k true d) (SplineTower.depth Θ k)) ^ 8 *
          (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
          cexp (((facePtFreq γ_min C Θ k true d * u : ℝ) : ℂ) * I) +
        conj (sincC (generalSplinePoint (facePtFreq γ_min C Θ k true d) (SplineTower.depth Θ k)) ^ 8) *
          (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
          cexp (((facePtFreq γ_min C Θ k true d * u : ℝ) : ℂ) * I))) with hg
  have hfib : ∀ k, HasSum (fun dbs : ↥(faceHarmonics γ_min C Θ k) × Bool × Bool => F ⟨k, dbs⟩)
      (g k) := by
    intro k
    have hfintype := hasSum_fintype
      (fun dbs : ↥(faceHarmonics γ_min C Θ k) × Bool × Bool => F ⟨k, dbs⟩)
    convert hfintype using 1
    rw [Fintype.sum_prod_type]
    have hbool : ∀ d : ↥(faceHarmonics γ_min C Θ k),
        (∑ bs : Bool × Bool, F ⟨k, (d, bs)⟩) =
          (sincC (generalSplinePoint (facePtFreq γ_min C Θ k false d.1) (SplineTower.depth Θ k)) ^ 8 *
              (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
              cexp (((facePtFreq γ_min C Θ k false d.1 * u : ℝ) : ℂ) * I) +
            conj (sincC (generalSplinePoint (facePtFreq γ_min C Θ k false d.1) (SplineTower.depth Θ k)) ^ 8) *
              (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
              cexp (((facePtFreq γ_min C Θ k false d.1 * u : ℝ) : ℂ) * I)) +
          (sincC (generalSplinePoint (facePtFreq γ_min C Θ k true d.1) (SplineTower.depth Θ k)) ^ 8 *
              (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
              cexp (((facePtFreq γ_min C Θ k true d.1 * u : ℝ) : ℂ) * I) +
            conj (sincC (generalSplinePoint (facePtFreq γ_min C Θ k true d.1) (SplineTower.depth Θ k)) ^ 8) *
              (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
              cexp (((facePtFreq γ_min C Θ k true d.1 * u : ℝ) : ℂ) * I)) := by
      intro d
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [Fintype.sum_bool, hF, gammaOf_facePt_true, gammaOf_facePt_false,
        SplineTower.paperFT_weilTest_spline (o := 3) le_rfl, show 2 * (3 + 1) = 8 by rfl,
        SplineTower.sincC_conj, map_pow, I_mul_generalSplinePoint,
        I_mul_conj_generalSplinePoint, Complex.exp_add, ← Complex.ofReal_exp]
      ring
    simp_rw [hbool]
    exact (Finset.sum_coe_sort (faceHarmonics γ_min C Θ k) _).symm
  have hG : HasSum g (lagStructure Z (boxSpline 1 3) u) := hS.sigma hfib
  have hre := (Complex.reCLM.hasSum hG).mul_left 2
  simp only [Complex.reCLM_apply] at hre
  rw [← hre.tsum_eq]
  refine tsum_congr fun k => ?_
  rw [hg]
  dsimp only [levelMain, levelRefl, faceHarmonics, facePtFreq]
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hre_pull : ∀ (c : ℂ) (r θ : ℝ),
      (c * (Real.exp r : ℂ) * cexp ((θ : ℂ) * I)).re =
        Real.exp r * (c * cexp ((θ : ℂ) * I)).re := by
    intro c r θ
    rw [show c * (Real.exp r : ℂ) * cexp ((θ : ℂ) * I) =
      (Real.exp r : ℂ) * (c * cexp ((θ : ℂ) * I)) by ring, Complex.re_ofReal_mul]
  rw [Complex.add_re, Complex.add_re, Complex.add_re, hre_pull, hre_pull, hre_pull, hre_pull]
  ring

/-- **Diverging lower bound on windows `[T_{k+1} − R_{k+1}, T_{k+1} + R_{k+1}]`.** At every level
`k + 1`, `2 Re S_Z(u) ≥ k + 1` across the entire window `|u − T_{k+1}| ≤ k + 2`. -/
theorem k_add_one_le_two_re_lagStructure_on_window (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (k : ℕ) {u : ℝ}
    (hu : |u - (winCenter γ_min C Θ (k + 1) : ℝ)| ≤ levelRadius (k + 1)) :
    (k : ℝ) + 1 ≤
      2 * (lagStructure (minimalFaceCounterConfig γ_min C hΘ hΘ2) (boxSpline 1 3) u).re := by
  rw [two_re_lagStructure_minimalFaceCounterConfig]
  have hT_bound := step_bound_winCenter γ_min C Θ (k + 1)
  have hTR : 104 * ((k : ℝ) + 2) + 1 ≤ (winCenter γ_min C Θ (k + 1) : ℝ) := by
    exact_mod_cast hT_bound
  have hrad : levelRadius (k + 1) = (k : ℝ) + 2 := by
    unfold levelRadius; push_cast; ring
  have hu_lo : (winCenter γ_min C Θ (k + 1) : ℝ) - levelRadius (k + 1) ≤ u := by
    linarith [(abs_le.mp hu).1]
  have hu_hi : u ≤ (winRight γ_min C Θ (k + 1) : ℝ) := by
    rw [winRight_cast]
    linarith [(abs_le.mp hu).2]
  have hu0 : 0 ≤ u := by linarith [Nat.cast_nonneg (α := ℝ) k]
  refine tsum_ge_of_top_window hΘ
    (fun j => SplineTower.depth_nonneg hΘ j)
    (fun j => (SplineTower.depth_lt hΘ j).le)
    (SplineTower.strictMono_depth hΘ).monotone
    (faceLevelWeight_nonneg γ_min C Θ)
    (faceLevelWeight_zero_le_one γ_min C Θ)
    (faceLevelWeight_succ_le γ_min C Θ)
    (monotone_winRight_cast γ_min C Θ)
    (Nat.cast_nonneg _)
    (fun j => abs_levelMain_le
      (Nat.le_trans (by decide : 2 ≤ 4) (four_le_faceBaseFreq γ_min C Θ j))
      (SplineTower.depth_nonneg hΘ j) ((SplineTower.depth_lt hΘ j).le.trans hΘ2)
      (winCenter_pos γ_min C Θ j) u)
    (fun j => abs_levelRefl_le
      (Nat.le_trans (by decide : 2 ≤ 4) (four_le_faceBaseFreq γ_min C Θ j))
      (SplineTower.depth_nonneg hΘ j) ((SplineTower.depth_lt hΘ j).le.trans hΘ2)
      (winCenter_pos γ_min C Θ j) u)
    hu0 (by positivity) hu_hi ?_
  have hmain_ge : faceFloorVal (faceBaseFreq γ_min C Θ (k + 1)) (k + 1)
      (SplineTower.depth Θ (k + 1)) ≤
      levelMain (faceBaseFreq γ_min C Θ (k + 1)) (k + 1) (SplineTower.depth Θ (k + 1))
        (winCenter γ_min C Θ (k + 1) : ℝ) u :=
    levelMain_ge_on_window (four_le_faceBaseFreq γ_min C Θ (k + 1))
      (SplineTower.depth_pos hΘ (k + 1)) ((SplineTower.depth_lt hΘ (k + 1)).le.trans hΘ2)
      (winCenter_pos γ_min C Θ (k + 1)) (err_bound_winCenter γ_min C Θ (k + 1)) hu
  have hexp_mono :
      Real.exp ((SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k) *
          ((winCenter γ_min C Θ (k + 1) : ℝ) - levelRadius (k + 1))) ≤
        Real.exp ((SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k) * u) := by
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu_lo ?_)
    exact sub_nonneg.mpr ((SplineTower.strictMono_depth hΘ (Nat.lt_succ_self k)).le)
  have hdom0 := exp_mul_faceFloorVal_ge γ_min C hΘ k
  have hL_nonneg : 0 ≤ faceFloorVal (faceBaseFreq γ_min C Θ (k + 1)) (k + 1)
      (SplineTower.depth Θ (k + 1)) := by
    unfold faceFloorVal levelMinWeight levelCoeffBound
    have := SplineTower.depth_nonneg hΘ (k + 1)
    positivity
  calc (k : ℝ) + 1 + 9 = (k : ℝ) + 10 := by ring
    _ ≤ Real.exp ((SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k) *
            ((winCenter γ_min C Θ (k + 1) : ℝ) - levelRadius (k + 1))) *
          faceFloorVal (faceBaseFreq γ_min C Θ (k + 1)) (k + 1)
            (SplineTower.depth Θ (k + 1)) := hdom0
    _ ≤ Real.exp ((SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k) * u) *
          levelMain (faceBaseFreq γ_min C Θ (k + 1)) (k + 1) (SplineTower.depth Θ (k + 1))
            (winCenter γ_min C Θ (k + 1) : ℝ) u :=
        mul_le_mul hexp_mono hmain_ge hL_nonneg (Real.exp_pos _).le

/-! ### Ordinate floor, unattained accumulating top, and local count bound `N(t, t + 1) ≤ C log(|t| + 3)` -/

theorem gamma_min_lt_im_minimalFaceCounterConfig (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) {ρ : ℂ}
    (hρ : ρ ∈ (minimalFaceCounterConfig γ_min C hΘ hΘ2).carrier) :
    γ_min < ρ.im := by
  rcases hρ with ⟨idx, rfl⟩
  exact (gamma_min_le_faceBaseFreq γ_min C Θ idx.1).trans_lt (facePt_im_bounds γ_min C Θ idx).1

theorem gamma_min_le_abs_im_minimalFaceCounterConfig {γ_min : ℝ} (hγ : 0 < γ_min) (C : ℝ)
    {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) {ρ : ℂ}
    (hρ : ρ ∈ (minimalFaceCounterConfig γ_min C hΘ hΘ2).carrier) :
    γ_min ≤ |ρ.im| := by
  have him := gamma_min_lt_im_minimalFaceCounterConfig γ_min C hΘ hΘ2 hρ
  rw [abs_of_pos (hγ.trans him)]
  exact him.le

theorem im_ne_zero_minimalFaceCounterConfig {γ_min : ℝ} (hγ : 0 < γ_min) (C : ℝ)
    {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) {ρ : ℂ}
    (hρ : ρ ∈ (minimalFaceCounterConfig γ_min C hΘ hΘ2).carrier) :
    ρ.im ≠ 0 :=
  (hγ.trans (gamma_min_lt_im_minimalFaceCounterConfig γ_min C hΘ hΘ2 hρ)).ne'

theorem re_lt_half_add_minimalFaceCounterConfig (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) {ρ : ℂ}
    (hρ : ρ ∈ (minimalFaceCounterConfig γ_min C hΘ hΘ2).carrier) :
    ρ.re < 1 / 2 + Θ := by
  rcases hρ with ⟨⟨k, ⟨d, b, s⟩⟩, rfl⟩
  have h0 := SplineTower.depth_nonneg hΘ k
  have h1 := SplineTower.depth_lt hΘ k
  cases s
  · rw [facePt_false_re]; linarith
  · rw [facePt_true_re]; linarith

theorem exists_re_gt_half_add_sub_minimalFaceCounterConfig (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ ∈ (minimalFaceCounterConfig γ_min C hΘ hΘ2).carrier, 1 / 2 + Θ - ε < ρ.re := by
  have hlim : Tendsto (SplineTower.depth Θ) atTop (𝓝 Θ) := by
    have h1 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k : ℕ => Θ * (1 - (1 / 2 : ℝ) ^ (k + 1))) atTop (𝓝 (Θ * (1 - 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.sub h1)
    rw [sub_zero, mul_one] at h2
    exact h2
  obtain ⟨k, hk⟩ := (eventually_atTop.mp (hlim.eventually (Ioi_mem_nhds (by linarith : Θ - ε < Θ))))
  have hk0 := hk k le_rfl
  set m₀ := levelStart (faceBaseFreq γ_min C Θ k) k
  have hm₀_mem : m₀ ∈ faceHarmonics γ_min C Θ k := by
    unfold faceHarmonics
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  refine ⟨facePt γ_min C Θ ⟨k, (⟨m₀, hm₀_mem⟩, false, true)⟩,
    ⟨⟨k, (⟨m₀, hm₀_mem⟩, false, true)⟩, rfl⟩, ?_⟩
  rw [facePt_true_re]
  linarith

/-- Auxiliary map for a fixed level `k` avoiding subtype coercions when bounding finite window
counts. -/
def facePtAtLevel (γ_min C Θ : ℝ) (k : ℕ) (dbs : ℕ × Bool × Bool) : ℂ :=
  if dbs.2.2 then
    (1 / 2 : ℂ) + (SplineTower.depth Θ k : ℂ) +
      (facePtFreq γ_min C Θ k dbs.2.1 dbs.1 : ℂ) * I
  else
    (1 / 2 : ℂ) - (SplineTower.depth Θ k : ℂ) +
      (facePtFreq γ_min C Θ k dbs.2.1 dbs.1 : ℂ) * I

theorem facePt_eq_facePtAtLevel (γ_min C Θ : ℝ) (idx : FaceIdx γ_min C Θ) :
    facePt γ_min C Θ idx =
      facePtAtLevel γ_min C Θ idx.1 (idx.2.1.1, idx.2.2.1, idx.2.2.2) := by
  rcases idx with ⟨k, ⟨d, b, _ | _⟩⟩ <;> rfl

/-- **Local count bound `N(t, t + 1) ≤ C log(|t| + 3)`.** Any unit ordinate interval `(t, t + 1]`
meets at most one tower level `k₀` and at most `8 k₀ + 10` harmonic indices `d`, contributing at
most `32 k₀ + 40 ≤ C log Γ_{k₀} ≤ C log(|t| + 3)` simple zeros. -/
theorem localCount_minimalFaceCounterConfig (γ_min : ℝ) {C : ℝ} (hC : 0 < C)
    {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (t : ℝ) :
    ((minimalFaceCounterConfig γ_min C hΘ hΘ2).N t (t + 1) : ℝ) ≤
      C * Real.log (|t| + 3) := by
  set Z := minimalFaceCounterConfig γ_min C hΘ hΘ2
  have hlog0 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  rcases (Z.window t (t + 1)).eq_empty_or_nonempty with hE | ⟨ρ₀, hρ₀⟩
  · have hN0 : Z.N t (t + 1) = 0 := by
      simp only [ZeroConfig.N, hE, finsum_mem_empty]
    rw [hN0, Nat.cast_zero]
    positivity
  rcases hρ₀ with ⟨⟨idx₀, rfl⟩, ht_lo₀, ht_hi₀⟩
  set k₀ := idx₀.1
  have him₀ := facePt_im_bounds γ_min C Θ idx₀
  have hΓ₀_ge : (4 : ℝ) ≤ (faceBaseFreq γ_min C Θ k₀ : ℝ) := by
    exact_mod_cast four_le_faceBaseFreq γ_min C Θ k₀
  have ht_gt_three : 3 < t := by linarith
  -- Every zero of `Z` in `(t, t + 1]` belongs to the same level `k₀`
  have hlevel_eq : ∀ idx : FaceIdx γ_min C Θ,
      t < (facePt γ_min C Θ idx).im → (facePt γ_min C Θ idx).im ≤ t + 1 → idx.1 = k₀ := by
    intro idx hlo hhi
    have him := facePt_im_bounds γ_min C Θ idx
    rcases lt_trichotomy idx.1 k₀ with hlt | heq | hgt
    · have hsep := two_mul_faceBaseFreq_add_four_le_of_lt γ_min C Θ hlt
      have hsepR : 2 * (faceBaseFreq γ_min C Θ idx.1 : ℝ) + 4 ≤
          (faceBaseFreq γ_min C Θ k₀ : ℝ) := by exact_mod_cast hsep
      linarith
    · exact heq
    · have hsep := two_mul_faceBaseFreq_add_four_le_of_lt γ_min C Θ hgt
      have hsepR : 2 * (faceBaseFreq γ_min C Θ k₀ : ℝ) + 4 ≤
          (faceBaseFreq γ_min C Θ idx.1 : ℝ) := by exact_mod_cast hsep
      linarith
  set d_min : ℕ := ⌊4 * ((k₀ : ℝ) + 1) * (t - 1)⌋₊
  set d_max : ℕ := ⌊4 * ((k₀ : ℝ) + 1) * (t + 1)⌋₊
  set S : Finset ℂ :=
    (Finset.Icc d_min d_max ×ˢ (Finset.univ : Finset (Bool × Bool))).image
      (facePtAtLevel γ_min C Θ k₀)
  have hfin := Z.finite_window t (t + 1)
  have hsub : hfin.toFinset ⊆ S := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    rcases hρ with ⟨⟨⟨k, ⟨⟨d, hd⟩, b, s⟩⟩, rfl⟩, hlo, hhi⟩
    have hk_eq : k = k₀ := hlevel_eq ⟨k, ⟨⟨d, hd⟩, b, s⟩⟩ hlo hhi
    rw [facePt_eq_facePtAtLevel]
    dsimp only
    rw [hk_eq]
    refine Finset.mem_image.mpr ⟨(d, b, s), ?_, rfl⟩
    rw [Finset.mem_product]
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · -- Lower bound `d_min ≤ d`
      have hord := levelFreq_strict_order (faceBaseFreq γ_min C Θ k) k
        (SplineTower.depth Θ k) (winCenter_pos γ_min C Θ k) d
      have h26 := two_six_div_winCenter_le_one γ_min C Θ k
      rw [facePt_im] at hlo
      dsimp only at hlo
      unfold facePtFreq at hlo
      have hbase_gt : t - 1 < levelBaseFreq k₀ d := by
        rw [← hk_eq]
        cases b <;> linarith
      unfold levelBaseFreq levelStep levelRadius at hbase_gt
      have hpos_k : 0 < 4 * ((k₀ : ℝ) + 1) := by positivity
      have hmul : 4 * ((k₀ : ℝ) + 1) * (t - 1) < (d : ℝ) := by
        have h1 := mul_lt_mul_of_pos_left hbase_gt hpos_k
        have h2 : 4 * ((k₀ : ℝ) + 1) * ((d : ℝ) * (1 / (4 * ((k₀ : ℝ) + 1)))) = (d : ℝ) := by
          field_simp [hpos_k.ne']
        linarith
      have hfl : (d_min : ℝ) ≤ 4 * ((k₀ : ℝ) + 1) * (t - 1) :=
        Nat.floor_le (mul_nonneg (by positivity) (by linarith))
      exact_mod_cast (hfl.trans_lt hmul).le
    · -- Upper bound `d ≤ d_max`
      have hord := levelFreq_strict_order (faceBaseFreq γ_min C Θ k) k
        (SplineTower.depth Θ k) (winCenter_pos γ_min C Θ k) d
      rw [facePt_im] at hhi
      dsimp only at hhi
      unfold facePtFreq at hhi
      have hbase_lt : levelBaseFreq k₀ d < t + 1 := by
        rw [← hk_eq]
        cases b <;> linarith
      unfold levelBaseFreq levelStep levelRadius at hbase_lt
      have hpos_k : 0 < 4 * ((k₀ : ℝ) + 1) := by positivity
      have hmul : (d : ℝ) ≤ 4 * ((k₀ : ℝ) + 1) * (t + 1) := by
        have h1 := mul_lt_mul_of_pos_left hbase_lt hpos_k
        have h2 : 4 * ((k₀ : ℝ) + 1) * ((d : ℝ) * (1 / (4 * ((k₀ : ℝ) + 1)))) = (d : ℝ) := by
          field_simp [hpos_k.ne']
        linarith
      exact Nat.le_floor hmul
  have hcard_Icc : (Finset.Icc d_min d_max).card ≤ 8 * k₀ + 10 := by
    rw [Nat.card_Icc]
    have hfl_hi : (d_max : ℝ) ≤ 4 * ((k₀ : ℝ) + 1) * (t + 1) :=
      Nat.floor_le (mul_nonneg (by positivity) (by linarith))
    have hfl_lo : 4 * ((k₀ : ℝ) + 1) * (t - 1) - 1 < (d_min : ℝ) :=
      Nat.sub_one_lt_floor _
    have hdiff_R : (d_max : ℝ) < (d_min : ℝ) + (8 * (k₀ : ℝ) + 9) := by linarith
    have hdiff_nat : d_max < d_min + (8 * k₀ + 9) := by exact_mod_cast hdiff_R
    omega
  have hcard_S : S.card ≤ 32 * k₀ + 40 := by
    calc S.card
        ≤ (Finset.Icc d_min d_max ×ˢ (Finset.univ : Finset (Bool × Bool))).card :=
          Finset.card_image_le
      _ = (Finset.Icc d_min d_max).card * 4 := by
          rw [Finset.card_product]
          rfl
      _ ≤ (8 * k₀ + 10) * 4 := Nat.mul_le_mul_right 4 hcard_Icc
      _ = 32 * k₀ + 40 := by omega
  have hN_le : Z.N t (t + 1) ≤ 32 * k₀ + 40 := by
    calc Z.N t (t + 1)
        = ∑ ρ ∈ hfin.toFinset, Z.mult ρ := finsum_mem_eq_finite_toFinset_sum _ hfin
      _ = hfin.toFinset.card := by
          simp [Z, minimalFaceCounterConfig]
      _ ≤ S.card := Finset.card_le_card hsub
      _ ≤ 32 * k₀ + 40 := hcard_S
  have hexp_le : Real.exp ((32 * (k₀ : ℝ) + 40) / C) ≤ |t| + 3 := by
    have h1 := exp_count_le_faceBaseFreq γ_min C Θ k₀
    have ht_abs : t ≤ |t| := le_abs_self t
    linarith
  have hlog_le : (32 * (k₀ : ℝ) + 40) / C ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp ((32 * (k₀ : ℝ) + 40) / C)]
    exact Real.log_le_log (Real.exp_pos _) hexp_le
  have hcount_R : 32 * (k₀ : ℝ) + 40 ≤ C * Real.log (|t| + 3) := by
    have := (div_le_iff₀ hC).mp hlog_le
    linarith
  calc (Z.N t (t + 1) : ℝ)
      ≤ ((32 * k₀ + 40 : ℕ) : ℝ) := by exact_mod_cast hN_le
    _ = 32 * (k₀ : ℝ) + 40 := by push_cast; ring
    _ ≤ C * Real.log (|t| + 3) := hcount_R

/-! ### The unbounded sub-logarithmic window radius `R(T) = o(log T)` -/

theorem exists_lt_winCenter_succ (γ_min C Θ T : ℝ) :
    ∃ n : ℕ, T < (winCenter γ_min C Θ (n + 1) : ℝ) := by
  refine ⟨⌊max T 0⌋₊, ?_⟩
  have h1 : T ≤ max T 0 := le_max_left _ _
  have h2 : max T 0 < (⌊max T 0⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h3 : ⌊max T 0⌋₊ + 1 ≤ winCenter γ_min C Θ (⌊max T 0⌋₊ + 1) :=
    k_le_winCenter γ_min C Θ _
  have h3R : (⌊max T 0⌋₊ : ℝ) + 1 ≤ (winCenter γ_min C Θ (⌊max T 0⌋₊ + 1) : ℝ) := by
    exact_mod_cast h3
  linarith

/-- Window index `k(T)`: the least `k` such that `T < T_{k+1}`. -/
def winIndex (γ_min C Θ T : ℝ) : ℕ :=
  Nat.find (exists_lt_winCenter_succ γ_min C Θ T)

/-- **The unbounded sub-logarithmic window radius `R(T)`.** Equal to `k + 1` on `[T_k, T_{k+1})`
and `1` below `T_1`. -/
def minimalFaceSubLogRadius (γ_min C Θ T : ℝ) : ℝ :=
  levelRadius (winIndex γ_min C Θ T)

theorem monotone_winIndex (γ_min C Θ : ℝ) : Monotone (winIndex γ_min C Θ) := by
  intro T₁ T₂ h12
  unfold winIndex
  exact Nat.find_min' _ (h12.trans_lt (Nat.find_spec (exists_lt_winCenter_succ γ_min C Θ T₂)))

theorem monotone_minimalFaceSubLogRadius (γ_min C Θ : ℝ) :
    Monotone (minimalFaceSubLogRadius γ_min C Θ) := by
  intro T₁ T₂ h12
  unfold minimalFaceSubLogRadius levelRadius
  have h := monotone_winIndex γ_min C Θ h12
  have hR : (winIndex γ_min C Θ T₁ : ℝ) ≤ (winIndex γ_min C Θ T₂ : ℝ) := by exact_mod_cast h
  linarith

theorem winIndex_winCenter (γ_min C Θ : ℝ) (k : ℕ) :
    winIndex γ_min C Θ (winCenter γ_min C Θ k : ℝ) = k := by
  unfold winIndex
  refine le_antisymm ?_ ?_
  · refine Nat.find_min' _ ?_
    exact_mod_cast strictMono_winCenter γ_min C Θ (Nat.lt_succ_self k)
  · by_contra hlt
    push Not at hlt
    have hspec := Nat.find_spec (exists_lt_winCenter_succ γ_min C Θ (winCenter γ_min C Θ k : ℝ))
    change (winCenter γ_min C Θ k : ℝ) <
      (winCenter γ_min C Θ (winIndex γ_min C Θ (winCenter γ_min C Θ k : ℝ) + 1) : ℝ) at hspec
    have hle : winIndex γ_min C Θ (winCenter γ_min C Θ k : ℝ) + 1 ≤ k := hlt
    have hmono := (strictMono_winCenter γ_min C Θ).monotone hle
    have hmonoR : (winCenter γ_min C Θ
        (winIndex γ_min C Θ (winCenter γ_min C Θ k : ℝ) + 1) : ℝ) ≤
        (winCenter γ_min C Θ k : ℝ) := by exact_mod_cast hmono
    linarith

theorem minimalFaceSubLogRadius_winCenter (γ_min C Θ : ℝ) (k : ℕ) :
    minimalFaceSubLogRadius γ_min C Θ (winCenter γ_min C Θ k : ℝ) = levelRadius k := by
  unfold minimalFaceSubLogRadius
  rw [winIndex_winCenter]

theorem one_le_minimalFaceSubLogRadius (γ_min C Θ T : ℝ) :
    1 ≤ minimalFaceSubLogRadius γ_min C Θ T := by
  unfold minimalFaceSubLogRadius levelRadius
  linarith [Nat.cast_nonneg (α := ℝ) (winIndex γ_min C Θ T)]

theorem tendsto_minimalFaceSubLogRadius_atTop (γ_min C Θ : ℝ) :
    Tendsto (minimalFaceSubLogRadius γ_min C Θ) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  refine ⟨(winCenter γ_min C Θ ⌈max B 0⌉₊ : ℝ), fun T hT => ?_⟩
  have h1 := monotone_minimalFaceSubLogRadius γ_min C Θ hT
  rw [minimalFaceSubLogRadius_winCenter] at h1
  unfold levelRadius at h1
  have h2 : B ≤ (⌈max B 0⌉₊ : ℝ) := (le_max_left B 0).trans (Nat.le_ceil _)
  linarith

theorem minimalFaceSubLogRadius_sq_le_log (γ_min C Θ : ℝ) {T : ℝ}
    (hT : (winCenter γ_min C Θ 1 : ℝ) ≤ T) :
    minimalFaceSubLogRadius γ_min C Θ T ^ 2 ≤ Real.log T := by
  set k := winIndex γ_min C Θ T
  have hk_pos : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    have hspec := Nat.find_spec (exists_lt_winCenter_succ γ_min C Θ T)
    change T < (winCenter γ_min C Θ (k + 1) : ℝ) at hspec
    rw [hk0] at hspec
    linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  have hmin := Nat.find_min (exists_lt_winCenter_succ γ_min C Θ T) (show m < k by omega)
  push Not at hmin
  rw [← hm] at hmin
  have hexp : Real.exp (levelRadius k ^ 2) ≤ T := by
    rw [hm]
    exact (exp_levelRadius_sq_le_winCenter γ_min C Θ m).trans (by rw [← hm]; exact hmin)
  have hT_pos : 0 < T := (Real.exp_pos _).trans_le hexp
  change levelRadius k ^ 2 ≤ Real.log T
  rw [← Real.log_exp (levelRadius k ^ 2)]
  exact Real.log_le_log (Real.exp_pos _) hexp

theorem tendsto_minimalFaceSubLogRadius_div_log (γ_min C Θ : ℝ) :
    Tendsto (fun T => minimalFaceSubLogRadius γ_min C Θ T / Real.log T) atTop (𝓝 0) := by
  set R := minimalFaceSubLogRadius γ_min C Θ
  have hinv : Tendsto (fun T => 1 / R T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_minimalFaceSubLogRadius_atTop γ_min C Θ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
  · filter_upwards [eventually_ge_atTop (winCenter γ_min C Θ 1 : ℝ)] with T hT
    have hR : 1 ≤ R T := one_le_minimalFaceSubLogRadius γ_min C Θ T
    have hlog : 1 ≤ Real.log T := by
      calc (1 : ℝ) ≤ R T ^ 2 := by nlinarith
        _ ≤ Real.log T := minimalFaceSubLogRadius_sq_le_log γ_min C Θ hT
    positivity
  · filter_upwards [eventually_ge_atTop (winCenter γ_min C Θ 1 : ℝ)] with T hT
    have hR : 1 ≤ R T := one_le_minimalFaceSubLogRadius γ_min C Θ T
    have hsq : R T ^ 2 ≤ Real.log T := minimalFaceSubLogRadius_sq_le_log γ_min C Θ hT
    have hlog_pos : 0 < Real.log T := by nlinarith
    calc R T / Real.log T
        ≤ R T / R T ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      _ = 1 / R T := by rw [sq]; field_simp [(by positivity : 0 < R T).ne']

/-! ### Main theorems: complete resolution of the minimal face for class `𝒵` -/

/-- Membership in the class `𝒵(γ_min, C)` of tempered reflection-symmetric zero configurations
without real zeros, with lowest ordinate at least `γ_min` and local counts
`N(t, t + 1) ≤ C log(|t| + 3)`. -/
def InClassZ (γ_min C : ℝ) (Z : ZeroConfig) : Prop :=
  TemperedConfig Z ∧
    (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
    (∀ ρ ∈ Z.carrier, γ_min ≤ |ρ.im|) ∧
    (∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ C * Real.log (|t| + 3))

theorem inClassZ_minimalFaceCounterConfig {γ_min C : ℝ} (hγ : 0 < γ_min) (hC : 0 < C)
    {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    InClassZ γ_min C (minimalFaceCounterConfig γ_min C hΘ hΘ2) :=
  ⟨temperedConfig_minimalFaceCounterConfig γ_min C hΘ hΘ2,
    fun _ hρ => im_ne_zero_minimalFaceCounterConfig hγ C hΘ hΘ2 hρ,
    fun _ hρ => gamma_min_le_abs_im_minimalFaceCounterConfig hγ C hΘ hΘ2 hρ,
    localCount_minimalFaceCounterConfig γ_min hC hΘ hΘ2⟩

/-- **Complete resolution of Question 2 (unbounded sub-logarithmic windows).** For every
`γ_min > 0`, `C > 0`, and `0 < Θ ≤ 1/2`, there exist a configuration `Z ∈ 𝒵(γ_min, C)` of simple
zeros (`mult ≡ 1`) with unattained accumulating top `sup Re ρ = 1/2 + Θ` and a monotone unbounded
sub-logarithmic radius `R(T) → ∞` with `R(T) = o(log T)` such that `2 Re S_Z(u)` is bounded below
beyond every bound on windows `[T − R(T), T + R(T)]` as `T → ∞`. -/
theorem exists_classZ_unbounded_subLog_windows_bddBelow_beyond_every_bound
    {γ_min C Θ : ℝ} (hγ : 0 < γ_min) (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ (Z : ZeroConfig) (R : ℝ → ℝ),
      InClassZ γ_min C Z ∧
      (∀ ρ ∈ Z.carrier, Z.mult ρ = 1) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ ρ ∈ Z.carrier, 1 / 2 + Θ - ε < ρ.re) ∧
      Monotone R ∧
      Tendsto R atTop atTop ∧
      Tendsto (fun T => R T / Real.log T) atTop (𝓝 0) ∧
      ∀ K U : ℝ, ∃ T : ℝ, U ≤ T ∧
        ∀ u : ℝ, |u - T| ≤ R T → K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  refine ⟨minimalFaceCounterConfig γ_min C hΘ hΘ2, minimalFaceSubLogRadius γ_min C Θ,
    inClassZ_minimalFaceCounterConfig hγ hC hΘ hΘ2,
    fun _ _ => rfl,
    fun _ hρ => re_lt_half_add_minimalFaceCounterConfig γ_min C hΘ hΘ2 hρ,
    fun _ hε => exists_re_gt_half_add_sub_minimalFaceCounterConfig γ_min C hΘ hΘ2 hε,
    monotone_minimalFaceSubLogRadius γ_min C Θ,
    tendsto_minimalFaceSubLogRadius_atTop γ_min C Θ,
    tendsto_minimalFaceSubLogRadius_div_log γ_min C Θ,
    fun K U => ?_⟩
  set k := max ⌈max K 0⌉₊ ⌈max U 0⌉₊
  refine ⟨(winCenter γ_min C Θ (k + 1) : ℝ), ?_, fun u hu => ?_⟩
  · have h1 : U ≤ (⌈max U 0⌉₊ : ℝ) := (le_max_left U 0).trans (Nat.le_ceil _)
    have h2 : ⌈max U 0⌉₊ ≤ k := le_max_right _ _
    have h3 : k + 1 ≤ winCenter γ_min C Θ (k + 1) := k_le_winCenter γ_min C Θ (k + 1)
    have h2R : (⌈max U 0⌉₊ : ℝ) ≤ (winCenter γ_min C Θ (k + 1) : ℝ) := by
      exact_mod_cast h2.trans (by omega : k ≤ winCenter γ_min C Θ (k + 1))
    linarith
  · rw [minimalFaceSubLogRadius_winCenter] at hu
    have hfloor := k_add_one_le_two_re_lagStructure_on_window γ_min C hΘ hΘ2 k hu
    have hK1 : K ≤ (⌈max K 0⌉₊ : ℝ) := (le_max_left K 0).trans (Nat.le_ceil _)
    have hK2 : (⌈max K 0⌉₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_max_left _ _
    linarith

/-- **Negation of "every unbounded radius decides `𝒵`".** Not every unbounded window radius
`R(T) → ∞` forces configurations in `𝒵(γ_min, C)` with bounded-below traces onto the critical
line. -/
theorem not_forall_unbounded_radius_decides_classZ {γ_min C : ℝ} (hγ : 0 < γ_min) (hC : 0 < C) :
    ¬ (∀ R : ℝ → ℝ, Tendsto R atTop atTop →
        ∀ Z : ZeroConfig, InClassZ γ_min C Z →
          (∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
            ∀ u : ℝ, |u - T| ≤ R T → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) →
          ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) := by
  intro hdecide
  obtain ⟨Z, R, hZ, _, _, hex_top, _, hR_top, _, hwin⟩ :=
    exists_classZ_unbounded_subLog_windows_bddBelow_beyond_every_bound hγ hC
      (Θ := 1 / 2) (by norm_num) le_rfl
  obtain ⟨ρ, hρ, hρ_re⟩ := hex_top (1 / 4) (by norm_num)
  have hcrit := hdecide R hR_top Z hZ ⟨0, fun U => by
    obtain ⟨T, hTU, hT⟩ := hwin 0 U
    exact ⟨T, hTU, fun u hu => by linarith [hT u hu]⟩⟩ ρ hρ
  linarith

/-- **Complete resolution of Question 1 (bounded windows): universal falsifier.** For every
`γ_min > 0`, `C > 0`, and `0 < Θ ≤ 1/2`, a single configuration `Z ∈ 𝒵(γ_min, C)` with unattained
accumulating top `sup Re ρ = 1/2 + Θ` simultaneously defeats every bounded window length `L > 0`
and every floor `K`: for every `L > 0`, `K : ℝ`, and `U : ℝ`, there exists `u₀ ≥ U` such that
`2 Re S_Z(u) ≥ K` on `[u₀, u₀ + L]`. -/
theorem exists_classZ_bounded_windows_bddBelow_beyond_every_bound
    {γ_min C Θ : ℝ} (hγ : 0 < γ_min) (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ Z : ZeroConfig,
      InClassZ γ_min C Z ∧
      (∀ ρ ∈ Z.carrier, Z.mult ρ = 1) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ ρ ∈ Z.carrier, 1 / 2 + Θ - ε < ρ.re) ∧
      ∀ L K U : ℝ, 0 < L → ∃ u₀ : ℝ, U ≤ u₀ ∧
        ∀ u ∈ Set.Icc u₀ (u₀ + L), K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  refine ⟨minimalFaceCounterConfig γ_min C hΘ hΘ2,
    inClassZ_minimalFaceCounterConfig hγ hC hΘ hΘ2,
    fun _ _ => rfl,
    fun _ hρ => re_lt_half_add_minimalFaceCounterConfig γ_min C hΘ hΘ2 hρ,
    fun _ hε => exists_re_gt_half_add_sub_minimalFaceCounterConfig γ_min C hΘ hΘ2 hε,
    fun L K U hL => ?_⟩
  set k := max (max ⌈L⌉₊ ⌈max K 0⌉₊) ⌈max (U + L) 0⌉₊
  set T := (winCenter γ_min C Θ (k + 1) : ℝ)
  have hL_le_rad : L ≤ levelRadius (k + 1) := by
    unfold levelRadius
    push_cast
    have h1 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
    have h2 : ⌈L⌉₊ ≤ k := (le_max_left _ _).trans (le_max_left _ _)
    have h2R : (⌈L⌉₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2
    linarith
  refine ⟨T - L / 2, ?_, fun u hu => ?_⟩
  · have h1 : U + L ≤ (⌈max (U + L) 0⌉₊ : ℝ) := (le_max_left _ 0).trans (Nat.le_ceil _)
    have h2 : ⌈max (U + L) 0⌉₊ ≤ k := le_max_right _ _
    have h3 : k + 1 ≤ winCenter γ_min C Θ (k + 1) := k_le_winCenter γ_min C Θ (k + 1)
    have h2R : (⌈max (U + L) 0⌉₊ : ℝ) ≤ T := by
      dsimp only [T]
      exact_mod_cast h2.trans (by omega : k ≤ winCenter γ_min C Θ (k + 1))
    linarith
  · rcases Set.mem_Icc.mp hu with ⟨hu1, hu2⟩
    have habs : |u - T| ≤ levelRadius (k + 1) := by
      rw [abs_le]
      constructor <;> linarith
    have hfloor := k_add_one_le_two_re_lagStructure_on_window γ_min C hΘ hΘ2 k habs
    have hK1 : K ≤ (⌈max K 0⌉₊ : ℝ) := (le_max_left K 0).trans (Nat.le_ceil _)
    have hK2 : ⌈max K 0⌉₊ ≤ k := (le_max_right _ _).trans (le_max_left _ _)
    have hK2R : (⌈max K 0⌉₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hK2
    linarith

/-- **Negative answer to Question 1 (bounded windows).** There is no bounded window length
`L = L(γ_min, C) > 0` such that a floor `2 Re S_Z(u) ≥ −K` on arbitrarily high windows
`[u₀, u₀ + L]` forces every zero of a configuration in `𝒵(γ_min, C)` onto the critical line. -/
theorem not_exists_bounded_window_length_decides_classZ
    {γ_min C : ℝ} (hγ : 0 < γ_min) (hC : 0 < C) :
    ¬ (∃ L : ℝ, 0 < L ∧ ∀ Z : ZeroConfig, InClassZ γ_min C Z →
        (∃ K : ℝ, ∀ U : ℝ, ∃ u₀ : ℝ, U ≤ u₀ ∧
          ∀ u ∈ Set.Icc u₀ (u₀ + L), -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) →
        ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) := by
  rintro ⟨L, hL, hdecide⟩
  obtain ⟨Z, hZ, _, _, hex_top, hwin⟩ :=
    exists_classZ_bounded_windows_bddBelow_beyond_every_bound hγ hC
      (Θ := 1 / 2) (by norm_num) le_rfl
  obtain ⟨ρ, hρ, hρ_re⟩ := hex_top (1 / 4) (by norm_num)
  have hcrit := hdecide Z hZ ⟨0, fun U => by
    obtain ⟨u₀, hu₀, h⟩ := hwin L 0 U hL
    exact ⟨u₀, hu₀, fun u hu => by linarith [h u hu]⟩⟩ ρ hρ
  linarith

/-! ### Corollaries: prime windows `log p ∈ [T − R(T), T + R(T)]` and maximal strip boundary `Θ = 1/2` -/

/-- **Prime-window corollary on unbounded sub-logarithmic windows.** Restricting `u = log p` to
primes `p` in `[T − R(T), T + R(T)]`, the same class-`𝒵` configuration satisfies
`2 Re S_Z(log p) ≥ K` for all primes `p` in the window, beyond every bound `K`. -/
theorem exists_classZ_unbounded_subLog_prime_windows_bddBelow
    {γ_min C Θ : ℝ} (hγ : 0 < γ_min) (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ (Z : ZeroConfig) (R : ℝ → ℝ),
      InClassZ γ_min C Z ∧
      (∀ ρ ∈ Z.carrier, Z.mult ρ = 1) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ ρ ∈ Z.carrier, 1 / 2 + Θ - ε < ρ.re) ∧
      Monotone R ∧
      Tendsto R atTop atTop ∧
      Tendsto (fun T => R T / Real.log T) atTop (𝓝 0) ∧
      ∀ K U : ℝ, ∃ T : ℝ, U ≤ T ∧
        ∀ p : ℕ, Nat.Prime p → |Real.log p - T| ≤ R T →
          K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re := by
  obtain ⟨Z, R, hZ, hmult, hlt, hex, hmono, htop, hsub, hwin⟩ :=
    exists_classZ_unbounded_subLog_windows_bddBelow_beyond_every_bound hγ hC hΘ hΘ2
  refine ⟨Z, R, hZ, hmult, hlt, hex, hmono, htop, hsub, fun K U => ?_⟩
  obtain ⟨T, hTU, hT⟩ := hwin K U
  exact ⟨T, hTU, fun p _ hp => hT (Real.log p) hp⟩

/-- **Prime-window corollary on bounded windows `[u₀, u₀ + L]`.** -/
theorem exists_classZ_bounded_prime_windows_bddBelow
    {γ_min C Θ : ℝ} (hγ : 0 < γ_min) (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ Z : ZeroConfig,
      InClassZ γ_min C Z ∧
      (∀ ρ ∈ Z.carrier, Z.mult ρ = 1) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ ρ ∈ Z.carrier, 1 / 2 + Θ - ε < ρ.re) ∧
      ∀ L K U : ℝ, 0 < L → ∃ u₀ : ℝ, U ≤ u₀ ∧
        ∀ p : ℕ, Nat.Prime p → Real.log p ∈ Set.Icc u₀ (u₀ + L) →
          K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re := by
  obtain ⟨Z, hZ, hmult, hlt, hex, hwin⟩ :=
    exists_classZ_bounded_windows_bddBelow_beyond_every_bound hγ hC hΘ hΘ2
  refine ⟨Z, hZ, hmult, hlt, hex, fun L K U hL => ?_⟩
  obtain ⟨u₀, hu₀, h⟩ := hwin L K U hL
  exact ⟨u₀, hu₀, fun p _ hp => h (Real.log p) hp⟩

/-- **Maximal strip boundary (`Θ = 1/2`, `sup Re ρ = 1`).** Even when zeros accumulate all the way
to the edge `Re s = 1` of the critical strip (`sup Re ρ = 1`), sub-logarithmic windows of radius
`R(T) = o(log T)` cannot detect the off-line zeros of `𝒵(γ_min, C)`. -/
theorem exists_classZ_top_one_unbounded_subLog_windows
    {γ_min C : ℝ} (hγ : 0 < γ_min) (hC : 0 < C) :
    ∃ (Z : ZeroConfig) (R : ℝ → ℝ),
      InClassZ γ_min C Z ∧
      (∀ ρ ∈ Z.carrier, Z.mult ρ = 1) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1) ∧
      (∀ ε : ℝ, 0 < ε → ∃ ρ ∈ Z.carrier, 1 - ε < ρ.re) ∧
      Monotone R ∧
      Tendsto R atTop atTop ∧
      Tendsto (fun T => R T / Real.log T) atTop (𝓝 0) ∧
      ∀ K U : ℝ, ∃ T : ℝ, U ≤ T ∧
        ∀ u : ℝ, |u - T| ≤ R T → K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  obtain ⟨Z, R, hZ, hmult, hlt, hex, hmono, htop, hsub, hwin⟩ :=
    exists_classZ_unbounded_subLog_windows_bddBelow_beyond_every_bound hγ hC
      (Θ := 1 / 2) (by norm_num) le_rfl
  refine ⟨Z, R, hZ, hmult, fun ρ hρ => by linarith [hlt ρ hρ],
    fun ε hε => ?_, hmono, htop, hsub, hwin⟩
  obtain ⟨ρ, hρ, hre⟩ := hex ε hε
  exact ⟨ρ, hρ, by linarith⟩

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
