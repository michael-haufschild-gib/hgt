import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.ArithmeticRealityAndBirkhoffSzego
import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.SharpStripZeroGrowthAndSqrtLowerBound
import GaloisForLFunctions.ConjugateDiagonalGeometry.CollisionChargeIncrements

/-!
# Zero-Separation-Free Polynomial-Prefix and `Θ(√m)` Unit-Window Stabilization

Qualitative Rouché stabilization of `integerThetaCollisionOperator` (`thetaPrefixThreshold T n` and
`sourceLoopStoppingPrefix T n`) requires resolving all pairwise zero coordinates `Π13` via
`collisionWindowGap T`, making the prefix cutoff sensitive to hypothetical close zero pairs.

This module eliminates zero-separation (`Π13`) dependence completely by combining three ingredients:

1. **Discrete strict convexity and multi-ellipse stage avoidance (`§1`)**:
   For `n ≥ 7`, the second difference of `zhukovskyEllipseForm n d` satisfies
   `16 (Re d - 1/2)² / n³ + 2 (Im d)² ≤ E_{n-1}(d) - 2 E_n(d) + E_{n+1}(d)`.
   Consequently, for any `6 ≤ S₀ ≤ S_max` and any `d ∈ ℂ`, at most `2` stages in `[S₀, S_max]` fall
   within `1 / (8 S_max³)` of `1`. By pigeonhole, for any target stage `S` and any `P : Finset ℂ`,
   some stage `n_* ∈ [max S 6, max S 6 + 2 |P|]` avoids all `|P|` Zhukovsky ellipses with uniform
   Euclidean loop clearance `‖zhukovskyLoop n_* u - d‖ ≥ (56 (max S 6 + 2 |P|)⁴)⁻¹`.
2. **Homogeneous Newton–Girard Lipschitz bounds without root separation (`§2`)**:
   Bounding elementary symmetric coefficients directly by rising binomials `C(M + k, k) Λ^k` yields
   `‖(pairDiffPoly d s₁).eval(J_n(u)) - (pairDiffPoly d s₂).eval(J_n(u))‖ ≤ 4 ε d⁴ (8 R)^{d²}`
   with zero root-gap denominators.
3. **Cumulative `O(m log²(m + S))` stabilization and optimal `Θ(√m)` Burnol unit-window
   stabilization (`§3–§4`)**:
   - On cumulative windows `[0, T_*)` (`T_* ∈ [m, m + 1]`), `integerThetaCollisionOperator`
     stabilizes for all `N ≥ C_cum (m + 1) (⌈log(m + S + 4)⌉₊ + 1)²` with zero `Π13` dependence.
   - Introducing the source-pure centered operator `centeredThetaCollisionOperator y₁ y₂ n N` on any
     vertical window `[y₁, y₂]` preserves arithmetic reality and the 6-way Birkhoff–Szegő TFAE, and
     stabilizes on Burnol-bracketed unit windows covering `[m, m + 1)` at the **optimal** prefix
     length `N ≥ C_unit (Nat.sqrt m + 1)` (`Θ(√m)`, matching the `Ω(√T)` lower bound) uniformly
     across all stages `S ≤ exp(√m)`.
-/

set_option autoImplicit false

open Complex MeasureTheory Filter Set Metric intervalIntegral Polynomial
open scoped BigOperators Topology Classical Real

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §1 Discrete strict convexity of `zhukovskyEllipseForm` and multi-ellipse avoidance -/

/-- Exact formula for `zhukovskyEllipseForm k d` at any stage `k ≥ 6`. -/
private lemma zhukovskyEllipseForm_eq_of_six_le {k : ℕ} (hk : 6 ≤ k) (d : ℂ) :
    zhukovskyEllipseForm k d =
      4 * (d.re - 1 / 2) ^ 2 * (1 + 1 / ((k : ℝ) - 1)) ^ 2 + d.im ^ 2 * (k : ℝ) ^ 2 := by
  have hstage : (zhukovskyStage k : ℝ) = (k : ℝ) := by
    exact_mod_cast zhukovskyStage_eq_self hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
    have hk6 : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hmaj : zhukovskyMajorAxis k = ((k : ℝ) - 1) / (2 * (k : ℝ)) := by
    unfold zhukovskyMajorAxis
    rw [hstage]
    field_simp [hk_pos.ne']
    ring
  have hmin : zhukovskyMinorAxis k = 1 / (k : ℝ) := by
    unfold zhukovskyMinorAxis
    rw [hstage]
  unfold zhukovskyEllipseForm
  rw [hmaj, hmin]
  field_simp [hk_pos.ne', hk1_pos.ne']
  ring

/-- **Discrete strict convexity of `zhukovskyEllipseForm` in the stage index `n ≥ 7`.**
With zero calculus, the second difference `E_{n-1}(d) - 2 E_n(d) + E_{n+1}(d)` dominates
`16 (Re d - 1/2)² / n³ + 2 (Im d)²`. -/
theorem zhukovskyEllipseForm_second_diff_ge {n : ℕ} (hn : 7 ≤ n) (d : ℂ) :
    16 * (d.re - 1 / 2) ^ 2 / (n : ℝ) ^ 3 + 2 * d.im ^ 2 ≤
      zhukovskyEllipseForm (n - 1) d - 2 * zhukovskyEllipseForm n d +
        zhukovskyEllipseForm (n + 1) d := by
  have hn1 : 6 ≤ n - 1 := by omega
  have hn0 : 6 ≤ n := by omega
  have hn2 : 6 ≤ n + 1 := by omega
  rw [zhukovskyEllipseForm_eq_of_six_le hn1 d, zhukovskyEllipseForm_eq_of_six_le hn0 d,
    zhukovskyEllipseForm_eq_of_six_le hn2 d]
  have hcast_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := Nat.cast_sub (by omega)
  have hcast_add : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast_sub, hcast_add]
  have hn7 : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set t : ℝ := (n : ℝ) - 1
  have ht6 : 6 ≤ t := by dsimp only [t]; linarith
  have ht_m1_pos : 0 < t - 1 := by linarith
  have ht_pos : 0 < t := by linarith
  have ht_p1_pos : 0 < t + 1 := by linarith
  have hsub_t : (n : ℝ) - 1 - 1 = t - 1 := by dsimp only [t]; ring
  have hadd_t : (n : ℝ) + 1 - 1 = t + 1 := by dsimp only [t]; ring
  rw [hsub_t, hadd_t]
  set a : ℝ := 1 + 1 / (t - 1)
  set b : ℝ := 1 + 1 / t
  set c : ℝ := 1 + 1 / (t + 1)
  have habc_diff : a - 2 * b + c = 2 / ((t - 1) * t * (t + 1)) := by
    dsimp only [a, b, c]
    field_simp [ht_m1_pos.ne', ht_pos.ne', ht_p1_pos.ne']
    ring
  have hprod_le : (t - 1) * t * (t + 1) ≤ (n : ℝ) ^ 3 := by
    have h1 : t - 1 ≤ (n : ℝ) := by dsimp only [t]; linarith
    have h2 : t ≤ (n : ℝ) := by dsimp only [t]; linarith
    have h3 : t + 1 = (n : ℝ) := by dsimp only [t]; ring
    rw [h3]
    calc (t - 1) * t * (n : ℝ)
        ≤ ((n : ℝ) * (n : ℝ)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul h1 h2 ht_pos.le (by linarith)) (by linarith)
      _ = (n : ℝ) ^ 3 := by ring
  have hdiff_ge : 2 / (n : ℝ) ^ 3 ≤ a - 2 * b + c := by
    rw [habc_diff]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hprod_le
  have hsum_ge : 4 ≤ a + 2 * b + c := by
    have ha1 : 1 ≤ a := by dsimp only [a]; positivity
    have hb1 : 1 ≤ b := by dsimp only [b]; positivity
    have hc1 : 1 ≤ c := by dsimp only [c]; positivity
    linarith
  have hquad_id : 4 * (a ^ 2 - 2 * b ^ 2 + c ^ 2) =
      2 * (a - c) ^ 2 + 2 * (a - 2 * b + c) * (a + 2 * b + c) := by ring
  have hquad_ge : 16 / (n : ℝ) ^ 3 ≤ 4 * (a ^ 2 - 2 * b ^ 2 + c ^ 2) := by
    rw [hquad_id]
    have hmul : 2 * (2 / (n : ℝ) ^ 3) * 4 ≤ 2 * (a - 2 * b + c) * (a + 2 * b + c) := by
      have h1 : 2 * (2 / (n : ℝ) ^ 3) ≤ 2 * (a - 2 * b + c) := by linarith
      exact mul_le_mul h1 hsum_ge (by norm_num) (by positivity)
    have hsq_nn : 0 ≤ 2 * (a - c) ^ 2 := by positivity
    calc 16 / (n : ℝ) ^ 3 = 2 * (2 / (n : ℝ) ^ 3) * 4 := by ring
      _ ≤ 2 * (a - c) ^ 2 + 2 * (a - 2 * b + c) * (a + 2 * b + c) := by linarith
  have him_id : d.im ^ 2 * ((n : ℝ) - 1) ^ 2 - 2 * (d.im ^ 2 * (n : ℝ) ^ 2) +
      d.im ^ 2 * ((n : ℝ) + 1) ^ 2 = 2 * d.im ^ 2 := by ring
  have hre_id :
      4 * (d.re - 1 / 2) ^ 2 * a ^ 2 + d.im ^ 2 * ((n : ℝ) - 1) ^ 2 -
        2 * (4 * (d.re - 1 / 2) ^ 2 * b ^ 2 + d.im ^ 2 * (n : ℝ) ^ 2) +
        (4 * (d.re - 1 / 2) ^ 2 * c ^ 2 + d.im ^ 2 * ((n : ℝ) + 1) ^ 2) =
      (d.re - 1 / 2) ^ 2 * (4 * (a ^ 2 - 2 * b ^ 2 + c ^ 2)) + 2 * d.im ^ 2 := by
    linear_combination him_id
  rw [hre_id]
  have hre_le : 16 * (d.re - 1 / 2) ^ 2 / (n : ℝ) ^ 3 ≤
      (d.re - 1 / 2) ^ 2 * (4 * (a ^ 2 - 2 * b ^ 2 + c ^ 2)) := by
    calc 16 * (d.re - 1 / 2) ^ 2 / (n : ℝ) ^ 3
        = (d.re - 1 / 2) ^ 2 * (16 / (n : ℝ) ^ 3) := by ring
      _ ≤ (d.re - 1 / 2) ^ 2 * (4 * (a ^ 2 - 2 * b ^ 2 + c ^ 2)) :=
          mul_le_mul_of_nonneg_left hquad_ge (sq_nonneg _)
  linarith

/-- Monotonicity of first differences under a nonnegative second-difference bound on `(S₀, S_max)`. -/
private lemma first_diff_mono_of_second_diff {f : ℕ → ℝ} {S₀ S_max : ℕ} {κ : ℝ}
    (hκ : 0 ≤ κ)
    (hconv : ∀ n : ℕ, S₀ < n → n < S_max → κ ≤ f (n - 1) - 2 * f n + f (n + 1)) :
    ∀ m₁ m₂ : ℕ, S₀ ≤ m₁ → m₁ ≤ m₂ → m₂ < S_max →
      f (m₁ + 1) - f m₁ ≤ f (m₂ + 1) - f m₂ := by
  intro m₁ m₂ hm₁ h12 hm₂
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h12
  induction k with
  | zero => simp
  | succ k ih =>
      have hk_lt : m₁ + k < S_max := by omega
      have hstep := hconv (m₁ + k + 1) (by omega) (by omega)
      have hsub : m₁ + k + 1 - 1 = m₁ + k := by omega
      rw [hsub] at hstep
      linarith [ih hk_lt]

/-- Lower telescoping bound when the initial forward difference is nonnegative. -/
private lemma diff_ge_first_step_of_nonneg {f : ℕ → ℝ} {S₀ S_max : ℕ} {κ : ℝ}
    (hκ : 0 ≤ κ)
    (hconv : ∀ n : ℕ, S₀ < n → n < S_max → κ ≤ f (n - 1) - 2 * f n + f (n + 1))
    {a b : ℕ} (ha : S₀ ≤ a) (hab : a < b) (hb : b ≤ S_max)
    (hstep0 : 0 ≤ f (a + 1) - f a) :
    f (a + 1) - f a ≤ f b - f a := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hab)
  subst hd
  induction d with
  | zero => simp
  | succ d ih =>
      have hmono := first_diff_mono_of_second_diff hκ hconv a (a + 1 + d) ha (by omega) (by omega)
      have prev := ih (by omega) (by omega)
      have hnext : a + 1 + (d + 1) = (a + 1 + d) + 1 := by omega
      rw [hnext]
      linarith

/-- Upper telescoping bound when the final backward difference is nonpositive. -/
private lemma diff_le_last_step_of_nonpos' {f : ℕ → ℝ} {S₀ S_max : ℕ} {κ : ℝ}
    (hκ : 0 ≤ κ)
    (hconv : ∀ n : ℕ, S₀ < n → n < S_max → κ ≤ f (n - 1) - 2 * f n + f (n + 1))
    {a b : ℕ} (ha : S₀ ≤ a) (hab : a < b) (hb : b ≤ S_max)
    (hstep1 : f b - f (b - 1) ≤ 0) :
    f b - f a ≤ f b - f (b - 1) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hab)
  subst hd
  induction d with
  | zero =>
      have hsub : a + 1 + 0 - 1 = a := by omega
      rw [hsub]
  | succ d ih =>
      have h1 : a + 1 + (d + 1) - 1 = a + 1 + d := by omega
      have h2 : (a + 1 + d) + 1 = a + 1 + (d + 1) := by omega
      rw [h1] at hstep1 ⊢
      have hmono_prev : f (a + 1 + d) - f (a + 1 + d - 1) ≤ 0 := by
        have hm := first_diff_mono_of_second_diff hκ hconv
          (a + 1 + d - 1) (a + 1 + d) (by omega) (by omega) (by omega)
        have hs : (a + 1 + d - 1) + 1 = a + 1 + d := by omega
        rw [hs, h2] at hm
        linarith
      have prev := ih (by omega) (by omega) hmono_prev
      have hprev_nonpos : f (a + 1 + d) - f a ≤ 0 := prev.trans hmono_prev
      linarith

/-- Any `Finset ℕ` of cardinality at least `3` contains three strictly increasing elements. -/
private lemma exists_three_strict_mono_of_three_le_card {A : Finset ℕ} (hcard : 3 ≤ A.card) :
    ∃ n₁ ∈ A, ∃ n₂ ∈ A, ∃ n₃ ∈ A, n₁ < n₂ ∧ n₂ < n₃ := by
  have hne1 : A.Nonempty := Finset.card_pos.mp (by omega)
  let n₁ := A.min' hne1
  have hn₁ : n₁ ∈ A := Finset.min'_mem A hne1
  let A₁ := A.erase n₁
  have hcard1 : 2 ≤ A₁.card := by
    rw [Finset.card_erase_of_mem hn₁]; omega
  have hne2 : A₁.Nonempty := Finset.card_pos.mp (by omega)
  let n₂ := A₁.min' hne2
  have hn₂_A₁ : n₂ ∈ A₁ := Finset.min'_mem A₁ hne2
  obtain ⟨hn₂_ne, hn₂⟩ := Finset.mem_erase.mp hn₂_A₁
  have h12 : n₁ < n₂ := lt_of_le_of_ne (Finset.min'_le A n₂ hn₂) hn₂_ne.symm
  let A₂ := A₁.erase n₂
  have hcard2 : 1 ≤ A₂.card := by
    rw [Finset.card_erase_of_mem hn₂_A₁]; omega
  obtain ⟨n₃, hn₃_A₂⟩ := Finset.card_pos.mp (by omega : 0 < A₂.card)
  obtain ⟨hn₃_ne, hn₃_A₁⟩ := Finset.mem_erase.mp hn₃_A₂
  have hn₃ : n₃ ∈ A := Finset.mem_of_mem_erase hn₃_A₁
  have h23 : n₂ < n₃ := lt_of_le_of_ne (Finset.min'_le A₁ n₃ hn₃_A₁) hn₃_ne.symm
  exact ⟨n₁, hn₁, n₂, hn₂, n₃, hn₃, h12, h23⟩

/-- **Three-point discrete convexity exclusion lemma.**
If `f : ℕ → ℝ` has second differences `≥ κ > 0` on `(S₀, S_max)`, at most `2` integers in
`[S₀, S_max]` satisfy `|f n - 1| < κ / 4`. -/
theorem card_filter_abs_sub_lt_le_two_of_second_diff {f : ℕ → ℝ} {S₀ S_max : ℕ} {κ : ℝ}
    (hκ : 0 < κ)
    (hconv : ∀ n : ℕ, S₀ < n → n < S_max → κ ≤ f (n - 1) - 2 * f n + f (n + 1)) :
    ((Finset.Icc S₀ S_max).filter (fun n => |f n - 1| < κ / 4)).card ≤ 2 := by
  by_contra hgt
  obtain ⟨n₁, h1, n₂, h2, n₃, h3, h12, h23⟩ :=
    exists_three_strict_mono_of_three_le_card (by omega : 3 ≤ _)
  obtain ⟨hI1, hf1⟩ := Finset.mem_filter.mp h1
  obtain ⟨hI2, hf2⟩ := Finset.mem_filter.mp h2
  obtain ⟨hI3, hf3⟩ := Finset.mem_filter.mp h3
  obtain ⟨hS1, _⟩ := Finset.mem_Icc.mp hI1
  obtain ⟨_, _⟩ := Finset.mem_Icc.mp hI2
  obtain ⟨_, h3S⟩ := Finset.mem_Icc.mp hI3
  have hmid : κ ≤ f (n₂ - 1) - 2 * f n₂ + f (n₂ + 1) :=
    hconv n₂ (by omega) (by omega)
  -- Upper bound on `f (n₂ + 1) - f n₂ < κ / 2`.
  have hright : f (n₂ + 1) - f n₂ < κ / 2 := by
    by_contra hge
    replace hge : κ / 2 ≤ f (n₂ + 1) - f n₂ := not_lt.mp hge
    have htel := diff_ge_first_step_of_nonneg hκ.le hconv (by omega : S₀ ≤ n₂) h23 h3S
      (by linarith)
    have habs2 := abs_lt.mp hf2
    have habs3 := abs_lt.mp hf3
    linarith
  -- Consequently `f n₂ - f (n₂ - 1) ≤ (f (n₂ + 1) - f n₂) - κ < -κ / 2 < 0`.
  have hleft : f n₂ - f (n₂ - 1) < -(κ / 2) := by linarith
  have htel_left := diff_le_last_step_of_nonpos' hκ.le hconv hS1 h12 (by omega : n₂ ≤ S_max)
    (by linarith)
  have habs1 := abs_lt.mp hf1
  have habs2 := abs_lt.mp hf2
  linarith

/-- For every `6 ≤ S₀ ≤ S_max` and every `d ∈ ℂ`, at most `2` stages in `[S₀, S_max]` satisfy
`|zhukovskyEllipseForm n d - 1| < 1 / (8 * S_max³)`. -/
theorem card_filter_zhukovskyEllipseForm_near_one_le_two {S₀ S_max : ℕ}
    (hS₀ : 6 ≤ S₀) (hSS : S₀ ≤ S_max) (d : ℂ) :
    ((Finset.Icc S₀ S_max).filter
      (fun n => |zhukovskyEllipseForm n d - 1| < 1 / (8 * (S_max : ℝ) ^ 3))).card ≤ 2 := by
  have hS_pos : (6 : ℝ) ≤ (S_max : ℝ) := by exact_mod_cast (hS₀.trans hSS)
  have hS3_pos : 0 < (S_max : ℝ) ^ 3 := by positivity
  by_cases hex : ∃ n₀ ∈ Finset.Icc S₀ S_max, 1 / 2 < zhukovskyEllipseForm n₀ d
  · obtain ⟨n₀, hn₀_mem, hn₀_gt⟩ := hex
    obtain ⟨hn₀_lo, hn₀_hi⟩ := Finset.mem_Icc.mp hn₀_mem
    have hn₀_6 : 6 ≤ n₀ := hS₀.trans hn₀_lo
    -- Either `8 * (d.re - 1/2)² > 1/4` or `d.im² * S_max² > 1/4`.
    have hmaj_ge : 5 / 12 ≤ zhukovskyMajorAxis n₀ := five_twelfths_le_zhukovskyMajorAxis n₀
    have hmaj_sq : 1 / 8 ≤ zhukovskyMajorAxis n₀ ^ 2 := by nlinarith
    have hmin_eq : zhukovskyMinorAxis n₀ = 1 / (n₀ : ℝ) := by
      unfold zhukovskyMinorAxis
      rw [zhukovskyStage_eq_self hn₀_6]
    have hform_le : zhukovskyEllipseForm n₀ d ≤
        8 * (d.re - 1 / 2) ^ 2 + d.im ^ 2 * (S_max : ℝ) ^ 2 := by
      unfold zhukovskyEllipseForm
      have h1 : (d.re - 1 / 2) ^ 2 / zhukovskyMajorAxis n₀ ^ 2 ≤ 8 * (d.re - 1 / 2) ^ 2 := by
        rw [div_le_iff₀ (sq_pos_of_pos (zhukovskyMajorAxis_pos n₀))]
        nlinarith [sq_nonneg (d.re - 1 / 2)]
      have hn₀_pos : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast (show 0 < n₀ by omega)
      have hn₀_S : (n₀ : ℝ) ≤ (S_max : ℝ) := by exact_mod_cast hn₀_hi
      have h2 : d.im ^ 2 / zhukovskyMinorAxis n₀ ^ 2 ≤ d.im ^ 2 * (S_max : ℝ) ^ 2 := by
        rw [hmin_eq, one_div, inv_pow, div_inv_eq_mul]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn₀_pos.le hn₀_S 2) (sq_nonneg _)
      linarith
    have hsum_gt : 1 / 2 < 8 * (d.re - 1 / 2) ^ 2 + d.im ^ 2 * (S_max : ℝ) ^ 2 :=
      hn₀_gt.trans_le hform_le
    set κ : ℝ := 1 / (2 * (S_max : ℝ) ^ 3)
    have hκ_pos : 0 < κ := by dsimp only [κ]; positivity
    have hconv : ∀ n : ℕ, S₀ < n → n < S_max →
        κ ≤ zhukovskyEllipseForm (n - 1) d - 2 * zhukovskyEllipseForm n d +
          zhukovskyEllipseForm (n + 1) d := by
      intro n hn_lo hn_hi
      have hn7 : 7 ≤ n := by omega
      have hsd := zhukovskyEllipseForm_second_diff_ge hn7 d
      have hn_le_S : (n : ℝ) ≤ (S_max : ℝ) := by exact_mod_cast hn_hi.le
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hn3_le : (n : ℝ) ^ 3 ≤ (S_max : ℝ) ^ 3 := pow_le_pow_left₀ hn_pos.le hn_le_S 3
      rcases lt_or_ge (1 / 4 : ℝ) (8 * (d.re - 1 / 2) ^ 2) with hre_big | hre_small
      · have h1 : κ ≤ 16 * (d.re - 1 / 2) ^ 2 / (S_max : ℝ) ^ 3 := by
          dsimp only [κ]
          rw [div_le_div_iff₀ (by positivity) hS3_pos]
          nlinarith
        have h2 : 16 * (d.re - 1 / 2) ^ 2 / (S_max : ℝ) ^ 3 ≤
            16 * (d.re - 1 / 2) ^ 2 / (n : ℝ) ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hn3_le
        have him_nn : 0 ≤ 2 * d.im ^ 2 := by positivity
        linarith
      · have him_big : 1 / 4 < d.im ^ 2 * (S_max : ℝ) ^ 2 := by linarith
        have hS_ge1 : (1 : ℝ) ≤ (S_max : ℝ) := by linarith
        have him_2 : κ ≤ 2 * d.im ^ 2 := by
          dsimp only [κ]
          rw [div_le_iff₀ (by positivity)]
          have h3 : d.im ^ 2 * (S_max : ℝ) ^ 2 ≤ d.im ^ 2 * (S_max : ℝ) ^ 3 := by
            have hp : (S_max : ℝ) ^ 2 ≤ (S_max : ℝ) ^ 3 := by nlinarith [sq_nonneg (S_max : ℝ)]
            exact mul_le_mul_of_nonneg_left hp (sq_nonneg _)
          nlinarith
        have hre_nn : 0 ≤ 16 * (d.re - 1 / 2) ^ 2 / (n : ℝ) ^ 3 := by positivity
        linarith
    have hκ4 : κ / 4 = 1 / (8 * (S_max : ℝ) ^ 3) := by dsimp only [κ]; ring
    rw [← hκ4]
    exact card_filter_abs_sub_lt_le_two_of_second_diff hκ_pos hconv
  · -- Every `n ∈ Icc S₀ S_max` has `zhukovskyEllipseForm n d ≤ 1 / 2`, so the filter is empty!
    push_neg at hex
    have hempty : (Finset.Icc S₀ S_max).filter
        (fun n => |zhukovskyEllipseForm n d - 1| < 1 / (8 * (S_max : ℝ) ^ 3)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro n hn hlt
      have hle := hex n hn
      have hsmall : 1 / (8 * (S_max : ℝ) ^ 3) < 1 / 2 := by
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hS_pos]
      have habs := (abs_lt.mp hlt).1
      linarith
    rw [hempty, Finset.card_empty]
    omega

/-- **Zero-separation-free multi-ellipse avoidance theorem.**
For any target stage `S : ℕ` and any finite set `P : Finset ℂ`, there exists a stage
`n_* ∈ [max S 6, max S 6 + 2 * P.card]` avoiding every Zhukovsky ellipse at `d ∈ P` with quantitative
gap `|zhukovskyEllipseForm n_* d - 1| ≥ 1 / (8 * (max S 6 + 2 * P.card)³)`. -/
theorem exists_natStage_avoiding_zhukovsky_ellipses (S : ℕ) (P : Finset ℂ) :
    ∃ n_star ∈ Finset.Icc (max S 6) (max S 6 + 2 * P.card),
      ∀ d ∈ P,
        1 / (8 * ((max S 6 + 2 * P.card : ℕ) : ℝ) ^ 3) ≤ |zhukovskyEllipseForm n_star d - 1| := by
  set S₀ : ℕ := max S 6
  set S_max : ℕ := S₀ + 2 * P.card
  set η : ℝ := 1 / (8 * ((S_max : ℕ) : ℝ) ^ 3)
  let bad : ℂ → Finset ℕ := fun d =>
    (Finset.Icc S₀ S_max).filter (fun n => |zhukovskyEllipseForm n d - 1| < η)
  have hbad_card : (P.biUnion bad).card ≤ 2 * P.card := by
    calc (P.biUnion bad).card
        ≤ ∑ d ∈ P, (bad d).card := Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ P, 2 := Finset.sum_le_sum fun d _ =>
          card_filter_zhukovskyEllipseForm_near_one_le_two (le_max_right S 6) (Nat.le_add_right _ _) d
      _ = 2 * P.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hIcc_card : (Finset.Icc S₀ S_max).card = 2 * P.card + 1 := by
    rw [Nat.card_Icc]
    dsimp only [S_max]
    omega
  have hsdiff_pos : 0 < ((Finset.Icc S₀ S_max) \ P.biUnion bad).card := by
    have hlt : (P.biUnion bad).card < (Finset.Icc S₀ S_max).card := by omega
    have hle := Finset.card_sdiff_add_card (Finset.Icc S₀ S_max) (P.biUnion bad)
    omega
  obtain ⟨n_star, hn_mem⟩ := Finset.card_pos.mp hsdiff_pos
  obtain ⟨hn_Icc, hn_not_bad⟩ := Finset.mem_sdiff.mp hn_mem
  refine ⟨n_star, hn_Icc, fun d hd => ?_⟩
  by_contra hlt
  exact hn_not_bad (Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_filter.mpr ⟨hn_Icc, not_le.mp hlt⟩⟩)

/-- **Quantitative Euclidean distance lower bound on `zhukovskyLoop n` from an ellipse-form gap.**
Whenever `0 < η ≤ 1` and `η ≤ |zhukovskyEllipseForm n d - 1|`, every point `u : UnitCircle` satisfies
`η / (7 * zhukovskyStage n) ≤ ‖zhukovskyLoop n u - d‖`. -/
theorem norm_zhukovskyLoop_sub_ge_of_ellipse_gap {n : ℕ} {d : ℂ} {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hgap : η ≤ |zhukovskyEllipseForm n d - 1|)
    (u : HTGeometry.UnitCircle) :
    η / (7 * (zhukovskyStage n : ℝ)) ≤ ‖zhukovskyLoop n u - d‖ := by
  set s : ℝ := (zhukovskyStage n : ℝ)
  have hs6 : 6 ≤ s := six_le_zhukovskyStage_real n
  have hs_pos : 0 < s := zhukovskyStage_pos n
  set z : ℂ := zhukovskyLoop n u
  set δ : ℝ := ‖z - d‖
  rcases le_or_gt (1 / s) δ with hbig | hsmall
  · calc η / (7 * s)
        ≤ 1 / s := by
          rw [div_le_div_iff₀ (by positivity) hs_pos]
          nlinarith
      _ ≤ δ := hbig
  · have hz_form : zhukovskyEllipseForm n z = 1 := zhukovskyEllipseForm_loop n u
    set a := zhukovskyMajorAxis n
    set b := zhukovskyMinorAxis n
    have ha_ge : 5 / 12 ≤ a := five_twelfths_le_zhukovskyMajorAxis n
    have ha_lt : a < 1 / 2 := zhukovskyMajorAxis_lt_half n
    have hb_eq : b = 1 / s := rfl
    have hre_diff : |(z.re - 1 / 2) - (d.re - 1 / 2)| ≤ δ := by
      have h : (z.re - 1 / 2) - (d.re - 1 / 2) = (z - d).re := by simp
      rw [h]; exact Complex.abs_re_le_norm (z - d)
    have him_diff : |z.im - d.im| ≤ δ := by
      have h : z.im - d.im = (z - d).im := (Complex.sub_im z d).symm
      rw [h]; exact Complex.abs_im_le_norm (z - d)
    have hz_re_le : |z.re - 1 / 2| ≤ a := by
      have h1 : (z.re - 1 / 2) ^ 2 / a ^ 2 ≤ 1 := by
        rw [← hz_form]; unfold zhukovskyEllipseForm
        have hnn : 0 ≤ z.im ^ 2 / b ^ 2 := by positivity
        dsimp only [a, b]; linarith
      have h2 : (z.re - 1 / 2) ^ 2 ≤ a ^ 2 := (div_le_one (by positivity)).mp h1
      have h3 : |z.re - 1 / 2| ≤ |a| := sq_le_sq.mp h2
      rwa [abs_of_pos (zhukovskyMajorAxis_pos n)] at h3
    have hz_im_le : |z.im| ≤ b := by
      have h1 : z.im ^ 2 / b ^ 2 ≤ 1 := by
        rw [← hz_form]; unfold zhukovskyEllipseForm
        have hnn : 0 ≤ (z.re - 1 / 2) ^ 2 / a ^ 2 := by positivity
        dsimp only [a, b]; linarith
      have h2 : z.im ^ 2 ≤ b ^ 2 := (div_le_one (by positivity)).mp h1
      have h3 : |z.im| ≤ |b| := sq_le_sq.mp h2
      rwa [abs_of_pos (zhukovskyMinorAxis_pos n)] at h3
    have hδ_sixth : δ ≤ 1 / 6 := hsmall.le.trans (one_div_le_one_div_of_le (by norm_num) hs6)
    have hre_sum : |(z.re - 1 / 2) + (d.re - 1 / 2)| ≤ 7 / 6 := by
      have h1 : |d.re - 1 / 2| ≤ |z.re - 1 / 2| + |(z.re - 1 / 2) - (d.re - 1 / 2)| := by
        have ht := abs_sub_le (d.re - 1 / 2) (z.re - 1 / 2) 0
        rw [sub_zero, sub_zero, abs_sub_comm] at ht
        exact ht
      have h2 := abs_add_le (z.re - 1 / 2) (d.re - 1 / 2)
      linarith
    have him_sum : |z.im + d.im| ≤ 3 / s := by
      have h1 : |d.im| ≤ |z.im| + |z.im - d.im| := by
        have ht := abs_sub_le d.im z.im 0
        rw [sub_zero, sub_zero, abs_sub_comm] at ht
        exact ht
      have h2 := abs_add_le z.im d.im
      rw [hb_eq] at hz_im_le
      have h3 : 1 / s + 1 / s + 1 / s = 3 / s := by ring
      linarith
    have hre_term : |(z.re - 1 / 2) ^ 2 - (d.re - 1 / 2) ^ 2| / a ^ 2 ≤ δ * (168 / 25) := by
      have hf : (z.re - 1 / 2) ^ 2 - (d.re - 1 / 2) ^ 2 =
          ((z.re - 1 / 2) - (d.re - 1 / 2)) * ((z.re - 1 / 2) + (d.re - 1 / 2)) := by ring
      have ha_sq : (25 / 144 : ℝ) ≤ a ^ 2 := by nlinarith
      rw [hf, abs_mul, div_le_iff₀ (by positivity : 0 < a ^ 2)]
      have hm : |(z.re - 1 / 2) - (d.re - 1 / 2)| * |(z.re - 1 / 2) + (d.re - 1 / 2)| ≤
          δ * (7 / 6) :=
        mul_le_mul hre_diff hre_sum (abs_nonneg _) (norm_nonneg _)
      have h2 : δ * (7 / 6) = δ * (168 / 25) * (25 / 144) := by ring
      calc |(z.re - 1 / 2) - (d.re - 1 / 2)| * |(z.re - 1 / 2) + (d.re - 1 / 2)|
          ≤ δ * (168 / 25) * (25 / 144) := hm.trans_eq h2
        _ ≤ δ * (168 / 25) * a ^ 2 :=
            mul_le_mul_of_nonneg_left ha_sq (mul_nonneg (norm_nonneg _) (by norm_num))
    have him_term : |z.im ^ 2 - d.im ^ 2| / b ^ 2 ≤ δ * (3 * s) := by
      have hf : z.im ^ 2 - d.im ^ 2 = (z.im - d.im) * (z.im + d.im) := by ring
      rw [hf, abs_mul, hb_eq, one_div, inv_pow, div_inv_eq_mul]
      calc |z.im - d.im| * |z.im + d.im| * s ^ 2
          ≤ (δ * (3 / s)) * s ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul him_diff him_sum (abs_nonneg _) (norm_nonneg _)) (sq_nonneg s)
        _ = δ * (3 * s) := by field_simp [hs_pos.ne']; ring
    have hform_diff : |zhukovskyEllipseForm n d - 1| ≤ δ * (7 * s) := by
      rw [← hz_form, abs_sub_comm]
      unfold zhukovskyEllipseForm
      have hsplit : ((z.re - 1 / 2) ^ 2 / a ^ 2 + z.im ^ 2 / b ^ 2) -
          ((d.re - 1 / 2) ^ 2 / a ^ 2 + d.im ^ 2 / b ^ 2) =
          ((z.re - 1 / 2) ^ 2 - (d.re - 1 / 2) ^ 2) / a ^ 2 +
            (z.im ^ 2 - d.im ^ 2) / b ^ 2 := by ring
      dsimp only [a, b] at hre_term him_term hsplit
      rw [hsplit]
      have htri := abs_add_le (((z.re - 1 / 2) ^ 2 - (d.re - 1 / 2) ^ 2) / zhukovskyMajorAxis n ^ 2)
        ((z.im ^ 2 - d.im ^ 2) / zhukovskyMinorAxis n ^ 2)
      rw [abs_div, abs_div, abs_of_pos (by positivity : 0 < zhukovskyMajorAxis n ^ 2),
        abs_of_pos (by positivity : 0 < zhukovskyMinorAxis n ^ 2)] at htri
      have h7s : 168 / 25 + 3 * s ≤ 7 * s := by linarith
      have hδ_nn : 0 ≤ δ := norm_nonneg _
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    exact hgap.trans hform_diff

/-! ## §2 Homogeneous Newton–Girard and pair-difference Lipschitz bounds -/

/-- Hockey-stick binomial identity `∑_{j=0}^k C(M + j, j) = C(M + 1 + k, k)`. -/
private lemma sum_range_choose_add (M k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), Nat.choose (M + j) j = Nat.choose (M + 1 + k) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : M + (k + 1) = (M + 1 + k) := by omega
      have h2 : M + 1 + (k + 1) = (M + 1 + k) + 1 := by omega
      rw [h1, h2, Nat.choose_succ_succ]

/-- Binomial absorption identity `(M + 1) C(M + k + 1, k) = (k + 1) C(M + k + 1, k + 1)`. -/
private lemma succ_mul_choose_add_eq (M k : ℕ) :
    (M + 1) * Nat.choose (M + k + 1) k = (k + 1) * Nat.choose (M + (k + 1)) (k + 1) := by
  suffices h : ∀ S M k : ℕ, M + k = S →
      (M + 1) * Nat.choose (M + k + 1) k = (k + 1) * Nat.choose (M + (k + 1)) (k + 1) from
    h (M + k) M k rfl
  intro S
  induction S with
  | zero =>
      intro M k hMk
      have hM0 : M = 0 := by omega
      have hk0 : k = 0 := by omega
      subst hM0 hk0
      simp
  | succ S ih =>
      intro M k hMk
      rcases k with _ | k'
      · simp
      · rcases M with _ | M'
        · simp [Nat.choose_succ_self_right]
        · set N := M' + k' + 2
          have htop1 : M' + 1 + (k' + 1) + 1 = N + 1 := by dsimp only [N]; omega
          have htop2 : M' + 1 + (k' + 1 + 1) = N + 1 := by dsimp only [N]; omega
          rw [htop1, htop2, Nat.choose_succ_succ N k', Nat.choose_succ_succ N (k' + 1)]
          have ih1 := ih (M' + 1) k' (by omega)
          have ih2 := ih M' (k' + 1) (by omega)
          have hN1 : M' + 1 + k' + 1 = N := by dsimp only [N]; omega
          have hN2 : M' + 1 + (k' + 1) = N := by dsimp only [N]; omega
          have hN3 : M' + (k' + 1) + 1 = N := by dsimp only [N]; omega
          have hN4 : M' + (k' + 1 + 1) = N := by dsimp only [N]; omega
          rw [hN1, hN2] at ih1
          rw [hN3, hN4] at ih2
          nlinarith

private lemma choose_le_two_pow (n k : ℕ) : Nat.choose n k ≤ 2 ^ n := by
  induction n generalizing k with
  | zero =>
      rcases k with _ | k <;> simp
  | succ n ih =>
      rcases k with _ | k
      · simp
      · rw [Nat.choose_succ_succ, pow_succ]
        have h1 := ih k
        have h2 := ih (k + 1)
        omega

private lemma sum_range_choose_real (n : ℕ) :
    ∑ r ∈ Finset.range (n + 1), (Nat.choose n r : ℝ) = 2 ^ n := by
  have h := (Commute.one_right (1 : ℝ)).add_pow n
  norm_num at h
  exact h.symm

private lemma sum_range_reflect_choose (M k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (Nat.choose (M + (k - j)) (k - j) : ℝ) =
      (Nat.choose (M + 1 + k) k : ℝ) := by
  have hbij : ∑ j ∈ Finset.range (k + 1), (Nat.choose (M + (k - j)) (k - j) : ℝ) =
      ∑ i ∈ Finset.range (k + 1), (Nat.choose (M + i) i : ℝ) := by
    refine Finset.sum_bij (fun j _ => k - j)
      (fun j hj => Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega))
      (fun j₁ hj₁ j₂ hj₂ h => by
        have h1 := Finset.mem_range.mp hj₁
        have h2 := Finset.mem_range.mp hj₂
        omega)
      (fun i hi => ⟨k - i, Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega),
        by have := Finset.mem_range.mp hi; omega⟩)
      (fun _ _ => rfl)
  rw [hbij, ← Nat.cast_sum, sum_range_choose_add]

/-- Homogeneous upper bound `‖newtonElem P k‖ ≤ C(M + k, k) * Λ^k` whenever
`‖P r‖ ≤ (M + 1) * Λ^r` (`1 ≤ r ≤ D`). -/
theorem norm_newtonElem_le_choose_pow {P : ℕ → ℂ} {M D : ℕ} {Λ : ℝ}
    (hΛ : 0 ≤ Λ)
    (hP : ∀ r : ℕ, 1 ≤ r → r ≤ D → ‖P r‖ ≤ ((M + 1 : ℕ) : ℝ) * Λ ^ r) :
    ∀ k : ℕ, k ≤ D → ‖newtonElem P k‖ ≤ (Nat.choose (M + k) k : ℝ) * Λ ^ k := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | k
      · simp [newtonElem]
      · rw [newtonElem, norm_mul, norm_inv]
        have hk1_norm : ‖(k + 1 : ℂ)‖ = ((k + 1 : ℕ) : ℝ) := by
          rw [show (k + 1 : ℂ) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
        rw [hk1_norm]
        have hsum_le : ‖∑ j ∈ Finset.range (k + 1),
              (-1 : ℂ) ^ j * newtonElem P (k - j) * P (j + 1)‖ ≤
            ((M + 1 : ℕ) : ℝ) * (Nat.choose (M + 1 + k) k : ℝ) * Λ ^ (k + 1) := by
          calc ‖∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * newtonElem P (k - j) * P (j + 1)‖
              ≤ ∑ j ∈ Finset.range (k + 1),
                  ‖(-1 : ℂ) ^ j * newtonElem P (k - j) * P (j + 1)‖ := norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.range (k + 1),
                  (Nat.choose (M + (k - j)) (k - j) : ℝ) * (((M + 1 : ℕ) : ℝ) * Λ ^ (k + 1)) := by
                refine Finset.sum_le_sum fun j hj => ?_
                have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
                rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
                have h1 := ih (k - j) (by omega) (by omega)
                have h2 := hP (j + 1) (by omega) (by omega)
                have hm := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
                have hpow : Λ ^ (k - j) * Λ ^ (j + 1) = Λ ^ (k + 1) := by
                  rw [← pow_add, show k - j + (j + 1) = k + 1 by omega]
                calc ‖newtonElem P (k - j)‖ * ‖P (j + 1)‖
                    ≤ ((Nat.choose (M + (k - j)) (k - j) : ℝ) * Λ ^ (k - j)) *
                        (((M + 1 : ℕ) : ℝ) * Λ ^ (j + 1)) := hm
                  _ = (Nat.choose (M + (k - j)) (k - j) : ℝ) *
                        (((M + 1 : ℕ) : ℝ) * (Λ ^ (k - j) * Λ ^ (j + 1))) := by ring
                  _ = _ := by rw [hpow]
            _ = (∑ j ∈ Finset.range (k + 1), (Nat.choose (M + (k - j)) (k - j) : ℝ)) *
                  (((M + 1 : ℕ) : ℝ) * Λ ^ (k + 1)) := (Finset.sum_mul _ _ _).symm
            _ = ((M + 1 : ℕ) : ℝ) * (Nat.choose (M + 1 + k) k : ℝ) * Λ ^ (k + 1) := by
                rw [sum_range_reflect_choose]; ring
        have habs : ((M + 1 : ℕ) : ℝ) * (Nat.choose (M + 1 + k) k : ℝ) =
            ((k + 1 : ℕ) : ℝ) * (Nat.choose (M + (k + 1)) (k + 1) : ℝ) := by
          have hnat := succ_mul_choose_add_eq M k
          rw [show M + 1 + k = M + k + 1 by omega]
          exact_mod_cast hnat
        have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        calc (((k + 1 : ℕ) : ℝ))⁻¹ *
                ‖∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * newtonElem P (k - j) * P (j + 1)‖
            ≤ (((k + 1 : ℕ) : ℝ))⁻¹ *
                (((M + 1 : ℕ) : ℝ) * (Nat.choose (M + 1 + k) k : ℝ) * Λ ^ (k + 1)) :=
              mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = (((k + 1 : ℕ) : ℝ))⁻¹ *
                (((k + 1 : ℕ) : ℝ) * (Nat.choose (M + (k + 1)) (k + 1) : ℝ) * Λ ^ (k + 1)) := by
              rw [habs]
          _ = (Nat.choose (M + (k + 1)) (k + 1) : ℝ) * Λ ^ (k + 1) := by
              field_simp [hk1_pos.ne']

/-- Homogeneous Lipschitz bound `‖newtonElem P₁ k - newtonElem P₂ k‖ ≤ δ * k * C(M + k, k) * Λ^k`. -/
theorem norm_newtonElem_sub_le_choose_pow {P₁ P₂ : ℕ → ℂ} {M D : ℕ} {Λ δ : ℝ}
    (hΛ : 0 ≤ Λ) (hδ : 0 ≤ δ)
    (hP₁ : ∀ r : ℕ, 1 ≤ r → r ≤ D → ‖P₁ r‖ ≤ ((M + 1 : ℕ) : ℝ) * Λ ^ r)
    (hP₂ : ∀ r : ℕ, 1 ≤ r → r ≤ D → ‖P₂ r‖ ≤ ((M + 1 : ℕ) : ℝ) * Λ ^ r)
    (hdiff : ∀ r : ℕ, 1 ≤ r → r ≤ D → ‖P₁ r - P₂ r‖ ≤ δ * ((M + 1 : ℕ) : ℝ) * Λ ^ r) :
    ∀ k : ℕ, k ≤ D →
      ‖newtonElem P₁ k - newtonElem P₂ k‖ ≤ δ * (k : ℝ) * (Nat.choose (M + k) k : ℝ) * Λ ^ k := by
  have he₂ := norm_newtonElem_le_choose_pow hΛ hP₂
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | k
      · simp [newtonElem]
      · rw [newtonElem, newtonElem, ← mul_sub, norm_mul, norm_inv, ← Finset.sum_sub_distrib]
        have hk1_norm : ‖(k + 1 : ℂ)‖ = ((k + 1 : ℕ) : ℝ) := by
          rw [show (k + 1 : ℂ) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
        rw [hk1_norm]
        have hsum_le :
            ‖∑ j ∈ Finset.range (k + 1),
                ((-1 : ℂ) ^ j * newtonElem P₁ (k - j) * P₁ (j + 1) -
                  (-1 : ℂ) ^ j * newtonElem P₂ (k - j) * P₂ (j + 1))‖ ≤
              δ * ((k + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) *
                (Nat.choose (M + 1 + k) k : ℝ) * Λ ^ (k + 1) := by
          calc ‖∑ j ∈ Finset.range (k + 1),
                  ((-1 : ℂ) ^ j * newtonElem P₁ (k - j) * P₁ (j + 1) -
                    (-1 : ℂ) ^ j * newtonElem P₂ (k - j) * P₂ (j + 1))‖
              ≤ ∑ j ∈ Finset.range (k + 1),
                  ‖(-1 : ℂ) ^ j * newtonElem P₁ (k - j) * P₁ (j + 1) -
                    (-1 : ℂ) ^ j * newtonElem P₂ (k - j) * P₂ (j + 1)‖ := norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.range (k + 1),
                  (Nat.choose (M + (k - j)) (k - j) : ℝ) *
                    (δ * ((k + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) * Λ ^ (k + 1)) := by
                refine Finset.sum_le_sum fun j hj => ?_
                have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
                have hsplit : (-1 : ℂ) ^ j * newtonElem P₁ (k - j) * P₁ (j + 1) -
                    (-1 : ℂ) ^ j * newtonElem P₂ (k - j) * P₂ (j + 1) =
                    (-1 : ℂ) ^ j * ((newtonElem P₁ (k - j) - newtonElem P₂ (k - j)) * P₁ (j + 1) +
                      newtonElem P₂ (k - j) * (P₁ (j + 1) - P₂ (j + 1))) := by ring
                rw [hsplit, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
                have htri := norm_add_le
                  ((newtonElem P₁ (k - j) - newtonElem P₂ (k - j)) * P₁ (j + 1))
                  (newtonElem P₂ (k - j) * (P₁ (j + 1) - P₂ (j + 1)))
                rw [norm_mul, norm_mul] at htri
                have hA := ih (k - j) (by omega) (by omega)
                have hB := hP₁ (j + 1) (by omega) (by omega)
                have hC := he₂ (k - j) (by omega)
                have hD := hdiff (j + 1) (by omega) (by omega)
                have hm1 := mul_le_mul hA hB (norm_nonneg _) (by positivity)
                have hm2 := mul_le_mul hC hD (norm_nonneg _) (by positivity)
                have hpow : Λ ^ (k - j) * Λ ^ (j + 1) = Λ ^ (k + 1) := by
                  rw [← pow_add, show k - j + (j + 1) = k + 1 by omega]
                have hk_le : ((k - j : ℕ) : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) := by
                  exact_mod_cast (show (k - j) + 1 ≤ k + 1 by omega)
                have hcomb :
                    (δ * ((k - j : ℕ) : ℝ) * (Nat.choose (M + (k - j)) (k - j) : ℝ) * Λ ^ (k - j)) *
                        (((M + 1 : ℕ) : ℝ) * Λ ^ (j + 1)) +
                      ((Nat.choose (M + (k - j)) (k - j) : ℝ) * Λ ^ (k - j)) *
                        (δ * ((M + 1 : ℕ) : ℝ) * Λ ^ (j + 1)) =
                    (((k - j : ℕ) : ℝ) + 1) *
                      ((Nat.choose (M + (k - j)) (k - j) : ℝ) *
                        (δ * ((M + 1 : ℕ) : ℝ) * (Λ ^ (k - j) * Λ ^ (j + 1)))) := by ring
                rw [hpow] at hcomb
                refine htri.trans ((add_le_add hm1 hm2).trans (hcomb.trans_le ?_))
                have hnn : 0 ≤ (Nat.choose (M + (k - j)) (k - j) : ℝ) *
                    (δ * ((M + 1 : ℕ) : ℝ) * Λ ^ (k + 1)) := by positivity
                calc (((k - j : ℕ) : ℝ) + 1) *
                        ((Nat.choose (M + (k - j)) (k - j) : ℝ) *
                          (δ * ((M + 1 : ℕ) : ℝ) * Λ ^ (k + 1)))
                    ≤ ((k + 1 : ℕ) : ℝ) *
                        ((Nat.choose (M + (k - j)) (k - j) : ℝ) *
                          (δ * ((M + 1 : ℕ) : ℝ) * Λ ^ (k + 1))) :=
                      mul_le_mul_of_nonneg_right hk_le hnn
                  _ = _ := by ring
            _ = (∑ j ∈ Finset.range (k + 1), (Nat.choose (M + (k - j)) (k - j) : ℝ)) *
                  (δ * ((k + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) * Λ ^ (k + 1)) :=
                (Finset.sum_mul _ _ _).symm
            _ = δ * ((k + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) *
                  (Nat.choose (M + 1 + k) k : ℝ) * Λ ^ (k + 1) := by
                rw [sum_range_reflect_choose]; ring
        have habs : ((M + 1 : ℕ) : ℝ) * (Nat.choose (M + 1 + k) k : ℝ) =
            ((k + 1 : ℕ) : ℝ) * (Nat.choose (M + (k + 1)) (k + 1) : ℝ) := by
          have hnat := succ_mul_choose_add_eq M k
          rw [show M + 1 + k = M + k + 1 by omega]
          exact_mod_cast hnat
        have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        calc (((k + 1 : ℕ) : ℝ))⁻¹ *
                ‖∑ j ∈ Finset.range (k + 1),
                  ((-1 : ℂ) ^ j * newtonElem P₁ (k - j) * P₁ (j + 1) -
                    (-1 : ℂ) ^ j * newtonElem P₂ (k - j) * P₂ (j + 1))‖
            ≤ (((k + 1 : ℕ) : ℝ))⁻¹ *
                (δ * ((k + 1 : ℕ) : ℝ) *
                  (((M + 1 : ℕ) : ℝ) * (Nat.choose (M + 1 + k) k : ℝ)) * Λ ^ (k + 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact hsum_le.trans_eq (by ring)
          _ = (((k + 1 : ℕ) : ℝ))⁻¹ *
                (δ * ((k + 1 : ℕ) : ℝ) *
                  (((k + 1 : ℕ) : ℝ) * (Nat.choose (M + (k + 1)) (k + 1) : ℝ)) * Λ ^ (k + 1)) := by
              rw [habs]
          _ = δ * ((k + 1 : ℕ) : ℝ) * (Nat.choose (M + (k + 1)) (k + 1) : ℝ) * Λ ^ (k + 1) := by
              field_simp [hk1_pos.ne']

private lemma norm_zhukovskyLoop_le_two' (n : ℕ) (u : HTGeometry.UnitCircle) :
    ‖zhukovskyLoop n u‖ ≤ 2 := by
  have h1 := norm_zhukovskyLoop_sub_half_le n u
  have ha := (zhukovskyMajorAxis_lt_half n).le
  have hb := zhukovskyMinorAxis_le_sixth n
  have htri : ‖zhukovskyLoop n u‖ ≤ ‖zhukovskyLoop n u - (1 / 2 : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := by
    simpa using norm_add_le (zhukovskyLoop n u - (1 / 2 : ℂ)) (1 / 2 : ℂ)
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  linarith

/-- **Root-separation-free Lipschitz bound for `pairDiffPoly` along `zhukovskyLoop n`.**
If `1 ≤ R`, `0 ≤ ε`, and `‖sᵢ r‖ ≤ d * R^r`, `‖s₁ r - s₂ r‖ ≤ ε * d * R^r` for `1 ≤ r ≤ d²`,
then `‖(pairDiffPoly d s₁).eval(J_n(u)) - (pairDiffPoly d s₂).eval(J_n(u))‖ ≤ 4 ε d⁴ (8 R)^{d²}`
uniformly across all `n : ℕ` and `u : UnitCircle`. -/
theorem norm_pairDiffPoly_eval_sub_le_on_zhukovsky {d : ℕ} {s₁ s₂ : ℕ → ℂ} {R ε : ℝ}
    (hR : 1 ≤ R) (hε : 0 ≤ ε)
    (hs₁ : ∀ r : ℕ, 1 ≤ r → r ≤ d ^ 2 → ‖s₁ r‖ ≤ (d : ℝ) * R ^ r)
    (hs₂ : ∀ r : ℕ, 1 ≤ r → r ≤ d ^ 2 → ‖s₂ r‖ ≤ (d : ℝ) * R ^ r)
    (hdiff : ∀ r : ℕ, 1 ≤ r → r ≤ d ^ 2 → ‖s₁ r - s₂ r‖ ≤ ε * (d : ℝ) * R ^ r)
    (n : ℕ) (u : HTGeometry.UnitCircle) :
    ‖(pairDiffPoly d s₁).eval (zhukovskyLoop n u) -
        (pairDiffPoly d s₂).eval (zhukovskyLoop n u)‖ ≤
      4 * ε * ((d : ℝ) ^ 4) * (8 * R) ^ (d ^ 2) := by
  rcases eq_or_ne d 0 with rfl | hd_ne
  · simp
  have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero hd_ne
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  let s₀₁ : ℕ → ℂ := fun r => if r = 0 then (d : ℂ) else s₁ r
  let s₀₂ : ℕ → ℂ := fun r => if r = 0 then (d : ℂ) else s₂ r
  have hs₀₁ : ∀ r : ℕ, r ≤ d ^ 2 → ‖s₀₁ r‖ ≤ (d : ℝ) * R ^ r := by
    intro r hr
    by_cases hr0 : r = 0
    · subst hr0; simp [s₀₁]
    · simpa only [s₀₁, if_neg hr0] using hs₁ r (Nat.pos_of_ne_zero hr0) hr
  have hs₀₂ : ∀ r : ℕ, r ≤ d ^ 2 → ‖s₀₂ r‖ ≤ (d : ℝ) * R ^ r := by
    intro r hr
    by_cases hr0 : r = 0
    · subst hr0; simp [s₀₂]
    · simpa only [s₀₂, if_neg hr0] using hs₂ r (Nat.pos_of_ne_zero hr0) hr
  have hs₀_diff : ∀ r : ℕ, r ≤ d ^ 2 → ‖s₀₁ r - s₀₂ r‖ ≤ ε * (d : ℝ) * R ^ r := by
    intro r hr
    by_cases hr0 : r = 0
    · subst hr0; simp [s₀₁, s₀₂]; positivity
    · simpa only [s₀₁, s₀₂, if_neg hr0] using hdiff r (Nat.pos_of_ne_zero hr0) hr
  have hPD₁ : ∀ K : ℕ, 1 ≤ K → K ≤ d ^ 2 →
      ‖pairDiffPowerSum d s₁ K‖ ≤ ((d ^ 2 + 1 : ℕ) : ℝ) * (2 * R) ^ K := by
    intro K _ hK
    unfold pairDiffPowerSum
    change ‖∑ r ∈ Finset.range (K + 1),
      (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀₁ r * s₀₁ (K - r)‖ ≤ _
    calc ‖∑ r ∈ Finset.range (K + 1),
            (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀₁ r * s₀₁ (K - r)‖
        ≤ ∑ r ∈ Finset.range (K + 1),
            (Nat.choose K r : ℝ) * (((d : ℝ) ^ 2) * R ^ K) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
          have hrK : r ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Complex.norm_natCast]
          have hpow : R ^ r * R ^ (K - r) = R ^ K := by
            rw [← pow_add, Nat.add_sub_of_le hrK]
          calc (Nat.choose K r : ℝ) * ‖s₀₁ r‖ * ‖s₀₁ (K - r)‖
              = (Nat.choose K r : ℝ) * (‖s₀₁ r‖ * ‖s₀₁ (K - r)‖) := by ring
            _ ≤ (Nat.choose K r : ℝ) * (((d : ℝ) * R ^ r) * ((d : ℝ) * R ^ (K - r))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul (hs₀₁ r (hrK.trans hK))
                    (hs₀₁ (K - r) ((Nat.sub_le K r).trans hK)) (norm_nonneg _) (by positivity))
                  (by positivity)
            _ = (Nat.choose K r : ℝ) * ((d : ℝ) ^ 2 * (R ^ r * R ^ (K - r))) := by ring
            _ = _ := by rw [hpow]
      _ = (∑ r ∈ Finset.range (K + 1), (Nat.choose K r : ℝ)) * ((d : ℝ) ^ 2 * R ^ K) :=
          (Finset.sum_mul _ _ _).symm
      _ = (d : ℝ) ^ 2 * (2 * R) ^ K := by
          rw [sum_range_choose_real, mul_pow]; ring
      _ ≤ ((d ^ 2 + 1 : ℕ) : ℝ) * (2 * R) ^ K := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          push_cast; linarith
  have hPD₂ : ∀ K : ℕ, 1 ≤ K → K ≤ d ^ 2 →
      ‖pairDiffPowerSum d s₂ K‖ ≤ ((d ^ 2 + 1 : ℕ) : ℝ) * (2 * R) ^ K := by
    intro K _ hK
    unfold pairDiffPowerSum
    change ‖∑ r ∈ Finset.range (K + 1),
      (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀₂ r * s₀₂ (K - r)‖ ≤ _
    calc ‖∑ r ∈ Finset.range (K + 1),
            (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀₂ r * s₀₂ (K - r)‖
        ≤ ∑ r ∈ Finset.range (K + 1),
            (Nat.choose K r : ℝ) * (((d : ℝ) ^ 2) * R ^ K) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
          have hrK : r ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Complex.norm_natCast]
          have hpow : R ^ r * R ^ (K - r) = R ^ K := by
            rw [← pow_add, Nat.add_sub_of_le hrK]
          calc (Nat.choose K r : ℝ) * ‖s₀₂ r‖ * ‖s₀₂ (K - r)‖
              = (Nat.choose K r : ℝ) * (‖s₀₂ r‖ * ‖s₀₂ (K - r)‖) := by ring
            _ ≤ (Nat.choose K r : ℝ) * (((d : ℝ) * R ^ r) * ((d : ℝ) * R ^ (K - r))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul (hs₀₂ r (hrK.trans hK))
                    (hs₀₂ (K - r) ((Nat.sub_le K r).trans hK)) (norm_nonneg _) (by positivity))
                  (by positivity)
            _ = (Nat.choose K r : ℝ) * ((d : ℝ) ^ 2 * (R ^ r * R ^ (K - r))) := by ring
            _ = _ := by rw [hpow]
      _ = (∑ r ∈ Finset.range (K + 1), (Nat.choose K r : ℝ)) * ((d : ℝ) ^ 2 * R ^ K) :=
          (Finset.sum_mul _ _ _).symm
      _ = (d : ℝ) ^ 2 * (2 * R) ^ K := by
          rw [sum_range_choose_real, mul_pow]; ring
      _ ≤ ((d ^ 2 + 1 : ℕ) : ℝ) * (2 * R) ^ K := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          push_cast; linarith
  have hPD_diff : ∀ K : ℕ, 1 ≤ K → K ≤ d ^ 2 →
      ‖pairDiffPowerSum d s₁ K - pairDiffPowerSum d s₂ K‖ ≤
        (2 * ε) * ((d ^ 2 + 1 : ℕ) : ℝ) * (2 * R) ^ K := by
    intro K _ hK
    unfold pairDiffPowerSum
    change ‖(∑ r ∈ Finset.range (K + 1),
        (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀₁ r * s₀₁ (K - r)) -
      (∑ r ∈ Finset.range (K + 1),
        (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀₂ r * s₀₂ (K - r))‖ ≤ _
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ r ∈ Finset.range (K + 1),
            ((-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀₁ r * s₀₁ (K - r) -
              (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀₂ r * s₀₂ (K - r))‖
        ≤ ∑ r ∈ Finset.range (K + 1),
            (Nat.choose K r : ℝ) * (2 * ε * (d : ℝ) ^ 2 * R ^ K) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
          have hrK : r ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          have hsp : (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀₁ r * s₀₁ (K - r) -
              (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀₂ r * s₀₂ (K - r) =
              (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) *
                ((s₀₁ r - s₀₂ r) * s₀₁ (K - r) + s₀₂ r * (s₀₁ (K - r) - s₀₂ (K - r))) := by ring
          rw [hsp, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Complex.norm_natCast]
          have htri := norm_add_le ((s₀₁ r - s₀₂ r) * s₀₁ (K - r))
            (s₀₂ r * (s₀₁ (K - r) - s₀₂ (K - r)))
          rw [norm_mul, norm_mul] at htri
          have hm1 := mul_le_mul (hs₀_diff r (hrK.trans hK))
            (hs₀₁ (K - r) ((Nat.sub_le K r).trans hK)) (norm_nonneg _) (by positivity)
          have hm2 := mul_le_mul (hs₀₂ r (hrK.trans hK))
            (hs₀_diff (K - r) ((Nat.sub_le K r).trans hK)) (norm_nonneg _) (by positivity)
          have hpow : R ^ r * R ^ (K - r) = R ^ K := by
            rw [← pow_add, Nat.add_sub_of_le hrK]
          refine mul_le_mul_of_nonneg_left (htri.trans ((add_le_add hm1 hm2).trans_eq ?_))
            (by positivity)
          calc (ε * (d : ℝ) * R ^ r) * ((d : ℝ) * R ^ (K - r)) +
                ((d : ℝ) * R ^ r) * (ε * (d : ℝ) * R ^ (K - r))
              = 2 * ε * (d : ℝ) ^ 2 * (R ^ r * R ^ (K - r)) := by ring
            _ = _ := by rw [hpow]
      _ = (∑ r ∈ Finset.range (K + 1), (Nat.choose K r : ℝ)) *
            (2 * ε * (d : ℝ) ^ 2 * R ^ K) := (Finset.sum_mul _ _ _).symm
      _ = (2 * ε) * (d : ℝ) ^ 2 * (2 * R) ^ K := by
          rw [sum_range_choose_real, mul_pow]; ring
      _ ≤ (2 * ε) * ((d ^ 2 + 1 : ℕ) : ℝ) * (2 * R) ^ K := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          push_cast; linarith
  have helem := norm_newtonElem_sub_le_choose_pow (M := d ^ 2) (D := d ^ 2)
    (Λ := 2 * R) (δ := 2 * ε) (by positivity) (by positivity) hPD₁ hPD₂ hPD_diff
  unfold pairDiffPoly newtonPoly
  rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, ← Finset.sum_sub_distrib]
  have hloop_le : ‖zhukovskyLoop n u‖ ≤ 2 * R :=
    (norm_zhukovskyLoop_le_two' n u).trans (by linarith)
  calc ‖∑ k ∈ Finset.range (d ^ 2 + 1),
          ((C ((-1 : ℂ) ^ k * newtonElem (pairDiffPowerSum d s₁) k) * X ^ (d ^ 2 - k)).eval
              (zhukovskyLoop n u) -
            (C ((-1 : ℂ) ^ k * newtonElem (pairDiffPowerSum d s₂) k) * X ^ (d ^ 2 - k)).eval
              (zhukovskyLoop n u))‖
      ≤ ∑ k ∈ Finset.range (d ^ 2 + 1),
          (2 * ε * ((d : ℝ) ^ 2) * (8 * R) ^ (d ^ 2)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        have hk_le : k ≤ d ^ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
        have hsp : (-1 : ℂ) ^ k * newtonElem (pairDiffPowerSum d s₁) k *
              (zhukovskyLoop n u) ^ (d ^ 2 - k) -
            (-1 : ℂ) ^ k * newtonElem (pairDiffPowerSum d s₂) k *
              (zhukovskyLoop n u) ^ (d ^ 2 - k) =
            (-1 : ℂ) ^ k *
              (newtonElem (pairDiffPowerSum d s₁) k - newtonElem (pairDiffPowerSum d s₂) k) *
              (zhukovskyLoop n u) ^ (d ^ 2 - k) := by ring
        rw [hsp, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
        have he_k := helem k hk_le
        have hpow_z : ‖zhukovskyLoop n u‖ ^ (d ^ 2 - k) ≤ (2 * R) ^ (d ^ 2 - k) :=
          pow_le_pow_left₀ (norm_nonneg _) hloop_le _
        have hch : (Nat.choose (d ^ 2 + k) k : ℝ) ≤ (4 : ℝ) ^ (d ^ 2) := by
          have h1 : Nat.choose (d ^ 2 + k) k ≤ 2 ^ (d ^ 2 + k) := choose_le_two_pow _ _
          have h2 : 2 ^ (d ^ 2 + k) ≤ 2 ^ (2 * d ^ 2) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          have h3 : (2 ^ (2 * d ^ 2) : ℕ) = 4 ^ (d ^ 2) := by
            rw [pow_mul]; norm_num
          exact_mod_cast h1.trans (h2.trans_eq h3)
        have hk_real : (k : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast hk_le
        have hpow_comb : (2 * R) ^ k * (2 * R) ^ (d ^ 2 - k) = (2 * R) ^ (d ^ 2) := by
          rw [← pow_add, Nat.add_sub_of_le hk_le]
        have h8R : (4 : ℝ) ^ (d ^ 2) * (2 * R) ^ (d ^ 2) = (8 * R) ^ (d ^ 2) := by
          rw [← mul_pow]; congr 1; ring
        calc ‖newtonElem (pairDiffPowerSum d s₁) k - newtonElem (pairDiffPowerSum d s₂) k‖ *
                ‖zhukovskyLoop n u‖ ^ (d ^ 2 - k)
            ≤ (2 * ε * (k : ℝ) * (Nat.choose (d ^ 2 + k) k : ℝ) * (2 * R) ^ k) *
                (2 * R) ^ (d ^ 2 - k) :=
              mul_le_mul he_k hpow_z (by positivity) (by positivity)
          _ = 2 * ε * (k : ℝ) * (Nat.choose (d ^ 2 + k) k : ℝ) *
                ((2 * R) ^ k * (2 * R) ^ (d ^ 2 - k)) := by ring
          _ = 2 * ε * ((k : ℝ) * ((Nat.choose (d ^ 2 + k) k : ℝ) * (2 * R) ^ (d ^ 2))) := by
              rw [hpow_comb]; ring
          _ ≤ 2 * ε * ((d : ℝ) ^ 2 * ((4 : ℝ) ^ (d ^ 2) * (2 * R) ^ (d ^ 2))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul hk_real
                (mul_le_mul_of_nonneg_right hch (by positivity)) (by positivity) (by positivity)
          _ = 2 * ε * ((d : ℝ) ^ 2) * (8 * R) ^ (d ^ 2) := by rw [h8R]; ring
    _ = ((d ^ 2 + 1 : ℕ) : ℝ) * (2 * ε * ((d : ℝ) ^ 2) * (8 * R) ^ (d ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 * (d : ℝ) ^ 2) * (2 * ε * ((d : ℝ) ^ 2) * (8 * R) ^ (d ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hd1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by
          have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos
          nlinarith
        push_cast; linarith
    _ = 4 * ε * ((d : ℝ) ^ 4) * (8 * R) ^ (d ^ 2) := by ring


/-! ## §3 General divisor Birkhoff–Szegő engine, Burnol good heights, and `O(m log²(m + S))` stabilization -/

/-- Restriction of a polynomial `P` along `zhukovskyLoop n` as an element of `C(UnitCircle, ℂ)`. -/
def polyZhukovskyBaseLoop (n : ℕ) (P : Polynomial ℂ) : C(HTGeometry.UnitCircle, ℂ) where
  toFun u := P.eval (zhukovskyLoop n u)
  continuous_toFun := P.continuous.comp (zhukovskyLoop n).continuous

/-- Squared Zhukovsky loop `(P ∘ J_n)²` on `UnitCircle`. -/
def polyZhukovskyLaurentLoop (n : ℕ) (P : Polynomial ℂ) : C(HTGeometry.UnitCircle, ℂ) :=
  polyZhukovskyBaseLoop n P ^ 2

@[simp]
theorem polyZhukovskyBaseLoop_apply (n : ℕ) (P : Polynomial ℂ) (u : HTGeometry.UnitCircle) :
    polyZhukovskyBaseLoop n P u = P.eval (zhukovskyLoop n u) :=
  rfl

@[simp]
theorem polyZhukovskyLaurentLoop_apply (n : ℕ) (P : Polynomial ℂ) (u : HTGeometry.UnitCircle) :
    polyZhukovskyLaurentLoop n P u = (P.eval (zhukovskyLoop n u)) ^ 2 := by
  rw [polyZhukovskyLaurentLoop, ContinuousMap.coe_pow, Pi.pow_apply, polyZhukovskyBaseLoop_apply]

/-- Nonvanishing of `(P ∘ J_n)²` on `UnitCircle` forces ellipse nondegeneracy of every positive-order
root difference `z - w` (`z, w ∈ Z`). -/
theorem ellipse_nondegenerate_of_prod_eval_ne_zero {P : Polynomial ℂ} {Z : Finset ℂ}
    {mult : ℂ → ℕ} {n : ℕ}
    (heval : ∀ x : ℂ, P.eval x = ∏ z ∈ Z, ∏ w ∈ Z, (x - (z - w)) ^ (mult z * mult w))
    (hmult_pos : ∀ z ∈ Z, 0 < mult z)
    (hnz : ∀ u : HTGeometry.UnitCircle, (P.eval (zhukovskyLoop n u)) ^ 2 ≠ 0) :
    ∀ z ∈ Z, ∀ w ∈ Z, zhukovskyEllipseForm n (z - w) ≠ 1 := by
  intro z hz w hw hform1
  obtain ⟨u, hu⟩ := exists_unitCircle_zhukovskyLoop_eq hform1
  have hP0 : P.eval (zhukovskyLoop n u) = 0 := by
    rw [heval]
    refine Finset.prod_eq_zero hz ?_
    refine Finset.prod_eq_zero hw ?_
    rw [hu, sub_self, zero_pow (Nat.mul_pos (hmult_pos z hz) (hmult_pos w hw)).ne']
  apply hnz u
  rw [hP0, zero_pow two_ne_zero]

/-- **General divisor Birkhoff–Zhukovsky–Szegő factorization theorem.**
For any polynomial `P` whose evaluation factors as `∏_{z, w ∈ Z} (x - (z - w))^{mult z * mult w}`
with `zhukovskyEllipseForm n (z - w) ≠ 1` for all `z, w ∈ Z`, both `wienerHopfLift ((P ∘ J_n)²)` and
`wienerHopfLift (unitNormalizeSymbol ((P ∘ J_n)²))` factor as `A * cayleyWienerHopf ^ (2 * k) * B`
with `L²(ℝ)` units `A, B` and exact winding / Fredholm index `2 * k`. -/
theorem exists_birkhoffSzego_of_prod_eval {P : Polynomial ℂ} {Z : Finset ℂ}
    {mult : ℂ → ℕ} {n : ℕ}
    (heval : ∀ x : ℂ, P.eval x = ∏ z ∈ Z, ∏ w ∈ Z, (x - (z - w)) ^ (mult z * mult w))
    (hellipse : ∀ z ∈ Z, ∀ w ∈ Z, zhukovskyEllipseForm n (z - w) ≠ 1) :
    let k : ℕ := ∑ z ∈ Z, ∑ w ∈ Z,
      mult z * mult w * (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0)
    let Λ := polyZhukovskyLaurentLoop n P
    let T_op := HTGeometry.wienerHopfLift (unitNormalizeSymbol Λ)
    (∀ u : HTGeometry.UnitCircle, P.eval (zhukovskyLoop n u) ≠ 0) ∧
    _root_.RHTower.windingNumber
      (fun θ => (P.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) =
        (2 * (k : ℤ)) ∧
    ∃ g₀ h₀ : Polynomial ℂ,
      IsOuterPolynomial g₀ ∧ IsOuterPolynomial h₀ ∧
      polyZhukovskyBaseLoop n P =
        circlePoly g₀ * HTGeometry.circleCoord ^ k * star (circlePoly h₀) ∧
      Λ = circlePoly (g₀ ^ 2) * HTGeometry.circleCoord ^ (2 * k) * star (circlePoly (h₀ ^ 2)) ∧
      HTGeometry.fredholmIndex T_op = (2 * (k : ℤ)) ∧
      (IsUnit (HTGeometry.wienerHopfLift Λ) ↔ k = 0) ∧
      (IsUnit T_op ↔ k = 0) := by
  intro k Λ T_op
  have hpair : ∀ p : {p : ℂ × ℂ // p ∈ Z ×ˢ Z},
      ∃ g_p h_p : Polynomial ℂ, IsOuterPolynomial g_p ∧ IsOuterPolynomial h_p ∧
        let e : ℕ := if zhukovskyEllipseForm n (p.1.1 - p.1.2) < 1 then 1 else 0
        ∀ u : HTGeometry.UnitCircle,
          zhukovskyLoop n u - (p.1.1 - p.1.2) =
            circlePoly g_p u * (HTGeometry.circleCoord ^ e) u * star (circlePoly h_p u) := by
    intro p
    obtain ⟨hz, hw⟩ := Finset.mem_product.mp p.2
    by_cases hlt : zhukovskyEllipseForm n (p.1.1 - p.1.2) < 1
    · obtain ⟨q, hq_out, hq_eq⟩ := exists_zhukovsky_outer_factorization_of_lt_one hlt
      refine ⟨1, q, isOuterPolynomial_one, hq_out, fun u => ?_⟩
      simp only [if_pos hlt, pow_one, circlePoly_one, ContinuousMap.one_apply, one_mul]
      exact hq_eq u
    · have hgt : 1 < zhukovskyEllipseForm n (p.1.1 - p.1.2) :=
        lt_of_le_of_ne (not_lt.mp hlt) (hellipse p.1.1 hz p.1.2 hw).symm
      obtain ⟨g_p, h_p, hg_out, hh_out, hgh_eq⟩ :=
        exists_zhukovsky_outer_factorization_of_gt_one hgt
      refine ⟨g_p, h_p, hg_out, hh_out, fun u => ?_⟩
      simp only [if_neg hlt, pow_zero, ContinuousMap.one_apply, mul_one]
      exact hgh_eq u
  choose gF hF hgF hhF hpair_eq using hpair
  let S := (Z ×ˢ Z).attach
  let mPair : {p : ℂ × ℂ // p ∈ Z ×ˢ Z} → ℕ := fun p => mult p.1.1 * mult p.1.2
  let deg : {p : ℂ × ℂ // p ∈ Z ×ˢ Z} → ℕ :=
    fun p => if zhukovskyEllipseForm n (p.1.1 - p.1.2) < 1 then 1 else 0
  let g₀ : Polynomial ℂ := ∏ p ∈ S, gF p ^ mPair p
  let h₀ : Polynomial ℂ := ∏ p ∈ S, hF p ^ mPair p
  have hg₀_out : IsOuterPolynomial g₀ := by
    dsimp only [g₀]
    induction S using Finset.induction_on with
    | empty => simpa using isOuterPolynomial_one
    | @insert p s hp ih =>
        rw [Finset.prod_insert hp]
        exact isOuterPolynomial_mul (isOuterPolynomial_pow (hgF p) _) ih
  have hh₀_out : IsOuterPolynomial h₀ := by
    dsimp only [h₀]
    induction S using Finset.induction_on with
    | empty => simpa using isOuterPolynomial_one
    | @insert p s hp ih =>
        rw [Finset.prod_insert hp]
        exact isOuterPolynomial_mul (isOuterPolynomial_pow (hhF p) _) ih
  have hk_sum : ∑ p ∈ S, mPair p * deg p = k := by
    dsimp only [S, mPair, deg, k]
    rw [Finset.sum_attach (Z ×ˢ Z)
      (fun x : ℂ × ℂ => mult x.1 * mult x.2 *
        (if zhukovskyEllipseForm n (x.1 - x.2) < 1 then 1 else 0)),
      Finset.sum_product]
  have hbase_eq : polyZhukovskyBaseLoop n P =
      circlePoly g₀ * HTGeometry.circleCoord ^ k * star (circlePoly h₀) := by
    ext u
    change P.eval (zhukovskyLoop n u) =
      circlePoly g₀ u * (HTGeometry.circleCoord ^ k) u * star (circlePoly h₀ u)
    rw [heval (zhukovskyLoop n u), ← Finset.prod_product',
      ← Finset.prod_attach (Z ×ˢ Z)
        (fun x : ℂ × ℂ => (zhukovskyLoop n u - (x.1 - x.2)) ^ (mult x.1 * mult x.2))]
    have hterm : ∀ p ∈ S,
        (zhukovskyLoop n u - (p.1.1 - p.1.2)) ^ mPair p =
          (gF p ^ mPair p).eval (u : ℂ) *
            ((HTGeometry.circleCoord u) ^ (mPair p * deg p)) *
            star ((hF p ^ mPair p).eval (u : ℂ)) := by
      intro p _
      rw [hpair_eq p u, mul_pow, mul_pow, Polynomial.eval_pow, Polynomial.eval_pow, star_pow]
      congr 2
      rw [ContinuousMap.coe_pow, Pi.pow_apply, ← pow_mul, mul_comm (deg p) (mPair p)]
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hg_eval : (∏ p ∈ S, (gF p ^ mPair p).eval (u : ℂ)) = circlePoly g₀ u := by
      rw [circlePoly_apply]; dsimp only [g₀]; rw [Polynomial.eval_prod]
    have hh_eval : (∏ p ∈ S, star ((hF p ^ mPair p).eval (u : ℂ))) = star (circlePoly h₀ u) := by
      rw [circlePoly_apply]; dsimp only [h₀]; rw [Polynomial.eval_prod]
      change _ = (starRingEnd ℂ) (∏ p ∈ S, (hF p ^ mPair p).eval (u : ℂ))
      rw [map_prod]; rfl
    have hcoord_eval : (∏ p ∈ S, (HTGeometry.circleCoord u) ^ (mPair p * deg p)) =
        (HTGeometry.circleCoord ^ k) u := by
      have hpow_sum : ∀ (s : Finset {p : ℂ × ℂ // p ∈ Z ×ˢ Z}),
          (∏ p ∈ s, (HTGeometry.circleCoord u) ^ (mPair p * deg p)) =
            (HTGeometry.circleCoord u) ^ (∑ p ∈ s, mPair p * deg p) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | @insert p s hp ih => rw [Finset.prod_insert hp, Finset.sum_insert hp, pow_add, ih]
      rw [hpow_sum S, hk_sum, ContinuousMap.coe_pow, Pi.pow_apply]
    rw [hg_eval, hh_eval, hcoord_eval]
  have hlaurent_eq : Λ =
      circlePoly (g₀ ^ 2) * HTGeometry.circleCoord ^ (2 * k) * star (circlePoly (h₀ ^ 2)) := by
    dsimp only [Λ, polyZhukovskyLaurentLoop]
    rw [hbase_eq, circlePoly_pow, circlePoly_pow, star_pow]
    ext u
    simp only [ContinuousMap.coe_pow, ContinuousMap.coe_mul, ContinuousMap.star_apply,
      Pi.pow_apply, Pi.mul_apply]
    rw [pow_mul (HTGeometry.circleCoord u) 2 k]
    ring
  have hP_nz : ∀ u : HTGeometry.UnitCircle, P.eval (zhukovskyLoop n u) ≠ 0 := by
    intro u
    change polyZhukovskyBaseLoop n P u ≠ 0
    rw [hbase_eq]
    simp only [ContinuousMap.coe_mul, ContinuousMap.coe_pow, ContinuousMap.star_apply,
      Pi.mul_apply, Pi.pow_apply, circlePoly_apply]
    have hu_ne : (u : ℂ) ≠ 0 := by
      intro h0
      have h1 := HTGeometry.norm_coe_unitCircle u
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    exact mul_ne_zero
      (mul_ne_zero (hg₀_out (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le) (pow_ne_zero k hu_ne))
      (star_ne_zero.mpr (hh₀_out (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le))
  have hloop_nz : ∀ u : HTGeometry.UnitCircle, Λ u ≠ 0 := fun u => by
    rw [polyZhukovskyLaurentLoop_apply]
    exact pow_ne_zero 2 (hP_nz u)
  let G2 := g₀ ^ 2
  let H2 := h₀ ^ 2
  have hG2_out : IsOuterPolynomial G2 := isOuterPolynomial_pow hg₀_out 2
  have hH2_out : IsOuterPolynomial H2 := isOuterPolynomial_pow hh₀_out 2
  let A_un := HTGeometry.wienerHopfLift (circlePoly G2)
  let A_un_inv := HTGeometry.wienerHopfLift (circlePolyInv G2 hG2_out)
  let B_un := HTGeometry.wienerHopfLift (star (circlePoly H2))
  let B_un_inv := HTGeometry.wienerHopfLift (star (circlePolyInv H2 hH2_out))
  have hA_un_R : A_un * A_un_inv = 1 := by
    dsimp only [A_un, A_un_inv]
    rw [← wienerHopfLift_hardyPlus_mul (hankelPlus_circlePoly_eq_zero G2),
      circlePoly_mul_inv, HTGeometry.wienerHopfLift_one]
  have hA_un_L : A_un_inv * A_un = 1 := by
    dsimp only [A_un, A_un_inv]
    rw [← wienerHopfLift_hardyPlus_mul (hankelPlus_circlePolyInv_eq_zero G2 hG2_out),
      circlePolyInv_mul, HTGeometry.wienerHopfLift_one]
  have hB_un_R : B_un * B_un_inv = 1 := by
    dsimp only [B_un, B_un_inv]
    rw [← wienerHopfLift_mul_star_hardyPlus _ (hankelPlus_circlePolyInv_eq_zero H2 hH2_out),
      ← star_mul, circlePolyInv_mul, star_one, HTGeometry.wienerHopfLift_one]
  have hB_un_L : B_un_inv * B_un = 1 := by
    dsimp only [B_un, B_un_inv]
    rw [← wienerHopfLift_mul_star_hardyPlus _ (hankelPlus_circlePoly_eq_zero H2),
      ← star_mul, circlePoly_mul_inv, star_one, HTGeometry.wienerHopfLift_one]
  have hWH_un_eq : HTGeometry.wienerHopfLift Λ =
      A_un * HTGeometry.cayleyWienerHopf ^ (2 * k) * B_un := by
    rw [hlaurent_eq, mul_assoc (circlePoly G2),
      wienerHopfLift_hardyPlus_mul (hankelPlus_circlePoly_eq_zero G2),
      wienerHopfLift_mul_star_hardyPlus _ (hankelPlus_circlePoly_eq_zero H2),
      HTGeometry.wienerHopfLift_circleCoord_pow, ← mul_assoc]
  obtain ⟨_, _, _, _, hunit_un⟩ :=
    fredholm_and_kernel_of_sandwiched_cayleyPow hA_un_R hA_un_L hB_un_R hB_un_L (2 * k)
  rw [← hWH_un_eq] at hunit_un
  let A_nm := HTGeometry.wienerHopfLift (circlePoly g₀) *
    HTGeometry.wienerHopfLift (circlePolyInv h₀ hh₀_out)
  let A_nm_inv := HTGeometry.wienerHopfLift (circlePoly h₀) *
    HTGeometry.wienerHopfLift (circlePolyInv g₀ hg₀_out)
  let B_nm := HTGeometry.wienerHopfLift (star (circlePolyInv g₀ hg₀_out)) *
    HTGeometry.wienerHopfLift (star (circlePoly h₀))
  let B_nm_inv := HTGeometry.wienerHopfLift (star (circlePolyInv h₀ hh₀_out)) *
    HTGeometry.wienerHopfLift (star (circlePoly g₀))
  have hg_R : HTGeometry.wienerHopfLift (circlePoly g₀) *
      HTGeometry.wienerHopfLift (circlePolyInv g₀ hg₀_out) = 1 := by
    rw [← wienerHopfLift_hardyPlus_mul (hankelPlus_circlePoly_eq_zero g₀),
      circlePoly_mul_inv, HTGeometry.wienerHopfLift_one]
  have hg_L : HTGeometry.wienerHopfLift (circlePolyInv g₀ hg₀_out) *
      HTGeometry.wienerHopfLift (circlePoly g₀) = 1 := by
    rw [← wienerHopfLift_hardyPlus_mul (hankelPlus_circlePolyInv_eq_zero g₀ hg₀_out),
      circlePolyInv_mul, HTGeometry.wienerHopfLift_one]
  have hh_R : HTGeometry.wienerHopfLift (circlePoly h₀) *
      HTGeometry.wienerHopfLift (circlePolyInv h₀ hh₀_out) = 1 := by
    rw [← wienerHopfLift_hardyPlus_mul (hankelPlus_circlePoly_eq_zero h₀),
      circlePoly_mul_inv, HTGeometry.wienerHopfLift_one]
  have hh_L : HTGeometry.wienerHopfLift (circlePolyInv h₀ hh₀_out) *
      HTGeometry.wienerHopfLift (circlePoly h₀) = 1 := by
    rw [← wienerHopfLift_hardyPlus_mul (hankelPlus_circlePolyInv_eq_zero h₀ hh₀_out),
      circlePolyInv_mul, HTGeometry.wienerHopfLift_one]
  have hsg_R : HTGeometry.wienerHopfLift (star (circlePoly g₀)) *
      HTGeometry.wienerHopfLift (star (circlePolyInv g₀ hg₀_out)) = 1 := by
    rw [← wienerHopfLift_mul_star_hardyPlus _ (hankelPlus_circlePolyInv_eq_zero g₀ hg₀_out),
      ← star_mul, circlePolyInv_mul, star_one, HTGeometry.wienerHopfLift_one]
  have hsg_L : HTGeometry.wienerHopfLift (star (circlePolyInv g₀ hg₀_out)) *
      HTGeometry.wienerHopfLift (star (circlePoly g₀)) = 1 := by
    rw [← wienerHopfLift_mul_star_hardyPlus _ (hankelPlus_circlePoly_eq_zero g₀),
      ← star_mul, circlePoly_mul_inv, star_one, HTGeometry.wienerHopfLift_one]
  have hsh_R : HTGeometry.wienerHopfLift (star (circlePoly h₀)) *
      HTGeometry.wienerHopfLift (star (circlePolyInv h₀ hh₀_out)) = 1 := by
    rw [← wienerHopfLift_mul_star_hardyPlus _ (hankelPlus_circlePolyInv_eq_zero h₀ hh₀_out),
      ← star_mul, circlePolyInv_mul, star_one, HTGeometry.wienerHopfLift_one]
  have hsh_L : HTGeometry.wienerHopfLift (star (circlePolyInv h₀ hh₀_out)) *
      HTGeometry.wienerHopfLift (star (circlePoly h₀)) = 1 := by
    rw [← wienerHopfLift_mul_star_hardyPlus _ (hankelPlus_circlePoly_eq_zero h₀),
      ← star_mul, circlePoly_mul_inv, star_one, HTGeometry.wienerHopfLift_one]
  have hA_nm_R : A_nm * A_nm_inv = 1 := by
    dsimp only [A_nm, A_nm_inv]
    calc (HTGeometry.wienerHopfLift (circlePoly g₀) *
            HTGeometry.wienerHopfLift (circlePolyInv h₀ hh₀_out)) *
          (HTGeometry.wienerHopfLift (circlePoly h₀) *
            HTGeometry.wienerHopfLift (circlePolyInv g₀ hg₀_out))
        = HTGeometry.wienerHopfLift (circlePoly g₀) *
            (HTGeometry.wienerHopfLift (circlePolyInv h₀ hh₀_out) *
              HTGeometry.wienerHopfLift (circlePoly h₀)) *
            HTGeometry.wienerHopfLift (circlePolyInv g₀ hg₀_out) := by noncomm_ring
      _ = 1 := by rw [hh_L, mul_one, hg_R]
  have hA_nm_L : A_nm_inv * A_nm = 1 := by
    dsimp only [A_nm, A_nm_inv]
    calc (HTGeometry.wienerHopfLift (circlePoly h₀) *
            HTGeometry.wienerHopfLift (circlePolyInv g₀ hg₀_out)) *
          (HTGeometry.wienerHopfLift (circlePoly g₀) *
            HTGeometry.wienerHopfLift (circlePolyInv h₀ hh₀_out))
        = HTGeometry.wienerHopfLift (circlePoly h₀) *
            (HTGeometry.wienerHopfLift (circlePolyInv g₀ hg₀_out) *
              HTGeometry.wienerHopfLift (circlePoly g₀)) *
            HTGeometry.wienerHopfLift (circlePolyInv h₀ hh₀_out) := by noncomm_ring
      _ = 1 := by rw [hg_L, mul_one, hh_R]
  have hB_nm_R : B_nm * B_nm_inv = 1 := by
    dsimp only [B_nm, B_nm_inv]
    calc (HTGeometry.wienerHopfLift (star (circlePolyInv g₀ hg₀_out)) *
            HTGeometry.wienerHopfLift (star (circlePoly h₀))) *
          (HTGeometry.wienerHopfLift (star (circlePolyInv h₀ hh₀_out)) *
            HTGeometry.wienerHopfLift (star (circlePoly g₀)))
        = HTGeometry.wienerHopfLift (star (circlePolyInv g₀ hg₀_out)) *
            (HTGeometry.wienerHopfLift (star (circlePoly h₀)) *
              HTGeometry.wienerHopfLift (star (circlePolyInv h₀ hh₀_out))) *
            HTGeometry.wienerHopfLift (star (circlePoly g₀)) := by noncomm_ring
      _ = 1 := by rw [hsh_R, mul_one, hsg_L]
  have hB_nm_L : B_nm_inv * B_nm = 1 := by
    dsimp only [B_nm, B_nm_inv]
    calc (HTGeometry.wienerHopfLift (star (circlePolyInv h₀ hh₀_out)) *
            HTGeometry.wienerHopfLift (star (circlePoly g₀))) *
          (HTGeometry.wienerHopfLift (star (circlePolyInv g₀ hg₀_out)) *
            HTGeometry.wienerHopfLift (star (circlePoly h₀)))
        = HTGeometry.wienerHopfLift (star (circlePolyInv h₀ hh₀_out)) *
            (HTGeometry.wienerHopfLift (star (circlePoly g₀)) *
              HTGeometry.wienerHopfLift (star (circlePolyInv g₀ hg₀_out))) *
            HTGeometry.wienerHopfLift (star (circlePoly h₀)) := by noncomm_ring
      _ = 1 := by rw [hsg_R, mul_one, hsh_L]
  have hsym_eq : unitNormalizeSymbol Λ =
      circlePoly g₀ *
        (circlePolyInv h₀ hh₀_out *
          ((HTGeometry.circleCoord ^ (2 * k) * star (circlePolyInv g₀ hg₀_out)) *
            star (circlePoly h₀))) := by
    ext u
    rw [unitNormalizeSymbol_apply_of_ne_zero hloop_nz, hlaurent_eq]
    simp only [ContinuousMap.mul_apply, ContinuousMap.pow_apply, ContinuousMap.star_apply,
      circlePoly_apply, circlePolyInv_apply, circlePoly_pow, star_pow, star_inv₀]
    set gu := g₀.eval (u : ℂ)
    set hu := h₀.eval (u : ℂ)
    have hgu_ne : gu ≠ 0 := hg₀_out (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le
    have hhu_ne : hu ≠ 0 := hh₀_out (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le
    have hnorm_eq : (‖gu ^ 2 * (HTGeometry.circleCoord u) ^ (2 * k) * (star hu) ^ 2‖ : ℂ) =
        (gu * star gu) * (hu * star hu) := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, Complex.star_def, Complex.norm_conj,
        show ‖HTGeometry.circleCoord u‖ = 1 from HTGeometry.norm_coe_unitCircle u,
        one_pow, mul_one, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow,
        ← Complex.mul_conj', ← Complex.mul_conj']
    rw [hnorm_eq]
    have hsg_ne : star gu ≠ 0 := star_ne_zero.mpr hgu_ne
    have hsh_ne : star hu ≠ 0 := star_ne_zero.mpr hhu_ne
    field_simp [hgu_ne, hhu_ne, hsg_ne, hsh_ne]
  have hWH_nm_eq : T_op = A_nm * HTGeometry.cayleyWienerHopf ^ (2 * k) * B_nm := by
    dsimp only [T_op, A_nm, B_nm]
    rw [hsym_eq,
      wienerHopfLift_hardyPlus_mul (hankelPlus_circlePoly_eq_zero g₀),
      wienerHopfLift_hardyPlus_mul (hankelPlus_circlePolyInv_eq_zero h₀ hh₀_out),
      wienerHopfLift_mul_star_hardyPlus _ (hankelPlus_circlePoly_eq_zero h₀),
      wienerHopfLift_mul_star_hardyPlus _ (hankelPlus_circlePolyInv_eq_zero g₀ hg₀_out),
      HTGeometry.wienerHopfLift_circleCoord_pow]
    noncomm_ring
  obtain ⟨_, _, _, hind_nm, hunit_nm⟩ :=
    fredholm_and_kernel_of_sandwiched_cayleyPow hA_nm_R hA_nm_L hB_nm_R hB_nm_L (2 * k)
  rw [← hWH_nm_eq] at hind_nm hunit_nm
  have hind_int : HTGeometry.fredholmIndex T_op = (2 * (k : ℤ)) := by
    push_cast at hind_nm; exact hind_nm
  have hwind : _root_.RHTower.windingNumber
      (fun θ => (P.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) =
      (2 * (k : ℤ)) := by
    have h1 := fredholmIndex_wienerHopfLift_unitNormalizeSymbol Λ
    rw [circleWinding_unitNormalizeSymbol_of_ne_zero hloop_nz] at h1
    exact h1.symm.trans hind_int
  have hk2_iff : (2 * k = 0) ↔ k = 0 := by omega
  exact ⟨hP_nz, hwind, g₀, h₀, hg₀_out, hh₀_out, hbase_eq, hlaurent_eq, hind_int,
    hunit_un.trans hk2_iff, hunit_nm.trans hk2_iff⟩
