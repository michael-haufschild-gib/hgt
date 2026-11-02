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
  have hcast_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  have hcast_add : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast_sub, hcast_add]
  have hn7 : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set t : ℝ := (n : ℝ) - 1
  have ht6 : 6 ≤ t := by dsimp only [t]; linarith
  have ht_m1_pos : 0 < t - 1 := by linarith
  have ht_pos : 0 < t := by linarith
  have ht_p1_pos : 0 < t + 1 := by linarith
  have hsub_t : (n : ℝ) - 1 - 1 = t - 1 := rfl
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
    have ha1 : 1 ≤ a := le_add_of_nonneg_right (by positivity)
    have hb1 : 1 ≤ b := le_add_of_nonneg_right (by positivity)
    have hc1 : 1 ≤ c := le_add_of_nonneg_right (by positivity)
    linarith
  have hquad_id : 4 * (a ^ 2 - 2 * b ^ 2 + c ^ 2) =
      2 * (a - c) ^ 2 + 2 * (a - 2 * b + c) * (a + 2 * b + c) := by ring
  have hquad_ge : 16 / (n : ℝ) ^ 3 ≤ 4 * (a ^ 2 - 2 * b ^ 2 + c ^ 2) := by
    rw [hquad_id]
    have hmul : 2 * (2 / (n : ℝ) ^ 3) * 4 ≤ 2 * (a - 2 * b + c) * (a + 2 * b + c) := by
      have h1 : 2 * (2 / (n : ℝ) ^ 3) ≤ 2 * (a - 2 * b + c) := by linarith
      exact mul_le_mul h1 hsum_ge (by norm_num)
        ((by positivity : (0 : ℝ) ≤ 2 * (2 / (n : ℝ) ^ 3)).trans h1)
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
      have ha1 : m₁ + (k + 1) + 1 = m₁ + k + 1 + 1 := by omega
      have ha2 : m₁ + (k + 1) = m₁ + k + 1 := by omega
      rw [hsub] at hstep
      rw [ha1, ha2]
      linarith only [hκ, hstep, ih (by omega) hk_lt]

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
  set A := (Finset.Icc S₀ S_max).filter (fun n => |f n - 1| < κ / 4)
  by_contra hgt
  obtain ⟨n₁, h1, n₂, h2, n₃, h3, h12, h23⟩ :=
    exists_three_strict_mono_of_three_le_card (show 3 ≤ A.card by omega)
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
    simp only [not_exists, not_and, not_lt] at hex
    have hempty : (Finset.Icc S₀ S_max).filter
        (fun n => |zhukovskyEllipseForm n d - 1| < 1 / (8 * (S_max : ℝ) ^ 3)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro n hn hlt
      have hle := hex n hn
      have hsmall : 1 / (8 * (S_max : ℝ) ^ 3) < 1 / 2 := by
        have hS3 : (216 : ℝ) ≤ (S_max : ℝ) ^ 3 := by
          have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) hS_pos 3
          norm_num at hp
          exact hp
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        linarith
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
  have hex_good : ∃ n_star ∈ Finset.Icc S₀ S_max, n_star ∉ P.biUnion bad := by
    by_contra hall
    simp only [not_exists, not_and, Classical.not_not] at hall
    have hle := Finset.card_le_card hall
    omega
  obtain ⟨n_star, hn_Icc, hn_not_bad⟩ := hex_good
  refine ⟨n_star, hn_Icc, fun d hd => ?_⟩
  by_contra hlt
  exact hn_not_bad (Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_filter.mpr ⟨hn_Icc, not_le.mp hlt⟩⟩)

/-- **Quantitative Euclidean distance lower bound on `zhukovskyLoop n` from an ellipse-form gap.**
Whenever `0 < η ≤ 1` and `η ≤ |zhukovskyEllipseForm n d - 1|`, every point `u : UnitCircle` satisfies
`η / (7 * zhukovskyStage n) ≤ ‖zhukovskyLoop n u - d‖`. -/
theorem norm_zhukovskyLoop_sub_ge_of_ellipse_gap {n : ℕ} {d : ℂ} {η : ℝ}
    (_hη0 : 0 < η) (hη1 : η ≤ 1) (hgap : η ≤ |zhukovskyEllipseForm n d - 1|)
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
    have ha_pos : 0 < a := zhukovskyMajorAxis_pos n
    have hb_pos : 0 < b := zhukovskyMinorAxis_pos n
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
        have hnn : 0 ≤ z.im ^ 2 / b ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
        calc (z.re - 1 / 2) ^ 2 / a ^ 2
            ≤ (z.re - 1 / 2) ^ 2 / a ^ 2 + z.im ^ 2 / b ^ 2 := le_add_of_nonneg_right hnn
          _ = zhukovskyEllipseForm n z := rfl
          _ = 1 := hz_form
      have h2 : (z.re - 1 / 2) ^ 2 ≤ a ^ 2 := (div_le_one (sq_pos_of_pos ha_pos)).mp h1
      have h3 : |z.re - 1 / 2| ≤ |a| := sq_le_sq.mp h2
      rwa [abs_of_pos ha_pos] at h3
    have hz_im_le : |z.im| ≤ b := by
      have h1 : z.im ^ 2 / b ^ 2 ≤ 1 := by
        have hnn : 0 ≤ (z.re - 1 / 2) ^ 2 / a ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
        calc z.im ^ 2 / b ^ 2
            ≤ (z.re - 1 / 2) ^ 2 / a ^ 2 + z.im ^ 2 / b ^ 2 := le_add_of_nonneg_left hnn
          _ = zhukovskyEllipseForm n z := rfl
          _ = 1 := hz_form
      have h2 : z.im ^ 2 ≤ b ^ 2 := (div_le_one (sq_pos_of_pos hb_pos)).mp h1
      have h3 : |z.im| ≤ |b| := sq_le_sq.mp h2
      rwa [abs_of_pos hb_pos] at h3
    have hδ_sixth : δ ≤ 1 / 6 := hsmall.le.trans (one_div_le_one_div_of_le (by norm_num) hs6)
    have hre_sum : |(z.re - 1 / 2) + (d.re - 1 / 2)| ≤ 7 / 6 := by
      have h1 : |d.re - 1 / 2| ≤ |z.re - 1 / 2| + |(z.re - 1 / 2) - (d.re - 1 / 2)| := by
        calc |d.re - 1 / 2|
            = |(z.re - 1 / 2) - ((z.re - 1 / 2) - (d.re - 1 / 2))| := by ring_nf
          _ ≤ |z.re - 1 / 2| + |(z.re - 1 / 2) - (d.re - 1 / 2)| := abs_sub _ _
      have h2 := abs_add_le (z.re - 1 / 2) (d.re - 1 / 2)
      linarith
    have him_sum : |z.im + d.im| ≤ 3 / s := by
      have h1 : |d.im| ≤ |z.im| + |z.im - d.im| := by
        calc |d.im| = |z.im - (z.im - d.im)| := by ring_nf
          _ ≤ |z.im| + |z.im - d.im| := abs_sub _ _
      have h2 := abs_add_le z.im d.im
      rw [hb_eq] at hz_im_le
      have h3 : 1 / s + 1 / s + 1 / s = 3 / s := by ring
      linarith
    have hre_term : |(z.re - 1 / 2) ^ 2 - (d.re - 1 / 2) ^ 2| / a ^ 2 ≤ δ * (168 / 25) := by
      have hf : (z.re - 1 / 2) ^ 2 - (d.re - 1 / 2) ^ 2 =
          ((z.re - 1 / 2) - (d.re - 1 / 2)) * ((z.re - 1 / 2) + (d.re - 1 / 2)) := by ring
      have ha_sq : (25 / 144 : ℝ) ≤ a ^ 2 := by nlinarith
      rw [hf, abs_mul, div_le_iff₀ (sq_pos_of_pos ha_pos)]
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
        _ = δ * (3 * s) := by field_simp [hs_pos.ne']
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
      rw [abs_div, abs_div, abs_of_pos (sq_pos_of_pos (zhukovskyMajorAxis_pos n)),
        abs_of_pos (sq_pos_of_pos (zhukovskyMinorAxis_pos n))] at htri
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
      · simp only [Nat.choose_zero_right]
        exact Nat.one_le_two_pow
      · rw [Nat.choose_succ_succ, pow_succ]
        change n.choose k + n.choose (k + 1) ≤ 2 ^ n * 2
        linarith [ih k, ih (k + 1)]

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

private lemma exists_unitCircle_zhukovskyLoop_eq {n : ℕ} {d : ℂ}
    (hform : zhukovskyEllipseForm n d = 1) :
    ∃ u : HTGeometry.UnitCircle, zhukovskyLoop n u = d := by
  set a := zhukovskyMajorAxis n
  set b := zhukovskyMinorAxis n
  have ha_ne : a ≠ 0 := (zhukovskyMajorAxis_pos n).ne'
  have hb_ne : b ≠ 0 := (zhukovskyMinorAxis_pos n).ne'
  let ζ : ℂ := (((d.re - 1 / 2) / a : ℝ) : ℂ) + (((d.im / b : ℝ) : ℂ) * I)
  have hζ_norm : ‖ζ‖ = 1 := by
    have hsq : ‖ζ‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      dsimp only [ζ]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
      unfold zhukovskyEllipseForm at hform
      dsimp only [a, b]
      linarith [div_pow (d.re - 1 / 2) a 2, div_pow d.im b 2]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) two_ne_zero).mp hsq
  let u : HTGeometry.UnitCircle := ⟨ζ, mem_sphere_zero_iff_norm.mpr hζ_norm⟩
  refine ⟨u, ?_⟩
  have hu_inv : ζ⁻¹ = star ζ := unitCircle_inv_eq_star u
  have hmaj := zhukovskyAxis_major_identity n
  have hmin := zhukovskyAxis_minor_identity n
  have hζ_star : star ζ = (((d.re - 1 / 2) / a : ℝ) : ℂ) - (((d.im / b : ℝ) : ℂ) * I) := by
    dsimp only [ζ]
    simp [sub_eq_add_neg]
  change (1 / 2 : ℂ) + ((zhukovskyFocal n : ℂ) / 2) *
    ((zhukovskyRadius n : ℂ) * ζ + ((zhukovskyRadius n : ℂ) * ζ)⁻¹) = d
  rw [mul_inv, hu_inv, hζ_star, ← Complex.ofReal_inv]
  dsimp only [ζ]
  have hmaj_re : (zhukovskyFocal n / 2) * (zhukovskyRadius n + (zhukovskyRadius n)⁻¹) *
      ((d.re - 1 / 2) / a) = d.re - 1 / 2 := by
    rw [hmaj]; exact mul_div_cancel₀ _ ha_ne
  have hmin_im : (zhukovskyFocal n / 2) * (zhukovskyRadius n - (zhukovskyRadius n)⁻¹) *
      (d.im / b) = d.im := by
    rw [hmin]; exact mul_div_cancel₀ _ hb_ne
  calc (1 / 2 : ℂ) + ((zhukovskyFocal n : ℂ) / 2) *
        ((zhukovskyRadius n : ℂ) *
            ((((d.re - 1 / 2) / a : ℝ) : ℂ) + ((d.im / b : ℝ) : ℂ) * I) +
          (((zhukovskyRadius n)⁻¹ : ℝ) : ℂ) *
            ((((d.re - 1 / 2) / a : ℝ) : ℂ) - ((d.im / b : ℝ) : ℂ) * I))
      = (((1 / 2 + (zhukovskyFocal n / 2) * (zhukovskyRadius n + (zhukovskyRadius n)⁻¹) *
          ((d.re - 1 / 2) / a) : ℝ) : ℂ)) +
        ((((zhukovskyFocal n / 2) * (zhukovskyRadius n - (zhukovskyRadius n)⁻¹) *
          (d.im / b) : ℝ) : ℂ)) * I := by
          push_cast; ring
    _ = ((d.re : ℝ) : ℂ) + ((d.im : ℝ) : ℂ) * I := by
          rw [hmaj_re, hmin_im]
          congr 1; push_cast; ring
    _ = d := Complex.re_add_im d

private lemma wienerHopfLift_hardyPlus_mul' {U : C(HTGeometry.UnitCircle, ℂ)}
    (hU : HTGeometry.hankelPlus U = 0) (V : C(HTGeometry.UnitCircle, ℂ)) :
    HTGeometry.wienerHopfLift (U * V) =
      HTGeometry.wienerHopfLift U * HTGeometry.wienerHopfLift V := by
  rw [HTGeometry.wienerHopfLift_mul, hU, zero_mul, sub_zero]

private lemma wienerHopfLift_mul_star_hardyPlus' (U : C(HTGeometry.UnitCircle, ℂ))
    {V : C(HTGeometry.UnitCircle, ℂ)} (hV : HTGeometry.hankelPlus V = 0) :
    HTGeometry.wienerHopfLift (U * star V) =
      HTGeometry.wienerHopfLift U * HTGeometry.wienerHopfLift (star V) := by
  rw [HTGeometry.wienerHopfLift_mul, HTGeometry.hankelMinus_star, hV, star_zero, mul_zero, sub_zero]

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
    rw [← wienerHopfLift_hardyPlus_mul' (hankelPlus_circlePoly_eq_zero G2),
      circlePoly_mul_inv, HTGeometry.wienerHopfLift_one]
  have hA_un_L : A_un_inv * A_un = 1 := by
    dsimp only [A_un, A_un_inv]
    rw [← wienerHopfLift_hardyPlus_mul' (hankelPlus_circlePolyInv_eq_zero G2 hG2_out),
      circlePolyInv_mul, HTGeometry.wienerHopfLift_one]
  have hB_un_R : B_un * B_un_inv = 1 := by
    dsimp only [B_un, B_un_inv]
    rw [← wienerHopfLift_mul_star_hardyPlus' _ (hankelPlus_circlePolyInv_eq_zero H2 hH2_out),
      ← star_mul, circlePolyInv_mul, star_one, HTGeometry.wienerHopfLift_one]
  have hB_un_L : B_un_inv * B_un = 1 := by
    dsimp only [B_un, B_un_inv]
    rw [← wienerHopfLift_mul_star_hardyPlus' _ (hankelPlus_circlePoly_eq_zero H2),
      ← star_mul, circlePoly_mul_inv, star_one, HTGeometry.wienerHopfLift_one]
  have hWH_un_eq : HTGeometry.wienerHopfLift Λ =
      A_un * HTGeometry.cayleyWienerHopf ^ (2 * k) * B_un := by
    rw [hlaurent_eq, mul_assoc (circlePoly G2),
      wienerHopfLift_hardyPlus_mul' (hankelPlus_circlePoly_eq_zero G2),
      wienerHopfLift_mul_star_hardyPlus' _ (hankelPlus_circlePoly_eq_zero H2),
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
    rw [← wienerHopfLift_hardyPlus_mul' (hankelPlus_circlePoly_eq_zero g₀),
      circlePoly_mul_inv, HTGeometry.wienerHopfLift_one]
  have hg_L : HTGeometry.wienerHopfLift (circlePolyInv g₀ hg₀_out) *
      HTGeometry.wienerHopfLift (circlePoly g₀) = 1 := by
    rw [← wienerHopfLift_hardyPlus_mul' (hankelPlus_circlePolyInv_eq_zero g₀ hg₀_out),
      circlePolyInv_mul, HTGeometry.wienerHopfLift_one]
  have hh_R : HTGeometry.wienerHopfLift (circlePoly h₀) *
      HTGeometry.wienerHopfLift (circlePolyInv h₀ hh₀_out) = 1 := by
    rw [← wienerHopfLift_hardyPlus_mul' (hankelPlus_circlePoly_eq_zero h₀),
      circlePoly_mul_inv, HTGeometry.wienerHopfLift_one]
  have hh_L : HTGeometry.wienerHopfLift (circlePolyInv h₀ hh₀_out) *
      HTGeometry.wienerHopfLift (circlePoly h₀) = 1 := by
    rw [← wienerHopfLift_hardyPlus_mul' (hankelPlus_circlePolyInv_eq_zero h₀ hh₀_out),
      circlePolyInv_mul, HTGeometry.wienerHopfLift_one]
  have hsg_R : HTGeometry.wienerHopfLift (star (circlePoly g₀)) *
      HTGeometry.wienerHopfLift (star (circlePolyInv g₀ hg₀_out)) = 1 := by
    rw [← wienerHopfLift_mul_star_hardyPlus' _ (hankelPlus_circlePolyInv_eq_zero g₀ hg₀_out),
      ← star_mul, circlePolyInv_mul, star_one, HTGeometry.wienerHopfLift_one]
  have hsg_L : HTGeometry.wienerHopfLift (star (circlePolyInv g₀ hg₀_out)) *
      HTGeometry.wienerHopfLift (star (circlePoly g₀)) = 1 := by
    rw [← wienerHopfLift_mul_star_hardyPlus' _ (hankelPlus_circlePoly_eq_zero g₀),
      ← star_mul, circlePoly_mul_inv, star_one, HTGeometry.wienerHopfLift_one]
  have hsh_R : HTGeometry.wienerHopfLift (star (circlePoly h₀)) *
      HTGeometry.wienerHopfLift (star (circlePolyInv h₀ hh₀_out)) = 1 := by
    rw [← wienerHopfLift_mul_star_hardyPlus' _ (hankelPlus_circlePolyInv_eq_zero h₀ hh₀_out),
      ← star_mul, circlePolyInv_mul, star_one, HTGeometry.wienerHopfLift_one]
  have hsh_L : HTGeometry.wienerHopfLift (star (circlePolyInv h₀ hh₀_out)) *
      HTGeometry.wienerHopfLift (star (circlePoly h₀)) = 1 := by
    rw [← wienerHopfLift_mul_star_hardyPlus' _ (hankelPlus_circlePoly_eq_zero h₀),
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
      wienerHopfLift_hardyPlus_mul' (hankelPlus_circlePoly_eq_zero g₀),
      wienerHopfLift_hardyPlus_mul' (hankelPlus_circlePolyInv_eq_zero h₀ hh₀_out),
      wienerHopfLift_mul_star_hardyPlus' _ (hankelPlus_circlePoly_eq_zero h₀),
      wienerHopfLift_mul_star_hardyPlus' _ (hankelPlus_circlePolyInv_eq_zero g₀ hg₀_out),
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


/-- **General 6-way Birkhoff–Szegő TFAE for any divisor difference polynomial on `zhukovskyLoop n`.** -/
theorem szego_positivity_tfae_of_prod_eval {P : Polynomial ℂ} {Z : Finset ℂ}
    {mult : ℂ → ℕ} {n : ℕ}
    (heval : ∀ x : ℂ, P.eval x = ∏ z ∈ Z, ∏ w ∈ Z, (x - (z - w)) ^ (mult z * mult w))
    (hellipse : ∀ z ∈ Z, ∀ w ∈ Z, zhukovskyEllipseForm n (z - w) ≠ 1) :
    let Λ := polyZhukovskyLaurentLoop n P
    let T_op := HTGeometry.wienerHopfLift (unitNormalizeSymbol Λ)
    [ HTGeometry.fredholmIndex T_op < 2,
      HTGeometry.fredholmIndex T_op = 0,
      IsUnit T_op,
      IsUnit (HTGeometry.wienerHopfLift Λ),
      ∃ G H : Polynomial ℂ, IsOuterPolynomial G ∧ IsOuterPolynomial H ∧
        Λ = circlePoly G * star (circlePoly H),
      ∃ F : ℂ → ℂ, IsDiskUnit F ∧
        ∀ u : HTGeometry.UnitCircle, 0 < (F (u : ℂ) * Λ u).re
    ].TFAE := by
  intro Λ T_op
  obtain ⟨_, _, g₀, h₀, hg₀, hh₀, _, hlaurent, hind_nm, hunit_un, hunit_nm⟩ :=
    exists_birkhoffSzego_of_prod_eval heval hellipse
  set k : ℕ := ∑ z ∈ Z, ∑ w ∈ Z,
    mult z * mult w * (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0)
  tfae_have 1 → 2 := by
    intro hlt; rw [hind_nm] at hlt ⊢; omega
  tfae_have 2 → 3 := by
    intro h0; rw [hind_nm] at h0; exact hunit_nm.mpr (by omega)
  tfae_have 3 → 4 := fun hu => hunit_un.mpr (hunit_nm.mp hu)
  tfae_have 4 → 5 := by
    intro hu
    have hk0 : k = 0 := hunit_un.mp hu
    refine ⟨g₀ ^ 2, h₀ ^ 2, isOuterPolynomial_pow hg₀ 2, isOuterPolynomial_pow hh₀ 2, ?_⟩
    dsimp only [Λ] at hlaurent ⊢
    rw [hlaurent, hk0, mul_zero, pow_zero, mul_one]
  tfae_have 5 → 6 := by
    rintro ⟨G, H, hG, hH, hGH⟩
    let F : ℂ → ℂ := fun z => (G.eval z)⁻¹ * H.eval z
    have hF_disk : IsDiskUnit F := by
      refine ⟨(G.continuous.continuousOn.inv₀ fun z hz => ?_).mul H.continuous.continuousOn,
        fun z hz => ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hG z hz
      · rw [Metric.mem_closedBall, dist_zero_right] at hz
        exact mul_ne_zero (inv_ne_zero (hG z hz)) (hH z hz)
    refine ⟨F, hF_disk, fun u => ?_⟩
    rw [hGH]
    simp only [F, ContinuousMap.mul_apply, ContinuousMap.star_apply, circlePoly_apply]
    have hGu_ne : G.eval (u : ℂ) ≠ 0 := hG (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le
    have hHu_ne : H.eval (u : ℂ) ≠ 0 := hH (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le
    have hprod : ((G.eval (u : ℂ))⁻¹ * H.eval (u : ℂ)) *
        (G.eval (u : ℂ) * star (H.eval (u : ℂ))) =
        H.eval (u : ℂ) * star (H.eval (u : ℂ)) := by
      field_simp [hGu_ne]
    rw [hprod, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr hHu_ne)
  tfae_have 6 → 1 := by
    rintro ⟨F, hF, hpos⟩
    have h0 := (fredholmIndex_eq_zero_of_diskUnit_re_pos Λ hF hpos).2
    dsimp only [T_op]
    rw [h0]; norm_num
  tfae_finish

/-- Height-uniform upper bound on `‖xi z‖` and `‖deriv xi z‖` across the entire vertical strip
`|Re z| ≤ 2`. -/
theorem exists_strip_xi_and_deriv_bound :
    ∃ M_strip : ℝ, 1 ≤ M_strip ∧ ∀ z : ℂ, |z.re| ≤ 2 →
      ‖_root_.RHTower.xi z‖ ≤ M_strip ∧ ‖deriv _root_.RHTower.xi z‖ ≤ M_strip := by
  obtain ⟨A_xi, hA_xi1, hxi_growth⟩ := RiemannGaussian.riemannXi_logLinearGrowth
  let B_amp : ℝ := Real.exp (A_xi * RiemannGaussian.xiLogLinearScale 3) + thetaStripTailBound 0
  let B_der : ℝ := _root_.RHTower.thetaAmplitudeEnvelope 2 + thetaStripTailBound 0
  let M_strip : ℝ := max 1 (max B_amp B_der)
  refine ⟨M_strip, le_max_left 1 _, fun z hz => ?_⟩
  have hre_scale : RiemannGaussian.xiLogLinearScale (‖(z.re : ℂ)‖ + 1) ≤
      RiemannGaussian.xiLogLinearScale 3 := by
    unfold RiemannGaussian.xiLogLinearScale
    have h1 : ‖(z.re : ℂ)‖ + 1 ≤ 3 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    have hlog_nn : 0 ≤ 1 + Real.log (‖(z.re : ℂ)‖ + 1 + 1) :=
      add_nonneg zero_le_one (Real.log_nonneg (by linarith [norm_nonneg (z.re : ℂ)]))
    refine mul_le_mul h1 ?_ hlog_nn (by norm_num)
    exact add_le_add le_rfl (Real.log_le_log (by positivity) (by linarith))
  have hamp : ‖_root_.RHTower.xi z‖ ≤ B_amp := by
    have h0 : ‖_root_.RHTower.finiteThetaAmplitude 0 z‖ ≤
        Real.exp (A_xi * RiemannGaussian.xiLogLinearScale 3) :=
      (norm_finiteThetaAmplitude_le_riemannXi_re 0 z).trans
        ((hxi_growth (z.re : ℂ)).trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hre_scale (by linarith))))
    have htail : ‖_root_.RHTower.finiteThetaAmplitude 0 z - _root_.RHTower.xi z‖ ≤
        thetaStripTailBound 0 := by
      simpa only [thetaStripTailBound, mul_right_comm] using
        norm_finiteThetaAmplitude_sub_xi_le_strip 0 (by norm_num : (0 : ℝ) ≤ 2) hz
    have htri : ‖_root_.RHTower.xi z‖ ≤
        ‖_root_.RHTower.finiteThetaAmplitude 0 z‖ +
          ‖_root_.RHTower.finiteThetaAmplitude 0 z - _root_.RHTower.xi z‖ := by
      have := norm_sub_le (_root_.RHTower.finiteThetaAmplitude 0 z)
        (_root_.RHTower.finiteThetaAmplitude 0 z - _root_.RHTower.xi z)
      simpa only [sub_sub_cancel] using this
    dsimp only [B_amp]; linarith
  have hder : ‖deriv _root_.RHTower.xi z‖ ≤ B_der := by
    have h0 : ‖-_root_.RHTower.finiteThetaFirstMoment 0 z‖ ≤
        _root_.RHTower.thetaAmplitudeEnvelope 2 := by
      rw [norm_neg]
      exact norm_finiteThetaFirstMoment_le_strip 0 (by norm_num : (0 : ℝ) ≤ 2) hz
    have htail : ‖-_root_.RHTower.finiteThetaFirstMoment 0 z - deriv _root_.RHTower.xi z‖ ≤
        thetaStripTailBound 0 := by
      simpa only [thetaStripTailBound, mul_right_comm] using
        norm_finiteThetaFirstMoment_sub_deriv_xi_le_strip 0 (by norm_num : (0 : ℝ) ≤ 2) hz
    have htri : ‖deriv _root_.RHTower.xi z‖ ≤
        ‖-_root_.RHTower.finiteThetaFirstMoment 0 z‖ +
          ‖-_root_.RHTower.finiteThetaFirstMoment 0 z - deriv _root_.RHTower.xi z‖ := by
      have := norm_sub_le (-_root_.RHTower.finiteThetaFirstMoment 0 z)
        (-_root_.RHTower.finiteThetaFirstMoment 0 z - deriv _root_.RHTower.xi z)
      simpa only [sub_sub_cancel] using this
    dsimp only [B_der]; linarith
  exact ⟨hamp.trans ((le_max_left _ _).trans (le_max_right 1 _)),
    hder.trans ((le_max_right _ _).trans (le_max_right 1 _))⟩

private lemma continuous_neg_finiteThetaFirstMoment' (N : ℕ) :
    Continuous (fun z : ℂ => -_root_.RHTower.finiteThetaFirstMoment N z) := by
  have heq : (fun z : ℂ => -_root_.RHTower.finiteThetaFirstMoment N z) =
      deriv (_root_.RHTower.finiteThetaAmplitude N) :=
    funext fun z => (_root_.RHTower.deriv_finiteThetaAmplitude N z).symm
  rw [heq]
  exact continuousOn_univ.mp
    (((_root_.RHTower.differentiable_finiteThetaAmplitude N).differentiableOn.deriv
      isOpen_univ).continuousOn)

/-- **Quantitative contour moment perturbation and `r = 0` Rouché degree lock** on any rectangle
`[-1 / 2, 3 / 2] × [z₁.im, z₂.im]` (`z₁.im ≤ z₂.im`) around any center `c : ℂ`. -/
theorem rectIntegral_shifted_powerSum_perturbation {z₁ z₂ c : ℂ} {μ R H_span M_strip : ℝ} {N : ℕ}
    (hre₁ : z₁.re = -1 / 2) (hre₂ : z₂.re = 3 / 2) (him : z₁.im ≤ z₂.im)
    (hμ_pos : 0 < μ) (_hμ_le : μ ≤ 1) (hR1 : 1 ≤ R) (hH1 : 1 ≤ H_span) (hM1 : 1 ≤ M_strip)
    (hspan : z₂.im - z₁.im ≤ H_span)
    (hstrip : ∀ z : ℂ, |z.re| ≤ 2 →
      ‖_root_.RHTower.xi z‖ ≤ M_strip ∧ ‖deriv _root_.RHTower.xi z‖ ≤ M_strip)
    (hμ_bdry : ∀ t : ℝ, μ ≤ ‖_root_.RHTower.xi (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t)‖)
    (hR_bdry : ∀ t : ℝ, ‖_root_.RHTower.rectangleBoundaryPath z₁ z₂ t - c‖ ≤ R)
    (hN_tail : thetaStripTailBound N ≤ μ / 2) :
    (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
        (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t) ≠ 0) ∧
    ((2 * Real.pi * I)⁻¹ *
        _root_.RHTower.rectIntegral
          (fun z => -_root_.RHTower.finiteThetaFirstMoment N z /
            _root_.RHTower.finiteThetaAmplitude N z) z₁ z₂ =
      (2 * Real.pi * I)⁻¹ * _root_.RHTower.rectIntegral (logDeriv _root_.RHTower.xi) z₁ z₂) ∧
    ∀ r : ℕ,
      ‖(2 * Real.pi * I)⁻¹ *
          _root_.RHTower.rectIntegral
            (fun z => (z - c) ^ r *
              (-_root_.RHTower.finiteThetaFirstMoment N z /
                _root_.RHTower.finiteThetaAmplitude N z)) z₁ z₂ -
        (2 * Real.pi * I)⁻¹ *
          _root_.RHTower.rectIntegral
            (fun z => (z - c) ^ r * logDeriv _root_.RHTower.xi z) z₁ z₂‖ ≤
        R ^ r * (4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N := by
  set γ := _root_.RHTower.rectangleBoundaryPath z₁ z₂
  set vel := _root_.RHTower.rectangleBoundaryVelocity z₁ z₂
  have hre_le : z₁.re ≤ z₂.re := by linarith
  have hγ_re2 : ∀ t : ℝ, |(γ t).re| ≤ 2 := by
    intro t
    have hm := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm z₁ z₂ hre_le him t
    rw [uIcc_of_le hre_le, Complex.mem_reProdIm, hre₁, hre₂] at hm
    exact abs_le.mpr ⟨by linarith [hm.1.1], by linarith [hm.1.2]⟩
  have hamp_diff : ∀ t : ℝ,
      ‖_root_.RHTower.finiteThetaAmplitude N (γ t) - _root_.RHTower.xi (γ t)‖ ≤
        thetaStripTailBound N := fun t => by
    simpa only [thetaStripTailBound, mul_right_comm] using
      norm_finiteThetaAmplitude_sub_xi_le_strip N (by norm_num : (0 : ℝ) ≤ 2) (hγ_re2 t)
  have hmom_diff : ∀ t : ℝ,
      ‖-_root_.RHTower.finiteThetaFirstMoment N (γ t) - deriv _root_.RHTower.xi (γ t)‖ ≤
        thetaStripTailBound N := fun t => by
    simpa only [thetaStripTailBound, mul_right_comm] using
      norm_finiteThetaFirstMoment_sub_deriv_xi_le_strip N (by norm_num : (0 : ℝ) ≤ 2) (hγ_re2 t)
  have hrouche : ∀ t : ℝ,
      ‖_root_.RHTower.finiteThetaAmplitude N (γ t) - _root_.RHTower.xi (γ t)‖ <
        ‖_root_.RHTower.xi (γ t)‖ := fun t =>
    (hamp_diff t).trans_lt ((hN_tail.trans_lt (by linarith)).trans_le (hμ_bdry t))
  have hamp_lo : ∀ t : ℝ, μ / 2 ≤ ‖_root_.RHTower.finiteThetaAmplitude N (γ t)‖ := by
    intro t
    have htri := norm_sub_norm_le (_root_.RHTower.xi (γ t))
      (_root_.RHTower.finiteThetaAmplitude N (γ t))
    rw [norm_sub_rev] at htri
    linarith [hμ_bdry t, (hamp_diff t).trans hN_tail]
  have hamp_nz : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N (γ t) ≠ 0 := by
    intro t h0
    have hl := hamp_lo t
    rw [h0, norm_zero] at hl
    linarith
  have hxi_nz : ∀ t : ℝ, _root_.RHTower.xi (γ t) ≠ 0 := by
    intro t h0
    have hl := hμ_bdry t
    rw [h0, norm_zero] at hl
    linarith
  have hlog_eq : (fun z : ℂ =>
      -_root_.RHTower.finiteThetaFirstMoment N z / _root_.RHTower.finiteThetaAmplitude N z) =
      logDeriv (_root_.RHTower.finiteThetaAmplitude N) := by
    funext z
    rw [logDeriv_apply, _root_.RHTower.deriv_finiteThetaAmplitude]
  have hr0_eq : (2 * Real.pi * I)⁻¹ *
      _root_.RHTower.rectIntegral
        (fun z => -_root_.RHTower.finiteThetaFirstMoment N z /
          _root_.RHTower.finiteThetaAmplitude N z) z₁ z₂ =
      (2 * Real.pi * I)⁻¹ * _root_.RHTower.rectIntegral (logDeriv _root_.RHTower.xi) z₁ z₂ := by
    rw [hlog_eq]
    exact (rectIntegral_logDeriv_eq_of_norm_sub_lt
      _root_.RHTower.xi_differentiable
      (_root_.RHTower.differentiable_finiteThetaAmplitude N) z₁ z₂ hrouche).symm
  refine ⟨hamp_nz, hr0_eq, fun r => ?_⟩
  have hγ_cont : Continuous γ := _root_.RHTower.continuous_rectangleBoundaryPath z₁ z₂
  have hxi_deriv_cont : Continuous (deriv _root_.RHTower.xi) :=
    continuousOn_univ.mp
      ((_root_.RHTower.xi_differentiable.differentiableOn.deriv isOpen_univ).continuousOn)
  let gN : ℂ → ℂ := fun z => (z - c) ^ r *
    (-_root_.RHTower.finiteThetaFirstMoment N z / _root_.RHTower.finiteThetaAmplitude N z)
  let gXi : ℂ → ℂ := fun z => (z - c) ^ r * logDeriv _root_.RHTower.xi z
  have hgN_cont : Continuous (fun t : ℝ => gN (γ t)) :=
    ((hγ_cont.sub continuous_const).pow r).mul
      (((continuous_neg_finiteThetaFirstMoment' N).comp hγ_cont).div
        (((_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous).comp hγ_cont)
        hamp_nz)
  have hgXi_cont : Continuous (fun t : ℝ => gXi (γ t)) :=
    ((hγ_cont.sub continuous_const).pow r).mul
      ((hxi_deriv_cont.comp hγ_cont).div
        (_root_.RHTower.xi_differentiable.continuous.comp hγ_cont)
        hxi_nz)
  rw [← _root_.RHTower.integral_rectangleBoundary_eq_rectIntegral z₁ z₂ gN hgN_cont,
    ← _root_.RHTower.integral_rectangleBoundary_eq_rectIntegral z₁ z₂ gXi hgXi_cont,
    ← mul_sub, norm_mul,
    ← intervalIntegral.integral_sub
      (_root_.RHTower.intervalIntegrable_mul_rectangleBoundaryVelocity z₁ z₂ hgN_cont 0 1)
      (_root_.RHTower.intervalIntegrable_mul_rectangleBoundaryVelocity z₁ z₂ hgXi_cont 0 1)]
  have hvel_le : ∀ t : ℝ, ‖vel t‖ ≤ 12 * H_span := by
    intro t
    have hv := _root_.RHTower.norm_rectangleBoundaryVelocity_le z₁ z₂ t
    have hre_abs : |z₂.re - z₁.re| = 2 := by rw [hre₁, hre₂]; norm_num
    have him_abs : |z₂.im - z₁.im| = z₂.im - z₁.im := abs_of_nonneg (sub_nonneg.mpr him)
    rw [hre_abs, him_abs] at hv
    linarith
  have hpt : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖gN (γ t) * vel t - gXi (γ t) * vel t‖ ≤
        R ^ r * ((2 * M_strip + 1) / (μ ^ 2 / 2)) * (12 * H_span) * thetaStripTailBound N := by
    intro t _
    set A_N := -_root_.RHTower.finiteThetaFirstMoment N (γ t)
    set B_N := _root_.RHTower.finiteThetaAmplitude N (γ t)
    set A := deriv _root_.RHTower.xi (γ t)
    set B := _root_.RHTower.xi (γ t)
    have hquot : A_N / B_N - A / B = ((A_N - A) * B + A * (B - B_N)) / (B_N * B) := by
      rw [div_sub_div _ _ (hamp_nz t) (hxi_nz t)]
      congr 1; ring
    have hdenom_pos : 0 < μ ^ 2 / 2 := by positivity
    have hdenom_le : μ ^ 2 / 2 ≤ ‖B_N * B‖ := by
      rw [norm_mul]
      calc μ ^ 2 / 2 = (μ / 2) * μ := by ring
        _ ≤ ‖B_N‖ * ‖B‖ := mul_le_mul (hamp_lo t) (hμ_bdry t) (by positivity) (norm_nonneg _)
    obtain ⟨hB_le, hA_le⟩ := hstrip (γ t) (hγ_re2 t)
    have herr_nn : 0 ≤ thetaStripTailBound N := thetaStripTailBound_nonneg N
    have hnum_le : ‖(A_N - A) * B + A * (B - B_N)‖ ≤ (2 * M_strip + 1) * thetaStripTailBound N := by
      calc ‖(A_N - A) * B + A * (B - B_N)‖
          ≤ ‖A_N - A‖ * ‖B‖ + ‖A‖ * ‖B_N - B‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_sub_rev B B_N]
        _ ≤ thetaStripTailBound N * M_strip + M_strip * thetaStripTailBound N :=
            add_le_add
              (mul_le_mul (hmom_diff t) hB_le (norm_nonneg _) herr_nn)
              (mul_le_mul hA_le (hamp_diff t) (norm_nonneg _) (by linarith))
        _ ≤ (2 * M_strip + 1) * thetaStripTailBound N := by nlinarith
    have hquot_le : ‖A_N / B_N - logDeriv _root_.RHTower.xi (γ t)‖ ≤
        ((2 * M_strip + 1) / (μ ^ 2 / 2)) * thetaStripTailBound N := by
      rw [logDeriv_apply, hquot, norm_div]
      have hBB_pos : 0 < ‖B_N * B‖ := lt_of_lt_of_le hdenom_pos hdenom_le
      calc ‖(A_N - A) * B + A * (B - B_N)‖ / ‖B_N * B‖
          ≤ ((2 * M_strip + 1) * thetaStripTailBound N) / (μ ^ 2 / 2) := by
            rw [div_le_div_iff₀ hBB_pos hdenom_pos]
            exact mul_le_mul hnum_le hdenom_le hdenom_pos.le (by positivity)
        _ = ((2 * M_strip + 1) / (μ ^ 2 / 2)) * thetaStripTailBound N := by ring
    have halg : gN (γ t) * vel t - gXi (γ t) * vel t =
        (γ t - c) ^ r * (A_N / B_N - logDeriv _root_.RHTower.xi (γ t)) * vel t := by
      dsimp only [gN, gXi]; ring
    rw [halg, norm_mul, norm_mul, norm_pow]
    have hpow_r : ‖γ t - c‖ ^ r ≤ R ^ r := pow_le_pow_left₀ (norm_nonneg _) (hR_bdry t) r
    calc ‖γ t - c‖ ^ r * ‖A_N / B_N - logDeriv _root_.RHTower.xi (γ t)‖ * ‖vel t‖
        ≤ (R ^ r * (((2 * M_strip + 1) / (μ ^ 2 / 2)) * thetaStripTailBound N)) *
            (12 * H_span) := by
          refine mul_le_mul ?_ (hvel_le t) (norm_nonneg _) (by positivity)
          exact mul_le_mul hpow_r hquot_le (norm_nonneg _) (by positivity)
      _ = R ^ r * ((2 * M_strip + 1) / (μ ^ 2 / 2)) * (12 * H_span) * thetaStripTailBound N := by
          ring
  have hint_le := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at hint_le
  have h2pi_inv : ‖(2 * Real.pi * I : ℂ)⁻¹‖ ≤ 1 / 6 := by
    have hnorm : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    rw [norm_inv, hnorm, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.pi_gt_three])
  calc ‖(2 * Real.pi * I : ℂ)⁻¹‖ * ‖∫ t in (0 : ℝ)..1, (gN (γ t) * vel t - gXi (γ t) * vel t)‖
      ≤ (1 / 6) *
          (R ^ r * ((2 * M_strip + 1) / (μ ^ 2 / 2)) * (12 * H_span) * thetaStripTailBound N) :=
        mul_le_mul h2pi_inv hint_le (norm_nonneg _) (by norm_num)
    _ = R ^ r * (4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N := by
        field_simp [hμ_pos.ne']; ring

/-- Uniform all-`m` upper bound on `xiUnitWindowOrder (m : ℝ)` and cumulative
`xiStripWindowTotalOrder T`. -/
theorem exists_all_xiUnitWindowOrder_le_log :
    ∃ C_loc : ℝ, 1 ≤ C_loc ∧
      (∀ m : ℕ, (xiUnitWindowOrder (m : ℝ) : ℝ) ≤ C_loc * Real.log ((m + 4 : ℕ) : ℝ)) ∧
      (∀ (m : ℕ) (T : ℝ), T ≤ ((m + 1 : ℕ) : ℝ) →
        (_root_.RHTower.xiStripWindowTotalOrder T : ℝ) ≤
          C_loc * ((m + 1 : ℕ) : ℝ) * Real.log ((m + 4 : ℕ) : ℝ)) := by
  obtain ⟨C₀, hC₀_pos, hev⟩ := exists_xiUnitWindowOrder_le_log
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  let K₁ : ℕ := Nat.ceil (max T₁ 2)
  let B_fin : ℝ := (_root_.RHTower.xiStripWindowTotalOrder ((K₁ + 1 : ℕ) : ℝ) : ℝ) + 1
  let C_loc : ℝ := max 1 (max C₀ (B_fin / Real.log 4))
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hC1 : 1 ≤ C_loc := le_max_left 1 _
  have hunit : ∀ m : ℕ, (xiUnitWindowOrder (m : ℝ) : ℝ) ≤ C_loc * Real.log ((m + 4 : ℕ) : ℝ) := by
    intro m
    have hlog_ge : Real.log 4 ≤ Real.log ((m + 4 : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show 4 ≤ m + 4 by omega))
    rcases lt_or_ge m K₁ with hlt | hge
    · have hm_le : (xiUnitWindowOrder (m : ℝ) : ℝ) ≤ B_fin := by
        have hsub : xiUnitWindowZeros (m : ℝ) ⊆
            (_root_.RHTower.stripZeros_finite ((K₁ + 1 : ℕ) : ℝ)).toFinset := by
          intro ρ hρ
          have h1 := (mem_xiUnitWindowZeros.mp hρ).1
          exact _root_.RHTower.stripZeros_toFinset_mono
            (by exact_mod_cast (show m + 1 ≤ K₁ + 1 by omega)) h1
        have hle_nat : xiUnitWindowOrder (m : ℝ) ≤
            _root_.RHTower.xiStripWindowTotalOrder ((K₁ + 1 : ℕ) : ℝ) :=
          Finset.sum_le_sum_of_subset hsub
        have hle_real : (xiUnitWindowOrder (m : ℝ) : ℝ) ≤
            (_root_.RHTower.xiStripWindowTotalOrder ((K₁ + 1 : ℕ) : ℝ) : ℝ) := by
          exact_mod_cast hle_nat
        dsimp only [B_fin]; linarith
      calc (xiUnitWindowOrder (m : ℝ) : ℝ)
          ≤ B_fin := hm_le
        _ = (B_fin / Real.log 4) * Real.log 4 := by field_simp [hlog4_pos.ne']
        _ ≤ C_loc * Real.log ((m + 4 : ℕ) : ℝ) :=
            mul_le_mul ((le_max_right _ _).trans (le_max_right 1 _)) hlog_ge
              hlog4_pos.le (by linarith)
    · have hmT₁ : T₁ ≤ (m : ℝ) :=
        (le_max_left T₁ 2).trans ((Nat.le_ceil _).trans (by exact_mod_cast hge))
      have hm2 : (2 : ℝ) ≤ (m : ℝ) :=
        (le_max_right T₁ 2).trans ((Nat.le_ceil _).trans (by exact_mod_cast hge))
      have hlog_m : Real.log (m : ℝ) ≤ Real.log ((m + 4 : ℕ) : ℝ) :=
        Real.log_le_log (by linarith) (by push_cast; linarith)
      calc (xiUnitWindowOrder (m : ℝ) : ℝ)
          ≤ C₀ * Real.log (m : ℝ) := hT₁ (m : ℝ) hmT₁
        _ ≤ C_loc * Real.log ((m + 4 : ℕ) : ℝ) :=
            mul_le_mul ((le_max_left _ _).trans (le_max_right 1 _)) hlog_m
              (Real.log_nonneg (by linarith)) (by linarith)
  refine ⟨C_loc, hC1, hunit, fun m T hT => ?_⟩
  have hmono_nat : _root_.RHTower.xiStripWindowTotalOrder T ≤
      _root_.RHTower.xiStripWindowTotalOrder ((m + 1 : ℕ) : ℝ) :=
    Finset.sum_le_sum_of_subset (_root_.RHTower.stripZeros_toFinset_mono hT)
  have hsum_nat : ∀ k : ℕ,
      _root_.RHTower.xiStripWindowTotalOrder (k : ℝ) =
        ∑ j ∈ Finset.range k, xiUnitWindowOrder (j : ℝ) := by
    intro k
    induction k with
    | zero =>
        simp only [Nat.cast_zero, Finset.range_zero, Finset.sum_empty]
        unfold _root_.RHTower.xiStripWindowTotalOrder
        apply Finset.sum_eq_zero
        intro ρ hρ
        have h := (_root_.RHTower.stripZeros_finite 0).mem_toFinset.mp hρ
        linarith [h.1.2.2.1, h.1.2.2.2]
    | succ k ih =>
        rw [Finset.sum_range_succ, ← ih]
        unfold _root_.RHTower.xiStripWindowTotalOrder xiUnitWindowOrder
        push_cast
        exact sum_stripZeros_add_one (k : ℝ) _
  calc (_root_.RHTower.xiStripWindowTotalOrder T : ℝ)
      ≤ (_root_.RHTower.xiStripWindowTotalOrder ((m + 1 : ℕ) : ℝ) : ℝ) := by
        exact_mod_cast hmono_nat
    _ = ∑ j ∈ Finset.range (m + 1), (xiUnitWindowOrder (j : ℝ) : ℝ) := by
        rw [hsum_nat (m + 1), Nat.cast_sum]
    _ ≤ ∑ _j ∈ Finset.range (m + 1), (C_loc * Real.log ((m + 4 : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun j hj => (hunit j).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact Real.log_le_log (by exact_mod_cast (show 0 < j + 4 by omega))
          (by exact_mod_cast (show j + 4 ≤ m + 4 by have := Finset.mem_range.mp hj; omega))
    _ = C_loc * ((m + 1 : ℕ) : ℝ) * Real.log ((m + 4 : ℕ) : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring


/-- **Uniform all-`m` Burnol good-height selection.**
There exist `c_good > 0` (`c_good ≤ (5026 / 16875) * exp(-π)`) and `T_good : ℕ → ℝ` such that for
every `m : ℕ`, `T_good m ∈ [m, m + 1]` (`1 / 2 ≤ T_good m`), and `c_good * exp(-(m + 1))` bounds
`‖xi‖` below along both the horizontal segment `[-1, 2] + i * T_good m` and the vertical sides
`{-1 / 2, 3 / 2} + i * [-T_good m, T_good m]`. -/
theorem exists_all_nat_burnol_good_height :
    ∃ (c_good : ℝ) (T_good : ℕ → ℝ),
      0 < c_good ∧ c_good ≤ (5026 / 16875) * Real.exp (-Real.pi) ∧
      ∀ m : ℕ,
        (m : ℝ) ≤ T_good m ∧ T_good m ≤ (m : ℝ) + 1 ∧ (1 / 2 : ℝ) ≤ T_good m ∧
        (∀ x : ℝ, -1 ≤ x → x ≤ 2 →
          c_good * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤
            ‖_root_.RHTower.xi ((x : ℂ) + (T_good m : ℂ) * I)‖) ∧
        (∀ y : ℝ, |y| ≤ T_good m →
          c_good * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤
              ‖_root_.RHTower.xi ((3 / 2 : ℂ) + (y : ℂ) * I)‖ ∧
            c_good * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤
              ‖_root_.RHTower.xi ((-1 / 2 : ℂ) + (y : ℂ) * I)‖) := by
  obtain ⟨H₀, c_bdry, K_bdry, hH₀9, hc_bdry, hc_bdry_le, hburnol⟩ :=
    exists_burnol_horizontal_and_vertical_xi_lower
  let c_low : ℝ := (5026 / 16875) * Real.exp (-Real.pi)
  have hc_low_pos : 0 < c_low := by dsimp only [c_low]; positivity
  -- High regime `m ≥ Nat.ceil H₀`: absorb `T_star ^ K_bdry` into `exp((1 / 10) * T_star)`.
  let K_pos : ℕ := K_bdry + 1
  have hK_pos : 0 < (K_pos : ℝ) := by dsimp only [K_pos]; positivity
  let C_pow : ℝ := (10 * (K_pos : ℝ)) ^ K_pos
  have hC_pow_pos : 0 < C_pow := by dsimp only [C_pow]; positivity
  let c_high : ℝ := c_bdry / C_pow
  have hc_high_pos : 0 < c_high := div_pos hc_bdry hC_pow_pos
  let M₀ : ℕ := Nat.ceil H₀
  -- For EVERY `m : ℕ`, construct `T_m ∈ [m, m + 1]` (`1 / 2 ≤ T_m`) and `c_m > 0` individually,
  -- then take the uniform minimum over `m < M₀` and `c_high`.
  have hsingle : ∀ m : ℕ, ∃ (T_m c_m : ℝ), 0 < c_m ∧
      (m : ℝ) ≤ T_m ∧ T_m ≤ (m : ℝ) + 1 ∧ (1 / 2 : ℝ) ≤ T_m ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 2 →
        c_m * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤
          ‖_root_.RHTower.xi ((x : ℂ) + (T_m : ℂ) * I)‖) ∧
      (∀ y : ℝ, |y| ≤ T_m →
        c_m * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤
            ‖_root_.RHTower.xi ((3 / 2 : ℂ) + (y : ℂ) * I)‖ ∧
          c_m * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤
            ‖_root_.RHTower.xi ((-1 / 2 : ℂ) + (y : ℂ) * I)‖) := by
    intro m
    -- Pick a zero-free ordinate `T_m ∈ (m + 1 / 2, m + 1)` by finite pigeonhole, then take
    -- compact minimums along `[-1, 2] + i * T_m` and `{-1/2, 3/2} + i * [-T_m, T_m]`.
    let Y : Finset ℝ :=
      ((_root_.RHTower.stripZeros_finite ((m + 2 : ℕ) : ℝ)).toFinset).image Complex.im
    let cand : ℕ → ℝ := fun j =>
      (m : ℝ) + 1 / 2 + ((j + 1 : ℕ) : ℝ) / (2 * ((Y.card + 2 : ℕ) : ℝ))
    have hcand_inj : Function.Injective cand := by
      intro j₁ j₂ heq
      dsimp only [cand] at heq
      have hden : (0 : ℝ) < 2 * ((Y.card + 2 : ℕ) : ℝ) := by positivity
      have h1 : ((j₁ + 1 : ℕ) : ℝ) / (2 * ((Y.card + 2 : ℕ) : ℝ)) =
          ((j₂ + 1 : ℕ) : ℝ) / (2 * ((Y.card + 2 : ℕ) : ℝ)) := by linarith
      have h2 : ((j₁ + 1 : ℕ) : ℝ) = ((j₂ + 1 : ℕ) : ℝ) :=
        (div_left_inj' hden.ne').mp h1
      have h3 : j₁ + 1 = j₂ + 1 := Nat.cast_injective h2
      omega
    let C_set : Finset ℝ := (Finset.range (Y.card + 1)).image cand
    have hC_card : C_set.card = Y.card + 1 := by
      rw [Finset.card_image_of_injective _ hcand_inj, Finset.card_range]
    have hex_T : ∃ T_m ∈ C_set, T_m ∉ Y := by
      by_contra hall
      simp only [not_exists, not_and, Classical.not_not] at hall
      have hle := Finset.card_le_card hall
      omega
    obtain ⟨T_m, hTm_C, hTm_notY⟩ := hex_T
    obtain ⟨j₀, hj₀, rfl⟩ := Finset.mem_image.mp hTm_C
    have hj₀_lt : j₀ < Y.card + 1 := Finset.mem_range.mp hj₀
    have hden_pos : (0 : ℝ) < 2 * ((Y.card + 2 : ℕ) : ℝ) := by positivity
    have hfrac_pos : 0 < ((j₀ + 1 : ℕ) : ℝ) / (2 * ((Y.card + 2 : ℕ) : ℝ)) := by positivity
    have hfrac_lt_half : ((j₀ + 1 : ℕ) : ℝ) / (2 * ((Y.card + 2 : ℕ) : ℝ)) < 1 / 2 := by
      rw [div_lt_div_iff₀ hden_pos (by norm_num)]
      have hlt_nat : ((j₀ + 1 : ℕ) : ℝ) < ((Y.card + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show j₀ + 1 < Y.card + 2 by omega)
      linarith
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hTm_gt : (m : ℝ) + 1 / 2 < cand j₀ := by dsimp only [cand]; linarith
    have hTm_lt : cand j₀ < (m : ℝ) + 1 := by dsimp only [cand]; linarith
    have hTm_half : (1 / 2 : ℝ) ≤ cand j₀ := by linarith
    -- `xi` never vanishes on `[-1, 2] + i * cand j₀`.
    have hhor_nz : ∀ x ∈ Icc (-1 : ℝ) 2,
        _root_.RHTower.xi ((x : ℂ) + (cand j₀ : ℂ) * I) ≠ 0 := by
      intro x _ h0
      set w : ℂ := (x : ℂ) + (cand j₀ : ℂ) * I
      obtain ⟨hw0, hw1⟩ := _root_.RHTower.xi_zero_re_mem_open_unit h0
      have hw_im : w.im = cand j₀ := by simp [w]
      have hw_strip : w ∈ (_root_.RHTower.stripZeros_finite ((m + 2 : ℕ) : ℝ)).toFinset := by
        apply (_root_.RHTower.stripZeros_finite ((m + 2 : ℕ) : ℝ)).mem_toFinset.mpr
        refine ⟨⟨hw0, hw1, by rw [hw_im]; linarith, ?_⟩, h0⟩
        rw [hw_im]; push_cast; linarith
      exact hTm_notY (Finset.mem_image.mpr ⟨w, hw_strip, hw_im⟩)
    let f_hor : ℝ → ℝ := fun x => ‖_root_.RHTower.xi ((x : ℂ) + (cand j₀ : ℂ) * I)‖
    have hhor_cont : ContinuousOn f_hor (Icc (-1 : ℝ) 2) :=
      (_root_.RHTower.xi_differentiable.continuous.comp
        (Complex.continuous_ofReal.add continuous_const)).norm.continuousOn
    obtain ⟨x₀, hx₀, hx₀_min⟩ :=
      isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by norm_num)) hhor_cont
    have hμ_hor_pos : 0 < f_hor x₀ := norm_pos_iff.mpr (hhor_nz x₀ hx₀)
    have hvert_r_nz : ∀ y : ℝ, _root_.RHTower.xi ((3 / 2 : ℂ) + (y : ℂ) * I) ≠ 0 := by
      intro y h0
      have h1 := (_root_.RHTower.xi_zero_re_mem_open_unit h0).2
      simp at h1; linarith
    have hvert_l_nz : ∀ y : ℝ, _root_.RHTower.xi ((-1 / 2 : ℂ) + (y : ℂ) * I) ≠ 0 := by
      intro y h0
      have h1 := (_root_.RHTower.xi_zero_re_mem_open_unit h0).1
      simp at h1; linarith
    have hne_y : (Icc (-cand j₀) (cand j₀)).Nonempty := nonempty_Icc.mpr (by linarith)
    let f_r : ℝ → ℝ := fun y => ‖_root_.RHTower.xi ((3 / 2 : ℂ) + (y : ℂ) * I)‖
    let f_l : ℝ → ℝ := fun y => ‖_root_.RHTower.xi ((-1 / 2 : ℂ) + (y : ℂ) * I)‖
    have hfr_cont : ContinuousOn f_r (Icc (-cand j₀) (cand j₀)) :=
      (_root_.RHTower.xi_differentiable.continuous.comp
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).norm.continuousOn
    have hfl_cont : ContinuousOn f_l (Icc (-cand j₀) (cand j₀)) :=
      (_root_.RHTower.xi_differentiable.continuous.comp
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).norm.continuousOn
    obtain ⟨y₁, _, hy₁_min⟩ := isCompact_Icc.exists_isMinOn hne_y hfr_cont
    obtain ⟨y₂, _, hy₂_min⟩ := isCompact_Icc.exists_isMinOn hne_y hfl_cont
    let μ_m : ℝ := min (f_hor x₀) (min (f_r y₁) (f_l y₂))
    have hμ_m_pos : 0 < μ_m :=
      lt_min hμ_hor_pos (lt_min (norm_pos_iff.mpr (hvert_r_nz y₁))
        (norm_pos_iff.mpr (hvert_l_nz y₂)))
    refine ⟨cand j₀, μ_m * Real.exp ((m + 1 : ℕ) : ℝ), by positivity,
      by linarith, hTm_lt.le, hTm_half, fun x hx1 hx2 => ?_, fun y hy => ?_⟩
    · have hexp_cancel : μ_m * Real.exp ((m + 1 : ℕ) : ℝ) * Real.exp (-((m + 1 : ℕ) : ℝ)) = μ_m := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      rw [hexp_cancel]
      exact (min_le_left _ _).trans (isMinOn_iff.mp hx₀_min x ⟨hx1, hx2⟩)
    · have hexp_cancel : μ_m * Real.exp ((m + 1 : ℕ) : ℝ) * Real.exp (-((m + 1 : ℕ) : ℝ)) = μ_m := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      rw [hexp_cancel]
      have hy_mem : y ∈ Icc (-cand j₀) (cand j₀) := abs_le.mp hy
      exact ⟨((min_le_right _ _).trans (min_le_left _ _)).trans (isMinOn_iff.mp hy₁_min y hy_mem),
        ((min_le_right _ _).trans (min_le_right _ _)).trans (isMinOn_iff.mp hy₂_min y hy_mem)⟩
  choose T_fin c_fin hc_fin_pos hT_fin_lo hT_fin_hi hT_fin_half hT_fin_hor hT_fin_vert using hsingle
  -- High regime `m ≥ M₀`: use `hburnol (m : ℝ)`.
  have hhigh : ∀ m : ℕ, M₀ ≤ m → ∃ T_star : ℝ,
      (m : ℝ) ≤ T_star ∧ T_star ≤ (m : ℝ) + 1 ∧ (1 / 2 : ℝ) ≤ T_star ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 2 →
        c_high * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤
          ‖_root_.RHTower.xi ((x : ℂ) + (T_star : ℂ) * I)‖) ∧
      (∀ y : ℝ, |y| ≤ T_star →
        c_high * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤
            ‖_root_.RHTower.xi ((3 / 2 : ℂ) + (y : ℂ) * I)‖ ∧
          c_high * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤
            ‖_root_.RHTower.xi ((-1 / 2 : ℂ) + (y : ℂ) * I)‖) := by
    intro m hm
    have hmH₀ : H₀ ≤ (m : ℝ) := (Nat.le_ceil H₀).trans (by exact_mod_cast hm)
    obtain ⟨T_star, hlo, hhi, hhor, hvert_b⟩ := hburnol (m : ℝ) hmH₀
    have hT9 : 9 ≤ T_star := hH₀9.trans (hmH₀.trans hlo)
    have hT1 : 1 ≤ T_star := by linarith
    have hpow_absorb : T_star ^ K_bdry ≤ C_pow * Real.exp ((1 / 10) * T_star) := by
      set u : ℝ := T_star / (10 * (K_pos : ℝ))
      have hu0 : 0 ≤ u := by dsimp [u]; positivity
      have hu_exp : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
      have hp := pow_le_pow_left₀ hu0 hu_exp K_pos
      rw [← Real.exp_nat_mul, show (K_pos : ℝ) * u = (1 / 10) * T_star by
        dsimp [u]; field_simp [hK_pos.ne']] at hp
      have hlhs : T_star = (10 * (K_pos : ℝ)) * u := by dsimp [u]; field_simp [hK_pos.ne']
      calc T_star ^ K_bdry
          ≤ T_star ^ K_pos := pow_le_pow_right₀ hT1 (by dsimp [K_pos]; omega)
        _ = ((10 * (K_pos : ℝ)) * u) ^ K_pos := by rw [← hlhs]
        _ = C_pow * u ^ K_pos := by dsimp [C_pow]; exact mul_pow _ _ _
        _ ≤ C_pow * Real.exp ((1 / 10) * T_star) := mul_le_mul_of_nonneg_left hp hC_pow_pos.le
    have hbase_ge : c_high * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤
        c_bdry * (T_star ^ K_bdry)⁻¹ * Real.exp (-(Real.pi / 4) * T_star) := by
      have hinv : (C_pow * Real.exp ((1 / 10) * T_star))⁻¹ ≤ (T_star ^ K_bdry)⁻¹ :=
        inv_anti₀ (by positivity) hpow_absorb
      have hpi_lt : Real.pi / 4 ≤ 4 / 5 := by linarith [Real.pi_lt_d2]
      have hT_le_m1 : T_star ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; exact hhi
      have hexp_le : Real.exp (-((m + 1 : ℕ) : ℝ)) ≤
          (Real.exp ((1 / 10) * T_star))⁻¹ * Real.exp (-(4 / 5) * T_star) := by
        rw [← Real.exp_neg, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      calc c_high * Real.exp (-((m + 1 : ℕ) : ℝ))
          ≤ c_high * ((Real.exp ((1 / 10) * T_star))⁻¹ * Real.exp (-(4 / 5) * T_star)) :=
            mul_le_mul_of_nonneg_left hexp_le hc_high_pos.le
        _ = c_bdry * (C_pow * Real.exp ((1 / 10) * T_star))⁻¹ * Real.exp (-(4 / 5) * T_star) := by
            rw [mul_inv]; dsimp only [c_high, div_eq_mul_inv]; ring
        _ ≤ c_bdry * (T_star ^ K_bdry)⁻¹ * Real.exp (-(Real.pi / 4) * T_star) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hinv hc_bdry.le)
              (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (by positivity)
    exact ⟨T_star, hlo, hhi, by linarith,
      fun x hx1 hx2 => hbase_ge.trans (hhor x hx1 hx2),
      fun y hy => ⟨hbase_ge.trans (hvert_b y hy).1, hbase_ge.trans (hvert_b y hy).2⟩⟩
  let T_good : ℕ → ℝ := fun m =>
    if hm : M₀ ≤ m then (hhigh m hm).choose else T_fin m
  let S_low : Finset ℝ := insert c_low (insert c_high ((Finset.range M₀).image c_fin))
  have hS_ne : S_low.Nonempty := ⟨c_low, Finset.mem_insert_self _ _⟩
  let c_good : ℝ := S_low.min' hS_ne
  have hc_good_pos : 0 < c_good := by
    dsimp only [c_good]
    rw [Finset.lt_min'_iff]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx1
    · exact hc_low_pos
    · rcases Finset.mem_insert.mp hx1 with rfl | hx2
      · exact hc_high_pos
      · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx2
        exact hc_fin_pos k
  have hc_good_le_low : c_good ≤ c_low :=
    Finset.min'_le S_low c_low (Finset.mem_insert_self _ _)
  have hc_good_le_high : c_good ≤ c_high :=
    Finset.min'_le S_low c_high (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  refine ⟨c_good, T_good, hc_good_pos, hc_good_le_low, fun m => ?_⟩
  dsimp only [T_good]
  split_ifs with hm
  · obtain ⟨hlo, hhi, hhalf, hhor, hvert_m⟩ := (hhigh m hm).choose_spec
    have hle : ∀ u : ℝ, 0 ≤ u → c_good * u ≤ c_high * u :=
      fun _ hu => mul_le_mul_of_nonneg_right hc_good_le_high hu
    exact ⟨hlo, hhi, hhalf,
      fun x hx1 hx2 => (hle _ (Real.exp_pos _).le).trans (hhor x hx1 hx2),
      fun y hy => ⟨(hle _ (Real.exp_pos _).le).trans (hvert_m y hy).1,
        (hle _ (Real.exp_pos _).le).trans (hvert_m y hy).2⟩⟩
  · have hm_lt : m < M₀ := not_le.mp hm
    have hc_le : c_good ≤ c_fin m :=
      Finset.min'_le S_low (c_fin m)
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm_lt, rfl⟩)))
    have hle : ∀ u : ℝ, 0 ≤ u → c_good * u ≤ c_fin m * u :=
      fun _ hu => mul_le_mul_of_nonneg_right hc_le hu
    exact ⟨hT_fin_lo m, hT_fin_hi m, hT_fin_half m,
      fun x hx1 hx2 => (hle _ (Real.exp_pos _).le).trans (hT_fin_hor m x hx1 hx2),
      fun y hy => ⟨(hle _ (Real.exp_pos _).le).trans (hT_fin_vert m y hy).1,
        (hle _ (Real.exp_pos _).le).trans (hT_fin_vert m y hy).2⟩⟩


/-- Product of powers lower bound: if `0 < b ≤ 1` and `b ≤ f z w` for all `z, w ∈ Z`, then
`b ^ ((∑ z ∈ Z, mult z) ^ 2) ≤ ∏ z ∈ Z, ∏ w ∈ Z, (f z w) ^ (mult z * mult w)`. -/
private lemma pow_sum_sq_le_prod_pow {Z : Finset ℂ} {mult : ℂ → ℕ} {f : ℂ → ℂ → ℝ} {b : ℝ}
    (hb0 : 0 < b) (_hb1 : b ≤ 1) (hf : ∀ z ∈ Z, ∀ w ∈ Z, b ≤ f z w) :
    b ^ ((∑ z ∈ Z, mult z) ^ 2) ≤ ∏ z ∈ Z, ∏ w ∈ Z, (f z w) ^ (mult z * mult w) := by
  have hsum_sq : (∑ z ∈ Z, mult z) ^ 2 = ∑ z ∈ Z, ∑ w ∈ Z, mult z * mult w := by
    rw [sq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => Finset.mul_sum Z mult (mult z)
  rw [hsum_sq]
  have hprod_b : b ^ (∑ z ∈ Z, ∑ w ∈ Z, mult z * mult w) =
      ∏ z ∈ Z, ∏ w ∈ Z, b ^ (mult z * mult w) := by
    have houter : ∀ s : Finset ℂ,
        b ^ (∑ z ∈ s, ∑ w ∈ Z, mult z * mult w) =
          ∏ z ∈ s, b ^ (∑ w ∈ Z, mult z * mult w) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert z s hz ih => rw [Finset.sum_insert hz, pow_add, ih, Finset.prod_insert hz]
    have hinner : ∀ z : ℂ, ∀ s : Finset ℂ,
        b ^ (∑ w ∈ s, mult z * mult w) = ∏ w ∈ s, b ^ (mult z * mult w) := by
      intro z s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert w s hw ih => rw [Finset.sum_insert hw, pow_add, ih, Finset.prod_insert hw]
    rw [houter Z]
    exact Finset.prod_congr rfl fun z _ => hinner z Z
  rw [hprod_b]
  refine Finset.prod_le_prod (fun z _ => Finset.prod_nonneg fun w _ => pow_nonneg hb0.le _)
    fun z hz => Finset.prod_le_prod (fun w _ => pow_nonneg hb0.le _) fun w hw =>
      pow_le_pow_left₀ hb0.le (hf z hz w hw) _

/-- **Reusable shifted-rectangle Rouché + Newton–Girard stabilization core.**
Applies identically to cumulative `c = 0` windows (`§3`) and centered `c = 1/2 + i(y₁+y₂)/2` unit
windows (`§4`). -/
theorem pairDiffPoly_rouche_stabilization_core
    {z₁ z₂ c : ℂ} {Z_xi : Finset ℂ} {μ R H_span M_strip : ℝ} {n_star S_max N : ℕ}
    (hre₁ : z₁.re = -1 / 2) (hre₂ : z₂.re = 3 / 2) (him : z₁.im ≤ z₂.im)
    (hμ_pos : 0 < μ) (hμ_le : μ ≤ 1) (hR1 : 1 ≤ R) (hH1 : 1 ≤ H_span) (hM1 : 1 ≤ M_strip)
    (hspan : z₂.im - z₁.im ≤ H_span)
    (hstrip : ∀ z : ℂ, |z.re| ≤ 2 →
      ‖_root_.RHTower.xi z‖ ≤ M_strip ∧ ‖deriv _root_.RHTower.xi z‖ ≤ M_strip)
    (hμ_bdry : ∀ t : ℝ, μ ≤ ‖_root_.RHTower.xi (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t)‖)
    (hR_bdry : ∀ t : ℝ, ‖_root_.RHTower.rectangleBoundaryPath z₁ z₂ t - c‖ ≤ R)
    (hZ_rad : ∀ w ∈ Z_xi, ‖w - c‖ ≤ R)
    (hxi_moments : ∀ r : ℕ,
      (2 * Real.pi * I)⁻¹ *
        _root_.RHTower.rectIntegral (fun z => (z - c) ^ r * logDeriv _root_.RHTower.xi z) z₁ z₂ =
      ∑ w ∈ Z_xi, ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * (w - c) ^ r)
    (hn6 : 6 ≤ n_star) (hnS : n_star ≤ S_max)
    (havoid : ∀ z ∈ Z_xi, ∀ w ∈ Z_xi,
      1 / (8 * (S_max : ℝ) ^ 3) ≤ |zhukovskyEllipseForm n_star (z - w) - 1|)
    (hN_tail : thetaStripTailBound N ≤ μ / 2)
    (hN_half : (4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N ≤ 1 / 2)
    (hN_rouche :
      let d := ∑ w ∈ Z_xi, (analyticOrderAt _root_.RHTower.xi w).toNat
      4 * ((4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N) *
        (((d + 1 : ℕ) : ℝ) ^ 4) * (896 * R * (S_max : ℝ) ^ 4) ^ (d ^ 2) < 1) :
    let d := ∑ w ∈ Z_xi, (analyticOrderAt _root_.RHTower.xi w).toNat
    let s_N : ℕ → ℂ := fun r =>
      (2 * Real.pi * I)⁻¹ *
        _root_.RHTower.rectIntegral
          (fun z => (z - c) ^ r *
            (-_root_.RHTower.finiteThetaFirstMoment N z /
              _root_.RHTower.finiteThetaAmplitude N z)) z₁ z₂
    let P_N := pairDiffPoly d s_N
    (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t) ≠ 0) ∧
    s_N 0 = (d : ℂ) ∧
    Nat.floor (s_N 0).re = d ∧
    (∀ u : HTGeometry.UnitCircle, (P_N.eval (zhukovskyLoop n_star u)) ^ 2 ≠ 0) ∧
    _root_.RHTower.windingNumber
      (fun θ => (P_N.eval (zhukovskyLoop n_star (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) =
      2 * ∑ z ∈ Z_xi, ∑ w ∈ Z_xi,
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
          ((analyticOrderAt _root_.RHTower.xi w).toNat : ℤ) *
          (if zhukovskyEllipseForm n_star (z - w) < 1 then 1 else 0) := by
  intro d s_N P_N
  obtain ⟨hamp_nz, hr0_raw, hpert⟩ := rectIntegral_shifted_powerSum_perturbation
    hre₁ hre₂ him hμ_pos hμ_le hR1 hH1 hM1 hspan hstrip hμ_bdry hR_bdry hN_tail
  have hs0_eq : s_N 0 = (d : ℂ) := by
    have hN0 : s_N 0 = (2 * Real.pi * I)⁻¹ *
        _root_.RHTower.rectIntegral
          (fun z => -_root_.RHTower.finiteThetaFirstMoment N z /
            _root_.RHTower.finiteThetaAmplitude N z) z₁ z₂ := by
      dsimp only [s_N]; simp only [pow_zero, one_mul]
    have hxi0 := hxi_moments 0
    simp only [pow_zero, mul_one, one_mul] at hxi0
    rw [hN0, hr0_raw, hxi0, Nat.cast_sum]
  have hfloor : Nat.floor (s_N 0).re = d := by
    rw [hs0_eq, Complex.natCast_re]
    exact (Nat.floor_eq_iff (Nat.cast_nonneg d)).mpr ⟨le_rfl, by linarith⟩
  let mult : ℂ → ℕ := fun w => (analyticOrderAt _root_.RHTower.xi w).toNat
  let s_xi : ℕ → ℂ := fun r => ∑ w ∈ Z_xi, (mult w : ℂ) * (w - c) ^ r
  let Q_xi : Polynomial ℂ := pairDiffPoly d s_xi
  have hQ_eval : ∀ x : ℂ, Q_xi.eval x =
      ∏ z ∈ Z_xi, ∏ w ∈ Z_xi, (x - (z - w)) ^ (mult z * mult w) := by
    intro x
    have he := eval_pairDiffPoly_eq_finset_prod Z_xi (fun w => w - c) mult rfl
      (fun _ _ _ => rfl) x
    dsimp only [Q_xi]
    rw [he]
    refine Finset.prod_congr rfl fun z _ => Finset.prod_congr rfl fun w _ => ?_
    rw [show (z - c) - (w - c) = z - w by ring]
  have hS_ge6 : (6 : ℝ) ≤ (S_max : ℝ) := by exact_mod_cast (hn6.trans hnS)
  have hη_pos : 0 < 1 / (8 * (S_max : ℝ) ^ 3) := by positivity
  have hη_le1 : 1 / (8 * (S_max : ℝ) ^ 3) ≤ 1 := by
    have hS3_ge1 : (1 : ℝ) ≤ (S_max : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    exact div_le_one_of_le₀ (by linarith) (by positivity)
  have hell_ne1 : ∀ z ∈ Z_xi, ∀ w ∈ Z_xi, zhukovskyEllipseForm n_star (z - w) ≠ 1 := by
    intro z hz w hw h1
    have hg := havoid z hz w hw
    rw [h1, sub_self, abs_zero] at hg
    linarith
  obtain ⟨hQ_nz, hQ_wind, _⟩ := exists_birkhoffSzego_of_prod_eval hQ_eval hell_ne1
  -- Lower bound `‖Q_xi.eval (zhukovskyLoop n_star u)‖ ≥ (56 * S_max ^ 4)⁻¹ ^ (d ^ 2)`.
  have hstage_eq : (zhukovskyStage n_star : ℝ) = (n_star : ℝ) := by
    exact_mod_cast zhukovskyStage_eq_self hn6
  have hn_le_S : (n_star : ℝ) ≤ (S_max : ℝ) := by exact_mod_cast hnS
  have hpair_lo : ∀ u : HTGeometry.UnitCircle, ∀ z ∈ Z_xi, ∀ w ∈ Z_xi,
      (56 * (S_max : ℝ) ^ 4)⁻¹ ≤ ‖zhukovskyLoop n_star u - (z - w)‖ := by
    intro u z hz w hw
    have hg := norm_zhukovskyLoop_sub_ge_of_ellipse_gap hη_pos hη_le1 (havoid z hz w hw) u
    rw [hstage_eq] at hg
    have hstep : (56 * (S_max : ℝ) ^ 4)⁻¹ ≤
        (1 / (8 * (S_max : ℝ) ^ 3)) / (7 * (n_star : ℝ)) := by
      have hn_pos : (0 : ℝ) < (n_star : ℝ) := by exact_mod_cast (show 0 < n_star by omega)
      rw [div_div, one_div, inv_le_inv₀ (by positivity) (by positivity)]
      calc 8 * (S_max : ℝ) ^ 3 * (7 * (n_star : ℝ))
          ≤ 8 * (S_max : ℝ) ^ 3 * (7 * (S_max : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 56 * (S_max : ℝ) ^ 4 := by ring
    exact hstep.trans hg
  have hQ_lo : ∀ u : HTGeometry.UnitCircle,
      ((56 * (S_max : ℝ) ^ 4)⁻¹) ^ (d ^ 2) ≤ ‖Q_xi.eval (zhukovskyLoop n_star u)‖ := by
    intro u
    rw [hQ_eval]
    have hprod_norm : ‖∏ z ∈ Z_xi, ∏ w ∈ Z_xi,
          (zhukovskyLoop n_star u - (z - w)) ^ (mult z * mult w)‖ =
        ∏ z ∈ Z_xi, ∏ w ∈ Z_xi, ‖zhukovskyLoop n_star u - (z - w)‖ ^ (mult z * mult w) := by
      rw [norm_prod]
      refine Finset.prod_congr rfl fun z _ => ?_
      rw [norm_prod]
      exact Finset.prod_congr rfl fun w _ => norm_pow _ _
    rw [hprod_norm]
    have hS4_ge1 : (1 : ℝ) ≤ (S_max : ℝ) ^ 4 := one_le_pow₀ (by linarith)
    exact pow_sum_sq_le_prod_pow (by positivity)
      (inv_le_one_of_one_le₀ (by linarith)) (hpair_lo u)
  -- Upper bound `‖P_N.eval (zhukovskyLoop n_star u) - Q_xi.eval (zhukovskyLoop n_star u)‖`.
  have happrox : ∀ u : HTGeometry.UnitCircle,
      ‖P_N.eval (zhukovskyLoop n_star u) - Q_xi.eval (zhukovskyLoop n_star u)‖ <
        ‖Q_xi.eval (zhukovskyLoop n_star u)‖ := by
    intro u
    rcases eq_or_ne d 0 with hd0 | hd_ne
    · have hPN0 : P_N = pairDiffPoly 0 s_N := by dsimp only [P_N]; rw [hd0]
      have hQX0 : Q_xi = pairDiffPoly 0 s_xi := by dsimp only [Q_xi]; rw [hd0]
      have h1 : (pairDiffPoly 0 s_N).eval (zhukovskyLoop n_star u) =
          (pairDiffPoly 0 s_xi).eval (zhukovskyLoop n_star u) := by
        simp [pairDiffPoly, newtonPoly, newtonElem]
      rw [hPN0, hQX0, h1, sub_self, norm_zero]
      have hQ_nz_u := hQ_nz u
      rw [hQX0] at hQ_nz_u
      exact norm_pos_iff.mpr hQ_nz_u
    · have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd_ne
      have hd1_real : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      set ε_lip : ℝ := (4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N
      have hε_nn : 0 ≤ ε_lip := by
        dsimp only [ε_lip]; exact mul_nonneg (by positivity) (thetaStripTailBound_nonneg N)
      have hs_xi_bd : ∀ r : ℕ, 1 ≤ r → r ≤ d ^ 2 → ‖s_xi r‖ ≤ (d : ℝ) * R ^ r := by
        intro r _ _
        calc ‖∑ w ∈ Z_xi, (mult w : ℂ) * (w - c) ^ r‖
            ≤ ∑ w ∈ Z_xi, ‖(mult w : ℂ) * (w - c) ^ r‖ := norm_sum_le _ _
          _ ≤ ∑ w ∈ Z_xi, (mult w : ℝ) * R ^ r := by
              refine Finset.sum_le_sum fun w hw => ?_
              rw [norm_mul, Complex.norm_natCast, norm_pow]
              exact mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (norm_nonneg _) (hZ_rad w hw) r) (Nat.cast_nonneg _)
          _ = (d : ℝ) * R ^ r := by rw [← Finset.sum_mul, ← Nat.cast_sum]
      have hs_diff_R : ∀ r : ℕ, 1 ≤ r → r ≤ d ^ 2 → ‖s_N r - s_xi r‖ ≤ ε_lip * R ^ r := by
        intro r _ _
        have hp := hpert r
        rw [hxi_moments r] at hp
        exact hp.trans_eq (by dsimp only [ε_lip]; ring)
      have h2R1 : 1 ≤ 2 * R := by linarith
      have hpow2 : ∀ r : ℕ, 1 ≤ r → 2 * R ^ r ≤ (2 * R) ^ r := by
        intro r hr
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Nat.pow_le_pow_right (by omega) hr : 2 ^ 1 ≤ 2 ^ r))
          (pow_nonneg (by linarith) r)
      have hs_N_2R : ∀ r : ℕ, 1 ≤ r → r ≤ d ^ 2 → ‖s_N r‖ ≤ (d : ℝ) * (2 * R) ^ r := by
        intro r hr1 hr2
        have htri : ‖s_N r‖ ≤ ‖s_xi r‖ + ‖s_N r - s_xi r‖ := by
          have := norm_add_le (s_xi r) (s_N r - s_xi r)
          simpa only [add_sub_cancel] using this
        have h1 := hs_xi_bd r hr1 hr2
        have h2 := (hs_diff_R r hr1 hr2).trans
          (mul_le_mul_of_nonneg_right hN_half (pow_nonneg (by linarith) r))
        calc ‖s_N r‖
            ≤ (d : ℝ) * R ^ r + (1 / 2) * R ^ r := htri.trans (add_le_add h1 h2)
          _ ≤ (d : ℝ) * (2 * R ^ r) := by nlinarith [pow_nonneg (show 0 ≤ R by linarith) r]
          _ ≤ (d : ℝ) * (2 * R) ^ r := mul_le_mul_of_nonneg_left (hpow2 r hr1) (Nat.cast_nonneg d)
      have hs_xi_2R : ∀ r : ℕ, 1 ≤ r → r ≤ d ^ 2 → ‖s_xi r‖ ≤ (d : ℝ) * (2 * R) ^ r := by
        intro r hr1 hr2
        exact (hs_xi_bd r hr1 hr2).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) (by linarith) r) (Nat.cast_nonneg d))
      have hs_diff_2R : ∀ r : ℕ, 1 ≤ r → r ≤ d ^ 2 →
          ‖s_N r - s_xi r‖ ≤ ε_lip * (d : ℝ) * (2 * R) ^ r := by
        intro r hr1 hr2
        calc ‖s_N r - s_xi r‖
            ≤ ε_lip * R ^ r := hs_diff_R r hr1 hr2
          _ ≤ (ε_lip * (d : ℝ)) * (2 * R) ^ r :=
              mul_le_mul (by nlinarith) (pow_le_pow_left₀ (by linarith) (by linarith) r)
                (pow_nonneg (by linarith) r) (by positivity)
          _ = ε_lip * (d : ℝ) * (2 * R) ^ r := by ring
      have hlip := norm_pairDiffPoly_eval_sub_le_on_zhukovsky h2R1 hε_nn
        hs_N_2R hs_xi_2R hs_diff_2R n_star u
      have hd_pow : (d : ℝ) ^ 4 ≤ ((d + 1 : ℕ) : ℝ) ^ 4 :=
        pow_le_pow_left₀ (Nat.cast_nonneg d) (by exact_mod_cast (Nat.le_succ d)) 4
      have h16_eq : (8 * (2 * R)) ^ (d ^ 2) * (56 * (S_max : ℝ) ^ 4) ^ (d ^ 2) =
          (896 * R * (S_max : ℝ) ^ 4) ^ (d ^ 2) := by
        rw [← mul_pow]; congr 1; ring
      have hprod_lt :
          (4 * ε_lip * ((d : ℝ) ^ 4) * (8 * (2 * R)) ^ (d ^ 2)) *
            (56 * (S_max : ℝ) ^ 4) ^ (d ^ 2) < 1 := by
        calc (4 * ε_lip * ((d : ℝ) ^ 4) * (8 * (2 * R)) ^ (d ^ 2)) *
                (56 * (S_max : ℝ) ^ 4) ^ (d ^ 2)
            = 4 * ε_lip * ((d : ℝ) ^ 4) *
                ((8 * (2 * R)) ^ (d ^ 2) * (56 * (S_max : ℝ) ^ 4) ^ (d ^ 2)) := by ring
          _ ≤ 4 * ε_lip * (((d + 1 : ℕ) : ℝ) ^ 4) *
                (896 * R * (S_max : ℝ) ^ 4) ^ (d ^ 2) := by
              rw [h16_eq]
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left hd_pow (by positivity)
          _ < 1 := hN_rouche
      have hpos_pow : 0 < (56 * (S_max : ℝ) ^ 4) ^ (d ^ 2) := by positivity
      have hlt_inv : 4 * ε_lip * ((d : ℝ) ^ 4) * (8 * (2 * R)) ^ (d ^ 2) <
          ((56 * (S_max : ℝ) ^ 4)⁻¹) ^ (d ^ 2) := by
        rw [inv_pow, ← one_div]
        exact (lt_div_iff₀ hpos_pow).mpr hprod_lt
      exact (hlip.trans_lt hlt_inv).trans_le (hQ_lo u)
  obtain ⟨hPN_sq_nz, hPN_wind⟩ := windingNumber_zhukovsky_poly_sq_of_approx n_star P_N Q_xi
    hQ_nz happrox
  refine ⟨hamp_nz, hs0_eq, hfloor, hPN_sq_nz, ?_⟩
  rw [hPN_wind, hQ_wind]
  congr 1
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hlt : zhukovskyEllipseForm n_star (z - w) < 1 <;> simp [hlt, mult]


private lemma rectangleBoundaryPath_on_edges' (z₁ z₂ : ℂ) (t : ℝ) :
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t).re = z₁.re ∨
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t).re = z₂.re ∨
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t).im = z₁.im ∨
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t).im = z₂.im := by
  unfold _root_.RHTower.rectangleBoundaryPath _root_.RHTower.rectangleEdgePath
  split_ifs
  · right; right; left; simp
  · right; left; simp
  · right; right; right; simp
  · left; simp

/-- Pure real-analytic Rouché budget selector for the `O(m log²(m + S))` cumulative prefix. -/
private theorem exists_cumulative_prefix_constant
    {c_good M_strip C_loc C_e : ℝ}
    (hc_good_pos : 0 < c_good) (hM1 : 1 ≤ M_strip) (hC_loc1 : 1 ≤ C_loc) (hC_env1 : 1 ≤ C_e)
    (hC_env_tail : ∀ N : ℕ, thetaStripTailBound N ≤ C_e * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) :
    ∃ K_cum : ℕ, 1 ≤ K_cum ∧ ∀ (m S d N : ℕ),
      (d : ℝ) ≤ C_loc * ((m + 1 : ℕ) : ℝ) * Real.log ((m + 4 : ℕ) : ℝ) →
      K_cum * (m + 1) * (Nat.ceil (Real.log ((m + S + 4 : ℕ) : ℝ)) + 1) ^ 2 ≤ N →
      let μ : ℝ := c_good * Real.exp (-((m + 1 : ℕ) : ℝ))
      let H_span : ℝ := ((m + 2 : ℕ) : ℝ)
      let R : ℝ := ((m + 4 : ℕ) : ℝ)
      let S_max : ℕ := max S 6 + 2 * d ^ 2
      thetaStripTailBound N ≤ μ / 2 ∧
      (4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N ≤ 1 / 2 ∧
      4 * ((4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N) *
        (((d + 1 : ℕ) : ℝ) ^ 4) * (896 * R * (S_max : ℝ) ^ 4) ^ (d ^ 2) < 1 := by
  let K_pre : ℝ := 8 * (2 * M_strip + 1) * C_e / c_good ^ 2 + 1
  have hK_pre1 : 1 ≤ K_pre := by dsimp only [K_pre]; exact le_add_of_nonneg_left (by positivity)
  have hK_pre_def : 8 * (2 * M_strip + 1) * C_e / c_good ^ 2 ≤ K_pre := by
    dsimp only [K_pre]; linarith
  let K_base : ℝ := 896 * (6 + 2 * C_loc ^ 2) ^ 4
  have hK_base1 : 1 ≤ K_base := by
    dsimp only [K_base]
    have hp : (1 : ℝ) ≤ (6 + 2 * C_loc ^ 2) ^ 4 := one_le_pow₀ (by linarith [sq_nonneg C_loc])
    linarith
  have hK_base_def : 896 * (6 + 2 * C_loc ^ 2) ^ 4 = K_base := rfl
  have hCloc4 : (1 : ℝ) ≤ (C_loc + 1) ^ 4 := one_le_pow₀ (by linarith)
  have hlog4K_nonneg : 0 ≤ Real.log (4 * K_pre * (C_loc + 1) ^ 4) := by
    refine Real.log_nonneg ?_
    have hm := mul_le_mul_of_nonneg_left hCloc4 (by positivity : (0 : ℝ) ≤ 4 * K_pre)
    linarith
  let B_tot : ℝ :=
    (1 + |Real.log (2 * C_e / c_good)|) +
    (3 + Real.log (2 * K_pre)) +
    (Real.log (4 * K_pre * (C_loc + 1) ^ 4) + 7 + C_loc ^ 2 * (Real.log K_base + 17)) + 2
  have hB_tot_pos : 2 ≤ B_tot := by
    dsimp only [B_tot]
    have h1 : 0 ≤ Real.log (2 * K_pre) := Real.log_nonneg (by linarith)
    have h4 : 0 ≤ C_loc ^ 2 * (Real.log K_base + 17) :=
      mul_nonneg (sq_nonneg _) (by linarith [Real.log_nonneg hK_base1])
    linarith [abs_nonneg (Real.log (2 * C_e / c_good)), hlog4K_nonneg]
  have hB_part1 : 1 + |Real.log (2 * C_e / c_good)| ≤ B_tot := by
    dsimp only [B_tot]
    have h1 : 0 ≤ Real.log (2 * K_pre) := Real.log_nonneg (by linarith)
    have h3 : 0 ≤ C_loc ^ 2 * (Real.log K_base + 17) :=
      mul_nonneg (sq_nonneg _) (by linarith [Real.log_nonneg hK_base1])
    linarith [hlog4K_nonneg]
  have hB_part2 : 3 + Real.log (2 * K_pre) ≤ B_tot := by
    dsimp only [B_tot]
    have h3 : 0 ≤ C_loc ^ 2 * (Real.log K_base + 17) :=
      mul_nonneg (sq_nonneg _) (by linarith [Real.log_nonneg hK_base1])
    linarith [abs_nonneg (Real.log (2 * C_e / c_good)), hlog4K_nonneg]
  have hB_part3 :
      Real.log (4 * K_pre * (C_loc + 1) ^ 4) + 7 +
        C_loc ^ 2 * (Real.log K_base + 17) + 1 ≤ B_tot := by
    dsimp only [B_tot]
    linarith [abs_nonneg (Real.log (2 * C_e / c_good)),
      Real.log_nonneg (show 1 ≤ 2 * K_pre by linarith)]
  let C_cum : ℕ := Nat.ceil (Real.sqrt B_tot) + 1
  have hC_cum1 : 1 ≤ C_cum := by dsimp only [C_cum]; omega
  have hC_cum_sq : B_tot ≤ (C_cum : ℝ) ^ 2 := by
    have h1 : Real.sqrt B_tot ≤ (C_cum : ℝ) := by
      calc Real.sqrt B_tot ≤ (Nat.ceil (Real.sqrt B_tot) : ℝ) := Nat.le_ceil _
        _ ≤ (C_cum : ℝ) := by dsimp only [C_cum]; push_cast; linarith
    calc B_tot = (Real.sqrt B_tot) ^ 2 := (Real.sq_sqrt (by linarith)).symm
      _ ≤ (C_cum : ℝ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  generalize C_cum = K_cum at hC_cum1 hC_cum_sq
  generalize B_tot = B_t at hB_tot_pos hC_cum_sq hB_part1 hB_part2 hB_part3
  generalize K_base = K_b at hK_base1 hK_base_def hB_part3
  generalize K_pre = K_p at hK_pre1 hK_pre_def hlog4K_nonneg hB_part2 hB_part3
  clear C_cum B_tot K_base K_pre
  have hCe_pos : 0 < C_e := by linarith only [hC_env1]
  have hKp_pos : 0 < K_p := by linarith only [hK_pre1]
  have hKb_pos : 0 < K_b := by linarith only [hK_base1]
  have hBt_pos : 0 < B_t := by linarith only [hB_tot_pos]
  have hCloc_pos : 0 < C_loc := by linarith only [hC_loc1]
  have hM_pos : 0 < M_strip := by linarith only [hM1]
  have hKcum_pos : 0 < (K_cum : ℝ) := by exact_mod_cast (show 0 < K_cum by omega)
  refine ⟨K_cum, hC_cum1, fun m S d N hd_raw hN => ?_⟩
  intro μ H_span R S_max
  set L : ℝ := Real.log ((m + S + 4 : ℕ) : ℝ)
  have hR_pos : 0 < R := by dsimp only [R]; exact_mod_cast (show 0 < m + 4 by omega)
  have hL_ge1 : 1 ≤ L := by
    dsimp only [L]
    have he4 : Real.exp 1 ≤ ((m + S + 4 : ℕ) : ℝ) := by
      have h4 : (4 : ℝ) ≤ ((m + S + 4 : ℕ) : ℝ) := by exact_mod_cast (show 4 ≤ m + S + 4 by omega)
      linarith [Real.exp_one_lt_d9]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he4
  have hm1_ge1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos m)
  have hL_ceil : L ≤ ((Nat.ceil L + 1 : ℕ) : ℝ) := by
    calc L ≤ (Nat.ceil L : ℝ) := Nat.le_ceil L
      _ ≤ ((Nat.ceil L + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hN1_ge : (K_cum : ℝ) * ((m + 1 : ℕ) : ℝ) * L ^ 2 ≤ ((N + 1 : ℕ) : ℝ) := by
    have hL_sq : L ^ 2 ≤ ((Nat.ceil L + 1 : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith only [hL_ge1]) hL_ceil 2
    have hnat : ((K_cum * (m + 1) * (Nat.ceil L + 1) ^ 2 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (hN.trans (Nat.le_succ N))
    calc (K_cum : ℝ) * ((m + 1 : ℕ) : ℝ) * L ^ 2
        ≤ (K_cum : ℝ) * ((m + 1 : ℕ) : ℝ) * ((Nat.ceil L + 1 : ℕ) : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hL_sq (by positivity)
      _ = ((K_cum * (m + 1) * (Nat.ceil L + 1) ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((N + 1 : ℕ) : ℝ) := hnat
  have hN1_sq : B_t * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4 ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
    have hp := pow_le_pow_left₀ (by positivity) hN1_ge 2
    calc B_t * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4
        ≤ (K_cum : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hC_cum_sq (by positivity)
      _ = ((K_cum : ℝ) * ((m + 1 : ℕ) : ℝ) * L ^ 2) ^ 2 := by ring
      _ ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := hp
  have hd_le : (d : ℝ) ≤ C_loc * ((m + 1 : ℕ) : ℝ) * L := by
    have hlog_le : Real.log ((m + 4 : ℕ) : ℝ) ≤ L :=
      Real.log_le_log (by exact_mod_cast (show 0 < m + 4 by omega))
        (by exact_mod_cast (show m + 4 ≤ m + S + 4 by omega))
    exact hd_raw.trans (mul_le_mul_of_nonneg_left hlog_le (by positivity))
  have htail_env : thetaStripTailBound N ≤ C_e * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) :=
    hC_env_tail N
  have hm1_sq_ge1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := one_le_pow₀ hm1_ge1
  have hL4_ge1 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL_ge1
  have hprod_ge1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4 := by
    simpa using mul_le_mul hm1_sq_ge1 hL4_ge1 zero_le_one (by positivity)
  have hm1_le_sq : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
    calc ((m + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) * 1 := (mul_one _).symm
      _ ≤ ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hm1_ge1 (by positivity)
      _ = ((m + 1 : ℕ) : ℝ) ^ 2 := (sq _).symm
  have hm_le_prod : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4 := by
    calc ((m + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) * 1 := (mul_one _).symm
      _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4 :=
          mul_le_mul hm1_le_sq hL4_ge1 zero_le_one (by positivity)
  have hN_tail : thetaStripTailBound N ≤ μ / 2 := by
    have hexp_arg : -((N + 1 : ℕ) : ℝ) ^ 2 ≤
        Real.log (c_good / (2 * C_e)) - ((m + 1 : ℕ) : ℝ) := by
      have hlog_abs : |Real.log (2 * C_e / c_good)| = |Real.log (c_good / (2 * C_e))| := by
        rw [show c_good / (2 * C_e) = (2 * C_e / c_good)⁻¹ by rw [inv_div], Real.log_inv, abs_neg]
      have hsub : ((m + 1 : ℕ) : ℝ) + |Real.log (2 * C_e / c_good)| ≤
          (1 + |Real.log (2 * C_e / c_good)|) * (((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4) := by
        have habs_le : |Real.log (2 * C_e / c_good)| ≤
            |Real.log (2 * C_e / c_good)| * (((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4) :=
          le_mul_of_one_le_right (abs_nonneg _) hprod_ge1
        linarith only [hm_le_prod, habs_le]
      have hB1_mul : (1 + |Real.log (2 * C_e / c_good)|) * (((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4) ≤
          B_t * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4 := by
        have hm := mul_le_mul_of_nonneg_right hB_part1 (zero_le_one.trans hprod_ge1)
        exact hm.trans_eq (by ring)
      have hpart_le : ((m + 1 : ℕ) : ℝ) + |Real.log (2 * C_e / c_good)| ≤
          ((N + 1 : ℕ) : ℝ) ^ 2 := hsub.trans (hB1_mul.trans hN1_sq)
      linarith only [hpart_le, neg_abs_le (Real.log (c_good / (2 * C_e))), hlog_abs]
    calc thetaStripTailBound N
        ≤ C_e * Real.exp (Real.log (c_good / (2 * C_e)) - ((m + 1 : ℕ) : ℝ)) :=
          htail_env.trans
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) hCe_pos.le)
      _ = μ / 2 := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by positivity)]
          dsimp only [μ]
          have hCe_ne : C_e ≠ 0 := hCe_pos.ne'
          field_simp [hCe_ne]
  have hpre_bound : (4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N ≤
      K_p * Real.exp (3 * ((m + 1 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ) ^ 2) := by
    have hH_le : H_span ≤ 2 * Real.exp ((m + 1 : ℕ) : ℝ) := by
      have h1 : H_span ≤ 2 * ((m + 1 : ℕ) : ℝ) := by dsimp only [H_span]; push_cast; linarith
      have h2 : ((m + 1 : ℕ) : ℝ) ≤ Real.exp ((m + 1 : ℕ) : ℝ) := by
        linarith [Real.add_one_le_exp ((m + 1 : ℕ) : ℝ)]
      linarith only [h1, h2]
    have hμ_sq : μ ^ 2 = c_good ^ 2 * Real.exp (-2 * ((m + 1 : ℕ) : ℝ)) := by
      dsimp only [μ]
      rw [mul_pow, ← Real.exp_nat_mul,
        show ((2 : ℕ) : ℝ) * -((m + 1 : ℕ) : ℝ) = -2 * ((m + 1 : ℕ) : ℝ) by push_cast; ring]
    calc (4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N
        ≤ (4 * (2 * M_strip + 1) * (2 * Real.exp ((m + 1 : ℕ) : ℝ)) /
            (c_good ^ 2 * Real.exp (-2 * ((m + 1 : ℕ) : ℝ)))) *
            (C_e * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) := by
          rw [hμ_sq]
          refine mul_le_mul ?_ htail_env (thetaStripTailBound_nonneg N) (by positivity)
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hH_le (by positivity)) (by positivity)
      _ = (8 * (2 * M_strip + 1) * C_e / c_good ^ 2) *
            (Real.exp ((m + 1 : ℕ) : ℝ) / Real.exp (-2 * ((m + 1 : ℕ) : ℝ)) *
              Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) := by
          field_simp [hc_good_pos.ne']; ring
      _ = (8 * (2 * M_strip + 1) * C_e / c_good ^ 2) *
            Real.exp (3 * ((m + 1 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ) ^ 2) := by
          rw [← Real.exp_sub, ← Real.exp_add,
            show ((m + 1 : ℕ) : ℝ) - -2 * ((m + 1 : ℕ) : ℝ) + -((N + 1 : ℕ) : ℝ) ^ 2 =
              3 * ((m + 1 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ) ^ 2 by ring]
      _ ≤ K_p * Real.exp (3 * ((m + 1 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hK_pre_def (Real.exp_pos _).le
  have hN_half : (4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N ≤ 1 / 2 := by
    have hexp_arg : 3 * ((m + 1 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ) ^ 2 ≤ -Real.log (2 * K_p) := by
      have h1 : 3 * ((m + 1 : ℕ) : ℝ) + Real.log (2 * K_p) ≤
          (3 + Real.log (2 * K_p)) * (((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4) := by
        have hlog_le : Real.log (2 * K_p) ≤
            Real.log (2 * K_p) * (((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4) :=
          le_mul_of_one_le_right (Real.log_nonneg (by linarith only [hK_pre1])) hprod_ge1
        linarith only [hm_le_prod, hlog_le]
      have hB2_mul : (3 + Real.log (2 * K_p)) * (((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4) ≤
          B_t * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4 := by
        have hm := mul_le_mul_of_nonneg_right hB_part2 (zero_le_one.trans hprod_ge1)
        exact hm.trans_eq (by ring)
      have h2 := h1.trans (hB2_mul.trans hN1_sq)
      linarith only [h2]
    calc (4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N
        ≤ K_p * Real.exp (-Real.log (2 * K_p)) :=
          hpre_bound.trans
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) hKp_pos.le)
      _ = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          have hKp_ne : K_p ≠ 0 := hKp_pos.ne'
          field_simp [hKp_ne]
  have hN_rouche :
      4 * ((4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N) *
        (((d + 1 : ℕ) : ℝ) ^ 4) * (896 * R * (S_max : ℝ) ^ 4) ^ (d ^ 2) < 1 := by
    have hd1_bound : (((d + 1 : ℕ) : ℝ) ^ 4) ≤
        (C_loc + 1) ^ 4 * Real.exp (4 * ((m + 1 : ℕ) : ℝ) * L) := by
      have h1 : ((d + 1 : ℕ) : ℝ) ≤ (C_loc + 1) * (((m + 1 : ℕ) : ℝ) * L) := by
        have hml1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * L := by
          simpa using mul_le_mul hm1_ge1 hL_ge1 zero_le_one (by positivity)
        have hd_cast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
        rw [hd_cast]
        have hd_mul : (d : ℝ) ≤ C_loc * (((m + 1 : ℕ) : ℝ) * L) := by
          simpa only [mul_assoc] using hd_le
        linarith only [hd_mul, hml1]
      have h2 : ((m + 1 : ℕ) : ℝ) * L ≤ Real.exp (((m + 1 : ℕ) : ℝ) * L) := by
        linarith [Real.add_one_le_exp (((m + 1 : ℕ) : ℝ) * L)]
      have h3 : ((d + 1 : ℕ) : ℝ) ≤ (C_loc + 1) * Real.exp (((m + 1 : ℕ) : ℝ) * L) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      calc (((d + 1 : ℕ) : ℝ) ^ 4)
          ≤ ((C_loc + 1) * Real.exp (((m + 1 : ℕ) : ℝ) * L)) ^ 4 :=
            pow_le_pow_left₀ (by positivity) h3 4
        _ = (C_loc + 1) ^ 4 * Real.exp (4 * ((m + 1 : ℕ) : ℝ) * L) := by
            rw [mul_pow, ← Real.exp_nat_mul,
              show ((4 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * L) = 4 * ((m + 1 : ℕ) : ℝ) * L by
                push_cast; ring]
    have hbase_exp : 896 * R * (S_max : ℝ) ^ 4 ≤ K_b * Real.exp (17 * L) := by
      have hexpL : ((m + S + 4 : ℕ) : ℝ) = Real.exp L :=
        (Real.exp_log (by exact_mod_cast (show 0 < m + S + 4 by omega))).symm
      have hR_exp : R ≤ Real.exp L := by
        rw [← hexpL]; dsimp only [R]
        exact_mod_cast (show m + 4 ≤ m + S + 4 by omega)
      have hS_exp : (S_max : ℝ) ≤ (6 + 2 * C_loc ^ 2) * Real.exp (4 * L) := by
        have hmaxS : (max S 6 : ℝ) ≤ 6 * Real.exp (4 * L) := by
          have hs1 : (max S 6 : ℝ) ≤ 6 * ((m + S + 4 : ℕ) : ℝ) := by
            have hS_le : (S : ℝ) ≤ ((m + S + 4 : ℕ) : ℝ) := by
              exact_mod_cast (show S ≤ m + S + 4 by omega)
            have h4 : (4 : ℝ) ≤ ((m + S + 4 : ℕ) : ℝ) := by
              exact_mod_cast (show 4 ≤ m + S + 4 by omega)
            exact max_le (by linarith only [hS_le, h4]) (by linarith only [h4])
          rw [hexpL] at hs1
          exact hs1.trans (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by linarith only [hL_ge1])) (by norm_num))
        have hd2_exp : 2 * (d : ℝ) ^ 2 ≤ 2 * C_loc ^ 2 * Real.exp (4 * L) := by
          have hm1_exp : ((m + 1 : ℕ) : ℝ) ≤ Real.exp L := by
            rw [← hexpL]; exact_mod_cast (show m + 1 ≤ m + S + 4 by omega)
          have hL_exp : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
          have hd_e : (d : ℝ) ≤ C_loc * Real.exp (2 * L) := by
            calc (d : ℝ) ≤ C_loc * (((m + 1 : ℕ) : ℝ) * L) := by simpa only [mul_assoc] using hd_le
              _ ≤ C_loc * (Real.exp L * Real.exp L) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul hm1_exp hL_exp (by linarith only [hL_ge1]) (Real.exp_pos _).le)
                    hCloc_pos.le
              _ = C_loc * Real.exp (2 * L) := by
                  rw [← Real.exp_add, show L + L = 2 * L by ring]
          have hsq := pow_le_pow_left₀ (Nat.cast_nonneg d) hd_e 2
          calc 2 * (d : ℝ) ^ 2
              ≤ 2 * (C_loc * Real.exp (2 * L)) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
            _ = 2 * C_loc ^ 2 * Real.exp (4 * L) := by
                rw [mul_pow, ← Real.exp_nat_mul]
                have he : ((2 : ℕ) : ℝ) * (2 * L) = 4 * L := by push_cast; ring
                rw [he]; ring
        have hcast_S : (S_max : ℝ) = (max S 6 : ℝ) + 2 * (d : ℝ) ^ 2 := by
          dsimp only [S_max]; push_cast; ring
        rw [hcast_S]; linarith only [hmaxS, hd2_exp]
      calc 896 * R * (S_max : ℝ) ^ 4
          ≤ 896 * Real.exp L * ((6 + 2 * C_loc ^ 2) * Real.exp (4 * L)) ^ 4 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hR_exp (by norm_num))
              (pow_le_pow_left₀ (Nat.cast_nonneg _) hS_exp 4) (by positivity) (by positivity)
        _ = K_b * (Real.exp L * (Real.exp (4 * L)) ^ 4) := by
            rw [← hK_base_def, mul_pow]; ring
        _ = K_b * Real.exp (17 * L) := by
            rw [← Real.exp_nat_mul, ← Real.exp_add,
              show L + ((4 : ℕ) : ℝ) * (4 * L) = 17 * L by push_cast; ring]
    have hpow_d2 : (896 * R * (S_max : ℝ) ^ 4) ^ (d ^ 2) ≤
        Real.exp (C_loc ^ 2 * (Real.log K_b + 17) * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 3) := by
      have h1 : 896 * R * (S_max : ℝ) ^ 4 ≤ Real.exp (Real.log K_b + 17 * L) := by
        rw [Real.exp_add, Real.exp_log hKb_pos]
        exact hbase_exp
      have hbase_nn : 0 ≤ 896 * R * (S_max : ℝ) ^ 4 :=
        mul_nonneg (mul_nonneg (by norm_num) hR_pos.le) (pow_nonneg (Nat.cast_nonneg _) 4)
      have hp := pow_le_pow_left₀ hbase_nn h1 (d ^ 2)
      rw [← Real.exp_nat_mul] at hp
      refine hp.trans (Real.exp_le_exp.mpr ?_)
      have hd2_le : ((d ^ 2 : ℕ) : ℝ) ≤ C_loc ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 2 := by
        have hsq := pow_le_pow_left₀ (Nat.cast_nonneg d) hd_le 2
        have hcast_d2 : ((d ^ 2 : ℕ) : ℝ) = (d : ℝ) ^ 2 := by push_cast; ring
        rw [hcast_d2]
        exact hsq.trans_eq (by ring)
      have hKL : Real.log K_b + 17 * L ≤ (Real.log K_b + 17) * L := by
        have hlog_le : Real.log K_b ≤ Real.log K_b * L :=
          le_mul_of_one_le_right (Real.log_nonneg hK_base1) hL_ge1
        linarith only [hlog_le]
      calc ((d ^ 2 : ℕ) : ℝ) * (Real.log K_b + 17 * L)
          ≤ (C_loc ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 2) * ((Real.log K_b + 17) * L) :=
            mul_le_mul hd2_le hKL
              (by linarith [Real.log_nonneg hK_base1, hL_ge1]) (by positivity)
        _ = C_loc ^ 2 * (Real.log K_b + 17) * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 3 := by ring
    have h4K_pos : 0 < 4 * K_p * (C_loc + 1) ^ 4 := by positivity
    have hprod_le :
        4 * ((4 * (2 * M_strip + 1) * H_span / μ ^ 2) * thetaStripTailBound N) *
          (((d + 1 : ℕ) : ℝ) ^ 4) * (896 * R * (S_max : ℝ) ^ 4) ^ (d ^ 2) ≤
        Real.exp (Real.log (4 * K_p * (C_loc + 1) ^ 4) +
          3 * ((m + 1 : ℕ) : ℝ) + 4 * ((m + 1 : ℕ) : ℝ) * L +
          C_loc ^ 2 * (Real.log K_b + 17) * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 3 -
          ((N + 1 : ℕ) : ℝ) ^ 2) := by
      have hm12 := mul_le_mul
        (mul_le_mul_of_nonneg_left hpre_bound (by norm_num : (0 : ℝ) ≤ 4))
        hd1_bound (by positivity) (by positivity)
      have hm123 := mul_le_mul hm12 hpow_d2 (by positivity) (by positivity)
      refine hm123.trans_eq ?_
      symm
      rw [show Real.log (4 * K_p * (C_loc + 1) ^ 4) +
            3 * ((m + 1 : ℕ) : ℝ) + 4 * ((m + 1 : ℕ) : ℝ) * L +
            C_loc ^ 2 * (Real.log K_b + 17) * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 3 -
            ((N + 1 : ℕ) : ℝ) ^ 2 =
          Real.log (4 * K_p * (C_loc + 1) ^ 4) +
            ((3 * ((m + 1 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ) ^ 2) +
              4 * ((m + 1 : ℕ) : ℝ) * L +
              C_loc ^ 2 * (Real.log K_b + 17) * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 3) by ring]
      rw [Real.exp_add, Real.exp_log h4K_pos, Real.exp_add, Real.exp_add]
      ring
    refine hprod_le.trans_lt (Real.exp_lt_one_iff.mpr ?_)
    set P4 : ℝ := ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 4
    have hP4_ge1 : (1 : ℝ) ≤ P4 := hprod_ge1
    have h_m1_P4 : ((m + 1 : ℕ) : ℝ) ≤ P4 := hm_le_prod
    have h_m1L_P4 : ((m + 1 : ℕ) : ℝ) * L ≤ P4 := by
      dsimp only [P4]
      have hl3 : L ≤ L ^ 4 := by
        have hL3 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL_ge1
        calc L = L * 1 := (mul_one L).symm
          _ ≤ L * L ^ 3 := mul_le_mul_of_nonneg_left hL3 (by linarith only [hL_ge1])
          _ = L ^ 4 := by ring
      exact mul_le_mul hm1_le_sq hl3 (by linarith only [hL_ge1]) (by positivity)
    have h_L3_P4 : ((m + 1 : ℕ) ^ 2 : ℝ) * L ^ 3 ≤ P4 := by
      dsimp only [P4]
      have hL34 : L ^ 3 ≤ L ^ 4 := by
        calc L ^ 3 = L ^ 3 * 1 := (mul_one _).symm
          _ ≤ L ^ 3 * L := mul_le_mul_of_nonneg_left hL_ge1 (by positivity)
          _ = L ^ 4 := by ring
      exact mul_le_mul_of_nonneg_left hL34 (by positivity)
    have hsum_P4 :
        Real.log (4 * K_p * (C_loc + 1) ^ 4) +
          3 * ((m + 1 : ℕ) : ℝ) + 4 * ((m + 1 : ℕ) : ℝ) * L +
          C_loc ^ 2 * (Real.log K_b + 17) * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 3 <
        B_t * P4 := by
      have h1 : Real.log (4 * K_p * (C_loc + 1) ^ 4) ≤
          Real.log (4 * K_p * (C_loc + 1) ^ 4) * P4 :=
        le_mul_of_one_le_right hlog4K_nonneg hP4_ge1
      have h2 : C_loc ^ 2 * (Real.log K_b + 17) * (((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 3) ≤
          C_loc ^ 2 * (Real.log K_b + 17) * P4 :=
        mul_le_mul_of_nonneg_left h_L3_P4
          (mul_nonneg (sq_nonneg _) (by linarith [Real.log_nonneg hK_base1]))
      have hsum_le :
          (Real.log (4 * K_p * (C_loc + 1) ^ 4) + 7 +
            C_loc ^ 2 * (Real.log K_b + 17) + 1) * P4 ≤ B_t * P4 :=
        mul_le_mul_of_nonneg_right hB_part3 (by linarith only [hP4_ge1])
      have hexp_ring :
          (Real.log (4 * K_p * (C_loc + 1) ^ 4) + 7 +
            C_loc ^ 2 * (Real.log K_b + 17) + 1) * P4 =
          Real.log (4 * K_p * (C_loc + 1) ^ 4) * P4 + 3 * P4 + 4 * P4 +
            C_loc ^ 2 * (Real.log K_b + 17) * P4 + P4 := by ring
      have h2' : C_loc ^ 2 * (Real.log K_b + 17) * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 3 ≤
          C_loc ^ 2 * (Real.log K_b + 17) * P4 := by
        simpa only [mul_assoc] using h2
      linarith only [h1, h2', h_m1_P4, h_m1L_P4, hP4_ge1, hsum_le, hexp_ring]
    have hN1_P4 : B_t * P4 ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
      simpa only [P4, mul_assoc] using hN1_sq
    linarith only [hsum_P4, hN1_P4]
  exact ⟨hN_tail, hN_half, hN_rouche⟩

/-- Pigeonhole stage selection and Burnol rectangle moment setup for the cumulative window. -/
private theorem cumulative_window_pigeonhole_and_rect
    {c_good : ℝ} (hc_good_pos : 0 < c_good)
    (hc_good_le_low : c_good ≤ 5026 / 16875 * Real.exp (-Real.pi))
    (m S : ℕ) {T_star : ℝ}
    (_hT_lo : (m : ℝ) ≤ T_star) (hT_hi : T_star ≤ (m : ℝ) + 1) (hT_half : 1 / 2 ≤ T_star)
    (hT_hor : ∀ x : ℝ, -1 ≤ x → x ≤ 2 →
      c_good * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤ ‖_root_.RHTower.xi ((x : ℂ) + (T_star : ℂ) * I)‖)
    (hT_vert : ∀ y : ℝ, |y| ≤ T_star →
      c_good * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤ ‖_root_.RHTower.xi ((3 / 2 : ℂ) + (y : ℂ) * I)‖ ∧
      c_good * Real.exp (-((m + 1 : ℕ) : ℝ)) ≤ ‖_root_.RHTower.xi ((-1 / 2 : ℂ) + (y : ℂ) * I)‖) :
    let Z_xi : Finset ℂ := (_root_.RHTower.stripZeros_finite T_star).toFinset
    let d : ℕ := _root_.RHTower.xiStripWindowTotalOrder T_star
    let S_max : ℕ := max S 6 + 2 * d ^ 2
    ∃ n_star ∈ Finset.Icc (max S 6) S_max,
      6 ≤ n_star ∧
      (∀ z ∈ Z_xi, ∀ w ∈ Z_xi,
        1 / (8 * (S_max : ℝ) ^ 3) ≤ |zhukovskyEllipseForm n_star (z - w) - 1|) ∧
      let T_win : ℝ := T_star + 1 / (2 * (zhukovskyStage n_star : ℝ))
      let z₁ : ℂ := thetaWindowLowerLeft n_star
      let z₂ : ℂ := thetaWindowUpperRight T_win n_star
      let μ : ℝ := c_good * Real.exp (-((m + 1 : ℕ) : ℝ))
      z₁.im ≤ z₂.im ∧
      z₂.im - z₁.im ≤ ((m + 2 : ℕ) : ℝ) ∧
      0 < μ ∧ μ ≤ 1 ∧
      (∀ t : ℝ, μ ≤ ‖_root_.RHTower.xi (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t)‖) ∧
      (∀ t : ℝ, ‖_root_.RHTower.rectangleBoundaryPath z₁ z₂ t - 0‖ ≤ ((m + 4 : ℕ) : ℝ)) ∧
      (∀ w ∈ Z_xi, ‖w - 0‖ ≤ ((m + 4 : ℕ) : ℝ)) ∧
      (∀ r : ℕ,
        (2 * Real.pi * I)⁻¹ *
          _root_.RHTower.rectIntegral (fun z => (z - 0) ^ r * logDeriv _root_.RHTower.xi z) z₁ z₂ =
        ∑ w ∈ Z_xi, ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * (w - 0) ^ r) := by
  intro Z_xi d S_max
  let P_diff : Finset ℂ := (Z_xi ×ˢ Z_xi).image fun p => p.1 - p.2
  have hP_card : P_diff.card ≤ d ^ 2 := by
    have hcard_Z : Z_xi.card ≤ d := by
      have h1 : ∀ w ∈ Z_xi, 1 ≤ (analyticOrderAt _root_.RHTower.xi w).toNat := by
        intro w hw
        have hw0 := ((_root_.RHTower.stripZeros_finite T_star).mem_toFinset.mp hw).2
        have hne0 : analyticOrderAt _root_.RHTower.xi w ≠ 0 := by
          intro h0
          rcases analyticOrderAt_eq_zero.mp h0 with hnot | hnz
          · exact hnot (_root_.RHTower.xi_analyticOnNhd Set.univ w (Set.mem_univ w))
          · exact hnz hw0
        have hcoe := ENat.coe_toNat (_root_.RHTower.xi_orderAt_ne_top w)
        by_contra hlt
        have hz : (analyticOrderAt _root_.RHTower.xi w).toNat = 0 := by omega
        rw [hz, ENat.coe_zero] at hcoe
        exact hne0 hcoe.symm
      calc Z_xi.card = ∑ _w ∈ Z_xi, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ ∑ w ∈ Z_xi, (analyticOrderAt _root_.RHTower.xi w).toNat := Finset.sum_le_sum h1
        _ = d := rfl
    calc P_diff.card ≤ (Z_xi ×ˢ Z_xi).card := Finset.card_image_le
      _ = Z_xi.card ^ 2 := by rw [Finset.card_product, sq]
      _ ≤ d ^ 2 := Nat.pow_le_pow_left hcard_Z 2
  obtain ⟨n_star, hn_Icc_P, havoid_P⟩ := exists_natStage_avoiding_zhukovsky_ellipses S P_diff
  have hn_Icc : n_star ∈ Finset.Icc (max S 6) S_max := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn_Icc_P
    exact Finset.mem_Icc.mpr ⟨h1, h2.trans (by dsimp only [S_max]; omega)⟩
  obtain ⟨hn_lo, _⟩ := Finset.mem_Icc.mp hn_Icc
  have hn6 : 6 ≤ n_star := (le_max_right S 6).trans hn_lo
  have havoid : ∀ z ∈ Z_xi, ∀ w ∈ Z_xi,
      1 / (8 * (S_max : ℝ) ^ 3) ≤ |zhukovskyEllipseForm n_star (z - w) - 1| := by
    intro z hz w hw
    have hmem : z - w ∈ P_diff :=
      Finset.mem_image.mpr ⟨(z, w), Finset.mem_product.mpr ⟨hz, hw⟩, rfl⟩
    have hP_le_S : ((max S 6 + 2 * P_diff.card : ℕ) : ℝ) ≤ (S_max : ℝ) := by
      exact_mod_cast (show max S 6 + 2 * P_diff.card ≤ S_max by dsimp only [S_max]; omega)
    have hstep : 1 / (8 * (S_max : ℝ) ^ 3) ≤
        1 / (8 * ((max S 6 + 2 * P_diff.card : ℕ) : ℝ) ^ 3) := by
      have hp : (0 : ℝ) < ((max S 6 + 2 * P_diff.card : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < max S 6 + 2 * P_diff.card by omega)
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le hP_le_S 3) (by norm_num))
    exact hstep.trans (havoid_P (z - w) hmem)
  refine ⟨n_star, hn_Icc, hn6, havoid, ?_⟩
  set δ_n : ℝ := 1 / (2 * (zhukovskyStage n_star : ℝ))
  have hδ_pos : 0 < δ_n := one_div_pos.mpr (by positivity [zhukovskyStage_pos n_star])
  have hδ_le : δ_n ≤ 1 / 12 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [six_le_zhukovskyStage_real n_star])
  set T_win : ℝ := T_star + δ_n
  have hT_win_nn : 0 ≤ T_win := by dsimp only [T_win]; linarith
  set z₁ := thetaWindowLowerLeft n_star
  set z₂ := thetaWindowUpperRight T_win n_star
  have hz₁_re : z₁.re = -1 / 2 := thetaWindowLowerLeft_re n_star
  have hz₂_re : z₂.re = 3 / 2 := thetaWindowUpperRight_re T_win n_star
  have hz₁_im : z₁.im = -δ_n := thetaWindowLowerLeft_im n_star
  have hz₂_im : z₂.im = T_star := by
    dsimp only [z₂]
    rw [thetaWindowUpperRight_im, max_eq_right hT_win_nn]
    dsimp only [T_win, δ_n]; ring
  have him_le : z₁.im ≤ z₂.im := by rw [hz₁_im, hz₂_im]; linarith
  set μ : ℝ := c_good * Real.exp (-((m + 1 : ℕ) : ℝ))
  have hμ_pos : 0 < μ := by dsimp only [μ]; positivity
  have hc_good_le1 : c_good ≤ 1 := by
    have hexp_le : Real.exp (-Real.pi) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
    have hmul := mul_le_mul_of_nonneg_left hexp_le (by norm_num : (0 : ℝ) ≤ 5026 / 16875)
    linarith [hc_good_le_low]
  have hμ_le1 : μ ≤ 1 := by
    dsimp only [μ]
    calc c_good * Real.exp (-((m + 1 : ℕ) : ℝ))
        ≤ 1 * 1 := mul_le_mul hc_good_le1
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _)))
          (Real.exp_pos _).le zero_le_one
      _ = 1 := one_mul 1
  have hμ_bdry : ∀ t : ℝ, μ ≤ ‖_root_.RHTower.xi (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t)‖ := by
    intro t
    set w := _root_.RHTower.rectangleBoundaryPath z₁ z₂ t
    have hrect := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm z₁ z₂
      (by linarith : z₁.re ≤ z₂.re) him_le t
    rw [uIcc_of_le (by linarith : z₁.re ≤ z₂.re), uIcc_of_le him_le,
      Complex.mem_reProdIm, hz₁_re, hz₂_re, hz₁_im, hz₂_im] at hrect
    have hw_eq : ((w.re : ℂ) + (w.im : ℂ) * I) = w := Complex.re_add_im w
    have him_abs : |w.im| ≤ T_star := abs_le.mpr ⟨by linarith [hrect.2.1], hrect.2.2⟩
    rcases rectangleBoundaryPath_on_edges' z₁ z₂ t with h1 | h2 | h3 | h4
    · rw [← hw_eq, h1, hz₁_re]; push_cast; exact (hT_vert w.im him_abs).2
    · rw [← hw_eq, h2, hz₂_re]; push_cast; exact (hT_vert w.im him_abs).1
    · have hexp1 : Real.exp (-((m + 1 : ℕ) : ℝ)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
      have hμ_low : μ ≤ (5026 / 16875) * Real.exp (-Real.pi) := by
        calc μ = c_good * Real.exp (-((m + 1 : ℕ) : ℝ)) := rfl
          _ ≤ c_good * 1 := mul_le_mul_of_nonneg_left hexp1 hc_good_pos.le
          _ = c_good := mul_one _
          _ ≤ (5026 / 16875) * Real.exp (-Real.pi) := hc_good_le_low
      exact hμ_low.trans ((xi_re_ge_lowWindow
        (abs_le.mpr ⟨by linarith [hrect.1.1], by linarith [hrect.1.2]⟩)
        (by rw [h3, hz₁_im, abs_neg, abs_of_pos hδ_pos]; linarith)).trans (Complex.re_le_norm _))
    · rw [← hw_eq, h4, hz₂_im]
      exact hT_hor w.re (by linarith [hrect.1.1]) (by linarith [hrect.1.2])
  have hxi_nz_bdry : ∀ t : ℝ, _root_.RHTower.xi (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t) ≠ 0 := by
    intro t h0; have hb := hμ_bdry t; rw [h0, norm_zero] at hb; linarith
  have hxi_moments : ∀ r : ℕ,
      (2 * Real.pi * I)⁻¹ *
        _root_.RHTower.rectIntegral (fun z => (z - 0) ^ r * logDeriv _root_.RHTower.xi z) z₁ z₂ =
      ∑ w ∈ Z_xi, ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * (w - 0) ^ r := by
    intro r
    obtain ⟨Z_box, hZ_box_mem, hrect_sum⟩ := entire_rectIntegral_mul_logDeriv_eq_sum
      (_root_.RHTower.xi_analyticOnNhd Set.univ) _root_.RHTower.xi_orderAt_ne_top
      (g := fun z => (z - 0) ^ r) (fun _ _ => (analyticAt_id.sub analyticAt_const).pow r)
      (by linarith : z₁.re ≤ z₂.re) him_le hxi_nz_bdry
    have hZ_eq : Z_box = Z_xi := by
      ext w
      rw [hZ_box_mem, (_root_.RHTower.stripZeros_finite T_star).mem_toFinset]
      rw [hz₁_re, hz₂_re, hz₁_im, hz₂_im]
      constructor
      · rintro ⟨⟨_, _, hy1, hy2⟩, hw0⟩
        obtain ⟨hre0, hre1⟩ := _root_.RHTower.xi_zero_re_mem_open_unit hw0
        have hy_nn : 0 ≤ w.im := by
          by_contra hneg
          have him61 : |w.im| ≤ 61 / 20 := abs_le.mpr ⟨by linarith, by linarith⟩
          have hpos := xi_re_ge_lowWindow (abs_le.mpr ⟨by linarith, by linarith⟩) him61
          rw [hw0, Complex.zero_re] at hpos
          have : (0 : ℝ) < (5026 / 16875) * Real.exp (-Real.pi) := by positivity
          linarith
        exact ⟨⟨hre0, hre1, hy_nn, hy2⟩, hw0⟩
      · rintro ⟨⟨hre0, hre1, hy0, hyT⟩, hw0⟩
        exact ⟨⟨by linarith, by linarith, by linarith, hyT⟩, hw0⟩
    rwa [hZ_eq] at hrect_sum
  have hspan : z₂.im - z₁.im ≤ ((m + 2 : ℕ) : ℝ) := by
    rw [hz₂_im, hz₁_im]; push_cast; linarith
  have hR_bdry : ∀ t : ℝ, ‖_root_.RHTower.rectangleBoundaryPath z₁ z₂ t - 0‖ ≤ ((m + 4 : ℕ) : ℝ) := by
    intro t
    rw [sub_zero]
    set w := _root_.RHTower.rectangleBoundaryPath z₁ z₂ t
    have hrect := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm z₁ z₂
      (by linarith : z₁.re ≤ z₂.re) him_le t
    rw [uIcc_of_le (by linarith : z₁.re ≤ z₂.re), uIcc_of_le him_le,
      Complex.mem_reProdIm, hz₁_re, hz₂_re, hz₁_im, hz₂_im] at hrect
    have hn := Complex.norm_le_abs_re_add_abs_im w
    have hre_abs : |w.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hrect.1.1], hrect.1.2⟩
    have him_abs : |w.im| ≤ T_star := abs_le.mpr ⟨by linarith [hrect.2.1], hrect.2.2⟩
    push_cast; linarith
  have hZ_rad : ∀ w ∈ Z_xi, ‖w - 0‖ ≤ ((m + 4 : ℕ) : ℝ) := by
    intro w hw
    rw [sub_zero]
    obtain ⟨⟨hre0, hre1, hy0, hyT⟩, _⟩ := (_root_.RHTower.stripZeros_finite T_star).mem_toFinset.mp hw
    have hn := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_pos hre0, abs_of_nonneg hy0] at hn
    push_cast; linarith
  exact ⟨him_le, hspan, hμ_pos, hμ_le1, hμ_bdry, hR_bdry, hZ_rad, hxi_moments⟩

/-- **Zero-separation-free `O(m log²(m + S))` cumulative polynomial-prefix stabilization.**
There exists an absolute constant `C_cum ≥ 1` such that for every natural height `m : ℕ` and every
target Zhukovsky stage `S : ℕ`, there exist a Burnol good height `T_* ∈ [m, m + 1]` and an
ellipse-avoiding stage `n_* ∈ [max S 6, max S 6 + 2 * (xiStripWindowTotalOrder T_*)²]` such that at
`T_win := T_* + 1 / (2 * zhukovskyStage n_*)`, for all
`N ≥ C_cum * (m + 1) * (⌈log(m + S + 4)⌉₊ + 1)²`:
1. `finiteThetaAmplitude N` avoids `∂R_{T_win, n_*}` and `integerThetaWindowDegree = xiStripWindowTotalOrder T_*`;
2. `integerThetaLaurentLoop T_win n_* N` is nonvanishing on `UnitCircle` and its enclosed zeros are
   ellipse-nondegenerate (unlocking the 6-way `integerTheta_szego_positivity_tfae`);
3. `fredholmIndex (integerThetaCollisionOperator T_win n_* N)` equals the exact `n_*`-resolved `xi`
   pair-collision sum on `stripZeros T_*`, and equals `(xiHorizontalCollisionCharge T_* : ℤ)`
   whenever `thetaWindowScale T_* ≤ S`. -/
theorem integerThetaCollisionOperator_polynomial_stabilization :
    ∃ C_cum : ℕ, 1 ≤ C_cum ∧ ∀ (m S : ℕ),
      ∃ (T_star : ℝ) (n_star : ℕ),
        (m : ℝ) ≤ T_star ∧ T_star ≤ (m : ℝ) + 1 ∧
        n_star ∈ Finset.Icc (max S 6)
          (max S 6 + 2 * (_root_.RHTower.xiStripWindowTotalOrder T_star) ^ 2) ∧
        let T_win : ℝ := T_star + 1 / (2 * (zhukovskyStage n_star : ℝ))
        ∀ N : ℕ,
          C_cum * (m + 1) * (Nat.ceil (Real.log ((m + S + 4 : ℕ) : ℝ)) + 1) ^ 2 ≤ N →
          (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
            (_root_.RHTower.rectangleBoundaryPath
              (thetaWindowLowerLeft n_star) (thetaWindowUpperRight T_win n_star) t) ≠ 0) ∧
          integerThetaWindowDegree T_win n_star N =
            _root_.RHTower.xiStripWindowTotalOrder T_star ∧
          (∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T_win n_star N u ≠ 0) ∧
          (∀ z ∈ prefixEnclosedZeros T_win n_star N, ∀ w ∈ prefixEnclosedZeros T_win n_star N,
            zhukovskyEllipseForm n_star (z - w) ≠ 1) ∧
          HTGeometry.fredholmIndex (integerThetaCollisionOperator T_win n_star N) =
            2 * ∑ z ∈ (_root_.RHTower.stripZeros_finite T_star).toFinset,
              ∑ w ∈ (_root_.RHTower.stripZeros_finite T_star).toFinset,
                ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
                  ((analyticOrderAt _root_.RHTower.xi w).toNat : ℤ) *
                  (if zhukovskyEllipseForm n_star (z - w) < 1 then 1 else 0) ∧
          (thetaWindowScale T_star ≤ S →
            HTGeometry.fredholmIndex (integerThetaCollisionOperator T_win n_star N) =
              (_root_.RHTower.xiHorizontalCollisionCharge T_star : ℤ)) := by
  obtain ⟨c_good, T_good, hc_good_pos, hc_good_le_low, hgood⟩ := exists_all_nat_burnol_good_height
  obtain ⟨M_strip, hM1, hstrip⟩ := exists_strip_xi_and_deriv_bound
  obtain ⟨C_loc, hC_loc1, _, hcum_log⟩ := exists_all_xiUnitWindowOrder_le_log
  let C_env : ℝ :=
    _root_.RHTower.thetaCuspIntegerTailConstant * _root_.RHTower.thetaAmplitudeEnvelope 2 + 1
  have hC_env1 : 1 ≤ C_env := by
    dsimp only [C_env]
    have hnn := mul_nonneg _root_.RHTower.thetaCuspIntegerTailConstant_nonneg
      (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2)
    linarith
  have hC_env_tail : ∀ N : ℕ,
      thetaStripTailBound N ≤ C_env * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) := fun N => by
    unfold thetaStripTailBound
    exact mul_le_mul_of_nonneg_right (by dsimp only [C_env]; linarith) (Real.exp_pos _).le
  obtain ⟨K_cum, hC_cum1, hbudget⟩ :=
    exists_cumulative_prefix_constant hc_good_pos hM1 hC_loc1 hC_env1 hC_env_tail
  refine ⟨K_cum, hC_cum1, fun m S => ?_⟩
  obtain ⟨hT_lo, hT_hi, hT_half, hT_hor, hT_vert⟩ := hgood m
  obtain ⟨n_star, hn_Icc, hn6, havoid, him_le, hspan, hμ_pos, hμ_le1, hμ_bdry, hR_bdry,
      hZ_rad, hxi_moments⟩ :=
    cumulative_window_pigeonhole_and_rect hc_good_pos hc_good_le_low m S hT_lo hT_hi hT_half
      hT_hor hT_vert
  obtain ⟨hn_lo, hn_hi⟩ := Finset.mem_Icc.mp hn_Icc
  refine ⟨T_good m, n_star, hT_lo, hT_hi, hn_Icc, fun N hN => ?_⟩
  have hd_raw := hcum_log m (T_good m) (by push_cast; exact hT_hi)
  obtain ⟨hN_tail, hN_half, hN_rouche⟩ :=
    hbudget m S (_root_.RHTower.xiStripWindowTotalOrder (T_good m)) N hd_raw hN
  have hR1 : (1 : ℝ) ≤ ((m + 4 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m + 4 by omega)
  have hH1 : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m + 2 by omega)
  set T_win : ℝ := T_good m + 1 / (2 * (zhukovskyStage n_star : ℝ))
  obtain ⟨hbdry_N, hs0_N, _, hPN_nz, hPN_wind⟩ :=
    pairDiffPoly_rouche_stabilization_core (thetaWindowLowerLeft_re n_star)
      (thetaWindowUpperRight_re T_win n_star) him_le hμ_pos hμ_le1 hR1 hH1 hM1 hspan hstrip
      hμ_bdry hR_bdry hZ_rad hxi_moments hn6 hn_hi havoid hN_tail hN_half hN_rouche
  have hsN_eq : (fun r : ℕ =>
      (2 * Real.pi * I)⁻¹ *
        _root_.RHTower.rectIntegral
          (fun z => (z - 0) ^ r *
            (-_root_.RHTower.finiteThetaFirstMoment N z /
              _root_.RHTower.finiteThetaAmplitude N z))
          (thetaWindowLowerLeft n_star) (thetaWindowUpperRight T_win n_star)) =
      integerThetaWindowPowerSum T_win n_star N := by
    funext r
    simp only [sub_zero, integerThetaWindowPowerSum]
  have hd_def :
      (∑ w ∈ (_root_.RHTower.stripZeros_finite (T_good m)).toFinset,
        (analyticOrderAt _root_.RHTower.xi w).toNat) =
      _root_.RHTower.xiStripWindowTotalOrder (T_good m) := rfl
  have hs0_eq : integerThetaWindowPowerSum T_win n_star N 0 =
      (_root_.RHTower.xiStripWindowTotalOrder (T_good m) : ℂ) := by
    rw [← congrFun hsN_eq 0]
    exact hs0_N.trans (congrArg Nat.cast hd_def)
  have hdeg_eq : integerThetaWindowDegree T_win n_star N =
      _root_.RHTower.xiStripWindowTotalOrder (T_good m) := by
    unfold integerThetaWindowDegree
    rw [hs0_eq, Complex.natCast_re]
    exact (Nat.floor_eq_iff (by positivity)).mpr ⟨by linarith, by linarith⟩
  have hpoly_eq : integerThetaDifferencePoly T_win n_star N =
      pairDiffPoly (_root_.RHTower.xiStripWindowTotalOrder (T_good m))
        (integerThetaWindowPowerSum T_win n_star N) := by
    unfold integerThetaDifferencePoly
    rw [hdeg_eq]
  rw [hsN_eq, hd_def, ← hpoly_eq] at hPN_nz hPN_wind
  have hloop_nz : ∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T_win n_star N u ≠ 0 :=
    fun u => by rw [integerThetaLaurentLoop_apply]; exact hPN_nz u
  have hell_N := ellipse_nondegenerate_of_loop_ne_zero T_win n_star N hbdry_N hloop_nz
  have hind_eq : HTGeometry.fredholmIndex (integerThetaCollisionOperator T_win n_star N) =
      _root_.RHTower.windingNumber
        (fun θ => ((integerThetaDifferencePoly T_win n_star N).eval
          (zhukovskyLoop n_star (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) := by
    unfold integerThetaCollisionOperator integerThetaCollisionSymbol
    rw [fredholmIndex_wienerHopfLift_unitNormalizeSymbol,
      circleWinding_unitNormalizeSymbol_of_ne_zero hloop_nz]
    rfl
  refine ⟨hbdry_N, hdeg_eq, hloop_nz, hell_N, hind_eq.trans hPN_wind, fun hscale => ?_⟩
  have hn_scale : thetaWindowScale (T_good m) ≤ n_star :=
    hscale.trans ((le_max_left S 6).trans hn_lo)
  obtain ⟨_, hwind_charge⟩ := exactWindowDifferencePoly_winding (T_good m) hn_scale
  have hQ_eval_exact : ∀ x : ℂ, (exactWindowDifferencePoly (T_good m)).eval x =
      ∏ z ∈ (_root_.RHTower.stripZeros_finite (T_good m)).toFinset,
        ∏ w ∈ (_root_.RHTower.stripZeros_finite (T_good m)).toFinset,
          (x - (z - w)) ^
            ((analyticOrderAt _root_.RHTower.xi z).toNat *
              (analyticOrderAt _root_.RHTower.xi w).toNat) :=
    fun x => eval_pairDiffPoly_eq_finset_prod
      (_root_.RHTower.stripZeros_finite (T_good m)).toFinset id
      (fun w => (analyticOrderAt _root_.RHTower.xi w).toNat) rfl (fun _ _ _ => rfl) x
  have hell_xi :
      ∀ z ∈ (_root_.RHTower.stripZeros_finite (T_good m)).toFinset,
      ∀ w ∈ (_root_.RHTower.stripZeros_finite (T_good m)).toFinset,
        zhukovskyEllipseForm n_star (z - w) ≠ 1 := by
    intro z hz w hw h1
    have hg := havoid z hz w hw
    rw [h1, sub_self, abs_zero] at hg
    set S_max := max S 6 + 2 * (_root_.RHTower.xiStripWindowTotalOrder (T_good m)) ^ 2
    have hS6 : (6 : ℝ) ≤ (S_max : ℝ) := by exact_mod_cast (hn6.trans hn_hi)
    have hp : 0 < 1 / (8 * (S_max : ℝ) ^ 3) := by positivity
    linarith
  obtain ⟨_, hQ_birk, _⟩ := exists_birkhoffSzego_of_prod_eval hQ_eval_exact hell_xi
  rw [hind_eq, hPN_wind]
  have hsum_cast :
      (2 * ∑ z ∈ (_root_.RHTower.stripZeros_finite (T_good m)).toFinset,
        ∑ w ∈ (_root_.RHTower.stripZeros_finite (T_good m)).toFinset,
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
            ((analyticOrderAt _root_.RHTower.xi w).toNat : ℤ) *
            (if zhukovskyEllipseForm n_star (z - w) < 1 then 1 else 0)) =
      (2 * ((∑ z ∈ (_root_.RHTower.stripZeros_finite (T_good m)).toFinset,
        ∑ w ∈ (_root_.RHTower.stripZeros_finite (T_good m)).toFinset,
          (analyticOrderAt _root_.RHTower.xi z).toNat *
            (analyticOrderAt _root_.RHTower.xi w).toNat *
            (if zhukovskyEllipseForm n_star (z - w) < 1 then 1 else 0) : ℕ) : ℤ)) := by
    congr 1
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hlt : zhukovskyEllipseForm n_star (z - w) < 1 <;> simp [hlt]
  rw [hsum_cast, ← hQ_birk, hwind_charge]


/-! ## §4 Source-pure centered window operator and optimal `Θ(√m)` Burnol unit-window stabilization -/

/-- Lower-left corner `-1 / 2 + i y₁` of a vertical window `[y₁, y₂]`. -/
def centeredWindowLowerLeft (y₁ : ℝ) : ℂ :=
  (-1 / 2 : ℂ) + (y₁ : ℂ) * I

/-- Upper-right corner `3 / 2 + i y₂` of a vertical window `[y₁, y₂]`. -/
def centeredWindowUpperRight (y₂ : ℝ) : ℂ :=
  (3 / 2 : ℂ) + (y₂ : ℂ) * I

/-- Midpoint `1 / 2 + i ((y₁ + y₂) / 2)` of the vertical window `[-1 / 2, 3 / 2] × [y₁, y₂]`. -/
def centeredWindowMid (y₁ y₂ : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (((y₁ + y₂) / 2 : ℝ) : ℂ) * I

@[simp]
theorem centeredWindowLowerLeft_re (y₁ : ℝ) : (centeredWindowLowerLeft y₁).re = -1 / 2 := by
  simp [centeredWindowLowerLeft]

@[simp]
theorem centeredWindowLowerLeft_im (y₁ : ℝ) : (centeredWindowLowerLeft y₁).im = y₁ := by
  simp [centeredWindowLowerLeft]

@[simp]
theorem centeredWindowUpperRight_re (y₂ : ℝ) : (centeredWindowUpperRight y₂).re = 3 / 2 := by
  simp [centeredWindowUpperRight]

@[simp]
theorem centeredWindowUpperRight_im (y₂ : ℝ) : (centeredWindowUpperRight y₂).im = y₂ := by
  simp [centeredWindowUpperRight]

/-- Source-pure centered `r`-th logarithmic-derivative moment of `finiteThetaAmplitude N` on
`[-1 / 2, 3 / 2] × [y₁, y₂]`. -/
def centeredThetaWindowPowerSum (y₁ y₂ : ℝ) (N r : ℕ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    _root_.RHTower.rectIntegral
      (fun z => (z - centeredWindowMid y₁ y₂) ^ r *
        (-_root_.RHTower.finiteThetaFirstMoment N z /
          _root_.RHTower.finiteThetaAmplitude N z))
      (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂)

/-- Source-pure enclosed zero count on `[-1 / 2, 3 / 2] × [y₁, y₂]`. -/
def centeredThetaWindowDegree (y₁ y₂ : ℝ) (N : ℕ) : ℕ :=
  Nat.floor (centeredThetaWindowPowerSum y₁ y₂ N 0).re

/-- Source-pure Newton–Girard pair-difference polynomial on `[-1 / 2, 3 / 2] × [y₁, y₂]`. -/
def centeredThetaDifferencePoly (y₁ y₂ : ℝ) (N : ℕ) : Polynomial ℂ :=
  pairDiffPoly (centeredThetaWindowDegree y₁ y₂ N) (centeredThetaWindowPowerSum y₁ y₂ N)

/-- Base Zhukovsky circle loop `(centeredThetaDifferencePoly y₁ y₂ N) ∘ zhukovskyLoop n`. -/
def centeredThetaBaseLoop (y₁ y₂ : ℝ) (n N : ℕ) : C(HTGeometry.UnitCircle, ℂ) :=
  polyZhukovskyBaseLoop n (centeredThetaDifferencePoly y₁ y₂ N)

/-- Squared Zhukovsky Laurent loop `(centeredThetaBaseLoop y₁ y₂ n N)²` on `UnitCircle`. -/
def centeredThetaLaurentLoop (y₁ y₂ : ℝ) (n N : ℕ) : C(HTGeometry.UnitCircle, ℂ) :=
  polyZhukovskyLaurentLoop n (centeredThetaDifferencePoly y₁ y₂ N)

/-- Unit-normalized circle symbol of `centeredThetaLaurentLoop y₁ y₂ n N`. -/
def centeredThetaCollisionSymbol (y₁ y₂ : ℝ) (n N : ℕ) : C(HTGeometry.UnitCircle, ℂ) :=
  unitNormalizeSymbol (centeredThetaLaurentLoop y₁ y₂ n N)

/-- Source-pure centered Wiener–Hopf collision operator on `L²(ℝ)`. -/
def centeredThetaCollisionOperator (y₁ y₂ : ℝ) (n N : ℕ) :
    HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real :=
  HTGeometry.wienerHopfLift (centeredThetaCollisionSymbol y₁ y₂ n N)

/-- Exact divisor product factorization of `centeredThetaDifferencePoly y₁ y₂ N` whenever
`y₁ ≤ y₂` and `finiteThetaAmplitude N` avoids the rectangle boundary. -/
theorem eval_centeredThetaDifferencePoly_eq_prod {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) t) ≠ 0) :
    ∃ Z_N : Finset ℂ,
      (∀ w : ℂ, w ∈ Z_N ↔
        (-1 / 2 < w.re ∧ w.re < 3 / 2 ∧ y₁ < w.im ∧ w.im < y₂) ∧
          _root_.RHTower.finiteThetaAmplitude N w = 0) ∧
      centeredThetaWindowDegree y₁ y₂ N =
        ∑ w ∈ Z_N, (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat ∧
      ∀ x : ℂ, (centeredThetaDifferencePoly y₁ y₂ N).eval x =
        ∏ z ∈ Z_N, ∏ w ∈ Z_N,
          (x - (z - w)) ^
            ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat *
              (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat) := by
  have han_A : AnalyticOnNhd ℂ (_root_.RHTower.finiteThetaAmplitude N) Set.univ := fun w _ => by
    have hfun : _root_.RHTower.finiteThetaAmplitude N = finiteThetaShellPencil N 0 :=
      (funext (finiteThetaShellPencil_zero N)).symm
    rw [hfun]
    exact analyticOnNhd_finiteThetaShellPencil N 0 w (Set.mem_univ w)
  have hord_A : ∀ w : ℂ, analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w ≠ ⊤ := fun w => by
    have hfun : _root_.RHTower.finiteThetaAmplitude N = finiteThetaShellPencil N 0 :=
      (funext (finiteThetaShellPencil_zero N)).symm
    rw [hfun]
    exact finiteThetaShellPencil_orderAt_ne_top N ⟨le_rfl, zero_le_one⟩ w
  have hre_le : (centeredWindowLowerLeft y₁).re ≤ (centeredWindowUpperRight y₂).re := by
    simp; norm_num
  have him_le : (centeredWindowLowerLeft y₁).im ≤ (centeredWindowUpperRight y₂).im := by
    simpa using hy
  obtain ⟨Z_N, hZN_mem, hsum0⟩ := entire_rectIntegral_mul_logDeriv_eq_sum han_A hord_A
    (g := fun _ => (1 : ℂ)) (fun _ _ => analyticAt_const) hre_le him_le hbdry
  have hmem' : ∀ w : ℂ, w ∈ Z_N ↔
      (-1 / 2 < w.re ∧ w.re < 3 / 2 ∧ y₁ < w.im ∧ w.im < y₂) ∧
        _root_.RHTower.finiteThetaAmplitude N w = 0 := by
    intro w
    simpa using hZN_mem w
  have hps : ∀ r : ℕ, centeredThetaWindowPowerSum y₁ y₂ N r =
      ∑ w ∈ Z_N,
        ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat : ℂ) *
          (w - centeredWindowMid y₁ y₂) ^ r := by
    intro r
    obtain ⟨Z_r, hZr_mem, hsum_r⟩ := entire_rectIntegral_mul_logDeriv_eq_sum han_A hord_A
      (g := fun z => (z - centeredWindowMid y₁ y₂) ^ r)
      (fun _ _ => (analyticAt_id.sub analyticAt_const).pow r) hre_le him_le hbdry
    have hZ_eq : Z_r = Z_N := by
      ext w; rw [hZr_mem, hZN_mem]
    rw [hZ_eq] at hsum_r
    unfold centeredThetaWindowPowerSum
    have hint_eq : (fun z : ℂ => (z - centeredWindowMid y₁ y₂) ^ r *
        (-_root_.RHTower.finiteThetaFirstMoment N z /
          _root_.RHTower.finiteThetaAmplitude N z)) =
        (fun z : ℂ => (z - centeredWindowMid y₁ y₂) ^ r *
          logDeriv (_root_.RHTower.finiteThetaAmplitude N) z) := by
      funext z
      rw [logDeriv_apply, _root_.RHTower.deriv_finiteThetaAmplitude]
    rw [hint_eq, hsum_r]
  have hdeg_eq : centeredThetaWindowDegree y₁ y₂ N =
      ∑ w ∈ Z_N, (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat := by
    unfold centeredThetaWindowDegree
    rw [hps 0]
    simp only [pow_zero, mul_one, ← Nat.cast_sum, Complex.natCast_re]
    exact (Nat.floor_eq_iff (Nat.cast_nonneg _)).mpr ⟨le_rfl, by linarith⟩
  refine ⟨Z_N, hmem', hdeg_eq, fun x => ?_⟩
  unfold centeredThetaDifferencePoly
  rw [eval_pairDiffPoly_eq_finset_prod Z_N (fun w => w - centeredWindowMid y₁ y₂)
    (fun w => (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat)
    hdeg_eq (fun r _ _ => hps r) x]
  refine Finset.prod_congr rfl fun z _ => Finset.prod_congr rfl fun w _ => ?_
  rw [show (z - centeredWindowMid y₁ y₂) - (w - centeredWindowMid y₁ y₂) = z - w by ring]

/-- **Arithmetic reality of `centeredThetaDifferencePoly` and `centeredThetaLaurentLoop`.**
Because horizontal reflection `w ↦ 1 - conj w` preserves `(-1 / 2, 3 / 2) × (y₁, y₂)` while
shifting cancels in `(z - c) - (w - c) = z - w`, every boundary-regular centered difference
polynomial has real coefficients and reflection-symmetric circle loop. -/
theorem centeredThetaDifferencePoly_real_and_loop_symmetric {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂)
    (n N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) t) ≠ 0) :
    (∀ x : ℂ, star ((centeredThetaDifferencePoly y₁ y₂ N).eval (star x)) =
      (centeredThetaDifferencePoly y₁ y₂ N).eval x) ∧
    (∀ k : ℕ, ((centeredThetaDifferencePoly y₁ y₂ N).coeff k).im = 0) ∧
    (∀ u : HTGeometry.UnitCircle,
      star (centeredThetaLaurentLoop y₁ y₂ n N (circleConj u)) =
        centeredThetaLaurentLoop y₁ y₂ n N u) := by
  obtain ⟨Z_N, hZN_mem, _, heval⟩ := eval_centeredThetaDifferencePoly_eq_prod hy N hbdry
  set P := centeredThetaDifferencePoly y₁ y₂ N
  let mult : ℂ → ℕ := fun w => (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat
  have hrefl_mem : ∀ w : ℂ, 1 - star w ∈ Z_N ↔ w ∈ Z_N := by
    have hinv : ∀ z : ℂ, z ∈ Z_N → 1 - star z ∈ Z_N := by
      intro z hz
      obtain ⟨⟨hx1, hx2, hy1, hy2⟩, hz0⟩ := (hZN_mem z).mp hz
      rw [hZN_mem]
      refine ⟨⟨by simp; linarith, by simp; linarith, by simpa using hy1, by simpa using hy2⟩, ?_⟩
      rw [finiteThetaAmplitude_one_sub]
      have hconj := finiteThetaAmplitude_conj N z
      rw [hz0] at hconj
      exact star_eq_zero.mp hconj
    exact fun w => ⟨fun h => by have h' := hinv (1 - star w) h; simpa using h', hinv w⟩
  have hreal_eval : ∀ x : ℂ, star (P.eval (star x)) = P.eval x := by
    intro x
    rw [heval (star x), heval x]
    change (starRingEnd ℂ) (∏ z ∈ Z_N, ∏ w ∈ Z_N, (star x - (z - w)) ^ (mult z * mult w)) = _
    rw [map_prod]
    have hstep1 : (∏ z ∈ Z_N, (starRingEnd ℂ) (∏ w ∈ Z_N, (star x - (z - w)) ^ (mult z * mult w))) =
        ∏ z ∈ Z_N, ∏ w ∈ Z_N, (x - (star z - star w)) ^ (mult z * mult w) := by
      refine Finset.prod_congr rfl fun z _ => ?_
      rw [map_prod]; exact Finset.prod_congr rfl fun w _ => by simp
    rw [hstep1]
    have hreidx : (∏ z ∈ Z_N, ∏ w ∈ Z_N, (x - (star z - star w)) ^ (mult z * mult w)) =
        ∏ z' ∈ Z_N, ∏ w' ∈ Z_N, (x - (w' - z')) ^ (mult z' * mult w') := by
      refine Finset.prod_bij (fun z _ => 1 - star z)
        (fun z hz => (hrefl_mem z).mpr hz)
        (fun z₁ _ z₂ _ heq => by have h := congrArg (fun u => 1 - star u) heq; simpa using h)
        (fun z' hz' => ⟨1 - star z', (hrefl_mem z').mpr hz', by simp⟩)
        (fun z _ => ?_)
      have hmz : mult (1 - star z) = mult z :=
        congrArg ENat.toNat (analyticOrderAt_finiteThetaAmplitude_one_sub_conj N z)
      rw [hmz]
      refine Finset.prod_bij (fun w _ => 1 - star w)
        (fun w hw => (hrefl_mem w).mpr hw)
        (fun w₁ _ w₂ _ heq => by have h := congrArg (fun u => 1 - star u) heq; simpa using h)
        (fun w' hw' => ⟨1 - star w', (hrefl_mem w').mpr hw', by simp⟩)
        (fun w _ => ?_)
      have hmw : mult (1 - star w) = mult w :=
        congrArg ENat.toNat (analyticOrderAt_finiteThetaAmplitude_one_sub_conj N w)
      rw [hmw, show star z - star w = (1 - star w) - (1 - star z) by ring]
    rw [hreidx, Finset.prod_comm]
    exact Finset.prod_congr rfl fun _ _ => Finset.prod_congr rfl fun _ _ => by rw [mul_comm]
  have hcoeff : ∀ k : ℕ, (P.coeff k).im = 0 := by
    let Q : Polynomial ℂ := P.map (starRingEnd ℂ)
    have hQP : Q = P := by
      haveI : Infinite ℂ := Infinite.of_injective (fun j : ℕ => (j : ℂ)) Nat.cast_injective
      apply Polynomial.funext
      intro x
      set D := max Q.natDegree P.natDegree + 1
      have hQsum := Polynomial.eval_eq_sum_range' (p := Q) (n := D)
        (Nat.lt_succ_of_le (le_max_left _ _)) x
      have hPsum := Polynomial.eval_eq_sum_range' (p := P) (n := D)
        (Nat.lt_succ_of_le (le_max_right _ _)) (star x)
      have hQeval : Q.eval x = star (P.eval (star x)) := by
        rw [hQsum, hPsum]
        change _ = (starRingEnd ℂ) (∑ i ∈ Finset.range D, P.coeff i * (star x) ^ i)
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [Q]; rw [Polynomial.coeff_map, map_mul, map_pow]; simp
      rw [hQeval, hreal_eval]
    intro k
    have hk : (starRingEnd ℂ) (P.coeff k) = P.coeff k := by
      rw [← Polynomial.coeff_map (starRingEnd ℂ) k, show P.map (starRingEnd ℂ) = P from hQP]
    exact Complex.conj_eq_iff_im.mp hk
  refine ⟨hreal_eval, hcoeff, fun u => ?_⟩
  unfold centeredThetaLaurentLoop
  rw [polyZhukovskyLaurentLoop_apply, polyZhukovskyLaurentLoop_apply, star_pow]
  congr 1
  have hzhuk : zhukovskyLoop n (circleConj u) = star (zhukovskyLoop n u) := by
    have h := congrArg star (zhukovskyLoop_circleConj n u); simpa using h
  rw [hzhuk, hreal_eval]

/-- **Six-way Birkhoff–Szegő positivity equivalence (`List.TFAE`) for `centeredThetaCollisionOperator`.**
Whenever `y₁ ≤ y₂`, `finiteThetaAmplitude N` avoids the rectangle boundary, and
`centeredThetaLaurentLoop y₁ y₂ n N` is nonvanishing on `UnitCircle`, `fredholmIndex < 2`,
`fredholmIndex = 0`, `L²(ℝ)` invertibility of the normalized or unnormalized Wiener–Hopf lift,
outer polynomial Szegő factorization, and Devinatz–Widom closed-disk sectoriality are all
unconditionally equivalent. -/
theorem centeredTheta_szego_positivity_tfae {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (n N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) t) ≠ 0)
    (hnz : ∀ u : HTGeometry.UnitCircle, centeredThetaLaurentLoop y₁ y₂ n N u ≠ 0) :
    [ HTGeometry.fredholmIndex (centeredThetaCollisionOperator y₁ y₂ n N) < 2,
      HTGeometry.fredholmIndex (centeredThetaCollisionOperator y₁ y₂ n N) = 0,
      IsUnit (centeredThetaCollisionOperator y₁ y₂ n N),
      IsUnit (HTGeometry.wienerHopfLift (centeredThetaLaurentLoop y₁ y₂ n N)),
      ∃ G H : Polynomial ℂ, IsOuterPolynomial G ∧ IsOuterPolynomial H ∧
        centeredThetaLaurentLoop y₁ y₂ n N = circlePoly G * star (circlePoly H),
      ∃ F : ℂ → ℂ, IsDiskUnit F ∧
        ∀ u : HTGeometry.UnitCircle, 0 < (F (u : ℂ) * centeredThetaLaurentLoop y₁ y₂ n N u).re
    ].TFAE := by
  obtain ⟨Z_N, hZN_mem, _, heval⟩ := eval_centeredThetaDifferencePoly_eq_prod hy N hbdry
  have hmult_pos : ∀ z ∈ Z_N,
      0 < (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat := by
    intro z hz
    have hz0 := ((hZN_mem z).mp hz).2
    have han_z : AnalyticAt ℂ (_root_.RHTower.finiteThetaAmplitude N) z := by
      have hfun : _root_.RHTower.finiteThetaAmplitude N = finiteThetaShellPencil N 0 :=
        (funext (finiteThetaShellPencil_zero N)).symm
      rw [hfun]
      exact analyticOnNhd_finiteThetaShellPencil N 0 z (Set.mem_univ z)
    have hord_ne_top : analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z ≠ ⊤ := by
      have hfun : _root_.RHTower.finiteThetaAmplitude N = finiteThetaShellPencil N 0 :=
        (funext (finiteThetaShellPencil_zero N)).symm
      rw [hfun]
      exact finiteThetaShellPencil_orderAt_ne_top N ⟨le_rfl, zero_le_one⟩ z
    have hne0 : analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z ≠ 0 := by
      intro h0
      rcases analyticOrderAt_eq_zero.mp h0 with hnot | hnz_z
      · exact hnot han_z
      · exact hnz_z hz0
    have hcoe := ENat.coe_toNat hord_ne_top
    by_contra hlt
    have hz_ord : (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat = 0 := by omega
    rw [hz_ord, ENat.coe_zero] at hcoe
    exact hne0 hcoe.symm
  have hell := ellipse_nondegenerate_of_prod_eval_ne_zero heval hmult_pos fun u => by
    simpa only [centeredThetaLaurentLoop, polyZhukovskyLaurentLoop_apply] using hnz u
  exact szego_positivity_tfae_of_prod_eval heval hell


/-- **Corridor-to-ellipse exterior lemma.**
1. Whenever `|z.re - 1 / 2| < 1 / (4 * s_n)` and `|w.re - 1 / 2| < 1 / (4 * s_n)`, `z - w` lies
   strictly outside the `n`-th Zhukovsky ellipse (`1 < zhukovskyEllipseForm n (z - w)`), regardless
   of vertical spacing `z.im - w.im`.
2. Stronger quantitative form for `6 ≤ n`: whenever `|z.re - 1 / 2| ≤ 1 / (8 * n)` and
   `|w.re - 1 / 2| ≤ 1 / (8 * n)`, `1 + 1 / n ≤ zhukovskyEllipseForm n (z - w)`, hence
   `1 / (8 * n³) ≤ |zhukovskyEllipseForm n (z - w) - 1|` at `n` itself with zero stage shift. -/
theorem zhukovskyEllipseForm_gt_one_of_re_margin :
    (∀ (n : ℕ) {z w : ℂ},
      |z.re - 1 / 2| < 1 / (4 * (zhukovskyStage n : ℝ)) →
      |w.re - 1 / 2| < 1 / (4 * (zhukovskyStage n : ℝ)) →
      1 < zhukovskyEllipseForm n (z - w)) ∧
    (∀ {n : ℕ}, 6 ≤ n → ∀ {z w : ℂ},
      |z.re - 1 / 2| ≤ 1 / (8 * (n : ℝ)) →
      |w.re - 1 / 2| ≤ 1 / (8 * (n : ℝ)) →
      1 < zhukovskyEllipseForm n (z - w) ∧
        1 / (8 * (n : ℝ) ^ 3) ≤ |zhukovskyEllipseForm n (z - w) - 1|) := by
  constructor
  · intro n z w hz hw
    set s : ℝ := (zhukovskyStage n : ℝ)
    have ha_pos : 0 < zhukovskyMajorAxis n := zhukovskyMajorAxis_pos n
    have ha_eq : zhukovskyMajorAxis n = 1 / 2 - 1 / (2 * s) := rfl
    have hz_ub := (abs_lt.mp hz).2
    have hw_lb := (abs_lt.mp hw).1
    have hdiff_lt : (z - w).re < 1 / (2 * s) := by
      rw [Complex.sub_re]
      have h24 : 1 / (4 * s) + 1 / (4 * s) = 1 / (2 * s) := by ring
      linarith
    have hgt_a : zhukovskyMajorAxis n < 1 / 2 - (z - w).re := by rw [ha_eq]; linarith
    have hsq_gt : zhukovskyMajorAxis n ^ 2 < ((z - w).re - 1 / 2) ^ 2 := by
      have h1 : ((z - w).re - 1 / 2) ^ 2 = (1 / 2 - (z - w).re) ^ 2 := by ring
      rw [h1]; nlinarith
    have hdiv_gt : 1 < ((z - w).re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 :=
      (one_lt_div (sq_pos_of_pos ha_pos)).mpr hsq_gt
    unfold zhukovskyEllipseForm
    have him_nn : 0 ≤ (z - w).im ^ 2 / zhukovskyMinorAxis n ^ 2 := by positivity
    linarith
  · intro n hn6 z w hz hw
    have hs_eq : (zhukovskyStage n : ℝ) = (n : ℝ) := by exact_mod_cast zhukovskyStage_eq_self hn6
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have ha_pos : 0 < zhukovskyMajorAxis n := zhukovskyMajorAxis_pos n
    have ha_lt : zhukovskyMajorAxis n < 1 / 2 := zhukovskyMajorAxis_lt_half n
    have ha_eq : zhukovskyMajorAxis n = 1 / 2 - 1 / (2 * (n : ℝ)) := by
      unfold zhukovskyMajorAxis; rw [hs_eq]
    have hz_ub := (abs_le.mp hz).2
    have hw_lb := (abs_le.mp hw).1
    have hdiff_le : (z - w).re ≤ 1 / (4 * (n : ℝ)) := by
      rw [Complex.sub_re]
      have h84 : 1 / (8 * (n : ℝ)) + 1 / (8 * (n : ℝ)) = 1 / (4 * (n : ℝ)) := by ring
      linarith
    have hge_a : zhukovskyMajorAxis n + 1 / (4 * (n : ℝ)) ≤ 1 / 2 - (z - w).re := by
      rw [ha_eq]
      have h24 : 1 / (2 * (n : ℝ)) - 1 / (4 * (n : ℝ)) = 1 / (4 * (n : ℝ)) := by ring
      linarith
    have hsq_ge : zhukovskyMajorAxis n ^ 2 + zhukovskyMajorAxis n / (2 * (n : ℝ)) ≤
        ((z - w).re - 1 / 2) ^ 2 := by
      have h1 : ((z - w).re - 1 / 2) ^ 2 = (1 / 2 - (z - w).re) ^ 2 := by ring
      have h2 : (zhukovskyMajorAxis n + 1 / (4 * (n : ℝ))) ^ 2 =
          zhukovskyMajorAxis n ^ 2 + zhukovskyMajorAxis n / (2 * (n : ℝ)) +
            1 / (16 * (n : ℝ) ^ 2) := by ring
      have h3 : 0 ≤ 1 / (16 * (n : ℝ) ^ 2) := by positivity
      have hp := pow_le_pow_left₀ (by positivity) hge_a 2
      linarith
    have hform_ge : 1 + 1 / (n : ℝ) ≤ zhukovskyEllipseForm n (z - w) := by
      unfold zhukovskyEllipseForm
      have him_nn : 0 ≤ (z - w).im ^ 2 / zhukovskyMinorAxis n ^ 2 := by positivity
      have hdiv : 1 + 1 / (n : ℝ) ≤ ((z - w).re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos ha_pos)]
        have h_an : (1 / (n : ℝ)) * zhukovskyMajorAxis n ^ 2 ≤
            zhukovskyMajorAxis n / (2 * (n : ℝ)) := by
          calc (1 / (n : ℝ)) * zhukovskyMajorAxis n ^ 2
              = (1 / (n : ℝ)) * zhukovskyMajorAxis n * zhukovskyMajorAxis n := by ring
            _ ≤ (1 / (n : ℝ)) * zhukovskyMajorAxis n * (1 / 2) :=
                mul_le_mul_of_nonneg_left ha_lt.le (by positivity)
            _ = zhukovskyMajorAxis n / (2 * (n : ℝ)) := by ring
        linarith
      linarith
    refine ⟨by linarith [one_div_pos.mpr hn_pos], ?_⟩
    rw [abs_of_pos (by linarith [one_div_pos.mpr hn_pos])]
    have hn6_r : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn6
    have hcube : 1 / (8 * (n : ℝ) ^ 3) ≤ 1 / (n : ℝ) := by
      refine one_div_le_one_div_of_le hn_pos ?_
      have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by linarith)
      nlinarith
    linarith

/-- **Off-line horizontal collision detection lemma.**
In any reflection-symmetric finite root set `Z` (`w ∈ Z → 1 - conj w ∈ Z`) with positive
multiplicities, any root `ρ ∈ Z` in the resolved band
`1 / (4 * s_n) < |ρ.re - 1 / 2| < 1 / 2 - 1 / (4 * s_n)` produces an interior horizontal pair
`(z, 1 - conj z)` (`zhukovskyEllipseForm n (z - (1 - conj z)) < 1`), forcing the doubled collision
sum to be `≥ 2`. -/
theorem two_le_collision_sum_of_offLine_in_band {Z : Finset ℂ} {mult : ℂ → ℕ} {n : ℕ}
    (hrefl : ∀ w ∈ Z, 1 - star w ∈ Z)
    (hmult_pos : ∀ w ∈ Z, 1 ≤ mult w)
    {ρ : ℂ} (hρ : ρ ∈ Z)
    (hband_lo : 1 / (4 * (zhukovskyStage n : ℝ)) < |ρ.re - 1 / 2|)
    (hband_hi : |ρ.re - 1 / 2| < 1 / 2 - 1 / (4 * (zhukovskyStage n : ℝ))) :
    2 ≤ 2 * ∑ z ∈ Z, ∑ w ∈ Z,
      (mult z : ℤ) * (mult w : ℤ) * (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0) := by
  let z₀ : ℂ := if 1 / 2 ≤ ρ.re then ρ else 1 - star ρ
  let w₀ : ℂ := 1 - star z₀
  have hz₀_mem : z₀ ∈ Z := by
    dsimp only [z₀]; split_ifs with h
    · exact hρ
    · exact hrefl ρ hρ
  have hw₀_mem : w₀ ∈ Z := hrefl z₀ hz₀_mem
  have hz₀_re : z₀.re - 1 / 2 = |ρ.re - 1 / 2| := by
    dsimp only [z₀]
    split_ifs with h
    · rw [abs_of_nonneg (by linarith)]
    · have hlt : ρ.re - 1 / 2 < 0 := by linarith
      rw [abs_of_neg hlt]; simp; ring
  have hdiff_im : (z₀ - w₀).im = 0 := by dsimp only [w₀]; simp
  have hdiff_re : (z₀ - w₀).re - 1 / 2 = 2 * |ρ.re - 1 / 2| - 1 / 2 := by
    have h1 : (z₀ - w₀).re = 2 * z₀.re - 1 := by dsimp only [w₀]; simp; ring
    linarith [hz₀_re]
  have ha_pos : 0 < zhukovskyMajorAxis n := zhukovskyMajorAxis_pos n
  have ha_eq : zhukovskyMajorAxis n = 1 / 2 - 1 / (2 * (zhukovskyStage n : ℝ)) := rfl
  have habs_lt : |(z₀ - w₀).re - 1 / 2| < zhukovskyMajorAxis n := by
    rw [hdiff_re, ha_eq, abs_lt]
    have h24 : 2 * (1 / (4 * (zhukovskyStage n : ℝ))) = 1 / (2 * (zhukovskyStage n : ℝ)) := by ring
    exact ⟨by linarith, by linarith⟩
  have hform_lt1 : zhukovskyEllipseForm n (z₀ - w₀) < 1 := by
    unfold zhukovskyEllipseForm
    rw [hdiff_im, show (0 : ℝ) ^ 2 / zhukovskyMinorAxis n ^ 2 = 0 by ring,
      add_zero, div_lt_one (sq_pos_of_pos ha_pos)]
    have hsq := sq_lt_sq.mpr (by rwa [abs_of_pos ha_pos] : |(z₀ - w₀).re - 1 / 2| < |zhukovskyMajorAxis n|)
    exact hsq
  let term : ℂ → ℂ → ℤ := fun z w =>
    (mult z : ℤ) * (mult w : ℤ) * (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0)
  have hterm_nn : ∀ z w : ℂ, 0 ≤ term z w := fun z w => by
    dsimp only [term]
    split_ifs <;> positivity
  have hterm_ge1 : (1 : ℤ) ≤ term z₀ w₀ := by
    dsimp only [term]
    rw [if_pos hform_lt1, mul_one]
    have h1 : (1 : ℤ) ≤ (mult z₀ : ℤ) := by exact_mod_cast hmult_pos z₀ hz₀_mem
    have h2 : (1 : ℤ) ≤ (mult w₀ : ℤ) := by exact_mod_cast hmult_pos w₀ hw₀_mem
    nlinarith
  have hinner_ge : (1 : ℤ) ≤ ∑ w ∈ Z, term z₀ w :=
    hterm_ge1.trans (Finset.single_le_sum (f := fun w => term z₀ w)
      (fun w _ => hterm_nn z₀ w) hw₀_mem)
  have houter_ge : (1 : ℤ) ≤ ∑ z ∈ Z, ∑ w ∈ Z, term z w :=
    hinner_ge.trans (Finset.single_le_sum (f := fun z => ∑ w ∈ Z, term z w)
      (fun z _ => Finset.sum_nonneg fun w _ => hterm_nn z w) hz₀_mem)
  dsimp only [term] at houter_ge
  linarith

/-- Elementary sub-Gaussian bound `(Real.log ((m + 5 : ℕ) : ℝ))² ≤ 16 * Real.sqrt ((m + 5 : ℕ) : ℝ)`. -/
private lemma log_sq_le_sixteen_sqrt_add_five (m : ℕ) :
    (Real.log ((m + 5 : ℕ) : ℝ)) ^ 2 ≤ 16 * Real.sqrt ((m + 5 : ℕ) : ℝ) := by
  set x : ℝ := ((m + 5 : ℕ) : ℝ)
  have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast (show 1 ≤ m + 5 by omega)
  have hx_pos : 0 < x := by linarith
  set q : ℝ := Real.sqrt (Real.sqrt x)
  have hq_pos : 0 < q := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx_pos)
  have hq4 : q ^ 4 = x := by
    dsimp only [q]
    calc (Real.sqrt (Real.sqrt x)) ^ 4
        = ((Real.sqrt (Real.sqrt x)) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt x) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg x)]
      _ = x := Real.sq_sqrt hx_pos.le
  have hlog_x : Real.log x ≤ 4 * q := by
    rw [← hq4, Real.log_pow]
    have hl : Real.log q ≤ q := (Real.log_le_sub_one_of_pos hq_pos).trans (by linarith)
    push_cast; linarith
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  calc (Real.log x) ^ 2
      ≤ (4 * q) ^ 2 := pow_le_pow_left₀ hlog_nn hlog_x 2
    _ = 16 * (q ^ 2) := by ring
    _ = 16 * Real.sqrt x := by dsimp only [q]; rw [Real.sq_sqrt (Real.sqrt_nonneg x)]

private lemma sum_biUnion_le_sum_nat {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℕ) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      set u := t a ∪ s.biUnion t
      have hu_eq : u \ s.biUnion t ∪ s.biUnion t = u :=
        Finset.sdiff_union_of_subset Finset.subset_union_right
      have hsub : u \ s.biUnion t ⊆ t a := fun x hx => by
        rw [Finset.mem_sdiff, Finset.mem_union] at hx
        exact hx.1.resolve_right hx.2
      have hunion : ∑ x ∈ u, f x ≤ ∑ x ∈ t a, f x + ∑ x ∈ s.biUnion t, f x := by
        rw [← hu_eq, Finset.sum_union Finset.sdiff_disjoint]
        exact Nat.add_le_add_right
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _) _
      exact hunion.trans (Nat.add_le_add_left ih _)

/-- Burnol good-height bracketing geometry and `O(log(m + 5))` local zero-multiplicity bound on
each unit window `[m, m + 1)`. -/
private theorem exists_burnol_unit_window_geometry :
    ∃ (c_good : ℝ) (Y₁ Y₂ : ℕ → ℝ) (Z_box_fn : ℕ → Finset ℂ) (C_deg : ℝ),
      0 < c_good ∧ c_good ≤ 1 ∧ 6 ≤ C_deg ∧
      (∀ m : ℕ,
        (-1 / 12 : ℝ) ≤ Y₁ m ∧ Y₁ m ≤ (m : ℝ) - 1 / 12 ∧
        (m : ℝ) + 2 ≤ Y₂ m ∧ Y₂ m ≤ (m : ℝ) + 3 ∧ Y₂ m - Y₁ m ≤ 5 ∧
        (∀ t : ℝ,
          c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) ≤
            ‖_root_.RHTower.xi (_root_.RHTower.rectangleBoundaryPath
              (centeredWindowLowerLeft (Y₁ m)) (centeredWindowUpperRight (Y₂ m)) t)‖) ∧
        (∀ w : ℂ, w ∈ Z_box_fn m ↔
          (0 < w.re ∧ w.re < 1 ∧ Y₁ m < w.im ∧ w.im < Y₂ m) ∧ _root_.RHTower.xi w = 0) ∧
        xiUnitWindowZeros (m : ℝ) ⊆ Z_box_fn m ∧
        (∀ w ∈ Z_box_fn m, 1 - star w ∈ Z_box_fn m) ∧
        ((∑ w ∈ Z_box_fn m, (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ≤
          C_deg * Real.log ((m + 5 : ℕ) : ℝ)) := by
  obtain ⟨c_good, T_good, hc_good_pos, hc_good_le_low, hgood⟩ := exists_all_nat_burnol_good_height
  obtain ⟨C_loc, hC_loc1, hunit_log, _⟩ := exists_all_xiUnitWindowOrder_le_log
  have hc_good_le1 : c_good ≤ 1 := by
    have hexp_le : Real.exp (-Real.pi) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
    have hmul := mul_le_mul_of_nonneg_left hexp_le (by norm_num : (0 : ℝ) ≤ 5026 / 16875)
    linarith [hc_good_le_low]
  let y₁ : ℕ → ℝ := fun m => if m ≤ 1 then -1 / 12 else T_good (m - 2)
  let y₂ : ℕ → ℝ := fun m => T_good (m + 2)
  let Z_xi : ℕ → Finset ℂ := fun m =>
    ((_root_.RHTower.stripZeros_finite ((m + 4 : ℕ) : ℝ)).toFinset).filter
      fun w => y₁ m < w.im ∧ w.im < y₂ m
  let C_d : ℝ := 6 * C_loc
  have hC_d6 : 6 ≤ C_d := by dsimp only [C_d]; linarith
  refine ⟨c_good, y₁, y₂, Z_xi, C_d, hc_good_pos, hc_good_le1, hC_d6, fun m => ?_⟩
  obtain ⟨hT2_lo, hT2_hi, _, hT2_hor, hT2_vert⟩ := hgood (m + 2)
  have hy₂_lo : (m : ℝ) + 2 ≤ y₂ m := by dsimp only [y₂]; push_cast at hT2_lo; linarith
  have hy₂_hi : y₂ m ≤ (m : ℝ) + 3 := by dsimp only [y₂]; push_cast at hT2_hi; linarith
  have hy₁_bds : (-1 / 12 : ℝ) ≤ y₁ m ∧ y₁ m ≤ (m : ℝ) - 1 / 12 ∧ (m : ℝ) - 2 ≤ y₁ m := by
    dsimp only [y₁]
    split_ifs with hm1
    · have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hm_le1 : (m : ℝ) ≤ 1 := by exact_mod_cast hm1
      exact ⟨le_rfl, by linarith, by linarith⟩
    · obtain ⟨hlo, hhi, hhalf, _, _⟩ := hgood (m - 2)
      have hcast : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := Nat.cast_sub (by omega)
      rw [hcast] at hlo hhi
      exact ⟨by linarith, by linarith, hlo⟩
  have hspan5 : y₂ m - y₁ m ≤ 5 := by linarith [hy₁_bds.2.2, hy₂_hi]
  have him_le : (centeredWindowLowerLeft (y₁ m)).im ≤ (centeredWindowUpperRight (y₂ m)).im := by
    simp; linarith [hy₁_bds.2.1, hy₂_lo]
  have hre_le : (centeredWindowLowerLeft (y₁ m)).re ≤ (centeredWindowUpperRight (y₂ m)).re := by
    simp; norm_num
  have hbdry_m : ∀ t : ℝ,
      c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) ≤
        ‖_root_.RHTower.xi (_root_.RHTower.rectangleBoundaryPath
          (centeredWindowLowerLeft (y₁ m)) (centeredWindowUpperRight (y₂ m)) t)‖ := by
    intro t
    set w := _root_.RHTower.rectangleBoundaryPath
      (centeredWindowLowerLeft (y₁ m)) (centeredWindowUpperRight (y₂ m)) t
    have hrect := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm _ _ hre_le him_le t
    rw [uIcc_of_le hre_le, uIcc_of_le him_le, Complex.mem_reProdIm] at hrect
    simp only [centeredWindowLowerLeft_re, centeredWindowUpperRight_re,
      centeredWindowLowerLeft_im, centeredWindowUpperRight_im] at hrect
    have hw_eq : ((w.re : ℂ) + (w.im : ℂ) * I) = w := Complex.re_add_im w
    have him_abs : |w.im| ≤ T_good (m + 2) := by
      refine abs_le.mpr ⟨?_, hrect.2.2⟩
      have hT2_ge2 : (2 : ℝ) ≤ T_good (m + 2) := by linarith [hy₂_lo, Nat.cast_nonneg (α := ℝ) m]
      linarith [hrect.2.1, hy₁_bds.1]
    have hm2_nat : m + 2 + 1 = m + 3 := by omega
    rw [hm2_nat] at hT2_hor hT2_vert
    rcases rectangleBoundaryPath_on_edges'
        (centeredWindowLowerLeft (y₁ m)) (centeredWindowUpperRight (y₂ m)) t with h1 | h2 | h3 | h4
    · rw [← hw_eq, h1, centeredWindowLowerLeft_re]
      rw [show ((-1 / 2 : ℝ) : ℂ) = -1 / 2 by norm_num]
      exact (hT2_vert w.im him_abs).2
    · rw [← hw_eq, h2, centeredWindowUpperRight_re]
      rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by norm_num]
      exact (hT2_vert w.im him_abs).1
    · rw [← hw_eq, h3, centeredWindowLowerLeft_im]
      dsimp only [y₁]
      split_ifs with hm1
      · have hexp1 : Real.exp (-((m + 3 : ℕ) : ℝ)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
        have hμ_low : c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) ≤
            (5026 / 16875) * Real.exp (-Real.pi) := by
          calc c_good * Real.exp (-((m + 3 : ℕ) : ℝ))
              ≤ c_good * 1 := mul_le_mul_of_nonneg_left hexp1 hc_good_pos.le
            _ = c_good := mul_one _
            _ ≤ (5026 / 16875) * Real.exp (-Real.pi) := hc_good_le_low
        exact hμ_low.trans ((xi_re_ge_lowWindow
          (by simp; exact abs_le.mpr ⟨by linarith [hrect.1.1], by linarith [hrect.1.2]⟩)
          (by simp; norm_num)).trans (Complex.re_le_norm _))
      · obtain ⟨_, _, _, hhor_m2, _⟩ := hgood (m - 2)
        have hexp_le : Real.exp (-((m + 3 : ℕ) : ℝ)) ≤
            Real.exp (-((m - 2 + 1 : ℕ) : ℝ)) :=
          Real.exp_le_exp.mpr (by
            have : ((m - 2 + 1 : ℕ) : ℝ) ≤ ((m + 3 : ℕ) : ℝ) := by
              exact_mod_cast (show m - 2 + 1 ≤ m + 3 by omega)
            linarith)
        exact (mul_le_mul_of_nonneg_left hexp_le hc_good_pos.le).trans
          (hhor_m2 w.re (by linarith [hrect.1.1]) (by linarith [hrect.1.2]))
    · rw [← hw_eq, h4, centeredWindowUpperRight_im]
      dsimp only [y₂]
      exact hT2_hor w.re (by linarith [hrect.1.1]) (by linarith [hrect.1.2])
  have hZ_iff : ∀ w : ℂ, w ∈ Z_xi m ↔
      (0 < w.re ∧ w.re < 1 ∧ y₁ m < w.im ∧ w.im < y₂ m) ∧ _root_.RHTower.xi w = 0 := by
    intro w
    dsimp only [Z_xi]
    rw [Finset.mem_filter, (_root_.RHTower.stripZeros_finite ((m + 4 : ℕ) : ℝ)).mem_toFinset]
    constructor
    · rintro ⟨⟨⟨hr0, hr1, _, _⟩, hw0⟩, hy_lo, hy_hi⟩
      exact ⟨⟨hr0, hr1, hy_lo, hy_hi⟩, hw0⟩
    · rintro ⟨⟨hr0, hr1, hy_lo, hy_hi⟩, hw0⟩
      have hy_nn : 0 ≤ w.im := by
        by_contra hneg
        have him61 : |w.im| ≤ 61 / 20 := abs_le.mpr ⟨by linarith [hy₁_bds.1], by linarith⟩
        have hpos := xi_re_ge_lowWindow (abs_le.mpr ⟨by linarith, by linarith⟩) him61
        rw [hw0, Complex.zero_re] at hpos
        have : (0 : ℝ) < (5026 / 16875) * Real.exp (-Real.pi) := by positivity
        linarith
      exact ⟨⟨⟨hr0, hr1, hy_nn, by push_cast; linarith⟩, hw0⟩, hy_lo, hy_hi⟩
  have hsub_unit : xiUnitWindowZeros (m : ℝ) ⊆ Z_xi m := by
    intro w hw
    obtain ⟨hS, hm_le⟩ := mem_xiUnitWindowZeros.mp hw
    obtain ⟨⟨hr0, hr1, _, hm1⟩, hw0⟩ := (_root_.RHTower.stripZeros_finite ((m : ℝ) + 1)).mem_toFinset.mp hS
    rw [hZ_iff]
    exact ⟨⟨hr0, hr1, by linarith [hy₁_bds.2.1], by linarith [hy₂_lo]⟩, hw0⟩
  have hrefl_Z : ∀ w ∈ Z_xi m, 1 - star w ∈ Z_xi m := by
    intro w hw
    obtain ⟨⟨hr0, hr1, hy_lo, hy_hi⟩, hw0⟩ := (hZ_iff w).mp hw
    rw [hZ_iff]
    refine ⟨⟨by simp; linarith, by simp; linarith, by simpa using hy_lo, by simpa using hy_hi⟩, ?_⟩
    change _root_.RHTower.xi (1 - (starRingEnd ℂ) w) = 0
    rw [_root_.RHTower.xi_one_sub, _root_.RHTower.xi_conj, hw0, map_zero]
  have hd_bound : ((∑ w ∈ Z_xi m, (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ≤
      C_d * Real.log ((m + 5 : ℕ) : ℝ) := by
    let U5 : Finset ℂ := (Finset.Icc (m - 2) (m + 2)).biUnion fun k => xiUnitWindowZeros (k : ℝ)
    have hZ_sub_U5 : Z_xi m ⊆ U5 := by
      intro w hw
      obtain ⟨⟨hr0, hr1, hy_lo, hy_hi⟩, hw0⟩ := (hZ_iff w).mp hw
      have hw_nn : 0 ≤ w.im := by
        by_contra hneg
        have him61 : |w.im| ≤ 61 / 20 := abs_le.mpr ⟨by linarith [hy₁_bds.1], by linarith⟩
        have hpos := xi_re_ge_lowWindow (abs_le.mpr ⟨by linarith, by linarith⟩) him61
        rw [hw0, Complex.zero_re] at hpos
        have : (0 : ℝ) < (5026 / 16875) * Real.exp (-Real.pi) := by positivity
        linarith
      let k : ℕ := Nat.floor w.im
      have hk_le : (k : ℝ) ≤ w.im := Nat.floor_le hw_nn
      have hk_gt : w.im < (k : ℝ) + 1 := Nat.lt_floor_add_one w.im
      have hk_hi : k ≤ m + 2 := by
        have : (k : ℝ) < ((m + 3 : ℕ) : ℝ) := by push_cast; linarith [hy₂_hi]
        have hlt : k < m + 3 := Nat.cast_lt.mp this
        omega
      have hk_lo : m - 2 ≤ k := by
        by_cases hm2 : m ≤ 2
        · omega
        · have hsub2 : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := Nat.cast_sub (show 2 ≤ m by omega)
          have h1 : ((m - 2 : ℕ) : ℝ) < ((k + 1 : ℕ) : ℝ) := by
            rw [hsub2]; push_cast; linarith [hy₁_bds.2.2]
          have hlt : m - 2 < k + 1 := Nat.cast_lt.mp h1
          omega
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk_lo, hk_hi⟩,
        mem_xiUnitWindowZeros.mpr
          ⟨(_root_.RHTower.stripZeros_finite ((k : ℝ) + 1)).mem_toFinset.mpr
            ⟨⟨hr0, hr1, hw_nn, hk_gt⟩, hw0⟩, hk_le⟩⟩
    have hsum_le_nat :
        (∑ w ∈ Z_xi m, (analyticOrderAt _root_.RHTower.xi w).toNat) ≤
          ∑ k ∈ Finset.Icc (m - 2) (m + 2), xiUnitWindowOrder (k : ℝ) :=
      (Finset.sum_le_sum_of_subset hZ_sub_U5).trans
        (sum_biUnion_le_sum_nat (Finset.Icc (m - 2) (m + 2))
          (fun k => xiUnitWindowZeros (k : ℝ))
          (fun w => (analyticOrderAt _root_.RHTower.xi w).toNat))
    have hcard_Icc : (Finset.Icc (m - 2) (m + 2)).card ≤ 5 := by
      rw [Nat.card_Icc]; omega
    calc ((∑ w ∈ Z_xi m, (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ)
        ≤ ∑ k ∈ Finset.Icc (m - 2) (m + 2), (xiUnitWindowOrder (k : ℝ) : ℝ) := by
          exact_mod_cast hsum_le_nat
      _ ≤ ∑ _k ∈ Finset.Icc (m - 2) (m + 2), (C_loc * Real.log ((m + 6 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => (hunit_log k).trans ?_
          have hk_hi := (Finset.mem_Icc.mp hk).2
          exact mul_le_mul_of_nonneg_left
            (Real.log_le_log (by exact_mod_cast (show 0 < k + 4 by omega))
              (by exact_mod_cast (show k + 4 ≤ m + 6 by omega))) (by linarith)
      _ ≤ 5 * (C_loc * Real.log ((m + 5 : ℕ) : ℝ)) * (6 / 5) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hc5 : ((Finset.Icc (m - 2) (m + 2)).card : ℝ) ≤ 5 := by exact_mod_cast hcard_Icc
          have hlog6 : Real.log ((m + 6 : ℕ) : ℝ) ≤ (6 / 5) * Real.log ((m + 5 : ℕ) : ℝ) := by
            have hpow56 : ((m + 6 : ℕ) : ℝ) ^ 5 ≤ ((m + 5 : ℕ) : ℝ) ^ 6 := by
              set x : ℝ := ((m + 5 : ℕ) : ℝ)
              have hx5 : 5 ≤ x := by dsimp only [x]; exact_mod_cast (show 5 ≤ m + 5 by omega)
              have hx1 : ((m + 6 : ℕ) : ℝ) = x + 1 := by dsimp only [x]; push_cast; ring
              rw [hx1]
              have h65 : x + 1 ≤ (6 / 5) * x := by linarith
              have hp5 := pow_le_pow_left₀ (by linarith) h65 5
              have h7776 : ((6 / 5 : ℝ) ^ 5) ≤ 5 := by norm_num
              calc (x + 1) ^ 5 ≤ (6 / 5) ^ 5 * x ^ 5 := by rw [mul_pow] at hp5; exact hp5
                _ ≤ 5 * x ^ 5 := mul_le_mul_of_nonneg_right h7776 (by positivity)
                _ ≤ x * x ^ 5 := mul_le_mul_of_nonneg_right hx5 (by positivity)
                _ = x ^ 6 := by ring
            have hl := Real.log_le_log (by positivity) hpow56
            rw [Real.log_pow, Real.log_pow, Nat.cast_ofNat, Nat.cast_ofNat] at hl
            linarith
          have h1 := mul_le_mul hc5
            (mul_le_mul_of_nonneg_left hlog6 (by linarith : 0 ≤ C_loc))
            (mul_nonneg (by linarith) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 6 by omega))))
            (by norm_num)
          linarith
      _ = C_d * Real.log ((m + 5 : ℕ) : ℝ) := by dsimp only [C_d]; ring
  exact ⟨hy₁_bds.1, hy₁_bds.2.1, hy₂_lo, hy₂_hi, hspan5, hbdry_m, hZ_iff, hsub_unit, hrefl_Z,
    hd_bound⟩

/-- Real-analytic prefix budget selector for `centeredTheta_sqrtPrefix_stabilization`:
chooses `K_unit ≥ 4` (`C_deg ≤ K_unit`) so that at every integer window height `m` and opaque
degree `d ≤ C_deg log(m + 5)`, both the base `Θ(√m)` tail/prefactor/single-stage Rouché bounds
and the unrestricted-`S` Rouché bound hold uniformly. -/
private theorem exists_centered_unit_prefix_constant
    {c_good C_deg M_strip : ℝ} (hc_good_pos : 0 < c_good) (hC_d6 : 6 ≤ C_deg) (hM1 : 1 ≤ M_strip) :
    ∃ K_unit : ℕ, 4 ≤ K_unit ∧ C_deg ≤ (K_unit : ℝ) ∧
      ∀ (m d : ℕ),
        (d : ℝ) ≤ C_deg * Real.log ((m + 5 : ℕ) : ℝ) →
        let μ : ℝ := c_good * Real.exp (-((m + 3 : ℕ) : ℝ))
        (∀ N : ℕ, K_unit * (Nat.sqrt m + 1) ≤ N →
          thetaStripTailBound N ≤ μ / 2 ∧
          (4 * (2 * M_strip + 1) * 5 / μ ^ 2) * thetaStripTailBound N ≤ 1 / 2) ∧
        (∀ S_max N : ℕ,
          (S_max : ℝ) ≤ 6 * Real.exp (Real.sqrt ((m + 5 : ℕ) : ℝ)) + 2 * (d : ℝ) ^ 2 →
          K_unit * (Nat.sqrt m + 1) ≤ N →
          4 * ((4 * (2 * M_strip + 1) * 5 / μ ^ 2) * thetaStripTailBound N) *
            (((d + 1 : ℕ) : ℝ) ^ 4) * (896 * (4 : ℝ) * (S_max : ℝ) ^ 4) ^ (d ^ 2) < 1) ∧
        (∀ S N : ℕ,
          K_unit * (Nat.sqrt m + 1 +
            (Nat.ceil (Real.log ((m + 5 : ℕ) : ℝ)) + 1) *
              (Nat.ceil (Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ))) + 1)) ≤ N →
          let S_max : ℕ := max S 6 + 2 * d ^ 2
          4 * ((4 * (2 * M_strip + 1) * 5 / μ ^ 2) * thetaStripTailBound N) *
            (((d + 1 : ℕ) : ℝ) ^ 4) * (896 * (4 : ℝ) * (S_max : ℝ) ^ 4) ^ (d ^ 2) < 1) := by
  let C_env : ℝ :=
    _root_.RHTower.thetaCuspIntegerTailConstant * _root_.RHTower.thetaAmplitudeEnvelope 2 + 1
  have hC_env1 : 1 ≤ C_env := by
    dsimp only [C_env]
    have hnn := mul_nonneg _root_.RHTower.thetaCuspIntegerTailConstant_nonneg
      (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2)
    linarith
  have hC_env_tail : ∀ N : ℕ,
      thetaStripTailBound N ≤ C_env * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) := fun N => by
    unfold thetaStripTailBound
    exact mul_le_mul_of_nonneg_right (by dsimp only [C_env]; linarith) (Real.exp_pos _).le
  let K_pre_u : ℝ := 20 * (2 * M_strip + 1) * C_env / c_good ^ 2 + 1
  have hK_pre_u1 : 1 ≤ K_pre_u := by dsimp only [K_pre_u]; exact le_add_of_nonneg_left (by positivity)
  have hK_pre_u_def : 20 * (2 * M_strip + 1) * C_env / c_good ^ 2 ≤ K_pre_u := by
    dsimp only [K_pre_u]; linarith
  let K_base_u : ℝ := 3584 * (6 + 32 * C_deg ^ 2) ^ 4
  have hK_base_u1 : 1 ≤ K_base_u := by
    dsimp only [K_base_u]
    have hp : (1 : ℝ) ≤ (6 + 32 * C_deg ^ 2) ^ 4 := one_le_pow₀ (by linarith [sq_nonneg C_deg])
    linarith
  have hK_base_u_def : 3584 * (6 + 32 * C_deg ^ 2) ^ 4 = K_base_u := rfl
  have hCd4 : (1 : ℝ) ≤ (C_deg + 1) ^ 4 := one_le_pow₀ (by linarith)
  have hlog4Ku_nn : 0 ≤ Real.log (4 * K_pre_u * (C_deg + 1) ^ 4) := by
    refine Real.log_nonneg ?_
    have hm := mul_le_mul_of_nonneg_left hCd4 (by positivity : (0 : ℝ) ≤ 4 * K_pre_u)
    linarith
  let B_unit : ℝ :=
    (1 + |Real.log (2 * C_env / c_good)|) +
    (2 + Real.log (2 * K_pre_u)) +
    (Real.log (4 * K_pre_u * (C_deg + 1) ^ 4) + 6 + 16 * C_deg ^ 2 * (Real.log K_base_u + 4)) + 2
  have hB_unit2 : 2 ≤ B_unit := by
    dsimp only [B_unit]
    have h1 : 0 ≤ Real.log (2 * K_pre_u) := Real.log_nonneg (by linarith)
    have h3 : 0 ≤ 16 * C_deg ^ 2 * (Real.log K_base_u + 4) :=
      mul_nonneg (by positivity) (by linarith [Real.log_nonneg hK_base_u1])
    linarith [abs_nonneg (Real.log (2 * C_env / c_good)), hlog4Ku_nn]
  have hBu_part1 : 1 + |Real.log (2 * C_env / c_good)| ≤ B_unit := by
    dsimp only [B_unit]
    have h1 : 0 ≤ Real.log (2 * K_pre_u) := Real.log_nonneg (by linarith)
    have h3 : 0 ≤ 16 * C_deg ^ 2 * (Real.log K_base_u + 4) :=
      mul_nonneg (by positivity) (by linarith [Real.log_nonneg hK_base_u1])
    linarith [hlog4Ku_nn]
  have hBu_part2 : 2 + Real.log (2 * K_pre_u) ≤ B_unit := by
    dsimp only [B_unit]
    have h3 : 0 ≤ 16 * C_deg ^ 2 * (Real.log K_base_u + 4) :=
      mul_nonneg (by positivity) (by linarith [Real.log_nonneg hK_base_u1])
    linarith [abs_nonneg (Real.log (2 * C_env / c_good)), hlog4Ku_nn]
  have hBu_part3 :
      Real.log (4 * K_pre_u * (C_deg + 1) ^ 4) + 6 +
        16 * C_deg ^ 2 * (Real.log K_base_u + 4) + 1 ≤ B_unit := by
    dsimp only [B_unit]
    linarith [abs_nonneg (Real.log (2 * C_env / c_good)),
      Real.log_nonneg (show 1 ≤ 2 * K_pre_u by linarith)]
  let C_unit : ℕ := max 4 (max (Nat.ceil (2 * C_deg)) (Nat.ceil (Real.sqrt (5 * B_unit)) + 1))
  have hCu4 : 4 ≤ C_unit := le_max_left _ _
  have h2Cd_le : 2 * C_deg ≤ (C_unit : ℝ) := by
    calc 2 * C_deg ≤ (Nat.ceil (2 * C_deg) : ℝ) := Nat.le_ceil (2 * C_deg)
      _ ≤ (C_unit : ℝ) := by
        exact_mod_cast ((le_max_left _ _).trans (le_max_right 4 _))
  have hCd_le : C_deg ≤ (C_unit : ℝ) := by linarith
  have hCu_sq : 5 * B_unit ≤ (C_unit : ℝ) ^ 2 := by
    have hrt : Real.sqrt (5 * B_unit) ≤ (C_unit : ℝ) := by
      calc Real.sqrt (5 * B_unit)
          ≤ ((Nat.ceil (Real.sqrt (5 * B_unit)) + 1 : ℕ) : ℝ) := by
            push_cast; linarith [Nat.le_ceil (Real.sqrt (5 * B_unit))]
        _ ≤ (C_unit : ℝ) := by
            exact_mod_cast ((le_max_right _ _).trans (le_max_right 4 _))
    calc 5 * B_unit = (Real.sqrt (5 * B_unit)) ^ 2 := (Real.sq_sqrt (by linarith)).symm
      _ ≤ (C_unit : ℝ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hrt 2
  generalize C_unit = K_unit at hCu4 h2Cd_le hCd_le hCu_sq
  generalize B_unit = B_u at hB_unit2 hCu_sq hBu_part1 hBu_part2 hBu_part3
  generalize K_base_u = K_bu at hK_base_u1 hK_base_u_def hBu_part3
  generalize K_pre_u = K_pu at hK_pre_u1 hK_pre_u_def hlog4Ku_nn hBu_part2 hBu_part3
  generalize C_env = C_eu at hC_env1 hC_env_tail hK_pre_u_def hBu_part1
  clear C_unit B_unit K_base_u K_pre_u C_env
  have hKu_pos : 0 < (K_unit : ℝ) := by exact_mod_cast (show 0 < K_unit by omega)
  have hKbu_pos : 0 < K_bu := by linarith only [hK_base_u1]
  have hKpu_pos : 0 < K_pu := by linarith only [hK_pre_u1]
  have hCeu_pos : 0 < C_eu := by linarith only [hC_env1]
  have hCdeg_pos : 0 < C_deg := by linarith only [hC_d6]
  have hM_pos : 0 < M_strip := by linarith only [hM1]
  refine ⟨K_unit, hCu4, hCd_le, fun m d hd_Cd => ?_⟩
  intro μ
  set X_m : ℝ := ((m + 5 : ℕ) : ℝ)
  have hX5 : 5 ≤ X_m := by dsimp only [X_m]; exact_mod_cast (show 5 ≤ m + 5 by omega)
  have hX1 : 1 ≤ X_m := by linarith only [hX5]
  have hX_pos : 0 < X_m := by linarith only [hX1]
  have hlogX_nn : 0 ≤ Real.log X_m := Real.log_nonneg hX1
  have hA_sq : B_u * X_m ≤ ((K_unit : ℝ) * ((Nat.sqrt m + 1 : ℕ) : ℝ)) ^ 2 := by
    have hm1_le_sq : m + 1 ≤ (Nat.sqrt m + 1) ^ 2 := Nat.succ_le_of_lt (Nat.lt_succ_sqrt' m)
    have hX_le_sq : X_m ≤ 5 * ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by
      have h5 : m + 5 ≤ 5 * (m + 1) := by omega
      have hnat : m + 5 ≤ 5 * (Nat.sqrt m + 1) ^ 2 := h5.trans (Nat.mul_le_mul_left 5 hm1_le_sq)
      dsimp only [X_m]
      exact_mod_cast hnat
    calc B_u * X_m
        ≤ B_u * (5 * ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hX_le_sq (by linarith only [hB_unit2])
      _ = (5 * B_u) * ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by ring
      _ ≤ (K_unit : ℝ) ^ 2 * ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hCu_sq (by positivity)
      _ = ((K_unit : ℝ) * ((Nat.sqrt m + 1 : ℕ) : ℝ)) ^ 2 := by ring
  have hN1_sq_of : ∀ N : ℕ, K_unit * (Nat.sqrt m + 1) ≤ N →
      B_u * X_m ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
    intro N hN
    have hN1_ge : (K_unit : ℝ) * ((Nat.sqrt m + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (hN.trans (Nat.le_succ N))
    exact hA_sq.trans (pow_le_pow_left₀ (by positivity) hN1_ge 2)
  have hN_tail_of : ∀ N : ℕ, K_unit * (Nat.sqrt m + 1) ≤ N → thetaStripTailBound N ≤ μ / 2 := by
    intro N hN
    have hN1_sq := hN1_sq_of N hN
    have hexp_arg : -((N + 1 : ℕ) : ℝ) ^ 2 ≤
        Real.log (c_good / (2 * C_eu)) - ((m + 3 : ℕ) : ℝ) := by
      have hlog_abs : |Real.log (2 * C_eu / c_good)| = |Real.log (c_good / (2 * C_eu))| := by
        rw [show c_good / (2 * C_eu) = (2 * C_eu / c_good)⁻¹ by rw [inv_div], Real.log_inv, abs_neg]
      have hm3_X : ((m + 3 : ℕ) : ℝ) ≤ X_m := by
        dsimp only [X_m]; exact_mod_cast (show m + 3 ≤ m + 5 by omega)
      have h1 : ((m + 3 : ℕ) : ℝ) + |Real.log (2 * C_eu / c_good)| ≤
          (1 + |Real.log (2 * C_eu / c_good)|) * X_m := by
        have habs_le : |Real.log (2 * C_eu / c_good)| ≤
            |Real.log (2 * C_eu / c_good)| * X_m :=
          le_mul_of_one_le_right (abs_nonneg _) hX1
        linarith only [hm3_X, habs_le]
      have h2 := h1.trans ((mul_le_mul_of_nonneg_right hBu_part1 (by linarith only [hX1])).trans hN1_sq)
      linarith only [h2, neg_abs_le (Real.log (c_good / (2 * C_eu))), hlog_abs]
    calc thetaStripTailBound N
        ≤ C_eu * Real.exp (Real.log (c_good / (2 * C_eu)) - ((m + 3 : ℕ) : ℝ)) :=
          (hC_env_tail N).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) hCeu_pos.le)
      _ = μ / 2 := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by positivity)]
          dsimp only [μ]
          have hCeu_ne : C_eu ≠ 0 := hCeu_pos.ne'
          field_simp [hCeu_ne]
  have hpre_bound_of : ∀ N : ℕ,
      (4 * (2 * M_strip + 1) * 5 / μ ^ 2) * thetaStripTailBound N ≤
        K_pu * Real.exp (2 * X_m - ((N + 1 : ℕ) : ℝ) ^ 2) := by
    intro N
    have hμ_sq : μ ^ 2 = c_good ^ 2 * Real.exp (-2 * ((m + 3 : ℕ) : ℝ)) := by
      dsimp only [μ]
      rw [mul_pow, ← Real.exp_nat_mul,
        show ((2 : ℕ) : ℝ) * -((m + 3 : ℕ) : ℝ) = -2 * ((m + 3 : ℕ) : ℝ) by push_cast; ring]
    have hm3_X : 2 * ((m + 3 : ℕ) : ℝ) ≤ 2 * X_m := by
      dsimp only [X_m]; have : ((m + 3 : ℕ) : ℝ) ≤ ((m + 5 : ℕ) : ℝ) := by
        exact_mod_cast (show m + 3 ≤ m + 5 by omega)
      linarith
    calc (4 * (2 * M_strip + 1) * 5 / μ ^ 2) * thetaStripTailBound N
        ≤ (20 * (2 * M_strip + 1) / (c_good ^ 2 * Real.exp (-2 * ((m + 3 : ℕ) : ℝ)))) *
            (C_eu * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) := by
          rw [hμ_sq, show (4 : ℝ) * (2 * M_strip + 1) * 5 = 20 * (2 * M_strip + 1) by ring]
          exact mul_le_mul_of_nonneg_left (hC_env_tail N) (by positivity)
      _ = (20 * (2 * M_strip + 1) * C_eu / c_good ^ 2) *
            Real.exp (2 * ((m + 3 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ) ^ 2) := by
          field_simp [hc_good_pos.ne']
          rw [← Real.exp_add]
          exact congrArg Real.exp (by ring)
      _ ≤ K_pu * Real.exp (2 * X_m - ((N + 1 : ℕ) : ℝ) ^ 2) := by
          refine mul_le_mul hK_pre_u_def
            (Real.exp_le_exp.mpr (by linarith only [hm3_X])) (Real.exp_pos _).le hKpu_pos.le
  have hN_half_of : ∀ N : ℕ, K_unit * (Nat.sqrt m + 1) ≤ N →
      (4 * (2 * M_strip + 1) * 5 / μ ^ 2) * thetaStripTailBound N ≤ 1 / 2 := by
    intro N hN
    have hN1_sq := hN1_sq_of N hN
    have hexp_arg : 2 * X_m - ((N + 1 : ℕ) : ℝ) ^ 2 ≤ -Real.log (2 * K_pu) := by
      have h1 : 2 * X_m + Real.log (2 * K_pu) ≤ (2 + Real.log (2 * K_pu)) * X_m := by
        have hlog_le : Real.log (2 * K_pu) ≤ Real.log (2 * K_pu) * X_m :=
          le_mul_of_one_le_right (Real.log_nonneg (by linarith only [hK_pre_u1])) hX1
        linarith only [hlog_le]
      have h2 := h1.trans ((mul_le_mul_of_nonneg_right hBu_part2 (by linarith only [hX1])).trans hN1_sq)
      linarith only [h2]
    calc (4 * (2 * M_strip + 1) * 5 / μ ^ 2) * thetaStripTailBound N
        ≤ K_pu * Real.exp (-Real.log (2 * K_pu)) :=
          (hpre_bound_of N).trans
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) hKpu_pos.le)
      _ = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          have hKpu_ne : K_pu ≠ 0 := hKpu_pos.ne'
          field_simp [hKpu_ne]
  have hd1_exp : (((d + 1 : ℕ) : ℝ) ^ 4) ≤ (C_deg + 1) ^ 4 * Real.exp (4 * X_m) := by
    have hlog_le_X : Real.log X_m ≤ X_m :=
      (Real.log_le_sub_one_of_pos hX_pos).trans (by linarith)
    have hd_X : (d : ℝ) ≤ C_deg * X_m :=
      hd_Cd.trans (mul_le_mul_of_nonneg_left hlog_le_X (by linarith only [hC_d6]))
    have hd1_X : ((d + 1 : ℕ) : ℝ) ≤ (C_deg + 1) * Real.exp X_m := by
      have h1 : ((d + 1 : ℕ) : ℝ) ≤ (C_deg + 1) * X_m := by
        have hc : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
        rw [hc]; linarith only [hd_X, hX1]
      have h2 : X_m ≤ Real.exp X_m := by linarith [Real.add_one_le_exp X_m]
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    calc (((d + 1 : ℕ) : ℝ) ^ 4)
        ≤ ((C_deg + 1) * Real.exp X_m) ^ 4 := pow_le_pow_left₀ (by positivity) hd1_X 4
      _ = (C_deg + 1) ^ 4 * Real.exp (4 * X_m) := by
          rw [mul_pow, ← Real.exp_nat_mul,
            show ((4 : ℕ) : ℝ) * X_m = 4 * X_m by push_cast; ring]
  have hd2_sqrt : (d : ℝ) ^ 2 ≤ 16 * C_deg ^ 2 * Real.sqrt X_m := by
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg d) hd_Cd 2
    have hl16 := log_sq_le_sixteen_sqrt_add_five m
    calc (d : ℝ) ^ 2
        ≤ (C_deg * Real.log X_m) ^ 2 := hsq
      _ = C_deg ^ 2 * (Real.log X_m) ^ 2 := by ring
      _ ≤ C_deg ^ 2 * (16 * Real.sqrt X_m) := mul_le_mul_of_nonneg_left hl16 (sq_nonneg _)
      _ = 16 * C_deg ^ 2 * Real.sqrt X_m := by ring
  have hrouche_of_extra : ∀ (S_max N : ℕ) (L_extra : ℝ),
      (S_max : ℝ) ≤ (6 + 32 * C_deg ^ 2) * Real.exp (Real.sqrt X_m + L_extra) →
      B_u * X_m + 4 * (d : ℝ) ^ 2 * L_extra ≤ ((N + 1 : ℕ) : ℝ) ^ 2 →
      4 * ((4 * (2 * M_strip + 1) * 5 / μ ^ 2) * thetaStripTailBound N) *
        (((d + 1 : ℕ) : ℝ) ^ 4) * (896 * (4 : ℝ) * (S_max : ℝ) ^ 4) ^ (d ^ 2) < 1 := by
    intro S_max N L_extra hS_exp hN1_sq_extra
    have hbase_exp : 896 * (4 : ℝ) * (S_max : ℝ) ^ 4 ≤
        K_bu * Real.exp (4 * Real.sqrt X_m + 4 * L_extra) := by
      calc 896 * (4 : ℝ) * (S_max : ℝ) ^ 4
          ≤ 3584 * ((6 + 32 * C_deg ^ 2) * Real.exp (Real.sqrt X_m + L_extra)) ^ 4 := by
            rw [show (896 : ℝ) * 4 = 3584 by norm_num]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (Nat.cast_nonneg _) hS_exp 4) (by norm_num)
        _ = K_bu * Real.exp (4 * Real.sqrt X_m + 4 * L_extra) := by
            rw [mul_pow, ← mul_assoc, hK_base_u_def, ← Real.exp_nat_mul,
              show ((4 : ℕ) : ℝ) * (Real.sqrt X_m + L_extra) =
                4 * Real.sqrt X_m + 4 * L_extra by push_cast; ring]
    have hpow_d2 : (896 * (4 : ℝ) * (S_max : ℝ) ^ 4) ^ (d ^ 2) ≤
        Real.exp (16 * C_deg ^ 2 * (Real.log K_bu + 4) * X_m + 4 * (d : ℝ) ^ 2 * L_extra) := by
      have h1 : 896 * (4 : ℝ) * (S_max : ℝ) ^ 4 ≤
          Real.exp (Real.log K_bu + (4 * Real.sqrt X_m + 4 * L_extra)) := by
        rw [Real.exp_add, Real.exp_log hKbu_pos]
        exact hbase_exp
      have hbase_nn : 0 ≤ 896 * (4 : ℝ) * (S_max : ℝ) ^ 4 :=
        mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) 4)
      have hp := pow_le_pow_left₀ hbase_nn h1 (d ^ 2)
      rw [← Real.exp_nat_mul] at hp
      refine hp.trans (Real.exp_le_exp.mpr ?_)
      have hsqrt1 : 1 ≤ Real.sqrt X_m := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hX1
      have hKb_sqrt : Real.log K_bu + 4 * Real.sqrt X_m ≤
          (Real.log K_bu + 4) * Real.sqrt X_m := by
        have hlog_le : Real.log K_bu ≤ Real.log K_bu * Real.sqrt X_m :=
          le_mul_of_one_le_right (Real.log_nonneg hK_base_u1) hsqrt1
        linarith only [hlog_le]
      have hd2_cast : ((d ^ 2 : ℕ) : ℝ) = (d : ℝ) ^ 2 := by push_cast; ring
      rw [hd2_cast]
      have hpart1 : (d : ℝ) ^ 2 * (Real.log K_bu + 4 * Real.sqrt X_m) ≤
          16 * C_deg ^ 2 * (Real.log K_bu + 4) * X_m := by
        calc (d : ℝ) ^ 2 * (Real.log K_bu + 4 * Real.sqrt X_m)
            ≤ (16 * C_deg ^ 2 * Real.sqrt X_m) * ((Real.log K_bu + 4) * Real.sqrt X_m) :=
              mul_le_mul hd2_sqrt hKb_sqrt
                (add_nonneg (Real.log_nonneg hK_base_u1) (by positivity)) (by positivity)
          _ = 16 * C_deg ^ 2 * (Real.log K_bu + 4) * (Real.sqrt X_m ^ 2) := by ring
          _ = 16 * C_deg ^ 2 * (Real.log K_bu + 4) * X_m := by rw [Real.sq_sqrt hX_pos.le]
      have hsplit :
          (d : ℝ) ^ 2 * (Real.log K_bu + (4 * Real.sqrt X_m + 4 * L_extra)) =
          (d : ℝ) ^ 2 * (Real.log K_bu + 4 * Real.sqrt X_m) + 4 * (d : ℝ) ^ 2 * L_extra := by ring
      linarith only [hsplit, hpart1]
    have h4K_pos : 0 < 4 * K_pu * (C_deg + 1) ^ 4 := by positivity
    have hprod_le :
        4 * ((4 * (2 * M_strip + 1) * 5 / μ ^ 2) * thetaStripTailBound N) *
          (((d + 1 : ℕ) : ℝ) ^ 4) * (896 * (4 : ℝ) * (S_max : ℝ) ^ 4) ^ (d ^ 2) ≤
        Real.exp (Real.log (4 * K_pu * (C_deg + 1) ^ 4) +
          6 * X_m + 16 * C_deg ^ 2 * (Real.log K_bu + 4) * X_m +
          4 * (d : ℝ) ^ 2 * L_extra - ((N + 1 : ℕ) : ℝ) ^ 2) := by
      have hm12 := mul_le_mul
        (mul_le_mul_of_nonneg_left (hpre_bound_of N) (by norm_num : (0 : ℝ) ≤ 4))
        hd1_exp (by positivity) (by positivity)
      have hm123 := mul_le_mul hm12 hpow_d2 (by positivity) (by positivity)
      refine hm123.trans_eq ?_
      symm
      rw [show Real.log (4 * K_pu * (C_deg + 1) ^ 4) +
            6 * X_m + 16 * C_deg ^ 2 * (Real.log K_bu + 4) * X_m +
            4 * (d : ℝ) ^ 2 * L_extra - ((N + 1 : ℕ) : ℝ) ^ 2 =
          Real.log (4 * K_pu * (C_deg + 1) ^ 4) +
            ((2 * X_m - ((N + 1 : ℕ) : ℝ) ^ 2) +
              4 * X_m +
              (16 * C_deg ^ 2 * (Real.log K_bu + 4) * X_m + 4 * (d : ℝ) ^ 2 * L_extra)) by ring]
      rw [Real.exp_add, Real.exp_log h4K_pos, Real.exp_add, Real.exp_add]
      ring
    refine hprod_le.trans_lt (Real.exp_lt_one_iff.mpr ?_)
    have hlog_le : Real.log (4 * K_pu * (C_deg + 1) ^ 4) ≤
        Real.log (4 * K_pu * (C_deg + 1) ^ 4) * X_m :=
      le_mul_of_one_le_right hlog4Ku_nn hX1
    have hmul := mul_le_mul_of_nonneg_right hBu_part3 hX_pos.le
    have hexp_ring :
        (Real.log (4 * K_pu * (C_deg + 1) ^ 4) + 6 +
          16 * C_deg ^ 2 * (Real.log K_bu + 4) + 1) * X_m =
        Real.log (4 * K_pu * (C_deg + 1) ^ 4) * X_m + 6 * X_m +
          16 * C_deg ^ 2 * (Real.log K_bu + 4) * X_m + X_m := by ring
    linarith only [hlog_le, hX1, hmul, hexp_ring, hN1_sq_extra]
  refine ⟨fun N hN => ⟨hN_tail_of N hN, hN_half_of N hN⟩, ?_, ?_⟩
  · intro S_max N hS_hi hN
    refine hrouche_of_extra S_max N 0 ?_ (by simpa using hN1_sq_of N hN)
    rw [add_zero]
    have hsqrt_exp : Real.sqrt X_m ≤ Real.exp (Real.sqrt X_m) := by
      linarith [Real.add_one_le_exp (Real.sqrt X_m)]
    have h2d2 : 2 * (d : ℝ) ^ 2 ≤ 32 * C_deg ^ 2 * Real.exp (Real.sqrt X_m) := by
      calc 2 * (d : ℝ) ^ 2
          ≤ 32 * C_deg ^ 2 * Real.sqrt X_m := by linarith only [hd2_sqrt]
        _ ≤ 32 * C_deg ^ 2 * Real.exp (Real.sqrt X_m) :=
            mul_le_mul_of_nonneg_left hsqrt_exp (by positivity)
    linarith only [hS_hi, h2d2]
  · intro S N hN S_max
    set L_S : ℝ := Real.log ((S + 6 : ℕ) : ℝ)
    have hLS_nn : 0 ≤ L_S := by
      dsimp only [L_S]
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ S + 6 by omega))
    set A_nat : ℕ := Nat.sqrt m + 1
    set D_nat : ℕ := (Nat.ceil (Real.log X_m) + 1) * (Nat.ceil (Real.sqrt L_S) + 1)
    have hN1_sq_AD : B_u * X_m + 4 * (d : ℝ) ^ 2 * L_S ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
      have hlogX_ceil : Real.log X_m ≤ ((Nat.ceil (Real.log X_m) + 1 : ℕ) : ℝ) :=
        (Nat.le_ceil _).trans (by push_cast; linarith)
      have hsqrtLS_ceil : Real.sqrt L_S ≤ ((Nat.ceil (Real.sqrt L_S) + 1 : ℕ) : ℝ) :=
        (Nat.le_ceil _).trans (by push_cast; linarith)
      have hD_ge : 2 * (d : ℝ) * Real.sqrt L_S ≤ (K_unit : ℝ) * (D_nat : ℝ) := by
        have h2d_le : 2 * (d : ℝ) ≤ 2 * C_deg * Real.log X_m := by linarith only [hd_Cd]
        have h2d_K : 2 * C_deg * Real.log X_m ≤
            (K_unit : ℝ) * ((Nat.ceil (Real.log X_m) + 1 : ℕ) : ℝ) :=
          mul_le_mul h2Cd_le hlogX_ceil hlogX_nn (by positivity)
        calc 2 * (d : ℝ) * Real.sqrt L_S
            ≤ ((K_unit : ℝ) * ((Nat.ceil (Real.log X_m) + 1 : ℕ) : ℝ)) *
                ((Nat.ceil (Real.sqrt L_S) + 1 : ℕ) : ℝ) :=
              mul_le_mul (h2d_le.trans h2d_K) hsqrtLS_ceil (Real.sqrt_nonneg _) (by positivity)
          _ = (K_unit : ℝ) * (D_nat : ℝ) := by dsimp only [D_nat]; push_cast; ring
      have hD_sq : 4 * (d : ℝ) ^ 2 * L_S ≤ ((K_unit : ℝ) * (D_nat : ℝ)) ^ 2 := by
        calc 4 * (d : ℝ) ^ 2 * L_S
            = 4 * (d : ℝ) ^ 2 * (Real.sqrt L_S) ^ 2 := by rw [Real.sq_sqrt hLS_nn]
          _ = (2 * (d : ℝ) * Real.sqrt L_S) ^ 2 := by ring
          _ ≤ ((K_unit : ℝ) * (D_nat : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hD_ge 2
      have hN1_ge_AD :
          (K_unit : ℝ) * (A_nat : ℝ) + (K_unit : ℝ) * (D_nat : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        have hnat : ((K_unit * (A_nat + D_nat) : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast (hN.trans (Nat.le_succ N))
        calc (K_unit : ℝ) * (A_nat : ℝ) + (K_unit : ℝ) * (D_nat : ℝ)
            = ((K_unit * (A_nat + D_nat) : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((N + 1 : ℕ) : ℝ) := hnat
      have hp := pow_le_pow_left₀ (by positivity) hN1_ge_AD 2
      have hcross : 0 ≤ 2 * ((K_unit : ℝ) * (A_nat : ℝ)) * ((K_unit : ℝ) * (D_nat : ℝ)) := by
        positivity
      have hexp_sq :
          ((K_unit : ℝ) * (A_nat : ℝ) + (K_unit : ℝ) * (D_nat : ℝ)) ^ 2 =
          ((K_unit : ℝ) * (A_nat : ℝ)) ^ 2 + ((K_unit : ℝ) * (D_nat : ℝ)) ^ 2 +
            2 * ((K_unit : ℝ) * (A_nat : ℝ)) * ((K_unit : ℝ) * (D_nat : ℝ)) := by ring
      linarith only [hA_sq, hD_sq, hp, hcross, hexp_sq]
    have hS_exp : (S_max : ℝ) ≤ (6 + 32 * C_deg ^ 2) * Real.exp (Real.sqrt X_m + L_S) := by
      have hexpLS : ((S + 6 : ℕ) : ℝ) = Real.exp L_S :=
        (Real.exp_log (by exact_mod_cast (show 0 < S + 6 by omega))).symm
      have hmaxS : ((max S 6 : ℕ) : ℝ) ≤ 6 * Real.exp (Real.sqrt X_m + L_S) := by
        have h1 : ((max S 6 : ℕ) : ℝ) ≤ ((S + 6 : ℕ) : ℝ) := by
          exact_mod_cast (show max S 6 ≤ S + 6 by omega)
        rw [hexpLS] at h1
        have h2 : Real.exp L_S ≤ Real.exp (Real.sqrt X_m + L_S) :=
          Real.exp_le_exp.mpr (le_add_of_nonneg_left (Real.sqrt_nonneg X_m))
        have h3 := h1.trans h2
        linarith [Real.exp_pos (Real.sqrt X_m + L_S)]
      have h2d2 : 2 * (d : ℝ) ^ 2 ≤ 32 * C_deg ^ 2 * Real.exp (Real.sqrt X_m + L_S) := by
        have hsqrt_exp : Real.sqrt X_m ≤ Real.exp (Real.sqrt X_m + L_S) :=
          (by linarith [Real.add_one_le_exp (Real.sqrt X_m)] :
              Real.sqrt X_m ≤ Real.exp (Real.sqrt X_m)).trans
            (Real.exp_le_exp.mpr (le_add_of_nonneg_right hLS_nn))
        calc 2 * (d : ℝ) ^ 2
            ≤ 32 * C_deg ^ 2 * Real.sqrt X_m := by linarith only [hd2_sqrt]
          _ ≤ 32 * C_deg ^ 2 * Real.exp (Real.sqrt X_m + L_S) :=
              mul_le_mul_of_nonneg_left hsqrt_exp (by positivity)
      have hcast_S : (S_max : ℝ) = ((max S 6 : ℕ) : ℝ) + 2 * (d : ℝ) ^ 2 := by
        dsimp only [S_max]; push_cast; ring
      rw [hcast_S]; linarith only [hmaxS, h2d2]
    exact hrouche_of_extra S_max N L_S hS_exp hN1_sq_AD

/-- **Optimal `Θ(√m)` Burnol-bracketed unit-window stabilization (`centeredTheta_sqrtPrefix_stabilization`).**
There exist an absolute prefix constant `C_unit ≥ 4`, Burnol good-height brackets
`y₁(m) ≤ m - 1 / 12` and `y₂(m) ≥ m + 2` (`y₂(m) - y₁(m) ≤ 5`), and enclosed `xi` root sets
`Z_xi(m)` covering `xiUnitWindowZeros (m : ℝ)` such that:
1. Boundary regularity and `r = 0` Rouché degree lock hold unconditionally at EVERY
   `N ≥ C_unit * (Nat.sqrt m + 1)` independently of the stage `n`.
2. At ANY single stage `n ≥ 6` with `n ≤ S_max ≤ 6 exp(√(m + 5)) + 2 d_m²` satisfying the
   `1 / (8 S_max³)` ellipse gap on `Z_xi(m)`, `centeredThetaCollisionOperator y₁(m) y₂(m) n N`
   stabilizes directly at `n` for ALL `N ≥ C_unit * (Nat.sqrt m + 1)` with zero stage shift.
3. For every `m : ℕ` and every target stage `S : ℕ` with `(S : ℝ) ≤ exp(√m)`, there exists an
   ellipse-avoiding stage `n_* ∈ [max S 6, max S 6 + 2 * d_m²]` stabilizing at `N ≥ C_unit * (Nat.sqrt m + 1)`.
4. Unrestricted-`S` stabilization: for EVERY `(m, S) : ℕ × ℕ` (with zero restriction on `S`),
   there exists `n_* ∈ [max S 6, max S 6 + 2 * d_m²]` stabilizing for ALL
   `N ≥ C_unit * (Nat.sqrt m + 1 + (⌈log(m + 5)⌉₊ + 1) * (⌈√(log(S + 6))⌉₊ + 1))`. -/
theorem centeredTheta_sqrtPrefix_stabilization :
    ∃ (C_unit : ℕ) (c_good : ℝ) (y₁ y₂ : ℕ → ℝ) (Z_xi : ℕ → Finset ℂ),
      4 ≤ C_unit ∧ 0 < c_good ∧ c_good ≤ 1 ∧
      (∀ m : ℕ,
        (-1 / 12 : ℝ) ≤ y₁ m ∧ y₁ m ≤ (m : ℝ) - 1 / 12 ∧
        (m : ℝ) + 2 ≤ y₂ m ∧ y₂ m ≤ (m : ℝ) + 3 ∧ y₂ m - y₁ m ≤ 5 ∧
        (∀ t : ℝ,
          c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) ≤
            ‖_root_.RHTower.xi (_root_.RHTower.rectangleBoundaryPath
              (centeredWindowLowerLeft (y₁ m)) (centeredWindowUpperRight (y₂ m)) t)‖) ∧
        (∀ w : ℂ, w ∈ Z_xi m ↔
          (0 < w.re ∧ w.re < 1 ∧ y₁ m < w.im ∧ w.im < y₂ m) ∧ _root_.RHTower.xi w = 0) ∧
        xiUnitWindowZeros (m : ℝ) ⊆ Z_xi m ∧
        (∀ w ∈ Z_xi m, 1 - star w ∈ Z_xi m) ∧
        ((∑ w ∈ Z_xi m, (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ≤
          (C_unit : ℝ) * Real.log ((m + 5 : ℕ) : ℝ) ∧
        -- 1. Unconditional boundary regularity & `r = 0` degree lock for ALL `N ≥ C_unit * (Nat.sqrt m + 1)`:
        (∀ N : ℕ, C_unit * (Nat.sqrt m + 1) ≤ N →
          thetaStripTailBound N ≤ (c_good / 2) * Real.exp (-((m + 3 : ℕ) : ℝ)) ∧
          (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
            (_root_.RHTower.rectangleBoundaryPath
              (centeredWindowLowerLeft (y₁ m)) (centeredWindowUpperRight (y₂ m)) t) ≠ 0) ∧
          centeredThetaWindowDegree (y₁ m) (y₂ m) N =
            ∑ w ∈ Z_xi m, (analyticOrderAt _root_.RHTower.xi w).toNat) ∧
        -- 2. Direct single-stage stabilization whenever `6 ≤ n ≤ S_max ≤ 6 exp(√(m+5)) + 2 d_m²` has `1/(8 S_max³)` gap:
        (∀ (n S_max : ℕ), 6 ≤ n → n ≤ S_max →
          (S_max : ℝ) ≤ 6 * Real.exp (Real.sqrt ((m + 5 : ℕ) : ℝ)) +
            2 * ((∑ w ∈ Z_xi m, (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ^ 2 →
          (∀ z ∈ Z_xi m, ∀ w ∈ Z_xi m,
            1 / (8 * (S_max : ℝ) ^ 3) ≤ |zhukovskyEllipseForm n (z - w) - 1|) →
          ∀ N : ℕ, C_unit * (Nat.sqrt m + 1) ≤ N →
            (∀ u : HTGeometry.UnitCircle, centeredThetaLaurentLoop (y₁ m) (y₂ m) n N u ≠ 0) ∧
            HTGeometry.fredholmIndex (centeredThetaCollisionOperator (y₁ m) (y₂ m) n N) =
              2 * ∑ z ∈ Z_xi m, ∑ w ∈ Z_xi m,
                ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
                  ((analyticOrderAt _root_.RHTower.xi w).toNat : ℤ) *
                  (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0)) ∧
        -- 3. Automatic `Θ(√m)` pigeonhole stage selection for ANY `S` with `(S : ℝ) ≤ exp(√m)`:
        (∀ S : ℕ, (S : ℝ) ≤ Real.exp (Real.sqrt (m : ℝ)) →
          ∃ n_star ∈ Finset.Icc (max S 6)
              (max S 6 + 2 * (∑ w ∈ Z_xi m, (analyticOrderAt _root_.RHTower.xi w).toNat) ^ 2),
            ∀ N : ℕ, C_unit * (Nat.sqrt m + 1) ≤ N →
              (∀ u : HTGeometry.UnitCircle,
                centeredThetaLaurentLoop (y₁ m) (y₂ m) n_star N u ≠ 0) ∧
              HTGeometry.fredholmIndex (centeredThetaCollisionOperator (y₁ m) (y₂ m) n_star N) =
                2 * ∑ z ∈ Z_xi m, ∑ w ∈ Z_xi m,
                  ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
                    ((analyticOrderAt _root_.RHTower.xi w).toNat : ℤ) *
                    (if zhukovskyEllipseForm n_star (z - w) < 1 then 1 else 0)) ∧
        -- 4. Unrestricted-`S` pigeonhole stage selection for EVERY `(m, S) : ℕ × ℕ`:
        (∀ S : ℕ,
          ∃ n_star ∈ Finset.Icc (max S 6)
              (max S 6 + 2 * (∑ w ∈ Z_xi m, (analyticOrderAt _root_.RHTower.xi w).toNat) ^ 2),
            ∀ N : ℕ,
              C_unit * (Nat.sqrt m + 1 +
                (Nat.ceil (Real.log ((m + 5 : ℕ) : ℝ)) + 1) *
                  (Nat.ceil (Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ))) + 1)) ≤ N →
              (∀ u : HTGeometry.UnitCircle,
                centeredThetaLaurentLoop (y₁ m) (y₂ m) n_star N u ≠ 0) ∧
              HTGeometry.fredholmIndex (centeredThetaCollisionOperator (y₁ m) (y₂ m) n_star N) =
                2 * ∑ z ∈ Z_xi m, ∑ w ∈ Z_xi m,
                  ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
                    ((analyticOrderAt _root_.RHTower.xi w).toNat : ℤ) *
                    (if zhukovskyEllipseForm n_star (z - w) < 1 then 1 else 0))) := by
  obtain ⟨c_good, Y₁, Y₂, Z_box_fn, C_deg, hc_good_pos, hc_good_le1, hC_d6, hgeom⟩ :=
    exists_burnol_unit_window_geometry
  obtain ⟨M_strip, hM1, hstrip⟩ := exists_strip_xi_and_deriv_bound
  obtain ⟨K_unit, hCu4, hCd_le, hunit_budget⟩ :=
    exists_centered_unit_prefix_constant hc_good_pos hC_d6 hM1
  refine ⟨K_unit, c_good, Y₁, Y₂, Z_box_fn, hCu4, hc_good_pos, hc_good_le1, fun m => ?_⟩
  obtain ⟨hy₁_lo, hy₁_hi, hy₂_lo, hy₂_hi, hspan5, hbdry_m, hZ_iff, hsub_unit, hrefl_Z, hd_Cd⟩ :=
    hgeom m
  set X_m : ℝ := ((m + 5 : ℕ) : ℝ)
  have hX1 : 1 ≤ X_m := by dsimp only [X_m]; exact_mod_cast (show 1 ≤ m + 5 by omega)
  have hlogX_nn : 0 ≤ Real.log X_m := Real.log_nonneg hX1
  have hd_Cu :
      ((∑ w ∈ Z_box_fn m, (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ≤
        (K_unit : ℝ) * Real.log X_m :=
    hd_Cd.trans (mul_le_mul_of_nonneg_right hCd_le hlogX_nn)
  set z₁ := centeredWindowLowerLeft (Y₁ m)
  set z₂ := centeredWindowUpperRight (Y₂ m)
  set c := centeredWindowMid (Y₁ m) (Y₂ m)
  set d : ℕ := ∑ w ∈ Z_box_fn m, (analyticOrderAt _root_.RHTower.xi w).toNat
  set μ : ℝ := c_good * Real.exp (-((m + 3 : ℕ) : ℝ))
  obtain ⟨hN_tail_half, hrouche_single, hrouche_unres⟩ := hunit_budget m d hd_Cd
  have hz₁_re : z₁.re = -1 / 2 := centeredWindowLowerLeft_re (Y₁ m)
  have hz₂_re : z₂.re = 3 / 2 := centeredWindowUpperRight_re (Y₂ m)
  have hz₁_im : z₁.im = Y₁ m := centeredWindowLowerLeft_im (Y₁ m)
  have hz₂_im : z₂.im = Y₂ m := centeredWindowUpperRight_im (Y₂ m)
  have him_le : z₁.im ≤ z₂.im := by rw [hz₁_im, hz₂_im]; linarith
  have hspan_im : z₂.im - z₁.im ≤ 5 := by rw [hz₁_im, hz₂_im]; exact hspan5
  have hμ_pos : 0 < μ := by dsimp only [μ]; positivity
  have hμ_le1 : μ ≤ 1 := by
    dsimp only [μ]
    calc c_good * Real.exp (-((m + 3 : ℕ) : ℝ))
        ≤ 1 * 1 := mul_le_mul hc_good_le1
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _)))
          (Real.exp_pos _).le zero_le_one
      _ = 1 := one_mul 1
  have hbox_rad : ∀ w : ℂ, -1 / 2 ≤ w.re → w.re ≤ 3 / 2 → Y₁ m ≤ w.im → w.im ≤ Y₂ m →
      ‖w - c‖ ≤ 4 := by
    intro w hx1 hx2 hy1 hy2
    have hre_diff : |(w - c).re| ≤ 1 := by
      have hc_re : c.re = 1 / 2 := by dsimp only [c, centeredWindowMid]; simp
      rw [Complex.sub_re, hc_re]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have him_diff : |(w - c).im| ≤ 5 / 2 := by
      have hc_im : c.im = (Y₁ m + Y₂ m) / 2 := by dsimp only [c, centeredWindowMid]; simp
      rw [Complex.sub_im, hc_im]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    linarith [Complex.norm_le_abs_re_add_abs_im (w - c)]
  have hR_bdry : ∀ t : ℝ, ‖_root_.RHTower.rectangleBoundaryPath z₁ z₂ t - c‖ ≤ 4 := by
    intro t
    have hrect := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm z₁ z₂
      (by linarith : z₁.re ≤ z₂.re) him_le t
    rw [uIcc_of_le (by linarith : z₁.re ≤ z₂.re), uIcc_of_le him_le,
      Complex.mem_reProdIm, hz₁_re, hz₂_re, hz₁_im, hz₂_im] at hrect
    exact hbox_rad _ hrect.1.1 hrect.1.2 hrect.2.1 hrect.2.2
  have hZ_rad : ∀ w ∈ Z_box_fn m, ‖w - c‖ ≤ 4 := by
    intro w hw
    obtain ⟨⟨hr0, hr1, hy1, hy2⟩, _⟩ := (hZ_iff w).mp hw
    exact hbox_rad w (by linarith) (by linarith) hy1.le hy2.le
  have hxi_nz_bdry : ∀ t : ℝ, _root_.RHTower.xi (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t) ≠ 0 := by
    intro t h0; have hb := hbdry_m t; rw [h0, norm_zero] at hb; linarith
  have hxi_moments : ∀ r : ℕ,
      (2 * Real.pi * I)⁻¹ *
        _root_.RHTower.rectIntegral (fun z => (z - c) ^ r * logDeriv _root_.RHTower.xi z) z₁ z₂ =
      ∑ w ∈ Z_box_fn m, ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * (w - c) ^ r := by
    intro r
    obtain ⟨Z_box, hZ_box_mem, hrect_sum⟩ := entire_rectIntegral_mul_logDeriv_eq_sum
      (_root_.RHTower.xi_analyticOnNhd Set.univ) _root_.RHTower.xi_orderAt_ne_top
      (g := fun z => (z - c) ^ r) (fun _ _ => (analyticAt_id.sub analyticAt_const).pow r)
      (by linarith : z₁.re ≤ z₂.re) him_le hxi_nz_bdry
    have hZ_eq : Z_box = Z_box_fn m := by
      ext w
      rw [hZ_box_mem, hZ_iff, hz₁_re, hz₂_re, hz₁_im, hz₂_im]
      constructor
      · rintro ⟨⟨_, _, hy1, hy2⟩, hw0⟩
        obtain ⟨hr0, hr1⟩ := _root_.RHTower.xi_zero_re_mem_open_unit hw0
        exact ⟨⟨hr0, hr1, hy1, hy2⟩, hw0⟩
      · rintro ⟨⟨hr0, hr1, hy1, hy2⟩, hw0⟩
        exact ⟨⟨by linarith, by linarith, hy1, hy2⟩, hw0⟩
    rwa [hZ_eq] at hrect_sum
  have hclause_bdry : ∀ N : ℕ, K_unit * (Nat.sqrt m + 1) ≤ N →
      thetaStripTailBound N ≤ (c_good / 2) * Real.exp (-((m + 3 : ℕ) : ℝ)) ∧
      (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
        (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t) ≠ 0) ∧
      centeredThetaWindowDegree (Y₁ m) (Y₂ m) N = d := by
    intro N hN
    have htail := (hN_tail_half N hN).1
    obtain ⟨hamp_nz, hr0_raw, _⟩ := rectIntegral_shifted_powerSum_perturbation
      hz₁_re hz₂_re him_le hμ_pos hμ_le1 (by norm_num : (1 : ℝ) ≤ 4) (by norm_num : (1 : ℝ) ≤ 5)
      hM1 hspan_im hstrip hbdry_m hR_bdry htail
    have hs0_eq : centeredThetaWindowPowerSum (Y₁ m) (Y₂ m) N 0 = (d : ℂ) := by
      unfold centeredThetaWindowPowerSum
      simp only [pow_zero, one_mul]
      have hxi0 := hxi_moments 0
      simp only [pow_zero, mul_one, one_mul] at hxi0
      rw [show centeredWindowLowerLeft (Y₁ m) = z₁ from rfl,
          show centeredWindowUpperRight (Y₂ m) = z₂ from rfl,
          hr0_raw, hxi0, Nat.cast_sum]
    have hdeg : centeredThetaWindowDegree (Y₁ m) (Y₂ m) N = d := by
      unfold centeredThetaWindowDegree
      rw [hs0_eq, Complex.natCast_re]
      exact (Nat.floor_eq_iff (Nat.cast_nonneg d)).mpr ⟨le_rfl, by linarith⟩
    exact ⟨htail.trans_eq (by ring), hamp_nz, hdeg⟩
  have hcore_of_rouche : ∀ (n S_max N : ℕ),
      6 ≤ n → n ≤ S_max →
      (∀ z ∈ Z_box_fn m, ∀ w ∈ Z_box_fn m,
        1 / (8 * (S_max : ℝ) ^ 3) ≤ |zhukovskyEllipseForm n (z - w) - 1|) →
      K_unit * (Nat.sqrt m + 1) ≤ N →
      4 * ((4 * (2 * M_strip + 1) * 5 / μ ^ 2) * thetaStripTailBound N) *
        (((d + 1 : ℕ) : ℝ) ^ 4) * (896 * (4 : ℝ) * (S_max : ℝ) ^ 4) ^ (d ^ 2) < 1 →
      (∀ u : HTGeometry.UnitCircle, centeredThetaLaurentLoop (Y₁ m) (Y₂ m) n N u ≠ 0) ∧
      HTGeometry.fredholmIndex (centeredThetaCollisionOperator (Y₁ m) (Y₂ m) n N) =
        2 * ∑ z ∈ Z_box_fn m, ∑ w ∈ Z_box_fn m,
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
            ((analyticOrderAt _root_.RHTower.xi w).toNat : ℤ) *
            (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0) := by
    intro n S_max N hn6 hnS havoid hN_base hN_rouche
    obtain ⟨_, _, _, hPN_nz, hPN_wind⟩ :=
      pairDiffPoly_rouche_stabilization_core hz₁_re hz₂_re him_le
        hμ_pos hμ_le1 (by norm_num : (1 : ℝ) ≤ 4) (by norm_num : (1 : ℝ) ≤ 5) hM1
        hspan_im hstrip hbdry_m hR_bdry hZ_rad hxi_moments hn6 hnS havoid
        (hN_tail_half N hN_base).1 (hN_tail_half N hN_base).2 hN_rouche
    have hsN_eq : (fun r : ℕ =>
        (2 * Real.pi * I)⁻¹ *
          _root_.RHTower.rectIntegral
            (fun z => (z - c) ^ r *
              (-_root_.RHTower.finiteThetaFirstMoment N z /
                _root_.RHTower.finiteThetaAmplitude N z)) z₁ z₂) =
        centeredThetaWindowPowerSum (Y₁ m) (Y₂ m) N := rfl
    have hdeg_eq : centeredThetaWindowDegree (Y₁ m) (Y₂ m) N = d := (hclause_bdry N hN_base).2.2
    have hpoly_eq : centeredThetaDifferencePoly (Y₁ m) (Y₂ m) N =
        pairDiffPoly d (centeredThetaWindowPowerSum (Y₁ m) (Y₂ m) N) := by
      unfold centeredThetaDifferencePoly; rw [hdeg_eq]
    rw [hsN_eq, ← hpoly_eq] at hPN_nz hPN_wind
    have hloop_nz : ∀ u : HTGeometry.UnitCircle,
        centeredThetaLaurentLoop (Y₁ m) (Y₂ m) n N u ≠ 0 := by
      intro u
      simpa only [centeredThetaLaurentLoop, polyZhukovskyLaurentLoop_apply] using hPN_nz u
    have hind_eq :
        HTGeometry.fredholmIndex (centeredThetaCollisionOperator (Y₁ m) (Y₂ m) n N) =
          _root_.RHTower.windingNumber
            (fun θ => ((centeredThetaDifferencePoly (Y₁ m) (Y₂ m) N).eval
              (zhukovskyLoop n (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) := by
      unfold centeredThetaCollisionOperator centeredThetaCollisionSymbol
      rw [fredholmIndex_wienerHopfLift_unitNormalizeSymbol,
        circleWinding_unitNormalizeSymbol_of_ne_zero hloop_nz]
      rfl
    exact ⟨hloop_nz, hind_eq.trans hPN_wind⟩
  have hclause_single : ∀ (n S_max : ℕ), 6 ≤ n → n ≤ S_max →
      (S_max : ℝ) ≤ 6 * Real.exp (Real.sqrt X_m) + 2 * (d : ℝ) ^ 2 →
      (∀ z ∈ Z_box_fn m, ∀ w ∈ Z_box_fn m,
        1 / (8 * (S_max : ℝ) ^ 3) ≤ |zhukovskyEllipseForm n (z - w) - 1|) →
      ∀ N : ℕ, K_unit * (Nat.sqrt m + 1) ≤ N →
        (∀ u : HTGeometry.UnitCircle, centeredThetaLaurentLoop (Y₁ m) (Y₂ m) n N u ≠ 0) ∧
        HTGeometry.fredholmIndex (centeredThetaCollisionOperator (Y₁ m) (Y₂ m) n N) =
          2 * ∑ z ∈ Z_box_fn m, ∑ w ∈ Z_box_fn m,
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
              ((analyticOrderAt _root_.RHTower.xi w).toNat : ℤ) *
              (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0) :=
    fun n S_max hn6 hnS hS_hi havoid N hN =>
      hcore_of_rouche n S_max N hn6 hnS havoid hN (hrouche_single S_max N hS_hi hN)
  have hpigeon : ∀ S : ℕ,
      ∃ n_star ∈ Finset.Icc (max S 6) (max S 6 + 2 * d ^ 2),
        6 ≤ n_star ∧
        (∀ z ∈ Z_box_fn m, ∀ w ∈ Z_box_fn m,
          1 / (8 * ((max S 6 + 2 * d ^ 2 : ℕ) : ℝ) ^ 3) ≤
            |zhukovskyEllipseForm n_star (z - w) - 1|) := by
    intro S
    let P_diff : Finset ℂ := (Z_box_fn m ×ˢ Z_box_fn m).image fun p => p.1 - p.2
    have hP_card : P_diff.card ≤ d ^ 2 := by
      have hcard_Z : (Z_box_fn m).card ≤ d := by
        have h1 : ∀ w ∈ Z_box_fn m, 1 ≤ (analyticOrderAt _root_.RHTower.xi w).toNat := by
          intro w hw
          have hw0 := ((hZ_iff w).mp hw).2
          have hne0 : analyticOrderAt _root_.RHTower.xi w ≠ 0 := by
            intro h0
            rcases analyticOrderAt_eq_zero.mp h0 with hnot | hnz
            · exact hnot (_root_.RHTower.xi_analyticOnNhd Set.univ w (Set.mem_univ w))
            · exact hnz hw0
          have hcoe := ENat.coe_toNat (_root_.RHTower.xi_orderAt_ne_top w)
          by_contra hlt
          have hz : (analyticOrderAt _root_.RHTower.xi w).toNat = 0 := by omega
          rw [hz, ENat.coe_zero] at hcoe
          exact hne0 hcoe.symm
        calc (Z_box_fn m).card = ∑ _w ∈ Z_box_fn m, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ ∑ w ∈ Z_box_fn m, (analyticOrderAt _root_.RHTower.xi w).toNat := Finset.sum_le_sum h1
          _ = d := rfl
      calc P_diff.card ≤ (Z_box_fn m ×ˢ Z_box_fn m).card := Finset.card_image_le
        _ = (Z_box_fn m).card ^ 2 := by rw [Finset.card_product, sq]
        _ ≤ d ^ 2 := Nat.pow_le_pow_left hcard_Z 2
    obtain ⟨n_star, hn_Icc_P, havoid_P⟩ := exists_natStage_avoiding_zhukovsky_ellipses S P_diff
    set S_max : ℕ := max S 6 + 2 * d ^ 2
    have hn_Icc : n_star ∈ Finset.Icc (max S 6) S_max := by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn_Icc_P
      exact Finset.mem_Icc.mpr ⟨h1, h2.trans (by dsimp only [S_max]; omega)⟩
    have hn6 : 6 ≤ n_star := (le_max_right S 6).trans (Finset.mem_Icc.mp hn_Icc).1
    refine ⟨n_star, hn_Icc, hn6, fun z hz w hw => ?_⟩
    have hmem : z - w ∈ P_diff :=
      Finset.mem_image.mpr ⟨(z, w), Finset.mem_product.mpr ⟨hz, hw⟩, rfl⟩
    have hP_le_S : ((max S 6 + 2 * P_diff.card : ℕ) : ℝ) ≤ (S_max : ℝ) := by
      exact_mod_cast (show max S 6 + 2 * P_diff.card ≤ S_max by dsimp only [S_max]; omega)
    have hstep : 1 / (8 * (S_max : ℝ) ^ 3) ≤
        1 / (8 * ((max S 6 + 2 * P_diff.card : ℕ) : ℝ) ^ 3) := by
      have hp : (0 : ℝ) < ((max S 6 + 2 * P_diff.card : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < max S 6 + 2 * P_diff.card by omega)
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le hP_le_S 3) (by norm_num))
    exact hstep.trans (havoid_P (z - w) hmem)
  refine ⟨hy₁_lo, hy₁_hi, hy₂_lo, hy₂_hi, hspan5, hbdry_m, hZ_iff, hsub_unit, hrefl_Z,
    hd_Cu, hclause_bdry, hclause_single, ?_, ?_⟩
  · intro S hS_exp
    obtain ⟨n_star, hn_Icc, hn6, havoid⟩ := hpigeon S
    set S_max : ℕ := max S 6 + 2 * d ^ 2
    obtain ⟨_, hn_hi⟩ := Finset.mem_Icc.mp hn_Icc
    have hS_max_hi : (S_max : ℝ) ≤ 6 * Real.exp (Real.sqrt X_m) + 2 * (d : ℝ) ^ 2 := by
      have hexp_mono : Real.exp (Real.sqrt (m : ℝ)) ≤ Real.exp (Real.sqrt X_m) :=
        Real.exp_le_exp.mpr (Real.sqrt_le_sqrt (by
          dsimp only [X_m]; exact_mod_cast (show m ≤ m + 5 by omega)))
      have hexp1 : 1 ≤ Real.exp (Real.sqrt X_m) := Real.one_le_exp (Real.sqrt_nonneg X_m)
      have hmax6 : ((max S 6 : ℕ) : ℝ) ≤ 6 * Real.exp (Real.sqrt X_m) := by
        rw [Nat.cast_max, Nat.cast_ofNat]
        exact max_le (by linarith [Real.exp_pos (Real.sqrt X_m)]) (by linarith)
      have hcast_S : (S_max : ℝ) = ((max S 6 : ℕ) : ℝ) + 2 * (d : ℝ) ^ 2 := by
        dsimp only [S_max]; push_cast; ring
      rw [hcast_S]; linarith only [hmax6]
    exact ⟨n_star, hn_Icc, hclause_single n_star S_max hn6 hn_hi hS_max_hi havoid⟩
  · intro S
    obtain ⟨n_star, hn_Icc, hn6, havoid⟩ := hpigeon S
    set S_max : ℕ := max S 6 + 2 * d ^ 2
    obtain ⟨_, hn_hi⟩ := Finset.mem_Icc.mp hn_Icc
    refine ⟨n_star, hn_Icc, fun N hN => ?_⟩
    have hN_A : K_unit * (Nat.sqrt m + 1) ≤ N :=
      (Nat.mul_le_mul_left K_unit (Nat.le_add_right _ _)).trans hN
    exact hcore_of_rouche n_star S_max N hn6 hn_hi havoid hN_A (hrouche_unres S N hN)

end GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.exists_natStage_avoiding_zhukovsky_ellipses
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.norm_pairDiffPoly_eval_sub_le_on_zhukovsky
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.integerThetaCollisionOperator_polynomial_stabilization
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.centeredThetaDifferencePoly_real_and_loop_symmetric
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.centeredTheta_szego_positivity_tfae
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.centeredTheta_sqrtPrefix_stabilization

