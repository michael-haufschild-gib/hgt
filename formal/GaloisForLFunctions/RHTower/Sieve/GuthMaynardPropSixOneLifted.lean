import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumMiddleBlock
import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumRestrictedRange

/-!
# Heath-Brown over a lifted range `(A^k, B^k]`

Guth–Maynard's (6.2) raises a Dirichlet polynomial supported on `(A, B]` to its `k`-th power, whose
support is `(A^k, B^k]` — a range of ratio `(B/A)^k`, not a single dyadic block.  This module
covers such a range by `m` dyadic blocks `(2^i P, 2^{i+1} P]`, pays one Cauchy–Schwarz factor per
split (the corpus `hbPairSum_union_le`), and applies the corpus all-lengths Heath-Brown bound
`hbPairSum_Ioc_le_anyBlock` to each block.  The result is Guth–Maynard's (6.3) carrying the fourth
term of the all-lengths bound:

`Σ_{t₁,t₂∈W} |Σ_{P<u≤2^m P} a_u u^{i(t₁−t₂)}|² ≤
    8^m C (W² P + W P² + W^{5/4} T^{1/2} P + W^{3/2} P²)`.
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset

noncomputable section

theorem hbPairSum_emptySupport (W : Finset ℝ) (a : ℕ → ℂ) :
    hbPairSum W (∅ : Finset ℕ) a = 0 := by
  unfold hbPairSum hbPoly
  simp

/-- Consecutive half-open integer ranges are disjoint. -/
theorem Ioc_disjoint_Ioc_succ (A B C : ℕ) :
    Disjoint (Finset.Ioc A B) (Finset.Ioc B C) := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  rw [Finset.mem_Ioc] at hn hn'
  omega

/-- **The dyadic cover of `(P, 2^m P]`.**  Splitting off one block at a time costs `2^m`. -/
theorem hbPairSum_Ioc_two_pow_le (W : Finset ℝ) (a : ℕ → ℂ) (P : ℕ) :
    ∀ m : ℕ, hbPairSum W (Finset.Ioc P (2 ^ m * P)) a ≤
      2 ^ m * ∑ i ∈ Finset.range m, hbPairSum W (Finset.Ioc (2 ^ i * P) (2 * (2 ^ i * P))) a := by
  intro m
  induction m with
  | zero => simp [hbPairSum_emptySupport]
  | succ m ih =>
      have hPle : P ≤ 2 ^ m * P := Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) m)
      have hstep : 2 ^ m * P ≤ 2 * (2 ^ m * P) := Nat.le_mul_of_pos_left _ (by norm_num)
      have hunion : Finset.Ioc P (2 ^ m * P) ∪ Finset.Ioc (2 ^ m * P) (2 * (2 ^ m * P)) =
          Finset.Ioc P (2 * (2 ^ m * P)) := Finset.Ioc_union_Ioc_eq_Ioc hPle hstep
      have hgoal : Finset.Ioc P (2 ^ (m + 1) * P) = Finset.Ioc P (2 * (2 ^ m * P)) := by
        congr 1
        ring
      have hsplit := hbPairSum_union_le W (Ioc_disjoint_Ioc_succ P (2 ^ m * P) (2 * (2 ^ m * P))) a
      rw [hunion] at hsplit
      have hnn : 0 ≤ hbPairSum W (Finset.Ioc (2 ^ m * P) (2 * (2 ^ m * P))) a :=
        hbPairSum_nonneg _ _ _
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range m,
          hbPairSum W (Finset.Ioc (2 ^ i * P) (2 * (2 ^ i * P))) a :=
        Finset.sum_nonneg fun i _ => hbPairSum_nonneg _ _ _
      have h2m : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      rw [hgoal, Finset.sum_range_succ]
      have hpow : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
      rw [hpow]
      nlinarith

/-- `hbBlockConst` is monotone in its block-length parameter. -/
theorem hbBlockConst_mono {T δ : ℝ} (hδ : 0 < δ) {L L' : ℕ} (hT : 1 ≤ T) (hLL' : L ≤ L') :
    hbBlockConst T δ L ≤ hbBlockConst T δ L' := by
  have hc := one_le_hbReflFactor (T := T) hT
  have hK := hbDualFactor_nonneg T
  have hC0 : (0 : ℝ) < divisorBoundConst δ := divisorBoundConst_pos hδ
  have hmono : ((8 * L : ℕ) : ℝ) ^ δ ≤ ((8 * L' : ℕ) : ℝ) ^ δ := by
    refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hδ.le
    exact_mod_cast Nat.mul_le_mul_left 8 hLL'
  have hpow : (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 ≤
      (divisorBoundConst δ * ((8 * L' : ℕ) : ℝ) ^ δ) ^ 10 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 10
    exact mul_le_mul_of_nonneg_left hmono hC0.le
  unfold hbBlockConst
  have hfac : (0 : ℝ) ≤ hbReflFactor T + hbDualFactor T + 1 := by linarith
  nlinarith

theorem sum_geom_two_le (m : ℕ) : ∑ i ∈ Finset.range m, (2 : ℝ) ^ i ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have : (2 : ℝ) ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      rw [this]
      linarith

theorem sum_geom_four_le (m : ℕ) : ∑ i ∈ Finset.range m, (4 : ℝ) ^ i ≤ 4 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have h0 : (0 : ℝ) ≤ 4 ^ m := by positivity
      have : (4 : ℝ) ^ (m + 1) = 4 ^ m + 3 * 4 ^ m := by ring
      rw [this]
      linarith

theorem two_pow_le_four_pow (m : ℕ) : (2 : ℝ) ^ m ≤ 4 ^ m :=
  pow_le_pow_left₀ (by norm_num) (by norm_num) m

/-- **Heath-Brown on a dyadic cover of `(P, 2^m P]`.**  The all-lengths bound on each block,
summed; the constant is the all-lengths constant of the top block times `8^m`. -/
theorem hbPairSum_Ioc_two_pow_le_majorant {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {δ : ℝ} (hδ : 0 < δ)
    {P : ℕ} (hP : 1 ≤ P) (m : ℕ) {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc P (2 ^ m * P)) a ≤
      8 ^ m * (hbSmallConst T δ + hbBlockConst T δ ((2 ^ m * P) ^ 2)) *
        ((W.card : ℝ) ^ 2 * P + (W.card : ℝ) * (P : ℝ) ^ 2
          + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * P
          + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (P : ℝ) ^ 2) := by
  classical
  set Cm : ℝ := hbSmallConst T δ + hbBlockConst T δ ((2 ^ m * P) ^ 2) with hCm
  have hS0 : 0 ≤ hbSmallConst T δ := le_trans zero_le_one (one_le_hbSmallConst hT hδ)
  have hCm0 : 0 ≤ Cm := by
    have := hbBlockConst_nonneg (T := T) (δ := δ) hT ((2 ^ m * P) ^ 2)
    rw [hCm]; linarith
  set A : ℝ := (W.card : ℝ) ^ 2 * (P : ℝ) with hAdef
  set B : ℝ := (W.card : ℝ) * (P : ℝ) ^ 2 with hBdef
  set C : ℝ := (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (P : ℝ) with hCdef
  set D : ℝ := (W.card : ℝ) ^ ((3 : ℝ) / 2) * (P : ℝ) ^ 2 with hDdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hC0 : 0 ≤ C := by
    have h1 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((5 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    have h2 : (0 : ℝ) ≤ T ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    rw [hCdef]; positivity
  have hD0 : 0 ≤ D := by
    have h1 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
    rw [hDdef]; positivity
  -- each block, with the top constant
  have hblock : ∀ i ∈ Finset.range m,
      hbPairSum W (Finset.Ioc (2 ^ i * P) (2 * (2 ^ i * P))) a ≤
        Cm * (A * 2 ^ i + B * 4 ^ i + C * 2 ^ i + D * 4 ^ i) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hLi : 1 ≤ 2 ^ i * P := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hmono : (2 ^ i * P) ^ 2 ≤ (2 ^ m * P) ^ 2 := by
      have : (2 : ℕ) ^ i * P ≤ 2 ^ m * P :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hi'.le)
      exact Nat.pow_le_pow_left this 2
    have hany := hbPairSum_Ioc_le_anyBlock hW hT hdiam hLi hδ (fun n _ => ha n)
    have hconst : hbSmallConst T δ + hbBlockConst T δ ((2 ^ i * P) ^ 2) ≤ Cm := by
      have := hbBlockConst_mono (T := T) (δ := δ) hδ hT hmono
      rw [hCm]; linarith
    have hcast : ((2 ^ i * P : ℕ) : ℝ) = 2 ^ i * (P : ℝ) := by push_cast; ring
    have h4 : ((2 : ℝ) ^ i) ^ 2 = (4 : ℝ) ^ i := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hmaj : (W.card : ℝ) ^ 2 * ((2 ^ i * P : ℕ) : ℝ)
          + (W.card : ℝ) * ((2 ^ i * P : ℕ) : ℝ) ^ 2
          + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((2 ^ i * P : ℕ) : ℝ)
          + (W.card : ℝ) ^ ((3 : ℝ) / 2) * ((2 ^ i * P : ℕ) : ℝ) ^ 2
        = A * 2 ^ i + B * 4 ^ i + C * 2 ^ i + D * 4 ^ i := by
      rw [hcast, hAdef, hBdef, hCdef, hDdef, mul_pow, h4]
      ring
    rw [hmaj] at hany
    refine hany.trans (mul_le_mul_of_nonneg_right hconst ?_)
    have h2i : (0 : ℝ) ≤ (2 : ℝ) ^ i := by positivity
    have h4i : (0 : ℝ) ≤ (4 : ℝ) ^ i := by positivity
    positivity
  -- sum the blocks
  have hterms : ∑ i ∈ Finset.range m,
      hbPairSum W (Finset.Ioc (2 ^ i * P) (2 * (2 ^ i * P))) a ≤
      Cm * 4 ^ m * (A + B + C + D) := by
    have h2 := sum_geom_two_le m
    have h4 := sum_geom_four_le m
    have h24 := two_pow_le_four_pow m
    calc ∑ i ∈ Finset.range m, hbPairSum W (Finset.Ioc (2 ^ i * P) (2 * (2 ^ i * P))) a
        ≤ ∑ i ∈ Finset.range m, Cm * (A * 2 ^ i + B * 4 ^ i + C * 2 ^ i + D * 4 ^ i) :=
          Finset.sum_le_sum hblock
      _ = Cm * ((A + C) * (∑ i ∈ Finset.range m, (2 : ℝ) ^ i)
            + (B + D) * (∑ i ∈ Finset.range m, (4 : ℝ) ^ i)) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ Cm * ((A + C) * 4 ^ m + (B + D) * 4 ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_ hCm0
          have hAC : 0 ≤ A + C := by linarith
          have hBD : 0 ≤ B + D := by linarith
          have e1 : (A + C) * (∑ i ∈ Finset.range m, (2 : ℝ) ^ i) ≤ (A + C) * 4 ^ m :=
            mul_le_mul_of_nonneg_left (h2.trans h24) hAC
          have e2 : (B + D) * (∑ i ∈ Finset.range m, (4 : ℝ) ^ i) ≤ (B + D) * 4 ^ m :=
            mul_le_mul_of_nonneg_left h4 hBD
          linarith
      _ = Cm * 4 ^ m * (A + B + C + D) := by ring
  have h8 : (8 : ℝ) ^ m = 2 ^ m * 4 ^ m := by rw [← mul_pow]; norm_num
  have h2m0 : (0 : ℝ) ≤ (2 : ℝ) ^ m := by positivity
  calc hbPairSum W (Finset.Ioc P (2 ^ m * P)) a
      ≤ 2 ^ m * ∑ i ∈ Finset.range m,
          hbPairSum W (Finset.Ioc (2 ^ i * P) (2 * (2 ^ i * P))) a :=
        hbPairSum_Ioc_two_pow_le W a P m
    _ ≤ 2 ^ m * (Cm * 4 ^ m * (A + B + C + D)) :=
        mul_le_mul_of_nonneg_left hterms h2m0
    _ = _ := by rw [h8]; ring

end

end RHTower.Sieve
