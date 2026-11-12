import GaloisForLFunctions.LogarithmicChowla.ArcMass

/-!
# Dilated windows have small logarithmic mean square

* (A1) `limAvg_le_of_dyadic`: if `0 ≤ G ≤ B` and `Σ_{X ≤ k < 2X} G(k) ≤ cX` for `X ≥ X₀`, then
  `L(G) ≤ 3c`: the logarithmic sum over `[1, X₀2^J]` is at most `BX₀ + 2cJ`.
* (A2) `exists_limAvg_dilWin_le`: for `|f| ≤ 1` with the dyadic short-window mean-square bound
  (`DyadicMR`) and `D ≥ 1`, the windows `Σ_{n ≤ Dm < n+T} f(m)` (`dilWin`) satisfy
  `L(|T^{-1} dilWin|²) → 0` as `T → ∞`.  The index set is `(A − 1, A − 1 + h]`, `A = ⌈n/D⌉`,
  `h = ⌊T/D⌋`, up to one endpoint (`norm_dilWin_sub_winSum_le`); `n ↦ A − 1` is at most `D`-to-one and
  maps `[X, 2X)` into `[Y, 2Y + 1]`, `Y = ⌈X/D⌉ − 1` (`sum_comp_ceilDiv_le`).
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Filter Topology

noncomputable section
set_option autoImplicit false

variable {U : Ultrafilter ℝ}

/-- `Σ_{k < m ≤ k + h} f(m)`. -/
def winSum (f : ℕ → ℂ) (k h : ℕ) : ℂ := ∑ m ∈ Ioc k (k + h), f m

/-- The dyadic short-window mean-square bound for `f`. -/
def DyadicMR (f : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    ∑ k ∈ range X, ‖winSum f (X + k) h‖ ^ 2 ≤ ε * (h : ℝ) ^ 2 * X

/-- `Σ_{n ≤ D m < n + T} f(m)`. -/
def dilWin (f : ℕ → ℂ) (D n T : ℕ) : ℂ :=
  ∑ m ∈ (range (n + T)).filter (fun m => n ≤ D * m ∧ D * m < n + T), f m

theorem norm_winSum_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (k h : ℕ) : ‖winSum f k h‖ ≤ h := by
  calc ‖winSum f k h‖ ≤ ∑ m ∈ Ioc k (k + h), ‖f m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Ioc k (k + h), (1 : ℝ) := sum_le_sum fun m _ => hf m
    _ = h := by simp

theorem logSum_mono_length {G : ℕ → ℝ} (hG0 : ∀ n, 0 ≤ G n) {N M : ℕ} (hNM : N ≤ M) :
    logSum G N ≤ logSum G M :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hNM) fun n _ _ => by
    have := hG0 (n + 1); positivity

/-- The logarithmic sum up to `X₀ 2^J`. -/
theorem logSum_dyadic_le {G : ℕ → ℝ} (hG0 : ∀ n, 0 ≤ G n) {B : ℝ} (hGB : ∀ n, G n ≤ B)
    {c : ℝ} (hc : 0 ≤ c) {X₀ : ℕ} (hX₀ : 1 ≤ X₀)
    (hdy : ∀ X, X₀ ≤ X → ∑ k ∈ range X, G (X + k) ≤ c * X) (J : ℕ) :
    logSum G (X₀ * 2 ^ J) ≤ B * X₀ + 2 * c * J := by
  induction J with
  | zero =>
    simp only [pow_zero, mul_one, Nat.cast_zero, mul_zero, add_zero]
    calc logSum G X₀ = ∑ n ∈ range X₀, G (n + 1) / ((n : ℝ) + 1) := rfl
      _ ≤ ∑ _n ∈ range X₀, B := sum_le_sum fun n _ => by
          have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
          rw [div_le_iff₀ (by linarith)]
          have h1 := hGB (n + 1)
          have h2 := hG0 (n + 1)
          nlinarith
      _ = B * X₀ := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]
  | succ J ih =>
    set Y := X₀ * 2 ^ J with hY
    have hY1 : 1 ≤ Y := Nat.mul_pos (by omega) (by positivity)
    have hYX : X₀ ≤ Y := Nat.le_mul_of_pos_right _ (by positivity)
    have e : X₀ * 2 ^ (J + 1) = Y + Y := by rw [hY, pow_succ]; ring
    have hsplit : logSum G (Y + Y) = logSum G Y
        + ∑ k ∈ range Y, G (Y + k + 1) / (((Y + k : ℕ) : ℝ) + 1) := by
      rw [logSum, sum_range_add]; rfl
    rw [e, hsplit]
    have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY1
    -- the dyadic block `[Y + 1, 2Y]`
    have hblock : ∑ k ∈ range Y, G (Y + k + 1) / (((Y + k : ℕ) : ℝ) + 1) ≤ 2 * c := by
      have h1 : ∑ k ∈ range Y, G (Y + k + 1) / (((Y + k : ℕ) : ℝ) + 1)
          ≤ ∑ k ∈ range Y, G (Y + k + 1) / Y :=
        sum_le_sum fun k _ => div_le_div_of_nonneg_left (hG0 _) hY0 (by push_cast; linarith)
      have h2 : ∑ k ∈ range Y, G (Y + k + 1) ≤ ∑ k ∈ range (Y + 1), G ((Y + 1) + k) := by
        rw [sum_range_succ]
        have : ∑ k ∈ range Y, G (Y + k + 1) = ∑ k ∈ range Y, G ((Y + 1) + k) :=
          sum_congr rfl fun k _ => by congr 1; omega
        rw [this]
        linarith [hG0 (Y + 1 + Y)]
      have h3 := hdy (Y + 1) (by omega)
      have h4 : ∑ k ∈ range Y, G (Y + k + 1) / Y = (∑ k ∈ range Y, G (Y + k + 1)) / Y := by
        rw [sum_div]
      rw [h4] at h1
      have h5 : (∑ k ∈ range Y, G (Y + k + 1)) / Y ≤ c * ((Y + 1 : ℕ) : ℝ) / Y :=
        div_le_div_of_nonneg_right (le_trans h2 h3) hY0.le
      have h6 : c * ((Y + 1 : ℕ) : ℝ) / Y ≤ 2 * c := by
        rw [div_le_iff₀ hY0]; push_cast
        have : (1 : ℝ) ≤ Y := by exact_mod_cast hY1
        nlinarith
      linarith
    rw [Nat.cast_succ]
    linarith

/-- **(A1) Dyadic control gives logarithmic-average control.** -/
theorem limAvg_le_of_dyadic (hU : (U : Filter ℝ) ≤ atTop) {G : ℕ → ℝ} (hG0 : ∀ n, 0 ≤ G n)
    {B : ℝ} (hGB : ∀ n, G n ≤ B) {c : ℝ} (hc : 0 ≤ c) {X₀ : ℕ} (hX₀ : 1 ≤ X₀)
    (hdy : ∀ X, X₀ ≤ X → ∑ k ∈ range X, G (X + k) ≤ c * X) :
    limAvg U G ≤ 3 * c := by
  have hB0 : 0 ≤ B := le_trans (hG0 0) (hGB 0)
  have hb : Bdd G := ⟨B, fun n => abs_le.mpr ⟨by linarith [hG0 n], hGB n⟩⟩
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  refine le_of_tendsto (tendsto_limAvg hU hb) (hU ?_)
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  filter_upwards [eventually_ge_atTop (Real.exp ((B * X₀ + 2 * c) / δ + 1)),
    eventually_ge_atTop (2 : ℝ)] with x hx hx2
  have hx0 : 0 < x := by linarith
  have hlogx : (B * X₀ + 2 * c) / δ + 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hlogx0 : 0 < Real.log x := by
    have : 0 ≤ (B * X₀ + 2 * c) / δ := by positivity
    linarith
  set N := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  set J := Nat.log 2 N + 1 with hJ
  have hNJ : N ≤ X₀ * 2 ^ J := by
    have h1 : N < 2 ^ J := Nat.lt_pow_succ_log_self (by norm_num) N
    have h2 : 2 ^ J ≤ X₀ * 2 ^ J := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hT := le_trans (logSum_mono_length hG0 hNJ) (logSum_dyadic_le hG0 hGB hc hX₀ hdy J)
  -- `J ≤ log x / log 2 + 1`
  have hJlog : (J : ℝ) ≤ Real.log x / Real.log 2 + 1 := by
    have h1 : (2 : ℝ) ^ (Nat.log 2 N) ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h2 : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log x := by
      have := Real.log_le_log (by positivity) (le_trans h1 hNx)
      rwa [Real.log_pow] at this
    have h3 : (Nat.log 2 N : ℝ) ≤ Real.log x / Real.log 2 := by
      rw [le_div_iff₀ (by linarith)]; exact h2
    rw [hJ]; push_cast; linarith
  have hJ3 : 2 * c * (J : ℝ) ≤ 3 * c * Real.log x + 2 * c := by
    have h1 : Real.log x / Real.log 2 ≤ 3 / 2 * Real.log x := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have : (J : ℝ) ≤ 3 / 2 * Real.log x + 1 := by linarith
    nlinarith
  rw [logAvg, div_le_iff₀ hlogx0]
  have hδlog : B * X₀ + 2 * c ≤ δ * Real.log x := by
    have : (B * X₀ + 2 * c) / δ ≤ Real.log x := by linarith
    rw [div_le_iff₀ hδ] at this
    linarith
  calc logSum G N ≤ B * X₀ + 2 * c * J := hT
    _ ≤ B * X₀ + 3 * c * Real.log x + 2 * c := by linarith
    _ ≤ (3 * c + δ) * Real.log x := by linarith

/-- The facts on `A = ⌈n/D⌉` and `h = ⌊T/D⌋`. -/
theorem ceilDiv_facts {D n : ℕ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    n ≤ D * ((n + D - 1) / D) ∧ D * ((n + D - 1) / D) < n + D ∧ 1 ≤ (n + D - 1) / D := by
  have h1 := Nat.div_mul_le_self (n + D - 1) D
  have h2 := Nat.lt_div_mul_add (a := n + D - 1) (b := D) (by omega)
  obtain ⟨q, hq⟩ : ∃ q, q = (n + D - 1) / D := ⟨_, rfl⟩
  rw [← hq] at h1 h2 ⊢
  obtain ⟨p, hp⟩ : ∃ p, p = q * D := ⟨_, rfl⟩
  rw [← hp] at h1 h2
  have hnD : n + D - 1 + 1 = n + D := by omega
  rw [mul_comm, ← hp]
  refine ⟨by omega, by omega, ?_⟩
  by_contra h
  push Not at h
  have hq0 : q = 0 := by omega
  rw [hq0, zero_mul] at hp
  omega

/-- **The dilated window is a short window up to one endpoint.** -/
theorem norm_dilWin_sub_winSum_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {D n T : ℕ} (hD : 1 ≤ D)
    (hn : 1 ≤ n) :
    ‖dilWin f D n T - winSum f ((n + D - 1) / D - 1) (T / D)‖ ≤ 1 := by
  set A := (n + D - 1) / D with hA
  set h := T / D with hh
  obtain ⟨hA1, hA2, hA0⟩ := ceilDiv_facts (n := n) hD hn
  rw [← hA] at hA1 hA2 hA0
  have hh1 : D * h ≤ T := by rw [mul_comm]; exact Nat.div_mul_le_self T D
  have hh2 : T < D * (h + 1) := by
    have := Nat.lt_div_mul_add (a := T) (b := D) (by omega)
    rw [mul_add, mul_one, mul_comm]; exact this
  set I := (range (n + T)).filter (fun m => n ≤ D * m ∧ D * m < n + T) with hI
  set Wn := Ioc (A - 1) (A - 1 + h) with hW
  have hsub : Wn ⊆ I := by
    intro m hm
    rw [hW, mem_Ioc] at hm
    have hAm : D * A ≤ D * m := Nat.mul_le_mul_left D (by omega)
    have hm1 : D * (m + 1) ≤ D * (A + h) := Nat.mul_le_mul_left D (by omega)
    rw [mul_add, mul_one, mul_add] at hm1
    have hmD : m ≤ D * m := Nat.le_mul_of_pos_left m (by omega)
    rw [hI, mem_filter, mem_range]
    omega
  have hdiff : I \ Wn ⊆ {A + h} := by
    intro m hm
    rw [mem_sdiff, hI, mem_filter, mem_range] at hm
    obtain ⟨⟨-, h1, h2⟩, h3⟩ := hm
    rw [hW, mem_Ioc] at h3
    rw [mem_singleton]
    -- `m ≥ A`
    have hmA : A ≤ m := by
      by_contra hc
      push Not at hc
      have : D * (m + 1) ≤ D * A := Nat.mul_le_mul_left D (by omega)
      rw [mul_add, mul_one] at this
      omega
    -- `m ≤ A + h`
    have hmAh : m ≤ A + h := by
      by_contra hc
      push Not at hc
      have : D * (A + (h + 1)) ≤ D * m := Nat.mul_le_mul_left D (by omega)
      rw [mul_add] at this
      omega
    omega
  have hsplit : dilWin f D n T = winSum f (A - 1) h + ∑ m ∈ I \ Wn, f m := by
    rw [dilWin, winSum, ← hI, ← hW, ← sum_sdiff hsub]; ring
  rw [hsplit, add_sub_cancel_left]
  calc ‖∑ m ∈ I \ Wn, f m‖ ≤ ∑ m ∈ I \ Wn, ‖f m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ I \ Wn, (1 : ℝ) := sum_le_sum fun m _ => hf m
    _ = (I \ Wn).card := by simp
    _ ≤ ({A + h} : Finset ℕ).card := by exact_mod_cast card_le_card hdiff
    _ = 1 := by simp

/-- `n ↦ ⌈n/D⌉ − 1` is at most `D`-to-one, from `[X, 2X)` into `[Y, 2Y + 1]`. -/
theorem sum_comp_ceilDiv_le {G : ℕ → ℝ} (hG0 : ∀ k, 0 ≤ G k) {D X : ℕ} (hD : 1 ≤ D)
    (hX : 1 ≤ X) :
    ∑ n ∈ Ico X (2 * X), G ((n + D - 1) / D - 1)
      ≤ D * ∑ k ∈ Icc ((X + D - 1) / D - 1) (2 * ((X + D - 1) / D - 1) + 1), G k := by
  set φ : ℕ → ℕ := fun n => (n + D - 1) / D - 1 with hφ
  set Y := (X + D - 1) / D - 1 with hY
  obtain ⟨hX1, hX2, hX0⟩ := ceilDiv_facts (n := X) hD hX
  have himage : (Ico X (2 * X)).image φ ⊆ Icc Y (2 * Y + 1) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    rw [mem_Ico] at hn
    obtain ⟨hn1, hn2, hn0⟩ := ceilDiv_facts (n := n) hD (by omega)
    rw [mem_Icc]
    have hmono : (X + D - 1) / D ≤ (n + D - 1) / D := Nat.div_le_div_right (by omega)
    refine ⟨by simp only [hφ, hY]; omega, ?_⟩
    -- `D (φ n) < n < 2X ≤ D (2Y + 2)`
    by_contra hc
    push Not at hc
    have h1 : D * (2 * Y + 2) ≤ D * ((n + D - 1) / D - 1) :=
      Nat.mul_le_mul_left D (by simp only [hφ] at hc; omega)
    have h2 : D * ((n + D - 1) / D - 1) + D = D * ((n + D - 1) / D) := by
      rw [← mul_add_one]; congr 1; omega
    have h3 : D * (2 * Y + 2) = 2 * (D * ((X + D - 1) / D)) := by
      rw [hY]
      have : 2 * ((X + D - 1) / D - 1) + 2 = 2 * ((X + D - 1) / D) := by omega
      rw [this]; ring
    omega
  rw [sum_comp]
  have hfib : ∀ k ∈ (Ico X (2 * X)).image φ,
      (((Ico X (2 * X)).filter (fun n => φ n = k)).card • G k) ≤ D * G k := by
    intro k _
    rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hG0 k)
    have hsub : (Ico X (2 * X)).filter (fun n => φ n = k) ⊆ Ioc (D * k) (D * k + D) := by
      intro n hn
      rw [mem_filter, mem_Ico] at hn
      obtain ⟨⟨hn1, -⟩, hk⟩ := hn
      obtain ⟨hm1, hm2, hm0⟩ := ceilDiv_facts (n := n) hD (by omega)
      simp only [hφ] at hk
      have hk' : (n + D - 1) / D = k + 1 := by omega
      rw [hk'] at hm1 hm2
      rw [mul_add, mul_one] at hm1 hm2
      rw [mem_Ioc]
      omega
    have := card_le_card hsub
    rw [Nat.card_Ioc] at this
    exact_mod_cast le_trans this (by omega)
  calc ∑ k ∈ (Ico X (2 * X)).image φ, ((Ico X (2 * X)).filter (fun n => φ n = k)).card • G k
      ≤ ∑ k ∈ (Ico X (2 * X)).image φ, (D : ℝ) * G k := sum_le_sum hfib
    _ = D * ∑ k ∈ (Ico X (2 * X)).image φ, G k := by rw [mul_sum]
    _ ≤ D * ∑ k ∈ Icc Y (2 * Y + 1), G k :=
        mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg himage
          fun k _ _ => hG0 k) (Nat.cast_nonneg D)

end

end GaloisForLFunctions.LogarithmicChowla
