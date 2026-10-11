import GaloisForLFunctions.RHTower.ZetaRigidOrdinateLocalRH

/-!
# Local rigidity of the ordered ordinates

`RigidAt h n` says that the ordered positive ordinates increase strictly at `n` and the consecutive
gaps `g_n, g_{n+1}` satisfy `g_{n+1} ≤ g_n e^{(g_n+g_{n+1})/h}` and `g_n ≤ g_{n+1} e^{(g_n+g_{n+1})/h}`.
The gap chains, the normalized gap bounds and the local critical-line law of
`ZetaRigidOrdinateGaps` and `ZetaRigidOrdinateLocalRH` need rigidity only on the indices they touch:

* `gap_chain_local`: rigidity on `[n, n + j)` gives the chain bound from `n` to `n + j`;
* `exists_gap_mul_log_le_local`: rigidity on the indices with ordinate in `[γ_n, γ_n + 2w]` gives
  `g_n log γ_n ≤ c₂`;
* `exists_le_gap_mul_log_local`: rigidity on `[γ_n, γ_n + 2w + 2]` gives `c₁ ≤ g_n log γ_n`;
* `re_eq_half_of_strict_window`: strictness on a window puts every zero with ordinate in the window
  on the critical line.

The constants `w, c₁, c₂` do not depend on the window.
-/

open Complex Filter Topology Set Finset

namespace RHTower

noncomputable section

/-- **Rigidity at one index.** -/
def RigidAt (h : ℝ) (n : ℕ) : Prop :=
  xiOrderedPositiveOrdinate n < xiOrderedPositiveOrdinate (n + 1) ∧
    ordinateGap (n + 1) ≤ ordinateGap n * Real.exp ((ordinateGap n + ordinateGap (n + 1)) / h) ∧
    ordinateGap n ≤ ordinateGap (n + 1) * Real.exp ((ordinateGap n + ordinateGap (n + 1)) / h)

/-- Rigidity from `N₀` on is rigidity at every index `≥ N₀`. -/
theorem RigidOrdinates.rigidAt {h : ℝ} {N₀ : ℕ} (H : RigidOrdinates h N₀) {n : ℕ}
    (hn : N₀ ≤ n) : RigidAt h n :=
  ⟨H.strict n hn, H.up n hn, H.down n hn⟩

/-- **Local gap chains.** -/
theorem gap_chain_local {h : ℝ} {n : ℕ} (j : ℕ) (hR : ∀ k, n ≤ k → k < n + j → RigidAt h k) :
    ordinateGap (n + j) ≤ ordinateGap n * Real.exp (((xiOrderedPositiveOrdinate (n + j) -
        xiOrderedPositiveOrdinate n) + (xiOrderedPositiveOrdinate (n + j + 1) -
        xiOrderedPositiveOrdinate (n + 1))) / h) ∧
    ordinateGap n ≤ ordinateGap (n + j) * Real.exp (((xiOrderedPositiveOrdinate (n + j) -
        xiOrderedPositiveOrdinate n) + (xiOrderedPositiveOrdinate (n + j + 1) -
        xiOrderedPositiveOrdinate (n + 1))) / h) := by
  induction j with
  | zero => simp
  | succ j ih =>
    set γ := xiOrderedPositiveOrdinate with hγ
    have ih' := ih fun k hk1 hk2 => hR k hk1 (by omega)
    obtain ⟨-, hup, hdown⟩ := hR (n + j) (by omega) (by omega)
    have hE : ((γ (n + (j + 1)) - γ n) + (γ (n + (j + 1) + 1) - γ (n + 1))) / h =
        ((γ (n + j) - γ n) + (γ (n + j + 1) - γ (n + 1))) / h +
          (ordinateGap (n + j) + ordinateGap (n + j + 1)) / h := by
      simp only [ordinateGap, hγ]
      rw [show n + (j + 1) = n + j + 1 by ring]
      ring
    rw [show n + (j + 1) = n + j + 1 by ring] at hE ⊢
    rw [hE, Real.exp_add]
    constructor
    · calc ordinateGap (n + j + 1)
          ≤ ordinateGap (n + j) * Real.exp ((ordinateGap (n + j) + ordinateGap (n + j + 1)) / h) :=
            hup
        _ ≤ (ordinateGap n * Real.exp (((γ (n + j) - γ n) + (γ (n + j + 1) - γ (n + 1))) / h)) *
              Real.exp ((ordinateGap (n + j) + ordinateGap (n + j + 1)) / h) :=
            mul_le_mul_of_nonneg_right ih'.1 (Real.exp_pos _).le
        _ = _ := by ring
    · calc ordinateGap n
          ≤ ordinateGap (n + j) * Real.exp (((γ (n + j) - γ n) + (γ (n + j + 1) - γ (n + 1))) / h) :=
            ih'.2
        _ ≤ (ordinateGap (n + j + 1) *
              Real.exp ((ordinateGap (n + j) + ordinateGap (n + j + 1)) / h)) *
              Real.exp (((γ (n + j) - γ n) + (γ (n + j + 1) - γ (n + 1))) / h) :=
            mul_le_mul_of_nonneg_right hdown (Real.exp_pos _).le
        _ = _ := by ring

/-- Local chain bounds in span form. -/
theorem gap_chain_span_local {h : ℝ} (hh : 0 < h) {n : ℕ} (j : ℕ)
    (hR : ∀ k, n ≤ k → k < n + j → RigidAt h k) {D : ℝ}
    (hD : xiOrderedPositiveOrdinate (n + j + 1) - xiOrderedPositiveOrdinate n ≤ D) :
    ordinateGap (n + j) ≤ ordinateGap n * Real.exp (2 * D / h) ∧
    ordinateGap n ≤ ordinateGap (n + j) * Real.exp (2 * D / h) := by
  obtain ⟨h1, h2⟩ := gap_chain_local j hR
  have hE : Real.exp (((xiOrderedPositiveOrdinate (n + j) - xiOrderedPositiveOrdinate n) +
      (xiOrderedPositiveOrdinate (n + j + 1) - xiOrderedPositiveOrdinate (n + 1))) / h) ≤
      Real.exp (2 * D / h) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hh.le
    linarith [chain_exponent_le n j]
  exact ⟨h1.trans (mul_le_mul_of_nonneg_left hE (ordinateGap_nonneg n)),
    h2.trans (mul_le_mul_of_nonneg_left hE (ordinateGap_nonneg _))⟩

/-- **Local upper normalized gap bound, uniform in the scale.** For some `w > 0` and `T₂`, every
`h > 0` and every `γ_n ≥ T₂` that is `h`-rigid on `[γ_n, γ_n + 2w]` satisfy
`g_n log γ_n ≤ 4w e^{4w/h}`. -/
theorem exists_gap_mul_log_le_uniform :
    ∃ w : ℝ, 0 < w ∧ ∃ T₂ : ℝ, ∀ h : ℝ, 0 < h → ∀ n, T₂ ≤ xiOrderedPositiveOrdinate n →
      (∀ k, n ≤ k → xiOrderedPositiveOrdinate k ≤ xiOrderedPositiveOrdinate n + 2 * w →
        RigidAt h k) →
      ordinateGap n * Real.log (xiOrderedPositiveOrdinate n) ≤ 4 * w * Real.exp (4 * w / h) := by
  obtain ⟨w, hw, T₁, hT₁4, hwin⟩ := exists_xiZeroCount_window_ge_log
  refine ⟨w, hw, max T₁ (Real.exp 2), fun h hh n hγ hR => ?_⟩
  set γ := xiOrderedPositiveOrdinate with hγdef
  have hγT₁ : T₁ ≤ γ n := le_trans (le_max_left _ _) hγ
  have hγe : Real.exp 2 ≤ γ n := le_trans (le_max_right _ _) hγ
  have hγ0 : 0 < γ n := lt_of_lt_of_le (Real.exp_pos _) hγe
  have hlog2 : 2 ≤ Real.log (γ n) := by
    have := Real.log_le_log (Real.exp_pos _) hγe; rwa [Real.log_exp] at this
  have hwinn := hwin (γ n + w) (by linarith)
  rw [show γ n + w - w = γ n by ring, show γ n + w + w = γ n + 2 * w by ring] at hwinn
  have hstrictn := (hR n le_rfl (by linarith)).1
  have hcount := xiZeroCount_ordinate_eq hstrictn
  rw [← hγdef] at hcount
  set m : ℤ := xiZeroCount (γ n + 2 * w) - ((n + 1 : ℕ) : ℤ) with hm
  have hlogw : Real.log (γ n) ≤ Real.log (γ n + w) := Real.log_le_log hγ0 (by linarith)
  have hmR : Real.log (γ n) ≤ (m : ℝ) := by
    have hc : ((xiZeroCount (γ n) : ℤ) : ℝ) = (n : ℝ) + 1 := by rw [hcount]; push_cast; ring
    rw [hc] at hwinn
    rw [hm]; push_cast
    linarith
  have hm2 : (2 : ℤ) ≤ m := by
    have : (2 : ℝ) ≤ (m : ℝ) := le_trans hlog2 hmR
    exact_mod_cast this
  set M : ℕ := m.toNat with hM
  have hMm : (M : ℤ) = m := Int.toNat_of_nonneg (by omega)
  have hMR : (M : ℝ) = (m : ℝ) := by exact_mod_cast hMm
  have hM2 : 2 ≤ M := by omega
  have hγM : γ (n + M) ≤ γ n + 2 * w := by
    apply xiOrderedPositiveOrdinate_le_iff.mpr
    have : xiZeroCount (γ n + 2 * w) = m + ((n + 1 : ℕ) : ℤ) := by rw [hm]; ring
    rw [this, ← hMm]; push_cast; omega
  have hsum := sum_ordinateGap (n + 1) (M - 1)
  rw [show n + 1 + (M - 1) = n + M by omega] at hsum
  have hterm : ∀ i ∈ Finset.range (M - 1),
      ordinateGap n * Real.exp (-(4 * w / h)) ≤ ordinateGap (n + 1 + i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hspan : γ (n + (1 + i) + 1) - γ n ≤ 2 * w := by
      have := xiOrderedPositiveOrdinate_monotone (show n + (1 + i) + 1 ≤ n + M by omega)
      linarith
    have hRk : ∀ k, n ≤ k → k < n + (1 + i) → RigidAt h k := fun k hk1 hk2 =>
      hR k hk1 (by
        have := xiOrderedPositiveOrdinate_monotone (show k ≤ n + M by omega)
        linarith)
    have hc := (gap_chain_span_local hh (1 + i) hRk hspan).2
    rw [show n + (1 + i) = n + 1 + i by ring, show 2 * (2 * w) / h = 4 * w / h by ring] at hc
    rw [Real.exp_neg]
    calc ordinateGap n * (Real.exp (4 * w / h))⁻¹
        ≤ (ordinateGap (n + 1 + i) * Real.exp (4 * w / h)) * (Real.exp (4 * w / h))⁻¹ :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = ordinateGap (n + 1 + i) := by field_simp
  have hlow := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsum] at hlow
  have hspan1 : γ (n + M) - γ (n + 1) ≤ 2 * w := by
    have := xiOrderedPositiveOrdinate_monotone (Nat.le_succ n)
    linarith
  have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hM1] at hlow
  have hg0 := ordinateGap_nonneg n
  have hfin : ((M : ℝ) - 1) * ordinateGap n ≤ 2 * w * Real.exp (4 * w / h) := by
    have h1 : ((M : ℝ) - 1) * (ordinateGap n * Real.exp (-(4 * w / h))) ≤ 2 * w := by linarith
    have h2 : Real.exp (-(4 * w / h)) * Real.exp (4 * w / h) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (4 * w / h)).le
    calc ((M : ℝ) - 1) * ordinateGap n
        = ((M : ℝ) - 1) * (ordinateGap n * Real.exp (-(4 * w / h))) * Real.exp (4 * w / h) := by
          rw [mul_assoc, mul_assoc, h2, mul_one]
      _ ≤ 2 * w * Real.exp (4 * w / h) := h3
  have hMl : Real.log (γ n) ≤ 2 * ((M : ℝ) - 1) := by rw [hMR]; linarith
  calc ordinateGap n * Real.log (γ n) ≤ ordinateGap n * (2 * ((M : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hMl hg0
    _ = 2 * (((M : ℝ) - 1) * ordinateGap n) := by ring
    _ ≤ 2 * (2 * w * Real.exp (4 * w / h)) := by linarith
    _ = 4 * w * Real.exp (4 * w / h) := by ring


/-- **Local upper normalized gap bound.** -/
theorem exists_gap_mul_log_le_local {h : ℝ} (hh : 0 < h) :
    ∃ w : ℝ, 0 < w ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ T₂ : ℝ, ∀ n, T₂ ≤ xiOrderedPositiveOrdinate n →
      (∀ k, n ≤ k → xiOrderedPositiveOrdinate k ≤ xiOrderedPositiveOrdinate n + 2 * w →
        RigidAt h k) →
      ordinateGap n * Real.log (xiOrderedPositiveOrdinate n) ≤ c₂ := by
  obtain ⟨w, hw, T₂, hU⟩ := exists_gap_mul_log_le_uniform
  exact ⟨w, hw, 4 * w * Real.exp (4 * w / h), by positivity, T₂, hU h hh⟩

/-- The height above which the lower gap bound holds at scale `h`. -/
def lowerGapThreshold (w T₂ h : ℝ) : ℝ :=
  max (max T₂ 4) (max (Real.exp (2 * (4 * w * Real.exp (4 * w / h))))
    (Real.exp (xiLineTwoLogDerivConstant + 1)))

/-- **Local lower normalized gap bound, uniform in the scale.** For some `w > 0` and `T₂`, every
`h > 0` and every `γ_n ≥ lowerGapThreshold w T₂ h` that is `h`-rigid on `[γ_n, γ_n + 2w + 2]`
satisfy `e^{−2/h}/64 ≤ g_n log γ_n`. -/
theorem exists_le_gap_mul_log_uniform :
    ∃ w : ℝ, 0 < w ∧ ∃ T₂ : ℝ, ∀ h : ℝ, 0 < h → ∀ n,
      lowerGapThreshold w T₂ h ≤ xiOrderedPositiveOrdinate n →
      (∀ k, n ≤ k → xiOrderedPositiveOrdinate k ≤ xiOrderedPositiveOrdinate n + 2 * w + 2 →
        RigidAt h k) →
      Real.exp (-(2 / h)) / 64 ≤ ordinateGap n * Real.log (xiOrderedPositiveOrdinate n) := by
  obtain ⟨w, hw, T₂, hU'⟩ := exists_gap_mul_log_le_uniform
  refine ⟨w, hw, T₂, fun h hh n hγ hR => ?_⟩
  set c₂ := 4 * w * Real.exp (4 * w / h) with hc₂def
  have hc₂ : 0 < c₂ := by positivity
  have hU := hU' h hh
  set C₀ := xiLineTwoLogDerivConstant with hC₀
  have hC₀0 : 0 ≤ C₀ := xiLineTwoLogDerivConstant_nonneg
  unfold lowerGapThreshold at hγ
  rw [← hc₂def, ← hC₀] at hγ
  set γ := xiOrderedPositiveOrdinate with hγdef
  have hγT₂ : T₂ ≤ γ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hγ
  have hγ4 : 4 ≤ γ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hγ
  have hγc : Real.exp (2 * c₂) ≤ γ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hγ
  have hγC : Real.exp (C₀ + 1) ≤ γ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hγ
  have hγ0 : 0 < γ n := by linarith
  have hlogc : 2 * c₂ ≤ Real.log (γ n) := by
    have := Real.log_le_log (Real.exp_pos _) hγc; rwa [Real.log_exp] at this
  have hlogC : C₀ + 1 ≤ Real.log (γ n) := by
    have := Real.log_le_log (Real.exp_pos _) hγC; rwa [Real.log_exp] at this
  have hlog0 : 0 < Real.log (γ n) := by linarith
  -- gaps within distance `1` of `γ_n` are at most `c₂ / log γ_n`
  have hsmall : ∀ j, γ (n + j) ≤ γ n + 1 → ordinateGap (n + j) ≤ c₂ / Real.log (γ n) := by
    intro j hj
    have hmono : γ n ≤ γ (n + j) := xiOrderedPositiveOrdinate_monotone (Nat.le_add_right n j)
    have h1 := hU (n + j) (le_trans hγT₂ hmono) (fun k hk1 hk2 => hR k (by omega) (by linarith))
    have hlj : Real.log (γ n) ≤ Real.log (γ (n + j)) := Real.log_le_log hγ0 hmono
    rw [le_div_iff₀ hlog0]
    calc ordinateGap (n + j) * Real.log (γ n) ≤ ordinateGap (n + j) * Real.log (γ (n + j)) :=
          mul_le_mul_of_nonneg_left hlj (ordinateGap_nonneg _)
      _ ≤ c₂ := h1
  have hhalf : c₂ / Real.log (γ n) ≤ 1 / 2 := by
    rw [div_le_iff₀ hlog0]; linarith
  set ε := ordinateGap n * Real.exp (2 / h) with hε
  have hg0 : 0 < ordinateGap n := sub_pos.mpr (hR n le_rfl (by linarith)).1
  have hε0 : 0 < ε := by positivity
  have hprop : ∀ j : ℕ, (j : ℝ) * ε ≤ 1 / 2 → γ (n + j) - γ n ≤ j * ε := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      push_cast at hj ⊢
      have hj' : (j : ℝ) * ε ≤ 1 / 2 := by nlinarith
      have h1 := ih hj'
      have h2 := hsmall j (by linarith)
      have hspan : γ (n + j + 1) - γ n ≤ 1 := by
        have : γ (n + j + 1) - γ n = (γ (n + j) - γ n) + ordinateGap (n + j) := by
          simp only [ordinateGap, hγdef]; ring
        rw [this]; linarith
      have hRk : ∀ k, n ≤ k → k < n + j → RigidAt h k := fun k hk1 hk2 =>
        hR k hk1 (by
          have := xiOrderedPositiveOrdinate_monotone (show k ≤ n + j by omega)
          rw [← hγdef] at this; linarith)
      have hc := (gap_chain_span_local hh j hRk hspan).1
      rw [show 2 * 1 / h = 2 / h by ring] at hc
      have : γ (n + (j + 1)) - γ n = (γ (n + j) - γ n) + ordinateGap (n + j) := by
        simp only [ordinateGap, hγdef]; ring_nf
      rw [this]
      linarith
  set K : ℕ := ⌊1 / (2 * ε)⌋₊ with hK
  have hKε : (K : ℝ) * ε ≤ 1 / 2 := by
    have := Nat.floor_le (show 0 ≤ 1 / (2 * ε) by positivity)
    rw [← hK] at this
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hwin : ∀ j ≤ K, |γ (n + j) - γ n| ≤ 1 / 2 := by
    intro j hj
    have hjK : (j : ℝ) * ε ≤ (K : ℝ) * ε :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hε0.le
    have h1 := hprop j (le_trans hjK hKε)
    have h2 : γ n ≤ γ (n + j) := xiOrderedPositiveOrdinate_monotone (Nat.le_add_right n j)
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hcard := card_le_two_lorentzMass (t := γ n) (n := n) (K := K) hwin
  have hmass := lorentzMass_le_log (γ n)
  rw [abs_of_pos hγ0] at hmass
  have hlog4 : Real.log (γ n + 4) ≤ Real.log 2 + Real.log (γ n) := by
    rw [← Real.log_mul (by norm_num) hγ0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hKlt : 1 / (2 * ε) < (K : ℝ) + 1 := by
    rw [hK]; exact Nat.lt_floor_add_one _
  push_cast at hcard
  have hbound : 1 / (2 * ε) < 32 * Real.log (γ n) := by linarith
  rw [div_lt_iff₀ (by positivity)] at hbound
  have hexp : Real.exp (-(2 / h)) * Real.exp (2 / h) = 1 := by rw [← Real.exp_add]; simp
  have h1 : 1 ≤ 64 * (ordinateGap n * Real.log (γ n)) * Real.exp (2 / h) := by
    rw [hε] at hbound; nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(2 / h))).le
  rw [mul_one] at h2
  have e : Real.exp (-(2 / h)) * (64 * (ordinateGap n * Real.log (γ n)) * Real.exp (2 / h)) =
      64 * (ordinateGap n * Real.log (γ n)) := by
    rw [show Real.exp (-(2 / h)) * (64 * (ordinateGap n * Real.log (γ n)) * Real.exp (2 / h)) =
      64 * (ordinateGap n * Real.log (γ n)) * (Real.exp (-(2 / h)) * Real.exp (2 / h)) by ring,
      hexp, mul_one]
  rw [e] at h2
  linarith

/-- **Local lower normalized gap bound.** -/
theorem exists_le_gap_mul_log_local {h : ℝ} (hh : 0 < h) :
    ∃ w : ℝ, 0 < w ∧ ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ T₃ : ℝ, ∀ n, T₃ ≤ xiOrderedPositiveOrdinate n →
      (∀ k, n ≤ k → xiOrderedPositiveOrdinate k ≤ xiOrderedPositiveOrdinate n + 2 * w + 2 →
        RigidAt h k) →
      c₁ ≤ ordinateGap n * Real.log (xiOrderedPositiveOrdinate n) := by
  obtain ⟨w, hw, T₂, hL⟩ := exists_le_gap_mul_log_uniform
  exact ⟨w, hw, Real.exp (-(2 / h)) / 64, by positivity, lowerGapThreshold w T₂ h, hL h hh⟩

/-- **Windowed critical line.** If the ordered ordinates increase strictly at every index with
ordinate in `[X, Y]`, every zero of `ξ` with ordinate in `[X, Y] ∩ (0, ∞)` is on the critical
line. -/
theorem re_eq_half_of_strict_window {X Y : ℝ}
    (hS : ∀ k, X ≤ xiOrderedPositiveOrdinate k → xiOrderedPositiveOrdinate k ≤ Y →
      xiOrderedPositiveOrdinate k < xiOrderedPositiveOrdinate (k + 1))
    {ρ : ℂ} (hρ : xi ρ = 0) (hX : X ≤ ρ.im) (hY : ρ.im ≤ Y) (hpos : 0 < ρ.im) :
    ρ.re = 1 / 2 := by
  set ρ' : ℂ := 1 - (starRingEnd ℂ) ρ with hρ'
  have hρ'0 : xi ρ' = 0 := by rw [hρ', xi_one_sub, xi_conj, hρ, map_zero]
  have him' : ρ'.im = ρ.im := by simp [hρ']
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  obtain ⟨q', hq'⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ'0
  have hqpos : 0 < (q.1 : ℂ).im := by rw [hq]; exact hpos
  have hq'pos : 0 < (q'.1 : ℂ).im := by rw [hq', him']; exact hpos
  obtain ⟨n, hn⟩ := exists_xiOrderedPositiveZeroCopy_eq hqpos
  obtain ⟨n', hn'⟩ := exists_xiOrderedPositiveZeroCopy_eq hq'pos
  have hγn : xiOrderedPositiveOrdinate n = ρ.im := by
    rw [← xiOrderedPositiveZeroCopy_im_eq, hn, hq]
  have hγn' : xiOrderedPositiveOrdinate n' = ρ.im := by
    rw [← xiOrderedPositiveZeroCopy_im_eq, hn', hq', him']
  have hnn : n = n' := by
    rcases lt_trichotomy n n' with hlt | heq | hgt
    · have h1 := hS n (by rw [hγn]; exact hX) (by rw [hγn]; exact hY)
      have h2 := xiOrderedPositiveOrdinate_monotone (show n + 1 ≤ n' by omega)
      linarith
    · exact heq
    · have h1 := hS n' (by rw [hγn']; exact hX) (by rw [hγn']; exact hY)
      have h2 := xiOrderedPositiveOrdinate_monotone (show n' + 1 ≤ n by omega)
      linarith
  have hqq : q = q' := by rw [← hn, ← hn', hnn]
  have : ρ = ρ' := by rw [← hq, ← hq', hqq]
  have hre := congrArg Complex.re this
  simp [hρ'] at hre
  linarith

/-- The ordered copies with ordinate in a strict window are `½ + iγ_n`. -/
theorem orderedPositiveZeroCopy_eq_of_strict_window {X Y : ℝ}
    (hS : ∀ k, X ≤ xiOrderedPositiveOrdinate k → xiOrderedPositiveOrdinate k ≤ Y →
      xiOrderedPositiveOrdinate k < xiOrderedPositiveOrdinate (k + 1))
    {n : ℕ} (hX : X ≤ xiOrderedPositiveOrdinate n) (hY : xiOrderedPositiveOrdinate n ≤ Y) :
    ((xiOrderedPositiveZeroCopy n).1 : ℂ) = 1 / 2 + (xiOrderedPositiveOrdinate n : ℂ) * I := by
  have him := xiOrderedPositiveZeroCopy_im_eq n
  have hpos := xiOrderedPositiveOrdinate_pos n
  have hre := re_eq_half_of_strict_window hS (xi_xiZeroCopy_eq_zero _) (by rw [him]; exact hX)
    (by rw [him]; exact hY) (by rw [him]; exact hpos)
  apply Complex.ext
  · rw [hre]; simp
  · rw [him]; simp

end

end RHTower
