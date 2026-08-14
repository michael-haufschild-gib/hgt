import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentAggregateReflection
import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeCells

/-!
# Dyadic amplitude layer extraction

Cancellation-preserving cell extraction produces a lower bound for a finite first moment.  The
Maynard receiver needs a superlevel cardinality times its amplitude.  This module proves the exact
finite layer-cake bridge: after paying the bottom layer, one dyadic superlevel retains the first
moment up to only the number of amplitude layers.
-/

noncomputable section
namespace RHTower.Sieve

open Finset

/-- Canonical Maynard amplitude attached to a selected aggregate threshold, measured relative to
the physical lower support scale and after paying exact one-box selection cost. -/
def routeTCellAmplitude (L X k : ℕ) (N V : ℝ) : ℝ :=
  maynardAmplitude 1 (N / (2 ^ (2 * k) : ℝ))
    (V / heathBrownEligibleBoxCost L X k)

/-- A selected threshold between the physical `3/4` scale and the one-box cost has canonical
amplitude in the complete Route-T receiver range `[3/4,1]`. -/
theorem routeTCellAmplitude_range
    (L X k : ℕ) (hk : 0 < k) {N V : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (hV : 0 < V)
    (hlow : heathBrownEligibleBoxCost L X k *
        (N / (2 ^ (2 * k) : ℝ)) ^ (-(1 : ℝ) / 4) ≤ V)
    (hhigh : V ≤ heathBrownEligibleBoxCost L X k) :
    3 / 4 ≤ routeTCellAmplitude L X k N V ∧
      routeTCellAmplitude L X k N V ≤ 1 := by
  let D : ℝ := N / (2 ^ (2 * k) : ℝ)
  let C : ℝ := heathBrownEligibleBoxCost L X k
  let W : ℝ := V / C
  have hC : 0 < C := heathBrownEligibleBoxCost_pos L X k hk
  have hW : 0 < W := div_pos hV hC
  have hWle : W ≤ 1 := (div_le_one hC).2 hhigh
  have hlow' : D ^ ((3 / 4 : ℝ) - 1) ≤ W := by
    dsimp only [D, C, W]
    rw [le_div_iff₀ hC]
    have he : (3 / 4 : ℝ) - 1 = -(1 : ℝ) / 4 := by norm_num
    rw [he]
    simpa only [mul_comm] using hlow
  constructor
  · dsimp only [routeTCellAmplitude, D, C, W]
    exact le_maynardAmplitude_of_rpow_le hD hlow'
  · have hlogW : Real.log W ≤ 0 := Real.log_nonpos hW.le hWle
    have hlogD : 0 < Real.log D := Real.log_pos hD
    dsimp only [routeTCellAmplitude, maynardAmplitude, D, C, W]
    exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hlogW hlogD.le)

/-- Physical window relevance discharges the complete selected-cell receiver's reserve premise at
the canonical cell amplitude.  Since that amplitude is at most one, the exponent is nonpositive,
and every relevant box lower edge exceeds the physical scale. -/
theorem routeTCellAmplitude_windowRelevant_reserve
    (L X k : ℕ) (hk : 0 < k) {N V : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (hV : 0 < V)
    (hhigh : V ≤ heathBrownEligibleBoxCost L X k) :
    ∀ box : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxWindowRelevant N X k box →
      heathBrownEligibleBoxCost L X k *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
              (routeTCellAmplitude L X k N V - 1) ≤ V := by
  let D : ℝ := N / (2 ^ (2 * k) : ℝ)
  let C : ℝ := heathBrownEligibleBoxCost L X k
  let W : ℝ := V / C
  have hC : 0 < C := heathBrownEligibleBoxCost_pos L X k hk
  have hW : 0 < W := div_pos hV hC
  have hWle : W ≤ 1 := (div_le_one hC).2 hhigh
  have halpha : routeTCellAmplitude L X k N V ≤ 1 := by
    have hlogW : Real.log W ≤ 0 := Real.log_nonpos hW.le hWle
    have hlogD : 0 < Real.log D := Real.log_pos hD
    dsimp only [routeTCellAmplitude, maynardAmplitude, D, C, W]
    exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hlogW hlogD.le)
  have hexact : D ^ (routeTCellAmplitude L X k N V - 1) = W := by
    dsimp only [routeTCellAmplitude, D, C, W]
    exact rpow_maynardAmplitude_sub_abscissa hD hW
  intro box hbox
  have hbase := windowRelevant_heathBrownBox_coreLower_gt hbox
  have hpow :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
          (routeTCellAmplitude L X k N V - 1) ≤
        D ^ (routeTCellAmplitude L X k N V - 1) := by
    exact Real.rpow_le_rpow_of_nonpos (by dsimp only [D]; linarith)
      hbase.le (sub_nonpos.mpr halpha)
  calc
    C * (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
          (routeTCellAmplitude L X k N V - 1) ≤
        C * D ^ (routeTCellAmplitude L X k N V - 1) :=
      mul_le_mul_of_nonneg_left hpow hC.le
    _ = C * W := by rw [hexact]
    _ = V := by dsimp only [W]; field_simp

/-- Adaptive logarithmic coordinate for an aggregate threshold.  Thresholds below one-box cost
are normalized at the physical lower support edge; thresholds above it are normalized at the
physical upper support edge.  These are exactly the two monotonicity directions of real powers. -/
def routeTAdaptiveCellAmplitude
    (L X k : ℕ) (N V : ℝ) : ℝ :=
  let C := heathBrownEligibleBoxCost L X k
  if V ≤ C then
    maynardAmplitude 1 (N / (2 ^ (2 * k) : ℝ)) (V / C)
  else
    maynardAmplitude 1 (X : ℝ) (V / C)

/-- **Two-edge amplitude reserve.**  Every positive selected aggregate threshold, with no a priori
upper or lower amplitude restriction, has a canonical exponent satisfying the selected-cell
receiver reserve on every window-relevant box.  Below one-box cost the negative exponent uses the
lower support edge; above one-box cost the positive exponent uses the upper support edge. -/
theorem routeTAdaptiveCellAmplitude_windowRelevant_reserve
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X) {N V : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (hV : 0 < V) :
    ∀ box : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxWindowRelevant N X k box →
      heathBrownEligibleBoxCost L X k *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
              (routeTAdaptiveCellAmplitude L X k N V - 1) ≤ V := by
  let D : ℝ := N / (2 ^ (2 * k) : ℝ)
  let C : ℝ := heathBrownEligibleBoxCost L X k
  let W : ℝ := V / C
  have hC : 0 < C := heathBrownEligibleBoxCost_pos L X k hk
  have hW : 0 < W := div_pos hV hC
  intro box hbox
  by_cases hVC : V ≤ C
  · have halpha : routeTAdaptiveCellAmplitude L X k N V ≤ 1 := by
      have hWle : W ≤ 1 := (div_le_one hC).2 hVC
      have hlogW : Real.log W ≤ 0 := Real.log_nonpos hW.le hWle
      have hlogD : 0 < Real.log D := Real.log_pos (by simpa only [D] using hD)
      rw [routeTAdaptiveCellAmplitude, if_pos hVC]
      exact add_le_of_nonpos_right
        (div_nonpos_of_nonpos_of_nonneg hlogW hlogD.le)
    have hexact : D ^
        (routeTAdaptiveCellAmplitude L X k N V - 1) = W := by
      rw [routeTAdaptiveCellAmplitude, if_pos hVC]
      exact rpow_maynardAmplitude_sub_abscissa
        (by simpa only [D] using hD) hW
    have hbase := windowRelevant_heathBrownBox_coreLower_gt hbox
    have hpow :
        (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
            (routeTAdaptiveCellAmplitude L X k N V - 1) ≤
          D ^ (routeTAdaptiveCellAmplitude L X k N V - 1) := by
      exact Real.rpow_le_rpow_of_nonpos (by dsimp only [D]; linarith)
        hbase.le (sub_nonpos.mpr halpha)
    calc
      C * (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
            (routeTAdaptiveCellAmplitude L X k N V - 1) ≤
          C * D ^ (routeTAdaptiveCellAmplitude L X k N V - 1) :=
        mul_le_mul_of_nonneg_left hpow hC.le
      _ = C * W := by rw [hexact]
      _ = V := by dsimp only [W]; field_simp
  · have hCV : C < V := lt_of_not_ge hVC
    have hWone : 1 ≤ W := (one_le_div hC).2 hCV.le
    have hXR : (1 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have halpha : 1 ≤ routeTAdaptiveCellAmplitude L X k N V := by
      rw [routeTAdaptiveCellAmplitude, if_neg hVC]
      apply le_maynardAmplitude_of_rpow_le hXR
      simpa using hWone
    have hexact : (X : ℝ) ^
        (routeTAdaptiveCellAmplitude L X k N V - 1) = W := by
      rw [routeTAdaptiveCellAmplitude, if_neg hVC]
      exact rpow_maynardAmplitude_sub_abscissa hXR hW
    have hbase0 : 0 ≤
        (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) := by positivity
    have hbaseUpper := windowRelevant_heathBrownBox_coreLower_le hbox
    have hpow :
        (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
            (routeTAdaptiveCellAmplitude L X k N V - 1) ≤
          (X : ℝ) ^ (routeTAdaptiveCellAmplitude L X k N V - 1) :=
      Real.rpow_le_rpow hbase0 hbaseUpper (sub_nonneg.mpr halpha)
    calc
      C * (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
            (routeTAdaptiveCellAmplitude L X k N V - 1) ≤
          C * (X : ℝ) ^
            (routeTAdaptiveCellAmplitude L X k N V - 1) :=
        mul_le_mul_of_nonneg_left hpow hC.le
      _ = C * W := by rw [hexact]
      _ = V := by dsimp only [W]; field_simp

theorem routeTAdaptiveCellAmplitude_threeQuarter_le
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X) {N V : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (hV : 0 < V)
    (hlow : heathBrownEligibleBoxCost L X k *
        (N / (2 ^ (2 * k) : ℝ)) ^ (-(1 : ℝ) / 4) ≤ V) :
    3 / 4 ≤ routeTAdaptiveCellAmplitude L X k N V := by
  let C : ℝ := heathBrownEligibleBoxCost L X k
  have hC : 0 < C := heathBrownEligibleBoxCost_pos L X k hk
  by_cases hVC : V ≤ C
  · rw [routeTAdaptiveCellAmplitude, if_pos hVC]
    exact (routeTCellAmplitude_range L X k hk hD hV hlow hVC).1
  · have hCV : C < V := lt_of_not_ge hVC
    have hXR : (1 : ℝ) < X := by exact_mod_cast hX
    have hone : 1 ≤ maynardAmplitude 1 (X : ℝ) (V / C) := by
      apply le_maynardAmplitude_of_rpow_le hXR
      simpa using (one_le_div hC).2 hCV.le
    rw [routeTAdaptiveCellAmplitude, if_neg hVC]
    linarith

/-- Finite geometric identity in the normalization used by amplitude superlevels. -/
theorem base_add_sum_two_pow_mul (v : ℝ) (Q : ℕ) :
    v + ∑ q ∈ Finset.range Q, (((2 ^ q : ℕ) : ℝ) * v) =
      (((2 ^ Q : ℕ) : ℝ) * v) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih]
      push_cast [pow_succ]
      ring

/-- A bounded nonnegative-scale value is dominated by its base layer plus every dyadic threshold
which it crosses. -/
theorem le_base_add_sum_dyadic_threshold
    {a v : ℝ} (hv : 0 < v) (Q : ℕ)
    (ha : a ≤ (((2 ^ Q : ℕ) : ℝ) * v)) :
    a ≤ v + ∑ q ∈ Finset.range Q,
      if (((2 ^ q : ℕ) : ℝ) * v) ≤ a then
        (((2 ^ q : ℕ) : ℝ) * v)
      else 0 := by
  induction Q with
  | zero => simpa using ha
  | succ Q ih =>
      rw [Finset.sum_range_succ]
      by_cases hprev : a ≤ (((2 ^ Q : ℕ) : ℝ) * v)
      · have hih := ih hprev
        have hterm : 0 ≤
            (if (((2 ^ Q : ℕ) : ℝ) * v) ≤ a then
              (((2 ^ Q : ℕ) : ℝ) * v) else 0) := by
          split_ifs <;> positivity
        linarith
      · have hall : ∀ q ∈ Finset.range (Q + 1),
            (((2 ^ q : ℕ) : ℝ) * v) ≤ a := by
          intro q hq
          have hqQ : q ≤ Q := by simpa using hq
          have hpNat : 2 ^ q ≤ 2 ^ Q := Nat.pow_le_pow_right (by omega) hqQ
          have hp : (((2 ^ q : ℕ) : ℝ) ≤ ((2 ^ Q : ℕ) : ℝ)) := by
            exact_mod_cast hpNat
          have hscale : (((2 ^ q : ℕ) : ℝ) * v) ≤
              (((2 ^ Q : ℕ) : ℝ) * v) :=
            mul_le_mul_of_nonneg_right hp hv.le
          exact hscale.trans (le_of_lt (lt_of_not_ge hprev))
        have hsum : v + ∑ q ∈ Finset.range (Q + 1),
            (if (((2 ^ q : ℕ) : ℝ) * v) ≤ a then
              (((2 ^ q : ℕ) : ℝ) * v) else 0) =
            (((2 ^ (Q + 1) : ℕ) : ℝ) * v) := by
          rw [Finset.sum_congr rfl (fun q hq => if_pos (hall q hq))]
          exact base_add_sum_two_pow_mul v (Q + 1)
        simpa only [Finset.sum_range_succ] using ha.trans_eq hsum.symm

/-- Finite layer-cake inequality.  The first moment is bounded by the base layer plus weighted
cardinalities of dyadic superlevel sets. -/
theorem sum_le_card_mul_add_sum_dyadic_superlevel
    {ι : Type*} {s : Finset ι} {a : ι → ℝ} {v : ℝ} (hv : 0 < v) (Q : ℕ)
    (hupper : ∀ i ∈ s, a i ≤ (((2 ^ Q : ℕ) : ℝ) * v)) :
    ∑ i ∈ s, a i ≤
      (s.card : ℝ) * v +
        ∑ q ∈ Finset.range Q,
          (((2 ^ q : ℕ) : ℝ) * v) *
            ((s.filter fun i => (((2 ^ q : ℕ) : ℝ) * v) ≤ a i).card : ℝ) := by
  classical
  have hpoint : ∀ i ∈ s, a i ≤ v + ∑ q ∈ Finset.range Q,
      if (((2 ^ q : ℕ) : ℝ) * v) ≤ a i then
        (((2 ^ q : ℕ) : ℝ) * v) else 0 := by
    intro i hi
    exact le_base_add_sum_dyadic_threshold hv Q (hupper i hi)
  calc
    ∑ i ∈ s, a i ≤ ∑ i ∈ s, (v + ∑ q ∈ Finset.range Q,
        if (((2 ^ q : ℕ) : ℝ) * v) ≤ a i then
          (((2 ^ q : ℕ) : ℝ) * v) else 0) :=
      Finset.sum_le_sum hpoint
    _ = (s.card : ℝ) * v + ∑ q ∈ Finset.range Q,
          (((2 ^ q : ℕ) : ℝ) * v) *
            ((s.filter fun i => (((2 ^ q : ℕ) : ℝ) * v) ≤ a i).card : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- **Dyadic superlevel extraction.**  If values above a base threshold carry at least half of a
positive first moment, one of `Q` dyadic superlevels has amplitude times cardinality at least
`B/(2Q)`.  This is the exact logarithmic-loss interface for Maynard's first count receiver. -/
theorem exists_dyadic_superlevel_card_mul_ge
    {ι : Type*} {s : Finset ι} {a : ι → ℝ} {v B : ℝ} {Q : ℕ}
    (hv : 0 < v) (hB : 0 < B) (hQ : 0 < Q)
    (hupper : ∀ i ∈ s, a i ≤ (((2 ^ Q : ℕ) : ℝ) * v))
    (hmass : B ≤ ∑ i ∈ s, a i)
    (hsmall : (s.card : ℝ) * v ≤ B / 2) :
    ∃ q ∈ Finset.range Q,
      B / (2 * (Q : ℝ)) ≤
        (((2 ^ q : ℕ) : ℝ) * v) *
          ((s.filter fun i => (((2 ^ q : ℕ) : ℝ) * v) ≤ a i).card : ℝ) := by
  classical
  by_contra hnone
  push Not at hnone
  have hall : ∀ q ∈ Finset.range Q,
      (((2 ^ q : ℕ) : ℝ) * v) *
          ((s.filter fun i => (((2 ^ q : ℕ) : ℝ) * v) ≤ a i).card : ℝ) <
        B / (2 * (Q : ℝ)) := hnone
  have hsumlt :
      (∑ q ∈ Finset.range Q,
        (((2 ^ q : ℕ) : ℝ) * v) *
          ((s.filter fun i => (((2 ^ q : ℕ) : ℝ) * v) ≤ a i).card : ℝ)) <
        ∑ _q ∈ Finset.range Q, B / (2 * (Q : ℝ)) := by
    exact Finset.sum_lt_sum_of_nonempty
      ⟨0, Finset.mem_range.mpr hQ⟩ hall
  have hQreal : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hconst : (∑ _q ∈ Finset.range Q, B / (2 * (Q : ℝ))) = B / 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    field_simp
  have hdecomp := sum_le_card_mul_add_sum_dyadic_superlevel hv Q hupper
  rw [hconst] at hsumlt
  linarith

/-- Cell maxima, parity separation, and dyadic layer extraction compose without losing their
literal ordinate geometry.  One globally `Δ`-spaced sequence and one superlevel set retain
`B / (4 Δ M Q)` of amplitude times cardinality. -/
theorem exists_gap_sequence_dyadic_superlevel_of_cell_sum
    {A : ℝ → ℂ} {a Δ M B P v : ℝ} {Q n : ℕ}
    (hΔ : 0 < Δ) (hM : 0 < M) (hB : 0 < B) (hv : 0 < v) (hQ : 0 < Q)
    {c : ℕ → ℝ}
    (hc : ∀ j, j < 2 * n → c j ∈
      Set.Icc (a + (j : ℝ) * Δ) (a + ((j : ℝ) + 1) * Δ))
    (hcell : B ≤ ∑ j ∈ Finset.range (2 * n), Δ * (M * ‖A (c j)‖))
    (hA : ∀ y : ℝ, ‖A y‖ ≤ P)
    (hP : P ≤ (((2 ^ Q : ℕ) : ℝ) * v))
    (hsmall : (n : ℝ) * v ≤ B / (4 * Δ * M)) :
    ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
      (∀ i, lam i + Δ ≤ lam (i + 1)) ∧
      S ⊆ Finset.range n ∧ q < Q ∧
      (∀ j < n,
        lam j ∈ Set.Icc (a + ((2 * j : ℕ) : ℝ) * Δ)
            (a + (((2 * j : ℕ) : ℝ) + 1) * Δ) ∨
        lam j ∈ Set.Icc (a + ((2 * j + 1 : ℕ) : ℝ) * Δ)
            (a + (((2 * j + 1 : ℕ) : ℝ) + 1) * Δ)) ∧
      (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * v) ≤ ‖A (lam r)‖) ∧
      B / (4 * Δ * M * (Q : ℝ)) ≤
        (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) := by
  obtain ⟨lam0, lam1, hgap0, hgap1, hmem0, hmem1, hsum⟩ :=
    exists_two_gap_sequences_of_cell_sum_bound hΔ n hc hcell
  have hscale : 0 < Δ * M := mul_pos hΔ hM
  have hsum' : B / (Δ * M) ≤
      (∑ j ∈ Finset.range n, ‖A (lam0 j)‖) +
        ∑ j ∈ Finset.range n, ‖A (lam1 j)‖ := by
    rw [div_le_iff₀ hscale]
    calc
      B ≤ (∑ j ∈ Finset.range n, Δ * (M * ‖A (lam0 j)‖)) +
          ∑ j ∈ Finset.range n, Δ * (M * ‖A (lam1 j)‖) := hsum
      _ = ((∑ j ∈ Finset.range n, ‖A (lam0 j)‖) +
          ∑ j ∈ Finset.range n, ‖A (lam1 j)‖) * (Δ * M) := by
        simp_rw [show ∀ x : ℝ, Δ * (M * x) = (Δ * M) * x by intro x; ring]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
  have hhalf : B / (2 * Δ * M) ≤ ∑ j ∈ Finset.range n, ‖A (lam0 j)‖ ∨
      B / (2 * Δ * M) ≤ ∑ j ∈ Finset.range n, ‖A (lam1 j)‖ := by
    by_contra hnone
    push Not at hnone
    have hden : B / (Δ * M) = 2 * (B / (2 * Δ * M)) := by
      field_simp
    rw [hden] at hsum'
    linarith
  rcases hhalf with hmass0 | hmass1
  · have hupper0 : ∀ i ∈ Finset.range n,
        ‖A (lam0 i)‖ ≤ (((2 ^ Q : ℕ) : ℝ) * v) := by
      intro i hi
      exact (hA (lam0 i)).trans hP
    have hbasePos : 0 < B / (2 * Δ * M) := by positivity
    have hsmall0 : (Finset.range n).card * v ≤ (B / (2 * Δ * M)) / 2 := by
      simp only [Finset.card_range]
      norm_cast
      convert hsmall using 1 <;> field_simp <;> ring
    obtain ⟨q, hq, hlevel⟩ := exists_dyadic_superlevel_card_mul_ge
      hv hbasePos hQ hupper0 hmass0 hsmall0
    let S := (Finset.range n).filter fun i =>
      (((2 ^ q : ℕ) : ℝ) * v) ≤ ‖A (lam0 i)‖
    refine ⟨lam0, S, q, hgap0, Finset.filter_subset _ _,
      Finset.mem_range.mp hq, ?_, ?_, ?_⟩
    · intro j hj
      exact Or.inl (hmem0 j hj)
    · intro r hr
      exact (Finset.mem_filter.mp hr).2
    · dsimp only [S]
      convert hlevel using 1 <;> field_simp <;> ring
  · have hupper1 : ∀ i ∈ Finset.range n,
        ‖A (lam1 i)‖ ≤ (((2 ^ Q : ℕ) : ℝ) * v) := by
      intro i hi
      exact (hA (lam1 i)).trans hP
    have hbasePos : 0 < B / (2 * Δ * M) := by positivity
    have hsmall1 : (Finset.range n).card * v ≤ (B / (2 * Δ * M)) / 2 := by
      simp only [Finset.card_range]
      norm_cast
      convert hsmall using 1 <;> field_simp <;> ring
    obtain ⟨q, hq, hlevel⟩ := exists_dyadic_superlevel_card_mul_ge
      hv hbasePos hQ hupper1 hmass1 hsmall1
    let S := (Finset.range n).filter fun i =>
      (((2 ^ q : ℕ) : ℝ) * v) ≤ ‖A (lam1 i)‖
    refine ⟨lam1, S, q, hgap1, Finset.filter_subset _ _,
      Finset.mem_range.mp hq, ?_, ?_, ?_⟩
    · intro j hj
      exact Or.inr (hmem1 j hj)
    · intro r hr
      exact (Finset.mem_filter.mp hr).2
    · dsimp only [S]
      convert hlevel using 1 <;> field_simp <;> ring

/-- **Unconditional layer dichotomy.** A signed cell first moment is carried either by the base
amplitude layer or by one dyadic superlevel. No high-amplitude conclusion is possible without
explicitly retaining this base branch. -/
theorem base_layer_or_exists_gap_sequence_dyadic_superlevel_of_cell_sum
    {A : ℝ → ℂ} {a Δ M B P v : ℝ} {Q n : ℕ}
    (hΔ : 0 < Δ) (hM : 0 < M) (hB : 0 < B) (hv : 0 < v) (hQ : 0 < Q)
    {c : ℕ → ℝ}
    (hc : ∀ j, j < 2 * n → c j ∈
      Set.Icc (a + (j : ℝ) * Δ) (a + ((j : ℝ) + 1) * Δ))
    (hcell : B ≤ ∑ j ∈ Finset.range (2 * n), Δ * (M * ‖A (c j)‖))
    (hA : ∀ y : ℝ, ‖A y‖ ≤ P)
    (hP : P ≤ (((2 ^ Q : ℕ) : ℝ) * v)) :
    B / (4 * Δ * M) ≤ (n : ℝ) * v ∨
      ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
        (∀ i, lam i + Δ ≤ lam (i + 1)) ∧
        S ⊆ Finset.range n ∧ q < Q ∧
        (∀ j < n,
          lam j ∈ Set.Icc (a + ((2 * j : ℕ) : ℝ) * Δ)
              (a + (((2 * j : ℕ) : ℝ) + 1) * Δ) ∨
          lam j ∈ Set.Icc (a + ((2 * j + 1 : ℕ) : ℝ) * Δ)
              (a + (((2 * j + 1 : ℕ) : ℝ) + 1) * Δ)) ∧
        (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * v) ≤ ‖A (lam r)‖) ∧
        B / (4 * Δ * M * (Q : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) := by
  by_cases hbase : B / (4 * Δ * M) ≤ (n : ℝ) * v
  · exact Or.inl hbase
  · right
    apply exists_gap_sequence_dyadic_superlevel_of_cell_sum
      hΔ hM hB hv hQ hc hcell hA hP
    exact le_of_not_ge hbase

/-- The base branch has exact Route-T phase exponent
`T * (T^mu)^(alpha-1) = T^(1-mu(1-alpha))`. -/
theorem routeT_base_layer_phase_identity
    {T mu alpha : ℝ} (hT : 0 < T) :
    T * (T ^ mu) ^ (alpha - 1) =
      T ^ (1 - mu * (1 - alpha)) := by
  calc
    T * (T ^ mu) ^ (alpha - 1) =
        T ^ (1 : ℝ) * T ^ (mu * (alpha - 1)) := by
      rw [Real.rpow_one, Real.rpow_mul hT.le]
    _ = T ^ ((1 : ℝ) + mu * (alpha - 1)) := by
      rw [Real.rpow_add hT]
    _ = T ^ (1 - mu * (1 - alpha)) := by ring

/-- The base layer decays exactly on the positive side of the moving-reserve boundary. -/
theorem routeT_base_layer_phase_exponent_neg_iff
    {mu alpha : ℝ} :
    1 - mu * (1 - alpha) < 0 ↔ 1 < mu * (1 - alpha) := by
  constructor <;> intro h <;> linarith

/-- A large signed defect on an even-cell interval inside the common central band directly yields
a receiver-ready superlevel on one globally spaced parity sequence.  Exact pole cancellation fixes
the kernel cost at `4`, hence the explicit `B / (16 Δ Q)` output. -/
theorem exists_gap_sequence_dyadic_superlevel_of_adjacent_defect_central
    (L X k : ℕ) (T0 t : ℝ) {N H R a Δ B v : ℝ} {Q n : ℕ}
    (hX : 1 ≤ X) (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hΔ : 0 < Δ) (hB : 0 < B) (hv : 0 < v) (hQ : 0 < Q)
    (hband : ∀ y ∈ Set.Icc a (a + ((2 * n : ℕ) : ℝ) * Δ),
      |y| ≤ N / (2 * R))
    (hdefect : B ≤ ‖∫ y in a..(a + ((2 * n : ℕ) : ℝ) * Δ),
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((1 : ℂ) + (y : ℝ) * Complex.I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖)
    (hP : heathBrownWindowRelevantFixedPolylogBound L X k N 1 ≤
      (((2 ^ Q : ℕ) : ℝ) * v))
    (hsmall : (n : ℝ) * v ≤ B / (16 * Δ)) :
    ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
      (∀ i, lam i + Δ ≤ lam (i + 1)) ∧
      S ⊆ Finset.range n ∧ q < Q ∧
      (∀ j < n,
        lam j ∈ Set.Icc (a + ((2 * j : ℕ) : ℝ) * Δ)
            (a + (((2 * j : ℕ) : ℝ) + 1) * Δ) ∨
        lam j ∈ Set.Icc (a + ((2 * j + 1 : ℕ) : ℝ) * Δ)
            (a + (((2 * j + 1 : ℕ) : ℝ) + 1) * Δ)) ∧
      (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * v) ≤
        ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
      B / (16 * Δ * (Q : ℝ)) ≤
        (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) := by
  obtain ⟨c, hc, hcellUpper⟩ :=
    exists_cell_max_norm_intervalIntegral_adjacent_defect_central_le
      L X k T0 t hN hH hR hHR hΔ (2 * n) hband
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  have hcell : B ≤ ∑ j ∈ Finset.range (2 * n), Δ * (4 * ‖A (c j)‖) := by
    exact hdefect.trans (by simpa only [A] using hcellUpper)
  have hA : ∀ y : ℝ, ‖A y‖ ≤
      heathBrownWindowRelevantFixedPolylogBound L X k N 1 := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t N 1 y hN (by norm_num)
  have hsmall' : (n : ℝ) * v ≤ B / (4 * Δ * 4) := by
    convert hsmall using 1 <;> ring
  obtain ⟨lam, S, q, hgap, hS, hq, hmem, hlarge, hmass⟩ :=
    exists_gap_sequence_dyadic_superlevel_of_cell_sum
      hΔ (by norm_num : (0 : ℝ) < 4) hB hv hQ hc hcell hA hP hsmall'
  refine ⟨lam, S, q, hgap, hS, hq, hmem, ?_, ?_⟩
  · intro r hr
    simpa only [A] using hlarge r hr
  · convert hmass using 1 <;> ring

/-- The same receiver-ready extraction on an outer interval.  Quadratic Mellin decay contributes
the exact kernel cost `65 * C * (N/R)² / U²`; no further loss occurs in cell or amplitude
selection. -/
theorem exists_gap_sequence_dyadic_superlevel_of_adjacent_defect_tail :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (L X k : ℕ) (T0 t : ℝ) {N H R U a Δ B v : ℝ} {Q n : ℕ},
        1 ≤ X → 0 < N → 0 < H → 0 < R → H ≤ R →
        R ≤ 2 * H → R ≤ N → 0 < U → 0 < Δ →
        0 < B → 0 < v → 0 < Q →
        (∀ y ∈ Set.Icc a (a + ((2 * n : ℕ) : ℝ) * Δ), U ≤ |y|) →
        B ≤ ‖∫ y in a..(a + ((2 * n : ℕ) : ℝ) * Δ),
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((1 : ℂ) + (y : ℝ) * Complex.I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * Complex.I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * Complex.I))‖ →
        heathBrownWindowRelevantFixedPolylogBound L X k N 1 ≤
          (((2 ^ Q : ℕ) : ℝ) * v) →
        (n : ℝ) * v ≤
          B / (4 * Δ * (65 * C * (N / R) ^ 2 / U ^ 2)) →
        ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
          (∀ i, lam i + Δ ≤ lam (i + 1)) ∧
          S ⊆ Finset.range n ∧ q < Q ∧
          (∀ j < n,
            lam j ∈ Set.Icc (a + ((2 * j : ℕ) : ℝ) * Δ)
                (a + (((2 * j : ℕ) : ℝ) + 1) * Δ) ∨
            lam j ∈ Set.Icc (a + ((2 * j + 1 : ℕ) : ℝ) * Δ)
                (a + (((2 * j + 1 : ℕ) : ℝ) + 1) * Δ)) ∧
          (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * v) ≤
            ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
          B / (4 * Δ * (65 * C * (N / R) ^ 2 / U ^ 2) * (Q : ℝ)) ≤
            (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) := by
  obtain ⟨C, hC, htailCell⟩ :=
    exists_cell_max_norm_intervalIntegral_adjacent_defect_tail_le
  refine ⟨C, hC, ?_⟩
  intro L X k T0 t N H R U a Δ B v Q n hX hN hH hR hHR hRH hRN hU hΔ
    hB hv hQ hband hdefect hP hsmall
  obtain ⟨c, hc, hcellUpper⟩ :=
    htailCell L X k T0 t hN hH hR hHR hRH hRN hU hΔ (2 * n) hband
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let M : ℝ := 65 * C * (N / R) ^ 2 / U ^ 2
  have hM : 0 < M := by
    dsimp only [M]
    have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
    positivity
  have hcell : B ≤ ∑ j ∈ Finset.range (2 * n), Δ * (M * ‖A (c j)‖) := by
    exact hdefect.trans (by simpa only [A, M] using hcellUpper)
  have hA : ∀ y : ℝ, ‖A y‖ ≤
      heathBrownWindowRelevantFixedPolylogBound L X k N 1 := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t N 1 y hN (by norm_num)
  obtain ⟨lam, S, q, hgap, hS, hq, hmem, hlarge, hmass⟩ :=
    exists_gap_sequence_dyadic_superlevel_of_cell_sum
      hΔ hM hB hv hQ hc hcell hA hP (by simpa only [M] using hsmall)
  refine ⟨lam, S, q, hgap, hS, hq, hmem, ?_, ?_⟩
  · intro r hr
    simpa only [A] using hlarge r hr
  · simpa only [M] using hmass

/-- Every interval of length at least two admits an exact even-cell partition with cell width in
`[1,2]`.  Choosing the width after the cell count avoids endpoint trimming and therefore preserves
the full signed integral. -/
theorem exists_even_cells_unit_two_of_two_le_length
    {a b : ℝ} (h : a + 2 ≤ b) :
    ∃ n : ℕ, ∃ Δ : ℝ,
      0 < n ∧ 1 ≤ Δ ∧ Δ ≤ 2 ∧
        b = a + ((2 * n : ℕ) : ℝ) * Δ := by
  let L : ℝ := b - a
  let n : ℕ := ⌊L / 2⌋₊
  have hL : 2 ≤ L := by dsimp only [L]; linarith
  have hL0 : 0 ≤ L / 2 := by linarith
  have hn : 1 ≤ n := by
    dsimp only [n]
    apply Nat.le_floor
    norm_num
    linarith
  have hnpos : 0 < n := by omega
  have hnle : (n : ℝ) ≤ L / 2 := by
    dsimp only [n]
    exact Nat.floor_le hL0
  have hLlt : L / 2 < (n : ℝ) + 1 := by
    dsimp only [n]
    exact Nat.lt_floor_add_one _
  let Δ : ℝ := L / (2 * (n : ℝ))
  have hden : 0 < 2 * (n : ℝ) := by positivity
  have hΔlo : 1 ≤ Δ := by
    dsimp only [Δ]
    rw [le_div_iff₀ hden]
    linarith
  have hΔhi : Δ ≤ 2 := by
    dsimp only [Δ]
    rw [div_le_iff₀ hden]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨n, Δ, hnpos, hΔlo, hΔhi, ?_⟩
  dsimp only [Δ, L]
  push_cast
  field_simp
  ring

end RHTower.Sieve
