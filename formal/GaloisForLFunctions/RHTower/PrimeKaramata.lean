import GaloisForLFunctions.RHTower.PrimeKaramataBody

/-!
# The prime Karamata law

`W_X = ∑_{p ≤ X}(log p)p^{−α}L(p) ∼ X^{1−α}L(X)/(1−α)`  for `0 ≤ α < 1` and `L` slowly varying.

This is the card's `(9)`.  Everything is now assembled: the head is negligible by Potter, the body
is bracketed by the two Darboux sums of `v ↦ v^{−α}` through the shell sandwich, and the Darboux
gap telescopes to `(v₀^{−α} − 1)·(1−v₀)/N`.
-/

open MeasureTheory Filter Topology HTGeometry

namespace RHTower

noncomputable section

/-- The head is monotone in the cutoff. -/
theorem primeLogSum_head_mono {α : ℝ} {L : ℝ → ℝ} (hL : IsSlowlyVarying L) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    primeLogSum (rvPrimeWeight α L) 0 a ≤ primeLogSum (rvPrimeWeight α L) 0 b := by
  have hfl1 : ⌊(0 : ℝ)⌋₊ ≤ ⌊a⌋₊ := by simp
  have hfl2 : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have hadd := primeLogSum_add (f := rvPrimeWeight α L) hfl1 hfl2
  have hnn : 0 ≤ primeLogSum (rvPrimeWeight α L) a b := by
    refine primeLogSum_nonneg ha fun p _ h1 _ => ?_
    exact rvPrimeWeight_nonneg hL (lt_of_le_of_lt ha h1)
  linarith

/-- The Darboux sums differ by the telescoped endpoint gap. -/
theorem karamata_darboux_gap {α v₀ : ℝ} {N : ℕ} (hN : 0 < N) :
    (∑ j ∈ Finset.range N, karamataNode v₀ N j ^ (-α))
      - ∑ j ∈ Finset.range N, karamataNode v₀ N (j + 1) ^ (-α)
      = v₀ ^ (-α) - 1 := by
  rw [← Finset.sum_sub_distrib]
  have := Finset.sum_range_sub' (fun j : ℕ => karamataNode v₀ N j ^ (-α)) N
  rw [this, karamataNode_zero, karamataNode_last hN, Real.one_rpow]

/-- **The prime Karamata law**, the card's `(9)`. -/
theorem tendsto_rvWeightSum {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) :
    Tendsto (fun X : ℝ => rvWeightSum α L X / (X ^ (1 - α) * L X)) atTop
      (𝓝 (1 / (1 - α))) := by
  have hα' : (0 : ℝ) < 1 - α := by linarith
  set A : ℝ := 1 / (1 - α) with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  rw [Metric.tendsto_nhds]
  intro η hη
  -- the head threshold
  obtain ⟨w, hw0, hw1, hwbound⟩ := exists_karamata_head_bound hα0 hα1 hL
    (show (0 : ℝ) < η / 4 by linarith)
  -- the integral threshold
  obtain ⟨u, hu0, hu1, hu⟩ : ∃ u : ℝ, 0 < u ∧ u < 1 ∧ u ^ (1 - α) * A ≤ η / 8 := by
    have hc : ContinuousAt (fun v : ℝ => v ^ (1 - α)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr hα'.le)
    have h0 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rw [Real.zero_rpow hα'.ne'] at h0
    have hlim := h0.mul_const A
    rw [zero_mul] at hlim
    have hev := hlim.eventually_le_const (show (0 : ℝ) < η / 8 by linarith)
    obtain ⟨v, ⟨hv1, hv2⟩⟩ := ((hev.and self_mem_nhdsWithin).and
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)).exists
    exact ⟨v, hv1.2, hv2, hv1.1⟩
  set v₀ : ℝ := min w u with hv₀def
  have hv₀0 : 0 < v₀ := lt_min hw0 hu0
  have hv₀1 : v₀ < 1 := lt_of_le_of_lt (min_le_left _ _) hw1
  have hv₀w : v₀ ≤ w := min_le_left _ _
  have hv₀u : v₀ ≤ u := min_le_right _ _
  -- the integral deficit at `v₀`
  have hIdef : v₀ ^ (1 - α) * A ≤ η / 8 := by
    have hmono : v₀ ^ (1 - α) ≤ u ^ (1 - α) :=
      Real.rpow_le_rpow hv₀0.le hv₀u hα'.le
    nlinarith [hmono, hA0]
  set P : ℝ := v₀ ^ (-α) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hv₀0 _
  -- the number of blocks
  obtain ⟨N, hN0, hNbound⟩ : ∃ N : ℕ, 0 < N ∧ P * ((1 - v₀) / N) ≤ η / 8 := by
    obtain ⟨M, hM⟩ := exists_nat_gt (P * (1 - v₀) / (η / 8))
    refine ⟨M + 1, Nat.succ_pos _, ?_⟩
    have hMR : (0 : ℝ) < ((M : ℝ) + 1) := by positivity
    have hM' : P * (1 - v₀) / (η / 8) < (M : ℝ) + 1 := by linarith [hM]
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < η / 8)] at hM'
    have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ hMR]
    nlinarith [hM']
  set h : ℝ := (1 - v₀) / N with hh
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hh0 : 0 < h := by
    rw [hh]
    have : (0 : ℝ) < 1 - v₀ := by linarith
    positivity
  have hPh : P * h ≤ η / 8 := hNbound
  -- the Darboux data
  set Sup : ℝ := ∑ j ∈ Finset.range N, karamataNode v₀ N j ^ (-α) with hSup
  set Slow : ℝ := ∑ j ∈ Finset.range N, karamataNode v₀ N (j + 1) ^ (-α) with hSlow
  have hgap : Sup - Slow = P - 1 := karamata_darboux_gap hN0
  have hnodeP : ∀ j : ℕ, karamataNode v₀ N j ^ (-α) ≤ P := by
    intro j
    have h1 : v₀ ≤ karamataNode v₀ N j := by
      have := karamataNode_mono (v₀ := v₀) (N := N) hv₀1 (Nat.zero_le j)
      rwa [karamataNode_zero] at this
    exact Real.rpow_le_rpow_of_nonpos hv₀0 h1 (by linarith)
  have hSupbound : Sup ≤ (N : ℝ) * P := by
    calc Sup ≤ ∑ _j ∈ Finset.range N, P := Finset.sum_le_sum fun j _ => hnodeP j
      _ = (N : ℝ) * P := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hSlowbound : Slow ≤ (N : ℝ) * P := by
    calc Slow ≤ ∑ _j ∈ Finset.range N, P := Finset.sum_le_sum fun j _ => hnodeP (j + 1)
      _ = (N : ℝ) * P := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hSlow0 : 0 ≤ Slow := by
    refine Finset.sum_nonneg fun j _ => ?_
    exact Real.rpow_nonneg (karamataNode_pos hv₀0 hv₀1 N (j + 1)).le _
  obtain ⟨hdarL, hdarU⟩ := rpow_darboux hα0 hv₀0 hv₀1 hN0
  have hInt : (∫ v in v₀..(1 : ℝ), v ^ (-α)) = (1 - v₀ ^ (1 - α)) * A := by
    rw [integral_rpow_neg_unit hα1 hv₀0, hA]
    ring
  have hnodes : ∀ j : ℕ, karamataNode v₀ N j = v₀ + (j : ℝ) * h := fun j => rfl
  have hUp : Sup * h ≤ A + P * h := by
    have h1 : Slow * h ≤ (1 - v₀ ^ (1 - α)) * A := by
      rw [← hInt]
      simpa [hSlow, hnodes, hh] using hdarL
    have h2 : (1 - v₀ ^ (1 - α)) * A ≤ A := by
      have : (0 : ℝ) ≤ v₀ ^ (1 - α) := Real.rpow_nonneg hv₀0.le _
      nlinarith [hA0]
    have h3 : Sup * h = Slow * h + (P - 1) * h := by
      have hs : Sup = Slow + (P - 1) := by linarith [hgap]
      rw [hs]; ring
    nlinarith [h1, h2, h3, hh0]
  have hLo : (1 - v₀ ^ (1 - α)) * A - P * h ≤ Slow * h := by
    have h1 : (1 - v₀ ^ (1 - α)) * A ≤ Sup * h := by
      rw [← hInt]
      simpa [hSup, hnodes, hh] using hdarU
    have h3 : Sup * h = Slow * h + (P - 1) * h := by
      have hs : Sup = Slow + (P - 1) := by linarith [hgap]
      rw [hs]; ring
    nlinarith [h1, h3, hh0]
  -- the tilt tolerance
  obtain ⟨ε, hε0, hε1, hεbound⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ε * (A + P * h + 4 * (N : ℝ) * P) ≤ η / 8 := by
    set D : ℝ := A + P * h + 4 * (N : ℝ) * P with hD
    have hD0 : 0 < D := by rw [hD]; positivity
    refine ⟨min (1 / 2) ((η / 8) / D), lt_min (by norm_num) (by positivity),
      lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_⟩
    have hle : min (1 / 2) ((η / 8) / D) ≤ (η / 8) / D := min_le_right _ _
    calc min (1 / 2) ((η / 8) / D) * D ≤ ((η / 8) / D) * D :=
          mul_le_mul_of_nonneg_right hle hD0.le
      _ = η / 8 := by field_simp
  -- put it together
  have hshells := karamata_shells_bounds hα0 hL hv₀0 hv₀1 hN0 hε0 hε1
  filter_upwards [hshells, hwbound, eventually_gt_atTop (0 : ℝ)] with X hXsh hXhead hX0
  have hLX : 0 < L X := hL.pos _ hX0
  have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
  have hden : (0 : ℝ) < X ^ (1 - α) * L X := by positivity
  have hheadv : primeLogSum (rvPrimeWeight α L) 0 (v₀ * X)
      ≤ (η / 4) * (X ^ (1 - α) * L X) := by
    refine le_trans (primeLogSum_head_mono hL (by positivity) ?_) hXhead
    nlinarith [hv₀w, hX0.le]
  have hdecomp := rvWeightSum_decomp (α := α) (L := L) hv₀0 hv₀1 hN0 hX0
  have hheadnn : 0 ≤ primeLogSum (rvPrimeWeight α L) 0 (v₀ * X) := by
    refine primeLogSum_nonneg le_rfl fun p _ h1 _ => ?_
    exact rvPrimeWeight_nonneg hL (lt_of_le_of_lt le_rfl h1)
  -- the two coefficient bounds
  have hSup0 : 0 ≤ Sup := by
    refine Finset.sum_nonneg fun j _ => ?_
    exact Real.rpow_nonneg (karamataNode_pos hv₀0 hv₀1 N j).le _
  have hcoeffUp : (∑ j ∈ Finset.range N, karamataNode v₀ N j ^ (-α) * (1 + ε) * (h + 2 * ε))
      ≤ A + η / 2 := by
    have hid : (∑ j ∈ Finset.range N, karamataNode v₀ N j ^ (-α) * (1 + ε) * (h + 2 * ε))
        = (1 + ε) * (Sup * h) + (2 * ε) * ((1 + ε) * Sup) := by
      have hsm : (∑ j ∈ Finset.range N, karamataNode v₀ N j ^ (-α) * (1 + ε) * (h + 2 * ε))
          = Sup * ((1 + ε) * (h + 2 * ε)) := by
        rw [hSup, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsm]; ring
    rw [hid]
    have b1 : (1 + ε) * (Sup * h) ≤ (1 + ε) * (A + P * h) :=
      mul_le_mul_of_nonneg_left hUp (by linarith)
    have b2 : (2 * ε) * ((1 + ε) * Sup) ≤ (2 * ε) * (2 * ((N : ℝ) * P)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      nlinarith [hSupbound, hSup0, hε1, hε0]
    have b4 : ε * (A + P * h) + (2 * ε) * (2 * ((N : ℝ) * P)) ≤ η / 8 := by
      nlinarith [hεbound]
    nlinarith [b1, b2, b4, hPh, hη]
  have hcoeffLo : A - η / 2 ≤
      (∑ j ∈ Finset.range N, karamataNode v₀ N (j + 1) ^ (-α) * (1 - ε) * (h - 2 * ε)) := by
    have hid : (∑ j ∈ Finset.range N, karamataNode v₀ N (j + 1) ^ (-α) * (1 - ε) * (h - 2 * ε))
        = (1 - ε) * (Slow * h) - (2 * ε) * ((1 - ε) * Slow) := by
      have hsm : (∑ j ∈ Finset.range N, karamataNode v₀ N (j + 1) ^ (-α) * (1 - ε) * (h - 2 * ε))
          = Slow * ((1 - ε) * (h - 2 * ε)) := by
        rw [hSlow, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsm]; ring
    rw [hid]
    set B : ℝ := (1 - v₀ ^ (1 - α)) * A - P * h with hB
    have hv₀pow : (0 : ℝ) ≤ v₀ ^ (1 - α) := Real.rpow_nonneg hv₀0.le _
    have hBle : B ≤ A := by
      rw [hB]
      nlinarith [hv₀pow, hA0, hPh, hP0, hh0]
    have hBge : A - η / 4 ≤ B := by
      rw [hB]
      nlinarith [hIdef, hPh]
    have b1 : (1 - ε) * B ≤ (1 - ε) * (Slow * h) :=
      mul_le_mul_of_nonneg_left hLo (by linarith)
    have b2 : (2 * ε) * ((1 - ε) * Slow) ≤ (2 * ε) * ((N : ℝ) * P) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      nlinarith [hSlowbound, hSlow0, hε1, hε0]
    have b3 : B - ε * A ≤ (1 - ε) * B := by nlinarith [hBle, hε0.le]
    have b4 : ε * A + (2 * ε) * ((N : ℝ) * P) ≤ η / 8 := by
      nlinarith [hεbound, hP0, hh0, hA0]
    nlinarith [b1, b2, b3, b4, hBge, hη]
  have hupper : rvWeightSum α L X ≤ (A + 3 * η / 4) * (X ^ (1 - α) * L X) := by
    have h1 := hXsh.2
    have h2 : (∑ j ∈ Finset.range N, karamataNode v₀ N j ^ (-α) * (1 + ε)
          * ((1 - v₀) / N + 2 * ε)) * (X ^ (1 - α) * L X)
        ≤ (A + η / 2) * (X ^ (1 - α) * L X) := by
      refine mul_le_mul_of_nonneg_right ?_ hden.le
      rw [← hh]
      exact hcoeffUp
    rw [hdecomp]
    nlinarith [hheadv, h1, h2, hden]
  have hlower : (A - η / 2) * (X ^ (1 - α) * L X) ≤ rvWeightSum α L X := by
    have h1 := hXsh.1
    have h2 : (A - η / 2) * (X ^ (1 - α) * L X)
        ≤ (∑ j ∈ Finset.range N, karamataNode v₀ N (j + 1) ^ (-α) * (1 - ε)
            * ((1 - v₀) / N - 2 * ε)) * (X ^ (1 - α) * L X) := by
      refine mul_le_mul_of_nonneg_right ?_ hden.le
      rw [← hh]
      exact hcoeffLo
    rw [hdecomp]
    linarith [hheadnn, h1, h2]
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, ← sub_lt_iff_lt_add', lt_div_iff₀ hden]
    nlinarith [hlower, hden, hη]
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hden]
    nlinarith [hupper, hden, hη]

end

end RHTower
