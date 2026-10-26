import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AlmostEveryHeightIsNearlyWeilPositive

/-!
# Almost every zero ordinate is nearly Weil-positive

`AlmostEveryHeightIsNearlyWeilPositive` reads the negative part of the Weil form at a height `γ`
through the off-line field `Φ(γ) = Σ_q (Re q - 1/2)² / (1 + (Im q - γ)²)²` and shows that `Φ` is
small on most of every window of length `Γ^{99/100}` in Lebesgue measure. Here the heights are the
zero ordinates themselves.

**Theorem** (`exists_shortWindow_almostEvery_zeroOrdinate_nearly_positive`). For `Γ` large,
`Γ^{99/100} ≤ H ≤ Γ/8` and `η > 0`, the zero copies with ordinate in `[Γ, Γ + H]` number at least
`H log Γ / (16π)`, and all but `C H / η` of them have `Φ(Im q) ≤ η`; at each such ordinate
`Q(F₀ cos γ·) + Q(F₀ sin γ·) ≥ -4η (A + 1)² e^A N(F₀)²` for every aperture `A` and every real
`F₀ ∈ C²_c([-A, A])`. So the exceptional ordinates are a proportion `O(1/(η log Γ))`.

**Mechanism** (`exists_sum_offLineField_zeroOrdinates_le`). `Σ_{q' ∈ Z} Φ(Im q') = Σ_q δ_q² Σ_{q' ∈ Z}
(1 + (Im q - Im q')²)^{-2}`. For `q` near the window the inner sum is at most the Lorentzian mass
`O(log Γ)` and `Σ δ_q² = O(H / log Γ)`; for `q` far from it the inner sum is `O(#Z log Γ / H²)`.
Hence `Σ_{q' ∈ Z} Φ(Im q') = O(H)` while `#Z ≍ H log Γ`.
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped BigOperators Real ComplexConjugate
open Zeta23 RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.BiScaleUncertainty
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The contribution of the copy `q` to the off-line field at the ordinate of `q'`. -/
def pairWeight (q' q : XiZeroCopy) : ℝ :=
  ((q.1 : ℂ).re - 1 / 2) ^ 2 / (1 + ((q.1 : ℂ).im - (q'.1 : ℂ).im) ^ 2) ^ 2

theorem offLineField_eq_tsum_pairWeight (q' : XiZeroCopy) :
    offLineField (q'.1 : ℂ).im = ∑' q, pairWeight q' q := rfl

theorem summable_pairWeight (q' : XiZeroCopy) : Summable (pairWeight q') :=
  summable_offLineField (q'.1 : ℂ).im

/-- `Σ_{q' ∈ Z} Φ(Im q') = Σ'_q Σ_{q' ∈ Z} w(q', q)`. -/
theorem sum_offLineField_eq_tsum (Z : Finset XiZeroCopy) :
    ∑ q' ∈ Z, offLineField (q'.1 : ℂ).im = ∑' q, ∑ q' ∈ Z, pairWeight q' q := by
  simp only [offLineField_eq_tsum_pairWeight]
  exact (Summable.tsum_finsetSum fun q' _ => summable_pairWeight q').symm

private theorem lorentzMassTerm_eq_pair (q q' : XiZeroCopy) :
    lorentzMassTerm (q'.1 : ℂ).im q = 1 / (1 + ((q.1 : ℂ).im - (q'.1 : ℂ).im) ^ 2) := by
  unfold lorentzMassTerm
  rw [show ((q'.1 : ℂ).im - (q.1 : ℂ).im) ^ 2 = ((q.1 : ℂ).im - (q'.1 : ℂ).im) ^ 2 by ring]

/-- A copy near the window: `Σ_{q' ∈ Z} w(q', q) ≤ δ_q² · ℒ(Im q)`, with `ℒ` the Lorentzian mass. -/
theorem sum_pairWeight_le_local (Z : Finset XiZeroCopy) (q : XiZeroCopy) :
    ∑ q' ∈ Z, pairWeight q' q ≤ (foldedRe q - 1 / 2) ^ 2 * lorentzMass (q.1 : ℂ).im := by
  have hsqre : ((q.1 : ℂ).re - 1 / 2) ^ 2 = (foldedRe q - 1 / 2) ^ 2 := by
    rw [foldedRe_sub_half_eq_abs, sq_abs]
  have hpt : ∀ q' ∈ Z, pairWeight q' q ≤
      (foldedRe q - 1 / 2) ^ 2 * lorentzMassTerm (q.1 : ℂ).im q' := fun q' _ => by
    unfold pairWeight lorentzMassTerm
    rw [← hsqre, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact one_div_le_one_div_of_le (by positivity)
      (le_self_pow₀ (le_add_of_nonneg_right (sq_nonneg _)) two_ne_zero)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left ((summable_lorentzMassTerm _).sum_le_tsum _
    (fun q' _ => lorentzMassTerm_nonneg _ q')) (sq_nonneg _)

/-- A copy at distance `≥ H` from every ordinate of `Z`:
`Σ_{q' ∈ Z} w(q', q) ≤ (1/(4H²)) Σ_{q' ∈ Z} ℓ(Im q', q)`. -/
theorem sum_pairWeight_le_remote {H : ℝ} (hH : 0 < H) (Z : Finset XiZeroCopy) (q : XiZeroCopy)
    (hfar : ∀ q' ∈ Z, H ≤ |(q.1 : ℂ).im - (q'.1 : ℂ).im|) :
    ∑ q' ∈ Z, pairWeight q' q ≤ (1 / (4 * H ^ 2)) * ∑ q' ∈ Z, lorentzMassTerm (q'.1 : ℂ).im q := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hδ : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ 1 / 4 := by nlinarith [hstrip.1, hstrip.2]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q' hq' => ?_
  have hl := lorentz_sq_le_of_far hH (hfar q' hq')
  rw [lorentzMassTerm_eq_pair]
  unfold pairWeight
  calc ((q.1 : ℂ).re - 1 / 2) ^ 2 / (1 + ((q.1 : ℂ).im - (q'.1 : ℂ).im) ^ 2) ^ 2
      = ((q.1 : ℂ).re - 1 / 2) ^ 2 * (1 / (1 + ((q.1 : ℂ).im - (q'.1 : ℂ).im) ^ 2) ^ 2) := by
        ring
    _ ≤ (1 / 4) * ((1 / H ^ 2) * (1 / (1 + ((q.1 : ℂ).im - (q'.1 : ℂ).im) ^ 2))) :=
        mul_le_mul hδ hl (by positivity) (by norm_num)
    _ = _ := by ring

/-- **Double counting.** For finite `Z` and `G` with every copy outside `G` at distance `≥ H` from
every ordinate of `Z`: `Σ_{q' ∈ Z} Φ(Im q') ≤ Σ_{q ∈ G} δ_q² ℒ(Im q) + (1/(4H²)) Σ_{q' ∈ Z} ℒ(Im q')`. -/
theorem sum_offLineField_le_split {H : ℝ} (hH : 0 < H) (Z G : Finset XiZeroCopy)
    (hfar : ∀ q, q ∉ G → ∀ q' ∈ Z, H ≤ |(q.1 : ℂ).im - (q'.1 : ℂ).im|) :
    ∑ q' ∈ Z, offLineField (q'.1 : ℂ).im ≤
      (∑ q ∈ G, (foldedRe q - 1 / 2) ^ 2 * lorentzMass (q.1 : ℂ).im) +
        (1 / (4 * H ^ 2)) * ∑ q' ∈ Z, lorentzMass (q'.1 : ℂ).im := by
  classical
  have hFM : ∀ q, ∑ q' ∈ Z, pairWeight q' q ≤
      (if q ∈ G then (foldedRe q - 1 / 2) ^ 2 * lorentzMass (q.1 : ℂ).im else 0) +
        (1 / (4 * H ^ 2)) * ∑ q' ∈ Z, lorentzMassTerm (q'.1 : ℂ).im q := by
    intro q
    have hrest : 0 ≤ (1 / (4 * H ^ 2)) * ∑ q' ∈ Z, lorentzMassTerm (q'.1 : ℂ).im q :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun q' _ => lorentzMassTerm_nonneg _ _)
    by_cases hq : q ∈ G
    · rw [if_pos hq]
      linarith [sum_pairWeight_le_local Z q]
    · rw [if_neg hq, zero_add]
      exact sum_pairWeight_le_remote hH Z q (hfar q hq)
  have hsumF : Summable fun q => ∑ q' ∈ Z, pairWeight q' q :=
    summable_sum fun q' _ => summable_pairWeight q'
  have hsum_ite : Summable fun q : XiZeroCopy =>
      (if q ∈ G then (foldedRe q - 1 / 2) ^ 2 * lorentzMass (q.1 : ℂ).im else 0) :=
    summable_of_ne_finset_zero (s := G) fun q hq => if_neg hq
  have hsum_lor : Summable fun q : XiZeroCopy =>
      (1 / (4 * H ^ 2)) * ∑ q' ∈ Z, lorentzMassTerm (q'.1 : ℂ).im q :=
    (summable_sum fun q' _ => summable_lorentzMassTerm (q'.1 : ℂ).im).mul_left _
  have e1 : ∑' q : XiZeroCopy,
      (if q ∈ G then (foldedRe q - 1 / 2) ^ 2 * lorentzMass (q.1 : ℂ).im else 0) =
        ∑ q ∈ G, (foldedRe q - 1 / 2) ^ 2 * lorentzMass (q.1 : ℂ).im := by
    rw [tsum_eq_sum (s := G) fun q hq => if_neg hq]
    exact Finset.sum_congr rfl fun q hq => if_pos hq
  have e2 : ∑' q : XiZeroCopy, (1 / (4 * H ^ 2)) * ∑ q' ∈ Z, lorentzMassTerm (q'.1 : ℂ).im q =
      (1 / (4 * H ^ 2)) * ∑ q' ∈ Z, lorentzMass (q'.1 : ℂ).im := by
    have hswap2 : ∑' q : XiZeroCopy, ∑ q' ∈ Z, lorentzMassTerm (q'.1 : ℂ).im q =
        ∑ q' ∈ Z, ∑' q : XiZeroCopy, lorentzMassTerm (q'.1 : ℂ).im q :=
      Summable.tsum_finsetSum fun (q' : XiZeroCopy) _ => summable_lorentzMassTerm (q'.1 : ℂ).im
    rw [tsum_mul_left, hswap2]
    rfl
  rw [sum_offLineField_eq_tsum]
  calc ∑' q, ∑ q' ∈ Z, pairWeight q' q
      ≤ ∑' q : XiZeroCopy,
          ((if q ∈ G then (foldedRe q - 1 / 2) ^ 2 * lorentzMass (q.1 : ℂ).im else 0) +
            (1 / (4 * H ^ 2)) * ∑ q' ∈ Z, lorentzMassTerm (q'.1 : ℂ).im q) :=
        Summable.tsum_le_tsum hFM hsumF (hsum_ite.add hsum_lor)
    _ = _ := by rw [hsum_ite.tsum_add hsum_lor, e1, e2]

/-- **The off-line field summed over the zero ordinates of a short window is `O(H)`.** -/
theorem exists_sum_offLineField_zeroOrdinates_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Γ₀ : ℝ, 64 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ H : ℝ, Γ ^ (99 / 100 : ℝ) ≤ H → H ≤ Γ / 8 →
        ∀ Z : Finset XiZeroCopy, (∀ q ∈ Z, Γ ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + H) →
          ∑ q' ∈ Z, offLineField (q'.1 : ℂ).im ≤ C * H := by
  obtain ⟨C₃, hC₃, Γ₁, hΓ₁, hsq⟩ := exists_window_sum_sq_depth_le
  obtain ⟨Cw, hCw, T₀w, -, hwinle⟩ := exists_xiZeroCount_window_le
  obtain ⟨K₁, hK₁1, hK₁⟩ := exists_one_add_log_pow_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 2)
  set c : ℝ := |xiLineTwoLogDerivConstant| with hc
  have hc0 : 0 ≤ c := abs_nonneg _
  obtain ⟨Γ₀, hΓ₀1, hΓ₀T, hΓ₀C, hΓ₀K⟩ : ∃ Γ₀ : ℝ, Γ₁ ≤ Γ₀ ∧ 2 * T₀w + 2 ≤ Γ₀ ∧
      (8 * Cw + 8) ^ (2 : ℕ) ≤ Γ₀ ∧ (6 * (c + 3) * K₁) ^ (2 : ℕ) ≤ Γ₀ := by
    refine ⟨max Γ₁ (max (2 * T₀w + 2) (max ((8 * Cw + 8) ^ (2 : ℕ))
      ((6 * (c + 3) * K₁) ^ (2 : ℕ)))), le_max_left _ _, ?_, ?_, ?_⟩
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    · exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨8 * (c + 3) * C₃ + 1, by positivity, Γ₀, hΓ₁.trans hΓ₀1,
    fun Γ hΓ H hH1 hH2 Z hZ => ?_⟩
  classical
  have hΓ1' : Γ₁ ≤ Γ := hΓ₀1.trans hΓ
  have hΓ64 : 64 ≤ Γ := hΓ₁.trans hΓ1'
  have hΓ0 : 0 < Γ := by linarith
  have hΓ1 : 1 ≤ Γ := by linarith
  set L : ℝ := Real.log Γ with hLdef
  have hL : 1 ≤ L := by
    have : Real.exp 1 ≤ Γ := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) this
    rwa [Real.log_exp] at this
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hΓ0 _) hH1
  have hsqrtH : Γ ^ (1 / 2 : ℝ) ≤ H :=
    (Real.rpow_le_rpow_of_exponent_le hΓ1 (by norm_num)).trans hH1
  have hHC : 8 * Cw + 8 ≤ H := by
    refine le_trans ?_ hsqrtH
    have := Real.rpow_le_rpow (by positivity) (hΓ₀C.trans hΓ) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at this
  have hlog2 : Real.log (2 * Γ + 4) ≤ 3 * L := by
    have hΓsq : 16 * Γ ≤ Γ ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) hΓ0.le
    have hΓ3 : Γ ^ 2 ≤ Γ ^ 3 := pow_le_pow_right₀ hΓ1 (by norm_num)
    have : Real.log (2 * Γ + 4) ≤ Real.log (Γ ^ 3) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hmass : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * Γ → lorentzMass t ≤ 8 * (c + 3) * L := by
    intro t ht0 ht
    refine (lorentzMass_le_log t).trans ?_
    have hle : |t| + 4 ≤ 2 * Γ + 4 := by rw [abs_of_nonneg ht0]; linarith
    have := Real.log_le_log (by positivity) hle
    have hcl : xiLineTwoLogDerivConstant ≤ c := le_abs_self _
    nlinarith
  have hS_fin : ({q : XiZeroCopy | Γ - H ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + 2 * H}).Finite :=
    (finite_xiOrdinateWindow (Γ + 2 * H) 0).subset fun q hq => by
      rw [mem_xiOrdinateWindow_iff, sub_zero, abs_le]
      exact ⟨by linarith [hq.1], hq.2⟩
  obtain ⟨G_loc, hmem⟩ : ∃ G_loc : Finset XiZeroCopy,
      ∀ q : XiZeroCopy, q ∈ G_loc ↔ Γ - H ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + 2 * H :=
    ⟨hS_fin.toFinset, fun _ => hS_fin.mem_toFinset⟩
  have hsumG := hsq Γ hΓ1' H hH1 hH2 G_loc fun q hq => (hmem q).mp hq
  have hcardZ : (Z.card : ℝ) ≤ 3 * H * L :=
    window_card_le hCw hwinle (hΓ₀T.trans hΓ) hH0 hH2 hHC Z fun q hq =>
      ⟨by linarith [(hZ q hq).1], by linarith [(hZ q hq).2]⟩
  have hfar : ∀ q, q ∉ G_loc → ∀ q' ∈ Z, H ≤ |(q.1 : ℂ).im - (q'.1 : ℂ).im| := by
    intro q hq q' hq'
    have hq'' := hZ q' hq'
    rw [hmem, not_and_or] at hq
    rcases hq with h | h
    · rw [abs_sub_comm, abs_of_nonneg (by linarith [hq''.1, not_le.mp h])]
      linarith [hq''.1, not_le.mp h]
    · rw [abs_of_nonneg (by linarith [hq''.2, not_le.mp h])]
      linarith [hq''.2, not_le.mp h]
  have hsplit := sum_offLineField_le_split hH0 Z G_loc hfar
  have hloc : (∑ q ∈ G_loc, (foldedRe q - 1 / 2) ^ 2 * lorentzMass (q.1 : ℂ).im) ≤
      8 * (c + 3) * C₃ * H := by
    have h1 : (∑ q ∈ G_loc, (foldedRe q - 1 / 2) ^ 2 * lorentzMass (q.1 : ℂ).im) ≤
        ∑ q ∈ G_loc, (foldedRe q - 1 / 2) ^ 2 * (8 * (c + 3) * L) := by
      refine Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have hq' := (hmem q).mp hq
      exact hmass _ (by linarith [hq'.1]) (by linarith [hq'.2])
    rw [← Finset.sum_mul] at h1
    have h2 := mul_le_mul_of_nonneg_right hsumG (by positivity : 0 ≤ 8 * (c + 3) * L)
    have e : C₃ * H / L * (8 * (c + 3) * L) = 8 * (c + 3) * C₃ * H := by field_simp
    linarith
  have hfar_part : (1 / (4 * H ^ 2)) * ∑ q' ∈ Z, lorentzMass (q'.1 : ℂ).im ≤ H := by
    have hZm : ∑ q' ∈ Z, lorentzMass (q'.1 : ℂ).im ≤ (Z.card : ℝ) * (8 * (c + 3) * L) := by
      refine (Finset.sum_le_sum fun q' hq' => hmass _ (by linarith [(hZ q' hq').1])
        (by linarith [(hZ q' hq').2])).trans_eq ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have hZm' : ∑ q' ∈ Z, lorentzMass (q'.1 : ℂ).im ≤ (3 * H * L) * (8 * (c + 3) * L) :=
      hZm.trans (mul_le_mul_of_nonneg_right hcardZ (by positivity))
    have hsqrt : 6 * (c + 3) * K₁ ≤ Γ ^ (1 / 2 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) (hΓ₀K.trans hΓ) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at this
    have hlogsq : L ^ 2 ≤ K₁ * Γ ^ (1 / 2 : ℝ) :=
      (pow_le_pow_left₀ hL0.le (by linarith) 2).trans (hK₁ Γ hΓ1)
    have hkey : 6 * (c + 3) * L ^ 2 ≤ H ^ 2 := by
      calc 6 * (c + 3) * L ^ 2 ≤ 6 * (c + 3) * (K₁ * Γ ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogsq (by positivity)
        _ = (6 * (c + 3) * K₁) * Γ ^ (1 / 2 : ℝ) := by ring
        _ ≤ Γ ^ (1 / 2 : ℝ) * Γ ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hsqrt (by positivity)
        _ ≤ H * H := mul_le_mul hsqrtH hsqrtH (by positivity) hH0.le
        _ = H ^ 2 := by ring
    calc (1 / (4 * H ^ 2)) * ∑ q' ∈ Z, lorentzMass (q'.1 : ℂ).im
        ≤ (1 / (4 * H ^ 2)) * ((3 * H * L) * (8 * (c + 3) * L)) :=
          mul_le_mul_of_nonneg_left hZm' (by positivity)
      _ = 6 * (c + 3) * L ^ 2 / H := by field_simp; ring
      _ ≤ H ^ 2 / H := div_le_div_of_nonneg_right hkey hH0.le
      _ = H := by field_simp
  calc ∑ q' ∈ Z, offLineField (q'.1 : ℂ).im
      ≤ (∑ q ∈ G_loc, (foldedRe q - 1 / 2) ^ 2 * lorentzMass (q.1 : ℂ).im) +
          (1 / (4 * H ^ 2)) * ∑ q' ∈ Z, lorentzMass (q'.1 : ℂ).im := hsplit
    _ ≤ 8 * (c + 3) * C₃ * H + H := add_le_add hloc hfar_part
    _ = (8 * (c + 3) * C₃ + 1) * H := by ring

/-- **Almost every zero ordinate of a short window is nearly Weil-positive.** There are `C` and `Γ₀`
such that for `Γ ≥ Γ₀`, `Γ^{99/100} ≤ H ≤ Γ/8` and `η > 0`, the finite set `Z` of zero copies with
ordinate in `[Γ, Γ + H]` has at least `H log Γ / (16π)` elements, at most `C H / η` of them have
`Φ(Im q) > η`, and at every other one, for every aperture `A ≥ 0` and every real
`F₀ ∈ C²_c([-A, A])`, `Q(F₀ cos γ·) + Q(F₀ sin γ·) ≥ -4η (A + 1)² e^A N(F₀)²` at `γ = Im q`. -/
theorem exists_shortWindow_almostEvery_zeroOrdinate_nearly_positive :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Γ₀ : ℝ, 64 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ H : ℝ, Γ ^ (99 / 100 : ℝ) ≤ H → H ≤ Γ / 8 → ∀ η : ℝ, 0 < η →
        ∃ Z : Finset XiZeroCopy,
          (∀ q : XiZeroCopy, q ∈ Z ↔ Γ ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + H) ∧
          H * Real.log Γ / (16 * Real.pi) ≤ (Z.card : ℝ) ∧
          ((Z.filter fun q => η < offLineField (q.1 : ℂ).im).card : ℝ) ≤ C * H / η ∧
          ∀ q ∈ Z, offLineField (q.1 : ℂ).im ≤ η →
            ∀ A : ℝ, 0 ≤ A → ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
              (∀ u : ℝ, A < |u| → F₀ u = 0) →
              -(4 * η * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
                fullZeroForm (cosineSource F₀ (q.1 : ℂ).im) +
                  fullZeroForm (sineSource F₀ (q.1 : ℂ).im) := by
  obtain ⟨C, hC, Γ₁, hΓ₁, hsum⟩ := exists_sum_offLineField_zeroOrdinates_le
  obtain ⟨Γ_c, hΓ_c, hcore⟩ := exists_window_core_count
  refine ⟨C, hC, max Γ₁ Γ_c, hΓ₁.trans (le_max_left _ _),
    fun Γ hΓ H hH1 hH2 η hη => ?_⟩
  classical
  have hΓ64 : 64 ≤ Γ := (hΓ₁.trans (le_max_left _ _)).trans hΓ
  have hΓ0 : 0 < Γ := by linarith
  have hH0 : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hΓ0 _) hH1
  have hS_fin : ({q : XiZeroCopy | Γ ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + H}).Finite :=
    (finite_xiOrdinateWindow (Γ + H) 0).subset fun q hq => by
      rw [mem_xiOrdinateWindow_iff, sub_zero, abs_le]
      exact ⟨by linarith [hq.1], hq.2⟩
  obtain ⟨Z, hmemZ⟩ : ∃ Z : Finset XiZeroCopy,
      ∀ q : XiZeroCopy, q ∈ Z ↔ Γ ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + H :=
    ⟨hS_fin.toFinset, fun _ => hS_fin.mem_toFinset⟩
  have hsumZ := hsum Γ ((le_max_left _ _).trans hΓ) H hH1 hH2 Z fun q hq => (hmemZ q).mp hq
  refine ⟨Z, hmemZ, ?_, ?_, ?_⟩
  · -- The core copies lie in `Z`.
    obtain ⟨hlow, -⟩ := hcore Γ ((le_max_right _ _).trans hΓ) H hH1 hH2
    set W := xiSupportsWindow (Γ + H / 4) (Γ + 3 * H / 4)
    have hW0 : (0 : ℝ) ≤ Γ + H / 4 := by linarith
    have hsub : xiCopiesOf W ⊆ Z := fun q hq => by
      unfold xiCopiesOf at hq
      rw [Finset.mem_sigma] at hq
      have h := (mem_xiSupportsWindow hW0).mp hq.1
      exact (hmemZ q).mpr ⟨by linarith [h.1], by linarith [h.2]⟩
    have hcopies : ((xiCopiesOf W).card : ℝ) = ∑ ρ ∈ W, (xiSupportMultiplicity ρ : ℝ) := by
      unfold xiCopiesOf
      rw [Finset.card_sigma]
      push_cast
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [Finset.card_univ, Fintype.card_fin]
      rfl
    have hcard := Finset.card_le_card hsub
    have : ((xiCopiesOf W).card : ℝ) ≤ (Z.card : ℝ) := by exact_mod_cast hcard
    rw [hcopies] at this
    have e : H * Real.log Γ / (16 * Real.pi) = (1 / (16 * Real.pi)) * H * Real.log Γ := by ring
    linarith
  · -- Markov over the ordinates.
    set Zb := Z.filter fun q => η < offLineField (q.1 : ℂ).im
    have h1 := Finset.card_nsmul_le_sum Zb (fun q => offLineField (q.1 : ℂ).im) η
      fun q hq => (Finset.mem_filter.mp hq).2.le
    rw [nsmul_eq_mul] at h1
    have h2 : ∑ q ∈ Zb, offLineField (q.1 : ℂ).im ≤ ∑ q ∈ Z, offLineField (q.1 : ℂ).im :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun q _ _ => offLineField_nonneg _
    rw [le_div_iff₀ hη]
    linarith
  · intro q _ hq A hA F₀ hF₀ hF₀c hsupp
    have h := neg_offLineField_le_fullZeroForm hF₀ hF₀c hA hsupp (q.1 : ℂ).im
    have hK : 0 ≤ 4 * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hq hK
    linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
