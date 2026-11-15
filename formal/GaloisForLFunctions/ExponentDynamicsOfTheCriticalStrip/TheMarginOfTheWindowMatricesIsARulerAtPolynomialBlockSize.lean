import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.StepSamplesCarryWeilsFormOfALipschitzPacket
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheRateOfTheMarginOfTheWindowMatricesBoundsTheAbscissaOfTheZeros

/-!
# The margin of the window matrices is a ruler at polynomial block size

The margin of a window `(R, (3K + 1)R]` is the second eigenvalue of its neutral matrix `N_W`.
The **margin law of rate `β`** along a block-size law `ρ` says: for some `C` and every `K`, the
matrix `N_W + C K^β` of the window of ratio `3K + 1` at block size `ρ(K)` has at most one negative
square. This module proves that the law reads the zero width `w = sup |Re ρ − ½|` exactly, at
block sizes polynomial in the ratio and with no hypothesis on the zeros:

* **Receiver** (`zetaZeroWidth_le_of_neutralWindow_marginRate_of_pow_le_blockSize`): if
  `ρ(K) ≥ K¹⁰` and the law holds at a rate `θ < ½`, then `w ≤ θ`.
* **Ruler** (`isRuler_marginLaw`): if `K¹⁰ ≤ ρ(K) ≤ K^A`, then `w ≤ β` iff the law holds at
  every rate `β + ε`.
* **Exponent** (`sInf_marginLaw_eq_zetaZeroWidth`): the infimum of the rates of the margin law
  is `w`.

The receiver puts the plane of the binding state and of the antisymmetric state of the two ends
at lag `v` into the window matrix of ratio `3K + 1 ≍ e^v`. The two states are Lipschitz packets
with constants independent of `v`, so their step samples carry the neutral form and the mass up
to `O(K⁴ log R / R)`; for `R ≥ K¹⁰` this is `O(1/K)`, below the depth `1` by which the smooth
plane lies under `−C K^θ` times the mass (`two_le_hermNegIndex_neutralWindow_of_plane`). No limit
in the block size is taken, which is what makes the block size polynomial.
-/

open Finset Filter Topology MeasureTheory Matrix
open scoped Real
open Zeta23
open GaloisForLFunctions.HTGeometry (hermNegIndex)
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg
  zetaZeroWidth_le_three_eighths lagStructure)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx)
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

noncomputable section

/-! ### 1. Bounds and Lipschitz constants -/

/-- A function vanishing for `|u| > L` has compact support. -/
theorem hasCompactSupport_of_abs_lt {f : ℝ → ℝ} {L : ℝ} (h : ∀ u, L < |u| → f u = 0) :
    HasCompactSupport f :=
  hasCompactSupport_of_support_le (l := -L) (r := L) fun u hu => by
    by_contra hcon
    refine hu (h u ?_)
    rw [not_and_or, not_le, not_le] at hcon
    rcases hcon with h1 | h1
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
    · exact lt_of_lt_of_le h1 (le_abs_self u)

/-- A function of class `C²` with compact support is bounded and Lipschitz. -/
theorem exists_bound_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ M L : ℝ, (∀ u, |f u| ≤ M) ∧ ∀ u u', |f u - f u'| ≤ L * |u - u'| := by
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨C, hC⟩ := hf.lipschitzWith_of_hasCompactSupport hfc (by norm_num)
  refine ⟨B, C, fun u => ?_, fun u u' => ?_⟩
  · rw [← Real.norm_eq_abs]
    exact hB u
  · have h := hC.dist_le_mul u u'
    rwa [Real.dist_eq, Real.dist_eq] at h

/-- The binding state of the two ends is bounded and Lipschitz uniformly in the lag. -/
theorem twoEndSpline_bounds {M L : ℝ} (hb : ∀ u, |spline u| ≤ M)
    (hL : ∀ u u', |spline u - spline u'| ≤ L * |u - u'|) (v : ℝ) :
    (∀ u, |twoEndSpline v u| ≤ 2 * M) ∧
      ∀ u u', |twoEndSpline v u - twoEndSpline v u'| ≤ 2 * L * |u - u'| := by
  refine ⟨fun u => ?_, fun u u' => ?_⟩
  · unfold twoEndSpline
    exact (abs_add_le _ _).trans (by linarith [hb (u + v / 2), hb (u - v / 2)])
  · unfold twoEndSpline
    have h1 := hL (u + v / 2) (u' + v / 2)
    have h2 := hL (u - v / 2) (u' - v / 2)
    rw [add_sub_add_right_eq_sub] at h1
    rw [sub_sub_sub_cancel_right] at h2
    have e : spline (u + v / 2) + spline (u - v / 2) -
        (spline (u' + v / 2) + spline (u' - v / 2)) =
        (spline (u + v / 2) - spline (u' + v / 2)) +
          (spline (u - v / 2) - spline (u' - v / 2)) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (by linarith)

/-- The antisymmetric state of the two ends is bounded and Lipschitz uniformly in the lag. -/
theorem twoEndOdd_bounds {M L : ℝ} (hb : ∀ u, |poleFreeProfile u| ≤ M)
    (hL : ∀ u u', |poleFreeProfile u - poleFreeProfile u'| ≤ L * |u - u'|) (v : ℝ) :
    (∀ u, |twoEndOdd v u| ≤ 2 * M) ∧
      ∀ u u', |twoEndOdd v u - twoEndOdd v u'| ≤ 2 * L * |u - u'| := by
  refine ⟨fun u => ?_, fun u u' => ?_⟩
  · unfold twoEndOdd
    exact (abs_sub _ _).trans (by linarith [hb (u + v / 2), hb (u - v / 2)])
  · unfold twoEndOdd
    have h1 := hL (u + v / 2) (u' + v / 2)
    have h2 := hL (u - v / 2) (u' - v / 2)
    rw [add_sub_add_right_eq_sub] at h1
    rw [sub_sub_sub_cancel_right] at h2
    have e : poleFreeProfile (u + v / 2) - poleFreeProfile (u - v / 2) -
        (poleFreeProfile (u' + v / 2) - poleFreeProfile (u' - v / 2)) =
        (poleFreeProfile (u + v / 2) - poleFreeProfile (u' + v / 2)) -
          (poleFreeProfile (u - v / 2) - poleFreeProfile (u' - v / 2)) := by ring
    rw [e]
    exact (abs_sub _ _).trans (by linarith)

/-! ### 2. Packets translated into a window -/

/-- A packet supported in `(log 3, log K)`, translated by `log R`, is a packet of the window
`(R, (3K + 1)R]`. -/
theorem windowPacket_translate {f : ℝ → ℝ} {M L : ℝ} (hfc : Continuous f)
    (hb : ∀ u, |f u| ≤ M) (hL : ∀ u u', |f u - f u'| ≤ L * |u - u'|) {K R : ℕ} (hK : 1 ≤ K)
    (hR : 1 ≤ R) (hs : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    WindowPacket R (3 * K * R) M L (fun u => f (u - Real.log R)) where
  continuous := hfc.comp (continuous_id.sub continuous_const)
  bound := fun u => hb _
  lipschitz := fun u u' => by
    have h := hL (u - Real.log R) (u' - Real.log R)
    rwa [sub_sub_sub_cancel_right] at h
  support := fun u hu => by
    have h1 : ¬(u - Real.log R ≤ Real.log 3 ∨ Real.log K ≤ u - Real.log R) := fun h =>
      hu (hs _ h)
    rw [not_or, not_le, not_le] at h1
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hR' : (0 : ℝ) < R := by exact_mod_cast hR
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hle : Real.log ((K : ℝ) * R) ≤ Real.log ((R + 3 * K * R : ℕ) : ℝ) :=
      Real.log_le_log (mul_pos hK' hR') (by
        push_cast
        nlinarith [mul_pos hK' hR'])
    rw [Real.log_mul hK'.ne' hR'.ne'] at hle
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

/-- On a packet of class `C²` supported in an interval shorter than `log(Q + 1)` the neutral
form by the zeros and the charges is the neutral form of the window of ratio `Q`. -/
theorem smoothNeutral_eq_neutralForm_of_window {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {l r : ℝ}
    (hs : ∀ u, f u ≠ 0 → l ≤ u ∧ u ≤ r) {Q : ℕ} (hQ : r - l < Real.log ((Q : ℝ) + 1)) :
    smoothNeutral f = neutralForm Q f := by
  have hoff : ∀ u, u < l ∨ r < u → f u = 0 := fun u hu => by
    by_contra h
    obtain ⟨h1, h2⟩ := hs u h
    rcases hu with h3 | h3 <;> linarith
  have hQn : ∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0 := fun n hn =>
    packetAutocorr_eq_zero_of_vanishing_off hoff (lt_of_lt_of_le hQ
      (Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_of_lt hn)))
  unfold smoothNeutral neutralForm
  rw [zeroSum_eq_packetForm hf (hasCompactSupport_of_support_le hs) hQn]

/-- **The window matrix on the samples of a translated packet.** For a packet `f` of class `C²`
supported in `(log 3, log K)`, bounded by `M` and Lipschitz with constant `L`, the neutral
matrix of the window `(R, (3K + 1)R]` on the cell coefficients of `f(· − log R)` is within
`(L + M)² · sampleError` of the neutral form of `f`, and their mass within
`(L + M)² log(3K + 1)/R²` of the mass of `f`. -/
theorem abs_sample_translate_sub_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M L : ℝ}
    (hb : ∀ u, |f u| ≤ M) (hL : ∀ u u', |f u - f u'| ≤ L * |u - u'|) {K R : ℕ} (hK : 1 ≤ K)
    (hR : 1 ≤ R) (hs : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    |∑ j ∈ range (3 * K * R), ∑ l ∈ range (3 * K * R),
          cellCoeff (fun u => f (u - Real.log R)) R j *
            cellCoeff (fun u => f (u - Real.log R)) R l *
              neutralBlock (3 * K + 1) (R + j) (R + l) - smoothNeutral f| ≤
        (L + M) ^ 2 * sampleError (3 * K + 1) R (3 * K * R) ∧
      |∑ j ∈ range (3 * K * R), cellCoeff (fun u => f (u - Real.log R)) R j ^ 2 -
          ∫ u, f u ^ 2| ≤
        (L + M) ^ 2 * (Real.log ((3 * K + 1 : ℕ) : ℝ) / (R : ℝ) ^ 2) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hQR : R + 3 * K * R ≤ (3 * K + 1) * R := le_of_eq (by ring)
  have hQ1 : 1 ≤ 3 * K + 1 := by omega
  have hW := windowPacket_translate hf.continuous hb hL hK hR hs
  -- the neutral form does not change under the translation
  have habs : ∀ u : ℝ, Real.log K < |u| → f u = 0 := fun u hu => by
    rcases le_or_gt 0 u with h0 | h0
    · rw [abs_of_nonneg h0] at hu
      exact hs u (Or.inr hu.le)
    · exact hs u (Or.inl (by linarith))
  have hT : smoothNeutral (fun u => f (u - Real.log R)) = smoothNeutral f :=
    smoothNeutral_translate hf habs (Real.log R)
  have hFs : ∀ u, f (u - Real.log R) ≠ 0 →
      Real.log R + Real.log 3 ≤ u ∧ u ≤ Real.log R + Real.log K := fun u hu => by
    have h1 : ¬(u - Real.log R ≤ Real.log 3 ∨ Real.log K ≤ u - Real.log R) := fun h =>
      hu (hs _ h)
    rw [not_or, not_le, not_le] at h1
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hN : smoothNeutral (fun u => f (u - Real.log R)) =
      neutralForm (3 * K + 1) (fun u => f (u - Real.log R)) :=
    smoothNeutral_eq_neutralForm_of_window (f := fun u => f (u - Real.log R))
      (hf.comp (contDiff_id.sub contDiff_const)) hFs
      (lt_of_lt_of_le (by linarith) (Real.log_le_log hK' (by
        push_cast
        linarith)))
  constructor
  · have h := abs_neutralForm_stepSample_sub_le hW hR hQ1 hQR
    unfold stepSample at h
    rw [neutralForm_stepPacket hR, ← hN, hT] at h
    exact h
  · have h := abs_sum_cellCoeff_sq_sub_le hW hR hQ1 hQR
    rw [integral_comp_sub_sq f (Real.log R)] at h
    refine h.trans (le_of_eq ?_)
    ring

/-! ### 3. A quadratic form on a plane -/

/-- A quadratic form on a combination of two vectors. -/
theorem sum_plane_expand (J : ℕ) (A : ℕ → ℕ → ℝ) (s t : ℝ) (a b : ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, (s * a j + t * b j) * (s * a l + t * b l) * A j l =
      s ^ 2 * (∑ j ∈ range J, ∑ l ∈ range J, a j * a l * A j l) +
        s * t * ((∑ j ∈ range J, ∑ l ∈ range J, (a j + b j) * (a l + b l) * A j l) -
          (∑ j ∈ range J, ∑ l ∈ range J, a j * a l * A j l) -
            ∑ j ∈ range J, ∑ l ∈ range J, b j * b l * A j l) +
        t ^ 2 * ∑ j ∈ range J, ∑ l ∈ range J, b j * b l * A j l := by
  have h : ∀ j l, (s * a j + t * b j) * (s * a l + t * b l) * A j l =
      s ^ 2 * (a j * a l * A j l) +
        s * t * ((a j + b j) * (a l + b l) * A j l - a j * a l * A j l - b j * b l * A j l) +
        t ^ 2 * (b j * b l * A j l) := fun j l => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-! ### 4. The plane of the two states inside a window matrix -/

/-- **The plane of the two states at finite block size.** Let `v` be a lag with
`log 3 + 12 + |v| ≤ log K`. If the neutral forms of the binding state and of the antisymmetric
state of the two ends lie below `−D` times their masses by at least `1`, and the sampling error
of the window `(R, (3K + 1)R]` is at most `1/(10 (1 + D))`, then `N_W + c` has two negative
squares for every `c ≤ D`. -/
theorem two_le_hermNegIndex_neutralWindow_of_plane {Ms Ls Mp Lp : ℝ}
    (hMs : ∀ u, |spline u| ≤ Ms) (hLs : ∀ u u', |spline u - spline u'| ≤ Ls * |u - u'|)
    (hMp : ∀ u, |poleFreeProfile u| ≤ Mp)
    (hLp : ∀ u u', |poleFreeProfile u - poleFreeProfile u'| ≤ Lp * |u - u'|)
    {v : ℝ} {K R : ℕ} (hK : 1 ≤ K) (hR : 1 ≤ R)
    (hKlog : Real.log 3 + 12 + |v| ≤ Real.log K) {c D : ℝ} (hD : 0 ≤ D) (hcD : c ≤ D)
    (hg : smoothNeutral (fun u => twoEndSpline v (u - stateShift v)) +
      D * ∫ u, twoEndSpline v (u - stateShift v) ^ 2 ≤ -1)
    (ho : smoothNeutral (shiftedOdd v) + D * ∫ u, shiftedOdd v u ^ 2 ≤ -1)
    (herr : (2 * (Ls + Ms) + 2 * (Lp + Mp)) ^ 2 *
        (sampleError (3 * K + 1) R (3 * K * R) +
          Real.log ((3 * K + 1 : ℕ) : ℝ) / (R : ℝ) ^ 2) ≤ 1 / (10 * (1 + D))) :
    2 ≤ hermNegIndex ((neutralWindow (3 * K + 1) R (3 * K * R) +
      Matrix.diagonal fun _ => c).map (↑) :
        Matrix (Fin (3 * K * R)) (Fin (3 * K * R)) ℂ) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hMs0 : 0 ≤ Ms := (abs_nonneg _).trans (hMs 0)
  have hMp0 : 0 ≤ Mp := (abs_nonneg _).trans (hMp 0)
  have hLs0 : 0 ≤ Ls := by
    have h := (abs_nonneg _).trans (hLs 1 0)
    rwa [sub_zero, abs_one, mul_one] at h
  have hLp0 : 0 ≤ Lp := by
    have h := (abs_nonneg _).trans (hLp 1 0)
    rwa [sub_zero, abs_one, mul_one] at h
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 2 * (Ls + Ms) + 2 * (Lp + Mp) := ⟨_, rfl⟩
  obtain ⟨SE, hSE⟩ : ∃ SE : ℝ, SE = sampleError (3 * K + 1) R (3 * K * R) := ⟨_, rfl⟩
  obtain ⟨lq, hlq⟩ : ∃ lq : ℝ, lq = Real.log ((3 * K + 1 : ℕ) : ℝ) / (R : ℝ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℝ, e₀ = 1 / (10 * (1 + D)) := ⟨_, rfl⟩
  rw [← hc₀, ← hSE, ← hlq, ← he₀] at herr
  have hSE0 : 0 ≤ SE := by rw [hSE]; exact sampleError_nonneg (by omega) R (3 * K * R)
  have hlq0 : 0 ≤ lq := by
    rw [hlq]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 3 * K + 1)))
      (sq_nonneg _)
  have he₀0 : 0 < e₀ := by rw [he₀]; positivity
  have he₀b : 5 / 2 * e₀ * (1 + D + 0) ≤ 1 / 4 := by
    have hD1 : (1 : ℝ) + D ≠ 0 := by linarith
    have h1 : e₀ * (1 + D) = 1 / 10 := by
      rw [he₀]
      field_simp
    linarith
  -- an error with constant below c₀ is below e₀
  have hSEle : ∀ a : ℝ, 0 ≤ a → a ≤ c₀ → a ^ 2 * SE ≤ e₀ := fun a ha hac => by
    have h1 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hac 2) hSE0
    have h2 := mul_nonneg (sq_nonneg c₀) hlq0
    have e : c₀ ^ 2 * (SE + lq) = c₀ ^ 2 * SE + c₀ ^ 2 * lq := by ring
    linarith
  have hlqle : ∀ a : ℝ, 0 ≤ a → a ≤ c₀ → a ^ 2 * lq ≤ e₀ := fun a ha hac => by
    have h1 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hac 2) hlq0
    have h2 := mul_nonneg (sq_nonneg c₀) hSE0
    have e : c₀ ^ 2 * (SE + lq) = c₀ ^ 2 * SE + c₀ ^ 2 * lq := by ring
    linarith
  -- the two states live in (log 3, log K)
  have hvan := vanishing_twoEndSpline v
  have hshift : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u →
      5 + |v| / 2 < |u - stateShift v| := fun u hu => by
    unfold stateShift
    have hv' := abs_nonneg v
    rcases hu with h1 | h1
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
    · exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  have hsg : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → twoEndSpline v (u - stateShift v) = 0 :=
    fun u hu => (hvan _ (hshift u hu)).1
  have hso : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → shiftedOdd v u = 0 := fun u hu =>
    (hvan _ (hshift u hu)).2
  have hss : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u →
      twoEndSpline v (u - stateShift v) + shiftedOdd v u = 0 := fun u hu => by
    rw [hsg u hu, hso u hu, add_zero]
  have hcg : ContDiff ℝ 2 fun u => twoEndSpline v (u - stateShift v) :=
    (contDiff_twoEndSpline v).comp (contDiff_id.sub contDiff_const)
  have hco : ContDiff ℝ 2 (shiftedOdd v) := contDiff_shiftedOdd v
  have hcs : ContDiff ℝ 2 fun u => twoEndSpline v (u - stateShift v) + shiftedOdd v u :=
    hcg.add hco
  -- their bounds and Lipschitz constants
  obtain ⟨hbG, hlG⟩ := twoEndSpline_bounds hMs hLs v
  obtain ⟨hbO, hlO⟩ := twoEndOdd_bounds hMp hLp v
  have hbG' : ∀ u, |twoEndSpline v (u - stateShift v)| ≤ 2 * Ms := fun u => hbG _
  have hlG' : ∀ u u', |twoEndSpline v (u - stateShift v) - twoEndSpline v (u' - stateShift v)| ≤
      2 * Ls * |u - u'| := fun u u' => by
    have h := hlG (u - stateShift v) (u' - stateShift v)
    rwa [sub_sub_sub_cancel_right] at h
  have hbO' : ∀ u, |shiftedOdd v u| ≤ 2 * Mp := fun u => hbO (u - stateShift v)
  have hlO' : ∀ u u', |shiftedOdd v u - shiftedOdd v u'| ≤ 2 * Lp * |u - u'| := fun u u' => by
    have h := hlO (u - stateShift v) (u' - stateShift v)
    rw [sub_sub_sub_cancel_right] at h
    exact h
  have hbS : ∀ u, |twoEndSpline v (u - stateShift v) + shiftedOdd v u| ≤ 2 * Ms + 2 * Mp :=
    fun u => (abs_add_le _ _).trans (add_le_add (hbG' u) (hbO' u))
  have hlS : ∀ u u', |twoEndSpline v (u - stateShift v) + shiftedOdd v u -
      (twoEndSpline v (u' - stateShift v) + shiftedOdd v u')| ≤
      (2 * Ls + 2 * Lp) * |u - u'| := fun u u' => by
    have e : twoEndSpline v (u - stateShift v) + shiftedOdd v u -
        (twoEndSpline v (u' - stateShift v) + shiftedOdd v u') =
        (twoEndSpline v (u - stateShift v) - twoEndSpline v (u' - stateShift v)) +
          (shiftedOdd v u - shiftedOdd v u') := by ring
    rw [e, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hlG' u u') (hlO' u u'))
  -- the samples of the three packets of the plane
  obtain ⟨hG1, hG2⟩ := abs_sample_translate_sub_le hcg hbG' hlG' hK hR hsg
  obtain ⟨hO1, hO2⟩ := abs_sample_translate_sub_le hco hbO' hlO' hK hR hso
  obtain ⟨hS1, hS2⟩ := abs_sample_translate_sub_le hcs hbS hlS hK hR hss
  obtain ⟨-, -, hNs⟩ := smoothNeutral_plane v
  have hmass := integral_plane_sq v
  rw [hNs] at hS1
  rw [hmass] at hS2
  -- the coefficients of the sum are the sums of the coefficients
  obtain ⟨σg, hσg⟩ : ∃ σ : ℕ → ℝ,
      σ = cellCoeff (fun u => twoEndSpline v (u - Real.log R - stateShift v)) R := ⟨_, rfl⟩
  obtain ⟨σo, hσo⟩ : ∃ σ : ℕ → ℝ, σ = cellCoeff (fun u => shiftedOdd v (u - Real.log R)) R :=
    ⟨_, rfl⟩
  have hσs : ∀ j, cellCoeff (fun u => twoEndSpline v (u - Real.log R - stateShift v) +
      shiftedOdd v (u - Real.log R)) R j = σg j + σo j := fun j => by
    rw [hσg, hσo]
    exact cellCoeff_add (G := fun u => twoEndSpline v (u - Real.log R - stateShift v))
      (H := fun u => shiftedOdd v (u - Real.log R))
      (hcg.continuous.comp (continuous_id.sub continuous_const))
      (hco.continuous.comp (continuous_id.sub continuous_const)) R j
  rw [← hσg] at hG1 hG2
  rw [← hσo] at hO1 hO2
  simp only [hσs] at hS1 hS2
  -- the smooth plane
  obtain ⟨Ng, hNg⟩ : ∃ N, N = smoothNeutral (fun u => twoEndSpline v (u - stateShift v)) :=
    ⟨_, rfl⟩
  obtain ⟨No, hNo⟩ : ∃ N, N = smoothNeutral (shiftedOdd v) := ⟨_, rfl⟩
  obtain ⟨mg, hmg⟩ : ∃ m, m = ∫ u, twoEndSpline v (u - stateShift v) ^ 2 := ⟨_, rfl⟩
  obtain ⟨mo, hmo⟩ : ∃ m, m = ∫ u, shiftedOdd v u ^ 2 := ⟨_, rfl⟩
  have hmg0 : 0 ≤ mg := by rw [hmg]; exact integral_nonneg fun u => sq_nonneg _
  have hmo0 : 0 ≤ mo := by rw [hmo]; exact integral_nonneg fun u => sq_nonneg _
  rw [← hNg, ← hmg] at hg
  rw [← hNo, ← hmo] at ho
  rw [← hNg] at hG1
  rw [← hmg] at hG2
  rw [← hNo] at hO1
  rw [← hmo] at hO2
  rw [← hNg, ← hNo] at hS1
  rw [← hmg, ← hmo] at hS2
  -- the six errors are below e₀
  rw [← hSE] at hG1 hO1 hS1
  have hG1' := hG1.trans (hSEle (2 * Ls + 2 * Ms) (by linarith) (by rw [hc₀]; linarith))
  have hO1' := hO1.trans (hSEle (2 * Lp + 2 * Mp) (by linarith) (by rw [hc₀]; linarith))
  have hS1' := hS1.trans (hSEle (2 * Ls + 2 * Lp + (2 * Ms + 2 * Mp)) (by linarith)
    (by rw [hc₀]; linarith))
  rw [← hlq] at hG2 hO2 hS2
  have hG2' := hG2.trans (hlqle (2 * Ls + 2 * Ms) (by linarith) (by rw [hc₀]; linarith))
  have hO2' := hO2.trans (hlqle (2 * Lp + 2 * Mp) (by linarith) (by rw [hc₀]; linarith))
  have hS2' := hS2.trans (hlqle (2 * Ls + 2 * Lp + (2 * Ms + 2 * Mp)) (by linarith)
    (by rw [hc₀]; linarith))
  -- two negative squares
  refine two_le_hermNegIndex_of_plane _ (fun i : Fin (3 * K * R) => σg (i : ℕ))
    (fun i : Fin (3 * K * R) => σo (i : ℕ)) fun s t hst => ?_
  have key := sum_fin_neutralWindow_add_diag (3 * K + 1) R (3 * K * R) c
    (fun n => s * σg n + t * σo n)
  refine lt_of_eq_of_lt key ?_
  have hx0 : 0 ≤ ∑ j ∈ range (3 * K * R), (s * σg j + t * σo j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [sum_sq_lin (range (3 * K * R)) s t σg σo] at hx0
  rw [sum_plane_expand (3 * K * R) (fun j l => neutralBlock (3 * K + 1) (R + j) (R + l)) s t
    σg σo, sum_sq_lin (range (3 * K * R)) s t σg σo]
  refine plane_endgame (s := s) (t := t) (lam := 0) (Mm := mg + mo + 1) hst one_pos he₀0 hD
    le_rfl hg ho (by linarith) (by linarith) (by norm_num) he₀b hG1' hO1' hS1' hG2' hO2' hS2' ?_
  have h1 := mul_le_mul_of_nonneg_right hcD hx0
  linarith

/-! ### 5. The sampling error at polynomial block size -/

/-- The constant of the sampling error at ratio `3K + 1`. -/
def sampleRateConst : ℝ := 256 * (40 * windowRateConst 1 + 7)

theorem sampleRateConst_nonneg : 0 ≤ sampleRateConst := by
  unfold sampleRateConst
  have := windowRateConst_nonneg 1
  linarith

/-- The step samples of the window `(R, (3K + 1)R]` are resolved by the integers up to
`N = 4 (3K + 1) R³`, and `1 + log N ≤ 8 (3K + 1)(1 + log R)`. -/
theorem one_add_log_resolution_le {K R : ℕ} (hK : 1 ≤ K) (hR : 1 ≤ R) :
    1 + Real.log ((4 * (R + 3 * K * R) * R ^ 2 : ℕ) : ℝ) ≤
      8 * ((3 * K + 1 : ℕ) : ℝ) * (1 + Real.log R) := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hR0 : (0 : ℝ) < R := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((3 * K + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hqK : q = 3 * K + 1 := by
    rw [hq]
    push_cast
    ring
  have hq1 : 1 ≤ q := by rw [hqK]; linarith
  have hq0 : 0 < q := by linarith
  have hlq : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos hq0
  have hlR0 : 0 ≤ Real.log R := Real.log_nonneg hR'
  have hNq : ((4 * (R + 3 * K * R) * R ^ 2 : ℕ) : ℝ) = 4 * q * (R : ℝ) ^ 3 := by
    rw [hqK]
    push_cast
    ring
  have hlogN : Real.log ((4 * (R + 3 * K * R) * R ^ 2 : ℕ) : ℝ) =
      Real.log 4 + Real.log q + 3 * Real.log R := by
    have h4q : (4 : ℝ) * q ≠ 0 := (mul_pos (by norm_num) hq0).ne'
    have hR3 : (R : ℝ) ^ 3 ≠ 0 := (pow_pos hR0 3).ne'
    rw [hNq, Real.log_mul h4q hR3, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hq0.ne',
      Real.log_pow]
    norm_num
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have h1 : 0 ≤ (q - 1) * Real.log R := mul_nonneg (sub_nonneg.mpr hq1) hlR0
  rw [← hq, hlogN]
  linarith

/-- **The depth of the sampling error** of the window `(R, (3K + 1)R]` is at most
`40 W q³ (1 + log R)`, `q = 3K + 1`: the depth of the window at the resolution of its samples. -/
theorem sampleDepth_le {K R : ℕ} (hK : 1 ≤ K) (hR : 1 ≤ R) :
    160 * (logSamplingConst ((Real.log ((3 * K + 1 : ℕ) : ℝ) + 1) / 2) zetaZeroWidth *
        (16 * Real.log (1 + 4 * ((R + 3 * K * R : ℕ) : ℝ) * (R : ℝ) ^ 2) + 5)) ≤
      40 * windowRateConst 1 * (((3 * K + 1 : ℕ) : ℝ) ^ 3 * (1 + Real.log R)) := by
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((3 * K + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hq1 : 1 ≤ q := by
    rw [hq]
    exact_mod_cast (by omega : 1 ≤ 3 * K + 1)
  have hq0 : 0 < q := by linarith
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlq : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos hq0
  have hlR0 : 0 ≤ Real.log R := Real.log_nonneg hR'
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log R := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = windowRateConst 1 := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; exact windowRateConst_nonneg 1
  -- the integers up to which the step samples are resolved
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 4 * (R + 3 * K * R) * R ^ 2 := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.add_pos_left hR _)) (pow_pos hR 2)
  have hNc : (N : ℝ) = 4 * ((R + 3 * K * R : ℕ) : ℝ) * (R : ℝ) ^ 2 := by
    rw [hN, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have h1N : 1 + Real.log (N : ℝ) ≤ 8 * q * ℓ := by
    rw [hN, hq, hℓ]
    exact one_add_log_resolution_le hK hR
  -- the depth of the window
  obtain ⟨Lc, hLc⟩ : ∃ Lc : ℝ, Lc = logSamplingConst ((Real.log q + 1) / 2) zetaZeroWidth :=
    ⟨_, rfl⟩
  have hLc0 : 0 ≤ Lc := by
    rw [hLc]
    exact logSamplingConst_nonneg (by linarith)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.log (1 + (N : ℝ)) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by
    rw [hT]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact Real.log_nonneg (by linarith)
  have hdepth : windowMarginDepth (3 * K + 1) N ≤
      W * ((1 + Real.log q) * q * (1 + Real.log N)) := by
    have h := windowMarginDepth_le (θ := 1) (by linarith [zetaZeroWidth_le_three_eighths])
      (Q := 3 * K + 1) (N := N) (by omega) hN1
    rwa [Real.rpow_one, ← hq, ← hW] at h
  have hD : 160 * (Lc * (16 * T + 5)) ≤ 5 * windowMarginDepth (3 * K + 1) N := by
    unfold windowMarginDepth
    rw [← hq, ← hLc, ← hT]
    linarith [mul_nonneg hLc0 hT0]
  have h1 : (1 + Real.log q) * q * (1 + Real.log N) ≤ q * q * (8 * q * ℓ) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hq0.le) h1N (by linarith)
      (mul_nonneg hq0.le hq0.le)
  have h2 := mul_le_mul_of_nonneg_left h1 hW0
  have e : W * (q * q * (8 * q * ℓ)) = 8 * W * (q ^ 3 * ℓ) := by ring
  rw [← hq, ← hℓ, ← hW, ← hNc, ← hLc, ← hT]
  linarith

/-- The arithmetic of the sampling error: with `lq = log q`, `q ≤ 4k` and a depth
`X ≤ 40 W q³ ℓ`, the error `(lq + 1)/R · (X + 6 lq q) + lq/R²` is at most
`256 (40 W + 7) k⁴ ℓ/R`. -/
theorem sampleError_real_le {q k ℓ R W lq X : ℝ} (hq1 : 1 ≤ q) (hq4 : q ≤ 4 * k) (hℓ1 : 1 ≤ ℓ)
    (hR : 1 ≤ R) (hW0 : 0 ≤ W) (hlq0 : 0 ≤ lq) (hlq : lq ≤ q - 1) (hX0 : 0 ≤ X)
    (hX : X ≤ 40 * W * (q ^ 3 * ℓ)) :
    (lq + 1) / R * (X + 6 * (lq * q)) + lq / R ^ 2 ≤ 256 * (40 * W + 7) * (k ^ 4 * ℓ / R) := by
  have hq0 : 0 < q := by linarith
  have hR0 : 0 < R := by linarith
  have hq23 : q ^ 2 ≤ q ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hq1 (sq_nonneg q)
    rw [mul_one] at h
    calc q ^ 2 ≤ q ^ 2 * q := h
      _ = q ^ 3 := by ring
  have hq3 : 1 ≤ q ^ 3 := one_le_pow₀ hq1
  have hq3ℓ : q ^ 3 ≤ q ^ 3 * ℓ := le_mul_of_one_le_right (pow_nonneg hq0.le 3) hℓ1
  -- the two factors of the error
  have hA : (lq + 1) / R ≤ q / R := div_le_div_of_nonneg_right (by linarith) hR0.le
  have hB : X + 6 * (lq * q) ≤ (40 * W + 6) * (q ^ 3 * ℓ) := by
    have h2 : lq * q ≤ q * q := mul_le_mul_of_nonneg_right (by linarith) hq0.le
    have h3 : q * q = q ^ 2 := by ring
    linarith
  have hprod : (lq + 1) / R * (X + 6 * (lq * q)) ≤ q / R * ((40 * W + 6) * (q ^ 3 * ℓ)) :=
    mul_le_mul hA hB (add_nonneg hX0 (mul_nonneg (by norm_num) (mul_nonneg hlq0 hq0.le)))
      (div_nonneg hq0.le hR0.le)
  -- the mass term
  have hmass : lq / R ^ 2 ≤ q / R * (q ^ 3 * ℓ) := by
    have h1 : lq / R ^ 2 ≤ q / R := by
      rw [div_le_div_iff₀ (pow_pos hR0 2) hR0]
      have h5 : lq * R ≤ q * R := mul_le_mul_of_nonneg_right (by linarith) hR0.le
      have h7 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR hR0.le) hq0.le
      have e : q * (R * R) = q * R ^ 2 := by ring
      have e' : q * (R * 1) = q * R := by ring
      linarith
    have h3 : q / R ≤ q / R * (q ^ 3 * ℓ) :=
      le_mul_of_one_le_right (div_nonneg hq0.le hR0.le) (hq3.trans hq3ℓ)
    linarith
  have hq4' : q ^ 4 ≤ 256 * k ^ 4 := by
    have h := pow_le_pow_left₀ hq0.le hq4 4
    calc q ^ 4 ≤ (4 * k) ^ 4 := h
      _ = 256 * k ^ 4 := by ring
  have e1 : q / R * ((40 * W + 6) * (q ^ 3 * ℓ)) + q / R * (q ^ 3 * ℓ) =
      (40 * W + 7) * (q ^ 4 * ℓ / R) := by ring
  have h5 : (40 * W + 7) * (q ^ 4 * ℓ / R) ≤ (40 * W + 7) * (256 * k ^ 4 * ℓ / R) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hq4' (by linarith)) hR0.le) (by linarith)
  have e2 : 256 * (40 * W + 7) * (k ^ 4 * ℓ / R) = (40 * W + 7) * (256 * k ^ 4 * ℓ / R) := by
    ring
  linarith

/-- **The sampling error of the window `(R, (3K + 1)R]`** is at most
`C K⁴ (1 + log R)/R`. -/
theorem sampleError_ratio_le {K R : ℕ} (hK : 1 ≤ K) (hR : 1 ≤ R) :
    sampleError (3 * K + 1) R (3 * K * R) + Real.log ((3 * K + 1 : ℕ) : ℝ) / (R : ℝ) ^ 2 ≤
      sampleRateConst * ((K : ℝ) ^ 4 * (1 + Real.log R) / R) := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hdep := sampleDepth_le hK hR
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((3 * K + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hqK : q = 3 * K + 1 := by
    rw [hq]
    push_cast
    ring
  have hq1 : 1 ≤ q := by rw [hqK]; linarith
  have hq0 : 0 < q := by linarith
  have hq4 : q ≤ 4 * K := by rw [hqK]; linarith
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlq : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos hq0
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log R := ⟨_, rfl⟩
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ]
    linarith [Real.log_nonneg hR']
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = windowRateConst 1 := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; exact windowRateConst_nonneg 1
  obtain ⟨X, hX⟩ : ∃ X : ℝ,
      X = 160 * (logSamplingConst ((Real.log q + 1) / 2) zetaZeroWidth *
        (16 * Real.log (1 + 4 * ((R + 3 * K * R : ℕ) : ℝ) * (R : ℝ) ^ 2) + 5)) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by
    have hT : 0 ≤ Real.log (1 + 4 * ((R + 3 * K * R : ℕ) : ℝ) * (R : ℝ) ^ 2) := by
      have h : (0 : ℝ) ≤ 4 * ((R + 3 * K * R : ℕ) : ℝ) * (R : ℝ) ^ 2 := by positivity
      exact Real.log_nonneg (by linarith)
    rw [hX]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (logSamplingConst_nonneg (by linarith)) (by linarith))
  rw [← hq, ← hℓ, ← hW, ← hX] at hdep
  have hSE : sampleError (3 * K + 1) R (3 * K * R) =
      (Real.log q + 1) / R * (X + 6 * (Real.log q * q)) := by
    unfold sampleError
    rw [← hq, ← hX]
  rw [hSE, ← hq, ← hℓ]
  unfold sampleRateConst
  rw [← hW]
  exact sampleError_real_le hq1 hq4 hℓ1 hR' hW0 hlq0 hlq hX0 hdep

/-- For `R ≥ K¹⁰` the factor `K⁴ (1 + log R)/R` is at most `2/K`. -/
theorem pow_four_mul_log_div_le {K R : ℕ} (hK : 1 ≤ K) (hRK : K ^ 10 ≤ R) :
    (K : ℝ) ^ 4 * (1 + Real.log R) / R ≤ 2 / K := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  have hRK' : (K : ℝ) ^ 10 ≤ R := by exact_mod_cast hRK
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (pow_pos hK0 10) hRK'
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt R := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr hR0
  have hrr : r * r = R := by rw [hr]; exact Real.mul_self_sqrt hR0.le
  have hKr : (K : ℝ) ^ 5 ≤ r := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : r * r < (K : ℝ) ^ 5 * (K : ℝ) ^ 5 := mul_lt_mul'' hlt hlt hr0.le hr0.le
    have h2 : (K : ℝ) ^ 5 * (K : ℝ) ^ 5 = (K : ℝ) ^ 10 := by ring
    linarith
  have hlog : 1 + Real.log R ≤ 2 * r := by
    have h1 := Real.log_le_sub_one_of_pos hr0
    have h2 : Real.log R = Real.log r + Real.log r := by
      rw [← hrr, Real.log_mul hr0.ne' hr0.ne']
    linarith
  have hlogR : 0 ≤ Real.log R :=
    Real.log_nonneg (le_trans (by exact_mod_cast (Nat.one_le_pow 10 K hK)) hRK')
  rw [div_le_div_iff₀ hR0 hK0]
  calc (K : ℝ) ^ 4 * (1 + Real.log R) * K = (K : ℝ) ^ 5 * (1 + Real.log R) := by ring
    _ ≤ r * (2 * r) := mul_le_mul hKr hlog (by linarith) hr0.le
    _ = 2 * R := by rw [← hrr]; ring

/-! ### 6. The receiver -/

/-- **The margin law at polynomial block size confines the zeros.** Let `ρ(K) ≥ K¹⁰`. If for
some `θ < ½` and `C` the neutral part of every window `(ρ(K), (3K + 1)ρ(K)]` plus `C K^θ` has at
most one negative square, every zero of `ζ` has `|Re ρ − ½| ≤ θ`. -/
theorem zetaZeroWidth_le_of_neutralWindow_marginRate_of_pow_le_blockSize {θ C : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (ρ : ℕ → ℕ) (hρ : ∀ K, K ^ 10 ≤ ρ K)
    (h : ∀ K : ℕ, 1 ≤ K →
      hermNegIndex ((neutralWindow (3 * K + 1) (ρ K) (3 * K * ρ K) +
        Matrix.diagonal fun _ => C * (K : ℝ) ^ θ).map (↑) :
          Matrix (Fin (3 * K * ρ K)) (Fin (3 * K * ρ K)) ℂ) ≤ 1) :
    zetaZeroWidth ≤ θ := by
  -- constants of the two profiles
  obtain ⟨Ms, Ls, hMs, hLs⟩ := exists_bound_lipschitz contDiff_spline
    (hasCompactSupport_of_abs_lt (L := 4) fun u hu => spline_eq_zero hu)
  obtain ⟨Mp, Lp, hMp, hLp⟩ := exists_bound_lipschitz contDiff_poleFreeProfile
    (hasCompactSupport_of_abs_lt (L := 5) fun u hu => poleFreeProfile_eq_zero hu)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 2 * (Ls + Ms) + 2 * (Lp + Mp) := ⟨_, rfl⟩
  obtain ⟨S0, hS0⟩ : ∃ S, S = 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re :=
    ⟨_, rfl⟩
  obtain ⟨m₀, hm₀⟩ : ∃ m, m = ∫ u, poleFreeProfile u ^ 2 := ⟨_, rfl⟩
  obtain ⟨mU, hmU⟩ : ∃ m, m = ∫ u, spline u ^ 2 := ⟨_, rfl⟩
  obtain ⟨Bθ, hBθ⟩ : ∃ B, B = (2 * Real.exp (Real.log 3 + 12)) ^ θ := ⟨_, rfl⟩
  have hBθ0 : 0 ≤ Bθ := by rw [hBθ]; positivity
  obtain ⟨E, hE⟩ : ∃ E, E = |C| * Bθ := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hC₂0 := sampleRateConst_nonneg
  -- the lag from which the sampling error is below the allowed depth
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 20 * c₀ ^ 2 * sampleRateConst * (1 + E) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hC₂0) (by linarith)
  obtain ⟨V₁, hV₁⟩ := eventually_atTop.mp (eventually_binding_deep hθ (4 * E * mU + 1))
  refine zetaZeroWidth_le_of_eventually_lag_le hθ0 hθ (V := max V₁ (2 * Real.log (X + 1)))
    (E := 4 * E * m₀ + 1) fun v hv => ?_
  rw [← hS0]
  have hv0 : 0 ≤ v := (le_max_right _ _).trans hv
  have hvV : V₁ ≤ v := ((le_max_left _ _).trans (le_max_left _ _)).trans hv
  have hvX : 2 * Real.log (X + 1) ≤ v := ((le_max_right _ _).trans (le_max_left _ _)).trans hv
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨K, hK1, hKlog, hKle⟩ := exists_ratio_le hv0
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  -- the allowed depth at ratio 3K + 1
  obtain ⟨D, hD⟩ : ∃ D, D = |C| * (K : ℝ) ^ θ := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; exact mul_nonneg (abs_nonneg C) (Real.rpow_nonneg hK0 θ)
  have hDE : D ≤ E * Real.exp (θ * v) := by
    have hKθ : (K : ℝ) ^ θ ≤ Bθ * Real.exp (θ * v) := by
      calc (K : ℝ) ^ θ ≤ (2 * Real.exp (Real.log 3 + 12) * Real.exp v) ^ θ :=
            Real.rpow_le_rpow hK0 hKle hθ0
        _ = Bθ * Real.exp (θ * v) := by
            rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, hBθ, ← Real.exp_mul,
              mul_comm v θ]
    rw [hD, hE, mul_assoc]
    exact mul_le_mul_of_nonneg_left hKθ (abs_nonneg C)
  have hCD : C * (K : ℝ) ^ θ ≤ D := by
    rw [hD]
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hK0 θ)
  -- the smooth plane lies below −D times the mass by at least 1
  obtain ⟨hNg, hNo, -⟩ := smoothNeutral_plane v
  have hmg : (∫ u, twoEndSpline v (u - stateShift v) ^ 2) ≤ 4 * mU := by
    rw [integral_comp_sub_sq (twoEndSpline v) (stateShift v), hmU]
    exact integral_twoEndSpline_sq_le v
  have hmo : (∫ u, shiftedOdd v u ^ 2) ≤ 4 * m₀ := by
    simp only [shiftedOdd_eq]
    rw [integral_comp_sub_sq (twoEndOdd v) (stateShift v), hm₀]
    exact integral_twoEndOdd_sq_le v
  have hmg0 : 0 ≤ ∫ u, twoEndSpline v (u - stateShift v) ^ 2 :=
    integral_nonneg fun u => sq_nonneg _
  have hmo0 : 0 ≤ ∫ u, shiftedOdd v u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have he1 : 1 ≤ Real.exp (θ * v) := Real.one_le_exp (mul_nonneg hθ0 hv0)
  have hEe : 0 ≤ E * Real.exp (θ * v) := mul_nonneg hE0 (Real.exp_pos _).le
  have hDmg : D * (∫ u, twoEndSpline v (u - stateShift v) ^ 2) ≤
      4 * E * mU * Real.exp (θ * v) := by
    have := mul_le_mul hDE hmg hmg0 hEe
    linarith only [this]
  have hDmo : D * (∫ u, shiftedOdd v u ^ 2) ≤ 4 * E * m₀ * Real.exp (θ * v) := by
    have := mul_le_mul hDE hmo hmo0 hEe
    linarith only [this]
  have hg : smoothNeutral (fun u => twoEndSpline v (u - stateShift v)) +
      D * ∫ u, twoEndSpline v (u - stateShift v) ^ 2 ≤ -1 := by
    have h1 := hV₁ v hvV
    have h2 := mul_le_mul_of_nonneg_left (exp_half_le_sq v) (sq_nonneg splineCharge)
    have h4 : ((Real.exp (v / 4) + Real.exp (-(v / 4))) * splineCharge) ^ 2 =
        splineCharge ^ 2 * (Real.exp (v / 4) + Real.exp (-(v / 4))) ^ 2 := by ring
    rw [hNg]
    linarith only [h1, h2, h4, hDmg, he1]
  have ho : smoothNeutral (shiftedOdd v) + D * ∫ u, shiftedOdd v u ^ 2 ≤ -1 := by
    rw [hNo, ← hS0]
    linarith only [hcon, hDmo, he1]
  -- two negative squares at the block size ρ(K)
  have hR1 : 1 ≤ ρ K := lt_of_lt_of_le (pow_pos hK1 10) (hρ K)
  refine absurd (h K hK1) (not_le.mpr (lt_of_lt_of_le one_lt_two ?_))
  refine two_le_hermNegIndex_neutralWindow_of_plane hMs hLs hMp hLp hK1 hR1 hKlog hD0 hCD hg ho
    ?_
  -- the sampling error is below the allowed depth
  rw [← hc₀]
  have h1 := (sampleError_ratio_le hK1 hR1).trans
    (mul_le_mul_of_nonneg_left (pow_four_mul_log_div_le hK1 (hρ K)) hC₂0)
  refine (mul_le_mul_of_nonneg_left h1 (sq_nonneg c₀)).trans ?_
  have hexp : X + 1 ≤ Real.exp (v / 2) := by
    have h3 := Real.exp_le_exp.mpr (by linarith : Real.log (X + 1) ≤ v / 2)
    rwa [Real.exp_log (by linarith)] at h3
  have hθv : Real.exp (θ * v) ≤ Real.exp (v / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - θ) hv0])
  have hD1 : 1 + D ≤ (1 + E) * Real.exp (v / 2) := by
    have h3 : E * Real.exp (θ * v) ≤ E * Real.exp (v / 2) := mul_le_mul_of_nonneg_left hθv hE0
    have h4 : 1 ≤ Real.exp (v / 2) := Real.one_le_exp (by linarith)
    linarith
  have hKv : Real.exp v ≤ K := by
    have h3 : v ≤ Real.log K := by
      have h5 := le_abs_self v
      have h6 := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
      linarith
    have h4 := Real.exp_le_exp.mpr h3
    rwa [Real.exp_log hKpos] at h4
  have hee : Real.exp (v / 2) * Real.exp (v / 2) = Real.exp v := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmain : 20 * c₀ ^ 2 * sampleRateConst * (1 + D) ≤ K := by
    have h5 : 20 * c₀ ^ 2 * sampleRateConst * (1 + D) ≤
        20 * c₀ ^ 2 * sampleRateConst * ((1 + E) * Real.exp (v / 2)) :=
      mul_le_mul_of_nonneg_left hD1 (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hC₂0)
    have h6 : X * Real.exp (v / 2) ≤ Real.exp (v / 2) * Real.exp (v / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    have e : 20 * c₀ ^ 2 * sampleRateConst * ((1 + E) * Real.exp (v / 2)) =
        X * Real.exp (v / 2) := by
      rw [hX]
      ring
    linarith
  have h1D : (0 : ℝ) < 10 * (1 + D) := by linarith
  have e : c₀ ^ 2 * (sampleRateConst * (2 / (K : ℝ))) = c₀ ^ 2 * sampleRateConst * 2 / K := by
    ring
  rw [e, div_le_div_iff₀ hKpos h1D]
  linarith

/-! ### 7. The ruler -/

/-- The **margin law of rate `β`** along a block-size law `ρ`: for some `C`, the neutral part
of every window `(ρ(K), (3K + 1)ρ(K)]` plus `C K^β` has at most one negative square. -/
def MarginLaw (ρ : ℕ → ℕ) (β : ℝ) : Prop :=
  ∃ C : ℝ, ∀ K : ℕ, 1 ≤ K →
    hermNegIndex ((neutralWindow (3 * K + 1) (ρ K) (3 * K * ρ K) +
      Matrix.diagonal fun _ => C * (K : ℝ) ^ β).map (↑) :
        Matrix (Fin (3 * K * ρ K)) (Fin (3 * K * ρ K)) ℂ) ≤ 1

/-- The margin law holds at every rate above the zero width, along block sizes at most
polynomial in the ratio. -/
theorem marginLaw_of_zetaZeroWidth_lt {ρ : ℕ → ℕ} (hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K) {A : ℕ}
    (hρA : ∀ K, ρ K ≤ K ^ A) {β : ℝ} (hβ : zetaZeroWidth < β) : MarginLaw ρ β := by
  obtain ⟨C, hC⟩ := exists_neutralWindow_marginRate_of_blockSize_le_pow (θ := zetaZeroWidth)
    le_rfl (ε := β - zetaZeroWidth) (by linarith) A
  refine ⟨C, fun K hK => ?_⟩
  have h := hC K (ρ K) hK (hρ₁ K hK) (hρA K)
  have e : zetaZeroWidth + (β - zetaZeroWidth) = β := by ring
  rwa [e] at h

/-- The margin law at a nonnegative rate bounds the zero width, along block sizes at least the
tenth power of the ratio. -/
theorem zetaZeroWidth_le_of_marginLaw {ρ : ℕ → ℕ} (hρ : ∀ K, K ^ 10 ≤ ρ K) {β : ℝ}
    (hβ0 : 0 ≤ β) (h : MarginLaw ρ β) : zetaZeroWidth ≤ β := by
  rcases lt_or_ge β (1 / 2) with hlt | hge
  · obtain ⟨C, hC⟩ := h
    exact zetaZeroWidth_le_of_neutralWindow_marginRate_of_pow_le_blockSize hβ0 hlt ρ hρ hC
  · linarith [zetaZeroWidth_le_three_eighths]

/-- **The margin of the window matrices is a ruler at polynomial block size.** Along a
block-size law with `K¹⁰ ≤ ρ(K) ≤ K^A`, the zero width is at most `β` iff the margin law holds
at every rate above `β`. -/
theorem isRuler_marginLaw {ρ : ℕ → ℕ} (hρ : ∀ K, K ^ 10 ≤ ρ K) {A : ℕ}
    (hρA : ∀ K, ρ K ≤ K ^ A) :
    IsRuler zetaZeroWidth (Set.Ici 0) fun β => ∀ ε : ℝ, 0 < ε → MarginLaw ρ (β + ε) := by
  have hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K := fun K hK => lt_of_lt_of_le (pow_pos hK 10) (hρ K)
  intro β hβ
  have hβ0 : 0 ≤ β := hβ
  constructor
  · intro hw ε hε
    exact marginLaw_of_zetaZeroWidth_lt hρ₁ hρA (by linarith)
  · intro h
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact zetaZeroWidth_le_of_marginLaw hρ (by linarith) (h ε hε)

/-- The ruler along the block sizes `ρ(K) = K¹⁰`. -/
theorem isRuler_marginLaw_pow_ten :
    IsRuler zetaZeroWidth (Set.Ici 0) fun β =>
      ∀ ε : ℝ, 0 < ε → MarginLaw (fun K => K ^ 10) (β + ε) :=
  isRuler_marginLaw (ρ := fun K => K ^ 10) (fun _ => le_rfl) (A := 10) fun _ => le_rfl

/-- **The margin exponent at polynomial block size is the zero width**: along a block-size law
with `K¹⁰ ≤ ρ(K) ≤ K^A`, the infimum of the nonnegative rates of the margin law is
`sup |Re ρ − ½|`. -/
theorem sInf_marginLaw_eq_zetaZeroWidth {ρ : ℕ → ℕ} (hρ : ∀ K, K ^ 10 ≤ ρ K) {A : ℕ}
    (hρA : ∀ K, ρ K ≤ K ^ A) :
    sInf {β : ℝ | 0 ≤ β ∧ MarginLaw ρ β} = zetaZeroWidth := by
  have hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K := fun K hK => lt_of_lt_of_le (pow_pos hK 10) (hρ K)
  have hw0 := zetaZeroWidth_nonneg
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroWidth + ε ∈ {β : ℝ | 0 ≤ β ∧ MarginLaw ρ β} :=
    fun ε hε => ⟨by linarith, marginLaw_of_zetaZeroWidth_lt hρ₁ hρA (by linarith)⟩
  have hbdd : BddBelow {β : ℝ | 0 ≤ β ∧ MarginLaw ρ β} := ⟨0, fun β hβ => hβ.1⟩
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => csInf_le hbdd (hmem ε hε)) ?_
  exact le_csInf ⟨_, hmem 1 one_pos⟩ fun β hβ => zetaZeroWidth_le_of_marginLaw hρ hβ.1 hβ.2

#print axioms zetaZeroWidth_le_of_neutralWindow_marginRate_of_pow_le_blockSize
#print axioms isRuler_marginLaw
#print axioms sInf_marginLaw_eq_zetaZeroWidth

end

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
