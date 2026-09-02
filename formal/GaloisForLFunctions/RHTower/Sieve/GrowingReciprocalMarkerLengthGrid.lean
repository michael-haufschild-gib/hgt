import GaloisForLFunctions.RHTower.Sieve.MovingWindowLengthGrid
import GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerNormalizationError

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- Slowly growing number of length cells used by the normalization grid. -/
def growingReciprocalMarkerGridBreadth (x : ℝ) : ℕ :=
  ⌈Real.log (Real.log x)⌉₊

/-- Natural mesh chosen so the length grid has at most `log log x` cells. -/
def growingReciprocalMarkerGridMesh (x : ℝ) : ℕ :=
  ⌈growingReciprocalMarkerH x⌉₊ / growingReciprocalMarkerGridBreadth x + 1

theorem growingReciprocalMarkerGridMesh_pos (x : ℝ) :
    0 < growingReciprocalMarkerGridMesh x := by
  change 0 < (⌈growingReciprocalMarkerH x⌉₊ /
    growingReciprocalMarkerGridBreadth x : ℕ) + 1
  exact Nat.zero_lt_succ _

theorem tendsto_growingReciprocalMarkerGridBreadth_atTop :
    Tendsto (fun x : ℝ => (growingReciprocalMarkerGridBreadth x : ℝ)) atTop atTop := by
  have hll : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [hll.eventually_ge_atTop b] with x hx
  exact hx.trans (Nat.le_ceil _)

theorem tendsto_growingReciprocalMarkerGridMesh_div_h :
    Tendsto (fun x : ℝ =>
      (growingReciprocalMarkerGridMesh x : ℝ) / growingReciprocalMarkerH x)
      atTop (𝓝 0) := by
  have hinvK : Tendsto (fun x : ℝ =>
      1 / (growingReciprocalMarkerGridBreadth x : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop.comp tendsto_growingReciprocalMarkerGridBreadth_atTop
  have hinvH : Tendsto (fun x : ℝ => 1 / growingReciprocalMarkerH x) atTop (𝓝 0) :=
    tendsto_one_div_atTop.comp tendsto_growingReciprocalMarkerH_atTop
  have hmajor : Tendsto (fun x : ℝ =>
      (1 + 1 / growingReciprocalMarkerH x) *
          (1 / (growingReciprocalMarkerGridBreadth x : ℝ)) +
        1 / growingReciprocalMarkerH x) atTop (𝓝 0) := by
    have hone : Tendsto (fun _x : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [add_zero, one_mul, mul_zero, zero_add] using
      (hone.add hinvH).mul hinvK |>.add hinvH
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards with x
    exact div_nonneg (by positivity) (growingReciprocalMarkerH_pos x).le
  · filter_upwards [
      tendsto_growingReciprocalMarkerGridBreadth_atTop.eventually_gt_atTop (0 : ℝ)] with x hK
    have hH0 : 0 < growingReciprocalMarkerH x := growingReciprocalMarkerH_pos x
    have hKnat : 0 < growingReciprocalMarkerGridBreadth x := by exact_mod_cast hK
    have hceil : (⌈growingReciprocalMarkerH x⌉₊ : ℝ)
        < growingReciprocalMarkerH x + 1 := Nat.ceil_lt_add_one hH0.le
    have hdiv : ((⌈growingReciprocalMarkerH x⌉₊ /
          growingReciprocalMarkerGridBreadth x : ℕ) : ℝ)
        ≤ (⌈growingReciprocalMarkerH x⌉₊ : ℝ) /
          (growingReciprocalMarkerGridBreadth x : ℝ) := Nat.cast_div_le
    have hdiv' : ((⌈growingReciprocalMarkerH x⌉₊ /
          growingReciprocalMarkerGridBreadth x : ℕ) : ℝ)
        < (growingReciprocalMarkerH x + 1) /
          (growingReciprocalMarkerGridBreadth x : ℝ) :=
      hdiv.trans_lt (div_lt_div_of_pos_right hceil (by exact_mod_cast hKnat))
    have hmesh : (growingReciprocalMarkerGridMesh x : ℝ)
        ≤ (growingReciprocalMarkerH x + 1) /
            (growingReciprocalMarkerGridBreadth x : ℝ) + 1 := by
      rw [growingReciprocalMarkerGridMesh]
      push_cast
      linarith
    have hquot := div_le_div_of_nonneg_right hmesh hH0.le
    calc
      (growingReciprocalMarkerGridMesh x : ℝ) / growingReciprocalMarkerH x
          ≤ ((growingReciprocalMarkerH x + 1) /
              (growingReciprocalMarkerGridBreadth x : ℝ) + 1) /
              growingReciprocalMarkerH x := hquot
      _ = (1 + 1 / growingReciprocalMarkerH x) *
            (1 / (growingReciprocalMarkerGridBreadth x : ℝ)) +
          1 / growingReciprocalMarkerH x := by
        field_simp [ne_of_gt hH0, Nat.cast_ne_zero.mpr (ne_of_gt hKnat)]

theorem eventually_card_growingReciprocalMarkerLengthGrid_le_breadth :
    ∀ᶠ x : ℝ in atTop,
      ((Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊).image
        (lengthGridQuantizer (growingReciprocalMarkerGridMesh x)
          (movingFibreWindowLength x (growingReciprocalMarkerH x)))).card
        ≤ growingReciprocalMarkerGridBreadth x := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    tendsto_growingReciprocalMarkerGridBreadth_atTop.eventually_gt_atTop (0 : ℝ)] with x hx hK
  have hKnat : 0 < growingReciprocalMarkerGridBreadth x := by exact_mod_cast hK
  have hcard := card_movingLengthGrid_le x (growingReciprocalMarkerH x) hx
    (growingReciprocalMarkerH_pos x).le (growingReciprocalMarkerGridMesh x)
  have hdecomp := Nat.div_add_mod ⌈growingReciprocalMarkerH x⌉₊
    (growingReciprocalMarkerGridBreadth x)
  have hmod := Nat.mod_lt ⌈growingReciprocalMarkerH x⌉₊ hKnat
  have hmul : ⌈growingReciprocalMarkerH x⌉₊ <
      (⌈growingReciprocalMarkerH x⌉₊ / growingReciprocalMarkerGridBreadth x + 1) *
        growingReciprocalMarkerGridBreadth x := by
    calc
      ⌈growingReciprocalMarkerH x⌉₊ =
          growingReciprocalMarkerGridBreadth x *
              (⌈growingReciprocalMarkerH x⌉₊ / growingReciprocalMarkerGridBreadth x) +
            ⌈growingReciprocalMarkerH x⌉₊ % growingReciprocalMarkerGridBreadth x := by
        exact hdecomp.symm
      _ < growingReciprocalMarkerGridBreadth x *
              (⌈growingReciprocalMarkerH x⌉₊ / growingReciprocalMarkerGridBreadth x) +
            growingReciprocalMarkerGridBreadth x := Nat.add_lt_add_left hmod _
      _ = (⌈growingReciprocalMarkerH x⌉₊ / growingReciprocalMarkerGridBreadth x + 1) *
            growingReciprocalMarkerGridBreadth x := by
        rw [Nat.add_mul]
        simp only [one_mul, Nat.mul_comm]
  have hquot : ⌈growingReciprocalMarkerH x⌉₊ /
      growingReciprocalMarkerGridMesh x < growingReciprocalMarkerGridBreadth x := by
    apply Nat.div_lt_of_lt_mul
    simpa [growingReciprocalMarkerGridMesh] using hmul
  omega

theorem tendsto_growingReciprocalMarkerGridQuantizationError :
    Tendsto (fun x : ℝ =>
      (((Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊).card : ℝ) *
          (growingReciprocalMarkerGridMesh x : ℝ) ^ 2) /
        (growingReciprocalMarkerH x ^ 2 * Real.sqrt x)) atTop (𝓝 0) := by
  have hsqrtTop : Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop :=
    Real.tendsto_sqrt_atTop
  have hinvSqrt : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_one_div_atTop.comp hsqrtTop
  have hfactor : Tendsto (fun x : ℝ => (Real.sqrt x + 2) / Real.sqrt x)
      atTop (𝓝 1) := by
    have hone : Tendsto (fun _x : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have htwo : Tendsto (fun _x : ℝ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    have hlim : Tendsto (fun x : ℝ => 1 + 2 * (1 / Real.sqrt x)) atTop (𝓝 1) := by
      simpa using hone.add (htwo.mul hinvSqrt)
    exact hlim.congr' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hs0 : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
      rw [eq_div_iff hs0]
      field_simp [hs0])
  have hmesh2 := tendsto_growingReciprocalMarkerGridMesh_div_h.pow 2
  have hmajor := hfactor.mul hmesh2
  simp only [one_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hmajor
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    have hceil : (⌈Real.sqrt x⌉₊ : ℝ) < Real.sqrt x + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg x)
    have hcard : (((Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊).card : ℕ) : ℝ)
        ≤ Real.sqrt x + 2 := by
      have hraw := card_Icc_cast_le
        (a := ⌈Real.sqrt x / 2⌉₊) (b := ⌈Real.sqrt x⌉₊)
        (r := 0) (s := Real.sqrt x + 1)
        (by positivity) hceil.le (by nlinarith [Real.sqrt_nonneg x])
      convert hraw using 1
      ring
    have hnum := mul_le_mul_of_nonneg_right hcard
      (sq_nonneg (growingReciprocalMarkerGridMesh x : ℝ))
    have hden : 0 < growingReciprocalMarkerH x ^ 2 * Real.sqrt x :=
      mul_pos (sq_pos_of_pos (growingReciprocalMarkerH_pos x)) hs0
    have hdiv := div_le_div_of_nonneg_right hnum hden.le
    calc
      (((Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊).card : ℝ) *
          (growingReciprocalMarkerGridMesh x : ℝ) ^ 2) /
          (growingReciprocalMarkerH x ^ 2 * Real.sqrt x)
        ≤ ((Real.sqrt x + 2) * (growingReciprocalMarkerGridMesh x : ℝ) ^ 2) /
          (growingReciprocalMarkerH x ^ 2 * Real.sqrt x) := hdiv
      _ = (Real.sqrt x + 2) / Real.sqrt x *
          ((growingReciprocalMarkerGridMesh x : ℝ) /
            growingReciprocalMarkerH x) ^ 2 := by
        field_simp [ne_of_gt hs0, ne_of_gt (growingReciprocalMarkerH_pos x)]

/-- Exact finite normalization at the card's growing low-breadth grid schedule. -/
theorem sum_innerFibre_sq_le_growingReciprocalMarkerGrid (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) {x : ℝ} (hx : 4 < x) :
    (∑ a ∈ outerBlock x (growingReciprocalMarkerH x),
        (∑ b ∈ innerFibre x (growingReciprocalMarkerH x) a, f b) ^ 2)
      ≤ 16 * ∑ ℓ ∈
          (Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊).image
            (lengthGridQuantizer (growingReciprocalMarkerGridMesh x)
              (movingFibreWindowLength x (growingReciprocalMarkerH x))),
            dyadicMeanSquare f ℓ (⌈Real.sqrt x / 2⌉₊ - 1) (⌈Real.sqrt x⌉₊ - 1)
        + 16 * ((Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊).card : ℝ) *
            (growingReciprocalMarkerGridMesh x : ℝ) ^ 2
        + 2 * ((outerBlock x (growingReciprocalMarkerH x)).card : ℝ) *
            (growingReciprocalMarkerH x / Real.sqrt x + 2) ^ 2 := by
  exact sum_innerFibre_sq_le_lengthGridPartition f hf hx
    (growingReciprocalMarkerH_pos x).le (growingReciprocalMarkerGridMesh x)
    (growingReciprocalMarkerGridMesh_pos x)

end

end RHTower.Sieve
