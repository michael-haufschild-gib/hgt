import Mathlib

/-!
# The Bailey–Borwein–Plouffe series for `π`

`π = Σ_{k ≥ 0} 16⁻ᵏ (4/(8k+1) − 2/(8k+4) − 1/(8k+5) − 1/(8k+6))`.

The power series `Φ(t) = Σ_k 16⁻ᵏ (4t^{8k+1}/(8k+1) − 2t^{8k+4}/(8k+4) − t^{8k+5}/(8k+5) −
t^{8k+6}/(8k+6))` converges on `|t| < 5/4` with derivative
`(4 − 2t³ − t⁴ − t⁵)/(1 − t⁸/16) = 16(1 − t)/((2 − t²)(t² − 2t + 2))`, which is also the derivative
of `G(t) = 2 log(2 − t²) − 2 log(t² − 2t + 2) + 4 arctan(t − 1) + π`.  Both vanish at `0`, so
`Φ(1) = G(1) = π`.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry.BBPPi

/-- The `k`-th BBP coefficient `4/(8k+1) − 2/(8k+4) − 1/(8k+5) − 1/(8k+6)`. -/
noncomputable def bbpTerm (k : ℕ) : ℝ :=
  4 / (8 * k + 1) - 2 / (8 * k + 4) - 1 / (8 * k + 5) - 1 / (8 * k + 6)

/-- The `k`-th block of the BBP power series. -/
noncomputable def bbpPiece (k : ℕ) (t : ℝ) : ℝ :=
  (1 / 16) ^ k * (4 * t ^ (8 * k + 1) / (8 * k + 1) - 2 * t ^ (8 * k + 4) / (8 * k + 4) -
    t ^ (8 * k + 5) / (8 * k + 5) - t ^ (8 * k + 6) / (8 * k + 6))

/-- The derivative of the `k`-th block. -/
noncomputable def bbpPieceDeriv (k : ℕ) (t : ℝ) : ℝ :=
  (1 / 16) ^ k * (4 * t ^ (8 * k) - 2 * t ^ (8 * k + 3) - t ^ (8 * k + 4) - t ^ (8 * k + 5))

theorem hasDerivAt_pow_div (m : ℕ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ (m + 1) / ((m : ℝ) + 1)) (t ^ m) t := by
  have h := (hasDerivAt_pow (m + 1) t).div_const ((m : ℝ) + 1)
  refine h.congr_deriv ?_
  have : (m : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.add_sub_cancel]
  push_cast
  field_simp

theorem hasDerivAt_bbpPiece (k : ℕ) (t : ℝ) :
    HasDerivAt (bbpPiece k) (bbpPieceDeriv k t) t := by
  have h1 := hasDerivAt_pow_div (8 * k) t
  have h4 := hasDerivAt_pow_div (8 * k + 3) t
  have h5 := hasDerivAt_pow_div (8 * k + 4) t
  have h6 := hasDerivAt_pow_div (8 * k + 5) t
  have h := (((h1.const_mul 4).sub (h4.const_mul 2)).sub h5).sub h6
  have h' := h.const_mul ((1 / 16 : ℝ) ^ k)
  refine (h'.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [bbpPiece, Pi.sub_apply]
    push_cast
    ring_nf
  · simp only [bbpPieceDeriv]

/-- The convergence ratio `(5/4)⁸/16 < 1`. -/
theorem bbp_ratio_lt_one : (5 / 4 : ℝ) ^ 8 / 16 < 1 := by norm_num

theorem abs_bbpPieceDeriv_le (k : ℕ) {t : ℝ} (ht : |t| < 5 / 4) :
    |bbpPieceDeriv k t| ≤ 32 * ((5 / 4 : ℝ) ^ 8 / 16) ^ k := by
  have ha : |t| ≤ 5 / 4 := ht.le
  have hpow : ∀ j : ℕ, |t| ^ (8 * k + j) ≤ (5 / 4 : ℝ) ^ (8 * k) * (5 / 4) ^ j := fun j => by
    rw [← pow_add]
    exact pow_le_pow_left₀ (abs_nonneg t) ha _
  have h0 : |t| ^ (8 * k) ≤ (5 / 4 : ℝ) ^ (8 * k) := pow_le_pow_left₀ (abs_nonneg t) ha _
  have h3 := hpow 3
  have h4 := hpow 4
  have h5 := hpow 5
  have hk : (5 / 4 : ℝ) ^ (8 * k) * (1 / 16) ^ k = ((5 / 4 : ℝ) ^ 8 / 16) ^ k := by
    rw [pow_mul, ← mul_pow]; ring_nf
  have hnn : (0 : ℝ) ≤ (5 / 4) ^ (8 * k) := by positivity
  unfold bbpPieceDeriv
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 16) ^ k)]
  have hin : |4 * t ^ (8 * k) - 2 * t ^ (8 * k + 3) - t ^ (8 * k + 4) - t ^ (8 * k + 5)| ≤
      32 * (5 / 4 : ℝ) ^ (8 * k) := by
    calc _ ≤ |4 * t ^ (8 * k)| + |2 * t ^ (8 * k + 3)| + |t ^ (8 * k + 4)| + |t ^ (8 * k + 5)| := by
          have e1 := abs_sub (4 * t ^ (8 * k) - 2 * t ^ (8 * k + 3) - t ^ (8 * k + 4))
            (t ^ (8 * k + 5))
          have e2 := abs_sub (4 * t ^ (8 * k) - 2 * t ^ (8 * k + 3)) (t ^ (8 * k + 4))
          have e3 := abs_sub (4 * t ^ (8 * k)) (2 * t ^ (8 * k + 3))
          linarith
      _ = 4 * |t| ^ (8 * k) + 2 * |t| ^ (8 * k + 3) + |t| ^ (8 * k + 4) + |t| ^ (8 * k + 5) := by
          simp [abs_mul, abs_pow]
      _ ≤ 4 * (5 / 4 : ℝ) ^ (8 * k) + 2 * ((5 / 4 : ℝ) ^ (8 * k) * (5 / 4) ^ 3) +
            (5 / 4 : ℝ) ^ (8 * k) * (5 / 4) ^ 4 + (5 / 4 : ℝ) ^ (8 * k) * (5 / 4) ^ 5 := by
          linarith
      _ ≤ 32 * (5 / 4 : ℝ) ^ (8 * k) := by nlinarith
  calc (1 / 16 : ℝ) ^ k * |4 * t ^ (8 * k) - 2 * t ^ (8 * k + 3) - t ^ (8 * k + 4) -
        t ^ (8 * k + 5)| ≤ (1 / 16) ^ k * (32 * (5 / 4 : ℝ) ^ (8 * k)) :=
        mul_le_mul_of_nonneg_left hin (by positivity)
    _ = 32 * ((5 / 4 : ℝ) ^ 8 / 16) ^ k := by rw [← hk]; ring

theorem summable_bbpBound : Summable fun k : ℕ => 32 * ((5 / 4 : ℝ) ^ 8 / 16) ^ k :=
  (summable_geometric_of_lt_one (by positivity) bbp_ratio_lt_one).mul_left _

/-- The derivative series sums to `(4 − 2t³ − t⁴ − t⁵)/(1 − t⁸/16)`. -/
theorem tsum_bbpPieceDeriv {t : ℝ} (ht : |t| < 5 / 4) :
    ∑' k, bbpPieceDeriv k t = (4 - 2 * t ^ 3 - t ^ 4 - t ^ 5) * (1 - t ^ 8 / 16)⁻¹ := by
  have hr0 : 0 ≤ t ^ 8 / 16 := by positivity
  have hr1 : t ^ 8 / 16 < 1 := by
    have h8 : t ^ 8 ≤ (5 / 4 : ℝ) ^ 8 := by
      rw [show t ^ 8 = |t| ^ 8 by rw [pow_abs, abs_of_nonneg (by positivity)]]
      exact pow_le_pow_left₀ (abs_nonneg t) ht.le 8
    have := bbp_ratio_lt_one
    linarith [div_le_div_of_nonneg_right h8 (by norm_num : (0 : ℝ) ≤ 16)]
  have he : ∀ k, bbpPieceDeriv k t = (4 - 2 * t ^ 3 - t ^ 4 - t ^ 5) * (t ^ 8 / 16) ^ k := by
    intro k
    have hp : (t ^ 8 / 16) ^ k = (1 / 16) ^ k * t ^ (8 * k) := by
      rw [div_pow, ← pow_mul, div_eq_mul_one_div (t ^ (8 * k)), one_div_pow]
      ring
    unfold bbpPieceDeriv
    rw [hp]
    ring
  simp_rw [he]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]

/-- The BBP power series. -/
noncomputable def bbpSeries (t : ℝ) : ℝ := ∑' k, bbpPiece k t

theorem hasDerivAt_bbpSeries {t : ℝ} (ht : |t| < 5 / 4) :
    HasDerivAt bbpSeries ((4 - 2 * t ^ 3 - t ^ 4 - t ^ 5) * (1 - t ^ 8 / 16)⁻¹) t := by
  have hopen : IsOpen (Set.Ioo (-(5 / 4 : ℝ)) (5 / 4)) := isOpen_Ioo
  have hmem : ∀ {y : ℝ}, |y| < 5 / 4 → y ∈ Set.Ioo (-(5 / 4 : ℝ)) (5 / 4) := fun {y} hy =>
    ⟨by linarith [neg_abs_le y], lt_of_le_of_lt (le_abs_self y) hy⟩
  have h := hasDerivAt_tsum_of_isPreconnected summable_bbpBound hopen
    (isPreconnected_Ioo (a := -(5 / 4 : ℝ)) (b := 5 / 4))
    (g := bbpPiece) (g' := bbpPieceDeriv) (fun k y _ => hasDerivAt_bbpPiece k y)
    (fun k y hy => by
      rw [Real.norm_eq_abs]
      exact abs_bbpPieceDeriv_le k (abs_lt.mpr ⟨by linarith [hy.1], hy.2⟩))
    (y₀ := 0) (hmem (by norm_num)) (by simp [bbpPiece]) (hmem ht)
  rw [tsum_bbpPieceDeriv ht] at h
  exact h

/-- The closed form `2 log(2 − t²) − 2 log(t² − 2t + 2) + 4 arctan(t − 1) + π`. -/
noncomputable def bbpClosedForm (t : ℝ) : ℝ :=
  2 * Real.log (2 - t ^ 2) - 2 * Real.log (t ^ 2 - 2 * t + 2) + 4 * Real.arctan (t - 1) + Real.pi

theorem hasDerivAt_bbpClosedForm {t : ℝ} (ht : |t| < 5 / 4) :
    HasDerivAt bbpClosedForm ((4 - 2 * t ^ 3 - t ^ 4 - t ^ 5) * (1 - t ^ 8 / 16)⁻¹) t := by
  have ht2 : t ^ 2 < 25 / 16 := by
    have := abs_lt.mp ht
    nlinarith
  have hA : 2 - t ^ 2 ≠ 0 := by nlinarith
  have hB : t ^ 2 - 2 * t + 2 ≠ 0 := by nlinarith [sq_nonneg (t - 1)]
  have hC : 1 - t ^ 8 / 16 ≠ 0 := by
    have : t ^ 8 < 16 := by
      have h4 : t ^ 4 < 4 := by nlinarith
      have h40 : 0 ≤ t ^ 4 := by positivity
      have e : t ^ 8 = t ^ 4 * t ^ 4 := by ring
      rw [e]
      nlinarith
    intro h
    have : t ^ 8 = 16 := by linarith
    linarith
  have d1 := ((hasDerivAt_pow 2 t).const_sub 2).log hA
  have d2 := (((hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul 2)).add_const 2).log hB
  have d3 := ((hasDerivAt_id t).sub_const 1).arctan
  have d := (((d1.const_mul 2).sub (d2.const_mul 2)).add (d3.const_mul 4)).add_const Real.pi
  refine (d.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [bbpClosedForm, Pi.sub_apply, Pi.add_apply, id]
  · have hP : (2 + t ^ 2) * (t ^ 2 + 2 * t + 2) ≠ 0 := by
      have : 0 < t ^ 2 + 2 * t + 2 := by nlinarith [sq_nonneg (t + 1)]
      positivity
    have key : (4 - 2 * t ^ 3 - t ^ 4 - t ^ 5) * (1 - t ^ 8 / 16)⁻¹ =
        -4 * t / (2 - t ^ 2) + (8 - 4 * t) / (t ^ 2 - 2 * t + 2) := by
      rw [div_add_div _ _ hA hB, ← div_eq_mul_inv, div_eq_div_iff hC (mul_ne_zero hA hB)]
      ring
    rw [key]
    simp only [Pi.sub_apply, id]
    rw [show 1 + (t - 1) ^ 2 = t ^ 2 - 2 * t + 2 by ring]
    push_cast
    field_simp
    ring

theorem bbpSeries_zero : bbpSeries 0 = 0 := by simp [bbpSeries, bbpPiece]

theorem bbpClosedForm_zero : bbpClosedForm 0 = 0 := by
  unfold bbpClosedForm
  rw [show (0 : ℝ) - 1 = -1 by norm_num, Real.arctan_neg, Real.arctan_one]
  norm_num
  ring

theorem bbpClosedForm_one : bbpClosedForm 1 = Real.pi := by
  simp [bbpClosedForm]
  norm_num

theorem bbpSeries_one : bbpSeries 1 = Real.pi := by
  have hab : (0 : ℝ) < 1 := one_pos
  have hd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |x| < 5 / 4 := fun x hx => by
    rw [abs_of_nonneg hx.1]; linarith [hx.2]
  have hcont : ContinuousOn (fun x => bbpSeries x - bbpClosedForm x) (Set.Icc 0 1) :=
    fun x hx => ((hasDerivAt_bbpSeries (hd x hx)).sub
      (hasDerivAt_bbpClosedForm (hd x hx))).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun x => bbpSeries x - bbpClosedForm x) 0 x := fun x hx => by
    have h := (hasDerivAt_bbpSeries (hd x (Set.Ioo_subset_Icc_self hx))).sub
      (hasDerivAt_bbpClosedForm (hd x (Set.Ioo_subset_Icc_self hx)))
    rwa [sub_self] at h
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun x => bbpSeries x - bbpClosedForm x)
    (fun _ => 0) hab hcont hderiv
  rw [bbpSeries_zero, bbpClosedForm_zero, bbpClosedForm_one] at hslope
  simp only [sub_zero, div_one] at hslope
  linarith

theorem bbpTerm_nonneg (k : ℕ) : 0 ≤ bbpTerm k := by
  unfold bbpTerm
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have a : (4 : ℝ) / (8 * k + 4) ≤ 4 / (8 * k + 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have b : 1 / (8 * (k : ℝ) + 5) ≤ 1 / (8 * k + 4) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have c : 1 / (8 * (k : ℝ) + 6) ≤ 1 / (8 * k + 4) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have e : (4 : ℝ) / (8 * k + 4) = 1 / (8 * k + 4) + 1 / (8 * k + 4) + 2 / (8 * k + 4) := by ring
  linarith

theorem bbpTerm_le (k : ℕ) : bbpTerm k ≤ 4 / (8 * k + 1) := by
  unfold bbpTerm
  have : (0 : ℝ) ≤ 2 / (8 * k + 4) := by positivity
  have : (0 : ℝ) ≤ 1 / (8 * k + 5) := by positivity
  have : (0 : ℝ) ≤ 1 / (8 * k + 6) := by positivity
  linarith

theorem bbpTerm_le_four (k : ℕ) : bbpTerm k ≤ 4 := by
  refine (bbpTerm_le k).trans ?_
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * k + 1)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

theorem summable_bbp : Summable fun k : ℕ => (1 / 16 : ℝ) ^ k * bbpTerm k :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (bbpTerm_nonneg k))
    (fun k => by
      have := bbpTerm_le_four k
      have h16 : (0 : ℝ) ≤ (1 / 16) ^ k := by positivity
      show (1 / 16 : ℝ) ^ k * bbpTerm k ≤ 4 * (1 / 16) ^ k
      nlinarith)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4)

/-- **The Bailey–Borwein–Plouffe formula.** -/
theorem hasSum_bbp : HasSum (fun k : ℕ => (1 / 16 : ℝ) ^ k * bbpTerm k) Real.pi := by
  have h := summable_bbp.hasSum
  convert h using 1
  rw [← bbpSeries_one]
  unfold bbpSeries
  refine tsum_congr fun k => ?_
  simp only [bbpPiece, bbpTerm, one_pow, mul_one]

theorem bbp_formula :
    Real.pi = ∑' k : ℕ, (1 / 16 : ℝ) ^ k *
      (4 / (8 * k + 1) - 2 / (8 * k + 4) - 1 / (8 * k + 5) - 1 / (8 * k + 6)) :=
  hasSum_bbp.tsum_eq.symm

end GaloisForLFunctions.HTGeometry.BBPPi
