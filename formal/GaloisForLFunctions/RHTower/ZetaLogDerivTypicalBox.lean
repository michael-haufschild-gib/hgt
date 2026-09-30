import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalScale

/-!
# `ζ'/ζ` on a box at a typical height

*Log-derivative scale data* `ZetaLogDerivScaleData t R B` at height `t` and scale `R` are:

* every zero `w` of `ζ` with `Re w > ½ + R/2` satisfies `|Im w − t| > (Re w − ½) + 12R`;
* `|ζ'/ζ(s)| ≤ B` on the box `½ + 3R/4 ≤ Re s ≤ ½ + 6R`, `|Im s − t| ≤ 6R`.

They follow at a height `t ∈ [T, 2T]` from Selberg's explicit formula at `t` with remainder `≤ 1`
(`zetaLogDerivScaleData_of_good`) when

* no zero `w` of the fixed rectangle with `Re w > ½ + R/2` has `|Im w − t| ≤ W(w) = 12R x^{3(Re w − ½)}`,
  and `36 R log x ≥ 1`;
* `|D_x| ≤ M_D` on the box,

with `B = 1 + M_D + (2306 x^{−R/4}/log x) Λ(t) + F(t)`, where `Λ` is the Lorentzian sum of the
rectangle at width `R/4` and `F` its far-right majorant.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

open Sieve

/-- **Log-derivative scale data** at height `t`, scale `R` and level `B`. -/
structure ZetaLogDerivScaleData (t R B : ℝ) : Prop where
  zeroFree : ∀ w : ℂ, riemannZeta w = 0 → 1 / 2 + R / 2 < w.re →
    (w.re - 1 / 2) + 12 * R < |w.im - t|
  logDeriv : ∀ s : ℂ, 1 / 2 + 3 * R / 4 ≤ s.re → s.re ≤ 1 / 2 + 6 * R → |s.im - t| ≤ 6 * R →
    ‖logDeriv riemannZeta s‖ ≤ B

theorem reflectedLeftAbscissa_le_half {T : ℝ} (hT : 16 ≤ T) : reflectedLeftAbscissa T ≤ 1 / 2 := by
  have h := reflectedLeftAbscissa_le hT
  have hl := log_ge_of_sixteen_le hT
  have : 1 / (8 * Real.log T ^ (9 : ℕ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ^ 9 ≤ Real.log T ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) hl 9
    linarith
  linarith

/-- A zero of `ζ` right of the line and within height `2` of `t ∈ [T, 2T]` lies in the fixed
rectangle. -/
theorem mem_selbergMidZeros_of_zero {T t : ℝ} (hT : 16 ≤ T) (ht : t ∈ Icc T (2 * T)) {w : ℂ}
    (hζ : riemannZeta w = 0) (hre : 1 / 2 ≤ w.re) (him : |w.im - t| ≤ 2) :
    w ∈ selbergMidZeros T := by
  have hre1 : w.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hζ
  have hw1 : w ≠ 1 := by
    intro h; rw [h] at hre1; simp at hre1
  rw [selbergMidZeros, mem_zetaResidueUnitClosedRectangleZeros]
  refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, (zetaResidueUnit_eq_zero_iff hw1).2 hζ⟩
  · have hσ := reflectedLeftAbscissa_le_half (show 16 ≤ 4 * T by linarith)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, Complex.re_ofNat, zero_mul]
    rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith, by linarith⟩
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.im_ofNat, add_zero]
    rw [uIcc_of_le (by linarith [ht.1])]
    have := abs_le.mp him
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **Zero-free region from the exclusion windows.** -/
theorem zeroFree_of_windows {T t x R : ℝ} (hT : 16 ≤ T) (ht : t ∈ Icc T (2 * T)) (hx : 1 < x)
    (hR : 0 < R) (hR16 : R ≤ 1 / 16) (hRx : 1 ≤ 36 * R * Real.log x)
    (hgood : ∀ w ∈ selbergMidZeros T, 1 / 2 + R / 2 < w.re →
      selbergRightWindow x R w < |w.im - t|) :
    ∀ w : ℂ, riemannZeta w = 0 → 1 / 2 + R / 2 < w.re → (w.re - 1 / 2) + 12 * R < |w.im - t| := by
  intro w hζ hre
  by_contra hle
  push Not at hle
  have hre1 : w.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hζ
  have hmem := mem_selbergMidZeros_of_zero hT ht hζ (by linarith) (by linarith)
  have hW := hgood w hmem hre
  have hl := Real.log_pos hx
  have hb : 0 ≤ w.re - 1 / 2 := by linarith
  have hWge : (w.re - 1 / 2) + 12 * R ≤ selbergRightWindow x R w := by
    unfold selbergRightWindow
    have h1 : 1 + 3 * (w.re - 1 / 2) * Real.log x ≤ Real.exp (3 * (w.re - 1 / 2) * Real.log x) :=
      by linarith [Real.add_one_le_exp (3 * (w.re - 1 / 2) * Real.log x)]
    have h2 : 12 * R * (1 + 3 * (w.re - 1 / 2) * Real.log x) ≤
        12 * R * Real.exp (3 * (w.re - 1 / 2) * Real.log x) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  linarith

/-- **The box bound from the explicit formula.** -/
theorem norm_logDeriv_zeta_le_of_good {T t x R T₁ T₂ M_D : ℝ} (hT : 64 ≤ T)
    (ht : t ∈ Icc T (2 * T)) (hx : 1 < x) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (hT₁ : t / 2 - 1 < T₁) (hT₂ : T₂ < 3 * t / 2 + 1) (hT12 : T₁ ≤ T₂)
    (hEF : ∀ s₀ : ℂ, |s₀.im - t| ≤ t / 8 → 1 / 2 ≤ s₀.re → s₀.re ≤ 1 → riemannZeta s₀ ≠ 0 →
      ‖logDeriv riemannZeta s₀ + selbergVonMangoldtPoly x s₀ +
        ∑ w ∈ selbergHeightZeros t T₁ T₂,
          ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s₀)‖ ≤ 1)
    (hgood : ∀ w ∈ selbergMidZeros T, 1 / 2 + R / 2 < w.re →
      selbergRightWindow x R w < |w.im - t|)
    (hD : ∀ z : ℂ, 1 / 2 + 3 * R / 4 ≤ z.re → z.re ≤ 1 / 2 + 6 * R → |z.im - t| ≤ 6 * R →
      ‖selbergVonMangoldtPoly x z‖ ≤ M_D)
    {s : ℂ} (hs1 : 1 / 2 + 3 * R / 4 ≤ s.re) (hs2 : s.re ≤ 1 / 2 + 6 * R)
    (hst : |s.im - t| ≤ 6 * R) (hζs : riemannZeta s ≠ 0) :
    ‖logDeriv riemannZeta s‖ ≤ 1 + M_D +
      2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 *
        selbergLorentzSum (selbergMidZeros T) (R / 4) t +
      selbergRightFar (selbergMidZeros T) x R t := by
  have ht64 : 64 ≤ t := le_trans hT ht.1
  have hsub := selbergHeightZeros_subset_mid (by linarith) ht hT₁ hT₂ hT12
  set Z := selbergHeightZeros t T₁ T₂ with hZ
  have hEFs := hEF s (by linarith) (by linarith) (by linarith) hζs
  have hsum : ‖∑ w ∈ Z, ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s)‖ ≤
      ∑ w ∈ Z, zeroMult w * ‖selbergKernel x (w - s)‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun w _ => ?_))
    rw [norm_mul, Complex.norm_natCast]
    rfl
  have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun w : ℂ => w.re ≤ 1 / 2 + R / 2)
    (fun w => zeroMult w * ‖selbergKernel x (w - s)‖)
  have hnot : Z.filter (fun w : ℂ => ¬ w.re ≤ 1 / 2 + R / 2) =
      Z.filter (fun w : ℂ => 1 / 2 + R / 2 < w.re) :=
    Finset.filter_congr fun w _ => not_le
  rw [hnot] at hsplit
  have hleft := sum_left_selbergKernel_le hx hR hs1 hst hsub (x := x)
  have hright := sum_right_selbergKernel_le hx hR (by linarith) hst hsub hgood
  have hDs := hD s hs1 hs2 hst
  have htri : ‖logDeriv riemannZeta s‖ ≤
      ‖logDeriv riemannZeta s + selbergVonMangoldtPoly x s +
        ∑ w ∈ Z, ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s)‖ +
      ‖selbergVonMangoldtPoly x s‖ +
      ‖∑ w ∈ Z, ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s)‖ := by
    have e : logDeriv riemannZeta s = (logDeriv riemannZeta s + selbergVonMangoldtPoly x s +
        ∑ w ∈ Z, ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s)) -
        selbergVonMangoldtPoly x s -
        ∑ w ∈ Z, ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s) := by
      ring
    calc ‖logDeriv riemannZeta s‖ = ‖_ - _ - _‖ := congrArg norm e
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
  linarith

/-- **Log-derivative scale data at a good height.** -/
theorem zetaLogDerivScaleData_of_good {T t x R T₁ T₂ M_D : ℝ} (hT : 64 ≤ T)
    (ht : t ∈ Icc T (2 * T)) (hx : 1 < x) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (hRx : 1 ≤ 36 * R * Real.log x)
    (hT₁ : t / 2 - 1 < T₁) (hT₂ : T₂ < 3 * t / 2 + 1) (hT12 : T₁ ≤ T₂)
    (hEF : ∀ s₀ : ℂ, |s₀.im - t| ≤ t / 8 → 1 / 2 ≤ s₀.re → s₀.re ≤ 1 → riemannZeta s₀ ≠ 0 →
      ‖logDeriv riemannZeta s₀ + selbergVonMangoldtPoly x s₀ +
        ∑ w ∈ selbergHeightZeros t T₁ T₂,
          ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s₀)‖ ≤ 1)
    (hgood : ∀ w ∈ selbergMidZeros T, 1 / 2 + R / 2 < w.re →
      selbergRightWindow x R w < |w.im - t|)
    (hD : ∀ z : ℂ, 1 / 2 + 3 * R / 4 ≤ z.re → z.re ≤ 1 / 2 + 6 * R → |z.im - t| ≤ 6 * R →
      ‖selbergVonMangoldtPoly x z‖ ≤ M_D) :
    ZetaLogDerivScaleData t R (1 + M_D +
      2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 *
        selbergLorentzSum (selbergMidZeros T) (R / 4) t +
      selbergRightFar (selbergMidZeros T) x R t) := by
  have hzf := zeroFree_of_windows (by linarith) ht hx hR hR16 hRx hgood
  refine ⟨hzf, fun s hs1 hs2 hst => ?_⟩
  have hζs : riemannZeta s ≠ 0 := by
    intro h0
    have := hzf s h0 (by linarith)
    linarith
  exact norm_logDeriv_zeta_le_of_good hT ht hx hR hR16 hT₁ hT₂ hT12 hEF hgood hD hs1 hs2 hst hζs

end RHTower
