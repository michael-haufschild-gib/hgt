import GaloisForLFunctions.HTGeometry.GammaStirlingDifference
import GaloisForLFunctions.HTGeometry.SectorPowerMassLower

/-!
# Symmetric vertical splits of the Gamma function

Write `φ(X, Y) = Re(w log w − w)` at `w = X + iY`, the Stirling main term of `log |Γ(w)|`.  On the
right half-plane

* `∂φ/∂X = log |w|`, which increases with `X`;
* `∂φ/∂Y = −arg w`, which decreases with `Y`, so `φ(X, ·)` is concave.

Hence two points at abscissa `X₁`, split symmetrically about an ordinate `Y`, satisfy the exact
inequality

```
φ(X₁, Y + d) + φ(X₁, Y − d) − 2 φ(X₀, Y) ≤ −2 (X₀ − X₁) log |X₁ + iY|      (0 < X₁ ≤ X₀),
```

with no error term and no restriction on `d`.  Combined with the complex Stirling difference along
the two segments this gives the decay law for `|Γ|` used on circles centred on the real axis:

```
log|Γ(X₁+i(Y+d))| + log|Γ(X₁+i(Y−d))| − 2 log|Γ(X₀+iY)| ≤ −2(X₀−X₁) log Y + 12(X₀−X₁+|d|)/Y
```

for `Y ≥ 4` and `|d| ≤ Y/2`.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- The real part of the Stirling main term on the horizontal line through `Y`. -/
def stirlingRe (X Y : ℝ) : ℝ := (stirlingMain ((X : ℂ) + (Y : ℂ) * I)).re

theorem add_mul_I_mem_slitPlane {X : ℝ} (Y : ℝ) (hX : 0 < X) :
    (X : ℂ) + (Y : ℂ) * I ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (by simp [hX]))

/-- Horizontally, `Re(w log w − w)` has derivative `log |w|`. -/
theorem hasDerivAt_stirlingRe_left {X Y : ℝ} (hX : 0 < X) :
    HasDerivAt (fun u => stirlingRe u Y) (Real.log ‖(X : ℂ) + (Y : ℂ) * I‖) X := by
  have h1 : HasDerivAt (fun u : ℂ => u + (Y : ℂ) * I) 1 (X : ℂ) :=
    (hasDerivAt_id _).add_const _
  have h2 := (hasDerivAt_stirlingMain (add_mul_I_mem_slitPlane Y hX)).comp (X : ℂ) h1
  have h3 := h2.real_of_complex
  simpa [stirlingRe, Function.comp_def, Complex.log_re] using h3

/-- Vertically, `Re(w log w − w)` has derivative `−arg w`. -/
theorem hasDerivAt_stirlingRe_right {X Y : ℝ} (hX : 0 < X) :
    HasDerivAt (fun v => stirlingRe X v) (-((X : ℂ) + (Y : ℂ) * I).arg) Y := by
  have h1 : HasDerivAt (fun v : ℂ => (X : ℂ) + v * I) I (Y : ℂ) := by
    simpa using ((hasDerivAt_id (Y : ℂ)).mul_const I).const_add (X : ℂ)
  have h2 := (hasDerivAt_stirlingMain (add_mul_I_mem_slitPlane Y hX)).comp (Y : ℂ) h1
  have h3 := h2.real_of_complex
  have hre : (Complex.log ((X : ℂ) + (Y : ℂ) * I) * I).re = -((X : ℂ) + (Y : ℂ) * I).arg := by
    simp [Complex.mul_re, Complex.log_im]
  rw [hre] at h3
  simpa [stirlingRe, Function.comp_def] using h3

/-- In the right half-plane the principal argument increases with the ordinate. -/
theorem arg_add_mul_I_le {X Y Y' : ℝ} (hX : 0 < X) (h : Y ≤ Y') :
    ((X : ℂ) + (Y : ℂ) * I).arg ≤ ((X : ℂ) + (Y' : ℂ) * I).arg := by
  rw [GaloisForLFunctions.HTGeometry.complexArg_eq_arctan_of_re_pos (by simp [hX]),
    GaloisForLFunctions.HTGeometry.complexArg_eq_arctan_of_re_pos (by simp [hX])]
  apply Real.arctan_strictMono.monotone
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add]
  exact div_le_div_of_nonneg_right h hX.le

/-- **Vertical concavity of the Stirling main term.**  On every vertical line in the right
half-plane, `Y ↦ Re(w log w − w)` is concave: its derivative `−arg w` decreases.  In particular a
symmetric vertical split never increases the sum. -/
theorem stirlingRe_add_add_sub_le {X Y d : ℝ} (hX : 0 < X) :
    stirlingRe X (Y + d) + stirlingRe X (Y - d) ≤ 2 * stirlingRe X Y := by
  -- reduce to `d ≥ 0`
  wlog hd : 0 ≤ d generalizing d
  · have := this (d := -d) (by linarith)
    rw [sub_neg_eq_add, ← sub_eq_add_neg] at this
    linarith
  set h : ℝ → ℝ := fun s => stirlingRe X (Y + s) + stirlingRe X (Y - s) with hh
  have hderiv : ∀ s, HasDerivAt h
      (-((X : ℂ) + ((Y + s : ℝ) : ℂ) * I).arg + ((X : ℂ) + ((Y - s : ℝ) : ℂ) * I).arg) s := by
    intro s
    have hp := (hasDerivAt_stirlingRe_right (Y := Y + s) hX).comp s
      ((hasDerivAt_id s).const_add Y)
    have hm := (hasDerivAt_stirlingRe_right (Y := Y - s) hX).comp s
      ((hasDerivAt_id s).const_sub Y)
    exact (hp.add hm).congr_deriv (by ring)
  have hanti : AntitoneOn h (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun s _ => (hderiv s).continuousAt.continuousWithinAt
    · exact fun s _ => (hderiv s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hderiv s).deriv]
      have := arg_add_mul_I_le (Y := Y - s) (Y' := Y + s) hX (by linarith [(show (0:ℝ) < s from hs).le])
      push_cast at this ⊢
      linarith
  have := hanti (Set.self_mem_Ici) (Set.mem_Ici.mpr hd) hd
  simp only [hh, add_zero, sub_zero] at this
  linarith

/-- **Horizontal growth of the Stirling main term.**  Moving from `X₁` right to `X₀` raises
`Re(w log w − w)` by at least `(X₀ − X₁) log|X₁ + iY|`, since the horizontal derivative is
`log |w|`, increasing in `X`. -/
theorem stirlingRe_sub_ge {X₀ X₁ Y : ℝ} (hX₁ : 0 < X₁) (hX : X₁ ≤ X₀) :
    (X₀ - X₁) * Real.log ‖(X₁ : ℂ) + (Y : ℂ) * I‖ ≤ stirlingRe X₀ Y - stirlingRe X₁ Y := by
  set L := Real.log ‖(X₁ : ℂ) + (Y : ℂ) * I‖
  set k : ℝ → ℝ := fun u => stirlingRe u Y - u * L with hk
  have hderiv : ∀ u : ℝ, 0 < u → HasDerivAt k (Real.log ‖(u : ℂ) + (Y : ℂ) * I‖ - L) u := by
    intro u hu
    have := (hasDerivAt_stirlingRe_left (Y := Y) hu).sub ((hasDerivAt_id' u).mul_const L)
    exact this.congr_deriv (by ring)
  have hmono : MonotoneOn k (Set.Ici X₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici X₁)
    · exact fun u hu => (hderiv u (lt_of_lt_of_le hX₁ hu)).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      exact (hderiv u (lt_trans hX₁ hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      have hu0 : 0 < u := lt_trans hX₁ hu
      rw [(hderiv u hu0).deriv, sub_nonneg]
      apply Real.log_le_log
      · rw [Complex.norm_add_mul_I]
        exact Real.sqrt_pos.mpr (by positivity)
      · rw [Complex.norm_add_mul_I, Complex.norm_add_mul_I]
        apply Real.sqrt_le_sqrt
        have : X₁ ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hX₁.le (le_of_lt hu) 2
        linarith
  have := hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr hX) hX
  simp only [hk] at this
  linarith

/-- **Symmetric-split law for the Stirling main term.**  Two points at abscissa `X₁`, split
symmetrically about the ordinate `Y`, carry at most the Stirling mass of two points at `X₀ ≥ X₁`
on the ordinate `Y`, less `2(X₀ − X₁) log|X₁ + iY|`.  There is no error term and no restriction on
the size of the split. -/
theorem stirlingRe_split_le {X₀ X₁ Y d : ℝ} (hX₁ : 0 < X₁) (hX : X₁ ≤ X₀) :
    stirlingRe X₁ (Y + d) + stirlingRe X₁ (Y - d) - 2 * stirlingRe X₀ Y
      ≤ -2 * (X₀ - X₁) * Real.log ‖(X₁ : ℂ) + (Y : ℂ) * I‖ := by
  have h1 := stirlingRe_add_add_sub_le (Y := Y) (d := d) hX₁
  have h2 := stirlingRe_sub_ge (Y := Y) hX₁ hX
  linarith

/-- **Symmetric-split decay of `|Γ|`.**  For ordinate `Y ≥ 4`, abscissae `0 < X₁ ≤ X₀` and a split
`|d| ≤ Y/2`,
`log|Γ(X₁+i(Y+d))| + log|Γ(X₁+i(Y−d))| − 2 log|Γ(X₀+iY)| ≤ −2(X₀−X₁) log Y + 12(X₀−X₁+|d|)/Y`.
The main term is the symmetric-split law for `Re(w log w − w)`; the error is the complex Stirling
difference along the two segments, which stay at distance `≥ Y/2` from `0`. -/
theorem log_norm_Gamma_split_le {X₀ X₁ Y d : ℝ} (hX₁ : 0 < X₁) (hX : X₁ ≤ X₀) (hY : 4 ≤ Y)
    (hd : |d| ≤ Y / 2) :
    Real.log ‖Complex.Gamma ((X₁ : ℂ) + ((Y + d : ℝ) : ℂ) * I)‖
      + Real.log ‖Complex.Gamma ((X₁ : ℂ) + ((Y - d : ℝ) : ℂ) * I)‖
      - 2 * Real.log ‖Complex.Gamma ((X₀ : ℂ) + (Y : ℂ) * I)‖
      ≤ -2 * (X₀ - X₁) * Real.log Y + 12 * (X₀ - X₁ + |d|) / Y := by
  have hm : (2 : ℝ) ≤ Y / 2 := by linarith
  -- one segment, with ordinate shift `e`, `|e| ≤ Y/2`
  have seg : ∀ e : ℝ, |e| ≤ Y / 2 →
      |(Real.log ‖Complex.Gamma ((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I)‖
          - Real.log ‖Complex.Gamma ((X₀ : ℂ) + (Y : ℂ) * I)‖)
        - (stirlingRe X₁ (Y + e) - stirlingRe X₀ Y)| ≤ 6 * (X₀ - X₁ + |e|) / Y := by
    intro e he
    have hseg : ∀ l ∈ Set.Icc (0 : ℝ) 1,
        0 < ((X₀ : ℂ) + (Y : ℂ) * I + (l : ℂ) *
          (((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I) - ((X₀ : ℂ) + (Y : ℂ) * I))).re ∧
        Y / 2 ≤ ‖(X₀ : ℂ) + (Y : ℂ) * I + (l : ℂ) *
          (((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I) - ((X₀ : ℂ) + (Y : ℂ) * I))‖ := by
      intro l hl
      obtain ⟨hl0, hl1⟩ := hl
      constructor
      · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one,
          sub_self, add_zero, sub_re, zero_mul, add_im, mul_im, zero_add, sub_im]
        nlinarith
      · refine le_trans ?_ (Complex.abs_im_le_norm _)
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one,
          sub_self, add_zero, sub_re, zero_mul, add_im, mul_im, zero_add, sub_im]
        have hle : |l * e| ≤ Y / 2 := by
          rw [abs_mul, abs_of_nonneg hl0]
          nlinarith [abs_nonneg e]
        have : Y + l * (Y + e - Y) = Y + l * e := by ring
        rw [this]
        rw [abs_of_nonneg (by linarith [neg_abs_le (l * e)])]
        linarith [neg_abs_le (l * e)]
    have hS := abs_log_norm_Gamma_sub_stirlingMain_le hm hseg
    have hnorm : ‖((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I) - ((X₀ : ℂ) + (Y : ℂ) * I)‖
        ≤ X₀ - X₁ + |e| := by
      have : ((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I) - ((X₀ : ℂ) + (Y : ℂ) * I)
          = ((X₁ - X₀ : ℝ) : ℂ) + ((e : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.norm_add_mul_I]
      have := Real.sqrt_le_sqrt (show (X₁ - X₀) ^ 2 + e ^ 2 ≤ (X₀ - X₁ + |e|) ^ 2 by
        nlinarith [abs_nonneg e, sq_abs e, abs_nonneg (X₁ - X₀)])
      rwa [Real.sqrt_sq (by linarith [abs_nonneg e])] at this
    have hY0 : 0 < Y := by linarith
    calc _ ≤ 3 * ‖((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I) - ((X₀ : ℂ) + (Y : ℂ) * I)‖ / (Y / 2) := by
            simpa [stirlingRe] using hS
      _ ≤ 3 * (X₀ - X₁ + |e|) / (Y / 2) := by gcongr
      _ = 6 * (X₀ - X₁ + |e|) / Y := by field_simp; ring
  have hp := seg d hd
  have hm' := seg (-d) (by rwa [abs_neg])
  rw [abs_neg] at hm'
  have hsub : Y + -d = Y - d := by ring
  rw [hsub] at hm'
  have hmain := stirlingRe_split_le (Y := Y) (d := d) hX₁ hX
  have hlogY : Real.log Y ≤ Real.log ‖(X₁ : ℂ) + (Y : ℂ) * I‖ := by
    apply Real.log_le_log (by linarith)
    rw [Complex.norm_add_mul_I]
    rw [show Y = Real.sqrt (Y ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg X₁, Real.sqrt_sq (show (0:ℝ) ≤ Y by linarith)]
  have hXX : 0 ≤ X₀ - X₁ := by linarith
  have hlog2 : -2 * (X₀ - X₁) * Real.log ‖(X₁ : ℂ) + (Y : ℂ) * I‖ ≤ -2 * (X₀ - X₁) * Real.log Y := by
    nlinarith
  have e12 : 6 * (X₀ - X₁ + |d|) / Y + 6 * (X₀ - X₁ + |d|) / Y = 12 * (X₀ - X₁ + |d|) / Y := by ring
  have ha := (abs_le.mp hp).2
  have hb := (abs_le.mp hm').2
  linarith

end

end HTGeometry
