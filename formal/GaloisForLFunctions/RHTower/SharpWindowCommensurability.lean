import GaloisForLFunctions.RHTower.CCM.CCMRectangularTwoEdge

/-!
# Two-width sharp-window amplitude commensurability

The window amplitude `A_L(w) = (1 - e^{-Lw})/w` (with removable value `L` at `0`) vanishes off the
origin exactly on the imaginary period lattice `w ∈ (2πi/L)·(ℤ∖{0})`.  On the open right half-plane
`Re w > 0` it has no zero (`rectangularWindowAmplitude_ne_zero`), so a single positive width already
detects every off-critical pole.  On the imaginary axis (`Re w = 0`, the critical-line heights
`w = iγ`) it *can* vanish — but only on that one lattice.

Two widths `L₁, L₂` share an off-origin zero `w` only when their lattices meet there, which forces
`L₁·n = L₂·m` for nonzero integers `m, n`, i.e. `L₁/L₂ ∈ ℚ`.  Hence *irrationally related* widths never
kill a common `w`: every critical-line height is seen by at least one of the two windows.  This is the
amplitude core of two-width complete divisor recovery (`bounded-variation-prime-window-divisor-tomography`).
-/

open Complex

namespace RHTower

/-- A zero of the window amplitude off the origin lies on the imaginary period lattice: if
`A_L(w) = 0` with `w ≠ 0`, then `L·w = -m·(2πi)` for some nonzero integer `m` (equivalently
`e^{-Lw} = 1`). -/
theorem rectangularWindowAmplitude_eq_zero_forces {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : w ≠ 0)
    (h : rectangularWindowAmplitude L w = 0) :
    ∃ m : ℤ, m ≠ 0 ∧ (L : ℂ) * w = -(m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [rectangularWindowAmplitude_eq_div hw] at h
  have hnum : 1 - Complex.exp (-(L : ℂ) * w) = 0 := (div_eq_zero_iff.mp h).resolve_right hw
  have hexp : Complex.exp (-(L : ℂ) * w) = 1 := (sub_eq_zero.mp hnum).symm
  rw [Complex.exp_eq_one_iff] at hexp
  obtain ⟨m, hm⟩ := hexp
  refine ⟨m, ?_, by linear_combination -hm⟩
  rintro rfl
  simp only [Int.cast_zero, zero_mul] at hm
  have hLne : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  exact (mul_ne_zero (neg_ne_zero.mpr hLne) hw) hm

/-- **Two-width amplitude commensurability.**  If two positive-length sharp windows both annihilate the
same off-origin point `w` (both `A_{L₁}(w) = 0` and `A_{L₂}(w) = 0`), then their lengths are
commensurable: there are nonzero integers `m, n` with `L₁·n = L₂·m`.  Contrapositive: irrationally
related widths cannot both kill a common `w`. -/
theorem rectangularWindowAmplitude_joint_vanishing_commensurable
    {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) {w : ℂ} (hw : w ≠ 0)
    (h₁ : rectangularWindowAmplitude L₁ w = 0) (h₂ : rectangularWindowAmplitude L₂ w = 0) :
    ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ L₁ * (n : ℝ) = L₂ * (m : ℝ) := by
  obtain ⟨m, hm0, hm⟩ := rectangularWindowAmplitude_eq_zero_forces hL₁ hw h₁
  obtain ⟨n, hn0, hn⟩ := rectangularWindowAmplitude_eq_zero_forces hL₂ hw h₂
  refine ⟨m, n, hm0, hn0, ?_⟩
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hkey : ((L₂ : ℂ) * -(m : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I)
      = ((L₁ : ℂ) * -(n : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have e1 : (L₂ : ℂ) * ((L₁ : ℂ) * w) = (L₁ : ℂ) * ((L₂ : ℂ) * w) := by ring
    rw [hm, hn] at e1
    linear_combination e1
  have hcancel := mul_right_cancel₀ h2pi hkey
  have key : (L₂ : ℂ) * (m : ℂ) = (L₁ : ℂ) * (n : ℂ) := by linear_combination -hcancel
  have hreal : (L₂ : ℝ) * (m : ℝ) = (L₁ : ℝ) * (n : ℝ) := by exact_mod_cast key
  linarith

/-- **Two-width non-vanishing.**  For irrationally related widths `L₁, L₂`, no `w ≠ 0` is a common zero
of both amplitudes: at least one of `A_{L₁}(w), A_{L₂}(w)` is nonzero.  Joint vanishing would force
commensurability (`rectangularWindowAmplitude_joint_vanishing_commensurable`), contradicting the
irrationality of `L₁/L₂`. -/
theorem sharpAmplitude_not_both_zero {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hirr : Irrational (L₁ / L₂)) {w : ℂ} (hw : w ≠ 0) :
    rectangularWindowAmplitude L₁ w ≠ 0 ∨ rectangularWindowAmplitude L₂ w ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨m, n, hm0, hn0, hrel⟩ :=
    rectangularWindowAmplitude_joint_vanishing_commensurable hL₁ hL₂ hw h.1 h.2
  apply hirr
  have hnne : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn0
  refine ⟨(m : ℚ) / (n : ℚ), ?_⟩
  have hcast : (((m : ℚ) / (n : ℚ) : ℚ) : ℝ) = (m : ℝ) / (n : ℝ) := by push_cast; ring
  rw [hcast, div_eq_div_iff hnne hL₂.ne']
  linear_combination -hrel

/-- **Critical-line two-width detectability.**  For irrationally related widths `L₁, L₂` and any nonzero
height `γ`, at least one sharp-window amplitude is nonzero at the imaginary point `iγ`.  On the
imaginary axis the half-plane nonvanishing law fails, but incommensurability keeps the two period
lattices `(2π/Lⱼ)ℤ` disjoint off `0`, so no common imaginary zero survives — every critical-line height
is seen by at least one width. -/
theorem sharpAmplitude_imaginary_not_both_zero {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hirr : Irrational (L₁ / L₂)) {γ : ℝ} (hγ : γ ≠ 0) :
    rectangularWindowAmplitude L₁ ((γ : ℂ) * Complex.I) ≠ 0
      ∨ rectangularWindowAmplitude L₂ ((γ : ℂ) * Complex.I) ≠ 0 :=
  sharpAmplitude_not_both_zero hL₁ hL₂ hirr (by simp [Complex.ext_iff, hγ])

end RHTower
