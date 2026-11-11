import GaloisForLFunctions.FloorFreeArithmetic.MomentsOnWindowsAmplifyTheDepth
import GaloisForLFunctions.FloorFreeArithmetic.NonAttainmentIsALawOfConfigurations
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheReflectionSectorsOfTheHodgeDefect

/-!
# The order of a moment is the depth it reaches

A bound `∫_T^{T+L} (2 Re S)^{2k} ≤ C e^{AT}` for one order `k ≥ 1`, on arbitrarily late windows of
one length, excludes the finite top layers of depth beyond `A/2k` and no others: a finite top
layer at the depth `b` has `2k`-th window moments of the exact rate `e^{2kbT}`.

* `false_of_frequently_exp_le`: a positive multiple of `e^{gT}`, `g > 0`, is not bounded on
  arbitrarily large `T`.
* `abscissaLawAt_of_window_moment`: the abscissa law at every depth `h ≥ A/2k`.

The exponent that a moment of one order buys is divided by the order. Only a family of bounds
of all orders with one exponent reaches every depth.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality
open ZeroConfigurationGeometry ZeroConfigurationGeometry.ConfigAbscissa

/-- A positive multiple of `e^{gT}` with `g > 0` is not bounded on arbitrarily large `T`. -/
theorem false_of_frequently_exp_le {κ g C : ℝ} (hκ : 0 < κ) (hg : 0 < g)
    (h : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ κ * Real.exp (g * T) ≤ C) : False := by
  obtain ⟨T, hT, hle⟩ := h (|C| / (κ * g) + 1)
  have hκg : 0 < κ * g := mul_pos hκ hg
  have h1 : g * T + 1 ≤ Real.exp (g * T) := Real.add_one_le_exp _
  have h2 := mul_le_mul_of_nonneg_left h1 hκ.le
  have h3 : |C| + κ * g ≤ κ * g * T := by
    have h4 := mul_le_mul_of_nonneg_left hT hκg.le
    rw [mul_add, mul_one, mul_div_cancel₀ _ hκg.ne'] at h4
    exact h4
  have e : κ * (g * T + 1) = κ * g * T + κ := by ring
  rw [e] at h2
  linarith only [h2, hle, h3, le_abs_self C, hκ, hκg]

/-- **A moment of order `2k` with the exponent `A` gives the abscissa law beyond the depth
`A/2k`.** If on arbitrarily late windows of length `L` the `2k`-th moment of the spline trace of
`ζ` is at most `C e^{AT}`, with `k ≥ 1`, then for every depth `h ≥ 0` with `A ≤ 2kh`: finitely
many zeros beyond the depth `h` means none. -/
theorem abscissaLawAt_of_window_moment {L A C : ℝ} {k : ℕ} (hL : 0 < L) (hk : 1 ≤ k)
    (hmom : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
      (∫ u in T..(T + L), (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re) ^ (2 * k)) ≤
        C * Real.exp (A * T))
    {h : ℝ} (hh : 0 ≤ h) (hA : A ≤ 2 * k * h) : AbscissaLawAt zetaZeroConfig h := by
  by_contra hnot
  obtain ⟨b, hb, htop, S, hS, hne⟩ := exists_finite_top_of_not_abscissaLawAt_config
    (fun ρ hρ => _root_.RHTower.conj_mem_zetaZeroConfig hρ)
    (fun ρ hρ _ => ArithmeticCastelnuovoSeveri.zetaZeroConfig_im_ne_zero' ρ hρ) hh hnot
  obtain ⟨c, η, U₀, hc, hη, hlow⟩ := finite_top_moment_lower_bound
    temperedConfig_zetaZeroConfig (hh.trans hb.le) htop hL S hS hne
    (fun z hz _ => evenCoeff_spline_real hz)
  -- the amplified depth exceeds the exponent
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hg : 0 < 2 * (k : ℝ) * b - A := by
    have h1 := mul_pos (mul_pos two_pos hk') (sub_pos.mpr hb)
    have e : 2 * (k : ℝ) * (b - h) = 2 * k * b - 2 * k * h := by ring
    rw [e] at h1
    linarith only [h1, hA]
  refine false_of_frequently_exp_le (C := C) (mul_pos hη (pow_pos hc (2 * k))) hg fun U => ?_
  obtain ⟨T, hT, hup⟩ := hmom (max U U₀)
  refine ⟨T, (le_max_left _ _).trans hT, ?_⟩
  have hlo := hlow T ((le_max_right _ _).trans hT) k
  have hE : 0 < Real.exp (A * T) := Real.exp_pos _
  have hpow : (c * Real.exp (b * T)) ^ (2 * k) =
      c ^ (2 * k) * (Real.exp ((2 * (k : ℝ) * b - A) * T) * Real.exp (A * T)) := by
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    push_cast
    ring
  rw [hpow] at hlo
  have h2 : η * c ^ (2 * k) * Real.exp ((2 * (k : ℝ) * b - A) * T) * Real.exp (A * T) ≤
      C * Real.exp (A * T) := by
    have h3 := hlo.trans hup
    linarith only [h3, mul_assoc (η * c ^ (2 * k)) (Real.exp ((2 * (k : ℝ) * b - A) * T))
      (Real.exp (A * T)), mul_assoc η (c ^ (2 * k))
      (Real.exp ((2 * (k : ℝ) * b - A) * T) * Real.exp (A * T))]
  exact le_of_mul_le_mul_right h2 hE

end GaloisForLFunctions.FloorFreeArithmetic
