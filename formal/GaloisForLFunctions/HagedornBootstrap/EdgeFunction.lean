import GaloisForLFunctions.HagedornBootstrap.BootstrapSlope
import GaloisForLFunctions.HagedornBootstrap.TanhGaussianFloor
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Deriv

/-!
# The edge function and the zero law of the bootstrap

Two explicit functions govern the optimal spinless bootstrap functionals at large central charge.

* **The edge function** `F(w) = arsinh(cosh πw)/π` (the saddle-point phase along the edge
  `Im b = 1/2` through the vacuum). It is even, `F(0) = x*`, its slope
  `F'(w) = sinh(πw)/√(2 + sinh²(πw))` is strictly increasing with `|F'| < 1`, so `F` is strictly
  convex, and `|w| < F(w) ≤ |w| + x*`.
* **The zero law** `ρ_U(x) = (4/3π) arcosh(sinh π|x|)` on the slits `|x| ≥ x*`: the density of
  the double zeros of near-optimal functionals. It vanishes exactly at the tip, is strictly
  increasing beyond it, satisfies `cosh(3πρ_U/4) = sinh(π|x|)`, and
  `(3πρ_U/4)² ≤ 2(sinh(π|x|) − 1)` (square-root growth at the tip).
* **The Cardy deficit integrand** `π/2 − arcsin(sinh πs)` is positive on `[0, x*)` and vanishes
  at the tip.
* On the edge through the vacuum, `|cosh(π(v + i/2)/2)|² = cosh(πv)/2`, so the comb factor
  `sech²(πb/2)` has modulus `2/cosh πv` there.
-/

noncomputable section

open Real Set

namespace GaloisForLFunctions.HagedornBootstrap

/-! ### The edge function -/

/-- The edge function `F(w) = arsinh(cosh πw)/π`. -/
def edgeF (w : ℝ) : ℝ := Real.arsinh (Real.cosh (π * w)) / π

/-- Its slope `F'(w) = sinh(πw)/√(2 + sinh²(πw))`. -/
def edgeSlope (w : ℝ) : ℝ := Real.sinh (π * w) / √(2 + Real.sinh (π * w) ^ 2)

theorem edgeF_neg (w : ℝ) : edgeF (-w) = edgeF w := by
  unfold edgeF; rw [mul_neg, Real.cosh_neg]

theorem edgeF_zero : edgeF 0 = bootstrapTip := by simp [edgeF, bootstrapTip]

theorem hasDerivAt_edgeF (w : ℝ) : HasDerivAt edgeF (edgeSlope w) w := by
  have h1 : HasDerivAt (fun w => Real.cosh (π * w)) (Real.sinh (π * w) * π) w := by
    have h := (Real.hasDerivAt_cosh (π * w)).comp w ((hasDerivAt_id w).const_mul π)
    exact h.congr_deriv (by simp)
  have h2 := ((Real.hasDerivAt_arsinh _).comp w h1).div_const π
  refine h2.congr_deriv ?_
  have hs : √(1 + Real.cosh (π * w) ^ 2) = √(2 + Real.sinh (π * w) ^ 2) := by
    congr 1; rw [Real.cosh_sq]; ring
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hpos : 0 < √(2 + Real.sinh (π * w) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  unfold edgeSlope
  rw [hs]
  field_simp

theorem deriv_edgeF : deriv edgeF = edgeSlope := funext fun w => (hasDerivAt_edgeF w).deriv

/-- `|F'| < 1`: the edge function is a strict contraction of slopes. -/
theorem abs_edgeSlope_lt_one (w : ℝ) : |edgeSlope w| < 1 := by
  have hpos : 0 < √(2 + Real.sinh (π * w) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  unfold edgeSlope
  rw [abs_div, abs_of_pos hpos, div_lt_one hpos]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)

theorem edgeSlope_pos {w : ℝ} (hw : 0 < w) : 0 < edgeSlope w := by
  unfold edgeSlope
  have : 0 < Real.sinh (π * w) := Real.sinh_pos_iff.mpr (by positivity)
  have : 0 < √(2 + Real.sinh (π * w) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- `t ↦ t/√(2 + t²)` is strictly increasing. -/
theorem strictMono_div_sqrt_two_add_sq : StrictMono fun t : ℝ => t / √(2 + t ^ 2) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t / √(2 + t ^ 2))
      (2 / ((2 + t ^ 2) * √(2 + t ^ 2))) t := by
    intro t
    have hq : 0 < 2 + t ^ 2 := by positivity
    have hs : HasDerivAt (fun t : ℝ => √(2 + t ^ 2)) (2 * t / (2 * √(2 + t ^ 2))) t := by
      have := ((hasDerivAt_pow 2 t).const_add 2).sqrt hq.ne'
      refine this.congr_deriv ?_
      push_cast; ring
    have hsp : 0 < √(2 + t ^ 2) := Real.sqrt_pos.mpr hq
    refine ((hasDerivAt_id t).div hs hsp.ne').congr_deriv ?_
    simp only [id]
    have hsq : √(2 + t ^ 2) ^ 2 = 2 + t ^ 2 := Real.sq_sqrt hq.le
    field_simp
    nlinarith [hsq]
  apply strictMono_of_deriv_pos
  intro t
  rw [(hd t).deriv]
  have hq : 0 < 2 + t ^ 2 := by positivity
  have : 0 < √(2 + t ^ 2) := Real.sqrt_pos.mpr hq
  positivity

theorem edgeSlope_strictMono : StrictMono edgeSlope := by
  intro a b hab
  exact strictMono_div_sqrt_two_add_sq
    (Real.sinh_strictMono (mul_lt_mul_of_pos_left hab Real.pi_pos))

/-- **The edge function is strictly convex.** -/
theorem edgeF_strictConvexOn : StrictConvexOn ℝ univ edgeF := by
  apply StrictMono.strictConvexOn_univ_of_deriv
  · exact continuous_iff_continuousAt.2 fun w => (hasDerivAt_edgeF w).continuousAt
  · rw [deriv_edgeF]; exact edgeSlope_strictMono

/-- `|w| < F(w)`: the edge function lies strictly above the light cone. -/
theorem abs_lt_edgeF (w : ℝ) : |w| < edgeF w := by
  unfold edgeF
  rw [lt_div_iff₀ Real.pi_pos]
  have hc : Real.cosh (π * w) = Real.cosh (π * |w|) := by
    rcases le_or_gt 0 w with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, mul_neg, Real.cosh_neg]
  rw [hc, show |w| * π = Real.arsinh (Real.sinh (π * |w|)) by rw [Real.arsinh_sinh]; ring]
  exact Real.arsinh_lt_arsinh.mpr (Real.sinh_lt_cosh _)

/-- `F(w) ≤ |w| + x*`. -/
theorem edgeF_le (w : ℝ) : edgeF w ≤ |w| + bootstrapTip := by
  set u := π * |w| with hu
  have hu0 : 0 ≤ u := by positivity
  have hc : Real.cosh (π * w) = Real.cosh u := by
    rcases le_or_gt 0 w with h | h
    · rw [hu, abs_of_nonneg h]
    · rw [hu, abs_of_neg h, mul_neg, Real.cosh_neg]
  have key : Real.arsinh (Real.cosh (π * w)) ≤ u + Real.arsinh 1 := by
    rw [hc, ← Real.arsinh_sinh (u + Real.arsinh 1)]
    apply Real.arsinh_le_arsinh.mpr
    rw [Real.sinh_add, Real.sinh_arsinh, Real.cosh_arsinh]
    have : 0 ≤ Real.sinh u * √(1 + 1 ^ 2) := by
      have := Real.sinh_nonneg_iff.mpr hu0; positivity
    linarith
  unfold edgeF bootstrapTip
  calc Real.arsinh (Real.cosh (π * w)) / π ≤ (u + Real.arsinh 1) / π :=
        div_le_div_of_nonneg_right key Real.pi_pos.le
    _ = |w| + Real.arsinh 1 / π := by rw [hu]; field_simp

/-! ### The zero law -/

/-- The zero law `ρ_U(x) = (4/3π) arcosh(sinh π|x|)`. -/
def zeroLaw (x : ℝ) : ℝ := 4 / (3 * π) * Real.arcosh (Real.sinh (π * |x|))

theorem zeroLaw_neg (x : ℝ) : zeroLaw (-x) = zeroLaw x := by simp [zeroLaw]

theorem zeroLaw_tip : zeroLaw bootstrapTip = 0 := by
  unfold zeroLaw
  rw [abs_of_pos bootstrapTip_pos, sinh_pi_mul_bootstrapTip]
  simp

theorem one_lt_sinh_of_tip_lt {x : ℝ} (h : bootstrapTip < |x|) : 1 < Real.sinh (π * |x|) := by
  rw [← sinh_pi_mul_bootstrapTip]
  exact Real.sinh_strictMono (mul_lt_mul_of_pos_left h Real.pi_pos)

/-- The zero law is positive beyond the tip. -/
theorem zeroLaw_pos {x : ℝ} (h : bootstrapTip < |x|) : 0 < zeroLaw x := by
  unfold zeroLaw
  have h1 := one_lt_sinh_of_tip_lt h
  have : Real.arcosh 1 < Real.arcosh (Real.sinh (π * |x|)) :=
    (Real.arcosh_lt_arcosh one_pos (by linarith)).mpr h1
  rw [Real.arcosh_zero] at this
  have : 0 < 4 / (3 * π) := by positivity
  positivity

/-- The zero law increases strictly along the slit. -/
theorem zeroLaw_strictMonoOn : StrictMonoOn zeroLaw (Ici bootstrapTip) := by
  intro a ha b hb hab
  simp only [mem_Ici] at ha hb
  have ha0 : 0 < a := lt_of_lt_of_le bootstrapTip_pos ha
  have hb0 : 0 < b := lt_trans ha0 hab
  unfold zeroLaw
  rw [abs_of_pos ha0, abs_of_pos hb0]
  have hsa : 1 ≤ Real.sinh (π * a) := by
    rw [← sinh_pi_mul_bootstrapTip]
    exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left ha Real.pi_pos.le)
  have hlt : Real.sinh (π * a) < Real.sinh (π * b) :=
    Real.sinh_strictMono (mul_lt_mul_of_pos_left hab Real.pi_pos)
  have := (Real.arcosh_lt_arcosh (by linarith) (by linarith)).mpr hlt
  have : 0 < 4 / (3 * π) := by positivity
  exact mul_lt_mul_of_pos_left (by assumption) this

/-- The zero law inverts the edge: `cosh(3πρ_U(x)/4) = sinh(π|x|)` on the slits. -/
theorem cosh_zeroLaw {x : ℝ} (h : bootstrapTip ≤ |x|) :
    Real.cosh (3 * π / 4 * zeroLaw x) = Real.sinh (π * |x|) := by
  have h1 : 1 ≤ Real.sinh (π * |x|) := by
    rw [← sinh_pi_mul_bootstrapTip]
    exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left h Real.pi_pos.le)
  unfold zeroLaw
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [show 3 * π / 4 * (4 / (3 * π) * Real.arcosh (Real.sinh (π * |x|))) =
    Real.arcosh (Real.sinh (π * |x|)) by field_simp, Real.cosh_arcosh h1]

/-- `1 + t²/2 ≤ cosh t` for `t ≥ 0`. -/
theorem one_add_sq_div_two_le_cosh {t : ℝ} (ht : 0 ≤ t) : 1 + t ^ 2 / 2 ≤ Real.cosh t := by
  have d : ∀ x, HasDerivAt (fun x => Real.cosh x - 1 - x ^ 2 / 2) (Real.sinh x - x) x := by
    intro x
    refine (((Real.hasDerivAt_cosh x).sub_const 1).sub ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv ?_
    push_cast; ring
  have := nonneg_of_hasDerivAt_of_zero d (by simp) (fun x hx => by
    have := Real.self_le_sinh_iff.mpr hx.le; linarith) ht
  linarith

/-- Square-root growth at the tip: `(3πρ_U/4)² ≤ 2(sinh(π|x|) − 1)`. -/
theorem zeroLaw_sq_le {x : ℝ} (h : bootstrapTip ≤ |x|) :
    (3 * π / 4 * zeroLaw x) ^ 2 ≤ 2 * (Real.sinh (π * |x|) - 1) := by
  have hc := cosh_zeroLaw h
  have hnn : 0 ≤ 3 * π / 4 * zeroLaw x := by
    unfold zeroLaw
    have h1 : 1 ≤ Real.sinh (π * |x|) := by
      rw [← sinh_pi_mul_bootstrapTip]
      exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left h Real.pi_pos.le)
    have := Real.arcosh_nonneg h1
    positivity
  have := one_add_sq_div_two_le_cosh hnn
  linarith

/-! ### The Cardy deficit integrand -/

theorem deficit_integrand_pos {s : ℝ} (h : s < bootstrapTip) :
    0 < π / 2 - Real.arcsin (Real.sinh (π * s)) := by
  have : Real.sinh (π * s) < 1 := by
    rw [← sinh_pi_mul_bootstrapTip]
    exact Real.sinh_strictMono (mul_lt_mul_of_pos_left h Real.pi_pos)
  have := Real.arcsin_lt_pi_div_two.mpr this
  linarith

theorem deficit_integrand_tip : π / 2 - Real.arcsin (Real.sinh (π * bootstrapTip)) = 0 := by
  rw [sinh_pi_mul_bootstrapTip, Real.arcsin_one]; ring

/-! ### The comb on the edge through the vacuum -/

/-- `|cosh(x + iy)|² = sinh² x + cos² y`. -/
theorem normSq_cosh_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.cosh (x + y * Complex.I)) = Real.sinh x ^ 2 + Real.cos y ^ 2 := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
  have h1 := Real.cosh_sq x
  have h2 := Real.sin_sq_add_cos_sq y
  nlinarith [h1, h2]

/-- On the edge `b = v + i/2`: `|cosh(πb/2)|² = cosh(πv)/2`, so `|sech²(πb/2)| = 2/cosh πv`. -/
theorem normSq_cosh_edge (v : ℝ) :
    Complex.normSq (Complex.cosh (((π * v / 2 : ℝ) : ℂ) + ((π / 4 : ℝ) : ℂ) * Complex.I)) =
      Real.cosh (π * v) / 2 := by
  rw [normSq_cosh_add_mul_I, Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : Real.cosh (π * v) = Real.cosh (2 * (π * v / 2)) := by ring_nf
  rw [h2, Real.cosh_two_mul, Real.cosh_sq]
  ring

end GaloisForLFunctions.HagedornBootstrap
