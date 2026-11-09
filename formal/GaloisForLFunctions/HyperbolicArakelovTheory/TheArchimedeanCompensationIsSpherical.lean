import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanFrobeniusIsAHyperbolicGreenFunction
import GaloisForLFunctions.SurfaceOfSpecZ.TheTorsionEnergyAgainstTheJets

/-!
# The archimedean compensation is spherical: the pole lives at `ν = 3/2`

On the archimedean fibre `ℍ³` the radial functions with Laplace eigenvalue `1 − ν²` are spanned by
`e^{±νd}/sinh d`; the **spherical function** `φ_ν(d) = sinh(νd)/(ν sinh d)` (`sphericalFn`) is the
one regular at `d = 0` (`sphericalFn_radial`: `φ″ + 2coth(d) φ′ = (ν² − 1)φ`). The archimedean
Frobenius is the Green function `2πG_{1/2}` of `Δ − ¾`; the pole of Weil's form is the bidegree
pairing `m + n = 2√(mn) cosh(d/2)`. Both decompose into spherical pieces:

* **the pole is two spherical functions** (`two_cosh_half_eq_spherical`):
  `2cosh(d/2) = (3/2)φ_{3/2}(d) + ½φ_{1/2}(d)`, eigenvalues `−5/4` and `¾`;
* **the Frobenius is the standard Green function plus the same complementary piece**
  (`archProfile_eq_spherical`): `2πG_{1/2} = 2πG_{3/2} + ½φ_{1/2}`, with `φ_{1/2} = sech(d/2)`
  (`sphericalFn_half`).

So in Weil's archimedean compensation, pole minus Frobenius, the complementary-series piece at
`ν = ½` cancels exactly (`compensation_eq_spherical`, `archCompensation_eq_spherical`):

  `C_∞(d) = 2cosh(d/2) − 2πG_{1/2}(d) = (3/2)φ_{3/2}(d) − 2πG_{3/2}(d)`,

the spherical function at `ν = 3/2` (outside the unitary dual) against the `L²` resolvent of `Δ − ¾`
(the quantization `Δ = 3/2`). Weil's archimedean-plus-pole weight is `4πG_{3/2} − 3φ_{3/2}`
(`weilKernel_eq_spherical`).

**The plastic ratio is the balance of the two pieces** (`compensation_neg_iff`,
`compensation_pos_iff`). `C_∞(d) < 0` iff `2 sinh(3d/2) < e^{−d/2}` iff `e^{3d} < e^d + 1`, i.e. iff
`e^d` lies below the plastic number `ρ³ = ρ + 1`. The plastic sign law of the atomic kernel is the
point where the pole's `ν = 3/2` component overtakes the standard Green function of the fibre.
-/

open Real

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ

/-- The spherical function `φ_ν(d) = sinh(νd)/(ν sinh d)` of `ℍ³` (Laplace eigenvalue `1 − ν²`). -/
def sphericalFn (ν d : ℝ) : ℝ := Real.sinh (ν * d) / (ν * Real.sinh d)

/-- `φ_ν = (e^{νd} − e^{−νd})/(2ν sinh d)`, a combination of the radial modes. -/
theorem sphericalFn_eq (ν : ℝ) :
    sphericalFn ν = fun d => (radialMode (-ν) d - radialMode ν d) / (2 * ν) := by
  funext d
  simp only [sphericalFn, radialMode, neg_mul, neg_neg, Real.sinh_eq (ν * d)]
  ring

/-- **`φ_ν` is a radial eigenfunction**: `φ″ + 2coth(d) φ′ = (ν² − 1)φ` for `d ≠ 0`. -/
theorem sphericalFn_radial (ν : ℝ) {d : ℝ} (hd : d ≠ 0) :
    deriv (deriv (sphericalFn ν)) d + 2 * (Real.cosh d / Real.sinh d) * deriv (sphericalFn ν) d =
      (ν ^ 2 - 1) * sphericalFn ν d := by
  have hs : Real.sinh d ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
  have key : ∀ α : ℝ, radialMode'' α d + 2 * (Real.cosh d / Real.sinh d) * radialMode' α d =
      (α ^ 2 - 1) * radialMode α d := by
    intro α
    have h := radialMode_radial α hd
    rwa [(deriv_radialMode_eventually α hd).deriv_eq, (hasDerivAt_radialMode' α hs).deriv,
      (hasDerivAt_radialMode α hs).deriv] at h
  have hD1 : deriv (sphericalFn ν) =ᶠ[nhds d]
      fun x => (radialMode' (-ν) x - radialMode' ν x) / (2 * ν) := by
    have hne : ∀ᶠ x in nhds d, x ≠ 0 := isOpen_ne.mem_nhds hd
    filter_upwards [hne] with x hx
    have hsx : Real.sinh x ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
    rw [sphericalFn_eq]
    exact (((hasDerivAt_radialMode (-ν) hsx).sub (hasDerivAt_radialMode ν hsx)).div_const
      (2 * ν)).deriv
  have hD2 : deriv (fun x => (radialMode' (-ν) x - radialMode' ν x) / (2 * ν)) d =
      (radialMode'' (-ν) d - radialMode'' ν d) / (2 * ν) :=
    (((hasDerivAt_radialMode' (-ν) hs).sub (hasDerivAt_radialMode' ν hs)).div_const
      (2 * ν)).deriv
  rw [hD1.deriv_eq, hD2, hD1.eq_of_nhds, sphericalFn_eq]
  have h1 := key (-ν)
  have h2 := key ν
  rw [neg_sq] at h1
  linear_combination (h1 - h2) / (2 * ν)

/-- `φ_{1/2}(d) = sech(d/2)`, the complementary-series spherical function at eigenvalue `¾`. -/
theorem sphericalFn_half {d : ℝ} (hd : d ≠ 0) : sphericalFn (1 / 2) d = 1 / Real.cosh (d / 2) := by
  have hs : Real.sinh (d / 2) ≠ 0 := by
    rw [ne_eq, Real.sinh_eq_zero]; intro h; exact hd (by linarith)
  have hc : Real.cosh (d / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have h2 : Real.sinh d = 2 * Real.sinh (d / 2) * Real.cosh (d / 2) := by
    rw [← Real.sinh_two_mul]; congr 1; ring
  rw [sphericalFn, h2, show 1 / 2 * d = d / 2 by ring]
  field_simp

/-- **The pole is spherical.** `2cosh(d/2) = (3/2)φ_{3/2}(d) + ½φ_{1/2}(d)`. -/
theorem two_cosh_half_eq_spherical {d : ℝ} (hd : d ≠ 0) :
    2 * Real.cosh (d / 2) = 3 / 2 * sphericalFn (3 / 2) d + 1 / 2 * sphericalFn (1 / 2) d := by
  have hs : Real.sinh d ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
  have hsum : Real.sinh (3 / 2 * d) + Real.sinh (1 / 2 * d) = 2 * Real.sinh d * Real.cosh (d / 2) := by
    have e1 : 3 / 2 * d = d + d / 2 := by ring
    have e2 : 1 / 2 * d = d - d / 2 := by ring
    rw [e1, e2, Real.sinh_add, Real.sinh_sub]; ring
  unfold sphericalFn
  rw [show (3 / 2 : ℝ) * (Real.sinh (3 / 2 * d) / (3 / 2 * Real.sinh d)) +
      1 / 2 * (Real.sinh (1 / 2 * d) / (1 / 2 * Real.sinh d)) =
      (Real.sinh (3 / 2 * d) + Real.sinh (1 / 2 * d)) / Real.sinh d by field_simp, hsum]
  field_simp

/-- **The Frobenius is the standard Green function plus the complementary piece.**
`2πG_{1/2}(d) = 2πG_{3/2}(d) + ½φ_{1/2}(d)`. -/
theorem archProfile_eq_spherical {d : ℝ} (hd : d ≠ 0) :
    archProfile d = 2 * π * hyperbolicGreen (3 / 2) d + 1 / 2 * sphericalFn (1 / 2) d := by
  rw [archProfile_eq_standard_add_spherical hd, sphericalFn_half hd]
  ring

/-- **The complementary series cancels.** `2cosh(d/2) − 2πG_{1/2}(d) = (3/2)φ_{3/2}(d) − 2πG_{3/2}(d)`. -/
theorem compensation_eq_spherical {d : ℝ} (hd : d ≠ 0) :
    2 * Real.cosh (d / 2) - archProfile d =
      3 / 2 * sphericalFn (3 / 2) d - 2 * π * hyperbolicGreen (3 / 2) d := by
  rw [two_cosh_half_eq_spherical hd, archProfile_eq_spherical hd]
  ring

/-- **Weil's archimedean compensation on two atoms** is `(3/2)φ_{3/2} − 2πG_{3/2}` at the hyperbolic
distance `|log m − log n|` of the degree points. -/
theorem archCompensation_eq_spherical {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    archCompensation m n =
      3 / 2 * sphericalFn (3 / 2) |Real.log m - Real.log n| -
        2 * π * hyperbolicGreen (3 / 2) |Real.log m - Real.log n| := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : |Real.log m - Real.log n| ≠ 0 := by
    rw [abs_ne_zero, sub_ne_zero]
    intro h
    exact hmn (by exact_mod_cast Real.log_injOn_pos hm' hn' h)
  rw [← compensation_eq_spherical hne, archCompensation, ← Real.cosh_abs (_ / 2), abs_div,
    abs_two]
  rfl

/-- **Weil's archimedean-plus-pole weight** is `4πG_{3/2} − 3φ_{3/2}`. -/
theorem weilKernel_eq_spherical {u : ℝ} (hu : u ≠ 0) :
    RHTower.ArchimedeanKernel.weilKernel u =
      4 * π * hyperbolicGreen (3 / 2) u - 3 * sphericalFn (3 / 2) u := by
  rw [weilKernel_eq_hyperbolicGreen hu]
  have h1 := archProfile_eq_hyperbolicGreen hu
  have h2 := archProfile_eq_spherical hu
  have h3 := two_cosh_half_eq_spherical hu
  linear_combination 2 * (h2 - h1) - 2 * h3

/-! ## The plastic crossing -/

/-- The sign of `(3/2)φ_{3/2} − 2πG_{3/2}` is the sign of `e^{3d} − e^d − 1`, `d > 0`. -/
theorem compensation_mul_eq {d : ℝ} (hd : 0 < d) :
    (2 * Real.cosh (d / 2) - archProfile d) * (2 * Real.sinh d * Real.exp (3 * d / 2)) =
      Real.exp d ^ 3 - Real.exp d - 1 := by
  have hs : Real.sinh d ≠ 0 := (Real.sinh_pos_iff.mpr hd).ne'
  rw [compensation_eq_spherical hd.ne']
  unfold sphericalFn hyperbolicGreen
  have hπ : π ≠ 0 := Real.pi_ne_zero
  set u := Real.exp (d / 2) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have e1 : Real.exp (3 * d / 2) = u ^ 3 := by rw [hu, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp d = u ^ 2 := by rw [hu, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Real.exp (-(3 / 2 - 1) * d) = u⁻¹ := by
    rw [hu, ← Real.exp_neg]; congr 1; ring
  have e4 : Real.sinh (3 / 2 * d) = (u ^ 3 - (u ^ 3)⁻¹) / 2 := by
    rw [Real.sinh_eq, ← e1, ← Real.exp_neg]; congr 2 <;> ring_nf
  rw [e1, e2, e3, e4]
  field_simp
  ring

/-- **The plastic law, spectrally.** For `d > 0`, `C_∞(d) < 0` iff `e^{3d} < e^d + 1`. -/
theorem compensation_neg_iff {d : ℝ} (hd : 0 < d) :
    2 * Real.cosh (d / 2) - archProfile d < 0 ↔ Real.exp d ^ 3 < Real.exp d + 1 := by
  have hpos : 0 < 2 * Real.sinh d * Real.exp (3 * d / 2) :=
    mul_pos (mul_pos two_pos (Real.sinh_pos_iff.mpr hd)) (Real.exp_pos _)
  have h := compensation_mul_eq hd
  constructor
  · intro hneg
    have : (2 * Real.cosh (d / 2) - archProfile d) * (2 * Real.sinh d * Real.exp (3 * d / 2)) < 0 :=
      mul_neg_of_neg_of_pos hneg hpos
    linarith
  · intro hlt
    by_contra hge
    push Not at hge
    have : 0 ≤ (2 * Real.cosh (d / 2) - archProfile d) * (2 * Real.sinh d * Real.exp (3 * d / 2)) :=
      mul_nonneg hge hpos.le
    linarith

/-- For `d > 0`, `C_∞(d) > 0` iff `e^{3d} > e^d + 1`. -/
theorem compensation_pos_iff {d : ℝ} (hd : 0 < d) :
    0 < 2 * Real.cosh (d / 2) - archProfile d ↔ Real.exp d + 1 < Real.exp d ^ 3 := by
  have hpos : 0 < 2 * Real.sinh d * Real.exp (3 * d / 2) :=
    mul_pos (mul_pos two_pos (Real.sinh_pos_iff.mpr hd)) (Real.exp_pos _)
  have h := compensation_mul_eq hd
  constructor
  · intro hp
    have := mul_pos hp hpos
    linarith
  · intro hlt
    by_contra hle
    push Not at hle
    have : (2 * Real.cosh (d / 2) - archProfile d) * (2 * Real.sinh d * Real.exp (3 * d / 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hpos.le
    linarith

end GaloisForLFunctions.HyperbolicArakelovTheory
