/-
# Localization of the scaffold patch square (mixed-pair wiring, step B7′)

The one obstruction to the mixed-pair tower avoiding `closedBall 0 2` is the depth-1 scaffold
patch `{v : T v ∈ closedBall c 4}` (a `σ₁`-lift landing in the ball forces its `T`-predecessor
into the critical-value ball).  This file pins the patch's SQUARE: for a patch point `v`, the
functional equation sends `v²` to `T(v)² + c ∈ closedBall (c²+c) (8‖c‖+16)`, deep in the far
field where the below-anchor identity (`SectionIdentityBelowAnchor`) and the explicit rate
(`BottcherExplicitRate`) give `v² ∈ closedBall (c²+c) (8‖c‖+17)` — relative deviation
`≤ 9/‖c‖`, so the patch itself sits in two antipodal angular wedges of width `O(1/‖c‖)` at
`½·arg(c²+c)`.  The wedge-slit scaffold consumes this.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.SectionIdentityBelowAnchor
import GaloisForLFunctions.Bottcher.GreenBallPinch
import GaloisForLFunctions.Bottcher.BottcherExplicitRate
import GaloisForLFunctions.Bottcher.ComplexLogBound
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set

namespace Bottcher

/-- **The patch square localizes.**  A scaffold-annulus point whose section value lies in
`closedBall c 4` has its square within `8‖c‖ + 17` of `c² + c`. -/
theorem patch_square_mem_closedBall {c : ℂ} {rlo R₀ Ra : ℝ}
    (S : TowerSection c rlo R₀) (hc : (1000:ℝ) ≤ ‖c‖)
    (hrlo0 : 0 < rlo) (hRa1 : 1 < Ra) (hRaR₀ : Ra < R₀)
    (hfar : ∀ w : ℂ, Ra < ‖w‖ → ‖w‖ < R₀ → bottcherCoord c (S.T w) = w)
    (hrlo_ceiling : Real.log rlo ≤ (Real.log (‖c‖ ^ 2 + ‖c‖) + 1) / 2)
    {v : ℂ} (hv : v ∈ annulusSet rlo R₀) (hv2 : v ^ 2 ∈ annulusSet rlo R₀)
    (hpatch : ‖S.T v - c‖ ≤ 4) :
    ‖v ^ 2 - (c ^ 2 + c)‖ ≤ 8 * ‖c‖ + 17 := by
  have hc0 : (0:ℝ) < ‖c‖ := by linarith
  have hc100 : (100:ℝ) ≤ ‖c‖ := by linarith
  -- the functional equation at the patch point
  have hfe : S.T (v ^ 2) = (S.T v) ^ 2 + c := S.fe v hv hv2
  -- the image ball: `T(v²) ∈ closedBall (c²+c) (8‖c‖+16)`
  have hT2ball : ‖S.T (v ^ 2) - (c ^ 2 + c)‖ ≤ 8 * ‖c‖ + 16 := by
    have hfact : S.T (v ^ 2) - (c ^ 2 + c) = (S.T v - c) * (S.T v + c) := by
      rw [hfe]
      ring
    rw [hfact, norm_mul]
    have h2 : ‖S.T v + c‖ ≤ 2 * ‖c‖ + 4 := by
      have h3 : ‖(S.T v - c) + (c + c)‖ ≤ ‖S.T v - c‖ + ‖c + c‖ := norm_add_le _ _
      have h4 : (S.T v - c) + (c + c) = S.T v + c := by ring
      have h5 : ‖c + c‖ ≤ 2 * ‖c‖ := by
        have := norm_add_le c c
        linarith
      rw [h4] at h3
      linarith
    calc ‖S.T v - c‖ * ‖S.T v + c‖ ≤ 4 * (2 * ‖c‖ + 4) := by
          apply mul_le_mul hpatch h2 (norm_nonneg _) (by norm_num)
      _ = 8 * ‖c‖ + 16 := by ring
  -- the image is deep in the far field
  have hccnorm : ‖c‖ ^ 2 - ‖c‖ ≤ ‖c ^ 2 + c‖ := by
    have h1 : ‖c ^ 2‖ ≤ ‖c ^ 2 + c‖ + ‖c‖ := by
      have h2 : ‖(c ^ 2 + c) + (-c)‖ ≤ ‖c ^ 2 + c‖ + ‖-c‖ := norm_add_le _ _
      rw [add_neg_cancel_right, norm_neg] at h2
      exact h2
    rw [norm_pow] at h1
    linarith
  have hT2lo : (9:ℝ)/10 * ‖c‖ ^ 2 ≤ ‖S.T (v ^ 2)‖ := by
    have h1 : ‖c ^ 2 + c‖ - ‖S.T (v ^ 2)‖ ≤ ‖S.T (v ^ 2) - (c ^ 2 + c)‖ := by
      have h2 := norm_sub_norm_le (c ^ 2 + c) (S.T (v ^ 2))
      rwa [norm_sub_rev] at h2
    nlinarith
  -- level bookkeeping: `log ‖v²‖ = 2·G(T v) ≥ 4h − ½` clears the identity ceiling
  have hpinch := abs_le.mp (abs_greenFunctionDyn_sub_two_crit_le hc100 hpatch)
  have h2h := abs_le.mp (abs_two_greenCritical_sub_log_le hc100)
  have hlev2 : greenFunctionDyn c (S.T (v ^ 2)) = Real.log ‖v ^ 2‖ := S.level (v ^ 2) hv2
  have hGdouble : greenFunctionDyn c (S.T (v ^ 2)) = 2 * greenFunctionDyn c (S.T v) := by
    rw [hfe]
    have h1 := greenFunctionDyn_quadratic c (S.T v)
    simpa [quadratic] using h1
  have hceil_le : Real.log (‖c‖ ^ 2 + ‖c‖) ≤ 2 * Real.log ‖c‖ + 1 / 1000 := by
    have h1 : ‖c‖ ^ 2 + ‖c‖ = ‖c‖ ^ 2 * (1 + 1 / ‖c‖) := by
      field_simp
    rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_pow, Nat.cast_ofNat]
    have h2 : Real.log (1 + 1 / ‖c‖) ≤ 1 / ‖c‖ := by
      have h3 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1 / ‖c‖ by positivity)
      linarith
    have h4 : (1:ℝ) / ‖c‖ ≤ 1 / 1000 := by
      rw [div_le_div_iff₀ hc0 (by norm_num)]
      linarith
    linarith
  have hexp3 : Real.exp 3 ≤ 27 := by
    have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h1]
    have h3 : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9
      linarith
    calc Real.exp 1 ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h3 3
      _ = 27 := by norm_num
  have hlogR3 : (3:ℝ) ≤ Real.log ‖c‖ := by
    have h1 : Real.exp 3 ≤ ‖c‖ := by linarith
    calc (3:ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      _ ≤ Real.log ‖c‖ := Real.log_le_log (Real.exp_pos 3) h1
  have hw_lo : (Real.log (‖c‖ ^ 2 + ‖c‖) + 1) / 2 < Real.log ‖v ^ 2‖ := by
    rw [← hlev2, hGdouble]
    linarith [hpinch.1, h2h.1]
  -- the below-anchor identity at `v²`
  have hid : bottcherCoord c (S.T (v ^ 2)) = v ^ 2 :=
    sectionInverse_identity_at S (by linarith) hRa1 hRaR₀ hfar hrlo0 hrlo_ceiling
      hw_lo hv2.2
  -- the explicit rate at `T(v²)`
  have hcz : ‖c‖ ≤ ‖S.T (v ^ 2)‖ := by nlinarith
  have h2z : (2:ℝ) < ‖S.T (v ^ 2)‖ := by nlinarith
  have hrate := norm_bottcherCoord_sub_id_le hcz h2z
  have hrate1 : ‖bottcherCoord c (S.T (v ^ 2)) - S.T (v ^ 2)‖ ≤ 1 := by
    have h1 : 4 * ‖c‖ / ‖S.T (v ^ 2)‖ ≤ 1 := by
      rw [div_le_one (by nlinarith)]
      nlinarith
    linarith
  rw [hid] at hrate1
  -- assemble
  have hsplit : ‖v ^ 2 - (c ^ 2 + c)‖
      = ‖(v ^ 2 - S.T (v ^ 2)) + (S.T (v ^ 2) - (c ^ 2 + c))‖ := by
    congr 1
    ring
  rw [hsplit]
  calc ‖(v ^ 2 - S.T (v ^ 2)) + (S.T (v ^ 2) - (c ^ 2 + c))‖
      ≤ ‖v ^ 2 - S.T (v ^ 2)‖ + ‖S.T (v ^ 2) - (c ^ 2 + c)‖ := norm_add_le _ _
    _ ≤ 1 + (8 * ‖c‖ + 16) := add_le_add hrate1 hT2ball
    _ = 8 * ‖c‖ + 17 := by ring

/-- **Lattice localization of the patch angle.**  If `exp(ξ)²` lies within `‖a‖/100` of `a`,
then `ξ.im` lies within `1/100` of the half-argument lattice `arg(a)/2 + πℤ` — the two
antipodal wedges the wedge-slit scaffold must dodge. -/
theorem exists_int_im_near_half_arg_of_sq_near {a : ℂ} (ha : a ≠ 0)
    {ξ : ℂ} (hρ : ‖Complex.exp ξ ^ 2 - a‖ ≤ 1 / 100 * ‖a‖) :
    ∃ n : ℤ, |ξ.im - (Complex.arg a / 2 + Real.pi * n)| ≤ 1 / 100 := by
  have hapos : (0:ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  set u : ℂ := Complex.exp ξ ^ 2 / a with hudef
  have hu1 : ‖u - 1‖ ≤ 1 / 100 := by
    have h1 : u - 1 = (Complex.exp ξ ^ 2 - a) / a := by
      rw [hudef]
      field_simp
    rw [h1, norm_div, div_le_iff₀ hapos]
    linarith
  have hune : u ≠ 0 := by
    intro h0
    rw [h0] at hu1
    norm_num at hu1
  have hexpsq : Complex.exp (2 * ξ) = Complex.exp ξ ^ 2 := by
    rw [two_mul, Complex.exp_add, sq]
  have hexp2 : Complex.exp (2 * ξ) = a * u := by
    rw [hexpsq, hudef, mul_comm, div_mul_cancel₀ _ ha]
  have hkey : Complex.exp (2 * ξ - Complex.log a - Complex.log u) = 1 := by
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_log ha, Complex.exp_log hune, hexp2]
    field_simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hkey
  have him' : 2 * ξ.im - Complex.arg a - Complex.arg u = (n : ℝ) * (2 * Real.pi) := by
    have him := congrArg Complex.im hn
    rw [show ((n : ℂ) * (2 * Real.pi * Complex.I))
        = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I from by push_cast; ring] at him
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.log_im, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, mul_zero, add_zero, mul_one] at him
    exact him
  have hargu : |Complex.arg u| ≤ 1 / 50 := by
    have h2 : ‖u - 1‖ ≤ 1 / 2 := by linarith
    have h3 := norm_clog_one_add_le h2
    rw [show (1 : ℂ) + (u - 1) = u from by ring] at h3
    calc |Complex.arg u| = |(Complex.log u).im| := by rw [Complex.log_im]
      _ ≤ ‖Complex.log u‖ := Complex.abs_im_le_norm _
      _ ≤ 2 * ‖u - 1‖ := h3
      _ ≤ 1 / 50 := by linarith
  refine ⟨n, ?_⟩
  have h5 : ξ.im - (Complex.arg a / 2 + Real.pi * n) = Complex.arg u / 2 := by
    linarith [him']
  rw [h5, abs_div]
  have h6 : |(2:ℝ)| = 2 := by norm_num
  rw [h6, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith [hargu]

end Bottcher
