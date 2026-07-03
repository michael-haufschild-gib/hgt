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
import GaloisForLFunctions.Bottcher.SectionInverse
import GaloisForLFunctions.Bottcher.SlitAnnulus
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

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

/-- **Existence of a patch-covering slit center.**  The patch `{v : T v ∈ closedBall c 4}` is
the continuous image of the connected ball under the section inverse, so it meets only ONE of
the two antipodal half-argument wedges; that wedge's center (normalized to `[−π, π]`) is a
slit angle whose window avoids the whole patch — the input the wedge-slit scaffold
(`exists_scaffold_chain_window`) consumes. -/
theorem exists_slit_center_avoiding_patch {c : ℂ} {rlo R₀ Ra : ℝ}
    (S : TowerSection c rlo R₀) (hc : (1000:ℝ) ≤ ‖c‖)
    (hrlo1 : 1 < rlo) (hRa1 : 1 < Ra) (hRaR₀ : Ra < R₀)
    (hfar : ∀ w : ℂ, Ra < ‖w‖ → ‖w‖ < R₀ → bottcherCoord c (S.T w) = w)
    (hrlo_ceiling : Real.log rlo ≤ (Real.log (‖c‖ ^ 2 + ‖c‖) + 1) / 2)
    (hrlo2h : Real.log rlo < 2 * greenFunctionDyn c 0 - 1/4)
    (hR₀4h : 4 * greenFunctionDyn c 0 + 1 < Real.log R₀)
    (hsurj : ∀ z : ℂ, Real.log rlo < greenFunctionDyn c z →
      greenFunctionDyn c z < Real.log R₀ → z ∈ S.T '' annulusSet rlo R₀) :
    ∃ θs : ℝ, -Real.pi ≤ θs ∧ θs ≤ Real.pi ∧
      ∀ ra RW : ℝ, rlo < ra → ra < RW → RW < R₀ →
      ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
        S.T v ∉ Metric.closedBall c 4 := by
  classical
  have hπ := Real.pi_pos
  have hπ3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hc100 : (100:ℝ) ≤ ‖c‖ := by linarith
  have h2h := abs_le.mp (abs_two_greenCritical_sub_log_le hc100)
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
  have hlogc3 : (3:ℝ) ≤ Real.log ‖c‖ := by
    have h1 : Real.exp 3 ≤ ‖c‖ := by linarith
    calc (3:ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      _ ≤ Real.log ‖c‖ := Real.log_le_log (Real.exp_pos 3) h1
  have hccnorm : ‖c‖ ^ 2 - ‖c‖ ≤ ‖c ^ 2 + c‖ := by
    have h2 : ‖(c ^ 2 + c) + (-c)‖ ≤ ‖c ^ 2 + c‖ + ‖-c‖ := norm_add_le _ _
    rw [add_neg_cancel_right, norm_neg, norm_pow] at h2
    linarith
  have hane : (c ^ 2 + c) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hccnorm
    nlinarith
  set ψ₀ : ℝ := Complex.arg (c ^ 2 + c) / 2 with hψdef
  have hψlo : -(Real.pi / 2) < ψ₀ := by
    have := Complex.neg_pi_lt_arg (c ^ 2 + c)
    rw [hψdef]
    linarith
  have hψhi : ψ₀ ≤ Real.pi / 2 := by
    have := Complex.arg_le_pi (c ^ 2 + c)
    rw [hψdef]
    linarith
  -- the critical-value ball sits inside the band
  have hballband : ∀ z ∈ Metric.closedBall c 4, Real.log rlo < greenFunctionDyn c z ∧
      greenFunctionDyn c z < Real.log R₀ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hp := abs_le.mp (abs_greenFunctionDyn_sub_two_crit_le hc100 hz)
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
  -- the key localization at any annulus point over the ball
  have hkey : ∀ v ∈ annulusSet rlo R₀, S.T v ∈ Metric.closedBall c 4 →
      ∀ ξ : ℂ, v = Complex.exp ξ →
      ∃ n : ℤ, |ξ.im - (ψ₀ + Real.pi * n)| ≤ 1 / 100 := by
    intro v hv hball ξ hξ
    have hballn : ‖S.T v - c‖ ≤ 4 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hball
      exact hball
    have hlev : greenFunctionDyn c (S.T v) = Real.log ‖v‖ := S.level v hv
    have hp := abs_le.mp (abs_greenFunctionDyn_sub_two_crit_le hc100 hballn)
    have hvpos : (0:ℝ) < ‖v‖ := lt_trans (by linarith) hv.1
    have hexp2log : Real.exp (2 * Real.log ‖v‖) = ‖v‖ ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log hvpos]
      ring
    have hv2 : v ^ 2 ∈ annulusSet rlo R₀ := by
      rw [annulusSet, Set.mem_setOf_eq, norm_pow]
      constructor
      · have h1 : Real.log rlo < 2 * Real.log ‖v‖ := by
          rw [← hlev]
          linarith [hp.1]
        calc rlo = Real.exp (Real.log rlo) := (Real.exp_log (by linarith)).symm
          _ < Real.exp (2 * Real.log ‖v‖) := Real.exp_lt_exp.mpr h1
          _ = ‖v‖ ^ 2 := hexp2log
      · have h1 : 2 * Real.log ‖v‖ < Real.log R₀ := by
          rw [← hlev]
          linarith [hp.2]
        calc ‖v‖ ^ 2 = Real.exp (2 * Real.log ‖v‖) := hexp2log.symm
          _ < Real.exp (Real.log R₀) := Real.exp_lt_exp.mpr h1
          _ = R₀ := Real.exp_log (by linarith)
    have hsq := patch_square_mem_closedBall S hc (by linarith : (0:ℝ) < rlo) hRa1 hRaR₀ hfar
      hrlo_ceiling hv hv2 hballn
    have hsmall : ‖Complex.exp ξ ^ 2 - (c ^ 2 + c)‖ ≤ 1 / 100 * ‖c ^ 2 + c‖ := by
      rw [← hξ]
      calc ‖v ^ 2 - (c ^ 2 + c)‖ ≤ 8 * ‖c‖ + 17 := hsq
        _ ≤ 1 / 100 * (‖c‖ ^ 2 - ‖c‖) := by nlinarith
        _ ≤ 1 / 100 * ‖c ^ 2 + c‖ := by nlinarith [hccnorm]
    obtain ⟨n, hn⟩ := exists_int_im_near_half_arg_of_sq_near hane hsmall
    refine ⟨n, ?_⟩
    rw [hψdef]
    exact hn
  -- trigonometric helpers
  have hcos_shift : ∀ (k : ℤ) (δ : ℝ), Real.cos ((k:ℝ) * (2 * Real.pi) + δ) = Real.cos δ := by
    intro k δ
    rw [Real.cos_add, Real.cos_int_mul_two_pi]
    have h1 : ((k : ℝ) * (2 * Real.pi)) = ((2 * k : ℤ) : ℝ) * Real.pi := by
      push_cast
      ring
    rw [h1, Real.sin_int_mul_pi]
    ring
  have hcosδ : ∀ δ : ℝ, |δ| ≤ 1/100 → 0 < Real.cos δ := by
    intro δ hδ
    have h1 := abs_le.mp hδ
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · show -(Real.pi/2) < δ
      linarith
    · show δ < Real.pi/2
      linarith
  have hside_of : ∀ (x : ℝ) (n : ℤ), |x - (ψ₀ + Real.pi * n)| ≤ 1/100 →
      (Even n → 0 < Real.cos (x - ψ₀)) ∧ (Odd n → Real.cos (x - ψ₀) < 0) := by
    intro x n hxn
    constructor
    · rintro ⟨k, hk⟩
      have hx : x - ψ₀ = (k:ℝ) * (2*Real.pi) + (x - (ψ₀ + Real.pi * n)) := by
        rw [hk]
        push_cast
        ring
      rw [hx, hcos_shift k _]
      exact hcosδ _ hxn
    · rintro ⟨k, hk⟩
      have hx : x - ψ₀ = (k:ℝ) * (2*Real.pi) + ((x - (ψ₀ + Real.pi * n)) + Real.pi) := by
        rw [hk]
        push_cast
        ring
      rw [hx, hcos_shift k _, Real.cos_add_pi]
      have := hcosδ _ hxn
      linarith
  -- the side functional and its exp-coordinate form
  set Q : ℂ → ℝ := fun v => (v * Complex.exp (-(ψ₀:ℂ) * Complex.I)).re with hQdef
  have hQexp : ∀ ξ : ℂ, Q (Complex.exp ξ) = Real.exp ξ.re * Real.cos (ξ.im - ψ₀) := by
    intro ξ
    have h1 : Complex.exp ξ * Complex.exp (-(ψ₀:ℂ) * Complex.I)
        = Complex.exp (ξ - (ψ₀:ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have h2 : (ξ - (ψ₀:ℂ) * Complex.I).re = ξ.re := by
      simp [Complex.sub_re, Complex.mul_re]
    have h3 : (ξ - (ψ₀:ℂ) * Complex.I).im = ξ.im - ψ₀ := by
      simp [Complex.sub_im, Complex.mul_im]
    rw [hQdef]
    show (Complex.exp ξ * Complex.exp (-(ψ₀:ℂ) * Complex.I)).re = _
    rw [h1, Complex.exp_re, h2, h3]
  have hQcont : Continuous Q := by
    rw [hQdef]
    exact Complex.continuous_re.comp (continuous_mul_const _)
  -- the patch is connected and one-sided
  set P : Set ℂ := S.inv '' Metric.closedBall c 4 with hPdef
  have hPconn : IsPreconnected P := by
    apply IsPreconnected.image (convex_closedBall c 4).isPreconnected
    intro z hz
    have hzim : z ∈ S.T '' annulusSet rlo R₀ := hsurj z (hballband z hz).1 (hballband z hz).2
    exact ((S.inv_analytic z hzim).continuousAt).continuousWithinAt
  have hPsub : P ⊆ {v : ℂ | 0 < Q v} ∪ {v : ℂ | Q v < 0} := by
    rintro v ⟨z, hz, rfl⟩
    have hzim : z ∈ S.T '' annulusSet rlo R₀ := hsurj z (hballband z hz).1 (hballband z hz).2
    have hwann : S.inv z ∈ annulusSet rlo R₀ := S.inv_mem hzim
    have hwT : S.T (S.inv z) = z := S.inv_right hzim
    have hwne : S.inv z ≠ 0 := by
      intro h0
      have h1 := hwann.1
      rw [h0, norm_zero] at h1
      linarith
    have hξ : S.inv z = Complex.exp (Complex.log (S.inv z)) := (Complex.exp_log hwne).symm
    obtain ⟨n, hn⟩ := hkey (S.inv z) hwann (by rw [hwT]; exact hz) _ hξ
    have hQv : Q (S.inv z) = Real.exp (Complex.log (S.inv z)).re
        * Real.cos ((Complex.log (S.inv z)).im - ψ₀) := by
      conv_lhs => rw [hξ]
      exact hQexp _
    rcases Int.even_or_odd n with he | ho
    · left
      show 0 < Q (S.inv z)
      rw [hQv]
      exact mul_pos (Real.exp_pos _) ((hside_of _ n hn).1 he)
    · right
      show Q (S.inv z) < 0
      rw [hQv]
      have h1 := (hside_of _ n hn).2 ho
      nlinarith [Real.exp_pos (Complex.log (S.inv z)).re]
  have hUpo : IsOpen {v : ℂ | 0 < Q v} := isOpen_lt continuous_const hQcont
  have hUmo : IsOpen {v : ℂ | Q v < 0} := isOpen_lt hQcont continuous_const
  have hdisj : Disjoint {v : ℂ | 0 < Q v} {v : ℂ | Q v < 0} := by
    rw [Set.disjoint_left]
    intro v h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    linarith
  -- the shared window argument
  have hwindow : ∀ θs : ℝ,
      (∀ v ∈ annulusSet rlo R₀, S.T v ∈ Metric.closedBall c 4 →
        ∀ ξ : ℂ, v = Complex.exp ξ →
        ∃ k : ℤ, |ξ.im - (θs + (k:ℝ) * (2 * Real.pi))| ≤ 1/100) →
      ∀ ra RW : ℝ, rlo < ra → ra < RW → RW < R₀ →
      ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
        S.T v ∉ Metric.closedBall c 4 := by
    intro θs hlat ra RW hra hraRW hRW v hv hball
    have hvann : v ∈ annulusSet rlo R₀ := by
      have h1 := arcAnnulus_subset (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8)
        (by linarith : (0:ℝ) < ra) hraRW hv
      exact ⟨lt_trans hra h1.1, lt_trans h1.2 hRW⟩
    obtain ⟨ξ, hξbox, hξexp⟩ := hv
    obtain ⟨k, hk⟩ := hlat v hvann hball ξ hξexp.symm
    have him1 : θs + Real.pi / 8 < ξ.im := hξbox.2.2.1
    have him2 : ξ.im < θs + 2 * Real.pi - Real.pi / 8 := hξbox.2.2.2
    have habs := abs_le.mp hk
    rcases le_or_gt k 0 with hk0 | hk0
    · have hk0' : (k:ℝ) ≤ 0 := by exact_mod_cast hk0
      have h2πk : (k:ℝ) * (2 * Real.pi) ≤ 0 := by nlinarith
      linarith [habs.2]
    · have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk0
      have h2πk : 2 * Real.pi ≤ (k:ℝ) * (2 * Real.pi) := by nlinarith
      linarith [habs.1]
  -- the dichotomy chooses the slit center
  rcases hPconn.subset_or_subset hUpo hUmo hdisj hPsub with hPpos | hPneg
  · -- even side: the true wedge is at `ψ₀`
    refine ⟨ψ₀, by linarith, by linarith, hwindow ψ₀ ?_⟩
    intro v hv hball ξ hξ
    obtain ⟨n, hn⟩ := hkey v hv hball ξ hξ
    have hvP : v ∈ P := ⟨S.T v, hball, S.inv_left hv⟩
    have hQpos : 0 < Q v := hPpos hvP
    have hcospos : 0 < Real.cos (ξ.im - ψ₀) := by
      rw [hξ, hQexp ξ] at hQpos
      nlinarith [Real.exp_pos ξ.re]
    have heven : Even n := by
      rcases Int.even_or_odd n with he | ho
      · exact he
      · exfalso
        have := (hside_of ξ.im n hn).2 ho
        linarith
    obtain ⟨j, hj⟩ := heven
    refine ⟨j, ?_⟩
    have h1 : ψ₀ + Real.pi * n = ψ₀ + (j:ℝ) * (2 * Real.pi) := by
      rw [hj]
      push_cast
      ring
    rw [← h1]
    exact hn
  · -- odd side: the true wedge is at `ψ₀ ± π`
    have hodd_lattice : ∀ (θs : ℝ) (j₀ : ℤ), θs = ψ₀ + Real.pi + (j₀:ℝ) * (2 * Real.pi) →
        ∀ v ∈ annulusSet rlo R₀, S.T v ∈ Metric.closedBall c 4 →
        ∀ ξ : ℂ, v = Complex.exp ξ →
        ∃ k : ℤ, |ξ.im - (θs + (k:ℝ) * (2 * Real.pi))| ≤ 1/100 := by
      intro θs j₀ hθeq v hv hball ξ hξ
      obtain ⟨n, hn⟩ := hkey v hv hball ξ hξ
      have hvP : v ∈ P := ⟨S.T v, hball, S.inv_left hv⟩
      have hQneg : Q v < 0 := hPneg hvP
      have hcosneg : Real.cos (ξ.im - ψ₀) < 0 := by
        rw [hξ, hQexp ξ] at hQneg
        nlinarith [Real.exp_pos ξ.re]
      have hodd : Odd n := by
        rcases Int.even_or_odd n with he | ho
        · exfalso
          have := (hside_of ξ.im n hn).1 he
          linarith
        · exact ho
      obtain ⟨j, hj⟩ := hodd
      refine ⟨j - j₀, ?_⟩
      have h1 : ψ₀ + Real.pi * n = θs + ((j - j₀ : ℤ):ℝ) * (2 * Real.pi) := by
        rw [hj, hθeq]
        push_cast
        ring
      rw [← h1]
      exact hn
    rcases le_or_gt ψ₀ 0 with hψ0 | hψ0
    · refine ⟨ψ₀ + Real.pi, by linarith, by linarith,
        hwindow (ψ₀ + Real.pi) (hodd_lattice (ψ₀ + Real.pi) 0 (by push_cast; ring))⟩
    · refine ⟨ψ₀ - Real.pi, by linarith, by linarith,
        hwindow (ψ₀ - Real.pi) (hodd_lattice (ψ₀ - Real.pi) (-1) (by push_cast; ring))⟩

end Bottcher

namespace Bottcher

/-- **Parametric patch square localization.**  A scaffold-annulus point whose section value lies
in `closedBall c (s²)` (`2 ≤ s`, `s² ≤ ‖c‖/40`) has its square within `2s²‖c‖ + s⁴ + 1` of
`c² + c`. -/
theorem patch_square_mem_closedBall_s {c : ℂ} {rlo R₀ Ra : ℝ}
    (S : TowerSection c rlo R₀) (hc : (1000:ℝ) ≤ ‖c‖)
    (hrlo0 : 0 < rlo) (hRa1 : 1 < Ra) (hRaR₀ : Ra < R₀)
    (hfar : ∀ w : ℂ, Ra < ‖w‖ → ‖w‖ < R₀ → bottcherCoord c (S.T w) = w)
    (hrlo_ceiling : Real.log rlo ≤ (Real.log (‖c‖ ^ 2 + ‖c‖) + 1) / 2)
    {s : ℝ} (hs2 : 2 ≤ s) (hs40 : s ^ 2 ≤ ‖c‖ / 40)
    {v : ℂ} (hv : v ∈ annulusSet rlo R₀) (hv2 : v ^ 2 ∈ annulusSet rlo R₀)
    (hpatch : ‖S.T v - c‖ ≤ s ^ 2) :
    ‖v ^ 2 - (c ^ 2 + c)‖ ≤ 2 * s ^ 2 * ‖c‖ + s ^ 4 + 1 := by
  have hc0 : (0:ℝ) < ‖c‖ := by linarith
  have hc100 : (100:ℝ) ≤ ‖c‖ := by linarith
  have hcc : 100 * ‖c‖ ≤ ‖c‖ ^ 2 := by nlinarith
  have hs0 : (0:ℝ) < s := by linarith
  -- the functional equation at the patch point
  have hfe : S.T (v ^ 2) = (S.T v) ^ 2 + c := S.fe v hv hv2
  -- the image ball: `T(v²) ∈ closedBall (c²+c) (2s²‖c‖ + s⁴)`
  have hT2ball : ‖S.T (v ^ 2) - (c ^ 2 + c)‖ ≤ 2 * s ^ 2 * ‖c‖ + s ^ 4 := by
    have hfact : S.T (v ^ 2) - (c ^ 2 + c) = (S.T v - c) * (S.T v + c) := by
      rw [hfe]
      ring
    rw [hfact, norm_mul]
    have h2 : ‖S.T v + c‖ ≤ 2 * ‖c‖ + s ^ 2 := by
      have h3 : ‖(S.T v - c) + (c + c)‖ ≤ ‖S.T v - c‖ + ‖c + c‖ := norm_add_le _ _
      have h4 : (S.T v - c) + (c + c) = S.T v + c := by ring
      have h5 : ‖c + c‖ ≤ 2 * ‖c‖ := by
        have := norm_add_le c c
        linarith
      rw [h4] at h3
      linarith
    calc ‖S.T v - c‖ * ‖S.T v + c‖ ≤ s ^ 2 * (2 * ‖c‖ + s ^ 2) := by
          apply mul_le_mul hpatch h2 (norm_nonneg _) (by positivity)
      _ = 2 * s ^ 2 * ‖c‖ + s ^ 4 := by ring
  -- the image is deep in the far field
  have hccnorm : ‖c‖ ^ 2 - ‖c‖ ≤ ‖c ^ 2 + c‖ := by
    have h1 : ‖c ^ 2‖ ≤ ‖c ^ 2 + c‖ + ‖c‖ := by
      have h2 : ‖(c ^ 2 + c) + (-c)‖ ≤ ‖c ^ 2 + c‖ + ‖-c‖ := norm_add_le _ _
      rw [add_neg_cancel_right, norm_neg] at h2
      exact h2
    rw [norm_pow] at h1
    linarith
  have hradbd : 2 * s ^ 2 * ‖c‖ + s ^ 4 ≤ (21/400) * ‖c‖ ^ 2 := by
    have h1 : 2 * s ^ 2 * ‖c‖ ≤ 2 * (‖c‖ / 40) * ‖c‖ := by nlinarith
    have h2 : s ^ 4 ≤ (‖c‖ / 40) ^ 2 := by nlinarith [sq_nonneg s]
    nlinarith
  have hT2lo : (9:ℝ)/10 * ‖c‖ ^ 2 ≤ ‖S.T (v ^ 2)‖ := by
    have h1 : ‖c ^ 2 + c‖ - ‖S.T (v ^ 2)‖ ≤ ‖S.T (v ^ 2) - (c ^ 2 + c)‖ := by
      have h2 := norm_sub_norm_le (c ^ 2 + c) (S.T (v ^ 2))
      rwa [norm_sub_rev] at h2
    nlinarith
  -- level bookkeeping: `log ‖v²‖ = 2·G(T v) ≥ 4h − ½` clears the identity ceiling
  have hpinch := abs_le.mp (abs_greenFunctionDyn_sub_two_crit_le_s hc100 hs40 hpatch)
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
    _ ≤ 1 + (2 * s ^ 2 * ‖c‖ + s ^ 4) := add_le_add hrate1 hT2ball
    _ = 2 * s ^ 2 * ‖c‖ + s ^ 4 + 1 := by ring

set_option maxHeartbeats 1600000 in
/-- **Parametric slit center avoiding the `s²`-patch.**  As
`exists_slit_center_avoiding_patch`, with the critical-value ball radius freed to `s²`
(`2 ≤ s`, `s² ≤ ‖c‖/40`, and the patch-square smallness
`2s²‖c‖ + s⁴ + 1 ≤ (‖c‖² − ‖c‖)/100`). -/
theorem exists_slit_center_avoiding_patch_s {c : ℂ} {rlo R₀ Ra : ℝ}
    (S : TowerSection c rlo R₀) (hc : (1000:ℝ) ≤ ‖c‖)
    (hrlo1 : 1 < rlo) (hRa1 : 1 < Ra) (hRaR₀ : Ra < R₀)
    (hfar : ∀ w : ℂ, Ra < ‖w‖ → ‖w‖ < R₀ → bottcherCoord c (S.T w) = w)
    (hrlo_ceiling : Real.log rlo ≤ (Real.log (‖c‖ ^ 2 + ‖c‖) + 1) / 2)
    (hrlo2h : Real.log rlo < 2 * greenFunctionDyn c 0 - 1/4)
    (hR₀4h : 4 * greenFunctionDyn c 0 + 1 < Real.log R₀)
    (hsurj : ∀ z : ℂ, Real.log rlo < greenFunctionDyn c z →
      greenFunctionDyn c z < Real.log R₀ → z ∈ S.T '' annulusSet rlo R₀)
    {s : ℝ} (hs2 : 2 ≤ s) (hs40 : s ^ 2 ≤ ‖c‖ / 40)
    (hsmall : 2 * s ^ 2 * ‖c‖ + s ^ 4 + 1 ≤ 1/100 * (‖c‖ ^ 2 - ‖c‖)) :
    ∃ θs : ℝ, -Real.pi ≤ θs ∧ θs ≤ Real.pi ∧
      ∀ ra RW : ℝ, rlo < ra → ra < RW → RW < R₀ →
      ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
        S.T v ∉ Metric.closedBall c (s ^ 2) := by
  classical
  have hπ := Real.pi_pos
  have hπ3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hc100 : (100:ℝ) ≤ ‖c‖ := by linarith
  have h2h := abs_le.mp (abs_two_greenCritical_sub_log_le hc100)
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
  have hlogc3 : (3:ℝ) ≤ Real.log ‖c‖ := by
    have h1 : Real.exp 3 ≤ ‖c‖ := by linarith
    calc (3:ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      _ ≤ Real.log ‖c‖ := Real.log_le_log (Real.exp_pos 3) h1
  have hccnorm : ‖c‖ ^ 2 - ‖c‖ ≤ ‖c ^ 2 + c‖ := by
    have h2 : ‖(c ^ 2 + c) + (-c)‖ ≤ ‖c ^ 2 + c‖ + ‖-c‖ := norm_add_le _ _
    rw [add_neg_cancel_right, norm_neg, norm_pow] at h2
    linarith
  have hane : (c ^ 2 + c) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hccnorm
    nlinarith
  set ψ₀ : ℝ := Complex.arg (c ^ 2 + c) / 2 with hψdef
  have hψlo : -(Real.pi / 2) < ψ₀ := by
    have := Complex.neg_pi_lt_arg (c ^ 2 + c)
    rw [hψdef]
    linarith
  have hψhi : ψ₀ ≤ Real.pi / 2 := by
    have := Complex.arg_le_pi (c ^ 2 + c)
    rw [hψdef]
    linarith
  -- the critical-value ball sits inside the band
  have hballband : ∀ z ∈ Metric.closedBall c (s ^ 2), Real.log rlo < greenFunctionDyn c z ∧
      greenFunctionDyn c z < Real.log R₀ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hp := abs_le.mp (abs_greenFunctionDyn_sub_two_crit_le_s hc100 hs40 hz)
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
  -- the key localization at any annulus point over the ball
  have hkey : ∀ v ∈ annulusSet rlo R₀, S.T v ∈ Metric.closedBall c (s ^ 2) →
      ∀ ξ : ℂ, v = Complex.exp ξ →
      ∃ n : ℤ, |ξ.im - (ψ₀ + Real.pi * n)| ≤ 1 / 100 := by
    intro v hv hball ξ hξ
    have hballn : ‖S.T v - c‖ ≤ s ^ 2 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hball
      exact hball
    have hlev : greenFunctionDyn c (S.T v) = Real.log ‖v‖ := S.level v hv
    have hp := abs_le.mp (abs_greenFunctionDyn_sub_two_crit_le_s hc100 hs40 hballn)
    have hvpos : (0:ℝ) < ‖v‖ := lt_trans (by linarith) hv.1
    have hexp2log : Real.exp (2 * Real.log ‖v‖) = ‖v‖ ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log hvpos]
      ring
    have hv2 : v ^ 2 ∈ annulusSet rlo R₀ := by
      rw [annulusSet, Set.mem_setOf_eq, norm_pow]
      constructor
      · have h1 : Real.log rlo < 2 * Real.log ‖v‖ := by
          rw [← hlev]
          linarith [hp.1]
        calc rlo = Real.exp (Real.log rlo) := (Real.exp_log (by linarith)).symm
          _ < Real.exp (2 * Real.log ‖v‖) := Real.exp_lt_exp.mpr h1
          _ = ‖v‖ ^ 2 := hexp2log
      · have h1 : 2 * Real.log ‖v‖ < Real.log R₀ := by
          rw [← hlev]
          linarith [hp.2]
        calc ‖v‖ ^ 2 = Real.exp (2 * Real.log ‖v‖) := hexp2log.symm
          _ < Real.exp (Real.log R₀) := Real.exp_lt_exp.mpr h1
          _ = R₀ := Real.exp_log (by linarith)
    have hsq := patch_square_mem_closedBall_s S hc (by linarith : (0:ℝ) < rlo) hRa1 hRaR₀ hfar
      hrlo_ceiling hs2 hs40 hv hv2 hballn
    have hsmall' : ‖Complex.exp ξ ^ 2 - (c ^ 2 + c)‖ ≤ 1 / 100 * ‖c ^ 2 + c‖ := by
      rw [← hξ]
      calc ‖v ^ 2 - (c ^ 2 + c)‖ ≤ 2 * s ^ 2 * ‖c‖ + s ^ 4 + 1 := hsq
        _ ≤ 1 / 100 * (‖c‖ ^ 2 - ‖c‖) := hsmall
        _ ≤ 1 / 100 * ‖c ^ 2 + c‖ := by nlinarith [hccnorm]
    obtain ⟨n, hn⟩ := exists_int_im_near_half_arg_of_sq_near hane hsmall'
    refine ⟨n, ?_⟩
    rw [hψdef]
    exact hn
  -- trigonometric helpers
  have hcos_shift : ∀ (k : ℤ) (δ : ℝ), Real.cos ((k:ℝ) * (2 * Real.pi) + δ) = Real.cos δ := by
    intro k δ
    rw [Real.cos_add, Real.cos_int_mul_two_pi]
    have h1 : ((k : ℝ) * (2 * Real.pi)) = ((2 * k : ℤ) : ℝ) * Real.pi := by
      push_cast
      ring
    rw [h1, Real.sin_int_mul_pi]
    ring
  have hcosδ : ∀ δ : ℝ, |δ| ≤ 1/100 → 0 < Real.cos δ := by
    intro δ hδ
    have h1 := abs_le.mp hδ
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · show -(Real.pi/2) < δ
      linarith
    · show δ < Real.pi/2
      linarith
  have hside_of : ∀ (x : ℝ) (n : ℤ), |x - (ψ₀ + Real.pi * n)| ≤ 1/100 →
      (Even n → 0 < Real.cos (x - ψ₀)) ∧ (Odd n → Real.cos (x - ψ₀) < 0) := by
    intro x n hxn
    constructor
    · rintro ⟨k, hk⟩
      have hx : x - ψ₀ = (k:ℝ) * (2*Real.pi) + (x - (ψ₀ + Real.pi * n)) := by
        rw [hk]
        push_cast
        ring
      rw [hx, hcos_shift k _]
      exact hcosδ _ hxn
    · rintro ⟨k, hk⟩
      have hx : x - ψ₀ = (k:ℝ) * (2*Real.pi) + ((x - (ψ₀ + Real.pi * n)) + Real.pi) := by
        rw [hk]
        push_cast
        ring
      rw [hx, hcos_shift k _, Real.cos_add_pi]
      have := hcosδ _ hxn
      linarith
  -- the side functional and its exp-coordinate form
  set Q : ℂ → ℝ := fun v => (v * Complex.exp (-(ψ₀:ℂ) * Complex.I)).re with hQdef
  have hQexp : ∀ ξ : ℂ, Q (Complex.exp ξ) = Real.exp ξ.re * Real.cos (ξ.im - ψ₀) := by
    intro ξ
    have h1 : Complex.exp ξ * Complex.exp (-(ψ₀:ℂ) * Complex.I)
        = Complex.exp (ξ - (ψ₀:ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have h2 : (ξ - (ψ₀:ℂ) * Complex.I).re = ξ.re := by
      simp [Complex.sub_re, Complex.mul_re]
    have h3 : (ξ - (ψ₀:ℂ) * Complex.I).im = ξ.im - ψ₀ := by
      simp [Complex.sub_im, Complex.mul_im]
    rw [hQdef]
    show (Complex.exp ξ * Complex.exp (-(ψ₀:ℂ) * Complex.I)).re = _
    rw [h1, Complex.exp_re, h2, h3]
  have hQcont : Continuous Q := by
    rw [hQdef]
    exact Complex.continuous_re.comp (continuous_mul_const _)
  -- the patch is connected and one-sided
  set P : Set ℂ := S.inv '' Metric.closedBall c (s ^ 2) with hPdef
  have hPconn : IsPreconnected P := by
    apply IsPreconnected.image (convex_closedBall c (s ^ 2)).isPreconnected
    intro z hz
    have hzim : z ∈ S.T '' annulusSet rlo R₀ := hsurj z (hballband z hz).1 (hballband z hz).2
    exact ((S.inv_analytic z hzim).continuousAt).continuousWithinAt
  have hPsub : P ⊆ {v : ℂ | 0 < Q v} ∪ {v : ℂ | Q v < 0} := by
    rintro v ⟨z, hz, rfl⟩
    have hzim : z ∈ S.T '' annulusSet rlo R₀ := hsurj z (hballband z hz).1 (hballband z hz).2
    have hwann : S.inv z ∈ annulusSet rlo R₀ := S.inv_mem hzim
    have hwT : S.T (S.inv z) = z := S.inv_right hzim
    have hwne : S.inv z ≠ 0 := by
      intro h0
      have h1 := hwann.1
      rw [h0, norm_zero] at h1
      linarith
    have hξ : S.inv z = Complex.exp (Complex.log (S.inv z)) := (Complex.exp_log hwne).symm
    obtain ⟨n, hn⟩ := hkey (S.inv z) hwann (by rw [hwT]; exact hz) _ hξ
    have hQv : Q (S.inv z) = Real.exp (Complex.log (S.inv z)).re
        * Real.cos ((Complex.log (S.inv z)).im - ψ₀) := by
      conv_lhs => rw [hξ]
      exact hQexp _
    rcases Int.even_or_odd n with he | ho
    · left
      show 0 < Q (S.inv z)
      rw [hQv]
      exact mul_pos (Real.exp_pos _) ((hside_of _ n hn).1 he)
    · right
      show Q (S.inv z) < 0
      rw [hQv]
      have h1 := (hside_of _ n hn).2 ho
      nlinarith [Real.exp_pos (Complex.log (S.inv z)).re]
  have hUpo : IsOpen {v : ℂ | 0 < Q v} := isOpen_lt continuous_const hQcont
  have hUmo : IsOpen {v : ℂ | Q v < 0} := isOpen_lt hQcont continuous_const
  have hdisj : Disjoint {v : ℂ | 0 < Q v} {v : ℂ | Q v < 0} := by
    rw [Set.disjoint_left]
    intro v h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    linarith
  -- the shared window argument
  have hwindow : ∀ θs : ℝ,
      (∀ v ∈ annulusSet rlo R₀, S.T v ∈ Metric.closedBall c (s ^ 2) →
        ∀ ξ : ℂ, v = Complex.exp ξ →
        ∃ k : ℤ, |ξ.im - (θs + (k:ℝ) * (2 * Real.pi))| ≤ 1/100) →
      ∀ ra RW : ℝ, rlo < ra → ra < RW → RW < R₀ →
      ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
        S.T v ∉ Metric.closedBall c (s ^ 2) := by
    intro θs hlat ra RW hra hraRW hRW v hv hball
    have hvann : v ∈ annulusSet rlo R₀ := by
      have h1 := arcAnnulus_subset (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8)
        (by linarith : (0:ℝ) < ra) hraRW hv
      exact ⟨lt_trans hra h1.1, lt_trans h1.2 hRW⟩
    obtain ⟨ξ, hξbox, hξexp⟩ := hv
    obtain ⟨k, hk⟩ := hlat v hvann hball ξ hξexp.symm
    have him1 : θs + Real.pi / 8 < ξ.im := hξbox.2.2.1
    have him2 : ξ.im < θs + 2 * Real.pi - Real.pi / 8 := hξbox.2.2.2
    have habs := abs_le.mp hk
    rcases le_or_gt k 0 with hk0 | hk0
    · have hk0' : (k:ℝ) ≤ 0 := by exact_mod_cast hk0
      have h2πk : (k:ℝ) * (2 * Real.pi) ≤ 0 := by nlinarith
      linarith [habs.2]
    · have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk0
      have h2πk : 2 * Real.pi ≤ (k:ℝ) * (2 * Real.pi) := by nlinarith
      linarith [habs.1]
  -- the dichotomy chooses the slit center
  rcases hPconn.subset_or_subset hUpo hUmo hdisj hPsub with hPpos | hPneg
  · -- even side: the true wedge is at `ψ₀`
    refine ⟨ψ₀, by linarith, by linarith, hwindow ψ₀ ?_⟩
    intro v hv hball ξ hξ
    obtain ⟨n, hn⟩ := hkey v hv hball ξ hξ
    have hvP : v ∈ P := ⟨S.T v, hball, S.inv_left hv⟩
    have hQpos : 0 < Q v := hPpos hvP
    have hcospos : 0 < Real.cos (ξ.im - ψ₀) := by
      rw [hξ, hQexp ξ] at hQpos
      nlinarith [Real.exp_pos ξ.re]
    have heven : Even n := by
      rcases Int.even_or_odd n with he | ho
      · exact he
      · exfalso
        have := (hside_of ξ.im n hn).2 ho
        linarith
    obtain ⟨j, hj⟩ := heven
    refine ⟨j, ?_⟩
    have h1 : ψ₀ + Real.pi * n = ψ₀ + (j:ℝ) * (2 * Real.pi) := by
      rw [hj]
      push_cast
      ring
    rw [← h1]
    exact hn
  · -- odd side: the true wedge is at `ψ₀ ± π`
    have hodd_lattice : ∀ (θs : ℝ) (j₀ : ℤ), θs = ψ₀ + Real.pi + (j₀:ℝ) * (2 * Real.pi) →
        ∀ v ∈ annulusSet rlo R₀, S.T v ∈ Metric.closedBall c (s ^ 2) →
        ∀ ξ : ℂ, v = Complex.exp ξ →
        ∃ k : ℤ, |ξ.im - (θs + (k:ℝ) * (2 * Real.pi))| ≤ 1/100 := by
      intro θs j₀ hθeq v hv hball ξ hξ
      obtain ⟨n, hn⟩ := hkey v hv hball ξ hξ
      have hvP : v ∈ P := ⟨S.T v, hball, S.inv_left hv⟩
      have hQneg : Q v < 0 := hPneg hvP
      have hcosneg : Real.cos (ξ.im - ψ₀) < 0 := by
        rw [hξ, hQexp ξ] at hQneg
        nlinarith [Real.exp_pos ξ.re]
      have hodd : Odd n := by
        rcases Int.even_or_odd n with he | ho
        · exfalso
          have := (hside_of ξ.im n hn).1 he
          linarith
        · exact ho
      obtain ⟨j, hj⟩ := hodd
      refine ⟨j - j₀, ?_⟩
      have h1 : ψ₀ + Real.pi * n = θs + ((j - j₀ : ℤ):ℝ) * (2 * Real.pi) := by
        rw [hj, hθeq]
        push_cast
        ring
      rw [← h1]
      exact hn
    rcases le_or_gt ψ₀ 0 with hψ0 | hψ0
    · refine ⟨ψ₀ + Real.pi, by linarith, by linarith,
        hwindow (ψ₀ + Real.pi) (hodd_lattice (ψ₀ + Real.pi) 0 (by push_cast; ring))⟩
    · refine ⟨ψ₀ - Real.pi, by linarith, by linarith,
        hwindow (ψ₀ - Real.pi) (hodd_lattice (ψ₀ - Real.pi) (-1) (by push_cast; ring))⟩

end Bottcher
