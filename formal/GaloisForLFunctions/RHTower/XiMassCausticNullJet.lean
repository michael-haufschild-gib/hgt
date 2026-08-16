import GaloisForLFunctions.RHTower.XiMassTimelikeIdentityWall

/-!
# The caustic-null jet

The exterior stationary point at the balance slope has dispersion `Ω_B = 2a√(a²−1/4) = 2a²/κ_B`,
a strictly positive real number.  The associated jet multiplier

`P_N(w) = (w² + Ω_B²)^{2N}`

vanishes to order `2N` at the caustic frequency `iΩ_B` while remaining nonzero at every point of
the open right half plane.  Two consequences are recorded here.

*Source safety.*  The mass-shifted spectral points all lie in the open right half plane, so no
spectral coefficient is destroyed: `P_N` cannot be used to hide a zero.

*Dispersion normal form.*  Along the Bessel dispersion relation `ω(x)² = x² + a²` the jet is the
real polynomial `(x² + 4a⁴)^{2N}`, because `a² + Ω_B² = 4a⁴`.  This polynomial has no real root, so
the modified profile is a genuine polynomial modification of the receiver on every horizontal
contour, of degree exactly `4N`.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## The caustic frequency -/

/-- The caustic frequency `Ω_B = 2a√(a²−1/4)`, the exterior stationary dispersion at the
balance slope. -/
def xiMassCausticFrequency (a : ℝ) : ℝ := 2 * a * Real.sqrt (a ^ 2 - 1 / 4)

theorem xiMassCausticFrequency_pos {a : ℝ} (ha : 1 / 2 < a) : 0 < xiMassCausticFrequency a := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hpos : (0 : ℝ) < a ^ 2 - 1 / 4 := by nlinarith
  exact mul_pos (by positivity) (Real.sqrt_pos.2 hpos)

/-- `Ω_B² = 4a⁴ − a²`. -/
theorem xiMassCausticFrequency_sq {a : ℝ} (ha : 1 / 2 < a) :
    xiMassCausticFrequency a ^ 2 = 4 * a ^ 4 - a ^ 2 := by
  have hpos : (0 : ℝ) < a ^ 2 - 1 / 4 := by nlinarith
  have hs : Real.sqrt (a ^ 2 - 1 / 4) ^ 2 = a ^ 2 - 1 / 4 := Real.sq_sqrt hpos.le
  rw [xiMassCausticFrequency, mul_pow, mul_pow, hs]
  ring

/-- **(22.1) The caustic frequency is the balance-slope stationary dispersion.** -/
theorem xiMassCausticFrequency_eq_saddleDispersion {a : ℝ} (ha : 1 / 2 < a) :
    xiMassCausticFrequency a
      = xiMassSpacelikeSaddleDispersion a (xiMassSpacelikeSharpSlope a) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkpos : (0 : ℝ) < xiMassSpacelikeSharpSlope a := sharpSlope_pos ha
  rw [xiMassSpacelikeSaddleDispersion_sharpSlope ha, xiMassSpacelikeSharpSlope,
    xiMassCausticFrequency]
  have hpos : (0 : ℝ) < a ^ 2 - 1 / 4 := by nlinarith
  have hne : Real.sqrt (a ^ 2 - 1 / 4) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  field_simp

/-! ## The jet multiplier -/

/-- The caustic-null jet multiplier `P_N(w) = (w² + Ω_B²)^{2N}`. -/
def xiMassCausticJet (a : ℝ) (N : ℕ) (w : ℂ) : ℂ :=
  (w ^ 2 + ((xiMassCausticFrequency a : ℝ) : ℂ) ^ 2) ^ (2 * N)

/-- **(22.2) The jet vanishes to order `2N` at the caustic frequency.** -/
theorem xiMassCausticJet_caustic {a : ℝ} (N : ℕ) (hN : 0 < N) :
    xiMassCausticJet a N (Complex.I * ((xiMassCausticFrequency a : ℝ) : ℂ)) = 0 := by
  rw [xiMassCausticJet]
  have hbase : (Complex.I * ((xiMassCausticFrequency a : ℝ) : ℂ)) ^ 2
      + ((xiMassCausticFrequency a : ℝ) : ℂ) ^ 2 = 0 := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hbase, zero_pow (by omega)]

/-- The only zeros of `w ↦ w² + Ω_B²` are purely imaginary. -/
theorem re_eq_zero_of_sq_add_causticFrequency_sq {a : ℝ} (ha : 1 / 2 < a) {w : ℂ}
    (hw : w ^ 2 + ((xiMassCausticFrequency a : ℝ) : ℂ) ^ 2 = 0) : w.re = 0 := by
  have hOm : (0 : ℝ) < xiMassCausticFrequency a := xiMassCausticFrequency_pos ha
  have hre : w.re ^ 2 - w.im ^ 2 + xiMassCausticFrequency a ^ 2 = 0 := by
    have := congrArg Complex.re hw
    simpa [Complex.add_re, Complex.ofReal_pow, pow_two, Complex.mul_re] using this
  have him : 2 * (w.re * w.im) = 0 := by
    have := congrArg Complex.im hw
    simp only [Complex.add_im, pow_two, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_im] at this
    linarith [this]
  by_contra hne
  have hrepos : 0 < w.re ^ 2 := by positivity
  have him0 : w.im = 0 := by
    rcases mul_eq_zero.1 (by linarith : w.re * w.im = 0) with h | h
    · exact absurd h hne
    · exact h
  rw [him0] at hre
  nlinarith [hOm]

/-- **(22.3) The caustic-null jet is source safe.**  Every point of the open right half plane —
in particular every mass-shifted spectral point — has a nonzero jet value, so the jet destroys no
spectral coefficient. -/
theorem xiMassCausticJet_ne_zero {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) {w : ℂ} (hw : 0 < w.re) :
    xiMassCausticJet a N w ≠ 0 := by
  rw [xiMassCausticJet]
  refine pow_ne_zero _ fun hcon => ?_
  have := re_eq_zero_of_sq_add_causticFrequency_sq ha hcon
  rw [this] at hw
  exact lt_irrefl 0 hw

/-- The jet-modified spectral coefficient of a strictly positive mass at a right-half-plane
point is nonzero. -/
theorem xiMassCausticJet_smul_ne_zero {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) {m : ℂ} {w : ℂ}
    (hm : m ≠ 0) (hw : 0 < w.re) : m * xiMassCausticJet a N w * Complex.exp (-w) ≠ 0 :=
  mul_ne_zero (mul_ne_zero hm (xiMassCausticJet_ne_zero ha N hw)) (Complex.exp_ne_zero _)

/-! ## The dispersion normal form -/

/-- **(22.4) The jet is a real polynomial along the Bessel dispersion relation.**
`P_N(√(x²+a²)) = (x² + 4a⁴)^{2N}`, because `a² + Ω_B² = 4a⁴`. -/
theorem xiMassCausticJet_dispersion {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) (x : ℝ) :
    xiMassCausticJet a N ((Real.sqrt (x ^ 2 + a ^ 2) : ℝ) : ℂ)
      = ((x ^ 2 + 4 * a ^ 4 : ℝ) : ℂ) ^ (2 * N) := by
  have hnn : (0 : ℝ) ≤ x ^ 2 + a ^ 2 := by positivity
  have hs : Real.sqrt (x ^ 2 + a ^ 2) ^ 2 = x ^ 2 + a ^ 2 := Real.sq_sqrt hnn
  have hbase : ((Real.sqrt (x ^ 2 + a ^ 2) : ℝ) : ℂ) ^ 2
      + ((xiMassCausticFrequency a : ℝ) : ℂ) ^ 2 = ((x ^ 2 + 4 * a ^ 4 : ℝ) : ℂ) := by
    have hreal : Real.sqrt (x ^ 2 + a ^ 2) ^ 2 + xiMassCausticFrequency a ^ 2
        = x ^ 2 + 4 * a ^ 4 := by
      rw [hs, xiMassCausticFrequency_sq ha]
      ring
    calc ((Real.sqrt (x ^ 2 + a ^ 2) : ℝ) : ℂ) ^ 2 + ((xiMassCausticFrequency a : ℝ) : ℂ) ^ 2
        = ((Real.sqrt (x ^ 2 + a ^ 2) ^ 2 + xiMassCausticFrequency a ^ 2 : ℝ) : ℂ) := by
          push_cast
          ring
      _ = ((x ^ 2 + 4 * a ^ 4 : ℝ) : ℂ) := by rw [hreal]
  rw [xiMassCausticJet, hbase]

/-- The dispersion polynomial has no real root, so the modification never annihilates a legal
horizontal contour. -/
theorem xiMassCausticJet_dispersion_ne_zero {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) (x : ℝ) :
    xiMassCausticJet a N ((Real.sqrt (x ^ 2 + a ^ 2) : ℝ) : ℂ) ≠ 0 := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hpos : (0 : ℝ) < x ^ 2 + 4 * a ^ 4 := by positivity
  rw [xiMassCausticJet_dispersion ha N x]
  exact pow_ne_zero _ (by exact_mod_cast ne_of_gt hpos)

/-- The jet grows at most polynomially of degree `4N` along the dispersion relation. -/
theorem norm_xiMassCausticJet_dispersion_le {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) {x : ℝ}
    (hx : 1 ≤ |x|) :
    ‖xiMassCausticJet a N ((Real.sqrt (x ^ 2 + a ^ 2) : ℝ) : ℂ)‖
      ≤ (1 + 4 * a ^ 4) ^ (2 * N) * |x| ^ (4 * N) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hx0 : (0 : ℝ) < |x| := lt_of_lt_of_le (by norm_num) hx
  have hxsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hstep : x ^ 2 + 4 * a ^ 4 ≤ (1 + 4 * a ^ 4) * |x| ^ 2 := by
    have h1 : (1 : ℝ) ≤ |x| ^ 2 := by nlinarith [hx, abs_nonneg x]
    have h2 : 4 * a ^ 4 * 1 ≤ 4 * a ^ 4 * |x| ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have hexp : (1 + 4 * a ^ 4) * |x| ^ 2 = |x| ^ 2 + 4 * a ^ 4 * |x| ^ 2 := by ring
    rw [hxsq, hexp]
    linarith [h2]
  have hnn : (0 : ℝ) ≤ x ^ 2 + 4 * a ^ 4 := by positivity
  rw [xiMassCausticJet_dispersion ha N x, Complex.norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hnn]
  calc (x ^ 2 + 4 * a ^ 4) ^ (2 * N) ≤ ((1 + 4 * a ^ 4) * |x| ^ 2) ^ (2 * N) :=
        pow_le_pow_left₀ hnn hstep _
    _ = (1 + 4 * a ^ 4) ^ (2 * N) * |x| ^ (4 * N) := by
        rw [mul_pow, ← pow_mul]
        congr 2
        ring

end

end RHTower
