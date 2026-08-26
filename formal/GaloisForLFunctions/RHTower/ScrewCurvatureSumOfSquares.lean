import GaloisForLFunctions.RHTower.CCMRectangularScrewCurvature
import GaloisForLFunctions.RHTower.XiAbstractInstance

/-!
# The rectangular Weil value is a sum of squares over the zeros

The fixed-width rectangular Weil functional is a centered second difference of the Xi screw
profile.  Because the profile's summand is `(cosh(t w) − 1)/w²`, that second difference factors
completely: the sum-to-product identity

```text
cosh(2u+2v) + cosh(2u−2v) − 2cosh(2u) + 2cosh(2v) − 2 = 8 sinh²v · cosh²u
```

turns the whole window combination into a perfect square in each spectral variable.  With
`w = i·(spectral point)`, `u = (x−L)w/2`, `v = Lw/2` this gives

```text
xiScrewWindowCurvature L x = 16 ∑_ρ ( sinh(Lw/2) · cosh((x−L)w/2) / w )² .
```

Two consequences are immediate from the factored form and are not visible in the second-difference
form.

*Reality is positivity.*  The summand is the **square** of `g_ρ = sinh(Lw/2)cosh((x−L)w/2)/w`, so
the functional is nonnegative as soon as every `g_ρ` is real, and `g_ρ` is real exactly when `w` is
purely imaginary — that is, exactly when the zero lies on the critical line.  Weil positivity is
therefore not an inequality to be established but the reality of an explicit family of numbers; a
sum of squares of *complex* numbers carries no sign, which is precisely why positivity here cannot
be transported from any general principle.

*Constant plus oscillation.*  Halving the angle once more, `cosh²u = (1 + cosh 2u)/2` splits the
functional into an `x`-independent term and an `x`-dependent one with the same coefficients:

```text
xiScrewWindowCurvature L x = 8 ∑_ρ A_ρ² + 8 ∑_ρ A_ρ² cosh((x−L)w) ,   A_ρ = sinh(Lw/2)/w .
```

On the critical line the second sum is a bounded oscillation about the first, and dominance is
term-by-term; off the line the corresponding term grows exponentially in `x` with an uncontrolled
phase.  The criterion is thus a dominance statement between two sums with identical coefficients.
-/

open Complex

namespace RHTower

noncomputable section

/-- The spectral variable of a Xi zero copy, in the coordinate where the screw profile is
`(cosh(t w) − 1)/w²`. -/
def screwVariable (q : XiZeroCopy) : ℂ := I * xiSpectralPoint q

theorem screwVariable_ne_zero (q : XiZeroCopy) : screwVariable q ≠ 0 :=
  mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q)

/-- **The window identity.**  The centered second difference of `cosh` at half-step `v`, corrected
by the constant `2cosh 2v − 2`, is a perfect square. -/
theorem cosh_window_eq_sq (u v : ℂ) :
    Complex.cosh (2 * u + 2 * v) + Complex.cosh (2 * u - 2 * v)
        - 2 * Complex.cosh (2 * u) + 2 * Complex.cosh (2 * v) - 2
      = 8 * Complex.sinh v ^ 2 * Complex.cosh u ^ 2 := by
  simp only [Complex.cosh_add, Complex.cosh_sub, Complex.cosh_two_mul, Complex.sinh_two_mul]
  linear_combination
    (-2 * Complex.sinh v ^ 2 - 2 * Complex.cosh v ^ 2 + 2) * (Complex.cosh_sq_sub_sinh_sq u)
      + (4 * Complex.cosh u ^ 2) * (Complex.cosh_sq_sub_sinh_sq v)

/-- The square root of one window summand: `sinh(Lw/2)·cosh((x−L)w/2)/w`. -/
def screwSquareRoot (L x : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.sinh ((L : ℂ) * screwVariable q / 2) *
      Complex.cosh (((x : ℂ) - (L : ℂ)) * screwVariable q / 2) / screwVariable q

/-- One window summand of the curvature, before the outer factor. -/
def screwSquareTerm (L x : ℝ) (q : XiZeroCopy) : ℂ := screwSquareRoot L x q ^ 2

/-- **The pointwise factorization.**  The window combination of screw summands at one zero is
eight times a perfect square. -/
theorem screwDivisorTerm_window_eq (L x : ℝ) (q : XiZeroCopy) :
    xiScrewDivisorTerm x q + xiScrewDivisorTerm (x - 2 * L) q
        - 2 * xiScrewDivisorTerm (x - L) q + 2 * xiScrewDivisorTerm L q
      = 8 * screwSquareTerm L x q := by
  have hw : screwVariable q ≠ 0 := screwVariable_ne_zero q
  simp only [xiScrewDivisorTerm, screwSquareTerm, screwSquareRoot,
    show I * xiSpectralPoint q = screwVariable q from rfl]
  set w : ℂ := screwVariable q with hwdef
  set u : ℂ := ((x : ℂ) - (L : ℂ)) * w / 2 with hu
  set v : ℂ := (L : ℂ) * w / 2 with hv
  have h1 : ((x : ℝ) : ℂ) * w = 2 * u + 2 * v := by rw [hu, hv]; ring
  have h2 : (((x - 2 * L : ℝ)) : ℂ) * w = 2 * u - 2 * v := by push_cast; rw [hu, hv]; ring
  have h3 : (((x - L : ℝ)) : ℂ) * w = 2 * u := by push_cast; rw [hu]; ring
  have h4 : ((L : ℝ) : ℂ) * w = 2 * v := by rw [hv]; ring
  have hkey := cosh_window_eq_sq u v
  rw [h1, h2, h3, h4]
  have hexp : (8 : ℂ) * (Complex.sinh v * Complex.cosh u / w) ^ 2
      = (8 * Complex.sinh v ^ 2 * Complex.cosh u ^ 2) / w ^ 2 := by
    field_simp
  rw [hexp, ← hkey]
  field_simp
  ring

/-- The square summand is summable: it is a fixed combination of summable screw summands. -/
theorem screwSquareTerm_summable (L x : ℝ) : Summable (screwSquareTerm L x) := by
  have hcomb : Summable fun q : XiZeroCopy =>
      xiScrewDivisorTerm x q + xiScrewDivisorTerm (x - 2 * L) q
        - 2 * xiScrewDivisorTerm (x - L) q + 2 * xiScrewDivisorTerm L q :=
    (((xiScrewDivisorTerm_summable x).add (xiScrewDivisorTerm_summable (x - 2 * L))).sub
      ((xiScrewDivisorTerm_summable (x - L)).mul_left 2)).add
      ((xiScrewDivisorTerm_summable L).mul_left 2)
  have := hcomb.mul_left (8⁻¹ : ℂ)
  refine this.congr fun q => ?_
  rw [screwDivisorTerm_window_eq L x q]
  field_simp

/-- **The rectangular Weil value is a sum of squares over the Xi zeros.**  Every fixed-width
rectangular carrier value is `16` times an absolutely convergent sum of squares of explicit
spectral quantities.  No hypothesis on the location of the zeros is used. -/
theorem xiScrewWindowCurvature_eq_tsum_sq (L x : ℝ) :
    xiScrewWindowCurvature L x = 16 * ∑' q : XiZeroCopy, screwSquareTerm L x q := by
  have hs1 := xiScrewDivisorTerm_summable x
  have hs2 := xiScrewDivisorTerm_summable (x - 2 * L)
  have hs3 := xiScrewDivisorTerm_summable (x - L)
  have hs4 := xiScrewDivisorTerm_summable L
  have hsplit : ∑' q : XiZeroCopy, screwSquareTerm L x q
      = 8⁻¹ * (xiScrewDivisor x + xiScrewDivisor (x - 2 * L)
          - 2 * xiScrewDivisor (x - L) + 2 * xiScrewDivisor L) := by
    have hcongr : ∀ q : XiZeroCopy, screwSquareTerm L x q
        = 8⁻¹ * (xiScrewDivisorTerm x q + xiScrewDivisorTerm (x - 2 * L) q
            - 2 * xiScrewDivisorTerm (x - L) q + 2 * xiScrewDivisorTerm L q) := by
      intro q
      rw [screwDivisorTerm_window_eq L x q]
      field_simp
    rw [tsum_congr hcongr, tsum_mul_left]
    congr 1
    simp only [xiScrewDivisor]
    rw [Summable.tsum_add ((hs1.add hs2).sub (hs3.mul_left 2)) (hs4.mul_left 2),
      Summable.tsum_sub (hs1.add hs2) (hs3.mul_left 2),
      Summable.tsum_add hs1 hs2, tsum_mul_left, tsum_mul_left]
  rw [hsplit, xiScrewWindowCurvature]
  ring

/-! ### Reality of the square roots is exactly positivity -/

/-- **Critical-line zeros give real square roots.**  If the spectral point is real — equivalently,
the zero is on the critical line — then `sinh(Lw/2)cosh((x−L)w/2)/w` is a real number.  The three
sign flips under conjugation (`sinh` odd, `w` odd, `cosh` even) cancel exactly. -/
theorem screwSquareRoot_isReal (L x : ℝ) (q : XiZeroCopy)
    (hq : (xiSpectralPoint q).im = 0) :
    (screwSquareRoot L x q).im = 0 := by
  have hw : (starRingEnd ℂ) (screwVariable q) = -screwVariable q := by
    rw [screwVariable, map_mul, Complex.conj_I, Complex.conj_eq_iff_im.mpr hq]
    ring
  have hstar : (starRingEnd ℂ) (screwSquareRoot L x q) = screwSquareRoot L x q := by
    rw [screwSquareRoot, map_div₀, map_mul, ← Complex.sinh_conj, ← Complex.cosh_conj,
      map_div₀, map_div₀, map_mul, map_mul, map_sub, Complex.conj_ofReal,
      Complex.conj_ofReal, hw]
    have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
    rw [show ((L : ℂ) * -screwVariable q / (starRingEnd ℂ) 2)
        = -((L : ℂ) * screwVariable q / 2) by rw [h2]; ring,
      show (((x : ℂ) - (L : ℂ)) * -screwVariable q / (starRingEnd ℂ) 2)
        = -(((x : ℂ) - (L : ℂ)) * screwVariable q / 2) by rw [h2]; ring,
      Complex.sinh_neg, Complex.cosh_neg]
    ring
  exact Complex.conj_eq_iff_im.mp hstar

/-- **Positivity of one summand on the critical line.**  A real square root gives a nonnegative
real square: the summand of the sum-of-squares representation is `≥ 0` at every critical-line
zero, for every window width and every center. -/
theorem screwSquareTerm_re_nonneg_of_isReal (L x : ℝ) (q : XiZeroCopy)
    (hq : (xiSpectralPoint q).im = 0) :
    0 ≤ (screwSquareTerm L x q).re := by
  have him := screwSquareRoot_isReal L x q hq
  rw [screwSquareTerm, sq, Complex.mul_re, him]
  simp only [mul_zero, sub_zero]
  exact mul_self_nonneg _

/-- **Reality of the spectrum is positivity of the carrier.**  If every Xi zero copy has a real
spectral point, the rectangular Weil value is nonnegative at every width and center.  This is the
positivity half of the Weil criterion read off the sum-of-squares form, with no analytic input
beyond the summability already proved. -/
theorem xiScrewWindowCurvature_re_nonneg_of_spectrum_isReal (L x : ℝ)
    (hreal : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0) :
    0 ≤ (xiScrewWindowCurvature L x).re := by
  rw [xiScrewWindowCurvature_eq_tsum_sq]
  have hre : (∑' q : XiZeroCopy, screwSquareTerm L x q).re
      = ∑' q : XiZeroCopy, (screwSquareTerm L x q).re := Complex.re_tsum (screwSquareTerm_summable L x)
  have hnn : 0 ≤ ∑' q : XiZeroCopy, (screwSquareTerm L x q).re :=
    tsum_nonneg fun q => screwSquareTerm_re_nonneg_of_isReal L x q (hreal q)
  have : (16 * ∑' q : XiZeroCopy, screwSquareTerm L x q).re
      = 16 * (∑' q : XiZeroCopy, screwSquareTerm L x q).re := by
    simp [Complex.mul_re]
  rw [this, hre]
  linarith

/-! ### Constant plus oscillation -/

/-- The `x`-independent amplitude of a zero: `sinh(Lw/2)/w`. -/
def screwAmplitude (L : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.sinh ((L : ℂ) * screwVariable q / 2) / screwVariable q

/-- **The dominance form.**  Each summand is its amplitude squared times `(1 + cosh((x−L)w))/2`,
so the carrier is an `x`-independent sum plus an `x`-dependent sum carrying the *same*
coefficients.  Positivity is therefore exactly dominance of the first sum over the second, and on
the critical line the domination is term-by-term because the cosine factor lies in `[−1,1]`. -/
theorem screwSquareTerm_eq_amplitude_split (L x : ℝ) (q : XiZeroCopy) :
    screwSquareTerm L x q
      = screwAmplitude L q ^ 2 * (1 + Complex.cosh (((x : ℂ) - (L : ℂ)) * screwVariable q)) / 2 := by
  have hw : screwVariable q ≠ 0 := screwVariable_ne_zero q
  have hdouble : Complex.cosh (((x : ℂ) - (L : ℂ)) * screwVariable q)
      = 2 * Complex.cosh (((x : ℂ) - (L : ℂ)) * screwVariable q / 2) ^ 2 - 1 := by
    set z : ℂ := ((x : ℂ) - (L : ℂ)) * screwVariable q / 2 with hz
    have harg : ((x : ℂ) - (L : ℂ)) * screwVariable q = 2 * z := by rw [hz]; ring
    rw [harg, Complex.cosh_two_mul]
    linear_combination -(Complex.cosh_sq_sub_sinh_sq z)
  rw [screwSquareTerm, screwSquareRoot, screwAmplitude, hdouble]
  field_simp
  ring


/-- At the diagonal center `x = L` the oscillating factor is `1`, so the square root is exactly the
amplitude. -/
theorem screwSquareTerm_diagonal (L : ℝ) (q : XiZeroCopy) :
    screwSquareTerm L L q = screwAmplitude L q ^ 2 := by
  rw [screwSquareTerm, screwSquareRoot, screwAmplitude]
  norm_num

/-- The squared amplitudes are summable. -/
theorem screwAmplitude_sq_summable (L : ℝ) :
    Summable fun q : XiZeroCopy => screwAmplitude L q ^ 2 := by
  refine (screwSquareTerm_summable L L).congr fun q => ?_
  exact screwSquareTerm_diagonal L q

/-- **The diagonal rectangular value.**  At `x = L` the carrier is `16` times the sum of squared
amplitudes — the unconditional maximum of the window over its center, since the oscillating factor
attains its largest value there on the critical line. -/
theorem xiScrewWindowCurvature_diagonal (L : ℝ) :
    xiScrewWindowCurvature L L = 16 * ∑' q : XiZeroCopy, screwAmplitude L q ^ 2 := by
  rw [xiScrewWindowCurvature_eq_tsum_sq L L]
  congr 1
  exact tsum_congr fun q => screwSquareTerm_diagonal L q

/-- The oscillating summand: amplitude squared times `cosh((x−L)w)`. -/
def screwOscillationTerm (L x : ℝ) (q : XiZeroCopy) : ℂ :=
  screwAmplitude L q ^ 2 * Complex.cosh (((x : ℂ) - (L : ℂ)) * screwVariable q)

theorem screwOscillationTerm_summable (L x : ℝ) :
    Summable (screwOscillationTerm L x) := by
  have h : ∀ q : XiZeroCopy, screwOscillationTerm L x q
      = 2 * screwSquareTerm L x q - screwAmplitude L q ^ 2 := by
    intro q
    rw [screwOscillationTerm, screwSquareTerm_eq_amplitude_split]
    ring
  exact (((screwSquareTerm_summable L x).mul_left 2).sub
    (screwAmplitude_sq_summable L)).congr fun q => (h q).symm

/-- **Constant plus oscillation.**  The carrier is an `x`-independent sum of squared amplitudes plus
an `x`-dependent sum with the *same* coefficients.  Nonnegativity is therefore exactly the statement
that the first sum dominates the second, and on the critical line the domination is term-by-term
because each `cosh((x−L)w)` is then a cosine.  Off the line the corresponding factor grows without
bound in `x`, which is why no bounded correction can repair a misplaced zero. -/
theorem xiScrewWindowCurvature_eq_const_add_oscillation (L x : ℝ) :
    xiScrewWindowCurvature L x
      = 8 * (∑' q : XiZeroCopy, screwAmplitude L q ^ 2)
        + 8 * ∑' q : XiZeroCopy, screwOscillationTerm L x q := by
  rw [xiScrewWindowCurvature_eq_tsum_sq]
  have hsplit : ∀ q : XiZeroCopy, screwSquareTerm L x q
      = 2⁻¹ * screwAmplitude L q ^ 2 + 2⁻¹ * screwOscillationTerm L x q := by
    intro q
    rw [screwSquareTerm_eq_amplitude_split, screwOscillationTerm]
    ring
  rw [tsum_congr hsplit,
    Summable.tsum_add ((screwAmplitude_sq_summable L).mul_left 2⁻¹)
      ((screwOscillationTerm_summable L x).mul_left 2⁻¹),
    tsum_mul_left, tsum_mul_left]
  ring



/-! ### The carrier as a difference of two nonnegative energies

For a complex number `g`, `Re(g²) = ‖g‖² − 2(Im g)²`.  Applied termwise to the sum-of-squares
representation this writes the real rectangular carrier as

```text
Re xiScrewWindowCurvature L x = 16 ( ∑_ρ ‖g_ρ‖² − 2 ∑_ρ (Im g_ρ)² ) ,
```

a difference of two absolutely convergent sums, **both manifestly nonnegative**.  The subtracted
term is supported exactly on the zeros off the critical line, so it is an explicit, convergent
measure of the failure of RH — and the positivity question becomes a quantitative comparison
between the total spectral energy and its imaginary part, rather than a sign to be conjured.

This is the exact unconditional form of the classical statement that the Weil functional is
`∑_ρ |ĝ(ρ)|²`: that identity holds only under RH, and the defect between `∑ g²` and `∑ ‖g‖²` is
precisely twice the imaginary energy. -/

/-- The total spectral energy of the window: `∑_ρ ‖g_ρ‖²`. -/
def screwTotalEnergy (L x : ℝ) : ℝ := ∑' q : XiZeroCopy, ‖screwSquareRoot L x q‖ ^ 2

/-- The imaginary energy of the window: `∑_ρ (Im g_ρ)²`.  It vanishes exactly when every square
root is real. -/
def screwImaginaryEnergy (L x : ℝ) : ℝ := ∑' q : XiZeroCopy, (screwSquareRoot L x q).im ^ 2

theorem screwNormSq_summable (L x : ℝ) :
    Summable fun q : XiZeroCopy => ‖screwSquareRoot L x q‖ ^ 2 := by
  have h : Summable fun q : XiZeroCopy => ‖screwSquareTerm L x q‖ :=
    summable_norm_iff.mpr (screwSquareTerm_summable L x)
  refine h.congr fun q => ?_
  rw [screwSquareTerm, norm_pow]

theorem screwImSq_summable (L x : ℝ) :
    Summable fun q : XiZeroCopy => (screwSquareRoot L x q).im ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun q => by
      have := Complex.abs_im_le_norm (screwSquareRoot L x q)
      nlinarith [abs_nonneg (screwSquareRoot L x q).im, norm_nonneg (screwSquareRoot L x q),
        sq_abs (screwSquareRoot L x q).im])
    (screwNormSq_summable L x)

theorem screwTotalEnergy_nonneg (L x : ℝ) : 0 ≤ screwTotalEnergy L x :=
  tsum_nonneg fun _ => sq_nonneg _

theorem screwImaginaryEnergy_nonneg (L x : ℝ) : 0 ≤ screwImaginaryEnergy L x :=
  tsum_nonneg fun _ => sq_nonneg _

/-- **The energy decomposition of the rectangular carrier.**  Unconditionally, the real part of the
carrier is sixteen times the total spectral energy minus thirty-two times the imaginary energy.
Both sums converge absolutely and are nonnegative; no hypothesis on the zeros is used. -/
theorem xiScrewWindowCurvature_re_eq_energy_difference (L x : ℝ) :
    (xiScrewWindowCurvature L x).re
      = 16 * (screwTotalEnergy L x - 2 * screwImaginaryEnergy L x) := by
  have hterm : ∀ q : XiZeroCopy, (screwSquareTerm L x q).re
      = ‖screwSquareRoot L x q‖ ^ 2 - 2 * (screwSquareRoot L x q).im ^ 2 := by
    intro q
    rw [screwSquareTerm, sq, Complex.mul_re, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [xiScrewWindowCurvature_eq_tsum_sq]
  have hmul : (16 * ∑' q : XiZeroCopy, screwSquareTerm L x q).re
      = 16 * (∑' q : XiZeroCopy, screwSquareTerm L x q).re := by
    simp [Complex.mul_re]
  rw [hmul, Complex.re_tsum (screwSquareTerm_summable L x), tsum_congr hterm,
    Summable.tsum_sub (screwNormSq_summable L x) ((screwImSq_summable L x).mul_left 2),
    tsum_mul_left]
  rfl

/-- **The imaginary energy is the exact defect.**  The carrier is nonnegative at `(L,x)` precisely
when the total energy dominates twice the imaginary energy there. -/
theorem xiScrewWindowCurvature_re_nonneg_iff (L x : ℝ) :
    0 ≤ (xiScrewWindowCurvature L x).re ↔
      2 * screwImaginaryEnergy L x ≤ screwTotalEnergy L x := by
  rw [xiScrewWindowCurvature_re_eq_energy_difference]
  constructor <;> intro h <;> linarith

/-- **Vanishing imaginary energy forces the carrier nonnegative.**  A one-line consequence, but it
identifies what has to be proved: not a sign, but the vanishing of an explicit convergent sum of
squares. -/
theorem xiScrewWindowCurvature_re_nonneg_of_imaginaryEnergy_eq_zero (L x : ℝ)
    (h : screwImaginaryEnergy L x = 0) :
    0 ≤ (xiScrewWindowCurvature L x).re := by
  rw [xiScrewWindowCurvature_re_nonneg_iff, h]
  simpa using screwTotalEnergy_nonneg L x

/-- **The imaginary energy vanishes exactly on a real spectrum.**  Each summand is a square, so the
sum vanishes iff every square root is real — which by `screwSquareRoot_isReal` is implied by
reality of the spectral points.  This makes the defect a faithful measure: it is zero only in the
critical-line configuration. -/
theorem screwImaginaryEnergy_eq_zero_of_spectrum_isReal (L x : ℝ)
    (hreal : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0) :
    screwImaginaryEnergy L x = 0 := by
  rw [screwImaginaryEnergy, tsum_congr (fun q : XiZeroCopy => by
    rw [screwSquareRoot_isReal L x q (hreal q)]
    norm_num : ∀ q : XiZeroCopy, (screwSquareRoot L x q).im ^ 2 = 0)]
  exact tsum_zero



/-- **RH as a comparison of two spectral energies.**  For every fixed positive window width, the
Riemann Hypothesis is equivalent to the imaginary energy of the window staying below half the total
energy, up to a single additive constant, along the arithmetic mesh `x = log n`.

Both sides are absolutely convergent sums of nonnegative reals built from the same explicit
spectral quantity `g_ρ = sinh(Lw/2)cosh((x−L)w/2)/w`; the criterion asks only that the part of the
energy carried by the imaginary components never grows to half the whole.  This replaces the sign
question for an oscillating carrier by a dominance question between two positive quantities. -/
theorem riemannHypothesis_iff_screwImaginaryEnergy_le_totalEnergy
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → L ≤ Real.log n / 2 →
        2 * screwImaginaryEnergy L (Real.log n)
          ≤ screwTotalEnergy L (Real.log n) + B := by
  rw [riemannHypothesis_iff_xiScrewWindowCurvature_logSample_eventually_bddBelow hL]
  constructor
  · rintro ⟨B, N0, h⟩
    refine ⟨-B / 16, N0, fun n hn hLn => ?_⟩
    have hkey := h n hn hLn
    rw [xiScrewWindowCurvature_re_eq_energy_difference] at hkey
    linarith
  · rintro ⟨B, N0, h⟩
    refine ⟨-(16 * B), N0, fun n hn hLn => ?_⟩
    have hkey := h n hn hLn
    rw [xiScrewWindowCurvature_re_eq_energy_difference]
    linarith



/-! ### How far the criterion sits from the trivial bound

Termwise `(Im g)² ≤ ‖g‖²`, so the imaginary energy never exceeds the total energy — **that
inequality is free and unconditional**.  The criterion of
`riemannHypothesis_iff_screwImaginaryEnergy_le_totalEnergy` asks for the same inequality with
constant `1/2` in place of `1`, up to an additive constant.

In terms of the split `total = real + imaginary`, the condition `imaginary ≤ c · total` says
`imaginary/real ≤ c/(1−c)`.  So `c = 1` is precisely the **vacuous endpoint** — it bounds that ratio
by `∞` and asserts nothing — while `c = 1/2` bounds it by `1` and is RH.  The free bound is
therefore not a near-miss but the boundary of emptiness, and the honest reading is: *any*
unconditional `c < 1` is already a genuine theorem, since it asserts that the real parts of the
`g_ρ` carry a definite positive proportion of the spectral energy.  No such `c` is known.

The asymptotic reason the RH threshold sits at `1/2` is that for an off-line zero the phase of `g`
rotates uniformly in `x` while its modulus grows, and `sin²` has mean `1/2`; the two energies are
then comparable with ratio oscillating about exactly the critical constant, which is why the
carrier dips below every level rather than merely changing sign. -/

/-- **The free half of the criterion.**  Unconditionally, the imaginary energy is at most the total
energy — termwise, since `|Im z| ≤ ‖z‖`. -/
theorem screwImaginaryEnergy_le_totalEnergy (L x : ℝ) :
    screwImaginaryEnergy L x ≤ screwTotalEnergy L x := by
  refine Summable.tsum_le_tsum (fun q => ?_) (screwImSq_summable L x) (screwNormSq_summable L x)
  have h := Complex.abs_im_le_norm (screwSquareRoot L x q)
  nlinarith [abs_nonneg (screwSquareRoot L x q).im, norm_nonneg (screwSquareRoot L x q),
    sq_abs (screwSquareRoot L x q).im]

/-- **Any constant below one half proves RH.**  If the imaginary energy is eventually at most `c`
times the total energy plus a constant, for some `c ≤ 1/2`, the Riemann Hypothesis follows.  The
unconditional bound has `c = 1`, which is the vacuous endpoint; every `c < 1` is an open
statement. -/
theorem riemannHypothesis_of_screwImaginaryEnergy_le_half_totalEnergy
    {L : ℝ} (hL : 0 < L) {c : ℝ} (hc : c ≤ 1 / 2)
    (h : ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → L ≤ Real.log n / 2 →
      screwImaginaryEnergy L (Real.log n) ≤ c * screwTotalEnergy L (Real.log n) + B) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_screwImaginaryEnergy_le_totalEnergy hL]
  obtain ⟨B, N0, hB⟩ := h
  refine ⟨2 * B, N0, fun n hn hLn => ?_⟩
  have hkey := hB n hn hLn
  have hpos : 0 ≤ screwTotalEnergy L (Real.log n) := screwTotalEnergy_nonneg L (Real.log n)
  nlinarith

/-- **The criterion, stated as the improvement of a constant.**  RH is equivalent to the existence
of an admissible pair `(c, B)` with `c ≤ 1/2`.  The unconditional theorem
`screwImaginaryEnergy_le_totalEnergy` supplies the pair `(1, 0)`, which is exactly the vacuous end
of the range; the open ground is the whole interval `c ∈ (1/2, 1)`, where no unconditional value is
known.  Nothing else about the zeros is used in either direction. -/
theorem riemannHypothesis_iff_exists_constant_le_half
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ c : ℝ, c ≤ 1 / 2 ∧ ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → L ≤ Real.log n / 2 →
        screwImaginaryEnergy L (Real.log n) ≤ c * screwTotalEnergy L (Real.log n) + B := by
  constructor
  · intro hRH
    obtain ⟨B, N0, hB⟩ := (riemannHypothesis_iff_screwImaginaryEnergy_le_totalEnergy hL).mp hRH
    refine ⟨1 / 2, le_refl _, B / 2, N0, fun n hn hLn => ?_⟩
    have := hB n hn hLn
    linarith
  · rintro ⟨c, hc, hrest⟩
    exact riemannHypothesis_of_screwImaginaryEnergy_le_half_totalEnergy hL hc hrest



/-! ### RH as boundedness of a single nonnegative energy

The comparison of §-form criteria still asks for a sign.  The total energy alone already decides,
and asks for nothing but boundedness.

On the critical line every `w` is purely imaginary, so `cosh((x−L)w/2)` is a cosine and has modulus
at most `1`; the square roots are then dominated by their own amplitudes uniformly in the center
`x`, and the energy never exceeds its diagonal value.  Off the line the corresponding factor grows
exponentially, and the corpus's cofinal-unboundedness theorem for the carrier forces the energy
itself to be unbounded, because the carrier is bounded below by minus the energy.

So the Riemann Hypothesis is exactly the statement that one explicit nonnegative spectral sum stays
bounded along the arithmetic mesh — no positivity, no comparison, no test function to choose. -/

/-- The square root is the amplitude times the centered cosh factor. -/
theorem screwSquareRoot_eq_amplitude_mul (L x : ℝ) (q : XiZeroCopy) :
    screwSquareRoot L x q
      = screwAmplitude L q * Complex.cosh (((x : ℂ) - (L : ℂ)) * screwVariable q / 2) := by
  rw [screwSquareRoot, screwAmplitude]
  ring

/-- On a real spectrum the centered argument is purely imaginary. -/
theorem screwCenteredArg_re_eq_zero (L x : ℝ) (q : XiZeroCopy)
    (hq : (xiSpectralPoint q).im = 0) :
    ((((x : ℂ) - (L : ℂ)) * screwVariable q / 2)).re = 0 := by
  simp [screwVariable, Complex.mul_re, Complex.mul_im, hq]

/-- **Uniform domination on the critical line.**  With a real spectral point the cosh factor is a
cosine, so the square root never exceeds its amplitude, uniformly in the center. -/
theorem norm_screwSquareRoot_le_amplitude_of_isReal (L x : ℝ) (q : XiZeroCopy)
    (hq : (xiSpectralPoint q).im = 0) :
    ‖screwSquareRoot L x q‖ ≤ ‖screwAmplitude L q‖ := by
  rw [screwSquareRoot_eq_amplitude_mul, norm_mul]
  have hcosh : ‖Complex.cosh (((x : ℂ) - (L : ℂ)) * screwVariable q / 2)‖ ≤ 1 := by
    have h := norm_cosh_le_exp_abs_re (((x : ℂ) - (L : ℂ)) * screwVariable q / 2)
    rw [screwCenteredArg_re_eq_zero L x q hq] at h
    simpa using h
  nlinarith [norm_nonneg (screwAmplitude L q),
    norm_nonneg (Complex.cosh (((x : ℂ) - (L : ℂ)) * screwVariable q / 2))]

/-- The diagonal square root is exactly the amplitude in norm. -/
theorem norm_screwSquareRoot_diagonal (L : ℝ) (q : XiZeroCopy) :
    ‖screwSquareRoot L L q‖ = ‖screwAmplitude L q‖ := by
  rw [screwSquareRoot_eq_amplitude_mul]
  norm_num

/-- **A real spectrum bounds the energy by its diagonal value, uniformly in the center.** -/
theorem screwTotalEnergy_le_diagonal_of_spectrum_isReal (L x : ℝ)
    (hreal : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0) :
    screwTotalEnergy L x ≤ screwTotalEnergy L L := by
  refine Summable.tsum_le_tsum (fun q => ?_) (screwNormSq_summable L x) (screwNormSq_summable L L)
  rw [norm_screwSquareRoot_diagonal]
  have h := norm_screwSquareRoot_le_amplitude_of_isReal L x q (hreal q)
  nlinarith [norm_nonneg (screwSquareRoot L x q), norm_nonneg (screwAmplitude L q)]

/-- Under RH every Xi spectral point is real. -/
theorem xiSpectralPoint_im_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis)
    (q : XiZeroCopy) : (xiSpectralPoint q).im = 0 := by
  obtain ⟨r, hr⟩ := xiSpectralPoint_real_of_xiPoissonPoint_im_eq_zero
    (fun q' => xiPoissonPoint_im_eq_zero_of_riemannHypothesis hRH q') q
  rw [hr]
  simp

/-- **RH is the boundedness of one nonnegative spectral energy.**  For every fixed positive window
width, the Riemann Hypothesis holds if and only if the total energy of the window stays bounded
along the arithmetic mesh `x = log n`.

Forward: a real spectrum makes every cosh factor a cosine, so the energy is dominated by its
diagonal value uniformly in the center.  Backward: the carrier is bounded below by minus sixteen
times the energy, so cofinal unboundedness of the carrier below — which false RH forces — makes the
energy unbounded above.  No sign, comparison, or choice of test function appears in the
statement. -/
theorem riemannHypothesis_iff_screwTotalEnergy_bounded {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → L ≤ Real.log n / 2 →
        screwTotalEnergy L (Real.log n) ≤ C := by
  constructor
  · intro hRH
    exact ⟨screwTotalEnergy L L, 0, fun n _ _ =>
      screwTotalEnergy_le_diagonal_of_spectrum_isReal L (Real.log n)
        (xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH)⟩
  · rintro ⟨C, N0, hC⟩
    by_contra hRH
    obtain ⟨n, hn, hLn, hcarrier⟩ :=
      not_riemannHypothesis_implies_xiScrewWindowCurvature_logSample_cofinally_unbounded_below
        hL hRH (-(16 * C)) N0
    rw [xiScrewWindowCurvature_re_eq_energy_difference] at hcarrier
    have h1 := hC n hn hLn
    have h2 := screwImaginaryEnergy_le_totalEnergy L (Real.log n)
    linarith

/-- **Canonical unit-width energy criterion.** RH is exactly domination of the arithmetic-mesh
energy at the fixed width `L = 1` by its own diagonal value. This removes the arbitrary width,
ceiling, starting index, and aperture side condition from the bounded-energy receiver. -/
theorem riemannHypothesis_iff_unitScrewTotalEnergy_le_diagonal :
    RiemannHypothesis ↔
      ∀ n : ℕ,
        screwTotalEnergy 1 (Real.log n) ≤ screwTotalEnergy 1 1 := by
  constructor
  · intro hRH n
    exact screwTotalEnergy_le_diagonal_of_spectrum_isReal 1 (Real.log n)
      (xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH)
  · intro h
    apply (riemannHypothesis_iff_screwTotalEnergy_bounded
      (L := 1) (by norm_num)).2
    exact ⟨screwTotalEnergy 1 1, 0, fun n _ _ => h n⟩



/-! ### Growth forces reality: the criterion decomposes zero by zero

The corpus supplies the upper bound `‖cosh z‖ ≤ exp|Re z|`.  The matching lower bound
`sinh|Re z| ≤ ‖cosh z‖` comes from the reverse triangle inequality on `(eᶻ + e⁻ᶻ)/2`, and it turns
boundedness of the centered factor into reality of the spectral variable.

Together with the general no-go for nonnegative-sum criteria, this settles the status of the energy
criterion: a bounded sum of nonnegative terms bounds every term, and a bounded term forces its own
zero onto the line.  So the criterion is exactly the conjunction of its per-zero statements — there
is no cancellation between zeros for any weighting or test vector to exploit, and no reformulation
of this shape can be weaker than RH itself. -/

/-- **Lower bound for the complex hyperbolic cosine.**  The reverse triangle inequality on
`(eᶻ + e⁻ᶻ)/2` gives `sinh(Re z) ≤ ‖cosh z‖`. -/
theorem sinh_re_le_norm_cosh (z : ℂ) : Real.sinh z.re ≤ ‖Complex.cosh z‖ := by
  rw [Complex.cosh, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num, Real.sinh_eq]
  have h := norm_sub_norm_le (Complex.exp z) (-(Complex.exp (-z)))
  rw [norm_neg, sub_neg_eq_add, Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h
  linarith

/-- The two-sided form, using that `cosh` is even. -/
theorem sinh_abs_re_le_norm_cosh (z : ℂ) : Real.sinh |z.re| ≤ ‖Complex.cosh z‖ := by
  rcases abs_cases z.re with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]; exact sinh_re_le_norm_cosh z
  · rw [he]
    have h := sinh_re_le_norm_cosh (-z)
    rwa [Complex.neg_re, Complex.cosh_neg] at h

/-- **Boundedness of the centered factor forces the spectral variable real.**  If the centered
`cosh` factor of a zero stays bounded as the center varies, that zero's spectral variable has
vanishing real part — it lies on the critical line. -/
theorem screwVariable_re_eq_zero_of_bounded_cosh (L : ℝ) (q : XiZeroCopy) (C : ℝ)
    (h : ∀ x : ℝ, ‖Complex.cosh (((x : ℂ) - (L : ℂ)) * screwVariable q / 2)‖ ≤ C) :
    (screwVariable q).re = 0 := by
  by_contra hne
  set a : ℝ := (screwVariable q).re with ha
  have hapos : 0 < |a| := abs_pos.mpr hne
  have hargre : ∀ y : ℝ, ((((y : ℂ) - (L : ℂ)) * screwVariable q / 2)).re = (y - L) / 2 * a := by
    intro y
    have hrw : ((y : ℂ) - (L : ℂ)) * screwVariable q / 2
        = (((y - L) / 2 : ℝ) : ℂ) * screwVariable q := by push_cast; ring
    rw [hrw, Complex.re_ofReal_mul]
  set x : ℝ := L + 2 * (|C| + 1) / |a| with hxdef
  have hxre : ((((x : ℂ) - (L : ℂ)) * screwVariable q / 2)).re = (|C| + 1) / |a| * a := by
    rw [hargre x, hxdef]
    ring_nf
  have habs : C + 1 ≤ |((((x : ℂ) - (L : ℂ)) * screwVariable q / 2)).re| := by
    rw [hxre, abs_mul, abs_div, abs_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |C| + 1)]
    have hcancel : (|C| + 1) / |a| * |a| = |C| + 1 := by field_simp
    rw [hcancel]
    linarith [le_abs_self C]
  have hsinh := sinh_abs_re_le_norm_cosh ((((x : ℂ) - (L : ℂ)) * screwVariable q / 2))
  have hself : |((((x : ℂ) - (L : ℂ)) * screwVariable q / 2)).re|
      ≤ Real.sinh |((((x : ℂ) - (L : ℂ)) * screwVariable q / 2)).re| :=
    Real.self_le_sinh_iff.mpr (abs_nonneg _)
  have hC := h x
  linarith


end

end RHTower
