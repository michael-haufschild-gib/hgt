import GaloisForLFunctions.ZeroConfigurationGeometry.TheCameraAndTheTilt
import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerCoefficients
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanCalibration

/-!
# Ramanujan is reality of an Euler column

The positive twins of `ζ` (`SelbergClass.PositiveFiniteEuler`) multiply `ζ(s)` by one reciprocal
Euler factor `1 + A p^{−s} + p^{1−2s}` (`localFactor p A`). Its zeros are the arithmetic fakes that
every reality criterion must exclude. In the coordinate `x = p^{−s}` the factor is the real
quadratic `1 + Ax + px²`, and `|x| = p^{−Re s}`.

* **Depth law** (`localFactor_zero_depth`). For a zero `s` of depth `δ = Re s − ½`: if `A² < 4p`
  then `δ = 0`; if `A² ≥ 4p` then `2 cosh(δ log p) √p = |A|`. Hence
  `Re s = ½ ⇔ A² ≤ 4p` (`localFactor_zero_re_eq_half_iff`): the Ramanujan bound `|A| ≤ 2√p` at `p`
  is reality of the column, and beyond it the depth is read from the coefficient.
* **Ramanujan for curves** (`norm_eq_one_iff_tracePoint`, `curveDatum_pure_iff_tracePoints`). The
  same reciprocal quadratic with `p = 1`: a Frobenius point is on the unit circle iff its trace
  point `β + β⁻¹` is real and in `[−2, 2]`. Purity of a curve datum is a position statement about
  its `g` trace points.
* **The column is an off-line lattice** (`localFactor_eulerColumnCoeff_eq_zero_iff`). With
  `A_δ = −2√p cosh(δ log p)` the zero set of the factor is exactly the vertical lattice pair
  `{½ ± δ + 2πik/log p}` (`RHTower.offLineLatticeConfig` with `L = log p`).
* **Hiding below the prime** (`eulerColumn_mimics_onLineLattice`). On windows of aperture
  `≤ log p / 2` the column has the image of the doubled on-line lattice
  (`W_offLineLatticeConfig_eq_onLine`), whatever its depth. Its image differs first at lag
  `log p`, where the lattice carries `2cosh(δ log p) = |A_δ|/√p` (`two_cosh_eq_eulerColumnCoeff`):
  the camera sees the column exactly at its prime, and what it sees there is the Euler coefficient.
* **No bounded aperture is selective** (`no_bounded_aperture_excludes_eulerColumns`). For every
  aperture `a` there is a prime `p` such that every depth `δ ∈ (0, ½]` is realised by the zeros of
  an Euler factor at `p` whose image at aperture `a` is that of an on-line lattice.
-/

open Complex
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 _root_.RHTower SelbergClass.PositiveFiniteEuler

/-! ### The real quadratic -/

/-- **Roots of a real reciprocal quadratic.** A non-real root of `1 + Ax + Px²` has
`P|x|² = 1` and `A² < 4P`; a real root has `A² ≥ 4P` and `P|x|² + 1 = |A||x|`. -/
theorem reciprocalQuadratic_root {P A : ℝ} (hP : 0 < P) {x : ℂ}
    (hx : 1 + (A : ℂ) * x + (P : ℂ) * x ^ 2 = 0) :
    (x.im ≠ 0 → P * Complex.normSq x = 1 ∧ A ^ 2 < 4 * P) ∧
      (x.im = 0 → 4 * P ≤ A ^ 2 ∧ P * ‖x‖ ^ 2 + 1 = |A| * ‖x‖) := by
  have hre := congrArg Complex.re hx
  have him := congrArg Complex.im hx
  simp only [sq, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, Complex.add_im, Complex.one_im,
    zero_add, Complex.zero_re, Complex.zero_im] at hre him
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have hA : A = -2 * P * x.re := by
      have : x.im * (A + 2 * P * x.re) = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hb
      linarith
    have hn : P * Complex.normSq x = 1 := by
      rw [Complex.normSq_apply]; subst hA; nlinarith
    refine ⟨hn, ?_⟩
    have hb2 : 0 < x.im ^ 2 := by positivity
    rw [Complex.normSq_apply] at hn
    have e : 4 * P - A ^ 2 = 4 * P * P * x.im ^ 2 := by
      rw [hA]; linear_combination (-4 * P) * hn
    nlinarith [mul_pos (mul_pos (by positivity : (0 : ℝ) < 4 * P) hP) hb2]
  · rw [hb] at hre
    simp only [mul_zero, sub_zero] at hre
    have hnx : ‖x‖ = |x.re| := by
      rw [← Complex.re_add_im x, hb]; simp
    refine ⟨by nlinarith [sq_nonneg (2 * P * x.re + A)], ?_⟩
    rw [hnx, sq_abs]
    have hpos : 0 < P * x.re ^ 2 + 1 := by positivity
    have : -(A * x.re) = P * x.re ^ 2 + 1 := by linarith
    rw [← abs_mul, abs_of_neg (by linarith : A * x.re < 0)]
    linarith

/-! ### The depth law -/

theorem natCast_cpow_neg {p : ℕ} (hp : p ≠ 0) (s : ℂ) :
    (p : ℂ) ^ (-s) = cexp (-((Real.log p : ℝ) : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp), ← Complex.natCast_log]; ring_nf

theorem norm_natCast_cpow_neg {p : ℕ} (hp : p ≠ 0) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = Real.exp (-(Real.log p * s.re)) := by
  rw [natCast_cpow_neg hp, Complex.norm_exp, neg_mul, Complex.neg_re, Complex.re_ofReal_mul]

/-- **The depth law of an Euler column.** -/
theorem localFactor_zero_depth {p : ℕ} (hp : 1 < p) {A : ℝ} {s : ℂ} (hs : localFactor p A s = 0) :
    (A ^ 2 < 4 * p → s.re = 1 / 2) ∧
      (4 * p ≤ A ^ 2 → 2 * Real.cosh ((s.re - 1 / 2) * Real.log p) * Real.sqrt p = |A|) := by
  have hp0 : p ≠ 0 := by omega
  have hP : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  set x := (p : ℂ) ^ (-s) with hxdef
  have hx : 1 + (A : ℂ) * x + ((p : ℝ) : ℂ) * x ^ 2 = 0 := by
    rw [Complex.ofReal_natCast]; exact hs
  obtain ⟨h1, h2⟩ := reciprocalQuadratic_root hP hx
  set ℓ := Real.log p with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by exact_mod_cast hp)
  have hpexp : (p : ℝ) = Real.exp ℓ := (Real.exp_log hP).symm
  have hnx : ‖x‖ = Real.exp (-(ℓ * s.re)) := norm_natCast_cpow_neg hp0 s
  have hpx : (p : ℝ) * ‖x‖ ^ 2 = Real.exp (ℓ - 2 * (ℓ * s.re)) := by
    rw [hnx, hpexp, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  refine ⟨fun hA => ?_, fun hA => ?_⟩
  · have him : x.im ≠ 0 := fun h => by linarith [(h2 h).1]
    have hn := (h1 him).1
    rw [Complex.normSq_eq_norm_sq, hpx, Real.exp_eq_one_iff] at hn
    have : ℓ * (1 - 2 * s.re) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hℓ0.ne'
    linarith
  · have him : x.im = 0 := by
      by_contra h; linarith [(h1 h).2]
    have key := (h2 him).2
    rw [hpx, hnx] at key
    set y := (s.re - 1 / 2) * ℓ
    have hsq : Real.sqrt p = Real.exp (ℓ / 2) := by rw [Real.exp_half, ← hpexp]
    have e1 : Real.exp y * Real.exp (ℓ / 2) = Real.exp (ℓ * s.re) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-y) * Real.exp (ℓ / 2) =
        Real.exp (ℓ - 2 * (ℓ * s.re)) * Real.exp (ℓ * s.re) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have e3 : Real.exp (-(ℓ * s.re)) * Real.exp (ℓ * s.re) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [Real.cosh_eq, hsq]
    linear_combination e1 + e2 + Real.exp (ℓ * s.re) * key + |A| * e3

/-- **Ramanujan is reality.** A zero of `1 + Ap^{−s} + p^{1−2s}` lies on the critical line iff
`A² ≤ 4p`. -/
theorem localFactor_zero_re_eq_half_iff {p : ℕ} (hp : 1 < p) {A : ℝ} {s : ℂ}
    (hs : localFactor p A s = 0) : s.re = 1 / 2 ↔ A ^ 2 ≤ 4 * p := by
  obtain ⟨h1, h2⟩ := localFactor_zero_depth hp hs
  have hsq : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < p by omega))
  have hsq2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt (by positivity)
  constructor
  · intro hre
    by_contra hA
    push Not at hA
    have h := h2 hA.le
    rw [hre, sub_self, zero_mul, Real.cosh_zero, mul_one] at h
    have : A ^ 2 = 4 * p := by rw [← sq_abs, ← h]; nlinarith
    linarith
  · intro hA
    rcases hA.lt_or_eq with hA | hA
    · exact h1 hA
    · have h := h2 hA.ge
      have habs : |A| = 2 * Real.sqrt p := by
        have : |A| ^ 2 = (2 * Real.sqrt p) ^ 2 := by rw [sq_abs, hA, mul_pow, hsq2]; ring
        exact (pow_left_inj₀ (abs_nonneg A) (by positivity) two_ne_zero).mp this
      rw [habs] at h
      have hc : Real.cosh ((s.re - 1 / 2) * Real.log p) = 1 := by
        have := mul_right_cancel₀ hsq.ne' (h.trans (by ring : 2 * Real.sqrt p = 2 * 1 * Real.sqrt p))
        linarith
      have h0 : (s.re - 1 / 2) * Real.log p = 0 := by
        by_contra hne; exact (Real.one_lt_cosh.mpr hne).ne' hc
      have hℓ : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
      have := (mul_eq_zero.mp h0).resolve_right hℓ
      linarith

/-! ### Ramanujan for a Frobenius point -/

/-- **Ramanujan for a Frobenius point.** A nonzero `β` lies on the unit circle iff its trace point
`β + β⁻¹` is real and lies in `[−2, 2]`: `β` is a root of the reciprocal quadratic
`1 − (β + β⁻¹)x + x²`, the case `p = 1` of the Euler factor. -/
theorem norm_eq_one_iff_tracePoint {β : ℂ} (hβ : β ≠ 0) :
    ‖β‖ = 1 ↔ (β + β⁻¹).im = 0 ∧ |(β + β⁻¹).re| ≤ 2 := by
  constructor
  · intro h
    have hn : Complex.normSq β = 1 := by rw [Complex.normSq_eq_norm_sq, h, one_pow]
    have hinv : β⁻¹ = (starRingEnd ℂ) β := by rw [Complex.inv_def, hn, inv_one, Complex.ofReal_one, mul_one]
    rw [hinv, Complex.add_conj]
    refine ⟨by simp, ?_⟩
    rw [show ((2 * β.re : ℝ) : ℂ).re = 2 * β.re by simp, abs_mul, abs_two]
    have := Complex.abs_re_le_norm β
    rw [h] at this; linarith
  · rintro ⟨him, hre⟩
    set y := β + β⁻¹ with hy
    have hyr : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have hq : 1 + ((-y.re : ℝ) : ℂ) * β + ((1 : ℝ) : ℂ) * β ^ 2 = 0 := by
      rw [Complex.ofReal_neg, Complex.ofReal_one, ← hyr, hy]; field_simp; ring
    obtain ⟨h1, h2⟩ := reciprocalQuadratic_root one_pos hq
    by_cases hb : β.im = 0
    · obtain ⟨-, h⟩ := h2 hb
      rw [abs_neg] at h
      have hn0 : 0 ≤ ‖β‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖β‖ - 1), mul_le_mul_of_nonneg_right hre hn0]
    · have h := (h1 hb).1
      rw [one_mul, Complex.normSq_eq_norm_sq] at h
      nlinarith [norm_nonneg β, sq_nonneg (‖β‖ - 1)]

/-- **A curve datum is pure iff all of its trace points lie in `[−2, 2]`.** -/
theorem curveDatum_pure_iff_tracePoints {ι : Type*} [Fintype ι]
    (D : ArithmeticCastelnuovoSeveri.CurveDatum ι) :
    (∀ i, ‖D.β i‖ = 1) ↔ ∀ i, (D.β i + (D.β i)⁻¹).im = 0 ∧ |(D.β i + (D.β i)⁻¹).re| ≤ 2 := by
  have hne : ∀ i, D.β i ≠ 0 := fun i h => by
    have := D.β_fePerm i
    rw [h, mul_zero] at this
    exact zero_ne_one this
  exact forall_congr' fun i => norm_eq_one_iff_tracePoint (hne i)

/-! ### The column is an off-line lattice -/

/-- The Euler coefficient of the column of depth `δ`: `A_δ = −2√p cosh(δ log p)`. -/
def eulerColumnCoeff (p : ℕ) (δ : ℝ) : ℝ := -(2 * Real.sqrt p * Real.cosh (δ * Real.log p))

/-- The depth signal of the column at its first lag is the normalized Euler coefficient. -/
theorem two_cosh_eq_eulerColumnCoeff {p : ℕ} (hp : 0 < p) (δ : ℝ) :
    2 * Real.cosh (δ * Real.log p) = |eulerColumnCoeff p δ| / Real.sqrt p := by
  have hsq : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp)
  rw [eulerColumnCoeff, abs_neg, abs_of_pos (by positivity)]
  field_simp

/-- Away from the line the column violates the Ramanujan bound. -/
theorem four_mul_lt_eulerColumnCoeff_sq {p : ℕ} (hp : 1 < p) {δ : ℝ} (hδ : δ ≠ 0) :
    4 * (p : ℝ) < eulerColumnCoeff p δ ^ 2 := by
  have hc : 1 < Real.cosh (δ * Real.log p) := Real.one_lt_cosh.mpr
    (mul_ne_zero hδ (Real.log_pos (by exact_mod_cast hp : (1 : ℝ) < p)).ne')
  have hsq2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt (by positivity)
  have hP : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hc2 : 1 < Real.cosh (δ * Real.log p) ^ 2 := by nlinarith
  rw [eulerColumnCoeff, neg_sq, mul_pow, mul_pow, hsq2]
  nlinarith

theorem localFactor_eulerColumnCoeff_eq {p : ℕ} (hp : 1 < p) (δ : ℝ) (s : ℂ) :
    localFactor p (eulerColumnCoeff p δ) s =
      (p : ℂ) * ((p : ℂ) ^ (-s) - (Real.exp (-((1 / 2 + δ) * Real.log p)) : ℝ)) *
        ((p : ℂ) ^ (-s) - (Real.exp (-((1 / 2 - δ) * Real.log p)) : ℝ)) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  set ℓ := Real.log p
  have hpexp : (p : ℝ) = Real.exp ℓ := (Real.exp_log hP).symm
  have hsq : Real.sqrt p = Real.exp (ℓ / 2) := by rw [Real.exp_half, ← hpexp]
  have hprod : (p : ℝ) * (Real.exp (-((1 / 2 + δ) * ℓ)) * Real.exp (-((1 / 2 - δ) * ℓ))) = 1 := by
    rw [hpexp, ← Real.exp_add, ← Real.exp_add]; simp only [Real.exp_eq_one_iff]; ring
  have hsum : (p : ℝ) * (Real.exp (-((1 / 2 + δ) * ℓ)) + Real.exp (-((1 / 2 - δ) * ℓ))) =
      2 * Real.sqrt p * Real.cosh (δ * ℓ) := by
    rw [hsq, Real.cosh_eq, hpexp, mul_add, ← Real.exp_add, ← Real.exp_add]
    rw [show 2 * Real.exp (ℓ / 2) * ((Real.exp (δ * ℓ) + Real.exp (-(δ * ℓ))) / 2) =
      Real.exp (ℓ / 2 + δ * ℓ) + Real.exp (ℓ / 2 + -(δ * ℓ)) by
        rw [Real.exp_add, Real.exp_add]; ring]
    rw [add_comm (Real.exp (ℓ + -((1 / 2 + δ) * ℓ)))]
    congr 2 <;> ring
  have hprodC : ((p : ℝ) : ℂ) * ((Real.exp (-((1 / 2 + δ) * ℓ)) : ℝ) *
      (Real.exp (-((1 / 2 - δ) * ℓ)) : ℝ)) = 1 := by exact_mod_cast hprod
  have hsumC : ((p : ℝ) : ℂ) * ((Real.exp (-((1 / 2 + δ) * ℓ)) : ℝ) +
      (Real.exp (-((1 / 2 - δ) * ℓ)) : ℝ)) = ((2 * Real.sqrt p * Real.cosh (δ * ℓ) : ℝ) : ℂ) := by
    exact_mod_cast hsum
  rw [Complex.ofReal_natCast] at hprodC hsumC
  rw [localFactor, eulerColumnCoeff, Complex.ofReal_neg]
  linear_combination (-1 : ℂ) * hprodC + ((p : ℂ) ^ (-s)) * hsumC

/-- `e^{−ℓs} = e^{−cℓ}` exactly on the vertical progression `c + 2πik/ℓ`. -/
theorem cexp_neg_mul_eq_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (c : ℝ) (s : ℂ) :
    cexp (-(ℓ : ℂ) * s) = cexp ((-(c * ℓ) : ℝ) : ℂ) ↔
      ∃ k : ℤ, s = ⟨c, (k : ℝ) * (2 * π / ℓ)⟩ := by
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have him := congrArg Complex.im hn
    simp at hre him
    refine ⟨-n, Complex.ext ?_ ?_⟩
    · simp only
      have : ℓ * (s.re - c) = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hℓ0
      linarith
    · simp only
      push_cast
      field_simp
      linarith
  · rintro ⟨k, rfl⟩
    refine ⟨-k, Complex.ext ?_ ?_⟩
    · simp; ring
    · simp; field_simp

/-- `p^{−s} = p^{−(½+δ)}` exactly on the vertical progression `½ + δ + 2πik/log p`. -/
theorem natCast_cpow_neg_eq_iff {p : ℕ} (hp : 1 < p) (δ : ℝ) (s : ℂ) :
    (p : ℂ) ^ (-s) = ((Real.exp (-((1 / 2 + δ) * Real.log p)) : ℝ) : ℂ) ↔
      s ∈ Set.range (verticalLatticePoint (Real.log p) δ) := by
  have hp0 : p ≠ 0 := by omega
  rw [natCast_cpow_neg hp0, Complex.ofReal_exp,
    cexp_neg_mul_eq_iff (Real.log_pos (by exact_mod_cast hp)) (1 / 2 + δ) s]
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩

/-- **The Euler column of depth `δ` is the off-line lattice pair of spacing `2π/log p`.** -/
theorem localFactor_eulerColumnCoeff_eq_zero_iff {p : ℕ} (hp : 1 < p) (δ : ℝ) (s : ℂ) :
    localFactor p (eulerColumnCoeff p δ) s = 0 ↔
      s ∈ Set.range (verticalLatticePoint (Real.log p) δ) ∪
        Set.range (verticalLatticePoint (Real.log p) (-δ)) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [localFactor_eulerColumnCoeff_eq hp, Set.mem_union, ← natCast_cpow_neg_eq_iff hp,
    ← natCast_cpow_neg_eq_iff hp, show 1 / 2 + -δ = 1 / 2 - δ by ring]
  simp only [mul_eq_zero, hp0, false_or, sub_eq_zero]

/-! ### Hiding below the prime -/

/-- **An Euler column hides below its prime.** For `0 < δ ≤ ½` the zeros of the factor at `p`
with coefficient `A_δ` form `offLineLatticeConfig` with `L = log p`, and on windows of aperture
`log p / 2` that configuration has the image of the doubled on-line lattice. -/
theorem eulerColumn_mimics_onLineLattice {p : ℕ} (hp : 1 < p) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    let hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
    (offLineLatticeConfig hL hδ hδ').carrier = {s | localFactor p (eulerColumnCoeff p δ) s = 0} ∧
      ∀ f g, ApertureWindow (Real.log p / 2) f → ApertureWindow (Real.log p / 2) g →
        (offLineLatticeConfig hL hδ hδ').W f g = (onLineLatticeConfig hL).W f g := by
  intro hL
  refine ⟨Set.ext fun s => (localFactor_eulerColumnCoeff_eq_zero_iff hp δ s).symm, ?_⟩
  intro f g hf hg
  exact W_offLineLatticeConfig_eq_onLine hL hδ hδ' hf.1 hg.1.continuous hf.2 hg.2

/-- **No bounded aperture excludes Euler columns.** For every aperture `a` there is a prime `p`
such that, for every depth `δ ∈ (0, ½]`, the zeros of an Euler factor at `p` form an off-line
configuration whose image at aperture `a` is that of an on-line lattice. -/
theorem no_bounded_aperture_excludes_eulerColumns (a : ℝ) :
    ∃ p : ℕ, p.Prime ∧ ∃ hL : 0 < Real.log p, ∀ δ (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2),
      (offLineLatticeConfig hL hδ hδ').carrier =
          {s | localFactor p (eulerColumnCoeff p δ) s = 0} ∧
        ∀ f, ApertureWindow a f →
          (offLineLatticeConfig hL hδ hδ').W f f = (onLineLatticeConfig hL).W f f := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (⌈Real.exp (2 * |a|)⌉₊ + 2)
  have hp1 : 1 < p := hp.one_lt
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp1)
  have ha : a ≤ Real.log p / 2 := by
    have h1 : Real.exp (2 * |a|) < p := by
      have := Nat.le_ceil (Real.exp (2 * |a|))
      have : ((⌈Real.exp (2 * |a|)⌉₊ + 2 : ℕ) : ℝ) ≤ p := by exact_mod_cast hpN
      push_cast at this; linarith
    have h2 := Real.log_lt_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    linarith [le_abs_self a]
  refine ⟨p, hp, hL, fun δ hδ hδ' => ⟨(eulerColumn_mimics_onLineLattice hp1 hδ hδ').1, ?_⟩⟩
  intro f hf
  have hf' : ApertureWindow (Real.log p / 2) f :=
    ⟨hf.1, hf.2.trans (Set.Icc_subset_Icc (by linarith) ha)⟩
  exact (eulerColumn_mimics_onLineLattice hp1 hδ hδ').2 f f hf' hf'

end GaloisForLFunctions.ZeroConfigurationGeometry
