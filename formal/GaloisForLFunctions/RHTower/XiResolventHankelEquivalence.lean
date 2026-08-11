import GaloisForLFunctions.RHTower.XiResolventTowerLowDegreePositivity

/-!
# RH as positive semidefiniteness of the resolvent Hankel matrix, at every single shift

The resolvent-Hankel criterion is completed to an equivalence: for every fixed shift `X ≥ 0`,

`RH  ↔  ∀ N a, 0 ≤ Re (xiResolventHankelForm N a X)`.

The backward direction is the corpus's trace–Hankel converse.  The forward direction is the
Hamburger mechanism: under RH every resolvent coordinate is a strictly positive real (the
spectral points are real and the height gap keeps the shifted squares positive), so every
polynomial trace is a sum of nonnegative reals — with the junk-value convention absorbing any
non-summable polynomial weight.  In particular one single shift already carries the whole
hypothesis, and for `X = x²` with `x > 1/2` the matrix entries are the Euler-ray jets of
`logDeriv xi`: an explicit arithmetic Hankel matrix whose positive semidefiniteness is RH.

The order-two consequence is recorded separately: under RH the resolvent Turán minor is
nonnegative through its variance expansion, every ordered pair contributing a nonnegative
real. -/

open Complex

namespace RHTower

noncomputable section

/-- Under RH every resolvent coordinate is a strictly positive real. -/
theorem exists_pos_ofReal_xiResolventPoint_of_rh (hRH : RiemannHypothesis) {X : ℝ}
    (hX : 0 ≤ X) (q : XiZeroCopy) :
    ∃ v : ℝ, 0 < v ∧ xiResolventPoint X q = (v : ℂ) := by
  obtain ⟨r, hr⟩ := xiSpectralPoint_real_of_rh hRH q
  have hr2 : 2 < r ^ 2 := by
    have h := xiZeroCopy_two_lt_im_sq q
    rw [← xiSpectralPoint_re_eq, hr] at h
    simpa using h
  have hpos : 0 < r ^ 2 + X := by linarith
  refine ⟨(r ^ 2 + X)⁻¹, by positivity, ?_⟩
  rw [xiResolventPoint, hr]
  norm_cast

/-- **Under RH every polynomial resolvent trace is nonnegative**: the Hamburger direction. -/
theorem xiResolventTrace_re_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 0 ≤ X) (p : Polynomial ℝ) :
    0 ≤ (xiResolventTrace X p).re := by
  rw [xiResolventTrace]
  have hterm : ∀ q : XiZeroCopy, ∃ w : ℝ, 0 ≤ w ∧
      xiResolventPoint X q *
        evalRealPolynomial p (xiResolventPoint X q) ^ 2 = (w : ℂ) := by
    intro q
    obtain ⟨v, hv, hveq⟩ := exists_pos_ofReal_xiResolventPoint_of_rh hRH hX q
    refine ⟨v * Polynomial.eval v p ^ 2, by positivity, ?_⟩
    rw [hveq, evalRealPolynomial_ofReal]
    push_cast
    ring
  choose w hw hweq using hterm
  rw [tsum_congr hweq]
  by_cases hsum : Summable (fun q : XiZeroCopy => ((w q : ℝ) : ℂ))
  · rw [Complex.re_tsum hsum]
    exact tsum_nonneg fun q => by simpa using hw q
  · rw [tsum_eq_zero_of_not_summable hsum]
    simp

/-- Under RH every resolvent Hankel form is nonnegative. -/
theorem xiResolventHankelForm_re_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 0 ≤ X) (N : ℕ) (a : ℕ → ℝ) :
    0 ≤ (xiResolventHankelForm N a X).re := by
  rw [← xiResolventTrace_rangeSum hX N a]
  exact xiResolventTrace_re_nonneg_of_riemannHypothesis hRH hX _

/-- **RH ⟺ positive semidefiniteness of the resolvent Hankel matrix at any one shift.**  A
single fixed `X ≥ 0` carries the whole hypothesis; for `X = x²`, `x > 1/2`, the entries are the
Euler-ray jets of `logDeriv xi` — an explicit arithmetic Hankel matrix. -/
theorem riemannHypothesis_iff_forall_xiResolventHankelForm_re_nonneg {X : ℝ} (hX : 0 ≤ X) :
    RiemannHypothesis ↔
      ∀ (N : ℕ) (a : ℕ → ℝ), 0 ≤ (xiResolventHankelForm N a X).re :=
  ⟨fun hRH N a => xiResolventHankelForm_re_nonneg_of_riemannHypothesis hRH hX N a,
    riemannHypothesis_of_forall_xiResolventHankelForm_re_nonneg hX⟩

/-- **Under RH the resolvent Turán minor is nonnegative**: in the variance expansion every
ordered pair contributes a nonnegative real. -/
theorem xiResolventTuranMinor_re_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 0 ≤ X) :
    0 ≤ (xiResolventMoment 0 X * xiResolventMoment 2 X - xiResolventMoment 1 X ^ 2).re := by
  have hhalf : (0 : ℝ) ≤ (2 * (xiResolventMoment 0 X * xiResolventMoment 2 X -
      xiResolventMoment 1 X ^ 2)).re := by
    rw [two_mul_xiResolventTuranMinor_eq_tsum_pair hX]
    have hterm : ∀ z : XiZeroCopy × XiZeroCopy, ∃ w : ℝ, 0 ≤ w ∧
        xiResolventPairTerm X z = (w : ℂ) := by
      intro z
      obtain ⟨v₁, hv₁, hveq₁⟩ := exists_pos_ofReal_xiResolventPoint_of_rh hRH hX z.1
      obtain ⟨v₂, hv₂, hveq₂⟩ := exists_pos_ofReal_xiResolventPoint_of_rh hRH hX z.2
      refine ⟨v₁ * v₂ * (v₁ - v₂) ^ 2, by positivity, ?_⟩
      rw [xiResolventPairTerm, hveq₁, hveq₂]
      push_cast
      ring
    choose w hw hweq using hterm
    rw [tsum_congr hweq]
    by_cases hsum : Summable (fun z : XiZeroCopy × XiZeroCopy => ((w z : ℝ) : ℂ))
    · rw [Complex.re_tsum hsum]
      exact tsum_nonneg fun z => by simpa using hw z
    · rw [tsum_eq_zero_of_not_summable hsum]
      simp
  have hre : (2 * (xiResolventMoment 0 X * xiResolventMoment 2 X -
      xiResolventMoment 1 X ^ 2)).re =
        2 * (xiResolventMoment 0 X * xiResolventMoment 2 X -
          xiResolventMoment 1 X ^ 2).re := by
    simp [Complex.mul_re]
  rw [hre] at hhalf
  linarith

end

end RHTower
