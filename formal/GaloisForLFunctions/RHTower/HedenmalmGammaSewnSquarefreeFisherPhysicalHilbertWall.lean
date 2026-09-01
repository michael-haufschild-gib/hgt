import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusTwoSidedApertureWall
import GaloisForLFunctions.RHTower.SquarefreeMoebiusCrossGram
import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherRegularGermCofinal

/-!
# The physical MSC divisor lies beyond the source Hilbert wall

The squarefree-Möbius source column at aperture `u` has squared coefficients equal to squarefree
Dirichlet mass at exponent

`a = sigma + 2 u (sigma - 1)`.

The existing two-sided construction proves square summability for `u > -1/2`.  Prime-subseries
divergence gives the converse, so the open half-plane `Re u > -1/2` is the exact complex Hilbert
domain.

For a fixed spectral point `rho` with `Re rho < 1`, its physical coordinate

`u_sigma = (rho - sigma) / (sigma - 1)`

satisfies `Re u_sigma < -1/2` for every `sigma > 1`.  Therefore the physical source column has no
`ell^2` representative at any finite stage.  This kills ordinary-Hilbert singular-graph landing at
a strict-right Xi divisor.  The algebraic regular germ remains valid, but its continuation must use
a rigged or distributional source completion.
-/

open Complex

namespace RHTower

noncomputable section

/-- Squarefree Dirichlet mass diverges throughout the closed half-plane `a <= 1`.  The prime
subseries already dominates the harmonic prime series. -/
theorem not_summable_squarefreeMobiusMass_of_le_one
    {a : ℝ} (ha : a ≤ 1) :
    ¬ Summable (squarefreeMobiusMass a) := by
  intro hsum
  apply not_summable_squarefreeTransverseWeight_one
  refine Summable.of_nonneg_of_le
    (fun n => squarefreeTransverseWeight_nonneg 1 n) ?_ hsum
  intro n
  rw [squarefreeTransverseWeight]
  split_ifs with hn
  · rw [squarefreeMobiusMass, if_pos hn.1, Real.rpow_one]
    have hnbase : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.1.ne_zero)
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hnbase (neg_le_neg ha)
  · exact squarefreeMobiusMass_nonneg a n

/-- Exact abscissa of squarefree Dirichlet mass. -/
theorem summable_squarefreeMobiusMass_iff {a : ℝ} :
    Summable (squarefreeMobiusMass a) ↔ 1 < a := by
  constructor
  · intro hsum
    by_contra h
    exact not_summable_squarefreeMobiusMass_of_le_one
      (le_of_not_gt h) hsum
  · exact summable_squarefreeMobiusMass

namespace HedenmalmThetaSource

/-- At or beyond the half-density wall, the real damped Möbius source is not square-summable. -/
theorem
    not_summable_norm_sq_infiniteMobiusCriticalDampedSignedWeight_of_le_negHalf
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : u ≤ -(1 / 2 : ℝ)) :
    ¬ Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalDampedSignedWeight sigma u n‖ ^ 2) := by
  intro hsum
  let a := mobiusCriticalBoundaryParameter sigma (2 * u)
  have ha : a ≤ 1 := by
    dsimp only [a, mobiusCriticalBoundaryParameter]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg
      (show 2 * u + 1 ≤ 0 by linarith) (sub_nonneg.mpr hsigma.le)]
  have htotal : squarefreeMobiusTotal sigma ≠ 0 :=
    (squarefreeMobiusTotal_pos hsigma).ne'
  have hscaled := Summable.mul_left (squarefreeMobiusTotal sigma) hsum
  have hmass : Summable (squarefreeMobiusMass a) := by
    apply hscaled.congr
    intro n
    dsimp only [a]
    rw [norm_sq_infiniteMobiusCriticalDampedSignedWeight_eq_boundaryLayer
      hsigma,
      squarefreeMobiusBoundaryLayerTerm_eq]
    field_simp [htotal]
  exact not_summable_squarefreeMobiusMass_of_le_one ha hmass

/-- The real squarefree-Möbius source has maximal Hilbert aperture `u > -1/2`. -/
theorem summable_norm_sq_infiniteMobiusCriticalDampedSignedWeight_iff
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalDampedSignedWeight sigma u n‖ ^ 2) ↔
        -(1 / 2 : ℝ) < u := by
  constructor
  · intro hsum
    by_contra h
    exact
      not_summable_norm_sq_infiniteMobiusCriticalDampedSignedWeight_of_le_negHalf
        hsigma (le_of_not_gt h) hsum
  · exact
      summable_norm_sq_infiniteMobiusCriticalDampedSignedWeight_of_negHalf_lt
        hsigma

/-- Imaginary phase cannot repair loss of square summability at the half-density wall. -/
theorem
    not_summable_norm_sq_infiniteMobiusCriticalComplexDampedSignedWeight_of_re_le_negHalf
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma)
    (hu : u.re ≤ -(1 / 2 : ℝ)) :
    ¬ Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma u n‖ ^ 2) := by
  intro hsum
  apply
    not_summable_norm_sq_infiniteMobiusCriticalDampedSignedWeight_of_le_negHalf
      hsigma hu
  exact hsum.congr (fun n => by
    rw [norm_infiniteMobiusCriticalComplexDampedSignedWeight])

/-- Exact maximal complex Hilbert domain of the phase-damped Möbius source. -/
theorem summable_norm_sq_infiniteMobiusCriticalComplexDampedSignedWeight_iff
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma u n‖ ^ 2) ↔
        -(1 / 2 : ℝ) < u.re := by
  constructor
  · intro hsum
    by_contra h
    exact
      not_summable_norm_sq_infiniteMobiusCriticalComplexDampedSignedWeight_of_re_le_negHalf
        hsigma (le_of_not_gt h) hsum
  · intro hu
    have hsum :=
      summable_norm_sq_infiniteMobiusCriticalDampedSignedWeight_of_negHalf_lt
        hsigma hu
    exact hsum.congr (fun n => by
      rw [norm_infiniteMobiusCriticalComplexDampedSignedWeight])

/-- A fixed point left of `Re = 1` is always strictly beyond the physical half-density wall. -/
theorem mscPhysicalZeroCoordinate_re_lt_negHalf
    {rho : ℂ} (hrho : rho.re < 1) {sigma : ℝ} (hsigma : 1 < sigma) :
    (mscPhysicalZeroCoordinate rho sigma).re < -(1 / 2 : ℝ) := by
  have hden : 0 < sigma - 1 := sub_pos.mpr hsigma
  have hre : (mscPhysicalZeroCoordinate rho sigma).re =
      (rho.re - sigma) / (sigma - 1) := by
    rw [mscPhysicalZeroCoordinate, Complex.div_re]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero, Complex.normSq_apply]
    field_simp [hden.ne']
    ring
  rw [hre, div_lt_iff₀ hden]
  nlinarith

/-- Physical evaluation at any fixed strip point left of one has nonsummable source energy. -/
theorem not_summable_mscPhysicalZeroSourceColumn
    {rho : ℂ} (hrho : rho.re < 1) {sigma : ℝ} (hsigma : 1 < sigma) :
    ¬ Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma
          (mscPhysicalZeroCoordinate rho sigma) n‖ ^ 2) := by
  apply
    not_summable_norm_sq_infiniteMobiusCriticalComplexDampedSignedWeight_of_re_le_negHalf
      hsigma
  exact le_of_lt (mscPhysicalZeroCoordinate_re_lt_negHalf hrho hsigma)

/-- **MSC ordinary-Hilbert graph no-go.**  No `ell^2` source vector carries the exact physical
coefficients of a fixed strip point with `Re rho < 1`. -/
theorem not_exists_lp_mscPhysicalZeroSourceColumn
    {rho : ℂ} (hrho : rho.re < 1) {sigma : ℝ} (hsigma : 1 < sigma) :
    ¬ ∃ w : lp (fun _ : ℕ => ℂ) 2,
        ∀ n,
          w n = infiniteMobiusCriticalComplexDampedSignedWeight sigma
            (mscPhysicalZeroCoordinate rho sigma) n := by
  rintro ⟨w, hw⟩
  apply not_summable_mscPhysicalZeroSourceColumn hrho hsigma
  have hsum := (lp.memℓp w).summable (p := 2) (by norm_num)
  have hcast : ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) := by
    norm_num
  simp only [hcast, Real.rpow_natCast] at hsum
  exact hsum.congr (fun n => by rw [hw n])

end HedenmalmThetaSource

end

end RHTower
