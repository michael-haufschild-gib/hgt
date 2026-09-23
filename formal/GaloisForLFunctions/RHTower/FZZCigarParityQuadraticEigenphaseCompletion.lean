import GaloisForLFunctions.RHTower.FZZCigarParityKreinEigenlineQuadrantSurjectivity

/-!
# Quadratic eigenphase completion of the FZZ parity source

The literal conjugate FZZ source Krein eigenpair is linearly phase-incomplete: its two balanced
coordinates occupy only the left half-circle. Positive physical scale nevertheless fills those
two strict quadrants exactly. This module computes the first nonlinear interaction closure.

Squares of the positive and conjugate eigenlines cover the two open semicircles. Their product and
negative product supply the two real boundary phases. Hence four source-derived quadratic channels
cover the entire unit circle at positive physical scale.

The centered dyadic Mellin character matches one of these channels exactly when its real part is
one half. Consequently quadratic source-phase completeness for all open-strip zeta divisors is
equivalent to RH. This does not assume or prove the missing dynamical landing law; it closes the
phase-capacity burden and shows that interaction degree two is both sufficient for complete
critical phase capacity and still sharply selective.

`[NEW] [NONLINEAR SOURCE COMPLETION] [UNIT-CIRCLE SURJECTIVITY] [EXACT RH ENDPOINT] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Algebraic upper-left square root of a unit phase. -/
def fzzCigarParityUpperLeftUnitSquareRoot (z : ℂ) : ℂ :=
  ⟨-Real.sqrt ((1 + z.re) / 2), Real.sqrt ((1 - z.re) / 2)⟩

theorem norm_fzzCigarParityUpperLeftUnitSquareRoot
    {z : ℂ} (hnorm : ‖z‖ = 1) :
    ‖fzzCigarParityUpperLeftUnitSquareRoot z‖ = 1 := by
  have hnormsq := congrArg (fun x : ℝ => x ^ (2 : ℕ)) hnorm
  rw [Complex.sq_norm, Complex.normSq_apply] at hnormsq
  have hreLower : -1 ≤ z.re := by nlinarith [sq_nonneg z.im]
  have hreUpper : z.re ≤ 1 := by nlinarith [sq_nonneg z.im]
  have hplus : 0 ≤ (1 + z.re) / 2 := by linarith
  have hminus : 0 ≤ (1 - z.re) / 2 := by linarith
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp only [fzzCigarParityUpperLeftUnitSquareRoot, neg_sq]
  rw [Real.sq_sqrt hplus, Real.sq_sqrt hminus]
  ring_nf
  rw [Real.sqrt_one]

theorem fzzCigarParityUpperLeftUnitSquareRoot_re_neg
    {z : ℂ} (hnorm : ‖z‖ = 1) (him : z.im ≠ 0) :
    (fzzCigarParityUpperLeftUnitSquareRoot z).re < 0 := by
  have hnormsq := congrArg (fun x : ℝ => x ^ (2 : ℕ)) hnorm
  rw [Complex.sq_norm, Complex.normSq_apply] at hnormsq
  have himsq : 0 < z.im ^ (2 : ℕ) := sq_pos_of_ne_zero him
  have hplus : 0 < (1 + z.re) / 2 := by nlinarith
  simp only [fzzCigarParityUpperLeftUnitSquareRoot]
  exact neg_neg_of_pos (Real.sqrt_pos.2 hplus)

theorem fzzCigarParityUpperLeftUnitSquareRoot_im_pos
    {z : ℂ} (hnorm : ‖z‖ = 1) (him : z.im ≠ 0) :
    0 < (fzzCigarParityUpperLeftUnitSquareRoot z).im := by
  have hnormsq := congrArg (fun x : ℝ => x ^ (2 : ℕ)) hnorm
  rw [Complex.sq_norm, Complex.normSq_apply] at hnormsq
  have himsq : 0 < z.im ^ (2 : ℕ) := sq_pos_of_ne_zero him
  have hminus : 0 < (1 - z.re) / 2 := by nlinarith
  simp only [fzzCigarParityUpperLeftUnitSquareRoot]
  exact Real.sqrt_pos.2 hminus

/-- Lower-half unit phases are squares of their algebraic upper-left roots. -/
theorem fzzCigarParityUpperLeftUnitSquareRoot_sq_eq_of_im_neg
    {z : ℂ} (hnorm : ‖z‖ = 1) (him : z.im < 0) :
    fzzCigarParityUpperLeftUnitSquareRoot z ^ (2 : ℕ) = z := by
  have hnormsq := congrArg (fun x : ℝ => x ^ (2 : ℕ)) hnorm
  rw [Complex.sq_norm, Complex.normSq_apply] at hnormsq
  have himne : z.im ≠ 0 := ne_of_lt him
  have himsq : 0 < z.im ^ (2 : ℕ) := sq_pos_of_ne_zero himne
  have hplus : 0 < (1 + z.re) / 2 := by nlinarith
  have hminus : 0 < (1 - z.re) / 2 := by nlinarith
  apply Complex.ext
  · simp only [fzzCigarParityUpperLeftUnitSquareRoot, pow_two, mul_re]
    rw [show -Real.sqrt ((1 + z.re) / 2) *
          -Real.sqrt ((1 + z.re) / 2) =
        Real.sqrt ((1 + z.re) / 2) ^ (2 : ℕ) by ring,
      show Real.sqrt ((1 - z.re) / 2) *
          Real.sqrt ((1 - z.re) / 2) =
        Real.sqrt ((1 - z.re) / 2) ^ (2 : ℕ) by ring,
      Real.sq_sqrt hplus.le, Real.sq_sqrt hminus.le]
    ring
  · simp only [fzzCigarParityUpperLeftUnitSquareRoot, pow_two, mul_im]
    have hsquare :
        (-Real.sqrt ((1 + z.re) / 2) * Real.sqrt ((1 - z.re) / 2) +
          Real.sqrt ((1 - z.re) / 2) *
            -Real.sqrt ((1 + z.re) / 2)) ^ (2 : ℕ) = z.im ^ (2 : ℕ) := by
      rw [show
          -Real.sqrt ((1 + z.re) / 2) * Real.sqrt ((1 - z.re) / 2) +
              Real.sqrt ((1 - z.re) / 2) *
                -Real.sqrt ((1 + z.re) / 2) =
            -2 * (Real.sqrt ((1 + z.re) / 2) *
              Real.sqrt ((1 - z.re) / 2)) by ring,
        mul_pow, mul_pow, Real.sq_sqrt hplus.le, Real.sq_sqrt hminus.le]
      nlinarith
    have hleftneg :
        -Real.sqrt ((1 + z.re) / 2) * Real.sqrt ((1 - z.re) / 2) +
            Real.sqrt ((1 - z.re) / 2) *
              -Real.sqrt ((1 + z.re) / 2) < 0 := by
      have hp := Real.sqrt_pos.2 hplus
      have hm := Real.sqrt_pos.2 hminus
      nlinarith [mul_pos hp hm]
    nlinarith

/-- Upper-half unit phases are squares of conjugate algebraic upper-left roots. -/
theorem star_fzzCigarParityUpperLeftUnitSquareRoot_sq_eq_of_im_pos
    {z : ℂ} (hnorm : ‖z‖ = 1) (him : 0 < z.im) :
    star (fzzCigarParityUpperLeftUnitSquareRoot z) ^ (2 : ℕ) = z := by
  have hsq := fzzCigarParityUpperLeftUnitSquareRoot_sq_eq_of_im_neg
    (z := star z) (by simpa using hnorm) (by simpa using him)
  have hroot : fzzCigarParityUpperLeftUnitSquareRoot (star z) =
      fzzCigarParityUpperLeftUnitSquareRoot z := by
    apply Complex.ext <;>
      simp [fzzCigarParityUpperLeftUnitSquareRoot]
  rw [hroot] at hsq
  have hstar := congrArg (starRingEnd ℂ) hsq
  have hzz : (starRingEnd ℂ) (star z) = z := by
    exact star_star z
  rw [map_pow, hzz] at hstar
  change (starRingEnd ℂ) (fzzCigarParityUpperLeftUnitSquareRoot z) ^ (2 : ℕ) = z
  exact hstar

/-- Four quadratic interaction channels of the literal conjugate source eigenpair. -/
inductive FZZCigarParityQuadraticEigenphaseChannel
  | positiveSquare
  | conjugateSquare
  | product
  | negativeProduct
  deriving DecidableEq

/-- Quadratic balanced phase reported by one source interaction channel. -/
def fzzCigarParityQuadraticEigenphase
    (beta : ℝ) : FZZCigarParityQuadraticEigenphaseChannel → ℂ
  | .positiveSquare =>
      fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta ^ (2 : ℕ)
  | .conjugateSquare =>
      star (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) ^ (2 : ℕ)
  | .product =>
      fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta *
        star (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta)
  | .negativeProduct =>
      -(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta *
        star (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta))

theorem fzzCigarParityQuadraticEigenphase_product_eq_one
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityQuadraticEigenphase beta .product = 1 := by
  rw [fzzCigarParityQuadraticEigenphase, Complex.star_def, Complex.mul_conj',
    norm_fzzCigarParityDilatedKreinEigenlineBalancedCoordinate hbeta]
  norm_num

theorem fzzCigarParityQuadraticEigenphase_negativeProduct_eq_neg_one
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityQuadraticEigenphase beta .negativeProduct = -1 := by
  rw [fzzCigarParityQuadraticEigenphase, Complex.star_def, Complex.mul_conj',
    norm_fzzCigarParityDilatedKreinEigenlineBalancedCoordinate hbeta]
  norm_num

/-- **Quadratic phase completeness.** Every unit complex phase is an exact quadratic interaction
phase of the literal source eigenpair at some positive physical scale. -/
theorem exists_pos_fzzCigarParityQuadraticEigenphase_eq_of_norm_one
    {z : ℂ} (hnorm : ‖z‖ = 1) :
    ∃ beta : ℝ, 0 < beta ∧
      ∃ channel : FZZCigarParityQuadraticEigenphaseChannel,
        fzzCigarParityQuadraticEigenphase beta channel = z := by
  rcases lt_trichotomy z.im 0 with himneg | himzero | himpos
  · let w := fzzCigarParityUpperLeftUnitSquareRoot z
    obtain ⟨beta, hbeta, hy⟩ :=
      exists_pos_fzzCigarParityKreinEigenline_eq_of_unit_upperLeft
        (norm_fzzCigarParityUpperLeftUnitSquareRoot hnorm)
        (fzzCigarParityUpperLeftUnitSquareRoot_re_neg hnorm (ne_of_lt himneg))
        (fzzCigarParityUpperLeftUnitSquareRoot_im_pos hnorm (ne_of_lt himneg))
    refine ⟨beta, hbeta, .positiveSquare, ?_⟩
    rw [fzzCigarParityQuadraticEigenphase, hy]
    exact fzzCigarParityUpperLeftUnitSquareRoot_sq_eq_of_im_neg hnorm himneg
  · have hnormsq := congrArg (fun x : ℝ => x ^ (2 : ℕ)) hnorm
    rw [Complex.sq_norm, Complex.normSq_apply, himzero] at hnormsq
    have hreSq : z.re ^ (2 : ℕ) = 1 := by nlinarith
    rcases sq_eq_one_iff.mp hreSq with hre | hre
    · refine ⟨1, by norm_num, .product, ?_⟩
      rw [fzzCigarParityQuadraticEigenphase_product_eq_one (by norm_num)]
      apply Complex.ext
      · simp [hre]
      · simp [himzero]
    · refine ⟨1, by norm_num, .negativeProduct, ?_⟩
      rw [fzzCigarParityQuadraticEigenphase_negativeProduct_eq_neg_one (by norm_num)]
      apply Complex.ext
      · simp [hre]
      · simp [himzero]
  · let w := fzzCigarParityUpperLeftUnitSquareRoot z
    obtain ⟨beta, hbeta, hy⟩ :=
      exists_pos_fzzCigarParityKreinEigenline_eq_of_unit_upperLeft
        (norm_fzzCigarParityUpperLeftUnitSquareRoot hnorm)
        (fzzCigarParityUpperLeftUnitSquareRoot_re_neg hnorm (ne_of_gt himpos))
        (fzzCigarParityUpperLeftUnitSquareRoot_im_pos hnorm (ne_of_gt himpos))
    refine ⟨beta, hbeta, .conjugateSquare, ?_⟩
    rw [fzzCigarParityQuadraticEigenphase, hy]
    exact star_fzzCigarParityUpperLeftUnitSquareRoot_sq_eq_of_im_pos hnorm himpos

theorem norm_fzzCigarParityQuadraticEigenphase
    {beta : ℝ} (hbeta : 0 < beta)
    (channel : FZZCigarParityQuadraticEigenphaseChannel) :
    ‖fzzCigarParityQuadraticEigenphase beta channel‖ = 1 := by
  cases channel <;>
    simp [fzzCigarParityQuadraticEigenphase,
      norm_fzzCigarParityDilatedKreinEigenlineBalancedCoordinate hbeta]

/-- Matching any quadratic source interaction phase forces critical-line placement. -/
theorem fzzCigarParityDyadicMellinCharacter_eq_quadraticEigenphase_forces_critical
    {beta : ℝ} (hbeta : 0 < beta) {rho : ℂ}
    {channel : FZZCigarParityQuadraticEigenphaseChannel}
    (hmatch : fzzCigarParityDyadicMellinCharacter rho =
      fzzCigarParityQuadraticEigenphase beta channel) :
    rho.re = 1 / 2 := by
  have hnorm := congrArg norm hmatch
  rw [norm_fzzCigarParityDyadicMellinCharacter,
    norm_fzzCigarParityQuadraticEigenphase hbeta] at hnorm
  have hnorm' : Real.exp (Real.log 2 * (rho.re - 1 / 2)) = Real.exp 0 := by
    simpa using hnorm
  have harg : Real.log 2 * (rho.re - 1 / 2) = 0 :=
    Real.exp_injective hnorm'
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Every critical-line centered dyadic Mellin character has an exact positive-scale quadratic
source realization. -/
theorem exists_pos_fzzCigarParityQuadraticEigenphase_eq_dyadicMellinCharacter
    {rho : ℂ} (hrho : rho.re = 1 / 2) :
    ∃ beta : ℝ, 0 < beta ∧
      ∃ channel : FZZCigarParityQuadraticEigenphaseChannel,
        fzzCigarParityQuadraticEigenphase beta channel =
          fzzCigarParityDyadicMellinCharacter rho := by
  apply exists_pos_fzzCigarParityQuadraticEigenphase_eq_of_norm_one
  rw [norm_fzzCigarParityDyadicMellinCharacter, hrho]
  norm_num

/-- Exact local classification: quadratic source incidence is precisely the critical line. -/
theorem exists_pos_fzzCigarParityQuadraticEigenphase_eq_dyadicMellinCharacter_iff
    (rho : ℂ) :
    (∃ beta : ℝ, 0 < beta ∧
      ∃ channel : FZZCigarParityQuadraticEigenphaseChannel,
        fzzCigarParityQuadraticEigenphase beta channel =
          fzzCigarParityDyadicMellinCharacter rho) ↔
      rho.re = 1 / 2 := by
  constructor
  · rintro ⟨beta, hbeta, channel, hmatch⟩
    exact fzzCigarParityDyadicMellinCharacter_eq_quadraticEigenphase_forces_critical
      hbeta hmatch.symm
  · exact exists_pos_fzzCigarParityQuadraticEigenphase_eq_dyadicMellinCharacter

/-- Every open-strip zeta divisor is realized by a positive-scale quadratic interaction phase. -/
def FZZCigarParityQuadraticEigenphaseDivisorComplete : Prop :=
  ∀ rho : ℂ, riemannZeta rho = 0 → 0 < rho.re → rho.re < 1 →
    ∃ beta : ℝ, 0 < beta ∧
      ∃ channel : FZZCigarParityQuadraticEigenphaseChannel,
        fzzCigarParityQuadraticEigenphase beta channel =
          fzzCigarParityDyadicMellinCharacter rho

/-- **Exact global endpoint.** Quadratic source-phase completeness on the open zeta divisor is
equivalent to RH. -/
theorem fzzCigarParityQuadraticEigenphaseDivisorComplete_iff_rh :
    FZZCigarParityQuadraticEigenphaseDivisorComplete ↔ RiemannHypothesis := by
  constructor
  · intro hcomplete
    rw [riemannHypothesis_iff_forall_zero_re_le_half]
    intro rho hz
    rcases riemannZeta_zero_trivial_or_mem_strip hz with htrivial | hstrip
    · obtain ⟨n, rfl⟩ := htrivial
      rw [show (-(2 * ((n : ℂ) + 1))) =
          ((-(2 * ((n : ℝ) + 1)) : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · exact le_of_eq ((exists_pos_fzzCigarParityQuadraticEigenphase_eq_dyadicMellinCharacter_iff
        rho).mp (hcomplete rho hz hstrip.1 hstrip.2))
  · intro hRH rho hz h0 h1
    have htrivial : ¬ ∃ n : ℕ, rho = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, hn⟩
      rw [hn, show (-2 * ((n : ℂ) + 1)) =
          ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re] at h0
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hrho : rho.re = 1 / 2 :=
      hRH rho hz htrivial (riemannZeta_zero_ne_one hz)
    exact exists_pos_fzzCigarParityQuadraticEigenphase_eq_dyadicMellinCharacter hrho

end

end RHTower
