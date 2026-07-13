import GaloisForLFunctions.RHTower.PrimeAlgebraicTranslationWeylPhase
import Mathlib.NumberTheory.Niven

/-!
# Irrational-rotation K-zero trace collision

At the rational-imaginary prime--Weyl step `I/q`, write

`theta_(p,q) = log(p) / (2*pi*q)`.

The Weyl multiplier is `exp(-2*pi*I*theta_(p,q))`.  Its Gelfond--Schneider transcendence implies
that `theta_(p,q)` is irrational.  The canonical trace of an irrational-rotation `K₀` coordinate
`(rank, chern)` has the form

`rank + theta_(p,q) * chern`.

If this trace is an integer, irrationality forces the Chern coordinate to vanish.  This gives a
second positive successor to the moving-fiber parallelogram: a moving cluster may remain a genuine
projective module rather than descend to one fixed finite-dimensional fiber, but an integer analytic
rank cannot coexist with a nonzero rotation Chern charge.

The file proves the concrete irrational parameter and the arithmetic collision.  The final RH
interface deliberately exposes the missing source theorem: construct a prime-rotation projective
module whose canonical trace is the analytic cluster rank and whose Chern coordinate is its
off-line local multiplicity.
-/

open Complex

namespace RHTower

noncomputable section

/-- Rotation parameter of the prime--Weyl relation at the step `I/q`. -/
def primeRotationParameter (p : Nat.Primes) (q : ℕ) : ℝ :=
  Real.log p / (2 * Real.pi * q)

/-- The prime--Weyl determinant phase in rank one is the irrational-rotation multiplier. -/
theorem primeAlgebraicWeylDeterminantPhase_one_eq_rotationMultiplier
    (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) :
    primeAlgebraicWeylDeterminantPhase p 1 q =
      Complex.exp
        (((-2 * primeRotationParameter p q : ℝ) : ℂ) *
          (Real.pi : ℂ) * Complex.I) := by
  rw [primeAlgebraicWeylDeterminantPhase,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast p.2.ne_zero)]
  rw [← Complex.natCast_log]
  congr 1
  norm_num only [Nat.cast_one]
  have hreal :
      -Real.log p / (q : ℝ) =
        (-2 * primeRotationParameter p q) * Real.pi := by
    unfold primeRotationParameter
    field_simp [Real.pi_ne_zero, hq]
  calc
    ↑(Real.log p) * (-((1 : ℂ) / (q : ℂ)) * I) =
        ((-Real.log p / (q : ℝ) : ℝ) : ℂ) * I := by push_cast; ring
    _ = (((-2 * primeRotationParameter p q) * Real.pi : ℝ) : ℂ) * I := by
      rw [hreal]
    _ = ↑(-2 * primeRotationParameter p q) * ↑Real.pi * I := by
      push_cast
      ring

/-- The concrete rotation parameter is irrational.  If it were rational, its rotation multiplier
would be a root of unity and hence algebraic, contradicting the prime-phase transcendence theorem. -/
theorem primeRotationParameter_irrational
    (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) :
    Irrational (primeRotationParameter p q) := by
  rintro ⟨r, hr⟩
  have hphase : IsAlgebraic ℚ
      (primeAlgebraicWeylDeterminantPhase p 1 q) := by
    rw [primeAlgebraicWeylDeterminantPhase_one_eq_rotationMultiplier p hq]
    rw [← hr]
    have hi := Complex.isIntegral_exp_rat_mul_pi_mul_I (-2 * r)
    have ha : IsAlgebraic ℤ
        (Complex.exp
          ((((-2 * r : ℚ) : ℝ) : ℂ) * (Real.pi : ℂ) * Complex.I)) :=
      hi.isAlgebraic
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp (by simpa using ha)
  exact primeAlgebraicWeylDeterminantPhase_transcendental p
    (by norm_num) hq hphase

/-- Numerical trace pairing of a rotation `K₀` coordinate `(rank, chern)`. -/
def irrationalRotationKZeroTrace (theta : ℝ) (rank chern : ℤ) : ℝ :=
  rank + theta * chern

/-- **Irrational trace collision.**  An irrational-rotation `K₀` trace can be an integer only when
the Chern coordinate vanishes. -/
theorem chern_eq_zero_of_irrationalRotationKZeroTrace_eq_integer
    {theta : ℝ} (htheta : Irrational theta) {rank chern index : ℤ}
    (htrace : irrationalRotationKZeroTrace theta rank chern = index) :
    chern = 0 := by
  by_contra hchern
  apply htheta
  refine ⟨((index - rank : ℤ) : ℚ) / (chern : ℚ), ?_⟩
  rw [irrationalRotationKZeroTrace] at htrace
  push_cast at htrace ⊢
  field_simp
  nlinarith

/-- Minimal coordinate interface for a source projective module: its canonical rotation trace is
the integer analytic rank `d`, and its Chern coordinate is the local off-line charge `d`.  The
source construction of such a module is intentionally not part of this definition. -/
structure PrimeRotationKZeroIndexDatum
    (p : Nat.Primes) (q d : ℕ) where
  rank : ℤ
  chern : ℤ
  trace_eq_order :
    irrationalRotationKZeroTrace (primeRotationParameter p q) rank chern = (d : ℤ)
  chern_eq_order : chern = (d : ℤ)

/-- A prime-rotation `K₀` datum with integer analytic trace and multiplicity Chern charge exists
exactly in rank zero. -/
theorem primeRotationKZeroIndexDatum_iff
    (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) (d : ℕ) :
    Nonempty (PrimeRotationKZeroIndexDatum p q d) ↔ d = 0 := by
  constructor
  · rintro ⟨h⟩
    have hchern := chern_eq_zero_of_irrationalRotationKZeroTrace_eq_integer
      (primeRotationParameter_irrational p hq) h.trace_eq_order
    have hd : (d : ℤ) = 0 := by rw [← h.chern_eq_order, hchern]
    exact_mod_cast hd
  · rintro rfl
    exact ⟨⟨0, 0, by simp [irrationalRotationKZeroTrace], by simp⟩⟩

/-- Prime-rotation `K₀` datum attached to the local Xi multiplicity. -/
abbrev XiPrimeRotationKZeroIndexDatum
    (p : Nat.Primes) (q : ℕ) (rho : ℂ) :=
  PrimeRotationKZeroIndexDatum p q (analyticOrderAt xi rho).toNat

/-- **Irrational-rotation projective-module criterion for RH.**  Constructing the trace/Chern
interface at every hypothetical right-half zero forces its local order to vanish. -/
theorem riemannHypothesis_iff_xiPrimeRotationKZeroIndexData
    (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) :
    RiemannHypothesis ↔
      ∀ rho ∈ rightHalf, xi rho = 0 →
        Nonempty (XiPrimeRotationKZeroIndexDatum p q rho) := by
  constructor
  · intro hRH rho hrho hzero
    exact (rh_iff_xi_ne_zero_right.mp hRH rho hrho hzero).elim
  · intro hdata
    apply rh_iff_xi_ne_zero_right.mpr
    intro rho hrho hzero
    have horder :=
      (primeRotationKZeroIndexDatum_iff
        p hq (analyticOrderAt xi rho).toNat).mp
          (hdata rho hrho hzero)
    exact (xi_order_toNat_ne_zero hzero horder).elim

end

end RHTower
