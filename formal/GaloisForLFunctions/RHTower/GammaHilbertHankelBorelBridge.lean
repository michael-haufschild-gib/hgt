import GaloisForLFunctions.RHTower.GammaCoPoissonIntervalFactorialBridge

/-!
# Gamma factorial compression as a Hilbert--Hankel Borel column

The Hilbert--Hankel moment kernel

`H(m,n) = 1 / (m+n+1)`

solves the local coordinate mismatch between Hardy source depth and the
Gamma factorial jet.  Its columns advance by the backward coefficient shift,
and the exponential Borel transform of its zeroth column is exactly the
Gamma factorial compression

`C(z) = ∑ n, z^n / (n+1)!`.

Consequently every confluent Gamma/co-Poisson interval jet is the
corresponding Hilbert moment multiplied by the exact exponential character
and logarithmic-action power.

This file proves the dependency-closed coefficient and confluence core.  It
does not construct the bounded infinite Hilbert operator, the multiplicative
all-prime Hilbert completion, the source-normal exact-couple morphism, or an
Xi conormal landing.
-/

open Complex

namespace RHTower

noncomputable section

/-- Hilbert--Hankel moment entry.  Analytically this is both
`∫ t in 0..1, t^(m+n)` and `∫ x in 0..∞, exp (-(m+n+1)x)`. -/
def gammaHilbertHankelEntry (m n : ℕ) : ℂ :=
  (((m + n + 1 : ℕ) : ℂ))⁻¹

/-- Hilbert--Hankel entries are symmetric. -/
theorem gammaHilbertHankelEntry_symm (m n : ℕ) :
    gammaHilbertHankelEntry m n = gammaHilbertHankelEntry n m := by
  simp [gammaHilbertHankelEntry, add_comm]

/-- **Hankel shift law.**  Advancing the column is the same as advancing the
row.  On the finite-sequence core this is the matrix identity `H S = S† H`. -/
theorem gammaHilbertHankelEntry_succ_left (m n : ℕ) :
    gammaHilbertHankelEntry (m + 1) n =
      gammaHilbertHankelEntry m (n + 1) := by
  simp [gammaHilbertHankelEntry, add_comm, add_left_comm]

/-- Exponential Borel compression of one Hilbert--Hankel column. -/
def gammaHilbertBorelColumnCompression (m : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ,
    gammaHilbertHankelEntry m n * z ^ n / (n.factorial : ℂ)

/-- **Gamma/Hilbert--Hankel identification.**  The complete factorial-tail
Gamma conormal is exactly the exponential Borel transform of the zeroth
Hilbert--Hankel column. -/
theorem gammaFactorialComplexCompression_eq_gammaHilbertBorelColumn
    (z : ℂ) :
    gammaFactorialComplexCompression z =
      gammaHilbertBorelColumnCompression 0 z := by
  rw [gammaFactorialComplexCompression, gammaHilbertBorelColumnCompression]
  apply tsum_congr
  intro n
  rw [Nat.factorial_succ]
  simp only [gammaHilbertHankelEntry, zero_add]
  push_cast
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- **Confluent interval jets are Hilbert moments.**  The `k`th local
multiplicity jet of the literal Gamma/co-Poisson interval cell is the zeroth
row, `k`th column Hilbert moment times the exact logarithmic character. -/
theorem iteratedDeriv_gammaCoPoissonIntervalCell_self_eq_hilbertEntry
    (L w : ℂ) (k : ℕ) :
    iteratedDeriv k (fun z =>
      gammaCoPoissonIntervalCell L z w) w =
      Complex.exp ((w - 1 / 2) * L) *
        L ^ (k + 1) * gammaHilbertHankelEntry 0 k := by
  rw [iteratedDeriv_gammaCoPoissonIntervalCell_self]
  simp only [gammaHilbertHankelEntry, zero_add]
  rw [div_eq_mul_inv]
  push_cast
  rfl

/-- The scalar entry of the multiplicative-Hilbert Gram form after moving
its lower Mellin horizon from `1/2` to `1/2-c`.

For a positive real logarithmic action `L = log (m*n)`, this is

`∫ s in (1/2-c)..∞, exp (-L*s) = exp ((c-1/2)*L) / L`.

The algebraic definition is used here so the boundary identities remain
unconditional over `ℂ`, including the totalized value at `L = 0`. -/
def movingHorizonMultiplicativeHilbertEntry (c L : ℂ) : ℂ :=
  Complex.exp ((c - 1 / 2) * L) / L

/-- Boundary amplitude produced by differentiating the lower Mellin horizon.
For `L = log n` and real `c`, this is `n^(c-1/2)`. -/
def movingHorizonBoundaryAmplitude (c L : ℂ) : ℂ :=
  Complex.exp ((c - 1 / 2) * L)

/-- Boundary amplitudes factor over additive logarithmic actions.  On
`L₁ = log m`, `L₂ = log n`, this is the rank-one factorization of the
moving-horizon boundary Gram kernel. -/
theorem movingHorizonBoundaryAmplitude_add (c L₁ L₂ : ℂ) :
    movingHorizonBoundaryAmplitude c (L₁ + L₂) =
      movingHorizonBoundaryAmplitude c L₁ *
        movingHorizonBoundaryAmplitude c L₂ := by
  rw [movingHorizonBoundaryAmplitude, movingHorizonBoundaryAmplitude,
    movingHorizonBoundaryAmplitude]
  rw [mul_add, Complex.exp_add]

/-- **Rank-one horizon derivative.**  Away from the totalized zero-action
coordinate, differentiating the multiplicative-Hilbert Gram horizon produces
the factorized boundary amplitude. -/
theorem hasDerivAt_movingHorizonMultiplicativeHilbertEntry
    (c L : ℂ) (hL : L ≠ 0) :
    HasDerivAt
      (fun z => movingHorizonMultiplicativeHilbertEntry z L)
      (movingHorizonBoundaryAmplitude c L) c := by
  have hinner :
      HasDerivAt (fun z : ℂ => (z - 1 / 2) * L) L c := by
    simpa [div_eq_mul_inv] using
      ((hasDerivAt_id c).sub_const ((1 : ℂ) / 2)).mul_const L
  simpa [movingHorizonMultiplicativeHilbertEntry,
    movingHorizonBoundaryAmplitude, hL] using hinner.cexp.div_const L

/-- Squared coefficient weight of the real moving-horizon boundary amplitude,
indexed from the first nontrivial integer `n + 2`. -/
def movingHorizonBoundaryWeight (c : ℝ) (n : ℕ) : ℝ :=
  (((n + 2 : ℕ) : ℝ)) ^ (2 * c - 1)

/-- **Sharp horizon regularity wall.**  The rank-one boundary amplitude is
square summable on the ordinary integer coefficient space exactly on the
strict left side `c < 0`. -/
theorem summable_movingHorizonBoundaryWeight_iff (c : ℝ) :
    Summable (movingHorizonBoundaryWeight c) ↔ c < 0 := by
  constructor
  · intro h
    change Summable
      (fun n : ℕ => (((n + 2 : ℕ) : ℝ)) ^ (2 * c - 1)) at h
    have hshift :
        Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ)) ^ (2 * c - 1)) := by
      exact h
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (2 * c - 1)) := by
      exact (summable_nat_add_iff
        (f := fun n : ℕ => (n : ℝ) ^ (2 * c - 1)) 2).1 hshift
    have hexponent := Real.summable_nat_rpow.1 hbase
    linarith
  · intro hc
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (2 * c - 1)) :=
      Real.summable_nat_rpow.2 (by linarith)
    have hshift :
        Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ)) ^ (2 * c - 1)) := by
      exact (summable_nat_add_iff
        (f := fun n : ℕ => (n : ℝ) ^ (2 * c - 1)) 2).2 hbase
    change Summable
      (fun n : ℕ => (((n + 2 : ℕ) : ℝ)) ^ (2 * c - 1))
    exact hshift

/-- The reflected boundary amplitude is square summable exactly on the
opposite strict side. -/
theorem summable_reflected_movingHorizonBoundaryWeight_iff (c : ℝ) :
    Summable (movingHorizonBoundaryWeight (-c)) ↔ 0 < c := by
  rw [summable_movingHorizonBoundaryWeight_iff]
  constructor <;> intro h <;> linarith

/-- Reflected moving-horizon boundary amplitudes can never both be Hilbert
vectors in the fixed ordinary-integer coefficient space. -/
theorem not_both_summable_reflected_movingHorizonBoundaryWeight (c : ℝ) :
    ¬ (Summable (movingHorizonBoundaryWeight c) ∧
      Summable (movingHorizonBoundaryWeight (-c))) := by
  rw [summable_movingHorizonBoundaryWeight_iff,
    summable_reflected_movingHorizonBoundaryWeight_iff]
  rintro ⟨hcneg, hcpos⟩
  linarith

/-- Off the fixed horizon, exactly one of the two reflected rank-one boundary
amplitudes lies in the ordinary coefficient Hilbert space.  At `c = 0`,
neither does: both coincide with the critical harmonic boundary. -/
theorem one_summable_reflected_movingHorizonBoundaryWeight
    {c : ℝ} (hc : c ≠ 0) :
    Summable (movingHorizonBoundaryWeight c) ∨
      Summable (movingHorizonBoundaryWeight (-c)) := by
  rw [summable_movingHorizonBoundaryWeight_iff,
    summable_reflected_movingHorizonBoundaryWeight_iff]
  exact lt_or_gt_of_ne hc

/-- **Diagonal Gamma/Hilbert horizon law.**  The moving-horizon Gram entry
is the diagonal Gamma/co-Poisson interval cell divided by the square of the
logarithmic action. -/
theorem movingHorizonMultiplicativeHilbertEntry_eq_gammaCell_self
    (c L : ℂ) :
    movingHorizonMultiplicativeHilbertEntry c L =
      gammaCoPoissonIntervalCell L c c / L ^ 2 := by
  rw [movingHorizonMultiplicativeHilbertEntry,
    gammaCoPoissonIntervalCell_self]
  field_simp

/-- **Critical-horizon transgression.**  The literal Gamma/co-Poisson
interval cell is exactly the secant displacement of the multiplicative
Hilbert Gram entry away from the fixed critical horizon `c = 0`. -/
theorem movingHorizonMultiplicativeHilbertEntry_sub_critical
    (c L : ℂ) :
    movingHorizonMultiplicativeHilbertEntry c L -
        movingHorizonMultiplicativeHilbertEntry 0 L =
      c / L * gammaCoPoissonIntervalCell L c 0 := by
  rw [movingHorizonMultiplicativeHilbertEntry,
    movingHorizonMultiplicativeHilbertEntry]
  have hboundary :
      Complex.exp ((c - 1 / 2) * L) -
          Complex.exp ((0 - 1 / 2) * L) =
        c * gammaCoPoissonIntervalCell L c 0 := by
    simpa only [sub_zero] using
      (spectralBoundary_mul_gammaCoPoissonIntervalCell L c 0).symm
  calc
    Complex.exp ((c - 1 / 2) * L) / L -
          Complex.exp ((0 - 1 / 2) * L) / L =
        (Complex.exp ((c - 1 / 2) * L) -
          Complex.exp ((0 - 1 / 2) * L)) / L := by ring
    _ = (c * gammaCoPoissonIntervalCell L c 0) / L := by rw [hboundary]
    _ = c / L * gammaCoPoissonIntervalCell L c 0 := by
      field_simp

/-- **Reflected-horizon transgression.**  The Gamma/co-Poisson cell is
exactly the signed displacement between reflected multiplicative-Hilbert
Gram horizons.  This identifies the local Sonin/reflection defect with a
moving-boundary Gram defect, rather than with a new positivity condition. -/
theorem movingHorizonMultiplicativeHilbertEntry_sub_reflected
    (c L : ℂ) :
    movingHorizonMultiplicativeHilbertEntry c L -
        movingHorizonMultiplicativeHilbertEntry (-c) L =
      (2 * c) / L * gammaCoPoissonIntervalCell L c (-c) := by
  rw [movingHorizonMultiplicativeHilbertEntry,
    movingHorizonMultiplicativeHilbertEntry]
  have hboundary :
      Complex.exp ((c - 1 / 2) * L) -
          Complex.exp ((-c - 1 / 2) * L) =
        (2 * c) * gammaCoPoissonIntervalCell L c (-c) := by
    calc
      Complex.exp ((c - 1 / 2) * L) -
            Complex.exp ((-c - 1 / 2) * L) =
          (c - (-c)) * gammaCoPoissonIntervalCell L c (-c) :=
        (spectralBoundary_mul_gammaCoPoissonIntervalCell L c (-c)).symm
      _ = (2 * c) * gammaCoPoissonIntervalCell L c (-c) := by ring
  calc
    Complex.exp ((c - 1 / 2) * L) / L -
          Complex.exp ((-c - 1 / 2) * L) / L =
        (Complex.exp ((c - 1 / 2) * L) -
          Complex.exp ((-c - 1 / 2) * L)) / L := by ring
    _ = ((2 * c) * gammaCoPoissonIntervalCell L c (-c)) / L := by
      rw [hboundary]
    _ = (2 * c) / L * gammaCoPoissonIntervalCell L c (-c) := by
      field_simp

/-- Moving a Gram horizon from `-c` to `c` is multiplication by the exact
reflected modular character `exp (2*c*L)`.  This equality is entrywise; it
does not assert a bounded operator quotient between the two completions. -/
theorem movingHorizonMultiplicativeHilbertEntry_reflection_transport
    (c L : ℂ) :
    movingHorizonMultiplicativeHilbertEntry c L =
      Complex.exp (2 * c * L) *
        movingHorizonMultiplicativeHilbertEntry (-c) L := by
  rw [movingHorizonMultiplicativeHilbertEntry,
    movingHorizonMultiplicativeHilbertEntry, ← mul_div_assoc,
    ← Complex.exp_add]
  congr 2
  ring

/-- A horizon displacement is diagonal gauge multiplication of the fixed
critical entry.  For `L = log (m*n)`, the multiplier is `(m*n)^c`. -/
theorem movingHorizonMultiplicativeHilbertEntry_eq_gauge_mul_critical
    (c L : ℂ) :
    movingHorizonMultiplicativeHilbertEntry c L =
      Complex.exp (c * L) *
        movingHorizonMultiplicativeHilbertEntry 0 L := by
  rw [movingHorizonMultiplicativeHilbertEntry,
    movingHorizonMultiplicativeHilbertEntry, ← mul_div_assoc,
    ← Complex.exp_add]
  congr 2
  ring

/-- **Two-sided diagonal gauge law.**  After decomposing
`L = L₁ + L₂`, moving the Gram horizon is multiplication by one gauge
factor on each coefficient index.  This is the scalar core of
`H_c = D_c H_0 D_c`. -/
theorem movingHorizonMultiplicativeHilbertEntry_twoSidedGauge
    (c L₁ L₂ : ℂ) :
    movingHorizonMultiplicativeHilbertEntry c (L₁ + L₂) =
      Complex.exp (c * L₁) *
        movingHorizonMultiplicativeHilbertEntry 0 (L₁ + L₂) *
          Complex.exp (c * L₂) := by
  rw [movingHorizonMultiplicativeHilbertEntry_eq_gauge_mul_critical,
    mul_add, Complex.exp_add]
  ring

/-- For nonzero logarithmic action, the reflected Gram-entry ratio is the
exact modular drift `exp (2*c*L)`. -/
theorem movingHorizonMultiplicativeHilbertEntry_reflection_ratio
    (c L : ℂ) (hL : L ≠ 0) :
    movingHorizonMultiplicativeHilbertEntry c L /
        movingHorizonMultiplicativeHilbertEntry (-c) L =
      Complex.exp (2 * c * L) := by
  apply (div_eq_iff ?_).2
  · exact movingHorizonMultiplicativeHilbertEntry_reflection_transport c L
  · exact div_ne_zero (Complex.exp_ne_zero _) hL

end

end RHTower
