import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthReflectionDiagonalBlindness
import GaloisForLFunctions.RHTower.BurnolCoPoissonConormalReflectionCover

/-!
# Off-diagonal countertransport and the exact all-depth Hodge wall

The reflected primitive/co-source codiagonal erases centered horizontal
displacement.  This module retains two distinct prime-depth labels first.
For log-clock `lambda_i = log (p^(e+1))`, the literal source incidence
factors as

`P_(eps,a)(i,j) = P_(eps,0)(i,j) * exp (a * (lambda_j-lambda_i))`.

Hence the normalized incidence is the exact edge character
`H_a(i,j) = exp (a * (lambda_j-lambda_i))`.  It is a flat coboundary:
all triangle holonomies are one.  This closes the entire multiplicative
cycle class as horizontally blind, rather than merely finding one failed
cycle.  More strongly, every finite displaced source-incidence matrix is
explicitly diagonally similar to its zero-displacement matrix.  Its
characteristic polynomial, determinant, and every cyclic trace moment are
therefore horizontally blind.

On every finite injectively resolved packet, division by the nonzero
log-clock difference constructs a canonical depth-nonlocal countertransport.
Its clock commutator recovers the full off-diagonal incidence.  For the
normalized incidence, the countertransport is skew-Hermitian on the reflected
Hodge sector `re a = 0`, and its commutator is Hermitian there.  The edge
Hermitian law itself is equivalent to `re a = 0` for every distinct pair.

The global capacity wall is sharp: `H_a` is uniformly bounded over all
oriented prime-depth pairs iff `re a = 0`.  Depth separation at the single
prime `2` proves both escape directions.  Specializing `a = rho - 1/2`
identifies `H_a` with the centered Burnol conormal character at the exact
log-clock window length, and uniform capacity over all Xi divisor supports
is equivalent to RH.

This is an unconditional classification, not a proof of RH.  It shows that
the separable/coboundary off-diagonal source has no independent annihilation
law: cycle invariants are identically blind, while uniform Hodge capacity
already is the target critical-line assertion.  A surviving Route-J source
must therefore be genuinely non-coboundary or nonseparable before
codiagonalization.
-/
open Complex Filter

namespace RHTower

noncomputable section

def xiGammaEulerPrimitivePrimeDepthLogClock (pe : Nat.Primes × ℕ) : ℝ :=
  Real.log (xiGammaEulerValuationNat pe : ℝ)

def xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy (a : ℂ) (i j : Nat.Primes × ℕ) : ℂ :=
  Complex.exp (a * ((xiGammaEulerPrimitivePrimeDepthLogClock j - xiGammaEulerPrimitivePrimeDepthLogClock i : ℝ) : ℂ))

def xiGammaEulerPrimitiveReflectedOffDiagonalHolonomyCpow (a : ℂ) (i j : Nat.Primes × ℕ) : ℂ :=
  ((xiGammaEulerValuationNat j : ℂ) ^ a) *
    ((xiGammaEulerValuationNat i : ℂ) ^ a)⁻¹

theorem xiGammaEulerPrimitivePrimeDepthLogClock_apply (p : Nat.Primes) (e : ℕ) :
    xiGammaEulerPrimitivePrimeDepthLogClock (p, e) = (e + 1 : ℕ) * Real.log (p : ℝ) := by
  rw [xiGammaEulerPrimitivePrimeDepthLogClock, xiGammaEulerValuationNat]
  rw [Nat.cast_pow, Real.log_pow]

theorem xiGammaEulerPrimitiveReflectedOffDiagonalHolonomyCpow_eq (a : ℂ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomyCpow a i j = xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i j := by
  have hi : (xiGammaEulerValuationNat i : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ i.1.property.ne_zero
  have hj : (xiGammaEulerValuationNat j : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ j.1.property.ne_zero
  have hlogi : Complex.log (xiGammaEulerValuationNat i : ℂ) =
      (xiGammaEulerPrimitivePrimeDepthLogClock i : ℂ) := by
    rw [xiGammaEulerPrimitivePrimeDepthLogClock, ← Complex.natCast_log]
  have hlogj : Complex.log (xiGammaEulerValuationNat j : ℂ) =
      (xiGammaEulerPrimitivePrimeDepthLogClock j : ℂ) := by
    rw [xiGammaEulerPrimitivePrimeDepthLogClock, ← Complex.natCast_log]
  rw [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomyCpow, xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy,
    Complex.cpow_def_of_ne_zero hi, Complex.cpow_def_of_ne_zero hj,
    hlogi, hlogj, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

def xiGammaEulerPrimitiveReflectedOffDiagonalIncidence (eps : ℝ) (a : ℂ)
    (i j : Nat.Primes × ℕ) : ℂ :=
  xiGammaEulerPrimitiveCommonTestSourceCoeff ((eps : ℂ) + a) i *
    star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff
      ((eps : ℂ) - star a) j)

theorem star_xiGammaEulerPrimitiveCommonTestCoSourceCoeff_eq (w : ℂ) (pe : Nat.Primes × ℕ) :
    star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff w pe) =
      (xiGammaEulerPrimitiveDescentTestAmplitude 0 pe : ℂ) *
        ((xiGammaEulerValuationNat pe : ℂ) ^ star w)⁻¹ := by
  have hn : xiGammaEulerValuationNat pe ≠ 0 :=
    pow_ne_zero _ pe.1.property.ne_zero
  rw [xiGammaEulerPrimitiveCommonTestCoSourceCoeff]
  change (starRingEnd ℂ) (_ * _) = _
  rw [map_mul, Complex.conj_ofReal]
  change _ * star (((xiGammaEulerValuationNat pe : ℂ) ^ w)⁻¹) = _
  rw [star_eulerPrimitivePrimeFeature w _ hn]

theorem xiGammaEulerPrimitiveReflectedOffDiagonalIncidence_factor (eps : ℝ) (a : ℂ)
    (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedOffDiagonalIncidence eps a i j =
      xiGammaEulerPrimitiveReflectedOffDiagonalIncidence eps 0 i j * xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i j := by
  have hi : (xiGammaEulerValuationNat i : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ i.1.property.ne_zero
  have hj : (xiGammaEulerValuationNat j : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ j.1.property.ne_zero
  rw [xiGammaEulerPrimitiveReflectedOffDiagonalIncidence, xiGammaEulerPrimitiveReflectedOffDiagonalIncidence,
    xiGammaEulerPrimitiveCommonTestSourceCoeff,
    xiGammaEulerPrimitiveCommonTestSourceCoeff,
    star_xiGammaEulerPrimitiveCommonTestCoSourceCoeff_eq, star_xiGammaEulerPrimitiveCommonTestCoSourceCoeff_eq,
    ← xiGammaEulerPrimitiveReflectedOffDiagonalHolonomyCpow_eq]
  simp only [map_sub, RCLike.star_def, Complex.conj_ofReal,
    Complex.conj_conj, sub_zero, add_zero]
  rw [Complex.cpow_add _ _ hi,
    show (eps : ℂ) - a = (eps : ℂ) + (-a) by ring,
    Complex.cpow_add _ _ hj, Complex.cpow_neg]
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv]
  simp only [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomyCpow]
  ring

theorem xiGammaEulerPrimitiveReflectedOffDiagonalIncidence_ne_zero (eps : ℝ) (a : ℂ)
    (i j : Nat.Primes × ℕ) : xiGammaEulerPrimitiveReflectedOffDiagonalIncidence eps a i j ≠ 0 := by
  rw [xiGammaEulerPrimitiveReflectedOffDiagonalIncidence]
  apply mul_ne_zero
  · rw [xiGammaEulerPrimitiveCommonTestSourceCoeff]
    apply mul_ne_zero
    · exact_mod_cast (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 i).ne'
    · apply inv_ne_zero
      exact Complex.cpow_ne_zero_iff.mpr <| Or.inl <| by
        exact_mod_cast pow_ne_zero _ i.1.property.ne_zero
  · rw [star_xiGammaEulerPrimitiveCommonTestCoSourceCoeff_eq]
    apply mul_ne_zero
    · exact_mod_cast (xiGammaEulerPrimitiveDescentTestAmplitude_pos 0 j).ne'
    · apply inv_ne_zero
      exact Complex.cpow_ne_zero_iff.mpr <| Or.inl <| by
        exact_mod_cast pow_ne_zero _ j.1.property.ne_zero

def xiGammaEulerPrimitiveReflectedNormalizedIncidence (eps : ℝ) (a : ℂ)
    (i j : Nat.Primes × ℕ) : ℂ :=
  xiGammaEulerPrimitiveReflectedOffDiagonalIncidence eps a i j / xiGammaEulerPrimitiveReflectedOffDiagonalIncidence eps 0 i j

theorem xiGammaEulerPrimitiveReflectedNormalizedIncidence_eq_holonomy (eps : ℝ) (a : ℂ)
    (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedNormalizedIncidence eps a i j = xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i j := by
  rw [xiGammaEulerPrimitiveReflectedNormalizedIncidence, xiGammaEulerPrimitiveReflectedOffDiagonalIncidence_factor]
  field_simp [xiGammaEulerPrimitiveReflectedOffDiagonalIncidence_ne_zero eps 0 i j]

theorem xiGammaEulerPrimitiveReflectedNormalizedIncidence_triangle (eps : ℝ) (a : ℂ)
    (i j k : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedNormalizedIncidence eps a i j *
        xiGammaEulerPrimitiveReflectedNormalizedIncidence eps a j k *
      xiGammaEulerPrimitiveReflectedNormalizedIncidence eps a k i = 1 := by
  rw [xiGammaEulerPrimitiveReflectedNormalizedIncidence_eq_holonomy,
    xiGammaEulerPrimitiveReflectedNormalizedIncidence_eq_holonomy,
    xiGammaEulerPrimitiveReflectedNormalizedIncidence_eq_holonomy,
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy,
    ← Complex.exp_add, ← Complex.exp_add]
  rw [show
    a * ((xiGammaEulerPrimitivePrimeDepthLogClock j - xiGammaEulerPrimitivePrimeDepthLogClock i : ℝ) : ℂ) +
          a * ((xiGammaEulerPrimitivePrimeDepthLogClock k - xiGammaEulerPrimitivePrimeDepthLogClock j : ℝ) : ℂ) +
        a * ((xiGammaEulerPrimitivePrimeDepthLogClock i - xiGammaEulerPrimitivePrimeDepthLogClock k : ℝ) : ℂ) = 0 by
      push_cast
      ring]
  exact Complex.exp_zero

theorem xiGammaEulerPrimitivePrimeDepthLogClock_injective : Function.Injective xiGammaEulerPrimitivePrimeDepthLogClock := by
  intro i j h
  apply xiGammaEulerValuationNat_injective_commonTest
  have hi : (0 : ℝ) < xiGammaEulerValuationNat i := by
    exact_mod_cast pow_pos i.1.property.pos (i.2 + 1)
  have hj : (0 : ℝ) < xiGammaEulerValuationNat j := by
    exact_mod_cast pow_pos j.1.property.pos (j.2 + 1)
  have hexp := congrArg Real.exp h
  rw [xiGammaEulerPrimitivePrimeDepthLogClock, xiGammaEulerPrimitivePrimeDepthLogClock, Real.exp_log hi, Real.exp_log hj] at hexp
  exact_mod_cast hexp

def xiGammaEulerPrimitivePrimeDepthFiniteLogClock {N : ℕ} (packet : Fin N → Nat.Primes × ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => (xiGammaEulerPrimitivePrimeDepthLogClock (packet i) : ℂ)

def xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence {N : ℕ} (eps : ℝ) (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => xiGammaEulerPrimitiveReflectedOffDiagonalIncidence eps a (packet i) (packet j)

/-! ## Complete finite spectral blindness under diagonal source gauge -/

/-- Vertex gauge whose quotient is the normalized off-diagonal source character. -/
def xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge {N : ℕ} (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i =>
    Complex.exp (a * (xiGammaEulerPrimitivePrimeDepthLogClock (packet i) : ℂ))

/-- Explicit inverse of the finite source vertex gauge. -/
def xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv {N : ℕ} (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i =>
    Complex.exp (-a * (xiGammaEulerPrimitivePrimeDepthLogClock (packet i) : ℂ))

/-- The two explicit source gauges cancel in forward order. -/
theorem xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge_mul_inv {N : ℕ} (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet * xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge, xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv, ← Complex.exp_add]
  · simp [xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge, xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv, hij]

/-- The two explicit source gauges cancel in reverse order. -/
theorem xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge_inv_mul {N : ℕ} (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet * xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge, xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv, ← Complex.exp_add]
  · simp [xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge, xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv, hij]

/-- **Full finite source gauge law.**  Every displaced incidence matrix is
explicitly diagonally similar to its zero-displacement matrix. -/
theorem xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_similarity {N : ℕ} (eps : ℝ) (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps a packet =
      xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet *
        xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet *
      xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet := by
  ext i j
  simp only [xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv, xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge,
    xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [xiGammaEulerPrimitiveReflectedOffDiagonalIncidence_factor]
  have hexp :
      xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a (packet i) (packet j) =
        Complex.exp
            (-a * (xiGammaEulerPrimitivePrimeDepthLogClock (packet i) : ℂ)) *
          Complex.exp
            (a * (xiGammaEulerPrimitivePrimeDepthLogClock (packet j) : ℂ)) := by
    rw [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- Every finite characteristic polynomial is horizontally blind. -/
theorem xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_charpoly {N : ℕ} (eps : ℝ) (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) :
    (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps a packet).charpoly =
      (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet).charpoly := by
  rw [xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_similarity]
  rw [Matrix.charpoly_mul_comm]
  rw [← Matrix.mul_assoc, xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge_mul_inv, Matrix.one_mul]

/-- Every finite determinant is horizontally blind. -/
theorem xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_det {N : ℕ} (eps : ℝ) (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) :
    (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps a packet).det =
      (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet).det := by
  rw [xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_similarity, Matrix.det_mul, Matrix.det_mul]
  have hdet : (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet).det * (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet).det = 1 := by
    rw [← Matrix.det_mul, xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge_inv_mul, Matrix.det_one]
  calc
    (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet).det *
          (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet).det *
        (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet).det =
      (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet).det *
        ((xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet).det * (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet).det) := by ring
    _ = _ := by rw [hdet, mul_one]

/-- Diagonal similarity persists through every matrix power. -/
theorem xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_pow {N : ℕ} (eps : ℝ) (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) (m : ℕ) :
    (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps a packet) ^ m =
      xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet *
        (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet) ^ m *
      xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet := by
  induction m with
  | zero =>
      simp [xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge_inv_mul]
  | succ m ih =>
      rw [pow_succ, ih, xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_similarity eps a packet]
      rw [show
        (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet *
              (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet) ^ m *
            xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet) *
            (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet *
                xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet *
              xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet) =
          xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet *
              (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet) ^ m *
            (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet * xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet) *
            xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet *
          xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet by noncomm_ring]
      rw [xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge_mul_inv, Matrix.mul_one, pow_succ]
      noncomm_ring

/-- Every finite cyclic trace moment is horizontally blind. -/
theorem xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_trace_pow {N : ℕ} (eps : ℝ) (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) (m : ℕ) :
    Matrix.trace
        ((xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps a packet) ^ m) =
      Matrix.trace
        ((xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet) ^ m) := by
  rw [xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_pow]
  calc
    Matrix.trace
        (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet *
          (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet) ^ m *
          xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet) =
      Matrix.trace
        (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge a packet *
          (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGaugeInv a packet *
            (xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps 0 packet) ^ m)) :=
      Matrix.trace_mul_comm _ _
    _ = _ := by
      rw [← Matrix.mul_assoc, xiGammaEulerPrimitiveReflectedFiniteOffDiagonalGauge_mul_inv, Matrix.one_mul]


def xiGammaEulerPrimitiveReflectedFiniteOffDiagonalCountertransport {N : ℕ} (eps : ℝ) (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i = j then 0 else
    xiGammaEulerPrimitiveReflectedOffDiagonalIncidence eps a (packet i) (packet j) /
      ((xiGammaEulerPrimitivePrimeDepthLogClock (packet i) - xiGammaEulerPrimitivePrimeDepthLogClock (packet j) : ℝ) : ℂ)

theorem xiGammaEulerPrimitiveReflectedFiniteOffDiagonalCountertransport_commutator {N : ℕ}
    (eps : ℝ) (a : ℂ) (packet : Fin N → Nat.Primes × ℕ)
    (hpacket : Function.Injective packet) :
    xiGammaEulerPrimitivePrimeDepthFiniteLogClock packet * xiGammaEulerPrimitiveReflectedFiniteOffDiagonalCountertransport eps a packet -
        xiGammaEulerPrimitiveReflectedFiniteOffDiagonalCountertransport eps a packet * xiGammaEulerPrimitivePrimeDepthFiniteLogClock packet =
      xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence eps a packet -
        Matrix.diagonal (fun i => xiGammaEulerPrimitiveReflectedOffDiagonalIncidence eps a (packet i) (packet i)) := by
  ext i j
  simp only [xiGammaEulerPrimitivePrimeDepthFiniteLogClock, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.sub_apply, xiGammaEulerPrimitiveReflectedFiniteOffDiagonalCountertransport, xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence]
  by_cases hij : i = j
  · subst j
    simp
  · have hclock : xiGammaEulerPrimitivePrimeDepthLogClock (packet i) - xiGammaEulerPrimitivePrimeDepthLogClock (packet j) ≠ 0 := by
      rw [sub_ne_zero]
      exact xiGammaEulerPrimitivePrimeDepthLogClock_injective.ne (hpacket.ne hij)
    simp only [hij, if_false, Matrix.diagonal_apply_ne _ hij]
    have hclockC :
        ((xiGammaEulerPrimitivePrimeDepthLogClock (packet i) - xiGammaEulerPrimitivePrimeDepthLogClock (packet j) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hclock
    field_simp [hclockC]
    push_cast
    ring

theorem norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy (a : ℂ) (i j : Nat.Primes × ℕ) :
    ‖xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i j‖ =
      Real.exp (a.re * (xiGammaEulerPrimitivePrimeDepthLogClock j - xiGammaEulerPrimitivePrimeDepthLogClock i)) := by
  rw [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, Complex.norm_exp]
  simp

theorem xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_cocycle (a : ℂ) (i j k : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i j * xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a j k = xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i k := by
  rw [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_reverse (a : ℂ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i j * xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a j i = 1 := by
  rw [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_cocycle]
  simp [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy]

theorem xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_triangle (a : ℂ) (i j k : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i j * xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a j k * xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a k i = 1 := by
  rw [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_cocycle, xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_reverse]

theorem xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_reflection (a : ℂ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy (-star a) i j = (star (xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i j))⁻¹ := by
  rw [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy]
  rw [show star (Complex.exp
      (a * ((xiGammaEulerPrimitivePrimeDepthLogClock j - xiGammaEulerPrimitivePrimeDepthLogClock i : ℝ) : ℂ))) =
        Complex.exp (star a * ((xiGammaEulerPrimitivePrimeDepthLogClock j - xiGammaEulerPrimitivePrimeDepthLogClock i : ℝ) : ℂ)) by
    change (starRingEnd ℂ) (Complex.exp _) = _
    rw [← Complex.exp_conj]
    congr 1
    simp]
  rw [← Complex.exp_neg]
  congr 1
  ring

theorem xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_eq_reflection_iff (a : ℂ)
    {i j : Nat.Primes × ℕ} (hij : i ≠ j) :
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i j = xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy (-star a) i j ↔ a.re = 0 := by
  have hclock : xiGammaEulerPrimitivePrimeDepthLogClock j - xiGammaEulerPrimitivePrimeDepthLogClock i ≠ 0 := by
    rw [sub_ne_zero]
    exact xiGammaEulerPrimitivePrimeDepthLogClock_injective.ne hij.symm
  constructor
  · intro h
    have hn := congrArg norm h
    rw [norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy] at hn
    have hexp := Real.exp_injective hn
    simp only [neg_re, RCLike.star_def, Complex.conj_re] at hexp
    have hmul : a.re * (xiGammaEulerPrimitivePrimeDepthLogClock j - xiGammaEulerPrimitivePrimeDepthLogClock i) = 0 := by
      linarith
    exact (mul_eq_zero.mp hmul).resolve_right hclock
  · intro hre
    have ha : a = -star a := by
      apply Complex.ext
      · simp [hre]
      · simp
    rw [← ha]

theorem xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_hermitianEdge_iff (a : ℂ)
    {i j : Nat.Primes × ℕ} (hij : i ≠ j) :
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a j i = star (xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i j) ↔ a.re = 0 := by
  have hclock : xiGammaEulerPrimitivePrimeDepthLogClock j - xiGammaEulerPrimitivePrimeDepthLogClock i ≠ 0 := by
    rw [sub_ne_zero]
    exact xiGammaEulerPrimitivePrimeDepthLogClock_injective.ne hij.symm
  constructor
  · intro h
    have hn := congrArg norm h
    rw [norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, norm_star, norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy] at hn
    have hexp := Real.exp_injective hn
    have hmul : a.re * (xiGammaEulerPrimitivePrimeDepthLogClock j - xiGammaEulerPrimitivePrimeDepthLogClock i) = 0 := by
      linarith
    exact (mul_eq_zero.mp hmul).resolve_right hclock
  · intro hre
    rw [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy]
    change Complex.exp _ = (starRingEnd ℂ) (Complex.exp _)
    rw [← Complex.exp_conj]
    congr 1
    have ha : (starRingEnd ℂ) a = -a := by
      change star a = -a
      apply Complex.ext
      · simp [hre]
      · simp
    rw [map_mul, ha, Complex.conj_ofReal]
    push_cast
    ring

theorem xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_hermitianEdge_of_re_zero
    {a : ℂ} (ha : a.re = 0) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a j i = star (xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i j) := by
  rw [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy]
  change Complex.exp _ = (starRingEnd ℂ) (Complex.exp _)
  rw [← Complex.exp_conj]
  congr 1
  have hstar : (starRingEnd ℂ) a = -a := by
    change star a = -a
    apply Complex.ext
    · simp [ha]
    · simp
  rw [map_mul, hstar, Complex.conj_ofReal]
  push_cast
  ring

theorem xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_eq_burnolCenteredConormalCharacter
    (rho : ℂ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy (rho - 1 / 2) i j =
      burnolCoPoissonCenteredConormalCharacter
        (xiGammaEulerPrimitivePrimeDepthLogClock j - xiGammaEulerPrimitivePrimeDepthLogClock i) rho := by
  rw [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, burnolCoPoissonCenteredConormalCharacter]
  congr 1
  push_cast
  ring

/-- The normalized source incidence on a finite resolved prime-depth packet. -/
def xiGammaEulerPrimitiveReflectedFiniteOffDiagonalHolonomy {N : ℕ} (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a (packet i) (packet j)

/-- Canonical inverse-clock countertransport of the normalized source
incidence.  It is depth-nonlocal: every pair of distinct retained labels is
transported. -/
def xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport {N : ℕ} (a : ℂ)
    (packet : Fin N → Nat.Primes × ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i = j then 0 else
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a (packet i) (packet j) /
      ((xiGammaEulerPrimitivePrimeDepthLogClock (packet i) - xiGammaEulerPrimitivePrimeDepthLogClock (packet j) : ℝ) : ℂ)

/-- The inverse-clock countertransport reconstructs the whole normalized
off-diagonal source incidence; only its unit codiagonal remains. -/
theorem xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport_commutator {N : ℕ}
    (a : ℂ) (packet : Fin N → Nat.Primes × ℕ)
    (hpacket : Function.Injective packet) :
    xiGammaEulerPrimitivePrimeDepthFiniteLogClock packet * xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport a packet -
        xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport a packet * xiGammaEulerPrimitivePrimeDepthFiniteLogClock packet =
      xiGammaEulerPrimitiveReflectedFiniteOffDiagonalHolonomy a packet - 1 := by
  ext i j
  simp only [xiGammaEulerPrimitivePrimeDepthFiniteLogClock, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.sub_apply, xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport,
    xiGammaEulerPrimitiveReflectedFiniteOffDiagonalHolonomy, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy]
  · have hclock : xiGammaEulerPrimitivePrimeDepthLogClock (packet i) - xiGammaEulerPrimitivePrimeDepthLogClock (packet j) ≠ 0 := by
      rw [sub_ne_zero]
      exact xiGammaEulerPrimitivePrimeDepthLogClock_injective.ne (hpacket.ne hij)
    simp only [hij, if_false]
    have hclockC :
        ((xiGammaEulerPrimitivePrimeDepthLogClock (packet i) - xiGammaEulerPrimitivePrimeDepthLogClock (packet j) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hclock
    field_simp [hclockC]
    push_cast
    ring

/-- On the reflected Hodge sector, the normalized inverse-clock
countertransport is skew-Hermitian. -/
theorem xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport_conjTranspose_eq_neg {N : ℕ}
    {a : ℂ} (ha : a.re = 0)
    (packet : Fin N → Nat.Primes × ℕ) :
    (xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport a packet).conjTranspose =
      -xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport a packet := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  change star (xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport a packet j i) =
    -(xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport a packet i j)
  rw [xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport,
    xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport]
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := Ne.symm hij
    simp only [hji, hij, if_false]
    rw [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_hermitianEdge_of_re_zero ha]
    rw [show star (star (xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a (packet i) (packet j)) /
        (((xiGammaEulerPrimitivePrimeDepthLogClock (packet j) - xiGammaEulerPrimitivePrimeDepthLogClock (packet i) : ℝ) : ℂ))) =
        xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a (packet i) (packet j) /
          (((xiGammaEulerPrimitivePrimeDepthLogClock (packet j) - xiGammaEulerPrimitivePrimeDepthLogClock (packet i) : ℝ) : ℂ)) by
      change (starRingEnd ℂ) (_ / _) = _
      rw [map_div₀]
      change star (star (xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a (packet i) (packet j))) /
          star (((xiGammaEulerPrimitivePrimeDepthLogClock (packet j) - xiGammaEulerPrimitivePrimeDepthLogClock (packet i) : ℝ) : ℂ)) = _
      rw [star_star]
      simp]
    rw [show (((xiGammaEulerPrimitivePrimeDepthLogClock (packet i) - xiGammaEulerPrimitivePrimeDepthLogClock (packet j) : ℝ) : ℂ)) =
        -(((xiGammaEulerPrimitivePrimeDepthLogClock (packet j) - xiGammaEulerPrimitivePrimeDepthLogClock (packet i) : ℝ) : ℂ)) by
      push_cast
      ring, div_neg]
    ring

/-- Equivalently, the clock commutator of the normalized countertransport is
Hermitian on the reflected Hodge sector. -/
theorem xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport_commutator_isHermitian {N : ℕ}
    {a : ℂ} (ha : a.re = 0)
    (packet : Fin N → Nat.Primes × ℕ) :
    (xiGammaEulerPrimitivePrimeDepthFiniteLogClock packet * xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport a packet -
      xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport a packet *
        xiGammaEulerPrimitivePrimeDepthFiniteLogClock packet).IsHermitian := by
  have hclock : (xiGammaEulerPrimitivePrimeDepthFiniteLogClock packet).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [xiGammaEulerPrimitivePrimeDepthFiniteLogClock, Matrix.conjTranspose_apply]
    · simp [xiGammaEulerPrimitivePrimeDepthFiniteLogClock, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  rw [Matrix.IsHermitian]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hclock,
    xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport_conjTranspose_eq_neg ha]
  noncomm_ring

def EulerPrimitiveReflectedOffDiagonalHolonomyUniformlyBounded (a : ℂ) : Prop :=
  ∃ C : ℝ, ∀ i j : Nat.Primes × ℕ, ‖xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a i j‖ ≤ C

theorem tendsto_norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_two_depth_atTop
    {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun e : ℕ => ‖xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a (⟨2, Nat.prime_two⟩, 0)
      (⟨2, Nat.prime_two⟩, e)‖) atTop atTop := by
  rw [show (fun e : ℕ => ‖xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a (⟨2, Nat.prime_two⟩, 0)
      (⟨2, Nat.prime_two⟩, e)‖) =
    fun e : ℕ => Real.exp ((a.re * Real.log 2) * (e : ℝ)) by
      funext e
      rw [norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, xiGammaEulerPrimitivePrimeDepthLogClock_apply, xiGammaEulerPrimitivePrimeDepthLogClock_apply]
      norm_num
      ring]
  apply Real.tendsto_exp_atTop.comp
  exact tendsto_natCast_atTop_atTop.const_mul_atTop
    (mul_pos ha (Real.log_pos (by norm_num)))

theorem not_eulerPrimitiveReflectedOffDiagonalHolonomyUniformlyBounded_of_pos {a : ℂ} (ha : 0 < a.re) :
    ¬ EulerPrimitiveReflectedOffDiagonalHolonomyUniformlyBounded a := by
  rintro ⟨C, hC⟩
  have hev := (tendsto_norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_two_depth_atTop ha).eventually_gt_atTop C
  obtain ⟨e, he⟩ := hev.exists
  exact (not_lt_of_ge (hC _ _) he)

theorem not_eulerPrimitiveReflectedOffDiagonalHolonomyUniformlyBounded_of_neg {a : ℂ} (ha : a.re < 0) :
    ¬ EulerPrimitiveReflectedOffDiagonalHolonomyUniformlyBounded a := by
  rintro ⟨C, hC⟩
  have hpos : 0 < (-a).re := by simp [ha]
  have hev := (tendsto_norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_two_depth_atTop hpos).eventually_gt_atTop C
  obtain ⟨e, he⟩ := hev.exists
  have hnorm : ‖xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy (-a) (⟨2, Nat.prime_two⟩, 0)
      (⟨2, Nat.prime_two⟩, e)‖ =
      ‖xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a (⟨2, Nat.prime_two⟩, e)
        (⟨2, Nat.prime_two⟩, 0)‖ := by
    rw [norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy]
    simp
    ring
  rw [hnorm] at he
  exact (not_lt_of_ge (hC _ _) he)

theorem eulerPrimitiveReflectedOffDiagonalHolonomyUniformlyBounded_iff (a : ℂ) :
    EulerPrimitiveReflectedOffDiagonalHolonomyUniformlyBounded a ↔ a.re = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy a.re 0 with hneg | hzero | hpos
    · exact False.elim (not_eulerPrimitiveReflectedOffDiagonalHolonomyUniformlyBounded_of_neg hneg h)
    · exact hzero
    · exact False.elim (not_eulerPrimitiveReflectedOffDiagonalHolonomyUniformlyBounded_of_pos hpos h)
  · intro h
    refine ⟨1, fun i j => ?_⟩
    rw [norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy, h]
    simp

def XiGammaEulerPrimitiveReflectedOffDiagonalHolonomyUniformCapacity : Prop :=
  ∃ C : ℝ, ∀ rho : XiDivisorSupport,
    ∀ i j : Nat.Primes × ℕ,
      ‖xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy ((rho : ℂ) - 1 / 2) i j‖ ≤ C

theorem xiGammaEulerPrimitiveReflectedOffDiagonalHolonomyUniformCapacity_iff_riemannHypothesis :
    XiGammaEulerPrimitiveReflectedOffDiagonalHolonomyUniformCapacity ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨C, hC⟩
    rw [rh_iff_xi_ne_zero_right]
    intro z hz hzero
    have hmem := mem_xi_divisor_support_of_eq_zero hzero
    let rho : XiDivisorSupport := ⟨z, hmem⟩
    have hbounded : EulerPrimitiveReflectedOffDiagonalHolonomyUniformlyBounded (z - 1 / 2) :=
      ⟨C, fun i j => hC rho i j⟩
    have hre := (eulerPrimitiveReflectedOffDiagonalHolonomyUniformlyBounded_iff (z - 1 / 2)).mp hbounded
    have hre' : z.re - 1 / 2 = 0 := by
      simpa using hre
    have hzre : z.re = 1 / 2 := by
      linarith
    exact (ne_of_gt (mem_rightHalf.mp hz)) hzre
  · intro hRH
    refine ⟨1, fun rho i j => ?_⟩
    have hre := xi_divisor_support_re_eq_half_of_rh hRH rho
    rw [norm_xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy]
    have ha : ((rho : ℂ) - 1 / 2).re = 0 := by
      simp [hre]
    rw [ha]
    simp

end
end RHTower
