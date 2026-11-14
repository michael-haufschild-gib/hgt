import GaloisForLFunctions.HTGeometry.CPVThermalRadiation
import GaloisForLFunctions.HTGeometry.CPVPrimeOccupation

/-!
# The thermal radiation pair is a Bogoliubov vacuum

On occupation coefficients, annihilation shifts a level down with coefficient
`sqrt (n + 1)` and creation shifts it up with coefficient `sqrt n`. The existing
normalized radiation pair obeys the two squeezed-vacuum equations. Thus the
thermal state in the corpus is annihilated by operators mixing the two copies,
as in equations (2.8)--(2.9) of Maldacena, arXiv:hep-th/0106112.

The operators below act on coefficient sequences. No assertion that an
unbounded oscillator operator acts everywhere on Hilbert space is needed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Thermofield

open CPV

/-- Left-mode annihilation in the normalized occupation basis. -/
def annihilateLeft (ψ : ℕ × ℕ → ℂ) (p : ℕ × ℕ) : ℂ :=
  (Real.sqrt (p.1 + 1 : ℝ) : ℂ) * ψ (p.1 + 1, p.2)

/-- Right-mode creation, with the vacuum boundary built into the definition. -/
def createRight (ψ : ℕ × ℕ → ℂ) : ℕ × ℕ → ℂ
  | (m, 0) => 0
  | (m, n + 1) => (Real.sqrt (n + 1 : ℝ) : ℂ) * ψ (m, n)

def annihilateRight (ψ : ℕ × ℕ → ℂ) (p : ℕ × ℕ) : ℂ :=
  (Real.sqrt (p.2 + 1 : ℝ) : ℂ) * ψ (p.1, p.2 + 1)

def createLeft (ψ : ℕ × ℕ → ℂ) : ℕ × ℕ → ℂ
  | (0, n) => 0
  | (m + 1, n) => (Real.sqrt (m + 1 : ℝ) : ℂ) * ψ (m, n)

/-- Successive Schmidt amplitudes have ratio `exp (-βω/2)`. -/
theorem radiationVector_successor (τ : ℝ) (n : ℕ) :
    radiationVector τ (n + 1) =
      (Real.sqrt (thermalRatio τ) : ℂ) * radiationVector τ n := by
  rw [radiationVector_apply, radiationMass_successor]
  rw [Real.sqrt_mul (thermalRatio_pos τ).le]
  simp only [radiationVector_apply, Complex.ofReal_mul, thermalRatio]

/-- Annihilating one partner is equivalent to creating the other. -/
theorem radiationPair_annihilate_left (τ : ℝ) :
    annihilateLeft (radiationPair τ) =
      fun p => (Real.sqrt (thermalRatio τ) : ℂ) * createRight (radiationPair τ) p := by
  funext p
  rcases p with ⟨m, n⟩
  cases n with
  | zero => simp [annihilateLeft, createRight, radiationPair, thermofieldDiagonalKernel]
  | succ n =>
    by_cases h : m = n
    · subst n
      simp only [annihilateLeft, createRight, radiationPair, thermofieldDiagonalKernel,
        if_true]
      rw [radiationVector_successor]
      ring
    · simp [annihilateLeft, createRight, radiationPair, thermofieldDiagonalKernel, h]

theorem radiationPair_annihilate_right (τ : ℝ) :
    annihilateRight (radiationPair τ) =
      fun p => (Real.sqrt (thermalRatio τ) : ℂ) * createLeft (radiationPair τ) p := by
  funext p
  rcases p with ⟨m, n⟩
  cases m with
  | zero => simp [annihilateRight, createLeft, radiationPair, thermofieldDiagonalKernel]
  | succ m =>
    by_cases h : m = n
    · subst n
      simp only [annihilateRight, createLeft, radiationPair, thermofieldDiagonalKernel,
        if_true]
      rw [radiationVector_successor]
      ring
    · simp [annihilateRight, createLeft, radiationPair, thermofieldDiagonalKernel, h]

/-- Canonical normalization of the mixed annihilation operator. -/
def squeezeGain (τ : ℝ) : ℝ := (Real.sqrt (1 - thermalRatio τ))⁻¹

def squeezeMix (τ : ℝ) : ℝ :=
  squeezeGain τ * Real.sqrt (thermalRatio τ)

/-- The coefficients preserve the oscillator commutator. -/
theorem squeezeGain_sq_sub_squeezeMix_sq (τ : ℝ) :
    squeezeGain τ ^ 2 - squeezeMix τ ^ 2 = 1 := by
  have hq : 0 < 1 - thermalRatio τ := sub_pos.mpr (thermalRatio_lt_one τ)
  rw [squeezeMix, mul_pow, Real.sq_sqrt (thermalRatio_pos τ).le,
    squeezeGain, inv_pow, Real.sq_sqrt hq.le]
  field_simp [hq.ne']
  ring

def bogoliubovLeft (τ : ℝ) (ψ : ℕ × ℕ → ℂ) (p : ℕ × ℕ) : ℂ :=
  (squeezeGain τ : ℂ) * annihilateLeft ψ p -
    (squeezeMix τ : ℂ) * createRight ψ p

def bogoliubovRight (τ : ℝ) (ψ : ℕ × ℕ → ℂ) (p : ℕ × ℕ) : ℂ :=
  (squeezeGain τ : ℂ) * annihilateRight ψ p -
    (squeezeMix τ : ℂ) * createLeft ψ p

/-- The existing infinite-dimensional thermal pair is a vacuum for both mixed modes. -/
theorem radiationPair_bogoliubov_vacuum (τ : ℝ) :
    bogoliubovLeft τ (radiationPair τ) = 0 ∧
      bogoliubovRight τ (radiationPair τ) = 0 := by
  constructor
  · funext p
    simp only [bogoliubovLeft, radiationPair_annihilate_left, squeezeMix,
      Complex.ofReal_mul, Pi.zero_apply]
    ring
  · funext p
    simp only [bogoliubovRight, radiationPair_annihilate_right, squeezeMix,
      Complex.ofReal_mul, Pi.zero_apply]
    ring

private theorem annihilateLeft_row_normSq (τ : ℝ) (m : ℕ) :
    (∑' n, ‖annihilateLeft (radiationPair τ) (m, n)‖ ^ 2) =
      ((m + 1 : ℕ) : ℝ) * radiationMass τ (m + 1) := by
  rw [tsum_eq_single (m + 1)]
  · simp only [annihilateLeft, radiationPair, thermofieldDiagonalKernel, if_true,
      radiationVector_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Nat.cast_add, Nat.cast_one]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (radiationMass_pos τ _).le]
  · intro n hn
    simp [annihilateLeft, radiationPair, thermofieldDiagonalKernel, Ne.symm hn]

/-- The thermal pair belongs to the actual square-summable domain of annihilation. -/
theorem radiationPair_annihilate_isHS (τ : ℝ) :
    HilbertSchmidt.IsHS (annihilateLeft (radiationPair τ)) := by
  rw [HilbertSchmidt.IsHS, summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · intro m
    apply summable_of_ne_finset_zero (s := {m + 1})
    intro n hn
    have hnm : n ≠ m + 1 := by simpa using hn
    simp [annihilateLeft, radiationPair, thermofieldDiagonalKernel, Ne.symm hnm]
  · simpa only [annihilateLeft_row_normSq] using
      (summable_nat_add_iff 1).mpr (radiationMass_mean τ).summable

/-- The norm of the annihilated state is the thermal mean occupation. -/
theorem radiationPair_annihilate_normSq (τ : ℝ) :
    HilbertSchmidt.hsNormSq (annihilateLeft (radiationPair τ)) =
      ∑' n : ℕ, (n : ℝ) * radiationMass τ n := by
  rw [HilbertSchmidt.hsNormSq, (radiationPair_annihilate_isHS τ).tsum_prod]
  simp only [annihilateLeft_row_normSq]
  have h := (radiationMass_mean τ).summable.tsum_eq_zero_add
  simpa only [Nat.cast_zero, zero_mul, zero_add] using h.symm

/-- The excitation norm is the Bose occupation number, with convergence already proved. -/
theorem radiationPair_annihilate_bose_norm (τ : ℝ) :
    HilbertSchmidt.hsNormSq (annihilateLeft (radiationPair τ)) =
      1 / (Real.exp (Real.exp τ) - 1) := by
  rw [radiationPair_annihilate_normSq, radiationMass_bose_mean]

/-- The left creation and annihilation operators satisfy the actual CCR on coefficients. -/
theorem left_commutator (ψ : ℕ × ℕ → ℂ) :
    annihilateLeft (createLeft ψ) - createLeft (annihilateLeft ψ) = ψ := by
  funext p
  rcases p with ⟨m, n⟩
  cases m with
  | zero => simp [annihilateLeft, createLeft]
  | succ m =>
    simp only [Pi.sub_apply, annihilateLeft, createLeft]
    simp only [← mul_assoc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity : 0 ≤ (m + 1 : ℝ)),
      Real.mul_self_sqrt (by positivity : 0 ≤ ((m + 1 : ℕ) + 1 : ℝ))]
    push_cast
    ring

/-- Opposite annihilators commute on every coefficient sequence. -/
theorem annihilators_commute (ψ : ℕ × ℕ → ℂ) :
    annihilateLeft (annihilateRight ψ) = annihilateRight (annihilateLeft ψ) := by
  funext p
  simp only [annihilateLeft, annihilateRight]
  ring

/-- Opposite creation and annihilation commute, including the vacuum boundary. -/
theorem left_annihilate_right_create_commute (ψ : ℕ × ℕ → ℂ) :
    annihilateLeft (createRight ψ) = createRight (annihilateLeft ψ) := by
  funext p
  rcases p with ⟨m, n⟩
  cases n <;> simp [annihilateLeft, createRight, mul_left_comm]

/-- Prime occupation states inherit the squeezed-vacuum equations at their
already constructed thermal coordinate. -/
theorem primeRadiation_bogoliubov_vacuum (p : Nat.Primes) :
    bogoliubovLeft (primeThermalCoordinate p)
        (radiationPair (primeThermalCoordinate p)) = 0 ∧
      bogoliubovRight (primeThermalCoordinate p)
        (radiationPair (primeThermalCoordinate p)) = 0 :=
  radiationPair_bogoliubov_vacuum _

/-- The prime occupation law gives the exact excitation norm `1 / (p - 1)`. -/
theorem primeRadiation_annihilate_norm (p : Nat.Primes) :
    HilbertSchmidt.hsNormSq
        (annihilateLeft (radiationPair (primeThermalCoordinate p))) =
      1 / ((p : ℝ) - 1) := by
  rw [radiationPair_annihilate_normSq, primeRadiation_mean]

end GaloisForLFunctions.HTGeometry.Thermofield
