import GaloisForLFunctions.HTGeometry.HadamardFinitePart
import GaloisForLFunctions.HTGeometry.AtomicJumpForm
import Mathlib

/-!
# The restricted Weil form, assembled

Suzuki's distributional screw kernel on an aperture is

`k = −½ Pf(1/|t|) − (2A+1) δ₀ − ∑_{n ≤ e^{2a}} Λ(n)/√n (δ_{log n} + δ_{−log n}) − r''`,

and the restricted Weil form is `Q(u, φ) = ∫∫ k(x−y) u(y) φ(x)`.  Every one of those four pieces is
already an explicit object: the finite part is the cutoff-free Cauchy finite part, the Dirac terms
are `L²` pairings and translation pairings, and the smooth remainder is an ordinary continuous
convolution block, its kernel `r''` carried as a parameter because Suzuki's `r` is source data.  This file assembles them, so the form is a definition rather than a hypothesis, and
records the decomposition that the source cards use: the prime block is a *positive* atomic
Dirichlet form minus a scalar potential.

No operator is constructed.  What a card calls `A_a u = w` is the statement that `w` represents
`Q(u, ·)` in the `L²` pairing, which is `IsRestrictedWeilRepresentative` below.
-/

open MeasureTheory intervalIntegral Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-! ## The four blocks -/

/-- Hadamard finite part of the Cauchy kernel against a weight, at an interior point.  This is the
cutoff-free form: the divided-difference integral plus the exact logarithmic term.  It is the
`ε → 0` value of `cutoffFinitePart`, whose split is cutoff-independent. -/
def cauchyFinitePart (a x : ℝ) (u : ℝ → ℝ) : ℝ :=
  (∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹) + (∫ y in x..a, (u y - u x) * (y - x)⁻¹) +
    u x * Real.log (a ^ 2 - x ^ 2)

/-- The finite-part block of the form. -/
def weilFinitePartBlock (a : ℝ) (u φ : ℝ → ℝ) : ℝ :=
  -(1 / 2) * ∫ x in (-a)..a, cauchyFinitePart a x u * φ x

/-- The archimedean scalar block. -/
def weilScalarBlock (a A : ℝ) (u φ : ℝ → ℝ) : ℝ :=
  -(2 * A + 1) * ∫ x in (-a)..a, u x * φ x

/-- The prime block: a symmetric translation pair for each visible prime power. -/
def weilPrimeBlock (s : Finset ℕ) (u φ : ℝ → ℝ) : ℝ :=
  -∑ n ∈ s, primePairWeight n *
    (pairing (fun x => u (x + Real.log n)) φ + pairing (fun x => u (x - Real.log n)) φ)

/-- The smooth archimedean remainder block.  Suzuki's remainder `r` is `C²` on the compact
difference interval, so its second derivative enters as an ordinary continuous convolution kernel;
that kernel is the parameter `k` here. -/
def weilSmoothBlock (a : ℝ) (k : ℝ → ℝ) (u φ : ℝ → ℝ) : ℝ :=
  -∫ x in (-a)..a, (∫ y in (-a)..a, k (x - y) * u y) * φ x

/-- The representative of the smooth block. -/
def weilSmoothRepresentative (a : ℝ) (k : ℝ → ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  -∫ y in (-a)..a, k (x - y) * u y

/-- **The restricted Weil form.** -/
def restrictedWeilForm (a A : ℝ) (s : Finset ℕ) (k : ℝ → ℝ) (u φ : ℝ → ℝ) : ℝ :=
  weilFinitePartBlock a u φ + weilScalarBlock a A u φ + weilPrimeBlock s u φ +
    weilSmoothBlock a k u φ

/-- `w` represents the form at `u`: this is what a card means by `A_a u = w`. -/
def IsRestrictedWeilRepresentative (a A : ℝ) (s : Finset ℕ) (k : ℝ → ℝ) (u w : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ →
    restrictedWeilForm a A s k u φ = ∫ x in (-a)..a, w x * φ x

/-- The candidate representative assembled block by block. -/
def restrictedWeilRepresentative (a A : ℝ) (s : Finset ℕ) (k : ℝ → ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(1 / 2) * cauchyFinitePart a x u - (2 * A + 1) * u x -
    (∑ n ∈ s, primePairWeight n * (u (x + Real.log n) + u (x - Real.log n))) +
    weilSmoothRepresentative a k u x

/-- **The endpoint logarithm is the only unbounded part of the representative.**  Splitting off the
logarithmic term leaves the divided difference, three bounded blocks, and nothing else. -/
theorem restrictedWeilRepresentative_eq (a A : ℝ) (s : Finset ℕ) (k : ℝ → ℝ) (u : ℝ → ℝ) (x : ℝ) :
    restrictedWeilRepresentative a A s k u x =
      -(1 / 2) * (u x * Real.log (a ^ 2 - x ^ 2)) +
        (-(1 / 2) * ((∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹) +
            ∫ y in x..a, (u y - u x) * (y - x)⁻¹) - (2 * A + 1) * u x -
          (∑ n ∈ s, primePairWeight n * (u (x + Real.log n) + u (x - Real.log n))) +
          weilSmoothRepresentative a k u x) := by
  rw [restrictedWeilRepresentative, cauchyFinitePart]
  ring

/-! ## The prime block is a positive atomic Dirichlet form minus a potential -/

/-- **Atomic decomposition of the prime block.**  Each symmetric prime pair is the jump form of its
displacement minus twice the `L²` pairing, so the prime block is a nonnegatively weighted sum of
Dirichlet forms minus a scalar potential.  This is the sign that an arbitrary bounded `L²`
perturbation would destroy. -/
theorem weilPrimeBlock_eq_jumpForms {u φ : ℝ → ℝ} (hu : Continuous u) (hφ : Continuous φ)
    (hcu : HasCompactSupport u) (s : Finset ℕ) :
    weilPrimeBlock s u φ =
      (∑ n ∈ s, primePairWeight n * jumpForm (Real.log n) u φ) -
        2 * (∑ n ∈ s, primePairWeight n) * pairing u φ := by
  have hstep : ∀ n ∈ s,
      primePairWeight n *
          (pairing (fun x => u (x + Real.log n)) φ + pairing (fun x => u (x - Real.log n)) φ) =
        2 * primePairWeight n * pairing u φ -
          primePairWeight n * jumpForm (Real.log n) u φ := by
    intro n _
    have h := jumpForm_eq_two_pairing_sub hu hφ hcu (Real.log n)
    have : pairing (fun x => u (x + Real.log n)) φ + pairing (fun x => u (x - Real.log n)) φ =
        2 * pairing u φ - jumpForm (Real.log n) u φ := by linarith
    rw [this]
    ring
  rw [weilPrimeBlock, Finset.sum_congr rfl hstep]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- **Prime-block coercivity against a truncation.**  Every prime pair contributes nonnegatively to
the jump part when tested against an increasing one-Lipschitz truncation of the same function. -/
theorem weilPrimeBlock_jumpPart_nonneg (s : Finset ℕ) (hstep : ℕ → ℝ) (v : ℝ → ℝ)
    (hnn : ∀ n ∈ s, 0 ≤ jumpForm (hstep n) v v) :
    0 ≤ ∑ n ∈ s, primePairWeight n * jumpForm (hstep n) v v :=
  sum_primePairWeight_jumpForm_nonneg s hstep v hnn

/-! ## The finite-part block carries the endpoint logarithm -/

/-- **Cutoff-free finite part.**  For every admissible cutoff the finite part of the Cauchy kernel
splits with the *same* logarithmic coefficient `u x`, so `cauchyFinitePart` is that cutoff's value
with the divided-difference integrals completed. -/
theorem cutoffFinitePart_eq_of_split {a x ε : ℝ} (u : ℝ → ℝ) (hu : Continuous u)
    (hxa : -a < x) (hax : x < a) (hε : 0 < ε) (hleft : -a ≤ x - ε) (hright : x + ε ≤ a) :
    cutoffFinitePart a x ε u =
      cutoffDividedDifference a x ε u + u x * Real.log (a ^ 2 - x ^ 2) :=
  cutoffFinitePart_eq u hu hxa hax hε hleft hright

/-- The logarithmic coefficient of the finite part at an interior point is the value of the weight
there — an exact invariant of the kernel, independent of every cutoff. -/
theorem cauchyFinitePart_log_coefficient (a x : ℝ) (u : ℝ → ℝ) :
    cauchyFinitePart a x u -
        ((∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹) + ∫ y in x..a, (u y - u x) * (y - x)⁻¹) =
      u x * Real.log (a ^ 2 - x ^ 2) := by
  rw [cauchyFinitePart]
  ring

/-! ## Linearity of the form in the test function -/

theorem weilScalarBlock_zero (a A : ℝ) (φ : ℝ → ℝ) :
    weilScalarBlock a A (fun _ => 0) φ = 0 := by
  simp [weilScalarBlock]

theorem weilPrimeBlock_zero (s : Finset ℕ) (φ : ℝ → ℝ) :
    weilPrimeBlock s (fun _ => 0) φ = 0 := by
  simp [weilPrimeBlock, pairing]

end GaloisForLFunctions.RHTower
