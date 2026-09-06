import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Mixed Euler-deletion refinement with the full cell correction

Pair the centered deletion prefix with the ordinary Dirichlet weight. Subdivision into
`p`-cells gives an exact dilation law with the within-cell weight variation retained.
The outer cutoff must be `p * N`, while the inserted source has cutoff `N`.

The correction satisfies an exact weighted cocycle law at matched finite cutoffs.
The centering value `Z` is arbitrary; choosing `Z = zeta(s)` gives the literal centered
Euler-deletion source. No vanishing of a correction or equality with replication is asserted.
-/

noncomputable section
open scoped BigOperators

namespace RHTower.DeletionMixedRefinement

/-- Ordinary positive-integer Dirichlet weight, extended to the natural index type. -/
def kernel (s : ℂ) (n : ℕ) : ℂ := (n : ℂ) ^ (-s)

/-- Literal Euler insertion amplitude. -/
def amplitude (s : ℂ) (p : ℕ) : ℂ := (p : ℂ) * kernel s p

/-- Unregularized sum through the integer cutoff. -/
def rawPrefix (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, kernel s (n + 1)

/-- Deletion prefix with its prescribed Euler-factor endpoint subtracted. -/
def centeredTail (s Z : ℂ) (p N : ℕ) : ℂ :=
  rawPrefix s N - amplitude s p * rawPrefix s (N / p) - (1 - amplitude s p) * Z

/-- Strict mixed prefix: centered deletion against the ordinary conjugate weight. -/
def mixedPrefix (s Z : ℂ) (p N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, centeredTail s Z p k * star (kernel s (k + 1))

/-- Full within-cell correction, including every weight before the cell endpoint. -/
def cellCorrection (s Z : ℂ) (p q N : ℕ) : ℂ :=
  amplitude s p * ∑ k ∈ Finset.range N, centeredTail s Z q k *
    ((∑ r ∈ Finset.range p, star (kernel s (p * k + r + 1))) -
      (p : ℂ) * star (kernel s (p * (k + 1))))

/-- The actual Dirichlet weight preserves multiplication of nonnegative integer indices. -/
theorem kernel_mul (s : ℂ) (p q : ℕ) :
    kernel s (p * q) = kernel s p * kernel s q := by
  simpa [kernel, Nat.cast_mul] using
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q) (-s)

/-- Euler insertion amplitudes compose multiplicatively. -/
theorem amplitude_mul (s : ℂ) (p q : ℕ) :
    amplitude s (p * q) = amplitude s p * amplitude s q := by
  simp only [amplitude, kernel_mul, Nat.cast_mul]
  ring

/-- Composite centered deletion retains the inserted prefix at its floor-divided cutoff. -/
theorem centeredTail_mul (s Z : ℂ) (p q N : ℕ) :
    centeredTail s Z (p * q) N =
      centeredTail s Z p N + amplitude s p * centeredTail s Z q (N / p) := by
  simp only [centeredTail, amplitude_mul, Nat.div_div_eq_div_mul]
  ring

private theorem sum_blocks (p N : ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.range (p * N), f n =
      ∑ k ∈ Finset.range N, ∑ r ∈ Finset.range p, f (p * k + r) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Complete arithmetic cells give the literal mixed insertion sum. -/
theorem mixedPrefix_mul_cells (s Z : ℂ) {p : ℕ} (hp : 0 < p) (q N : ℕ) :
    mixedPrefix s Z (p * q) (p * N) = mixedPrefix s Z p (p * N) +
      amplitude s p * ∑ k ∈ Finset.range N, centeredTail s Z q k *
        ∑ r ∈ Finset.range p, star (kernel s (p * k + r + 1)) := by
  calc
    _ = mixedPrefix s Z p (p * N) +
        ∑ n ∈ Finset.range (p * N),
          (amplitude s p * centeredTail s Z q (n / p)) * star (kernel s (n + 1)) := by
      simp only [mixedPrefix, centeredTail_mul, add_mul, Finset.sum_add_distrib]
    _ = mixedPrefix s Z p (p * N) + amplitude s p *
        ∑ n ∈ Finset.range (p * N),
          centeredTail s Z q (n / p) * star (kernel s (n + 1)) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = mixedPrefix s Z p (p * N) + amplitude s p *
        ∑ k ∈ Finset.range N, ∑ r ∈ Finset.range p,
          centeredTail s Z q ((p * k + r) / p) *
            star (kernel s (p * k + r + 1)) := by rw [sum_blocks]
    _ = _ := by
      congr 2
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Nat.mul_add_div hp, Nat.div_eq_of_lt (Finset.mem_range.mp hr), Nat.add_zero]

/-- The cell correction is the full cell sum minus its endpoint-dilation contribution. -/
theorem cellCorrection_eq (s Z : ℂ) (p q N : ℕ) :
    cellCorrection s Z p q N =
      amplitude s p * (∑ k ∈ Finset.range N, centeredTail s Z q k *
        ∑ r ∈ Finset.range p, star (kernel s (p * k + r + 1))) -
      (amplitude s p * star (amplitude s p)) * mixedPrefix s Z q N := by
  simp only [cellCorrection, mul_sub, Finset.sum_sub_distrib]
  congr 1
  simp only [mixedPrefix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [kernel_mul, amplitude, star_mul, star_natCast]
  ring

/-- Exact finite mixed refinement: squared Euler amplitude plus the retained cell correction. -/
theorem mixedPrefix_mul (s Z : ℂ) {p : ℕ} (hp : 0 < p) (q N : ℕ) :
    mixedPrefix s Z (p * q) (p * N) = mixedPrefix s Z p (p * N) +
      (amplitude s p * star (amplitude s p)) * mixedPrefix s Z q N +
      cellCorrection s Z p q N := by
  rw [mixedPrefix_mul_cells s Z hp, cellCorrection_eq]
  ring

/-- The mixed refinement multiplier is precisely the squared Euler amplitude. -/
theorem amplitude_mul_star (s : ℂ) (p : ℕ) :
    amplitude s p * star (amplitude s p) = (Complex.normSq (amplitude s p) : ℂ) := by
  exact Complex.mul_conj _

/-- Three arithmetic refinements conserve the full correction with its squared-amplitude weight
and its required rescaling of the finite cutoffs. -/
theorem cellCorrection_cocycle (s Z : ℂ) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (r N : ℕ) :
    cellCorrection s Z p q (q * N) + cellCorrection s Z (p * q) r N =
      (amplitude s p * star (amplitude s p)) * cellCorrection s Z q r N +
        cellCorrection s Z p (q * r) (q * N) := by
  have hleft := mixedPrefix_mul s Z (Nat.mul_pos hp hq) r N
  have hright := mixedPrefix_mul s Z hp (q * r) (q * N)
  rw [Nat.mul_assoc, Nat.mul_assoc,
    mixedPrefix_mul s Z hp q (q * N), amplitude_mul, star_mul] at hleft
  rw [mixedPrefix_mul s Z hq r N] at hright
  linear_combination hright - hleft


/-- Strict ordinary mixed prefix with a fixed centering value. -/
def ordinaryMixedPrefix (s Z : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, (rawPrefix s k - Z) * star (kernel s (k + 1))

/-- Ordinary source paired with the endpoint of its dilated block. -/
def dilationEndpointPairing (s : ℂ) (p N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, kernel s (k + 1) * star (rawPrefix s (p * (k + 1)))

private theorem rawPrefix_succ (s : ℂ) (N : ℕ) :
    rawPrefix s (N + 1) = rawPrefix s N + kernel s (N + 1) := by
  exact Finset.sum_range_succ _ _

private theorem rawPrefix_block (s : ℂ) (p N : ℕ) :
    (∑ r ∈ Finset.range p, star (kernel s (p * N + r + 1))) =
      star (rawPrefix s (p * (N + 1))) - star (rawPrefix s (p * N)) := by
  rw [Nat.mul_succ, rawPrefix, Finset.sum_range_add]
  simp [rawPrefix]

/-- Finite summation by parts keeps the terminal ordinary-source product. -/
theorem centeredBlockSum_eq_endpoint_sub_pairing (s Z : ℂ) (p N : ℕ) :
    (∑ k ∈ Finset.range N, (rawPrefix s k - Z) *
      ∑ r ∈ Finset.range p, star (kernel s (p * k + r + 1))) =
      (rawPrefix s N - Z) * star (rawPrefix s (p * N)) -
        dilationEndpointPairing s p N := by
  induction N with
  | zero => simp [rawPrefix, dilationEndpointPairing]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, rawPrefix_block, rawPrefix_succ]
      simp only [dilationEndpointPairing, Finset.sum_range_succ]
      ring

/-- Exact ordinary-source decomposition of the mixed deletion prefix. -/
theorem mixedPrefix_eq_ordinary_endpoint_pairing (s Z : ℂ) {p : ℕ}
    (hp : 0 < p) (N : ℕ) :
    mixedPrefix s Z p (p * N) = ordinaryMixedPrefix s Z (p * N) -
      amplitude s p * (rawPrefix s N - Z) * star (rawPrefix s (p * N)) +
        amplitude s p * dilationEndpointPairing s p N := by
  have hsplit (k : ℕ) : centeredTail s Z p k =
      (rawPrefix s k - Z) - amplitude s p * (rawPrefix s (k / p) - Z) := by
    simp only [centeredTail]
    ring
  have hblocks :
      (∑ k ∈ Finset.range (p * N),
        (rawPrefix s (k / p) - Z) * star (kernel s (k + 1))) =
      ∑ k ∈ Finset.range N, (rawPrefix s k - Z) *
        ∑ r ∈ Finset.range p, star (kernel s (p * k + r + 1)) := by
    rw [sum_blocks]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Nat.mul_add_div hp, Nat.div_eq_of_lt (Finset.mem_range.mp hr), Nat.add_zero]
  calc
    _ = ordinaryMixedPrefix s Z (p * N) - amplitude s p *
        ∑ k ∈ Finset.range (p * N),
          (rawPrefix s (k / p) - Z) * star (kernel s (k + 1)) := by
      simp only [mixedPrefix, hsplit, sub_mul, Finset.sum_sub_distrib,
        ordinaryMixedPrefix, mul_assoc]
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by
      rw [hblocks, centeredBlockSum_eq_endpoint_sub_pairing]
      ring

/-- The centered ordinary prefix has an exact quadratic endpoint law. -/
theorem ordinaryMixedPrefix_quadratic_identity (s Z : ℂ) (N : ℕ) :
    Complex.normSq (rawPrefix s N - Z) = Complex.normSq Z +
      (∑ k ∈ Finset.range N, Complex.normSq (kernel s (k + 1))) +
        2 * (ordinaryMixedPrefix s Z N).re := by
  induction N with
  | zero => simp [rawPrefix, ordinaryMixedPrefix]
  | succ N ih =>
      rw [rawPrefix_succ, show rawPrefix s N + kernel s (N + 1) - Z =
        (rawPrefix s N - Z) + kernel s (N + 1) by ring, Complex.normSq_add, ih]
      have ho : ordinaryMixedPrefix s Z (N + 1) = ordinaryMixedPrefix s Z N +
          (rawPrefix s N - Z) * star (kernel s (N + 1)) := by
        exact Finset.sum_range_succ _ _
      rw [ho, Finset.sum_range_succ, Complex.add_re]
      change Complex.normSq Z +
          (∑ k ∈ Finset.range N, Complex.normSq (kernel s (k + 1))) +
          2 * (ordinaryMixedPrefix s Z N).re + Complex.normSq (kernel s (N + 1)) +
          2 * ((rawPrefix s N - Z) * star (kernel s (N + 1))).re = _
      ring

end RHTower.DeletionMixedRefinement
