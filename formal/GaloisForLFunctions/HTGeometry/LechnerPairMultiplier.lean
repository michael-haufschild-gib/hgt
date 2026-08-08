import GaloisForLFunctions.HTGeometry.KolchinExchangeGaugeObstruction
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The Lechner pair multiplier

The intertwiner between an `S`-permutation representation and a constant Bose/Fermi one is the
product of an elementary half-phase over all pairs,

`Y_n (theta) = prod_(k < l < n) y (theta_k - theta_l)`.

Two facts carry its use.

* `pairMultiplier_shift` -- adjoining a new **first** particle multiplies the whole product by the
  string `prod_(j < n) y (theta_0 - theta_(j+1))` and leaves the rest untouched.  This is the
  recursion behind the conjugated creation operator: the pair phases split into those meeting the
  new particle and those internal to the old ones.
* `norm_pairMultiplier` -- a unimodular half-phase gives a unimodular multiplier, so the
  intertwiner is unitary at every particle number.

In the two-particle relative coordinate the multiplier is the elementary factor itself, and the
swap ratio reproduces the exchange law: `S = epsilon * y / (y . neg)`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- The pair multiplier of a half-phase over the first `n` rapidities. -/
noncomputable def pairMultiplier (y : ℝ → ℂ) (θ : ℕ → ℝ) (n : ℕ) : ℂ :=
  ∏ l ∈ Finset.range n, ∏ k ∈ Finset.range l, y (θ k - θ l)

@[simp]
theorem pairMultiplier_zero (y : ℝ → ℂ) (θ : ℕ → ℝ) : pairMultiplier y θ 0 = 1 := by
  rw [pairMultiplier, Finset.prod_range_zero]

@[simp]
theorem pairMultiplier_one (y : ℝ → ℂ) (θ : ℕ → ℝ) : pairMultiplier y θ 1 = 1 := by
  rw [pairMultiplier, Finset.prod_range_one, Finset.prod_range_zero]

theorem pairMultiplier_two (y : ℝ → ℂ) (θ : ℕ → ℝ) :
    pairMultiplier y θ 2 = y (θ 0 - θ 1) := by
  rw [pairMultiplier, Finset.prod_range_succ, Finset.prod_range_one, Finset.prod_range_zero,
    Finset.prod_range_one, one_mul]

/-- Adjoining a new last particle multiplies by its pair string. -/
theorem pairMultiplier_succ (y : ℝ → ℂ) (θ : ℕ → ℝ) (n : ℕ) :
    pairMultiplier y θ (n + 1)
      = pairMultiplier y θ n * ∏ k ∈ Finset.range n, y (θ k - θ n) := by
  rw [pairMultiplier, pairMultiplier, Finset.prod_range_succ]

/-- **The creation recursion.**  Adjoining a new *first* particle multiplies the pair multiplier by
the string of its phases against all the others, leaving the shifted multiplier untouched. -/
theorem pairMultiplier_shift (y : ℝ → ℂ) (θ : ℕ → ℝ) (n : ℕ) :
    pairMultiplier y θ (n + 1)
      = (∏ j ∈ Finset.range n, y (θ 0 - θ (j + 1)))
        * pairMultiplier y (fun k => θ (k + 1)) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pairMultiplier_succ y θ (n + 1), ih, pairMultiplier_succ y (fun k => θ (k + 1)) n,
        Finset.prod_range_succ' (fun k => y (θ k - θ (n + 1))) n,
        Finset.prod_range_succ (fun j => y (θ 0 - θ (j + 1))) n]
      ring

/-- **Unitarity.**  A unimodular half-phase gives a unimodular multiplier. -/
theorem norm_pairMultiplier (y : ℝ → ℂ) (hy : ∀ t : ℝ, ‖y t‖ = 1) (θ : ℕ → ℝ) (n : ℕ) :
    ‖pairMultiplier y θ n‖ = 1 := by
  rw [pairMultiplier, norm_prod]
  refine Finset.prod_eq_one fun l _ => ?_
  rw [norm_prod]
  exact Finset.prod_eq_one fun k _ => hy _

/-- **The exchange law from the swap ratio.**  In the two-particle relative coordinate the pair
multiplier is the elementary half-phase, so the ratio of the two orderings reproduces the exchange
cocycle. -/
theorem exchangeLaw_of_pairMultiplier_swap {y : ℝ → ℂ} {S : ℝ → ℂ} {ε : ℂ}
    (hS : ∀ t : ℝ, S t = ε * (y t / y (-t))) (θ : ℕ → ℝ) :
    S (θ 0 - θ 1)
      = ε * (pairMultiplier y θ 2 / pairMultiplier y (fun k => θ (1 - k)) 2) := by
  rw [pairMultiplier_two, pairMultiplier_two, hS]
  norm_num

theorem pairMultiplier_ne_zero {y : ℝ → ℂ} (hy : ∀ t : ℝ, ‖y t‖ = 1) (θ : ℕ → ℝ) (n : ℕ) :
    pairMultiplier y θ n ≠ 0 := by
  intro h
  have hn := norm_pairMultiplier y hy θ n
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

/-- **Pointwise unitarity.**  Multiplying by the pair multiplier preserves modulus, so the
intertwiner is an isometry wherever it is defined. -/
theorem norm_pairMultiplier_mul {y : ℝ → ℂ} (hy : ∀ t : ℝ, ‖y t‖ = 1) (θ : ℕ → ℝ) (n : ℕ)
    (c : ℂ) : ‖pairMultiplier y θ n * c‖ = ‖c‖ := by
  rw [norm_mul, norm_pairMultiplier y hy θ n, one_mul]

/-- **The intertwining relation.**  A two-particle section obeying the `S`-exchange law becomes,
after multiplication by the pair multiplier, a section obeying the *constant* `epsilon` exchange
law.  This is Lechner's trivialization in its essential form: the whole `S`-dependence is absorbed
into the half-phase. -/
theorem intertwine_two {y S : ℝ → ℂ} {ε : ℂ} (hy : ∀ t : ℝ, y t ≠ 0)
    (hS : ∀ t : ℝ, S t = ε * (y t / y (-t)))
    {ψ : ℝ → ℝ → ℂ} (hψ : ∀ a b : ℝ, ψ b a = S (a - b) * ψ a b) (a b : ℝ) :
    y (b - a) * ψ b a = ε * (y (a - b) * ψ a b) := by
  have hneg : -(a - b) = b - a := by ring
  have hSab : S (a - b) = ε * (y (a - b) / y (b - a)) := by
    rw [hS, hneg]
  have h1 : y (b - a) ≠ 0 := hy _
  have h2 : y (a - b) ≠ 0 := hy _
  rw [hψ a b, hSab]
  field_simp

/-- **The constant-statistics frame.**  Written with the multiplier itself: the transformed section
`phi = Y_2 psi` satisfies the constant exchange law. -/
theorem intertwine_two_pairMultiplier {y S : ℝ → ℂ} {ε : ℂ} (hy : ∀ t : ℝ, y t ≠ 0)
    (hS : ∀ t : ℝ, S t = ε * (y t / y (-t)))
    {ψ : ℝ → ℝ → ℂ} (hψ : ∀ a b : ℝ, ψ b a = S (a - b) * ψ a b) (θ : ℕ → ℝ) :
    pairMultiplier y (fun k => θ (1 - k)) 2 * ψ (θ 1) (θ 0)
      = ε * (pairMultiplier y θ 2 * ψ (θ 0) (θ 1)) := by
  rw [pairMultiplier_two, pairMultiplier_two]
  have h : (fun k => θ (1 - k)) 0 - (fun k => θ (1 - k)) 1 = θ 1 - θ 0 := by norm_num
  rw [h]
  exact intertwine_two hy hS hψ (θ 0) (θ 1)

/-! ### The adjacent transposition -/

/-- The index involution transposing `m` and `m+1`. -/
def swapIdx (m k : ℕ) : ℕ := if k = m then m + 1 else if k = m + 1 then m else k

/-- Transposing two adjacent rapidities. -/
def swapAt (m : ℕ) (θ : ℕ → ℝ) : ℕ → ℝ := θ ∘ swapIdx m

theorem swapAt_apply (m : ℕ) (θ : ℕ → ℝ) (k : ℕ) : swapAt m θ k = θ (swapIdx m k) := rfl

@[simp]
theorem swapIdx_self (m : ℕ) : swapIdx m m = m + 1 := by
  rw [swapIdx, if_pos rfl]

@[simp]
theorem swapIdx_succ (m : ℕ) : swapIdx m (m + 1) = m := by
  rw [swapIdx, if_neg (by omega), if_pos rfl]

theorem swapIdx_of_ne (m k : ℕ) (h1 : k ≠ m) (h2 : k ≠ m + 1) : swapIdx m k = k := by
  rw [swapIdx, if_neg h1, if_neg h2]

theorem swapIdx_involutive (m : ℕ) : Function.Involutive (swapIdx m) := by
  intro k
  by_cases h1 : k = m
  · rw [h1, swapIdx_self, swapIdx_succ]
  · by_cases h2 : k = m + 1
    · rw [h2, swapIdx_succ, swapIdx_self]
    · rw [swapIdx_of_ne m k h1 h2, swapIdx_of_ne m k h1 h2]

theorem swapIdx_lt {m k n : ℕ} (h : m + 1 < n) (hk : k < n) : swapIdx m k < n := by
  by_cases h1 : k = m
  · rw [h1, swapIdx_self]; omega
  · by_cases h2 : k = m + 1
    · rw [h2, swapIdx_succ]; omega
    · rw [swapIdx_of_ne m k h1 h2]; exact hk

theorem swapAt_of_lt {m k : ℕ} (θ : ℕ → ℝ) (h : k < m) : swapAt m θ k = θ k := by
  rw [swapAt_apply, swapIdx_of_ne m k (by omega) (by omega)]

/-- The pair multiplier only sees the first `n` rapidities. -/
theorem pairMultiplier_congr (y : ℝ → ℂ) {θ φ : ℕ → ℝ} (n : ℕ) (h : ∀ k, k < n → θ k = φ k) :
    pairMultiplier y θ n = pairMultiplier y φ n := by
  rw [pairMultiplier, pairMultiplier]
  refine Finset.prod_congr rfl fun l hl => ?_
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [h k (lt_trans (Finset.mem_range.mp hk) (Finset.mem_range.mp hl)),
    h l (Finset.mem_range.mp hl)]

/-- The pair string against a fixed rapidity is invariant under an adjacent transposition of the
other indices. -/
theorem prod_range_swapAt (y : ℝ → ℂ) (θ : ℕ → ℝ) (c : ℝ) {m n : ℕ} (h : m + 1 < n) :
    ∏ k ∈ Finset.range n, y (swapAt m θ k - c) = ∏ k ∈ Finset.range n, y (θ k - c) := by
  refine Finset.prod_nbij' (fun k => swapIdx m k) (fun k => swapIdx m k) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_range.mpr (swapIdx_lt h (Finset.mem_range.mp hk))
  · intro k hk
    exact Finset.mem_range.mpr (swapIdx_lt h (Finset.mem_range.mp hk))
  · intro k _
    exact swapIdx_involutive m k
  · intro k _
    exact swapIdx_involutive m k
  · intro k _
    rw [swapAt_apply]

/-- **The adjacent transposition ratio.**  Swapping two adjacent rapidities changes the pair
multiplier by exactly the elementary factor of that pair, reversed.  All other pair phases are
permuted among themselves. -/
theorem pairMultiplier_swapAt (y : ℝ → ℂ) (θ : ℕ → ℝ) {m n : ℕ} (h : m + 1 < n) :
    pairMultiplier y (swapAt m θ) n * y (θ m - θ (m + 1))
      = pairMultiplier y θ n * y (θ (m + 1) - θ m) := by
  induction n, h using Nat.le_induction with
  | base =>
      have hlow : pairMultiplier y (swapAt m θ) m = pairMultiplier y θ m :=
        pairMultiplier_congr y m fun k hk => swapAt_of_lt θ hk
      have hstr1 : ∏ k ∈ Finset.range m, y (swapAt m θ k - swapAt m θ m)
          = ∏ k ∈ Finset.range m, y (θ k - θ (m + 1)) := by
        refine Finset.prod_congr rfl fun k hk => ?_
        rw [swapAt_of_lt θ (Finset.mem_range.mp hk), swapAt_apply, swapIdx_self]
      have hstr2 : ∏ k ∈ Finset.range (m + 1), y (swapAt m θ k - swapAt m θ (m + 1))
          = (∏ k ∈ Finset.range m, y (θ k - θ m)) * y (θ (m + 1) - θ m) := by
        rw [Finset.prod_range_succ]
        congr 1
        · refine Finset.prod_congr rfl fun k hk => ?_
          rw [swapAt_of_lt θ (Finset.mem_range.mp hk), swapAt_apply, swapIdx_succ]
        · rw [swapAt_apply, swapAt_apply, swapIdx_self, swapIdx_succ]
      have e1 : pairMultiplier y (swapAt m θ) (m + 2)
          = pairMultiplier y (swapAt m θ) m
            * (∏ k ∈ Finset.range m, y (swapAt m θ k - swapAt m θ m))
            * (∏ k ∈ Finset.range (m + 1), y (swapAt m θ k - swapAt m θ (m + 1))) := by
        rw [show m + 2 = (m + 1) + 1 from rfl, pairMultiplier_succ, pairMultiplier_succ]
      have e2 : pairMultiplier y θ (m + 2)
          = pairMultiplier y θ m
            * (∏ k ∈ Finset.range m, y (θ k - θ m))
            * (∏ k ∈ Finset.range (m + 1), y (θ k - θ (m + 1))) := by
        rw [show m + 2 = (m + 1) + 1 from rfl, pairMultiplier_succ, pairMultiplier_succ]
      have e3 : ∏ k ∈ Finset.range (m + 1), y (θ k - θ (m + 1))
          = (∏ k ∈ Finset.range m, y (θ k - θ (m + 1))) * y (θ m - θ (m + 1)) :=
        Finset.prod_range_succ _ m
      rw [e1, e2, hlow, hstr1, hstr2, e3]
      ring
  | succ n hn ih =>
      have htop : swapAt m θ n = θ n := by
        rw [swapAt_apply, swapIdx_of_ne m n (by omega) (by omega)]
      have e1 : pairMultiplier y (swapAt m θ) (n + 1) * y (θ m - θ (m + 1))
          = (pairMultiplier y (swapAt m θ) n * y (θ m - θ (m + 1)))
            * (∏ k ∈ Finset.range n, y (θ k - θ n)) := by
        rw [pairMultiplier_succ, htop, prod_range_swapAt y θ (θ n) hn]
        ring
      have e2 : pairMultiplier y θ (n + 1) * y (θ (m + 1) - θ m)
          = (pairMultiplier y θ n * y (θ (m + 1) - θ m))
            * (∏ k ∈ Finset.range n, y (θ k - θ n)) := by
        rw [pairMultiplier_succ]
        ring
      rw [e1, e2, ih]

/-- **The intertwining theorem.**  A section obeying the `S`-exchange law under an adjacent
transposition becomes, after multiplication by the pair multiplier, a section obeying the *constant*
`epsilon` law.  Since adjacent transpositions generate the permutations, this is the statement that
the pair multiplier intertwines the `S`-permutation representation with the constant Bose/Fermi
one. -/
theorem intertwine_swapAt {y S : ℝ → ℂ} {ε : ℂ} (hy : ∀ t : ℝ, y t ≠ 0)
    (hS : ∀ t : ℝ, S t = ε * (y t / y (-t))) {ψ : (ℕ → ℝ) → ℂ} {m n : ℕ} (h : m + 1 < n)
    (hψ : ∀ φ : ℕ → ℝ, ψ (swapAt m φ) = S (φ m - φ (m + 1)) * ψ φ) (θ : ℕ → ℝ) :
    pairMultiplier y (swapAt m θ) n * ψ (swapAt m θ)
      = ε * (pairMultiplier y θ n * ψ θ) := by
  have hrel := pairMultiplier_swapAt y θ h
  have ha : y (θ m - θ (m + 1)) ≠ 0 := hy _
  have hb : y (θ (m + 1) - θ m) ≠ 0 := hy _
  have hSm : S (θ m - θ (m + 1)) = ε * (y (θ m - θ (m + 1)) / y (θ (m + 1) - θ m)) := by
    rw [hS, neg_sub]
  rw [hψ θ, hSm]
  field_simp
  linear_combination (ε * ψ θ) * hrel

/-! ### The intertwiner is an isometry -/

section Isometry

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Multiplication by a unimodular function preserves every `L^p` seminorm.** -/
theorem eLpNorm_mul_of_norm_eq_one {g f : α → ℂ} (hg : ∀ x : α, ‖g x‖ = 1) (p : ℝ≥0∞) :
    eLpNorm (fun x => g x * f x) p μ = eLpNorm f p μ := by
  refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, hg, one_mul]

/-- Membership in `L^p` is preserved by a unimodular multiplier. -/
theorem memLp_mul_of_norm_eq_one {g f : α → ℂ} (hg : ∀ x : α, ‖g x‖ = 1)
    (hgm : AEStronglyMeasurable g μ) {p : ℝ≥0∞} (hf : MemLp f p μ) :
    MemLp (fun x => g x * f x) p μ := by
  refine ⟨hgm.mul hf.1, ?_⟩
  rw [eLpNorm_mul_of_norm_eq_one hg]
  exact hf.2

/-- **The pair multiplier acts isometrically.**  For a unimodular half-phase, multiplying a
rapidity-space function by the pair multiplier leaves every `L^p` seminorm unchanged, so the
intertwiner is an isometry at each particle number. -/
theorem eLpNorm_pairMultiplier_mul {y : ℝ → ℂ} (hy : ∀ t : ℝ, ‖y t‖ = 1) (n : ℕ)
    (Θ : α → (ℕ → ℝ)) (f : α → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun x => pairMultiplier y (Θ x) n * f x) p μ = eLpNorm f p μ :=
  eLpNorm_mul_of_norm_eq_one (fun x => norm_pairMultiplier y hy (Θ x) n) p

end Isometry

end GaloisForLFunctions.HTGeometry
