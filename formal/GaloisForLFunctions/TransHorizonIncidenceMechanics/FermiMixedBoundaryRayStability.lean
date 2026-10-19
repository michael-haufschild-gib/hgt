import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiCompleteTraceValuationStability
import GaloisForLFunctions.RHTower.AutocorrelationChainSineCertificate
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Mixed-boundary sine control on normalized Fermi rays

The existing scalar path sine certificate is reflected across the free endpoint.
The actual Fermi jump then supplies the consecutive difference of the normalized
sieve ray. This is an ingredient for sharp physical trace estimates; it does not
by itself assert an asymptotic pronic inverse constant.
-/

open Finset
open RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Sieve readings normalized by their dyadic dilation. -/
def fermiNormalizedDyadicSieve (N : ℕ) (c : ℕ → ℝ) (b k : ℕ) : ℝ :=
  sieveSeq N c (2 ^ k * b) / (2 : ℝ) ^ k

/-- Boundary readings at the following dyadic level, with the same normalization. -/
def fermiNormalizedDyadicJump (N : ℕ) (c : ℕ → ℝ) (b k : ℕ) : ℝ :=
  fermiBoundaryJump N c (2 ^ (k + 1) * b) / (2 : ℝ) ^ (k + 1)

/-- The normalized Fermi observation is the exact forward difference along a ray. -/
theorem fermiNormalizedDyadicJump_eq_sub (N : ℕ) (c : ℕ → ℝ)
    {b : ℕ} (hb : 0 < b) (k : ℕ) :
    fermiNormalizedDyadicJump N c b k =
      fermiNormalizedDyadicSieve N c b k - fermiNormalizedDyadicSieve N c b (k + 1) := by
  have hp : 0 < 2 ^ k * b := Nat.mul_pos (by positivity) hb
  have hj := fermiBoundaryJump_even N c (2 ^ k * b - 1)
  rw [show 2 ^ k * b - 1 + 1 = 2 ^ k * b by omega,
    show 2 * (2 ^ k * b - 1) + 2 = 2 ^ (k + 1) * b by
      rw [pow_succ', Nat.mul_assoc]; omega] at hj
  unfold fermiNormalizedDyadicJump fermiNormalizedDyadicSieve
  rw [hj, pow_succ']
  field_simp
  ring

private theorem mixed_boundary_sine (n : ℕ) (f : ℕ → ℝ) (hf : f n = 0) :
    (2 - 2 * Real.cos (Real.pi / (((2 * n : ℕ) : ℝ) + 1))) *
        (∑ k ∈ Finset.range n, (f k)^2) ≤
      ∑ k ∈ Finset.range n, (f k - f (k + 1))^2 := by
  let v : ℕ → ℝ := fun k => if k ≤ n then f (n - k) else f (k - n - 1)
  have hv0 : v 0 = 0 := by simp [v, hf]
  have hve : v (2 * n + 1) = 0 := by
    simp [v, show ¬ 2 * n + 1 ≤ n by omega,
      show 2 * n + 1 - n - 1 = n by omega, hf]
  have hmassLeft : (∑ k ∈ Finset.range (n + 1), (v k)^2) =
      ∑ k ∈ Finset.range n, (f k)^2 := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1), (f ((n + 1) - 1 - k))^2 := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ n := by simpa using Finset.mem_range.mp hk
        simp [v, hk']
      _ = ∑ k ∈ Finset.range (n + 1), (f k)^2 :=
        Finset.sum_range_reflect (fun k => (f k)^2) (n + 1)
      _ = _ := by rw [Finset.sum_range_succ, hf]; ring
  have hmassRight : (∑ k ∈ Finset.range n, (v (n + 1 + k))^2) =
      ∑ k ∈ Finset.range n, (f k)^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [v, show ¬ n + 1 + k ≤ n by omega,
      show n + 1 + k - n - 1 = k by omega]
  have hmass : (∑ k ∈ Finset.range (2 * n + 1), (v k)^2) =
      2 * ∑ k ∈ Finset.range n, (f k)^2 := by
    rw [show 2 * n + 1 = (n + 1) + n by omega, Finset.sum_range_add,
      hmassLeft, hmassRight]
    ring
  have hcrossLeft : (∑ k ∈ Finset.range n, v k * v (k + 1)) =
      ∑ k ∈ Finset.range n, f k * f (k + 1) := by
    calc
      _ = ∑ k ∈ Finset.range n, f (n - 1 - k) * f (n - 1 - k + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        simp only [v, if_pos (show k ≤ n by omega),
          if_pos (show k + 1 ≤ n by omega)]
        rw [show n - k = n - 1 - k + 1 by omega,
          show n - (k + 1) = n - 1 - k by omega]
        ring
      _ = _ := Finset.sum_range_reflect (fun k => f k * f (k + 1)) n
  have hcenter : v n * v (n + 1) = (f 0)^2 := by
    simp [v, show ¬ n + 1 ≤ n by omega, pow_two]
  have hcrossRight : (∑ k ∈ Finset.range (n + 1), v (n + k) * v (n + k + 1)) =
      (∑ k ∈ Finset.range n, f k * f (k + 1)) + (f 0)^2 := by
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero, hcenter]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    simp [v, show ¬ n + (k + 1) ≤ n by omega,
      show ¬ n + (k + 1) + 1 ≤ n by omega,
      show n + (k + 1) + 1 - n - 1 = k + 1 by omega]
  have hcross : (∑ k ∈ Finset.range (2 * n + 1), v k * v (k + 1)) =
      2 * (∑ k ∈ Finset.range n, f k * f (k + 1)) + (f 0)^2 := by
    rw [show 2 * n + 1 = n + (n + 1) by omega, Finset.sum_range_add,
      hcrossLeft, hcrossRight]
    ring
  have hb := RHTower.autocorrelation_chain_sine_bound (2 * n) v hv0 hve
  rw [hmass, hcross] at hb
  have hshift : (∑ k ∈ Finset.range n, (f (k + 1))^2) =
      (∑ k ∈ Finset.range n, (f k)^2) - (f 0)^2 := by
    have h1 := Finset.sum_range_succ' (fun k => (f k)^2) n
    have h2 := Finset.sum_range_succ (fun k => (f k)^2) n
    rw [hf] at h2
    linarith
  have he : (∑ k ∈ Finset.range n, (f k - f (k + 1))^2) =
      2 * (∑ k ∈ Finset.range n, (f k)^2) - (f 0)^2 -
        2 * ∑ k ∈ Finset.range n, f k * f (k + 1) := by
    calc
      _ = ∑ k ∈ Finset.range n,
          ((f k)^2 + (f (k + 1))^2 - 2 * (f k * f (k + 1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hshift]
        ring
  rw [he]
  nlinarith only [hb]

/-- Exact sine coercivity after retaining the observed terminal value. -/
theorem fermiNormalizedDyadicSieve_terminal_sine_bound (N : ℕ) (c : ℕ → ℝ)
    {b : ℕ} (hb : 0 < b) (a n : ℕ) :
    (2 - 2 * Real.cos (Real.pi / (((2 * n : ℕ) : ℝ) + 1))) *
        (∑ k ∈ Finset.range n,
          (fermiNormalizedDyadicSieve N c b (a + k) -
            fermiNormalizedDyadicSieve N c b (a + n)) ^ 2) ≤
      ∑ k ∈ Finset.range n, (fermiNormalizedDyadicJump N c b (a + k)) ^ 2 := by
  have h := mixed_boundary_sine n
    (fun k => fermiNormalizedDyadicSieve N c b (a + k) -
      fermiNormalizedDyadicSieve N c b (a + n)) (by simp)
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [fermiNormalizedDyadicJump_eq_sub N c hb]
  congr 1
  rw [show a + (k + 1) = a + k + 1 by omega]
  ring

/-- Horizon saturation becomes an exact half-decay step in normalized coordinates. -/
theorem fermiNormalizedDyadicSieve_depth_step (N : ℕ) (c : ℕ → ℝ) (b : ℕ) :
    let D := Nat.log 2 N + 1
    fermiNormalizedDyadicSieve N c b (D + 1) =
      fermiNormalizedDyadicSieve N c b D / 2 := by
  dsimp only
  have hs : sieveSeq N c (2 ^ (Nat.log 2 N + 1 + 1) * b) =
      sieveSeq N c (2 ^ (Nat.log 2 N + 1) * b) := by
    simpa only [Nat.add_assoc] using sieveSeq_dyadic_depth_saturation N c b
  unfold fermiNormalizedDyadicSieve
  rw [hs, pow_succ']
  field_simp
  ring

/-- The terminal normalized observation equals the next normalized sieve value. -/
theorem fermiNormalizedDyadicJump_depth_boundary (N : ℕ) (c : ℕ → ℝ)
    {b : ℕ} (hb : 0 < b) :
    let D := Nat.log 2 N + 1
    fermiNormalizedDyadicJump N c b D = fermiNormalizedDyadicSieve N c b (D + 1) := by
  dsimp only
  rw [fermiNormalizedDyadicJump_eq_sub N c hb]
  have hs := fermiNormalizedDyadicSieve_depth_step N c b
  dsimp only at hs
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
