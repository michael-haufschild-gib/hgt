import GaloisForLFunctions.RHTower.Sieve.PrimeSieveAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.PrimeLogWindowCount

/-!
# The affine mean square of an arbitrary finitely supported Dirichlet series

The almost-diagonal mean value theorem leaves behind the neighbour count
`#{m ∈ s : |log n − log m| < δ}`.  For a prime support the Selberg sieve saves a logarithm on it; but
for *any* support of positive integers the count is at most the number of integers in the window,

`#{m ∈ s : |log n − log m| < δ} ≤ n(e^δ − e^{−δ}) + 1`,

and that already suffices for the affine shape.  At the neighbour scale `δ = 1/T` forced by the
truncation, `T(e^{1/T} − e^{−1/T}) ≤ 2e`, so

`∫_{|y| ≤ T} ‖L(a,σ+iy)‖² dy ≤ 5πe·∑_n n‖a_n n^{−σ}‖² + (5π/2)·T·∑_n ‖a_n n^{−σ}‖²`.

The height-independent part is the `n`-weighted mass and the height-linear part is the plain mass —
no primality, no sieve level, no sieve error, and no additive `z`.  Against the prime-sieve version the
constant is worse by `2/log Y` and the rate is *better* by the whole `selbergFibreError z Y + z`, so for
supports the sieve cannot handle — a convolution of two prime weights, say — this is the estimate to
use.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set Finset

/-- A multiplicative window of ratio `e^δ` around `n` consists of integers of one interval. -/
theorem logNeighbourCount_le_card_Ioc (s : Finset ℕ) (hs0 : (0 : ℕ) ∉ s) {δ : ℝ} {n : ℕ}
    (hn : 1 ≤ n) :
    logNeighbourCount s δ n
      ≤ #(Finset.Ioc ⌊(n : ℝ) * Real.exp (-δ)⌋₊ ⌊(n : ℝ) * Real.exp δ⌋₊) := by
  classical
  rw [logNeighbourCount]
  refine Finset.card_le_card ?_
  intro m hm
  rw [Finset.mem_filter] at hm
  obtain ⟨hms, hmlog⟩ := hm
  have hm1 : 0 < m := Nat.pos_of_ne_zero fun h => hs0 (h ▸ hms)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [abs_lt] at hmlog
  have hupper : (m : ℝ) < (n : ℝ) * Real.exp δ := by
    have h := Real.exp_lt_exp.2
      (show Real.log (m : ℝ) - Real.log (n : ℝ) < δ by linarith [hmlog.1])
    rw [Real.exp_sub, Real.exp_log hmR, Real.exp_log hnR, div_lt_iff₀ hnR] at h
    linarith [h]
  have hlower : (n : ℝ) * Real.exp (-δ) < (m : ℝ) := by
    have h := Real.exp_lt_exp.2 hmlog.2
    rw [Real.exp_sub, Real.exp_log hnR, Real.exp_log hmR, div_lt_iff₀ hmR] at h
    have hprod : Real.exp δ * Real.exp (-δ) = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith [h, Real.exp_pos (-δ), hprod]
  rw [Finset.mem_Ioc]
  refine ⟨?_, ?_⟩
  · rw [Nat.floor_lt (by positivity)]
    exact hlower
  · exact Nat.le_floor hupper.le

/-- **The neighbour count of an arbitrary support.**  At most the number of integers in the
multiplicative window. -/
theorem logNeighbourCount_le_window (s : Finset ℕ) (hs0 : (0 : ℕ) ∉ s) {δ : ℝ} (hδ : 0 ≤ δ)
    {n : ℕ} (hn : 1 ≤ n) :
    (logNeighbourCount s δ n : ℝ) ≤ (n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1 := by
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hexp : Real.exp (-δ) ≤ Real.exp δ := Real.exp_le_exp.2 (by linarith)
  have hab : ⌊(n : ℝ) * Real.exp (-δ)⌋₊ ≤ ⌊(n : ℝ) * Real.exp δ⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left hexp hnR)
  have hsub := logNeighbourCount_le_card_Ioc s hs0 (δ := δ) hn
  have hsubR : (logNeighbourCount s δ n : ℝ)
      ≤ ((⌊(n : ℝ) * Real.exp δ⌋₊ - ⌊(n : ℝ) * Real.exp (-δ)⌋₊ : ℕ) : ℝ) := by
    rw [← Nat.card_Ioc ⌊(n : ℝ) * Real.exp (-δ)⌋₊ ⌊(n : ℝ) * Real.exp δ⌋₊]
    exact_mod_cast hsub
  rw [Nat.cast_sub hab] at hsubR
  have hlen := floor_sub_floor_le (x := (n : ℝ) * Real.exp (-δ))
    (y := (n : ℝ) * Real.exp δ) (by positivity)
  linarith

/-- **The mean value theorem for an arbitrary finitely supported Dirichlet polynomial.**  The
almost-diagonal mean value theorem with its neighbour count discharged by the number of integers in the
window. -/
theorem integral_Icc_normSq_logPoly_le_general (a : ℕ → ℂ) (s : Finset ℕ) (hs0 : (0 : ℕ) ∉ s)
    {δ W : ℝ} (hδ : 0 < δ) (hWδ : 2 * Real.pi * δ * W ≤ 1) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2)
      ≤ (5 / (4 * δ)) * ∑ n ∈ s, ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) * ‖a n‖ ^ 2 := by
  refine le_trans (integral_Icc_normSq_logPoly_le_count a s hδ hWδ) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) (by positivity)
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h => hs0 (h ▸ hn)
  exact mul_le_mul_of_nonneg_right (logNeighbourCount_le_window s hs0 hδ.le hn1) (by positivity)

/-- **The truncated mean square of an arbitrary finitely supported Dirichlet series on the Perron
line.**  The window mean value theorem at the neighbour scale `δ = 1/T` forced by the truncation, with
its count discharged by the length of the window. -/
theorem integral_Icc_normSq_LSeries_le_general {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ 2 * Real.pi * ((5 * T / 4) * ∑ n ∈ s,
          ((n : ℝ) * (Real.exp (1 / T) - Real.exp (-(1 / T))) + 1)
              * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hδ : (0 : ℝ) < 1 / T := by positivity
  have hWδ : 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) ≤ 1 := by
    rw [show 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) = 1 by field_simp]
  rw [integral_Icc_normSq_LSeries_eq hs0 hsupp σ hT.le]
  refine mul_le_mul_of_nonneg_left ?_ hpi.le
  refine le_trans (integral_Icc_normSq_logPoly_le_general
    (fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s hs0 hδ hWδ) ?_
  rw [show (5 : ℝ) / (4 * (1 / T)) = 5 * T / 4 by field_simp]

/-- The height-independent part of the general mean square: the `n`-weighted mass. -/
def generalMeanSquareConst (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) : ℝ :=
  5 * Real.pi * Real.exp 1
    * ∑ n ∈ s, (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2

/-- The height-linear part of the general mean square: the plain mass. -/
def generalMeanSquareRate (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) : ℝ :=
  (5 * Real.pi / 2) * ∑ n ∈ s, ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2

theorem generalMeanSquareConst_nonneg (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) :
    0 ≤ generalMeanSquareConst a s σ := by
  rw [generalMeanSquareConst]
  have : (0 : ℝ) ≤ ∑ n ∈ s, (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  positivity

theorem generalMeanSquareRate_nonneg (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) :
    0 ≤ generalMeanSquareRate a s σ := by
  rw [generalMeanSquareRate]
  have : (0 : ℝ) ≤ ∑ n ∈ s, ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  positivity

/-- **The affine mean square of an arbitrary finitely supported Dirichlet series.**  The neighbour
count's factor `T` is cancelled by the window width `1/T` it forces, so the `n`-weighted mass is charged
no height at all and only the plain mass grows with the height. -/
theorem integral_Icc_normSq_LSeries_le_general_affine {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ generalMeanSquareConst a s σ + generalMeanSquareRate a s σ * T := by
  have hT0 : (0 : ℝ) < T := by linarith
  refine le_trans (integral_Icc_normSq_LSeries_le_general hs0 hsupp σ hT0) ?_
  have hsplit : ∑ n ∈ s, ((n : ℝ) * (Real.exp (1 / T) - Real.exp (-(1 / T))) + 1)
        * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      = (Real.exp (1 / T) - Real.exp (-(1 / T)))
          * (∑ n ∈ s, (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2)
        + ∑ n ∈ s, ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsplit, generalMeanSquareConst, generalMeanSquareRate]
  have hS1 : (0 : ℝ) ≤ ∑ n ∈ s, (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hkey : (5 * Real.pi / 2)
        * ((T * (Real.exp (1 / T) - Real.exp (-(1 / T))))
            * ∑ n ∈ s, (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2)
      ≤ (5 * Real.pi / 2)
        * ((2 * Real.exp 1) * ∑ n ∈ s, (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_exp_sub_exp_neg_le hT) hS1) (by positivity)
  linarith

end RHTower.Sieve
end
