/-
The mean square of the σ-weighted detection polynomial, split into diagonal and off-diagonal parts.

The detection polynomial `E = D_N·M − 1` (where `D_N` is the length-`N` Dirichlet polynomial of ζ
and `M` the length-`y` Möbius mollifier) has σ-weighted coefficients `detCoeffW N y σ` supported on
`[1, N·y]` and vanishing below the cutoff `min(N,y)`.  Its second moment over `[T, T+U]` is, by the
mean-value identity `secondMoment_meanValue`,

  ∫_T^{T+U} ‖E‖² = U·∑_k eₖ² + (off-diagonal),

and both parts are bounded here without any Hilbert / large-sieve inequality:

  * the **diagonal** `∑_k eₖ²` runs only over `k > min(N,y)` (below-cutoff coefficients vanish) and
    is dominated by the convergent divisor tail `∑' 𝟙_{k>min} d(k)² k^{-2σ}`, which `→ 0` as the
    cutoff `→ ∞` (`detection_diagonal_le_tsum`);
  * the **off-diagonal** is dominated by the elementary harmonic bound
    `4·(N·y)·H(N·y)·∑ eₖ²` from `offDiagonal_le` (via `|log(n/m)| ≥ |n−m|/K` and AM–GM).

Dividing by `U` and letting `U → ∞` kills the off-diagonal part (it is `U`-independent); the diagonal
part is the vanishing tail.  This is the `o(T)` mean-square input that the large-values density
argument (`CarlsonDensity`) consumes to bound `N(σ,T)`.
-/
import GaloisForLFunctions.RHTower.MollifierDetection
import GaloisForLFunctions.RHTower.OffDiagonalBound

open Complex Filter

namespace RHTower

/-- **The detection diagonal tail vanishes with the cutoff.**  The divisor tail
`∑' 𝟙_{m<k} d(k)² k^{-2σ}` `→ 0` as `m → ∞`.  Reindexing the indicator sum onto `{k ≥ m+1}`
(`Function.Injective.tsum_eq`) identifies it with the shifted tail `∑'_j g(j+(m+1))`, which vanishes
by `tendsto_divisor_sq_rpow_tail_zero`.  This turns the diagonal hypothesis `D(T) → 0` of the density
capstone into the elementary requirement that the mollifier cutoff `min(N,y) → ∞`. -/
theorem detection_diagonal_tail_tendsto (σ : ℝ) :
    Tendsto
      (fun m : ℕ => ∑' k : ℕ, Set.indicator {j | m < j}
          (fun k => (k.divisors.card : ℝ) ^ 2 * (k : ℝ) ^ (-2 * σ)) k)
      atTop (nhds 0) := by
  set g : ℕ → ℝ := fun k => (k.divisors.card : ℝ) ^ 2 * (k : ℝ) ^ (-2 * σ) with hg
  have hpt : ∀ m : ℕ,
      (∑' k : ℕ, Set.indicator {j | m < j} g k) = ∑' j : ℕ, g (j + (m + 1)) := by
    intro m
    have hinj : Function.Injective (fun j : ℕ => j + (m + 1)) := add_left_injective _
    have hsupp : Function.support (Set.indicator {j | m < j} g)
        ⊆ Set.range (fun j : ℕ => j + (m + 1)) := by
      intro k hk
      have hval : Set.indicator {j | m < j} g k ≠ 0 := hk
      have hkset : m < k := by
        by_contra hc
        have hnot : k ∉ {j | m < j} := by simp only [Set.mem_setOf_eq]; omega
        rw [Set.indicator_of_notMem hnot] at hval
        exact hval rfl
      exact ⟨k - (m + 1), by show k - (m + 1) + (m + 1) = k; omega⟩
    have hre := Function.Injective.tsum_eq hinj hsupp
    rw [← hre]
    exact tsum_congr (fun j => Set.indicator_of_mem
      (show j + (m + 1) ∈ {j | m < j} by simp only [Set.mem_setOf_eq]; omega) g)
  have htail := tendsto_divisor_sq_rpow_tail_zero σ
  have hcomp : Tendsto (fun m : ℕ => ∑' j : ℕ, g (j + (m + 1))) atTop (nhds 0) :=
    htail.comp (tendsto_add_atTop_nat 1)
  exact (tendsto_congr hpt).mpr hcomp

/-- **The diagonal input of the density capstone holds for any cutoff schedule tending to `∞`.**  If
`cut : ℝ → ℕ` (e.g. the mollifier cutoff `min(N(T), y(T))`) tends to `∞` with `T`, then the diagonal
tail `D(T) = ∑' 𝟙_{cut T < k} d(k)² k^{-2σ}` eventually falls below any `ε > 0`.  Immediate from
`detection_diagonal_tail_tendsto` composed with `cut`.  This discharges the `hD` hypothesis of
`carlson_rhLadder_of_schedule`: the diagonal contributes nothing but the elementary requirement that
the cutoff grow. -/
theorem detection_diagonal_hD_of_cutoff {cut : ℝ → ℕ} (σ : ℝ)
    (hcut : Tendsto cut atTop atTop) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (∑' k : ℕ, Set.indicator {j | cut T < j}
        (fun k => (k.divisors.card : ℝ) ^ 2 * (k : ℝ) ^ (-2 * σ)) k) ≤ ε := by
  intro ε hε
  have hcomp : Tendsto (fun T => ∑' k : ℕ, Set.indicator {j | cut T < j}
      (fun k => (k.divisors.card : ℝ) ^ 2 * (k : ℝ) ^ (-2 * σ)) k) atTop (nhds 0) :=
    (detection_diagonal_tail_tendsto σ).comp hcut
  have hev := hcomp.eventually (Iic_mem_nhds hε)
  rw [eventually_atTop] at hev
  obtain ⟨T₀, hT₀⟩ := hev
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

/-- **σ-weighted detection second moment.**  The mean square of the detection polynomial
`E = D_N·M − 1` over `[T, T+U]` is bounded by `U` times the divisor tail (the diagonal) plus the
elementary off-diagonal bound `4·(N·y)·H(N·y)·∑ eₖ²`.  Direct from the mean-value identity
`secondMoment_meanValue`, the diagonal tail control `detection_diagonal_le_tsum`, and the off-diagonal
bound `offDiagonal_le`. -/
theorem detectionW_secondMoment_bound {N y : ℕ} (σ : ℝ) (hσ : 1 / 2 < σ)
    (hmin : 1 ≤ min N y) (T U : ℝ) (hU : 0 ≤ U) :
    (∫ t in T..(T + U),
        ‖dpoly (detCoeffW N y σ) (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)) t‖ ^ 2)
      ≤ U * (∑' k : ℕ, Set.indicator {j | min N y < j}
                (fun k => (k.divisors.card : ℝ) ^ 2 * (k : ℝ) ^ (-2 * σ)) k)
        + 4 * ((N * y : ℕ) : ℝ) * (∑ j ∈ Finset.Icc 1 (N * y), 1 / (j : ℝ))
            * ∑ k ∈ convSupp (Finset.Icc 1 N) (Finset.Icc 1 y), (detCoeffW N y σ k) ^ 2 := by
  rw [secondMoment_meanValue]
  have hdiag : U * (∑ m ∈ convSupp (Finset.Icc 1 N) (Finset.Icc 1 y), (detCoeffW N y σ m) ^ 2)
      ≤ U * (∑' k : ℕ, Set.indicator {j | min N y < j}
                (fun k => (k.divisors.card : ℝ) ^ 2 * (k : ℝ) ^ (-2 * σ)) k) := by
    apply mul_le_mul_of_nonneg_left _ hU
    rw [detectionW_diagonal_tail]
    exact detection_diagonal_le_tsum σ hσ hmin
  have hoff : (∑ m ∈ convSupp (Finset.Icc 1 N) (Finset.Icc 1 y),
                ∑ n ∈ (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)).erase m,
                  detCoeffW N y σ m * detCoeffW N y σ n * cosInt (Real.log n - Real.log m) T U)
      ≤ 4 * ((N * y : ℕ) : ℝ) * (∑ j ∈ Finset.Icc 1 (N * y), 1 / (j : ℝ))
          * ∑ k ∈ convSupp (Finset.Icc 1 N) (Finset.Icc 1 y), (detCoeffW N y σ k) ^ 2 := by
    refine le_trans (le_abs_self _) ?_
    refine le_trans (offDiagonal_abs_le _ _ _ _ (fun n hn => one_le_of_mem_convSupp hn)) ?_
    exact offDiagonal_le _ (convSupp_subset_Icc N y)
  linarith [hdiag, hoff]

end RHTower
