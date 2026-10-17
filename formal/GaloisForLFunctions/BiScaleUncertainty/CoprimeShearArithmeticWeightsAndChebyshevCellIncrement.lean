import GaloisForLFunctions.BiScaleUncertainty.CoprimeShearAndMultiplicativeGraphUncertainty
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicGaugeMeanSquareChebyshevWeilSynthesis
import GaloisForLFunctions.RHTower.TruncatedMoebiusResidual
import GaloisForLFunctions.RHTower.FermiNymanLogMobiusHead

/-!
# Pillar XXX: Coprime Shear Coupled to Arithmetic Weights ($\mu, \Lambda, \psi$) & Nyquist-Cell Abel Summation

This module develops **Direction 2**, coupling the discrete additive successor/difference calculus
(`addShift`, `addDiff`, and coprime neighbor orthogonality $\gcd(n, n+1) = 1$) directly to the
arithmetic weights $\mu(d)$, $\Lambda(n)$, $\psi(n)$, the Wall 1 dyadic Chebyshev difference
$D_\psi(n) = 2\psi(n/2) - \psi(n)$, and the discrete Nyquist-cell Chebyshev mean-square sum
`discreteChebyshevCellSum`:

1. **Exact Floor-Step Divisor Indicators & Coprime Neighbor Disjointness:**
   For the integer floor sequence `floorDivSeq d n = ⌊n / d⌋`, the unit additive step
   `addDiff (floorDivSeq d) n` is identically the divisor indicator $\mathbf{1}_{d \mid (n+1)}$.
   Because consecutive integers are coprime, for every divisor $d + 2 \ge 2$ the consecutive
   additive jumps have strictly disjoint support:
   $$\operatorname{addDiff}(\operatorname{floorDivSeq}(d+2))(n) \cdot
     \operatorname{addDiff}(\operatorname{floorDivSeq}(d+2))(n+1) = 0.$$
   Coupling `addDiff` to the Möbius floor summatory sequence identifies its forward difference with
   `truncMoebiusDivisorSum N (n + 1)`, which vanishes identically below the cutoff.
2. **Von Mangoldt Additive Shear of $\psi(n)$ and Parity-Split Shear of $2\psi(n/2) - \psi(n)$:**
   The unit additive difference of `chebyshevPsiSeq n = ψ(n)` is $\Lambda(n+1)$, matching the
   forward difference of the logarithmic Möbius floor sum below cutoff. For the dyadic Chebyshev
   difference `dyadicChebyshevDiffSeq n = 2ψ(n/2) - ψ(n)` governing the head of
   `logMobiusFermiErrorEnergy`, we prove the exact odd/even parity-split shear laws:
   - Odd step ($2m \mapsto 2m+1$): $\operatorname{addDiff}\,\operatorname{dyadicChebyshevDiffSeq}\,(2m) = -\Lambda(2m+1)$,
   - Even step ($2m+1 \mapsto 2m+2$): $\operatorname{addDiff}\,\operatorname{dyadicChebyshevDiffSeq}\,(2m+1) = 2\Lambda(m+1) - \Lambda(2m+2)$,
   - Two-step dyadic increment: $D_\psi(2m+2) - D_\psi(2m) = 2\Lambda(m+1) - \Lambda(2m+1) - \Lambda(2m+2)$.
3. **Exact Nyquist-Cell Abel Summation & Bilinear Von Mangoldt Increment Representation:**
   Using $\frac{1}{(k+1)(k+2)} = \frac{1}{k+1} - \frac{1}{k+2}$, we prove an exact discrete
   summation-by-parts (Abel) identity on the Nyquist cells and apply it to the integer-centered
   Chebyshev square $(\psi(k+1) - (k+1))^2$, expressing the cell sum in terms of the bilinear
   von Mangoldt shear increments $(\Lambda(k+2) - 1)(2(\psi(k+1)-(k+1)) + \Lambda(k+2) - 1)/(k+2)$
   and comparing it two-sidedly with `discreteChebyshevCellSum N`.
-/

open Complex MeasureTheory Set Filter Topology Finset
open Zeta23 RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector RHTower.WeilOneSided RHTower.WeilPoleWeight
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. Coupling Discrete Coprime Shear (`addDiff`) to Floor Sequences & Truncated Möbius Sums -/

/-- The integer floor-division sequence $\lfloor n / d \rfloor$ viewed in $\mathbb{R}$. -/
def floorDivSeq (d n : ℕ) : ℝ :=
  ((n / d : ℕ) : ℝ)

/-- Counting multiples of `d` in `Finset.Icc 1 n` recovers `n / d` unconditionally for all `d n : ℕ`. -/
theorem card_filter_dvd_Icc_eq_div (d n : ℕ) :
    (Finset.filter (fun k => d ∣ k) (Finset.Icc 1 n)).card = n / d := by
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]

/-- Exact integer division step: `(n + 1) / d = n / d + if d ∣ n + 1 then 1 else 0` for all `d n : ℕ`. -/
theorem succ_div_eq_add_ite_dvd (d n : ℕ) :
    (n + 1) / d = n / d + if d ∣ n + 1 then 1 else 0 := by
  classical
  rw [← card_filter_dvd_Icc_eq_div d (n + 1), ← card_filter_dvd_Icc_eq_div d n]
  have hins : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]
    omega
  rw [hins, Finset.filter_insert]
  split_ifs with hdvd
  · rw [Finset.card_insert_of_notMem (fun h => hnot (Finset.mem_of_mem_filter _ h))]
  · rw [add_zero]

/-- **Exact Divisor-Indicator Law for the Additive Difference of `floorDivSeq`:**
For EVERY `d n : ℕ` (with **zero hypotheses**!), the forward additive difference of `floorDivSeq d`
at `n` is the indicator of `d ∣ n + 1`:
$$\operatorname{addDiff}(\operatorname{floorDivSeq}\,d)(n)
  = \left\lfloor\frac{n+1}{d}\right\rfloor - \left\lfloor\frac{n}{d}\right\rfloor
  = \begin{cases} 1 & \text{if } d \mid (n+1), \\ 0 & \text{otherwise.} \end{cases}$$ -/
theorem addDiff_floorDivSeq_eq_ite_dvd (d n : ℕ) :
    addDiff (floorDivSeq d) n = if d ∣ n + 1 then 1 else 0 := by
  classical
  unfold addDiff floorDivSeq
  rw [succ_div_eq_add_ite_dvd d n]
  push_cast
  split_ifs <;> ring

/-- Every additive step of `floorDivSeq d` is idempotent (`0` or `1`), so its square equals itself. -/
theorem addDiff_floorDivSeq_sq_eq_self (d n : ℕ) :
    addDiff (floorDivSeq d) n ^ 2 = addDiff (floorDivSeq d) n := by
  classical
  rw [addDiff_floorDivSeq_eq_ite_dvd]
  split_ifs <;> ring

/-- **Unconditional Coprime Neighbor Disjointness of Floor Jumps
(`addDiff_floorDivSeq_mul_succ_eq_zero`):**
Because $\gcd(n+1, n+2) = 1$, no divisor $d + 2 \ge 2$ can divide both $n+1$ and $n+2$. Hence for
EVERY `d n : ℕ` (with **zero hypotheses**!), consecutive additive jumps of `floorDivSeq (d + 2)`
have strictly disjoint support:
$$\operatorname{addDiff}(\operatorname{floorDivSeq}(d + 2))(n) \cdot
  \operatorname{addDiff}(\operatorname{floorDivSeq}(d + 2))(n + 1) = 0.$$ -/
theorem addDiff_floorDivSeq_mul_succ_eq_zero (d n : ℕ) :
    addDiff (floorDivSeq (d + 2)) n * addDiff (floorDivSeq (d + 2)) (n + 1) = 0 := by
  classical
  rw [addDiff_floorDivSeq_eq_ite_dvd, addDiff_floorDivSeq_eq_ite_dvd]
  by_cases hdvd : d + 2 ∣ n + 1
  · have hnot : ¬ (d + 2 ∣ n + 1 + 1) := not_dvd_succ_of_dvd (by omega) hdvd
    rw [if_pos hdvd, if_neg hnot, mul_zero]
  · rw [if_neg hdvd, zero_mul]

/-- The general weighted floor summatory sequence $\sum_{d=1}^{N} c(d)\lfloor n / d \rfloor$. -/
def weightedFloorSumSeq (c : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, c d * floorDivSeq d n

/-- **Exact Divisor-Sum Law for the Additive Difference of Any Weighted Floor Sum:**
For EVERY `(c : ℕ → ℝ) (N n : ℕ)` (with **zero hypotheses**!), advancing `n ↦ n + 1` extracts the
truncated divisor sum of `c` over divisors of `n + 1`:
$$\operatorname{addDiff}(\operatorname{weightedFloorSumSeq}\,c\,N)(n)
  = \sum_{\substack{1 \le d \le N \\ d \mid (n+1)}} c(d).$$ -/
theorem addDiff_weightedFloorSumSeq_eq_sum_filter_dvd (c : ℕ → ℝ) (N n : ℕ) :
    addDiff (weightedFloorSumSeq c N) n =
      ∑ d ∈ Finset.filter (fun d => d ∣ n + 1) (Finset.Icc 1 N), c d := by
  classical
  unfold addDiff weightedFloorSumSeq
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h := addDiff_floorDivSeq_eq_ite_dvd d n
  unfold addDiff at h
  calc
    c d * floorDivSeq d (n + 1) - c d * floorDivSeq d n
        = c d * (floorDivSeq d (n + 1) - floorDivSeq d n) := by ring
    _ = c d * (if d ∣ n + 1 then 1 else 0) := by rw [h]
    _ = if d ∣ n + 1 then c d else 0 := by split_ifs <;> ring

/-- The Möbius floor summatory sequence $F_N(n) = \sum_{d=1}^{N} \mu(d)\lfloor n / d \rfloor$. -/
def moebiusFloorSumSeq (N n : ℕ) : ℝ :=
  weightedFloorSumSeq (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) N n

/-- `moebiusFloorSumSeq N n` equals the partial sum of `truncMoebiusDivisorSum N k` over `1 ≤ k ≤ n`. -/
theorem moebiusFloorSumSeq_eq_sum_truncMoebiusDivisorSum (N n : ℕ) :
    moebiusFloorSumSeq N n = ∑ k ∈ Finset.Icc 1 n, truncMoebiusDivisorSum N k :=
  sum_moebius_floor_eq_sum_trunc n N

/-- **Exact Möbius Shear Identity (`addDiff_moebiusFloorSumSeq_eq_truncMoebiusDivisorSum`):**
For EVERY `N n : ℕ` (with **zero hypotheses**!), the forward additive difference of
`moebiusFloorSumSeq N` at `n` is identically the truncated Möbius divisor sum at `n + 1`:
$$\operatorname{addDiff}(\operatorname{moebiusFloorSumSeq}\,N)(n)
  = \operatorname{truncMoebiusDivisorSum}\,N\,(n + 1).$$ -/
theorem addDiff_moebiusFloorSumSeq_eq_truncMoebiusDivisorSum (N n : ℕ) :
    addDiff (moebiusFloorSumSeq N) n = truncMoebiusDivisorSum N (n + 1) := by
  unfold moebiusFloorSumSeq truncMoebiusDivisorSum
  exact addDiff_weightedFloorSumSeq_eq_sum_filter_dvd _ N n

/-- **Unconditional Möbius Shear Annihilation Below the Cutoff:**
For EVERY `n k : ℕ` (with **zero hypotheses**!), at argument `n + 1 ≥ 1` and cutoff `n + k + 2 ≥ n + 2`,
the additive step of `moebiusFloorSumSeq (n + k + 2)` from `n + 1` to `n + 2` vanishes identically:
$$\operatorname{addDiff}(\operatorname{moebiusFloorSumSeq}(n + k + 2))(n + 1) = 0.$$ -/
theorem addDiff_moebiusFloorSumSeq_below_cutoff_eq_zero (n k : ℕ) :
    addDiff (moebiusFloorSumSeq (n + k + 2)) (n + 1) = 0 := by
  rw [addDiff_moebiusFloorSumSeq_eq_truncMoebiusDivisorSum,
    truncMoebiusDivisorSum_of_le (by omega) (by omega), if_neg (by omega)]

/-! ## §2. Coupling Coprime Shear to $\Lambda$, $\psi(n)$, and the Dyadic Chebyshev Difference $2\psi(n/2) - \psi(n)$ -/

/-- The discrete Chebyshev sequence `n ↦ ψ(n)`. -/
def chebyshevPsiSeq (n : ℕ) : ℝ :=
  Chebyshev.psi (n : ℝ)

/-- The discrete integer-centered Chebyshev error sequence `n ↦ ψ(n) - n`. -/
def chebyshevErrorSeq (n : ℕ) : ℝ :=
  Chebyshev.psi (n : ℝ) - (n : ℝ)

/-- The discrete Wall 1 dyadic Chebyshev difference sequence `n ↦ 2ψ(n/2) - ψ(n)`. -/
def dyadicChebyshevDiffSeq (n : ℕ) : ℝ :=
  2 * Chebyshev.psi ((n : ℝ) / 2) - Chebyshev.psi (n : ℝ)

/-- The logarithmic Möbius floor summatory sequence
$-\sum_{d=1}^{N} \mu(d)\log d \cdot \lfloor n / d \rfloor$. -/
def logMoebiusFloorSumSeq (N n : ℕ) : ℝ :=
  -weightedFloorSumSeq
    (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) N n

/-- Below the cutoff (`N = n + k`), `logMoebiusFloorSumSeq (n + k) n` equals `ψ(n)` unconditionally. -/
theorem logMoebiusFloorSumSeq_eq_chebyshevPsiSeq (n k : ℕ) :
    logMoebiusFloorSumSeq (n + k) n = chebyshevPsiSeq n := by
  unfold logMoebiusFloorSumSeq weightedFloorSumSeq floorDivSeq chebyshevPsiSeq
  have h := sum_moebius_log_mul_floor (n + k) (x := (n : ℝ)) (Nat.cast_nonneg n)
    (by rw [Nat.floor_natCast]; omega)
  have hcongr :
      (∑ d ∈ Finset.Icc 1 (n + k),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ)) =
      ∑ d ∈ Finset.Icc 1 (n + k),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (d : ℝ) *
          (⌊(n : ℝ) / (d : ℝ)⌋ : ℝ) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [real_floor_div_eq_nat_div d (Nat.cast_nonneg n), Nat.floor_natCast]
  rw [hcongr, h, neg_neg]

/-- **Unconditional Von Mangoldt Step Law (`addDiff_chebyshevPsiSeq`):**
For EVERY `n : ℕ` (with **zero hypotheses**!), the forward additive difference of `ψ(n)` is
$\Lambda(n + 1)$:
$$\operatorname{addDiff}\,\operatorname{chebyshevPsiSeq}\,n
  = \psi(n + 1) - \psi(n) = \Lambda(n + 1).$$ -/
theorem addDiff_chebyshevPsiSeq (n : ℕ) :
    addDiff chebyshevPsiSeq n = ArithmeticFunction.vonMangoldt (n + 1) := by
  classical
  unfold addDiff chebyshevPsiSeq Chebyshev.psi
  rw [Nat.floor_natCast, Nat.floor_natCast]
  have hins : Finset.Ioc 0 (n + 1) = insert (n + 1) (Finset.Ioc 0 n) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Ioc 0 n := by
    simp only [Finset.mem_Ioc]
    omega
  rw [hins, Finset.sum_insert hnot]
  ring

/-- **Unconditional Centered Chebyshev Step Law (`addDiff_chebyshevErrorSeq`):**
For EVERY `n : ℕ` (with **zero hypotheses**!),
$$\operatorname{addDiff}\,\operatorname{chebyshevErrorSeq}\,n
  = \bigl(\psi(n + 1) - (n + 1)\bigr) - \bigl(\psi(n) - n\bigr)
  = \Lambda(n + 1) - 1.$$ -/
theorem addDiff_chebyshevErrorSeq (n : ℕ) :
    addDiff chebyshevErrorSeq n = ArithmeticFunction.vonMangoldt (n + 1) - 1 := by
  have h := addDiff_chebyshevPsiSeq n
  unfold addDiff chebyshevPsiSeq at h
  unfold addDiff chebyshevErrorSeq
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  linarith [h, hcast]

/-- Below the cutoff (`N = n + k + 1`), the additive difference of the logarithmic Möbius floor
sum equals $\Lambda(n + 1)$ unconditionally. -/
theorem addDiff_logMoebiusFloorSumSeq_below_cutoff (n k : ℕ) :
    addDiff (logMoebiusFloorSumSeq (n + k + 1)) n =
      ArithmeticFunction.vonMangoldt (n + 1) := by
  unfold addDiff
  rw [show n + k + 1 = (n + 1) + k by omega,
    logMoebiusFloorSumSeq_eq_chebyshevPsiSeq (n + 1) k,
    show (n + 1) + k = n + (k + 1) by omega,
    logMoebiusFloorSumSeq_eq_chebyshevPsiSeq n (k + 1)]
  exact addDiff_chebyshevPsiSeq n

/-- At any odd integer `2 * m + 1`, $\psi((2m + 1) / 2) = \psi(m)$ because $\lfloor (2m + 1) / 2 \rfloor = m$. -/
theorem chebyshev_psi_odd_half_eq (m : ℕ) :
    Chebyshev.psi (((2 * m + 1 : ℕ) : ℝ) / 2) = Chebyshev.psi (m : ℝ) := by
  rw [Chebyshev.psi_eq_psi_coe_floor]
  have hfloor : ⌊((2 * m + 1 : ℕ) : ℝ) / 2⌋₊ = m := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> · push_cast; linarith
  rw [hfloor]

/-- At any even integer `2 * m`, $\psi((2m) / 2) = \psi(m)$. -/
theorem chebyshev_psi_even_half_eq (m : ℕ) :
    Chebyshev.psi (((2 * m : ℕ) : ℝ) / 2) = Chebyshev.psi (m : ℝ) := by
  have h : ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) := by push_cast; ring
  rw [h]

/-- **Unconditional Odd-Step Shear Law for the Wall 1 Dyadic Chebyshev Difference
(`addDiff_dyadicChebyshevDiffSeq_even`):**
For EVERY `m : ℕ` (with **zero hypotheses**!), stepping from the even integer `2 * m` to the odd
integer `2 * m + 1` leaves $\psi(x/2)$ unchanged and subtracts $\Lambda(2m + 1)$:
$$\operatorname{addDiff}\,\operatorname{dyadicChebyshevDiffSeq}\,(2m)
  = D_\psi(2m + 1) - D_\psi(2m) = -\Lambda(2m + 1).$$ -/
theorem addDiff_dyadicChebyshevDiffSeq_even (m : ℕ) :
    addDiff dyadicChebyshevDiffSeq (2 * m) =
      -ArithmeticFunction.vonMangoldt (2 * m + 1) := by
  have hpsi := addDiff_chebyshevPsiSeq (2 * m)
  unfold addDiff chebyshevPsiSeq at hpsi
  unfold addDiff dyadicChebyshevDiffSeq
  rw [chebyshev_psi_odd_half_eq m, chebyshev_psi_even_half_eq m]
  linarith

/-- **Unconditional Even-Step Shear Law for the Wall 1 Dyadic Chebyshev Difference
(`addDiff_dyadicChebyshevDiffSeq_odd`):**
For EVERY `m : ℕ` (with **zero hypotheses**!), stepping from the odd integer `2 * m + 1` to the
even integer `2 * m + 2` couples the half-scale jump $2\Lambda(m + 1)$ against the full-scale
jump $-\Lambda(2m + 2)$:
$$\operatorname{addDiff}\,\operatorname{dyadicChebyshevDiffSeq}\,(2m + 1)
  = D_\psi(2m + 2) - D_\psi(2m + 1) = 2\Lambda(m + 1) - \Lambda(2m + 2).$$ -/
theorem addDiff_dyadicChebyshevDiffSeq_odd (m : ℕ) :
    addDiff dyadicChebyshevDiffSeq (2 * m + 1) =
      2 * ArithmeticFunction.vonMangoldt (m + 1) -
        ArithmeticFunction.vonMangoldt (2 * m + 2) := by
  have hpsi_half := addDiff_chebyshevPsiSeq m
  have hpsi_full := addDiff_chebyshevPsiSeq (2 * m + 1)
  unfold addDiff chebyshevPsiSeq at hpsi_half hpsi_full
  unfold addDiff dyadicChebyshevDiffSeq
  have heven : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
  rw [heven, chebyshev_psi_even_half_eq (m + 1), chebyshev_psi_odd_half_eq m]
  rw [show 2 * (m + 1) = 2 * m + 2 by omega]
  rw [show 2 * m + 1 + 1 = 2 * m + 2 by omega] at hpsi_full
  linarith

/-- **Unconditional Two-Step Dyadic Cell Increment for $2\psi(n/2) - \psi(n)$:**
For EVERY `m : ℕ` (with **zero hypotheses**!),
$$D_\psi(2m + 2) - D_\psi(2m)
  = 2\Lambda(m + 1) - \Lambda(2m + 1) - \Lambda(2m + 2).$$ -/
theorem dyadicChebyshevDiffSeq_add_two_sub (m : ℕ) :
    dyadicChebyshevDiffSeq (2 * m + 2) - dyadicChebyshevDiffSeq (2 * m) =
      2 * ArithmeticFunction.vonMangoldt (m + 1) -
        ArithmeticFunction.vonMangoldt (2 * m + 1) -
        ArithmeticFunction.vonMangoldt (2 * m + 2) := by
  have h1 := addDiff_dyadicChebyshevDiffSeq_even m
  have h2 := addDiff_dyadicChebyshevDiffSeq_odd m
  unfold addDiff at h1 h2
  linarith

/-! ## §3. Bilinear Chebyshev Square Increment & Nyquist-Cell Abel Summation -/

/-- **Exact Bilinear Increment Law for the Squared Centered Chebyshev Error:**
For EVERY `n : ℕ` (with **zero hypotheses**!), the forward additive difference of
$(\psi(n) - n)^2$ is driven by the von Mangoldt shear $\Lambda(n + 1) - 1$:
$$\operatorname{addDiff}(\operatorname{chebyshevErrorSeq}^2)(n)
  = \bigl(\Lambda(n + 1) - 1\bigr)\bigl(2\,\operatorname{chebyshevErrorSeq}(n) + \Lambda(n + 1) - 1\bigr).$$ -/
theorem addDiff_chebyshevErrorSeq_sq (n : ℕ) :
    addDiff (fun k => chebyshevErrorSeq k ^ 2) n =
      (ArithmeticFunction.vonMangoldt (n + 1) - 1) *
        (2 * chebyshevErrorSeq n + (ArithmeticFunction.vonMangoldt (n + 1) - 1)) := by
  have hstep := addDiff_chebyshevErrorSeq n
  unfold addDiff at hstep ⊢
  dsimp only
  have h1 : chebyshevErrorSeq (n + 1) =
      chebyshevErrorSeq n + (ArithmeticFunction.vonMangoldt (n + 1) - 1) := by
    linarith [hstep]
  rw [h1]
  ring

/-- **Exact Discrete Summation-by-Parts (Abel) Identity on Nyquist Cells (`sum_nyquist_cell_weight_eq_abel`):**
Because the Nyquist cell weight satisfies $\frac{1}{(k+1)(k+2)} = \frac{1}{k+1} - \frac{1}{k+2}$,
for EVERY sequence `A : ℕ → ℝ` and cutoff `N : ℕ` (with **zero hypotheses**!),
$$\sum_{k \in \mathrm{range}(N+1)} \frac{A(k)}{(k+1)(k+2)}
  = A(0) - \frac{A(N)}{N+2} + \sum_{k \in \mathrm{range}\,N} \frac{\operatorname{addDiff}\,A\,k}{k+2}.$$ -/
theorem sum_nyquist_cell_weight_eq_abel (A : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      A k / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) =
      A 0 - A N / ((N + 2 : ℕ) : ℝ) +
        ∑ k ∈ Finset.range N, addDiff A k / ((k + 2 : ℕ) : ℝ) := by
  induction N with
  | zero =>
    simp only [Finset.range_one, Finset.sum_singleton, Finset.range_zero, Finset.sum_empty,
      Nat.zero_add, Nat.cast_one, Nat.cast_ofNat, add_zero]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ (n := N + 1), ih, Finset.sum_range_succ (n := N)]
    unfold addDiff
    have h1 : ((N + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 : ((N + 1 + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast at h1 h2 ⊢
    field_simp
    ring

/-- The integer-centered Nyquist-cell Chebyshev mean-square sum up to cutoff index `N`:
$$\operatorname{integerCenteredChebyshevCellSum}(N)
  := \sum_{k=0}^{N} \frac{(\psi(k+1) - (k+1))^2}{(k+1)(k+2)}.$$ -/
def integerCenteredChebyshevCellSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1),
    chebyshevErrorSeq (k + 1) ^ 2 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))

theorem chebyshevErrorSeq_one_sq : chebyshevErrorSeq 1 ^ 2 = 1 := by
  unfold chebyshevErrorSeq Chebyshev.psi
  rw [Nat.cast_one, Nat.floor_one]
  have h1 : Finset.Ioc 0 1 = {1} := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  rw [h1, Finset.sum_singleton]
  simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_sub, even_two, Even.neg_pow, one_pow]

/-- **Exact Von Mangoldt Shear Abel Decomposition of `integerCenteredChebyshevCellSum`:**
For EVERY `N : ℕ` (with **zero hypotheses**!), the integer-centered Nyquist-cell Chebyshev sum
is given identically by the boundary deficit plus the harmonic sum of bilinear von Mangoldt
shear increments:
$$\operatorname{integerCenteredChebyshevCellSum}(N)
  = 1 - \frac{(\psi(N+1) - (N+1))^2}{N+2}
    + \sum_{k=0}^{N-1} \frac{(\Lambda(k+2) - 1)\bigl(2(\psi(k+1) - (k+1)) + \Lambda(k+2) - 1\bigr)}{k+2}.$$ -/
theorem integerCenteredChebyshevCellSum_eq_vonMangoldt_shear_sum (N : ℕ) :
    integerCenteredChebyshevCellSum N =
      1 - chebyshevErrorSeq (N + 1) ^ 2 / ((N + 2 : ℕ) : ℝ) +
        ∑ k ∈ Finset.range N,
          ((ArithmeticFunction.vonMangoldt (k + 2) - 1) *
            (2 * chebyshevErrorSeq (k + 1) +
              (ArithmeticFunction.vonMangoldt (k + 2) - 1))) /
            ((k + 2 : ℕ) : ℝ) := by
  unfold integerCenteredChebyshevCellSum
  rw [sum_nyquist_cell_weight_eq_abel (fun k => chebyshevErrorSeq (k + 1) ^ 2) N,
    Nat.zero_add, chebyshevErrorSeq_one_sq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := addDiff_chebyshevErrorSeq_sq (k + 1)
  unfold addDiff at h ⊢
  rw [h]

/-- Telescoping Nyquist cell weights: $\sum_{k=0}^{N} \frac{1}{(k+1)(k+2)} \le 1$. -/
theorem sum_nyquist_cell_inv_le_one (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) ≤ 1 := by
  rw [sum_nyquist_cell_weight_eq_abel (fun _ => (1 : ℝ)) N]
  have hz : (∑ k ∈ Finset.range N, addDiff (fun _ => (1 : ℝ)) k / ((k + 2 : ℕ) : ℝ)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    unfold addDiff
    simp
  rw [hz, add_zero]
  have hpos : 0 ≤ (1 : ℝ) / ((N + 2 : ℕ) : ℝ) := by positivity
  linarith

/-- **Unconditional Upper Bound of `discreteChebyshevCellSum` by `integerCenteredChebyshevCellSum`:**
For EVERY `N : ℕ` (with **zero hypotheses**!), since the optimal cell center satisfies
$k + 1 \le m_{k+1} \le k + 2$,
$$\operatorname{discreteChebyshevCellSum}(N)
  \;\le\; 2\,\operatorname{integerCenteredChebyshevCellSum}(N) + 2.$$ -/
theorem discreteChebyshevCellSum_le_two_mul_integerCentered (N : ℕ) :
    discreteChebyshevCellSum N ≤ 2 * integerCenteredChebyshevCellSum N + 2 := by
  unfold discreteChebyshevCellSum integerCenteredChebyshevCellSum
  have hterm : ∀ k ∈ Finset.range (N + 1),
      (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ChebyshevGauge.cellCenter (k + 1)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) ≤
        2 * (chebyshevErrorSeq (k + 1) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) +
        2 * ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) := by
    intro k _
    have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have hc1 := ChebyshevGauge.le_cellCenter hk
    have hc2 := ChebyshevGauge.cellCenter_le hk
    have hdiff_sq : (ChebyshevGauge.cellCenter (k + 1) - ((k + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_le]
      constructor <;> linarith
    have hsq :
        (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ChebyshevGauge.cellCenter (k + 1)) ^ 2 ≤
          2 * chebyshevErrorSeq (k + 1) ^ 2 + 2 := by
      unfold chebyshevErrorSeq
      have hnonneg : 0 ≤ (chebyshevErrorSeq (k + 1) +
          (ChebyshevGauge.cellCenter (k + 1) - ((k + 1 : ℕ) : ℝ))) ^ 2 := sq_nonneg _
      unfold chebyshevErrorSeq at hnonneg
      linarith
    have hden : 0 < ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) := by positivity
    calc
      (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ChebyshevGauge.cellCenter (k + 1)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))
          ≤ (2 * chebyshevErrorSeq (k + 1) ^ 2 + 2) /
              (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) :=
        div_le_div_of_nonneg_right hsq hden.le
      _ = 2 * (chebyshevErrorSeq (k + 1) ^ 2 /
            (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) +
          2 * ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) := by ring
  calc
    (∑ k ∈ Finset.range (N + 1),
      (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ChebyshevGauge.cellCenter (k + 1)) ^ 2 /
        (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)))
        ≤ ∑ k ∈ Finset.range (N + 1),
            (2 * (chebyshevErrorSeq (k + 1) ^ 2 /
              (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) +
            2 * ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)))) :=
      Finset.sum_le_sum hterm
    _ = 2 * (∑ k ∈ Finset.range (N + 1),
          chebyshevErrorSeq (k + 1) ^ 2 /
            (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) +
        2 * (∑ k ∈ Finset.range (N + 1),
          (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (∑ k ∈ Finset.range (N + 1),
          chebyshevErrorSeq (k + 1) ^ 2 /
            (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) + 2 * 1 := by
      gcongr
      exact sum_nyquist_cell_inv_le_one N
    _ = _ := by ring

/-- The integer-centered Nyquist-cell gauge bound for `packetEnergy f N`, expressible directly via
the von Mangoldt shear sum `integerCenteredChebyshevCellSum_eq_vonMangoldt_shear_sum`:
$$\operatorname{integerCenteredGaugeBound}(f, N)
  := 3\bigl(10 + \tilde{E}(\operatorname{cutoff} N)^2\bigr)\,\operatorname{autocorr}(f, 0)
    + 6\left(\int_{\mathbb{R}} |f'(u) - f(u)/2|\,du\right)^2
      \bigl(\operatorname{integerCenteredChebyshevCellSum}(N) + 2\bigr).$$ -/
def integerCenteredGaugeBound (f : C_c(ℝ, ℝ)) (N : ℕ) : ℝ :=
  3 * (10 + ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) ^ 2) *
    autocorr f 0 +
  6 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
    (integerCenteredChebyshevCellSum N + 2)

theorem discreteCellGaugeBound_le_integerCenteredGaugeBound (f : C_c(ℝ, ℝ)) (N : ℕ) :
    discreteCellGaugeBound f N ≤ integerCenteredGaugeBound f N := by
  unfold discreteCellGaugeBound integerCenteredGaugeBound
  have h := discreteChebyshevCellSum_le_two_mul_integerCentered N
  have hmul :
      3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
          (discreteChebyshevCellSum N + 2) ≤
        6 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
          (integerCenteredChebyshevCellSum N + 2) := by
    have hpos : 0 ≤ (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 := sq_nonneg _
    nlinarith
  linarith only [hmul]

/-- **Unconditional Full Weil Functional Von Mangoldt Shear-Cell Lower Bound on `RealWeilTestFn`:**
For EVERY `f : RealWeilTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!), the full Weil
explicit-formula functional of `Λ` is bounded below by the integer-centered Chebyshev cell gauge
bound `integerCenteredGaugeBound` (whose cell sum expands into the von Mangoldt additive shear
increments via `integerCenteredChebyshevCellSum_eq_vonMangoldt_shear_sum`):
$$(1 - 2 e^c)\,\operatorname{biScaleLevyEnergy}(f.\mathrm{source})
  + \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
  - 2\,\operatorname{chebyshevWork}(f.\mathrm{toCompactlySupported}, a, b, f.\mathrm{supportScale})
  - \frac{\operatorname{integerCenteredGaugeBound}(f.\mathrm{toCompactlySupported}, f.\mathrm{supportScale})}{e^c e^{2b}}
    \int_{e^a}^{e^a + e^b} e^{-y/2}\sinh y\,dy$$
$$\le\; (\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}.$$ -/
theorem RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_integerCenteredGauge_lower_bound
    (f : RealWeilTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork f.toCompactlySupported a b f.supportScale -
        integerCenteredGaugeBound f.toCompactlySupported f.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re := by
  refine le_trans ?_
    (f.unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound a b c)
  have hint_pos :
      0 ≤ ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y := by
    refine intervalIntegral.integral_nonneg (by linarith [Real.exp_pos b]) fun y hy => ?_
    have hy_pos : 0 < y := lt_of_lt_of_le (Real.exp_pos a) hy.1
    exact mul_nonneg (Real.exp_pos _).le (Real.sinh_pos_iff.mpr hy_pos).le
  have hcell :
      discreteCellGaugeBound f.toCompactlySupported f.supportScale /
          (Real.exp c * Real.exp b ^ 2) *
        (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      integerCenteredGaugeBound f.toCompactlySupported f.supportScale /
          (Real.exp c * Real.exp b ^ 2) *
        (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) := by
    refine mul_le_mul_of_nonneg_right ?_ hint_pos
    exact div_le_div_of_nonneg_right
      (discreteCellGaugeBound_le_integerCenteredGaugeBound
        f.toCompactlySupported f.supportScale)
      (by positivity)
  linarith only [hcell]

end

end GaloisForLFunctions.BiScaleUncertainty
