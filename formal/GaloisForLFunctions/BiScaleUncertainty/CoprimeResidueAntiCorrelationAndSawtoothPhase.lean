import GaloisForLFunctions.BiScaleUncertainty.CoprimeShearArithmeticWeightsAndChebyshevCellIncrement
import GaloisForLFunctions.BiScaleUncertainty.FoldFreeKernelGramAndFranelGcdCancellation

/-!
# Pillar XXXIII: Coprime Residue Anti-Correlation ($\{n/d\} = 1 - 1/d$) & Sawtooth Phase Coupling to $\Lambda(n+1)$ and $\psi(n) - n$

This module develops **Component 2** of the FZZ-P / `BiScaleUncertainty` synthesis, resolving the
missing arithmetic mechanism behind sign-sensitive off-diagonal cancellation in the Nyquist-cell
Abel–Chebyshev shear sum:

1. **Exact Predecessor-Divisor Residue Anti-Correlation (`{n / (d + 1)} = 1 - 1 / (d + 1)`):**
   For the fractional-part sequence `fractDivSeq d n = {n / d}` on the divisor grid, stepping from
   $n$ to $n + 1$ shifts the phase by $1 / (d + 1)$ minus the divisor step indicator:
   $$\operatorname{addDiff}(\operatorname{fractDivSeq}(d + 1))(n)
     = \frac{1}{d + 1} - \operatorname{addDiff}(\operatorname{floorDivSeq}(d + 1))(n).$$
   Because $\gcd(n, n + 1) = 1$, whenever $(d + 1) \mid (n + 1)$ ($n = q(d + 1) + d$), the residue
   at the predecessor $n$ is **maximally close to $1$**:
   $$\left\{\frac{q(d + 1) + d}{d + 1}\right\} = 1 - \frac{1}{d + 1},
     \qquad \operatorname{centeredFract}\!\left(\frac{q(d + 1) + d}{d + 1}\right) = \frac{1}{2} - \frac{1}{d + 1}.$$
   Multiplying by the divisor step indicator yields the unconditional, hypothesis-free identity
   valid for all $d, n \in \mathbb{N}$:
   $$\operatorname{addDiff}(\operatorname{floorDivSeq}(d + 1))(n) \cdot \left\{\frac{n}{d + 1}\right\}
     = \operatorname{addDiff}(\operatorname{floorDivSeq}(d + 1))(n) \cdot \left(1 - \frac{1}{d + 1}\right).$$

2. **Coupling Coprime Residue Anti-Correlation to $\Lambda(n + 1)$, $\psi(n)$, and $\psi(n) - n$:**
   Summing the predecessor-phase identity against the von Mangoldt Dirichlet weight
   $w_\Lambda(d) = -\mu(d)\log d$ expresses the prime jump $\Lambda(n + 1)$ directly through the
   sawtooth phases $\{n / d\}$ at the predecessor $n$:
   $$\sum_{d=1}^{n+1} (-\mu(d)\log d)\,\operatorname{addDiff}(\operatorname{floorDivSeq}\,d)(n)\,\left\{\frac{n}{d}\right\}
     = \Lambda(n + 1) - \sum_{\substack{1 \le d \le n+1 \\ d \mid (n+1)}} \frac{-\mu(d)\log d}{d}.$$
   Simultaneously, the centered Chebyshev error `chebyshevErrorSeq n = ψ(n) - n` splits into the
   harmonic Möbius-log drift minus the sawtooth phase sum:
   $$\psi(n) - n = n\left(\sum_{d=1}^n \frac{-\mu(d)\log d}{d} - 1\right)
     - \sum_{d=1}^n (-\mu(d)\log d)\left\{\frac{n}{d}\right\},$$
   decomposing the Abel–Chebyshev cross-term $(\Lambda(n + 1) - 1)(\psi(n) - n)$ into its
   harmonic-drift and sawtooth-phase correlation components.
-/

open Complex MeasureTheory Set Filter Topology Finset
open RHTower
open scoped BigOperators ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ## §1. Exact Predecessor-Divisor Residue Anti-Correlation (`{n/d} = 1 - 1/d` for `d ∣ (n+1)`) -/

/-- The fractional-part sequence `fractDivSeq d n = {n / d}` on the divisor grid. -/
def fractDivSeq (d n : ℕ) : ℝ :=
  Int.fract ((n : ℝ) / (d : ℝ))

/-- Fundamental identity decomposing `(n : ℝ) / (d : ℝ)` into `floorDivSeq d n + fractDivSeq d n`
for all `n : ℕ` and positive divisor `d + 1`. -/
theorem natCast_div_succ_eq_floorDivSeq_add_fractDivSeq (d n : ℕ) :
    (n : ℝ) / ((d + 1 : ℕ) : ℝ) = floorDivSeq (d + 1) n + fractDivSeq (d + 1) n := by
  unfold fractDivSeq Int.fract floorDivSeq
  rw [real_floor_div_eq_nat_div (d + 1) (Nat.cast_nonneg n), Nat.floor_natCast]
  ring

/-- **Forward Additive Difference of the Fractional-Part Sequence (`addDiff_fractDivSeq_succ`):**
For every `d n : ℕ`, stepping `n ↦ n + 1` shifts `{n / (d + 1)}` by `1 / (d + 1)` minus the
divisor indicator `1_{(d+1) ∣ (n+1)}`:
`{(n + 1) / (d + 1)} - {n / (d + 1)} = 1 / (d + 1) - addDiff (floorDivSeq (d + 1)) n`. -/
theorem addDiff_fractDivSeq_succ (d n : ℕ) :
    addDiff (fractDivSeq (d + 1)) n =
      1 / ((d + 1 : ℕ) : ℝ) - addDiff (floorDivSeq (d + 1)) n := by
  unfold addDiff
  have h1 := natCast_div_succ_eq_floorDivSeq_add_fractDivSeq d (n + 1)
  have h2 := natCast_div_succ_eq_floorDivSeq_add_fractDivSeq d n
  have hdiff : (((n + 1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) - ((n : ℝ) / ((d + 1 : ℕ) : ℝ)) =
      1 / ((d + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  linarith

/-- At any exact multiple `q * (d + 1)`, the fractional part vanishes. -/
theorem fractDivSeq_mul_eq_zero (q d : ℕ) :
    fractDivSeq (d + 1) (q * (d + 1)) = 0 := by
  have h1 := natCast_div_succ_eq_floorDivSeq_add_fractDivSeq d (q * (d + 1))
  unfold floorDivSeq at h1
  have hdiv : (q * (d + 1)) / (d + 1) = q := Nat.mul_div_cancel q (Nat.succ_pos d)
  have hreal : (((q * (d + 1) : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) = (q : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_div_cancel_right₀ (q : ℝ) (by positivity)
  rw [hdiv, hreal] at h1
  linarith

/-- **Explicit Coprime Predecessor Residue Law on Multiples (`fract_pred_mul_eq_one_sub_inv`):**
At the predecessor `n = q * (d + 1) + d = (q + 1)(d + 1) - 1` of any multiple of `d + 1`,
the fractional part is identically `1 - 1 / (d + 1)`. -/
theorem fract_pred_mul_eq_one_sub_inv (q d : ℕ) :
    fractDivSeq (d + 1) (q * (d + 1) + d) = 1 - 1 / ((d + 1 : ℕ) : ℝ) := by
  have hstep := addDiff_fractDivSeq_succ d (q * (d + 1) + d)
  have hdvd : d + 1 ∣ (q * (d + 1) + d + 1) := ⟨q + 1, by ring⟩
  have hfl := addDiff_floorDivSeq_eq_ite_dvd (d + 1) (q * (d + 1) + d)
  rw [if_pos hdvd] at hfl
  rw [hfl] at hstep
  unfold addDiff at hstep
  have hsucc : q * (d + 1) + d + 1 = (q + 1) * (d + 1) := by ring
  rw [hsucc, fractDivSeq_mul_eq_zero (q + 1) d] at hstep
  linarith

/-- **Centered Franel Sawtooth Phase at a Predecessor of a Multiple:**
At `n = q * (d + 1) + d`, the centered Franel sawtooth `centeredFract (n / (d + 1)) = {n / (d + 1)} - 1/2`
equals `1/2 - 1/(d + 1)`. -/
theorem centeredFract_pred_mul_eq_half_sub_inv (q d : ℕ) :
    centeredFract (((q * (d + 1) + d : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) =
      1 / 2 - 1 / ((d + 1 : ℕ) : ℝ) := by
  unfold centeredFract
  change fractDivSeq (d + 1) (q * (d + 1) + d) - 1 / 2 = _
  rw [fract_pred_mul_eq_one_sub_inv]
  ring

/-- **Unconditional Coprime Residue Anti-Correlation Identity (`addDiff_floor_mul_fract_eq`):**
For EVERY `d n : ℕ` (with **zero hypotheses**!), multiplying the divisor step indicator
`addDiff (floorDivSeq (d + 1)) n` by the predecessor fractional part `fractDivSeq (d + 1) n`
replaces `{n / (d + 1)}` with the deterministic residue `1 - 1 / (d + 1)`:
`addDiff (floorDivSeq (d + 1)) n * fractDivSeq (d + 1) n =
  addDiff (floorDivSeq (d + 1)) n * (1 - 1 / (d + 1))`. -/
theorem addDiff_floor_mul_fract_eq (d n : ℕ) :
    addDiff (floorDivSeq (d + 1)) n * fractDivSeq (d + 1) n =
      addDiff (floorDivSeq (d + 1)) n * (1 - 1 / ((d + 1 : ℕ) : ℝ)) := by
  classical
  by_cases hdvd : d + 1 ∣ n + 1
  · obtain ⟨q, hq⟩ := hdvd
    rcases q with _ | q
    · omega
    · have hmul : (d + 1) * (q + 1) = q * (d + 1) + d + 1 := by ring
      have hn : n = q * (d + 1) + d := by omega
      rw [hn, fract_pred_mul_eq_one_sub_inv]
  · have hfl := addDiff_floorDivSeq_eq_ite_dvd (d + 1) n
    rw [if_neg hdvd] at hfl
    rw [hfl, zero_mul, zero_mul]

/-! ## §2. Coupling Coprime Residue Anti-Correlation to `Λ(n+1)` and `ψ(n) - n` -/

/-- The weighted fractional-part sum `∑_{d=1}^N w(d) {n / d}`. -/
def weightedFractSumSeq (w : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, w d * fractDivSeq d n

/-- **Unconditional Decomposition of Any Weighted Floor Sum into Harmonic Drift Minus Sawtooth Phase:**
For every `w : ℕ → ℝ` and `N n : ℕ`,
`weightedFloorSumSeq w N n = n * (∑_{d=1}^N w(d)/d) - weightedFractSumSeq w N n`. -/
theorem weightedFloorSumSeq_eq_harmonic_sub_fractSum (w : ℕ → ℝ) (N n : ℕ) :
    weightedFloorSumSeq w N n =
      (n : ℝ) * (∑ d ∈ Finset.Icc 1 N, w d / (d : ℝ)) - weightedFractSumSeq w N n := by
  unfold weightedFloorSumSeq weightedFractSumSeq
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
  have hd_eq : d = (d - 1) + 1 := by omega
  have hdecomp := natCast_div_succ_eq_floorDivSeq_add_fractDivSeq (d - 1) n
  rw [← hd_eq] at hdecomp
  calc
    w d * floorDivSeq d n = w d * ((n : ℝ) / (d : ℝ) - fractDivSeq d n) := by
      congr 1; linarith
    _ = (n : ℝ) * (w d / (d : ℝ)) - w d * fractDivSeq d n := by ring

/-- **Unconditional Predecessor-Phase Divisor Sum Law:**
Weighting the active divisor jumps at `n ↦ n + 1` by the predecessor fractional part `{n / d}`
extracts the divisor sum of `w(d) * (1 - 1 / d)` over divisors of `n + 1`. -/
theorem sum_addDiff_floor_mul_fract_eq_filter_dvd (w : ℕ → ℝ) (N n : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, w d * (addDiff (floorDivSeq d) n * fractDivSeq d n)) =
      (∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ (n + 1)), w d) -
        ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ (n + 1)), w d / (d : ℝ) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
  have hd_eq : d = (d - 1) + 1 := by omega
  have hanti := addDiff_floor_mul_fract_eq (d - 1) n
  rw [← hd_eq] at hanti
  rw [hanti, addDiff_floorDivSeq_eq_ite_dvd]
  split_ifs <;> ring

/-- The von Mangoldt Dirichlet weight `w_Λ(d) = -μ(d) log d`. -/
def vonMangoldtDivisorWeight (d : ℕ) : ℝ :=
  -((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (d : ℝ)

/-- `weightedFloorSumSeq vonMangoldtDivisorWeight N n` equals `logMoebiusFloorSumSeq N n`. -/
theorem weightedFloorSumSeq_vonMangoldt_eq_logMoebius (N n : ℕ) :
    weightedFloorSumSeq vonMangoldtDivisorWeight N n = logMoebiusFloorSumSeq N n := by
  simp only [weightedFloorSumSeq, logMoebiusFloorSumSeq, vonMangoldtDivisorWeight,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => by ring

/-- **Unconditional Predecessor-Sawtooth Representation of `Λ(n + 1)`:**
For every `n : ℕ`, summing `(-μ(d) log d) * addDiff(floorDivSeq d)(n) * {n / d}` over `1 ≤ d ≤ n + 1`
equals `Λ(n + 1)` minus the harmonic divisor sum `∑_{d ∣ (n+1)} (-μ(d) log d) / d`. -/
theorem vonMangoldt_succ_eq_predecessor_fract_sum_add_harmonic (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 (n + 1),
      vonMangoldtDivisorWeight d * (addDiff (floorDivSeq d) n * fractDivSeq d n)) =
    Λ (n + 1) -
      ∑ d ∈ (Finset.Icc 1 (n + 1)).filter (fun d => d ∣ (n + 1)),
        vonMangoldtDivisorWeight d / (d : ℝ) := by
  rw [sum_addDiff_floor_mul_fract_eq_filter_dvd]
  congr 1
  rw [← addDiff_weightedFloorSumSeq_eq_sum_filter_dvd]
  have h1 : weightedFloorSumSeq vonMangoldtDivisorWeight (n + 1) =
      logMoebiusFloorSumSeq (n + 0 + 1) := by
    funext m
    simpa using weightedFloorSumSeq_vonMangoldt_eq_logMoebius (n + 1) m
  rw [h1, addDiff_logMoebiusFloorSumSeq_below_cutoff n 0]

/-- **Unconditional Sawtooth Phase Decomposition of `ψ(n)` (`chebyshevPsiSeq_eq_harmonic_sub_fractSum`):**
For every `n : ℕ`, the Chebyshev function `ψ(n)` decomposes into `n` times the partial harmonic
sum `∑_{d=1}^n (-μ(d) log d)/d` minus the sawtooth phase sum `∑_{d=1}^n (-μ(d) log d) {n / d}`. -/
theorem chebyshevPsiSeq_eq_harmonic_sub_fractSum (n : ℕ) :
    chebyshevPsiSeq n =
      (n : ℝ) * (∑ d ∈ Finset.Icc 1 n, vonMangoldtDivisorWeight d / (d : ℝ)) -
        weightedFractSumSeq vonMangoldtDivisorWeight n n := by
  have h := logMoebiusFloorSumSeq_eq_chebyshevPsiSeq n 0
  rw [Nat.add_zero] at h
  rw [← h, ← weightedFloorSumSeq_vonMangoldt_eq_logMoebius]
  exact weightedFloorSumSeq_eq_harmonic_sub_fractSum vonMangoldtDivisorWeight n n

/-- **Unconditional Sawtooth Phase Decomposition of the Centered Chebyshev Error `ψ(n) - n`:**
For every `n : ℕ`, `chebyshevErrorSeq n = ψ(n) - n` splits into the harmonic Möbius-log drift
plus the sawtooth phase sum:
`ψ(n) - n = n * (∑_{d=1}^n (-μ(d) log d)/d - 1) - ∑_{d=1}^n (-μ(d) log d) {n / d}`. -/
theorem chebyshevErrorSeq_eq_harmonic_drift_sub_fractSum (n : ℕ) :
    chebyshevErrorSeq n =
      (n : ℝ) * ((∑ d ∈ Finset.Icc 1 n, vonMangoldtDivisorWeight d / (d : ℝ)) - 1) -
        weightedFractSumSeq vonMangoldtDivisorWeight n n := by
  unfold chebyshevErrorSeq
  change chebyshevPsiSeq n - (n : ℝ) = _
  rw [chebyshevPsiSeq_eq_harmonic_sub_fractSum]
  ring

/-- **Bilinear Sawtooth-Phase Decomposition of the Abel–Chebyshev Cross-Term:**
In the Nyquist-cell Abel summation identity, the cross-term `(Λ(n + 1) - 1) * (ψ(n) - n)` decomposes
into the harmonic-drift product minus the sawtooth-phase correlation `(Λ(n + 1) - 1) * Φ_{fract}(n)`. -/
theorem abelChebyshevCrossTerm_eq_harmonic_drift_sub_fract_correlation (n : ℕ) :
    (Λ (n + 1) - 1) * chebyshevErrorSeq n =
      (Λ (n + 1) - 1) * ((n : ℝ) *
        ((∑ d ∈ Finset.Icc 1 n, vonMangoldtDivisorWeight d / (d : ℝ)) - 1)) -
      (Λ (n + 1) - 1) * weightedFractSumSeq vonMangoldtDivisorWeight n n := by
  rw [chebyshevErrorSeq_eq_harmonic_drift_sub_fractSum]
  ring

end GaloisForLFunctions.BiScaleUncertainty
