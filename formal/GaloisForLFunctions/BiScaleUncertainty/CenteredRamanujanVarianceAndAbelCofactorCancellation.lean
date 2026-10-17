import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanTransfer
import GaloisForLFunctions.RHTower.PMRamanujanJointResidue
import GaloisForLFunctions.BiScaleUncertainty.CoprimeResidueAntiCorrelationAndSawtoothPhase

/-!
# Centered Ramanujan Variance, Discrete Bernoulli Sawtooth & Dyadic Cofactor Transfer

This module resolves **Item 1 + Item 2** on the `FZZ-P` / `Route PM` power-damped Möbius and
Ramanujan-variance chain by replacing the uncentered triangle inequality on `{N / d}` in
`PMPowerDampedMobiusRamanujanAbsolute` with three exact structural mechanisms:

1. **Centered Discrete Bernoulli Sawtooth & Coprime Predecessor Sign-Flip (§1):**
   For every divisor $d \ge 1$, the discrete sawtooth $\{n / d\} = (n \bmod d) / d$ has exact
   complete-period average $\frac{d - 1}{2d}$. Subtracting this mean defines the zero-mean
   discrete Bernoulli sawtooth
   $$\widetilde{B}_1(d, n) := \left\{\frac{n}{d}\right\} - \frac{d - 1}{2d},$$
   which vanishes identically at $d = 1$, has exact zero sum over every complete period
   $0 \le r < d$, satisfies $|\widetilde{B}_1(d, n)| \le \frac{d - 1}{2d} < \frac{1}{2}$, and
   undergoes an **exact sign flip** across every divisibility step $d \mid (n + 1)$:
   $$\widetilde{B}_1(d, n) = +\frac{d - 1}{2d}, \qquad
     \widetilde{B}_1(d, n + 1) = -\frac{d - 1}{2d}, \qquad
     \widetilde{B}_1(d, n) + \widetilde{B}_1(d, n + 1) = 0.$$

2. **Exact Decomposition of `pmPowerDampedRamanujanCumulativePrefix` & Dyadic Transfer Bridge (§2):**
   - Decomposing `{N / d}` into $\frac{d - 1}{2d} + \widetilde{B}_1(d, N)$ splits
     `(pmPowerDampedRamanujanCumulativePrefix ε Q N).re` into the constant complete-period bias
     `pmPowerDampedRamanujanPeriodMean ε Q` plus the zero-mean sawtooth prefix
     `pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N` (whose $d = 1$ mode vanishes identically).
   - Forming the dyadic difference $N \mapsto 2N$ of `pmPowerDampedRamanujanCumulativePrefix ε Q`
     recovers the Fermi generator $\varphi_d(1/(2N)) = \{2N/d\} - 2\{N/d\}$, yielding the **exact
     dyadic bridge identity** to `pmPowerDampedRamanujanFermiPrefix` and its multiplicative transfer
     convolution `pmPowerDampedRamanujanTransfer`:
     $$\operatorname{pmPowerDampedRamanujanCumulativePrefix}\,\varepsilon\,Q\,(2N)
       - 2\,\operatorname{pmPowerDampedRamanujanCumulativePrefix}\,\varepsilon\,Q\,N
       = \operatorname{pmPowerDampedRamanujanFermiPrefix}\,\varepsilon\,(Q + 1)\,\left(\frac{1}{2N}\right).$$

3. **Reciprocal-vs-Cesàro Centering Bridge & Variational Optimality of `pmPowerDampedRamanujanEnergyVariance` (§3):**
   - For each modulus $q \ge 2$, the difference between the Cesàro period-centered primitive
     `pmRamanujanMeanCenteredPrimitive q N = Re P_q(N) + φ(q)/2` and the reciprocal energy-centered
     primitive `pmRamanujanEnergyCenteredPrimitive q N = Re P_q(N) + Λ(q)` is the constant
     discrepancy $\Delta(q) = \frac{\varphi(q)}{2} - \Lambda(q)$.
   - Because `pmRamanujanEnergyCenteredPrimitive q` has exact zero $\frac{1}{N(N+1)}$-mean and
     $\sum_{N=1}^\infty \frac{1}{N(N+1)} = 1$, the two Gram matrices differ by an **exact rank-one
     positive semidefinite matrix**:
     $$\operatorname{pmRamanujanMeanCenteredGram}(p, q)
       = \operatorname{pmRamanujanEnergyCenteredGram}(p, q)
         + \left(\frac{\varphi(p)}{2} - \Lambda(p)\right)\left(\frac{\varphi(q)}{2} - \Lambda(q)\right).$$
   - Consequently, the quadratic form of `pmRamanujanMeanCenteredGram` equals
     `pmPowerDampedRamanujanEnergyVariance ε Q` plus a single non-negative square, and for **every**
     trial constant $c \in \mathbb{R}$ (in particular $c = \operatorname{pmPowerDampedRamanujanPeriodMean}\,\varepsilon\,Q$),
     $$\operatorname{pmPowerDampedRamanujanEnergyVariance}(\varepsilon, Q)
       \le \sum_{N=1}^\infty \frac{\bigl((\operatorname{pmPowerDampedRamanujanCumulativePrefix}\,\varepsilon\,Q\,N).\mathrm{re} - c\bigr)^2}{N(N+1)}.$$
-/

open MeasureTheory Set Filter Topology Complex Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. Centered Discrete Bernoulli Sawtooth & Coprime Predecessor Sign-Flip Law -/

/-- The **centered discrete Bernoulli sawtooth** at modulus `d` and integer argument `n`:
$$\widetilde{B}_1(d, n) := \left\{\frac{n}{d}\right\} - \frac{d - 1}{2d}.$$ -/
def centeredDiscreteSawtooth (d n : ℕ) : ℝ :=
  Int.fract ((n : ℝ) / (d : ℝ)) - ((d : ℝ) - 1) / (2 * (d : ℝ))

/-- At modulus `d = 1`, the centered discrete sawtooth vanishes identically for all `n : ℕ`. -/
@[simp]
theorem centeredDiscreteSawtooth_one (n : ℕ) :
    centeredDiscreteSawtooth 1 n = 0 := by
  unfold centeredDiscreteSawtooth
  simp [Int.fract_natCast]

/-- For every `d > 0` and `n : ℕ`, `Int.fract ((n : ℝ) / (d : ℝ)) = ((n % d : ℕ) : ℝ) / (d : ℝ)`. -/
theorem int_fract_natCast_div_eq_mod_div {d : ℕ} (hd : 0 < d) (n : ℕ) :
    Int.fract ((n : ℝ) / (d : ℝ)) = ((n % d : ℕ) : ℝ) / (d : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [Int.fract, real_floor_div_eq_nat_div d (Nat.cast_nonneg n), Nat.floor_natCast]
  have hmod : ((n % d : ℕ) : ℝ) + (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.mod_add_div n d
  field_simp [hdR]
  linarith

/-- Explicit residue formula: for `d > 0`,
$$\widetilde{B}_1(d, n) = \frac{(n \bmod d) - \frac{d - 1}{2}}{d}.$$ -/
theorem centeredDiscreteSawtooth_eq_mod_sub_half {d : ℕ} (hd : 0 < d) (n : ℕ) :
    centeredDiscreteSawtooth d n =
      (((n % d : ℕ) : ℝ) - ((d : ℝ) - 1) / 2) / (d : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  unfold centeredDiscreteSawtooth
  rw [int_fract_natCast_div_eq_mod_div hd n]
  field_simp [hdR]

/-- Whenever `d ∣ n` and `d > 0`, the centered discrete sawtooth takes its minimum value
$-(d - 1) / (2d)$. -/
theorem centeredDiscreteSawtooth_of_dvd {d n : ℕ} (hd : 0 < d) (hdvd : d ∣ n) :
    centeredDiscreteSawtooth d n = -(((d : ℝ) - 1) / (2 * (d : ℝ))) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [centeredDiscreteSawtooth_eq_mod_sub_half hd n, Nat.mod_eq_zero_of_dvd hdvd]
  field_simp [hdR]
  ring

/-- **Predecessor Lock for `centeredDiscreteSawtooth`:**
Whenever `d ∣ n` with `d > 0` and `n > 0`, at the predecessor `n - 1` the centered discrete
sawtooth is locked at its maximum value $+(d - 1) / (2d)$. -/
theorem centeredDiscreteSawtooth_pred_of_dvd {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hdvd : d ∣ n) :
    centeredDiscreteSawtooth d (n - 1) = ((d : ℝ) - 1) / (2 * (d : ℝ)) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  obtain ⟨k, rfl⟩ := hdvd
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hpred : d * (m + 1) - 1 = (d - 1) + d * m := by
    rw [Nat.mul_succ]
    omega
  have hmod : (d * (m + 1) - 1) % d = d - 1 := by
    rw [hpred, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.sub_lt hd zero_lt_one)]
  rw [centeredDiscreteSawtooth_eq_mod_sub_half hd (d * (m + 1) - 1), hmod,
    Nat.cast_sub hd, Nat.cast_one]
  field_simp [hdR]
  ring

/-- **Coprime Predecessor Sign-Flip Law:**
Across any divisibility step `d ∣ (n + 1)` (`d > 0`), the centered discrete sawtooth flips sign
from $+\frac{d-1}{2d}$ at `n` to $-\frac{d-1}{2d}$ at `n + 1`, so their sum vanishes identically:
$$\widetilde{B}_1(d, n) + \widetilde{B}_1(d, n + 1) = 0.$$ -/
theorem centeredDiscreteSawtooth_pred_add_self_of_dvd {d n : ℕ}
    (hd : 0 < d) (hdvd : d ∣ (n + 1)) :
    centeredDiscreteSawtooth d n + centeredDiscreteSawtooth d (n + 1) = 0 := by
  have hpred : centeredDiscreteSawtooth d n = ((d : ℝ) - 1) / (2 * (d : ℝ)) :=
    centeredDiscreteSawtooth_pred_of_dvd hd (Nat.succ_pos n) hdvd
  have hself := centeredDiscreteSawtooth_of_dvd hd hdvd
  rw [hpred, hself, add_neg_cancel]

/-- Across any divisibility step `d ∣ (n + 1)` (`d > 0`), the jump of the centered discrete
sawtooth is `1 - 1 / d`. -/
theorem centeredDiscreteSawtooth_pred_sub_self_of_dvd {d n : ℕ}
    (hd : 0 < d) (hdvd : d ∣ (n + 1)) :
    centeredDiscreteSawtooth d n - centeredDiscreteSawtooth d (n + 1) = 1 - 1 / (d : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hpred : centeredDiscreteSawtooth d n = ((d : ℝ) - 1) / (2 * (d : ℝ)) :=
    centeredDiscreteSawtooth_pred_of_dvd hd (Nat.succ_pos n) hdvd
  have hself := centeredDiscreteSawtooth_of_dvd hd hdvd
  rw [hpred, hself]
  field_simp [hdR]
  ring

/-- **Sharp Two-Sided Amplitude Bound:**
For every `d > 0` and `n : ℕ`,
$$|\widetilde{B}_1(d, n)| \le \frac{d - 1}{2d} < \frac{1}{2}.$$ -/
theorem abs_centeredDiscreteSawtooth_le {d : ℕ} (hd : 0 < d) (n : ℕ) :
    |centeredDiscreteSawtooth d n| ≤ ((d : ℝ) - 1) / (2 * (d : ℝ)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hmod_lt : (n % d : ℕ) < d := Nat.mod_lt n hd
  have hmod_le : ((n % d : ℕ) : ℝ) ≤ (d : ℝ) - 1 := by
    have : (n % d : ℕ) + 1 ≤ d := hmod_lt
    have hcast : ((n % d : ℕ) : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast this
    linarith
  have hmod_nonneg : (0 : ℝ) ≤ ((n % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have habs : |((n % d : ℕ) : ℝ) - ((d : ℝ) - 1) / 2| ≤ ((d : ℝ) - 1) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [centeredDiscreteSawtooth_eq_mod_sub_half hd n, abs_div, abs_of_pos hdR]
  calc
    |((n % d : ℕ) : ℝ) - ((d : ℝ) - 1) / 2| / (d : ℝ)
      ≤ (((d : ℝ) - 1) / 2) / (d : ℝ) := div_le_div_of_nonneg_right habs hdR.le
    _ = ((d : ℝ) - 1) / (2 * (d : ℝ)) := by ring

theorem abs_centeredDiscreteSawtooth_lt_half {d : ℕ} (hd : 0 < d) (n : ℕ) :
    |centeredDiscreteSawtooth d n| < 1 / 2 := by
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  calc
    |centeredDiscreteSawtooth d n| ≤ ((d : ℝ) - 1) / (2 * (d : ℝ)) :=
      abs_centeredDiscreteSawtooth_le hd n
    _ < (d : ℝ) / (2 * (d : ℝ)) := by
      apply div_lt_div_of_pos_right (by linarith) (by positivity)
    _ = 1 / 2 := by field_simp [hdR.ne']

/-- **Complete-Period Zero-Mean Law:**
For every `d > 0`, summing `centeredDiscreteSawtooth d r` over `r ∈ Finset.range d` vanishes
identically. -/
theorem sum_centeredDiscreteSawtooth_range_eq_zero {d : ℕ} (hd : 0 < d) :
    (∑ r ∈ Finset.range d, centeredDiscreteSawtooth d r) = 0 := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hterm : ∀ r ∈ Finset.range d,
      centeredDiscreteSawtooth d r = ((r : ℝ) - ((d : ℝ) - 1) / 2) / (d : ℝ) := by
    intro r hr
    rw [centeredDiscreteSawtooth_eq_mod_sub_half hd r,
      Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_sub_distrib]
  have hgauss : (∑ r ∈ Finset.range d, (r : ℝ)) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
    have hnat := Finset.sum_range_id d
    have hmul : 2 * (∑ r ∈ Finset.range d, r) = d * (d - 1) := by
      rw [hnat, Nat.mul_div_cancel' (Nat.even_mul_pred_self d).two_dvd]
    have hcast : ((2 * ∑ r ∈ Finset.range d, r : ℕ) : ℝ) = ((d * (d - 1) : ℕ) : ℝ) := by
      exact_mod_cast hmul
    have hd1 : (1 : ℕ) ≤ d := hd
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_mul, Nat.cast_sub hd1,
      Nat.cast_one] at hcast
    linarith
  rw [hgauss, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-! ## §2. Exact Decomposition of `pmPowerDampedRamanujanCumulativePrefix` & Dyadic Transfer Bridge -/

/-- The constant complete-period bias of `pmPowerDampedRamanujanCumulativePrefix ε Q`:
$$\operatorname{pmPowerDampedRamanujanPeriodMean}(\varepsilon, Q)
  := -\sum_{d=1}^{Q+1} \operatorname{Re} W_{\varepsilon, Q+1}(d)\,\frac{d - 1}{2d}.$$ -/
def pmPowerDampedRamanujanPeriodMean (ε : ℝ) (Q : ℕ) : ℝ :=
  -∑ d ∈ Finset.Icc 1 (Q + 1),
    (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re * (((d : ℝ) - 1) / (2 * (d : ℝ)))

/-- The zero-mean periodic sawtooth part of `pmPowerDampedRamanujanCumulativePrefix ε Q N`:
$$\operatorname{pmPowerDampedRamanujanCenteredSawtoothPrefix}(\varepsilon, Q, N)
  := -\sum_{d=1}^{Q+1} \operatorname{Re} W_{\varepsilon, Q+1}(d)\,\widetilde{B}_1(d, N).$$ -/
def pmPowerDampedRamanujanCenteredSawtoothPrefix (ε : ℝ) (Q N : ℕ) : ℝ :=
  -∑ d ∈ Finset.Icc 1 (Q + 1),
    (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re * centeredDiscreteSawtooth d N

/-- Real-part cofactor-sawtooth expansion of `pmPowerDampedRamanujanCumulativePrefix ε Q N`. -/
theorem pmPowerDampedRamanujanCumulativePrefix_re_eq_cofactor_fract
    {ε : ℝ} (hε : 0 < ε) (Q N : ℕ) :
    (pmPowerDampedRamanujanCumulativePrefix ε Q N).re =
      -∑ d ∈ Finset.Icc 1 (Q + 1),
        (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re *
          Int.fract ((N : ℝ) / (d : ℝ)) := by
  have h := congrArg Complex.re (pmPowerDampedRamanujanCumulativePrefix_eq_cofactor_fract hε Q N)
  simpa only [Complex.neg_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] using h

/-- **Exact Decomposition into Period Mean + Zero-Mean Bernoulli Sawtooth Prefix:**
For every `ε > 0` and `Q N : ℕ`,
$$(\operatorname{pmPowerDampedRamanujanCumulativePrefix}\,\varepsilon\,Q\,N).\mathrm{re}
  = \operatorname{pmPowerDampedRamanujanPeriodMean}\,\varepsilon\,Q
    + \operatorname{pmPowerDampedRamanujanCenteredSawtoothPrefix}\,\varepsilon\,Q\,N.$$ -/
theorem pmPowerDampedRamanujanCumulativePrefix_re_eq_periodMean_add_centeredSawtooth
    {ε : ℝ} (hε : 0 < ε) (Q N : ℕ) :
    (pmPowerDampedRamanujanCumulativePrefix ε Q N).re =
      pmPowerDampedRamanujanPeriodMean ε Q +
        pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N := by
  rw [pmPowerDampedRamanujanCumulativePrefix_re_eq_cofactor_fract hε Q N]
  unfold pmPowerDampedRamanujanPeriodMean pmPowerDampedRamanujanCenteredSawtoothPrefix
    centeredDiscreteSawtooth
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Because `centeredDiscreteSawtooth 1 N = 0`, the `d = 1` mode drops out of
`pmPowerDampedRamanujanCenteredSawtoothPrefix` identically, and its amplitude is halved relative
to the uncentered sawtooth bound. -/
theorem pmPowerDampedRamanujanCenteredSawtoothPrefix_eq_sum_Icc_two
    (ε : ℝ) (Q N : ℕ) :
    pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N =
      -∑ d ∈ Finset.Icc 2 (Q + 1),
        (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re * centeredDiscreteSawtooth d N := by
  unfold pmPowerDampedRamanujanCenteredSawtoothPrefix
  congr 1
  have hsplit : Finset.Icc 1 (Q + 1) = insert 1 (Finset.Icc 2 (Q + 1)) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  simp [centeredDiscreteSawtooth_one]

/-- **Halved-Amplitude Bound on the Centered Sawtooth Prefix (`d ≥ 2`):**
For every `ε > 0` and `Q N : ℕ`,
$$|\operatorname{pmPowerDampedRamanujanCenteredSawtoothPrefix}\,\varepsilon\,Q\,N|
  \le \frac{1}{2} \sum_{d=2}^{Q+1} d^{-\varepsilon}.$$ -/
theorem abs_pmPowerDampedRamanujanCenteredSawtoothPrefix_le
    {ε : ℝ} (hε : 0 < ε) (Q N : ℕ) :
    |pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N| ≤
      (1 / 2 : ℝ) * ∑ d ∈ Finset.Icc 2 (Q + 1), (d : ℝ) ^ (-ε) := by
  rw [pmPowerDampedRamanujanCenteredSawtoothPrefix_eq_sum_Icc_two, abs_neg]
  calc
    |∑ d ∈ Finset.Icc 2 (Q + 1),
        (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re * centeredDiscreteSawtooth d N|
      ≤ ∑ d ∈ Finset.Icc 2 (Q + 1),
          |(pmPowerDampedRamanujanCofactor ε (Q + 1) d).re * centeredDiscreteSawtooth d N| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 2 (Q + 1), (1 / 2 : ℝ) * (d : ℝ) ^ (-ε) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd_pos : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
      rw [abs_mul]
      have hcof : |(pmPowerDampedRamanujanCofactor ε (Q + 1) d).re| ≤ (d : ℝ) ^ (-ε) :=
        (Complex.abs_re_le_norm _).trans (norm_pmPowerDampedRamanujanCofactor_le hε (Q + 1) hd_pos)
      have hsaw : |centeredDiscreteSawtooth d N| ≤ 1 / 2 :=
        (abs_centeredDiscreteSawtooth_lt_half hd_pos N).le
      calc
        |(pmPowerDampedRamanujanCofactor ε (Q + 1) d).re| * |centeredDiscreteSawtooth d N|
          ≤ (d : ℝ) ^ (-ε) * (1 / 2) :=
          mul_le_mul hcof hsaw (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
        _ = (1 / 2 : ℝ) * (d : ℝ) ^ (-ε) := by ring
    _ = (1 / 2 : ℝ) * ∑ d ∈ Finset.Icc 2 (Q + 1), (d : ℝ) ^ (-ε) := by
      rw [Finset.mul_sum]

/-- At `t = 1 / (2N)` (`N > 0`), the Fermi generator `fermiNymanGen d (1 / (2N))` equals the
dyadic fractional-part difference `{2N / d} - 2{N / d}`. -/
theorem fermiNymanGen_inv_two_mul_nat {N : ℕ} (hN : 0 < N) (d : ℕ) :
    fermiNymanGen (d : ℝ) (1 / (2 * (N : ℝ))) =
      ((Int.fract ((2 * N : ℕ) / (d : ℝ)) : ℝ) : ℂ) -
        2 * ((Int.fract ((N : ℝ) / (d : ℝ)) : ℝ) : ℂ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  unfold fermiNymanGen nymanGen
  rcases eq_or_ne (d : ℝ) 0 with hd0 | hd0
  · simp [hd0]
  · have h1 : 1 / ((d : ℝ) * (1 / (2 * (N : ℝ)))) = ((2 * N : ℕ) : ℝ) / (d : ℝ) := by
      push_cast
      field_simp [hd0, hNR.ne']
    have h2 : 1 / (2 * (d : ℝ) * (1 / (2 * (N : ℝ)))) = (N : ℝ) / (d : ℝ) := by
      field_simp [hd0, hNR.ne']
    rw [h1, h2]

/-- **Exact Dyadic Difference Bridge (`pmPowerDampedRamanujanCumulativePrefix` ↔ `pmPowerDampedRamanujanFermiPrefix`):**
For every `ε > 0`, `Q : ℕ`, and `N > 0`, the dyadic difference of
`pmPowerDampedRamanujanCumulativePrefix ε Q` between `2N` and `N` equals
`pmPowerDampedRamanujanFermiPrefix ε (Q + 1)` evaluated at `t = 1 / (2N)`:
$$\operatorname{pmPowerDampedRamanujanCumulativePrefix}\,\varepsilon\,Q\,(2N)
  - 2\,\operatorname{pmPowerDampedRamanujanCumulativePrefix}\,\varepsilon\,Q\,N
  = \operatorname{pmPowerDampedRamanujanFermiPrefix}\,\varepsilon\,(Q + 1)\,\left(\frac{1}{2N}\right).$$ -/
theorem pmPowerDampedRamanujanCumulativePrefix_dyadic_diff_eq_fermiPrefix
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) {N : ℕ} (hN : 0 < N) :
    pmPowerDampedRamanujanCumulativePrefix ε Q (2 * N) -
        2 * pmPowerDampedRamanujanCumulativePrefix ε Q N =
      pmPowerDampedRamanujanFermiPrefix ε (Q + 1) (1 / (2 * (N : ℝ))) := by
  rw [pmPowerDampedRamanujanCumulativePrefix_eq_cofactor_fract hε Q (2 * N),
    pmPowerDampedRamanujanCumulativePrefix_eq_cofactor_fract hε Q N]
  unfold pmPowerDampedRamanujanFermiPrefix
  simp_rw [fermiNymanGen_inv_two_mul_nat hN]
  rw [mul_neg, sub_neg_eq_add, Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_left_comm (2 : ℂ)]
  ring

/-- Combining `pmPowerDampedRamanujanCumulativePrefix_dyadic_diff_eq_fermiPrefix` with
`pmPowerDampedRamanujanFermiPrefix_eq_transfer` expresses the dyadic difference of the Ramanujan
cumulative prefix directly in terms of the damped Möbius Fermi prefixes
`pmPowerDampedFermiPrefix ε`. -/
theorem pmPowerDampedRamanujanCumulativePrefix_dyadic_diff_eq_transfer
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) {N : ℕ} (hN : 0 < N) :
    pmPowerDampedRamanujanCumulativePrefix ε Q (2 * N) -
        2 * pmPowerDampedRamanujanCumulativePrefix ε Q N =
      ∑ m ∈ Finset.Icc 1 (Q + 1), ∑ r ∈ Finset.Icc 1 ((Q + 1) / m),
        pmPowerDampedRamanujanTransfer ε m r *
          pmPowerDampedFermiPrefix ε ((Q + 1) / (m * r)) ((r : ℝ) * (1 / (2 * (N : ℝ)))) := by
  rw [pmPowerDampedRamanujanCumulativePrefix_dyadic_diff_eq_fermiPrefix hε Q hN,
    pmPowerDampedRamanujanFermiPrefix_eq_transfer]

/-! ## §3. Reciprocal-vs-Cesàro Centering Bridge & Variational Optimality of `pmPowerDampedRamanujanEnergyVariance` -/

/-- The **Cesàro-to-Reciprocal Centering Discrepancy** for modulus `q`:
$$\Delta_{\mathrm{cent}}(q) := \frac{\varphi(q)}{2} - \Lambda(q).$$ -/
def ramanujanCenteringDiscrepancy (q : ℕ) : ℝ :=
  (q.totient : ℝ) / 2 - vonMangoldt q

/-- Pointwise relation between the Cesàro period-centered primitive and the reciprocal
energy-centered primitive:
$$P_q^{\mathrm{mean}}(N) - P_q^{\mathrm{energy}}(N) = \frac{\varphi(q)}{2} - \Lambda(q).$$ -/
theorem pmRamanujanMeanCenteredPrimitive_sub_energyCentered (q N : ℕ) :
    pmRamanujanMeanCenteredPrimitive q N - pmRamanujanEnergyCenteredPrimitive q N =
      ramanujanCenteringDiscrepancy q := by
  unfold pmRamanujanMeanCenteredPrimitive pmRamanujanEnergyCenteredPrimitive
    ramanujanCenteringDiscrepancy
  ring

/-- **Exact Rank-One Bridge Between Mean-Centered and Energy-Centered Gram Matrices:**
For all `p > 1` and `q > 1`, the Cesàro period-centered Gram matrix `pmRamanujanMeanCenteredGram`
and the reciprocal energy-centered Gram matrix `pmRamanujanEnergyCenteredGram` differ by the
exact rank-one product of `ramanujanCenteringDiscrepancy`:
$$\operatorname{pmRamanujanMeanCenteredGram}(p, q)
  = \operatorname{pmRamanujanEnergyCenteredGram}(p, q)
    + \left(\frac{\varphi(p)}{2} - \Lambda(p)\right)\left(\frac{\varphi(q)}{2} - \Lambda(q)\right).$$ -/
theorem pmRamanujanMeanCenteredGram_eq_energyCentered_add_rankOne
    {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    pmRamanujanMeanCenteredGram p q =
      pmRamanujanEnergyCenteredGram p q +
        ramanujanCenteringDiscrepancy p * ramanujanCenteringDiscrepancy q := by
  have h1 := pmRamanujanPrimitiveGram_eq_meanCentered hp hq
  have h2 := pmRamanujanPrimitiveGram_eq_energyCentered hp hq
  unfold ramanujanCenteringDiscrepancy
  linarith

/-- Bilinear expansion of `pmPowerDampedRamanujanEnergyVariance ε Q` in terms of the centered
Gram matrix `pmRamanujanEnergyCenteredGram`. -/
theorem pmPowerDampedRamanujanEnergyVariance_eq_centeredGram_quadratic
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    pmPowerDampedRamanujanEnergyVariance ε Q =
      ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
        (pmPowerDampedRamanujanWeight ε (p + 2)).re *
          (pmPowerDampedRamanujanWeight ε (q + 2)).re *
            pmRamanujanEnergyCenteredGram (p + 2) (q + 2) := by
  have hdecomp := pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_variance hε Q
  have hgram : pmPowerDampedRamanujanGramQuadratic ε Q =
      pmPowerDampedRamanujanEnergyMean ε Q ^ 2 +
        ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
          (pmPowerDampedRamanujanWeight ε (p + 2)).re *
            (pmPowerDampedRamanujanWeight ε (q + 2)).re *
              pmRamanujanEnergyCenteredGram (p + 2) (q + 2) := by
    unfold pmPowerDampedRamanujanGramQuadratic pmPowerDampedRamanujanEnergyMean
    have hterm : ∀ p ∈ Finset.range Q, ∀ q ∈ Finset.range Q,
        (pmPowerDampedRamanujanWeight ε (p + 2)).re *
          (pmPowerDampedRamanujanWeight ε (q + 2)).re *
            pmRamanujanPrimitiveGram (p + 2) (q + 2) =
        ((pmPowerDampedRamanujanWeight ε (p + 2)).re * vonMangoldt (p + 2)) *
          ((pmPowerDampedRamanujanWeight ε (q + 2)).re * vonMangoldt (q + 2)) +
        (pmPowerDampedRamanujanWeight ε (p + 2)).re *
          (pmPowerDampedRamanujanWeight ε (q + 2)).re *
            pmRamanujanEnergyCenteredGram (p + 2) (q + 2) := by
      intro p _ q _
      rw [pmRamanujanPrimitiveGram_eq_energyCentered (by omega : 1 < p + 2) (by omega : 1 < q + 2)]
      ring
    calc
      (∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
          (pmPowerDampedRamanujanWeight ε (p + 2)).re *
            (pmPowerDampedRamanujanWeight ε (q + 2)).re *
              pmRamanujanPrimitiveGram (p + 2) (q + 2))
        = ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
            (((pmPowerDampedRamanujanWeight ε (p + 2)).re * vonMangoldt (p + 2)) *
              ((pmPowerDampedRamanujanWeight ε (q + 2)).re * vonMangoldt (q + 2)) +
            (pmPowerDampedRamanujanWeight ε (p + 2)).re *
              (pmPowerDampedRamanujanWeight ε (q + 2)).re *
                pmRamanujanEnergyCenteredGram (p + 2) (q + 2)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact Finset.sum_congr rfl (hterm p hp)
      _ = (∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
            ((pmPowerDampedRamanujanWeight ε (p + 2)).re * vonMangoldt (p + 2)) *
              ((pmPowerDampedRamanujanWeight ε (q + 2)).re * vonMangoldt (q + 2))) +
          ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
            (pmPowerDampedRamanujanWeight ε (p + 2)).re *
              (pmPowerDampedRamanujanWeight ε (q + 2)).re *
                pmRamanujanEnergyCenteredGram (p + 2) (q + 2) := by
          simp only [Finset.sum_add_distrib]
      _ = (-∑ q ∈ Finset.range Q, (pmPowerDampedRamanujanWeight ε (q + 2)).re * vonMangoldt (q + 2)) ^ 2 +
          ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
            (pmPowerDampedRamanujanWeight ε (p + 2)).re *
              (pmPowerDampedRamanujanWeight ε (q + 2)).re *
                pmRamanujanEnergyCenteredGram (p + 2) (q + 2) := by
          rw [neg_sq, pow_two, Finset.sum_mul_sum]
  linarith

/-- The quadratic form of the Cesàro period-centered Gram matrix `pmRamanujanMeanCenteredGram`: -/
def pmPowerDampedRamanujanMeanCenteredQuadratic (ε : ℝ) (Q : ℕ) : ℝ :=
  ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
    (pmPowerDampedRamanujanWeight ε (p + 2)).re *
      (pmPowerDampedRamanujanWeight ε (q + 2)).re *
        pmRamanujanMeanCenteredGram (p + 2) (q + 2)

/-- The weighted centering discrepancy sum across `2 ≤ q ≤ Q + 1`: -/
def pmPowerDampedRamanujanDiscrepancySum (ε : ℝ) (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.range Q,
    (pmPowerDampedRamanujanWeight ε (q + 2)).re * ramanujanCenteringDiscrepancy (q + 2)

/-- **Rank-One Quadratic Decomposition (`MeanCenteredQuadratic = EnergyVariance + DiscrepancySum²`):**
For every `ε > 0` and `Q : ℕ`,
$$\operatorname{pmPowerDampedRamanujanMeanCenteredQuadratic}(\varepsilon, Q)
  = \operatorname{pmPowerDampedRamanujanEnergyVariance}(\varepsilon, Q)
    + \bigl(\operatorname{pmPowerDampedRamanujanDiscrepancySum}(\varepsilon, Q)\bigr)^2.$$ -/
theorem pmPowerDampedRamanujanMeanCenteredQuadratic_eq_variance_add_discrepancy_sq
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    pmPowerDampedRamanujanMeanCenteredQuadratic ε Q =
      pmPowerDampedRamanujanEnergyVariance ε Q +
        pmPowerDampedRamanujanDiscrepancySum ε Q ^ 2 := by
  rw [pmPowerDampedRamanujanEnergyVariance_eq_centeredGram_quadratic hε Q]
  unfold pmPowerDampedRamanujanMeanCenteredQuadratic pmPowerDampedRamanujanDiscrepancySum
  have hterm : ∀ p ∈ Finset.range Q, ∀ q ∈ Finset.range Q,
      (pmPowerDampedRamanujanWeight ε (p + 2)).re *
        (pmPowerDampedRamanujanWeight ε (q + 2)).re *
          pmRamanujanMeanCenteredGram (p + 2) (q + 2) =
      (pmPowerDampedRamanujanWeight ε (p + 2)).re *
        (pmPowerDampedRamanujanWeight ε (q + 2)).re *
          pmRamanujanEnergyCenteredGram (p + 2) (q + 2) +
      ((pmPowerDampedRamanujanWeight ε (p + 2)).re * ramanujanCenteringDiscrepancy (p + 2)) *
        ((pmPowerDampedRamanujanWeight ε (q + 2)).re * ramanujanCenteringDiscrepancy (q + 2)) := by
    intro p _ q _
    rw [pmRamanujanMeanCenteredGram_eq_energyCentered_add_rankOne
      (by omega : 1 < p + 2) (by omega : 1 < q + 2)]
    ring
  calc
    (∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
        (pmPowerDampedRamanujanWeight ε (p + 2)).re *
          (pmPowerDampedRamanujanWeight ε (q + 2)).re *
            pmRamanujanMeanCenteredGram (p + 2) (q + 2))
      = ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
          ((pmPowerDampedRamanujanWeight ε (p + 2)).re *
            (pmPowerDampedRamanujanWeight ε (q + 2)).re *
              pmRamanujanEnergyCenteredGram (p + 2) (q + 2) +
          ((pmPowerDampedRamanujanWeight ε (p + 2)).re * ramanujanCenteringDiscrepancy (p + 2)) *
            ((pmPowerDampedRamanujanWeight ε (q + 2)).re * ramanujanCenteringDiscrepancy (q + 2))) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_congr rfl (hterm p hp)
    _ = (∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
          (pmPowerDampedRamanujanWeight ε (p + 2)).re *
            (pmPowerDampedRamanujanWeight ε (q + 2)).re *
              pmRamanujanEnergyCenteredGram (p + 2) (q + 2)) +
        (∑ q ∈ Finset.range Q,
          (pmPowerDampedRamanujanWeight ε (q + 2)).re * ramanujanCenteringDiscrepancy (q + 2)) ^ 2 := by
        simp only [Finset.sum_add_distrib, pow_two, Finset.sum_mul_sum]

/-- **Mean-Centered Upper Bound on `pmPowerDampedRamanujanEnergyVariance`:**
Because the centering discrepancy contributes a non-negative rank-one square, the reciprocal-energy
variance is always bounded above by the Cesàro period-centered quadratic form:
$$\operatorname{pmPowerDampedRamanujanEnergyVariance}(\varepsilon, Q)
  \le \operatorname{pmPowerDampedRamanujanMeanCenteredQuadratic}(\varepsilon, Q).$$ -/
theorem pmPowerDampedRamanujanEnergyVariance_le_meanCenteredQuadratic
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    pmPowerDampedRamanujanEnergyVariance ε Q ≤
      pmPowerDampedRamanujanMeanCenteredQuadratic ε Q := by
  rw [pmPowerDampedRamanujanMeanCenteredQuadratic_eq_variance_add_discrepancy_sq hε Q]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- **General Variational Optimality of `pmPowerDampedRamanujanEnergyVariance`:**
For any trial constant `c : ℝ`, the reciprocal-weighted second moment around `c` converges to
`pmPowerDampedRamanujanEnergyVariance ε Q + (c - pmPowerDampedRamanujanEnergyMean ε Q)^2`. -/
theorem hasSum_pmPowerDampedRamanujanShiftedVariance
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) (c : ℝ) :
    HasSum (fun N : ℕ =>
      ((pmPowerDampedRamanujanCumulativePrefix ε Q N).re - c) ^ 2 /
        ((N : ℝ) * ((N : ℝ) + 1)))
      (pmPowerDampedRamanujanEnergyVariance ε Q +
        (c - pmPowerDampedRamanujanEnergyMean ε Q) ^ 2) := by
  have h1 := hasSum_pmPowerDampedRamanujanEnergyTerm hε Q
  have h2 := (hasSum_pmPowerDampedRamanujanCumulativeMean hε Q).mul_left (2 * c)
  have h3 := hasSum_pm_reciprocal_weight.mul_left (c ^ 2)
  have hcomb := (h1.sub h2).add h3
  have hval : pmPowerDampedRamanujanGramQuadratic ε Q -
      2 * c * pmPowerDampedRamanujanEnergyMean ε Q + c ^ 2 * 1 =
      pmPowerDampedRamanujanEnergyVariance ε Q +
        (c - pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 := by
    rw [pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_variance hε Q]
    ring
  rw [hval] at hcomb
  apply hcomb.congr_fun
  intro N
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    pmPowerDampedRamanujanCumulativePrefix_im hε]
  ring

/-- For every trial constant `c : ℝ`, `pmPowerDampedRamanujanEnergyVariance ε Q` is bounded above
by the reciprocal-weighted second moment around `c`:
$$\operatorname{pmPowerDampedRamanujanEnergyVariance}(\varepsilon, Q)
  \le \sum_{N=0}^\infty \frac{\bigl((\operatorname{pmPowerDampedRamanujanCumulativePrefix}\,\varepsilon\,Q\,N).\mathrm{re} - c\bigr)^2}{N(N+1)}.$$ -/
theorem pmPowerDampedRamanujanEnergyVariance_le_shifted_tsum
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) (c : ℝ) :
    pmPowerDampedRamanujanEnergyVariance ε Q ≤
      ∑' N : ℕ, ((pmPowerDampedRamanujanCumulativePrefix ε Q N).re - c) ^ 2 /
        ((N : ℝ) * ((N : ℝ) + 1)) := by
  rw [(hasSum_pmPowerDampedRamanujanShiftedVariance hε Q c).tsum_eq]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Specializing `pmPowerDampedRamanujanEnergyVariance_le_shifted_tsum` to the complete-period mean
`c = pmPowerDampedRamanujanPeriodMean ε Q` bounds `pmPowerDampedRamanujanEnergyVariance ε Q`
directly by the reciprocal-weighted energy of the zero-mean periodic sawtooth prefix
`pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N`! -/
theorem pmPowerDampedRamanujanEnergyVariance_le_centeredSawtooth_tsum
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    pmPowerDampedRamanujanEnergyVariance ε Q ≤
      ∑' N : ℕ, (pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N) ^ 2 /
        ((N : ℝ) * ((N : ℝ) + 1)) := by
  have h := pmPowerDampedRamanujanEnergyVariance_le_shifted_tsum hε Q
    (pmPowerDampedRamanujanPeriodMean ε Q)
  refine h.trans_eq ?_
  apply tsum_congr
  intro N
  rw [pmPowerDampedRamanujanCumulativePrefix_re_eq_periodMean_add_centeredSawtooth hε Q N,
    add_sub_cancel_left]

end

end GaloisForLFunctions.BiScaleUncertainty
