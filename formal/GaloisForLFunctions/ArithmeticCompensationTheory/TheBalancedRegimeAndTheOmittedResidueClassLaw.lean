import GaloisForLFunctions.BezoutValuationIncidence.OmittedResidueClassLawOfThePrimeRow
import GaloisForLFunctions.BezoutValuationIncidence.DualNormOfTheActualRowsBeatsTheLargeSieve
import GaloisForLFunctions.BezoutValuationIncidence.ShortWindowPrimeSavingIsTheQuasiRiemannHypothesis
import GaloisForLFunctions.BezoutValuationIncidence.LittlewoodAdmitsTheReceiverAboveHalfTheZeroAbscissa
import GaloisForLFunctions.ArithmeticCompensationTheory.TheSeventeenThirtiethsWindowWidensTheCentredPrimeRowRange

/-!
# The balanced regime and the omitted-residue-class law of the centred prime block

This module resolves the cross-scale incidence problem for the actual centred prime and Möbius blocks
in the balanced regime `Q ≍ P`, keeping the omitted-residue-class main term and separating
unconditional qualitative block mean-square savings from a uniform bound for the complete coupled
receiver below half damping.

1. **The omitted-residue-class law survives centring (`tendsto_mul_kernelStatistic_centredPrimeBlock`).**
   Decomposing the centred prime block as `centredPrimeBlock Q = primeWindowRow Q - flatWindowRow Q`,
   the flat block `𝟙_{(Q, 2Q]}` has single-modulus kernel statistic bounded by `3p³/(2Q²)`
   (`abs_kernelStatistic_flatWindowRow_le`) because `𝔅(p, ·) - m_p` is `p`-periodic with zero period
   mean. Consequently `Q · Λ_p(flatWindowRow Q) → 0`, and `centredPrimeBlock Q` retains the exact
   non-vanishing omitted-residue-class limit of the uncentred prime row:
   `Q · Λ_p(centredPrimeBlock Q) → -π²(p² - 1)²/(144 p² (p - 1))`.
   Centring `Λ` by `1` kills the total block mass `S'(Q) = Σ_{Q<n≤2Q} (Λ(n) - 1)/n²` (and therefore
   the rank-one `equidistributedMain`), while preserving 100% of the omitted-residue-class main term
   in each single-modulus statistic `Λ_p`.

2. **The omitted-residue-class sieve corrector (`omittedClassCorrector`).**
   The `p`-periodic zero-mean weight assigning `1` to `n ≡ 0 (mod p)` and `-1/(p - 1)` to coprime
   residues on `(Q, 2Q]` has block mass `O(p/Q²)` (`abs_sum_omittedClassCorrector_div_sq_le`) and
   single-modulus statistic `+π²(p² - 1)²/(144 p² (p - 1) Q) + O(p³/Q²)`. Adding it to
   `centredPrimeBlock Q` cancels the omitted-residue-class main term (`Q · Λ_p → 0`) while keeping
   the block centred.

3. **Block-mass elimination and the `17/30` short-window transfer
   (`abs_sum_Icc_div_sq_le_of_shortWindowAverage`,
   `eventually_abs_rowBilinear_centredPrimeBlock_le_seventeenThirtieths`).**
   Because the short-window average `x̄` preserves the total sum of `x(n) = c'(n)/n²` and is supported
   on `Q + H ≤ 2Q` points, Cauchy–Schwarz bounds the block mass directly by `√(2Q) ‖x̄‖₂`. Feeding the
   uniform Guth–Maynard short-window prime theorem (`α > 17/30`) into the short-window mean-square
   transfer widens `CentredPrimeBlockBeatsTheLargeSieve` and
   `DualNormOfTheActualRowsBeatsTheLargeSieve` to every `17/30 < α < 1` and eliminates the
   previously unestimated block-mass terms `|Σ (Λ(n) - 1)/n²|` and `|moebiusBlockMass Q|` in favor of
   `√2 ε / Q`.

4. **Uniform balanced-regime bounds (`exists_balanced_centredPrimeBlock_rowBilinear_le`,
   `exists_balanced_centredPrimeBlock_dualNorm_le`).**
   In the balanced regime `P ≤ Q ≤ B P` with small primes `S ⊆ (P, 2P]`, choosing `α = 2/3 > 17/30`
   discharges the small-prime threshold `8⌈(2Q)^α⌉(log 2Q + 1)² ≤ ε² p` automatically for all large
   `P`, yielding unconditional `o(1)` savings over the large-sieve barrier for both the bilinear form
   and the single-modulus dual norm.

5. **Block mean-square estimates versus the complete coupled receiver
   (`primePowerWindowSaving_iff_receiverDampingRate_lt_half`,
   `moebiusPowerWindowSaving_iff_receiverDampingRate_lt_half`).**
   While qualitative `o(1)` short-window mean-square saving holds unconditionally on every dyadic
   block at `Q ≍ P`, upgrading the short-window mean square to a power saving at any fixed exponent
   `α ∈ (0, 1)` is equivalent to `receiverDampingRate < 1 / 2` (admission of the complete coupled
   receiver below half damping) and to the quasi-Riemann hypothesis `Θ < 1`.
-/

open Finset Filter Topology RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BezoutValuationIncidence
open ArithmeticFunction (vonMangoldt)
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## §1. Periodic sequences with zero period mean and the omitted-residue-class law -/

/-- Telescoping of first differences on `Ioc D X` when `D < X`. -/
theorem sum_Ioc_sub_succ (w : ℕ → ℝ) {D X : ℕ} (hDX : D < X) :
    ∑ d ∈ Ioc D X, (w d - w (d + 1)) = w (D + 1) - w (X + 1) := by
  induction X, hDX using Nat.le_induction with
  | base => simp
  | succ X hDX ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih]
    ring

/-- **Abel summation with uniformly bounded partial sums.** If `|Σ_{1 ≤ e ≤ x} s(e)| ≤ C` for
`D ≤ x ≤ X` and `w ≥ 0` is antitone beyond `D`, then `|Σ_{D < d ≤ X} s(d) w(d)| ≤ 2 C w(D + 1)`. -/
theorem abs_sum_Ioc_mul_le_of_bdd_partialSums {s w : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) {D X : ℕ}
    (hDX : D ≤ X) (hS : ∀ x, D ≤ x → x ≤ X → |∑ e ∈ Icc 1 x, s e| ≤ C)
    (hw0 : ∀ d, 0 ≤ w d) (hwa : ∀ d, D < d → w (d + 1) ≤ w d) :
    |∑ d ∈ Ioc D X, s d * w d| ≤ 2 * C * w (D + 1) := by
  rcases eq_or_lt_of_le hDX with rfl | hlt
  · simp only [Ioc_self, sum_empty, abs_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hC) (hw0 _)
  rw [sum_Ioc_mul_eq_partialSums s w hDX]
  have h1 : |(∑ e ∈ Icc 1 X, s e) * w (X + 1)| ≤ C * w (X + 1) := by
    rw [abs_mul, abs_of_nonneg (hw0 _)]
    exact mul_le_mul_of_nonneg_right (hS X hDX le_rfl) (hw0 _)
  have h2 : |(∑ e ∈ Icc 1 D, s e) * w (D + 1)| ≤ C * w (D + 1) := by
    rw [abs_mul, abs_of_nonneg (hw0 _)]
    exact mul_le_mul_of_nonneg_right (hS D le_rfl hDX) (hw0 _)
  have h3 : |∑ d ∈ Ioc D X, (∑ e ∈ Icc 1 d, s e) * (w d - w (d + 1))| ≤
      C * (w (D + 1) - w (X + 1)) := by
    calc |∑ d ∈ Ioc D X, (∑ e ∈ Icc 1 d, s e) * (w d - w (d + 1))|
        ≤ ∑ d ∈ Ioc D X, |(∑ e ∈ Icc 1 d, s e) * (w d - w (d + 1))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc D X, C * (w d - w (d + 1)) := by
          refine sum_le_sum fun d hd => ?_
          have hd' := mem_Ioc.mp hd
          have hwd : 0 ≤ w d - w (d + 1) := sub_nonneg.mpr (hwa d hd'.1)
          rw [abs_mul, abs_of_nonneg hwd]
          exact mul_le_mul_of_nonneg_right (hS d hd'.1.le hd'.2) hwd
      _ = C * (w (D + 1) - w (X + 1)) := by
          rw [← mul_sum, sum_Ioc_sub_succ w hlt]
  have ha := abs_add_le ((∑ e ∈ Icc 1 X, s e) * w (X + 1) - (∑ e ∈ Icc 1 D, s e) * w (D + 1))
    (∑ d ∈ Ioc D X, (∑ e ∈ Icc 1 d, s e) * (w d - w (d + 1)))
  have hb := abs_sub ((∑ e ∈ Icc 1 X, s e) * w (X + 1)) ((∑ e ∈ Icc 1 D, s e) * w (D + 1))
  linarith

/-- A `d`-periodic sequence `g` with zero period sum and `|g| ≤ B` has inverse-square dyadic sum
`|Σ_{Q < n ≤ 2Q} g(n)/n²| ≤ 2 d B / (Q + 1)²`. -/
theorem abs_sum_Ioc_div_sq_le_of_periodic {g : ℕ → ℝ} {d : ℕ} (hd : 0 < d)
    (hg : ∀ n, g (n + d) = g n) (h0 : ∑ r ∈ range d, g r = 0) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n, |g n| ≤ B) (Q : ℕ) :
    |∑ n ∈ Ioc Q (2 * Q), g n / (n : ℝ) ^ 2| ≤ 2 * (d : ℝ) * B / ((Q : ℝ) + 1) ^ 2 := by
  have hpart : ∀ x, |∑ e ∈ Icc 1 x, g e| ≤ (d : ℝ) * B := by
    intro x
    rw [show Icc 1 x = Ico 1 (1 + x) by ext n; simp only [mem_Icc, mem_Ico]; omega]
    exact abs_sum_Ico_le_of_periodic hd hg h0 hB 1 x
  have hab := abs_sum_Ioc_mul_le_of_bdd_partialSums (s := g) (w := fun n : ℕ => 1 / (n : ℝ) ^ 2)
    (C := (d : ℝ) * B) (by positivity) (D := Q) (X := 2 * Q) (by omega)
    (fun x _ _ => hpart x) (fun n => by positivity)
    (fun n hn => one_div_le_one_div_of_le
      (by have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          positivity)
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by push_cast; linarith) 2))
  rw [show (∑ n ∈ Ioc Q (2 * Q), g n / (n : ℝ) ^ 2) =
      ∑ n ∈ Ioc Q (2 * Q), g n * (1 / (n : ℝ) ^ 2) from
        sum_congr rfl fun _ _ => div_eq_mul_one_div _ _,
    show 2 * (d : ℝ) * B / ((Q : ℝ) + 1) ^ 2 =
      2 * ((d : ℝ) * B) * (1 / ((Q + 1 : ℕ) : ℝ) ^ 2) by push_cast; ring]
  exact hab

/-- The flat indicator row `𝟙_{(Q, 2Q]}`. -/
def flatWindowRow (Q : ℕ) (n : ℕ) : ℝ :=
  if Q < n ∧ n ≤ 2 * Q then 1 else 0

/-- The centred prime block is the uncentred prime row minus the flat window row. -/
theorem centredPrimeBlock_eq_sub (Q n : ℕ) :
    centredPrimeBlock Q n = primeWindowRow Q n - flatWindowRow Q n := by
  unfold centredPrimeBlock primeWindowRow flatWindowRow
  split_ifs <;> ring

/-- Linearity of `kernelStatistic` under subtraction. -/
theorem kernelStatistic_sub (N : ℕ) (f g : ℕ → ℝ) (p : ℕ) :
    kernelStatistic N (fun n => f n - g n) p = kernelStatistic N f p - kernelStatistic N g p := by
  simp only [kernelStatistic, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  ring

/-- Linearity of `kernelStatistic` under addition. -/
theorem kernelStatistic_add (N : ℕ) (f g : ℕ → ℝ) (p : ℕ) :
    kernelStatistic N (fun n => f n + g n) p = kernelStatistic N f p + kernelStatistic N g p := by
  simp only [kernelStatistic, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  ring

/-- **Non-asymptotic bound for the flat window row.** Because `𝔅(p, ·) - m_p` has zero period mean
modulo `p`, the flat block `𝟙_{(Q, 2Q]}` has kernel statistic at most `3p³/(2Q²)`. -/
theorem abs_kernelStatistic_flatWindowRow_le {p : ℕ} (hp : p.Prime) {Q : ℕ} (hQ : 1 ≤ Q) :
    |kernelStatistic (2 * Q) (flatWindowRow Q) p| ≤ 3 * (p : ℝ) ^ 3 / (2 * (Q : ℝ) ^ 2) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsub : Ioc Q (2 * Q) ⊆ Icc 1 (2 * Q) := fun n hn => by
    rw [mem_Ioc] at hn; rw [mem_Icc]; omega
  have hrestrict : kernelStatistic (2 * Q) (flatWindowRow Q) p =
      ∑ n ∈ Ioc Q (2 * Q), (bernoulliKernel p n - primeKernelMean p) / (n : ℝ) ^ 2 +
        ∑ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 3 * cubicKernel p n := by
    rw [kernelStatistic, ← sum_subset hsub fun n _ hn' => by
      have : ¬ (Q < n ∧ n ≤ 2 * Q) := fun h => hn' (mem_Ioc.mpr h)
      simp [flatWindowRow, this], ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [mem_Ioc] at hn
    simp only [flatWindowRow, if_pos hn]
    ring
  have hquad : |∑ n ∈ Ioc Q (2 * Q), (bernoulliKernel p n - primeKernelMean p) / (n : ℝ) ^ 2| ≤
      (p : ℝ) ^ 3 / (2 * (Q : ℝ) ^ 2) := by
    have hper := abs_sum_Ioc_div_sq_le_of_periodic hp.pos
      (fun n => by simp [bernoulliKernel_add_period]) (sum_range_bernoulliKernel_sub_mean hp)
      (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 2 / 4) (abs_bernoulliKernel_sub_mean_le hp) Q
    calc |∑ n ∈ Ioc Q (2 * Q), (bernoulliKernel p n - primeKernelMean p) / (n : ℝ) ^ 2|
        ≤ 2 * (p : ℝ) * ((p : ℝ) ^ 2 / 4) / ((Q : ℝ) + 1) ^ 2 := hper
      _ = (p : ℝ) ^ 3 / (2 * ((Q : ℝ) + 1) ^ 2) := by field_simp; ring
      _ ≤ (p : ℝ) ^ 3 / (2 * (Q : ℝ) ^ 2) := by
          gcongr
          linarith
  have hcub : |∑ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 3 * cubicKernel p n| ≤
      (p : ℝ) ^ 3 / (Q : ℝ) ^ 2 := by
    have hterm : ∀ n ∈ Ioc Q (2 * Q), |1 / (n : ℝ) ^ 3 * cubicKernel p n| ≤
        (p : ℝ) ^ 3 / (Q : ℝ) ^ 3 := by
      intro n hn
      have hn' := mem_Ioc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hQn : (Q : ℝ) ≤ n := by exact_mod_cast hn'.1.le
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ) ^ 3)]
      calc 1 / (n : ℝ) ^ 3 * |cubicKernel p n|
          ≤ 1 / (Q : ℝ) ^ 3 * (p : ℝ) ^ 3 :=
            mul_le_mul (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hQ0.le hQn 3))
              (abs_cubicKernel_le hp.pos n) (abs_nonneg _) (by positivity)
        _ = (p : ℝ) ^ 3 / (Q : ℝ) ^ 3 := by ring
    calc |∑ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 3 * cubicKernel p n|
        ≤ ∑ _n ∈ Ioc Q (2 * Q), (p : ℝ) ^ 3 / (Q : ℝ) ^ 3 :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
      _ = (p : ℝ) ^ 3 / (Q : ℝ) ^ 2 := by
          rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * Q - Q = Q by omega]
          field_simp
  rw [hrestrict]
  calc |∑ n ∈ Ioc Q (2 * Q), (bernoulliKernel p n - primeKernelMean p) / (n : ℝ) ^ 2 +
          ∑ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 3 * cubicKernel p n|
      ≤ (p : ℝ) ^ 3 / (2 * (Q : ℝ) ^ 2) + (p : ℝ) ^ 3 / (Q : ℝ) ^ 2 :=
        (abs_add_le _ _).trans (add_le_add hquad hcub)
    _ = 3 * (p : ℝ) ^ 3 / (2 * (Q : ℝ) ^ 2) := by ring

/-- The flat window row has vanishing rescaled kernel statistic `Q · Λ_p(𝟙_{(Q, 2Q]}) → 0`. -/
theorem tendsto_mul_kernelStatistic_flatWindowRow {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (flatWindowRow Q) p) atTop (𝓝 0) := by
  have hlim : Tendsto (fun Q : ℕ => 3 * (p : ℝ) ^ 3 / 2 * (1 / (Q : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (3 * (p : ℝ) ^ 3 / 2)
    rwa [mul_zero] at h
  refine squeeze_zero_norm' (eventually_ge_atTop 1 |>.mono fun Q hQ => ?_) hlim
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hQ0]
  calc (Q : ℝ) * |kernelStatistic (2 * Q) (flatWindowRow Q) p|
      ≤ (Q : ℝ) * (3 * (p : ℝ) ^ 3 / (2 * (Q : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (abs_kernelStatistic_flatWindowRow_le hp hQ) hQ0.le
    _ = 3 * (p : ℝ) ^ 3 / 2 * (1 / (Q : ℝ)) := by field_simp

/-- **The omitted-residue-class law of the centred prime block.** Centring `Λ` by `1` on `(Q, 2Q]`
preserves the exact omitted-residue-class limit of the uncentred prime row:
`Q · Λ_p((Λ - 1) 𝟙_{(Q, 2Q]}) → -π²(p² - 1)²/(144 p² (p - 1))`. -/
theorem tendsto_mul_kernelStatistic_centredPrimeBlock {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (centredPrimeBlock Q) p) atTop
      (𝓝 (-(Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (144 * (p : ℝ) ^ 2 * ((p : ℝ) - 1))))) := by
  have h := (tendsto_mul_kernelStatistic_primeWindowRow hp).sub
    (tendsto_mul_kernelStatistic_flatWindowRow hp)
  rw [sub_zero] at h
  refine h.congr fun Q => ?_
  have hsub : centredPrimeBlock Q = fun n => primeWindowRow Q n - flatWindowRow Q n :=
    funext (centredPrimeBlock_eq_sub Q)
  rw [hsub, kernelStatistic_sub, mul_sub]

/-! ## §2. The omitted-residue-class sieve corrector -/

/-- The `p`-periodic zero-mean weight assigning `1` to multiples of `p` and `-1/(p - 1)` to coprime
residues. -/
def omittedClassWeight (p : ℕ) (n : ℕ) : ℝ :=
  if n % p = 0 then 1 else -1 / ((p : ℝ) - 1)

/-- The omitted-residue-class sieve corrector on the dyadic window `(Q, 2Q]`. -/
def omittedClassCorrector (p Q : ℕ) (n : ℕ) : ℝ :=
  if Q < n ∧ n ≤ 2 * Q then omittedClassWeight p n else 0

theorem omittedClassWeight_add_period (p n : ℕ) :
    omittedClassWeight p (n + p) = omittedClassWeight p n := by
  unfold omittedClassWeight
  rw [Nat.add_mod_right]

theorem sum_range_omittedClassWeight {p : ℕ} (hp : p.Prime) :
    ∑ r ∈ range p, omittedClassWeight p r = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [← add_sum_erase _ _ (mem_range.mpr hp.pos)]
  have h0 : omittedClassWeight p 0 = 1 := by simp [omittedClassWeight]
  have hcop : ∀ r ∈ (range p).erase 0, omittedClassWeight p r = -1 / ((p : ℝ) - 1) := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_mem_erase hr
    have hrp : r < p := mem_range.mp (mem_of_mem_erase hr)
    have hmod : r % p ≠ 0 := by rw [Nat.mod_eq_of_lt hrp]; exact hr0
    simp [omittedClassWeight, hmod]
  rw [h0, sum_congr rfl hcop, sum_const, card_erase_of_mem (mem_range.mpr hp.pos), card_range,
    nsmul_eq_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem abs_omittedClassWeight_le {p : ℕ} (hp : p.Prime) (n : ℕ) :
    |omittedClassWeight p n| ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold omittedClassWeight
  split_ifs
  · norm_num
  · rw [abs_div, abs_neg, abs_one, abs_of_pos (by linarith), div_le_one (by linarith)]
    linarith

/-- **The omitted-class corrector has `O(p/Q²)` block mass.** Adding it to `centredPrimeBlock Q`
preserves the `o(1/Q)` centring of the block mass. -/
theorem abs_sum_omittedClassCorrector_div_sq_le {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    |∑ n ∈ Ioc Q (2 * Q), omittedClassCorrector p Q n / (n : ℝ) ^ 2| ≤
      2 * (p : ℝ) / ((Q : ℝ) + 1) ^ 2 := by
  have heq : ∑ n ∈ Ioc Q (2 * Q), omittedClassCorrector p Q n / (n : ℝ) ^ 2 =
      ∑ n ∈ Ioc Q (2 * Q), omittedClassWeight p n / (n : ℝ) ^ 2 := by
    refine sum_congr rfl fun n hn => ?_
    rw [omittedClassCorrector, if_pos (mem_Ioc.mp hn)]
  rw [heq]
  simpa using abs_sum_Ioc_div_sq_le_of_periodic hp.pos (omittedClassWeight_add_period p)
    (sum_range_omittedClassWeight hp) zero_le_one (abs_omittedClassWeight_le hp) Q

/-- The product of `omittedClassWeight p` and `𝔅(p, ·) - m_p` has period mean
`(𝔅(p, 0) - m_p)/(p - 1)`. -/
theorem sum_range_omittedClassWeight_mul_bernoulliKernel_sub_mean {p : ℕ} (hp : p.Prime) :
    ∑ r ∈ range p,
      (omittedClassWeight p r * (bernoulliKernel p r - primeKernelMean p) -
        (bernoulliKernel p 0 - primeKernelMean p) / ((p : ℝ) - 1)) = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set b : ℕ → ℝ := fun r => bernoulliKernel p r - primeKernelMean p
  have hsum0 : ∑ r ∈ (range p).erase 0, b r = -(b 0) := by
    have h := sum_range_bernoulliKernel_sub_mean hp
    rw [← add_sum_erase _ _ (mem_range.mpr hp.pos)] at h
    linarith
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
    ← add_sum_erase _ _ (mem_range.mpr hp.pos)]
  have h0 : omittedClassWeight p 0 * b 0 = b 0 := by simp [omittedClassWeight]
  have hcop : ∑ r ∈ (range p).erase 0, omittedClassWeight p r * b r =
      (-1 / ((p : ℝ) - 1)) * ∑ r ∈ (range p).erase 0, b r := by
    rw [mul_sum]
    refine sum_congr rfl fun r hr => ?_
    have hr0 : r ≠ 0 := ne_of_mem_erase hr
    have hrp : r < p := mem_range.mp (mem_of_mem_erase hr)
    have hmod : r % p ≠ 0 := by rw [Nat.mod_eq_of_lt hrp]; exact hr0
    simp [omittedClassWeight, hmod]
  rw [h0, hcop, hsum0]
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **The omitted-class corrector carries the exact opposite single-modulus main term.** -/
theorem tendsto_mul_kernelStatistic_omittedClassCorrector {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (omittedClassCorrector p Q) p) atTop
      (𝓝 (Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (144 * (p : ℝ) ^ 2 * ((p : ℝ) - 1)))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set μ : ℝ := (bernoulliKernel p 0 - primeKernelMean p) / ((p : ℝ) - 1) with hμdef
  set g : ℕ → ℝ := fun n =>
    omittedClassWeight p n * (bernoulliKernel p n - primeKernelMean p) - μ
  have hgper : ∀ n, g (n + p) = g n := fun n => by
    simp only [g, omittedClassWeight_add_period, bernoulliKernel_add_period]
  have hg0 : ∑ r ∈ range p, g r = 0 :=
    sum_range_omittedClassWeight_mul_bernoulliKernel_sub_mean hp
  have hμb : |μ| ≤ (p : ℝ) ^ 2 / 4 := by
    simp only [hμdef]
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
    calc |bernoulliKernel p 0 - primeKernelMean p| / ((p : ℝ) - 1)
        ≤ |bernoulliKernel p 0 - primeKernelMean p| / 1 := by gcongr; linarith
      _ ≤ (p : ℝ) ^ 2 / 4 := by rw [div_one]; exact abs_bernoulliKernel_sub_mean_le hp 0
  have hgb : ∀ n, |g n| ≤ (p : ℝ) ^ 2 / 2 := fun n => by
    simp only [g]
    calc |omittedClassWeight p n * (bernoulliKernel p n - primeKernelMean p) - μ|
        ≤ |omittedClassWeight p n| * |bernoulliKernel p n - primeKernelMean p| + |μ| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ 1 * ((p : ℝ) ^ 2 / 4) + (p : ℝ) ^ 2 / 4 :=
          add_le_add (mul_le_mul (abs_omittedClassWeight_le hp n)
            (abs_bernoulliKernel_sub_mean_le hp n) (abs_nonneg _) zero_le_one) hμb
      _ = (p : ℝ) ^ 2 / 2 := by ring
  have hrem_tendsto : Tendsto (fun Q : ℕ =>
      (Q : ℝ) * (kernelStatistic (2 * Q) (omittedClassCorrector p Q) p -
        μ * dyadicInverseSquareMass Q)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun Q : ℕ => 2 * (p : ℝ) ^ 3 * (1 / (Q : ℝ))) atTop (𝓝 0) := by
      have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (p : ℝ) ^ 3)
      rwa [mul_zero] at h
    refine squeeze_zero_norm' (eventually_ge_atTop 1 |>.mono fun Q hQ => ?_) hlim
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hsub : Ioc Q (2 * Q) ⊆ Icc 1 (2 * Q) := fun n hn => by
      rw [mem_Ioc] at hn; rw [mem_Icc]; omega
    have hsplit : kernelStatistic (2 * Q) (omittedClassCorrector p Q) p -
        μ * dyadicInverseSquareMass Q =
        ∑ n ∈ Ioc Q (2 * Q), g n / (n : ℝ) ^ 2 +
          ∑ n ∈ Ioc Q (2 * Q), omittedClassWeight p n / (n : ℝ) ^ 3 * cubicKernel p n := by
      rw [kernelStatistic, ← sum_subset hsub fun n _ hn' => by
        have : ¬ (Q < n ∧ n ≤ 2 * Q) := fun h => hn' (mem_Ioc.mpr h)
        simp [omittedClassCorrector, this], dyadicInverseSquareMass, mul_sum,
        ← sum_sub_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun n hn => ?_
      rw [omittedClassCorrector, if_pos (mem_Ioc.mp hn)]
      simp only [g]
      ring
    have hquad : |∑ n ∈ Ioc Q (2 * Q), g n / (n : ℝ) ^ 2| ≤ (p : ℝ) ^ 3 / (Q : ℝ) ^ 2 := by
      have hper := abs_sum_Ioc_div_sq_le_of_periodic hp.pos hgper hg0
        (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 2 / 2) hgb Q
      calc |∑ n ∈ Ioc Q (2 * Q), g n / (n : ℝ) ^ 2|
          ≤ 2 * (p : ℝ) * ((p : ℝ) ^ 2 / 2) / ((Q : ℝ) + 1) ^ 2 := hper
        _ = (p : ℝ) ^ 3 / ((Q : ℝ) + 1) ^ 2 := by ring
        _ ≤ (p : ℝ) ^ 3 / (Q : ℝ) ^ 2 := by gcongr; linarith
    have hcub : |∑ n ∈ Ioc Q (2 * Q), omittedClassWeight p n / (n : ℝ) ^ 3 * cubicKernel p n| ≤
        (p : ℝ) ^ 3 / (Q : ℝ) ^ 2 := by
      have hterm : ∀ n ∈ Ioc Q (2 * Q),
          |omittedClassWeight p n / (n : ℝ) ^ 3 * cubicKernel p n| ≤
            (p : ℝ) ^ 3 / (Q : ℝ) ^ 3 := by
        intro n hn
        have hn' := mem_Ioc.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hQn : (Q : ℝ) ≤ n := by exact_mod_cast hn'.1.le
        rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)]
        calc |omittedClassWeight p n| / (n : ℝ) ^ 3 * |cubicKernel p n|
            ≤ 1 / (Q : ℝ) ^ 3 * (p : ℝ) ^ 3 :=
              mul_le_mul (div_le_div₀ zero_le_one (abs_omittedClassWeight_le hp n)
                (by positivity) (pow_le_pow_left₀ hQ0.le hQn 3))
                (abs_cubicKernel_le hp.pos n) (abs_nonneg _) (by positivity)
          _ = (p : ℝ) ^ 3 / (Q : ℝ) ^ 3 := by ring
      calc |∑ n ∈ Ioc Q (2 * Q), omittedClassWeight p n / (n : ℝ) ^ 3 * cubicKernel p n|
          ≤ ∑ _n ∈ Ioc Q (2 * Q), (p : ℝ) ^ 3 / (Q : ℝ) ^ 3 :=
            (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
        _ = (p : ℝ) ^ 3 / (Q : ℝ) ^ 2 := by
            rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * Q - Q = Q by omega]
            field_simp
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hQ0, hsplit]
    calc (Q : ℝ) * |∑ n ∈ Ioc Q (2 * Q), g n / (n : ℝ) ^ 2 +
            ∑ n ∈ Ioc Q (2 * Q), omittedClassWeight p n / (n : ℝ) ^ 3 * cubicKernel p n|
        ≤ (Q : ℝ) * ((p : ℝ) ^ 3 / (Q : ℝ) ^ 2 + (p : ℝ) ^ 3 / (Q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hquad hcub)) hQ0.le
      _ = 2 * (p : ℝ) ^ 3 * (1 / (Q : ℝ)) := by field_simp; ring
  have hmain := (tendsto_mul_dyadicInverseSquareMass.const_mul μ).add hrem_tendsto
  have hL : μ * (1 / 2) + 0 =
      Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (144 * (p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
    simp only [hμdef, bernoulliKernel_zero hp.pos, primeKernelMean]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    have : (p : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hL] at hmain
  refine hmain.congr fun Q => ?_
  ring

/-- **Cancelling the omitted-residue-class main term.** Adding `omittedClassCorrector p Q` to
`centredPrimeBlock Q` cancels the single-modulus main term (`Q · Λ_p → 0`). -/
theorem tendsto_mul_kernelStatistic_centredPrimeBlock_add_corrector {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) *
      kernelStatistic (2 * Q) (fun n => centredPrimeBlock Q n + omittedClassCorrector p Q n) p)
      atTop (𝓝 0) := by
  have h := (tendsto_mul_kernelStatistic_centredPrimeBlock hp).add
    (tendsto_mul_kernelStatistic_omittedClassCorrector hp)
  rw [neg_add_cancel] at h
  refine h.congr fun Q => ?_
  rw [kernelStatistic_add, mul_add]

/-! ## §3. Block-mass elimination by Cauchy–Schwarz and the `17/30` short-window transfer -/

/-- **Short-window mean square controls the block mass.** Because `shortWindowAverage H x` preserves
the total sum of `x(n) = c'(n)/n²` and is supported on `Icc (Q + 1) (Q + Q + H)`, Cauchy–Schwarz
bounds the block mass directly by `√(2Q)` times the `ℓ²` norm of the short-window average. -/
theorem abs_sum_Icc_div_sq_le_of_shortWindowAverage {Q H : ℕ} (hH1 : 1 ≤ H) (hHQ : H ≤ Q)
    {c' : ℕ → ℝ} (hsupp : ∀ n, c' n ≠ 0 → n ∈ Icc (Q + 1) (Q + Q)) :
    |∑ n ∈ Icc (Q + 1) (Q + Q), c' n / (n : ℝ) ^ 2| ≤
      Real.sqrt (2 * (Q : ℝ)) * Real.sqrt (∑ n ∈ Icc (Q + 1) (Q + Q + H),
        shortWindowAverage H (fun n => c' n / (n : ℝ) ^ 2) n ^ 2) := by
  set x : ℕ → ℝ := fun n => c' n / (n : ℝ) ^ 2
  have hx0 : x 0 = 0 := by simp [x]
  have hxsupp : ∀ n, x n ≠ 0 → n ∈ Icc (Q + 1) (Q + Q) := fun n hn =>
    hsupp n fun h => hn (by simp [x, h])
  have hxN : ∀ n, x n ≠ 0 → n + H ≤ (Q + Q + H) + 1 := fun n hn => by
    have := mem_Icc.mp (hxsupp n hn); omega
  have hmass : ∑ n ∈ Icc (Q + 1) (Q + Q), x n =
      ∑ n ∈ Icc (Q + 1) (Q + Q + H), shortWindowAverage H x n := by
    have h1 : ∑ n ∈ Icc (Q + 1) (Q + Q), x n = ∑ n ∈ Icc 1 (Q + Q + H), x n :=
      sum_subset (Icc_subset_Icc (by omega) (by omega)) fun n _ hn => by
        by_contra h; exact hn (hxsupp n h)
    have h2 : ∑ n ∈ Icc (Q + 1) (Q + Q + H), shortWindowAverage H x n =
        ∑ n ∈ Icc 1 (Q + Q + H), shortWindowAverage H x n := by
      refine sum_subset (Icc_subset_Icc (by omega) le_rfl) fun n _ hn => ?_
      by_contra h
      have hmem := mem_Icc.mp (shortWindowAverage_supp hx0 hxsupp n h)
      exact hn (mem_Icc.mpr ⟨hmem.1, by omega⟩)
    rw [h1, h2, sum_shortWindowAverage hH1 hx0 hxN]
  rw [hmass]
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt (Icc (Q + 1) (Q + Q + H)) (fun _ => (1 : ℝ))
    (fun n => |shortWindowAverage H x n|)
  simp only [one_mul, one_pow, sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, sq_abs] at hCS
  rw [show Q + Q + H + 1 - (Q + 1) = Q + H by omega] at hCS
  refine (abs_sum_le_sum_abs _ _).trans (hCS.trans ?_)
  refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
  have : ((Q + H : ℕ) : ℝ) ≤ 2 * (Q : ℝ) := by
    have : Q + H ≤ 2 * Q := by omega
    exact_mod_cast this
  exact this

/-- When the short-window average has `Σ x̄(n)² ≤ ε²/Q³`, the block mass is at most `√2 ε / Q`. -/
theorem abs_sum_Icc_div_sq_le_sqrt_two_mul_div {Q H : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hQ1 : 1 ≤ Q)
    (hH1 : 1 ≤ H) (hHQ : H ≤ Q) {c' : ℕ → ℝ} (hsupp : ∀ n, c' n ≠ 0 → n ∈ Icc (Q + 1) (Q + Q))
    (hxbar : ∑ n ∈ Icc (Q + 1) (Q + Q + H),
      shortWindowAverage H (fun n => c' n / (n : ℝ) ^ 2) n ^ 2 ≤ ε ^ 2 / (Q : ℝ) ^ 3) :
    |∑ n ∈ Icc (Q + 1) (Q + Q), c' n / (n : ℝ) ^ 2| ≤ Real.sqrt 2 * ε / (Q : ℝ) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
  calc |∑ n ∈ Icc (Q + 1) (Q + Q), c' n / (n : ℝ) ^ 2|
      ≤ Real.sqrt (2 * (Q : ℝ)) * Real.sqrt (ε ^ 2 / (Q : ℝ) ^ 3) :=
        (abs_sum_Icc_div_sq_le_of_shortWindowAverage hH1 hHQ hsupp).trans
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxbar) (Real.sqrt_nonneg _))
    _ = Real.sqrt (2 * (Q : ℝ) * (ε ^ 2 / (Q : ℝ) ^ 3)) :=
        (Real.sqrt_mul (by positivity) _).symm
    _ = Real.sqrt ((Real.sqrt 2 * ε / (Q : ℝ)) ^ 2) := by
        congr 1
        rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
        field_simp
    _ = Real.sqrt 2 * ε / (Q : ℝ) := Real.sqrt_sq (by positivity)

/-- **The averaged centred prime block at the `17/30` exponent.** For every `17/30 < α < 1` and
`ε > 0`, eventually in `Q`, `H = ⌈(2Q)^α⌉` satisfies `1 ≤ H ≤ Q`, `Σ x̄(n)² ≤ ε²/Q³`, and the
block mass satisfies `|Σ_{Q<n≤2Q} (Λ(n) - 1)/n²| ≤ √2 ε / Q`. -/
theorem eventually_centredPrimeBlock_average_le_seventeenThirtieths {α : ℝ} (hα : 17 / 30 < α)
    (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, 1 ≤ ⌈(2 * (Q : ℝ)) ^ α⌉₊ ∧ ⌈(2 * (Q : ℝ)) ^ α⌉₊ ≤ Q ∧
      ∑ n ∈ Icc (Q + 1) (Q + Q + ⌈(2 * (Q : ℝ)) ^ α⌉₊),
        shortWindowAverage ⌈(2 * (Q : ℝ)) ^ α⌉₊
          (fun n => centredPrimeBlock Q n / (n : ℝ) ^ 2) n ^ 2 ≤ ε ^ 2 / (Q : ℝ) ^ 3 ∧
      |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| ≤ Real.sqrt 2 * ε / (Q : ℝ) := by
  have hα0 : 0 ≤ α := by linarith
  set ε₁ : ℝ := min (ε / 4) 1
  have hε₁ : 0 < ε₁ := lt_min (by linarith) one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁4 : ε₁ ≤ ε / 4 := min_le_left _ _
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    (eventually_abs_psi_window_sub_le_seventeenThirtieths hα hα1 hε₁)
  set δ₀ : ℝ := min (ε / 7) (ε₁ / 20)
  have hδ₀ : 0 < δ₀ := lt_min (by linarith) (by linarith)
  have hg := (tendsto_one_add_log_div_rpow_atTop_zero (t := (1 - α) / 2) (by linarith)).eventually
    (eventually_le_nhds hδ₀)
  filter_upwards [hg, eventually_ge_atTop 100, eventually_ge_atTop ⌈X₀ + 1⌉₊] with Q hgQ hQ100 hQX
  set H := ⌈(2 * (Q : ℝ)) ^ α⌉₊
  set L := Real.log (2 * Q) + 1
  have hQ1 : 1 ≤ Q := by omega
  have hQR : (100 : ℝ) ≤ Q := by exact_mod_cast hQ100
  have hQXR : X₀ + 1 ≤ Q := (Nat.le_ceil _).trans (by exact_mod_cast hQX)
  have hL1 : 1 ≤ L := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * Q by linarith); simp only [L]; linarith
  have hHL : (H : ℝ) * L ^ 2 ≤ 16 * δ₀ ^ 2 * Q := natCeil_rpow_mul_log_sq_le hα0 hα1.le hQ1 hgQ
  have hHle : (2 * (Q : ℝ)) ^ α ≤ H := Nat.le_ceil _
  have hH1 : 1 ≤ H := by
    have : (1 : ℝ) ≤ (2 * (Q : ℝ)) ^ α := Real.one_le_rpow (by linarith) hα0
    exact_mod_cast this.trans hHle
  have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  have hHL' : (H : ℝ) ≤ H * L ^ 2 := by
    calc (H : ℝ) = H * 1 := by ring
      _ ≤ H * L ^ 2 := mul_le_mul_of_nonneg_left hL2 (by positivity)
  have h8 : 8 * (H : ℝ) * L ^ 2 ≤ 3 * ε ^ 2 * Q := by
    have : δ₀ ^ 2 ≤ (ε / 7) ^ 2 := pow_le_pow_left₀ hδ₀.le (min_le_left _ _) 2
    nlinarith
  have h25 : 25 * (H : ℝ) ≤ ε₁ * Q := by
    have : δ₀ ^ 2 ≤ (ε₁ / 20) ^ 2 := pow_le_pow_left₀ hδ₀.le (min_le_right _ _) 2
    have : ε₁ ^ 2 ≤ ε₁ := by nlinarith
    nlinarith
  have hHQ : H ≤ Q := by
    have : (H : ℝ) ≤ Q := by nlinarith
    exact_mod_cast this
  have hwin : ∀ t, Q ≤ t → t + H < 2 * Q →
      |∑ m ∈ Ioc t (t + H), centredPrimeBlock Q m / (m : ℝ) ^ 2| ≤ 2 * ε₁ * H / (Q : ℝ) ^ 2 := by
    intro t ht1 ht2
    have hb := abs_sum_block_le_of_window hα0 hε₁ hε₁1 hX₀ (A := t + 1) (K := 1) (m := 0)
      (by omega) (by omega) hH1 hQR hQXR hHle h25 (by norm_num)
    simp only [zero_mul, add_zero] at hb
    rw [show ∑ m ∈ Ioc t (t + H), centredPrimeBlock Q m / (m : ℝ) ^ 2 =
        ∑ n ∈ Ico (t + 1) (t + 1 + H), (vonMangoldt n - 1) / (n : ℝ) ^ 2 by
      rw [show Ioc t (t + H) = Ico (t + 1) (t + 1 + H) by ext n; simp only [mem_Ioc, mem_Ico]; omega]
      refine sum_congr rfl fun n hn => ?_
      have := mem_Ico.mp hn
      rw [centredPrimeBlock, if_pos ⟨by omega, by omega⟩]]
    exact hb
  have hxbar : ∑ n ∈ Icc (Q + 1) (Q + Q + H),
      shortWindowAverage H (fun n => centredPrimeBlock Q n / (n : ℝ) ^ 2) n ^ 2 ≤
        ε ^ 2 / (Q : ℝ) ^ 3 := by
    refine (sum_sq_shortWindowAverage_le_of_window hH1 hHQ
      (fun m => abs_centredPrimeBlock_div_le hQ1 m) hwin).trans ?_
    have hQ0 : (0 : ℝ) < Q := by linarith
    have e1 : (Q : ℝ) * (2 * ε₁ * H / (Q : ℝ) ^ 2 / H) ^ 2 = 4 * ε₁ ^ 2 / (Q : ℝ) ^ 3 := by
      field_simp; ring
    have e2 : 2 * (H : ℝ) * (L / (Q : ℝ) ^ 2) ^ 2 = 2 * (H * L ^ 2) / (Q : ℝ) ^ 4 := by
      field_simp
    rw [e1, e2]
    have hε4 : 4 * ε₁ ^ 2 ≤ ε ^ 2 / 4 := by
      have := pow_le_pow_left₀ hε₁.le hε₁4 2; nlinarith
    have hQ4 : 2 * (H * L ^ 2) / (Q : ℝ) ^ 4 ≤ 3 / 4 * ε ^ 2 / (Q : ℝ) ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 2 * (H * L ^ 2) ≤ 3 / 4 * ε ^ 2 * Q := by linarith
      have hQ3 : (0 : ℝ) ≤ (Q : ℝ) ^ 3 := by positivity
      calc 2 * (H * L ^ 2) * (Q : ℝ) ^ 3 ≤ 3 / 4 * ε ^ 2 * Q * (Q : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_right this hQ3
        _ = 3 / 4 * ε ^ 2 * (Q : ℝ) ^ 4 := by ring
    have hQ3' : 4 * ε₁ ^ 2 / (Q : ℝ) ^ 3 ≤ ε ^ 2 / 4 / (Q : ℝ) ^ 3 :=
      div_le_div_of_nonneg_right hε4 (by positivity)
    calc _ ≤ ε ^ 2 / 4 / (Q : ℝ) ^ 3 + 3 / 4 * ε ^ 2 / (Q : ℝ) ^ 3 := add_le_add hQ3' hQ4
      _ = ε ^ 2 / (Q : ℝ) ^ 3 := by ring
  have hmass : |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| ≤
      Real.sqrt 2 * ε / (Q : ℝ) := by
    rw [← sum_Icc_centredPrimeBlock_div_eq]
    exact abs_sum_Icc_div_sq_le_sqrt_two_mul_div hε.le hQ1 hH1 hHQ
      (fun n hn => centredPrimeBlock_supp hn) hxbar
  exact ⟨hH1, hHQ, hxbar, hmass⟩

/-- **The centred prime block beats the large sieve at every `17/30 < α < 1`, with the block-mass
term bounded by `√2 ε / (6Q)`.** -/
theorem eventually_abs_rowBilinear_centredPrimeBlock_le_seventeenThirtieths {α : ℝ}
    (hα : 17 / 30 < α) (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ {N Q₀ : ℕ} {S : Finset ℕ} {c : ℕ → ℝ}, 2 ≤ Q₀ →
      Q + Q + ⌈(2 * (Q : ℝ)) ^ α⌉₊ ≤ N + 1 → (∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) →
      (∀ p ∈ S, 8 * (⌈(2 * (Q : ℝ)) ^ α⌉₊ : ℝ) * (Real.log (2 * Q) + 1) ^ 2 ≤ ε ^ 2 * p) →
      (∀ n, c n ≠ 0 → n ∈ S) →
      |rowBilinear N c (centredPrimeBlock Q) +
          rowMean N c * vonMangoldtReadout N (centredPrimeBlock Q) +
          rowBeta N c * finiteHarmonicSum N (centredPrimeBlock Q)| ≤
        ε * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) *
            Real.sqrt (1 / (Q : ℝ) ^ 3) +
          Real.sqrt 2 * ε / (6 * (Q : ℝ)) * ∑ p ∈ S, |c p| / p +
          3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
            ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 := by
  filter_upwards [eventually_centredPrimeBlock_average_le_seventeenThirtieths hα hα1 hε,
    eventually_ge_atTop 1] with Q hQ hQ1
  intro N Q₀ S c hQ₀ hN hS hSP hsupp
  have h1 := abs_rowBilinear_centredPrimeBlock_le_of_average hε hQ1 hQ.1 hQ.2.1 hQ.2.2.1 hQ₀ hN
    hS hSP hsupp
  have hsum_pos : 0 ≤ ∑ p ∈ S, |c p| / (p : ℝ) := sum_nonneg fun _ _ => by positivity
  have h2 : |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| / 6 * ∑ p ∈ S, |c p| / p ≤
      Real.sqrt 2 * ε / (6 * (Q : ℝ)) * ∑ p ∈ S, |c p| / p := by
    rw [show Real.sqrt 2 * ε / (6 * (Q : ℝ)) = Real.sqrt 2 * ε / (Q : ℝ) / 6 by ring]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hQ.2.2.2 (by norm_num)) hsum_pos
  linarith

/-- **The dual norm of the centred prime block at every `17/30 < α < 1`, with the block-mass term
bounded by `(1/6 + π²/72) √2 ε / Q`.** -/
theorem eventually_sum_abs_kernelStatistic_centredPrimeBlock_le_seventeenThirtieths {α : ℝ}
    (hα : 17 / 30 < α) (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ {N Q₀ : ℕ} {S : Finset ℕ}, 2 ≤ Q₀ →
      Q + Q + ⌈(2 * (Q : ℝ)) ^ α⌉₊ ≤ N + 1 → (∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) →
      (∀ p ∈ S, 8 * (⌈(2 * (Q : ℝ)) ^ α⌉₊ : ℝ) * (Real.log (2 * Q) + 1) ^ 2 ≤ ε ^ 2 * p) →
      ∑ p ∈ S, |kernelStatistic N (centredPrimeBlock Q) p| / p ≤
        ε * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
            (Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) +
          (1 / 6 + Real.pi ^ 2 / 72) * (Real.sqrt 2 * ε / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ) +
          3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 +
          6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 4 := by
  filter_upwards [eventually_centredPrimeBlock_average_le_seventeenThirtieths hα hα1 hε,
    eventually_abs_rowBilinear_centredPrimeBlock_le_seventeenThirtieths hα hα1 hε,
    eventually_ge_atTop 1] with Q hQavg hQbil hQ1
  intro N Q₀ S hQ₀ hN hS hSP
  have hS' : ∀ p ∈ S, p.Prime ∧ p ≤ N := fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩
  have hH1 := hQavg.1
  have hmass : ∑ n ∈ Icc 1 N, centredPrimeBlock Q n / (n : ℝ) ^ 2 =
      ∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2 := by
    rw [sum_Icc_div_sq_eq_of_supp (by omega) (fun n hn => centredPrimeBlock_supp hn),
      sum_Icc_centredPrimeBlock_div_eq]
  have h := sum_abs_kernelStatistic_le_of_remainder hS' (c' := centredPrimeBlock Q) hε.le
    (V := Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3))
    (m := Real.sqrt 2 * ε / (6 * (Q : ℝ))) (by positivity) (by positivity)
    (fun c _ hsupp => by
      have := hQbil hQ₀ hN hS hSP hsupp
      calc _ ≤ _ := this
        _ = _ := by ring)
  rw [hmass] at h
  have hsum_pos : 0 ≤ ∑ p ∈ S, 1 / (p : ℝ) := sum_nonneg fun _ _ => by positivity
  have hm_le : (Real.sqrt 2 * ε / (6 * (Q : ℝ)) +
      Real.pi ^ 2 / 72 * |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2|) *
        ∑ p ∈ S, 1 / (p : ℝ) ≤
      (1 / 6 + Real.pi ^ 2 / 72) * (Real.sqrt 2 * ε / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ) := by
    refine mul_le_mul_of_nonneg_right ?_ hsum_pos
    have hpi : 0 ≤ Real.pi ^ 2 / 72 := by positivity
    have hmb := mul_le_mul_of_nonneg_left hQavg.2.2.2 hpi
    have hdiv : Real.sqrt 2 * ε / (6 * (Q : ℝ)) = 1 / 6 * (Real.sqrt 2 * ε / (Q : ℝ)) := by ring
    linarith
  linarith

/-- **The Möbius block mass is controlled by its short-window average.** -/
theorem eventually_moebiusBlockMass_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, |moebiusBlockMass Q| ≤ Real.sqrt 2 * ε / (Q : ℝ) := by
  filter_upwards [eventually_sum_sq_shortWindowAverage_moebiusWindowRow_le
    (by positivity : 0 < ε ^ 2), tendsto_natLog_two_atTop.eventually_ge_atTop 1] with Q hQ hH1
  set H := Nat.log 2 Q
  have hHQ : H ≤ Q := Nat.log_le_self 2 Q
  have hQ1 : 1 ≤ Q := hH1.trans hHQ
  rw [← sum_Icc_moebiusWindowRow_div_eq_blockMass]
  exact abs_sum_Icc_div_sq_le_sqrt_two_mul_div hε.le hQ1 hH1 hHQ
    (fun n hn => moebiusWindowRow_supp hn) hQ

/-- **The Möbius block beats the Type-II barrier with the block-mass term bounded by
`√2 ε / (6Q)`.** -/
theorem eventually_abs_rowBilinear_moebiusWindowRow_le_eliminated {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ {N Q₀ : ℕ} {S : Finset ℕ} {c : ℕ → ℝ}, 2 ≤ Q₀ →
      Q + Q + Nat.log 2 Q ≤ N + 1 → (∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) →
      (∀ p ∈ S, 8 * (Nat.log 2 Q : ℝ) ≤ ε ^ 2 * p) → (∀ n, c n ≠ 0 → n ∈ S) →
      |rowBilinear N c (moebiusWindowRow Q) +
          rowMean N c * vonMangoldtReadout N (moebiusWindowRow Q) +
          rowBeta N c * finiteHarmonicSum N (moebiusWindowRow Q)| ≤
        ε * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) *
            Real.sqrt (1 / (Q : ℝ) ^ 3) +
          Real.sqrt 2 * ε / (6 * (Q : ℝ)) * ∑ p ∈ S, |c p| / p +
          3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
            ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 3 := by
  filter_upwards [eventually_abs_rowBilinear_moebiusWindowRow_le hε,
    eventually_moebiusBlockMass_le hε] with Q hQ hmass
  intro N Q₀ S c hQ₀ hN hS hSP hsupp
  have h1 := hQ hQ₀ hN hS hSP hsupp
  have hsum_pos : 0 ≤ ∑ p ∈ S, |c p| / (p : ℝ) := sum_nonneg fun _ _ => by positivity
  have h2 : |moebiusBlockMass Q| / 6 * ∑ p ∈ S, |c p| / p ≤
      Real.sqrt 2 * ε / (6 * (Q : ℝ)) * ∑ p ∈ S, |c p| / p := by
    rw [show Real.sqrt 2 * ε / (6 * (Q : ℝ)) = Real.sqrt 2 * ε / (Q : ℝ) / 6 by ring]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmass (by norm_num)) hsum_pos
  linarith

/-- **The dual norm of the Möbius block with the block-mass term bounded by
`(1/6 + π²/72) √2 ε / Q`.** -/
theorem eventually_sum_abs_kernelStatistic_moebiusWindowRow_le_eliminated {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ {N Q₀ : ℕ} {S : Finset ℕ}, 2 ≤ Q₀ →
      Q + Q + Nat.log 2 Q ≤ N + 1 → (∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) →
      (∀ p ∈ S, 8 * (Nat.log 2 Q : ℝ) ≤ ε ^ 2 * p) →
      ∑ p ∈ S, |kernelStatistic N (moebiusWindowRow Q) p| / p ≤
        ε * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
            (Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) +
          (1 / 6 + Real.pi ^ 2 / 72) * (Real.sqrt 2 * ε / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ) +
          3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 3 +
          6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 4 := by
  filter_upwards [eventually_sum_abs_kernelStatistic_moebiusWindowRow_le hε,
    eventually_moebiusBlockMass_le hε] with Q hQ hmass
  intro N Q₀ S hQ₀ hN hS hSP
  have h1 := hQ hQ₀ hN hS hSP
  have hsum_pos : 0 ≤ ∑ p ∈ S, 1 / (p : ℝ) := sum_nonneg fun _ _ => by positivity
  have h2 : (1 / 6 + Real.pi ^ 2 / 72) * |moebiusBlockMass Q| * ∑ p ∈ S, 1 / (p : ℝ) ≤
      (1 / 6 + Real.pi ^ 2 / 72) * (Real.sqrt 2 * ε / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ) := by
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (by positivity)) hsum_pos
  linarith

/-! ## §4. Uniform cross-scale and dual-norm bounds in the balanced regime `P ≤ Q ≤ B P` -/

/-- **The centred prime block in the balanced regime `P ≤ Q ≤ B P` (bilinear form).** For every
aspect ratio `B ≥ 1` and `ε > 0`, there is `P₀` such that for all `P ≥ P₀`, all `P ≤ Q ≤ B P`,
horizons `N ≥ 3Q`, and prime sets `S ⊆ (P, 2P]` with `2P ≤ N`, the small-prime window condition is
discharged automatically and the cross-scale remainder beats the large sieve uniformly. -/
theorem exists_balanced_centredPrimeBlock_rowBilinear_le {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ {N P Q : ℕ} {S : Finset ℕ} {c : ℕ → ℝ}, P₀ ≤ P → P ≤ Q → (Q : ℝ) ≤ B * P →
      3 * Q ≤ N → (∀ p ∈ S, p.Prime ∧ P < p ∧ p ≤ 2 * P ∧ p ≤ N) →
      (∀ n, c n ≠ 0 → n ∈ S) →
      |rowBilinear N c (centredPrimeBlock Q) +
          rowMean N c * vonMangoldtReadout N (centredPrimeBlock Q) +
          rowBeta N c * finiteHarmonicSum N (centredPrimeBlock Q)| ≤
        ε * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt ((Q : ℝ) + 8 * (P : ℝ) ^ 2) *
            Real.sqrt (1 / (Q : ℝ) ^ 3) +
          Real.sqrt 2 * ε / (6 * (Q : ℝ)) * ∑ p ∈ S, |c p| / p +
          3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
            ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 := by
  have hα : (17 / 30 : ℝ) < 2 / 3 := by norm_num
  have hα1 : (2 / 3 : ℝ) < 1 := by norm_num
  set δ : ℝ := ε / (12 * Real.sqrt B)
  have hδ : 0 < δ := by positivity
  have hg := (tendsto_one_add_log_div_rpow_atTop_zero
    (t := (1 - (2 / 3 : ℝ)) / 2) (by norm_num)).eventually (eventually_le_nhds hδ)
  have hev := (eventually_centredPrimeBlock_average_le_seventeenThirtieths hα hα1 hε).and
    ((eventually_abs_rowBilinear_centredPrimeBlock_le_seventeenThirtieths hα hα1 hε).and
      (hg.and (eventually_ge_atTop 1)))
  obtain ⟨Q₁, hQ₁⟩ := eventually_atTop.mp hev
  refine ⟨max Q₁ 1, ?_⟩
  intro N P Q S c hP hPQ hQB hN hS hsupp
  have hP1 : 1 ≤ P := (le_max_right _ _).trans hP
  have hQ : Q₁ ≤ Q := ((le_max_left _ _).trans hP).trans hPQ
  obtain ⟨havg, hbil, hgQ, hQ1⟩ := hQ₁ Q hQ
  have hHQ : ⌈(2 * (Q : ℝ)) ^ (2 / 3 : ℝ)⌉₊ ≤ Q := havg.2.1
  have hN' : Q + Q + ⌈(2 * (Q : ℝ)) ^ (2 / 3 : ℝ)⌉₊ ≤ N + 1 := by omega
  have hQ₀ : 2 ≤ 2 * P := by omega
  have hS' : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ 2 * P := fun p hp =>
    ⟨(hS p hp).1, (hS p hp).2.2.2, (hS p hp).2.2.1⟩
  have hSP : ∀ p ∈ S, 8 * (⌈(2 * (Q : ℝ)) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * (Real.log (2 * Q) + 1) ^ 2 ≤
      ε ^ 2 * p := by
    intro p hp
    have hHL := natCeil_rpow_mul_log_sq_le (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num : (2 / 3 : ℝ) ≤ 1) hQ1 hgQ
    have hδ2 : δ ^ 2 = ε ^ 2 / (144 * B) := by
      simp only [δ]; rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    have hpP : (P : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1.le
    have hQP : (Q : ℝ) ≤ B * p := hQB.trans (mul_le_mul_of_nonneg_left hpP (by positivity))
    have hB0 : 0 < B := by positivity
    calc 8 * (⌈(2 * (Q : ℝ)) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * (Real.log (2 * Q) + 1) ^ 2
        ≤ 8 * (16 * δ ^ 2 * (Q : ℝ)) := by linarith
      _ = 128 / 144 * ε ^ 2 * ((Q : ℝ) / B) := by rw [hδ2]; field_simp; ring
      _ ≤ 1 * ε ^ 2 * p := by
          have h1 : (Q : ℝ) / B ≤ p := (div_le_iff₀ hB0).mpr (by linarith)
          have h2 : (128 / 144 : ℝ) ≤ 1 := by norm_num
          nlinarith [sq_nonneg ε, Nat.cast_nonneg (α := ℝ) p]
      _ = ε ^ 2 * p := by ring
  have hmain := hbil hQ₀ hN' hS' hSP hsupp
  rwa [show (2 * (2 * P : ℕ) ^ 2 : ℝ) = 8 * (P : ℝ) ^ 2 by push_cast; ring] at hmain

/-- **The centred prime block in the balanced regime `P ≤ Q ≤ B P` (dual norm).** -/
theorem exists_balanced_centredPrimeBlock_dualNorm_le {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ {N P Q : ℕ} {S : Finset ℕ}, P₀ ≤ P → P ≤ Q → (Q : ℝ) ≤ B * P →
      3 * Q ≤ N → (∀ p ∈ S, p.Prime ∧ P < p ∧ p ≤ 2 * P ∧ p ≤ N) →
      ∑ p ∈ S, |kernelStatistic N (centredPrimeBlock Q) p| / p ≤
        ε * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
            (Real.sqrt ((Q : ℝ) + 8 * (P : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) +
          (1 / 6 + Real.pi ^ 2 / 72) * (Real.sqrt 2 * ε / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ) +
          3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 +
          6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 4 := by
  have hα : (17 / 30 : ℝ) < 2 / 3 := by norm_num
  have hα1 : (2 / 3 : ℝ) < 1 := by norm_num
  set δ : ℝ := ε / (12 * Real.sqrt B)
  have hδ : 0 < δ := by positivity
  have hg := (tendsto_one_add_log_div_rpow_atTop_zero
    (t := (1 - (2 / 3 : ℝ)) / 2) (by norm_num)).eventually (eventually_le_nhds hδ)
  have hev := (eventually_centredPrimeBlock_average_le_seventeenThirtieths hα hα1 hε).and
    ((eventually_sum_abs_kernelStatistic_centredPrimeBlock_le_seventeenThirtieths hα hα1 hε).and
      (hg.and (eventually_ge_atTop 1)))
  obtain ⟨Q₁, hQ₁⟩ := eventually_atTop.mp hev
  refine ⟨max Q₁ 1, ?_⟩
  intro N P Q S hP hPQ hQB hN hS
  have hP1 : 1 ≤ P := (le_max_right _ _).trans hP
  have hQ : Q₁ ≤ Q := ((le_max_left _ _).trans hP).trans hPQ
  obtain ⟨havg, hdual, hgQ, hQ1⟩ := hQ₁ Q hQ
  have hHQ : ⌈(2 * (Q : ℝ)) ^ (2 / 3 : ℝ)⌉₊ ≤ Q := havg.2.1
  have hN' : Q + Q + ⌈(2 * (Q : ℝ)) ^ (2 / 3 : ℝ)⌉₊ ≤ N + 1 := by omega
  have hQ₀ : 2 ≤ 2 * P := by omega
  have hS' : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ 2 * P := fun p hp =>
    ⟨(hS p hp).1, (hS p hp).2.2.2, (hS p hp).2.2.1⟩
  have hSP : ∀ p ∈ S, 8 * (⌈(2 * (Q : ℝ)) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * (Real.log (2 * Q) + 1) ^ 2 ≤
      ε ^ 2 * p := by
    intro p hp
    have hHL := natCeil_rpow_mul_log_sq_le (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num : (2 / 3 : ℝ) ≤ 1) hQ1 hgQ
    have hδ2 : δ ^ 2 = ε ^ 2 / (144 * B) := by
      simp only [δ]; rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    have hpP : (P : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1.le
    have hQP : (Q : ℝ) ≤ B * p := hQB.trans (mul_le_mul_of_nonneg_left hpP (by positivity))
    have hB0 : 0 < B := by positivity
    calc 8 * (⌈(2 * (Q : ℝ)) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * (Real.log (2 * Q) + 1) ^ 2
        ≤ 8 * (16 * δ ^ 2 * (Q : ℝ)) := by linarith
      _ = 128 / 144 * ε ^ 2 * ((Q : ℝ) / B) := by rw [hδ2]; field_simp; ring
      _ ≤ 1 * ε ^ 2 * p := by
          have h1 : (Q : ℝ) / B ≤ p := (div_le_iff₀ hB0).mpr (by linarith)
          have h2 : (128 / 144 : ℝ) ≤ 1 := by norm_num
          nlinarith [sq_nonneg ε, Nat.cast_nonneg (α := ℝ) p]
      _ = ε ^ 2 * p := by ring
  have hmain := hdual hQ₀ hN' hS' hSP
  rwa [show (2 * (2 * P : ℕ) ^ 2 : ℝ) = 8 * (P : ℝ) ^ 2 by push_cast; ring] at hmain

/-! ## §5. Qualitative block mean-square saving versus uniform admission of the coupled receiver -/

/-- **Power saving in the prime short-window mean square is equivalent to crossing below half
damping for the complete coupled receiver.** -/
theorem primePowerWindowSaving_iff_receiverDampingRate_lt_half :
    PrimePowerWindowSaving ↔ receiverDampingRate < 1 / 2 :=
  primePowerWindowSaving_iff.trans receiverDampingRate_lt_half_iff.symm

/-- **Power saving in the Möbius short-window mean square is equivalent to crossing below half
damping for the complete coupled receiver.** -/
theorem moebiusPowerWindowSaving_iff_receiverDampingRate_lt_half :
    MoebiusPowerWindowSaving ↔ receiverDampingRate < 1 / 2 :=
  moebiusPowerWindowSaving_iff.trans receiverDampingRate_lt_half_iff.symm

/-- **Equivalence of prime and Möbius short-window power savings.** -/
theorem primePowerWindowSaving_iff_moebiusPowerWindowSaving :
    PrimePowerWindowSaving ↔ MoebiusPowerWindowSaving :=
  primePowerWindowSaving_iff.trans moebiusPowerWindowSaving_iff.symm

end GaloisForLFunctions.ArithmeticCompensationTheory

end
