import GaloisForLFunctions.«arithmetic-positivity-theory».GeneralDivisorBernoulliFilterClassification
import GaloisForLFunctions.«arithmetic-positivity-theory».CompactCriticalSourceWeilPositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeKernelNegativeDefinite
import GaloisForLFunctions.«arithmetic-positivity-theory».ExplicitCollarThresholdsAndKernelShape
import GaloisForLFunctions.«arithmetic-positivity-theory».FromTheCriticalFamilyToTheReceiver

/-!
# Admissible Divisor Stencils, Non-Bernoulli Harmonic Sources, Receiver Landing, and Sign-Definite Cell Kernels Beyond the Dyadic Stencil

This module resolves the open problem on arithmetic sources beyond the canonical dyadic stencil
`{1, 2, 4}` with weights `(4, -2, 1/4)`:

1. **General Divisor-Stencil Phase Profiles, General Harmonic-Multiplier Critical Sources, and
   Four Infinite Admissible Families (`divisorBernoulliPhaseProfile`, `divisorHarmonicWeight`,
   `generalPhaseCombination`, `AdmissibleHarmonicWeight`,
   `admissibleHarmonicWeight_dyadic`, `admissibleHarmonicWeight_qAdicSignFlip`,
   `admissibleHarmonicWeight_qAdicDriftFree`, `admissibleHarmonicWeight_higherOrder`):**
   - For any finite divisor set `D` with `0 ∉ D` and stencil `α : ℕ → ℝ`, the collar-difference
     phase profile
     `Φ_{D, α, N}(v) = (P_{D, α}(λ_N v) - P_{D, α}(N v)) / 4`
     expands in an absolutely convergent cosine series with harmonic weights
     `w_k = M_{D, α}(k) / (4 k²)` (`M_{D, α}(k) = ∑_{d ∈ D, d ∣ k} α(d) d²`), and is globally
     Lipschitz on `ℝ` with constant `(∑_{d ∈ D} d |α d| / 8) (λ_N + N)`.
   - We define the general class `AdmissibleHarmonicWeight w C_w τ` of harmonic weight sequences
     satisfying `w 0 = 0`, `w 1 = 1`, `|w k| ≤ C_w / k²`, and higher-harmonic tail
     `∑_{k ≥ 2} |w k| ≤ τ < 1`, and prove that four explicit families belong to this class:
     1. the canonical dyadic stencil `dyadicHarmonicWeight` (`C_w = 1`, `τ = 3/4 < 1`);
     2. all `q`-adic 3-scale sign-flip stencils on `{1, q, q²}` for every `q ≥ 2`
        (`qAdicSignFlipWeight q`, with `C_w = 1` and `τ = 3/4 < 1`);
     3. all `q`-adic 3-scale **drift-free** stencils on `{1, q, q²}` for every `q ≥ 2`
        (`qAdicDriftFreeWeight q`, which simultaneously cancel both the linear secular ramp
        `L = 0` and the quadratic drift `Q = 0`, and satisfy the exact identity
        `∑_{k ≥ 2} |w_k| = (π²/6)(1 + (q² - q - 1)/q³) - 1 ≤ (32/27)(π²/6) - 1 ≤ 24/25 < 1`
        via the polynomial sum-of-squares identity `5 q³ - 27(q² - q - 1) = (q - 3)²(5q + 3) ≥ 0`);
     4. all higher-order / non-Bernoulli Fourier-multiplier filters `w_k = c_k / k^p` (`p ≥ 2`,
        `c_1 = 1`, `|c_k| ≤ 1`), which for `p ≥ 3` have summable derivative series
        `∑ k |w_k| < ∞` and are globally `C¹` and Lipschitz on `ℝ`.

2. **Window Coercivity, Collared & Doubly Collared Mass Floors, Low-Band Mellin Exclusion,
   `ℓ²`-Uniform Prime/Polar Channels, and Receiver Positivity for All `AdmissibleHarmonicWeight`
   Sources (`generalPhaseCombination_window_lower`, `generalCollaredSource_mass_bounds`,
   `ofReal_le_sourceLevyEnergy_generalCollaredSource`,
   `abs_generalCollaredPrimeEnergy_le_of_dyadic`, `abs_generalTruncatedPrimeEnergy_le_of_dyadic`,
   `abs_generalCollaredPolarReadout_le`, `compactFullWeilEnergy_generalTruncatedTest`,
   `exists_generalTruncatedCompleteEnergy_and_receiver_pos`):**
   - For every `AdmissibleHarmonicWeight w C_w τ`, the window length
     `generalWindowLength τ = 8 (1 + τ²) / (1 - τ²)² * K` (`K = 390/π`) gives the uniform mean-square
     window floor `∫_a^{a+L_τ} (B_{w,b}(v))² dv ≥ (8 K / π⁴) ∑ b_n²`, which induces physical
     `L²` mass floors and ceilings on both the collared source `generalCollaredSource w S b` and
     the compact doubly collared source `generalTruncatedSource w V S b`.
   - Each harmonic layer obeys the nonstationary Mellin bound, giving low-frequency exclusion
     `‖ĝ_{w,c}(t)‖ ≤ C_w D_c ∑ |b_n|/(n+1)` on `|t| ≤ π(n+1)` and logarithmic archimedean Lévy
     coercivity `Lévy(g) ≥ s_w (log M - c_w) ∑ b_n²` on scales `n + 1 ≥ M`.
   - The dyadic dilation correlation inequality extends with factor `C_w²`, bounding both the
     collared and compact doubly collared von Mangoldt prime channels on every dyadic block by
     `C_w² C_c ∑ b_n²` and `C_w² C_T ∑ b_n²` uniformly in `V > 0`, `M`, and the pattern, while the
     smooth harmonic sine primitive `generalPhasePrimitive` bounds the polar readouts by
     `O((1 + τ) ∑ |b_n|/(n+1))`.
   - Whenever `generalPhaseCombination w S b` is Lipschitz on `ℝ` (covering all divisor stencils
     `(D, α)` and all `p ≥ 3` non-Bernoulli multipliers), the compact source `generalTruncatedTest`
     lands in the receiver `compactFullWeilEnergy`, `fullZeroForm`, `weilFullFunctional`, and
     (via mollification) `zetaZeroConfig.W` on `[-log(2V), 0]`, with strict block positivity above
     an explicit scale `M₀(C_w, τ)` uniformly in `V ≥ V₀(τ)`.

3. **Sign-Definite Cell Kernels Beyond the Dyadic Stencil: Positive-Definite vs Negative-Definite
   Classification (`generalCriticalPrimeHarmonicCharge`,
   `generalCriticalPrimeContinuousRealKernel`,
   `generalCriticalPrimeContinuousRealKernel_eq_poisson_window`,
   `generalCriticalPrimeContinuousRealKernel_pos_of_nonneg_charge`,
   `qAdicSignFlip_harmonicCharge_two_pos_of_three_le`,
   `generalCriticalPrimeContinuousRealKernel_neg_of_charge_perturbation`,
   `exists_nonDyadic_stencil_negative_definite_cellKernel`):**
   - For any multiplier `χ : ℕ → ℝ`, the harmonic divisor charge
     `A_χ(m) = χ(m) ∑_{r ∣ m} r Λ(r) χ(m/r)` satisfies `A_χ(1) = 0` universally and
     `A_χ(p) = p (log p) χ(1) χ(p)` at every prime `p` (in particular `A_χ(2) = 2 (log 2) χ(1) χ(2)`).
   - **Strictly Positive-Definite Cell Kernels (`R_χ > 0` — Prime Penalty Regime):** Whenever
     `A_χ(m) ≥ 0` for all `m ≥ 1` and `A_χ(p) > 0` at some `p ≥ 2` (which holds for every
     nonnegative multiplier `χ(1) > 0, χ(2) > 0, χ(m) ≥ 0`, including the 1-scale Bernoulli kernel,
     all higher even Bernoulli/spline filters `w_k = 1/k^{2r}`, and any stencil supported on
     multiples where `χ` is positive), the continuous cell kernel `R_χ(t)` is strictly positive on
     `[0, 1]` and the asymptotic prime form `(4/π⁴) ∫_0^1 R_χ(t) Q_{S,b}(t) dt ≥ c_χ ∑ b_j² > 0`
     is strictly positive definite.
   - **Uniqueness of Base `q = 2` Among `q`-Adic Sign-Flip Stencils:** For every `q ≥ 3`, the
     `q`-adic 3-scale sign-flip stencil on `{1, q, q²}` has `χ_q(2) = +1`, hence positive
     harmonic-2 charge `A_{χ_q}(2) = +2 log 2 > 0` and `A_{χ_q}(m) = ∑_{d ∣ m} d Λ(d) ≥ 0` for all
     `q ∤ m`, so `q = 2` is the unique `q`-adic sign-flip stencil with `A(2) < 0`.
   - **Strictly Negative-Definite Cell Kernels (`R_χ < 0` — Prime Subsidy Regime Beyond Dyadic):**
     Perturbing around the dyadic divisor charge shows that every multiplier `χ` satisfying
     `(π²/12) ∑_{m ≥ 1} |A_χ(m) - A_{dyadic}(m)| / m³ ≤ 1/7000 - μ` (`μ > 0`) — including an
     explicit infinite family of multi-scale divisor stencils beyond `{1, 2, 4}` (such as
     `{1, 2, 4, d}` for any `d ≥ 3` with small fourth-scale weight) and non-Bernoulli harmonic
     perturbations — has a strictly negative-definite cell kernel `R_χ(t) ≤ -μ < 0` on `[0, 1]` and
     asymptotic prime form `(4/π⁴) ∫_0^1 R_χ(t) Q_{S,b}(t) dt ≤ -(4μ/π⁴) ∑ b_j² < 0`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators ENNReal CompactlySupported ComplexConjugate
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ## Section 1: General Divisor-Stencil Phase Profiles, General Harmonic-Multiplier Critical Sources, and Four Infinite Admissible Families -/

/-- Normalized collar-difference phase profile of a general divisor stencil `(D, α)`:
`Φ_{D, α, N}(v) = (P_{D, α}(λ_N v) - P_{D, α}(N v)) / 4`. At `(D, α) = ({1, 2, 4}, canonicalDyadicStencil)`,
the factor `1/4` matches `M(1) = 4` so the first harmonic has unit weight `w_1 = 1`. -/
def divisorBernoulliPhaseProfile (D : Finset ℕ) (α : ℕ → ℝ) (N : ℕ) (v : ℝ) : ℝ :=
  (divisorBernoulliFilter D α (factorialShiftedFreq N * v) -
    divisorBernoulliFilter D α ((N : ℝ) * v)) / 4

/-- Harmonic weight sequence `w_k = M_{D, α}(k) / (4 k²)` of a general divisor stencil `(D, α)`. -/
def divisorHarmonicWeight (D : Finset ℕ) (α : ℕ → ℝ) (k : ℕ) : ℝ :=
  divisorHarmonicMultiplier D α k / (4 * (k : ℝ) ^ 2)

@[simp]
theorem divisorHarmonicWeight_zero (D : Finset ℕ) (α : ℕ → ℝ) :
    divisorHarmonicWeight D α 0 = 0 := by
  simp [divisorHarmonicWeight]

theorem divisorHarmonicWeight_one {D : Finset ℕ} (h0 : 0 ∉ D) (α : ℕ → ℝ) :
    divisorHarmonicWeight D α 1 = (if 1 ∈ D then α 1 else 0) / 4 := by
  unfold divisorHarmonicWeight divisorHarmonicMultiplier
  simp only [Nat.cast_one, one_pow, mul_one]
  congr 1
  have hfilter : (D.filter fun d => d ∣ 1) = if 1 ∈ D then {1} else ∅ := by
    ext d
    simp only [Finset.mem_filter, Nat.dvd_one]
    split_ifs with h1
    · simp only [Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ h1, h⟩⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      intro hd hd1
      exact h1 (hd1 ▸ hd)
  rw [hfilter]
  split_ifs <;> simp

theorem abs_divisorHarmonicWeight_le (D : Finset ℕ) (α : ℕ → ℝ) (k : ℕ) :
    |divisorHarmonicWeight D α k| ≤
      ((∑ d ∈ D, |α d| * (d : ℝ) ^ 2) / 4) / (k : ℝ) ^ 2 := by
  unfold divisorHarmonicWeight divisorHarmonicMultiplier
  rw [div_eq_mul_inv, abs_mul, abs_inv, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_nonneg (sq_nonneg (k : ℝ)), div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun d _ => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ D) fun d _ _ => by positivity)
  rw [abs_mul, abs_of_nonneg (sq_nonneg (d : ℝ))]

/-- **Bernoulli cosine expansion of a general divisor-stencil filter.** For any finite divisor set
`D` with `0 ∉ D` and any stencil `α : ℕ → ℝ`,
`∑_{k ≥ 1} divisorHarmonicWeight D α k * cos(2π k u) = -(π² / 2) * (divisorCenteredBernoulliFilter D α u / 4)`. -/
theorem divisorCenteredBernoulliFilter_hasSum {D : Finset ℕ} (h0 : 0 ∉ D) (α : ℕ → ℝ) (u : ℝ) :
    HasSum (fun k : ℕ => divisorHarmonicWeight D α k * Real.cos (2 * Real.pi * k * u))
      (-(Real.pi ^ 2 / 2) * (divisorCenteredBernoulliFilter D α u / 4)) := by
  have hd (d : ℕ) (hdD : d ∈ D) :
      HasSum (fun k : ℕ => (α d / 4) *
        (if d ∣ k then (d : ℝ) ^ 2 * Real.cos (2 * Real.pi * k * u) / (k : ℝ) ^ 2 else 0))
        ((α d / 4) * (2 * Real.pi ^ 2 * (1 / 12 - periodicClampedKernel ((d : ℝ) * u)))) := by
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr fun h => h0 (h ▸ hdD)
    exact (periodicClampedKernel_mul_hasSum_cos hd1 u).mul_left (α d / 4)
  have hsum := hasSum_sum (s := D) hd
  refine hasSum_of_eq_of_eq hsum (fun k => ?_) ?_
  · unfold divisorHarmonicWeight divisorHarmonicMultiplier
    rw [Finset.sum_Filter, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> ring
  · unfold divisorCenteredBernoulliFilter periodicCenteredClampedKernel
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring

/-- **Bernoulli cosine expansion of a general divisor-stencil phase profile.** -/
theorem divisorBernoulliPhaseProfile_hasSum {D : Finset ℕ} (h0 : 0 ∉ D) (α : ℕ → ℝ)
    (N : ℕ) (v : ℝ) :
    HasSum (fun k : ℕ => divisorHarmonicWeight D α k *
      (Real.cos (2 * Real.pi * k * (factorialShiftedFreq N * v)) -
        Real.cos (2 * Real.pi * k * ((N : ℝ) * v))))
      (-(Real.pi ^ 2 / 2) * divisorBernoulliPhaseProfile D α N v) := by
  have h := (divisorCenteredBernoulliFilter_hasSum h0 α (factorialShiftedFreq N * v)).sub
    (divisorCenteredBernoulliFilter_hasSum h0 α ((N : ℝ) * v))
  refine hasSum_of_eq_of_eq h (fun k => by ring) ?_
  unfold divisorBernoulliPhaseProfile
  rw [divisorBernoulliFilter_collar_diff_eq_centered]
  ring

/-- General harmonic-multiplier real phase combination:
`B_{w, S, b}(v) = -(2 / π²) ∑_{k ≥ 0} w_k H_k(v)`. -/
def generalPhaseCombination (w : ℕ → ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) : ℝ :=
  -(2 / Real.pi ^ 2) * ∑' k : ℕ, w k * realHarmonicLayer S b k v

/-- Complex lift of the general harmonic-multiplier phase combination. -/
def generalComplexPhaseCombination (w : ℕ → ℝ) (S : Finset ℕ) (b : ℕ → ℂ) (v : ℝ) : ℂ :=
  -((2 / Real.pi ^ 2 : ℝ) : ℂ) * ∑' k : ℕ, (w k : ℂ) * factorialHarmonicLayer S b k v

theorem generalComplexPhaseCombination_ofReal (w : ℕ → ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    generalComplexPhaseCombination w S (fun n => (b n : ℂ)) v =
      (generalPhaseCombination w S b v : ℂ) := by
  unfold generalComplexPhaseCombination generalPhaseCombination
  have hlayer (k : ℕ) : factorialHarmonicLayer S (fun n => (b n : ℂ)) k v =
      (realHarmonicLayer S b k v : ℂ) := by
    unfold factorialHarmonicLayer realHarmonicLayer
    push_cast
    rfl
  simp_rw [hlayer, ← Complex.ofReal_mul, Complex.ofReal_tsum]

theorem generalPhaseCombination_dyadic_eq (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    generalPhaseCombination dyadicHarmonicWeight S b v = realPhaseCombination S b v := by
  unfold generalPhaseCombination
  rw [(realPhaseCombination_hasSum S b v).tsum_eq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem generalPhaseCombination_hasSum {w : ℕ → ℝ} (hw : Summable fun k => |w k|)
    (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    HasSum (fun k => w k * realHarmonicLayer S b k v)
      (-(Real.pi ^ 2 / 2) * generalPhaseCombination w S b v) := by
  have hs : Summable fun k => w k * realHarmonicLayer S b k v := by
    refine Summable.of_norm_bounded (hw.mul_right (2 * ∑ n ∈ S, |b n|)) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_realHarmonicLayer_le S b k v) (abs_nonneg _)
  refine hs.hasSum.congr_Of_eq ?_
  unfold generalPhaseCombination
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem generalComplexPhaseCombination_hasSum {w : ℕ → ℝ} (hw : Summable fun k => |w k|)
    (S : Finset ℕ) (b : ℕ → ℂ) (v : ℝ) :
    HasSum (fun k => (w k : ℂ) * factorialHarmonicLayer S b k v)
      (-((Real.pi ^ 2 / 2 : ℝ) : ℂ) * generalComplexPhaseCombination w S b v) := by
  have hs : Summable fun k => (w k : ℂ) * factorialHarmonicLayer S b k v := by
    refine Summable.of_norm_bounded (hw.mul_right (2 * ∑ n ∈ S, ‖b n‖)) fun k => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_factorialHarmonicLayer_le S b k v) (abs_nonneg _)
  have h := hs.hasSum
  have heq : -((Real.pi ^ 2 / 2 : ℝ) : ℂ) * generalComplexPhaseCombination w S b v =
      ∑' k, (w k : ℂ) * factorialHarmonicLayer S b k v := by
    unfold generalComplexPhaseCombination
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [← mul_assoc]
    have h1 : -((Real.pi ^ 2 / 2 : ℝ) : ℂ) * -((2 / Real.pi ^ 2 : ℝ) : ℂ) = 1 := by
      push_cast; field_simp; ring
    rw [h1, one_mul]
  exact heq ▸ h

/-- For any divisor stencil `(D, α)` with `0 ∉ D`, the general harmonic phase combination with
weights `divisorHarmonicWeight D α` coincides pointwise with the finite stencil combination
`∑_{n ∈ S} b_n Φ_{D, α, n+1}(v)`. -/
theorem generalPhaseCombination_divisor_eq {D : Finset ℕ} (h0 : 0 ∉ D) (α : ℕ → ℝ)
    (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    generalPhaseCombination (divisorHarmonicWeight D α) S b v =
      ∑ n ∈ S, b n * divisorBernoulliPhaseProfile D α (n + 1) v := by
  have hsum : HasSum (fun k => divisorHarmonicWeight D α k * realHarmonicLayer S b k v)
      (-(Real.pi ^ 2 / 2) * ∑ n ∈ S, b n * divisorBernoulliPhaseProfile D α (n + 1) v) := by
    have hn (n : ℕ) := (divisorBernoulliPhaseProfile_hasSum h0 α (n + 1) v).mul_left (b n)
    have h := hasSum_sum (s := S) fun n _ => hn n
    refine hasSum_of_eq_of_eq h (fun k => ?_) ?_
    · unfold realHarmonicLayer
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
  unfold generalPhaseCombination
  rw [hsum.tsum_eq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- Global Lipschitz bound for any general divisor-stencil Bernoulli filter `P_{D, α}`. -/
theorem abs_divisorBernoulliFilter_sub_le (D : Finset ℕ) (α : ℕ → ℝ) (u u' : ℝ) :
    |divisorBernoulliFilter D α u - divisorBernoulliFilter D α u'| ≤
      ((∑ d ∈ D, |α d| * (d : ℝ)) / 2) * |u - u'| := by
  have hk (x y : ℝ) : |periodicClampedKernel x - periodicClampedKernel y| ≤ |x - y| / 2 := by
    unfold periodicClampedKernel
    rw [show -RHTower.bernoulliPeriodic x - -RHTower.bernoulliPeriodic y =
      -(RHTower.bernoulliPeriodic x - RHTower.bernoulliPeriodic y) by ring, abs_neg]
    exact RHTower.DeletionMixedRefinement.bernoulliPeriodic_lipschitz_bound x y
  unfold divisorBernoulliFilter
  rw [← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [← mul_sub, abs_mul]
  have hd := hk ((d : ℝ) * u) ((d : ℝ) * u')
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg d)] at hd
  calc |α d| * |periodicClampedKernel ((d : ℝ) * u) - periodicClampedKernel ((d : ℝ) * u')|
      ≤ |α d| * ((d : ℝ) * |u - u'| / 2) := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    _ = |α d| * (d : ℝ) / 2 * |u - u'| := by ring

/-- Global Lipschitz constant of a divisor-stencil phase combination `∑_{n ∈ S} b_n Φ_{D, α, n+1}`. -/
def divisorPhaseLipschitz (D : Finset ℕ) (α : ℕ → ℝ) (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, |b n| * (((∑ d ∈ D, |α d| * (d : ℝ)) / 8) *
    (factorialShiftedFreq (n + 1) + ((n + 1 : ℕ) : ℝ)))

theorem divisorPhaseLipschitz_nonneg (D : Finset ℕ) (α : ℕ → ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    0 ≤ divisorPhaseLipschitz D α S b := by
  unfold divisorPhaseLipschitz
  refine Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (mul_nonneg ?_ ?_)
  · exact div_nonneg (Finset.sum_nonneg fun d _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (by norm_num)
  · have := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).1
    have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith

/-- Global Lipschitz bound for `generalPhaseCombination (divisorHarmonicWeight D α) S b`. -/
theorem abs_generalPhaseCombination_divisor_sub_le {D : Finset ℕ} (h0 : 0 ∉ D) (α : ℕ → ℝ)
    (S : Finset ℕ) (b : ℕ → ℝ) (v v' : ℝ) :
    |generalPhaseCombination (divisorHarmonicWeight D α) S b v -
      generalPhaseCombination (divisorHarmonicWeight D α) S b v'| ≤
      divisorPhaseLipschitz D α S b * |v - v'| := by
  rw [generalPhaseCombination_divisor_eq h0, generalPhaseCombination_divisor_eq h0]
  unfold divisorPhaseLipschitz
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [← mul_sub, abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  unfold divisorBernoulliPhaseProfile
  have hlam : 0 ≤ factorialShiftedFreq (n + 1) := by
    have := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).1
    have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h1 := abs_divisorBernoulliFilter_sub_le D α (factorialShiftedFreq (n + 1) * v)
    (factorialShiftedFreq (n + 1) * v')
  have h2 := abs_divisorBernoulliFilter_sub_le D α (((n + 1 : ℕ) : ℝ) * v)
    (((n + 1 : ℕ) : ℝ) * v')
  rw [← mul_sub, abs_mul, abs_of_nonneg hlam] at h1
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n + 1))] at h2
  have he : (divisorBernoulliFilter D α (factorialShiftedFreq (n + 1) * v) -
        divisorBernoulliFilter D α (((n + 1 : ℕ) : ℝ) * v)) / 4 -
      (divisorBernoulliFilter D α (factorialShiftedFreq (n + 1) * v') -
        divisorBernoulliFilter D α (((n + 1 : ℕ) : ℝ) * v')) / 4 =
      ((divisorBernoulliFilter D α (factorialShiftedFreq (n + 1) * v) -
          divisorBernoulliFilter D α (factorialShiftedFreq (n + 1) * v')) -
        (divisorBernoulliFilter D α (((n + 1 : ℕ) : ℝ) * v) -
          divisorBernoulliFilter D α (((n + 1 : ℕ) : ℝ) * v'))) / 4 := by ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hsub := abs_sub
    (divisorBernoulliFilter D α (factorialShiftedFreq (n + 1) * v) -
      divisorBernoulliFilter D α (factorialShiftedFreq (n + 1) * v'))
    (divisorBernoulliFilter D α (((n + 1 : ℕ) : ℝ) * v) -
      divisorBernoulliFilter D α (((n + 1 : ℕ) : ℝ) * v'))
  linarith

/-- Global Lipschitz bound for `generalPhaseCombination w S b` whenever `∑ k |w k| < ∞`
(covering all higher-order non-Bernoulli filters `|w k| ≤ C_w / k³` and all finite harmonic filters). -/
theorem abs_generalPhaseCombination_sub_le_of_summable_mul {w : ℕ → ℝ}
    (hw : Summable fun k : ℕ => (k : ℝ) * |w k|) (S : Finset ℕ) (b : ℕ → ℝ) (v v' : ℝ) :
    |generalPhaseCombination w S b v - generalPhaseCombination w S b v'| ≤
      ((4 / Real.pi) * (∑' k : ℕ, (k : ℝ) * |w k|) *
        ∑ n ∈ S, |b n| * (factorialShiftedFreq (n + 1) + ((n + 1 : ℕ) : ℝ))) * |v - v'| := by
  have hw0 : Summable fun k : ℕ => |w k| := by
    rw [← summable_nat_add_iff 1] at hw ⊢
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_) hw
    have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    exact le_mul_of_one_le_left (abs_nonneg _) this
  set B1 := ∑ n ∈ S, |b n|
  have hB1 : 0 ≤ B1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set L1 := ∑ n ∈ S, |b n| * (factorialShiftedFreq (n + 1) + ((n + 1 : ℕ) : ℝ))
  have hL1 : 0 ≤ L1 := by
    refine Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) ?_
    have := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).1
    have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hlayer_lip (k : ℕ) :
      |realHarmonicLayer S b k v - realHarmonicLayer S b k v'| ≤
        (2 * Real.pi * k * L1) * |v - v'| := by
    unfold realHarmonicLayer
    rw [← Finset.sum_sub_distrib, mul_assoc (2 * Real.pi * (k : ℝ)), Finset.sum_mul, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [← mul_sub, abs_mul]
    have hlam : 0 ≤ factorialShiftedFreq (n + 1) := by
      have := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).1
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hc1 := Real.abs_cos_sub_cos_le
      (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v))
      (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v'))
    have hc2 := Real.abs_cos_sub_cos_le
      (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v))
      (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v'))
    have he1 : 2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v) -
        2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v') =
        (2 * Real.pi * k * factorialShiftedFreq (n + 1)) * (v - v') := by ring
    have he2 : 2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v) -
        2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v') =
        (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) * (v - v') := by ring
    rw [he1, abs_mul, abs_of_nonneg (by positivity)] at hc1
    rw [he2, abs_mul, abs_of_nonneg (by positivity)] at hc2
    have hdiff : Real.cos (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v)) -
          Real.cos (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v)) -
        (Real.cos (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v')) -
          Real.cos (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v'))) =
        (Real.cos (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v)) -
          Real.cos (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v'))) -
        (Real.cos (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v)) -
          Real.cos (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v'))) := by ring
    rw [hdiff]
    have htri := (abs_sub _ _).trans (add_le_add hc1 hc2)
    calc |b n| * |(Real.cos (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v)) -
            Real.cos (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v'))) -
          (Real.cos (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v)) -
            Real.cos (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v')))|
        ≤ |b n| * (2 * Real.pi * k * factorialShiftedFreq (n + 1) * |v - v'| +
            2 * Real.pi * k * ((n + 1 : ℕ) : ℝ) * |v - v'|) :=
          mul_le_mul_of_nonneg_left htri (abs_nonneg _)
      _ = 2 * Real.pi * (k : ℝ) * (|b n| * (factorialShiftedFreq (n + 1) + ((n + 1 : ℕ) : ℝ)) *
            |v - v'|) := by ring
  unfold generalPhaseCombination
  have hs1 : Summable fun k => w k * realHarmonicLayer S b k v :=
    (generalPhaseCombination_hasSum hw0 S b v).summable
  have hs2 : Summable fun k => w k * realHarmonicLayer S b k v' :=
    (generalPhaseCombination_hasSum hw0 S b v').summable
  rw [← mul_sub, ← hs1.tsum_sub hs2, abs_mul, abs_neg,
    abs_of_pos (by positivity : 0 < 2 / Real.pi ^ 2)]
  have hterm (k : ℕ) :
      ‖w k * realHarmonicLayer S b k v - w k * realHarmonicLayer S b k v'‖ ≤
        ((k : ℝ) * |w k|) * (2 * Real.pi * L1 * |v - v'|) := by
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    calc |w k| * |realHarmonicLayer S b k v - realHarmonicLayer S b k v'|
        ≤ |w k| * ((2 * Real.pi * k * L1) * |v - v'|) :=
          mul_le_mul_of_nonneg_left (hlayer_lip k) (abs_nonneg _)
      _ = ((k : ℝ) * |w k|) * (2 * Real.pi * L1 * |v - v'|) := by ring
  have hsum_norm : Summable fun k => ‖w k * realHarmonicLayer S b k v -
      w k * realHarmonicLayer S b k v'‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hw.mul_right _)
  rw [← Real.norm_eq_abs]
  have htsum := (norm_tsum_le_tsum_norm hsum_norm).trans
    (hsum_norm.tsum_le_tsum hterm (hw.mul_right _))
  rw [tsum_mul_right] at htsum
  calc 2 / Real.pi ^ 2 * ‖∑' k, (w k * realHarmonicLayer S b k v - w k * realHarmonicLayer S b k v')‖
      ≤ 2 / Real.pi ^ 2 * ((∑' k, (k : ℝ) * |w k|) * (2 * Real.pi * L1 * |v - v'|)) :=
        mul_le_mul_of_nonneg_left htsum (by positivity)
    _ = ((4 / Real.pi) * (∑' k : ℕ, (k : ℝ) * |w k|) * L1) * |v - v'| := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp
        ring

/-- **Admissible Harmonic Weight Class (`AdmissibleHarmonicWeight w C_w τ`).**
A harmonic weight sequence `w : ℕ → ℝ` is admissible with inverse-square envelope `C_w > 0` and
higher-harmonic tail `τ ∈ [0, 1)` when `w 0 = 0`, `w 1 = 1`, `|w k| ≤ C_w / k²` for all `k`, and
`∑_{k ≥ 2} |w k| ≤ τ < 1`. -/
structure AdmissibleHarmonicWeight (w : ℕ → ℝ) (C_w τ : ℝ) : Prop where
  w_zero : w 0 = 0
  w_one : w 1 = 1
  C_pos : 0 < C_w
  abs_w_le : ∀ k : ℕ, |w k| ≤ C_w / (k : ℝ) ^ 2
  τ_nonneg : 0 ≤ τ
  τ_lt_one : τ < 1
  tsum_tail_le : ∑' k : ℕ, |w (k + 2)| ≤ τ

namespace AdmissibleHarmonicWeight

variable {w : ℕ → ℝ} {C_w τ : ℝ}

theorem summable_abs (hw : AdmissibleHarmonicWeight w C_w τ) :
    Summable fun k : ℕ => |w k| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hw.abs_w_le
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left C_w |>.congr fun k => by ring)

theorem tsum_abs_le (hw : AdmissibleHarmonicWeight w C_w τ) :
    ∑' k : ℕ, |w k| ≤ 1 + τ := by
  have hs := hw.summable_abs
  rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  simp only [zero_add, hw.w_zero, abs_zero, hw.w_one, abs_one]
  have h := hw.tsum_tail_le
  simp only [show ∀ k : ℕ, k + 1 + 1 = k + 2 from fun _ => rfl]
  linarith

theorem abs_generalPhaseCombination_le (hw : AdmissibleHarmonicWeight w C_w τ)
    (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    |generalPhaseCombination w S b v| ≤
      (4 * (1 + τ) / Real.pi ^ 2) * ∑ n ∈ S, |b n| := by
  unfold generalPhaseCombination
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 / Real.pi ^ 2)]
  set B1 := ∑ n ∈ S, |b n|
  have hB1 : 0 ≤ B1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hterm (k : ℕ) : ‖w k * realHarmonicLayer S b k v‖ ≤ |w k| * (2 * B1) := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_realHarmonicLayer_le S b k v) (abs_nonneg _)
  have hs : Summable fun k => ‖w k * realHarmonicLayer S b k v‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hw.summable_abs.mul_right (2 * B1))
  rw [← Real.norm_eq_abs]
  have hle := (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hterm (hw.summable_abs.mul_right _))
  rw [tsum_mul_right] at hle
  have htot := hw.tsum_abs_le
  calc 2 / Real.pi ^ 2 * ‖∑' k, w k * realHarmonicLayer S b k v‖
      ≤ 2 / Real.pi ^ 2 * ((∑' k, |w k|) * (2 * B1)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ 2 / Real.pi ^ 2 * ((1 + τ) * (2 * B1)) := by gcongr
    _ = (4 * (1 + τ) / Real.pi ^ 2) * B1 := by ring

theorem norm_generalComplexPhaseCombination_le (hw : AdmissibleHarmonicWeight w C_w τ)
    (S : Finset ℕ) (b : ℕ → ℂ) (v : ℝ) :
    ‖generalComplexPhaseCombination w S b v‖ ≤
      (4 * (1 + τ) / Real.pi ^ 2) * ∑ n ∈ S, ‖b n‖ := by
  unfold generalComplexPhaseCombination
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 2 / Real.pi ^ 2)]
  set B1 := ∑ n ∈ S, ‖b n‖
  have hB1 : 0 ≤ B1 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hterm (k : ℕ) : ‖(w k : ℂ) * factorialHarmonicLayer S b k v‖ ≤ |w k| * (2 * B1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_factorialHarmonicLayer_le S b k v) (abs_nonneg _)
  have hs : Summable fun k => ‖(w k : ℂ) * factorialHarmonicLayer S b k v‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hw.summable_abs.mul_right (2 * B1))
  have hle := (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hterm (hw.summable_abs.mul_right _))
  rw [tsum_mul_right] at hle
  have htot := hw.tsum_abs_le
  calc 2 / Real.pi ^ 2 * ‖∑' k, (w k : ℂ) * factorialHarmonicLayer S b k v‖
      ≤ 2 / Real.pi ^ 2 * ((∑' k, |w k|) * (2 * B1)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ 2 / Real.pi ^ 2 * ((1 + τ) * (2 * B1)) := by gcongr
    _ = (4 * (1 + τ) / Real.pi ^ 2) * B1 := by ring

theorem continuous_generalComplexPhaseCombination (hw : AdmissibleHarmonicWeight w C_w τ)
    (S : Finset ℕ) (b : ℕ → ℂ) :
    Continuous (generalComplexPhaseCombination w S b) := by
  unfold generalComplexPhaseCombination
  refine continuous_const.mul (continuous_tsum (fun k => continuous_const.mul
    (continuous_factorialHarmonicLayer S b k)) (hw.summable_abs.mul_right (2 * ∑ n ∈ S, ‖b n‖))
    fun k v => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_factorialHarmonicLayer_le S b k v) (abs_nonneg _)

theorem continuous_generalPhaseCombination (hw : AdmissibleHarmonicWeight w C_w τ)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    Continuous (generalPhaseCombination w S b) := by
  have h := continuous_generalComplexPhaseCombination hw S (fun n => (b n : ℂ))
  have heq : generalPhaseCombination w S b =
      fun v => (generalComplexPhaseCombination w S (fun n => (b n : ℂ)) v).re := by
    funext v
    rw [generalComplexPhaseCombination_ofReal, Complex.ofReal_re]
  rw [heq]
  exact Complex.continuous_re.comp h

end AdmissibleHarmonicWeight

/-- **Family 1 (Canonical Dyadic Stencil):** `dyadicHarmonicWeight` satisfies
`AdmissibleHarmonicWeight dyadicHarmonicWeight 1 (3 / 4)`. -/
theorem admissibleHarmonicWeight_dyadic :
    AdmissibleHarmonicWeight dyadicHarmonicWeight 1 (3 / 4) where
  w_zero := dyadicHarmonicWeight_zero
  w_one := dyadicHarmonicWeight_one
  C_pos := one_pos
  abs_w_le := abs_dyadicHarmonicWeight_le
  τ_nonneg := by norm_num
  τ_lt_one := by norm_num
  tsum_tail_le := tsum_abs_dyadicHarmonicWeight_tail_le

/-- **Family 2 (`q`-Adic 3-Scale Sign-Flip Stencils on `{1, q, q²}` for Every `q ≥ 2`):**
Normalized stencil weights `(4, -8/q², 4/q⁴)` on `{1, q, q²}`, harmonic multiplier
`qAdicSignFlipChi q k = 1 - 2[q ∣ k] + [q² ∣ k]`, and harmonic weights
`qAdicSignFlipWeight q k = qAdicSignFlipChi q k / k²`. -/
def qAdicSignFlipStencil (q d : ℕ) : ℝ :=
  if d = 1 then 4 else if d = q then -8 / (q : ℝ) ^ 2 else if d = q ^ 2 then 4 / (q : ℝ) ^ 4 else 0

def qAdicSignFlipChi (q k : ℕ) : ℝ :=
  1 - 2 * (if q ∣ k then 1 else 0) + (if q ^ 2 ∣ k then 1 else 0)

def qAdicSignFlipWeight (q k : ℕ) : ℝ :=
  qAdicSignFlipChi q k / (k : ℝ) ^ 2

theorem qAdicSignFlipChi_one {q : ℕ} (hq : 2 ≤ q) : qAdicSignFlipChi q 1 = 1 := by
  unfold qAdicSignFlipChi
  have h1 : ¬ (q ∣ 1) := fun h => by have := Nat.le_of_dvd one_pos h; omega
  have h2 : ¬ (q ^ 2 ∣ 1) := fun h => by
    have := Nat.le_of_dvd one_pos h
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  simp [h1, h2]

theorem qAdicSignFlipChi_self {q : ℕ} (hq : 2 ≤ q) : qAdicSignFlipChi q q = -1 := by
  unfold qAdicSignFlipChi
  have h2 : ¬ (q ^ 2 ∣ q) := fun h => by
    have := Nat.le_of_dvd (by omega) h
    have : q < q ^ 2 := by nlinarith
    omega
  simp [dvd_refl q, h2]
  ring

theorem qAdicSignFlipChi_sq_mul (q m : ℕ) : qAdicSignFlipChi q (q ^ 2 * m) = 0 := by
  unfold qAdicSignFlipChi
  have h1 : q ∣ q ^ 2 * m := ⟨q * m, by ring⟩
  have h2 : q ^ 2 ∣ q ^ 2 * m := dvd_mul_right (q ^ 2) m
  simp [h1, h2]
  ring

theorem abs_qAdicSignFlipChi_le_one {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    |qAdicSignFlipChi q k| ≤ 1 := by
  unfold qAdicSignFlipChi
  by_cases h1 : q ∣ k
  · by_cases h2 : q ^ 2 ∣ k
    · simp [h1, h2]; norm_num
    · simp [h1, h2]; norm_num
  · have h2 : ¬ (q ^ 2 ∣ k) := fun h => h1 ( dvd_trans ⟨q, sq q⟩ h )
    simp [h1, h2]

theorem divisorHarmonicWeight_qAdicSignFlip_eq {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    divisorHarmonicWeight ({1, q, q ^ 2} : Finset ℕ) (qAdicSignFlipStencil q) k =
      qAdicSignFlipWeight q k := by
  unfold divisorHarmonicWeight qAdicSignFlipWeight divisorHarmonicMultiplier qAdicSignFlipStencil
    qAdicSignFlipChi
  congr 1
  have hq_lt_sq : q < q ^ 2 := by nlinarith
  have h1_mem : (1 : ℕ) ∉ ({q, q ^ 2} : Finset ℕ) := by simp; omega
  have hq_mem : q ∉ ({q ^ 2} : Finset ℕ) := by simp; omega
  have hq_ne1 : q ≠ 1 := by omega
  have hq2_ne1 : q ^ 2 ≠ 1 := by omega
  have hq2_neq : q ^ 2 ≠ q := by omega
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq2_ne0 : (q : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq_pos.ne'
  have hq4_ne0 : (q : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 hq_pos.ne'
  rw [Finset.sum_Filter, Finset.sum_insert h1_mem, Finset.sum_insert hq_mem, Finset.sum_singleton]
  simp only [one_dvd, if_true, Nat.cast_one, one_pow, mul_one, hq_ne1, hq2_ne1, hq2_neq, if_false,
    Nat.cast_pow]
  split_ifs <;> field_simp [hq2_ne0, hq4_ne0] <;> ring

/-- Every `q`-adic 3-scale sign-flip stencil (`q ≥ 2`) satisfies
`AdmissibleHarmonicWeight (qAdicSignFlipWeight q) 1 (3 / 4)`. -/
theorem admissibleHarmonicWeight_qAdicSignFlip {q : ℕ} (hq : 2 ≤ q) :
    AdmissibleHarmonicWeight (qAdicSignFlipWeight q) 1 (3 / 4) where
  w_zero := by simp [qAdicSignFlipWeight]
  w_one := by simp [qAdicSignFlipWeight, qAdicSignFlipChi_one hq]
  C_pos := one_pos
  abs_w_le := fun k => by
    unfold qAdicSignFlipWeight
    rw [abs_div, abs_of_nonneg (sq_nonneg (k : ℝ))]
    exact div_le_div_of_nonneg_right (abs_qAdicSignFlipChi_le_one hq k) (sq_nonneg _)
  τ_nonneg := by norm_num
  τ_lt_one := by norm_num
  tsum_tail_le := by
    have hs : Summable fun k : ℕ => |qAdicSignFlipWeight q (k + 2)| := by
      refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_)
        ((summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two))
      unfold qAdicSignFlipWeight
      rw [abs_div, abs_of_nonneg (sq_nonneg _)]
      exact div_le_div_of_nonneg_right (abs_qAdicSignFlipChi_le_one hq (k + 2)) (sq_nonneg _)
    refine hs.tsum_le_of_sum_range_le fun M => ?_
    rcases eq_or_ne M 0 with rfl | hM0
    · simp; norm_num
    · have hle : (∑ k ∈ Finset.range M, |qAdicSignFlipWeight q (k + 2)|) ≤
          ∑ k ∈ Finset.Icc 2 (M + 1), 1 / (k : ℝ) ^ 2 := by
        rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun k => |qAdicSignFlipWeight q k|) 0 M 2,
          zero_add, ← Finset.Ico_add_one_right_eq_Icc]
        refine Finset.sum_le_sum fun k _ => ?_
        unfold qAdicSignFlipWeight
        rw [abs_div, abs_of_nonneg (sq_nonneg _)]
        exact div_le_div_of_nonneg_right (abs_qAdicSignFlipChi_le_one hq k) (sq_nonneg _)
      have hsplit : Finset.Icc 2 (M + 1) = insert 2 (Finset.Icc 3 (M + 1)) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)] at hle
      have htel := sum_Icc_three_inv_sq_le (M + 1) (by omega)
      have h2 : (1 : ℝ) / ((2 : ℕ) : ℝ) ^ 2 = 1 / 4 := by norm_num
      have hMinv : 0 ≤ 1 / ((M + 1 : ℕ) : ℝ) := by positivity
      linarith

/-- **Family 3 (`q`-Adic 3-Scale Drift-Free Stencils on `{1, q, q²}` for Every `q ≥ 2`):**
Normalized stencil weights `(4, -4(q+1)/q², 4/q³)` on `{1, q, q²}`, which simultaneously cancel
both the linear secular ramp (`L = 0`) and the quadratic drift (`Q = 0`). -/
def qAdicDriftFreeStencil (q d : ℕ) : ℝ :=
  if d = 1 then 4
  else if d = q then -4 * ((q : ℝ) + 1) / (q : ℝ) ^ 2
  else if d = q ^ 2 then 4 / (q : ℝ) ^ 3
  else 0

def qAdicDriftFreeChi (q k : ℕ) : ℝ :=
  1 - ((q : ℝ) + 1) * (if q ∣ k then 1 else 0) + (q : ℝ) * (if q ^ 2 ∣ k then 1 else 0)

def qAdicDriftFreeWeight (q k : ℕ) : ℝ :=
  qAdicDriftFreeChi q k / (k : ℝ) ^ 2

/-- For every `q ≥ 2`, `qAdicDriftFreeStencil q` on `{1, q, q²}` has fundamental harmonic multiplier
`M(1) = 4`, zero linear drift (`L = 0`), and zero quadratic drift (`Q = 0`). -/
theorem qAdicDriftFreeStencil_drifts_zero {q : ℕ} (hq : 2 ≤ q) :
    divisorHarmonicMultiplier ({1, q, q ^ 2} : Finset ℕ) (qAdicDriftFreeStencil q) 1 = 4 ∧
    divisorLinearDrift ({1, q, q ^ 2} : Finset ℕ) (qAdicDriftFreeStencil q) = 0 ∧
    divisorQuadraticDrift ({1, q, q ^ 2} : Finset ℕ) (qAdicDriftFreeStencil q) = 0 := by
  rw [qAdic_three_scale_drift_free_stencil_iff hq 4 (qAdicDriftFreeStencil q)]
  unfold qAdicDriftFreeStencil
  have hq_ne1 : q ≠ 1 := by omega
  have hq2_ne1 : q ^ 2 ≠ 1 := by nlinarith
  have hq2_neq : q ^ 2 ≠ q := by nlinarith
  simp only [if_true, hq_ne1, hq2_ne1, hq2_neq, if_false]
  exact ⟨rfl, by ring, by ring⟩

theorem divisorHarmonicWeight_qAdicDriftFree_eq {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    divisorHarmonicWeight ({1, q, q ^ 2} : Finset ℕ) (qAdicDriftFreeStencil q) k =
      qAdicDriftFreeWeight q k := by
  unfold divisorHarmonicWeight qAdicDriftFreeWeight divisorHarmonicMultiplier qAdicDriftFreeStencil
    qAdicDriftFreeChi
  congr 1
  have hq_lt_sq : q < q ^ 2 := by nlinarith
  have h1_mem : (1 : ℕ) ∉ ({q, q ^ 2} : Finset ℕ) := by simp; omega
  have hq_mem : q ∉ ({q ^ 2} : Finset ℕ) := by simp; omega
  have hq_ne1 : q ≠ 1 := by omega
  have hq2_ne1 : q ^ 2 ≠ 1 := by omega
  have hq2_neq : q ^ 2 ≠ q := by omega
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq2_ne0 : (q : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq_pos.ne'
  have hq3_ne0 : (q : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hq_pos.ne'
  rw [Finset.sum_Filter, Finset.sum_insert h1_mem, Finset.sum_insert hq_mem, Finset.sum_singleton]
  simp only [one_dvd, if_true, Nat.cast_one, one_pow, mul_one, hq_ne1, hq2_ne1, hq2_neq, if_false,
    Nat.cast_pow]
  split_ifs <;> field_simp [hq2_ne0, hq3_ne0] <;> ring

theorem qAdicDriftFreeChi_one {q : ℕ} (hq : 2 ≤ q) : qAdicDriftFreeChi q 1 = 1 := by
  unfold qAdicDriftFreeChi
  have h1 : ¬ (q ∣ 1) := fun h => by have := Nat.le_of_dvd one_pos h; omega
  have h2 : ¬ (q ^ 2 ∣ 1) := fun h => by
    have := Nat.le_of_dvd one_pos h
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  simp [h1, h2]

theorem qAdicDriftFreeChi_self {q : ℕ} (hq : 2 ≤ q) : qAdicDriftFreeChi q q = -(q : ℝ) := by
  unfold qAdicDriftFreeChi
  have h2 : ¬ (q ^ 2 ∣ q) := fun h => by
    have := Nat.le_of_dvd (by omega) h
    have : q < q ^ 2 := by nlinarith
    omega
  simp [dvd_refl q, h2]
  ring

/-- Exact indicator decomposition of `|qAdicDriftFreeChi q k|` for every `q ≥ 2` and `k : ℕ`:
`|χ_{q, df}(k)| = 1 + (q - 1)[q ∣ k] - q[q² ∣ k]`. -/
theorem abs_qAdicDriftFreeChi_eq {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    |qAdicDriftFreeChi q k| =
      1 + ((q : ℝ) - 1) * (if q ∣ k then 1 else 0) -
        (q : ℝ) * (if q ^ 2 ∣ k then 1 else 0) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  unfold qAdicDriftFreeChi
  by_cases h1 : q ∣ k
  · by_cases h2 : q ^ 2 ∣ k
    · simp only [h1, h2, if_true]
      rw [show (1 : ℝ) - ((q : ℝ) + 1) * 1 + (q : ℝ) * 1 = 0 by ring, abs_zero]
      ring
    · simp only [h1, h2, if_true, if_false]
      rw [show (1 : ℝ) - ((q : ℝ) + 1) * 1 + (q : ℝ) * 0 = -(q : ℝ) by ring,
        abs_neg, abs_of_nonneg hq0]
      ring
  · have h2 : ¬ (q ^ 2 ∣ k) := fun h => h1 (dvd_trans ⟨q, sq q⟩ h)
    simp [h1, h2]

theorem abs_qAdicDriftFreeChi_le {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    |qAdicDriftFreeChi q k| ≤ (q : ℝ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  rw [abs_qAdicDriftFreeChi_eq hq]
  by_cases h1 : q ∣ k
  · by_cases h2 : q ^ 2 ∣ k
    · simp [h1, h2]; linarith
    · simp [h1, h2]
  · have h2 : ¬ (q ^ 2 ∣ k) := fun h => h1 (dvd_trans ⟨q, sq q⟩ h)
    simp [h1, h2]; linarith

/-- Exact `HasSum` for `d ∣ k` over `1 / k²`:
`∑_{k : ℕ} (if d ∣ k then 1 / k² else 0) = (π² / 6) / d²` for `d ≥ 1`. -/
theorem hasSum_dvd_inv_sq {d : ℕ} (hd : 1 ≤ d) :
    HasSum (fun k : ℕ => (if d ∣ k then (1 : ℝ) else 0) / (k : ℝ) ^ 2)
      ((Real.pi ^ 2 / 6) / (d : ℝ) ^ 2) := by
  have hinj : Function.Injective (fun n : ℕ => d * n) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left (by omega) h
  refine (hinj.hasSum_iff fun k hk => ?_).mp ?_
  · rw [if_neg]
    · simp
    · rintro ⟨m, rfl⟩
      exact hk ⟨m, rfl⟩
  · have hz := hasSum_zeta_two.div_const ((d : ℝ) ^ 2)
    refine hz.congr_fun fun n => ?_
    simp only [Function.comp_apply, dvd_mul_right, if_true]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · push_cast
      ring

/-- **Exact Higher-Harmonic Tail Identity for `q`-Adic Drift-Free Stencils.**
For every `q ≥ 2`,
`∑_{k = 0}^∞ |qAdicDriftFreeWeight q k| = (π² / 6) (1 + (q² - q - 1) / q³)`. -/
theorem hasSum_abs_qAdicDriftFreeWeight {q : ℕ} (hq : 2 ≤ q) :
    HasSum (fun k : ℕ => |qAdicDriftFreeWeight q k|)
      ((Real.pi ^ 2 / 6) * (1 + ((q : ℝ) ^ 2 - (q : ℝ) - 1) / (q : ℝ) ^ 3)) := by
  have h1 := hasSum_zeta_two
  have hq1 : 1 ≤ q := by omega
  have hq2_1 : 1 ≤ q ^ 2 := by nlinarith
  have h2 := (hasSum_dvd_inv_sq hq1).mul_left ((q : ℝ) - 1)
  have h3 := (hasSum_dvd_inv_sq hq2_1).mul_left (q : ℝ)
  have hcomb := (h1.add h2).sub h3
  have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  refine hasSum_of_eq_of_eq hcomb (fun k => ?_) ?_
  · unfold qAdicDriftFreeWeight
    rw [abs_div, abs_of_nonneg (sq_nonneg (k : ℝ)), abs_qAdicDriftFreeChi_eq hq k]
    ring
  · push_cast
    field_simp [hq_ne]
    ring

/-- **Every `q`-Adic 3-Scale Drift-Free Stencil (`q ≥ 2`) is Admissible (`τ = 24/25 < 1`).**
By the polynomial sum-of-squares identity `5 q³ - 27(q² - q - 1) = (q - 3)²(5q + 3) ≥ 0` and
`π < 3.15`, the higher-harmonic tail is bounded by `(32/27)(π²/6) - 1 ≤ 24/25 < 1` for all `q ≥ 2`. -/
theorem admissibleHarmonicWeight_qAdicDriftFree {q : ℕ} (hq : 2 ≤ q) :
    AdmissibleHarmonicWeight (qAdicDriftFreeWeight q) (q : ℝ) (24 / 25) where
  w_zero := by simp [qAdicDriftFreeWeight]
  w_one := by simp [qAdicDriftFreeWeight, qAdicDriftFreeChi_one hq]
  C_pos := by exact_mod_cast (show 0 < q by omega)
  abs_w_le := fun k => by
    unfold qAdicDriftFreeWeight
    rw [abs_div, abs_of_nonneg (sq_nonneg (k : ℝ))]
    exact div_le_div_of_nonneg_right (abs_qAdicDriftFreeChi_le hq k) (sq_nonneg _)
  τ_nonneg := by norm_num
  τ_lt_one := by norm_num
  tsum_tail_le := by
    have hsum := hasSum_abs_qAdicDriftFreeWeight hq
    have hs := hsum.summable
    have htot := hsum.tsum_eq
    rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add] at htot
    have hw0 : qAdicDriftFreeWeight q 0 = 0 := by simp [qAdicDriftFreeWeight]
    have hw1 : qAdicDriftFreeWeight q 1 = 1 := by
      simp [qAdicDriftFreeWeight, qAdicDriftFreeChi_one hq]
    simp only [zero_add, hw0, abs_zero, hw1, abs_one,
      show ∀ k : ℕ, k + 1 + 1 = k + 2 from fun _ => rfl] at htot
    have htail_eq : (∑' k : ℕ, |qAdicDriftFreeWeight q (k + 2)|) =
        (Real.pi ^ 2 / 6) * (1 + ((q : ℝ) ^ 2 - (q : ℝ) - 1) / (q : ℝ) ^ 3) - 1 := by
      linarith
    rw [htail_eq]
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hq3_pos : (0 : ℝ) < (q : ℝ) ^ 3 := pow_pos hq_pos 3
    have hsos : 0 ≤ ((q : ℝ) - 3) ^ 2 * (5 * (q : ℝ) + 3) := by positivity
    have hrat : 1 + ((q : ℝ) ^ 2 - (q : ℝ) - 1) / (q : ℝ) ^ 3 ≤ 32 / 27 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 27), add_mul, div_mul_eq_mul_div,
        div_le_iff₀ hq3_pos]
      have hid : (32 : ℝ) * (q : ℝ) ^ 3 - (1 * 27 * (q : ℝ) ^ 3 + ((q : ℝ) ^ 2 - (q : ℝ) - 1) * 27) =
          ((q : ℝ) - 3) ^ 2 * (5 * (q : ℝ) + 3) := by ring
      linarith
    have hpi : Real.pi < 63 / 20 := by
      have := Real.pi_lt_d2
      linarith
    have hpi2 : Real.pi ^ 2 / 6 ≤ (63 / 20 : ℝ) ^ 2 / 6 := by
      have := Real.pi_pos
      nlinarith
    have hprod : (Real.pi ^ 2 / 6) * (1 + ((q : ℝ) ^ 2 - (q : ℝ) - 1) / (q : ℝ) ^ 3) ≤
        ((63 / 20 : ℝ) ^ 2 / 6) * (32 / 27) := by
      refine mul_le_mul hpi2 hrat ?_ (by norm_num)
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      have : 0 ≤ (q : ℝ) ^ 2 - (q : ℝ) - 1 := by nlinarith
      positivity
    linarith

/-- **Family 4 (Non-Bernoulli / Higher-Order Fourier-Multiplier Filters):**
For any exponent `p ≥ 2` and coefficient sequence `c : ℕ → ℝ` with `c 1 = 1` and `|c k| ≤ 1`,
`higherOrderHarmonicWeight p c k = if k = 0 then 0 else c k / k^p` satisfies
`AdmissibleHarmonicWeight (higherOrderHarmonicWeight p c) 1 (3 / 4)`, and for `p ≥ 3` has
summable derivative series `∑ k |w_k| < ∞`. -/
def higherOrderHarmonicWeight (p : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else c k / (k : ℝ) ^ p

theorem admissibleHarmonicWeight_higherOrder {p : ℕ} (hp : 2 ≤ p) {c : ℕ → ℝ}
    (hc1 : c 1 = 1) (hcb : ∀ k, |c k| ≤ 1) :
    AdmissibleHarmonicWeight (higherOrderHarmonicWeight p c) 1 (3 / 4) where
  w_zero := by simp [higherOrderHarmonicWeight]
  w_one := by simp [higherOrderHarmonicWeight, hc1]
  C_pos := one_pos
  abs_w_le := fun k => by
    unfold higherOrderHarmonicWeight
    split_ifs with hk
    · simp
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have hpow : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ p := pow_le_pow_right₀ hk1 hp
      rw [abs_div, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg k) p)]
      calc |c k| / (k : ℝ) ^ p ≤ 1 / (k : ℝ) ^ p :=
            div_le_div_of_nonneg_right (hcb k) (by positivity)
        _ ≤ 1 / (k : ℝ) ^ 2 := one_div_le_one_div_of_le (by positivity) hpow
  τ_nonneg := by norm_num
  τ_lt_one := by norm_num
  tsum_tail_le := by
    have hle_dyadic (k : ℕ) : |higherOrderHarmonicWeight p c (k + 2)| ≤
        1 / ((k + 2 : ℕ) : ℝ) ^ 2 := by
      unfold higherOrderHarmonicWeight
      rw [if_neg (by omega), abs_div, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) p)]
      have hk1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by positivity
      have hpow : ((k + 2 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ) ^ p := pow_le_pow_right₀ hk1 hp
      exact (div_le_div_of_nonneg_right (hcb (k + 2)) (by positivity)).trans
        (one_div_le_one_div_of_le (by positivity) hpow)
    have hs : Summable fun k : ℕ => |higherOrderHarmonicWeight p c (k + 2)| :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle_dyadic
        ((summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two))
    refine hs.tsum_le_of_sum_range_le fun M => ?_
    rcases eq_or_ne M 0 with rfl | hM0
    · simp; norm_num
    · have hle : (∑ k ∈ Finset.range M, |higherOrderHarmonicWeight p c (k + 2)|) ≤
          ∑ k ∈ Finset.Icc 2 (M + 1), 1 / (k : ℝ) ^ 2 := by
        rw [Finset.range_eq_Ico,
          Finset.sum_Ico_add' (fun k => |higherOrderHarmonicWeight p c k|) 0 M 2,
          zero_add, ← Finset.Ico_add_one_right_eq_Icc]
        intro
        refine Finset.sum_le_sum fun k hk => ?_
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        simpa [Nat.sub_add_cancel hk2] using hle_dyadic (k - 2)
      have hsplit : Finset.Icc 2 (M + 1) = insert 2 (Finset.Icc 3 (M + 1)) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)] at hle
      have htel := sum_Icc_three_inv_sq_le (M + 1) (by omega)
      have h2 : (1 : ℝ) / ((2 : ℕ) : ℝ) ^ 2 = 1 / 4 := by norm_num
      have hMinv : 0 ≤ 1 / ((M + 1 : ℕ) : ℝ) := by positivity
      linarith

theorem summable_mul_higherOrderHarmonicWeight {p : ℕ} (hp : 3 ≤ p) {c : ℕ → ℝ}
    (hcb : ∀ k, |c k| ≤ 1) :
    Summable fun k : ℕ => (k : ℝ) * |higherOrderHarmonicWeight p c k| := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Nat.cast_nonneg k) (abs_nonneg _))
    (fun k => ?_) (Real.summable_one_div_nat_pow.mpr one_lt_two)
  unfold higherOrderHarmonicWeight
  split_ifs with hk
  · simp
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have hk0 : (0 : ℝ) < k := by positivity
    rw [abs_div, abs_of_nonneg (pow_nonneg hk0.le p)]
    have hpow : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ p := pow_le_pow_right₀ hk1 hp
    calc (k : ℝ) * (|c k| / (k : ℝ) ^ p)
        ≤ (k : ℝ) * (1 / (k : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hcb k) (by positivity)) hk0.le
      _ ≤ (k : ℝ) * (1 / (k : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) hpow) hk0.le
      _ = 1 / (k : ℝ) ^ 2 := by field_simp; ring

/-! ## Section 2: Window Coercivity, Collared & Doubly Collared Mass Floors, Low-Band Mellin Exclusion, `ℓ²`-Uniform Prime/Polar Channels, and Receiver Positivity -/

/-- Window length `L(τ) = 8(1 + τ²) / (1 - τ²)² * K` (`K = 390/π`) for a general admissible
harmonic weight sequence with higher-harmonic tail `τ ∈ [0, 1)`. -/
def generalWindowLength (τ : ℝ) : ℝ :=
  8 * (1 + τ ^ 2) / (1 - τ ^ 2) ^ 2 * factorialWindowGapConstant

theorem generalWindowLength_pos {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    0 < generalWindowLength τ := by
  unfold generalWindowLength
  have h1 : 0 < 1 - τ ^ 2 := by nlinarith
  have hK := factorialWindowGapConstant_pos
  positivity

/-- **Finite-window coercivity for any `AdmissibleHarmonicWeight w C_w τ`.**
On every interval `[a, a + generalWindowLength τ]`,
`∫_a^{a + L(τ)} ‖generalComplexPhaseCombination w S b v‖² dv ≥ (8 K / π⁴) ∑_{n ∈ S} ‖b_n‖²`. -/
theorem generalComplexPhaseCombination_window_lower {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) (S : Finset ℕ) (b : ℕ → ℂ) (a : ℝ) :
    (8 * factorialWindowGapConstant / Real.pi ^ 4) * ∑ n ∈ S, ‖b n‖ ^ 2 ≤
      ∫ v in a..a + generalWindowLength τ, ‖generalComplexPhaseCombination w S b v‖ ^ 2 := by
  set L := generalWindowLength τ
  set K := factorialWindowGapConstant
  set Sb := ∑ n ∈ S, ‖b n‖ ^ 2
  have hτ0 := hw.τ_nonneg
  have hτ1 := hw.τ_lt_one
  have hL : 0 < L := generalWindowLength_pos hτ0 hτ1
  have hK : 0 < K := factorialWindowGapConstant_pos
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hI (k : ℕ) : (∫ v in a..a + L, ‖factorialHarmonicLayer S b k v‖ ^ 2) =
      ∫ v in Ioc a (a + L), ‖factorialHarmonicLayer S b k v‖ ^ 2 :=
    intervalIntegral.integral_of_le (by linarith)
  have h1 : (L - K) * Sb ≤ ∫ v in Ioc a (a + L), ‖factorialHarmonicLayer S b 1 v‖ ^ 2 := by
    have h := (factorialHarmonicLayer_interval_bounds S b (k := 1) le_rfl (r := 1) le_rfl a L).1
    simp only [one_mul, Nat.cast_one, div_one] at h
    rwa [hI] at h
  have hk : ∀ k, 2 ≤ k →
      ∫ v in Ioc a (a + L), ‖factorialHarmonicLayer S b k v‖ ^ 2 ≤ (L + K) * Sb := by
    intro k hk2
    have h := (factorialHarmonicLayer_interval_bounds S b (k := k) (by omega) (r := 1) le_rfl
      a L).2
    simp only [one_mul] at h
    rw [hI] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hSb0)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have : K / k ≤ K := div_le_self hK.le hk1
    linarith
  set θ : ℝ := (1 + τ ^ 2) / 2
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by dsimp [θ]; nlinarith
  have hdom := integral_norm_sq_ge_of_first_harmonic
    (μ := volume.restrict (Ioc a (a + L)))
    (F := fun v => -((Real.pi ^ 2 / 2 : ℝ) : ℂ) * generalComplexPhaseCombination w S b v)
    (generalComplexPhaseCombination_hasSum hw.summable_abs S b) hw.summable_abs
    hw.w_zero hw.w_one hw.tsum_tail_le
    (continuous_factorialHarmonicLayer S b) (norm_factorialHarmonicLayer_le S b) h1 hk hθ0 hθ1
  simp only [norm_neg_pi_sq_half_mul_sq, integral_const_mul] at hdom
  have h1mτ2 : 0 < 1 - τ ^ 2 := by nlinarith
  have h1pτ2 : 0 < 1 + τ ^ 2 := by positivity
  have halg : (1 - θ) * ((L - K) * Sb) - (1 / θ - 1) * τ ^ 2 * ((L + K) * Sb) =
      ((4 - (1 - τ ^ 2) * (1 + 3 * τ ^ 2) / (2 * (1 + τ ^ 2))) * K) * Sb := by
    dsimp [θ, L, generalWindowLength]
    field_simp [h1mτ2.ne', h1pτ2.ne']
    ring
  rw [halg] at hdom
  have hfrac : (1 - τ ^ 2) * (1 + 3 * τ ^ 2) / (2 * (1 + τ ^ 2)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg τ]
  have h2K : (2 * K) * Sb ≤ (Real.pi ^ 4 / 4) *
      ∫ v in Ioc a (a + L), ‖generalComplexPhaseCombination w S b v‖ ^ 2 := by
    nlinarith [mul_nonneg hK.le hSb0]
  have hpi4 : 0 < Real.pi ^ 4 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpi4]
  linarith

/-- **Dilated window upper bound for any `AdmissibleHarmonicWeight w C_w τ`.** -/
theorem generalComplexPhaseCombination_dilated_window_upper {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) (S : Finset ℕ) (b : ℕ → ℂ) {r : ℝ}
    (hr : 1 ≤ r) (a : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    IntervalIntegrable (fun v => ‖generalComplexPhaseCombination w S b (r * v)‖ ^ 2)
      volume a (a + ℓ) ∧
    (∫ v in a..a + ℓ, ‖generalComplexPhaseCombination w S b (r * v)‖ ^ 2) ≤
      (4 * (1 + τ) ^ 2 / Real.pi ^ 4) * (ℓ + factorialWindowGapConstant) * ∑ n ∈ S, ‖b n‖ ^ 2 := by
  set K := factorialWindowGapConstant
  set Sb := ∑ n ∈ S, ‖b n‖ ^ 2
  have hK : 0 < K := factorialWindowGapConstant_pos
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hI (k : ℕ) : (∫ v in a..a + ℓ, ‖factorialHarmonicLayer S b k (r * v)‖ ^ 2) =
      ∫ v in Ioc a (a + ℓ), ‖factorialHarmonicLayer S b k (r * v)‖ ^ 2 :=
    intervalIntegral.integral_of_le (by linarith)
  have hk : ∀ k, 1 ≤ k →
      ∫ v in Ioc a (a + ℓ), ‖factorialHarmonicLayer S b k (r * v)‖ ^ 2 ≤ (ℓ + K) * Sb := by
    intro k hk1
    have h := (factorialHarmonicLayer_interval_bounds S b hk1 hr a ℓ).2
    rw [hI] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hSb0)
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have : K / k ≤ K := div_le_self hK.le hk1'
    linarith
  obtain ⟨hint, hup⟩ := integral_norm_sq_le_of_harmonics
    (μ := volume.restrict (Ioc a (a + ℓ)))
    (H := fun k v => factorialHarmonicLayer S b k (r * v))
    (F := fun v => -((Real.pi ^ 2 / 2 : ℝ) : ℂ) * generalComplexPhaseCombination w S b (r * v))
    (fun v => generalComplexPhaseCombination_hasSum hw.summable_abs S b (r * v)) hw.summable_abs
    hw.w_zero hw.tsum_abs_le
    (fun k => (continuous_factorialHarmonicLayer S b k).comp (continuous_const.mul continuous_id))
    (fun k v => norm_factorialHarmonicLayer_le S b k (r * v)) hk
    (mul_nonneg (by linarith) hSb0)
  simp only [norm_neg_pi_sq_half_mul_sq, integral_const_mul] at hup
  have hpi4 : 0 < Real.pi ^ 4 / 4 := by positivity
  have hint' : IntegrableOn (fun v => ‖generalComplexPhaseCombination w S b (r * v)‖ ^ 2)
      (Ioc a (a + ℓ)) := by
    have := hint.const_mul (4 / Real.pi ^ 4)
    refine this.congr_fun (fun v _ => ?_) measurableSet_Ioc
    simp only [norm_neg_pi_sq_half_mul_sq]
    field_simp
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr hint', ?_⟩
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hgoal : (Real.pi ^ 4 / 4) *
      (∫ v in Ioc a (a + ℓ), ‖generalComplexPhaseCombination w S b (r * v)‖ ^ 2) ≤
      (Real.pi ^ 4 / 4) * ((4 * (1 + τ) ^ 2 / Real.pi ^ 4) * (ℓ + K) * Sb) := by
    calc (Real.pi ^ 4 / 4) *
          (∫ v in Ioc a (a + ℓ), ‖generalComplexPhaseCombination w S b (r * v)‖ ^ 2)
        ≤ (1 + τ) ^ 2 * ((ℓ + K) * Sb) := hup
      _ = (Real.pi ^ 4 / 4) * ((4 * (1 + τ) ^ 2 / Real.pi ^ 4) * (ℓ + K) * Sb) := by
          field_simp; ring
  exact le_of_mul_le_mul_left hgoal hpi4

/-- **`ℓ²` upper bound with the critical weight `v^{-2}` for any `AdmissibleHarmonicWeight`.** -/
theorem integrableOn_rpow_neg_two_mul_norm_sq_generalComplexPhaseCombination_dilate
    {w : ℕ → ℝ} {C_w τ : ℝ} (hw : AdmissibleHarmonicWeight w C_w τ)
    (S : Finset ℕ) (b : ℕ → ℂ) (r : ℝ) :
    IntegrableOn (fun v => v ^ (-2 : ℝ) * ‖generalComplexPhaseCombination w S b (r * v)‖ ^ 2)
      (Ioi 1) := by
  have h1 : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  refine (h1.mul_const (((4 * (1 + τ) / Real.pi ^ 2) * ∑ n ∈ S, ‖b n‖) ^ 2)).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne')).mul
      (((hw.continuous_generalComplexPhaseCombination S b).comp
        (continuous_const.mul continuous_id)).norm.pow 2).continuousAt).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans zero_lt_one hv
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hv0.le _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (hw.norm_generalComplexPhaseCombination_le S b (r * v)) 2) (Real.rpow_nonneg hv0.le _)

/-- Unit-interval upper mass constant for an admissible weight sequence with tail `τ`. -/
def generalUnitIntervalUpper (τ : ℝ) : ℝ :=
  4 * (1 + τ) ^ 2 * (1 + factorialWindowGapConstant) / Real.pi ^ 4

/-- Upper mass constant `U_w(τ) = (π²/6) * generalUnitIntervalUpper τ`. -/
def generalCollarMassUpper (τ : ℝ) : ℝ :=
  Real.pi ^ 2 / 6 * generalUnitIntervalUpper τ

theorem generalCollarMassUpper_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < generalCollarMassUpper τ := by
  unfold generalCollarMassUpper generalUnitIntervalUpper
  have := factorialWindowGapConstant_pos
  positivity

theorem integral_Ioi_one_rpow_neg_two_mul_norm_sq_general_dilate_le
    {w : ℕ → ℝ} {C_w τ : ℝ} (hw : AdmissibleHarmonicWeight w C_w τ)
    (S : Finset ℕ) (b : ℕ → ℂ) {r : ℝ} (hr : 1 ≤ r) :
    (∫ v in Ioi 1, v ^ (-2 : ℝ) * ‖generalComplexPhaseCombination w S b (r * v)‖ ^ 2) ≤
      generalCollarMassUpper τ * ∑ n ∈ S, ‖b n‖ ^ 2 := by
  set Sb := ∑ n ∈ S, ‖b n‖ ^ 2
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set g : ℝ → ℝ := fun v => v ^ (-2 : ℝ) * ‖generalComplexPhaseCombination w S b (r * v)‖ ^ 2
  have hint := integrableOn_rpow_neg_two_mul_norm_sq_generalComplexPhaseCombination_dilate hw S b r
  have hlim := intervalIntegral_tendsto_integral_Ioi (f := g) (μ := volume) 1 hint
    (b := fun M : ℕ => 1 + (M : ℝ)) (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  refine le_of_tendsto' hlim fun M => ?_
  have hpiece : ∀ j : ℕ, IntervalIntegrable g volume (1 + (j : ℝ)) (1 + ((j + 1 : ℕ) : ℝ)) ∧
      (∫ v in (1 + (j : ℝ))..(1 + ((j + 1 : ℕ) : ℝ)), g v) ≤
        (1 / ((j + 1 : ℕ) : ℝ) ^ 2) * (generalUnitIntervalUpper τ * Sb) := by
    intro j
    set aj : ℝ := 1 + (j : ℝ)
    have haj1 : 1 ≤ aj := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have haj0 : 0 < aj := by linarith
    have hend : (1 : ℝ) + ((j + 1 : ℕ) : ℝ) = aj + 1 := by dsimp [aj]; push_cast; ring
    rw [hend]
    have hgi : IntervalIntegrable g volume aj (aj + 1) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
      exact hint.mono_set fun v hv => lt_of_le_of_lt haj1 hv.1
    obtain ⟨hBi, hBle⟩ := generalComplexPhaseCombination_dilated_window_upper hw S b hr aj zero_le_one
    refine ⟨hgi, ?_⟩
    have hmono : (∫ v in aj..aj + 1, g v) ≤
        ∫ v in aj..aj + 1, aj ^ (-2 : ℝ) * ‖generalComplexPhaseCombination w S b (r * v)‖ ^ 2 := by
      refine intervalIntegral.integral_mono_on (by linarith) hgi (hBi.const_mul _) fun v hv => ?_
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos haj0 hv.1 (by norm_num)) (sq_nonneg _)
    rw [intervalIntegral.integral_const_mul] at hmono
    have hpow : aj ^ (-2 : ℝ) = 1 / ((j + 1 : ℕ) : ℝ) ^ 2 := by
      rw [Real.rpow_neg haj0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        one_div]
      dsimp [aj]; push_cast; ring_nf
    rw [hpow] at hmono
    refine hmono.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    unfold generalUnitIntervalUpper
    have he : 4 * (1 + τ) ^ 2 / Real.pi ^ 4 * (1 + factorialWindowGapConstant) * Sb =
        4 * (1 + τ) ^ 2 * (1 + factorialWindowGapConstant) / Real.pi ^ 4 * Sb := by ring
    rwa [← he]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
    (a := fun k : ℕ => 1 + (k : ℝ)) (n := M) fun k _ => (hpiece k).1
  simp only [Nat.cast_zero, add_zero] at hsum
  rw [← hsum]
  have hz : Summable fun d : ℕ => 1 / (d : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  have hJ0 : 0 ≤ generalUnitIntervalUpper τ * Sb := by
    unfold generalUnitIntervalUpper
    have := factorialWindowGapConstant_pos
    have := hw.τ_nonneg
    positivity
  calc (∑ k ∈ Finset.range M, ∫ v in (1 + (k : ℝ))..(1 + ((k + 1 : ℕ) : ℝ)), g v)
      ≤ ∑ k ∈ Finset.range M, (1 / ((k + 1 : ℕ) : ℝ) ^ 2) * (generalUnitIntervalUpper τ * Sb) :=
        Finset.sum_le_sum fun k _ => (hpiece k).2
    _ = (∑ k ∈ Finset.range M, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) * (generalUnitIntervalUpper τ * Sb) := by
        rw [Finset.sum_mul]
    _ ≤ (∑' d : ℕ, 1 / (d : ℝ) ^ 2) * (generalUnitIntervalUpper τ * Sb) := by
        refine mul_le_mul_of_nonneg_right ?_ hJ0
        have himg : ∑ k ∈ Finset.range M, 1 / ((k + 1 : ℕ) : ℝ) ^ 2 =
            ∑ d ∈ (Finset.range M).image (fun k : ℕ => k + 1), 1 / (d : ℝ) ^ 2 := by
          rw [Finset.sum_image fun x _ y _ h => Nat.add_right_cancel h]
        rw [himg]
        exact hz.sum_le_tsum _ fun d _ => by positivity
    _ = generalCollarMassUpper τ * Sb := by
        unfold generalCollarMassUpper
        rw [hasSum_zeta_two.tsum_eq]; ring

/-- **Collared critical source** `g_{w,c}(x) = σ(e^{-x} - 1) e^{x/2} B_{w,b}(e^{-x}) 1_{x ≤ 0}`
associated to a general harmonic weight sequence `w : ℕ → ℝ`. -/
def generalCollaredSource (w : ℕ → ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  (Iic (0 : ℝ)).indicator (fun y => Real.smoothTransition (Real.exp (-y) - 1) *
    (Real.exp (y / 2) * generalPhaseCombination w S b (Real.exp (-y)))) x

/-- **Doubly collared compact critical source** `g_{w}^V(x) = χ(e^{-x}/V) g_{w,c}(x)` supported in
`[-log(2V), 0]`. -/
def generalTruncatedSource (w : ℕ → ℝ) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  criticalUpperCutoff (Real.exp (-x) / V) * generalCollaredSource w S b x

/-- Lower mass constant `A_w(τ) = (8 K / π⁴) / (2 + generalWindowLength τ)²` of the collared
critical source on `[2, 2 + generalWindowLength τ]`. -/
def generalCollarMassLower (τ : ℝ) : ℝ :=
  (8 * factorialWindowGapConstant / Real.pi ^ 4) / (2 + generalWindowLength τ) ^ 2

theorem generalCollarMassLower_pos {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    0 < generalCollarMassLower τ := by
  unfold generalCollarMassLower
  have hK := factorialWindowGapConstant_pos
  have hL := generalWindowLength_pos hτ0 hτ1
  positivity

/-- **Physical mass floor and ceiling for `generalCollaredSource`.**
For every `AdmissibleHarmonicWeight w C_w τ`, `generalCollaredSource w S b` is an
`AdmissibleSource` (`L¹ ∩ L²`) and satisfies
`generalCollarMassLower τ * ∑ b_n² ≤ ∫ (generalCollaredSource w S b)² ≤ generalCollarMassUpper τ * ∑ b_n²`. -/
theorem generalCollaredSource_mass_bounds {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) (S : Finset ℕ) (b : ℕ → ℝ) :
    AdmissibleSource (generalCollaredSource w S b) ∧
    generalCollarMassLower τ * ∑ n ∈ S, b n ^ 2 ≤ ∫ x, generalCollaredSource w S b x ^ 2 ∧
    (∫ x, generalCollaredSource w S b x ^ 2) ≤ generalCollarMassUpper τ * ∑ n ∈ S, b n ^ 2 := by
  set B := generalPhaseCombination w S b
  set Bc := generalComplexPhaseCombination w S (fun n => (b n : ℂ))
  have hB_eq (v : ℝ) : ‖Bc v‖ ^ 2 = B v ^ 2 := by
    rw [generalComplexPhaseCombination_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsq_eq : (∫ x, generalCollaredSource w S b x ^ 2) =
      ∫ v in Ioi (1 : ℝ), Real.smoothTransition (v - 1) ^ 2 * B v ^ 2 / v ^ 2 := by
    set H : ℝ → ℝ := fun v => Real.smoothTransition (v - 1) ^ 2 * B v ^ 2
    have hpt : ∀ x, generalCollaredSource w S b x ^ 2 =
        (Iic (0 : ℝ)).indicator (fun y => Real.exp y * H (Real.exp (-y))) x := by
      intro x
      by_cases hx : x ≤ 0
      · rw [indicator_of_mem (show x ∈ Iic 0 from hx), generalCollaredSource,
          indicator_of_mem (show x ∈ Iic 0 from hx)]
        have : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; ring_nf
        simp only [H]
        rw [mul_pow, mul_pow, this]
        ring
      · rw [indicator_of_notMem (show x ∉ Iic 0 from hx), generalCollaredSource,
          indicator_of_notMem (show x ∉ Iic 0 from hx), sq, mul_zero]
    rw [funext hpt, integral_indicator measurableSet_Iic, integral_Iic_zero_exp_mul_comp_exp_neg H]
  have hDom : IntegrableOn (fun v => v ^ (-2 : ℝ) * ‖Bc v‖ ^ 2) (Ioi 1) := by
    simpa using integrableOn_rpow_neg_two_mul_norm_sq_generalComplexPhaseCombination_dilate hw
      S (fun n => (b n : ℂ)) 1
  have hInt_Ioi : IntegrableOn (fun v => Real.smoothTransition (v - 1) ^ 2 * B v ^ 2 / v ^ 2)
      (Ioi 1) := by
    refine hDom.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun v hv => ?_) measurableSet_Ioi
      have hv0 : (0 : ℝ) < v := lt_trans zero_lt_one hv
      exact (((((Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)).pow 2).mul
        ((hw.continuous_generalPhaseCombination S b).pow 2)).continuousAt).div
          (continuous_id.pow 2).continuousAt (pow_ne_zero 2 hv0.ne')).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := lt_trans zero_lt_one hv
      have hσ : Real.smoothTransition (v - 1) ^ 2 ≤ 1 :=
        pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
      rw [Real.norm_of_nonneg (by positivity), hB_eq, Real.rpow_neg hv0.le,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (sq_nonneg _) hσ) (sq_nonneg _)
  -- AdmissibleSource: L¹ and L²
  have hAdm : AdmissibleSource (generalCollaredSource w S b) := by
    set C0 := (4 * (1 + τ) / Real.pi ^ 2) * ∑ n ∈ S, |b n|
    have hC0 : 0 ≤ C0 := by
      have := hw.τ_nonneg
      have := Finset.sum_nonneg fun n (_ : n ∈ S) => abs_nonneg (b n)
      positivity
    have hcont : Continuous (generalCollaredSource w S b) := by
      have heq : generalCollaredSource w S b = fun y =>
          Real.smoothTransition (Real.exp (-y) - 1) *
            (Real.exp (y / 2) * B (Real.exp (-y))) := by
        funext y
        unfold generalCollaredSource
        by_cases hy : y ≤ 0
        · rw [indicator_of_mem (show y ∈ Iic 0 from hy)]
        · rw [indicator_of_notMem (show y ∉ Iic 0 from hy)]
          have hle : Real.exp (-y) ≤ 1 := by
            rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith [not_le.mp hy])
          rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
      rw [heq]
      have he : Continuous fun y : ℝ => Real.exp (-y) := Real.continuous_exp.comp continuous_neg
      exact (Real.smoothTransition.continuous.comp (he.sub continuous_const)).mul
        ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
          ((hw.continuous_generalPhaseCombination S b).comp he))
    have hL1 : Integrable fun x => (generalCollaredSource w S b x : ℂ) := by
      have hexp : IntegrableOn (fun y : ℝ => C0 * Real.exp (y / 2)) (Iic 0) := by
        have h1 : IntegrableOn (fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * y)) (Ioi 0) :=
          integrableOn_exp_mul_Ioi (by norm_num) 0
        have h2 := h1.comp_neg
        simp only [neg_Ioi, neg_zero] at h2
        refine ((h2.const_mul C0).mono_set Iic_subset_Iic.rfl).congr_fun (fun y _ => ?_) measurableSet_Iic
        congr 2; ring
      rw [← integrable_indicator_iff measurableSet_Iic] at hexp
      refine hexp.mono' (Complex.continuous_ofReal.comp hcont).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      by_cases hx : x ≤ 0
      · rw [indicator_of_mem (show x ∈ Iic 0 from hx), generalCollaredSource,
          indicator_of_mem (show x ∈ Iic 0 from hx), Complex.norm_real, Real.norm_eq_abs,
          abs_mul, abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _),
          abs_of_pos (Real.exp_pos _)]
        have hσ := Real.smoothTransition.le_one (Real.exp (-x) - 1)
        have hB := hw.abs_generalPhaseCombination_le S b (Real.exp (-x))
        calc Real.smoothTransition (Real.exp (-x) - 1) * (Real.exp (x / 2) * |B (Real.exp (-x))|)
            ≤ 1 * (Real.exp (x / 2) * C0) :=
              mul_le_mul hσ (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le) (by positivity) zero_le_one
          _ = C0 * Real.exp (x / 2) := by ring
      · rw [indicator_of_notMem (show x ∉ Iic 0 from hx), generalCollaredSource,
          indicator_of_notMem (show x ∉ Iic 0 from hx), Complex.ofReal_zero, norm_zero]
    have hL2 : MemLp (fun x => (generalCollaredSource w S b x : ℂ)) 2 := by
      rw [memLp_two_iff_integrable_sq_norm (Complex.continuous_ofReal.comp hcont).aestronglyMeasurable]
      have hexp2 : IntegrableOn (fun y : ℝ => C0 ^ 2 * Real.exp y) (Iic 0) := by
        have h1 : IntegrableOn (fun y : ℝ => Real.exp ((-1 : ℝ) * y)) (Ioi 0) :=
          integrableOn_exp_mul_Ioi (by norm_num) 0
        have h2 := h1.comp_neg
        simp only [neg_Ioi, neg_zero] at h2
        refine (h2.const_mul (C0 ^ 2)).congr_fun (fun y _ => ?_) measurableSet_Iic
        congr 2; ring
      rw [← integrable_indicator_iff measurableSet_Iic] at hexp2
      refine hexp2.mono' ((Complex.continuous_ofReal.comp hcont).norm.pow 2).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      by_cases hx : x ≤ 0
      · rw [indicator_of_mem (show x ∈ Iic 0 from hx), generalCollaredSource,
          indicator_of_mem (show x ∈ Iic 0 from hx), Complex.norm_real, Real.norm_eq_abs, sq_abs,
          Real.norm_of_nonneg (sq_nonneg _), mul_pow, mul_pow]
        have hσ : Real.smoothTransition (Real.exp (-x) - 1) ^ 2 ≤ 1 :=
          pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
        have hB : B (Real.exp (-x)) ^ 2 ≤ C0 ^ 2 := by
          rw [← sq_abs (B _)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hw.abs_generalPhaseCombination_le S b _) 2
        have hex : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; ring_nf
        rw [hex]
        calc Real.smoothTransition (Real.exp (-x) - 1) ^ 2 * (Real.exp x * B (Real.exp (-x)) ^ 2)
            ≤ 1 * (Real.exp x * C0 ^ 2) :=
              mul_le_mul hσ (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le) (by positivity) zero_le_one
          _ = C0 ^ 2 * Real.exp x := by ring
      · rw [indicator_of_notMem (show x ∉ Iic 0 from hx), generalCollaredSource,
          indicator_of_notMem (show x ∉ Iic 0 from hx), Complex.ofReal_zero, norm_zero, sq, mul_zero,
          norm_zero]
    exact ⟨hL1, hL2⟩
  -- Upper bound
  have hup : (∫ x, generalCollaredSource w S b x ^ 2) ≤
      generalCollarMassUpper τ * ∑ n ∈ S, b n ^ 2 := by
    rw [hsq_eq]
    have h1 := integral_Ioi_one_rpow_neg_two_mul_norm_sq_general_dilate_le hw S
      (fun n => (b n : ℂ)) le_rfl
    simp only [one_mul, hB_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h1
    refine (setIntegral_mono_on hInt_Ioi ?_ measurableSet_Ioi fun v hv => ?_).trans h1
    · simpa [hB_eq] using hDom
    · have hv0 : 0 < v := lt_trans zero_lt_one hv
      have hσ : Real.smoothTransition (v - 1) ^ 2 ≤ 1 :=
        pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
      rw [Real.rpow_neg hv0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (sq_nonneg _) hσ) (sq_nonneg _)
  -- Lower bound on `[2, 2 + generalWindowLength τ]`
  have hlo : generalCollarMassLower τ * ∑ n ∈ S, b n ^ 2 ≤
      ∫ x, generalCollaredSource w S b x ^ 2 := by
    rw [hsq_eq]
    set L := generalWindowLength τ
    have hL : 0 < L := generalWindowLength_pos hw.τ_nonneg hw.τ_lt_one
    have hsub : Ioc 2 (2 + L) ⊆ Ioi (1 : ℝ) := fun v hv => lt_trans one_lt_two hv.1
    have hrest : (∫ v in Ioc 2 (2 + L), Real.smoothTransition (v - 1) ^ 2 * B v ^ 2 / v ^ 2) ≤
        ∫ v in Ioi 1, Real.smoothTransition (v - 1) ^ 2 * B v ^ 2 / v ^ 2 :=
      setIntegral_mono_set hInt_Ioi (Eventually.of_forall fun v => by positivity)
        (Eventually.of_forall hsub)
    have hwin := generalComplexPhaseCombination_window_lower hw S (fun n => (b n : ℂ)) 2
    simp only [hB_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hwin
    rw [intervalIntegral.integral_of_le (by linarith)] at hwin
    have hB_int : IntegrableOn (fun v => B v ^ 2) (Ioc 2 (2 + L)) :=
      ((hw.continuous_generalPhaseCombination S b).pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hpt : (∫ v in Ioc 2 (2 + L), B v ^ 2 / (2 + L) ^ 2) ≤
        ∫ v in Ioc 2 (2 + L), Real.smoothTransition (v - 1) ^ 2 * B v ^ 2 / v ^ 2 := by
      refine setIntegral_mono_on (hB_int.div_const _) (hInt_Ioi.mono_set hsub) measurableSet_Ioc
        fun v hv => ?_
      have hv2 : 2 ≤ v := hv.1.le
      have hσ : Real.smoothTransition (v - 1) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith)
      rw [hσ, one_pow, one_mul]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (pow_le_pow_left₀ (by linarith) hv.2 2)
    rw [integral_div] at hpt
    unfold generalCollarMassLower
    rw [div_mul_eq_mul_div]
    exact (div_le_div_of_nonneg_right hwin (sq_nonneg _)).trans (hpt.trans hrest)
  exact ⟨hAdm, hlo, hup⟩

/-- **Low-frequency Mellin exclusion for `generalCollaredSource`.**
For any `AdmissibleHarmonicWeight w C_w τ` and `|t| ≤ π (n + 1)` on `S`,
`‖paperFT (generalCollaredSource w S b) t‖ ≤ 2 * C_w * criticalCollarLowFreqConstant * ∑_{n ∈ S} |b_n| / (n + 1)`. -/
theorem norm_paperFT_generalCollaredSource_le {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) (S : Finset ℕ) (b : ℕ → ℝ) {t : ℝ}
    (ht : ∀ n ∈ S, |t| ≤ Real.pi * ((n + 1 : ℕ) : ℝ)) :
    ‖paperFT (fun x => (generalCollaredSource w S b x : ℂ)) t‖ ≤
      (2 * C_w * criticalCollarLowFreqConstant) * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) := by
  set bc : ℕ → ℂ := fun n => (b n : ℂ)
  set B := generalComplexPhaseCombination w S bc
  -- Step 1: Mellin representation `paperFT g_{w,c} t = ∫_{v>1} B(v) a_c(v) e^{-it log v} dv`
  have hFT : paperFT (fun x => (generalCollaredSource w S b x : ℂ)) t =
      ∫ v in Ioi (1 : ℝ), B v * criticalCollarMellinKernel t v := by
    have h1 : paperFT (fun x => (generalCollaredSource w S b x : ℂ)) t = ∫ y in Iic (0 : ℝ),
        ((Real.smoothTransition (Real.exp (-y) - 1) * Real.exp (y / 2) : ℝ) : ℂ) * B (Real.exp (-y)) *
          Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) := by
      unfold paperFT
      rw [← integral_indicator measurableSet_Iic]
      congr 1; funext y
      by_cases hy : y ≤ 0
      · simp only [generalCollaredSource, indicator_of_mem (show y ∈ Iic 0 from hy), B,
          generalComplexPhaseCombination_ofReal]
        push_cast; ring
      · simp only [generalCollaredSource, indicator_of_notMem (show y ∉ Iic 0 from hy),
          Complex.ofReal_zero, zero_mul]
    have h2 : (∫ y in Iic (0 : ℝ),
        ((Real.smoothTransition (Real.exp (-y) - 1) * Real.exp (y / 2) : ℝ) : ℂ) * B (Real.exp (-y)) *
          Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))) =
        ∫ y in Ioi (0 : ℝ), ((Real.smoothTransition (Real.exp y - 1) * Real.exp (-y / 2) : ℝ) : ℂ) *
          B (Real.exp y) * Complex.exp (-(Complex.I * ((t * y : ℝ) : ℂ))) := by
      have h := integral_comp_neg_Iic (0 : ℝ) (fun y : ℝ =>
        ((Real.smoothTransition (Real.exp y - 1) * Real.exp (-y / 2) : ℝ) : ℂ) *
          B (Real.exp y) * Complex.exp (-(Complex.I * ((t * y : ℝ) : ℂ))))
      simp only [neg_zero] at h
      rw [← h]
      refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
      rw [show -(-y) / 2 = y / 2 by ring,
        show (-(Complex.I * ((t * -y : ℝ) : ℂ))) = Complex.I * (t : ℂ) * (y : ℂ) by push_cast; ring]
    have h3 := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := Real.exp)
      (f' := Real.exp) measurableSet_Ioi (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
      Real.exp_injective.injOn (fun v => B v * criticalCollarMellinKernel t v)
    rw [Real.image_exp_Ioi, Real.exp_zero] at h3
    rw [h1, h2, h3]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    rw [abs_of_pos (Real.exp_pos y), Complex.real_smul]
    unfold criticalCollarMellinKernel criticalCollarAmplitude
    rw [Real.log_exp, ← Real.exp_mul]
    have he : Real.exp y * Real.exp (y * -(3 / 2)) = Real.exp (-y / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← he]; push_cast; ring
  -- Step 2: Expand B into harmonic layers and apply `norm_integral_factorialHarmonicLayer_criticalCollarMellinKernel_le`
  rw [hFT]
  set C := criticalCollarPhaseConstant
  have hC := criticalCollarPhaseConstant_nonneg
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  set Cb := 2 * ∑ n ∈ S, ‖bc n‖
  have hCb0 : 0 ≤ Cb := by positivity
  set fk : ℕ → ℝ → ℂ := fun k v =>
    -((2 / Real.pi ^ 2 : ℝ) : ℂ) * ((w k : ℂ) *
      (factorialHarmonicLayer S bc k v * criticalCollarMellinKernel t v))
  have hpt (v : ℝ) : B v * criticalCollarMellinKernel t v = ∑' k, fk k v := by
    unfold B generalComplexPhaseCombination
    have hs : Summable fun k => (w k : ℂ) * factorialHarmonicLayer S bc k v :=
      (generalComplexPhaseCombination_hasSum hw.summable_abs S bc v).summable
    rw [mul_assoc, ← tsum_mul_right, ← tsum_mul_left]
    refine tsum_congr fun k => by simp only [fk]; ring
  have hker_int : IntegrableOn (fun v : ℝ => v ^ (-3 / 2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hfk_int (k : ℕ) : Integrable (fk k) (volume.restrict (Ioi 1)) := by
    refine ((hker_int.const_mul Cb).const_mul (2 / Real.pi ^ 2 * |w k|)).mono' ?_ ?_
    · refine (continuous_const.mul (continuous_const.mul
        ((continuous_factorialHarmonicLayer S bc k).mul ?_))).aestronglyMeasurable
      unfold criticalCollarMellinKernel
      refine (Complex.continuous_ofReal.comp contDiff_criticalCollarAmplitude.continuous).mul ?_
      refine Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_const.mul ?_))))
      exact Real.continuous_log
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := lt_trans zero_lt_one hv
      simp only [fk, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : 0 ≤ 2 / Real.pi ^ 2), Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) (by positivity)
      exact mul_le_mul (norm_factorialHarmonicLayer_le S bc k v)
        (norm_criticalCollarMellinKernel_le hv0) (norm_nonneg _) hCb0
  have hfk_norm (k : ℕ) : (∫ v in Ioi 1, ‖fk k v‖) ≤
      (2 / Real.pi ^ 2 * |w k|) * (Cb * ∫ v in Ioi (1 : ℝ), v ^ (-3 / 2 : ℝ)) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_on (hfk_int k).norm ((hker_int.const_mul Cb).const_mul _)
      measurableSet_Ioi fun v hv => ?_
    have hv0 : 0 < v := lt_trans zero_lt_one hv
    simp only [fk, Real.norm_eq_abs, norm_mul, norm_neg, Complex.norm_real,
      abs_of_pos (by positivity : 0 < 2 / Real.pi ^ 2)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) (by positivity)
    exact mul_le_mul (norm_factorialHarmonicLayer_le S bc k v)
      (norm_criticalCollarMellinKernel_le hv0) (norm_nonneg _) hCb0
  have hfk_sum : Summable fun k => ∫ v in Ioi 1, ‖fk k v‖ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hfk_norm
      ((hw.summable_abs.mul_left (2 / Real.pi ^ 2)).mul_right _)
  have hexch : (∫ v in Ioi (1 : ℝ), B v * criticalCollarMellinKernel t v) =
      ∑' k, ∫ v in Ioi (1 : ℝ), fk k v := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun v _ => hpt v]
    exact (integral_tsum_of_summable_integral_norm hfk_int hfk_sum).symm
  have hk_bound (k : ℕ) : ‖∫ v in Ioi (1 : ℝ), fk k v‖ ≤
      (2 * C_w * C / Real.pi ^ 3 * T) * (1 / (k : ℝ) ^ 2) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [fk, hw.w_zero]
    · simp only [fk, integral_const_mul, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : 0 ≤ 2 / Real.pi ^ 2), Real.norm_eq_abs]
      have hlayer := (norm_integral_factorialHarmonicLayer_criticalCollarMellinKernel_le S bc hk ht).2
      have hwk := hw.abs_w_le k
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hsum_le : (∑ n ∈ S, ‖bc n‖ * (C / (Real.pi * (k : ℝ) * ((n + 1 : ℕ) : ℝ)))) ≤
          (C / Real.pi) * T := by
        calc ∑ n ∈ S, ‖bc n‖ * (C / (Real.pi * (k : ℝ) * ((n + 1 : ℕ) : ℝ)))
            ≤ ∑ n ∈ S, ‖bc n‖ * (C / (Real.pi * 1 * ((n + 1 : ℕ) : ℝ))) := by
              refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              exact div_le_div_of_nonneg_left hC (by positivity) (by nlinarith [Real.pi_pos])
          _ = (C / Real.pi) * T := by
              dsimp [T, bc]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun n _ => ?_
              rw [Complex.norm_real, Real.norm_eq_abs]; ring
      calc 2 / Real.pi ^ 2 * (|w k| *
            ‖∫ v in Ioi (1 : ℝ), factorialHarmonicLayer S bc k v * criticalCollarMellinKernel t v‖)
          ≤ 2 / Real.pi ^ 2 * ((C_w / (k : ℝ) ^ 2) * ((C / Real.pi) * T)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hwk (hlayer.trans hsum_le) (norm_nonneg _) (by have := hw.C_pos; positivity))
              (by positivity)
        _ = (2 * C_w * C / Real.pi ^ 3 * T) * (1 / (k : ℝ) ^ 2) := by ring
  have hz2 : Summable fun k : ℕ => 1 / (k : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  have hs_int : Summable fun k => ‖∫ v in Ioi (1 : ℝ), fk k v‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hk_bound (hz2.mul_left _)
  rw [hexch]
  refine (norm_tsum_le_tsum_norm hs_int).trans ?_
  have htsum := (hs_int.tsum_le_tsum hk_bound (hz2.mul_left _)).trans_eq (tsum_mul_left)
  refine htsum.trans ?_
  have hz_le := tsum_one_div_nat_sq_le_two
  have hC0 := hw.C_pos
  unfold criticalCollarLowFreqConstant
  have h1 : (2 * C_w * C / Real.pi ^ 3 * T) * (∑' k : ℕ, 1 / (k : ℝ) ^ 2) ≤
      (2 * C_w * C / Real.pi ^ 3 * T) * 2 :=
    mul_le_mul_of_nonneg_left hz_le (by positivity)
  have hgoal : (2 * C_w * C / Real.pi ^ 3 * T) * 2 ≤
      2 * C_w * (3 * (C + 1) / Real.pi ^ 3) * T := by
    have hle : 4 * C ≤ 6 * (C + 1) := by linarith
    calc (2 * C_w * C / Real.pi ^ 3 * T) * 2
        = (C_w * T / Real.pi ^ 3) * (4 * C) := by ring
      _ ≤ (C_w * T / Real.pi ^ 3) * (6 * (C + 1)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 2 * C_w * (3 * (C + 1) / Real.pi ^ 3) * T := by ring
  exact h1.trans hgoal

/-- **Low-frequency spectral density bound for `generalCollaredSource`.**
For `n + 1 ≥ M ≥ 2` on `S` and `|t| ≤ π M`,
`‖paperFT (generalCollaredSource w S b) t‖² ≤ (2 (2 C_w D_c)² / M) ∑_{n ∈ S} b_n²`. -/
theorem norm_sq_paperFT_generalCollaredSource_le {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ}
    (hM : 2 ≤ M) (hS : ∀ n ∈ S, M ≤ n + 1) {t : ℝ} (ht : |t| ≤ Real.pi * M) :
    ‖paperFT (fun x => (generalCollaredSource w S b x : ℂ)) t‖ ^ 2 ≤
      2 * (2 * C_w * criticalCollarLowFreqConstant) ^ 2 / M * ∑ n ∈ S, b n ^ 2 := by
  have ht' : ∀ n ∈ S, |t| ≤ Real.pi * ((n + 1 : ℕ) : ℝ) := fun n hn => ht.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hS n hn) Real.pi_pos.le)
  have h1 := norm_paperFT_generalCollaredSource_le hw S b ht'
  set D := 2 * C_w * criticalCollarLowFreqConstant
  have hC0 := hw.C_pos
  have hD0 : 0 < D := mul_pos (mul_pos zero_lt_two hC0) criticalCollarLowFreqConstant_pos
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) with hT
  have hcs : T ^ 2 ≤ (∑ n ∈ S, b n ^ 2) * ∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun n => |b n|) (fun n => 1 / ((n + 1 : ℕ) : ℝ))
    simpa only [hT, mul_one_div, sq_abs] using h
  have hinv : (∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2) ≤ 2 / (M : ℝ) := by
    have h := sum_low_freq_sq_le_two_mul_sq_div (S.map ⟨fun n => n + 1, add_left_injective 1⟩) hM
      (by simpa using hS) 1
    simpa [Finset.sum_map] using h
  have hE : 0 ≤ ∑ n ∈ S, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ‖paperFT (fun x => (generalCollaredSource w S b x : ℂ)) t‖ ^ 2 ≤ (D * T) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = D ^ 2 * T ^ 2 := by ring
    _ ≤ D ^ 2 * ((∑ n ∈ S, b n ^ 2) * (2 / (M : ℝ))) :=
        mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul_of_nonneg_left hinv hE)) (sq_nonneg _)
    _ = 2 * D ^ 2 / M * ∑ n ∈ S, b n ^ 2 := by ring

/-- Logarithmic archimedean slope `s_w(τ) = e^{-1/2} generalCollarMassLower τ / 2` of a general
admissible harmonic source. -/
def generalCollarArchLogSlope (τ : ℝ) : ℝ :=
  Real.exp (-(1 / 2 : ℝ)) * (generalCollarMassLower τ / 2)

/-- Logarithmic archimedean offset `c_w(C_w, τ)` of a general admissible harmonic source. -/
def generalCollarArchLogOffset (C_w τ : ℝ) : ℝ :=
  3 + Real.log (1 / lowFreqRelativeCutoff (generalCollarMassLower τ)
    (2 * C_w * criticalCollarLowFreqConstant))

theorem generalCollarArchLogSlope_pos {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    0 < generalCollarArchLogSlope τ := by
  unfold generalCollarArchLogSlope
  have := generalCollarMassLower_pos hτ0 hτ1
  positivity

/-- **Logarithmic archimedean Lévy coercivity for `generalCollaredSource`.**
For every `AdmissibleHarmonicWeight w C_w τ` and every family on scales `n + 1 ≥ M ≥ 2`,
`sourceLevyEnergy (generalCollaredSource w S b) ≥ s_w(τ) (log M - c_w(C_w, τ)) ∑_{n ∈ S} b_n²`. -/
theorem ofReal_le_sourceLevyEnergy_generalCollaredSource {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ}
    (hM : 2 ≤ M) (hS : ∀ n ∈ S, M ≤ n + 1) :
    ENNReal.ofReal (generalCollarArchLogSlope τ *
      (Real.log M - generalCollarArchLogOffset C_w τ) * ∑ n ∈ S, b n ^ 2) ≤
      sourceLevyEnergy (generalCollaredSource w S b) := by
  obtain ⟨hAdm, hlo, -⟩ := generalCollaredSource_mass_bounds hw S b
  have hA := generalCollarMassLower_pos hw.τ_nonneg hw.τ_lt_one
  have hD : 0 < 2 * C_w * criticalCollarLowFreqConstant :=
    mul_pos (mul_pos zero_lt_two hw.C_pos) criticalCollarLowFreqConstant_pos
  unfold generalCollarArchLogSlope generalCollarArchLogOffset
  exact ofReal_le_sourceLevyEnergy hAdm hA hD
    (Finset.sum_nonneg fun n _ => sq_nonneg (b n)) hM hlo
    (fun t ht => norm_sq_paperFT_generalCollaredSource_le hw S b hM hS ht)

/-! ### `ℓ²`-Uniform Prime Channel for General Admissible Harmonic Sources -/

/-- **Harmonic reduction of a dilation correlation for `generalPhaseCombination`.** -/
theorem abs_integral_weight_generalPhaseCombination_dilate_le_of_bilinear
    {w : ℕ → ℝ} {C_w τ : ℝ} (hw : AdmissibleHarmonicWeight w C_w τ)
    {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1)) (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ)
    {μ : ℕ × ℕ → ℝ} (hμ : Summable μ) (hμ0 : ∀ p, 0 ≤ μ p)
    (hbil : ∀ p : ℕ × ℕ, 1 ≤ p.1 → 1 ≤ p.2 → 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) *
      |∑ n ∈ S, ∑ n' ∈ S, b n * b n' *
        dyadicCrossKernel (weightCosineTransform φ) p.1 ((p.2 * r : ℕ) : ℝ) n n'| ≤ μ p) :
    |∫ v in Ioi 1, φ v *
      (generalPhaseCombination w S b v * generalPhaseCombination w S b (r * v))| ≤
      C_w ^ 2 * (4 / Real.pi ^ 4 * ∑' p, μ p) := by
  set B1 := ∑ n ∈ S, |b n|
  have hB1 : 0 ≤ B1 := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hpi4 : 0 < 4 / Real.pi ^ 4 := by positivity
  have hC0 := hw.C_pos
  set h := realHarmonicLayer S b
  have hw2 : Summable fun p : ℕ × ℕ => |w p.1| * |w p.2| :=
    hw.summable_abs.mul_of_nonneg hw.summable_abs (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  have hhc (k : ℕ) : Continuous (h k) := by
    show Continuous (realHarmonicLayer S b k)
    unfold realHarmonicLayer
    fun_prop
  set f : ℕ × ℕ → ℝ → ℝ := fun p v =>
    4 / Real.pi ^ 4 * (w p.1 * w p.2) * (φ v * (h p.1 v * h p.2 (r * v)))
  have hpt (v : ℝ) : φ v *
      (generalPhaseCombination w S b v * generalPhaseCombination w S b (r * v)) =
      ∑' p, f p v := by
    have h1 := generalPhaseCombination_hasSum hw.summable_abs S b v
    have h2 := generalPhaseCombination_hasSum hw.summable_abs S b (r * v)
    have hs : Summable fun p : ℕ × ℕ => (w p.1 * h p.1 v) * (w p.2 * h p.2 (r * v)) := by
      refine Summable.of_norm_bounded (hw2.mul_right ((2 * B1) ^ 2)) fun p => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      have e1 := abs_realHarmonicLayer_le S b p.1 v
      have e2 := abs_realHarmonicLayer_le S b p.2 (r * v)
      have := mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
      calc |w p.1| * |h p.1 v| * (|w p.2| * |h p.2 (r * v)|) =
            |w p.1| * |w p.2| * (|h p.1 v| * |h p.2 (r * v)|) := by ring
        _ ≤ |w p.1| * |w p.2| * ((2 * B1) * (2 * B1)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = |w p.1| * |w p.2| * (2 * B1) ^ 2 := by ring
    have hm := (h1.mul h2 hs).mul_left (4 / Real.pi ^ 4 * φ v)
    have heq : (fun p => f p v) = fun i => 4 / Real.pi ^ 4 * φ v *
        (w i.1 * realHarmonicLayer S b i.1 v *
          (w i.2 * realHarmonicLayer S b i.2 (r * v))) := by
      funext p
      simp only [f, h]
      ring
    rw [heq, hm.tsum_eq]
    field_simp
    ring
  have hint (p : ℕ × ℕ) : Integrable (f p) (volume.restrict (Ioi 1)) := by
    have hc : Continuous fun v => h p.1 v * h p.2 (r * v) :=
      (hhc p.1).mul ((hhc p.2).comp (continuous_const.mul continuous_id))
    have := (hφ.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_realHarmonicLayer_le S b p.1 v) (abs_realHarmonicLayer_le S b p.2 _)
        (abs_nonneg _) (by positivity)))
    exact this.const_mul _
  have hnorm (p : ℕ × ℕ) : ∫ v in Ioi 1, ‖f p v‖ ≤
      4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) * ((2 * B1) ^ 2 * ∫ v in Ioi 1, |φ v|) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_on (hint p).norm ((hφ.abs.const_mul _).const_mul _) measurableSet_Ioi
      fun v _ => ?_
    simp only [f, Real.norm_eq_abs, abs_mul, abs_of_pos hpi4]
    have e1 := abs_realHarmonicLayer_le S b p.1 v
    have e2 := abs_realHarmonicLayer_le S b p.2 (r * v)
    have := mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
    calc 4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) * (|φ v| * (|h p.1 v| * |h p.2 (r * v)|)) ≤
          4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) * (|φ v| * ((2 * B1) * (2 * B1))) := by
          gcongr
      _ = _ := by ring
  have hsumm : Summable fun p => ∫ v in Ioi 1, ‖f p v‖ :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg fun _ => norm_nonneg _) hnorm
      ((hw2.mul_left (4 / Real.pi ^ 4)).mul_right ((2 * B1) ^ 2 * ∫ v in Ioi 1, |φ v|))
  have hexch : ∫ v in Ioi 1, φ v *
      (generalPhaseCombination w S b v * generalPhaseCombination w S b (r * v)) =
      ∑' p, ∫ v in Ioi 1, f p v := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun v _ => hpt v]
    exact (integral_tsum_of_summable_integral_norm hint hsumm).symm
  have hbound (p : ℕ × ℕ) : |∫ v in Ioi 1, f p v| ≤ (C_w ^ 2 * (4 / Real.pi ^ 4)) * μ p := by
    have hμp := hμ0 p
    rcases Nat.eq_zero_or_pos p.1 with hk | hk
    · simp only [f, hk, hw.w_zero, zero_mul, mul_zero, integral_zero, abs_zero]
      positivity
    rcases Nat.eq_zero_or_pos p.2 with hl | hl
    · simp only [f, hl, hw.w_zero, zero_mul, mul_zero, integral_zero, abs_zero]
      positivity
    simp only [f]
    rw [integral_const_mul, integral_mul_realHarmonicLayer_mul_dilate hφ, abs_mul, abs_mul,
      abs_of_pos hpi4, abs_mul]
    have hwk := hw.abs_w_le p.1
    have hwl := hw.abs_w_le p.2
    have hb := hbil p hk hl
    have hw_prod : |w p.1| * |w p.2| ≤ C_w ^ 2 * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2)) := by
      calc |w p.1| * |w p.2| ≤ (C_w / (p.1 : ℝ) ^ 2) * (C_w / (p.2 : ℝ) ^ 2) :=
            mul_le_mul hwk hwl (abs_nonneg _) (by positivity)
        _ = C_w ^ 2 * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2)) := by ring
    calc 4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) *
          |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel (weightCosineTransform φ) p.1
            ((p.2 * r : ℕ) : ℝ) n n'|
        ≤ 4 / Real.pi ^ 4 * (C_w ^ 2 * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2))) *
          |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel (weightCosineTransform φ) p.1
            ((p.2 * r : ℕ) : ℝ) n n'| := by gcongr
      _ = (C_w ^ 2 * (4 / Real.pi ^ 4)) * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) *
          |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel (weightCosineTransform φ) p.1
            ((p.2 * r : ℕ) : ℝ) n n'|) := by ring
      _ ≤ (C_w ^ 2 * (4 / Real.pi ^ 4)) * μ p :=
          mul_le_mul_of_nonneg_left hb (by positivity)
  have hgs : Summable fun p => (C_w ^ 2 * (4 / Real.pi ^ 4)) * μ p := hμ.mul_left _
  have habs : Summable fun p => ‖∫ v in Ioi 1, f p v‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => by rw [Real.norm_eq_abs]; exact hbound p) hgs
  rw [hexch, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm habs).trans ?_
  refine (habs.tsum_le_tsum (fun p => by rw [Real.norm_eq_abs]; exact hbound p) hgs).trans (le_of_eq ?_)
  rw [tsum_mul_left, mul_assoc]

/-- **Dyadic dilation correlation inequality for `generalPhaseCombination`.**
For any `AdmissibleHarmonicWeight w C_w τ`, on every dyadic block `M ≤ n + 1 ≤ 2M` and for every
dilation `r ≥ 1`,
`|∫_{v>1} φ(v) B_{w,b}(v) B_{w,b}(rv) dv| ≤ C_w² (4/π⁴) (dyadicDilationConstant A B / √r) ∑ b_n²`. -/
theorem abs_integral_weight_generalPhaseCombination_dilate_le
    {w : ℕ → ℝ} {C_w τ : ℝ} (hw : AdmissibleHarmonicWeight w C_w τ)
    {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1))
    {A B : ℝ} (hA : ∀ f, |weightCosineTransform φ f| ≤ A)
    (hB : ∀ f, f ≠ 0 → |weightCosineTransform φ f| ≤ B / f ^ 2) (hB0 : 0 ≤ B)
    {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hS : DyadicScaleBlock S M) (b : ℕ → ℝ)
    {r : ℕ} (hr : 1 ≤ r) :
    |∫ v in Ioi 1, φ v *
      (generalPhaseCombination w S b v * generalPhaseCombination w S b (r * v))| ≤
      C_w ^ 2 * (4 / Real.pi ^ 4 * (dyadicDilationConstant A B / Real.sqrt r) * ∑ n ∈ S, b n ^ 2) := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  set m : ℕ × ℕ → ℝ := fun p =>
    4 * (A + (80 * (Real.pi ^ 2 / 3) + 2) * B) * (1 / ((p.1 : ℝ) * Real.sqrt p.1) * (1 / (p.2 : ℝ) ^ 2)) +
      68 * B * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2))
  have hz2 : Summable fun l : ℕ => 1 / (l : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  have hm : Summable m := by
    refine ((summable_inv_mul_sqrt.mul_of_nonneg hz2 (fun _ => by positivity) (fun _ => by positivity)).mul_left _).add
      ((hz2.mul_of_nonneg hz2 (fun _ => by positivity) (fun _ => by positivity)).mul_left _)
  have hn1 : Summable fun k : ℕ => ‖1 / ((k : ℝ) * Real.sqrt k)‖ :=
    summable_inv_mul_sqrt.abs.congr fun k => (Real.norm_eq_abs _).symm
  have hn2 : Summable fun l : ℕ => ‖1 / (l : ℝ) ^ 2‖ := hz2.abs.congr fun l => (Real.norm_eq_abs _).symm
  have hmsum : ∑' p, m p = dyadicDilationConstant A B := by
    unfold dyadicDilationConstant
    rw [Summable.tsum_add ((summable_inv_mul_sqrt.mul_of_nonneg hz2 (fun _ => by positivity)
        (fun _ => by positivity)).mul_left _)
      ((hz2.mul_of_nonneg hz2 (fun _ => by positivity) (fun _ => by positivity)).mul_left _),
      tsum_mul_left, tsum_mul_left,
      tsum_mul_tsum_of_summable_norm hn1 hn2, tsum_mul_tsum_of_summable_norm hn2 hn2]
  have hm0 (p : ℕ × ℕ) : 0 ≤ m p := by simp only [m]; positivity
  have h := abs_integral_weight_generalPhaseCombination_dilate_le_of_bilinear hw hφ S b r
    (μ := fun p => 1 / Real.sqrt r * E * m p) (hm.mul_left (1 / Real.sqrt r * E))
    (fun p => by have := hm0 p; positivity) fun p hk hl => by
      have hr' : (1 : ℝ) ≤ ((p.2 * r : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hk1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hk
      have hker := abs_bilinear_dyadicCrossKernel_le hA hB hB0 hM hS hk1 hr' b
      have hmaj := weight_mul_resonance_le hA0 hB0 hk hl hr
      calc 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) *
            |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel (weightCosineTransform φ) p.1
              ((p.2 * r : ℕ) : ℝ) n n'|
          ≤ 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) *
            (2 * (dyadicResonanceBound A B p.1 ((p.2 * r : ℕ) : ℝ) +
              2 * B / ((p.2 * r : ℕ) : ℝ) ^ 2) * E) := by gcongr
        _ = E * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) * (2 * (dyadicResonanceBound A B p.1
              ((p.2 * r : ℕ) : ℝ) + 2 * B / ((p.2 * r : ℕ) : ℝ) ^ 2))) := by ring
        _ ≤ E * (1 / Real.sqrt r * m p) := by gcongr
        _ = _ := by ring
  refine h.trans (le_of_eq ?_)
  rw [tsum_mul_left, hmsum]
  ring

/-- Collared prime atom for `generalCollaredSource w S b`. -/
def generalCollaredPrimeAtom (w : ℕ → ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) : ℝ :=
  (if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ) else 0) *
    ∫ x, generalCollaredSource w S b x * generalCollaredSource w S b (x - Real.log r)

/-- Collared prime channel `∑_r Λ(r)/√r · ac_{w,c}(log r)` for `generalCollaredSource`. -/
def generalCollaredPrimeEnergy (w : ℕ → ℝ) (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑' r : ℕ, generalCollaredPrimeAtom w S b r

/-- Truncated prime atom for `generalTruncatedSource w V S b`. -/
def generalTruncatedPrimeAtom (w : ℕ → ℝ) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) : ℝ :=
  (if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ) else 0) *
    ∫ x, generalTruncatedSource w V S b x * generalTruncatedSource w V S b (x - Real.log r)

/-- Truncated prime channel for `generalTruncatedSource w V S b`. -/
def generalTruncatedPrimeEnergy (w : ℕ → ℝ) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑' r : ℕ, generalTruncatedPrimeAtom w V S b r

theorem integral_generalCollaredSource_mul_dilate (w : ℕ → ℝ) (S : Finset ℕ) (b : ℕ → ℝ)
    {r : ℕ} (hr : 2 ≤ r) :
    ∫ x, generalCollaredSource w S b x * generalCollaredSource w S b (x - Real.log r) =
      1 / Real.sqrt r * ∫ v in Ioi 1, criticalCollarWeight v *
        (generalPhaseCombination w S b v * generalPhaseCombination w S b (r * v)) := by
  set R := generalPhaseCombination w S b
  have hr0 : (0 : ℝ) < r := by positivity
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hsqrt : Real.exp (Real.log r / 2) = Real.sqrt r := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr0]; ring_nf
  have hpt : ∀ x, generalCollaredSource w S b x * generalCollaredSource w S b (x - Real.log r) =
      (Iic (0 : ℝ)).indicator (fun x => 1 / Real.sqrt r * (Real.exp x *
        (Real.smoothTransition (Real.exp (-x) - 1) * (R (Real.exp (-x)) * R (r * Real.exp (-x)))))) x := by
    intro x
    by_cases hx : x ≤ 0
    · rw [indicator_of_mem (show x ∈ Iic 0 from hx)]
      have hxr : x - Real.log r ≤ 0 := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ r)]
      have hexp : Real.exp (-(x - Real.log r)) = r * Real.exp (-x) := by
        rw [neg_sub, Real.exp_sub, Real.exp_log hr0, Real.exp_neg]; field_simp
      have hc : Real.smoothTransition (r * Real.exp (-x) - 1) = 1 := by
        refine Real.smoothTransition.one_of_one_le ?_
        have : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
        nlinarith
      have hhalf : Real.exp ((x - Real.log r) / 2) = Real.exp (x / 2) / Real.sqrt r := by
        rw [← hsqrt, ← Real.exp_sub]; ring_nf
      have hxx : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by rw [← Real.exp_add]; ring_nf
      simp only [generalCollaredSource, indicator_of_mem (show x ∈ Iic 0 from hx),
        indicator_of_mem (show x - Real.log r ∈ Iic 0 from hxr), R, hexp, hc, hhalf]
      have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
      field_simp
      rw [← hxx]; ring
    · rw [indicator_of_notMem (show x ∉ Iic 0 from hx)]
      simp only [generalCollaredSource, indicator_of_notMem (show x ∉ Iic 0 from hx), zero_mul]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Iic, integral_const_mul,
    integral_Iic_zero_exp_mul_comp_exp_neg (fun v => Real.smoothTransition (v - 1) * (R v * R (r * v)))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [criticalCollarWeight]
  ring

theorem integral_generalTruncatedSource_mul_dilate {V : ℝ} (hV : 0 < V) (w : ℕ → ℝ)
    (S : Finset ℕ) (b : ℕ → ℝ) {r : ℕ} (hr : 2 ≤ r) :
    ∫ x, generalTruncatedSource w V S b x * generalTruncatedSource w V S b (x - Real.log r) =
      1 / Real.sqrt r * ∫ v in Ioi 1, criticalCollarWeight v * criticalUpperCutoff (r * v / V) *
        (generalPhaseCombination w S b v * generalPhaseCombination w S b (r * v)) := by
  set R := generalPhaseCombination w S b
  have hr0 : (0 : ℝ) < r := by positivity
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hsqrt : Real.exp (Real.log r / 2) = Real.sqrt r := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr0]; ring_nf
  have hpt : ∀ x, generalTruncatedSource w V S b x * generalTruncatedSource w V S b (x - Real.log r) =
      (Iic (0 : ℝ)).indicator (fun x => 1 / Real.sqrt r * (Real.exp x *
        (Real.smoothTransition (Real.exp (-x) - 1) * criticalUpperCutoff (r * Real.exp (-x) / V) *
          (R (Real.exp (-x)) * R (r * Real.exp (-x)))))) x := by
    intro x
    by_cases hx : x ≤ 0
    · rw [indicator_of_mem (show x ∈ Iic 0 from hx)]
      have hxr : x - Real.log r ≤ 0 := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ r)]
      have hexp : Real.exp (-(x - Real.log r)) = r * Real.exp (-x) := by
        rw [neg_sub, Real.exp_sub, Real.exp_log hr0, Real.exp_neg]; field_simp
      have he1 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
      have hc : Real.smoothTransition (r * Real.exp (-x) - 1) = 1 :=
        Real.smoothTransition.one_of_one_le (by nlinarith)
      have hcut : criticalUpperCutoff (Real.exp (-x) / V) * criticalUpperCutoff (r * Real.exp (-x) / V) =
          criticalUpperCutoff (r * Real.exp (-x) / V) := by
        rcases le_or_gt 2 (r * Real.exp (-x) / V) with h | h
        · rw [criticalUpperCutoff_eq_zero h, mul_zero]
        · have : Real.exp (-x) / V ≤ 1 := by
            rw [div_le_one hV]
            have h' : r * Real.exp (-x) < 2 * V := by rwa [div_lt_iff₀ hV] at h
            nlinarith
          rw [criticalUpperCutoff_eq_one this, one_mul]
      have hhalf : Real.exp ((x - Real.log r) / 2) = Real.exp (x / 2) / Real.sqrt r := by
        rw [← hsqrt, ← Real.exp_sub]; ring_nf
      have hxx : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by rw [← Real.exp_add]; ring_nf
      simp only [generalTruncatedSource, generalCollaredSource,
        indicator_of_mem (show x ∈ Iic 0 from hx),
        indicator_of_mem (show x - Real.log r ∈ Iic 0 from hxr), R, hexp, hc, hhalf]
      rw [← hxx]
      calc _ = criticalUpperCutoff (Real.exp (-x) / V) * criticalUpperCutoff (r * Real.exp (-x) / V) *
            (1 / Real.sqrt r * (Real.exp (x / 2) * Real.exp (x / 2) *
              (Real.smoothTransition (Real.exp (-x) - 1) *
                (R (Real.exp (-x)) * R (r * Real.exp (-x)))))) := by ring
        _ = _ := by rw [hcut]; ring
    · rw [indicator_of_notMem (show x ∉ Iic 0 from hx)]
      simp only [generalTruncatedSource, generalCollaredSource,
        indicator_of_notMem (show x ∉ Iic 0 from hx), mul_zero, zero_mul]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Iic, integral_const_mul,
    integral_Iic_zero_exp_mul_comp_exp_neg (fun v => Real.smoothTransition (v - 1) *
      criticalUpperCutoff (r * v / V) * (R v * R (r * v)))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [criticalCollarWeight]
  ring

/-- **`ℓ²`-uniform collared prime channel for `generalCollaredSource`.**
For any `AdmissibleHarmonicWeight w C_w τ`, on every dyadic block `M ≤ n + 1 ≤ 2M` (`M ≥ 1`),
`|generalCollaredPrimeEnergy w S b| ≤ C_w² * criticalCollaredPrimeConstant * ∑_{n ∈ S} b_n²`. -/
theorem abs_generalCollaredPrimeEnergy_le_of_dyadic {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M)
    (hS : DyadicScaleBlock S M) (b : ℕ → ℝ) :
    |generalCollaredPrimeEnergy w S b| ≤
      (C_w ^ 2 * criticalCollaredPrimeConstant) * ∑ n ∈ S, b n ^ 2 := by
  set C := C_w ^ 2 * (4 / Real.pi ^ 4 *
    dyadicDilationConstant criticalCollarMass criticalCollarCurvature * ∑ n ∈ S, b n ^ 2)
  have hsum : Summable (envelopePrimeMajorant 1) :=
    summable_envelopePrimeMajorant_of_half_lt (by norm_num)
  have hbd (r : ℕ) : |generalCollaredPrimeAtom w S b r| ≤ C * envelopePrimeMajorant 1 r := by
    unfold generalCollaredPrimeAtom envelopePrimeMajorant
    split_ifs with hr
    · have hr0 : (0 : ℝ) < r := by positivity
      have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
      have hK := abs_integral_weight_generalPhaseCombination_dilate_le hw
        integrableOn_criticalCollarWeight abs_weightCosineTransform_criticalCollarWeight_le
        (fun f hf => abs_weightCosineTransform_criticalCollarWeight_le_div_sq hf)
        criticalCollarCurvature_nonneg hM hS b (r := r) (by omega)
      rw [integral_generalCollaredSource_mul_dilate w S b hr, abs_mul, abs_mul,
        abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hs.le),
        abs_of_pos (by positivity : 0 < 1 / Real.sqrt r)]
      have hpow : (r : ℝ) ^ ((1 : ℝ) + 1 / 2) = Real.sqrt r * Real.sqrt r * Real.sqrt r := by
        rw [Real.rpow_add hr0, Real.rpow_one, ← Real.sqrt_eq_rpow, Real.mul_self_sqrt hr0.le]
      rw [hpow]
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := r)
      calc (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r * |_|)
          ≤ (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r *
            (C_w ^ 2 * (4 / Real.pi ^ 4 *
              (dyadicDilationConstant criticalCollarMass criticalCollarCurvature / Real.sqrt r) *
                ∑ n ∈ S, b n ^ 2))) := by gcongr
        _ = C * ((ArithmeticFunction.vonMangoldt r : ℝ) / (Real.sqrt r * Real.sqrt r * Real.sqrt r)) := by
            dsimp [C]; field_simp
    · simp
  have habs : Summable fun r => ‖generalCollaredPrimeAtom w S b r‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun r => by rw [Real.norm_eq_abs]; exact hbd r) (hsum.mul_left C)
  unfold generalCollaredPrimeEnergy
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm habs).trans ?_
  refine (habs.tsum_le_tsum (fun r => by rw [Real.norm_eq_abs]; exact hbd r)
    (hsum.mul_left C)).trans (le_of_eq ?_)
  rw [tsum_mul_left]
  unfold criticalCollaredPrimeConstant
  dsimp [C]; ring

/-- **`ℓ²`-uniform truncated prime channel for `generalTruncatedSource`.**
For any `AdmissibleHarmonicWeight w C_w τ` and `V > 0`, on every dyadic block `M ≤ n + 1 ≤ 2M`
(`M ≥ 1`),
`|generalTruncatedPrimeEnergy w V S b| ≤ C_w² * criticalTruncatedPrimeConstant * ∑_{n ∈ S} b_n²`,
uniformly in `V > 0`. -/
theorem abs_generalTruncatedPrimeEnergy_le_of_dyadic {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) {V : ℝ} (hV : 0 < V)
    {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hS : DyadicScaleBlock S M) (b : ℕ → ℝ) :
    |generalTruncatedPrimeEnergy w V S b| ≤
      (C_w ^ 2 * criticalTruncatedPrimeConstant) * ∑ n ∈ S, b n ^ 2 := by
  set C := C_w ^ 2 * (4 / Real.pi ^ 4 *
    dyadicDilationConstant criticalCollarMass criticalTruncatedCurvature * ∑ n ∈ S, b n ^ 2)
  have hsum : Summable (envelopePrimeMajorant 1) :=
    summable_envelopePrimeMajorant_of_half_lt (by norm_num)
  have hbd (r : ℕ) : |generalTruncatedPrimeAtom w V S b r| ≤ C * envelopePrimeMajorant 1 r := by
    unfold generalTruncatedPrimeAtom envelopePrimeMajorant
    split_ifs with hr
    · have hr0 : (0 : ℝ) < r := by positivity
      have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
      have hl : 0 ≤ (r : ℝ) / V := by positivity
      obtain ⟨hA, hB⟩ := abs_weightCosineTransform_criticalTruncatedWeight_le hl
      have hK := abs_integral_weight_generalPhaseCombination_dilate_le hw
        (integrableOn_criticalTruncatedWeight ((r : ℝ) / V)) hA hB
        criticalTruncatedCurvature_nonneg hM hS b (r := r) (by omega)
      have hw_eq : (∫ v in Ioi 1, criticalCollarWeight v * criticalUpperCutoff (r * v / V) *
          (generalPhaseCombination w S b v * generalPhaseCombination w S b (r * v))) =
          ∫ v in Ioi 1, criticalTruncatedWeight ((r : ℝ) / V) v *
            (generalPhaseCombination w S b v * generalPhaseCombination w S b (r * v)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        simp only [criticalTruncatedWeight]
        rw [show (r : ℝ) / V * v = r * v / V by ring]
      rw [integral_generalTruncatedSource_mul_dilate hV w S b hr, hw_eq, abs_mul, abs_mul,
        abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hs.le),
        abs_of_pos (by positivity : 0 < 1 / Real.sqrt r)]
      have hpow : (r : ℝ) ^ ((1 : ℝ) + 1 / 2) = Real.sqrt r * Real.sqrt r * Real.sqrt r := by
        rw [Real.rpow_add hr0, Real.rpow_one, ← Real.sqrt_eq_rpow, Real.mul_self_sqrt hr0.le]
      rw [hpow]
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := r)
      calc (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r * |_|)
          ≤ (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r *
            (C_w ^ 2 * (4 / Real.pi ^ 4 *
              (dyadicDilationConstant criticalCollarMass criticalTruncatedCurvature / Real.sqrt r) *
                ∑ n ∈ S, b n ^ 2))) := by gcongr
        _ = C * ((ArithmeticFunction.vonMangoldt r : ℝ) / (Real.sqrt r * Real.sqrt r * Real.sqrt r)) := by
            dsimp [C]; field_simp
    · simp
  have habs : Summable fun r => ‖generalTruncatedPrimeAtom w V S b r‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun r => by rw [Real.norm_eq_abs]; exact hbd r) (hsum.mul_left C)
  unfold generalTruncatedPrimeEnergy
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm habs).trans ?_
  refine (habs.tsum_le_tsum (fun r => by rw [Real.norm_eq_abs]; exact hbd r)
    (hsum.mul_left C)).trans (le_of_eq ?_)
  rw [tsum_mul_left]
  unfold criticalTruncatedPrimeConstant
  dsimp [C]; ring

end GaloisForLFunctions.ArithmeticPositivityTheory
