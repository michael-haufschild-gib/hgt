import GaloisForLFunctions.«arithmetic-positivity-theory».GeneralDivisorBernoulliFilterClassification
import GaloisForLFunctions.«arithmetic-positivity-theory».CompactCriticalSourceWeilPositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeKernelNegativeDefinite
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

/-- Collar-difference phase profile of a general divisor stencil `(D, α)`:
`Φ_{D, α, N}(v) = P_{D, α}(λ_N v) - P_{D, α}(N v)`. At `(D, α) = ({1, 2, 4}, canonicalDyadicStencil)`,
this coincides with `factorialPhaseProfile N v`. -/
def divisorBernoulliPhaseProfile (D : Finset ℕ) (α : ℕ → ℝ) (N : ℕ) (v : ℝ) : ℝ :=
  divisorBernoulliFilter D α (factorialShiftedFreq N * v) -
    divisorBernoulliFilter D α ((N : ℝ) * v)

/-- Harmonic weight sequence `w_k = M_{D, α}(k) / (4 k²)` of a general divisor stencil `(D, α)`. -/
def divisorHarmonicWeight (D : Finset ℕ) (α : ℕ → ℝ) (k : ℕ) : ℝ :=
  divisorHarmonicMultiplier D α k / (4 * (k : ℝ) ^ 2)

@[simp]
theorem divisorHarmonicWeight_zero (D : Finset ℕ) (α : ℕ → ℝ) :
    divisorHarmonicWeight D α 0 = 0 := by
  simp [divisorHarmonicWeight]

theorem divisorHarmonicWeight_one {D : Finset ℕ} (_h0 : 0 ∉ D) (α : ℕ → ℝ) :
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
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_pow, Nat.abs_cast, div_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun d _ => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ D) fun d _ _ => by positivity)
  rw [abs_mul, abs_pow, Nat.abs_cast]

/-- **Bernoulli cosine expansion of a general divisor-stencil filter.** For any finite divisor set
`D` with `0 ∉ D` and any stencil `α : ℕ → ℝ`,
`∑_{k ≥ 1} divisorHarmonicWeight D α k * cos(2π k u) = -(π² / 2) * divisorCenteredBernoulliFilter D α u`. -/
theorem divisorCenteredBernoulliFilter_hasSum {D : Finset ℕ} (h0 : 0 ∉ D) (α : ℕ → ℝ) (u : ℝ) :
    HasSum (fun k : ℕ => divisorHarmonicWeight D α k * Real.cos (2 * Real.pi * k * u))
      (-(Real.pi ^ 2 / 2) * divisorCenteredBernoulliFilter D α u) := by
  have hd (d : ℕ) (hdD : d ∈ D) :
      HasSum (fun k : ℕ => (α d / 4) *
        (if d ∣ k then (d : ℝ) ^ 2 * Real.cos (2 * Real.pi * k * u) / (k : ℝ) ^ 2 else 0))
        ((α d / 4) * (2 * Real.pi ^ 2 * (1 / 12 - periodicClampedKernel ((d : ℝ) * u)))) := by
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr fun h => h0 (h ▸ hdD)
    exact (periodicClampedKernel_mul_hasSum_cos hd1 u).mul_left (α d / 4)
  have hsum := hasSum_sum (s := D) hd
  refine hasSum_of_eq_of_eq hsum (fun k => ?_) ?_
  · unfold divisorHarmonicWeight divisorHarmonicMultiplier
    rw [Finset.sum_filter, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> ring
  · unfold divisorCenteredBernoulliFilter periodicCenteredClampedKernel
    rw [Finset.mul_sum]
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
  have hlayer (k : ℕ) : (w k : ℂ) * factorialHarmonicLayer S (fun n => (b n : ℂ)) k v =
      ((w k * realHarmonicLayer S b k v : ℝ) : ℂ) := by
    unfold factorialHarmonicLayer realHarmonicLayer
    push_cast
    ring
  simp_rw [hlayer]
  rw [← Complex.ofReal_tsum]
  push_cast
  ring

theorem generalPhaseCombination_dyadic_eq (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    generalPhaseCombination dyadicHarmonicWeight S b v = realPhaseCombination S b v := by
  unfold generalPhaseCombination
  rw [(realPhaseCombination_hasSum S b v).tsum_eq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

theorem generalPhaseCombination_hasSum {w : ℕ → ℝ} (hw : Summable fun k => |w k|)
    (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    HasSum (fun k => w k * realHarmonicLayer S b k v)
      (-(Real.pi ^ 2 / 2) * generalPhaseCombination w S b v) := by
  have hs : Summable fun k => w k * realHarmonicLayer S b k v := by
    refine Summable.of_norm_bounded (hw.mul_right (2 * ∑ n ∈ S, |b n|)) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_realHarmonicLayer_le S b k v) (abs_nonneg _)
  have h := hs.hasSum
  have heq : -(Real.pi ^ 2 / 2) * generalPhaseCombination w S b v =
      ∑' k, w k * realHarmonicLayer S b k v := by
    unfold generalPhaseCombination
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  exact heq ▸ h

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
      push_cast; field_simp
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
  rw [← mul_sub, abs_mul, Nat.abs_cast] at hd
  calc |α d| * |periodicClampedKernel ((d : ℝ) * u) - periodicClampedKernel ((d : ℝ) * u')|
      ≤ |α d| * ((d : ℝ) * |u - u'| / 2) := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    _ = |α d| * (d : ℝ) / 2 * |u - u'| := by ring

/-- Global Lipschitz constant of a divisor-stencil phase combination `∑_{n ∈ S} b_n Φ_{D, α, n+1}`. -/
def divisorPhaseLipschitz (D : Finset ℕ) (α : ℕ → ℝ) (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, |b n| * (((∑ d ∈ D, |α d| * (d : ℝ)) / 2) *
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
  rw [← mul_sub, abs_mul, Nat.abs_cast] at h2
  have he : (divisorBernoulliFilter D α (factorialShiftedFreq (n + 1) * v) -
        divisorBernoulliFilter D α (((n + 1 : ℕ) : ℝ) * v)) -
      (divisorBernoulliFilter D α (factorialShiftedFreq (n + 1) * v') -
        divisorBernoulliFilter D α (((n + 1 : ℕ) : ℝ) * v')) =
      (divisorBernoulliFilter D α (factorialShiftedFreq (n + 1) * v) -
          divisorBernoulliFilter D α (factorialShiftedFreq (n + 1) * v')) -
        (divisorBernoulliFilter D α (((n + 1 : ℕ) : ℝ) * v) -
          divisorBernoulliFilter D α (((n + 1 : ℕ) : ℝ) * v')) := by ring
  rw [he]
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
    have hpos1 : 0 ≤ 2 * Real.pi * (k : ℝ) * factorialShiftedFreq (n + 1) := by positivity
    have hpos2 : 0 ≤ 2 * Real.pi * (k : ℝ) * ((n + 1 : ℕ) : ℝ) := by positivity
    rw [he1, abs_mul, abs_of_nonneg hpos1] at hc1
    rw [he2, abs_mul, abs_of_nonneg hpos2] at hc2
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
  calc 2 / Real.pi ^ 2 * ‖∑' k : ℕ, (w k * realHarmonicLayer S b k v - w k * realHarmonicLayer S b k v')‖
      ≤ 2 / Real.pi ^ 2 * ((∑' k : ℕ, (k : ℝ) * |w k|) * (2 * Real.pi * L1 * |v - v'|)) :=
        mul_le_mul_of_nonneg_left htsum (by positivity)
    _ = ((4 / Real.pi) * (∑' k : ℕ, (k : ℝ) * |w k|) * L1) * |v - v'| := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp

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
  simp [h2]
  ring

theorem qAdicSignFlipChi_sq_mul (q m : ℕ) : qAdicSignFlipChi q (q ^ 2 * m) = 0 := by
  unfold qAdicSignFlipChi
  have h1 : q ∣ q ^ 2 * m := ⟨q * m, by ring⟩
  have h2 : q ^ 2 ∣ q ^ 2 * m := dvd_mul_right (q ^ 2) m
  simp [h1, h2]
  ring

theorem abs_qAdicSignFlipChi_le_one {q : ℕ} (_hq : 2 ≤ q) (k : ℕ) :
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
  have hmul : divisorHarmonicMultiplier ({1, q, q ^ 2} : Finset ℕ) (qAdicSignFlipStencil q) k =
      4 * qAdicSignFlipChi q k := by
    unfold divisorHarmonicMultiplier qAdicSignFlipStencil qAdicSignFlipChi
    have hq_lt_sq : q < q ^ 2 := by nlinarith
    have h1_mem : (1 : ℕ) ∉ ({q, q ^ 2} : Finset ℕ) := by simp; omega
    have hq_mem : q ∉ ({q ^ 2} : Finset ℕ) := by simp; omega
    have hq_ne1 : q ≠ 1 := by omega
    have hq2_ne1 : q ^ 2 ≠ 1 := by omega
    have hq2_neq : q ^ 2 ≠ q := by omega
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hq2_ne0 : (q : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq_pos.ne'
    have hq4_ne0 : (q : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 hq_pos.ne'
    rw [Finset.sum_filter, Finset.sum_insert h1_mem, Finset.sum_insert hq_mem, Finset.sum_singleton]
    simp only [one_dvd, if_true, Nat.cast_one, one_pow, mul_one, hq_ne1, hq2_ne1, hq2_neq, if_false,
      Nat.cast_pow]
    split_ifs <;> field_simp [hq2_ne0, hq4_ne0] <;> ring
  unfold divisorHarmonicWeight qAdicSignFlipWeight
  rw [hmul]
  ring

private theorem tsum_one_div_nat_sq_le_two :
    (∑' k : ℕ, 1 / (k : ℝ) ^ 2) ≤ 2 := by
  rw [hasSum_zeta_two.tsum_eq]
  have hpi : Real.pi < 63 / 20 := by linarith [Real.pi_lt_d2]
  have := Real.pi_pos
  nlinarith

private theorem tsum_inv_sq_add_two_le :
    (∑' k : ℕ, 1 / ((k + 2 : ℕ) : ℝ) ^ 2) ≤ 3 / 4 := by
  have hsum := hasSum_zeta_two
  have hs := hsum.summable
  have htot := hsum.tsum_eq
  rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add] at htot
  simp only [Nat.cast_zero, sq (0 : ℝ), mul_zero, div_zero, zero_add,
    Nat.cast_one, one_pow, div_one, show ∀ k : ℕ, k + 1 + 1 = k + 2 from fun _ => rfl] at htot
  have hpi : Real.pi < 63 / 20 := by linarith [Real.pi_lt_d2]
  have hpi2 : Real.pi ^ 2 / 6 ≤ (63 / 20 : ℝ) ^ 2 / 6 := by
    have := Real.pi_pos; nlinarith
  linarith

/-- Every `q`-adic 3-scale sign-flip stencil (`q ≥ 2`) satisfies
`AdmissibleHarmonicWeight (qAdicSignFlipWeight q) 1 (3 / 4)`. -/
theorem admissibleHarmonicWeight_qAdicSignFlip {q : ℕ} (hq : 2 ≤ q) :
    AdmissibleHarmonicWeight (qAdicSignFlipWeight q) 1 (3 / 4) where
  w_zero := by simp [qAdicSignFlipWeight]
  w_one := by simp [qAdicSignFlipWeight, qAdicSignFlipChi_one hq]
  C_pos := one_pos
  abs_w_le := fun k => by
    unfold qAdicSignFlipWeight
    rw [abs_div, abs_pow, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (abs_qAdicSignFlipChi_le_one hq k) (sq_nonneg _)
  τ_nonneg := by norm_num
  τ_lt_one := by norm_num
  tsum_tail_le := by
    have hbd (k : ℕ) : |qAdicSignFlipWeight q (k + 2)| ≤ 1 / ((k + 2 : ℕ) : ℝ) ^ 2 := by
      unfold qAdicSignFlipWeight
      rw [abs_div, abs_pow, Nat.abs_cast]
      exact div_le_div_of_nonneg_right (abs_qAdicSignFlipChi_le_one hq (k + 2)) (sq_nonneg _)
    have hs2 : Summable fun k : ℕ => 1 / ((k + 2 : ℕ) : ℝ) ^ 2 :=
      (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    have hs : Summable fun k : ℕ => |qAdicSignFlipWeight q (k + 2)| :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hbd hs2
    exact (hs.tsum_le_tsum hbd hs2).trans tsum_inv_sq_add_two_le

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
  exact ⟨trivial, by ring, by ring⟩

theorem divisorHarmonicWeight_qAdicDriftFree_eq {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    divisorHarmonicWeight ({1, q, q ^ 2} : Finset ℕ) (qAdicDriftFreeStencil q) k =
      qAdicDriftFreeWeight q k := by
  have hmul : divisorHarmonicMultiplier ({1, q, q ^ 2} : Finset ℕ) (qAdicDriftFreeStencil q) k =
      4 * qAdicDriftFreeChi q k := by
    unfold divisorHarmonicMultiplier qAdicDriftFreeStencil qAdicDriftFreeChi
    have hq_lt_sq : q < q ^ 2 := by nlinarith
    have h1_mem : (1 : ℕ) ∉ ({q, q ^ 2} : Finset ℕ) := by simp; omega
    have hq_mem : q ∉ ({q ^ 2} : Finset ℕ) := by simp; omega
    have hq_ne1 : q ≠ 1 := by omega
    have hq2_ne1 : q ^ 2 ≠ 1 := by omega
    have hq2_neq : q ^ 2 ≠ q := by omega
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hq2_ne0 : (q : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq_pos.ne'
    have hq3_ne0 : (q : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hq_pos.ne'
    rw [Finset.sum_filter, Finset.sum_insert h1_mem, Finset.sum_insert hq_mem, Finset.sum_singleton]
    simp only [one_dvd, if_true, Nat.cast_one, one_pow, mul_one, hq_ne1, hq2_ne1, hq2_neq, if_false,
      Nat.cast_pow]
    split_ifs <;> field_simp [hq2_ne0, hq3_ne0] <;> ring
  unfold divisorHarmonicWeight qAdicDriftFreeWeight
  rw [hmul]
  ring

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
  simp [h2]

/-- Exact indicator decomposition of `|qAdicDriftFreeChi q k|` for every `q ≥ 2` and `k : ℕ`:
`|χ_{q, df}(k)| = 1 + (q - 1)[q ∣ k] - q[q² ∣ k]`. -/
theorem abs_qAdicDriftFreeChi_eq {q : ℕ} (_hq : 2 ≤ q) (k : ℕ) :
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
    · simp [h1, h2]
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
    rw [abs_div, abs_pow, Nat.abs_cast, abs_qAdicDriftFreeChi_eq hq k]
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
    rw [abs_div, abs_pow, Nat.abs_cast]
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
      have hq3_ne : (q : ℝ) ^ 3 ≠ 0 := hq3_pos.ne'
      have hid : 32 / 27 - (1 + ((q : ℝ) ^ 2 - (q : ℝ) - 1) / (q : ℝ) ^ 3) =
          ((q : ℝ) - 3) ^ 2 * (5 * (q : ℝ) + 3) / (27 * (q : ℝ) ^ 3) := by
        field_simp [hq3_ne]
        ring
      linarith [div_nonneg hsos (by positivity : (0 : ℝ) ≤ 27 * (q : ℝ) ^ 3)]
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
      rw [abs_div, abs_pow, Nat.abs_cast]
      calc |c k| / (k : ℝ) ^ p ≤ 1 / (k : ℝ) ^ p :=
            div_le_div_of_nonneg_right (hcb k) (by positivity)
        _ ≤ 1 / (k : ℝ) ^ 2 := one_div_le_one_div_of_le (by positivity) hpow
  τ_nonneg := by norm_num
  τ_lt_one := by norm_num
  tsum_tail_le := by
    have hle_dyadic (k : ℕ) : |higherOrderHarmonicWeight p c (k + 2)| ≤
        1 / ((k + 2 : ℕ) : ℝ) ^ 2 := by
      unfold higherOrderHarmonicWeight
      rw [if_neg (by omega), abs_div, abs_pow, Nat.abs_cast]
      have hk1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by positivity
      have hpow : ((k + 2 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ) ^ p := pow_le_pow_right₀ hk1 hp
      exact (div_le_div_of_nonneg_right (hcb (k + 2)) (by positivity)).trans
        (one_div_le_one_div_of_le (by positivity) hpow)
    have hs2 : Summable fun k : ℕ => 1 / ((k + 2 : ℕ) : ℝ) ^ 2 :=
      (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    have hs : Summable fun k : ℕ => |higherOrderHarmonicWeight p c (k + 2)| :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle_dyadic hs2
    exact (hs.tsum_le_tsum hle_dyadic hs2).trans tsum_inv_sq_add_two_le

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
    rw [abs_div, abs_pow, Nat.abs_cast]
    have hpow : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ p := pow_le_pow_right₀ hk1 hp
    calc (k : ℝ) * (|c k| / (k : ℝ) ^ p)
        ≤ (k : ℝ) * (1 / (k : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hcb k) (by positivity)) hk0.le
      _ ≤ (k : ℝ) * (1 / (k : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) hpow) hk0.le
      _ = 1 / (k : ℝ) ^ 2 := by field_simp

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
    have h1 : IntegrableOn (fun v => (4 / Real.pi ^ 4) *
        ‖-((Real.pi ^ 2 / 2 : ℝ) : ℂ) * generalComplexPhaseCombination w S b (r * v)‖ ^ 2)
        (Ioc a (a + ℓ)) := hint.const_mul (4 / Real.pi ^ 4)
    refine h1.congr_fun (fun v _ => ?_) measurableSet_Ioc
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
          field_simp
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
  have hB_eq (v : ℝ) :
      ‖generalComplexPhaseCombination w S (fun n => (b n : ℂ)) v‖ ^ 2 = B v ^ 2 := by
    dsimp only [B]
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
  have hDom : IntegrableOn
      (fun v => v ^ (-2 : ℝ) * ‖generalComplexPhaseCombination w S (fun n => (b n : ℂ)) v‖ ^ 2)
      (Ioi 1) := by
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
        have h1 : IntegrableOn (fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * y)) (Ici 0) :=
          integrableOn_Ici_iff_integrableOn_Ioi.mpr (integrableOn_exp_mul_Ioi (by norm_num) 0)
        have h2 : IntegrableOn (fun y : ℝ => C0 * Real.exp (-(1 / 2 : ℝ) * -y)) (Iic 0) := by
          simpa using (h1.comp_neg).const_mul C0
        exact h2.congr_fun (fun y _ => by congr 1; congr 1; ring) measurableSet_Iic
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
      refine (memLp_two_iff_integrable_sq_norm
        (Complex.continuous_ofReal.comp hcont).aestronglyMeasurable).mpr ?_
      have hexp2 : IntegrableOn (fun y : ℝ => C0 ^ 2 * Real.exp y) (Iic 0) := by
        have h1 : IntegrableOn (fun y : ℝ => Real.exp ((-1 : ℝ) * y)) (Ici 0) :=
          integrableOn_Ici_iff_integrableOn_Ioi.mpr (integrableOn_exp_mul_Ioi (by norm_num) 0)
        have h2 : IntegrableOn (fun y : ℝ => C0 ^ 2 * Real.exp ((-1 : ℝ) * -y)) (Iic 0) := by
          simpa using (h1.comp_neg).const_mul (C0 ^ 2)
        exact h2.congr_fun (fun y _ => by congr 1; congr 1; ring) measurableSet_Iic
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
    have hDomB : IntegrableOn (fun v => v ^ (-2 : ℝ) * B v ^ 2) (Ioi 1) := by
      simpa only [hB_eq] using hDom
    refine (setIntegral_mono_on hInt_Ioi hDomB measurableSet_Ioi fun v hv => ?_).trans h1
    have hv0 : 0 < v := lt_trans zero_lt_one hv
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
      · dsimp only [B, bc]
        rw [generalComplexPhaseCombination_ofReal]
        simp only [generalCollaredSource, indicator_of_mem (show y ∈ Iic 0 from hy)]
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
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [fk, hw.w_zero]
    · exact ((norm_integral_factorialHarmonicLayer_criticalCollarMellinKernel_le S bc hk ht).1.const_mul
        (w k : ℂ)).const_mul (-((2 / Real.pi ^ 2 : ℝ) : ℂ))
  have hfk_norm (k : ℕ) : (∫ v in Ioi 1, ‖fk k v‖) ≤
      (2 / Real.pi ^ 2 * |w k|) * (Cb * ∫ v in Ioi (1 : ℝ), v ^ (-3 / 2 : ℝ)) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_on (hfk_int k).norm ((hker_int.const_mul Cb).const_mul _)
      measurableSet_Ioi fun v hv => ?_
    have hv0 : 0 < v := lt_trans zero_lt_one hv
    simp only [fk, Real.norm_eq_abs, norm_mul, norm_neg, Complex.norm_real,
      abs_of_pos (by positivity : 0 < 2 / Real.pi ^ 2)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
      (by positivity : (0 : ℝ) ≤ 2 / Real.pi ^ 2)
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
              exact div_le_div_of_nonneg_left hC (by positivity)
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk1 Real.pi_pos.le)
                  (by positivity))
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

/-! ### Smooth Harmonic Sine Primitive and Polar Channel Bounds -/

/-- Exact trigonometric primitive of `realHarmonicLayer S b k`:
for `k ≥ 1`,
`G_k(v) = ∑_{n ∈ S} b_n (sin(2π k λ_{n+1} v) / (2π k λ_{n+1}) - sin(2π k (n+1) v) / (2π k (n+1)))`. -/
def realHarmonicLayerPrimitive (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) (v : ℝ) : ℝ :=
  if k = 0 then 0 else
    ∑ n ∈ S, b n *
      (Real.sin (2 * Real.pi * (k : ℝ) * (factorialShiftedFreq (n + 1) * v)) /
          (2 * Real.pi * (k : ℝ) * factorialShiftedFreq (n + 1)) -
        Real.sin (2 * Real.pi * (k : ℝ) * (((n + 1 : ℕ) : ℝ) * v)) /
          (2 * Real.pi * (k : ℝ) * ((n + 1 : ℕ) : ℝ)))

theorem hasDerivAt_realHarmonicLayerPrimitive (S : Finset ℕ) (b : ℕ → ℝ) {k : ℕ}
    (hk : 1 ≤ k) (v : ℝ) :
    HasDerivAt (realHarmonicLayerPrimitive S b k) (realHarmonicLayer S b k v) v := by
  have hk0 : k ≠ 0 := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  have heq : realHarmonicLayerPrimitive S b k = fun u =>
      ∑ n ∈ S, b n *
        (Real.sin (2 * Real.pi * (k : ℝ) * (factorialShiftedFreq (n + 1) * u)) /
            (2 * Real.pi * (k : ℝ) * factorialShiftedFreq (n + 1)) -
          Real.sin (2 * Real.pi * (k : ℝ) * (((n + 1 : ℕ) : ℝ) * u)) /
            (2 * Real.pi * (k : ℝ) * ((n + 1 : ℕ) : ℝ))) := by
    funext u; simp [realHarmonicLayerPrimitive, hk0]
  rw [heq]
  unfold realHarmonicLayer
  refine HasDerivAt.sum fun n _ => ?_
  set ω1 := 2 * Real.pi * (k : ℝ) * factorialShiftedFreq (n + 1)
  set ω2 := 2 * Real.pi * (k : ℝ) * ((n + 1 : ℕ) : ℝ)
  have hlam : ((n + 1 : ℕ) : ℝ) ≤ factorialShiftedFreq (n + 1) := by
    have := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).1
    linarith
  have hω1 : ω1 ≠ 0 := mul_ne_zero (mul_ne_zero hpi hkR) (by linarith [show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity])
  have hω2 : ω2 ≠ 0 := mul_ne_zero (mul_ne_zero hpi hkR) (by positivity)
  have hd1 : HasDerivAt (fun u => Real.sin (2 * Real.pi * (k : ℝ) * (factorialShiftedFreq (n + 1) * u)) / ω1)
      (Real.cos (2 * Real.pi * (k : ℝ) * (factorialShiftedFreq (n + 1) * v))) v := by
    have hin : HasDerivAt (fun u => 2 * Real.pi * (k : ℝ) * (factorialShiftedFreq (n + 1) * u)) ω1 v := by
      have := (hasDerivAt_id v).const_mul (factorialShiftedFreq (n + 1))
      have := this.const_mul (2 * Real.pi * (k : ℝ))
      exact this.congr_deriv (by dsimp [ω1]; ring)
    exact (hin.sin.div_const ω1).congr_deriv (by field_simp [hω1])
  have hd2 : HasDerivAt (fun u => Real.sin (2 * Real.pi * (k : ℝ) * (((n + 1 : ℕ) : ℝ) * u)) / ω2)
      (Real.cos (2 * Real.pi * (k : ℝ) * (((n + 1 : ℕ) : ℝ) * v))) v := by
    have hin : HasDerivAt (fun u => 2 * Real.pi * (k : ℝ) * (((n + 1 : ℕ) : ℝ) * u)) ω2 v := by
      have := (hasDerivAt_id v).const_mul ((n + 1 : ℕ) : ℝ)
      have := this.const_mul (2 * Real.pi * (k : ℝ))
      exact this.congr_deriv (by dsimp [ω2]; ring)
    exact (hin.sin.div_const ω2).congr_deriv (by field_simp [hω2])
  exact (hd1.sub hd2).const_mul (b n)

theorem abs_realHarmonicLayerPrimitive_le (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) (v : ℝ) :
    |realHarmonicLayerPrimitive S b k v| ≤
      (1 / Real.pi) * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) := by
  unfold realHarmonicLayerPrimitive
  split_ifs with hk
  · rw [abs_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    have hlam : ((n + 1 : ℕ) : ℝ) ≤ factorialShiftedFreq (n + 1) := by
      have := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).1
      linarith
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1 : |Real.sin (2 * Real.pi * (k : ℝ) * (factorialShiftedFreq (n + 1) * v)) /
        (2 * Real.pi * (k : ℝ) * factorialShiftedFreq (n + 1))| ≤
        1 / (2 * Real.pi * ((n + 1 : ℕ) : ℝ)) := by
      rw [abs_div, abs_of_pos (by nlinarith)]
      calc |Real.sin _| / (2 * Real.pi * (k : ℝ) * factorialShiftedFreq (n + 1))
          ≤ 1 / (2 * Real.pi * (k : ℝ) * factorialShiftedFreq (n + 1)) :=
            div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by nlinarith)
        _ ≤ 1 / (2 * Real.pi * ((n + 1 : ℕ) : ℝ)) :=
            one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h2 : |Real.sin (2 * Real.pi * (k : ℝ) * (((n + 1 : ℕ) : ℝ) * v)) /
        (2 * Real.pi * (k : ℝ) * ((n + 1 : ℕ) : ℝ))| ≤
        1 / (2 * Real.pi * ((n + 1 : ℕ) : ℝ)) := by
      rw [abs_div, abs_of_pos (by positivity)]
      calc |Real.sin _| / (2 * Real.pi * (k : ℝ) * ((n + 1 : ℕ) : ℝ))
          ≤ 1 / (2 * Real.pi * (k : ℝ) * ((n + 1 : ℕ) : ℝ)) :=
            div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
        _ ≤ 1 / (2 * Real.pi * ((n + 1 : ℕ) : ℝ)) :=
            one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have hsub : |Real.sin (2 * Real.pi * (k : ℝ) * (factorialShiftedFreq (n + 1) * v)) /
        (2 * Real.pi * (k : ℝ) * factorialShiftedFreq (n + 1)) -
        Real.sin (2 * Real.pi * (k : ℝ) * (((n + 1 : ℕ) : ℝ) * v)) /
        (2 * Real.pi * (k : ℝ) * ((n + 1 : ℕ) : ℝ))| ≤
        1 / (Real.pi * ((n + 1 : ℕ) : ℝ)) := by
      refine (abs_sub _ _).trans ?_
      have : 1 / (2 * Real.pi * ((n + 1 : ℕ) : ℝ)) + 1 / (2 * Real.pi * ((n + 1 : ℕ) : ℝ)) =
          1 / (Real.pi * ((n + 1 : ℕ) : ℝ)) := by ring
      linarith
    calc |b n| * |_| ≤ |b n| * (1 / (Real.pi * ((n + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hsub (abs_nonneg _)
      _ = 1 / Real.pi * (|b n| / ((n + 1 : ℕ) : ℝ)) := by ring

/-- **Integration by parts for `generalPhaseCombination` against a flat weight.**
For any `AdmissibleHarmonicWeight w C_w τ` and any differentiable weight `φ` on `[1, ∞)` with
`φ(1) = 0`, `φ → 0`, and `φ, φ' ∈ L¹(1, ∞)`,
`|∫_{v>1} φ(v) B_{w,b}(v) dv| ≤ (2 (1 + τ) / π³) ‖φ'‖₁ ∑_{n ∈ S} |b_n| / (n + 1)`. -/
theorem abs_integral_weight_mul_generalPhaseCombination_le
    {w : ℕ → ℝ} {C_w τ : ℝ} (hw : AdmissibleHarmonicWeight w C_w τ)
    {φ φ' : ℝ → ℝ} (hd : ∀ v ∈ Ici (1 : ℝ), HasDerivAt φ (φ' v) v)
    (hφ1 : φ 1 = 0) (hφt : Tendsto φ atTop (𝓝 0))
    (hφi : IntegrableOn φ (Ioi 1)) (hφi' : IntegrableOn φ' (Ioi 1))
    (S : Finset ℕ) (b : ℕ → ℝ) :
    |∫ v in Ioi 1, φ v * generalPhaseCombination w S b v| ≤
      (∫ v in Ioi 1, |φ' v|) * ((2 * (1 + τ) / Real.pi ^ 3) * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) := by
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => by positivity
  set B1 := 2 * ∑ n ∈ S, |b n|
  have hB1 : 0 ≤ B1 := by
    have := Finset.sum_nonneg fun n (_ : n ∈ S) => abs_nonneg (b n); positivity
  set fk : ℕ → ℝ → ℝ := fun k v => -(2 / Real.pi ^ 2) * (w k * (φ v * realHarmonicLayer S b k v))
  have hpt (v : ℝ) : φ v * generalPhaseCombination w S b v = ∑' k, fk k v := by
    unfold generalPhaseCombination
    have hs : Summable fun k => w k * realHarmonicLayer S b k v :=
      (generalPhaseCombination_hasSum hw.summable_abs S b v).summable
    rw [← mul_assoc, mul_comm (φ v), mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun k => by simp only [fk]; ring
  have hfk_int (k : ℕ) : Integrable (fk k) (volume.restrict (Ioi 1)) := by
    have hc : Continuous (realHarmonicLayer S b k) := by unfold realHarmonicLayer; fun_prop
    have := hφi.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact abs_realHarmonicLayer_le S b k v)
    exact (this.const_mul (w k)).const_mul (-(2 / Real.pi ^ 2))
  have hfk_norm (k : ℕ) : (∫ v in Ioi 1, ‖fk k v‖) ≤
      (2 / Real.pi ^ 2 * |w k|) * (B1 * ∫ v in Ioi 1, |φ v|) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_on (hfk_int k).norm ((hφi.abs.const_mul B1).const_mul _)
      measurableSet_Ioi fun v _ => ?_
    simp only [fk, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 / Real.pi ^ 2)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) (by positivity)
    rw [mul_comm B1]
    exact mul_le_mul_of_nonneg_left (abs_realHarmonicLayer_le S b k v) (abs_nonneg _)
  have hfk_sum : Summable fun k => ∫ v in Ioi 1, ‖fk k v‖ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hfk_norm
      ((hw.summable_abs.mul_left (2 / Real.pi ^ 2)).mul_right _)
  have hexch : (∫ v in Ioi 1, φ v * generalPhaseCombination w S b v) =
      ∑' k, ∫ v in Ioi 1, fk k v := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun v _ => hpt v]
    exact (integral_tsum_of_summable_integral_norm hfk_int hfk_sum).symm
  set W1 := ∫ v in Ioi 1, |φ' v|
  have hW1 : 0 ≤ W1 := integral_nonneg fun _ => abs_nonneg _
  have hk_bound (k : ℕ) : |∫ v in Ioi 1, fk k v| ≤
      (W1 * (2 / Real.pi ^ 3 * T)) * |w k| := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [fk, hw.w_zero]
    · simp only [fk, integral_const_mul, abs_mul, abs_neg,
        abs_of_pos (by positivity : 0 < 2 / Real.pi ^ 2)]
      set Gk := realHarmonicLayerPrimitive S b k
      set Hk := realHarmonicLayer S b k
      have hGk_deriv (v : ℝ) : HasDerivAt Gk (Hk v) v :=
        hasDerivAt_realHarmonicLayerPrimitive S b hk v
      have hGk_cont' : Continuous Gk :=
        continuous_iff_continuousAt.mpr fun v => (hGk_deriv v).continuousAt
      have hHk_cont : Continuous Hk := by unfold Hk realHarmonicLayer; fun_prop
      have hint1 : IntegrableOn (φ * Hk) (Ioi 1) :=
        hφi.mul_bdd hHk_cont.aestronglyMeasurable (Eventually.of_forall fun v => by
          rw [Real.norm_eq_abs]; exact abs_realHarmonicLayer_le S b k v)
      have hint2 : IntegrableOn (φ' * Gk) (Ioi 1) :=
        hφi'.mul_bdd hGk_cont'.aestronglyMeasurable (Eventually.of_forall fun v => by
          rw [Real.norm_eq_abs]; exact abs_realHarmonicLayerPrimitive_le S b k v)
      have hlim1 : Tendsto (φ * Gk) (𝓝[>] 1) (𝓝 0) := by
        have h := ((hd 1 self_mem_Ici).continuousAt.mul hGk_cont'.continuousAt).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
        have h0 : (φ * Gk) 1 = 0 := by simp [hφ1]
        rwa [h0] at h
      have hlim2 : Tendsto (φ * Gk) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (fun _ => norm_nonneg _) (fun v => ?_)
          (by simpa using hφt.norm.mul_const (1 / Real.pi * T))
        rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs (Gk v)]
        exact mul_le_mul_of_nonneg_left (abs_realHarmonicLayerPrimitive_le S b k v) (norm_nonneg _)
      have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (u := φ) (v := Gk) (u' := φ') (v' := Hk)
        (a' := 0) (b' := 0) (fun x hx => hd x (Ioi_subset_Ici_self hx))
        (fun x _ => hGk_deriv x) hint1 hint2 hlim1 hlim2
      have hibp_bound : |∫ v in Ioi 1, φ v * Hk v| ≤ W1 * (1 / Real.pi * T) := by
        change |∫ v in Ioi 1, (φ * Hk) v| ≤ _
        rw [hibp, sub_self, zero_sub, abs_neg, ← integral_mul_const]
        refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on hint2.abs
          (hφi'.abs.mul_const _) measurableSet_Ioi fun v _ => ?_)
        rw [Pi.mul_apply, abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_realHarmonicLayerPrimitive_le S b k v) (abs_nonneg _)
      calc 2 / Real.pi ^ 2 * (|w k| * |∫ v in Ioi 1, φ v * Hk v|)
          ≤ 2 / Real.pi ^ 2 * (|w k| * (W1 * (1 / Real.pi * T))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hibp_bound (abs_nonneg _)) (by positivity)
        _ = (W1 * (2 / Real.pi ^ 3 * T)) * |w k| := by ring
  have hs_int : Summable fun k => ‖∫ v in Ioi 1, fk k v‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by rw [Real.norm_eq_abs]; exact hk_bound k) (hw.summable_abs.mul_left _)
  rw [hexch, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hs_int).trans ?_
  have htsum := (hs_int.tsum_le_tsum (fun k => by rw [Real.norm_eq_abs]; exact hk_bound k)
    (hw.summable_abs.mul_left _)).trans_eq tsum_mul_left
  refine htsum.trans ?_
  calc (W1 * (2 / Real.pi ^ 3 * T)) * (∑' k, |w k|)
      ≤ (W1 * (2 / Real.pi ^ 3 * T)) * (1 + τ) :=
        mul_le_mul_of_nonneg_left hw.tsum_abs_le (by positivity)
    _ = W1 * ((2 * (1 + τ) / Real.pi ^ 3) * T) := by ring

/-- Upper polar readout `∫ g_w^V(x) e^{x/2} dx` of `generalTruncatedSource`. -/
def generalTruncatedPolarReadout (w : ℕ → ℝ) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∫ x, generalTruncatedSource w V S b x * Real.exp (x / 2)

/-- Lower polar readout `∫ g_w^V(x) e^{-x/2} dx` of `generalTruncatedSource`. -/
def generalTruncatedPolarEndpoint (w : ℕ → ℝ) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∫ x, generalTruncatedSource w V S b x * Real.exp (-(x / 2))

theorem abs_generalTruncatedPolarReadout_le {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    |generalTruncatedPolarReadout w V S b| ≤
      criticalTruncatedReadoutConstant *
        ((2 * (1 + τ) / Real.pi ^ 3) * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) := by
  have hl : 0 ≤ 1 / V := by positivity
  set F := generalPhaseCombination w S b
  have hrep : generalTruncatedPolarReadout w V S b =
      ∫ v in Ioi 1, criticalTruncatedWeight (1 / V) v * F v := by
    have hpt : ∀ x, generalTruncatedSource w V S b x * Real.exp (x / 2) =
        (Iic (0 : ℝ)).indicator (fun x => Real.exp x * (Real.smoothTransition (Real.exp (-x) - 1) *
          criticalUpperCutoff (Real.exp (-x) / V) * F (Real.exp (-x)))) x := by
      intro x
      by_cases hx : x ≤ 0
      · rw [indicator_of_mem (show x ∈ Iic 0 from hx), generalTruncatedSource, generalCollaredSource,
          indicator_of_mem (show x ∈ Iic 0 from hx)]
        have : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by rw [← Real.exp_add]; ring_nf
        rw [← this]; ring
      · rw [indicator_of_notMem (show x ∉ Iic 0 from hx), generalTruncatedSource, generalCollaredSource,
          indicator_of_notMem (show x ∉ Iic 0 from hx)]
        ring
    unfold generalTruncatedPolarReadout
    rw [funext hpt, integral_indicator measurableSet_Iic,
      integral_Iic_zero_exp_mul_comp_exp_neg (fun v => Real.smoothTransition (v - 1) *
        criticalUpperCutoff (v / V) * F v)]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [criticalTruncatedWeight, criticalCollarWeight, F]
    rw [show 1 / V * v = v / V by ring]; ring
  rw [hrep]
  have ht : Tendsto (criticalTruncatedWeight (1 / V)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (g := fun v => |criticalCollarWeight v|) (fun _ => norm_nonneg _)
      (fun v => by rw [Real.norm_eq_abs]; exact abs_criticalTruncatedWeight_le _ v)
      (by simpa using tendsto_criticalCollarWeight_atTop.abs)
  have h := abs_integral_weight_mul_generalPhaseCombination_le hw
    (w := w) (φ := criticalTruncatedWeight (1 / V)) (φ' := criticalTruncatedWeightDeriv (1 / V))
    (fun v _ => hasDerivAt_criticalTruncatedWeight _ v)
    (by rw [criticalTruncatedWeight, criticalCollarWeight_eq_zero le_rfl, zero_mul]) ht
    (integrableOn_criticalTruncatedWeight _) (integrableOn_criticalTruncatedWeightDeriv hl) S b
  have hτ0 := hw.τ_nonneg
  have hT0 : 0 ≤ (2 * (1 + τ) / Real.pi ^ 3) * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) := by
    have := Finset.sum_nonneg fun n (_ : n ∈ S) => div_nonneg (abs_nonneg (b n)) (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    positivity
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hT0)
  unfold criticalTruncatedReadoutConstant criticalCollarMass
  calc (∫ v in Ioi 1, |criticalTruncatedWeightDeriv (1 / V) v|) ≤
        ∫ v in Ioi 1, (|deriv criticalCollarWeight v| +
          2 * smoothTransitionSlope * |criticalCollarWeight v|) :=
        setIntegral_mono_on (integrableOn_criticalTruncatedWeightDeriv hl).abs
          (integrableOn_deriv_criticalCollarWeight.abs.add
            (integrableOn_criticalCollarWeight.abs.const_mul _)) measurableSet_Ioi
          fun v hv => abs_criticalTruncatedWeightDeriv_le hl (le_of_lt hv)
    _ = _ := by
        rw [integral_add integrableOn_deriv_criticalCollarWeight.abs
          (integrableOn_criticalCollarWeight.abs.const_mul _), integral_const_mul]

theorem abs_generalTruncatedPolarEndpoint_le {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) {V : ℝ} (hV : 1 ≤ V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    |generalTruncatedPolarEndpoint w V S b| ≤
      criticalTruncatedEndpointConstant *
        ((2 * (1 + τ) / Real.pi ^ 3) * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) := by
  have hV0 : 0 < V := by linarith
  have hl : 0 ≤ 1 / V := by positivity
  set F := generalPhaseCombination w S b
  have hrep : generalTruncatedPolarEndpoint w V S b =
      ∫ v in Ioi 1, criticalTruncatedEndpointWeight V v * F v := by
    have hpt : ∀ x, generalTruncatedSource w V S b x * Real.exp (-(x / 2)) =
        (Iic (0 : ℝ)).indicator (fun x => Real.smoothTransition (Real.exp (-x) - 1) *
          criticalUpperCutoff (Real.exp (-x) / V) * F (Real.exp (-x))) x := by
      intro x
      by_cases hx : x ≤ 0
      · rw [indicator_of_mem (show x ∈ Iic 0 from hx), generalTruncatedSource, generalCollaredSource,
          indicator_of_mem (show x ∈ Iic 0 from hx)]
        have : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by rw [← Real.exp_add]; simp
        calc _ = criticalUpperCutoff (Real.exp (-x) / V) * Real.smoothTransition (Real.exp (-x) - 1) *
              F (Real.exp (-x)) * (Real.exp (x / 2) * Real.exp (-(x / 2))) := by ring
          _ = _ := by rw [this]; ring
      · rw [indicator_of_notMem (show x ∉ Iic 0 from hx), generalTruncatedSource, generalCollaredSource,
          indicator_of_notMem (show x ∉ Iic 0 from hx)]
        ring
    unfold generalTruncatedPolarEndpoint
    rw [funext hpt, integral_indicator measurableSet_Iic,
      integral_Iic_zero_comp_exp_neg (fun v => Real.smoothTransition (v - 1) *
        criticalUpperCutoff (v / V) * F v)]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [criticalTruncatedEndpointWeight, criticalCollarEndpointWeight, F]
    rw [show 1 / V * v = v / V by ring]; ring
  rw [hrep]
  have hc : Continuous (criticalTruncatedEndpointWeight V) :=
    contDiff_criticalCollarEndpointWeight.continuous.mul
      (continuous_criticalUpperCutoff.comp (continuous_const.mul continuous_id))
  have hc' : Continuous (criticalTruncatedEndpointWeightDeriv V) := by
    unfold criticalTruncatedEndpointWeightDeriv
    exact ((contDiff_infty_iff_deriv.mp contDiff_criticalCollarEndpointWeight).2.continuous.mul
      (continuous_criticalUpperCutoff.comp (continuous_const.mul continuous_id))).add
      (contDiff_criticalCollarEndpointWeight.continuous.mul (continuous_const.mul
        ((contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2.continuous.comp
          ((continuous_const.mul continuous_id).sub continuous_const))).neg)
  have hzero {v : ℝ} (hv : 2 * V ≤ v) : criticalTruncatedEndpointWeight V v = 0 := by
    rw [criticalTruncatedEndpointWeight, criticalUpperCutoff_eq_zero, mul_zero]
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hV0]; linarith
  have hw2 : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hbd' : ∀ v ∈ Ioi (1 : ℝ), |criticalTruncatedEndpointWeightDeriv V v| ≤
      |deriv criticalCollarEndpointWeight v| + 2 * smoothTransitionSlope * v ^ (-2 : ℝ) := by
    intro v hv
    have hv0 : 0 < v := lt_trans one_pos hv
    unfold criticalTruncatedEndpointWeightDeriv
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (by rw [abs_of_nonneg (criticalUpperCutoff_nonneg _)]; exact criticalUpperCutoff_le_one _)
    · rw [abs_mul, abs_neg]
      have h1 : |criticalCollarEndpointWeight v| ≤ 1 / v := by
        rw [criticalCollarEndpointWeight, abs_div, abs_of_pos hv0,
          abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact div_le_div_of_nonneg_right (Real.smoothTransition.le_one _) hv0.le
      have h2 := abs_mul_deriv_smoothTransition_le_div hl hv0
      calc |criticalCollarEndpointWeight v| * |1 / V * deriv Real.smoothTransition (1 / V * v - 1)| ≤
            1 / v * (2 * smoothTransitionSlope / v) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = 2 * smoothTransitionSlope * v ^ (-2 : ℝ) := by
            rw [Real.rpow_neg hv0.le, Real.rpow_two]; field_simp
  have hi' : IntegrableOn (criticalTruncatedEndpointWeightDeriv V) (Ioi 1) := by
    refine (integrableOn_deriv_criticalCollarEndpointWeight.abs.add
      (hw2.const_mul (2 * smoothTransitionSlope))).mono' hc'.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs]; exact hbd' v hv
  have hi : IntegrableOn (criticalTruncatedEndpointWeight V) (Ioi 1) := by
    refine (hw2.const_mul (2 * V)).mono' hc.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans one_pos hv
    rw [Real.norm_eq_abs, Real.rpow_neg hv0.le, Real.rpow_two]
    rcases le_or_gt (2 * V) v with h | h
    · rw [hzero h, abs_zero]; positivity
    · rw [criticalTruncatedEndpointWeight, abs_mul]
      have h1 : |criticalCollarEndpointWeight v| ≤ 1 / v := by
        rw [criticalCollarEndpointWeight, abs_div, abs_of_pos hv0,
          abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact div_le_div_of_nonneg_right (Real.smoothTransition.le_one _) hv0.le
      have h2 : |criticalUpperCutoff (1 / V * v)| ≤ 1 := by
        rw [abs_of_nonneg (criticalUpperCutoff_nonneg _)]; exact criticalUpperCutoff_le_one _
      calc |criticalCollarEndpointWeight v| * |criticalUpperCutoff (1 / V * v)| ≤ 1 / v * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ 2 * V * (v ^ 2)⁻¹ := by
            rw [mul_one, one_div, show (v ^ 2)⁻¹ = v⁻¹ * v⁻¹ by rw [sq, mul_inv]]
            have : 1 ≤ 2 * V * v⁻¹ := by rw [← div_eq_mul_inv, le_div_iff₀ hv0]; linarith
            nlinarith [inv_pos.mpr hv0]
  have hd : ∀ v ∈ Ici (1 : ℝ), HasDerivAt (criticalTruncatedEndpointWeight V)
      (criticalTruncatedEndpointWeightDeriv V v) v := fun v _ => by
    have hσ : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition (1 / V * v - 1)) (1 / V * v - 1) :=
      ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp) _).hasDerivAt
    have hin : HasDerivAt (fun u => 1 / V * u - 1) (1 / V) v := by
      simpa using ((hasDerivAt_id v).const_mul (1 / V)).sub_const 1
    have hcut : HasDerivAt (fun u => criticalUpperCutoff (1 / V * u))
        (-(1 / V * deriv Real.smoothTransition (1 / V * v - 1))) v :=
      ((hσ.comp v hin).const_sub 1).congr_deriv (by ring)
    exact ((hasDerivAt_criticalCollarEndpointWeight v).mul hcut).congr_deriv
      (by unfold criticalTruncatedEndpointWeightDeriv; ring)
  have h1 : criticalTruncatedEndpointWeight V 1 = 0 := by
    rw [criticalTruncatedEndpointWeight, criticalCollarEndpointWeight_eq_zero le_rfl, zero_mul]
  have ht : Tendsto (criticalTruncatedEndpointWeight V) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (2 * V)] with v hv
    exact (hzero hv).symm
  have h := abs_integral_weight_mul_generalPhaseCombination_le hw hd h1 ht hi hi' S b
  have hτ0 := hw.τ_nonneg
  have hT0 : 0 ≤ (2 * (1 + τ) / Real.pi ^ 3) * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) := by
    have := Finset.sum_nonneg fun n (_ : n ∈ S) => div_nonneg (abs_nonneg (b n)) (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    positivity
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hT0)
  unfold criticalTruncatedEndpointConstant
  have hint2 : (∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ)) = 1 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]; norm_num
  calc (∫ v in Ioi 1, |criticalTruncatedEndpointWeightDeriv V v|) ≤
        ∫ v in Ioi 1, (|deriv criticalCollarEndpointWeight v| +
          2 * smoothTransitionSlope * v ^ (-2 : ℝ)) :=
        setIntegral_mono_on hi'.abs (integrableOn_deriv_criticalCollarEndpointWeight.abs.add
          (hw2.const_mul _)) measurableSet_Ioi hbd'
    _ = (∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v|) + 2 * smoothTransitionSlope := by
        rw [integral_add integrableOn_deriv_criticalCollarEndpointWeight.abs (hw2.const_mul _),
          integral_const_mul, hint2, mul_one]

/-! ### Doubly Collared Compact Sources and Receiver Positivity for General Admissible Stencils -/

/-- The far tail `h_w^V = g_{w,c} - g_w^V` removed by the upper cutoff. -/
def generalTruncationTail (w : ℕ → ℝ) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  (1 - criticalUpperCutoff (Real.exp (-x) / V)) * generalCollaredSource w S b x

theorem generalTruncatedSource_add_tail (w : ℕ → ℝ) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    generalTruncatedSource w V S b x + generalTruncationTail w V S b x =
      generalCollaredSource w S b x := by
  unfold generalTruncatedSource generalTruncationTail; ring

theorem generalTruncatedSource_eq (w : ℕ → ℝ) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    generalTruncatedSource w V S b x = criticalUpperCutoff (Real.exp (-x) / V) *
      (Real.smoothTransition (Real.exp (-x) - 1) *
        (Real.exp (x / 2) * generalPhaseCombination w S b (Real.exp (-x)))) := by
  unfold generalTruncatedSource generalCollaredSource
  by_cases hx : x ≤ 0
  · rw [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)]
  · rw [indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx),
      Real.smoothTransition.zero_of_nonpos (by
        have := Real.exp_le_exp.mpr (show -x ≤ 0 by simp only [not_le] at hx; linarith)
        rw [Real.exp_zero] at this; linarith)]
    simp

theorem continuous_generalTruncatedSource {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    Continuous (generalTruncatedSource w V S b) := by
  have he : Continuous fun x : ℝ => Real.exp (-x) := Real.continuous_exp.comp continuous_neg
  rw [show generalTruncatedSource w V S b = fun x => _ from funext (generalTruncatedSource_eq w V S b)]
  exact (continuous_criticalUpperCutoff.comp (he.div_const V)).mul
    ((Real.smoothTransition.continuous.comp (he.sub continuous_const)).mul
      ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
        ((hw.continuous_generalPhaseCombination S b).comp he)))

theorem generalTruncatedSource_eq_zero (w : ℕ → ℝ) {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) {x : ℝ} (hx : x ∉ Icc (-Real.log (2 * V)) 0) :
    generalTruncatedSource w V S b x = 0 := by
  rw [generalTruncatedSource_eq]
  rcases not_and_or.mp hx with h | h
  · rw [not_le] at h
    have h2 : 2 * V < Real.exp (-x) := by
      rw [← Real.exp_log (show 0 < 2 * V by positivity)]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [criticalUpperCutoff_eq_zero (by rw [le_div_iff₀ hV]; linarith), zero_mul]
  · rw [not_le] at h
    rw [Real.smoothTransition.zero_of_nonpos (by
      have := Real.exp_le_exp.mpr (show -x ≤ 0 by linarith)
      rw [Real.exp_zero] at this; linarith), zero_mul, mul_zero]

theorem hasCompactSupport_generalTruncatedSource (w : ℕ → ℝ) {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    HasCompactSupport (generalTruncatedSource w V S b) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => generalTruncatedSource_eq_zero w hV S b hx

/-- The doubly collared general source `g_w^V` as a compactly supported continuous test in `C_c(ℝ, ℝ)`. -/
def generalTruncatedTest {w : ℕ → ℝ} {C_w τ : ℝ} (hw : AdmissibleHarmonicWeight w C_w τ)
    {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨generalTruncatedSource w V S b, continuous_generalTruncatedSource hw V S b⟩,
    hasCompactSupport_generalTruncatedSource w hV S b⟩

theorem generalTruncatedSource_mass_and_tail_bounds {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) {V : ℝ} (hV : 2 + generalWindowLength τ ≤ V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    AdmissibleSource (generalTruncatedSource w V S b) ∧
    AdmissibleSource (generalTruncationTail w V S b) ∧
    generalCollarMassLower τ * ∑ n ∈ S, b n ^ 2 ≤ ∫ x, generalTruncatedSource w V S b x ^ 2 ∧
    (∫ x, generalTruncatedSource w V S b x ^ 2) ≤ generalCollarMassUpper τ * ∑ n ∈ S, b n ^ 2 ∧
    (∫ x, generalTruncationTail w V S b x ^ 2) ≤ generalCollarMassUpper τ / V * ∑ n ∈ S, b n ^ 2 := by
  have hL := generalWindowLength_pos hw.τ_nonneg hw.τ_lt_one
  have hV1 : 1 ≤ V := by linarith
  have hV0 : 0 < V := by linarith
  obtain ⟨hAdm_c, _, hup_c⟩ := generalCollaredSource_mass_bounds hw S b
  have hcont_t := continuous_generalTruncatedSource hw V S b
  have hcont_c : Continuous (generalCollaredSource w S b) := by
    have heq : generalCollaredSource w S b = fun y =>
        Real.smoothTransition (Real.exp (-y) - 1) *
          (Real.exp (y / 2) * generalPhaseCombination w S b (Real.exp (-y))) := by
      funext y; unfold generalCollaredSource
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
  have hAdm_t : AdmissibleSource (generalTruncatedSource w V S b) := by
    have hm : AEStronglyMeasurable (fun x => (generalTruncatedSource w V S b x : ℂ)) volume :=
      (Complex.continuous_ofReal.comp hcont_t).aestronglyMeasurable
    have hle : ∀ᵐ x ∂volume, ‖(generalTruncatedSource w V S b x : ℂ)‖ ≤
        ‖(generalCollaredSource w S b x : ℂ)‖ := Eventually.of_forall fun x => by
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        generalTruncatedSource, abs_mul, abs_of_nonneg (criticalUpperCutoff_nonneg _)]
      exact mul_le_of_le_one_left (abs_nonneg _) (criticalUpperCutoff_le_one _)
    exact ⟨hAdm_c.1.norm.mono' hm (by simpa using hle), hAdm_c.2.of_le hm hle⟩
  have hAdm_tail : AdmissibleSource (generalTruncationTail w V S b) := by
    have hcont_tail : Continuous (generalTruncationTail w V S b) := by
      have : generalTruncationTail w V S b =
          fun x => generalCollaredSource w S b x - generalTruncatedSource w V S b x := by
        funext x; linarith [generalTruncatedSource_add_tail w V S b x]
      rw [this]; exact hcont_c.sub hcont_t
    have hm : AEStronglyMeasurable (fun x => (generalTruncationTail w V S b x : ℂ)) volume :=
      (Complex.continuous_ofReal.comp hcont_tail).aestronglyMeasurable
    have hle : ∀ᵐ x ∂volume, ‖(generalTruncationTail w V S b x : ℂ)‖ ≤
        ‖(generalCollaredSource w S b x : ℂ)‖ := Eventually.of_forall fun x => by
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        generalTruncationTail, abs_mul,
        abs_of_nonneg (by linarith [criticalUpperCutoff_le_one (Real.exp (-x) / V)])]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (by linarith [criticalUpperCutoff_nonneg (Real.exp (-x) / V)])
    exact ⟨hAdm_c.1.norm.mono' hm (by simpa using hle), hAdm_c.2.of_le hm hle⟩
  set B := generalPhaseCombination w S b
  set Bc := generalComplexPhaseCombination w S (fun n => (b n : ℂ))
  have hB_eq (v : ℝ) : ‖Bc v‖ ^ 2 = B v ^ 2 := by
    rw [generalComplexPhaseCombination_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hDom : IntegrableOn (fun v => v ^ (-2 : ℝ) * ‖Bc v‖ ^ 2) (Ioi 1) := by
    simpa using integrableOn_rpow_neg_two_mul_norm_sq_generalComplexPhaseCombination_dilate hw
      S (fun n => (b n : ℂ)) 1
  -- Truncated mass ceiling
  have hint_c2 : Integrable fun y => generalCollaredSource w S b y ^ 2 := by
    have := (memLp_two_iff_integrable_sq_norm hAdm_c.1.aestronglyMeasurable).mp hAdm_c.2
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using this
  have hup_t : (∫ x, generalTruncatedSource w V S b x ^ 2) ≤
      generalCollarMassUpper τ * ∑ n ∈ S, b n ^ 2 := by
    refine (integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _) hint_c2
      (Eventually.of_forall fun y => ?_)).trans hup_c
    simp only [generalTruncatedSource]
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _)
      (pow_le_one₀ (criticalUpperCutoff_nonneg _) (criticalUpperCutoff_le_one _))
  -- Truncated mass floor on `[2, 2 + generalWindowLength τ]`
  have hlo_t : generalCollarMassLower τ * ∑ n ∈ S, b n ^ 2 ≤
      ∫ x, generalTruncatedSource w V S b x ^ 2 := by
    set H : ℝ → ℝ := fun v => Real.smoothTransition (v - 1) ^ 2 *
      criticalUpperCutoff (v / V) ^ 2 * B v ^ 2
    have hsq_eq : (∫ x, generalTruncatedSource w V S b x ^ 2) =
        ∫ v in Ioi (1 : ℝ), H v / v ^ 2 := by
      have hpt : ∀ x, generalTruncatedSource w V S b x ^ 2 =
          (Iic (0 : ℝ)).indicator (fun y => Real.exp y * H (Real.exp (-y))) x := by
        intro x
        by_cases hx : x ≤ 0
        · rw [indicator_of_mem (show x ∈ Iic 0 from hx), generalTruncatedSource,
            generalCollaredSource, indicator_of_mem (show x ∈ Iic 0 from hx)]
          have : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; ring_nf
          simp only [H]; rw [mul_pow, mul_pow, mul_pow, this]; ring
        · rw [indicator_of_notMem (show x ∉ Iic 0 from hx), generalTruncatedSource,
            generalCollaredSource, indicator_of_notMem (show x ∉ Iic 0 from hx)]
          ring
      rw [funext hpt, integral_indicator measurableSet_Iic, integral_Iic_zero_exp_mul_comp_exp_neg H]
    have hInt_Ioi : IntegrableOn (fun v => H v / v ^ 2) (Ioi 1) := by
      refine hDom.mono' ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable (fun v hv => ?_) measurableSet_Ioi
        have hv0 : (0 : ℝ) < v := lt_trans zero_lt_one hv
        exact ((((((Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)).pow 2).mul
          ((continuous_criticalUpperCutoff.comp (continuous_id.div_const V)).pow 2)).mul
            ((hw.continuous_generalPhaseCombination S b).pow 2)).continuousAt).div
              (continuous_id.pow 2).continuousAt (pow_ne_zero 2 hv0.ne')).continuousWithinAt
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        have hv0 : 0 < v := lt_trans zero_lt_one hv
        have hσ : Real.smoothTransition (v - 1) ^ 2 ≤ 1 :=
          pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
        have hχ : criticalUpperCutoff (v / V) ^ 2 ≤ 1 :=
          pow_le_one₀ (criticalUpperCutoff_nonneg _) (criticalUpperCutoff_le_one _)
        rw [Real.norm_of_nonneg (by dsimp [H]; positivity), hB_eq, Real.rpow_neg hv0.le,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_mul_eq_div]
        refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
        dsimp [H]
        calc Real.smoothTransition (v - 1) ^ 2 * criticalUpperCutoff (v / V) ^ 2 * B v ^ 2
            ≤ 1 * 1 * B v ^ 2 := by gcongr
          _ = B v ^ 2 := by ring
    rw [hsq_eq]
    set L := generalWindowLength τ
    have hsub : Ioc 2 (2 + L) ⊆ Ioi (1 : ℝ) := fun v hv => lt_trans one_lt_two hv.1
    have hrest : (∫ v in Ioc 2 (2 + L), H v / v ^ 2) ≤ ∫ v in Ioi 1, H v / v ^ 2 :=
      setIntegral_mono_set hInt_Ioi (Eventually.of_forall fun v => by dsimp [H]; positivity)
        (Eventually.of_forall hsub)
    have hwin := generalComplexPhaseCombination_window_lower hw S (fun n => (b n : ℂ)) 2
    simp only [hB_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hwin
    rw [intervalIntegral.integral_of_le (by linarith)] at hwin
    have hB_int : IntegrableOn (fun v => B v ^ 2) (Ioc 2 (2 + L)) :=
      ((hw.continuous_generalPhaseCombination S b).pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hpt : (∫ v in Ioc 2 (2 + L), B v ^ 2 / (2 + L) ^ 2) ≤
        ∫ v in Ioc 2 (2 + L), H v / v ^ 2 := by
      refine setIntegral_mono_on (hB_int.div_const _) (hInt_Ioi.mono_set hsub) measurableSet_Ioc
        fun v hv => ?_
      have hv2 : 2 ≤ v := hv.1.le
      have hσ : Real.smoothTransition (v - 1) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith)
      have hχ : criticalUpperCutoff (v / V) = 1 :=
        criticalUpperCutoff_eq_one (by rw [div_le_one hV0]; linarith [hv.2])
      simp only [H, hσ, hχ, one_pow, one_mul]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (pow_le_pow_left₀ (by linarith) hv.2 2)
    rw [integral_div] at hpt
    unfold generalCollarMassLower
    rw [div_mul_eq_mul_div]
    exact (div_le_div_of_nonneg_right hwin (sq_nonneg _)).trans (hpt.trans hrest)
  -- Tail mass bound `∫ h² ≤ (U_w(τ) / V) ∑ b_n²`
  have htail : (∫ x, generalTruncationTail w V S b x ^ 2) ≤
      generalCollarMassUpper τ / V * ∑ n ∈ S, b n ^ 2 := by
    set H : ℝ → ℝ := fun v => Real.smoothTransition (v - 1) ^ 2 *
      (1 - criticalUpperCutoff (v / V)) ^ 2 * B v ^ 2
    have hsq_eq : (∫ x, generalTruncationTail w V S b x ^ 2) =
        ∫ v in Ioi (1 : ℝ), H v / v ^ 2 := by
      have hpt : ∀ x, generalTruncationTail w V S b x ^ 2 =
          (Iic (0 : ℝ)).indicator (fun y => Real.exp y * H (Real.exp (-y))) x := by
        intro x
        by_cases hx : x ≤ 0
        · rw [indicator_of_mem (show x ∈ Iic 0 from hx), generalTruncationTail,
            generalCollaredSource, indicator_of_mem (show x ∈ Iic 0 from hx)]
          have : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; ring_nf
          simp only [H]; rw [mul_pow, mul_pow, mul_pow, this]; ring
        · rw [indicator_of_notMem (show x ∉ Iic 0 from hx), generalTruncationTail,
            generalCollaredSource, indicator_of_notMem (show x ∉ Iic 0 from hx)]
          ring
      rw [funext hpt, integral_indicator measurableSet_Iic, integral_Iic_zero_exp_mul_comp_exp_neg H]
    set G : ℝ → ℝ := fun v => B v ^ 2 / v ^ 2
    have hdil := integral_Ioi_one_rpow_neg_two_mul_norm_sq_general_dilate_le hw S
      (fun n => (b n : ℂ)) hV1
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hdil
    have hdilB : (∫ u in Ioi 1, u ^ (-2 : ℝ) * B (V * u) ^ 2) ≤
        generalCollarMassUpper τ * ∑ n ∈ S, b n ^ 2 := by
      refine le_of_eq_of_le (setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_) hdil
      rw [hB_eq]
    have hGint : IntegrableOn G (Ioi V) := by
      refine (hDom.mono_set (Ioi_subset_Ioi hV1)).congr_fun (fun v hv => ?_) measurableSet_Ioi
      have hv0 : 0 < v := lt_of_lt_of_le hV0 (le_of_lt hv)
      simp only [G, hB_eq, Real.rpow_neg hv0.le, Real.rpow_two]; ring
    have hsubst : ∫ v in Ioi V, G v = V⁻¹ * ∫ u in Ioi 1, u ^ (-2 : ℝ) * B (V * u) ^ 2 := by
      have h := integral_comp_mul_left_Ioi G 1 hV0
      rw [mul_one, smul_eq_mul] at h
      rw [show (∫ v in Ioi V, G v) = V * ∫ u in Ioi 1, G (V * u) by rw [h]; field_simp]
      rw [← integral_const_mul, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      have hu0 : 0 < u := lt_trans one_pos hu
      simp only [G]; rw [Real.rpow_neg hu0.le, Real.rpow_two]; field_simp
    have hpt : ∀ v ∈ Ioi (1 : ℝ), H v / v ^ 2 ≤ (Ioi V).indicator G v := by
      intro v _
      by_cases hvV : v ∈ Ioi V
      · rw [indicator_of_mem hvV]
        have h1 : Real.smoothTransition (v - 1) ^ 2 ≤ 1 :=
          pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
        have h2 : (1 - criticalUpperCutoff (v / V)) ^ 2 ≤ 1 :=
          pow_le_one₀ (by linarith [criticalUpperCutoff_le_one (v / V)])
            (by linarith [criticalUpperCutoff_nonneg (v / V)])
        simp only [G, H]
        gcongr
        calc Real.smoothTransition (v - 1) ^ 2 * (1 - criticalUpperCutoff (v / V)) ^ 2 * B v ^ 2 ≤
              1 * 1 * B v ^ 2 := by gcongr
          _ = B v ^ 2 := by ring
      · rw [indicator_of_notMem hvV]
        have : criticalUpperCutoff (v / V) = 1 :=
          criticalUpperCutoff_eq_one (by rw [div_le_one hV0]; exact not_lt.mp hvV)
        simp [H, this]
    rw [hsq_eq]
    calc (∫ v in Ioi 1, H v / v ^ 2) ≤ ∫ v in Ioi 1, (Ioi V).indicator G v := by
          refine setIntegral_mono_on ?_ ((hGint.integrable_indicator measurableSet_Ioi).integrableOn)
            measurableSet_Ioi hpt
          refine ((hGint.integrable_indicator measurableSet_Ioi).integrableOn).mono' ?_ ?_
          · refine ContinuousOn.aestronglyMeasurable (fun v hv => ?_) measurableSet_Ioi
            have hv0 : (0 : ℝ) < v := lt_trans zero_lt_one hv
            exact ((((((Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)).pow 2).mul
              ((continuous_const.sub (continuous_criticalUpperCutoff.comp (continuous_id.div_const V))).pow 2)).mul
                ((hw.continuous_generalPhaseCombination S b).pow 2)).continuousAt).div
                  (continuous_id.pow 2).continuousAt (pow_ne_zero 2 hv0.ne')).continuousWithinAt
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
            rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [H]; positivity)]
            exact hpt v hv
      _ = ∫ v in Ioi V, G v := by
          rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi hV1)]
      _ ≤ V⁻¹ * (generalCollarMassUpper τ * ∑ n ∈ S, b n ^ 2) := by rw [hsubst]; gcongr
      _ = generalCollarMassUpper τ / V * ∑ n ∈ S, b n ^ 2 := by ring
  exact ⟨hAdm_t, hAdm_tail, hlo_t, hup_t, htail⟩

/-- Truncation threshold `V₀(τ) = max(2 + L(τ), 8 U_w(τ) / A_w(τ))` for a general admissible
harmonic weight sequence. -/
def generalTruncationThreshold (τ : ℝ) : ℝ :=
  max (2 + generalWindowLength τ) (8 * generalCollarMassUpper τ / generalCollarMassLower τ)

/-- Logarithmic archimedean slope `s_{w,T}(τ) = e^{-1/2} generalCollarMassLower τ / 4` of the
doubly collared source `generalTruncatedSource`. -/
def generalTruncatedArchLogSlope (τ : ℝ) : ℝ :=
  Real.exp (-(1 / 2 : ℝ)) * (generalCollarMassLower τ / 4)

/-- Logarithmic archimedean offset `c_{w,T}(C_w, τ)` of the doubly collared source
`generalTruncatedSource`. -/
def generalTruncatedArchLogOffset (C_w τ : ℝ) : ℝ :=
  3 + Real.log (1 / lowFreqRelativeCutoff (generalCollarMassLower τ / 2)
    (2 * C_w * criticalCollarLowFreqConstant))

theorem generalTruncatedArchLogSlope_pos {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    0 < generalTruncatedArchLogSlope τ := by
  unfold generalTruncatedArchLogSlope
  have := generalCollarMassLower_pos hτ0 hτ1
  positivity

/-- **Truncated archimedean log-coercivity for `generalTruncatedSource`.**
For every `AdmissibleHarmonicWeight w C_w τ`, every family on scales `n + 1 ≥ M ≥ 2`, and every
`V ≥ generalTruncationThreshold τ`,
`sourceLevyEnergy (generalTruncatedSource w V S b) ≥ s_{w,T}(τ) (log M - c_{w,T}(C_w, τ)) ∑ b_n²`. -/
theorem ofReal_le_sourceLevyEnergy_generalTruncatedSource {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ}
    (hM : 2 ≤ M) (hS : ∀ n ∈ S, M ≤ n + 1) {V : ℝ}
    (hV : generalTruncationThreshold τ ≤ V) :
    ENNReal.ofReal (generalTruncatedArchLogSlope τ *
      (Real.log M - generalTruncatedArchLogOffset C_w τ) * ∑ n ∈ S, b n ^ 2) ≤
      sourceLevyEnergy (generalTruncatedSource w V S b) := by
  set A := generalCollarMassLower τ
  set D := 2 * C_w * criticalCollarLowFreqConstant
  set U := generalCollarMassUpper τ
  set η := lowFreqRelativeCutoff (A / 2) D
  set E := ∑ n ∈ S, b n ^ 2
  set g := generalTruncatedSource w V S b
  have hA : 0 < A := generalCollarMassLower_pos hw.τ_nonneg hw.τ_lt_one
  have hD : 0 < D := mul_pos (mul_pos zero_lt_two hw.C_pos) criticalCollarLowFreqConstant_pos
  have hη : 0 < η := lowFreqRelativeCutoff_pos (by positivity) hD
  have hE : 0 ≤ E := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hU : 0 ≤ U := (generalCollarMassUpper_pos hw.τ_nonneg).le
  have hL := generalWindowLength_pos hw.τ_nonneg hw.τ_lt_one
  have hV1 : 2 + generalWindowLength τ ≤ V := (le_max_left _ _).trans hV
  have hV2 : 8 * U / A ≤ V := (le_max_right _ _).trans hV
  have hVpos : 0 < V := by linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set R := η * M
  have hRpos : 0 < R := mul_pos hη hMpos
  have hlogR : Real.log M - generalTruncatedArchLogOffset C_w τ = Real.log R - 3 := by
    unfold generalTruncatedArchLogOffset
    rw [Real.log_mul hη.ne' hMpos.ne', one_div, Real.log_inv]; ring
  rw [hlogR]
  have hs : 0 < generalTruncatedArchLogSlope τ :=
    generalTruncatedArchLogSlope_pos hw.τ_nonneg hw.τ_lt_one
  rcases le_or_gt (Real.log R - 3) 0 with hneg | hpos
  · rw [ENNReal.ofReal_of_nonpos]
    · exact zero_le
    · have : generalTruncatedArchLogSlope τ * (Real.log R - 3) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs.le hneg
      nlinarith
  have hR1 : 1 ≤ R := by
    by_contra h
    have := Real.log_nonpos hRpos.le (not_le.mp h).le
    linarith
  obtain ⟨hg, hh, hmass, -, htail⟩ := generalTruncatedSource_mass_and_tail_bounds hw hV1 S b
  obtain ⟨hgc, -, -⟩ := generalCollaredSource_mass_bounds hw S b
  have hhigh := sourceLevyEnergy_ge_highBand hg hR1
  have hmi := integrable_levySourceSpectralDensity hg
  have hhi := integrable_levySourceSpectralDensity hh
  have hsplit : ∀ t, levySourceSpectralDensity g t ≤
      2 * levySourceSpectralDensity (generalCollaredSource w S b) t +
        2 * levySourceSpectralDensity (generalTruncationTail w V S b) t := by
    intro t
    have hfun : (fun x => (g x : ℂ)) = (fun x => (generalCollaredSource w S b x : ℂ)) +
        (-1 : ℂ) • fun x => (generalTruncationTail w V S b x : ℂ) := by
      funext x
      have := generalTruncatedSource_add_tail w V S b x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, g]
      rw [← this]; push_cast; ring
    unfold levySourceSpectralDensity
    rw [hfun, RHTower.WeilSpectral.paperFT_add_smul_real hgc.1 hh.1, neg_one_mul, ← sub_eq_add_neg]
    have := norm_sub_le (paperFT (fun x => (generalCollaredSource w S b x : ℂ)) t)
      (paperFT (fun x => (generalTruncationTail w V S b x : ℂ)) t)
    nlinarith [norm_nonneg (paperFT (fun x => (generalCollaredSource w S b x : ℂ)) t -
      paperFT (fun x => (generalTruncationTail w V S b x : ℂ)) t),
      sq_nonneg (‖paperFT (fun x => (generalCollaredSource w S b x : ℂ)) t‖ -
        ‖paperFT (fun x => (generalTruncationTail w V S b x : ℂ)) t‖),
      norm_nonneg (paperFT (fun x => (generalCollaredSource w S b x : ℂ)) t),
      norm_nonneg (paperFT (fun x => (generalTruncationTail w V S b x : ℂ)) t)]
  have hlowc : ∀ t ∈ Icc (-R) R, levySourceSpectralDensity (generalCollaredSource w S b) t ≤
      2 * D ^ 2 / M * E := by
    intro t ht
    refine norm_sq_paperFT_generalCollaredSource_le hw S b hM hS ?_
    have hηπ : η ≤ Real.pi := (min_le_right _ _).trans (min_le_left _ _)
    calc |t| ≤ R := abs_le.mpr ht
      _ ≤ Real.pi * M := mul_le_mul_of_nonneg_right hηπ hMpos.le
  have hhtot := integral_levySourceSpectralDensity hh
  have hhnn : ∀ t, 0 ≤ levySourceSpectralDensity (generalTruncationTail w V S b) t :=
    fun t => sq_nonneg _
  have hlow : 1 / (2 * Real.pi) * ∫ t in Icc (-R) R, levySourceSpectralDensity g t ≤
      A / 2 * E + 2 * (U / V * E) := by
    have h1 : (∫ t in Icc (-R) R, levySourceSpectralDensity g t) ≤
        ∫ t in Icc (-R) R, (2 * (2 * D ^ 2 / M * E) +
          2 * levySourceSpectralDensity (generalTruncationTail w V S b) t) :=
      setIntegral_mono_on hmi.integrableOn ((integrableOn_const (by simp)).add
        (hhi.integrableOn.const_mul 2)) measurableSet_Icc fun t ht => (hsplit t).trans
          (by gcongr; exact hlowc t ht)
    have h2 : (∫ t in Icc (-R) R, (2 * (2 * D ^ 2 / M * E) +
        2 * levySourceSpectralDensity (generalTruncationTail w V S b) t)) ≤
        (2 * R) * (2 * (2 * D ^ 2 / M * E)) +
          2 * (2 * Real.pi * ∫ x, generalTruncationTail w V S b x ^ 2) := by
      have hc : IntegrableOn (fun _ : ℝ => 2 * (2 * D ^ 2 / M * E)) (Icc (-R) R) :=
        integrableOn_const (by simp)
      rw [integral_add hc (hhi.integrableOn.const_mul 2), setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, integral_const_mul, ← hhtot]
      rw [show R - -R = 2 * R by ring]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hhi (Eventually.of_forall hhnn)) (by norm_num))
    have hpi : 0 < Real.pi := Real.pi_pos
    have h3 : 1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E)) ≤ (A / 2) / 2 * E := by
      have := low_band_plancherel_energy_le_half_arch (A := A / 2) hD hE hM
      calc 1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E)) =
            (1 / (2 * Real.pi)) * (2 * η * (M : ℝ)) * (2 * D ^ 2 * E / (M : ℝ)) := by ring
        _ ≤ _ := this
    calc 1 / (2 * Real.pi) * ∫ t in Icc (-R) R, levySourceSpectralDensity g t ≤
          1 / (2 * Real.pi) * ((2 * R) * (2 * (2 * D ^ 2 / M * E)) +
            2 * (2 * Real.pi * ∫ x, generalTruncationTail w V S b x ^ 2)) := by
          gcongr; exact h1.trans h2
      _ = 2 * (1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E))) +
            2 * ∫ x, generalTruncationTail w V S b x ^ 2 := by field_simp
      _ ≤ 2 * ((A / 2) / 2 * E) + 2 * (U / V * E) := by gcongr
      _ = A / 2 * E + 2 * (U / V * E) := by ring
  have hUV : 2 * (U / V * E) ≤ A / 4 * E := by
    have : U / V ≤ A / 8 := by
      rw [div_le_iff₀ hVpos]
      have := (div_le_iff₀ hA).mp hV2
      linarith
    nlinarith
  have htot := integral_levySourceSpectralDensity hg
  have hsplit2 := integral_add_compl (measurableSet_Icc (a := -R) (b := R)) hmi
  have hhighmass : A / 4 * E ≤ 1 / (2 * Real.pi) * ∫ t in (Icc (-R) R)ᶜ, levySourceSpectralDensity g t := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1 : 1 / (2 * Real.pi) * ∫ t, levySourceSpectralDensity g t = ∫ y, g y ^ 2 := by
      rw [htot]; field_simp; rfl
    rw [← hsplit2, mul_add] at h1
    linarith
  refine le_trans ?_ hhigh
  have hc0 : 0 ≤ Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3) := by positivity
  rw [show generalTruncatedArchLogSlope τ * (Real.log R - 3) * E =
      (Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3)) * (A / 4 * E) by
      unfold generalTruncatedArchLogSlope; ring, ENNReal.ofReal_mul hc0]
  gcongr

/-- Complete energy of `generalTruncatedSource w V S b` in Gamma–Lévy form:
`Lévy(g_w^V) + Ω(0) ac_w^V(0) + 2 R_w^V E_w^V - 2 P_w^V`. -/
def generalTruncatedCompleteEnergy (w : ℕ → ℝ) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) : EReal :=
  (sourceLevyEnergy (generalTruncatedSource w V S b) : EReal) +
    ((EF.gammaBracket 0 * sourceAutocorrelation (generalTruncatedSource w V S b) 0 +
      2 * (generalTruncatedPolarReadout w V S b * generalTruncatedPolarEndpoint w V S b) -
      2 * generalTruncatedPrimeEnergy w V S b : ℝ) : EReal)

/-- Channel constant `K_{w,T}(C_w, τ)` bounding the Gamma, polar, and prime channels of
`generalTruncatedSource`, uniformly in `V`. -/
def generalTruncatedChannelConstant (C_w τ : ℝ) : ℝ :=
  |EF.gammaBracket 0| * generalCollarMassUpper τ +
    2 * (2 * (1 + τ) / Real.pi ^ 3) ^ 2 *
      criticalTruncatedReadoutConstant * criticalTruncatedEndpointConstant +
    2 * C_w ^ 2 * criticalTruncatedPrimeConstant

/-- **Lipschitz continuity of `generalTruncatedSource` whenever `generalPhaseCombination` is Lipschitz.** -/
theorem exists_lipschitz_generalTruncatedSource {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) {L_B : ℝ} (hL_B : 0 ≤ L_B)
    (hLip : ∀ u v, |generalPhaseCombination w S b u - generalPhaseCombination w S b v| ≤ L_B * |u - v|) :
    ∃ K : ℝ, ∀ x y, |generalTruncatedSource w V S b x - generalTruncatedSource w V S b y| ≤
      K * |x - y| := by
  set a := -Real.log (2 * V)
  set g := generalTruncatedSource w V S b
  by_cases ha : a ≤ 0
  swap
  · refine ⟨0, fun x y => ?_⟩
    have hz (z : ℝ) : g z = 0 :=
      generalTruncatedSource_eq_zero w hV S b fun h => ha (h.1.trans h.2)
    rw [hz x, hz y, sub_self, abs_zero, zero_mul]
  set s := Icc a 0
  have hea : Real.exp (-a) = 2 * V := by
    simp only [a, neg_neg]; exact Real.exp_log (by positivity)
  have hExp_sub : ∀ x ∈ s, ∀ y ∈ s, |Real.exp (-x) - Real.exp (-y)| ≤ 2 * V * |x - y| := by
    intro x hx y hy
    wlog hxy : x ≤ y generalizing x y
    · rw [abs_sub_comm, abs_sub_comm x]; exact this y hy x hx (le_of_not_ge hxy)
    have h1 : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    have h2 : 1 - Real.exp (-(y - x)) ≤ y - x := by linarith [Real.add_one_le_exp (-(y - x))]
    have h3 : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
      rw [← Real.exp_add]; ring_nf
    have h4 : Real.exp (-x) ≤ 2 * V := by
      rw [← hea]; exact Real.exp_le_exp.mpr (by linarith [hx.1])
    rw [h3]
    nlinarith [Real.exp_pos (-x), Real.exp_pos (-(y - x))]
  have hsl := smoothTransitionSlope_nonneg
  have hA : ∀ x ∈ s, ∀ y ∈ s, |criticalUpperCutoff (Real.exp (-x) / V) -
      criticalUpperCutoff (Real.exp (-y) / V)| ≤ smoothTransitionSlope * 2 * |x - y| := by
    intro x hx y hy
    unfold criticalUpperCutoff
    rw [show 1 - Real.smoothTransition (Real.exp (-x) / V - 1) -
        (1 - Real.smoothTransition (Real.exp (-y) / V - 1)) =
        Real.smoothTransition (Real.exp (-y) / V - 1) - Real.smoothTransition (Real.exp (-x) / V - 1)
        by ring]
    refine (abs_smoothTransition_sub_le _ _).trans ?_
    rw [show Real.exp (-y) / V - 1 - (Real.exp (-x) / V - 1) = (Real.exp (-x) - Real.exp (-y)) / -V
      by field_simp; ring, abs_div, abs_neg, abs_of_pos hV]
    calc smoothTransitionSlope * (|Real.exp (-x) - Real.exp (-y)| / V) ≤
          smoothTransitionSlope * (2 * V * |x - y| / V) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hExp_sub x hx y hy) hV.le) hsl
      _ = smoothTransitionSlope * 2 * |x - y| := by field_simp
  have hA' : ∀ x ∈ s, |criticalUpperCutoff (Real.exp (-x) / V)| ≤ 1 := fun x _ => by
    rw [abs_of_nonneg (criticalUpperCutoff_nonneg _)]; exact criticalUpperCutoff_le_one _
  have hB : ∀ x ∈ s, ∀ y ∈ s, |Real.smoothTransition (Real.exp (-x) - 1) -
      Real.smoothTransition (Real.exp (-y) - 1)| ≤ smoothTransitionSlope * (2 * V) * |x - y| := by
    intro x hx y hy
    refine (abs_smoothTransition_sub_le _ _).trans ?_
    rw [show Real.exp (-x) - 1 - (Real.exp (-y) - 1) = Real.exp (-x) - Real.exp (-y) by ring, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hExp_sub x hx y hy) hsl
  have hB' : ∀ x ∈ s, |Real.smoothTransition (Real.exp (-x) - 1)| ≤ 1 := fun x _ => by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
  have hC : ∀ x ∈ s, ∀ y ∈ s, |Real.exp (x / 2) - Real.exp (y / 2)| ≤ 1 / 2 * |x - y| := by
    intro x hx y hy
    wlog hxy : x ≤ y generalizing x y
    · rw [abs_sub_comm, abs_sub_comm x]; exact this y hy x hx (le_of_not_ge hxy)
    have h1 : Real.exp (x / 2) ≤ Real.exp (y / 2) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    have h2 : 1 - Real.exp (-((y - x) / 2)) ≤ (y - x) / 2 := by
      linarith [Real.add_one_le_exp (-((y - x) / 2))]
    have h3 : Real.exp (x / 2) = Real.exp (y / 2) * Real.exp (-((y - x) / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have h4 : Real.exp (y / 2) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith [hy.2])
    rw [h3]
    nlinarith [Real.exp_pos (y / 2), Real.exp_pos (-((y - x) / 2))]
  have hC' : ∀ x ∈ s, |Real.exp (x / 2)| ≤ 1 := fun x hx => by
    rw [abs_of_pos (Real.exp_pos _)]
    have := Real.exp_le_exp.mpr (show x / 2 ≤ 0 by linarith [hx.2])
    rwa [Real.exp_zero] at this
  set CB := (4 * (1 + τ) / Real.pi ^ 2) * ∑ n ∈ S, |b n|
  have hCB : 0 ≤ CB := by
    have := hw.τ_nonneg
    have := Finset.sum_nonneg fun n (_ : n ∈ S) => abs_nonneg (b n)
    positivity
  have hD : ∀ x ∈ s, ∀ y ∈ s, |generalPhaseCombination w S b (Real.exp (-x)) -
      generalPhaseCombination w S b (Real.exp (-y))| ≤ L_B * (2 * V) * |x - y| := by
    intro x hx y hy
    refine (hLip _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hExp_sub x hx y hy) hL_B
  have hD' : ∀ x ∈ s, |generalPhaseCombination w S b (Real.exp (-x))| ≤ CB :=
    fun x _ => hw.abs_generalPhaseCombination_le S b _
  have hmul_lip {f1 f2 : ℝ → ℝ} {F1 F2 K1 K2 : ℝ} (hF1 : 0 ≤ F1) (hF2 : 0 ≤ F2)
      (hf1 : ∀ x ∈ s, |f1 x| ≤ F1) (hf2 : ∀ x ∈ s, |f2 x| ≤ F2)
      (hf1L : ∀ x ∈ s, ∀ y ∈ s, |f1 x - f1 y| ≤ K1 * |x - y|)
      (hf2L : ∀ x ∈ s, ∀ y ∈ s, |f2 x - f2 y| ≤ K2 * |x - y|) :
      (∀ x ∈ s, |f1 x * f2 x| ≤ F1 * F2) ∧
      (∀ x ∈ s, ∀ y ∈ s, |f1 x * f2 x - f1 y * f2 y| ≤ (F1 * K2 + F2 * K1) * |x - y|) := by
    refine ⟨fun x hx => by rw [abs_mul]; exact mul_le_mul (hf1 x hx) (hf2 x hx) (abs_nonneg _) hF1,
      fun x hx y hy => ?_⟩
    rw [show f1 x * f2 x - f1 y * f2 y = f1 x * (f2 x - f2 y) + f2 y * (f1 x - f1 y) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    calc |f1 x| * |f2 x - f2 y| + |f2 y| * |f1 x - f1 y|
        ≤ F1 * (K2 * |x - y|) + F2 * (K1 * |x - y|) :=
          add_le_add (mul_le_mul (hf1 x hx) (hf2L x hx y hy) (abs_nonneg _) hF1)
            (mul_le_mul (hf2 y hy) (hf1L x hx y hy) (abs_nonneg _) hF2)
      _ = (F1 * K2 + F2 * K1) * |x - y| := by ring
  obtain ⟨hCD', hCD⟩ := hmul_lip zero_le_one hCB hC' hD' hC hD
  obtain ⟨hBCD', hBCD⟩ := hmul_lip zero_le_one (by positivity) hB' hCD' hB hCD
  obtain ⟨-, hABCD⟩ := hmul_lip zero_le_one (by positivity) hA' hBCD' hA hBCD
  obtain ⟨K, hgs⟩ : ∃ K, ∀ x ∈ s, ∀ y ∈ s, |g x - g y| ≤ K * |x - y| :=
    ⟨_, fun x hx y hy => by simp only [g, generalTruncatedSource_eq]; exact hABCD x hx y hy⟩
  have hz : ∀ x, x ∉ Ioo a 0 → g x = 0 := by
    intro x hx
    by_cases hxs : x ∈ s
    · rcases (show x = a ∨ x = 0 by
        rcases eq_or_lt_of_le hxs.1 with h | h
        · exact Or.inl h.symm
        · rcases eq_or_lt_of_le hxs.2 with h' | h'
          · exact Or.inr h'
          · exact absurd ⟨h, h'⟩ hx) with rfl | rfl
      · simp only [g, generalTruncatedSource_eq, hea]
        rw [criticalUpperCutoff_eq_zero (by rw [mul_div_assoc, div_self hV.ne', mul_one]), zero_mul]
      · simp only [g, generalTruncatedSource_eq, neg_zero, Real.exp_zero, sub_self,
          Real.smoothTransition.zero, zero_mul, mul_zero]
    · exact generalTruncatedSource_eq_zero w hV S b hxs
  have hproj : ∀ x, g x = g (Set.projIcc a 0 ha x) := by
    intro x
    by_cases hx : x ∈ Ioo a 0
    · rw [Set.projIcc_of_mem ha (Ioo_subset_Icc_self hx)]
    · rw [hz x hx, hz]
      rcases le_or_gt x a with h | h
      · rw [Set.projIcc_of_le_left ha h]; exact fun h' => lt_irrefl _ h'.1
      · have h0 : 0 ≤ x := not_lt.mp fun h0 => hx ⟨h, h0⟩
        rw [Set.projIcc_of_right_le ha h0]; exact fun h' => lt_irrefl _ h'.2
  refine ⟨max K 0, fun x y => ?_⟩
  rw [hproj x, hproj y]
  calc _ ≤ K * |(Set.projIcc a 0 ha x : ℝ) - Set.projIcc a 0 ha y| :=
        hgs _ (Set.projIcc a 0 ha x).2 _ (Set.projIcc a 0 ha y).2
    _ ≤ max K 0 * |(Set.projIcc a 0 ha x : ℝ) - Set.projIcc a 0 ha y| :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
    _ ≤ max K 0 * |x - y| :=
        mul_le_mul_of_nonneg_left (Set.abs_projIcc_sub_projIcc ha) (le_max_right _ _)

/-- **Receiver identity for `generalTruncatedTest`.**
Whenever `generalPhaseCombination w S b` is Lipschitz on `ℝ` (including all divisor stencils
`(D, α)` and all `p ≥ 3` non-Bernoulli filters), the real part of the full Weil functional of `ζ`
on `generalTruncatedTest` equals `generalTruncatedCompleteEnergy w V S b`. -/
theorem compactFullWeilEnergy_generalTruncatedTest {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) {L_B : ℝ} (hL_B : 0 ≤ L_B)
    (hLip : ∀ u v, |generalPhaseCombination w S b u - generalPhaseCombination w S b v| ≤ L_B * |u - v|) :
    (compactFullWeilEnergy (generalTruncatedTest hw hV S b) : EReal) =
      generalTruncatedCompleteEnergy w V S b := by
  set f := generalTruncatedTest hw hV S b
  set g := generalTruncatedSource w V S b
  have hfg : (f : ℝ → ℝ) = g := rfl
  obtain ⟨K, hK⟩ := exists_lipschitz_generalTruncatedSource hw hV S b hL_B hLip
  have hJ := integrableOn_levy_of_lipschitz f (K := K) (by rw [hfg]; exact hK)
  have hW := re_weilFullFunctional_eq_of_compact_finite_jump f hJ
  have hpol := integral_polar_autocorr_eq_moments f
  have hac : ∀ x, autocorr f x = sourceAutocorrelation g x := fun x => by
    rw [← autocorr_neg, hfg]; unfold sourceAutocorrelation autocorr; simp only [sub_eq_add_neg]
  have hprime : (∑' n : ℕ, primeTerm (autocorr f) n) = generalTruncatedPrimeEnergy w V S b := by
    unfold generalTruncatedPrimeEnergy
    refine tsum_congr fun r => ?_
    unfold primeTerm generalTruncatedPrimeAtom primeWeight
    split_ifs
    · rw [← autocorr_neg, hfg]; unfold autocorr; simp only [sub_eq_add_neg]; rfl
    · simp
  have hR : (∫ u, Real.exp (u / 2) * f u) = generalTruncatedPolarReadout w V S b := by
    unfold generalTruncatedPolarReadout; rw [hfg]; exact integral_congr_ae (by
      filter_upwards with u; ring)
  have hE : (∫ u, Real.exp (-(u / 2)) * f u) = generalTruncatedPolarEndpoint w V S b := by
    unfold generalTruncatedPolarEndpoint; rw [hfg]; exact integral_congr_ae (by
      filter_upwards with u; ring)
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    intro x hx
    refine mul_nonneg ?_ (archLevySinhWeight_nonneg (le_of_lt hx))
    have h0 : 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 := integral_nonneg fun u => sq_nonneg _
    rw [integral_sub_shift_sq f.hasCompactSupport f.continuous x] at h0
    linarith
  have hlev : (sourceLevyEnergy g : EReal) = (biScaleLevyEnergy f : ℝ) := by
    unfold sourceLevyEnergy biScaleLevyEnergy
    simp only [← hac]
    rw [← ofReal_integral_eq_lintegral_ofReal hJ
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hnn)),
      EReal.coe_ennreal_ofReal, max_eq_left (setIntegral_nonneg measurableSet_Ioi hnn)]
  unfold compactFullWeilEnergy generalTruncatedCompleteEnergy
  rw [hW, hlev, ← EReal.coe_add, EReal.coe_eq_coe_iff]
  unfold fullPairing
  rw [hprime, hpol, hR, hE, hac 0]
  ring

/-- **Complete energy lower bound on dyadic blocks for `generalTruncatedSource`.** -/
theorem generalTruncatedCompleteEnergy_ge {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) (S : Finset ℕ) (b : ℕ → ℝ)
    {M : ℕ} (hM : 2 ≤ M) (hS : DyadicScaleBlock S M)
    {V : ℝ} (hV : generalTruncationThreshold τ ≤ V) :
    (((generalTruncatedArchLogSlope τ * (Real.log M - generalTruncatedArchLogOffset C_w τ) -
        generalTruncatedChannelConstant C_w τ) * ∑ n ∈ S, b n ^ 2 : ℝ) : EReal) ≤
      generalTruncatedCompleteEnergy w V S b := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hL := generalWindowLength_pos hw.τ_nonneg hw.τ_lt_one
  have hV_win : 2 + generalWindowLength τ ≤ V := (le_max_left _ _).trans hV
  have hV1 : 1 ≤ V := by linarith
  have hV0 : 0 < V := by linarith
  have hM0 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  set X := generalTruncatedArchLogSlope τ * (Real.log M - generalTruncatedArchLogOffset C_w τ) * E
  have hlev : (X : EReal) ≤ (sourceLevyEnergy (generalTruncatedSource w V S b) : EReal) := by
    have h1 := ofReal_le_sourceLevyEnergy_generalTruncatedSource hw S b hM (fun n hn => (hS n hn).1) hV
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  set ac := sourceAutocorrelation (generalTruncatedSource w V S b) 0
  have hac_eq : ac = ∫ x, generalTruncatedSource w V S b x ^ 2 := by
    unfold ac sourceAutocorrelation; simp only [sub_zero, sq]
  have hac0 : 0 ≤ ac := by rw [hac_eq]; exact integral_nonneg fun _ => sq_nonneg _
  obtain ⟨-, -, -, hac_up, -⟩ := generalTruncatedSource_mass_and_tail_bounds hw hV_win S b
  rw [← hac_eq] at hac_up
  have hΩ : -(|EF.gammaBracket 0| * (generalCollarMassUpper τ * E)) ≤ EF.gammaBracket 0 * ac := by
    have h1 : -(|EF.gammaBracket 0| * ac) ≤ EF.gammaBracket 0 * ac := by
      have := neg_abs_le (EF.gammaBracket 0 * ac)
      rwa [abs_mul, abs_of_nonneg hac0] at this
    have h2 : |EF.gammaBracket 0| * ac ≤ |EF.gammaBracket 0| * (generalCollarMassUpper τ * E) :=
      mul_le_mul_of_nonneg_left hac_up (abs_nonneg _)
    linarith
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hT2 := sq_sum_abs_div_succ_le S b hM fun n hn => (hS n hn).1
  have hTE : T ^ 2 ≤ E := hT2.trans (by
    have : 2 / (M : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM0
    nlinarith)
  set a := criticalTruncatedReadoutConstant
  set c := criticalTruncatedEndpointConstant
  have ha : 0 ≤ a := by
    unfold a criticalTruncatedReadoutConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarWeight v| := integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    have : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
    positivity
  have hc : 0 ≤ c := by
    unfold c criticalTruncatedEndpointConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v| :=
      integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    positivity
  have hτ0 := hw.τ_nonneg
  have hpol : |generalTruncatedPolarReadout w V S b * generalTruncatedPolarEndpoint w V S b| ≤
      (2 * (1 + τ) / Real.pi ^ 3) ^ 2 * a * c * E := by
    rw [abs_mul]
    have h1 := abs_generalTruncatedPolarReadout_le hw hV0 S b
    have h2 := abs_generalTruncatedPolarEndpoint_le hw hV1 S b
    have h12 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    calc |generalTruncatedPolarReadout w V S b| * |generalTruncatedPolarEndpoint w V S b|
        ≤ (a * ((2 * (1 + τ) / Real.pi ^ 3) * T)) * (c * ((2 * (1 + τ) / Real.pi ^ 3) * T)) := h12
      _ = (2 * (1 + τ) / Real.pi ^ 3) ^ 2 * a * c * T ^ 2 := by ring
      _ ≤ (2 * (1 + τ) / Real.pi ^ 3) ^ 2 * a * c * E :=
          mul_le_mul_of_nonneg_left hTE (by positivity)
  have hP := abs_generalTruncatedPrimeEnergy_le_of_dyadic hw hV0 (by omega) hS b
  have hP' := (abs_le.mp hP).2
  have hpol' := (abs_le.mp hpol).1
  have hch : -(generalTruncatedChannelConstant C_w τ * E) ≤
      EF.gammaBracket 0 * ac +
        2 * (generalTruncatedPolarReadout w V S b * generalTruncatedPolarEndpoint w V S b) -
        2 * generalTruncatedPrimeEnergy w V S b := by
    unfold generalTruncatedChannelConstant
    nlinarith
  unfold generalTruncatedCompleteEnergy
  rw [show (generalTruncatedArchLogSlope τ * (Real.log M - generalTruncatedArchLogOffset C_w τ) -
      generalTruncatedChannelConstant C_w τ) * E =
      X + -(generalTruncatedChannelConstant C_w τ * E) by ring, EReal.coe_add]
  exact add_le_add hlev (EReal.coe_le_coe_iff.mpr hch)

/-- **Unconditional Block Positivity and Receiver Positivity for All Admissible Harmonic Sources.**
For every `AdmissibleHarmonicWeight w C_w τ`, there is a scale threshold `M₀` such that for all
`M ≥ M₀`, `V ≥ generalTruncationThreshold τ`, every dyadic block `S` at `M`, and every nonzero
pattern `b`, `0 < generalTruncatedCompleteEnergy w V S b`; and whenever `generalPhaseCombination w S b`
is Lipschitz on `ℝ` (in particular for all divisor stencils and all `p ≥ 3` non-Bernoulli filters),
`0 < compactFullWeilEnergy (generalTruncatedTest hw hV S b)` and
`0 < fullZeroForm (generalTruncatedTest hw hV S b)`. -/
theorem exists_generalTruncatedCompleteEnergy_and_receiver_pos {w : ℕ → ℝ} {C_w τ : ℝ}
    (hw : AdmissibleHarmonicWeight w C_w τ) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ V : ℝ, ∀ hV : 0 < V, generalTruncationThreshold τ ≤ V →
      ∀ S : Finset ℕ, DyadicScaleBlock S M → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
        0 < generalTruncatedCompleteEnergy w V S b ∧
        (∀ L_B : ℝ, 0 ≤ L_B →
          (∀ u v, |generalPhaseCombination w S b u - generalPhaseCombination w S b v| ≤ L_B * |u - v|) →
          0 < compactFullWeilEnergy (generalTruncatedTest hw hV S b) ∧
          0 < fullZeroForm (generalTruncatedTest hw hV S b)) := by
  have hs := generalTruncatedArchLogSlope_pos hw.τ_nonneg hw.τ_lt_one
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop
    (generalTruncatedArchLogOffset C_w τ +
      generalTruncatedChannelConstant C_w τ / generalTruncatedArchLogSlope τ)).and
      (eventually_ge_atTop 2))
  refine ⟨M₀, fun M hM V hV hVt S hS b hb => ?_⟩
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  obtain ⟨j, hj, hbj⟩ := hb
  have hE : 0 < ∑ n ∈ S, b n ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  have hgap : 0 < generalTruncatedArchLogSlope τ *
      (Real.log M - generalTruncatedArchLogOffset C_w τ) -
      generalTruncatedChannelConstant C_w τ := by
    have h1 : generalTruncatedChannelConstant C_w τ / generalTruncatedArchLogSlope τ <
        Real.log M - generalTruncatedArchLogOffset C_w τ := by linarith
    have h2 := (div_lt_iff₀ hs).mp h1
    linarith
  have hpos : 0 < generalTruncatedCompleteEnergy w V S b :=
    lt_of_lt_of_le (EReal.coe_pos.mpr (mul_pos hgap hE))
      (generalTruncatedCompleteEnergy_ge hw S b hM2 hS hVt)
  refine ⟨hpos, fun L_B hL_B hLip => ?_⟩
  have hW_eq := compactFullWeilEnergy_generalTruncatedTest hw hV S b hL_B hLip
  have hW_pos : 0 < compactFullWeilEnergy (generalTruncatedTest hw hV S b) := by
    rw [← hW_eq] at hpos
    exact EReal.coe_pos.mp hpos
  refine ⟨hW_pos, ?_⟩
  rwa [fullZeroForm_eq_compactFullWeilEnergy]

/-! ## Section 3: Sign-Definite Cell Kernels Beyond the Dyadic Stencil: Positive-Definite vs Negative-Definite Classification -/

/-- **General harmonic divisor charge** `A_χ(m) = χ(m) ∑_{r ∣ m} r Λ(r) χ(m / r)` associated to
any harmonic multiplier `χ : ℕ → ℝ` (`w_k = χ(k) / k²`). -/
def generalCriticalPrimeHarmonicCharge (χ : ℕ → ℝ) (m : ℕ) : ℝ :=
  χ m * ∑ r ∈ m.divisors, (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * χ (m / r)

theorem generalCriticalPrimeHarmonicCharge_zero (χ : ℕ → ℝ) :
    generalCriticalPrimeHarmonicCharge χ 0 = 0 := by
  simp [generalCriticalPrimeHarmonicCharge]

theorem generalCriticalPrimeHarmonicCharge_one (χ : ℕ → ℝ) :
    generalCriticalPrimeHarmonicCharge χ 1 = 0 := by
  simp [generalCriticalPrimeHarmonicCharge]

/-- At every prime `p`, the harmonic divisor charge is `A_χ(p) = p (log p) χ(1) χ(p)`. -/
theorem generalCriticalPrimeHarmonicCharge_prime (χ : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    generalCriticalPrimeHarmonicCharge χ p = (p : ℝ) * Real.log p * (χ 1 * χ p) := by
  unfold generalCriticalPrimeHarmonicCharge
  rw [hp.divisors, Finset.sum_insert (by simp [hp.ne_one.symm]), Finset.sum_singleton,
    ArithmeticFunction.vonMangoldt_one, mul_zero, zero_mul, zero_add,
    Nat.div_self hp.pos, ArithmeticFunction.vonMangoldt_apply_prime hp]
  ring

theorem generalCriticalPrimeHarmonicCharge_two (χ : ℕ → ℝ) :
    generalCriticalPrimeHarmonicCharge χ 2 = 2 * Real.log 2 * (χ 1 * χ 2) := by
  simpa using generalCriticalPrimeHarmonicCharge_prime χ Nat.prime_two

theorem generalCriticalPrimeHarmonicCharge_dyadic_eq :
    generalCriticalPrimeHarmonicCharge dyadicHarmonicChi =
      factorialCriticalPrimeHarmonicCharge := by
  funext m; rfl

theorem abs_generalCriticalPrimeHarmonicCharge_le {χ : ℕ → ℝ} {C_χ : ℝ}
    (hC : 0 ≤ C_χ) (hχ : ∀ k, |χ k| ≤ C_χ) (m : ℕ) :
    |generalCriticalPrimeHarmonicCharge χ m| ≤ C_χ ^ 2 * ((m : ℝ) * Real.log m) := by
  unfold generalCriticalPrimeHarmonicCharge
  rw [abs_mul]
  have hsum : |∑ r ∈ m.divisors, (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * χ (m / r)| ≤
      C_χ * ((m : ℝ) * Real.log m) := by
    calc |∑ r ∈ m.divisors, (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * χ (m / r)|
        ≤ ∑ r ∈ m.divisors, |(r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * χ (m / r)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ m.divisors, C_χ * ((m : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ)) := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt r : ℝ) :=
            ArithmeticFunction.vonMangoldt_nonneg
          have hrm : (r : ℝ) ≤ m := by exact_mod_cast Nat.divisor_le hr
          rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg r) hΛ)]
          calc (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * |χ (m / r)|
              ≤ (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * C_χ :=
                mul_le_mul_of_nonneg_left (hχ _) (by positivity)
            _ ≤ (m : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * C_χ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrm hΛ) hC
            _ = C_χ * ((m : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ)) := by ring
      _ = C_χ * ((m : ℝ) * Real.log m) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
  calc |χ m| * |∑ r ∈ m.divisors, (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * χ (m / r)|
      ≤ C_χ * (C_χ * ((m : ℝ) * Real.log m)) :=
        mul_le_mul (hχ m) hsum (abs_nonneg _) hC
    _ = C_χ ^ 2 * ((m : ℝ) * Real.log m) := by ring

theorem summable_abs_generalCriticalPrimeHarmonicCharge_div_cube {χ : ℕ → ℝ} {C_χ : ℝ}
    (hC : 0 ≤ C_χ) (hχ : ∀ k, |χ k| ≤ C_χ) :
    Summable fun m : ℕ => |generalCriticalPrimeHarmonicCharge χ m| / (m : ℝ) ^ 3 := by
  refine Summable.of_nonneg_of_le (fun m => div_nonneg (abs_nonneg _) (by positivity))
    (fun m => ?_)
    ((summable_envelopeLogMajorant_of_half_lt (by norm_num : (1 : ℝ) / 2 < 3 / 2)).mul_left (C_χ ^ 2))
  by_cases hm : 2 ≤ m
  · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    calc |generalCriticalPrimeHarmonicCharge χ m| / (m : ℝ) ^ 3
        ≤ (C_χ ^ 2 * ((m : ℝ) * Real.log m)) / (m : ℝ) ^ 3 :=
          div_le_div_of_nonneg_right (abs_generalCriticalPrimeHarmonicCharge_le hC hχ m) (by positivity)
      _ = C_χ ^ 2 * (Real.log m / (m : ℝ) ^ 2) := by field_simp [hm0]
      _ = C_χ ^ 2 * envelopeLogMajorant (3 / 2) m := by
          simp only [envelopeLogMajorant, if_pos hm, show (3 / 2 : ℝ) + 1 / 2 = 2 by norm_num,
            Real.rpow_two]
  · have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl
    · simp [envelopeLogMajorant]
    · simp [envelopeLogMajorant, generalCriticalPrimeHarmonicCharge_one]

/-- **General continuous real cell kernel** `R_χ(t)` on `[0, 1]`, expressed as the charge-weighted
reflected harmonic-tail series:
`R_χ(t) = ∑_{m = 1}^∞ (A_χ(m) / m³) ((T_m(t) + T_m(1 - t)) / 2)`. -/
def generalCriticalPrimeContinuousRealKernel (χ : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, (generalCriticalPrimeHarmonicCharge χ m / (m : ℝ) ^ 3) *
    ((factorialCriticalPrimeHarmonicTail m t + factorialCriticalPrimeHarmonicTail m (1 - t)) / 2)

/-- For the canonical dyadic multiplier `dyadicHarmonicChi`, `generalCriticalPrimeContinuousRealKernel`
coincides with `factorialCriticalPrimeContinuousRealKernel` on `[0, 1]`. -/
theorem generalCriticalPrimeContinuousRealKernel_dyadic_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    generalCriticalPrimeContinuousRealKernel dyadicHarmonicChi t =
      factorialCriticalPrimeContinuousRealKernel t := by
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hcs := summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube
  have hcb (m : ℕ) : |factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3| =
      |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 := by
    rw [abs_div, abs_pow, Nat.abs_cast]
  have hsT {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : Summable fun m : ℕ =>
      factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 * factorialCriticalPrimeHarmonicTail m u := by
    refine (hcs.mul_right (Real.pi ^ 2 / 6)).of_norm_bounded fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Real.norm_eq_abs, abs_mul, hcb, abs_of_nonneg (factorialCriticalPrimeHarmonicTail_nonneg m hu.1)]
      exact mul_le_mul_of_nonneg_left (factorialCriticalPrimeHarmonicTail_le hm hu)
        (div_nonneg (abs_nonneg _) (by positivity))
  unfold generalCriticalPrimeContinuousRealKernel factorialCriticalPrimeContinuousRealKernel
  rw [generalCriticalPrimeHarmonicCharge_dyadic_eq,
    factorialCriticalPrimeCellKernel_eq_tsum_tail ht.1,
    factorialCriticalPrimeCellKernel_eq_tsum_tail ht'.1,
    ← (hsT ht).tsum_add (hsT ht'), ← tsum_div_const]
  refine tsum_congr fun m => by ring

/-- **Poisson window decomposition of `generalCriticalPrimeContinuousRealKernel`.**
On `t ∈ [0, 1]`,
`R_χ(t) = ∑_m A_χ(m) J_m / m⁴ - (1/2) ∑_m (A_χ(m) / m³) (W_m(t) - 2 ∫_0^m γ)`. -/
theorem generalCriticalPrimeContinuousRealKernel_eq_poisson_window {χ : ℕ → ℝ} {C_χ : ℝ}
    (hC : 0 ≤ C_χ) (hχ : ∀ k, |χ k| ≤ C_χ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    generalCriticalPrimeContinuousRealKernel χ t =
      (∑' m : ℕ, generalCriticalPrimeHarmonicCharge χ m * factorialCriticalHarmonicDefect m /
        (m : ℝ) ^ 4) -
      (1 / 2) * ∑' m : ℕ, generalCriticalPrimeHarmonicCharge χ m / (m : ℝ) ^ 3 *
        criticalBandWindowDeviation m t := by
  have hcs := summable_abs_generalCriticalPrimeHarmonicCharge_div_cube hC hχ
  have hcb (m : ℕ) : |generalCriticalPrimeHarmonicCharge χ m / (m : ℝ) ^ 3| =
      |generalCriticalPrimeHarmonicCharge χ m| / (m : ℝ) ^ 3 := by
    rw [abs_div, abs_pow, Nat.abs_cast]
  have hsJ : Summable fun m : ℕ => generalCriticalPrimeHarmonicCharge χ m *
      factorialCriticalHarmonicDefect m / (m : ℝ) ^ 4 := by
    refine (hcs.mul_right 2).of_norm_bounded fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      obtain ⟨hJ0, hJ2⟩ := factorialCriticalHarmonicDefect_bounds m
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hJ0, abs_pow, Nat.abs_cast,
        show (m : ℝ) ^ 4 = (m : ℝ) ^ 3 * m by ring, div_mul_eq_div_div_swap]
      rw [div_le_iff₀ (by positivity)]
      have : |generalCriticalPrimeHarmonicCharge χ m| * factorialCriticalHarmonicDefect m ≤
          |generalCriticalPrimeHarmonicCharge χ m| * 2 :=
        mul_le_mul_of_nonneg_left hJ2 (abs_nonneg _)
      calc |generalCriticalPrimeHarmonicCharge χ m| * factorialCriticalHarmonicDefect m / (m : ℝ)
          ≤ |generalCriticalPrimeHarmonicCharge χ m| * 2 / 1 :=
            div_le_div₀ (by positivity) this one_pos hmR
        _ = _ := by field_simp
  have hsD : Summable fun m : ℕ => generalCriticalPrimeHarmonicCharge χ m / (m : ℝ) ^ 3 *
      criticalBandWindowDeviation m t := by
    refine (hcs.mul_right ((Real.pi / 6) ^ 3 / 35)).of_norm_bounded fun m => ?_
    rw [Real.norm_eq_abs, abs_mul, hcb]
    exact mul_le_mul_of_nonneg_left (abs_criticalBandWindowDeviation_le_cube m ht)
      (div_nonneg (abs_nonneg _) (by positivity))
  have hterm (m : ℕ) : (generalCriticalPrimeHarmonicCharge χ m / (m : ℝ) ^ 3) *
        ((factorialCriticalPrimeHarmonicTail m t + factorialCriticalPrimeHarmonicTail m (1 - t)) / 2) =
      generalCriticalPrimeHarmonicCharge χ m * factorialCriticalHarmonicDefect m / (m : ℝ) ^ 4 -
        1 / 2 * (generalCriticalPrimeHarmonicCharge χ m / (m : ℝ) ^ 3 *
          criticalBandWindowDeviation m t) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      rw [factorialCriticalPrimeHarmonicTail_mean hm ht]
      field_simp
  unfold generalCriticalPrimeContinuousRealKernel
  rw [tsum_congr hterm, hsJ.tsum_sub (hsD.mul_left (1 / 2)), tsum_mul_left]

/-- Uniform lower bound on the `m = 2` harmonic tail on `[0, 1]`:
for `t ∈ [0, 1]`, `u = 2 + t ∈ [2, 3]` has `cos(2π u / 12) ≤ cos(π/3) = 1/2` and `u^{-2} ≥ 1/9`,
so `factorialCriticalPrimeHarmonicTail 2 t ≥ factorialCriticalPrimeKernelWeight (2 + t) ≥ 1/18`. -/
theorem one_div_eighteen_le_factorialCriticalPrimeHarmonicTail_two {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    1 / 18 ≤ factorialCriticalPrimeHarmonicTail 2 t := by
  set u := ((2 : ℕ) : ℝ) + t
  have hu2 : 2 ≤ u := by dsimp [u]; linarith [ht.1]
  have hu3 : u ≤ 3 := by dsimp [u]; linarith [ht.2]
  have hu0 : 0 < u := by linarith
  have hcos : Real.cos (2 * Real.pi * u / 12) ≤ 1 / 2 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hle : Real.pi / 3 ≤ 2 * Real.pi * u / 12 := by nlinarith
    have hhi : 2 * Real.pi * u / 12 ≤ Real.pi := by nlinarith
    have hanti := Real.strictAntiOn_cos.antitoneOn
      (show Real.pi / 3 ∈ Icc 0 Real.pi from ⟨by positivity, by linarith⟩)
      (show 2 * Real.pi * u / 12 ∈ Icc 0 Real.pi from ⟨by positivity, hhi⟩) hle
    rwa [Real.cos_pi_div_three] at hanti
  have hker : 1 / 18 ≤ factorialCriticalPrimeKernelWeight u := by
    unfold factorialCriticalPrimeKernelWeight
    rw [Real.rpow_neg hu0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hu_sq : (u ^ 2)⁻¹ ≥ 1 / 9 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h1m : 1 / 2 ≤ 1 - Real.cos (2 * Real.pi * u / 12) := by linarith
    calc (1 / 18 : ℝ) = (1 / 9) * (1 / 2) := by norm_num
      _ ≤ (u ^ 2)⁻¹ * (1 - Real.cos (2 * Real.pi * u / 12)) :=
          mul_le_mul hu_sq h1m (by norm_num) (by positivity)
  have hs : Summable fun j : ℕ => factorialCriticalPrimeKernelWeight (((j + 2 : ℕ) : ℝ) + t) := by
    have h1 : ∀ j : ℕ, factorialCriticalPrimeKernelWeight (((j + 2 : ℕ) : ℝ) + t) =
        criticalBandWeight (t + ((j + 2 : ℕ) : ℝ)) := fun j => by
      have : (0 : ℝ) < ((j + 2 : ℕ) : ℝ) + t := by positivity
      rw [factorialCriticalPrimeKernelWeight_eq_band this, add_comm]
    refine ((summable_nat_add_iff 2).mpr (summable_criticalBandWeight_nat t)).congr fun j => ?_
    rw [h1]
  have hle_tsum : factorialCriticalPrimeKernelWeight u ≤
      factorialCriticalPrimeHarmonicTail 2 t := by
    unfold factorialCriticalPrimeHarmonicTail
    have := hs.le_tsum 0 fun j _ =>
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (sub_nonneg.mpr (Real.cos_le_one _))
    simpa [u] using this
  exact hker.trans hle_tsum

/-- **Strictly Positive-Definite Cell Kernels (`R_χ > 0` — Prime Penalty Regime).**
Whenever `A_χ(m) ≥ 0` for all `m` and `A_χ(2) > 0` (which holds for every bounded multiplier with
`χ(1) > 0, χ(2) > 0` and `A_χ(m) ≥ 0`, including all nonnegative multipliers such as the 1-scale
Bernoulli kernel and all higher-order positive filters `w_k = c_k / k^p` with `c_k ≥ 0, c_1, c_2 > 0`),
the cell kernel is strictly positive on `[0, 1]`:
`R_χ(t) ≥ A_χ(2) / 144 > 0`, and the asymptotic prime form is strictly positive definite:
`(4 / π⁴) ∫_0^1 R_χ(t) Q_{S,b}(t) dt ≥ (A_χ(2) / (36 π⁴)) ∑_{j ∈ S} b_j²`. -/
theorem generalCriticalPrimeContinuousRealKernel_pos_of_nonneg_charge
    {χ : ℕ → ℝ} {C_χ : ℝ} (hC : 0 ≤ C_χ) (hχ : ∀ k, |χ k| ≤ C_χ)
    (hnonneg : ∀ m, 0 ≤ generalCriticalPrimeHarmonicCharge χ m) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      generalCriticalPrimeHarmonicCharge χ 2 / 144 ≤
        generalCriticalPrimeContinuousRealKernel χ t := by
  intro t ht
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hcs := summable_abs_generalCriticalPrimeHarmonicCharge_div_cube hC hχ
  have hs : Summable fun m : ℕ => (generalCriticalPrimeHarmonicCharge χ m / (m : ℝ) ^ 3) *
      ((factorialCriticalPrimeHarmonicTail m t + factorialCriticalPrimeHarmonicTail m (1 - t)) / 2) := by
    refine (hcs.mul_right (Real.pi ^ 2 / 6)).of_norm_bounded fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have ht1 := factorialCriticalPrimeHarmonicTail_nonneg m ht.1
      have ht2 := factorialCriticalPrimeHarmonicTail_nonneg m ht'.1
      have hub1 := factorialCriticalPrimeHarmonicTail_le hm ht
      have hub2 := factorialCriticalPrimeHarmonicTail_le hm ht'
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast,
        abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (abs_nonneg _) (by positivity))
  have hterm_nonneg (m : ℕ) : 0 ≤ (generalCriticalPrimeHarmonicCharge χ m / (m : ℝ) ^ 3) *
      ((factorialCriticalPrimeHarmonicTail m t + factorialCriticalPrimeHarmonicTail m (1 - t)) / 2) := by
    refine mul_nonneg (div_nonneg (hnonneg m) (by positivity)) ?_
    have := factorialCriticalPrimeHarmonicTail_nonneg m ht.1
    have := factorialCriticalPrimeHarmonicTail_nonneg m ht'.1
    linarith
  unfold generalCriticalPrimeContinuousRealKernel
  have hle2 := hs.le_tsum 2 fun m _ => hterm_nonneg m
  have h2_lo1 := one_div_eighteen_le_factorialCriticalPrimeHarmonicTail_two ht
  have h2_lo2 := one_div_eighteen_le_factorialCriticalPrimeHarmonicTail_two ht'
  have h2_mean : 1 / 18 ≤
      (factorialCriticalPrimeHarmonicTail 2 t + factorialCriticalPrimeHarmonicTail 2 (1 - t)) / 2 := by
    linarith
  have hA2 := hnonneg 2
  calc generalCriticalPrimeHarmonicCharge χ 2 / 144
      = (generalCriticalPrimeHarmonicCharge χ 2 / ((2 : ℕ) : ℝ) ^ 3) * (1 / 18) := by
          push_cast; ring
    _ ≤ (generalCriticalPrimeHarmonicCharge χ 2 / ((2 : ℕ) : ℝ) ^ 3) *
        ((factorialCriticalPrimeHarmonicTail 2 t + factorialCriticalPrimeHarmonicTail 2 (1 - t)) / 2) :=
          mul_le_mul_of_nonneg_left h2_mean (div_nonneg hA2 (by positivity))
    _ ≤ _ := hle2

/-- **Uniqueness of Base `q = 2` Among `q`-Adic Sign-Flip Stencils.**
For every `q ≥ 3`, the `q`-adic 3-scale sign-flip stencil on `{1, q, q²}` has `χ_q(1) = 1` and
`χ_q(2) = 1`, hence strictly positive harmonic-2 charge `A_{χ_q}(2) = +2 log 2 > 0` (whereas
for `q = 2`, `A_{χ_2}(2) = -2 log 2 < 0`), and `A_{χ_q}(m) = ∑_{r ∣ m} r Λ(r) ≥ 0` for all
`m` not divisible by `q`. -/
theorem qAdicSignFlip_harmonicCharge_two_pos_of_three_le {q : ℕ} (hq : 3 ≤ q) :
    generalCriticalPrimeHarmonicCharge (qAdicSignFlipChi q) 2 = 2 * Real.log 2 ∧
    0 < generalCriticalPrimeHarmonicCharge (qAdicSignFlipChi q) 2 ∧
    (∀ m : ℕ, ¬ (q ∣ m) →
      generalCriticalPrimeHarmonicCharge (qAdicSignFlipChi q) m =
        ∑ r ∈ m.divisors, (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) ∧
      0 ≤ generalCriticalPrimeHarmonicCharge (qAdicSignFlipChi q) m) := by
  have hq2 : 2 ≤ q := by omega
  have hchi1 : qAdicSignFlipChi q 1 = 1 := qAdicSignFlipChi_one hq2
  have hchi2 : qAdicSignFlipChi q 2 = 1 := by
    unfold qAdicSignFlipChi
    have h1 : ¬ (q ∣ 2) := fun h => by have := Nat.le_of_dvd two_pos h; omega
    have h2 : ¬ (q ^ 2 ∣ 2) := fun h => by
      have := Nat.le_of_dvd two_pos h
      have : 9 ≤ q ^ 2 := by nlinarith
      omega
    simp [h1, h2]
  have hA2 : generalCriticalPrimeHarmonicCharge (qAdicSignFlipChi q) 2 = 2 * Real.log 2 := by
    rw [generalCriticalPrimeHarmonicCharge_two, hchi1, hchi2]; ring
  refine ⟨hA2, ?_, fun m hm => ?_⟩
  · rw [hA2]; exact mul_pos zero_lt_two (Real.log_pos one_lt_two)
  · have hchim : qAdicSignFlipChi q m = 1 := by
      unfold qAdicSignFlipChi
      have h2 : ¬ (q ^ 2 ∣ m) := fun h => hm (dvd_trans ⟨q, sq q⟩ h)
      simp [hm, h2]
    have hsum : generalCriticalPrimeHarmonicCharge (qAdicSignFlipChi q) m =
        ∑ r ∈ m.divisors, (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) := by
      unfold generalCriticalPrimeHarmonicCharge
      rw [hchim, one_mul]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hdvd : m / r ∣ m := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hr)
      have hnot1 : ¬ (q ∣ m / r) := fun h => hm (dvd_trans h hdvd)
      have hnot2 : ¬ (q ^ 2 ∣ m / r) := fun h => hnot1 (dvd_trans ⟨q, sq q⟩ h)
      have hchir : qAdicSignFlipChi q (m / r) = 1 := by
        unfold qAdicSignFlipChi; simp [hnot1, hnot2]
      rw [hchir, mul_one]
    refine ⟨hsum, ?_⟩
    rw [hsum]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (Nat.cast_nonneg r) ArithmeticFunction.vonMangoldt_nonneg

/-- **Strictly Negative-Definite Cell Kernels (`R_χ < 0` — Prime Subsidy Regime Beyond Dyadic).**
For any bounded multiplier `χ : ℕ → ℝ` and margin `μ > 0` satisfying
`(π² / 6) ∑_{m = 0}^∞ |A_χ(m) - A_{dyadic}(m)| / m³ ≤ 1 / 7000 - μ`,
the cell kernel `generalCriticalPrimeContinuousRealKernel χ t` is uniformly bounded above by
`-μ < 0` across all `t ∈ [0, 1]`, and the asymptotic prime form is strictly negative definite:
`(4 / π⁴) ∫_0^1 R_χ(t) Q_{S,b}(t) dt ≤ -(4 μ / π⁴) ∑_{j ∈ S} b_j²`. -/
theorem generalCriticalPrimeContinuousRealKernel_neg_of_charge_perturbation
    {χ : ℕ → ℝ} {C_χ μ : ℝ} (hC : 0 ≤ C_χ) (hχ : ∀ k, |χ k| ≤ C_χ)
    (hpert : (Real.pi ^ 2 / 6) *
      (∑' m : ℕ, |generalCriticalPrimeHarmonicCharge χ m -
        factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3) ≤ 1 / 7000 - μ) :
    ∀ t ∈ Icc (0 : ℝ) 1, generalCriticalPrimeContinuousRealKernel χ t ≤ -μ := by
  intro t ht
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hdyad_le := factorialCriticalPrimeContinuousRealKernel_le ht
  rw [← generalCriticalPrimeContinuousRealKernel_dyadic_eq ht] at hdyad_le
  set M_t : ℕ → ℝ := fun m =>
    (factorialCriticalPrimeHarmonicTail m t + factorialCriticalPrimeHarmonicTail m (1 - t)) / 2
  have hM_nonneg (m : ℕ) : 0 ≤ M_t m := by
    dsimp [M_t]
    have := factorialCriticalPrimeHarmonicTail_nonneg m ht.1
    have := factorialCriticalPrimeHarmonicTail_nonneg m ht'.1
    linarith
  have hM_le {m : ℕ} (hm : 0 < m) : M_t m ≤ Real.pi ^ 2 / 6 := by
    dsimp [M_t]
    have h1 := factorialCriticalPrimeHarmonicTail_le hm ht
    have h2 := factorialCriticalPrimeHarmonicTail_le hm ht'
    linarith
  have hcs1 := summable_abs_generalCriticalPrimeHarmonicCharge_div_cube hC hχ
  have hcs2 := summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube
  have hcs_diff : Summable fun m : ℕ =>
      |generalCriticalPrimeHarmonicCharge χ m - factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 := by
    refine (hcs1.add hcs2).of_nonneg_of_le (fun m => div_nonneg (abs_nonneg _) (by positivity))
      fun m => ?_
    rw [← add_div]
    exact div_le_div_of_nonneg_right (abs_sub _ _) (by positivity)
  have hs1 : Summable fun m : ℕ =>
      (generalCriticalPrimeHarmonicCharge χ m / (m : ℝ) ^ 3) * M_t m := by
    refine (hcs1.mul_right (Real.pi ^ 2 / 6)).of_norm_bounded fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg (hM_nonneg m)]
      exact mul_le_mul_of_nonneg_left (hM_le hm) (div_nonneg (abs_nonneg _) (by positivity))
  have hs2 : Summable fun m : ℕ =>
      (factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3) * M_t m := by
    refine (hcs2.mul_right (Real.pi ^ 2 / 6)).of_norm_bounded fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg (hM_nonneg m)]
      exact mul_le_mul_of_nonneg_left (hM_le hm) (div_nonneg (abs_nonneg _) (by positivity))
  have hdiff_bound (m : ℕ) :
      |(generalCriticalPrimeHarmonicCharge χ m / (m : ℝ) ^ 3) * M_t m -
        (factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3) * M_t m| ≤
      (Real.pi ^ 2 / 6) *
        (|generalCriticalPrimeHarmonicCharge χ m - factorialCriticalPrimeHarmonicCharge m| /
          (m : ℝ) ^ 3) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [← sub_mul, ← sub_div, abs_mul, abs_div, abs_pow, Nat.abs_cast,
        abs_of_nonneg (hM_nonneg m), mul_comm]
      exact mul_le_mul_of_nonneg_right (hM_le hm) (div_nonneg (abs_nonneg _) (by positivity))
  have hs_sub : Summable fun m : ℕ =>
      ‖(generalCriticalPrimeHarmonicCharge χ m / (m : ℝ) ^ 3) * M_t m -
        (factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3) * M_t m‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun m => by rw [Real.norm_eq_abs]; exact hdiff_bound m)
      (hcs_diff.mul_left (Real.pi ^ 2 / 6))
  have hsub_le : generalCriticalPrimeContinuousRealKernel χ t -
      generalCriticalPrimeContinuousRealKernel dyadicHarmonicChi t ≤
      (Real.pi ^ 2 / 6) * ∑' m : ℕ,
        |generalCriticalPrimeHarmonicCharge χ m - factorialCriticalPrimeHarmonicCharge m| /
          (m : ℝ) ^ 3 := by
    unfold generalCriticalPrimeContinuousRealKernel
    rw [generalCriticalPrimeHarmonicCharge_dyadic_eq, ← hs1.tsum_sub hs2]
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm hs_sub).trans ?_
    exact (hs_sub.tsum_le_tsum (fun m => by rw [Real.norm_eq_abs]; exact hdiff_bound m)
      (hcs_diff.mul_left (Real.pi ^ 2 / 6))).trans_eq tsum_mul_left
  linarith

/-- Perturbed multi-scale harmonic multiplier `χ_{d, ε}(k) = dyadicHarmonicChi k + ε [d ∣ k]`
associated to adding a fourth divisor scale `d ≥ 3` to `{1, 2, 4}` (or perturbing the `d`-th
harmonic family). -/
def perturbedMultiScaleChi (d : ℕ) (ε : ℝ) (k : ℕ) : ℝ :=
  dyadicHarmonicChi k + ε * (if d ∣ k then 1 else 0)

/-- **Infinite Family of Non-Dyadic Multi-Scale Multipliers with Strictly Negative-Definite Cell Kernels.**
For every scale `d ≥ 3`, there exists `ε > 0` such that `χ = perturbedMultiScaleChi d ε`
differs from `dyadicHarmonicChi` at `k = d`, generates an `AdmissibleHarmonicWeight` sequence
`w_k = χ(k) / k²` with `τ = 4/5 < 1`, and has a strictly negative-definite continuous cell kernel
`generalCriticalPrimeContinuousRealKernel χ t ≤ -1 / 14000 < 0` across all `t ∈ [0, 1]`. -/
theorem exists_nonDyadic_stencil_negative_definite_cellKernel (d : ℕ) (hd : 3 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧
      perturbedMultiScaleChi d ε d ≠ dyadicHarmonicChi d ∧
      AdmissibleHarmonicWeight
        (fun k => if k = 0 then 0 else perturbedMultiScaleChi d ε k / (k : ℝ) ^ 2)
        (1 + ε) (4 / 5) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        generalCriticalPrimeContinuousRealKernel (perturbedMultiScaleChi d ε) t ≤ -1 / 14000 := by
  set S_log := ∑' m : ℕ, envelopeLogMajorant (3 / 2) m
  have hS_summ := summable_envelopeLogMajorant_of_half_lt (by norm_num : (1 : ℝ) / 2 < 3 / 2)
  have hS_nonneg : 0 ≤ S_log := tsum_nonneg fun m => by
    unfold envelopeLogMajorant
    split_ifs with hm
    · have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      exact div_nonneg (Real.log_nonneg this) (by positivity)
    · exact le_rfl
  set K_pert := (Real.pi ^ 2 / 6) * (3 * (S_log + 1))
  have hK_pos : 0 < K_pert := by positivity
  set ε := min (1 / 40) ((1 / 14000) / K_pert)
  have hε_pos : 0 < ε := lt_min (by norm_num) (div_pos (by norm_num) hK_pos)
  have hε_le1 : ε ≤ 1 / 40 := min_le_left _ _
  have hε_le2 : ε * K_pert ≤ 1 / 14000 := by
    have := min_le_right (1 / 40) ((1 / 14000) / K_pert)
    exact (le_div_iff₀ hK_pos).mp this
  refine ⟨ε, hε_pos, ?_, ?_, ?_⟩
  · unfold perturbedMultiScaleChi
    simp [dvd_refl d, hε_pos.ne']
  · refine
      { w_zero := by simp
        w_one := by
          have hd1 : ¬ (d ∣ 1) := fun h => by have := Nat.le_of_dvd one_pos h; omega
          have hchi1 : dyadicHarmonicChi 1 = 1 := by decide
          simp [perturbedMultiScaleChi, hd1, hchi1]
        C_pos := by linarith
        abs_w_le := fun k => by
          split_ifs with hk
          · simp; positivity
          · rw [abs_div, abs_of_nonneg (sq_nonneg _)]
            refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
            unfold perturbedMultiScaleChi
            refine (abs_add_le _ _).trans (add_le_add (abs_dyadicHarmonicChi_le_one k) ?_)
            rw [abs_mul, abs_of_pos hε_pos]
            split_ifs <;> simp [hε_pos.le]
        τ_nonneg := by norm_num
        τ_lt_one := by norm_num
        tsum_tail_le := by
          set w_pert : ℕ → ℝ := fun k =>
            if k = 0 then 0 else perturbedMultiScaleChi d ε k / (k : ℝ) ^ 2
          have hbd (k : ℕ) : |w_pert (k + 2)| ≤
              |dyadicHarmonicWeight (k + 2)| + ε * (1 / ((k + 2 : ℕ) : ℝ) ^ 2) := by
            simp only [w_pert, dyadicHarmonicWeight, show k + 2 ≠ 0 by omega, if_false,
              perturbedMultiScaleChi]
            rw [add_div]
            refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [abs_div, abs_mul, abs_of_pos hε_pos, abs_of_nonneg (sq_nonneg _)]
            split_ifs <;> simp [div_eq_mul_inv]
          have hs_dyad : Summable fun k : ℕ => |dyadicHarmonicWeight (k + 2)| :=
            (summable_nat_add_iff 2).mpr summable_abs_dyadicHarmonicWeight
          have hs_z2 : Summable fun k : ℕ => 1 / ((k + 2 : ℕ) : ℝ) ^ 2 :=
            (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
          have hs_pert : Summable fun k : ℕ => |w_pert (k + 2)| :=
            Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hbd
              (hs_dyad.add (hs_z2.mul_left ε))
          have h1 : (∑' k : ℕ, |w_pert (k + 2)|) ≤
              (∑' k : ℕ, |dyadicHarmonicWeight (k + 2)|) +
                ε * ∑' k : ℕ, 1 / ((k + 2 : ℕ) : ℝ) ^ 2 := by
            calc (∑' k : ℕ, |w_pert (k + 2)|)
                ≤ ∑' k : ℕ, (|dyadicHarmonicWeight (k + 2)| + ε * (1 / ((k + 2 : ℕ) : ℝ) ^ 2)) :=
                  hs_pert.tsum_le_tsum hbd (hs_dyad.add (hs_z2.mul_left ε))
              _ = _ := by rw [hs_dyad.tsum_add (hs_z2.mul_left ε), tsum_mul_left]
          have hdyad_tail := tsum_abs_dyadicHarmonicWeight_tail_le
          have hz2_le : (∑' k : ℕ, 1 / ((k + 2 : ℕ) : ℝ) ^ 2) ≤ 2 := by
            have hz : Summable fun k : ℕ => 1 / (k : ℝ) ^ 2 :=
              Real.summable_one_div_nat_pow.mpr one_lt_two
            have hle : (∑' k : ℕ, 1 / ((k + 2 : ℕ) : ℝ) ^ 2) ≤ ∑' k : ℕ, 1 / (k : ℝ) ^ 2 := by
              rw [← hz.sum_add_tsum_nat_add 2]
              have : 0 ≤ ∑ i ∈ Finset.range 2, 1 / (i : ℝ) ^ 2 :=
                Finset.sum_nonneg fun _ _ => by positivity
              linarith
            exact hle.trans tsum_one_div_nat_sq_le_two
          nlinarith }
  · set χ := perturbedMultiScaleChi d ε
    have hχ_bd (k : ℕ) : |χ k| ≤ 1 + ε := by
      unfold χ perturbedMultiScaleChi
      refine (abs_add_le _ _).trans (add_le_add (abs_dyadicHarmonicChi_le_one k) ?_)
      rw [abs_mul, abs_of_pos hε_pos]
      split_ifs <;> simp [hε_pos.le]
    have hdiff_chi (k : ℕ) : |χ k - dyadicHarmonicChi k| ≤ ε := by
      unfold χ perturbedMultiScaleChi
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hε_pos]
      split_ifs <;> simp [hε_pos.le]
    have hcharge_diff (m : ℕ) :
        |generalCriticalPrimeHarmonicCharge χ m - factorialCriticalPrimeHarmonicCharge m| /
          (m : ℝ) ^ 3 ≤
          (3 * ε) * envelopeLogMajorant (3 / 2) m := by
      by_cases hm : 2 ≤ m
      · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
        have h1 : generalCriticalPrimeHarmonicCharge χ m - factorialCriticalPrimeHarmonicCharge m =
            (χ m - dyadicHarmonicChi m) *
              (∑ r ∈ m.divisors, (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * χ (m / r)) +
            dyadicHarmonicChi m *
              (∑ r ∈ m.divisors, (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) *
                (χ (m / r) - dyadicHarmonicChi (m / r))) := by
          unfold generalCriticalPrimeHarmonicCharge factorialCriticalPrimeHarmonicCharge
          rw [← Finset.sum_sub_distrib]
          have : (∑ x ∈ m.divisors, ((x : ℝ) * (ArithmeticFunction.vonMangoldt x : ℝ) * χ (m / x) -
              (x : ℝ) * (ArithmeticFunction.vonMangoldt x : ℝ) * dyadicHarmonicChi (m / x))) =
              ∑ x ∈ m.divisors, (x : ℝ) * (ArithmeticFunction.vonMangoldt x : ℝ) *
                (χ (m / x) - dyadicHarmonicChi (m / x)) :=
            Finset.sum_congr rfl fun x _ => by ring
          rw [this]; ring
        have hsum1 : |∑ r ∈ m.divisors, (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * χ (m / r)| ≤
            (1 + ε) * ((m : ℝ) * Real.log m) := by
          calc |∑ r ∈ m.divisors, (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * χ (m / r)|
              ≤ ∑ r ∈ m.divisors, |(r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * χ (m / r)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ r ∈ m.divisors, (1 + ε) * ((m : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ)) := by
                refine Finset.sum_le_sum fun r hr => ?_
                have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt r : ℝ) :=
                  ArithmeticFunction.vonMangoldt_nonneg
                have hrm : (r : ℝ) ≤ m := by exact_mod_cast Nat.divisor_le hr
                rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg r) hΛ)]
                calc (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * |χ (m / r)|
                    ≤ (m : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * (1 + ε) :=
                      mul_le_mul (mul_le_mul_of_nonneg_right hrm hΛ) (hχ_bd _)
                        (abs_nonneg _) (by positivity)
                  _ = (1 + ε) * ((m : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ)) := by ring
            _ = (1 + ε) * ((m : ℝ) * Real.log m) := by
                rw [← Finset.mul_sum, ← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
        have hsum2 : |∑ r ∈ m.divisors, (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) *
            (χ (m / r) - dyadicHarmonicChi (m / r))| ≤
            ε * ((m : ℝ) * Real.log m) := by
          calc |∑ r ∈ m.divisors, (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) *
                (χ (m / r) - dyadicHarmonicChi (m / r))|
              ≤ ∑ r ∈ m.divisors, |(r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) *
                (χ (m / r) - dyadicHarmonicChi (m / r))| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ r ∈ m.divisors, ε * ((m : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ)) := by
                refine Finset.sum_le_sum fun r hr => ?_
                have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt r : ℝ) :=
                  ArithmeticFunction.vonMangoldt_nonneg
                have hrm : (r : ℝ) ≤ m := by exact_mod_cast Nat.divisor_le hr
                rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg r) hΛ)]
                calc (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) *
                      |χ (m / r) - dyadicHarmonicChi (m / r)|
                    ≤ (m : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * ε :=
                      mul_le_mul (mul_le_mul_of_nonneg_right hrm hΛ) (hdiff_chi _)
                        (abs_nonneg _) (by positivity)
                  _ = ε * ((m : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ)) := by ring
            _ = ε * ((m : ℝ) * Real.log m) := by
                rw [← Finset.mul_sum, ← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
        have htot : |generalCriticalPrimeHarmonicCharge χ m - factorialCriticalPrimeHarmonicCharge m| ≤
            (3 * ε) * ((m : ℝ) * Real.log m) := by
          rw [h1]
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
          have ha := mul_le_mul (hdiff_chi m) hsum1 (abs_nonneg _) hε_pos.le
          have hb := mul_le_mul (abs_dyadicHarmonicChi_le_one m) hsum2 (abs_nonneg _) zero_le_one
          have hlog0 : 0 ≤ (m : ℝ) * Real.log m :=
            mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega)))
          nlinarith
        calc |generalCriticalPrimeHarmonicCharge χ m - factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3
            ≤ ((3 * ε) * ((m : ℝ) * Real.log m)) / (m : ℝ) ^ 3 :=
              div_le_div_of_nonneg_right htot (by positivity)
          _ = (3 * ε) * (Real.log m / (m : ℝ) ^ 2) := by field_simp [hm0]
          _ = (3 * ε) * envelopeLogMajorant (3 / 2) m := by
              simp only [envelopeLogMajorant, if_pos hm, show (3 / 2 : ℝ) + 1 / 2 = 2 by norm_num,
                Real.rpow_two]
      · have hm01 : m = 0 ∨ m = 1 := by omega
        rcases hm01 with rfl | rfl
        · simp [envelopeLogMajorant]
        · have hA1 : factorialCriticalPrimeHarmonicCharge 1 = 0 :=
            (factorialCriticalPrimeHarmonicCharge_sign 1).2.1.mpr (Or.inl rfl)
          simp [envelopeLogMajorant, generalCriticalPrimeHarmonicCharge_one, hA1]
    have hs_diff : Summable fun m : ℕ =>
        |generalCriticalPrimeHarmonicCharge χ m - factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 :=
      Summable.of_nonneg_of_le (fun m => div_nonneg (abs_nonneg _) (by positivity))
        hcharge_diff (hS_summ.mul_left (3 * ε))
    have htsum_le : (∑' m : ℕ,
        |generalCriticalPrimeHarmonicCharge χ m - factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3) ≤
        (3 * ε) * S_log :=
      (hs_diff.tsum_le_tsum hcharge_diff (hS_summ.mul_left (3 * ε))).trans_eq tsum_mul_left
    have hpert : (Real.pi ^ 2 / 6) *
        (∑' m : ℕ, |generalCriticalPrimeHarmonicCharge χ m -
          factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3) ≤
        1 / 7000 - 1 / 14000 := by
      have h1 : (Real.pi ^ 2 / 6) *
          (∑' m : ℕ, |generalCriticalPrimeHarmonicCharge χ m -
            factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3) ≤
          (Real.pi ^ 2 / 6) * ((3 * ε) * S_log) :=
        mul_le_mul_of_nonneg_left htsum_le (by positivity)
      have h2 : (Real.pi ^ 2 / 6) * ((3 * ε) * S_log) ≤ ε * K_pert := by
        dsimp [K_pert]
        have : 0 ≤ (Real.pi ^ 2 / 6) * (3 * ε) := by positivity
        nlinarith
      linarith
    exact generalCriticalPrimeContinuousRealKernel_neg_of_charge_perturbation
      (by linarith) hχ_bd hpert

end GaloisForLFunctions.ArithmeticPositivityTheory
