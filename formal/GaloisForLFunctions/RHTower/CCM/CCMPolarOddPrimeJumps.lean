import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarParitySourceProfile

/-!
# Positive spatial prime jumps of the actual odd Weil pole source

Fix an aperture `a > 0` and write `O_a(x) = Re K_a^{odd}(x)` for the reflection-odd prime–Gamma pole
source (`ccmPolarParityBoundaryProfile a (−1)`).  Put `E = e^{a/2}`, `F = e^{−a/2}`.

**Decomposition** (`ccmPolarOddSource_eq_core_add_atoms`).  On the open aperture
`O_a = G_a + Σ_{2 ≤ n ≤ e^{2a}} A_{a,n}`, where the core
`G_a(x) = e^{x/2}(B(a−x, a+x) + e^{a−x} + a + x) − e^{−x/2}(B(a+x, a−x) + e^{a+x} + a − x)`
is continuous (`continuousOn_ccmPolarOddSourceCore`) and each visible von Mangoldt atom
`A_{a,n}(x) = −Λ(n)[(e^{x/2} − e^{−x/2}/n)1_{log n ≤ a−x} + (e^{x/2}/n − e^{−x/2})1_{log n ≤ a+x}]`
is a two-step function.  The exponential main terms `e^{x/2}e^{a−x} − e^{−x/2}e^{a+x} = −2e^a sinh(x/2)`
do not cancel; they are continuous and sit in the core.

**Jump law** (`ccmPolarOddSource_jump`).  At every interior point `x` both one-sided limits of `O_a`
exist and their difference is
`O_a(x⁺) − O_a(x⁻) = (E − F) Σ_{2 ≤ n ≤ e^{2a}} Λ(n) n^{−1/2} (1_{x = a − log n} + 1_{x = log n − a}) ≥ 0`.
Each prime power contributes the same positive weight at its two reflected sites; coinciding sites
add with multiplicity.  So the odd source can only jump upward, and every sign loss of the odd source
happens in its continuous drift between prime sites.
-/

open Complex MeasureTheory Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RHTower

/-- The visible prime powers `2 ≤ n ≤ e^{2a}` of the aperture. -/
def oddVisiblePrimes (a : SuzukiPositiveAperture) : Finset ℕ :=
  Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊

/-- Continuous part of the odd physical source on the open aperture. -/
def ccmPolarOddSourceCore (a : SuzukiPositiveAperture) (x : ℝ) : ℝ :=
  Real.exp (x / 2) * (ccmGammaPolarBoundary (a.1 - x) (a.1 + x) + Real.exp (a.1 - x) + (a.1 + x)) -
  Real.exp (-x / 2) * (ccmGammaPolarBoundary (a.1 + x) (a.1 - x) + Real.exp (a.1 + x) + (a.1 - x))

/-- A single visible von Mangoldt atom in the odd source profile. -/
def ccmPolarOddSourcePrimeAtom (a : SuzukiPositiveAperture) (n : ℕ) (x : ℝ) : ℝ :=
  -ArithmeticFunction.vonMangoldt n *
    ((Real.exp (x / 2) - Real.exp (-x / 2) / n) *
      (if Real.log n ≤ a.1 - x then 1 else 0) +
     (Real.exp (x / 2) / n - Real.exp (-x / 2)) *
      (if Real.log n ≤ a.1 + x then 1 else 0))

private theorem sum_log_cutoff (a : SuzukiPositiveAperture) (f : ℕ → ℝ)
    {y : ℝ} (hy : y ≤ 2 * a.1) :
    (∑ n ∈ oddVisiblePrimes a, if Real.log n ≤ y then f n else 0) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp y⌋₊, f n := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  by_cases hn : 2 ≤ n
  · have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have heq : Real.log n ≤ y ↔ n ≤ ⌊Real.exp y⌋₊ :=
      (Real.log_le_iff_le_exp hnR).trans (Nat.le_floor_iff (Real.exp_pos y).le).symm
    have hfloor := Nat.floor_mono (Real.exp_le_exp.mpr hy)
    rw [heq]
    simp only [oddVisiblePrimes, Finset.mem_Icc] at *
    omega
  · simp [hn, oddVisiblePrimes]

private theorem psi_eq_sum_from_two (X : ℝ) :
    Chebyshev.psi X = ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc]
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨Nat.zero_le _, hn.2⟩
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl <;> simp

/-- An atom split into its four indicator channels. -/
private theorem primeAtom_eq (a : SuzukiPositiveAperture) (n : ℕ) (x : ℝ) :
    ccmPolarOddSourcePrimeAtom a n x =
      -Real.exp (x / 2) * (if Real.log n ≤ a.1 - x then ArithmeticFunction.vonMangoldt n else 0) +
      Real.exp (-x / 2) *
        (if Real.log n ≤ a.1 - x then ArithmeticFunction.vonMangoldt n / n else 0) -
      Real.exp (x / 2) *
        (if Real.log n ≤ a.1 + x then ArithmeticFunction.vonMangoldt n / n else 0) +
      Real.exp (-x / 2) * (if Real.log n ≤ a.1 + x then ArithmeticFunction.vonMangoldt n else 0) := by
  unfold ccmPolarOddSourcePrimeAtom
  split_ifs <;> ring

/-- **The odd source is its continuous core plus all finite visible prime atoms.** -/
theorem ccmPolarOddSource_eq_core_add_atoms (a : SuzukiPositiveAperture) {x : ℝ}
    (hx : x ∈ Ioo (-a.1) a.1) :
    (ccmPolarParityBoundaryProfile a (-1) x).re =
      ccmPolarOddSourceCore a x +
        ∑ n ∈ oddVisiblePrimes a, ccmPolarOddSourcePrimeAtom a n x := by
  classical
  have hpR : Chebyshev.psi (Real.exp (a.1 - x)) =
      ∑ n ∈ oddVisiblePrimes a,
        if Real.log n ≤ a.1 - x then ArithmeticFunction.vonMangoldt n else 0 := by
    rw [psi_eq_sum_from_two]
    exact (sum_log_cutoff a _ (by linarith [hx.1])).symm
  have hpL : Chebyshev.psi (Real.exp (a.1 + x)) =
      ∑ n ∈ oddVisiblePrimes a,
        if Real.log n ≤ a.1 + x then ArithmeticFunction.vonMangoldt n else 0 := by
    rw [psi_eq_sum_from_two]
    exact (sum_log_cutoff a _ (by linarith [hx.2])).symm
  have hsR : ccmReciprocalMangoldtCumulative (Real.exp (a.1 - x)) =
      ∑ n ∈ oddVisiblePrimes a,
        if Real.log n ≤ a.1 - x then ArithmeticFunction.vonMangoldt n / n else 0 := by
    unfold ccmReciprocalMangoldtCumulative
    exact (sum_log_cutoff a _ (by linarith [hx.1])).symm
  have hsL : ccmReciprocalMangoldtCumulative (Real.exp (a.1 + x)) =
      ∑ n ∈ oddVisiblePrimes a,
        if Real.log n ≤ a.1 + x then ArithmeticFunction.vonMangoldt n / n else 0 := by
    unfold ccmReciprocalMangoldtCumulative
    exact (sum_log_cutoff a _ (by linarith [hx.2])).symm
  have hre : (ccmPolarParityBoundaryProfile a (-1) x).re =
      (ccmPolarBoundaryArithmeticProfile a x).re -
        (ccmPolarBoundaryArithmeticProfile a (-x)).re := by
    unfold ccmPolarParityBoundaryProfile
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    ring
  have hatoms : ∑ n ∈ oddVisiblePrimes a, ccmPolarOddSourcePrimeAtom a n x =
      -Real.exp (x / 2) * Chebyshev.psi (Real.exp (a.1 - x)) +
      Real.exp (-x / 2) * ccmReciprocalMangoldtCumulative (Real.exp (a.1 - x)) -
      Real.exp (x / 2) * ccmReciprocalMangoldtCumulative (Real.exp (a.1 + x)) +
      Real.exp (-x / 2) * Chebyshev.psi (Real.exp (a.1 + x)) := by
    rw [hpR, hpL, hsR, hsL, Finset.sum_congr rfl fun n _ => primeAtom_eq a n x]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hre, hatoms]
  unfold ccmPolarBoundaryArithmeticProfile ccmReciprocalMangoldtError ccmPolarOddSourceCore
  simp only [Complex.ofReal_re, sub_neg_eq_add]
  ring_nf

/-! ### Continuity of the core -/

private theorem continuousAt_log_one_sub_exp {g : ℝ → ℝ} (hg : Continuous g) {x : ℝ}
    (hpos : 0 < g x) : ContinuousAt (fun y => Real.log (1 - Real.exp (-g y))) x := by
  have hlt : Real.exp (-g x) < 1 := by
    have := Real.exp_lt_exp.mpr (show -g x < 0 by linarith)
    rwa [Real.exp_zero] at this
  exact ContinuousAt.log (by fun_prop) (by linarith)

/-- The core is continuous on the open aperture: both Gamma boundary arguments stay positive. -/
theorem continuousAt_ccmPolarOddSourceCore (a : SuzukiPositiveAperture) {x : ℝ}
    (hx : x ∈ Ioo (-a.1) a.1) : ContinuousAt (ccmPolarOddSourceCore a) x := by
  have hR : 0 < a.1 - x := by linarith [hx.2]
  have hL : 0 < a.1 + x := by linarith [hx.1]
  have h1 := continuousAt_log_one_sub_exp (g := fun y => 2 * (a.1 - y)) (by fun_prop) (x := x)
    (by positivity)
  have h2 := continuousAt_log_one_sub_exp (g := fun y => a.1 + y) (by fun_prop) (x := x) hL
  have h3 := continuousAt_log_one_sub_exp (g := fun y => 2 * (a.1 + y)) (by fun_prop) (x := x)
    (by positivity)
  have h4 := continuousAt_log_one_sub_exp (g := fun y => 2 * (a.1 + y)) (by fun_prop) (x := x)
    (by positivity)
  have h5 := continuousAt_log_one_sub_exp (g := fun y => a.1 - y) (by fun_prop) (x := x) hR
  have h6 := continuousAt_log_one_sub_exp (g := fun y => 2 * (a.1 - y)) (by fun_prop) (x := x)
    (by positivity)
  unfold ccmPolarOddSourceCore ccmGammaPolarBoundary
  have hE1 : ContinuousAt (fun y : ℝ => Real.exp (y / 2)) x := by fun_prop
  have hE2 : ContinuousAt (fun y : ℝ => Real.exp (-y / 2)) x := by fun_prop
  have hE3 : ContinuousAt (fun y : ℝ => Real.exp (a.1 - y)) x := by fun_prop
  have hE4 : ContinuousAt (fun y : ℝ => Real.exp (a.1 + y)) x := by fun_prop
  have hlin1 : ContinuousAt (fun y : ℝ => a.1 + y) x := by fun_prop
  have hlin2 : ContinuousAt (fun y : ℝ => a.1 - y) x := by fun_prop
  exact (hE1.mul ((((h1.const_mul (-(1 / 2))).sub h2).add (h3.const_mul (1 / 2))).add hE3
    |>.add hlin1)).sub (hE2.mul ((((h4.const_mul (-(1 / 2))).sub h5).add (h6.const_mul (1 / 2))).add
    hE4 |>.add hlin2))

/-! ### One-sided limits of the atoms -/

/-- The right limit of a prime atom at `x`. -/
def ccmPolarOddSourcePrimeAtomRight (a : SuzukiPositiveAperture) (n : ℕ) (x : ℝ) : ℝ :=
  -ArithmeticFunction.vonMangoldt n *
    ((Real.exp (x / 2) - Real.exp (-x / 2) / n) * (if x < a.1 - Real.log n then 1 else 0) +
     (Real.exp (x / 2) / n - Real.exp (-x / 2)) * (if Real.log n - a.1 ≤ x then 1 else 0))

/-- The left limit of a prime atom at `x`. -/
def ccmPolarOddSourcePrimeAtomLeft (a : SuzukiPositiveAperture) (n : ℕ) (x : ℝ) : ℝ :=
  -ArithmeticFunction.vonMangoldt n *
    ((Real.exp (x / 2) - Real.exp (-x / 2) / n) * (if x ≤ a.1 - Real.log n then 1 else 0) +
     (Real.exp (x / 2) / n - Real.exp (-x / 2)) * (if Real.log n - a.1 < x then 1 else 0))

private theorem continuous_atomShape (n : ℕ) (c₁ c₂ : ℝ) :
    Continuous fun y : ℝ => -ArithmeticFunction.vonMangoldt n *
      ((Real.exp (y / 2) - Real.exp (-y / 2) / n) * c₁ +
        (Real.exp (y / 2) / n - Real.exp (-y / 2)) * c₂) := by
  fun_prop

theorem tendsto_primeAtom_right (a : SuzukiPositiveAperture) (n : ℕ) (x : ℝ) :
    Tendsto (ccmPolarOddSourcePrimeAtom a n) (𝓝[>] x)
      (𝓝 (ccmPolarOddSourcePrimeAtomRight a n x)) := by
  have hcont := ((continuous_atomShape n (if x < a.1 - Real.log n then 1 else 0)
    (if Real.log n - a.1 ≤ x then 1 else 0)).tendsto x).mono_left (nhdsWithin_le_nhds (s := Ioi x))
  refine hcont.congr' ?_
  have h1 : ∀ᶠ y in 𝓝[>] x, (if Real.log n ≤ a.1 - y then (1 : ℝ) else 0) =
      if x < a.1 - Real.log n then 1 else 0 := by
    by_cases hx : x < a.1 - Real.log n
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx)] with y hy
      have : Real.log n ≤ a.1 - y := by have := mem_Iio.mp hy; linarith
      simp [hx, this]
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      have hy' : x < y := hy
      have : ¬ Real.log n ≤ a.1 - y := by push Not at hx ⊢; linarith
      simp [hx, this]
  have h2 : ∀ᶠ y in 𝓝[>] x, (if Real.log n ≤ a.1 + y then (1 : ℝ) else 0) =
      if Real.log n - a.1 ≤ x then 1 else 0 := by
    by_cases hx : Real.log n - a.1 ≤ x
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      have hy' : x < y := hy
      have : Real.log n ≤ a.1 + y := by linarith
      simp [hx, this]
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (not_le.mp hx))] with y hy
      have : ¬ Real.log n ≤ a.1 + y := by have := mem_Iio.mp hy; push Not; linarith
      simp [hx, this]
  filter_upwards [h1, h2] with y hy1 hy2
  unfold ccmPolarOddSourcePrimeAtom
  rw [hy1, hy2]

theorem tendsto_primeAtom_left (a : SuzukiPositiveAperture) (n : ℕ) (x : ℝ) :
    Tendsto (ccmPolarOddSourcePrimeAtom a n) (𝓝[<] x)
      (𝓝 (ccmPolarOddSourcePrimeAtomLeft a n x)) := by
  have hcont := ((continuous_atomShape n (if x ≤ a.1 - Real.log n then 1 else 0)
    (if Real.log n - a.1 < x then 1 else 0)).tendsto x).mono_left (nhdsWithin_le_nhds (s := Iio x))
  refine hcont.congr' ?_
  have h1 : ∀ᶠ y in 𝓝[<] x, (if Real.log n ≤ a.1 - y then (1 : ℝ) else 0) =
      if x ≤ a.1 - Real.log n then 1 else 0 := by
    by_cases hx : x ≤ a.1 - Real.log n
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      have hy' : y < x := hy
      have : Real.log n ≤ a.1 - y := by linarith
      simp [hx, this]
    · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (not_le.mp hx))] with y hy
      have : ¬ Real.log n ≤ a.1 - y := by have := mem_Ioi.mp hy; push Not; linarith
      simp [hx, this]
  have h2 : ∀ᶠ y in 𝓝[<] x, (if Real.log n ≤ a.1 + y then (1 : ℝ) else 0) =
      if Real.log n - a.1 < x then 1 else 0 := by
    by_cases hx : Real.log n - a.1 < x
    · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hx)] with y hy
      have : Real.log n ≤ a.1 + y := by have := mem_Ioi.mp hy; linarith
      simp [hx, this]
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      have hy' : y < x := hy
      have : ¬ Real.log n ≤ a.1 + y := by push Not at hx ⊢; linarith
      simp [hx, this]
  filter_upwards [h1, h2] with y hy1 hy2
  unfold ccmPolarOddSourcePrimeAtom
  rw [hy1, hy2]

/-! ### The jump law -/

/-- **Each prime atom jumps up by `(e^{a/2} − e^{−a/2})Λ(n)/√n` at both reflected sites.** -/
theorem primeAtomRight_sub_primeAtomLeft (a : SuzukiPositiveAperture) {n : ℕ} (hn : 1 ≤ n)
    (x : ℝ) :
    ccmPolarOddSourcePrimeAtomRight a n x - ccmPolarOddSourcePrimeAtomLeft a n x =
      (Real.exp (a.1 / 2) - Real.exp (-a.1 / 2)) *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          ((if x = a.1 - Real.log n then 1 else 0) + (if x = Real.log n - a.1 then 1 else 0))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set r : ℝ := Real.sqrt n with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hn0
  have hrr : r * r = n := Real.mul_self_sqrt hn0.le
  have hexp : Real.exp (Real.log n / 2) = r := by
    rw [hr, ← Real.log_sqrt hn0.le, Real.exp_log hr0]
  -- the two site identities
  have hsite1 : Real.exp ((a.1 - Real.log n) / 2) - Real.exp (-(a.1 - Real.log n) / 2) / n =
      (Real.exp (a.1 / 2) - Real.exp (-a.1 / 2)) / r := by
    have e1 : Real.exp ((a.1 - Real.log n) / 2) = Real.exp (a.1 / 2) / r := by
      rw [← hexp, ← Real.exp_sub]; ring_nf
    have e2 : Real.exp (-(a.1 - Real.log n) / 2) = Real.exp (-a.1 / 2) * r := by
      rw [← hexp, ← Real.exp_add]; ring_nf
    rw [e1, e2, ← hrr]
    field_simp
  have hsite2 : Real.exp (-(Real.log n - a.1) / 2) - Real.exp ((Real.log n - a.1) / 2) / n =
      (Real.exp (a.1 / 2) - Real.exp (-a.1 / 2)) / r := by
    have e1 : Real.exp (-(Real.log n - a.1) / 2) = Real.exp (a.1 / 2) / r := by
      rw [← hexp, ← Real.exp_sub]; ring_nf
    have e2 : Real.exp ((Real.log n - a.1) / 2) = Real.exp (-a.1 / 2) * r := by
      rw [← hexp, ← Real.exp_add]; ring_nf
    rw [e1, e2, ← hrr]
    field_simp
  have ind1 : (if x < a.1 - Real.log n then (1 : ℝ) else 0) =
      (if x ≤ a.1 - Real.log n then 1 else 0) - (if x = a.1 - Real.log n then 1 else 0) := by
    rcases lt_trichotomy x (a.1 - Real.log n) with h | h | h
    · simp [h, h.le, h.ne]
    · simp [h]
    · simp [not_lt.mpr h.le, not_le.mpr h, h.ne']
  have ind2 : (if Real.log n - a.1 ≤ x then (1 : ℝ) else 0) =
      (if Real.log n - a.1 < x then 1 else 0) + (if x = Real.log n - a.1 then 1 else 0) := by
    rcases lt_trichotomy x (Real.log n - a.1) with h | h | h
    · simp [h.ne, not_le.mpr h, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.le, h.ne']
  have t1 : (Real.exp (x / 2) - Real.exp (-x / 2) / n) *
      (if x = a.1 - Real.log n then (1 : ℝ) else 0) =
      (Real.exp (a.1 / 2) - Real.exp (-a.1 / 2)) / r *
        (if x = a.1 - Real.log n then 1 else 0) := by
    by_cases h : x = a.1 - Real.log n
    · simp only [if_pos h, mul_one]
      subst h
      exact hsite1
    · simp [h]
  have t2 : (Real.exp (-x / 2) - Real.exp (x / 2) / n) *
      (if x = Real.log n - a.1 then (1 : ℝ) else 0) =
      (Real.exp (a.1 / 2) - Real.exp (-a.1 / 2)) / r *
        (if x = Real.log n - a.1 then 1 else 0) := by
    by_cases h : x = Real.log n - a.1
    · simp only [if_pos h, mul_one]
      subst h
      exact hsite2
    · simp [h]
  have key : ccmPolarOddSourcePrimeAtomRight a n x - ccmPolarOddSourcePrimeAtomLeft a n x =
      ArithmeticFunction.vonMangoldt n *
        ((Real.exp (x / 2) - Real.exp (-x / 2) / n) * (if x = a.1 - Real.log n then 1 else 0) +
          (Real.exp (-x / 2) - Real.exp (x / 2) / n) *
            (if x = Real.log n - a.1 then 1 else 0)) := by
    unfold ccmPolarOddSourcePrimeAtomRight ccmPolarOddSourcePrimeAtomLeft
    rw [ind1, ind2]
    ring
  rw [key, t1, t2]
  ring

/-- **The jump law of the odd source.**  At every interior point both one-sided limits of the odd
source exist, and the right limit exceeds the left one by
`(e^{a/2} − e^{−a/2}) Σ_{2 ≤ n ≤ e^{2a}} Λ(n) n^{−1/2} (1_{x = a − log n} + 1_{x = log n − a})`. -/
theorem ccmPolarOddSource_jump (a : SuzukiPositiveAperture) {x : ℝ} (hx : x ∈ Ioo (-a.1) a.1) :
    Tendsto (fun y => (ccmPolarParityBoundaryProfile a (-1) y).re) (𝓝[<] x)
        (𝓝 (ccmPolarOddSourceCore a x +
          ∑ n ∈ oddVisiblePrimes a, ccmPolarOddSourcePrimeAtomLeft a n x)) ∧
      Tendsto (fun y => (ccmPolarParityBoundaryProfile a (-1) y).re) (𝓝[>] x)
        (𝓝 (ccmPolarOddSourceCore a x +
          ∑ n ∈ oddVisiblePrimes a, ccmPolarOddSourcePrimeAtomRight a n x)) ∧
      (ccmPolarOddSourceCore a x + ∑ n ∈ oddVisiblePrimes a, ccmPolarOddSourcePrimeAtomRight a n x) -
          (ccmPolarOddSourceCore a x +
            ∑ n ∈ oddVisiblePrimes a, ccmPolarOddSourcePrimeAtomLeft a n x) =
        (Real.exp (a.1 / 2) - Real.exp (-a.1 / 2)) *
          ∑ n ∈ oddVisiblePrimes a, ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            ((if x = a.1 - Real.log n then 1 else 0) + (if x = Real.log n - a.1 then 1 else 0)) := by
  have hcore := (continuousAt_ccmPolarOddSourceCore a hx).tendsto
  have hdecomp : (fun y => ccmPolarOddSourceCore a y +
        ∑ n ∈ oddVisiblePrimes a, ccmPolarOddSourcePrimeAtom a n y) =ᶠ[𝓝 x]
      fun y => (ccmPolarParityBoundaryProfile a (-1) y).re := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (ccmPolarOddSource_eq_core_add_atoms a hy).symm
  refine ⟨?_, ?_, ?_⟩
  · exact ((hcore.mono_left nhdsWithin_le_nhds).add
      (tendsto_finsetSum _ fun n _ => tendsto_primeAtom_left a n x)).congr'
      (hdecomp.filter_mono nhdsWithin_le_nhds)
  · exact ((hcore.mono_left nhdsWithin_le_nhds).add
      (tendsto_finsetSum _ fun n _ => tendsto_primeAtom_right a n x)).congr'
      (hdecomp.filter_mono nhdsWithin_le_nhds)
  · rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := by
      simp only [oddVisiblePrimes, Finset.mem_Icc] at hn; omega
    rw [primeAtomRight_sub_primeAtomLeft a hn1]

/-- **The odd source never jumps down.** -/
theorem ccmPolarOddSource_jump_nonneg (a : SuzukiPositiveAperture) {x : ℝ} :
    0 ≤ (Real.exp (a.1 / 2) - Real.exp (-a.1 / 2)) *
      ∑ n ∈ oddVisiblePrimes a, ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        ((if x = a.1 - Real.log n then 1 else 0) + (if x = Real.log n - a.1 then 1 else 0)) := by
  have hE : Real.exp (-a.1 / 2) ≤ Real.exp (a.1 / 2) :=
    Real.exp_le_exp.mpr (by linarith [a.2])
  refine mul_nonneg (by linarith) (Finset.sum_nonneg fun n _ => mul_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)) ?_)
  split_ifs <;> norm_num

end RHTower
