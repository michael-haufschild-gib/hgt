import GaloisForLFunctions.RHTower.MarkovOddShiftWindowAndPlasticCrossoverPBAP

/-!
# Markov Odd-Sector and Primitive-Hyperplane Farkas Duality, Odd Node Generators, and One-Sided PBAP Extension

This module advances Route HF and the Prime-Blind Archimedean Positivity (PBAP) program by
establishing **pole-free two-sided Farkas duality and one-sided M. Riesz extension** directly on the
**odd sector** (`OddWeilTestFn`) and on the **primitive hyperplane** (`PrimitiveWeilTestFn`,
`coshHalfMoment f = 0`), where the pole term of `ζ` is completely absent (`markovArchRe` and
`markovCountertermEnergy`).

## Key Mathematical Insights

1. **Both Signs of Every Coordinate `e_j` (`j ≥ 2`) Are Reachable Inside the Odd Sector Alone:**
   - For an **even** narrow bump `evenNarrowBump j` supported in `[-1/(4(j+1)), 1/(4(j+1))]`, the
     **odd shift** `oddShift (evenNarrowBump j) (Real.log j)` is an **odd** real test whose
     `logVector` is a **strictly negative** multiple of `Finsupp.single j 1`:
     `Finsupp.single j (-((∫ t, evenNarrowBump j t ^ 2) / (2 * Real.sqrt j)))`.
   - For an **odd** narrow bump `oddNarrowBump j u = u * evenNarrowBump j u` supported in
     `[-1/(4(j+1)), 1/(4(j+1))]`, the **symmetric translate average**
     `evenShift (oddNarrowBump j) (Real.log j) x = (o_j(x - (log j)/2) + o_j(x + (log j)/2)) / 2`
     is ALSO an **odd** real test (`evenShift_neg_of_odd`), and its `logVector` is a **strictly
     positive** multiple of `Finsupp.single j 1`:
     `Finsupp.single j ((∫ t, oddNarrowBump j t ^ 2) / (2 * Real.sqrt j))`.

2. **Pole-Free Farkas and M. Riesz Extension on the Odd Sector and Primitive Hyperplane:**
   - Because `OddWeilTestFn` (and a fortiori `PrimitiveWeilTestFn`) contains coordinate generators
     of both signs `± e_j` for every `j : LogIndex`, `exists_of_nonneg_on_null_cone`,
     `exists_le_of_nonneg_on_nonpos_cone`, and `exists_ge_of_nonneg_on_nonneg_cone` apply directly
     to the **pole-free** archimedean Gamma/Lévy functional `markovArchRe`:
     - `exists_markovPositiveOdd_iff_oddPrimeBlindPositive`:
       `(∃ lam : ℕ → ℝ, MarkovPositiveOdd lam) ↔ OddPrimeBlindPositive`.
     - `exists_markovPositivePrimitive_iff_primitivePrimeBlindPositive`:
       `(∃ lam : ℕ → ℝ, MarkovPositivePrimitive lam) ↔ PrimitivePrimeBlindPositive`.
     - `exists_markovPositiveOdd_le_of_oddPositiveOnNonposCone` and
       `exists_markovPositiveOdd_ge_of_oddPositiveOnNonnegCone`: one-sided minorant/majorant
       extension on the odd sector.
     - `exists_markovPositivePrimitive_le_of_primitivePositiveOnNonposCone` and
       `exists_markovPositivePrimitive_ge_of_primitivePositiveOnNonnegCone`: one-sided
       minorant/majorant extension on the primitive hyperplane.

3. **Uniform Pole-Free Window Bounds on `MarkovPositiveOdd` Systems:**
   - Testing `MarkovPositiveOdd lam` on `oddShift g h` for an even bump `g` supported in `[-1/4, 1/4]`
     bounds `windowSum hg hgc hsupp lam h` uniformly from **below** by `-2 B_g` across all `h ∈ ℝ`
     (with NO `cosh(h/2)` growth!).
   - Testing `MarkovPositiveOdd lam` on `evenShift o h` for an odd bump `o` supported in `[-1/4, 1/4]`
     bounds `windowSum ho hoc hsupp lam h` uniformly from **above** by `+2 B_o` across all `h ∈ ℝ`.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: The Symmetric Translate Operator `evenShift g h`, Position-Space Autocorrelation, and Short-Support Window Evaluation -/

/-- The symmetric translate average of `u` by `± h / 2`:
`E_h(x) = (u(x - h / 2) + u(x + h / 2)) / 2`.
When `u` is odd (`∀ x, u (-x) = -u x`), `evenShift u h` is **odd**; when `u` is even, `evenShift u h`
is **even**. -/
def evenShift (u : ℝ → ℝ) (h x : ℝ) : ℝ :=
  (u (x - h / 2) + u (x + h / 2)) / 2

/-- When `u : ℝ → ℝ` is odd (`∀ x, u (-x) = -u x`), `evenShift u h` is odd for every `h ∈ ℝ`. -/
theorem evenShift_neg_of_odd {u : ℝ → ℝ} (hodd : ∀ x, u (-x) = -u x) (h x : ℝ) :
    evenShift u h (-x) = -evenShift u h x := by
  unfold evenShift
  rw [show -x - h / 2 = -(x + h / 2) by ring, show -x + h / 2 = -(x - h / 2) by ring, hodd, hodd]
  ring

/-- When `u : ℝ → ℝ` is even (`∀ x, u (-x) = u x`), `evenShift u h` is even for every `h ∈ ℝ`. -/
theorem evenShift_neg_of_even {u : ℝ → ℝ} (heven : ∀ x, u (-x) = u x) (h x : ℝ) :
    evenShift u h (-x) = evenShift u h x := by
  unfold evenShift
  rw [show -x - h / 2 = -(x + h / 2) by ring, show -x + h / 2 = -(x - h / 2) by ring, heven, heven]
  ring

/-- `evenShift u h` preserves `ContDiff ℝ 2`. -/
theorem contDiff_evenShift {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (h : ℝ) :
    ContDiff ℝ 2 (evenShift u h) := by
  unfold evenShift
  exact ((hu.comp (contDiff_id.sub contDiff_const)).add
    (hu.comp (contDiff_id.add contDiff_const))).div_const 2

/-- `evenShift u h` preserves `HasCompactSupport`. -/
theorem hasCompactSupport_evenShift {u : ℝ → ℝ} (hcpt : HasCompactSupport u) (h : ℝ) :
    HasCompactSupport (evenShift u h) := by
  have h1 : HasCompactSupport (fun x => u (x - h / 2)) :=
    hcpt.comp_homeomorph (Homeomorph.subRight (h / 2))
  have h2 : HasCompactSupport (fun x => u (x + h / 2)) :=
    hcpt.comp_homeomorph (Homeomorph.addRight (h / 2))
  have h3 := (h1.add h2).comp_left (g := fun y : ℝ => y / 2) (by norm_num)
  convert h3 using 1
  funext x
  simp [evenShift, Function.comp]

/-- The complex lift of `evenShift g h` expressed as a 2-term linear combination of translates of
`liftC g`. -/
theorem evenShift_liftC_eq_sum (g : ℝ → ℝ) (h : ℝ) :
    (fun u => (evenShift g h u : ℂ)) = fun u => ∑ m ∈ Finset.range 2,
      (if m = 0 then (1 / 2 : ℂ) else (1 / 2 : ℂ)) *
        liftC g (u - if m = 0 then h / 2 else -(h / 2)) := by
  funext u
  simp only [evenShift, liftC, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    if_true, one_ne_zero, if_false, sub_neg_eq_add]
  push_cast
  ring

/-- **Exact Position-Space Autocorrelation Identity for `evenShift g h`**:
for any continuous compactly supported `g : ℝ → ℝ` and `h, y ∈ ℝ`,
`EF.weilTest (evenShift g h) (evenShift g h) y = (2 * autoCorr g y + autoCorr g (y + h) + autoCorr g (y - h)) / 4`. -/
theorem weilTest_evenShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h y : ℝ) :
    EF.weilTest (fun u => (evenShift g h u : ℂ)) (fun u => (evenShift g h u : ℂ)) y =
      (((2 * autoCorr g y + autoCorr g (y + h) + autoCorr g (y - h)) / 4 : ℝ) : ℂ) := by
  rw [evenShift_liftC_eq_sum, weilTest_sum_translates
    (show Continuous (liftC g) from Complex.continuous_ofReal.comp hg) (hasCompactSupport_liftC hgc)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_true, one_ne_zero,
    if_false, map_div₀, map_one, map_ofNat, sub_neg_eq_add, weilTest_liftC]
  rw [show y - h / 2 + h / 2 = y by ring,
    show y - h / 2 + -(h / 2) = y - h by ring,
    show y + h / 2 + h / 2 = y + h by ring,
    show y + h / 2 + -(h / 2) = y by ring]
  push_cast
  ring

/-- **Exact Autocorrelation Bridge Between `evenShift g h` and `shiftPair g 1 h`**:
because `EF.weilTest` is translation-invariant and `evenShift g h` is `1/2` of a translate of
`shiftPair g 1 h`, its autocorrelation is identically `1/4` of `EF.weilTest (shiftPair g 1 h) (shiftPair g 1 h)`. -/
theorem weilTest_evenShift_eq_one_fourth_shiftPair {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (h y : ℝ) :
    EF.weilTest (fun u => (evenShift g h u : ℂ)) (fun u => (evenShift g h u : ℂ)) y =
      (1 / 4 : ℂ) * EF.weilTest (shiftPair g 1 h) (shiftPair g 1 h) y := by
  rw [weilTest_evenShift hg hgc, weilTest_shiftPair hg hgc]
  push_cast
  ring

/-- For every continuous compactly supported `g : ℝ → ℝ`, `h ∈ ℝ`, and `n : ℕ`,
`logValue (evenShift g h) n = (1 / 4) * logValue (shiftPair g 1 h) n`. -/
theorem logValue_evenShift_eq_one_fourth_shiftPair {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (h : ℝ) (n : ℕ) :
    logValue (fun u => (evenShift g h u : ℂ)) n =
      (1 / 4 : ℝ) * logValue (shiftPair g 1 h) n := by
  unfold logValue
  rw [weilTest_evenShift_eq_one_fourth_shiftPair hg hgc,
    weilTest_evenShift_eq_one_fourth_shiftPair hg hgc,
    ← mul_add, show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]
  ring

/-- **Short-Support Window Identity for `logValue` of `evenShift g h`**:
when `g` is supported in `[-1/4, 1/4]` (`∀ u, 1 / 4 < |u| → g u = 0`), for every `n ≥ 2` and `h ∈ ℝ`,
`logValue (evenShift g h) n = (1 / 2) * windowValue g h n`. -/
theorem logValue_evenShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (h : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    logValue (fun u => (evenShift g h u : ℂ)) n = (1 / 2 : ℝ) * windowValue g h n := by
  rw [logValue_evenShift_eq_one_fourth_shiftPair hg hgc h n,
    logValue_shiftPair hg hgc hsupp 1 h hn]
  ring

/-- **Short-Support Window Identity for `logVector` of `evenShift g h`**:
when `g ∈ C²_c(ℝ)` is supported in `[-1/4, 1/4]`, the finitely supported `logVector` of
`evenShift g h` equals `(1 / 2) • windowVector hg hgc hsupp h`. -/
theorem logVector_evenShift {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (h : ℝ) :
    logVector (realWeilTestFn (evenShift g h) (contDiff_evenShift hg h)
      (hasCompactSupport_evenShift hgc h)) =
      (1 / 2 : ℝ) • windowVector hg hgc hsupp h := by
  ext j
  rw [logVector_apply, Finsupp.smul_apply, smul_eq_mul]
  change logValue (fun u => (evenShift g h u : ℂ)) j = _
  rw [logValue_evenShift hg.continuous hgc hsupp h j.2]
  simp [windowVector, Finsupp.ofSupportFinite_coe]

/-- **Window Identity for `primeBlindCounterterm` on `evenShift g h`**:
for any `g ∈ C²_c(ℝ)` supported in `[-1/4, 1/4]`, any counterterm sequence `lam : ℕ → ℝ`, and
any shift `h ∈ ℝ`,
`primeBlindCounterterm lam (evenShift g h) = (1 / 2) * windowSum hg hgc hsupp lam h`. -/
theorem primeBlindCounterterm_evenShift (lam : ℕ → ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (h : ℝ) :
    primeBlindCounterterm lam (realWeilTestFn (evenShift g h) (contDiff_evenShift hg h)
      (hasCompactSupport_evenShift hgc h)) =
      (1 / 2 : ℝ) * windowSum hg hgc hsupp lam h := by
  unfold primeBlindCounterterm windowSum
  rw [logVector_evenShift hg hgc hsupp h, map_smul, smul_eq_mul]

/-- **Markov Counterterm Energy of `evenShift g h` for a Short-Support Bump**:
for any `g ∈ C²_c(ℝ)` supported in `[-1/4, 1/4]`, any counterterm `lam : ℕ → ℝ`, and `h ∈ ℝ`,
`markovCountertermEnergy lam (evenShift g h) = markovArchRe k_{evenShift g h} - (1 / 2) * windowSum lam h`. -/
theorem markovCountertermEnergy_evenShift_eq_arch_sub_half_windowSum (lam : ℕ → ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0)
    (h : ℝ) :
    markovCountertermEnergy lam (fun u => (evenShift g h u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ))) -
        (1 / 2 : ℝ) * windowSum hg hgc hsupp lam h := by
  have h1 : markovCountertermEnergy lam (fun u => (evenShift g h u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ))) -
        primeBlindCounterterm lam (realWeilTestFn (evenShift g h) (contDiff_evenShift hg h)
          (hasCompactSupport_evenShift hgc h)) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam
      (realWeilTestFn (evenShift g h) (contDiff_evenShift hg h) (hasCompactSupport_evenShift hgc h))
  rw [h1, primeBlindCounterterm_evenShift lam hg hgc hsupp h]

/-! ## Section 2: General Short-Support Shift-Pair Node Isolation and Odd Coordinate Generators Reaching Every `j ≥ 2` with Both Signs -/

/-- If `g : ℝ → ℝ` vanishes for `R < |u|`, then `autoCorr g y = 0` for `2 * R < |y|`. -/
theorem autoCorr_eq_zero_of_radius {g : ℝ → ℝ} {R y : ℝ}
    (hsupp : ∀ u, R < |u| → g u = 0) (hy : 2 * R < |y|) :
    autoCorr g y = 0 := by
  unfold autoCorr
  have h0 : (fun t => g t * g (t - y)) = fun _ => 0 := by
    funext t
    rcases le_or_gt |t| R with ht | ht
    · have : R < |t - y| := by
        have := abs_sub_abs_le_abs_sub y t
        rw [abs_sub_comm] at this
        linarith
      simp [hsupp _ this]
    · simp [hsupp t ht]
  rw [h0, integral_zero]

/-- At `x = 0`, `autoCorr g 0 = ∫ t, g t ^ 2`. -/
@[simp]
theorem autoCorr_zero (g : ℝ → ℝ) : autoCorr g 0 = ∫ t, g t ^ 2 := by
  unfold autoCorr
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp [sq]

/-- **General Short-Support Node Isolation for `shiftPair g σ (Real.log j)`**:
for any continuous compactly supported `g : ℝ → ℝ` vanishing outside `[-1/(4(j+1)), 1/(4(j+1))]`,
and any `j ≥ 2`, `m ≥ 2`, and `σ ∈ ℝ`,
`logValue (shiftPair g σ (Real.log j)) m = if m = j then 2 * σ * (∫ t, g t ^ 2) / Real.sqrt j else 0`. -/
theorem logValue_shiftPair_log_eq_ite {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {j : ℕ} (hj : 2 ≤ j) (hsupp : ∀ u, 1 / (4 * ((j : ℝ) + 1)) < |u| → g u = 0)
    (σ : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    logValue (shiftPair g σ (Real.log j)) m =
      if m = j then 2 * σ * (∫ t, g t ^ 2) / Real.sqrt j else 0 := by
  have hH : ∀ Y : ℝ, 1 / (2 * ((j : ℝ) + 1)) < |Y| → autoCorr g Y = 0 := fun Y hY =>
    autoCorr_eq_zero_of_radius hsupp
      (by rw [show 2 * (1 / (4 * ((j : ℝ) + 1))) = 1 / (2 * ((j : ℝ) + 1)) by field_simp; ring]
          exact hY)
  have hlog2 : ∀ n : ℕ, 2 ≤ n → Real.log 2 ≤ Real.log n := fun n hn =>
    Real.log_le_log two_pos (by exact_mod_cast hn)
  have hsmall : 1 / (2 * ((j : ℝ) + 1)) < Real.log 2 := by
    refine lt_of_le_of_lt ?_ WeilExcess.seventeen_div_twentyfive_lt_log_two
    rw [div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hm2 := hlog2 m hm
  have hj2 := hlog2 j hj
  have hpos : 0 < 1 / (2 * ((j : ℝ) + 1)) := by positivity
  have e1 := hH (Real.log m) (by rw [abs_of_pos (by linarith)]; linarith)
  have e2 := hH (-Real.log m) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have e3 := hH (Real.log m + Real.log j) (by rw [abs_of_pos (by linarith)]; linarith)
  have e4 := hH (-Real.log m - Real.log j) (by
    rw [show -Real.log m - Real.log j = -(Real.log m + Real.log j) by ring, abs_neg,
      abs_of_pos (by linarith)]; linarith)
  rw [logValue, weilTest_shiftPair hg hgc, weilTest_shiftPair hg hgc, e1, e2, e3,
    show -Real.log m + Real.log j = -(Real.log m - Real.log j) by ring, e4]
  split_ifs with hmj
  · subst hmj
    rw [sub_self, neg_zero, autoCorr_zero]
    rw [← Complex.ofReal_add, Complex.ofReal_re]
    ring
  · have hgap := WeilExcess.inv_succ_le_abs_log_sub (by omega) (by omega) hmj
    have hlt : 1 / (2 * ((j : ℝ) + 1)) < 1 / ((j : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    rw [hH (Real.log m - Real.log j) (by linarith), hH (-(Real.log m - Real.log j))
      (by rw [abs_neg]; linarith)]
    simp

/-- **Node Isolation for `oddShift g (Real.log j)`**:
when `g` vanishes outside `[-1/(4(j+1)), 1/(4(j+1))]`,
`logValue (oddShift g (Real.log j)) m = if m = j then -((∫ t, g t ^ 2) / (2 * Real.sqrt j)) else 0`. -/
theorem logValue_oddShift_log_eq_ite {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {j : ℕ} (hj : 2 ≤ j) (hsupp : ∀ u, 1 / (4 * ((j : ℝ) + 1)) < |u| → g u = 0)
    {m : ℕ} (hm : 2 ≤ m) :
    logValue (fun u => (oddShift g (Real.log j) u : ℂ)) m =
      if m = j then -((∫ t, g t ^ 2) / (2 * Real.sqrt j)) else 0 := by
  rw [logValue_oddShift_eq_one_fourth_shiftPair hg hgc (Real.log j) m,
    logValue_shiftPair_log_eq_ite hg hgc hj hsupp (-1) hm]
  split_ifs <;> ring

/-- **Node Isolation for `evenShift g (Real.log j)`**:
when `g` vanishes outside `[-1/(4(j+1)), 1/(4(j+1))]`,
`logValue (evenShift g (Real.log j)) m = if m = j then (∫ t, g t ^ 2) / (2 * Real.sqrt j) else 0`. -/
theorem logValue_evenShift_log_eq_ite {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {j : ℕ} (hj : 2 ≤ j) (hsupp : ∀ u, 1 / (4 * ((j : ℝ) + 1)) < |u| → g u = 0)
    {m : ℕ} (hm : 2 ≤ m) :
    logValue (fun u => (evenShift g (Real.log j) u : ℂ)) m =
      if m = j then (∫ t, g t ^ 2) / (2 * Real.sqrt j) else 0 := by
  rw [logValue_evenShift_eq_one_fourth_shiftPair hg hgc (Real.log j) m,
    logValue_shiftPair_log_eq_ite hg hgc hj hsupp 1 hm]
  split_ifs <;> ring

/-- The symmetrized even narrow bump `(narrowBump j u + narrowBump j (-u)) / 2` of radius
`1 / (4 * (j + 1))`. -/
def evenNarrowBump (j : ℕ) (u : ℝ) : ℝ :=
  evenPartReal (fun x => narrowBump j x) u

/-- The odd narrow bump `u * evenNarrowBump j u` of radius `1 / (4 * (j + 1))`. -/
def oddNarrowBump (j : ℕ) (u : ℝ) : ℝ :=
  u * evenNarrowBump j u

theorem evenNarrowBump_neg (j : ℕ) (u : ℝ) : evenNarrowBump j (-u) = evenNarrowBump j u :=
  evenPartReal_neg _ u

theorem oddNarrowBump_neg (j : ℕ) (u : ℝ) : oddNarrowBump j (-u) = -oddNarrowBump j u := by
  unfold oddNarrowBump
  rw [evenNarrowBump_neg]
  ring

theorem contDiff_evenNarrowBump (j : ℕ) : ContDiff ℝ 2 (evenNarrowBump j) :=
  contDiff_evenPartReal ((narrowBump j).contDiff.of_le (by norm_cast))

theorem hasCompactSupport_evenNarrowBump (j : ℕ) : HasCompactSupport (evenNarrowBump j) :=
  hasCompactSupport_evenPartReal (narrowBump j).hasCompactSupport

theorem contDiff_oddNarrowBump (j : ℕ) : ContDiff ℝ 2 (oddNarrowBump j) :=
  contDiff_id.mul (contDiff_evenNarrowBump j)

theorem hasCompactSupport_oddNarrowBump (j : ℕ) : HasCompactSupport (oddNarrowBump j) :=
  (hasCompactSupport_evenNarrowBump j).mul_left

theorem evenNarrowBump_eq_zero (j : ℕ) {u : ℝ} (hu : 1 / (4 * ((j : ℝ) + 1)) < |u|) :
    evenNarrowBump j u = 0 := by
  have h1 : (narrowBump j).rOut ≤ dist u 0 := by rw [Real.dist_eq, sub_zero]; exact hu.le
  have h2 : (narrowBump j).rOut ≤ dist (-u) 0 := by
    rw [Real.dist_eq, sub_zero, abs_neg]; exact hu.le
  unfold evenNarrowBump evenPartReal
  dsimp only
  rw [(narrowBump j).zero_of_le_dist h1, (narrowBump j).zero_of_le_dist h2]
  ring

theorem oddNarrowBump_eq_zero (j : ℕ) {u : ℝ} (hu : 1 / (4 * ((j : ℝ) + 1)) < |u|) :
    oddNarrowBump j u = 0 := by
  rw [oddNarrowBump, evenNarrowBump_eq_zero j hu, mul_zero]

theorem integral_evenNarrowBump_sq_pos (j : ℕ) : 0 < ∫ t, evenNarrowBump j t ^ 2 := by
  have hc : Continuous fun t => evenNarrowBump j t ^ 2 :=
    (contDiff_evenNarrowBump j).continuous.pow 2
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((hasCompactSupport_evenNarrowBump j).comp_left (g := fun x : ℝ => x ^ 2) (by norm_num))
    (fun t => sq_nonneg _) (x := 0) ?_
  unfold evenNarrowBump evenPartReal
  dsimp only
  rw [neg_zero,
    (narrowBump j).one_of_mem_closedBall (Metric.mem_closedBall_self (narrowBump j).rIn_pos.le)]
  norm_num

theorem integral_oddNarrowBump_sq_pos (j : ℕ) : 0 < ∫ t, oddNarrowBump j t ^ 2 := by
  have hc : Continuous fun t => oddNarrowBump j t ^ 2 :=
    (contDiff_oddNarrowBump j).continuous.pow 2
  set x₀ : ℝ := (narrowBump j).rIn / 2 with hx₀_def
  have hx₀ : 0 < x₀ := div_pos (narrowBump j).rIn_pos two_pos
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((hasCompactSupport_oddNarrowBump j).comp_left (g := fun x : ℝ => x ^ 2) (by norm_num))
    (fun t => sq_nonneg _) (x := x₀) ?_
  have hm1 : x₀ ∈ Metric.closedBall (0 : ℝ) (narrowBump j).rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos hx₀, hx₀_def]
    linarith [(narrowBump j).rIn_pos]
  have hm2 : -x₀ ∈ Metric.closedBall (0 : ℝ) (narrowBump j).rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_neg, abs_of_pos hx₀, hx₀_def]
    linarith [(narrowBump j).rIn_pos]
  unfold oddNarrowBump evenNarrowBump evenPartReal
  dsimp only
  rw [(narrowBump j).one_of_mem_closedBall hm1, (narrowBump j).one_of_mem_closedBall hm2]
  positivity

/-! ## Section 3: The Odd-Sector and Primitive-Hyperplane Markov Cones and Pole-Free Farkas / M. Riesz Extension Theorems -/

/-- The type of **odd real Weil tests**: `f ∈ C²_c(ℝ)` satisfying `∀ x, f (-x) = -f x`. -/
def OddWeilTestFn : Type :=
  {f : ℝ → ℝ // ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ ∀ x, f (-x) = -f x}

/-- Complex lift of `f : OddWeilTestFn` into `WeilTestFn`. -/
def OddWeilTestFn.toWeilTestFn (f : OddWeilTestFn) : WeilTestFn :=
  realWeilTestFn f.1 f.2.1 f.2.2.1

/-- The type of **primitive-hyperplane real Weil tests**: `f ∈ C²_c(ℝ)` satisfying
`coshHalfMoment f = 0`. -/
def PrimitiveWeilTestFn : Type :=
  {f : ℝ → ℝ // ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ coshHalfMoment f = 0}

/-- Complex lift of `f : PrimitiveWeilTestFn` into `WeilTestFn`. -/
def PrimitiveWeilTestFn.toWeilTestFn (f : PrimitiveWeilTestFn) : WeilTestFn :=
  realWeilTestFn f.1 f.2.1 f.2.2.1

/-- Canonical embedding of `OddWeilTestFn` into `PrimitiveWeilTestFn` (`coshHalfMoment_eq_zero_of_odd`). -/
def OddWeilTestFn.toPrimitiveWeilTestFn (f : OddWeilTestFn) : PrimitiveWeilTestFn :=
  ⟨f.1, f.2.1, f.2.2.1, coshHalfMoment_eq_zero_of_odd f.2.2.2⟩

/-- The **odd negative node generator** at `j : ℕ`: `oddShift (evenNarrowBump j) (Real.log j)`. -/
def oddNegNodeTest (j : ℕ) : OddWeilTestFn :=
  ⟨oddShift (evenNarrowBump j) (Real.log j),
    contDiff_oddShift (contDiff_evenNarrowBump j) (Real.log j),
    hasCompactSupport_oddShift (hasCompactSupport_evenNarrowBump j) (Real.log j),
    oddShift_neg (evenNarrowBump_neg j) (Real.log j)⟩

/-- The **odd positive node generator** at `j : ℕ`: `evenShift (oddNarrowBump j) (Real.log j)`. -/
def oddPosNodeTest (j : ℕ) : OddWeilTestFn :=
  ⟨evenShift (oddNarrowBump j) (Real.log j),
    contDiff_evenShift (contDiff_oddNarrowBump j) (Real.log j),
    hasCompactSupport_evenShift (hasCompactSupport_oddNarrowBump j) (Real.log j),
    evenShift_neg_of_odd (oddNarrowBump_neg j) (Real.log j)⟩

/-- For every `j : LogIndex`, `logVector (oddNegNodeTest j).toWeilTestFn` is a strictly negative
multiple of `Finsupp.single j 1`. -/
theorem logVector_oddNegNodeTest (j : LogIndex) :
    logVector (oddNegNodeTest j).toWeilTestFn =
      Finsupp.single j (-((∫ t, evenNarrowBump j t ^ 2) / (2 * Real.sqrt j))) := by
  ext m
  rw [logVector_apply, Finsupp.single_apply]
  change logValue (fun u => (oddShift (evenNarrowBump j) (Real.log j) u : ℂ)) m = _
  rw [logValue_oddShift_log_eq_ite (contDiff_evenNarrowBump j).continuous
    (hasCompactSupport_evenNarrowBump j) j.2 (fun u hu => evenNarrowBump_eq_zero j hu) m.2]
  by_cases h : (m : ℕ) = j
  · rw [if_pos h, if_pos (Subtype.ext h).symm]
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h'.symm)]

/-- For every `j : LogIndex`, `logVector (oddPosNodeTest j).toWeilTestFn` is a strictly positive
multiple of `Finsupp.single j 1`. -/
theorem logVector_oddPosNodeTest (j : LogIndex) :
    logVector (oddPosNodeTest j).toWeilTestFn =
      Finsupp.single j ((∫ t, oddNarrowBump j t ^ 2) / (2 * Real.sqrt j)) := by
  ext m
  rw [logVector_apply, Finsupp.single_apply]
  change logValue (fun u => (evenShift (oddNarrowBump j) (Real.log j) u : ℂ)) m = _
  rw [logValue_evenShift_log_eq_ite (contDiff_oddNarrowBump j).continuous
    (hasCompactSupport_oddNarrowBump j) j.2 (fun u hu => oddNarrowBump_eq_zero j hu) m.2]
  by_cases h : (m : ℕ) = j
  · rw [if_pos h, if_pos (Subtype.ext h).symm]
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h'.symm)]

theorem oddNegNodeTest_weight_pos (j : LogIndex) :
    0 < (∫ t, evenNarrowBump j t ^ 2) / (2 * Real.sqrt j) := by
  have hj : (0 : ℝ) < (j : ℕ) := by exact_mod_cast (lt_of_lt_of_le two_pos j.2)
  exact div_pos (integral_evenNarrowBump_sq_pos j) (mul_pos two_pos (Real.sqrt_pos.mpr hj))

theorem oddPosNodeTest_weight_pos (j : LogIndex) :
    0 < (∫ t, oddNarrowBump j t ^ 2) / (2 * Real.sqrt j) := by
  have hj : (0 : ℝ) < (j : ℕ) := by exact_mod_cast (lt_of_lt_of_le two_pos j.2)
  exact div_pos (integral_oddNarrowBump_sq_pos j) (mul_pos two_pos (Real.sqrt_pos.mpr hj))

/-- **Markov Positivity on Odd Tests**: `0 ≤ markovCountertermEnergy lam F` for every odd real test
`f ∈ C²_c(ℝ)`. -/
def MarkovPositiveOdd (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → (∀ x, f (-x) = -f x) →
    0 ≤ markovCountertermEnergy lam (fun x => (f x : ℂ))

/-- **Markov Positivity on the Primitive Hyperplane**: `0 ≤ markovCountertermEnergy lam F` for every
real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`. -/
def MarkovPositivePrimitive (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → coshHalfMoment f = 0 →
    0 ≤ markovCountertermEnergy lam (fun x => (f x : ℂ))

/-- `RiemannHypothesis` is equivalent to `MarkovPositiveOdd Λ`. -/
theorem riemannHypothesis_iff_markovPositiveOdd_vonMangoldt :
    RiemannHypothesis ↔
      MarkovPositiveOdd (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
  riemannHypothesis_iff_forall_odd_markovEnergy_nonneg

/-- `RiemannHypothesis` is equivalent to `MarkovPositivePrimitive Λ`. -/
theorem riemannHypothesis_iff_markovPositivePrimitive_vonMangoldt :
    RiemannHypothesis ↔
      MarkovPositivePrimitive (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
  riemannHypothesis_iff_forall_cosh_moment_zero_markovEnergy_nonneg

/-- Every `WeilPositiveFull lam` sequence is `MarkovPositivePrimitive lam` (and hence
`MarkovPositiveOdd lam`). -/
theorem markovPositivePrimitive_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    MarkovPositivePrimitive lam := by
  intro f hf hfc hcosh
  rw [markovCountertermEnergy_real_eq_re_weilFullFunctional_add_sinh_sq_of_cosh_zero lam hf hfc
    hcosh]
  have h1 := hW (fun x => (f x : ℂ)) (Complex.ofRealCLM.contDiff.comp hf)
    (hfc.comp_left Complex.ofReal_zero)
  nlinarith [sq_nonneg (sinhHalfMoment f)]

/-- Every `MarkovPositivePrimitive lam` sequence is `MarkovPositiveOdd lam`. -/
theorem markovPositiveOdd_of_markovPositivePrimitive {lam : ℕ → ℝ}
    (hP : MarkovPositivePrimitive lam) : MarkovPositiveOdd lam :=
  fun f hf hfc hodd => hP f hf hfc (coshHalfMoment_eq_zero_of_odd hodd)

/-- **Pole-Free Odd-Sector Prime-Blind Positivity**:
for every nonnegative mixture `c : OddWeilTestFn →₀ ℝ` of odd tests whose `logValue` sums vanish at
all `n ≥ 2`, the pole-free archimedean Gamma/Lévy functional `markovArchRe` is nonnegative. -/
def OddPrimeBlindPositive : Prop :=
  ∀ c : OddWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.toWeilTestFn.1 n) = 0) →
    0 ≤ c.sum fun f t => t * markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)

/-- **Pole-Free Primitive-Hyperplane Prime-Blind Positivity**:
for every nonnegative mixture `c : PrimitiveWeilTestFn →₀ ℝ` of primitive-hyperplane tests whose
`logValue` sums vanish at all `n ≥ 2`, `markovArchRe` is nonnegative. -/
def PrimitivePrimeBlindPositive : Prop :=
  ∀ c : PrimitiveWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.toWeilTestFn.1 n) = 0) →
    0 ≤ c.sum fun f t => t * markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)

/-- **One-Sided Nonpositive Cone Positivity on the Odd Sector**: -/
def OddPositiveOnNonposCone (U : ℕ → ℝ) : Prop :=
  ∀ c : OddWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.toWeilTestFn.1 n) ≤ 0) →
    0 ≤ c.sum fun f t => t * markovCountertermEnergy U f.toWeilTestFn.1

/-- **One-Sided Nonnegative Cone Positivity on the Odd Sector**: -/
def OddPositiveOnNonnegCone (L : ℕ → ℝ) : Prop :=
  ∀ c : OddWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.toWeilTestFn.1 n) →
    0 ≤ c.sum fun f t => t * markovCountertermEnergy L f.toWeilTestFn.1

/-- **One-Sided Nonpositive Cone Positivity on the Primitive Hyperplane**: -/
def PrimitivePositiveOnNonposCone (U : ℕ → ℝ) : Prop :=
  ∀ c : PrimitiveWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.toWeilTestFn.1 n) ≤ 0) →
    0 ≤ c.sum fun f t => t * markovCountertermEnergy U f.toWeilTestFn.1

/-- **One-Sided Nonnegative Cone Positivity on the Primitive Hyperplane**: -/
def PrimitivePositiveOnNonnegCone (L : ℕ → ℝ) : Prop :=
  ∀ c : PrimitiveWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.toWeilTestFn.1 n) →
    0 ≤ c.sum fun f t => t * markovCountertermEnergy L f.toWeilTestFn.1

theorem sum_markovCountertermEnergy_odd (U : ℕ → ℝ) (c : OddWeilTestFn →₀ ℝ) :
    (c.sum fun f t => t * markovCountertermEnergy U f.toWeilTestFn.1) =
      linearCombination ℝ (fun f : OddWeilTestFn =>
        markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)) c -
      linearCombination ℝ (fun j : LogIndex => U j)
        (linearCombination ℝ (fun f : OddWeilTestFn => logVector f.toWeilTestFn) c) := by
  simp_rw [markovCountertermEnergy_eq_markovArchRe_sub_counterterm, primeBlindCounterterm]
  have e1 : linearCombination ℝ (fun f : OddWeilTestFn =>
      markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)) c =
      c.sum fun f t => t * markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1) := by
    rw [linearCombination_apply]; simp only [smul_eq_mul]
  have e2 : linearCombination ℝ (fun j : LogIndex => U j)
      (linearCombination ℝ (fun f : OddWeilTestFn => logVector f.toWeilTestFn) c) =
      c.sum fun f t => t * linearCombination ℝ (fun j : LogIndex => U j)
        (logVector f.toWeilTestFn) := by
    rw [linearCombination_apply ℝ (v := fun f : OddWeilTestFn => logVector f.toWeilTestFn),
      map_finsuppSum]
    exact Finsupp.sum_congr fun f _ => by rw [map_smul, smul_eq_mul]
  rw [e1, e2, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun f _ => by ring

theorem sum_markovCountertermEnergy_primitive (U : ℕ → ℝ) (c : PrimitiveWeilTestFn →₀ ℝ) :
    (c.sum fun f t => t * markovCountertermEnergy U f.toWeilTestFn.1) =
      linearCombination ℝ (fun f : PrimitiveWeilTestFn =>
        markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)) c -
      linearCombination ℝ (fun j : LogIndex => U j)
        (linearCombination ℝ (fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn) c) := by
  simp_rw [markovCountertermEnergy_eq_markovArchRe_sub_counterterm, primeBlindCounterterm]
  have e1 : linearCombination ℝ (fun f : PrimitiveWeilTestFn =>
      markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)) c =
      c.sum fun f t => t * markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1) := by
    rw [linearCombination_apply]; simp only [smul_eq_mul]
  have e2 : linearCombination ℝ (fun j : LogIndex => U j)
      (linearCombination ℝ (fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn) c) =
      c.sum fun f t => t * linearCombination ℝ (fun j : LogIndex => U j)
        (logVector f.toWeilTestFn) := by
    rw [linearCombination_apply ℝ (v := fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn),
      map_finsuppSum]
    exact Finsupp.sum_congr fun f _ => by rw [map_smul, smul_eq_mul]
  rw [e1, e2, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun f _ => by ring

theorem markovPositiveOdd_of_le_arch {lam : LogIndex → ℝ}
    (h : ∀ f : OddWeilTestFn,
      linearCombination ℝ lam (logVector f.toWeilTestFn) ≤
        markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)) :
    MarkovPositiveOdd fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0 := by
  intro f hf hfc hodd
  let F : OddWeilTestFn := ⟨f, hf, hfc, hodd⟩
  have h1 : markovCountertermEnergy (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0)
      (fun x => (f x : ℂ)) =
      markovArchRe (EF.weilTest F.toWeilTestFn.1 F.toWeilTestFn.1) -
        linearCombination ℝ (fun j : LogIndex =>
          (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ))
          (logVector F.toWeilTestFn) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm _ F.toWeilTestFn
  rw [h1]
  have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ)) =
      lam := funext fun j => by simp [j.2]
  rw [e]
  linarith [h F]

theorem markovPositivePrimitive_of_le_arch {lam : LogIndex → ℝ}
    (h : ∀ f : PrimitiveWeilTestFn,
      linearCombination ℝ lam (logVector f.toWeilTestFn) ≤
        markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)) :
    MarkovPositivePrimitive fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0 := by
  intro f hf hfc hcosh
  let F : PrimitiveWeilTestFn := ⟨f, hf, hfc, hcosh⟩
  have h1 : markovCountertermEnergy (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0)
      (fun x => (f x : ℂ)) =
      markovArchRe (EF.weilTest F.toWeilTestFn.1 F.toWeilTestFn.1) -
        linearCombination ℝ (fun j : LogIndex =>
          (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ))
          (logVector F.toWeilTestFn) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm _ F.toWeilTestFn
  rw [h1]
  have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ)) =
      lam := funext fun j => by simp [j.2]
  rw [e]
  linarith [h F]

/-- **Pole-Free Odd-Sector Two-Sided Farkas Theorem**:
some real sequence `lam : ℕ → ℝ` satisfies `MarkovPositiveOdd lam` if and only if the pole-free
archimedean Gamma/Lévy functional `markovArchRe` is nonnegative on the odd prime-blind cone
(`OddPrimeBlindPositive`). -/
theorem exists_markovPositiveOdd_iff_oddPrimeBlindPositive :
    (∃ lam : ℕ → ℝ, MarkovPositiveOdd lam) ↔ OddPrimeBlindPositive := by
  constructor
  · rintro ⟨lam, hM⟩ c hc hnull
    have h1 : 0 ≤ c.sum fun f t => t * markovCountertermEnergy lam f.toWeilTestFn.1 :=
      Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (hM f.1 f.2.1 f.2.2.1 f.2.2.2)
    have h0 : linearCombination ℝ (fun f : OddWeilTestFn => logVector f.toWeilTestFn) c = 0 := by
      ext j
      rw [linearCombination_apply, Finsupp.sum_apply, Finsupp.coe_zero, Pi.zero_apply]
      simp only [Finsupp.smul_apply, logVector_apply, smul_eq_mul]
      exact hnull j j.2
    rw [sum_markovCountertermEnergy_odd, h0, map_zero, sub_zero, linearCombination_apply] at h1
    simpa only [smul_eq_mul] using h1
  · intro h
    obtain ⟨lam, hlam⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
      (fun f : OddWeilTestFn => logVector f.toWeilTestFn)
      (fun f : OddWeilTestFn => markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1))
      (fun j => ⟨oddNegNodeTest j, _, oddNegNodeTest_weight_pos j, logVector_oddNegNodeTest j⟩)
      (fun j => ⟨oddPosNodeTest j, _, oddPosNodeTest_weight_pos j, logVector_oddPosNodeTest j⟩)
      (fun c hc hnull => by
        rw [linearCombination_apply]
        simp only [smul_eq_mul]
        refine h c hc fun n hn => ?_
        have h0 := congrArg (fun v : LogIndex →₀ ℝ => v ⟨n, hn⟩) hnull
        simp only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
          logVector_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h0
        exact h0)
    exact ⟨_, markovPositiveOdd_of_le_arch hlam⟩

/-- **Pole-Free Primitive-Hyperplane Two-Sided Farkas Theorem**:
some real sequence `lam : ℕ → ℝ` satisfies `MarkovPositivePrimitive lam` if and only if
`PrimitivePrimeBlindPositive` holds. -/
theorem exists_markovPositivePrimitive_iff_primitivePrimeBlindPositive :
    (∃ lam : ℕ → ℝ, MarkovPositivePrimitive lam) ↔ PrimitivePrimeBlindPositive := by
  constructor
  · rintro ⟨lam, hM⟩ c hc hnull
    have h1 : 0 ≤ c.sum fun f t => t * markovCountertermEnergy lam f.toWeilTestFn.1 :=
      Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (hM f.1 f.2.1 f.2.2.1 f.2.2.2)
    have h0 : linearCombination ℝ
        (fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn) c = 0 := by
      ext j
      rw [linearCombination_apply, Finsupp.sum_apply, Finsupp.coe_zero, Pi.zero_apply]
      simp only [Finsupp.smul_apply, logVector_apply, smul_eq_mul]
      exact hnull j j.2
    rw [sum_markovCountertermEnergy_primitive, h0, map_zero, sub_zero,
      linearCombination_apply] at h1
    simpa only [smul_eq_mul] using h1
  · intro h
    obtain ⟨lam, hlam⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
      (fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn)
      (fun f : PrimitiveWeilTestFn =>
        markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1))
      (fun j => ⟨(oddNegNodeTest j).toPrimitiveWeilTestFn, _, oddNegNodeTest_weight_pos j,
        logVector_oddNegNodeTest j⟩)
      (fun j => ⟨(oddPosNodeTest j).toPrimitiveWeilTestFn, _, oddPosNodeTest_weight_pos j,
        logVector_oddPosNodeTest j⟩)
      (fun c hc hnull => by
        rw [linearCombination_apply]
        simp only [smul_eq_mul]
        refine h c hc fun n hn => ?_
        have h0 := congrArg (fun v : LogIndex →₀ ℝ => v ⟨n, hn⟩) hnull
        simp only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
          logVector_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h0
        exact h0)
    exact ⟨_, markovPositivePrimitive_of_le_arch hlam⟩

/-- **One-Sided M. Riesz Minorant Extension on the Odd Sector**:
if `OddPositiveOnNonposCone U` holds, there exists `lam : ℕ → ℝ` with `MarkovPositiveOdd lam`,
`lam n ≤ U n` for all `n ≥ 2`, and `lam n = 0` for `n < 2`. -/
theorem exists_markovPositiveOdd_le_of_oddPositiveOnNonposCone {U : ℕ → ℝ}
    (h : OddPositiveOnNonposCone U) :
    ∃ lam : ℕ → ℝ, MarkovPositiveOdd lam ∧ (∀ n, 2 ≤ n → lam n ≤ U n) ∧
      ∀ n, n < 2 → lam n = 0 := by
  obtain ⟨lam, hlamU, hlamT⟩ := GaloisForLFunctions.HTGeometry.exists_le_of_nonneg_on_nonpos_cone
    (fun f : OddWeilTestFn => logVector f.toWeilTestFn)
    (fun f : OddWeilTestFn => markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1))
    (fun j : LogIndex => U j)
    (fun j => ⟨oddNegNodeTest j, _, oddNegNodeTest_weight_pos j, logVector_oddNegNodeTest j⟩)
    (fun c hc hcT => by
      have h1 := h c hc fun n hn => by
        have h0 := hcT ⟨n, hn⟩
        simpa only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
          logVector_apply, smul_eq_mul] using h0
      rw [sum_markovCountertermEnergy_odd] at h1
      linarith)
  refine ⟨_, markovPositiveOdd_of_le_arch hlamT, fun n hn => ?_, fun n hn => ?_⟩
  · simp only [dif_pos hn]; exact hlamU ⟨n, hn⟩
  · simp only [dif_neg (by omega : ¬ 2 ≤ n)]

/-- **One-Sided M. Riesz Majorant Extension on the Odd Sector**:
if `OddPositiveOnNonnegCone L` holds, there exists `lam : ℕ → ℝ` with `MarkovPositiveOdd lam`,
`L n ≤ lam n` for all `n ≥ 2`, and `lam n = 0` for `n < 2`. -/
theorem exists_markovPositiveOdd_ge_of_oddPositiveOnNonnegCone {L : ℕ → ℝ}
    (h : OddPositiveOnNonnegCone L) :
    ∃ lam : ℕ → ℝ, MarkovPositiveOdd lam ∧ (∀ n, 2 ≤ n → L n ≤ lam n) ∧
      ∀ n, n < 2 → lam n = 0 := by
  obtain ⟨lam, hlamL, hlamT⟩ := GaloisForLFunctions.HTGeometry.exists_ge_of_nonneg_on_nonneg_cone
    (fun f : OddWeilTestFn => logVector f.toWeilTestFn)
    (fun f : OddWeilTestFn => markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1))
    (fun j : LogIndex => L j)
    (fun j => ⟨oddPosNodeTest j, _, oddPosNodeTest_weight_pos j, logVector_oddPosNodeTest j⟩)
    (fun c hc hcT => by
      have h1 := h c hc fun n hn => by
        have h0 := hcT ⟨n, hn⟩
        simpa only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
          logVector_apply, smul_eq_mul] using h0
      rw [sum_markovCountertermEnergy_odd] at h1
      linarith)
  refine ⟨_, markovPositiveOdd_of_le_arch hlamT, fun n hn => ?_, fun n hn => ?_⟩
  · simp only [dif_pos hn]; exact hlamL ⟨n, hn⟩
  · simp only [dif_neg (by omega : ¬ 2 ≤ n)]

/-- **One-Sided M. Riesz Minorant Extension on the Primitive Hyperplane**:
if `PrimitivePositiveOnNonposCone U` holds, there exists `lam : ℕ → ℝ` with
`MarkovPositivePrimitive lam`, `lam n ≤ U n` for all `n ≥ 2`, and `lam n = 0` for `n < 2`. -/
theorem exists_markovPositivePrimitive_le_of_primitivePositiveOnNonposCone {U : ℕ → ℝ}
    (h : PrimitivePositiveOnNonposCone U) :
    ∃ lam : ℕ → ℝ, MarkovPositivePrimitive lam ∧ (∀ n, 2 ≤ n → lam n ≤ U n) ∧
      ∀ n, n < 2 → lam n = 0 := by
  obtain ⟨lam, hlamU, hlamT⟩ := GaloisForLFunctions.HTGeometry.exists_le_of_nonneg_on_nonpos_cone
    (fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn)
    (fun f : PrimitiveWeilTestFn =>
      markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1))
    (fun j : LogIndex => U j)
    (fun j => ⟨(oddNegNodeTest j).toPrimitiveWeilTestFn, _, oddNegNodeTest_weight_pos j,
      logVector_oddNegNodeTest j⟩)
    (fun c hc hcT => by
      have h1 := h c hc fun n hn => by
        have h0 := hcT ⟨n, hn⟩
        simpa only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
          logVector_apply, smul_eq_mul] using h0
      rw [sum_markovCountertermEnergy_primitive] at h1
      linarith)
  refine ⟨_, markovPositivePrimitive_of_le_arch hlamT, fun n hn => ?_, fun n hn => ?_⟩
  · simp only [dif_pos hn]; exact hlamU ⟨n, hn⟩
  · simp only [dif_neg (by omega : ¬ 2 ≤ n)]

/-- **One-Sided M. Riesz Majorant Extension on the Primitive Hyperplane**:
if `PrimitivePositiveOnNonnegCone L` holds, there exists `lam : ℕ → ℝ` with
`MarkovPositivePrimitive lam`, `L n ≤ lam n` for all `n ≥ 2`, and `lam n = 0` for `n < 2`. -/
theorem exists_markovPositivePrimitive_ge_of_primitivePositiveOnNonnegCone {L : ℕ → ℝ}
    (h : PrimitivePositiveOnNonnegCone L) :
    ∃ lam : ℕ → ℝ, MarkovPositivePrimitive lam ∧ (∀ n, 2 ≤ n → L n ≤ lam n) ∧
      ∀ n, n < 2 → lam n = 0 := by
  obtain ⟨lam, hlamL, hlamT⟩ := GaloisForLFunctions.HTGeometry.exists_ge_of_nonneg_on_nonneg_cone
    (fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn)
    (fun f : PrimitiveWeilTestFn =>
      markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1))
    (fun j : LogIndex => L j)
    (fun j => ⟨(oddPosNodeTest j).toPrimitiveWeilTestFn, _, oddPosNodeTest_weight_pos j,
      logVector_oddPosNodeTest j⟩)
    (fun c hc hcT => by
      have h1 := h c hc fun n hn => by
        have h0 := hcT ⟨n, hn⟩
        simpa only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
          logVector_apply, smul_eq_mul] using h0
      rw [sum_markovCountertermEnergy_primitive] at h1
      linarith)
  refine ⟨_, markovPositivePrimitive_of_le_arch hlamT, fun n hn => ?_, fun n hn => ?_⟩
  · simp only [dif_pos hn]; exact hlamL ⟨n, hn⟩
  · simp only [dif_neg (by omega : ¬ 2 ≤ n)]

/-! ## Section 4: Uniform Pole-Free Window Bounds for `MarkovPositiveOdd` Systems -/

/-- `markovArchRe` of `oddShift g h` is bounded in absolute value by
`∫ τ, ‖paperFT (EF.weilTest (liftC g) (liftC g)) τ * (mu τ : ℂ)‖` uniformly in `h ∈ ℝ`. -/
theorem abs_markovArchRe_oddShift_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (h : ℝ) :
    |markovArchRe (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ)))| ≤
      ∫ τ : ℝ, ‖paperFT (EF.weilTest (liftC g) (liftC g)) τ * (mu τ : ℂ)‖ := by
  have heq : EF.weilTest (fun u => (oddShift g h u : ℂ)) (fun u => (oddShift g h u : ℂ)) =
      fun y => (1 / 4 : ℂ) * EF.weilTest (shiftPair g (-1) h) (shiftPair g (-1) h) y :=
    funext (weilTest_oddShift_eq_one_fourth_shiftPair hg.continuous hgc h)
  have hsd := contDiff_shiftPair hg (-1) h
  have hsc := hasCompactSupport_shiftPair hgc (-1) h
  have hkd := EF.weilTest_contDiff hsd hsd.continuous hsc
  have hkc := EF.weilTest_hasCompactSupport hsc hsc
  have hFT : ∀ r : ℝ, paperFT (EF.weilTest (fun u => (oddShift g h u : ℂ))
      (fun u => (oddShift g h u : ℂ))) r =
      (1 / 4 : ℂ) * paperFT (EF.weilTest (shiftPair g (-1) h) (shiftPair g (-1) h)) r := by
    intro r
    rw [heq]
    exact paperFT_const_mul _ _ _
  have harch : markovArchRe (EF.weilTest (fun u => (oddShift g h u : ℂ))
      (fun u => (oddShift g h u : ℂ))) =
      (1 / 4 : ℝ) * markovArchRe (EF.weilTest (shiftPair g (-1) h) (shiftPair g (-1) h)) := by
    rw [markovArchRe_eq_re_archIntegral, markovArchRe_eq_re_archIntegral]
    have hI : (∫ r : ℝ, paperFT (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ))) r * (EF.gammaBracket r : ℂ)) =
        (1 / 4 : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest (shiftPair g (-1) h)
          (shiftPair g (-1) h)) r * (EF.gammaBracket r : ℂ) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [hFT r]
      ring
    rw [hI, ← mul_assoc,
      show (1 / (2 * π) : ℂ) * (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) * (1 / (2 * π) : ℂ) by
        push_cast; ring,
      mul_assoc, Complex.re_ofReal_mul]
  rw [harch, abs_mul, show |(1 / 4 : ℝ)| = 1 / 4 by norm_num]
  have hb := abs_arch_shiftPair_le hg hgc (σ := -1) (by norm_num) h
  rw [ ← markovArchRe_eq_re_archIntegral] at hb
  linarith

/-- `markovArchRe` of `evenShift g h` is bounded in absolute value by
`∫ τ, ‖paperFT (EF.weilTest (liftC g) (liftC g)) τ * (mu τ : ℂ)‖` uniformly in `h ∈ ℝ`. -/
theorem abs_markovArchRe_evenShift_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (h : ℝ) :
    |markovArchRe (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ)))| ≤
      ∫ τ : ℝ, ‖paperFT (EF.weilTest (liftC g) (liftC g)) τ * (mu τ : ℂ)‖ := by
  have heq : EF.weilTest (fun u => (evenShift g h u : ℂ)) (fun u => (evenShift g h u : ℂ)) =
      fun y => (1 / 4 : ℂ) * EF.weilTest (shiftPair g 1 h) (shiftPair g 1 h) y :=
    funext (weilTest_evenShift_eq_one_fourth_shiftPair hg.continuous hgc h)
  have hFT : ∀ r : ℝ, paperFT (EF.weilTest (fun u => (evenShift g h u : ℂ))
      (fun u => (evenShift g h u : ℂ))) r =
      (1 / 4 : ℂ) * paperFT (EF.weilTest (shiftPair g 1 h) (shiftPair g 1 h)) r := by
    intro r
    rw [heq]
    exact paperFT_const_mul _ _ _
  have harch : markovArchRe (EF.weilTest (fun u => (evenShift g h u : ℂ))
      (fun u => (evenShift g h u : ℂ))) =
      (1 / 4 : ℝ) * markovArchRe (EF.weilTest (shiftPair g 1 h) (shiftPair g 1 h)) := by
    rw [markovArchRe_eq_re_archIntegral, markovArchRe_eq_re_archIntegral]
    have hI : (∫ r : ℝ, paperFT (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ))) r * (EF.gammaBracket r : ℂ)) =
        (1 / 4 : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest (shiftPair g 1 h)
          (shiftPair g 1 h)) r * (EF.gammaBracket r : ℂ) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [hFT r]
      ring
    rw [hI, ← mul_assoc,
      show (1 / (2 * π) : ℂ) * (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) * (1 / (2 * π) : ℂ) by
        push_cast; ring,
      mul_assoc, Complex.re_ofReal_mul]
  rw [harch, abs_mul, show |(1 / 4 : ℝ)| = 1 / 4 by norm_num]
  have hb := abs_arch_shiftPair_le hg hgc (σ := 1) (by norm_num) h
  rw [← markovArchRe_eq_re_archIntegral] at hb
  linarith

/-- **Uniform Pole-Free Lower Window Bound for `MarkovPositiveOdd` Systems**:
for any `lam : ℕ → ℝ` satisfying `MarkovPositiveOdd lam`, any **even** bump `g ∈ C²_c(ℝ)` supported
in `[-1/4, 1/4]`, and any shift `h ∈ ℝ`,
`-2 * ∫ τ, ‖paperFT k_g τ * mu τ‖ ≤ windowSum hg hgc hsupp lam h`. -/
theorem neg_two_mul_archBound_le_windowSum_of_markovPositiveOdd {lam : ℕ → ℝ}
    (hM : MarkovPositiveOdd lam) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (heven : ∀ x, g (-x) = g x) (h : ℝ) :
    -2 * (∫ τ : ℝ, ‖paperFT (EF.weilTest (liftC g) (liftC g)) τ * (mu τ : ℂ)‖) ≤
      windowSum hg hgc hsupp lam h := by
  have hnn := hM (oddShift g h) (contDiff_oddShift hg h) (hasCompactSupport_oddShift hgc h)
    (oddShift_neg heven h)
  rw [markovCountertermEnergy_oddShift_eq_arch_add_half_windowSum lam hg hgc hsupp h] at hnn
  have hb := (abs_le.mp (abs_markovArchRe_oddShift_le hg hgc h)).2
  linarith

/-- **Uniform Pole-Free Upper Window Bound for `MarkovPositiveOdd` Systems**:
for any `lam : ℕ → ℝ` satisfying `MarkovPositiveOdd lam`, any **odd** bump `o ∈ C²_c(ℝ)` supported
in `[-1/4, 1/4]`, and any shift `h ∈ ℝ`,
`windowSum ho hoc hsupp lam h ≤ 2 * ∫ τ, ‖paperFT k_o τ * mu τ‖`. -/
theorem windowSum_le_two_mul_archBound_of_markovPositiveOdd {lam : ℕ → ℝ}
    (hM : MarkovPositiveOdd lam) {o : ℝ → ℝ} (ho : ContDiff ℝ 2 o) (hoc : HasCompactSupport o)
    (hsupp : ∀ u, 1 / 4 < |u| → o u = 0) (hodd : ∀ x, o (-x) = -o x) (h : ℝ) :
    windowSum ho hoc hsupp lam h ≤
      2 * (∫ τ : ℝ, ‖paperFT (EF.weilTest (liftC o) (liftC o)) τ * (mu τ : ℂ)‖) := by
  have hnn := hM (evenShift o h) (contDiff_evenShift ho h) (hasCompactSupport_evenShift hoc h)
    (evenShift_neg_of_odd hodd h)
  rw [markovCountertermEnergy_evenShift_eq_arch_sub_half_windowSum lam ho hoc hsupp h] at hnn
  have hb := (abs_le.mp (abs_markovArchRe_evenShift_le ho hoc h)).2
  linarith

end RHTower

end
