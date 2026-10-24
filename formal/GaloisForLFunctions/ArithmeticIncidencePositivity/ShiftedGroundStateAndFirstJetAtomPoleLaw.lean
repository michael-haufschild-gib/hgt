import GaloisForLFunctions.ArithmeticIncidencePositivity.TheIntegratedAtomPoleLawOfLogConcaveGauges
import GaloisForLFunctions.RHTower.RiemannKernelSharpLogDerivative

/-!
# The Shifted Ground-State and First-Jet Integrated Atom-Against-Pole Laws

This module completes the resolution of the integrated atom-against-pole law across the three
canonical gauge families of the incidence-positivity programme:

1. **Strict Midpoint Payment Outside `{2, 3, 4, 5, 7}`
   (`vonMangoldtAtom_lt_crossingPolarWeight_midpoint_of_not_mem`,
   `vonMangoldtAtom_lt_crossingPolarWeight_midpoint_iff`):**
   For every integer `n ≥ 2`, the polar weight at the midpoint `L / 2` (`L = log n`) strictly
   beats the von Mangoldt atom `Λ(n) / √n` if and only if `n ∉ atomDominatedModuli = {2, 3, 4, 5, 7}`.

2. **Midpoint Concentration of Shifted Ground-State Collars and Complete Integrated Classification
   (`shiftDifference_collar_le_of_abs_sub_ge`, `shiftDifference_collar_ge_of_abs_sub_le`,
   `eventually_shiftedGroundState_collar_integral_pos`,
   `eventually_collarAtomMass_lt_collarPolarMass_of_not_mem`,
   `eventually_collarAtomMass_lt_collarPolarMass_iff`,
   `exists_collarAtomMass_lt_collarPolarMass_shiftedGroundState_iff`):**
   Using the sharp double-exponential tail bounds `riemannKernelReal_le_sharp` and
   `riemannKernelReal_ge_sharp` from base point `a - L`, as `a → ∞` the shifted ground-state collar
   `shiftDifference a x * shiftDifference a (L - x)` satisfies
   - Outside `|x - L / 2| < δ`:
     `m_a(x) m_a(L - x) ≤ Φ(a - L)² exp(2π e^{2(a - L)} + 5L - 2π e^{2a - L} cosh(2δ))`.
   - Inside `|y - L / 2| ≤ δ / 2`:
     `m_a(y) m_a(L - y) ≥ (1/4) Φ(a - L)² exp(2π e^{2(a - L)} - 4π L - 2π e^{2a - L} cosh δ)`.
   The base factor `Φ(a - L)² exp(2π e^{2(a - L)})` cancels identically between the two bounds, and
   since `cosh(2δ) > cosh δ` for `δ > 0`, the collar concentrates at the midpoint `L / 2` with
   double-exponential speed `exp(-2π e^{2a - L} (cosh(2δ) - cosh δ))`. Consequently, for every
   `n ≥ 2`:
   - `∀ᶠ a in atTop, collarAtomMass (shiftDifference a) n < collarPolarMass (shiftDifference a) n`
     if and only if `∃ a > 0, collarAtomMass (shiftDifference a) n < collarPolarMass (shiftDifference a) n`
     if and only if `n ∉ atomDominatedModuli = {2, 3, 4, 5, 7}` (paying both `11` and `13`).

3. **The Axis-Decay Law and First-Jet Log-Concave Classification
   (`firstJetAtomDominatedModuli`, `integral_mul_sub_crossingPolarWeight`,
   `collarPolarMass_id_sub_collarAtomMass_id`, `collarAtomMass_id_lt_collarPolarMass_id_thirteen`,
   `collarPolarMass_id_lt_collarAtomMass_id_eleven`,
   `collarAtomMass_lt_collarPolarMass_of_div_id_logConcave`,
   `forall_div_id_logConcave_collarAtomMass_lt_iff`):**
   An odd `C¹` gauge `M` vanishes at the origin (`M(0) = 0`), so its collar product `M(x) M(L - x)`
   carries the parabolic axis-vanishing factor `x(L - x)`. For the linear gauge `M(x) = x`:
   - `∫₀ᴸ x(L - x) dx = L³ / 6` and
     `∫₀ᴸ x(L - x) P_L(x) dx = (L³ / 6 - 2L) cosh(L / 2) + 4 sinh(L / 2)`.
   - `12 √n (collarPolarMass id n - collarAtomMass id n) = L³ (n + 1 - 2Λ(n)) - 12L(n + 1) + 24(n - 1)`.
   - At `n = 13` (`L = log 13`), the right-hand side factors over `ℤ` as
     `2(3 - L)(4 - L)(12 - L²) > 0`, so `collarAtomMass id 13 < collarPolarMass id 13`.
   - At `n = 11` (`L = log 11`), the right-hand side equals
     `18(4 - L)² - 2(L(3 - L))² - 48 < 0`, so `collarPolarMass id 11 < collarAtomMass id 11`.
   - For the class of continuous gauges `M` with `0 < M x` and `x ↦ log(M x / x)` concave on
     `(0, log n)`, the pole pays the atom of every such gauge if and only if
     `n ∉ firstJetAtomDominatedModuli = {2, 3, 4, 5, 7, 11}`. This establishes the exact three-tier
     axis-decay hierarchy `{2, 3, 4, 5, 7, 11, 13} ⊃ {2, 3, 4, 5, 7, 11} ⊃ {2, 3, 4, 5, 7}`.

4. **Two-Sided Deficit Bounds and Interior Lattice Crossing Vanishing on `{2, 3, 4, 5, 7}`
   (`collarAtomMass_sub_collarPolarMass_bounds`,
   `interior_lattice_crossing_of_mem_atomDominatedModuli_eq_two_two`,
   `reflectedDifferenceJump_four_midpoint_eq_zero`):**
   For `n ∈ {2, 3, 4, 5, 7}`, every nonnegative gauge leaves a positive integrated atom deficit
   bounded between `(vonMangoldtAtom n - 2 sinh(log n / 4)²) ∫ M(x) M(L - x)` and
   `vonMangoldtAtom n ∫ M(x) M(L - x)`. Moreover, the only interior lattice crossing pair `(a, b)`
   (`a, b ≥ 2`) with `a * b ∈ {2, 3, 4, 5, 7}` is `(2, 2)` (`a * b = 4`), which sits at the
   anti-diagonal midpoint `x = log 2 = log 4 / 2` where the reflected difference jump
   `reflectedDifferenceJump ω u (log 4) (log 2)` vanishes identically for every gauge `ω` and
   test `u`. Thus the five moduli `{2, 3, 4, 5, 7}` are paid not by their own anti-diagonal pole
   or interior lattice crossings, but by the prime-ratio atoms (`4/3`, `3/2`, `5/4`, `7/5`) and
   shared archimedean strip derivative energy.
-/

open MeasureTheory Set Filter Topology Real
open RHTower RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ## 1. Strict Midpoint Payment Outside `{2, 3, 4, 5, 7}` -/

/-- For every `n ≥ 2` with `n ∉ atomDominatedModuli = {2, 3, 4, 5, 7}`, the polar weight at the
anti-diagonal midpoint `log n / 2` strictly exceeds `vonMangoldtAtom n`. -/
theorem vonMangoldtAtom_lt_crossingPolarWeight_midpoint_of_not_mem {n : ℕ} (hn : 2 ≤ n)
    (hn5 : n ∉ atomDominatedModuli) :
    vonMangoldtAtom n < crossingPolarWeight (Real.log n) (Real.log n / 2) := by
  by_cases h1113 : n = 11 ∨ n = 13
  · exact vonMangoldtAtom_lt_crossingPolarWeight_midpoint h1113
  · have hn7 : n ∉ integratedAtomDominatedModuli := by
      intro hmem
      simp only [integratedAtomDominatedModuli, atomDominatedModuli, Finset.mem_insert,
        Finset.mem_singleton] at hmem hn5 h1113
      omega
    have hlt : collarAtomMass (fun _ => 1) n < collarPolarMass (fun _ => 1) n :=
      collarAtomMass_lt_collarPolarMass_of_logConcave continuous_const hn hn7
        (fun _ _ => one_pos)
        (by simpa using concaveOn_const (𝕜 := ℝ) (0 : ℝ) (convex_Ioo (0 : ℝ) (Real.log n)))
    have hle := collarPolarMass_le_midpoint_mul_integral continuous_const
      (fun _ _ => zero_le_one) n
    have hI : ∫ x in Ioo (0 : ℝ) (Real.log n), (1 : ℝ) * 1 = Real.log n := by
      have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      simp only [mul_one]
      rw [setIntegral_Ioo_eq_intervalIntegral hL, intervalIntegral.integral_const, smul_eq_mul,
        sub_zero, mul_one]
    rw [hI] at hle
    rw [collarAtomMass_one] at hlt
    have hLpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    rw [crossingPolarWeight_midpoint]
    nlinarith

/-- **Complete Midpoint Payment Characterization.**
For `n ≥ 2`, `vonMangoldtAtom n < crossingPolarWeight (Real.log n) (Real.log n / 2)` if and only if
`n ∉ atomDominatedModuli = {2, 3, 4, 5, 7}`. -/
theorem vonMangoldtAtom_lt_crossingPolarWeight_midpoint_iff {n : ℕ} (hn : 2 ≤ n) :
    vonMangoldtAtom n < crossingPolarWeight (Real.log n) (Real.log n / 2) ↔
      n ∉ atomDominatedModuli := by
  constructor
  · intro hlt hmem
    exact lt_asymm hlt (crossingPolarWeight_lt_vonMangoldtAtom hmem (Real.log n / 2))
  · exact vonMangoldtAtom_lt_crossingPolarWeight_midpoint_of_not_mem hn

/-! ## 2. Shifted Ground-State Midpoint Concentration and Complete Integrated Classification -/

/-- Symmetric exponential sum identity along `x + (L - x) = L`:
`exp(2(a - x)) + exp(2(a - (L - x))) = 2 exp(2a - L) cosh(L - 2x)`. -/
theorem exp_two_sub_add_exp_two_sub_sub (a L x : ℝ) :
    Real.exp (2 * (a - x)) + Real.exp (2 * (a - (L - x))) =
      2 * Real.exp (2 * a - L) * Real.cosh (L - 2 * x) := by
  rw [Real.cosh_eq]
  have h1 : 2 * (a - x) = (2 * a - L) + (L - 2 * x) := by ring
  have h2 : 2 * (a - (L - x)) = (2 * a - L) + -(L - 2 * x) := by ring
  rw [h1, h2, Real.exp_add, Real.exp_add]
  ring

/-- `shiftDifference a x = Φ(a - x) - Φ(a + x)` by evenness of `riemannKernelReal`. -/
theorem shiftDifference_eq_sub (a x : ℝ) :
    shiftDifference a x = riemannKernelReal (a - x) - riemannKernelReal (a + x) := by
  unfold shiftDifference riemannKernelReal
  rw [abs_sub_comm, add_comm x a]

/-- **Outer Collar Upper Bound for Shifted Ground States.**
For `x ∈ [0, L]` with `|x - L / 2| ≥ δ ≥ 0` and `a ≥ L + log 3 / 2`, the collar product
`shiftDifference a x * shiftDifference a (L - x)` is bounded above by
`Φ(a - L)² exp(2π e^{2(a - L)} + 5L - 2π e^{2a - L} cosh(2δ))`. -/
theorem shiftDifference_collar_le_of_abs_sub_ge {a L δ x : ℝ}
    (ha : L + Real.log 3 / 2 ≤ a) (hδ : 0 ≤ δ) (hx : x ∈ Icc 0 L)
    (hxδ : δ ≤ |x - L / 2|) :
    shiftDifference a x * shiftDifference a (L - x) ≤
      riemannKernelReal (a - L) ^ 2 *
        Real.exp (2 * π * Real.exp (2 * (a - L)) + 5 * L -
          2 * π * Real.exp (2 * a - L) * Real.cosh (2 * δ)) := by
  have haL : Real.log 3 / 2 ≤ a - L := by linarith
  have ha0 : 0 < a := by
    have : 0 < Real.log 3 := Real.log_pos (by norm_num)
    linarith [hx.1, hx.2]
  have hmx0 : 0 ≤ shiftDifference a x := shiftDifference_nonneg_of_nonneg ha0.le hx.1
  have hmy0 : 0 ≤ shiftDifference a (L - x) :=
    shiftDifference_nonneg_of_nonneg ha0.le (by linarith [hx.2])
  have hmx_le : shiftDifference a x ≤ riemannKernelReal (a - x) := by
    rw [shiftDifference_eq_sub]
    linarith [riemannKernelReal_pos (a + x)]
  have hmy_le : shiftDifference a (L - x) ≤ riemannKernelReal (a - (L - x)) := by
    rw [shiftDifference_eq_sub]
    linarith [riemannKernelReal_pos (a + (L - x))]
  have h1 := riemannKernelReal_le_sharp haL (by linarith [hx.2] : a - L ≤ a - x)
  have h2 := riemannKernelReal_le_sharp haL (by linarith [hx.1] : a - L ≤ a - (L - x))
  have hΦaL := riemannKernelReal_pos (a - L)
  have hprod : shiftDifference a x * shiftDifference a (L - x) ≤
      riemannKernelReal (a - x) * riemannKernelReal (a - (L - x)) :=
    mul_le_mul hmx_le hmy_le hmy0 (riemannKernelReal_pos _).le
  have hprod2 : riemannKernelReal (a - x) * riemannKernelReal (a - (L - x)) ≤
      riemannKernelReal (a - L) ^ 2 *
        Real.exp (2 * π * Real.exp (2 * (a - L)) + 5 * L -
          π * (Real.exp (2 * (a - x)) + Real.exp (2 * (a - (L - x))))) := by
    calc riemannKernelReal (a - x) * riemannKernelReal (a - (L - x))
        ≤ (riemannKernelReal (a - L) *
            Real.exp (-(π * (Real.exp (2 * (a - x)) - Real.exp (2 * (a - L)))) +
              5 * ((a - x) - (a - L)))) *
          (riemannKernelReal (a - L) *
            Real.exp (-(π * (Real.exp (2 * (a - (L - x))) - Real.exp (2 * (a - L)))) +
              5 * ((a - (L - x)) - (a - L)))) :=
          mul_le_mul h1 h2 (riemannKernelReal_pos _).le (by positivity)
      _ = riemannKernelReal (a - L) ^ 2 *
            (Real.exp (-(π * (Real.exp (2 * (a - x)) - Real.exp (2 * (a - L)))) +
              5 * ((a - x) - (a - L))) *
            Real.exp (-(π * (Real.exp (2 * (a - (L - x))) - Real.exp (2 * (a - L)))) +
              5 * ((a - (L - x)) - (a - L)))) := by ring
      _ = _ := by
          rw [← Real.exp_add]
          congr 2
          ring
  have hcosh : Real.cosh (2 * δ) ≤ Real.cosh (L - 2 * x) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith : 0 ≤ 2 * δ)]
    have habs : |L - 2 * x| = 2 * |x - L / 2| := by
      rw [show L - 2 * x = -(2 * (x - L / 2)) by ring, abs_neg, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hexp : Real.exp (2 * π * Real.exp (2 * (a - L)) + 5 * L -
        π * (Real.exp (2 * (a - x)) + Real.exp (2 * (a - (L - x))))) ≤
      Real.exp (2 * π * Real.exp (2 * (a - L)) + 5 * L -
        2 * π * Real.exp (2 * a - L) * Real.cosh (2 * δ)) := by
    rw [exp_two_sub_add_exp_two_sub_sub, Real.exp_le_exp]
    have hπe : 0 ≤ 2 * π * Real.exp (2 * a - L) := by positivity
    nlinarith
  exact hprod.trans (hprod2.trans (mul_le_mul_of_nonneg_left hexp (sq_nonneg _)))

/-- For `z ∈ [L / 4, L]`, once `a ≥ L + log 2 / 2` and `log 2 ≤ π e^{2(a - L)} (L / 2)`,
`shiftDifference a z ≥ (1 / 2) Φ(a - z)`. -/
theorem half_mul_riemannKernelReal_le_shiftDifference {a L z : ℝ} (hL : 0 < L)
    (ha : L + Real.log 2 / 2 ≤ a) (hexp : Real.log 2 ≤ π * Real.exp (2 * (a - L)) * (L / 2))
    (hz1 : L / 4 ≤ z) (hz2 : z ≤ L) :
    1 / 2 * riemannKernelReal (a - z) ≤ shiftDifference a z := by
  have hs : Real.log 2 / 2 ≤ a - z := by linarith
  have hst : a - z ≤ a + z := by linarith
  have hle := riemannKernelReal_le_mul_exp hs hst
  have hprod : Real.log 2 ≤ π * Real.exp (2 * (a - z)) * ((a + z) - (a - z)) := by
    have he : Real.exp (2 * (a - L)) ≤ Real.exp (2 * (a - z)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h1 : π * Real.exp (2 * (a - L)) * (L / 2) ≤
        π * Real.exp (2 * (a - z)) * ((a + z) - (a - z)) := by
      have : L / 2 ≤ (a + z) - (a - z) := by linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left he Real.pi_pos.le) this (by positivity)
        (by positivity)
    exact hexp.trans h1
  have hexp_half : Real.exp (-(π * Real.exp (2 * (a - z)) * ((a + z) - (a - z)))) ≤ 1 / 2 := by
    calc Real.exp (-(π * Real.exp (2 * (a - z)) * ((a + z) - (a - z))))
        ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log two_pos, one_div]
  have hΦ := (riemannKernelReal_pos (a - z)).le
  have h2 : riemannKernelReal (a + z) ≤ riemannKernelReal (a - z) * (1 / 2) :=
    hle.trans (mul_le_mul_of_nonneg_left hexp_half hΦ)
  rw [shiftDifference_eq_sub]
  linarith

/-- **Inner Collar Lower Bound for Shifted Ground States.**
For `y` with `|y - L / 2| ≤ δ / 2` (`0 ≤ δ ≤ L / 2`), once `a ≥ L + log 2 / 2` and
`log 2 ≤ π e^{2(a - L)} (L / 2)`, the collar product `shiftDifference a y * shiftDifference a (L - y)`
is bounded below by `(1 / 4) Φ(a - L)² exp(2π e^{2(a - L)} - 4π L - 2π e^{2a - L} cosh δ)`. -/
theorem shiftDifference_collar_ge_of_abs_sub_le {a L δ y : ℝ} (hL : 0 < L)
    (ha : L + Real.log 2 / 2 ≤ a) (hexp : Real.log 2 ≤ π * Real.exp (2 * (a - L)) * (L / 2))
    (hδ0 : 0 ≤ δ) (hδL : δ ≤ L / 2) (hy : |y - L / 2| ≤ δ / 2) :
    1 / 4 * riemannKernelReal (a - L) ^ 2 *
        Real.exp (2 * π * Real.exp (2 * (a - L)) - 4 * π * L -
          2 * π * Real.exp (2 * a - L) * Real.cosh δ) ≤
      shiftDifference a y * shiftDifference a (L - y) := by
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hy_low : L / 4 ≤ y := by linarith
  have hy_high : y ≤ L := by linarith
  have hLy_low : L / 4 ≤ L - y := by linarith
  have hLy_high : L - y ≤ L := by linarith
  have hm1 := half_mul_riemannKernelReal_le_shiftDifference hL ha hexp hy_low hy_high
  have hm2 := half_mul_riemannKernelReal_le_shiftDifference hL ha hexp hLy_low hLy_high
  have haL0 : 0 ≤ a - L := by
    have : 0 ≤ Real.log 2 / 2 := by positivity
    linarith
  have hg1 := riemannKernelReal_ge_sharp haL0 (by linarith : a - L ≤ a - y)
  have hg2 := riemannKernelReal_ge_sharp haL0 (by linarith : a - L ≤ a - (L - y))
  have hΦaL := riemannKernelReal_pos (a - L)
  have hΦay := riemannKernelReal_pos (a - y)
  have hΦaLy := riemannKernelReal_pos (a - (L - y))
  have hcosh : Real.cosh (L - 2 * y) ≤ Real.cosh δ := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hδ0]
    have habs : |L - 2 * y| = 2 * |y - L / 2| := by
      rw [show L - 2 * y = -(2 * (y - L / 2)) by ring, abs_neg, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hexp_le : Real.exp (2 * π * Real.exp (2 * (a - L)) - 4 * π * L -
        2 * π * Real.exp (2 * a - L) * Real.cosh δ) ≤
      Real.exp (2 * π * Real.exp (2 * (a - L)) - 4 * π * L -
        π * (Real.exp (2 * (a - y)) + Real.exp (2 * (a - (L - y))))) := by
    rw [exp_two_sub_add_exp_two_sub_sub, Real.exp_le_exp]
    have hπe : 0 ≤ 2 * π * Real.exp (2 * a - L) := by positivity
    nlinarith
  calc 1 / 4 * riemannKernelReal (a - L) ^ 2 *
        Real.exp (2 * π * Real.exp (2 * (a - L)) - 4 * π * L -
          2 * π * Real.exp (2 * a - L) * Real.cosh δ)
      ≤ 1 / 4 * riemannKernelReal (a - L) ^ 2 *
        Real.exp (2 * π * Real.exp (2 * (a - L)) - 4 * π * L -
          π * (Real.exp (2 * (a - y)) + Real.exp (2 * (a - (L - y))))) :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
    _ = (1 / 2 * (riemannKernelReal (a - L) *
          Real.exp (-(π * (Real.exp (2 * (a - y)) - Real.exp (2 * (a - L)))) -
            4 * π * ((a - y) - (a - L))))) *
        (1 / 2 * (riemannKernelReal (a - L) *
          Real.exp (-(π * (Real.exp (2 * (a - (L - y))) - Real.exp (2 * (a - L)))) -
            4 * π * ((a - (L - y)) - (a - L))))) := by
        rw [show (1 / 2 * (riemannKernelReal (a - L) *
            Real.exp (-(π * (Real.exp (2 * (a - y)) - Real.exp (2 * (a - L)))) -
              4 * π * ((a - y) - (a - L))))) *
          (1 / 2 * (riemannKernelReal (a - L) *
            Real.exp (-(π * (Real.exp (2 * (a - (L - y))) - Real.exp (2 * (a - L)))) -
              4 * π * ((a - (L - y)) - (a - L))))) =
          1 / 4 * riemannKernelReal (a - L) ^ 2 *
            (Real.exp (-(π * (Real.exp (2 * (a - y)) - Real.exp (2 * (a - L)))) -
              4 * π * ((a - y) - (a - L))) *
            Real.exp (-(π * (Real.exp (2 * (a - (L - y))) - Real.exp (2 * (a - L)))) -
              4 * π * ((a - (L - y)) - (a - L)))) by ring, ← Real.exp_add]
        congr 2
        ring
    _ ≤ (1 / 2 * riemannKernelReal (a - y)) * (1 / 2 * riemannKernelReal (a - (L - y))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hg1 (by norm_num))
          (mul_le_mul_of_nonneg_left hg2 (by norm_num)) (by positivity) (by positivity)
    _ ≤ shiftDifference a y * shiftDifference a (L - y) :=
        mul_le_mul hm1 hm2 (by positivity) (le_trans (by positivity) hm1)

/-- Elementary constant lower bound for an interval integral of a continuous function. -/
theorem mul_sub_le_intervalIntegral_of_le {F : ℝ → ℝ} (hF : Continuous F) {u v c : ℝ}
    (huv : u ≤ v) (h : ∀ x ∈ Icc u v, c ≤ F x) :
    c * (v - u) ≤ ∫ x in u..v, F x := by
  have h1 := intervalIntegral.integral_mono_on huv (intervalIntegrable_const (μ := volume))
    (hF.intervalIntegrable u v) h
  rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h1

/-- Five-interval decomposition of `∫ x in 0..L, F x` around the midpoint `L / 2`. -/
theorem intervalIntegral_five_split {F : ℝ → ℝ} (hF : Continuous F) (L δ : ℝ) :
    ∫ x in (0 : ℝ)..L, F x =
      (∫ x in (0 : ℝ)..(L / 2 - δ), F x) +
      (∫ x in (L / 2 - δ)..(L / 2 - δ / 2), F x) +
      (∫ x in (L / 2 - δ / 2)..(L / 2 + δ / 2), F x) +
      (∫ x in (L / 2 + δ / 2)..(L / 2 + δ), F x) +
      (∫ x in (L / 2 + δ)..L, F x) := by
  have hi : ∀ u v, IntervalIntegrable F volume u v := fun u v => hF.intervalIntegrable u v
  rw [intervalIntegral.integral_add_adjacent_intervals (hi 0 (L / 2 - δ))
      (hi (L / 2 - δ) (L / 2 - δ / 2)),
    intervalIntegral.integral_add_adjacent_intervals (hi 0 (L / 2 - δ / 2))
      (hi (L / 2 - δ / 2) (L / 2 + δ / 2)),
    intervalIntegral.integral_add_adjacent_intervals (hi 0 (L / 2 + δ / 2))
      (hi (L / 2 + δ / 2) (L / 2 + δ)),
    intervalIntegral.integral_add_adjacent_intervals (hi 0 (L / 2 + δ))
      (hi (L / 2 + δ) L)]

/-- **Asymptotic Midpoint Concentration Positivity Law for Shifted Ground-State Collars.**
For any continuous function `g : ℝ → ℝ` on `(0, L)` (`L > 0`) with `0 < g (L / 2)`, the collar
integral `∫ x in Ioo 0 L, shiftDifference a x * shiftDifference a (L - x) * g x` is strictly
positive for all sufficiently large shifts `a`. -/
theorem eventually_shiftedGroundState_collar_integral_pos {g : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hg : Continuous g) (hmid : 0 < g (L / 2)) :
    ∀ᶠ a in atTop,
      0 < ∫ x in Ioo (0 : ℝ) L, shiftDifference a x * shiftDifference a (L - x) * g x := by
  set m := g (L / 2) / 2
  have hm : 0 < m := half_pos hmid
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff.mp
    (hg.continuousAt.eventually (lt_mem_nhds (half_lt_self hmid)))
  set δ := min (r₀ / 2) (L / 4)
  have hδ0 : 0 < δ := lt_min (half_pos hr₀) (by linarith)
  have hδL : δ ≤ L / 4 := min_le_right _ _
  have hδr : δ < r₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr₀)
  have hg_mid : ∀ x, |x - L / 2| ≤ δ → m ≤ g x := fun x hx =>
    (hball (by rw [Real.dist_eq]; exact lt_of_le_of_lt hx hδr)).le
  obtain ⟨x_min, -, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hg.continuousOn
  set B := max 1 (-g x_min)
  have hB0 : 0 < B := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hg_low : ∀ x ∈ Icc 0 L, -B ≤ g x := fun x hx => by
    have h1 : g x_min ≤ g x := hmin hx
    have h2 : -g x_min ≤ B := le_max_right _ _
    linarith
  have hcosh_diff : 0 < Real.cosh (2 * δ) - Real.cosh δ := by
    rw [sub_pos, Real.cosh_lt_cosh, abs_of_pos hδ0, abs_of_pos (by linarith)]
    linarith
  have hlim_exp : Tendsto (fun a : ℝ =>
      2 * π * Real.exp (2 * a - L) * (Real.cosh (2 * δ) - Real.cosh δ)) atTop atTop := by
    have h1 : Tendsto (fun a : ℝ => 2 * a - L) atTop atTop :=
      tendsto_atTop_add_const_right _ (-L) (Tendsto.const_mul_atTop two_pos tendsto_id)
    have h2 := Real.tendsto_exp_atTop.comp h1
    exact (Tendsto.const_mul_atTop (mul_pos two_pos Real.pi_pos) h2).atTop_mul_const hcosh_diff
  have hlim_zero : Tendsto (fun a : ℝ =>
      L * B * Real.exp (5 * L + 4 * π * L) *
        Real.exp (-(2 * π * Real.exp (2 * a - L) * (Real.cosh (2 * δ) - Real.cosh δ))))
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlim_exp).const_mul
      (L * B * Real.exp (5 * L + 4 * π * L))
  have hlim_log2 : Tendsto (fun a : ℝ => π * Real.exp (2 * (a - L)) * (L / 2)) atTop atTop := by
    have h1 : Tendsto (fun a : ℝ => 2 * (a - L)) atTop atTop :=
      Tendsto.const_mul_atTop two_pos (tendsto_atTop_add_const_right _ (-L) tendsto_id)
    exact (Tendsto.const_mul_atTop Real.pi_pos (Real.tendsto_exp_atTop.comp h1)).atTop_mul_const
      (half_pos hL)
  filter_upwards [eventually_ge_atTop (L + Real.log 3 / 2),
    eventually_ge_atTop (L + Real.log 2 / 2),
    hlim_log2.eventually_ge_atTop (Real.log 2),
    hlim_zero.eventually (gt_mem_nhds (show (0 : ℝ) < δ * m * (1 / 4) by positivity))]
    with a ha3 ha2 hexp hsmall
  rw [setIntegral_Ioo_eq_intervalIntegral hL.le]
  set F : ℝ → ℝ := fun x => shiftDifference a x * shiftDifference a (L - x) * g x
  have hF : Continuous F :=
    ((continuous_shiftDifference a).mul
      ((continuous_shiftDifference a).comp (continuous_const.sub continuous_id))).mul hg
  have hΦaL := riemannKernelReal_pos (a - L)
  set C₀ := riemannKernelReal (a - L) ^ 2 * Real.exp (2 * π * Real.exp (2 * (a - L)))
  have hC₀ : 0 < C₀ := by positivity
  set M_out := C₀ * Real.exp (5 * L - 2 * π * Real.exp (2 * a - L) * Real.cosh (2 * δ))
  set M_in := 1 / 4 * C₀ * Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ)
  have hM_out : ∀ x ∈ Icc 0 L, δ ≤ |x - L / 2| →
      shiftDifference a x * shiftDifference a (L - x) ≤ M_out := fun x hx hxδ => by
    have h := shiftDifference_collar_le_of_abs_sub_ge ha3 hδ0.le hx hxδ
    have heq : M_out = riemannKernelReal (a - L) ^ 2 *
        Real.exp (2 * π * Real.exp (2 * (a - L)) + 5 * L -
          2 * π * Real.exp (2 * a - L) * Real.cosh (2 * δ)) := by
      dsimp [M_out, C₀]
      rw [mul_assoc, ← Real.exp_add]
      congr 2; ring
    rwa [heq]
  have hM_in : ∀ x, |x - L / 2| ≤ δ / 2 →
      M_in ≤ shiftDifference a x * shiftDifference a (L - x) := fun x hx => by
    have h := shiftDifference_collar_ge_of_abs_sub_le hL ha2 hexp hδ0.le (by linarith) hx
    have heq : M_in = 1 / 4 * riemannKernelReal (a - L) ^ 2 *
        Real.exp (2 * π * Real.exp (2 * (a - L)) - 4 * π * L -
          2 * π * Real.exp (2 * a - L) * Real.cosh δ) := by
      dsimp [M_in, C₀]
      rw [show 1 / 4 * (riemannKernelReal (a - L) ^ 2 * Real.exp (2 * π * Real.exp (2 * (a - L)))) *
          Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) =
        1 / 4 * riemannKernelReal (a - L) ^ 2 *
          (Real.exp (2 * π * Real.exp (2 * (a - L))) *
            Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ)) by ring,
        ← Real.exp_add]
      congr 2; ring
    rwa [heq]
  have ha0 : 0 < a := by
    have : 0 < Real.log 2 := Real.log_pos one_lt_two
    linarith
  have hcoll_nn : ∀ x ∈ Icc 0 L, 0 ≤ shiftDifference a x * shiftDifference a (L - x) :=
    fun x hx => mul_nonneg (shiftDifference_nonneg_of_nonneg ha0.le hx.1)
      (shiftDifference_nonneg_of_nonneg ha0.le (by linarith [hx.2]))
  have hI1 : -(B * M_out) * (L / 2 - δ - 0) ≤ ∫ x in (0 : ℝ)..(L / 2 - δ), F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxL : x ∈ Icc 0 L := ⟨hx.1, by linarith [hx.2]⟩
    have hxδ : δ ≤ |x - L / 2| := by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2]
    have h1 := hM_out x hxL hxδ
    have h2 := hg_low x hxL
    have h3 := hcoll_nn x hxL
    dsimp [F]
    nlinarith
  have hI2 : 0 * (L / 2 - δ / 2 - (L / 2 - δ)) ≤ ∫ x in (L / 2 - δ)..(L / 2 - δ / 2), F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxL : x ∈ Icc 0 L := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxδ : |x - L / 2| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (hcoll_nn x hxL) (hm.le.trans (hg_mid x hxδ))
  have hI3 : (m * M_in) * (L / 2 + δ / 2 - (L / 2 - δ / 2)) ≤
      ∫ x in (L / 2 - δ / 2)..(L / 2 + δ / 2), F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxδ2 : |x - L / 2| ≤ δ / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxδ : |x - L / 2| ≤ δ := hxδ2.trans (by linarith)
    have h1 := hM_in x hxδ2
    have h2 := hg_mid x hxδ
    dsimp [F]
    nlinarith [show 0 ≤ M_in by positivity]
  have hI4 : 0 * (L / 2 + δ - (L / 2 + δ / 2)) ≤ ∫ x in (L / 2 + δ / 2)..(L / 2 + δ), F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxL : x ∈ Icc 0 L := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxδ : |x - L / 2| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (hcoll_nn x hxL) (hm.le.trans (hg_mid x hxδ))
  have hI5 : -(B * M_out) * (L - (L / 2 + δ)) ≤ ∫ x in (L / 2 + δ)..L, F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxL : x ∈ Icc 0 L := ⟨by linarith [hx.1], hx.2⟩
    have hxδ : δ ≤ |x - L / 2| := by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.1]
    have h1 := hM_out x hxL hxδ
    have h2 := hg_low x hxL
    have h3 := hcoll_nn x hxL
    dsimp [F]
    nlinarith
  rw [intervalIntegral_five_split hF L δ]
  have hdiff_pos : 0 < δ * (m * M_in) - L * (B * M_out) := by
    have hrel : L * (B * M_out) =
        C₀ * Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) *
          (L * B * Real.exp (5 * L + 4 * π * L) *
            Real.exp (-(2 * π * Real.exp (2 * a - L) * (Real.cosh (2 * δ) - Real.cosh δ)))) := by
      dsimp [M_out]
      rw [show C₀ * Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) *
          (L * B * Real.exp (5 * L + 4 * π * L) *
            Real.exp (-(2 * π * Real.exp (2 * a - L) * (Real.cosh (2 * δ) - Real.cosh δ)))) =
          L * B * C₀ * (Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) *
            Real.exp (5 * L + 4 * π * L) *
            Real.exp (-(2 * π * Real.exp (2 * a - L) * (Real.cosh (2 * δ) - Real.cosh δ)))) by ring,
        ← Real.exp_add, ← Real.exp_add]
      ring_nf
    have hin_rel : δ * (m * M_in) =
        C₀ * Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) *
          (δ * m * (1 / 4)) := by
      dsimp [M_in]
      ring
    rw [hin_rel, hrel, ← mul_sub]
    exact mul_pos (by positivity) (sub_pos.mpr hsmall)
  have hBM : 0 ≤ B * M_out := by positivity
  nlinarith

/-- **Asymptotic Shifted Ground-State Payment Outside `{2, 3, 4, 5, 7}`.**
For every integer `n ≥ 2` with `n ∉ atomDominatedModuli = {2, 3, 4, 5, 7}`, the shifted ground-state
gauge `shiftDifference a` pays the atom of `n` for all sufficiently large shifts `a`. -/
theorem eventually_collarAtomMass_lt_collarPolarMass_of_not_mem {n : ℕ} (hn : 2 ≤ n)
    (hn5 : n ∉ atomDominatedModuli) :
    ∀ᶠ a in atTop,
      collarAtomMass (shiftDifference a) n < collarPolarMass (shiftDifference a) n := by
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hmid := vonMangoldtAtom_lt_crossingPolarWeight_midpoint_of_not_mem hn hn5
  have hg : Continuous fun x => crossingPolarWeight (Real.log n) x - vonMangoldtAtom n :=
    (continuous_crossingPolarWeight _).sub continuous_const
  have hev := eventually_shiftedGroundState_collar_integral_pos hL hg (sub_pos.mpr hmid)
  filter_upwards [hev] with a ha
  rw [← sub_pos, collarPolarMass_sub_collarAtomMass (continuous_shiftDifference a)]
  exact ha

/-- **Complete Asymptotic Shifted Ground-State Classification.**
For `n ≥ 2`, `collarAtomMass (shiftDifference a) n < collarPolarMass (shiftDifference a) n` holds
for all sufficiently large shifts `a` if and only if `n ∉ atomDominatedModuli = {2, 3, 4, 5, 7}`. -/
theorem eventually_collarAtomMass_lt_collarPolarMass_iff {n : ℕ} (hn : 2 ≤ n) :
    (∀ᶠ a in atTop,
      collarAtomMass (shiftDifference a) n < collarPolarMass (shiftDifference a) n) ↔
      n ∉ atomDominatedModuli := by
  constructor
  · intro hev hmem
    obtain ⟨a, ha1, ha2⟩ := (hev.and (eventually_gt_atTop (0 : ℝ))).exists
    exact lt_asymm ha1 (collarPolarMass_lt_collarAtomMass_of_mem_atomDominatedModuli ha2 hmem).2.2
  · exact eventually_collarAtomMass_lt_collarPolarMass_of_not_mem hn

/-- **Complete Existential Shifted Ground-State Classification.**
For `n ≥ 2`, there exists a positive shift `a > 0` such that `shiftDifference a` pays the atom of
`n` (`collarAtomMass (shiftDifference a) n < collarPolarMass (shiftDifference a) n`) if and only if
`n ∉ atomDominatedModuli = {2, 3, 4, 5, 7}`. -/
theorem exists_collarAtomMass_lt_collarPolarMass_shiftedGroundState_iff {n : ℕ} (hn : 2 ≤ n) :
    (∃ a > 0, collarAtomMass (shiftDifference a) n < collarPolarMass (shiftDifference a) n) ↔
      n ∉ atomDominatedModuli := by
  constructor
  · rintro ⟨a, ha, hlt⟩ hmem
    exact lt_asymm hlt (collarPolarMass_lt_collarAtomMass_of_mem_atomDominatedModuli ha hmem).2.2
  · intro hn5
    obtain ⟨a, ha1, ha2⟩ :=
      ((eventually_collarAtomMass_lt_collarPolarMass_of_not_mem hn hn5).and
        (eventually_gt_atTop (0 : ℝ))).exists
    exact ⟨a, ha2, ha1⟩

/-! ## 3. The Axis-Decay Law and First-Jet Log-Concave Classification -/

/-- The six moduli `{2, 3, 4, 5, 7, 11}` whose atom is not paid by every first-jet log-concave
gauge (`x ↦ log(M x / x)` concave on `(0, log n)`). -/
def firstJetAtomDominatedModuli : Finset ℕ := {2, 3, 4, 5, 7, 11}

/-- Exact parabolic collar integral `∫₀ᴸ x(L - x) dx = L³ / 6`. -/
theorem integral_mul_sub_self (L : ℝ) :
    ∫ x in (0 : ℝ)..L, x * (L - x) = L ^ 3 / 6 := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) L, HasDerivAt
      (fun y => L * y ^ 2 / 2 - y ^ 3 / 3) (x * (L - x)) x := by
    intro x _
    have h1 := ((hasDerivAt_id' x).pow 2).const_mul L |>.div_const 2
    have h2 := ((hasDerivAt_id' x).pow 3).div_const 3
    exact (h1.sub h2).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_id.mul (continuous_const.sub continuous_id)).intervalIntegrable 0 L)]
  ring

/-- **Exact Parabolic Polar Integral.**
`∫₀ᴸ x(L - x) P_L(x) dx = (L³ / 6 - 2L) cosh(L / 2) + 4 sinh(L / 2)`. -/
theorem integral_mul_sub_crossingPolarWeight (L : ℝ) :
    ∫ x in (0 : ℝ)..L, x * (L - x) * crossingPolarWeight L x =
      (L ^ 3 / 6 - 2 * L) * Real.cosh (L / 2) + 4 * Real.sinh (L / 2) := by
  set G : ℝ → ℝ := fun y =>
    Real.cosh (L / 2) * (L * y ^ 2 / 2 - y ^ 3 / 3) +
      (y * (L - y) - 2) * Real.sinh (L / 2 - y) +
      (L - 2 * y) * Real.cosh (L / 2 - y)
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) L, HasDerivAt G (x * (L - x) * crossingPolarWeight L x) x := by
    intro x _
    rw [crossingPolarWeight_eq]
    have h1 : HasDerivAt (fun y => Real.cosh (L / 2) * (L * y ^ 2 / 2 - y ^ 3 / 3))
        (Real.cosh (L / 2) * (x * (L - x))) x := by
      have hp1 := ((hasDerivAt_id' x).pow 2).const_mul L |>.div_const 2
      have hp2 := ((hasDerivAt_id' x).pow 3).div_const 3
      exact ((hp1.sub hp2).const_mul (Real.cosh (L / 2))).congr_deriv (by ring)
    have h2 : HasDerivAt (fun y => (y * (L - y) - 2) * Real.sinh (L / 2 - y))
        ((L - 2 * x) * Real.sinh (L / 2 - x) +
          (x * (L - x) - 2) * (-Real.cosh (L / 2 - x))) x := by
      have hp : HasDerivAt (fun y => y * (L - y) - 2) (L - 2 * x) x :=
        (((hasDerivAt_id' x).mul ((hasDerivAt_id' x).const_sub L)).sub_const 2).congr_deriv (by ring)
      have hs : HasDerivAt (fun y => Real.sinh (L / 2 - y)) (-Real.cosh (L / 2 - x)) x :=
        (((hasDerivAt_id' x).const_sub (L / 2)).sinh).congr_deriv (by ring)
      exact hp.mul hs
    have h3 : HasDerivAt (fun y => (L - 2 * y) * Real.cosh (L / 2 - y))
        (-2 * Real.cosh (L / 2 - x) + (L - 2 * x) * (-Real.sinh (L / 2 - x))) x := by
      have hp : HasDerivAt (fun y => L - 2 * y) (-2) x :=
        (((hasDerivAt_id' x).const_mul 2).const_sub L).congr_deriv (by ring)
      have hc : HasDerivAt (fun y => Real.cosh (L / 2 - y)) (-Real.sinh (L / 2 - x)) x :=
        (((hasDerivAt_id' x).const_sub (L / 2)).cosh).congr_deriv (by ring)
      exact hp.mul hc
    exact ((h1.add h2).add h3).congr_deriv (by ring)
  have hcont : Continuous fun x => x * (L - x) * crossingPolarWeight L x :=
    (continuous_id.mul (continuous_const.sub continuous_id)).mul (continuous_crossingPolarWeight L)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 L)]
  dsimp [G]
  simp only [sub_zero, show L / 2 - L = -(L / 2) by ring, Real.sinh_neg, Real.cosh_neg]
  ring

/-- Exact closed form of `collarAtomMass id n` and `collarPolarMass id n`. -/
theorem collarAtomMass_id (n : ℕ) :
    collarAtomMass id n = vonMangoldtAtom n * (Real.log n ^ 3 / 6) := by
  unfold collarAtomMass id
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [vonMangoldtAtom]
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [setIntegral_Ioo_eq_intervalIntegral hL, integral_mul_sub_self]

theorem collarPolarMass_id (n : ℕ) :
    collarPolarMass id n =
      (Real.log n ^ 3 / 6 - 2 * Real.log n) * Real.cosh (Real.log n / 2) +
        4 * Real.sinh (Real.log n / 2) := by
  unfold collarPolarMass id
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [setIntegral_Ioo_eq_intervalIntegral hL, integral_mul_sub_crossingPolarWeight]

/-- **Algebraic Identity for the Parabolic Collar Surplus.**
For `n ≥ 2` and `L = log n`:
`12 √n (collarPolarMass id n - collarAtomMass id n) = L³ (n + 1 - 2Λ(n)) - 12L(n + 1) + 24(n - 1)`. -/
theorem collarPolarMass_id_sub_collarAtomMass_id {n : ℕ} (hn : 2 ≤ n) :
    12 * Real.sqrt n * (collarPolarMass id n - collarAtomMass id n) =
      Real.log n ^ 3 * ((n : ℝ) + 1 - 2 * ArithmeticFunction.vonMangoldt n) -
        12 * Real.log n * ((n : ℝ) + 1) + 24 * ((n : ℝ) - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hcosh, hsinh⟩ := cosh_sinh_log_div_two (n := n) (by omega)
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
  have hss : Real.sqrt n * (Real.sqrt n)⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
  rw [collarPolarMass_id, collarAtomMass_id]
  unfold vonMangoldtAtom
  rw [if_pos hn, hcosh, hsinh]
  calc 12 * Real.sqrt n * (((Real.log n ^ 3 / 6 - 2 * Real.log n) *
        ((Real.sqrt n + (Real.sqrt n)⁻¹) / 2) +
          4 * ((Real.sqrt n - (Real.sqrt n)⁻¹) / 2)) -
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * (Real.log n ^ 3 / 6))
      = Real.log n ^ 3 * (Real.sqrt n ^ 2 + Real.sqrt n * (Real.sqrt n)⁻¹ -
          2 * ArithmeticFunction.vonMangoldt n * (Real.sqrt n * (Real.sqrt n)⁻¹)) -
        12 * Real.log n * (Real.sqrt n ^ 2 + Real.sqrt n * (Real.sqrt n)⁻¹) +
        24 * (Real.sqrt n ^ 2 - Real.sqrt n * (Real.sqrt n)⁻¹) := by ring
    _ = _ := by rw [hs2, hss]; ring

/-- **At `n = 13`, the linear gauge `M(x) = x` pays the atom (`collarAtomMass id 13 < collarPolarMass id 13`).**
With `L = log 13`, `12 √13 (collarPolarMass id 13 - collarAtomMass id 13) = 2(3 - L)(4 - L)(12 - L²) > 0`. -/
theorem collarAtomMass_id_lt_collarPolarMass_id_thirteen :
    collarAtomMass id 13 < collarPolarMass id 13 := by
  have h := collarPolarMass_id_sub_collarAtomMass_id (n := 13) (by norm_num)
  rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)] at h
  push_cast at h
  have hfac : Real.log 13 ^ 3 * (13 + 1 - 2 * Real.log 13) -
      12 * Real.log 13 * (13 + 1) + 24 * (13 - 1) =
      2 * (3 - Real.log 13) * (4 - Real.log 13) * (12 - Real.log 13 ^ 2) := by ring
  rw [hfac] at h
  have h16 : Real.log 13 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
  rw [log_sixteen_eq] at h16
  have hl2 := Real.log_two_lt_d9
  have hL0 : 0 < Real.log 13 := Real.log_pos (by norm_num)
  have hL28 : Real.log 13 < 2.8 := by linarith
  have h12 : 0 < 12 - Real.log 13 ^ 2 := by nlinarith
  have hpos : 0 < 2 * (3 - Real.log 13) * (4 - Real.log 13) * (12 - Real.log 13 ^ 2) :=
    mul_pos (mul_pos (mul_pos two_pos (by linarith)) (by linarith)) h12
  have hs0 : 0 < 12 * Real.sqrt 13 := by positivity
  rw [← sub_pos]
  by_contra hle
  push Not at hle
  have := mul_nonpos_of_nonneg_of_nonpos hs0.le hle
  linarith

/-- **At `n = 11`, the linear gauge `M(x) = x` leaves the atom unpaid
(`collarPolarMass id 11 < collarAtomMass id 11`).**
With `L = log 11`, `12 √11 (collarPolarMass id 11 - collarAtomMass id 11) = 18(4 - L)² - 2(L(3 - L))² - 48 < 0`. -/
theorem collarPolarMass_id_lt_collarAtomMass_id_eleven :
    collarPolarMass id 11 < collarAtomMass id 11 := by
  have h := collarPolarMass_id_sub_collarAtomMass_id (n := 11) (by norm_num)
  rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)] at h
  push_cast at h
  have hfac : Real.log 11 ^ 3 * (11 + 1 - 2 * Real.log 11) -
      12 * Real.log 11 * (11 + 1) + 24 * (11 - 1) =
      18 * (4 - Real.log 11) ^ 2 - 2 * (Real.log 11 * (3 - Real.log 11)) ^ 2 - 48 := by ring
  rw [hfac] at h
  have hrat := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 128 / 121 by norm_num)
  have hrat_eq : Real.log (128 / 121 : ℝ) = 7 * Real.log 2 - 2 * Real.log 11 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (128 : ℝ) = 2 ^ 7 by norm_num, show (121 : ℝ) = 11 ^ 2 by norm_num,
      Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hrat_eq] at hrat
  have hl2 := Real.log_two_gt_d9
  have hLlow : 2.397 < Real.log 11 := by linarith
  have h16 : Real.log 11 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
  rw [log_sixteen_eq] at h16
  have hl2' := Real.log_two_lt_d9
  have hLup : Real.log 11 < 2.8 := by linarith
  have h4L : (4 - Real.log 11) ^ 2 < 1.603 ^ 2 := by nlinarith
  have hneg : 18 * (4 - Real.log 11) ^ 2 - 2 * (Real.log 11 * (3 - Real.log 11)) ^ 2 - 48 < 0 := by
    nlinarith [sq_nonneg (Real.log 11 * (3 - Real.log 11))]
  have hs0 : 0 < 12 * Real.sqrt 11 := by positivity
  by_contra hle
  push Not at hle
  have := mul_nonneg hs0.le (sub_nonneg.mpr hle)
  linarith

/-- Every `n ∈ firstJetAtomDominatedModuli = {2, 3, 4, 5, 7, 11}` leaves the atom of the linear
gauge `id` unpaid (`collarPolarMass id n < collarAtomMass id n`). -/
theorem collarPolarMass_id_lt_collarAtomMass_id_of_mem {n : ℕ}
    (hn : n ∈ firstJetAtomDominatedModuli) :
    collarPolarMass id n < collarAtomMass id n := by
  by_cases h5 : n ∈ atomDominatedModuli
  · have hn2 := two_le_of_mem_atomDominatedModuli h5
    have hmid := crossingPolarWeight_lt_vonMangoldtAtom h5 (Real.log n / 2)
    rw [crossingPolarWeight_midpoint] at hmid
    have hle := collarPolarMass_le_midpoint_mul_integral continuous_id (fun _ hx => hx.le) n
    have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hI : ∫ x in Ioo (0 : ℝ) (Real.log n), id x * id (Real.log n - x) = Real.log n ^ 3 / 6 := by
      change ∫ x in Ioo (0 : ℝ) (Real.log n), x * (Real.log n - x) = Real.log n ^ 3 / 6
      rw [setIntegral_Ioo_eq_intervalIntegral hL.le, integral_mul_sub_self]
    rw [hI] at hle
    rw [collarAtomMass_id]
    have hL3 : 0 < Real.log n ^ 3 / 6 := by positivity
    nlinarith
  · have h11 : n = 11 := by
      simp only [firstJetAtomDominatedModuli, atomDominatedModuli, Finset.mem_insert,
        Finset.mem_singleton] at hn h5
      omega
    subst h11
    exact collarPolarMass_id_lt_collarAtomMass_id_eleven

/-- If `x ↦ log(M x / x)` is concave on `(0, L)` and `0 < M x` on `(0, L)`, then `x ↦ log(M x)`
is also concave on `(0, L)`. -/
theorem concaveOn_log_of_concaveOn_log_div_id {M : ℝ → ℝ} {L : ℝ}
    (hpos : ∀ x ∈ Ioo 0 L, 0 < M x)
    (hcc : ConcaveOn ℝ (Ioo 0 L) fun x => Real.log (M x / x)) :
    ConcaveOn ℝ (Ioo 0 L) fun x => Real.log (M x) := by
  have hlog : ConcaveOn ℝ (Ioo 0 L) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn.subset Ioo_subset_Ioi_self (convex_Ioo 0 L)
  refine (hcc.add hlog).congr fun x hx => ?_
  simp only [Pi.add_apply]
  rw [Real.log_div (hpos x hx).ne' hx.1.ne', sub_add_cancel]

/-- **First-Jet Log-Concave Payment Theorem.**
For every integer `n ≥ 2` with `n ∉ firstJetAtomDominatedModuli = {2, 3, 4, 5, 7, 11}` and every
continuous gauge `M` that is positive on `(0, log n)` with `x ↦ log(M x / x)` concave on
`(0, log n)`, the pole pays the atom (`collarAtomMass M n < collarPolarMass M n`). -/
theorem collarAtomMass_lt_collarPolarMass_of_div_id_logConcave {M : ℝ → ℝ} (hM : Continuous M)
    {n : ℕ} (hn : 2 ≤ n) (hn6 : n ∉ firstJetAtomDominatedModuli)
    (hpos : ∀ x ∈ Ioo 0 (Real.log n), 0 < M x)
    (hcc : ConcaveOn ℝ (Ioo 0 (Real.log n)) fun x => Real.log (M x / x)) :
    collarAtomMass M n < collarPolarMass M n := by
  by_cases h13 : n = 13
  · subst h13
    rw [← sub_pos, collarPolarMass_sub_collarAtomMass hM]
    set L := Real.log (13 : ℕ) with hL_def
    have hL : 0 < L := Real.log_pos (by norm_num)
    set q : ℝ → ℝ := fun x => M x / x
    have hq_pos : ∀ x ∈ Ioo 0 L, 0 < q x := fun x hx => div_pos (hpos x hx) hx.1
    have hmid : vonMangoldtAtom 13 < crossingPolarWeight L (L / 2) :=
      vonMangoldtAtom_lt_crossingPolarWeight_midpoint (Or.inr rfl)
    have hw : Continuous fun x => crossingPolarWeight L x - vonMangoldtAtom 13 :=
      (continuous_crossingPolarWeight L).sub continuous_const
    have hzero : crossingPolarWeight L 0 = 0 := by simp [crossingPolarWeight]
    have hc_pos : 0 < vonMangoldtAtom 13 := by
      unfold vonMangoldtAtom
      rw [if_pos (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
      positivity
    obtain ⟨x₀, ⟨hx₀0, hx₀m⟩, hx₀⟩ : ∃ x₀ ∈ Icc (0 : ℝ) (L / 2),
        crossingPolarWeight L x₀ - vonMangoldtAtom 13 = 0 := by
      have h := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ L / 2) hw.continuousOn
      exact h ⟨by rw [hzero]; linarith, by linarith⟩
    have hx₀pos : 0 < x₀ := by
      rcases eq_or_lt_of_le hx₀0 with h | h
      · rw [← h, hzero] at hx₀; linarith
      · exact h
    have hx₀I : x₀ ∈ Ioo 0 L := ⟨hx₀pos, by linarith⟩
    have hq₀ : 0 < q x₀ * q (L - x₀) :=
      mul_pos (hq_pos x₀ hx₀I) (hq_pos (L - x₀) ⟨by linarith, by linarith⟩)
    have hpt : ∀ x ∈ Ioo 0 L,
        q x₀ * q (L - x₀) * (x * (L - x) * (crossingPolarWeight L x - vonMangoldtAtom 13)) ≤
          M x * M (L - x) * (crossingPolarWeight L x - vonMangoldtAtom 13) := by
      intro x hx
      have hMx : M x * M (L - x) * (crossingPolarWeight L x - vonMangoldtAtom 13) =
          q x * q (L - x) * (x * (L - x) * (crossingPolarWeight L x - vonMangoldtAtom 13)) := by
        dsimp [q]
        have hx1 : x ≠ 0 := hx.1.ne'
        have hx2 : L - x ≠ 0 := (sub_pos.mpr hx.2).ne'
        field_simp
      rw [hMx]
      have hxLx : 0 ≤ x * (L - x) := mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)
      by_cases h : |x - L / 2| ≤ |x₀ - L / 2|
      · have hq_le := collar_le_collar_of_abs_le hq_pos hcc hx₀I h
        have hwx : 0 ≤ crossingPolarWeight L x - vonMangoldtAtom 13 := by
          have hc' : Real.cosh (L / 2 - x) ≤ Real.cosh (L / 2 - x₀) := by
            rw [Real.cosh_le_cosh, abs_sub_comm, abs_sub_comm (L / 2)]; exact h
          rw [crossingPolarWeight_eq] at hx₀ ⊢
          linarith
        exact mul_le_mul_of_nonneg_right hq_le (mul_nonneg hxLx hwx)
      · push Not at h
        have hq_le := collar_le_collar_of_abs_le hq_pos hcc hx h.le
        have hwx : crossingPolarWeight L x - vonMangoldtAtom 13 ≤ 0 := by
          have hc' : Real.cosh (L / 2 - x₀) ≤ Real.cosh (L / 2 - x) := by
            rw [Real.cosh_le_cosh, abs_sub_comm, abs_sub_comm (L / 2)]; exact h.le
          rw [crossingPolarWeight_eq] at hx₀ ⊢
          linarith
        exact mul_le_mul_of_nonpos_right hq_le (mul_nonpos_of_nonneg_of_nonpos hxLx hwx)
    have hid_pos : 0 < ∫ x in Ioo (0 : ℝ) L,
        id x * id (L - x) * (crossingPolarWeight L x - vonMangoldtAtom 13) := by
      rw [← collarPolarMass_sub_collarAtomMass continuous_id 13]
      exact sub_pos.mpr collarAtomMass_id_lt_collarPolarMass_id_thirteen
    have hint₀ : IntegrableOn (fun x => q x₀ * q (L - x₀) *
        (x * (L - x) * (crossingPolarWeight L x - vonMangoldtAtom 13))) (Ioo (0 : ℝ) L) :=
      (continuous_const.mul ((continuous_id.mul (continuous_const.sub continuous_id)).mul
        hw)).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hint : IntegrableOn (fun x => M x * M (L - x) *
        (crossingPolarWeight L x - vonMangoldtAtom 13)) (Ioo (0 : ℝ) L) :=
      ((hM.mul (hM.comp (continuous_const.sub continuous_id))).mul
        hw).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    calc (0 : ℝ) < q x₀ * q (L - x₀) * ∫ x in Ioo (0 : ℝ) L,
          x * (L - x) * (crossingPolarWeight L x - vonMangoldtAtom 13) := mul_pos hq₀ hid_pos
      _ = ∫ x in Ioo (0 : ℝ) L, q x₀ * q (L - x₀) *
            (x * (L - x) * (crossingPolarWeight L x - vonMangoldtAtom 13)) :=
          (integral_const_mul _ _).symm
      _ ≤ _ := setIntegral_mono_on hint₀ hint measurableSet_Ioo hpt
  · have hn7 : n ∉ integratedAtomDominatedModuli := by
      intro hmem
      simp only [integratedAtomDominatedModuli, firstJetAtomDominatedModuli, Finset.mem_insert,
        Finset.mem_singleton] at hmem hn6 h13
      omega
    exact collarAtomMass_lt_collarPolarMass_of_logConcave hM hn hn7 hpos
      (concaveOn_log_of_concaveOn_log_div_id hpos hcc)

/-- **Complete Classification for First-Jet Log-Concave Gauges.**
For `n ≥ 2`, the pole pays the atom of every continuous gauge `M` with `0 < M x` and
`x ↦ log(M x / x)` concave on `(0, log n)` if and only if
`n ∉ firstJetAtomDominatedModuli = {2, 3, 4, 5, 7, 11}`. -/
theorem forall_div_id_logConcave_collarAtomMass_lt_iff {n : ℕ} (hn : 2 ≤ n) :
    (∀ M : ℝ → ℝ, Continuous M → (∀ x ∈ Ioo 0 (Real.log n), 0 < M x) →
        ConcaveOn ℝ (Ioo 0 (Real.log n)) (fun x => Real.log (M x / x)) →
          collarAtomMass M n < collarPolarMass M n) ↔
      n ∉ firstJetAtomDominatedModuli := by
  constructor
  · intro h hmem
    have hcc_id : ConcaveOn ℝ (Ioo 0 (Real.log n)) (fun x : ℝ => Real.log (id x / x)) := by
      refine (concaveOn_const (𝕜 := ℝ) (0 : ℝ) (convex_Ioo 0 (Real.log n))).congr fun x hx => ?_
      rw [id, div_self hx.1.ne', Real.log_one]
    have h1 := h id continuous_id (fun _ hx => hx.1) hcc_id
    exact lt_asymm h1 (collarPolarMass_id_lt_collarAtomMass_id_of_mem hmem)
  · intro hn6 M hM hpos hcc
    exact collarAtomMass_lt_collarPolarMass_of_div_id_logConcave hM hn hn6 hpos hcc

/-! ## 4. Two-Sided Deficit Bounds and Interior Lattice Crossing Vanishing on `{2, 3, 4, 5, 7}` -/

/-- **Two-Sided Integrated Atom Deficit Bounds on `{2, 3, 4, 5, 7}`.**
For every `n ∈ atomDominatedModuli = {2, 3, 4, 5, 7}` and every continuous gauge `M` that is
nonnegative on `(0, log n)`, the integrated atom deficit `collarAtomMass M n - collarPolarMass M n`
satisfies
`0 ≤ (vonMangoldtAtom n - 2 sinh(log n / 4)²) ∫ M(x) M(log n - x) ≤ collarAtomMass M n - collarPolarMass M n ≤ vonMangoldtAtom n ∫ M(x) M(log n - x)`. -/
theorem collarAtomMass_sub_collarPolarMass_bounds {M : ℝ → ℝ} (hM : Continuous M)
    (hnn : ∀ x, 0 < x → 0 ≤ M x) {n : ℕ} (hn : n ∈ atomDominatedModuli) :
    0 ≤ (vonMangoldtAtom n - 2 * Real.sinh (Real.log n / 4) ^ 2) *
        (∫ x in Ioo (0 : ℝ) (Real.log n), M x * M (Real.log n - x)) ∧
    (vonMangoldtAtom n - 2 * Real.sinh (Real.log n / 4) ^ 2) *
        (∫ x in Ioo (0 : ℝ) (Real.log n), M x * M (Real.log n - x)) ≤
      collarAtomMass M n - collarPolarMass M n ∧
    collarAtomMass M n - collarPolarMass M n ≤
      vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n), M x * M (Real.log n - x) := by
  have hmid := crossingPolarWeight_lt_vonMangoldtAtom hn (Real.log n / 2)
  rw [crossingPolarWeight_midpoint] at hmid
  have hI_nn : 0 ≤ ∫ x in Ioo (0 : ℝ) (Real.log n), M x * M (Real.log n - x) :=
    setIntegral_nonneg measurableSet_Ioo fun x hx =>
      mul_nonneg (hnn x hx.1) (hnn _ (sub_pos.mpr hx.2))
  have hle := collarPolarMass_le_midpoint_mul_integral hM hnn n
  have hpol_nn : 0 ≤ collarPolarMass M n := by
    unfold collarPolarMass
    refine setIntegral_nonneg measurableSet_Ioo fun x hx =>
      mul_nonneg (mul_nonneg (hnn x hx.1) (hnn _ (sub_pos.mpr hx.2)))
        (crossingPolarWeight_nonneg hx.1.le hx.2.le)
  unfold collarAtomMass
  exact ⟨mul_nonneg (sub_nonneg.mpr hmid.le) hI_nn, by linarith, by linarith⟩

/-- **Unique Interior Lattice Crossing on `{2, 3, 4, 5, 7}`.**
Among all pairs of integers `a, b ≥ 2`, the product `a * b` belongs to
`atomDominatedModuli = {2, 3, 4, 5, 7}` if and only if `a = 2 ∧ b = 2` (`a * b = 4`). -/
theorem interior_lattice_crossing_of_mem_atomDominatedModuli_eq_two_two {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    a * b ∈ atomDominatedModuli ↔ a = 2 ∧ b = 2 := by
  constructor
  · intro hmem
    simp only [atomDominatedModuli, Finset.mem_insert, Finset.mem_singleton] at hmem
    have ha7 : a ≤ 7 := by
      have : a * 2 ≤ a * b := Nat.mul_le_mul_left a hb
      omega
    have hb7 : b ≤ 7 := by
      have : 2 * b ≤ a * b := Nat.mul_le_mul_right b ha
      omega
    interval_cases a <;> interval_cases b <;> omega
  · rintro ⟨rfl, rfl⟩
    simp [atomDominatedModuli]

/-- **Midpoint Vanishing of the Interior Lattice Crossing Jump at `n = 4 = 2 × 2`.**
The unique interior lattice crossing `(log 2, log 2)` on the anti-diagonals of `{2, 3, 4, 5, 7}`
lies at the anti-diagonal midpoint `log 2 = log 4 / 2`, where `reflectedDifferenceJump` vanishes
identically for every gauge `ω` and test `u`. -/
theorem reflectedDifferenceJump_four_midpoint_eq_zero (ω u : ℝ → ℝ) :
    reflectedDifferenceJump ω u (Real.log (4 : ℕ)) (Real.log (2 : ℕ)) = 0 := by
  unfold reflectedDifferenceJump
  have hlog4 : Real.log (4 : ℕ) = 2 * Real.log (2 : ℕ) := by
    push_cast
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [hlog4, show 2 * Real.log (2 : ℕ) - Real.log (2 : ℕ) = Real.log (2 : ℕ) by ring]
  ring

end GaloisForLFunctions.ArithmeticIncidencePositivity
