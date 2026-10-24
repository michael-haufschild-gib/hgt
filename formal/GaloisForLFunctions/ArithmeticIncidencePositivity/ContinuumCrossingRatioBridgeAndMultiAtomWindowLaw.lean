import GaloisForLFunctions.ArithmeticIncidencePositivity.ShiftedGroundStateAndFirstJetAtomPoleLaw
import GaloisForLFunctions.ArithmeticIncidencePositivity.QuarterPointClassification
import GaloisForLFunctions.ArithmeticIncidencePositivity.FirstOpenWindowTwoAtomLaw
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeCombEnergyReduction
import GaloisForLFunctions.ArithmeticIncidencePositivity.ReflectedPrimePolarAllocation

/-!
# Continuum Crossing Pairs, the Same-Side Ratio Bridge, and Multi-Atom Window Laws

For a crossing pair `(-a, log n - a)` at a lattice point (`a = log d`, `d ∣ n`), the divisor-lattice
Gram identity absorbs the anti-diagonal crossing term into the diagonal variance at `d` and `n / d`
and the same-side ratio correlation at `n / d²`. For a **continuum crossing pair** `(-a, log n - a)`
with `a ∈ (0, log n)` between lattice points, `e^a` is not an integer divisor of `n`. This module
establishes the complete four-part theory pricing continuum crossing pairs by the polar weight,
the variance, and the same-side ratio correlations reachable from them:

1. **Exact Polar Payment Zone and Cubic Lipschitz Suppression on the Unpaid Axis Intervals:**
   For every prime power `n ∉ atomDominatedModuli = {2, 3, 4, 5, 7}` with `Λ(n) > 0`, the atom
   `Λ(n) n^{-1/2}` lies strictly below the midpoint polar weight `P_{log n}(½ log n)`. Consequently,
   there is a threshold `c_n ∈ (0, ½ log n)` with `P_{log n}(c_n) = Λ(n) n^{-1/2}` such that the
   polar weight pays the continuum crossing atom pointwise at every `a ∈ [c_n, log n - c_n]`, and
   the unpaid set of the atom is the union of two symmetric axis intervals `(0, c_n) ∪ (log n - c_n, log n)`
   with inner end `ℓ_n^atom = 2 Λ(n) / (n - 1)` (`unpaidSet_vonMangoldtAtom_eq`,
   `vonMangoldtAtom_paid_on_middle_interval`, `unpaidInnerEnd_vonMangoldtAtom_eq`). On any unpaid
   axis interval `[0, c]`, every odd `K`-Lipschitz test `F` satisfies
   `∫_0^c F(a)² da ≤ K² c³ / 3` (`integral_unpaidAxis_sq_le_cube`) and
   `2 ∫_0^c F(a) F(L - a) da ≤ γ⁻¹ K² c³ / 3 + γ ∫_{L - c}^L F(a)² da`
   (`two_mul_integral_unpaidAxis_crossing_le`), suppressing the near-axis crossing mass cubically in `c`.

2. **Pointwise and Integrated Continuum Crossing-to-Ratio Bridge:**
   At any continuum crossing pair `(-a, L - a)` (`L = log n`) and for any intermediate point
   `y' = a + log m` at a same-side ratio shift `log m` reachable from `a`, the harmonic-mean
   decomposition of `(F(a) - F(L - a))²` across `F(a + log m)` gives, for every `θ > 0`,
   `4 α_{F, L}(a)² ≤ (1 + θ)(F(a) - F(a + log m))² + (1 + θ⁻¹)(F(a + log m) - F(L - a))²`
   (`reflectedOddPart_sq_le_ratio_arch_step`). For odd `F`, combining this with the exact identity
   `2 F(-a) F(L - a) + (F(a)² + F(L - a)²) = 4 α_{F, L}(a)²` prices the continuum crossing product
   `2 F(-a) F(L - a)` at every `a ∈ ℝ` by the **variance** `F(a)² + F(L - a)²`, the **same-side
   ratio jump** `(F(a) - F(a + log m))²` at lag `log m`, and the **archimedean same-side jump**
   `(F(a + log m) - F(L - a))²` at distance `|L - log m - 2a|`
   (`continuum_crossing_le_variance_and_ratio_arch`). Integrating over `a ∈ [log n - r, r]` yields
   the strip-level bridge (`oddStripCost_le_ratio_and_arch_shift`).

3. **Weighted Two-Atom Ratio-Lag Law and Complete Two-Prime Window Certificates (`r = 23/40`):**
   Evaluating the discriminant of the three-shift Gram form `three_shift_gram` along the ray
   `(λ, μ) = (θ w₁, θ w₂)` yields the **weighted two-atom ratio-lag law** (`sq_weighted_two_atom_le`):
   `(w₁ A_F(a) + w₂ A_F(b))² ≤ A_F(0) ((w₁² + w₂²) A_F(0) + 2 w₁ w₂ A_F(b - a))`,
   together with its sign-flipped companion (`sq_weighted_two_atom_sub_le`) and the exact
   ratio-free polarization ceiling (`sq_weighted_two_atom_polarization`):
   `(w₁ A_F(a) + w₂ A_F(b))² + (w₁ A_F(a) - w₂ A_F(b))² ≤ 2 (w₁² + w₂²) A_F(0)²`.
   At `r = 23/40` (`relevantShifts (23/40) = {2, 3}`), this prices `primeSideCharge F` directly by
   the mass `A_F(0)` and the single same-side ratio lag `A_F(log 3 - log 2)`
   (`sq_primeSideCharge_twentyThreeFortieths_le`), and combining the overlapping-strip Harnack
   allocation with the incidence ledger gives the complete two-prime full-zero-form certificate
   (`fullZeroForm_ge_twentyThreeFortieths_complete`).

4. **All-Aperture Multi-Atom Ratio-Comb Pricing of the Ledger:**
   At any aperture `r > 0`, `primeSideCharge F = ∑_{n ∈ relevantShifts r} Λ(n) n^{-1/2} A_F(log n)`,
   so Cauchy–Schwarz on the prime comb prices the squared prime-side crossing charge by the mass
   `A_F(0)` times the diagonal variance `(∑ Λ_n²) A_F(0)` plus the **same-side ratio correlation sum**
   `∑_{n ≠ m} Λ_n Λ_m A_F(log m - log n)` (`sq_primeSideCharge_le_mass_mul_combEnergy`,
   `fullZeroForm_ge_incidenceBudget_sub_combEnergy`).
-/

open MeasureTheory Set Filter Topology
open scoped ArithmeticFunction
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ## Part I: Exact Polar Payment Zone and Cubic Lipschitz Suppression on the Unpaid Axis Intervals -/

/-- The inner endpoint of the unpaid set for the anti-diagonal atom `Λ(n) n^{-1/2}` alone is
`2 Λ(n) / (n - 1)`. -/
theorem unpaidInnerEnd_vonMangoldtAtom_eq {n : ℕ} (hn : 2 ≤ n) :
    unpaidInnerEnd (Real.log n) (vonMangoldtAtom n) =
      2 * ArithmeticFunction.vonMangoldt n / ((n : ℝ) - 1) := by
  unfold unpaidInnerEnd vonMangoldtAtom
  rw [if_pos hn, sinh_half_log_nat (by omega)]
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hne : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- On the middle interval `[c, s - c]` between the symmetric threshold points where
`P_s(c) = E`, the polar weight pays the level `E` pointwise. -/
theorem level_paid_on_middle_interval {s E c a : ℝ}
    (hc : crossingPolarWeight s c = E) (ha1 : c ≤ a) (ha2 : a ≤ s - c) :
    E ≤ crossingPolarWeight s a := by
  rcases le_total a (s / 2) with hhalf | hhalf
  · rw [← hc]
    exact crossingPolarWeight_mono ha1 hhalf
  · rw [← hc, ← crossingPolarWeight_symm s a]
    exact crossingPolarWeight_mono (by linarith) (by linarith)

/-- **Exact Continuum Polar Payment Zone for the Anti-Diagonal Atom.** For every `n ≥ 2` outside
`atomDominatedModuli = {2, 3, 4, 5, 7}` with `0 < Λ(n)`, there exists a threshold
`c ∈ (0, ½ log n)` where `P_{log n}(c) = Λ(n) n^{-1/2}` such that:
1. The unpaid set of the atom is the union of the two symmetric axis intervals
   `(0, c) ∪ (log n - c, log n)`.
2. At every continuum point `a ∈ [c, log n - c]`, the polar weight pays the atom pointwise:
   `Λ(n) n^{-1/2} ≤ P_{log n}(a)`. -/
theorem unpaidSet_vonMangoldtAtom_eq {n : ℕ} (hn2 : 2 ≤ n)
    (hn : n ∉ atomDominatedModuli) (hΛ : 0 < ArithmeticFunction.vonMangoldt n) :
    ∃ c, 0 < c ∧ c < Real.log n / 2 ∧
      crossingPolarWeight (Real.log n) c = vonMangoldtAtom n ∧
      unpaidSet (Real.log n) (vonMangoldtAtom n) =
        Ioo 0 c ∪ Ioo (Real.log n - c) (Real.log n) ∧
      ∀ a, c ≤ a → a ≤ Real.log n - c →
        vonMangoldtAtom n ≤ crossingPolarWeight (Real.log n) a := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hs : 0 < Real.log n := Real.log_pos hn1
  have hE0 : 0 < vonMangoldtAtom n := by
    unfold vonMangoldtAtom
    rw [if_pos hn2]
    exact div_pos hΛ (Real.sqrt_pos.mpr (by linarith))
  have hEm : vonMangoldtAtom n < crossingPolarWeight (Real.log n) (Real.log n / 2) :=
    vonMangoldtAtom_lt_crossingPolarWeight_midpoint_of_not_mem hn2 hn
  obtain ⟨c, hc0, hcm, hceq, hunpaid⟩ := unpaidSet_eq_of_le_midpoint hs hE0 hEm.le
  have hclt : c < Real.log n / 2 :=
    lt_of_le_of_ne hcm (ne_of_apply_ne (crossingPolarWeight (Real.log n)) (by linarith))
  exact ⟨c, hc0, hclt, hceq, hunpaid, fun a ha1 ha2 => level_paid_on_middle_interval hceq ha1 ha2⟩

/-- **Cubic Lipschitz Suppression of the Axis Mass.** For any continuous function `F : ℝ → ℝ`
satisfying `|F a| ≤ K * a` on `[0, c]` (`0 ≤ c`) — in particular for any odd `K`-Lipschitz
test (`F 0 = 0`) — the `L²` mass on the axis interval `[0, c]` is at most `K² c³ / 3`. -/
theorem integral_unpaidAxis_sq_le_cube {F : ℝ → ℝ} {K c : ℝ} (hF : Continuous F)
    (hc : 0 ≤ c) (hLip : ∀ a ∈ Icc (0 : ℝ) c, |F a| ≤ K * a) :
    (∫ a in (0 : ℝ)..c, F a ^ 2) ≤ K ^ 2 * c ^ 3 / 3 := by
  have hpt : ∀ a ∈ Icc (0 : ℝ) c, F a ^ 2 ≤ K ^ 2 * a ^ 2 := by
    intro a ha
    have h1 := hLip a ha
    have h2 : |F a| ^ 2 ≤ (K * a) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at h2
    linarith [show (K * a) ^ 2 = K ^ 2 * a ^ 2 by ring]
  have hmono : (∫ a in (0 : ℝ)..c, F a ^ 2) ≤ ∫ a in (0 : ℝ)..c, K ^ 2 * a ^ 2 :=
    intervalIntegral.integral_mono_on hc ((hF.pow 2).intervalIntegrable 0 c)
      ((continuous_const.mul (continuous_pow 2)).intervalIntegrable 0 c) hpt
  have hint : (∫ a in (0 : ℝ)..c, K ^ 2 * a ^ 2) = K ^ 2 * c ^ 3 / 3 := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    ring
  linarith

/-- For an odd `K`-Lipschitz function `F`, `|F a| ≤ K * a` for all `a ≥ 0`. -/
theorem abs_le_mul_of_odd_lipschitz {F : ℝ → ℝ} {K : ℝ} (hodd : ∀ x, F (-x) = -F x)
    (hLip : ∀ a b, |F a - F b| ≤ K * |a - b|) {a : ℝ} (ha : 0 ≤ a) :
    |F a| ≤ K * a := by
  have h0 : F 0 = 0 := by have := hodd 0; rw [neg_zero] at this; linarith
  have h := hLip a 0
  rwa [h0, sub_zero, sub_zero, abs_of_nonneg ha] at h

/-- **Cubic Lipschitz Suppression of Continuum Crossing Charge on the Unpaid Axis Intervals.**
For any continuous odd `K`-Lipschitz test `F : ℝ → ℝ`, any `0 ≤ c`, any shift `L : ℝ`, and any
weight `γ > 0`, the continuum crossing integral on the axis interval `[0, c]` obeys
`2 ∫_0^c F(a) F(L - a) da ≤ γ⁻¹ (K² c³ / 3) + γ ∫_{L - c}^L F(a)² da`. -/
theorem two_mul_integral_unpaidAxis_crossing_le {F : ℝ → ℝ} {K c L γ : ℝ}
    (hF : Continuous F) (hodd : ∀ x, F (-x) = -F x)
    (hLip : ∀ a b, |F a - F b| ≤ K * |a - b|)
    (hc : 0 ≤ c) (hγ : 0 < γ) :
    2 * (∫ a in (0 : ℝ)..c, F a * F (L - a)) ≤
      γ⁻¹ * (K ^ 2 * c ^ 3 / 3) + γ * (∫ a in (L - c)..L, F a ^ 2) := by
  have hpt : ∀ a ∈ Icc (0 : ℝ) c,
      2 * (F a * F (L - a)) ≤ γ⁻¹ * F a ^ 2 + γ * F (L - a) ^ 2 := by
    intro a _
    have hsq : 0 ≤ (F a - γ * F (L - a)) ^ 2 := sq_nonneg _
    have hid : γ⁻¹ * F a ^ 2 + γ * F (L - a) ^ 2 - 2 * (F a * F (L - a)) =
        γ⁻¹ * (F a - γ * F (L - a)) ^ 2 := by
      have hne : γ ≠ 0 := hγ.ne'
      field_simp
      ring
    have hpos : 0 ≤ γ⁻¹ * (F a - γ * F (L - a)) ^ 2 :=
      mul_nonneg (inv_nonneg.mpr hγ.le) hsq
    linarith
  have hi1 : IntervalIntegrable (fun a => 2 * (F a * F (L - a))) volume 0 c :=
    (continuous_const.mul (hF.mul (hF.comp (continuous_const.sub continuous_id)))).intervalIntegrable 0 c
  have hi2a : IntervalIntegrable (fun a => γ⁻¹ * F a ^ 2) volume 0 c :=
    (continuous_const.mul (hF.pow 2)).intervalIntegrable 0 c
  have hi2b : IntervalIntegrable (fun a => γ * F (L - a) ^ 2) volume 0 c :=
    (continuous_const.mul ((hF.comp (continuous_const.sub continuous_id)).pow 2)).intervalIntegrable 0 c
  have hmono := intervalIntegral.integral_mono_on hc hi1 (hi2a.add hi2b) hpt
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi2a hi2b,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  have href : (∫ a in (0 : ℝ)..c, F (L - a) ^ 2) = ∫ a in (L - c)..L, F a ^ 2 := by
    have := intervalIntegral.integral_comp_sub_left (fun x => F x ^ 2) L (a := 0) (b := c)
    simpa [sub_zero] using this
  have hcube : (∫ a in (0 : ℝ)..c, F a ^ 2) ≤ K ^ 2 * c ^ 3 / 3 :=
    integral_unpaidAxis_sq_le_cube hF hc fun a ha => abs_le_mul_of_odd_lipschitz hodd hLip ha.1
  rw [href] at hmono
  have hmul := mul_le_mul_of_nonneg_left hcube (inv_nonneg.mpr hγ.le)
  linarith

/-! ## Part II: Pointwise and Integrated Continuum Crossing-to-Ratio Bridge -/

/-- **Harmonic-Mean / Young Step for Two Jumps.** For any weights `A, B ≥ 0` with `0 < A + B`
and any three real numbers `u, w, v`,
`(A * B / (A + B)) * (u - v)² ≤ A * (u - w)² + B * (w - v)²`. -/
theorem sq_sub_le_harmonic_step {A B : ℝ} (hAB : 0 < A + B) (u w v : ℝ) :
    A * B / (A + B) * (u - v) ^ 2 ≤ A * (u - w) ^ 2 + B * (w - v) ^ 2 := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hAB]
  have hid : (A * (u - w) ^ 2 + B * (w - v) ^ 2) * (A + B) - A * B * (u - v) ^ 2 =
      (A * (u - w) - B * (w - v)) ^ 2 := by ring
  linarith [sq_nonneg (A * (u - w) - B * (w - v))]

/-- **Parameterized Two-Step Jump Inequality.** For every `θ > 0` and `u, w, v : ℝ`,
`(u - v)² ≤ (1 + θ) * (u - w)² + (1 + θ⁻¹) * (w - v)²`. -/
theorem sq_sub_le_one_add_mul {θ : ℝ} (hθ : 0 < θ) (u w v : ℝ) :
    (u - v) ^ 2 ≤ (1 + θ) * (u - w) ^ 2 + (1 + θ⁻¹) * (w - v) ^ 2 := by
  have h := sq_sub_le_harmonic_step (A := 1 + θ) (B := 1 + θ⁻¹) (by positivity) u w v
  have h1 : (1 + θ) * (1 + θ⁻¹) / (1 + θ + (1 + θ⁻¹)) = 1 := by
    have hne : θ ≠ 0 := hθ.ne'
    have hden : 1 + θ + (1 + θ⁻¹) ≠ 0 := by positivity
    rw [div_eq_one_iff_eq hden]
    field_simp
    ring
  rwa [h1, one_mul] at h

/-- **Pointwise Reflected-Odd-Part Ratio Bridge.** At every continuum point `a ∈ ℝ`, for every
shift `L : ℝ`, every intermediate ratio shift `log m`, and every `θ > 0`, the reflected odd part
`4 * reflectedOddPart F L a ^ 2 = (F a - F (L - a))²` is bounded by the same-side ratio jump
`(F a - F (a + log m))²` at lag `log m` and the archimedean jump `(F (a + log m) - F (L - a))²`
at distance `|L - log m - 2a|`:
`4 * reflectedOddPart F L a ^ 2 ≤ (1 + θ) * (F a - F (a + log m))² + (1 + θ⁻¹) * (F (a + log m) - F (L - a))²`. -/
theorem reflectedOddPart_sq_le_ratio_arch_step (F : ℝ → ℝ) (L : ℝ) (m : ℕ) {θ : ℝ}
    (hθ : 0 < θ) (a : ℝ) :
    4 * reflectedOddPart F L a ^ 2 ≤
      (1 + θ) * (F a - F (a + Real.log m)) ^ 2 +
        (1 + θ⁻¹) * (F (a + Real.log m) - F (L - a)) ^ 2 := by
  have h1 : 4 * reflectedOddPart F L a ^ 2 = (F a - F (L - a)) ^ 2 := by
    unfold reflectedOddPart; ring
  rw [h1]
  exact sq_sub_le_one_add_mul hθ (F a) (F (a + Real.log m)) (F (L - a))

/-- **Pointwise Continuum Crossing-to-Ratio Bridge.** For an odd function `F : ℝ → ℝ`, at every
continuum crossing pair `(-a, L - a)` (`a ∈ ℝ`), for every ratio modulus `m : ℕ` and every `θ > 0`,
the crossing product `2 * F (-a) * F (L - a)` plus the pair variance `F a ^ 2 + F (L - a) ^ 2`
is bounded by the same-side ratio jump at lag `log m` and the archimedean jump between `a + log m`
and `L - a`:
`2 * F (-a) * F (L - a) + (F a ^ 2 + F (L - a) ^ 2) ≤ (1 + θ) * (F a - F (a + log m))² + (1 + θ⁻¹) * (F (a + log m) - F (L - a))²`. -/
theorem continuum_crossing_le_variance_and_ratio_arch {F : ℝ → ℝ}
    (hodd : ∀ x, F (-x) = -F x) (L : ℝ) (m : ℕ) {θ : ℝ} (hθ : 0 < θ) (a : ℝ) :
    2 * F (-a) * F (L - a) + (F a ^ 2 + F (L - a) ^ 2) ≤
      (1 + θ) * (F a - F (a + Real.log m)) ^ 2 +
        (1 + θ⁻¹) * (F (a + Real.log m) - F (L - a)) ^ 2 := by
  have hid : 2 * F (-a) * F (L - a) + (F a ^ 2 + F (L - a) ^ 2) =
      4 * reflectedOddPart F L a ^ 2 := by
    rw [hodd a]
    unfold reflectedOddPart
    ring
  rw [hid]
  exact reflectedOddPart_sq_le_ratio_arch_step F L m hθ a

/-- **Integrated Odd-Strip Cost Ratio Bridge.** For any continuous `F : ℝ → ℝ`, any shift `n : ℕ`
with `log n ≤ 2 * r`, any ratio modulus `m : ℕ`, and any `θ > 0`, the odd strip cost `oddStripCost F r n`
on `S_n = [log n - r, r]` is bounded by the same-side ratio jump integral at lag `log m` and the
archimedean jump integral along `a + log m ↔ log n - a`:
`oddStripCost F r n ≤ vonMangoldtAtom n * ((1 + θ) * ∫_{S_n} (F(a) - F(a + log m))² da + (1 + θ⁻¹) * ∫_{S_n} (F(a + log m) - F(log n - a))² da)`. -/
theorem oddStripCost_le_ratio_and_arch_shift {F : ℝ → ℝ} (hF : Continuous F) {r : ℝ}
    {n : ℕ} (hn : Real.log n ≤ 2 * r) (m : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    oddStripCost F r n ≤
      vonMangoldtAtom n *
        ((1 + θ) * (∫ a in (Real.log n - r)..r, (F a - F (a + Real.log m)) ^ 2) +
          (1 + θ⁻¹) * (∫ a in (Real.log n - r)..r, (F (a + Real.log m) - F (Real.log n - a)) ^ 2)) := by
  have hlr : Real.log n - r ≤ r := by linarith
  have hi0 : IntervalIntegrable (fun a => 4 * reflectedOddPart F (Real.log n) a ^ 2)
      volume (Real.log n - r) r := by
    have hc : Continuous fun a => 4 * reflectedOddPart F (Real.log n) a ^ 2 := by
      unfold reflectedOddPart
      exact continuous_const.mul (((hF.sub (hF.comp (continuous_const.sub continuous_id))).div_const 2).pow 2)
    exact hc.intervalIntegrable _ _
  have hi1 : IntervalIntegrable (fun a => (1 + θ) * (F a - F (a + Real.log m)) ^ 2)
      volume (Real.log n - r) r :=
    (continuous_const.mul ((hF.sub (hF.comp (continuous_id.add continuous_const))).pow 2)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun a => (1 + θ⁻¹) * (F (a + Real.log m) - F (Real.log n - a)) ^ 2)
      volume (Real.log n - r) r :=
    (continuous_const.mul (((hF.comp (continuous_id.add continuous_const)).sub
      (hF.comp (continuous_const.sub continuous_id))).pow 2)).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on hlr hi0 (hi1.add hi2)
    fun a _ => reflectedOddPart_sq_le_ratio_arch_step F (Real.log n) m hθ a
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  have hcost : oddStripCost F r n =
      vonMangoldtAtom n * (4 * ∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2) := by
    unfold oddStripCost; ring
  rw [hcost]
  exact mul_le_mul_of_nonneg_left hmono (vonMangoldtAtom_nonneg n)

/-! ## Part III: Weighted Two-Atom Ratio-Lag Law and Complete Two-Prime Window Certificates -/

/-- **The Weighted Two-Atom Ratio-Lag Law.** For any continuous compactly supported test `F : ℝ → ℝ`,
any weights `w₁, w₂ : ℝ`, and any shifts `a, b : ℝ`,
`(w₁ * autoCorr F a + w₂ * autoCorr F b)² ≤ autoCorr F 0 * ((w₁² + w₂²) * autoCorr F 0 + 2 * w₁ * w₂ * autoCorr F (b - a))`.
This extends `sq_two_atom_le` to arbitrary atomic weights `(w₁, w₂)` (such as the Euler weights
`(Λ(2)/√2, Λ(3)/√3)` in the two-prime window), pricing the weighted two-atom crossing bill by the
mass `A_F(0)` and the free same-side ratio correlation `A_F(b - a)`. -/
theorem sq_weighted_two_atom_le {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (w₁ w₂ a b : ℝ) :
    (w₁ * autoCorr F a + w₂ * autoCorr F b) ^ 2 ≤
      autoCorr F 0 * ((w₁ ^ 2 + w₂ ^ 2) * autoCorr F 0 + 2 * w₁ * w₂ * autoCorr F (b - a)) := by
  have hquad : ∀ θ : ℝ, 0 ≤
      ((w₁ ^ 2 + w₂ ^ 2) * autoCorr F 0 + 2 * w₁ * w₂ * autoCorr F (b - a)) * (θ * θ) +
        (-2 * (w₁ * autoCorr F a + w₂ * autoCorr F b)) * θ + autoCorr F 0 := by
    intro θ
    have h := three_shift_gram hF hFc (θ * w₁) (θ * w₂) a b
    linarith [h, show (1 + (θ * w₁) ^ 2 + (θ * w₂) ^ 2) * autoCorr F 0 +
        2 * (θ * w₁) * (θ * w₂) * autoCorr F (b - a) -
        (2 * (θ * w₁) * autoCorr F a + 2 * (θ * w₂) * autoCorr F b) =
      ((w₁ ^ 2 + w₂ ^ 2) * autoCorr F 0 + 2 * w₁ * w₂ * autoCorr F (b - a)) * (θ * θ) +
        (-2 * (w₁ * autoCorr F a + w₂ * autoCorr F b)) * θ + autoCorr F 0 by ring]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  linarith [hdisc, show (-2 * (w₁ * autoCorr F a + w₂ * autoCorr F b)) ^ 2 -
      4 * ((w₁ ^ 2 + w₂ ^ 2) * autoCorr F 0 + 2 * w₁ * w₂ * autoCorr F (b - a)) * autoCorr F 0 =
    4 * ((w₁ * autoCorr F a + w₂ * autoCorr F b) ^ 2 -
      autoCorr F 0 * ((w₁ ^ 2 + w₂ ^ 2) * autoCorr F 0 + 2 * w₁ * w₂ * autoCorr F (b - a))) by ring]

/-- **Sign-Flipped Weighted Two-Atom Ratio-Lag Law.** Replacing `w₂` by `-w₂` in
`sq_weighted_two_atom_le` flips the sign of the ratio correlation `autoCorr F (b - a)`:
`(w₁ * autoCorr F a - w₂ * autoCorr F b)² ≤ autoCorr F 0 * ((w₁² + w₂²) * autoCorr F 0 - 2 * w₁ * w₂ * autoCorr F (b - a))`. -/
theorem sq_weighted_two_atom_sub_le {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (w₁ w₂ a b : ℝ) :
    (w₁ * autoCorr F a - w₂ * autoCorr F b) ^ 2 ≤
      autoCorr F 0 * ((w₁ ^ 2 + w₂ ^ 2) * autoCorr F 0 - 2 * w₁ * w₂ * autoCorr F (b - a)) := by
  have h := sq_weighted_two_atom_le hF hFc w₁ (-w₂) a b
  linarith [h, show w₁ * autoCorr F a + -w₂ * autoCorr F b = w₁ * autoCorr F a - w₂ * autoCorr F b by ring,
    show (w₁ ^ 2 + (-w₂) ^ 2) * autoCorr F 0 + 2 * w₁ * -w₂ * autoCorr F (b - a) =
      (w₁ ^ 2 + w₂ ^ 2) * autoCorr F 0 - 2 * w₁ * w₂ * autoCorr F (b - a) by ring]

/-- **Weighted Two-Atom Polarization Ceiling.** Adding `sq_weighted_two_atom_le` and
`sq_weighted_two_atom_sub_le` cancels the same-side ratio correlation `autoCorr F (b - a)`
completely:
`(w₁ A_F(a) + w₂ A_F(b))² + (w₁ A_F(a) - w₂ A_F(b))² ≤ 2 (w₁² + w₂²) A_F(0)²`. -/
theorem sq_weighted_two_atom_polarization {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (w₁ w₂ a b : ℝ) :
    (w₁ * autoCorr F a + w₂ * autoCorr F b) ^ 2 +
        (w₁ * autoCorr F a - w₂ * autoCorr F b) ^ 2 ≤
      2 * (w₁ ^ 2 + w₂ ^ 2) * autoCorr F 0 ^ 2 := by
  have h1 := sq_weighted_two_atom_le hF hFc w₁ w₂ a b
  have h2 := sq_weighted_two_atom_sub_le hF hFc w₁ w₂ a b
  linarith [h1, h2]

/-- At `r = 23/40`, the prime-side charge of any test `F` supported in `[−23/40, 23/40]` is the sum
of the two prime-atom correlations at `log 2` and `log 3`:
`primeSideCharge F = Λ(2)/√2 · A_F(log 2) + Λ(3)/√3 · A_F(log 3)`. -/
theorem primeSideCharge_eq_two_three_twentyThreeFortieths {F : ℝ → ℝ}
    (hsupp : ∀ x, 23 / 40 < |x| → F x = 0) :
    primeSideCharge F =
      vonMangoldtAtom 2 * autoCorr F (Real.log 2) +
        vonMangoldtAtom 3 * autoCorr F (Real.log 3) := by
  rw [primeSideCharge_eq_sum_relevantShifts (by norm_num : (0 : ℝ) ≤ 23 / 40) hsupp,
    relevantShifts_twentyThreeFortieths, Finset.sum_pair (by decide : (2 : ℕ) ≠ 3)]
  push_cast
  rfl

/-- **Exact Ratio-Lag Pricing of the Prime Side in the Two-Atom Window `r = 23/40`.**
For any continuous compactly supported test `F` vanishing outside `[−23/40, 23/40]`, the squared
prime-side charge is controlled by the mass `A_F(0)` and the single free same-side ratio correlation
`A_F(log 3 - log 2)`:
`(primeSideCharge F)² ≤ A_F(0) ((Λ₂² + Λ₃²) A_F(0) + 2 Λ₂ Λ₃ A_F(log 3 - log 2))`. -/
theorem sq_primeSideCharge_twentyThreeFortieths_le {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hsupp : ∀ x, 23 / 40 < |x| → F x = 0) :
    primeSideCharge F ^ 2 ≤
      autoCorr F 0 *
        ((vonMangoldtAtom 2 ^ 2 + vonMangoldtAtom 3 ^ 2) * autoCorr F 0 +
          2 * vonMangoldtAtom 2 * vonMangoldtAtom 3 * autoCorr F (Real.log 3 - Real.log 2)) := by
  rw [primeSideCharge_eq_two_three_twentyThreeFortieths hsupp]
  exact sq_weighted_two_atom_le hF hFc (vonMangoldtAtom 2) (vonMangoldtAtom 3) (Real.log 2) (Real.log 3)

/-- The diagonal weight sum `Λ(2)²/2 + Λ(3)²/3` in the two-prime window is strictly below `643/1000`. -/
theorem vonMangoldtAtom_two_sq_add_three_sq_lt :
    vonMangoldtAtom 2 ^ 2 + vonMangoldtAtom 3 ^ 2 < 643 / 1000 := by
  obtain ⟨h20, h21⟩ := vonMangoldtAtom_two_bounds
  obtain ⟨_, h31⟩ := vonMangoldtAtom_three_bounds
  have hs2 : vonMangoldtAtom 2 ^ 2 ≤ (4902 / 10000) ^ 2 := pow_le_pow_left₀ h20 h21 2
  have hs3 : vonMangoldtAtom 3 ^ 2 ≤ (6344 / 10000) ^ 2 :=
    pow_le_pow_left₀ (vonMangoldtAtom_nonneg 3) h31 2
  linarith

/-- **Complete Two-Prime Window Incidence Ledger Floor (`r = 23/40`).**
For every real odd `F ∈ C²_c(ℝ)` supported in `[−23/40, 23/40]` and every plateau radius `R > 23/40`,
the overlapping prime strips `{2, 3}` are paid by `2 stripSurplus F (log 2 - 23/40) (23/40)` and
`evenStripGain`, leaving `(1/62) ∫_{S₂} F²` of positive strip mass to spare in the full zero form:
`(surplusPool - 2 stripSurplus_{S₂}) + crossingPotentialTerm + (1/62) ∫_{S₂} F² + ∫ F² plateauPotentialFloor R - poleCharge F ≤ fullZeroForm F`. -/
theorem fullZeroForm_ge_twentyThreeFortieths_complete {F : ℝ → ℝ} {R : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 23 / 40 < |x| → F x = 0) (hrR : 23 / 40 < R) :
    (surplusPool (aperturePlateau (23 / 40) R) F -
        2 * stripSurplus F (Real.log 2 - 23 / 40) (23 / 40)) +
      crossingPotentialTerm (aperturePlateau (23 / 40) R) F +
      1 / 62 * (∫ x in (Real.log 2 - 23 / 40)..(23 / 40), F x ^ 2) +
      (∫ x, F x ^ 2 * plateauPotentialFloor R x) -
      poleCharge F ≤ fullZeroForm F := by
  have hled := fullZeroForm_eq_incidenceLedger hF hFc hodd (by norm_num : (0 : ℝ) < 23 / 40) hsupp hrR
  have hstrip := sum_oddStripCost_le_stripSurplus_add_evenStripGain_twentyThreeFortieths
    (hF.of_le (by norm_num)) hFc hodd hsupp
  have hrem := gaugeRemainder_ge_plateauPotentialFloor hF hFc hsupp hrR
  linarith

/-! ## Part IV: All-Aperture Multi-Atom Ratio-Comb Pricing of the Ledger -/

/-- **All-Aperture Ratio-Comb Bound on the Prime-Side Crossing Charge.**
For any continuous compactly supported test `F : ℝ → ℝ` supported in `[−r, r]` (`r ≥ 0`), the
squared prime-side crossing charge is bounded by the mass `autoCorr F 0` times the prime-comb
energy `combEnergy F (relevantShifts r) vonMangoldtAtom`, which expands into the diagonal variance
`(∑_{n} Λ_n²) A_F(0)` and the **same-side ratio correlations** `∑_{n ≠ m} Λ_n Λ_m A_F(log m - log n)`:
`(primeSideCharge F)² ≤ A_F(0) * ((∑_{n ∈ relevantShifts r} Λ_n²) A_F(0) + ∑_{n ∈ relevantShifts r} ∑_{m ∈ (relevantShifts r).erase n} Λ_n Λ_m A_F(log m - log n))`. -/
theorem sq_primeSideCharge_le_mass_mul_combEnergy {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 ≤ r) (hsupp : ∀ x, r < |x| → F x = 0) :
    primeSideCharge F ^ 2 ≤
      autoCorr F 0 *
        ((∑ n ∈ relevantShifts r, vonMangoldtAtom n ^ 2) * autoCorr F 0 +
          ∑ n ∈ relevantShifts r, ∑ m ∈ (relevantShifts r).erase n,
            vonMangoldtAtom n * vonMangoldtAtom m * autoCorr F (Real.log m - Real.log n)) := by
  rw [primeSideCharge_eq_sum_relevantShifts hr hsupp, ← combEnergy_eq_diagonal_add_cross]
  exact sq_cost_le_mass_mul_combEnergy hF hFc (relevantShifts r) vonMangoldtAtom

/-- **All-Aperture Incidence Ledger Identity with Net Prime Charge Priced by `primeSideCharge`.**
For any real odd `F ∈ C²_c(ℝ)` supported in `[−r, r]` (`0 < r < R`),
`fullZeroForm F = surplusPool + crossingPotentialTerm + gaugeRemainder - poleCharge - 2 * primeSideCharge F`. -/
theorem fullZeroForm_eq_incidenceBudget_sub_primeSideCharge {F : ℝ → ℝ} {r R : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) :
    fullZeroForm F =
      surplusPool (aperturePlateau r R) F +
        crossingPotentialTerm (aperturePlateau r R) F +
        gaugeRemainder (aperturePlateau r R) F -
        poleCharge F -
        2 * primeSideCharge F := by
  have hled := fullZeroForm_eq_incidenceLedger hF hFc hodd hr hsupp hrR
  have hnet := sum_evenStripGain_sub_sum_oddStripCost hF.continuous hodd hr.le hsupp
  linarith

/-- If `X² ≤ A * B` with `0 ≤ A`, `0 ≤ B`, and `0 < γ`, then `2 * X ≤ γ * A + γ⁻¹ * B`. -/
theorem two_mul_le_of_sq_le_mul {X A B γ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hγ : 0 < γ)
    (hX : X ^ 2 ≤ A * B) : 2 * X ≤ γ * A + γ⁻¹ * B := by
  have hS : 0 ≤ γ * A + γ⁻¹ * B := by positivity
  rcases le_or_gt X 0 with hX0 | hX0
  · linarith
  · have hpos : 0 < γ * A + γ⁻¹ * B + 2 * X := by linarith
    have hid : (γ * A + γ⁻¹ * B - 2 * X) * (γ * A + γ⁻¹ * B + 2 * X) =
        (γ * A - γ⁻¹ * B) ^ 2 + 4 * (A * B - X ^ 2) := by
      have hne : γ ≠ 0 := hγ.ne'
      field_simp
      ring
    have hnn : 0 ≤ (γ * A + γ⁻¹ * B - 2 * X) * (γ * A + γ⁻¹ * B + 2 * X) := by
      rw [hid]
      nlinarith [sq_nonneg (γ * A - γ⁻¹ * B)]
    nlinarith

/-- **All-Aperture Multi-Atom Ratio-Comb Lower Bound on the Full Zero Form.**
For any real odd `F ∈ C²_c(ℝ)` supported in `[−r, r]` (`0 < r < R`) and any weight `γ > 0`,
bounding `2 * primeSideCharge F ≤ γ * autoCorr F 0 + γ⁻¹ * combEnergy F (relevantShifts r) vonMangoldtAtom`
prices the entire prime-power crossing bill in `fullZeroForm F` by the variance `autoCorr F 0` and
the same-side ratio correlations `autoCorr F (log m - log n)`:
`surplusPool + crossingPotentialTerm + gaugeRemainder - poleCharge - γ * autoCorr F 0 - γ⁻¹ * combEnergy F (relevantShifts r) vonMangoldtAtom ≤ fullZeroForm F`. -/
theorem fullZeroForm_ge_incidenceBudget_sub_combEnergy {F : ℝ → ℝ} {r R γ : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) (hγ : 0 < γ) :
    surplusPool (aperturePlateau r R) F +
        crossingPotentialTerm (aperturePlateau r R) F +
        gaugeRemainder (aperturePlateau r R) F -
        poleCharge F -
        γ * autoCorr F 0 -
        γ⁻¹ * combEnergy F (relevantShifts r) vonMangoldtAtom ≤
      fullZeroForm F := by
  have hbud := fullZeroForm_eq_incidenceBudget_sub_primeSideCharge hF hFc hodd hr hsupp hrR
  have hcomb : primeSideCharge F ^ 2 ≤
      autoCorr F 0 * combEnergy F (relevantShifts r) vonMangoldtAtom := by
    rw [primeSideCharge_eq_sum_relevantShifts hr.le hsupp]
    exact sq_cost_le_mass_mul_combEnergy hF.continuous hFc (relevantShifts r) vonMangoldtAtom
  have h0 : 0 ≤ autoCorr F 0 := autoCorr_zero_nonneg hF.continuous hFc
  have hE : 0 ≤ combEnergy F (relevantShifts r) vonMangoldtAtom := by
    rw [combEnergy_eq_testPairing ⟨hF.continuous, hFc⟩]
    exact testPairing_self_nonneg _
  have hyoung := two_mul_le_of_sq_le_mul h0 hE hγ hcomb
  linarith

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
