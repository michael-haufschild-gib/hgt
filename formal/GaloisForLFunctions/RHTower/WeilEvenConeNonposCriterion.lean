import GaloisForLFunctions.RHTower.WeilEvenConeOneSidedCriterion

/-!
# The one-sided Weil criterion on even tests, nonpositive side

The **even nonpositive cone** consists of the nonnegative combinations of autocorrelations of EVEN
tests whose normalized values `Σ c_f ℓ_n(f)` at every `±log n`, `n ≥ 2`, are `≤ 0`.

**Theorem** (`riemannHypothesis_and_ge_vonMangoldt_of_positiveOnEvenNonposCone`). If the Weil
functional `W_U` (pole weight `1`) of some weights `U` is nonnegative on the even nonpositive cone,
then RH holds and `Λ ≤ U` on `n ≥ 2`.

**Corollary** (`riemannHypothesis_iff_positiveOnEvenNonposCone`). RH holds iff `W_Λ ≥ 0` on the even
nonpositive cone.

With `riemannHypothesis_and_le_vonMangoldt_of_positiveOnEvenNonnegCone` both one-sided cones of the
even sector force RH for arbitrary weights, while on the odd sector only the nonpositive cone does
(for minorants of `Λ`).

Proof. The negative coordinate directions are reached by EVEN tests: for an odd narrow bump
`o_j(u) = u h_j(u)` the test `o_j(· + log j/2) − o_j(· − log j/2)` is even and its autocorrelation
`2k_o − k_o(· − log j) − k_o(· + log j)` has a single node value, `−2∫o_j²/√j` at `n = j`
(`logVector_evenOddPairFn`). The M. Riesz extension then gives weights `lam ≤ U` that are
Weil-positive on all even tests, and the even cone is `{Λ}` under RH and empty otherwise.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff
open Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-! ## The odd narrow bump -/

/-- The odd narrow bump `u h_j(u)` (real form). -/
def oddNarrowBumpR (j : ℕ) (u : ℝ) : ℝ := u * narrowBump j u

/-- The odd narrow bump `u h_j(u)`. -/
def oddNarrowBumpC (j : ℕ) (u : ℝ) : ℂ := ((oddNarrowBumpR j u : ℝ) : ℂ)

theorem contDiff_oddNarrowBumpC (j : ℕ) : ContDiff ℝ ∞ (oddNarrowBumpC j) :=
  ofRealCLM.contDiff.comp (contDiff_id.mul (narrowBump j).contDiff)

theorem oddNarrowBumpC_eq_zero (j : ℕ) {u : ℝ} (hu : 1 / (4 * ((j : ℝ) + 1)) < |u|) :
    oddNarrowBumpC j u = 0 := by
  have h : (narrowBump j).rOut ≤ dist u 0 := by rw [Real.dist_eq, sub_zero]; exact hu.le
  simp only [oddNarrowBumpC, oddNarrowBumpR, (narrowBump j).zero_of_le_dist h, mul_zero,
    Complex.ofReal_zero]

theorem hasCompactSupport_oddNarrowBumpC (j : ℕ) : HasCompactSupport (oddNarrowBumpC j) := by
  have : HasCompactSupport (oddNarrowBumpR j) := (narrowBump j).hasCompactSupport.mul_left
  exact this.comp_left Complex.ofReal_zero

theorem oddNarrowBumpC_neg (j : ℕ) (u : ℝ) : oddNarrowBumpC j (-u) = -oddNarrowBumpC j u := by
  simp only [oddNarrowBumpC, oddNarrowBumpR, ContDiffBump.neg, neg_mul, Complex.ofReal_neg]

theorem integral_oddNarrowBumpR_sq_pos (j : ℕ) : 0 < ∫ t, (oddNarrowBumpR j t) ^ 2 := by
  have hc : Continuous fun t => (oddNarrowBumpR j t) ^ 2 :=
    (continuous_id.mul (narrowBump j).continuous).pow 2
  have hpos := (narrowBump j).rIn_pos
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (((narrowBump j).hasCompactSupport.mul_left).comp_left (g := fun x : ℝ => x ^ 2)
      (by norm_num)) (fun t => sq_nonneg _) (x := (narrowBump j).rIn / 2) ?_
  have hmem : (narrowBump j).rIn / 2 ∈ Metric.closedBall (0 : ℝ) (narrowBump j).rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
  simp only [oddNarrowBumpR, (narrowBump j).one_of_mem_closedBall hmem, mul_one]
  positivity

/-! ## The odd pair test and its even translate -/

/-- The pair test `o_j(u) − o_j(u − log j)`. -/
def oddBumpPair (j : ℕ) (u : ℝ) : ℂ := oddNarrowBumpC j u - oddNarrowBumpC j (u - Real.log j)

theorem oddBumpPair_eq_sum (j : ℕ) :
    oddBumpPair j = fun u => ∑ m ∈ Finset.range 2,
      (if m = 0 then (1 : ℂ) else (-1 : ℂ)) *
        oddNarrowBumpC j (u - if m = 0 then 0 else Real.log j) := by
  funext u
  simp [oddBumpPair, Finset.sum_range_succ]
  ring

theorem contDiff_oddBumpPair (j : ℕ) : ContDiff ℝ 2 (oddBumpPair j) :=
  ((contDiff_oddNarrowBumpC j).of_le (by norm_cast)).sub
    (((contDiff_oddNarrowBumpC j).of_le (by norm_cast)).comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_oddBumpPair (j : ℕ) : HasCompactSupport (oddBumpPair j) :=
  (hasCompactSupport_oddNarrowBumpC j).sub
    ((hasCompactSupport_oddNarrowBumpC j).comp_homeomorph (Homeomorph.subRight (Real.log j)))

theorem weilTest_oddBumpPair (j : ℕ) (y : ℝ) :
    EF.weilTest (oddBumpPair j) (oddBumpPair j) y =
      2 * EF.weilTest (oddNarrowBumpC j) (oddNarrowBumpC j) y -
        (EF.weilTest (oddNarrowBumpC j) (oddNarrowBumpC j) (y + Real.log j) +
          EF.weilTest (oddNarrowBumpC j) (oddNarrowBumpC j) (y - Real.log j)) := by
  rw [oddBumpPair_eq_sum, weilTest_sum_translates (contDiff_oddNarrowBumpC j).continuous
    (hasCompactSupport_oddNarrowBumpC j)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_true, one_ne_zero,
    if_false, map_one, map_neg, mul_one, one_mul, sub_zero, add_zero]
  rw [show y - Real.log j + Real.log j = y by ring]
  ring

theorem weilTest_oddNarrowBumpC_eq_zero (j : ℕ) {Y : ℝ} (hY : 1 / (2 * ((j : ℝ) + 1)) < |Y|) :
    EF.weilTest (oddNarrowBumpC j) (oddNarrowBumpC j) Y = 0 :=
  weilTest_self_eq_zero (fun u hu => oddNarrowBumpC_eq_zero j hu)
    (by rw [show 2 * (1 / (4 * ((j : ℝ) + 1))) = 1 / (2 * ((j : ℝ) + 1)) by field_simp; ring]
        exact hY)

theorem weilTest_oddNarrowBumpC_zero (j : ℕ) :
    EF.weilTest (oddNarrowBumpC j) (oddNarrowBumpC j) 0 =
      ((∫ t, (oddNarrowBumpR j t) ^ 2 : ℝ) : ℂ) :=
  weilTest_self_zero_ofReal (g := fun t => oddNarrowBumpR j t)

/-- The `ℓ`-values of the odd pair test: `−2∫o_j²/√j` at `n = j` and `0` at every other
`n ≥ 2`. -/
theorem logValue_oddBumpPair {j : ℕ} (hj : 2 ≤ j) {m : ℕ} (hm : 2 ≤ m) :
    logValue (oddBumpPair j) m =
      if m = j then -2 * (∫ t, (oddNarrowBumpR j t) ^ 2) / Real.sqrt j else 0 := by
  have hH := fun Y => weilTest_oddNarrowBumpC_eq_zero j (Y := Y)
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
  rw [logValue, weilTest_oddBumpPair, weilTest_oddBumpPair, e1, e2, e3,
    show -Real.log m + Real.log j = -(Real.log m - Real.log j) by ring, e4]
  split_ifs with hmj
  · subst hmj
    rw [sub_self, neg_zero, weilTest_oddNarrowBumpC_zero]
    rw [show (2 * 0 - (0 + ((∫ t, (oddNarrowBumpR m t) ^ 2 : ℝ) : ℂ)) +
        (2 * 0 - (((∫ t, (oddNarrowBumpR m t) ^ 2 : ℝ) : ℂ) + 0))) =
        ((-2 * ∫ t, (oddNarrowBumpR m t) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  · have hgap := WeilExcess.inv_succ_le_abs_log_sub (by omega) (by omega) hmj
    have hlt : 1 / (2 * ((j : ℝ) + 1)) < 1 / ((j : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    rw [hH (Real.log m - Real.log j) (by linarith), hH (-(Real.log m - Real.log j))
      (by rw [abs_neg]; linarith)]
    simp

/-- The even translate `o_j(u + log j/2) − o_j(u − log j/2)` of the odd pair test. -/
def evenOddPair (j : ℕ) (u : ℝ) : ℂ := oddBumpPair j (u + Real.log j / 2)

theorem evenOddPair_neg (j : ℕ) (u : ℝ) : evenOddPair j (-u) = evenOddPair j u := by
  unfold evenOddPair oddBumpPair
  rw [show -u + Real.log j / 2 = -(u - Real.log j / 2) by ring,
    show -(u - Real.log j / 2) - Real.log j = -(u + Real.log j / 2) by ring,
    oddNarrowBumpC_neg, oddNarrowBumpC_neg,
    show u + Real.log j / 2 - Real.log j = u - Real.log j / 2 by ring]
  ring

/-- The even translate as an even Weil test. -/
def evenOddPairFn (j : ℕ) : WeilEvenTestFn :=
  ⟨⟨evenOddPair j, (contDiff_oddBumpPair j).comp (contDiff_id.add contDiff_const),
    (hasCompactSupport_oddBumpPair j).comp_homeomorph (Homeomorph.addRight (Real.log j / 2))⟩,
    evenOddPair_neg j⟩

theorem logVector_evenOddPairFn (j : LogIndex) :
    logVector (evenOddPairFn j).1 =
      Finsupp.single j (-2 * (∫ t, (oddNarrowBumpR j t) ^ 2) / Real.sqrt j) := by
  ext m
  rw [logVector_apply, Finsupp.single_apply]
  change logValue (fun t => oddBumpPair j (t + Real.log j / 2)) m = _
  unfold logValue
  rw [RHTower.weilTest_comp_add_const]
  change logValue (oddBumpPair j) m = _
  rw [logValue_oddBumpPair j.2 m.2]
  by_cases h : (m : ℕ) = j
  · rw [if_pos h, if_pos (Subtype.ext h).symm]
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h'.symm)]

theorem oddBumpPair_weight_pos (j : LogIndex) :
    0 < 2 * (∫ t, (oddNarrowBumpR j t) ^ 2) / Real.sqrt j := by
  have hj : (0 : ℝ) < (j : ℕ) := by exact_mod_cast (lt_of_lt_of_le two_pos j.2)
  exact div_pos (mul_pos two_pos (integral_oddNarrowBumpR_sq_pos j)) (Real.sqrt_pos.mpr hj)

/-! ## The even nonpositive cone -/

/-- Weil positivity of `U` on the nonnegative combinations of even tests whose `ℓ`-values are
nonpositive at every `n ≥ 2`. -/
def PositiveOnEvenNonposCone (U : ℕ → ℝ) : Prop :=
  ∀ c : WeilEvenTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1.1 n) ≤ 0) →
    0 ≤ c.sum fun f t => t * (weilFullFunctional U (EF.weilTest f.1.1 f.1.1)).re

/-- **Positivity on the even nonpositive cone produces an even Weil-positive minorant of `U`.** -/
theorem exists_weilPositiveEvenAt_le_of_positiveOnEvenNonposCone {U : ℕ → ℝ}
    (h : PositiveOnEvenNonposCone U) :
    ∃ lam : ℕ → ℝ, EvenSector.WeilPositiveEvenAt 1 lam ∧ ∀ n, 2 ≤ n → lam n ≤ U n := by
  obtain ⟨lam, hlamU, hlamT⟩ := GaloisForLFunctions.HTGeometry.exists_le_of_nonneg_on_nonpos_cone
    (fun f : WeilEvenTestFn => logVector f.1)
    (fun f : WeilEvenTestFn => weilArchRe (EF.weilTest f.1.1 f.1.1)) (fun j : LogIndex => U j)
    (fun j => ⟨evenOddPairFn j, _, oddBumpPair_weight_pos j, by
      rw [logVector_evenOddPairFn]; congr 1; ring⟩)
    (fun c hc hcT => by
      have h1 := h c hc fun n hn => by
        rw [← linearCombination_logVector_even_apply c ⟨n, hn⟩]; exact hcT ⟨n, hn⟩
      rw [sum_re_weilFullFunctional_even] at h1
      linarith)
  refine ⟨fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0, fun f hf hc heven => ?_, fun n hn => ?_⟩
  · rw [EvenSector.weilPoleWeightFunctional_one, re_weilFullFunctional_eq _ ⟨f, hf, hc⟩]
    have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ)) =
        lam := funext fun j => by simp [j.2]
    rw [e]
    linarith [hlamT ⟨⟨f, hf, hc⟩, heven⟩]
  · simp only [dif_pos hn]; exact hlamU ⟨n, hn⟩

/-- **Even one-sided positivity on the nonpositive cone forces RH and `Λ ≤ U`.** -/
theorem riemannHypothesis_and_ge_vonMangoldt_of_positiveOnEvenNonposCone {U : ℕ → ℝ}
    (h : PositiveOnEvenNonposCone U) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → ArithmeticFunction.vonMangoldt n ≤ U n := by
  obtain ⟨lam, hW, hle⟩ := exists_weilPositiveEvenAt_le_of_positiveOnEvenNonposCone h
  obtain ⟨hRH, heq⟩ := EvenSector.weilPositiveEvenAt_one_iff.mp hW
  exact ⟨hRH, fun n hn => (heq n hn).symm.le.trans (hle n hn)⟩

/-- **The nonpositive one-sided Weil criterion on even tests.** -/
theorem riemannHypothesis_iff_positiveOnEvenNonposCone :
    RiemannHypothesis ↔
      PositiveOnEvenNonposCone fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  constructor
  · intro hRH c hc _
    exact Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f)
      (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH f.1.1 f.1.2.1 f.1.2.2)
  · exact fun h => (riemannHypothesis_and_ge_vonMangoldt_of_positiveOnEvenNonposCone h).1

end

end RHTower.WeilOneSided
