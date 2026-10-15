import GaloisForLFunctions.RHTower.WeilOddConeOneSidedCriterion
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity

/-!
# The one-sided Weil criterion on even tests

The **even nonnegative cone** consists of the nonnegative combinations `Σ c_f k_f` of
autocorrelations of EVEN tests whose normalized values `Σ c_f ℓ_n(f)` at every `±log n`, `n ≥ 2`,
are `≥ 0` (`logValue`).

**Theorem** (`riemannHypothesis_and_le_vonMangoldt_of_positiveOnEvenNonnegCone`). If the Weil
functional `W_L` (pole weight `1`) of some weights `L` is nonnegative on the even nonnegative cone,
then RH holds and `L ≤ Λ` on `n ≥ 2`.

**Corollary** (`riemannHypothesis_iff_positiveOnEvenNonnegCone`). RH holds iff `W_Λ ≥ 0` on the even
nonnegative cone.

Together with the odd criterion (`riemannHypothesis_iff_positiveOnOddNonposCone`) this gives a
parity–sign pairing: RH is positivity of `W_Λ` on even tests with nonnegative prime values, and
equally on odd tests with nonpositive prime values. On odd tests, also
`eq_vonMangoldt_of_positiveOnOddNonposCone_of_le`: a minorant `U ≤ Λ` with `W_U ≥ 0` on the odd
nonpositive cone equals `Λ`, and RH holds.

Proof. The M. Riesz extension (`HTGeometry.exists_ge_of_nonneg_on_nonneg_cone`) on even tests, with
positive coordinate generators the even translates `h_j(· + log j/2) + h_j(· − log j/2)` of the
pair tests `h_j + h_j(· − log j)` (`evenPairTestFn`), produces weights `lam ≥ L` that are
Weil-positive on all even tests. The even cone is `{Λ}` under RH and empty otherwise
(`weilPositiveEvenAt_one_iff`).
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff
open Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-- Even Weil tests. -/
def WeilEvenTestFn : Type := {f : WeilTestFn // ∀ x, f.1 (-x) = f.1 x}

/-- Weil positivity of `L` on the nonnegative combinations of even tests whose `ℓ`-values are
nonnegative at every `n ≥ 2`. -/
def PositiveOnEvenNonnegCone (L : ℕ → ℝ) : Prop :=
  ∀ c : WeilEvenTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.1.1 n) →
    0 ≤ c.sum fun f t => t * (weilFullFunctional L (EF.weilTest f.1.1 f.1.1)).re

/-! ## The even pair tests -/

/-- The even pair test `h_j(u + log j/2) + h_j(u − log j/2)`. -/
def evenPairTest (j : ℕ) (u : ℝ) : ℂ := pairTest j 1 (u + Real.log j / 2)

theorem evenPairTest_neg (j : ℕ) (u : ℝ) : evenPairTest j (-u) = evenPairTest j u := by
  unfold evenPairTest pairTest
  rw [show -u + Real.log j / 2 = -(u - Real.log j / 2) by ring,
    show -(u - Real.log j / 2) - Real.log j = -(u + Real.log j / 2) by ring,
    narrowBumpC_neg, narrowBumpC_neg, show u + Real.log j / 2 - Real.log j = u - Real.log j / 2 by
      ring]
  push_cast; ring

/-- The even pair test as an even Weil test. -/
def evenPairTestFn (j : ℕ) : WeilEvenTestFn :=
  ⟨⟨evenPairTest j, (contDiff_pairTest j 1).comp (contDiff_id.add contDiff_const),
    (hasCompactSupport_pairTest j 1).comp_homeomorph (Homeomorph.addRight (Real.log j / 2))⟩,
    evenPairTest_neg j⟩

theorem logVector_evenPairTestFn (j : ℕ) :
    logVector (evenPairTestFn j).1 = logVector (pairTestFn j 1) := by
  ext m
  rw [logVector_apply, logVector_apply]
  unfold logValue
  change ((EF.weilTest (fun t => pairTest j 1 (t + Real.log j / 2))
    (fun t => pairTest j 1 (t + Real.log j / 2)) (Real.log m) +
      EF.weilTest (fun t => pairTest j 1 (t + Real.log j / 2))
        (fun t => pairTest j 1 (t + Real.log j / 2)) (-Real.log m)).re / Real.sqrt m) = _
  rw [RHTower.weilTest_comp_add_const]
  rfl

/-! ## The one-sided extension on even tests -/

theorem linearCombination_logVector_even_apply (c : WeilEvenTestFn →₀ ℝ) (j : LogIndex) :
    linearCombination ℝ (fun f : WeilEvenTestFn => logVector f.1) c j =
      c.sum fun f t => t * logValue f.1.1 j := by
  rw [linearCombination_apply, Finsupp.sum_apply]
  simp [logVector_apply]

theorem sum_re_weilFullFunctional_even (U : ℕ → ℝ) (c : WeilEvenTestFn →₀ ℝ) :
    (c.sum fun f t => t * (weilFullFunctional U (EF.weilTest f.1.1 f.1.1)).re) =
      linearCombination ℝ (fun f : WeilEvenTestFn => weilArchRe (EF.weilTest f.1.1 f.1.1)) c -
        linearCombination ℝ (fun j : LogIndex => U j)
          (linearCombination ℝ (fun f : WeilEvenTestFn => logVector f.1) c) := by
  simp_rw [fun f : WeilEvenTestFn => re_weilFullFunctional_eq U f.1]
  have e1 : linearCombination ℝ (fun f : WeilEvenTestFn => weilArchRe (EF.weilTest f.1.1 f.1.1))
      c = c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1) := by
    rw [linearCombination_apply]; simp only [smul_eq_mul]
  have e2 : linearCombination ℝ (fun j : LogIndex => U j)
      (linearCombination ℝ (fun f : WeilEvenTestFn => logVector f.1) c) =
      c.sum fun f t => t * linearCombination ℝ (fun j : LogIndex => U j) (logVector f.1) := by
    rw [linearCombination_apply ℝ (v := fun f : WeilEvenTestFn => logVector f.1), map_finsuppSum]
    exact Finsupp.sum_congr fun f _ => by rw [map_smul, smul_eq_mul]
  rw [e1, e2, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun f _ => by ring

/-- **Positivity on the even nonnegative cone produces an even Weil-positive majorant of `L`.** -/
theorem exists_weilPositiveEvenAt_ge_of_positiveOnEvenNonnegCone {L : ℕ → ℝ}
    (h : PositiveOnEvenNonnegCone L) :
    ∃ lam : ℕ → ℝ, EvenSector.WeilPositiveEvenAt 1 lam ∧ ∀ n, 2 ≤ n → L n ≤ lam n := by
  obtain ⟨lam, hlamL, hlamT⟩ := GaloisForLFunctions.HTGeometry.exists_ge_of_nonneg_on_nonneg_cone
    (fun f : WeilEvenTestFn => logVector f.1)
    (fun f : WeilEvenTestFn => weilArchRe (EF.weilTest f.1.1 f.1.1)) (fun j : LogIndex => L j)
    (fun j => ⟨evenPairTestFn j, _, pairTest_weight_pos j, by
      rw [logVector_evenPairTestFn, logVector_pairTestFn]; congr 1; ring⟩)
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
  · simp only [dif_pos hn]; exact hlamL ⟨n, hn⟩

/-- **Even one-sided positivity forces RH and bounds the weights by `Λ`.** -/
theorem riemannHypothesis_and_le_vonMangoldt_of_positiveOnEvenNonnegCone {L : ℕ → ℝ}
    (h : PositiveOnEvenNonnegCone L) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → L n ≤ ArithmeticFunction.vonMangoldt n := by
  obtain ⟨lam, hW, hge⟩ := exists_weilPositiveEvenAt_ge_of_positiveOnEvenNonnegCone h
  obtain ⟨hRH, heq⟩ := EvenSector.weilPositiveEvenAt_one_iff.mp hW
  exact ⟨hRH, fun n hn => (hge n hn).trans (heq n hn).le⟩

/-- **The one-sided Weil criterion on even tests.** RH holds iff `W_Λ` is nonnegative on the cone
of nonnegative combinations of even tests that are nonnegative at every `±log n`. -/
theorem riemannHypothesis_iff_positiveOnEvenNonnegCone :
    RiemannHypothesis ↔
      PositiveOnEvenNonnegCone fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  constructor
  · intro hRH c hc _
    exact Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f)
      (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH f.1.1 f.1.2.1 f.1.2.2)
  · exact fun h => (riemannHypothesis_and_le_vonMangoldt_of_positiveOnEvenNonnegCone h).1

/-- **Odd one-sided positivity of a minorant of `Λ` forces equality and RH.** -/
theorem eq_vonMangoldt_of_positiveOnOddNonposCone_of_le {U : ℕ → ℝ}
    (h : PositiveOnOddNonposCone U)
    (hle : ∀ n, 2 ≤ n → U n ≤ ArithmeticFunction.vonMangoldt n) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → U n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨lam, hW, hlamU⟩ := exists_weilPositiveOdd_le_of_positiveOnOddNonposCone h
  have hlamΛ : ∀ n, 2 ≤ n → lam n ≤ ArithmeticFunction.vonMangoldt n :=
    fun n hn => (hlamU n hn).trans (hle n hn)
  have heq := RHTower.eq_vonMangoldt_of_weilPositiveOdd_of_le hW hlamΛ
  refine ⟨RHTower.riemannHypothesis_iff_exists_weilPositiveOdd_le.mpr ⟨lam, hW, hlamΛ⟩,
    fun n hn => le_antisymm (hle n hn) ?_⟩
  rw [← heq n hn]; exact hlamU n hn

end

end RHTower.WeilOneSided
