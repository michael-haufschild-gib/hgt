import GaloisForLFunctions.RHTower.WeilOddConeMinorantRigidity
import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion

/-!
# The one-sided Weil criterion on odd tests

For a Weil test `f` write `ℓ_n(f) = Re(k_f(log n) + k_f(−log n))/√n` for the normalized values of
its autocorrelation `k_f = f ⋆ f̃` (`logValue`). The **odd nonpositive cone** consists of the
nonnegative combinations `Σ c_f k_f` of autocorrelations of ODD tests with `Σ c_f ℓ_n(f) ≤ 0` for
every `n ≥ 2`.
On this cone the prime sum of the Weil functional `W_Λ` (pole weight `1`) is a nonnegative term.

**Theorem** (`riemannHypothesis_iff_positiveOnOddNonposCone`). RH holds iff `W_Λ ≥ 0` on the odd
nonpositive cone.

This sharpens the one-sided criterion on all tests (`riemannHypothesis_iff_positiveOnNonposCone`):
only odd tests are needed, and among them only the combinations at which every prime atom of
`W_Λ` enters with a favourable sign.

Proof. Positivity on the odd nonpositive cone is the hypothesis of the M. Riesz extension theorem
(`HTGeometry.exists_le_of_nonneg_on_nonpos_cone`) for the odd tests; the generators of the
negative coordinate directions are the odd translates `h_j(· + log j/2) − h_j(· − log j/2)` of the
pair tests `h_j − h_j(· − log j)` (`oddPairTestFn`), which have the same autocorrelation. The
extension is an odd Weil-positive `lam ≤ Λ`, and odd Weil positivity admits no minorant of `Λ`
other than `Λ`
(`eq_vonMangoldt_of_weilPositiveOdd_of_le`), so `Λ` is odd Weil-positive, which is RH.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff
open Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-- Odd Weil tests. -/
def WeilOddTestFn : Type := {f : WeilTestFn // ∀ x, f.1 (-x) = -f.1 x}

/-- Weil positivity of `U` on the nonnegative combinations of odd tests whose `ℓ`-values are
nonpositive at every `n ≥ 2`. -/
def PositiveOnOddNonposCone (U : ℕ → ℝ) : Prop :=
  ∀ c : WeilOddTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1.1 n) ≤ 0) →
    0 ≤ c.sum fun f t => t * (weilFullFunctional U (EF.weilTest f.1.1 f.1.1)).re

/-! ## The odd pair tests -/

theorem narrowBumpC_neg (j : ℕ) (u : ℝ) : narrowBumpC j (-u) = narrowBumpC j u := by
  unfold narrowBumpC; rw [ContDiffBump.neg]

/-- The odd pair test `h_j(u + log j/2) − h_j(u − log j/2)`. -/
def oddPairTest (j : ℕ) (u : ℝ) : ℂ := pairTest j (-1) (u + Real.log j / 2)

theorem oddPairTest_neg (j : ℕ) (u : ℝ) : oddPairTest j (-u) = -oddPairTest j u := by
  unfold oddPairTest pairTest
  rw [show -u + Real.log j / 2 = -(u - Real.log j / 2) by ring,
    show -(u - Real.log j / 2) - Real.log j = -(u + Real.log j / 2) by ring,
    narrowBumpC_neg, narrowBumpC_neg, show u + Real.log j / 2 - Real.log j = u - Real.log j / 2 by
      ring]
  push_cast; ring

/-- The odd pair test as an odd Weil test. -/
def oddPairTestFn (j : ℕ) : WeilOddTestFn :=
  ⟨⟨oddPairTest j, (contDiff_pairTest j (-1)).comp (contDiff_id.add contDiff_const),
    (hasCompactSupport_pairTest j (-1)).comp_homeomorph (Homeomorph.addRight (Real.log j / 2))⟩,
    oddPairTest_neg j⟩

theorem logVector_oddPairTestFn (j : ℕ) :
    logVector (oddPairTestFn j).1 = logVector (pairTestFn j (-1)) := by
  ext m
  rw [logVector_apply, logVector_apply]
  unfold logValue
  change ((EF.weilTest (fun t => pairTest j (-1) (t + Real.log j / 2))
    (fun t => pairTest j (-1) (t + Real.log j / 2)) (Real.log m) +
      EF.weilTest (fun t => pairTest j (-1) (t + Real.log j / 2))
        (fun t => pairTest j (-1) (t + Real.log j / 2)) (-Real.log m)).re / Real.sqrt m) = _
  rw [RHTower.weilTest_comp_add_const]
  rfl

/-! ## The one-sided extension on odd tests -/

theorem linearCombination_logVector_odd_apply (c : WeilOddTestFn →₀ ℝ) (j : LogIndex) :
    linearCombination ℝ (fun f : WeilOddTestFn => logVector f.1) c j =
      c.sum fun f t => t * logValue f.1.1 j := by
  rw [linearCombination_apply, Finsupp.sum_apply]
  simp [logVector_apply]

theorem sum_re_weilFullFunctional_odd (U : ℕ → ℝ) (c : WeilOddTestFn →₀ ℝ) :
    (c.sum fun f t => t * (weilFullFunctional U (EF.weilTest f.1.1 f.1.1)).re) =
      linearCombination ℝ (fun f : WeilOddTestFn => weilArchRe (EF.weilTest f.1.1 f.1.1)) c -
        linearCombination ℝ (fun j : LogIndex => U j)
          (linearCombination ℝ (fun f : WeilOddTestFn => logVector f.1) c) := by
  simp_rw [fun f : WeilOddTestFn => re_weilFullFunctional_eq U f.1]
  have e1 : linearCombination ℝ (fun f : WeilOddTestFn => weilArchRe (EF.weilTest f.1.1 f.1.1)) c =
      c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1) := by
    rw [linearCombination_apply]; simp only [smul_eq_mul]
  have e2 : linearCombination ℝ (fun j : LogIndex => U j)
      (linearCombination ℝ (fun f : WeilOddTestFn => logVector f.1) c) =
      c.sum fun f t => t * linearCombination ℝ (fun j : LogIndex => U j) (logVector f.1) := by
    rw [linearCombination_apply ℝ (v := fun f : WeilOddTestFn => logVector f.1), map_finsuppSum]
    exact Finsupp.sum_congr fun f _ => by rw [map_smul, smul_eq_mul]
  rw [e1, e2, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun f _ => by ring

/-- **Positivity on the odd nonpositive cone produces an odd Weil-positive minorant of `U`.** -/
theorem exists_weilPositiveOdd_le_of_positiveOnOddNonposCone {U : ℕ → ℝ}
    (h : PositiveOnOddNonposCone U) :
    ∃ lam : ℕ → ℝ, RHTower.WeilPositiveOdd lam ∧ ∀ n, 2 ≤ n → lam n ≤ U n := by
  obtain ⟨lam, hlamU, hlamT⟩ := GaloisForLFunctions.HTGeometry.exists_le_of_nonneg_on_nonpos_cone
    (fun f : WeilOddTestFn => logVector f.1)
    (fun f : WeilOddTestFn => weilArchRe (EF.weilTest f.1.1 f.1.1)) (fun j : LogIndex => U j)
    (fun j => ⟨oddPairTestFn j, _, pairTest_weight_pos j, by
      rw [logVector_oddPairTestFn, logVector_pairTestFn]; congr 1; ring⟩)
    (fun c hc hcT => by
      have h1 := h c hc fun n hn => by
        rw [← linearCombination_logVector_odd_apply c ⟨n, hn⟩]; exact hcT ⟨n, hn⟩
      rw [sum_re_weilFullFunctional_odd] at h1
      linarith)
  refine ⟨fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0, fun f hf hc hodd => ?_, fun n hn => ?_⟩
  · rw [re_weilFullFunctional_eq _ ⟨f, hf, hc⟩]
    have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ)) =
        lam := funext fun j => by simp [j.2]
    rw [e]
    linarith [hlamT ⟨⟨f, hf, hc⟩, hodd⟩]
  · simp only [dif_pos hn]; exact hlamU ⟨n, hn⟩

/-- **The one-sided Weil criterion on odd tests.** RH holds iff `W_Λ` is nonnegative on the cone of
nonnegative combinations of odd tests that are nonpositive at every `±log n`. -/
theorem riemannHypothesis_iff_positiveOnOddNonposCone :
    RiemannHypothesis ↔
      PositiveOnOddNonposCone fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  constructor
  · intro hRH c hc _
    exact Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f)
      (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH f.1.1 f.1.2.1 f.1.2.2)
  · intro h
    obtain ⟨lam, hW, hle⟩ := exists_weilPositiveOdd_le_of_positiveOnOddNonposCone h
    exact RHTower.riemannHypothesis_iff_exists_weilPositiveOdd_le.mpr ⟨lam, hW, hle⟩

end

end RHTower.WeilOneSided
