import GaloisForLFunctions.RHTower.CompactCarrierFECompleteness

/-!
# Critical-centre compact-disc Euler completeness

This file instantiates the abstract compact-carrier theorem on literal closed
discs centred at `1/2`, with the actual reflection `s ↦ 1-s` and explicit
right-half-plane bounds.
-/

noncomputable section

namespace RHTower

open Complex Metric Set

/-- Closed disc of radius `r` around the functional-equation centre. -/
abbrev CriticalClosedDisc (r : ℝ) :=
  {z : ℂ // z ∈ closedBall (1 / 2 : ℂ) r}

instance criticalClosedDisc_compactSpace (r : ℝ) :
    CompactSpace (CriticalClosedDisc r) := by
  change CompactSpace {z : ℂ // z ∈ closedBall (1 / 2 : ℂ) r}
  exact isCompact_iff_compactSpace.mp
    (isCompact_closedBall (1 / 2 : ℂ) r)

/-- Coordinate inclusion of the critical closed disc. -/
def criticalDiscCoordinate (r : ℝ) : C(CriticalClosedDisc r, ℂ) where
  toFun z := (z : ℂ)
  continuous_toFun := continuous_subtype_val

/-- Functional-equation reflection on the critical closed disc. -/
def criticalDiscReflection (r : ℝ) : C(CriticalClosedDisc r, CriticalClosedDisc r) where
  toFun z := ⟨1 - (z : ℂ), by
    have hz := z.prop
    rw [mem_closedBall, dist_eq] at hz ⊢
    have heq : (1 : ℂ) - (z : ℂ) - 1 / 2 = -((z : ℂ) - 1 / 2) := by ring
    rw [heq, norm_neg]
    exact hz⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_const.sub continuous_subtype_val) _

@[simp]
theorem criticalDiscCoordinate_reflection (r : ℝ) (z : CriticalClosedDisc r) :
    criticalDiscCoordinate r (criticalDiscReflection r z) =
      1 - criticalDiscCoordinate r z := by rfl

/-- Real-part lower bound on a critical closed disc. -/
theorem criticalDiscCoordinate_re_lower {r : ℝ} (z : CriticalClosedDisc r) :
    1 / 2 - r ≤ (criticalDiscCoordinate r z).re := by
  change 1 / 2 - r ≤ (z : ℂ).re
  have hz := z.prop
  rw [mem_closedBall, dist_eq] at hz
  have hre := Complex.abs_re_le_norm ((z : ℂ) - 1 / 2)
  norm_num at hre
  have hlo := (abs_le.mp (hre.trans hz)).1
  linarith

/-- Imaginary-part bound on a critical closed disc. -/
theorem criticalDiscCoordinate_abs_im_le {r : ℝ} (z : CriticalClosedDisc r) :
    |(criticalDiscCoordinate r z).im| ≤ r := by
  change |(z : ℂ).im| ≤ r
  have hz := z.prop
  rw [mem_closedBall, dist_eq] at hz
  have him := Complex.abs_im_le_norm ((z : ℂ) - 1 / 2)
  norm_num at him
  exact him.trans hz

/-- Literal critical-disc polynomial completeness for the actual paired Euler
tangents: every FE-odd coordinate monomial lies in their cofinite closed span. -/
theorem criticalDisc_fe_odd_monomial_mem_closedSpan
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1 / 2)
    (R₀ : ℝ) (hR₀ : 0 < R₀) (N : ℕ) :
    criticalDiscCoordinate r ^ N - (1 - criticalDiscCoordinate r) ^ N ∈
      (Submodule.span ℂ
        (Set.range fun p : {p : Nat.Primes // R₀ + 1 < Real.log (p : ℝ)} =>
          compactPrimeEulerUnitFETangent
            (criticalDiscCoordinate r) (criticalDiscReflection r)
            (p : Nat.Primes))).topologicalClosure := by
  apply fe_odd_coordinate_pow_mem_closedSpan
    (criticalDiscCoordinate r) (criticalDiscReflection r)
    (criticalDiscCoordinate_reflection r)
    (1 / 2 - r) r R₀
  · linarith
  · exact hr0
  · exact hR₀
  · exact criticalDiscCoordinate_re_lower
  · exact criticalDiscCoordinate_abs_im_le

/-- Exact finite-exception form: deleting an arbitrary finite set of primes
does not change critical-disc FE-odd polynomial completeness. -/
theorem criticalDisc_fe_odd_monomial_mem_closedSpan_compl_finset
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1 / 2)
    (S : Finset Nat.Primes) (N : ℕ) :
    criticalDiscCoordinate r ^ N - (1 - criticalDiscCoordinate r) ^ N ∈
      (Submodule.span ℂ
        (Set.range fun p : {p : Nat.Primes // p ∉ S} =>
          compactPrimeEulerUnitFETangent
            (criticalDiscCoordinate r) (criticalDiscReflection r)
            (p : Nat.Primes))).topologicalClosure := by
  let B : ℝ := ∑ p ∈ S, Real.log (p : ℝ)
  let R₀ : ℝ := 1 + B
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith
  have htail := criticalDisc_fe_odd_monomial_mem_closedSpan hr0 hr R₀ hR₀ N
  apply (Submodule.topologicalClosure_mono ?_) htail
  apply Submodule.span_mono
  rintro x ⟨p, rfl⟩
  have hpnot : (p : Nat.Primes) ∉ S := by
    intro hpS
    have hlognonneg : ∀ q ∈ S, 0 ≤ Real.log ((q : Nat.Primes) : ℝ) := by
      intro q hq
      apply Real.log_nonneg
      exact_mod_cast q.prop.one_lt.le
    have hle : Real.log ((p : Nat.Primes) : ℝ) ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum hlognonneg hpS
    have hp := p.prop
    dsimp [R₀] at hp
    linarith
  exact ⟨⟨(p : Nat.Primes), hpnot⟩, rfl⟩

/-- Every FE-oddified scalar polynomial belongs to the cofinite actual paired
Euler-tangent closed span on a critical disc. -/
theorem criticalDisc_fe_odd_polynomial_mem_closedSpan_compl_finset
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1 / 2)
    (S : Finset Nat.Primes) (P : Polynomial ℂ) :
    compactPolynomialEval (criticalDiscCoordinate r) P -
        compactPolynomialEval (1 - criticalDiscCoordinate r) P ∈
      (Submodule.span ℂ
        (Set.range fun p : {p : Nat.Primes // p ∉ S} =>
          compactPrimeEulerUnitFETangent
            (criticalDiscCoordinate r) (criticalDiscReflection r)
            (p : Nat.Primes))).topologicalClosure := by
  rw [compactPolynomialEval, compactPolynomialEval, ← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro n hn
  rw [← smul_sub]
  exact Submodule.smul_mem _ _
    (criticalDisc_fe_odd_monomial_mem_closedSpan_compl_finset hr0 hr S n)

end RHTower
