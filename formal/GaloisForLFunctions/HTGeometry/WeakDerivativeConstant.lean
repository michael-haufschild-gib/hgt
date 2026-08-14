import GaloisForLFunctions.HTGeometry.CompactPrimitive
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# A vanishing weak derivative forces a constant

A locally integrable function whose weak derivative vanishes on an open interval agrees almost
everywhere with a constant there.  The mechanism is the classical one: a test function with
vanishing integral is the derivative of a test function, so the pairing of the function with a test
function depends only on the integral of the test function.
-/

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A normalised test function supported in a bounded open interval. -/
theorem exists_test_integral_one {a b : ℝ} (hab : a < b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ioo a b ∧
      (∫ x, χ x) = 1 := by
  set c : ℝ := (a + b) / 2 with hc
  set r : ℝ := (b - a) / 4 with hr
  have hrpos : 0 < r := by
    rw [hr]; linarith
  set f : ContDiffBump c := ⟨r / 2, r, by linarith, by linarith⟩ with hf
  refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed, ?_,
    f.integral_normed⟩
  intro x hx
  rw [f.tsupport_normed_eq] at hx
  rw [Metric.mem_closedBall, Real.dist_eq] at hx
  have hrout : f.rOut = r := rfl
  rw [hrout] at hx
  have h2 := abs_le.mp hx
  have hrv : r = (b - a) / 4 := hr
  have hcv : c = (a + b) / 2 := hc
  constructor
  · have := h2.1
    linarith
  · have := h2.2
    linarith

/-- A test function with vanishing integral is the derivative of a test function. -/
theorem exists_test_primitive {φ : ℝ → ℝ} {a b : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Ioo a b)
    (hzero : (∫ x, φ x) = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioo a b ∧
      deriv ψ = φ := by
  rcases eq_empty_or_nonempty (tsupport φ) with hempty | hne
  · refine ⟨fun _ => 0, contDiff_const, ?_, ?_, ?_⟩
    · exact HasCompactSupport.intro isCompact_empty fun x _ => rfl
    · intro x hx
      exact absurd hx (by simp [tsupport, Function.support])
    · funext x
      have hφ0 : φ x = 0 := by
        have : x ∉ tsupport φ := by rw [hempty]; exact notMem_empty x
        exact Function.notMem_support.mp fun hmem => this (subset_closure hmem)
      rw [hφ0]
      simp
  · have hcompact : IsCompact (tsupport φ) := hcs
    set A₀ : ℝ := sInf (tsupport φ) with hA₀
    set B₀ : ℝ := sSup (tsupport φ) with hB₀
    have hA₀mem : A₀ ∈ tsupport φ := hcompact.sInf_mem hne
    have hB₀mem : B₀ ∈ tsupport φ := hcompact.sSup_mem hne
    have hA₀gt : a < A₀ := (hsupp hA₀mem).1
    have hB₀lt : B₀ < b := (hsupp hB₀mem).2
    set A : ℝ := (a + A₀) / 2 with hA
    set B : ℝ := (B₀ + b) / 2 with hB
    have hAlt : A < A₀ := by rw [hA]; linarith
    have hBgt : B₀ < B := by rw [hB]; linarith
    have hAB : A < B := by
      have : A₀ ≤ B₀ := le_csSup hcompact.isBounded.bddAbove hA₀mem |>.trans (le_refl _) |>.trans
        (le_refl _)
      linarith [hAlt, hBgt, this]
    have hbdd : BddBelow (tsupport φ) := hcompact.isBounded.bddBelow
    have hbdd' : BddAbove (tsupport φ) := hcompact.isBounded.bddAbove
    have hφzero : ∀ x, x ∉ Ioo A B → φ x = 0 := by
      intro x hx
      have hnot : x ∉ tsupport φ := by
        intro hmem
        refine hx ⟨?_, ?_⟩
        · have : A₀ ≤ x := csInf_le hbdd hmem
          linarith
        · have : x ≤ B₀ := le_csSup hbdd' hmem
          linarith
      exact Function.notMem_support.mp fun hmem => hnot (subset_closure hmem)
    have hcont : Continuous φ := hφ.continuous
    have hintAB : (∫ t in A..B, φ t) = 0 := by
      rw [intervalIntegral.integral_of_le (le_of_lt hAB)]
      have hsubset : ∀ x ∉ Ioc A B, φ x = 0 := by
        intro x hx
        refine hφzero x ?_
        intro hmem
        exact hx ⟨hmem.1, le_of_lt hmem.2⟩
      rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsubset]
      exact hzero
    refine ⟨fun x => ∫ t in A..x, φ t, contDiff_primitive (φ := φ) hφ A, ?_, ?_, ?_⟩
    · refine HasCompactSupport.intro (isCompact_Icc (a := A) (b := B)) fun x hx => ?_
      refine primitive_eq_zero_outside hcont hφzero hintAB x ?_
      intro hmem
      exact hx ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
    · intro x hx
      have hsub : tsupport (fun x => ∫ t in A..x, φ t) ⊆ Icc A B := by
        refine closure_minimal ?_ isClosed_Icc
        intro y hy
        by_contra hcon
        refine hy ?_
        refine primitive_eq_zero_outside hcont hφzero hintAB y ?_
        intro hmem
        exact hcon ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
      have hx' : x ∈ Icc A B := hsub hx
      exact ⟨by have := hx'.1; rw [hA] at this; linarith,
        by have := hx'.2; rw [hB] at this; linarith⟩
    · funext x
      have hd : HasDerivAt (fun y : ℝ => ∫ t in A..y, φ t) (φ x) x :=
        intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable A x)
          (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
      exact hd.deriv

end

end GaloisForLFunctions.HTGeometry
