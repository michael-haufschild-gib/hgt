import GaloisForLFunctions.HTGeometry.UpperEndDifferentialField
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Rational coordinates and prime-log sources in the upper-end field

The upper-end meromorphic differential field contains the coordinate field `ℂ(z)` faithfully and
contains every bounded-gauge prime-log Herglotz source together with all its complex translates.
This is the concrete one-variable carrier needed to turn functional relation rigidity into a
differential-algebraic independence statement.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology Polynomial Function

noncomputable section

/-- Every upper half-plane contains infinitely many points. -/
theorem upperTail_infinite (H : ℝ) : (upperTail H).Infinite := by
  let f : ℕ → ℂ := fun n ↦ ((H + 1 + n : ℝ) : ℂ) * Complex.I
  have hf : Function.Injective f := by
    intro m n hmn
    have him := congrArg Complex.im hmn
    simp [f] at him
    exact_mod_cast him
  apply (Set.infinite_range_of_injective hf).mono
  rintro z ⟨n, rfl⟩
  simp only [f, upperTail, mem_setOf_eq, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- Polynomial evaluation is analytic at the upper end. -/
theorem upperEnd_analyticOnNhd_polyEval (p : Polynomial ℂ) :
    AnalyticOnNhd ℂ (fun z => p.eval z) (upperTail 0) := by
  have h : AnalyticOnNhd ℂ (fun z => aeval z p) (univ : Set ℂ) :=
    analyticOnNhd_id.aeval_polynomial p
  have heq : (fun z => aeval z p) = (fun z => p.eval z) := by
    funext z
    simp [aeval_def]
  rw [heq] at h
  exact h.mono (subset_univ _)

/-- Polynomial coefficients as genuine coordinate-function germs at the upper end. -/
noncomputable def upperEndPolyToAnalytic :
    Polynomial ℂ →+* upperEndAnalyticSubring :=
  ((Germ.coeRingHom upperEndFilter).comp
    (Pi.ringHom (fun z => Polynomial.evalRingHom z))).codRestrict
      upperEndAnalyticSubring
      (fun p => ⟨fun z => p.eval z, 0, upperEnd_analyticOnNhd_polyEval p, rfl⟩)

/-- Polynomial evaluation remains faithful after passing to upper-end germs. -/
theorem upperEndPolyToAnalytic_injective :
    Injective upperEndPolyToAnalytic := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hgerm : (↑(fun z => p.eval z) : Germ upperEndFilter ℂ) = 0 := by
    have h2 := congrArg Subtype.val hp
    rwa [ZeroMemClass.coe_zero] at h2
  rw [← Germ.coe_zero, Germ.coe_eq] at hgerm
  change ∀ᶠ z in upperEndFilter, p.eval z = 0 at hgerm
  rw [upperEndFilter_basis.eventually_iff] at hgerm
  obtain ⟨H, -, hH⟩ := hgerm
  have hroots : upperTail H ⊆ {x | p.IsRoot x} := hH
  exact Polynomial.eq_zero_of_infinite_isRoot p ((upperTail_infinite H).mono hroots)

/-- Polynomial coordinates embedded in the upper-end meromorphic field. -/
noncomputable def upperEndPolyToMero :
    Polynomial ℂ →+* upperEndMeroField :=
  letI := isDomain_upperEndAnalyticSubring
  (algebraMap upperEndAnalyticSubring upperEndMeroField).comp upperEndPolyToAnalytic

theorem upperEndPolyToMero_injective : Injective upperEndPolyToMero := by
  letI := isDomain_upperEndAnalyticSubring
  exact (IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField).comp
    upperEndPolyToAnalytic_injective

/-- **Faithful rational coordinate field.** The genuine field `ℂ(z)` embeds in the upper-end
meromorphic field by evaluation of its numerator and denominator. -/
noncomputable def upperEndRatfuncToMero : RatFunc ℂ →+* upperEndMeroField :=
  letI := isDomain_upperEndAnalyticSubring
  IsFractionRing.lift upperEndPolyToMero_injective

theorem upperEndRatfuncToMero_injective : Injective upperEndRatfuncToMero := by
  letI := isDomain_upperEndAnalyticSubring
  exact upperEndRatfuncToMero.injective

theorem upperEndRatfuncToMero_algebraMap_polynomial (p : Polynomial ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndRatfuncToMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
      upperEndPolyToMero p := by
  letI := isDomain_upperEndAnalyticSubring
  exact IsFractionRing.lift_algebraMap upperEndPolyToMero_injective p

/-- The prime-log source is analytic on the whole upper half-plane. -/
theorem analyticOnNhd_primeLogHerglotz_upperHalfPlane
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    AnalyticOnNhd ℂ (primeLogHerglotz u) upperHalfPlane :=
  (differentiableOn_primeLogHerglotz_upperHalfPlane u C hu).analyticOnNhd
    isOpen_upperHalfPlane

/-- A bounded-gauge prime-log Herglotz source as an eventual-analytic germ. -/
def primeLogHerglotzUpperEndAnalytic
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (primeLogHerglotz u),
    primeLogHerglotz u, 0, analyticOnNhd_primeLogHerglotz_upperHalfPlane u C hu, rfl⟩

/-- A bounded-gauge prime-log source as an upper-end meromorphic element. -/
def primeLogHerglotzUpperEndMero
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact algebraMap upperEndAnalyticSubring upperEndMeroField
    (primeLogHerglotzUpperEndAnalytic u C hu)

/-- Every complex translate of the source lives in the same upper-end field. -/
def translatedPrimeLogHerglotzUpperEndMero
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (h : ℂ) :
    upperEndMeroField :=
  upperEndTranslationMeroEquiv h (primeLogHerglotzUpperEndMero u C hu)

/-- The translated field element is the image of the genuinely translated analytic germ. -/
theorem translatedPrimeLogHerglotzUpperEndMero_algebraMap
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (h : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    translatedPrimeLogHerglotzUpperEndMero u C hu h =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (upperEndTranslationAnalyticEquiv h
          (primeLogHerglotzUpperEndAnalytic u C hu)) := by
  letI := isDomain_upperEndAnalyticSubring
  exact upperEndTranslationMeroEquiv_algebraMap h _

end

end GaloisForLFunctions.HTGeometry
