import GaloisForLFunctions.HTGeometry.BurnolDepthCompletion
import GaloisForLFunctions.RHTower.PrimeBurnolThetaModularHolonomy

/-!
# Literal prime-depth completion classification

Every one-prime tower in the existing finite modular-support source has dense
span in the physical Burnol L² output.  The exact unsquared Euler amplitudes
are retained.  The scalar contrast coordinate of the existing prime-only
frame consequently has full-product relation closure at every nonneutral
displacement when two distinct primes are present.  When the prescriptions
coincide its closure is exactly the ordinary scalar graph.

These are unconditional source statements, not a construction of actual
theta admission.  This supplies the literal-source density and scalar
completion part of ULF-BFCC-001; the full matrix-frame and valuation-Cayley
classifications are separate claims.
-/

open MeasureTheory Set

namespace RHTower
noncomputable section

def primeBurnolLogRate (p : Nat.Primes) : Ioi (0 : ℝ) :=
  ⟨Real.log (p : ℝ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩

/-- Exact unsquared Euler amplitude times the geometric depth feature. -/
theorem primeBurnolWindowFeature_zero_eq_depth
    (p : Nat.Primes) (n : ℕ) (t : ℝ) :
    primeBurnolWindowFeature (p, n) 0 t =
      primeBurnolAmplitude (p, n) *
        HTGeometry.burnolDepthFeature (Real.log (p : ℝ)) n t := by
  have hfreq : primeBurnolLogFrequency (p, n) =
      (n + 1 : ℝ) * Real.log (p : ℝ) := by
    simp [primeBurnolLogFrequency, primeBurnolValuation,
      Nat.cast_pow, Real.log_pow]
  simp only [primeBurnolWindowFeature, primeBurnolComplexExponent, hfreq,
    Complex.ofReal_zero, mul_zero, add_zero, HTGeometry.burnolDepthFeature,
    Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg, neg_mul, mul_assoc]

theorem primeBurnolWindowFeatureLp_zero_eq_scaled_depth
    (p : Nat.Primes) (n : ℕ) :
    primeBurnolWindowFeatureLp (p, n) 0 =
      primeBurnolAmplitude (p, n) •
        HTGeometry.burnolDepthFeatureL2 (primeBurnolLogRate p) n := by
  apply Lp.ext
  have hbase : (primeBurnolWindowFeatureLp (p, n) 0 : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioi (0 : ℝ))] primeBurnolWindowFeature (p, n) 0 :=
    (memLp_primeBurnolWindowFeature (p, n) 0).coeFn_toLp
  filter_upwards [hbase, Lp.coeFn_smul
      (primeBurnolAmplitude (p, n))
      (HTGeometry.burnolDepthFeatureL2 (primeBurnolLogRate p) n),
      HTGeometry.burnolDepthFeatureL2_ae (primeBurnolLogRate p) n] with t ht hs hd
  rw [ht, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hd]
  exact primeBurnolWindowFeature_zero_eq_depth p n t

/-- The actual Euler coefficients are retained in the defining generators. -/
def primeBurnolLiteralDepthSpan (p : Nat.Primes) : Submodule ℂ primeBurnolHalfLineL2 :=
  Submodule.span ℂ (Set.range (fun n => primeBurnolWindowFeatureLp (p, n) 0))

theorem primeBurnolLiteralDepthSpan_eq (p : Nat.Primes) :
    primeBurnolLiteralDepthSpan p = HTGeometry.burnolDepthSpan (primeBurnolLogRate p) := by
  unfold primeBurnolLiteralDepthSpan
  simp_rw [primeBurnolWindowFeatureLp_zero_eq_scaled_depth]
  exact (HTGeometry.burnolDepthSpan_eq_span_scaled (primeBurnolLogRate p) _
    (fun n => primeBurnolAmplitude_ne_zero (p, n))).symm

/-- Every individual prime's literal unsquared Burnol columns already have dense output span. -/
theorem dense_primeBurnolLiteralDepthSpan (p : Nat.Primes) :
    Dense (primeBurnolLiteralDepthSpan p : Set primeBurnolHalfLineL2) := by
  rw [primeBurnolLiteralDepthSpan_eq]
  exact HTGeometry.dense_burnolDepthSpan (primeBurnolLogRate p)

/-- Scalar contrast coordinate of the corpus's prime-only frame, on the actual two-prime core. -/
def primeOnlyBurnolContrastRelation (p q : Nat.Primes) (a : ℝ) :
    Submodule ℂ (primeBurnolHalfLineL2 × primeBurnolHalfLineL2) :=
  Submodule.span ℂ
    (((fun x : primeBurnolHalfLineL2 => (x, (primeBurnolThetaContrast a p : ℂ) • x)) ''
      (primeBurnolLiteralDepthSpan p : Set _)) ∪
    ((fun x : primeBurnolHalfLineL2 => (x, (primeBurnolThetaContrast a q : ℂ) • x)) ''
      (primeBurnolLiteralDepthSpan q : Set _)))

/-- At nonzero displacement every input/output pair lies in the contrast relation's closure. -/
theorem primeOnlyBurnolContrastRelation_closure_eq_top
    {p q : Nat.Primes} (hpq : p ≠ q) {a : ℝ} (ha : a ≠ 0) :
    (primeOnlyBurnolContrastRelation p q a).topologicalClosure = ⊤ := by
  unfold primeOnlyBurnolContrastRelation
  rw [primeBurnolLiteralDepthSpan_eq, primeBurnolLiteralDepthSpan_eq]
  apply HTGeometry.burnolTwoClockRelation_closure_eq_top
  exact_mod_cast primeBurnolThetaContrast_ne_of_prime_ne ha hpq

/-- At neutral displacement the contrast relation closes to the zero operator graph. -/
theorem primeOnlyBurnolContrastRelation_zero
    (p q : Nat.Primes) :
    (primeOnlyBurnolContrastRelation p q 0).topologicalClosure =
      (0 : primeBurnolHalfLineL2 →ₗ[ℂ] primeBurnolHalfLineL2).graph := by
  unfold primeOnlyBurnolContrastRelation
  rw [primeBurnolLiteralDepthSpan_eq, primeBurnolLiteralDepthSpan_eq]
  simp only [primeBurnolThetaContrast, primeBurnolThetaRapidity, zero_mul, zero_div,
    Real.tanh_zero, Complex.ofReal_zero]
  simpa only [HTGeometry.burnolTwoClockRelation, zero_smul] using
    HTGeometry.burnolTwoClockRelation_closure_eq_graph
    (primeBurnolLogRate p) (primeBurnolLogRate q) 0

/-- Unconditional classification on literal source columns: ordinary graph when the prescriptions
coincide, whole product otherwise.  It assumes neither RH nor any admission criterion. -/
theorem primeOnlyBurnolContrastRelation_closure
    (p q : Nat.Primes) (a : ℝ) :
    (primeOnlyBurnolContrastRelation p q a).topologicalClosure =
      if p = q ∨ a = 0 then
        ((primeBurnolThetaContrast a p : ℂ) •
          (LinearMap.id : primeBurnolHalfLineL2 →ₗ[ℂ] primeBurnolHalfLineL2)).graph
      else ⊤ := by
  have hc : (primeBurnolThetaContrast a p : ℂ) =
      (primeBurnolThetaContrast a q : ℂ) ↔ p = q ∨ a = 0 := by
    constructor
    · intro h
      by_cases hpq : p = q
      · exact Or.inl hpq
      · right
        by_contra ha
        exact primeBurnolThetaContrast_ne_of_prime_ne ha hpq
          (Complex.ofReal_injective h)
    · rintro (rfl | rfl)
      · rfl
      · simp [primeBurnolThetaContrast, primeBurnolThetaRapidity]
  unfold primeOnlyBurnolContrastRelation
  rw [primeBurnolLiteralDepthSpan_eq, primeBurnolLiteralDepthSpan_eq]
  change (HTGeometry.burnolTwoClockRelation (primeBurnolLogRate p) (primeBurnolLogRate q)
    (primeBurnolThetaContrast a p : ℂ) (primeBurnolThetaContrast a q : ℂ)).topologicalClosure = _
  rw [HTGeometry.burnolTwoClockRelation_closure]
  simp only [hc]


end
end RHTower
