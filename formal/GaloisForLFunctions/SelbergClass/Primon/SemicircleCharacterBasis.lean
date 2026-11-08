import GaloisForLFunctions.SelbergClass.Primon.SpectralCharacterAlgebra
import GaloisForLFunctions.SelbergClass.Primon.SemicircleObservableLinear
import GaloisForLFunctions.RHTower.EntireExponentialMomentPolynomialDensity
import GaloisForLFunctions.HTGeometry.MonicOrthoExtremalComparison

/-!
# Complete Chebyshev basis of the semicircle Hilbert space

Prime Favard polynomials have every degree and are finite combinations of
spectral characters. They therefore span all polynomial observables.
Compact spectral support supplies every exponential moment, so polynomial
density upgrades character orthogonality to a complete Hilbert basis.
-/

open MeasureTheory Set ProbabilityTheory
open _root_.RHTower _root_.HTGeometry
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private def polynomialContinuousMap : Polynomial ℝ →ₗ[ℝ] C(ℝ, ℝ) where
  toFun P := ⟨fun x => P.eval x, by fun_prop⟩
  map_add' P Q := by ext x; simp
  map_smul' c P := by ext x; simp

/-- Polynomial observables realized in the actual semicircle Hilbert space. -/
def semicirclePolynomialMap : Polynomial ℝ →ₗ[ℝ] SemicircleL2 :=
  semicircleObservableMap.comp polynomialContinuousMap

/-- The algebraic span of every spectral character, including both parities. -/
def spectralCharacterSpan : Submodule ℝ SemicircleL2 :=
  Submodule.span ℝ (Set.range spectralCharacterVector)

/-- A prime Favard polynomial realizes the corresponding two-character correction in `L²`. -/
theorem semicirclePolynomialMap_kesten_add_two (p : Nat.Primes) (n : ℕ) :
    semicirclePolynomialMap (kestenPolynomial p (n + 2)) =
      spectralCharacterVector (n + 2) - (p : ℝ)⁻¹ • spectralCharacterVector n := by
  change semicircleObservableMap (polynomialContinuousMap (kestenPolynomial p (n + 2))) =
    semicircleObservableMap (spectralCharacter (n + 2)) -
      (p : ℝ)⁻¹ • semicircleObservableMap (spectralCharacter n)
  rw [← map_smul, ← map_sub]
  congr 1
  ext x
  exact kestenPolynomial_eval_spectral p n x

private theorem kestenPolynomial_mem_characterSpan (p : Nat.Primes) (n : ℕ) :
    semicirclePolynomialMap (kestenPolynomial p n) ∈ spectralCharacterSpan := by
  rcases n with _ | _ | n
  · have he : polynomialContinuousMap (kestenPolynomial p 0) = spectralCharacter 0 := by
      ext x
      simp [polynomialContinuousMap]
    change semicircleObservableMap (polynomialContinuousMap (kestenPolynomial p 0)) ∈ _
    rw [he]
    exact Submodule.subset_span (Set.mem_range_self 0)
  · have he : polynomialContinuousMap (kestenPolynomial p 1) = spectralCharacter 1 := by
      ext x
      simp [polynomialContinuousMap]
    change semicircleObservableMap (polynomialContinuousMap (kestenPolynomial p 1)) ∈ _
    rw [he]
    exact Submodule.subset_span (Set.mem_range_self 1)
  · rw [semicirclePolynomialMap_kesten_add_two]
    exact spectralCharacterSpan.sub_mem (Submodule.subset_span (Set.mem_range_self (n + 2)))
      (spectralCharacterSpan.smul_mem _ (Submodule.subset_span (Set.mem_range_self n)))

/-- Every polynomial observable is a finite linear combination of spectral characters. -/
theorem polynomial_mem_spectralCharacterSpan (P : Polynomial ℝ) :
    semicirclePolynomialMap P ∈ spectralCharacterSpan := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hP := mem_span_of_degree_lt (kestenPolynomial_natDegree p)
    (fun n => (kestenPolynomial_monic p n).ne_zero) (P.natDegree + 1) P
    (lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self P.natDegree))
  have hle : Submodule.span ℝ (kestenPolynomial p '' {k : ℕ | k < P.natDegree + 1}) ≤
      spectralCharacterSpan.comap semicirclePolynomialMap := by
    apply Submodule.span_le.2
    rintro _ ⟨n, hn, rfl⟩
    exact kestenPolynomial_mem_characterSpan p n
  exact hle hP

/-- Compact spectral support gives the entire bilateral exponential-moment window. -/
theorem semicircle_entireExponentialMoments :
    HasEntireExponentialMoments (semicircleSpectralLaw : Measure ℝ) := by
  change integrableExpSet id (semicircleSpectralLaw : Measure ℝ) = Set.univ
  ext t
  simp only [Set.mem_univ, iff_true]
  change Integrable (fun x : ℝ => Real.exp (t * x)) (semicircleSpectralLaw : Measure ℝ)
  exact integrable_semicircleSpectralLaw_continuous ⟨_, by fun_prop⟩

private theorem semicirclePolynomialMap_X_pow (n : ℕ) :
    semicirclePolynomialMap (Polynomial.X ^ n) =
      realMonomialLp (semicircleSpectralLaw : Measure ℝ) semicircle_entireExponentialMoments n := by
  apply (MemLp.toLp_eq_toLp_iff
    (memLp_semicircle_continuous (polynomialContinuousMap (Polynomial.X ^ n)))
    (monomial_memLp_two_of_entireExponentialMoments semicircle_entireExponentialMoments n)).2
  apply Filter.Eventually.of_forall
  intro x
  simp [polynomialContinuousMap]

/-- The full character family is total in semicircle `L²`. -/
theorem spectralCharacterSpan_closure : spectralCharacterSpan.topologicalClosure = ⊤ := by
  have hle : realMonomialSpan (semicircleSpectralLaw : Measure ℝ)
      semicircle_entireExponentialMoments ≤ spectralCharacterSpan := by
    apply Submodule.span_le.2
    rintro _ ⟨n, rfl⟩
    rw [← semicirclePolynomialMap_X_pow]
    exact polynomial_mem_spectralCharacterSpan _
  have h := Submodule.topologicalClosure_mono hle
  rw [realMonomialSpan_closure_eq_top] at h
  exact top_le_iff.mp h

/-- Complete orthonormal Chebyshev basis for the actual semicircle probability law. -/
def semicircleCharacterBasis : HilbertBasis ℕ ℝ SemicircleL2 :=
  HilbertBasis.mk orthonormal_spectralCharacterVector (by
    change ⊤ ≤ spectralCharacterSpan.topologicalClosure
    rw [spectralCharacterSpan_closure])

@[simp] theorem semicircleCharacterBasis_apply (n : ℕ) :
    semicircleCharacterBasis n = spectralCharacterVector n := by
  exact congrFun (HilbertBasis.coe_mk _ _) n

/-- The complete Fourier coordinate of a semicircle observable is its character inner product. -/
theorem semicircleCharacterBasis_repr (f : SemicircleL2) (n : ℕ) :
    semicircleCharacterBasis.repr f n = inner ℝ (spectralCharacterVector n) f := by
  rw [HilbertBasis.repr_apply_apply, semicircleCharacterBasis_apply]

/-- Every square-integrable semicircle observable has its convergent character expansion. -/
theorem hasSum_spectralCharacters (f : SemicircleL2) :
    HasSum (fun n => inner ℝ (spectralCharacterVector n) f • spectralCharacterVector n) f := by
  simpa only [semicircleCharacterBasis_repr, semicircleCharacterBasis_apply] using
    semicircleCharacterBasis.hasSum_repr f

end
end GaloisForLFunctions.SelbergClass.Primon

