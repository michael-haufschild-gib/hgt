import GaloisForLFunctions.HeckeKreinToeplitz.Index.BoundedSignedSpectralMeasure
import GaloisForLFunctions.HeckeKreinToeplitz.Index.TorusSpectralForms
import GaloisForLFunctions.HTGeometry.TorusL2Positivity

/-!
# Polynomial corrections for signed torus spectra

Finite combinations of lattice translates become continuous torus polynomials.
Their repaired Gram inequality extends to every square-integrable spectral test.
-/

open Complex Finset MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

variable {I : Type*} [Countable I]

/-- The polynomial representing a finite combination of kernel translates. -/
def torusTranslatePolynomial {r : ℕ}
    (x : Fin r → Multiplicative (I →₀ ℤ)) (w : Fin r → ℂ) : C(UnitAddTorus I, ℂ) :=
  ∑ b, w b • torusCharacter (-(x b).toAdd)

/-- Integration of a translated polynomial against one character is a
finite combination of translated Fourier coefficients. -/
theorem integral_torusTranslatePolynomial_mul_character
    (μ : Measure (UnitAddTorus I)) [IsFiniteMeasure μ] {r : ℕ}
    (x : Fin r → Multiplicative (I →₀ ℤ)) (w : Fin r → ℂ)
    (g : Multiplicative (I →₀ ℤ)) :
    (∫ θ, torusTranslatePolynomial x w θ * torusCharacter g.toAdd θ ∂μ) =
      ∑ b, w b * torusFourierKernel μ ((x b)⁻¹ * g) := by
  have he (θ : UnitAddTorus I) :
      torusTranslatePolynomial x w θ * torusCharacter g.toAdd θ =
        ∑ b, w b * torusCharacter (((x b)⁻¹ * g).toAdd) θ := by
    simp only [torusTranslatePolynomial, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul, sum_mul]
    apply sum_congr rfl fun b _ => ?_
    change (w b * torusCharacter (-(x b).toAdd) θ) * torusCharacter g.toAdd θ =
      w b * torusCharacter (-(x b).toAdd + g.toAdd) θ
    rw [torusCharacter_add_index, mul_assoc]
  have hint (b : Fin r) : Integrable
      (fun θ => w b * torusCharacter (((x b)⁻¹ * g).toAdd) θ) μ :=
    ((torusCharacter (((x b)⁻¹ * g).toAdd)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  simp_rw [he]
  rw [integral_finsetSum _ fun b _ => hint b]
  simp only [integral_const_mul, torusFourierKernel]

/-- The signed integral of a polynomial packet separates into its coefficient
functionals. -/
theorem signed_integral_torus_packet
    (P N : Measure (UnitAddTorus I)) [IsFiniteMeasure P] [IsFiniteMeasure N]
    (q : C(UnitAddTorus I, ℂ)) {r : ℕ}
    (x : Fin r → I →₀ ℤ) (c : Fin r → ℂ) :
    (∫ θ, q θ * (∑ a, c a * torusCharacter (x a) θ) ∂P) -
      (∫ θ, q θ * (∑ a, c a * torusCharacter (x a) θ) ∂N) =
      ∑ a, c a * ((∫ θ, q θ * torusCharacter (x a) θ ∂P) -
        ∫ θ, q θ * torusCharacter (x a) θ ∂N) := by
  have he (μ : Measure (UnitAddTorus I)) [IsFiniteMeasure μ] :
      (∫ θ, q θ * (∑ a, c a * torusCharacter (x a) θ) ∂μ) =
        ∑ a, c a * ∫ θ, q θ * torusCharacter (x a) θ ∂μ := by
    have hint (a : Fin r) : Integrable
        (fun θ => q θ * (c a * torusCharacter (x a) θ)) μ := by
      have hc : Continuous (fun θ => q θ * (c a * torusCharacter (x a) θ)) :=
        q.continuous.mul (continuous_const.mul (torusCharacter (x a)).continuous)
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp only [mul_sum]
    rw [integral_finsetSum _ fun a _ => hint a]
    apply sum_congr rfl fun a _ => ?_
    calc
      (∫ θ, q θ * (c a * torusCharacter (x a) θ) ∂μ) =
          ∫ θ, c a * (q θ * torusCharacter (x a) θ) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun θ => mul_left_comm _ _ _)
      _ = c a * ∫ θ, q θ * torusCharacter (x a) θ ∂μ := integral_const_mul _ _
  rw [he P, he N, ← sum_sub_distrib]
  exact sum_congr rfl fun a _ => (mul_sub _ _ _).symm

/-- Gram energy respects subtraction of kernels. -/
private theorem hermQuad_gram_sub {G : Type*} [Group G] {J : Type*} [Fintype J]
    (k l : G → ℂ) (x : J → G) (c : J → ℂ) :
    hermQuad (gram (fun g => k g - l g) x) c =
      hermQuad (gram k x) c - hermQuad (gram l x) c := by
  simp only [hermQuad_gram, mul_sub, sub_mul, sum_sub_distrib, Complex.sub_re]

/-- The bounded Pontryagin corrections become polynomial densities for the
signed spectral measure, and repair its form on every square-integrable test. -/
theorem exists_signed_torus_measure_with_repaired_L2
    {k : Multiplicative (I →₀ ℤ) → ℂ} (hk : IsHermKernel k)
    {m : ℕ} (hm : negIndex k = m)
    (hbounded : ∃ M : ℝ, ∀ g, ‖k g‖ ≤ M) :
    ∃ P N : FiniteMeasure (UnitAddTorus I),
      (P : Measure (UnitAddTorus I)) ⟂ₘ (N : Measure (UnitAddTorus I)) ∧
      (∀ g, k g = torusFourierKernel (P : Measure _) g - torusFourierKernel (N : Measure _) g) ∧
      ∃ q : Fin m → C(UnitAddTorus I, ℂ),
        ∀ f : UnitAddTorus I → ℂ, MemLp f 2 ((P : Measure _) + (N : Measure _)) →
          0 ≤ (∫ θ, ‖f θ‖ ^ 2 ∂(P : Measure _)) -
            (∫ θ, ‖f θ‖ ^ 2 ∂(N : Measure _)) +
            ∑ i, ‖(∫ θ, q i θ * f θ ∂(P : Measure _)) -
              ∫ θ, q i θ * f θ ∂(N : Measure _)‖ ^ 2 := by
  classical
  obtain ⟨r, x₀, w, C, _, hbound, hrepair⟩ :=
    exists_bounded_pontryagin_corrections hk hm hbounded
  let φ : Fin m → Multiplicative (I →₀ ℤ) → ℂ :=
    fun i g => ∑ b, w i b * k ((x₀ b)⁻¹ * g)
  obtain ⟨P, N, hmut, hcoeff⟩ :=
    exists_signed_torus_measure_of_bounded_corrections hk φ hbound hrepair
  have hrepr (g : Multiplicative (I →₀ ℤ)) :
      k g = torusFourierKernel (P : Measure _) g - torusFourierKernel (N : Measure _) g :=
    hcoeff g.toAdd
  let q : Fin m → C(UnitAddTorus I, ℂ) := fun i => torusTranslatePolynomial x₀ (w i)
  have hφ (i : Fin m) (g : Multiplicative (I →₀ ℤ)) :
      φ i g = (∫ θ, q i θ * torusCharacter g.toAdd θ ∂(P : Measure _)) -
        ∫ θ, q i θ * torusCharacter g.toAdd θ ∂(N : Measure _) := by
    dsimp only [φ, q]
    rw [integral_torusTranslatePolynomial_mul_character (P : Measure _) x₀ (w i) g,
      integral_torusTranslatePolynomial_mul_character (N : Measure _) x₀ (w i) g,
      ← sum_sub_distrib]
    apply sum_congr rfl fun b _ => ?_
    rw [hrepr]
    exact mul_sub _ _ _
  refine ⟨P, N, hmut, hrepr, q, ?_⟩
  apply torus_signed_corrected_nonneg_of_character_span (P : Measure _) (N : Measure _) hmut q
  intro f hf
  obtain ⟨n, x, c, hc⟩ := exists_finite_torus_packet hf
  have hform : hermQuad (gram k (fun a => Multiplicative.ofAdd (x a))) c =
      (∫ θ, ‖f θ‖ ^ 2 ∂(P : Measure _)) - ∫ θ, ‖f θ‖ ^ 2 ∂(N : Measure _) := by
    have hkfun : k = fun g => torusFourierKernel (P : Measure _) g -
        torusFourierKernel (N : Measure _) g := funext hrepr
    rw [hkfun, hermQuad_gram_sub, hermQuad_gram_torusFourierKernel,
      hermQuad_gram_torusFourierKernel]
    simp_rw [hc]
    rfl
  have hcorr (i : Fin m) : (∑ a, c a * φ i (Multiplicative.ofAdd (x a))) =
      (∫ θ, q i θ * f θ ∂(P : Measure _)) -
        ∫ θ, q i θ * f θ ∂(N : Measure _) := by
    simp_rw [hc]
    rw [signed_integral_torus_packet]
    exact sum_congr rfl fun a _ => congrArg (fun z => c a * z) (hφ i _)
  have h := hrepair n (fun a => Multiplicative.ofAdd (x a)) c
  change 0 ≤ hermQuad (gram k (fun a => Multiplicative.ofAdd (x a))) c +
    ∑ i, normSq (∑ a, c a * φ i (Multiplicative.ofAdd (x a))) at h
  simpa only [hform, hcorr, normSq_eq_norm_sq] using h

end

end GaloisForLFunctions.HeckeKreinToeplitz
