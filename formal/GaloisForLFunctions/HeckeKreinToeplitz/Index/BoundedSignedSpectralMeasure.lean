import GaloisForLFunctions.HeckeKreinToeplitz.Index.TorusFejerFourierCoefficients
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FreeLatticeWindows
import GaloisForLFunctions.HTGeometry.ContinuousDensityFiniteMeasures
import GaloisForLFunctions.HTGeometry.SignedMeasureCompactness

/-!
# Signed spectral measures from bounded Pontryagin corrections

Normalized Toeplitz densities and bounded correction squares give two
positive measure families with uniformly bounded masses. Expanding lattice
windows recover every Fourier coefficient; compactness and Jordan reduction
produce a mutually singular signed representation of the kernel.
-/

open Complex Finset MeasureTheory Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

variable {I : Type*} [Countable I] {m : ℕ}

/-- A repaired Toeplitz density is a difference of two positive measures with
uniformly bounded masses and an exact Fejér Fourier coefficient. -/
theorem exists_torus_fejer_measure_pair
    {k : Multiplicative (I →₀ ℤ) → ℂ} (hk : IsHermKernel k)
    (φ : Fin m → Multiplicative (I →₀ ℤ) → ℂ) {C : ℝ}
    (hbound : ∀ i g, ‖φ i g‖ ≤ C)
    (hrepair : ∀ (n : ℕ) (x : Fin n → Multiplicative (I →₀ ℤ)) (c : Fin n → ℂ),
      0 ≤ hermQuad (gram k x) c + ∑ i, normSq (∑ a, c a * φ i (x a)))
    (F : Finset I) (N : ℕ) :
    ∃ μ ν : FiniteMeasure (UnitAddTorus I),
      (μ.mass : ℝ) ≤ |(k 1).re| + m * C ^ 2 + 1 ∧
      (ν.mass : ℝ) ≤ |(k 1).re| + m * C ^ 2 + 1 ∧
      ∀ t, (∫ θ, torusCharacter t θ ∂(μ : Measure (UnitAddTorus I))) -
        ∫ θ, torusCharacter t θ ∂(ν : Measure (UnitAddTorus I)) =
        (freeLatticeFejerWeight F N t : ℂ) * k (Multiplicative.ofAdd t) := by
  classical
  let x := freeLatticeFinWindow F N
  have hx := freeLatticeFinWindow_injective F N
  let d : C(UnitAddTorus I, ℝ) :=
    ⟨torusKernelDensity k x, continuous_torusKernelDensity k x⟩
  let q : C(UnitAddTorus I, ℝ) :=
    ⟨torusCorrectionDensity x (fun i a => φ i (Multiplicative.ofAdd (x a))),
      continuous_torusCorrectionDensity _ _⟩
  have hq : ∀ θ, 0 ≤ q θ := torusCorrectionDensity_nonneg _ _
  have hdq : ∀ θ, 0 ≤ (d + q) θ :=
    torusKernelDensity_add_correction_nonneg k φ hrepair x
  let H : FiniteMeasure (UnitAddTorus I) := ⟨torusHaar I, inferInstance⟩
  let μ := continuousDensityFiniteMeasure H (d + q)
  let ν := continuousDensityFiniteMeasure H q
  have hint (f : C(UnitAddTorus I, ℝ)) : Integrable (fun θ => f θ) (torusHaar I) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmassq : (ν.mass : ℝ) ≤ m * C ^ 2 := by
    rw [mass_continuousDensityFiniteMeasure H q hq]
    exact integral_torusCorrectionDensity_le x hx _ (fun i a => hbound i _)
  have hmassμ : (μ.mass : ℝ) = (k 1).re + ν.mass := by
    rw [mass_continuousDensityFiniteMeasure H (d + q) hdq,
      mass_continuousDensityFiniteMeasure H q hq]
    change (∫ θ, d θ + q θ ∂torusHaar I) = _
    rw [integral_add (hint d) (hint q)]
    congr 1
    exact integral_torusKernelDensity hk x hx (freeLatticeWindow_card_pos F N)
  refine ⟨μ, ν, ?_, ?_, fun t => ?_⟩
  · rw [hmassμ]
    linarith only [le_abs_self (k 1).re, hmassq]
  · linarith only [abs_nonneg (k 1).re, hmassq]
  · rw [integral_continuousDensityFiniteMeasure H (d + q) hdq,
      integral_continuousDensityFiniteMeasure H q hq]
    have hi (f : C(UnitAddTorus I, ℝ)) : Integrable
        (fun θ => (f θ : ℂ) * torusCharacter t θ) (torusHaar I) := by
      have hc : Continuous (fun θ => (f θ : ℂ) * torusCharacter t θ) :=
        (Complex.continuous_ofReal.comp f.continuous).mul (torusCharacter t).continuous
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    change (∫ θ, ((d θ + q θ : ℝ) : ℂ) * torusCharacter t θ ∂torusHaar I) -
      (∫ θ, (q θ : ℂ) * torusCharacter t θ ∂torusHaar I) = _
    simp only [Complex.ofReal_add, add_mul]
    rw [integral_add (hi d) (hi q), add_sub_cancel_right]
    have hd (θ : UnitAddTorus I) : d θ = torusKernelDensity k x θ := rfl
    simp only [hd]
    rw [integral_torusKernelDensity_mul_character hk x t]
    have hs : (∑ a, ∑ b, if x b - x a = t then k (Multiplicative.ofAdd t) else 0) =
        (∑ a, ∑ b, if x b - x a = t then (1 : ℂ) else 0) *
          k (Multiplicative.ofAdd t) := by
      simp only [sum_mul]
      apply sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      split_ifs <;> simp only [one_mul, zero_mul]
    rw [hs, mul_div_right_comm]
    dsimp only [x]
    rw [normalized_freeLatticeFinWindow_pairs F N t]

/-- Bounded finite translate corrections produce a signed spectral measure;
its Jordan parts are mutually singular. -/
theorem exists_signed_torus_measure_of_bounded_corrections
    {k : Multiplicative (I →₀ ℤ) → ℂ} (hk : IsHermKernel k)
    (φ : Fin m → Multiplicative (I →₀ ℤ) → ℂ) {C : ℝ}
    (hbound : ∀ i g, ‖φ i g‖ ≤ C)
    (hrepair : ∀ (n : ℕ) (x : Fin n → Multiplicative (I →₀ ℤ)) (c : Fin n → ℂ),
      0 ≤ hermQuad (gram k x) c + ∑ i, normSq (∑ a, c a * φ i (x a))) :
    ∃ P N : FiniteMeasure (UnitAddTorus I),
      (P : Measure (UnitAddTorus I)) ⟂ₘ (N : Measure (UnitAddTorus I)) ∧
      ∀ t, k (Multiplicative.ofAdd t) =
        (∫ θ, torusCharacter t θ ∂(P : Measure (UnitAddTorus I))) -
        ∫ θ, torusCharacter t θ ∂(N : Measure (UnitAddTorus I)) := by
  classical
  have hex (a : Finset I × ℕ) := exists_torus_fejer_measure_pair hk φ hbound hrepair a.1 a.2
  choose μ ν hμ hν hcoeff using hex
  let B : ℝ≥0 := ⟨|(k 1).re| + m * C ^ 2 + 1, by positivity⟩
  have hlimit (t : I →₀ ℤ) : Tendsto (fun a : Finset I × ℕ =>
      (∫ θ, torusCharacter t θ ∂(μ a : Measure (UnitAddTorus I))) -
        ∫ θ, torusCharacter t θ ∂(ν a : Measure (UnitAddTorus I)))
      (atTop ×ˢ atTop) (𝓝 (k (Multiplicative.ofAdd t))) := by
    simp_rw [hcoeff]
    simpa only [Function.comp_apply, Complex.ofReal_one, one_mul] using
      ((Complex.continuous_ofReal.tendsto 1).comp
        (tendsto_freeLatticeFejerWeight t)).mul_const (k (Multiplicative.ofAdd t))
  obtain ⟨μ₀, ν₀, _, _, h₀⟩ := exists_finite_measure_pair_of_integral_difference_limit
    (l := atTop ×ˢ atTop) μ ν B (fun a => hμ a) (fun a => hν a)
    torusCharacter (fun t => k (Multiplicative.ofAdd t)) hlimit
  obtain ⟨P, N, hmut, hPN⟩ := exists_mutuallySingular_finite_measure_pair μ₀ ν₀
  refine ⟨P, N, hmut, fun t => ?_⟩
  rw [hPN (torusCharacter t), h₀ t]

end

end GaloisForLFunctions.HeckeKreinToeplitz
