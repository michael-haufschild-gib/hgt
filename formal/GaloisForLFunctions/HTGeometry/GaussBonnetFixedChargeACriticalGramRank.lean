import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQuantumKernelLimits
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQuarticHarmonicJets

/-!
# Five harmonic coordinates for the critical Gibbs quantum Gram matrix

The critical two-copy fidelity kernel factors through the constant,
cosine-two, sine-two, cosine-four and sine-four coordinates. Every
finite critical Gram matrix therefore has rank at most five. All
sizes at least six have zero determinant, independently of inputs.
-/
noncomputable section
open Real Filter Set
open scoped Topology BigOperators ComplexOrder
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeACriticalGram (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (cos (x i - x j) ^ 4 : ℂ)

def egbFixedChargeAGramFeatures (ψ : ℝ) : Fin 5 → ℂ :=
  ![1, (cos (2 * ψ) : ℂ), (sin (2 * ψ) : ℂ), (cos (4 * ψ) : ℂ), (sin (4 * ψ) : ℂ)]

def egbFixedChargeAGramWeightedFeatures (ψ : ℝ) : Fin 5 → ℂ :=
  ![3 / 8, (cos (2 * ψ) : ℂ) / 2, (sin (2 * ψ) : ℂ) / 2,
    (cos (4 * ψ) : ℂ) / 8, (sin (4 * ψ) : ℂ) / 8]

theorem egbFixedChargeACriticalKernel_harmonic_separation (ψ θ : ℝ) :
    (cos (ψ - θ) ^ 4 : ℂ) = 3 / 8 +
      ((cos (2 * ψ) : ℂ) * (cos (2 * θ) : ℂ) + (sin (2 * ψ) : ℂ) * (sin (2 * θ) : ℂ)) / 2 +
      ((cos (4 * ψ) : ℂ) * (cos (4 * θ) : ℂ) + (sin (4 * ψ) : ℂ) * (sin (4 * θ) : ℂ)) / 8 := by
  have hr : cos (ψ - θ) ^ 4 = 3 / 8 +
      (cos (2 * ψ) * cos (2 * θ) + sin (2 * ψ) * sin (2 * θ)) / 2 +
      (cos (4 * ψ) * cos (4 * θ) + sin (4 * ψ) * sin (4 * θ)) / 8 := by
    have h := egbFixedChargeAQuarticProfile_harmonic_decomposition (ψ - θ)
    rw [show 2 * (ψ - θ) = 2 * ψ - 2 * θ by ring,
      show 4 * (ψ - θ) = 4 * ψ - 4 * θ by ring,
      cos_sub (2 * ψ) (2 * θ), cos_sub (4 * ψ) (4 * θ)] at h
    linarith
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hr
  norm_num only [Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div] at hc
  exact hc

theorem egbFixedChargeACriticalGram_factorization (n : ℕ) (x : Fin n → ℝ) :
    egbFixedChargeACriticalGram n x =
      (Matrix.of fun (i : Fin n) (k : Fin 5) => egbFixedChargeAGramWeightedFeatures (x i) k) *
      (Matrix.of fun (k : Fin 5) (j : Fin n) => egbFixedChargeAGramFeatures (x j) k) := by
  ext i j
  simp only [egbFixedChargeACriticalGram, Matrix.of_apply, Matrix.mul_apply,
    egbFixedChargeAGramWeightedFeatures, egbFixedChargeAGramFeatures,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero]
  rw [egbFixedChargeACriticalKernel_harmonic_separation]
  ring

theorem egbFixedChargeACriticalGram_rank_le_five (n : ℕ) (x : Fin n → ℝ) :
    (egbFixedChargeACriticalGram n x).rank ≤ 5 := by
  rw [egbFixedChargeACriticalGram_factorization]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

theorem egbFixedChargeACriticalGram_posSemidef (n : ℕ) (x : Fin n → ℝ) :
    (egbFixedChargeACriticalGram n x).PosSemidef :=
  egbFixedChargeAQuarticProfile_gram_posSemidef n x

theorem egbFixedChargeACriticalGram_det_zero (n : ℕ) (x : Fin (n + 6) → ℝ) :
    (egbFixedChargeACriticalGram (n + 6) x).det = 0 := by
  by_contra h
  have hu : IsUnit (egbFixedChargeACriticalGram (n + 6) x) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
  have hr := Matrix.rank_of_isUnit (egbFixedChargeACriticalGram (n + 6) x) hu
  have hb := egbFixedChargeACriticalGram_rank_le_five (n + 6) x
  rw [hr, Fintype.card_fin] at hb
  omega

end GaloisForLFunctions.HTGeometry
