import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Topology.Instances.Matrix

/-!
# Finite spectral Green functions

The shifted inverse of a real symmetric matrix is a sum of spectral
projectors divided by the shifted eigenvalues. At each real level the
projector at that level is the coefficient of the pole; the remaining
spectral terms are continuous there.
-/

open Filter Matrix Set
open scoped Topology Matrix

namespace GaloisForLFunctions.HTGeometry.BoundaryResponse

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

private abbrev spectralConjugation (hA : A.IsHermitian) :=
  Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hA.eigenvectorUnitary

private def spectralMultiplier (hA : A.IsHermitian) (d : ι → ℝ) : Matrix ι ι ℝ :=
  spectralConjugation hA (Matrix.diagonal d)

/-- Spectral Green function, with each reciprocal totalized at its own pole. -/
def spectralGreen (hA : A.IsHermitian) (s : ℝ) : Matrix ι ι ℝ :=
  spectralMultiplier hA fun k => (hA.eigenvalues k - s)⁻¹

/-- Orthogonal spectral projector at the indicated level. -/
def spectralPoleProjector (hA : A.IsHermitian) (μ : ℝ) : Matrix ι ι ℝ :=
  spectralMultiplier hA fun k => if hA.eigenvalues k = μ then 1 else 0

private def regularMultiplier (hA : A.IsHermitian) (μ s : ℝ) (k : ι) : ℝ :=
  if hA.eigenvalues k = μ then 0 else (hA.eigenvalues k - s)⁻¹

/-- Green function with the terms at one spectral level removed. -/
def spectralGreenRegularPart (hA : A.IsHermitian) (μ s : ℝ) : Matrix ι ι ℝ :=
  spectralMultiplier hA (regularMultiplier hA μ s)

private theorem spectralMultiplier_apply (hA : A.IsHermitian) (d : ι → ℝ) (i j : ι) :
    spectralMultiplier hA d i j =
      ∑ k, (hA.eigenvectorUnitary : Matrix ι ι ℝ) i k *
        (hA.eigenvectorUnitary : Matrix ι ι ℝ) j k * d k := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  change (U * Matrix.diagonal d * star U) i j = ∑ k, U i k * U j k * d k
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial]
  ring

/-- Entrywise Green function expansion in an orthonormal eigenbasis. -/
theorem spectralGreen_apply (hA : A.IsHermitian) (s : ℝ) (i j : ι) :
    spectralGreen hA s i j =
      ∑ k, (hA.eigenvectorUnitary : Matrix ι ι ℝ) i k *
        (hA.eigenvectorUnitary : Matrix ι ι ℝ) j k * (hA.eigenvalues k - s)⁻¹ :=
  spectralMultiplier_apply hA _ i j

theorem spectralPoleProjector_apply (hA : A.IsHermitian) (μ : ℝ) (i j : ι) :
    spectralPoleProjector hA μ i j =
      ∑ k, (hA.eigenvectorUnitary : Matrix ι ι ℝ) i k *
        (hA.eigenvectorUnitary : Matrix ι ι ℝ) j k * (if hA.eigenvalues k = μ then 1 else 0) :=
  spectralMultiplier_apply hA _ i j

private theorem sub_scalar_eq_spectral (hA : A.IsHermitian) (s : ℝ) :
    A - s • (1 : Matrix ι ι ℝ) = spectralMultiplier hA (fun k => hA.eigenvalues k - s) := by
  have hd : A = spectralConjugation hA (Matrix.diagonal hA.eigenvalues) := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hA.spectral_theorem
  unfold spectralMultiplier
  rw [← Matrix.diagonal_sub, ← Matrix.smul_one_eq_diagonal, map_sub, map_smul, map_one, ← hd]

/-- The spectral Green function is the two-sided shifted inverse away
from the spectrum. -/
theorem spectralGreen_mul_shift (hA : A.IsHermitian) (s : ℝ)
    (hs : ∀ k, hA.eigenvalues k ≠ s) :
    spectralGreen hA s * (A - s • (1 : Matrix ι ι ℝ)) = 1 ∧
      (A - s • (1 : Matrix ι ι ℝ)) * spectralGreen hA s = 1 := by
  have hm (k : ι) : hA.eigenvalues k - s ≠ 0 := sub_ne_zero.mpr (hs k)
  rw [sub_scalar_eq_spectral hA s]
  unfold spectralGreen spectralMultiplier
  constructor
  · rw [← map_mul, Matrix.diagonal_mul_diagonal]
    simp only [inv_mul_cancel₀ (hm _), Matrix.diagonal_one, map_one]
  · rw [← map_mul, Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (hm _), Matrix.diagonal_one, map_one]

theorem shiftedInverse_eq_spectralGreen (hA : A.IsHermitian) (s : ℝ)
    (hs : ∀ k, hA.eigenvalues k ≠ s) :
    (A - s • (1 : Matrix ι ι ℝ))⁻¹ = spectralGreen hA s :=
  Matrix.inv_eq_right_inv (spectralGreen_mul_shift hA s hs).2

/-- The terms at a fixed spectral level form its pole projector; all other
terms are in the regular part. This identity uses Lean's total inverse. -/
theorem spectralGreen_eq_pole_add_regular (hA : A.IsHermitian) (μ s : ℝ) :
    spectralGreen hA s = (μ - s)⁻¹ • spectralPoleProjector hA μ + spectralGreenRegularPart hA μ s := by
  unfold spectralGreen spectralPoleProjector spectralGreenRegularPart spectralMultiplier
  rw [← map_smul, ← map_add, ← Matrix.diagonal_smul, Matrix.diagonal_add]
  congr 2
  funext k
  by_cases hk : hA.eigenvalues k = μ
  · simp only [regularMultiplier, hk, if_true, Pi.smul_apply, smul_eq_mul, mul_one, add_zero]
  · simp only [regularMultiplier, if_neg hk, Pi.smul_apply, smul_eq_mul, mul_zero, zero_add]

/-- Removing the terms at a level leaves a Green function continuous there. -/
theorem continuousAt_spectralGreenRegularPart (hA : A.IsHermitian) (μ : ℝ) :
    ContinuousAt (spectralGreenRegularPart hA μ) μ := by
  have hs (k : ι) : ContinuousAt (fun s => regularMultiplier hA μ s k) μ := by
    by_cases hk : hA.eigenvalues k = μ
    · simpa only [regularMultiplier, if_pos hk] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) μ)
    · have h : ContinuousAt (fun s : ℝ => hA.eigenvalues k - s) μ :=
        continuousAt_const.sub continuousAt_id
      have he : ContinuousAt (fun s : ℝ => (hA.eigenvalues k - s)⁻¹) μ :=
        h.inv₀ (sub_ne_zero.mpr hk)
      simpa only [regularMultiplier, if_neg hk] using he
  have hd : ContinuousAt (fun s => Matrix.diagonal (regularMultiplier hA μ s)) μ := by
    change ContinuousAt (fun s => fun i j => Matrix.diagonal (regularMultiplier hA μ s) i j) μ
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq] using hs i
    · simpa only [Matrix.diagonal_apply_ne _ hij] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) μ)
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  change ContinuousAt (fun s => U * Matrix.diagonal (regularMultiplier hA μ s) * star U) μ
  exact (continuousAt_const.mul hd).mul continuousAt_const

/-- Every real level has a punctured neighborhood free of the other
eigenvalues. The shifted inverse there is given by the Green function. -/
theorem shiftedInverse_eventuallyEq_spectralGreen (hA : A.IsHermitian) (μ : ℝ) :
    (fun s => (A - s • (1 : Matrix ι ι ℝ))⁻¹) =ᶠ[𝓝[≠] μ] spectralGreen hA := by
  let rest := Set.range hA.eigenvalues \ {μ}
  have hf : rest.Finite := (Set.finite_range _).subset sdiff_subset
  have hm : μ ∉ rest := fun h => h.2 (Set.mem_singleton μ)
  have hn : restᶜ ∈ 𝓝 μ := hf.isClosed.isOpen_compl.mem_nhds hm
  have hne : ∀ᶠ s in 𝓝[≠] μ, s ≠ μ := self_mem_nhdsWithin
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn, hne] with s hs hne'
  exact shiftedInverse_eq_spectralGreen hA s fun k he =>
    hs ⟨⟨k, he⟩, hne'⟩

/-- The shifted inverse scaled by distance to the level converges to its
orthogonal spectral projector, with sign convention `μ - s`. -/
theorem tendsto_shiftedInverse_pole (hA : A.IsHermitian) (μ : ℝ) :
    Tendsto (fun s => (μ - s) • (A - s • (1 : Matrix ι ι ℝ))⁻¹)
      (𝓝[≠] μ) (𝓝 (spectralPoleProjector hA μ)) := by
  have hd : ContinuousAt (fun s : ℝ => μ - s) μ := continuousAt_const.sub continuousAt_id
  have hz : Tendsto (fun s : ℝ => μ - s) (𝓝[≠] μ) (𝓝 0) := by
    simpa only [ContinuousWithinAt, sub_self] using hd.continuousWithinAt (s := ({μ}ᶜ : Set ℝ))
  have hr := (continuousAt_spectralGreenRegularPart hA μ).continuousWithinAt
    (s := ({μ}ᶜ : Set ℝ))
  have hl : Tendsto (fun s => spectralPoleProjector hA μ + (μ - s) • spectralGreenRegularPart hA μ s)
      (𝓝[≠] μ) (𝓝 (spectralPoleProjector hA μ)) := by
    simpa only [zero_smul, add_zero] using tendsto_const_nhds.add (hz.smul hr)
  apply hl.congr'
  have hne : ∀ᶠ s in 𝓝[≠] μ, s ≠ μ := self_mem_nhdsWithin
  filter_upwards [shiftedInverse_eventuallyEq_spectralGreen hA μ, hne] with s hs hn
  rw [hs, spectralGreen_eq_pole_add_regular hA μ s, smul_add, smul_smul,
    mul_inv_cancel₀ (sub_ne_zero.mpr hn.symm), one_smul]

#print axioms spectralGreen_apply
#print axioms spectralGreen_mul_shift
#print axioms spectralGreen_eq_pole_add_regular
#print axioms tendsto_shiftedInverse_pole

end

end GaloisForLFunctions.HTGeometry.BoundaryResponse
