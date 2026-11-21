import GaloisForLFunctions.HTGeometry.Quantum.BoundaryResponse.LayeredGreen

/-!
# Green kernel of the harmonic extension

A boundary point source produces a voltage throughout the network. Each
spectral term is the product of the boundary eigenvector at the source
and its harmonic extension at the readout vertex.
-/

open Filter Matrix
open scoped Topology Matrix

namespace GaloisForLFunctions.HTGeometry.BoundaryResponse

open WeightedGraph

noncomputable section

/-- Boundary and series-interior vertices of the layered network. -/
abbrev LayeredSeriesVertex (K N : ℕ) :=
  LayeredBoundary K N ⊕ SeriesInterior (LayeredBoundary K N)

private abbrev ResponseMatrix (K N : ℕ) :=
  Matrix (LayeredBoundary K N) (LayeredBoundary K N) ℝ

/-- Voltage at any vertex for a unit source at a boundary vertex in the
shifted boundary problem. -/
def layeredGreenKernel (K N : ℕ) (s : ℝ) (z : LayeredSeriesVertex K N)
    (b : LayeredBoundary K N) : ℝ :=
  seriesMidpointExtension (fun v => ((layeredBoundaryLaplacian K N -
    s • (1 : ResponseMatrix K N))⁻¹) v b) z

private def midpointEvaluation (K N : ℕ) (z : LayeredSeriesVertex K N) :
    (LayeredBoundary K N → ℝ) →ₗ[ℝ] ℝ where
  toFun x := seriesMidpointExtension x z
  map_add' x y := by
    cases z with
    | inl _ => rfl
    | inr p =>
      simp only [seriesMidpointExtension, Pi.add_apply]
      ring
  map_smul' c x := by
    cases z with
    | inl _ => rfl
    | inr p =>
      simp only [seriesMidpointExtension, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
      ring

private theorem continuous_midpointEvaluation (K N : ℕ) (z : LayeredSeriesVertex K N) :
    Continuous (midpointEvaluation K N z) := by
  cases z with
  | inl v => exact continuous_apply v
  | inr p =>
    exact ((continuous_apply p.1.1).add (continuous_apply p.1.2)).div_const 2

/-- At a nonspectral shift, each Green coefficient pairs the boundary
source with the harmonic extension of its corresponding eigenvector. -/
theorem layeredGreenKernel_eq_spectralSum (K N : ℕ) (s : ℝ)
    (z : LayeredSeriesVertex K N) (b : LayeredBoundary K N)
    (hs : ∀ k, (isHermitian_layeredBoundaryLaplacian K N).eigenvalues k ≠ s) :
    layeredGreenKernel K N s z b =
      ∑ k, seriesMidpointExtension
          (⇑((isHermitian_layeredBoundaryLaplacian K N).eigenvectorBasis k)) z *
        (isHermitian_layeredBoundaryLaplacian K N).eigenvectorBasis k b *
        ((isHermitian_layeredBoundaryLaplacian K N).eigenvalues k - s)⁻¹ := by
  let hA := isHermitian_layeredBoundaryLaplacian K N
  let U : ResponseMatrix K N := hA.eigenvectorUnitary
  let d (k : LayeredBoundary K N) : ℝ := (hA.eigenvalues k - s)⁻¹
  have hc : (fun v => spectralGreen hA s v b) =
      ∑ k, (U b k * d k) • (fun v => U v k) := by
    funext v
    rw [Finset.sum_apply, spectralGreen_apply]
    apply Finset.sum_congr rfl
    intro k _
    change U v k * U b k * d k = (U b k * d k) * U v k
    ring
  rw [layeredGreenKernel, shiftedInverse_eq_spectralGreen hA s hs]
  change midpointEvaluation K N z (fun v => spectralGreen hA s v b) =
    ∑ k, seriesMidpointExtension (fun v => U v k) z * U b k * d k
  rw [hc, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  change U b k * d k * seriesMidpointExtension (fun v => U v k) z = _
  ring

/-- The squared boundary norm at a fixed readout is the sum of the
squared extension coefficients divided by squared spectral distances. -/
theorem sum_sq_layeredGreenKernel (K N : ℕ) (s : ℝ) (z : LayeredSeriesVertex K N)
    (hs : ∀ k, (isHermitian_layeredBoundaryLaplacian K N).eigenvalues k ≠ s) :
    (∑ b, layeredGreenKernel K N s z b ^ 2) =
      ∑ k, (seriesMidpointExtension
        (⇑((isHermitian_layeredBoundaryLaplacian K N).eigenvectorBasis k)) z) ^ 2 *
        (((isHermitian_layeredBoundaryLaplacian K N).eigenvalues k - s)⁻¹) ^ 2 := by
  let hA := isHermitian_layeredBoundaryLaplacian K N
  let U : ResponseMatrix K N := hA.eigenvectorUnitary
  let a (k : LayeredBoundary K N) : ℝ :=
    seriesMidpointExtension (⇑(hA.eigenvectorBasis k)) z * (hA.eigenvalues k - s)⁻¹
  have hrow : (fun b => layeredGreenKernel K N s z b) = U *ᵥ a := by
    funext b
    rw [layeredGreenKernel_eq_spectralSum K N s z b hs]
    change (∑ k, seriesMidpointExtension (⇑(hA.eigenvectorBasis k)) z *
        U b k * (hA.eigenvalues k - s)⁻¹) = ∑ k, U b k * a k
    exact Finset.sum_congr rfl fun k _ => by dsimp only [a]; ring
  have htrans : Uᵀ = star U := by
    ext v w
    simp only [Matrix.transpose_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      star_trivial]
  have hunit : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  calc
    _ = dotProduct (U *ᵥ a) (U *ᵥ a) := by rw [← hrow]; simp only [dotProduct, pow_two]
    _ = dotProduct a a := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, htrans,
        Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec]
    _ = _ := by
      unfold dotProduct
      exact Finset.sum_congr rfl fun k _ => by dsimp only [a]; ring

/-- The color pole seen by a boundary point source and an arbitrary
readout has coefficient equal to the product of their mode evaluations. -/
theorem tendsto_layeredGreenKernel_colorPole (K N : ℕ) (i : Fin (N + 1))
    (z : LayeredSeriesVertex K N) (b : LayeredBoundary K N) :
    Tendsto (fun s => (colorEigenvalue K i - s) * layeredGreenKernel K N s z b)
      (𝓝[≠] (colorEigenvalue K i))
      (𝓝 ((2 * ((K + 1 : ℕ) : ℝ))⁻¹ *
        (seriesMidpointExtension (colorMode i) z * colorMode i b))) := by
  let E := midpointEvaluation K N z
  let readout (M : ResponseMatrix K N) : ℝ := E (fun v => M v b)
  let x : LayeredBoundary K N → ℝ := colorMode i
  have hc : Continuous readout :=
    (continuous_midpointEvaluation K N z).comp
      (continuous_pi fun v => (continuous_apply b).comp (continuous_apply v))
  have hsmul (c : ℝ) (M : ResponseMatrix K N) : readout (c • M) = c * readout M :=
    map_smul E c (fun v => M v b)
  have hcolumn : (fun v => Matrix.vecMulVec x x v b) = x b • x :=
    funext fun v => mul_comm (x v) (x b)
  have hproj : readout (Matrix.vecMulVec (colorMode i) (colorMode i)) =
      seriesMidpointExtension (colorMode i) z * colorMode i b := by
    change E (fun v => Matrix.vecMulVec x x v b) = _
    rw [hcolumn, map_smul]
    exact mul_comm (x b) (seriesMidpointExtension x z)
  have h := hc.continuousAt.tendsto.comp (tendsto_layeredBoundaryShiftedInverse_colorPole K N i)
  change Tendsto (fun s => (colorEigenvalue K i - s) *
    readout ((layeredBoundaryLaplacian K N - s • (1 : ResponseMatrix K N))⁻¹)) _ _
  simpa only [Function.comp_def, hsmul, hproj] using h

#print axioms layeredGreenKernel_eq_spectralSum
#print axioms sum_sq_layeredGreenKernel
#print axioms tendsto_layeredGreenKernel_colorPole

end

end GaloisForLFunctions.HTGeometry.BoundaryResponse
