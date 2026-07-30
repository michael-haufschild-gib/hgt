import GaloisForLFunctions.HTGeometry.AffineEigenbranchGeneralSecondOrderLaw

/-!
# Exact first-order transition law for a diagonal probe

Two simple affine eigenbranches are represented by canonical adjugate-column
eigenvector germs.  For any diagonal probe, the derivative of their
bilinear transition amplitude is controlled exactly by one spectral gap,
the two adjugate normalization factors, and the directed interaction
matrix elements.  This is the local mechanism by which an arbitrarily small
interaction creates new observable transition edges.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Bilinear transition amplitude of a diagonal probe between two canonical
adjugate-column eigenvector germs. -/
def affineEigenbranchDiagonalProbe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branchX branchY : ℂ → ℂ) (D : ι → ℂ)
    (x y : ι) (g : ℂ) : ℂ :=
  ∑ i,
    affineEigenbranchAdjugateColumn energy V branchX x g i *
      D i *
      affineEigenbranchAdjugateColumn energy V branchY y g i

/-- **Exact diagonal-probe transition derivative.** For distinct simple
levels `x,y`, multiplying the first derivative of the bilinear probe
transition by their spectral gap removes every denominator.  The result is
the difference of the two directed interaction channels, weighted by the
probe values and the nonzero adjugate normalizations. -/
theorem affineEigenbranchDiagonalProbe_deriv_gap_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (V : Matrix ι ι ℂ)
    (x y : ι) (hxy : x ≠ y)
    (branchX branchY : ℂ → ℂ)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0)
    (hbaseX : branchX 0 = energy x)
    (hbaseY : branchY 0 = energy y)
    (hrootX :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy + g • V, branchX g) = 0)
    (hrootY :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy + g • V, branchY g) = 0)
    (D : ι → ℂ) :
    (energy x - energy y) *
        deriv
          (affineEigenbranchDiagonalProbe
            energy V branchX branchY D x y) 0 =
      (∏ j ∈ Finset.univ.erase x, (energy x - energy j)) *
        (∏ j ∈ Finset.univ.erase y, (energy y - energy j)) *
        (D y * V y x - D x * V x y) := by
  let wx : ℂ → ι → ℂ :=
    fun g => affineEigenbranchAdjugateColumn
      energy V branchX x g
  let wy : ℂ → ι → ℂ :=
    fun g => affineEigenbranchAdjugateColumn
      energy V branchY y g
  let Px : ℂ :=
    ∏ j ∈ Finset.univ.erase x, (energy x - energy j)
  let Py : ℂ :=
    ∏ j ∈ Finset.univ.erase y, (energy y - energy j)
  let term : ι → ℂ :=
    fun i =>
      deriv (fun g => wx g i) 0 * D i * wy 0 i +
        wx 0 i * D i * deriv (fun g => wy g i) 0
  have hwxan :
      ∀ i, AnalyticAt ℂ (fun g => wx g i) 0 :=
    analyticAt_affineEigenbranchAdjugateColumn
      energy V branchX x hbranchX
  have hwyan :
      ∀ i, AnalyticAt ℂ (fun g => wy g i) 0 :=
    analyticAt_affineEigenbranchAdjugateColumn
      energy V branchY y hbranchY
  have hprobe :
      deriv
          (affineEigenbranchDiagonalProbe
            energy V branchX branchY D x y) 0 =
        ∑ i, term i := by
    have hderiv :
        HasDerivAt
          (affineEigenbranchDiagonalProbe
            energy V branchX branchY D x y)
          (∑ i, term i) 0 := by
      unfold affineEigenbranchDiagonalProbe
      apply HasDerivAt.fun_sum
      intro i hi
      change HasDerivAt
        (fun g => wx g i * D i * wy g i)
        (deriv (fun g => wx g i) 0 * D i * wy 0 i +
          wx 0 i * D i * deriv (fun g => wy g i) 0) 0
      convert!
        (((hwxan i).differentiableAt.hasDerivAt.mul_const (D i)).mul
          (hwyan i).differentiableAt.hasDerivAt) using 1
    exact hderiv.deriv
  have hwx0 :
      ∀ i, wx 0 i = if i = x then Px else 0 := by
    intro i
    simpa [wx, Px] using
      affineEigenbranchAdjugateColumn_zero
        energy V branchX x i hbaseX
  have hwy0 :
      ∀ i, wy 0 i = if i = y then Py else 0 := by
    intro i
    simpa [wy, Py] using
      affineEigenbranchAdjugateColumn_zero
        energy V branchY y i hbaseY
  have hterm_other :
      ∀ i, i ≠ x → i ≠ y → term i = 0 := by
    intro i hix hiy
    simp [term, hwx0 i, hwy0 i, hix, hiy]
  have hyErase : y ∈ (Finset.univ.erase x : Finset ι) := by
    simp [hxy.symm]
  have hsum :
      (∑ i, term i) = term x + term y := by
    rw [← Finset.sum_erase_add _ term (Finset.mem_univ x)]
    rw [Finset.sum_eq_single y]
    · ring
    · intro i hi hiy
      exact hterm_other i (Finset.mem_erase.mp hi).1 hiy
    · exact fun hy => absurd hyErase hy
  have htermX :
      term x =
        Px * D x * deriv (fun g => wy g x) 0 := by
    simp [term, hwx0 x, hwy0 x, hxy, Px]
  have htermY :
      term y =
        deriv (fun g => wx g y) 0 * D y * Py := by
    simp [term, hwx0 y, hwy0 y, hxy.symm, Py]
  have hxderiv :
      (energy x - energy y) *
          deriv (fun g => wx g y) 0 =
        V y x * Px := by
    simpa [wx, Px] using
      affineEigenbranchAdjugateColumn_deriv_gap_mul_general
        energy hinj V x y hxy.symm
        branchX hbranchX hbaseX hrootX
  have hyderiv :
      (energy y - energy x) *
          deriv (fun g => wy g x) 0 =
        V x y * Py := by
    simpa [wy, Py] using
      affineEigenbranchAdjugateColumn_deriv_gap_mul_general
        energy hinj V y x hxy
        branchY hbranchY hbaseY hrootY
  rw [hprobe, hsum, htermX, htermY]
  linear_combination
    -Px * D x * hyderiv + D y * Py * hxderiv

end

end GaloisForLFunctions.HTGeometry
