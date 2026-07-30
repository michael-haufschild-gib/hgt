import GaloisForLFunctions.HTGeometry.AffineEigenbranchGeneralSecondOrderLaw
import GaloisForLFunctions.HTGeometry.LocalExtensionMatrixChart
import GaloisForLFunctions.HTGeometry.HermitianLocalExtensionChart

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

/-- The canonical diagonal-probe transition amplitude is analytic wherever
both labeled eigenvalue branches are analytic. -/
theorem analyticAt_affineEigenbranchDiagonalProbe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branchX branchY : ℂ → ℂ) (D : ι → ℂ)
    (x y : ι)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0) :
    AnalyticAt ℂ
      (affineEigenbranchDiagonalProbe
        energy V branchX branchY D x y) 0 := by
  apply Finset.analyticAt_fun_sum
  intro i hi
  exact
    ((analyticAt_affineEigenbranchAdjugateColumn
      energy V branchX x hbranchX i).mul analyticAt_const).mul
      (analyticAt_affineEigenbranchAdjugateColumn
        energy V branchY y hbranchY i)

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

/-- A one-sided diagonal probe necessarily detects a newly mixed transition:
if it vanishes on `x`, is nonzero on `y`, and the directed interaction
channel from `x` to `y` is nonzero, then the transition amplitude has
nonzero first derivative at zero coupling. -/
theorem affineEigenbranchDiagonalProbe_deriv_ne_zero_of_left_zero
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
    (D : ι → ℂ) (hDx : D x = 0) (hDy : D y ≠ 0)
    (hVyx : V y x ≠ 0) :
    deriv
      (affineEigenbranchDiagonalProbe
        energy V branchX branchY D x y) 0 ≠ 0 := by
  intro hzero
  have hformula :=
    affineEigenbranchDiagonalProbe_deriv_gap_mul
      energy hinj V x y hxy branchX branchY
      hbranchX hbranchY hbaseX hbaseY hrootX hrootY D
  rw [hzero, mul_zero, hDx, zero_mul, sub_zero] at hformula
  have hPx :
      (∏ j ∈ Finset.univ.erase x,
        (energy x - energy j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hj).1 (hinj heq.symm)
  have hPy :
      (∏ j ∈ Finset.univ.erase y,
        (energy y - energy j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hj).1 (hinj heq.symm)
  exact
    (mul_ne_zero (mul_ne_zero hPx hPy)
      (mul_ne_zero hDy hVyx)) hformula.symm

/-- Bilinear transition amplitude of an arbitrary matrix probe between two
canonical adjugate-column eigenvector germs. -/
def affineEigenbranchMatrixProbe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branchX branchY : ℂ → ℂ) (O : Matrix ι ι ℂ)
    (x y : ι) (g : ℂ) : ℂ :=
  ∑ i, ∑ j,
    affineEigenbranchAdjugateColumn energy V branchX x g i *
      O i j *
      affineEigenbranchAdjugateColumn energy V branchY y g j

/-- Physical sesquilinear bra--ket amplitude of an arbitrary matrix probe
between two canonical adjugate-column eigenvector germs. -/
def affineEigenbranchSesquilinearMatrixProbe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branchX branchY : ℂ → ℂ) (O : Matrix ι ι ℂ)
    (x y : ι) (g : ℂ) : ℂ :=
  ∑ i, ∑ j,
    star
        (affineEigenbranchAdjugateColumn
          energy V branchX x g i) *
      O i j *
      affineEigenbranchAdjugateColumn energy V branchY y g j

/-- On a real adjugate-column slice, the algebraic bilinear response is
exactly the physical sesquilinear bra--ket response. -/
theorem affineEigenbranchSesquilinearMatrixProbe_eq_bilinear_of_left_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branchX branchY : ℂ → ℂ) (O : Matrix ι ι ℂ)
    (x y : ι) (g : ℂ)
    (hreal :
      ∀ i,
        star
            (affineEigenbranchAdjugateColumn
              energy V branchX x g i) =
          affineEigenbranchAdjugateColumn
            energy V branchX x g i) :
    affineEigenbranchSesquilinearMatrixProbe
        energy V branchX branchY O x y g =
      affineEigenbranchMatrixProbe
        energy V branchX branchY O x y g := by
  unfold affineEigenbranchSesquilinearMatrixProbe
    affineEigenbranchMatrixProbe
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hreal i]

/-- Arbitrary probe transitions are analytic along analytic labeled
eigenbranches. -/
theorem analyticAt_affineEigenbranchMatrixProbe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branchX branchY : ℂ → ℂ) (O : Matrix ι ι ℂ)
    (x y : ι)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0) :
    AnalyticAt ℂ
      (affineEigenbranchMatrixProbe
        energy V branchX branchY O x y) 0 := by
  apply Finset.analyticAt_fun_sum
  intro i hi
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact
    ((analyticAt_affineEigenbranchAdjugateColumn
      energy V branchX x hbranchX i).mul analyticAt_const).mul
      (analyticAt_affineEigenbranchAdjugateColumn
        energy V branchY y hbranchY j)

/-- **Exact arbitrary-probe first derivative.** At the uncoupled point only
the `y` coordinate of the second eigenvector germ and the `x` coordinate of
the first survive.  Hence the full transition derivative reduces exactly
to one row and one column of the probe. -/
theorem affineEigenbranchMatrixProbe_deriv_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (x y : ι)
    (branchX branchY : ℂ → ℂ)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0)
    (hbaseX : branchX 0 = energy x)
    (hbaseY : branchY 0 = energy y)
    (O : Matrix ι ι ℂ) :
    deriv
        (affineEigenbranchMatrixProbe
          energy V branchX branchY O x y) 0 =
      (∏ k ∈ Finset.univ.erase y, (energy y - energy k)) *
          ∑ i,
            deriv
                (fun g =>
                  affineEigenbranchAdjugateColumn
                    energy V branchX x g i) 0 *
              O i y +
        (∏ k ∈ Finset.univ.erase x, (energy x - energy k)) *
          ∑ j,
            O x j *
              deriv
                (fun g =>
                  affineEigenbranchAdjugateColumn
                    energy V branchY y g j) 0 := by
  let wx : ℂ → ι → ℂ :=
    fun g => affineEigenbranchAdjugateColumn
      energy V branchX x g
  let wy : ℂ → ι → ℂ :=
    fun g => affineEigenbranchAdjugateColumn
      energy V branchY y g
  let Px : ℂ :=
    ∏ k ∈ Finset.univ.erase x, (energy x - energy k)
  let Py : ℂ :=
    ∏ k ∈ Finset.univ.erase y, (energy y - energy k)
  let term : ι → ι → ℂ :=
    fun i j =>
      deriv (fun g => wx g i) 0 * O i j * wy 0 j +
        wx 0 i * O i j * deriv (fun g => wy g j) 0
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
          (affineEigenbranchMatrixProbe
            energy V branchX branchY O x y) 0 =
        ∑ i, ∑ j, term i j := by
    have hderiv :
        HasDerivAt
          (affineEigenbranchMatrixProbe
            energy V branchX branchY O x y)
          (∑ i, ∑ j, term i j) 0 := by
      unfold affineEigenbranchMatrixProbe
      apply HasDerivAt.fun_sum
      intro i hi
      apply HasDerivAt.fun_sum
      intro j hj
      change HasDerivAt
        (fun g => wx g i * O i j * wy g j)
        (deriv (fun g => wx g i) 0 * O i j * wy 0 j +
          wx 0 i * O i j * deriv (fun g => wy g j) 0) 0
      convert!
        (((hwxan i).differentiableAt.hasDerivAt.mul_const (O i j)).mul
          (hwyan j).differentiableAt.hasDerivAt) using 1
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
  have hfirst :
      (∑ i, ∑ j,
        deriv (fun g => wx g i) 0 * O i j * wy 0 j) =
        Py * ∑ i, deriv (fun g => wx g i) 0 * O i y := by
    calc
      (∑ i, ∑ j,
        deriv (fun g => wx g i) 0 * O i j * wy 0 j) =
          ∑ i,
            deriv (fun g => wx g i) 0 * O i y * Py := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_eq_single y]
              · rw [hwy0 y]
                simp [Py]
              · intro j hj hjy
                simp [hwy0 j, hjy]
              · exact fun hy => absurd (Finset.mem_univ y) hy
      _ = Py * ∑ i,
            deriv (fun g => wx g i) 0 * O i y := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
  have hsecond :
      (∑ i, ∑ j,
        wx 0 i * O i j * deriv (fun g => wy g j) 0) =
        Px * ∑ j, O x j * deriv (fun g => wy g j) 0 := by
    rw [Finset.sum_eq_single x]
    · rw [hwx0 x]
      simp only [if_pos]
      change
        (∑ j, Px * O x j * deriv (fun g => wy g j) 0) =
          Px * ∑ j, O x j * deriv (fun g => wy g j) 0
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · intro i hi hix
      simp [hwx0 i, hix]
    · exact fun hx => absurd (Finset.mem_univ x) hx
  have hsplit :
      (∑ i, ∑ j, term i j) =
        (∑ i, ∑ j,
          deriv (fun g => wx g i) 0 * O i j * wy 0 j) +
        (∑ i, ∑ j,
          wx 0 i * O i j * deriv (fun g => wy g j) 0) := by
    simp only [term, Finset.sum_add_distrib]
  rw [hprobe, hsplit, hfirst, hsecond]

/-- A directed probe creates a nonzero transition without any cancellation.
If the probe row at `x` vanishes, its column at `y` is supported only at
`u`, and both the probe entry `O u y` and interaction channel `V u x` are
nonzero, then the transition derivative is nonzero.  This is the
phase-independent mechanism needed for same-layer endpoint propagation. -/
theorem affineEigenbranchMatrixProbe_deriv_ne_zero_of_one_sided
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (V : Matrix ι ι ℂ)
    (x y u : ι) (hux : u ≠ x)
    (branchX branchY : ℂ → ℂ)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0)
    (hbaseX : branchX 0 = energy x)
    (hbaseY : branchY 0 = energy y)
    (hrootX :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy + g • V, branchX g) = 0)
    (O : Matrix ι ι ℂ)
    (hrow : ∀ j, O x j = 0)
    (hcolumn : ∀ i, i ≠ u → O i y = 0)
    (hOuy : O u y ≠ 0)
    (hVux : V u x ≠ 0) :
    deriv
      (affineEigenbranchMatrixProbe
        energy V branchX branchY O x y) 0 ≠ 0 := by
  let Px : ℂ :=
    ∏ k ∈ Finset.univ.erase x, (energy x - energy k)
  let Py : ℂ :=
    ∏ k ∈ Finset.univ.erase y, (energy y - energy k)
  let dx : ι → ℂ :=
    fun i =>
      deriv
        (fun g =>
          affineEigenbranchAdjugateColumn
            energy V branchX x g i) 0
  let dy : ι → ℂ :=
    fun j =>
      deriv
        (fun g =>
          affineEigenbranchAdjugateColumn
            energy V branchY y g j) 0
  have hformula :=
    affineEigenbranchMatrixProbe_deriv_eq
      energy V x y branchX branchY hbranchX hbranchY
      hbaseX hbaseY O
  have hcolsum :
      (∑ i, dx i * O i y) = dx u * O u y := by
    rw [Finset.sum_eq_single u]
    · intro i hi hiu
      rw [hcolumn i hiu, mul_zero]
    · exact fun hu => absurd (Finset.mem_univ u) hu
  have hrowsum :
      (∑ j, O x j * dy j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hrow j, zero_mul]
  have hPx :
      Px ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hk).1 (hinj heq.symm)
  have hPy :
      Py ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hk).1 (hinj heq.symm)
  have hgap :
      (energy x - energy u) * dx u =
        V u x * Px := by
    simpa [dx, Px] using
      affineEigenbranchAdjugateColumn_deriv_gap_mul_general
        energy hinj V x u hux branchX
        hbranchX hbaseX hrootX
  intro hzero
  change
    deriv
      (affineEigenbranchMatrixProbe
        energy V branchX branchY O x y) 0 = 0 at hzero
  change
    deriv
      (affineEigenbranchMatrixProbe
        energy V branchX branchY O x y) 0 =
      Py * (∑ i, dx i * O i y) +
        Px * (∑ j, O x j * dy j) at hformula
  rw [hzero, hcolsum, hrowsum, mul_zero, add_zero] at hformula
  have hdx : dx u = 0 := by
    exact
      (mul_eq_zero.mp hformula.symm).resolve_left hPy
      |> fun h =>
        (mul_eq_zero.mp h).resolve_right hOuy
  rw [hdx, mul_zero] at hgap
  exact (mul_ne_zero hVux hPx) hgap.symm

/-- Matrix unit on a local factor, directed from `source` to `target`. -/
def directedLayerMatrix
    {ρ : Type*} [DecidableEq ρ] (target source : ρ) :
    Matrix ρ ρ ℂ :=
  fun r s => if r = target ∧ s = source then 1 else 0

/-- **Phase-independent same-layer transition creation.** Let a tensor-local
interaction contain a nonzero old-system channel `b ← a` and a nonzero
new-factor channel `s ← r`.  The directed local probe `s ← r` then acquires
a nonzero transition between the two same-layer branches `(a,r)` and
`(b,r)` at first order.  No reality, symmetry, or phase convention is
required. -/
theorem localDirectedProbe_sameLayer_deriv_ne_zero
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α × ρ → ℂ) (hinj : Function.Injective energy)
    (transition : Matrix α α ℂ) (edge : Matrix ρ ρ ℂ)
    (a b : α) (r s : ρ) (hab : a ≠ b) (hrs : r ≠ s)
    (htransition : transition b a ≠ 0)
    (hedge : edge s r ≠ 0)
    (branchX branchY : ℂ → ℂ)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0)
    (hbaseX : branchX 0 = energy (a, r))
    (hbaseY : branchY 0 = energy (b, r))
    (hrootX :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy +
            g • layerMatrixCoupling transition edge,
            branchX g) = 0) :
    deriv
      (affineEigenbranchMatrixProbe
        energy (layerMatrixCoupling transition edge)
        branchX branchY
        (layerMatrixCoupling (1 : Matrix α α ℂ)
          (directedLayerMatrix s r))
        (a, r) (b, r)) 0 ≠ 0 := by
  apply
    affineEigenbranchMatrixProbe_deriv_ne_zero_of_one_sided
      energy hinj (layerMatrixCoupling transition edge)
      (a, r) (b, r) (b, s)
  · intro h
    exact hab (congrArg Prod.fst h).symm
  · exact hbranchX
  · exact hbranchY
  · exact hbaseX
  · exact hbaseY
  · exact hrootX
  · intro j
    simp [layerMatrixCoupling, directedLayerMatrix, hrs]
  · intro i hi
    by_cases hiold : i.1 = b
    · by_cases hilayer : i.2 = s
      · exfalso
        apply hi
        exact Prod.ext hiold hilayer
      · simp [layerMatrixCoupling, directedLayerMatrix,
          hilayer]
    · simp [layerMatrixCoupling, directedLayerMatrix, hiold]
  · simp [layerMatrixCoupling, directedLayerMatrix]
  · exact mul_ne_zero htransition hedge

/-- Hermitian cosine quadrature of one directed local matrix unit. -/
def hermitianLayerCosineProbe
    {ρ : Type*} [DecidableEq ρ] (target source : ρ) :
    Matrix ρ ρ ℂ :=
  directedLayerMatrix target source +
    directedLayerMatrix source target

/-- Hermitian sine quadrature of one directed local matrix unit. -/
def hermitianLayerSineProbe
    {ρ : Type*} [DecidableEq ρ] (target source : ρ) :
    Matrix ρ ρ ℂ :=
  Complex.I • directedLayerMatrix target source +
    (-Complex.I) • directedLayerMatrix source target

theorem directedLayerMatrix_conjTranspose
    {ρ : Type*} [DecidableEq ρ] (target source : ρ) :
    Matrix.conjTranspose (directedLayerMatrix target source) =
      directedLayerMatrix source target := by
  ext r s
  simp [Matrix.conjTranspose_apply, directedLayerMatrix, and_comm]

theorem hermitianLayerCosineProbe_isHermitian
    {ρ : Type*} [DecidableEq ρ] (target source : ρ) :
    (hermitianLayerCosineProbe target source).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [hermitianLayerCosineProbe,
    directedLayerMatrix_conjTranspose, add_comm]

theorem hermitianLayerSineProbe_isHermitian
    {ρ : Type*} [DecidableEq ρ] (target source : ρ) :
    (hermitianLayerSineProbe target source).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [hermitianLayerSineProbe,
    directedLayerMatrix_conjTranspose, add_comm]

/-- Every off-diagonal directed matrix unit is the complex polarization of
two explicit Hermitian quadrature probes. -/
theorem directedLayerMatrix_eq_hermitian_quadratures
    {ρ : Type*} [DecidableEq ρ] (target source : ρ)
    (hts : target ≠ source) :
    directedLayerMatrix target source =
      (2 : ℂ)⁻¹ • hermitianLayerCosineProbe target source +
        (-(2 : ℂ)⁻¹ * Complex.I) •
          hermitianLayerSineProbe target source := by
  ext r s
  simp [hermitianLayerCosineProbe, hermitianLayerSineProbe,
    directedLayerMatrix]
  by_cases h : r = target ∧ s = source
  · rcases h with ⟨rfl, rfl⟩
    simp [hts]
    ring_nf
    norm_num
  · by_cases h' : r = source ∧ s = target
    · rcases h' with ⟨rfl, rfl⟩
      simp [hts]
      ring_nf
      norm_num
    · simp [h, h']

/-- Matrix-probe eigenbranch responses respect the Hermitian quadrature
decomposition of a directed local probe. -/
theorem affineEigenbranchMatrixProbe_directed_eq_quadratures
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branchX branchY : ℂ → ℂ)
    (target source : ρ) (hts : target ≠ source)
    (lift : Matrix ρ ρ ℂ → Matrix ι ι ℂ)
    (hlift_add :
      ∀ A B, lift (A + B) = lift A + lift B)
    (hlift_smul :
      ∀ (c : ℂ) A, lift (c • A) = c • lift A)
    (x y : ι) :
    affineEigenbranchMatrixProbe
        energy V branchX branchY
        (lift (directedLayerMatrix target source)) x y =
      fun g =>
        (2 : ℂ)⁻¹ *
            affineEigenbranchMatrixProbe
              energy V branchX branchY
              (lift (hermitianLayerCosineProbe target source)) x y g +
          (-(2 : ℂ)⁻¹ * Complex.I) *
            affineEigenbranchMatrixProbe
              energy V branchX branchY
              (lift (hermitianLayerSineProbe target source)) x y g := by
  funext g
  rw [directedLayerMatrix_eq_hermitian_quadratures target source hts,
    hlift_add, hlift_smul, hlift_smul]
  unfold affineEigenbranchMatrixProbe
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- **Hermitian polarization of a nonzero directed response.** If one
directed local matrix unit has nonzero first response between two canonical
eigenbranch germs, then at least one of its explicit Hermitian cosine/sine
quadratures has nonzero first response. -/
theorem exists_hermitianLocalQuadratureProbe_deriv_ne_zero
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α × ρ → ℂ) (V : Matrix (α × ρ) (α × ρ) ℂ)
    (branchX branchY : ℂ → ℂ)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0)
    (x y : α × ρ) (target source : ρ)
    (hts : target ≠ source)
    (hdir :
      deriv
        (affineEigenbranchMatrixProbe
          energy V branchX branchY
          (layerMatrixCoupling (1 : Matrix α α ℂ)
            (directedLayerMatrix target source))
          x y) 0 ≠ 0) :
    ∃ O : Matrix (α × ρ) (α × ρ) ℂ,
      O.IsHermitian ∧
        deriv
          (affineEigenbranchMatrixProbe
            energy V branchX branchY O x y) 0 ≠ 0 := by
  let OX : Matrix (α × ρ) (α × ρ) ℂ :=
    layerMatrixCoupling (1 : Matrix α α ℂ)
      (hermitianLayerCosineProbe target source)
  let OY : Matrix (α × ρ) (α × ρ) ℂ :=
    layerMatrixCoupling (1 : Matrix α α ℂ)
      (hermitianLayerSineProbe target source)
  have hOX : OX.IsHermitian := by
    exact layerMatrixCoupling_isHermitian Matrix.isHermitian_one
      (hermitianLayerCosineProbe_isHermitian target source)
  have hOY : OY.IsHermitian := by
    exact layerMatrixCoupling_isHermitian Matrix.isHermitian_one
      (hermitianLayerSineProbe_isHermitian target source)
  have hlift_add :
      ∀ A B : Matrix ρ ρ ℂ,
        layerMatrixCoupling (1 : Matrix α α ℂ) (A + B) =
          layerMatrixCoupling (1 : Matrix α α ℂ) A +
            layerMatrixCoupling (1 : Matrix α α ℂ) B := by
    intro A B
    ext i j
    simp [layerMatrixCoupling, mul_add]
  have hlift_smul :
      ∀ (c : ℂ) (A : Matrix ρ ρ ℂ),
        layerMatrixCoupling (1 : Matrix α α ℂ) (c • A) =
          c • layerMatrixCoupling (1 : Matrix α α ℂ) A := by
    intro c A
    ext i j
    simp [layerMatrixCoupling]
    ring
  have hquadratures :=
    affineEigenbranchMatrixProbe_directed_eq_quadratures
      energy V branchX branchY target source hts
      (fun A => layerMatrixCoupling (1 : Matrix α α ℂ) A)
      hlift_add hlift_smul x y
  have hOXan :
      AnalyticAt ℂ
        (affineEigenbranchMatrixProbe
          energy V branchX branchY OX x y) 0 :=
    analyticAt_affineEigenbranchMatrixProbe
      energy V branchX branchY OX x y hbranchX hbranchY
  have hOYan :
      AnalyticAt ℂ
        (affineEigenbranchMatrixProbe
          energy V branchX branchY OY x y) 0 :=
    analyticAt_affineEigenbranchMatrixProbe
      energy V branchX branchY OY x y hbranchX hbranchY
  by_cases hx :
      deriv
        (affineEigenbranchMatrixProbe
          energy V branchX branchY OX x y) 0 ≠ 0
  · exact ⟨OX, hOX, hx⟩
  · refine ⟨OY, hOY, ?_⟩
    intro hy
    apply hdir
    rw [hquadratures]
    have hsum :
        HasDerivAt
          (fun g =>
            (2 : ℂ)⁻¹ *
                affineEigenbranchMatrixProbe
                  energy V branchX branchY OX x y g +
              (-(2 : ℂ)⁻¹ * Complex.I) *
                affineEigenbranchMatrixProbe
                  energy V branchX branchY OY x y g)
          ((2 : ℂ)⁻¹ *
              deriv
                (affineEigenbranchMatrixProbe
                  energy V branchX branchY OX x y) 0 +
            (-(2 : ℂ)⁻¹ * Complex.I) *
              deriv
                (affineEigenbranchMatrixProbe
                  energy V branchX branchY OY x y) 0) 0 := by
      exact
        (hOXan.differentiableAt.hasDerivAt.const_mul (2 : ℂ)⁻¹).add
          (hOYan.differentiableAt.hasDerivAt.const_mul
            (-(2 : ℂ)⁻¹ * Complex.I))
    rw [hsum.deriv, not_ne_iff.mp hx, hy]
    ring

/-- A nonzero tensor-local interaction channel always admits an explicit
Hermitian new-factor quadrature with nonzero same-layer first response. -/
theorem exists_hermitianLocalProbe_sameLayer_deriv_ne_zero
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α × ρ → ℂ) (hinj : Function.Injective energy)
    (transition : Matrix α α ℂ) (edge : Matrix ρ ρ ℂ)
    (a b : α) (r s : ρ) (hab : a ≠ b) (hrs : r ≠ s)
    (htransition : transition b a ≠ 0)
    (hedge : edge s r ≠ 0)
    (branchX branchY : ℂ → ℂ)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0)
    (hbaseX : branchX 0 = energy (a, r))
    (hbaseY : branchY 0 = energy (b, r))
    (hrootX :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy +
            g • layerMatrixCoupling transition edge,
            branchX g) = 0) :
    ∃ O : Matrix (α × ρ) (α × ρ) ℂ,
      O.IsHermitian ∧
        deriv
          (affineEigenbranchMatrixProbe
            energy (layerMatrixCoupling transition edge)
            branchX branchY O (a, r) (b, r)) 0 ≠ 0 := by
  apply
    exists_hermitianLocalQuadratureProbe_deriv_ne_zero
      energy (layerMatrixCoupling transition edge)
      branchX branchY hbranchX hbranchY
      (a, r) (b, r) s r hrs.symm
  exact
    localDirectedProbe_sameLayer_deriv_ne_zero
      energy hinj transition edge a b r s hab hrs
      htransition hedge branchX branchY hbranchX hbranchY
      hbaseX hbaseY hrootX

end

end GaloisForLFunctions.HTGeometry
