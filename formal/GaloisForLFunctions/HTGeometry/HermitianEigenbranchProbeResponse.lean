import GaloisForLFunctions.HTGeometry.AffineEigenbranchDiagonalProbeLaw

/-!
# Analytic Hermitian eigenbranch probe response

For a Hermitian affine matrix on the real parameter line, the conjugate of
an adjugate eigenvector column is the corresponding adjugate row.  Replacing
the conjugated column by that row gives a holomorphic row--column probe whose
restriction to the Hermitian line is exactly the physical sesquilinear
amplitude.  Its derivative uses the oriented matrix entry `V x i`, removing
the real-symmetry assumption from the two-step response mechanism.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One adjugate row of the affine characteristic matrix. -/
def affineEigenbranchAdjugateRow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ) (branch : ℂ → ℂ)
    (x : ι) (g : ℂ) : ι → ℂ :=
  fun i =>
    (affineBranchCharacteristicMatrix energy V branch g).adjugate x i

/-- Transposition of the interaction transposes the full affine
characteristic matrix. -/
theorem affineBranchCharacteristicMatrix_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branch : ℂ → ℂ) (g : ℂ) :
    (affineBranchCharacteristicMatrix energy V branch g).transpose =
      affineBranchCharacteristicMatrix energy V.transpose branch g := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [affineBranchCharacteristicMatrix, Matrix.scalar_apply]
  · simp [affineBranchCharacteristicMatrix, Matrix.scalar_apply,
      hij, Ne.symm hij]

/-- An adjugate row for `V` is an adjugate column for `Vᵀ`. -/
theorem affineEigenbranchAdjugateRow_eq_transposeColumn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branch : ℂ → ℂ) (x : ι) (g : ℂ) :
    affineEigenbranchAdjugateRow energy V branch x g =
      affineEigenbranchAdjugateColumn
        energy V.transpose branch x g := by
  funext i
  unfold affineEigenbranchAdjugateRow
    affineEigenbranchAdjugateColumn
  rw [← affineBranchCharacteristicMatrix_transpose]
  rw [← Matrix.adjugate_transpose]
  rfl

/-- Adjugate rows inherit holomorphic dependence from adjugate columns. -/
theorem analyticAt_affineEigenbranchAdjugateRow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branch : ℂ → ℂ) (x : ι)
    (hbranch : AnalyticAt ℂ branch 0) :
    ∀ i,
      AnalyticAt ℂ
        (fun g =>
          affineEigenbranchAdjugateRow
            energy V branch x g i) 0 := by
  intro i
  rw [show
      (fun g =>
        affineEigenbranchAdjugateRow
          energy V branch x g i) =
        fun g =>
          affineEigenbranchAdjugateColumn
            energy V.transpose branch x g i by
      funext g
      exact congrFun
        (affineEigenbranchAdjugateRow_eq_transposeColumn
          energy V branch x g) i]
  exact analyticAt_affineEigenbranchAdjugateColumn
    energy V.transpose branch x hbranch i

/-- The characteristic relation is invariant under transposing the affine
interaction. -/
theorem matrixCharpolyRelation_affine_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branch : ℂ → ℂ) (g : ℂ) :
    matrixCharpolyRelation
        (Matrix.diagonal energy + g • V.transpose, branch g) =
      matrixCharpolyRelation
        (Matrix.diagonal energy + g • V, branch g) := by
  unfold matrixCharpolyRelation
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, hij, Ne.symm hij]

/-- Off-label derivative of an adjugate row.  The orientation is `V x i`,
as required by a physical left eigenvector. -/
theorem affineEigenbranchAdjugateRow_deriv_eq_div_general
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (V : Matrix ι ι ℂ)
    (x i : ι) (hix : i ≠ x)
    (branch : ℂ → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hbase : branch 0 = energy x)
    (hroot :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy + g • V, branch g) = 0) :
    deriv
        (fun g =>
          affineEigenbranchAdjugateRow
            energy V branch x g i) 0 =
      (V x i *
          ∏ j ∈ Finset.univ.erase x,
            (energy x - energy j)) /
        (energy x - energy i) := by
  have hrootTranspose :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy + g • V.transpose, branch g) = 0 := by
    filter_upwards [hroot] with g hg
    rwa [matrixCharpolyRelation_affine_transpose]
  rw [show
      (fun g =>
        affineEigenbranchAdjugateRow
          energy V branch x g i) =
        fun g =>
          affineEigenbranchAdjugateColumn
            energy V.transpose branch x g i by
      funext g
      exact congrFun
        (affineEigenbranchAdjugateRow_eq_transposeColumn
          energy V branch x g) i]
  simpa using
    affineEigenbranchAdjugateColumn_deriv_eq_div_general
      energy hinj V.transpose x i hix branch
      hbranch hbase hrootTranspose

/-- Holomorphic row--column probe whose Hermitian-line restriction is the
physical bra--ket amplitude. -/
def affineEigenbranchRowColumnMatrixProbe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branchX branchY : ℂ → ℂ)
    (O : Matrix ι ι ℂ) (x y : ι) (g : ℂ) : ℂ :=
  ∑ i, ∑ j,
    affineEigenbranchAdjugateRow energy V branchX x g i *
      O i j *
      affineEigenbranchAdjugateColumn energy V branchY y g j

/-- Base value of the row--column probe at the uncoupled diagonal point. -/
theorem affineEigenbranchRowColumnMatrixProbe_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branchX branchY : ℂ → ℂ)
    (O : Matrix ι ι ℂ) (x y : ι)
    (hbaseX : branchX 0 = energy x)
    (hbaseY : branchY 0 = energy y) :
    affineEigenbranchRowColumnMatrixProbe
        energy V branchX branchY O x y 0 =
      (∏ k ∈ Finset.univ.erase x, (energy x - energy k)) *
        O x y *
        ∏ k ∈ Finset.univ.erase y, (energy y - energy k) := by
  unfold affineEigenbranchRowColumnMatrixProbe
  simp_rw [
    affineEigenbranchAdjugateRow_eq_transposeColumn,
    affineEigenbranchAdjugateColumn_zero
      energy V.transpose branchX x _ hbaseX,
    affineEigenbranchAdjugateColumn_zero
      energy V branchY y _ hbaseY]
  simp

/-- Row--column probes are holomorphic along analytic labeled branches. -/
theorem analyticAt_affineEigenbranchRowColumnMatrixProbe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branchX branchY : ℂ → ℂ)
    (O : Matrix ι ι ℂ) (x y : ι)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0) :
    AnalyticAt ℂ
      (affineEigenbranchRowColumnMatrixProbe
        energy V branchX branchY O x y) 0 := by
  apply Finset.analyticAt_fun_sum
  intro i hi
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact
    ((analyticAt_affineEigenbranchAdjugateRow
      energy V branchX x hbranchX i).mul analyticAt_const).mul
      (analyticAt_affineEigenbranchAdjugateColumn
        energy V branchY y hbranchY j)

/-- At a Hermitian characteristic matrix, the analytic row--column probe
equals the physical sesquilinear probe exactly. -/
theorem affineEigenbranchSesquilinearMatrixProbe_eq_rowColumn_of_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branchX branchY : ℂ → ℂ)
    (O : Matrix ι ι ℂ) (x y : ι) (g : ℂ)
    (hchar :
      (affineBranchCharacteristicMatrix
        energy V branchX g).IsHermitian) :
    affineEigenbranchSesquilinearMatrixProbe
        energy V branchX branchY O x y g =
      affineEigenbranchRowColumnMatrixProbe
        energy V branchX branchY O x y g := by
  unfold affineEigenbranchSesquilinearMatrixProbe
    affineEigenbranchRowColumnMatrixProbe
    affineEigenbranchAdjugateRow
    affineEigenbranchAdjugateColumn
  simp_rw [hchar.adjugate.apply x]

/-- Exact first derivative of the analytic row--column probe. -/
theorem affineEigenbranchRowColumnMatrixProbe_deriv_eq
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
        (affineEigenbranchRowColumnMatrixProbe
          energy V branchX branchY O x y) 0 =
      (∏ k ∈ Finset.univ.erase y, (energy y - energy k)) *
          ∑ i,
            deriv
                (fun g =>
                  affineEigenbranchAdjugateRow
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
    fun g => affineEigenbranchAdjugateRow
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
    analyticAt_affineEigenbranchAdjugateRow
      energy V branchX x hbranchX
  have hwyan :
      ∀ i, AnalyticAt ℂ (fun g => wy g i) 0 :=
    analyticAt_affineEigenbranchAdjugateColumn
      energy V branchY y hbranchY
  have hprobe :
      deriv
          (affineEigenbranchRowColumnMatrixProbe
            energy V branchX branchY O x y) 0 =
        ∑ i, ∑ j, term i j := by
    have hderiv :
        HasDerivAt
          (affineEigenbranchRowColumnMatrixProbe
            energy V branchX branchY O x y)
          (∑ i, ∑ j, term i j) 0 := by
      unfold affineEigenbranchRowColumnMatrixProbe
      apply HasDerivAt.fun_sum
      intro i hi
      apply HasDerivAt.fun_sum
      intro j hj
      change HasDerivAt
        (fun g => wx g i * O i j * wy g j)
        (deriv (fun g => wx g i) 0 * O i j * wy 0 j +
          wx 0 i * O i j * deriv (fun g => wy g j) 0) 0
      convert!
        (((hwxan i).differentiableAt.hasDerivAt.mul_const
          (O i j)).mul
          (hwyan j).differentiableAt.hasDerivAt) using 1
    exact hderiv.deriv
  have hwx0 :
      ∀ i, wx 0 i = if i = x then Px else 0 := by
    intro i
    rw [show wx 0 i =
        affineEigenbranchAdjugateColumn
          energy V.transpose branchX x 0 i by
      exact congrFun
        (affineEigenbranchAdjugateRow_eq_transposeColumn
          energy V branchX x 0) i]
    simpa [Px] using
      affineEigenbranchAdjugateColumn_zero
        energy V.transpose branchX x i hbaseX
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

/-- Exact partial-fraction response of the Hermitian row--column probe. -/
theorem affineEigenbranchRowColumnMatrixProbe_deriv_eq_gapPackets
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (V : Matrix ι ι ℂ)
    (x y : ι)
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
    (O : Matrix ι ι ℂ) (hOxy : O x y = 0) :
    deriv
        (affineEigenbranchRowColumnMatrixProbe
          energy V branchX branchY O x y) 0 =
      ((∏ k ∈ Finset.univ.erase x, (energy x - energy k)) *
        (∏ k ∈ Finset.univ.erase y, (energy y - energy k))) *
        ((∑ i,
            V x i * O i y / (energy x - energy i)) +
          ∑ j,
            O x j * V j y / (energy y - energy j)) := by
  let Px : ℂ :=
    ∏ k ∈ Finset.univ.erase x, (energy x - energy k)
  let Py : ℂ :=
    ∏ k ∈ Finset.univ.erase y, (energy y - energy k)
  let dx : ι → ℂ :=
    fun i =>
      deriv
        (fun g =>
          affineEigenbranchAdjugateRow
            energy V branchX x g i) 0
  let dy : ι → ℂ :=
    fun j =>
      deriv
        (fun g =>
          affineEigenbranchAdjugateColumn
            energy V branchY y g j) 0
  have hformula :=
    affineEigenbranchRowColumnMatrixProbe_deriv_eq
      energy V x y branchX branchY hbranchX hbranchY
      hbaseX hbaseY O
  have hfirst :
      (∑ i, dx i * O i y) =
        Px * ∑ i, V x i * O i y / (energy x - energy i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hix : i = x
    · subst i
      simp [hOxy]
    · have hdx :
          dx i =
            (V x i * Px) / (energy x - energy i) := by
        simpa [dx, Px] using
          affineEigenbranchAdjugateRow_deriv_eq_div_general
            energy hinj V x i hix branchX
            hbranchX hbaseX hrootX
      rw [hdx]
      ring
  have hsecond :
      (∑ j, O x j * dy j) =
        Py * ∑ j, O x j * V j y / (energy y - energy j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjy : j = y
    · subst j
      simp [hOxy]
    · have hdy :
          dy j =
            (V j y * Py) / (energy y - energy j) := by
        simpa [dy, Py] using
          affineEigenbranchAdjugateColumn_deriv_eq_div_general
            energy hinj V y j hjy branchY
            hbranchY hbaseY hrootY
      rw [hdy]
      ring
  change
    deriv
        (affineEigenbranchRowColumnMatrixProbe
          energy V branchX branchY O x y) 0 =
      Py * (∑ i, dx i * O i y) +
        Px * (∑ j, O x j * dy j) at hformula
  change
    deriv
        (affineEigenbranchRowColumnMatrixProbe
          energy V branchX branchY O x y) 0 =
      (Px * Py) *
        ((∑ i, V x i * O i y / (energy x - energy i)) +
          ∑ j, O x j * V j y / (energy y - energy j))
  rw [hformula, hfirst, hsecond]
  ring

/-- A one-sided probe row and one nonzero oriented interaction entry force
a nonzero row--column response derivative. -/
theorem affineEigenbranchRowColumnMatrixProbe_deriv_ne_zero_of_one_sided
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
    (hVxu : V x u ≠ 0) :
    deriv
      (affineEigenbranchRowColumnMatrixProbe
        energy V branchX branchY O x y) 0 ≠ 0 := by
  let Px : ℂ :=
    ∏ k ∈ Finset.univ.erase x, (energy x - energy k)
  let Py : ℂ :=
    ∏ k ∈ Finset.univ.erase y, (energy y - energy k)
  let dx : ι → ℂ :=
    fun i =>
      deriv
        (fun g =>
          affineEigenbranchAdjugateRow
            energy V branchX x g i) 0
  let dy : ι → ℂ :=
    fun j =>
      deriv
        (fun g =>
          affineEigenbranchAdjugateColumn
            energy V branchY y g j) 0
  have hformula :=
    affineEigenbranchRowColumnMatrixProbe_deriv_eq
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
        V x u * Px := by
    have hquot :=
      affineEigenbranchAdjugateRow_deriv_eq_div_general
        energy hinj V x u hux branchX
        hbranchX hbaseX hrootX
    have hgapNe : energy x - energy u ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      exact hux (hinj heq).symm
    change
      dx u = (V x u * Px) / (energy x - energy u) at hquot
    rw [hquot]
    field_simp
  intro hzero
  change
    deriv
      (affineEigenbranchRowColumnMatrixProbe
        energy V branchX branchY O x y) 0 = 0 at hzero
  change
    deriv
      (affineEigenbranchRowColumnMatrixProbe
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
  exact (mul_ne_zero hVxu hPx) hgap.symm

/-- Row--column responses respect the Hermitian cosine/sine decomposition
of a directed local matrix unit. -/
theorem affineEigenbranchRowColumnMatrixProbe_directed_eq_quadratures
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
    affineEigenbranchRowColumnMatrixProbe
        energy V branchX branchY
        (lift (directedLayerMatrix target source)) x y =
      fun g =>
        (2 : ℂ)⁻¹ *
            affineEigenbranchRowColumnMatrixProbe
              energy V branchX branchY
              (lift (hermitianLayerCosineProbe target source)) x y g +
          (-(2 : ℂ)⁻¹ * Complex.I) *
            affineEigenbranchRowColumnMatrixProbe
              energy V branchX branchY
              (lift (hermitianLayerSineProbe target source)) x y g := by
  funext g
  rw [directedLayerMatrix_eq_hermitian_quadratures
    target source hts, hlift_add, hlift_smul, hlift_smul]
  unfold affineEigenbranchRowColumnMatrixProbe
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

end

end GaloisForLFunctions.HTGeometry
