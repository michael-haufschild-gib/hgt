import GaloisForLFunctions.HTGeometry.ComplexDeterminantSecondJet

/-!
# Second-order motion of a simple affine eigenbranch

The proof constructs a canonical analytic eigenvector germ from one column of
the adjugate characteristic matrix.  Differentiating the exact eigenvector
equation gives the second-order spectral response without importing
perturbation theory as an assumption.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One adjugate column of the characteristic matrix, used as an analytic
eigenvector germ. -/
def affineEigenbranchAdjugateColumn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ) (branch : ℂ → ℂ)
    (x : ι) (g : ℂ) : ι → ℂ :=
  fun i =>
    (affineBranchCharacteristicMatrix energy V branch g).adjugate i x

/-- Adjugation preserves entrywise analyticity for finite matrix families. -/
theorem analyticAt_matrix_adjugate_apply_parametric
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ℂ → Matrix ι ι ℂ} {g₀ : ℂ}
    (hM : ∀ i j, AnalyticAt ℂ (fun g => M g i j) g₀)
    (i j : ι) :
    AnalyticAt ℂ (fun g => (M g).adjugate i j) g₀ := by
  have heq :
      (fun g => (M g).adjugate i j) =
        fun g => ((M g).updateRow j (Pi.single i 1)).det := by
    funext g
    exact Matrix.adjugate_apply (M g) i j
  rw [heq]
  apply analyticAt_matrix_det_parametric
  intro r c
  by_cases hr : r = j
  · subst r
    simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simp [Matrix.updateRow, hr]
    exact hM r c

/-- The adjugate eigenvector germ is analytic in every coordinate. -/
theorem analyticAt_affineEigenbranchAdjugateColumn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ) (branch : ℂ → ℂ)
    (x : ι) (hbranch : AnalyticAt ℂ branch 0) :
    ∀ i,
      AnalyticAt ℂ
        (fun g =>
          affineEigenbranchAdjugateColumn energy V branch x g i) 0 := by
  have hA :
      ∀ i j,
        AnalyticAt ℂ
          (fun g =>
            affineBranchCharacteristicMatrix energy V branch g i j) 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa only [affineBranchCharacteristicMatrix_apply_same] using!
        (hbranch.sub analyticAt_const).sub
          (analyticAt_id.mul analyticAt_const)
    · simpa only [
        affineBranchCharacteristicMatrix_apply_ne _ _ _ _ hij] using!
        (analyticAt_id.mul analyticAt_const).neg
  intro i
  exact analyticAt_matrix_adjugate_apply_parametric hA i x

/-- Entrywise reality of the affine characteristic data forces the canonical
adjugate-column eigenvector coordinate to be real at the same parameter.
This supplies the exact bridge on a real-symmetric Hamiltonian slice between
the bilinear adjugate response and the physical sesquilinear bra--ket
response. -/
theorem star_affineEigenbranchAdjugateColumn_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branch : ℂ → ℂ) (x i : ι) (g : ℂ)
    (henergy : ∀ k, (starRingEnd ℂ) (energy k) = energy k)
    (hV : ∀ k l, (starRingEnd ℂ) (V k l) = V k l)
    (hbranch : (starRingEnd ℂ) (branch g) = branch g)
    (hg : (starRingEnd ℂ) g = g) :
    star (affineEigenbranchAdjugateColumn
      energy V branch x g i) =
      affineEigenbranchAdjugateColumn energy V branch x g i := by
  let M := affineBranchCharacteristicMatrix energy V branch g
  have hM : (starRingEnd ℂ).mapMatrix M = M := by
    ext k l
    rw [RingHom.mapMatrix_apply]
    by_cases hkl : k = l
    · subst l
      simp [M, henergy, hV, hbranch, hg]
    · simp [M, affineBranchCharacteristicMatrix_apply_ne _ _ _ _ hkl,
        hV, hg]
  have hadj := (starRingEnd ℂ).map_adjugate M
  have hentry := congrArg (fun N : Matrix ι ι ℂ => N i x) hadj
  rw [hM] at hentry
  simpa [M, affineEigenbranchAdjugateColumn,
    RingHom.mapMatrix_apply] using hentry

/-- At the uncoupled point the adjugate column is supported only at its
labelled simple level. -/
theorem affineEigenbranchAdjugateColumn_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ) (branch : ℂ → ℂ)
    (x i : ι) (hbase : branch 0 = energy x) :
    affineEigenbranchAdjugateColumn energy V branch x 0 i =
      if i = x then
        ∏ j ∈ Finset.univ.erase x, (energy x - energy j)
      else 0 := by
  have hA0 :
      affineBranchCharacteristicMatrix energy V branch 0 =
        Matrix.diagonal (fun j => energy x - energy j) := by
    ext r c
    by_cases hrc : r = c
    · subst c
      simp [hbase]
    · simp [affineBranchCharacteristicMatrix_apply_ne _ _ _ _ hrc,
        Matrix.diagonal_apply_ne _ hrc]
  rw [affineEigenbranchAdjugateColumn, hA0,
    Matrix.adjugate_diagonal, Matrix.diagonal_apply]
  split_ifs with hix
  · subst i
    rfl
  · rfl

/-- Along an actual characteristic-root branch, the adjugate column satisfies
the exact eigenvector equation in scalar coordinates. -/
theorem affineEigenbranchAdjugateColumn_relation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ) (branch : ℂ → ℂ)
    (x : ι)
    (hroot :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy + g • V, branch g) = 0) :
    ∀ᶠ g in 𝓝 0,
      ∀ i,
        (branch g - energy i) *
            affineEigenbranchAdjugateColumn energy V branch x g i -
          g * ∑ j,
            V i j *
              affineEigenbranchAdjugateColumn energy V branch x g j = 0 := by
  let A := affineBranchCharacteristicMatrix energy V branch
  let w := affineEigenbranchAdjugateColumn energy V branch x
  filter_upwards [hroot] with g hg
  have hdet : (A g).det = 0 := by
    simpa [A, affineBranchCharacteristicMatrix,
      matrixCharpolyRelation, sub_add_eq_sub_sub] using hg
  have hmul : Matrix.mulVec (A g) (w g) = 0 := by
    funext i
    have hmatrix := Matrix.mul_adjugate (A g)
    have hentry := congrArg (fun M : Matrix ι ι ℂ => M i x) hmatrix
    change (∑ j, A g i j * w g j) = 0
    simpa [A, w, affineEigenbranchAdjugateColumn,
      Matrix.mul_apply, hdet] using hentry
  have hAdiag :
      A g =
        Matrix.diagonal (fun i => branch g - energy i) - g • V := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [A]
    · simp [A, affineBranchCharacteristicMatrix_apply_ne _ _ _ _ hij,
        Matrix.diagonal_apply_ne _ hij]
  intro i
  have hi := congrFun hmul i
  rw [hAdiag, Matrix.sub_mulVec] at hi
  simp only [Pi.sub_apply, Pi.zero_apply] at hi
  rw [Matrix.mulVec_diagonal, Matrix.smul_mulVec] at hi
  simpa [w, Matrix.mulVec, dotProduct, Finset.mul_sum] using hi

/-- Every off-label coordinate of the canonical eigenvector germ has the
exact first-order response forced by its spectral gap. -/
theorem affineEigenbranchAdjugateColumn_deriv_gap_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (V : Matrix ι ι ℂ) (hVdiag : ∀ i, V i i = 0)
    (x y : ι) (hyx : y ≠ x) (branch : ℂ → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hbase : branch 0 = energy x)
    (hroot :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy + g • V, branch g) = 0) :
    (energy x - energy y) *
        deriv
          (fun g =>
            affineEigenbranchAdjugateColumn energy V branch x g y) 0 =
      V y x *
        ∏ j ∈ Finset.univ.erase x, (energy x - energy j) := by
  let w := affineEigenbranchAdjugateColumn energy V branch x
  let S : ℂ → ℂ := fun g => ∑ j, V y j * w g j
  let P : ℂ := ∏ j ∈ Finset.univ.erase x, (energy x - energy j)
  have hfirst :
      deriv branch 0 = 0 :=
    affineEigenbranch_firstDerivative_eq_zero_of_diagonal_zero
      energy hinj V hVdiag x branch hbranch hbase hroot
  have hwan :
      ∀ i, AnalyticAt ℂ (fun g => w g i) 0 :=
    analyticAt_affineEigenbranchAdjugateColumn
      energy V branch x hbranch
  have hSan : AnalyticAt ℂ S 0 := by
    apply Finset.analyticAt_fun_sum
    intro j hj
    exact analyticAt_const.mul (hwan j)
  have hwy0 : w 0 y = 0 := by
    simp [w, affineEigenbranchAdjugateColumn_zero,
      hbase, hyx]
  have hS0 : S 0 = V y x * P := by
    unfold S P w
    rw [Finset.sum_eq_single x]
    · rw [affineEigenbranchAdjugateColumn_zero
        energy V branch x x hbase]
      simp
    · intro j hj hjx
      rw [affineEigenbranchAdjugateColumn_zero
        energy V branch x j hbase]
      simp [hjx]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  have hRderiv :
      HasDerivAt
        (fun g =>
          (branch g - energy y) * w g y - g * S g)
        ((deriv branch 0) * w 0 y +
            (branch 0 - energy y) *
              deriv (fun g => w g y) 0 -
          (S 0)) 0 := by
    convert!
      (((hbranch.differentiableAt.hasDerivAt.sub_const (energy y)).mul
          (hwan y).differentiableAt.hasDerivAt).sub
        ((hasDerivAt_id (0 : ℂ)).mul
          hSan.differentiableAt.hasDerivAt)) using 1
    all_goals simp [id_eq]
  have hRzero :
      (fun g =>
        (branch g - energy y) * w g y - g * S g) =ᶠ[𝓝 0]
        fun _ => 0 := by
    filter_upwards [
      affineEigenbranchAdjugateColumn_relation
        energy V branch x hroot] with g hg
    simpa [S, w] using hg y
  have hcoeff :
      (deriv branch 0) * w 0 y +
          (branch 0 - energy y) *
            deriv (fun g => w g y) 0 -
        S 0 = 0 := by
    rw [← hRderiv.deriv]
    simpa using hRzero.deriv_eq
  rw [hfirst, hwy0, hbase, hS0] at hcoeff
  linear_combination hcoeff

/-- **Exact second-order affine eigenbranch law.**  At a simple diagonal
spectrum, every analytic eigenvalue branch under a zero-diagonal affine
perturbation has the usual second-order response.  Here it is derived from
the characteristic equation and adjugate identity, not assumed from
perturbation theory. -/
theorem affineEigenbranch_secondDerivative_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (V : Matrix ι ι ℂ) (hVdiag : ∀ i, V i i = 0)
    (x : ι) (branch : ℂ → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hbase : branch 0 = energy x)
    (hroot :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy + g • V, branch g) = 0) :
    deriv (deriv branch) 0 =
      2 * ∑ y ∈ Finset.univ.erase x,
        V x y * V y x / (energy x - energy y) := by
  let w := affineEigenbranchAdjugateColumn energy V branch x
  let u : ℂ → ℂ := fun g => w g x
  let S : ℂ → ℂ := fun g => ∑ y, V x y * w g y
  let R : ℂ → ℂ := fun g =>
    (branch g - energy x) * u g - g * S g
  let Q : ℂ → ℂ := fun g =>
    deriv branch g * u g +
        (branch g - energy x) * deriv u g -
      (S g + g * deriv S g)
  let P : ℂ := ∏ y ∈ Finset.univ.erase x, (energy x - energy y)
  have hfirst :
      deriv branch 0 = 0 :=
    affineEigenbranch_firstDerivative_eq_zero_of_diagonal_zero
      energy hinj V hVdiag x branch hbranch hbase hroot
  have hwan :
      ∀ i, AnalyticAt ℂ (fun g => w g i) 0 :=
    analyticAt_affineEigenbranchAdjugateColumn
      energy V branch x hbranch
  have huan : AnalyticAt ℂ u 0 := hwan x
  have hSan : AnalyticAt ℂ S 0 := by
    apply Finset.analyticAt_fun_sum
    intro y hy
    exact analyticAt_const.mul (hwan y)
  have hu0 : u 0 = P := by
    simp [u, w, P, affineEigenbranchAdjugateColumn_zero,
      hbase]
  have hPne : P ≠ 0 := by
    unfold P
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hy).1 (hinj heq.symm)
  have hSderiv :
      HasDerivAt S
        (∑ y, V x y * deriv (fun g => w g y) 0) 0 := by
    apply HasDerivAt.fun_sum
    intro y hy
    exact (hwan y).differentiableAt.hasDerivAt.const_mul (V x y)
  have hSprime :
      deriv S 0 =
        P * ∑ y ∈ Finset.univ.erase x,
          V x y * V y x / (energy x - energy y) := by
    rw [hSderiv.deriv]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
    rw [hVdiag x, zero_mul, add_zero]
    calc
      ∑ y ∈ Finset.univ.erase x,
          V x y * deriv (fun g => w g y) 0 =
          ∑ y ∈ Finset.univ.erase x,
            V x y *
              (V y x * P / (energy x - energy y)) := by
            apply Finset.sum_congr rfl
            intro y hy
            congr 1
            apply (eq_div_iff ?_).2
            · rw [mul_comm]
              exact affineEigenbranchAdjugateColumn_deriv_gap_mul
                energy hinj V hVdiag x y
                (Finset.mem_erase.mp hy).1
                branch hbranch hbase hroot
            · apply sub_ne_zero.mpr
              intro heq
              exact (Finset.mem_erase.mp hy).1 (hinj heq.symm)
      _ = P * ∑ y ∈ Finset.univ.erase x,
            V x y * V y x / (energy x - energy y) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ring
  have hRzero :
      R =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [
      affineEigenbranchAdjugateColumn_relation
        energy V branch x hroot] with g hg
    simpa [R, S, u, w] using hg x
  have hRQ : deriv R =ᶠ[𝓝 0] Q := by
    filter_upwards [
      hbranch.eventually_analyticAt,
      huan.eventually_analyticAt,
      hSan.eventually_analyticAt] with g hbg hug hSg
    have hRderiv :
        HasDerivAt R
          (deriv branch g * u g +
              (branch g - energy x) * deriv u g -
            (S g + g * deriv S g)) g := by
      simpa [R, id_eq] using!
        (((hbg.differentiableAt.hasDerivAt.sub_const (energy x)).mul
            hug.differentiableAt.hasDerivAt).sub
          ((hasDerivAt_id g).mul
            hSg.differentiableAt.hasDerivAt))
    exact hRderiv.deriv
  have hQderiv :
      HasDerivAt Q
        (deriv (deriv branch) 0 * P - 2 * deriv S 0) 0 := by
    convert!
      (((hbranch.deriv.differentiableAt.hasDerivAt.mul
            huan.differentiableAt.hasDerivAt).add
          ((hbranch.differentiableAt.hasDerivAt.sub_const (energy x)).mul
            huan.deriv.differentiableAt.hasDerivAt)).sub
        (hSan.differentiableAt.hasDerivAt.add
          ((hasDerivAt_id (0 : ℂ)).mul
            hSan.deriv.differentiableAt.hasDerivAt))) using 1
    all_goals simp [id_eq, hfirst, hbase, hu0]
    all_goals ring
  have hQzero : Q =ᶠ[𝓝 0] fun _ => 0 := by
    have hRderivZero : deriv R =ᶠ[𝓝 0] fun _ => 0 := by
      simpa using hRzero.deriv
    exact hRQ.symm.trans hRderivZero
  have hcoeff :
      deriv (deriv branch) 0 * P - 2 * deriv S 0 = 0 := by
    rw [← hQderiv.deriv]
    simpa using hQzero.deriv_eq
  rw [hSprime] at hcoeff
  have hfactor :
      P * (deriv (deriv branch) 0 -
        2 * ∑ y ∈ Finset.univ.erase x,
          V x y * V y x / (energy x - energy y)) = 0 := by
    linear_combination hcoeff
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hPne)

/-- A branchwise linear spectral relation annihilates the exact second-order
interaction response.  This converts an analytic relation among actual
eigenvalues into a finite rational identity in unperturbed gaps. -/
theorem affineEigenbranch_linear_relation_secondOrder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (V : Matrix ι ι ℂ) (hVdiag : ∀ i, V i i = 0)
    (coefficient : ι → ℂ) (branch : ι → ℂ → ℂ)
    (hbranch : ∀ i, AnalyticAt ℂ (branch i) 0)
    (hbase : ∀ i, branch i 0 = energy i)
    (hroot :
      ∀ i,
        ∀ᶠ g in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal energy + g • V, branch i g) = 0)
    (hrelation :
      ∀ᶠ g in 𝓝 0,
        ∑ i, coefficient i * branch i g = 0) :
    ∑ i, coefficient i *
        (∑ j ∈ Finset.univ.erase i,
          V i j * V j i / (energy i - energy j)) = 0 := by
  let F : ℂ → ℂ := fun g => ∑ i, coefficient i * branch i g
  let F₁ : ℂ → ℂ := fun g =>
    ∑ i, coefficient i * deriv (branch i) g
  have hbranchEventually :
      ∀ᶠ g in 𝓝 0, ∀ i, AnalyticAt ℂ (branch i) g := by
    have hall :
        ∀ᶠ g in 𝓝 0,
          ∀ i ∈ (Finset.univ : Finset ι),
            AnalyticAt ℂ (branch i) g :=
      (Finset.eventually_all (Finset.univ : Finset ι)).2
        fun i hi => (hbranch i).eventually_analyticAt
    filter_upwards [hall] with g hg
    exact fun i => hg i (Finset.mem_univ i)
  have hderivF : deriv F =ᶠ[𝓝 0] F₁ := by
    filter_upwards [hbranchEventually] with g hg
    have hF :
        HasDerivAt F
          (∑ i, coefficient i * deriv (branch i) g) g := by
      apply HasDerivAt.fun_sum
      intro i hi
      exact (hg i).differentiableAt.hasDerivAt.const_mul
        (coefficient i)
    exact hF.deriv
  have hF₁deriv :
      HasDerivAt F₁
        (∑ i, coefficient i * deriv (deriv (branch i)) 0) 0 := by
    apply HasDerivAt.fun_sum
    intro i hi
    exact (hbranch i).deriv.differentiableAt.hasDerivAt.const_mul
      (coefficient i)
  have hFzero : F =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hrelation] with g hg
    simpa [F] using hg
  have hF₁zero : F₁ =ᶠ[𝓝 0] fun _ => 0 := by
    have hderivZero : deriv F =ᶠ[𝓝 0] fun _ => 0 := by
      simpa using hFzero.deriv
    exact hderivF.symm.trans hderivZero
  have hsecondRelation :
      ∑ i, coefficient i * deriv (deriv (branch i)) 0 = 0 := by
    rw [← hF₁deriv.deriv]
    simpa using hF₁zero.deriv_eq
  have hresponse (i : ι) :
      deriv (deriv (branch i)) 0 =
        2 * ∑ j ∈ Finset.univ.erase i,
          V i j * V j i / (energy i - energy j) :=
    affineEigenbranch_secondDerivative_eq
      energy hinj V hVdiag i (branch i)
      (hbranch i) (hbase i) (hroot i)
  simp_rw [hresponse] at hsecondRelation
  have htwice :
      2 * ∑ i, coefficient i *
          (∑ j ∈ Finset.univ.erase i,
            V i j * V j i / (energy i - energy j)) = 0 := by
    rw [Finset.mul_sum]
    calc
      ∑ i, 2 * (coefficient i *
          ∑ j ∈ Finset.univ.erase i,
            V i j * V j i / (energy i - energy j)) =
          ∑ i, coefficient i *
            (2 * ∑ j ∈ Finset.univ.erase i,
              V i j * V j i / (energy i - energy j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 0 := hsecondRelation
  exact (mul_eq_zero.mp htwice).resolve_left (by norm_num)

end

end GaloisForLFunctions.HTGeometry
