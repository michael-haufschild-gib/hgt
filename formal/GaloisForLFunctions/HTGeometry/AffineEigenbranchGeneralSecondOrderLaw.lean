import GaloisForLFunctions.HTGeometry.AffineEigenbranchSecondOrderLaw

/-!
# Second-order affine eigenbranch law with arbitrary diagonal

The usual second-order response depends only on off-diagonal transition
matrix elements.  This file removes the zero-diagonal restriction from the
formal perturbation theorem.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- General Hellmann--Feynman first derivative for a simple diagonal
spectral branch. -/
theorem affineEigenbranch_firstDerivative_eq_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (V : Matrix ι ι ℂ)
    (x : ι) (branch : ℂ → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hbase : branch 0 = energy x)
    (hroot :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy + g • V, branch g) = 0) :
    deriv branch 0 = V x x := by
  let A := affineBranchCharacteristicMatrix energy V branch
  let B := affineBranchCharacteristicMatrixFirstJet V branch 0
  have hAentry :
      ∀ i j, HasDerivAt (fun g => A g i j) (B i j) 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [A, B, affineBranchCharacteristicMatrix_apply_same,
        affineBranchCharacteristicMatrixFirstJet_apply_same]
      simpa only [Pi.sub_apply, id_eq, one_mul] using!
        ((hbranch.differentiableAt.hasDerivAt.sub_const (energy i)).sub
          ((hasDerivAt_id (0 : ℂ)).mul_const (V i i)))
    · simp only [A, B,
        affineBranchCharacteristicMatrix_apply_ne _ _ _ _ hij,
        affineBranchCharacteristicMatrixFirstJet_apply_ne _ _ _ hij]
      simpa only [Pi.neg_apply, id_eq, one_mul] using!
        ((hasDerivAt_id (0 : ℂ)).mul_const (V i j)).neg
  have hdetDeriv :=
    hasDerivAt_complexMatrixDet A B 0 hAentry
  have hdetZero :
      (fun g => (A g).det) =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
    filter_upwards [hroot] with g hg
    simpa [A, affineBranchCharacteristicMatrix,
      matrixCharpolyRelation, sub_add_eq_sub_sub] using hg
  have hjetZero : complexDetFirstJet (A 0) B = 0 := by
    rw [← hdetDeriv.deriv]
    simpa using hdetZero.deriv_eq
  have hA0 :
      A 0 = Matrix.diagonal (fun i => energy x - energy i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [A, hbase]
    · simp [A, affineBranchCharacteristicMatrix_apply_ne _ _ _ _ hij,
        Matrix.diagonal_apply_ne _ hij]
  have hBxx :
      B x x = deriv branch 0 - V x x := by
    simp [B]
  rw [hA0,
    complexDetFirstJet_diagonal_single_zero
      (fun i => energy x - energy i) B x (sub_self _),
    hBxx] at hjetZero
  have hprod :
      ∏ i ∈ Finset.univ.erase x,
        (energy x - energy i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hi).1 (hinj heq.symm)
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hjetZero).resolve_left hprod)

/-- Off-label first derivative of the canonical eigenvector germ; no
condition on the perturbation diagonal is required. -/
theorem affineEigenbranchAdjugateColumn_deriv_gap_mul_general
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (_hinj : Function.Injective energy)
    (V : Matrix ι ι ℂ)
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
            affineEigenbranchAdjugateColumn
              energy V branch x g y) 0 =
      V y x *
        ∏ j ∈ Finset.univ.erase x,
          (energy x - energy j) := by
  let w := affineEigenbranchAdjugateColumn
    energy V branch x
  let S : ℂ → ℂ := fun g => ∑ j, V y j * w g j
  let P : ℂ :=
    ∏ j ∈ Finset.univ.erase x, (energy x - energy j)
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
      (((hbranch.differentiableAt.hasDerivAt.sub_const
          (energy y)).mul
          (hwan y).differentiableAt.hasDerivAt).sub
        ((hasDerivAt_id (0 : ℂ)).mul
          hSan.differentiableAt.hasDerivAt)) using 1
    all_goals simp [id_eq]
  have hRzero :
      (fun g =>
        (branch g - energy y) * w g y - g * S g)
          =ᶠ[𝓝 0] fun _ => 0 := by
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
  rw [hwy0, hbase, hS0] at hcoeff
  linear_combination hcoeff

/-- Exact second-order eigenvalue response for an arbitrary affine
perturbation. -/
theorem affineEigenbranch_secondDerivative_eq_general
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (V : Matrix ι ι ℂ)
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
  let w :=
    affineEigenbranchAdjugateColumn energy V branch x
  let u : ℂ → ℂ := fun g => w g x
  let S : ℂ → ℂ := fun g => ∑ y, V x y * w g y
  let R : ℂ → ℂ := fun g =>
    (branch g - energy x) * u g - g * S g
  let Q : ℂ → ℂ := fun g =>
    deriv branch g * u g +
        (branch g - energy x) * deriv u g -
      (S g + g * deriv S g)
  let P : ℂ :=
    ∏ y ∈ Finset.univ.erase x, (energy x - energy y)
  have hfirst :
      deriv branch 0 = V x x :=
    affineEigenbranch_firstDerivative_eq_diagonal
      energy hinj V x branch hbranch hbase hroot
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
    simp [u, w, P,
      affineEigenbranchAdjugateColumn_zero, hbase]
  have hPne : P ≠ 0 := by
    unfold P
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hy).1 (hinj heq.symm)
  have hSderiv :
      HasDerivAt S
        (∑ y, V x y *
          deriv (fun g => w g y) 0) 0 := by
    apply HasDerivAt.fun_sum
    intro y hy
    exact
      (hwan y).differentiableAt.hasDerivAt.const_mul
        (V x y)
  have hSprime :
      deriv S 0 =
        V x x * deriv u 0 +
          P * ∑ y ∈ Finset.univ.erase x,
            V x y * V y x /
              (energy x - energy y) := by
    rw [hSderiv.deriv]
    rw [← Finset.sum_erase_add _
      (fun y => V x y * deriv (fun g => w g y) 0)
      (Finset.mem_univ x)]
    rw [add_comm
      (∑ y ∈ Finset.univ.erase x,
        V x y * deriv (fun g => w g y) 0)
      (V x x * deriv (fun g => w g x) 0)]
    change
      V x x * deriv u 0 +
        ∑ y ∈ Finset.univ.erase x,
          V x y * deriv (fun g => w g y) 0 =
      _
    congr 1
    calc
      ∑ y ∈ Finset.univ.erase x,
          V x y * deriv (fun g => w g y) 0 =
          ∑ y ∈ Finset.univ.erase x,
            V x y *
              (V y x * P /
                (energy x - energy y)) := by
            apply Finset.sum_congr rfl
            intro y hy
            congr 1
            apply (eq_div_iff ?_).2
            · rw [mul_comm]
              exact
                affineEigenbranchAdjugateColumn_deriv_gap_mul_general
                  energy hinj V x y
                  (Finset.mem_erase.mp hy).1
                  branch hbranch hbase hroot
            · apply sub_ne_zero.mpr
              intro heq
              exact (Finset.mem_erase.mp hy).1
                (hinj heq.symm)
      _ = P * ∑ y ∈ Finset.univ.erase x,
            V x y * V y x /
              (energy x - energy y) := by
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
        (((hbg.differentiableAt.hasDerivAt.sub_const
            (energy x)).mul
            hug.differentiableAt.hasDerivAt).sub
          ((hasDerivAt_id g).mul
            hSg.differentiableAt.hasDerivAt))
    exact hRderiv.deriv
  have hQderiv :
      HasDerivAt Q
        (deriv (deriv branch) 0 * P +
          2 * V x x * deriv u 0 -
          2 * deriv S 0) 0 := by
    convert!
      (((hbranch.deriv.differentiableAt.hasDerivAt.mul
            huan.differentiableAt.hasDerivAt).add
          ((hbranch.differentiableAt.hasDerivAt.sub_const
            (energy x)).mul
            huan.deriv.differentiableAt.hasDerivAt)).sub
        (hSan.differentiableAt.hasDerivAt.add
          ((hasDerivAt_id (0 : ℂ)).mul
            hSan.deriv.differentiableAt.hasDerivAt))) using 1
    all_goals simp [id_eq, hfirst, hbase, hu0]
    all_goals ring
  have hQzero : Q =ᶠ[𝓝 0] fun _ => 0 := by
    have hRderivZero :
        deriv R =ᶠ[𝓝 0] fun _ => 0 := by
      simpa using hRzero.deriv
    exact hRQ.symm.trans hRderivZero
  have hcoeff :
      deriv (deriv branch) 0 * P +
          2 * V x x * deriv u 0 -
        2 * deriv S 0 = 0 := by
    rw [← hQderiv.deriv]
    simpa using hQzero.deriv_eq
  rw [hSprime] at hcoeff
  have hfactor :
      P * (deriv (deriv branch) 0 -
        2 * ∑ y ∈ Finset.univ.erase x,
          V x y * V y x /
            (energy x - energy y)) = 0 := by
    linear_combination hcoeff
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hfactor).resolve_left hPne)

/-- A branchwise linear relation annihilates the exact second-order
off-diagonal response for an arbitrary affine perturbation. -/
theorem affineEigenbranch_linear_relation_secondOrder_general
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (V : Matrix ι ι ℂ)
    (coefficient : ι → ℂ) (branch : ι → ℂ → ℂ)
    (hbranch : ∀ i, AnalyticAt ℂ (branch i) 0)
    (hbase : ∀ i, branch i 0 = energy i)
    (hroot :
      ∀ i,
        ∀ᶠ g in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal energy + g • V,
              branch i g) = 0)
    (hrelation :
      ∀ᶠ g in 𝓝 0,
        ∑ i, coefficient i * branch i g = 0) :
    ∑ i, coefficient i *
        (∑ j ∈ Finset.univ.erase i,
          V i j * V j i /
            (energy i - energy j)) = 0 := by
  let F : ℂ → ℂ :=
    fun g => ∑ i, coefficient i * branch i g
  let F₁ : ℂ → ℂ :=
    fun g =>
      ∑ i, coefficient i * deriv (branch i) g
  have hbranchEventually :
      ∀ᶠ g in 𝓝 0,
        ∀ i, AnalyticAt ℂ (branch i) g := by
    have hall :
        ∀ᶠ g in 𝓝 0,
          ∀ i ∈ (Finset.univ : Finset ι),
            AnalyticAt ℂ (branch i) g :=
      (Finset.eventually_all
        (Finset.univ : Finset ι)).2
        fun i hi => (hbranch i).eventually_analyticAt
    filter_upwards [hall] with g hg
    exact fun i => hg i (Finset.mem_univ i)
  have hderivF : deriv F =ᶠ[𝓝 0] F₁ := by
    filter_upwards [hbranchEventually] with g hg
    have hF :
        HasDerivAt F
          (∑ i, coefficient i *
            deriv (branch i) g) g := by
      apply HasDerivAt.fun_sum
      intro i hi
      exact
        (hg i).differentiableAt.hasDerivAt.const_mul
          (coefficient i)
    exact hF.deriv
  have hF₁deriv :
      HasDerivAt F₁
        (∑ i, coefficient i *
          deriv (deriv (branch i)) 0) 0 := by
    apply HasDerivAt.fun_sum
    intro i hi
    exact
      (hbranch i).deriv.differentiableAt.hasDerivAt.const_mul
        (coefficient i)
  have hFzero : F =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hrelation] with g hg
    simpa [F] using hg
  have hF₁zero : F₁ =ᶠ[𝓝 0] fun _ => 0 := by
    have hderivZero :
        deriv F =ᶠ[𝓝 0] fun _ => 0 := by
      simpa using hFzero.deriv
    exact hderivF.symm.trans hderivZero
  have hsecondRelation :
      ∑ i, coefficient i *
        deriv (deriv (branch i)) 0 = 0 := by
    rw [← hF₁deriv.deriv]
    simpa using hF₁zero.deriv_eq
  have hresponse (i : ι) :
      deriv (deriv (branch i)) 0 =
        2 * ∑ j ∈ Finset.univ.erase i,
          V i j * V j i /
            (energy i - energy j) :=
    affineEigenbranch_secondDerivative_eq_general
      energy hinj V i (branch i)
      (hbranch i) (hbase i) (hroot i)
  simp_rw [hresponse] at hsecondRelation
  have htwice :
      2 * ∑ i, coefficient i *
          (∑ j ∈ Finset.univ.erase i,
            V i j * V j i /
              (energy i - energy j)) = 0 := by
    rw [Finset.mul_sum]
    calc
      ∑ i, 2 * (coefficient i *
          ∑ j ∈ Finset.univ.erase i,
            V i j * V j i /
              (energy i - energy j)) =
          ∑ i, coefficient i *
            (2 * ∑ j ∈ Finset.univ.erase i,
              V i j * V j i /
                (energy i - energy j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 0 := hsecondRelation
  exact
    (mul_eq_zero.mp htwice).resolve_left
      (by norm_num)

end

end GaloisForLFunctions.HTGeometry
