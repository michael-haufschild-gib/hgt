import GaloisForLFunctions.HilbertMetric.SymmetricFockShadow
import GaloisForLFunctions.HilbertMetric.RankOneSchurGaussianConcavity

/-!
# Central-Casimir Hall expansion

A finite self-adjoint Parseval family cannot shrink any subspace.  The second
theorem transports this law through an arbitrary invertible scaling.  This is
the formal Hilbert-space core of the replica local-Casimir argument: once the
inverse square root of a central positive Casimir makes the scaled generators
self-adjoint and Parseval, Hall expansion follows without a coordinate or
generic-position hypothesis.
-/

open scoped BigOperators Matrix MatrixOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions.HilbertMetric

/-- A finite self-adjoint Parseval family expands every subspace. -/
theorem selfAdjointParsevalFamily_subspace_finrank
    {X J : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [Fintype J]
    (T : J → X →ₗ[ℝ] X)
    (hsymm : ∀ j, (T j).IsSymmetric)
    (hparseval : ∀ x, ∑ j, ‖T j x‖ ^ 2 = ‖x‖ ^ 2)
    (U V : Submodule ℝ X)
    (hUV : ∀ j x, x ∈ U → T j x ∈ V) :
    Module.finrank ℝ U ≤ Module.finrank ℝ V := by
  have hleft : ∀ x, ∑ j, ‖T j x‖ ^ 2 = (1 : ℝ) * ‖x‖ ^ 2 := by
    intro x
    simpa using hparseval x
  have hright : ∀ y, ∑ j, ‖(T j).adjoint y‖ ^ 2 = (1 : ℝ) * ‖y‖ ^ 2 := by
    intro y
    simp_rw [(hsymm _).adjoint_eq]
    simpa using hparseval y
  have h := tightOperatorFamily_subspace_finrank
    T 1 1 hleft hright U V hUV
  norm_num at h
  exact_mod_cast h

/-- Hall expansion is invariant under an invertible left scaling when the
scaled family is self-adjoint and Parseval. -/
theorem equivScaledSelfAdjointParsevalFamily_subspace_finrank
    {X J : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [Fintype J]
    (A : J → X →ₗ[ℝ] X) (R : X ≃ₗ[ℝ] X)
    (hsymm : ∀ j, (R.toLinearMap.comp (A j)).IsSymmetric)
    (hparseval : ∀ x, ∑ j, ‖R (A j x)‖ ^ 2 = ‖x‖ ^ 2)
    (U V : Submodule ℝ X)
    (hUV : ∀ j x, x ∈ U → A j x ∈ V) :
    Module.finrank ℝ U ≤ Module.finrank ℝ V := by
  let T : J → X →ₗ[ℝ] X := fun j => R.toLinearMap.comp (A j)
  let RV : Submodule ℝ X := V.map R.toLinearMap
  have hTRV : ∀ j x, x ∈ U → T j x ∈ RV := by
    intro j x hx
    refine ⟨A j x, hUV j x hx, ?_⟩
    rfl
  have hscaled : Module.finrank ℝ U ≤ Module.finrank ℝ RV :=
    selfAdjointParsevalFamily_subspace_finrank T
      (by simpa [T] using hsymm)
      (by simpa [T] using hparseval) U RV hTRV
  rw [show Module.finrank ℝ RV = Module.finrank ℝ V by
    exact LinearEquiv.finrank_map_eq R V] at hscaled
  exact hscaled

/-- A finite family with exact left and right Hilbert-energy constants expands
every subspace over either the real or complex field. -/
theorem tightOperatorFamily_subspace_finrank_rclike
    {𝕜 X Y J : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]
    [Fintype J]
    (T : J → X →ₗ[𝕜] Y) (a b : ℝ)
    (hleft : ∀ x, ∑ j, ‖T j x‖ ^ 2 = a * ‖x‖ ^ 2)
    (hright : ∀ y, ∑ j, ‖(T j).adjoint y‖ ^ 2 = b * ‖y‖ ^ 2)
    (U : Submodule 𝕜 X) (V : Submodule 𝕜 Y)
    (hUV : ∀ j x, x ∈ U → T j x ∈ V) :
    a * (Module.finrank 𝕜 U : ℝ) ≤ b * (Module.finrank 𝕜 V : ℝ) := by
  let u := stdOrthonormalBasis 𝕜 U
  let v := stdOrthonormalBasis 𝕜 V
  have hu : Orthonormal 𝕜 (fun p => ((u p : U) : X)) := by
    refine ⟨?_, ?_⟩
    · intro p
      change ‖u p‖ = 1
      exact u.orthonormal.1 p
    · intro p q hpq
      change inner 𝕜 (u p) (u q) = 0
      exact u.orthonormal.2 hpq
  have hvnorm (q) : ‖((v q : V) : Y)‖ ^ 2 = 1 := by
    change ‖v q‖ ^ 2 = 1
    rw [v.orthonormal.1 q]
    norm_num
  have hunorm (p) : ‖((u p : U) : X)‖ ^ 2 = 1 := by
    change ‖u p‖ ^ 2 = 1
    rw [u.orthonormal.1 p]
    norm_num
  rw [show a * (Module.finrank 𝕜 U : ℝ) =
      ∑ p, a * ‖((u p : U) : X)‖ ^ 2 by
        simp [hunorm, mul_comm],
    show b * (Module.finrank 𝕜 V : ℝ) =
      ∑ q, b * ‖((v q : V) : Y)‖ ^ 2 by
        simp [hvnorm, mul_comm]]
  rw [show (∑ p, a * ‖((u p : U) : X)‖ ^ 2) =
      ∑ p, ∑ j, ‖T j ((u p : U) : X)‖ ^ 2 by
        apply Finset.sum_congr rfl
        intro p _
        exact (hleft _).symm]
  rw [Finset.sum_comm]
  calc
    ∑ j, ∑ p, ‖T j ((u p : U) : X)‖ ^ 2 =
        ∑ j, ∑ p, ∑ q,
          ‖inner 𝕜 ((v q : V) : Y) (T j ((u p : U) : X))‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro p _
          let z : V := ⟨T j ((u p : U) : X), hUV j _ (u p).property⟩
          simpa [z] using (v.sum_sq_norm_inner_right z).symm
    _ = ∑ j, ∑ q, ∑ p,
        ‖inner 𝕜 ((u p : U) : X) ((T j).adjoint ((v q : V) : Y))‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro q _
          apply Finset.sum_congr rfl
          intro p _
          calc
            ‖inner 𝕜 ((v q : V) : Y) (T j ((u p : U) : X))‖ ^ 2 =
                ‖inner 𝕜 ((T j).adjoint ((v q : V) : Y))
                  ((u p : U) : X)‖ ^ 2 := by
                    rw [(T j).adjoint_inner_left]
            _ = ‖inner 𝕜 ((u p : U) : X)
                ((T j).adjoint ((v q : V) : Y))‖ ^ 2 := by
                  rw [← inner_conj_symm, RCLike.norm_conj]
    _ ≤ ∑ j, ∑ q, ‖(T j).adjoint ((v q : V) : Y)‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro q _
          simpa using (hu.sum_inner_products_le
            ((T j).adjoint ((v q : V) : Y)) (s := Finset.univ))
    _ = ∑ q, ∑ j, ‖(T j).adjoint ((v q : V) : Y)‖ ^ 2 := by
          rw [Finset.sum_comm]
    _ = ∑ q, b * ‖((v q : V) : Y)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro q _
          exact hright _

/-- A finite self-adjoint Parseval family over either `ℝ` or `ℂ` expands
every subspace. -/
theorem selfAdjointParsevalFamily_subspace_finrank_rclike
    {𝕜 X J : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    [Fintype J]
    (T : J → X →ₗ[𝕜] X)
    (hsymm : ∀ j, (T j).IsSymmetric)
    (hparseval : ∀ x, ∑ j, ‖T j x‖ ^ 2 = ‖x‖ ^ 2)
    (U V : Submodule 𝕜 X)
    (hUV : ∀ j x, x ∈ U → T j x ∈ V) :
    Module.finrank 𝕜 U ≤ Module.finrank 𝕜 V := by
  have hleft : ∀ x, ∑ j, ‖T j x‖ ^ 2 = (1 : ℝ) * ‖x‖ ^ 2 := by
    intro x
    simpa using hparseval x
  have hright : ∀ y, ∑ j, ‖(T j).adjoint y‖ ^ 2 = (1 : ℝ) * ‖y‖ ^ 2 := by
    intro y
    simp_rw [(hsymm _).adjoint_eq]
    simpa using hparseval y
  have h := tightOperatorFamily_subspace_finrank_rclike
    T 1 1 hleft hright U V hUV
  norm_num at h
  exact_mod_cast h

/-- RCLike Hall expansion is invariant under an invertible left scaling when
the scaled family is self-adjoint and Parseval. -/
theorem equivScaledSelfAdjointParsevalFamily_subspace_finrank_rclike
    {𝕜 X J : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    [Fintype J]
    (A : J → X →ₗ[𝕜] X) (R : X ≃ₗ[𝕜] X)
    (hsymm : ∀ j, (R.toLinearMap.comp (A j)).IsSymmetric)
    (hparseval : ∀ x, ∑ j, ‖R (A j x)‖ ^ 2 = ‖x‖ ^ 2)
    (U V : Submodule 𝕜 X)
    (hUV : ∀ j x, x ∈ U → A j x ∈ V) :
    Module.finrank 𝕜 U ≤ Module.finrank 𝕜 V := by
  let T : J → X →ₗ[𝕜] X := fun j => R.toLinearMap.comp (A j)
  let RV : Submodule 𝕜 X := V.map R.toLinearMap
  have hTRV : ∀ j x, x ∈ U → T j x ∈ RV := by
    intro j x hx
    refine ⟨A j x, hUV j x hx, ?_⟩
    rfl
  have hscaled : Module.finrank 𝕜 U ≤ Module.finrank 𝕜 RV :=
    selfAdjointParsevalFamily_subspace_finrank_rclike T
      (by simpa [T] using hsymm)
      (by simpa [T] using hparseval) U RV hTRV
  rw [show Module.finrank 𝕜 RV = Module.finrank 𝕜 V by
    exact LinearEquiv.finrank_map_eq R V] at hscaled
  exact hscaled

private theorem matrixSqrt_mul_self_rclike
    {𝕜 X : Type*} [RCLike 𝕜] [Fintype X] [DecidableEq X]
    (M : Matrix X X 𝕜) (hM : 0 ≤ M) :
    CFC.sqrt M * CFC.sqrt M = M := by
  exact CFC.sqrt_mul_sqrt_self _ hM

private theorem matrixSqrt_conjTranspose_rclike
    {𝕜 X : Type*} [RCLike 𝕜] [Fintype X] [DecidableEq X]
    (M : Matrix X X 𝕜) :
    (CFC.sqrt M).conjTranspose = CFC.sqrt M := by
  have hstar := (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq
  rw [Matrix.star_eq_conjTranspose] at hstar
  exact hstar

private theorem matrix_inv_eq_sqrt_inv_mul_rclike
    {𝕜 X : Type*} [RCLike 𝕜] [Fintype X] [DecidableEq X]
    (M : Matrix X X 𝕜) (hM : 0 ≤ M) (hMunit : IsUnit M) :
    M⁻¹ = (CFC.sqrt M)⁻¹ * (CFC.sqrt M)⁻¹ := by
  let R := CFC.sqrt M
  letI : Invertible M :=
    Matrix.invertibleOfIsUnitDet M (M.isUnit_iff_isUnit_det.mp hMunit)
  have hRunit : IsUnit R :=
    (CFC.isUnit_sqrt_iff M hM).mpr hMunit
  letI : Invertible R := hRunit.nonempty_invertible.some
  have hR2 : R * R = M := matrixSqrt_mul_self_rclike M hM
  apply Matrix.mul_left_injective_of_invertible (A := M)
  change M⁻¹ * M = (R⁻¹ * R⁻¹) * M
  rw [Matrix.inv_mul_of_invertible, ← hR2]
  have hcancel : R⁻¹ * R = 1 := Matrix.inv_mul_of_invertible _
  symm
  calc
    (R⁻¹ * R⁻¹) * (R * R) = R⁻¹ * (R⁻¹ * R) * R := by noncomm_ring
    _ = R⁻¹ * R := by rw [hcancel]; simp
    _ = 1 := hcancel

private theorem conjTranspose_mul_toEuclideanLin
    {𝕜 X Y : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (B : Matrix Y X 𝕜) :
    (B.conjTranspose * B).toEuclideanLin =
      B.toEuclideanLin.adjoint ∘ₗ B.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.toLpLin_apply]
  rw [Matrix.mulVec_mulVec]

private theorem matrixFamily_energy_eq_re_inner_sum
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜)
    (x : EuclideanSpace 𝕜 X) :
    ∑ j, ‖(A j).toEuclideanLin x‖ ^ 2 =
      RCLike.re (inner 𝕜 x (Matrix.toEuclideanLin
        (∑ j, (A j).conjTranspose * A j) x)) := by
  classical
  calc
    ∑ j, ‖(A j).toEuclideanLin x‖ ^ 2 =
        ∑ j, RCLike.re (inner 𝕜 x (Matrix.toEuclideanLin
          ((A j).conjTranspose * A j) x)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← inner_self_eq_norm_sq (𝕜 := 𝕜)]
          congr 1
          rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply,
            ← conjTranspose_mul_toEuclideanLin]
    _ = RCLike.re (inner 𝕜 x ((∑ j, Matrix.toEuclideanLin
        ((A j).conjTranspose * A j)) x)) := by
          simp [inner_sum]
    _ = RCLike.re (inner 𝕜 x (Matrix.toEuclideanLin
        (∑ j, (A j).conjTranspose * A j) x)) := by
          rw [map_sum]

private theorem matrixFamily_energy_of_sum_conjTranspose_mul_eq_one
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (B : J → Matrix X X 𝕜)
    (hB : ∑ j, (B j).conjTranspose * B j = 1)
    (x : EuclideanSpace 𝕜 X) :
    ∑ j, ‖(B j).toEuclideanLin x‖ ^ 2 = ‖x‖ ^ 2 := by
  classical
  rw [matrixFamily_energy_eq_re_inner_sum B, hB]
  simp

/-- A Hermitian finite family with trivial common kernel has a nonnegative,
invertible quadratic Casimir. -/
theorem hermitianQuadraticCasimir_nonneg_and_isUnit_of_commonKernel
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜)
    (hsymm : ∀ j, (A j).conjTranspose = A j)
    (hker : ∀ x : EuclideanSpace 𝕜 X,
      (∀ j, (A j).toEuclideanLin x = 0) → x = 0) :
    0 ≤ (∑ j, A j * A j) ∧ IsUnit (∑ j, A j * A j) := by
  classical
  let K : Matrix X X 𝕜 := ∑ j, A j * A j
  have hKform : K = ∑ j, (A j).conjTranspose * A j := by
    dsimp [K]
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j]
  have hnonneg : 0 ≤ K := by
    rw [hKform]
    exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg (A j)
  have hKinj : Function.Injective K.toEuclideanLin := by
    intro x y hxy
    have hKzero : K.toEuclideanLin (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hsum : ∑ j, ‖(A j).toEuclideanLin (x - y)‖ ^ 2 = 0 := by
      rw [matrixFamily_energy_eq_re_inner_sum A, ← hKform, hKzero]
      simp
    have hterm : ∀ j, ‖(A j).toEuclideanLin (x - y)‖ ^ 2 = 0 := by
      intro j
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg ‖(A j).toEuclideanLin (x - y)‖)).mp hsum j
        (Finset.mem_univ j)
    have hz : x - y = 0 := hker (x - y) fun j => by
      apply norm_eq_zero.mp
      exact sq_eq_zero_iff.mp (hterm j)
    exact sub_eq_zero.mp hz
  have hmulVec : Function.Injective K.mulVec := by
    intro x y hxy
    have heuc :
        K.toEuclideanLin (WithLp.toLp 2 x) =
          K.toEuclideanLin (WithLp.toLp 2 y) := by
      simpa [Matrix.toLpLin_apply] using congrArg (WithLp.toLp 2) hxy
    have hcoord := congrArg WithLp.ofLp (hKinj heuc)
    simpa using hcoord
  exact ⟨by simpa [K] using hnonneg,
    by simpa [K] using (Matrix.mulVec_injective_iff_isUnit.mp hmulVec)⟩

def centralCasimirInvSqrtScaleRCLike
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜) : Matrix X X 𝕜 :=
  (CFC.sqrt (∑ j, A j * A j))⁻¹

theorem centralCasimirInvSqrtScaleRCLike_commutes
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜)
    (hnonneg : 0 ≤ (∑ j, A j * A j))
    (hunit : IsUnit (∑ j, A j * A j))
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k))
    (j : J) :
    centralCasimirInvSqrtScaleRCLike A * A j =
      A j * centralCasimirInvSqrtScaleRCLike A := by
  classical
  let K : Matrix X X 𝕜 := ∑ k, A k * A k
  let S : Matrix X X 𝕜 := CFC.sqrt K
  let R : Matrix X X 𝕜 := S⁻¹
  have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff K hnonneg).mpr hunit
  letI : Invertible S := hSunit.nonempty_invertible.some
  have hSA : S * A j = A j * S := by
    have hKA : Commute K (A j) := hcentral j
    have h := hKA.cfcₙ_nnreal NNReal.sqrt
    simpa [S, K, CFC.sqrt] using h.eq
  have hleft : R * S = 1 := Matrix.inv_mul_of_invertible _
  have hright : S * R = 1 := Matrix.mul_inv_of_invertible _
  change R * A j = A j * R
  calc
    R * A j = R * A j * (S * R) := by rw [hright, Matrix.mul_one]
    _ = R * (A j * S) * R := by noncomm_ring
    _ = R * (S * A j) * R := by rw [hSA]
    _ = (R * S) * A j * R := by noncomm_ring
    _ = A j * R := by rw [hleft, Matrix.one_mul]

theorem centralCasimirInvSqrtScaleRCLike_conjTranspose
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜) :
    (centralCasimirInvSqrtScaleRCLike A).conjTranspose =
      centralCasimirInvSqrtScaleRCLike A := by
  classical
  rw [centralCasimirInvSqrtScaleRCLike, Matrix.conjTranspose_nonsing_inv,
    matrixSqrt_conjTranspose_rclike]

theorem centralCasimirRCLike_scaled_conjTranspose_mul_sum
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜)
    (hsymm : ∀ j, (A j).conjTranspose = A j)
    (hnonneg : 0 ≤ (∑ j, A j * A j))
    (hunit : IsUnit (∑ j, A j * A j))
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k)) :
    ∑ j,
      (centralCasimirInvSqrtScaleRCLike A * A j).conjTranspose *
        (centralCasimirInvSqrtScaleRCLike A * A j) = 1 := by
  classical
  let K : Matrix X X 𝕜 := ∑ k, A k * A k
  let R : Matrix X X 𝕜 := centralCasimirInvSqrtScaleRCLike A
  letI : Invertible K :=
    Matrix.invertibleOfIsUnitDet K (K.isUnit_iff_isUnit_det.mp hunit)
  have hRconjTranspose : R.conjTranspose = R :=
    centralCasimirInvSqrtScaleRCLike_conjTranspose A
  have hRA : ∀ j, R * A j = A j * R :=
    centralCasimirInvSqrtScaleRCLike_commutes A hnonneg hunit hcentral
  have hR2 : R * R = K⁻¹ := by
    dsimp [R, centralCasimirInvSqrtScaleRCLike]
    exact (matrix_inv_eq_sqrt_inv_mul_rclike K hnonneg hunit).symm
  calc
    (∑ j, (R * A j).conjTranspose * (R * A j)) =
        ∑ j, R * R * (A j * A j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Matrix.conjTranspose_mul, hsymm j, hRconjTranspose]
          calc
            (A j * R) * (R * A j) =
                (A j * R) * (A j * R) := by rw [hRA j]
            _ = (R * A j) * (R * A j) := by rw [← hRA j]
            _ = R * (A j * R) * A j := by noncomm_ring
            _ = R * (R * A j) * A j := by rw [← hRA j]
            _ = R * R * (A j * A j) := by noncomm_ring
    _ = R * R * (∑ j, A j * A j) := by rw [Matrix.mul_sum]
    _ = K⁻¹ * K := by rw [hR2]
    _ = 1 := Matrix.inv_mul_of_invertible _

/-- Central nonnegative invertible Casimir is an exact Hall certificate over
either `ℝ` or `ℂ`: every subspace has at least its own dimension after applying
all self-adjoint generators. -/
theorem centralCasimirMatrixFamily_subspace_finrank_rclike
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜)
    (hsymm : ∀ j, (A j).conjTranspose = A j)
    (hnonneg : 0 ≤ (∑ j, A j * A j))
    (hunit : IsUnit (∑ j, A j * A j))
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k))
    (U V : Submodule 𝕜 (EuclideanSpace 𝕜 X))
    (hUV : ∀ j x, x ∈ U → (A j).toEuclideanLin x ∈ V) :
    Module.finrank 𝕜 U ≤ Module.finrank 𝕜 V := by
  classical
  let Rm : Matrix X X 𝕜 := centralCasimirInvSqrtScaleRCLike A
  let B : J → Matrix X X 𝕜 := fun j => Rm * A j
  have hBsum : ∑ j, (B j).conjTranspose * B j = 1 := by
    simpa [B, Rm] using
      centralCasimirRCLike_scaled_conjTranspose_mul_sum
        A hsymm hnonneg hunit hcentral
  have hBsymm : ∀ j, (B j).conjTranspose = B j := by
    intro j
    dsimp [B]
    rw [Matrix.conjTranspose_mul, hsymm j,
      centralCasimirInvSqrtScaleRCLike_conjTranspose,
      centralCasimirInvSqrtScaleRCLike_commutes A hnonneg hunit hcentral]
  let K : Matrix X X 𝕜 := ∑ j, A j * A j
  let S : Matrix X X 𝕜 := CFC.sqrt K
  have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff K hnonneg).mpr hunit
  have hRunit : IsUnit Rm := by
    dsimp [Rm, centralCasimirInvSqrtScaleRCLike, S, K]
    exact Matrix.isUnit_nonsing_inv_iff.mpr hSunit
  have hRinj : Function.Injective Rm.toEuclideanLin := by
    intro x y hxy
    have hmul : Rm.mulVec x.ofLp = Rm.mulVec y.ofLp :=
      congrArg (fun z => z.ofLp) hxy
    have hcoord : x.ofLp = y.ofLp :=
      Matrix.mulVec_injective_of_isUnit hRunit hmul
    have := congrArg (WithLp.toLp 2) hcoord
    simpa using this
  have hRsurj : Function.Surjective Rm.toEuclideanLin :=
    LinearMap.injective_iff_surjective.mp hRinj
  let R : EuclideanSpace 𝕜 X ≃ₗ[𝕜] EuclideanSpace 𝕜 X :=
    LinearEquiv.ofBijective Rm.toEuclideanLin ⟨hRinj, hRsurj⟩
  have hRmap : R.toLinearMap = Rm.toEuclideanLin := by rfl
  let T : J → EuclideanSpace 𝕜 X →ₗ[𝕜] EuclideanSpace 𝕜 X :=
    fun j => (B j).toEuclideanLin
  have hTsymm : ∀ j, (T j).IsSymmetric := by
    intro j
    have hAdj : (T j).adjoint = T j := by
      dsimp [T]
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hBsymm]
    intro x y
    calc
      inner 𝕜 (T j x) y = inner 𝕜 x ((T j).adjoint y) :=
        (LinearMap.adjoint_inner_right (T j) x y).symm
      _ = inner 𝕜 x (T j y) := by rw [hAdj]
  have hTparseval : ∀ x, ∑ j, ‖T j x‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    exact matrixFamily_energy_of_sum_conjTranspose_mul_eq_one B hBsum x
  let BV : Submodule 𝕜 (EuclideanSpace 𝕜 X) := V.map R.toLinearMap
  have hTBV : ∀ j x, x ∈ U → T j x ∈ BV := by
    intro j x hx
    refine ⟨(A j).toEuclideanLin x, hUV j x hx, ?_⟩
    rw [hRmap]
    ext
    simp [T, B, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have hscaled := selfAdjointParsevalFamily_subspace_finrank_rclike
    T hTsymm hTparseval U BV hTBV
  have hBVfin : Module.finrank 𝕜 BV = Module.finrank 𝕜 V := by
    simpa [BV] using LinearEquiv.finrank_map_eq R V
  rw [hBVfin] at hscaled
  exact hscaled

/-- A Hermitian family with central quadratic Casimir and trivial common
kernel satisfies the exact Hall inequality on every subspace. -/
theorem centralHermitianMatrixFamily_subspace_finrank_of_commonKernel
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜)
    (hsymm : ∀ j, (A j).conjTranspose = A j)
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k))
    (hker : ∀ x : EuclideanSpace 𝕜 X,
      (∀ j, (A j).toEuclideanLin x = 0) → x = 0)
    (U V : Submodule 𝕜 (EuclideanSpace 𝕜 X))
    (hUV : ∀ j x, x ∈ U → (A j).toEuclideanLin x ∈ V) :
    Module.finrank 𝕜 U ≤ Module.finrank 𝕜 V := by
  obtain ⟨hnonneg, hunit⟩ :=
    hermitianQuadraticCasimir_nonneg_and_isUnit_of_commonKernel A hsymm hker
  exact centralCasimirMatrixFamily_subspace_finrank_rclike
    A hsymm hnonneg hunit hcentral U V hUV

private theorem transpose_mul_toEuclideanLin
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (B : Matrix Y X ℝ) :
    (B.transpose * B).toEuclideanLin =
      B.toEuclideanLin.adjoint ∘ₗ B.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.toLpLin_apply]
  rw [Matrix.mulVec_mulVec]

/-- A real matrix family whose transpose-square sum is the identity is a
Parseval family on Euclidean space. -/
theorem matrixFamily_energy_of_sum_transpose_mul_eq_one
    {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J]
    (B : J → Matrix X X ℝ)
    (hB : ∑ j, (B j).transpose * B j = 1)
    (x : EuclideanSpace ℝ X) :
    ∑ j, ‖(B j).toEuclideanLin x‖ ^ 2 = ‖x‖ ^ 2 := by
  classical
  calc
    ∑ j, ‖(B j).toEuclideanLin x‖ ^ 2 =
        ∑ j, inner ℝ x (Matrix.toEuclideanLin
          ((B j).transpose * B j) x) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← real_inner_self_eq_norm_sq]
          change inner ℝ ((B j).toEuclideanLin x)
            ((B j).toEuclideanLin x) = _
          rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply,
            ← transpose_mul_toEuclideanLin]
    _ = inner ℝ x ((∑ j, Matrix.toEuclideanLin
        ((B j).transpose * B j)) x) := by
          simp [inner_sum]
    _ = inner ℝ x (Matrix.toEuclideanLin
        (∑ j, (B j).transpose * B j) x) := by
          rw [map_sum]
    _ = ‖x‖ ^ 2 := by
          rw [hB]
          simp

/-- Inverse square-root normalization by a family's quadratic Casimir. -/
def centralCasimirInvSqrtScale
    {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X ℝ) : Matrix X X ℝ :=
  (CFC.sqrt (∑ j, A j * A j))⁻¹

/-- Inverse square-root normalization commutes with every generator whenever
the quadratic Casimir does and is positive definite. -/
theorem centralCasimirInvSqrtScale_commutes
    {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X ℝ)
    (hpos : (∑ j, A j * A j).PosDef)
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k))
    (j : J) :
    centralCasimirInvSqrtScale A * A j =
      A j * centralCasimirInvSqrtScale A := by
  classical
  let K : Matrix X X ℝ := ∑ k, A k * A k
  let S : Matrix X X ℝ := CFC.sqrt K
  let R : Matrix X X ℝ := S⁻¹
  have hSunit : IsUnit S :=
    (CFC.isUnit_sqrt_iff K hpos.posSemidef.nonneg).mpr hpos.isUnit
  letI : Invertible S := hSunit.nonempty_invertible.some
  have hSA : S * A j = A j * S := by
    have hKA : Commute K (A j) := hcentral j
    have h := hKA.cfcₙ_nnreal NNReal.sqrt
    simpa [S, K, CFC.sqrt] using h.eq
  have hleft : R * S = 1 := Matrix.inv_mul_of_invertible _
  have hright : S * R = 1 := Matrix.mul_inv_of_invertible _
  change R * A j = A j * R
  calc
    R * A j = R * A j * (S * R) := by rw [hright, Matrix.mul_one]
    _ = R * (A j * S) * R := by noncomm_ring
    _ = R * (S * A j) * R := by rw [hSA]
    _ = (R * S) * A j * R := by noncomm_ring
    _ = A j * R := by rw [hleft, Matrix.one_mul]

/-- The real central-Casimir normalization is symmetric. -/
theorem centralCasimirInvSqrtScale_transpose
    {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X ℝ) :
    (centralCasimirInvSqrtScale A).transpose =
      centralCasimirInvSqrtScale A := by
  classical
  rw [centralCasimirInvSqrtScale, Matrix.transpose_nonsing_inv,
    matrixSqrt_transpose]

/-- A symmetric family with central positive-definite quadratic Casimir becomes
a self-adjoint Parseval family after inverse square-root normalization. -/
theorem centralCasimir_scaled_transpose_mul_sum
    {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X ℝ)
    (hsymm : ∀ j, (A j).transpose = A j)
    (hpos : (∑ j, A j * A j).PosDef)
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k)) :
    ∑ j,
      (centralCasimirInvSqrtScale A * A j).transpose *
        (centralCasimirInvSqrtScale A * A j) = 1 := by
  classical
  let K : Matrix X X ℝ := ∑ k, A k * A k
  let R : Matrix X X ℝ := centralCasimirInvSqrtScale A
  have hKunit : IsUnit K := hpos.isUnit
  letI : Invertible K :=
    Matrix.invertibleOfIsUnitDet K (K.isUnit_iff_isUnit_det.mp hKunit)
  have hRtranspose : R.transpose = R :=
    centralCasimirInvSqrtScale_transpose A
  have hRA : ∀ j, R * A j = A j * R :=
    centralCasimirInvSqrtScale_commutes A hpos hcentral
  have hR2 : R * R = K⁻¹ := by
    dsimp [R, centralCasimirInvSqrtScale]
    exact (matrix_inv_eq_sqrt_inv_mul K hpos).symm
  calc
    (∑ j, (R * A j).transpose * (R * A j)) =
        ∑ j, R * R * (A j * A j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Matrix.transpose_mul, hsymm j, hRtranspose]
          calc
            (A j * R) * (R * A j) =
                (A j * R) * (A j * R) := by rw [hRA j]
            _ = (R * A j) * (R * A j) := by rw [← hRA j]
            _ = R * (A j * R) * A j := by noncomm_ring
            _ = R * (R * A j) * A j := by rw [← hRA j]
            _ = R * R * (A j * A j) := by noncomm_ring
    _ = R * R * (∑ j, A j * A j) := by
          rw [Matrix.mul_sum]
    _ = K⁻¹ * K := by rw [hR2]
    _ = 1 := Matrix.inv_mul_of_invertible _

/-- Central positive-definite Casimir is an exact Hall certificate: every real
subspace has at least its own dimension after applying all generators. -/
theorem centralCasimirMatrixFamily_subspace_finrank
    {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X ℝ)
    (hsymm : ∀ j, (A j).transpose = A j)
    (hpos : (∑ j, A j * A j).PosDef)
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k))
    (U V : Submodule ℝ (EuclideanSpace ℝ X))
    (hUV : ∀ j x, x ∈ U → (A j).toEuclideanLin x ∈ V) :
    Module.finrank ℝ U ≤ Module.finrank ℝ V := by
  classical
  let Rm : Matrix X X ℝ := centralCasimirInvSqrtScale A
  let B : J → Matrix X X ℝ := fun j => Rm * A j
  have hBsum : ∑ j, (B j).transpose * B j = 1 := by
    simpa [B, Rm] using
      centralCasimir_scaled_transpose_mul_sum A hsymm hpos hcentral
  have hBsymm : ∀ j, (B j).transpose = B j := by
    intro j
    dsimp [B]
    rw [Matrix.transpose_mul, hsymm j,
      centralCasimirInvSqrtScale_transpose,
      centralCasimirInvSqrtScale_commutes A hpos hcentral]
  let K : Matrix X X ℝ := ∑ j, A j * A j
  let S : Matrix X X ℝ := CFC.sqrt K
  have hSunit : IsUnit S :=
    (CFC.isUnit_sqrt_iff K hpos.posSemidef.nonneg).mpr hpos.isUnit
  have hRunit : IsUnit Rm := by
    dsimp [Rm, centralCasimirInvSqrtScale, S, K]
    exact Matrix.isUnit_nonsing_inv_iff.mpr hSunit
  have hRinj : Function.Injective Rm.toEuclideanLin := by
    intro x y hxy
    have hmul : Rm.mulVec x.ofLp = Rm.mulVec y.ofLp :=
      congrArg (fun z => z.ofLp) hxy
    have hcoord : x.ofLp = y.ofLp :=
      Matrix.mulVec_injective_of_isUnit hRunit hmul
    have := congrArg (WithLp.toLp 2) hcoord
    simpa using this
  have hRsurj : Function.Surjective Rm.toEuclideanLin :=
    LinearMap.injective_iff_surjective.mp hRinj
  let R : EuclideanSpace ℝ X ≃ₗ[ℝ] EuclideanSpace ℝ X :=
    LinearEquiv.ofBijective Rm.toEuclideanLin ⟨hRinj, hRsurj⟩
  have hRmap : R.toLinearMap = Rm.toEuclideanLin := by
    rfl
  let T : J → EuclideanSpace ℝ X →ₗ[ℝ] EuclideanSpace ℝ X :=
    fun j => (B j).toEuclideanLin
  have hTsymm : ∀ j, (T j).IsSymmetric := by
    intro j
    have hAdj : (T j).adjoint = T j := by
      dsimp [T]
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        Matrix.conjTranspose_eq_transpose_of_trivial, hBsymm]
    intro x y
    calc
      inner ℝ (T j x) y = inner ℝ x ((T j).adjoint y) :=
        (LinearMap.adjoint_inner_right (T j) x y).symm
      _ = inner ℝ x (T j y) := by rw [hAdj]
  have hTparseval : ∀ x, ∑ j, ‖T j x‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    exact matrixFamily_energy_of_sum_transpose_mul_eq_one B hBsum x
  let BV : Submodule ℝ (EuclideanSpace ℝ X) :=
    V.map R.toLinearMap
  have hTBV : ∀ j x, x ∈ U → T j x ∈ BV := by
    intro j x hx
    refine ⟨(A j).toEuclideanLin x, hUV j x hx, ?_⟩
    rw [hRmap]
    ext
    simp [T, B, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have hscaled := selfAdjointParsevalFamily_subspace_finrank
    T hTsymm hTparseval U BV hTBV
  have hBVfin : Module.finrank ℝ BV = Module.finrank ℝ V := by
    simpa [BV] using LinearEquiv.finrank_map_eq R V
  rw [hBVfin] at hscaled
  exact hscaled

end


end GaloisForLFunctions.HTGeometry
