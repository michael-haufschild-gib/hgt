import GaloisForLFunctions.HTGeometry.ReplicaReturnShellCoareaIncidenceLaw
import GaloisForLFunctions.HTGeometry.FullPauliCollectiveCasimir

/-!
# Replica projection incidence law

Orthogonal projection commutes exactly with finite Veronese replica lifting.
This file constructs the tensor functor of every finite-dimensional linear
operator, proves its composition and adjoint structure, and specializes it to
one-copy orthogonal projectors.

For any complete target family, the image of its occupied replica span under
the tensor projector is exactly the occupied span of the projected targets.
Consequently, label collisions and zero images are retained geometrically
rather than counted combinatorially, and projected occupied-image rank cannot
exceed original occupied-image rank.
-/

open scoped BigOperators Matrix ComplexConjugate
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Tensor lift of a finite-dimensional one-copy linear operator. -/
noncomputable def finiteTensorEuclideanMap
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    (A : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α) :
    EuclideanSpace ℂ (Fin r → α) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin r → α) := by
  classical
  let b := (EuclideanSpace.basisFun α ℂ).toBasis
  let br := (EuclideanSpace.basisFun (Fin r → α) ℂ).toBasis
  exact Matrix.toLin br br
    (finiteTensorLocalMatrix fun _ : Fin r => LinearMap.toMatrix b b A)

theorem finiteTensorEuclideanMap_toMatrix
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    (A : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α) :
    LinearMap.toMatrix
        (EuclideanSpace.basisFun (Fin r → α) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin r → α) ℂ).toBasis
        (finiteTensorEuclideanMap r A) =
      finiteTensorLocalMatrix fun _ : Fin r =>
        LinearMap.toMatrix
          (EuclideanSpace.basisFun α ℂ).toBasis
          (EuclideanSpace.basisFun α ℂ).toBasis A := by
  classical
  simp [finiteTensorEuclideanMap]

/-- Functoriality on a pure tensor: applying the tensor lift is exactly
replicating the one-copy image. -/
theorem finiteTensorEuclideanMap_pureTensor
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    (A : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α)
    (ψ : α → ℂ) :
    finiteTensorEuclideanMap r A
        (finitePureTensorPowerEuclidean r ψ) =
      finitePureTensorPowerEuclidean r
        (fun x => A (WithLp.toLp 2 ψ) x) := by
  classical
  let br := (EuclideanSpace.basisFun (Fin r → α) ℂ).toBasis
  apply br.repr.injective
  ext x
  rw [show finiteTensorEuclideanMap r A =
      Matrix.toLin br br
        (finiteTensorLocalMatrix fun _ : Fin r =>
          LinearMap.toMatrix
            (EuclideanSpace.basisFun α ℂ).toBasis
            (EuclideanSpace.basisFun α ℂ).toBasis A) by
      rfl]
  rw [Matrix.repr_toLin]
  simp only [br]
  let M := LinearMap.toMatrix
    (EuclideanSpace.basisFun α ℂ).toBasis
    (EuclideanSpace.basisFun α ℂ).toBasis A
  change (∑ y : Fin r → α,
      (∏ i, M (x i) (y i)) * ∏ i, ψ (y i)) =
    ∏ i, A (WithLp.toLp 2 ψ) (x i)
  simp_rw [← Finset.prod_mul_distrib]
  have hfactor := sum_pi_prod_complex
    (fun i (y : α) => M (x i) y * ψ y)
  rw [hfactor]
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only [M]
  have hmul := LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun α ℂ).toBasis
    (EuclideanSpace.basisFun α ℂ).toBasis A
    (WithLp.toLp 2 ψ)
  have hi' := congrFun hmul (x i)
  simpa [Matrix.mulVec, dotProduct, EuclideanSpace.basisFun_repr] using hi'

/-- Tensor lifting preserves composition exactly. -/
theorem finiteTensorEuclideanMap_comp
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    (A B : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α) :
    finiteTensorEuclideanMap r (A.comp B) =
      (finiteTensorEuclideanMap r A).comp
        (finiteTensorEuclideanMap r B) := by
  let br := (EuclideanSpace.basisFun (Fin r → α) ℂ).toBasis
  apply (LinearMap.toMatrix br br).injective
  rw [LinearMap.toMatrix_comp br br br]
  simp only [br, finiteTensorEuclideanMap_toMatrix]
  rw [LinearMap.toMatrix_comp
    (EuclideanSpace.basisFun α ℂ).toBasis
    (EuclideanSpace.basisFun α ℂ).toBasis
    (EuclideanSpace.basisFun α ℂ).toBasis,
    finiteTensorLocalMatrix_mul]

/-- Tensor lifting preserves Hilbert-space symmetry. -/
theorem finiteTensorEuclideanMap_isSymmetric
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    {A : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α}
    (hA : A.IsSymmetric) :
    (finiteTensorEuclideanMap r A).IsSymmetric := by
  let b := EuclideanSpace.basisFun α ℂ
  let br := EuclideanSpace.basisFun (Fin r → α) ℂ
  rw [← LinearMap.isHermitian_toMatrix_iff br]
  rw [finiteTensorEuclideanMap_toMatrix]
  have hM : (LinearMap.toMatrix b.toBasis b.toBasis A).IsHermitian :=
    (LinearMap.isHermitian_toMatrix_iff b).mpr hA
  rw [Matrix.IsHermitian, finiteTensorLocalMatrix_conjTranspose]
  congr 1
  funext i
  exact hM.eq

/-- Tensor lifting preserves idempotence. -/
theorem finiteTensorEuclideanMap_isIdempotentElem
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    {A : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α}
    (hA : IsIdempotentElem A) :
    IsIdempotentElem (finiteTensorEuclideanMap r A) := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp,
    ← finiteTensorEuclideanMap_comp]
  have hAA : A.comp A = A := by
    change A.comp A = A at hA
    exact hA
  rw [hAA]

/-- A symmetric one-copy projector lifts to a symmetric replica projector. -/
theorem finiteTensorEuclideanMap_isSymmetricProjection
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    {A : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α}
    (hAidem : IsIdempotentElem A) (hAsymm : A.IsSymmetric) :
    (finiteTensorEuclideanMap r A).IsSymmetricProjection :=
  ⟨finiteTensorEuclideanMap_isIdempotentElem r hAidem,
    finiteTensorEuclideanMap_isSymmetric r hAsymm⟩

/-- Exact image identity for an arbitrary finite-dimensional linear map. -/
theorem map_replicaTargetSpan_finiteTensorEuclideanMap
    {C α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (A : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α)
    (target : C → α → ℂ) :
    Submodule.map (finiteTensorEuclideanMap r A)
        (replicaTargetSpan r target) =
      replicaTargetSpan r
        (fun c x => A (WithLp.toLp 2 (target c)) x) := by
  unfold replicaTargetSpan
  rw [Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨u, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (finiteTensorEuclideanMap_pureTensor r A (target c)).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨finitePureTensorPowerEuclidean r (target c),
      Set.mem_range_self c, ?_⟩
    exact finiteTensorEuclideanMap_pureTensor r A (target c)

/-- Linear images cannot increase occupied replica-span rank. -/
theorem finrank_projectedReplicaTargetSpan_le
    {C α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (A : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α)
    (target : C → α → ℂ) :
    Module.finrank ℂ
        (replicaTargetSpan r
          (fun c x => A (WithLp.toLp 2 (target c)) x)) ≤
      Module.finrank ℂ (replicaTargetSpan r target) := by
  rw [← map_replicaTargetSpan_finiteTensorEuclideanMap r A target]
  exact Submodule.finrank_map_le _ _

/-- Coordinate family obtained by orthogonally projecting every target. -/
noncomputable def projectedReplicaTarget
    {C α : Type*} [Fintype α]
    (S : Submodule ℂ (EuclideanSpace ℂ α))
    (target : C → α → ℂ) : C → α → ℂ :=
  fun c x => S.starProjection (WithLp.toLp 2 (target c)) x

/-- Tensor lift of the one-copy orthogonal projector. -/
noncomputable def finiteTensorStarProjection
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ α)) :
    EuclideanSpace ℂ (Fin r → α) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin r → α) :=
  finiteTensorEuclideanMap r S.starProjection.toLinearMap

theorem finiteTensorStarProjection_isSymmetricProjection
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ α)) :
    (finiteTensorStarProjection r S).IsSymmetricProjection := by
  apply finiteTensorEuclideanMap_isSymmetricProjection
  · exact ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr
      S.isIdempotentElem_starProjection
  · exact S.starProjection_isSymmetric

/-- Tensor lift of an orthogonal projector is precisely the orthogonal
projector onto its tensor-image range. -/
theorem finiteTensorStarProjection_eq_range_starProjection
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ α)) :
    finiteTensorStarProjection r S =
      (LinearMap.range (finiteTensorStarProjection r S)).starProjection := by
  exact (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
    (finiteTensorStarProjection_isSymmetricProjection r S)).2

theorem finiteTensorStarProjection_pureTensor
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ α)) (ψ : α → ℂ) :
    finiteTensorStarProjection r S
        (finitePureTensorPowerEuclidean r ψ) =
      finitePureTensorPowerEuclidean r
        (fun x => S.starProjection (WithLp.toLp 2 ψ) x) := by
  exact finiteTensorEuclideanMap_pureTensor r
    S.starProjection.toLinearMap ψ

/-- A projected pure tensor is fixed by the tensor projector. -/
theorem finiteTensorStarProjection_projectedPureTensor
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ α)) (ψ : α → ℂ) :
    finiteTensorStarProjection r S
        (finitePureTensorPowerEuclidean r
          (fun x => S.starProjection (WithLp.toLp 2 ψ) x)) =
      finitePureTensorPowerEuclidean r
        (fun x => S.starProjection (WithLp.toLp 2 ψ) x) := by
  rw [finiteTensorStarProjection_pureTensor]
  congr 1
  funext x
  have hfixed :
      S.starProjection (S.starProjection (WithLp.toLp 2 ψ)) =
        S.starProjection (WithLp.toLp 2 ψ) :=
    S.starProjection_eq_self_iff.mpr
      (S.starProjection_apply_mem (WithLp.toLp 2 ψ))
  have hcoord :
      WithLp.toLp 2
          (fun x => S.starProjection (WithLp.toLp 2 ψ) x) =
        S.starProjection (WithLp.toLp 2 ψ) := by
    ext y
    rfl
  rw [hcoord, hfixed]

/-- Exact occupied-image identity: projection commutes with the complete
Veronese target span, including all label collisions. -/
theorem map_replicaTargetSpan_finiteTensorStarProjection
    {C α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ α))
    (target : C → α → ℂ) :
    Submodule.map (finiteTensorStarProjection r S)
        (replicaTargetSpan r target) =
      replicaTargetSpan r (projectedReplicaTarget S target) := by
  exact map_replicaTargetSpan_finiteTensorEuclideanMap r
    S.starProjection.toLinearMap target

/-- First simultaneous rank cap: projected occupied-image rank does not
exceed the original occupied-image rank. -/
theorem finrank_projectedReplicaTargetSpan_le_original
    {C α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ α))
    (target : C → α → ℂ) :
    Module.finrank ℂ
        (replicaTargetSpan r (projectedReplicaTarget S target)) ≤
      Module.finrank ℂ (replicaTargetSpan r target) := by
  exact finrank_projectedReplicaTargetSpan_le r
    S.starProjection.toLinearMap target

/-- Projecting both a target subspace and a source fixed by a symmetric
projector cannot decrease its captured projection mass. -/
theorem starProjectionMass_le_map_of_fixed_symmetricProjection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (P : E →ₗ[ℂ] E) (hP : P.IsSymmetricProjection)
    (U : Submodule ℂ E) (y : E) (hy : P y = y) :
    ‖U.starProjection y‖ ^ (2 : ℕ) ≤
      ‖(Submodule.map P U).starProjection y‖ ^ (2 : ℕ) := by
  let V := Submodule.map P U
  let u := U.starProjection y
  have hu : u ∈ U := U.starProjection_apply_mem y
  have hPu : P u ∈ V := ⟨u, hu, rfl⟩
  have hmin : ‖y - V.starProjection y‖ ≤ ‖y - P u‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le
      ⟨0, by rintro z ⟨v, rfl⟩; exact norm_nonneg _⟩
      (⟨P u, hPu⟩ : V)
  obtain ⟨hRange, hPeq⟩ :=
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hP
  letI := hRange
  have hcontract : ‖P (y - u)‖ ≤ ‖y - u‖ := by
    rw [hPeq]
    exact (LinearMap.range P).norm_starProjection_apply_le (y - u)
  have hresidual :
      ‖y - V.starProjection y‖ ≤ ‖y - U.starProjection y‖ := by
    calc
      ‖y - V.starProjection y‖ ≤ ‖y - P u‖ := hmin
      _ = ‖P (y - u)‖ := by rw [map_sub, hy]
      _ ≤ ‖y - u‖ := hcontract
      _ = ‖y - U.starProjection y‖ := rfl
  have hU := U.norm_sq_eq_add_norm_sq_starProjection y
  have hV := V.norm_sq_eq_add_norm_sq_starProjection y
  rw [U.starProjection_orthogonal_val] at hU
  rw [V.starProjection_orthogonal_val] at hV
  have hresidualSq :
      ‖y - V.starProjection y‖ ^ (2 : ℕ) ≤
        ‖y - U.starProjection y‖ ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hresidual 2
  nlinarith

/-- Projection before replicas cannot decrease complete occupied-image
incidence for a source already in the projected replica carrier. -/
theorem replicaTargetProjectionMass_projectedState_le
    {C α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ α))
    (target : C → α → ℂ) (ψ : α → ℂ) :
    replicaTargetProjectionMass r target
        (fun x => S.starProjection (WithLp.toLp 2 ψ) x) ≤
      replicaTargetProjectionMass r (projectedReplicaTarget S target)
        (fun x => S.starProjection (WithLp.toLp 2 ψ) x) := by
  unfold replicaTargetProjectionMass
  have hspan := map_replicaTargetSpan_finiteTensorStarProjection
    r S target
  have hmass := starProjectionMass_le_map_of_fixed_symmetricProjection
      (finiteTensorStarProjection r S)
      (finiteTensorStarProjection_isSymmetricProjection r S)
      (replicaTargetSpan r target)
      (finitePureTensorPowerEuclidean r
        (fun x => S.starProjection (WithLp.toLp 2 ψ) x))
      (finiteTensorStarProjection_projectedPureTensor r S ψ)
  simpa only [hspan, Submodule.starProjection_apply, Submodule.coe_norm]
    using hmass

/-- On the unit interval, the power map is `r`-Lipschitz. -/
theorem pow_sub_pow_le_nat_mul_sub
    (r : ℕ) {a b : ℝ} (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    a ^ r - b ^ r ≤ (r : ℝ) * (a - b) := by
  have ha0 : 0 ≤ a := hb0.trans hba
  induction r with
  | zero => simp
  | succ r ihr =>
      have hbr0 : 0 ≤ b ^ r := pow_nonneg hb0 r
      have har0 : 0 ≤ a ^ r := pow_nonneg ha0 r
      have hbr_le_har : b ^ r ≤ a ^ r :=
        pow_le_pow_left₀ hb0 hba r
      have har_le_one : a ^ r ≤ 1 := by
        simpa using pow_le_pow_left₀ ha0 ha1 r
      have hb_le_one : b ≤ 1 := hba.trans ha1
      have hsplit :
          a ^ (r + 1) - b ^ (r + 1) =
            a ^ r * (a - b) + b * (a ^ r - b ^ r) := by
        rw [pow_succ, pow_succ]
        ring
      rw [hsplit]
      have hfirst : a ^ r * (a - b) ≤ a - b := by
        nlinarith
      have hsecond : b * (a ^ r - b ^ r) ≤
          (r : ℝ) * (a - b) := by
        have hdiff0 : 0 ≤ a ^ r - b ^ r := sub_nonneg.mpr hbr_le_har
        have hbmul : b * (a ^ r - b ^ r) ≤ a ^ r - b ^ r := by
          nlinarith
        exact hbmul.trans ihr
      push_cast
      linarith

/-- Exact replica projection-defect identity.  Orthogonality removes all
cross terms, leaving a difference of one-copy retained-norm powers. -/
theorem norm_sq_pureTensor_sub_projected_eq_pow_sub_pow
    {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ α)) (ψ : α → ℂ) :
    ‖finitePureTensorPowerEuclidean r ψ -
        finitePureTensorPowerEuclidean r
          (fun x => S.starProjection (WithLp.toLp 2 ψ) x)‖ ^ (2 : ℕ) =
      (‖WithLp.toLp 2 ψ‖ ^ (2 : ℕ)) ^ r -
        (‖S.starProjection (WithLp.toLp 2 ψ)‖ ^ (2 : ℕ)) ^ r := by
  let P := finiteTensorStarProjection r S
  let C := LinearMap.range P
  let u := finitePureTensorPowerEuclidean r ψ
  let v := finitePureTensorPowerEuclidean r
    (fun x => S.starProjection (WithLp.toLp 2 ψ) x)
  have hCproj : C.starProjection u = v := by
    dsimp only [C, P, u, v]
    have hPeq := finiteTensorStarProjection_eq_range_starProjection r S
    have happ := congrArg
      (fun A => A (finitePureTensorPowerEuclidean r ψ)) hPeq
    exact happ.symm.trans
      (finiteTensorStarProjection_pureTensor r S ψ)
  have hpy := C.norm_sq_eq_add_norm_sq_starProjection u
  rw [C.starProjection_orthogonal_val, hCproj] at hpy
  have huNorm := norm_sq_finitePureTensorPowerEuclidean_eq_pow r ψ
  have hvNorm := norm_sq_finitePureTensorPowerEuclidean_eq_pow r
    (fun x => S.starProjection (WithLp.toLp 2 ψ) x)
  have hcoord :
      WithLp.toLp 2
          (fun x => S.starProjection (WithLp.toLp 2 ψ) x) =
        S.starProjection (WithLp.toLp 2 ψ) := by
    ext x
    rfl
  rw [huNorm, hvNorm, hcoord] at hpy
  dsimp only [u, v] at hpy
  linarith

/-- A one-copy orthogonal projection defect amplifies by at most the replica
order.  The bound is independent of ambient dimension and target count. -/
theorem norm_pureTensor_sub_projected_le_nat_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    {r : ℕ} (hr : 0 < r)
    (S : Submodule ℂ (EuclideanSpace ℂ α)) (ψ : α → ℂ)
    (hψ : ‖WithLp.toLp 2 ψ‖ ≤ 1) :
    ‖finitePureTensorPowerEuclidean r ψ -
        finitePureTensorPowerEuclidean r
          (fun x => S.starProjection (WithLp.toLp 2 ψ) x)‖ ≤
      (r : ℝ) *
        ‖WithLp.toLp 2 ψ - S.starProjection (WithLp.toLp 2 ψ)‖ := by
  let a := ‖WithLp.toLp 2 ψ‖ ^ (2 : ℕ)
  let b := ‖S.starProjection (WithLp.toLp 2 ψ)‖ ^ (2 : ℕ)
  have hb0 : 0 ≤ b := sq_nonneg _
  have hnormProj := S.norm_starProjection_apply_le (WithLp.toLp 2 ψ)
  have hba : b ≤ a := by
    exact pow_le_pow_left₀ (norm_nonneg _) hnormProj 2
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    nlinarith [norm_nonneg (WithLp.toLp 2 ψ)]
  have hpow := pow_sub_pow_le_nat_mul_sub r hb0 hba ha1
  have hone := S.norm_sq_eq_add_norm_sq_starProjection
    (WithLp.toLp 2 ψ)
  rw [S.starProjection_orthogonal_val] at hone
  have hrep := norm_sq_pureTensor_sub_projected_eq_pow_sub_pow
    r S ψ
  have hrepSq :
      ‖finitePureTensorPowerEuclidean r ψ -
          finitePureTensorPowerEuclidean r
            (fun x => S.starProjection (WithLp.toLp 2 ψ) x)‖ ^ (2 : ℕ) ≤
        (r : ℝ) *
          ‖WithLp.toLp 2 ψ - S.starProjection (WithLp.toLp 2 ψ)‖ ^ (2 : ℕ) := by
    rw [hrep]
    dsimp only [a, b] at hpow
    nlinarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsq :
      ‖finitePureTensorPowerEuclidean r ψ -
          finitePureTensorPowerEuclidean r
            (fun x => S.starProjection (WithLp.toLp 2 ψ) x)‖ ^ (2 : ℕ) ≤
        ((r : ℝ) *
          ‖WithLp.toLp 2 ψ - S.starProjection (WithLp.toLp 2 ψ)‖) ^ (2 : ℕ) := by
    rw [mul_pow]
    have hd0 : 0 ≤
        ‖WithLp.toLp 2 ψ - S.starProjection (WithLp.toLp 2 ψ)‖ ^ (2 : ℕ) :=
      sq_nonneg _
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by positivity) (norm_nonneg _))).mp hsq

/-- Replica lifting preserves the closed unit ball. -/
theorem norm_finitePureTensorPowerEuclidean_le_one
    {α : Type*} [Fintype α] (r : ℕ) (ψ : α → ℂ)
    (hψ : ‖WithLp.toLp 2 ψ‖ ≤ 1) :
    ‖finitePureTensorPowerEuclidean r ψ‖ ≤ 1 := by
  have hnorm := norm_sq_finitePureTensorPowerEuclidean_eq_pow r ψ
  have hbase : ‖WithLp.toLp 2 ψ‖ ^ (2 : ℕ) ≤ 1 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 ψ)]
  have hpow : (‖WithLp.toLp 2 ψ‖ ^ (2 : ℕ)) ^ r ≤ 1 := by
    simpa using pow_le_pow_left₀ (sq_nonneg _) hbase r
  rw [← sq_le_sq₀ (norm_nonneg _) zero_le_one]
  rw [hnorm]
  simpa using hpow

/-- Squared orthogonal-projection mass is `2`-Lipschitz on the Hilbert unit
ball. -/
theorem starProjectionMass_le_add_two_mul_norm_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U : Submodule ℂ E) (u v : E)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖U.starProjection u‖ ^ (2 : ℕ) ≤
      ‖U.starProjection v‖ ^ (2 : ℕ) + 2 * ‖u - v‖ := by
  let a := ‖U.starProjection u‖
  let b := ‖U.starProjection v‖
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have ha1 : a ≤ 1 := (U.norm_starProjection_apply_le u).trans hu
  have hb1 : b ≤ 1 := (U.norm_starProjection_apply_le v).trans hv
  have hpdist :
      ‖U.starProjection u - U.starProjection v‖ ≤ ‖u - v‖ := by
    rw [← map_sub]
    exact U.norm_starProjection_apply_le (u - v)
  have habs : |a - b| ≤ ‖u - v‖ := by
    exact (abs_norm_sub_norm_le (U.starProjection u)
      (U.starProjection v)).trans hpdist
  calc
    a ^ (2 : ℕ) ≤ b ^ (2 : ℕ) + |a ^ (2 : ℕ) - b ^ (2 : ℕ)| := by
      nlinarith [le_abs_self (a ^ (2 : ℕ) - b ^ (2 : ℕ))]
    _ = b ^ (2 : ℕ) + |a - b| * (a + b) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg ha0 hb0)]
      ring
    _ ≤ b ^ (2 : ℕ) + ‖u - v‖ * 2 := by
      gcongr
      linarith
    _ = b ^ (2 : ℕ) + 2 * ‖u - v‖ := by ring

/-- **Projection-before-replicas action law.**  Complete occupied-image
incidence changes by at most twice the replica-amplified one-copy projection
defect, paid once for the whole target image. -/
theorem replicaTargetProjectionMass_le_projected_add_defect
    {C α : Type*} [Fintype α] [DecidableEq α]
    {r : ℕ} (hr : 0 < r)
    (S : Submodule ℂ (EuclideanSpace ℂ α))
    (target : C → α → ℂ) (ψ : α → ℂ)
    (hψ : ‖WithLp.toLp 2 ψ‖ ≤ 1) :
    replicaTargetProjectionMass r target ψ ≤
      replicaTargetProjectionMass r (projectedReplicaTarget S target)
        (fun x => S.starProjection (WithLp.toLp 2 ψ) x) +
      2 * (r : ℝ) *
        ‖WithLp.toLp 2 ψ - S.starProjection (WithLp.toLp 2 ψ)‖ := by
  let projectedψ : α → ℂ :=
    fun x => S.starProjection (WithLp.toLp 2 ψ) x
  let u := finitePureTensorPowerEuclidean r ψ
  let v := finitePureTensorPowerEuclidean r projectedψ
  have hprojectedCoord :
      WithLp.toLp 2 projectedψ =
        S.starProjection (WithLp.toLp 2 ψ) := by
    ext x
    rfl
  have hprojectedOne : ‖WithLp.toLp 2 projectedψ‖ ≤ 1 := by
    rw [hprojectedCoord]
    exact (S.norm_starProjection_apply_le (WithLp.toLp 2 ψ)).trans hψ
  have hu : ‖u‖ ≤ 1 :=
    norm_finitePureTensorPowerEuclidean_le_one r ψ hψ
  have hv : ‖v‖ ≤ 1 :=
    norm_finitePureTensorPowerEuclidean_le_one r projectedψ hprojectedOne
  have hlip := starProjectionMass_le_add_two_mul_norm_sub
    (replicaTargetSpan r target) u v hu hv
  have hlip' :
      replicaTargetProjectionMass r target ψ ≤
        replicaTargetProjectionMass r target projectedψ + 2 * ‖u - v‖ := by
    simpa only [replicaTargetProjectionMass, Submodule.starProjection_apply,
      Submodule.coe_norm, u, v] using hlip
  have hdom := replicaTargetProjectionMass_projectedState_le
    r S target ψ
  have htensor := norm_pureTensor_sub_projected_le_nat_mul
    hr S ψ hψ
  calc
    replicaTargetProjectionMass r target ψ ≤
        replicaTargetProjectionMass r target projectedψ + 2 * ‖u - v‖ :=
      hlip'
    _ ≤ replicaTargetProjectionMass r (projectedReplicaTarget S target)
          projectedψ +
        2 * ((r : ℝ) *
          ‖WithLp.toLp 2 ψ - S.starProjection (WithLp.toLp 2 ψ)‖) := by
      apply add_le_add hdom
      apply mul_le_mul_of_nonneg_left
      · simpa only [u, v, projectedψ] using htensor
      · norm_num
    _ = replicaTargetProjectionMass r (projectedReplicaTarget S target)
          projectedψ +
        2 * (r : ℝ) *
          ‖WithLp.toLp 2 ψ - S.starProjection (WithLp.toLp 2 ψ)‖ := by
      ring

/-- Error-budget form of the complete projection-before-replicas law. -/
theorem replicaTargetProjectionMass_le_projected_add_error
    {C α : Type*} [Fintype α] [DecidableEq α]
    {r : ℕ} (hr : 0 < r)
    (S : Submodule ℂ (EuclideanSpace ℂ α))
    (target : C → α → ℂ) (ψ : α → ℂ)
    (hψ : ‖WithLp.toLp 2 ψ‖ ≤ 1)
    {η : ℝ}
    (hdefect :
      ‖WithLp.toLp 2 ψ - S.starProjection (WithLp.toLp 2 ψ)‖ ≤ η) :
    replicaTargetProjectionMass r target ψ ≤
      replicaTargetProjectionMass r (projectedReplicaTarget S target)
        (fun x => S.starProjection (WithLp.toLp 2 ψ) x) +
      2 * (r : ℝ) * η := by
  calc
    replicaTargetProjectionMass r target ψ ≤
        replicaTargetProjectionMass r (projectedReplicaTarget S target)
          (fun x => S.starProjection (WithLp.toLp 2 ψ) x) +
        2 * (r : ℝ) *
          ‖WithLp.toLp 2 ψ - S.starProjection (WithLp.toLp 2 ψ)‖ :=
      replicaTargetProjectionMass_le_projected_add_defect
        hr S target ψ hψ
    _ ≤ replicaTargetProjectionMass r (projectedReplicaTarget S target)
          (fun x => S.starProjection (WithLp.toLp 2 ψ) x) +
        2 * (r : ℝ) * η := by
      gcongr

end

end GaloisForLFunctions.HTGeometry
