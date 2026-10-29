import GaloisForLFunctions.HTGeometry.GaussianLatticeTheta
import GaloisForLFunctions.HTGeometry.DualZLatticeCovolume

/-!
# Gaussian theta on intrinsic dual lattices

An invertible Euclidean map parametrizes an actual integer lattice. Testing integer
pairings against the coordinate vectors identifies its intrinsic dual with the image
of the inverse adjoint. Reindexing Gaussian Poisson summation through these bijections
replaces integer parameters by lattice points and the determinant factor by inverse
covolume. The same identity applies to the integer span of every real basis.
-/

noncomputable section
open Module
open scoped Classical

namespace GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

variable {ι : Type*} [Fintype ι]
local notation "X" => ι → ℝ
local notation "Z" => ι → ℤ
local notation "E" => EuclideanSpace ℝ ι

/-- Coordinatewise integer inclusion as an integer-linear map. -/
def integerPointLinearMap : Z →ₗ[ℤ] X where
  toFun := integerPoint
  map_add' n m := by
    funext i
    exact Int.cast_add (n i) (m i)
  map_smul' m n := by
    funext i
    simp only [integerPoint, Pi.smul_apply, RingHom.id_apply, zsmul_eq_mul, Int.cast_mul]
    norm_cast

/-- A Euclidean linear equivalence expressed in ordinary real coordinates. -/
def latticeCoordinateEquiv (B : E ≃L[ℝ] E) : X ≃ₗ[ℝ] X :=
  (WithLp.linearEquiv 2 ℝ X).symm.trans
    (B.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ X))

/-- Integer coordinates mapped into the ambient real coordinate space. -/
def coordinateLatticeMap (B : E ≃L[ℝ] E) : Z →ₗ[ℤ] X :=
  ((latticeCoordinateEquiv B).toLinearMap.restrictScalars ℤ).comp integerPointLinearMap

/-- The actual image of the integer lattice under an invertible Euclidean map. -/
def coordinateLattice (B : E ≃L[ℝ] E) : Submodule ℤ X :=
  LinearMap.range (coordinateLatticeMap B)

omit [Fintype ι] in
theorem coordinateLatticeMap_apply (B : E ≃L[ℝ] E) (n : Z) :
    coordinateLatticeMap B n = (B (euclideanIntegerPoint n)).ofLp := rfl

omit [Fintype ι] in
theorem mem_coordinateLattice (B : E ≃L[ℝ] E) {x : X} :
    x ∈ coordinateLattice B ↔ ∃ n : Z, (B (euclideanIntegerPoint n)).ofLp = x := Iff.rfl

omit [Fintype ι] in
theorem coordinateLatticeMap_injective (B : E ≃L[ℝ] E) :
    Function.Injective (coordinateLatticeMap B) := by
  intro n m h
  have h' : integerPoint n = integerPoint m := (latticeCoordinateEquiv B).injective h
  funext i
  exact Int.cast_injective (congrFun h' i)

theorem coordinatePair_eq_inner (x y : X) :
    DualZLattice.pair x y = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
  simp only [DualZLattice.pair, PiLp.inner_apply, Real.inner_apply]

theorem coordinateLattice_pair_eq_adjoint (B : E ≃L[ℝ] E) (n : Z) (y : X) :
    DualZLattice.pair (coordinateLatticeMap B n) y =
      inner ℝ (euclideanIntegerPoint n)
        (ContinuousLinearMap.adjoint B.toContinuousLinearMap (WithLp.toLp 2 y)) := by
  rw [coordinatePair_eq_inner]
  change inner ℝ (B (euclideanIntegerPoint n)) (WithLp.toLp 2 y) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem integerPoint_pair_inverseAdjoint (B : E ≃L[ℝ] E) (n m : Z) :
    DualZLattice.pair (coordinateLatticeMap B n)
      (coordinateLatticeMap (inverseAdjointEquiv B) m) = (∑ i, n i * m i : ℤ) := by
  rw [coordinatePair_eq_inner]
  change inner ℝ (B (euclideanIntegerPoint n))
    (inverseAdjointEquiv B (euclideanIntegerPoint m)) = _
  rw [inverseAdjointEquiv_apply, inverseAdjoint, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (B.symm (B (euclideanIntegerPoint n))) (euclideanIntegerPoint m) = _
  rw [B.symm_apply_apply]
  simp only [euclideanIntegerPoint, integerPoint, PiLp.inner_apply, Real.inner_apply,
    Int.cast_sum, Int.cast_mul]

/-- Integral pairings force the adjoint coordinates to be integers. -/
theorem mem_dual_coordinateLattice (B : E ≃L[ℝ] E) {y : X} :
    y ∈ DualZLattice.dual (coordinateLattice B) ↔
      ∃ m : Z, (inverseAdjointEquiv B (euclideanIntegerPoint m)).ofLp = y := by
  classical
  constructor
  · intro hy
    have hcoords : ∀ i, ∃ m : ℤ,
        (ContinuousLinearMap.adjoint B.toContinuousLinearMap (WithLp.toLp 2 y)) i = m := by
      intro i
      obtain ⟨m, hm⟩ := hy (coordinateLatticeMap B (Pi.single i 1)) ⟨Pi.single i 1, rfl⟩
      rw [coordinateLattice_pair_eq_adjoint] at hm
      refine ⟨m, ?_⟩
      simpa [euclideanIntegerPoint, integerPoint, PiLp.inner_apply, Real.inner_apply,
        Pi.single_apply] using hm
    choose m hm using hcoords
    have heq : (inverseAdjointEquiv B).symm (WithLp.toLp 2 y) =
        euclideanIntegerPoint m := by
      apply (WithLp.linearEquiv 2 ℝ X).injective
      funext i
      exact hm i
    refine ⟨m, ?_⟩
    have h := (inverseAdjointEquiv B).apply_symm_apply (WithLp.toLp 2 y)
    rw [heq] at h
    exact congrArg (fun z : E => z.ofLp) h
  · rintro ⟨m, rfl⟩ x hx
    rcases (mem_coordinateLattice B).mp hx with ⟨n, rfl⟩
    exact ⟨∑ i, n i * m i, integerPoint_pair_inverseAdjoint B n m⟩

theorem dual_coordinateLattice (B : E ≃L[ℝ] E) :
    DualZLattice.dual (coordinateLattice B) = coordinateLattice (inverseAdjointEquiv B) := by
  ext y
  exact (mem_dual_coordinateLattice B).trans (mem_coordinateLattice (inverseAdjointEquiv B)).symm

theorem integerPoint_eq_sum (n : Z) :
    integerPoint n = ∑ i, n i • (Pi.basisFun ℝ ι) i := by
  classical
  funext j
  simp [integerPoint, Pi.basisFun_apply, Pi.single_apply]

/-- Images of the coordinate basis generate exactly the parametrized integer lattice. -/
theorem coordinateLattice_eq_span (B : E ≃L[ℝ] E) :
    coordinateLattice B = Submodule.span ℤ
      (Set.range ((Pi.basisFun ℝ ι).map (latticeCoordinateEquiv B))) := by
  classical
  apply le_antisymm
  · rintro x ⟨n, rfl⟩
    have h : coordinateLatticeMap B n =
        ∑ i, n i • ((Pi.basisFun ℝ ι).map (latticeCoordinateEquiv B)) i := by
      change latticeCoordinateEquiv B (integerPoint n) = _
      rw [integerPoint_eq_sum, map_sum]
      simp only [map_zsmul, Basis.map_apply]
    rw [h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    change latticeCoordinateEquiv B (integerPoint (Pi.single i 1)) =
      latticeCoordinateEquiv B ((Pi.basisFun ℝ ι) i)
    congr 1
    funext j
    simp [integerPoint, Pi.basisFun_apply, Pi.single_apply]

omit [Fintype ι] in
theorem det_latticeCoordinateEquiv (B : E ≃L[ℝ] E) :
    LinearMap.det (latticeCoordinateEquiv B : X →ₗ[ℝ] X) =
      LinearMap.det (B : E →ₗ[ℝ] E) := by
  exact LinearMap.det_conj (B : E →ₗ[ℝ] E) (WithLp.linearEquiv 2 ℝ X)

/-- The covolume of the actual lattice is the absolute determinant of its parametrization. -/
theorem covolume_coordinateLattice (B : E ≃L[ℝ] E) :
    ZLattice.covolume (coordinateLattice B) = |LinearMap.det (B : E →ₗ[ℝ] E)| := by
  classical
  have hd : (Pi.basisFun ℝ ι).det
      ⇑((Pi.basisFun ℝ ι).map (latticeCoordinateEquiv B)) =
        LinearMap.det (latticeCoordinateEquiv B : X →ₗ[ℝ] X) := by
    have h := (Pi.basisFun ℝ ι).det_comp
      (latticeCoordinateEquiv B).toLinearMap (Pi.basisFun ℝ ι)
    rw [Basis.det_self, mul_one] at h
    rw [Basis.coe_map]
    exact h
  rw [coordinateLattice_eq_span, DualZLattice.covolume_span_eq_abs_det,
    ← Pi.basisFun_det_apply, hd, det_latticeCoordinateEquiv]

theorem latticeScale_eq_inv_covolume (B : E ≃L[ℝ] E) :
    latticeScale B = (ZLattice.covolume (coordinateLattice B))⁻¹ := by
  rw [covolume_coordinateLattice]
  rfl

/-- The Euclidean linear map sending the coordinate basis to a prescribed real basis. -/
def basisLatticeEquiv (b : Basis ι ℝ X) : E ≃L[ℝ] E :=
  (((WithLp.linearEquiv 2 ℝ X).trans
    ((Pi.basisFun ℝ ι).equiv b (Equiv.refl ι))).trans
      (WithLp.linearEquiv 2 ℝ X).symm).toContinuousLinearEquiv

theorem coordinateLattice_basisLatticeEquiv (b : Basis ι ℝ X) :
    coordinateLattice (basisLatticeEquiv b) = Submodule.span ℤ (Set.range b) := by
  classical
  have he : latticeCoordinateEquiv (basisLatticeEquiv b) =
      (Pi.basisFun ℝ ι).equiv b (Equiv.refl ι) := by
    apply LinearEquiv.ext
    intro x
    rfl
  rw [coordinateLattice_eq_span, he, Basis.map_equiv, Equiv.refl_symm, Basis.reindex_refl]

/-- Integer parameters and actual lattice points are in bijection. -/
def latticePointEquiv (B : E ≃L[ℝ] E) : Z ≃ coordinateLattice B :=
  Equiv.ofInjective (coordinateLatticeMap B) (coordinateLatticeMap_injective B)

/-- Gaussian theta summed over actual points of a coordinate lattice. -/
def intrinsicLatticeTheta (L : Submodule ℤ X) (t : ℝ) : ℝ :=
  ∑' x : L, Real.exp (-(Real.pi * t) * ‖WithLp.toLp 2 (x : X)‖ ^ 2)

theorem coordinateLatticeTheta_eq (B : E ≃L[ℝ] E) (t : ℝ) :
    intrinsicLatticeTheta (coordinateLattice B) t = latticeTheta B t := by
  unfold intrinsicLatticeTheta latticeTheta gaussianLatticeSum
  exact ((latticePointEquiv B).tsum_eq _).symm

theorem summable_intrinsicLatticeTheta (B : E ≃L[ℝ] E) {t : ℝ} (ht : 0 < t) :
    Summable (fun x : coordinateLattice B =>
      Real.exp (-(Real.pi * t) * ‖WithLp.toLp 2 (x : X)‖ ^ 2)) := by
  apply (latticePointEquiv B).summable_iff.mp
  exact summable_gaussianLatticeSum B (mul_pos Real.pi_pos ht)

theorem summable_intrinsicLatticeTheta_basis (b : Basis ι ℝ X) {t : ℝ} (ht : 0 < t) :
    Summable (fun x : Submodule.span ℤ (Set.range b) =>
      Real.exp (-(Real.pi * t) * ‖WithLp.toLp 2 (x : X)‖ ^ 2)) := by
  have h := summable_intrinsicLatticeTheta (basisLatticeEquiv b) ht
  rw [coordinateLattice_basisLatticeEquiv] at h
  exact h

/-- Theta inversion with the intrinsic integer dual and the actual lattice covolume. -/
theorem intrinsicLatticeTheta_inversion (B : E ≃L[ℝ] E) {t : ℝ} (ht : 0 < t) :
    intrinsicLatticeTheta (coordinateLattice B) t =
      (ZLattice.covolume (coordinateLattice B))⁻¹ *
        t ^ (-((Module.finrank ℝ E : ℝ) / 2)) *
          intrinsicLatticeTheta (DualZLattice.dual (coordinateLattice B)) (1 / t) := by
  rw [dual_coordinateLattice, coordinateLatticeTheta_eq, coordinateLatticeTheta_eq,
    ← latticeScale_eq_inv_covolume]
  exact latticeTheta_inversion B ht

theorem intrinsicLatticeTheta_basis_inversion (b : Basis ι ℝ X) {t : ℝ} (ht : 0 < t) :
    intrinsicLatticeTheta (Submodule.span ℤ (Set.range b)) t =
      (ZLattice.covolume (Submodule.span ℤ (Set.range b)))⁻¹ *
        t ^ (-((Module.finrank ℝ E : ℝ) / 2)) *
          intrinsicLatticeTheta (DualZLattice.dual (Submodule.span ℤ (Set.range b))) (1 / t) := by
  simpa only [coordinateLattice_basisLatticeEquiv] using
    intrinsicLatticeTheta_inversion (basisLatticeEquiv b) ht

end GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
