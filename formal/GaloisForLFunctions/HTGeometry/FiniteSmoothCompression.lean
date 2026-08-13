import GaloisForLFunctions.HTGeometry.BoundedPerturbedCompactResolvent
import GaloisForLFunctions.RHTower.LeastSquaresProjection

/-!
# Finite smooth compression of a self-adjoint operator

Let `T` be a densely defined self-adjoint operator and let `v` be a finite packet whose vectors
belong to `T.domain`.  If `P` is the orthogonal projection onto their span and `Q = 1-P`, then
`Q T Q` on `T.domain` is an explicit bounded self-adjoint perturbation of `T`:

`Q T Q = T - T P - (T P)† + P T P`.

The domain membership is encoded in the type of `v`; no smoothness premise is postulated.  The
finite-dimensional restriction makes `T P` bounded.  This yields exact self-adjointness and,
when `T` has compact resolvent at `i`, exact compact resolvent for the compression.  It supplies
the functional-analytic core of Connes--Consani's finite-rank Dirac compression.
-/

open Module Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Span of a finite packet already typed as vectors in the operator domain. -/
def smoothPacketSpan (T : H →ₗ.[ℂ] H) {k : ℕ} (v : Fin k → T.domain) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun i => (v i : H))

omit [CompleteSpace H] in theorem smoothPacketSpan_le_domain
    (T : H →ₗ.[ℂ] H) {k : ℕ} (v : Fin k → T.domain) :
    smoothPacketSpan T v ≤ T.domain := by
  rw [smoothPacketSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (v i).property

/-- Orthogonal projection onto a finite smooth packet. -/
noncomputable def smoothPacketProjection (T : H →ₗ.[ℂ] H) {k : ℕ}
    (v : Fin k → T.domain) : H →L[ℂ] H := by
  letI : (smoothPacketSpan T v).HasOrthogonalProjection := by
    rw [smoothPacketSpan]
    exact RHTower.hasOrthogonalProjection_span (𝕜 := ℂ) (fun i => (v i : H))
  exact (smoothPacketSpan T v).starProjection

omit [CompleteSpace H] in
/-- Projection onto the smooth packet lands back in the operator domain. -/
theorem smoothPacketProjection_mem_domain
    (T : H →ₗ.[ℂ] H) {k : ℕ}
    (v : Fin k → T.domain) (x : H) :
    smoothPacketProjection T v x ∈ T.domain := by
  apply smoothPacketSpan_le_domain T v
  letI : (smoothPacketSpan T v).HasOrthogonalProjection := by
    rw [smoothPacketSpan]
    exact RHTower.hasOrthogonalProjection_span (𝕜 := ℂ) (fun i => (v i : H))
  exact (smoothPacketSpan T v).orthogonalProjectionOnto x |>.property

theorem smoothPacketProjection_isSelfAdjoint (T : H →ₗ.[ℂ] H) {k : ℕ}
    (v : Fin k → T.domain) : IsSelfAdjoint (smoothPacketProjection T v) := by
  letI : (smoothPacketSpan T v).HasOrthogonalProjection := by
    rw [smoothPacketSpan]
    exact RHTower.hasOrthogonalProjection_span (𝕜 := ℂ) (fun i => (v i : H))
  exact isSelfAdjoint_starProjection (smoothPacketSpan T v)

/-- Inclusion of the finite smooth span into the graph domain. -/
def smoothPacketSpanToDomain (T : H →ₗ.[ℂ] H) {k : ℕ} (v : Fin k → T.domain) :
    smoothPacketSpan T v →ₗ[ℂ] T.domain where
  toFun x := ⟨(x : H), smoothPacketSpan_le_domain T v x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction of `T` to the finite smooth span, automatically bounded by finite dimension. -/
noncomputable def smoothPacketDiracRestriction (T : H →ₗ.[ℂ] H) {k : ℕ}
    (v : Fin k → T.domain) : smoothPacketSpan T v →L[ℂ] H := by
  letI : FiniteDimensional ℂ (smoothPacketSpan T v) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range fun i => (v i : H))
  exact LinearMap.toContinuousLinearMap (T.toFun.comp (smoothPacketSpanToDomain T v))

/-- The bounded finite-rank operator `T P`. -/
noncomputable def smoothPacketTP (T : H →ₗ.[ℂ] H) {k : ℕ}
    (v : Fin k → T.domain) : H →L[ℂ] H := by
  letI : (smoothPacketSpan T v).HasOrthogonalProjection := by
    rw [smoothPacketSpan]
    exact RHTower.hasOrthogonalProjection_span (𝕜 := ℂ) (fun i => (v i : H))
  exact (smoothPacketDiracRestriction T v).comp
    (smoothPacketSpan T v).orthogonalProjectionOnto

omit [CompleteSpace H] in
theorem smoothPacketTP_apply (T : H →ₗ.[ℂ] H) {k : ℕ}
    (v : Fin k → T.domain) (x : H) :
    smoothPacketTP T v x =
      T ⟨smoothPacketProjection T v x, smoothPacketProjection_mem_domain T v x⟩ := by
  apply congrArg T
  apply Subtype.ext
  rfl

/-- A self-adjoint partial operator is its own formal adjoint on its domain. -/
theorem selfAdjointPMap_isFormalAdjoint (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    T.IsFormalAdjoint T := by
  have hle : T ≤ T.adjoint := le_of_eq hT.symm
  intro x y
  let xAdj : T.adjoint.domain := ⟨(x : H), hle.1 x.property⟩
  have hxApply : T x = T.adjoint xAdj := hle.2 rfl
  rw [hxApply]
  exact LinearPMap.adjoint_isFormalAdjoint hT.dense_domain xAdj y

/-- On the original domain, `(TP)†` agrees exactly with `PT`. -/
theorem smoothPacketTP_adjoint_apply (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T)
    {k : ℕ} (v : Fin k → T.domain) (x : T.domain) :
    (smoothPacketTP T v).adjoint (x : H) = smoothPacketProjection T v (T x) := by
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [smoothPacketTP_apply]
  have hformal := selfAdjointPMap_isFormalAdjoint T hT
  rw [← hformal x ⟨smoothPacketProjection T v y, smoothPacketProjection_mem_domain T v y⟩]
  have hPself := smoothPacketProjection_isSelfAdjoint T v
  rw [← ContinuousLinearMap.adjoint_inner_left, hPself.adjoint_eq]

/-- Bounded perturbation whose sum with `T` is the finite compression `Q T Q`. -/
def smoothPacketCompressionPerturbation (T : H →ₗ.[ℂ] H) {k : ℕ}
    (v : Fin k → T.domain) : H →L[ℂ] H :=
  -(smoothPacketTP T v) - (smoothPacketTP T v).adjoint +
    (smoothPacketProjection T v).comp (smoothPacketTP T v)

theorem smoothPacketProjection_comp_TP_isSelfAdjoint
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) {k : ℕ} (v : Fin k → T.domain) :
    IsSelfAdjoint ((smoothPacketProjection T v).comp (smoothPacketTP T v)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [ContinuousLinearMap.adjoint_comp]
  have hPself := smoothPacketProjection_isSelfAdjoint T v
  rw [hPself.adjoint_eq]
  ext x
  let Px : T.domain :=
    ⟨smoothPacketProjection T v x, smoothPacketProjection_mem_domain T v x⟩
  change (smoothPacketTP T v).adjoint (smoothPacketProjection T v x) =
    smoothPacketProjection T v (smoothPacketTP T v x)
  rw [smoothPacketTP_adjoint_apply T hT v Px, smoothPacketTP_apply]

theorem smoothPacketCompressionPerturbation_isSelfAdjoint
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) {k : ℕ} (v : Fin k → T.domain) :
    IsSelfAdjoint (smoothPacketCompressionPerturbation T v) := by
  apply IsSelfAdjoint.add
  · simpa [ContinuousLinearMap.star_eq_adjoint, sub_eq_add_neg, add_comm] using
      (IsSelfAdjoint.add_star_self (smoothPacketTP T v)).neg
  · exact smoothPacketProjection_comp_TP_isSelfAdjoint T hT v

/-- Exact finite smooth compression, represented as a bounded shift on the original domain. -/
def smoothPacketCompressedOperator (T : H →ₗ.[ℂ] H) {k : ℕ}
    (v : Fin k → T.domain) : H →ₗ.[ℂ] H :=
  boundedShift T (smoothPacketCompressionPerturbation T v)

/-- The bounded-shift construction is literally `Q T Q`, with `Q = 1-P`. -/
theorem smoothPacketCompressedOperator_apply
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) {k : ℕ}
    (v : Fin k → T.domain) (x : (smoothPacketCompressedOperator T v).domain) :
    smoothPacketCompressedOperator T v x =
      (1 - smoothPacketProjection T v)
        (T ⟨(1 - smoothPacketProjection T v) (x : H), by
          have hx : (x : H) ∈ T.domain := x.property
          exact T.domain.sub_mem hx (smoothPacketProjection_mem_domain T v x)⟩) := by
  change boundedShift T (smoothPacketCompressionPerturbation T v) x = _
  rw [boundedShift_apply]
  let xT : T.domain := ⟨(x : H), x.property⟩
  let Px : T.domain :=
    ⟨smoothPacketProjection T v x, smoothPacketProjection_mem_domain T v x⟩
  let Qx : T.domain :=
    ⟨(1 - smoothPacketProjection T v) (x : H), by
      change (x : H) - smoothPacketProjection T v x ∈ T.domain
      exact T.domain.sub_mem xT.property Px.property⟩
  have hAdj := smoothPacketTP_adjoint_apply T hT v xT
  change T xT + ((-smoothPacketTP T v - (smoothPacketTP T v).adjoint +
    (smoothPacketProjection T v).comp (smoothPacketTP T v)) (x : H)) = _
  simp only [_root_.add_apply, _root_.sub_apply, _root_.neg_apply,
    ContinuousLinearMap.comp_apply]
  rw [smoothPacketTP_apply, hAdj]
  change T xT + (-T Px - smoothPacketProjection T v (T xT) +
    smoothPacketProjection T v (T Px)) =
      (1 - smoothPacketProjection T v) (T Qx)
  have hQsub : (1 - smoothPacketProjection T v) (x : H) = (x : H) -
      smoothPacketProjection T v x := by rfl
  have hdomainEq : Qx = xT - Px := by
    apply Subtype.ext
    exact hQsub
  rw [hdomainEq]
  have hTsub : T (xT - Px) = T xT - T Px := T.toFun.map_sub xT Px
  rw [hTsub]
  change T xT + (-T Px - smoothPacketProjection T v (T xT) +
    smoothPacketProjection T v (T Px)) =
      T xT - T Px - smoothPacketProjection T v (T xT - T Px)
  rw [map_sub]
  abel

/-- Finite smooth compression preserves self-adjointness. -/
theorem smoothPacketCompressedOperator_isSelfAdjoint
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) {k : ℕ} (v : Fin k → T.domain) :
    IsSelfAdjoint (smoothPacketCompressedOperator T v) :=
  boundedShift_isSelfAdjoint T (smoothPacketCompressionPerturbation T v) hT
    (smoothPacketCompressionPerturbation_isSelfAdjoint T hT v)

/-- Finite smooth compression preserves compact resolvent at `i`. -/
theorem smoothPacketCompressedOperator_hasCompactResolventAt_I
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T)
    (hres : LinearPMap.HasCompactResolventAt T Complex.I)
    {k : ℕ} (v : Fin k → T.domain) :
    LinearPMap.HasCompactResolventAt (smoothPacketCompressedOperator T v) Complex.I :=
  boundedShift_hasCompactResolventAt_I T (smoothPacketCompressionPerturbation T v) hT
    (smoothPacketCompressionPerturbation_isSelfAdjoint T hT v) hres

omit [CompleteSpace H] in
/-- Projection onto a finite smooth packet fixes exactly its span. -/
theorem smoothPacketProjection_eq_self_iff
    (T : H →ₗ.[ℂ] H) {k : ℕ} (v : Fin k → T.domain) (x : H) :
    smoothPacketProjection T v x = x ↔ x ∈ smoothPacketSpan T v := by
  letI : (smoothPacketSpan T v).HasOrthogonalProjection := by
    rw [smoothPacketSpan]
    exact RHTower.hasOrthogonalProjection_span (𝕜 := ℂ) (fun i => (v i : H))
  exact Submodule.starProjection_eq_self_iff

omit [CompleteSpace H] in
theorem one_sub_smoothPacketProjection_apply_eq_zero_iff
    (T : H →ₗ.[ℂ] H) {k : ℕ} (v : Fin k → T.domain) (x : H) :
    (1 - smoothPacketProjection T v) x = 0 ↔ x ∈ smoothPacketSpan T v := by
  change x - smoothPacketProjection T v x = 0 ↔ _
  rw [sub_eq_zero, eq_comm, smoothPacketProjection_eq_self_iff]

/-- **Exact extra-kernel classification.**  A vector lies in the kernel of `Q T Q` exactly when
the image under `T` of its `Q`-component lands back in the excised finite packet.  This is the
missing correction to the source's unsupported claim that compression raises nullity by exactly
the projection rank. -/
theorem smoothPacketCompressedOperator_apply_eq_zero_iff
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) {k : ℕ}
    (v : Fin k → T.domain) (x : (smoothPacketCompressedOperator T v).domain) :
    smoothPacketCompressedOperator T v x = 0 ↔
      T ⟨(1 - smoothPacketProjection T v) (x : H), by
        have hx : (x : H) ∈ T.domain := x.property
        exact T.domain.sub_mem hx (smoothPacketProjection_mem_domain T v x)⟩ ∈
        smoothPacketSpan T v := by
  rw [smoothPacketCompressedOperator_apply T hT v x,
    one_sub_smoothPacketProjection_apply_eq_zero_iff]

/-- Every vector in the excised finite packet is genuinely killed by the compression. -/
theorem smoothPacketCompressedOperator_projection_eq_zero
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) {k : ℕ}
    (v : Fin k → T.domain) (x : H) :
    smoothPacketCompressedOperator T v
      ⟨smoothPacketProjection T v x, smoothPacketProjection_mem_domain T v x⟩ = 0 := by
  let px : (smoothPacketCompressedOperator T v).domain :=
    ⟨smoothPacketProjection T v x, smoothPacketProjection_mem_domain T v x⟩
  rw [smoothPacketCompressedOperator_apply_eq_zero_iff T hT v px]
  have hPmem : smoothPacketProjection T v x ∈ smoothPacketSpan T v := by
    letI : (smoothPacketSpan T v).HasOrthogonalProjection := by
      rw [smoothPacketSpan]
      exact RHTower.hasOrthogonalProjection_span (𝕜 := ℂ) (fun i => (v i : H))
    exact (smoothPacketSpan T v).orthogonalProjectionOnto x |>.property
  have hPid : smoothPacketProjection T v (smoothPacketProjection T v x) =
      smoothPacketProjection T v x :=
    (smoothPacketProjection_eq_self_iff T v _).2 hPmem
  have hQzero : (1 - smoothPacketProjection T v) (smoothPacketProjection T v x) = 0 := by
    change smoothPacketProjection T v x -
      smoothPacketProjection T v (smoothPacketProjection T v x) = 0
    rw [hPid, sub_self]
  let qpx : T.domain :=
    ⟨(1 - smoothPacketProjection T v) (smoothPacketProjection T v x), by
      exact T.domain.sub_mem (smoothPacketProjection_mem_domain T v x)
        (smoothPacketProjection_mem_domain T v (smoothPacketProjection T v x))⟩
  change T qpx ∈ smoothPacketSpan T v
  have hqpx : qpx = 0 := Subtype.ext hQzero
  rw [hqpx, LinearPMap.map_zero]
  exact Submodule.zero_mem _

end

end GaloisForLFunctions.HTGeometry
