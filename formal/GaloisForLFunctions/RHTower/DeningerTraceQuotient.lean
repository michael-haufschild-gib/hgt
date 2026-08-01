import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# The trace quotient isometry

A continuous linear map between Hilbert spaces which is norm preserving on the orthogonal
complement of its kernel induces an isometric isomorphism from the quotient by that kernel.  The
mechanism is the minimality of the orthogonal projection: the quotient norm is the distance to the
kernel, and that distance is attained at the projection, so the quotient norm is the norm of the
component orthogonal to the kernel, which the map preserves.

Together with the orthogonal complementation of the kernel this is the Dirichlet decomposition of
an energy space into its zero-trace part and the orthogonal minimal-energy part carrying the
boundary values.

* `deningerProjection_minimal` : the projection minimizes the distance to the subspace.
* `deningerQuotientNorm_eq` : the quotient norm is the norm of the orthogonal component.
* `deningerZeroTrace_isCompl` : the kernel and its orthogonal complement are complementary.
* `deningerTraceIsometry` : the orthogonal complement of the kernel is isometric to the target.
* `deningerTraceQuotientIsometry` : so is the quotient by the kernel.
-/

namespace RHTower

open scoped InnerProductSpace

section TraceQuotient

variable {E B : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]

variable (K : Submodule ℂ E) [K.HasOrthogonalProjection]

/-- **The orthogonal projection minimizes the distance to the subspace.**  The residual is
orthogonal to the subspace, so Pythagoras adds a nonnegative square to every other choice. -/
theorem deningerProjection_minimal (x : E) {k : E} (hk : k ∈ K) :
    ‖x - K.starProjection x‖ ≤ ‖x - k‖ := by
  have hmem : K.starProjection x - k ∈ K :=
    K.sub_mem (K.starProjection_apply_mem x) hk
  have horth : ⟪x - K.starProjection x, K.starProjection x - k⟫_ℂ = 0 :=
    Submodule.starProjection_inner_eq_zero (K := K) x _ hmem
  have hsplit : x - k = (x - K.starProjection x) + (K.starProjection x - k) := by
    abel
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (x - K.starProjection x) (K.starProjection x - k) horth
  rw [← hsplit] at hpy
  nlinarith [norm_nonneg (x - k), norm_nonneg (x - K.starProjection x),
    sq_nonneg ‖K.starProjection x - k‖]

/-- **The quotient norm is the norm of the orthogonal component.**  One inequality is the general
bound by any representative, the other is the minimality of the projection applied to
representatives of almost minimal norm. -/
theorem deningerQuotientNorm_eq (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ K)‖ = ‖x - K.starProjection x‖ := by
  refine le_antisymm ?_ ?_
  · have hmk : (Submodule.Quotient.mk (x - K.starProjection x) : E ⧸ K)
        = Submodule.Quotient.mk x := by
      refine (Submodule.Quotient.eq K).mpr ?_
      have : x - K.starProjection x - x = -K.starProjection x := by abel
      rw [this]
      exact K.neg_mem (K.starProjection_apply_mem x)
    calc ‖(Submodule.Quotient.mk x : E ⧸ K)‖
        = ‖(Submodule.Quotient.mk (x - K.starProjection x) : E ⧸ K)‖ := by rw [hmk]
      _ ≤ ‖x - K.starProjection x‖ := Submodule.Quotient.norm_mk_le K _
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨m, hm, hmnorm⟩ :=
      Submodule.Quotient.norm_mk_lt (S := K) (Submodule.Quotient.mk x) hε
    have hmx : m - x ∈ K := (Submodule.Quotient.eq K).mp hm
    have hxm : x - m ∈ K := by
      have : x - m = -(m - x) := by abel
      rw [this]
      exact K.neg_mem hmx
    have hmin := deningerProjection_minimal K x hxm
    have hcancel : x - (x - m) = m := by abel
    rw [hcancel] at hmin
    exact le_of_lt (lt_of_le_of_lt hmin hmnorm)

variable (T : E →L[ℂ] B) [CompleteSpace E]

omit [CompleteSpace E] in
/-- The zero-trace subspace is closed. -/
theorem deningerZeroTrace_isClosed :
    IsClosed ((LinearMap.ker (T : E →ₗ[ℂ] B) : Submodule ℂ E) : Set E) :=
  T.isClosed_ker

instance deningerZeroTrace_completeSpace :
    CompleteSpace (LinearMap.ker (T : E →ₗ[ℂ] B)) :=
  (deningerZeroTrace_isClosed T).completeSpace_coe

/-- **The Dirichlet decomposition.**  The zero-trace subspace and its orthogonal complement are
complementary. -/
theorem deningerZeroTrace_isCompl :
    IsCompl (LinearMap.ker (T : E →ₗ[ℂ] B)) (LinearMap.ker (T : E →ₗ[ℂ] B))ᗮ :=
  Submodule.isCompl_orthogonal _

/-- Every vector splits as a zero-trace vector plus a vector orthogonal to the zero-trace
subspace with the same image. -/
theorem deningerTrace_split (x : E) :
    x - (LinearMap.ker (T : E →ₗ[ℂ] B)).starProjection x
        ∈ (LinearMap.ker (T : E →ₗ[ℂ] B))ᗮ ∧
      T (x - (LinearMap.ker (T : E →ₗ[ℂ] B)).starProjection x) = T x := by
  refine ⟨Submodule.sub_starProjection_mem_orthogonal (K := LinearMap.ker (T : E →ₗ[ℂ] B)) x, ?_⟩
  have hker : (LinearMap.ker (T : E →ₗ[ℂ] B)).starProjection x
      ∈ LinearMap.ker (T : E →ₗ[ℂ] B) :=
    Submodule.starProjection_apply_mem _ x
  have hzero : T ((LinearMap.ker (T : E →ₗ[ℂ] B)).starProjection x) = 0 := hker
  rw [map_sub, hzero, sub_zero]

variable (hiso : ∀ x : E, x ∈ (LinearMap.ker (T : E →ₗ[ℂ] B))ᗮ → ‖T x‖ = ‖x‖)
  (hsurj : Function.Surjective T)

include hiso hsurj

/-- The trace is bijective from the orthogonal complement of the zero-trace subspace. -/
theorem deningerTrace_bijective_orthogonal :
    Function.Bijective
      fun x : (LinearMap.ker (T : E →ₗ[ℂ] B))ᗮ => T (x : E) := by
  constructor
  · intro x y hxy
    have hsub : T ((x : E) - (y : E)) = 0 := by
      rw [map_sub]
      exact sub_eq_zero_of_eq hxy
    have hmem : (x : E) - (y : E) ∈ (LinearMap.ker (T : E →ₗ[ℂ] B))ᗮ :=
      Submodule.sub_mem _ x.2 y.2
    have hnorm : ‖(x : E) - (y : E)‖ = 0 := by
      rw [← hiso _ hmem, hsub, norm_zero]
    exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp hnorm))
  · intro b
    obtain ⟨x, hx⟩ := hsurj b
    refine ⟨⟨x - (LinearMap.ker (T : E →ₗ[ℂ] B)).starProjection x,
      (deningerTrace_split T x).1⟩, ?_⟩
    show T (x - (LinearMap.ker (T : E →ₗ[ℂ] B)).starProjection x) = b
    rw [(deningerTrace_split T x).2, hx]

/-- **The trace is an isometry on the orthogonal complement of the zero-trace subspace.**  This is
the minimal-energy right inverse of the trace: every boundary value is attained by exactly one
vector orthogonal to the zero-trace subspace, with the same norm. -/
noncomputable def deningerTraceIsometry :
    (LinearMap.ker (T : E →ₗ[ℂ] B))ᗮ ≃ₗᵢ[ℂ] B where
  toLinearEquiv :=
    LinearEquiv.ofBijective
      ((T : E →ₗ[ℂ] B).comp ((LinearMap.ker (T : E →ₗ[ℂ] B))ᗮ).subtype)
      (deningerTrace_bijective_orthogonal T hiso hsurj)
  norm_map' x := hiso _ x.2

theorem deningerTraceIsometry_apply (x : (LinearMap.ker (T : E →ₗ[ℂ] B))ᗮ) :
    deningerTraceIsometry T hiso hsurj x = T (x : E) := rfl

/-- **The trace quotient isometry.**  The trace descends to the quotient by the zero-trace
subspace, and there it is an isometric isomorphism onto the boundary space, because the quotient
norm is the norm of the component orthogonal to the zero-trace subspace. -/
noncomputable def deningerTraceQuotientIsometry :
    (E ⧸ LinearMap.ker (T : E →ₗ[ℂ] B)) ≃ₗᵢ[ℂ] B where
  toLinearEquiv :=
    LinearEquiv.ofBijective
      ((LinearMap.ker (T : E →ₗ[ℂ] B)).liftQ (T : E →ₗ[ℂ] B) le_rfl)
      (by
        constructor
        · refine LinearMap.ker_eq_bot.mp ?_
          exact Submodule.ker_liftQ_eq_bot _ _ le_rfl le_rfl
        · intro b
          obtain ⟨x, hx⟩ := hsurj b
          exact ⟨Submodule.Quotient.mk x, by rw [Submodule.liftQ_apply]; exact hx⟩)
  norm_map' := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show ‖(LinearMap.ker (T : E →ₗ[ℂ] B)).liftQ (T : E →ₗ[ℂ] B) le_rfl
        (Submodule.Quotient.mk x)‖ = ‖(Submodule.Quotient.mk x : E ⧸ _)‖
    rw [Submodule.liftQ_apply, deningerQuotientNorm_eq]
    show ‖T x‖ = ‖x - (LinearMap.ker (T : E →ₗ[ℂ] B)).starProjection x‖
    rw [← (deningerTrace_split T x).2, hiso _ (deningerTrace_split T x).1]

theorem deningerTraceQuotientIsometry_apply (x : E) :
    deningerTraceQuotientIsometry T hiso hsurj (Submodule.Quotient.mk x) = T x := rfl

end TraceQuotient

section QuotientTransport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable (d : E ≃ₗᵢ[ℂ] F) (K : Submodule ℂ E) (K' : Submodule ℂ F)
  (hK : ∀ y : F, y ∈ K' ↔ d.symm y ∈ K)

include hK

/-- **A surjective linear isometry transports quotient norms.**  Representatives correspond under
the isometry, and the isometry preserves their norms, so the two infima agree. -/
theorem deningerQuotient_norm_transport (x : E) :
    ‖(Submodule.Quotient.mk (d x) : F ⧸ K')‖ = ‖(Submodule.Quotient.mk x : E ⧸ K)‖ := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨m, hm, hmnorm⟩ :=
      Submodule.Quotient.norm_mk_lt (S := K) (Submodule.Quotient.mk x) hε
    have hmem : d m - d x ∈ K' := by
      refine (hK _).mpr ?_
      rw [← map_sub, LinearIsometryEquiv.symm_apply_apply]
      exact (Submodule.Quotient.eq K).mp hm
    have hmk : (Submodule.Quotient.mk (d m) : F ⧸ K') = Submodule.Quotient.mk (d x) :=
      (Submodule.Quotient.eq K').mpr hmem
    calc ‖(Submodule.Quotient.mk (d x) : F ⧸ K')‖
        = ‖(Submodule.Quotient.mk (d m) : F ⧸ K')‖ := by rw [hmk]
      _ ≤ ‖d m‖ := Submodule.Quotient.norm_mk_le K' _
      _ = ‖m‖ := d.norm_map m
      _ ≤ ‖(Submodule.Quotient.mk x : E ⧸ K)‖ + ε := le_of_lt hmnorm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn, hnnorm⟩ :=
      Submodule.Quotient.norm_mk_lt (S := K') (Submodule.Quotient.mk (d x)) hε
    have hmem : d.symm n - x ∈ K := by
      have hnk : n - d x ∈ K' := (Submodule.Quotient.eq K').mp hn
      have := (hK _).mp hnk
      rwa [map_sub, LinearIsometryEquiv.symm_apply_apply] at this
    have hmk : (Submodule.Quotient.mk (d.symm n) : E ⧸ K) = Submodule.Quotient.mk x :=
      (Submodule.Quotient.eq K).mpr hmem
    calc ‖(Submodule.Quotient.mk x : E ⧸ K)‖
        = ‖(Submodule.Quotient.mk (d.symm n) : E ⧸ K)‖ := by rw [hmk]
      _ ≤ ‖d.symm n‖ := Submodule.Quotient.norm_mk_le K _
      _ = ‖n‖ := d.symm.norm_map n
      _ ≤ ‖(Submodule.Quotient.mk (d x) : F ⧸ K')‖ + ε := le_of_lt hnnorm

/-- **A surjective linear isometry descends to the quotients.** -/
noncomputable def deningerQuotientTransport : (E ⧸ K) ≃ₗᵢ[ℂ] (F ⧸ K') where
  toLinearEquiv :=
    LinearEquiv.ofLinear
      (K.mapQ K' (d.toLinearEquiv : E →ₗ[ℂ] F) (fun x hx => by
        refine (hK _).mpr ?_
        show d.symm (d x) ∈ K
        rw [LinearIsometryEquiv.symm_apply_apply]
        exact hx))
      (K'.mapQ K (d.symm.toLinearEquiv : F →ₗ[ℂ] E) (fun y hy => (hK y).mp hy))
      (by
        refine LinearMap.ext fun q => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        show Submodule.Quotient.mk (d (d.symm y)) = _
        rw [LinearIsometryEquiv.apply_symm_apply]
        rfl)
      (by
        refine LinearMap.ext fun q => ?_
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        show Submodule.Quotient.mk (d.symm (d x)) = _
        rw [LinearIsometryEquiv.symm_apply_apply]
        rfl)
  norm_map' := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show ‖(Submodule.Quotient.mk (d x) : F ⧸ K')‖ = ‖(Submodule.Quotient.mk x : E ⧸ K)‖
    exact deningerQuotient_norm_transport d K K' hK x

end QuotientTransport

section GradientDefect

variable {E F B : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]

variable (T : E →L[ℂ] B) (d : E ≃ₗᵢ[ℂ] F) (K' : Submodule ℂ F)
  (hK : ∀ y : F, y ∈ K' ↔ d.symm y ∈ LinearMap.ker (T : E →ₗ[ℂ] B))
  (hiso : ∀ x : E, x ∈ (LinearMap.ker (T : E →ₗ[ℂ] B))ᗮ → ‖T x‖ = ‖x‖)
  (hsurj : Function.Surjective T)

include hK hiso hsurj

/-- **The relative boundary defect.**  Under a leafwise gradient — any surjective linear isometry
of the energy space — the quotient of the image of the full energy space by the image of the
zero-trace subspace is isometric to the boundary space.  So a gradient of a Poisson extension is a
nonzero class relative to the zero-trace domain exactly when its boundary value is nonzero. -/
noncomputable def deningerGradientDefectIsometry : (F ⧸ K') ≃ₗᵢ[ℂ] B :=
  (deningerQuotientTransport d (LinearMap.ker (T : E →ₗ[ℂ] B)) K' hK).symm.trans
    (deningerTraceQuotientIsometry T hiso hsurj)

theorem deningerGradientDefectIsometry_apply (x : E) :
    deningerGradientDefectIsometry T d K' hK hiso hsurj
        (Submodule.Quotient.mk (d x)) = T x := by
  have hmk : (deningerQuotientTransport d (LinearMap.ker (T : E →ₗ[ℂ] B)) K' hK)
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk (d x) := rfl
  show (deningerTraceQuotientIsometry T hiso hsurj)
      ((deningerQuotientTransport d (LinearMap.ker (T : E →ₗ[ℂ] B)) K' hK).symm
        (Submodule.Quotient.mk (d x))) = T x
  rw [← hmk, LinearIsometryEquiv.symm_apply_apply]
  rfl

end GradientDefect

end RHTower
