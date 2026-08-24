import GaloisForLFunctions.HTGeometry.FiniteBlaschkeLeakageRank

open Complex
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Complementary causal Hardy compression of a finite inner quotient. -/
def finiteBlaschkeCausalCore (A B : FiniteBlaschke) : HardyDisk →L[ℂ] HardyDisk :=
  (finiteBlaschkeMul B).adjoint.comp (finiteBlaschkeMul A)

/-- Multiplying the denominator adjoint back reconstructs the component orthogonal to its model
space. -/
theorem finiteBlaschkeMul_adjoint_eq_sub_starProjection (B : FiniteBlaschke)
    (g : HardyDisk) :
    finiteBlaschkeMul B ((finiteBlaschkeMul B).adjoint g) =
      g - (finiteBlaschkeModelSpace B).starProjection g := by
  let K : Submodule ℂ HardyDisk := finiteBlaschkeModelSpace B
  let u : HardyDisk := K.starProjection g
  let v : HardyDisk := g - u
  have hvmem : v ∈ Submodule.orthogonal K := by
    simpa [v, u, K] using
      (finiteBlaschkeModelSpace B).sub_starProjection_mem_orthogonal g
  obtain ⟨h, hh⟩ : ∃ h : HardyDisk, finiteBlaschkeMul B h = v := by
    have hrange : v ∈ LinearMap.range
        ((finiteBlaschkeMul B : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) := by
      rw [← finiteBlaschkeModelSpace_orthogonal_eq_range B]
      simpa [K] using hvmem
    simpa using hrange
  have humem : u ∈ K := by
    simpa [u, K] using
      (finiteBlaschkeModelSpace B).starProjection_apply_mem g
  have hadjU : (finiteBlaschkeMul B).adjoint u = 0 := by
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
    have hy : finiteBlaschkeMul B y ∈ Submodule.orthogonal K := by
      rw [show Submodule.orthogonal K =
          LinearMap.range ((finiteBlaschkeMul B : HardyDisk →L[ℂ] HardyDisk) :
            HardyDisk →ₗ[ℂ] HardyDisk) by
        simpa [K] using finiteBlaschkeModelSpace_orthogonal_eq_range B]
      exact ⟨y, rfl⟩
    exact (K.mem_orthogonal _).1 hy u humem
  have hsplit : g = u + v := by simp [v]
  have hadj : (finiteBlaschkeMul B).adjoint g = h := by
    rw [hsplit, map_add, hadjU, zero_add, ← hh, adjoint_finiteBlaschkeMul_comp]
  rw [hadj, hh]

/-- Exact causal/leakage reconstruction of the numerator multiplier. -/
theorem finiteBlaschke_leakage_add_causal_reconstruction
    (A B : FiniteBlaschke) (f : HardyDisk) :
    (finiteBlaschkeLeakageCore A B f : HardyDisk) +
        finiteBlaschkeMul B (finiteBlaschkeCausalCore A B f) =
      finiteBlaschkeMul A f := by
  rw [finiteBlaschkeCausalCore, ContinuousLinearMap.comp_apply,
    finiteBlaschkeMul_adjoint_eq_sub_starProjection]
  change (finiteBlaschkeModelSpace B).starProjection (finiteBlaschkeMul A f) +
      (finiteBlaschkeMul A f -
        (finiteBlaschkeModelSpace B).starProjection (finiteBlaschkeMul A f)) =
    finiteBlaschkeMul A f
  abel

/-- Polarized Hardy Pythagoras: leakage and causal compression split the full inner product. -/
theorem inner_finiteBlaschkeLeakageCore_add_causalCore
    (A B : FiniteBlaschke) (f g : HardyDisk) :
    inner ℂ (finiteBlaschkeLeakageCore A B f)
          (finiteBlaschkeLeakageCore A B g) +
        inner ℂ (finiteBlaschkeCausalCore A B f)
          (finiteBlaschkeCausalCore A B g) =
      inner ℂ f g := by
  let K : Submodule ℂ HardyDisk := finiteBlaschkeModelSpace B
  let Lf : HardyDisk := finiteBlaschkeLeakageCore A B f
  let Lg : HardyDisk := finiteBlaschkeLeakageCore A B g
  let Tf : HardyDisk := finiteBlaschkeCausalCore A B f
  let Tg : HardyDisk := finiteBlaschkeCausalCore A B g
  have hLf : Lf ∈ K := by
    simpa [Lf, K] using (finiteBlaschkeLeakageCore A B f).property
  have hLg : Lg ∈ K := by
    simpa [Lg, K] using (finiteBlaschkeLeakageCore A B g).property
  have hBTf : finiteBlaschkeMul B Tf ∈ Submodule.orthogonal K := by
    rw [show Submodule.orthogonal K =
        LinearMap.range ((finiteBlaschkeMul B : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) by
      simpa [K] using finiteBlaschkeModelSpace_orthogonal_eq_range B]
    exact ⟨Tf, rfl⟩
  have hBTg : finiteBlaschkeMul B Tg ∈ Submodule.orthogonal K := by
    rw [show Submodule.orthogonal K =
        LinearMap.range ((finiteBlaschkeMul B : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) by
      simpa [K] using finiteBlaschkeModelSpace_orthogonal_eq_range B]
    exact ⟨Tg, rfl⟩
  have hcross_fg : (inner ℂ Lf (finiteBlaschkeMul B Tg) : ℂ) = 0 :=
    (K.mem_orthogonal _).1 hBTg Lf hLf
  have hcross_gf : (inner ℂ (finiteBlaschkeMul B Tf) Lg : ℂ) = 0 := by
    rw [← inner_conj_symm, (K.mem_orthogonal _).1 hBTf Lg hLg, map_zero]
  have hsplit :
      inner ℂ Lf Lg +
          inner ℂ (finiteBlaschkeMul B Tf) (finiteBlaschkeMul B Tg) =
        inner ℂ (finiteBlaschkeMul A f) (finiteBlaschkeMul A g) := by
    rw [← finiteBlaschke_leakage_add_causal_reconstruction A B f,
      ← finiteBlaschke_leakage_add_causal_reconstruction A B g]
    change inner ℂ Lf Lg +
        inner ℂ (finiteBlaschkeMul B Tf) (finiteBlaschkeMul B Tg) =
      inner ℂ (Lf + finiteBlaschkeMul B Tf)
        (Lg + finiteBlaschkeMul B Tg)
    rw [inner_add_left, inner_add_right, inner_add_right, hcross_fg, hcross_gf]
    ring
  have hA := inner_map_map_of_isometry
    (fun x => norm_finiteBlaschkeMul A x) f g
  have hB := inner_map_map_of_isometry
    (fun x => norm_finiteBlaschkeMul B x) Tf Tg
  change inner ℂ Lf Lg + inner ℂ Tf Tg = inner ℂ f g
  rw [← hA, ← hB]
  exact hsplit

/-- Operator form of polarized Hardy Pythagoras, `L†L + T†T = I`. -/
theorem adjoint_comp_finiteBlaschkeLeakageCore_add_causalCore
    (A B : FiniteBlaschke) :
    (finiteBlaschkeLeakageCore A B).adjoint.comp
          (finiteBlaschkeLeakageCore A B) +
        (finiteBlaschkeCausalCore A B).adjoint.comp
          (finiteBlaschkeCausalCore A B) =
      ContinuousLinearMap.id ℂ HardyDisk := by
  apply ContinuousLinearMap.ext
  intro x
  refine ext_inner_right ℂ fun y => ?_
  rw [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  exact inner_finiteBlaschkeLeakageCore_add_causalCore A B x y

/-- Orthogonal inputs have exactly opposite leakage and causal cross-pairings. -/
theorem inner_finiteBlaschkeLeakageCore_eq_neg_causalCore_of_orthogonal
    (A B : FiniteBlaschke) (f g : HardyDisk) (hfg : inner ℂ f g = 0) :
    inner ℂ (finiteBlaschkeLeakageCore A B f)
        (finiteBlaschkeLeakageCore A B g) =
      -inner ℂ (finiteBlaschkeCausalCore A B f)
        (finiteBlaschkeCausalCore A B g) := by
  have h := inner_finiteBlaschkeLeakageCore_add_causalCore A B f g
  rw [hfg] at h
  exact eq_neg_of_add_eq_zero_left h

end GaloisForLFunctions.HTGeometry
