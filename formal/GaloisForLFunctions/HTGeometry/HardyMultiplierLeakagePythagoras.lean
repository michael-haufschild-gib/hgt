import GaloisForLFunctions.HTGeometry.HardyMultiplierModelSpaceProduct
import GaloisForLFunctions.HTGeometry.ModelSpaceLeakageDenseRank

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complementary causal Hardy compression of an arbitrary inner quotient. -/
def hardyMultiplierCausalCore (F B : DiskMultiplier) : HardyDisk →L[ℂ] HardyDisk :=
  (hardyMul B).adjoint.comp (hardyMul F)

/-- Projected anti-causal core of an arbitrary inner quotient. -/
def hardyMultiplierLeakageCore (F B : DiskMultiplier) :
    HardyDisk →L[ℂ] hardyMultiplierModelSpace B :=
  modelSpaceLeakageCore (hardyMultiplierModelSpace B) (hardyMul F)

/-- Multiplication by an inner denominator reconstructs the orthogonal complement of its model
space from the multiplier adjoint. -/
theorem hardyMul_adjoint_eq_sub_starProjection_of_isometry
    (B : DiskMultiplier) (hB : HardyMultiplierIsometry B) (g : HardyDisk) :
    hardyMul B ((hardyMul B).adjoint g) =
      g - (hardyMultiplierModelSpace B).starProjection g := by
  let K : Submodule ℂ HardyDisk := hardyMultiplierModelSpace B
  let u : HardyDisk := K.starProjection g
  let v : HardyDisk := g - u
  have hvmem : v ∈ Submodule.orthogonal K := by
    simpa [v, u, K] using K.sub_starProjection_mem_orthogonal g
  obtain ⟨h, hh⟩ : ∃ h : HardyDisk, hardyMul B h = v := by
    have hrange : v ∈ LinearMap.range
        ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) := by
      rw [← hardyMultiplierModelSpace_orthogonal_eq_range_of_isometry B hB]
      simpa [K] using hvmem
    simpa using hrange
  have humem : u ∈ K := by
    simpa [u, K] using K.starProjection_apply_mem g
  have hadjU : (hardyMul B).adjoint u = 0 := by
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
    have hy : hardyMul B y ∈ Submodule.orthogonal K := by
      rw [show Submodule.orthogonal K =
          LinearMap.range
            ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) :
              HardyDisk →ₗ[ℂ] HardyDisk) by
        simpa [K] using
          hardyMultiplierModelSpace_orthogonal_eq_range_of_isometry B hB]
      exact ⟨y, rfl⟩
    exact (K.mem_orthogonal _).1 hy u humem
  have hsplit : g = u + v := by simp [v]
  have hadj : (hardyMul B).adjoint g = h := by
    rw [hsplit, map_add, hadjU, zero_add, ← hh,
      adjoint_hardyMul_comp_of_isometry B hB]
  rw [hadj, hh]

/-- Exact causal/leakage reconstruction for arbitrary inner numerator and denominator. -/
theorem hardyMultiplier_leakage_add_causal_reconstruction
    (F B : DiskMultiplier) (hB : HardyMultiplierIsometry B) (f : HardyDisk) :
    (hardyMultiplierLeakageCore F B f : HardyDisk) +
        hardyMul B (hardyMultiplierCausalCore F B f) = hardyMul F f := by
  rw [hardyMultiplierCausalCore, ContinuousLinearMap.comp_apply,
    hardyMul_adjoint_eq_sub_starProjection_of_isometry B hB]
  change (hardyMultiplierModelSpace B).starProjection (hardyMul F f) +
      (hardyMul F f -
        (hardyMultiplierModelSpace B).starProjection (hardyMul F f)) = hardyMul F f
  abel

/-- Polarized Pythagoras for an arbitrary inner quotient. -/
theorem inner_hardyMultiplierLeakageCore_add_causalCore
    (F B : DiskMultiplier) (hF : HardyMultiplierIsometry F)
    (hB : HardyMultiplierIsometry B) (f g : HardyDisk) :
    inner ℂ (hardyMultiplierLeakageCore F B f)
          (hardyMultiplierLeakageCore F B g) +
        inner ℂ (hardyMultiplierCausalCore F B f)
          (hardyMultiplierCausalCore F B g) = inner ℂ f g := by
  let K : Submodule ℂ HardyDisk := hardyMultiplierModelSpace B
  let Lf : HardyDisk := hardyMultiplierLeakageCore F B f
  let Lg : HardyDisk := hardyMultiplierLeakageCore F B g
  let Tf : HardyDisk := hardyMultiplierCausalCore F B f
  let Tg : HardyDisk := hardyMultiplierCausalCore F B g
  have hLf : Lf ∈ K := by
    simpa [Lf, K] using (hardyMultiplierLeakageCore F B f).property
  have hLg : Lg ∈ K := by
    simpa [Lg, K] using (hardyMultiplierLeakageCore F B g).property
  have hBTf : hardyMul B Tf ∈ Submodule.orthogonal K := by
    rw [show Submodule.orthogonal K =
        LinearMap.range
          ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) :
            HardyDisk →ₗ[ℂ] HardyDisk) by
      simpa [K] using
        hardyMultiplierModelSpace_orthogonal_eq_range_of_isometry B hB]
    exact ⟨Tf, rfl⟩
  have hBTg : hardyMul B Tg ∈ Submodule.orthogonal K := by
    rw [show Submodule.orthogonal K =
        LinearMap.range
          ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) :
            HardyDisk →ₗ[ℂ] HardyDisk) by
      simpa [K] using
        hardyMultiplierModelSpace_orthogonal_eq_range_of_isometry B hB]
    exact ⟨Tg, rfl⟩
  have hcross_fg : (inner ℂ Lf (hardyMul B Tg) : ℂ) = 0 :=
    (K.mem_orthogonal _).1 hBTg Lf hLf
  have hcross_gf : (inner ℂ (hardyMul B Tf) Lg : ℂ) = 0 := by
    rw [← inner_conj_symm, (K.mem_orthogonal _).1 hBTf Lg hLg, map_zero]
  have hsplit :
      inner ℂ Lf Lg + inner ℂ (hardyMul B Tf) (hardyMul B Tg) =
        inner ℂ (hardyMul F f) (hardyMul F g) := by
    rw [← hardyMultiplier_leakage_add_causal_reconstruction F B hB f,
      ← hardyMultiplier_leakage_add_causal_reconstruction F B hB g]
    change inner ℂ Lf Lg + inner ℂ (hardyMul B Tf) (hardyMul B Tg) =
      inner ℂ (Lf + hardyMul B Tf) (Lg + hardyMul B Tg)
    rw [inner_add_left, inner_add_right, inner_add_right, hcross_fg, hcross_gf]
    ring
  have hFi := inner_map_map_of_isometry hF f g
  have hBi := inner_map_map_of_isometry hB Tf Tg
  change inner ℂ Lf Lg + inner ℂ Tf Tg = inner ℂ f g
  rw [← hFi, ← hBi]
  exact hsplit

/-- Operator identity `L†L + T†T = I` for arbitrary inner quotients. -/
theorem adjoint_comp_hardyMultiplierLeakageCore_add_causalCore
    (F B : DiskMultiplier) (hF : HardyMultiplierIsometry F)
    (hB : HardyMultiplierIsometry B) :
    (hardyMultiplierLeakageCore F B).adjoint.comp
          (hardyMultiplierLeakageCore F B) +
        (hardyMultiplierCausalCore F B).adjoint.comp
          (hardyMultiplierCausalCore F B) =
      ContinuousLinearMap.id ℂ HardyDisk := by
  apply ContinuousLinearMap.ext
  intro x
  refine ext_inner_right ℂ fun y => ?_
  rw [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  exact inner_hardyMultiplierLeakageCore_add_causalCore F B hF hB x y

/-- The adjoint of an inner Hardy multiplier is contractive. -/
theorem norm_adjoint_hardyMul_le_of_isometry
    (B : DiskMultiplier) (hB : HardyMultiplierIsometry B) (x : HardyDisk) :
    ‖(hardyMul B).adjoint x‖ ≤ ‖x‖ := by
  have hsquare := norm_sq_adjoint_hardyMul_of_isometry B hB x
  have hle : ‖(hardyMul B).adjoint x‖ ^ (2 : ℕ) ≤ ‖x‖ ^ (2 : ℕ) := by
    exact le_of_eq_of_le hsquare (sub_le_self _ (sq_nonneg _))
  nlinarith [norm_nonneg ((hardyMul B).adjoint x), norm_nonneg x]

/-- Causal compression of an arbitrary inner quotient is contractive. -/
theorem norm_hardyMultiplierCausalCore_le_one
    (F B : DiskMultiplier) (hF : HardyMultiplierIsometry F)
    (hB : HardyMultiplierIsometry B) :
    ‖hardyMultiplierCausalCore F B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, hardyMultiplierCausalCore, ContinuousLinearMap.comp_apply]
  calc
    ‖(hardyMul B).adjoint (hardyMul F x)‖ ≤ ‖hardyMul F x‖ :=
      norm_adjoint_hardyMul_le_of_isometry B hB _
    _ = ‖x‖ := hF x

end

end GaloisForLFunctions.HTGeometry
