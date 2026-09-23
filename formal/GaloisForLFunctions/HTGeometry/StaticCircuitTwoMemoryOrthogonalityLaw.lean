import GaloisForLFunctions.HTGeometry.RangeObservabilityDuality

/-!
# Static--circuit two-memory orthogonality law

Two nested orthogonal projections separate a universal invariant sector from a larger quenched
static sector.  A unitary evolution that fixes the static sector and a preparation vector with the
same universal projection then have an exact three-term collision decomposition:

* the universal baseline;
* alignment of static spectral memory with preparation memory;
* alignment of oscillatory dynamical memory with preparation memory.

The static and dynamical memories have a conserved total squared norm.  Thus failure of norm
mixing does not obstruct small collision: only the direction of retained memory matters.

For a finite target dictionary, one target collision forces an explicit positive dynamical-memory
alignment.  If the evolution returns exactly and the dictionary contains the seed, the same theorem
forces realignment by at least one inverse dictionary size minus the completed baseline.

The theorem is purely Hilbert-geometric.  It uses no finite-dimensionality, probability,
Hamiltonian ensemble, spectral gap, or asymptotic hypothesis.
-/

open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

variable (PiOp P : E →L[𝕜] E)

/-- Universal invariant component of the seed. -/
def universalSector (x : E) : E := PiOp x

/-- Part retained by the quenched static projection beyond the universal sector. -/
def staticMemory (x : E) : E := P x - PiOp x

/-- Oscillatory part of the evolved seed beyond the quenched static projection. -/
def dynamicMemory (U : E ≃ₗᵢ[𝕜] E) (x : E) : E := U x - P x

/-- Preparation vector with the universal seed component removed. -/
def preparationMemory (x y : E) : E := y - PiOp x

/-- A self-adjoint idempotent range is orthogonal to its complementary residual. -/
theorem projection_inner_complement_eq_zero
    (hPsa : IsSelfAdjoint P) (hPid : ∀ z, P (P z) = P z) (x y : E) :
    inner 𝕜 (P x) (y - P y) = 0 := by
  rw [inner_isSelfAdjoint_left hPsa, map_sub, hPid, sub_self, inner_zero_right]

/-- Universal and static-memory sectors are orthogonal. -/
theorem universal_static_inner_eq_zero
    (hPisa : IsSelfAdjoint PiOp) (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z) (x : E) :
    inner 𝕜 (universalSector PiOp x) (staticMemory PiOp P x) = 0 := by
  rw [universalSector, staticMemory, inner_isSelfAdjoint_left hPisa,
    map_sub, hPiP, hPiid, sub_self, inner_zero_right]

/-- Universal and dynamical-memory sectors are orthogonal. -/
theorem universal_dynamic_inner_eq_zero
    (U : E ≃ₗᵢ[𝕜] E) (x : E)
    (hPisa : IsSelfAdjoint PiOp) (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPU : ∀ z, P (U z) = P z) :
    inner 𝕜 (universalSector PiOp x) (dynamicMemory P U x) = 0 := by
  rw [universalSector, dynamicMemory, inner_isSelfAdjoint_left hPisa, map_sub]
  have hPiU : PiOp (U x) = PiOp x := by
    rw [← hPiP (U x), hPU, hPiP]
  rw [hPiU, hPiP, sub_self, inner_zero_right]

/-- Universal and preparation-memory sectors are orthogonal. -/
theorem universal_preparation_inner_eq_zero
    (x y : E) (hPisa : IsSelfAdjoint PiOp)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z) (hPiy : PiOp y = PiOp x) :
    inner 𝕜 (universalSector PiOp x) (preparationMemory PiOp x y) = 0 := by
  rw [universalSector, preparationMemory, inner_isSelfAdjoint_left hPisa,
    map_sub, hPiy, hPiid, sub_self, inner_zero_right]

/-- Quenched static and oscillatory dynamical memories are orthogonal. -/
theorem static_dynamic_inner_eq_zero
    (U : E ≃ₗᵢ[𝕜] E) (x : E)
    (hPsa : IsSelfAdjoint P) (hPid : ∀ z, P (P z) = P z)
    (hPU : ∀ z, P (U z) = P z)
    (hPPi : ∀ z, P (PiOp z) = PiOp z) :
    inner 𝕜 (staticMemory PiOp P x) (dynamicMemory P U x) = 0 := by
  rw [staticMemory, dynamicMemory, inner_sub_left]
  have hPr : P (U x - P x) = 0 := by rw [map_sub, hPU, hPid, sub_self]
  have h1 : inner 𝕜 (P x) (U x - P x) = 0 := by
    rw [inner_isSelfAdjoint_left hPsa, hPr, inner_zero_right]
  have h2 : inner 𝕜 (PiOp x) (U x - P x) = 0 := by
    rw [← hPPi x, inner_isSelfAdjoint_left hPsa, hPr, inner_zero_right]
  rw [h1, h2, sub_zero]

/-- **Two-memory collision law.** Every evolved--prepared collision has exactly one universal
baseline and two nonuniversal cross-alignments. -/
theorem twoMemory_collision
    (U : E ≃ₗᵢ[𝕜] E) (x y : E)
    (hPisa : IsSelfAdjoint PiOp)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z)
    (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPU : ∀ z, P (U z) = P z) (hPiy : PiOp y = PiOp x) :
    inner 𝕜 (U x) y =
      inner 𝕜 (universalSector PiOp x) (universalSector PiOp x) +
        inner 𝕜 (staticMemory PiOp P x) (preparationMemory PiOp x y) +
        inner 𝕜 (dynamicMemory P U x) (preparationMemory PiOp x y) := by
  have hu_c := universal_static_inner_eq_zero PiOp P hPisa hPiP hPiid x
  have hu_r := universal_dynamic_inner_eq_zero PiOp P U x hPisa hPiP hPU
  have hu_q := universal_preparation_inner_eq_zero PiOp x y hPisa hPiid hPiy
  have hUx : U x = universalSector PiOp x + staticMemory PiOp P x + dynamicMemory P U x := by
    simp only [universalSector, staticMemory, dynamicMemory]
    abel
  have hy : y = universalSector PiOp x + preparationMemory PiOp x y := by
    simp only [universalSector, preparationMemory]
    abel
  calc
    inner 𝕜 (U x) y = inner 𝕜
        (universalSector PiOp x + staticMemory PiOp P x + dynamicMemory P U x)
        (universalSector PiOp x + preparationMemory PiOp x y) := by
      rw [hUx]
      exact congrArg
        (fun z => inner 𝕜
          (universalSector PiOp x + staticMemory PiOp P x + dynamicMemory P U x) z) hy
    _ = inner 𝕜 (universalSector PiOp x) (universalSector PiOp x) +
        inner 𝕜 (staticMemory PiOp P x) (preparationMemory PiOp x y) +
        inner 𝕜 (dynamicMemory P U x) (preparationMemory PiOp x y) := by
      simp only [inner_add_left, inner_add_right, hu_q,
        inner_eq_zero_symm.mp hu_c, inner_eq_zero_symm.mp hu_r, zero_add, add_zero]
      abel

/-- The completed static collision is exactly the universal floor plus static-memory alignment. -/
theorem twoMemory_completedBaseline
    (x y : E)
    (hPisa : IsSelfAdjoint PiOp)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z)
    (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPiy : PiOp y = PiOp x) :
    inner 𝕜 (P x) y =
      inner 𝕜 (universalSector PiOp x) (universalSector PiOp x) +
        inner 𝕜 (staticMemory PiOp P x) (preparationMemory PiOp x y) := by
  have hu_c := universal_static_inner_eq_zero PiOp P hPisa hPiP hPiid x
  have hu_q := universal_preparation_inner_eq_zero PiOp x y hPisa hPiid hPiy
  have hPx : P x = universalSector PiOp x + staticMemory PiOp P x := by
    simp only [universalSector, staticMemory]
    abel
  have hy : y = universalSector PiOp x + preparationMemory PiOp x y := by
    simp only [universalSector, preparationMemory]
    abel
  calc
    inner 𝕜 (P x) y = inner 𝕜
        (universalSector PiOp x + staticMemory PiOp P x) y := by rw [hPx]
    _ = inner 𝕜 (universalSector PiOp x + staticMemory PiOp P x)
        (universalSector PiOp x + preparationMemory PiOp x y) :=
      congrArg (fun z => inner 𝕜
        (universalSector PiOp x + staticMemory PiOp P x) z) hy
    _ = inner 𝕜 (universalSector PiOp x) (universalSector PiOp x) +
        inner 𝕜 (staticMemory PiOp P x) (preparationMemory PiOp x y) := by
      simp only [inner_add_left, inner_add_right, hu_q,
        inner_eq_zero_symm.mp hu_c, zero_add, add_zero]

/-- The complete physical-time correction is one dynamical/preparation cross-alignment. -/
theorem twoMemory_dynamicCorrection
    (U : E ≃ₗᵢ[𝕜] E) (x y : E)
    (hPisa : IsSelfAdjoint PiOp)
    (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPU : ∀ z, P (U z) = P z) :
    inner 𝕜 (U x - P x) y =
      inner 𝕜 (dynamicMemory P U x) (preparationMemory PiOp x y) := by
  have hu_r := universal_dynamic_inner_eq_zero PiOp P U x hPisa hPiP hPU
  have hy : y = universalSector PiOp x + preparationMemory PiOp x y := by
    simp only [universalSector, preparationMemory]
    abel
  rw [dynamicMemory]
  have hr_u : inner 𝕜 (U x - P x) (universalSector PiOp x) = 0 := by
    simpa only [dynamicMemory] using inner_eq_zero_symm.mp hu_r
  calc
    inner 𝕜 (U x - P x) y = inner 𝕜 (U x - P x)
        (universalSector PiOp x + preparationMemory PiOp x y) :=
      congrArg (fun z => inner 𝕜 (U x - P x) z) hy
    _ = inner 𝕜 (U x - P x) (preparationMemory PiOp x y) := by
      rw [inner_add_right, hr_u, zero_add]

/-- **Static nonmixing law.** Static and dynamical memories have a conserved total squared norm. -/
theorem twoMemory_norm_conservation
    (U : E ≃ₗᵢ[𝕜] E) (x : E)
    (hPsa : IsSelfAdjoint P)
    (hPid : ∀ z, P (P z) = P z)
    (hPPi : ∀ z, P (PiOp z) = PiOp z)
    (hUP : ∀ z, U (P z) = P z) :
    ‖staticMemory PiOp P x‖ ^ (2 : ℕ) + ‖dynamicMemory P U x‖ ^ (2 : ℕ) =
      ‖x - PiOp x‖ ^ (2 : ℕ) := by
  have hcperp : inner 𝕜 (staticMemory PiOp P x) (x - P x) = 0 := by
    rw [staticMemory, inner_sub_left]
    have h1 : inner 𝕜 (P x) (x - P x) = 0 :=
      projection_inner_complement_eq_zero P hPsa hPid x x
    have h2 : inner 𝕜 (PiOp x) (x - P x) = 0 := by
      rw [← hPPi x, inner_isSelfAdjoint_left hPsa, map_sub, hPid, sub_self,
        inner_zero_right]
    rw [h1, h2, sub_zero]
  have hrnorm : ‖dynamicMemory P U x‖ = ‖x - P x‖ := by
    rw [dynamicMemory]
    calc
      ‖U x - P x‖ = ‖U x - U (P x)‖ := by rw [hUP]
      _ = ‖U (x - P x)‖ := by rw [map_sub]
      _ = ‖x - P x‖ := LinearIsometryEquiv.norm_map U _
  have hxsplit : x - PiOp x = staticMemory PiOp P x + (x - P x) := by
    simp only [staticMemory]
    abel
  calc
    ‖staticMemory PiOp P x‖ ^ (2 : ℕ) + ‖dynamicMemory P U x‖ ^ (2 : ℕ) =
        ‖staticMemory PiOp P x‖ ^ (2 : ℕ) + ‖x - P x‖ ^ (2 : ℕ) := by rw [hrnorm]
    _ = ‖staticMemory PiOp P x + (x - P x)‖ ^ (2 : ℕ) := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hcperp).symm
    _ = ‖x - PiOp x‖ ^ (2 : ℕ) := by rw [← hxsplit]

omit [CompleteSpace E] in
/-- A preparation channel preserving the universal projection preserves it at every depth. -/
theorem projection_preparation_pow_invariant
    (T : E →L[𝕜] E) (hPiT : ∀ z, PiOp (T z) = PiOp z) :
    ∀ s x, PiOp ((T ^ s) x) = PiOp x := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
      intro x
      rw [pow_succ]
      change PiOp ((T ^ s) (T x)) = PiOp x
      rw [ih, hPiT]

section RealCollision

variable {I : Type*} [Fintype I]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Uniform preparation moment of a finite target dictionary. -/
def finitePreparationMoment (target : I → F) : F :=
  ((Fintype.card I : ℝ)⁻¹) • ∑ i, target i

theorem inner_finitePreparationMoment (z : F) (target : I → F) :
    inner ℝ z (finitePreparationMoment target) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, inner ℝ z (target i) := by
  rw [finitePreparationMoment, inner_smul_right, inner_sum]

/-- One nonnegative target collision survives uniform dictionary averaging with inverse-cardinality
weight. -/
theorem one_collision_le_inner_finitePreparationMoment
    (z : F) (target : I → F) (i₀ : I)
    (h_nonneg : ∀ i, 0 ≤ inner ℝ z (target i)) :
    (Fintype.card I : ℝ)⁻¹ * inner ℝ z (target i₀) ≤
      inner ℝ z (finitePreparationMoment target) := by
  rw [inner_finitePreparationMoment]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun i _ => h_nonneg i) (Finset.mem_univ i₀)) (by positivity)

variable [CompleteSpace F]

/-- Any collision above `threshold` forces the dynamical/preparation alignment to cover the amount
left after subtracting the completed baseline. -/
theorem twoMemory_dynamicAlignment_ge_of_collision_ge
    (PiOp P : F →L[ℝ] F) (U : F ≃ₗᵢ[ℝ] F) (x y : F)
    (hPisa : IsSelfAdjoint PiOp)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z)
    (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPU : ∀ z, P (U z) = P z)
    (hPiy : PiOp y = PiOp x)
    {threshold : ℝ} (hcollision : threshold ≤ inner ℝ (U x) y) :
    threshold -
        (inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
          inner ℝ (staticMemory PiOp P x) (preparationMemory PiOp x y)) ≤
      inner ℝ (dynamicMemory P U x) (preparationMemory PiOp x y) := by
  have hdecomp := twoMemory_collision PiOp P U x y hPisa hPiid hPiP hPU hPiy
  rw [hdecomp] at hcollision
  linarith

/-- **Complete dictionary shortcut law.** One target collision of size at least `a` forces
realignment by its inverse-dictionary contribution minus the completed baseline. -/
theorem one_target_forces_memory_realign
    (PiOp P : F →L[ℝ] F) (U : F ≃ₗᵢ[ℝ] F) (x : F)
    (target : I → F) (i₀ : I)
    (hPisa : IsSelfAdjoint PiOp)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z)
    (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPU : ∀ z, P (U z) = P z)
    (hPiMoment : PiOp (finitePreparationMoment target) = PiOp x)
    (h_nonneg : ∀ i, 0 ≤ inner ℝ (U x) (target i))
    {a : ℝ} (ha : a ≤ inner ℝ (U x) (target i₀)) :
    (Fintype.card I : ℝ)⁻¹ * a -
        (inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
          inner ℝ (staticMemory PiOp P x)
            (preparationMemory PiOp x (finitePreparationMoment target))) ≤
      inner ℝ (dynamicMemory P U x)
        (preparationMemory PiOp x (finitePreparationMoment target)) := by
  have hfloor := one_collision_le_inner_finitePreparationMoment
    (z := U x) target i₀ h_nonneg
  have hthreshold : (Fintype.card I : ℝ)⁻¹ * a ≤
      inner ℝ (U x) (finitePreparationMoment target) := by
    exact le_trans (mul_le_mul_of_nonneg_left ha (by positivity)) hfloor
  exact twoMemory_dynamicAlignment_ge_of_collision_ge PiOp P U x
    (finitePreparationMoment target) hPisa hPiid hPiP hPU hPiMoment hthreshold

/-- **Recurrence realignment law.** At exact recurrence, a normalized seed target forces alignment
by one inverse dictionary size minus the completed baseline. -/
theorem recurrence_forces_memory_realign
    (PiOp P : F →L[ℝ] F) (U : F ≃ₗᵢ[ℝ] F) (x : F)
    (target : I → F) (i₀ : I)
    (hPisa : IsSelfAdjoint PiOp)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z)
    (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPU : ∀ z, P (U z) = P z)
    (hPiMoment : PiOp (finitePreparationMoment target) = PiOp x)
    (hrec : U x = x) (htarget : target i₀ = x) (hnorm : ‖x‖ = 1)
    (h_nonneg : ∀ i, 0 ≤ inner ℝ (U x) (target i)) :
    (Fintype.card I : ℝ)⁻¹ -
        (inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
          inner ℝ (staticMemory PiOp P x)
            (preparationMemory PiOp x (finitePreparationMoment target))) ≤
      inner ℝ (dynamicMemory P U x)
        (preparationMemory PiOp x (finitePreparationMoment target)) := by
  have hfloor := one_collision_le_inner_finitePreparationMoment
    (z := U x) target i₀ h_nonneg
  have hi : inner ℝ (U x) (target i₀) = 1 := by
    rw [hrec, htarget, real_inner_self_eq_norm_sq, hnorm]
    norm_num
  rw [hi, mul_one] at hfloor
  exact twoMemory_dynamicAlignment_ge_of_collision_ge PiOp P U x
    (finitePreparationMoment target) hPisa hPiid hPiP hPU hPiMoment hfloor

end RealCollision

end GaloisForLFunctions.HTGeometry
