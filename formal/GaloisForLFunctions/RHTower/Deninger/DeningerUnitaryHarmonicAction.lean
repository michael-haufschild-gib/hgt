import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticUnitaryBRSTHodge

/-!
# The unitary action on the BRST harmonic sector

A unitary chain symmetry `U` of a bounded differential `Q` commutes with the adjoint and hence
with the BRST--Hodge Hamiltonian.  The harmonic sector `ker Δ_Q = ker Q ∩ ker Q†` is therefore
not merely stable under `U`: since `U†` is also a unitary chain symmetry, `U` restricts to a
bijection of the harmonic sector, and it preserves the inner product there.

So a finite Deninger packet needs no separate Laplacian-equivariance axiom and no separate
unitarity axiom on harmonic cohomology: both are consequences of `U` being unitary and a chain
map.

* `deningerBRSTHarmonic_eq_ker` : `ker Q ⊓ ker Q† = ker Δ_Q`.
* `deningerUnitary_harmonic_bijective` : `U` is a bijection of the harmonic sector.
* `deningerHarmonicUnitary` : the induced unitary of the harmonic sector.
-/

namespace RHTower

section UnitaryHarmonic

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The harmonic sector of a bounded differential. -/
noncomputable def deningerBRSTHarmonic (Q : E →L[𝕜] E) : Submodule 𝕜 E :=
  LinearMap.ker (Q : E →L[𝕜] E).toLinearMap ⊓
    LinearMap.ker (ContinuousLinearMap.adjoint Q).toLinearMap

theorem mem_deningerBRSTHarmonic {Q : E →L[𝕜] E} {x : E} :
    x ∈ deningerBRSTHarmonic Q ↔ Q x = 0 ∧ ContinuousLinearMap.adjoint Q x = 0 :=
  Iff.rfl

/-- **The harmonic sector is the kernel of the BRST--Hodge Hamiltonian.** -/
theorem deningerBRSTHarmonic_eq_ker (Q : E →L[𝕜] E) :
    deningerBRSTHarmonic Q
      = LinearMap.ker (HTGeometry.brstHodgeHamiltonian Q).toLinearMap := by
  ext x
  rw [LinearMap.mem_ker]
  exact (HTGeometry.brstHodgeHamiltonian_apply_eq_zero_iff Q x).symm

/-- Applying the two-sided inverse relation of a unitary. -/
theorem deningerUnitary_apply_adjoint_apply {U : E →L[𝕜] E}
    (hUUadjoint : U * ContinuousLinearMap.adjoint U = 1) (x : E) :
    U (ContinuousLinearMap.adjoint U x) = x := by
  have h := congrArg (fun T : E →L[𝕜] E => T x) hUUadjoint
  simpa using h

theorem deningerUnitary_adjoint_apply_apply {U : E →L[𝕜] E}
    (hadjointU : ContinuousLinearMap.adjoint U * U = 1) (x : E) :
    ContinuousLinearMap.adjoint U (U x) = x := by
  have h := congrArg (fun T : E →L[𝕜] E => T x) hadjointU
  simpa using h

/-- A two-sided unitary preserves the norm. -/
theorem deningerUnitary_norm_apply {U : E →L[𝕜] E}
    (hadjointU : ContinuousLinearMap.adjoint U * U = 1) (x : E) :
    ‖U x‖ = ‖x‖ := by
  have hUx : ContinuousLinearMap.adjoint U (U x) = x :=
    deningerUnitary_adjoint_apply_apply hadjointU x
  have hinner : (inner 𝕜 (U x) (U x) : 𝕜) = inner 𝕜 x x := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hUx]
  have hre := congrArg (RCLike.re (K := 𝕜)) hinner
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at hre
  nlinarith [norm_nonneg (U x), norm_nonneg x]

/-- A two-sided unitary preserves the inner product. -/
theorem deningerUnitary_inner_apply {U : E →L[𝕜] E}
    (hadjointU : ContinuousLinearMap.adjoint U * U = 1) (x y : E) :
    (inner 𝕜 (U x) (U y) : 𝕜) = inner 𝕜 x y := by
  rw [← ContinuousLinearMap.adjoint_inner_left,
    deningerUnitary_adjoint_apply_apply hadjointU x]

/-- The adjoint of a unitary chain symmetry is again a chain symmetry. -/
theorem deningerUnitary_adjoint_commutes {U Q : E →L[𝕜] E}
    (hUUadjoint : U * ContinuousLinearMap.adjoint U = 1)
    (hadjointU : ContinuousLinearMap.adjoint U * U = 1)
    (hUQ : U * Q = Q * U) :
    ContinuousLinearMap.adjoint U * Q = Q * ContinuousLinearMap.adjoint U := by
  have h2 : U * ContinuousLinearMap.adjoint Q = ContinuousLinearMap.adjoint Q * U :=
    deningerUnitary_commutes_adjoint_of_commutes U Q hUUadjoint hadjointU hUQ
  have h := congrArg ContinuousLinearMap.adjoint h2
  simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp] using h.symm

omit [CompleteSpace E] in
/-- A unitary chain symmetry preserves `ker Q`. -/
theorem deningerUnitary_mem_ker {U Q : E →L[𝕜] E} (hUQ : U * Q = Q * U)
    {x : E} (hx : Q x = 0) : Q (U x) = 0 := by
  have h : U (Q x) = Q (U x) := by
    have h0 := congrArg (fun T : E →L[𝕜] E => T x) hUQ
    simpa using h0
  rw [hx, map_zero] at h
  exact h.symm

/-- A unitary chain symmetry preserves the harmonic sector. -/
theorem deningerUnitary_mem_harmonic {U Q : E →L[𝕜] E}
    (hUUadjoint : U * ContinuousLinearMap.adjoint U = 1)
    (hadjointU : ContinuousLinearMap.adjoint U * U = 1)
    (hUQ : U * Q = Q * U)
    {x : E} (hx : x ∈ deningerBRSTHarmonic Q) : U x ∈ deningerBRSTHarmonic Q := by
  obtain ⟨hQ, hQa⟩ := hx
  refine ⟨deningerUnitary_mem_ker hUQ hQ, ?_⟩
  exact deningerUnitary_mem_ker
    (deningerUnitary_commutes_adjoint_of_commutes U Q hUUadjoint hadjointU hUQ) hQa

/-- The adjoint of a unitary chain symmetry preserves the harmonic sector. -/
theorem deningerUnitary_adjoint_mem_harmonic {U Q : E →L[𝕜] E}
    (hUUadjoint : U * ContinuousLinearMap.adjoint U = 1)
    (hadjointU : ContinuousLinearMap.adjoint U * U = 1)
    (hUQ : U * Q = Q * U)
    {x : E} (hx : x ∈ deningerBRSTHarmonic Q) :
    ContinuousLinearMap.adjoint U x ∈ deningerBRSTHarmonic Q := by
  refine deningerUnitary_mem_harmonic (U := ContinuousLinearMap.adjoint U) ?_ ?_ ?_ hx
  · rw [ContinuousLinearMap.adjoint_adjoint]
    exact hadjointU
  · rw [ContinuousLinearMap.adjoint_adjoint]
    exact hUUadjoint
  · exact deningerUnitary_adjoint_commutes hUUadjoint hadjointU hUQ

/-- **The unitary chain symmetry acts bijectively on the harmonic sector.** -/
theorem deningerUnitary_harmonic_bijective {U Q : E →L[𝕜] E}
    (hUUadjoint : U * ContinuousLinearMap.adjoint U = 1)
    (hadjointU : ContinuousLinearMap.adjoint U * U = 1)
    (hUQ : U * Q = Q * U) :
    Function.Bijective
      (fun x : deningerBRSTHarmonic Q =>
        (⟨U x, deningerUnitary_mem_harmonic hUUadjoint hadjointU hUQ x.2⟩ :
          deningerBRSTHarmonic Q)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun y => ⟨ContinuousLinearMap.adjoint U y,
      deningerUnitary_adjoint_mem_harmonic hUUadjoint hadjointU hUQ y.2⟩, ?_, ?_⟩
  · intro x
    exact Subtype.ext (deningerUnitary_adjoint_apply_apply hadjointU (x : E))
  · intro y
    exact Subtype.ext (deningerUnitary_apply_adjoint_apply hUUadjoint (y : E))

/-- **The unitary of the harmonic sector induced by a unitary chain symmetry.**  No separate
spectral or equivariance hypothesis is used: unitarity and the chain-map property suffice. -/
noncomputable def deningerHarmonicUnitary (U Q : E →L[𝕜] E)
    (hUUadjoint : U * ContinuousLinearMap.adjoint U = 1)
    (hadjointU : ContinuousLinearMap.adjoint U * U = 1)
    (hUQ : U * Q = Q * U) :
    deningerBRSTHarmonic Q ≃ₗᵢ[𝕜] deningerBRSTHarmonic Q where
  toFun x := ⟨U x, deningerUnitary_mem_harmonic hUUadjoint hadjointU hUQ x.2⟩
  invFun y := ⟨ContinuousLinearMap.adjoint U y,
    deningerUnitary_adjoint_mem_harmonic hUUadjoint hadjointU hUQ y.2⟩
  map_add' x y := Subtype.ext (map_add U (x : E) (y : E))
  map_smul' c x := Subtype.ext (map_smul U c (x : E))
  left_inv x := Subtype.ext (deningerUnitary_adjoint_apply_apply hadjointU (x : E))
  right_inv y := Subtype.ext (deningerUnitary_apply_adjoint_apply hUUadjoint (y : E))
  norm_map' x := deningerUnitary_norm_apply hadjointU (x : E)

@[simp] theorem deningerHarmonicUnitary_coe (U Q : E →L[𝕜] E)
    (hUUadjoint : U * ContinuousLinearMap.adjoint U = 1)
    (hadjointU : ContinuousLinearMap.adjoint U * U = 1)
    (hUQ : U * Q = Q * U) (x : deningerBRSTHarmonic Q) :
    ((deningerHarmonicUnitary U Q hUUadjoint hadjointU hUQ x : deningerBRSTHarmonic Q) : E)
      = U x := rfl

/-- The induced harmonic unitary preserves the inner product. -/
theorem deningerHarmonicUnitary_inner (U Q : E →L[𝕜] E)
    (hUUadjoint : U * ContinuousLinearMap.adjoint U = 1)
    (hadjointU : ContinuousLinearMap.adjoint U * U = 1)
    (hUQ : U * Q = Q * U) (x y : deningerBRSTHarmonic Q) :
    (inner 𝕜 (deningerHarmonicUnitary U Q hUUadjoint hadjointU hUQ x)
        (deningerHarmonicUnitary U Q hUUadjoint hadjointU hUQ y) : 𝕜)
      = inner 𝕜 x y :=
  deningerUnitary_inner_apply hadjointU (x : E) (y : E)

end UnitaryHarmonic

end RHTower
