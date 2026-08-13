import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Gauge spectral-flow rigidity and crossing tensors

This file isolates the finite-dimensional algebra at one regular crossing.  A unitary gauge sends
the Hessian to a conjugate operator.  Differentiating that conjugation adds the commutator
`[K,H]`; on the zero-mode space both commutator terms vanish against the inner product.  Hence the
crossing tensor and its nondegeneracy are gauge invariant.  The same conjugation preserves the
ordered eigenvalue list and inertia, so a pure unitary gauge path has zero finite-dimensional
spectral flow.  No determinant phase or choice of eigenvectors enters these statements.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.GaugeSpectralFlow

open scoped InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

abbrev End := Module.End 𝕜 E

/-! ## Unitary conjugation and inertia -/

/-- Unitary conjugation of a Hessian. -/
def conjugate (U : E ≃ₗᵢ[𝕜] E) (H : End (𝕜 := 𝕜) (E := E)) : End (𝕜 := 𝕜) (E := E) :=
  U.toLinearEquiv.conj H

@[simp]
theorem conjugate_apply_map (U : E ≃ₗᵢ[𝕜] E) (H : End (𝕜 := 𝕜) (E := E)) (x : E) :
    conjugate U H (U x) = U (H x) := by
  simp [conjugate, LinearEquiv.conj_apply]

@[simp]
theorem conjugate_apply_symm (U : E ≃ₗᵢ[𝕜] E) (H : End (𝕜 := 𝕜) (E := E)) (x : E) :
    conjugate U H x = U (H (U.symm x)) := by
  simp [conjugate, LinearEquiv.conj_apply]

/-- Unitary conjugation identifies the zero-mode spaces pointwise. -/
theorem conjugate_apply_map_eq_zero_iff
    (U : E ≃ₗᵢ[𝕜] E) (H : End (𝕜 := 𝕜) (E := E)) (x : E) :
    conjugate U H (U x) = 0 ↔ H x = 0 := by
  rw [conjugate_apply_map]
  exact U.map_eq_zero_iff

/-- Self-adjointness is preserved by unitary conjugation. -/
theorem conjugate_isSymmetric
    (U : E ≃ₗᵢ[𝕜] E) {H : End (𝕜 := 𝕜) (E := E)} (hH : H.IsSymmetric) :
    (conjugate U H).IsSymmetric := by
  intro x y
  calc
    inner 𝕜 (conjugate U H x) y =
        inner 𝕜 (H (U.symm x)) (U.symm y) := by
      simpa using U.inner_map_map (H (U.symm x)) (U.symm y)
    _ = inner 𝕜 (U.symm x) (H (U.symm y)) := hH _ _
    _ = inner 𝕜 x (conjugate U H y) := by
      simpa using (U.inner_map_map (U.symm x) (H (U.symm y))).symm

section FiniteDimension

variable [FiniteDimensional 𝕜 E]

/-- Similar Hessians have identical characteristic polynomials. -/
theorem conjugate_charpoly (U : E ≃ₗᵢ[𝕜] E) (H : End (𝕜 := 𝕜) (E := E)) :
    (conjugate U H).charpoly = H.charpoly := by
  simp [conjugate]

/-- Ordered real eigenvalues of a self-adjoint Hessian are unchanged by unitary gauge. -/
theorem conjugate_eigenvalues
    (U : E ≃ₗᵢ[𝕜] E) {H : End (𝕜 := 𝕜) (E := E)} (hH : H.IsSymmetric) :
    (conjugate_isSymmetric U hH).eigenvalues rfl = hH.eigenvalues rfl := by
  apply ((conjugate_isSymmetric U hH).eigenvalues_eq_eigenvalues_iff rfl hH rfl).2
  exact conjugate_charpoly U H

/-- Number of negative eigenvalues, counted with multiplicity. -/
noncomputable def negativeIndex
    (H : End (𝕜 := 𝕜) (E := E)) (hH : H.IsSymmetric) : ℕ :=
  Finset.card (Finset.univ.filter fun i => hH.eigenvalues rfl i < 0)

/-- Number of positive eigenvalues, counted with multiplicity. -/
noncomputable def positiveIndex
    (H : End (𝕜 := 𝕜) (E := E)) (hH : H.IsSymmetric) : ℕ :=
  Finset.card (Finset.univ.filter fun i => 0 < hH.eigenvalues rfl i)

/-- Positive index, negative index, and nullity of a finite-dimensional Hessian. -/
noncomputable def inertia
    (H : End (𝕜 := 𝕜) (E := E)) (hH : H.IsSymmetric) : ℕ × ℕ × ℕ :=
  (positiveIndex H hH, negativeIndex H hH, Module.finrank 𝕜 (LinearMap.ker H))

theorem negativeIndex_conjugate
    (U : E ≃ₗᵢ[𝕜] E) {H : End (𝕜 := 𝕜) (E := E)} (hH : H.IsSymmetric) :
    negativeIndex (conjugate U H) (conjugate_isSymmetric U hH) = negativeIndex H hH := by
  simp only [negativeIndex, conjugate_eigenvalues U hH]

theorem positiveIndex_conjugate
    (U : E ≃ₗᵢ[𝕜] E) {H : End (𝕜 := 𝕜) (E := E)} (hH : H.IsSymmetric) :
    positiveIndex (conjugate U H) (conjugate_isSymmetric U hH) = positiveIndex H hH := by
  simp only [positiveIndex, conjugate_eigenvalues U hH]

/-- Unitary conjugation preserves positive index, negative index, and zero-mode multiplicity. -/
theorem inertia_conjugate
    (U : E ≃ₗᵢ[𝕜] E) {H : End (𝕜 := 𝕜) (E := E)} (hH : H.IsSymmetric) :
    inertia (conjugate U H) (conjugate_isSymmetric U hH) = inertia H hH := by
  apply Prod.ext
  · exact positiveIndex_conjugate U hH
  · apply Prod.ext
    · exact negativeIndex_conjugate U hH
    · let e : LinearMap.ker H ≃ₗ[𝕜] LinearMap.ker (conjugate U H) :=
        LinearEquiv.ofBijective
          ((U.toLinearEquiv.toLinearMap).domRestrict (LinearMap.ker H) |>.codRestrict
            (LinearMap.ker (conjugate U H))
            (fun x => by
              rw [LinearMap.mem_ker]
              exact (conjugate_apply_map_eq_zero_iff U H x).2 x.property))
          ⟨fun _ _ h => Subtype.ext (U.injective (congrArg Subtype.val h)), fun y => by
            let x : LinearMap.ker H :=
              ⟨U.symm y, by
                change H (U.symm y) = 0
                rw [← conjugate_apply_map_eq_zero_iff U H]
                rw [U.apply_symm_apply]
                exact y.property⟩
            exact ⟨x, Subtype.ext (U.apply_symm_apply y)⟩⟩
      exact LinearEquiv.finrank_eq e.symm

/-- Finite-dimensional spectral flow between invertible endpoints is the negative-index drop. -/
noncomputable def finiteSpectralFlow
    (H₀ H₁ : End (𝕜 := 𝕜) (E := E))
    (h₀ : H₀.IsSymmetric) (h₁ : H₁.IsSymmetric) : ℤ :=
  (negativeIndex H₀ h₀ : ℤ) - negativeIndex H₁ h₁

/-- A pure unitary gauge path has zero finite-dimensional spectral flow. -/
theorem finiteSpectralFlow_conjugate_zero
    (U : E ≃ₗᵢ[𝕜] E) {H : End (𝕜 := 𝕜) (E := E)} (hH : H.IsSymmetric) :
    finiteSpectralFlow H (conjugate U H) hH (conjugate_isSymmetric U hH) = 0 := by
  simp [finiteSpectralFlow, negativeIndex_conjugate U hH]

end FiniteDimension

/-! ## Crossing tensors -/

/-- Commutator contribution produced by differentiating a gauge conjugation. -/
def commutator (K H : End (𝕜 := 𝕜) (E := E)) : End (𝕜 := 𝕜) (E := E) :=
  K.comp H - H.comp K

/-- Derivative of `U(t) H(t) U(t)⁻¹`, pulled through the current unitary gauge. -/
def gaugeDerivative
    (U : E ≃ₗᵢ[𝕜] E) (H Hdot K : End (𝕜 := 𝕜) (E := E)) :
    End (𝕜 := 𝕜) (E := E) :=
  conjugate U (Hdot + commutator K H)

/-- Crossing tensor obtained by restricting the Hessian derivative to zero modes. -/
def crossingForm (Hdot : End (𝕜 := 𝕜) (E := E)) (x y : E) : 𝕜 :=
  inner 𝕜 x (Hdot y)

/-- Gauge commutator terms vanish on the zero-mode space. -/
theorem crossingForm_commutator_eq_zero
    {H : End (𝕜 := 𝕜) (E := E)} (hH : H.IsSymmetric)
    (K : End (𝕜 := 𝕜) (E := E)) {x y : E} (hx : H x = 0) (hy : H y = 0) :
    crossingForm (commutator K H) x y = 0 := by
  have hsecond : inner 𝕜 x (H (K y)) = 0 := by
    rw [← hH x (K y), hx, inner_zero_left]
  simp [crossingForm, commutator, LinearMap.comp_apply, hy, hsecond]

/-- The crossing tensor is invariant under a differentiable unitary gauge jet. -/
theorem crossingForm_gauge_invariant
    (U : E ≃ₗᵢ[𝕜] E) {H : End (𝕜 := 𝕜) (E := E)} (hH : H.IsSymmetric)
    (Hdot K : End (𝕜 := 𝕜) (E := E)) {x y : E} (hx : H x = 0) (hy : H y = 0) :
    crossingForm (gaugeDerivative U H Hdot K) (U x) (U y) = crossingForm Hdot x y := by
  rw [crossingForm, gaugeDerivative, conjugate_apply_map, U.inner_map_map]
  change inner 𝕜 x ((Hdot + commutator K H) y) = inner 𝕜 x (Hdot y)
  rw [LinearMap.add_apply, inner_add_right]
  have hcomm := crossingForm_commutator_eq_zero hH K hx hy
  change inner 𝕜 x ((commutator K H) y) = 0 at hcomm
  rw [hcomm, add_zero]

/-- Nondegeneracy of the crossing tensor on the Hessian kernel. -/
def IsRegularCrossing
    (H Hdot : End (𝕜 := 𝕜) (E := E)) : Prop :=
  ∀ x, H x = 0 → (∀ y, H y = 0 → crossingForm Hdot x y = 0) → x = 0

/-- Regularity of a crossing is invariant under unitary gauge. -/
theorem regularCrossing_gauge_iff
    (U : E ≃ₗᵢ[𝕜] E) {H : End (𝕜 := 𝕜) (E := E)} (hH : H.IsSymmetric)
    (Hdot K : End (𝕜 := 𝕜) (E := E)) :
    IsRegularCrossing (conjugate U H) (gaugeDerivative U H Hdot K) ↔
      IsRegularCrossing H Hdot := by
  constructor
  · intro hregular x hx horth
    have hUx : U x = 0 := hregular (U x)
      ((conjugate_apply_map_eq_zero_iff U H x).2 hx) (fun y hy => by
        let z := U.symm y
        have hz : H z = 0 := by
          rw [← conjugate_apply_map_eq_zero_iff U H]
          simpa [z] using hy
        have hzero := horth z hz
        simpa [z] using
          (crossingForm_gauge_invariant U hH Hdot K hx hz).trans hzero)
    exact U.injective (by simpa using hUx)
  · intro hregular x hx horth
    let z := U.symm x
    have hz : H z = 0 := by
      rw [← conjugate_apply_map_eq_zero_iff U H]
      simpa [z] using hx
    have hzzero : z = 0 := hregular z hz (fun y hy => by
      have hzero := horth (U y) ((conjugate_apply_map_eq_zero_iff U H y).2 hy)
      have hxrep : U z = x := by simp [z]
      rw [← hxrep] at hzero
      exact (crossingForm_gauge_invariant U hH Hdot K hz hy).symm.trans hzero)
    rw [← U.apply_symm_apply x, show U.symm x = z by rfl, hzzero, map_zero]

/-- Persistent pure-gauge zero modes have identically zero crossing tensor. -/
theorem pureGauge_crossingForm_eq_zero
    {H : End (𝕜 := 𝕜) (E := E)} (hH : H.IsSymmetric)
    (K : End (𝕜 := 𝕜) (E := E)) {x y : E} (hx : H x = 0) (hy : H y = 0) :
    crossingForm (commutator K H) x y = 0 :=
  crossingForm_commutator_eq_zero hH K hx hy

/-- A pure-gauge derivative cannot make a nontrivial persistent zero mode into a regular crossing. -/
theorem pureGauge_not_regular_of_nontrivial_kernel
    {H : End (𝕜 := 𝕜) (E := E)} (hH : H.IsSymmetric)
    (K : End (𝕜 := 𝕜) (E := E)) {x : E} (hx : H x = 0) (hx0 : x ≠ 0) :
    ¬ IsRegularCrossing H (commutator K H) := by
  intro hregular
  exact hx0 (hregular x hx fun y hy => pureGauge_crossingForm_eq_zero hH K hx hy)

end HTGeometry.NomologicalHomotopyGeometry.GaugeSpectralFlow
