import GaloisForLFunctions.HTGeometry.PullbackCompletion
import GaloisForLFunctions.HTGeometry.DilationSpectralType

/-!
# The pullback-completion verdict

Complete a test domain in the norm of the image of a linear map into a Hilbert space.  The
completion is the closure of the range, a closed subspace of the ambient space.  Any operator on
that completion which restricts the ambient operator inherits its spectral type: if the ambient
operator has no eigenvectors, neither does the restriction, and if the restriction is self-adjoint
the ambient resolvent preserves the completion.

Applied to a generator with no point spectrum — after the logarithmic and Fourier unitaries a
multiplication operator whose symbol has null level sets — this says that no boundary condition
imposed inside such a pullback completion can create point spectrum.
-/

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

variable {D K : Type*} [AddCommGroup D] [Module ℂ D]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- **The pullback completion has no point spectrum.**  Every operator on the pullback completion
that restricts an eigenvector-free ambient operator is itself eigenvector-free. -/
theorem pullbackCompletion_hasNoEigenvector {A : K →ₗ.[ℂ] K} (hA : HasNoEigenvector A)
    (Δ : D →ₗ[ℂ] K) {B : (pullbackSpace Δ) →ₗ.[ℂ] (pullbackSpace Δ)}
    (hres : IsPMapRestriction A (pullbackSpace Δ) B) : HasNoEigenvector B :=
  hasNoEigenvector_of_restriction hres hA

/-- **The pullback completion reduces the ambient operator.**  If the restriction is self-adjoint,
every solution of `(A - z) x = y` with `y` in the pullback completion already lies there. -/
theorem pullbackCompletion_resolvent_mem {A : K →ₗ.[ℂ] K} (hA : IsSelfAdjoint A)
    (Δ : D →ₗ[ℂ] K) {B : (pullbackSpace Δ) →ₗ.[ℂ] (pullbackSpace Δ)} (hB : IsSelfAdjoint B)
    (hres : IsPMapRestriction A (pullbackSpace Δ) B) {z : ℂ} (hz : z.im ≠ 0) {y : K}
    (hy : y ∈ pullbackSpace Δ) {x : A.domain} (hx : shiftedMap A z x = y) :
    (x : K) ∈ pullbackSpace Δ :=
  mem_of_shiftedMap_eq hA hB hres hz hy hx

omit [CompleteSpace K] in
/-- **The multiplication model has no point spectrum in any pullback completion.**  Combining the
two previous statements with the multiplication criterion: if the ambient generator is unitarily
conjugate to a multiplication operator whose symbol has null level sets, then no self-adjoint
operator on a pullback completion of it has an eigenvector. -/
theorem pullbackCompletion_multiplication_hasNoEigenvector
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (U : K ≃ₗᵢ[ℂ] (MeasureTheory.Lp ℂ 2 μ))
    {T : (MeasureTheory.Lp ℂ 2 μ) →ₗ.[ℂ] (MeasureTheory.Lp ℂ 2 μ)} {g : α → ℂ}
    (hT : ∀ f : T.domain,
      (T f : α → ℂ) =ᵐ[μ] fun x => g x * ((f : MeasureTheory.Lp ℂ 2 μ) : α → ℂ) x)
    (hlevel : ∀ lam : ℂ, μ {x | g x = lam} = 0)
    (Δ : D →ₗ[ℂ] K)
    {B : (pullbackSpace Δ) →ₗ.[ℂ] (pullbackSpace Δ)}
    (hres : IsPMapRestriction (unitaryConjugateLinearPMap U T) (pullbackSpace Δ) B) :
    HasNoEigenvector B :=
  hasNoEigenvector_of_restriction hres
    (hasNoEigenvector_unitaryConjugate U (hasNoEigenvector_of_multiplication hT hlevel))

end RHTower
