import GaloisForLFunctions.RHTower.SelbergMaassFiniteIndexTrace

/-!
# Maass trace to a principal congruence target

A finite-index trace to the embedded principal congruence group preserves the
actual Maass equation and integral-cusp decay. Its coset summands are inverse
integral pullbacks, so this is a closed analytic trace construction, not only an
abstract invariant-function average. A trace may vanish; this file keeps that
alternative explicit.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint
open scoped MatrixGroups ContDiff

noncomputable section

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex (principalCongruenceGL N)]

local notation "ℋ" => principalCongruenceGL N
local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

local instance : MulAction ℋ ℋ := Monoid.toMulAction ..
local instance : MulAction ℋ 𝒬 := .quotient ..

private theorem principalTrace_component_eigen (N : ℕ) (lam : ℝ)
    (f : upperHalfPlaneInvariantFunctions 𝒢) (hf : IsMaassEigenfunction lam f.1) (q : 𝒬) :
    IsMaassEigenfunction lam (maassTraceQuotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h r =>
    simpa only [maassTraceQuotientFunc_mk] using
      (show IsMaassEigenfunction lam (fun z => f.1 (r.val⁻¹ • z)) from by
        obtain ⟨A, hA, hEq⟩ := r.2
        rw [← hEq]
        simpa only [Matrix.SpecialLinearGroup.mapGL_inv, ModularGroup.sl_moeb] using
          SelbergMaassCuspTransport.eigenfunction_pullback A⁻¹ lam f.1 hf)

private theorem principalTrace_component_cusp (N : ℕ)
    (f : upperHalfPlaneInvariantFunctions 𝒢) (hf : IsCuspidalAtIntegralCusps f.1) (q : 𝒬) :
    IsCuspidalAtIntegralCusps (maassTraceQuotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h r =>
    simpa only [maassTraceQuotientFunc_mk] using
      (show IsCuspidalAtIntegralCusps (fun z => f.1 (r.val⁻¹ • z)) from by
        obtain ⟨A, hA, hEq⟩ := r.2
        rw [← hEq]
        simpa only [Matrix.SpecialLinearGroup.mapGL_inv, ModularGroup.sl_moeb] using
          SelbergMaassCuspTransport.cuspidal_pullback A⁻¹ f.1 hf)

/-- The finite principal trace retains real `C²` upper-half-plane regularity. -/
theorem principalMaassTrace_smooth (N : ℕ) (lam : ℝ) (f : GLMaassCuspEigenform 𝒢 lam) :
    IsRealSmoothUpperHalfPlane (maassTraceFunction f.1) := by
  letI := Fintype.ofFinite 𝒬
  unfold maassTraceFunction
  exact ContDiffOn.sum (fun q _ => (principalTrace_component_eigen N lam f.1 f.2.2.1 q).1)

/-- The finite principal trace has the unchanged Maass eigenvalue. -/
theorem principalMaassTrace_eigen (N : ℕ) (lam : ℝ) (f : GLMaassCuspEigenform 𝒢 lam) (z : ℍ) :
    positiveHyperbolicLaplacian (maassTraceFunction f.1) z =
      (lam : ℂ) * maassTraceFunction f.1 z := by
  letI := Fintype.ofFinite 𝒬
  have hq (q : 𝒬) : ContDiffAt ℝ 2 (maassTraceQuotientFunc f.1 q ∘ ofComplex) (z : ℂ) :=
    (principalTrace_component_eigen N lam f.1 f.2.2.1 q).1.contDiffAt
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  simp only [Function.comp_def] at hq
  change -(z.im : ℂ) ^ 2 *
    (dir 1 (dir 1 (fun w : ℂ => ∑ q : 𝒬, maassTraceQuotientFunc f.1 q (ofComplex w))) (z : ℂ) +
      dir Complex.I (dir Complex.I (fun w : ℂ => ∑ q : 𝒬,
        maassTraceQuotientFunc f.1 q (ofComplex w))) (z : ℂ)) = _
  rw [second_dir_sum Finset.univ (fun q _ => hq q),
    second_dir_sum Finset.univ (fun q _ => hq q), ← Finset.sum_add_distrib, Finset.mul_sum]
  change (∑ q : 𝒬, positiveHyperbolicLaplacian (maassTraceQuotientFunc f.1 q) z) =
    (lam : ℂ) * ∑ q : 𝒬, maassTraceQuotientFunc f.1 q z
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl
    (fun q _ => (principalTrace_component_eigen N lam f.1 f.2.2.1 q).2 z)

/-- The finite principal trace preserves every integral-cusp decay condition. -/
theorem principalMaassTrace_cuspidal (N : ℕ) (lam : ℝ) (f : GLMaassCuspEigenform 𝒢 lam) :
    IsCuspidalAtIntegralCusps (maassTraceFunction f.1) := by
  intro A
  letI := Fintype.ofFinite 𝒬
  change Tendsto (fun z : ℍ => ∑ q : 𝒬,
    maassTraceQuotientFunc f.1 q (integralSL2ToReal A • z)) atImInfty (𝓝 0)
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
    (fun q _ => principalTrace_component_cusp N f.1 f.2.2.2 q A)

/-- The principal trace, with its exact invariant, eigenfunction, and cusp data. -/
def principalMaassTraceData (N : ℕ) (lam : ℝ) (f : GLMaassCuspEigenform 𝒢 lam) :
    {F : upperHalfPlaneInvariantFunctions (principalCongruenceGL N) //
      IsMaassEigenfunction lam F.1 ∧ IsCuspidalAtIntegralCusps F.1} :=
  ⟨maassTraceInvariant f.1,
    ⟨⟨principalMaassTrace_smooth N lam f, principalMaassTrace_eigen N lam f⟩,
      principalMaassTrace_cuspidal N lam f⟩⟩

/-- A principal Maass trace either vanishes or yields a bundled nonzero Maass eigenform
at the principal target with the same eigenvalue. -/
theorem principalMaassTrace_zero_or_eigenform (N : ℕ) (lam : ℝ)
    (f : GLMaassCuspEigenform 𝒢 lam) :
    maassTraceFunction f.1 = 0 ∨
      ∃ F : GLMaassCuspEigenform (principalCongruenceGL N) lam, F.1.1 = maassTraceFunction f.1 := by
  classical
  by_cases hzero : maassTraceFunction f.1 = 0
  · exact Or.inl hzero
  · refine Or.inr ⟨⟨(principalMaassTraceData N lam f).1, ?_,
      (principalMaassTraceData N lam f).2.1, (principalMaassTraceData N lam f).2.2⟩, rfl⟩
    intro h
    exact hzero (congrArg Subtype.val h)

end

end GaloisForLFunctions.RHTower
