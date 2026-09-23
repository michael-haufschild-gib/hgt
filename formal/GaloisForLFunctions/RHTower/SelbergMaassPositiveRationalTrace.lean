import GaloisForLFunctions.RHTower.SelbergMaassRationalTrace

/-!
# Finite Maass trace through positive rational lifts

If every element of a finite-index target subgroup is represented by an
orientation-preserving rational matrix, each trace summand is a rational
pullback. The trace therefore preserves the Maass equation and decay at all
integral cusps. This is the analytic input for stabilizer intersections in the
finite double-coset decomposition.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint
open SelbergMaassTraceEnergy
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

variable {G H : Subgroup (GL (Fin 2) ℝ)} [G.IsFiniteRelIndex H]

local notation "𝒬" => H ⧸ (G.subgroupOf H)

local instance selbergMaassPositiveRationalTraceInst1 : MulAction H H := Monoid.toMulAction ..
local instance selbergMaassPositiveRationalTraceInst2 : MulAction H 𝒬 := .quotient ..

omit [G.IsFiniteRelIndex H] in
theorem positiveRationalTrace_component_eigen
    (hH : HasPositiveRationalLifts H) (lam : ℝ)
    (f : glUpperHalfPlaneInvariantFunctions G) (hf : IsMaassEigenfunction lam f.1) (q : 𝒬) :
    IsMaassEigenfunction lam (maassTraceQuotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h r =>
    change IsMaassEigenfunction lam
      (fun z => maassTraceQuotientFunc f (QuotientGroup.mk r) z)
    simp only [maassTraceQuotientFunc_mk]
    obtain ⟨a, ha, hapos⟩ := hH r⁻¹
    change IsMaassEigenfunction lam (fun z => f.1 ((r⁻¹).val • z))
    rw [← ha]
    exact SelbergMaassCuspTransport.eigenfunction_pullback_gl
      (a.map (algebraMap ℚ ℝ)) hapos lam f.1 hf

omit [G.IsFiniteRelIndex H] in
private theorem positiveRationalTrace_component_cusp
    (hH : HasPositiveRationalLifts H)
    (f : glUpperHalfPlaneInvariantFunctions G) (hf : IsCuspidalAtIntegralCusps f.1) (q : 𝒬) :
    IsCuspidalAtIntegralCusps (maassTraceQuotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h r =>
    change IsCuspidalAtIntegralCusps
      (fun z => maassTraceQuotientFunc f (QuotientGroup.mk r) z)
    simp only [maassTraceQuotientFunc_mk]
    obtain ⟨a, ha, hapos⟩ := hH r⁻¹
    change IsCuspidalAtIntegralCusps (fun z => f.1 ((r⁻¹).val • z))
    rw [← ha]
    exact rationalGL_cuspidal_pullback a f.1 hf

/-- A finite trace into a target with positive rational lifts retains real `C²`
regularity. -/
theorem positiveRationalMaassTrace_smooth_of_data
    (hH : HasPositiveRationalLifts H) (lam : ℝ)
    (f : glUpperHalfPlaneInvariantFunctions G)
    (heigen : IsMaassEigenfunction lam f.1) :
    IsRealSmoothUpperHalfPlane (maassTraceFunction (H := H) f) := by
  letI := Fintype.ofFinite 𝒬
  unfold maassTraceFunction
  exact ContDiffOn.sum (fun q _ =>
    (positiveRationalTrace_component_eigen hH lam f heigen q).1)

/-- A finite trace into a target with positive rational lifts retains its Maass
eigen-equation. -/
theorem positiveRationalMaassTrace_eigen_of_data
    (hH : HasPositiveRationalLifts H) (lam : ℝ)
    (f : glUpperHalfPlaneInvariantFunctions G)
    (heigen : IsMaassEigenfunction lam f.1) (z : ℍ) :
    positiveHyperbolicLaplacian (maassTraceFunction (H := H) f) z =
      (lam : ℂ) * maassTraceFunction (H := H) f z := by
  letI := Fintype.ofFinite 𝒬
  have hq (q : 𝒬) : ContDiffAt ℝ 2 (maassTraceQuotientFunc f q ∘ ofComplex) (z : ℂ) :=
    (positiveRationalTrace_component_eigen hH lam f heigen q).1.contDiffAt
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  simp only [Function.comp_def] at hq
  change -(z.im : ℂ) ^ (2 : ℕ) *
    (dir 1 (dir 1 (fun w : ℂ => ∑ q : 𝒬, maassTraceQuotientFunc f q (ofComplex w))) (z : ℂ) +
      dir Complex.I (dir Complex.I (fun w : ℂ => ∑ q : 𝒬,
        maassTraceQuotientFunc f q (ofComplex w))) (z : ℂ)) = _
  rw [second_dir_sum Finset.univ (fun q _ => hq q),
    second_dir_sum Finset.univ (fun q _ => hq q), ← Finset.sum_add_distrib, Finset.mul_sum]
  change (∑ q : 𝒬, positiveHyperbolicLaplacian (maassTraceQuotientFunc f q) z) =
    (lam : ℂ) * ∑ q : 𝒬, maassTraceQuotientFunc f q z
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl
    (fun q _ => (positiveRationalTrace_component_eigen hH lam f heigen q).2 z)

/-- A finite trace into a target with positive rational lifts preserves decay at
every integral cusp. -/
theorem positiveRationalMaassTrace_cuspidal_of_data
    (hH : HasPositiveRationalLifts H)
    (f : glUpperHalfPlaneInvariantFunctions G)
    (hcusp : IsCuspidalAtIntegralCusps f.1) :
    IsCuspidalAtIntegralCusps (maassTraceFunction (H := H) f) := by
  intro A
  letI := Fintype.ofFinite 𝒬
  change Tendsto (fun z : ℍ => ∑ q : 𝒬,
    maassTraceQuotientFunc f q (integralSL2ToReal A • z)) atImInfty (𝓝 0)
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
    (fun q _ => positiveRationalTrace_component_cusp hH f hcusp q A)

/-- Exact invariant, eigenfunction, and cusp data for finite trace through a
positive-rational target. -/
def positiveRationalMaassTraceData_of_data
    (hH : HasPositiveRationalLifts H) (lam : ℝ)
    (f : glUpperHalfPlaneInvariantFunctions G)
    (heigen : IsMaassEigenfunction lam f.1)
    (hcusp : IsCuspidalAtIntegralCusps f.1) :
    {F : glUpperHalfPlaneInvariantFunctions H //
      IsMaassEigenfunction lam F.1 ∧ IsCuspidalAtIntegralCusps F.1} :=
  ⟨maassTraceInvariant (H := H) f,
    ⟨⟨positiveRationalMaassTrace_smooth_of_data hH lam f heigen,
      positiveRationalMaassTrace_eigen_of_data hH lam f heigen⟩,
      positiveRationalMaassTrace_cuspidal_of_data hH f hcusp⟩⟩

end

end GaloisForLFunctions.RHTower
