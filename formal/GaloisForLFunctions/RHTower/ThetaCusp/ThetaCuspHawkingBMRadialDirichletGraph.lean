import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalJointProjection

/-! The original radial Dirichlet graph and its preservation by actual angular contraction. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev RadialDerivativeSpace := PiLp 2 (fun _ : Fin 2 => RadialSpace)

/-- Value and actual derivative of an original smooth interior tortoise test. -/
def radialDirichletGraph (f : RadialCore) : RadialDerivativeSpace :=
  WithLp.toLp 2 ![radialValue f,radialDerivative f]

/-- Closure of the original interior radial cores retains the Dirichlet boundary domain. -/
def radialDirichletDomain : Submodule ℂ RadialDerivativeSpace :=
  (Submodule.span ℂ (Set.range radialDirichletGraph)).topologicalClosure

instance : CompleteSpace radialDirichletDomain := by unfold radialDirichletDomain; infer_instance

theorem radialDirichletGraph_mem (f : RadialCore) : radialDirichletGraph f ∈ radialDirichletDomain :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f,rfl⟩)

/-- Partial Hilbert contraction by an arbitrary original angular L2 vector. -/
def angularContraction (g : D4BMModularCore.Space) : SpatialSpace →L[ℂ] RadialSpace :=
  (l2SeparatedProductContinuousBilinear.flip g : RadialSpace →L[ℂ] SpatialSpace).adjoint

theorem angularContraction_inner (g : D4BMModularCore.Space) (h : RadialSpace) (u : SpatialSpace) :
    inner ℂ h (angularContraction g u) = inner ℂ (l2SeparatedProduct h g) u := by
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

theorem angularContraction_separated (g k : D4BMModularCore.Space) (f : RadialSpace) :
    angularContraction g (l2SeparatedProduct f k) = inner ℂ g k • f := by
  apply ext_inner_left ℂ
  intro h
  rw [angularContraction_inner,l2SeparatedProduct_inner,inner_smul_right]
  exact mul_comm _ _

/-- Contraction retains both the original value and radial derivative. -/
def radialGraphContraction (g : D4BMModularCore.Space) : JointEnergySpace →L[ℂ] RadialDerivativeSpace :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => RadialSpace)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 2 =>
      (angularContraction g).comp (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) i.castSucc.castSucc)))

theorem radialGraphContraction_core (g : D4BMModularCore.Space) (f : RadialCore)
    (k : D4BMModularCore.CoreField) :
    radialGraphContraction g (jointGraph f k) = inner ℂ g (D4BMModularCore.fieldVector k) • radialDirichletGraph f := by
  apply PiLp.ext
  intro i
  fin_cases i <;> exact angularContraction_separated _ _ _

/-- Every angular L2 contraction of the original completed joint domain lies in the original radial Dirichlet domain. -/
theorem radialGraphContraction_mem (g : D4BMModularCore.Space) (u : jointDomain) :
    radialGraphContraction g u ∈ radialDirichletDomain := by
  have hs : jointDomain ≤ radialDirichletDomain.comap (radialGraphContraction g).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨f,k⟩,rfl⟩
      change radialGraphContraction g (jointGraph f k) ∈ radialDirichletDomain
      rw [radialGraphContraction_core]
      exact radialDirichletDomain.smul_mem _ (radialDirichletGraph_mem f)
    · exact (Submodule.isClosed_topologicalClosure _).preimage (radialGraphContraction g).continuous
  exact hs u.property

/-- Pairwise weak limits retain the closed original Dirichlet graph, including its endpoint information. -/
theorem radialDirichletDomain_of_pairing_limit (v : ℕ → RadialDerivativeSpace)
    (hv : ∀ n, v n ∈ radialDirichletDomain) (R D : RadialSpace)
    (hR : ∀ h : RadialSpace, Tendsto (fun n => inner ℂ h (v n 0)) atTop (𝓝 (inner ℂ h R)))
    (hD : ∀ h : RadialSpace, Tendsto (fun n => inner ℂ h (v n 1)) atTop (𝓝 (inner ℂ h D))) :
    WithLp.toLp 2 ![R,D] ∈ radialDirichletDomain := by
  rw [← radialDirichletDomain.orthogonal_orthogonal]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro z hz
  have ht := (hR (z 0)).add (hD (z 1))
  have he : ∀ n, inner ℂ (z 0) (v n 0)+inner ℂ (z 1) (v n 1) = 0 := by
    intro n
    have h := (Submodule.mem_orthogonal' _ _).mp hz (v n) (hv n)
    simpa [PiLp.inner_apply,Fin.sum_univ_succ] using h
  have hzero : inner ℂ (z 0) R+inner ℂ (z 1) D = 0 :=
    tendsto_nhds_unique ht (by simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0)))
  simpa [PiLp.inner_apply,Fin.sum_univ_succ] using hzero

end
end RHTower.D4BMJointWave
