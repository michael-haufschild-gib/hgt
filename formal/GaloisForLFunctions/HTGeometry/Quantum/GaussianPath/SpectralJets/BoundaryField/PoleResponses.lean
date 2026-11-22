import GaloisForLFunctions.HTGeometry.LocalExtensionQuadraticRateFlatCollapse
import GaloisForLFunctions.HTGeometry.LayerSplitEndpointStep

/-! # Dependence of the transverse spectral response on one boundary field -/
open Set Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Half the second derivative of a weighted energy sum in the transverse
bond, as a rational function of the new longitudinal splitting. -/
def transverseResponse (E : A→ℂ) (M : Matrix A A ℂ) (c : A×Bool→ℂ) (z : ℂ) : ℂ :=
  ∑ a, ∑ b, (c (a,false)-c (b,true))*(M a b*M b a)/(z+E a-E b)

/-- Every level set of the response of a nonzero balanced packet is finite.
The residue at each nonzero gap equates the weights across that edge of
the two layers. The off-diagonal edges already connect the whole graph. -/
theorem finite_response_level (hcard : 3≤Fintype.card A) {E : A→ℂ} (hE : Function.Injective E)
    (hgap : ∀ a b i j, a≠b → i≠j → E b-E a=E j-E i → (a,b)=(i,j))
    {M : Matrix A A ℂ} (hM : ∀ a b, a≠b → M a b≠0)
    {c : A×Bool→ℂ} (hbal : ∑ i, c i=0) (hc : c≠0) (v : ℂ) :
    {z | transverseResponse E M c z=v}.Finite := by
  classical
  by_contra hinf
  let bad := range (fun ab : A×A => E ab.2-E ab.1)
  let S := {z | transverseResponse E M c z=v} \ bad
  have hS : S.Infinite := (show {z | transverseResponse E M c z=v}.Infinite from hinf).sdiff (finite_range _)
  have hpos : 0<Fintype.card A := by omega
  obtain ⟨a₀⟩ := Fintype.card_pos_iff.mp hpos
  have haway (z) (hz : z∈S) : z≠0 ∧ ∀ a b, a≠b → z≠E b-E a := by
    refine ⟨fun he => hz.2 ⟨(a₀,a₀),by simpa only [sub_self] using he.symm⟩,?_⟩
    exact fun a b _ he => hz.2 ⟨(a,b),he.symm⟩
  have h := extensionPacket_crossPair_constant hcard hE hgap
    (w := fun a b => M a b*M b a) (fun a b hab => mul_ne_zero (hM a b hab) (hM b a hab.symm))
    (fun a => c (a,false)) (fun b => c (b,true)) (p := 1) (q := 0) (cst := v)
    (Or.inl one_ne_zero) hS haway (fun z hz => by simpa only [zero_mul,add_zero,one_mul,transverseResponse] using
      (show transverseResponse E M c z=v from hz.1))
  exact hc (crossPairConstant_eq_zero_of_sum_zero hpos c h.1 h.2.2 hbal)

/-- In any infinite set of field settings there is a simple split avoiding one
prescribed response value for each member of a finite family of nonzero
balanced packets. -/
theorem simultaneous_response_escape {I : Type*} [Fintype I] (hcard : 3≤Fintype.card A)
    {E : A→ℂ} (hE : Function.Injective E)
    (hgap : ∀ a b i j, a≠b → i≠j → E b-E a=E j-E i → (a,b)=(i,j))
    {M : Matrix A A ℂ} (hM : ∀ a b, a≠b → M a b≠0) (c : I→A×Bool→ℂ)
    (hbal : ∀ j, ∑ i, c j i=0) (hc : ∀ j, c j≠0) (v : I→ℂ)
    {T : Set ℂ} (hT : T.Infinite) :
    ∃ z ∈ T, Function.Injective (layerSplitEnergy E z) ∧ ∀ j, transverseResponse E M (c j) z≠v j := by
  classical
  let bad := (range (fun ab : A×A => E ab.2-E ab.1)) ∪ ⋃ j, {z | transverseResponse E M (c j) z=v j}
  have hfin : bad.Finite := (finite_range _).union (finite_iUnion (fun j =>
    finite_response_level hcard hE hgap hM (hbal j) (hc j) (v j)))
  obtain ⟨z,hz,hn⟩ := (hT.sdiff hfin).nonempty
  refine ⟨z,hz,injective_layerSplitEnergy hE (fun a b he => hn (Or.inl ⟨(a,b),he.symm⟩)),?_⟩
  exact fun j he => hn (Or.inr (mem_iUnion.mpr ⟨j,he⟩))

#print axioms finite_response_level
#print axioms simultaneous_response_escape
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
