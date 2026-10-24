import GaloisForLFunctions.HTGeometry.PSDKernelOperations

/-!
# The unique antipodal extension of a positive kernel

Adjoining the negative of one Gram vector preserves positivity and determines
every new covariance. Conversely, equal masses and maximally negative pairing
force this extension. Antipodality is therefore compatible with every positive
kernel; a source constraint must specify more than the extra Gram coordinate.
-/

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*}

/-- Extend a kernel by the negative of its Gram vector at the distinguished point. -/
def antipodalKernelExtension (K : X → X → ℂ) (o : X) : Option X → Option X → ℂ
  | some x, some y => K x y
  | some x, none => -K x o
  | none, some y => -K o y
  | none, none => K o o

/-- Every positive kernel admits an antipodal extra coordinate. -/
theorem IsPSDKernel.antipodalExtension {K : X → X → ℂ}
    (hK : IsPSDKernel K) (o : X) : IsPSDKernel (antipodalKernelExtension K o) := by
  letI : Fact (IsPSDKernel K) := ⟨hK⟩
  let v : Option X → KernelHilbert K
    | none => -KernelHilbert.vector K o
    | some x => KernelHilbert.vector K x
  have heq : antipodalKernelExtension K o = fun x y => ⟪v y, v x⟫_ℂ := by
    funext x y
    cases x <;> cases y <;>
      simp only [antipodalKernelExtension, v, inner_neg_left, inner_neg_right,
        neg_neg, KernelHilbert.inner_vector]
  rw [heq]
  exact isPSDKernel_gram v

/-- Equal masses and maximally negative pairing force the extra vector to be
the negative of the distinguished vector, hence force every mixed covariance. -/
theorem antipodalKernelExtension_unique {K : X → X → ℂ} (o : X)
    {J : Option X → Option X → ℂ} (hJ : IsPSDKernel J)
    (hbase : ∀ x y, J (some x) (some y) = K x y)
    (hmass : J none none = K o o)
    (hanti : J none (some o) = -K o o) :
    J = antipodalKernelExtension K o := by
  letI : Fact (IsPSDKernel J) := ⟨hJ⟩
  have hconj : conj (K o o) = K o o := by
    rw [← hbase o o]
    exact hJ.conj_symm _ _
  have hanti' : J (some o) none = -K o o := by
    rw [← hJ.conj_symm none (some o), hanti, map_neg, hconj]
  have hsum : KernelHilbert.vector J none + KernelHilbert.vector J (some o) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [inner_add_left, inner_add_right, inner_add_right]
    simp only [KernelHilbert.inner_vector, hmass, hanti, hanti', hbase]
    ring
  have hvec : KernelHilbert.vector J none = -KernelHilbert.vector J (some o) := by
    exact eq_neg_of_add_eq_zero_left hsum
  funext x y
  cases x with
  | none =>
    cases y with
    | none => exact hmass
    | some y =>
      change J none (some y) = -K o y
      rw [← KernelHilbert.inner_vector, hvec, inner_neg_right,
        KernelHilbert.inner_vector, hbase]
  | some x =>
    cases y with
    | none =>
      change J (some x) none = -K x o
      rw [← KernelHilbert.inner_vector, hvec, inner_neg_left,
        KernelHilbert.inner_vector, hbase]
    | some y => exact hbase x y

/-- Positive antipodal extensions are unique, without a rank or dimension restriction. -/
theorem existsUnique_antipodalKernelExtension {K : X → X → ℂ}
    (hK : IsPSDKernel K) (o : X) :
    ∃! J : Option X → Option X → ℂ,
      IsPSDKernel J ∧ (∀ x y, J (some x) (some y) = K x y) ∧
        J none none = K o o ∧ J none (some o) = -K o o := by
  refine ⟨antipodalKernelExtension K o, ⟨hK.antipodalExtension o,
    fun _ _ => rfl, rfl, rfl⟩, ?_⟩
  intro J hJ
  exact antipodalKernelExtension_unique o hJ.1 hJ.2.1 hJ.2.2.1 hJ.2.2.2

end GaloisForLFunctions.HTGeometry
