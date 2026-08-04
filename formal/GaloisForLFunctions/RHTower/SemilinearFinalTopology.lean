import GaloisForLFunctions.RHTower.LinearFinalTopology

/-!
# Semilinear maps out of linear final topologies

The linear-final universal property extends to a semilinear map when its
scalar endomorphism is continuous.  This is needed for conjugate-linear Real
involutions on LF spaces: continuity is checked on every genuine finite stage,
while addition and scalar multiplication remain continuous in the induced
topology.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

universe uR uI uE uV uW

variable (R : Type uR) [Semiring R] [TopologicalSpace R]
variable {I : Type uI} (E : I → Type uE)
variable [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]
variable [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousAdd (E i)]
variable [∀ i, ContinuousSMul R (E i)]
variable (V : Type uV) [AddCommMonoid V] [Module R V]
variable (stage : ∀ i, E i →ₗ[R] V)
variable {W : Type uW} [AddCommMonoid W] [Module R W]
variable (tW : TopologicalSpace W)
variable (hWadd : @ContinuousAdd W tW inferInstance)
variable (hWsmul : @ContinuousSMul R W inferInstance inferInstance tW)
variable {σ : R →+* R}

include hWadd hWsmul

/-- A semilinear map from a linear-final space is continuous when its scalar
endomorphism and all stage restrictions are continuous. -/
theorem linearFinalTopology_semilinear_continuous
    (hσ : Continuous σ) (g : V →ₛₗ[σ] W)
    (hstage : ∀ i, @Continuous (E i) W inferInstance tW
      (fun x => g (stage i x))) :
    @Continuous V W (linearFinalTopology R E V stage) tW g := by
  letI : TopologicalSpace W := tW
  letI : ContinuousAdd W := hWadd
  letI : ContinuousSMul R W := hWsmul
  rw [continuous_iff_le_induced]
  apply sInf_le
  refine ⟨?_, ?_, ?_⟩
  · letI : TopologicalSpace V := TopologicalSpace.induced g tW
    refine ⟨?_⟩
    rw [continuous_induced_rng]
    change Continuous (fun p : V × V => g (p.1 + p.2))
    rw [show (fun p : V × V => g (p.1 + p.2)) =
        fun p => g p.1 + g p.2 by
      funext p
      exact map_add g p.1 p.2]
    exact (continuous_induced_dom.comp continuous_fst).add
      (continuous_induced_dom.comp continuous_snd)
  · letI : TopologicalSpace V := TopologicalSpace.induced g tW
    refine ⟨?_⟩
    rw [continuous_induced_rng]
    change Continuous (fun p : R × V => g (p.1 • p.2))
    rw [show (fun p : R × V => g (p.1 • p.2)) =
        fun p => σ p.1 • g p.2 by
      funext p
      exact map_smulₛₗ g p.1 p.2]
    exact (hσ.comp continuous_fst).smul
      (continuous_induced_dom.comp continuous_snd)
  · intro i
    rw [continuous_induced_rng]
    exact hstage i

end GaloisForLFunctions.RHTower
