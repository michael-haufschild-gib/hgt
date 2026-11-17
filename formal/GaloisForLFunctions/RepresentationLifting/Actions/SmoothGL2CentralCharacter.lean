import GaloisForLFunctions.RepresentationLifting.Actions.DiscreteSL2
import GaloisForLFunctions.RepresentationLifting.Actions.CommutingSemisimpleAlgebra

/-!
# Smooth GL₂ actions with central character

Finite-dimensional smooth actions over any coefficient field factor uniquely
through the determinant. A central character then forces every operator square
to be an invertible scalar. Over a perfect field in which two is nonzero,
the image algebra is semisimple.

This formalizes the contraction and scalar-square mechanism of
arXiv:2611.20896, Lemma 2.2, over every nontrivially normed base field.
-/

noncomputable section
open Filter Topology Matrix
namespace GaloisForLFunctions.RepresentationLifting.DiscreteGL2
variable {K : Type*} [NontriviallyNormedField K]
variable {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]

/-- Every continuous discrete image of GL₂ kills the determinant kernel. -/
theorem det_ker_le (f : GeneralLinearGroup (Fin 2) K →* H) (hf : ContinuousAt f 1) :
    (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) K →* Kˣ).ker ≤ f.ker := by
  intro g hg
  have hg' : g ∈ Set.range (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K → _) := by
    rw [SpecialLinearGroup.range_toGL]
    exact hg
  obtain ⟨s, rfl⟩ := hg'
  change f (SpecialLinearGroup.toGL s) = 1
  apply DiscreteSL2.hom_trivial (f.comp SpecialLinearGroup.toGL) ?_ s
  have hc := hf.comp SpecialLinearGroup.continuous_toGL.continuousAt
  simpa only [map_one] using hc

/-- Every continuous homomorphism from GL₂ to a discrete group factors uniquely through determinant. -/
theorem existsUnique_det_factor (f : GeneralLinearGroup (Fin 2) K →* H)
    (hf : ContinuousAt f 1) :
    ∃! χ : Kˣ →* H, χ.comp GeneralLinearGroup.det = f := by
  let d : GeneralLinearGroup (Fin 2) K →* Kˣ := GeneralLinearGroup.det
  let e := d.liftOfSurjective GeneralLinearGroup.det_surjective
  refine ⟨e ⟨f, det_ker_le f hf⟩, ?_, ?_⟩
  · exact congrArg Subtype.val (e.symm_apply_apply ⟨f, det_ker_le f hf⟩)
  · intro χ hχ
    apply e.symm.injective
    apply Subtype.ext
    exact hχ.trans (congrArg Subtype.val (e.symm_apply_apply ⟨f, det_ker_le f hf⟩)).symm

/-- Such images are abelian even when the target group is not. -/
theorem images_commute (f : GeneralLinearGroup (Fin 2) K →* H) (hf : ContinuousAt f 1)
    (g h : GeneralLinearGroup (Fin 2) K) : Commute (f g) (f h) := by
  obtain ⟨χ, hχ, _⟩ := existsUnique_det_factor f hf
  rw [← hχ]
  exact (Commute.all (GeneralLinearGroup.det g) (GeneralLinearGroup.det h)).map χ

/-- Smooth finite-dimensional GL₂ actions descend uniquely to the determinant. -/
theorem finiteDimensional_smooth_det_factor {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V]
    (ρ : GeneralLinearGroup (Fin 2) K →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) K), ρ g v = v) :
    ∃! χ : Kˣ →* (V ≃ₗ[k] V), χ.comp GeneralLinearGroup.det = ρ := by
  letI : TopologicalSpace (V ≃ₗ[k] V) := ⊥
  letI : DiscreteTopology (V ≃ₗ[k] V) := ⟨rfl⟩
  let b := Module.finBasis k V
  have he : ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) K),
      ∀ i : Fin (Module.finrank k V), ρ g (b i) = b i :=
    Filter.eventually_all.mpr (fun i => hρ (b i))
  have hk : ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) K), ρ g = 1 := by
    filter_upwards [he] with g hg
    apply LinearEquiv.toLinearMap_injective
    exact b.ext (fun i => hg i)
  apply existsUnique_det_factor ρ
  change Tendsto ρ (𝓝 1) (𝓝 (ρ 1))
  rw [map_one]
  exact tendsto_const_nhds.congr' (Filter.Eventually.mono hk (fun _ h => h.symm))

/-- A central character forces every action operator to satisfy a scalar-square relation. -/
theorem centralCharacter_square {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V]
    (ρ : GeneralLinearGroup (Fin 2) K →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) K), ρ g v = v)
    (c : Kˣ →* kˣ)
    (hc : ∀ u v, ρ (GeneralLinearGroup.scalar (Fin 2) u) v = (c u : k) • v)
    (g : GeneralLinearGroup (Fin 2) K) :
    (ρ g).toLinearMap ^ 2 = (c (GeneralLinearGroup.det g) : k) • 1 := by
  obtain ⟨χ, hχ, _⟩ := finiteDimensional_smooth_det_factor ρ hρ
  have he : ρ (g * g) = ρ (GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det g)) := by
    rw [← hχ]
    change χ (GeneralLinearGroup.det (g * g)) =
      χ (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det g)))
    rw [map_mul, GeneralLinearGroup.det_scalar]
    simp only [Fintype.card_fin, pow_two]
  apply LinearMap.ext
  intro v
  have hv := congrArg (fun e : V ≃ₗ[k] V => e v) he
  simpa only [pow_two, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_mul, LinearEquiv.mul_apply] using hv.trans (hc (GeneralLinearGroup.det g) v)

/-- Finite-dimensional smooth GL₂ actions with central character have semisimple image algebra in odd characteristic. -/
theorem centralCharacter_imageAlgebra_isSemisimple {k V : Type*} [Field k] [PerfectField k]
    [NeZero (2 : k)] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : GeneralLinearGroup (Fin 2) K →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) K), ρ g v = v)
    (c : Kˣ →* kˣ)
    (hc : ∀ u v, ρ (GeneralLinearGroup.scalar (Fin 2) u) v = (c u : k) • v) :
    IsSemisimpleRing (Algebra.adjoin k (Set.range (fun g => (ρ g).toLinearMap))) := by
  apply scalarSquare_adjoin_isSemisimpleRing (fun g => (ρ g).toLinearMap)
    (fun g => c (GeneralLinearGroup.det g))
  · obtain ⟨χ, hχ, _⟩ := finiteDimensional_smooth_det_factor ρ hρ
    intro g h
    have he := (Commute.all (GeneralLinearGroup.det g) (GeneralLinearGroup.det h)).map χ
    have he' := congrArg LinearEquiv.toLinearMap he
    rw [← hχ]
    exact he'
  · exact centralCharacter_square ρ hρ c hc

/-- Every invariant subspace splits: the action module over its image algebra is semisimple. -/
theorem centralCharacter_completelyReducible {k V : Type*} [Field k] [PerfectField k]
    [NeZero (2 : k)] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : GeneralLinearGroup (Fin 2) K →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) K), ρ g v = v)
    (c : Kˣ →* kˣ)
    (hc : ∀ u v, ρ (GeneralLinearGroup.scalar (Fin 2) u) v = (c u : k) • v) :
    let A := Algebra.adjoin k (Set.range (fun g => (ρ g).toLinearMap))
    letI : Module A V := Module.compHom V A.val.toRingHom
    IsSemisimpleModule A V := by
  let A := Algebra.adjoin k (Set.range (fun g => (ρ g).toLinearMap))
  letI : Module A V := Module.compHom V A.val.toRingHom
  letI : IsSemisimpleRing A := centralCharacter_imageAlgebra_isSemisimple ρ hρ c hc
  infer_instance

#print axioms centralCharacter_completelyReducible
#print axioms centralCharacter_imageAlgebra_isSemisimple

#print axioms finiteDimensional_smooth_det_factor
#print axioms centralCharacter_square

#print axioms existsUnique_det_factor
#print axioms images_commute
end GaloisForLFunctions.RepresentationLifting.DiscreteGL2
